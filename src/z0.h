
#include "llvm/Pass.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/Instruction.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"
#include "llvm/IR/DebugInfoMetadata.h"
// #include "llvm/IR/metadata.h"
#include "z3++.h"
#include "state.h"

#include <unordered_map>
#include <iostream>
#include <string>
#include <sstream>
#include <climits>
#include <cstdint>

using namespace llvm;


#define DEBUG_TYPE "Z0"

// An analysis pass that symbolically checks contracts.
class Z0 final : public ModulePass {

    Z0State state;
    z3::expr int_min_expr = state.bv_val(INT32_MIN, I32);
    z3::expr zero_expr = state.bv_val(0, I32);
    z3::expr minusone_expr = state.bv_val(-1, I32);
    z3::expr true_expr = state.bv_val(1, I1);
    z3::expr false_expr = state.bv_val(0, I1);

    // enum class Verb {
    //     errors=1, unknown=2, everything=3
    // } verbosity;

/* Standard ModulePass stuff */
public:
    static char ID;

    Z0() : ModulePass(ID) {}
    ~Z0() { }

    void getAnalysisUsage(AnalysisUsage &AU) const override {
        AU.setPreservesAll(); /* Doesn't modify the program, so preserve all analyses */
        AU.addRequired<LoopInfoWrapperPass>();
    }
    bool doInitialization(Module &M) override {
        DEBUG(dbgs() << "Z0 pass initializing...\n");
        DEBUG(dbgs() << "Z0 pass initialized.\n");
        return false; // Didn't modify anything
    }
    bool doFinalization(Module &M) override {
        DEBUG(dbgs() << "Z0 pass finalizing...\n");
        DEBUG(dbgs() << "Z0 pass finalized.\n");
        return false; // Didn't modify anything
    }

    bool runOnModule(Module &M) override {
        DEBUG(dbgs() << "Z0 pass running...\n");

        for (Function &F : M) {
            if (F.getName().startswith("_c0_")) {
                state.reset();
                outs() << "Analyzing function " << F.getName().drop_front(4) << "...\n";
                LoopInfoWrapperPass &info = getAnalysis<LoopInfoWrapperPass>(F);
                cut_loops(F, info.getLoopInfo());
                BasicBlock const& entry = F.getEntryBlock();
                try {
                    bool doesReturn = analyze_basicblock(entry, nullptr);
                    if (!doesReturn) {
                        outs() << "Warning: function never returns. Perhaps an infinite loop or unsatisfiable precondition?\n";
                    }
                    outs() << "OK!\n";
                } catch (StopZ0 e) {
                    DEBUG(dbgs() << "Z0 stopped cleanly via exception.\n");
                    errs() << "Z0 Stopped: " << e.why << "\n";
                    DEBUG(outs() << "Along path: ");
                    DEBUG(state.show_path(&entry));
                } catch (z3::exception e) {
                    errs() << "Internal Error! z3 raised an exception:\n";
                    errs() << e.msg() << "\n";
                }
            }
        }
        DEBUG(dbgs() << "Z0 pass finished.\n");
        return false;
    }

private: /* Z0-specific logic */
    template <typename T>
    std::string to_string(T e) {
        std::stringstream ss;
        ss << e;
        return ss.str();
    }

    void cut_loops(Function &F, LoopInfo &li){
        // loop transformation code would go here
    }

    bool is_reachable(void) {
        switch (state.solver.check()) {
            case z3::unknown:
                DEBUG(errs() << "***Path could not be confirmed reachable, assuming it is***\n");
            case z3::sat:
                return true;
            case z3::unsat:
                DEBUG(dbgs() << "is_reachable is false:\n");
                DEBUG(dbgs() << to_string(state.solver.assertions()));
                DEBUG(dbgs() << "\nalong path:\n");
                DEBUG(state.show_path(nullptr));
                return false;
        }
        __builtin_unreachable();
    }

    bool analyze_basicblock(BasicBlock const& BB, BasicBlock const* from) {
        DEBUG(dbgs() << "Analyzing Basic Block " << BB.getName());
        if (from == nullptr) {
            DEBUG(dbgs() << " (entry block):\n");
        } else {
            DEBUG(dbgs() << " (from " << from->getName() << "):\n");
        }
        // DEBUG(BB->dump());
        TerminatorInst const* term = BB.getTerminator();
        BasicBlock::const_iterator it = BB.begin();
        if (from != nullptr) {
            auto nonPhi = BB.getFirstNonPHI();
            while (&*it != nonPhi) {
                PHINode const* phi = cast<PHINode>(&*it);
                Value const* phiVal = phi->getIncomingValueForBlock(from);
                state.assert_eq(state.z3_repr(phi), state.z3_repr(phiVal));
                ++it;
            }
        }
        try {
            while (&*it != term) {
                analyze_instruction(&*it);
                ++it;
            }
        } catch (UnreachablePath _) {
            return false;
        }
        bool doesReturn = false;

        if (term->getOpcode() == Instruction::Ret) {
            doesReturn = is_reachable();
        } else if (BranchInst const* br = dyn_cast<BranchInst>(term)) {
            // The true branch is the first successor

            if (br->isConditional()) {
                Value const* cond = br->getCondition();
                z3::expr cond_expr = state.z3_repr(cond);
                {
                    BasicBlock const* next = br->getSuccessor(0);
                    state.push(next);
                    state.assert_eq(cond_expr, true_expr);
                    if (is_reachable()) {
                        try { doesReturn |= analyze_basicblock(*next, &BB);
                        } catch (UnreachablePath _){}
                    }
                    state.pop();
                }{
                    BasicBlock const* next = br->getSuccessor(1);
                    state.push(next);
                    state.assert_eq(cond_expr, false_expr);
                    if (is_reachable()) {
                        try { doesReturn |= analyze_basicblock(*next, &BB);
                        } catch (UnreachablePath u){}
                    }
                    state.pop();
                }
            } else { // unconditional branch
                BasicBlock const* next = br->getSuccessor(0);
                state.push(next);
                try {
                    doesReturn |= analyze_basicblock(*next, &BB);
                } catch (UnreachablePath u){}
                state.pop();
            }
        } else if (isa<UnreachableInst>(term)) {
            // If LLVM can detect this is impossible with
            // its few analyses, then it's probably pretty simple/intended
            DEBUG(dbgs() << "Assuming trivially unreachable path is intended\n");
            doesReturn = true;
        } else {
            DEBUG(term->dump());
            throw StopZ0("Unknown basic block terminator");
        }
        return doesReturn;
    }

    void analyze_instruction(Instruction const* instr) {
        if (CallInst const* ci = dyn_cast<CallInst>(instr)) {
            DEBUG(instr->dump());
            analyze_call(ci);
        } else if (isa<PHINode>(instr)) {
            DEBUG(instr->dump());
            assert(false && "PHI nodes shouldn't appear in analyze_instruction");
        } else if (instr->getNumOperands() == 2) {
            analyze_binop(instr);
        } else if (instr->getNumOperands() == 1) {
            analyze_unaryop(instr);
        } else {
            DEBUG(dbgs() << "Unknown instruction encountered:\n");
            DEBUG(instr->dump());
            throw StopZ0("Unknown instruction encountered\n");
        }
    }

    void analyze_call(CallInst const* ci) {
        StringRef name = ci->getCalledFunction()->getName();
        if (name.startswith("z0")) {
            analyze_z0_assert(ci);
        } else if (name == "c0_idiv") {
            z3::expr a = state.z3_repr(ci->getOperand(0));
            z3::expr b = state.z3_repr(ci->getOperand(1));
            z3::expr me = state.bv_constant(ci);
            check_div(a, b);
            state.assert_eq(me, binop_expr(Instruction::SDiv, a, b));
        } else if (name == "c0_imod") {
            z3::expr a = state.z3_repr(ci->getOperand(0));
            z3::expr b = state.z3_repr(ci->getOperand(1));
            z3::expr me = state.bv_constant(ci);
            check_div(a, b);
            state.assert_eq(me, binop_expr(Instruction::SRem, a, b));
        } else if (name == "llvm.dbg.value") {
            /* This intrinsic provides information when a user source variable
            is set to a new value.
            The first argument is the new value (wrapped as metadata).
            The second argument is the offset in the user source variable
                where the new value is written.
            The third argument is a local variable containing a description
                of the variable.
            The fourth argument is a complex expression.*/
            auto const* val_wrap = llvm::cast<MetadataAsValue>(ci->getOperand(0));
            auto const* lv_wrap = llvm::cast<MetadataAsValue>(ci->getOperand(2));
            auto const* val = llvm::cast<ValueAsMetadata>(val_wrap->getMetadata());
            auto const* lv = llvm::cast<DILocalVariable>(lv_wrap->getMetadata());
            DEBUG(dbgs() << "Got assignment to value: " << lv->getName() << " = " << *val << "\n");
            if (lv->getName().startswith("_c0v_") || lv->getName() == "_c0t__result") {
                state.update_ident(lv, val);
            }
        } else if (name == "llvm.dbg.declare") {
            DEBUG(dbgs() << "(Ignoring variable declaration.)\n");
            /* ignore */
        } else {
            throw StopZ0("Unknown function \"" + std::string(name.begin(), name.end()) + "\" called");
            assert(false);
        }
    }

    bool is_precondition(CallInst const* ci) {
        return ci->getCalledFunction()->getName() == "z0_requires";
    }

    void check_div(z3::expr a, z3::expr b);

    void analyze_z0_assert(CallInst const* ci);

    void analyze_binop(Instruction const* instr) {
        assert(instr->getNumOperands() == 2 && "not a binop!");
        z3::expr instrconst = state.bv_constant(instr);
        z3::expr a = state.z3_repr(instr->getOperand(0));
        z3::expr b = state.z3_repr(instr->getOperand(1));
        try {
            if (ICmpInst const* icmp = dyn_cast<ICmpInst>(instr)) {
                z3::expr c = cmp_expr(icmp->getPredicate(), a, b);
                state.assert_eq(instrconst, z3::ite(c, true_expr, false_expr));
            } else {
                z3::expr c = binop_expr(instr->getOpcode(), a, b);
                state.assert_eq(instrconst, c);
            }
        } catch (StopZ0 e) {
            DEBUG(instr->dump());
            throw e;
        }
    }
    void analyze_unaryop(Instruction const* instr) {
        z3::expr instrconst = state.bv_constant(instr);
        if (auto const* icast = dyn_cast<CastInst>(instr)) {
            state.assert_eq(instrconst, cast_expr(icast));
        } else {
            DEBUG(instr->dump());
            throw StopZ0("Unknown unary operator");
        }
    }

    /* Helper functions that are big and not very interesting are put into the
     * .cpp file to help reduce clutter and make the main algorithm more readable
     */
    z3::expr cmp_expr(llvm::CmpInst::Predicate pred, z3::expr a, z3::expr b);
    z3::expr binop_expr(unsigned opcode, z3::expr a, z3::expr b);
    z3::expr cast_expr(CastInst const* icmp);
    void display_counterexample(void);
};
#undef DEBUG_TYPE
