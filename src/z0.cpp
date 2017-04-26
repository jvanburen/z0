
#include "llvm/Pass.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/Instruction.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "z3++.h"
#include "state.h"

#include <unordered_map>
#include <iostream>
#include <string>
#include <sstream>
#include <climits>
#include <cstdint>

#define Z0_ASSERT_NAME "z0_assert"

using namespace llvm;

namespace {
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
        try {
            for (Function &F : M) {
                DEBUG(dbgs() << "Found " << F.getName() << "...\n");
                if (F.getName().str() ==  "_c0_main") {
                    DEBUG(dbgs() << "Oh, found main!\n");
                    for (BasicBlock &BB : F) { // there should only be one for now
                        analyze_basicblock(&BB);
                    }
                }
            }
        } catch (StopZ0 e) {
            DEBUG(dbgs() << "Z0 stopped cleanly via exception.\n");
            errs() << "Z0 Stopped. " << e.why << "\n";
        } catch (z3::exception e) {
            errs() << "z3 raised an exception:\n";
            errs() << e.msg() << "\n";
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

    void analyze_basicblock(BasicBlock const* BB) {
        DEBUG(dbgs() << "Printing Basic Block " << BB->getName() << ":\n");
        Instruction const* term = BB->getTerminator();
        for (auto it = BB->begin(); &*it != term; ++it) {
            Instruction const* instr = &*it;
            DEBUG(instr->dump());
        }
        DEBUG(dbgs() << "Analyzing Basic Block " << BB->getName() << ":\n");
        for (auto it = BB->begin(); &*it != term; ++it) {
            analyze_instruction(&*it);
        }
    }

    void analyze_instruction(Instruction const* instr) {
        if (CallInst const* ci = dyn_cast<CallInst>(instr)) {
            DEBUG(instr->dump());
            analyze_call(ci);
        } else if (instr->getNumOperands() == 2) {
            analyze_binop(instr);
        } else {
            analyze_other(instr);
        }
    }

    void analyze_call(CallInst const* ci) {
        StringRef name = ci->getCalledFunction()->getName();
        if (name == Z0_ASSERT_NAME) {
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
            /* update debug info */
            // DILocalVariable const* lv = llvm::cast<DILocalVariable>(ci->getOperand(2));
            // state.update_ident(lv->getName(), )
        }else if (name == "llvm.dbg.declare") {
            /* ignore */
        } else {
            throw StopZ0("Unknown function " + std::string(name.begin(), name.end()) + " called");
            assert(false);
        }
    }

    bool is_precondition(CallInst const* ci) {
        return false; /* TODO: change this in some horrible way */
    }

    void check_div(z3::expr a, z3::expr b) {
        z3::expr fdiv = (b == zero_expr) || (a == int_min_expr && b == minusone_expr);
        state.push();
        {
            state.add(fdiv);
            switch (state.check()) {
                case z3::sat:
                    errs() << "division by zero possible!\n"; break;
                case z3::unsat:
                    DEBUG(dbgs() << "division by zero impossible\n"); break;
                case z3::unknown:
                    errs() << "Cannot prove division safe!\n"; break;
            }
        }
        state.pop();
        state.add(!fdiv);
    }

    void analyze_z0_assert(CallInst const* ci) {
        Value const* cond = ci->getOperand(0);
        DEBUG(dbgs() << "analyzing assertion");
        DEBUG(ci->dump());
        if (is_precondition(ci)) {
            state.add(state.z3_repr(cond));
            switch (state.check()) {
                case z3::sat:
                    DEBUG(dbgs() << "Precondition ok\n"); break;
                case z3::unsat:
                    throw StopZ0("Precondition unsatisfiable!");
                case z3::unknown:
                    errs() << "Precondition could not be verified!\n"; break;
            }
        } else { // not a precondition
            state.push();
            {
                // outs() << "is bool "<< value2expr(cond).is_bool() << "\n";
                state.add(state.z3_repr(cond) != true_expr);
                switch (state.check()) {
                    case z3::sat:
                        DEBUG(dbgs() << "Found counterexample!\n");
                        errs() << to_string(state.solver.assertions()) << "\n";
                        errs() << to_string(state.solver.get_model()) << "\n";
                        errs() << "num Consts:" << state.solver.get_model().num_consts() << "\n";
                        errs() << "num funcs:" << state.solver.get_model().num_funcs() << "\n";
                        errs() << "\n";
                        throw StopZ0("Found counterexample to assertion");
                    case z3::unsat:
                        DEBUG(dbgs() << "Assertion verified!:\n");
                        DEBUG(dbgs() << to_string(state.solver.assertions()));
                        break;
                    case z3::unknown:
                        errs() << "Assertion could not be verified!\n"; break;
                }
            }
            state.pop();
            /* We add the assertion in case we couldn't derive it */
            state.add(state.z3_repr(cond) == true_expr);
        }
    }

    void analyze_other(Instruction const* instr) {
        DEBUG(dbgs() << "Unknown instruction encountered:\n");
        DEBUG(instr->dump());
        throw StopZ0("Unknown instruction encountered\n");
    }

    void analyze_binop(Instruction const* instr) {
        assert(instr->getNumOperands() == 2 && "not a binop!");
        z3::expr instrconst = state.bv_constant(instr);
        z3::expr a = state.z3_repr(instr->getOperand(0));
        z3::expr b = state.z3_repr(instr->getOperand(1));
        try {
            if (ICmpInst const* icmp = dyn_cast<ICmpInst>(instr)) {
                z3::expr c = cmp_expr(icmp->getPredicate(), a, b);
                state.add(instrconst == z3::ite(c, true_expr, false_expr));
            } else {
                z3::expr c = binop_expr(instr->getOpcode(), a, b);
                state.add(instrconst == c);
            }
        } catch (StopZ0 e) {
            DEBUG(instr->dump());
            throw e;
        }
    }

    z3::expr cmp_expr(llvm::CmpInst::Predicate pred, z3::expr a, z3::expr b) {
        switch (pred) {
            case llvm::CmpInst::ICMP_EQ:  return a == b;
            case llvm::CmpInst::ICMP_NE:  return a != b;
            case llvm::CmpInst::ICMP_SGT: return BV_ARITH(state, sgt, a, b);// to_expr(cxt, Z3_mk_bvsgt(cxt, a, b));
            case llvm::CmpInst::ICMP_SGE: return BV_ARITH(state, sge, a, b);//to_expr(cxt, Z3_mk_bvsge(cxt, a, b));
            case llvm::CmpInst::ICMP_SLT: return BV_ARITH(state, slt, a, b);//to_expr(cxt, Z3_mk_bvslt(cxt, a, b));
            case llvm::CmpInst::ICMP_SLE: return BV_ARITH(state, sle, a, b);//to_expr(cxt, Z3_mk_bvsle(cxt, a, b));
            case llvm::CmpInst::ICMP_UGT:
            case llvm::CmpInst::ICMP_UGE:
            case llvm::CmpInst::ICMP_ULT:
            case llvm::CmpInst::ICMP_ULE:
                throw StopZ0("unsigned ints in C0?");
            default:
                throw StopZ0("unknown compare operation?");
        }
    }

    z3::expr binop_expr(unsigned opcode, z3::expr a, z3::expr b) {
        switch (opcode) {
            case Instruction::Add:  return BV_ARITH(state, add, a, b);
            case Instruction::Sub:  return BV_ARITH(state, sub, a, b);
            case Instruction::Mul:  return BV_ARITH(state, mul, a, b);
            case Instruction::And:  return BV_ARITH(state, and, a, b);
            case Instruction::Xor:  return BV_ARITH(state, xor, a, b);
            case Instruction::Or:   return BV_ARITH(state, or, a, b);
            case Instruction::Shl:  return BV_ARITH(state, shl, a, b);
            case Instruction::SRem: return BV_ARITH(state, smod, a, b);
            case Instruction::AShr: return BV_ARITH(state, ashr, a, b);
            case Instruction::SDiv: return BV_ARITH(state, sdiv, a, b);
            case Instruction::UDiv:
            case Instruction::LShr:
            case Instruction::URem:
                throw StopZ0("unsigned ints in C0?");
            default:
                throw StopZ0 ("unknown binop encountered");
        }
    }
};
} // End anonymous namespace
#undef DEBUG_TYPE
// LLVM uses the address of this static member to identify the pass, so the
// initialization value is unimportant.
char Z0::ID = 0;
static RegisterPass<Z0>
    X("z0", "17-355: Z0 Symbolic Analysis pass", false, false);
