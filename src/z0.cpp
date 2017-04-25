
#include "llvm/Pass.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/Instruction.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"
#include "z3++.h"

#include <unordered_map>
#include <iostream>
#include <string>
#include <sstream>
#include <climits>

#define Z0_ASSERT_NAME "z0_assert"


using namespace llvm;

namespace {
#define DEBUG_TYPE "Z0"

struct StopZ0 final {
    char const* const why; /* Guaranteed non-null */
    explicit StopZ0(const char why[]="<no reason given>") :why(why) {
        assert(why != nullptr);
        DEBUG(dbgs() << "Stopping Z0 cleanly with exception (" << why << ")...\n");
    }
};

// An analysis pass that symbolically checks contracts.
class Z0 final : public ModulePass {
    z3::context cxt;
    z3::solver solver = z3::solver(cxt);
    z3::sort z0_int = cxt.bv_sort(32);
    z3::expr int_min_expr = cxt.bv_val(INT32_MIN, 32);
    z3::expr zero_expr = cxt.bv_val(0, 32);
    z3::expr minusone_expr = cxt.bv_val(-1, 32);
    z3::expr true_expr = cxt.bv_val(1, 1);
    z3::expr false_expr = cxt.bv_val(0, 1);

    std::unordered_map<Value const*, z3::symbol> val2symbol;
    unsigned int count = 0;
    // enum class Verb {
    //     errors=1, unknown=2, everything=3
    // } verbosity;

    // #define DO_ERROR(X) do {if (verbosity >= Verb::errors) { X; }} while (false)
    // #define DO_UNK(X) do {if (verbosity >= Verb::unknown) { X; }} while (false)

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
                    analyze_main(F);
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

    z3::symbol& get_symbol(Value const* v) {
        auto it = val2symbol.find(v);
        if (it == val2symbol.end()) {
            auto res = val2symbol.emplace(v, cxt.int_symbol(++count));
            return res.first->second;
        }
        return it->second;
    }

    /* Requires v to have an integer llvm type */
    z3::expr get_bv_constant(Value const* v) {
        IntegerType *type = llvm::cast<IntegerType>(v->getType());
        z3::symbol& name = this->get_symbol(v);
        return cxt.constant(name, cxt.bv_sort(type->getBitWidth()));
    }

    void analyze_basicblock(BasicBlock const* BB) {
        DEBUG(dbgs() << "Printing Basic Block " << BB->getName() << ":\n");
        // auto &BIL = BB->getInstList();
        Instruction const* term = BB->getTerminator();
        for (auto it = BB->begin(); &*it != term; ++it) {
            Instruction const* instr = &*it;
            DEBUG(instr->dump());
            // c.bv_val(const char *n, unsigned int sz)
        }
        DEBUG(dbgs() << "Analyzing Basic Block " << BB->getName() << ":\n");
        for (auto it = BB->begin(); &*it != term; ++it) {
            analyze_instruction(&*it);
            // c.bv_val(const char *n, unsigned int sz)
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
        } else {
            z3::expr me = get_bv_constant(ci);
            z3::expr a = value2expr(ci->getOperand(0));
            z3::expr b = value2expr(ci->getOperand(1));

            if (name == "c0_idiv") {
                check_div(a, b);
                solver.add(me == binop_expr(Instruction::SDiv, a, b));

            } else if (name == "c0_imod") {
                check_div(a, b);
                solver.add(me == binop_expr(Instruction::SRem, a, b));

            } else {
                errs() << "Unknown function called: " << name << "\n";
                assert(false);
            }
        }
    }

    bool is_precondition(CallInst const* ci) {
        return false; /* TODO: change this in some horrible way */
    }

    void check_div(z3::expr a, z3::expr b) {
        z3::expr fdiv = (b == zero_expr) || (a == int_min_expr && b == minusone_expr);
        solver.push();
        {
            solver.add(fdiv);
            switch (solver.check()) {
                case z3::sat:
                    errs() << "division by zero possible!\n"; break;
                case z3::unsat:
                    DEBUG(dbgs() << "division by zero impossible\n"); break;
                case z3::unknown:
                    errs() << "Cannot prove division safe!\n"; break;
            }
        }
        solver.pop();
        solver.add(!fdiv);
    }

    void analyze_z0_assert(CallInst const* ci) {
        Value const* cond = ci->getOperand(0);
        DEBUG(dbgs() << "analyzing assertion");
        DEBUG(ci->dump());
        if (is_precondition(ci)) {
            solver.add(value2expr(cond));
            switch (solver.check()) {
                case z3::sat:
                    DEBUG(dbgs() << "Precondition ok\n"); break;
                case z3::unsat:
                    throw StopZ0("Precondition unsatisfiable!");
                case z3::unknown:
                    errs() << "Precondition could not be verified!\n"; break;
            }
        } else { // not a precondition
            solver.push();
            {
                // outs() << "is bool "<< value2expr(cond).is_bool() << "\n";
                solver.add(value2expr(cond) != true_expr);
                switch (solver.check()) {
                    case z3::sat:
                        DEBUG(dbgs() << "Found counterexample!\n");
                        throw StopZ0("Found counterexample to assertion");
                    case z3::unsat:
                        DEBUG(dbgs() << "Assertion verified!:\n");
                        DEBUG(dbgs() << to_string(solver.assertions()));
                        break;
                    case z3::unknown:
                        errs() << "Assertion could not be verified!\n"; break;
                }
            }
            solver.pop();
            /* We add the assertion in case we couldn't derive it */
            solver.add(value2expr(cond) == true_expr);
        }
    }

    void analyze_other(Instruction const* instr) {
        DEBUG(dbgs() << "Unknown instruction encountered:\n");
        DEBUG(instr->dump());
        throw StopZ0("Unknown instruction encountered\n");
    }

    z3::expr value2expr(Value const* val) {
        if (ConstantInt const*n = dyn_cast<ConstantInt>(val)) {
            if (val->getType()->isIntegerTy(1) || val->getType()->isIntegerTy(32)) {
                return cxt.bv_val((int)n->getSExtValue(), n->getBitWidth());
            } else {
                DEBUG(val->dump());
                throw StopZ0("weird-width integer");
            }
        } else if (isa<Instruction>(val)) {
            if (llvm::IntegerType const* t = dyn_cast<IntegerType>(val->getType())) {
                return cxt.constant(get_symbol(val), cxt.bv_sort(t->getBitWidth()));
            } else {
                DEBUG(val->dump());
                throw StopZ0("Instruction doesn't have integer type!");
            }
        } else {
            DEBUG(val->dump());
            throw StopZ0("weird constant value");
        }
    }

    void analyze_binop(Instruction const* instr) {
        assert(instr->getNumOperands() == 2 && "not a binop!");
        z3::expr instrconst = get_bv_constant(instr);
        z3::expr a = value2expr(instr->getOperand(0));
        z3::expr b = value2expr(instr->getOperand(1));
        try {
            if (ICmpInst const* icmp = dyn_cast<ICmpInst>(instr)) {
                z3::expr c = cmp_expr(icmp->getPredicate(), a, b);
                solver.add(instrconst == z3::ite(c, true_expr, false_expr));
            } else {
                z3::expr c = binop_expr(instr->getOpcode(), a, b);
                solver.add(instrconst == c);
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
            case llvm::CmpInst::ICMP_SGT: return to_expr(cxt, Z3_mk_bvsgt(cxt, a, b));
            case llvm::CmpInst::ICMP_SGE: return to_expr(cxt, Z3_mk_bvsge(cxt, a, b));
            case llvm::CmpInst::ICMP_SLT: return to_expr(cxt, Z3_mk_bvslt(cxt, a, b));
            case llvm::CmpInst::ICMP_SLE: return to_expr(cxt, Z3_mk_bvsle(cxt, a, b));
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
            case Instruction::Add:  return to_expr(cxt, Z3_mk_bvadd(cxt, a, b));
            case Instruction::Sub:  return to_expr(cxt, Z3_mk_bvsub(cxt, a, b));
            case Instruction::Mul:  return to_expr(cxt, Z3_mk_bvmul(cxt, a, b));
            case Instruction::And:  return to_expr(cxt, Z3_mk_bvand(cxt, a, b));
            case Instruction::Xor:  return to_expr(cxt, Z3_mk_bvxor(cxt, a, b));
            case Instruction::Or:   return to_expr(cxt, Z3_mk_bvor(cxt, a, b));
            case Instruction::Shl:  return to_expr(cxt, Z3_mk_bvshl(cxt, a, b));
            case Instruction::SRem: return to_expr(cxt, Z3_mk_bvsmod(cxt, a, b));
            case Instruction::AShr: return to_expr(cxt, Z3_mk_bvashr(cxt, a, b));
            case Instruction::SDiv: return to_expr(cxt, Z3_mk_bvsdiv(cxt, a, b));
            case Instruction::UDiv:
            case Instruction::LShr:
            case Instruction::URem:
                throw StopZ0("unsigned ints in C0?");
            default:
                throw StopZ0 ("unknown binop encountered");
        }
    }

    void analyze_main(Function &F) {
        // ignore all control flow (for now)
        for (BasicBlock &BB : F) {
            analyze_basicblock(&BB);
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
