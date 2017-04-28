#include "z0.h"

#define DEBUG_TYPE "Z0"

void
Z0::display_counterexample(void) {
    z3::model model = state.get_model();
    outs() << "=== Counterexample: ===\n";
    DEBUG(dbgs() << "Outputting model:\n");
    DEBUG(dbgs() << to_string(model) << "\n");
    DEBUG(dbgs() << "From Assertions:\n");
    DEBUG(dbgs() << to_string(state.solver.assertions()) << "\n");

    std::map<z3::symbol, int> symb2num;
    int N = model.num_consts();

    __int64 integer;
    for (int i = 0; i < N; ++i) {
        auto funcdecl = model.get_const_decl(i);
        z3::symbol name = funcdecl.name();
        z3::expr value = model.get_const_interp(funcdecl).simplify();
        DEBUG(dbgs() << "Symbol " << to_string(name) << " <= " << to_string(value) << "\n");
        if (Z3_get_numeral_int64(state.cxt, value, &integer)) {
            symb2num[name] = integer;
        } else {
            DEBUG(dbgs() << "Can't get numeral from " << to_string(value) << "\n");
        }
    }
    for (auto& pair : state.name2val) {
        // DEBUG(dbgs() << "looking at variable " << pair.first << "\n");
        StringRef localname = pair.first;
        assert(localname.startswith("_c0v_"));
        outs() << localname.drop_front(5) << " = ";
        Value const* val = pair.second.second->getValue();
        if (z3::symbol* symb = state.lookup_symbol(val)) {
            auto it = symb2num.find(*symb);
            if (it == symb2num.end()) {
                outs() << to_string(*symb) << "?\n";
            } else {
                outs() << it->second << "\n";
            }
        } else if (auto const* intval = llvm::dyn_cast<ConstantInt>(val)) {
            outs() << intval->getSExtValue() << "\n";
        } else {
            outs() << "*\n";
        }
    }
}

void
Z0::analyze_z0_assert(CallInst const* ci) {
    Value const* cond = ci->getOperand(0);
    DEBUG(dbgs() << "Analyzing assertion ");
    DEBUG(ci->dump());
    DEBUG(dbgs() << "\n");
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
            state.add(state.z3_repr(cond) != true_expr);
            switch (state.check()) {
                case z3::sat:
                    DEBUG(dbgs() << "Found counterexample!\n");
                    display_counterexample();
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

void
Z0::check_div(z3::expr a, z3::expr b) {
    z3::expr fdiv = (b == zero_expr) || (a == int_min_expr && b == minusone_expr);
    state.push();
    {
        state.add(fdiv);
        switch (state.check()) {
            case z3::sat:
                errs() << "Division by zero possible!\n";
                display_counterexample();
                break;
            case z3::unsat:
                DEBUG(dbgs() << "Division by zero impossible\n"); break;
            case z3::unknown:
                errs() << "Cannot prove division safe!\n";
                errs() << state.solver.reason_unknown() << "\n";
                break;
        }
    }
    state.pop();
    state.add(!fdiv);
}


/* Implement bitvector arithmetic*/
#define Z3_MK(name, a, b) state.z3_to_expr(Z3_mk_##name(state.cxt, a, b))

z3::expr
Z0::cast_expr(CastInst const* icast) {
    z3::expr operand = state.z3_repr(icast->getOperand(0));
    if (!icast->isIntegerCast()) throw StopZ0("Unknown non-integer cast");
    unsigned srcTypeWidth = cast<IntegerType>(icast->getSrcTy())->getBitWidth();
    unsigned dstTypeWidth = cast<IntegerType>(icast->getDestTy())->getBitWidth();
    int change = dstTypeWidth - srcTypeWidth;
    switch (icast->getOpcode()) {
        case Instruction::ZExt: return Z3_MK(zero_ext, change, operand);
        case Instruction::SExt: return Z3_MK(sign_ext, change, operand);
        case Instruction::Trunc: return operand.extract(0, dstTypeWidth-1);
        default:
            DEBUG(icast->dump());
            throw StopZ0("Unknown cast encountered");
    }
}

z3::expr
Z0::binop_expr(unsigned opcode, z3::expr a, z3::expr b) {
    switch (opcode) {
        case Instruction::Add:  return Z3_MK(bvadd, a, b);
        case Instruction::Sub:  return Z3_MK(bvsub, a, b);
        case Instruction::Mul:  return Z3_MK(bvmul, a, b);
        case Instruction::And:  return Z3_MK(bvand, a, b);
        case Instruction::Xor:  return Z3_MK(bvxor, a, b);
        case Instruction::Or:   return Z3_MK(bvor, a, b);
        case Instruction::Shl:  return Z3_MK(bvshl, a, b);
        case Instruction::SRem: return Z3_MK(bvsrem, a, b);
        case Instruction::AShr: return Z3_MK(bvashr, a, b);
        case Instruction::SDiv: return Z3_MK(bvsdiv, a, b);
        case Instruction::UDiv:
        case Instruction::LShr:
        case Instruction::URem:
            throw StopZ0("Unsigned ints in C0?");
        default:
            throw StopZ0 ("Unknown binop encountered");
    }
}

z3::expr
Z0::cmp_expr(llvm::CmpInst::Predicate pred, z3::expr a, z3::expr b) {
    switch (pred) {
        case llvm::CmpInst::ICMP_EQ:  return a == b;
        case llvm::CmpInst::ICMP_NE:  return a != b;
        case llvm::CmpInst::ICMP_SGT: return Z3_MK(bvsgt, a, b);
        case llvm::CmpInst::ICMP_SGE: return Z3_MK(bvsge, a, b);
        case llvm::CmpInst::ICMP_SLT: return Z3_MK(bvslt, a, b);
        case llvm::CmpInst::ICMP_SLE: return Z3_MK(bvsle, a, b);
        case llvm::CmpInst::ICMP_UGT:
        case llvm::CmpInst::ICMP_UGE:
        case llvm::CmpInst::ICMP_ULT:
        case llvm::CmpInst::ICMP_ULE:
            throw StopZ0("Unsigned ints in C0?");
        default:
            throw StopZ0("Unknown compare operation?");
    }
}
#undef BV_ARITH
#undef DEBUG_TYPE

// LLVM uses the address of this static member to identify the pass, so the
// initialization value is unimportant.
char Z0::ID = 0;
static RegisterPass<Z0>
    X("z0", "17-355: Z0 Symbolic Analysis pass", false, false);
