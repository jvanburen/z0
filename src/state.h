#pragma once

#include "llvm/Support/Debug.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Constants.h"
#include "z3++.h"
#include <string>
#include <unordered_map>
#include <cstdint>

using std::unordered_map;
using std::string;
using namespace llvm;

#define DEBUG_TYPE "Z0State" /* For LLVM's DEBUG macro */

/* Implement bitvector arithmetic*/
#define BV_ARITH(state, operation, a, b) z3::to_expr((state).cxt, Z3_mk_bv##operation((state).cxt, (a), (b)))

struct StopZ0 final {
    std::string const why;
    explicit StopZ0(const char why[]="<no reason given>") :why(why) {
        assert(why != nullptr);
        DEBUG(dbgs() << "Stopping Z0 cleanly with exception (" << why << ")...\n");
    }
    explicit StopZ0(std::string const& why) :StopZ0(why.c_str()) {
        DEBUG(dbgs() << "Stopping Z0 cleanly with exception (" << why << ")...\n");
    }
};
enum BitWidth {I1=1u,I32=32u};
/* Z0 solver state */
class Z0State final {
    // Identifiers:
    unsigned int count = 0;
    std::unordered_map<Value const*, z3::symbol> val2symbol;
    std::unordered_map<std::string, z3::expr> ident2expr;

public:
    z3::context cxt;
    z3::sort z0_int_sort = cxt.bv_sort(32);

    z3::solver solver;

    explicit Z0State(void) : solver(cxt) {}

    void update_ident(std::string name, z3::expr expr) {
        ident2expr[name] = expr;
    }

    z3::expr bv_val(int32_t i, BitWidth bitwidth) {
        return cxt.bv_val(i, bitwidth);
    }

    z3::symbol& symbol(Value const* v) {
        auto it = val2symbol.find(v);
        if (it == val2symbol.end()) {
            auto res = val2symbol.emplace(v, cxt.int_symbol(++count));
            return res.first->second;
        }
        return it->second;
    }

    /* Requires v to have an integer llvm type */
    z3::expr bv_constant(Value const* v) {
        assert(llvm::isa<IntegerType>(v->getType()));
        IntegerType *type = llvm::cast<IntegerType>(v->getType());
        z3::symbol& name = this->symbol(v);
        return cxt.constant(name, cxt.bv_sort(type->getBitWidth()));
    }

    /* gets the z3 representation of an llvm value*/
    z3::expr z3_repr(Value const* val) {
        if (ConstantInt const* n = dyn_cast<ConstantInt>(val)) {
            if (val->getType()->isIntegerTy(1) || val->getType()->isIntegerTy(32)) {
                return cxt.bv_val((int)n->getSExtValue(), n->getBitWidth());
            } else {
                DEBUG(val->dump());
                throw StopZ0("weird-width integer");
            }
        } else if (isa<Instruction>(val)) {
            if (llvm::IntegerType const* t = dyn_cast<IntegerType>(val->getType())) {
                return cxt.constant(symbol(val), cxt.bv_sort(t->getBitWidth()));
            } else {
                DEBUG(val->dump());
                throw StopZ0("Instruction doesn't have integer type!");
            }
        } else {
            DEBUG(val->dump());
            throw StopZ0("weird constant value");
        }
    }

    void push(void) {
        solver.push();
    }
    void pop(void) {
        solver.pop();
    }

    void assert_eq(z3::expr a, z3::expr b) {
        solver.add(a == b);
    }
    void add(z3::expr e) {
        solver.add(e);
    }

    z3::check_result check(void){
        return solver.check();
    }

};

#undef DEBUG_TYPE
