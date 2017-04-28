/* This defines C functions and types that CC0-generated code uses */
/* Significant portions copied from cc0lib.h and c0runtime.h */


/* CC0 helper interfacs
 *
 * Primitives used by the cc0 compiler that aren't specificed as part
 * of the cc0 runtime go here.
 *
 * This header file uses c0runtime.h functions, but does not include
 * the c0runtime.h header because it does not know whether the runtime
 * has defined C0_RUNTIME_IMPELEMENTS_LENGTH or not.
 */

/* avoiding imprecise semantics */
#define CC0 1

// The type of an array of type ty
#define cc0_array(ty) c0_array

// Allocate a value of type ty on the heap
#define cc0_alloc(ty) ((ty*) c0_alloc(sizeof(ty)))

// Dereferences a pointer
#define cc0_deref(ty, p) (*(ty*)c0_deref((p)))

// Allocate an array of type ty with count elements
#define cc0_alloc_array(ty, count) ((cc0_array(ty)) c0_array_alloc(sizeof(ty), (count)))

// Generates an lvalue of type ty for the ith value in A
#define cc0_array_sub(ty, A, i) (*(ty*)c0_array_sub(A, i, sizeof(ty)))

#ifdef IGNORE_CC0_ASSERT
#define cc0_assert(cond, reason) ((void) 0)
#else
#define cc0_assert(cond, reason) c0_assert(cond, reason)
#endif

#define cc0_tag(ty, tyrep, e) (c0_tag_ptr(tyrep, e))
#define cc0_untag(ty, tyrep, e) ((ty)c0_untag_ptr(tyrep, e))
