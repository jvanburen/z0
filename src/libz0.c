#include <stdbool.h>
/* Z0 assertions
 * Needed because cc0 doesn't preserve the types of assertions
 */
#include "../include/z0/c0runtime.h"

#define Z0_IDENTITY(name) bool z0_##name(bool cond) { return cond; };

Z0_IDENTITY(requires);       // Indicates a precondition
Z0_IDENTITY(ensures);        // Indicates a postcondition
Z0_IDENTITY(loop_invariant); // Indicates a loop invariant
Z0_IDENTITY(assert);         // Indicates an assertion
