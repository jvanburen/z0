#include <stdbool.h>
/* Z0 assertions
 * Needed because cc0 doesn't preserve the types of assertions
 */
#include "../z0lib/c0runtime.h"

#define Z0_IDENTITY(name) void z0_##name(bool cond) {\
    if (cond) c0_abort("@name annotation failed!");\
}

Z0_IDENTITY(requires);       // Indicates a precondition
Z0_IDENTITY(ensures);        // Indicates a postcondition
Z0_IDENTITY(loop_invariant); // Indicates a loop invariant
Z0_IDENTITY(assert);         // Indicates an assertion
