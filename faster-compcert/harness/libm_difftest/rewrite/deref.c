/* EXPECT sqrt=builtin fabs=call */
/* (*sqrt)(x) is a direct call (the elaborator removes the dereference);
   (long) fabs takes the address of fabs. */
#include <math.h>
double f(double x) {
  return (*sqrt)(x) + sqrt(x) + fabs(x) + (long) fabs + 1.0;
}
