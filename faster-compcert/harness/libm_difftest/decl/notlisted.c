/* EXPECT on=6 off=6 */
/* Functions that are not in the list: lgamma sets signgam, frexp writes
   through a pointer, fmin is not listed. */
#include <math.h>
double f(double x, int *e) {
  return lgamma(x) + lgamma(x) + frexp(x, e) + frexp(x, e) + fmin(x, 1.0) + fmin(x, 1.0);
}
