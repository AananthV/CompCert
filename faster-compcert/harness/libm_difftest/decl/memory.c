/* EXPECT on=1 off=2 */
/* A store between the two calls: the calls do not depend on memory. */
#include <math.h>
double g[4];
double f(double x) { double a = floor(x); g[1] = a; return a + floor(x) + g[1]; }
