/* EXPECT sqrt=call fabs=call */
/* The addresses are taken in initializers. */
#include <math.h>
double (*p)(double) = sqrt;
double f(double x) {
  static double (*q)(double) = fabs;
  return q(x) + sqrt(x) + fabs(x) + 1.0;
}
