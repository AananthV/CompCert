/* EXPECT sqrt=none fabs=builtin */
/* A parameter named sqrt shadows the C library's sqrt; [p] calls it. */
#include <math.h>
double f(double (*sqrt)(double), double x) { return sqrt(x) + fabs(x) + 1.0; }
double g(double x) { return f(cbrt, x); }
