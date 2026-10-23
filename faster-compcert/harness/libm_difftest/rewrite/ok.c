/* EXPECT sqrt=builtin fabs=builtin */
#include <math.h>
double f(double x) { return sqrt(x) + fabs(x); }
double g(float y, int i) { return (sqrt)(i) * fabs(y); }
double h(double x) { return sqrt(x); }   /* would be a tail call */
