/* EXPECT sqrt=call fabs=call */
/* OPTIONS -fvararg-calls */
/* Not the C99 prototype: variadic. */
double sqrt(double, ...);
double fabs(double, ...);
double f(double x) { return sqrt(x) + fabs(x) + 1.0; }
