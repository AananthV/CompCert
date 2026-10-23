/* EXPECT sqrt=call fabs=call */
/* Not the C99 prototype: extra argument, integer types. */
double sqrt(double, double);
int fabs(int);
double f(double x, int i) { return sqrt(x, x) + fabs(i) + 1.0; }
