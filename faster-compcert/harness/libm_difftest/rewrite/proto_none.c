/* EXPECT sqrt=call fabs=call */
/* OPTIONS -funprototyped */
/* Not a prototype: old-style declarations. */
double sqrt();
double fabs();
double f(double x) { return sqrt(x) + fabs(x) + 1.0; }
