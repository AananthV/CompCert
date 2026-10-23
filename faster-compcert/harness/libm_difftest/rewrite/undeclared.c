/* EXPECT sqrt=none fabs=none */
/* A local variable named sqrt, no libm function. */
double f(double x) { double sqrt = x; return sqrt * 2.0; }
