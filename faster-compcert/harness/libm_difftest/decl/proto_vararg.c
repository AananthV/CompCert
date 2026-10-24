/* EXPECT on=2 off=2 */
/* Not the C99 prototype: variadic. */
double floor(double, ...);
double f(double x) { return floor(x) + floor(x); }
