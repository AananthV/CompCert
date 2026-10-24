/* EXPECT on=2 off=2 */
/* OPTIONS -funprototyped */
/* Not a prototype: an old-style declaration. */
double floor();
double f(double x) { return floor(x) + floor(x); }
