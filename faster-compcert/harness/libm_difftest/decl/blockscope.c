/* EXPECT on=1 off=2 */
/* A block-scope declaration with a typedef for double. */
typedef double real;
real f(real x) { extern real floor(real); return floor(x) + floor(x); }
