/* EXPECT on=6 off=12 */
/* <math.h> declarations: each duplicate call is shared. */
#include <math.h>
double f(double x, double y) {
  return floor(x) + floor(x) + sin(x) + sin(x) + pow(x, y) + pow(x, y);
}
float g(float x, float y) {
  return floorf(x) + floorf(x) + cosf(x) + cosf(x) + atan2f(x, y) + atan2f(x, y);
}
