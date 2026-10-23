/* Call the C library's sqrt and fabs on test vectors and print, for each
   test, "<function> <input> <result> <errno>" (input and result as 64-bit
   hexadecimal patterns, errno as a decimal number).
   Usage: hw [number of random tests] [seed]
   Compile with -fno-builtin: the functions are called through volatile
   pointers, so that the compiler cannot evaluate or inline them. */
#include <errno.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static double (*volatile p_sqrt)(double) = sqrt;
static double (*volatile p_fabs)(double) = fabs;

static uint64_t state;
static uint64_t rnd(void) {          /* xorshift64* */
  state ^= state >> 12; state ^= state << 25; state ^= state >> 27;
  return state * 2685821657736338717ULL;
}

/* Special doubles: zeros, infinities, quiet and signaling NaNs with
   payloads and both signs, subnormals, normal extremes, negatives. */
static const uint64_t special[] = {
  0x0000000000000000ULL, 0x8000000000000000ULL,   /* +0, -0 */
  0x7ff0000000000000ULL, 0xfff0000000000000ULL,   /* +inf, -inf */
  0x7ff8000000000000ULL, 0xfff8000000000000ULL,   /* default qNaNs */
  0x7ff8000000000001ULL, 0xfff8000000000001ULL,   /* qNaNs with payload */
  0x7ffc00000000abcdULL, 0xfffc00000000abcdULL,
  0x7fffffffffffffffULL, 0xffffffffffffffffULL,
  0x7ff0000000000001ULL, 0xfff0000000000001ULL,   /* sNaNs */
  0x7ff4000000001234ULL, 0xfff4000000001234ULL,
  0x7ff7ffffffffffffULL, 0xfff7ffffffffffffULL,
  0x0000000000000001ULL, 0x8000000000000001ULL,   /* smallest subnormals */
  0x000fffffffffffffULL, 0x800fffffffffffffULL,   /* largest subnormals */
  0x0008000000000000ULL, 0x8008000000000000ULL,
  0x0010000000000000ULL, 0x8010000000000000ULL,   /* smallest normals */
  0x7fefffffffffffffULL, 0xffefffffffffffffULL,   /* largest normals */
  0x3ff0000000000000ULL, 0xbff0000000000000ULL,   /* 1, -1 */
  0x4000000000000000ULL, 0xc000000000000000ULL,   /* 2, -2 */
  0x4010000000000000ULL, 0x3fb999999999999aULL,   /* 4, 0.1 */
  0x3ca0000000000000ULL, 0x7fe0000000000000ULL,   /* 2^-53, 2^1023 */
  0x3ff0000000000001ULL, 0x3fefffffffffffffULL,   /* 1 +/- ulp */
};
#define NS (sizeof(special) / sizeof(special[0]))

static void test(uint64_t x) {
  double d, r; uint64_t rb;
  memcpy(&d, &x, 8);
  errno = 0; r = p_sqrt(d); memcpy(&rb, &r, 8);
  printf("sqrt %016llx %016llx %d\n", (unsigned long long) x, (unsigned long long) rb, errno);
  errno = 0; r = p_fabs(d); memcpy(&rb, &r, 8);
  printf("fabs %016llx %016llx %d\n", (unsigned long long) x, (unsigned long long) rb, errno);
}

int main(int argc, char **argv) {
  long n = argc > 1 ? atol(argv[1]) : 10000000;
  state = argc > 2 ? strtoull(argv[2], NULL, 0) : 0x9e3779b97f4a7c15ULL;
  if (state == 0) state = 1;
  printf("special\n");
  for (size_t i = 0; i < NS; i++) test(special[i]);
  printf("random\n");                        /* random bit patterns */
  for (long i = 0; i < n; i++) test(rnd());
  printf("squares\n");     /* exact squares and their neighbours */
  for (long i = 0; i < n / 4; i++) {
    double m = (double) (rnd() >> 38), s = m * m;
    uint64_t x;
    memcpy(&x, &s, 8);
    test(x + (rnd() % 3) - 1);
  }
  printf("subnormal\n");                    /* random subnormals */
  for (long i = 0; i < n / 4; i++) test(rnd() & 0x800fffffffffffffULL);
  return 0;
}
