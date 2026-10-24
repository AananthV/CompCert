/* Hardware side of the "unal" group (issue #13): unaligned movq loads and
   stores at every offset 0..7 within a cache line, across cache lines,
   across a page boundary (two mapped pages), and at random addresses.
   For each test, prints the 24 bytes around the access (before and, for
   stores, after) and the result.  See check_unal.ml. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

uint64_t hw_ld0(const unsigned char *p);
uint64_t hw_ldx(const unsigned char *p, uint64_t idx);
void hw_st0(unsigned char *p, uint64_t v);
void hw_stx(unsigned char *p, uint64_t idx, uint64_t v);

static uint64_t s;
static uint64_t rnd(void) { s ^= s << 13; s ^= s >> 7; s ^= s << 17; return s; }

static unsigned char *buf;
static long pg;

static void hex(const unsigned char *p) { for (int i = 0; i < 24; i++) printf("%02x", p[i]); }

static void one(const char *cat, long aoff, int store) {
  unsigned char *a = buf + aoff;
  for (int i = -8; i < 16; i++) a[i] = (unsigned char)rnd();
  int form = (int)(rnd() & 1);
  uint64_t idx = rnd() & 15;
  unsigned char before[24]; memcpy(before, a - 8, 24);
  if (!store) {
    uint64_t r = form ? hw_ldx(a - 5 - 4 * idx, idx) : hw_ld0(a);
    printf("L %s %d %llu %ld ", cat, form, (unsigned long long)idx, aoff);
    hex(before); printf(" %016llx\n", (unsigned long long)r);
  } else {
    uint64_t v = rnd();
    if (form) hw_stx(a + 3 - 8 * idx, idx, v); else hw_st0(a, v);
    printf("S %s %d %llu %ld ", cat, form, (unsigned long long)idx, aoff);
    hex(before); printf(" %016llx ", (unsigned long long)v); hex(a - 8); printf("\n");
  }
}

int main(int argc, char **argv) {
  long n = argc > 1 ? atol(argv[1]) : 20000;
  s = argc > 2 ? strtoull(argv[2], 0, 0) : 0x9e3779b97f4a7c15ULL;
  if (s == 0) s = 1;
  pg = sysconf(_SC_PAGESIZE);
  buf = mmap(0, 2 * pg, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (buf == MAP_FAILED) return 2;
  for (int st = 0; st <= 1; st++) {
    for (long t = 0; t < n; t++) {
      long line = 64 * (1 + (long)(rnd() % (pg / 64 - 2)));
      one("line", line + t % 8, st);                         /* offsets 0..7 in a line */
      one("xline", line + 64 - 1 - t % 7, st);               /* crossing a cache line */
      one("page", pg - 1 - t % 7, st);                       /* crossing the page boundary */
      one("rand", 8 + (long)(rnd() % (2 * pg - 32)), st);    /* anywhere in the two pages */
    }
  }
  return 0;
}
