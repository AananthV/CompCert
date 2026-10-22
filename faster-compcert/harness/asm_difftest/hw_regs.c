/* Run the register-only instruction sequences of regs_tests.s (generated
   by gen_tests.py) from random complete register states, and print one
   line per test:

     <name> <imm> <a> <b> <r> <rh> <flags_kept> <others_kept> <xor> | <asm>

   a = destination before (low 64 bits), b = source before (low 64 bits;
   %rcx for the shifts by %cl; 0 if none), r / rh = destination after
   (low / high 64 bits; rh = 0 for an integer register),
   flags_kept = 1 if CF PF AF ZF SF OF are unchanged, others_kept = 1 if
   every register except the destination (all of %rax-%r15 but %rsp,
   %xmm0-%xmm15 in full) is unchanged, xor = 1 if the sequence starts
   with the printer's xorps/xorpd.  check_regs.ml compares with Asm.v.
   Usage: hw_regs [number of random tests per instruction] [seed] */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

struct state { uint64_t gpr[16]; uint64_t xmm[16][2]; uint64_t flags; };
void hw_run(const struct state *in, struct state *out, void (*body)(void));

struct entry {
  const char *name; void (*body)(void); int64_t imm;
  int64_t dst, src;           /* 0-15: GPR, 16-31: XMM, -1: none */
  int64_t dstcls, srccls;     /* value classes, see gen() */
  int64_t xor, weight;        /* weight: number of entries with this name */
  const char *text;
};
extern const struct entry test_table[];

enum { C_RANDOM, C_INT32, C_INT64, C_DOUBLE, C_SINGLE, C_COUNT };
#define ARITH_FLAGS 0x8d5

static uint64_t state;
static uint64_t rnd(void) {          /* xorshift64* */
  state ^= state >> 12; state ^= state << 25; state ^= state >> 27;
  return state * 2685821657736338717ULL;
}

static const uint32_t special_i[] = {
  0, 1, 2, 3, 0xffffffffu, 0x80000000u, 0x7fffffffu, 0x80000001u,
  0x55555555u, 0xaaaaaaaau, 0x0000ffffu, 0xffff0000u, 0x01000000u,
  0x00ffffffu, 0xff000000u, 0x01000001u, 0x7fffffc0u, 0xffffff81u,
};
static const uint64_t special_l[] = {
  0, 1, 2, 0xffffffffffffffffULL, 0x8000000000000000ULL, 0x7fffffffffffffffULL,
  0x8000000000000001ULL, 0x00000000ffffffffULL, 0xffffffff00000000ULL,
  0x0020000000000000ULL, 0x0020000000000001ULL, 0x001fffffffffffffULL,
  0xffdfffffffffffffULL, 0x0000000001000001ULL, 0x7ffffffffffffc00ULL,
  0x7ffffffffffffdffULL, 0x4000000000000400ULL, 0x00000000ffffff81ULL,
};
static const uint64_t special_d[] = {
  0x0000000000000000ULL, 0x8000000000000000ULL, 0x7ff0000000000000ULL,
  0xfff0000000000000ULL, 0x7ff8000000000000ULL, 0xfff8000000000000ULL,
  0x7ff8000000000001ULL, 0xfffc00000000abcdULL, 0x7ff0000000000001ULL,
  0xfff4000000001234ULL, 0x0000000000000001ULL, 0x8000000000000001ULL,
  0x000fffffffffffffULL, 0x800fffffffffffffULL, 0x0010000000000000ULL,
  0x7fefffffffffffffULL, 0xffefffffffffffffULL, 0x3ff0000000000000ULL,
  0xbff0000000000000ULL, 0x3fb999999999999aULL, 0x4000000000000000ULL,
  0x3ca0000000000000ULL, 0x7fe0000000000000ULL, 0x0008000000000000ULL,
  0x47efffffe0000000ULL, 0x47efffffefffffffULL, 0x47effffff0000000ULL,
  0x36a0000000000000ULL, 0x3690000000000000ULL, 0x3810000000000000ULL,
  0xc7f0000000000000ULL, 0x7ff00000ffffffffULL, 0x7ff7ffffe0000000ULL,
};
static const uint32_t special_s[] = {
  0x00000000u, 0x80000000u, 0x7f800000u, 0xff800000u, 0x7fc00000u,
  0xffc00000u, 0x7fc00001u, 0xffe0abcdu, 0x7f800001u, 0xffa01234u,
  0x00000001u, 0x80000001u, 0x007fffffu, 0x807fffffu, 0x00800000u,
  0x7f7fffffu, 0xff7fffffu, 0x3f800000u, 0xbf800000u, 0x3dcccccdu,
};
#define LEN(a) (sizeof(a) / sizeof((a)[0]))

static uint64_t dbits(double d) { uint64_t u; memcpy(&u, &d, 8); return u; }
static uint32_t fbits(float f) { uint32_t u; memcpy(&u, &f, 4); return u; }

/* Upper 32 bits of an integer register holding a 32-bit value:
   garbage, zero or all ones. */
static uint64_t upper_garbage(void) {
  switch (rnd() % 4) {
  case 0: return 0;
  case 1: return 0xffffffff00000000ULL;
  default: return rnd() & 0xffffffff00000000ULL;
  }
}

/* Value of class cls for test number i; the first tests of each
   entry enumerate the special values.  lo = low 64 bits; the high 64
   bits of an XMM register stay random. */
static uint64_t gen(int cls, long i) {
  switch (cls) {
  case C_INT32: {
    uint32_t v = (unsigned long) i < LEN(special_i) ? special_i[i]
               : rnd() % 3 ? (uint32_t) rnd() : special_i[rnd() % LEN(special_i)];
    return upper_garbage() | v;
  }
  case C_INT64:
    if ((unsigned long) i < LEN(special_l)) return special_l[i];
    switch (rnd() % 4) {
    case 0: return special_l[rnd() % LEN(special_l)] ^ (rnd() & 0xff);
    case 1: return (uint64_t) (int64_t) (int32_t) rnd();
    case 2: return rnd() >> (rnd() % 64);
    default: return rnd();
    }
  case C_DOUBLE:
    if ((unsigned long) i < LEN(special_d)) return special_d[i];
    switch (rnd() % 4) {
    case 0: return rnd();
    case 1: return special_d[rnd() % LEN(special_d)] ^ (rnd() & 0xf);
    default: return dbits(((double) (int64_t) rnd()) / (double) (1 + (rnd() % 1000000)));
    }
  case C_SINGLE: {
    uint32_t v;
    if ((unsigned long) i < LEN(special_s)) v = special_s[i];
    else switch (rnd() % 4) {
      case 0: v = (uint32_t) rnd(); break;
      case 1: v = special_s[rnd() % LEN(special_s)] ^ (rnd() & 0xf); break;
      default: v = fbits((float) ((double) (int32_t) rnd() / (double) (1 + (rnd() % 1000))));
      }
    return (rnd() & 0xffffffff00000000ULL) | v;
  }
  case C_COUNT:   /* %cl = i mod 256, garbage or zero in bits 8..63 */
    return (uint64_t) (i % 256) | ((rnd() % 2) ? rnd() & ~0xffULL : 0);
  default:
    return rnd();
  }
}

static uint64_t *reg(struct state *s, int r) {
  return r < 16 ? &s->gpr[r] : &s->xmm[r - 16][0];
}

static void run(const struct entry *e, long i) {
  struct state in, out;
  for (int r = 0; r < 16; r++) {
    in.gpr[r] = rnd(); in.xmm[r][0] = rnd(); in.xmm[r][1] = rnd();
  }
  in.flags = rnd() & ARITH_FLAGS;
  if (e->src >= 0) *reg(&in, e->src) = gen(e->srccls, i);
  if (e->src != e->dst) *reg(&in, e->dst) = gen(e->dstcls, i);
  memcpy(&out, &in, sizeof out);         /* %rsp is not saved */
  hw_run(&in, &out, e->body);
  int others = 1;
  for (int r = 0; r < 32; r++) {
    if (r == e->dst || r == 4) continue;
    if (r < 16 ? in.gpr[r] != out.gpr[r]
               : memcmp(in.xmm[r - 16], out.xmm[r - 16], 16) != 0)
      others = 0;
  }
  printf("%s %llx %016llx %016llx %016llx %016llx %d %d %d | %s\n",
         e->name, (unsigned long long) e->imm,
         (unsigned long long) *reg(&in, e->dst),
         (unsigned long long) (e->src >= 0 ? *reg(&in, e->src) : 0),
         (unsigned long long) *reg(&out, e->dst),
         (unsigned long long) (e->dst >= 16 ? out.xmm[e->dst - 16][1] : 0),
         in.flags == out.flags, others, (int) e->xor, e->text);
}

int main(int argc, char **argv) {
  long n = argc > 1 ? atol(argv[1]) : 20000;
  state = argc > 2 ? strtoull(argv[2], NULL, 0) : 0x9e3779b97f4a7c15ULL;
  for (const struct entry *e = test_table; e->name != NULL; e++) {
    /* n random tests per instruction, split over its entries (at least
       64 per entry, and 256 * 16 for the shifts by %cl, i.e. 16 per count). */
    long k = n / e->weight;
    if (k < 64) k = 64;
    if (e->srccls == C_COUNT && k < 256 * 16) k = 256 * 16;
    for (long i = 0; i < k; i++) run(e, i);
  }
  return 0;
}
