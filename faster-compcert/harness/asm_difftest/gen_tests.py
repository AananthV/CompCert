#!/usr/bin/env python3
"""Generate regs_tests.s: the register-only instruction sequences of
issues #10 and #11, in the exact syntax printed by x86/TargetPrinter.ml
(and x86/Asmexpand.ml for sqrtsd), each as a tiny "body" ending in ret,
plus a table describing them for hw_regs.c.

usage: gen_tests.py GROUPS SEED > regs_tests.s
GROUPS is a comma-separated subset of zx,cvt,shift,zxload."""

import random
import sys

GPR64 = ["rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi",
         "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"]
GPR32 = ["eax", "ecx", "edx", "ebx", "esp", "ebp", "esi", "edi",
         "r8d", "r9d", "r10d", "r11d", "r12d", "r13d", "r14d", "r15d"]
XMM = 16          # register index of %xmm0 in the hw_regs.c state

# Value classes, see gen() in hw_regs.c.
C_RANDOM, C_INT32, C_INT64, C_DOUBLE, C_SINGLE, C_COUNT, C_BYTE, C_HALF = range(8)

entries = []      # (name, imm, dst, src, dstcls, srccls, xor, asm lines, mem)

# mem = (base, index, scale, disp, memcls) for a memory operand
# disp(%base,%index,scale), with index = -1 if there is none, and memcls
# the class of the value loaded; NOMEM for no memory operand.
NOMEM = (-1, -1, 0, 0, C_RANDOM)


def add(name, imm, dst, src, dstcls, srccls, xor, lines, mem=NOMEM):
    entries.append((name, imm, dst, src, dstcls, srccls, xor, lines, mem))


def gen_zx(rng):
    # Asmgen emits Psallzx_ri for n in 1..24 (SelectLong.shllimm with
    # zext_shl_ok), Pshrlzx_ri for n in 1..31 (SelectOp.shruimm) and
    # Pandlzx_ri for any immediate.  We also test the shift counts 0 and
    # 32..63, for which the model is Vundef (counts >= 32) or which the
    # compiler never emits (0).
    special_and = [0, 1, 0x7f, 0x80, 0xff, 0xffff, 0x7fffffff, 0x80000000,
                   0xffffffff, 0xfffffff0, 0xffffff80, 0x0f0f0f0f, 0xffff0000,
                   0x00ff00ff, 0xfffffffe]
    ands = special_and + [rng.getrandbits(32) for _ in range(49)]
    for rd in (0, 11):                       # %eax, %r11d (REX prefix)
        r = "%" + GPR32[rd]
        for n in range(64):
            add("sallzx", n, rd, -1, C_INT32, C_RANDOM, 0, ["sall	$%d, %s" % (n, r)])
            add("shrlzx", n, rd, -1, C_INT32, C_RANDOM, 0, ["shrl	$%d, %s" % (n, r)])
        for n in ands:
            # TargetPrinter prints the immediate with coqint, i.e. as a
            # signed 32-bit decimal.
            s = n - (1 << 32) if n >= 1 << 31 else n
            add("andlzx", n, rd, -1, C_INT32, C_RANDOM, 0, ["andl	$%d, %s" % (s, r)])


def gen_shift(rng):
    for rd in (0, 2, 9):                     # %rax, %rdx, %r9
        for op in ("sal", "shr", "sar"):
            add(op + "l_rcl", 0, rd, 1, C_INT32, C_COUNT, 0,
                ["%sl	%%cl, %%%s" % (op, GPR32[rd])])
            add(op + "q_rcl", 0, rd, 1, C_INT64, C_COUNT, 0,
                ["%sq	%%cl, %%%s" % (op, GPR64[rd])])


def gen_cvt(rng):
    # GPR -> XMM conversions: TargetPrinter always clears rd first.
    for (d, s) in ((0, 0), (13, 12), (7, 1)):
        xd = "%%xmm%d" % d
        add("cvtsi2sd", 0, XMM + d, s, C_RANDOM, C_INT32, 1,
            ["xorpd	%s, %s" % (xd, xd), "cvtsi2sd %%%s, %s" % (GPR32[s], xd)])
        add("cvtsi2ss", 0, XMM + d, s, C_RANDOM, C_INT32, 1,
            ["xorps	%s, %s" % (xd, xd), "cvtsi2ss %%%s, %s" % (GPR32[s], xd)])
        add("cvtsl2sd", 0, XMM + d, s, C_RANDOM, C_INT64, 1,
            ["xorpd	%s, %s" % (xd, xd), "cvtsi2sdq %%%s, %s" % (GPR64[s], xd)])
        add("cvtsl2ss", 0, XMM + d, s, C_RANDOM, C_INT64, 1,
            ["xorps	%s, %s" % (xd, xd), "cvtsi2ssq %%%s, %s" % (GPR64[s], xd)])
    # XMM -> XMM: the clear is emitted only when rd <> r1.
    for (d, s) in ((0, 1), (14, 7), (3, 3), (9, 9)):
        xd, xs = "%%xmm%d" % d, "%%xmm%d" % s
        xor = 1 if d != s else 0
        def seq(z, ins):
            return (["%s	%s, %s" % (z, xd, xd)] if xor else []) + ["%s %s, %s" % (ins, xs, xd)]
        add("cvtss2sd", 0, XMM + d, XMM + s, C_RANDOM, C_SINGLE, xor, seq("xorpd", "cvtss2sd"))
        add("cvtsd2ss", 0, XMM + d, XMM + s, C_RANDOM, C_DOUBLE, xor, seq("xorps", "cvtsd2ss"))
        # Asmexpand: Pxorpd_f res (printed "xorpd") if res <> a1, then Psqrtsd.
        add("sqrtsd", 0, XMM + d, XMM + s, C_RANDOM, C_DOUBLE, xor, seq("xorpd", "sqrtsd	"))


def gen_zxload(rng):
    # Pmovzbq_rr / Pmovzwq_rr: printed as movzbl %r8, %r32 / movzwl %r16, %r32.
    GPR8 = ["al", "cl", "dl", "bl", "spl", "bpl", "sil", "dil"] + ["r%db" % i for i in range(8, 16)]
    GPR16 = ["ax", "cx", "dx", "bx", "sp", "bp", "si", "di"] + ["r%dw" % i for i in range(8, 16)]
    for (d, s) in ((0, 0), (0, 3), (11, 6), (2, 14), (9, 9)):
        add("movzbq_rr", 0, d, s, C_RANDOM, C_BYTE, 0,
            ["movzbl	%%%s, %%%s" % (GPR8[s], GPR32[d])])
        add("movzwq_rr", 0, d, s, C_RANDOM, C_HALF, 0,
            ["movzwl	%%%s, %%%s" % (GPR16[s], GPR32[d])])
    # Pmovzbq_rm / Pmovzwq_rm: movzbl/movzwl <addressing>, %r32, with the
    # addressing printed as TargetPrinter's [addressing]: disp(%base) or
    # disp(%base,%index,scale) with 64-bit registers.
    modes = [(7, -1, 1, 0), (6, -1, 1, 37), (6, 2, 4, -12), (13, 9, 8, 1000), (0, 1, 1, 0), (5, 12, 2, -3)]
    for (base, index, scale, disp) in modes:
        for (d, nm, ins, cls) in ((0, "movzbq_rm", "movzbl", C_BYTE), (14, "movzwq_rm", "movzwl", C_HALF)):
            if d in (base, index):
                d = 10
            a = "%d(%%%s" % (disp, GPR64[base]) + (",%%%s,%d)" % (GPR64[index], scale) if index >= 0 else ")")
            add(nm, 0, d, -1, C_RANDOM, C_RANDOM, 0, ["%s	%s, %%%s" % (ins, a, GPR32[d])],
                (base, index, scale, disp, cls))


def main():
    groups = sys.argv[1].split(",")
    rng = random.Random(int(sys.argv[2], 0))
    for g in groups:
        {"zx": gen_zx, "shift": gen_shift, "cvt": gen_cvt, "zxload": gen_zxload}[g](rng)
    weight = {}
    for e in entries:
        weight[e[0]] = weight.get(e[0], 0) + 1
    out = ["# Generated by gen_tests.py; do not edit.", "\t.text"]
    for i, (name, imm, dst, src, dc, sc, xor, lines, mem) in enumerate(entries):
        out.append("body_%d:" % i)
        out += ["\t" + l for l in lines]
        out.append("\tret")
    out.append("\t.section .data.rel.ro,\"aw\"")
    out.append("\t.globl\ttest_table")
    out.append("\t.p2align 3")
    out.append("test_table:")
    for i, (name, imm, dst, src, dc, sc, xor, lines, mem) in enumerate(entries):
        out.append("\t.quad\tname_%d, body_%d, %d, %d, %d, %d, %d, %d, %d, text_%d, %d, %d, %d, %d, %d"
                   % ((i, i, imm, dst, src, dc, sc, xor, weight[name], i) + mem))
    out.append("\t.quad\t0")
    out.append("\t.section .rodata")
    for i, (name, imm, dst, src, dc, sc, xor, lines, mem) in enumerate(entries):
        out.append("name_%d:\t.asciz \"%s\"" % (i, name))
        out.append("text_%d:\t.asciz \"%s\"" % (i, "; ".join(l.replace("\t", " ") for l in lines)))
    out.append("\t.section\t.note.GNU-stack,\"\",@progbits")
    print("\n".join(out))


main()
