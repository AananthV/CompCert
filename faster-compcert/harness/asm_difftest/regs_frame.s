# void hw_run(const struct state *in, struct state *out, void (*body)(void))
#
# Loads the complete register state *in (all general-purpose registers
# except %rsp, %xmm0-%xmm15 in full, and the arithmetic flags
# CF PF AF ZF SF OF), calls body (an instruction sequence from
# regs_tests.s ending in ret), and stores the complete register state
# right after it into *out.  Neither the call nor the code around it
# changes a register or a flag, so out - in is exactly the effect of
# the sequence under test.
#
# struct state { uint64_t gpr[16]; uint64_t xmm[16][2]; uint64_t flags; }
# gpr is in encoding order: rax rcx rdx rbx rsp rbp rsi rdi r8 ... r15.

	.set	XMM, 128
	.set	FLAGS, 384
	.set	ARITH_FLAGS, 0x8d5

	.text
	.globl	hw_run
hw_run:
	pushq	%rbx
	pushq	%rbp
	pushq	%r12
	pushq	%r13
	pushq	%r14
	pushq	%r15
	movq	%rsi, out_ptr(%rip)
	movq	%rdx, body_ptr(%rip)
	.irp	i, 0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15
	movdqu	XMM+16*\i(%rdi), %xmm\i
	.endr
	pushfq
	popq	%rax
	andq	$~ARITH_FLAGS, %rax
	orq	FLAGS(%rdi), %rax
	pushq	%rax
	popfq
	movq	0(%rdi), %rax
	movq	8(%rdi), %rcx
	movq	16(%rdi), %rdx
	movq	24(%rdi), %rbx
	movq	40(%rdi), %rbp
	movq	48(%rdi), %rsi
	.irp	i, 8,9,10,11,12,13,14,15
	movq	8*\i(%rdi), %r\i
	.endr
	movq	56(%rdi), %rdi
	call	*body_ptr(%rip)
	pushfq
	pushq	%rdi
	movq	out_ptr(%rip), %rdi
	movq	%rax, 0(%rdi)
	movq	%rcx, 8(%rdi)
	movq	%rdx, 16(%rdi)
	movq	%rbx, 24(%rdi)
	movq	%rbp, 40(%rdi)
	movq	%rsi, 48(%rdi)
	.irp	i, 8,9,10,11,12,13,14,15
	movq	%r\i, 8*\i(%rdi)
	.endr
	popq	%rax
	movq	%rax, 56(%rdi)
	popq	%rax
	andq	$ARITH_FLAGS, %rax
	movq	%rax, FLAGS(%rdi)
	.irp	i, 0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15
	movdqu	%xmm\i, XMM+16*\i(%rdi)
	.endr
	popq	%r15
	popq	%r14
	popq	%r13
	popq	%r12
	popq	%rbp
	popq	%rbx
	ret

	.bss
	.p2align 3
out_ptr:	.quad	0
body_ptr:	.quad	0
	.section	.note.GNU-stack,"",@progbits
