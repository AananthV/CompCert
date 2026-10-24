# Unaligned 64-bit loads and stores (issue #13), in the syntax printed by
# x86/TargetPrinter.ml for Pmovq_rm_u / Pmovq_mr_u (the same as movq).
	.text
	.globl hw_ld0
hw_ld0:
	movq	0(%rdi), %rax
	ret
	.globl hw_ldx
hw_ldx:
	movq	5(%rdi,%rsi,4), %rax
	ret
	.globl hw_st0
hw_st0:
	movq	%rsi, 0(%rdi)
	ret
	.globl hw_stx
hw_stx:
	movq	%rdx, -3(%rdi,%rsi,8)
	ret
	.section .note.GNU-stack,"",@progbits
