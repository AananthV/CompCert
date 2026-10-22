# The instructions under test, in the exact syntax printed by
# x86/TargetPrinter.ml, with the memory operand at 0(%rdi).
#   double hw_<op>sd(const double *m, double x)   -- x in %xmm0
#   int    hw_<op>l (const int *m, int x)          -- x in %esi
	.text
	.globl	hw_addsd, hw_subsd, hw_mulsd, hw_divsd
	.globl	hw_addl, hw_xorl, hw_andl, hw_orl
hw_addsd:
	addsd	0(%rdi), %xmm0
	ret
hw_subsd:
	subsd	0(%rdi), %xmm0
	ret
hw_mulsd:
	mulsd	0(%rdi), %xmm0
	ret
hw_divsd:
	divsd	0(%rdi), %xmm0
	ret
hw_addl:
	movl	%esi, %eax
	addl	0(%rdi), %eax
	ret
hw_xorl:
	movl	%esi, %eax
	xorl	0(%rdi), %eax
	ret
hw_andl:
	movl	%esi, %eax
	andl	0(%rdi), %eax
	ret
hw_orl:
	movl	%esi, %eax
	orl	0(%rdi), %eax
	ret
	.section	.note.GNU-stack,"",@progbits
