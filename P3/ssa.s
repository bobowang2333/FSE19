	.section	__TEXT,__text,regular,pure_instructions
	.macosx_version_min 10, 12
	.globl	__Z7computejjj
	.align	4, 0x90
__Z7computejjj:                         ## @_Z7computejjj
	.cfi_startproc
## BB#0:                                ## %entry
	pushq	%rbp
Ltmp0:
	.cfi_def_cfa_offset 16
Ltmp1:
	.cfi_offset %rbp, -16
	movq	%rsp, %rbp
Ltmp2:
	.cfi_def_cfa_register %rbp
	movl	%edi, -4(%rbp)
	movl	%esi, -8(%rbp)
	movl	%edx, -12(%rbp)
	xorl	-8(%rbp), %edx
	movl	%edx, -44(%rbp)
	xorl	-4(%rbp), %edx
	movl	%edx, -16(%rbp)
	xorl	-4(%rbp), %edx
	movl	%edx, -20(%rbp)
	xorl	-44(%rbp), %edx
	movl	%edx, -24(%rbp)
	movl	-4(%rbp), %eax
	xorl	-12(%rbp), %eax
	movl	%eax, -28(%rbp)
	xorl	-44(%rbp), %eax
	movl	%eax, -32(%rbp)
	xorl	-28(%rbp), %eax
	movl	%eax, -36(%rbp)
	xorl	-24(%rbp), %eax
	movl	%eax, -40(%rbp)
	popq	%rbp
	retq
	.cfi_endproc


.subsections_via_symbols
