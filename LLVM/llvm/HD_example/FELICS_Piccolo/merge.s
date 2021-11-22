	.section	__TEXT,__text,regular,pure_instructions
	.macosx_version_min 10, 11
	.globl	_Encrypt
	.align	4, 0x90
_Encrypt:                               ## @Encrypt
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
	pushq	%rbx
	subq	$72, %rsp
Ltmp3:
	.cfi_offset %rbx, -24
	movq	%rdi, -16(%rbp)
	movq	%rsi, -24(%rbp)
	movq	-16(%rbp), %rax
	movq	%rax, -40(%rbp)
	addq	$2, %rax
	movq	%rax, -48(%rbp)
	movq	-40(%rbp), %rax
	addq	$4, %rax
	movq	%rax, -56(%rbp)
	movq	-40(%rbp), %rax
	addq	$6, %rax
	movq	%rax, -64(%rbp)
	movq	-24(%rbp), %rax
	movq	%rax, -72(%rbp)
	movzwl	102(%rax), %eax
	movq	-48(%rbp), %rcx
	movzwl	(%rcx), %edx
	xorl	%eax, %edx
	movw	%dx, (%rcx)
	movq	-72(%rbp), %rax
	movzwl	100(%rax), %eax
	movq	-64(%rbp), %rcx
	movzwl	(%rcx), %edx
	xorl	%eax, %edx
	movw	%dx, (%rcx)
	movb	$0, -25(%rbp)
	jmp	LBB0_1
	.align	4, 0x90
LBB0_2:                                 ## %for.inc
                                        ##   in Loop: Header=BB0_1 Depth=1
	movq	-56(%rbp), %rax
	movzwl	(%rax), %ebx
	movq	-64(%rbp), %rax
	movzwl	(%rax), %edi
	callq	_F
                                        ## kill: AX<def> AX<kill> EAX<def>
	xorl	%ebx, %eax
	movzbl	-25(%rbp), %ecx
	movq	-72(%rbp), %rdx
	movzwl	(%rdx,%rcx,4), %ecx
	xorl	%eax, %ecx
	movq	-56(%rbp), %rax
	movw	%cx, (%rax)
	movq	-40(%rbp), %rax
	movzwl	(%rax), %ebx
	movq	-48(%rbp), %rax
	movzwl	(%rax), %edi
	callq	_F
                                        ## kill: AX<def> AX<kill> EAX<def>
	xorl	%ebx, %eax
	movzbl	-25(%rbp), %ecx
	movq	-72(%rbp), %rdx
	movzwl	2(%rdx,%rcx,4), %ecx
	xorl	%eax, %ecx
	movq	-40(%rbp), %rax
	movw	%cx, (%rax)
	movq	-64(%rbp), %rdi
	movq	-56(%rbp), %rsi
	movq	-48(%rbp), %rdx
	movq	-40(%rbp), %rcx
	callq	_RP
	incb	-25(%rbp)
LBB0_1:                                 ## %for.cond
                                        ## =>This Inner Loop Header: Depth=1
	movzbl	-25(%rbp), %eax
	cmpl	$23, %eax
	jle	LBB0_2
## BB#3:                                ## %for.end
	movq	-56(%rbp), %rax
	movzwl	(%rax), %ebx
	movq	-64(%rbp), %rax
	movzwl	(%rax), %edi
	callq	_F
                                        ## kill: AX<def> AX<kill> EAX<def>
	xorl	%ebx, %eax
	movq	-72(%rbp), %rcx
	movzwl	96(%rcx), %ecx
	xorl	%eax, %ecx
	movq	-56(%rbp), %rax
	movw	%cx, (%rax)
	movq	-40(%rbp), %rax
	movzwl	(%rax), %ebx
	movq	-48(%rbp), %rax
	movzwl	(%rax), %edi
	callq	_F
                                        ## kill: AX<def> AX<kill> EAX<def>
	xorl	%ebx, %eax
	movq	-72(%rbp), %rcx
	movzwl	98(%rcx), %ecx
	xorl	%eax, %ecx
	movq	-40(%rbp), %rax
	movw	%cx, (%rax)
	movq	-72(%rbp), %rax
	movzwl	104(%rax), %eax
	movq	-64(%rbp), %rcx
	movzwl	(%rcx), %edx
	xorl	%eax, %edx
	movw	%dx, (%rcx)
	movq	-72(%rbp), %rax
	movzwl	106(%rax), %eax
	movq	-48(%rbp), %rcx
	movzwl	(%rcx), %edx
	xorl	%eax, %edx
	movw	%dx, (%rcx)
	addq	$72, %rsp
	popq	%rbx
	popq	%rbp
	retq
	.cfi_endproc

	.globl	_RunEncryptionKeySchedule
	.align	4, 0x90
_RunEncryptionKeySchedule:              ## @RunEncryptionKeySchedule
	.cfi_startproc
## BB#0:                                ## %entry
	pushq	%rbp
Ltmp4:
	.cfi_def_cfa_offset 16
Ltmp5:
	.cfi_offset %rbp, -16
	movq	%rsp, %rbp
Ltmp6:
	.cfi_def_cfa_register %rbp
	movq	%rdi, -8(%rbp)
	movq	%rsi, -16(%rbp)
	movq	-8(%rbp), %rax
	movq	%rax, -32(%rbp)
	movq	-16(%rbp), %rax
	movq	%rax, -48(%rbp)
	movq	-16(%rbp), %rax
	leaq	100(%rax), %rcx
	movq	%rcx, -56(%rbp)
	movq	-32(%rbp), %rcx
	movzwl	(%rcx), %edx
	andl	$65280, %edx            ## imm = 0xFF00
	movzbl	2(%rcx), %ecx
	orl	%edx, %ecx
	movw	%cx, 100(%rax)
	movq	-32(%rbp), %rax
	movzwl	2(%rax), %ecx
	andl	$65280, %ecx            ## imm = 0xFF00
	movzbl	(%rax), %eax
	orl	%ecx, %eax
	movq	-56(%rbp), %rcx
	movw	%ax, 2(%rcx)
	movq	-32(%rbp), %rax
	movzwl	8(%rax), %ecx
	andl	$65280, %ecx            ## imm = 0xFF00
	movzbl	6(%rax), %eax
	orl	%ecx, %eax
	movq	-56(%rbp), %rcx
	movw	%ax, 4(%rcx)
	movq	-32(%rbp), %rax
	movzwl	6(%rax), %ecx
	andl	$65280, %ecx            ## imm = 0xFF00
	movzbl	8(%rax), %eax
	orl	%ecx, %eax
	movq	-56(%rbp), %rcx
	movw	%ax, 6(%rcx)
	movb	$0, -18(%rbp)
	movb	$0, -17(%rbp)
	leaq	_CON80(%rip), %rax
	leaq	LJTI1_0(%rip), %rcx
	jmp	LBB1_1
	.align	4, 0x90
LBB1_9:                                 ## %if.then
                                        ##   in Loop: Header=BB1_1 Depth=1
	movb	$0, -18(%rbp)
	incb	-17(%rbp)
LBB1_1:                                 ## %for.cond
                                        ## =>This Inner Loop Header: Depth=1
	movzbl	-17(%rbp), %edx
	cmpl	$24, %edx
	jg	LBB1_11
## BB#2:                                ## %for.body
                                        ##   in Loop: Header=BB1_1 Depth=1
	movzbl	-17(%rbp), %edx
	movl	(%rax,%rdx,4), %edx
	movl	%edx, -36(%rbp)
	movzbl	-18(%rbp), %edx
	cmpq	$4, %rdx
	ja	LBB1_8
## BB#3:                                ## %for.body
                                        ##   in Loop: Header=BB1_1 Depth=1
	movslq	(%rcx,%rdx,4), %rdx
	addq	%rcx, %rdx
	jmpq	*%rdx
LBB1_4:                                 ## %sw.bb
                                        ##   in Loop: Header=BB1_1 Depth=1
	movq	-32(%rbp), %rdx
	movl	4(%rdx), %edx
	jmp	LBB1_7
LBB1_6:                                 ## %sw.bb46
                                        ##   in Loop: Header=BB1_1 Depth=1
	movq	-32(%rbp), %rdx
	movl	(%rdx), %edx
LBB1_7:                                 ## %sw.epilog
                                        ##   in Loop: Header=BB1_1 Depth=1
	xorl	%edx, -36(%rbp)
	jmp	LBB1_8
LBB1_5:                                 ## %sw.bb39
                                        ##   in Loop: Header=BB1_1 Depth=1
	movq	-32(%rbp), %rdx
	movzwl	8(%rdx), %edx
	movl	%edx, %esi
	shll	$16, %esi
	orl	%edx, %esi
	xorl	%esi, -36(%rbp)
	.align	4, 0x90
LBB1_8:                                 ## %sw.epilog
                                        ##   in Loop: Header=BB1_1 Depth=1
	movl	-36(%rbp), %edx
	movzbl	-17(%rbp), %esi
	movq	-48(%rbp), %rdi
	movl	%edx, (%rdi,%rsi,4)
	movzbl	-18(%rbp), %edx
	cmpl	$4, %edx
	je	LBB1_9
## BB#10:                               ## %if.else
                                        ##   in Loop: Header=BB1_1 Depth=1
	incb	-18(%rbp)
	incb	-17(%rbp)
	jmp	LBB1_1
LBB1_11:                                ## %for.end
	popq	%rbp
	retq
	.cfi_endproc
	.align	2, 0x90
L1_0_set_4 = LBB1_4-LJTI1_0
L1_0_set_6 = LBB1_6-LJTI1_0
L1_0_set_5 = LBB1_5-LJTI1_0
LJTI1_0:
	.long	L1_0_set_4
	.long	L1_0_set_6
	.long	L1_0_set_4
	.long	L1_0_set_5
	.long	L1_0_set_6

	.globl	_polyEval
	.align	4, 0x90
_polyEval:                              ## @polyEval
	.cfi_startproc
## BB#0:                                ## %entry
	pushq	%rbp
Ltmp7:
	.cfi_def_cfa_offset 16
Ltmp8:
	.cfi_offset %rbp, -16
	movq	%rsp, %rbp
Ltmp9:
	.cfi_def_cfa_register %rbp
	movb	%dil, -1(%rbp)
	movb	%sil, -2(%rbp)
	movb	%dl, -3(%rbp)
	movb	%cl, -4(%rbp)
	movzbl	-1(%rbp), %eax
	movzbl	-2(%rbp), %ecx
	xorl	%eax, %ecx
	movzbl	-3(%rbp), %eax
	leaq	_GF16_MUL2(%rip), %rdx
	movzbl	(%rax,%rdx), %eax
	xorl	%ecx, %eax
	movzbl	-4(%rbp), %ecx
	leaq	_GF16_MUL3(%rip), %rdx
	movzbl	(%rcx,%rdx), %ecx
	xorl	%eax, %ecx
	movb	%cl, -5(%rbp)
	movzbl	-5(%rbp), %eax
	popq	%rbp
	retq
	.cfi_endproc

	.globl	_F
	.align	4, 0x90
_F:                                     ## @F
	.cfi_startproc
## BB#0:                                ## %entry
	pushq	%rbp
Ltmp10:
	.cfi_def_cfa_offset 16
Ltmp11:
	.cfi_offset %rbp, -16
	movq	%rsp, %rbp
Ltmp12:
	.cfi_def_cfa_register %rbp
	pushq	%rbx
	subq	$24, %rsp
Ltmp13:
	.cfi_offset %rbx, -24
	movw	%di, -10(%rbp)
	movzwl	-10(%rbp), %eax
	andl	$15, %eax
	movb	%al, -14(%rbp)
	movzwl	-10(%rbp), %eax
	shrl	$4, %eax
	andl	$15, %eax
	movb	%al, -13(%rbp)
	movzwl	-10(%rbp), %eax
	shrl	$8, %eax
	andl	$15, %eax
	movb	%al, -12(%rbp)
	movzwl	-10(%rbp), %eax
	shrl	$12, %eax
	movb	%al, -11(%rbp)
	movzbl	-14(%rbp), %eax
	leaq	_SBOX(%rip), %rbx
	movb	(%rax,%rbx), %al
	movb	%al, -14(%rbp)
	movzbl	-13(%rbp), %eax
	movb	(%rax,%rbx), %al
	movb	%al, -13(%rbp)
	movzbl	-12(%rbp), %eax
	movb	(%rax,%rbx), %al
	movb	%al, -12(%rbp)
	movzbl	-11(%rbp), %eax
	movb	(%rax,%rbx), %al
	movb	%al, -11(%rbp)
	movzbl	-12(%rbp), %ecx
	movzbl	-11(%rbp), %edx
	movzbl	-14(%rbp), %esi
	movzbl	-13(%rbp), %edi
	callq	_polyEval
	movb	%al, -15(%rbp)
	movzbl	-13(%rbp), %ecx
	movzbl	-12(%rbp), %edx
	movzbl	-11(%rbp), %esi
	movzbl	-14(%rbp), %edi
	callq	_polyEval
	movb	%al, -16(%rbp)
	movzbl	-14(%rbp), %ecx
	movzbl	-13(%rbp), %edx
	movzbl	-12(%rbp), %esi
	movzbl	-11(%rbp), %edi
	callq	_polyEval
	movb	%al, -17(%rbp)
	movzbl	-11(%rbp), %ecx
	movzbl	-14(%rbp), %edx
	movzbl	-13(%rbp), %esi
	movzbl	-12(%rbp), %edi
	callq	_polyEval
	movb	%al, -18(%rbp)
	movzbl	-15(%rbp), %eax
	movb	(%rax,%rbx), %al
	movb	%al, -15(%rbp)
	movzbl	-16(%rbp), %eax
	movb	(%rax,%rbx), %al
	movb	%al, -16(%rbp)
	movzbl	-17(%rbp), %eax
	movb	(%rax,%rbx), %al
	movb	%al, -17(%rbp)
	movzbl	-18(%rbp), %eax
	movb	(%rax,%rbx), %al
	movb	%al, -18(%rbp)
	movzbl	-15(%rbp), %eax
	shll	$12, %eax
	movzbl	-16(%rbp), %ecx
	shll	$8, %ecx
	orl	%eax, %ecx
	movzbl	-17(%rbp), %eax
	shll	$4, %eax
	orl	%ecx, %eax
	movzbl	-18(%rbp), %ecx
	orl	%eax, %ecx
	movzwl	%cx, %eax
	addq	$24, %rsp
	popq	%rbx
	popq	%rbp
	retq
	.cfi_endproc

	.globl	_RP
	.align	4, 0x90
_RP:                                    ## @RP
	.cfi_startproc
## BB#0:                                ## %entry
	pushq	%rbp
Ltmp14:
	.cfi_def_cfa_offset 16
Ltmp15:
	.cfi_offset %rbp, -16
	movq	%rsp, %rbp
Ltmp16:
	.cfi_def_cfa_register %rbp
	movq	%rdi, -8(%rbp)
	movq	%rsi, -16(%rbp)
	movq	%rdx, -24(%rbp)
	movq	%rcx, -32(%rbp)
	movq	-16(%rbp), %rax
	movzwl	(%rax), %eax
	andl	$65280, %eax            ## imm = 0xFF00
	movzbl	(%rcx), %ecx
	orl	%eax, %ecx
	movw	%cx, -34(%rbp)
	movq	-24(%rbp), %rax
	movzwl	(%rax), %eax
	andl	$65280, %eax            ## imm = 0xFF00
	movq	-8(%rbp), %rcx
	movzbl	(%rcx), %ecx
	orl	%eax, %ecx
	movw	%cx, -36(%rbp)
	movq	-32(%rbp), %rax
	movzwl	(%rax), %eax
	andl	$65280, %eax            ## imm = 0xFF00
	movq	-16(%rbp), %rcx
	movzbl	(%rcx), %ecx
	orl	%eax, %ecx
	movw	%cx, -38(%rbp)
	movq	-8(%rbp), %rax
	movzwl	(%rax), %eax
	andl	$65280, %eax            ## imm = 0xFF00
	movq	-24(%rbp), %rcx
	movzbl	(%rcx), %ecx
	orl	%eax, %ecx
	movw	%cx, -40(%rbp)
	movw	-34(%rbp), %ax
	movq	-8(%rbp), %rcx
	movw	%ax, (%rcx)
	movw	-36(%rbp), %ax
	movq	-16(%rbp), %rcx
	movw	%ax, (%rcx)
	movw	-38(%rbp), %ax
	movq	-24(%rbp), %rcx
	movw	%ax, (%rcx)
	movw	-40(%rbp), %ax
	movq	-32(%rbp), %rcx
	movw	%ax, (%rcx)
	popq	%rbp
	retq
	.cfi_endproc

	.globl	_main
	.align	4, 0x90
_main:                                  ## @main
	.cfi_startproc
## BB#0:                                ## %entry
	pushq	%rbp
Ltmp17:
	.cfi_def_cfa_offset 16
Ltmp18:
	.cfi_offset %rbp, -16
	movq	%rsp, %rbp
Ltmp19:
	.cfi_def_cfa_register %rbp
	pushq	%r15
	pushq	%r14
	pushq	%rbx
	subq	$56, %rsp
Ltmp20:
	.cfi_offset %rbx, -40
Ltmp21:
	.cfi_offset %r14, -32
Ltmp22:
	.cfi_offset %r15, -24
	movq	___stack_chk_guard@GOTPCREL(%rip), %r15
	movq	(%r15), %r15
	movq	%r15, -32(%rbp)
	movl	$0, -36(%rbp)
	movb	$104, -49(%rbp)
	movzbl	-49(%rbp), %eax
	movq	%rsp, -64(%rbp)
	movq	%rsp, %rsi
	addq	$15, %rax
	andq	$-16, %rax
	subq	%rax, %rsi
	movq	%rsi, %rsp
	movq	%rsi, -48(%rbp)
	leaq	_expectedKey(%rip), %rdi
	callq	_RunEncryptionKeySchedule
	movq	-48(%rbp), %rsi
	leaq	_expectedPlaintext(%rip), %r14
	movq	%r14, %rdi
	callq	_Encrypt
	movl	$0, -68(%rbp)
	leaq	L_.str(%rip), %rbx
	jmp	LBB5_1
	.align	4, 0x90
LBB5_2:                                 ## %for.body
                                        ##   in Loop: Header=BB5_1 Depth=1
	movl	-68(%rbp), %eax
	movzbl	(%rax,%r14), %esi
	xorl	%eax, %eax
	movq	%rbx, %rdi
	callq	_printf
	incl	-68(%rbp)
LBB5_1:                                 ## %for.cond
                                        ## =>This Inner Loop Header: Depth=1
	cmpl	$7, -68(%rbp)
	jbe	LBB5_2
## BB#3:                                ## %for.end
	leaq	_expectedCiphertext(%rip), %rdi
	leaq	_expectedPlaintext(%rip), %rsi
	movl	$8, %edx
	callq	_memcmp
	testl	%eax, %eax
	jne	LBB5_5
## BB#4:                                ## %if.then
	leaq	L_.str1(%rip), %rdi
	jmp	LBB5_6
LBB5_5:                                 ## %if.else
	leaq	L_.str2(%rip), %rdi
LBB5_6:                                 ## %if.end
	xorl	%eax, %eax
	callq	_printf
	movq	-64(%rbp), %rax
	movq	%rax, %rsp
	movl	-36(%rbp), %eax
	cmpq	-32(%rbp), %r15
	jne	LBB5_8
## BB#7:                                ## %if.end
	leaq	-24(%rbp), %rsp
	popq	%rbx
	popq	%r14
	popq	%r15
	popq	%rbp
	retq
LBB5_8:                                 ## %if.end
	callq	___stack_chk_fail
	.cfi_endproc

	.section	__TEXT,__const
	.globl	_SBOX                   ## @SBOX
	.align	4
_SBOX:
	.ascii	"\016\004\013\002\003\b\000\t\001\n\007\017\006\f\005\r"

	.globl	_GF16_MUL2              ## @GF16_MUL2
	.align	4
_GF16_MUL2:
	.ascii	"\000\002\004\006\b\n\f\016\003\001\007\005\013\t\017\r"

	.globl	_GF16_MUL3              ## @GF16_MUL3
	.align	4
_GF16_MUL3:
	.ascii	"\000\003\006\005\f\017\n\t\013\b\r\016\007\004\001\002"

	.globl	_CON80                  ## @CON80
	.align	4
_CON80:
	.long	691865372               ## 0x293d071c
	.long	624828186               ## 0x253e1f1a
	.long	557782808               ## 0x213f1718
	.long	1027092246              ## 0x3d382f16
	.long	960046868               ## 0x39392714
	.long	893009682               ## 0x353a3f12
	.long	825964304               ## 0x313b3710
	.long	221531918               ## 0xd344f0e
	.long	154486540               ## 0x935470c
	.long	87449354                ## 0x5365f0a
	.long	20403976                ## 0x1375708
	.long	489713414               ## 0x1d306f06
	.long	422668036               ## 0x19316704
	.long	355630850               ## 0x15327f02
	.long	288585472               ## 0x11337700
	.long	1831636798              ## 0x6d2c8f3e
	.long	1764591420              ## 0x692d873c
	.long	1697554234              ## 0x652e9f3a
	.long	1630508856              ## 0x612f9738
	.long	2099818294              ## 0x7d28af36
	.long	2032772916              ## 0x7929a734
	.long	1965735730              ## 0x752abf32
	.long	1898690352              ## 0x712bb730
	.long	1294257966              ## 0x4d24cf2e
	.long	1227212588              ## 0x4925c72c

	.section	__DATA,__data
	.globl	_expectedPlaintext      ## @expectedPlaintext
_expectedPlaintext:
	.ascii	"\357\315\253\211gE#\001"

	.globl	_expectedKey            ## @expectedKey
_expectedKey:
	.ascii	"\021\0003\"UDwf\231\210"

	.globl	_expectedCiphertext     ## @expectedCiphertext
_expectedCiphertext:
	.ascii	"V@\3705\231\377+\215"

	.section	__TEXT,__cstring,cstring_literals
L_.str:                                 ## @.str
	.asciz	"%x\n"

L_.str1:                                ## @.str1
	.asciz	"SUCCESS!\n"

L_.str2:                                ## @.str2
	.asciz	"FAILURE!\n"


.subsections_via_symbols
