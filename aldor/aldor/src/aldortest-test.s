	.file	"test.c"
	.text
.Ltext0:
	.file 0 "/home/kfp/devel/aldor/aldor/aldor/src" "test.c"
	.section	.rodata
.LC0:
	.string	"show"
	.text
	.globl	main
	.type	main, @function
main:
.LFB0:
	.file 1 "test.c"
	.loc 1 19 1
	.cfi_startproc
	endbr64
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$16, %rsp
	movl	%edi, -4(%rbp)
	movq	%rsi, -16(%rbp)
	.loc 1 20 5
	cmpl	$1, -4(%rbp)
	jne	.L4
	.loc 1 21 3
	leaq	.LC0(%rip), %rax
	movq	%rax, %rdi
	call	testSelf
	jmp	.L3
.L5:
	.loc 1 23 22 discriminator 2
	addq	$8, -16(%rbp)
	movq	-16(%rbp), %rax
	movq	(%rax), %rax
	movq	%rax, %rdi
	call	testSelf
.L4:
	.loc 1 23 14 discriminator 1
	movl	-4(%rbp), %eax
	leal	-1(%rax), %edx
	movl	%edx, -4(%rbp)
	.loc 1 23 17 discriminator 1
	cmpl	$1, %eax
	jg	.L5
.L3:
	.loc 1 25 9
	movl	$0, %eax
	.loc 1 26 1
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE0:
	.size	main, .-main
	.section	.rodata
.LC1:
	.string	"cport"
.LC2:
	.string	"opsys"
.LC3:
	.string	"store1a"
.LC4:
	.string	"store1b"
.LC5:
	.string	"store1c"
.LC6:
	.string	"store1d"
.LC7:
	.string	"store2"
.LC8:
	.string	"store3"
.LC9:
	.string	"util"
.LC10:
	.string	"float"
.LC11:
	.string	"fluid"
.LC12:
	.string	"format"
.LC13:
	.string	"bigint"
.LC14:
	.string	"bitv"
.LC15:
	.string	"btree"
.LC16:
	.string	"buffer"
.LC17:
	.string	"dnf"
.LC18:
	.string	"fname"
.LC19:
	.string	"list"
.LC20:
	.string	"priq"
.LC21:
	.string	"string"
.LC22:
	.string	"symbol"
.LC23:
	.string	"table"
.LC24:
	.string	"xfloat"
.LC25:
	.string	"ccode"
.LC26:
	.string	"msg"
.LC27:
	.string	"file"
.LC28:
	.string	"link"
	.section	.data.rel,"aw"
	.align 32
	.type	suite, @object
	.size	suite, 480
suite:
	.quad	.LC0
	.quad	testShow
	.quad	.LC1
	.quad	testCPort
	.quad	.LC2
	.quad	testOpsys
	.quad	.LC3
	.quad	testStore1a
	.quad	.LC4
	.quad	testStore1b
	.quad	.LC5
	.quad	testStore1c
	.quad	.LC6
	.quad	testStore1d
	.quad	.LC7
	.quad	testStore2
	.quad	.LC8
	.quad	testStore3
	.quad	.LC9
	.quad	testUtil
	.quad	.LC10
	.quad	testFloat
	.quad	.LC11
	.quad	testFluid
	.quad	.LC12
	.quad	testFormat
	.quad	.LC13
	.quad	testBigint
	.quad	.LC14
	.quad	testBitv
	.quad	.LC15
	.quad	testBtree
	.quad	.LC16
	.quad	testBuffer
	.quad	.LC17
	.quad	testDnf
	.quad	.LC18
	.quad	testFname
	.quad	.LC19
	.quad	testList
	.quad	.LC20
	.quad	testPriq
	.quad	.LC21
	.quad	testString
	.quad	.LC22
	.quad	testSymbol
	.quad	.LC23
	.quad	testTable
	.quad	.LC24
	.quad	testXFloat
	.quad	.LC25
	.quad	testCCode
	.quad	.LC26
	.quad	testMsg
	.quad	.LC27
	.quad	testFile
	.quad	.LC28
	.quad	testLink
	.quad	0
	.quad	0
	.section	.rodata
.LC29:
	.string	"out of memory"
.LC30:
	.string	"using non-allocated space"
	.align 8
.LC31:
	.string	"can't build internal structure"
.LC32:
	.string	"unexpected"
	.align 8
.LC33:
	.string	"Storage allocation error (%s).\n"
	.text
	.globl	testSelfStoHandler
	.type	testSelfStoHandler, @function
testSelfStoHandler:
.LFB1:
	.loc 1 124 1
	.cfi_startproc
	endbr64
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$32, %rsp
	movl	%edi, -20(%rbp)
	.loc 1 127 2
	cmpl	$3, -20(%rbp)
	je	.L8
	cmpl	$3, -20(%rbp)
	jg	.L9
	cmpl	$1, -20(%rbp)
	je	.L10
	cmpl	$2, -20(%rbp)
	je	.L11
	jmp	.L9
.L10:
	.loc 1 128 14
	leaq	.LC29(%rip), %rax
	movq	%rax, -8(%rbp)
	.loc 1 128 33
	jmp	.L12
.L11:
	.loc 1 129 14
	leaq	.LC30(%rip), %rax
	movq	%rax, -8(%rbp)
	.loc 1 129 45
	jmp	.L12
.L8:
	.loc 1 130 14
	leaq	.LC31(%rip), %rax
	movq	%rax, -8(%rbp)
	.loc 1 130 50
	jmp	.L12
.L9:
	.loc 1 131 15
	leaq	.LC32(%rip), %rax
	movq	%rax, -8(%rbp)
	.loc 1 131 31
	nop
.L12:
	.loc 1 133 2
	movq	stderr(%rip), %rax
	movq	-8(%rbp), %rdx
	leaq	.LC33(%rip), %rcx
	movq	%rcx, %rsi
	movq	%rax, %rdi
	movl	$0, %eax
	call	fprintf@PLT
	.loc 1 134 2
	call	exitFailure@PLT
	.cfi_endproc
.LFE1:
	.size	testSelfStoHandler, .-testSelfStoHandler
	.section	.rodata
.LC34:
	.string	"all"
.LC35:
	.string	"\nTest \"%s\" not found.\n"
	.text
	.globl	testSelf
	.type	testSelf, @function
testSelf:
.LFB2:
	.loc 1 140 1
	.cfi_startproc
	endbr64
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$32, %rsp
	movq	%rdi, -24(%rbp)
	.loc 1 145 7
	leaq	testSelfStoHandler(%rip), %rax
	movq	%rax, %rdi
	call	stoSetHandler@PLT
	movq	%rax, -8(%rbp)
	.loc 1 147 6
	movq	-24(%rbp), %rax
	leaq	.LC34(%rip), %rdx
	movq	%rdx, %rsi
	movq	%rax, %rdi
	call	strcmp@PLT
	.loc 1 147 5
	testl	%eax, %eax
	jne	.L14
	.loc 1 148 9
	movl	$0, -12(%rbp)
	.loc 1 148 3
	jmp	.L15
.L16:
	.loc 1 149 4 discriminator 3
	movl	-12(%rbp), %eax
	cltq
	salq	$4, %rax
	movq	%rax, %rdx
	leaq	8+suite(%rip), %rax
	movq	(%rdx,%rax), %rdx
	movl	-12(%rbp), %eax
	cltq
	salq	$4, %rax
	movq	%rax, %rcx
	leaq	suite(%rip), %rax
	movq	(%rcx,%rax), %rax
	movq	%rdx, %rsi
	movq	%rax, %rdi
	call	testRun
	.loc 1 148 34 discriminator 3
	addl	$1, -12(%rbp)
.L15:
	.loc 1 148 21 discriminator 1
	movl	-12(%rbp), %eax
	cltq
	salq	$4, %rax
	movq	%rax, %rdx
	leaq	suite(%rip), %rax
	movq	(%rdx,%rax), %rax
	.loc 1 148 27 discriminator 1
	testq	%rax, %rax
	jne	.L16
	jmp	.L17
.L14:
	.loc 1 152 9
	movl	$0, -12(%rbp)
	.loc 1 152 3
	jmp	.L18
.L21:
	.loc 1 153 33
	movl	-12(%rbp), %eax
	cltq
	salq	$4, %rax
	movq	%rax, %rdx
	leaq	suite(%rip), %rax
	movq	(%rdx,%rax), %rdx
	.loc 1 153 8
	movq	-24(%rbp), %rax
	movq	%rdx, %rsi
	movq	%rax, %rdi
	call	strcmp@PLT
	.loc 1 153 7
	testl	%eax, %eax
	je	.L23
	.loc 1 152 34 discriminator 2
	addl	$1, -12(%rbp)
.L18:
	.loc 1 152 21 discriminator 1
	movl	-12(%rbp), %eax
	cltq
	salq	$4, %rax
	movq	%rax, %rdx
	leaq	suite(%rip), %rax
	movq	(%rdx,%rax), %rax
	.loc 1 152 27 discriminator 1
	testq	%rax, %rax
	jne	.L21
	jmp	.L20
.L23:
	.loc 1 153 46
	nop
.L20:
	.loc 1 155 15
	movl	-12(%rbp), %eax
	cltq
	salq	$4, %rax
	movq	%rax, %rdx
	leaq	suite(%rip), %rax
	movq	(%rdx,%rax), %rax
	.loc 1 155 6
	testq	%rax, %rax
	jne	.L22
	.loc 1 156 4
	movq	-24(%rbp), %rax
	movq	%rax, %rsi
	leaq	.LC35(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	jmp	.L17
.L22:
	.loc 1 158 4
	movl	-12(%rbp), %eax
	cltq
	salq	$4, %rax
	movq	%rax, %rdx
	leaq	8+suite(%rip), %rax
	movq	(%rdx,%rax), %rdx
	movl	-12(%rbp), %eax
	cltq
	salq	$4, %rax
	movq	%rax, %rcx
	leaq	suite(%rip), %rax
	movq	(%rcx,%rax), %rax
	movq	%rdx, %rsi
	movq	%rax, %rdi
	call	testRun
.L17:
	.loc 1 160 2
	movq	-8(%rbp), %rax
	movq	%rax, %rdi
	call	stoSetHandler@PLT
	.loc 1 161 1
	nop
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE2:
	.size	testSelf, .-testSelf
	.section	.rodata
	.align 8
.LC36:
	.string	"==========================================================="
.LC37:
	.string	"===  Test \"%s\"\n"
.LC38:
	.string	"\nTest \"%s\" completed.\n"
	.text
	.globl	testRun
	.type	testRun, @function
testRun:
.LFB3:
	.loc 1 166 1
	.cfi_startproc
	endbr64
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$16, %rsp
	movq	%rdi, -8(%rbp)
	movq	%rsi, -16(%rbp)
	.loc 1 167 2
	leaq	.LC36(%rip), %rax
	movq	%rax, %rdi
	call	puts@PLT
	.loc 1 168 2
	movq	-8(%rbp), %rax
	movq	%rax, %rsi
	leaq	.LC37(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	.loc 1 169 2
	leaq	.LC36(%rip), %rax
	movq	%rax, %rdi
	call	puts@PLT
	.loc 1 171 9
	call	osInit@PLT
	.loc 1 173 2
	call	testStartNetStore
	.loc 1 175 2
	movq	-16(%rbp), %rax
	call	*%rax
.LVL0:
	.loc 1 177 2
	movq	-8(%rbp), %rax
	movq	%rax, %rsi
	leaq	.LC38(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	.loc 1 178 2
	call	testShowNetStore
	.loc 1 179 1
	nop
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE3:
	.size	testRun, .-testRun
	.local	alloc0
	.comm	alloc0,8,8
	.local	free0
	.comm	free0,8,8
	.local	gc0
	.comm	gc0,8,8
	.globl	testStartNetStore
	.type	testStartNetStore, @function
testStartNetStore:
.LFB4:
	.loc 1 186 1
	.cfi_startproc
	endbr64
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	.loc 1 187 9
	movq	stoBytesAlloc(%rip), %rax
	movq	%rax, alloc0(%rip)
	.loc 1 187 32
	movq	stoBytesFree(%rip), %rax
	movq	%rax, free0(%rip)
	.loc 1 187 52
	movq	stoBytesGc(%rip), %rax
	movq	%rax, gc0(%rip)
	.loc 1 188 1
	nop
	popq	%rbp
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE4:
	.size	testStartNetStore, .-testStartNetStore
	.section	.rodata
.LC39:
	.string	"Net store allocated is %ld\n"
	.text
	.globl	testShowNetStore
	.type	testShowNetStore, @function
testShowNetStore:
.LFB5:
	.loc 1 192 1
	.cfi_startproc
	endbr64
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$32, %rsp
	.loc 1 193 30
	movq	stoBytesAlloc(%rip), %rax
	movq	alloc0(%rip), %rdx
	subq	%rdx, %rax
	.loc 1 193 7
	movq	%rax, -24(%rbp)
	.loc 1 194 28
	movq	stoBytesFree(%rip), %rax
	movq	free0(%rip), %rdx
	subq	%rdx, %rax
	.loc 1 194 7
	movq	%rax, -16(%rbp)
	.loc 1 195 24
	movq	stoBytesGc(%rip), %rax
	movq	gc0(%rip), %rdx
	subq	%rdx, %rax
	.loc 1 195 7
	movq	%rax, -8(%rbp)
	.loc 1 197 48
	movq	-24(%rbp), %rax
	subq	-16(%rbp), %rax
	.loc 1 197 2
	subq	-8(%rbp), %rax
	movq	%rax, %rsi
	leaq	.LC39(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	.loc 1 198 1
	nop
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE5:
	.size	testShowNetStore, .-testShowNetStore
	.section	.rodata
.LC40:
	.string	"\nThe tests are:"
.LC41:
	.string	" \"%s\""
	.text
	.globl	testShow
	.type	testShow, @function
testShow:
.LFB6:
	.loc 1 203 1
	.cfi_startproc
	endbr64
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$16, %rsp
	.loc 1 206 2
	leaq	.LC40(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	.loc 1 207 9
	movl	$0, -4(%rbp)
	.loc 1 207 2
	jmp	.L28
.L29:
	.loc 1 207 39 discriminator 3
	movl	-4(%rbp), %eax
	cltq
	salq	$4, %rax
	movq	%rax, %rdx
	leaq	suite(%rip), %rax
	movq	(%rdx,%rax), %rax
	movq	%rax, %rsi
	leaq	.LC41(%rip), %rax
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	.loc 1 207 35 discriminator 3
	addl	$1, -4(%rbp)
.L28:
	.loc 1 207 22 discriminator 1
	movl	-4(%rbp), %eax
	cltq
	salq	$4, %rax
	movq	%rax, %rdx
	leaq	suite(%rip), %rax
	movq	(%rdx,%rax), %rax
	.loc 1 207 28 discriminator 1
	testq	%rax, %rax
	jne	.L29
	.loc 1 208 2
	movl	$10, %edi
	call	putchar@PLT
	.loc 1 209 1
	nop
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE6:
	.size	testShow, .-testShow
.Letext0:
	.file 2 "/usr/include/x86_64-linux-gnu/bits/types.h"
	.file 3 "/usr/lib/gcc/x86_64-linux-gnu/11/include/stddef.h"
	.file 4 "/usr/include/x86_64-linux-gnu/bits/types/struct_FILE.h"
	.file 5 "/usr/include/x86_64-linux-gnu/bits/types/FILE.h"
	.file 6 "cport.h"
	.file 7 "/usr/include/stdio.h"
	.file 8 "store.h"
	.file 9 "/usr/include/string.h"
	.file 10 "opsys.h"
	.file 11 "util.h"
	.section	.debug_info,"",@progbits
.Ldebug_info0:
	.long	0x667
	.value	0x5
	.byte	0x1
	.byte	0x8
	.long	.Ldebug_abbrev0
	.uleb128 0x16
	.long	.LASF108
	.byte	0xc
	.long	.LASF0
	.long	.LASF1
	.quad	.Ltext0
	.quad	.Letext0-.Ltext0
	.long	.Ldebug_line0
	.uleb128 0x17
	.byte	0x4
	.byte	0x5
	.string	"int"
	.uleb128 0x4
	.byte	0x1
	.byte	0x8
	.long	.LASF2
	.uleb128 0x4
	.byte	0x2
	.byte	0x7
	.long	.LASF3
	.uleb128 0x4
	.byte	0x4
	.byte	0x7
	.long	.LASF4
	.uleb128 0x4
	.byte	0x8
	.byte	0x7
	.long	.LASF5
	.uleb128 0x4
	.byte	0x1
	.byte	0x6
	.long	.LASF6
	.uleb128 0x4
	.byte	0x2
	.byte	0x5
	.long	.LASF7
	.uleb128 0x4
	.byte	0x8
	.byte	0x5
	.long	.LASF8
	.uleb128 0x7
	.long	.LASF9
	.byte	0x2
	.byte	0x98
	.byte	0x12
	.long	0x5f
	.uleb128 0x7
	.long	.LASF10
	.byte	0x2
	.byte	0x99
	.byte	0x12
	.long	0x5f
	.uleb128 0x18
	.byte	0x8
	.uleb128 0x3
	.long	0x85
	.uleb128 0x4
	.byte	0x1
	.byte	0x6
	.long	.LASF11
	.uleb128 0x19
	.long	0x85
	.uleb128 0x4
	.byte	0x4
	.byte	0x4
	.long	.LASF12
	.uleb128 0x4
	.byte	0x8
	.byte	0x4
	.long	.LASF13
	.uleb128 0x7
	.long	.LASF14
	.byte	0x3
	.byte	0xd1
	.byte	0x1b
	.long	0x4a
	.uleb128 0x10
	.long	.LASF57
	.byte	0xd8
	.byte	0x4
	.byte	0x31
	.long	0x231
	.uleb128 0x1
	.long	.LASF15
	.byte	0x4
	.byte	0x33
	.byte	0x7
	.long	0x2e
	.byte	0
	.uleb128 0x1
	.long	.LASF16
	.byte	0x4
	.byte	0x36
	.byte	0x9
	.long	0x80
	.byte	0x8
	.uleb128 0x1
	.long	.LASF17
	.byte	0x4
	.byte	0x37
	.byte	0x9
	.long	0x80
	.byte	0x10
	.uleb128 0x1
	.long	.LASF18
	.byte	0x4
	.byte	0x38
	.byte	0x9
	.long	0x80
	.byte	0x18
	.uleb128 0x1
	.long	.LASF19
	.byte	0x4
	.byte	0x39
	.byte	0x9
	.long	0x80
	.byte	0x20
	.uleb128 0x1
	.long	.LASF20
	.byte	0x4
	.byte	0x3a
	.byte	0x9
	.long	0x80
	.byte	0x28
	.uleb128 0x1
	.long	.LASF21
	.byte	0x4
	.byte	0x3b
	.byte	0x9
	.long	0x80
	.byte	0x30
	.uleb128 0x1
	.long	.LASF22
	.byte	0x4
	.byte	0x3c
	.byte	0x9
	.long	0x80
	.byte	0x38
	.uleb128 0x1
	.long	.LASF23
	.byte	0x4
	.byte	0x3d
	.byte	0x9
	.long	0x80
	.byte	0x40
	.uleb128 0x1
	.long	.LASF24
	.byte	0x4
	.byte	0x40
	.byte	0x9
	.long	0x80
	.byte	0x48
	.uleb128 0x1
	.long	.LASF25
	.byte	0x4
	.byte	0x41
	.byte	0x9
	.long	0x80
	.byte	0x50
	.uleb128 0x1
	.long	.LASF26
	.byte	0x4
	.byte	0x42
	.byte	0x9
	.long	0x80
	.byte	0x58
	.uleb128 0x1
	.long	.LASF27
	.byte	0x4
	.byte	0x44
	.byte	0x16
	.long	0x24a
	.byte	0x60
	.uleb128 0x1
	.long	.LASF28
	.byte	0x4
	.byte	0x46
	.byte	0x14
	.long	0x24f
	.byte	0x68
	.uleb128 0x1
	.long	.LASF29
	.byte	0x4
	.byte	0x48
	.byte	0x7
	.long	0x2e
	.byte	0x70
	.uleb128 0x1
	.long	.LASF30
	.byte	0x4
	.byte	0x49
	.byte	0x7
	.long	0x2e
	.byte	0x74
	.uleb128 0x1
	.long	.LASF31
	.byte	0x4
	.byte	0x4a
	.byte	0xb
	.long	0x66
	.byte	0x78
	.uleb128 0x1
	.long	.LASF32
	.byte	0x4
	.byte	0x4d
	.byte	0x12
	.long	0x3c
	.byte	0x80
	.uleb128 0x1
	.long	.LASF33
	.byte	0x4
	.byte	0x4e
	.byte	0xf
	.long	0x51
	.byte	0x82
	.uleb128 0x1
	.long	.LASF34
	.byte	0x4
	.byte	0x4f
	.byte	0x8
	.long	0x254
	.byte	0x83
	.uleb128 0x1
	.long	.LASF35
	.byte	0x4
	.byte	0x51
	.byte	0xf
	.long	0x264
	.byte	0x88
	.uleb128 0x1
	.long	.LASF36
	.byte	0x4
	.byte	0x59
	.byte	0xd
	.long	0x72
	.byte	0x90
	.uleb128 0x1
	.long	.LASF37
	.byte	0x4
	.byte	0x5b
	.byte	0x17
	.long	0x26e
	.byte	0x98
	.uleb128 0x1
	.long	.LASF38
	.byte	0x4
	.byte	0x5c
	.byte	0x19
	.long	0x278
	.byte	0xa0
	.uleb128 0x1
	.long	.LASF39
	.byte	0x4
	.byte	0x5d
	.byte	0x14
	.long	0x24f
	.byte	0xa8
	.uleb128 0x1
	.long	.LASF40
	.byte	0x4
	.byte	0x5e
	.byte	0x9
	.long	0x7e
	.byte	0xb0
	.uleb128 0x1
	.long	.LASF41
	.byte	0x4
	.byte	0x5f
	.byte	0xa
	.long	0x9f
	.byte	0xb8
	.uleb128 0x1
	.long	.LASF42
	.byte	0x4
	.byte	0x60
	.byte	0x7
	.long	0x2e
	.byte	0xc0
	.uleb128 0x1
	.long	.LASF43
	.byte	0x4
	.byte	0x62
	.byte	0x8
	.long	0x27d
	.byte	0xc4
	.byte	0
	.uleb128 0x7
	.long	.LASF44
	.byte	0x5
	.byte	0x7
	.byte	0x19
	.long	0xab
	.uleb128 0x1a
	.long	.LASF109
	.byte	0x4
	.byte	0x2b
	.byte	0xe
	.uleb128 0xc
	.long	.LASF45
	.uleb128 0x3
	.long	0x245
	.uleb128 0x3
	.long	0xab
	.uleb128 0xd
	.long	0x85
	.long	0x264
	.uleb128 0xe
	.long	0x4a
	.byte	0
	.byte	0
	.uleb128 0x3
	.long	0x23d
	.uleb128 0xc
	.long	.LASF46
	.uleb128 0x3
	.long	0x269
	.uleb128 0xc
	.long	.LASF47
	.uleb128 0x3
	.long	0x273
	.uleb128 0xd
	.long	0x85
	.long	0x28d
	.uleb128 0xe
	.long	0x4a
	.byte	0x13
	.byte	0
	.uleb128 0x3
	.long	0x231
	.uleb128 0x11
	.long	0x28d
	.uleb128 0xa
	.long	.LASF52
	.byte	0x7
	.byte	0x8b
	.long	0x28d
	.uleb128 0x4
	.byte	0x8
	.byte	0x5
	.long	.LASF48
	.uleb128 0x3
	.long	0x8c
	.uleb128 0x11
	.long	0x2a9
	.uleb128 0xf
	.long	.LASF49
	.value	0x13a
	.byte	0x17
	.long	0x4a
	.uleb128 0xf
	.long	.LASF50
	.value	0x16a
	.byte	0xf
	.long	0x80
	.uleb128 0xf
	.long	.LASF51
	.value	0x17a
	.byte	0x10
	.long	0x98
	.uleb128 0xa
	.long	.LASF53
	.byte	0x8
	.byte	0x1c
	.long	0x2b3
	.uleb128 0xa
	.long	.LASF54
	.byte	0x8
	.byte	0x1d
	.long	0x2b3
	.uleb128 0xa
	.long	.LASF55
	.byte	0x8
	.byte	0x1e
	.long	0x2b3
	.uleb128 0x7
	.long	.LASF56
	.byte	0x8
	.byte	0x5d
	.byte	0x1c
	.long	0x304
	.uleb128 0x3
	.long	0x309
	.uleb128 0x1b
	.long	0x318
	.long	0x318
	.uleb128 0x5
	.long	0x2e
	.byte	0
	.uleb128 0x3
	.long	0x2cb
	.uleb128 0x10
	.long	.LASF58
	.byte	0x10
	.byte	0x1
	.byte	0x48
	.long	0x344
	.uleb128 0x1
	.long	.LASF59
	.byte	0x1
	.byte	0x49
	.byte	0x8
	.long	0x80
	.byte	0
	.uleb128 0x1c
	.string	"fun"
	.byte	0x1
	.byte	0x4a
	.byte	0x9
	.long	0x345
	.byte	0x8
	.byte	0
	.uleb128 0x1d
	.uleb128 0x3
	.long	0x344
	.uleb128 0xd
	.long	0x31d
	.long	0x35a
	.uleb128 0xe
	.long	0x4a
	.byte	0x1d
	.byte	0
	.uleb128 0x8
	.long	.LASF60
	.byte	0x4d
	.byte	0x14
	.long	0x34a
	.uleb128 0x9
	.byte	0x3
	.quad	suite
	.uleb128 0x8
	.long	.LASF61
	.byte	0xb6
	.byte	0xd
	.long	0x5f
	.uleb128 0x9
	.byte	0x3
	.quad	alloc0
	.uleb128 0x8
	.long	.LASF62
	.byte	0xb6
	.byte	0x15
	.long	0x5f
	.uleb128 0x9
	.byte	0x3
	.quad	free0
	.uleb128 0x6
	.string	"gc0"
	.byte	0xb6
	.byte	0x1c
	.long	0x5f
	.uleb128 0x9
	.byte	0x3
	.quad	gc0
	.uleb128 0x2
	.long	.LASF67
	.byte	0xa
	.byte	0x15
	.uleb128 0x12
	.long	.LASF63
	.value	0x15e
	.long	0x2e
	.long	0x3cb
	.uleb128 0x5
	.long	0x2a9
	.uleb128 0x13
	.byte	0
	.uleb128 0x14
	.long	.LASF64
	.byte	0x9
	.byte	0x8c
	.byte	0xc
	.long	0x2e
	.long	0x3e6
	.uleb128 0x5
	.long	0x2a9
	.uleb128 0x5
	.long	0x2a9
	.byte	0
	.uleb128 0x14
	.long	.LASF65
	.byte	0x8
	.byte	0x5f
	.byte	0x14
	.long	0x2f8
	.long	0x3fc
	.uleb128 0x5
	.long	0x2f8
	.byte	0
	.uleb128 0x1e
	.long	.LASF110
	.byte	0xb
	.byte	0x15
	.byte	0xd
	.uleb128 0x12
	.long	.LASF66
	.value	0x158
	.long	0x2e
	.long	0x41f
	.uleb128 0x5
	.long	0x292
	.uleb128 0x5
	.long	0x2ae
	.uleb128 0x13
	.byte	0
	.uleb128 0x2
	.long	.LASF68
	.byte	0x1
	.byte	0x45
	.uleb128 0x2
	.long	.LASF69
	.byte	0x1
	.byte	0x43
	.uleb128 0x2
	.long	.LASF70
	.byte	0x1
	.byte	0x42
	.uleb128 0x2
	.long	.LASF71
	.byte	0x1
	.byte	0x41
	.uleb128 0x2
	.long	.LASF72
	.byte	0x1
	.byte	0x3f
	.uleb128 0x2
	.long	.LASF73
	.byte	0x1
	.byte	0x3e
	.uleb128 0x2
	.long	.LASF74
	.byte	0x1
	.byte	0x3d
	.uleb128 0x2
	.long	.LASF75
	.byte	0x1
	.byte	0x3c
	.uleb128 0x2
	.long	.LASF76
	.byte	0x1
	.byte	0x3b
	.uleb128 0x2
	.long	.LASF77
	.byte	0x1
	.byte	0x3a
	.uleb128 0x2
	.long	.LASF78
	.byte	0x1
	.byte	0x39
	.uleb128 0x2
	.long	.LASF79
	.byte	0x1
	.byte	0x38
	.uleb128 0x2
	.long	.LASF80
	.byte	0x1
	.byte	0x37
	.uleb128 0x2
	.long	.LASF81
	.byte	0x1
	.byte	0x36
	.uleb128 0x2
	.long	.LASF82
	.byte	0x1
	.byte	0x35
	.uleb128 0x2
	.long	.LASF83
	.byte	0x1
	.byte	0x34
	.uleb128 0x2
	.long	.LASF84
	.byte	0x1
	.byte	0x32
	.uleb128 0x2
	.long	.LASF85
	.byte	0x1
	.byte	0x31
	.uleb128 0x2
	.long	.LASF86
	.byte	0x1
	.byte	0x30
	.uleb128 0x2
	.long	.LASF87
	.byte	0x1
	.byte	0x2f
	.uleb128 0x2
	.long	.LASF88
	.byte	0x1
	.byte	0x2d
	.uleb128 0x2
	.long	.LASF89
	.byte	0x1
	.byte	0x2c
	.uleb128 0x2
	.long	.LASF90
	.byte	0x1
	.byte	0x2b
	.uleb128 0x2
	.long	.LASF91
	.byte	0x1
	.byte	0x2a
	.uleb128 0x2
	.long	.LASF92
	.byte	0x1
	.byte	0x29
	.uleb128 0x2
	.long	.LASF93
	.byte	0x1
	.byte	0x28
	.uleb128 0x2
	.long	.LASF94
	.byte	0x1
	.byte	0x26
	.uleb128 0x2
	.long	.LASF95
	.byte	0x1
	.byte	0x25
	.uleb128 0xb
	.long	.LASF96
	.byte	0xca
	.quad	.LFB6
	.quad	.LFE6-.LFB6
	.uleb128 0x1
	.byte	0x9c
	.long	0x50c
	.uleb128 0x6
	.string	"i"
	.byte	0xcc
	.byte	0x6
	.long	0x2e
	.uleb128 0x2
	.byte	0x91
	.sleb128 -20
	.byte	0
	.uleb128 0xb
	.long	.LASF97
	.byte	0xbf
	.quad	.LFB5
	.quad	.LFE5-.LFB5
	.uleb128 0x1
	.byte	0x9c
	.long	0x553
	.uleb128 0x8
	.long	.LASF98
	.byte	0xc1
	.byte	0x7
	.long	0x5f
	.uleb128 0x2
	.byte	0x91
	.sleb128 -40
	.uleb128 0x8
	.long	.LASF99
	.byte	0xc2
	.byte	0x7
	.long	0x5f
	.uleb128 0x2
	.byte	0x91
	.sleb128 -32
	.uleb128 0x6
	.string	"gcD"
	.byte	0xc3
	.byte	0x7
	.long	0x5f
	.uleb128 0x2
	.byte	0x91
	.sleb128 -24
	.byte	0
	.uleb128 0x1f
	.long	.LASF111
	.byte	0x1
	.byte	0xb9
	.byte	0x1
	.quad	.LFB4
	.quad	.LFE4-.LFB4
	.uleb128 0x1
	.byte	0x9c
	.uleb128 0xb
	.long	.LASF100
	.byte	0xa5
	.quad	.LFB3
	.quad	.LFE3-.LFB3
	.uleb128 0x1
	.byte	0x9c
	.long	0x5a7
	.uleb128 0x9
	.long	.LASF59
	.byte	0xa5
	.byte	0x10
	.long	0x2bf
	.uleb128 0x2
	.byte	0x91
	.sleb128 -24
	.uleb128 0x20
	.string	"fun"
	.byte	0x1
	.byte	0xa5
	.byte	0x1d
	.long	0x345
	.uleb128 0x2
	.byte	0x91
	.sleb128 -32
	.byte	0
	.uleb128 0xb
	.long	.LASF101
	.byte	0x8b
	.quad	.LFB2
	.quad	.LFE2-.LFB2
	.uleb128 0x1
	.byte	0x9c
	.long	0x5eb
	.uleb128 0x9
	.long	.LASF102
	.byte	0x8b
	.byte	0x11
	.long	0x2bf
	.uleb128 0x2
	.byte	0x91
	.sleb128 -40
	.uleb128 0x6
	.string	"i"
	.byte	0x8d
	.byte	0x6
	.long	0x2e
	.uleb128 0x2
	.byte	0x91
	.sleb128 -28
	.uleb128 0x6
	.string	"h0"
	.byte	0x8e
	.byte	0xe
	.long	0x2f8
	.uleb128 0x2
	.byte	0x91
	.sleb128 -24
	.byte	0
	.uleb128 0x15
	.long	.LASF104
	.byte	0x7b
	.long	0x318
	.quad	.LFB1
	.quad	.LFE1-.LFB1
	.uleb128 0x1
	.byte	0x9c
	.long	0x628
	.uleb128 0x9
	.long	.LASF103
	.byte	0x7b
	.byte	0x18
	.long	0x2e
	.uleb128 0x2
	.byte	0x91
	.sleb128 -36
	.uleb128 0x6
	.string	"msg"
	.byte	0x7d
	.byte	0x9
	.long	0x2bf
	.uleb128 0x2
	.byte	0x91
	.sleb128 -24
	.byte	0
	.uleb128 0x15
	.long	.LASF105
	.byte	0x12
	.long	0x2e
	.quad	.LFB0
	.quad	.LFE0-.LFB0
	.uleb128 0x1
	.byte	0x9c
	.long	0x665
	.uleb128 0x9
	.long	.LASF106
	.byte	0x12
	.byte	0xa
	.long	0x2e
	.uleb128 0x2
	.byte	0x91
	.sleb128 -20
	.uleb128 0x9
	.long	.LASF107
	.byte	0x12
	.byte	0x17
	.long	0x665
	.uleb128 0x2
	.byte	0x91
	.sleb128 -32
	.byte	0
	.uleb128 0x3
	.long	0x80
	.byte	0
	.section	.debug_abbrev,"",@progbits
.Ldebug_abbrev0:
	.uleb128 0x1
	.uleb128 0xd
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x38
	.uleb128 0xb
	.byte	0
	.byte	0
	.uleb128 0x2
	.uleb128 0x2e
	.byte	0
	.uleb128 0x3f
	.uleb128 0x19
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0x21
	.sleb128 13
	.uleb128 0x27
	.uleb128 0x19
	.uleb128 0x3c
	.uleb128 0x19
	.byte	0
	.byte	0
	.uleb128 0x3
	.uleb128 0xf
	.byte	0
	.uleb128 0xb
	.uleb128 0x21
	.sleb128 8
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x4
	.uleb128 0x24
	.byte	0
	.uleb128 0xb
	.uleb128 0xb
	.uleb128 0x3e
	.uleb128 0xb
	.uleb128 0x3
	.uleb128 0xe
	.byte	0
	.byte	0
	.uleb128 0x5
	.uleb128 0x5
	.byte	0
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x6
	.uleb128 0x34
	.byte	0
	.uleb128 0x3
	.uleb128 0x8
	.uleb128 0x3a
	.uleb128 0x21
	.sleb128 1
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x2
	.uleb128 0x18
	.byte	0
	.byte	0
	.uleb128 0x7
	.uleb128 0x16
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x8
	.uleb128 0x34
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0x21
	.sleb128 1
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x2
	.uleb128 0x18
	.byte	0
	.byte	0
	.uleb128 0x9
	.uleb128 0x5
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0x21
	.sleb128 1
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x2
	.uleb128 0x18
	.byte	0
	.byte	0
	.uleb128 0xa
	.uleb128 0x34
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0x21
	.sleb128 14
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x3f
	.uleb128 0x19
	.uleb128 0x3c
	.uleb128 0x19
	.byte	0
	.byte	0
	.uleb128 0xb
	.uleb128 0x2e
	.byte	0x1
	.uleb128 0x3f
	.uleb128 0x19
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0x21
	.sleb128 1
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0x21
	.sleb128 1
	.uleb128 0x27
	.uleb128 0x19
	.uleb128 0x11
	.uleb128 0x1
	.uleb128 0x12
	.uleb128 0x7
	.uleb128 0x40
	.uleb128 0x18
	.uleb128 0x7c
	.uleb128 0x19
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0xc
	.uleb128 0x13
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3c
	.uleb128 0x19
	.byte	0
	.byte	0
	.uleb128 0xd
	.uleb128 0x1
	.byte	0x1
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0xe
	.uleb128 0x21
	.byte	0
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x2f
	.uleb128 0xb
	.byte	0
	.byte	0
	.uleb128 0xf
	.uleb128 0x16
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0x21
	.sleb128 6
	.uleb128 0x3b
	.uleb128 0x5
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x10
	.uleb128 0x13
	.byte	0x1
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0xb
	.uleb128 0xb
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0x21
	.sleb128 8
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x11
	.uleb128 0x37
	.byte	0
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x12
	.uleb128 0x2e
	.byte	0x1
	.uleb128 0x3f
	.uleb128 0x19
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0x21
	.sleb128 7
	.uleb128 0x3b
	.uleb128 0x5
	.uleb128 0x39
	.uleb128 0x21
	.sleb128 12
	.uleb128 0x27
	.uleb128 0x19
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x3c
	.uleb128 0x19
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x13
	.uleb128 0x18
	.byte	0
	.byte	0
	.byte	0
	.uleb128 0x14
	.uleb128 0x2e
	.byte	0x1
	.uleb128 0x3f
	.uleb128 0x19
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x27
	.uleb128 0x19
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x3c
	.uleb128 0x19
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x15
	.uleb128 0x2e
	.byte	0x1
	.uleb128 0x3f
	.uleb128 0x19
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0x21
	.sleb128 1
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0x21
	.sleb128 1
	.uleb128 0x27
	.uleb128 0x19
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x11
	.uleb128 0x1
	.uleb128 0x12
	.uleb128 0x7
	.uleb128 0x40
	.uleb128 0x18
	.uleb128 0x7c
	.uleb128 0x19
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x16
	.uleb128 0x11
	.byte	0x1
	.uleb128 0x25
	.uleb128 0xe
	.uleb128 0x13
	.uleb128 0xb
	.uleb128 0x3
	.uleb128 0x1f
	.uleb128 0x1b
	.uleb128 0x1f
	.uleb128 0x11
	.uleb128 0x1
	.uleb128 0x12
	.uleb128 0x7
	.uleb128 0x10
	.uleb128 0x17
	.byte	0
	.byte	0
	.uleb128 0x17
	.uleb128 0x24
	.byte	0
	.uleb128 0xb
	.uleb128 0xb
	.uleb128 0x3e
	.uleb128 0xb
	.uleb128 0x3
	.uleb128 0x8
	.byte	0
	.byte	0
	.uleb128 0x18
	.uleb128 0xf
	.byte	0
	.uleb128 0xb
	.uleb128 0xb
	.byte	0
	.byte	0
	.uleb128 0x19
	.uleb128 0x26
	.byte	0
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x1a
	.uleb128 0x16
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.byte	0
	.byte	0
	.uleb128 0x1b
	.uleb128 0x15
	.byte	0x1
	.uleb128 0x27
	.uleb128 0x19
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x1c
	.uleb128 0xd
	.byte	0
	.uleb128 0x3
	.uleb128 0x8
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x38
	.uleb128 0xb
	.byte	0
	.byte	0
	.uleb128 0x1d
	.uleb128 0x15
	.byte	0
	.uleb128 0x27
	.uleb128 0x19
	.byte	0
	.byte	0
	.uleb128 0x1e
	.uleb128 0x2e
	.byte	0
	.uleb128 0x3f
	.uleb128 0x19
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x27
	.uleb128 0x19
	.uleb128 0x87
	.uleb128 0x19
	.uleb128 0x3c
	.uleb128 0x19
	.byte	0
	.byte	0
	.uleb128 0x1f
	.uleb128 0x2e
	.byte	0
	.uleb128 0x3f
	.uleb128 0x19
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x27
	.uleb128 0x19
	.uleb128 0x11
	.uleb128 0x1
	.uleb128 0x12
	.uleb128 0x7
	.uleb128 0x40
	.uleb128 0x18
	.uleb128 0x7a
	.uleb128 0x19
	.byte	0
	.byte	0
	.uleb128 0x20
	.uleb128 0x5
	.byte	0
	.uleb128 0x3
	.uleb128 0x8
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x2
	.uleb128 0x18
	.byte	0
	.byte	0
	.byte	0
	.section	.debug_aranges,"",@progbits
	.long	0x2c
	.value	0x2
	.long	.Ldebug_info0
	.byte	0x8
	.byte	0
	.value	0
	.value	0
	.quad	.Ltext0
	.quad	.Letext0-.Ltext0
	.quad	0
	.quad	0
	.section	.debug_line,"",@progbits
.Ldebug_line0:
	.section	.debug_str,"MS",@progbits,1
.LASF56:
	.string	"StoErrorFun"
.LASF85:
	.string	"testFluid"
.LASF80:
	.string	"testBuffer"
.LASF13:
	.string	"double"
.LASF57:
	.string	"_IO_FILE"
.LASF29:
	.string	"_fileno"
.LASF67:
	.string	"osInit"
.LASF73:
	.string	"testTable"
.LASF26:
	.string	"_IO_save_end"
.LASF103:
	.string	"errnum"
.LASF7:
	.string	"short int"
.LASF14:
	.string	"size_t"
.LASF53:
	.string	"stoBytesAlloc"
.LASF36:
	.string	"_offset"
.LASF97:
	.string	"testShowNetStore"
.LASF82:
	.string	"testBitv"
.LASF105:
	.string	"main"
.LASF83:
	.string	"testBigint"
.LASF110:
	.string	"exitFailure"
.LASF15:
	.string	"_flags"
.LASF90:
	.string	"testStore1d"
.LASF30:
	.string	"_flags2"
.LASF22:
	.string	"_IO_buf_base"
.LASF35:
	.string	"_lock"
.LASF27:
	.string	"_markers"
.LASF64:
	.string	"strcmp"
.LASF40:
	.string	"_freeres_buf"
.LASF102:
	.string	"testName"
.LASF74:
	.string	"testSymbol"
.LASF89:
	.string	"testStore2"
.LASF88:
	.string	"testStore3"
.LASF65:
	.string	"stoSetHandler"
.LASF61:
	.string	"alloc0"
.LASF6:
	.string	"signed char"
.LASF12:
	.string	"float"
.LASF96:
	.string	"testShow"
.LASF52:
	.string	"stderr"
.LASF48:
	.string	"long long int"
.LASF62:
	.string	"free0"
.LASF11:
	.string	"char"
.LASF72:
	.string	"testXFloat"
.LASF98:
	.string	"allocD"
.LASF63:
	.string	"printf"
.LASF32:
	.string	"_cur_column"
.LASF60:
	.string	"suite"
.LASF66:
	.string	"fprintf"
.LASF111:
	.string	"testStartNetStore"
.LASF107:
	.string	"argv"
.LASF77:
	.string	"testList"
.LASF20:
	.string	"_IO_write_ptr"
.LASF31:
	.string	"_old_offset"
.LASF49:
	.string	"ULong"
.LASF2:
	.string	"unsigned char"
.LASF93:
	.string	"testStore1a"
.LASF92:
	.string	"testStore1b"
.LASF91:
	.string	"testStore1c"
.LASF106:
	.string	"argc"
.LASF104:
	.string	"testSelfStoHandler"
.LASF37:
	.string	"_codecvt"
.LASF79:
	.string	"testDnf"
.LASF4:
	.string	"unsigned int"
.LASF45:
	.string	"_IO_marker"
.LASF34:
	.string	"_shortbuf"
.LASF68:
	.string	"testLink"
.LASF17:
	.string	"_IO_read_end"
.LASF19:
	.string	"_IO_write_base"
.LASF43:
	.string	"_unused2"
.LASF50:
	.string	"String"
.LASF23:
	.string	"_IO_buf_end"
.LASF55:
	.string	"stoBytesGc"
.LASF84:
	.string	"testFormat"
.LASF86:
	.string	"testFloat"
.LASF8:
	.string	"long int"
.LASF38:
	.string	"_wide_data"
.LASF39:
	.string	"_freeres_list"
.LASF10:
	.string	"__off64_t"
.LASF75:
	.string	"testString"
.LASF41:
	.string	"__pad5"
.LASF58:
	.string	"test"
.LASF71:
	.string	"testCCode"
.LASF108:
	.string	"GNU C99 11.2.0 -mtune=generic -march=x86-64 -g -g -O2 -O0 -std=c99 -fasynchronous-unwind-tables -fstack-protector-strong -fstack-clash-protection -fcf-protection"
.LASF5:
	.string	"long unsigned int"
.LASF76:
	.string	"testPriq"
.LASF21:
	.string	"_IO_write_end"
.LASF94:
	.string	"testOpsys"
.LASF42:
	.string	"_mode"
.LASF51:
	.string	"MostAlignedType"
.LASF28:
	.string	"_chain"
.LASF101:
	.string	"testSelf"
.LASF87:
	.string	"testUtil"
.LASF100:
	.string	"testRun"
.LASF9:
	.string	"__off_t"
.LASF25:
	.string	"_IO_backup_base"
.LASF70:
	.string	"testMsg"
.LASF3:
	.string	"short unsigned int"
.LASF46:
	.string	"_IO_codecvt"
.LASF18:
	.string	"_IO_read_base"
.LASF59:
	.string	"name"
.LASF95:
	.string	"testCPort"
.LASF33:
	.string	"_vtable_offset"
.LASF47:
	.string	"_IO_wide_data"
.LASF99:
	.string	"freeD"
.LASF24:
	.string	"_IO_save_base"
.LASF78:
	.string	"testFname"
.LASF44:
	.string	"FILE"
.LASF16:
	.string	"_IO_read_ptr"
.LASF54:
	.string	"stoBytesFree"
.LASF69:
	.string	"testFile"
.LASF81:
	.string	"testBtree"
.LASF109:
	.string	"_IO_lock_t"
	.section	.debug_line_str,"MS",@progbits,1
.LASF1:
	.string	"/home/kfp/devel/aldor/aldor/aldor/src"
.LASF0:
	.string	"test.c"
	.ident	"GCC: (Ubuntu 11.2.0-7ubuntu2) 11.2.0"
	.section	.note.GNU-stack,"",@progbits
	.section	.note.gnu.property,"a"
	.align 8
	.long	1f - 0f
	.long	4f - 1f
	.long	5
0:
	.string	"GNU"
1:
	.align 8
	.long	0xc0000002
	.long	3f - 2f
2:
	.long	0x3
3:
	.align 8
4:
