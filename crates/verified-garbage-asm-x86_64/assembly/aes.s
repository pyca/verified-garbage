// The functions of `src/aes.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_expand_key_aesni:
	pcmpeqd xmm5, xmm5
	psrld xmm5, 31
	movdqa xmm6, xmm5
	paddd xmm6, xmm6
	movdqa xmm7, xmm6
	paddd xmm7, xmm7
	movdqa xmm8, xmm7
	paddd xmm8, xmm8
	movdqa xmm9, xmm8
	paddd xmm9, xmm9
	movdqa xmm10, xmm9
	paddd xmm10, xmm10
	movdqa xmm11, xmm10
	paddd xmm11, xmm11
	movdqa xmm12, xmm11
	paddd xmm12, xmm12
	cmp rsi, 24
	je 20f
	cmp rsi, 32
	je 22f
	movdqa xmm13, xmm5
	pxor xmm13, xmm6
	pxor xmm13, xmm8
	pxor xmm13, xmm9
	movdqa xmm14, xmm13
	paddd xmm14, xmm14
	movdqu xmm1, XMMWORD PTR [rdi]
	movdqu XMMWORD PTR [rdx], xmm1
	pshufd xmm3, xmm1, 255
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm5
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+16], xmm1
	pshufd xmm3, xmm1, 255
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm6
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+32], xmm1
	pshufd xmm3, xmm1, 255
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm7
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+48], xmm1
	pshufd xmm3, xmm1, 255
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm8
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+64], xmm1
	pshufd xmm3, xmm1, 255
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm9
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+80], xmm1
	pshufd xmm3, xmm1, 255
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm10
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+96], xmm1
	pshufd xmm3, xmm1, 255
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm11
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+112], xmm1
	pshufd xmm3, xmm1, 255
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm12
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+128], xmm1
	pshufd xmm3, xmm1, 255
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm13
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+144], xmm1
	pshufd xmm3, xmm1, 255
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm14
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+160], xmm1
	jmp 23f
22:
	pxor xmm15, xmm15
	movdqu xmm1, XMMWORD PTR [rdi]
	movdqu xmm2, XMMWORD PTR [rdi+16]
	movdqu XMMWORD PTR [rdx], xmm1
	movdqu XMMWORD PTR [rdx+16], xmm2
	pshufd xmm3, xmm2, 255
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm5
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+32], xmm1
	pshufd xmm3, xmm1, 255
	aesenclast xmm3, xmm15
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	movdqa xmm4, xmm2
	pslldq xmm4, 8
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [rdx+48], xmm2
	pshufd xmm3, xmm2, 255
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm6
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+64], xmm1
	pshufd xmm3, xmm1, 255
	aesenclast xmm3, xmm15
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	movdqa xmm4, xmm2
	pslldq xmm4, 8
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [rdx+80], xmm2
	pshufd xmm3, xmm2, 255
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm7
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+96], xmm1
	pshufd xmm3, xmm1, 255
	aesenclast xmm3, xmm15
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	movdqa xmm4, xmm2
	pslldq xmm4, 8
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [rdx+112], xmm2
	pshufd xmm3, xmm2, 255
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm8
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+128], xmm1
	pshufd xmm3, xmm1, 255
	aesenclast xmm3, xmm15
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	movdqa xmm4, xmm2
	pslldq xmm4, 8
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [rdx+144], xmm2
	pshufd xmm3, xmm2, 255
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm9
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+160], xmm1
	pshufd xmm3, xmm1, 255
	aesenclast xmm3, xmm15
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	movdqa xmm4, xmm2
	pslldq xmm4, 8
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [rdx+176], xmm2
	pshufd xmm3, xmm2, 255
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm10
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+192], xmm1
	pshufd xmm3, xmm1, 255
	aesenclast xmm3, xmm15
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	movdqa xmm4, xmm2
	pslldq xmm4, 8
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [rdx+208], xmm2
	pshufd xmm3, xmm2, 255
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm11
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+224], xmm1
23:
	jmp 21f
20:
	movdqu xmm1, XMMWORD PTR [rdi]
	movdqu xmm2, XMMWORD PTR [rdi+8]
	psrldq xmm2, 8
	movdqu XMMWORD PTR [rdx], xmm1
	movdqu XMMWORD PTR [rdx+16], xmm2
	pshufd xmm3, xmm2, 85
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm5
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+24], xmm1
	pshufd xmm3, xmm1, 255
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [rdx+40], xmm2
	pshufd xmm3, xmm2, 85
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm6
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+48], xmm1
	pshufd xmm3, xmm1, 255
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [rdx+64], xmm2
	pshufd xmm3, xmm2, 85
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm7
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+72], xmm1
	pshufd xmm3, xmm1, 255
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [rdx+88], xmm2
	pshufd xmm3, xmm2, 85
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm8
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+96], xmm1
	pshufd xmm3, xmm1, 255
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [rdx+112], xmm2
	pshufd xmm3, xmm2, 85
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm9
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+120], xmm1
	pshufd xmm3, xmm1, 255
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [rdx+136], xmm2
	pshufd xmm3, xmm2, 85
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm10
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+144], xmm1
	pshufd xmm3, xmm1, 255
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [rdx+160], xmm2
	pshufd xmm3, xmm2, 85
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm11
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+168], xmm1
	pshufd xmm3, xmm1, 255
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [rdx+184], xmm2
	pshufd xmm3, xmm2, 85
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm12
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+192], xmm1
21:
	ret
	.p2align 6

vg_aes_expand_key:
	lea rsp, [rsp-520]
	mov rcx, rsp
	add rcx, 8
	mov r9, rcx
	mov QWORD PTR [r9+384], rbx
	mov QWORD PTR [r9+392], rbp
	mov QWORD PTR [r9+400], r12
	mov QWORD PTR [r9+408], r13
	mov QWORD PTR [r9+416], r14
	mov QWORD PTR [r9+424], r15
	mov r8, rsi
20:
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [rdx], rax
	add rdi, 8
	add rdx, 8
	sub rsi, 8
	jne 20b
	sub rsi, r8
	mov rdi, rsi
	shr r8, 2
	mov rax, r8
	add r8, r8
	add r8, rax
	add r8, 28
	movabs rax, 1
	mov QWORD PTR [r9+432], rax
21:
	mov eax, DWORD PTR [rdx-4]
	cmp rdi, rsi
	je 22f
	cmp rdi, -16
	je 24f
	jmp 25f
24:
	cmp rsi, -32
	je 26f
	jmp 27f
26:
	movabs r14, 6148914691236517205
	mov QWORD PTR [r9+32], r14
	movabs r14, 3689348814741910323
	mov QWORD PTR [r9+40], r14
	movabs r14, 1085102592571150095
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+32]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+32]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+32]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+32]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+40]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+40]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+40]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+40]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+48]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+48]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+48]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+48]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	movabs r14, -1
	mov QWORD PTR [r9], r14
	mov r14, r10
	xor r14, rcx
	mov r15, r13
	xor r15, rbx
	mov QWORD PTR [r9+8], rbp
	mov rbp, r13
	xor rbp, r10
	mov QWORD PTR [r9+16], rbp
	mov rbp, r13
	xor rbp, rcx
	xor r11, r12
	mov QWORD PTR [r9+24], r12
	mov r12, r11
	xor r12, rax
	xor r10, r12
	mov QWORD PTR [r9+32], r10
	mov r10, r15
	xor r10, r14
	mov QWORD PTR [r9+40], r14
	mov r14, r12
	xor r14, r13
	xor rbx, r12
	mov QWORD PTR [r9+48], r14
	mov r14, rbx
	xor r14, rbp
	mov QWORD PTR [r9+56], rbx
	mov rbx, QWORD PTR [r9+8]
	xor rbx, r10
	xor rcx, rbx
	xor rbx, QWORD PTR [r9+24]
	mov QWORD PTR [r9+24], r12
	mov r12, rcx
	xor r12, rax
	mov QWORD PTR [r9+8], r12
	mov r12, rcx
	xor r12, r11
	mov QWORD PTR [r9+64], r14
	mov r14, rbx
	xor r14, QWORD PTR [r9+16]
	mov QWORD PTR [r9+72], rbx
	mov rbx, rax
	xor rbx, r14
	mov QWORD PTR [r9+80], rbx
	mov rbx, r12
	xor rbx, r14
	mov QWORD PTR [r9+88], rbx
	mov rbx, r12
	xor rbx, rbp
	xor r11, r14
	mov QWORD PTR [r9+96], rbx
	mov rbx, r15
	xor rbx, r11
	xor r13, r11
	mov QWORD PTR [r9+104], r13
	mov r13, r10
	and r13, rcx
	mov QWORD PTR [r9+112], r10
	mov r10, QWORD PTR [r9+64]
	and r10, QWORD PTR [r9+8]
	xor r10, r13
	mov QWORD PTR [r9+120], rcx
	mov rcx, QWORD PTR [r9+32]
	and rcx, rax
	xor rcx, r13
	mov r13, r15
	and r13, r11
	mov QWORD PTR [r9+128], r15
	mov r15, QWORD PTR [r9+56]
	and r15, QWORD PTR [r9+24]
	xor r15, r13
	mov QWORD PTR [r9+136], r11
	mov r11, QWORD PTR [r9+48]
	and r11, QWORD PTR [r9+80]
	xor r11, r13
	mov r13, QWORD PTR [r9+16]
	and r13, r14
	mov QWORD PTR [r9+144], r14
	mov r14, QWORD PTR [r9+40]
	and r14, QWORD PTR [r9+88]
	xor r14, r13
	mov QWORD PTR [r9+152], rax
	mov rax, rbp
	and rax, r12
	xor rax, r13
	xor r10, r14
	xor rcx, rax
	xor r15, r14
	xor r11, rax
	xor r10, QWORD PTR [r9+72]
	xor rcx, QWORD PTR [r9+96]
	xor r15, rbx
	xor r11, QWORD PTR [r9+104]
	mov rbx, r10
	xor rbx, rcx
	and r10, r15
	mov rax, r11
	xor rax, r10
	mov r14, rbx
	and r14, rax
	xor r14, rcx
	mov r13, r15
	xor r13, r11
	xor rcx, r10
	and rcx, r13
	xor rcx, r11
	xor r15, rcx
	mov r13, rax
	xor r13, rcx
	and r11, r13
	xor r15, r11
	xor rax, r11
	and rax, r14
	xor rbx, rax
	mov rax, rbx
	xor rax, r15
	mov r11, r14
	xor r11, rcx
	mov r13, r14
	xor r13, rbx
	mov r10, rcx
	xor r10, r15
	mov QWORD PTR [r9+104], rbp
	mov rbp, r11
	xor rbp, rax
	mov QWORD PTR [r9+96], rax
	mov rax, r10
	and rax, QWORD PTR [r9+120]
	mov QWORD PTR [r9+120], rax
	mov rax, r15
	and rax, QWORD PTR [r9+8]
	mov QWORD PTR [r9+8], rax
	mov rax, rcx
	and rax, QWORD PTR [r9+152]
	mov QWORD PTR [r9+152], rax
	mov rax, r13
	and rax, QWORD PTR [r9+136]
	mov QWORD PTR [r9+136], rax
	mov rax, rbx
	and rax, QWORD PTR [r9+24]
	mov QWORD PTR [r9+24], rax
	mov rax, r14
	and rax, QWORD PTR [r9+80]
	mov QWORD PTR [r9+80], rax
	mov rax, r11
	and rax, QWORD PTR [r9+144]
	mov QWORD PTR [r9+144], rax
	mov rax, rbp
	and rax, QWORD PTR [r9+88]
	and r12, QWORD PTR [r9+96]
	and r10, QWORD PTR [r9+112]
	and r15, QWORD PTR [r9+64]
	and rcx, QWORD PTR [r9+32]
	and r13, QWORD PTR [r9+128]
	and rbx, QWORD PTR [r9+56]
	and r14, QWORD PTR [r9+48]
	and r11, QWORD PTR [r9+16]
	and rbp, QWORD PTR [r9+40]
	mov QWORD PTR [r9+40], r14
	mov r14, QWORD PTR [r9+96]
	and r14, QWORD PTR [r9+104]
	xor r11, rbp
	xor rcx, r15
	xor rbx, QWORD PTR [r9+80]
	xor r10, r15
	mov r15, QWORD PTR [r9+152]
	xor r15, r13
	mov QWORD PTR [r9+104], rcx
	mov rcx, QWORD PTR [r9+152]
	xor rcx, QWORD PTR [r9+80]
	xor r12, rax
	mov QWORD PTR [r9+80], rcx
	mov rcx, QWORD PTR [r9+120]
	xor rcx, QWORD PTR [r9+136]
	xor rax, QWORD PTR [r9+144]
	xor rbp, r14
	xor r13, rbx
	xor r15, rcx
	mov r14, QWORD PTR [r9+24]
	xor r14, r11
	xor rax, QWORD PTR [r9+136]
	xor r11, r15
	xor r15, QWORD PTR [r9+40]
	xor r12, r14
	xor r10, r14
	mov r14, QWORD PTR [r9+24]
	xor r14, rax
	xor r15, r12
	mov QWORD PTR [r9+24], rbp
	mov rbp, QWORD PTR [r9+8]
	xor rbp, r10
	xor rax, r10
	xor r13, r12
	xor r13, QWORD PTR [r9]
	xor rbx, r11
	xor rbx, QWORD PTR [r9]
	mov r11, r14
	xor r11, r15
	xor rcx, rbp
	xor rbp, QWORD PTR [r9+80]
	xor r15, QWORD PTR [r9+104]
	xor r14, rcx
	xor r14, QWORD PTR [r9]
	xor r11, QWORD PTR [r9+24]
	xor r11, QWORD PTR [r9]
	mov QWORD PTR [r9+24], r13
	mov r13, rax
	mov r12, r14
	mov r10, rcx
	mov rcx, r15
	mov QWORD PTR [r9+104], rbx
	mov rbx, QWORD PTR [r9+24]
	mov rax, QWORD PTR [r9+104]
	movabs r14, 6148914691236517205
	mov QWORD PTR [r9+32], r14
	movabs r14, 3689348814741910323
	mov QWORD PTR [r9+40], r14
	movabs r14, 1085102592571150095
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+32]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+32]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+32]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+32]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+40]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+40]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+40]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+40]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+48]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+48]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+48]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+48]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
27:
25:
	jmp 23f
22:
	movabs r14, 6148914691236517205
	mov QWORD PTR [r9+32], r14
	movabs r14, 3689348814741910323
	mov QWORD PTR [r9+40], r14
	movabs r14, 1085102592571150095
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+32]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+32]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+32]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+32]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+40]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+40]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+40]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+40]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+48]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+48]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+48]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+48]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	movabs r14, -1
	mov QWORD PTR [r9], r14
	mov r14, r10
	xor r14, rcx
	mov r15, r13
	xor r15, rbx
	mov QWORD PTR [r9+8], rbp
	mov rbp, r13
	xor rbp, r10
	mov QWORD PTR [r9+16], rbp
	mov rbp, r13
	xor rbp, rcx
	xor r11, r12
	mov QWORD PTR [r9+24], r12
	mov r12, r11
	xor r12, rax
	xor r10, r12
	mov QWORD PTR [r9+32], r10
	mov r10, r15
	xor r10, r14
	mov QWORD PTR [r9+40], r14
	mov r14, r12
	xor r14, r13
	xor rbx, r12
	mov QWORD PTR [r9+48], r14
	mov r14, rbx
	xor r14, rbp
	mov QWORD PTR [r9+56], rbx
	mov rbx, QWORD PTR [r9+8]
	xor rbx, r10
	xor rcx, rbx
	xor rbx, QWORD PTR [r9+24]
	mov QWORD PTR [r9+24], r12
	mov r12, rcx
	xor r12, rax
	mov QWORD PTR [r9+8], r12
	mov r12, rcx
	xor r12, r11
	mov QWORD PTR [r9+64], r14
	mov r14, rbx
	xor r14, QWORD PTR [r9+16]
	mov QWORD PTR [r9+72], rbx
	mov rbx, rax
	xor rbx, r14
	mov QWORD PTR [r9+80], rbx
	mov rbx, r12
	xor rbx, r14
	mov QWORD PTR [r9+88], rbx
	mov rbx, r12
	xor rbx, rbp
	xor r11, r14
	mov QWORD PTR [r9+96], rbx
	mov rbx, r15
	xor rbx, r11
	xor r13, r11
	mov QWORD PTR [r9+104], r13
	mov r13, r10
	and r13, rcx
	mov QWORD PTR [r9+112], r10
	mov r10, QWORD PTR [r9+64]
	and r10, QWORD PTR [r9+8]
	xor r10, r13
	mov QWORD PTR [r9+120], rcx
	mov rcx, QWORD PTR [r9+32]
	and rcx, rax
	xor rcx, r13
	mov r13, r15
	and r13, r11
	mov QWORD PTR [r9+128], r15
	mov r15, QWORD PTR [r9+56]
	and r15, QWORD PTR [r9+24]
	xor r15, r13
	mov QWORD PTR [r9+136], r11
	mov r11, QWORD PTR [r9+48]
	and r11, QWORD PTR [r9+80]
	xor r11, r13
	mov r13, QWORD PTR [r9+16]
	and r13, r14
	mov QWORD PTR [r9+144], r14
	mov r14, QWORD PTR [r9+40]
	and r14, QWORD PTR [r9+88]
	xor r14, r13
	mov QWORD PTR [r9+152], rax
	mov rax, rbp
	and rax, r12
	xor rax, r13
	xor r10, r14
	xor rcx, rax
	xor r15, r14
	xor r11, rax
	xor r10, QWORD PTR [r9+72]
	xor rcx, QWORD PTR [r9+96]
	xor r15, rbx
	xor r11, QWORD PTR [r9+104]
	mov rbx, r10
	xor rbx, rcx
	and r10, r15
	mov rax, r11
	xor rax, r10
	mov r14, rbx
	and r14, rax
	xor r14, rcx
	mov r13, r15
	xor r13, r11
	xor rcx, r10
	and rcx, r13
	xor rcx, r11
	xor r15, rcx
	mov r13, rax
	xor r13, rcx
	and r11, r13
	xor r15, r11
	xor rax, r11
	and rax, r14
	xor rbx, rax
	mov rax, rbx
	xor rax, r15
	mov r11, r14
	xor r11, rcx
	mov r13, r14
	xor r13, rbx
	mov r10, rcx
	xor r10, r15
	mov QWORD PTR [r9+104], rbp
	mov rbp, r11
	xor rbp, rax
	mov QWORD PTR [r9+96], rax
	mov rax, r10
	and rax, QWORD PTR [r9+120]
	mov QWORD PTR [r9+120], rax
	mov rax, r15
	and rax, QWORD PTR [r9+8]
	mov QWORD PTR [r9+8], rax
	mov rax, rcx
	and rax, QWORD PTR [r9+152]
	mov QWORD PTR [r9+152], rax
	mov rax, r13
	and rax, QWORD PTR [r9+136]
	mov QWORD PTR [r9+136], rax
	mov rax, rbx
	and rax, QWORD PTR [r9+24]
	mov QWORD PTR [r9+24], rax
	mov rax, r14
	and rax, QWORD PTR [r9+80]
	mov QWORD PTR [r9+80], rax
	mov rax, r11
	and rax, QWORD PTR [r9+144]
	mov QWORD PTR [r9+144], rax
	mov rax, rbp
	and rax, QWORD PTR [r9+88]
	and r12, QWORD PTR [r9+96]
	and r10, QWORD PTR [r9+112]
	and r15, QWORD PTR [r9+64]
	and rcx, QWORD PTR [r9+32]
	and r13, QWORD PTR [r9+128]
	and rbx, QWORD PTR [r9+56]
	and r14, QWORD PTR [r9+48]
	and r11, QWORD PTR [r9+16]
	and rbp, QWORD PTR [r9+40]
	mov QWORD PTR [r9+40], r14
	mov r14, QWORD PTR [r9+96]
	and r14, QWORD PTR [r9+104]
	xor r11, rbp
	xor rcx, r15
	xor rbx, QWORD PTR [r9+80]
	xor r10, r15
	mov r15, QWORD PTR [r9+152]
	xor r15, r13
	mov QWORD PTR [r9+104], rcx
	mov rcx, QWORD PTR [r9+152]
	xor rcx, QWORD PTR [r9+80]
	xor r12, rax
	mov QWORD PTR [r9+80], rcx
	mov rcx, QWORD PTR [r9+120]
	xor rcx, QWORD PTR [r9+136]
	xor rax, QWORD PTR [r9+144]
	xor rbp, r14
	xor r13, rbx
	xor r15, rcx
	mov r14, QWORD PTR [r9+24]
	xor r14, r11
	xor rax, QWORD PTR [r9+136]
	xor r11, r15
	xor r15, QWORD PTR [r9+40]
	xor r12, r14
	xor r10, r14
	mov r14, QWORD PTR [r9+24]
	xor r14, rax
	xor r15, r12
	mov QWORD PTR [r9+24], rbp
	mov rbp, QWORD PTR [r9+8]
	xor rbp, r10
	xor rax, r10
	xor r13, r12
	xor r13, QWORD PTR [r9]
	xor rbx, r11
	xor rbx, QWORD PTR [r9]
	mov r11, r14
	xor r11, r15
	xor rcx, rbp
	xor rbp, QWORD PTR [r9+80]
	xor r15, QWORD PTR [r9+104]
	xor r14, rcx
	xor r14, QWORD PTR [r9]
	xor r11, QWORD PTR [r9+24]
	xor r11, QWORD PTR [r9]
	mov QWORD PTR [r9+24], r13
	mov r13, rax
	mov r12, r14
	mov r10, rcx
	mov rcx, r15
	mov QWORD PTR [r9+104], rbx
	mov rbx, QWORD PTR [r9+24]
	mov rax, QWORD PTR [r9+104]
	movabs r14, 6148914691236517205
	mov QWORD PTR [r9+32], r14
	movabs r14, 3689348814741910323
	mov QWORD PTR [r9+40], r14
	movabs r14, 1085102592571150095
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+32]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+32]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+32]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+32]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+40]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+40]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+40]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+40]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+48]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+48]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+48]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+48]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	ror eax, 8
	xor rax, QWORD PTR [r9+432]
	mov rbx, QWORD PTR [r9+432]
	mov rcx, rbx
	shr rcx, 7
	movabs rbp, 0
	sub rbp, rcx
	and rbp, 27
	add rbx, rbx
	xor rbx, rbp
	and rbx, 255
	mov QWORD PTR [r9+432], rbx
23:
	xor eax, DWORD PTR [rdx+rsi*1]
	mov DWORD PTR [rdx], eax
	add rdx, 4
	add rdi, 4
	je 28f
	jmp 29f
28:
	mov rdi, rsi
29:
	sub r8, 1
	jne 21b
	mov rbx, QWORD PTR [r9+384]
	mov rbp, QWORD PTR [r9+392]
	mov r12, QWORD PTR [r9+400]
	mov r13, QWORD PTR [r9+408]
	mov r14, QWORD PTR [r9+416]
	mov r15, QWORD PTR [r9+424]
	mov r11d, 0
	mov QWORD PTR [rsp+8], r11
	mov QWORD PTR [rsp+16], r11
	mov QWORD PTR [rsp+24], r11
	mov QWORD PTR [rsp+32], r11
	mov QWORD PTR [rsp+40], r11
	mov QWORD PTR [rsp+48], r11
	mov QWORD PTR [rsp+56], r11
	mov QWORD PTR [rsp+64], r11
	mov QWORD PTR [rsp+72], r11
	mov QWORD PTR [rsp+80], r11
	mov QWORD PTR [rsp+88], r11
	mov QWORD PTR [rsp+96], r11
	mov QWORD PTR [rsp+104], r11
	mov QWORD PTR [rsp+112], r11
	mov QWORD PTR [rsp+120], r11
	mov QWORD PTR [rsp+128], r11
	mov QWORD PTR [rsp+136], r11
	mov QWORD PTR [rsp+144], r11
	mov QWORD PTR [rsp+152], r11
	mov QWORD PTR [rsp+160], r11
	mov QWORD PTR [rsp+168], r11
	mov QWORD PTR [rsp+176], r11
	mov QWORD PTR [rsp+184], r11
	mov QWORD PTR [rsp+192], r11
	mov QWORD PTR [rsp+200], r11
	mov QWORD PTR [rsp+208], r11
	mov QWORD PTR [rsp+216], r11
	mov QWORD PTR [rsp+224], r11
	mov QWORD PTR [rsp+232], r11
	mov QWORD PTR [rsp+240], r11
	mov QWORD PTR [rsp+248], r11
	mov QWORD PTR [rsp+256], r11
	mov QWORD PTR [rsp+264], r11
	mov QWORD PTR [rsp+272], r11
	mov QWORD PTR [rsp+280], r11
	mov QWORD PTR [rsp+288], r11
	mov QWORD PTR [rsp+296], r11
	mov QWORD PTR [rsp+304], r11
	mov QWORD PTR [rsp+312], r11
	mov QWORD PTR [rsp+320], r11
	mov QWORD PTR [rsp+328], r11
	mov QWORD PTR [rsp+336], r11
	mov QWORD PTR [rsp+344], r11
	mov QWORD PTR [rsp+352], r11
	mov QWORD PTR [rsp+360], r11
	mov QWORD PTR [rsp+368], r11
	mov QWORD PTR [rsp+376], r11
	mov QWORD PTR [rsp+384], r11
	mov QWORD PTR [rsp+392], r11
	mov QWORD PTR [rsp+400], r11
	mov QWORD PTR [rsp+408], r11
	mov QWORD PTR [rsp+416], r11
	mov QWORD PTR [rsp+424], r11
	mov QWORD PTR [rsp+432], r11
	mov QWORD PTR [rsp+440], r11
	mov QWORD PTR [rsp+448], r11
	mov QWORD PTR [rsp+456], r11
	mov QWORD PTR [rsp+464], r11
	mov QWORD PTR [rsp+472], r11
	mov QWORD PTR [rsp+480], r11
	mov QWORD PTR [rsp+488], r11
	mov QWORD PTR [rsp+496], r11
	mov QWORD PTR [rsp+504], r11
	mov QWORD PTR [rsp+512], r11
	lea rsp, [rsp+520]
	ret
	.p2align 6
