// The functions of `src/aes_gcm_siv.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_gcm_siv_seal_vaes_vpclmul_avx512:
	mov rax, QWORD PTR [rsp+8]
	or rax, r8
	cmp rax, 128
	jae 20f
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov r10, rsi
	shl r10, 4
	add r10, rdi
	mov rdx, QWORD PTR [r15+208]
	mov ebx, 0
22:
	mov rax, QWORD PTR [rdx+4]
	movq xmm2, rax
	mov eax, DWORD PTR [rdx]
	shl rax, 32
	or rax, rbx
	movq xmm0, rax
	punpcklqdq xmm0, xmm2
	or rax, 1
	movq xmm1, rax
	punpcklqdq xmm1, xmm2
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	cmp rsi, 10
	je 23f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	cmp rsi, 12
	je 25f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	jmp 26f
25:
26:
	jmp 24f
23:
24:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	punpcklqdq xmm0, xmm1
	mov rax, rbx
	shl rax, 3
	add rax, r15
	movdqu XMMWORD PTR [rax+16], xmm0
	add rbx, 2
	mov rax, rsi
	shr rax, 1
	sub rax, 1
	cmp rbx, rax
	jne 22b
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
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
	je 27f
	cmp rsi, 32
	je 29f
	movdqa xmm13, xmm5
	pxor xmm13, xmm6
	pxor xmm13, xmm8
	pxor xmm13, xmm9
	movdqa xmm14, xmm13
	paddd xmm14, xmm14
	movabs rax, 868928702305472013
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqu xmm1, XMMWORD PTR [rdi]
	movdqu XMMWORD PTR [rdx], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm5
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+16], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm6
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+32], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm7
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+48], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm8
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+64], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm9
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+80], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm10
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+96], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm11
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+112], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm12
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+128], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm13
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+144], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm14
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+160], xmm1
	jmp 210f
29:
	movabs rax, 868928702305472013
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	pxor xmm15, xmm15
	movdqu xmm1, XMMWORD PTR [rdi]
	movdqu xmm2, XMMWORD PTR [rdi+16]
	movdqu XMMWORD PTR [rdx], xmm1
	movdqu XMMWORD PTR [rdx+16], xmm2
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm11
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+224], xmm1
210:
	jmp 28f
27:
	movabs rax, 290207319600858629
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqu xmm1, XMMWORD PTR [rdi]
	movdqu xmm2, XMMWORD PTR [rdi+8]
	psrldq xmm2, 8
	movdqu XMMWORD PTR [rdx], xmm1
	movdqu XMMWORD PTR [rdx+16], xmm2
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm12
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+192], xmm1
28:
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	movq xmm7, rax
	movq xmm11, rdx
	punpcklqdq xmm7, xmm11
	movabs rax, 0
	movq xmm1, rax
	movabs rax, -4467570830351532032
	movq xmm12, rax
	punpcklqdq xmm1, xmm12
	movabs rax, 1
	movq xmm13, rax
	movabs rax, -4467570830351532032
	movq xmm12, rax
	punpcklqdq xmm13, xmm12
	movabs rax, -1
	movq xmm14, rax
	punpcklqdq xmm14, xmm14
	movdqa xmm3, xmm7
	psllq xmm3, 1
	movdqa xmm11, xmm7
	psrlq xmm11, 63
	pslldq xmm11, 8
	por xmm3, xmm11
	pshufd xmm11, xmm7, 255
	psrld xmm11, 31
	paddd xmm11, xmm14
	pandn xmm11, xmm13
	pxor xmm3, xmm11
	pxor xmm2, xmm2
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	test rbx, rbx
	je 211f
213:
	movdqu xmm7, XMMWORD PTR [r12]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	add r12, 16
	sub rbx, 1
	jne 213b
	jmp 212f
211:
212:
	mov rsi, r12
	mov rcx, rbp
	and rcx, 15
	test rcx, rcx
	je 214f
	mov rdi, r15
	add rdi, 128
	pxor xmm7, xmm7
	movdqu XMMWORD PTR [rdi], xmm7
	mov r10d, 0
216:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 216b
	movdqu xmm7, XMMWORD PTR [rdi]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	jmp 215f
214:
215:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	test rbx, rbx
	je 217f
	cmp rbx, 4
	jb 219f
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm4, xmm10
	pxor xmm4, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm5, xmm10
	pxor xmm5, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm6, xmm10
	pxor xmm6, xmm8
221:
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqu xmm7, XMMWORD PTR [r12]
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 16
	pxor xmm9, xmm11
	movdqu xmm7, XMMWORD PTR [r12+16]
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm5, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm5, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm5, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm5, 16
	pxor xmm9, xmm11
	movdqu xmm7, XMMWORD PTR [r12+32]
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm4, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm4, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm4, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm4, 16
	pxor xmm9, xmm11
	movdqu xmm7, XMMWORD PTR [r12+48]
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	add r12, 64
	sub rbx, 4
	cmp rbx, 4
	jae 221b
	jmp 220f
219:
220:
	test rbx, rbx
	je 222f
224:
	movdqu xmm7, XMMWORD PTR [r12]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	add r12, 16
	sub rbx, 1
	jne 224b
	jmp 223f
222:
223:
	jmp 218f
217:
218:
	mov rsi, r12
	mov rcx, rbp
	and rcx, 15
	test rcx, rcx
	je 225f
	mov rdi, r15
	add rdi, 128
	pxor xmm7, xmm7
	movdqu XMMWORD PTR [rdi], xmm7
	mov r10d, 0
227:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 227b
	movdqu xmm7, XMMWORD PTR [rdi]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	jmp 226f
225:
226:
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, QWORD PTR [r15+240]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	movq xmm7, rax
	movq xmm11, rdx
	punpcklqdq xmm7, xmm11
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	movq rax, xmm2
	psrldq xmm2, 8
	movq rdx, xmm2
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov r10, rsi
	shl r10, 4
	add r10, rdi
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	cmp rsi, 10
	je 228f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 230f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 231f
230:
231:
	jmp 229f
228:
229:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	movdqu XMMWORD PTR [r15], xmm0
	movdqu xmm0, XMMWORD PTR [r15]
	movabs rax, -9223372036854775808
	movq xmm9, rax
	pslldq xmm9, 8
	por xmm9, xmm0
	mov eax, 1
	movq xmm10, rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov r10, rsi
	shl r10, 4
	add r10, rdi
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 232f
	cmp rbx, 4
	jb 234f
236:
	movdqa xmm0, xmm9
	paddd xmm9, xmm10
	movdqa xmm1, xmm9
	paddd xmm9, xmm10
	movdqa xmm2, xmm9
	paddd xmm9, xmm10
	movdqa xmm3, xmm9
	paddd xmm9, xmm10
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	pxor xmm2, xmm8
	pxor xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	cmp rsi, 10
	je 237f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	cmp rsi, 12
	je 239f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	jmp 240f
239:
240:
	jmp 238f
237:
238:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	aesenclast xmm2, xmm8
	aesenclast xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [r12]
	pxor xmm0, xmm8
	movdqu XMMWORD PTR [r12], xmm0
	movdqu xmm8, XMMWORD PTR [r12+16]
	pxor xmm1, xmm8
	movdqu XMMWORD PTR [r12+16], xmm1
	movdqu xmm8, XMMWORD PTR [r12+32]
	pxor xmm2, xmm8
	movdqu XMMWORD PTR [r12+32], xmm2
	movdqu xmm8, XMMWORD PTR [r12+48]
	pxor xmm3, xmm8
	movdqu XMMWORD PTR [r12+48], xmm3
	add r12, 64
	sub rbx, 4
	cmp rbx, 4
	jae 236b
	jmp 235f
234:
235:
	test rbx, rbx
	je 241f
243:
	movdqa xmm0, xmm9
	paddd xmm9, xmm10
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	cmp rsi, 10
	je 244f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 246f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 247f
246:
247:
	jmp 245f
244:
245:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r12]
	pxor xmm0, xmm8
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	sub rbx, 1
	jne 243b
	jmp 242f
241:
242:
	jmp 233f
232:
233:
	test rbp, rbp
	je 248f
	movdqa xmm0, xmm9
	paddd xmm9, xmm10
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	cmp rsi, 10
	je 250f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 252f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 253f
252:
253:
	jmp 251f
250:
251:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	mov rsi, r15
	add rsi, 128
	movdqu XMMWORD PTR [rsi], xmm0
	mov rdi, r12
	mov rcx, rbp
	mov r10d, 0
254:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 254b
	jmp 249f
248:
249:
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [rcx], rax
	mov rax, QWORD PTR [r15+8]
	mov QWORD PTR [rcx+8], rax
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
21:
	ret
20:
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov ebx, 0
	mov rdi, r15
	add rdi, 488
	mov rbp, QWORD PTR [r15+200]
	shr rbp, 1
	sub rbp, 1
255:
	mov rax, QWORD PTR [r15+208]
	mov ecx, DWORD PTR [rax]
	shl rcx, 32
	or rcx, rbx
	mov rdx, QWORD PTR [rax+4]
	movq xmm0, rcx
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rdi, 16
	add rbx, 1
	cmp rbx, rbp
	jne 255b
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, rbp
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_vaes}
	mov rsi, r15
	add rsi, 488
	mov rdi, r15
	add rdi, 16
	mov rcx, rbp
256:
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+16]
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 32
	add rdi, 16
	sub rcx, 2
	jne 256b
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	bswap rdx
	bswap rax
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+64], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+80], xmm0
	mov rax, QWORD PTR [r15+240]
	cmp rax, 256
	jb 257f
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 259f
261:
	mov r14d, 64
	cmp rbx, r14
	jb 262f
	jmp 263f
262:
	mov r14, rbx
263:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 264f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
266:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 266b
	vzeroupper
	test rcx, rcx
	je 267f
269:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 269b
	jmp 268f
267:
268:
	jmp 265f
264:
270:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 270b
265:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_vpclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 261b
	jmp 260f
259:
260:
	test rbp, rbp
	je 271f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
273:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 273b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_vpclmul}
	jmp 272f
271:
272:
	mov rcx, r15
	add rcx, 80
	mov r8, r15
	add r8, 64
	mov r11, r15
	add r11, 1512
	mov rdx, QWORD PTR [r15+232]
	mov r9, QWORD PTR [r15+240]
	shr r9, 8
	add r9, r9
	add r9, r9
	add r9, r9
	add r9, r9
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	movdqu xmm7, XMMWORD PTR [r8]
	pshufb xmm7, xmm0
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm13, XMMWORD PTR [rax+32]
	movabs rax, -1
	movq xmm14, rax
	punpcklqdq xmm14, xmm14
	movdqa xmm3, xmm7
	psllq xmm3, 1
	movdqa xmm11, xmm7
	psrlq xmm11, 63
	pslldq xmm11, 8
	por xmm3, xmm11
	pshufd xmm11, xmm7, 255
	psrld xmm11, 31
	paddd xmm11, xmm14
	pandn xmm11, xmm13
	pxor xmm3, xmm11
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm4, xmm10
	pxor xmm4, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm5, xmm10
	pxor xmm5, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm6, xmm10
	pxor xmm6, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm12, xmm10
	pxor xmm12, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm4, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm4, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm4, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm4, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm13, xmm10
	pxor xmm13, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm5, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm5, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm5, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm5, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm14, xmm10
	pxor xmm14, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm6, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm6, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm6, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm6, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm15, xmm10
	pxor xmm15, xmm8
	vinserti128 ymm15, ymm15, xmm14, 1
	vinserti128 ymm14, ymm13, xmm12, 1
	vinserti128 ymm13, ymm6, xmm5, 1
	vinserti128 ymm12, ymm4, xmm3, 1
	vinserti128 ymm0, ymm0, xmm0, 1
	vinserti128 ymm1, ymm1, xmm1, 1
	vmovdqa xmm2, xmm2
	vinserti128 ymm7, ymm15, xmm15, 1
	vpxor ymm8, ymm8, ymm8
	vpxor ymm9, ymm9, ymm9
	vpxor ymm10, ymm10, ymm10
	vpclmulqdq ymm11, ymm15, ymm7, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm15, ymm7, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm15, ymm7, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm15, ymm7, 16
	vpxor ymm9, ymm9, ymm11
	vpsrldq ymm11, ymm9, 8
	vpxor ymm10, ymm10, ymm11
	vpslldq ymm9, ymm9, 8
	vpxor ymm8, ymm8, ymm9
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpxor ymm3, ymm10, ymm8
	vpxor ymm8, ymm8, ymm8
	vpxor ymm9, ymm9, ymm9
	vpxor ymm10, ymm10, ymm10
	vpclmulqdq ymm11, ymm14, ymm7, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm14, ymm7, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm14, ymm7, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm14, ymm7, 16
	vpxor ymm9, ymm9, ymm11
	vpsrldq ymm11, ymm9, 8
	vpxor ymm10, ymm10, ymm11
	vpslldq ymm9, ymm9, 8
	vpxor ymm8, ymm8, ymm9
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpxor ymm4, ymm10, ymm8
	vpxor ymm8, ymm8, ymm8
	vpxor ymm9, ymm9, ymm9
	vpxor ymm10, ymm10, ymm10
	vpclmulqdq ymm11, ymm13, ymm7, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm13, ymm7, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm13, ymm7, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm13, ymm7, 16
	vpxor ymm9, ymm9, ymm11
	vpsrldq ymm11, ymm9, 8
	vpxor ymm10, ymm10, ymm11
	vpslldq ymm9, ymm9, 8
	vpxor ymm8, ymm8, ymm9
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpxor ymm5, ymm10, ymm8
	vpxor ymm8, ymm8, ymm8
	vpxor ymm9, ymm9, ymm9
	vpxor ymm10, ymm10, ymm10
	vpclmulqdq ymm11, ymm12, ymm7, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm12, ymm7, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm12, ymm7, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm12, ymm7, 16
	vpxor ymm9, ymm9, ymm11
	vpsrldq ymm11, ymm9, 8
	vpxor ymm10, ymm10, ymm11
	vpslldq ymm9, ymm9, 8
	vpxor ymm8, ymm8, ymm9
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpxor ymm6, ymm10, ymm8
	vmovdqu YMMWORD PTR [r11], ymm3
	vmovdqu YMMWORD PTR [r11+32], ymm4
	vmovdqu YMMWORD PTR [r11+64], ymm5
	vmovdqu YMMWORD PTR [r11+96], ymm6
	vmovdqu YMMWORD PTR [r11+128], ymm15
	vmovdqu YMMWORD PTR [r11+160], ymm14
	vmovdqu YMMWORD PTR [r11+192], ymm13
	vmovdqu YMMWORD PTR [r11+224], ymm12
	vmovdqu xmm2, XMMWORD PTR [rcx]
	vpshufb xmm2, xmm2, xmm0
274:
	vpxor ymm8, ymm8, ymm8
	vpxor ymm9, ymm9, ymm9
	vpxor ymm10, ymm10, ymm10
	vmovdqu ymm12, YMMWORD PTR [r11+32]
	vmovdqu ymm7, YMMWORD PTR [rdx+32]
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vmovdqu ymm12, YMMWORD PTR [r11+64]
	vmovdqu ymm7, YMMWORD PTR [rdx+64]
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vmovdqu ymm12, YMMWORD PTR [r11+96]
	vmovdqu ymm7, YMMWORD PTR [rdx+96]
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vmovdqu ymm12, YMMWORD PTR [r11+128]
	vmovdqu ymm7, YMMWORD PTR [rdx+128]
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vmovdqu ymm12, YMMWORD PTR [r11+160]
	vmovdqu ymm7, YMMWORD PTR [rdx+160]
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vmovdqu ymm12, YMMWORD PTR [r11+192]
	vmovdqu ymm7, YMMWORD PTR [rdx+192]
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vmovdqu ymm12, YMMWORD PTR [r11+224]
	vmovdqu ymm7, YMMWORD PTR [rdx+224]
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vmovdqu ymm12, YMMWORD PTR [r11]
	vmovdqu ymm7, YMMWORD PTR [rdx]
	vpxor ymm7, ymm7, ymm2
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vpsrldq ymm11, ymm9, 8
	vpxor ymm10, ymm10, ymm11
	vpslldq ymm9, ymm9, 8
	vpxor ymm8, ymm8, ymm9
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpxor ymm7, ymm10, ymm8
	vextracti128 xmm11, ymm7, 1
	vpxor xmm2, xmm7, xmm11
	add rdx, 256
	sub r9, 16
	jne 274b
	vpshufb xmm2, xmm2, xmm0
	vmovdqu XMMWORD PTR [rcx], xmm2
	vzeroupper
	mov r12, QWORD PTR [r15+232]
	mov rax, QWORD PTR [r15+240]
	shr rax, 8
	shl rax, 8
	add r12, rax
	mov rbp, QWORD PTR [r15+240]
	and rbp, 255
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 275f
277:
	mov r14d, 64
	cmp rbx, r14
	jb 278f
	jmp 279f
278:
	mov r14, rbx
279:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 280f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
282:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 282b
	vzeroupper
	test rcx, rcx
	je 283f
285:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 285b
	jmp 284f
283:
284:
	jmp 281f
280:
286:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 286b
281:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_vpclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 277b
	jmp 276f
275:
276:
	test rbp, rbp
	je 287f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
289:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 289b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_vpclmul}
	jmp 288f
287:
288:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash_vpclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	jmp 258f
257:
	mov rax, QWORD PTR [r15+224]
	shr rax, 4
	mov rdx, QWORD PTR [r15+240]
	shr rdx, 4
	add rax, rdx
	cmp rax, 62
	jae 290f
	mov rdi, r15
	add rdi, 488
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 292f
	mov r14, rbx
	mov rcx, r14
	cmp rcx, 8
	jb 294f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
296:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 296b
	vzeroupper
	test rcx, rcx
	je 297f
299:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 299b
	jmp 298f
297:
298:
	jmp 295f
294:
2100:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2100b
295:
	jmp 293f
292:
293:
	test rbp, rbp
	je 2101f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
2103:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2103b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 2102f
2101:
2102:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 2104f
	mov r14, rbx
	mov rcx, r14
	cmp rcx, 8
	jb 2106f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
2108:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 2108b
	vzeroupper
	test rcx, rcx
	je 2109f
2111:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2111b
	jmp 2110f
2109:
2110:
	jmp 2107f
2106:
2112:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2112b
2107:
	jmp 2105f
2104:
2105:
	test rbp, rbp
	je 2113f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
2115:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2115b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 2114f
2113:
2114:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	mov rcx, rdi
	sub rcx, r15
	shr rcx, 4
	sub rcx, 29
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	call {vg_ghash_vpclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	jmp 291f
290:
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 2116f
2118:
	mov r14d, 64
	cmp rbx, r14
	jb 2119f
	jmp 2120f
2119:
	mov r14, rbx
2120:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 2121f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
2123:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 2123b
	vzeroupper
	test rcx, rcx
	je 2124f
2126:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2126b
	jmp 2125f
2124:
2125:
	jmp 2122f
2121:
2127:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2127b
2122:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_vpclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 2118b
	jmp 2117f
2116:
2117:
	test rbp, rbp
	je 2128f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
2130:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2130b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_vpclmul}
	jmp 2129f
2128:
2129:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 2131f
2133:
	mov r14d, 64
	cmp rbx, r14
	jb 2134f
	jmp 2135f
2134:
	mov r14, rbx
2135:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 2136f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
2138:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 2138b
	vzeroupper
	test rcx, rcx
	je 2139f
2141:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2141b
	jmp 2140f
2139:
2140:
	jmp 2137f
2136:
2142:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2142b
2137:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_vpclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 2133b
	jmp 2132f
2131:
2132:
	test rbp, rbp
	je 2143f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
2145:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2145b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_vpclmul}
	jmp 2144f
2143:
2144:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash_vpclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
291:
258:
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
	mov rcx, r15
	add rcx, 1768
	call {vg_aes_expand_key_scratch_aesni}
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 0
	call {vg_aes_ctr32_vaes}
	mov rax, QWORD PTR [r15+240]
	cmp rax, 256
	jb 2146f
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rax, rcx
	mov QWORD PTR [r15+104], rax
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 96
	mov rcx, r15
	add rcx, 80
	mov r8, r15
	add r8, 64
	mov r11, r15
	add r11, 1768
	mov r12, QWORD PTR [r15+232]
	mov r9, QWORD PTR [r15+240]
	shr r9, 8
	add r9, r9
	add r9, r9
	add r9, r9
	add r9, r9
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	vinserti128 ymm0, ymm0, xmm0, 1
	movabs r10, 1
	vmovq xmm15, r10
	vmovdqu xmm14, XMMWORD PTR [rdx]
	vpaddd xmm13, xmm14, xmm15
	vinserti128 ymm14, ymm14, xmm13, 1
	movabs r10, 2
	vmovq xmm15, r10
	vinserti128 ymm15, ymm15, xmm15, 1
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	mov rax, rdx
	mov rdx, r12
2148:
	vmovdqa ymm3, ymm14
	vpaddd ymm14, ymm14, ymm15
	vmovdqa ymm4, ymm14
	vpaddd ymm14, ymm14, ymm15
	vmovdqa ymm5, ymm14
	vpaddd ymm14, ymm14, ymm15
	vmovdqa ymm6, ymm14
	vpaddd ymm14, ymm14, ymm15
	vbroadcasti128 ymm13, XMMWORD PTR [rdi]
	vpxor ymm3, ymm3, ymm13
	vpxor ymm4, ymm4, ymm13
	vpxor ymm5, ymm5, ymm13
	vpxor ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+16]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+32]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+48]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+64]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+80]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+96]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+112]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+128]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+144]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	cmp rsi, 10
	je 2149f
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+160]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+176]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	cmp rsi, 12
	je 2151f
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+192]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+208]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	jmp 2152f
2151:
2152:
	jmp 2150f
2149:
2150:
	vbroadcasti128 ymm13, XMMWORD PTR [r10]
	vaesenclast ymm3, ymm3, ymm13
	vaesenclast ymm4, ymm4, ymm13
	vaesenclast ymm5, ymm5, ymm13
	vaesenclast ymm6, ymm6, ymm13
	vmovdqu ymm13, YMMWORD PTR [rdx]
	vpxor ymm3, ymm3, ymm13
	vmovdqu YMMWORD PTR [rdx], ymm3
	vmovdqu ymm13, YMMWORD PTR [rdx+32]
	vpxor ymm4, ymm4, ymm13
	vmovdqu YMMWORD PTR [rdx+32], ymm4
	vmovdqu ymm13, YMMWORD PTR [rdx+64]
	vpxor ymm5, ymm5, ymm13
	vmovdqu YMMWORD PTR [rdx+64], ymm5
	vmovdqu ymm13, YMMWORD PTR [rdx+96]
	vpxor ymm6, ymm6, ymm13
	vmovdqu YMMWORD PTR [rdx+96], ymm6
	vmovdqa ymm3, ymm14
	vpaddd ymm14, ymm14, ymm15
	vmovdqa ymm4, ymm14
	vpaddd ymm14, ymm14, ymm15
	vmovdqa ymm5, ymm14
	vpaddd ymm14, ymm14, ymm15
	vmovdqa ymm6, ymm14
	vpaddd ymm14, ymm14, ymm15
	vbroadcasti128 ymm13, XMMWORD PTR [rdi]
	vpxor ymm3, ymm3, ymm13
	vpxor ymm4, ymm4, ymm13
	vpxor ymm5, ymm5, ymm13
	vpxor ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+16]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+32]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+48]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+64]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+80]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+96]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+112]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+128]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+144]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	cmp rsi, 10
	je 2153f
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+160]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+176]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	cmp rsi, 12
	je 2155f
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+192]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+208]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	jmp 2156f
2155:
2156:
	jmp 2154f
2153:
2154:
	vbroadcasti128 ymm13, XMMWORD PTR [r10]
	vaesenclast ymm3, ymm3, ymm13
	vaesenclast ymm4, ymm4, ymm13
	vaesenclast ymm5, ymm5, ymm13
	vaesenclast ymm6, ymm6, ymm13
	vmovdqu ymm13, YMMWORD PTR [rdx+128]
	vpxor ymm3, ymm3, ymm13
	vmovdqu YMMWORD PTR [rdx+128], ymm3
	vmovdqu ymm13, YMMWORD PTR [rdx+160]
	vpxor ymm4, ymm4, ymm13
	vmovdqu YMMWORD PTR [rdx+160], ymm4
	vmovdqu ymm13, YMMWORD PTR [rdx+192]
	vpxor ymm5, ymm5, ymm13
	vmovdqu YMMWORD PTR [rdx+192], ymm5
	vmovdqu ymm13, YMMWORD PTR [rdx+224]
	vpxor ymm6, ymm6, ymm13
	vmovdqu YMMWORD PTR [rdx+224], ymm6
	add rdx, 256
	sub r9, 16
	jne 2148b
	vmovdqu XMMWORD PTR [rax], xmm14
	vzeroupper
	mov r12, QWORD PTR [r15+232]
	mov rax, QWORD PTR [r15+240]
	shr rax, 8
	shl rax, 8
	add r12, rax
	mov rbp, QWORD PTR [r15+240]
	and rbp, 255
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 2157f
2159:
	mov r14d, 64
	cmp rbx, r14
	jb 2160f
	jmp 2161f
2160:
	mov r14, rbx
2161:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
2162:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 2162b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_vaes}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
	cmp rcx, 8
	jb 2163f
2165:
	vmovdqu ymm1, YMMWORD PTR [rsi]
	vmovdqu ymm0, YMMWORD PTR [r12]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12], ymm1
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vmovdqu ymm0, YMMWORD PTR [r12+32]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12+32], ymm1
	add r12, 64
	add rsi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 2165b
	vzeroupper
	test rcx, rcx
	je 2166f
2168:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 2168b
	jmp 2167f
2166:
2167:
	jmp 2164f
2163:
2169:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 2169b
2164:
	sub rbx, r14
	jne 2159b
	jmp 2158f
2157:
2158:
	test rbp, rbp
	je 2170f
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_vaes}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
2172:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2172b
	jmp 2171f
2170:
2171:
	jmp 2147f
2146:
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rdx, rcx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 2173f
2175:
	mov r14d, 64
	cmp rbx, r14
	jb 2176f
	jmp 2177f
2176:
	mov r14, rbx
2177:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
2178:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 2178b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_vaes}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
	cmp rcx, 8
	jb 2179f
2181:
	vmovdqu ymm1, YMMWORD PTR [rsi]
	vmovdqu ymm0, YMMWORD PTR [r12]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12], ymm1
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vmovdqu ymm0, YMMWORD PTR [r12+32]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12+32], ymm1
	add r12, 64
	add rsi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 2181b
	vzeroupper
	test rcx, rcx
	je 2182f
2184:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 2184b
	jmp 2183f
2182:
2183:
	jmp 2180f
2179:
2185:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 2185b
2180:
	sub rbx, r14
	jne 2175b
	jmp 2174f
2173:
2174:
	test rbp, rbp
	je 2186f
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_vaes}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
2188:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2188b
	jmp 2187f
2186:
2187:
2147:
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [rcx], rax
	mov rax, QWORD PTR [r15+8]
	mov QWORD PTR [rcx+8], rax
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
	jmp 21b
	.p2align 6

vg_aes_gcm_siv_open_vaes_vpclmul_avx512:
	mov rax, QWORD PTR [rsp+8]
	or rax, r8
	cmp rax, 128
	jae 20f
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+8], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov r10, rsi
	shl r10, 4
	add r10, rdi
	mov rdx, QWORD PTR [r15+208]
	mov ebx, 0
22:
	mov rax, QWORD PTR [rdx+4]
	movq xmm2, rax
	mov eax, DWORD PTR [rdx]
	shl rax, 32
	or rax, rbx
	movq xmm0, rax
	punpcklqdq xmm0, xmm2
	or rax, 1
	movq xmm1, rax
	punpcklqdq xmm1, xmm2
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	cmp rsi, 10
	je 23f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	cmp rsi, 12
	je 25f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	jmp 26f
25:
26:
	jmp 24f
23:
24:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	punpcklqdq xmm0, xmm1
	mov rax, rbx
	shl rax, 3
	add rax, r15
	movdqu XMMWORD PTR [rax+16], xmm0
	add rbx, 2
	mov rax, rsi
	shr rax, 1
	sub rax, 1
	cmp rbx, rax
	jne 22b
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
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
	je 27f
	cmp rsi, 32
	je 29f
	movdqa xmm13, xmm5
	pxor xmm13, xmm6
	pxor xmm13, xmm8
	pxor xmm13, xmm9
	movdqa xmm14, xmm13
	paddd xmm14, xmm14
	movabs rax, 868928702305472013
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqu xmm1, XMMWORD PTR [rdi]
	movdqu XMMWORD PTR [rdx], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm5
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+16], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm6
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+32], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm7
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+48], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm8
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+64], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm9
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+80], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm10
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+96], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm11
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+112], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm12
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+128], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm13
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+144], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm14
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+160], xmm1
	jmp 210f
29:
	movabs rax, 868928702305472013
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	pxor xmm15, xmm15
	movdqu xmm1, XMMWORD PTR [rdi]
	movdqu xmm2, XMMWORD PTR [rdi+16]
	movdqu XMMWORD PTR [rdx], xmm1
	movdqu XMMWORD PTR [rdx+16], xmm2
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm11
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+224], xmm1
210:
	jmp 28f
27:
	movabs rax, 290207319600858629
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqu xmm1, XMMWORD PTR [rdi]
	movdqu xmm2, XMMWORD PTR [rdi+8]
	psrldq xmm2, 8
	movdqu XMMWORD PTR [rdx], xmm1
	movdqu XMMWORD PTR [rdx+16], xmm2
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm12
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+192], xmm1
28:
	movdqu xmm0, XMMWORD PTR [r15]
	movabs rax, -9223372036854775808
	movq xmm9, rax
	pslldq xmm9, 8
	por xmm9, xmm0
	mov eax, 1
	movq xmm10, rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov r10, rsi
	shl r10, 4
	add r10, rdi
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 211f
	cmp rbx, 4
	jb 213f
215:
	movdqa xmm0, xmm9
	paddd xmm9, xmm10
	movdqa xmm1, xmm9
	paddd xmm9, xmm10
	movdqa xmm2, xmm9
	paddd xmm9, xmm10
	movdqa xmm3, xmm9
	paddd xmm9, xmm10
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	pxor xmm2, xmm8
	pxor xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	cmp rsi, 10
	je 216f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	cmp rsi, 12
	je 218f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	jmp 219f
218:
219:
	jmp 217f
216:
217:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	aesenclast xmm2, xmm8
	aesenclast xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [r12]
	pxor xmm0, xmm8
	movdqu XMMWORD PTR [r12], xmm0
	movdqu xmm8, XMMWORD PTR [r12+16]
	pxor xmm1, xmm8
	movdqu XMMWORD PTR [r12+16], xmm1
	movdqu xmm8, XMMWORD PTR [r12+32]
	pxor xmm2, xmm8
	movdqu XMMWORD PTR [r12+32], xmm2
	movdqu xmm8, XMMWORD PTR [r12+48]
	pxor xmm3, xmm8
	movdqu XMMWORD PTR [r12+48], xmm3
	add r12, 64
	sub rbx, 4
	cmp rbx, 4
	jae 215b
	jmp 214f
213:
214:
	test rbx, rbx
	je 220f
222:
	movdqa xmm0, xmm9
	paddd xmm9, xmm10
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	cmp rsi, 10
	je 223f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 225f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 226f
225:
226:
	jmp 224f
223:
224:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r12]
	pxor xmm0, xmm8
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	sub rbx, 1
	jne 222b
	jmp 221f
220:
221:
	jmp 212f
211:
212:
	test rbp, rbp
	je 227f
	movdqa xmm0, xmm9
	paddd xmm9, xmm10
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	cmp rsi, 10
	je 229f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 231f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 232f
231:
232:
	jmp 230f
229:
230:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	mov rsi, r15
	add rsi, 128
	movdqu XMMWORD PTR [rsi], xmm0
	mov rdi, r12
	mov rcx, rbp
	mov r10d, 0
233:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 233b
	jmp 228f
227:
228:
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	movq xmm7, rax
	movq xmm11, rdx
	punpcklqdq xmm7, xmm11
	movabs rax, 0
	movq xmm1, rax
	movabs rax, -4467570830351532032
	movq xmm12, rax
	punpcklqdq xmm1, xmm12
	movabs rax, 1
	movq xmm13, rax
	movabs rax, -4467570830351532032
	movq xmm12, rax
	punpcklqdq xmm13, xmm12
	movabs rax, -1
	movq xmm14, rax
	punpcklqdq xmm14, xmm14
	movdqa xmm3, xmm7
	psllq xmm3, 1
	movdqa xmm11, xmm7
	psrlq xmm11, 63
	pslldq xmm11, 8
	por xmm3, xmm11
	pshufd xmm11, xmm7, 255
	psrld xmm11, 31
	paddd xmm11, xmm14
	pandn xmm11, xmm13
	pxor xmm3, xmm11
	pxor xmm2, xmm2
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	test rbx, rbx
	je 234f
236:
	movdqu xmm7, XMMWORD PTR [r12]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	add r12, 16
	sub rbx, 1
	jne 236b
	jmp 235f
234:
235:
	mov rsi, r12
	mov rcx, rbp
	and rcx, 15
	test rcx, rcx
	je 237f
	mov rdi, r15
	add rdi, 128
	pxor xmm7, xmm7
	movdqu XMMWORD PTR [rdi], xmm7
	mov r10d, 0
239:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 239b
	movdqu xmm7, XMMWORD PTR [rdi]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	jmp 238f
237:
238:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	test rbx, rbx
	je 240f
	cmp rbx, 4
	jb 242f
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm4, xmm10
	pxor xmm4, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm5, xmm10
	pxor xmm5, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm6, xmm10
	pxor xmm6, xmm8
244:
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqu xmm7, XMMWORD PTR [r12]
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 16
	pxor xmm9, xmm11
	movdqu xmm7, XMMWORD PTR [r12+16]
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm5, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm5, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm5, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm5, 16
	pxor xmm9, xmm11
	movdqu xmm7, XMMWORD PTR [r12+32]
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm4, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm4, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm4, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm4, 16
	pxor xmm9, xmm11
	movdqu xmm7, XMMWORD PTR [r12+48]
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	add r12, 64
	sub rbx, 4
	cmp rbx, 4
	jae 244b
	jmp 243f
242:
243:
	test rbx, rbx
	je 245f
247:
	movdqu xmm7, XMMWORD PTR [r12]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	add r12, 16
	sub rbx, 1
	jne 247b
	jmp 246f
245:
246:
	jmp 241f
240:
241:
	mov rsi, r12
	mov rcx, rbp
	and rcx, 15
	test rcx, rcx
	je 248f
	mov rdi, r15
	add rdi, 128
	pxor xmm7, xmm7
	movdqu XMMWORD PTR [rdi], xmm7
	mov r10d, 0
250:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 250b
	movdqu xmm7, XMMWORD PTR [rdi]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	jmp 249f
248:
249:
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, QWORD PTR [r15+240]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	movq xmm7, rax
	movq xmm11, rdx
	punpcklqdq xmm7, xmm11
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	movq rax, xmm2
	psrldq xmm2, 8
	movq rdx, xmm2
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov r10, rsi
	shl r10, 4
	add r10, rdi
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	cmp rsi, 10
	je 251f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 253f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 254f
253:
254:
	jmp 252f
251:
252:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rax, QWORD PTR [r15]
	xor rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+8]
	xor rdx, QWORD PTR [r15+136]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+192], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov r11d, 0
	sub r11, QWORD PTR [r15+192]
	mov r10d, 0
	mov rcx, rbp
	shr rcx, 4
	test rcx, rcx
	je 255f
	movq xmm0, r11
	punpcklqdq xmm0, xmm0
257:
	movdqu xmm1, XMMWORD PTR [r12+r10*1]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [r12+r10*1], xmm1
	add r10, 16
	sub rcx, 1
	jne 257b
	jmp 256f
255:
256:
	cmp r10, rbp
	je 258f
260:
	movzx eax, BYTE PTR [r12+r10*1]
	and rax, r11
	mov BYTE PTR [r12+r10*1], al
	add r10, 1
	cmp r10, rbp
	jne 260b
	jmp 259f
258:
259:
	mov rax, QWORD PTR [r15+192]
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
21:
	ret
20:
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+8], rax
	mov ebx, 0
	mov rdi, r15
	add rdi, 488
	mov rbp, QWORD PTR [r15+200]
	shr rbp, 1
	sub rbp, 1
261:
	mov rax, QWORD PTR [r15+208]
	mov ecx, DWORD PTR [rax]
	shl rcx, 32
	or rcx, rbx
	mov rdx, QWORD PTR [rax+4]
	movq xmm0, rcx
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rdi, 16
	add rbx, 1
	cmp rbx, rbp
	jne 261b
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, rbp
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_vaes}
	mov rsi, r15
	add rsi, 488
	mov rdi, r15
	add rdi, 16
	mov rcx, rbp
262:
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+16]
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 32
	add rdi, 16
	sub rcx, 2
	jne 262b
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
	mov rcx, r15
	add rcx, 1768
	call {vg_aes_expand_key_scratch_aesni}
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	bswap rdx
	bswap rax
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+64], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+80], xmm0
	mov rax, QWORD PTR [r15+240]
	cmp rax, 256
	jb 263f
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rax, rcx
	mov QWORD PTR [r15+104], rax
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 265f
267:
	mov r14d, 64
	cmp rbx, r14
	jb 268f
	jmp 269f
268:
	mov r14, rbx
269:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 270f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
272:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 272b
	vzeroupper
	test rcx, rcx
	je 273f
275:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 275b
	jmp 274f
273:
274:
	jmp 271f
270:
276:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 276b
271:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_vpclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 267b
	jmp 266f
265:
266:
	test rbp, rbp
	je 277f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
279:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 279b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_vpclmul}
	jmp 278f
277:
278:
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 96
	mov rcx, r15
	add rcx, 80
	mov r8, r15
	add r8, 64
	mov r11, r15
	add r11, 1768
	mov r12, QWORD PTR [r15+232]
	mov r9, QWORD PTR [r15+240]
	shr r9, 8
	add r9, r9
	add r9, r9
	add r9, r9
	add r9, r9
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	movdqu xmm7, XMMWORD PTR [r8]
	pshufb xmm7, xmm0
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm13, XMMWORD PTR [rax+32]
	movabs rax, -1
	movq xmm14, rax
	punpcklqdq xmm14, xmm14
	movdqa xmm3, xmm7
	psllq xmm3, 1
	movdqa xmm11, xmm7
	psrlq xmm11, 63
	pslldq xmm11, 8
	por xmm3, xmm11
	pshufd xmm11, xmm7, 255
	psrld xmm11, 31
	paddd xmm11, xmm14
	pandn xmm11, xmm13
	pxor xmm3, xmm11
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm4, xmm10
	pxor xmm4, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm5, xmm10
	pxor xmm5, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm6, xmm10
	pxor xmm6, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm12, xmm10
	pxor xmm12, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm4, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm4, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm4, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm4, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm13, xmm10
	pxor xmm13, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm5, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm5, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm5, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm5, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm14, xmm10
	pxor xmm14, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm6, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm6, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm6, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm6, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm15, xmm10
	pxor xmm15, xmm8
	vinserti128 ymm15, ymm15, xmm14, 1
	vinserti128 ymm14, ymm13, xmm12, 1
	vinserti128 ymm13, ymm6, xmm5, 1
	vinserti128 ymm12, ymm4, xmm3, 1
	vinserti128 ymm0, ymm0, xmm0, 1
	vinserti128 ymm1, ymm1, xmm1, 1
	vmovdqa xmm2, xmm2
	vinserti128 ymm7, ymm15, xmm15, 1
	vpxor ymm8, ymm8, ymm8
	vpxor ymm9, ymm9, ymm9
	vpxor ymm10, ymm10, ymm10
	vpclmulqdq ymm11, ymm15, ymm7, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm15, ymm7, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm15, ymm7, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm15, ymm7, 16
	vpxor ymm9, ymm9, ymm11
	vpsrldq ymm11, ymm9, 8
	vpxor ymm10, ymm10, ymm11
	vpslldq ymm9, ymm9, 8
	vpxor ymm8, ymm8, ymm9
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpxor ymm3, ymm10, ymm8
	vpxor ymm8, ymm8, ymm8
	vpxor ymm9, ymm9, ymm9
	vpxor ymm10, ymm10, ymm10
	vpclmulqdq ymm11, ymm14, ymm7, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm14, ymm7, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm14, ymm7, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm14, ymm7, 16
	vpxor ymm9, ymm9, ymm11
	vpsrldq ymm11, ymm9, 8
	vpxor ymm10, ymm10, ymm11
	vpslldq ymm9, ymm9, 8
	vpxor ymm8, ymm8, ymm9
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpxor ymm4, ymm10, ymm8
	vpxor ymm8, ymm8, ymm8
	vpxor ymm9, ymm9, ymm9
	vpxor ymm10, ymm10, ymm10
	vpclmulqdq ymm11, ymm13, ymm7, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm13, ymm7, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm13, ymm7, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm13, ymm7, 16
	vpxor ymm9, ymm9, ymm11
	vpsrldq ymm11, ymm9, 8
	vpxor ymm10, ymm10, ymm11
	vpslldq ymm9, ymm9, 8
	vpxor ymm8, ymm8, ymm9
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpxor ymm5, ymm10, ymm8
	vpxor ymm8, ymm8, ymm8
	vpxor ymm9, ymm9, ymm9
	vpxor ymm10, ymm10, ymm10
	vpclmulqdq ymm11, ymm12, ymm7, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm12, ymm7, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm12, ymm7, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm12, ymm7, 16
	vpxor ymm9, ymm9, ymm11
	vpsrldq ymm11, ymm9, 8
	vpxor ymm10, ymm10, ymm11
	vpslldq ymm9, ymm9, 8
	vpxor ymm8, ymm8, ymm9
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpxor ymm6, ymm10, ymm8
	vmovdqu YMMWORD PTR [r11], ymm3
	vmovdqu YMMWORD PTR [r11+32], ymm4
	vmovdqu YMMWORD PTR [r11+64], ymm5
	vmovdqu YMMWORD PTR [r11+96], ymm6
	vmovdqu YMMWORD PTR [r11+128], ymm15
	vmovdqu YMMWORD PTR [r11+160], ymm14
	vmovdqu YMMWORD PTR [r11+192], ymm13
	vmovdqu YMMWORD PTR [r11+224], ymm12
	vmovdqu xmm2, XMMWORD PTR [rcx]
	vpshufb xmm2, xmm2, xmm0
	movabs r10, 1
	vmovq xmm15, r10
	vmovdqu xmm14, XMMWORD PTR [rdx]
	vpaddd xmm13, xmm14, xmm15
	vinserti128 ymm14, ymm14, xmm13, 1
	movabs r10, 2
	vmovq xmm15, r10
	vinserti128 ymm15, ymm15, xmm15, 1
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	mov rax, rdx
	mov rdx, r12
	vmovdqa ymm3, ymm14
	vpaddd ymm14, ymm14, ymm15
	vmovdqa ymm4, ymm14
	vpaddd ymm14, ymm14, ymm15
	vmovdqa ymm5, ymm14
	vpaddd ymm14, ymm14, ymm15
	vmovdqa ymm6, ymm14
	vpaddd ymm14, ymm14, ymm15
	vbroadcasti128 ymm13, XMMWORD PTR [rdi]
	vpxor ymm3, ymm3, ymm13
	vpxor ymm4, ymm4, ymm13
	vpxor ymm5, ymm5, ymm13
	vpxor ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+16]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+32]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+48]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+64]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+80]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+96]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+112]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+128]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+144]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	cmp rsi, 10
	je 280f
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+160]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+176]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	cmp rsi, 12
	je 282f
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+192]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+208]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	jmp 283f
282:
283:
	jmp 281f
280:
281:
	vbroadcasti128 ymm13, XMMWORD PTR [r10]
	vaesenclast ymm3, ymm3, ymm13
	vaesenclast ymm4, ymm4, ymm13
	vaesenclast ymm5, ymm5, ymm13
	vaesenclast ymm6, ymm6, ymm13
	vmovdqu ymm13, YMMWORD PTR [rdx]
	vpxor ymm3, ymm3, ymm13
	vmovdqu YMMWORD PTR [rdx], ymm3
	vmovdqu ymm13, YMMWORD PTR [rdx+32]
	vpxor ymm4, ymm4, ymm13
	vmovdqu YMMWORD PTR [rdx+32], ymm4
	vmovdqu ymm13, YMMWORD PTR [rdx+64]
	vpxor ymm5, ymm5, ymm13
	vmovdqu YMMWORD PTR [rdx+64], ymm5
	vmovdqu ymm13, YMMWORD PTR [rdx+96]
	vpxor ymm6, ymm6, ymm13
	vmovdqu YMMWORD PTR [rdx+96], ymm6
	vmovdqa ymm3, ymm14
	vpaddd ymm14, ymm14, ymm15
	vmovdqa ymm4, ymm14
	vpaddd ymm14, ymm14, ymm15
	vmovdqa ymm5, ymm14
	vpaddd ymm14, ymm14, ymm15
	vmovdqa ymm6, ymm14
	vpaddd ymm14, ymm14, ymm15
	vbroadcasti128 ymm13, XMMWORD PTR [rdi]
	vpxor ymm3, ymm3, ymm13
	vpxor ymm4, ymm4, ymm13
	vpxor ymm5, ymm5, ymm13
	vpxor ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+16]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+32]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+48]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+64]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+80]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+96]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+112]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+128]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+144]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	cmp rsi, 10
	je 284f
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+160]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+176]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	cmp rsi, 12
	je 286f
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+192]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+208]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	jmp 287f
286:
287:
	jmp 285f
284:
285:
	vbroadcasti128 ymm13, XMMWORD PTR [r10]
	vaesenclast ymm3, ymm3, ymm13
	vaesenclast ymm4, ymm4, ymm13
	vaesenclast ymm5, ymm5, ymm13
	vaesenclast ymm6, ymm6, ymm13
	vmovdqu ymm13, YMMWORD PTR [rdx+128]
	vpxor ymm3, ymm3, ymm13
	vmovdqu YMMWORD PTR [rdx+128], ymm3
	vmovdqu ymm13, YMMWORD PTR [rdx+160]
	vpxor ymm4, ymm4, ymm13
	vmovdqu YMMWORD PTR [rdx+160], ymm4
	vmovdqu ymm13, YMMWORD PTR [rdx+192]
	vpxor ymm5, ymm5, ymm13
	vmovdqu YMMWORD PTR [rdx+192], ymm5
	vmovdqu ymm13, YMMWORD PTR [rdx+224]
	vpxor ymm6, ymm6, ymm13
	vmovdqu YMMWORD PTR [rdx+224], ymm6
	cmp r9, 32
	jb 288f
290:
	vpxor ymm8, ymm8, ymm8
	vpxor ymm9, ymm9, ymm9
	vpxor ymm10, ymm10, ymm10
	vmovdqa ymm3, ymm14
	vpaddd ymm14, ymm14, ymm15
	vmovdqa ymm4, ymm14
	vpaddd ymm14, ymm14, ymm15
	vmovdqa ymm5, ymm14
	vpaddd ymm14, ymm14, ymm15
	vmovdqa ymm6, ymm14
	vpaddd ymm14, ymm14, ymm15
	vbroadcasti128 ymm13, XMMWORD PTR [rdi]
	vpxor ymm3, ymm3, ymm13
	vpxor ymm4, ymm4, ymm13
	vpxor ymm5, ymm5, ymm13
	vpxor ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+16]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vmovdqu ymm12, YMMWORD PTR [r11+32]
	vmovdqu ymm7, YMMWORD PTR [rdx+32]
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+32]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vmovdqu ymm12, YMMWORD PTR [r11+64]
	vmovdqu ymm7, YMMWORD PTR [rdx+64]
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+48]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vmovdqu ymm12, YMMWORD PTR [r11+96]
	vmovdqu ymm7, YMMWORD PTR [rdx+96]
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+64]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vmovdqu ymm12, YMMWORD PTR [r11+128]
	vmovdqu ymm7, YMMWORD PTR [rdx+128]
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+80]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+96]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+112]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+128]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+144]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	cmp rsi, 10
	je 291f
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+160]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+176]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	cmp rsi, 12
	je 293f
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+192]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+208]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	jmp 294f
293:
294:
	jmp 292f
291:
292:
	vbroadcasti128 ymm13, XMMWORD PTR [r10]
	vaesenclast ymm3, ymm3, ymm13
	vaesenclast ymm4, ymm4, ymm13
	vaesenclast ymm5, ymm5, ymm13
	vaesenclast ymm6, ymm6, ymm13
	vmovdqu ymm13, YMMWORD PTR [rdx+256]
	vpxor ymm3, ymm3, ymm13
	vmovdqu YMMWORD PTR [rdx+256], ymm3
	vmovdqu ymm13, YMMWORD PTR [rdx+288]
	vpxor ymm4, ymm4, ymm13
	vmovdqu YMMWORD PTR [rdx+288], ymm4
	vmovdqu ymm13, YMMWORD PTR [rdx+320]
	vpxor ymm5, ymm5, ymm13
	vmovdqu YMMWORD PTR [rdx+320], ymm5
	vmovdqu ymm13, YMMWORD PTR [rdx+352]
	vpxor ymm6, ymm6, ymm13
	vmovdqu YMMWORD PTR [rdx+352], ymm6
	vmovdqa ymm3, ymm14
	vpaddd ymm14, ymm14, ymm15
	vmovdqa ymm4, ymm14
	vpaddd ymm14, ymm14, ymm15
	vmovdqa ymm5, ymm14
	vpaddd ymm14, ymm14, ymm15
	vmovdqa ymm6, ymm14
	vpaddd ymm14, ymm14, ymm15
	vbroadcasti128 ymm13, XMMWORD PTR [rdi]
	vpxor ymm3, ymm3, ymm13
	vpxor ymm4, ymm4, ymm13
	vpxor ymm5, ymm5, ymm13
	vpxor ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+16]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vmovdqu ymm12, YMMWORD PTR [r11+160]
	vmovdqu ymm7, YMMWORD PTR [rdx+160]
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+32]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vmovdqu ymm12, YMMWORD PTR [r11+192]
	vmovdqu ymm7, YMMWORD PTR [rdx+192]
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+48]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vmovdqu ymm12, YMMWORD PTR [r11+224]
	vmovdqu ymm7, YMMWORD PTR [rdx+224]
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+64]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vmovdqu ymm12, YMMWORD PTR [r11]
	vmovdqu ymm7, YMMWORD PTR [rdx]
	vpxor ymm7, ymm7, ymm2
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+80]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vpsrldq ymm11, ymm9, 8
	vpxor ymm10, ymm10, ymm11
	vpslldq ymm9, ymm9, 8
	vpxor ymm8, ymm8, ymm9
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpxor ymm7, ymm10, ymm8
	vextracti128 xmm11, ymm7, 1
	vpxor xmm2, xmm7, xmm11
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+96]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+112]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+128]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+144]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	cmp rsi, 10
	je 295f
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+160]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+176]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	cmp rsi, 12
	je 297f
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+192]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+208]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	jmp 298f
297:
298:
	jmp 296f
295:
296:
	vbroadcasti128 ymm13, XMMWORD PTR [r10]
	vaesenclast ymm3, ymm3, ymm13
	vaesenclast ymm4, ymm4, ymm13
	vaesenclast ymm5, ymm5, ymm13
	vaesenclast ymm6, ymm6, ymm13
	vmovdqu ymm13, YMMWORD PTR [rdx+384]
	vpxor ymm3, ymm3, ymm13
	vmovdqu YMMWORD PTR [rdx+384], ymm3
	vmovdqu ymm13, YMMWORD PTR [rdx+416]
	vpxor ymm4, ymm4, ymm13
	vmovdqu YMMWORD PTR [rdx+416], ymm4
	vmovdqu ymm13, YMMWORD PTR [rdx+448]
	vpxor ymm5, ymm5, ymm13
	vmovdqu YMMWORD PTR [rdx+448], ymm5
	vmovdqu ymm13, YMMWORD PTR [rdx+480]
	vpxor ymm6, ymm6, ymm13
	vmovdqu YMMWORD PTR [rdx+480], ymm6
	add rdx, 256
	sub r9, 16
	cmp r9, 32
	jae 290b
	jmp 289f
288:
289:
	vmovdqu XMMWORD PTR [rax], xmm14
	vpxor ymm8, ymm8, ymm8
	vpxor ymm9, ymm9, ymm9
	vpxor ymm10, ymm10, ymm10
	vmovdqu ymm12, YMMWORD PTR [r11+32]
	vmovdqu ymm7, YMMWORD PTR [rdx+32]
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vmovdqu ymm12, YMMWORD PTR [r11+64]
	vmovdqu ymm7, YMMWORD PTR [rdx+64]
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vmovdqu ymm12, YMMWORD PTR [r11+96]
	vmovdqu ymm7, YMMWORD PTR [rdx+96]
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vmovdqu ymm12, YMMWORD PTR [r11+128]
	vmovdqu ymm7, YMMWORD PTR [rdx+128]
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vmovdqu ymm12, YMMWORD PTR [r11+160]
	vmovdqu ymm7, YMMWORD PTR [rdx+160]
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vmovdqu ymm12, YMMWORD PTR [r11+192]
	vmovdqu ymm7, YMMWORD PTR [rdx+192]
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vmovdqu ymm12, YMMWORD PTR [r11+224]
	vmovdqu ymm7, YMMWORD PTR [rdx+224]
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vmovdqu ymm12, YMMWORD PTR [r11]
	vmovdqu ymm7, YMMWORD PTR [rdx]
	vpxor ymm7, ymm7, ymm2
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vpsrldq ymm11, ymm9, 8
	vpxor ymm10, ymm10, ymm11
	vpslldq ymm9, ymm9, 8
	vpxor ymm8, ymm8, ymm9
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpxor ymm7, ymm10, ymm8
	vextracti128 xmm11, ymm7, 1
	vpxor xmm2, xmm7, xmm11
	vpshufb xmm2, xmm2, xmm0
	vmovdqu XMMWORD PTR [rcx], xmm2
	vzeroupper
	mov r12, QWORD PTR [r15+232]
	mov rax, QWORD PTR [r15+240]
	shr rax, 8
	shl rax, 8
	add r12, rax
	mov rbp, QWORD PTR [r15+240]
	and rbp, 255
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 299f
2101:
	mov r14d, 64
	cmp rbx, r14
	jb 2102f
	jmp 2103f
2102:
	mov r14, rbx
2103:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
2104:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 2104b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_vaes}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
	cmp rcx, 8
	jb 2105f
2107:
	vmovdqu ymm1, YMMWORD PTR [rsi]
	vmovdqu ymm0, YMMWORD PTR [r12]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12], ymm1
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vmovdqu ymm0, YMMWORD PTR [r12+32]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12+32], ymm1
	add r12, 64
	add rsi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 2107b
	vzeroupper
	test rcx, rcx
	je 2108f
2110:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 2110b
	jmp 2109f
2108:
2109:
	jmp 2106f
2105:
2111:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 2111b
2106:
	sub rbx, r14
	jne 2101b
	jmp 2100f
299:
2100:
	test rbp, rbp
	je 2112f
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_vaes}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
2114:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2114b
	jmp 2113f
2112:
2113:
	mov r12, QWORD PTR [r15+232]
	mov rax, QWORD PTR [r15+240]
	shr rax, 8
	shl rax, 8
	add r12, rax
	mov rbp, QWORD PTR [r15+240]
	and rbp, 255
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 2115f
2117:
	mov r14d, 64
	cmp rbx, r14
	jb 2118f
	jmp 2119f
2118:
	mov r14, rbx
2119:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 2120f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
2122:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 2122b
	vzeroupper
	test rcx, rcx
	je 2123f
2125:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2125b
	jmp 2124f
2123:
2124:
	jmp 2121f
2120:
2126:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2126b
2121:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_vpclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 2117b
	jmp 2116f
2115:
2116:
	test rbp, rbp
	je 2127f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
2129:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2129b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_vpclmul}
	jmp 2128f
2127:
2128:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash_vpclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	jmp 264f
263:
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rdx, rcx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 2130f
2132:
	mov r14d, 64
	cmp rbx, r14
	jb 2133f
	jmp 2134f
2133:
	mov r14, rbx
2134:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
2135:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 2135b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_vaes}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
	cmp rcx, 8
	jb 2136f
2138:
	vmovdqu ymm1, YMMWORD PTR [rsi]
	vmovdqu ymm0, YMMWORD PTR [r12]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12], ymm1
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vmovdqu ymm0, YMMWORD PTR [r12+32]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12+32], ymm1
	add r12, 64
	add rsi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 2138b
	vzeroupper
	test rcx, rcx
	je 2139f
2141:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 2141b
	jmp 2140f
2139:
2140:
	jmp 2137f
2136:
2142:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 2142b
2137:
	sub rbx, r14
	jne 2132b
	jmp 2131f
2130:
2131:
	test rbp, rbp
	je 2143f
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_vaes}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
2145:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2145b
	jmp 2144f
2143:
2144:
	mov rax, QWORD PTR [r15+224]
	shr rax, 4
	mov rdx, QWORD PTR [r15+240]
	shr rdx, 4
	add rax, rdx
	cmp rax, 62
	jae 2146f
	mov rdi, r15
	add rdi, 488
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 2148f
	mov r14, rbx
	mov rcx, r14
	cmp rcx, 8
	jb 2150f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
2152:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 2152b
	vzeroupper
	test rcx, rcx
	je 2153f
2155:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2155b
	jmp 2154f
2153:
2154:
	jmp 2151f
2150:
2156:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2156b
2151:
	jmp 2149f
2148:
2149:
	test rbp, rbp
	je 2157f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
2159:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2159b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 2158f
2157:
2158:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 2160f
	mov r14, rbx
	mov rcx, r14
	cmp rcx, 8
	jb 2162f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
2164:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 2164b
	vzeroupper
	test rcx, rcx
	je 2165f
2167:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2167b
	jmp 2166f
2165:
2166:
	jmp 2163f
2162:
2168:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2168b
2163:
	jmp 2161f
2160:
2161:
	test rbp, rbp
	je 2169f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
2171:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2171b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 2170f
2169:
2170:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	mov rcx, rdi
	sub rcx, r15
	shr rcx, 4
	sub rcx, 29
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	call {vg_ghash_vpclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	jmp 2147f
2146:
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 2172f
2174:
	mov r14d, 64
	cmp rbx, r14
	jb 2175f
	jmp 2176f
2175:
	mov r14, rbx
2176:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 2177f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
2179:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 2179b
	vzeroupper
	test rcx, rcx
	je 2180f
2182:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2182b
	jmp 2181f
2180:
2181:
	jmp 2178f
2177:
2183:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2183b
2178:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_vpclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 2174b
	jmp 2173f
2172:
2173:
	test rbp, rbp
	je 2184f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
2186:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2186b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_vpclmul}
	jmp 2185f
2184:
2185:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 2187f
2189:
	mov r14d, 64
	cmp rbx, r14
	jb 2190f
	jmp 2191f
2190:
	mov r14, rbx
2191:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 2192f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
2194:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 2194b
	vzeroupper
	test rcx, rcx
	je 2195f
2197:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2197b
	jmp 2196f
2195:
2196:
	jmp 2193f
2192:
2198:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2198b
2193:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_vpclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 2189b
	jmp 2188f
2187:
2188:
	test rbp, rbp
	je 2199f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
2201:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2201b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_vpclmul}
	jmp 2200f
2199:
2200:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash_vpclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
2147:
264:
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_vaes}
	mov rax, QWORD PTR [r15]
	xor rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+8]
	xor rdx, QWORD PTR [r15+136]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+192], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov r11d, 0
	sub r11, QWORD PTR [r15+192]
	mov r10d, 0
	mov rcx, rbp
	shr rcx, 4
	test rcx, rcx
	je 2202f
	movq xmm0, r11
	punpcklqdq xmm0, xmm0
2204:
	movdqu xmm1, XMMWORD PTR [r12+r10*1]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [r12+r10*1], xmm1
	add r10, 16
	sub rcx, 1
	jne 2204b
	jmp 2203f
2202:
2203:
	cmp r10, rbp
	je 2205f
2207:
	movzx eax, BYTE PTR [r12+r10*1]
	and rax, r11
	mov BYTE PTR [r12+r10*1], al
	add r10, 1
	cmp r10, rbp
	jne 2207b
	jmp 2206f
2205:
2206:
	mov rax, QWORD PTR [r15+192]
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
	jmp 21b
	.p2align 6

vg_aes_gcm_siv_seal_aesni_pclmul_avx_avx2:
	mov rax, QWORD PTR [rsp+8]
	or rax, r8
	cmp rax, 128
	jae 20f
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov r10, rsi
	shl r10, 4
	add r10, rdi
	mov rdx, QWORD PTR [r15+208]
	mov ebx, 0
22:
	mov rax, QWORD PTR [rdx+4]
	movq xmm2, rax
	mov eax, DWORD PTR [rdx]
	shl rax, 32
	or rax, rbx
	movq xmm0, rax
	punpcklqdq xmm0, xmm2
	or rax, 1
	movq xmm1, rax
	punpcklqdq xmm1, xmm2
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	cmp rsi, 10
	je 23f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	cmp rsi, 12
	je 25f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	jmp 26f
25:
26:
	jmp 24f
23:
24:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	punpcklqdq xmm0, xmm1
	mov rax, rbx
	shl rax, 3
	add rax, r15
	movdqu XMMWORD PTR [rax+16], xmm0
	add rbx, 2
	mov rax, rsi
	shr rax, 1
	sub rax, 1
	cmp rbx, rax
	jne 22b
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
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
	je 27f
	cmp rsi, 32
	je 29f
	movdqa xmm13, xmm5
	pxor xmm13, xmm6
	pxor xmm13, xmm8
	pxor xmm13, xmm9
	movdqa xmm14, xmm13
	paddd xmm14, xmm14
	movabs rax, 868928702305472013
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqu xmm1, XMMWORD PTR [rdi]
	movdqu XMMWORD PTR [rdx], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm5
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+16], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm6
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+32], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm7
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+48], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm8
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+64], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm9
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+80], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm10
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+96], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm11
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+112], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm12
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+128], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm13
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+144], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm14
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+160], xmm1
	jmp 210f
29:
	movabs rax, 868928702305472013
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	pxor xmm15, xmm15
	movdqu xmm1, XMMWORD PTR [rdi]
	movdqu xmm2, XMMWORD PTR [rdi+16]
	movdqu XMMWORD PTR [rdx], xmm1
	movdqu XMMWORD PTR [rdx+16], xmm2
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm11
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+224], xmm1
210:
	jmp 28f
27:
	movabs rax, 290207319600858629
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqu xmm1, XMMWORD PTR [rdi]
	movdqu xmm2, XMMWORD PTR [rdi+8]
	psrldq xmm2, 8
	movdqu XMMWORD PTR [rdx], xmm1
	movdqu XMMWORD PTR [rdx+16], xmm2
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm12
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+192], xmm1
28:
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	movq xmm7, rax
	movq xmm11, rdx
	punpcklqdq xmm7, xmm11
	movabs rax, 0
	movq xmm1, rax
	movabs rax, -4467570830351532032
	movq xmm12, rax
	punpcklqdq xmm1, xmm12
	movabs rax, 1
	movq xmm13, rax
	movabs rax, -4467570830351532032
	movq xmm12, rax
	punpcklqdq xmm13, xmm12
	movabs rax, -1
	movq xmm14, rax
	punpcklqdq xmm14, xmm14
	movdqa xmm3, xmm7
	psllq xmm3, 1
	movdqa xmm11, xmm7
	psrlq xmm11, 63
	pslldq xmm11, 8
	por xmm3, xmm11
	pshufd xmm11, xmm7, 255
	psrld xmm11, 31
	paddd xmm11, xmm14
	pandn xmm11, xmm13
	pxor xmm3, xmm11
	pxor xmm2, xmm2
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	test rbx, rbx
	je 211f
213:
	movdqu xmm7, XMMWORD PTR [r12]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	add r12, 16
	sub rbx, 1
	jne 213b
	jmp 212f
211:
212:
	mov rsi, r12
	mov rcx, rbp
	and rcx, 15
	test rcx, rcx
	je 214f
	mov rdi, r15
	add rdi, 128
	pxor xmm7, xmm7
	movdqu XMMWORD PTR [rdi], xmm7
	mov r10d, 0
216:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 216b
	movdqu xmm7, XMMWORD PTR [rdi]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	jmp 215f
214:
215:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	test rbx, rbx
	je 217f
	cmp rbx, 4
	jb 219f
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm4, xmm10
	pxor xmm4, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm5, xmm10
	pxor xmm5, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm6, xmm10
	pxor xmm6, xmm8
221:
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqu xmm7, XMMWORD PTR [r12]
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 16
	pxor xmm9, xmm11
	movdqu xmm7, XMMWORD PTR [r12+16]
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm5, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm5, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm5, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm5, 16
	pxor xmm9, xmm11
	movdqu xmm7, XMMWORD PTR [r12+32]
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm4, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm4, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm4, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm4, 16
	pxor xmm9, xmm11
	movdqu xmm7, XMMWORD PTR [r12+48]
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	add r12, 64
	sub rbx, 4
	cmp rbx, 4
	jae 221b
	jmp 220f
219:
220:
	test rbx, rbx
	je 222f
224:
	movdqu xmm7, XMMWORD PTR [r12]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	add r12, 16
	sub rbx, 1
	jne 224b
	jmp 223f
222:
223:
	jmp 218f
217:
218:
	mov rsi, r12
	mov rcx, rbp
	and rcx, 15
	test rcx, rcx
	je 225f
	mov rdi, r15
	add rdi, 128
	pxor xmm7, xmm7
	movdqu XMMWORD PTR [rdi], xmm7
	mov r10d, 0
227:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 227b
	movdqu xmm7, XMMWORD PTR [rdi]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	jmp 226f
225:
226:
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, QWORD PTR [r15+240]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	movq xmm7, rax
	movq xmm11, rdx
	punpcklqdq xmm7, xmm11
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	movq rax, xmm2
	psrldq xmm2, 8
	movq rdx, xmm2
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov r10, rsi
	shl r10, 4
	add r10, rdi
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	cmp rsi, 10
	je 228f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 230f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 231f
230:
231:
	jmp 229f
228:
229:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	movdqu XMMWORD PTR [r15], xmm0
	movdqu xmm0, XMMWORD PTR [r15]
	movabs rax, -9223372036854775808
	movq xmm9, rax
	pslldq xmm9, 8
	por xmm9, xmm0
	mov eax, 1
	movq xmm10, rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov r10, rsi
	shl r10, 4
	add r10, rdi
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 232f
	cmp rbx, 4
	jb 234f
236:
	movdqa xmm0, xmm9
	paddd xmm9, xmm10
	movdqa xmm1, xmm9
	paddd xmm9, xmm10
	movdqa xmm2, xmm9
	paddd xmm9, xmm10
	movdqa xmm3, xmm9
	paddd xmm9, xmm10
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	pxor xmm2, xmm8
	pxor xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	cmp rsi, 10
	je 237f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	cmp rsi, 12
	je 239f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	jmp 240f
239:
240:
	jmp 238f
237:
238:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	aesenclast xmm2, xmm8
	aesenclast xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [r12]
	pxor xmm0, xmm8
	movdqu XMMWORD PTR [r12], xmm0
	movdqu xmm8, XMMWORD PTR [r12+16]
	pxor xmm1, xmm8
	movdqu XMMWORD PTR [r12+16], xmm1
	movdqu xmm8, XMMWORD PTR [r12+32]
	pxor xmm2, xmm8
	movdqu XMMWORD PTR [r12+32], xmm2
	movdqu xmm8, XMMWORD PTR [r12+48]
	pxor xmm3, xmm8
	movdqu XMMWORD PTR [r12+48], xmm3
	add r12, 64
	sub rbx, 4
	cmp rbx, 4
	jae 236b
	jmp 235f
234:
235:
	test rbx, rbx
	je 241f
243:
	movdqa xmm0, xmm9
	paddd xmm9, xmm10
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	cmp rsi, 10
	je 244f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 246f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 247f
246:
247:
	jmp 245f
244:
245:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r12]
	pxor xmm0, xmm8
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	sub rbx, 1
	jne 243b
	jmp 242f
241:
242:
	jmp 233f
232:
233:
	test rbp, rbp
	je 248f
	movdqa xmm0, xmm9
	paddd xmm9, xmm10
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	cmp rsi, 10
	je 250f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 252f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 253f
252:
253:
	jmp 251f
250:
251:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	mov rsi, r15
	add rsi, 128
	movdqu XMMWORD PTR [rsi], xmm0
	mov rdi, r12
	mov rcx, rbp
	mov r10d, 0
254:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 254b
	jmp 249f
248:
249:
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [rcx], rax
	mov rax, QWORD PTR [r15+8]
	mov QWORD PTR [rcx+8], rax
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
21:
	ret
20:
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov ebx, 0
	mov rdi, r15
	add rdi, 488
	mov rbp, QWORD PTR [r15+200]
	shr rbp, 1
	sub rbp, 1
255:
	mov rax, QWORD PTR [r15+208]
	mov ecx, DWORD PTR [rax]
	shl rcx, 32
	or rcx, rbx
	mov rdx, QWORD PTR [rax+4]
	movq xmm0, rcx
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rdi, 16
	add rbx, 1
	cmp rbx, rbp
	jne 255b
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, rbp
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_aesni}
	mov rsi, r15
	add rsi, 488
	mov rdi, r15
	add rdi, 16
	mov rcx, rbp
256:
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+16]
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 32
	add rdi, 16
	sub rcx, 2
	jne 256b
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	bswap rdx
	bswap rax
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+64], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+80], xmm0
	mov rax, QWORD PTR [r15+240]
	cmp rax, 256
	jb 257f
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 259f
261:
	mov r14d, 64
	cmp rbx, r14
	jb 262f
	jmp 263f
262:
	mov r14, rbx
263:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 264f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
266:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 266b
	vzeroupper
	test rcx, rcx
	je 267f
269:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 269b
	jmp 268f
267:
268:
	jmp 265f
264:
270:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 270b
265:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_pclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 261b
	jmp 260f
259:
260:
	test rbp, rbp
	je 271f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
273:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 273b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_pclmul}
	jmp 272f
271:
272:
	mov rcx, r15
	add rcx, 80
	mov r8, r15
	add r8, 64
	mov r11, r15
	add r11, 1512
	mov rdx, QWORD PTR [r15+232]
	mov r9, QWORD PTR [r15+240]
	shr r9, 8
	add r9, r9
	add r9, r9
	add r9, r9
	add r9, r9
	movabs rax, 579005069656919567
	movq xmm0, rax
	movabs rax, 283686952306183
	movq xmm12, rax
	punpcklqdq xmm0, xmm12
	movabs rax, 0
	movq xmm1, rax
	movabs rax, -4467570830351532032
	movq xmm12, rax
	punpcklqdq xmm1, xmm12
	movdqu xmm7, XMMWORD PTR [r8]
	pshufb xmm7, xmm0
	movabs rax, 1
	movq xmm13, rax
	movabs rax, -4467570830351532032
	movq xmm12, rax
	punpcklqdq xmm13, xmm12
	movabs rax, -1
	movq xmm14, rax
	punpcklqdq xmm14, xmm14
	movdqa xmm3, xmm7
	psllq xmm3, 1
	movdqa xmm11, xmm7
	psrlq xmm11, 63
	pslldq xmm11, 8
	por xmm3, xmm11
	pshufd xmm11, xmm7, 255
	psrld xmm11, 31
	paddd xmm11, xmm14
	pandn xmm11, xmm13
	pxor xmm3, xmm11
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm4, xmm10
	pxor xmm4, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm5, xmm10
	pxor xmm5, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm6, xmm10
	pxor xmm6, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm12, xmm10
	pxor xmm12, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm4, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm4, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm4, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm4, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm13, xmm10
	pxor xmm13, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm5, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm5, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm5, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm5, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm14, xmm10
	pxor xmm14, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm6, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm6, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm6, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm6, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm15, xmm10
	pxor xmm15, xmm8
	movdqu XMMWORD PTR [r11], xmm15
	movdqu XMMWORD PTR [r11+16], xmm14
	movdqu XMMWORD PTR [r11+32], xmm13
	movdqu XMMWORD PTR [r11+48], xmm12
	movdqu XMMWORD PTR [r11+64], xmm6
	movdqu XMMWORD PTR [r11+80], xmm5
	movdqu XMMWORD PTR [r11+96], xmm4
	movdqu XMMWORD PTR [r11+112], xmm3
	movdqu XMMWORD PTR [r11+144], xmm1
	movdqu xmm2, XMMWORD PTR [rcx]
	pshufb xmm2, xmm0
274:
	vmovdqu xmm12, XMMWORD PTR [r11+16]
	vmovdqu xmm7, XMMWORD PTR [rdx+16]
	vpclmulqdq xmm8, xmm7, xmm12, 0
	vpclmulqdq xmm10, xmm7, xmm12, 17
	vpclmulqdq xmm9, xmm7, xmm12, 1
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+32]
	vmovdqu xmm7, XMMWORD PTR [rdx+32]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+48]
	vmovdqu xmm7, XMMWORD PTR [rdx+48]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+64]
	vmovdqu xmm7, XMMWORD PTR [rdx+64]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+80]
	vmovdqu xmm7, XMMWORD PTR [rdx+80]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+96]
	vmovdqu xmm7, XMMWORD PTR [rdx+96]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+112]
	vmovdqu xmm7, XMMWORD PTR [rdx+112]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11]
	vmovdqu xmm7, XMMWORD PTR [rdx]
	vpxor xmm7, xmm7, xmm2
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+144]
	vpclmulqdq xmm11, xmm8, xmm12, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm9, xmm9, xmm8
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm9, xmm12, 16
	vpshufd xmm9, xmm9, 78
	vpxor xmm2, xmm10, xmm9
	vpxor xmm2, xmm2, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+16]
	vmovdqu xmm7, XMMWORD PTR [rdx+144]
	vpclmulqdq xmm8, xmm7, xmm12, 0
	vpclmulqdq xmm10, xmm7, xmm12, 17
	vpclmulqdq xmm9, xmm7, xmm12, 1
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+32]
	vmovdqu xmm7, XMMWORD PTR [rdx+160]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+48]
	vmovdqu xmm7, XMMWORD PTR [rdx+176]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+64]
	vmovdqu xmm7, XMMWORD PTR [rdx+192]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+80]
	vmovdqu xmm7, XMMWORD PTR [rdx+208]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+96]
	vmovdqu xmm7, XMMWORD PTR [rdx+224]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+112]
	vmovdqu xmm7, XMMWORD PTR [rdx+240]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11]
	vmovdqu xmm7, XMMWORD PTR [rdx+128]
	vpxor xmm7, xmm7, xmm2
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+144]
	vpclmulqdq xmm11, xmm8, xmm12, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm9, xmm9, xmm8
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm9, xmm12, 16
	vpshufd xmm9, xmm9, 78
	vpxor xmm2, xmm10, xmm9
	vpxor xmm2, xmm2, xmm11
	add rdx, 256
	sub r9, 16
	jne 274b
	movabs rax, 579005069656919567
	movq xmm0, rax
	movabs rax, 283686952306183
	movq xmm12, rax
	punpcklqdq xmm0, xmm12
	vpshufb xmm2, xmm2, xmm0
	vmovdqu XMMWORD PTR [rcx], xmm2
	mov r12, QWORD PTR [r15+232]
	mov rax, QWORD PTR [r15+240]
	shr rax, 8
	shl rax, 8
	add r12, rax
	mov rbp, QWORD PTR [r15+240]
	and rbp, 255
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 275f
277:
	mov r14d, 64
	cmp rbx, r14
	jb 278f
	jmp 279f
278:
	mov r14, rbx
279:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 280f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
282:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 282b
	vzeroupper
	test rcx, rcx
	je 283f
285:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 285b
	jmp 284f
283:
284:
	jmp 281f
280:
286:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 286b
281:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_pclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 277b
	jmp 276f
275:
276:
	test rbp, rbp
	je 287f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
289:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 289b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_pclmul}
	jmp 288f
287:
288:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	jmp 258f
257:
	mov rax, QWORD PTR [r15+224]
	shr rax, 4
	mov rdx, QWORD PTR [r15+240]
	shr rdx, 4
	add rax, rdx
	cmp rax, 62
	jae 290f
	mov rdi, r15
	add rdi, 488
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 292f
	mov r14, rbx
	mov rcx, r14
	cmp rcx, 8
	jb 294f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
296:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 296b
	vzeroupper
	test rcx, rcx
	je 297f
299:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 299b
	jmp 298f
297:
298:
	jmp 295f
294:
2100:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2100b
295:
	jmp 293f
292:
293:
	test rbp, rbp
	je 2101f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
2103:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2103b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 2102f
2101:
2102:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 2104f
	mov r14, rbx
	mov rcx, r14
	cmp rcx, 8
	jb 2106f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
2108:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 2108b
	vzeroupper
	test rcx, rcx
	je 2109f
2111:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2111b
	jmp 2110f
2109:
2110:
	jmp 2107f
2106:
2112:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2112b
2107:
	jmp 2105f
2104:
2105:
	test rbp, rbp
	je 2113f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
2115:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2115b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 2114f
2113:
2114:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	mov rcx, rdi
	sub rcx, r15
	shr rcx, 4
	sub rcx, 29
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	jmp 291f
290:
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 2116f
2118:
	mov r14d, 64
	cmp rbx, r14
	jb 2119f
	jmp 2120f
2119:
	mov r14, rbx
2120:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 2121f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
2123:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 2123b
	vzeroupper
	test rcx, rcx
	je 2124f
2126:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2126b
	jmp 2125f
2124:
2125:
	jmp 2122f
2121:
2127:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2127b
2122:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_pclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 2118b
	jmp 2117f
2116:
2117:
	test rbp, rbp
	je 2128f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
2130:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2130b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_pclmul}
	jmp 2129f
2128:
2129:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 2131f
2133:
	mov r14d, 64
	cmp rbx, r14
	jb 2134f
	jmp 2135f
2134:
	mov r14, rbx
2135:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 2136f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
2138:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 2138b
	vzeroupper
	test rcx, rcx
	je 2139f
2141:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2141b
	jmp 2140f
2139:
2140:
	jmp 2137f
2136:
2142:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2142b
2137:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_pclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 2133b
	jmp 2132f
2131:
2132:
	test rbp, rbp
	je 2143f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
2145:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2145b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_pclmul}
	jmp 2144f
2143:
2144:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
291:
258:
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
	mov rcx, r15
	add rcx, 1768
	call {vg_aes_expand_key_scratch_aesni}
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 0
	call {vg_aes_ctr32_aesni}
	mov rax, QWORD PTR [r15+240]
	cmp rax, 256
	jb 2146f
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rax, rcx
	mov QWORD PTR [r15+104], rax
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 96
	mov rcx, r15
	add rcx, 80
	mov r8, r15
	add r8, 64
	mov r11, r15
	add r11, 1768
	mov r12, QWORD PTR [r15+232]
	mov r9, QWORD PTR [r15+240]
	shr r9, 8
	add r9, r9
	add r9, r9
	add r9, r9
	add r9, r9
	mov r10d, 1
	movq xmm11, r10
	movdqu XMMWORD PTR [r11+128], xmm11
	mov r10, rsi
	shl r10, 4
	add r10, rdi
	mov rax, rdx
	mov rdx, r12
2148:
	vmovdqu xmm11, XMMWORD PTR [rax]
	vmovdqu xmm12, XMMWORD PTR [r11+128]
	vmovdqa xmm0, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm3, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm4, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm5, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm6, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm13, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm14, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm15, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqu XMMWORD PTR [rax], xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi]
	vpxor xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm1
	vpxor xmm4, xmm4, xmm1
	vpxor xmm5, xmm5, xmm1
	vpxor xmm6, xmm6, xmm1
	vpxor xmm13, xmm13, xmm1
	vpxor xmm14, xmm14, xmm1
	vpxor xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+16]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+32]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+48]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+64]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+80]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+96]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+112]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+128]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+144]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	cmp rsi, 10
	je 2149f
	vmovdqu xmm1, XMMWORD PTR [rdi+160]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+176]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	cmp rsi, 12
	je 2151f
	vmovdqu xmm1, XMMWORD PTR [rdi+192]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+208]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	jmp 2152f
2151:
2152:
	jmp 2150f
2149:
2150:
	vmovdqu xmm1, XMMWORD PTR [r10]
	vaesenclast xmm0, xmm0, xmm1
	vaesenclast xmm3, xmm3, xmm1
	vaesenclast xmm4, xmm4, xmm1
	vaesenclast xmm5, xmm5, xmm1
	vaesenclast xmm6, xmm6, xmm1
	vaesenclast xmm13, xmm13, xmm1
	vaesenclast xmm14, xmm14, xmm1
	vaesenclast xmm15, xmm15, xmm1
	vpxor xmm0, xmm0, XMMWORD PTR [rdx]
	vmovdqu XMMWORD PTR [rdx], xmm0
	vpxor xmm3, xmm3, XMMWORD PTR [rdx+16]
	vmovdqu XMMWORD PTR [rdx+16], xmm3
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+32]
	vmovdqu XMMWORD PTR [rdx+32], xmm4
	vpxor xmm5, xmm5, XMMWORD PTR [rdx+48]
	vmovdqu XMMWORD PTR [rdx+48], xmm5
	vpxor xmm6, xmm6, XMMWORD PTR [rdx+64]
	vmovdqu XMMWORD PTR [rdx+64], xmm6
	vpxor xmm13, xmm13, XMMWORD PTR [rdx+80]
	vmovdqu XMMWORD PTR [rdx+80], xmm13
	vpxor xmm14, xmm14, XMMWORD PTR [rdx+96]
	vmovdqu XMMWORD PTR [rdx+96], xmm14
	vpxor xmm15, xmm15, XMMWORD PTR [rdx+112]
	vmovdqu XMMWORD PTR [rdx+112], xmm15
	vmovdqu xmm11, XMMWORD PTR [rax]
	vmovdqu xmm12, XMMWORD PTR [r11+128]
	vmovdqa xmm0, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm3, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm4, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm5, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm6, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm13, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm14, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm15, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqu XMMWORD PTR [rax], xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi]
	vpxor xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm1
	vpxor xmm4, xmm4, xmm1
	vpxor xmm5, xmm5, xmm1
	vpxor xmm6, xmm6, xmm1
	vpxor xmm13, xmm13, xmm1
	vpxor xmm14, xmm14, xmm1
	vpxor xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+16]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+32]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+48]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+64]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+80]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+96]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+112]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+128]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+144]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	cmp rsi, 10
	je 2153f
	vmovdqu xmm1, XMMWORD PTR [rdi+160]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+176]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	cmp rsi, 12
	je 2155f
	vmovdqu xmm1, XMMWORD PTR [rdi+192]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+208]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	jmp 2156f
2155:
2156:
	jmp 2154f
2153:
2154:
	vmovdqu xmm1, XMMWORD PTR [r10]
	vaesenclast xmm0, xmm0, xmm1
	vaesenclast xmm3, xmm3, xmm1
	vaesenclast xmm4, xmm4, xmm1
	vaesenclast xmm5, xmm5, xmm1
	vaesenclast xmm6, xmm6, xmm1
	vaesenclast xmm13, xmm13, xmm1
	vaesenclast xmm14, xmm14, xmm1
	vaesenclast xmm15, xmm15, xmm1
	vpxor xmm0, xmm0, XMMWORD PTR [rdx+128]
	vmovdqu XMMWORD PTR [rdx+128], xmm0
	vpxor xmm3, xmm3, XMMWORD PTR [rdx+144]
	vmovdqu XMMWORD PTR [rdx+144], xmm3
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+160]
	vmovdqu XMMWORD PTR [rdx+160], xmm4
	vpxor xmm5, xmm5, XMMWORD PTR [rdx+176]
	vmovdqu XMMWORD PTR [rdx+176], xmm5
	vpxor xmm6, xmm6, XMMWORD PTR [rdx+192]
	vmovdqu XMMWORD PTR [rdx+192], xmm6
	vpxor xmm13, xmm13, XMMWORD PTR [rdx+208]
	vmovdqu XMMWORD PTR [rdx+208], xmm13
	vpxor xmm14, xmm14, XMMWORD PTR [rdx+224]
	vmovdqu XMMWORD PTR [rdx+224], xmm14
	vpxor xmm15, xmm15, XMMWORD PTR [rdx+240]
	vmovdqu XMMWORD PTR [rdx+240], xmm15
	add rdx, 256
	sub r9, 16
	jne 2148b
	mov r12, QWORD PTR [r15+232]
	mov rax, QWORD PTR [r15+240]
	shr rax, 8
	shl rax, 8
	add r12, rax
	mov rbp, QWORD PTR [r15+240]
	and rbp, 255
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 2157f
2159:
	mov r14d, 64
	cmp rbx, r14
	jb 2160f
	jmp 2161f
2160:
	mov r14, rbx
2161:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
2162:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 2162b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_aesni}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
	cmp rcx, 8
	jb 2163f
2165:
	vmovdqu ymm1, YMMWORD PTR [rsi]
	vmovdqu ymm0, YMMWORD PTR [r12]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12], ymm1
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vmovdqu ymm0, YMMWORD PTR [r12+32]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12+32], ymm1
	add r12, 64
	add rsi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 2165b
	vzeroupper
	test rcx, rcx
	je 2166f
2168:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 2168b
	jmp 2167f
2166:
2167:
	jmp 2164f
2163:
2169:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 2169b
2164:
	sub rbx, r14
	jne 2159b
	jmp 2158f
2157:
2158:
	test rbp, rbp
	je 2170f
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_aesni}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
2172:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2172b
	jmp 2171f
2170:
2171:
	jmp 2147f
2146:
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rdx, rcx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 2173f
2175:
	mov r14d, 64
	cmp rbx, r14
	jb 2176f
	jmp 2177f
2176:
	mov r14, rbx
2177:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
2178:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 2178b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_aesni}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
	cmp rcx, 8
	jb 2179f
2181:
	vmovdqu ymm1, YMMWORD PTR [rsi]
	vmovdqu ymm0, YMMWORD PTR [r12]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12], ymm1
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vmovdqu ymm0, YMMWORD PTR [r12+32]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12+32], ymm1
	add r12, 64
	add rsi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 2181b
	vzeroupper
	test rcx, rcx
	je 2182f
2184:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 2184b
	jmp 2183f
2182:
2183:
	jmp 2180f
2179:
2185:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 2185b
2180:
	sub rbx, r14
	jne 2175b
	jmp 2174f
2173:
2174:
	test rbp, rbp
	je 2186f
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_aesni}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
2188:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2188b
	jmp 2187f
2186:
2187:
2147:
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [rcx], rax
	mov rax, QWORD PTR [r15+8]
	mov QWORD PTR [rcx+8], rax
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
	jmp 21b
	.p2align 6

vg_aes_gcm_siv_open_aesni_pclmul_avx_avx2:
	mov rax, QWORD PTR [rsp+8]
	or rax, r8
	cmp rax, 128
	jae 20f
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+8], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov r10, rsi
	shl r10, 4
	add r10, rdi
	mov rdx, QWORD PTR [r15+208]
	mov ebx, 0
22:
	mov rax, QWORD PTR [rdx+4]
	movq xmm2, rax
	mov eax, DWORD PTR [rdx]
	shl rax, 32
	or rax, rbx
	movq xmm0, rax
	punpcklqdq xmm0, xmm2
	or rax, 1
	movq xmm1, rax
	punpcklqdq xmm1, xmm2
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	cmp rsi, 10
	je 23f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	cmp rsi, 12
	je 25f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	jmp 26f
25:
26:
	jmp 24f
23:
24:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	punpcklqdq xmm0, xmm1
	mov rax, rbx
	shl rax, 3
	add rax, r15
	movdqu XMMWORD PTR [rax+16], xmm0
	add rbx, 2
	mov rax, rsi
	shr rax, 1
	sub rax, 1
	cmp rbx, rax
	jne 22b
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
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
	je 27f
	cmp rsi, 32
	je 29f
	movdqa xmm13, xmm5
	pxor xmm13, xmm6
	pxor xmm13, xmm8
	pxor xmm13, xmm9
	movdqa xmm14, xmm13
	paddd xmm14, xmm14
	movabs rax, 868928702305472013
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqu xmm1, XMMWORD PTR [rdi]
	movdqu XMMWORD PTR [rdx], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm5
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+16], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm6
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+32], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm7
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+48], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm8
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+64], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm9
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+80], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm10
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+96], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm11
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+112], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm12
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+128], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm13
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+144], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm14
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+160], xmm1
	jmp 210f
29:
	movabs rax, 868928702305472013
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	pxor xmm15, xmm15
	movdqu xmm1, XMMWORD PTR [rdi]
	movdqu xmm2, XMMWORD PTR [rdi+16]
	movdqu XMMWORD PTR [rdx], xmm1
	movdqu XMMWORD PTR [rdx+16], xmm2
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm11
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+224], xmm1
210:
	jmp 28f
27:
	movabs rax, 290207319600858629
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqu xmm1, XMMWORD PTR [rdi]
	movdqu xmm2, XMMWORD PTR [rdi+8]
	psrldq xmm2, 8
	movdqu XMMWORD PTR [rdx], xmm1
	movdqu XMMWORD PTR [rdx+16], xmm2
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm12
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+192], xmm1
28:
	movdqu xmm0, XMMWORD PTR [r15]
	movabs rax, -9223372036854775808
	movq xmm9, rax
	pslldq xmm9, 8
	por xmm9, xmm0
	mov eax, 1
	movq xmm10, rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov r10, rsi
	shl r10, 4
	add r10, rdi
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 211f
	cmp rbx, 4
	jb 213f
215:
	movdqa xmm0, xmm9
	paddd xmm9, xmm10
	movdqa xmm1, xmm9
	paddd xmm9, xmm10
	movdqa xmm2, xmm9
	paddd xmm9, xmm10
	movdqa xmm3, xmm9
	paddd xmm9, xmm10
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	pxor xmm2, xmm8
	pxor xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	cmp rsi, 10
	je 216f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	cmp rsi, 12
	je 218f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	jmp 219f
218:
219:
	jmp 217f
216:
217:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	aesenclast xmm2, xmm8
	aesenclast xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [r12]
	pxor xmm0, xmm8
	movdqu XMMWORD PTR [r12], xmm0
	movdqu xmm8, XMMWORD PTR [r12+16]
	pxor xmm1, xmm8
	movdqu XMMWORD PTR [r12+16], xmm1
	movdqu xmm8, XMMWORD PTR [r12+32]
	pxor xmm2, xmm8
	movdqu XMMWORD PTR [r12+32], xmm2
	movdqu xmm8, XMMWORD PTR [r12+48]
	pxor xmm3, xmm8
	movdqu XMMWORD PTR [r12+48], xmm3
	add r12, 64
	sub rbx, 4
	cmp rbx, 4
	jae 215b
	jmp 214f
213:
214:
	test rbx, rbx
	je 220f
222:
	movdqa xmm0, xmm9
	paddd xmm9, xmm10
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	cmp rsi, 10
	je 223f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 225f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 226f
225:
226:
	jmp 224f
223:
224:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r12]
	pxor xmm0, xmm8
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	sub rbx, 1
	jne 222b
	jmp 221f
220:
221:
	jmp 212f
211:
212:
	test rbp, rbp
	je 227f
	movdqa xmm0, xmm9
	paddd xmm9, xmm10
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	cmp rsi, 10
	je 229f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 231f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 232f
231:
232:
	jmp 230f
229:
230:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	mov rsi, r15
	add rsi, 128
	movdqu XMMWORD PTR [rsi], xmm0
	mov rdi, r12
	mov rcx, rbp
	mov r10d, 0
233:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 233b
	jmp 228f
227:
228:
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	movq xmm7, rax
	movq xmm11, rdx
	punpcklqdq xmm7, xmm11
	movabs rax, 0
	movq xmm1, rax
	movabs rax, -4467570830351532032
	movq xmm12, rax
	punpcklqdq xmm1, xmm12
	movabs rax, 1
	movq xmm13, rax
	movabs rax, -4467570830351532032
	movq xmm12, rax
	punpcklqdq xmm13, xmm12
	movabs rax, -1
	movq xmm14, rax
	punpcklqdq xmm14, xmm14
	movdqa xmm3, xmm7
	psllq xmm3, 1
	movdqa xmm11, xmm7
	psrlq xmm11, 63
	pslldq xmm11, 8
	por xmm3, xmm11
	pshufd xmm11, xmm7, 255
	psrld xmm11, 31
	paddd xmm11, xmm14
	pandn xmm11, xmm13
	pxor xmm3, xmm11
	pxor xmm2, xmm2
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	test rbx, rbx
	je 234f
236:
	movdqu xmm7, XMMWORD PTR [r12]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	add r12, 16
	sub rbx, 1
	jne 236b
	jmp 235f
234:
235:
	mov rsi, r12
	mov rcx, rbp
	and rcx, 15
	test rcx, rcx
	je 237f
	mov rdi, r15
	add rdi, 128
	pxor xmm7, xmm7
	movdqu XMMWORD PTR [rdi], xmm7
	mov r10d, 0
239:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 239b
	movdqu xmm7, XMMWORD PTR [rdi]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	jmp 238f
237:
238:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	test rbx, rbx
	je 240f
	cmp rbx, 4
	jb 242f
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm4, xmm10
	pxor xmm4, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm5, xmm10
	pxor xmm5, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm6, xmm10
	pxor xmm6, xmm8
244:
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqu xmm7, XMMWORD PTR [r12]
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 16
	pxor xmm9, xmm11
	movdqu xmm7, XMMWORD PTR [r12+16]
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm5, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm5, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm5, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm5, 16
	pxor xmm9, xmm11
	movdqu xmm7, XMMWORD PTR [r12+32]
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm4, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm4, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm4, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm4, 16
	pxor xmm9, xmm11
	movdqu xmm7, XMMWORD PTR [r12+48]
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	add r12, 64
	sub rbx, 4
	cmp rbx, 4
	jae 244b
	jmp 243f
242:
243:
	test rbx, rbx
	je 245f
247:
	movdqu xmm7, XMMWORD PTR [r12]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	add r12, 16
	sub rbx, 1
	jne 247b
	jmp 246f
245:
246:
	jmp 241f
240:
241:
	mov rsi, r12
	mov rcx, rbp
	and rcx, 15
	test rcx, rcx
	je 248f
	mov rdi, r15
	add rdi, 128
	pxor xmm7, xmm7
	movdqu XMMWORD PTR [rdi], xmm7
	mov r10d, 0
250:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 250b
	movdqu xmm7, XMMWORD PTR [rdi]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	jmp 249f
248:
249:
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, QWORD PTR [r15+240]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	movq xmm7, rax
	movq xmm11, rdx
	punpcklqdq xmm7, xmm11
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	movq rax, xmm2
	psrldq xmm2, 8
	movq rdx, xmm2
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov r10, rsi
	shl r10, 4
	add r10, rdi
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	cmp rsi, 10
	je 251f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 253f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 254f
253:
254:
	jmp 252f
251:
252:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rax, QWORD PTR [r15]
	xor rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+8]
	xor rdx, QWORD PTR [r15+136]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+192], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov r11d, 0
	sub r11, QWORD PTR [r15+192]
	mov r10d, 0
	mov rcx, rbp
	shr rcx, 4
	test rcx, rcx
	je 255f
	movq xmm0, r11
	punpcklqdq xmm0, xmm0
257:
	movdqu xmm1, XMMWORD PTR [r12+r10*1]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [r12+r10*1], xmm1
	add r10, 16
	sub rcx, 1
	jne 257b
	jmp 256f
255:
256:
	cmp r10, rbp
	je 258f
260:
	movzx eax, BYTE PTR [r12+r10*1]
	and rax, r11
	mov BYTE PTR [r12+r10*1], al
	add r10, 1
	cmp r10, rbp
	jne 260b
	jmp 259f
258:
259:
	mov rax, QWORD PTR [r15+192]
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
21:
	ret
20:
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+8], rax
	mov ebx, 0
	mov rdi, r15
	add rdi, 488
	mov rbp, QWORD PTR [r15+200]
	shr rbp, 1
	sub rbp, 1
261:
	mov rax, QWORD PTR [r15+208]
	mov ecx, DWORD PTR [rax]
	shl rcx, 32
	or rcx, rbx
	mov rdx, QWORD PTR [rax+4]
	movq xmm0, rcx
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rdi, 16
	add rbx, 1
	cmp rbx, rbp
	jne 261b
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, rbp
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_aesni}
	mov rsi, r15
	add rsi, 488
	mov rdi, r15
	add rdi, 16
	mov rcx, rbp
262:
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+16]
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 32
	add rdi, 16
	sub rcx, 2
	jne 262b
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
	mov rcx, r15
	add rcx, 1768
	call {vg_aes_expand_key_scratch_aesni}
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	bswap rdx
	bswap rax
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+64], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+80], xmm0
	mov rax, QWORD PTR [r15+240]
	cmp rax, 256
	jb 263f
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rax, rcx
	mov QWORD PTR [r15+104], rax
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 265f
267:
	mov r14d, 64
	cmp rbx, r14
	jb 268f
	jmp 269f
268:
	mov r14, rbx
269:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 270f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
272:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 272b
	vzeroupper
	test rcx, rcx
	je 273f
275:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 275b
	jmp 274f
273:
274:
	jmp 271f
270:
276:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 276b
271:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_pclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 267b
	jmp 266f
265:
266:
	test rbp, rbp
	je 277f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
279:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 279b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_pclmul}
	jmp 278f
277:
278:
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 96
	mov rcx, r15
	add rcx, 80
	mov r8, r15
	add r8, 64
	mov r11, r15
	add r11, 1768
	mov r12, QWORD PTR [r15+232]
	mov r9, QWORD PTR [r15+240]
	shr r9, 8
	add r9, r9
	add r9, r9
	add r9, r9
	add r9, r9
	movabs rax, 579005069656919567
	movq xmm0, rax
	movabs rax, 283686952306183
	movq xmm12, rax
	punpcklqdq xmm0, xmm12
	movabs rax, 0
	movq xmm1, rax
	movabs rax, -4467570830351532032
	movq xmm12, rax
	punpcklqdq xmm1, xmm12
	movdqu xmm7, XMMWORD PTR [r8]
	pshufb xmm7, xmm0
	movabs rax, 1
	movq xmm13, rax
	movabs rax, -4467570830351532032
	movq xmm12, rax
	punpcklqdq xmm13, xmm12
	movabs rax, -1
	movq xmm14, rax
	punpcklqdq xmm14, xmm14
	movdqa xmm3, xmm7
	psllq xmm3, 1
	movdqa xmm11, xmm7
	psrlq xmm11, 63
	pslldq xmm11, 8
	por xmm3, xmm11
	pshufd xmm11, xmm7, 255
	psrld xmm11, 31
	paddd xmm11, xmm14
	pandn xmm11, xmm13
	pxor xmm3, xmm11
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm4, xmm10
	pxor xmm4, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm5, xmm10
	pxor xmm5, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm6, xmm10
	pxor xmm6, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm12, xmm10
	pxor xmm12, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm4, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm4, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm4, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm4, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm13, xmm10
	pxor xmm13, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm5, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm5, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm5, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm5, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm14, xmm10
	pxor xmm14, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm6, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm6, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm6, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm6, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm15, xmm10
	pxor xmm15, xmm8
	movdqu XMMWORD PTR [r11], xmm15
	movdqu XMMWORD PTR [r11+16], xmm14
	movdqu XMMWORD PTR [r11+32], xmm13
	movdqu XMMWORD PTR [r11+48], xmm12
	movdqu XMMWORD PTR [r11+64], xmm6
	movdqu XMMWORD PTR [r11+80], xmm5
	movdqu XMMWORD PTR [r11+96], xmm4
	movdqu XMMWORD PTR [r11+112], xmm3
	movdqu XMMWORD PTR [r11+144], xmm1
	mov r10d, 1
	movq xmm11, r10
	movdqu XMMWORD PTR [r11+128], xmm11
	movdqu xmm2, XMMWORD PTR [rcx]
	pshufb xmm2, xmm0
	mov r10, rsi
	shl r10, 4
	add r10, rdi
	mov rax, rdx
	mov rdx, r12
	vmovdqu xmm11, XMMWORD PTR [rax]
	vmovdqu xmm12, XMMWORD PTR [r11+128]
	vmovdqa xmm0, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm3, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm4, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm5, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm6, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm13, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm14, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm15, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqu XMMWORD PTR [rax], xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi]
	vpxor xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm1
	vpxor xmm4, xmm4, xmm1
	vpxor xmm5, xmm5, xmm1
	vpxor xmm6, xmm6, xmm1
	vpxor xmm13, xmm13, xmm1
	vpxor xmm14, xmm14, xmm1
	vpxor xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+16]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+32]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+48]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+64]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+80]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+96]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+112]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+128]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+144]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	cmp rsi, 10
	je 280f
	vmovdqu xmm1, XMMWORD PTR [rdi+160]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+176]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	cmp rsi, 12
	je 282f
	vmovdqu xmm1, XMMWORD PTR [rdi+192]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+208]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	jmp 283f
282:
283:
	jmp 281f
280:
281:
	vmovdqu xmm1, XMMWORD PTR [r10]
	vaesenclast xmm0, xmm0, xmm1
	vaesenclast xmm3, xmm3, xmm1
	vaesenclast xmm4, xmm4, xmm1
	vaesenclast xmm5, xmm5, xmm1
	vaesenclast xmm6, xmm6, xmm1
	vaesenclast xmm13, xmm13, xmm1
	vaesenclast xmm14, xmm14, xmm1
	vaesenclast xmm15, xmm15, xmm1
	vpxor xmm0, xmm0, XMMWORD PTR [rdx]
	vmovdqu XMMWORD PTR [rdx], xmm0
	vpxor xmm3, xmm3, XMMWORD PTR [rdx+16]
	vmovdqu XMMWORD PTR [rdx+16], xmm3
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+32]
	vmovdqu XMMWORD PTR [rdx+32], xmm4
	vpxor xmm5, xmm5, XMMWORD PTR [rdx+48]
	vmovdqu XMMWORD PTR [rdx+48], xmm5
	vpxor xmm6, xmm6, XMMWORD PTR [rdx+64]
	vmovdqu XMMWORD PTR [rdx+64], xmm6
	vpxor xmm13, xmm13, XMMWORD PTR [rdx+80]
	vmovdqu XMMWORD PTR [rdx+80], xmm13
	vpxor xmm14, xmm14, XMMWORD PTR [rdx+96]
	vmovdqu XMMWORD PTR [rdx+96], xmm14
	vpxor xmm15, xmm15, XMMWORD PTR [rdx+112]
	vmovdqu XMMWORD PTR [rdx+112], xmm15
	vmovdqu xmm11, XMMWORD PTR [rax]
	vmovdqu xmm12, XMMWORD PTR [r11+128]
	vmovdqa xmm0, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm3, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm4, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm5, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm6, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm13, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm14, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm15, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqu XMMWORD PTR [rax], xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi]
	vpxor xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm1
	vpxor xmm4, xmm4, xmm1
	vpxor xmm5, xmm5, xmm1
	vpxor xmm6, xmm6, xmm1
	vpxor xmm13, xmm13, xmm1
	vpxor xmm14, xmm14, xmm1
	vpxor xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+16]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+32]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+48]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+64]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+80]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+96]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+112]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+128]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+144]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	cmp rsi, 10
	je 284f
	vmovdqu xmm1, XMMWORD PTR [rdi+160]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+176]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	cmp rsi, 12
	je 286f
	vmovdqu xmm1, XMMWORD PTR [rdi+192]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+208]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	jmp 287f
286:
287:
	jmp 285f
284:
285:
	vmovdqu xmm1, XMMWORD PTR [r10]
	vaesenclast xmm0, xmm0, xmm1
	vaesenclast xmm3, xmm3, xmm1
	vaesenclast xmm4, xmm4, xmm1
	vaesenclast xmm5, xmm5, xmm1
	vaesenclast xmm6, xmm6, xmm1
	vaesenclast xmm13, xmm13, xmm1
	vaesenclast xmm14, xmm14, xmm1
	vaesenclast xmm15, xmm15, xmm1
	vpxor xmm0, xmm0, XMMWORD PTR [rdx+128]
	vmovdqu XMMWORD PTR [rdx+128], xmm0
	vpxor xmm3, xmm3, XMMWORD PTR [rdx+144]
	vmovdqu XMMWORD PTR [rdx+144], xmm3
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+160]
	vmovdqu XMMWORD PTR [rdx+160], xmm4
	vpxor xmm5, xmm5, XMMWORD PTR [rdx+176]
	vmovdqu XMMWORD PTR [rdx+176], xmm5
	vpxor xmm6, xmm6, XMMWORD PTR [rdx+192]
	vmovdqu XMMWORD PTR [rdx+192], xmm6
	vpxor xmm13, xmm13, XMMWORD PTR [rdx+208]
	vmovdqu XMMWORD PTR [rdx+208], xmm13
	vpxor xmm14, xmm14, XMMWORD PTR [rdx+224]
	vmovdqu XMMWORD PTR [rdx+224], xmm14
	vpxor xmm15, xmm15, XMMWORD PTR [rdx+240]
	vmovdqu XMMWORD PTR [rdx+240], xmm15
	cmp r9, 32
	jb 288f
290:
	vmovdqu xmm11, XMMWORD PTR [rax]
	vmovdqu xmm12, XMMWORD PTR [r11+128]
	vmovdqa xmm0, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm3, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm4, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm5, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm6, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm13, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm14, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm15, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqu XMMWORD PTR [rax], xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi]
	vpxor xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm1
	vpxor xmm4, xmm4, xmm1
	vpxor xmm5, xmm5, xmm1
	vpxor xmm6, xmm6, xmm1
	vpxor xmm13, xmm13, xmm1
	vpxor xmm14, xmm14, xmm1
	vpxor xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+16]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+16]
	vmovdqu xmm7, XMMWORD PTR [rdx+16]
	vpclmulqdq xmm8, xmm7, xmm12, 0
	vpclmulqdq xmm10, xmm7, xmm12, 17
	vpclmulqdq xmm9, xmm7, xmm12, 1
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+32]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+32]
	vmovdqu xmm7, XMMWORD PTR [rdx+32]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+48]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+48]
	vmovdqu xmm7, XMMWORD PTR [rdx+48]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+64]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+64]
	vmovdqu xmm7, XMMWORD PTR [rdx+64]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+80]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+80]
	vmovdqu xmm7, XMMWORD PTR [rdx+80]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+96]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+96]
	vmovdqu xmm7, XMMWORD PTR [rdx+96]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+112]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+112]
	vmovdqu xmm7, XMMWORD PTR [rdx+112]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+128]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11]
	vmovdqu xmm7, XMMWORD PTR [rdx]
	vpxor xmm7, xmm7, xmm2
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+144]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+144]
	vpclmulqdq xmm11, xmm8, xmm12, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm9, xmm9, xmm8
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm9, xmm12, 16
	vpshufd xmm9, xmm9, 78
	vpxor xmm2, xmm10, xmm9
	vpxor xmm2, xmm2, xmm11
	cmp rsi, 10
	je 291f
	vmovdqu xmm1, XMMWORD PTR [rdi+160]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+176]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	cmp rsi, 12
	je 293f
	vmovdqu xmm1, XMMWORD PTR [rdi+192]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+208]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	jmp 294f
293:
294:
	jmp 292f
291:
292:
	vmovdqu xmm1, XMMWORD PTR [r10]
	vaesenclast xmm0, xmm0, xmm1
	vaesenclast xmm3, xmm3, xmm1
	vaesenclast xmm4, xmm4, xmm1
	vaesenclast xmm5, xmm5, xmm1
	vaesenclast xmm6, xmm6, xmm1
	vaesenclast xmm13, xmm13, xmm1
	vaesenclast xmm14, xmm14, xmm1
	vaesenclast xmm15, xmm15, xmm1
	vpxor xmm0, xmm0, XMMWORD PTR [rdx+256]
	vmovdqu XMMWORD PTR [rdx+256], xmm0
	vpxor xmm3, xmm3, XMMWORD PTR [rdx+272]
	vmovdqu XMMWORD PTR [rdx+272], xmm3
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+288]
	vmovdqu XMMWORD PTR [rdx+288], xmm4
	vpxor xmm5, xmm5, XMMWORD PTR [rdx+304]
	vmovdqu XMMWORD PTR [rdx+304], xmm5
	vpxor xmm6, xmm6, XMMWORD PTR [rdx+320]
	vmovdqu XMMWORD PTR [rdx+320], xmm6
	vpxor xmm13, xmm13, XMMWORD PTR [rdx+336]
	vmovdqu XMMWORD PTR [rdx+336], xmm13
	vpxor xmm14, xmm14, XMMWORD PTR [rdx+352]
	vmovdqu XMMWORD PTR [rdx+352], xmm14
	vpxor xmm15, xmm15, XMMWORD PTR [rdx+368]
	vmovdqu XMMWORD PTR [rdx+368], xmm15
	vmovdqu xmm11, XMMWORD PTR [rax]
	vmovdqu xmm12, XMMWORD PTR [r11+128]
	vmovdqa xmm0, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm3, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm4, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm5, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm6, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm13, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm14, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm15, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqu XMMWORD PTR [rax], xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi]
	vpxor xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm1
	vpxor xmm4, xmm4, xmm1
	vpxor xmm5, xmm5, xmm1
	vpxor xmm6, xmm6, xmm1
	vpxor xmm13, xmm13, xmm1
	vpxor xmm14, xmm14, xmm1
	vpxor xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+16]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+16]
	vmovdqu xmm7, XMMWORD PTR [rdx+144]
	vpclmulqdq xmm8, xmm7, xmm12, 0
	vpclmulqdq xmm10, xmm7, xmm12, 17
	vpclmulqdq xmm9, xmm7, xmm12, 1
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+32]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+32]
	vmovdqu xmm7, XMMWORD PTR [rdx+160]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+48]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+48]
	vmovdqu xmm7, XMMWORD PTR [rdx+176]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+64]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+64]
	vmovdqu xmm7, XMMWORD PTR [rdx+192]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+80]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+80]
	vmovdqu xmm7, XMMWORD PTR [rdx+208]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+96]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+96]
	vmovdqu xmm7, XMMWORD PTR [rdx+224]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+112]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+112]
	vmovdqu xmm7, XMMWORD PTR [rdx+240]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+128]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11]
	vmovdqu xmm7, XMMWORD PTR [rdx+128]
	vpxor xmm7, xmm7, xmm2
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+144]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+144]
	vpclmulqdq xmm11, xmm8, xmm12, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm9, xmm9, xmm8
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm9, xmm12, 16
	vpshufd xmm9, xmm9, 78
	vpxor xmm2, xmm10, xmm9
	vpxor xmm2, xmm2, xmm11
	cmp rsi, 10
	je 295f
	vmovdqu xmm1, XMMWORD PTR [rdi+160]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+176]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	cmp rsi, 12
	je 297f
	vmovdqu xmm1, XMMWORD PTR [rdi+192]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+208]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	jmp 298f
297:
298:
	jmp 296f
295:
296:
	vmovdqu xmm1, XMMWORD PTR [r10]
	vaesenclast xmm0, xmm0, xmm1
	vaesenclast xmm3, xmm3, xmm1
	vaesenclast xmm4, xmm4, xmm1
	vaesenclast xmm5, xmm5, xmm1
	vaesenclast xmm6, xmm6, xmm1
	vaesenclast xmm13, xmm13, xmm1
	vaesenclast xmm14, xmm14, xmm1
	vaesenclast xmm15, xmm15, xmm1
	vpxor xmm0, xmm0, XMMWORD PTR [rdx+384]
	vmovdqu XMMWORD PTR [rdx+384], xmm0
	vpxor xmm3, xmm3, XMMWORD PTR [rdx+400]
	vmovdqu XMMWORD PTR [rdx+400], xmm3
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+416]
	vmovdqu XMMWORD PTR [rdx+416], xmm4
	vpxor xmm5, xmm5, XMMWORD PTR [rdx+432]
	vmovdqu XMMWORD PTR [rdx+432], xmm5
	vpxor xmm6, xmm6, XMMWORD PTR [rdx+448]
	vmovdqu XMMWORD PTR [rdx+448], xmm6
	vpxor xmm13, xmm13, XMMWORD PTR [rdx+464]
	vmovdqu XMMWORD PTR [rdx+464], xmm13
	vpxor xmm14, xmm14, XMMWORD PTR [rdx+480]
	vmovdqu XMMWORD PTR [rdx+480], xmm14
	vpxor xmm15, xmm15, XMMWORD PTR [rdx+496]
	vmovdqu XMMWORD PTR [rdx+496], xmm15
	add rdx, 256
	sub r9, 16
	cmp r9, 32
	jae 290b
	jmp 289f
288:
289:
	vmovdqu xmm12, XMMWORD PTR [r11+16]
	vmovdqu xmm7, XMMWORD PTR [rdx+16]
	vpclmulqdq xmm8, xmm7, xmm12, 0
	vpclmulqdq xmm10, xmm7, xmm12, 17
	vpclmulqdq xmm9, xmm7, xmm12, 1
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+32]
	vmovdqu xmm7, XMMWORD PTR [rdx+32]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+48]
	vmovdqu xmm7, XMMWORD PTR [rdx+48]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+64]
	vmovdqu xmm7, XMMWORD PTR [rdx+64]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+80]
	vmovdqu xmm7, XMMWORD PTR [rdx+80]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+96]
	vmovdqu xmm7, XMMWORD PTR [rdx+96]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+112]
	vmovdqu xmm7, XMMWORD PTR [rdx+112]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11]
	vmovdqu xmm7, XMMWORD PTR [rdx]
	vpxor xmm7, xmm7, xmm2
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+144]
	vpclmulqdq xmm11, xmm8, xmm12, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm9, xmm9, xmm8
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm9, xmm12, 16
	vpshufd xmm9, xmm9, 78
	vpxor xmm2, xmm10, xmm9
	vpxor xmm2, xmm2, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+16]
	vmovdqu xmm7, XMMWORD PTR [rdx+144]
	vpclmulqdq xmm8, xmm7, xmm12, 0
	vpclmulqdq xmm10, xmm7, xmm12, 17
	vpclmulqdq xmm9, xmm7, xmm12, 1
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+32]
	vmovdqu xmm7, XMMWORD PTR [rdx+160]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+48]
	vmovdqu xmm7, XMMWORD PTR [rdx+176]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+64]
	vmovdqu xmm7, XMMWORD PTR [rdx+192]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+80]
	vmovdqu xmm7, XMMWORD PTR [rdx+208]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+96]
	vmovdqu xmm7, XMMWORD PTR [rdx+224]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+112]
	vmovdqu xmm7, XMMWORD PTR [rdx+240]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11]
	vmovdqu xmm7, XMMWORD PTR [rdx+128]
	vpxor xmm7, xmm7, xmm2
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+144]
	vpclmulqdq xmm11, xmm8, xmm12, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm9, xmm9, xmm8
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm9, xmm12, 16
	vpshufd xmm9, xmm9, 78
	vpxor xmm2, xmm10, xmm9
	vpxor xmm2, xmm2, xmm11
	movabs rax, 579005069656919567
	movq xmm0, rax
	movabs rax, 283686952306183
	movq xmm12, rax
	punpcklqdq xmm0, xmm12
	vpshufb xmm2, xmm2, xmm0
	vmovdqu XMMWORD PTR [rcx], xmm2
	mov r12, QWORD PTR [r15+232]
	mov rax, QWORD PTR [r15+240]
	shr rax, 8
	shl rax, 8
	add r12, rax
	mov rbp, QWORD PTR [r15+240]
	and rbp, 255
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 299f
2101:
	mov r14d, 64
	cmp rbx, r14
	jb 2102f
	jmp 2103f
2102:
	mov r14, rbx
2103:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
2104:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 2104b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_aesni}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
	cmp rcx, 8
	jb 2105f
2107:
	vmovdqu ymm1, YMMWORD PTR [rsi]
	vmovdqu ymm0, YMMWORD PTR [r12]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12], ymm1
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vmovdqu ymm0, YMMWORD PTR [r12+32]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12+32], ymm1
	add r12, 64
	add rsi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 2107b
	vzeroupper
	test rcx, rcx
	je 2108f
2110:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 2110b
	jmp 2109f
2108:
2109:
	jmp 2106f
2105:
2111:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 2111b
2106:
	sub rbx, r14
	jne 2101b
	jmp 2100f
299:
2100:
	test rbp, rbp
	je 2112f
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_aesni}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
2114:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2114b
	jmp 2113f
2112:
2113:
	mov r12, QWORD PTR [r15+232]
	mov rax, QWORD PTR [r15+240]
	shr rax, 8
	shl rax, 8
	add r12, rax
	mov rbp, QWORD PTR [r15+240]
	and rbp, 255
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 2115f
2117:
	mov r14d, 64
	cmp rbx, r14
	jb 2118f
	jmp 2119f
2118:
	mov r14, rbx
2119:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 2120f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
2122:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 2122b
	vzeroupper
	test rcx, rcx
	je 2123f
2125:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2125b
	jmp 2124f
2123:
2124:
	jmp 2121f
2120:
2126:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2126b
2121:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_pclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 2117b
	jmp 2116f
2115:
2116:
	test rbp, rbp
	je 2127f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
2129:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2129b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_pclmul}
	jmp 2128f
2127:
2128:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	jmp 264f
263:
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rdx, rcx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 2130f
2132:
	mov r14d, 64
	cmp rbx, r14
	jb 2133f
	jmp 2134f
2133:
	mov r14, rbx
2134:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
2135:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 2135b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_aesni}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
	cmp rcx, 8
	jb 2136f
2138:
	vmovdqu ymm1, YMMWORD PTR [rsi]
	vmovdqu ymm0, YMMWORD PTR [r12]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12], ymm1
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vmovdqu ymm0, YMMWORD PTR [r12+32]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12+32], ymm1
	add r12, 64
	add rsi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 2138b
	vzeroupper
	test rcx, rcx
	je 2139f
2141:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 2141b
	jmp 2140f
2139:
2140:
	jmp 2137f
2136:
2142:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 2142b
2137:
	sub rbx, r14
	jne 2132b
	jmp 2131f
2130:
2131:
	test rbp, rbp
	je 2143f
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_aesni}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
2145:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2145b
	jmp 2144f
2143:
2144:
	mov rax, QWORD PTR [r15+224]
	shr rax, 4
	mov rdx, QWORD PTR [r15+240]
	shr rdx, 4
	add rax, rdx
	cmp rax, 62
	jae 2146f
	mov rdi, r15
	add rdi, 488
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 2148f
	mov r14, rbx
	mov rcx, r14
	cmp rcx, 8
	jb 2150f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
2152:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 2152b
	vzeroupper
	test rcx, rcx
	je 2153f
2155:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2155b
	jmp 2154f
2153:
2154:
	jmp 2151f
2150:
2156:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2156b
2151:
	jmp 2149f
2148:
2149:
	test rbp, rbp
	je 2157f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
2159:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2159b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 2158f
2157:
2158:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 2160f
	mov r14, rbx
	mov rcx, r14
	cmp rcx, 8
	jb 2162f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
2164:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 2164b
	vzeroupper
	test rcx, rcx
	je 2165f
2167:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2167b
	jmp 2166f
2165:
2166:
	jmp 2163f
2162:
2168:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2168b
2163:
	jmp 2161f
2160:
2161:
	test rbp, rbp
	je 2169f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
2171:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2171b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 2170f
2169:
2170:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	mov rcx, rdi
	sub rcx, r15
	shr rcx, 4
	sub rcx, 29
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	jmp 2147f
2146:
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 2172f
2174:
	mov r14d, 64
	cmp rbx, r14
	jb 2175f
	jmp 2176f
2175:
	mov r14, rbx
2176:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 2177f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
2179:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 2179b
	vzeroupper
	test rcx, rcx
	je 2180f
2182:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2182b
	jmp 2181f
2180:
2181:
	jmp 2178f
2177:
2183:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2183b
2178:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_pclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 2174b
	jmp 2173f
2172:
2173:
	test rbp, rbp
	je 2184f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
2186:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2186b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_pclmul}
	jmp 2185f
2184:
2185:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 2187f
2189:
	mov r14d, 64
	cmp rbx, r14
	jb 2190f
	jmp 2191f
2190:
	mov r14, rbx
2191:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 2192f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
2194:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 2194b
	vzeroupper
	test rcx, rcx
	je 2195f
2197:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2197b
	jmp 2196f
2195:
2196:
	jmp 2193f
2192:
2198:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2198b
2193:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_pclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 2189b
	jmp 2188f
2187:
2188:
	test rbp, rbp
	je 2199f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
2201:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2201b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_pclmul}
	jmp 2200f
2199:
2200:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
2147:
264:
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_aesni}
	mov rax, QWORD PTR [r15]
	xor rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+8]
	xor rdx, QWORD PTR [r15+136]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+192], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov r11d, 0
	sub r11, QWORD PTR [r15+192]
	mov r10d, 0
	mov rcx, rbp
	shr rcx, 4
	test rcx, rcx
	je 2202f
	movq xmm0, r11
	punpcklqdq xmm0, xmm0
2204:
	movdqu xmm1, XMMWORD PTR [r12+r10*1]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [r12+r10*1], xmm1
	add r10, 16
	sub rcx, 1
	jne 2204b
	jmp 2203f
2202:
2203:
	cmp r10, rbp
	je 2205f
2207:
	movzx eax, BYTE PTR [r12+r10*1]
	and rax, r11
	mov BYTE PTR [r12+r10*1], al
	add r10, 1
	cmp r10, rbp
	jne 2207b
	jmp 2206f
2205:
2206:
	mov rax, QWORD PTR [r15+192]
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
	jmp 21b
	.p2align 6

vg_aes_gcm_siv_seal_aesni_pclmul_avx:
	mov rax, QWORD PTR [rsp+8]
	or rax, r8
	cmp rax, 128
	jae 20f
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov r10, rsi
	shl r10, 4
	add r10, rdi
	mov rdx, QWORD PTR [r15+208]
	mov ebx, 0
22:
	mov rax, QWORD PTR [rdx+4]
	movq xmm2, rax
	mov eax, DWORD PTR [rdx]
	shl rax, 32
	or rax, rbx
	movq xmm0, rax
	punpcklqdq xmm0, xmm2
	or rax, 1
	movq xmm1, rax
	punpcklqdq xmm1, xmm2
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	cmp rsi, 10
	je 23f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	cmp rsi, 12
	je 25f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	jmp 26f
25:
26:
	jmp 24f
23:
24:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	punpcklqdq xmm0, xmm1
	mov rax, rbx
	shl rax, 3
	add rax, r15
	movdqu XMMWORD PTR [rax+16], xmm0
	add rbx, 2
	mov rax, rsi
	shr rax, 1
	sub rax, 1
	cmp rbx, rax
	jne 22b
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
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
	je 27f
	cmp rsi, 32
	je 29f
	movdqa xmm13, xmm5
	pxor xmm13, xmm6
	pxor xmm13, xmm8
	pxor xmm13, xmm9
	movdqa xmm14, xmm13
	paddd xmm14, xmm14
	movabs rax, 868928702305472013
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqu xmm1, XMMWORD PTR [rdi]
	movdqu XMMWORD PTR [rdx], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm5
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+16], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm6
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+32], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm7
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+48], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm8
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+64], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm9
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+80], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm10
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+96], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm11
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+112], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm12
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+128], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm13
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+144], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm14
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+160], xmm1
	jmp 210f
29:
	movabs rax, 868928702305472013
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	pxor xmm15, xmm15
	movdqu xmm1, XMMWORD PTR [rdi]
	movdqu xmm2, XMMWORD PTR [rdi+16]
	movdqu XMMWORD PTR [rdx], xmm1
	movdqu XMMWORD PTR [rdx+16], xmm2
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm11
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+224], xmm1
210:
	jmp 28f
27:
	movabs rax, 290207319600858629
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqu xmm1, XMMWORD PTR [rdi]
	movdqu xmm2, XMMWORD PTR [rdi+8]
	psrldq xmm2, 8
	movdqu XMMWORD PTR [rdx], xmm1
	movdqu XMMWORD PTR [rdx+16], xmm2
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm12
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+192], xmm1
28:
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	movq xmm7, rax
	movq xmm11, rdx
	punpcklqdq xmm7, xmm11
	movabs rax, 0
	movq xmm1, rax
	movabs rax, -4467570830351532032
	movq xmm12, rax
	punpcklqdq xmm1, xmm12
	movabs rax, 1
	movq xmm13, rax
	movabs rax, -4467570830351532032
	movq xmm12, rax
	punpcklqdq xmm13, xmm12
	movabs rax, -1
	movq xmm14, rax
	punpcklqdq xmm14, xmm14
	movdqa xmm3, xmm7
	psllq xmm3, 1
	movdqa xmm11, xmm7
	psrlq xmm11, 63
	pslldq xmm11, 8
	por xmm3, xmm11
	pshufd xmm11, xmm7, 255
	psrld xmm11, 31
	paddd xmm11, xmm14
	pandn xmm11, xmm13
	pxor xmm3, xmm11
	pxor xmm2, xmm2
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	test rbx, rbx
	je 211f
213:
	movdqu xmm7, XMMWORD PTR [r12]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	add r12, 16
	sub rbx, 1
	jne 213b
	jmp 212f
211:
212:
	mov rsi, r12
	mov rcx, rbp
	and rcx, 15
	test rcx, rcx
	je 214f
	mov rdi, r15
	add rdi, 128
	pxor xmm7, xmm7
	movdqu XMMWORD PTR [rdi], xmm7
	mov r10d, 0
216:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 216b
	movdqu xmm7, XMMWORD PTR [rdi]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	jmp 215f
214:
215:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	test rbx, rbx
	je 217f
	cmp rbx, 4
	jb 219f
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm4, xmm10
	pxor xmm4, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm5, xmm10
	pxor xmm5, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm6, xmm10
	pxor xmm6, xmm8
221:
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqu xmm7, XMMWORD PTR [r12]
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 16
	pxor xmm9, xmm11
	movdqu xmm7, XMMWORD PTR [r12+16]
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm5, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm5, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm5, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm5, 16
	pxor xmm9, xmm11
	movdqu xmm7, XMMWORD PTR [r12+32]
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm4, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm4, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm4, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm4, 16
	pxor xmm9, xmm11
	movdqu xmm7, XMMWORD PTR [r12+48]
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	add r12, 64
	sub rbx, 4
	cmp rbx, 4
	jae 221b
	jmp 220f
219:
220:
	test rbx, rbx
	je 222f
224:
	movdqu xmm7, XMMWORD PTR [r12]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	add r12, 16
	sub rbx, 1
	jne 224b
	jmp 223f
222:
223:
	jmp 218f
217:
218:
	mov rsi, r12
	mov rcx, rbp
	and rcx, 15
	test rcx, rcx
	je 225f
	mov rdi, r15
	add rdi, 128
	pxor xmm7, xmm7
	movdqu XMMWORD PTR [rdi], xmm7
	mov r10d, 0
227:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 227b
	movdqu xmm7, XMMWORD PTR [rdi]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	jmp 226f
225:
226:
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, QWORD PTR [r15+240]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	movq xmm7, rax
	movq xmm11, rdx
	punpcklqdq xmm7, xmm11
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	movq rax, xmm2
	psrldq xmm2, 8
	movq rdx, xmm2
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov r10, rsi
	shl r10, 4
	add r10, rdi
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	cmp rsi, 10
	je 228f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 230f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 231f
230:
231:
	jmp 229f
228:
229:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	movdqu XMMWORD PTR [r15], xmm0
	movdqu xmm0, XMMWORD PTR [r15]
	movabs rax, -9223372036854775808
	movq xmm9, rax
	pslldq xmm9, 8
	por xmm9, xmm0
	mov eax, 1
	movq xmm10, rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov r10, rsi
	shl r10, 4
	add r10, rdi
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 232f
	cmp rbx, 4
	jb 234f
236:
	movdqa xmm0, xmm9
	paddd xmm9, xmm10
	movdqa xmm1, xmm9
	paddd xmm9, xmm10
	movdqa xmm2, xmm9
	paddd xmm9, xmm10
	movdqa xmm3, xmm9
	paddd xmm9, xmm10
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	pxor xmm2, xmm8
	pxor xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	cmp rsi, 10
	je 237f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	cmp rsi, 12
	je 239f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	jmp 240f
239:
240:
	jmp 238f
237:
238:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	aesenclast xmm2, xmm8
	aesenclast xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [r12]
	pxor xmm0, xmm8
	movdqu XMMWORD PTR [r12], xmm0
	movdqu xmm8, XMMWORD PTR [r12+16]
	pxor xmm1, xmm8
	movdqu XMMWORD PTR [r12+16], xmm1
	movdqu xmm8, XMMWORD PTR [r12+32]
	pxor xmm2, xmm8
	movdqu XMMWORD PTR [r12+32], xmm2
	movdqu xmm8, XMMWORD PTR [r12+48]
	pxor xmm3, xmm8
	movdqu XMMWORD PTR [r12+48], xmm3
	add r12, 64
	sub rbx, 4
	cmp rbx, 4
	jae 236b
	jmp 235f
234:
235:
	test rbx, rbx
	je 241f
243:
	movdqa xmm0, xmm9
	paddd xmm9, xmm10
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	cmp rsi, 10
	je 244f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 246f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 247f
246:
247:
	jmp 245f
244:
245:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r12]
	pxor xmm0, xmm8
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	sub rbx, 1
	jne 243b
	jmp 242f
241:
242:
	jmp 233f
232:
233:
	test rbp, rbp
	je 248f
	movdqa xmm0, xmm9
	paddd xmm9, xmm10
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	cmp rsi, 10
	je 250f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 252f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 253f
252:
253:
	jmp 251f
250:
251:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	mov rsi, r15
	add rsi, 128
	movdqu XMMWORD PTR [rsi], xmm0
	mov rdi, r12
	mov rcx, rbp
	mov r10d, 0
254:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 254b
	jmp 249f
248:
249:
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [rcx], rax
	mov rax, QWORD PTR [r15+8]
	mov QWORD PTR [rcx+8], rax
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
21:
	ret
20:
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov ebx, 0
	mov rdi, r15
	add rdi, 488
	mov rbp, QWORD PTR [r15+200]
	shr rbp, 1
	sub rbp, 1
255:
	mov rax, QWORD PTR [r15+208]
	mov ecx, DWORD PTR [rax]
	shl rcx, 32
	or rcx, rbx
	mov rdx, QWORD PTR [rax+4]
	movq xmm0, rcx
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rdi, 16
	add rbx, 1
	cmp rbx, rbp
	jne 255b
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, rbp
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_aesni}
	mov rsi, r15
	add rsi, 488
	mov rdi, r15
	add rdi, 16
	mov rcx, rbp
256:
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+16]
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 32
	add rdi, 16
	sub rcx, 2
	jne 256b
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	bswap rdx
	bswap rax
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+64], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+80], xmm0
	mov rax, QWORD PTR [r15+240]
	cmp rax, 256
	jb 257f
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 259f
261:
	mov r14d, 64
	cmp rbx, r14
	jb 262f
	jmp 263f
262:
	mov r14, rbx
263:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
264:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 264b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_pclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 261b
	jmp 260f
259:
260:
	test rbp, rbp
	je 265f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
267:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 267b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_pclmul}
	jmp 266f
265:
266:
	mov rcx, r15
	add rcx, 80
	mov r8, r15
	add r8, 64
	mov r11, r15
	add r11, 1512
	mov rdx, QWORD PTR [r15+232]
	mov r9, QWORD PTR [r15+240]
	shr r9, 8
	add r9, r9
	add r9, r9
	add r9, r9
	add r9, r9
	movabs rax, 579005069656919567
	movq xmm0, rax
	movabs rax, 283686952306183
	movq xmm12, rax
	punpcklqdq xmm0, xmm12
	movabs rax, 0
	movq xmm1, rax
	movabs rax, -4467570830351532032
	movq xmm12, rax
	punpcklqdq xmm1, xmm12
	movdqu xmm7, XMMWORD PTR [r8]
	pshufb xmm7, xmm0
	movabs rax, 1
	movq xmm13, rax
	movabs rax, -4467570830351532032
	movq xmm12, rax
	punpcklqdq xmm13, xmm12
	movabs rax, -1
	movq xmm14, rax
	punpcklqdq xmm14, xmm14
	movdqa xmm3, xmm7
	psllq xmm3, 1
	movdqa xmm11, xmm7
	psrlq xmm11, 63
	pslldq xmm11, 8
	por xmm3, xmm11
	pshufd xmm11, xmm7, 255
	psrld xmm11, 31
	paddd xmm11, xmm14
	pandn xmm11, xmm13
	pxor xmm3, xmm11
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm4, xmm10
	pxor xmm4, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm5, xmm10
	pxor xmm5, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm6, xmm10
	pxor xmm6, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm12, xmm10
	pxor xmm12, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm4, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm4, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm4, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm4, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm13, xmm10
	pxor xmm13, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm5, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm5, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm5, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm5, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm14, xmm10
	pxor xmm14, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm6, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm6, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm6, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm6, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm15, xmm10
	pxor xmm15, xmm8
	movdqu XMMWORD PTR [r11], xmm15
	movdqu XMMWORD PTR [r11+16], xmm14
	movdqu XMMWORD PTR [r11+32], xmm13
	movdqu XMMWORD PTR [r11+48], xmm12
	movdqu XMMWORD PTR [r11+64], xmm6
	movdqu XMMWORD PTR [r11+80], xmm5
	movdqu XMMWORD PTR [r11+96], xmm4
	movdqu XMMWORD PTR [r11+112], xmm3
	movdqu XMMWORD PTR [r11+144], xmm1
	movdqu xmm2, XMMWORD PTR [rcx]
	pshufb xmm2, xmm0
268:
	vmovdqu xmm12, XMMWORD PTR [r11+16]
	vmovdqu xmm7, XMMWORD PTR [rdx+16]
	vpclmulqdq xmm8, xmm7, xmm12, 0
	vpclmulqdq xmm10, xmm7, xmm12, 17
	vpclmulqdq xmm9, xmm7, xmm12, 1
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+32]
	vmovdqu xmm7, XMMWORD PTR [rdx+32]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+48]
	vmovdqu xmm7, XMMWORD PTR [rdx+48]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+64]
	vmovdqu xmm7, XMMWORD PTR [rdx+64]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+80]
	vmovdqu xmm7, XMMWORD PTR [rdx+80]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+96]
	vmovdqu xmm7, XMMWORD PTR [rdx+96]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+112]
	vmovdqu xmm7, XMMWORD PTR [rdx+112]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11]
	vmovdqu xmm7, XMMWORD PTR [rdx]
	vpxor xmm7, xmm7, xmm2
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+144]
	vpclmulqdq xmm11, xmm8, xmm12, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm9, xmm9, xmm8
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm9, xmm12, 16
	vpshufd xmm9, xmm9, 78
	vpxor xmm2, xmm10, xmm9
	vpxor xmm2, xmm2, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+16]
	vmovdqu xmm7, XMMWORD PTR [rdx+144]
	vpclmulqdq xmm8, xmm7, xmm12, 0
	vpclmulqdq xmm10, xmm7, xmm12, 17
	vpclmulqdq xmm9, xmm7, xmm12, 1
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+32]
	vmovdqu xmm7, XMMWORD PTR [rdx+160]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+48]
	vmovdqu xmm7, XMMWORD PTR [rdx+176]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+64]
	vmovdqu xmm7, XMMWORD PTR [rdx+192]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+80]
	vmovdqu xmm7, XMMWORD PTR [rdx+208]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+96]
	vmovdqu xmm7, XMMWORD PTR [rdx+224]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+112]
	vmovdqu xmm7, XMMWORD PTR [rdx+240]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11]
	vmovdqu xmm7, XMMWORD PTR [rdx+128]
	vpxor xmm7, xmm7, xmm2
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+144]
	vpclmulqdq xmm11, xmm8, xmm12, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm9, xmm9, xmm8
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm9, xmm12, 16
	vpshufd xmm9, xmm9, 78
	vpxor xmm2, xmm10, xmm9
	vpxor xmm2, xmm2, xmm11
	add rdx, 256
	sub r9, 16
	jne 268b
	movabs rax, 579005069656919567
	movq xmm0, rax
	movabs rax, 283686952306183
	movq xmm12, rax
	punpcklqdq xmm0, xmm12
	vpshufb xmm2, xmm2, xmm0
	vmovdqu XMMWORD PTR [rcx], xmm2
	mov r12, QWORD PTR [r15+232]
	mov rax, QWORD PTR [r15+240]
	shr rax, 8
	shl rax, 8
	add r12, rax
	mov rbp, QWORD PTR [r15+240]
	and rbp, 255
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 269f
271:
	mov r14d, 64
	cmp rbx, r14
	jb 272f
	jmp 273f
272:
	mov r14, rbx
273:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
274:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 274b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_pclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 271b
	jmp 270f
269:
270:
	test rbp, rbp
	je 275f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
277:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 277b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_pclmul}
	jmp 276f
275:
276:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	jmp 258f
257:
	mov rax, QWORD PTR [r15+224]
	shr rax, 4
	mov rdx, QWORD PTR [r15+240]
	shr rdx, 4
	add rax, rdx
	cmp rax, 62
	jae 278f
	mov rdi, r15
	add rdi, 488
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 280f
	mov r14, rbx
	mov rcx, r14
282:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 282b
	jmp 281f
280:
281:
	test rbp, rbp
	je 283f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
285:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 285b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 284f
283:
284:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 286f
	mov r14, rbx
	mov rcx, r14
288:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 288b
	jmp 287f
286:
287:
	test rbp, rbp
	je 289f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
291:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 291b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 290f
289:
290:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	mov rcx, rdi
	sub rcx, r15
	shr rcx, 4
	sub rcx, 29
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	jmp 279f
278:
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 292f
294:
	mov r14d, 64
	cmp rbx, r14
	jb 295f
	jmp 296f
295:
	mov r14, rbx
296:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
297:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 297b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_pclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 294b
	jmp 293f
292:
293:
	test rbp, rbp
	je 298f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
2100:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2100b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_pclmul}
	jmp 299f
298:
299:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 2101f
2103:
	mov r14d, 64
	cmp rbx, r14
	jb 2104f
	jmp 2105f
2104:
	mov r14, rbx
2105:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
2106:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2106b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_pclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 2103b
	jmp 2102f
2101:
2102:
	test rbp, rbp
	je 2107f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
2109:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2109b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_pclmul}
	jmp 2108f
2107:
2108:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
279:
258:
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
	mov rcx, r15
	add rcx, 1768
	call {vg_aes_expand_key_scratch_aesni}
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 0
	call {vg_aes_ctr32_aesni}
	mov rax, QWORD PTR [r15+240]
	cmp rax, 256
	jb 2110f
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rax, rcx
	mov QWORD PTR [r15+104], rax
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 96
	mov rcx, r15
	add rcx, 80
	mov r8, r15
	add r8, 64
	mov r11, r15
	add r11, 1768
	mov r12, QWORD PTR [r15+232]
	mov r9, QWORD PTR [r15+240]
	shr r9, 8
	add r9, r9
	add r9, r9
	add r9, r9
	add r9, r9
	mov r10d, 1
	movq xmm11, r10
	movdqu XMMWORD PTR [r11+128], xmm11
	mov r10, rsi
	shl r10, 4
	add r10, rdi
	mov rax, rdx
	mov rdx, r12
2112:
	vmovdqu xmm11, XMMWORD PTR [rax]
	vmovdqu xmm12, XMMWORD PTR [r11+128]
	vmovdqa xmm0, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm3, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm4, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm5, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm6, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm13, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm14, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm15, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqu XMMWORD PTR [rax], xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi]
	vpxor xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm1
	vpxor xmm4, xmm4, xmm1
	vpxor xmm5, xmm5, xmm1
	vpxor xmm6, xmm6, xmm1
	vpxor xmm13, xmm13, xmm1
	vpxor xmm14, xmm14, xmm1
	vpxor xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+16]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+32]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+48]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+64]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+80]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+96]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+112]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+128]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+144]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	cmp rsi, 10
	je 2113f
	vmovdqu xmm1, XMMWORD PTR [rdi+160]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+176]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	cmp rsi, 12
	je 2115f
	vmovdqu xmm1, XMMWORD PTR [rdi+192]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+208]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	jmp 2116f
2115:
2116:
	jmp 2114f
2113:
2114:
	vmovdqu xmm1, XMMWORD PTR [r10]
	vaesenclast xmm0, xmm0, xmm1
	vaesenclast xmm3, xmm3, xmm1
	vaesenclast xmm4, xmm4, xmm1
	vaesenclast xmm5, xmm5, xmm1
	vaesenclast xmm6, xmm6, xmm1
	vaesenclast xmm13, xmm13, xmm1
	vaesenclast xmm14, xmm14, xmm1
	vaesenclast xmm15, xmm15, xmm1
	vpxor xmm0, xmm0, XMMWORD PTR [rdx]
	vmovdqu XMMWORD PTR [rdx], xmm0
	vpxor xmm3, xmm3, XMMWORD PTR [rdx+16]
	vmovdqu XMMWORD PTR [rdx+16], xmm3
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+32]
	vmovdqu XMMWORD PTR [rdx+32], xmm4
	vpxor xmm5, xmm5, XMMWORD PTR [rdx+48]
	vmovdqu XMMWORD PTR [rdx+48], xmm5
	vpxor xmm6, xmm6, XMMWORD PTR [rdx+64]
	vmovdqu XMMWORD PTR [rdx+64], xmm6
	vpxor xmm13, xmm13, XMMWORD PTR [rdx+80]
	vmovdqu XMMWORD PTR [rdx+80], xmm13
	vpxor xmm14, xmm14, XMMWORD PTR [rdx+96]
	vmovdqu XMMWORD PTR [rdx+96], xmm14
	vpxor xmm15, xmm15, XMMWORD PTR [rdx+112]
	vmovdqu XMMWORD PTR [rdx+112], xmm15
	vmovdqu xmm11, XMMWORD PTR [rax]
	vmovdqu xmm12, XMMWORD PTR [r11+128]
	vmovdqa xmm0, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm3, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm4, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm5, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm6, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm13, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm14, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm15, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqu XMMWORD PTR [rax], xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi]
	vpxor xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm1
	vpxor xmm4, xmm4, xmm1
	vpxor xmm5, xmm5, xmm1
	vpxor xmm6, xmm6, xmm1
	vpxor xmm13, xmm13, xmm1
	vpxor xmm14, xmm14, xmm1
	vpxor xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+16]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+32]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+48]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+64]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+80]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+96]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+112]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+128]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+144]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	cmp rsi, 10
	je 2117f
	vmovdqu xmm1, XMMWORD PTR [rdi+160]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+176]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	cmp rsi, 12
	je 2119f
	vmovdqu xmm1, XMMWORD PTR [rdi+192]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+208]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	jmp 2120f
2119:
2120:
	jmp 2118f
2117:
2118:
	vmovdqu xmm1, XMMWORD PTR [r10]
	vaesenclast xmm0, xmm0, xmm1
	vaesenclast xmm3, xmm3, xmm1
	vaesenclast xmm4, xmm4, xmm1
	vaesenclast xmm5, xmm5, xmm1
	vaesenclast xmm6, xmm6, xmm1
	vaesenclast xmm13, xmm13, xmm1
	vaesenclast xmm14, xmm14, xmm1
	vaesenclast xmm15, xmm15, xmm1
	vpxor xmm0, xmm0, XMMWORD PTR [rdx+128]
	vmovdqu XMMWORD PTR [rdx+128], xmm0
	vpxor xmm3, xmm3, XMMWORD PTR [rdx+144]
	vmovdqu XMMWORD PTR [rdx+144], xmm3
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+160]
	vmovdqu XMMWORD PTR [rdx+160], xmm4
	vpxor xmm5, xmm5, XMMWORD PTR [rdx+176]
	vmovdqu XMMWORD PTR [rdx+176], xmm5
	vpxor xmm6, xmm6, XMMWORD PTR [rdx+192]
	vmovdqu XMMWORD PTR [rdx+192], xmm6
	vpxor xmm13, xmm13, XMMWORD PTR [rdx+208]
	vmovdqu XMMWORD PTR [rdx+208], xmm13
	vpxor xmm14, xmm14, XMMWORD PTR [rdx+224]
	vmovdqu XMMWORD PTR [rdx+224], xmm14
	vpxor xmm15, xmm15, XMMWORD PTR [rdx+240]
	vmovdqu XMMWORD PTR [rdx+240], xmm15
	add rdx, 256
	sub r9, 16
	jne 2112b
	mov r12, QWORD PTR [r15+232]
	mov rax, QWORD PTR [r15+240]
	shr rax, 8
	shl rax, 8
	add r12, rax
	mov rbp, QWORD PTR [r15+240]
	and rbp, 255
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 2121f
2123:
	mov r14d, 64
	cmp rbx, r14
	jb 2124f
	jmp 2125f
2124:
	mov r14, rbx
2125:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
2126:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 2126b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_aesni}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
2127:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 2127b
	sub rbx, r14
	jne 2123b
	jmp 2122f
2121:
2122:
	test rbp, rbp
	je 2128f
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_aesni}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
2130:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2130b
	jmp 2129f
2128:
2129:
	jmp 2111f
2110:
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rdx, rcx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 2131f
2133:
	mov r14d, 64
	cmp rbx, r14
	jb 2134f
	jmp 2135f
2134:
	mov r14, rbx
2135:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
2136:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 2136b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_aesni}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
2137:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 2137b
	sub rbx, r14
	jne 2133b
	jmp 2132f
2131:
2132:
	test rbp, rbp
	je 2138f
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_aesni}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
2140:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2140b
	jmp 2139f
2138:
2139:
2111:
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [rcx], rax
	mov rax, QWORD PTR [r15+8]
	mov QWORD PTR [rcx+8], rax
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
	jmp 21b
	.p2align 6

vg_aes_gcm_siv_open_aesni_pclmul_avx:
	mov rax, QWORD PTR [rsp+8]
	or rax, r8
	cmp rax, 128
	jae 20f
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+8], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov r10, rsi
	shl r10, 4
	add r10, rdi
	mov rdx, QWORD PTR [r15+208]
	mov ebx, 0
22:
	mov rax, QWORD PTR [rdx+4]
	movq xmm2, rax
	mov eax, DWORD PTR [rdx]
	shl rax, 32
	or rax, rbx
	movq xmm0, rax
	punpcklqdq xmm0, xmm2
	or rax, 1
	movq xmm1, rax
	punpcklqdq xmm1, xmm2
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	cmp rsi, 10
	je 23f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	cmp rsi, 12
	je 25f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	jmp 26f
25:
26:
	jmp 24f
23:
24:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	punpcklqdq xmm0, xmm1
	mov rax, rbx
	shl rax, 3
	add rax, r15
	movdqu XMMWORD PTR [rax+16], xmm0
	add rbx, 2
	mov rax, rsi
	shr rax, 1
	sub rax, 1
	cmp rbx, rax
	jne 22b
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
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
	je 27f
	cmp rsi, 32
	je 29f
	movdqa xmm13, xmm5
	pxor xmm13, xmm6
	pxor xmm13, xmm8
	pxor xmm13, xmm9
	movdqa xmm14, xmm13
	paddd xmm14, xmm14
	movabs rax, 868928702305472013
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqu xmm1, XMMWORD PTR [rdi]
	movdqu XMMWORD PTR [rdx], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm5
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+16], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm6
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+32], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm7
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+48], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm8
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+64], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm9
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+80], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm10
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+96], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm11
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+112], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm12
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+128], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm13
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+144], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm14
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+160], xmm1
	jmp 210f
29:
	movabs rax, 868928702305472013
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	pxor xmm15, xmm15
	movdqu xmm1, XMMWORD PTR [rdi]
	movdqu xmm2, XMMWORD PTR [rdi+16]
	movdqu XMMWORD PTR [rdx], xmm1
	movdqu XMMWORD PTR [rdx+16], xmm2
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm11
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+224], xmm1
210:
	jmp 28f
27:
	movabs rax, 290207319600858629
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqu xmm1, XMMWORD PTR [rdi]
	movdqu xmm2, XMMWORD PTR [rdi+8]
	psrldq xmm2, 8
	movdqu XMMWORD PTR [rdx], xmm1
	movdqu XMMWORD PTR [rdx+16], xmm2
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm12
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+192], xmm1
28:
	movdqu xmm0, XMMWORD PTR [r15]
	movabs rax, -9223372036854775808
	movq xmm9, rax
	pslldq xmm9, 8
	por xmm9, xmm0
	mov eax, 1
	movq xmm10, rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov r10, rsi
	shl r10, 4
	add r10, rdi
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 211f
	cmp rbx, 4
	jb 213f
215:
	movdqa xmm0, xmm9
	paddd xmm9, xmm10
	movdqa xmm1, xmm9
	paddd xmm9, xmm10
	movdqa xmm2, xmm9
	paddd xmm9, xmm10
	movdqa xmm3, xmm9
	paddd xmm9, xmm10
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	pxor xmm2, xmm8
	pxor xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	cmp rsi, 10
	je 216f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	cmp rsi, 12
	je 218f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	jmp 219f
218:
219:
	jmp 217f
216:
217:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	aesenclast xmm2, xmm8
	aesenclast xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [r12]
	pxor xmm0, xmm8
	movdqu XMMWORD PTR [r12], xmm0
	movdqu xmm8, XMMWORD PTR [r12+16]
	pxor xmm1, xmm8
	movdqu XMMWORD PTR [r12+16], xmm1
	movdqu xmm8, XMMWORD PTR [r12+32]
	pxor xmm2, xmm8
	movdqu XMMWORD PTR [r12+32], xmm2
	movdqu xmm8, XMMWORD PTR [r12+48]
	pxor xmm3, xmm8
	movdqu XMMWORD PTR [r12+48], xmm3
	add r12, 64
	sub rbx, 4
	cmp rbx, 4
	jae 215b
	jmp 214f
213:
214:
	test rbx, rbx
	je 220f
222:
	movdqa xmm0, xmm9
	paddd xmm9, xmm10
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	cmp rsi, 10
	je 223f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 225f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 226f
225:
226:
	jmp 224f
223:
224:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r12]
	pxor xmm0, xmm8
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	sub rbx, 1
	jne 222b
	jmp 221f
220:
221:
	jmp 212f
211:
212:
	test rbp, rbp
	je 227f
	movdqa xmm0, xmm9
	paddd xmm9, xmm10
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	cmp rsi, 10
	je 229f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 231f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 232f
231:
232:
	jmp 230f
229:
230:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	mov rsi, r15
	add rsi, 128
	movdqu XMMWORD PTR [rsi], xmm0
	mov rdi, r12
	mov rcx, rbp
	mov r10d, 0
233:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 233b
	jmp 228f
227:
228:
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	movq xmm7, rax
	movq xmm11, rdx
	punpcklqdq xmm7, xmm11
	movabs rax, 0
	movq xmm1, rax
	movabs rax, -4467570830351532032
	movq xmm12, rax
	punpcklqdq xmm1, xmm12
	movabs rax, 1
	movq xmm13, rax
	movabs rax, -4467570830351532032
	movq xmm12, rax
	punpcklqdq xmm13, xmm12
	movabs rax, -1
	movq xmm14, rax
	punpcklqdq xmm14, xmm14
	movdqa xmm3, xmm7
	psllq xmm3, 1
	movdqa xmm11, xmm7
	psrlq xmm11, 63
	pslldq xmm11, 8
	por xmm3, xmm11
	pshufd xmm11, xmm7, 255
	psrld xmm11, 31
	paddd xmm11, xmm14
	pandn xmm11, xmm13
	pxor xmm3, xmm11
	pxor xmm2, xmm2
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	test rbx, rbx
	je 234f
236:
	movdqu xmm7, XMMWORD PTR [r12]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	add r12, 16
	sub rbx, 1
	jne 236b
	jmp 235f
234:
235:
	mov rsi, r12
	mov rcx, rbp
	and rcx, 15
	test rcx, rcx
	je 237f
	mov rdi, r15
	add rdi, 128
	pxor xmm7, xmm7
	movdqu XMMWORD PTR [rdi], xmm7
	mov r10d, 0
239:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 239b
	movdqu xmm7, XMMWORD PTR [rdi]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	jmp 238f
237:
238:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	test rbx, rbx
	je 240f
	cmp rbx, 4
	jb 242f
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm4, xmm10
	pxor xmm4, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm5, xmm10
	pxor xmm5, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm6, xmm10
	pxor xmm6, xmm8
244:
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqu xmm7, XMMWORD PTR [r12]
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 16
	pxor xmm9, xmm11
	movdqu xmm7, XMMWORD PTR [r12+16]
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm5, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm5, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm5, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm5, 16
	pxor xmm9, xmm11
	movdqu xmm7, XMMWORD PTR [r12+32]
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm4, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm4, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm4, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm4, 16
	pxor xmm9, xmm11
	movdqu xmm7, XMMWORD PTR [r12+48]
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	add r12, 64
	sub rbx, 4
	cmp rbx, 4
	jae 244b
	jmp 243f
242:
243:
	test rbx, rbx
	je 245f
247:
	movdqu xmm7, XMMWORD PTR [r12]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	add r12, 16
	sub rbx, 1
	jne 247b
	jmp 246f
245:
246:
	jmp 241f
240:
241:
	mov rsi, r12
	mov rcx, rbp
	and rcx, 15
	test rcx, rcx
	je 248f
	mov rdi, r15
	add rdi, 128
	pxor xmm7, xmm7
	movdqu XMMWORD PTR [rdi], xmm7
	mov r10d, 0
250:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 250b
	movdqu xmm7, XMMWORD PTR [rdi]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	jmp 249f
248:
249:
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, QWORD PTR [r15+240]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	movq xmm7, rax
	movq xmm11, rdx
	punpcklqdq xmm7, xmm11
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	movq rax, xmm2
	psrldq xmm2, 8
	movq rdx, xmm2
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov r10, rsi
	shl r10, 4
	add r10, rdi
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	cmp rsi, 10
	je 251f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 253f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 254f
253:
254:
	jmp 252f
251:
252:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rax, QWORD PTR [r15]
	xor rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+8]
	xor rdx, QWORD PTR [r15+136]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+192], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov r11d, 0
	sub r11, QWORD PTR [r15+192]
	mov r10d, 0
	mov rcx, rbp
	shr rcx, 4
	test rcx, rcx
	je 255f
	movq xmm0, r11
	punpcklqdq xmm0, xmm0
257:
	movdqu xmm1, XMMWORD PTR [r12+r10*1]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [r12+r10*1], xmm1
	add r10, 16
	sub rcx, 1
	jne 257b
	jmp 256f
255:
256:
	cmp r10, rbp
	je 258f
260:
	movzx eax, BYTE PTR [r12+r10*1]
	and rax, r11
	mov BYTE PTR [r12+r10*1], al
	add r10, 1
	cmp r10, rbp
	jne 260b
	jmp 259f
258:
259:
	mov rax, QWORD PTR [r15+192]
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
21:
	ret
20:
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+8], rax
	mov ebx, 0
	mov rdi, r15
	add rdi, 488
	mov rbp, QWORD PTR [r15+200]
	shr rbp, 1
	sub rbp, 1
261:
	mov rax, QWORD PTR [r15+208]
	mov ecx, DWORD PTR [rax]
	shl rcx, 32
	or rcx, rbx
	mov rdx, QWORD PTR [rax+4]
	movq xmm0, rcx
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rdi, 16
	add rbx, 1
	cmp rbx, rbp
	jne 261b
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, rbp
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_aesni}
	mov rsi, r15
	add rsi, 488
	mov rdi, r15
	add rdi, 16
	mov rcx, rbp
262:
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+16]
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 32
	add rdi, 16
	sub rcx, 2
	jne 262b
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
	mov rcx, r15
	add rcx, 1768
	call {vg_aes_expand_key_scratch_aesni}
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	bswap rdx
	bswap rax
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+64], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+80], xmm0
	mov rax, QWORD PTR [r15+240]
	cmp rax, 256
	jb 263f
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [r15+96], rax
	mov rax, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rax, rcx
	mov QWORD PTR [r15+104], rax
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 265f
267:
	mov r14d, 64
	cmp rbx, r14
	jb 268f
	jmp 269f
268:
	mov r14, rbx
269:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
270:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 270b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_pclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 267b
	jmp 266f
265:
266:
	test rbp, rbp
	je 271f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
273:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 273b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_pclmul}
	jmp 272f
271:
272:
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 96
	mov rcx, r15
	add rcx, 80
	mov r8, r15
	add r8, 64
	mov r11, r15
	add r11, 1768
	mov r12, QWORD PTR [r15+232]
	mov r9, QWORD PTR [r15+240]
	shr r9, 8
	add r9, r9
	add r9, r9
	add r9, r9
	add r9, r9
	movabs rax, 579005069656919567
	movq xmm0, rax
	movabs rax, 283686952306183
	movq xmm12, rax
	punpcklqdq xmm0, xmm12
	movabs rax, 0
	movq xmm1, rax
	movabs rax, -4467570830351532032
	movq xmm12, rax
	punpcklqdq xmm1, xmm12
	movdqu xmm7, XMMWORD PTR [r8]
	pshufb xmm7, xmm0
	movabs rax, 1
	movq xmm13, rax
	movabs rax, -4467570830351532032
	movq xmm12, rax
	punpcklqdq xmm13, xmm12
	movabs rax, -1
	movq xmm14, rax
	punpcklqdq xmm14, xmm14
	movdqa xmm3, xmm7
	psllq xmm3, 1
	movdqa xmm11, xmm7
	psrlq xmm11, 63
	pslldq xmm11, 8
	por xmm3, xmm11
	pshufd xmm11, xmm7, 255
	psrld xmm11, 31
	paddd xmm11, xmm14
	pandn xmm11, xmm13
	pxor xmm3, xmm11
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm4, xmm10
	pxor xmm4, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm5, xmm10
	pxor xmm5, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm6, xmm10
	pxor xmm6, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm12, xmm10
	pxor xmm12, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm4, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm4, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm4, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm4, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm13, xmm10
	pxor xmm13, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm5, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm5, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm5, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm5, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm14, xmm10
	pxor xmm14, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm6, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm6, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm6, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm6
	pclmulqdq xmm11, xmm6, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm15, xmm10
	pxor xmm15, xmm8
	movdqu XMMWORD PTR [r11], xmm15
	movdqu XMMWORD PTR [r11+16], xmm14
	movdqu XMMWORD PTR [r11+32], xmm13
	movdqu XMMWORD PTR [r11+48], xmm12
	movdqu XMMWORD PTR [r11+64], xmm6
	movdqu XMMWORD PTR [r11+80], xmm5
	movdqu XMMWORD PTR [r11+96], xmm4
	movdqu XMMWORD PTR [r11+112], xmm3
	movdqu XMMWORD PTR [r11+144], xmm1
	mov r10d, 1
	movq xmm11, r10
	movdqu XMMWORD PTR [r11+128], xmm11
	movdqu xmm2, XMMWORD PTR [rcx]
	pshufb xmm2, xmm0
	mov r10, rsi
	shl r10, 4
	add r10, rdi
	mov rax, rdx
	mov rdx, r12
	vmovdqu xmm11, XMMWORD PTR [rax]
	vmovdqu xmm12, XMMWORD PTR [r11+128]
	vmovdqa xmm0, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm3, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm4, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm5, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm6, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm13, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm14, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm15, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqu XMMWORD PTR [rax], xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi]
	vpxor xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm1
	vpxor xmm4, xmm4, xmm1
	vpxor xmm5, xmm5, xmm1
	vpxor xmm6, xmm6, xmm1
	vpxor xmm13, xmm13, xmm1
	vpxor xmm14, xmm14, xmm1
	vpxor xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+16]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+32]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+48]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+64]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+80]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+96]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+112]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+128]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+144]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	cmp rsi, 10
	je 274f
	vmovdqu xmm1, XMMWORD PTR [rdi+160]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+176]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	cmp rsi, 12
	je 276f
	vmovdqu xmm1, XMMWORD PTR [rdi+192]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+208]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	jmp 277f
276:
277:
	jmp 275f
274:
275:
	vmovdqu xmm1, XMMWORD PTR [r10]
	vaesenclast xmm0, xmm0, xmm1
	vaesenclast xmm3, xmm3, xmm1
	vaesenclast xmm4, xmm4, xmm1
	vaesenclast xmm5, xmm5, xmm1
	vaesenclast xmm6, xmm6, xmm1
	vaesenclast xmm13, xmm13, xmm1
	vaesenclast xmm14, xmm14, xmm1
	vaesenclast xmm15, xmm15, xmm1
	vpxor xmm0, xmm0, XMMWORD PTR [rdx]
	vmovdqu XMMWORD PTR [rdx], xmm0
	vpxor xmm3, xmm3, XMMWORD PTR [rdx+16]
	vmovdqu XMMWORD PTR [rdx+16], xmm3
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+32]
	vmovdqu XMMWORD PTR [rdx+32], xmm4
	vpxor xmm5, xmm5, XMMWORD PTR [rdx+48]
	vmovdqu XMMWORD PTR [rdx+48], xmm5
	vpxor xmm6, xmm6, XMMWORD PTR [rdx+64]
	vmovdqu XMMWORD PTR [rdx+64], xmm6
	vpxor xmm13, xmm13, XMMWORD PTR [rdx+80]
	vmovdqu XMMWORD PTR [rdx+80], xmm13
	vpxor xmm14, xmm14, XMMWORD PTR [rdx+96]
	vmovdqu XMMWORD PTR [rdx+96], xmm14
	vpxor xmm15, xmm15, XMMWORD PTR [rdx+112]
	vmovdqu XMMWORD PTR [rdx+112], xmm15
	vmovdqu xmm11, XMMWORD PTR [rax]
	vmovdqu xmm12, XMMWORD PTR [r11+128]
	vmovdqa xmm0, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm3, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm4, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm5, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm6, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm13, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm14, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm15, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqu XMMWORD PTR [rax], xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi]
	vpxor xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm1
	vpxor xmm4, xmm4, xmm1
	vpxor xmm5, xmm5, xmm1
	vpxor xmm6, xmm6, xmm1
	vpxor xmm13, xmm13, xmm1
	vpxor xmm14, xmm14, xmm1
	vpxor xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+16]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+32]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+48]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+64]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+80]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+96]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+112]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+128]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+144]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	cmp rsi, 10
	je 278f
	vmovdqu xmm1, XMMWORD PTR [rdi+160]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+176]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	cmp rsi, 12
	je 280f
	vmovdqu xmm1, XMMWORD PTR [rdi+192]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+208]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	jmp 281f
280:
281:
	jmp 279f
278:
279:
	vmovdqu xmm1, XMMWORD PTR [r10]
	vaesenclast xmm0, xmm0, xmm1
	vaesenclast xmm3, xmm3, xmm1
	vaesenclast xmm4, xmm4, xmm1
	vaesenclast xmm5, xmm5, xmm1
	vaesenclast xmm6, xmm6, xmm1
	vaesenclast xmm13, xmm13, xmm1
	vaesenclast xmm14, xmm14, xmm1
	vaesenclast xmm15, xmm15, xmm1
	vpxor xmm0, xmm0, XMMWORD PTR [rdx+128]
	vmovdqu XMMWORD PTR [rdx+128], xmm0
	vpxor xmm3, xmm3, XMMWORD PTR [rdx+144]
	vmovdqu XMMWORD PTR [rdx+144], xmm3
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+160]
	vmovdqu XMMWORD PTR [rdx+160], xmm4
	vpxor xmm5, xmm5, XMMWORD PTR [rdx+176]
	vmovdqu XMMWORD PTR [rdx+176], xmm5
	vpxor xmm6, xmm6, XMMWORD PTR [rdx+192]
	vmovdqu XMMWORD PTR [rdx+192], xmm6
	vpxor xmm13, xmm13, XMMWORD PTR [rdx+208]
	vmovdqu XMMWORD PTR [rdx+208], xmm13
	vpxor xmm14, xmm14, XMMWORD PTR [rdx+224]
	vmovdqu XMMWORD PTR [rdx+224], xmm14
	vpxor xmm15, xmm15, XMMWORD PTR [rdx+240]
	vmovdqu XMMWORD PTR [rdx+240], xmm15
	cmp r9, 32
	jb 282f
284:
	vmovdqu xmm11, XMMWORD PTR [rax]
	vmovdqu xmm12, XMMWORD PTR [r11+128]
	vmovdqa xmm0, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm3, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm4, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm5, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm6, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm13, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm14, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm15, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqu XMMWORD PTR [rax], xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi]
	vpxor xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm1
	vpxor xmm4, xmm4, xmm1
	vpxor xmm5, xmm5, xmm1
	vpxor xmm6, xmm6, xmm1
	vpxor xmm13, xmm13, xmm1
	vpxor xmm14, xmm14, xmm1
	vpxor xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+16]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+16]
	vmovdqu xmm7, XMMWORD PTR [rdx+16]
	vpclmulqdq xmm8, xmm7, xmm12, 0
	vpclmulqdq xmm10, xmm7, xmm12, 17
	vpclmulqdq xmm9, xmm7, xmm12, 1
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+32]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+32]
	vmovdqu xmm7, XMMWORD PTR [rdx+32]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+48]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+48]
	vmovdqu xmm7, XMMWORD PTR [rdx+48]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+64]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+64]
	vmovdqu xmm7, XMMWORD PTR [rdx+64]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+80]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+80]
	vmovdqu xmm7, XMMWORD PTR [rdx+80]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+96]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+96]
	vmovdqu xmm7, XMMWORD PTR [rdx+96]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+112]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+112]
	vmovdqu xmm7, XMMWORD PTR [rdx+112]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+128]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11]
	vmovdqu xmm7, XMMWORD PTR [rdx]
	vpxor xmm7, xmm7, xmm2
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+144]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+144]
	vpclmulqdq xmm11, xmm8, xmm12, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm9, xmm9, xmm8
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm9, xmm12, 16
	vpshufd xmm9, xmm9, 78
	vpxor xmm2, xmm10, xmm9
	vpxor xmm2, xmm2, xmm11
	cmp rsi, 10
	je 285f
	vmovdqu xmm1, XMMWORD PTR [rdi+160]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+176]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	cmp rsi, 12
	je 287f
	vmovdqu xmm1, XMMWORD PTR [rdi+192]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+208]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	jmp 288f
287:
288:
	jmp 286f
285:
286:
	vmovdqu xmm1, XMMWORD PTR [r10]
	vaesenclast xmm0, xmm0, xmm1
	vaesenclast xmm3, xmm3, xmm1
	vaesenclast xmm4, xmm4, xmm1
	vaesenclast xmm5, xmm5, xmm1
	vaesenclast xmm6, xmm6, xmm1
	vaesenclast xmm13, xmm13, xmm1
	vaesenclast xmm14, xmm14, xmm1
	vaesenclast xmm15, xmm15, xmm1
	vpxor xmm0, xmm0, XMMWORD PTR [rdx+256]
	vmovdqu XMMWORD PTR [rdx+256], xmm0
	vpxor xmm3, xmm3, XMMWORD PTR [rdx+272]
	vmovdqu XMMWORD PTR [rdx+272], xmm3
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+288]
	vmovdqu XMMWORD PTR [rdx+288], xmm4
	vpxor xmm5, xmm5, XMMWORD PTR [rdx+304]
	vmovdqu XMMWORD PTR [rdx+304], xmm5
	vpxor xmm6, xmm6, XMMWORD PTR [rdx+320]
	vmovdqu XMMWORD PTR [rdx+320], xmm6
	vpxor xmm13, xmm13, XMMWORD PTR [rdx+336]
	vmovdqu XMMWORD PTR [rdx+336], xmm13
	vpxor xmm14, xmm14, XMMWORD PTR [rdx+352]
	vmovdqu XMMWORD PTR [rdx+352], xmm14
	vpxor xmm15, xmm15, XMMWORD PTR [rdx+368]
	vmovdqu XMMWORD PTR [rdx+368], xmm15
	vmovdqu xmm11, XMMWORD PTR [rax]
	vmovdqu xmm12, XMMWORD PTR [r11+128]
	vmovdqa xmm0, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm3, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm4, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm5, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm6, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm13, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm14, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqa xmm15, xmm11
	vpaddd xmm11, xmm11, xmm12
	vmovdqu XMMWORD PTR [rax], xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi]
	vpxor xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm1
	vpxor xmm4, xmm4, xmm1
	vpxor xmm5, xmm5, xmm1
	vpxor xmm6, xmm6, xmm1
	vpxor xmm13, xmm13, xmm1
	vpxor xmm14, xmm14, xmm1
	vpxor xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+16]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+16]
	vmovdqu xmm7, XMMWORD PTR [rdx+144]
	vpclmulqdq xmm8, xmm7, xmm12, 0
	vpclmulqdq xmm10, xmm7, xmm12, 17
	vpclmulqdq xmm9, xmm7, xmm12, 1
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+32]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+32]
	vmovdqu xmm7, XMMWORD PTR [rdx+160]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+48]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+48]
	vmovdqu xmm7, XMMWORD PTR [rdx+176]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+64]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+64]
	vmovdqu xmm7, XMMWORD PTR [rdx+192]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+80]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+80]
	vmovdqu xmm7, XMMWORD PTR [rdx+208]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+96]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+96]
	vmovdqu xmm7, XMMWORD PTR [rdx+224]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+112]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+112]
	vmovdqu xmm7, XMMWORD PTR [rdx+240]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+128]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11]
	vmovdqu xmm7, XMMWORD PTR [rdx+128]
	vpxor xmm7, xmm7, xmm2
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+144]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+144]
	vpclmulqdq xmm11, xmm8, xmm12, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm9, xmm9, xmm8
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm9, xmm12, 16
	vpshufd xmm9, xmm9, 78
	vpxor xmm2, xmm10, xmm9
	vpxor xmm2, xmm2, xmm11
	cmp rsi, 10
	je 289f
	vmovdqu xmm1, XMMWORD PTR [rdi+160]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+176]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	cmp rsi, 12
	je 291f
	vmovdqu xmm1, XMMWORD PTR [rdi+192]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+208]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	jmp 292f
291:
292:
	jmp 290f
289:
290:
	vmovdqu xmm1, XMMWORD PTR [r10]
	vaesenclast xmm0, xmm0, xmm1
	vaesenclast xmm3, xmm3, xmm1
	vaesenclast xmm4, xmm4, xmm1
	vaesenclast xmm5, xmm5, xmm1
	vaesenclast xmm6, xmm6, xmm1
	vaesenclast xmm13, xmm13, xmm1
	vaesenclast xmm14, xmm14, xmm1
	vaesenclast xmm15, xmm15, xmm1
	vpxor xmm0, xmm0, XMMWORD PTR [rdx+384]
	vmovdqu XMMWORD PTR [rdx+384], xmm0
	vpxor xmm3, xmm3, XMMWORD PTR [rdx+400]
	vmovdqu XMMWORD PTR [rdx+400], xmm3
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+416]
	vmovdqu XMMWORD PTR [rdx+416], xmm4
	vpxor xmm5, xmm5, XMMWORD PTR [rdx+432]
	vmovdqu XMMWORD PTR [rdx+432], xmm5
	vpxor xmm6, xmm6, XMMWORD PTR [rdx+448]
	vmovdqu XMMWORD PTR [rdx+448], xmm6
	vpxor xmm13, xmm13, XMMWORD PTR [rdx+464]
	vmovdqu XMMWORD PTR [rdx+464], xmm13
	vpxor xmm14, xmm14, XMMWORD PTR [rdx+480]
	vmovdqu XMMWORD PTR [rdx+480], xmm14
	vpxor xmm15, xmm15, XMMWORD PTR [rdx+496]
	vmovdqu XMMWORD PTR [rdx+496], xmm15
	add rdx, 256
	sub r9, 16
	cmp r9, 32
	jae 284b
	jmp 283f
282:
283:
	vmovdqu xmm12, XMMWORD PTR [r11+16]
	vmovdqu xmm7, XMMWORD PTR [rdx+16]
	vpclmulqdq xmm8, xmm7, xmm12, 0
	vpclmulqdq xmm10, xmm7, xmm12, 17
	vpclmulqdq xmm9, xmm7, xmm12, 1
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+32]
	vmovdqu xmm7, XMMWORD PTR [rdx+32]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+48]
	vmovdqu xmm7, XMMWORD PTR [rdx+48]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+64]
	vmovdqu xmm7, XMMWORD PTR [rdx+64]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+80]
	vmovdqu xmm7, XMMWORD PTR [rdx+80]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+96]
	vmovdqu xmm7, XMMWORD PTR [rdx+96]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+112]
	vmovdqu xmm7, XMMWORD PTR [rdx+112]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11]
	vmovdqu xmm7, XMMWORD PTR [rdx]
	vpxor xmm7, xmm7, xmm2
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+144]
	vpclmulqdq xmm11, xmm8, xmm12, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm9, xmm9, xmm8
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm9, xmm12, 16
	vpshufd xmm9, xmm9, 78
	vpxor xmm2, xmm10, xmm9
	vpxor xmm2, xmm2, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+16]
	vmovdqu xmm7, XMMWORD PTR [rdx+144]
	vpclmulqdq xmm8, xmm7, xmm12, 0
	vpclmulqdq xmm10, xmm7, xmm12, 17
	vpclmulqdq xmm9, xmm7, xmm12, 1
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+32]
	vmovdqu xmm7, XMMWORD PTR [rdx+160]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+48]
	vmovdqu xmm7, XMMWORD PTR [rdx+176]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+64]
	vmovdqu xmm7, XMMWORD PTR [rdx+192]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+80]
	vmovdqu xmm7, XMMWORD PTR [rdx+208]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+96]
	vmovdqu xmm7, XMMWORD PTR [rdx+224]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+112]
	vmovdqu xmm7, XMMWORD PTR [rdx+240]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11]
	vmovdqu xmm7, XMMWORD PTR [rdx+128]
	vpxor xmm7, xmm7, xmm2
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+144]
	vpclmulqdq xmm11, xmm8, xmm12, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm9, xmm9, xmm8
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm9, xmm12, 16
	vpshufd xmm9, xmm9, 78
	vpxor xmm2, xmm10, xmm9
	vpxor xmm2, xmm2, xmm11
	movabs rax, 579005069656919567
	movq xmm0, rax
	movabs rax, 283686952306183
	movq xmm12, rax
	punpcklqdq xmm0, xmm12
	vpshufb xmm2, xmm2, xmm0
	vmovdqu XMMWORD PTR [rcx], xmm2
	mov r12, QWORD PTR [r15+232]
	mov rax, QWORD PTR [r15+240]
	shr rax, 8
	shl rax, 8
	add r12, rax
	mov rbp, QWORD PTR [r15+240]
	and rbp, 255
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 293f
295:
	mov r14d, 64
	cmp rbx, r14
	jb 296f
	jmp 297f
296:
	mov r14, rbx
297:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
298:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 298b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_aesni}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
299:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 299b
	sub rbx, r14
	jne 295b
	jmp 294f
293:
294:
	test rbp, rbp
	je 2100f
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_aesni}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
2102:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2102b
	jmp 2101f
2100:
2101:
	mov r12, QWORD PTR [r15+232]
	mov rax, QWORD PTR [r15+240]
	shr rax, 8
	shl rax, 8
	add r12, rax
	mov rbp, QWORD PTR [r15+240]
	and rbp, 255
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 2103f
2105:
	mov r14d, 64
	cmp rbx, r14
	jb 2106f
	jmp 2107f
2106:
	mov r14, rbx
2107:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
2108:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2108b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_pclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 2105b
	jmp 2104f
2103:
2104:
	test rbp, rbp
	je 2109f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
2111:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2111b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_pclmul}
	jmp 2110f
2109:
2110:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	jmp 264f
263:
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rdx, rcx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 2112f
2114:
	mov r14d, 64
	cmp rbx, r14
	jb 2115f
	jmp 2116f
2115:
	mov r14, rbx
2116:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
2117:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 2117b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_aesni}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
2118:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 2118b
	sub rbx, r14
	jne 2114b
	jmp 2113f
2112:
2113:
	test rbp, rbp
	je 2119f
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_aesni}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
2121:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2121b
	jmp 2120f
2119:
2120:
	mov rax, QWORD PTR [r15+224]
	shr rax, 4
	mov rdx, QWORD PTR [r15+240]
	shr rdx, 4
	add rax, rdx
	cmp rax, 62
	jae 2122f
	mov rdi, r15
	add rdi, 488
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 2124f
	mov r14, rbx
	mov rcx, r14
2126:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2126b
	jmp 2125f
2124:
2125:
	test rbp, rbp
	je 2127f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
2129:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2129b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 2128f
2127:
2128:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 2130f
	mov r14, rbx
	mov rcx, r14
2132:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2132b
	jmp 2131f
2130:
2131:
	test rbp, rbp
	je 2133f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
2135:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2135b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 2134f
2133:
2134:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	mov rcx, rdi
	sub rcx, r15
	shr rcx, 4
	sub rcx, 29
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	jmp 2123f
2122:
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 2136f
2138:
	mov r14d, 64
	cmp rbx, r14
	jb 2139f
	jmp 2140f
2139:
	mov r14, rbx
2140:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
2141:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2141b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_pclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 2138b
	jmp 2137f
2136:
2137:
	test rbp, rbp
	je 2142f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
2144:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2144b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_pclmul}
	jmp 2143f
2142:
2143:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 2145f
2147:
	mov r14d, 64
	cmp rbx, r14
	jb 2148f
	jmp 2149f
2148:
	mov r14, rbx
2149:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
2150:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2150b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_pclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 2147b
	jmp 2146f
2145:
2146:
	test rbp, rbp
	je 2151f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
2153:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2153b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_pclmul}
	jmp 2152f
2151:
2152:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
2123:
264:
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_aesni}
	mov rax, QWORD PTR [r15]
	xor rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+8]
	xor rdx, QWORD PTR [r15+136]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+192], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov r11d, 0
	sub r11, QWORD PTR [r15+192]
	mov r10d, 0
	mov rcx, rbp
	shr rcx, 4
	test rcx, rcx
	je 2154f
	movq xmm0, r11
	punpcklqdq xmm0, xmm0
2156:
	movdqu xmm1, XMMWORD PTR [r12+r10*1]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [r12+r10*1], xmm1
	add r10, 16
	sub rcx, 1
	jne 2156b
	jmp 2155f
2154:
2155:
	cmp r10, rbp
	je 2157f
2159:
	movzx eax, BYTE PTR [r12+r10*1]
	and rax, r11
	mov BYTE PTR [r12+r10*1], al
	add r10, 1
	cmp r10, rbp
	jne 2159b
	jmp 2158f
2157:
2158:
	mov rax, QWORD PTR [r15+192]
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
	jmp 21b
	.p2align 6

vg_aes_gcm_siv_seal_aesni_pclmul:
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov r10, rsi
	shl r10, 4
	add r10, rdi
	mov rdx, QWORD PTR [r15+208]
	mov ebx, 0
20:
	mov rax, QWORD PTR [rdx+4]
	movq xmm2, rax
	mov eax, DWORD PTR [rdx]
	shl rax, 32
	or rax, rbx
	movq xmm0, rax
	punpcklqdq xmm0, xmm2
	or rax, 1
	movq xmm1, rax
	punpcklqdq xmm1, xmm2
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	cmp rsi, 10
	je 21f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	cmp rsi, 12
	je 23f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	jmp 24f
23:
24:
	jmp 22f
21:
22:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	punpcklqdq xmm0, xmm1
	mov rax, rbx
	shl rax, 3
	add rax, r15
	movdqu XMMWORD PTR [rax+16], xmm0
	add rbx, 2
	mov rax, rsi
	shr rax, 1
	sub rax, 1
	cmp rbx, rax
	jne 20b
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
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
	je 25f
	cmp rsi, 32
	je 27f
	movdqa xmm13, xmm5
	pxor xmm13, xmm6
	pxor xmm13, xmm8
	pxor xmm13, xmm9
	movdqa xmm14, xmm13
	paddd xmm14, xmm14
	movabs rax, 868928702305472013
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqu xmm1, XMMWORD PTR [rdi]
	movdqu XMMWORD PTR [rdx], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm5
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+16], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm6
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+32], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm7
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+48], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm8
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+64], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm9
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+80], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm10
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+96], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm11
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+112], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm12
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+128], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm13
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+144], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm14
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+160], xmm1
	jmp 28f
27:
	movabs rax, 868928702305472013
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	pxor xmm15, xmm15
	movdqu xmm1, XMMWORD PTR [rdi]
	movdqu xmm2, XMMWORD PTR [rdi+16]
	movdqu XMMWORD PTR [rdx], xmm1
	movdqu XMMWORD PTR [rdx+16], xmm2
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm11
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+224], xmm1
28:
	jmp 26f
25:
	movabs rax, 290207319600858629
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqu xmm1, XMMWORD PTR [rdi]
	movdqu xmm2, XMMWORD PTR [rdi+8]
	psrldq xmm2, 8
	movdqu XMMWORD PTR [rdx], xmm1
	movdqu XMMWORD PTR [rdx+16], xmm2
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm12
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+192], xmm1
26:
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	movq xmm7, rax
	movq xmm11, rdx
	punpcklqdq xmm7, xmm11
	movabs rax, 0
	movq xmm1, rax
	movabs rax, -4467570830351532032
	movq xmm12, rax
	punpcklqdq xmm1, xmm12
	movabs rax, 1
	movq xmm13, rax
	movabs rax, -4467570830351532032
	movq xmm12, rax
	punpcklqdq xmm13, xmm12
	movabs rax, -1
	movq xmm14, rax
	punpcklqdq xmm14, xmm14
	movdqa xmm3, xmm7
	psllq xmm3, 1
	movdqa xmm11, xmm7
	psrlq xmm11, 63
	pslldq xmm11, 8
	por xmm3, xmm11
	pshufd xmm11, xmm7, 255
	psrld xmm11, 31
	paddd xmm11, xmm14
	pandn xmm11, xmm13
	pxor xmm3, xmm11
	pxor xmm2, xmm2
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	test rbx, rbx
	je 29f
211:
	movdqu xmm7, XMMWORD PTR [r12]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	add r12, 16
	sub rbx, 1
	jne 211b
	jmp 210f
29:
210:
	mov rsi, r12
	mov rcx, rbp
	and rcx, 15
	test rcx, rcx
	je 212f
	mov rdi, r15
	add rdi, 128
	pxor xmm7, xmm7
	movdqu XMMWORD PTR [rdi], xmm7
	mov r10d, 0
214:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 214b
	movdqu xmm7, XMMWORD PTR [rdi]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	jmp 213f
212:
213:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	test rbx, rbx
	je 215f
	cmp rbx, 4
	jb 217f
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm4, xmm10
	pxor xmm4, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm5, xmm10
	pxor xmm5, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm6, xmm10
	pxor xmm6, xmm8
219:
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqu xmm7, XMMWORD PTR [r12]
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 16
	pxor xmm9, xmm11
	movdqu xmm7, XMMWORD PTR [r12+16]
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm5, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm5, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm5, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm5, 16
	pxor xmm9, xmm11
	movdqu xmm7, XMMWORD PTR [r12+32]
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm4, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm4, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm4, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm4, 16
	pxor xmm9, xmm11
	movdqu xmm7, XMMWORD PTR [r12+48]
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	add r12, 64
	sub rbx, 4
	cmp rbx, 4
	jae 219b
	jmp 218f
217:
218:
	test rbx, rbx
	je 220f
222:
	movdqu xmm7, XMMWORD PTR [r12]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	add r12, 16
	sub rbx, 1
	jne 222b
	jmp 221f
220:
221:
	jmp 216f
215:
216:
	mov rsi, r12
	mov rcx, rbp
	and rcx, 15
	test rcx, rcx
	je 223f
	mov rdi, r15
	add rdi, 128
	pxor xmm7, xmm7
	movdqu XMMWORD PTR [rdi], xmm7
	mov r10d, 0
225:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 225b
	movdqu xmm7, XMMWORD PTR [rdi]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	jmp 224f
223:
224:
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, QWORD PTR [r15+240]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	movq xmm7, rax
	movq xmm11, rdx
	punpcklqdq xmm7, xmm11
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	movq rax, xmm2
	psrldq xmm2, 8
	movq rdx, xmm2
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov r10, rsi
	shl r10, 4
	add r10, rdi
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	cmp rsi, 10
	je 226f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 228f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 229f
228:
229:
	jmp 227f
226:
227:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	movdqu XMMWORD PTR [r15], xmm0
	movdqu xmm0, XMMWORD PTR [r15]
	movabs rax, -9223372036854775808
	movq xmm9, rax
	pslldq xmm9, 8
	por xmm9, xmm0
	mov eax, 1
	movq xmm10, rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov r10, rsi
	shl r10, 4
	add r10, rdi
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 230f
	cmp rbx, 4
	jb 232f
234:
	movdqa xmm0, xmm9
	paddd xmm9, xmm10
	movdqa xmm1, xmm9
	paddd xmm9, xmm10
	movdqa xmm2, xmm9
	paddd xmm9, xmm10
	movdqa xmm3, xmm9
	paddd xmm9, xmm10
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	pxor xmm2, xmm8
	pxor xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	cmp rsi, 10
	je 235f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	cmp rsi, 12
	je 237f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	jmp 238f
237:
238:
	jmp 236f
235:
236:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	aesenclast xmm2, xmm8
	aesenclast xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [r12]
	pxor xmm0, xmm8
	movdqu XMMWORD PTR [r12], xmm0
	movdqu xmm8, XMMWORD PTR [r12+16]
	pxor xmm1, xmm8
	movdqu XMMWORD PTR [r12+16], xmm1
	movdqu xmm8, XMMWORD PTR [r12+32]
	pxor xmm2, xmm8
	movdqu XMMWORD PTR [r12+32], xmm2
	movdqu xmm8, XMMWORD PTR [r12+48]
	pxor xmm3, xmm8
	movdqu XMMWORD PTR [r12+48], xmm3
	add r12, 64
	sub rbx, 4
	cmp rbx, 4
	jae 234b
	jmp 233f
232:
233:
	test rbx, rbx
	je 239f
241:
	movdqa xmm0, xmm9
	paddd xmm9, xmm10
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	cmp rsi, 10
	je 242f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 244f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 245f
244:
245:
	jmp 243f
242:
243:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r12]
	pxor xmm0, xmm8
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	sub rbx, 1
	jne 241b
	jmp 240f
239:
240:
	jmp 231f
230:
231:
	test rbp, rbp
	je 246f
	movdqa xmm0, xmm9
	paddd xmm9, xmm10
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	cmp rsi, 10
	je 248f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 250f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 251f
250:
251:
	jmp 249f
248:
249:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	mov rsi, r15
	add rsi, 128
	movdqu XMMWORD PTR [rsi], xmm0
	mov rdi, r12
	mov rcx, rbp
	mov r10d, 0
252:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 252b
	jmp 247f
246:
247:
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [rcx], rax
	mov rax, QWORD PTR [r15+8]
	mov QWORD PTR [rcx+8], rax
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
	ret
	.p2align 6

vg_aes_gcm_siv_open_aesni_pclmul:
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+8], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov r10, rsi
	shl r10, 4
	add r10, rdi
	mov rdx, QWORD PTR [r15+208]
	mov ebx, 0
20:
	mov rax, QWORD PTR [rdx+4]
	movq xmm2, rax
	mov eax, DWORD PTR [rdx]
	shl rax, 32
	or rax, rbx
	movq xmm0, rax
	punpcklqdq xmm0, xmm2
	or rax, 1
	movq xmm1, rax
	punpcklqdq xmm1, xmm2
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	cmp rsi, 10
	je 21f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	cmp rsi, 12
	je 23f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	jmp 24f
23:
24:
	jmp 22f
21:
22:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	punpcklqdq xmm0, xmm1
	mov rax, rbx
	shl rax, 3
	add rax, r15
	movdqu XMMWORD PTR [rax+16], xmm0
	add rbx, 2
	mov rax, rsi
	shr rax, 1
	sub rax, 1
	cmp rbx, rax
	jne 20b
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
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
	je 25f
	cmp rsi, 32
	je 27f
	movdqa xmm13, xmm5
	pxor xmm13, xmm6
	pxor xmm13, xmm8
	pxor xmm13, xmm9
	movdqa xmm14, xmm13
	paddd xmm14, xmm14
	movabs rax, 868928702305472013
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqu xmm1, XMMWORD PTR [rdi]
	movdqu XMMWORD PTR [rdx], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm5
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+16], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm6
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+32], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm7
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+48], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm8
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+64], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm9
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+80], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm10
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+96], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm11
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+112], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm12
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+128], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm13
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+144], xmm1
	movdqa xmm3, xmm1
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm14
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+160], xmm1
	jmp 28f
27:
	movabs rax, 868928702305472013
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	pxor xmm15, xmm15
	movdqu xmm1, XMMWORD PTR [rdi]
	movdqu xmm2, XMMWORD PTR [rdi+16]
	movdqu XMMWORD PTR [rdx], xmm1
	movdqu XMMWORD PTR [rdx+16], xmm2
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm11
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+224], xmm1
28:
	jmp 26f
25:
	movabs rax, 290207319600858629
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqu xmm1, XMMWORD PTR [rdi]
	movdqu xmm2, XMMWORD PTR [rdi+8]
	psrldq xmm2, 8
	movdqu XMMWORD PTR [rdx], xmm1
	movdqu XMMWORD PTR [rdx+16], xmm2
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
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
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
	aesenclast xmm3, xmm12
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+192], xmm1
26:
	movdqu xmm0, XMMWORD PTR [r15]
	movabs rax, -9223372036854775808
	movq xmm9, rax
	pslldq xmm9, 8
	por xmm9, xmm0
	mov eax, 1
	movq xmm10, rax
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov r10, rsi
	shl r10, 4
	add r10, rdi
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 29f
	cmp rbx, 4
	jb 211f
213:
	movdqa xmm0, xmm9
	paddd xmm9, xmm10
	movdqa xmm1, xmm9
	paddd xmm9, xmm10
	movdqa xmm2, xmm9
	paddd xmm9, xmm10
	movdqa xmm3, xmm9
	paddd xmm9, xmm10
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	pxor xmm2, xmm8
	pxor xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	cmp rsi, 10
	je 214f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	cmp rsi, 12
	je 216f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	jmp 217f
216:
217:
	jmp 215f
214:
215:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	aesenclast xmm2, xmm8
	aesenclast xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [r12]
	pxor xmm0, xmm8
	movdqu XMMWORD PTR [r12], xmm0
	movdqu xmm8, XMMWORD PTR [r12+16]
	pxor xmm1, xmm8
	movdqu XMMWORD PTR [r12+16], xmm1
	movdqu xmm8, XMMWORD PTR [r12+32]
	pxor xmm2, xmm8
	movdqu XMMWORD PTR [r12+32], xmm2
	movdqu xmm8, XMMWORD PTR [r12+48]
	pxor xmm3, xmm8
	movdqu XMMWORD PTR [r12+48], xmm3
	add r12, 64
	sub rbx, 4
	cmp rbx, 4
	jae 213b
	jmp 212f
211:
212:
	test rbx, rbx
	je 218f
220:
	movdqa xmm0, xmm9
	paddd xmm9, xmm10
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	cmp rsi, 10
	je 221f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 223f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 224f
223:
224:
	jmp 222f
221:
222:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r12]
	pxor xmm0, xmm8
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	sub rbx, 1
	jne 220b
	jmp 219f
218:
219:
	jmp 210f
29:
210:
	test rbp, rbp
	je 225f
	movdqa xmm0, xmm9
	paddd xmm9, xmm10
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	cmp rsi, 10
	je 227f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 229f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 230f
229:
230:
	jmp 228f
227:
228:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	mov rsi, r15
	add rsi, 128
	movdqu XMMWORD PTR [rsi], xmm0
	mov rdi, r12
	mov rcx, rbp
	mov r10d, 0
231:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 231b
	jmp 226f
225:
226:
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	movq xmm7, rax
	movq xmm11, rdx
	punpcklqdq xmm7, xmm11
	movabs rax, 0
	movq xmm1, rax
	movabs rax, -4467570830351532032
	movq xmm12, rax
	punpcklqdq xmm1, xmm12
	movabs rax, 1
	movq xmm13, rax
	movabs rax, -4467570830351532032
	movq xmm12, rax
	punpcklqdq xmm13, xmm12
	movabs rax, -1
	movq xmm14, rax
	punpcklqdq xmm14, xmm14
	movdqa xmm3, xmm7
	psllq xmm3, 1
	movdqa xmm11, xmm7
	psrlq xmm11, 63
	pslldq xmm11, 8
	por xmm3, xmm11
	pshufd xmm11, xmm7, 255
	psrld xmm11, 31
	paddd xmm11, xmm14
	pandn xmm11, xmm13
	pxor xmm3, xmm11
	pxor xmm2, xmm2
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	test rbx, rbx
	je 232f
234:
	movdqu xmm7, XMMWORD PTR [r12]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	add r12, 16
	sub rbx, 1
	jne 234b
	jmp 233f
232:
233:
	mov rsi, r12
	mov rcx, rbp
	and rcx, 15
	test rcx, rcx
	je 235f
	mov rdi, r15
	add rdi, 128
	pxor xmm7, xmm7
	movdqu XMMWORD PTR [rdi], xmm7
	mov r10d, 0
237:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 237b
	movdqu xmm7, XMMWORD PTR [rdi]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	jmp 236f
235:
236:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	test rbx, rbx
	je 238f
	cmp rbx, 4
	jb 240f
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm4, xmm10
	pxor xmm4, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm5, xmm10
	pxor xmm5, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm6, xmm10
	pxor xmm6, xmm8
242:
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqu xmm7, XMMWORD PTR [r12]
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 16
	pxor xmm9, xmm11
	movdqu xmm7, XMMWORD PTR [r12+16]
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm5, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm5, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm5, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm5, 16
	pxor xmm9, xmm11
	movdqu xmm7, XMMWORD PTR [r12+32]
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm4, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm4, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm4, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm4, 16
	pxor xmm9, xmm11
	movdqu xmm7, XMMWORD PTR [r12+48]
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	add r12, 64
	sub rbx, 4
	cmp rbx, 4
	jae 242b
	jmp 241f
240:
241:
	test rbx, rbx
	je 243f
245:
	movdqu xmm7, XMMWORD PTR [r12]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	add r12, 16
	sub rbx, 1
	jne 245b
	jmp 244f
243:
244:
	jmp 239f
238:
239:
	mov rsi, r12
	mov rcx, rbp
	and rcx, 15
	test rcx, rcx
	je 246f
	mov rdi, r15
	add rdi, 128
	pxor xmm7, xmm7
	movdqu XMMWORD PTR [rdi], xmm7
	mov r10d, 0
248:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 248b
	movdqu xmm7, XMMWORD PTR [rdi]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	jmp 247f
246:
247:
	mov rax, QWORD PTR [r15+224]
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, QWORD PTR [r15+240]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	movq xmm7, rax
	movq xmm11, rdx
	punpcklqdq xmm7, xmm11
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	movq rax, xmm2
	psrldq xmm2, 8
	movq rdx, xmm2
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov r10, rsi
	shl r10, 4
	add r10, rdi
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	cmp rsi, 10
	je 249f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 251f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 252f
251:
252:
	jmp 250f
249:
250:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rax, QWORD PTR [r15]
	xor rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+8]
	xor rdx, QWORD PTR [r15+136]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+192], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov r11d, 0
	sub r11, QWORD PTR [r15+192]
	mov r10d, 0
	mov rcx, rbp
	shr rcx, 4
	test rcx, rcx
	je 253f
	movq xmm0, r11
	punpcklqdq xmm0, xmm0
255:
	movdqu xmm1, XMMWORD PTR [r12+r10*1]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [r12+r10*1], xmm1
	add r10, 16
	sub rcx, 1
	jne 255b
	jmp 254f
253:
254:
	cmp r10, rbp
	je 256f
258:
	movzx eax, BYTE PTR [r12+r10*1]
	and rax, r11
	mov BYTE PTR [r12+r10*1], al
	add r10, 1
	cmp r10, rbp
	jne 258b
	jmp 257f
256:
257:
	mov rax, QWORD PTR [r15+192]
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
	ret
	.p2align 6

vg_aes_gcm_siv_seal_aesni_avx2:
	mov rax, QWORD PTR [rsp+8]
	or rax, r8
	cmp rax, 128
	jae 20f
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov ebx, 0
	mov rdi, r15
	add rdi, 488
	mov rbp, QWORD PTR [r15+200]
	shr rbp, 1
	sub rbp, 1
22:
	mov rax, QWORD PTR [r15+208]
	mov ecx, DWORD PTR [rax]
	shl rcx, 32
	or rcx, rbx
	mov rdx, QWORD PTR [rax+4]
	movq xmm0, rcx
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rdi, 16
	add rbx, 1
	cmp rbx, rbp
	jne 22b
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, rbp
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_aesni}
	mov rsi, r15
	add rsi, 488
	mov rdi, r15
	add rdi, 16
	mov rcx, rbp
23:
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+16]
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 32
	add rdi, 16
	sub rcx, 2
	jne 23b
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	bswap rdx
	bswap rax
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+64], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+80], xmm0
	mov rax, QWORD PTR [r15+224]
	shr rax, 4
	mov rdx, QWORD PTR [r15+240]
	shr rdx, 4
	add rax, rdx
	cmp rax, 62
	jae 24f
	mov rdi, r15
	add rdi, 488
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 26f
	mov r14, rbx
	mov rcx, r14
28:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 28b
	jmp 27f
26:
27:
	test rbp, rbp
	je 29f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
211:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 211b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 210f
29:
210:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 212f
	mov r14, rbx
	mov rcx, r14
214:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 214b
	jmp 213f
212:
213:
	test rbp, rbp
	je 215f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
217:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 217b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 216f
215:
216:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	mov rcx, rdi
	sub rcx, r15
	shr rcx, 4
	sub rcx, 29
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	call {vg_ghash}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	jmp 25f
24:
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 218f
220:
	mov r14d, 64
	cmp rbx, r14
	jb 221f
	jmp 222f
221:
	mov r14, rbx
222:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
223:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 223b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 220b
	jmp 219f
218:
219:
	test rbp, rbp
	je 224f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
226:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 226b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash}
	jmp 225f
224:
225:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 227f
229:
	mov r14d, 64
	cmp rbx, r14
	jb 230f
	jmp 231f
230:
	mov r14, rbx
231:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
232:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 232b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 229b
	jmp 228f
227:
228:
	test rbp, rbp
	je 233f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
235:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 235b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash}
	jmp 234f
233:
234:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
25:
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
	mov rcx, r15
	add rcx, 1768
	call {vg_aes_expand_key_scratch_aesni}
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 0
	call {vg_aes_ctr32_aesni}
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rdx, rcx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 236f
238:
	mov r14d, 64
	cmp rbx, r14
	jb 239f
	jmp 240f
239:
	mov r14, rbx
240:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
241:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 241b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_aesni}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
242:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 242b
	sub rbx, r14
	jne 238b
	jmp 237f
236:
237:
	test rbp, rbp
	je 243f
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_aesni}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
245:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 245b
	jmp 244f
243:
244:
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [rcx], rax
	mov rax, QWORD PTR [r15+8]
	mov QWORD PTR [rcx+8], rax
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
21:
	ret
20:
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov ebx, 0
	mov rdi, r15
	add rdi, 488
	mov rbp, QWORD PTR [r15+200]
	shr rbp, 1
	sub rbp, 1
246:
	mov rax, QWORD PTR [r15+208]
	mov ecx, DWORD PTR [rax]
	shl rcx, 32
	or rcx, rbx
	mov rdx, QWORD PTR [rax+4]
	movq xmm0, rcx
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rdi, 16
	add rbx, 1
	cmp rbx, rbp
	jne 246b
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, rbp
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_aesni}
	mov rsi, r15
	add rsi, 488
	mov rdi, r15
	add rdi, 16
	mov rcx, rbp
247:
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+16]
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 32
	add rdi, 16
	sub rcx, 2
	jne 247b
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	bswap rdx
	bswap rax
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+64], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+80], xmm0
	mov rax, QWORD PTR [r15+224]
	shr rax, 4
	mov rdx, QWORD PTR [r15+240]
	shr rdx, 4
	add rax, rdx
	cmp rax, 62
	jae 248f
	mov rdi, r15
	add rdi, 488
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 250f
	mov r14, rbx
	mov rcx, r14
	cmp rcx, 8
	jb 252f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
254:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 254b
	vzeroupper
	test rcx, rcx
	je 255f
257:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 257b
	jmp 256f
255:
256:
	jmp 253f
252:
258:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 258b
253:
	jmp 251f
250:
251:
	test rbp, rbp
	je 259f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
261:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 261b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 260f
259:
260:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 262f
	mov r14, rbx
	mov rcx, r14
	cmp rcx, 8
	jb 264f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
266:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 266b
	vzeroupper
	test rcx, rcx
	je 267f
269:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 269b
	jmp 268f
267:
268:
	jmp 265f
264:
270:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 270b
265:
	jmp 263f
262:
263:
	test rbp, rbp
	je 271f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
273:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 273b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 272f
271:
272:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	mov rcx, rdi
	sub rcx, r15
	shr rcx, 4
	sub rcx, 29
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	call {vg_ghash}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	jmp 249f
248:
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 274f
276:
	mov r14d, 64
	cmp rbx, r14
	jb 277f
	jmp 278f
277:
	mov r14, rbx
278:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 279f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
281:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 281b
	vzeroupper
	test rcx, rcx
	je 282f
284:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 284b
	jmp 283f
282:
283:
	jmp 280f
279:
285:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 285b
280:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 276b
	jmp 275f
274:
275:
	test rbp, rbp
	je 286f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
288:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 288b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash}
	jmp 287f
286:
287:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 289f
291:
	mov r14d, 64
	cmp rbx, r14
	jb 292f
	jmp 293f
292:
	mov r14, rbx
293:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 294f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
296:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 296b
	vzeroupper
	test rcx, rcx
	je 297f
299:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 299b
	jmp 298f
297:
298:
	jmp 295f
294:
2100:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2100b
295:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 291b
	jmp 290f
289:
290:
	test rbp, rbp
	je 2101f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
2103:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2103b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash}
	jmp 2102f
2101:
2102:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
249:
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
	mov rcx, r15
	add rcx, 1768
	call {vg_aes_expand_key_scratch_aesni}
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 0
	call {vg_aes_ctr32_aesni}
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rdx, rcx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 2104f
2106:
	mov r14d, 64
	cmp rbx, r14
	jb 2107f
	jmp 2108f
2107:
	mov r14, rbx
2108:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
2109:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 2109b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_aesni}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
	cmp rcx, 8
	jb 2110f
2112:
	vmovdqu ymm1, YMMWORD PTR [rsi]
	vmovdqu ymm0, YMMWORD PTR [r12]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12], ymm1
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vmovdqu ymm0, YMMWORD PTR [r12+32]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12+32], ymm1
	add r12, 64
	add rsi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 2112b
	vzeroupper
	test rcx, rcx
	je 2113f
2115:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 2115b
	jmp 2114f
2113:
2114:
	jmp 2111f
2110:
2116:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 2116b
2111:
	sub rbx, r14
	jne 2106b
	jmp 2105f
2104:
2105:
	test rbp, rbp
	je 2117f
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_aesni}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
2119:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2119b
	jmp 2118f
2117:
2118:
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [rcx], rax
	mov rax, QWORD PTR [r15+8]
	mov QWORD PTR [rcx+8], rax
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
	jmp 21b
	.p2align 6

vg_aes_gcm_siv_open_aesni_avx2:
	mov rax, QWORD PTR [rsp+8]
	or rax, r8
	cmp rax, 128
	jae 20f
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+8], rax
	mov ebx, 0
	mov rdi, r15
	add rdi, 488
	mov rbp, QWORD PTR [r15+200]
	shr rbp, 1
	sub rbp, 1
22:
	mov rax, QWORD PTR [r15+208]
	mov ecx, DWORD PTR [rax]
	shl rcx, 32
	or rcx, rbx
	mov rdx, QWORD PTR [rax+4]
	movq xmm0, rcx
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rdi, 16
	add rbx, 1
	cmp rbx, rbp
	jne 22b
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, rbp
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_aesni}
	mov rsi, r15
	add rsi, 488
	mov rdi, r15
	add rdi, 16
	mov rcx, rbp
23:
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+16]
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 32
	add rdi, 16
	sub rcx, 2
	jne 23b
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
	mov rcx, r15
	add rcx, 1768
	call {vg_aes_expand_key_scratch_aesni}
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	bswap rdx
	bswap rax
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+64], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+80], xmm0
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rdx, rcx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 24f
26:
	mov r14d, 64
	cmp rbx, r14
	jb 27f
	jmp 28f
27:
	mov r14, rbx
28:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
29:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 29b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_aesni}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
210:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 210b
	sub rbx, r14
	jne 26b
	jmp 25f
24:
25:
	test rbp, rbp
	je 211f
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_aesni}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
213:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 213b
	jmp 212f
211:
212:
	mov rax, QWORD PTR [r15+224]
	shr rax, 4
	mov rdx, QWORD PTR [r15+240]
	shr rdx, 4
	add rax, rdx
	cmp rax, 62
	jae 214f
	mov rdi, r15
	add rdi, 488
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 216f
	mov r14, rbx
	mov rcx, r14
218:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 218b
	jmp 217f
216:
217:
	test rbp, rbp
	je 219f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
221:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 221b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 220f
219:
220:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 222f
	mov r14, rbx
	mov rcx, r14
224:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 224b
	jmp 223f
222:
223:
	test rbp, rbp
	je 225f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
227:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 227b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 226f
225:
226:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	mov rcx, rdi
	sub rcx, r15
	shr rcx, 4
	sub rcx, 29
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	call {vg_ghash}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	jmp 215f
214:
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 228f
230:
	mov r14d, 64
	cmp rbx, r14
	jb 231f
	jmp 232f
231:
	mov r14, rbx
232:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
233:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 233b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 230b
	jmp 229f
228:
229:
	test rbp, rbp
	je 234f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
236:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 236b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash}
	jmp 235f
234:
235:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 237f
239:
	mov r14d, 64
	cmp rbx, r14
	jb 240f
	jmp 241f
240:
	mov r14, rbx
241:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
242:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 242b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 239b
	jmp 238f
237:
238:
	test rbp, rbp
	je 243f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
245:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 245b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash}
	jmp 244f
243:
244:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
215:
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_aesni}
	mov rax, QWORD PTR [r15]
	xor rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+8]
	xor rdx, QWORD PTR [r15+136]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+192], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov r11d, 0
	sub r11, QWORD PTR [r15+192]
	mov r10d, 0
	mov rcx, rbp
	shr rcx, 4
	test rcx, rcx
	je 246f
	movq xmm0, r11
	punpcklqdq xmm0, xmm0
248:
	movdqu xmm1, XMMWORD PTR [r12+r10*1]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [r12+r10*1], xmm1
	add r10, 16
	sub rcx, 1
	jne 248b
	jmp 247f
246:
247:
	cmp r10, rbp
	je 249f
251:
	movzx eax, BYTE PTR [r12+r10*1]
	and rax, r11
	mov BYTE PTR [r12+r10*1], al
	add r10, 1
	cmp r10, rbp
	jne 251b
	jmp 250f
249:
250:
	mov rax, QWORD PTR [r15+192]
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
21:
	ret
20:
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+8], rax
	mov ebx, 0
	mov rdi, r15
	add rdi, 488
	mov rbp, QWORD PTR [r15+200]
	shr rbp, 1
	sub rbp, 1
252:
	mov rax, QWORD PTR [r15+208]
	mov ecx, DWORD PTR [rax]
	shl rcx, 32
	or rcx, rbx
	mov rdx, QWORD PTR [rax+4]
	movq xmm0, rcx
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rdi, 16
	add rbx, 1
	cmp rbx, rbp
	jne 252b
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, rbp
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_aesni}
	mov rsi, r15
	add rsi, 488
	mov rdi, r15
	add rdi, 16
	mov rcx, rbp
253:
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+16]
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 32
	add rdi, 16
	sub rcx, 2
	jne 253b
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
	mov rcx, r15
	add rcx, 1768
	call {vg_aes_expand_key_scratch_aesni}
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	bswap rdx
	bswap rax
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+64], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+80], xmm0
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rdx, rcx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 254f
256:
	mov r14d, 64
	cmp rbx, r14
	jb 257f
	jmp 258f
257:
	mov r14, rbx
258:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
259:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 259b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_aesni}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
	cmp rcx, 8
	jb 260f
262:
	vmovdqu ymm1, YMMWORD PTR [rsi]
	vmovdqu ymm0, YMMWORD PTR [r12]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12], ymm1
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vmovdqu ymm0, YMMWORD PTR [r12+32]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12+32], ymm1
	add r12, 64
	add rsi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 262b
	vzeroupper
	test rcx, rcx
	je 263f
265:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 265b
	jmp 264f
263:
264:
	jmp 261f
260:
266:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 266b
261:
	sub rbx, r14
	jne 256b
	jmp 255f
254:
255:
	test rbp, rbp
	je 267f
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_aesni}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
269:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 269b
	jmp 268f
267:
268:
	mov rax, QWORD PTR [r15+224]
	shr rax, 4
	mov rdx, QWORD PTR [r15+240]
	shr rdx, 4
	add rax, rdx
	cmp rax, 62
	jae 270f
	mov rdi, r15
	add rdi, 488
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 272f
	mov r14, rbx
	mov rcx, r14
	cmp rcx, 8
	jb 274f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
276:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 276b
	vzeroupper
	test rcx, rcx
	je 277f
279:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 279b
	jmp 278f
277:
278:
	jmp 275f
274:
280:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 280b
275:
	jmp 273f
272:
273:
	test rbp, rbp
	je 281f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
283:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 283b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 282f
281:
282:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 284f
	mov r14, rbx
	mov rcx, r14
	cmp rcx, 8
	jb 286f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
288:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 288b
	vzeroupper
	test rcx, rcx
	je 289f
291:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 291b
	jmp 290f
289:
290:
	jmp 287f
286:
292:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 292b
287:
	jmp 285f
284:
285:
	test rbp, rbp
	je 293f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
295:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 295b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 294f
293:
294:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	mov rcx, rdi
	sub rcx, r15
	shr rcx, 4
	sub rcx, 29
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	call {vg_ghash}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	jmp 271f
270:
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 296f
298:
	mov r14d, 64
	cmp rbx, r14
	jb 299f
	jmp 2100f
299:
	mov r14, rbx
2100:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 2101f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
2103:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 2103b
	vzeroupper
	test rcx, rcx
	je 2104f
2106:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2106b
	jmp 2105f
2104:
2105:
	jmp 2102f
2101:
2107:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2107b
2102:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 298b
	jmp 297f
296:
297:
	test rbp, rbp
	je 2108f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
2110:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2110b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash}
	jmp 2109f
2108:
2109:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 2111f
2113:
	mov r14d, 64
	cmp rbx, r14
	jb 2114f
	jmp 2115f
2114:
	mov r14, rbx
2115:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 2116f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
2118:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 2118b
	vzeroupper
	test rcx, rcx
	je 2119f
2121:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2121b
	jmp 2120f
2119:
2120:
	jmp 2117f
2116:
2122:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2122b
2117:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 2113b
	jmp 2112f
2111:
2112:
	test rbp, rbp
	je 2123f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
2125:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2125b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash}
	jmp 2124f
2123:
2124:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
271:
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_aesni}
	mov rax, QWORD PTR [r15]
	xor rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+8]
	xor rdx, QWORD PTR [r15+136]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+192], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov r11d, 0
	sub r11, QWORD PTR [r15+192]
	mov r10d, 0
	mov rcx, rbp
	shr rcx, 4
	test rcx, rcx
	je 2126f
	movq xmm0, r11
	punpcklqdq xmm0, xmm0
2128:
	movdqu xmm1, XMMWORD PTR [r12+r10*1]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [r12+r10*1], xmm1
	add r10, 16
	sub rcx, 1
	jne 2128b
	jmp 2127f
2126:
2127:
	cmp r10, rbp
	je 2129f
2131:
	movzx eax, BYTE PTR [r12+r10*1]
	and rax, r11
	mov BYTE PTR [r12+r10*1], al
	add r10, 1
	cmp r10, rbp
	jne 2131b
	jmp 2130f
2129:
2130:
	mov rax, QWORD PTR [r15+192]
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
	jmp 21b
	.p2align 6

vg_aes_gcm_siv_seal_aesni:
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov ebx, 0
	mov rdi, r15
	add rdi, 488
	mov rbp, QWORD PTR [r15+200]
	shr rbp, 1
	sub rbp, 1
20:
	mov rax, QWORD PTR [r15+208]
	mov ecx, DWORD PTR [rax]
	shl rcx, 32
	or rcx, rbx
	mov rdx, QWORD PTR [rax+4]
	movq xmm0, rcx
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rdi, 16
	add rbx, 1
	cmp rbx, rbp
	jne 20b
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, rbp
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_aesni}
	mov rsi, r15
	add rsi, 488
	mov rdi, r15
	add rdi, 16
	mov rcx, rbp
21:
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+16]
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 32
	add rdi, 16
	sub rcx, 2
	jne 21b
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	bswap rdx
	bswap rax
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+64], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+80], xmm0
	mov rax, QWORD PTR [r15+224]
	shr rax, 4
	mov rdx, QWORD PTR [r15+240]
	shr rdx, 4
	add rax, rdx
	cmp rax, 62
	jae 22f
	mov rdi, r15
	add rdi, 488
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 24f
	mov r14, rbx
	mov rcx, r14
26:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 26b
	jmp 25f
24:
25:
	test rbp, rbp
	je 27f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
29:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 29b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 28f
27:
28:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 210f
	mov r14, rbx
	mov rcx, r14
212:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 212b
	jmp 211f
210:
211:
	test rbp, rbp
	je 213f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
215:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 215b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 214f
213:
214:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	mov rcx, rdi
	sub rcx, r15
	shr rcx, 4
	sub rcx, 29
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	call {vg_ghash}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	jmp 23f
22:
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 216f
218:
	mov r14d, 64
	cmp rbx, r14
	jb 219f
	jmp 220f
219:
	mov r14, rbx
220:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
221:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 221b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 218b
	jmp 217f
216:
217:
	test rbp, rbp
	je 222f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
224:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 224b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash}
	jmp 223f
222:
223:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 225f
227:
	mov r14d, 64
	cmp rbx, r14
	jb 228f
	jmp 229f
228:
	mov r14, rbx
229:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
230:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 230b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 227b
	jmp 226f
225:
226:
	test rbp, rbp
	je 231f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
233:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 233b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash}
	jmp 232f
231:
232:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
23:
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
	mov rcx, r15
	add rcx, 1768
	call {vg_aes_expand_key_scratch_aesni}
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 0
	call {vg_aes_ctr32_aesni}
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rdx, rcx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 234f
236:
	mov r14d, 64
	cmp rbx, r14
	jb 237f
	jmp 238f
237:
	mov r14, rbx
238:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
239:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 239b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_aesni}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
240:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 240b
	sub rbx, r14
	jne 236b
	jmp 235f
234:
235:
	test rbp, rbp
	je 241f
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_aesni}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
243:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 243b
	jmp 242f
241:
242:
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [rcx], rax
	mov rax, QWORD PTR [r15+8]
	mov QWORD PTR [rcx+8], rax
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
	ret
	.p2align 6

vg_aes_gcm_siv_open_aesni:
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+8], rax
	mov ebx, 0
	mov rdi, r15
	add rdi, 488
	mov rbp, QWORD PTR [r15+200]
	shr rbp, 1
	sub rbp, 1
20:
	mov rax, QWORD PTR [r15+208]
	mov ecx, DWORD PTR [rax]
	shl rcx, 32
	or rcx, rbx
	mov rdx, QWORD PTR [rax+4]
	movq xmm0, rcx
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rdi, 16
	add rbx, 1
	cmp rbx, rbp
	jne 20b
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, rbp
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_aesni}
	mov rsi, r15
	add rsi, 488
	mov rdi, r15
	add rdi, 16
	mov rcx, rbp
21:
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+16]
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 32
	add rdi, 16
	sub rcx, 2
	jne 21b
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
	mov rcx, r15
	add rcx, 1768
	call {vg_aes_expand_key_scratch_aesni}
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	bswap rdx
	bswap rax
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+64], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+80], xmm0
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rdx, rcx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 22f
24:
	mov r14d, 64
	cmp rbx, r14
	jb 25f
	jmp 26f
25:
	mov r14, rbx
26:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
27:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 27b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks_aesni}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
28:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 28b
	sub rbx, r14
	jne 24b
	jmp 23f
22:
23:
	test rbp, rbp
	je 29f
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_aesni}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
211:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 211b
	jmp 210f
29:
210:
	mov rax, QWORD PTR [r15+224]
	shr rax, 4
	mov rdx, QWORD PTR [r15+240]
	shr rdx, 4
	add rax, rdx
	cmp rax, 62
	jae 212f
	mov rdi, r15
	add rdi, 488
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 214f
	mov r14, rbx
	mov rcx, r14
216:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 216b
	jmp 215f
214:
215:
	test rbp, rbp
	je 217f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
219:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 219b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 218f
217:
218:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 220f
	mov r14, rbx
	mov rcx, r14
222:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 222b
	jmp 221f
220:
221:
	test rbp, rbp
	je 223f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
225:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 225b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 224f
223:
224:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	mov rcx, rdi
	sub rcx, r15
	shr rcx, 4
	sub rcx, 29
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	call {vg_ghash}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	jmp 213f
212:
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 226f
228:
	mov r14d, 64
	cmp rbx, r14
	jb 229f
	jmp 230f
229:
	mov r14, rbx
230:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
231:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 231b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 228b
	jmp 227f
226:
227:
	test rbp, rbp
	je 232f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
234:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 234b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash}
	jmp 233f
232:
233:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 235f
237:
	mov r14d, 64
	cmp rbx, r14
	jb 238f
	jmp 239f
238:
	mov r14, rbx
239:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
240:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 240b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 237b
	jmp 236f
235:
236:
	test rbp, rbp
	je 241f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
243:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 243b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash}
	jmp 242f
241:
242:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
213:
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32_aesni}
	mov rax, QWORD PTR [r15]
	xor rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+8]
	xor rdx, QWORD PTR [r15+136]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+192], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov r11d, 0
	sub r11, QWORD PTR [r15+192]
	mov r10d, 0
	mov rcx, rbp
	shr rcx, 4
	test rcx, rcx
	je 244f
	movq xmm0, r11
	punpcklqdq xmm0, xmm0
246:
	movdqu xmm1, XMMWORD PTR [r12+r10*1]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [r12+r10*1], xmm1
	add r10, 16
	sub rcx, 1
	jne 246b
	jmp 245f
244:
245:
	cmp r10, rbp
	je 247f
249:
	movzx eax, BYTE PTR [r12+r10*1]
	and rax, r11
	mov BYTE PTR [r12+r10*1], al
	add r10, 1
	cmp r10, rbp
	jne 249b
	jmp 248f
247:
248:
	mov rax, QWORD PTR [r15+192]
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
	ret
	.p2align 6

vg_aes_gcm_siv_seal_pclmul_avx2:
	mov rax, QWORD PTR [rsp+8]
	or rax, r8
	cmp rax, 128
	jae 20f
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov ebx, 0
	mov rdi, r15
	add rdi, 488
	mov rbp, QWORD PTR [r15+200]
	shr rbp, 1
	sub rbp, 1
22:
	mov rax, QWORD PTR [r15+208]
	mov ecx, DWORD PTR [rax]
	shl rcx, 32
	or rcx, rbx
	mov rdx, QWORD PTR [rax+4]
	movq xmm0, rcx
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rdi, 16
	add rbx, 1
	cmp rbx, rbp
	jne 22b
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, rbp
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks}
	mov rsi, r15
	add rsi, 488
	mov rdi, r15
	add rdi, 16
	mov rcx, rbp
23:
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+16]
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 32
	add rdi, 16
	sub rcx, 2
	jne 23b
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	bswap rdx
	bswap rax
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+64], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+80], xmm0
	mov rax, QWORD PTR [r15+224]
	shr rax, 4
	mov rdx, QWORD PTR [r15+240]
	shr rdx, 4
	add rax, rdx
	cmp rax, 62
	jae 24f
	mov rdi, r15
	add rdi, 488
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 26f
	mov r14, rbx
	mov rcx, r14
28:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 28b
	jmp 27f
26:
27:
	test rbp, rbp
	je 29f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
211:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 211b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 210f
29:
210:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 212f
	mov r14, rbx
	mov rcx, r14
214:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 214b
	jmp 213f
212:
213:
	test rbp, rbp
	je 215f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
217:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 217b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 216f
215:
216:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	mov rcx, rdi
	sub rcx, r15
	shr rcx, 4
	sub rcx, 29
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	jmp 25f
24:
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 218f
220:
	mov r14d, 64
	cmp rbx, r14
	jb 221f
	jmp 222f
221:
	mov r14, rbx
222:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
223:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 223b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_pclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 220b
	jmp 219f
218:
219:
	test rbp, rbp
	je 224f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
226:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 226b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_pclmul}
	jmp 225f
224:
225:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 227f
229:
	mov r14d, 64
	cmp rbx, r14
	jb 230f
	jmp 231f
230:
	mov r14, rbx
231:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
232:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 232b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_pclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 229b
	jmp 228f
227:
228:
	test rbp, rbp
	je 233f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
235:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 235b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_pclmul}
	jmp 234f
233:
234:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
25:
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
	mov rcx, r15
	add rcx, 1768
	call {vg_aes_expand_key_scratch}
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 0
	call {vg_aes_ctr32}
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rdx, rcx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 236f
238:
	mov r14d, 64
	cmp rbx, r14
	jb 239f
	jmp 240f
239:
	mov r14, rbx
240:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
241:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 241b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
242:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 242b
	sub rbx, r14
	jne 238b
	jmp 237f
236:
237:
	test rbp, rbp
	je 243f
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
245:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 245b
	jmp 244f
243:
244:
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [rcx], rax
	mov rax, QWORD PTR [r15+8]
	mov QWORD PTR [rcx+8], rax
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
21:
	vpxor xmm0, xmm0, xmm0
	vpxor xmm1, xmm1, xmm1
	vpxor xmm2, xmm2, xmm2
	vpxor xmm3, xmm3, xmm3
	vpxor xmm4, xmm4, xmm4
	vpxor xmm5, xmm5, xmm5
	vpxor xmm6, xmm6, xmm6
	vpxor xmm7, xmm7, xmm7
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	vpxor xmm11, xmm11, xmm11
	vpxor xmm12, xmm12, xmm12
	vpxor xmm13, xmm13, xmm13
	vpxor xmm14, xmm14, xmm14
	vpxor xmm15, xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-8]
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp-3848]
	vmovdqu YMMWORD PTR [rsp+3816], ymm0
	vmovdqu YMMWORD PTR [rsp+3784], ymm0
	vmovdqu YMMWORD PTR [rsp+3752], ymm0
	vmovdqu YMMWORD PTR [rsp+3720], ymm0
	vmovdqu YMMWORD PTR [rsp+3688], ymm0
	vmovdqu YMMWORD PTR [rsp+3656], ymm0
	vmovdqu YMMWORD PTR [rsp+3624], ymm0
	vmovdqu YMMWORD PTR [rsp+3592], ymm0
	vmovdqu YMMWORD PTR [rsp+3560], ymm0
	vmovdqu YMMWORD PTR [rsp+3528], ymm0
	vmovdqu YMMWORD PTR [rsp+3496], ymm0
	vmovdqu YMMWORD PTR [rsp+3464], ymm0
	vmovdqu YMMWORD PTR [rsp+3432], ymm0
	vmovdqu YMMWORD PTR [rsp+3400], ymm0
	vmovdqu YMMWORD PTR [rsp+3368], ymm0
	vmovdqu YMMWORD PTR [rsp+3336], ymm0
	vmovdqu YMMWORD PTR [rsp+3304], ymm0
	vmovdqu YMMWORD PTR [rsp+3272], ymm0
	vmovdqu YMMWORD PTR [rsp+3240], ymm0
	vmovdqu YMMWORD PTR [rsp+3208], ymm0
	vmovdqu YMMWORD PTR [rsp+3176], ymm0
	vmovdqu YMMWORD PTR [rsp+3144], ymm0
	vmovdqu YMMWORD PTR [rsp+3112], ymm0
	vmovdqu YMMWORD PTR [rsp+3080], ymm0
	vmovdqu YMMWORD PTR [rsp+3048], ymm0
	vmovdqu YMMWORD PTR [rsp+3016], ymm0
	vmovdqu YMMWORD PTR [rsp+2984], ymm0
	vmovdqu YMMWORD PTR [rsp+2952], ymm0
	vmovdqu YMMWORD PTR [rsp+2920], ymm0
	vmovdqu YMMWORD PTR [rsp+2888], ymm0
	vmovdqu YMMWORD PTR [rsp+2856], ymm0
	vmovdqu YMMWORD PTR [rsp+2824], ymm0
	vmovdqu YMMWORD PTR [rsp+2792], ymm0
	vmovdqu YMMWORD PTR [rsp+2760], ymm0
	vmovdqu YMMWORD PTR [rsp+2728], ymm0
	vmovdqu YMMWORD PTR [rsp+2696], ymm0
	vmovdqu YMMWORD PTR [rsp+2664], ymm0
	vmovdqu YMMWORD PTR [rsp+2632], ymm0
	vmovdqu YMMWORD PTR [rsp+2600], ymm0
	vmovdqu YMMWORD PTR [rsp+2568], ymm0
	vmovdqu YMMWORD PTR [rsp+2536], ymm0
	vmovdqu YMMWORD PTR [rsp+2504], ymm0
	vmovdqu YMMWORD PTR [rsp+2472], ymm0
	vmovdqu YMMWORD PTR [rsp+2440], ymm0
	vmovdqu YMMWORD PTR [rsp+2408], ymm0
	vmovdqu YMMWORD PTR [rsp+2376], ymm0
	vmovdqu YMMWORD PTR [rsp+2344], ymm0
	vmovdqu YMMWORD PTR [rsp+2312], ymm0
	vmovdqu YMMWORD PTR [rsp+2280], ymm0
	vmovdqu YMMWORD PTR [rsp+2248], ymm0
	vmovdqu YMMWORD PTR [rsp+2216], ymm0
	vmovdqu YMMWORD PTR [rsp+2184], ymm0
	vmovdqu YMMWORD PTR [rsp+2152], ymm0
	vmovdqu YMMWORD PTR [rsp+2120], ymm0
	vmovdqu YMMWORD PTR [rsp+2088], ymm0
	vmovdqu YMMWORD PTR [rsp+2056], ymm0
	vmovdqu YMMWORD PTR [rsp+2024], ymm0
	vmovdqu YMMWORD PTR [rsp+1992], ymm0
	vmovdqu YMMWORD PTR [rsp+1960], ymm0
	vmovdqu YMMWORD PTR [rsp+1928], ymm0
	vmovdqu YMMWORD PTR [rsp+1896], ymm0
	vmovdqu YMMWORD PTR [rsp+1864], ymm0
	vmovdqu YMMWORD PTR [rsp+1832], ymm0
	vmovdqu YMMWORD PTR [rsp+1800], ymm0
	vmovdqu YMMWORD PTR [rsp+1768], ymm0
	vmovdqu YMMWORD PTR [rsp+1736], ymm0
	vmovdqu YMMWORD PTR [rsp+1704], ymm0
	vmovdqu YMMWORD PTR [rsp+1672], ymm0
	vmovdqu YMMWORD PTR [rsp+1640], ymm0
	vmovdqu YMMWORD PTR [rsp+1608], ymm0
	vmovdqu YMMWORD PTR [rsp+1576], ymm0
	vmovdqu YMMWORD PTR [rsp+1544], ymm0
	vmovdqu YMMWORD PTR [rsp+1512], ymm0
	vmovdqu YMMWORD PTR [rsp+1480], ymm0
	vmovdqu YMMWORD PTR [rsp+1448], ymm0
	vmovdqu YMMWORD PTR [rsp+1416], ymm0
	vmovdqu YMMWORD PTR [rsp+1384], ymm0
	vmovdqu YMMWORD PTR [rsp+1352], ymm0
	vmovdqu YMMWORD PTR [rsp+1320], ymm0
	vmovdqu YMMWORD PTR [rsp+1288], ymm0
	vmovdqu YMMWORD PTR [rsp+1256], ymm0
	vmovdqu YMMWORD PTR [rsp+1224], ymm0
	vmovdqu YMMWORD PTR [rsp+1192], ymm0
	vmovdqu YMMWORD PTR [rsp+1160], ymm0
	vmovdqu YMMWORD PTR [rsp+1128], ymm0
	vmovdqu YMMWORD PTR [rsp+1096], ymm0
	vmovdqu YMMWORD PTR [rsp+1064], ymm0
	vmovdqu YMMWORD PTR [rsp+1032], ymm0
	vmovdqu YMMWORD PTR [rsp+1000], ymm0
	vmovdqu YMMWORD PTR [rsp+968], ymm0
	vmovdqu YMMWORD PTR [rsp+936], ymm0
	vmovdqu YMMWORD PTR [rsp+904], ymm0
	vmovdqu YMMWORD PTR [rsp+872], ymm0
	vmovdqu YMMWORD PTR [rsp+840], ymm0
	vmovdqu YMMWORD PTR [rsp+808], ymm0
	vmovdqu YMMWORD PTR [rsp+776], ymm0
	vmovdqu YMMWORD PTR [rsp+744], ymm0
	vmovdqu YMMWORD PTR [rsp+712], ymm0
	vmovdqu YMMWORD PTR [rsp+680], ymm0
	vmovdqu YMMWORD PTR [rsp+648], ymm0
	vmovdqu YMMWORD PTR [rsp+616], ymm0
	vmovdqu YMMWORD PTR [rsp+584], ymm0
	vmovdqu YMMWORD PTR [rsp+552], ymm0
	vmovdqu YMMWORD PTR [rsp+520], ymm0
	vmovdqu YMMWORD PTR [rsp+488], ymm0
	vmovdqu YMMWORD PTR [rsp+456], ymm0
	vmovdqu YMMWORD PTR [rsp+424], ymm0
	vmovdqu YMMWORD PTR [rsp+392], ymm0
	vmovdqu YMMWORD PTR [rsp+360], ymm0
	vmovdqu YMMWORD PTR [rsp+328], ymm0
	vmovdqu YMMWORD PTR [rsp+296], ymm0
	vmovdqu YMMWORD PTR [rsp+264], ymm0
	vmovdqu YMMWORD PTR [rsp+232], ymm0
	vmovdqu YMMWORD PTR [rsp+200], ymm0
	vmovdqu YMMWORD PTR [rsp+168], ymm0
	vmovdqu YMMWORD PTR [rsp+136], ymm0
	vmovdqu YMMWORD PTR [rsp+104], ymm0
	vmovdqu YMMWORD PTR [rsp+72], ymm0
	vmovdqu YMMWORD PTR [rsp+40], ymm0
	vmovdqu YMMWORD PTR [rsp+8], ymm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+3848]
	lea rsp, [rsp+8]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
20:
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov ebx, 0
	mov rdi, r15
	add rdi, 488
	mov rbp, QWORD PTR [r15+200]
	shr rbp, 1
	sub rbp, 1
246:
	mov rax, QWORD PTR [r15+208]
	mov ecx, DWORD PTR [rax]
	shl rcx, 32
	or rcx, rbx
	mov rdx, QWORD PTR [rax+4]
	movq xmm0, rcx
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rdi, 16
	add rbx, 1
	cmp rbx, rbp
	jne 246b
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, rbp
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks}
	mov rsi, r15
	add rsi, 488
	mov rdi, r15
	add rdi, 16
	mov rcx, rbp
247:
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+16]
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 32
	add rdi, 16
	sub rcx, 2
	jne 247b
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	bswap rdx
	bswap rax
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+64], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+80], xmm0
	mov rax, QWORD PTR [r15+224]
	shr rax, 4
	mov rdx, QWORD PTR [r15+240]
	shr rdx, 4
	add rax, rdx
	cmp rax, 62
	jae 248f
	mov rdi, r15
	add rdi, 488
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 250f
	mov r14, rbx
	mov rcx, r14
	cmp rcx, 8
	jb 252f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
254:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 254b
	vzeroupper
	test rcx, rcx
	je 255f
257:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 257b
	jmp 256f
255:
256:
	jmp 253f
252:
258:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 258b
253:
	jmp 251f
250:
251:
	test rbp, rbp
	je 259f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
261:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 261b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 260f
259:
260:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 262f
	mov r14, rbx
	mov rcx, r14
	cmp rcx, 8
	jb 264f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
266:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 266b
	vzeroupper
	test rcx, rcx
	je 267f
269:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 269b
	jmp 268f
267:
268:
	jmp 265f
264:
270:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 270b
265:
	jmp 263f
262:
263:
	test rbp, rbp
	je 271f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
273:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 273b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 272f
271:
272:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	mov rcx, rdi
	sub rcx, r15
	shr rcx, 4
	sub rcx, 29
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	jmp 249f
248:
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 274f
276:
	mov r14d, 64
	cmp rbx, r14
	jb 277f
	jmp 278f
277:
	mov r14, rbx
278:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 279f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
281:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 281b
	vzeroupper
	test rcx, rcx
	je 282f
284:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 284b
	jmp 283f
282:
283:
	jmp 280f
279:
285:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 285b
280:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_pclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 276b
	jmp 275f
274:
275:
	test rbp, rbp
	je 286f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
288:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 288b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_pclmul}
	jmp 287f
286:
287:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 289f
291:
	mov r14d, 64
	cmp rbx, r14
	jb 292f
	jmp 293f
292:
	mov r14, rbx
293:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 294f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
296:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 296b
	vzeroupper
	test rcx, rcx
	je 297f
299:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 299b
	jmp 298f
297:
298:
	jmp 295f
294:
2100:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2100b
295:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_pclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 291b
	jmp 290f
289:
290:
	test rbp, rbp
	je 2101f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
2103:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2103b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_pclmul}
	jmp 2102f
2101:
2102:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
249:
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
	mov rcx, r15
	add rcx, 1768
	call {vg_aes_expand_key_scratch}
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 0
	call {vg_aes_ctr32}
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rdx, rcx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 2104f
2106:
	mov r14d, 64
	cmp rbx, r14
	jb 2107f
	jmp 2108f
2107:
	mov r14, rbx
2108:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
2109:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 2109b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
	cmp rcx, 8
	jb 2110f
2112:
	vmovdqu ymm1, YMMWORD PTR [rsi]
	vmovdqu ymm0, YMMWORD PTR [r12]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12], ymm1
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vmovdqu ymm0, YMMWORD PTR [r12+32]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12+32], ymm1
	add r12, 64
	add rsi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 2112b
	vzeroupper
	test rcx, rcx
	je 2113f
2115:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 2115b
	jmp 2114f
2113:
2114:
	jmp 2111f
2110:
2116:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 2116b
2111:
	sub rbx, r14
	jne 2106b
	jmp 2105f
2104:
2105:
	test rbp, rbp
	je 2117f
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
2119:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2119b
	jmp 2118f
2117:
2118:
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [rcx], rax
	mov rax, QWORD PTR [r15+8]
	mov QWORD PTR [rcx+8], rax
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
	jmp 21b
	.p2align 6

vg_aes_gcm_siv_open_pclmul_avx2:
	mov rax, QWORD PTR [rsp+8]
	or rax, r8
	cmp rax, 128
	jae 20f
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+8], rax
	mov ebx, 0
	mov rdi, r15
	add rdi, 488
	mov rbp, QWORD PTR [r15+200]
	shr rbp, 1
	sub rbp, 1
22:
	mov rax, QWORD PTR [r15+208]
	mov ecx, DWORD PTR [rax]
	shl rcx, 32
	or rcx, rbx
	mov rdx, QWORD PTR [rax+4]
	movq xmm0, rcx
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rdi, 16
	add rbx, 1
	cmp rbx, rbp
	jne 22b
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, rbp
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks}
	mov rsi, r15
	add rsi, 488
	mov rdi, r15
	add rdi, 16
	mov rcx, rbp
23:
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+16]
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 32
	add rdi, 16
	sub rcx, 2
	jne 23b
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
	mov rcx, r15
	add rcx, 1768
	call {vg_aes_expand_key_scratch}
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	bswap rdx
	bswap rax
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+64], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+80], xmm0
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rdx, rcx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 24f
26:
	mov r14d, 64
	cmp rbx, r14
	jb 27f
	jmp 28f
27:
	mov r14, rbx
28:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
29:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 29b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
210:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 210b
	sub rbx, r14
	jne 26b
	jmp 25f
24:
25:
	test rbp, rbp
	je 211f
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
213:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 213b
	jmp 212f
211:
212:
	mov rax, QWORD PTR [r15+224]
	shr rax, 4
	mov rdx, QWORD PTR [r15+240]
	shr rdx, 4
	add rax, rdx
	cmp rax, 62
	jae 214f
	mov rdi, r15
	add rdi, 488
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 216f
	mov r14, rbx
	mov rcx, r14
218:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 218b
	jmp 217f
216:
217:
	test rbp, rbp
	je 219f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
221:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 221b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 220f
219:
220:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 222f
	mov r14, rbx
	mov rcx, r14
224:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 224b
	jmp 223f
222:
223:
	test rbp, rbp
	je 225f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
227:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 227b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 226f
225:
226:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	mov rcx, rdi
	sub rcx, r15
	shr rcx, 4
	sub rcx, 29
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	jmp 215f
214:
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 228f
230:
	mov r14d, 64
	cmp rbx, r14
	jb 231f
	jmp 232f
231:
	mov r14, rbx
232:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
233:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 233b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_pclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 230b
	jmp 229f
228:
229:
	test rbp, rbp
	je 234f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
236:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 236b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_pclmul}
	jmp 235f
234:
235:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 237f
239:
	mov r14d, 64
	cmp rbx, r14
	jb 240f
	jmp 241f
240:
	mov r14, rbx
241:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
242:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 242b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_pclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 239b
	jmp 238f
237:
238:
	test rbp, rbp
	je 243f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
245:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 245b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_pclmul}
	jmp 244f
243:
244:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
215:
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32}
	mov rax, QWORD PTR [r15]
	xor rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+8]
	xor rdx, QWORD PTR [r15+136]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+192], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov r11d, 0
	sub r11, QWORD PTR [r15+192]
	mov r10d, 0
	mov rcx, rbp
	shr rcx, 4
	test rcx, rcx
	je 246f
	movq xmm0, r11
	punpcklqdq xmm0, xmm0
248:
	movdqu xmm1, XMMWORD PTR [r12+r10*1]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [r12+r10*1], xmm1
	add r10, 16
	sub rcx, 1
	jne 248b
	jmp 247f
246:
247:
	cmp r10, rbp
	je 249f
251:
	movzx eax, BYTE PTR [r12+r10*1]
	and rax, r11
	mov BYTE PTR [r12+r10*1], al
	add r10, 1
	cmp r10, rbp
	jne 251b
	jmp 250f
249:
250:
	mov rax, QWORD PTR [r15+192]
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
21:
	vpxor xmm0, xmm0, xmm0
	vpxor xmm1, xmm1, xmm1
	vpxor xmm2, xmm2, xmm2
	vpxor xmm3, xmm3, xmm3
	vpxor xmm4, xmm4, xmm4
	vpxor xmm5, xmm5, xmm5
	vpxor xmm6, xmm6, xmm6
	vpxor xmm7, xmm7, xmm7
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	vpxor xmm11, xmm11, xmm11
	vpxor xmm12, xmm12, xmm12
	vpxor xmm13, xmm13, xmm13
	vpxor xmm14, xmm14, xmm14
	vpxor xmm15, xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-8]
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp-3848]
	vmovdqu YMMWORD PTR [rsp+3816], ymm0
	vmovdqu YMMWORD PTR [rsp+3784], ymm0
	vmovdqu YMMWORD PTR [rsp+3752], ymm0
	vmovdqu YMMWORD PTR [rsp+3720], ymm0
	vmovdqu YMMWORD PTR [rsp+3688], ymm0
	vmovdqu YMMWORD PTR [rsp+3656], ymm0
	vmovdqu YMMWORD PTR [rsp+3624], ymm0
	vmovdqu YMMWORD PTR [rsp+3592], ymm0
	vmovdqu YMMWORD PTR [rsp+3560], ymm0
	vmovdqu YMMWORD PTR [rsp+3528], ymm0
	vmovdqu YMMWORD PTR [rsp+3496], ymm0
	vmovdqu YMMWORD PTR [rsp+3464], ymm0
	vmovdqu YMMWORD PTR [rsp+3432], ymm0
	vmovdqu YMMWORD PTR [rsp+3400], ymm0
	vmovdqu YMMWORD PTR [rsp+3368], ymm0
	vmovdqu YMMWORD PTR [rsp+3336], ymm0
	vmovdqu YMMWORD PTR [rsp+3304], ymm0
	vmovdqu YMMWORD PTR [rsp+3272], ymm0
	vmovdqu YMMWORD PTR [rsp+3240], ymm0
	vmovdqu YMMWORD PTR [rsp+3208], ymm0
	vmovdqu YMMWORD PTR [rsp+3176], ymm0
	vmovdqu YMMWORD PTR [rsp+3144], ymm0
	vmovdqu YMMWORD PTR [rsp+3112], ymm0
	vmovdqu YMMWORD PTR [rsp+3080], ymm0
	vmovdqu YMMWORD PTR [rsp+3048], ymm0
	vmovdqu YMMWORD PTR [rsp+3016], ymm0
	vmovdqu YMMWORD PTR [rsp+2984], ymm0
	vmovdqu YMMWORD PTR [rsp+2952], ymm0
	vmovdqu YMMWORD PTR [rsp+2920], ymm0
	vmovdqu YMMWORD PTR [rsp+2888], ymm0
	vmovdqu YMMWORD PTR [rsp+2856], ymm0
	vmovdqu YMMWORD PTR [rsp+2824], ymm0
	vmovdqu YMMWORD PTR [rsp+2792], ymm0
	vmovdqu YMMWORD PTR [rsp+2760], ymm0
	vmovdqu YMMWORD PTR [rsp+2728], ymm0
	vmovdqu YMMWORD PTR [rsp+2696], ymm0
	vmovdqu YMMWORD PTR [rsp+2664], ymm0
	vmovdqu YMMWORD PTR [rsp+2632], ymm0
	vmovdqu YMMWORD PTR [rsp+2600], ymm0
	vmovdqu YMMWORD PTR [rsp+2568], ymm0
	vmovdqu YMMWORD PTR [rsp+2536], ymm0
	vmovdqu YMMWORD PTR [rsp+2504], ymm0
	vmovdqu YMMWORD PTR [rsp+2472], ymm0
	vmovdqu YMMWORD PTR [rsp+2440], ymm0
	vmovdqu YMMWORD PTR [rsp+2408], ymm0
	vmovdqu YMMWORD PTR [rsp+2376], ymm0
	vmovdqu YMMWORD PTR [rsp+2344], ymm0
	vmovdqu YMMWORD PTR [rsp+2312], ymm0
	vmovdqu YMMWORD PTR [rsp+2280], ymm0
	vmovdqu YMMWORD PTR [rsp+2248], ymm0
	vmovdqu YMMWORD PTR [rsp+2216], ymm0
	vmovdqu YMMWORD PTR [rsp+2184], ymm0
	vmovdqu YMMWORD PTR [rsp+2152], ymm0
	vmovdqu YMMWORD PTR [rsp+2120], ymm0
	vmovdqu YMMWORD PTR [rsp+2088], ymm0
	vmovdqu YMMWORD PTR [rsp+2056], ymm0
	vmovdqu YMMWORD PTR [rsp+2024], ymm0
	vmovdqu YMMWORD PTR [rsp+1992], ymm0
	vmovdqu YMMWORD PTR [rsp+1960], ymm0
	vmovdqu YMMWORD PTR [rsp+1928], ymm0
	vmovdqu YMMWORD PTR [rsp+1896], ymm0
	vmovdqu YMMWORD PTR [rsp+1864], ymm0
	vmovdqu YMMWORD PTR [rsp+1832], ymm0
	vmovdqu YMMWORD PTR [rsp+1800], ymm0
	vmovdqu YMMWORD PTR [rsp+1768], ymm0
	vmovdqu YMMWORD PTR [rsp+1736], ymm0
	vmovdqu YMMWORD PTR [rsp+1704], ymm0
	vmovdqu YMMWORD PTR [rsp+1672], ymm0
	vmovdqu YMMWORD PTR [rsp+1640], ymm0
	vmovdqu YMMWORD PTR [rsp+1608], ymm0
	vmovdqu YMMWORD PTR [rsp+1576], ymm0
	vmovdqu YMMWORD PTR [rsp+1544], ymm0
	vmovdqu YMMWORD PTR [rsp+1512], ymm0
	vmovdqu YMMWORD PTR [rsp+1480], ymm0
	vmovdqu YMMWORD PTR [rsp+1448], ymm0
	vmovdqu YMMWORD PTR [rsp+1416], ymm0
	vmovdqu YMMWORD PTR [rsp+1384], ymm0
	vmovdqu YMMWORD PTR [rsp+1352], ymm0
	vmovdqu YMMWORD PTR [rsp+1320], ymm0
	vmovdqu YMMWORD PTR [rsp+1288], ymm0
	vmovdqu YMMWORD PTR [rsp+1256], ymm0
	vmovdqu YMMWORD PTR [rsp+1224], ymm0
	vmovdqu YMMWORD PTR [rsp+1192], ymm0
	vmovdqu YMMWORD PTR [rsp+1160], ymm0
	vmovdqu YMMWORD PTR [rsp+1128], ymm0
	vmovdqu YMMWORD PTR [rsp+1096], ymm0
	vmovdqu YMMWORD PTR [rsp+1064], ymm0
	vmovdqu YMMWORD PTR [rsp+1032], ymm0
	vmovdqu YMMWORD PTR [rsp+1000], ymm0
	vmovdqu YMMWORD PTR [rsp+968], ymm0
	vmovdqu YMMWORD PTR [rsp+936], ymm0
	vmovdqu YMMWORD PTR [rsp+904], ymm0
	vmovdqu YMMWORD PTR [rsp+872], ymm0
	vmovdqu YMMWORD PTR [rsp+840], ymm0
	vmovdqu YMMWORD PTR [rsp+808], ymm0
	vmovdqu YMMWORD PTR [rsp+776], ymm0
	vmovdqu YMMWORD PTR [rsp+744], ymm0
	vmovdqu YMMWORD PTR [rsp+712], ymm0
	vmovdqu YMMWORD PTR [rsp+680], ymm0
	vmovdqu YMMWORD PTR [rsp+648], ymm0
	vmovdqu YMMWORD PTR [rsp+616], ymm0
	vmovdqu YMMWORD PTR [rsp+584], ymm0
	vmovdqu YMMWORD PTR [rsp+552], ymm0
	vmovdqu YMMWORD PTR [rsp+520], ymm0
	vmovdqu YMMWORD PTR [rsp+488], ymm0
	vmovdqu YMMWORD PTR [rsp+456], ymm0
	vmovdqu YMMWORD PTR [rsp+424], ymm0
	vmovdqu YMMWORD PTR [rsp+392], ymm0
	vmovdqu YMMWORD PTR [rsp+360], ymm0
	vmovdqu YMMWORD PTR [rsp+328], ymm0
	vmovdqu YMMWORD PTR [rsp+296], ymm0
	vmovdqu YMMWORD PTR [rsp+264], ymm0
	vmovdqu YMMWORD PTR [rsp+232], ymm0
	vmovdqu YMMWORD PTR [rsp+200], ymm0
	vmovdqu YMMWORD PTR [rsp+168], ymm0
	vmovdqu YMMWORD PTR [rsp+136], ymm0
	vmovdqu YMMWORD PTR [rsp+104], ymm0
	vmovdqu YMMWORD PTR [rsp+72], ymm0
	vmovdqu YMMWORD PTR [rsp+40], ymm0
	vmovdqu YMMWORD PTR [rsp+8], ymm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+3848]
	lea rsp, [rsp+8]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
20:
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+8], rax
	mov ebx, 0
	mov rdi, r15
	add rdi, 488
	mov rbp, QWORD PTR [r15+200]
	shr rbp, 1
	sub rbp, 1
252:
	mov rax, QWORD PTR [r15+208]
	mov ecx, DWORD PTR [rax]
	shl rcx, 32
	or rcx, rbx
	mov rdx, QWORD PTR [rax+4]
	movq xmm0, rcx
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rdi, 16
	add rbx, 1
	cmp rbx, rbp
	jne 252b
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, rbp
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks}
	mov rsi, r15
	add rsi, 488
	mov rdi, r15
	add rdi, 16
	mov rcx, rbp
253:
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+16]
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 32
	add rdi, 16
	sub rcx, 2
	jne 253b
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
	mov rcx, r15
	add rcx, 1768
	call {vg_aes_expand_key_scratch}
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	bswap rdx
	bswap rax
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+64], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+80], xmm0
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rdx, rcx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 254f
256:
	mov r14d, 64
	cmp rbx, r14
	jb 257f
	jmp 258f
257:
	mov r14, rbx
258:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
259:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 259b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
	cmp rcx, 8
	jb 260f
262:
	vmovdqu ymm1, YMMWORD PTR [rsi]
	vmovdqu ymm0, YMMWORD PTR [r12]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12], ymm1
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vmovdqu ymm0, YMMWORD PTR [r12+32]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12+32], ymm1
	add r12, 64
	add rsi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 262b
	vzeroupper
	test rcx, rcx
	je 263f
265:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 265b
	jmp 264f
263:
264:
	jmp 261f
260:
266:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 266b
261:
	sub rbx, r14
	jne 256b
	jmp 255f
254:
255:
	test rbp, rbp
	je 267f
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
269:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 269b
	jmp 268f
267:
268:
	mov rax, QWORD PTR [r15+224]
	shr rax, 4
	mov rdx, QWORD PTR [r15+240]
	shr rdx, 4
	add rax, rdx
	cmp rax, 62
	jae 270f
	mov rdi, r15
	add rdi, 488
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 272f
	mov r14, rbx
	mov rcx, r14
	cmp rcx, 8
	jb 274f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
276:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 276b
	vzeroupper
	test rcx, rcx
	je 277f
279:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 279b
	jmp 278f
277:
278:
	jmp 275f
274:
280:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 280b
275:
	jmp 273f
272:
273:
	test rbp, rbp
	je 281f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
283:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 283b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 282f
281:
282:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 284f
	mov r14, rbx
	mov rcx, r14
	cmp rcx, 8
	jb 286f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
288:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 288b
	vzeroupper
	test rcx, rcx
	je 289f
291:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 291b
	jmp 290f
289:
290:
	jmp 287f
286:
292:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 292b
287:
	jmp 285f
284:
285:
	test rbp, rbp
	je 293f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
295:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 295b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 294f
293:
294:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	mov rcx, rdi
	sub rcx, r15
	shr rcx, 4
	sub rcx, 29
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	jmp 271f
270:
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 296f
298:
	mov r14d, 64
	cmp rbx, r14
	jb 299f
	jmp 2100f
299:
	mov r14, rbx
2100:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 2101f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
2103:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 2103b
	vzeroupper
	test rcx, rcx
	je 2104f
2106:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2106b
	jmp 2105f
2104:
2105:
	jmp 2102f
2101:
2107:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2107b
2102:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_pclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 298b
	jmp 297f
296:
297:
	test rbp, rbp
	je 2108f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
2110:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2110b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_pclmul}
	jmp 2109f
2108:
2109:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 2111f
2113:
	mov r14d, 64
	cmp rbx, r14
	jb 2114f
	jmp 2115f
2114:
	mov r14, rbx
2115:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 2116f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
2118:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 2118b
	vzeroupper
	test rcx, rcx
	je 2119f
2121:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2121b
	jmp 2120f
2119:
2120:
	jmp 2117f
2116:
2122:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2122b
2117:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_pclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 2113b
	jmp 2112f
2111:
2112:
	test rbp, rbp
	je 2123f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
2125:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2125b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_pclmul}
	jmp 2124f
2123:
2124:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
271:
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32}
	mov rax, QWORD PTR [r15]
	xor rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+8]
	xor rdx, QWORD PTR [r15+136]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+192], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov r11d, 0
	sub r11, QWORD PTR [r15+192]
	mov r10d, 0
	mov rcx, rbp
	shr rcx, 4
	test rcx, rcx
	je 2126f
	movq xmm0, r11
	punpcklqdq xmm0, xmm0
2128:
	movdqu xmm1, XMMWORD PTR [r12+r10*1]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [r12+r10*1], xmm1
	add r10, 16
	sub rcx, 1
	jne 2128b
	jmp 2127f
2126:
2127:
	cmp r10, rbp
	je 2129f
2131:
	movzx eax, BYTE PTR [r12+r10*1]
	and rax, r11
	mov BYTE PTR [r12+r10*1], al
	add r10, 1
	cmp r10, rbp
	jne 2131b
	jmp 2130f
2129:
2130:
	mov rax, QWORD PTR [r15+192]
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
	jmp 21b
	.p2align 6

vg_aes_gcm_siv_seal_pclmul:
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov ebx, 0
	mov rdi, r15
	add rdi, 488
	mov rbp, QWORD PTR [r15+200]
	shr rbp, 1
	sub rbp, 1
20:
	mov rax, QWORD PTR [r15+208]
	mov ecx, DWORD PTR [rax]
	shl rcx, 32
	or rcx, rbx
	mov rdx, QWORD PTR [rax+4]
	movq xmm0, rcx
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rdi, 16
	add rbx, 1
	cmp rbx, rbp
	jne 20b
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, rbp
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks}
	mov rsi, r15
	add rsi, 488
	mov rdi, r15
	add rdi, 16
	mov rcx, rbp
21:
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+16]
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 32
	add rdi, 16
	sub rcx, 2
	jne 21b
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	bswap rdx
	bswap rax
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+64], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+80], xmm0
	mov rax, QWORD PTR [r15+224]
	shr rax, 4
	mov rdx, QWORD PTR [r15+240]
	shr rdx, 4
	add rax, rdx
	cmp rax, 62
	jae 22f
	mov rdi, r15
	add rdi, 488
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 24f
	mov r14, rbx
	mov rcx, r14
26:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 26b
	jmp 25f
24:
25:
	test rbp, rbp
	je 27f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
29:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 29b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 28f
27:
28:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 210f
	mov r14, rbx
	mov rcx, r14
212:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 212b
	jmp 211f
210:
211:
	test rbp, rbp
	je 213f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
215:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 215b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 214f
213:
214:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	mov rcx, rdi
	sub rcx, r15
	shr rcx, 4
	sub rcx, 29
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	jmp 23f
22:
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 216f
218:
	mov r14d, 64
	cmp rbx, r14
	jb 219f
	jmp 220f
219:
	mov r14, rbx
220:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
221:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 221b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_pclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 218b
	jmp 217f
216:
217:
	test rbp, rbp
	je 222f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
224:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 224b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_pclmul}
	jmp 223f
222:
223:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 225f
227:
	mov r14d, 64
	cmp rbx, r14
	jb 228f
	jmp 229f
228:
	mov r14, rbx
229:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
230:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 230b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_pclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 227b
	jmp 226f
225:
226:
	test rbp, rbp
	je 231f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
233:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 233b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_pclmul}
	jmp 232f
231:
232:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
23:
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
	mov rcx, r15
	add rcx, 1768
	call {vg_aes_expand_key_scratch}
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 0
	call {vg_aes_ctr32}
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rdx, rcx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 234f
236:
	mov r14d, 64
	cmp rbx, r14
	jb 237f
	jmp 238f
237:
	mov r14, rbx
238:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
239:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 239b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
240:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 240b
	sub rbx, r14
	jne 236b
	jmp 235f
234:
235:
	test rbp, rbp
	je 241f
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
243:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 243b
	jmp 242f
241:
242:
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [rcx], rax
	mov rax, QWORD PTR [r15+8]
	mov QWORD PTR [rcx+8], rax
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	pxor xmm12, xmm12
	pxor xmm13, xmm13
	pxor xmm14, xmm14
	pxor xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-8]
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp-3848]
	movdqu XMMWORD PTR [rsp+3832], xmm0
	movdqu XMMWORD PTR [rsp+3816], xmm0
	movdqu XMMWORD PTR [rsp+3800], xmm0
	movdqu XMMWORD PTR [rsp+3784], xmm0
	movdqu XMMWORD PTR [rsp+3768], xmm0
	movdqu XMMWORD PTR [rsp+3752], xmm0
	movdqu XMMWORD PTR [rsp+3736], xmm0
	movdqu XMMWORD PTR [rsp+3720], xmm0
	movdqu XMMWORD PTR [rsp+3704], xmm0
	movdqu XMMWORD PTR [rsp+3688], xmm0
	movdqu XMMWORD PTR [rsp+3672], xmm0
	movdqu XMMWORD PTR [rsp+3656], xmm0
	movdqu XMMWORD PTR [rsp+3640], xmm0
	movdqu XMMWORD PTR [rsp+3624], xmm0
	movdqu XMMWORD PTR [rsp+3608], xmm0
	movdqu XMMWORD PTR [rsp+3592], xmm0
	movdqu XMMWORD PTR [rsp+3576], xmm0
	movdqu XMMWORD PTR [rsp+3560], xmm0
	movdqu XMMWORD PTR [rsp+3544], xmm0
	movdqu XMMWORD PTR [rsp+3528], xmm0
	movdqu XMMWORD PTR [rsp+3512], xmm0
	movdqu XMMWORD PTR [rsp+3496], xmm0
	movdqu XMMWORD PTR [rsp+3480], xmm0
	movdqu XMMWORD PTR [rsp+3464], xmm0
	movdqu XMMWORD PTR [rsp+3448], xmm0
	movdqu XMMWORD PTR [rsp+3432], xmm0
	movdqu XMMWORD PTR [rsp+3416], xmm0
	movdqu XMMWORD PTR [rsp+3400], xmm0
	movdqu XMMWORD PTR [rsp+3384], xmm0
	movdqu XMMWORD PTR [rsp+3368], xmm0
	movdqu XMMWORD PTR [rsp+3352], xmm0
	movdqu XMMWORD PTR [rsp+3336], xmm0
	movdqu XMMWORD PTR [rsp+3320], xmm0
	movdqu XMMWORD PTR [rsp+3304], xmm0
	movdqu XMMWORD PTR [rsp+3288], xmm0
	movdqu XMMWORD PTR [rsp+3272], xmm0
	movdqu XMMWORD PTR [rsp+3256], xmm0
	movdqu XMMWORD PTR [rsp+3240], xmm0
	movdqu XMMWORD PTR [rsp+3224], xmm0
	movdqu XMMWORD PTR [rsp+3208], xmm0
	movdqu XMMWORD PTR [rsp+3192], xmm0
	movdqu XMMWORD PTR [rsp+3176], xmm0
	movdqu XMMWORD PTR [rsp+3160], xmm0
	movdqu XMMWORD PTR [rsp+3144], xmm0
	movdqu XMMWORD PTR [rsp+3128], xmm0
	movdqu XMMWORD PTR [rsp+3112], xmm0
	movdqu XMMWORD PTR [rsp+3096], xmm0
	movdqu XMMWORD PTR [rsp+3080], xmm0
	movdqu XMMWORD PTR [rsp+3064], xmm0
	movdqu XMMWORD PTR [rsp+3048], xmm0
	movdqu XMMWORD PTR [rsp+3032], xmm0
	movdqu XMMWORD PTR [rsp+3016], xmm0
	movdqu XMMWORD PTR [rsp+3000], xmm0
	movdqu XMMWORD PTR [rsp+2984], xmm0
	movdqu XMMWORD PTR [rsp+2968], xmm0
	movdqu XMMWORD PTR [rsp+2952], xmm0
	movdqu XMMWORD PTR [rsp+2936], xmm0
	movdqu XMMWORD PTR [rsp+2920], xmm0
	movdqu XMMWORD PTR [rsp+2904], xmm0
	movdqu XMMWORD PTR [rsp+2888], xmm0
	movdqu XMMWORD PTR [rsp+2872], xmm0
	movdqu XMMWORD PTR [rsp+2856], xmm0
	movdqu XMMWORD PTR [rsp+2840], xmm0
	movdqu XMMWORD PTR [rsp+2824], xmm0
	movdqu XMMWORD PTR [rsp+2808], xmm0
	movdqu XMMWORD PTR [rsp+2792], xmm0
	movdqu XMMWORD PTR [rsp+2776], xmm0
	movdqu XMMWORD PTR [rsp+2760], xmm0
	movdqu XMMWORD PTR [rsp+2744], xmm0
	movdqu XMMWORD PTR [rsp+2728], xmm0
	movdqu XMMWORD PTR [rsp+2712], xmm0
	movdqu XMMWORD PTR [rsp+2696], xmm0
	movdqu XMMWORD PTR [rsp+2680], xmm0
	movdqu XMMWORD PTR [rsp+2664], xmm0
	movdqu XMMWORD PTR [rsp+2648], xmm0
	movdqu XMMWORD PTR [rsp+2632], xmm0
	movdqu XMMWORD PTR [rsp+2616], xmm0
	movdqu XMMWORD PTR [rsp+2600], xmm0
	movdqu XMMWORD PTR [rsp+2584], xmm0
	movdqu XMMWORD PTR [rsp+2568], xmm0
	movdqu XMMWORD PTR [rsp+2552], xmm0
	movdqu XMMWORD PTR [rsp+2536], xmm0
	movdqu XMMWORD PTR [rsp+2520], xmm0
	movdqu XMMWORD PTR [rsp+2504], xmm0
	movdqu XMMWORD PTR [rsp+2488], xmm0
	movdqu XMMWORD PTR [rsp+2472], xmm0
	movdqu XMMWORD PTR [rsp+2456], xmm0
	movdqu XMMWORD PTR [rsp+2440], xmm0
	movdqu XMMWORD PTR [rsp+2424], xmm0
	movdqu XMMWORD PTR [rsp+2408], xmm0
	movdqu XMMWORD PTR [rsp+2392], xmm0
	movdqu XMMWORD PTR [rsp+2376], xmm0
	movdqu XMMWORD PTR [rsp+2360], xmm0
	movdqu XMMWORD PTR [rsp+2344], xmm0
	movdqu XMMWORD PTR [rsp+2328], xmm0
	movdqu XMMWORD PTR [rsp+2312], xmm0
	movdqu XMMWORD PTR [rsp+2296], xmm0
	movdqu XMMWORD PTR [rsp+2280], xmm0
	movdqu XMMWORD PTR [rsp+2264], xmm0
	movdqu XMMWORD PTR [rsp+2248], xmm0
	movdqu XMMWORD PTR [rsp+2232], xmm0
	movdqu XMMWORD PTR [rsp+2216], xmm0
	movdqu XMMWORD PTR [rsp+2200], xmm0
	movdqu XMMWORD PTR [rsp+2184], xmm0
	movdqu XMMWORD PTR [rsp+2168], xmm0
	movdqu XMMWORD PTR [rsp+2152], xmm0
	movdqu XMMWORD PTR [rsp+2136], xmm0
	movdqu XMMWORD PTR [rsp+2120], xmm0
	movdqu XMMWORD PTR [rsp+2104], xmm0
	movdqu XMMWORD PTR [rsp+2088], xmm0
	movdqu XMMWORD PTR [rsp+2072], xmm0
	movdqu XMMWORD PTR [rsp+2056], xmm0
	movdqu XMMWORD PTR [rsp+2040], xmm0
	movdqu XMMWORD PTR [rsp+2024], xmm0
	movdqu XMMWORD PTR [rsp+2008], xmm0
	movdqu XMMWORD PTR [rsp+1992], xmm0
	movdqu XMMWORD PTR [rsp+1976], xmm0
	movdqu XMMWORD PTR [rsp+1960], xmm0
	movdqu XMMWORD PTR [rsp+1944], xmm0
	movdqu XMMWORD PTR [rsp+1928], xmm0
	movdqu XMMWORD PTR [rsp+1912], xmm0
	movdqu XMMWORD PTR [rsp+1896], xmm0
	movdqu XMMWORD PTR [rsp+1880], xmm0
	movdqu XMMWORD PTR [rsp+1864], xmm0
	movdqu XMMWORD PTR [rsp+1848], xmm0
	movdqu XMMWORD PTR [rsp+1832], xmm0
	movdqu XMMWORD PTR [rsp+1816], xmm0
	movdqu XMMWORD PTR [rsp+1800], xmm0
	movdqu XMMWORD PTR [rsp+1784], xmm0
	movdqu XMMWORD PTR [rsp+1768], xmm0
	movdqu XMMWORD PTR [rsp+1752], xmm0
	movdqu XMMWORD PTR [rsp+1736], xmm0
	movdqu XMMWORD PTR [rsp+1720], xmm0
	movdqu XMMWORD PTR [rsp+1704], xmm0
	movdqu XMMWORD PTR [rsp+1688], xmm0
	movdqu XMMWORD PTR [rsp+1672], xmm0
	movdqu XMMWORD PTR [rsp+1656], xmm0
	movdqu XMMWORD PTR [rsp+1640], xmm0
	movdqu XMMWORD PTR [rsp+1624], xmm0
	movdqu XMMWORD PTR [rsp+1608], xmm0
	movdqu XMMWORD PTR [rsp+1592], xmm0
	movdqu XMMWORD PTR [rsp+1576], xmm0
	movdqu XMMWORD PTR [rsp+1560], xmm0
	movdqu XMMWORD PTR [rsp+1544], xmm0
	movdqu XMMWORD PTR [rsp+1528], xmm0
	movdqu XMMWORD PTR [rsp+1512], xmm0
	movdqu XMMWORD PTR [rsp+1496], xmm0
	movdqu XMMWORD PTR [rsp+1480], xmm0
	movdqu XMMWORD PTR [rsp+1464], xmm0
	movdqu XMMWORD PTR [rsp+1448], xmm0
	movdqu XMMWORD PTR [rsp+1432], xmm0
	movdqu XMMWORD PTR [rsp+1416], xmm0
	movdqu XMMWORD PTR [rsp+1400], xmm0
	movdqu XMMWORD PTR [rsp+1384], xmm0
	movdqu XMMWORD PTR [rsp+1368], xmm0
	movdqu XMMWORD PTR [rsp+1352], xmm0
	movdqu XMMWORD PTR [rsp+1336], xmm0
	movdqu XMMWORD PTR [rsp+1320], xmm0
	movdqu XMMWORD PTR [rsp+1304], xmm0
	movdqu XMMWORD PTR [rsp+1288], xmm0
	movdqu XMMWORD PTR [rsp+1272], xmm0
	movdqu XMMWORD PTR [rsp+1256], xmm0
	movdqu XMMWORD PTR [rsp+1240], xmm0
	movdqu XMMWORD PTR [rsp+1224], xmm0
	movdqu XMMWORD PTR [rsp+1208], xmm0
	movdqu XMMWORD PTR [rsp+1192], xmm0
	movdqu XMMWORD PTR [rsp+1176], xmm0
	movdqu XMMWORD PTR [rsp+1160], xmm0
	movdqu XMMWORD PTR [rsp+1144], xmm0
	movdqu XMMWORD PTR [rsp+1128], xmm0
	movdqu XMMWORD PTR [rsp+1112], xmm0
	movdqu XMMWORD PTR [rsp+1096], xmm0
	movdqu XMMWORD PTR [rsp+1080], xmm0
	movdqu XMMWORD PTR [rsp+1064], xmm0
	movdqu XMMWORD PTR [rsp+1048], xmm0
	movdqu XMMWORD PTR [rsp+1032], xmm0
	movdqu XMMWORD PTR [rsp+1016], xmm0
	movdqu XMMWORD PTR [rsp+1000], xmm0
	movdqu XMMWORD PTR [rsp+984], xmm0
	movdqu XMMWORD PTR [rsp+968], xmm0
	movdqu XMMWORD PTR [rsp+952], xmm0
	movdqu XMMWORD PTR [rsp+936], xmm0
	movdqu XMMWORD PTR [rsp+920], xmm0
	movdqu XMMWORD PTR [rsp+904], xmm0
	movdqu XMMWORD PTR [rsp+888], xmm0
	movdqu XMMWORD PTR [rsp+872], xmm0
	movdqu XMMWORD PTR [rsp+856], xmm0
	movdqu XMMWORD PTR [rsp+840], xmm0
	movdqu XMMWORD PTR [rsp+824], xmm0
	movdqu XMMWORD PTR [rsp+808], xmm0
	movdqu XMMWORD PTR [rsp+792], xmm0
	movdqu XMMWORD PTR [rsp+776], xmm0
	movdqu XMMWORD PTR [rsp+760], xmm0
	movdqu XMMWORD PTR [rsp+744], xmm0
	movdqu XMMWORD PTR [rsp+728], xmm0
	movdqu XMMWORD PTR [rsp+712], xmm0
	movdqu XMMWORD PTR [rsp+696], xmm0
	movdqu XMMWORD PTR [rsp+680], xmm0
	movdqu XMMWORD PTR [rsp+664], xmm0
	movdqu XMMWORD PTR [rsp+648], xmm0
	movdqu XMMWORD PTR [rsp+632], xmm0
	movdqu XMMWORD PTR [rsp+616], xmm0
	movdqu XMMWORD PTR [rsp+600], xmm0
	movdqu XMMWORD PTR [rsp+584], xmm0
	movdqu XMMWORD PTR [rsp+568], xmm0
	movdqu XMMWORD PTR [rsp+552], xmm0
	movdqu XMMWORD PTR [rsp+536], xmm0
	movdqu XMMWORD PTR [rsp+520], xmm0
	movdqu XMMWORD PTR [rsp+504], xmm0
	movdqu XMMWORD PTR [rsp+488], xmm0
	movdqu XMMWORD PTR [rsp+472], xmm0
	movdqu XMMWORD PTR [rsp+456], xmm0
	movdqu XMMWORD PTR [rsp+440], xmm0
	movdqu XMMWORD PTR [rsp+424], xmm0
	movdqu XMMWORD PTR [rsp+408], xmm0
	movdqu XMMWORD PTR [rsp+392], xmm0
	movdqu XMMWORD PTR [rsp+376], xmm0
	movdqu XMMWORD PTR [rsp+360], xmm0
	movdqu XMMWORD PTR [rsp+344], xmm0
	movdqu XMMWORD PTR [rsp+328], xmm0
	movdqu XMMWORD PTR [rsp+312], xmm0
	movdqu XMMWORD PTR [rsp+296], xmm0
	movdqu XMMWORD PTR [rsp+280], xmm0
	movdqu XMMWORD PTR [rsp+264], xmm0
	movdqu XMMWORD PTR [rsp+248], xmm0
	movdqu XMMWORD PTR [rsp+232], xmm0
	movdqu XMMWORD PTR [rsp+216], xmm0
	movdqu XMMWORD PTR [rsp+200], xmm0
	movdqu XMMWORD PTR [rsp+184], xmm0
	movdqu XMMWORD PTR [rsp+168], xmm0
	movdqu XMMWORD PTR [rsp+152], xmm0
	movdqu XMMWORD PTR [rsp+136], xmm0
	movdqu XMMWORD PTR [rsp+120], xmm0
	movdqu XMMWORD PTR [rsp+104], xmm0
	movdqu XMMWORD PTR [rsp+88], xmm0
	movdqu XMMWORD PTR [rsp+72], xmm0
	movdqu XMMWORD PTR [rsp+56], xmm0
	movdqu XMMWORD PTR [rsp+40], xmm0
	movdqu XMMWORD PTR [rsp+24], xmm0
	movdqu XMMWORD PTR [rsp+8], xmm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+3848]
	lea rsp, [rsp+8]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6

vg_aes_gcm_siv_open_pclmul:
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+8], rax
	mov ebx, 0
	mov rdi, r15
	add rdi, 488
	mov rbp, QWORD PTR [r15+200]
	shr rbp, 1
	sub rbp, 1
20:
	mov rax, QWORD PTR [r15+208]
	mov ecx, DWORD PTR [rax]
	shl rcx, 32
	or rcx, rbx
	mov rdx, QWORD PTR [rax+4]
	movq xmm0, rcx
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rdi, 16
	add rbx, 1
	cmp rbx, rbp
	jne 20b
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, rbp
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks}
	mov rsi, r15
	add rsi, 488
	mov rdi, r15
	add rdi, 16
	mov rcx, rbp
21:
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+16]
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 32
	add rdi, 16
	sub rcx, 2
	jne 21b
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
	mov rcx, r15
	add rcx, 1768
	call {vg_aes_expand_key_scratch}
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	bswap rdx
	bswap rax
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+64], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+80], xmm0
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rdx, rcx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 22f
24:
	mov r14d, 64
	cmp rbx, r14
	jb 25f
	jmp 26f
25:
	mov r14, rbx
26:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
27:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 27b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
28:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 28b
	sub rbx, r14
	jne 24b
	jmp 23f
22:
23:
	test rbp, rbp
	je 29f
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
211:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 211b
	jmp 210f
29:
210:
	mov rax, QWORD PTR [r15+224]
	shr rax, 4
	mov rdx, QWORD PTR [r15+240]
	shr rdx, 4
	add rax, rdx
	cmp rax, 62
	jae 212f
	mov rdi, r15
	add rdi, 488
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 214f
	mov r14, rbx
	mov rcx, r14
216:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 216b
	jmp 215f
214:
215:
	test rbp, rbp
	je 217f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
219:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 219b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 218f
217:
218:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 220f
	mov r14, rbx
	mov rcx, r14
222:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 222b
	jmp 221f
220:
221:
	test rbp, rbp
	je 223f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
225:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 225b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 224f
223:
224:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	mov rcx, rdi
	sub rcx, r15
	shr rcx, 4
	sub rcx, 29
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	jmp 213f
212:
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 226f
228:
	mov r14d, 64
	cmp rbx, r14
	jb 229f
	jmp 230f
229:
	mov r14, rbx
230:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
231:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 231b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_pclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 228b
	jmp 227f
226:
227:
	test rbp, rbp
	je 232f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
234:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 234b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_pclmul}
	jmp 233f
232:
233:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 235f
237:
	mov r14d, 64
	cmp rbx, r14
	jb 238f
	jmp 239f
238:
	mov r14, rbx
239:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
240:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 240b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash_pclmul}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 237b
	jmp 236f
235:
236:
	test rbp, rbp
	je 241f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
243:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 243b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash_pclmul}
	jmp 242f
241:
242:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
213:
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32}
	mov rax, QWORD PTR [r15]
	xor rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+8]
	xor rdx, QWORD PTR [r15+136]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+192], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov r11d, 0
	sub r11, QWORD PTR [r15+192]
	mov r10d, 0
	mov rcx, rbp
	shr rcx, 4
	test rcx, rcx
	je 244f
	movq xmm0, r11
	punpcklqdq xmm0, xmm0
246:
	movdqu xmm1, XMMWORD PTR [r12+r10*1]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [r12+r10*1], xmm1
	add r10, 16
	sub rcx, 1
	jne 246b
	jmp 245f
244:
245:
	cmp r10, rbp
	je 247f
249:
	movzx eax, BYTE PTR [r12+r10*1]
	and rax, r11
	mov BYTE PTR [r12+r10*1], al
	add r10, 1
	cmp r10, rbp
	jne 249b
	jmp 248f
247:
248:
	mov rax, QWORD PTR [r15+192]
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	pxor xmm12, xmm12
	pxor xmm13, xmm13
	pxor xmm14, xmm14
	pxor xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-8]
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp-3848]
	movdqu XMMWORD PTR [rsp+3832], xmm0
	movdqu XMMWORD PTR [rsp+3816], xmm0
	movdqu XMMWORD PTR [rsp+3800], xmm0
	movdqu XMMWORD PTR [rsp+3784], xmm0
	movdqu XMMWORD PTR [rsp+3768], xmm0
	movdqu XMMWORD PTR [rsp+3752], xmm0
	movdqu XMMWORD PTR [rsp+3736], xmm0
	movdqu XMMWORD PTR [rsp+3720], xmm0
	movdqu XMMWORD PTR [rsp+3704], xmm0
	movdqu XMMWORD PTR [rsp+3688], xmm0
	movdqu XMMWORD PTR [rsp+3672], xmm0
	movdqu XMMWORD PTR [rsp+3656], xmm0
	movdqu XMMWORD PTR [rsp+3640], xmm0
	movdqu XMMWORD PTR [rsp+3624], xmm0
	movdqu XMMWORD PTR [rsp+3608], xmm0
	movdqu XMMWORD PTR [rsp+3592], xmm0
	movdqu XMMWORD PTR [rsp+3576], xmm0
	movdqu XMMWORD PTR [rsp+3560], xmm0
	movdqu XMMWORD PTR [rsp+3544], xmm0
	movdqu XMMWORD PTR [rsp+3528], xmm0
	movdqu XMMWORD PTR [rsp+3512], xmm0
	movdqu XMMWORD PTR [rsp+3496], xmm0
	movdqu XMMWORD PTR [rsp+3480], xmm0
	movdqu XMMWORD PTR [rsp+3464], xmm0
	movdqu XMMWORD PTR [rsp+3448], xmm0
	movdqu XMMWORD PTR [rsp+3432], xmm0
	movdqu XMMWORD PTR [rsp+3416], xmm0
	movdqu XMMWORD PTR [rsp+3400], xmm0
	movdqu XMMWORD PTR [rsp+3384], xmm0
	movdqu XMMWORD PTR [rsp+3368], xmm0
	movdqu XMMWORD PTR [rsp+3352], xmm0
	movdqu XMMWORD PTR [rsp+3336], xmm0
	movdqu XMMWORD PTR [rsp+3320], xmm0
	movdqu XMMWORD PTR [rsp+3304], xmm0
	movdqu XMMWORD PTR [rsp+3288], xmm0
	movdqu XMMWORD PTR [rsp+3272], xmm0
	movdqu XMMWORD PTR [rsp+3256], xmm0
	movdqu XMMWORD PTR [rsp+3240], xmm0
	movdqu XMMWORD PTR [rsp+3224], xmm0
	movdqu XMMWORD PTR [rsp+3208], xmm0
	movdqu XMMWORD PTR [rsp+3192], xmm0
	movdqu XMMWORD PTR [rsp+3176], xmm0
	movdqu XMMWORD PTR [rsp+3160], xmm0
	movdqu XMMWORD PTR [rsp+3144], xmm0
	movdqu XMMWORD PTR [rsp+3128], xmm0
	movdqu XMMWORD PTR [rsp+3112], xmm0
	movdqu XMMWORD PTR [rsp+3096], xmm0
	movdqu XMMWORD PTR [rsp+3080], xmm0
	movdqu XMMWORD PTR [rsp+3064], xmm0
	movdqu XMMWORD PTR [rsp+3048], xmm0
	movdqu XMMWORD PTR [rsp+3032], xmm0
	movdqu XMMWORD PTR [rsp+3016], xmm0
	movdqu XMMWORD PTR [rsp+3000], xmm0
	movdqu XMMWORD PTR [rsp+2984], xmm0
	movdqu XMMWORD PTR [rsp+2968], xmm0
	movdqu XMMWORD PTR [rsp+2952], xmm0
	movdqu XMMWORD PTR [rsp+2936], xmm0
	movdqu XMMWORD PTR [rsp+2920], xmm0
	movdqu XMMWORD PTR [rsp+2904], xmm0
	movdqu XMMWORD PTR [rsp+2888], xmm0
	movdqu XMMWORD PTR [rsp+2872], xmm0
	movdqu XMMWORD PTR [rsp+2856], xmm0
	movdqu XMMWORD PTR [rsp+2840], xmm0
	movdqu XMMWORD PTR [rsp+2824], xmm0
	movdqu XMMWORD PTR [rsp+2808], xmm0
	movdqu XMMWORD PTR [rsp+2792], xmm0
	movdqu XMMWORD PTR [rsp+2776], xmm0
	movdqu XMMWORD PTR [rsp+2760], xmm0
	movdqu XMMWORD PTR [rsp+2744], xmm0
	movdqu XMMWORD PTR [rsp+2728], xmm0
	movdqu XMMWORD PTR [rsp+2712], xmm0
	movdqu XMMWORD PTR [rsp+2696], xmm0
	movdqu XMMWORD PTR [rsp+2680], xmm0
	movdqu XMMWORD PTR [rsp+2664], xmm0
	movdqu XMMWORD PTR [rsp+2648], xmm0
	movdqu XMMWORD PTR [rsp+2632], xmm0
	movdqu XMMWORD PTR [rsp+2616], xmm0
	movdqu XMMWORD PTR [rsp+2600], xmm0
	movdqu XMMWORD PTR [rsp+2584], xmm0
	movdqu XMMWORD PTR [rsp+2568], xmm0
	movdqu XMMWORD PTR [rsp+2552], xmm0
	movdqu XMMWORD PTR [rsp+2536], xmm0
	movdqu XMMWORD PTR [rsp+2520], xmm0
	movdqu XMMWORD PTR [rsp+2504], xmm0
	movdqu XMMWORD PTR [rsp+2488], xmm0
	movdqu XMMWORD PTR [rsp+2472], xmm0
	movdqu XMMWORD PTR [rsp+2456], xmm0
	movdqu XMMWORD PTR [rsp+2440], xmm0
	movdqu XMMWORD PTR [rsp+2424], xmm0
	movdqu XMMWORD PTR [rsp+2408], xmm0
	movdqu XMMWORD PTR [rsp+2392], xmm0
	movdqu XMMWORD PTR [rsp+2376], xmm0
	movdqu XMMWORD PTR [rsp+2360], xmm0
	movdqu XMMWORD PTR [rsp+2344], xmm0
	movdqu XMMWORD PTR [rsp+2328], xmm0
	movdqu XMMWORD PTR [rsp+2312], xmm0
	movdqu XMMWORD PTR [rsp+2296], xmm0
	movdqu XMMWORD PTR [rsp+2280], xmm0
	movdqu XMMWORD PTR [rsp+2264], xmm0
	movdqu XMMWORD PTR [rsp+2248], xmm0
	movdqu XMMWORD PTR [rsp+2232], xmm0
	movdqu XMMWORD PTR [rsp+2216], xmm0
	movdqu XMMWORD PTR [rsp+2200], xmm0
	movdqu XMMWORD PTR [rsp+2184], xmm0
	movdqu XMMWORD PTR [rsp+2168], xmm0
	movdqu XMMWORD PTR [rsp+2152], xmm0
	movdqu XMMWORD PTR [rsp+2136], xmm0
	movdqu XMMWORD PTR [rsp+2120], xmm0
	movdqu XMMWORD PTR [rsp+2104], xmm0
	movdqu XMMWORD PTR [rsp+2088], xmm0
	movdqu XMMWORD PTR [rsp+2072], xmm0
	movdqu XMMWORD PTR [rsp+2056], xmm0
	movdqu XMMWORD PTR [rsp+2040], xmm0
	movdqu XMMWORD PTR [rsp+2024], xmm0
	movdqu XMMWORD PTR [rsp+2008], xmm0
	movdqu XMMWORD PTR [rsp+1992], xmm0
	movdqu XMMWORD PTR [rsp+1976], xmm0
	movdqu XMMWORD PTR [rsp+1960], xmm0
	movdqu XMMWORD PTR [rsp+1944], xmm0
	movdqu XMMWORD PTR [rsp+1928], xmm0
	movdqu XMMWORD PTR [rsp+1912], xmm0
	movdqu XMMWORD PTR [rsp+1896], xmm0
	movdqu XMMWORD PTR [rsp+1880], xmm0
	movdqu XMMWORD PTR [rsp+1864], xmm0
	movdqu XMMWORD PTR [rsp+1848], xmm0
	movdqu XMMWORD PTR [rsp+1832], xmm0
	movdqu XMMWORD PTR [rsp+1816], xmm0
	movdqu XMMWORD PTR [rsp+1800], xmm0
	movdqu XMMWORD PTR [rsp+1784], xmm0
	movdqu XMMWORD PTR [rsp+1768], xmm0
	movdqu XMMWORD PTR [rsp+1752], xmm0
	movdqu XMMWORD PTR [rsp+1736], xmm0
	movdqu XMMWORD PTR [rsp+1720], xmm0
	movdqu XMMWORD PTR [rsp+1704], xmm0
	movdqu XMMWORD PTR [rsp+1688], xmm0
	movdqu XMMWORD PTR [rsp+1672], xmm0
	movdqu XMMWORD PTR [rsp+1656], xmm0
	movdqu XMMWORD PTR [rsp+1640], xmm0
	movdqu XMMWORD PTR [rsp+1624], xmm0
	movdqu XMMWORD PTR [rsp+1608], xmm0
	movdqu XMMWORD PTR [rsp+1592], xmm0
	movdqu XMMWORD PTR [rsp+1576], xmm0
	movdqu XMMWORD PTR [rsp+1560], xmm0
	movdqu XMMWORD PTR [rsp+1544], xmm0
	movdqu XMMWORD PTR [rsp+1528], xmm0
	movdqu XMMWORD PTR [rsp+1512], xmm0
	movdqu XMMWORD PTR [rsp+1496], xmm0
	movdqu XMMWORD PTR [rsp+1480], xmm0
	movdqu XMMWORD PTR [rsp+1464], xmm0
	movdqu XMMWORD PTR [rsp+1448], xmm0
	movdqu XMMWORD PTR [rsp+1432], xmm0
	movdqu XMMWORD PTR [rsp+1416], xmm0
	movdqu XMMWORD PTR [rsp+1400], xmm0
	movdqu XMMWORD PTR [rsp+1384], xmm0
	movdqu XMMWORD PTR [rsp+1368], xmm0
	movdqu XMMWORD PTR [rsp+1352], xmm0
	movdqu XMMWORD PTR [rsp+1336], xmm0
	movdqu XMMWORD PTR [rsp+1320], xmm0
	movdqu XMMWORD PTR [rsp+1304], xmm0
	movdqu XMMWORD PTR [rsp+1288], xmm0
	movdqu XMMWORD PTR [rsp+1272], xmm0
	movdqu XMMWORD PTR [rsp+1256], xmm0
	movdqu XMMWORD PTR [rsp+1240], xmm0
	movdqu XMMWORD PTR [rsp+1224], xmm0
	movdqu XMMWORD PTR [rsp+1208], xmm0
	movdqu XMMWORD PTR [rsp+1192], xmm0
	movdqu XMMWORD PTR [rsp+1176], xmm0
	movdqu XMMWORD PTR [rsp+1160], xmm0
	movdqu XMMWORD PTR [rsp+1144], xmm0
	movdqu XMMWORD PTR [rsp+1128], xmm0
	movdqu XMMWORD PTR [rsp+1112], xmm0
	movdqu XMMWORD PTR [rsp+1096], xmm0
	movdqu XMMWORD PTR [rsp+1080], xmm0
	movdqu XMMWORD PTR [rsp+1064], xmm0
	movdqu XMMWORD PTR [rsp+1048], xmm0
	movdqu XMMWORD PTR [rsp+1032], xmm0
	movdqu XMMWORD PTR [rsp+1016], xmm0
	movdqu XMMWORD PTR [rsp+1000], xmm0
	movdqu XMMWORD PTR [rsp+984], xmm0
	movdqu XMMWORD PTR [rsp+968], xmm0
	movdqu XMMWORD PTR [rsp+952], xmm0
	movdqu XMMWORD PTR [rsp+936], xmm0
	movdqu XMMWORD PTR [rsp+920], xmm0
	movdqu XMMWORD PTR [rsp+904], xmm0
	movdqu XMMWORD PTR [rsp+888], xmm0
	movdqu XMMWORD PTR [rsp+872], xmm0
	movdqu XMMWORD PTR [rsp+856], xmm0
	movdqu XMMWORD PTR [rsp+840], xmm0
	movdqu XMMWORD PTR [rsp+824], xmm0
	movdqu XMMWORD PTR [rsp+808], xmm0
	movdqu XMMWORD PTR [rsp+792], xmm0
	movdqu XMMWORD PTR [rsp+776], xmm0
	movdqu XMMWORD PTR [rsp+760], xmm0
	movdqu XMMWORD PTR [rsp+744], xmm0
	movdqu XMMWORD PTR [rsp+728], xmm0
	movdqu XMMWORD PTR [rsp+712], xmm0
	movdqu XMMWORD PTR [rsp+696], xmm0
	movdqu XMMWORD PTR [rsp+680], xmm0
	movdqu XMMWORD PTR [rsp+664], xmm0
	movdqu XMMWORD PTR [rsp+648], xmm0
	movdqu XMMWORD PTR [rsp+632], xmm0
	movdqu XMMWORD PTR [rsp+616], xmm0
	movdqu XMMWORD PTR [rsp+600], xmm0
	movdqu XMMWORD PTR [rsp+584], xmm0
	movdqu XMMWORD PTR [rsp+568], xmm0
	movdqu XMMWORD PTR [rsp+552], xmm0
	movdqu XMMWORD PTR [rsp+536], xmm0
	movdqu XMMWORD PTR [rsp+520], xmm0
	movdqu XMMWORD PTR [rsp+504], xmm0
	movdqu XMMWORD PTR [rsp+488], xmm0
	movdqu XMMWORD PTR [rsp+472], xmm0
	movdqu XMMWORD PTR [rsp+456], xmm0
	movdqu XMMWORD PTR [rsp+440], xmm0
	movdqu XMMWORD PTR [rsp+424], xmm0
	movdqu XMMWORD PTR [rsp+408], xmm0
	movdqu XMMWORD PTR [rsp+392], xmm0
	movdqu XMMWORD PTR [rsp+376], xmm0
	movdqu XMMWORD PTR [rsp+360], xmm0
	movdqu XMMWORD PTR [rsp+344], xmm0
	movdqu XMMWORD PTR [rsp+328], xmm0
	movdqu XMMWORD PTR [rsp+312], xmm0
	movdqu XMMWORD PTR [rsp+296], xmm0
	movdqu XMMWORD PTR [rsp+280], xmm0
	movdqu XMMWORD PTR [rsp+264], xmm0
	movdqu XMMWORD PTR [rsp+248], xmm0
	movdqu XMMWORD PTR [rsp+232], xmm0
	movdqu XMMWORD PTR [rsp+216], xmm0
	movdqu XMMWORD PTR [rsp+200], xmm0
	movdqu XMMWORD PTR [rsp+184], xmm0
	movdqu XMMWORD PTR [rsp+168], xmm0
	movdqu XMMWORD PTR [rsp+152], xmm0
	movdqu XMMWORD PTR [rsp+136], xmm0
	movdqu XMMWORD PTR [rsp+120], xmm0
	movdqu XMMWORD PTR [rsp+104], xmm0
	movdqu XMMWORD PTR [rsp+88], xmm0
	movdqu XMMWORD PTR [rsp+72], xmm0
	movdqu XMMWORD PTR [rsp+56], xmm0
	movdqu XMMWORD PTR [rsp+40], xmm0
	movdqu XMMWORD PTR [rsp+24], xmm0
	movdqu XMMWORD PTR [rsp+8], xmm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+3848]
	lea rsp, [rsp+8]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6

vg_aes_gcm_siv_seal_avx2:
	mov rax, QWORD PTR [rsp+8]
	or rax, r8
	cmp rax, 128
	jae 20f
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov ebx, 0
	mov rdi, r15
	add rdi, 488
	mov rbp, QWORD PTR [r15+200]
	shr rbp, 1
	sub rbp, 1
22:
	mov rax, QWORD PTR [r15+208]
	mov ecx, DWORD PTR [rax]
	shl rcx, 32
	or rcx, rbx
	mov rdx, QWORD PTR [rax+4]
	movq xmm0, rcx
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rdi, 16
	add rbx, 1
	cmp rbx, rbp
	jne 22b
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, rbp
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks}
	mov rsi, r15
	add rsi, 488
	mov rdi, r15
	add rdi, 16
	mov rcx, rbp
23:
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+16]
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 32
	add rdi, 16
	sub rcx, 2
	jne 23b
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	bswap rdx
	bswap rax
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+64], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+80], xmm0
	mov rax, QWORD PTR [r15+224]
	shr rax, 4
	mov rdx, QWORD PTR [r15+240]
	shr rdx, 4
	add rax, rdx
	cmp rax, 62
	jae 24f
	mov rdi, r15
	add rdi, 488
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 26f
	mov r14, rbx
	mov rcx, r14
28:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 28b
	jmp 27f
26:
27:
	test rbp, rbp
	je 29f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
211:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 211b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 210f
29:
210:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 212f
	mov r14, rbx
	mov rcx, r14
214:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 214b
	jmp 213f
212:
213:
	test rbp, rbp
	je 215f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
217:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 217b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 216f
215:
216:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	mov rcx, rdi
	sub rcx, r15
	shr rcx, 4
	sub rcx, 29
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	call {vg_ghash}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	jmp 25f
24:
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 218f
220:
	mov r14d, 64
	cmp rbx, r14
	jb 221f
	jmp 222f
221:
	mov r14, rbx
222:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
223:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 223b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 220b
	jmp 219f
218:
219:
	test rbp, rbp
	je 224f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
226:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 226b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash}
	jmp 225f
224:
225:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 227f
229:
	mov r14d, 64
	cmp rbx, r14
	jb 230f
	jmp 231f
230:
	mov r14, rbx
231:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
232:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 232b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 229b
	jmp 228f
227:
228:
	test rbp, rbp
	je 233f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
235:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 235b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash}
	jmp 234f
233:
234:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
25:
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
	mov rcx, r15
	add rcx, 1768
	call {vg_aes_expand_key_scratch}
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 0
	call {vg_aes_ctr32}
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rdx, rcx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 236f
238:
	mov r14d, 64
	cmp rbx, r14
	jb 239f
	jmp 240f
239:
	mov r14, rbx
240:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
241:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 241b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
242:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 242b
	sub rbx, r14
	jne 238b
	jmp 237f
236:
237:
	test rbp, rbp
	je 243f
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
245:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 245b
	jmp 244f
243:
244:
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [rcx], rax
	mov rax, QWORD PTR [r15+8]
	mov QWORD PTR [rcx+8], rax
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
21:
	vpxor xmm0, xmm0, xmm0
	vpxor xmm1, xmm1, xmm1
	vpxor xmm2, xmm2, xmm2
	vpxor xmm3, xmm3, xmm3
	vpxor xmm4, xmm4, xmm4
	vpxor xmm5, xmm5, xmm5
	vpxor xmm6, xmm6, xmm6
	vpxor xmm7, xmm7, xmm7
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	vpxor xmm11, xmm11, xmm11
	vpxor xmm12, xmm12, xmm12
	vpxor xmm13, xmm13, xmm13
	vpxor xmm14, xmm14, xmm14
	vpxor xmm15, xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-8]
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp-3848]
	vmovdqu YMMWORD PTR [rsp+3816], ymm0
	vmovdqu YMMWORD PTR [rsp+3784], ymm0
	vmovdqu YMMWORD PTR [rsp+3752], ymm0
	vmovdqu YMMWORD PTR [rsp+3720], ymm0
	vmovdqu YMMWORD PTR [rsp+3688], ymm0
	vmovdqu YMMWORD PTR [rsp+3656], ymm0
	vmovdqu YMMWORD PTR [rsp+3624], ymm0
	vmovdqu YMMWORD PTR [rsp+3592], ymm0
	vmovdqu YMMWORD PTR [rsp+3560], ymm0
	vmovdqu YMMWORD PTR [rsp+3528], ymm0
	vmovdqu YMMWORD PTR [rsp+3496], ymm0
	vmovdqu YMMWORD PTR [rsp+3464], ymm0
	vmovdqu YMMWORD PTR [rsp+3432], ymm0
	vmovdqu YMMWORD PTR [rsp+3400], ymm0
	vmovdqu YMMWORD PTR [rsp+3368], ymm0
	vmovdqu YMMWORD PTR [rsp+3336], ymm0
	vmovdqu YMMWORD PTR [rsp+3304], ymm0
	vmovdqu YMMWORD PTR [rsp+3272], ymm0
	vmovdqu YMMWORD PTR [rsp+3240], ymm0
	vmovdqu YMMWORD PTR [rsp+3208], ymm0
	vmovdqu YMMWORD PTR [rsp+3176], ymm0
	vmovdqu YMMWORD PTR [rsp+3144], ymm0
	vmovdqu YMMWORD PTR [rsp+3112], ymm0
	vmovdqu YMMWORD PTR [rsp+3080], ymm0
	vmovdqu YMMWORD PTR [rsp+3048], ymm0
	vmovdqu YMMWORD PTR [rsp+3016], ymm0
	vmovdqu YMMWORD PTR [rsp+2984], ymm0
	vmovdqu YMMWORD PTR [rsp+2952], ymm0
	vmovdqu YMMWORD PTR [rsp+2920], ymm0
	vmovdqu YMMWORD PTR [rsp+2888], ymm0
	vmovdqu YMMWORD PTR [rsp+2856], ymm0
	vmovdqu YMMWORD PTR [rsp+2824], ymm0
	vmovdqu YMMWORD PTR [rsp+2792], ymm0
	vmovdqu YMMWORD PTR [rsp+2760], ymm0
	vmovdqu YMMWORD PTR [rsp+2728], ymm0
	vmovdqu YMMWORD PTR [rsp+2696], ymm0
	vmovdqu YMMWORD PTR [rsp+2664], ymm0
	vmovdqu YMMWORD PTR [rsp+2632], ymm0
	vmovdqu YMMWORD PTR [rsp+2600], ymm0
	vmovdqu YMMWORD PTR [rsp+2568], ymm0
	vmovdqu YMMWORD PTR [rsp+2536], ymm0
	vmovdqu YMMWORD PTR [rsp+2504], ymm0
	vmovdqu YMMWORD PTR [rsp+2472], ymm0
	vmovdqu YMMWORD PTR [rsp+2440], ymm0
	vmovdqu YMMWORD PTR [rsp+2408], ymm0
	vmovdqu YMMWORD PTR [rsp+2376], ymm0
	vmovdqu YMMWORD PTR [rsp+2344], ymm0
	vmovdqu YMMWORD PTR [rsp+2312], ymm0
	vmovdqu YMMWORD PTR [rsp+2280], ymm0
	vmovdqu YMMWORD PTR [rsp+2248], ymm0
	vmovdqu YMMWORD PTR [rsp+2216], ymm0
	vmovdqu YMMWORD PTR [rsp+2184], ymm0
	vmovdqu YMMWORD PTR [rsp+2152], ymm0
	vmovdqu YMMWORD PTR [rsp+2120], ymm0
	vmovdqu YMMWORD PTR [rsp+2088], ymm0
	vmovdqu YMMWORD PTR [rsp+2056], ymm0
	vmovdqu YMMWORD PTR [rsp+2024], ymm0
	vmovdqu YMMWORD PTR [rsp+1992], ymm0
	vmovdqu YMMWORD PTR [rsp+1960], ymm0
	vmovdqu YMMWORD PTR [rsp+1928], ymm0
	vmovdqu YMMWORD PTR [rsp+1896], ymm0
	vmovdqu YMMWORD PTR [rsp+1864], ymm0
	vmovdqu YMMWORD PTR [rsp+1832], ymm0
	vmovdqu YMMWORD PTR [rsp+1800], ymm0
	vmovdqu YMMWORD PTR [rsp+1768], ymm0
	vmovdqu YMMWORD PTR [rsp+1736], ymm0
	vmovdqu YMMWORD PTR [rsp+1704], ymm0
	vmovdqu YMMWORD PTR [rsp+1672], ymm0
	vmovdqu YMMWORD PTR [rsp+1640], ymm0
	vmovdqu YMMWORD PTR [rsp+1608], ymm0
	vmovdqu YMMWORD PTR [rsp+1576], ymm0
	vmovdqu YMMWORD PTR [rsp+1544], ymm0
	vmovdqu YMMWORD PTR [rsp+1512], ymm0
	vmovdqu YMMWORD PTR [rsp+1480], ymm0
	vmovdqu YMMWORD PTR [rsp+1448], ymm0
	vmovdqu YMMWORD PTR [rsp+1416], ymm0
	vmovdqu YMMWORD PTR [rsp+1384], ymm0
	vmovdqu YMMWORD PTR [rsp+1352], ymm0
	vmovdqu YMMWORD PTR [rsp+1320], ymm0
	vmovdqu YMMWORD PTR [rsp+1288], ymm0
	vmovdqu YMMWORD PTR [rsp+1256], ymm0
	vmovdqu YMMWORD PTR [rsp+1224], ymm0
	vmovdqu YMMWORD PTR [rsp+1192], ymm0
	vmovdqu YMMWORD PTR [rsp+1160], ymm0
	vmovdqu YMMWORD PTR [rsp+1128], ymm0
	vmovdqu YMMWORD PTR [rsp+1096], ymm0
	vmovdqu YMMWORD PTR [rsp+1064], ymm0
	vmovdqu YMMWORD PTR [rsp+1032], ymm0
	vmovdqu YMMWORD PTR [rsp+1000], ymm0
	vmovdqu YMMWORD PTR [rsp+968], ymm0
	vmovdqu YMMWORD PTR [rsp+936], ymm0
	vmovdqu YMMWORD PTR [rsp+904], ymm0
	vmovdqu YMMWORD PTR [rsp+872], ymm0
	vmovdqu YMMWORD PTR [rsp+840], ymm0
	vmovdqu YMMWORD PTR [rsp+808], ymm0
	vmovdqu YMMWORD PTR [rsp+776], ymm0
	vmovdqu YMMWORD PTR [rsp+744], ymm0
	vmovdqu YMMWORD PTR [rsp+712], ymm0
	vmovdqu YMMWORD PTR [rsp+680], ymm0
	vmovdqu YMMWORD PTR [rsp+648], ymm0
	vmovdqu YMMWORD PTR [rsp+616], ymm0
	vmovdqu YMMWORD PTR [rsp+584], ymm0
	vmovdqu YMMWORD PTR [rsp+552], ymm0
	vmovdqu YMMWORD PTR [rsp+520], ymm0
	vmovdqu YMMWORD PTR [rsp+488], ymm0
	vmovdqu YMMWORD PTR [rsp+456], ymm0
	vmovdqu YMMWORD PTR [rsp+424], ymm0
	vmovdqu YMMWORD PTR [rsp+392], ymm0
	vmovdqu YMMWORD PTR [rsp+360], ymm0
	vmovdqu YMMWORD PTR [rsp+328], ymm0
	vmovdqu YMMWORD PTR [rsp+296], ymm0
	vmovdqu YMMWORD PTR [rsp+264], ymm0
	vmovdqu YMMWORD PTR [rsp+232], ymm0
	vmovdqu YMMWORD PTR [rsp+200], ymm0
	vmovdqu YMMWORD PTR [rsp+168], ymm0
	vmovdqu YMMWORD PTR [rsp+136], ymm0
	vmovdqu YMMWORD PTR [rsp+104], ymm0
	vmovdqu YMMWORD PTR [rsp+72], ymm0
	vmovdqu YMMWORD PTR [rsp+40], ymm0
	vmovdqu YMMWORD PTR [rsp+8], ymm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+3848]
	lea rsp, [rsp+8]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
20:
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov ebx, 0
	mov rdi, r15
	add rdi, 488
	mov rbp, QWORD PTR [r15+200]
	shr rbp, 1
	sub rbp, 1
246:
	mov rax, QWORD PTR [r15+208]
	mov ecx, DWORD PTR [rax]
	shl rcx, 32
	or rcx, rbx
	mov rdx, QWORD PTR [rax+4]
	movq xmm0, rcx
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rdi, 16
	add rbx, 1
	cmp rbx, rbp
	jne 246b
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, rbp
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks}
	mov rsi, r15
	add rsi, 488
	mov rdi, r15
	add rdi, 16
	mov rcx, rbp
247:
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+16]
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 32
	add rdi, 16
	sub rcx, 2
	jne 247b
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	bswap rdx
	bswap rax
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+64], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+80], xmm0
	mov rax, QWORD PTR [r15+224]
	shr rax, 4
	mov rdx, QWORD PTR [r15+240]
	shr rdx, 4
	add rax, rdx
	cmp rax, 62
	jae 248f
	mov rdi, r15
	add rdi, 488
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 250f
	mov r14, rbx
	mov rcx, r14
	cmp rcx, 8
	jb 252f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
254:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 254b
	vzeroupper
	test rcx, rcx
	je 255f
257:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 257b
	jmp 256f
255:
256:
	jmp 253f
252:
258:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 258b
253:
	jmp 251f
250:
251:
	test rbp, rbp
	je 259f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
261:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 261b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 260f
259:
260:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 262f
	mov r14, rbx
	mov rcx, r14
	cmp rcx, 8
	jb 264f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
266:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 266b
	vzeroupper
	test rcx, rcx
	je 267f
269:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 269b
	jmp 268f
267:
268:
	jmp 265f
264:
270:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 270b
265:
	jmp 263f
262:
263:
	test rbp, rbp
	je 271f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
273:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 273b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 272f
271:
272:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	mov rcx, rdi
	sub rcx, r15
	shr rcx, 4
	sub rcx, 29
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	call {vg_ghash}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	jmp 249f
248:
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 274f
276:
	mov r14d, 64
	cmp rbx, r14
	jb 277f
	jmp 278f
277:
	mov r14, rbx
278:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 279f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
281:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 281b
	vzeroupper
	test rcx, rcx
	je 282f
284:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 284b
	jmp 283f
282:
283:
	jmp 280f
279:
285:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 285b
280:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 276b
	jmp 275f
274:
275:
	test rbp, rbp
	je 286f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
288:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 288b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash}
	jmp 287f
286:
287:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 289f
291:
	mov r14d, 64
	cmp rbx, r14
	jb 292f
	jmp 293f
292:
	mov r14, rbx
293:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 294f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
296:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 296b
	vzeroupper
	test rcx, rcx
	je 297f
299:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 299b
	jmp 298f
297:
298:
	jmp 295f
294:
2100:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2100b
295:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 291b
	jmp 290f
289:
290:
	test rbp, rbp
	je 2101f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
2103:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2103b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash}
	jmp 2102f
2101:
2102:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
249:
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
	mov rcx, r15
	add rcx, 1768
	call {vg_aes_expand_key_scratch}
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 0
	call {vg_aes_ctr32}
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rdx, rcx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 2104f
2106:
	mov r14d, 64
	cmp rbx, r14
	jb 2107f
	jmp 2108f
2107:
	mov r14, rbx
2108:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
2109:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 2109b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
	cmp rcx, 8
	jb 2110f
2112:
	vmovdqu ymm1, YMMWORD PTR [rsi]
	vmovdqu ymm0, YMMWORD PTR [r12]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12], ymm1
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vmovdqu ymm0, YMMWORD PTR [r12+32]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12+32], ymm1
	add r12, 64
	add rsi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 2112b
	vzeroupper
	test rcx, rcx
	je 2113f
2115:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 2115b
	jmp 2114f
2113:
2114:
	jmp 2111f
2110:
2116:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 2116b
2111:
	sub rbx, r14
	jne 2106b
	jmp 2105f
2104:
2105:
	test rbp, rbp
	je 2117f
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
2119:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2119b
	jmp 2118f
2117:
2118:
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [rcx], rax
	mov rax, QWORD PTR [r15+8]
	mov QWORD PTR [rcx+8], rax
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
	jmp 21b
	.p2align 6

vg_aes_gcm_siv_open_avx2:
	mov rax, QWORD PTR [rsp+8]
	or rax, r8
	cmp rax, 128
	jae 20f
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+8], rax
	mov ebx, 0
	mov rdi, r15
	add rdi, 488
	mov rbp, QWORD PTR [r15+200]
	shr rbp, 1
	sub rbp, 1
22:
	mov rax, QWORD PTR [r15+208]
	mov ecx, DWORD PTR [rax]
	shl rcx, 32
	or rcx, rbx
	mov rdx, QWORD PTR [rax+4]
	movq xmm0, rcx
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rdi, 16
	add rbx, 1
	cmp rbx, rbp
	jne 22b
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, rbp
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks}
	mov rsi, r15
	add rsi, 488
	mov rdi, r15
	add rdi, 16
	mov rcx, rbp
23:
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+16]
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 32
	add rdi, 16
	sub rcx, 2
	jne 23b
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
	mov rcx, r15
	add rcx, 1768
	call {vg_aes_expand_key_scratch}
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	bswap rdx
	bswap rax
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+64], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+80], xmm0
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rdx, rcx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 24f
26:
	mov r14d, 64
	cmp rbx, r14
	jb 27f
	jmp 28f
27:
	mov r14, rbx
28:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
29:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 29b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
210:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 210b
	sub rbx, r14
	jne 26b
	jmp 25f
24:
25:
	test rbp, rbp
	je 211f
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
213:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 213b
	jmp 212f
211:
212:
	mov rax, QWORD PTR [r15+224]
	shr rax, 4
	mov rdx, QWORD PTR [r15+240]
	shr rdx, 4
	add rax, rdx
	cmp rax, 62
	jae 214f
	mov rdi, r15
	add rdi, 488
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 216f
	mov r14, rbx
	mov rcx, r14
218:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 218b
	jmp 217f
216:
217:
	test rbp, rbp
	je 219f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
221:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 221b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 220f
219:
220:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 222f
	mov r14, rbx
	mov rcx, r14
224:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 224b
	jmp 223f
222:
223:
	test rbp, rbp
	je 225f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
227:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 227b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 226f
225:
226:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	mov rcx, rdi
	sub rcx, r15
	shr rcx, 4
	sub rcx, 29
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	call {vg_ghash}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	jmp 215f
214:
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 228f
230:
	mov r14d, 64
	cmp rbx, r14
	jb 231f
	jmp 232f
231:
	mov r14, rbx
232:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
233:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 233b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 230b
	jmp 229f
228:
229:
	test rbp, rbp
	je 234f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
236:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 236b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash}
	jmp 235f
234:
235:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 237f
239:
	mov r14d, 64
	cmp rbx, r14
	jb 240f
	jmp 241f
240:
	mov r14, rbx
241:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
242:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 242b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 239b
	jmp 238f
237:
238:
	test rbp, rbp
	je 243f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
245:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 245b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash}
	jmp 244f
243:
244:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
215:
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32}
	mov rax, QWORD PTR [r15]
	xor rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+8]
	xor rdx, QWORD PTR [r15+136]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+192], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov r11d, 0
	sub r11, QWORD PTR [r15+192]
	mov r10d, 0
	mov rcx, rbp
	shr rcx, 4
	test rcx, rcx
	je 246f
	movq xmm0, r11
	punpcklqdq xmm0, xmm0
248:
	movdqu xmm1, XMMWORD PTR [r12+r10*1]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [r12+r10*1], xmm1
	add r10, 16
	sub rcx, 1
	jne 248b
	jmp 247f
246:
247:
	cmp r10, rbp
	je 249f
251:
	movzx eax, BYTE PTR [r12+r10*1]
	and rax, r11
	mov BYTE PTR [r12+r10*1], al
	add r10, 1
	cmp r10, rbp
	jne 251b
	jmp 250f
249:
250:
	mov rax, QWORD PTR [r15+192]
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
21:
	vpxor xmm0, xmm0, xmm0
	vpxor xmm1, xmm1, xmm1
	vpxor xmm2, xmm2, xmm2
	vpxor xmm3, xmm3, xmm3
	vpxor xmm4, xmm4, xmm4
	vpxor xmm5, xmm5, xmm5
	vpxor xmm6, xmm6, xmm6
	vpxor xmm7, xmm7, xmm7
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	vpxor xmm11, xmm11, xmm11
	vpxor xmm12, xmm12, xmm12
	vpxor xmm13, xmm13, xmm13
	vpxor xmm14, xmm14, xmm14
	vpxor xmm15, xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-8]
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp-3848]
	vmovdqu YMMWORD PTR [rsp+3816], ymm0
	vmovdqu YMMWORD PTR [rsp+3784], ymm0
	vmovdqu YMMWORD PTR [rsp+3752], ymm0
	vmovdqu YMMWORD PTR [rsp+3720], ymm0
	vmovdqu YMMWORD PTR [rsp+3688], ymm0
	vmovdqu YMMWORD PTR [rsp+3656], ymm0
	vmovdqu YMMWORD PTR [rsp+3624], ymm0
	vmovdqu YMMWORD PTR [rsp+3592], ymm0
	vmovdqu YMMWORD PTR [rsp+3560], ymm0
	vmovdqu YMMWORD PTR [rsp+3528], ymm0
	vmovdqu YMMWORD PTR [rsp+3496], ymm0
	vmovdqu YMMWORD PTR [rsp+3464], ymm0
	vmovdqu YMMWORD PTR [rsp+3432], ymm0
	vmovdqu YMMWORD PTR [rsp+3400], ymm0
	vmovdqu YMMWORD PTR [rsp+3368], ymm0
	vmovdqu YMMWORD PTR [rsp+3336], ymm0
	vmovdqu YMMWORD PTR [rsp+3304], ymm0
	vmovdqu YMMWORD PTR [rsp+3272], ymm0
	vmovdqu YMMWORD PTR [rsp+3240], ymm0
	vmovdqu YMMWORD PTR [rsp+3208], ymm0
	vmovdqu YMMWORD PTR [rsp+3176], ymm0
	vmovdqu YMMWORD PTR [rsp+3144], ymm0
	vmovdqu YMMWORD PTR [rsp+3112], ymm0
	vmovdqu YMMWORD PTR [rsp+3080], ymm0
	vmovdqu YMMWORD PTR [rsp+3048], ymm0
	vmovdqu YMMWORD PTR [rsp+3016], ymm0
	vmovdqu YMMWORD PTR [rsp+2984], ymm0
	vmovdqu YMMWORD PTR [rsp+2952], ymm0
	vmovdqu YMMWORD PTR [rsp+2920], ymm0
	vmovdqu YMMWORD PTR [rsp+2888], ymm0
	vmovdqu YMMWORD PTR [rsp+2856], ymm0
	vmovdqu YMMWORD PTR [rsp+2824], ymm0
	vmovdqu YMMWORD PTR [rsp+2792], ymm0
	vmovdqu YMMWORD PTR [rsp+2760], ymm0
	vmovdqu YMMWORD PTR [rsp+2728], ymm0
	vmovdqu YMMWORD PTR [rsp+2696], ymm0
	vmovdqu YMMWORD PTR [rsp+2664], ymm0
	vmovdqu YMMWORD PTR [rsp+2632], ymm0
	vmovdqu YMMWORD PTR [rsp+2600], ymm0
	vmovdqu YMMWORD PTR [rsp+2568], ymm0
	vmovdqu YMMWORD PTR [rsp+2536], ymm0
	vmovdqu YMMWORD PTR [rsp+2504], ymm0
	vmovdqu YMMWORD PTR [rsp+2472], ymm0
	vmovdqu YMMWORD PTR [rsp+2440], ymm0
	vmovdqu YMMWORD PTR [rsp+2408], ymm0
	vmovdqu YMMWORD PTR [rsp+2376], ymm0
	vmovdqu YMMWORD PTR [rsp+2344], ymm0
	vmovdqu YMMWORD PTR [rsp+2312], ymm0
	vmovdqu YMMWORD PTR [rsp+2280], ymm0
	vmovdqu YMMWORD PTR [rsp+2248], ymm0
	vmovdqu YMMWORD PTR [rsp+2216], ymm0
	vmovdqu YMMWORD PTR [rsp+2184], ymm0
	vmovdqu YMMWORD PTR [rsp+2152], ymm0
	vmovdqu YMMWORD PTR [rsp+2120], ymm0
	vmovdqu YMMWORD PTR [rsp+2088], ymm0
	vmovdqu YMMWORD PTR [rsp+2056], ymm0
	vmovdqu YMMWORD PTR [rsp+2024], ymm0
	vmovdqu YMMWORD PTR [rsp+1992], ymm0
	vmovdqu YMMWORD PTR [rsp+1960], ymm0
	vmovdqu YMMWORD PTR [rsp+1928], ymm0
	vmovdqu YMMWORD PTR [rsp+1896], ymm0
	vmovdqu YMMWORD PTR [rsp+1864], ymm0
	vmovdqu YMMWORD PTR [rsp+1832], ymm0
	vmovdqu YMMWORD PTR [rsp+1800], ymm0
	vmovdqu YMMWORD PTR [rsp+1768], ymm0
	vmovdqu YMMWORD PTR [rsp+1736], ymm0
	vmovdqu YMMWORD PTR [rsp+1704], ymm0
	vmovdqu YMMWORD PTR [rsp+1672], ymm0
	vmovdqu YMMWORD PTR [rsp+1640], ymm0
	vmovdqu YMMWORD PTR [rsp+1608], ymm0
	vmovdqu YMMWORD PTR [rsp+1576], ymm0
	vmovdqu YMMWORD PTR [rsp+1544], ymm0
	vmovdqu YMMWORD PTR [rsp+1512], ymm0
	vmovdqu YMMWORD PTR [rsp+1480], ymm0
	vmovdqu YMMWORD PTR [rsp+1448], ymm0
	vmovdqu YMMWORD PTR [rsp+1416], ymm0
	vmovdqu YMMWORD PTR [rsp+1384], ymm0
	vmovdqu YMMWORD PTR [rsp+1352], ymm0
	vmovdqu YMMWORD PTR [rsp+1320], ymm0
	vmovdqu YMMWORD PTR [rsp+1288], ymm0
	vmovdqu YMMWORD PTR [rsp+1256], ymm0
	vmovdqu YMMWORD PTR [rsp+1224], ymm0
	vmovdqu YMMWORD PTR [rsp+1192], ymm0
	vmovdqu YMMWORD PTR [rsp+1160], ymm0
	vmovdqu YMMWORD PTR [rsp+1128], ymm0
	vmovdqu YMMWORD PTR [rsp+1096], ymm0
	vmovdqu YMMWORD PTR [rsp+1064], ymm0
	vmovdqu YMMWORD PTR [rsp+1032], ymm0
	vmovdqu YMMWORD PTR [rsp+1000], ymm0
	vmovdqu YMMWORD PTR [rsp+968], ymm0
	vmovdqu YMMWORD PTR [rsp+936], ymm0
	vmovdqu YMMWORD PTR [rsp+904], ymm0
	vmovdqu YMMWORD PTR [rsp+872], ymm0
	vmovdqu YMMWORD PTR [rsp+840], ymm0
	vmovdqu YMMWORD PTR [rsp+808], ymm0
	vmovdqu YMMWORD PTR [rsp+776], ymm0
	vmovdqu YMMWORD PTR [rsp+744], ymm0
	vmovdqu YMMWORD PTR [rsp+712], ymm0
	vmovdqu YMMWORD PTR [rsp+680], ymm0
	vmovdqu YMMWORD PTR [rsp+648], ymm0
	vmovdqu YMMWORD PTR [rsp+616], ymm0
	vmovdqu YMMWORD PTR [rsp+584], ymm0
	vmovdqu YMMWORD PTR [rsp+552], ymm0
	vmovdqu YMMWORD PTR [rsp+520], ymm0
	vmovdqu YMMWORD PTR [rsp+488], ymm0
	vmovdqu YMMWORD PTR [rsp+456], ymm0
	vmovdqu YMMWORD PTR [rsp+424], ymm0
	vmovdqu YMMWORD PTR [rsp+392], ymm0
	vmovdqu YMMWORD PTR [rsp+360], ymm0
	vmovdqu YMMWORD PTR [rsp+328], ymm0
	vmovdqu YMMWORD PTR [rsp+296], ymm0
	vmovdqu YMMWORD PTR [rsp+264], ymm0
	vmovdqu YMMWORD PTR [rsp+232], ymm0
	vmovdqu YMMWORD PTR [rsp+200], ymm0
	vmovdqu YMMWORD PTR [rsp+168], ymm0
	vmovdqu YMMWORD PTR [rsp+136], ymm0
	vmovdqu YMMWORD PTR [rsp+104], ymm0
	vmovdqu YMMWORD PTR [rsp+72], ymm0
	vmovdqu YMMWORD PTR [rsp+40], ymm0
	vmovdqu YMMWORD PTR [rsp+8], ymm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+3848]
	lea rsp, [rsp+8]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
20:
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+8], rax
	mov ebx, 0
	mov rdi, r15
	add rdi, 488
	mov rbp, QWORD PTR [r15+200]
	shr rbp, 1
	sub rbp, 1
252:
	mov rax, QWORD PTR [r15+208]
	mov ecx, DWORD PTR [rax]
	shl rcx, 32
	or rcx, rbx
	mov rdx, QWORD PTR [rax+4]
	movq xmm0, rcx
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rdi, 16
	add rbx, 1
	cmp rbx, rbp
	jne 252b
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, rbp
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks}
	mov rsi, r15
	add rsi, 488
	mov rdi, r15
	add rdi, 16
	mov rcx, rbp
253:
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+16]
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 32
	add rdi, 16
	sub rcx, 2
	jne 253b
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
	mov rcx, r15
	add rcx, 1768
	call {vg_aes_expand_key_scratch}
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	bswap rdx
	bswap rax
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+64], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+80], xmm0
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rdx, rcx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 254f
256:
	mov r14d, 64
	cmp rbx, r14
	jb 257f
	jmp 258f
257:
	mov r14, rbx
258:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
259:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 259b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
	cmp rcx, 8
	jb 260f
262:
	vmovdqu ymm1, YMMWORD PTR [rsi]
	vmovdqu ymm0, YMMWORD PTR [r12]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12], ymm1
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vmovdqu ymm0, YMMWORD PTR [r12+32]
	vpxor ymm1, ymm1, ymm0
	vmovdqu YMMWORD PTR [r12+32], ymm1
	add r12, 64
	add rsi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 262b
	vzeroupper
	test rcx, rcx
	je 263f
265:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 265b
	jmp 264f
263:
264:
	jmp 261f
260:
266:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 266b
261:
	sub rbx, r14
	jne 256b
	jmp 255f
254:
255:
	test rbp, rbp
	je 267f
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
269:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 269b
	jmp 268f
267:
268:
	mov rax, QWORD PTR [r15+224]
	shr rax, 4
	mov rdx, QWORD PTR [r15+240]
	shr rdx, 4
	add rax, rdx
	cmp rax, 62
	jae 270f
	mov rdi, r15
	add rdi, 488
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 272f
	mov r14, rbx
	mov rcx, r14
	cmp rcx, 8
	jb 274f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
276:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 276b
	vzeroupper
	test rcx, rcx
	je 277f
279:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 279b
	jmp 278f
277:
278:
	jmp 275f
274:
280:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 280b
275:
	jmp 273f
272:
273:
	test rbp, rbp
	je 281f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
283:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 283b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 282f
281:
282:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 284f
	mov r14, rbx
	mov rcx, r14
	cmp rcx, 8
	jb 286f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
288:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 288b
	vzeroupper
	test rcx, rcx
	je 289f
291:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 291b
	jmp 290f
289:
290:
	jmp 287f
286:
292:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 292b
287:
	jmp 285f
284:
285:
	test rbp, rbp
	je 293f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
295:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 295b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 294f
293:
294:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	mov rcx, rdi
	sub rcx, r15
	shr rcx, 4
	sub rcx, 29
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	call {vg_ghash}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	jmp 271f
270:
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 296f
298:
	mov r14d, 64
	cmp rbx, r14
	jb 299f
	jmp 2100f
299:
	mov r14, rbx
2100:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 2101f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
2103:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 2103b
	vzeroupper
	test rcx, rcx
	je 2104f
2106:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2106b
	jmp 2105f
2104:
2105:
	jmp 2102f
2101:
2107:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2107b
2102:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 298b
	jmp 297f
296:
297:
	test rbp, rbp
	je 2108f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
2110:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2110b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash}
	jmp 2109f
2108:
2109:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 2111f
2113:
	mov r14d, 64
	cmp rbx, r14
	jb 2114f
	jmp 2115f
2114:
	mov r14, rbx
2115:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
	cmp rcx, 8
	jb 2116f
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax]
	vinserti128 ymm1, ymm1, xmm1, 1
2118:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+32]
	vpshufb ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rsi, 64
	add rdi, 64
	sub rcx, 4
	cmp rcx, 4
	jae 2118b
	vzeroupper
	test rcx, rcx
	je 2119f
2121:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2121b
	jmp 2120f
2119:
2120:
	jmp 2117f
2116:
2122:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 2122b
2117:
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 2113b
	jmp 2112f
2111:
2112:
	test rbp, rbp
	je 2123f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
2125:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2125b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash}
	jmp 2124f
2123:
2124:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
271:
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32}
	mov rax, QWORD PTR [r15]
	xor rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+8]
	xor rdx, QWORD PTR [r15+136]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+192], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov r11d, 0
	sub r11, QWORD PTR [r15+192]
	mov r10d, 0
	mov rcx, rbp
	shr rcx, 4
	test rcx, rcx
	je 2126f
	movq xmm0, r11
	punpcklqdq xmm0, xmm0
2128:
	movdqu xmm1, XMMWORD PTR [r12+r10*1]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [r12+r10*1], xmm1
	add r10, 16
	sub rcx, 1
	jne 2128b
	jmp 2127f
2126:
2127:
	cmp r10, rbp
	je 2129f
2131:
	movzx eax, BYTE PTR [r12+r10*1]
	and rax, r11
	mov BYTE PTR [r12+r10*1], al
	add r10, 1
	cmp r10, rbp
	jne 2131b
	jmp 2130f
2129:
2130:
	mov rax, QWORD PTR [r15+192]
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
	jmp 21b
	.p2align 6

vg_aes_gcm_siv_seal:
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov ebx, 0
	mov rdi, r15
	add rdi, 488
	mov rbp, QWORD PTR [r15+200]
	shr rbp, 1
	sub rbp, 1
20:
	mov rax, QWORD PTR [r15+208]
	mov ecx, DWORD PTR [rax]
	shl rcx, 32
	or rcx, rbx
	mov rdx, QWORD PTR [rax+4]
	movq xmm0, rcx
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rdi, 16
	add rbx, 1
	cmp rbx, rbp
	jne 20b
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, rbp
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks}
	mov rsi, r15
	add rsi, 488
	mov rdi, r15
	add rdi, 16
	mov rcx, rbp
21:
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+16]
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 32
	add rdi, 16
	sub rcx, 2
	jne 21b
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	bswap rdx
	bswap rax
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+64], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+80], xmm0
	mov rax, QWORD PTR [r15+224]
	shr rax, 4
	mov rdx, QWORD PTR [r15+240]
	shr rdx, 4
	add rax, rdx
	cmp rax, 62
	jae 22f
	mov rdi, r15
	add rdi, 488
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 24f
	mov r14, rbx
	mov rcx, r14
26:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 26b
	jmp 25f
24:
25:
	test rbp, rbp
	je 27f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
29:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 29b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 28f
27:
28:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 210f
	mov r14, rbx
	mov rcx, r14
212:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 212b
	jmp 211f
210:
211:
	test rbp, rbp
	je 213f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
215:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 215b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 214f
213:
214:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	mov rcx, rdi
	sub rcx, r15
	shr rcx, 4
	sub rcx, 29
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	call {vg_ghash}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	jmp 23f
22:
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 216f
218:
	mov r14d, 64
	cmp rbx, r14
	jb 219f
	jmp 220f
219:
	mov r14, rbx
220:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
221:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 221b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 218b
	jmp 217f
216:
217:
	test rbp, rbp
	je 222f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
224:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 224b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash}
	jmp 223f
222:
223:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 225f
227:
	mov r14d, 64
	cmp rbx, r14
	jb 228f
	jmp 229f
228:
	mov r14, rbx
229:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
230:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 230b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 227b
	jmp 226f
225:
226:
	test rbp, rbp
	je 231f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
233:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 233b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash}
	jmp 232f
231:
232:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
23:
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
	mov rcx, r15
	add rcx, 1768
	call {vg_aes_expand_key_scratch}
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 0
	call {vg_aes_ctr32}
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rdx, rcx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 234f
236:
	mov r14d, 64
	cmp rbx, r14
	jb 237f
	jmp 238f
237:
	mov r14, rbx
238:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
239:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 239b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
240:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 240b
	sub rbx, r14
	jne 236b
	jmp 235f
234:
235:
	test rbp, rbp
	je 241f
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
243:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 243b
	jmp 242f
241:
242:
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [r15]
	mov QWORD PTR [rcx], rax
	mov rax, QWORD PTR [r15+8]
	mov QWORD PTR [rcx+8], rax
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	pxor xmm12, xmm12
	pxor xmm13, xmm13
	pxor xmm14, xmm14
	pxor xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-8]
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp-3848]
	movdqu XMMWORD PTR [rsp+3832], xmm0
	movdqu XMMWORD PTR [rsp+3816], xmm0
	movdqu XMMWORD PTR [rsp+3800], xmm0
	movdqu XMMWORD PTR [rsp+3784], xmm0
	movdqu XMMWORD PTR [rsp+3768], xmm0
	movdqu XMMWORD PTR [rsp+3752], xmm0
	movdqu XMMWORD PTR [rsp+3736], xmm0
	movdqu XMMWORD PTR [rsp+3720], xmm0
	movdqu XMMWORD PTR [rsp+3704], xmm0
	movdqu XMMWORD PTR [rsp+3688], xmm0
	movdqu XMMWORD PTR [rsp+3672], xmm0
	movdqu XMMWORD PTR [rsp+3656], xmm0
	movdqu XMMWORD PTR [rsp+3640], xmm0
	movdqu XMMWORD PTR [rsp+3624], xmm0
	movdqu XMMWORD PTR [rsp+3608], xmm0
	movdqu XMMWORD PTR [rsp+3592], xmm0
	movdqu XMMWORD PTR [rsp+3576], xmm0
	movdqu XMMWORD PTR [rsp+3560], xmm0
	movdqu XMMWORD PTR [rsp+3544], xmm0
	movdqu XMMWORD PTR [rsp+3528], xmm0
	movdqu XMMWORD PTR [rsp+3512], xmm0
	movdqu XMMWORD PTR [rsp+3496], xmm0
	movdqu XMMWORD PTR [rsp+3480], xmm0
	movdqu XMMWORD PTR [rsp+3464], xmm0
	movdqu XMMWORD PTR [rsp+3448], xmm0
	movdqu XMMWORD PTR [rsp+3432], xmm0
	movdqu XMMWORD PTR [rsp+3416], xmm0
	movdqu XMMWORD PTR [rsp+3400], xmm0
	movdqu XMMWORD PTR [rsp+3384], xmm0
	movdqu XMMWORD PTR [rsp+3368], xmm0
	movdqu XMMWORD PTR [rsp+3352], xmm0
	movdqu XMMWORD PTR [rsp+3336], xmm0
	movdqu XMMWORD PTR [rsp+3320], xmm0
	movdqu XMMWORD PTR [rsp+3304], xmm0
	movdqu XMMWORD PTR [rsp+3288], xmm0
	movdqu XMMWORD PTR [rsp+3272], xmm0
	movdqu XMMWORD PTR [rsp+3256], xmm0
	movdqu XMMWORD PTR [rsp+3240], xmm0
	movdqu XMMWORD PTR [rsp+3224], xmm0
	movdqu XMMWORD PTR [rsp+3208], xmm0
	movdqu XMMWORD PTR [rsp+3192], xmm0
	movdqu XMMWORD PTR [rsp+3176], xmm0
	movdqu XMMWORD PTR [rsp+3160], xmm0
	movdqu XMMWORD PTR [rsp+3144], xmm0
	movdqu XMMWORD PTR [rsp+3128], xmm0
	movdqu XMMWORD PTR [rsp+3112], xmm0
	movdqu XMMWORD PTR [rsp+3096], xmm0
	movdqu XMMWORD PTR [rsp+3080], xmm0
	movdqu XMMWORD PTR [rsp+3064], xmm0
	movdqu XMMWORD PTR [rsp+3048], xmm0
	movdqu XMMWORD PTR [rsp+3032], xmm0
	movdqu XMMWORD PTR [rsp+3016], xmm0
	movdqu XMMWORD PTR [rsp+3000], xmm0
	movdqu XMMWORD PTR [rsp+2984], xmm0
	movdqu XMMWORD PTR [rsp+2968], xmm0
	movdqu XMMWORD PTR [rsp+2952], xmm0
	movdqu XMMWORD PTR [rsp+2936], xmm0
	movdqu XMMWORD PTR [rsp+2920], xmm0
	movdqu XMMWORD PTR [rsp+2904], xmm0
	movdqu XMMWORD PTR [rsp+2888], xmm0
	movdqu XMMWORD PTR [rsp+2872], xmm0
	movdqu XMMWORD PTR [rsp+2856], xmm0
	movdqu XMMWORD PTR [rsp+2840], xmm0
	movdqu XMMWORD PTR [rsp+2824], xmm0
	movdqu XMMWORD PTR [rsp+2808], xmm0
	movdqu XMMWORD PTR [rsp+2792], xmm0
	movdqu XMMWORD PTR [rsp+2776], xmm0
	movdqu XMMWORD PTR [rsp+2760], xmm0
	movdqu XMMWORD PTR [rsp+2744], xmm0
	movdqu XMMWORD PTR [rsp+2728], xmm0
	movdqu XMMWORD PTR [rsp+2712], xmm0
	movdqu XMMWORD PTR [rsp+2696], xmm0
	movdqu XMMWORD PTR [rsp+2680], xmm0
	movdqu XMMWORD PTR [rsp+2664], xmm0
	movdqu XMMWORD PTR [rsp+2648], xmm0
	movdqu XMMWORD PTR [rsp+2632], xmm0
	movdqu XMMWORD PTR [rsp+2616], xmm0
	movdqu XMMWORD PTR [rsp+2600], xmm0
	movdqu XMMWORD PTR [rsp+2584], xmm0
	movdqu XMMWORD PTR [rsp+2568], xmm0
	movdqu XMMWORD PTR [rsp+2552], xmm0
	movdqu XMMWORD PTR [rsp+2536], xmm0
	movdqu XMMWORD PTR [rsp+2520], xmm0
	movdqu XMMWORD PTR [rsp+2504], xmm0
	movdqu XMMWORD PTR [rsp+2488], xmm0
	movdqu XMMWORD PTR [rsp+2472], xmm0
	movdqu XMMWORD PTR [rsp+2456], xmm0
	movdqu XMMWORD PTR [rsp+2440], xmm0
	movdqu XMMWORD PTR [rsp+2424], xmm0
	movdqu XMMWORD PTR [rsp+2408], xmm0
	movdqu XMMWORD PTR [rsp+2392], xmm0
	movdqu XMMWORD PTR [rsp+2376], xmm0
	movdqu XMMWORD PTR [rsp+2360], xmm0
	movdqu XMMWORD PTR [rsp+2344], xmm0
	movdqu XMMWORD PTR [rsp+2328], xmm0
	movdqu XMMWORD PTR [rsp+2312], xmm0
	movdqu XMMWORD PTR [rsp+2296], xmm0
	movdqu XMMWORD PTR [rsp+2280], xmm0
	movdqu XMMWORD PTR [rsp+2264], xmm0
	movdqu XMMWORD PTR [rsp+2248], xmm0
	movdqu XMMWORD PTR [rsp+2232], xmm0
	movdqu XMMWORD PTR [rsp+2216], xmm0
	movdqu XMMWORD PTR [rsp+2200], xmm0
	movdqu XMMWORD PTR [rsp+2184], xmm0
	movdqu XMMWORD PTR [rsp+2168], xmm0
	movdqu XMMWORD PTR [rsp+2152], xmm0
	movdqu XMMWORD PTR [rsp+2136], xmm0
	movdqu XMMWORD PTR [rsp+2120], xmm0
	movdqu XMMWORD PTR [rsp+2104], xmm0
	movdqu XMMWORD PTR [rsp+2088], xmm0
	movdqu XMMWORD PTR [rsp+2072], xmm0
	movdqu XMMWORD PTR [rsp+2056], xmm0
	movdqu XMMWORD PTR [rsp+2040], xmm0
	movdqu XMMWORD PTR [rsp+2024], xmm0
	movdqu XMMWORD PTR [rsp+2008], xmm0
	movdqu XMMWORD PTR [rsp+1992], xmm0
	movdqu XMMWORD PTR [rsp+1976], xmm0
	movdqu XMMWORD PTR [rsp+1960], xmm0
	movdqu XMMWORD PTR [rsp+1944], xmm0
	movdqu XMMWORD PTR [rsp+1928], xmm0
	movdqu XMMWORD PTR [rsp+1912], xmm0
	movdqu XMMWORD PTR [rsp+1896], xmm0
	movdqu XMMWORD PTR [rsp+1880], xmm0
	movdqu XMMWORD PTR [rsp+1864], xmm0
	movdqu XMMWORD PTR [rsp+1848], xmm0
	movdqu XMMWORD PTR [rsp+1832], xmm0
	movdqu XMMWORD PTR [rsp+1816], xmm0
	movdqu XMMWORD PTR [rsp+1800], xmm0
	movdqu XMMWORD PTR [rsp+1784], xmm0
	movdqu XMMWORD PTR [rsp+1768], xmm0
	movdqu XMMWORD PTR [rsp+1752], xmm0
	movdqu XMMWORD PTR [rsp+1736], xmm0
	movdqu XMMWORD PTR [rsp+1720], xmm0
	movdqu XMMWORD PTR [rsp+1704], xmm0
	movdqu XMMWORD PTR [rsp+1688], xmm0
	movdqu XMMWORD PTR [rsp+1672], xmm0
	movdqu XMMWORD PTR [rsp+1656], xmm0
	movdqu XMMWORD PTR [rsp+1640], xmm0
	movdqu XMMWORD PTR [rsp+1624], xmm0
	movdqu XMMWORD PTR [rsp+1608], xmm0
	movdqu XMMWORD PTR [rsp+1592], xmm0
	movdqu XMMWORD PTR [rsp+1576], xmm0
	movdqu XMMWORD PTR [rsp+1560], xmm0
	movdqu XMMWORD PTR [rsp+1544], xmm0
	movdqu XMMWORD PTR [rsp+1528], xmm0
	movdqu XMMWORD PTR [rsp+1512], xmm0
	movdqu XMMWORD PTR [rsp+1496], xmm0
	movdqu XMMWORD PTR [rsp+1480], xmm0
	movdqu XMMWORD PTR [rsp+1464], xmm0
	movdqu XMMWORD PTR [rsp+1448], xmm0
	movdqu XMMWORD PTR [rsp+1432], xmm0
	movdqu XMMWORD PTR [rsp+1416], xmm0
	movdqu XMMWORD PTR [rsp+1400], xmm0
	movdqu XMMWORD PTR [rsp+1384], xmm0
	movdqu XMMWORD PTR [rsp+1368], xmm0
	movdqu XMMWORD PTR [rsp+1352], xmm0
	movdqu XMMWORD PTR [rsp+1336], xmm0
	movdqu XMMWORD PTR [rsp+1320], xmm0
	movdqu XMMWORD PTR [rsp+1304], xmm0
	movdqu XMMWORD PTR [rsp+1288], xmm0
	movdqu XMMWORD PTR [rsp+1272], xmm0
	movdqu XMMWORD PTR [rsp+1256], xmm0
	movdqu XMMWORD PTR [rsp+1240], xmm0
	movdqu XMMWORD PTR [rsp+1224], xmm0
	movdqu XMMWORD PTR [rsp+1208], xmm0
	movdqu XMMWORD PTR [rsp+1192], xmm0
	movdqu XMMWORD PTR [rsp+1176], xmm0
	movdqu XMMWORD PTR [rsp+1160], xmm0
	movdqu XMMWORD PTR [rsp+1144], xmm0
	movdqu XMMWORD PTR [rsp+1128], xmm0
	movdqu XMMWORD PTR [rsp+1112], xmm0
	movdqu XMMWORD PTR [rsp+1096], xmm0
	movdqu XMMWORD PTR [rsp+1080], xmm0
	movdqu XMMWORD PTR [rsp+1064], xmm0
	movdqu XMMWORD PTR [rsp+1048], xmm0
	movdqu XMMWORD PTR [rsp+1032], xmm0
	movdqu XMMWORD PTR [rsp+1016], xmm0
	movdqu XMMWORD PTR [rsp+1000], xmm0
	movdqu XMMWORD PTR [rsp+984], xmm0
	movdqu XMMWORD PTR [rsp+968], xmm0
	movdqu XMMWORD PTR [rsp+952], xmm0
	movdqu XMMWORD PTR [rsp+936], xmm0
	movdqu XMMWORD PTR [rsp+920], xmm0
	movdqu XMMWORD PTR [rsp+904], xmm0
	movdqu XMMWORD PTR [rsp+888], xmm0
	movdqu XMMWORD PTR [rsp+872], xmm0
	movdqu XMMWORD PTR [rsp+856], xmm0
	movdqu XMMWORD PTR [rsp+840], xmm0
	movdqu XMMWORD PTR [rsp+824], xmm0
	movdqu XMMWORD PTR [rsp+808], xmm0
	movdqu XMMWORD PTR [rsp+792], xmm0
	movdqu XMMWORD PTR [rsp+776], xmm0
	movdqu XMMWORD PTR [rsp+760], xmm0
	movdqu XMMWORD PTR [rsp+744], xmm0
	movdqu XMMWORD PTR [rsp+728], xmm0
	movdqu XMMWORD PTR [rsp+712], xmm0
	movdqu XMMWORD PTR [rsp+696], xmm0
	movdqu XMMWORD PTR [rsp+680], xmm0
	movdqu XMMWORD PTR [rsp+664], xmm0
	movdqu XMMWORD PTR [rsp+648], xmm0
	movdqu XMMWORD PTR [rsp+632], xmm0
	movdqu XMMWORD PTR [rsp+616], xmm0
	movdqu XMMWORD PTR [rsp+600], xmm0
	movdqu XMMWORD PTR [rsp+584], xmm0
	movdqu XMMWORD PTR [rsp+568], xmm0
	movdqu XMMWORD PTR [rsp+552], xmm0
	movdqu XMMWORD PTR [rsp+536], xmm0
	movdqu XMMWORD PTR [rsp+520], xmm0
	movdqu XMMWORD PTR [rsp+504], xmm0
	movdqu XMMWORD PTR [rsp+488], xmm0
	movdqu XMMWORD PTR [rsp+472], xmm0
	movdqu XMMWORD PTR [rsp+456], xmm0
	movdqu XMMWORD PTR [rsp+440], xmm0
	movdqu XMMWORD PTR [rsp+424], xmm0
	movdqu XMMWORD PTR [rsp+408], xmm0
	movdqu XMMWORD PTR [rsp+392], xmm0
	movdqu XMMWORD PTR [rsp+376], xmm0
	movdqu XMMWORD PTR [rsp+360], xmm0
	movdqu XMMWORD PTR [rsp+344], xmm0
	movdqu XMMWORD PTR [rsp+328], xmm0
	movdqu XMMWORD PTR [rsp+312], xmm0
	movdqu XMMWORD PTR [rsp+296], xmm0
	movdqu XMMWORD PTR [rsp+280], xmm0
	movdqu XMMWORD PTR [rsp+264], xmm0
	movdqu XMMWORD PTR [rsp+248], xmm0
	movdqu XMMWORD PTR [rsp+232], xmm0
	movdqu XMMWORD PTR [rsp+216], xmm0
	movdqu XMMWORD PTR [rsp+200], xmm0
	movdqu XMMWORD PTR [rsp+184], xmm0
	movdqu XMMWORD PTR [rsp+168], xmm0
	movdqu XMMWORD PTR [rsp+152], xmm0
	movdqu XMMWORD PTR [rsp+136], xmm0
	movdqu XMMWORD PTR [rsp+120], xmm0
	movdqu XMMWORD PTR [rsp+104], xmm0
	movdqu XMMWORD PTR [rsp+88], xmm0
	movdqu XMMWORD PTR [rsp+72], xmm0
	movdqu XMMWORD PTR [rsp+56], xmm0
	movdqu XMMWORD PTR [rsp+40], xmm0
	movdqu XMMWORD PTR [rsp+24], xmm0
	movdqu XMMWORD PTR [rsp+8], xmm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+3848]
	lea rsp, [rsp+8]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6

vg_aes_gcm_siv_open:
	lea rsp, [rsp-3848]
	mov rax, QWORD PTR [rsp+3856]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3864]
	mov QWORD PTR [rsp+16], rax
	mov rax, rsp
	add rax, 32
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+144], rbx
	mov QWORD PTR [rax+152], rbp
	mov QWORD PTR [rax+160], r12
	mov QWORD PTR [rax+168], r13
	mov QWORD PTR [rax+176], r14
	mov QWORD PTR [rax+184], r15
	mov r15, rax
	mov r13, rdi
	mov QWORD PTR [r15+200], rsi
	mov QWORD PTR [r15+208], rdx
	mov QWORD PTR [r15+216], rcx
	mov QWORD PTR [r15+224], r8
	mov QWORD PTR [r15+232], r9
	mov QWORD PTR [r15+240], r10
	mov rcx, QWORD PTR [rsp+16]
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+8], rax
	mov ebx, 0
	mov rdi, r15
	add rdi, 488
	mov rbp, QWORD PTR [r15+200]
	shr rbp, 1
	sub rbp, 1
20:
	mov rax, QWORD PTR [r15+208]
	mov ecx, DWORD PTR [rax]
	shl rcx, 32
	or rcx, rbx
	mov rdx, QWORD PTR [rax+4]
	movq xmm0, rcx
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rdi, 16
	add rbx, 1
	cmp rbx, rbp
	jne 20b
	mov rdi, r13
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, rbp
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks}
	mov rsi, r15
	add rsi, 488
	mov rdi, r15
	add rdi, 16
	mov rcx, rbp
21:
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+16]
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 32
	add rdi, 16
	sub rcx, 2
	jne 21b
	mov rdi, r15
	add rdi, 32
	mov rsi, QWORD PTR [r15+200]
	sub rsi, 6
	add rsi, rsi
	add rsi, rsi
	mov rdx, r15
	add rdx, 248
	mov rcx, r15
	add rcx, 1768
	call {vg_aes_expand_key_scratch}
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov rcx, rax
	and rcx, 1
	mov r8d, 0
	sub r8, rcx
	shr rax, 1
	mov rcx, rdx
	and rcx, 1
	ror rcx, 1
	or rax, rcx
	shr rdx, 1
	movabs rcx, -2233785415175766016
	and rcx, r8
	xor rdx, rcx
	bswap rdx
	bswap rax
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+64], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+80], xmm0
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	movabs rcx, -9223372036854775808
	or rdx, rcx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 22f
24:
	mov r14d, 64
	cmp rbx, r14
	jb 25f
	jmp 26f
25:
	mov r14, rbx
26:
	movdqu xmm0, XMMWORD PTR [r15+96]
	mov r8d, 1
	movq xmm1, r8
	mov rcx, r14
	mov rdi, r15
	add rdi, 488
27:
	movdqu XMMWORD PTR [rdi], xmm0
	paddd xmm0, xmm1
	add rdi, 16
	sub rcx, 1
	jne 27b
	movdqu XMMWORD PTR [r15+96], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	mov r8, r15
	add r8, 1768
	call {vg_aes_encrypt_blocks}
	mov rcx, r14
	mov rsi, r15
	add rsi, 488
28:
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r12], xmm0
	add r12, 16
	add rsi, 16
	sub rcx, 1
	jne 28b
	sub rbx, r14
	jne 24b
	jmp 23f
22:
23:
	test rbp, rbp
	je 29f
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32}
	mov rdi, r12
	mov rsi, r15
	add rsi, 128
	mov rcx, rbp
	mov r10d, 0
211:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 211b
	jmp 210f
29:
210:
	mov rax, QWORD PTR [r15+224]
	shr rax, 4
	mov rdx, QWORD PTR [r15+240]
	shr rdx, 4
	add rax, rdx
	cmp rax, 62
	jae 212f
	mov rdi, r15
	add rdi, 488
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 214f
	mov r14, rbx
	mov rcx, r14
216:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 216b
	jmp 215f
214:
215:
	test rbp, rbp
	je 217f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
219:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 219b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 218f
217:
218:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	mov rsi, r12
	test rbx, rbx
	je 220f
	mov r14, rbx
	mov rcx, r14
222:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 222b
	jmp 221f
220:
221:
	test rbp, rbp
	je 223f
	mov rbx, rdi
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rcx, rbp
	mov r10d, 0
225:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 225b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rbx], xmm0
	mov rdi, rbx
	add rdi, 16
	jmp 224f
223:
224:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	mov rcx, rdi
	sub rcx, r15
	shr rcx, 4
	sub rcx, 29
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	call {vg_ghash}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
	jmp 213f
212:
	mov r12, QWORD PTR [r15+216]
	mov rbp, QWORD PTR [r15+224]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 226f
228:
	mov r14d, 64
	cmp rbx, r14
	jb 229f
	jmp 230f
229:
	mov r14, rbx
230:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
231:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 231b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 228b
	jmp 227f
226:
227:
	test rbp, rbp
	je 232f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
234:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 234b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash}
	jmp 233f
232:
233:
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov rbx, rbp
	shr rbx, 4
	and rbp, 15
	test rbx, rbx
	je 235f
237:
	mov r14d, 64
	cmp rbx, r14
	jb 238f
	jmp 239f
238:
	mov r14, rbx
239:
	mov rsi, r12
	mov rdi, r15
	add rdi, 488
	mov rcx, r14
240:
	mov rax, QWORD PTR [rsi]
	mov rdx, QWORD PTR [rsi+8]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	add rsi, 16
	add rdi, 16
	sub rcx, 1
	jne 240b
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov rcx, r14
	call {vg_ghash}
	mov rax, r14
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add r12, rax
	sub rbx, r14
	jne 237b
	jmp 236f
235:
236:
	test rbp, rbp
	je 241f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 128
	mov rsi, r12
	mov rcx, rbp
	mov r10d, 0
243:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 243b
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	bswap rax
	bswap rdx
	movq xmm0, rdx
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+488], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 488
	mov ecx, 1
	call {vg_ghash}
	jmp 242f
241:
242:
	mov rax, QWORD PTR [r15+240]
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov rdx, QWORD PTR [r15+224]
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	bswap rdx
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 64
	mov rsi, r15
	add rsi, 80
	mov r8, r15
	add r8, 1512
	mov rdx, r15
	add rdx, 128
	mov ecx, 1
	call {vg_ghash}
	mov rax, QWORD PTR [r15+88]
	bswap rax
	mov rdx, QWORD PTR [r15+80]
	bswap rdx
	mov rcx, QWORD PTR [r15+208]
	xor rax, QWORD PTR [rcx]
	mov r8d, DWORD PTR [rcx+8]
	xor rdx, r8
	movabs r8, 9223372036854775807
	and rdx, r8
	movq xmm0, rax
	movq xmm1, rdx
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [r15+96], xmm0
213:
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [r15+112], xmm0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rdi, r15
	add rdi, 248
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 1768
	mov rcx, r15
	add rcx, 128
	call {vg_aes_ctr32}
	mov rax, QWORD PTR [r15]
	xor rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+8]
	xor rdx, QWORD PTR [r15+136]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+192], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+240]
	mov r11d, 0
	sub r11, QWORD PTR [r15+192]
	mov r10d, 0
	mov rcx, rbp
	shr rcx, 4
	test rcx, rcx
	je 244f
	movq xmm0, r11
	punpcklqdq xmm0, xmm0
246:
	movdqu xmm1, XMMWORD PTR [r12+r10*1]
	pand xmm1, xmm0
	movdqu XMMWORD PTR [r12+r10*1], xmm1
	add r10, 16
	sub rcx, 1
	jne 246b
	jmp 245f
244:
245:
	cmp r10, rbp
	je 247f
249:
	movzx eax, BYTE PTR [r12+r10*1]
	and rax, r11
	mov BYTE PTR [r12+r10*1], al
	add r10, 1
	cmp r10, rbp
	jne 249b
	jmp 248f
247:
248:
	mov rax, QWORD PTR [r15+192]
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	lea rsp, [rsp+3848]
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	pxor xmm12, xmm12
	pxor xmm13, xmm13
	pxor xmm14, xmm14
	pxor xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-8]
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp-3848]
	movdqu XMMWORD PTR [rsp+3832], xmm0
	movdqu XMMWORD PTR [rsp+3816], xmm0
	movdqu XMMWORD PTR [rsp+3800], xmm0
	movdqu XMMWORD PTR [rsp+3784], xmm0
	movdqu XMMWORD PTR [rsp+3768], xmm0
	movdqu XMMWORD PTR [rsp+3752], xmm0
	movdqu XMMWORD PTR [rsp+3736], xmm0
	movdqu XMMWORD PTR [rsp+3720], xmm0
	movdqu XMMWORD PTR [rsp+3704], xmm0
	movdqu XMMWORD PTR [rsp+3688], xmm0
	movdqu XMMWORD PTR [rsp+3672], xmm0
	movdqu XMMWORD PTR [rsp+3656], xmm0
	movdqu XMMWORD PTR [rsp+3640], xmm0
	movdqu XMMWORD PTR [rsp+3624], xmm0
	movdqu XMMWORD PTR [rsp+3608], xmm0
	movdqu XMMWORD PTR [rsp+3592], xmm0
	movdqu XMMWORD PTR [rsp+3576], xmm0
	movdqu XMMWORD PTR [rsp+3560], xmm0
	movdqu XMMWORD PTR [rsp+3544], xmm0
	movdqu XMMWORD PTR [rsp+3528], xmm0
	movdqu XMMWORD PTR [rsp+3512], xmm0
	movdqu XMMWORD PTR [rsp+3496], xmm0
	movdqu XMMWORD PTR [rsp+3480], xmm0
	movdqu XMMWORD PTR [rsp+3464], xmm0
	movdqu XMMWORD PTR [rsp+3448], xmm0
	movdqu XMMWORD PTR [rsp+3432], xmm0
	movdqu XMMWORD PTR [rsp+3416], xmm0
	movdqu XMMWORD PTR [rsp+3400], xmm0
	movdqu XMMWORD PTR [rsp+3384], xmm0
	movdqu XMMWORD PTR [rsp+3368], xmm0
	movdqu XMMWORD PTR [rsp+3352], xmm0
	movdqu XMMWORD PTR [rsp+3336], xmm0
	movdqu XMMWORD PTR [rsp+3320], xmm0
	movdqu XMMWORD PTR [rsp+3304], xmm0
	movdqu XMMWORD PTR [rsp+3288], xmm0
	movdqu XMMWORD PTR [rsp+3272], xmm0
	movdqu XMMWORD PTR [rsp+3256], xmm0
	movdqu XMMWORD PTR [rsp+3240], xmm0
	movdqu XMMWORD PTR [rsp+3224], xmm0
	movdqu XMMWORD PTR [rsp+3208], xmm0
	movdqu XMMWORD PTR [rsp+3192], xmm0
	movdqu XMMWORD PTR [rsp+3176], xmm0
	movdqu XMMWORD PTR [rsp+3160], xmm0
	movdqu XMMWORD PTR [rsp+3144], xmm0
	movdqu XMMWORD PTR [rsp+3128], xmm0
	movdqu XMMWORD PTR [rsp+3112], xmm0
	movdqu XMMWORD PTR [rsp+3096], xmm0
	movdqu XMMWORD PTR [rsp+3080], xmm0
	movdqu XMMWORD PTR [rsp+3064], xmm0
	movdqu XMMWORD PTR [rsp+3048], xmm0
	movdqu XMMWORD PTR [rsp+3032], xmm0
	movdqu XMMWORD PTR [rsp+3016], xmm0
	movdqu XMMWORD PTR [rsp+3000], xmm0
	movdqu XMMWORD PTR [rsp+2984], xmm0
	movdqu XMMWORD PTR [rsp+2968], xmm0
	movdqu XMMWORD PTR [rsp+2952], xmm0
	movdqu XMMWORD PTR [rsp+2936], xmm0
	movdqu XMMWORD PTR [rsp+2920], xmm0
	movdqu XMMWORD PTR [rsp+2904], xmm0
	movdqu XMMWORD PTR [rsp+2888], xmm0
	movdqu XMMWORD PTR [rsp+2872], xmm0
	movdqu XMMWORD PTR [rsp+2856], xmm0
	movdqu XMMWORD PTR [rsp+2840], xmm0
	movdqu XMMWORD PTR [rsp+2824], xmm0
	movdqu XMMWORD PTR [rsp+2808], xmm0
	movdqu XMMWORD PTR [rsp+2792], xmm0
	movdqu XMMWORD PTR [rsp+2776], xmm0
	movdqu XMMWORD PTR [rsp+2760], xmm0
	movdqu XMMWORD PTR [rsp+2744], xmm0
	movdqu XMMWORD PTR [rsp+2728], xmm0
	movdqu XMMWORD PTR [rsp+2712], xmm0
	movdqu XMMWORD PTR [rsp+2696], xmm0
	movdqu XMMWORD PTR [rsp+2680], xmm0
	movdqu XMMWORD PTR [rsp+2664], xmm0
	movdqu XMMWORD PTR [rsp+2648], xmm0
	movdqu XMMWORD PTR [rsp+2632], xmm0
	movdqu XMMWORD PTR [rsp+2616], xmm0
	movdqu XMMWORD PTR [rsp+2600], xmm0
	movdqu XMMWORD PTR [rsp+2584], xmm0
	movdqu XMMWORD PTR [rsp+2568], xmm0
	movdqu XMMWORD PTR [rsp+2552], xmm0
	movdqu XMMWORD PTR [rsp+2536], xmm0
	movdqu XMMWORD PTR [rsp+2520], xmm0
	movdqu XMMWORD PTR [rsp+2504], xmm0
	movdqu XMMWORD PTR [rsp+2488], xmm0
	movdqu XMMWORD PTR [rsp+2472], xmm0
	movdqu XMMWORD PTR [rsp+2456], xmm0
	movdqu XMMWORD PTR [rsp+2440], xmm0
	movdqu XMMWORD PTR [rsp+2424], xmm0
	movdqu XMMWORD PTR [rsp+2408], xmm0
	movdqu XMMWORD PTR [rsp+2392], xmm0
	movdqu XMMWORD PTR [rsp+2376], xmm0
	movdqu XMMWORD PTR [rsp+2360], xmm0
	movdqu XMMWORD PTR [rsp+2344], xmm0
	movdqu XMMWORD PTR [rsp+2328], xmm0
	movdqu XMMWORD PTR [rsp+2312], xmm0
	movdqu XMMWORD PTR [rsp+2296], xmm0
	movdqu XMMWORD PTR [rsp+2280], xmm0
	movdqu XMMWORD PTR [rsp+2264], xmm0
	movdqu XMMWORD PTR [rsp+2248], xmm0
	movdqu XMMWORD PTR [rsp+2232], xmm0
	movdqu XMMWORD PTR [rsp+2216], xmm0
	movdqu XMMWORD PTR [rsp+2200], xmm0
	movdqu XMMWORD PTR [rsp+2184], xmm0
	movdqu XMMWORD PTR [rsp+2168], xmm0
	movdqu XMMWORD PTR [rsp+2152], xmm0
	movdqu XMMWORD PTR [rsp+2136], xmm0
	movdqu XMMWORD PTR [rsp+2120], xmm0
	movdqu XMMWORD PTR [rsp+2104], xmm0
	movdqu XMMWORD PTR [rsp+2088], xmm0
	movdqu XMMWORD PTR [rsp+2072], xmm0
	movdqu XMMWORD PTR [rsp+2056], xmm0
	movdqu XMMWORD PTR [rsp+2040], xmm0
	movdqu XMMWORD PTR [rsp+2024], xmm0
	movdqu XMMWORD PTR [rsp+2008], xmm0
	movdqu XMMWORD PTR [rsp+1992], xmm0
	movdqu XMMWORD PTR [rsp+1976], xmm0
	movdqu XMMWORD PTR [rsp+1960], xmm0
	movdqu XMMWORD PTR [rsp+1944], xmm0
	movdqu XMMWORD PTR [rsp+1928], xmm0
	movdqu XMMWORD PTR [rsp+1912], xmm0
	movdqu XMMWORD PTR [rsp+1896], xmm0
	movdqu XMMWORD PTR [rsp+1880], xmm0
	movdqu XMMWORD PTR [rsp+1864], xmm0
	movdqu XMMWORD PTR [rsp+1848], xmm0
	movdqu XMMWORD PTR [rsp+1832], xmm0
	movdqu XMMWORD PTR [rsp+1816], xmm0
	movdqu XMMWORD PTR [rsp+1800], xmm0
	movdqu XMMWORD PTR [rsp+1784], xmm0
	movdqu XMMWORD PTR [rsp+1768], xmm0
	movdqu XMMWORD PTR [rsp+1752], xmm0
	movdqu XMMWORD PTR [rsp+1736], xmm0
	movdqu XMMWORD PTR [rsp+1720], xmm0
	movdqu XMMWORD PTR [rsp+1704], xmm0
	movdqu XMMWORD PTR [rsp+1688], xmm0
	movdqu XMMWORD PTR [rsp+1672], xmm0
	movdqu XMMWORD PTR [rsp+1656], xmm0
	movdqu XMMWORD PTR [rsp+1640], xmm0
	movdqu XMMWORD PTR [rsp+1624], xmm0
	movdqu XMMWORD PTR [rsp+1608], xmm0
	movdqu XMMWORD PTR [rsp+1592], xmm0
	movdqu XMMWORD PTR [rsp+1576], xmm0
	movdqu XMMWORD PTR [rsp+1560], xmm0
	movdqu XMMWORD PTR [rsp+1544], xmm0
	movdqu XMMWORD PTR [rsp+1528], xmm0
	movdqu XMMWORD PTR [rsp+1512], xmm0
	movdqu XMMWORD PTR [rsp+1496], xmm0
	movdqu XMMWORD PTR [rsp+1480], xmm0
	movdqu XMMWORD PTR [rsp+1464], xmm0
	movdqu XMMWORD PTR [rsp+1448], xmm0
	movdqu XMMWORD PTR [rsp+1432], xmm0
	movdqu XMMWORD PTR [rsp+1416], xmm0
	movdqu XMMWORD PTR [rsp+1400], xmm0
	movdqu XMMWORD PTR [rsp+1384], xmm0
	movdqu XMMWORD PTR [rsp+1368], xmm0
	movdqu XMMWORD PTR [rsp+1352], xmm0
	movdqu XMMWORD PTR [rsp+1336], xmm0
	movdqu XMMWORD PTR [rsp+1320], xmm0
	movdqu XMMWORD PTR [rsp+1304], xmm0
	movdqu XMMWORD PTR [rsp+1288], xmm0
	movdqu XMMWORD PTR [rsp+1272], xmm0
	movdqu XMMWORD PTR [rsp+1256], xmm0
	movdqu XMMWORD PTR [rsp+1240], xmm0
	movdqu XMMWORD PTR [rsp+1224], xmm0
	movdqu XMMWORD PTR [rsp+1208], xmm0
	movdqu XMMWORD PTR [rsp+1192], xmm0
	movdqu XMMWORD PTR [rsp+1176], xmm0
	movdqu XMMWORD PTR [rsp+1160], xmm0
	movdqu XMMWORD PTR [rsp+1144], xmm0
	movdqu XMMWORD PTR [rsp+1128], xmm0
	movdqu XMMWORD PTR [rsp+1112], xmm0
	movdqu XMMWORD PTR [rsp+1096], xmm0
	movdqu XMMWORD PTR [rsp+1080], xmm0
	movdqu XMMWORD PTR [rsp+1064], xmm0
	movdqu XMMWORD PTR [rsp+1048], xmm0
	movdqu XMMWORD PTR [rsp+1032], xmm0
	movdqu XMMWORD PTR [rsp+1016], xmm0
	movdqu XMMWORD PTR [rsp+1000], xmm0
	movdqu XMMWORD PTR [rsp+984], xmm0
	movdqu XMMWORD PTR [rsp+968], xmm0
	movdqu XMMWORD PTR [rsp+952], xmm0
	movdqu XMMWORD PTR [rsp+936], xmm0
	movdqu XMMWORD PTR [rsp+920], xmm0
	movdqu XMMWORD PTR [rsp+904], xmm0
	movdqu XMMWORD PTR [rsp+888], xmm0
	movdqu XMMWORD PTR [rsp+872], xmm0
	movdqu XMMWORD PTR [rsp+856], xmm0
	movdqu XMMWORD PTR [rsp+840], xmm0
	movdqu XMMWORD PTR [rsp+824], xmm0
	movdqu XMMWORD PTR [rsp+808], xmm0
	movdqu XMMWORD PTR [rsp+792], xmm0
	movdqu XMMWORD PTR [rsp+776], xmm0
	movdqu XMMWORD PTR [rsp+760], xmm0
	movdqu XMMWORD PTR [rsp+744], xmm0
	movdqu XMMWORD PTR [rsp+728], xmm0
	movdqu XMMWORD PTR [rsp+712], xmm0
	movdqu XMMWORD PTR [rsp+696], xmm0
	movdqu XMMWORD PTR [rsp+680], xmm0
	movdqu XMMWORD PTR [rsp+664], xmm0
	movdqu XMMWORD PTR [rsp+648], xmm0
	movdqu XMMWORD PTR [rsp+632], xmm0
	movdqu XMMWORD PTR [rsp+616], xmm0
	movdqu XMMWORD PTR [rsp+600], xmm0
	movdqu XMMWORD PTR [rsp+584], xmm0
	movdqu XMMWORD PTR [rsp+568], xmm0
	movdqu XMMWORD PTR [rsp+552], xmm0
	movdqu XMMWORD PTR [rsp+536], xmm0
	movdqu XMMWORD PTR [rsp+520], xmm0
	movdqu XMMWORD PTR [rsp+504], xmm0
	movdqu XMMWORD PTR [rsp+488], xmm0
	movdqu XMMWORD PTR [rsp+472], xmm0
	movdqu XMMWORD PTR [rsp+456], xmm0
	movdqu XMMWORD PTR [rsp+440], xmm0
	movdqu XMMWORD PTR [rsp+424], xmm0
	movdqu XMMWORD PTR [rsp+408], xmm0
	movdqu XMMWORD PTR [rsp+392], xmm0
	movdqu XMMWORD PTR [rsp+376], xmm0
	movdqu XMMWORD PTR [rsp+360], xmm0
	movdqu XMMWORD PTR [rsp+344], xmm0
	movdqu XMMWORD PTR [rsp+328], xmm0
	movdqu XMMWORD PTR [rsp+312], xmm0
	movdqu XMMWORD PTR [rsp+296], xmm0
	movdqu XMMWORD PTR [rsp+280], xmm0
	movdqu XMMWORD PTR [rsp+264], xmm0
	movdqu XMMWORD PTR [rsp+248], xmm0
	movdqu XMMWORD PTR [rsp+232], xmm0
	movdqu XMMWORD PTR [rsp+216], xmm0
	movdqu XMMWORD PTR [rsp+200], xmm0
	movdqu XMMWORD PTR [rsp+184], xmm0
	movdqu XMMWORD PTR [rsp+168], xmm0
	movdqu XMMWORD PTR [rsp+152], xmm0
	movdqu XMMWORD PTR [rsp+136], xmm0
	movdqu XMMWORD PTR [rsp+120], xmm0
	movdqu XMMWORD PTR [rsp+104], xmm0
	movdqu XMMWORD PTR [rsp+88], xmm0
	movdqu XMMWORD PTR [rsp+72], xmm0
	movdqu XMMWORD PTR [rsp+56], xmm0
	movdqu XMMWORD PTR [rsp+40], xmm0
	movdqu XMMWORD PTR [rsp+24], xmm0
	movdqu XMMWORD PTR [rsp+8], xmm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+3848]
	lea rsp, [rsp+8]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6
