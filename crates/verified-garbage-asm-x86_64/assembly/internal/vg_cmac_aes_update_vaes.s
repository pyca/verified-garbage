// The functions of `src/internal/vg_cmac_aes_update_vaes.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cmac_aes_update_vaes:
	cmp r8, 2
	jae 20f
	mov QWORD PTR [r9+2064], rbx
	mov QWORD PTR [r9+2072], rbp
	mov QWORD PTR [r9+2080], r12
	mov QWORD PTR [r9+2088], r13
	mov QWORD PTR [r9+2096], r14
	mov QWORD PTR [r9+2104], r15
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rdx
	mov r13, rcx
	mov r14, r8
	mov r15, r9
	test r14, r14
	je 22f
24:
	mov rax, QWORD PTR [r12]
	xor rax, QWORD PTR [r13]
	mov QWORD PTR [r15+2048], rax
	mov rax, QWORD PTR [r12+8]
	xor rax, QWORD PTR [r13+8]
	mov QWORD PTR [r15+2056], rax
	mov eax, 0
	mov QWORD PTR [r12], rax
	mov QWORD PTR [r12+8], rax
	mov rdi, rbx
	mov rsi, rbp
	mov r9, r15
	mov rdx, r15
	add rdx, 2048
	mov rcx, r12
	mov r8d, 1
	call {vg_aes_ctr32_vaes}
	add r13, 16
	sub r14, 1
	jne 24b
	jmp 23f
22:
23:
	mov rbx, QWORD PTR [r15+2064]
	mov rbp, QWORD PTR [r15+2072]
	mov r12, QWORD PTR [r15+2080]
	mov r13, QWORD PTR [r15+2088]
	mov r14, QWORD PTR [r15+2096]
	mov r15, QWORD PTR [r15+2104]
21:
	ret
20:
	test r8, r8
	je 25f
	movdqu xmm1, XMMWORD PTR [rdi]
	movdqu xmm0, XMMWORD PTR [rdx]
	pxor xmm0, xmm1
	movdqu xmm2, XMMWORD PTR [rdi+16]
	movdqu xmm3, XMMWORD PTR [rdi+32]
	movdqu xmm4, XMMWORD PTR [rdi+48]
	movdqu xmm5, XMMWORD PTR [rdi+64]
	movdqu xmm6, XMMWORD PTR [rdi+80]
	movdqu xmm7, XMMWORD PTR [rdi+96]
	movdqu xmm8, XMMWORD PTR [rdi+112]
	movdqu xmm9, XMMWORD PTR [rdi+128]
	movdqu xmm10, XMMWORD PTR [rdi+144]
	movdqu xmm11, XMMWORD PTR [rdi+160]
	movdqu xmm12, XMMWORD PTR [rdi+176]
	movdqu xmm13, XMMWORD PTR [rdi+192]
	movdqu xmm14, XMMWORD PTR [rdi+208]
	cmp rsi, 10
	je 27f
	cmp rsi, 12
	je 29f
	movdqu xmm15, XMMWORD PTR [rdi+224]
	pxor xmm15, xmm1
211:
	movdqu xmm1, XMMWORD PTR [rcx]
	pxor xmm0, xmm1
	aesenc xmm0, xmm2
	aesenc xmm0, xmm3
	aesenc xmm0, xmm4
	aesenc xmm0, xmm5
	aesenc xmm0, xmm6
	aesenc xmm0, xmm7
	aesenc xmm0, xmm8
	aesenc xmm0, xmm9
	aesenc xmm0, xmm10
	aesenc xmm0, xmm11
	aesenc xmm0, xmm12
	aesenc xmm0, xmm13
	aesenc xmm0, xmm14
	aesenclast xmm0, xmm15
	add rcx, 16
	sub r8, 1
	jne 211b
	jmp 210f
29:
	movdqu xmm15, XMMWORD PTR [rdi+192]
	pxor xmm15, xmm1
212:
	movdqu xmm1, XMMWORD PTR [rcx]
	pxor xmm0, xmm1
	aesenc xmm0, xmm2
	aesenc xmm0, xmm3
	aesenc xmm0, xmm4
	aesenc xmm0, xmm5
	aesenc xmm0, xmm6
	aesenc xmm0, xmm7
	aesenc xmm0, xmm8
	aesenc xmm0, xmm9
	aesenc xmm0, xmm10
	aesenc xmm0, xmm11
	aesenc xmm0, xmm12
	aesenclast xmm0, xmm15
	add rcx, 16
	sub r8, 1
	jne 212b
210:
	jmp 28f
27:
	movdqu xmm15, XMMWORD PTR [rdi+160]
	pxor xmm15, xmm1
213:
	movdqu xmm1, XMMWORD PTR [rcx]
	pxor xmm0, xmm1
	aesenc xmm0, xmm2
	aesenc xmm0, xmm3
	aesenc xmm0, xmm4
	aesenc xmm0, xmm5
	aesenc xmm0, xmm6
	aesenc xmm0, xmm7
	aesenc xmm0, xmm8
	aesenc xmm0, xmm9
	aesenc xmm0, xmm10
	aesenclast xmm0, xmm15
	add rcx, 16
	sub r8, 1
	jne 213b
28:
	movdqu xmm1, XMMWORD PTR [rdi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [rdx], xmm0
	jmp 26f
25:
26:
	jmp 21b
	.p2align 6
