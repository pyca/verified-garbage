// The functions of `src/internal/vg_hmac_sha1_init_scratch.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_sha1_init_scratch:
	mov QWORD PTR [r8+160], rbx
	mov QWORD PTR [r8+168], rbp
	mov QWORD PTR [r8+176], r12
	mov QWORD PTR [r8+184], r13
	mov QWORD PTR [r8+192], r14
	mov QWORD PTR [r8+200], r15
	mov rbx, rdi
	mov r12, rsi
	mov r15, r8
	mov rbp, rdx
	mov r13, rcx
	mov rdi, rbx
	call {vg_sha1_init_core}
	mov rdi, r12
	call {vg_sha1_init_core}
	movabs rax, 3906369333256140342
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqu XMMWORD PTR [rbx+20], xmm0
	movdqu XMMWORD PTR [rbx+36], xmm0
	movdqu XMMWORD PTR [rbx+52], xmm0
	movdqu XMMWORD PTR [rbx+68], xmm0
	mov r14d, 0
	mov rcx, r13
	shr rcx, 4
	test rcx, rcx
	je 20f
22:
	movdqu xmm1, XMMWORD PTR [rbp+r14*1]
	pxor xmm1, xmm0
	mov r10, r14
	and r10, 48
	movdqu XMMWORD PTR [rbx+r10*1+20], xmm1
	add r14, 16
	sub rcx, 1
	jne 22b
	jmp 21f
20:
21:
	cmp r14, r13
	je 23f
25:
	movzx eax, BYTE PTR [rbp+r14*1]
	xor eax, 54
	mov r10, r14
	and r10, 63
	mov BYTE PTR [rbx+r10*1+20], al
	add r14, 1
	cmp r14, r13
	jne 25b
	jmp 24f
23:
24:
	movabs rax, 7668058320836127338
	movq xmm1, rax
	punpcklqdq xmm1, xmm1
	movdqu xmm2, XMMWORD PTR [rbx+20]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [r12+20], xmm2
	movdqu xmm2, XMMWORD PTR [rbx+36]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [r12+36], xmm2
	movdqu xmm2, XMMWORD PTR [rbx+52]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [r12+52], xmm2
	movdqu xmm2, XMMWORD PTR [rbx+68]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [r12+68], xmm2
	mov rsi, rbx
	add rsi, 20
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha1_compress}
	mov rbx, rdi
	mov r15, rcx
	mov rbx, r12
	mov rsi, r12
	add rsi, 20
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha1_compress}
	mov rbx, rdi
	mov r15, rcx
	mov rbx, QWORD PTR [r15+160]
	mov rbp, QWORD PTR [r15+168]
	mov r12, QWORD PTR [r15+176]
	mov r13, QWORD PTR [r15+184]
	mov r14, QWORD PTR [r15+192]
	mov r15, QWORD PTR [r15+200]
	ret
	.p2align 6
