// The functions of `src/internal/vg_hmac_sha512_224_init_scratch.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_sha512_224_init_scratch:
	mov QWORD PTR [r8+1376], rbx
	mov QWORD PTR [r8+1384], rbp
	mov QWORD PTR [r8+1392], r12
	mov QWORD PTR [r8+1400], r13
	mov QWORD PTR [r8+1408], r14
	mov QWORD PTR [r8+1416], r15
	mov rbx, rdi
	mov r12, rsi
	mov r15, r8
	mov rbp, rdx
	mov r13, rcx
	mov rdi, rbx
	call {vg_sha512_224_init_core}
	mov rdi, r12
	call {vg_sha512_224_init_core}
	movabs rax, 3906369333256140342
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov r14d, 0
	mov rcx, r13
	shr rcx, 4
	test rcx, rcx
	je 20f
22:
	movdqu xmm1, XMMWORD PTR [rbp+r14*1]
	pxor xmm1, xmm0
	mov r10, r14
	and r10, 112
	movdqu XMMWORD PTR [rbx+r10*1+64], xmm1
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
	and r10, 127
	mov BYTE PTR [rbx+r10*1+64], al
	add r14, 1
	cmp r14, r13
	jne 25b
	jmp 24f
23:
24:
	movabs rax, 7668058320836127338
	movq xmm1, rax
	punpcklqdq xmm1, xmm1
	movdqu xmm2, XMMWORD PTR [rbx+64]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [r12+64], xmm2
	movdqu xmm2, XMMWORD PTR [rbx+80]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [r12+80], xmm2
	movdqu xmm2, XMMWORD PTR [rbx+96]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [r12+96], xmm2
	movdqu xmm2, XMMWORD PTR [rbx+112]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [r12+112], xmm2
	movdqu xmm2, XMMWORD PTR [rbx+128]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [r12+128], xmm2
	movdqu xmm2, XMMWORD PTR [rbx+144]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [r12+144], xmm2
	movdqu xmm2, XMMWORD PTR [rbx+160]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [r12+160], xmm2
	movdqu xmm2, XMMWORD PTR [rbx+176]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [r12+176], xmm2
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
	mov rbx, r12
	mov rsi, r12
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
	mov rbx, QWORD PTR [r15+1376]
	mov rbp, QWORD PTR [r15+1384]
	mov r12, QWORD PTR [r15+1392]
	mov r13, QWORD PTR [r15+1400]
	mov r14, QWORD PTR [r15+1408]
	mov r15, QWORD PTR [r15+1416]
	ret
	.p2align 6
