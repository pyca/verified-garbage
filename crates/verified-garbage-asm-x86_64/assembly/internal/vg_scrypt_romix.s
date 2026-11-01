// The functions of `src/internal/vg_scrypt_romix.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_scrypt_romix:
	mov QWORD PTR [r8+128], rbx
	mov QWORD PTR [r8+136], rbp
	mov QWORD PTR [r8+144], r12
	mov QWORD PTR [r8+152], r14
	mov QWORD PTR [r8+160], r15
	mov QWORD PTR [r8+168], r13
	mov rbx, rdi
	mov r12, rdx
	mov r13, r8
	mov r14, rsi
	add r14, r14
	add r14, r14
	add r14, r14
	add r14, r14
	add r14, r14
	add r14, r14
	add r14, r14
	mov rax, rsi
	mov edx, 1
	add rcx, rcx
20:
	add rax, rax
	add rdx, rdx
	cmp rax, rcx
	jne 20b
	shr rdx, 1
	mov QWORD PTR [r13+176], rdx
	mov r15, rdx
	mov rbp, r12
	mov rdi, rbx
	mov rsi, rbp
	mov rcx, r14
	shr rcx, 4
21:
	movdqu xmm0, XMMWORD PTR [rdi]
	movdqu XMMWORD PTR [rsi], xmm0
	add rdi, 16
	add rsi, 16
	sub rcx, 1
	jne 21b
22:
	mov rdi, rbp
	mov rsi, r14
	shr rsi, 7
	mov rcx, rsi
	mov rdx, rbp
	add rdx, r14
	mov r8, r13
	cmp r15, 1
	je 23f
	jmp 24f
23:
	mov rdx, rbx
24:
	call {vg_scrypt_blockmix}
	add rbp, r14
	sub r15, 1
	jne 22b
	mov r15, QWORD PTR [r13+176]
	mov rbp, r15
	sub rbp, 1
25:
	mov rax, QWORD PTR [rbx+r14*1-64]
	and rax, rbp
	mov rdx, r12
	mov rcx, r14
	mov rdi, rdx
	mul rcx
	mov rdx, rdi
	add rdx, rax
	mov rdi, rbx
	mov rsi, rdx
	mov r8, r13
	add r8, 192
	mov rcx, r14
	shr rcx, 4
26:
	movdqu xmm0, XMMWORD PTR [rdi]
	movdqu xmm1, XMMWORD PTR [rsi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [r8], xmm0
	add rdi, 16
	add rsi, 16
	add r8, 16
	sub rcx, 1
	jne 26b
	mov rdi, r13
	add rdi, 192
	mov rsi, r14
	shr rsi, 7
	mov rcx, rsi
	mov rdx, rbx
	mov r8, r13
	call {vg_scrypt_blockmix}
	sub r15, 1
	jne 25b
	mov rbx, QWORD PTR [r13+128]
	mov rbp, QWORD PTR [r13+136]
	mov r12, QWORD PTR [r13+144]
	mov r14, QWORD PTR [r13+152]
	mov r15, QWORD PTR [r13+160]
	mov r13, QWORD PTR [r13+168]
	ret
	.p2align 6
