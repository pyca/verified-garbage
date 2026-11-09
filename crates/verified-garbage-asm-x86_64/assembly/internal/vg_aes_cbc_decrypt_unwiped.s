// The functions of `src/internal/vg_aes_cbc_decrypt_unwiped.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_cbc_decrypt_unwiped:
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
	je 20f
	cmp r14, 4
	jb 22f
24:
	mov rax, QWORD PTR [r13]
	mov QWORD PTR [r15+2112], rax
	mov rax, QWORD PTR [r13+8]
	mov QWORD PTR [r15+2120], rax
	mov rax, QWORD PTR [r13+16]
	mov QWORD PTR [r15+2128], rax
	mov rax, QWORD PTR [r13+24]
	mov QWORD PTR [r15+2136], rax
	mov rax, QWORD PTR [r13+32]
	mov QWORD PTR [r15+2144], rax
	mov rax, QWORD PTR [r13+40]
	mov QWORD PTR [r15+2152], rax
	mov rax, QWORD PTR [r13+48]
	mov QWORD PTR [r15+2160], rax
	mov rax, QWORD PTR [r13+56]
	mov QWORD PTR [r15+2168], rax
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r13
	mov ecx, 4
	mov r8, r15
	call {vg_aes_decrypt_blocks}
	mov rax, QWORD PTR [r13]
	xor rax, QWORD PTR [r12]
	mov QWORD PTR [r13], rax
	mov rax, QWORD PTR [r13+8]
	xor rax, QWORD PTR [r12+8]
	mov QWORD PTR [r13+8], rax
	mov rax, QWORD PTR [r13+16]
	xor rax, QWORD PTR [r15+2112]
	mov QWORD PTR [r13+16], rax
	mov rax, QWORD PTR [r13+24]
	xor rax, QWORD PTR [r15+2120]
	mov QWORD PTR [r13+24], rax
	mov rax, QWORD PTR [r13+32]
	xor rax, QWORD PTR [r15+2128]
	mov QWORD PTR [r13+32], rax
	mov rax, QWORD PTR [r13+40]
	xor rax, QWORD PTR [r15+2136]
	mov QWORD PTR [r13+40], rax
	mov rax, QWORD PTR [r13+48]
	xor rax, QWORD PTR [r15+2144]
	mov QWORD PTR [r13+48], rax
	mov rax, QWORD PTR [r13+56]
	xor rax, QWORD PTR [r15+2152]
	mov QWORD PTR [r13+56], rax
	mov rax, QWORD PTR [r15+2160]
	mov QWORD PTR [r12], rax
	mov rax, QWORD PTR [r15+2168]
	mov QWORD PTR [r12+8], rax
	add r13, 64
	sub r14, 4
	cmp r14, 4
	jae 24b
	jmp 23f
22:
23:
	test r14, r14
	je 25f
27:
	mov rax, QWORD PTR [r13]
	mov QWORD PTR [r15+2048], rax
	mov rax, QWORD PTR [r13+8]
	mov QWORD PTR [r15+2056], rax
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r13
	mov ecx, 1
	mov r8, r15
	call {vg_aes_decrypt_blocks}
	mov rax, QWORD PTR [r13]
	xor rax, QWORD PTR [r12]
	mov QWORD PTR [r13], rax
	mov rax, QWORD PTR [r13+8]
	xor rax, QWORD PTR [r12+8]
	mov QWORD PTR [r13+8], rax
	mov rax, QWORD PTR [r15+2048]
	mov QWORD PTR [r12], rax
	mov rax, QWORD PTR [r15+2056]
	mov QWORD PTR [r12+8], rax
	add r13, 16
	sub r14, 1
	jne 27b
	jmp 26f
25:
26:
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+2064]
	mov rbp, QWORD PTR [r15+2072]
	mov r12, QWORD PTR [r15+2080]
	mov r13, QWORD PTR [r15+2088]
	mov r14, QWORD PTR [r15+2096]
	mov r15, QWORD PTR [r15+2104]
	ret
	.p2align 6
