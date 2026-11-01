// The functions of `src/aes_cfb8.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_cfb8_encrypt_aesni:
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
22:
	mov rax, QWORD PTR [r12]
	mov QWORD PTR [r15+2048], rax
	mov rax, QWORD PTR [r12+8]
	mov QWORD PTR [r15+2056], rax
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2048
	mov ecx, 1
	mov r8, r15
	call {vg_aes_encrypt_blocks_aesni}
	movzx eax, BYTE PTR [r13]
	movzx ecx, BYTE PTR [r15+2048]
	xor rax, rcx
	mov BYTE PTR [r13], al
	mov rcx, QWORD PTR [r12+1]
	mov rdx, QWORD PTR [r12+8]
	mov QWORD PTR [r12], rcx
	mov QWORD PTR [r12+7], rdx
	mov BYTE PTR [r12+15], al
	add r13, 1
	sub r14, 1
	jne 22b
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

vg_aes_cfb8_decrypt_aesni:
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
22:
	mov rax, QWORD PTR [r12]
	mov QWORD PTR [r15+2048], rax
	mov rax, QWORD PTR [r12+8]
	mov QWORD PTR [r15+2056], rax
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2048
	mov ecx, 1
	mov r8, r15
	call {vg_aes_encrypt_blocks_aesni}
	movzx eax, BYTE PTR [r13]
	movzx ecx, BYTE PTR [r15+2048]
	xor rcx, rax
	mov BYTE PTR [r13], cl
	mov rcx, QWORD PTR [r12+1]
	mov rdx, QWORD PTR [r12+8]
	mov QWORD PTR [r12], rcx
	mov QWORD PTR [r12+7], rdx
	mov BYTE PTR [r12+15], al
	add r13, 1
	sub r14, 1
	jne 22b
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

vg_aes_cfb8_encrypt:
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
22:
	mov rax, QWORD PTR [r12]
	mov QWORD PTR [r15+2048], rax
	mov rax, QWORD PTR [r12+8]
	mov QWORD PTR [r15+2056], rax
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2048
	mov ecx, 1
	mov r8, r15
	call {vg_aes_encrypt_blocks}
	movzx eax, BYTE PTR [r13]
	movzx ecx, BYTE PTR [r15+2048]
	xor rax, rcx
	mov BYTE PTR [r13], al
	mov rcx, QWORD PTR [r12+1]
	mov rdx, QWORD PTR [r12+8]
	mov QWORD PTR [r12], rcx
	mov QWORD PTR [r12+7], rdx
	mov BYTE PTR [r12+15], al
	add r13, 1
	sub r14, 1
	jne 22b
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

vg_aes_cfb8_decrypt:
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
22:
	mov rax, QWORD PTR [r12]
	mov QWORD PTR [r15+2048], rax
	mov rax, QWORD PTR [r12+8]
	mov QWORD PTR [r15+2056], rax
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2048
	mov ecx, 1
	mov r8, r15
	call {vg_aes_encrypt_blocks}
	movzx eax, BYTE PTR [r13]
	movzx ecx, BYTE PTR [r15+2048]
	xor rcx, rax
	mov BYTE PTR [r13], cl
	mov rcx, QWORD PTR [r12+1]
	mov rdx, QWORD PTR [r12+8]
	mov QWORD PTR [r12], rcx
	mov QWORD PTR [r12+7], rdx
	mov BYTE PTR [r12+15], al
	add r13, 1
	sub r14, 1
	jne 22b
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

vg_aes_cfb8_encrypt_vaes:
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
22:
	mov rax, QWORD PTR [r12]
	mov QWORD PTR [r15+2048], rax
	mov rax, QWORD PTR [r12+8]
	mov QWORD PTR [r15+2056], rax
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2048
	mov ecx, 1
	mov r8, r15
	call {vg_aes_encrypt_blocks_vaes}
	movzx eax, BYTE PTR [r13]
	movzx ecx, BYTE PTR [r15+2048]
	xor rax, rcx
	mov BYTE PTR [r13], al
	mov rcx, QWORD PTR [r12+1]
	mov rdx, QWORD PTR [r12+8]
	mov QWORD PTR [r12], rcx
	mov QWORD PTR [r12+7], rdx
	mov BYTE PTR [r12+15], al
	add r13, 1
	sub r14, 1
	jne 22b
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

vg_aes_cfb8_decrypt_vaes:
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
22:
	mov rax, QWORD PTR [r12]
	mov QWORD PTR [r15+2048], rax
	mov rax, QWORD PTR [r12+8]
	mov QWORD PTR [r15+2056], rax
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2048
	mov ecx, 1
	mov r8, r15
	call {vg_aes_encrypt_blocks_vaes}
	movzx eax, BYTE PTR [r13]
	movzx ecx, BYTE PTR [r15+2048]
	xor rcx, rax
	mov BYTE PTR [r13], cl
	mov rcx, QWORD PTR [r12+1]
	mov rdx, QWORD PTR [r12+8]
	mov QWORD PTR [r12], rcx
	mov QWORD PTR [r12+7], rdx
	mov BYTE PTR [r12+15], al
	add r13, 1
	sub r14, 1
	jne 22b
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
