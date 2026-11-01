// The functions of `src/internal/vg_aes_xts_encrypt_aesni.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_xts_encrypt_aesni:
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
	mov r10, r13
	mov r11, r14
	mov rax, QWORD PTR [r12]
	mov rcx, QWORD PTR [r12+8]
22:
	mov rdx, QWORD PTR [r13]
	xor rdx, rax
	mov QWORD PTR [r13], rdx
	mov rdx, QWORD PTR [r13+8]
	xor rdx, rcx
	mov QWORD PTR [r13+8], rdx
	mov rdx, rcx
	add rdx, rdx
	sbb rdx, rdx
	and rdx, 135
	add rax, rax
	adc rcx, rcx
	xor rax, rdx
	add r13, 16
	sub r14, 1
	jne 22b
	mov r13, r10
	mov r14, r11
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r13
	mov rcx, r14
	mov r8, r15
	call {vg_aes_encrypt_blocks_aesni}
	mov rax, QWORD PTR [r12]
	mov rcx, QWORD PTR [r12+8]
23:
	mov rdx, QWORD PTR [r13]
	xor rdx, rax
	mov QWORD PTR [r13], rdx
	mov rdx, QWORD PTR [r13+8]
	xor rdx, rcx
	mov QWORD PTR [r13+8], rdx
	mov rdx, rcx
	add rdx, rdx
	sbb rdx, rdx
	and rdx, 135
	add rax, rax
	adc rcx, rcx
	xor rax, rdx
	add r13, 16
	sub r14, 1
	jne 23b
	mov QWORD PTR [r12], rax
	mov QWORD PTR [r12+8], rcx
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
