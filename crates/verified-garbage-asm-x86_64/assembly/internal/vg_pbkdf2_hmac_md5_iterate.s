// The functions of `src/internal/vg_pbkdf2_hmac_md5_iterate.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_md5_iterate:
	mov QWORD PTR [r8], rbx
	mov QWORD PTR [r8+8], rbp
	mov QWORD PTR [r8+16], r12
	mov QWORD PTR [r8+24], r13
	mov QWORD PTR [r8+32], r14
	mov QWORD PTR [r8+40], r15
	mov r15, r8
	mov r12, rdi
	mov r13, rcx
	mov r14d, edx
	mov rbx, r8
	add rbx, 48
	mov rbp, r8
	add rbp, 64
	mov eax, DWORD PTR [rsi]
	mov DWORD PTR [rbp], eax
	mov eax, DWORD PTR [rsi+4]
	mov DWORD PTR [rbp+4], eax
	mov eax, DWORD PTR [rsi+8]
	mov DWORD PTR [rbp+8], eax
	mov eax, DWORD PTR [rsi+12]
	mov DWORD PTR [rbp+12], eax
	mov eax, 128
	mov DWORD PTR [rbp+16], eax
	mov eax, 0
	mov DWORD PTR [rbp+20], eax
	mov DWORD PTR [rbp+24], eax
	mov DWORD PTR [rbp+28], eax
	mov DWORD PTR [rbp+32], eax
	mov DWORD PTR [rbp+36], eax
	mov DWORD PTR [rbp+40], eax
	mov DWORD PTR [rbp+44], eax
	mov DWORD PTR [rbp+48], eax
	mov DWORD PTR [rbp+52], eax
	mov r12d, 80
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	mov QWORD PTR [rbx+72], rax
	mov r12, rdi
	test r14, r14
	je 20f
22:
	mov eax, DWORD PTR [r12]
	mov DWORD PTR [rbx], eax
	mov eax, DWORD PTR [r12+4]
	mov DWORD PTR [rbx+4], eax
	mov eax, DWORD PTR [r12+8]
	mov DWORD PTR [rbx+8], eax
	mov eax, DWORD PTR [r12+12]
	mov DWORD PTR [rbx+12], eax
	mov rsi, rbp
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_md5_compress}
	mov rbx, rdi
	mov r15, rcx
	mov eax, DWORD PTR [rbx]
	mov DWORD PTR [rbp], eax
	mov eax, DWORD PTR [rbx+4]
	mov DWORD PTR [rbp+4], eax
	mov eax, DWORD PTR [rbx+8]
	mov DWORD PTR [rbp+8], eax
	mov eax, DWORD PTR [rbx+12]
	mov DWORD PTR [rbp+12], eax
	mov eax, DWORD PTR [r12+80]
	mov DWORD PTR [rbx], eax
	mov eax, DWORD PTR [r12+84]
	mov DWORD PTR [rbx+4], eax
	mov eax, DWORD PTR [r12+88]
	mov DWORD PTR [rbx+8], eax
	mov eax, DWORD PTR [r12+92]
	mov DWORD PTR [rbx+12], eax
	mov rsi, rbp
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_md5_compress}
	mov rbx, rdi
	mov r15, rcx
	mov eax, DWORD PTR [rbx]
	mov DWORD PTR [rbp], eax
	mov eax, DWORD PTR [rbx+4]
	mov DWORD PTR [rbp+4], eax
	mov eax, DWORD PTR [rbx+8]
	mov DWORD PTR [rbp+8], eax
	mov eax, DWORD PTR [rbx+12]
	mov DWORD PTR [rbp+12], eax
	mov eax, DWORD PTR [rbp]
	xor eax, DWORD PTR [r13]
	mov DWORD PTR [r13], eax
	mov eax, DWORD PTR [rbp+4]
	xor eax, DWORD PTR [r13+4]
	mov DWORD PTR [r13+4], eax
	mov eax, DWORD PTR [rbp+8]
	xor eax, DWORD PTR [r13+8]
	mov DWORD PTR [r13+8], eax
	mov eax, DWORD PTR [rbp+12]
	xor eax, DWORD PTR [r13+12]
	mov DWORD PTR [r13+12], eax
	sub r14, 1
	jne 22b
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15]
	mov rbp, QWORD PTR [r15+8]
	mov r12, QWORD PTR [r15+16]
	mov r13, QWORD PTR [r15+24]
	mov r14, QWORD PTR [r15+32]
	mov r15, QWORD PTR [r15+40]
	ret
	.p2align 6
