// The functions of `src/internal/vg_hmac_md5_init_scratch.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_md5_init_scratch:
	mov QWORD PTR [r8+112], rbx
	mov QWORD PTR [r8+120], rbp
	mov QWORD PTR [r8+128], r12
	mov QWORD PTR [r8+136], r13
	mov QWORD PTR [r8+144], r14
	mov QWORD PTR [r8+152], r15
	mov rbx, rdi
	mov r12, rsi
	mov r15, r8
	mov rbp, rdx
	mov r13, rcx
	mov rdi, rbx
	call {vg_md5_init}
	mov rdi, r12
	call {vg_md5_init}
	mov eax, 909522486
	mov DWORD PTR [rbx+16], eax
	mov DWORD PTR [rbx+20], eax
	mov DWORD PTR [rbx+24], eax
	mov DWORD PTR [rbx+28], eax
	mov DWORD PTR [rbx+32], eax
	mov DWORD PTR [rbx+36], eax
	mov DWORD PTR [rbx+40], eax
	mov DWORD PTR [rbx+44], eax
	mov DWORD PTR [rbx+48], eax
	mov DWORD PTR [rbx+52], eax
	mov DWORD PTR [rbx+56], eax
	mov DWORD PTR [rbx+60], eax
	mov DWORD PTR [rbx+64], eax
	mov DWORD PTR [rbx+68], eax
	mov DWORD PTR [rbx+72], eax
	mov DWORD PTR [rbx+76], eax
	mov r14d, 0
	test r13, r13
	je 20f
22:
	movzx eax, BYTE PTR [rbp+r14*1]
	xor eax, 54
	mov BYTE PTR [rbx+r14*1+16], al
	add r14, 1
	cmp r14, r13
	jne 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [rbx+16]
	xor eax, 1785358954
	mov DWORD PTR [r12+16], eax
	mov eax, DWORD PTR [rbx+20]
	xor eax, 1785358954
	mov DWORD PTR [r12+20], eax
	mov eax, DWORD PTR [rbx+24]
	xor eax, 1785358954
	mov DWORD PTR [r12+24], eax
	mov eax, DWORD PTR [rbx+28]
	xor eax, 1785358954
	mov DWORD PTR [r12+28], eax
	mov eax, DWORD PTR [rbx+32]
	xor eax, 1785358954
	mov DWORD PTR [r12+32], eax
	mov eax, DWORD PTR [rbx+36]
	xor eax, 1785358954
	mov DWORD PTR [r12+36], eax
	mov eax, DWORD PTR [rbx+40]
	xor eax, 1785358954
	mov DWORD PTR [r12+40], eax
	mov eax, DWORD PTR [rbx+44]
	xor eax, 1785358954
	mov DWORD PTR [r12+44], eax
	mov eax, DWORD PTR [rbx+48]
	xor eax, 1785358954
	mov DWORD PTR [r12+48], eax
	mov eax, DWORD PTR [rbx+52]
	xor eax, 1785358954
	mov DWORD PTR [r12+52], eax
	mov eax, DWORD PTR [rbx+56]
	xor eax, 1785358954
	mov DWORD PTR [r12+56], eax
	mov eax, DWORD PTR [rbx+60]
	xor eax, 1785358954
	mov DWORD PTR [r12+60], eax
	mov eax, DWORD PTR [rbx+64]
	xor eax, 1785358954
	mov DWORD PTR [r12+64], eax
	mov eax, DWORD PTR [rbx+68]
	xor eax, 1785358954
	mov DWORD PTR [r12+68], eax
	mov eax, DWORD PTR [rbx+72]
	xor eax, 1785358954
	mov DWORD PTR [r12+72], eax
	mov eax, DWORD PTR [rbx+76]
	xor eax, 1785358954
	mov DWORD PTR [r12+76], eax
	mov rsi, rbx
	add rsi, 16
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_md5_compress}
	mov rbx, rdi
	mov r15, rcx
	mov rbx, r12
	mov rsi, r12
	add rsi, 16
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_md5_compress}
	mov rbx, rdi
	mov r15, rcx
	mov rbx, QWORD PTR [r15+112]
	mov rbp, QWORD PTR [r15+120]
	mov r12, QWORD PTR [r15+128]
	mov r13, QWORD PTR [r15+136]
	mov r14, QWORD PTR [r15+144]
	mov r15, QWORD PTR [r15+152]
	ret
	.p2align 6
