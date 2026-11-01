// The functions of `src/internal/vg_hmac_md5_finalize_scratch.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_md5_finalize_scratch:
	mov QWORD PTR [r8+112], rbx
	mov QWORD PTR [r8+120], rbp
	mov QWORD PTR [r8+128], r12
	mov QWORD PTR [r8+136], r13
	mov QWORD PTR [r8+144], r14
	mov QWORD PTR [r8+152], r15
	mov rbx, rdi
	mov r12, rsi
	mov r13, rcx
	mov r15, r8
	mov rsi, rdx
	mov rdx, r15
	add rdx, 160
	mov rcx, r15
	call {vg_md5_finalize_scratch}
	mov eax, DWORD PTR [r12]
	mov DWORD PTR [rbx], eax
	mov eax, DWORD PTR [r12+4]
	mov DWORD PTR [rbx+4], eax
	mov eax, DWORD PTR [r12+8]
	mov DWORD PTR [rbx+8], eax
	mov eax, DWORD PTR [r12+12]
	mov DWORD PTR [rbx+12], eax
	mov eax, DWORD PTR [r15+160]
	mov DWORD PTR [rbx+16], eax
	mov eax, DWORD PTR [r15+164]
	mov DWORD PTR [rbx+20], eax
	mov eax, DWORD PTR [r15+168]
	mov DWORD PTR [rbx+24], eax
	mov eax, DWORD PTR [r15+172]
	mov DWORD PTR [rbx+28], eax
	mov rbp, rbx
	add rbp, 16
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
	mov rsi, rbp
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_md5_compress}
	mov rbx, rdi
	mov r15, rcx
	mov rbp, r13
	mov eax, DWORD PTR [rbx]
	mov DWORD PTR [rbp], eax
	mov eax, DWORD PTR [rbx+4]
	mov DWORD PTR [rbp+4], eax
	mov eax, DWORD PTR [rbx+8]
	mov DWORD PTR [rbp+8], eax
	mov eax, DWORD PTR [rbx+12]
	mov DWORD PTR [rbp+12], eax
	mov rbx, QWORD PTR [r15+112]
	mov rbp, QWORD PTR [r15+120]
	mov r12, QWORD PTR [r15+128]
	mov r13, QWORD PTR [r15+136]
	mov r14, QWORD PTR [r15+144]
	mov r15, QWORD PTR [r15+152]
	ret
	.p2align 6
