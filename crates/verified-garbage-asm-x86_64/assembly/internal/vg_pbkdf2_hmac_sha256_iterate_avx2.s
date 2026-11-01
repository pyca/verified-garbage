// The functions of `src/internal/vg_pbkdf2_hmac_sha256_iterate_avx2.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_sha256_iterate_avx2:
	mov QWORD PTR [r8+560], rbx
	mov QWORD PTR [r8+568], rbp
	mov QWORD PTR [r8+576], r12
	mov QWORD PTR [r8+584], r13
	mov QWORD PTR [r8+592], r14
	mov QWORD PTR [r8+600], r15
	mov r15, r8
	mov r12, rdi
	mov r13, rcx
	mov r14d, edx
	mov rbx, r8
	add rbx, 608
	mov rbp, r8
	add rbp, 640
	mov eax, DWORD PTR [rsi]
	mov DWORD PTR [rbp], eax
	mov eax, DWORD PTR [rsi+4]
	mov DWORD PTR [rbp+4], eax
	mov eax, DWORD PTR [rsi+8]
	mov DWORD PTR [rbp+8], eax
	mov eax, DWORD PTR [rsi+12]
	mov DWORD PTR [rbp+12], eax
	mov eax, DWORD PTR [rsi+16]
	mov DWORD PTR [rbp+16], eax
	mov eax, DWORD PTR [rsi+20]
	mov DWORD PTR [rbp+20], eax
	mov eax, DWORD PTR [rsi+24]
	mov DWORD PTR [rbp+24], eax
	mov eax, DWORD PTR [rsi+28]
	mov DWORD PTR [rbp+28], eax
	mov eax, 128
	mov DWORD PTR [rbp+32], eax
	mov eax, 0
	mov DWORD PTR [rbp+36], eax
	mov DWORD PTR [rbp+40], eax
	mov DWORD PTR [rbp+44], eax
	mov DWORD PTR [rbp+48], eax
	mov DWORD PTR [rbp+52], eax
	mov r12d, 96
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+88], rax
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
	mov eax, DWORD PTR [r12+16]
	mov DWORD PTR [rbx+16], eax
	mov eax, DWORD PTR [r12+20]
	mov DWORD PTR [rbx+20], eax
	mov eax, DWORD PTR [r12+24]
	mov DWORD PTR [rbx+24], eax
	mov eax, DWORD PTR [r12+28]
	mov DWORD PTR [rbx+28], eax
	mov rsi, rbp
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov eax, DWORD PTR [rbx]
	bswap eax
	mov DWORD PTR [rbp], eax
	mov eax, DWORD PTR [rbx+4]
	bswap eax
	mov DWORD PTR [rbp+4], eax
	mov eax, DWORD PTR [rbx+8]
	bswap eax
	mov DWORD PTR [rbp+8], eax
	mov eax, DWORD PTR [rbx+12]
	bswap eax
	mov DWORD PTR [rbp+12], eax
	mov eax, DWORD PTR [rbx+16]
	bswap eax
	mov DWORD PTR [rbp+16], eax
	mov eax, DWORD PTR [rbx+20]
	bswap eax
	mov DWORD PTR [rbp+20], eax
	mov eax, DWORD PTR [rbx+24]
	bswap eax
	mov DWORD PTR [rbp+24], eax
	mov eax, DWORD PTR [rbx+28]
	bswap eax
	mov DWORD PTR [rbp+28], eax
	mov eax, DWORD PTR [r12+96]
	mov DWORD PTR [rbx], eax
	mov eax, DWORD PTR [r12+100]
	mov DWORD PTR [rbx+4], eax
	mov eax, DWORD PTR [r12+104]
	mov DWORD PTR [rbx+8], eax
	mov eax, DWORD PTR [r12+108]
	mov DWORD PTR [rbx+12], eax
	mov eax, DWORD PTR [r12+112]
	mov DWORD PTR [rbx+16], eax
	mov eax, DWORD PTR [r12+116]
	mov DWORD PTR [rbx+20], eax
	mov eax, DWORD PTR [r12+120]
	mov DWORD PTR [rbx+24], eax
	mov eax, DWORD PTR [r12+124]
	mov DWORD PTR [rbx+28], eax
	mov rsi, rbp
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov eax, DWORD PTR [rbx]
	bswap eax
	mov DWORD PTR [rbp], eax
	mov eax, DWORD PTR [rbx+4]
	bswap eax
	mov DWORD PTR [rbp+4], eax
	mov eax, DWORD PTR [rbx+8]
	bswap eax
	mov DWORD PTR [rbp+8], eax
	mov eax, DWORD PTR [rbx+12]
	bswap eax
	mov DWORD PTR [rbp+12], eax
	mov eax, DWORD PTR [rbx+16]
	bswap eax
	mov DWORD PTR [rbp+16], eax
	mov eax, DWORD PTR [rbx+20]
	bswap eax
	mov DWORD PTR [rbp+20], eax
	mov eax, DWORD PTR [rbx+24]
	bswap eax
	mov DWORD PTR [rbp+24], eax
	mov eax, DWORD PTR [rbx+28]
	bswap eax
	mov DWORD PTR [rbp+28], eax
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
	mov eax, DWORD PTR [rbp+16]
	xor eax, DWORD PTR [r13+16]
	mov DWORD PTR [r13+16], eax
	mov eax, DWORD PTR [rbp+20]
	xor eax, DWORD PTR [r13+20]
	mov DWORD PTR [r13+20], eax
	mov eax, DWORD PTR [rbp+24]
	xor eax, DWORD PTR [r13+24]
	mov DWORD PTR [r13+24], eax
	mov eax, DWORD PTR [rbp+28]
	xor eax, DWORD PTR [r13+28]
	mov DWORD PTR [r13+28], eax
	sub r14, 1
	jne 22b
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+560]
	mov rbp, QWORD PTR [r15+568]
	mov r12, QWORD PTR [r15+576]
	mov r13, QWORD PTR [r15+584]
	mov r14, QWORD PTR [r15+592]
	mov r15, QWORD PTR [r15+600]
	ret
	.p2align 6
