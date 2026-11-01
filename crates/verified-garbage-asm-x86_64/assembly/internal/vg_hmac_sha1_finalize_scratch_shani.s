// The functions of `src/internal/vg_hmac_sha1_finalize_scratch_shani.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_sha1_finalize_scratch_shani:
	mov QWORD PTR [r8+160], rbx
	mov QWORD PTR [r8+168], rbp
	mov QWORD PTR [r8+176], r12
	mov QWORD PTR [r8+184], r13
	mov QWORD PTR [r8+192], r14
	mov QWORD PTR [r8+200], r15
	mov rbx, rdi
	mov r12, rsi
	mov r13, rcx
	mov r15, r8
	mov rsi, rdx
	mov rdx, r15
	add rdx, 208
	mov rcx, r15
	call {vg_sha1_finalize_scratch_shani}
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
	mov eax, DWORD PTR [r15+208]
	mov DWORD PTR [rbx+20], eax
	mov eax, DWORD PTR [r15+212]
	mov DWORD PTR [rbx+24], eax
	mov eax, DWORD PTR [r15+216]
	mov DWORD PTR [rbx+28], eax
	mov eax, DWORD PTR [r15+220]
	mov DWORD PTR [rbx+32], eax
	mov eax, DWORD PTR [r15+224]
	mov DWORD PTR [rbx+36], eax
	mov rbp, rbx
	add rbp, 20
	mov eax, 128
	mov DWORD PTR [rbp+20], eax
	mov eax, 0
	mov DWORD PTR [rbp+24], eax
	mov DWORD PTR [rbp+28], eax
	mov DWORD PTR [rbp+32], eax
	mov DWORD PTR [rbp+36], eax
	mov DWORD PTR [rbp+40], eax
	mov DWORD PTR [rbp+44], eax
	mov DWORD PTR [rbp+48], eax
	mov DWORD PTR [rbp+52], eax
	mov r12d, 84
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+76], rax
	mov rsi, rbp
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha1_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov rbp, r13
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
	mov rbx, QWORD PTR [r15+160]
	mov rbp, QWORD PTR [r15+168]
	mov r12, QWORD PTR [r15+176]
	mov r13, QWORD PTR [r15+184]
	mov r14, QWORD PTR [r15+192]
	mov r15, QWORD PTR [r15+200]
	ret
	.p2align 6
