// The functions of `src/internal/vg_hmac_sha512_224_finalize_scratch_shani.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_sha512_224_finalize_scratch_shani:
	mov QWORD PTR [r8+48], rbx
	mov QWORD PTR [r8+56], rbp
	mov QWORD PTR [r8+64], r12
	mov QWORD PTR [r8+72], r13
	mov QWORD PTR [r8+80], r14
	mov QWORD PTR [r8+88], r15
	mov rbx, rdi
	mov r12, rsi
	mov r13, rcx
	mov r15, r8
	mov rsi, rdx
	mov rdx, r15
	add rdx, 96
	mov rcx, r15
	call {vg_sha512_finalize_scratch_shani}
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu XMMWORD PTR [rbx], xmm0
	movdqu xmm0, XMMWORD PTR [r12+16]
	movdqu XMMWORD PTR [rbx+16], xmm0
	movdqu xmm0, XMMWORD PTR [r12+32]
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu xmm0, XMMWORD PTR [r12+48]
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu xmm0, XMMWORD PTR [r15+96]
	movdqu XMMWORD PTR [rbx+64], xmm0
	mov rax, QWORD PTR [r15+112]
	mov QWORD PTR [rbx+80], rax
	mov eax, DWORD PTR [r15+120]
	mov DWORD PTR [rbx+88], eax
	mov rbp, rbx
	add rbp, 64
	mov eax, 128
	mov DWORD PTR [rbp+28], eax
	mov eax, 0
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbp+32], xmm0
	movdqu XMMWORD PTR [rbp+48], xmm0
	movdqu XMMWORD PTR [rbp+64], xmm0
	movdqu XMMWORD PTR [rbp+80], xmm0
	movdqu XMMWORD PTR [rbp+96], xmm0
	mov r12d, 156
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	movdqu XMMWORD PTR [rbp+112], xmm7
	mov rsi, rbp
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	mov rax, QWORD PTR [rbx+32]
	bswap rax
	mov QWORD PTR [rbp+32], rax
	mov rax, QWORD PTR [rbx+40]
	bswap rax
	mov QWORD PTR [rbp+40], rax
	mov rax, QWORD PTR [rbx+48]
	bswap rax
	mov QWORD PTR [rbp+48], rax
	mov rax, QWORD PTR [rbx+56]
	bswap rax
	mov QWORD PTR [rbp+56], rax
	movdqu xmm0, XMMWORD PTR [rbp]
	movdqu XMMWORD PTR [r13], xmm0
	mov rax, QWORD PTR [rbp+16]
	mov QWORD PTR [r13+16], rax
	mov eax, DWORD PTR [rbp+24]
	mov DWORD PTR [r13+24], eax
	mov rbx, QWORD PTR [r15+48]
	mov rbp, QWORD PTR [r15+56]
	mov r12, QWORD PTR [r15+64]
	mov r13, QWORD PTR [r15+72]
	mov r14, QWORD PTR [r15+80]
	mov r15, QWORD PTR [r15+88]
	ret
	.p2align 6
