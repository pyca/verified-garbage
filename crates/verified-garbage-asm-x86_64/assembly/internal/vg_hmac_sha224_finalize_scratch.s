// The functions of `src/internal/vg_hmac_sha224_finalize_scratch.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_sha224_finalize_scratch:
	mov QWORD PTR [r8+608], rbx
	mov QWORD PTR [r8+616], rbp
	mov QWORD PTR [r8+624], r12
	mov QWORD PTR [r8+632], r13
	mov QWORD PTR [r8+640], r14
	mov QWORD PTR [r8+648], r15
	mov rbx, rdi
	mov r12, rsi
	mov r13, rcx
	mov r15, r8
	mov rsi, rdx
	mov rdx, r15
	add rdx, 656
	mov rcx, r15
	call {vg_sha256_finalize_scratch}
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
	mov eax, DWORD PTR [r15+656]
	mov DWORD PTR [rbx+32], eax
	mov eax, DWORD PTR [r15+660]
	mov DWORD PTR [rbx+36], eax
	mov eax, DWORD PTR [r15+664]
	mov DWORD PTR [rbx+40], eax
	mov eax, DWORD PTR [r15+668]
	mov DWORD PTR [rbx+44], eax
	mov eax, DWORD PTR [r15+672]
	mov DWORD PTR [rbx+48], eax
	mov eax, DWORD PTR [r15+676]
	mov DWORD PTR [rbx+52], eax
	mov eax, DWORD PTR [r15+680]
	mov DWORD PTR [rbx+56], eax
	mov rbp, rbx
	add rbp, 32
	mov eax, 128
	mov DWORD PTR [rbp+28], eax
	mov eax, 0
	mov DWORD PTR [rbp+32], eax
	mov DWORD PTR [rbp+36], eax
	mov DWORD PTR [rbp+40], eax
	mov DWORD PTR [rbp+44], eax
	mov DWORD PTR [rbp+48], eax
	mov DWORD PTR [rbp+52], eax
	mov r12d, 92
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+88], rax
	mov rsi, rbp
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress}
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
	mov DWORD PTR [r13], eax
	mov eax, DWORD PTR [rbp+4]
	mov DWORD PTR [r13+4], eax
	mov eax, DWORD PTR [rbp+8]
	mov DWORD PTR [r13+8], eax
	mov eax, DWORD PTR [rbp+12]
	mov DWORD PTR [r13+12], eax
	mov eax, DWORD PTR [rbp+16]
	mov DWORD PTR [r13+16], eax
	mov eax, DWORD PTR [rbp+20]
	mov DWORD PTR [r13+20], eax
	mov eax, DWORD PTR [rbp+24]
	mov DWORD PTR [r13+24], eax
	mov rbx, QWORD PTR [r15+608]
	mov rbp, QWORD PTR [r15+616]
	mov r12, QWORD PTR [r15+624]
	mov r13, QWORD PTR [r15+632]
	mov r14, QWORD PTR [r15+640]
	mov r15, QWORD PTR [r15+648]
	ret
	.p2align 6
