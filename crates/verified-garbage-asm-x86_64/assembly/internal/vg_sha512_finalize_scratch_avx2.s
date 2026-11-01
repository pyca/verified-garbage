// The functions of `src/internal/vg_sha512_finalize_scratch_avx2.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha512_finalize_scratch_avx2:
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 127
	mov r9d, 128
	mov r14d, 0
	cmp r13, 112
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+64], r9b
	add r13, 1
	mov eax, 128
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 112
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+64], r9
	add r13, 8
	sub rax, 8
	cmp rax, 8
	jae 29b
	jmp 28f
27:
28:
	test rax, rax
	je 210f
212:
	mov BYTE PTR [rbx+r13*1+64], r9b
	add r13, 1
	sub rax, 1
	jne 212b
	jmp 211f
210:
211:
	test r14, r14
	je 213f
	jmp 214f
213:
	mov rax, r12
	shr rax, 61
	bswap rax
	mov QWORD PTR [rbx+176], rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+184], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 112
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+64], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 112
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
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
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+176], xmm0
24:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
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
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	ret
	.p2align 6
