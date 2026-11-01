// The functions of `src/internal/vg_sha1_finalize_scratch.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha1_finalize_scratch:
	mov QWORD PTR [rcx+112], rbx
	mov QWORD PTR [rcx+120], rbp
	mov QWORD PTR [rcx+128], r12
	mov QWORD PTR [rcx+136], r13
	mov QWORD PTR [rcx+144], r14
	mov QWORD PTR [rcx+152], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r12, rsi
	mov r13, rsi
	and r13, 63
	mov r9d, 128
	mov r14d, 0
	cmp r13, 56
	jae 20f
	jmp 21f
20:
	mov r14d, 1
21:
22:
	mov rax, r13
	and rax, 15
	je 23f
	mov BYTE PTR [rbx+r13*1+20], r9b
	add r13, 1
	mov eax, 64
	test r14, r14
	je 25f
	jmp 26f
25:
	mov eax, 56
26:
	mov r9d, 0
	sub rax, r13
	cmp rax, 8
	jb 27f
29:
	mov QWORD PTR [rbx+r13*1+20], r9
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
	mov BYTE PTR [rbx+r13*1+20], r9b
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
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+76], rax
214:
	jmp 24f
23:
	movq xmm0, r9
	cmp r13, 48
	jae 215f
217:
	movdqu XMMWORD PTR [rbx+r13*1+20], xmm0
	pxor xmm0, xmm0
	add r13, 16
	cmp r13, 48
	jb 217b
	jmp 216f
215:
216:
	test r14, r14
	je 218f
	jmp 219f
218:
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm7, rax
	pslldq xmm7, 8
	por xmm0, xmm7
219:
	movdqu XMMWORD PTR [rbx+68], xmm0
24:
	mov rsi, rbx
	add rsi, 20
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha1_compress}
	mov rbx, rdi
	mov r15, rcx
	mov r13d, 0
	mov r9d, 0
	sub r14, 1
	je 22b
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
	mov rbx, QWORD PTR [r15+112]
	mov rbp, QWORD PTR [r15+120]
	mov r12, QWORD PTR [r15+128]
	mov r13, QWORD PTR [r15+136]
	mov r14, QWORD PTR [r15+144]
	mov r15, QWORD PTR [r15+152]
	ret
	.p2align 6
