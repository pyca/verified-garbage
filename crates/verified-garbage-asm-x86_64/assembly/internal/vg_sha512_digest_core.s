// The functions of `src/internal/vg_sha512_digest_core.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha512_digest_core:
	lea rsp, [rsp-1592]
	mov rcx, rsp
	add rcx, 8
	add rcx, 192
	mov QWORD PTR [rcx+1328], rbx
	mov QWORD PTR [rcx+1336], rbp
	mov QWORD PTR [rcx+1344], r12
	mov QWORD PTR [rcx+1352], r13
	mov QWORD PTR [rcx+1360], r14
	mov QWORD PTR [rcx+1368], r15
	mov r15, rcx
	mov rbx, rcx
	sub rbx, 192
	mov r13, rdi
	mov r12, rsi
	mov rbp, rdx
	mov rdi, rbx
	movabs rax, 7640891576956012808
	mov QWORD PTR [rdi], rax
	movabs rax, -4942790177534073029
	mov QWORD PTR [rdi+8], rax
	movabs rax, 4354685564936845355
	mov QWORD PTR [rdi+16], rax
	movabs rax, -6534734903238641935
	mov QWORD PTR [rdi+24], rax
	movabs rax, 5840696475078001361
	mov QWORD PTR [rdi+32], rax
	movabs rax, -7276294671716946913
	mov QWORD PTR [rdi+40], rax
	movabs rax, 2270897969802886507
	mov QWORD PTR [rdi+48], rax
	movabs rax, 6620516959819538809
	mov QWORD PTR [rdi+56], rax
	mov r14, r12
	shr r14, 7
	test r14, r14
	je 20f
	mov rsi, r13
	mov rdi, rbx
	mov rdx, r14
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
	mov rax, r14
	shl rax, 7
	add r13, rax
	jmp 21f
20:
21:
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov r10, r12
	and r10, 127
	mov r11d, 0
	mov r9, r10
	shr r9, 4
	je 22f
24:
	movdqu xmm1, XMMWORD PTR [r13]
	mov ecx, 112
	cmp r11, rcx
	cmovb rcx, r11
	movdqu XMMWORD PTR [rbx+rcx*1+64], xmm1
	add r13, 16
	add r11, 16
	sub r9, 1
	jne 24b
	jmp 23f
22:
23:
	mov rax, r10
	and rax, 15
	je 25f
	cmp r12, 8
	jb 27f
	cmp rax, 8
	jb 29f
	mov r8, QWORD PTR [r13]
	mov r9, QWORD PTR [r13+rax*1-8]
	mov ecx, 15
	sub rcx, rax
	shl rcx, 3
	shr r9, cl
	shr r9, 8
	mov rcx, rax
	sub rcx, 8
	shl rcx, 3
	mov edx, 128
	shl rdx, cl
	or r9, rdx
	movq xmm1, r8
	movq xmm2, r9
	punpcklqdq xmm1, xmm2
	mov ecx, 112
	cmp r11, rcx
	cmovb rcx, r11
	movdqu XMMWORD PTR [rbx+rcx*1+64], xmm1
	jmp 210f
29:
	mov r8, QWORD PTR [r13+rax*1-8]
	mov ecx, 8
	sub rcx, rax
	shl rcx, 3
	shr r8, cl
	mov rcx, rax
	shl rcx, 3
	mov r9d, 128
	shl r9, cl
	or r8, r9
	movq xmm1, r8
	mov ecx, 112
	cmp r11, rcx
	cmovb rcx, r11
	movdqu XMMWORD PTR [rbx+rcx*1+64], xmm1
210:
	jmp 28f
27:
	test rax, rax
	je 211f
213:
	movzx r8d, BYTE PTR [r13]
	mov ecx, 127
	cmp r11, rcx
	cmovb rcx, r11
	mov BYTE PTR [rbx+rcx*1+64], r8b
	add r13, 1
	add r11, 1
	sub rax, 1
	jne 213b
	jmp 212f
211:
212:
	mov r8d, 128
	mov ecx, 127
	cmp r11, rcx
	cmovb rcx, r11
	mov BYTE PTR [rbx+rcx*1+64], r8b
28:
	jmp 26f
25:
	mov r8d, 128
	movq xmm1, r8
	mov ecx, 112
	cmp r11, rcx
	cmovb rcx, r11
	movdqu XMMWORD PTR [rbx+rcx*1+64], xmm1
26:
	cmp r10, 112
	jae 214f
	jmp 215f
214:
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
215:
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
	movdqu xmm0, XMMWORD PTR [rbx+176]
	por xmm0, xmm7
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress}
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
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbx], xmm0
	movdqu XMMWORD PTR [rbx+16], xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu XMMWORD PTR [rbx+96], xmm0
	movdqu XMMWORD PTR [rbx+112], xmm0
	movdqu XMMWORD PTR [rbx+128], xmm0
	movdqu XMMWORD PTR [rbx+144], xmm0
	movdqu XMMWORD PTR [rbx+160], xmm0
	movdqu XMMWORD PTR [rbx+176], xmm0
	mov rbx, QWORD PTR [r15+1328]
	mov rbp, QWORD PTR [r15+1336]
	mov r12, QWORD PTR [r15+1344]
	mov r13, QWORD PTR [r15+1352]
	mov r14, QWORD PTR [r15+1360]
	mov r15, QWORD PTR [r15+1368]
	lea rsp, [rsp+1592]
	ret
	.p2align 6
