// The functions of `src/cast5_ofb.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cast5_ofb:
	lea rsp, [rsp-240]
	mov r9, rsp
	add r9, 8
	mov r9, r9
	mov QWORD PTR [r9+168], rbx
	mov QWORD PTR [r9+176], rbp
	mov QWORD PTR [r9+184], r12
	mov QWORD PTR [r9+192], r13
	mov QWORD PTR [r9+200], r14
	mov QWORD PTR [r9+208], r15
	movq xmm15, rdx
	mov r12, rcx
	mov r13, r8
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [r9+40], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [r9+48], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [r9+56], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [r9+64], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [r9+72], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [r9+80], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [r9+88], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [r9+96], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [r9+104], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [r9+112], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [r9+120], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [r9+128], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [r9+136], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [r9+144], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [r9+152], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [r9+160], rax
	movq rax, xmm15
	mov rbp, QWORD PTR [rax]
	mov QWORD PTR [r9+16], rbp
	test r13, r13
	je 20f
22:
	movq rcx, xmm15
	mov r8, r9
	mov QWORD PTR [r8+24], r12
	mov QWORD PTR [r8+32], r13
	mov rdx, r9
	add rdx, 16
	mov rdi, r9
	add rdi, 40
	mov ebx, DWORD PTR [rdx]
	bswap ebx
	mov ebp, DWORD PTR [rdx+4]
	bswap ebp
	mov r12, rdi
	mov r13, rsi
	shr r13, 2
	add r13, 1
	cmp rsi, 16
23:
	mov eax, DWORD PTR [r12]
	add eax, ebp
	mov r9d, DWORD PTR [r12+64]
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 31
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 30
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 28
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 24
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 16
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	mov r9d, eax
	and r9d, 255
	mov r14d, eax
	shr r14d, 8
	and r14d, 255
	shl r14, 32
	or r9, r14
	movq xmm0, r9
	mov r9d, eax
	shr r9d, 16
	and r9d, 255
	mov r14d, eax
	shr r14d, 24
	shl r14, 32
	or r9, r14
	movq xmm4, r9
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S1234}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
24:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 24b
	movdqu XMMWORD PTR [r8], xmm1
	mov eax, DWORD PTR [r8+12]
	xor eax, DWORD PTR [r8+8]
	sub eax, DWORD PTR [r8+4]
	add eax, DWORD PTR [r8]
	xor eax, ebx
	mov ebx, ebp
	mov ebp, eax
	add r12, 4
	mov eax, DWORD PTR [r12]
	xor eax, ebp
	mov r9d, DWORD PTR [r12+64]
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 31
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 30
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 28
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 24
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 16
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	mov r9d, eax
	and r9d, 255
	mov r14d, eax
	shr r14d, 8
	and r14d, 255
	shl r14, 32
	or r9, r14
	movq xmm0, r9
	mov r9d, eax
	shr r9d, 16
	and r9d, 255
	mov r14d, eax
	shr r14d, 24
	shl r14, 32
	or r9, r14
	movq xmm4, r9
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S1234}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
25:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 25b
	movdqu XMMWORD PTR [r8], xmm1
	mov eax, DWORD PTR [r8+12]
	sub eax, DWORD PTR [r8+8]
	add eax, DWORD PTR [r8+4]
	xor eax, DWORD PTR [r8]
	xor eax, ebx
	mov ebx, ebp
	mov ebp, eax
	add r12, 4
	mov eax, DWORD PTR [r12]
	sub eax, ebp
	mov r9d, DWORD PTR [r12+64]
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 31
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 30
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 28
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 24
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 16
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	mov r9d, eax
	and r9d, 255
	mov r14d, eax
	shr r14d, 8
	and r14d, 255
	shl r14, 32
	or r9, r14
	movq xmm0, r9
	mov r9d, eax
	shr r9d, 16
	and r9d, 255
	mov r14d, eax
	shr r14d, 24
	shl r14, 32
	or r9, r14
	movq xmm4, r9
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S1234}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
26:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 26b
	movdqu XMMWORD PTR [r8], xmm1
	mov eax, DWORD PTR [r8+12]
	add eax, DWORD PTR [r8+8]
	xor eax, DWORD PTR [r8+4]
	sub eax, DWORD PTR [r8]
	xor eax, ebx
	mov ebx, ebp
	mov ebp, eax
	add r12, 4
	sub r13, 1
	jne 23b
	cmp rsi, 16
	je 27f
	jmp 28f
27:
	mov eax, DWORD PTR [r12]
	add eax, ebp
	mov r9d, DWORD PTR [r12+64]
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 31
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 30
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 28
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 24
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	shr r9d, 1
	mov r14d, r9d
	and r14d, 1
	sub r14d, 1
	mov r15d, eax
	ror r15d, 16
	xor eax, r15d
	and eax, r14d
	xor eax, r15d
	mov r9d, eax
	and r9d, 255
	mov r14d, eax
	shr r14d, 8
	and r14d, 255
	shl r14, 32
	or r9, r14
	movq xmm0, r9
	mov r9d, eax
	shr r9d, 16
	and r9d, 255
	mov r14d, eax
	shr r14d, 24
	shl r14, 32
	or r9, r14
	movq xmm4, r9
	punpcklqdq xmm0, xmm4
	lea r10, {VG_CAST5_S1234}
	mov r11d, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pcmpeqd xmm3, xmm3
	psrld xmm3, 31
	movdqa xmm4, xmm0
	pand xmm4, xmm3
	pxor xmm6, xmm6
	psubd xmm6, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 1
	pand xmm4, xmm3
	pxor xmm7, xmm7
	psubd xmm7, xmm4
	movdqa xmm8, xmm0
	psrld xmm8, 2
29:
	movdqu xmm4, XMMWORD PTR [r10]
	movdqu xmm5, XMMWORD PTR [r10+16]
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm9, XMMWORD PTR [r10+32]
	movdqu xmm5, XMMWORD PTR [r10+48]
	pxor xmm5, xmm9
	pand xmm5, xmm6
	pxor xmm9, xmm5
	pxor xmm9, xmm4
	pand xmm9, xmm7
	pxor xmm4, xmm9
	movdqa xmm5, xmm8
	pcmpeqd xmm5, xmm2
	pand xmm4, xmm5
	por xmm1, xmm4
	paddd xmm2, xmm3
	add r10, 64
	sub r11, 1
	jne 29b
	movdqu XMMWORD PTR [r8], xmm1
	mov eax, DWORD PTR [r8+12]
	xor eax, DWORD PTR [r8+8]
	sub eax, DWORD PTR [r8+4]
	add eax, DWORD PTR [r8]
	xor eax, ebx
	mov ebx, ebp
	mov ebp, eax
	add r12, 4
28:
	bswap ebp
	mov DWORD PTR [rdx], ebp
	bswap ebx
	mov DWORD PTR [rdx+4], ebx
	add rdx, 8
	sub rcx, 1
	mov r12, QWORD PTR [r8+24]
	mov r13, QWORD PTR [r8+32]
	mov r9, r8
	add rcx, 1
	movq xmm15, rcx
	mov rax, QWORD PTR [r12]
	xor rax, QWORD PTR [r9+16]
	mov QWORD PTR [r12], rax
	add r12, 8
	sub r13, 1
	jne 22b
	jmp 21f
20:
21:
	movq rax, xmm15
	mov rbp, QWORD PTR [r9+16]
	mov QWORD PTR [rax], rbp
	mov rbx, QWORD PTR [r9+168]
	mov rbp, QWORD PTR [r9+176]
	mov r12, QWORD PTR [r9+184]
	mov r13, QWORD PTR [r9+192]
	mov r14, QWORD PTR [r9+200]
	mov r15, QWORD PTR [r9+208]
	mov r11d, 0
	mov QWORD PTR [rsp+8], r11
	mov QWORD PTR [rsp+16], r11
	mov QWORD PTR [rsp+24], r11
	mov QWORD PTR [rsp+32], r11
	mov QWORD PTR [rsp+40], r11
	mov QWORD PTR [rsp+48], r11
	mov QWORD PTR [rsp+56], r11
	mov QWORD PTR [rsp+64], r11
	mov QWORD PTR [rsp+72], r11
	mov QWORD PTR [rsp+80], r11
	mov QWORD PTR [rsp+88], r11
	mov QWORD PTR [rsp+96], r11
	mov QWORD PTR [rsp+104], r11
	mov QWORD PTR [rsp+112], r11
	mov QWORD PTR [rsp+120], r11
	mov QWORD PTR [rsp+128], r11
	mov QWORD PTR [rsp+136], r11
	mov QWORD PTR [rsp+144], r11
	mov QWORD PTR [rsp+152], r11
	mov QWORD PTR [rsp+160], r11
	mov QWORD PTR [rsp+168], r11
	mov QWORD PTR [rsp+176], r11
	mov QWORD PTR [rsp+184], r11
	mov QWORD PTR [rsp+192], r11
	mov QWORD PTR [rsp+200], r11
	mov QWORD PTR [rsp+208], r11
	mov QWORD PTR [rsp+216], r11
	mov QWORD PTR [rsp+224], r11
	mov QWORD PTR [rsp+232], r11
	lea rsp, [rsp+240]
	ret
	.p2align 6
