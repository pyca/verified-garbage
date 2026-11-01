// The functions of `src/blowfish_cbc.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blowfish_cbc_encrypt_chained:
	lea rsp, [rsp-96]
	mov r8, rsp
	add r8, 8
	mov r9, r8
	mov QWORD PTR [r9+24], rbx
	mov QWORD PTR [r9+32], rbp
	mov QWORD PTR [r9+40], r12
	mov QWORD PTR [r9+48], r13
	mov QWORD PTR [r9+56], r14
	mov QWORD PTR [r9+64], r15
	movq xmm15, rsi
	test rcx, rcx
	je 20f
	mov rax, QWORD PTR [rdx]
	xor rax, QWORD PTR [rsi]
	mov QWORD PTR [rdx], rax
	jmp 21f
20:
21:
	mov r12, rdx
	mov r13, rcx
	test r13, r13
	je 22f
24:
	mov rax, QWORD PTR [r12]
	mov QWORD PTR [r9], rax
	movq r14, xmm15
	mov rdx, r9
	mov rsi, r9
	mov rcx, r9
	add rcx, 8
	movabs r11, 281479271743489
	movq xmm13, r11
	movabs r11, 281479271743489
	movq xmm12, r11
	punpcklqdq xmm13, xmm12
	movabs r11, 4503668347895824
	movq xmm14, r11
	movabs r11, 4503668347895824
	movq xmm12, r11
	punpcklqdq xmm14, xmm12
	movabs r11, 71777214294589695
	movq xmm15, r11
	movabs r11, 71777214294589695
	movq xmm12, r11
	punpcklqdq xmm15, xmm12
	mov r11d, DWORD PTR [rsi]
	bswap r11d
	movq xmm0, r11
	mov r11d, DWORD PTR [rsi+4]
	bswap r11d
	movq xmm1, r11
	mov eax, 0
	mov r10d, 16
25:
	mov r11d, DWORD PTR [rdi+rax*1+4096]
	movq xmm12, r11
	pxor xmm0, xmm12
	movdqa xmm3, xmm0
	pslld xmm3, 0
	psrld xmm3, 24
	punpcklwd xmm3, xmm3
	pshufd xmm3, xmm3, 0
	movabs r11, 1688867040264192
	movq xmm4, r11
	movabs r11, 3940701214212104
	movq xmm12, r11
	punpcklqdq xmm4, xmm12
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	mov r8d, 0
	mov r9d, 16
26:
	movdqa xmm6, xmm4
	pxor xmm6, xmm3
	psubw xmm6, xmm13
	psraw xmm6, 15
	movdqa xmm7, xmm4
	paddw xmm7, xmm13
	pxor xmm7, xmm3
	psubw xmm7, xmm13
	psraw xmm7, 15
	pand xmm6, xmm15
	psllw xmm7, 8
	por xmm6, xmm7
	movdqu xmm12, XMMWORD PTR [rdi+r8*1]
	pand xmm12, xmm6
	por xmm8, xmm12
	movdqu xmm12, XMMWORD PTR [rdi+r8*1+256]
	pand xmm12, xmm6
	por xmm9, xmm12
	movdqu xmm12, XMMWORD PTR [rdi+r8*1+512]
	pand xmm12, xmm6
	por xmm10, xmm12
	movdqu xmm12, XMMWORD PTR [rdi+r8*1+768]
	pand xmm12, xmm6
	por xmm11, xmm12
	paddw xmm4, xmm14
	add r8, 16
	sub r9, 1
	jne 26b
	pshufd xmm12, xmm8, 78
	por xmm8, xmm12
	pshufd xmm12, xmm8, 177
	por xmm8, xmm12
	movdqa xmm12, xmm8
	psrld xmm12, 16
	por xmm8, xmm12
	movdqa xmm12, xmm8
	psrld xmm12, 8
	por xmm8, xmm12
	pslld xmm8, 24
	psrld xmm8, 24
	pshufd xmm12, xmm9, 78
	por xmm9, xmm12
	pshufd xmm12, xmm9, 177
	por xmm9, xmm12
	movdqa xmm12, xmm9
	psrld xmm12, 16
	por xmm9, xmm12
	movdqa xmm12, xmm9
	psrld xmm12, 8
	por xmm9, xmm12
	pslld xmm9, 24
	psrld xmm9, 24
	pshufd xmm12, xmm10, 78
	por xmm10, xmm12
	pshufd xmm12, xmm10, 177
	por xmm10, xmm12
	movdqa xmm12, xmm10
	psrld xmm12, 16
	por xmm10, xmm12
	movdqa xmm12, xmm10
	psrld xmm12, 8
	por xmm10, xmm12
	pslld xmm10, 24
	psrld xmm10, 24
	pshufd xmm12, xmm11, 78
	por xmm11, xmm12
	pshufd xmm12, xmm11, 177
	por xmm11, xmm12
	movdqa xmm12, xmm11
	psrld xmm12, 16
	por xmm11, xmm12
	movdqa xmm12, xmm11
	psrld xmm12, 8
	por xmm11, xmm12
	pslld xmm11, 24
	psrld xmm11, 24
	pslld xmm9, 8
	pslld xmm10, 16
	pslld xmm11, 24
	por xmm8, xmm9
	por xmm8, xmm10
	por xmm8, xmm11
	movdqa xmm2, xmm8
	movdqa xmm3, xmm0
	pslld xmm3, 8
	psrld xmm3, 24
	punpcklwd xmm3, xmm3
	pshufd xmm3, xmm3, 0
	movabs r11, 1688867040264192
	movq xmm4, r11
	movabs r11, 3940701214212104
	movq xmm12, r11
	punpcklqdq xmm4, xmm12
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	mov r8d, 0
	mov r9d, 16
27:
	movdqa xmm6, xmm4
	pxor xmm6, xmm3
	psubw xmm6, xmm13
	psraw xmm6, 15
	movdqa xmm7, xmm4
	paddw xmm7, xmm13
	pxor xmm7, xmm3
	psubw xmm7, xmm13
	psraw xmm7, 15
	pand xmm6, xmm15
	psllw xmm7, 8
	por xmm6, xmm7
	movdqu xmm12, XMMWORD PTR [rdi+r8*1+1024]
	pand xmm12, xmm6
	por xmm8, xmm12
	movdqu xmm12, XMMWORD PTR [rdi+r8*1+1280]
	pand xmm12, xmm6
	por xmm9, xmm12
	movdqu xmm12, XMMWORD PTR [rdi+r8*1+1536]
	pand xmm12, xmm6
	por xmm10, xmm12
	movdqu xmm12, XMMWORD PTR [rdi+r8*1+1792]
	pand xmm12, xmm6
	por xmm11, xmm12
	paddw xmm4, xmm14
	add r8, 16
	sub r9, 1
	jne 27b
	pshufd xmm12, xmm8, 78
	por xmm8, xmm12
	pshufd xmm12, xmm8, 177
	por xmm8, xmm12
	movdqa xmm12, xmm8
	psrld xmm12, 16
	por xmm8, xmm12
	movdqa xmm12, xmm8
	psrld xmm12, 8
	por xmm8, xmm12
	pslld xmm8, 24
	psrld xmm8, 24
	pshufd xmm12, xmm9, 78
	por xmm9, xmm12
	pshufd xmm12, xmm9, 177
	por xmm9, xmm12
	movdqa xmm12, xmm9
	psrld xmm12, 16
	por xmm9, xmm12
	movdqa xmm12, xmm9
	psrld xmm12, 8
	por xmm9, xmm12
	pslld xmm9, 24
	psrld xmm9, 24
	pshufd xmm12, xmm10, 78
	por xmm10, xmm12
	pshufd xmm12, xmm10, 177
	por xmm10, xmm12
	movdqa xmm12, xmm10
	psrld xmm12, 16
	por xmm10, xmm12
	movdqa xmm12, xmm10
	psrld xmm12, 8
	por xmm10, xmm12
	pslld xmm10, 24
	psrld xmm10, 24
	pshufd xmm12, xmm11, 78
	por xmm11, xmm12
	pshufd xmm12, xmm11, 177
	por xmm11, xmm12
	movdqa xmm12, xmm11
	psrld xmm12, 16
	por xmm11, xmm12
	movdqa xmm12, xmm11
	psrld xmm12, 8
	por xmm11, xmm12
	pslld xmm11, 24
	psrld xmm11, 24
	pslld xmm9, 8
	pslld xmm10, 16
	pslld xmm11, 24
	por xmm8, xmm9
	por xmm8, xmm10
	por xmm8, xmm11
	paddd xmm2, xmm8
	movdqa xmm3, xmm0
	pslld xmm3, 16
	psrld xmm3, 24
	punpcklwd xmm3, xmm3
	pshufd xmm3, xmm3, 0
	movabs r11, 1688867040264192
	movq xmm4, r11
	movabs r11, 3940701214212104
	movq xmm12, r11
	punpcklqdq xmm4, xmm12
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	mov r8d, 0
	mov r9d, 16
28:
	movdqa xmm6, xmm4
	pxor xmm6, xmm3
	psubw xmm6, xmm13
	psraw xmm6, 15
	movdqa xmm7, xmm4
	paddw xmm7, xmm13
	pxor xmm7, xmm3
	psubw xmm7, xmm13
	psraw xmm7, 15
	pand xmm6, xmm15
	psllw xmm7, 8
	por xmm6, xmm7
	movdqu xmm12, XMMWORD PTR [rdi+r8*1+2048]
	pand xmm12, xmm6
	por xmm8, xmm12
	movdqu xmm12, XMMWORD PTR [rdi+r8*1+2304]
	pand xmm12, xmm6
	por xmm9, xmm12
	movdqu xmm12, XMMWORD PTR [rdi+r8*1+2560]
	pand xmm12, xmm6
	por xmm10, xmm12
	movdqu xmm12, XMMWORD PTR [rdi+r8*1+2816]
	pand xmm12, xmm6
	por xmm11, xmm12
	paddw xmm4, xmm14
	add r8, 16
	sub r9, 1
	jne 28b
	pshufd xmm12, xmm8, 78
	por xmm8, xmm12
	pshufd xmm12, xmm8, 177
	por xmm8, xmm12
	movdqa xmm12, xmm8
	psrld xmm12, 16
	por xmm8, xmm12
	movdqa xmm12, xmm8
	psrld xmm12, 8
	por xmm8, xmm12
	pslld xmm8, 24
	psrld xmm8, 24
	pshufd xmm12, xmm9, 78
	por xmm9, xmm12
	pshufd xmm12, xmm9, 177
	por xmm9, xmm12
	movdqa xmm12, xmm9
	psrld xmm12, 16
	por xmm9, xmm12
	movdqa xmm12, xmm9
	psrld xmm12, 8
	por xmm9, xmm12
	pslld xmm9, 24
	psrld xmm9, 24
	pshufd xmm12, xmm10, 78
	por xmm10, xmm12
	pshufd xmm12, xmm10, 177
	por xmm10, xmm12
	movdqa xmm12, xmm10
	psrld xmm12, 16
	por xmm10, xmm12
	movdqa xmm12, xmm10
	psrld xmm12, 8
	por xmm10, xmm12
	pslld xmm10, 24
	psrld xmm10, 24
	pshufd xmm12, xmm11, 78
	por xmm11, xmm12
	pshufd xmm12, xmm11, 177
	por xmm11, xmm12
	movdqa xmm12, xmm11
	psrld xmm12, 16
	por xmm11, xmm12
	movdqa xmm12, xmm11
	psrld xmm12, 8
	por xmm11, xmm12
	pslld xmm11, 24
	psrld xmm11, 24
	pslld xmm9, 8
	pslld xmm10, 16
	pslld xmm11, 24
	por xmm8, xmm9
	por xmm8, xmm10
	por xmm8, xmm11
	pxor xmm2, xmm8
	movdqa xmm3, xmm0
	pslld xmm3, 24
	psrld xmm3, 24
	punpcklwd xmm3, xmm3
	pshufd xmm3, xmm3, 0
	movabs r11, 1688867040264192
	movq xmm4, r11
	movabs r11, 3940701214212104
	movq xmm12, r11
	punpcklqdq xmm4, xmm12
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	mov r8d, 0
	mov r9d, 16
29:
	movdqa xmm6, xmm4
	pxor xmm6, xmm3
	psubw xmm6, xmm13
	psraw xmm6, 15
	movdqa xmm7, xmm4
	paddw xmm7, xmm13
	pxor xmm7, xmm3
	psubw xmm7, xmm13
	psraw xmm7, 15
	pand xmm6, xmm15
	psllw xmm7, 8
	por xmm6, xmm7
	movdqu xmm12, XMMWORD PTR [rdi+r8*1+3072]
	pand xmm12, xmm6
	por xmm8, xmm12
	movdqu xmm12, XMMWORD PTR [rdi+r8*1+3328]
	pand xmm12, xmm6
	por xmm9, xmm12
	movdqu xmm12, XMMWORD PTR [rdi+r8*1+3584]
	pand xmm12, xmm6
	por xmm10, xmm12
	movdqu xmm12, XMMWORD PTR [rdi+r8*1+3840]
	pand xmm12, xmm6
	por xmm11, xmm12
	paddw xmm4, xmm14
	add r8, 16
	sub r9, 1
	jne 29b
	pshufd xmm12, xmm8, 78
	por xmm8, xmm12
	pshufd xmm12, xmm8, 177
	por xmm8, xmm12
	movdqa xmm12, xmm8
	psrld xmm12, 16
	por xmm8, xmm12
	movdqa xmm12, xmm8
	psrld xmm12, 8
	por xmm8, xmm12
	pslld xmm8, 24
	psrld xmm8, 24
	pshufd xmm12, xmm9, 78
	por xmm9, xmm12
	pshufd xmm12, xmm9, 177
	por xmm9, xmm12
	movdqa xmm12, xmm9
	psrld xmm12, 16
	por xmm9, xmm12
	movdqa xmm12, xmm9
	psrld xmm12, 8
	por xmm9, xmm12
	pslld xmm9, 24
	psrld xmm9, 24
	pshufd xmm12, xmm10, 78
	por xmm10, xmm12
	pshufd xmm12, xmm10, 177
	por xmm10, xmm12
	movdqa xmm12, xmm10
	psrld xmm12, 16
	por xmm10, xmm12
	movdqa xmm12, xmm10
	psrld xmm12, 8
	por xmm10, xmm12
	pslld xmm10, 24
	psrld xmm10, 24
	pshufd xmm12, xmm11, 78
	por xmm11, xmm12
	pshufd xmm12, xmm11, 177
	por xmm11, xmm12
	movdqa xmm12, xmm11
	psrld xmm12, 16
	por xmm11, xmm12
	movdqa xmm12, xmm11
	psrld xmm12, 8
	por xmm11, xmm12
	pslld xmm11, 24
	psrld xmm11, 24
	pslld xmm9, 8
	pslld xmm10, 16
	pslld xmm11, 24
	por xmm8, xmm9
	por xmm8, xmm10
	por xmm8, xmm11
	paddd xmm2, xmm8
	pxor xmm1, xmm2
	movdqa xmm12, xmm0
	movdqa xmm0, xmm1
	movdqa xmm1, xmm12
	add rax, 4
	sub r10, 1
	jne 25b
	mov r11d, DWORD PTR [rdi+4160]
	movq xmm12, r11
	pxor xmm0, xmm12
	mov r11d, DWORD PTR [rdi+4164]
	movq xmm12, r11
	pxor xmm1, xmm12
	movdqu XMMWORD PTR [rcx], xmm1
	mov r11d, DWORD PTR [rcx]
	bswap r11d
	mov DWORD PTR [rsi], r11d
	movdqu XMMWORD PTR [rcx], xmm0
	mov r11d, DWORD PTR [rcx]
	bswap r11d
	mov DWORD PTR [rsi+4], r11d
	mov r9, rdx
	movq xmm15, r14
	mov rax, QWORD PTR [r9]
	mov QWORD PTR [r12], rax
	sub r13, 1
	je 210f
	mov rax, QWORD PTR [r12+8]
	xor rax, QWORD PTR [r9]
	mov QWORD PTR [r12+8], rax
	jmp 211f
210:
211:
	add r12, 8
	test r13, r13
	jne 24b
	movq rax, xmm15
	mov rbp, QWORD PTR [r9]
	mov QWORD PTR [rax], rbp
	jmp 23f
22:
23:
	mov rbx, QWORD PTR [r9+24]
	mov rbp, QWORD PTR [r9+32]
	mov r12, QWORD PTR [r9+40]
	mov r13, QWORD PTR [r9+48]
	mov r14, QWORD PTR [r9+56]
	mov r15, QWORD PTR [r9+64]
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
	lea rsp, [rsp+96]
	ret
	.p2align 6

vg_blowfish_cbc_decrypt_chained:
	lea rsp, [rsp-96]
	mov r8, rsp
	add r8, 8
	mov r9, r8
	mov QWORD PTR [r9+24], rbx
	mov QWORD PTR [r9+32], rbp
	mov QWORD PTR [r9+40], r12
	mov QWORD PTR [r9+48], r13
	mov QWORD PTR [r9+56], r14
	mov QWORD PTR [r9+64], r15
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [r9+72], rax
	test rcx, rcx
	je 20f
	mov rax, rcx
	sub rax, 1
	shl rax, 3
	add rax, rdx
	mov rbx, QWORD PTR [rax]
	mov QWORD PTR [rsi], rbx
	jmp 21f
20:
21:
	mov r12, rdx
	mov r13, rcx
	test r13, r13
	je 22f
24:
	movabs rcx, 1
	cmp r13, 1
	jb 25f
	jmp 26f
25:
	mov rcx, r13
26:
	mov rax, r9
	add rax, 0
	mov rbx, r12
	mov r10, rcx
27:
	mov rbp, QWORD PTR [rbx]
	mov QWORD PTR [rax], rbp
	add rax, 8
	add rbx, 8
	sub rcx, 1
	jne 27b
	movq r14, xmm15
	mov rdx, r9
	mov rsi, r9
	mov rcx, r9
	add rcx, 8
	movabs r11, 281479271743489
	movq xmm13, r11
	movabs r11, 281479271743489
	movq xmm12, r11
	punpcklqdq xmm13, xmm12
	movabs r11, 4503668347895824
	movq xmm14, r11
	movabs r11, 4503668347895824
	movq xmm12, r11
	punpcklqdq xmm14, xmm12
	movabs r11, 71777214294589695
	movq xmm15, r11
	movabs r11, 71777214294589695
	movq xmm12, r11
	punpcklqdq xmm15, xmm12
	mov r11d, DWORD PTR [rsi]
	bswap r11d
	movq xmm0, r11
	mov r11d, DWORD PTR [rsi+4]
	bswap r11d
	movq xmm1, r11
	mov eax, 68
	mov r10d, 16
28:
	mov r11d, DWORD PTR [rdi+rax*1+4096]
	movq xmm12, r11
	pxor xmm0, xmm12
	movdqa xmm3, xmm0
	pslld xmm3, 0
	psrld xmm3, 24
	punpcklwd xmm3, xmm3
	pshufd xmm3, xmm3, 0
	movabs r11, 1688867040264192
	movq xmm4, r11
	movabs r11, 3940701214212104
	movq xmm12, r11
	punpcklqdq xmm4, xmm12
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	mov r8d, 0
	mov r9d, 16
29:
	movdqa xmm6, xmm4
	pxor xmm6, xmm3
	psubw xmm6, xmm13
	psraw xmm6, 15
	movdqa xmm7, xmm4
	paddw xmm7, xmm13
	pxor xmm7, xmm3
	psubw xmm7, xmm13
	psraw xmm7, 15
	pand xmm6, xmm15
	psllw xmm7, 8
	por xmm6, xmm7
	movdqu xmm12, XMMWORD PTR [rdi+r8*1]
	pand xmm12, xmm6
	por xmm8, xmm12
	movdqu xmm12, XMMWORD PTR [rdi+r8*1+256]
	pand xmm12, xmm6
	por xmm9, xmm12
	movdqu xmm12, XMMWORD PTR [rdi+r8*1+512]
	pand xmm12, xmm6
	por xmm10, xmm12
	movdqu xmm12, XMMWORD PTR [rdi+r8*1+768]
	pand xmm12, xmm6
	por xmm11, xmm12
	paddw xmm4, xmm14
	add r8, 16
	sub r9, 1
	jne 29b
	pshufd xmm12, xmm8, 78
	por xmm8, xmm12
	pshufd xmm12, xmm8, 177
	por xmm8, xmm12
	movdqa xmm12, xmm8
	psrld xmm12, 16
	por xmm8, xmm12
	movdqa xmm12, xmm8
	psrld xmm12, 8
	por xmm8, xmm12
	pslld xmm8, 24
	psrld xmm8, 24
	pshufd xmm12, xmm9, 78
	por xmm9, xmm12
	pshufd xmm12, xmm9, 177
	por xmm9, xmm12
	movdqa xmm12, xmm9
	psrld xmm12, 16
	por xmm9, xmm12
	movdqa xmm12, xmm9
	psrld xmm12, 8
	por xmm9, xmm12
	pslld xmm9, 24
	psrld xmm9, 24
	pshufd xmm12, xmm10, 78
	por xmm10, xmm12
	pshufd xmm12, xmm10, 177
	por xmm10, xmm12
	movdqa xmm12, xmm10
	psrld xmm12, 16
	por xmm10, xmm12
	movdqa xmm12, xmm10
	psrld xmm12, 8
	por xmm10, xmm12
	pslld xmm10, 24
	psrld xmm10, 24
	pshufd xmm12, xmm11, 78
	por xmm11, xmm12
	pshufd xmm12, xmm11, 177
	por xmm11, xmm12
	movdqa xmm12, xmm11
	psrld xmm12, 16
	por xmm11, xmm12
	movdqa xmm12, xmm11
	psrld xmm12, 8
	por xmm11, xmm12
	pslld xmm11, 24
	psrld xmm11, 24
	pslld xmm9, 8
	pslld xmm10, 16
	pslld xmm11, 24
	por xmm8, xmm9
	por xmm8, xmm10
	por xmm8, xmm11
	movdqa xmm2, xmm8
	movdqa xmm3, xmm0
	pslld xmm3, 8
	psrld xmm3, 24
	punpcklwd xmm3, xmm3
	pshufd xmm3, xmm3, 0
	movabs r11, 1688867040264192
	movq xmm4, r11
	movabs r11, 3940701214212104
	movq xmm12, r11
	punpcklqdq xmm4, xmm12
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	mov r8d, 0
	mov r9d, 16
210:
	movdqa xmm6, xmm4
	pxor xmm6, xmm3
	psubw xmm6, xmm13
	psraw xmm6, 15
	movdqa xmm7, xmm4
	paddw xmm7, xmm13
	pxor xmm7, xmm3
	psubw xmm7, xmm13
	psraw xmm7, 15
	pand xmm6, xmm15
	psllw xmm7, 8
	por xmm6, xmm7
	movdqu xmm12, XMMWORD PTR [rdi+r8*1+1024]
	pand xmm12, xmm6
	por xmm8, xmm12
	movdqu xmm12, XMMWORD PTR [rdi+r8*1+1280]
	pand xmm12, xmm6
	por xmm9, xmm12
	movdqu xmm12, XMMWORD PTR [rdi+r8*1+1536]
	pand xmm12, xmm6
	por xmm10, xmm12
	movdqu xmm12, XMMWORD PTR [rdi+r8*1+1792]
	pand xmm12, xmm6
	por xmm11, xmm12
	paddw xmm4, xmm14
	add r8, 16
	sub r9, 1
	jne 210b
	pshufd xmm12, xmm8, 78
	por xmm8, xmm12
	pshufd xmm12, xmm8, 177
	por xmm8, xmm12
	movdqa xmm12, xmm8
	psrld xmm12, 16
	por xmm8, xmm12
	movdqa xmm12, xmm8
	psrld xmm12, 8
	por xmm8, xmm12
	pslld xmm8, 24
	psrld xmm8, 24
	pshufd xmm12, xmm9, 78
	por xmm9, xmm12
	pshufd xmm12, xmm9, 177
	por xmm9, xmm12
	movdqa xmm12, xmm9
	psrld xmm12, 16
	por xmm9, xmm12
	movdqa xmm12, xmm9
	psrld xmm12, 8
	por xmm9, xmm12
	pslld xmm9, 24
	psrld xmm9, 24
	pshufd xmm12, xmm10, 78
	por xmm10, xmm12
	pshufd xmm12, xmm10, 177
	por xmm10, xmm12
	movdqa xmm12, xmm10
	psrld xmm12, 16
	por xmm10, xmm12
	movdqa xmm12, xmm10
	psrld xmm12, 8
	por xmm10, xmm12
	pslld xmm10, 24
	psrld xmm10, 24
	pshufd xmm12, xmm11, 78
	por xmm11, xmm12
	pshufd xmm12, xmm11, 177
	por xmm11, xmm12
	movdqa xmm12, xmm11
	psrld xmm12, 16
	por xmm11, xmm12
	movdqa xmm12, xmm11
	psrld xmm12, 8
	por xmm11, xmm12
	pslld xmm11, 24
	psrld xmm11, 24
	pslld xmm9, 8
	pslld xmm10, 16
	pslld xmm11, 24
	por xmm8, xmm9
	por xmm8, xmm10
	por xmm8, xmm11
	paddd xmm2, xmm8
	movdqa xmm3, xmm0
	pslld xmm3, 16
	psrld xmm3, 24
	punpcklwd xmm3, xmm3
	pshufd xmm3, xmm3, 0
	movabs r11, 1688867040264192
	movq xmm4, r11
	movabs r11, 3940701214212104
	movq xmm12, r11
	punpcklqdq xmm4, xmm12
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	mov r8d, 0
	mov r9d, 16
211:
	movdqa xmm6, xmm4
	pxor xmm6, xmm3
	psubw xmm6, xmm13
	psraw xmm6, 15
	movdqa xmm7, xmm4
	paddw xmm7, xmm13
	pxor xmm7, xmm3
	psubw xmm7, xmm13
	psraw xmm7, 15
	pand xmm6, xmm15
	psllw xmm7, 8
	por xmm6, xmm7
	movdqu xmm12, XMMWORD PTR [rdi+r8*1+2048]
	pand xmm12, xmm6
	por xmm8, xmm12
	movdqu xmm12, XMMWORD PTR [rdi+r8*1+2304]
	pand xmm12, xmm6
	por xmm9, xmm12
	movdqu xmm12, XMMWORD PTR [rdi+r8*1+2560]
	pand xmm12, xmm6
	por xmm10, xmm12
	movdqu xmm12, XMMWORD PTR [rdi+r8*1+2816]
	pand xmm12, xmm6
	por xmm11, xmm12
	paddw xmm4, xmm14
	add r8, 16
	sub r9, 1
	jne 211b
	pshufd xmm12, xmm8, 78
	por xmm8, xmm12
	pshufd xmm12, xmm8, 177
	por xmm8, xmm12
	movdqa xmm12, xmm8
	psrld xmm12, 16
	por xmm8, xmm12
	movdqa xmm12, xmm8
	psrld xmm12, 8
	por xmm8, xmm12
	pslld xmm8, 24
	psrld xmm8, 24
	pshufd xmm12, xmm9, 78
	por xmm9, xmm12
	pshufd xmm12, xmm9, 177
	por xmm9, xmm12
	movdqa xmm12, xmm9
	psrld xmm12, 16
	por xmm9, xmm12
	movdqa xmm12, xmm9
	psrld xmm12, 8
	por xmm9, xmm12
	pslld xmm9, 24
	psrld xmm9, 24
	pshufd xmm12, xmm10, 78
	por xmm10, xmm12
	pshufd xmm12, xmm10, 177
	por xmm10, xmm12
	movdqa xmm12, xmm10
	psrld xmm12, 16
	por xmm10, xmm12
	movdqa xmm12, xmm10
	psrld xmm12, 8
	por xmm10, xmm12
	pslld xmm10, 24
	psrld xmm10, 24
	pshufd xmm12, xmm11, 78
	por xmm11, xmm12
	pshufd xmm12, xmm11, 177
	por xmm11, xmm12
	movdqa xmm12, xmm11
	psrld xmm12, 16
	por xmm11, xmm12
	movdqa xmm12, xmm11
	psrld xmm12, 8
	por xmm11, xmm12
	pslld xmm11, 24
	psrld xmm11, 24
	pslld xmm9, 8
	pslld xmm10, 16
	pslld xmm11, 24
	por xmm8, xmm9
	por xmm8, xmm10
	por xmm8, xmm11
	pxor xmm2, xmm8
	movdqa xmm3, xmm0
	pslld xmm3, 24
	psrld xmm3, 24
	punpcklwd xmm3, xmm3
	pshufd xmm3, xmm3, 0
	movabs r11, 1688867040264192
	movq xmm4, r11
	movabs r11, 3940701214212104
	movq xmm12, r11
	punpcklqdq xmm4, xmm12
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	mov r8d, 0
	mov r9d, 16
212:
	movdqa xmm6, xmm4
	pxor xmm6, xmm3
	psubw xmm6, xmm13
	psraw xmm6, 15
	movdqa xmm7, xmm4
	paddw xmm7, xmm13
	pxor xmm7, xmm3
	psubw xmm7, xmm13
	psraw xmm7, 15
	pand xmm6, xmm15
	psllw xmm7, 8
	por xmm6, xmm7
	movdqu xmm12, XMMWORD PTR [rdi+r8*1+3072]
	pand xmm12, xmm6
	por xmm8, xmm12
	movdqu xmm12, XMMWORD PTR [rdi+r8*1+3328]
	pand xmm12, xmm6
	por xmm9, xmm12
	movdqu xmm12, XMMWORD PTR [rdi+r8*1+3584]
	pand xmm12, xmm6
	por xmm10, xmm12
	movdqu xmm12, XMMWORD PTR [rdi+r8*1+3840]
	pand xmm12, xmm6
	por xmm11, xmm12
	paddw xmm4, xmm14
	add r8, 16
	sub r9, 1
	jne 212b
	pshufd xmm12, xmm8, 78
	por xmm8, xmm12
	pshufd xmm12, xmm8, 177
	por xmm8, xmm12
	movdqa xmm12, xmm8
	psrld xmm12, 16
	por xmm8, xmm12
	movdqa xmm12, xmm8
	psrld xmm12, 8
	por xmm8, xmm12
	pslld xmm8, 24
	psrld xmm8, 24
	pshufd xmm12, xmm9, 78
	por xmm9, xmm12
	pshufd xmm12, xmm9, 177
	por xmm9, xmm12
	movdqa xmm12, xmm9
	psrld xmm12, 16
	por xmm9, xmm12
	movdqa xmm12, xmm9
	psrld xmm12, 8
	por xmm9, xmm12
	pslld xmm9, 24
	psrld xmm9, 24
	pshufd xmm12, xmm10, 78
	por xmm10, xmm12
	pshufd xmm12, xmm10, 177
	por xmm10, xmm12
	movdqa xmm12, xmm10
	psrld xmm12, 16
	por xmm10, xmm12
	movdqa xmm12, xmm10
	psrld xmm12, 8
	por xmm10, xmm12
	pslld xmm10, 24
	psrld xmm10, 24
	pshufd xmm12, xmm11, 78
	por xmm11, xmm12
	pshufd xmm12, xmm11, 177
	por xmm11, xmm12
	movdqa xmm12, xmm11
	psrld xmm12, 16
	por xmm11, xmm12
	movdqa xmm12, xmm11
	psrld xmm12, 8
	por xmm11, xmm12
	pslld xmm11, 24
	psrld xmm11, 24
	pslld xmm9, 8
	pslld xmm10, 16
	pslld xmm11, 24
	por xmm8, xmm9
	por xmm8, xmm10
	por xmm8, xmm11
	paddd xmm2, xmm8
	pxor xmm1, xmm2
	movdqa xmm12, xmm0
	movdqa xmm0, xmm1
	movdqa xmm1, xmm12
	sub rax, 4
	sub r10, 1
	jne 28b
	mov r11d, DWORD PTR [rdi+4100]
	movq xmm12, r11
	pxor xmm0, xmm12
	mov r11d, DWORD PTR [rdi+4096]
	movq xmm12, r11
	pxor xmm1, xmm12
	movdqu XMMWORD PTR [rcx], xmm1
	mov r11d, DWORD PTR [rcx]
	bswap r11d
	mov DWORD PTR [rsi], r11d
	movdqu XMMWORD PTR [rcx], xmm0
	mov r11d, DWORD PTR [rcx]
	bswap r11d
	mov DWORD PTR [rsi+4], r11d
	mov r9, rdx
	movq xmm15, r14
	movabs rcx, 1
	cmp r13, 1
	jb 213f
	jmp 214f
213:
	mov rcx, r13
214:
	mov rax, r9
	add rax, 0
	mov rbx, r12
	mov r10, rcx
215:
	mov rbp, QWORD PTR [rax]
	xor rbp, QWORD PTR [r9+72]
	mov QWORD PTR [rax], rbp
	mov rbp, QWORD PTR [rbx]
	mov QWORD PTR [r9+72], rbp
	mov rbp, QWORD PTR [rax]
	mov QWORD PTR [rbx], rbp
	add rax, 8
	add rbx, 8
	sub rcx, 1
	jne 215b
	mov r12, rbx
	sub r13, r10
	jne 24b
	jmp 23f
22:
23:
	mov rbx, QWORD PTR [r9+24]
	mov rbp, QWORD PTR [r9+32]
	mov r12, QWORD PTR [r9+40]
	mov r13, QWORD PTR [r9+48]
	mov r14, QWORD PTR [r9+56]
	mov r15, QWORD PTR [r9+64]
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
	lea rsp, [rsp+96]
	ret
	.p2align 6
