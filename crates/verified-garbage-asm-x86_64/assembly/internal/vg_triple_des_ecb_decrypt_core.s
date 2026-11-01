// The functions of `src/internal/vg_triple_des_ecb_decrypt_core.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_triple_des_ecb_decrypt_core:
	cmp rdx, 128
	jb 20f
	mov QWORD PTR [rcx+1016], rbx
	mov QWORD PTR [rcx+1008], r12
	mov QWORD PTR [rcx+1000], r13
22:
	mov r11, 8
23:
	movabs rbx, 4294967295
	movq xmm13, rbx
	punpcklqdq xmm13, xmm13
	movabs rbx, 281470681808895
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movabs rbx, 71777214294589695
	movq xmm15, rbx
	punpcklqdq xmm15, xmm15
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+128]
	movdqu xmm2, XMMWORD PTR [rsi+256]
	movdqu xmm3, XMMWORD PTR [rsi+384]
	movdqu xmm4, XMMWORD PTR [rsi+512]
	movdqu xmm5, XMMWORD PTR [rsi+640]
	movdqu xmm6, XMMWORD PTR [rsi+768]
	movdqu xmm7, XMMWORD PTR [rsi+896]
	movdqa xmm8, xmm0
	psrlq xmm8, 32
	pxor xmm8, xmm4
	pand xmm8, xmm13
	pxor xmm4, xmm8
	psllq xmm8, 32
	pxor xmm0, xmm8
	movdqa xmm8, xmm1
	psrlq xmm8, 32
	pxor xmm8, xmm5
	pand xmm8, xmm13
	pxor xmm5, xmm8
	psllq xmm8, 32
	pxor xmm1, xmm8
	movdqa xmm8, xmm2
	psrlq xmm8, 32
	pxor xmm8, xmm6
	pand xmm8, xmm13
	pxor xmm6, xmm8
	psllq xmm8, 32
	pxor xmm2, xmm8
	movdqa xmm8, xmm3
	psrlq xmm8, 32
	pxor xmm8, xmm7
	pand xmm8, xmm13
	pxor xmm7, xmm8
	psllq xmm8, 32
	pxor xmm3, xmm8
	movdqa xmm8, xmm0
	psrlq xmm8, 16
	pxor xmm8, xmm2
	pand xmm8, xmm14
	pxor xmm2, xmm8
	psllq xmm8, 16
	pxor xmm0, xmm8
	movdqa xmm8, xmm1
	psrlq xmm8, 16
	pxor xmm8, xmm3
	pand xmm8, xmm14
	pxor xmm3, xmm8
	psllq xmm8, 16
	pxor xmm1, xmm8
	movdqa xmm8, xmm4
	psrlq xmm8, 16
	pxor xmm8, xmm6
	pand xmm8, xmm14
	pxor xmm6, xmm8
	psllq xmm8, 16
	pxor xmm4, xmm8
	movdqa xmm8, xmm5
	psrlq xmm8, 16
	pxor xmm8, xmm7
	pand xmm8, xmm14
	pxor xmm7, xmm8
	psllq xmm8, 16
	pxor xmm5, xmm8
	movdqa xmm8, xmm0
	psrlq xmm8, 8
	pxor xmm8, xmm1
	pand xmm8, xmm15
	pxor xmm1, xmm8
	psllq xmm8, 8
	pxor xmm0, xmm8
	movdqa xmm8, xmm2
	psrlq xmm8, 8
	pxor xmm8, xmm3
	pand xmm8, xmm15
	pxor xmm3, xmm8
	psllq xmm8, 8
	pxor xmm2, xmm8
	movdqa xmm8, xmm4
	psrlq xmm8, 8
	pxor xmm8, xmm5
	pand xmm8, xmm15
	pxor xmm5, xmm8
	psllq xmm8, 8
	pxor xmm4, xmm8
	movdqa xmm8, xmm6
	psrlq xmm8, 8
	pxor xmm8, xmm7
	pand xmm8, xmm15
	pxor xmm7, xmm8
	psllq xmm8, 8
	pxor xmm6, xmm8
	movdqu XMMWORD PTR [rsi], xmm0
	movdqu XMMWORD PTR [rsi+128], xmm1
	movdqu XMMWORD PTR [rsi+256], xmm2
	movdqu XMMWORD PTR [rsi+384], xmm3
	movdqu XMMWORD PTR [rsi+512], xmm4
	movdqu XMMWORD PTR [rsi+640], xmm5
	movdqu XMMWORD PTR [rsi+768], xmm6
	movdqu XMMWORD PTR [rsi+896], xmm7
	add rsi, 16
	sub r11, 1
	jne 23b
	sub rsi, 128
	mov r11, 8
24:
	movabs rbx, 1085102592571150095
	movq xmm13, rbx
	punpcklqdq xmm13, xmm13
	movabs rbx, 3689348814741910323
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movabs rbx, 6148914691236517205
	movq xmm15, rbx
	punpcklqdq xmm15, xmm15
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+16]
	movdqu xmm2, XMMWORD PTR [rsi+32]
	movdqu xmm3, XMMWORD PTR [rsi+48]
	movdqu xmm4, XMMWORD PTR [rsi+64]
	movdqu xmm5, XMMWORD PTR [rsi+80]
	movdqu xmm6, XMMWORD PTR [rsi+96]
	movdqu xmm7, XMMWORD PTR [rsi+112]
	movdqa xmm8, xmm0
	psrlq xmm8, 4
	pxor xmm8, xmm4
	pand xmm8, xmm13
	pxor xmm4, xmm8
	psllq xmm8, 4
	pxor xmm0, xmm8
	movdqa xmm8, xmm1
	psrlq xmm8, 4
	pxor xmm8, xmm5
	pand xmm8, xmm13
	pxor xmm5, xmm8
	psllq xmm8, 4
	pxor xmm1, xmm8
	movdqa xmm8, xmm2
	psrlq xmm8, 4
	pxor xmm8, xmm6
	pand xmm8, xmm13
	pxor xmm6, xmm8
	psllq xmm8, 4
	pxor xmm2, xmm8
	movdqa xmm8, xmm3
	psrlq xmm8, 4
	pxor xmm8, xmm7
	pand xmm8, xmm13
	pxor xmm7, xmm8
	psllq xmm8, 4
	pxor xmm3, xmm8
	movdqa xmm8, xmm0
	psrlq xmm8, 2
	pxor xmm8, xmm2
	pand xmm8, xmm14
	pxor xmm2, xmm8
	psllq xmm8, 2
	pxor xmm0, xmm8
	movdqa xmm8, xmm1
	psrlq xmm8, 2
	pxor xmm8, xmm3
	pand xmm8, xmm14
	pxor xmm3, xmm8
	psllq xmm8, 2
	pxor xmm1, xmm8
	movdqa xmm8, xmm4
	psrlq xmm8, 2
	pxor xmm8, xmm6
	pand xmm8, xmm14
	pxor xmm6, xmm8
	psllq xmm8, 2
	pxor xmm4, xmm8
	movdqa xmm8, xmm5
	psrlq xmm8, 2
	pxor xmm8, xmm7
	pand xmm8, xmm14
	pxor xmm7, xmm8
	psllq xmm8, 2
	pxor xmm5, xmm8
	movdqa xmm8, xmm0
	psrlq xmm8, 1
	pxor xmm8, xmm1
	pand xmm8, xmm15
	pxor xmm1, xmm8
	psllq xmm8, 1
	pxor xmm0, xmm8
	movdqa xmm8, xmm2
	psrlq xmm8, 1
	pxor xmm8, xmm3
	pand xmm8, xmm15
	pxor xmm3, xmm8
	psllq xmm8, 1
	pxor xmm2, xmm8
	movdqa xmm8, xmm4
	psrlq xmm8, 1
	pxor xmm8, xmm5
	pand xmm8, xmm15
	pxor xmm5, xmm8
	psllq xmm8, 1
	pxor xmm4, xmm8
	movdqa xmm8, xmm6
	psrlq xmm8, 1
	pxor xmm8, xmm7
	pand xmm8, xmm15
	pxor xmm7, xmm8
	psllq xmm8, 1
	pxor xmm6, xmm8
	movdqu XMMWORD PTR [rsi], xmm0
	movdqu XMMWORD PTR [rsi+16], xmm1
	movdqu XMMWORD PTR [rsi+32], xmm2
	movdqu XMMWORD PTR [rsi+48], xmm3
	movdqu XMMWORD PTR [rsi+64], xmm4
	movdqu XMMWORD PTR [rsi+80], xmm5
	movdqu XMMWORD PTR [rsi+96], xmm6
	movdqu XMMWORD PTR [rsi+112], xmm7
	add rsi, 128
	sub r11, 1
	jne 24b
	sub rsi, 1024
	movabs rbx, -1
	movq xmm15, rbx
	punpcklqdq xmm15, xmm15
	mov r11, 3
25:
	cmp r11, 3
	je 26f
	cmp r11, 2
	je 28f
	mov r8, rdi
	add r8, 120
	mov r9, -8
	jmp 29f
28:
	mov r8, rdi
	add r8, 128
	mov r9, 8
29:
	jmp 27f
26:
	mov r8, rdi
	add r8, 376
	mov r9, -8
27:
	mov r10, 16
	mov r12, rsi
	add r12, 16
	mov r13, rsi
210:
	mov rax, QWORD PTR [r8]
	add r8, r9
	ror rax, 48
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm5, XMMWORD PTR [r12]
	pxor xmm5, xmm14
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm4, XMMWORD PTR [r12+992]
	pxor xmm4, xmm14
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm3, XMMWORD PTR [r12+864]
	pxor xmm3, xmm14
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm2, XMMWORD PTR [r12+736]
	pxor xmm2, xmm14
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm1, XMMWORD PTR [r12+608]
	pxor xmm1, xmm14
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm0, XMMWORD PTR [r12+480]
	pxor xmm0, xmm14
	movdqa xmm6, xmm1
	pandn xmm6, xmm5
	movdqa xmm7, xmm2
	pxor xmm7, xmm6
	movdqa xmm8, xmm3
	por xmm8, xmm0
	movdqa xmm9, xmm5
	pxor xmm9, xmm3
	movdqa xmm10, xmm8
	pand xmm10, xmm9
	movdqa xmm11, xmm2
	pxor xmm11, xmm10
	movdqa xmm12, xmm7
	pandn xmm12, xmm11
	movdqa xmm13, xmm1
	pxor xmm13, xmm0
	movdqa xmm14, xmm3
	pxor xmm14, xmm13
	pandn xmm14, xmm7
	por xmm10, xmm0
	pxor xmm14, xmm10
	movdqa xmm10, xmm12
	pandn xmm10, xmm14
	por xmm0, xmm5
	movdqu XMMWORD PTR [rcx], xmm10
	movdqa xmm10, xmm14
	por xmm10, xmm0
	pandn xmm11, xmm1
	movdqu XMMWORD PTR [rcx+16], xmm1
	movdqa xmm1, xmm10
	pxor xmm1, xmm11
	pandn xmm0, xmm2
	pxor xmm0, xmm11
	pandn xmm9, xmm13
	por xmm0, xmm9
	pandn xmm6, xmm3
	movdqa xmm3, xmm7
	pxor xmm3, xmm10
	pandn xmm6, xmm3
	movdqa xmm3, xmm6
	pxor xmm3, xmm15
	pand xmm14, xmm8
	pxor xmm3, xmm14
	por xmm1, xmm4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	pxor xmm6, xmm13
	por xmm11, xmm6
	pxor xmm11, xmm8
	pxor xmm5, xmm11
	pxor xmm3, xmm5
	por xmm12, xmm4
	pxor xmm12, xmm3
	pxor xmm8, xmm10
	por xmm8, xmm0
	pxor xmm8, xmm5
	por xmm13, xmm3
	pxor xmm13, xmm8
	movdqu xmm3, XMMWORD PTR [rcx]
	movdqa xmm10, xmm3
	por xmm10, xmm4
	pxor xmm10, xmm13
	movdqu xmm13, XMMWORD PTR [rcx+16]
	por xmm13, xmm7
	pandn xmm8, xmm13
	pand xmm3, xmm5
	pxor xmm8, xmm3
	por xmm8, xmm4
	pxor xmm8, xmm0
	movdqa xmm0, xmm8
	movdqa xmm2, xmm10
	movdqa xmm3, xmm12
	movdqu xmm14, XMMWORD PTR [r13+128]
	pxor xmm0, xmm14
	movdqu XMMWORD PTR [r13+128], xmm0
	movdqu xmm14, XMMWORD PTR [r13+160]
	pxor xmm1, xmm14
	movdqu XMMWORD PTR [r13+160], xmm1
	movdqu xmm14, XMMWORD PTR [r13+928]
	pxor xmm2, xmm14
	movdqu XMMWORD PTR [r13+928], xmm2
	movdqu xmm14, XMMWORD PTR [r13+960]
	pxor xmm3, xmm14
	movdqu XMMWORD PTR [r13+960], xmm3
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm5, XMMWORD PTR [r12+608]
	pxor xmm5, xmm14
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm4, XMMWORD PTR [r12+480]
	pxor xmm4, xmm14
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm3, XMMWORD PTR [r12+352]
	pxor xmm3, xmm14
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm2, XMMWORD PTR [r12+224]
	pxor xmm2, xmm14
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm1, XMMWORD PTR [r12+96]
	pxor xmm1, xmm14
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm0, XMMWORD PTR [r12+960]
	pxor xmm0, xmm14
	movdqa xmm6, xmm4
	pxor xmm6, xmm1
	movdqa xmm7, xmm0
	pandn xmm7, xmm5
	pandn xmm7, xmm1
	movdqa xmm8, xmm4
	por xmm8, xmm7
	movdqa xmm9, xmm0
	pandn xmm9, xmm6
	movdqa xmm10, xmm5
	pand xmm10, xmm6
	pxor xmm1, xmm10
	movdqa xmm10, xmm9
	pandn xmm10, xmm1
	movdqa xmm11, xmm3
	pand xmm11, xmm0
	pxor xmm7, xmm9
	pand xmm7, xmm8
	movdqa xmm9, xmm11
	pandn xmm9, xmm7
	movdqa xmm12, xmm3
	pand xmm12, xmm7
	pxor xmm5, xmm15
	pxor xmm5, xmm12
	pxor xmm0, xmm6
	movdqa xmm13, xmm11
	pandn xmm13, xmm0
	movdqa xmm14, xmm5
	pxor xmm14, xmm13
	pandn xmm9, xmm2
	pxor xmm9, xmm14
	pandn xmm13, xmm4
	pxor xmm1, xmm13
	por xmm5, xmm1
	pxor xmm5, xmm1
	pxor xmm3, xmm0
	pxor xmm5, xmm3
	movdqa xmm4, xmm2
	pandn xmm4, xmm8
	pxor xmm4, xmm5
	pxor xmm12, xmm13
	por xmm3, xmm12
	pxor xmm8, xmm14
	por xmm11, xmm8
	movdqa xmm12, xmm3
	pxor xmm12, xmm11
	pxor xmm7, xmm14
	pxor xmm5, xmm7
	pand xmm11, xmm5
	pand xmm6, xmm3
	pxor xmm11, xmm6
	movdqa xmm6, xmm11
	por xmm6, xmm2
	pxor xmm6, xmm12
	pandn xmm1, xmm11
	por xmm0, xmm8
	pxor xmm1, xmm0
	por xmm10, xmm2
	pxor xmm10, xmm1
	movdqa xmm0, xmm10
	movdqa xmm1, xmm6
	movdqa xmm2, xmm9
	movdqa xmm3, xmm4
	movdqu xmm14, XMMWORD PTR [r13+800]
	pxor xmm0, xmm14
	movdqu XMMWORD PTR [r13+800], xmm0
	movdqu xmm14, XMMWORD PTR [r13+864]
	pxor xmm1, xmm14
	movdqu XMMWORD PTR [r13+864], xmm1
	movdqu xmm14, XMMWORD PTR [r13+512]
	pxor xmm2, xmm14
	movdqu XMMWORD PTR [r13+512], xmm2
	movdqu xmm14, XMMWORD PTR [r13+448]
	pxor xmm3, xmm14
	movdqu XMMWORD PTR [r13+448], xmm3
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm5, XMMWORD PTR [r12+96]
	pxor xmm5, xmm14
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm4, XMMWORD PTR [r12+960]
	pxor xmm4, xmm14
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm3, XMMWORD PTR [r12+832]
	pxor xmm3, xmm14
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm2, XMMWORD PTR [r12+704]
	pxor xmm2, xmm14
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm1, XMMWORD PTR [r12+576]
	pxor xmm1, xmm14
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm0, XMMWORD PTR [r12+448]
	pxor xmm0, xmm14
	movdqa xmm6, xmm4
	pandn xmm6, xmm5
	movdqa xmm7, xmm3
	pxor xmm7, xmm0
	movdqa xmm8, xmm6
	por xmm8, xmm7
	movdqa xmm9, xmm2
	pxor xmm9, xmm0
	movdqa xmm10, xmm5
	pandn xmm10, xmm9
	movdqa xmm11, xmm8
	pxor xmm11, xmm10
	movdqa xmm12, xmm4
	pxor xmm12, xmm7
	movdqa xmm13, xmm0
	pandn xmm13, xmm12
	pxor xmm8, xmm13
	movdqa xmm13, xmm8
	pandn xmm13, xmm11
	movdqa xmm14, xmm0
	pand xmm14, xmm11
	por xmm14, xmm2
	pand xmm14, xmm5
	pxor xmm14, xmm12
	movdqu XMMWORD PTR [rcx], xmm6
	movdqa xmm6, xmm1
	pandn xmm6, xmm11
	pxor xmm6, xmm14
	pand xmm7, xmm9
	movdqa xmm9, xmm5
	pxor xmm9, xmm2
	movdqu XMMWORD PTR [rcx+16], xmm6
	movdqa xmm6, xmm8
	pxor xmm6, xmm9
	por xmm6, xmm3
	pandn xmm7, xmm6
	por xmm10, xmm9
	movdqa xmm9, xmm10
	pandn xmm9, xmm14
	pand xmm0, xmm2
	movdqa xmm6, xmm4
	pandn xmm6, xmm0
	pxor xmm9, xmm6
	pand xmm8, xmm9
	por xmm0, xmm12
	pandn xmm8, xmm0
	pxor xmm5, xmm8
	pand xmm7, xmm1
	pxor xmm7, xmm5
	pxor xmm11, xmm15
	por xmm4, xmm11
	por xmm3, xmm4
	pxor xmm12, xmm3
	pxor xmm10, xmm12
	pandn xmm13, xmm1
	pxor xmm13, xmm10
	pand xmm2, xmm11
	pxor xmm14, xmm2
	por xmm12, xmm14
	movdqu xmm14, XMMWORD PTR [rcx]
	pxor xmm14, xmm5
	pxor xmm12, xmm14
	por xmm9, xmm1
	pxor xmm9, xmm12
	movdqu xmm0, XMMWORD PTR [rcx+16]
	movdqa xmm1, xmm9
	movdqa xmm2, xmm7
	movdqa xmm3, xmm13
	movdqu xmm14, XMMWORD PTR [r13+352]
	pxor xmm0, xmm14
	movdqu XMMWORD PTR [r13+352], xmm0
	movdqu xmm14, XMMWORD PTR [r13+256]
	pxor xmm1, xmm14
	movdqu XMMWORD PTR [r13+256], xmm1
	movdqu xmm14, XMMWORD PTR [r13+64]
	pxor xmm2, xmm14
	movdqu XMMWORD PTR [r13+64], xmm2
	movdqu xmm14, XMMWORD PTR [r13+32]
	pxor xmm3, xmm14
	movdqu XMMWORD PTR [r13+32], xmm3
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm5, XMMWORD PTR [r12+576]
	pxor xmm5, xmm14
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm4, XMMWORD PTR [r12+448]
	pxor xmm4, xmm14
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm3, XMMWORD PTR [r12+320]
	pxor xmm3, xmm14
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm2, XMMWORD PTR [r12+192]
	pxor xmm2, xmm14
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm1, XMMWORD PTR [r12+64]
	pxor xmm1, xmm14
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm0, XMMWORD PTR [r12+928]
	pxor xmm0, xmm14
	pxor xmm5, xmm3
	pxor xmm3, xmm1
	movdqa xmm6, xmm4
	por xmm6, xmm2
	pxor xmm6, xmm1
	pandn xmm6, xmm3
	movdqa xmm7, xmm4
	pandn xmm7, xmm3
	movdqa xmm8, xmm2
	pxor xmm8, xmm7
	movdqa xmm9, xmm5
	por xmm9, xmm8
	por xmm9, xmm6
	pxor xmm9, xmm6
	movdqa xmm10, xmm4
	pxor xmm10, xmm9
	pand xmm8, xmm10
	por xmm3, xmm8
	pxor xmm3, xmm8
	pxor xmm5, xmm10
	pandn xmm3, xmm5
	pxor xmm6, xmm3
	pxor xmm4, xmm2
	por xmm1, xmm7
	pxor xmm5, xmm1
	movdqa xmm1, xmm4
	pandn xmm1, xmm5
	pxor xmm9, xmm1
	movdqa xmm1, xmm6
	pandn xmm1, xmm0
	pxor xmm1, xmm9
	pxor xmm9, xmm15
	movdqa xmm7, xmm0
	pandn xmm7, xmm6
	pxor xmm7, xmm9
	pxor xmm6, xmm9
	pandn xmm4, xmm6
	por xmm8, xmm4
	pxor xmm5, xmm8
	movdqa xmm8, xmm10
	por xmm8, xmm0
	pxor xmm8, xmm5
	pand xmm0, xmm10
	pxor xmm0, xmm5
	movdqu XMMWORD PTR [rcx], xmm1
	movdqa xmm1, xmm8
	movdqa xmm2, xmm7
	movdqu xmm3, XMMWORD PTR [rcx]
	movdqu xmm14, XMMWORD PTR [r13+992]
	pxor xmm0, xmm14
	movdqu XMMWORD PTR [r13+992], xmm0
	movdqu xmm14, XMMWORD PTR [r13+832]
	pxor xmm1, xmm14
	movdqu XMMWORD PTR [r13+832], xmm1
	movdqu xmm14, XMMWORD PTR [r13+544]
	pxor xmm2, xmm14
	movdqu XMMWORD PTR [r13+544], xmm2
	movdqu xmm14, XMMWORD PTR [r13+768]
	pxor xmm3, xmm14
	movdqu XMMWORD PTR [r13+768], xmm3
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm5, XMMWORD PTR [r12+64]
	pxor xmm5, xmm14
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm4, XMMWORD PTR [r12+928]
	pxor xmm4, xmm14
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm3, XMMWORD PTR [r12+800]
	pxor xmm3, xmm14
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm2, XMMWORD PTR [r12+672]
	pxor xmm2, xmm14
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm1, XMMWORD PTR [r12+544]
	pxor xmm1, xmm14
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm0, XMMWORD PTR [r12+416]
	pxor xmm0, xmm14
	movdqa xmm6, xmm5
	por xmm6, xmm3
	movdqa xmm7, xmm0
	pandn xmm7, xmm6
	movdqa xmm8, xmm5
	pxor xmm8, xmm7
	movdqa xmm9, xmm3
	pxor xmm9, xmm8
	movdqa xmm10, xmm2
	por xmm10, xmm9
	por xmm7, xmm2
	pxor xmm7, xmm2
	pxor xmm3, xmm7
	movdqa xmm7, xmm1
	pand xmm7, xmm3
	por xmm9, xmm5
	pxor xmm7, xmm9
	pxor xmm7, xmm2
	pxor xmm0, xmm7
	movdqa xmm11, xmm8
	por xmm11, xmm0
	movdqa xmm12, xmm1
	pand xmm12, xmm11
	movdqa xmm13, xmm8
	pxor xmm13, xmm12
	movdqa xmm14, xmm2
	pand xmm14, xmm9
	pxor xmm13, xmm14
	por xmm11, xmm5
	pxor xmm11, xmm5
	movdqa xmm14, xmm3
	pxor xmm14, xmm11
	pxor xmm1, xmm10
	pandn xmm14, xmm1
	pxor xmm14, xmm15
	por xmm14, xmm4
	pxor xmm14, xmm4
	pxor xmm14, xmm7
	movdqa xmm7, xmm12
	pandn xmm7, xmm3
	pxor xmm11, xmm1
	por xmm11, xmm13
	pandn xmm7, xmm11
	movdqa xmm11, xmm7
	pandn xmm11, xmm10
	pand xmm0, xmm7
	pxor xmm1, xmm0
	pand xmm9, xmm3
	por xmm9, xmm1
	pxor xmm12, xmm9
	pand xmm12, xmm4
	pxor xmm12, xmm13
	pxor xmm5, xmm6
	pxor xmm7, xmm5
	pand xmm2, xmm1
	pxor xmm7, xmm2
	por xmm11, xmm4
	pxor xmm11, xmm7
	pxor xmm3, xmm10
	pandn xmm7, xmm3
	pxor xmm8, xmm1
	pxor xmm7, xmm8
	pand xmm10, xmm4
	pxor xmm10, xmm7
	movdqa xmm0, xmm12
	movdqa xmm1, xmm14
	movdqa xmm2, xmm10
	movdqa xmm3, xmm11
	movdqu xmm14, XMMWORD PTR [r13+736]
	pxor xmm0, xmm14
	movdqu XMMWORD PTR [r13+736], xmm0
	movdqu xmm14, XMMWORD PTR [r13+896]
	pxor xmm1, xmm14
	movdqu XMMWORD PTR [r13+896], xmm1
	movdqu xmm14, XMMWORD PTR [r13+320]
	pxor xmm2, xmm14
	movdqu XMMWORD PTR [r13+320], xmm2
	movdqu xmm14, XMMWORD PTR [r13+96]
	pxor xmm3, xmm14
	movdqu XMMWORD PTR [r13+96], xmm3
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm5, XMMWORD PTR [r12+544]
	pxor xmm5, xmm14
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm4, XMMWORD PTR [r12+416]
	pxor xmm4, xmm14
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm3, XMMWORD PTR [r12+288]
	pxor xmm3, xmm14
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm2, XMMWORD PTR [r12+160]
	pxor xmm2, xmm14
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm1, XMMWORD PTR [r12+32]
	pxor xmm1, xmm14
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm0, XMMWORD PTR [r12+896]
	pxor xmm0, xmm14
	movdqa xmm6, xmm4
	pxor xmm6, xmm1
	movdqa xmm7, xmm4
	por xmm7, xmm0
	pand xmm7, xmm5
	pxor xmm6, xmm7
	movdqa xmm8, xmm0
	pxor xmm8, xmm6
	movdqa xmm9, xmm8
	pandn xmm9, xmm1
	pand xmm8, xmm5
	movdqa xmm10, xmm4
	pxor xmm10, xmm8
	movdqa xmm11, xmm5
	pxor xmm11, xmm3
	movdqa xmm12, xmm10
	por xmm12, xmm11
	movdqa xmm13, xmm6
	pxor xmm13, xmm12
	movdqa xmm14, xmm3
	pand xmm14, xmm13
	movdqu XMMWORD PTR [rcx], xmm8
	movdqa xmm8, xmm0
	pandn xmm8, xmm14
	por xmm10, xmm9
	movdqu XMMWORD PTR [rcx+16], xmm6
	movdqa xmm6, xmm8
	pxor xmm6, xmm10
	movdqu XMMWORD PTR [rcx+32], xmm9
	movdqa xmm9, xmm6
	pand xmm9, xmm2
	pxor xmm9, xmm13
	pxor xmm12, xmm4
	movdqu XMMWORD PTR [rcx+48], xmm9
	movdqa xmm9, xmm12
	pandn xmm9, xmm0
	pxor xmm3, xmm9
	movdqa xmm9, xmm14
	pandn xmm9, xmm1
	por xmm9, xmm3
	por xmm4, xmm11
	pxor xmm6, xmm4
	por xmm7, xmm9
	pxor xmm6, xmm7
	por xmm13, xmm5
	pand xmm10, xmm13
	pxor xmm10, xmm3
	pandn xmm8, xmm10
	movdqu xmm13, XMMWORD PTR [rcx+32]
	por xmm13, xmm2
	pxor xmm13, xmm8
	movdqu xmm8, XMMWORD PTR [rcx+16]
	pxor xmm8, xmm10
	pandn xmm8, xmm1
	pxor xmm4, xmm15
	pxor xmm12, xmm4
	pxor xmm8, xmm12
	por xmm8, xmm2
	pxor xmm8, xmm2
	pxor xmm8, xmm6
	movdqu xmm6, XMMWORD PTR [rcx]
	pxor xmm0, xmm6
	pxor xmm5, xmm3
	pand xmm0, xmm5
	pxor xmm14, xmm12
	pxor xmm0, xmm14
	pandn xmm2, xmm9
	pxor xmm2, xmm0
	movdqu xmm0, XMMWORD PTR [rcx+48]
	movdqa xmm1, xmm13
	movdqu XMMWORD PTR [rcx], xmm2
	movdqa xmm2, xmm8
	movdqu xmm3, XMMWORD PTR [rcx]
	movdqu xmm14, XMMWORD PTR [r13+672]
	pxor xmm0, xmm14
	movdqu XMMWORD PTR [r13+672], xmm0
	movdqu xmm14, XMMWORD PTR [r13+704]
	pxor xmm1, xmm14
	movdqu XMMWORD PTR [r13+704], xmm1
	movdqu xmm14, XMMWORD PTR [r13+384]
	pxor xmm2, xmm14
	movdqu XMMWORD PTR [r13+384], xmm2
	movdqu xmm14, XMMWORD PTR [r13+608]
	pxor xmm3, xmm14
	movdqu XMMWORD PTR [r13+608], xmm3
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm5, XMMWORD PTR [r12+32]
	pxor xmm5, xmm14
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm4, XMMWORD PTR [r12+896]
	pxor xmm4, xmm14
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm3, XMMWORD PTR [r12+768]
	pxor xmm3, xmm14
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm2, XMMWORD PTR [r12+640]
	pxor xmm2, xmm14
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm1, XMMWORD PTR [r12+512]
	pxor xmm1, xmm14
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm0, XMMWORD PTR [r12+384]
	pxor xmm0, xmm14
	movdqa xmm6, xmm2
	pxor xmm6, xmm1
	movdqa xmm7, xmm3
	pxor xmm7, xmm6
	movdqa xmm8, xmm0
	pand xmm8, xmm7
	movdqa xmm9, xmm2
	pand xmm9, xmm6
	movdqa xmm10, xmm4
	pxor xmm10, xmm9
	movdqa xmm11, xmm8
	pand xmm11, xmm10
	movdqa xmm12, xmm0
	pand xmm12, xmm9
	movdqa xmm13, xmm3
	pxor xmm13, xmm12
	movdqa xmm14, xmm10
	por xmm14, xmm13
	pxor xmm6, xmm0
	movdqu XMMWORD PTR [rcx], xmm0
	movdqa xmm0, xmm14
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [rcx+16], xmm9
	movdqa xmm9, xmm11
	pandn xmm9, xmm5
	pxor xmm9, xmm0
	pandn xmm7, xmm1
	movdqa xmm0, xmm10
	por xmm0, xmm7
	pxor xmm13, xmm8
	pxor xmm0, xmm13
	pxor xmm8, xmm6
	por xmm2, xmm8
	pxor xmm2, xmm8
	movdqa xmm6, xmm2
	pandn xmm6, xmm10
	pxor xmm1, xmm13
	pxor xmm6, xmm1
	pandn xmm12, xmm8
	por xmm2, xmm12
	pxor xmm14, xmm4
	pand xmm14, xmm6
	pxor xmm14, xmm2
	movdqa xmm8, xmm14
	pand xmm8, xmm5
	pxor xmm8, xmm6
	pandn xmm3, xmm10
	por xmm12, xmm3
	movdqu xmm3, XMMWORD PTR [rcx+16]
	por xmm3, xmm6
	pand xmm12, xmm3
	pxor xmm14, xmm12
	pxor xmm7, xmm2
	movdqu xmm2, XMMWORD PTR [rcx]
	pand xmm2, xmm7
	por xmm11, xmm2
	pxor xmm12, xmm11
	movdqa xmm2, xmm5
	pandn xmm2, xmm12
	pxor xmm2, xmm0
	pand xmm4, xmm11
	pxor xmm0, xmm15
	pxor xmm4, xmm0
	pxor xmm12, xmm4
	por xmm14, xmm5
	pxor xmm14, xmm12
	movdqa xmm0, xmm9
	movdqa xmm1, xmm8
	movdqu XMMWORD PTR [rcx], xmm2
	movdqa xmm2, xmm14
	movdqu xmm3, XMMWORD PTR [rcx]
	movdqu xmm14, XMMWORD PTR [r13+224]
	pxor xmm0, xmm14
	movdqu XMMWORD PTR [r13+224], xmm0
	movdqu xmm14, XMMWORD PTR [r13+288]
	pxor xmm1, xmm14
	movdqu XMMWORD PTR [r13+288], xmm1
	movdqu xmm14, XMMWORD PTR [r13+576]
	pxor xmm2, xmm14
	movdqu XMMWORD PTR [r13+576], xmm2
	movdqu xmm14, XMMWORD PTR [r13]
	pxor xmm3, xmm14
	movdqu XMMWORD PTR [r13], xmm3
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm5, XMMWORD PTR [r12+512]
	pxor xmm5, xmm14
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm4, XMMWORD PTR [r12+384]
	pxor xmm4, xmm14
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm3, XMMWORD PTR [r12+256]
	pxor xmm3, xmm14
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm2, XMMWORD PTR [r12+128]
	pxor xmm2, xmm14
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm1, XMMWORD PTR [r12]
	pxor xmm1, xmm14
	add rax, rax
	sbb rbx, rbx
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movdqu xmm0, XMMWORD PTR [r12+992]
	pxor xmm0, xmm14
	movdqa xmm6, xmm4
	pandn xmm6, xmm3
	movdqa xmm7, xmm3
	pandn xmm7, xmm1
	pxor xmm7, xmm2
	movdqa xmm8, xmm5
	pand xmm8, xmm7
	movdqa xmm9, xmm6
	pandn xmm9, xmm8
	movdqa xmm10, xmm7
	pandn xmm10, xmm4
	movdqa xmm11, xmm5
	por xmm11, xmm10
	movdqa xmm12, xmm3
	pandn xmm12, xmm4
	pxor xmm12, xmm1
	movdqa xmm13, xmm11
	pand xmm13, xmm12
	por xmm8, xmm13
	pxor xmm7, xmm15
	pxor xmm13, xmm7
	pandn xmm11, xmm3
	pxor xmm13, xmm11
	pxor xmm6, xmm13
	movdqa xmm11, xmm9
	por xmm11, xmm0
	pxor xmm11, xmm6
	pxor xmm6, xmm5
	movdqa xmm3, xmm1
	pand xmm3, xmm6
	pxor xmm13, xmm4
	pxor xmm3, xmm13
	pxor xmm10, xmm3
	pxor xmm3, xmm8
	por xmm4, xmm3
	pxor xmm1, xmm6
	pxor xmm4, xmm1
	pand xmm8, xmm0
	pxor xmm8, xmm4
	pxor xmm12, xmm10
	por xmm13, xmm2
	pxor xmm13, xmm12
	pxor xmm5, xmm13
	pand xmm5, xmm0
	pxor xmm5, xmm10
	pandn xmm2, xmm12
	pand xmm4, xmm2
	pxor xmm9, xmm13
	pxor xmm4, xmm9
	por xmm4, xmm0
	pxor xmm4, xmm10
	movdqa xmm0, xmm5
	movdqa xmm1, xmm8
	movdqa xmm2, xmm11
	movdqa xmm3, xmm4
	movdqu xmm14, XMMWORD PTR [r13+416]
	pxor xmm0, xmm14
	movdqu XMMWORD PTR [r13+416], xmm0
	movdqu xmm14, XMMWORD PTR [r13+192]
	pxor xmm1, xmm14
	movdqu XMMWORD PTR [r13+192], xmm1
	movdqu xmm14, XMMWORD PTR [r13+640]
	pxor xmm2, xmm14
	movdqu XMMWORD PTR [r13+640], xmm2
	movdqu xmm14, XMMWORD PTR [r13+480]
	pxor xmm3, xmm14
	movdqu XMMWORD PTR [r13+480], xmm3
	mov rbx, r12
	mov r12, r13
	mov r13, rbx
	sub r10, 1
	jne 210b
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+16]
	movdqu XMMWORD PTR [rsi], xmm1
	movdqu XMMWORD PTR [rsi+16], xmm0
	movdqu xmm0, XMMWORD PTR [rsi+128]
	movdqu xmm1, XMMWORD PTR [rsi+144]
	movdqu XMMWORD PTR [rsi+128], xmm1
	movdqu XMMWORD PTR [rsi+144], xmm0
	movdqu xmm0, XMMWORD PTR [rsi+256]
	movdqu xmm1, XMMWORD PTR [rsi+272]
	movdqu XMMWORD PTR [rsi+256], xmm1
	movdqu XMMWORD PTR [rsi+272], xmm0
	movdqu xmm0, XMMWORD PTR [rsi+384]
	movdqu xmm1, XMMWORD PTR [rsi+400]
	movdqu XMMWORD PTR [rsi+384], xmm1
	movdqu XMMWORD PTR [rsi+400], xmm0
	movdqu xmm0, XMMWORD PTR [rsi+512]
	movdqu xmm1, XMMWORD PTR [rsi+528]
	movdqu XMMWORD PTR [rsi+512], xmm1
	movdqu XMMWORD PTR [rsi+528], xmm0
	movdqu xmm0, XMMWORD PTR [rsi+640]
	movdqu xmm1, XMMWORD PTR [rsi+656]
	movdqu XMMWORD PTR [rsi+640], xmm1
	movdqu XMMWORD PTR [rsi+656], xmm0
	movdqu xmm0, XMMWORD PTR [rsi+768]
	movdqu xmm1, XMMWORD PTR [rsi+784]
	movdqu XMMWORD PTR [rsi+768], xmm1
	movdqu XMMWORD PTR [rsi+784], xmm0
	movdqu xmm0, XMMWORD PTR [rsi+896]
	movdqu xmm1, XMMWORD PTR [rsi+912]
	movdqu XMMWORD PTR [rsi+896], xmm1
	movdqu XMMWORD PTR [rsi+912], xmm0
	movdqu xmm0, XMMWORD PTR [rsi+32]
	movdqu xmm1, XMMWORD PTR [rsi+48]
	movdqu XMMWORD PTR [rsi+32], xmm1
	movdqu XMMWORD PTR [rsi+48], xmm0
	movdqu xmm0, XMMWORD PTR [rsi+160]
	movdqu xmm1, XMMWORD PTR [rsi+176]
	movdqu XMMWORD PTR [rsi+160], xmm1
	movdqu XMMWORD PTR [rsi+176], xmm0
	movdqu xmm0, XMMWORD PTR [rsi+288]
	movdqu xmm1, XMMWORD PTR [rsi+304]
	movdqu XMMWORD PTR [rsi+288], xmm1
	movdqu XMMWORD PTR [rsi+304], xmm0
	movdqu xmm0, XMMWORD PTR [rsi+416]
	movdqu xmm1, XMMWORD PTR [rsi+432]
	movdqu XMMWORD PTR [rsi+416], xmm1
	movdqu XMMWORD PTR [rsi+432], xmm0
	movdqu xmm0, XMMWORD PTR [rsi+544]
	movdqu xmm1, XMMWORD PTR [rsi+560]
	movdqu XMMWORD PTR [rsi+544], xmm1
	movdqu XMMWORD PTR [rsi+560], xmm0
	movdqu xmm0, XMMWORD PTR [rsi+672]
	movdqu xmm1, XMMWORD PTR [rsi+688]
	movdqu XMMWORD PTR [rsi+672], xmm1
	movdqu XMMWORD PTR [rsi+688], xmm0
	movdqu xmm0, XMMWORD PTR [rsi+800]
	movdqu xmm1, XMMWORD PTR [rsi+816]
	movdqu XMMWORD PTR [rsi+800], xmm1
	movdqu XMMWORD PTR [rsi+816], xmm0
	movdqu xmm0, XMMWORD PTR [rsi+928]
	movdqu xmm1, XMMWORD PTR [rsi+944]
	movdqu XMMWORD PTR [rsi+928], xmm1
	movdqu XMMWORD PTR [rsi+944], xmm0
	movdqu xmm0, XMMWORD PTR [rsi+64]
	movdqu xmm1, XMMWORD PTR [rsi+80]
	movdqu XMMWORD PTR [rsi+64], xmm1
	movdqu XMMWORD PTR [rsi+80], xmm0
	movdqu xmm0, XMMWORD PTR [rsi+192]
	movdqu xmm1, XMMWORD PTR [rsi+208]
	movdqu XMMWORD PTR [rsi+192], xmm1
	movdqu XMMWORD PTR [rsi+208], xmm0
	movdqu xmm0, XMMWORD PTR [rsi+320]
	movdqu xmm1, XMMWORD PTR [rsi+336]
	movdqu XMMWORD PTR [rsi+320], xmm1
	movdqu XMMWORD PTR [rsi+336], xmm0
	movdqu xmm0, XMMWORD PTR [rsi+448]
	movdqu xmm1, XMMWORD PTR [rsi+464]
	movdqu XMMWORD PTR [rsi+448], xmm1
	movdqu XMMWORD PTR [rsi+464], xmm0
	movdqu xmm0, XMMWORD PTR [rsi+576]
	movdqu xmm1, XMMWORD PTR [rsi+592]
	movdqu XMMWORD PTR [rsi+576], xmm1
	movdqu XMMWORD PTR [rsi+592], xmm0
	movdqu xmm0, XMMWORD PTR [rsi+704]
	movdqu xmm1, XMMWORD PTR [rsi+720]
	movdqu XMMWORD PTR [rsi+704], xmm1
	movdqu XMMWORD PTR [rsi+720], xmm0
	movdqu xmm0, XMMWORD PTR [rsi+832]
	movdqu xmm1, XMMWORD PTR [rsi+848]
	movdqu XMMWORD PTR [rsi+832], xmm1
	movdqu XMMWORD PTR [rsi+848], xmm0
	movdqu xmm0, XMMWORD PTR [rsi+960]
	movdqu xmm1, XMMWORD PTR [rsi+976]
	movdqu XMMWORD PTR [rsi+960], xmm1
	movdqu XMMWORD PTR [rsi+976], xmm0
	movdqu xmm0, XMMWORD PTR [rsi+96]
	movdqu xmm1, XMMWORD PTR [rsi+112]
	movdqu XMMWORD PTR [rsi+96], xmm1
	movdqu XMMWORD PTR [rsi+112], xmm0
	movdqu xmm0, XMMWORD PTR [rsi+224]
	movdqu xmm1, XMMWORD PTR [rsi+240]
	movdqu XMMWORD PTR [rsi+224], xmm1
	movdqu XMMWORD PTR [rsi+240], xmm0
	movdqu xmm0, XMMWORD PTR [rsi+352]
	movdqu xmm1, XMMWORD PTR [rsi+368]
	movdqu XMMWORD PTR [rsi+352], xmm1
	movdqu XMMWORD PTR [rsi+368], xmm0
	movdqu xmm0, XMMWORD PTR [rsi+480]
	movdqu xmm1, XMMWORD PTR [rsi+496]
	movdqu XMMWORD PTR [rsi+480], xmm1
	movdqu XMMWORD PTR [rsi+496], xmm0
	movdqu xmm0, XMMWORD PTR [rsi+608]
	movdqu xmm1, XMMWORD PTR [rsi+624]
	movdqu XMMWORD PTR [rsi+608], xmm1
	movdqu XMMWORD PTR [rsi+624], xmm0
	movdqu xmm0, XMMWORD PTR [rsi+736]
	movdqu xmm1, XMMWORD PTR [rsi+752]
	movdqu XMMWORD PTR [rsi+736], xmm1
	movdqu XMMWORD PTR [rsi+752], xmm0
	movdqu xmm0, XMMWORD PTR [rsi+864]
	movdqu xmm1, XMMWORD PTR [rsi+880]
	movdqu XMMWORD PTR [rsi+864], xmm1
	movdqu XMMWORD PTR [rsi+880], xmm0
	movdqu xmm0, XMMWORD PTR [rsi+992]
	movdqu xmm1, XMMWORD PTR [rsi+1008]
	movdqu XMMWORD PTR [rsi+992], xmm1
	movdqu XMMWORD PTR [rsi+1008], xmm0
	sub r11, 1
	jne 25b
	mov r11, 8
211:
	movabs rbx, 4294967295
	movq xmm13, rbx
	punpcklqdq xmm13, xmm13
	movabs rbx, 281470681808895
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movabs rbx, 71777214294589695
	movq xmm15, rbx
	punpcklqdq xmm15, xmm15
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+128]
	movdqu xmm2, XMMWORD PTR [rsi+256]
	movdqu xmm3, XMMWORD PTR [rsi+384]
	movdqu xmm4, XMMWORD PTR [rsi+512]
	movdqu xmm5, XMMWORD PTR [rsi+640]
	movdqu xmm6, XMMWORD PTR [rsi+768]
	movdqu xmm7, XMMWORD PTR [rsi+896]
	movdqa xmm8, xmm0
	psrlq xmm8, 32
	pxor xmm8, xmm4
	pand xmm8, xmm13
	pxor xmm4, xmm8
	psllq xmm8, 32
	pxor xmm0, xmm8
	movdqa xmm8, xmm1
	psrlq xmm8, 32
	pxor xmm8, xmm5
	pand xmm8, xmm13
	pxor xmm5, xmm8
	psllq xmm8, 32
	pxor xmm1, xmm8
	movdqa xmm8, xmm2
	psrlq xmm8, 32
	pxor xmm8, xmm6
	pand xmm8, xmm13
	pxor xmm6, xmm8
	psllq xmm8, 32
	pxor xmm2, xmm8
	movdqa xmm8, xmm3
	psrlq xmm8, 32
	pxor xmm8, xmm7
	pand xmm8, xmm13
	pxor xmm7, xmm8
	psllq xmm8, 32
	pxor xmm3, xmm8
	movdqa xmm8, xmm0
	psrlq xmm8, 16
	pxor xmm8, xmm2
	pand xmm8, xmm14
	pxor xmm2, xmm8
	psllq xmm8, 16
	pxor xmm0, xmm8
	movdqa xmm8, xmm1
	psrlq xmm8, 16
	pxor xmm8, xmm3
	pand xmm8, xmm14
	pxor xmm3, xmm8
	psllq xmm8, 16
	pxor xmm1, xmm8
	movdqa xmm8, xmm4
	psrlq xmm8, 16
	pxor xmm8, xmm6
	pand xmm8, xmm14
	pxor xmm6, xmm8
	psllq xmm8, 16
	pxor xmm4, xmm8
	movdqa xmm8, xmm5
	psrlq xmm8, 16
	pxor xmm8, xmm7
	pand xmm8, xmm14
	pxor xmm7, xmm8
	psllq xmm8, 16
	pxor xmm5, xmm8
	movdqa xmm8, xmm0
	psrlq xmm8, 8
	pxor xmm8, xmm1
	pand xmm8, xmm15
	pxor xmm1, xmm8
	psllq xmm8, 8
	pxor xmm0, xmm8
	movdqa xmm8, xmm2
	psrlq xmm8, 8
	pxor xmm8, xmm3
	pand xmm8, xmm15
	pxor xmm3, xmm8
	psllq xmm8, 8
	pxor xmm2, xmm8
	movdqa xmm8, xmm4
	psrlq xmm8, 8
	pxor xmm8, xmm5
	pand xmm8, xmm15
	pxor xmm5, xmm8
	psllq xmm8, 8
	pxor xmm4, xmm8
	movdqa xmm8, xmm6
	psrlq xmm8, 8
	pxor xmm8, xmm7
	pand xmm8, xmm15
	pxor xmm7, xmm8
	psllq xmm8, 8
	pxor xmm6, xmm8
	movdqu XMMWORD PTR [rsi], xmm0
	movdqu XMMWORD PTR [rsi+128], xmm1
	movdqu XMMWORD PTR [rsi+256], xmm2
	movdqu XMMWORD PTR [rsi+384], xmm3
	movdqu XMMWORD PTR [rsi+512], xmm4
	movdqu XMMWORD PTR [rsi+640], xmm5
	movdqu XMMWORD PTR [rsi+768], xmm6
	movdqu XMMWORD PTR [rsi+896], xmm7
	add rsi, 16
	sub r11, 1
	jne 211b
	sub rsi, 128
	mov r11, 8
212:
	movabs rbx, 1085102592571150095
	movq xmm13, rbx
	punpcklqdq xmm13, xmm13
	movabs rbx, 3689348814741910323
	movq xmm14, rbx
	punpcklqdq xmm14, xmm14
	movabs rbx, 6148914691236517205
	movq xmm15, rbx
	punpcklqdq xmm15, xmm15
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+16]
	movdqu xmm2, XMMWORD PTR [rsi+32]
	movdqu xmm3, XMMWORD PTR [rsi+48]
	movdqu xmm4, XMMWORD PTR [rsi+64]
	movdqu xmm5, XMMWORD PTR [rsi+80]
	movdqu xmm6, XMMWORD PTR [rsi+96]
	movdqu xmm7, XMMWORD PTR [rsi+112]
	movdqa xmm8, xmm0
	psrlq xmm8, 4
	pxor xmm8, xmm4
	pand xmm8, xmm13
	pxor xmm4, xmm8
	psllq xmm8, 4
	pxor xmm0, xmm8
	movdqa xmm8, xmm1
	psrlq xmm8, 4
	pxor xmm8, xmm5
	pand xmm8, xmm13
	pxor xmm5, xmm8
	psllq xmm8, 4
	pxor xmm1, xmm8
	movdqa xmm8, xmm2
	psrlq xmm8, 4
	pxor xmm8, xmm6
	pand xmm8, xmm13
	pxor xmm6, xmm8
	psllq xmm8, 4
	pxor xmm2, xmm8
	movdqa xmm8, xmm3
	psrlq xmm8, 4
	pxor xmm8, xmm7
	pand xmm8, xmm13
	pxor xmm7, xmm8
	psllq xmm8, 4
	pxor xmm3, xmm8
	movdqa xmm8, xmm0
	psrlq xmm8, 2
	pxor xmm8, xmm2
	pand xmm8, xmm14
	pxor xmm2, xmm8
	psllq xmm8, 2
	pxor xmm0, xmm8
	movdqa xmm8, xmm1
	psrlq xmm8, 2
	pxor xmm8, xmm3
	pand xmm8, xmm14
	pxor xmm3, xmm8
	psllq xmm8, 2
	pxor xmm1, xmm8
	movdqa xmm8, xmm4
	psrlq xmm8, 2
	pxor xmm8, xmm6
	pand xmm8, xmm14
	pxor xmm6, xmm8
	psllq xmm8, 2
	pxor xmm4, xmm8
	movdqa xmm8, xmm5
	psrlq xmm8, 2
	pxor xmm8, xmm7
	pand xmm8, xmm14
	pxor xmm7, xmm8
	psllq xmm8, 2
	pxor xmm5, xmm8
	movdqa xmm8, xmm0
	psrlq xmm8, 1
	pxor xmm8, xmm1
	pand xmm8, xmm15
	pxor xmm1, xmm8
	psllq xmm8, 1
	pxor xmm0, xmm8
	movdqa xmm8, xmm2
	psrlq xmm8, 1
	pxor xmm8, xmm3
	pand xmm8, xmm15
	pxor xmm3, xmm8
	psllq xmm8, 1
	pxor xmm2, xmm8
	movdqa xmm8, xmm4
	psrlq xmm8, 1
	pxor xmm8, xmm5
	pand xmm8, xmm15
	pxor xmm5, xmm8
	psllq xmm8, 1
	pxor xmm4, xmm8
	movdqa xmm8, xmm6
	psrlq xmm8, 1
	pxor xmm8, xmm7
	pand xmm8, xmm15
	pxor xmm7, xmm8
	psllq xmm8, 1
	pxor xmm6, xmm8
	movdqu XMMWORD PTR [rsi], xmm0
	movdqu XMMWORD PTR [rsi+16], xmm1
	movdqu XMMWORD PTR [rsi+32], xmm2
	movdqu XMMWORD PTR [rsi+48], xmm3
	movdqu XMMWORD PTR [rsi+64], xmm4
	movdqu XMMWORD PTR [rsi+80], xmm5
	movdqu XMMWORD PTR [rsi+96], xmm6
	movdqu XMMWORD PTR [rsi+112], xmm7
	add rsi, 128
	sub r11, 1
	jne 212b
	sub rsi, 1024
	add rsi, 1024
	sub rdx, 128
	cmp rdx, 128
	jae 22b
	mov rbx, QWORD PTR [rcx+1016]
	mov r12, QWORD PTR [rcx+1008]
	mov r13, QWORD PTR [rcx+1000]
	jmp 21f
20:
21:
	mov QWORD PTR [rcx+576], rbx
	mov QWORD PTR [rcx+584], rbp
	mov QWORD PTR [rcx+592], r12
	mov QWORD PTR [rcx+600], r13
	mov QWORD PTR [rcx+608], r14
	mov QWORD PTR [rcx+616], r15
	mov QWORD PTR [rcx+624], rdi
	mov QWORD PTR [rcx+632], rsi
	mov QWORD PTR [rcx+640], rdx
	cmp rdx, 0
	je 213f
215:
	mov rax, QWORD PTR [rcx+640]
	cmp rax, 64
	jb 216f
	mov rax, 64
	jmp 217f
216:
217:
	mov QWORD PTR [rcx+648], rax
	mov r8, QWORD PTR [rcx+624]
	mov r9, QWORD PTR [rcx+632]
	mov r10, QWORD PTR [rcx+640]
	mov r11, QWORD PTR [rcx+648]
	mov rsi, r9
	mov rdi, rcx
	add rdi, 64
	mov rdx, r11
218:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rsi, 8
	add rdi, 8
	sub rdx, 1
	jne 218b
	mov QWORD PTR [rcx+624], r8
	mov QWORD PTR [rcx+632], r9
	mov QWORD PTR [rcx+640], r10
	mov QWORD PTR [rcx+648], r11
	movabs r13, 4294967295
	movabs r14, 281470681808895
	movabs r15, 71777214294589695
	mov rax, QWORD PTR [rcx+64]
	mov rbx, QWORD PTR [rcx+128]
	mov rdx, QWORD PTR [rcx+192]
	mov rsi, QWORD PTR [rcx+256]
	mov rdi, QWORD PTR [rcx+320]
	mov rbp, QWORD PTR [rcx+384]
	mov r8, QWORD PTR [rcx+448]
	mov r9, QWORD PTR [rcx+512]
	mov r10, rax
	shr r10, 32
	xor r10, rdi
	and r10, r13
	xor rdi, r10
	ror r10, 32
	xor rax, r10
	mov r10, rbx
	shr r10, 32
	xor r10, rbp
	and r10, r13
	xor rbp, r10
	ror r10, 32
	xor rbx, r10
	mov r10, rdx
	shr r10, 32
	xor r10, r8
	and r10, r13
	xor r8, r10
	ror r10, 32
	xor rdx, r10
	mov r10, rsi
	shr r10, 32
	xor r10, r9
	and r10, r13
	xor r9, r10
	ror r10, 32
	xor rsi, r10
	mov r10, rax
	shr r10, 16
	xor r10, rdx
	and r10, r14
	xor rdx, r10
	ror r10, 48
	xor rax, r10
	mov r10, rbx
	shr r10, 16
	xor r10, rsi
	and r10, r14
	xor rsi, r10
	ror r10, 48
	xor rbx, r10
	mov r10, rdi
	shr r10, 16
	xor r10, r8
	and r10, r14
	xor r8, r10
	ror r10, 48
	xor rdi, r10
	mov r10, rbp
	shr r10, 16
	xor r10, r9
	and r10, r14
	xor r9, r10
	ror r10, 48
	xor rbp, r10
	mov r10, rax
	shr r10, 8
	xor r10, rbx
	and r10, r15
	xor rbx, r10
	ror r10, 56
	xor rax, r10
	mov r10, rdx
	shr r10, 8
	xor r10, rsi
	and r10, r15
	xor rsi, r10
	ror r10, 56
	xor rdx, r10
	mov r10, rdi
	shr r10, 8
	xor r10, rbp
	and r10, r15
	xor rbp, r10
	ror r10, 56
	xor rdi, r10
	mov r10, r8
	shr r10, 8
	xor r10, r9
	and r10, r15
	xor r9, r10
	ror r10, 56
	xor r8, r10
	mov QWORD PTR [rcx+64], rax
	mov QWORD PTR [rcx+128], rbx
	mov QWORD PTR [rcx+192], rdx
	mov QWORD PTR [rcx+256], rsi
	mov QWORD PTR [rcx+320], rdi
	mov QWORD PTR [rcx+384], rbp
	mov QWORD PTR [rcx+448], r8
	mov QWORD PTR [rcx+512], r9
	mov rax, QWORD PTR [rcx+72]
	mov rbx, QWORD PTR [rcx+136]
	mov rdx, QWORD PTR [rcx+200]
	mov rsi, QWORD PTR [rcx+264]
	mov rdi, QWORD PTR [rcx+328]
	mov rbp, QWORD PTR [rcx+392]
	mov r8, QWORD PTR [rcx+456]
	mov r9, QWORD PTR [rcx+520]
	mov r10, rax
	shr r10, 32
	xor r10, rdi
	and r10, r13
	xor rdi, r10
	ror r10, 32
	xor rax, r10
	mov r10, rbx
	shr r10, 32
	xor r10, rbp
	and r10, r13
	xor rbp, r10
	ror r10, 32
	xor rbx, r10
	mov r10, rdx
	shr r10, 32
	xor r10, r8
	and r10, r13
	xor r8, r10
	ror r10, 32
	xor rdx, r10
	mov r10, rsi
	shr r10, 32
	xor r10, r9
	and r10, r13
	xor r9, r10
	ror r10, 32
	xor rsi, r10
	mov r10, rax
	shr r10, 16
	xor r10, rdx
	and r10, r14
	xor rdx, r10
	ror r10, 48
	xor rax, r10
	mov r10, rbx
	shr r10, 16
	xor r10, rsi
	and r10, r14
	xor rsi, r10
	ror r10, 48
	xor rbx, r10
	mov r10, rdi
	shr r10, 16
	xor r10, r8
	and r10, r14
	xor r8, r10
	ror r10, 48
	xor rdi, r10
	mov r10, rbp
	shr r10, 16
	xor r10, r9
	and r10, r14
	xor r9, r10
	ror r10, 48
	xor rbp, r10
	mov r10, rax
	shr r10, 8
	xor r10, rbx
	and r10, r15
	xor rbx, r10
	ror r10, 56
	xor rax, r10
	mov r10, rdx
	shr r10, 8
	xor r10, rsi
	and r10, r15
	xor rsi, r10
	ror r10, 56
	xor rdx, r10
	mov r10, rdi
	shr r10, 8
	xor r10, rbp
	and r10, r15
	xor rbp, r10
	ror r10, 56
	xor rdi, r10
	mov r10, r8
	shr r10, 8
	xor r10, r9
	and r10, r15
	xor r9, r10
	ror r10, 56
	xor r8, r10
	mov QWORD PTR [rcx+72], rax
	mov QWORD PTR [rcx+136], rbx
	mov QWORD PTR [rcx+200], rdx
	mov QWORD PTR [rcx+264], rsi
	mov QWORD PTR [rcx+328], rdi
	mov QWORD PTR [rcx+392], rbp
	mov QWORD PTR [rcx+456], r8
	mov QWORD PTR [rcx+520], r9
	mov rax, QWORD PTR [rcx+80]
	mov rbx, QWORD PTR [rcx+144]
	mov rdx, QWORD PTR [rcx+208]
	mov rsi, QWORD PTR [rcx+272]
	mov rdi, QWORD PTR [rcx+336]
	mov rbp, QWORD PTR [rcx+400]
	mov r8, QWORD PTR [rcx+464]
	mov r9, QWORD PTR [rcx+528]
	mov r10, rax
	shr r10, 32
	xor r10, rdi
	and r10, r13
	xor rdi, r10
	ror r10, 32
	xor rax, r10
	mov r10, rbx
	shr r10, 32
	xor r10, rbp
	and r10, r13
	xor rbp, r10
	ror r10, 32
	xor rbx, r10
	mov r10, rdx
	shr r10, 32
	xor r10, r8
	and r10, r13
	xor r8, r10
	ror r10, 32
	xor rdx, r10
	mov r10, rsi
	shr r10, 32
	xor r10, r9
	and r10, r13
	xor r9, r10
	ror r10, 32
	xor rsi, r10
	mov r10, rax
	shr r10, 16
	xor r10, rdx
	and r10, r14
	xor rdx, r10
	ror r10, 48
	xor rax, r10
	mov r10, rbx
	shr r10, 16
	xor r10, rsi
	and r10, r14
	xor rsi, r10
	ror r10, 48
	xor rbx, r10
	mov r10, rdi
	shr r10, 16
	xor r10, r8
	and r10, r14
	xor r8, r10
	ror r10, 48
	xor rdi, r10
	mov r10, rbp
	shr r10, 16
	xor r10, r9
	and r10, r14
	xor r9, r10
	ror r10, 48
	xor rbp, r10
	mov r10, rax
	shr r10, 8
	xor r10, rbx
	and r10, r15
	xor rbx, r10
	ror r10, 56
	xor rax, r10
	mov r10, rdx
	shr r10, 8
	xor r10, rsi
	and r10, r15
	xor rsi, r10
	ror r10, 56
	xor rdx, r10
	mov r10, rdi
	shr r10, 8
	xor r10, rbp
	and r10, r15
	xor rbp, r10
	ror r10, 56
	xor rdi, r10
	mov r10, r8
	shr r10, 8
	xor r10, r9
	and r10, r15
	xor r9, r10
	ror r10, 56
	xor r8, r10
	mov QWORD PTR [rcx+80], rax
	mov QWORD PTR [rcx+144], rbx
	mov QWORD PTR [rcx+208], rdx
	mov QWORD PTR [rcx+272], rsi
	mov QWORD PTR [rcx+336], rdi
	mov QWORD PTR [rcx+400], rbp
	mov QWORD PTR [rcx+464], r8
	mov QWORD PTR [rcx+528], r9
	mov rax, QWORD PTR [rcx+88]
	mov rbx, QWORD PTR [rcx+152]
	mov rdx, QWORD PTR [rcx+216]
	mov rsi, QWORD PTR [rcx+280]
	mov rdi, QWORD PTR [rcx+344]
	mov rbp, QWORD PTR [rcx+408]
	mov r8, QWORD PTR [rcx+472]
	mov r9, QWORD PTR [rcx+536]
	mov r10, rax
	shr r10, 32
	xor r10, rdi
	and r10, r13
	xor rdi, r10
	ror r10, 32
	xor rax, r10
	mov r10, rbx
	shr r10, 32
	xor r10, rbp
	and r10, r13
	xor rbp, r10
	ror r10, 32
	xor rbx, r10
	mov r10, rdx
	shr r10, 32
	xor r10, r8
	and r10, r13
	xor r8, r10
	ror r10, 32
	xor rdx, r10
	mov r10, rsi
	shr r10, 32
	xor r10, r9
	and r10, r13
	xor r9, r10
	ror r10, 32
	xor rsi, r10
	mov r10, rax
	shr r10, 16
	xor r10, rdx
	and r10, r14
	xor rdx, r10
	ror r10, 48
	xor rax, r10
	mov r10, rbx
	shr r10, 16
	xor r10, rsi
	and r10, r14
	xor rsi, r10
	ror r10, 48
	xor rbx, r10
	mov r10, rdi
	shr r10, 16
	xor r10, r8
	and r10, r14
	xor r8, r10
	ror r10, 48
	xor rdi, r10
	mov r10, rbp
	shr r10, 16
	xor r10, r9
	and r10, r14
	xor r9, r10
	ror r10, 48
	xor rbp, r10
	mov r10, rax
	shr r10, 8
	xor r10, rbx
	and r10, r15
	xor rbx, r10
	ror r10, 56
	xor rax, r10
	mov r10, rdx
	shr r10, 8
	xor r10, rsi
	and r10, r15
	xor rsi, r10
	ror r10, 56
	xor rdx, r10
	mov r10, rdi
	shr r10, 8
	xor r10, rbp
	and r10, r15
	xor rbp, r10
	ror r10, 56
	xor rdi, r10
	mov r10, r8
	shr r10, 8
	xor r10, r9
	and r10, r15
	xor r9, r10
	ror r10, 56
	xor r8, r10
	mov QWORD PTR [rcx+88], rax
	mov QWORD PTR [rcx+152], rbx
	mov QWORD PTR [rcx+216], rdx
	mov QWORD PTR [rcx+280], rsi
	mov QWORD PTR [rcx+344], rdi
	mov QWORD PTR [rcx+408], rbp
	mov QWORD PTR [rcx+472], r8
	mov QWORD PTR [rcx+536], r9
	mov rax, QWORD PTR [rcx+96]
	mov rbx, QWORD PTR [rcx+160]
	mov rdx, QWORD PTR [rcx+224]
	mov rsi, QWORD PTR [rcx+288]
	mov rdi, QWORD PTR [rcx+352]
	mov rbp, QWORD PTR [rcx+416]
	mov r8, QWORD PTR [rcx+480]
	mov r9, QWORD PTR [rcx+544]
	mov r10, rax
	shr r10, 32
	xor r10, rdi
	and r10, r13
	xor rdi, r10
	ror r10, 32
	xor rax, r10
	mov r10, rbx
	shr r10, 32
	xor r10, rbp
	and r10, r13
	xor rbp, r10
	ror r10, 32
	xor rbx, r10
	mov r10, rdx
	shr r10, 32
	xor r10, r8
	and r10, r13
	xor r8, r10
	ror r10, 32
	xor rdx, r10
	mov r10, rsi
	shr r10, 32
	xor r10, r9
	and r10, r13
	xor r9, r10
	ror r10, 32
	xor rsi, r10
	mov r10, rax
	shr r10, 16
	xor r10, rdx
	and r10, r14
	xor rdx, r10
	ror r10, 48
	xor rax, r10
	mov r10, rbx
	shr r10, 16
	xor r10, rsi
	and r10, r14
	xor rsi, r10
	ror r10, 48
	xor rbx, r10
	mov r10, rdi
	shr r10, 16
	xor r10, r8
	and r10, r14
	xor r8, r10
	ror r10, 48
	xor rdi, r10
	mov r10, rbp
	shr r10, 16
	xor r10, r9
	and r10, r14
	xor r9, r10
	ror r10, 48
	xor rbp, r10
	mov r10, rax
	shr r10, 8
	xor r10, rbx
	and r10, r15
	xor rbx, r10
	ror r10, 56
	xor rax, r10
	mov r10, rdx
	shr r10, 8
	xor r10, rsi
	and r10, r15
	xor rsi, r10
	ror r10, 56
	xor rdx, r10
	mov r10, rdi
	shr r10, 8
	xor r10, rbp
	and r10, r15
	xor rbp, r10
	ror r10, 56
	xor rdi, r10
	mov r10, r8
	shr r10, 8
	xor r10, r9
	and r10, r15
	xor r9, r10
	ror r10, 56
	xor r8, r10
	mov QWORD PTR [rcx+96], rax
	mov QWORD PTR [rcx+160], rbx
	mov QWORD PTR [rcx+224], rdx
	mov QWORD PTR [rcx+288], rsi
	mov QWORD PTR [rcx+352], rdi
	mov QWORD PTR [rcx+416], rbp
	mov QWORD PTR [rcx+480], r8
	mov QWORD PTR [rcx+544], r9
	mov rax, QWORD PTR [rcx+104]
	mov rbx, QWORD PTR [rcx+168]
	mov rdx, QWORD PTR [rcx+232]
	mov rsi, QWORD PTR [rcx+296]
	mov rdi, QWORD PTR [rcx+360]
	mov rbp, QWORD PTR [rcx+424]
	mov r8, QWORD PTR [rcx+488]
	mov r9, QWORD PTR [rcx+552]
	mov r10, rax
	shr r10, 32
	xor r10, rdi
	and r10, r13
	xor rdi, r10
	ror r10, 32
	xor rax, r10
	mov r10, rbx
	shr r10, 32
	xor r10, rbp
	and r10, r13
	xor rbp, r10
	ror r10, 32
	xor rbx, r10
	mov r10, rdx
	shr r10, 32
	xor r10, r8
	and r10, r13
	xor r8, r10
	ror r10, 32
	xor rdx, r10
	mov r10, rsi
	shr r10, 32
	xor r10, r9
	and r10, r13
	xor r9, r10
	ror r10, 32
	xor rsi, r10
	mov r10, rax
	shr r10, 16
	xor r10, rdx
	and r10, r14
	xor rdx, r10
	ror r10, 48
	xor rax, r10
	mov r10, rbx
	shr r10, 16
	xor r10, rsi
	and r10, r14
	xor rsi, r10
	ror r10, 48
	xor rbx, r10
	mov r10, rdi
	shr r10, 16
	xor r10, r8
	and r10, r14
	xor r8, r10
	ror r10, 48
	xor rdi, r10
	mov r10, rbp
	shr r10, 16
	xor r10, r9
	and r10, r14
	xor r9, r10
	ror r10, 48
	xor rbp, r10
	mov r10, rax
	shr r10, 8
	xor r10, rbx
	and r10, r15
	xor rbx, r10
	ror r10, 56
	xor rax, r10
	mov r10, rdx
	shr r10, 8
	xor r10, rsi
	and r10, r15
	xor rsi, r10
	ror r10, 56
	xor rdx, r10
	mov r10, rdi
	shr r10, 8
	xor r10, rbp
	and r10, r15
	xor rbp, r10
	ror r10, 56
	xor rdi, r10
	mov r10, r8
	shr r10, 8
	xor r10, r9
	and r10, r15
	xor r9, r10
	ror r10, 56
	xor r8, r10
	mov QWORD PTR [rcx+104], rax
	mov QWORD PTR [rcx+168], rbx
	mov QWORD PTR [rcx+232], rdx
	mov QWORD PTR [rcx+296], rsi
	mov QWORD PTR [rcx+360], rdi
	mov QWORD PTR [rcx+424], rbp
	mov QWORD PTR [rcx+488], r8
	mov QWORD PTR [rcx+552], r9
	mov rax, QWORD PTR [rcx+112]
	mov rbx, QWORD PTR [rcx+176]
	mov rdx, QWORD PTR [rcx+240]
	mov rsi, QWORD PTR [rcx+304]
	mov rdi, QWORD PTR [rcx+368]
	mov rbp, QWORD PTR [rcx+432]
	mov r8, QWORD PTR [rcx+496]
	mov r9, QWORD PTR [rcx+560]
	mov r10, rax
	shr r10, 32
	xor r10, rdi
	and r10, r13
	xor rdi, r10
	ror r10, 32
	xor rax, r10
	mov r10, rbx
	shr r10, 32
	xor r10, rbp
	and r10, r13
	xor rbp, r10
	ror r10, 32
	xor rbx, r10
	mov r10, rdx
	shr r10, 32
	xor r10, r8
	and r10, r13
	xor r8, r10
	ror r10, 32
	xor rdx, r10
	mov r10, rsi
	shr r10, 32
	xor r10, r9
	and r10, r13
	xor r9, r10
	ror r10, 32
	xor rsi, r10
	mov r10, rax
	shr r10, 16
	xor r10, rdx
	and r10, r14
	xor rdx, r10
	ror r10, 48
	xor rax, r10
	mov r10, rbx
	shr r10, 16
	xor r10, rsi
	and r10, r14
	xor rsi, r10
	ror r10, 48
	xor rbx, r10
	mov r10, rdi
	shr r10, 16
	xor r10, r8
	and r10, r14
	xor r8, r10
	ror r10, 48
	xor rdi, r10
	mov r10, rbp
	shr r10, 16
	xor r10, r9
	and r10, r14
	xor r9, r10
	ror r10, 48
	xor rbp, r10
	mov r10, rax
	shr r10, 8
	xor r10, rbx
	and r10, r15
	xor rbx, r10
	ror r10, 56
	xor rax, r10
	mov r10, rdx
	shr r10, 8
	xor r10, rsi
	and r10, r15
	xor rsi, r10
	ror r10, 56
	xor rdx, r10
	mov r10, rdi
	shr r10, 8
	xor r10, rbp
	and r10, r15
	xor rbp, r10
	ror r10, 56
	xor rdi, r10
	mov r10, r8
	shr r10, 8
	xor r10, r9
	and r10, r15
	xor r9, r10
	ror r10, 56
	xor r8, r10
	mov QWORD PTR [rcx+112], rax
	mov QWORD PTR [rcx+176], rbx
	mov QWORD PTR [rcx+240], rdx
	mov QWORD PTR [rcx+304], rsi
	mov QWORD PTR [rcx+368], rdi
	mov QWORD PTR [rcx+432], rbp
	mov QWORD PTR [rcx+496], r8
	mov QWORD PTR [rcx+560], r9
	mov rax, QWORD PTR [rcx+120]
	mov rbx, QWORD PTR [rcx+184]
	mov rdx, QWORD PTR [rcx+248]
	mov rsi, QWORD PTR [rcx+312]
	mov rdi, QWORD PTR [rcx+376]
	mov rbp, QWORD PTR [rcx+440]
	mov r8, QWORD PTR [rcx+504]
	mov r9, QWORD PTR [rcx+568]
	mov r10, rax
	shr r10, 32
	xor r10, rdi
	and r10, r13
	xor rdi, r10
	ror r10, 32
	xor rax, r10
	mov r10, rbx
	shr r10, 32
	xor r10, rbp
	and r10, r13
	xor rbp, r10
	ror r10, 32
	xor rbx, r10
	mov r10, rdx
	shr r10, 32
	xor r10, r8
	and r10, r13
	xor r8, r10
	ror r10, 32
	xor rdx, r10
	mov r10, rsi
	shr r10, 32
	xor r10, r9
	and r10, r13
	xor r9, r10
	ror r10, 32
	xor rsi, r10
	mov r10, rax
	shr r10, 16
	xor r10, rdx
	and r10, r14
	xor rdx, r10
	ror r10, 48
	xor rax, r10
	mov r10, rbx
	shr r10, 16
	xor r10, rsi
	and r10, r14
	xor rsi, r10
	ror r10, 48
	xor rbx, r10
	mov r10, rdi
	shr r10, 16
	xor r10, r8
	and r10, r14
	xor r8, r10
	ror r10, 48
	xor rdi, r10
	mov r10, rbp
	shr r10, 16
	xor r10, r9
	and r10, r14
	xor r9, r10
	ror r10, 48
	xor rbp, r10
	mov r10, rax
	shr r10, 8
	xor r10, rbx
	and r10, r15
	xor rbx, r10
	ror r10, 56
	xor rax, r10
	mov r10, rdx
	shr r10, 8
	xor r10, rsi
	and r10, r15
	xor rsi, r10
	ror r10, 56
	xor rdx, r10
	mov r10, rdi
	shr r10, 8
	xor r10, rbp
	and r10, r15
	xor rbp, r10
	ror r10, 56
	xor rdi, r10
	mov r10, r8
	shr r10, 8
	xor r10, r9
	and r10, r15
	xor r9, r10
	ror r10, 56
	xor r8, r10
	mov QWORD PTR [rcx+120], rax
	mov QWORD PTR [rcx+184], rbx
	mov QWORD PTR [rcx+248], rdx
	mov QWORD PTR [rcx+312], rsi
	mov QWORD PTR [rcx+376], rdi
	mov QWORD PTR [rcx+440], rbp
	mov QWORD PTR [rcx+504], r8
	mov QWORD PTR [rcx+568], r9
	movabs r13, 1085102592571150095
	movabs r14, 3689348814741910323
	movabs r15, 6148914691236517205
	mov rax, QWORD PTR [rcx+64]
	mov rbx, QWORD PTR [rcx+72]
	mov rdx, QWORD PTR [rcx+80]
	mov rsi, QWORD PTR [rcx+88]
	mov rdi, QWORD PTR [rcx+96]
	mov rbp, QWORD PTR [rcx+104]
	mov r8, QWORD PTR [rcx+112]
	mov r9, QWORD PTR [rcx+120]
	mov r10, rax
	shr r10, 4
	xor r10, rdi
	and r10, r13
	xor rdi, r10
	ror r10, 60
	xor rax, r10
	mov r10, rbx
	shr r10, 4
	xor r10, rbp
	and r10, r13
	xor rbp, r10
	ror r10, 60
	xor rbx, r10
	mov r10, rdx
	shr r10, 4
	xor r10, r8
	and r10, r13
	xor r8, r10
	ror r10, 60
	xor rdx, r10
	mov r10, rsi
	shr r10, 4
	xor r10, r9
	and r10, r13
	xor r9, r10
	ror r10, 60
	xor rsi, r10
	mov r10, rax
	shr r10, 2
	xor r10, rdx
	and r10, r14
	xor rdx, r10
	ror r10, 62
	xor rax, r10
	mov r10, rbx
	shr r10, 2
	xor r10, rsi
	and r10, r14
	xor rsi, r10
	ror r10, 62
	xor rbx, r10
	mov r10, rdi
	shr r10, 2
	xor r10, r8
	and r10, r14
	xor r8, r10
	ror r10, 62
	xor rdi, r10
	mov r10, rbp
	shr r10, 2
	xor r10, r9
	and r10, r14
	xor r9, r10
	ror r10, 62
	xor rbp, r10
	mov r10, rax
	shr r10, 1
	xor r10, rbx
	and r10, r15
	xor rbx, r10
	ror r10, 63
	xor rax, r10
	mov r10, rdx
	shr r10, 1
	xor r10, rsi
	and r10, r15
	xor rsi, r10
	ror r10, 63
	xor rdx, r10
	mov r10, rdi
	shr r10, 1
	xor r10, rbp
	and r10, r15
	xor rbp, r10
	ror r10, 63
	xor rdi, r10
	mov r10, r8
	shr r10, 1
	xor r10, r9
	and r10, r15
	xor r9, r10
	ror r10, 63
	xor r8, r10
	mov QWORD PTR [rcx+64], rax
	mov QWORD PTR [rcx+72], rbx
	mov QWORD PTR [rcx+80], rdx
	mov QWORD PTR [rcx+88], rsi
	mov QWORD PTR [rcx+96], rdi
	mov QWORD PTR [rcx+104], rbp
	mov QWORD PTR [rcx+112], r8
	mov QWORD PTR [rcx+120], r9
	mov rax, QWORD PTR [rcx+128]
	mov rbx, QWORD PTR [rcx+136]
	mov rdx, QWORD PTR [rcx+144]
	mov rsi, QWORD PTR [rcx+152]
	mov rdi, QWORD PTR [rcx+160]
	mov rbp, QWORD PTR [rcx+168]
	mov r8, QWORD PTR [rcx+176]
	mov r9, QWORD PTR [rcx+184]
	mov r10, rax
	shr r10, 4
	xor r10, rdi
	and r10, r13
	xor rdi, r10
	ror r10, 60
	xor rax, r10
	mov r10, rbx
	shr r10, 4
	xor r10, rbp
	and r10, r13
	xor rbp, r10
	ror r10, 60
	xor rbx, r10
	mov r10, rdx
	shr r10, 4
	xor r10, r8
	and r10, r13
	xor r8, r10
	ror r10, 60
	xor rdx, r10
	mov r10, rsi
	shr r10, 4
	xor r10, r9
	and r10, r13
	xor r9, r10
	ror r10, 60
	xor rsi, r10
	mov r10, rax
	shr r10, 2
	xor r10, rdx
	and r10, r14
	xor rdx, r10
	ror r10, 62
	xor rax, r10
	mov r10, rbx
	shr r10, 2
	xor r10, rsi
	and r10, r14
	xor rsi, r10
	ror r10, 62
	xor rbx, r10
	mov r10, rdi
	shr r10, 2
	xor r10, r8
	and r10, r14
	xor r8, r10
	ror r10, 62
	xor rdi, r10
	mov r10, rbp
	shr r10, 2
	xor r10, r9
	and r10, r14
	xor r9, r10
	ror r10, 62
	xor rbp, r10
	mov r10, rax
	shr r10, 1
	xor r10, rbx
	and r10, r15
	xor rbx, r10
	ror r10, 63
	xor rax, r10
	mov r10, rdx
	shr r10, 1
	xor r10, rsi
	and r10, r15
	xor rsi, r10
	ror r10, 63
	xor rdx, r10
	mov r10, rdi
	shr r10, 1
	xor r10, rbp
	and r10, r15
	xor rbp, r10
	ror r10, 63
	xor rdi, r10
	mov r10, r8
	shr r10, 1
	xor r10, r9
	and r10, r15
	xor r9, r10
	ror r10, 63
	xor r8, r10
	mov QWORD PTR [rcx+128], rax
	mov QWORD PTR [rcx+136], rbx
	mov QWORD PTR [rcx+144], rdx
	mov QWORD PTR [rcx+152], rsi
	mov QWORD PTR [rcx+160], rdi
	mov QWORD PTR [rcx+168], rbp
	mov QWORD PTR [rcx+176], r8
	mov QWORD PTR [rcx+184], r9
	mov rax, QWORD PTR [rcx+192]
	mov rbx, QWORD PTR [rcx+200]
	mov rdx, QWORD PTR [rcx+208]
	mov rsi, QWORD PTR [rcx+216]
	mov rdi, QWORD PTR [rcx+224]
	mov rbp, QWORD PTR [rcx+232]
	mov r8, QWORD PTR [rcx+240]
	mov r9, QWORD PTR [rcx+248]
	mov r10, rax
	shr r10, 4
	xor r10, rdi
	and r10, r13
	xor rdi, r10
	ror r10, 60
	xor rax, r10
	mov r10, rbx
	shr r10, 4
	xor r10, rbp
	and r10, r13
	xor rbp, r10
	ror r10, 60
	xor rbx, r10
	mov r10, rdx
	shr r10, 4
	xor r10, r8
	and r10, r13
	xor r8, r10
	ror r10, 60
	xor rdx, r10
	mov r10, rsi
	shr r10, 4
	xor r10, r9
	and r10, r13
	xor r9, r10
	ror r10, 60
	xor rsi, r10
	mov r10, rax
	shr r10, 2
	xor r10, rdx
	and r10, r14
	xor rdx, r10
	ror r10, 62
	xor rax, r10
	mov r10, rbx
	shr r10, 2
	xor r10, rsi
	and r10, r14
	xor rsi, r10
	ror r10, 62
	xor rbx, r10
	mov r10, rdi
	shr r10, 2
	xor r10, r8
	and r10, r14
	xor r8, r10
	ror r10, 62
	xor rdi, r10
	mov r10, rbp
	shr r10, 2
	xor r10, r9
	and r10, r14
	xor r9, r10
	ror r10, 62
	xor rbp, r10
	mov r10, rax
	shr r10, 1
	xor r10, rbx
	and r10, r15
	xor rbx, r10
	ror r10, 63
	xor rax, r10
	mov r10, rdx
	shr r10, 1
	xor r10, rsi
	and r10, r15
	xor rsi, r10
	ror r10, 63
	xor rdx, r10
	mov r10, rdi
	shr r10, 1
	xor r10, rbp
	and r10, r15
	xor rbp, r10
	ror r10, 63
	xor rdi, r10
	mov r10, r8
	shr r10, 1
	xor r10, r9
	and r10, r15
	xor r9, r10
	ror r10, 63
	xor r8, r10
	mov QWORD PTR [rcx+192], rax
	mov QWORD PTR [rcx+200], rbx
	mov QWORD PTR [rcx+208], rdx
	mov QWORD PTR [rcx+216], rsi
	mov QWORD PTR [rcx+224], rdi
	mov QWORD PTR [rcx+232], rbp
	mov QWORD PTR [rcx+240], r8
	mov QWORD PTR [rcx+248], r9
	mov rax, QWORD PTR [rcx+256]
	mov rbx, QWORD PTR [rcx+264]
	mov rdx, QWORD PTR [rcx+272]
	mov rsi, QWORD PTR [rcx+280]
	mov rdi, QWORD PTR [rcx+288]
	mov rbp, QWORD PTR [rcx+296]
	mov r8, QWORD PTR [rcx+304]
	mov r9, QWORD PTR [rcx+312]
	mov r10, rax
	shr r10, 4
	xor r10, rdi
	and r10, r13
	xor rdi, r10
	ror r10, 60
	xor rax, r10
	mov r10, rbx
	shr r10, 4
	xor r10, rbp
	and r10, r13
	xor rbp, r10
	ror r10, 60
	xor rbx, r10
	mov r10, rdx
	shr r10, 4
	xor r10, r8
	and r10, r13
	xor r8, r10
	ror r10, 60
	xor rdx, r10
	mov r10, rsi
	shr r10, 4
	xor r10, r9
	and r10, r13
	xor r9, r10
	ror r10, 60
	xor rsi, r10
	mov r10, rax
	shr r10, 2
	xor r10, rdx
	and r10, r14
	xor rdx, r10
	ror r10, 62
	xor rax, r10
	mov r10, rbx
	shr r10, 2
	xor r10, rsi
	and r10, r14
	xor rsi, r10
	ror r10, 62
	xor rbx, r10
	mov r10, rdi
	shr r10, 2
	xor r10, r8
	and r10, r14
	xor r8, r10
	ror r10, 62
	xor rdi, r10
	mov r10, rbp
	shr r10, 2
	xor r10, r9
	and r10, r14
	xor r9, r10
	ror r10, 62
	xor rbp, r10
	mov r10, rax
	shr r10, 1
	xor r10, rbx
	and r10, r15
	xor rbx, r10
	ror r10, 63
	xor rax, r10
	mov r10, rdx
	shr r10, 1
	xor r10, rsi
	and r10, r15
	xor rsi, r10
	ror r10, 63
	xor rdx, r10
	mov r10, rdi
	shr r10, 1
	xor r10, rbp
	and r10, r15
	xor rbp, r10
	ror r10, 63
	xor rdi, r10
	mov r10, r8
	shr r10, 1
	xor r10, r9
	and r10, r15
	xor r9, r10
	ror r10, 63
	xor r8, r10
	mov QWORD PTR [rcx+256], rax
	mov QWORD PTR [rcx+264], rbx
	mov QWORD PTR [rcx+272], rdx
	mov QWORD PTR [rcx+280], rsi
	mov QWORD PTR [rcx+288], rdi
	mov QWORD PTR [rcx+296], rbp
	mov QWORD PTR [rcx+304], r8
	mov QWORD PTR [rcx+312], r9
	mov rax, QWORD PTR [rcx+320]
	mov rbx, QWORD PTR [rcx+328]
	mov rdx, QWORD PTR [rcx+336]
	mov rsi, QWORD PTR [rcx+344]
	mov rdi, QWORD PTR [rcx+352]
	mov rbp, QWORD PTR [rcx+360]
	mov r8, QWORD PTR [rcx+368]
	mov r9, QWORD PTR [rcx+376]
	mov r10, rax
	shr r10, 4
	xor r10, rdi
	and r10, r13
	xor rdi, r10
	ror r10, 60
	xor rax, r10
	mov r10, rbx
	shr r10, 4
	xor r10, rbp
	and r10, r13
	xor rbp, r10
	ror r10, 60
	xor rbx, r10
	mov r10, rdx
	shr r10, 4
	xor r10, r8
	and r10, r13
	xor r8, r10
	ror r10, 60
	xor rdx, r10
	mov r10, rsi
	shr r10, 4
	xor r10, r9
	and r10, r13
	xor r9, r10
	ror r10, 60
	xor rsi, r10
	mov r10, rax
	shr r10, 2
	xor r10, rdx
	and r10, r14
	xor rdx, r10
	ror r10, 62
	xor rax, r10
	mov r10, rbx
	shr r10, 2
	xor r10, rsi
	and r10, r14
	xor rsi, r10
	ror r10, 62
	xor rbx, r10
	mov r10, rdi
	shr r10, 2
	xor r10, r8
	and r10, r14
	xor r8, r10
	ror r10, 62
	xor rdi, r10
	mov r10, rbp
	shr r10, 2
	xor r10, r9
	and r10, r14
	xor r9, r10
	ror r10, 62
	xor rbp, r10
	mov r10, rax
	shr r10, 1
	xor r10, rbx
	and r10, r15
	xor rbx, r10
	ror r10, 63
	xor rax, r10
	mov r10, rdx
	shr r10, 1
	xor r10, rsi
	and r10, r15
	xor rsi, r10
	ror r10, 63
	xor rdx, r10
	mov r10, rdi
	shr r10, 1
	xor r10, rbp
	and r10, r15
	xor rbp, r10
	ror r10, 63
	xor rdi, r10
	mov r10, r8
	shr r10, 1
	xor r10, r9
	and r10, r15
	xor r9, r10
	ror r10, 63
	xor r8, r10
	mov QWORD PTR [rcx+320], rax
	mov QWORD PTR [rcx+328], rbx
	mov QWORD PTR [rcx+336], rdx
	mov QWORD PTR [rcx+344], rsi
	mov QWORD PTR [rcx+352], rdi
	mov QWORD PTR [rcx+360], rbp
	mov QWORD PTR [rcx+368], r8
	mov QWORD PTR [rcx+376], r9
	mov rax, QWORD PTR [rcx+384]
	mov rbx, QWORD PTR [rcx+392]
	mov rdx, QWORD PTR [rcx+400]
	mov rsi, QWORD PTR [rcx+408]
	mov rdi, QWORD PTR [rcx+416]
	mov rbp, QWORD PTR [rcx+424]
	mov r8, QWORD PTR [rcx+432]
	mov r9, QWORD PTR [rcx+440]
	mov r10, rax
	shr r10, 4
	xor r10, rdi
	and r10, r13
	xor rdi, r10
	ror r10, 60
	xor rax, r10
	mov r10, rbx
	shr r10, 4
	xor r10, rbp
	and r10, r13
	xor rbp, r10
	ror r10, 60
	xor rbx, r10
	mov r10, rdx
	shr r10, 4
	xor r10, r8
	and r10, r13
	xor r8, r10
	ror r10, 60
	xor rdx, r10
	mov r10, rsi
	shr r10, 4
	xor r10, r9
	and r10, r13
	xor r9, r10
	ror r10, 60
	xor rsi, r10
	mov r10, rax
	shr r10, 2
	xor r10, rdx
	and r10, r14
	xor rdx, r10
	ror r10, 62
	xor rax, r10
	mov r10, rbx
	shr r10, 2
	xor r10, rsi
	and r10, r14
	xor rsi, r10
	ror r10, 62
	xor rbx, r10
	mov r10, rdi
	shr r10, 2
	xor r10, r8
	and r10, r14
	xor r8, r10
	ror r10, 62
	xor rdi, r10
	mov r10, rbp
	shr r10, 2
	xor r10, r9
	and r10, r14
	xor r9, r10
	ror r10, 62
	xor rbp, r10
	mov r10, rax
	shr r10, 1
	xor r10, rbx
	and r10, r15
	xor rbx, r10
	ror r10, 63
	xor rax, r10
	mov r10, rdx
	shr r10, 1
	xor r10, rsi
	and r10, r15
	xor rsi, r10
	ror r10, 63
	xor rdx, r10
	mov r10, rdi
	shr r10, 1
	xor r10, rbp
	and r10, r15
	xor rbp, r10
	ror r10, 63
	xor rdi, r10
	mov r10, r8
	shr r10, 1
	xor r10, r9
	and r10, r15
	xor r9, r10
	ror r10, 63
	xor r8, r10
	mov QWORD PTR [rcx+384], rax
	mov QWORD PTR [rcx+392], rbx
	mov QWORD PTR [rcx+400], rdx
	mov QWORD PTR [rcx+408], rsi
	mov QWORD PTR [rcx+416], rdi
	mov QWORD PTR [rcx+424], rbp
	mov QWORD PTR [rcx+432], r8
	mov QWORD PTR [rcx+440], r9
	mov rax, QWORD PTR [rcx+448]
	mov rbx, QWORD PTR [rcx+456]
	mov rdx, QWORD PTR [rcx+464]
	mov rsi, QWORD PTR [rcx+472]
	mov rdi, QWORD PTR [rcx+480]
	mov rbp, QWORD PTR [rcx+488]
	mov r8, QWORD PTR [rcx+496]
	mov r9, QWORD PTR [rcx+504]
	mov r10, rax
	shr r10, 4
	xor r10, rdi
	and r10, r13
	xor rdi, r10
	ror r10, 60
	xor rax, r10
	mov r10, rbx
	shr r10, 4
	xor r10, rbp
	and r10, r13
	xor rbp, r10
	ror r10, 60
	xor rbx, r10
	mov r10, rdx
	shr r10, 4
	xor r10, r8
	and r10, r13
	xor r8, r10
	ror r10, 60
	xor rdx, r10
	mov r10, rsi
	shr r10, 4
	xor r10, r9
	and r10, r13
	xor r9, r10
	ror r10, 60
	xor rsi, r10
	mov r10, rax
	shr r10, 2
	xor r10, rdx
	and r10, r14
	xor rdx, r10
	ror r10, 62
	xor rax, r10
	mov r10, rbx
	shr r10, 2
	xor r10, rsi
	and r10, r14
	xor rsi, r10
	ror r10, 62
	xor rbx, r10
	mov r10, rdi
	shr r10, 2
	xor r10, r8
	and r10, r14
	xor r8, r10
	ror r10, 62
	xor rdi, r10
	mov r10, rbp
	shr r10, 2
	xor r10, r9
	and r10, r14
	xor r9, r10
	ror r10, 62
	xor rbp, r10
	mov r10, rax
	shr r10, 1
	xor r10, rbx
	and r10, r15
	xor rbx, r10
	ror r10, 63
	xor rax, r10
	mov r10, rdx
	shr r10, 1
	xor r10, rsi
	and r10, r15
	xor rsi, r10
	ror r10, 63
	xor rdx, r10
	mov r10, rdi
	shr r10, 1
	xor r10, rbp
	and r10, r15
	xor rbp, r10
	ror r10, 63
	xor rdi, r10
	mov r10, r8
	shr r10, 1
	xor r10, r9
	and r10, r15
	xor r9, r10
	ror r10, 63
	xor r8, r10
	mov QWORD PTR [rcx+448], rax
	mov QWORD PTR [rcx+456], rbx
	mov QWORD PTR [rcx+464], rdx
	mov QWORD PTR [rcx+472], rsi
	mov QWORD PTR [rcx+480], rdi
	mov QWORD PTR [rcx+488], rbp
	mov QWORD PTR [rcx+496], r8
	mov QWORD PTR [rcx+504], r9
	mov rax, QWORD PTR [rcx+512]
	mov rbx, QWORD PTR [rcx+520]
	mov rdx, QWORD PTR [rcx+528]
	mov rsi, QWORD PTR [rcx+536]
	mov rdi, QWORD PTR [rcx+544]
	mov rbp, QWORD PTR [rcx+552]
	mov r8, QWORD PTR [rcx+560]
	mov r9, QWORD PTR [rcx+568]
	mov r10, rax
	shr r10, 4
	xor r10, rdi
	and r10, r13
	xor rdi, r10
	ror r10, 60
	xor rax, r10
	mov r10, rbx
	shr r10, 4
	xor r10, rbp
	and r10, r13
	xor rbp, r10
	ror r10, 60
	xor rbx, r10
	mov r10, rdx
	shr r10, 4
	xor r10, r8
	and r10, r13
	xor r8, r10
	ror r10, 60
	xor rdx, r10
	mov r10, rsi
	shr r10, 4
	xor r10, r9
	and r10, r13
	xor r9, r10
	ror r10, 60
	xor rsi, r10
	mov r10, rax
	shr r10, 2
	xor r10, rdx
	and r10, r14
	xor rdx, r10
	ror r10, 62
	xor rax, r10
	mov r10, rbx
	shr r10, 2
	xor r10, rsi
	and r10, r14
	xor rsi, r10
	ror r10, 62
	xor rbx, r10
	mov r10, rdi
	shr r10, 2
	xor r10, r8
	and r10, r14
	xor r8, r10
	ror r10, 62
	xor rdi, r10
	mov r10, rbp
	shr r10, 2
	xor r10, r9
	and r10, r14
	xor r9, r10
	ror r10, 62
	xor rbp, r10
	mov r10, rax
	shr r10, 1
	xor r10, rbx
	and r10, r15
	xor rbx, r10
	ror r10, 63
	xor rax, r10
	mov r10, rdx
	shr r10, 1
	xor r10, rsi
	and r10, r15
	xor rsi, r10
	ror r10, 63
	xor rdx, r10
	mov r10, rdi
	shr r10, 1
	xor r10, rbp
	and r10, r15
	xor rbp, r10
	ror r10, 63
	xor rdi, r10
	mov r10, r8
	shr r10, 1
	xor r10, r9
	and r10, r15
	xor r9, r10
	ror r10, 63
	xor r8, r10
	mov QWORD PTR [rcx+512], rax
	mov QWORD PTR [rcx+520], rbx
	mov QWORD PTR [rcx+528], rdx
	mov QWORD PTR [rcx+536], rsi
	mov QWORD PTR [rcx+544], rdi
	mov QWORD PTR [rcx+552], rbp
	mov QWORD PTR [rcx+560], r8
	mov QWORD PTR [rcx+568], r9
	mov rax, 3
	mov QWORD PTR [rcx+680], rax
219:
	mov rax, QWORD PTR [rcx+680]
	cmp rax, 3
	je 220f
	cmp rax, 2
	je 222f
	mov rdx, QWORD PTR [rcx+624]
	add rdx, 120
	mov QWORD PTR [rcx+656], rdx
	mov rdx, -8
	mov QWORD PTR [rcx+664], rdx
	jmp 223f
222:
	mov rdx, QWORD PTR [rcx+624]
	add rdx, 128
	mov QWORD PTR [rcx+656], rdx
	mov rdx, 8
	mov QWORD PTR [rcx+664], rdx
223:
	jmp 221f
220:
	mov rdx, QWORD PTR [rcx+624]
	add rdx, 376
	mov QWORD PTR [rcx+656], rdx
	mov rdx, -8
	mov QWORD PTR [rcx+664], rdx
221:
	mov rax, 8
	mov QWORD PTR [rcx+672], rax
224:
	mov rax, QWORD PTR [rcx+656]
	mov r15, QWORD PTR [rax]
	mov rdx, QWORD PTR [rcx+664]
	add rax, rdx
	mov QWORD PTR [rcx+656], rax
	ror r15, 48
	add r15, r15
	sbb rbp, rbp
	xor rbp, QWORD PTR [rcx+72]
	add r15, r15
	sbb rdi, rdi
	xor rdi, QWORD PTR [rcx+568]
	add r15, r15
	sbb rsi, rsi
	xor rsi, QWORD PTR [rcx+504]
	add r15, r15
	sbb rdx, rdx
	xor rdx, QWORD PTR [rcx+440]
	add r15, r15
	sbb rbx, rbx
	xor rbx, QWORD PTR [rcx+376]
	add r15, r15
	sbb rax, rax
	xor rax, QWORD PTR [rcx+312]
	mov r8, rbx
	xor r8, -1
	and r8, rbp
	mov r9, rdx
	xor r9, r8
	mov r10, rsi
	or r10, rax
	mov r11, rbp
	xor r11, rsi
	mov r12, r10
	and r12, r11
	mov r13, rdx
	xor r13, r12
	mov r14, r9
	xor r14, -1
	and r14, r13
	mov QWORD PTR [rcx], rdi
	mov rdi, rbx
	xor rdi, rax
	mov QWORD PTR [rcx+8], r10
	mov r10, rsi
	xor r10, rdi
	xor r10, -1
	and r10, r9
	or r12, rax
	xor r10, r12
	mov r12, r14
	xor r12, -1
	and r12, r10
	or rax, rbp
	mov QWORD PTR [rcx+16], r12
	mov r12, r10
	or r12, rax
	xor r13, -1
	and r13, rbx
	mov QWORD PTR [rcx+24], rbx
	mov rbx, r12
	xor rbx, r13
	xor rax, -1
	and rax, rdx
	xor rax, r13
	xor r11, -1
	and r11, rdi
	or rax, r11
	xor r8, -1
	and r8, rsi
	mov rsi, r9
	xor rsi, r12
	xor r8, -1
	and r8, rsi
	mov rsi, r8
	xor rsi, -1
	and r10, QWORD PTR [rcx+8]
	xor rsi, r10
	or rbx, QWORD PTR [rcx]
	xor rbx, QWORD PTR [rcx]
	xor rbx, rsi
	xor r8, rdi
	or r13, r8
	xor r13, QWORD PTR [rcx+8]
	xor rbp, r13
	xor rsi, rbp
	or r14, QWORD PTR [rcx]
	xor r14, rsi
	xor r12, QWORD PTR [rcx+8]
	or r12, rax
	xor r12, rbp
	or rdi, rsi
	xor rdi, r12
	mov rsi, QWORD PTR [rcx+16]
	or rsi, QWORD PTR [rcx]
	xor rsi, rdi
	or r9, QWORD PTR [rcx+24]
	xor r12, -1
	and r12, r9
	and rbp, QWORD PTR [rcx+16]
	xor r12, rbp
	or r12, QWORD PTR [rcx]
	xor r12, rax
	mov rax, r12
	mov rdx, rsi
	mov rsi, r14
	xor rax, QWORD PTR [rcx+128]
	mov QWORD PTR [rcx+128], rax
	xor rbx, QWORD PTR [rcx+144]
	mov QWORD PTR [rcx+144], rbx
	xor rdx, QWORD PTR [rcx+528]
	mov QWORD PTR [rcx+528], rdx
	xor rsi, QWORD PTR [rcx+544]
	mov QWORD PTR [rcx+544], rsi
	add r15, r15
	sbb rbp, rbp
	xor rbp, QWORD PTR [rcx+376]
	add r15, r15
	sbb rdi, rdi
	xor rdi, QWORD PTR [rcx+312]
	add r15, r15
	sbb rsi, rsi
	xor rsi, QWORD PTR [rcx+248]
	add r15, r15
	sbb rdx, rdx
	xor rdx, QWORD PTR [rcx+184]
	add r15, r15
	sbb rbx, rbx
	xor rbx, QWORD PTR [rcx+120]
	add r15, r15
	sbb rax, rax
	xor rax, QWORD PTR [rcx+552]
	mov r8, rdi
	xor r8, rbx
	mov r9, rax
	xor r9, -1
	and r9, rbp
	xor r9, -1
	and r9, rbx
	mov r10, rdi
	or r10, r9
	mov r11, rax
	xor r11, -1
	and r11, r8
	mov r12, rbp
	and r12, r8
	xor rbx, r12
	mov r12, r11
	xor r12, -1
	and r12, rbx
	mov r13, rsi
	and r13, rax
	xor r9, r11
	and r9, r10
	mov r11, r13
	xor r11, -1
	and r11, r9
	mov r14, rsi
	and r14, r9
	xor rbp, -1
	xor rbp, r14
	xor rax, r8
	mov QWORD PTR [rcx], r12
	mov r12, r13
	xor r12, -1
	and r12, rax
	mov QWORD PTR [rcx+8], r8
	mov r8, rbp
	xor r8, r12
	xor r11, -1
	and r11, rdx
	xor r11, r8
	xor r12, -1
	and r12, rdi
	xor rbx, r12
	or rbp, rbx
	xor rbp, rbx
	xor rsi, rax
	xor rbp, rsi
	mov rdi, rdx
	xor rdi, -1
	and rdi, r10
	xor rdi, rbp
	xor r14, r12
	or rsi, r14
	xor r10, r8
	or r13, r10
	mov r14, rsi
	xor r14, r13
	xor r9, r8
	xor rbp, r9
	and r13, rbp
	and rsi, QWORD PTR [rcx+8]
	xor r13, rsi
	mov rsi, r13
	or rsi, rdx
	xor rsi, r14
	xor rbx, -1
	and rbx, r13
	or rax, r10
	xor rbx, rax
	or rdx, QWORD PTR [rcx]
	xor rdx, rbx
	mov rax, rdx
	mov rbx, rsi
	mov rdx, r11
	mov rsi, rdi
	xor rax, QWORD PTR [rcx+464]
	mov QWORD PTR [rcx+464], rax
	xor rbx, QWORD PTR [rcx+496]
	mov QWORD PTR [rcx+496], rbx
	xor rdx, QWORD PTR [rcx+320]
	mov QWORD PTR [rcx+320], rdx
	xor rsi, QWORD PTR [rcx+288]
	mov QWORD PTR [rcx+288], rsi
	add r15, r15
	sbb rbp, rbp
	xor rbp, QWORD PTR [rcx+120]
	add r15, r15
	sbb rdi, rdi
	xor rdi, QWORD PTR [rcx+552]
	add r15, r15
	sbb rsi, rsi
	xor rsi, QWORD PTR [rcx+488]
	add r15, r15
	sbb rdx, rdx
	xor rdx, QWORD PTR [rcx+424]
	add r15, r15
	sbb rbx, rbx
	xor rbx, QWORD PTR [rcx+360]
	add r15, r15
	sbb rax, rax
	xor rax, QWORD PTR [rcx+296]
	mov r8, rdi
	xor r8, -1
	and r8, rbp
	mov r9, rsi
	xor r9, rax
	mov r10, r8
	or r10, r9
	mov r11, rdx
	xor r11, rax
	mov r12, rbp
	xor r12, -1
	and r12, r11
	mov r13, r10
	xor r13, r12
	mov r14, rdi
	xor r14, r9
	mov QWORD PTR [rcx], r8
	mov r8, rax
	xor r8, -1
	and r8, r14
	xor r10, r8
	mov r8, r10
	xor r8, -1
	and r8, r13
	mov QWORD PTR [rcx+8], r8
	mov r8, rax
	and r8, r13
	or r8, rdx
	and r8, rbp
	xor r8, r14
	mov QWORD PTR [rcx+16], r14
	mov r14, rbx
	xor r14, -1
	and r14, r13
	xor r14, r8
	and r9, r11
	mov r11, rbp
	xor r11, rdx
	mov QWORD PTR [rcx+24], r14
	mov r14, r10
	xor r14, r11
	or r14, rsi
	xor r9, -1
	and r9, r14
	or r12, r11
	mov r11, r12
	xor r11, -1
	and r11, r8
	and rax, rdx
	mov r14, rdi
	xor r14, -1
	and r14, rax
	xor r11, r14
	and r10, r11
	or rax, QWORD PTR [rcx+16]
	xor r10, -1
	and r10, rax
	xor rbp, r10
	and r9, rbx
	xor r9, rbp
	xor r13, -1
	or rdi, r13
	or rsi, rdi
	xor rsi, QWORD PTR [rcx+16]
	xor r12, rsi
	mov rdi, QWORD PTR [rcx+8]
	xor rdi, -1
	and rdi, rbx
	xor rdi, r12
	and rdx, r13
	xor r8, rdx
	or rsi, r8
	xor rbp, QWORD PTR [rcx]
	xor rsi, rbp
	or r11, rbx
	xor r11, rsi
	mov rax, QWORD PTR [rcx+24]
	mov rbx, r11
	mov rdx, r9
	mov rsi, rdi
	xor rax, QWORD PTR [rcx+240]
	mov QWORD PTR [rcx+240], rax
	xor rbx, QWORD PTR [rcx+192]
	mov QWORD PTR [rcx+192], rbx
	xor rdx, QWORD PTR [rcx+96]
	mov QWORD PTR [rcx+96], rdx
	xor rsi, QWORD PTR [rcx+80]
	mov QWORD PTR [rcx+80], rsi
	add r15, r15
	sbb rbp, rbp
	xor rbp, QWORD PTR [rcx+360]
	add r15, r15
	sbb rdi, rdi
	xor rdi, QWORD PTR [rcx+296]
	add r15, r15
	sbb rsi, rsi
	xor rsi, QWORD PTR [rcx+232]
	add r15, r15
	sbb rdx, rdx
	xor rdx, QWORD PTR [rcx+168]
	add r15, r15
	sbb rbx, rbx
	xor rbx, QWORD PTR [rcx+104]
	add r15, r15
	sbb rax, rax
	xor rax, QWORD PTR [rcx+536]
	xor rbp, rsi
	xor rsi, rbx
	mov r8, rdi
	or r8, rdx
	xor r8, rbx
	xor r8, -1
	and r8, rsi
	mov r9, rdi
	xor r9, -1
	and r9, rsi
	mov r10, rdx
	xor r10, r9
	mov r11, rbp
	or r11, r10
	or r11, r8
	xor r11, r8
	mov r12, rdi
	xor r12, r11
	and r10, r12
	or rsi, r10
	xor rsi, r10
	xor rbp, r12
	xor rsi, -1
	and rsi, rbp
	xor r8, rsi
	xor rdi, rdx
	or rbx, r9
	xor rbp, rbx
	mov rbx, rdi
	xor rbx, -1
	and rbx, rbp
	xor r11, rbx
	mov rbx, r8
	xor rbx, -1
	and rbx, rax
	xor rbx, r11
	xor r11, -1
	mov r9, rax
	xor r9, -1
	and r9, r8
	xor r9, r11
	xor r8, r11
	xor rdi, -1
	and rdi, r8
	or r10, rdi
	xor rbp, r10
	mov r10, r12
	or r10, rax
	xor r10, rbp
	and rax, r12
	xor rax, rbp
	mov QWORD PTR [rcx], rbx
	mov rbx, r10
	mov rdx, r9
	mov rsi, QWORD PTR [rcx]
	xor rax, QWORD PTR [rcx+560]
	mov QWORD PTR [rcx+560], rax
	xor rbx, QWORD PTR [rcx+480]
	mov QWORD PTR [rcx+480], rbx
	xor rdx, QWORD PTR [rcx+336]
	mov QWORD PTR [rcx+336], rdx
	xor rsi, QWORD PTR [rcx+448]
	mov QWORD PTR [rcx+448], rsi
	add r15, r15
	sbb rbp, rbp
	xor rbp, QWORD PTR [rcx+104]
	add r15, r15
	sbb rdi, rdi
	xor rdi, QWORD PTR [rcx+536]
	add r15, r15
	sbb rsi, rsi
	xor rsi, QWORD PTR [rcx+472]
	add r15, r15
	sbb rdx, rdx
	xor rdx, QWORD PTR [rcx+408]
	add r15, r15
	sbb rbx, rbx
	xor rbx, QWORD PTR [rcx+344]
	add r15, r15
	sbb rax, rax
	xor rax, QWORD PTR [rcx+280]
	mov r8, rbp
	or r8, rsi
	mov r9, rax
	xor r9, -1
	and r9, r8
	mov r10, rbp
	xor r10, r9
	mov r11, rsi
	xor r11, r10
	mov r12, rdx
	or r12, r11
	or r9, rdx
	xor r9, rdx
	xor rsi, r9
	mov r9, rbx
	and r9, rsi
	or r11, rbp
	xor r9, r11
	xor r9, rdx
	xor rax, r9
	mov r13, r10
	or r13, rax
	mov r14, rbx
	and r14, r13
	mov QWORD PTR [rcx], r8
	mov r8, r10
	xor r8, r14
	mov QWORD PTR [rcx+8], r10
	mov r10, rdx
	and r10, r11
	xor r8, r10
	or r13, rbp
	xor r13, rbp
	mov r10, rsi
	xor r10, r13
	xor rbx, r12
	xor r10, -1
	and r10, rbx
	xor r10, -1
	or r10, rdi
	xor r10, rdi
	xor r10, r9
	mov r9, r14
	xor r9, -1
	and r9, rsi
	xor r13, rbx
	or r13, r8
	xor r9, -1
	and r9, r13
	mov r13, r9
	xor r13, -1
	and r13, r12
	and rax, r9
	xor rbx, rax
	and r11, rsi
	or r11, rbx
	xor r14, r11
	and r14, rdi
	xor r14, r8
	xor rbp, QWORD PTR [rcx]
	xor r9, rbp
	and rdx, rbx
	xor r9, rdx
	or r13, rdi
	xor r13, r9
	xor rsi, r12
	xor r9, -1
	and r9, rsi
	xor rbx, QWORD PTR [rcx+8]
	xor r9, rbx
	and r12, rdi
	xor r12, r9
	mov rax, r14
	mov rbx, r10
	mov rdx, r12
	mov rsi, r13
	xor rax, QWORD PTR [rcx+432]
	mov QWORD PTR [rcx+432], rax
	xor rbx, QWORD PTR [rcx+512]
	mov QWORD PTR [rcx+512], rbx
	xor rdx, QWORD PTR [rcx+224]
	mov QWORD PTR [rcx+224], rdx
	xor rsi, QWORD PTR [rcx+112]
	mov QWORD PTR [rcx+112], rsi
	add r15, r15
	sbb rbp, rbp
	xor rbp, QWORD PTR [rcx+344]
	add r15, r15
	sbb rdi, rdi
	xor rdi, QWORD PTR [rcx+280]
	add r15, r15
	sbb rsi, rsi
	xor rsi, QWORD PTR [rcx+216]
	add r15, r15
	sbb rdx, rdx
	xor rdx, QWORD PTR [rcx+152]
	add r15, r15
	sbb rbx, rbx
	xor rbx, QWORD PTR [rcx+88]
	add r15, r15
	sbb rax, rax
	xor rax, QWORD PTR [rcx+520]
	mov r8, rdi
	xor r8, rbx
	mov r9, rdi
	or r9, rax
	and r9, rbp
	xor r8, r9
	mov r10, rax
	xor r10, r8
	mov r11, r10
	xor r11, -1
	and r11, rbx
	and r10, rbp
	mov r12, rdi
	xor r12, r10
	mov r13, rbp
	xor r13, rsi
	mov r14, r12
	or r14, r13
	mov QWORD PTR [rcx], r10
	mov r10, r8
	xor r10, r14
	mov QWORD PTR [rcx+8], r8
	mov r8, rsi
	and r8, r10
	mov QWORD PTR [rcx+16], rbp
	mov rbp, rax
	xor rbp, -1
	and rbp, r8
	or r12, r11
	mov QWORD PTR [rcx+24], r11
	mov r11, rbp
	xor r11, r12
	mov QWORD PTR [rcx+32], rbp
	mov rbp, r11
	and rbp, rdx
	xor rbp, r10
	xor r14, rdi
	mov QWORD PTR [rcx+40], rbp
	mov rbp, r14
	xor rbp, -1
	and rbp, rax
	xor rsi, rbp
	mov rbp, r8
	xor rbp, -1
	and rbp, rbx
	or rbp, rsi
	or rdi, r13
	xor r11, rdi
	or r9, rbp
	xor r11, r9
	or r10, QWORD PTR [rcx+16]
	and r12, r10
	xor r12, rsi
	mov r10, QWORD PTR [rcx+32]
	xor r10, -1
	and r10, r12
	mov r9, QWORD PTR [rcx+24]
	or r9, rdx
	xor r9, r10
	xor r12, QWORD PTR [rcx+8]
	xor r12, -1
	and r12, rbx
	xor rdi, -1
	xor r14, rdi
	xor r12, r14
	or r12, rdx
	xor r12, rdx
	xor r12, r11
	xor rax, QWORD PTR [rcx]
	xor rsi, QWORD PTR [rcx+16]
	and rax, rsi
	xor r8, r14
	xor rax, r8
	xor rdx, -1
	and rdx, rbp
	xor rdx, rax
	mov rax, QWORD PTR [rcx+40]
	mov rbx, r9
	mov QWORD PTR [rcx+16], rdx
	mov rdx, r12
	mov rsi, QWORD PTR [rcx+16]
	xor rax, QWORD PTR [rcx+400]
	mov QWORD PTR [rcx+400], rax
	xor rbx, QWORD PTR [rcx+416]
	mov QWORD PTR [rcx+416], rbx
	xor rdx, QWORD PTR [rcx+256]
	mov QWORD PTR [rcx+256], rdx
	xor rsi, QWORD PTR [rcx+368]
	mov QWORD PTR [rcx+368], rsi
	add r15, r15
	sbb rbp, rbp
	xor rbp, QWORD PTR [rcx+88]
	add r15, r15
	sbb rdi, rdi
	xor rdi, QWORD PTR [rcx+520]
	add r15, r15
	sbb rsi, rsi
	xor rsi, QWORD PTR [rcx+456]
	add r15, r15
	sbb rdx, rdx
	xor rdx, QWORD PTR [rcx+392]
	add r15, r15
	sbb rbx, rbx
	xor rbx, QWORD PTR [rcx+328]
	add r15, r15
	sbb rax, rax
	xor rax, QWORD PTR [rcx+264]
	mov r8, rdx
	xor r8, rbx
	mov r9, rsi
	xor r9, r8
	mov r10, rax
	and r10, r9
	mov r11, rdx
	and r11, r8
	mov r12, rdi
	xor r12, r11
	mov r13, r10
	and r13, r12
	mov r14, rax
	and r14, r11
	mov QWORD PTR [rcx], r11
	mov r11, rsi
	xor r11, r14
	mov QWORD PTR [rcx+8], rsi
	mov rsi, r12
	or rsi, r11
	xor r8, rax
	mov QWORD PTR [rcx+16], rax
	mov rax, rsi
	xor rax, r8
	mov QWORD PTR [rcx+24], rsi
	mov rsi, r13
	xor rsi, -1
	and rsi, rbp
	xor rsi, rax
	xor r9, -1
	and r9, rbx
	mov rax, r12
	or rax, r9
	xor r11, r10
	xor rax, r11
	xor r10, r8
	or rdx, r10
	xor rdx, r10
	mov r8, rdx
	xor r8, -1
	and r8, r12
	xor rbx, r11
	xor r8, rbx
	xor r14, -1
	and r14, r10
	or rdx, r14
	mov r10, rdi
	xor r10, QWORD PTR [rcx+24]
	and r10, r8
	xor r10, rdx
	mov rbx, r10
	and rbx, rbp
	xor rbx, r8
	or r12, QWORD PTR [rcx+8]
	xor r12, QWORD PTR [rcx+8]
	or r14, r12
	or r8, QWORD PTR [rcx]
	and r14, r8
	xor r10, r14
	xor r9, rdx
	and r9, QWORD PTR [rcx+16]
	or r13, r9
	xor r14, r13
	mov r9, rbp
	xor r9, -1
	and r9, r14
	xor r9, rax
	and rdi, r13
	xor rax, -1
	xor rdi, rax
	xor r14, rdi
	or r10, rbp
	xor r10, r14
	mov rax, rsi
	mov rdx, r10
	mov rsi, r9
	xor rax, QWORD PTR [rcx+176]
	mov QWORD PTR [rcx+176], rax
	xor rbx, QWORD PTR [rcx+208]
	mov QWORD PTR [rcx+208], rbx
	xor rdx, QWORD PTR [rcx+352]
	mov QWORD PTR [rcx+352], rdx
	xor rsi, QWORD PTR [rcx+64]
	mov QWORD PTR [rcx+64], rsi
	add r15, r15
	sbb rbp, rbp
	xor rbp, QWORD PTR [rcx+328]
	add r15, r15
	sbb rdi, rdi
	xor rdi, QWORD PTR [rcx+264]
	add r15, r15
	sbb rsi, rsi
	xor rsi, QWORD PTR [rcx+200]
	add r15, r15
	sbb rdx, rdx
	xor rdx, QWORD PTR [rcx+136]
	add r15, r15
	sbb rbx, rbx
	xor rbx, QWORD PTR [rcx+72]
	add r15, r15
	sbb rax, rax
	xor rax, QWORD PTR [rcx+568]
	mov r8, rdi
	xor r8, -1
	and r8, rsi
	mov r9, rsi
	xor r9, -1
	and r9, rbx
	xor r9, rdx
	mov r10, rbp
	and r10, r9
	mov r11, r8
	xor r11, -1
	and r11, r10
	mov r12, r9
	xor r12, -1
	and r12, rdi
	mov r13, rbp
	or r13, r12
	mov r14, rsi
	xor r14, -1
	and r14, rdi
	xor r14, rbx
	mov QWORD PTR [rcx], rdx
	mov rdx, r13
	and rdx, r14
	or r10, rdx
	xor r9, -1
	xor rdx, r9
	xor r13, -1
	and r13, rsi
	xor rdx, r13
	xor r8, rdx
	mov r13, r11
	or r13, rax
	xor r13, r8
	xor r8, rbp
	mov rsi, rbx
	and rsi, r8
	xor rdx, rdi
	xor rsi, rdx
	xor r12, rsi
	xor rsi, r10
	or rdi, rsi
	xor rbx, r8
	xor rdi, rbx
	and r10, rax
	xor r10, rdi
	xor r14, r12
	or rdx, QWORD PTR [rcx]
	xor rdx, r14
	xor rbp, rdx
	and rbp, rax
	xor rbp, r12
	or r14, QWORD PTR [rcx]
	xor r14, QWORD PTR [rcx]
	and rdi, r14
	xor r11, rdx
	xor rdi, r11
	or rdi, rax
	xor rdi, r12
	mov rax, rbp
	mov rbx, r10
	mov rdx, r13
	mov rsi, rdi
	xor rax, QWORD PTR [rcx+272]
	mov QWORD PTR [rcx+272], rax
	xor rbx, QWORD PTR [rcx+160]
	mov QWORD PTR [rcx+160], rbx
	xor rdx, QWORD PTR [rcx+384]
	mov QWORD PTR [rcx+384], rdx
	xor rsi, QWORD PTR [rcx+304]
	mov QWORD PTR [rcx+304], rsi
	mov rax, QWORD PTR [rcx+656]
	mov r15, QWORD PTR [rax]
	mov rdx, QWORD PTR [rcx+664]
	add rax, rdx
	mov QWORD PTR [rcx+656], rax
	ror r15, 48
	add r15, r15
	sbb rbp, rbp
	xor rbp, QWORD PTR [rcx+64]
	add r15, r15
	sbb rdi, rdi
	xor rdi, QWORD PTR [rcx+560]
	add r15, r15
	sbb rsi, rsi
	xor rsi, QWORD PTR [rcx+496]
	add r15, r15
	sbb rdx, rdx
	xor rdx, QWORD PTR [rcx+432]
	add r15, r15
	sbb rbx, rbx
	xor rbx, QWORD PTR [rcx+368]
	add r15, r15
	sbb rax, rax
	xor rax, QWORD PTR [rcx+304]
	mov r8, rbx
	xor r8, -1
	and r8, rbp
	mov r9, rdx
	xor r9, r8
	mov r10, rsi
	or r10, rax
	mov r11, rbp
	xor r11, rsi
	mov r12, r10
	and r12, r11
	mov r13, rdx
	xor r13, r12
	mov r14, r9
	xor r14, -1
	and r14, r13
	mov QWORD PTR [rcx], rdi
	mov rdi, rbx
	xor rdi, rax
	mov QWORD PTR [rcx+8], r10
	mov r10, rsi
	xor r10, rdi
	xor r10, -1
	and r10, r9
	or r12, rax
	xor r10, r12
	mov r12, r14
	xor r12, -1
	and r12, r10
	or rax, rbp
	mov QWORD PTR [rcx+16], r12
	mov r12, r10
	or r12, rax
	xor r13, -1
	and r13, rbx
	mov QWORD PTR [rcx+24], rbx
	mov rbx, r12
	xor rbx, r13
	xor rax, -1
	and rax, rdx
	xor rax, r13
	xor r11, -1
	and r11, rdi
	or rax, r11
	xor r8, -1
	and r8, rsi
	mov rsi, r9
	xor rsi, r12
	xor r8, -1
	and r8, rsi
	mov rsi, r8
	xor rsi, -1
	and r10, QWORD PTR [rcx+8]
	xor rsi, r10
	or rbx, QWORD PTR [rcx]
	xor rbx, QWORD PTR [rcx]
	xor rbx, rsi
	xor r8, rdi
	or r13, r8
	xor r13, QWORD PTR [rcx+8]
	xor rbp, r13
	xor rsi, rbp
	or r14, QWORD PTR [rcx]
	xor r14, rsi
	xor r12, QWORD PTR [rcx+8]
	or r12, rax
	xor r12, rbp
	or rdi, rsi
	xor rdi, r12
	mov rsi, QWORD PTR [rcx+16]
	or rsi, QWORD PTR [rcx]
	xor rsi, rdi
	or r9, QWORD PTR [rcx+24]
	xor r12, -1
	and r12, r9
	and rbp, QWORD PTR [rcx+16]
	xor r12, rbp
	or r12, QWORD PTR [rcx]
	xor r12, rax
	mov rax, r12
	mov rdx, rsi
	mov rsi, r14
	xor rax, QWORD PTR [rcx+136]
	mov QWORD PTR [rcx+136], rax
	xor rbx, QWORD PTR [rcx+152]
	mov QWORD PTR [rcx+152], rbx
	xor rdx, QWORD PTR [rcx+536]
	mov QWORD PTR [rcx+536], rdx
	xor rsi, QWORD PTR [rcx+552]
	mov QWORD PTR [rcx+552], rsi
	add r15, r15
	sbb rbp, rbp
	xor rbp, QWORD PTR [rcx+368]
	add r15, r15
	sbb rdi, rdi
	xor rdi, QWORD PTR [rcx+304]
	add r15, r15
	sbb rsi, rsi
	xor rsi, QWORD PTR [rcx+240]
	add r15, r15
	sbb rdx, rdx
	xor rdx, QWORD PTR [rcx+176]
	add r15, r15
	sbb rbx, rbx
	xor rbx, QWORD PTR [rcx+112]
	add r15, r15
	sbb rax, rax
	xor rax, QWORD PTR [rcx+544]
	mov r8, rdi
	xor r8, rbx
	mov r9, rax
	xor r9, -1
	and r9, rbp
	xor r9, -1
	and r9, rbx
	mov r10, rdi
	or r10, r9
	mov r11, rax
	xor r11, -1
	and r11, r8
	mov r12, rbp
	and r12, r8
	xor rbx, r12
	mov r12, r11
	xor r12, -1
	and r12, rbx
	mov r13, rsi
	and r13, rax
	xor r9, r11
	and r9, r10
	mov r11, r13
	xor r11, -1
	and r11, r9
	mov r14, rsi
	and r14, r9
	xor rbp, -1
	xor rbp, r14
	xor rax, r8
	mov QWORD PTR [rcx], r12
	mov r12, r13
	xor r12, -1
	and r12, rax
	mov QWORD PTR [rcx+8], r8
	mov r8, rbp
	xor r8, r12
	xor r11, -1
	and r11, rdx
	xor r11, r8
	xor r12, -1
	and r12, rdi
	xor rbx, r12
	or rbp, rbx
	xor rbp, rbx
	xor rsi, rax
	xor rbp, rsi
	mov rdi, rdx
	xor rdi, -1
	and rdi, r10
	xor rdi, rbp
	xor r14, r12
	or rsi, r14
	xor r10, r8
	or r13, r10
	mov r14, rsi
	xor r14, r13
	xor r9, r8
	xor rbp, r9
	and r13, rbp
	and rsi, QWORD PTR [rcx+8]
	xor r13, rsi
	mov rsi, r13
	or rsi, rdx
	xor rsi, r14
	xor rbx, -1
	and rbx, r13
	or rax, r10
	xor rbx, rax
	or rdx, QWORD PTR [rcx]
	xor rdx, rbx
	mov rax, rdx
	mov rbx, rsi
	mov rdx, r11
	mov rsi, rdi
	xor rax, QWORD PTR [rcx+472]
	mov QWORD PTR [rcx+472], rax
	xor rbx, QWORD PTR [rcx+504]
	mov QWORD PTR [rcx+504], rbx
	xor rdx, QWORD PTR [rcx+328]
	mov QWORD PTR [rcx+328], rdx
	xor rsi, QWORD PTR [rcx+296]
	mov QWORD PTR [rcx+296], rsi
	add r15, r15
	sbb rbp, rbp
	xor rbp, QWORD PTR [rcx+112]
	add r15, r15
	sbb rdi, rdi
	xor rdi, QWORD PTR [rcx+544]
	add r15, r15
	sbb rsi, rsi
	xor rsi, QWORD PTR [rcx+480]
	add r15, r15
	sbb rdx, rdx
	xor rdx, QWORD PTR [rcx+416]
	add r15, r15
	sbb rbx, rbx
	xor rbx, QWORD PTR [rcx+352]
	add r15, r15
	sbb rax, rax
	xor rax, QWORD PTR [rcx+288]
	mov r8, rdi
	xor r8, -1
	and r8, rbp
	mov r9, rsi
	xor r9, rax
	mov r10, r8
	or r10, r9
	mov r11, rdx
	xor r11, rax
	mov r12, rbp
	xor r12, -1
	and r12, r11
	mov r13, r10
	xor r13, r12
	mov r14, rdi
	xor r14, r9
	mov QWORD PTR [rcx], r8
	mov r8, rax
	xor r8, -1
	and r8, r14
	xor r10, r8
	mov r8, r10
	xor r8, -1
	and r8, r13
	mov QWORD PTR [rcx+8], r8
	mov r8, rax
	and r8, r13
	or r8, rdx
	and r8, rbp
	xor r8, r14
	mov QWORD PTR [rcx+16], r14
	mov r14, rbx
	xor r14, -1
	and r14, r13
	xor r14, r8
	and r9, r11
	mov r11, rbp
	xor r11, rdx
	mov QWORD PTR [rcx+24], r14
	mov r14, r10
	xor r14, r11
	or r14, rsi
	xor r9, -1
	and r9, r14
	or r12, r11
	mov r11, r12
	xor r11, -1
	and r11, r8
	and rax, rdx
	mov r14, rdi
	xor r14, -1
	and r14, rax
	xor r11, r14
	and r10, r11
	or rax, QWORD PTR [rcx+16]
	xor r10, -1
	and r10, rax
	xor rbp, r10
	and r9, rbx
	xor r9, rbp
	xor r13, -1
	or rdi, r13
	or rsi, rdi
	xor rsi, QWORD PTR [rcx+16]
	xor r12, rsi
	mov rdi, QWORD PTR [rcx+8]
	xor rdi, -1
	and rdi, rbx
	xor rdi, r12
	and rdx, r13
	xor r8, rdx
	or rsi, r8
	xor rbp, QWORD PTR [rcx]
	xor rsi, rbp
	or r11, rbx
	xor r11, rsi
	mov rax, QWORD PTR [rcx+24]
	mov rbx, r11
	mov rdx, r9
	mov rsi, rdi
	xor rax, QWORD PTR [rcx+248]
	mov QWORD PTR [rcx+248], rax
	xor rbx, QWORD PTR [rcx+200]
	mov QWORD PTR [rcx+200], rbx
	xor rdx, QWORD PTR [rcx+104]
	mov QWORD PTR [rcx+104], rdx
	xor rsi, QWORD PTR [rcx+88]
	mov QWORD PTR [rcx+88], rsi
	add r15, r15
	sbb rbp, rbp
	xor rbp, QWORD PTR [rcx+352]
	add r15, r15
	sbb rdi, rdi
	xor rdi, QWORD PTR [rcx+288]
	add r15, r15
	sbb rsi, rsi
	xor rsi, QWORD PTR [rcx+224]
	add r15, r15
	sbb rdx, rdx
	xor rdx, QWORD PTR [rcx+160]
	add r15, r15
	sbb rbx, rbx
	xor rbx, QWORD PTR [rcx+96]
	add r15, r15
	sbb rax, rax
	xor rax, QWORD PTR [rcx+528]
	xor rbp, rsi
	xor rsi, rbx
	mov r8, rdi
	or r8, rdx
	xor r8, rbx
	xor r8, -1
	and r8, rsi
	mov r9, rdi
	xor r9, -1
	and r9, rsi
	mov r10, rdx
	xor r10, r9
	mov r11, rbp
	or r11, r10
	or r11, r8
	xor r11, r8
	mov r12, rdi
	xor r12, r11
	and r10, r12
	or rsi, r10
	xor rsi, r10
	xor rbp, r12
	xor rsi, -1
	and rsi, rbp
	xor r8, rsi
	xor rdi, rdx
	or rbx, r9
	xor rbp, rbx
	mov rbx, rdi
	xor rbx, -1
	and rbx, rbp
	xor r11, rbx
	mov rbx, r8
	xor rbx, -1
	and rbx, rax
	xor rbx, r11
	xor r11, -1
	mov r9, rax
	xor r9, -1
	and r9, r8
	xor r9, r11
	xor r8, r11
	xor rdi, -1
	and rdi, r8
	or r10, rdi
	xor rbp, r10
	mov r10, r12
	or r10, rax
	xor r10, rbp
	and rax, r12
	xor rax, rbp
	mov QWORD PTR [rcx], rbx
	mov rbx, r10
	mov rdx, r9
	mov rsi, QWORD PTR [rcx]
	xor rax, QWORD PTR [rcx+568]
	mov QWORD PTR [rcx+568], rax
	xor rbx, QWORD PTR [rcx+488]
	mov QWORD PTR [rcx+488], rbx
	xor rdx, QWORD PTR [rcx+344]
	mov QWORD PTR [rcx+344], rdx
	xor rsi, QWORD PTR [rcx+456]
	mov QWORD PTR [rcx+456], rsi
	add r15, r15
	sbb rbp, rbp
	xor rbp, QWORD PTR [rcx+96]
	add r15, r15
	sbb rdi, rdi
	xor rdi, QWORD PTR [rcx+528]
	add r15, r15
	sbb rsi, rsi
	xor rsi, QWORD PTR [rcx+464]
	add r15, r15
	sbb rdx, rdx
	xor rdx, QWORD PTR [rcx+400]
	add r15, r15
	sbb rbx, rbx
	xor rbx, QWORD PTR [rcx+336]
	add r15, r15
	sbb rax, rax
	xor rax, QWORD PTR [rcx+272]
	mov r8, rbp
	or r8, rsi
	mov r9, rax
	xor r9, -1
	and r9, r8
	mov r10, rbp
	xor r10, r9
	mov r11, rsi
	xor r11, r10
	mov r12, rdx
	or r12, r11
	or r9, rdx
	xor r9, rdx
	xor rsi, r9
	mov r9, rbx
	and r9, rsi
	or r11, rbp
	xor r9, r11
	xor r9, rdx
	xor rax, r9
	mov r13, r10
	or r13, rax
	mov r14, rbx
	and r14, r13
	mov QWORD PTR [rcx], r8
	mov r8, r10
	xor r8, r14
	mov QWORD PTR [rcx+8], r10
	mov r10, rdx
	and r10, r11
	xor r8, r10
	or r13, rbp
	xor r13, rbp
	mov r10, rsi
	xor r10, r13
	xor rbx, r12
	xor r10, -1
	and r10, rbx
	xor r10, -1
	or r10, rdi
	xor r10, rdi
	xor r10, r9
	mov r9, r14
	xor r9, -1
	and r9, rsi
	xor r13, rbx
	or r13, r8
	xor r9, -1
	and r9, r13
	mov r13, r9
	xor r13, -1
	and r13, r12
	and rax, r9
	xor rbx, rax
	and r11, rsi
	or r11, rbx
	xor r14, r11
	and r14, rdi
	xor r14, r8
	xor rbp, QWORD PTR [rcx]
	xor r9, rbp
	and rdx, rbx
	xor r9, rdx
	or r13, rdi
	xor r13, r9
	xor rsi, r12
	xor r9, -1
	and r9, rsi
	xor rbx, QWORD PTR [rcx+8]
	xor r9, rbx
	and r12, rdi
	xor r12, r9
	mov rax, r14
	mov rbx, r10
	mov rdx, r12
	mov rsi, r13
	xor rax, QWORD PTR [rcx+440]
	mov QWORD PTR [rcx+440], rax
	xor rbx, QWORD PTR [rcx+520]
	mov QWORD PTR [rcx+520], rbx
	xor rdx, QWORD PTR [rcx+232]
	mov QWORD PTR [rcx+232], rdx
	xor rsi, QWORD PTR [rcx+120]
	mov QWORD PTR [rcx+120], rsi
	add r15, r15
	sbb rbp, rbp
	xor rbp, QWORD PTR [rcx+336]
	add r15, r15
	sbb rdi, rdi
	xor rdi, QWORD PTR [rcx+272]
	add r15, r15
	sbb rsi, rsi
	xor rsi, QWORD PTR [rcx+208]
	add r15, r15
	sbb rdx, rdx
	xor rdx, QWORD PTR [rcx+144]
	add r15, r15
	sbb rbx, rbx
	xor rbx, QWORD PTR [rcx+80]
	add r15, r15
	sbb rax, rax
	xor rax, QWORD PTR [rcx+512]
	mov r8, rdi
	xor r8, rbx
	mov r9, rdi
	or r9, rax
	and r9, rbp
	xor r8, r9
	mov r10, rax
	xor r10, r8
	mov r11, r10
	xor r11, -1
	and r11, rbx
	and r10, rbp
	mov r12, rdi
	xor r12, r10
	mov r13, rbp
	xor r13, rsi
	mov r14, r12
	or r14, r13
	mov QWORD PTR [rcx], r10
	mov r10, r8
	xor r10, r14
	mov QWORD PTR [rcx+8], r8
	mov r8, rsi
	and r8, r10
	mov QWORD PTR [rcx+16], rbp
	mov rbp, rax
	xor rbp, -1
	and rbp, r8
	or r12, r11
	mov QWORD PTR [rcx+24], r11
	mov r11, rbp
	xor r11, r12
	mov QWORD PTR [rcx+32], rbp
	mov rbp, r11
	and rbp, rdx
	xor rbp, r10
	xor r14, rdi
	mov QWORD PTR [rcx+40], rbp
	mov rbp, r14
	xor rbp, -1
	and rbp, rax
	xor rsi, rbp
	mov rbp, r8
	xor rbp, -1
	and rbp, rbx
	or rbp, rsi
	or rdi, r13
	xor r11, rdi
	or r9, rbp
	xor r11, r9
	or r10, QWORD PTR [rcx+16]
	and r12, r10
	xor r12, rsi
	mov r10, QWORD PTR [rcx+32]
	xor r10, -1
	and r10, r12
	mov r9, QWORD PTR [rcx+24]
	or r9, rdx
	xor r9, r10
	xor r12, QWORD PTR [rcx+8]
	xor r12, -1
	and r12, rbx
	xor rdi, -1
	xor r14, rdi
	xor r12, r14
	or r12, rdx
	xor r12, rdx
	xor r12, r11
	xor rax, QWORD PTR [rcx]
	xor rsi, QWORD PTR [rcx+16]
	and rax, rsi
	xor r8, r14
	xor rax, r8
	xor rdx, -1
	and rdx, rbp
	xor rdx, rax
	mov rax, QWORD PTR [rcx+40]
	mov rbx, r9
	mov QWORD PTR [rcx+16], rdx
	mov rdx, r12
	mov rsi, QWORD PTR [rcx+16]
	xor rax, QWORD PTR [rcx+408]
	mov QWORD PTR [rcx+408], rax
	xor rbx, QWORD PTR [rcx+424]
	mov QWORD PTR [rcx+424], rbx
	xor rdx, QWORD PTR [rcx+264]
	mov QWORD PTR [rcx+264], rdx
	xor rsi, QWORD PTR [rcx+376]
	mov QWORD PTR [rcx+376], rsi
	add r15, r15
	sbb rbp, rbp
	xor rbp, QWORD PTR [rcx+80]
	add r15, r15
	sbb rdi, rdi
	xor rdi, QWORD PTR [rcx+512]
	add r15, r15
	sbb rsi, rsi
	xor rsi, QWORD PTR [rcx+448]
	add r15, r15
	sbb rdx, rdx
	xor rdx, QWORD PTR [rcx+384]
	add r15, r15
	sbb rbx, rbx
	xor rbx, QWORD PTR [rcx+320]
	add r15, r15
	sbb rax, rax
	xor rax, QWORD PTR [rcx+256]
	mov r8, rdx
	xor r8, rbx
	mov r9, rsi
	xor r9, r8
	mov r10, rax
	and r10, r9
	mov r11, rdx
	and r11, r8
	mov r12, rdi
	xor r12, r11
	mov r13, r10
	and r13, r12
	mov r14, rax
	and r14, r11
	mov QWORD PTR [rcx], r11
	mov r11, rsi
	xor r11, r14
	mov QWORD PTR [rcx+8], rsi
	mov rsi, r12
	or rsi, r11
	xor r8, rax
	mov QWORD PTR [rcx+16], rax
	mov rax, rsi
	xor rax, r8
	mov QWORD PTR [rcx+24], rsi
	mov rsi, r13
	xor rsi, -1
	and rsi, rbp
	xor rsi, rax
	xor r9, -1
	and r9, rbx
	mov rax, r12
	or rax, r9
	xor r11, r10
	xor rax, r11
	xor r10, r8
	or rdx, r10
	xor rdx, r10
	mov r8, rdx
	xor r8, -1
	and r8, r12
	xor rbx, r11
	xor r8, rbx
	xor r14, -1
	and r14, r10
	or rdx, r14
	mov r10, rdi
	xor r10, QWORD PTR [rcx+24]
	and r10, r8
	xor r10, rdx
	mov rbx, r10
	and rbx, rbp
	xor rbx, r8
	or r12, QWORD PTR [rcx+8]
	xor r12, QWORD PTR [rcx+8]
	or r14, r12
	or r8, QWORD PTR [rcx]
	and r14, r8
	xor r10, r14
	xor r9, rdx
	and r9, QWORD PTR [rcx+16]
	or r13, r9
	xor r14, r13
	mov r9, rbp
	xor r9, -1
	and r9, r14
	xor r9, rax
	and rdi, r13
	xor rax, -1
	xor rdi, rax
	xor r14, rdi
	or r10, rbp
	xor r10, r14
	mov rax, rsi
	mov rdx, r10
	mov rsi, r9
	xor rax, QWORD PTR [rcx+184]
	mov QWORD PTR [rcx+184], rax
	xor rbx, QWORD PTR [rcx+216]
	mov QWORD PTR [rcx+216], rbx
	xor rdx, QWORD PTR [rcx+360]
	mov QWORD PTR [rcx+360], rdx
	xor rsi, QWORD PTR [rcx+72]
	mov QWORD PTR [rcx+72], rsi
	add r15, r15
	sbb rbp, rbp
	xor rbp, QWORD PTR [rcx+320]
	add r15, r15
	sbb rdi, rdi
	xor rdi, QWORD PTR [rcx+256]
	add r15, r15
	sbb rsi, rsi
	xor rsi, QWORD PTR [rcx+192]
	add r15, r15
	sbb rdx, rdx
	xor rdx, QWORD PTR [rcx+128]
	add r15, r15
	sbb rbx, rbx
	xor rbx, QWORD PTR [rcx+64]
	add r15, r15
	sbb rax, rax
	xor rax, QWORD PTR [rcx+560]
	mov r8, rdi
	xor r8, -1
	and r8, rsi
	mov r9, rsi
	xor r9, -1
	and r9, rbx
	xor r9, rdx
	mov r10, rbp
	and r10, r9
	mov r11, r8
	xor r11, -1
	and r11, r10
	mov r12, r9
	xor r12, -1
	and r12, rdi
	mov r13, rbp
	or r13, r12
	mov r14, rsi
	xor r14, -1
	and r14, rdi
	xor r14, rbx
	mov QWORD PTR [rcx], rdx
	mov rdx, r13
	and rdx, r14
	or r10, rdx
	xor r9, -1
	xor rdx, r9
	xor r13, -1
	and r13, rsi
	xor rdx, r13
	xor r8, rdx
	mov r13, r11
	or r13, rax
	xor r13, r8
	xor r8, rbp
	mov rsi, rbx
	and rsi, r8
	xor rdx, rdi
	xor rsi, rdx
	xor r12, rsi
	xor rsi, r10
	or rdi, rsi
	xor rbx, r8
	xor rdi, rbx
	and r10, rax
	xor r10, rdi
	xor r14, r12
	or rdx, QWORD PTR [rcx]
	xor rdx, r14
	xor rbp, rdx
	and rbp, rax
	xor rbp, r12
	or r14, QWORD PTR [rcx]
	xor r14, QWORD PTR [rcx]
	and rdi, r14
	xor r11, rdx
	xor rdi, r11
	or rdi, rax
	xor rdi, r12
	mov rax, rbp
	mov rbx, r10
	mov rdx, r13
	mov rsi, rdi
	xor rax, QWORD PTR [rcx+280]
	mov QWORD PTR [rcx+280], rax
	xor rbx, QWORD PTR [rcx+168]
	mov QWORD PTR [rcx+168], rbx
	xor rdx, QWORD PTR [rcx+392]
	mov QWORD PTR [rcx+392], rdx
	xor rsi, QWORD PTR [rcx+312]
	mov QWORD PTR [rcx+312], rsi
	mov rax, QWORD PTR [rcx+672]
	sub rax, 1
	mov QWORD PTR [rcx+672], rax
	jne 224b
	mov rax, QWORD PTR [rcx+64]
	mov rdx, QWORD PTR [rcx+72]
	mov QWORD PTR [rcx+64], rdx
	mov QWORD PTR [rcx+72], rax
	mov rax, QWORD PTR [rcx+128]
	mov rdx, QWORD PTR [rcx+136]
	mov QWORD PTR [rcx+128], rdx
	mov QWORD PTR [rcx+136], rax
	mov rax, QWORD PTR [rcx+192]
	mov rdx, QWORD PTR [rcx+200]
	mov QWORD PTR [rcx+192], rdx
	mov QWORD PTR [rcx+200], rax
	mov rax, QWORD PTR [rcx+256]
	mov rdx, QWORD PTR [rcx+264]
	mov QWORD PTR [rcx+256], rdx
	mov QWORD PTR [rcx+264], rax
	mov rax, QWORD PTR [rcx+320]
	mov rdx, QWORD PTR [rcx+328]
	mov QWORD PTR [rcx+320], rdx
	mov QWORD PTR [rcx+328], rax
	mov rax, QWORD PTR [rcx+384]
	mov rdx, QWORD PTR [rcx+392]
	mov QWORD PTR [rcx+384], rdx
	mov QWORD PTR [rcx+392], rax
	mov rax, QWORD PTR [rcx+448]
	mov rdx, QWORD PTR [rcx+456]
	mov QWORD PTR [rcx+448], rdx
	mov QWORD PTR [rcx+456], rax
	mov rax, QWORD PTR [rcx+512]
	mov rdx, QWORD PTR [rcx+520]
	mov QWORD PTR [rcx+512], rdx
	mov QWORD PTR [rcx+520], rax
	mov rax, QWORD PTR [rcx+80]
	mov rdx, QWORD PTR [rcx+88]
	mov QWORD PTR [rcx+80], rdx
	mov QWORD PTR [rcx+88], rax
	mov rax, QWORD PTR [rcx+144]
	mov rdx, QWORD PTR [rcx+152]
	mov QWORD PTR [rcx+144], rdx
	mov QWORD PTR [rcx+152], rax
	mov rax, QWORD PTR [rcx+208]
	mov rdx, QWORD PTR [rcx+216]
	mov QWORD PTR [rcx+208], rdx
	mov QWORD PTR [rcx+216], rax
	mov rax, QWORD PTR [rcx+272]
	mov rdx, QWORD PTR [rcx+280]
	mov QWORD PTR [rcx+272], rdx
	mov QWORD PTR [rcx+280], rax
	mov rax, QWORD PTR [rcx+336]
	mov rdx, QWORD PTR [rcx+344]
	mov QWORD PTR [rcx+336], rdx
	mov QWORD PTR [rcx+344], rax
	mov rax, QWORD PTR [rcx+400]
	mov rdx, QWORD PTR [rcx+408]
	mov QWORD PTR [rcx+400], rdx
	mov QWORD PTR [rcx+408], rax
	mov rax, QWORD PTR [rcx+464]
	mov rdx, QWORD PTR [rcx+472]
	mov QWORD PTR [rcx+464], rdx
	mov QWORD PTR [rcx+472], rax
	mov rax, QWORD PTR [rcx+528]
	mov rdx, QWORD PTR [rcx+536]
	mov QWORD PTR [rcx+528], rdx
	mov QWORD PTR [rcx+536], rax
	mov rax, QWORD PTR [rcx+96]
	mov rdx, QWORD PTR [rcx+104]
	mov QWORD PTR [rcx+96], rdx
	mov QWORD PTR [rcx+104], rax
	mov rax, QWORD PTR [rcx+160]
	mov rdx, QWORD PTR [rcx+168]
	mov QWORD PTR [rcx+160], rdx
	mov QWORD PTR [rcx+168], rax
	mov rax, QWORD PTR [rcx+224]
	mov rdx, QWORD PTR [rcx+232]
	mov QWORD PTR [rcx+224], rdx
	mov QWORD PTR [rcx+232], rax
	mov rax, QWORD PTR [rcx+288]
	mov rdx, QWORD PTR [rcx+296]
	mov QWORD PTR [rcx+288], rdx
	mov QWORD PTR [rcx+296], rax
	mov rax, QWORD PTR [rcx+352]
	mov rdx, QWORD PTR [rcx+360]
	mov QWORD PTR [rcx+352], rdx
	mov QWORD PTR [rcx+360], rax
	mov rax, QWORD PTR [rcx+416]
	mov rdx, QWORD PTR [rcx+424]
	mov QWORD PTR [rcx+416], rdx
	mov QWORD PTR [rcx+424], rax
	mov rax, QWORD PTR [rcx+480]
	mov rdx, QWORD PTR [rcx+488]
	mov QWORD PTR [rcx+480], rdx
	mov QWORD PTR [rcx+488], rax
	mov rax, QWORD PTR [rcx+544]
	mov rdx, QWORD PTR [rcx+552]
	mov QWORD PTR [rcx+544], rdx
	mov QWORD PTR [rcx+552], rax
	mov rax, QWORD PTR [rcx+112]
	mov rdx, QWORD PTR [rcx+120]
	mov QWORD PTR [rcx+112], rdx
	mov QWORD PTR [rcx+120], rax
	mov rax, QWORD PTR [rcx+176]
	mov rdx, QWORD PTR [rcx+184]
	mov QWORD PTR [rcx+176], rdx
	mov QWORD PTR [rcx+184], rax
	mov rax, QWORD PTR [rcx+240]
	mov rdx, QWORD PTR [rcx+248]
	mov QWORD PTR [rcx+240], rdx
	mov QWORD PTR [rcx+248], rax
	mov rax, QWORD PTR [rcx+304]
	mov rdx, QWORD PTR [rcx+312]
	mov QWORD PTR [rcx+304], rdx
	mov QWORD PTR [rcx+312], rax
	mov rax, QWORD PTR [rcx+368]
	mov rdx, QWORD PTR [rcx+376]
	mov QWORD PTR [rcx+368], rdx
	mov QWORD PTR [rcx+376], rax
	mov rax, QWORD PTR [rcx+432]
	mov rdx, QWORD PTR [rcx+440]
	mov QWORD PTR [rcx+432], rdx
	mov QWORD PTR [rcx+440], rax
	mov rax, QWORD PTR [rcx+496]
	mov rdx, QWORD PTR [rcx+504]
	mov QWORD PTR [rcx+496], rdx
	mov QWORD PTR [rcx+504], rax
	mov rax, QWORD PTR [rcx+560]
	mov rdx, QWORD PTR [rcx+568]
	mov QWORD PTR [rcx+560], rdx
	mov QWORD PTR [rcx+568], rax
	mov rax, QWORD PTR [rcx+680]
	sub rax, 1
	mov QWORD PTR [rcx+680], rax
	jne 219b
	movabs r13, 4294967295
	movabs r14, 281470681808895
	movabs r15, 71777214294589695
	mov rax, QWORD PTR [rcx+64]
	mov rbx, QWORD PTR [rcx+128]
	mov rdx, QWORD PTR [rcx+192]
	mov rsi, QWORD PTR [rcx+256]
	mov rdi, QWORD PTR [rcx+320]
	mov rbp, QWORD PTR [rcx+384]
	mov r8, QWORD PTR [rcx+448]
	mov r9, QWORD PTR [rcx+512]
	mov r10, rax
	shr r10, 32
	xor r10, rdi
	and r10, r13
	xor rdi, r10
	ror r10, 32
	xor rax, r10
	mov r10, rbx
	shr r10, 32
	xor r10, rbp
	and r10, r13
	xor rbp, r10
	ror r10, 32
	xor rbx, r10
	mov r10, rdx
	shr r10, 32
	xor r10, r8
	and r10, r13
	xor r8, r10
	ror r10, 32
	xor rdx, r10
	mov r10, rsi
	shr r10, 32
	xor r10, r9
	and r10, r13
	xor r9, r10
	ror r10, 32
	xor rsi, r10
	mov r10, rax
	shr r10, 16
	xor r10, rdx
	and r10, r14
	xor rdx, r10
	ror r10, 48
	xor rax, r10
	mov r10, rbx
	shr r10, 16
	xor r10, rsi
	and r10, r14
	xor rsi, r10
	ror r10, 48
	xor rbx, r10
	mov r10, rdi
	shr r10, 16
	xor r10, r8
	and r10, r14
	xor r8, r10
	ror r10, 48
	xor rdi, r10
	mov r10, rbp
	shr r10, 16
	xor r10, r9
	and r10, r14
	xor r9, r10
	ror r10, 48
	xor rbp, r10
	mov r10, rax
	shr r10, 8
	xor r10, rbx
	and r10, r15
	xor rbx, r10
	ror r10, 56
	xor rax, r10
	mov r10, rdx
	shr r10, 8
	xor r10, rsi
	and r10, r15
	xor rsi, r10
	ror r10, 56
	xor rdx, r10
	mov r10, rdi
	shr r10, 8
	xor r10, rbp
	and r10, r15
	xor rbp, r10
	ror r10, 56
	xor rdi, r10
	mov r10, r8
	shr r10, 8
	xor r10, r9
	and r10, r15
	xor r9, r10
	ror r10, 56
	xor r8, r10
	mov QWORD PTR [rcx+64], rax
	mov QWORD PTR [rcx+128], rbx
	mov QWORD PTR [rcx+192], rdx
	mov QWORD PTR [rcx+256], rsi
	mov QWORD PTR [rcx+320], rdi
	mov QWORD PTR [rcx+384], rbp
	mov QWORD PTR [rcx+448], r8
	mov QWORD PTR [rcx+512], r9
	mov rax, QWORD PTR [rcx+72]
	mov rbx, QWORD PTR [rcx+136]
	mov rdx, QWORD PTR [rcx+200]
	mov rsi, QWORD PTR [rcx+264]
	mov rdi, QWORD PTR [rcx+328]
	mov rbp, QWORD PTR [rcx+392]
	mov r8, QWORD PTR [rcx+456]
	mov r9, QWORD PTR [rcx+520]
	mov r10, rax
	shr r10, 32
	xor r10, rdi
	and r10, r13
	xor rdi, r10
	ror r10, 32
	xor rax, r10
	mov r10, rbx
	shr r10, 32
	xor r10, rbp
	and r10, r13
	xor rbp, r10
	ror r10, 32
	xor rbx, r10
	mov r10, rdx
	shr r10, 32
	xor r10, r8
	and r10, r13
	xor r8, r10
	ror r10, 32
	xor rdx, r10
	mov r10, rsi
	shr r10, 32
	xor r10, r9
	and r10, r13
	xor r9, r10
	ror r10, 32
	xor rsi, r10
	mov r10, rax
	shr r10, 16
	xor r10, rdx
	and r10, r14
	xor rdx, r10
	ror r10, 48
	xor rax, r10
	mov r10, rbx
	shr r10, 16
	xor r10, rsi
	and r10, r14
	xor rsi, r10
	ror r10, 48
	xor rbx, r10
	mov r10, rdi
	shr r10, 16
	xor r10, r8
	and r10, r14
	xor r8, r10
	ror r10, 48
	xor rdi, r10
	mov r10, rbp
	shr r10, 16
	xor r10, r9
	and r10, r14
	xor r9, r10
	ror r10, 48
	xor rbp, r10
	mov r10, rax
	shr r10, 8
	xor r10, rbx
	and r10, r15
	xor rbx, r10
	ror r10, 56
	xor rax, r10
	mov r10, rdx
	shr r10, 8
	xor r10, rsi
	and r10, r15
	xor rsi, r10
	ror r10, 56
	xor rdx, r10
	mov r10, rdi
	shr r10, 8
	xor r10, rbp
	and r10, r15
	xor rbp, r10
	ror r10, 56
	xor rdi, r10
	mov r10, r8
	shr r10, 8
	xor r10, r9
	and r10, r15
	xor r9, r10
	ror r10, 56
	xor r8, r10
	mov QWORD PTR [rcx+72], rax
	mov QWORD PTR [rcx+136], rbx
	mov QWORD PTR [rcx+200], rdx
	mov QWORD PTR [rcx+264], rsi
	mov QWORD PTR [rcx+328], rdi
	mov QWORD PTR [rcx+392], rbp
	mov QWORD PTR [rcx+456], r8
	mov QWORD PTR [rcx+520], r9
	mov rax, QWORD PTR [rcx+80]
	mov rbx, QWORD PTR [rcx+144]
	mov rdx, QWORD PTR [rcx+208]
	mov rsi, QWORD PTR [rcx+272]
	mov rdi, QWORD PTR [rcx+336]
	mov rbp, QWORD PTR [rcx+400]
	mov r8, QWORD PTR [rcx+464]
	mov r9, QWORD PTR [rcx+528]
	mov r10, rax
	shr r10, 32
	xor r10, rdi
	and r10, r13
	xor rdi, r10
	ror r10, 32
	xor rax, r10
	mov r10, rbx
	shr r10, 32
	xor r10, rbp
	and r10, r13
	xor rbp, r10
	ror r10, 32
	xor rbx, r10
	mov r10, rdx
	shr r10, 32
	xor r10, r8
	and r10, r13
	xor r8, r10
	ror r10, 32
	xor rdx, r10
	mov r10, rsi
	shr r10, 32
	xor r10, r9
	and r10, r13
	xor r9, r10
	ror r10, 32
	xor rsi, r10
	mov r10, rax
	shr r10, 16
	xor r10, rdx
	and r10, r14
	xor rdx, r10
	ror r10, 48
	xor rax, r10
	mov r10, rbx
	shr r10, 16
	xor r10, rsi
	and r10, r14
	xor rsi, r10
	ror r10, 48
	xor rbx, r10
	mov r10, rdi
	shr r10, 16
	xor r10, r8
	and r10, r14
	xor r8, r10
	ror r10, 48
	xor rdi, r10
	mov r10, rbp
	shr r10, 16
	xor r10, r9
	and r10, r14
	xor r9, r10
	ror r10, 48
	xor rbp, r10
	mov r10, rax
	shr r10, 8
	xor r10, rbx
	and r10, r15
	xor rbx, r10
	ror r10, 56
	xor rax, r10
	mov r10, rdx
	shr r10, 8
	xor r10, rsi
	and r10, r15
	xor rsi, r10
	ror r10, 56
	xor rdx, r10
	mov r10, rdi
	shr r10, 8
	xor r10, rbp
	and r10, r15
	xor rbp, r10
	ror r10, 56
	xor rdi, r10
	mov r10, r8
	shr r10, 8
	xor r10, r9
	and r10, r15
	xor r9, r10
	ror r10, 56
	xor r8, r10
	mov QWORD PTR [rcx+80], rax
	mov QWORD PTR [rcx+144], rbx
	mov QWORD PTR [rcx+208], rdx
	mov QWORD PTR [rcx+272], rsi
	mov QWORD PTR [rcx+336], rdi
	mov QWORD PTR [rcx+400], rbp
	mov QWORD PTR [rcx+464], r8
	mov QWORD PTR [rcx+528], r9
	mov rax, QWORD PTR [rcx+88]
	mov rbx, QWORD PTR [rcx+152]
	mov rdx, QWORD PTR [rcx+216]
	mov rsi, QWORD PTR [rcx+280]
	mov rdi, QWORD PTR [rcx+344]
	mov rbp, QWORD PTR [rcx+408]
	mov r8, QWORD PTR [rcx+472]
	mov r9, QWORD PTR [rcx+536]
	mov r10, rax
	shr r10, 32
	xor r10, rdi
	and r10, r13
	xor rdi, r10
	ror r10, 32
	xor rax, r10
	mov r10, rbx
	shr r10, 32
	xor r10, rbp
	and r10, r13
	xor rbp, r10
	ror r10, 32
	xor rbx, r10
	mov r10, rdx
	shr r10, 32
	xor r10, r8
	and r10, r13
	xor r8, r10
	ror r10, 32
	xor rdx, r10
	mov r10, rsi
	shr r10, 32
	xor r10, r9
	and r10, r13
	xor r9, r10
	ror r10, 32
	xor rsi, r10
	mov r10, rax
	shr r10, 16
	xor r10, rdx
	and r10, r14
	xor rdx, r10
	ror r10, 48
	xor rax, r10
	mov r10, rbx
	shr r10, 16
	xor r10, rsi
	and r10, r14
	xor rsi, r10
	ror r10, 48
	xor rbx, r10
	mov r10, rdi
	shr r10, 16
	xor r10, r8
	and r10, r14
	xor r8, r10
	ror r10, 48
	xor rdi, r10
	mov r10, rbp
	shr r10, 16
	xor r10, r9
	and r10, r14
	xor r9, r10
	ror r10, 48
	xor rbp, r10
	mov r10, rax
	shr r10, 8
	xor r10, rbx
	and r10, r15
	xor rbx, r10
	ror r10, 56
	xor rax, r10
	mov r10, rdx
	shr r10, 8
	xor r10, rsi
	and r10, r15
	xor rsi, r10
	ror r10, 56
	xor rdx, r10
	mov r10, rdi
	shr r10, 8
	xor r10, rbp
	and r10, r15
	xor rbp, r10
	ror r10, 56
	xor rdi, r10
	mov r10, r8
	shr r10, 8
	xor r10, r9
	and r10, r15
	xor r9, r10
	ror r10, 56
	xor r8, r10
	mov QWORD PTR [rcx+88], rax
	mov QWORD PTR [rcx+152], rbx
	mov QWORD PTR [rcx+216], rdx
	mov QWORD PTR [rcx+280], rsi
	mov QWORD PTR [rcx+344], rdi
	mov QWORD PTR [rcx+408], rbp
	mov QWORD PTR [rcx+472], r8
	mov QWORD PTR [rcx+536], r9
	mov rax, QWORD PTR [rcx+96]
	mov rbx, QWORD PTR [rcx+160]
	mov rdx, QWORD PTR [rcx+224]
	mov rsi, QWORD PTR [rcx+288]
	mov rdi, QWORD PTR [rcx+352]
	mov rbp, QWORD PTR [rcx+416]
	mov r8, QWORD PTR [rcx+480]
	mov r9, QWORD PTR [rcx+544]
	mov r10, rax
	shr r10, 32
	xor r10, rdi
	and r10, r13
	xor rdi, r10
	ror r10, 32
	xor rax, r10
	mov r10, rbx
	shr r10, 32
	xor r10, rbp
	and r10, r13
	xor rbp, r10
	ror r10, 32
	xor rbx, r10
	mov r10, rdx
	shr r10, 32
	xor r10, r8
	and r10, r13
	xor r8, r10
	ror r10, 32
	xor rdx, r10
	mov r10, rsi
	shr r10, 32
	xor r10, r9
	and r10, r13
	xor r9, r10
	ror r10, 32
	xor rsi, r10
	mov r10, rax
	shr r10, 16
	xor r10, rdx
	and r10, r14
	xor rdx, r10
	ror r10, 48
	xor rax, r10
	mov r10, rbx
	shr r10, 16
	xor r10, rsi
	and r10, r14
	xor rsi, r10
	ror r10, 48
	xor rbx, r10
	mov r10, rdi
	shr r10, 16
	xor r10, r8
	and r10, r14
	xor r8, r10
	ror r10, 48
	xor rdi, r10
	mov r10, rbp
	shr r10, 16
	xor r10, r9
	and r10, r14
	xor r9, r10
	ror r10, 48
	xor rbp, r10
	mov r10, rax
	shr r10, 8
	xor r10, rbx
	and r10, r15
	xor rbx, r10
	ror r10, 56
	xor rax, r10
	mov r10, rdx
	shr r10, 8
	xor r10, rsi
	and r10, r15
	xor rsi, r10
	ror r10, 56
	xor rdx, r10
	mov r10, rdi
	shr r10, 8
	xor r10, rbp
	and r10, r15
	xor rbp, r10
	ror r10, 56
	xor rdi, r10
	mov r10, r8
	shr r10, 8
	xor r10, r9
	and r10, r15
	xor r9, r10
	ror r10, 56
	xor r8, r10
	mov QWORD PTR [rcx+96], rax
	mov QWORD PTR [rcx+160], rbx
	mov QWORD PTR [rcx+224], rdx
	mov QWORD PTR [rcx+288], rsi
	mov QWORD PTR [rcx+352], rdi
	mov QWORD PTR [rcx+416], rbp
	mov QWORD PTR [rcx+480], r8
	mov QWORD PTR [rcx+544], r9
	mov rax, QWORD PTR [rcx+104]
	mov rbx, QWORD PTR [rcx+168]
	mov rdx, QWORD PTR [rcx+232]
	mov rsi, QWORD PTR [rcx+296]
	mov rdi, QWORD PTR [rcx+360]
	mov rbp, QWORD PTR [rcx+424]
	mov r8, QWORD PTR [rcx+488]
	mov r9, QWORD PTR [rcx+552]
	mov r10, rax
	shr r10, 32
	xor r10, rdi
	and r10, r13
	xor rdi, r10
	ror r10, 32
	xor rax, r10
	mov r10, rbx
	shr r10, 32
	xor r10, rbp
	and r10, r13
	xor rbp, r10
	ror r10, 32
	xor rbx, r10
	mov r10, rdx
	shr r10, 32
	xor r10, r8
	and r10, r13
	xor r8, r10
	ror r10, 32
	xor rdx, r10
	mov r10, rsi
	shr r10, 32
	xor r10, r9
	and r10, r13
	xor r9, r10
	ror r10, 32
	xor rsi, r10
	mov r10, rax
	shr r10, 16
	xor r10, rdx
	and r10, r14
	xor rdx, r10
	ror r10, 48
	xor rax, r10
	mov r10, rbx
	shr r10, 16
	xor r10, rsi
	and r10, r14
	xor rsi, r10
	ror r10, 48
	xor rbx, r10
	mov r10, rdi
	shr r10, 16
	xor r10, r8
	and r10, r14
	xor r8, r10
	ror r10, 48
	xor rdi, r10
	mov r10, rbp
	shr r10, 16
	xor r10, r9
	and r10, r14
	xor r9, r10
	ror r10, 48
	xor rbp, r10
	mov r10, rax
	shr r10, 8
	xor r10, rbx
	and r10, r15
	xor rbx, r10
	ror r10, 56
	xor rax, r10
	mov r10, rdx
	shr r10, 8
	xor r10, rsi
	and r10, r15
	xor rsi, r10
	ror r10, 56
	xor rdx, r10
	mov r10, rdi
	shr r10, 8
	xor r10, rbp
	and r10, r15
	xor rbp, r10
	ror r10, 56
	xor rdi, r10
	mov r10, r8
	shr r10, 8
	xor r10, r9
	and r10, r15
	xor r9, r10
	ror r10, 56
	xor r8, r10
	mov QWORD PTR [rcx+104], rax
	mov QWORD PTR [rcx+168], rbx
	mov QWORD PTR [rcx+232], rdx
	mov QWORD PTR [rcx+296], rsi
	mov QWORD PTR [rcx+360], rdi
	mov QWORD PTR [rcx+424], rbp
	mov QWORD PTR [rcx+488], r8
	mov QWORD PTR [rcx+552], r9
	mov rax, QWORD PTR [rcx+112]
	mov rbx, QWORD PTR [rcx+176]
	mov rdx, QWORD PTR [rcx+240]
	mov rsi, QWORD PTR [rcx+304]
	mov rdi, QWORD PTR [rcx+368]
	mov rbp, QWORD PTR [rcx+432]
	mov r8, QWORD PTR [rcx+496]
	mov r9, QWORD PTR [rcx+560]
	mov r10, rax
	shr r10, 32
	xor r10, rdi
	and r10, r13
	xor rdi, r10
	ror r10, 32
	xor rax, r10
	mov r10, rbx
	shr r10, 32
	xor r10, rbp
	and r10, r13
	xor rbp, r10
	ror r10, 32
	xor rbx, r10
	mov r10, rdx
	shr r10, 32
	xor r10, r8
	and r10, r13
	xor r8, r10
	ror r10, 32
	xor rdx, r10
	mov r10, rsi
	shr r10, 32
	xor r10, r9
	and r10, r13
	xor r9, r10
	ror r10, 32
	xor rsi, r10
	mov r10, rax
	shr r10, 16
	xor r10, rdx
	and r10, r14
	xor rdx, r10
	ror r10, 48
	xor rax, r10
	mov r10, rbx
	shr r10, 16
	xor r10, rsi
	and r10, r14
	xor rsi, r10
	ror r10, 48
	xor rbx, r10
	mov r10, rdi
	shr r10, 16
	xor r10, r8
	and r10, r14
	xor r8, r10
	ror r10, 48
	xor rdi, r10
	mov r10, rbp
	shr r10, 16
	xor r10, r9
	and r10, r14
	xor r9, r10
	ror r10, 48
	xor rbp, r10
	mov r10, rax
	shr r10, 8
	xor r10, rbx
	and r10, r15
	xor rbx, r10
	ror r10, 56
	xor rax, r10
	mov r10, rdx
	shr r10, 8
	xor r10, rsi
	and r10, r15
	xor rsi, r10
	ror r10, 56
	xor rdx, r10
	mov r10, rdi
	shr r10, 8
	xor r10, rbp
	and r10, r15
	xor rbp, r10
	ror r10, 56
	xor rdi, r10
	mov r10, r8
	shr r10, 8
	xor r10, r9
	and r10, r15
	xor r9, r10
	ror r10, 56
	xor r8, r10
	mov QWORD PTR [rcx+112], rax
	mov QWORD PTR [rcx+176], rbx
	mov QWORD PTR [rcx+240], rdx
	mov QWORD PTR [rcx+304], rsi
	mov QWORD PTR [rcx+368], rdi
	mov QWORD PTR [rcx+432], rbp
	mov QWORD PTR [rcx+496], r8
	mov QWORD PTR [rcx+560], r9
	mov rax, QWORD PTR [rcx+120]
	mov rbx, QWORD PTR [rcx+184]
	mov rdx, QWORD PTR [rcx+248]
	mov rsi, QWORD PTR [rcx+312]
	mov rdi, QWORD PTR [rcx+376]
	mov rbp, QWORD PTR [rcx+440]
	mov r8, QWORD PTR [rcx+504]
	mov r9, QWORD PTR [rcx+568]
	mov r10, rax
	shr r10, 32
	xor r10, rdi
	and r10, r13
	xor rdi, r10
	ror r10, 32
	xor rax, r10
	mov r10, rbx
	shr r10, 32
	xor r10, rbp
	and r10, r13
	xor rbp, r10
	ror r10, 32
	xor rbx, r10
	mov r10, rdx
	shr r10, 32
	xor r10, r8
	and r10, r13
	xor r8, r10
	ror r10, 32
	xor rdx, r10
	mov r10, rsi
	shr r10, 32
	xor r10, r9
	and r10, r13
	xor r9, r10
	ror r10, 32
	xor rsi, r10
	mov r10, rax
	shr r10, 16
	xor r10, rdx
	and r10, r14
	xor rdx, r10
	ror r10, 48
	xor rax, r10
	mov r10, rbx
	shr r10, 16
	xor r10, rsi
	and r10, r14
	xor rsi, r10
	ror r10, 48
	xor rbx, r10
	mov r10, rdi
	shr r10, 16
	xor r10, r8
	and r10, r14
	xor r8, r10
	ror r10, 48
	xor rdi, r10
	mov r10, rbp
	shr r10, 16
	xor r10, r9
	and r10, r14
	xor r9, r10
	ror r10, 48
	xor rbp, r10
	mov r10, rax
	shr r10, 8
	xor r10, rbx
	and r10, r15
	xor rbx, r10
	ror r10, 56
	xor rax, r10
	mov r10, rdx
	shr r10, 8
	xor r10, rsi
	and r10, r15
	xor rsi, r10
	ror r10, 56
	xor rdx, r10
	mov r10, rdi
	shr r10, 8
	xor r10, rbp
	and r10, r15
	xor rbp, r10
	ror r10, 56
	xor rdi, r10
	mov r10, r8
	shr r10, 8
	xor r10, r9
	and r10, r15
	xor r9, r10
	ror r10, 56
	xor r8, r10
	mov QWORD PTR [rcx+120], rax
	mov QWORD PTR [rcx+184], rbx
	mov QWORD PTR [rcx+248], rdx
	mov QWORD PTR [rcx+312], rsi
	mov QWORD PTR [rcx+376], rdi
	mov QWORD PTR [rcx+440], rbp
	mov QWORD PTR [rcx+504], r8
	mov QWORD PTR [rcx+568], r9
	movabs r13, 1085102592571150095
	movabs r14, 3689348814741910323
	movabs r15, 6148914691236517205
	mov rax, QWORD PTR [rcx+64]
	mov rbx, QWORD PTR [rcx+72]
	mov rdx, QWORD PTR [rcx+80]
	mov rsi, QWORD PTR [rcx+88]
	mov rdi, QWORD PTR [rcx+96]
	mov rbp, QWORD PTR [rcx+104]
	mov r8, QWORD PTR [rcx+112]
	mov r9, QWORD PTR [rcx+120]
	mov r10, rax
	shr r10, 4
	xor r10, rdi
	and r10, r13
	xor rdi, r10
	ror r10, 60
	xor rax, r10
	mov r10, rbx
	shr r10, 4
	xor r10, rbp
	and r10, r13
	xor rbp, r10
	ror r10, 60
	xor rbx, r10
	mov r10, rdx
	shr r10, 4
	xor r10, r8
	and r10, r13
	xor r8, r10
	ror r10, 60
	xor rdx, r10
	mov r10, rsi
	shr r10, 4
	xor r10, r9
	and r10, r13
	xor r9, r10
	ror r10, 60
	xor rsi, r10
	mov r10, rax
	shr r10, 2
	xor r10, rdx
	and r10, r14
	xor rdx, r10
	ror r10, 62
	xor rax, r10
	mov r10, rbx
	shr r10, 2
	xor r10, rsi
	and r10, r14
	xor rsi, r10
	ror r10, 62
	xor rbx, r10
	mov r10, rdi
	shr r10, 2
	xor r10, r8
	and r10, r14
	xor r8, r10
	ror r10, 62
	xor rdi, r10
	mov r10, rbp
	shr r10, 2
	xor r10, r9
	and r10, r14
	xor r9, r10
	ror r10, 62
	xor rbp, r10
	mov r10, rax
	shr r10, 1
	xor r10, rbx
	and r10, r15
	xor rbx, r10
	ror r10, 63
	xor rax, r10
	mov r10, rdx
	shr r10, 1
	xor r10, rsi
	and r10, r15
	xor rsi, r10
	ror r10, 63
	xor rdx, r10
	mov r10, rdi
	shr r10, 1
	xor r10, rbp
	and r10, r15
	xor rbp, r10
	ror r10, 63
	xor rdi, r10
	mov r10, r8
	shr r10, 1
	xor r10, r9
	and r10, r15
	xor r9, r10
	ror r10, 63
	xor r8, r10
	mov QWORD PTR [rcx+64], rax
	mov QWORD PTR [rcx+72], rbx
	mov QWORD PTR [rcx+80], rdx
	mov QWORD PTR [rcx+88], rsi
	mov QWORD PTR [rcx+96], rdi
	mov QWORD PTR [rcx+104], rbp
	mov QWORD PTR [rcx+112], r8
	mov QWORD PTR [rcx+120], r9
	mov rax, QWORD PTR [rcx+128]
	mov rbx, QWORD PTR [rcx+136]
	mov rdx, QWORD PTR [rcx+144]
	mov rsi, QWORD PTR [rcx+152]
	mov rdi, QWORD PTR [rcx+160]
	mov rbp, QWORD PTR [rcx+168]
	mov r8, QWORD PTR [rcx+176]
	mov r9, QWORD PTR [rcx+184]
	mov r10, rax
	shr r10, 4
	xor r10, rdi
	and r10, r13
	xor rdi, r10
	ror r10, 60
	xor rax, r10
	mov r10, rbx
	shr r10, 4
	xor r10, rbp
	and r10, r13
	xor rbp, r10
	ror r10, 60
	xor rbx, r10
	mov r10, rdx
	shr r10, 4
	xor r10, r8
	and r10, r13
	xor r8, r10
	ror r10, 60
	xor rdx, r10
	mov r10, rsi
	shr r10, 4
	xor r10, r9
	and r10, r13
	xor r9, r10
	ror r10, 60
	xor rsi, r10
	mov r10, rax
	shr r10, 2
	xor r10, rdx
	and r10, r14
	xor rdx, r10
	ror r10, 62
	xor rax, r10
	mov r10, rbx
	shr r10, 2
	xor r10, rsi
	and r10, r14
	xor rsi, r10
	ror r10, 62
	xor rbx, r10
	mov r10, rdi
	shr r10, 2
	xor r10, r8
	and r10, r14
	xor r8, r10
	ror r10, 62
	xor rdi, r10
	mov r10, rbp
	shr r10, 2
	xor r10, r9
	and r10, r14
	xor r9, r10
	ror r10, 62
	xor rbp, r10
	mov r10, rax
	shr r10, 1
	xor r10, rbx
	and r10, r15
	xor rbx, r10
	ror r10, 63
	xor rax, r10
	mov r10, rdx
	shr r10, 1
	xor r10, rsi
	and r10, r15
	xor rsi, r10
	ror r10, 63
	xor rdx, r10
	mov r10, rdi
	shr r10, 1
	xor r10, rbp
	and r10, r15
	xor rbp, r10
	ror r10, 63
	xor rdi, r10
	mov r10, r8
	shr r10, 1
	xor r10, r9
	and r10, r15
	xor r9, r10
	ror r10, 63
	xor r8, r10
	mov QWORD PTR [rcx+128], rax
	mov QWORD PTR [rcx+136], rbx
	mov QWORD PTR [rcx+144], rdx
	mov QWORD PTR [rcx+152], rsi
	mov QWORD PTR [rcx+160], rdi
	mov QWORD PTR [rcx+168], rbp
	mov QWORD PTR [rcx+176], r8
	mov QWORD PTR [rcx+184], r9
	mov rax, QWORD PTR [rcx+192]
	mov rbx, QWORD PTR [rcx+200]
	mov rdx, QWORD PTR [rcx+208]
	mov rsi, QWORD PTR [rcx+216]
	mov rdi, QWORD PTR [rcx+224]
	mov rbp, QWORD PTR [rcx+232]
	mov r8, QWORD PTR [rcx+240]
	mov r9, QWORD PTR [rcx+248]
	mov r10, rax
	shr r10, 4
	xor r10, rdi
	and r10, r13
	xor rdi, r10
	ror r10, 60
	xor rax, r10
	mov r10, rbx
	shr r10, 4
	xor r10, rbp
	and r10, r13
	xor rbp, r10
	ror r10, 60
	xor rbx, r10
	mov r10, rdx
	shr r10, 4
	xor r10, r8
	and r10, r13
	xor r8, r10
	ror r10, 60
	xor rdx, r10
	mov r10, rsi
	shr r10, 4
	xor r10, r9
	and r10, r13
	xor r9, r10
	ror r10, 60
	xor rsi, r10
	mov r10, rax
	shr r10, 2
	xor r10, rdx
	and r10, r14
	xor rdx, r10
	ror r10, 62
	xor rax, r10
	mov r10, rbx
	shr r10, 2
	xor r10, rsi
	and r10, r14
	xor rsi, r10
	ror r10, 62
	xor rbx, r10
	mov r10, rdi
	shr r10, 2
	xor r10, r8
	and r10, r14
	xor r8, r10
	ror r10, 62
	xor rdi, r10
	mov r10, rbp
	shr r10, 2
	xor r10, r9
	and r10, r14
	xor r9, r10
	ror r10, 62
	xor rbp, r10
	mov r10, rax
	shr r10, 1
	xor r10, rbx
	and r10, r15
	xor rbx, r10
	ror r10, 63
	xor rax, r10
	mov r10, rdx
	shr r10, 1
	xor r10, rsi
	and r10, r15
	xor rsi, r10
	ror r10, 63
	xor rdx, r10
	mov r10, rdi
	shr r10, 1
	xor r10, rbp
	and r10, r15
	xor rbp, r10
	ror r10, 63
	xor rdi, r10
	mov r10, r8
	shr r10, 1
	xor r10, r9
	and r10, r15
	xor r9, r10
	ror r10, 63
	xor r8, r10
	mov QWORD PTR [rcx+192], rax
	mov QWORD PTR [rcx+200], rbx
	mov QWORD PTR [rcx+208], rdx
	mov QWORD PTR [rcx+216], rsi
	mov QWORD PTR [rcx+224], rdi
	mov QWORD PTR [rcx+232], rbp
	mov QWORD PTR [rcx+240], r8
	mov QWORD PTR [rcx+248], r9
	mov rax, QWORD PTR [rcx+256]
	mov rbx, QWORD PTR [rcx+264]
	mov rdx, QWORD PTR [rcx+272]
	mov rsi, QWORD PTR [rcx+280]
	mov rdi, QWORD PTR [rcx+288]
	mov rbp, QWORD PTR [rcx+296]
	mov r8, QWORD PTR [rcx+304]
	mov r9, QWORD PTR [rcx+312]
	mov r10, rax
	shr r10, 4
	xor r10, rdi
	and r10, r13
	xor rdi, r10
	ror r10, 60
	xor rax, r10
	mov r10, rbx
	shr r10, 4
	xor r10, rbp
	and r10, r13
	xor rbp, r10
	ror r10, 60
	xor rbx, r10
	mov r10, rdx
	shr r10, 4
	xor r10, r8
	and r10, r13
	xor r8, r10
	ror r10, 60
	xor rdx, r10
	mov r10, rsi
	shr r10, 4
	xor r10, r9
	and r10, r13
	xor r9, r10
	ror r10, 60
	xor rsi, r10
	mov r10, rax
	shr r10, 2
	xor r10, rdx
	and r10, r14
	xor rdx, r10
	ror r10, 62
	xor rax, r10
	mov r10, rbx
	shr r10, 2
	xor r10, rsi
	and r10, r14
	xor rsi, r10
	ror r10, 62
	xor rbx, r10
	mov r10, rdi
	shr r10, 2
	xor r10, r8
	and r10, r14
	xor r8, r10
	ror r10, 62
	xor rdi, r10
	mov r10, rbp
	shr r10, 2
	xor r10, r9
	and r10, r14
	xor r9, r10
	ror r10, 62
	xor rbp, r10
	mov r10, rax
	shr r10, 1
	xor r10, rbx
	and r10, r15
	xor rbx, r10
	ror r10, 63
	xor rax, r10
	mov r10, rdx
	shr r10, 1
	xor r10, rsi
	and r10, r15
	xor rsi, r10
	ror r10, 63
	xor rdx, r10
	mov r10, rdi
	shr r10, 1
	xor r10, rbp
	and r10, r15
	xor rbp, r10
	ror r10, 63
	xor rdi, r10
	mov r10, r8
	shr r10, 1
	xor r10, r9
	and r10, r15
	xor r9, r10
	ror r10, 63
	xor r8, r10
	mov QWORD PTR [rcx+256], rax
	mov QWORD PTR [rcx+264], rbx
	mov QWORD PTR [rcx+272], rdx
	mov QWORD PTR [rcx+280], rsi
	mov QWORD PTR [rcx+288], rdi
	mov QWORD PTR [rcx+296], rbp
	mov QWORD PTR [rcx+304], r8
	mov QWORD PTR [rcx+312], r9
	mov rax, QWORD PTR [rcx+320]
	mov rbx, QWORD PTR [rcx+328]
	mov rdx, QWORD PTR [rcx+336]
	mov rsi, QWORD PTR [rcx+344]
	mov rdi, QWORD PTR [rcx+352]
	mov rbp, QWORD PTR [rcx+360]
	mov r8, QWORD PTR [rcx+368]
	mov r9, QWORD PTR [rcx+376]
	mov r10, rax
	shr r10, 4
	xor r10, rdi
	and r10, r13
	xor rdi, r10
	ror r10, 60
	xor rax, r10
	mov r10, rbx
	shr r10, 4
	xor r10, rbp
	and r10, r13
	xor rbp, r10
	ror r10, 60
	xor rbx, r10
	mov r10, rdx
	shr r10, 4
	xor r10, r8
	and r10, r13
	xor r8, r10
	ror r10, 60
	xor rdx, r10
	mov r10, rsi
	shr r10, 4
	xor r10, r9
	and r10, r13
	xor r9, r10
	ror r10, 60
	xor rsi, r10
	mov r10, rax
	shr r10, 2
	xor r10, rdx
	and r10, r14
	xor rdx, r10
	ror r10, 62
	xor rax, r10
	mov r10, rbx
	shr r10, 2
	xor r10, rsi
	and r10, r14
	xor rsi, r10
	ror r10, 62
	xor rbx, r10
	mov r10, rdi
	shr r10, 2
	xor r10, r8
	and r10, r14
	xor r8, r10
	ror r10, 62
	xor rdi, r10
	mov r10, rbp
	shr r10, 2
	xor r10, r9
	and r10, r14
	xor r9, r10
	ror r10, 62
	xor rbp, r10
	mov r10, rax
	shr r10, 1
	xor r10, rbx
	and r10, r15
	xor rbx, r10
	ror r10, 63
	xor rax, r10
	mov r10, rdx
	shr r10, 1
	xor r10, rsi
	and r10, r15
	xor rsi, r10
	ror r10, 63
	xor rdx, r10
	mov r10, rdi
	shr r10, 1
	xor r10, rbp
	and r10, r15
	xor rbp, r10
	ror r10, 63
	xor rdi, r10
	mov r10, r8
	shr r10, 1
	xor r10, r9
	and r10, r15
	xor r9, r10
	ror r10, 63
	xor r8, r10
	mov QWORD PTR [rcx+320], rax
	mov QWORD PTR [rcx+328], rbx
	mov QWORD PTR [rcx+336], rdx
	mov QWORD PTR [rcx+344], rsi
	mov QWORD PTR [rcx+352], rdi
	mov QWORD PTR [rcx+360], rbp
	mov QWORD PTR [rcx+368], r8
	mov QWORD PTR [rcx+376], r9
	mov rax, QWORD PTR [rcx+384]
	mov rbx, QWORD PTR [rcx+392]
	mov rdx, QWORD PTR [rcx+400]
	mov rsi, QWORD PTR [rcx+408]
	mov rdi, QWORD PTR [rcx+416]
	mov rbp, QWORD PTR [rcx+424]
	mov r8, QWORD PTR [rcx+432]
	mov r9, QWORD PTR [rcx+440]
	mov r10, rax
	shr r10, 4
	xor r10, rdi
	and r10, r13
	xor rdi, r10
	ror r10, 60
	xor rax, r10
	mov r10, rbx
	shr r10, 4
	xor r10, rbp
	and r10, r13
	xor rbp, r10
	ror r10, 60
	xor rbx, r10
	mov r10, rdx
	shr r10, 4
	xor r10, r8
	and r10, r13
	xor r8, r10
	ror r10, 60
	xor rdx, r10
	mov r10, rsi
	shr r10, 4
	xor r10, r9
	and r10, r13
	xor r9, r10
	ror r10, 60
	xor rsi, r10
	mov r10, rax
	shr r10, 2
	xor r10, rdx
	and r10, r14
	xor rdx, r10
	ror r10, 62
	xor rax, r10
	mov r10, rbx
	shr r10, 2
	xor r10, rsi
	and r10, r14
	xor rsi, r10
	ror r10, 62
	xor rbx, r10
	mov r10, rdi
	shr r10, 2
	xor r10, r8
	and r10, r14
	xor r8, r10
	ror r10, 62
	xor rdi, r10
	mov r10, rbp
	shr r10, 2
	xor r10, r9
	and r10, r14
	xor r9, r10
	ror r10, 62
	xor rbp, r10
	mov r10, rax
	shr r10, 1
	xor r10, rbx
	and r10, r15
	xor rbx, r10
	ror r10, 63
	xor rax, r10
	mov r10, rdx
	shr r10, 1
	xor r10, rsi
	and r10, r15
	xor rsi, r10
	ror r10, 63
	xor rdx, r10
	mov r10, rdi
	shr r10, 1
	xor r10, rbp
	and r10, r15
	xor rbp, r10
	ror r10, 63
	xor rdi, r10
	mov r10, r8
	shr r10, 1
	xor r10, r9
	and r10, r15
	xor r9, r10
	ror r10, 63
	xor r8, r10
	mov QWORD PTR [rcx+384], rax
	mov QWORD PTR [rcx+392], rbx
	mov QWORD PTR [rcx+400], rdx
	mov QWORD PTR [rcx+408], rsi
	mov QWORD PTR [rcx+416], rdi
	mov QWORD PTR [rcx+424], rbp
	mov QWORD PTR [rcx+432], r8
	mov QWORD PTR [rcx+440], r9
	mov rax, QWORD PTR [rcx+448]
	mov rbx, QWORD PTR [rcx+456]
	mov rdx, QWORD PTR [rcx+464]
	mov rsi, QWORD PTR [rcx+472]
	mov rdi, QWORD PTR [rcx+480]
	mov rbp, QWORD PTR [rcx+488]
	mov r8, QWORD PTR [rcx+496]
	mov r9, QWORD PTR [rcx+504]
	mov r10, rax
	shr r10, 4
	xor r10, rdi
	and r10, r13
	xor rdi, r10
	ror r10, 60
	xor rax, r10
	mov r10, rbx
	shr r10, 4
	xor r10, rbp
	and r10, r13
	xor rbp, r10
	ror r10, 60
	xor rbx, r10
	mov r10, rdx
	shr r10, 4
	xor r10, r8
	and r10, r13
	xor r8, r10
	ror r10, 60
	xor rdx, r10
	mov r10, rsi
	shr r10, 4
	xor r10, r9
	and r10, r13
	xor r9, r10
	ror r10, 60
	xor rsi, r10
	mov r10, rax
	shr r10, 2
	xor r10, rdx
	and r10, r14
	xor rdx, r10
	ror r10, 62
	xor rax, r10
	mov r10, rbx
	shr r10, 2
	xor r10, rsi
	and r10, r14
	xor rsi, r10
	ror r10, 62
	xor rbx, r10
	mov r10, rdi
	shr r10, 2
	xor r10, r8
	and r10, r14
	xor r8, r10
	ror r10, 62
	xor rdi, r10
	mov r10, rbp
	shr r10, 2
	xor r10, r9
	and r10, r14
	xor r9, r10
	ror r10, 62
	xor rbp, r10
	mov r10, rax
	shr r10, 1
	xor r10, rbx
	and r10, r15
	xor rbx, r10
	ror r10, 63
	xor rax, r10
	mov r10, rdx
	shr r10, 1
	xor r10, rsi
	and r10, r15
	xor rsi, r10
	ror r10, 63
	xor rdx, r10
	mov r10, rdi
	shr r10, 1
	xor r10, rbp
	and r10, r15
	xor rbp, r10
	ror r10, 63
	xor rdi, r10
	mov r10, r8
	shr r10, 1
	xor r10, r9
	and r10, r15
	xor r9, r10
	ror r10, 63
	xor r8, r10
	mov QWORD PTR [rcx+448], rax
	mov QWORD PTR [rcx+456], rbx
	mov QWORD PTR [rcx+464], rdx
	mov QWORD PTR [rcx+472], rsi
	mov QWORD PTR [rcx+480], rdi
	mov QWORD PTR [rcx+488], rbp
	mov QWORD PTR [rcx+496], r8
	mov QWORD PTR [rcx+504], r9
	mov rax, QWORD PTR [rcx+512]
	mov rbx, QWORD PTR [rcx+520]
	mov rdx, QWORD PTR [rcx+528]
	mov rsi, QWORD PTR [rcx+536]
	mov rdi, QWORD PTR [rcx+544]
	mov rbp, QWORD PTR [rcx+552]
	mov r8, QWORD PTR [rcx+560]
	mov r9, QWORD PTR [rcx+568]
	mov r10, rax
	shr r10, 4
	xor r10, rdi
	and r10, r13
	xor rdi, r10
	ror r10, 60
	xor rax, r10
	mov r10, rbx
	shr r10, 4
	xor r10, rbp
	and r10, r13
	xor rbp, r10
	ror r10, 60
	xor rbx, r10
	mov r10, rdx
	shr r10, 4
	xor r10, r8
	and r10, r13
	xor r8, r10
	ror r10, 60
	xor rdx, r10
	mov r10, rsi
	shr r10, 4
	xor r10, r9
	and r10, r13
	xor r9, r10
	ror r10, 60
	xor rsi, r10
	mov r10, rax
	shr r10, 2
	xor r10, rdx
	and r10, r14
	xor rdx, r10
	ror r10, 62
	xor rax, r10
	mov r10, rbx
	shr r10, 2
	xor r10, rsi
	and r10, r14
	xor rsi, r10
	ror r10, 62
	xor rbx, r10
	mov r10, rdi
	shr r10, 2
	xor r10, r8
	and r10, r14
	xor r8, r10
	ror r10, 62
	xor rdi, r10
	mov r10, rbp
	shr r10, 2
	xor r10, r9
	and r10, r14
	xor r9, r10
	ror r10, 62
	xor rbp, r10
	mov r10, rax
	shr r10, 1
	xor r10, rbx
	and r10, r15
	xor rbx, r10
	ror r10, 63
	xor rax, r10
	mov r10, rdx
	shr r10, 1
	xor r10, rsi
	and r10, r15
	xor rsi, r10
	ror r10, 63
	xor rdx, r10
	mov r10, rdi
	shr r10, 1
	xor r10, rbp
	and r10, r15
	xor rbp, r10
	ror r10, 63
	xor rdi, r10
	mov r10, r8
	shr r10, 1
	xor r10, r9
	and r10, r15
	xor r9, r10
	ror r10, 63
	xor r8, r10
	mov QWORD PTR [rcx+512], rax
	mov QWORD PTR [rcx+520], rbx
	mov QWORD PTR [rcx+528], rdx
	mov QWORD PTR [rcx+536], rsi
	mov QWORD PTR [rcx+544], rdi
	mov QWORD PTR [rcx+552], rbp
	mov QWORD PTR [rcx+560], r8
	mov QWORD PTR [rcx+568], r9
	mov r8, QWORD PTR [rcx+624]
	mov r9, QWORD PTR [rcx+632]
	mov r10, QWORD PTR [rcx+640]
	mov r11, QWORD PTR [rcx+648]
	mov rsi, r9
	mov rdi, rcx
	add rdi, 64
	mov rdx, r11
225:
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [rsi], rax
	add rsi, 8
	add rdi, 8
	sub rdx, 1
	jne 225b
	mov QWORD PTR [rcx+624], r8
	mov QWORD PTR [rcx+632], rsi
	mov rax, r10
	sub rax, r11
	mov QWORD PTR [rcx+640], rax
	jne 215b
	jmp 214f
213:
214:
	mov rbx, QWORD PTR [rcx+576]
	mov rbp, QWORD PTR [rcx+584]
	mov r12, QWORD PTR [rcx+592]
	mov r13, QWORD PTR [rcx+600]
	mov r14, QWORD PTR [rcx+608]
	mov r15, QWORD PTR [rcx+616]
	ret
	.p2align 6
