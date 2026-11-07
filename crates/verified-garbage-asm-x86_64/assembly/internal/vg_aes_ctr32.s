// The functions of `src/internal/vg_aes_ctr32.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ctr32:
	mov QWORD PTR [r9+384], rbx
	mov QWORD PTR [r9+392], rbp
	mov QWORD PTR [r9+400], r12
	mov QWORD PTR [r9+408], r13
	mov QWORD PTR [r9+416], r14
	mov QWORD PTR [r9+424], r15
	mov rax, QWORD PTR [rdx]
	mov QWORD PTR [r9+432], rax
	mov eax, DWORD PTR [rdx+8]
	mov QWORD PTR [r9+440], rax
	mov eax, DWORD PTR [rdx+12]
	bswap eax
	mov DWORD PTR [r9+448], eax
	add eax, r8d
	bswap eax
	mov DWORD PTR [rdx+12], eax
	mov rdx, rcx
	mov r15, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rdi, rsi
	mov rsi, r9
	add rsi, 1920
20:
	mov rax, QWORD PTR [rdi]
	mov r10, QWORD PTR [rdi+8]
	mov rbx, rax
	mov rcx, rax
	mov rbp, rax
	mov r11, r10
	mov r12, r10
	mov r13, r10
	movabs r14, 4294901760
	mov QWORD PTR [r9+8], r14
	movabs r14, 280375465148160
	mov QWORD PTR [r9+16], r14
	movabs r14, 71777214294589695
	mov QWORD PTR [r9+24], r14
	movabs r14, 6148914691236517205
	mov QWORD PTR [r9+32], r14
	movabs r14, 3689348814741910323
	mov QWORD PTR [r9+40], r14
	movabs r14, 1085102592571150095
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	shr r14, 16
	xor r14, rax
	and r14, QWORD PTR [r9+8]
	xor rax, r14
	ror r14, 48
	xor rax, r14
	mov r14, rbx
	shr r14, 16
	xor r14, rbx
	and r14, QWORD PTR [r9+8]
	xor rbx, r14
	ror r14, 48
	xor rbx, r14
	mov r14, rcx
	shr r14, 16
	xor r14, rcx
	and r14, QWORD PTR [r9+8]
	xor rcx, r14
	ror r14, 48
	xor rcx, r14
	mov r14, rbp
	shr r14, 16
	xor r14, rbp
	and r14, QWORD PTR [r9+8]
	xor rbp, r14
	ror r14, 48
	xor rbp, r14
	mov r14, r10
	shr r14, 16
	xor r14, r10
	and r14, QWORD PTR [r9+8]
	xor r10, r14
	ror r14, 48
	xor r10, r14
	mov r14, r11
	shr r14, 16
	xor r14, r11
	and r14, QWORD PTR [r9+8]
	xor r11, r14
	ror r14, 48
	xor r11, r14
	mov r14, r12
	shr r14, 16
	xor r14, r12
	and r14, QWORD PTR [r9+8]
	xor r12, r14
	ror r14, 48
	xor r12, r14
	mov r14, r13
	shr r14, 16
	xor r14, r13
	and r14, QWORD PTR [r9+8]
	xor r13, r14
	ror r14, 48
	xor r13, r14
	mov r14, rax
	shr r14, 8
	xor r14, rax
	and r14, QWORD PTR [r9+16]
	xor rax, r14
	ror r14, 56
	xor rax, r14
	mov r14, rbx
	shr r14, 8
	xor r14, rbx
	and r14, QWORD PTR [r9+16]
	xor rbx, r14
	ror r14, 56
	xor rbx, r14
	mov r14, rcx
	shr r14, 8
	xor r14, rcx
	and r14, QWORD PTR [r9+16]
	xor rcx, r14
	ror r14, 56
	xor rcx, r14
	mov r14, rbp
	shr r14, 8
	xor r14, rbp
	and r14, QWORD PTR [r9+16]
	xor rbp, r14
	ror r14, 56
	xor rbp, r14
	mov r14, r10
	shr r14, 8
	xor r14, r10
	and r14, QWORD PTR [r9+16]
	xor r10, r14
	ror r14, 56
	xor r10, r14
	mov r14, r11
	shr r14, 8
	xor r14, r11
	and r14, QWORD PTR [r9+16]
	xor r11, r14
	ror r14, 56
	xor r11, r14
	mov r14, r12
	shr r14, 8
	xor r14, r12
	and r14, QWORD PTR [r9+16]
	xor r12, r14
	ror r14, 56
	xor r12, r14
	mov r14, r13
	shr r14, 8
	xor r14, r13
	and r14, QWORD PTR [r9+16]
	xor r13, r14
	ror r14, 56
	xor r13, r14
	mov r14, rax
	shr r14, 8
	xor r14, r10
	and r14, QWORD PTR [r9+24]
	xor r10, r14
	ror r14, 56
	xor rax, r14
	mov r14, rbx
	shr r14, 8
	xor r14, r11
	and r14, QWORD PTR [r9+24]
	xor r11, r14
	ror r14, 56
	xor rbx, r14
	mov r14, rcx
	shr r14, 8
	xor r14, r12
	and r14, QWORD PTR [r9+24]
	xor r12, r14
	ror r14, 56
	xor rcx, r14
	mov r14, rbp
	shr r14, 8
	xor r14, r13
	and r14, QWORD PTR [r9+24]
	xor r13, r14
	ror r14, 56
	xor rbp, r14
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+32]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+32]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+32]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+32]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+40]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+40]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+40]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+40]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+48]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+48]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+48]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+48]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	mov QWORD PTR [rsi], rax
	mov QWORD PTR [rsi+8], rbx
	mov QWORD PTR [rsi+16], rcx
	mov QWORD PTR [rsi+24], rbp
	mov QWORD PTR [rsi+32], r10
	mov QWORD PTR [rsi+40], r11
	mov QWORD PTR [rsi+48], r12
	mov QWORD PTR [rsi+56], r13
	sub rdi, 16
	sub rsi, 64
	sub r15, 1
	jae 20b
	movabs rax, -281470681808896
	movq xmm14, rax
	punpcklqdq xmm14, xmm14
	movdqu XMMWORD PTR [r9+464], xmm14
	movabs rax, -4294967296
	movq xmm14, rax
	punpcklqdq xmm14, xmm14
	movdqu XMMWORD PTR [r9+480], xmm14
	mov rdi, rsi
	add rdi, 64
	test r8, r8
	je 21f
23:
	cmp r8, 5
	jb 24f
	mov rcx, r9
	mov r11, r9
	add r11, 464
	mov rax, QWORD PTR [r9+432]
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqa xmm1, xmm0
	movdqa xmm2, xmm0
	movdqa xmm3, xmm0
	mov eax, DWORD PTR [r9+448]
	add eax, 0
	bswap eax
	ror rax, 32
	xor rax, QWORD PTR [r9+440]
	mov r10d, DWORD PTR [r9+448]
	add r10d, 4
	bswap r10d
	ror r10, 32
	xor r10, QWORD PTR [r9+440]
	movq xmm4, rax
	movq xmm8, r10
	punpcklqdq xmm4, xmm8
	mov eax, DWORD PTR [r9+448]
	add eax, 1
	bswap eax
	ror rax, 32
	xor rax, QWORD PTR [r9+440]
	mov r10d, DWORD PTR [r9+448]
	add r10d, 5
	bswap r10d
	ror r10, 32
	xor r10, QWORD PTR [r9+440]
	movq xmm5, rax
	movq xmm8, r10
	punpcklqdq xmm5, xmm8
	mov eax, DWORD PTR [r9+448]
	add eax, 2
	bswap eax
	ror rax, 32
	xor rax, QWORD PTR [r9+440]
	mov r10d, DWORD PTR [r9+448]
	add r10d, 6
	bswap r10d
	ror r10, 32
	xor r10, QWORD PTR [r9+440]
	movq xmm6, rax
	movq xmm8, r10
	punpcklqdq xmm6, xmm8
	mov eax, DWORD PTR [r9+448]
	add eax, 3
	bswap eax
	ror rax, 32
	xor rax, QWORD PTR [r9+440]
	mov r10d, DWORD PTR [r9+448]
	add r10d, 7
	bswap r10d
	ror r10, 32
	xor r10, QWORD PTR [r9+440]
	movq xmm7, rax
	movq xmm8, r10
	punpcklqdq xmm7, xmm8
	mov eax, DWORD PTR [r9+448]
	add eax, 8
	mov DWORD PTR [r9+448], eax
	movabs rax, 4294901760
	movq xmm8, rax
	punpcklqdq xmm8, xmm8
	movabs rax, 280375465148160
	movq xmm9, rax
	punpcklqdq xmm9, xmm9
	movabs rax, 71777214294589695
	movq xmm10, rax
	punpcklqdq xmm10, xmm10
	movabs rax, 6148914691236517205
	movq xmm11, rax
	punpcklqdq xmm11, xmm11
	movabs rax, 3689348814741910323
	movq xmm12, rax
	punpcklqdq xmm12, xmm12
	movabs rax, 1085102592571150095
	movq xmm13, rax
	punpcklqdq xmm13, xmm13
	movdqa xmm14, xmm0
	psrlq xmm14, 16
	pxor xmm14, xmm0
	pand xmm14, xmm8
	pxor xmm0, xmm14
	psllq xmm14, 16
	pxor xmm0, xmm14
	movdqa xmm14, xmm1
	psrlq xmm14, 16
	pxor xmm14, xmm1
	pand xmm14, xmm8
	pxor xmm1, xmm14
	psllq xmm14, 16
	pxor xmm1, xmm14
	movdqa xmm14, xmm2
	psrlq xmm14, 16
	pxor xmm14, xmm2
	pand xmm14, xmm8
	pxor xmm2, xmm14
	psllq xmm14, 16
	pxor xmm2, xmm14
	movdqa xmm14, xmm3
	psrlq xmm14, 16
	pxor xmm14, xmm3
	pand xmm14, xmm8
	pxor xmm3, xmm14
	psllq xmm14, 16
	pxor xmm3, xmm14
	movdqa xmm14, xmm4
	psrlq xmm14, 16
	pxor xmm14, xmm4
	pand xmm14, xmm8
	pxor xmm4, xmm14
	psllq xmm14, 16
	pxor xmm4, xmm14
	movdqa xmm14, xmm5
	psrlq xmm14, 16
	pxor xmm14, xmm5
	pand xmm14, xmm8
	pxor xmm5, xmm14
	psllq xmm14, 16
	pxor xmm5, xmm14
	movdqa xmm14, xmm6
	psrlq xmm14, 16
	pxor xmm14, xmm6
	pand xmm14, xmm8
	pxor xmm6, xmm14
	psllq xmm14, 16
	pxor xmm6, xmm14
	movdqa xmm14, xmm7
	psrlq xmm14, 16
	pxor xmm14, xmm7
	pand xmm14, xmm8
	pxor xmm7, xmm14
	psllq xmm14, 16
	pxor xmm7, xmm14
	movdqa xmm14, xmm0
	psrlq xmm14, 8
	pxor xmm14, xmm0
	pand xmm14, xmm9
	pxor xmm0, xmm14
	psllq xmm14, 8
	pxor xmm0, xmm14
	movdqa xmm14, xmm1
	psrlq xmm14, 8
	pxor xmm14, xmm1
	pand xmm14, xmm9
	pxor xmm1, xmm14
	psllq xmm14, 8
	pxor xmm1, xmm14
	movdqa xmm14, xmm2
	psrlq xmm14, 8
	pxor xmm14, xmm2
	pand xmm14, xmm9
	pxor xmm2, xmm14
	psllq xmm14, 8
	pxor xmm2, xmm14
	movdqa xmm14, xmm3
	psrlq xmm14, 8
	pxor xmm14, xmm3
	pand xmm14, xmm9
	pxor xmm3, xmm14
	psllq xmm14, 8
	pxor xmm3, xmm14
	movdqa xmm14, xmm4
	psrlq xmm14, 8
	pxor xmm14, xmm4
	pand xmm14, xmm9
	pxor xmm4, xmm14
	psllq xmm14, 8
	pxor xmm4, xmm14
	movdqa xmm14, xmm5
	psrlq xmm14, 8
	pxor xmm14, xmm5
	pand xmm14, xmm9
	pxor xmm5, xmm14
	psllq xmm14, 8
	pxor xmm5, xmm14
	movdqa xmm14, xmm6
	psrlq xmm14, 8
	pxor xmm14, xmm6
	pand xmm14, xmm9
	pxor xmm6, xmm14
	psllq xmm14, 8
	pxor xmm6, xmm14
	movdqa xmm14, xmm7
	psrlq xmm14, 8
	pxor xmm14, xmm7
	pand xmm14, xmm9
	pxor xmm7, xmm14
	psllq xmm14, 8
	pxor xmm7, xmm14
	movdqa xmm14, xmm0
	psrlq xmm14, 8
	pxor xmm14, xmm4
	pand xmm14, xmm10
	pxor xmm4, xmm14
	psllq xmm14, 8
	pxor xmm0, xmm14
	movdqa xmm14, xmm1
	psrlq xmm14, 8
	pxor xmm14, xmm5
	pand xmm14, xmm10
	pxor xmm5, xmm14
	psllq xmm14, 8
	pxor xmm1, xmm14
	movdqa xmm14, xmm2
	psrlq xmm14, 8
	pxor xmm14, xmm6
	pand xmm14, xmm10
	pxor xmm6, xmm14
	psllq xmm14, 8
	pxor xmm2, xmm14
	movdqa xmm14, xmm3
	psrlq xmm14, 8
	pxor xmm14, xmm7
	pand xmm14, xmm10
	pxor xmm7, xmm14
	psllq xmm14, 8
	pxor xmm3, xmm14
	movdqa xmm14, xmm0
	psrlq xmm14, 1
	pxor xmm14, xmm1
	pand xmm14, xmm11
	pxor xmm1, xmm14
	psllq xmm14, 1
	pxor xmm0, xmm14
	movdqa xmm14, xmm2
	psrlq xmm14, 1
	pxor xmm14, xmm3
	pand xmm14, xmm11
	pxor xmm3, xmm14
	psllq xmm14, 1
	pxor xmm2, xmm14
	movdqa xmm14, xmm4
	psrlq xmm14, 1
	pxor xmm14, xmm5
	pand xmm14, xmm11
	pxor xmm5, xmm14
	psllq xmm14, 1
	pxor xmm4, xmm14
	movdqa xmm14, xmm6
	psrlq xmm14, 1
	pxor xmm14, xmm7
	pand xmm14, xmm11
	pxor xmm7, xmm14
	psllq xmm14, 1
	pxor xmm6, xmm14
	movdqa xmm14, xmm0
	psrlq xmm14, 2
	pxor xmm14, xmm2
	pand xmm14, xmm12
	pxor xmm2, xmm14
	psllq xmm14, 2
	pxor xmm0, xmm14
	movdqa xmm14, xmm1
	psrlq xmm14, 2
	pxor xmm14, xmm3
	pand xmm14, xmm12
	pxor xmm3, xmm14
	psllq xmm14, 2
	pxor xmm1, xmm14
	movdqa xmm14, xmm4
	psrlq xmm14, 2
	pxor xmm14, xmm6
	pand xmm14, xmm12
	pxor xmm6, xmm14
	psllq xmm14, 2
	pxor xmm4, xmm14
	movdqa xmm14, xmm5
	psrlq xmm14, 2
	pxor xmm14, xmm7
	pand xmm14, xmm12
	pxor xmm7, xmm14
	psllq xmm14, 2
	pxor xmm5, xmm14
	movdqa xmm14, xmm0
	psrlq xmm14, 4
	pxor xmm14, xmm4
	pand xmm14, xmm13
	pxor xmm4, xmm14
	psllq xmm14, 4
	pxor xmm0, xmm14
	movdqa xmm14, xmm1
	psrlq xmm14, 4
	pxor xmm14, xmm5
	pand xmm14, xmm13
	pxor xmm5, xmm14
	psllq xmm14, 4
	pxor xmm1, xmm14
	movdqa xmm14, xmm2
	psrlq xmm14, 4
	pxor xmm14, xmm6
	pand xmm14, xmm13
	pxor xmm6, xmm14
	psllq xmm14, 4
	pxor xmm2, xmm14
	movdqa xmm14, xmm3
	psrlq xmm14, 4
	pxor xmm14, xmm7
	pand xmm14, xmm13
	pxor xmm7, xmm14
	psllq xmm14, 4
	pxor xmm3, xmm14
	mov rsi, rdi
	movdqu xmm8, XMMWORD PTR [rsi]
	punpcklqdq xmm8, xmm8
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rsi+8]
	punpcklqdq xmm8, xmm8
	pxor xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rsi+16]
	punpcklqdq xmm8, xmm8
	pxor xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [rsi+24]
	punpcklqdq xmm8, xmm8
	pxor xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rsi+32]
	punpcklqdq xmm8, xmm8
	pxor xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [rsi+40]
	punpcklqdq xmm8, xmm8
	pxor xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [rsi+48]
	punpcklqdq xmm8, xmm8
	pxor xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [rsi+56]
	punpcklqdq xmm8, xmm8
	pxor xmm7, xmm8
26:
	add rsi, 64
	movabs rax, -1
	movq xmm15, rax
	punpcklqdq xmm15, xmm15
	movdqa xmm8, xmm4
	pxor xmm8, xmm2
	movdqa xmm9, xmm7
	pxor xmm9, xmm1
	movdqa xmm10, xmm7
	pxor xmm10, xmm4
	movdqa xmm11, xmm7
	pxor xmm11, xmm2
	pxor xmm5, xmm6
	movdqa xmm12, xmm5
	pxor xmm12, xmm0
	pxor xmm4, xmm12
	movdqa xmm13, xmm9
	pxor xmm13, xmm8
	movdqa xmm14, xmm12
	pxor xmm14, xmm7
	pxor xmm1, xmm12
	movdqu XMMWORD PTR [rcx], xmm8
	movdqa xmm8, xmm1
	pxor xmm8, xmm11
	pxor xmm3, xmm13
	pxor xmm2, xmm3
	pxor xmm3, xmm6
	movdqa xmm6, xmm2
	pxor xmm6, xmm0
	movdqu XMMWORD PTR [rcx+16], xmm14
	movdqa xmm14, xmm2
	pxor xmm14, xmm5
	movdqu XMMWORD PTR [rcx+32], xmm1
	movdqa xmm1, xmm3
	pxor xmm1, xmm10
	movdqu XMMWORD PTR [rcx+48], xmm3
	movdqa xmm3, xmm0
	pxor xmm3, xmm1
	movdqu XMMWORD PTR [rcx+64], xmm10
	movdqa xmm10, xmm14
	pxor xmm10, xmm1
	movdqu XMMWORD PTR [rcx+80], xmm10
	movdqa xmm10, xmm14
	pxor xmm10, xmm11
	pxor xmm5, xmm1
	movdqu XMMWORD PTR [rcx+96], xmm10
	movdqa xmm10, xmm9
	pxor xmm10, xmm5
	pxor xmm7, xmm5
	movdqu XMMWORD PTR [rcx+112], xmm7
	movdqa xmm7, xmm13
	pand xmm7, xmm2
	movdqu XMMWORD PTR [rcx+128], xmm13
	movdqa xmm13, xmm8
	pand xmm13, xmm6
	pxor xmm13, xmm7
	movdqu XMMWORD PTR [rcx+144], xmm8
	movdqa xmm8, xmm4
	pand xmm8, xmm0
	pxor xmm8, xmm7
	movdqa xmm7, xmm9
	pand xmm7, xmm5
	movdqu XMMWORD PTR [rcx+160], xmm9
	movdqu xmm9, XMMWORD PTR [rcx+32]
	movdqu XMMWORD PTR [rcx+176], xmm4
	movdqa xmm4, xmm9
	pand xmm4, xmm12
	pxor xmm4, xmm7
	movdqu xmm9, XMMWORD PTR [rcx+16]
	movdqu XMMWORD PTR [rcx+192], xmm12
	movdqa xmm12, xmm9
	pand xmm12, xmm3
	pxor xmm12, xmm7
	movdqu xmm7, XMMWORD PTR [rcx+64]
	movdqa xmm9, xmm7
	pand xmm9, xmm1
	movdqu xmm7, XMMWORD PTR [rcx]
	movdqu XMMWORD PTR [rcx+208], xmm1
	movdqu xmm1, XMMWORD PTR [rcx+80]
	movdqu XMMWORD PTR [rcx+224], xmm3
	movdqa xmm3, xmm7
	pand xmm3, xmm1
	pxor xmm3, xmm9
	movdqa xmm7, xmm11
	pand xmm7, xmm14
	pxor xmm7, xmm9
	pxor xmm13, xmm3
	pxor xmm8, xmm7
	pxor xmm4, xmm3
	pxor xmm12, xmm7
	movdqu xmm7, XMMWORD PTR [rcx+48]
	pxor xmm13, xmm7
	movdqu xmm7, XMMWORD PTR [rcx+96]
	pxor xmm8, xmm7
	pxor xmm4, xmm10
	movdqu xmm10, XMMWORD PTR [rcx+112]
	pxor xmm12, xmm10
	movdqa xmm10, xmm13
	pxor xmm10, xmm8
	pand xmm13, xmm4
	movdqa xmm7, xmm12
	pxor xmm7, xmm13
	movdqa xmm3, xmm10
	pand xmm3, xmm7
	pxor xmm3, xmm8
	movdqa xmm9, xmm4
	pxor xmm9, xmm12
	pxor xmm8, xmm13
	pand xmm8, xmm9
	pxor xmm8, xmm12
	pxor xmm4, xmm8
	movdqa xmm9, xmm7
	pxor xmm9, xmm8
	pand xmm12, xmm9
	pxor xmm4, xmm12
	pxor xmm7, xmm12
	pand xmm7, xmm3
	pxor xmm10, xmm7
	movdqa xmm7, xmm10
	pxor xmm7, xmm4
	movdqa xmm12, xmm3
	pxor xmm12, xmm8
	movdqa xmm9, xmm3
	pxor xmm9, xmm10
	movdqa xmm13, xmm8
	pxor xmm13, xmm4
	movdqu XMMWORD PTR [rcx+112], xmm11
	movdqa xmm11, xmm12
	pxor xmm11, xmm7
	pand xmm2, xmm13
	pand xmm6, xmm4
	pand xmm0, xmm8
	pand xmm5, xmm9
	movdqu XMMWORD PTR [rcx+96], xmm6
	movdqu xmm6, XMMWORD PTR [rcx+192]
	pand xmm6, xmm10
	movdqu XMMWORD PTR [rcx+192], xmm6
	movdqu xmm6, XMMWORD PTR [rcx+224]
	pand xmm6, xmm3
	movdqu XMMWORD PTR [rcx+224], xmm5
	movdqu xmm5, XMMWORD PTR [rcx+208]
	pand xmm5, xmm12
	pand xmm1, xmm11
	pand xmm14, xmm7
	movdqu XMMWORD PTR [rcx+80], xmm5
	movdqu xmm5, XMMWORD PTR [rcx+128]
	pand xmm13, xmm5
	movdqu xmm5, XMMWORD PTR [rcx+144]
	pand xmm4, xmm5
	movdqu xmm5, XMMWORD PTR [rcx+176]
	pand xmm8, xmm5
	movdqu xmm5, XMMWORD PTR [rcx+160]
	pand xmm9, xmm5
	movdqu xmm5, XMMWORD PTR [rcx+32]
	pand xmm10, xmm5
	movdqu xmm5, XMMWORD PTR [rcx+16]
	pand xmm3, xmm5
	movdqu xmm5, XMMWORD PTR [rcx+64]
	pand xmm12, xmm5
	movdqu xmm5, XMMWORD PTR [rcx]
	pand xmm11, xmm5
	movdqu xmm5, XMMWORD PTR [rcx+112]
	pand xmm7, xmm5
	pxor xmm12, xmm11
	pxor xmm8, xmm4
	pxor xmm10, xmm6
	pxor xmm13, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm9
	pxor xmm0, xmm6
	pxor xmm14, xmm1
	movdqu xmm6, XMMWORD PTR [rcx+224]
	pxor xmm2, xmm6
	movdqu xmm5, XMMWORD PTR [rcx+80]
	pxor xmm5, xmm1
	pxor xmm11, xmm7
	pxor xmm9, xmm10
	pxor xmm4, xmm2
	movdqu xmm7, XMMWORD PTR [rcx+192]
	movdqa xmm1, xmm7
	pxor xmm1, xmm12
	pxor xmm6, xmm5
	pxor xmm12, xmm4
	pxor xmm3, xmm4
	pxor xmm14, xmm1
	pxor xmm13, xmm1
	pxor xmm7, xmm6
	pxor xmm3, xmm14
	movdqu xmm1, XMMWORD PTR [rcx+96]
	pxor xmm1, xmm13
	pxor xmm6, xmm13
	pxor xmm9, xmm14
	pxor xmm9, xmm15
	pxor xmm10, xmm12
	pxor xmm10, xmm15
	movdqa xmm12, xmm7
	pxor xmm12, xmm3
	pxor xmm2, xmm1
	pxor xmm0, xmm1
	pxor xmm8, xmm3
	pxor xmm7, xmm2
	pxor xmm7, xmm15
	pxor xmm11, xmm12
	pxor xmm11, xmm15
	movdqu XMMWORD PTR [rcx+96], xmm7
	movdqa xmm7, xmm6
	movdqu xmm6, XMMWORD PTR [rcx+96]
	movdqa xmm5, xmm11
	movdqa xmm4, xmm2
	movdqa xmm3, xmm0
	movdqa xmm2, xmm8
	movdqa xmm1, xmm9
	movdqa xmm0, xmm10
	movdqu xmm8, XMMWORD PTR [r11]
	movdqu xmm9, XMMWORD PTR [r11+16]
	movdqa xmm14, xmm0
	psrlw xmm14, 4
	movdqa xmm15, xmm0
	psllw xmm15, 12
	pxor xmm14, xmm15
	pxor xmm14, xmm0
	pand xmm14, xmm8
	pxor xmm0, xmm14
	movdqa xmm14, xmm0
	psrlw xmm14, 8
	movdqa xmm15, xmm0
	psllw xmm15, 8
	pxor xmm14, xmm15
	pxor xmm14, xmm0
	pand xmm14, xmm9
	pxor xmm0, xmm14
	movdqa xmm14, xmm1
	psrlw xmm14, 4
	movdqa xmm15, xmm1
	psllw xmm15, 12
	pxor xmm14, xmm15
	pxor xmm14, xmm1
	pand xmm14, xmm8
	pxor xmm1, xmm14
	movdqa xmm14, xmm1
	psrlw xmm14, 8
	movdqa xmm15, xmm1
	psllw xmm15, 8
	pxor xmm14, xmm15
	pxor xmm14, xmm1
	pand xmm14, xmm9
	pxor xmm1, xmm14
	movdqa xmm14, xmm2
	psrlw xmm14, 4
	movdqa xmm15, xmm2
	psllw xmm15, 12
	pxor xmm14, xmm15
	pxor xmm14, xmm2
	pand xmm14, xmm8
	pxor xmm2, xmm14
	movdqa xmm14, xmm2
	psrlw xmm14, 8
	movdqa xmm15, xmm2
	psllw xmm15, 8
	pxor xmm14, xmm15
	pxor xmm14, xmm2
	pand xmm14, xmm9
	pxor xmm2, xmm14
	movdqa xmm14, xmm3
	psrlw xmm14, 4
	movdqa xmm15, xmm3
	psllw xmm15, 12
	pxor xmm14, xmm15
	pxor xmm14, xmm3
	pand xmm14, xmm8
	pxor xmm3, xmm14
	movdqa xmm14, xmm3
	psrlw xmm14, 8
	movdqa xmm15, xmm3
	psllw xmm15, 8
	pxor xmm14, xmm15
	pxor xmm14, xmm3
	pand xmm14, xmm9
	pxor xmm3, xmm14
	movdqa xmm14, xmm4
	psrlw xmm14, 4
	movdqa xmm15, xmm4
	psllw xmm15, 12
	pxor xmm14, xmm15
	pxor xmm14, xmm4
	pand xmm14, xmm8
	pxor xmm4, xmm14
	movdqa xmm14, xmm4
	psrlw xmm14, 8
	movdqa xmm15, xmm4
	psllw xmm15, 8
	pxor xmm14, xmm15
	pxor xmm14, xmm4
	pand xmm14, xmm9
	pxor xmm4, xmm14
	movdqa xmm14, xmm5
	psrlw xmm14, 4
	movdqa xmm15, xmm5
	psllw xmm15, 12
	pxor xmm14, xmm15
	pxor xmm14, xmm5
	pand xmm14, xmm8
	pxor xmm5, xmm14
	movdqa xmm14, xmm5
	psrlw xmm14, 8
	movdqa xmm15, xmm5
	psllw xmm15, 8
	pxor xmm14, xmm15
	pxor xmm14, xmm5
	pand xmm14, xmm9
	pxor xmm5, xmm14
	movdqa xmm14, xmm6
	psrlw xmm14, 4
	movdqa xmm15, xmm6
	psllw xmm15, 12
	pxor xmm14, xmm15
	pxor xmm14, xmm6
	pand xmm14, xmm8
	pxor xmm6, xmm14
	movdqa xmm14, xmm6
	psrlw xmm14, 8
	movdqa xmm15, xmm6
	psllw xmm15, 8
	pxor xmm14, xmm15
	pxor xmm14, xmm6
	pand xmm14, xmm9
	pxor xmm6, xmm14
	movdqa xmm14, xmm7
	psrlw xmm14, 4
	movdqa xmm15, xmm7
	psllw xmm15, 12
	pxor xmm14, xmm15
	pxor xmm14, xmm7
	pand xmm14, xmm8
	pxor xmm7, xmm14
	movdqa xmm14, xmm7
	psrlw xmm14, 8
	movdqa xmm15, xmm7
	psllw xmm15, 8
	pxor xmm14, xmm15
	pxor xmm14, xmm7
	pand xmm14, xmm9
	pxor xmm7, xmm14
	movdqa xmm10, xmm7
	psrlq xmm10, 16
	movdqa xmm8, xmm7
	psllq xmm8, 48
	pxor xmm10, xmm8
	pxor xmm10, xmm7
	movdqa xmm14, xmm0
	psrlq xmm14, 16
	movdqa xmm8, xmm0
	psllq xmm8, 48
	pxor xmm14, xmm8
	pxor xmm0, xmm14
	pxor xmm14, xmm10
	pshufd xmm9, xmm0, 177
	pxor xmm14, xmm9
	movdqa xmm15, xmm1
	psrlq xmm15, 16
	movdqa xmm8, xmm1
	psllq xmm8, 48
	pxor xmm15, xmm8
	pxor xmm1, xmm15
	pxor xmm15, xmm0
	pxor xmm15, xmm10
	pshufd xmm9, xmm1, 177
	pxor xmm15, xmm9
	movdqa xmm0, xmm2
	psrlq xmm0, 16
	movdqa xmm8, xmm2
	psllq xmm8, 48
	pxor xmm0, xmm8
	pxor xmm2, xmm0
	pxor xmm0, xmm1
	pshufd xmm9, xmm2, 177
	pxor xmm0, xmm9
	movdqa xmm1, xmm3
	psrlq xmm1, 16
	movdqa xmm8, xmm3
	psllq xmm8, 48
	pxor xmm1, xmm8
	pxor xmm3, xmm1
	pxor xmm1, xmm2
	pxor xmm1, xmm10
	pshufd xmm9, xmm3, 177
	pxor xmm1, xmm9
	movdqa xmm2, xmm4
	psrlq xmm2, 16
	movdqa xmm8, xmm4
	psllq xmm8, 48
	pxor xmm2, xmm8
	pxor xmm4, xmm2
	pxor xmm2, xmm3
	pxor xmm2, xmm10
	pshufd xmm9, xmm4, 177
	pxor xmm2, xmm9
	movdqa xmm3, xmm5
	psrlq xmm3, 16
	movdqa xmm8, xmm5
	psllq xmm8, 48
	pxor xmm3, xmm8
	pxor xmm5, xmm3
	pxor xmm3, xmm4
	pshufd xmm9, xmm5, 177
	pxor xmm3, xmm9
	movdqa xmm4, xmm6
	psrlq xmm4, 16
	movdqa xmm8, xmm6
	psllq xmm8, 48
	pxor xmm4, xmm8
	pxor xmm6, xmm4
	pxor xmm4, xmm5
	pshufd xmm9, xmm6, 177
	pxor xmm4, xmm9
	movdqa xmm5, xmm7
	psrlq xmm5, 16
	movdqa xmm8, xmm7
	psllq xmm8, 48
	pxor xmm5, xmm8
	pxor xmm7, xmm5
	pxor xmm5, xmm6
	pshufd xmm9, xmm7, 177
	pxor xmm5, xmm9
	movdqa xmm7, xmm5
	movdqa xmm6, xmm4
	movdqa xmm5, xmm3
	movdqa xmm4, xmm2
	movdqa xmm3, xmm1
	movdqa xmm2, xmm0
	movdqa xmm1, xmm15
	movdqa xmm0, xmm14
	movdqu xmm8, XMMWORD PTR [rsi]
	punpcklqdq xmm8, xmm8
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rsi+8]
	punpcklqdq xmm8, xmm8
	pxor xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rsi+16]
	punpcklqdq xmm8, xmm8
	pxor xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [rsi+24]
	punpcklqdq xmm8, xmm8
	pxor xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rsi+32]
	punpcklqdq xmm8, xmm8
	pxor xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [rsi+40]
	punpcklqdq xmm8, xmm8
	pxor xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [rsi+48]
	punpcklqdq xmm8, xmm8
	pxor xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [rsi+56]
	punpcklqdq xmm8, xmm8
	pxor xmm7, xmm8
	mov rax, r9
	add rax, 1856
	cmp rsi, rax
	jne 26b
	add rsi, 64
	movabs rax, -1
	movq xmm15, rax
	punpcklqdq xmm15, xmm15
	movdqa xmm8, xmm4
	pxor xmm8, xmm2
	movdqa xmm9, xmm7
	pxor xmm9, xmm1
	movdqa xmm10, xmm7
	pxor xmm10, xmm4
	movdqa xmm11, xmm7
	pxor xmm11, xmm2
	pxor xmm5, xmm6
	movdqa xmm12, xmm5
	pxor xmm12, xmm0
	pxor xmm4, xmm12
	movdqa xmm13, xmm9
	pxor xmm13, xmm8
	movdqa xmm14, xmm12
	pxor xmm14, xmm7
	pxor xmm1, xmm12
	movdqu XMMWORD PTR [rcx], xmm8
	movdqa xmm8, xmm1
	pxor xmm8, xmm11
	pxor xmm3, xmm13
	pxor xmm2, xmm3
	pxor xmm3, xmm6
	movdqa xmm6, xmm2
	pxor xmm6, xmm0
	movdqu XMMWORD PTR [rcx+16], xmm14
	movdqa xmm14, xmm2
	pxor xmm14, xmm5
	movdqu XMMWORD PTR [rcx+32], xmm1
	movdqa xmm1, xmm3
	pxor xmm1, xmm10
	movdqu XMMWORD PTR [rcx+48], xmm3
	movdqa xmm3, xmm0
	pxor xmm3, xmm1
	movdqu XMMWORD PTR [rcx+64], xmm10
	movdqa xmm10, xmm14
	pxor xmm10, xmm1
	movdqu XMMWORD PTR [rcx+80], xmm10
	movdqa xmm10, xmm14
	pxor xmm10, xmm11
	pxor xmm5, xmm1
	movdqu XMMWORD PTR [rcx+96], xmm10
	movdqa xmm10, xmm9
	pxor xmm10, xmm5
	pxor xmm7, xmm5
	movdqu XMMWORD PTR [rcx+112], xmm7
	movdqa xmm7, xmm13
	pand xmm7, xmm2
	movdqu XMMWORD PTR [rcx+128], xmm13
	movdqa xmm13, xmm8
	pand xmm13, xmm6
	pxor xmm13, xmm7
	movdqu XMMWORD PTR [rcx+144], xmm8
	movdqa xmm8, xmm4
	pand xmm8, xmm0
	pxor xmm8, xmm7
	movdqa xmm7, xmm9
	pand xmm7, xmm5
	movdqu XMMWORD PTR [rcx+160], xmm9
	movdqu xmm9, XMMWORD PTR [rcx+32]
	movdqu XMMWORD PTR [rcx+176], xmm4
	movdqa xmm4, xmm9
	pand xmm4, xmm12
	pxor xmm4, xmm7
	movdqu xmm9, XMMWORD PTR [rcx+16]
	movdqu XMMWORD PTR [rcx+192], xmm12
	movdqa xmm12, xmm9
	pand xmm12, xmm3
	pxor xmm12, xmm7
	movdqu xmm7, XMMWORD PTR [rcx+64]
	movdqa xmm9, xmm7
	pand xmm9, xmm1
	movdqu xmm7, XMMWORD PTR [rcx]
	movdqu XMMWORD PTR [rcx+208], xmm1
	movdqu xmm1, XMMWORD PTR [rcx+80]
	movdqu XMMWORD PTR [rcx+224], xmm3
	movdqa xmm3, xmm7
	pand xmm3, xmm1
	pxor xmm3, xmm9
	movdqa xmm7, xmm11
	pand xmm7, xmm14
	pxor xmm7, xmm9
	pxor xmm13, xmm3
	pxor xmm8, xmm7
	pxor xmm4, xmm3
	pxor xmm12, xmm7
	movdqu xmm7, XMMWORD PTR [rcx+48]
	pxor xmm13, xmm7
	movdqu xmm7, XMMWORD PTR [rcx+96]
	pxor xmm8, xmm7
	pxor xmm4, xmm10
	movdqu xmm10, XMMWORD PTR [rcx+112]
	pxor xmm12, xmm10
	movdqa xmm10, xmm13
	pxor xmm10, xmm8
	pand xmm13, xmm4
	movdqa xmm7, xmm12
	pxor xmm7, xmm13
	movdqa xmm3, xmm10
	pand xmm3, xmm7
	pxor xmm3, xmm8
	movdqa xmm9, xmm4
	pxor xmm9, xmm12
	pxor xmm8, xmm13
	pand xmm8, xmm9
	pxor xmm8, xmm12
	pxor xmm4, xmm8
	movdqa xmm9, xmm7
	pxor xmm9, xmm8
	pand xmm12, xmm9
	pxor xmm4, xmm12
	pxor xmm7, xmm12
	pand xmm7, xmm3
	pxor xmm10, xmm7
	movdqa xmm7, xmm10
	pxor xmm7, xmm4
	movdqa xmm12, xmm3
	pxor xmm12, xmm8
	movdqa xmm9, xmm3
	pxor xmm9, xmm10
	movdqa xmm13, xmm8
	pxor xmm13, xmm4
	movdqu XMMWORD PTR [rcx+112], xmm11
	movdqa xmm11, xmm12
	pxor xmm11, xmm7
	pand xmm2, xmm13
	pand xmm6, xmm4
	pand xmm0, xmm8
	pand xmm5, xmm9
	movdqu XMMWORD PTR [rcx+96], xmm6
	movdqu xmm6, XMMWORD PTR [rcx+192]
	pand xmm6, xmm10
	movdqu XMMWORD PTR [rcx+192], xmm6
	movdqu xmm6, XMMWORD PTR [rcx+224]
	pand xmm6, xmm3
	movdqu XMMWORD PTR [rcx+224], xmm5
	movdqu xmm5, XMMWORD PTR [rcx+208]
	pand xmm5, xmm12
	pand xmm1, xmm11
	pand xmm14, xmm7
	movdqu XMMWORD PTR [rcx+80], xmm5
	movdqu xmm5, XMMWORD PTR [rcx+128]
	pand xmm13, xmm5
	movdqu xmm5, XMMWORD PTR [rcx+144]
	pand xmm4, xmm5
	movdqu xmm5, XMMWORD PTR [rcx+176]
	pand xmm8, xmm5
	movdqu xmm5, XMMWORD PTR [rcx+160]
	pand xmm9, xmm5
	movdqu xmm5, XMMWORD PTR [rcx+32]
	pand xmm10, xmm5
	movdqu xmm5, XMMWORD PTR [rcx+16]
	pand xmm3, xmm5
	movdqu xmm5, XMMWORD PTR [rcx+64]
	pand xmm12, xmm5
	movdqu xmm5, XMMWORD PTR [rcx]
	pand xmm11, xmm5
	movdqu xmm5, XMMWORD PTR [rcx+112]
	pand xmm7, xmm5
	pxor xmm12, xmm11
	pxor xmm8, xmm4
	pxor xmm10, xmm6
	pxor xmm13, xmm4
	movdqa xmm4, xmm0
	pxor xmm4, xmm9
	pxor xmm0, xmm6
	pxor xmm14, xmm1
	movdqu xmm6, XMMWORD PTR [rcx+224]
	pxor xmm2, xmm6
	movdqu xmm5, XMMWORD PTR [rcx+80]
	pxor xmm5, xmm1
	pxor xmm11, xmm7
	pxor xmm9, xmm10
	pxor xmm4, xmm2
	movdqu xmm7, XMMWORD PTR [rcx+192]
	movdqa xmm1, xmm7
	pxor xmm1, xmm12
	pxor xmm6, xmm5
	pxor xmm12, xmm4
	pxor xmm3, xmm4
	pxor xmm14, xmm1
	pxor xmm13, xmm1
	pxor xmm7, xmm6
	pxor xmm3, xmm14
	movdqu xmm1, XMMWORD PTR [rcx+96]
	pxor xmm1, xmm13
	pxor xmm6, xmm13
	pxor xmm9, xmm14
	pxor xmm9, xmm15
	pxor xmm10, xmm12
	pxor xmm10, xmm15
	movdqa xmm12, xmm7
	pxor xmm12, xmm3
	pxor xmm2, xmm1
	pxor xmm0, xmm1
	pxor xmm8, xmm3
	pxor xmm7, xmm2
	pxor xmm7, xmm15
	pxor xmm11, xmm12
	pxor xmm11, xmm15
	movdqu XMMWORD PTR [rcx+96], xmm7
	movdqa xmm7, xmm6
	movdqu xmm6, XMMWORD PTR [rcx+96]
	movdqa xmm5, xmm11
	movdqa xmm4, xmm2
	movdqa xmm3, xmm0
	movdqa xmm2, xmm8
	movdqa xmm1, xmm9
	movdqa xmm0, xmm10
	movdqu xmm8, XMMWORD PTR [r11]
	movdqu xmm9, XMMWORD PTR [r11+16]
	movdqa xmm14, xmm0
	psrlw xmm14, 4
	movdqa xmm15, xmm0
	psllw xmm15, 12
	pxor xmm14, xmm15
	pxor xmm14, xmm0
	pand xmm14, xmm8
	pxor xmm0, xmm14
	movdqa xmm14, xmm0
	psrlw xmm14, 8
	movdqa xmm15, xmm0
	psllw xmm15, 8
	pxor xmm14, xmm15
	pxor xmm14, xmm0
	pand xmm14, xmm9
	pxor xmm0, xmm14
	movdqa xmm14, xmm1
	psrlw xmm14, 4
	movdqa xmm15, xmm1
	psllw xmm15, 12
	pxor xmm14, xmm15
	pxor xmm14, xmm1
	pand xmm14, xmm8
	pxor xmm1, xmm14
	movdqa xmm14, xmm1
	psrlw xmm14, 8
	movdqa xmm15, xmm1
	psllw xmm15, 8
	pxor xmm14, xmm15
	pxor xmm14, xmm1
	pand xmm14, xmm9
	pxor xmm1, xmm14
	movdqa xmm14, xmm2
	psrlw xmm14, 4
	movdqa xmm15, xmm2
	psllw xmm15, 12
	pxor xmm14, xmm15
	pxor xmm14, xmm2
	pand xmm14, xmm8
	pxor xmm2, xmm14
	movdqa xmm14, xmm2
	psrlw xmm14, 8
	movdqa xmm15, xmm2
	psllw xmm15, 8
	pxor xmm14, xmm15
	pxor xmm14, xmm2
	pand xmm14, xmm9
	pxor xmm2, xmm14
	movdqa xmm14, xmm3
	psrlw xmm14, 4
	movdqa xmm15, xmm3
	psllw xmm15, 12
	pxor xmm14, xmm15
	pxor xmm14, xmm3
	pand xmm14, xmm8
	pxor xmm3, xmm14
	movdqa xmm14, xmm3
	psrlw xmm14, 8
	movdqa xmm15, xmm3
	psllw xmm15, 8
	pxor xmm14, xmm15
	pxor xmm14, xmm3
	pand xmm14, xmm9
	pxor xmm3, xmm14
	movdqa xmm14, xmm4
	psrlw xmm14, 4
	movdqa xmm15, xmm4
	psllw xmm15, 12
	pxor xmm14, xmm15
	pxor xmm14, xmm4
	pand xmm14, xmm8
	pxor xmm4, xmm14
	movdqa xmm14, xmm4
	psrlw xmm14, 8
	movdqa xmm15, xmm4
	psllw xmm15, 8
	pxor xmm14, xmm15
	pxor xmm14, xmm4
	pand xmm14, xmm9
	pxor xmm4, xmm14
	movdqa xmm14, xmm5
	psrlw xmm14, 4
	movdqa xmm15, xmm5
	psllw xmm15, 12
	pxor xmm14, xmm15
	pxor xmm14, xmm5
	pand xmm14, xmm8
	pxor xmm5, xmm14
	movdqa xmm14, xmm5
	psrlw xmm14, 8
	movdqa xmm15, xmm5
	psllw xmm15, 8
	pxor xmm14, xmm15
	pxor xmm14, xmm5
	pand xmm14, xmm9
	pxor xmm5, xmm14
	movdqa xmm14, xmm6
	psrlw xmm14, 4
	movdqa xmm15, xmm6
	psllw xmm15, 12
	pxor xmm14, xmm15
	pxor xmm14, xmm6
	pand xmm14, xmm8
	pxor xmm6, xmm14
	movdqa xmm14, xmm6
	psrlw xmm14, 8
	movdqa xmm15, xmm6
	psllw xmm15, 8
	pxor xmm14, xmm15
	pxor xmm14, xmm6
	pand xmm14, xmm9
	pxor xmm6, xmm14
	movdqa xmm14, xmm7
	psrlw xmm14, 4
	movdqa xmm15, xmm7
	psllw xmm15, 12
	pxor xmm14, xmm15
	pxor xmm14, xmm7
	pand xmm14, xmm8
	pxor xmm7, xmm14
	movdqa xmm14, xmm7
	psrlw xmm14, 8
	movdqa xmm15, xmm7
	psllw xmm15, 8
	pxor xmm14, xmm15
	pxor xmm14, xmm7
	pand xmm14, xmm9
	pxor xmm7, xmm14
	movdqu xmm8, XMMWORD PTR [rsi]
	punpcklqdq xmm8, xmm8
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rsi+8]
	punpcklqdq xmm8, xmm8
	pxor xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rsi+16]
	punpcklqdq xmm8, xmm8
	pxor xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [rsi+24]
	punpcklqdq xmm8, xmm8
	pxor xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rsi+32]
	punpcklqdq xmm8, xmm8
	pxor xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [rsi+40]
	punpcklqdq xmm8, xmm8
	pxor xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [rsi+48]
	punpcklqdq xmm8, xmm8
	pxor xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [rsi+56]
	punpcklqdq xmm8, xmm8
	pxor xmm7, xmm8
	movabs rax, 4294901760
	movq xmm8, rax
	punpcklqdq xmm8, xmm8
	movabs rax, 280375465148160
	movq xmm9, rax
	punpcklqdq xmm9, xmm9
	movabs rax, 71777214294589695
	movq xmm10, rax
	punpcklqdq xmm10, xmm10
	movabs rax, 6148914691236517205
	movq xmm11, rax
	punpcklqdq xmm11, xmm11
	movabs rax, 3689348814741910323
	movq xmm12, rax
	punpcklqdq xmm12, xmm12
	movabs rax, 1085102592571150095
	movq xmm13, rax
	punpcklqdq xmm13, xmm13
	movdqa xmm14, xmm0
	psrlq xmm14, 1
	pxor xmm14, xmm1
	pand xmm14, xmm11
	pxor xmm1, xmm14
	psllq xmm14, 1
	pxor xmm0, xmm14
	movdqa xmm14, xmm2
	psrlq xmm14, 1
	pxor xmm14, xmm3
	pand xmm14, xmm11
	pxor xmm3, xmm14
	psllq xmm14, 1
	pxor xmm2, xmm14
	movdqa xmm14, xmm4
	psrlq xmm14, 1
	pxor xmm14, xmm5
	pand xmm14, xmm11
	pxor xmm5, xmm14
	psllq xmm14, 1
	pxor xmm4, xmm14
	movdqa xmm14, xmm6
	psrlq xmm14, 1
	pxor xmm14, xmm7
	pand xmm14, xmm11
	pxor xmm7, xmm14
	psllq xmm14, 1
	pxor xmm6, xmm14
	movdqa xmm14, xmm0
	psrlq xmm14, 2
	pxor xmm14, xmm2
	pand xmm14, xmm12
	pxor xmm2, xmm14
	psllq xmm14, 2
	pxor xmm0, xmm14
	movdqa xmm14, xmm1
	psrlq xmm14, 2
	pxor xmm14, xmm3
	pand xmm14, xmm12
	pxor xmm3, xmm14
	psllq xmm14, 2
	pxor xmm1, xmm14
	movdqa xmm14, xmm4
	psrlq xmm14, 2
	pxor xmm14, xmm6
	pand xmm14, xmm12
	pxor xmm6, xmm14
	psllq xmm14, 2
	pxor xmm4, xmm14
	movdqa xmm14, xmm5
	psrlq xmm14, 2
	pxor xmm14, xmm7
	pand xmm14, xmm12
	pxor xmm7, xmm14
	psllq xmm14, 2
	pxor xmm5, xmm14
	movdqa xmm14, xmm0
	psrlq xmm14, 4
	pxor xmm14, xmm4
	pand xmm14, xmm13
	pxor xmm4, xmm14
	psllq xmm14, 4
	pxor xmm0, xmm14
	movdqa xmm14, xmm1
	psrlq xmm14, 4
	pxor xmm14, xmm5
	pand xmm14, xmm13
	pxor xmm5, xmm14
	psllq xmm14, 4
	pxor xmm1, xmm14
	movdqa xmm14, xmm2
	psrlq xmm14, 4
	pxor xmm14, xmm6
	pand xmm14, xmm13
	pxor xmm6, xmm14
	psllq xmm14, 4
	pxor xmm2, xmm14
	movdqa xmm14, xmm3
	psrlq xmm14, 4
	pxor xmm14, xmm7
	pand xmm14, xmm13
	pxor xmm7, xmm14
	psllq xmm14, 4
	pxor xmm3, xmm14
	movdqa xmm14, xmm0
	psrlq xmm14, 8
	pxor xmm14, xmm4
	pand xmm14, xmm10
	pxor xmm4, xmm14
	psllq xmm14, 8
	pxor xmm0, xmm14
	movdqa xmm14, xmm1
	psrlq xmm14, 8
	pxor xmm14, xmm5
	pand xmm14, xmm10
	pxor xmm5, xmm14
	psllq xmm14, 8
	pxor xmm1, xmm14
	movdqa xmm14, xmm2
	psrlq xmm14, 8
	pxor xmm14, xmm6
	pand xmm14, xmm10
	pxor xmm6, xmm14
	psllq xmm14, 8
	pxor xmm2, xmm14
	movdqa xmm14, xmm3
	psrlq xmm14, 8
	pxor xmm14, xmm7
	pand xmm14, xmm10
	pxor xmm7, xmm14
	psllq xmm14, 8
	pxor xmm3, xmm14
	movdqa xmm14, xmm0
	psrlq xmm14, 8
	pxor xmm14, xmm0
	pand xmm14, xmm9
	pxor xmm0, xmm14
	psllq xmm14, 8
	pxor xmm0, xmm14
	movdqa xmm14, xmm1
	psrlq xmm14, 8
	pxor xmm14, xmm1
	pand xmm14, xmm9
	pxor xmm1, xmm14
	psllq xmm14, 8
	pxor xmm1, xmm14
	movdqa xmm14, xmm2
	psrlq xmm14, 8
	pxor xmm14, xmm2
	pand xmm14, xmm9
	pxor xmm2, xmm14
	psllq xmm14, 8
	pxor xmm2, xmm14
	movdqa xmm14, xmm3
	psrlq xmm14, 8
	pxor xmm14, xmm3
	pand xmm14, xmm9
	pxor xmm3, xmm14
	psllq xmm14, 8
	pxor xmm3, xmm14
	movdqa xmm14, xmm4
	psrlq xmm14, 8
	pxor xmm14, xmm4
	pand xmm14, xmm9
	pxor xmm4, xmm14
	psllq xmm14, 8
	pxor xmm4, xmm14
	movdqa xmm14, xmm5
	psrlq xmm14, 8
	pxor xmm14, xmm5
	pand xmm14, xmm9
	pxor xmm5, xmm14
	psllq xmm14, 8
	pxor xmm5, xmm14
	movdqa xmm14, xmm6
	psrlq xmm14, 8
	pxor xmm14, xmm6
	pand xmm14, xmm9
	pxor xmm6, xmm14
	psllq xmm14, 8
	pxor xmm6, xmm14
	movdqa xmm14, xmm7
	psrlq xmm14, 8
	pxor xmm14, xmm7
	pand xmm14, xmm9
	pxor xmm7, xmm14
	psllq xmm14, 8
	pxor xmm7, xmm14
	movdqa xmm14, xmm0
	psrlq xmm14, 16
	pxor xmm14, xmm0
	pand xmm14, xmm8
	pxor xmm0, xmm14
	psllq xmm14, 16
	pxor xmm0, xmm14
	movdqa xmm14, xmm1
	psrlq xmm14, 16
	pxor xmm14, xmm1
	pand xmm14, xmm8
	pxor xmm1, xmm14
	psllq xmm14, 16
	pxor xmm1, xmm14
	movdqa xmm14, xmm2
	psrlq xmm14, 16
	pxor xmm14, xmm2
	pand xmm14, xmm8
	pxor xmm2, xmm14
	psllq xmm14, 16
	pxor xmm2, xmm14
	movdqa xmm14, xmm3
	psrlq xmm14, 16
	pxor xmm14, xmm3
	pand xmm14, xmm8
	pxor xmm3, xmm14
	psllq xmm14, 16
	pxor xmm3, xmm14
	movdqa xmm14, xmm4
	psrlq xmm14, 16
	pxor xmm14, xmm4
	pand xmm14, xmm8
	pxor xmm4, xmm14
	psllq xmm14, 16
	pxor xmm4, xmm14
	movdqa xmm14, xmm5
	psrlq xmm14, 16
	pxor xmm14, xmm5
	pand xmm14, xmm8
	pxor xmm5, xmm14
	psllq xmm14, 16
	pxor xmm5, xmm14
	movdqa xmm14, xmm6
	psrlq xmm14, 16
	pxor xmm14, xmm6
	pand xmm14, xmm8
	pxor xmm6, xmm14
	psllq xmm14, 16
	pxor xmm6, xmm14
	movdqa xmm14, xmm7
	psrlq xmm14, 16
	pxor xmm14, xmm7
	pand xmm14, xmm8
	pxor xmm7, xmm14
	psllq xmm14, 16
	pxor xmm7, xmm14
	cmp r8, 8
	jae 27f
	movdqa xmm8, xmm0
	punpcklqdq xmm8, xmm4
	movdqu xmm9, XMMWORD PTR [rdx]
	pxor xmm9, xmm8
	movdqu XMMWORD PTR [rdx], xmm9
	movdqa xmm8, xmm1
	punpcklqdq xmm8, xmm5
	movdqu xmm9, XMMWORD PTR [rdx+16]
	pxor xmm9, xmm8
	movdqu XMMWORD PTR [rdx+16], xmm9
	movdqa xmm8, xmm2
	punpcklqdq xmm8, xmm6
	movdqu xmm9, XMMWORD PTR [rdx+32]
	pxor xmm9, xmm8
	movdqu XMMWORD PTR [rdx+32], xmm9
	movdqa xmm8, xmm3
	punpcklqdq xmm8, xmm7
	movdqu xmm9, XMMWORD PTR [rdx+48]
	pxor xmm9, xmm8
	movdqu XMMWORD PTR [rdx+48], xmm9
	movdqa xmm8, xmm0
	punpckhqdq xmm8, xmm4
	movdqu xmm9, XMMWORD PTR [rdx+64]
	pxor xmm9, xmm8
	movdqu XMMWORD PTR [rdx+64], xmm9
	cmp r8, 6
	jae 29f
	jmp 210f
29:
	movdqa xmm8, xmm1
	punpckhqdq xmm8, xmm5
	movdqu xmm9, XMMWORD PTR [rdx+80]
	pxor xmm9, xmm8
	movdqu XMMWORD PTR [rdx+80], xmm9
	cmp r8, 7
	jae 211f
	jmp 212f
211:
	movdqa xmm8, xmm2
	punpckhqdq xmm8, xmm6
	movdqu xmm9, XMMWORD PTR [rdx+96]
	pxor xmm9, xmm8
	movdqu XMMWORD PTR [rdx+96], xmm9
212:
210:
	sub r8, r8
	jmp 28f
27:
	movdqa xmm8, xmm0
	punpcklqdq xmm8, xmm4
	movdqu xmm9, XMMWORD PTR [rdx]
	pxor xmm9, xmm8
	movdqu XMMWORD PTR [rdx], xmm9
	movdqa xmm8, xmm1
	punpcklqdq xmm8, xmm5
	movdqu xmm9, XMMWORD PTR [rdx+16]
	pxor xmm9, xmm8
	movdqu XMMWORD PTR [rdx+16], xmm9
	movdqa xmm8, xmm2
	punpcklqdq xmm8, xmm6
	movdqu xmm9, XMMWORD PTR [rdx+32]
	pxor xmm9, xmm8
	movdqu XMMWORD PTR [rdx+32], xmm9
	movdqa xmm8, xmm3
	punpcklqdq xmm8, xmm7
	movdqu xmm9, XMMWORD PTR [rdx+48]
	pxor xmm9, xmm8
	movdqu XMMWORD PTR [rdx+48], xmm9
	movdqa xmm8, xmm0
	punpckhqdq xmm8, xmm4
	movdqu xmm9, XMMWORD PTR [rdx+64]
	pxor xmm9, xmm8
	movdqu XMMWORD PTR [rdx+64], xmm9
	movdqa xmm8, xmm1
	punpckhqdq xmm8, xmm5
	movdqu xmm9, XMMWORD PTR [rdx+80]
	pxor xmm9, xmm8
	movdqu XMMWORD PTR [rdx+80], xmm9
	movdqa xmm8, xmm2
	punpckhqdq xmm8, xmm6
	movdqu xmm9, XMMWORD PTR [rdx+96]
	pxor xmm9, xmm8
	movdqu XMMWORD PTR [rdx+96], xmm9
	movdqa xmm8, xmm3
	punpckhqdq xmm8, xmm7
	movdqu xmm9, XMMWORD PTR [rdx+112]
	pxor xmm9, xmm8
	movdqu XMMWORD PTR [rdx+112], xmm9
	add rdx, 128
	sub r8, 8
28:
	jmp 25f
24:
	mov rax, QWORD PTR [r9+432]
	mov r14d, DWORD PTR [r9+448]
	add r14d, 0
	bswap r14d
	ror r14, 32
	mov r10, QWORD PTR [r9+440]
	xor r10, r14
	mov rbx, QWORD PTR [r9+432]
	mov r14d, DWORD PTR [r9+448]
	add r14d, 1
	bswap r14d
	ror r14, 32
	mov r11, QWORD PTR [r9+440]
	xor r11, r14
	mov rcx, QWORD PTR [r9+432]
	mov r14d, DWORD PTR [r9+448]
	add r14d, 2
	bswap r14d
	ror r14, 32
	mov r12, QWORD PTR [r9+440]
	xor r12, r14
	mov rbp, QWORD PTR [r9+432]
	mov r14d, DWORD PTR [r9+448]
	add r14d, 3
	bswap r14d
	ror r14, 32
	mov r13, QWORD PTR [r9+440]
	xor r13, r14
	mov r14d, DWORD PTR [r9+448]
	add r14d, 4
	mov DWORD PTR [r9+448], r14d
	movabs r14, 4294901760
	mov QWORD PTR [r9+8], r14
	movabs r14, 280375465148160
	mov QWORD PTR [r9+16], r14
	movabs r14, 71777214294589695
	mov QWORD PTR [r9+24], r14
	movabs r14, 6148914691236517205
	mov QWORD PTR [r9+32], r14
	movabs r14, 3689348814741910323
	mov QWORD PTR [r9+40], r14
	movabs r14, 1085102592571150095
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	shr r14, 16
	xor r14, rax
	and r14, QWORD PTR [r9+8]
	xor rax, r14
	ror r14, 48
	xor rax, r14
	mov r14, rbx
	shr r14, 16
	xor r14, rbx
	and r14, QWORD PTR [r9+8]
	xor rbx, r14
	ror r14, 48
	xor rbx, r14
	mov r14, rcx
	shr r14, 16
	xor r14, rcx
	and r14, QWORD PTR [r9+8]
	xor rcx, r14
	ror r14, 48
	xor rcx, r14
	mov r14, rbp
	shr r14, 16
	xor r14, rbp
	and r14, QWORD PTR [r9+8]
	xor rbp, r14
	ror r14, 48
	xor rbp, r14
	mov r14, r10
	shr r14, 16
	xor r14, r10
	and r14, QWORD PTR [r9+8]
	xor r10, r14
	ror r14, 48
	xor r10, r14
	mov r14, r11
	shr r14, 16
	xor r14, r11
	and r14, QWORD PTR [r9+8]
	xor r11, r14
	ror r14, 48
	xor r11, r14
	mov r14, r12
	shr r14, 16
	xor r14, r12
	and r14, QWORD PTR [r9+8]
	xor r12, r14
	ror r14, 48
	xor r12, r14
	mov r14, r13
	shr r14, 16
	xor r14, r13
	and r14, QWORD PTR [r9+8]
	xor r13, r14
	ror r14, 48
	xor r13, r14
	mov r14, rax
	shr r14, 8
	xor r14, rax
	and r14, QWORD PTR [r9+16]
	xor rax, r14
	ror r14, 56
	xor rax, r14
	mov r14, rbx
	shr r14, 8
	xor r14, rbx
	and r14, QWORD PTR [r9+16]
	xor rbx, r14
	ror r14, 56
	xor rbx, r14
	mov r14, rcx
	shr r14, 8
	xor r14, rcx
	and r14, QWORD PTR [r9+16]
	xor rcx, r14
	ror r14, 56
	xor rcx, r14
	mov r14, rbp
	shr r14, 8
	xor r14, rbp
	and r14, QWORD PTR [r9+16]
	xor rbp, r14
	ror r14, 56
	xor rbp, r14
	mov r14, r10
	shr r14, 8
	xor r14, r10
	and r14, QWORD PTR [r9+16]
	xor r10, r14
	ror r14, 56
	xor r10, r14
	mov r14, r11
	shr r14, 8
	xor r14, r11
	and r14, QWORD PTR [r9+16]
	xor r11, r14
	ror r14, 56
	xor r11, r14
	mov r14, r12
	shr r14, 8
	xor r14, r12
	and r14, QWORD PTR [r9+16]
	xor r12, r14
	ror r14, 56
	xor r12, r14
	mov r14, r13
	shr r14, 8
	xor r14, r13
	and r14, QWORD PTR [r9+16]
	xor r13, r14
	ror r14, 56
	xor r13, r14
	mov r14, rax
	shr r14, 8
	xor r14, r10
	and r14, QWORD PTR [r9+24]
	xor r10, r14
	ror r14, 56
	xor rax, r14
	mov r14, rbx
	shr r14, 8
	xor r14, r11
	and r14, QWORD PTR [r9+24]
	xor r11, r14
	ror r14, 56
	xor rbx, r14
	mov r14, rcx
	shr r14, 8
	xor r14, r12
	and r14, QWORD PTR [r9+24]
	xor r12, r14
	ror r14, 56
	xor rcx, r14
	mov r14, rbp
	shr r14, 8
	xor r14, r13
	and r14, QWORD PTR [r9+24]
	xor r13, r14
	ror r14, 56
	xor rbp, r14
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+32]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+32]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+32]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+32]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+40]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+40]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+40]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+40]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+48]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+48]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+48]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+48]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	mov rsi, rdi
	xor rax, QWORD PTR [rsi]
	xor rbx, QWORD PTR [rsi+8]
	xor rcx, QWORD PTR [rsi+16]
	xor rbp, QWORD PTR [rsi+24]
	xor r10, QWORD PTR [rsi+32]
	xor r11, QWORD PTR [rsi+40]
	xor r12, QWORD PTR [rsi+48]
	xor r13, QWORD PTR [rsi+56]
213:
	add rsi, 64
	movabs r14, -1
	mov QWORD PTR [r9], r14
	mov r14, r10
	xor r14, rcx
	mov r15, r13
	xor r15, rbx
	mov QWORD PTR [r9+8], rbp
	mov rbp, r13
	xor rbp, r10
	mov QWORD PTR [r9+16], rbp
	mov rbp, r13
	xor rbp, rcx
	xor r11, r12
	mov QWORD PTR [r9+24], r12
	mov r12, r11
	xor r12, rax
	xor r10, r12
	mov QWORD PTR [r9+32], r10
	mov r10, r15
	xor r10, r14
	mov QWORD PTR [r9+40], r14
	mov r14, r12
	xor r14, r13
	xor rbx, r12
	mov QWORD PTR [r9+48], r14
	mov r14, rbx
	xor r14, rbp
	mov QWORD PTR [r9+56], rbx
	mov rbx, QWORD PTR [r9+8]
	xor rbx, r10
	xor rcx, rbx
	xor rbx, QWORD PTR [r9+24]
	mov QWORD PTR [r9+24], r12
	mov r12, rcx
	xor r12, rax
	mov QWORD PTR [r9+8], r12
	mov r12, rcx
	xor r12, r11
	mov QWORD PTR [r9+64], r14
	mov r14, rbx
	xor r14, QWORD PTR [r9+16]
	mov QWORD PTR [r9+72], rbx
	mov rbx, rax
	xor rbx, r14
	mov QWORD PTR [r9+80], rbx
	mov rbx, r12
	xor rbx, r14
	mov QWORD PTR [r9+88], rbx
	mov rbx, r12
	xor rbx, rbp
	xor r11, r14
	mov QWORD PTR [r9+96], rbx
	mov rbx, r15
	xor rbx, r11
	xor r13, r11
	mov QWORD PTR [r9+104], r13
	mov r13, r10
	and r13, rcx
	mov QWORD PTR [r9+112], r10
	mov r10, QWORD PTR [r9+64]
	and r10, QWORD PTR [r9+8]
	xor r10, r13
	mov QWORD PTR [r9+120], rcx
	mov rcx, QWORD PTR [r9+32]
	and rcx, rax
	xor rcx, r13
	mov r13, r15
	and r13, r11
	mov QWORD PTR [r9+128], r15
	mov r15, QWORD PTR [r9+56]
	and r15, QWORD PTR [r9+24]
	xor r15, r13
	mov QWORD PTR [r9+136], r11
	mov r11, QWORD PTR [r9+48]
	and r11, QWORD PTR [r9+80]
	xor r11, r13
	mov r13, QWORD PTR [r9+16]
	and r13, r14
	mov QWORD PTR [r9+144], r14
	mov r14, QWORD PTR [r9+40]
	and r14, QWORD PTR [r9+88]
	xor r14, r13
	mov QWORD PTR [r9+152], rax
	mov rax, rbp
	and rax, r12
	xor rax, r13
	xor r10, r14
	xor rcx, rax
	xor r15, r14
	xor r11, rax
	xor r10, QWORD PTR [r9+72]
	xor rcx, QWORD PTR [r9+96]
	xor r15, rbx
	xor r11, QWORD PTR [r9+104]
	mov rbx, r10
	xor rbx, rcx
	and r10, r15
	mov rax, r11
	xor rax, r10
	mov r14, rbx
	and r14, rax
	xor r14, rcx
	mov r13, r15
	xor r13, r11
	xor rcx, r10
	and rcx, r13
	xor rcx, r11
	xor r15, rcx
	mov r13, rax
	xor r13, rcx
	and r11, r13
	xor r15, r11
	xor rax, r11
	and rax, r14
	xor rbx, rax
	mov rax, rbx
	xor rax, r15
	mov r11, r14
	xor r11, rcx
	mov r13, r14
	xor r13, rbx
	mov r10, rcx
	xor r10, r15
	mov QWORD PTR [r9+104], rbp
	mov rbp, r11
	xor rbp, rax
	mov QWORD PTR [r9+96], rax
	mov rax, r10
	and rax, QWORD PTR [r9+120]
	mov QWORD PTR [r9+120], rax
	mov rax, r15
	and rax, QWORD PTR [r9+8]
	mov QWORD PTR [r9+8], rax
	mov rax, rcx
	and rax, QWORD PTR [r9+152]
	mov QWORD PTR [r9+152], rax
	mov rax, r13
	and rax, QWORD PTR [r9+136]
	mov QWORD PTR [r9+136], rax
	mov rax, rbx
	and rax, QWORD PTR [r9+24]
	mov QWORD PTR [r9+24], rax
	mov rax, r14
	and rax, QWORD PTR [r9+80]
	mov QWORD PTR [r9+80], rax
	mov rax, r11
	and rax, QWORD PTR [r9+144]
	mov QWORD PTR [r9+144], rax
	mov rax, rbp
	and rax, QWORD PTR [r9+88]
	and r12, QWORD PTR [r9+96]
	and r10, QWORD PTR [r9+112]
	and r15, QWORD PTR [r9+64]
	and rcx, QWORD PTR [r9+32]
	and r13, QWORD PTR [r9+128]
	and rbx, QWORD PTR [r9+56]
	and r14, QWORD PTR [r9+48]
	and r11, QWORD PTR [r9+16]
	and rbp, QWORD PTR [r9+40]
	mov QWORD PTR [r9+40], r14
	mov r14, QWORD PTR [r9+96]
	and r14, QWORD PTR [r9+104]
	xor r11, rbp
	xor rcx, r15
	xor rbx, QWORD PTR [r9+80]
	xor r10, r15
	mov r15, QWORD PTR [r9+152]
	xor r15, r13
	mov QWORD PTR [r9+104], rcx
	mov rcx, QWORD PTR [r9+152]
	xor rcx, QWORD PTR [r9+80]
	xor r12, rax
	mov QWORD PTR [r9+80], rcx
	mov rcx, QWORD PTR [r9+120]
	xor rcx, QWORD PTR [r9+136]
	xor rax, QWORD PTR [r9+144]
	xor rbp, r14
	xor r13, rbx
	xor r15, rcx
	mov r14, QWORD PTR [r9+24]
	xor r14, r11
	xor rax, QWORD PTR [r9+136]
	xor r11, r15
	xor r15, QWORD PTR [r9+40]
	xor r12, r14
	xor r10, r14
	mov r14, QWORD PTR [r9+24]
	xor r14, rax
	xor r15, r12
	mov QWORD PTR [r9+24], rbp
	mov rbp, QWORD PTR [r9+8]
	xor rbp, r10
	xor rax, r10
	xor r13, r12
	xor r13, QWORD PTR [r9]
	xor rbx, r11
	xor rbx, QWORD PTR [r9]
	mov r11, r14
	xor r11, r15
	xor rcx, rbp
	xor rbp, QWORD PTR [r9+80]
	xor r15, QWORD PTR [r9+104]
	xor r14, rcx
	xor r14, QWORD PTR [r9]
	xor r11, QWORD PTR [r9+24]
	xor r11, QWORD PTR [r9]
	mov QWORD PTR [r9+24], r13
	mov r13, rax
	mov r12, r14
	mov r10, rcx
	mov rcx, r15
	mov QWORD PTR [r9+104], rbx
	mov rbx, QWORD PTR [r9+24]
	mov rax, QWORD PTR [r9+104]
	movabs r14, 281470681808895
	mov QWORD PTR [r9+8], r14
	movabs r14, 1152640029898506240
	mov QWORD PTR [r9+16], r14
	movabs r14, -1152921500580315136
	mov QWORD PTR [r9+24], r14
	movabs r14, 4294967295
	mov QWORD PTR [r9+32], r14
	movabs r14, 71777214277877760
	mov QWORD PTR [r9+40], r14
	movabs r14, -71777218572845056
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	ror r14, 4
	and r14, QWORD PTR [r9+16]
	mov r15, rax
	ror r15, 52
	and r15, QWORD PTR [r9+24]
	and rax, QWORD PTR [r9+8]
	xor rax, r14
	xor rax, r15
	mov r14, rax
	ror r14, 8
	and r14, QWORD PTR [r9+40]
	mov r15, rax
	ror r15, 56
	and r15, QWORD PTR [r9+48]
	and rax, QWORD PTR [r9+32]
	xor rax, r14
	xor rax, r15
	mov r14, rbx
	ror r14, 4
	and r14, QWORD PTR [r9+16]
	mov r15, rbx
	ror r15, 52
	and r15, QWORD PTR [r9+24]
	and rbx, QWORD PTR [r9+8]
	xor rbx, r14
	xor rbx, r15
	mov r14, rbx
	ror r14, 8
	and r14, QWORD PTR [r9+40]
	mov r15, rbx
	ror r15, 56
	and r15, QWORD PTR [r9+48]
	and rbx, QWORD PTR [r9+32]
	xor rbx, r14
	xor rbx, r15
	mov r14, rcx
	ror r14, 4
	and r14, QWORD PTR [r9+16]
	mov r15, rcx
	ror r15, 52
	and r15, QWORD PTR [r9+24]
	and rcx, QWORD PTR [r9+8]
	xor rcx, r14
	xor rcx, r15
	mov r14, rcx
	ror r14, 8
	and r14, QWORD PTR [r9+40]
	mov r15, rcx
	ror r15, 56
	and r15, QWORD PTR [r9+48]
	and rcx, QWORD PTR [r9+32]
	xor rcx, r14
	xor rcx, r15
	mov r14, rbp
	ror r14, 4
	and r14, QWORD PTR [r9+16]
	mov r15, rbp
	ror r15, 52
	and r15, QWORD PTR [r9+24]
	and rbp, QWORD PTR [r9+8]
	xor rbp, r14
	xor rbp, r15
	mov r14, rbp
	ror r14, 8
	and r14, QWORD PTR [r9+40]
	mov r15, rbp
	ror r15, 56
	and r15, QWORD PTR [r9+48]
	and rbp, QWORD PTR [r9+32]
	xor rbp, r14
	xor rbp, r15
	mov r14, r10
	ror r14, 4
	and r14, QWORD PTR [r9+16]
	mov r15, r10
	ror r15, 52
	and r15, QWORD PTR [r9+24]
	and r10, QWORD PTR [r9+8]
	xor r10, r14
	xor r10, r15
	mov r14, r10
	ror r14, 8
	and r14, QWORD PTR [r9+40]
	mov r15, r10
	ror r15, 56
	and r15, QWORD PTR [r9+48]
	and r10, QWORD PTR [r9+32]
	xor r10, r14
	xor r10, r15
	mov r14, r11
	ror r14, 4
	and r14, QWORD PTR [r9+16]
	mov r15, r11
	ror r15, 52
	and r15, QWORD PTR [r9+24]
	and r11, QWORD PTR [r9+8]
	xor r11, r14
	xor r11, r15
	mov r14, r11
	ror r14, 8
	and r14, QWORD PTR [r9+40]
	mov r15, r11
	ror r15, 56
	and r15, QWORD PTR [r9+48]
	and r11, QWORD PTR [r9+32]
	xor r11, r14
	xor r11, r15
	mov r14, r12
	ror r14, 4
	and r14, QWORD PTR [r9+16]
	mov r15, r12
	ror r15, 52
	and r15, QWORD PTR [r9+24]
	and r12, QWORD PTR [r9+8]
	xor r12, r14
	xor r12, r15
	mov r14, r12
	ror r14, 8
	and r14, QWORD PTR [r9+40]
	mov r15, r12
	ror r15, 56
	and r15, QWORD PTR [r9+48]
	and r12, QWORD PTR [r9+32]
	xor r12, r14
	xor r12, r15
	mov r14, r13
	ror r14, 4
	and r14, QWORD PTR [r9+16]
	mov r15, r13
	ror r15, 52
	and r15, QWORD PTR [r9+24]
	and r13, QWORD PTR [r9+8]
	xor r13, r14
	xor r13, r15
	mov r14, r13
	ror r14, 8
	and r14, QWORD PTR [r9+40]
	mov r15, r13
	ror r15, 56
	and r15, QWORD PTR [r9+48]
	and r13, QWORD PTR [r9+32]
	xor r13, r14
	xor r13, r15
	mov r14, r13
	ror r14, 16
	xor r14, r13
	mov QWORD PTR [r9+56], r14
	mov r14, rax
	ror r14, 16
	xor rax, r14
	xor r14, QWORD PTR [r9+56]
	ror rax, 32
	xor r14, rax
	ror rax, 32
	mov r15, rbx
	ror r15, 16
	xor rbx, r15
	xor r15, rax
	xor r15, QWORD PTR [r9+56]
	ror rbx, 32
	xor r15, rbx
	ror rbx, 32
	mov rax, rcx
	ror rax, 16
	xor rcx, rax
	xor rax, rbx
	ror rcx, 32
	xor rax, rcx
	ror rcx, 32
	mov rbx, rbp
	ror rbx, 16
	xor rbp, rbx
	xor rbx, rcx
	xor rbx, QWORD PTR [r9+56]
	ror rbp, 32
	xor rbx, rbp
	ror rbp, 32
	mov rcx, r10
	ror rcx, 16
	xor r10, rcx
	xor rcx, rbp
	xor rcx, QWORD PTR [r9+56]
	ror r10, 32
	xor rcx, r10
	ror r10, 32
	mov rbp, r11
	ror rbp, 16
	xor r11, rbp
	xor rbp, r10
	ror r11, 32
	xor rbp, r11
	ror r11, 32
	mov r10, r12
	ror r10, 16
	xor r12, r10
	xor r10, r11
	ror r12, 32
	xor r10, r12
	ror r12, 32
	mov r11, r13
	ror r11, 16
	xor r13, r11
	xor r11, r12
	ror r13, 32
	xor r11, r13
	ror r13, 32
	mov r13, r11
	mov r12, r10
	mov r11, rbp
	mov r10, rcx
	mov rbp, rbx
	mov rcx, rax
	mov rbx, r15
	mov rax, r14
	xor rax, QWORD PTR [rsi]
	xor rbx, QWORD PTR [rsi+8]
	xor rcx, QWORD PTR [rsi+16]
	xor rbp, QWORD PTR [rsi+24]
	xor r10, QWORD PTR [rsi+32]
	xor r11, QWORD PTR [rsi+40]
	xor r12, QWORD PTR [rsi+48]
	xor r13, QWORD PTR [rsi+56]
	mov r14, r9
	add r14, 1856
	cmp rsi, r14
	jne 213b
	add rsi, 64
	movabs r14, -1
	mov QWORD PTR [r9], r14
	mov r14, r10
	xor r14, rcx
	mov r15, r13
	xor r15, rbx
	mov QWORD PTR [r9+8], rbp
	mov rbp, r13
	xor rbp, r10
	mov QWORD PTR [r9+16], rbp
	mov rbp, r13
	xor rbp, rcx
	xor r11, r12
	mov QWORD PTR [r9+24], r12
	mov r12, r11
	xor r12, rax
	xor r10, r12
	mov QWORD PTR [r9+32], r10
	mov r10, r15
	xor r10, r14
	mov QWORD PTR [r9+40], r14
	mov r14, r12
	xor r14, r13
	xor rbx, r12
	mov QWORD PTR [r9+48], r14
	mov r14, rbx
	xor r14, rbp
	mov QWORD PTR [r9+56], rbx
	mov rbx, QWORD PTR [r9+8]
	xor rbx, r10
	xor rcx, rbx
	xor rbx, QWORD PTR [r9+24]
	mov QWORD PTR [r9+24], r12
	mov r12, rcx
	xor r12, rax
	mov QWORD PTR [r9+8], r12
	mov r12, rcx
	xor r12, r11
	mov QWORD PTR [r9+64], r14
	mov r14, rbx
	xor r14, QWORD PTR [r9+16]
	mov QWORD PTR [r9+72], rbx
	mov rbx, rax
	xor rbx, r14
	mov QWORD PTR [r9+80], rbx
	mov rbx, r12
	xor rbx, r14
	mov QWORD PTR [r9+88], rbx
	mov rbx, r12
	xor rbx, rbp
	xor r11, r14
	mov QWORD PTR [r9+96], rbx
	mov rbx, r15
	xor rbx, r11
	xor r13, r11
	mov QWORD PTR [r9+104], r13
	mov r13, r10
	and r13, rcx
	mov QWORD PTR [r9+112], r10
	mov r10, QWORD PTR [r9+64]
	and r10, QWORD PTR [r9+8]
	xor r10, r13
	mov QWORD PTR [r9+120], rcx
	mov rcx, QWORD PTR [r9+32]
	and rcx, rax
	xor rcx, r13
	mov r13, r15
	and r13, r11
	mov QWORD PTR [r9+128], r15
	mov r15, QWORD PTR [r9+56]
	and r15, QWORD PTR [r9+24]
	xor r15, r13
	mov QWORD PTR [r9+136], r11
	mov r11, QWORD PTR [r9+48]
	and r11, QWORD PTR [r9+80]
	xor r11, r13
	mov r13, QWORD PTR [r9+16]
	and r13, r14
	mov QWORD PTR [r9+144], r14
	mov r14, QWORD PTR [r9+40]
	and r14, QWORD PTR [r9+88]
	xor r14, r13
	mov QWORD PTR [r9+152], rax
	mov rax, rbp
	and rax, r12
	xor rax, r13
	xor r10, r14
	xor rcx, rax
	xor r15, r14
	xor r11, rax
	xor r10, QWORD PTR [r9+72]
	xor rcx, QWORD PTR [r9+96]
	xor r15, rbx
	xor r11, QWORD PTR [r9+104]
	mov rbx, r10
	xor rbx, rcx
	and r10, r15
	mov rax, r11
	xor rax, r10
	mov r14, rbx
	and r14, rax
	xor r14, rcx
	mov r13, r15
	xor r13, r11
	xor rcx, r10
	and rcx, r13
	xor rcx, r11
	xor r15, rcx
	mov r13, rax
	xor r13, rcx
	and r11, r13
	xor r15, r11
	xor rax, r11
	and rax, r14
	xor rbx, rax
	mov rax, rbx
	xor rax, r15
	mov r11, r14
	xor r11, rcx
	mov r13, r14
	xor r13, rbx
	mov r10, rcx
	xor r10, r15
	mov QWORD PTR [r9+104], rbp
	mov rbp, r11
	xor rbp, rax
	mov QWORD PTR [r9+96], rax
	mov rax, r10
	and rax, QWORD PTR [r9+120]
	mov QWORD PTR [r9+120], rax
	mov rax, r15
	and rax, QWORD PTR [r9+8]
	mov QWORD PTR [r9+8], rax
	mov rax, rcx
	and rax, QWORD PTR [r9+152]
	mov QWORD PTR [r9+152], rax
	mov rax, r13
	and rax, QWORD PTR [r9+136]
	mov QWORD PTR [r9+136], rax
	mov rax, rbx
	and rax, QWORD PTR [r9+24]
	mov QWORD PTR [r9+24], rax
	mov rax, r14
	and rax, QWORD PTR [r9+80]
	mov QWORD PTR [r9+80], rax
	mov rax, r11
	and rax, QWORD PTR [r9+144]
	mov QWORD PTR [r9+144], rax
	mov rax, rbp
	and rax, QWORD PTR [r9+88]
	and r12, QWORD PTR [r9+96]
	and r10, QWORD PTR [r9+112]
	and r15, QWORD PTR [r9+64]
	and rcx, QWORD PTR [r9+32]
	and r13, QWORD PTR [r9+128]
	and rbx, QWORD PTR [r9+56]
	and r14, QWORD PTR [r9+48]
	and r11, QWORD PTR [r9+16]
	and rbp, QWORD PTR [r9+40]
	mov QWORD PTR [r9+40], r14
	mov r14, QWORD PTR [r9+96]
	and r14, QWORD PTR [r9+104]
	xor r11, rbp
	xor rcx, r15
	xor rbx, QWORD PTR [r9+80]
	xor r10, r15
	mov r15, QWORD PTR [r9+152]
	xor r15, r13
	mov QWORD PTR [r9+104], rcx
	mov rcx, QWORD PTR [r9+152]
	xor rcx, QWORD PTR [r9+80]
	xor r12, rax
	mov QWORD PTR [r9+80], rcx
	mov rcx, QWORD PTR [r9+120]
	xor rcx, QWORD PTR [r9+136]
	xor rax, QWORD PTR [r9+144]
	xor rbp, r14
	xor r13, rbx
	xor r15, rcx
	mov r14, QWORD PTR [r9+24]
	xor r14, r11
	xor rax, QWORD PTR [r9+136]
	xor r11, r15
	xor r15, QWORD PTR [r9+40]
	xor r12, r14
	xor r10, r14
	mov r14, QWORD PTR [r9+24]
	xor r14, rax
	xor r15, r12
	mov QWORD PTR [r9+24], rbp
	mov rbp, QWORD PTR [r9+8]
	xor rbp, r10
	xor rax, r10
	xor r13, r12
	xor r13, QWORD PTR [r9]
	xor rbx, r11
	xor rbx, QWORD PTR [r9]
	mov r11, r14
	xor r11, r15
	xor rcx, rbp
	xor rbp, QWORD PTR [r9+80]
	xor r15, QWORD PTR [r9+104]
	xor r14, rcx
	xor r14, QWORD PTR [r9]
	xor r11, QWORD PTR [r9+24]
	xor r11, QWORD PTR [r9]
	mov QWORD PTR [r9+24], r13
	mov r13, rax
	mov r12, r14
	mov r10, rcx
	mov rcx, r15
	mov QWORD PTR [r9+104], rbx
	mov rbx, QWORD PTR [r9+24]
	mov rax, QWORD PTR [r9+104]
	movabs r14, 281470681808895
	mov QWORD PTR [r9+8], r14
	movabs r14, 1152640029898506240
	mov QWORD PTR [r9+16], r14
	movabs r14, -1152921500580315136
	mov QWORD PTR [r9+24], r14
	movabs r14, 4294967295
	mov QWORD PTR [r9+32], r14
	movabs r14, 71777214277877760
	mov QWORD PTR [r9+40], r14
	movabs r14, -71777218572845056
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	ror r14, 4
	and r14, QWORD PTR [r9+16]
	mov r15, rax
	ror r15, 52
	and r15, QWORD PTR [r9+24]
	and rax, QWORD PTR [r9+8]
	xor rax, r14
	xor rax, r15
	mov r14, rax
	ror r14, 8
	and r14, QWORD PTR [r9+40]
	mov r15, rax
	ror r15, 56
	and r15, QWORD PTR [r9+48]
	and rax, QWORD PTR [r9+32]
	xor rax, r14
	xor rax, r15
	mov r14, rbx
	ror r14, 4
	and r14, QWORD PTR [r9+16]
	mov r15, rbx
	ror r15, 52
	and r15, QWORD PTR [r9+24]
	and rbx, QWORD PTR [r9+8]
	xor rbx, r14
	xor rbx, r15
	mov r14, rbx
	ror r14, 8
	and r14, QWORD PTR [r9+40]
	mov r15, rbx
	ror r15, 56
	and r15, QWORD PTR [r9+48]
	and rbx, QWORD PTR [r9+32]
	xor rbx, r14
	xor rbx, r15
	mov r14, rcx
	ror r14, 4
	and r14, QWORD PTR [r9+16]
	mov r15, rcx
	ror r15, 52
	and r15, QWORD PTR [r9+24]
	and rcx, QWORD PTR [r9+8]
	xor rcx, r14
	xor rcx, r15
	mov r14, rcx
	ror r14, 8
	and r14, QWORD PTR [r9+40]
	mov r15, rcx
	ror r15, 56
	and r15, QWORD PTR [r9+48]
	and rcx, QWORD PTR [r9+32]
	xor rcx, r14
	xor rcx, r15
	mov r14, rbp
	ror r14, 4
	and r14, QWORD PTR [r9+16]
	mov r15, rbp
	ror r15, 52
	and r15, QWORD PTR [r9+24]
	and rbp, QWORD PTR [r9+8]
	xor rbp, r14
	xor rbp, r15
	mov r14, rbp
	ror r14, 8
	and r14, QWORD PTR [r9+40]
	mov r15, rbp
	ror r15, 56
	and r15, QWORD PTR [r9+48]
	and rbp, QWORD PTR [r9+32]
	xor rbp, r14
	xor rbp, r15
	mov r14, r10
	ror r14, 4
	and r14, QWORD PTR [r9+16]
	mov r15, r10
	ror r15, 52
	and r15, QWORD PTR [r9+24]
	and r10, QWORD PTR [r9+8]
	xor r10, r14
	xor r10, r15
	mov r14, r10
	ror r14, 8
	and r14, QWORD PTR [r9+40]
	mov r15, r10
	ror r15, 56
	and r15, QWORD PTR [r9+48]
	and r10, QWORD PTR [r9+32]
	xor r10, r14
	xor r10, r15
	mov r14, r11
	ror r14, 4
	and r14, QWORD PTR [r9+16]
	mov r15, r11
	ror r15, 52
	and r15, QWORD PTR [r9+24]
	and r11, QWORD PTR [r9+8]
	xor r11, r14
	xor r11, r15
	mov r14, r11
	ror r14, 8
	and r14, QWORD PTR [r9+40]
	mov r15, r11
	ror r15, 56
	and r15, QWORD PTR [r9+48]
	and r11, QWORD PTR [r9+32]
	xor r11, r14
	xor r11, r15
	mov r14, r12
	ror r14, 4
	and r14, QWORD PTR [r9+16]
	mov r15, r12
	ror r15, 52
	and r15, QWORD PTR [r9+24]
	and r12, QWORD PTR [r9+8]
	xor r12, r14
	xor r12, r15
	mov r14, r12
	ror r14, 8
	and r14, QWORD PTR [r9+40]
	mov r15, r12
	ror r15, 56
	and r15, QWORD PTR [r9+48]
	and r12, QWORD PTR [r9+32]
	xor r12, r14
	xor r12, r15
	mov r14, r13
	ror r14, 4
	and r14, QWORD PTR [r9+16]
	mov r15, r13
	ror r15, 52
	and r15, QWORD PTR [r9+24]
	and r13, QWORD PTR [r9+8]
	xor r13, r14
	xor r13, r15
	mov r14, r13
	ror r14, 8
	and r14, QWORD PTR [r9+40]
	mov r15, r13
	ror r15, 56
	and r15, QWORD PTR [r9+48]
	and r13, QWORD PTR [r9+32]
	xor r13, r14
	xor r13, r15
	xor rax, QWORD PTR [rsi]
	xor rbx, QWORD PTR [rsi+8]
	xor rcx, QWORD PTR [rsi+16]
	xor rbp, QWORD PTR [rsi+24]
	xor r10, QWORD PTR [rsi+32]
	xor r11, QWORD PTR [rsi+40]
	xor r12, QWORD PTR [rsi+48]
	xor r13, QWORD PTR [rsi+56]
	movabs r14, 4294901760
	mov QWORD PTR [r9+8], r14
	movabs r14, 280375465148160
	mov QWORD PTR [r9+16], r14
	movabs r14, 71777214294589695
	mov QWORD PTR [r9+24], r14
	movabs r14, 6148914691236517205
	mov QWORD PTR [r9+32], r14
	movabs r14, 3689348814741910323
	mov QWORD PTR [r9+40], r14
	movabs r14, 1085102592571150095
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+32]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+32]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+32]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+32]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+40]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+40]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+40]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+40]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+48]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+48]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+48]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+48]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	mov r14, rax
	shr r14, 8
	xor r14, r10
	and r14, QWORD PTR [r9+24]
	xor r10, r14
	ror r14, 56
	xor rax, r14
	mov r14, rbx
	shr r14, 8
	xor r14, r11
	and r14, QWORD PTR [r9+24]
	xor r11, r14
	ror r14, 56
	xor rbx, r14
	mov r14, rcx
	shr r14, 8
	xor r14, r12
	and r14, QWORD PTR [r9+24]
	xor r12, r14
	ror r14, 56
	xor rcx, r14
	mov r14, rbp
	shr r14, 8
	xor r14, r13
	and r14, QWORD PTR [r9+24]
	xor r13, r14
	ror r14, 56
	xor rbp, r14
	mov r14, rax
	shr r14, 8
	xor r14, rax
	and r14, QWORD PTR [r9+16]
	xor rax, r14
	ror r14, 56
	xor rax, r14
	mov r14, rbx
	shr r14, 8
	xor r14, rbx
	and r14, QWORD PTR [r9+16]
	xor rbx, r14
	ror r14, 56
	xor rbx, r14
	mov r14, rcx
	shr r14, 8
	xor r14, rcx
	and r14, QWORD PTR [r9+16]
	xor rcx, r14
	ror r14, 56
	xor rcx, r14
	mov r14, rbp
	shr r14, 8
	xor r14, rbp
	and r14, QWORD PTR [r9+16]
	xor rbp, r14
	ror r14, 56
	xor rbp, r14
	mov r14, r10
	shr r14, 8
	xor r14, r10
	and r14, QWORD PTR [r9+16]
	xor r10, r14
	ror r14, 56
	xor r10, r14
	mov r14, r11
	shr r14, 8
	xor r14, r11
	and r14, QWORD PTR [r9+16]
	xor r11, r14
	ror r14, 56
	xor r11, r14
	mov r14, r12
	shr r14, 8
	xor r14, r12
	and r14, QWORD PTR [r9+16]
	xor r12, r14
	ror r14, 56
	xor r12, r14
	mov r14, r13
	shr r14, 8
	xor r14, r13
	and r14, QWORD PTR [r9+16]
	xor r13, r14
	ror r14, 56
	xor r13, r14
	mov r14, rax
	shr r14, 16
	xor r14, rax
	and r14, QWORD PTR [r9+8]
	xor rax, r14
	ror r14, 48
	xor rax, r14
	mov r14, rbx
	shr r14, 16
	xor r14, rbx
	and r14, QWORD PTR [r9+8]
	xor rbx, r14
	ror r14, 48
	xor rbx, r14
	mov r14, rcx
	shr r14, 16
	xor r14, rcx
	and r14, QWORD PTR [r9+8]
	xor rcx, r14
	ror r14, 48
	xor rcx, r14
	mov r14, rbp
	shr r14, 16
	xor r14, rbp
	and r14, QWORD PTR [r9+8]
	xor rbp, r14
	ror r14, 48
	xor rbp, r14
	mov r14, r10
	shr r14, 16
	xor r14, r10
	and r14, QWORD PTR [r9+8]
	xor r10, r14
	ror r14, 48
	xor r10, r14
	mov r14, r11
	shr r14, 16
	xor r14, r11
	and r14, QWORD PTR [r9+8]
	xor r11, r14
	ror r14, 48
	xor r11, r14
	mov r14, r12
	shr r14, 16
	xor r14, r12
	and r14, QWORD PTR [r9+8]
	xor r12, r14
	ror r14, 48
	xor r12, r14
	mov r14, r13
	shr r14, 16
	xor r14, r13
	and r14, QWORD PTR [r9+8]
	xor r13, r14
	ror r14, 48
	xor r13, r14
	cmp r8, 4
	jae 214f
	mov r14, QWORD PTR [rdx]
	xor r14, rax
	mov QWORD PTR [rdx], r14
	mov r14, QWORD PTR [rdx+8]
	xor r14, r10
	mov QWORD PTR [rdx+8], r14
	cmp r8, 2
	jae 216f
	jmp 217f
216:
	mov r14, QWORD PTR [rdx+16]
	xor r14, rbx
	mov QWORD PTR [rdx+16], r14
	mov r14, QWORD PTR [rdx+24]
	xor r14, r11
	mov QWORD PTR [rdx+24], r14
	cmp r8, 3
	jae 218f
	jmp 219f
218:
	mov r14, QWORD PTR [rdx+32]
	xor r14, rcx
	mov QWORD PTR [rdx+32], r14
	mov r14, QWORD PTR [rdx+40]
	xor r14, r12
	mov QWORD PTR [rdx+40], r14
219:
217:
	sub r8, r8
	jmp 215f
214:
	mov r14, QWORD PTR [rdx]
	xor r14, rax
	mov QWORD PTR [rdx], r14
	mov r14, QWORD PTR [rdx+8]
	xor r14, r10
	mov QWORD PTR [rdx+8], r14
	mov r14, QWORD PTR [rdx+16]
	xor r14, rbx
	mov QWORD PTR [rdx+16], r14
	mov r14, QWORD PTR [rdx+24]
	xor r14, r11
	mov QWORD PTR [rdx+24], r14
	mov r14, QWORD PTR [rdx+32]
	xor r14, rcx
	mov QWORD PTR [rdx+32], r14
	mov r14, QWORD PTR [rdx+40]
	xor r14, r12
	mov QWORD PTR [rdx+40], r14
	mov r14, QWORD PTR [rdx+48]
	xor r14, rbp
	mov QWORD PTR [rdx+48], r14
	mov r14, QWORD PTR [rdx+56]
	xor r14, r13
	mov QWORD PTR [rdx+56], r14
	add rdx, 64
	sub r8, 4
215:
25:
	jne 23b
	jmp 22f
21:
22:
	mov rbx, QWORD PTR [r9+384]
	mov rbp, QWORD PTR [r9+392]
	mov r12, QWORD PTR [r9+400]
	mov r13, QWORD PTR [r9+408]
	mov r14, QWORD PTR [r9+416]
	mov r15, QWORD PTR [r9+424]
	ret
	.p2align 6
