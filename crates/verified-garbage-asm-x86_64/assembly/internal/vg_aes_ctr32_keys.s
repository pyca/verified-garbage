// The functions of `src/internal/vg_aes_ctr32_keys.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ctr32_keys:
	movabs rax, 6148914691236517205
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqu XMMWORD PTR [r9+144], xmm0
	movabs rax, 3689348814741910323
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqu XMMWORD PTR [r9+160], xmm0
	movabs rax, 1085102592571150095
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqu XMMWORD PTR [r9+176], xmm0
	movabs rax, 71777214294589695
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqu XMMWORD PTR [r9+192], xmm0
	movabs rax, 281470681808895
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqu XMMWORD PTR [r9+208], xmm0
	movabs rax, 4294967295
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqu XMMWORD PTR [r9+224], xmm0
	movabs rax, 71776119077928960
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqu XMMWORD PTR [r9+240], xmm0
	movabs rax, 71777214277877760
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqu XMMWORD PTR [r9+256], xmm0
	movabs rax, -281470681808896
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqu XMMWORD PTR [r9+272], xmm0
	mov r10, rdi
	mov rax, r9
	add rax, 416
	mov rdi, rsi
	shr rdi, 1
20:
	movdqu xmm0, XMMWORD PTR [r10]
	movdqu xmm1, XMMWORD PTR [r10+16]
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	punpckhqdq xmm4, xmm1
	movdqa xmm1, xmm0
	movdqa xmm2, xmm0
	movdqa xmm3, xmm0
	movdqa xmm5, xmm4
	movdqa xmm6, xmm4
	movdqa xmm7, xmm4
	movdqu xmm9, XMMWORD PTR [r9+192]
	movdqa xmm8, xmm0
	psrlq xmm8, 8
	pxor xmm8, xmm4
	pand xmm8, xmm9
	pxor xmm4, xmm8
	psllq xmm8, 8
	pxor xmm0, xmm8
	movdqa xmm8, xmm1
	psrlq xmm8, 8
	pxor xmm8, xmm5
	pand xmm8, xmm9
	pxor xmm5, xmm8
	psllq xmm8, 8
	pxor xmm1, xmm8
	movdqa xmm8, xmm2
	psrlq xmm8, 8
	pxor xmm8, xmm6
	pand xmm8, xmm9
	pxor xmm6, xmm8
	psllq xmm8, 8
	pxor xmm2, xmm8
	movdqa xmm8, xmm3
	psrlq xmm8, 8
	pxor xmm8, xmm7
	pand xmm8, xmm9
	pxor xmm7, xmm8
	psllq xmm8, 8
	pxor xmm3, xmm8
	movdqu xmm9, XMMWORD PTR [r9+208]
	movdqa xmm8, xmm0
	psrlq xmm8, 16
	pxor xmm8, xmm4
	pand xmm8, xmm9
	pxor xmm4, xmm8
	psllq xmm8, 16
	pxor xmm0, xmm8
	movdqa xmm8, xmm1
	psrlq xmm8, 16
	pxor xmm8, xmm5
	pand xmm8, xmm9
	pxor xmm5, xmm8
	psllq xmm8, 16
	pxor xmm1, xmm8
	movdqa xmm8, xmm2
	psrlq xmm8, 16
	pxor xmm8, xmm6
	pand xmm8, xmm9
	pxor xmm6, xmm8
	psllq xmm8, 16
	pxor xmm2, xmm8
	movdqa xmm8, xmm3
	psrlq xmm8, 16
	pxor xmm8, xmm7
	pand xmm8, xmm9
	pxor xmm7, xmm8
	psllq xmm8, 16
	pxor xmm3, xmm8
	movdqu xmm9, XMMWORD PTR [r9+224]
	movdqa xmm8, xmm0
	psrlq xmm8, 32
	pxor xmm8, xmm4
	pand xmm8, xmm9
	pxor xmm4, xmm8
	psllq xmm8, 32
	pxor xmm0, xmm8
	movdqa xmm8, xmm1
	psrlq xmm8, 32
	pxor xmm8, xmm5
	pand xmm8, xmm9
	pxor xmm5, xmm8
	psllq xmm8, 32
	pxor xmm1, xmm8
	movdqa xmm8, xmm2
	psrlq xmm8, 32
	pxor xmm8, xmm6
	pand xmm8, xmm9
	pxor xmm6, xmm8
	psllq xmm8, 32
	pxor xmm2, xmm8
	movdqa xmm8, xmm3
	psrlq xmm8, 32
	pxor xmm8, xmm7
	pand xmm8, xmm9
	pxor xmm7, xmm8
	psllq xmm8, 32
	pxor xmm3, xmm8
	movdqu xmm9, XMMWORD PTR [r9+176]
	movdqa xmm8, xmm0
	psrlq xmm8, 4
	pxor xmm8, xmm4
	pand xmm8, xmm9
	pxor xmm4, xmm8
	psllq xmm8, 4
	pxor xmm0, xmm8
	movdqa xmm8, xmm1
	psrlq xmm8, 4
	pxor xmm8, xmm5
	pand xmm8, xmm9
	pxor xmm5, xmm8
	psllq xmm8, 4
	pxor xmm1, xmm8
	movdqa xmm8, xmm2
	psrlq xmm8, 4
	pxor xmm8, xmm6
	pand xmm8, xmm9
	pxor xmm6, xmm8
	psllq xmm8, 4
	pxor xmm2, xmm8
	movdqa xmm8, xmm3
	psrlq xmm8, 4
	pxor xmm8, xmm7
	pand xmm8, xmm9
	pxor xmm7, xmm8
	psllq xmm8, 4
	pxor xmm3, xmm8
	movdqu xmm9, XMMWORD PTR [r9+160]
	movdqa xmm8, xmm0
	psrlq xmm8, 2
	pxor xmm8, xmm2
	pand xmm8, xmm9
	pxor xmm2, xmm8
	psllq xmm8, 2
	pxor xmm0, xmm8
	movdqa xmm8, xmm1
	psrlq xmm8, 2
	pxor xmm8, xmm3
	pand xmm8, xmm9
	pxor xmm3, xmm8
	psllq xmm8, 2
	pxor xmm1, xmm8
	movdqa xmm8, xmm4
	psrlq xmm8, 2
	pxor xmm8, xmm6
	pand xmm8, xmm9
	pxor xmm6, xmm8
	psllq xmm8, 2
	pxor xmm4, xmm8
	movdqa xmm8, xmm5
	psrlq xmm8, 2
	pxor xmm8, xmm7
	pand xmm8, xmm9
	pxor xmm7, xmm8
	psllq xmm8, 2
	pxor xmm5, xmm8
	movdqu xmm9, XMMWORD PTR [r9+144]
	movdqa xmm8, xmm0
	psrlq xmm8, 1
	pxor xmm8, xmm1
	pand xmm8, xmm9
	pxor xmm1, xmm8
	psllq xmm8, 1
	pxor xmm0, xmm8
	movdqa xmm8, xmm2
	psrlq xmm8, 1
	pxor xmm8, xmm3
	pand xmm8, xmm9
	pxor xmm3, xmm8
	psllq xmm8, 1
	pxor xmm2, xmm8
	movdqa xmm8, xmm4
	psrlq xmm8, 1
	pxor xmm8, xmm5
	pand xmm8, xmm9
	pxor xmm5, xmm8
	psllq xmm8, 1
	pxor xmm4, xmm8
	movdqa xmm8, xmm6
	psrlq xmm8, 1
	pxor xmm8, xmm7
	pand xmm8, xmm9
	pxor xmm7, xmm8
	psllq xmm8, 1
	pxor xmm6, xmm8
	movdqa xmm8, xmm0
	punpcklqdq xmm8, xmm1
	movdqu XMMWORD PTR [rax], xmm8
	movdqa xmm8, xmm2
	punpcklqdq xmm8, xmm3
	movdqu XMMWORD PTR [rax+16], xmm8
	movdqa xmm8, xmm4
	punpcklqdq xmm8, xmm5
	movdqu XMMWORD PTR [rax+32], xmm8
	movdqa xmm8, xmm6
	punpcklqdq xmm8, xmm7
	movdqu XMMWORD PTR [rax+48], xmm8
	movdqu xmm10, XMMWORD PTR [r9+256]
	movdqu xmm11, XMMWORD PTR [r9+272]
	movdqa xmm8, xmm0
	psrlw xmm8, 8
	pxor xmm8, xmm0
	pand xmm8, xmm10
	pxor xmm0, xmm8
	psllw xmm8, 8
	pxor xmm0, xmm8
	movdqa xmm8, xmm0
	psllw xmm8, 4
	movdqa xmm9, xmm0
	psrlw xmm9, 12
	pxor xmm8, xmm9
	pxor xmm8, xmm0
	pand xmm8, xmm11
	pxor xmm0, xmm8
	movdqa xmm8, xmm1
	psrlw xmm8, 8
	pxor xmm8, xmm1
	pand xmm8, xmm10
	pxor xmm1, xmm8
	psllw xmm8, 8
	pxor xmm1, xmm8
	movdqa xmm8, xmm1
	psllw xmm8, 4
	movdqa xmm9, xmm1
	psrlw xmm9, 12
	pxor xmm8, xmm9
	pxor xmm8, xmm1
	pand xmm8, xmm11
	pxor xmm1, xmm8
	movdqa xmm8, xmm2
	psrlw xmm8, 8
	pxor xmm8, xmm2
	pand xmm8, xmm10
	pxor xmm2, xmm8
	psllw xmm8, 8
	pxor xmm2, xmm8
	movdqa xmm8, xmm2
	psllw xmm8, 4
	movdqa xmm9, xmm2
	psrlw xmm9, 12
	pxor xmm8, xmm9
	pxor xmm8, xmm2
	pand xmm8, xmm11
	pxor xmm2, xmm8
	movdqa xmm8, xmm3
	psrlw xmm8, 8
	pxor xmm8, xmm3
	pand xmm8, xmm10
	pxor xmm3, xmm8
	psllw xmm8, 8
	pxor xmm3, xmm8
	movdqa xmm8, xmm3
	psllw xmm8, 4
	movdqa xmm9, xmm3
	psrlw xmm9, 12
	pxor xmm8, xmm9
	pxor xmm8, xmm3
	pand xmm8, xmm11
	pxor xmm3, xmm8
	movdqa xmm8, xmm4
	psrlw xmm8, 8
	pxor xmm8, xmm4
	pand xmm8, xmm10
	pxor xmm4, xmm8
	psllw xmm8, 8
	pxor xmm4, xmm8
	movdqa xmm8, xmm4
	psllw xmm8, 4
	movdqa xmm9, xmm4
	psrlw xmm9, 12
	pxor xmm8, xmm9
	pxor xmm8, xmm4
	pand xmm8, xmm11
	pxor xmm4, xmm8
	movdqa xmm8, xmm5
	psrlw xmm8, 8
	pxor xmm8, xmm5
	pand xmm8, xmm10
	pxor xmm5, xmm8
	psllw xmm8, 8
	pxor xmm5, xmm8
	movdqa xmm8, xmm5
	psllw xmm8, 4
	movdqa xmm9, xmm5
	psrlw xmm9, 12
	pxor xmm8, xmm9
	pxor xmm8, xmm5
	pand xmm8, xmm11
	pxor xmm5, xmm8
	movdqa xmm8, xmm6
	psrlw xmm8, 8
	pxor xmm8, xmm6
	pand xmm8, xmm10
	pxor xmm6, xmm8
	psllw xmm8, 8
	pxor xmm6, xmm8
	movdqa xmm8, xmm6
	psllw xmm8, 4
	movdqa xmm9, xmm6
	psrlw xmm9, 12
	pxor xmm8, xmm9
	pxor xmm8, xmm6
	pand xmm8, xmm11
	pxor xmm6, xmm8
	movdqa xmm8, xmm7
	psrlw xmm8, 8
	pxor xmm8, xmm7
	pand xmm8, xmm10
	pxor xmm7, xmm8
	psllw xmm8, 8
	pxor xmm7, xmm8
	movdqa xmm8, xmm7
	psllw xmm8, 4
	movdqa xmm9, xmm7
	psrlw xmm9, 12
	pxor xmm8, xmm9
	pxor xmm8, xmm7
	pand xmm8, xmm11
	pxor xmm7, xmm8
	punpckhqdq xmm0, xmm1
	movdqu XMMWORD PTR [rax+64], xmm0
	punpckhqdq xmm2, xmm3
	movdqu XMMWORD PTR [rax+80], xmm2
	punpckhqdq xmm4, xmm5
	movdqu XMMWORD PTR [rax+96], xmm4
	punpckhqdq xmm6, xmm7
	movdqu XMMWORD PTR [rax+112], xmm6
	add r10, 32
	add rax, 128
	sub rdi, 1
	jne 20b
	movdqu xmm0, XMMWORD PTR [r10]
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm0
	punpckhqdq xmm4, xmm4
	movdqa xmm1, xmm0
	movdqa xmm2, xmm0
	movdqa xmm3, xmm0
	movdqa xmm5, xmm4
	movdqa xmm6, xmm4
	movdqa xmm7, xmm4
	movdqu xmm9, XMMWORD PTR [r9+192]
	movdqa xmm8, xmm0
	psrlq xmm8, 8
	pxor xmm8, xmm4
	pand xmm8, xmm9
	pxor xmm4, xmm8
	psllq xmm8, 8
	pxor xmm0, xmm8
	movdqa xmm8, xmm1
	psrlq xmm8, 8
	pxor xmm8, xmm5
	pand xmm8, xmm9
	pxor xmm5, xmm8
	psllq xmm8, 8
	pxor xmm1, xmm8
	movdqa xmm8, xmm2
	psrlq xmm8, 8
	pxor xmm8, xmm6
	pand xmm8, xmm9
	pxor xmm6, xmm8
	psllq xmm8, 8
	pxor xmm2, xmm8
	movdqa xmm8, xmm3
	psrlq xmm8, 8
	pxor xmm8, xmm7
	pand xmm8, xmm9
	pxor xmm7, xmm8
	psllq xmm8, 8
	pxor xmm3, xmm8
	movdqu xmm9, XMMWORD PTR [r9+208]
	movdqa xmm8, xmm0
	psrlq xmm8, 16
	pxor xmm8, xmm4
	pand xmm8, xmm9
	pxor xmm4, xmm8
	psllq xmm8, 16
	pxor xmm0, xmm8
	movdqa xmm8, xmm1
	psrlq xmm8, 16
	pxor xmm8, xmm5
	pand xmm8, xmm9
	pxor xmm5, xmm8
	psllq xmm8, 16
	pxor xmm1, xmm8
	movdqa xmm8, xmm2
	psrlq xmm8, 16
	pxor xmm8, xmm6
	pand xmm8, xmm9
	pxor xmm6, xmm8
	psllq xmm8, 16
	pxor xmm2, xmm8
	movdqa xmm8, xmm3
	psrlq xmm8, 16
	pxor xmm8, xmm7
	pand xmm8, xmm9
	pxor xmm7, xmm8
	psllq xmm8, 16
	pxor xmm3, xmm8
	movdqu xmm9, XMMWORD PTR [r9+224]
	movdqa xmm8, xmm0
	psrlq xmm8, 32
	pxor xmm8, xmm4
	pand xmm8, xmm9
	pxor xmm4, xmm8
	psllq xmm8, 32
	pxor xmm0, xmm8
	movdqa xmm8, xmm1
	psrlq xmm8, 32
	pxor xmm8, xmm5
	pand xmm8, xmm9
	pxor xmm5, xmm8
	psllq xmm8, 32
	pxor xmm1, xmm8
	movdqa xmm8, xmm2
	psrlq xmm8, 32
	pxor xmm8, xmm6
	pand xmm8, xmm9
	pxor xmm6, xmm8
	psllq xmm8, 32
	pxor xmm2, xmm8
	movdqa xmm8, xmm3
	psrlq xmm8, 32
	pxor xmm8, xmm7
	pand xmm8, xmm9
	pxor xmm7, xmm8
	psllq xmm8, 32
	pxor xmm3, xmm8
	movdqu xmm9, XMMWORD PTR [r9+176]
	movdqa xmm8, xmm0
	psrlq xmm8, 4
	pxor xmm8, xmm4
	pand xmm8, xmm9
	pxor xmm4, xmm8
	psllq xmm8, 4
	pxor xmm0, xmm8
	movdqa xmm8, xmm1
	psrlq xmm8, 4
	pxor xmm8, xmm5
	pand xmm8, xmm9
	pxor xmm5, xmm8
	psllq xmm8, 4
	pxor xmm1, xmm8
	movdqa xmm8, xmm2
	psrlq xmm8, 4
	pxor xmm8, xmm6
	pand xmm8, xmm9
	pxor xmm6, xmm8
	psllq xmm8, 4
	pxor xmm2, xmm8
	movdqa xmm8, xmm3
	psrlq xmm8, 4
	pxor xmm8, xmm7
	pand xmm8, xmm9
	pxor xmm7, xmm8
	psllq xmm8, 4
	pxor xmm3, xmm8
	movdqu xmm9, XMMWORD PTR [r9+160]
	movdqa xmm8, xmm0
	psrlq xmm8, 2
	pxor xmm8, xmm2
	pand xmm8, xmm9
	pxor xmm2, xmm8
	psllq xmm8, 2
	pxor xmm0, xmm8
	movdqa xmm8, xmm1
	psrlq xmm8, 2
	pxor xmm8, xmm3
	pand xmm8, xmm9
	pxor xmm3, xmm8
	psllq xmm8, 2
	pxor xmm1, xmm8
	movdqa xmm8, xmm4
	psrlq xmm8, 2
	pxor xmm8, xmm6
	pand xmm8, xmm9
	pxor xmm6, xmm8
	psllq xmm8, 2
	pxor xmm4, xmm8
	movdqa xmm8, xmm5
	psrlq xmm8, 2
	pxor xmm8, xmm7
	pand xmm8, xmm9
	pxor xmm7, xmm8
	psllq xmm8, 2
	pxor xmm5, xmm8
	movdqu xmm9, XMMWORD PTR [r9+144]
	movdqa xmm8, xmm0
	psrlq xmm8, 1
	pxor xmm8, xmm1
	pand xmm8, xmm9
	pxor xmm1, xmm8
	psllq xmm8, 1
	pxor xmm0, xmm8
	movdqa xmm8, xmm2
	psrlq xmm8, 1
	pxor xmm8, xmm3
	pand xmm8, xmm9
	pxor xmm3, xmm8
	psllq xmm8, 1
	pxor xmm2, xmm8
	movdqa xmm8, xmm4
	psrlq xmm8, 1
	pxor xmm8, xmm5
	pand xmm8, xmm9
	pxor xmm5, xmm8
	psllq xmm8, 1
	pxor xmm4, xmm8
	movdqa xmm8, xmm6
	psrlq xmm8, 1
	pxor xmm8, xmm7
	pand xmm8, xmm9
	pxor xmm7, xmm8
	psllq xmm8, 1
	pxor xmm6, xmm8
	movdqa xmm8, xmm0
	punpcklqdq xmm8, xmm1
	movdqu XMMWORD PTR [rax], xmm8
	movdqa xmm8, xmm2
	punpcklqdq xmm8, xmm3
	movdqu XMMWORD PTR [rax+16], xmm8
	movdqa xmm8, xmm4
	punpcklqdq xmm8, xmm5
	movdqu XMMWORD PTR [rax+32], xmm8
	movdqa xmm8, xmm6
	punpcklqdq xmm8, xmm7
	movdqu XMMWORD PTR [rax+48], xmm8
	mov rax, r9
	add rax, 480
	mov rdi, rsi
21:
	mov r10, QWORD PTR [rax]
	xor r10, -1
	mov QWORD PTR [rax], r10
	mov r10, QWORD PTR [rax+8]
	xor r10, -1
	mov QWORD PTR [rax+8], r10
	mov r10, QWORD PTR [rax+40]
	xor r10, -1
	mov QWORD PTR [rax+40], r10
	mov r10, QWORD PTR [rax+48]
	xor r10, -1
	mov QWORD PTR [rax+48], r10
	add rax, 64
	sub rdi, 1
	jne 21b
	ret
	.p2align 6
