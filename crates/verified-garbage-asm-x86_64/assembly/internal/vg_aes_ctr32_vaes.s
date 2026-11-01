// The functions of `src/internal/vg_aes_ctr32_vaes.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ctr32_vaes:
	cmp r8, 16
	jb 20f
	movabs rax, 579005069656919567
	vmovq xmm10, rax
	movabs rax, 283686952306183
	vmovq xmm13, rax
	vpunpcklqdq xmm10, xmm10, xmm13
	vinserti128 ymm10, ymm10, xmm10, 1
	movabs rax, 1
	vmovq xmm11, rax
	movabs rax, 2
	vmovq xmm12, rax
	vinserti128 ymm12, ymm12, xmm12, 1
	vmovdqu xmm9, XMMWORD PTR [rdx]
	vpshufb xmm9, xmm9, xmm10
	vpaddd xmm13, xmm9, xmm11
	vinserti128 ymm9, ymm9, xmm13, 1
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
22:
	vpshufb ymm0, ymm9, ymm10
	vpaddd ymm9, ymm9, ymm12
	vpshufb ymm1, ymm9, ymm10
	vpaddd ymm9, ymm9, ymm12
	vpshufb ymm2, ymm9, ymm10
	vpaddd ymm9, ymm9, ymm12
	vpshufb ymm3, ymm9, ymm10
	vpaddd ymm9, ymm9, ymm12
	vpshufb ymm4, ymm9, ymm10
	vpaddd ymm9, ymm9, ymm12
	vpshufb ymm5, ymm9, ymm10
	vpaddd ymm9, ymm9, ymm12
	vpshufb ymm6, ymm9, ymm10
	vpaddd ymm9, ymm9, ymm12
	vpshufb ymm7, ymm9, ymm10
	vpaddd ymm9, ymm9, ymm12
	vbroadcasti128 ymm8, XMMWORD PTR [rdi]
	vpxor ymm0, ymm0, ymm8
	vpxor ymm1, ymm1, ymm8
	vpxor ymm2, ymm2, ymm8
	vpxor ymm3, ymm3, ymm8
	vpxor ymm4, ymm4, ymm8
	vpxor ymm5, ymm5, ymm8
	vpxor ymm6, ymm6, ymm8
	vpxor ymm7, ymm7, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [rdi+16]
	vaesenc ymm0, ymm0, ymm8
	vaesenc ymm1, ymm1, ymm8
	vaesenc ymm2, ymm2, ymm8
	vaesenc ymm3, ymm3, ymm8
	vaesenc ymm4, ymm4, ymm8
	vaesenc ymm5, ymm5, ymm8
	vaesenc ymm6, ymm6, ymm8
	vaesenc ymm7, ymm7, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [rdi+32]
	vaesenc ymm0, ymm0, ymm8
	vaesenc ymm1, ymm1, ymm8
	vaesenc ymm2, ymm2, ymm8
	vaesenc ymm3, ymm3, ymm8
	vaesenc ymm4, ymm4, ymm8
	vaesenc ymm5, ymm5, ymm8
	vaesenc ymm6, ymm6, ymm8
	vaesenc ymm7, ymm7, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [rdi+48]
	vaesenc ymm0, ymm0, ymm8
	vaesenc ymm1, ymm1, ymm8
	vaesenc ymm2, ymm2, ymm8
	vaesenc ymm3, ymm3, ymm8
	vaesenc ymm4, ymm4, ymm8
	vaesenc ymm5, ymm5, ymm8
	vaesenc ymm6, ymm6, ymm8
	vaesenc ymm7, ymm7, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [rdi+64]
	vaesenc ymm0, ymm0, ymm8
	vaesenc ymm1, ymm1, ymm8
	vaesenc ymm2, ymm2, ymm8
	vaesenc ymm3, ymm3, ymm8
	vaesenc ymm4, ymm4, ymm8
	vaesenc ymm5, ymm5, ymm8
	vaesenc ymm6, ymm6, ymm8
	vaesenc ymm7, ymm7, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [rdi+80]
	vaesenc ymm0, ymm0, ymm8
	vaesenc ymm1, ymm1, ymm8
	vaesenc ymm2, ymm2, ymm8
	vaesenc ymm3, ymm3, ymm8
	vaesenc ymm4, ymm4, ymm8
	vaesenc ymm5, ymm5, ymm8
	vaesenc ymm6, ymm6, ymm8
	vaesenc ymm7, ymm7, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [rdi+96]
	vaesenc ymm0, ymm0, ymm8
	vaesenc ymm1, ymm1, ymm8
	vaesenc ymm2, ymm2, ymm8
	vaesenc ymm3, ymm3, ymm8
	vaesenc ymm4, ymm4, ymm8
	vaesenc ymm5, ymm5, ymm8
	vaesenc ymm6, ymm6, ymm8
	vaesenc ymm7, ymm7, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [rdi+112]
	vaesenc ymm0, ymm0, ymm8
	vaesenc ymm1, ymm1, ymm8
	vaesenc ymm2, ymm2, ymm8
	vaesenc ymm3, ymm3, ymm8
	vaesenc ymm4, ymm4, ymm8
	vaesenc ymm5, ymm5, ymm8
	vaesenc ymm6, ymm6, ymm8
	vaesenc ymm7, ymm7, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [rdi+128]
	vaesenc ymm0, ymm0, ymm8
	vaesenc ymm1, ymm1, ymm8
	vaesenc ymm2, ymm2, ymm8
	vaesenc ymm3, ymm3, ymm8
	vaesenc ymm4, ymm4, ymm8
	vaesenc ymm5, ymm5, ymm8
	vaesenc ymm6, ymm6, ymm8
	vaesenc ymm7, ymm7, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [rdi+144]
	vaesenc ymm0, ymm0, ymm8
	vaesenc ymm1, ymm1, ymm8
	vaesenc ymm2, ymm2, ymm8
	vaesenc ymm3, ymm3, ymm8
	vaesenc ymm4, ymm4, ymm8
	vaesenc ymm5, ymm5, ymm8
	vaesenc ymm6, ymm6, ymm8
	vaesenc ymm7, ymm7, ymm8
	cmp rsi, 10
	je 23f
	vbroadcasti128 ymm8, XMMWORD PTR [rdi+160]
	vaesenc ymm0, ymm0, ymm8
	vaesenc ymm1, ymm1, ymm8
	vaesenc ymm2, ymm2, ymm8
	vaesenc ymm3, ymm3, ymm8
	vaesenc ymm4, ymm4, ymm8
	vaesenc ymm5, ymm5, ymm8
	vaesenc ymm6, ymm6, ymm8
	vaesenc ymm7, ymm7, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [rdi+176]
	vaesenc ymm0, ymm0, ymm8
	vaesenc ymm1, ymm1, ymm8
	vaesenc ymm2, ymm2, ymm8
	vaesenc ymm3, ymm3, ymm8
	vaesenc ymm4, ymm4, ymm8
	vaesenc ymm5, ymm5, ymm8
	vaesenc ymm6, ymm6, ymm8
	vaesenc ymm7, ymm7, ymm8
	cmp rsi, 12
	je 25f
	vbroadcasti128 ymm8, XMMWORD PTR [rdi+192]
	vaesenc ymm0, ymm0, ymm8
	vaesenc ymm1, ymm1, ymm8
	vaesenc ymm2, ymm2, ymm8
	vaesenc ymm3, ymm3, ymm8
	vaesenc ymm4, ymm4, ymm8
	vaesenc ymm5, ymm5, ymm8
	vaesenc ymm6, ymm6, ymm8
	vaesenc ymm7, ymm7, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [rdi+208]
	vaesenc ymm0, ymm0, ymm8
	vaesenc ymm1, ymm1, ymm8
	vaesenc ymm2, ymm2, ymm8
	vaesenc ymm3, ymm3, ymm8
	vaesenc ymm4, ymm4, ymm8
	vaesenc ymm5, ymm5, ymm8
	vaesenc ymm6, ymm6, ymm8
	vaesenc ymm7, ymm7, ymm8
	jmp 26f
25:
26:
	jmp 24f
23:
24:
	vbroadcasti128 ymm8, XMMWORD PTR [r10]
	vaesenclast ymm0, ymm0, ymm8
	vaesenclast ymm1, ymm1, ymm8
	vaesenclast ymm2, ymm2, ymm8
	vaesenclast ymm3, ymm3, ymm8
	vaesenclast ymm4, ymm4, ymm8
	vaesenclast ymm5, ymm5, ymm8
	vaesenclast ymm6, ymm6, ymm8
	vaesenclast ymm7, ymm7, ymm8
	vmovdqu ymm8, YMMWORD PTR [rcx]
	vpxor ymm0, ymm0, ymm8
	vmovdqu YMMWORD PTR [rcx], ymm0
	vmovdqu ymm8, YMMWORD PTR [rcx+32]
	vpxor ymm1, ymm1, ymm8
	vmovdqu YMMWORD PTR [rcx+32], ymm1
	vmovdqu ymm8, YMMWORD PTR [rcx+64]
	vpxor ymm2, ymm2, ymm8
	vmovdqu YMMWORD PTR [rcx+64], ymm2
	vmovdqu ymm8, YMMWORD PTR [rcx+96]
	vpxor ymm3, ymm3, ymm8
	vmovdqu YMMWORD PTR [rcx+96], ymm3
	vmovdqu ymm8, YMMWORD PTR [rcx+128]
	vpxor ymm4, ymm4, ymm8
	vmovdqu YMMWORD PTR [rcx+128], ymm4
	vmovdqu ymm8, YMMWORD PTR [rcx+160]
	vpxor ymm5, ymm5, ymm8
	vmovdqu YMMWORD PTR [rcx+160], ymm5
	vmovdqu ymm8, YMMWORD PTR [rcx+192]
	vpxor ymm6, ymm6, ymm8
	vmovdqu YMMWORD PTR [rcx+192], ymm6
	vmovdqu ymm8, YMMWORD PTR [rcx+224]
	vpxor ymm7, ymm7, ymm8
	vmovdqu YMMWORD PTR [rcx+224], ymm7
	add rcx, 256
	sub r8, 16
	cmp r8, 16
	jae 22b
	vzeroupper
	cmp r8, 8
	jb 27f
29:
	movdqa xmm0, xmm9
	pshufb xmm0, xmm10
	paddd xmm9, xmm11
	movdqa xmm1, xmm9
	pshufb xmm1, xmm10
	paddd xmm9, xmm11
	movdqa xmm2, xmm9
	pshufb xmm2, xmm10
	paddd xmm9, xmm11
	movdqa xmm3, xmm9
	pshufb xmm3, xmm10
	paddd xmm9, xmm11
	movdqa xmm4, xmm9
	pshufb xmm4, xmm10
	paddd xmm9, xmm11
	movdqa xmm5, xmm9
	pshufb xmm5, xmm10
	paddd xmm9, xmm11
	movdqa xmm6, xmm9
	pshufb xmm6, xmm10
	paddd xmm9, xmm11
	movdqa xmm7, xmm9
	pshufb xmm7, xmm10
	paddd xmm9, xmm11
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	pxor xmm2, xmm8
	pxor xmm3, xmm8
	pxor xmm4, xmm8
	pxor xmm5, xmm8
	pxor xmm6, xmm8
	pxor xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	cmp rsi, 10
	je 210f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	cmp rsi, 12
	je 212f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	jmp 213f
212:
213:
	jmp 211f
210:
211:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	aesenclast xmm2, xmm8
	aesenclast xmm3, xmm8
	aesenclast xmm4, xmm8
	aesenclast xmm5, xmm8
	aesenclast xmm6, xmm8
	aesenclast xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rcx]
	pxor xmm0, xmm8
	movdqu XMMWORD PTR [rcx], xmm0
	movdqu xmm8, XMMWORD PTR [rcx+16]
	pxor xmm1, xmm8
	movdqu XMMWORD PTR [rcx+16], xmm1
	movdqu xmm8, XMMWORD PTR [rcx+32]
	pxor xmm2, xmm8
	movdqu XMMWORD PTR [rcx+32], xmm2
	movdqu xmm8, XMMWORD PTR [rcx+48]
	pxor xmm3, xmm8
	movdqu XMMWORD PTR [rcx+48], xmm3
	movdqu xmm8, XMMWORD PTR [rcx+64]
	pxor xmm4, xmm8
	movdqu XMMWORD PTR [rcx+64], xmm4
	movdqu xmm8, XMMWORD PTR [rcx+80]
	pxor xmm5, xmm8
	movdqu XMMWORD PTR [rcx+80], xmm5
	movdqu xmm8, XMMWORD PTR [rcx+96]
	pxor xmm6, xmm8
	movdqu XMMWORD PTR [rcx+96], xmm6
	movdqu xmm8, XMMWORD PTR [rcx+112]
	pxor xmm7, xmm8
	movdqu XMMWORD PTR [rcx+112], xmm7
	add rcx, 128
	sub r8, 8
	cmp r8, 8
	jae 29b
	jmp 28f
27:
28:
	test r8, r8
	je 214f
216:
	movdqa xmm0, xmm9
	pshufb xmm0, xmm10
	paddd xmm9, xmm11
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	cmp rsi, 10
	je 217f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 219f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 220f
219:
220:
	jmp 218f
217:
218:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rcx]
	pxor xmm0, xmm8
	movdqu XMMWORD PTR [rcx], xmm0
	add rcx, 16
	sub r8, 1
	jne 216b
	jmp 215f
214:
215:
	pshufb xmm9, xmm10
	movdqu XMMWORD PTR [rdx], xmm9
	jmp 21f
20:
	movabs rax, 579005069656919567
	movq xmm10, rax
	movabs rax, 283686952306183
	movq xmm12, rax
	punpcklqdq xmm10, xmm12
	movabs rax, 1
	movq xmm11, rax
	movdqu xmm9, XMMWORD PTR [rdx]
	pshufb xmm9, xmm10
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	cmp r8, 8
	jb 221f
223:
	movdqa xmm0, xmm9
	pshufb xmm0, xmm10
	paddd xmm9, xmm11
	movdqa xmm1, xmm9
	pshufb xmm1, xmm10
	paddd xmm9, xmm11
	movdqa xmm2, xmm9
	pshufb xmm2, xmm10
	paddd xmm9, xmm11
	movdqa xmm3, xmm9
	pshufb xmm3, xmm10
	paddd xmm9, xmm11
	movdqa xmm4, xmm9
	pshufb xmm4, xmm10
	paddd xmm9, xmm11
	movdqa xmm5, xmm9
	pshufb xmm5, xmm10
	paddd xmm9, xmm11
	movdqa xmm6, xmm9
	pshufb xmm6, xmm10
	paddd xmm9, xmm11
	movdqa xmm7, xmm9
	pshufb xmm7, xmm10
	paddd xmm9, xmm11
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	pxor xmm2, xmm8
	pxor xmm3, xmm8
	pxor xmm4, xmm8
	pxor xmm5, xmm8
	pxor xmm6, xmm8
	pxor xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	cmp rsi, 10
	je 224f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	cmp rsi, 12
	je 226f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	jmp 227f
226:
227:
	jmp 225f
224:
225:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	aesenclast xmm2, xmm8
	aesenclast xmm3, xmm8
	aesenclast xmm4, xmm8
	aesenclast xmm5, xmm8
	aesenclast xmm6, xmm8
	aesenclast xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rcx]
	pxor xmm0, xmm8
	movdqu XMMWORD PTR [rcx], xmm0
	movdqu xmm8, XMMWORD PTR [rcx+16]
	pxor xmm1, xmm8
	movdqu XMMWORD PTR [rcx+16], xmm1
	movdqu xmm8, XMMWORD PTR [rcx+32]
	pxor xmm2, xmm8
	movdqu XMMWORD PTR [rcx+32], xmm2
	movdqu xmm8, XMMWORD PTR [rcx+48]
	pxor xmm3, xmm8
	movdqu XMMWORD PTR [rcx+48], xmm3
	movdqu xmm8, XMMWORD PTR [rcx+64]
	pxor xmm4, xmm8
	movdqu XMMWORD PTR [rcx+64], xmm4
	movdqu xmm8, XMMWORD PTR [rcx+80]
	pxor xmm5, xmm8
	movdqu XMMWORD PTR [rcx+80], xmm5
	movdqu xmm8, XMMWORD PTR [rcx+96]
	pxor xmm6, xmm8
	movdqu XMMWORD PTR [rcx+96], xmm6
	movdqu xmm8, XMMWORD PTR [rcx+112]
	pxor xmm7, xmm8
	movdqu XMMWORD PTR [rcx+112], xmm7
	add rcx, 128
	sub r8, 8
	cmp r8, 8
	jae 223b
	jmp 222f
221:
222:
	test r8, r8
	je 228f
230:
	movdqa xmm0, xmm9
	pshufb xmm0, xmm10
	paddd xmm9, xmm11
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	cmp rsi, 10
	je 231f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 233f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 234f
233:
234:
	jmp 232f
231:
232:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rcx]
	pxor xmm0, xmm8
	movdqu XMMWORD PTR [rcx], xmm0
	add rcx, 16
	sub r8, 1
	jne 230b
	jmp 229f
228:
229:
	pshufb xmm9, xmm10
	movdqu XMMWORD PTR [rdx], xmm9
21:
	ret
	.p2align 6
