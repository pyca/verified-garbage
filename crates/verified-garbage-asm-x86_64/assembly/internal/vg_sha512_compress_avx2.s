// The functions of `src/internal/vg_sha512_compress_avx2.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha512_compress_avx2:
	mov QWORD PTR [rcx+1280], rbx
	mov QWORD PTR [rcx+1288], rbp
	mov QWORD PTR [rcx+1296], r12
	mov QWORD PTR [rcx+1304], r13
	vmovq xmm14, r14
	vmovq xmm15, r15
	movabs rax, 283686952306183
	vmovq xmm12, rax
	movabs rax, 579005069656919567
	vmovq xmm13, rax
	vpunpcklqdq xmm12, xmm12, xmm13
	vinserti128 ymm12, ymm12, xmm12, 1
	test rdx, rdx
	je 20f
22:
	mov r15, rsi
	cmp rdx, 1
	je 23f
	add r15, 128
	jmp 24f
23:
24:
	vmovdqu xmm0, XMMWORD PTR [rsi]
	vmovdqu xmm13, XMMWORD PTR [r15]
	vinserti128 ymm0, ymm0, xmm13, 1
	vpshufb ymm0, ymm0, ymm12
	vmovdqu YMMWORD PTR [rcx], ymm0
	vmovdqu xmm1, XMMWORD PTR [rsi+16]
	vmovdqu xmm13, XMMWORD PTR [r15+16]
	vinserti128 ymm1, ymm1, xmm13, 1
	vpshufb ymm1, ymm1, ymm12
	vmovdqu YMMWORD PTR [rcx+32], ymm1
	vmovdqu xmm2, XMMWORD PTR [rsi+32]
	vmovdqu xmm13, XMMWORD PTR [r15+32]
	vinserti128 ymm2, ymm2, xmm13, 1
	vpshufb ymm2, ymm2, ymm12
	vmovdqu YMMWORD PTR [rcx+64], ymm2
	vmovdqu xmm3, XMMWORD PTR [rsi+48]
	vmovdqu xmm13, XMMWORD PTR [r15+48]
	vinserti128 ymm3, ymm3, xmm13, 1
	vpshufb ymm3, ymm3, ymm12
	vmovdqu YMMWORD PTR [rcx+96], ymm3
	vmovdqu xmm4, XMMWORD PTR [rsi+64]
	vmovdqu xmm13, XMMWORD PTR [r15+64]
	vinserti128 ymm4, ymm4, xmm13, 1
	vpshufb ymm4, ymm4, ymm12
	vmovdqu YMMWORD PTR [rcx+128], ymm4
	vmovdqu xmm5, XMMWORD PTR [rsi+80]
	vmovdqu xmm13, XMMWORD PTR [r15+80]
	vinserti128 ymm5, ymm5, xmm13, 1
	vpshufb ymm5, ymm5, ymm12
	vmovdqu YMMWORD PTR [rcx+160], ymm5
	vmovdqu xmm6, XMMWORD PTR [rsi+96]
	vmovdqu xmm13, XMMWORD PTR [r15+96]
	vinserti128 ymm6, ymm6, xmm13, 1
	vpshufb ymm6, ymm6, ymm12
	vmovdqu YMMWORD PTR [rcx+192], ymm6
	vmovdqu xmm7, XMMWORD PTR [rsi+112]
	vmovdqu xmm13, XMMWORD PTR [r15+112]
	vinserti128 ymm7, ymm7, xmm13, 1
	vpshufb ymm7, ymm7, ymm12
	vmovdqu YMMWORD PTR [rcx+224], ymm7
	mov rax, QWORD PTR [rdi]
	mov rbx, QWORD PTR [rdi+8]
	mov rbp, QWORD PTR [rdi+16]
	mov r8, QWORD PTR [rdi+24]
	mov r9, QWORD PTR [rdi+32]
	mov r10, QWORD PTR [rdi+40]
	mov r11, QWORD PTR [rdi+48]
	mov r12, QWORD PTR [rdi+56]
	mov r13, rbx
	xor r13, rbp
	mov QWORD PTR [rcx+1312], rsi
	mov QWORD PTR [rcx+1320], rdx
	lea rsi, {VG_SHA512_K}
	mov rdx, 0
25:
	vpalignr ymm8, ymm1, ymm0, 8
	add r12, QWORD PTR [rsi+rdx*1]
	add r12, QWORD PTR [rcx+rdx*2]
	mov r14, r9
	vpalignr ymm9, ymm5, ymm4, 8
	and r14, r10
	andn r15, r9, r11
	vpaddq ymm0, ymm0, ymm9
	add r14, r15
	add r12, r14
	vpsrlq ymm10, ymm8, 1
	rorx r14, r9, 14
	rorx r15, r9, 18
	vpsllq ymm11, ymm8, 63
	xor r14, r15
	rorx r15, r9, 41
	vpxor ymm10, ymm10, ymm11
	xor r14, r15
	add r12, r14
	vpsrlq ymm11, ymm8, 8
	add r8, r12
	rorx r14, rax, 28
	vpxor ymm10, ymm10, ymm11
	rorx r15, rax, 34
	xor r14, r15
	vpsllq ymm11, ymm8, 56
	rorx r15, rax, 39
	xor r14, r15
	vpxor ymm10, ymm10, ymm11
	add r12, r14
	mov r14, rax
	vpsrlq ymm11, ymm8, 7
	xor r14, rbx
	and r13, r14
	vpxor ymm10, ymm10, ymm11
	xor r13, rbx
	add r12, r13
	vpaddq ymm0, ymm0, ymm10
	add r11, QWORD PTR [rsi+rdx*1+8]
	add r11, QWORD PTR [rcx+rdx*2+8]
	mov r13, r8
	vpsrlq ymm10, ymm7, 19
	and r13, r9
	andn r15, r8, r10
	vpsllq ymm11, ymm7, 45
	add r13, r15
	add r11, r13
	vpxor ymm10, ymm10, ymm11
	rorx r13, r8, 14
	rorx r15, r8, 18
	vpsrlq ymm11, ymm7, 61
	xor r13, r15
	rorx r15, r8, 41
	vpxor ymm10, ymm10, ymm11
	xor r13, r15
	add r11, r13
	vpsllq ymm11, ymm7, 3
	add rbp, r11
	rorx r13, r12, 28
	vpxor ymm10, ymm10, ymm11
	rorx r15, r12, 34
	xor r13, r15
	vpsrlq ymm11, ymm7, 6
	rorx r15, r12, 39
	xor r13, r15
	vpxor ymm10, ymm10, ymm11
	add r11, r13
	mov r13, r12
	vpaddq ymm0, ymm0, ymm10
	xor r13, rax
	and r14, r13
	vmovdqu YMMWORD PTR [rcx+rdx*2+256], ymm0
	xor r14, rax
	add r11, r14
	vpalignr ymm8, ymm2, ymm1, 8
	add r10, QWORD PTR [rsi+rdx*1+16]
	add r10, QWORD PTR [rcx+rdx*2+32]
	mov r14, rbp
	vpalignr ymm9, ymm6, ymm5, 8
	and r14, r8
	andn r15, rbp, r9
	vpaddq ymm1, ymm1, ymm9
	add r14, r15
	add r10, r14
	vpsrlq ymm10, ymm8, 1
	rorx r14, rbp, 14
	rorx r15, rbp, 18
	vpsllq ymm11, ymm8, 63
	xor r14, r15
	rorx r15, rbp, 41
	vpxor ymm10, ymm10, ymm11
	xor r14, r15
	add r10, r14
	vpsrlq ymm11, ymm8, 8
	add rbx, r10
	rorx r14, r11, 28
	vpxor ymm10, ymm10, ymm11
	rorx r15, r11, 34
	xor r14, r15
	vpsllq ymm11, ymm8, 56
	rorx r15, r11, 39
	xor r14, r15
	vpxor ymm10, ymm10, ymm11
	add r10, r14
	mov r14, r11
	vpsrlq ymm11, ymm8, 7
	xor r14, r12
	and r13, r14
	vpxor ymm10, ymm10, ymm11
	xor r13, r12
	add r10, r13
	vpaddq ymm1, ymm1, ymm10
	add r9, QWORD PTR [rsi+rdx*1+24]
	add r9, QWORD PTR [rcx+rdx*2+40]
	mov r13, rbx
	vpsrlq ymm10, ymm0, 19
	and r13, rbp
	andn r15, rbx, r8
	vpsllq ymm11, ymm0, 45
	add r13, r15
	add r9, r13
	vpxor ymm10, ymm10, ymm11
	rorx r13, rbx, 14
	rorx r15, rbx, 18
	vpsrlq ymm11, ymm0, 61
	xor r13, r15
	rorx r15, rbx, 41
	vpxor ymm10, ymm10, ymm11
	xor r13, r15
	add r9, r13
	vpsllq ymm11, ymm0, 3
	add rax, r9
	rorx r13, r10, 28
	vpxor ymm10, ymm10, ymm11
	rorx r15, r10, 34
	xor r13, r15
	vpsrlq ymm11, ymm0, 6
	rorx r15, r10, 39
	xor r13, r15
	vpxor ymm10, ymm10, ymm11
	add r9, r13
	mov r13, r10
	vpaddq ymm1, ymm1, ymm10
	xor r13, r11
	and r14, r13
	vmovdqu YMMWORD PTR [rcx+rdx*2+288], ymm1
	xor r14, r11
	add r9, r14
	vpalignr ymm8, ymm3, ymm2, 8
	add r8, QWORD PTR [rsi+rdx*1+32]
	add r8, QWORD PTR [rcx+rdx*2+64]
	mov r14, rax
	vpalignr ymm9, ymm7, ymm6, 8
	and r14, rbx
	andn r15, rax, rbp
	vpaddq ymm2, ymm2, ymm9
	add r14, r15
	add r8, r14
	vpsrlq ymm10, ymm8, 1
	rorx r14, rax, 14
	rorx r15, rax, 18
	vpsllq ymm11, ymm8, 63
	xor r14, r15
	rorx r15, rax, 41
	vpxor ymm10, ymm10, ymm11
	xor r14, r15
	add r8, r14
	vpsrlq ymm11, ymm8, 8
	add r12, r8
	rorx r14, r9, 28
	vpxor ymm10, ymm10, ymm11
	rorx r15, r9, 34
	xor r14, r15
	vpsllq ymm11, ymm8, 56
	rorx r15, r9, 39
	xor r14, r15
	vpxor ymm10, ymm10, ymm11
	add r8, r14
	mov r14, r9
	vpsrlq ymm11, ymm8, 7
	xor r14, r10
	and r13, r14
	vpxor ymm10, ymm10, ymm11
	xor r13, r10
	add r8, r13
	vpaddq ymm2, ymm2, ymm10
	add rbp, QWORD PTR [rsi+rdx*1+40]
	add rbp, QWORD PTR [rcx+rdx*2+72]
	mov r13, r12
	vpsrlq ymm10, ymm1, 19
	and r13, rax
	andn r15, r12, rbx
	vpsllq ymm11, ymm1, 45
	add r13, r15
	add rbp, r13
	vpxor ymm10, ymm10, ymm11
	rorx r13, r12, 14
	rorx r15, r12, 18
	vpsrlq ymm11, ymm1, 61
	xor r13, r15
	rorx r15, r12, 41
	vpxor ymm10, ymm10, ymm11
	xor r13, r15
	add rbp, r13
	vpsllq ymm11, ymm1, 3
	add r11, rbp
	rorx r13, r8, 28
	vpxor ymm10, ymm10, ymm11
	rorx r15, r8, 34
	xor r13, r15
	vpsrlq ymm11, ymm1, 6
	rorx r15, r8, 39
	xor r13, r15
	vpxor ymm10, ymm10, ymm11
	add rbp, r13
	mov r13, r8
	vpaddq ymm2, ymm2, ymm10
	xor r13, r9
	and r14, r13
	vmovdqu YMMWORD PTR [rcx+rdx*2+320], ymm2
	xor r14, r9
	add rbp, r14
	vpalignr ymm8, ymm4, ymm3, 8
	add rbx, QWORD PTR [rsi+rdx*1+48]
	add rbx, QWORD PTR [rcx+rdx*2+96]
	mov r14, r11
	vpalignr ymm9, ymm0, ymm7, 8
	and r14, r12
	andn r15, r11, rax
	vpaddq ymm3, ymm3, ymm9
	add r14, r15
	add rbx, r14
	vpsrlq ymm10, ymm8, 1
	rorx r14, r11, 14
	rorx r15, r11, 18
	vpsllq ymm11, ymm8, 63
	xor r14, r15
	rorx r15, r11, 41
	vpxor ymm10, ymm10, ymm11
	xor r14, r15
	add rbx, r14
	vpsrlq ymm11, ymm8, 8
	add r10, rbx
	rorx r14, rbp, 28
	vpxor ymm10, ymm10, ymm11
	rorx r15, rbp, 34
	xor r14, r15
	vpsllq ymm11, ymm8, 56
	rorx r15, rbp, 39
	xor r14, r15
	vpxor ymm10, ymm10, ymm11
	add rbx, r14
	mov r14, rbp
	vpsrlq ymm11, ymm8, 7
	xor r14, r8
	and r13, r14
	vpxor ymm10, ymm10, ymm11
	xor r13, r8
	add rbx, r13
	vpaddq ymm3, ymm3, ymm10
	add rax, QWORD PTR [rsi+rdx*1+56]
	add rax, QWORD PTR [rcx+rdx*2+104]
	mov r13, r10
	vpsrlq ymm10, ymm2, 19
	and r13, r11
	andn r15, r10, r12
	vpsllq ymm11, ymm2, 45
	add r13, r15
	add rax, r13
	vpxor ymm10, ymm10, ymm11
	rorx r13, r10, 14
	rorx r15, r10, 18
	vpsrlq ymm11, ymm2, 61
	xor r13, r15
	rorx r15, r10, 41
	vpxor ymm10, ymm10, ymm11
	xor r13, r15
	add rax, r13
	vpsllq ymm11, ymm2, 3
	add r9, rax
	rorx r13, rbx, 28
	vpxor ymm10, ymm10, ymm11
	rorx r15, rbx, 34
	xor r13, r15
	vpsrlq ymm11, ymm2, 6
	rorx r15, rbx, 39
	xor r13, r15
	vpxor ymm10, ymm10, ymm11
	add rax, r13
	mov r13, rbx
	vpaddq ymm3, ymm3, ymm10
	xor r13, rbp
	and r14, r13
	vmovdqu YMMWORD PTR [rcx+rdx*2+352], ymm3
	xor r14, rbp
	add rax, r14
	vpalignr ymm8, ymm5, ymm4, 8
	add r12, QWORD PTR [rsi+rdx*1+64]
	add r12, QWORD PTR [rcx+rdx*2+128]
	mov r14, r9
	vpalignr ymm9, ymm1, ymm0, 8
	and r14, r10
	andn r15, r9, r11
	vpaddq ymm4, ymm4, ymm9
	add r14, r15
	add r12, r14
	vpsrlq ymm10, ymm8, 1
	rorx r14, r9, 14
	rorx r15, r9, 18
	vpsllq ymm11, ymm8, 63
	xor r14, r15
	rorx r15, r9, 41
	vpxor ymm10, ymm10, ymm11
	xor r14, r15
	add r12, r14
	vpsrlq ymm11, ymm8, 8
	add r8, r12
	rorx r14, rax, 28
	vpxor ymm10, ymm10, ymm11
	rorx r15, rax, 34
	xor r14, r15
	vpsllq ymm11, ymm8, 56
	rorx r15, rax, 39
	xor r14, r15
	vpxor ymm10, ymm10, ymm11
	add r12, r14
	mov r14, rax
	vpsrlq ymm11, ymm8, 7
	xor r14, rbx
	and r13, r14
	vpxor ymm10, ymm10, ymm11
	xor r13, rbx
	add r12, r13
	vpaddq ymm4, ymm4, ymm10
	add r11, QWORD PTR [rsi+rdx*1+72]
	add r11, QWORD PTR [rcx+rdx*2+136]
	mov r13, r8
	vpsrlq ymm10, ymm3, 19
	and r13, r9
	andn r15, r8, r10
	vpsllq ymm11, ymm3, 45
	add r13, r15
	add r11, r13
	vpxor ymm10, ymm10, ymm11
	rorx r13, r8, 14
	rorx r15, r8, 18
	vpsrlq ymm11, ymm3, 61
	xor r13, r15
	rorx r15, r8, 41
	vpxor ymm10, ymm10, ymm11
	xor r13, r15
	add r11, r13
	vpsllq ymm11, ymm3, 3
	add rbp, r11
	rorx r13, r12, 28
	vpxor ymm10, ymm10, ymm11
	rorx r15, r12, 34
	xor r13, r15
	vpsrlq ymm11, ymm3, 6
	rorx r15, r12, 39
	xor r13, r15
	vpxor ymm10, ymm10, ymm11
	add r11, r13
	mov r13, r12
	vpaddq ymm4, ymm4, ymm10
	xor r13, rax
	and r14, r13
	vmovdqu YMMWORD PTR [rcx+rdx*2+384], ymm4
	xor r14, rax
	add r11, r14
	vpalignr ymm8, ymm6, ymm5, 8
	add r10, QWORD PTR [rsi+rdx*1+80]
	add r10, QWORD PTR [rcx+rdx*2+160]
	mov r14, rbp
	vpalignr ymm9, ymm2, ymm1, 8
	and r14, r8
	andn r15, rbp, r9
	vpaddq ymm5, ymm5, ymm9
	add r14, r15
	add r10, r14
	vpsrlq ymm10, ymm8, 1
	rorx r14, rbp, 14
	rorx r15, rbp, 18
	vpsllq ymm11, ymm8, 63
	xor r14, r15
	rorx r15, rbp, 41
	vpxor ymm10, ymm10, ymm11
	xor r14, r15
	add r10, r14
	vpsrlq ymm11, ymm8, 8
	add rbx, r10
	rorx r14, r11, 28
	vpxor ymm10, ymm10, ymm11
	rorx r15, r11, 34
	xor r14, r15
	vpsllq ymm11, ymm8, 56
	rorx r15, r11, 39
	xor r14, r15
	vpxor ymm10, ymm10, ymm11
	add r10, r14
	mov r14, r11
	vpsrlq ymm11, ymm8, 7
	xor r14, r12
	and r13, r14
	vpxor ymm10, ymm10, ymm11
	xor r13, r12
	add r10, r13
	vpaddq ymm5, ymm5, ymm10
	add r9, QWORD PTR [rsi+rdx*1+88]
	add r9, QWORD PTR [rcx+rdx*2+168]
	mov r13, rbx
	vpsrlq ymm10, ymm4, 19
	and r13, rbp
	andn r15, rbx, r8
	vpsllq ymm11, ymm4, 45
	add r13, r15
	add r9, r13
	vpxor ymm10, ymm10, ymm11
	rorx r13, rbx, 14
	rorx r15, rbx, 18
	vpsrlq ymm11, ymm4, 61
	xor r13, r15
	rorx r15, rbx, 41
	vpxor ymm10, ymm10, ymm11
	xor r13, r15
	add r9, r13
	vpsllq ymm11, ymm4, 3
	add rax, r9
	rorx r13, r10, 28
	vpxor ymm10, ymm10, ymm11
	rorx r15, r10, 34
	xor r13, r15
	vpsrlq ymm11, ymm4, 6
	rorx r15, r10, 39
	xor r13, r15
	vpxor ymm10, ymm10, ymm11
	add r9, r13
	mov r13, r10
	vpaddq ymm5, ymm5, ymm10
	xor r13, r11
	and r14, r13
	vmovdqu YMMWORD PTR [rcx+rdx*2+416], ymm5
	xor r14, r11
	add r9, r14
	vpalignr ymm8, ymm7, ymm6, 8
	add r8, QWORD PTR [rsi+rdx*1+96]
	add r8, QWORD PTR [rcx+rdx*2+192]
	mov r14, rax
	vpalignr ymm9, ymm3, ymm2, 8
	and r14, rbx
	andn r15, rax, rbp
	vpaddq ymm6, ymm6, ymm9
	add r14, r15
	add r8, r14
	vpsrlq ymm10, ymm8, 1
	rorx r14, rax, 14
	rorx r15, rax, 18
	vpsllq ymm11, ymm8, 63
	xor r14, r15
	rorx r15, rax, 41
	vpxor ymm10, ymm10, ymm11
	xor r14, r15
	add r8, r14
	vpsrlq ymm11, ymm8, 8
	add r12, r8
	rorx r14, r9, 28
	vpxor ymm10, ymm10, ymm11
	rorx r15, r9, 34
	xor r14, r15
	vpsllq ymm11, ymm8, 56
	rorx r15, r9, 39
	xor r14, r15
	vpxor ymm10, ymm10, ymm11
	add r8, r14
	mov r14, r9
	vpsrlq ymm11, ymm8, 7
	xor r14, r10
	and r13, r14
	vpxor ymm10, ymm10, ymm11
	xor r13, r10
	add r8, r13
	vpaddq ymm6, ymm6, ymm10
	add rbp, QWORD PTR [rsi+rdx*1+104]
	add rbp, QWORD PTR [rcx+rdx*2+200]
	mov r13, r12
	vpsrlq ymm10, ymm5, 19
	and r13, rax
	andn r15, r12, rbx
	vpsllq ymm11, ymm5, 45
	add r13, r15
	add rbp, r13
	vpxor ymm10, ymm10, ymm11
	rorx r13, r12, 14
	rorx r15, r12, 18
	vpsrlq ymm11, ymm5, 61
	xor r13, r15
	rorx r15, r12, 41
	vpxor ymm10, ymm10, ymm11
	xor r13, r15
	add rbp, r13
	vpsllq ymm11, ymm5, 3
	add r11, rbp
	rorx r13, r8, 28
	vpxor ymm10, ymm10, ymm11
	rorx r15, r8, 34
	xor r13, r15
	vpsrlq ymm11, ymm5, 6
	rorx r15, r8, 39
	xor r13, r15
	vpxor ymm10, ymm10, ymm11
	add rbp, r13
	mov r13, r8
	vpaddq ymm6, ymm6, ymm10
	xor r13, r9
	and r14, r13
	vmovdqu YMMWORD PTR [rcx+rdx*2+448], ymm6
	xor r14, r9
	add rbp, r14
	vpalignr ymm8, ymm0, ymm7, 8
	add rbx, QWORD PTR [rsi+rdx*1+112]
	add rbx, QWORD PTR [rcx+rdx*2+224]
	mov r14, r11
	vpalignr ymm9, ymm4, ymm3, 8
	and r14, r12
	andn r15, r11, rax
	vpaddq ymm7, ymm7, ymm9
	add r14, r15
	add rbx, r14
	vpsrlq ymm10, ymm8, 1
	rorx r14, r11, 14
	rorx r15, r11, 18
	vpsllq ymm11, ymm8, 63
	xor r14, r15
	rorx r15, r11, 41
	vpxor ymm10, ymm10, ymm11
	xor r14, r15
	add rbx, r14
	vpsrlq ymm11, ymm8, 8
	add r10, rbx
	rorx r14, rbp, 28
	vpxor ymm10, ymm10, ymm11
	rorx r15, rbp, 34
	xor r14, r15
	vpsllq ymm11, ymm8, 56
	rorx r15, rbp, 39
	xor r14, r15
	vpxor ymm10, ymm10, ymm11
	add rbx, r14
	mov r14, rbp
	vpsrlq ymm11, ymm8, 7
	xor r14, r8
	and r13, r14
	vpxor ymm10, ymm10, ymm11
	xor r13, r8
	add rbx, r13
	vpaddq ymm7, ymm7, ymm10
	add rax, QWORD PTR [rsi+rdx*1+120]
	add rax, QWORD PTR [rcx+rdx*2+232]
	mov r13, r10
	vpsrlq ymm10, ymm6, 19
	and r13, r11
	andn r15, r10, r12
	vpsllq ymm11, ymm6, 45
	add r13, r15
	add rax, r13
	vpxor ymm10, ymm10, ymm11
	rorx r13, r10, 14
	rorx r15, r10, 18
	vpsrlq ymm11, ymm6, 61
	xor r13, r15
	rorx r15, r10, 41
	vpxor ymm10, ymm10, ymm11
	xor r13, r15
	add rax, r13
	vpsllq ymm11, ymm6, 3
	add r9, rax
	rorx r13, rbx, 28
	vpxor ymm10, ymm10, ymm11
	rorx r15, rbx, 34
	xor r13, r15
	vpsrlq ymm11, ymm6, 6
	rorx r15, rbx, 39
	xor r13, r15
	vpxor ymm10, ymm10, ymm11
	add rax, r13
	mov r13, rbx
	vpaddq ymm7, ymm7, ymm10
	xor r13, rbp
	and r14, r13
	vmovdqu YMMWORD PTR [rcx+rdx*2+480], ymm7
	xor r14, rbp
	add rax, r14
	add rdx, 128
	cmp rdx, 512
	jne 25b
	add r12, QWORD PTR [rsi+rdx*1]
	add r12, QWORD PTR [rcx+rdx*2]
	mov r14, r9
	and r14, r10
	andn r15, r9, r11
	add r14, r15
	add r12, r14
	rorx r14, r9, 14
	rorx r15, r9, 18
	xor r14, r15
	rorx r15, r9, 41
	xor r14, r15
	add r12, r14
	add r8, r12
	rorx r14, rax, 28
	rorx r15, rax, 34
	xor r14, r15
	rorx r15, rax, 39
	xor r14, r15
	add r12, r14
	mov r14, rax
	xor r14, rbx
	and r13, r14
	xor r13, rbx
	add r12, r13
	add r11, QWORD PTR [rsi+rdx*1+8]
	add r11, QWORD PTR [rcx+rdx*2+8]
	mov r13, r8
	and r13, r9
	andn r15, r8, r10
	add r13, r15
	add r11, r13
	rorx r13, r8, 14
	rorx r15, r8, 18
	xor r13, r15
	rorx r15, r8, 41
	xor r13, r15
	add r11, r13
	add rbp, r11
	rorx r13, r12, 28
	rorx r15, r12, 34
	xor r13, r15
	rorx r15, r12, 39
	xor r13, r15
	add r11, r13
	mov r13, r12
	xor r13, rax
	and r14, r13
	xor r14, rax
	add r11, r14
	add r10, QWORD PTR [rsi+rdx*1+16]
	add r10, QWORD PTR [rcx+rdx*2+32]
	mov r14, rbp
	and r14, r8
	andn r15, rbp, r9
	add r14, r15
	add r10, r14
	rorx r14, rbp, 14
	rorx r15, rbp, 18
	xor r14, r15
	rorx r15, rbp, 41
	xor r14, r15
	add r10, r14
	add rbx, r10
	rorx r14, r11, 28
	rorx r15, r11, 34
	xor r14, r15
	rorx r15, r11, 39
	xor r14, r15
	add r10, r14
	mov r14, r11
	xor r14, r12
	and r13, r14
	xor r13, r12
	add r10, r13
	add r9, QWORD PTR [rsi+rdx*1+24]
	add r9, QWORD PTR [rcx+rdx*2+40]
	mov r13, rbx
	and r13, rbp
	andn r15, rbx, r8
	add r13, r15
	add r9, r13
	rorx r13, rbx, 14
	rorx r15, rbx, 18
	xor r13, r15
	rorx r15, rbx, 41
	xor r13, r15
	add r9, r13
	add rax, r9
	rorx r13, r10, 28
	rorx r15, r10, 34
	xor r13, r15
	rorx r15, r10, 39
	xor r13, r15
	add r9, r13
	mov r13, r10
	xor r13, r11
	and r14, r13
	xor r14, r11
	add r9, r14
	add r8, QWORD PTR [rsi+rdx*1+32]
	add r8, QWORD PTR [rcx+rdx*2+64]
	mov r14, rax
	and r14, rbx
	andn r15, rax, rbp
	add r14, r15
	add r8, r14
	rorx r14, rax, 14
	rorx r15, rax, 18
	xor r14, r15
	rorx r15, rax, 41
	xor r14, r15
	add r8, r14
	add r12, r8
	rorx r14, r9, 28
	rorx r15, r9, 34
	xor r14, r15
	rorx r15, r9, 39
	xor r14, r15
	add r8, r14
	mov r14, r9
	xor r14, r10
	and r13, r14
	xor r13, r10
	add r8, r13
	add rbp, QWORD PTR [rsi+rdx*1+40]
	add rbp, QWORD PTR [rcx+rdx*2+72]
	mov r13, r12
	and r13, rax
	andn r15, r12, rbx
	add r13, r15
	add rbp, r13
	rorx r13, r12, 14
	rorx r15, r12, 18
	xor r13, r15
	rorx r15, r12, 41
	xor r13, r15
	add rbp, r13
	add r11, rbp
	rorx r13, r8, 28
	rorx r15, r8, 34
	xor r13, r15
	rorx r15, r8, 39
	xor r13, r15
	add rbp, r13
	mov r13, r8
	xor r13, r9
	and r14, r13
	xor r14, r9
	add rbp, r14
	add rbx, QWORD PTR [rsi+rdx*1+48]
	add rbx, QWORD PTR [rcx+rdx*2+96]
	mov r14, r11
	and r14, r12
	andn r15, r11, rax
	add r14, r15
	add rbx, r14
	rorx r14, r11, 14
	rorx r15, r11, 18
	xor r14, r15
	rorx r15, r11, 41
	xor r14, r15
	add rbx, r14
	add r10, rbx
	rorx r14, rbp, 28
	rorx r15, rbp, 34
	xor r14, r15
	rorx r15, rbp, 39
	xor r14, r15
	add rbx, r14
	mov r14, rbp
	xor r14, r8
	and r13, r14
	xor r13, r8
	add rbx, r13
	add rax, QWORD PTR [rsi+rdx*1+56]
	add rax, QWORD PTR [rcx+rdx*2+104]
	mov r13, r10
	and r13, r11
	andn r15, r10, r12
	add r13, r15
	add rax, r13
	rorx r13, r10, 14
	rorx r15, r10, 18
	xor r13, r15
	rorx r15, r10, 41
	xor r13, r15
	add rax, r13
	add r9, rax
	rorx r13, rbx, 28
	rorx r15, rbx, 34
	xor r13, r15
	rorx r15, rbx, 39
	xor r13, r15
	add rax, r13
	mov r13, rbx
	xor r13, rbp
	and r14, r13
	xor r14, rbp
	add rax, r14
	add r12, QWORD PTR [rsi+rdx*1+64]
	add r12, QWORD PTR [rcx+rdx*2+128]
	mov r14, r9
	and r14, r10
	andn r15, r9, r11
	add r14, r15
	add r12, r14
	rorx r14, r9, 14
	rorx r15, r9, 18
	xor r14, r15
	rorx r15, r9, 41
	xor r14, r15
	add r12, r14
	add r8, r12
	rorx r14, rax, 28
	rorx r15, rax, 34
	xor r14, r15
	rorx r15, rax, 39
	xor r14, r15
	add r12, r14
	mov r14, rax
	xor r14, rbx
	and r13, r14
	xor r13, rbx
	add r12, r13
	add r11, QWORD PTR [rsi+rdx*1+72]
	add r11, QWORD PTR [rcx+rdx*2+136]
	mov r13, r8
	and r13, r9
	andn r15, r8, r10
	add r13, r15
	add r11, r13
	rorx r13, r8, 14
	rorx r15, r8, 18
	xor r13, r15
	rorx r15, r8, 41
	xor r13, r15
	add r11, r13
	add rbp, r11
	rorx r13, r12, 28
	rorx r15, r12, 34
	xor r13, r15
	rorx r15, r12, 39
	xor r13, r15
	add r11, r13
	mov r13, r12
	xor r13, rax
	and r14, r13
	xor r14, rax
	add r11, r14
	add r10, QWORD PTR [rsi+rdx*1+80]
	add r10, QWORD PTR [rcx+rdx*2+160]
	mov r14, rbp
	and r14, r8
	andn r15, rbp, r9
	add r14, r15
	add r10, r14
	rorx r14, rbp, 14
	rorx r15, rbp, 18
	xor r14, r15
	rorx r15, rbp, 41
	xor r14, r15
	add r10, r14
	add rbx, r10
	rorx r14, r11, 28
	rorx r15, r11, 34
	xor r14, r15
	rorx r15, r11, 39
	xor r14, r15
	add r10, r14
	mov r14, r11
	xor r14, r12
	and r13, r14
	xor r13, r12
	add r10, r13
	add r9, QWORD PTR [rsi+rdx*1+88]
	add r9, QWORD PTR [rcx+rdx*2+168]
	mov r13, rbx
	and r13, rbp
	andn r15, rbx, r8
	add r13, r15
	add r9, r13
	rorx r13, rbx, 14
	rorx r15, rbx, 18
	xor r13, r15
	rorx r15, rbx, 41
	xor r13, r15
	add r9, r13
	add rax, r9
	rorx r13, r10, 28
	rorx r15, r10, 34
	xor r13, r15
	rorx r15, r10, 39
	xor r13, r15
	add r9, r13
	mov r13, r10
	xor r13, r11
	and r14, r13
	xor r14, r11
	add r9, r14
	add r8, QWORD PTR [rsi+rdx*1+96]
	add r8, QWORD PTR [rcx+rdx*2+192]
	mov r14, rax
	and r14, rbx
	andn r15, rax, rbp
	add r14, r15
	add r8, r14
	rorx r14, rax, 14
	rorx r15, rax, 18
	xor r14, r15
	rorx r15, rax, 41
	xor r14, r15
	add r8, r14
	add r12, r8
	rorx r14, r9, 28
	rorx r15, r9, 34
	xor r14, r15
	rorx r15, r9, 39
	xor r14, r15
	add r8, r14
	mov r14, r9
	xor r14, r10
	and r13, r14
	xor r13, r10
	add r8, r13
	add rbp, QWORD PTR [rsi+rdx*1+104]
	add rbp, QWORD PTR [rcx+rdx*2+200]
	mov r13, r12
	and r13, rax
	andn r15, r12, rbx
	add r13, r15
	add rbp, r13
	rorx r13, r12, 14
	rorx r15, r12, 18
	xor r13, r15
	rorx r15, r12, 41
	xor r13, r15
	add rbp, r13
	add r11, rbp
	rorx r13, r8, 28
	rorx r15, r8, 34
	xor r13, r15
	rorx r15, r8, 39
	xor r13, r15
	add rbp, r13
	mov r13, r8
	xor r13, r9
	and r14, r13
	xor r14, r9
	add rbp, r14
	add rbx, QWORD PTR [rsi+rdx*1+112]
	add rbx, QWORD PTR [rcx+rdx*2+224]
	mov r14, r11
	and r14, r12
	andn r15, r11, rax
	add r14, r15
	add rbx, r14
	rorx r14, r11, 14
	rorx r15, r11, 18
	xor r14, r15
	rorx r15, r11, 41
	xor r14, r15
	add rbx, r14
	add r10, rbx
	rorx r14, rbp, 28
	rorx r15, rbp, 34
	xor r14, r15
	rorx r15, rbp, 39
	xor r14, r15
	add rbx, r14
	mov r14, rbp
	xor r14, r8
	and r13, r14
	xor r13, r8
	add rbx, r13
	add rax, QWORD PTR [rsi+rdx*1+120]
	add rax, QWORD PTR [rcx+rdx*2+232]
	mov r13, r10
	and r13, r11
	andn r15, r10, r12
	add r13, r15
	add rax, r13
	rorx r13, r10, 14
	rorx r15, r10, 18
	xor r13, r15
	rorx r15, r10, 41
	xor r13, r15
	add rax, r13
	add r9, rax
	rorx r13, rbx, 28
	rorx r15, rbx, 34
	xor r13, r15
	rorx r15, rbx, 39
	xor r13, r15
	add rax, r13
	mov r13, rbx
	xor r13, rbp
	and r14, r13
	xor r14, rbp
	add rax, r14
	mov rsi, QWORD PTR [rcx+1312]
	mov rdx, QWORD PTR [rcx+1320]
	add rax, QWORD PTR [rdi]
	add rbx, QWORD PTR [rdi+8]
	add rbp, QWORD PTR [rdi+16]
	add r8, QWORD PTR [rdi+24]
	add r9, QWORD PTR [rdi+32]
	add r10, QWORD PTR [rdi+40]
	add r11, QWORD PTR [rdi+48]
	add r12, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rbx
	mov QWORD PTR [rdi+16], rbp
	mov QWORD PTR [rdi+24], r8
	mov QWORD PTR [rdi+32], r9
	mov QWORD PTR [rdi+40], r10
	mov QWORD PTR [rdi+48], r11
	mov QWORD PTR [rdi+56], r12
	cmp rdx, 1
	je 26f
	mov r13, rbx
	xor r13, rbp
	mov QWORD PTR [rcx+1312], rsi
	mov QWORD PTR [rcx+1320], rdx
	lea rsi, {VG_SHA512_K}
	mov rdx, 0
28:
	add r12, QWORD PTR [rsi+rdx*1]
	add r12, QWORD PTR [rcx+rdx*2+16]
	mov r14, r9
	and r14, r10
	andn r15, r9, r11
	add r14, r15
	add r12, r14
	rorx r14, r9, 14
	rorx r15, r9, 18
	xor r14, r15
	rorx r15, r9, 41
	xor r14, r15
	add r12, r14
	add r8, r12
	rorx r14, rax, 28
	rorx r15, rax, 34
	xor r14, r15
	rorx r15, rax, 39
	xor r14, r15
	add r12, r14
	mov r14, rax
	xor r14, rbx
	and r13, r14
	xor r13, rbx
	add r12, r13
	add r11, QWORD PTR [rsi+rdx*1+8]
	add r11, QWORD PTR [rcx+rdx*2+24]
	mov r13, r8
	and r13, r9
	andn r15, r8, r10
	add r13, r15
	add r11, r13
	rorx r13, r8, 14
	rorx r15, r8, 18
	xor r13, r15
	rorx r15, r8, 41
	xor r13, r15
	add r11, r13
	add rbp, r11
	rorx r13, r12, 28
	rorx r15, r12, 34
	xor r13, r15
	rorx r15, r12, 39
	xor r13, r15
	add r11, r13
	mov r13, r12
	xor r13, rax
	and r14, r13
	xor r14, rax
	add r11, r14
	add r10, QWORD PTR [rsi+rdx*1+16]
	add r10, QWORD PTR [rcx+rdx*2+48]
	mov r14, rbp
	and r14, r8
	andn r15, rbp, r9
	add r14, r15
	add r10, r14
	rorx r14, rbp, 14
	rorx r15, rbp, 18
	xor r14, r15
	rorx r15, rbp, 41
	xor r14, r15
	add r10, r14
	add rbx, r10
	rorx r14, r11, 28
	rorx r15, r11, 34
	xor r14, r15
	rorx r15, r11, 39
	xor r14, r15
	add r10, r14
	mov r14, r11
	xor r14, r12
	and r13, r14
	xor r13, r12
	add r10, r13
	add r9, QWORD PTR [rsi+rdx*1+24]
	add r9, QWORD PTR [rcx+rdx*2+56]
	mov r13, rbx
	and r13, rbp
	andn r15, rbx, r8
	add r13, r15
	add r9, r13
	rorx r13, rbx, 14
	rorx r15, rbx, 18
	xor r13, r15
	rorx r15, rbx, 41
	xor r13, r15
	add r9, r13
	add rax, r9
	rorx r13, r10, 28
	rorx r15, r10, 34
	xor r13, r15
	rorx r15, r10, 39
	xor r13, r15
	add r9, r13
	mov r13, r10
	xor r13, r11
	and r14, r13
	xor r14, r11
	add r9, r14
	add r8, QWORD PTR [rsi+rdx*1+32]
	add r8, QWORD PTR [rcx+rdx*2+80]
	mov r14, rax
	and r14, rbx
	andn r15, rax, rbp
	add r14, r15
	add r8, r14
	rorx r14, rax, 14
	rorx r15, rax, 18
	xor r14, r15
	rorx r15, rax, 41
	xor r14, r15
	add r8, r14
	add r12, r8
	rorx r14, r9, 28
	rorx r15, r9, 34
	xor r14, r15
	rorx r15, r9, 39
	xor r14, r15
	add r8, r14
	mov r14, r9
	xor r14, r10
	and r13, r14
	xor r13, r10
	add r8, r13
	add rbp, QWORD PTR [rsi+rdx*1+40]
	add rbp, QWORD PTR [rcx+rdx*2+88]
	mov r13, r12
	and r13, rax
	andn r15, r12, rbx
	add r13, r15
	add rbp, r13
	rorx r13, r12, 14
	rorx r15, r12, 18
	xor r13, r15
	rorx r15, r12, 41
	xor r13, r15
	add rbp, r13
	add r11, rbp
	rorx r13, r8, 28
	rorx r15, r8, 34
	xor r13, r15
	rorx r15, r8, 39
	xor r13, r15
	add rbp, r13
	mov r13, r8
	xor r13, r9
	and r14, r13
	xor r14, r9
	add rbp, r14
	add rbx, QWORD PTR [rsi+rdx*1+48]
	add rbx, QWORD PTR [rcx+rdx*2+112]
	mov r14, r11
	and r14, r12
	andn r15, r11, rax
	add r14, r15
	add rbx, r14
	rorx r14, r11, 14
	rorx r15, r11, 18
	xor r14, r15
	rorx r15, r11, 41
	xor r14, r15
	add rbx, r14
	add r10, rbx
	rorx r14, rbp, 28
	rorx r15, rbp, 34
	xor r14, r15
	rorx r15, rbp, 39
	xor r14, r15
	add rbx, r14
	mov r14, rbp
	xor r14, r8
	and r13, r14
	xor r13, r8
	add rbx, r13
	add rax, QWORD PTR [rsi+rdx*1+56]
	add rax, QWORD PTR [rcx+rdx*2+120]
	mov r13, r10
	and r13, r11
	andn r15, r10, r12
	add r13, r15
	add rax, r13
	rorx r13, r10, 14
	rorx r15, r10, 18
	xor r13, r15
	rorx r15, r10, 41
	xor r13, r15
	add rax, r13
	add r9, rax
	rorx r13, rbx, 28
	rorx r15, rbx, 34
	xor r13, r15
	rorx r15, rbx, 39
	xor r13, r15
	add rax, r13
	mov r13, rbx
	xor r13, rbp
	and r14, r13
	xor r14, rbp
	add rax, r14
	add r12, QWORD PTR [rsi+rdx*1+64]
	add r12, QWORD PTR [rcx+rdx*2+144]
	mov r14, r9
	and r14, r10
	andn r15, r9, r11
	add r14, r15
	add r12, r14
	rorx r14, r9, 14
	rorx r15, r9, 18
	xor r14, r15
	rorx r15, r9, 41
	xor r14, r15
	add r12, r14
	add r8, r12
	rorx r14, rax, 28
	rorx r15, rax, 34
	xor r14, r15
	rorx r15, rax, 39
	xor r14, r15
	add r12, r14
	mov r14, rax
	xor r14, rbx
	and r13, r14
	xor r13, rbx
	add r12, r13
	add r11, QWORD PTR [rsi+rdx*1+72]
	add r11, QWORD PTR [rcx+rdx*2+152]
	mov r13, r8
	and r13, r9
	andn r15, r8, r10
	add r13, r15
	add r11, r13
	rorx r13, r8, 14
	rorx r15, r8, 18
	xor r13, r15
	rorx r15, r8, 41
	xor r13, r15
	add r11, r13
	add rbp, r11
	rorx r13, r12, 28
	rorx r15, r12, 34
	xor r13, r15
	rorx r15, r12, 39
	xor r13, r15
	add r11, r13
	mov r13, r12
	xor r13, rax
	and r14, r13
	xor r14, rax
	add r11, r14
	add r10, QWORD PTR [rsi+rdx*1+80]
	add r10, QWORD PTR [rcx+rdx*2+176]
	mov r14, rbp
	and r14, r8
	andn r15, rbp, r9
	add r14, r15
	add r10, r14
	rorx r14, rbp, 14
	rorx r15, rbp, 18
	xor r14, r15
	rorx r15, rbp, 41
	xor r14, r15
	add r10, r14
	add rbx, r10
	rorx r14, r11, 28
	rorx r15, r11, 34
	xor r14, r15
	rorx r15, r11, 39
	xor r14, r15
	add r10, r14
	mov r14, r11
	xor r14, r12
	and r13, r14
	xor r13, r12
	add r10, r13
	add r9, QWORD PTR [rsi+rdx*1+88]
	add r9, QWORD PTR [rcx+rdx*2+184]
	mov r13, rbx
	and r13, rbp
	andn r15, rbx, r8
	add r13, r15
	add r9, r13
	rorx r13, rbx, 14
	rorx r15, rbx, 18
	xor r13, r15
	rorx r15, rbx, 41
	xor r13, r15
	add r9, r13
	add rax, r9
	rorx r13, r10, 28
	rorx r15, r10, 34
	xor r13, r15
	rorx r15, r10, 39
	xor r13, r15
	add r9, r13
	mov r13, r10
	xor r13, r11
	and r14, r13
	xor r14, r11
	add r9, r14
	add r8, QWORD PTR [rsi+rdx*1+96]
	add r8, QWORD PTR [rcx+rdx*2+208]
	mov r14, rax
	and r14, rbx
	andn r15, rax, rbp
	add r14, r15
	add r8, r14
	rorx r14, rax, 14
	rorx r15, rax, 18
	xor r14, r15
	rorx r15, rax, 41
	xor r14, r15
	add r8, r14
	add r12, r8
	rorx r14, r9, 28
	rorx r15, r9, 34
	xor r14, r15
	rorx r15, r9, 39
	xor r14, r15
	add r8, r14
	mov r14, r9
	xor r14, r10
	and r13, r14
	xor r13, r10
	add r8, r13
	add rbp, QWORD PTR [rsi+rdx*1+104]
	add rbp, QWORD PTR [rcx+rdx*2+216]
	mov r13, r12
	and r13, rax
	andn r15, r12, rbx
	add r13, r15
	add rbp, r13
	rorx r13, r12, 14
	rorx r15, r12, 18
	xor r13, r15
	rorx r15, r12, 41
	xor r13, r15
	add rbp, r13
	add r11, rbp
	rorx r13, r8, 28
	rorx r15, r8, 34
	xor r13, r15
	rorx r15, r8, 39
	xor r13, r15
	add rbp, r13
	mov r13, r8
	xor r13, r9
	and r14, r13
	xor r14, r9
	add rbp, r14
	add rbx, QWORD PTR [rsi+rdx*1+112]
	add rbx, QWORD PTR [rcx+rdx*2+240]
	mov r14, r11
	and r14, r12
	andn r15, r11, rax
	add r14, r15
	add rbx, r14
	rorx r14, r11, 14
	rorx r15, r11, 18
	xor r14, r15
	rorx r15, r11, 41
	xor r14, r15
	add rbx, r14
	add r10, rbx
	rorx r14, rbp, 28
	rorx r15, rbp, 34
	xor r14, r15
	rorx r15, rbp, 39
	xor r14, r15
	add rbx, r14
	mov r14, rbp
	xor r14, r8
	and r13, r14
	xor r13, r8
	add rbx, r13
	add rax, QWORD PTR [rsi+rdx*1+120]
	add rax, QWORD PTR [rcx+rdx*2+248]
	mov r13, r10
	and r13, r11
	andn r15, r10, r12
	add r13, r15
	add rax, r13
	rorx r13, r10, 14
	rorx r15, r10, 18
	xor r13, r15
	rorx r15, r10, 41
	xor r13, r15
	add rax, r13
	add r9, rax
	rorx r13, rbx, 28
	rorx r15, rbx, 34
	xor r13, r15
	rorx r15, rbx, 39
	xor r13, r15
	add rax, r13
	mov r13, rbx
	xor r13, rbp
	and r14, r13
	xor r14, rbp
	add rax, r14
	add rdx, 128
	cmp rdx, 640
	jne 28b
	mov rsi, QWORD PTR [rcx+1312]
	mov rdx, QWORD PTR [rcx+1320]
	add rax, QWORD PTR [rdi]
	add rbx, QWORD PTR [rdi+8]
	add rbp, QWORD PTR [rdi+16]
	add r8, QWORD PTR [rdi+24]
	add r9, QWORD PTR [rdi+32]
	add r10, QWORD PTR [rdi+40]
	add r11, QWORD PTR [rdi+48]
	add r12, QWORD PTR [rdi+56]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rbx
	mov QWORD PTR [rdi+16], rbp
	mov QWORD PTR [rdi+24], r8
	mov QWORD PTR [rdi+32], r9
	mov QWORD PTR [rdi+40], r10
	mov QWORD PTR [rdi+48], r11
	mov QWORD PTR [rdi+56], r12
	add rsi, 256
	sub rdx, 2
	jmp 27f
26:
	add rsi, 128
	sub rdx, 1
27:
	jne 22b
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [rcx+1280]
	mov rbp, QWORD PTR [rcx+1288]
	mov r12, QWORD PTR [rcx+1296]
	mov r13, QWORD PTR [rcx+1304]
	vzeroupper
	movq r14, xmm14
	movq r15, xmm15
	ret
	.p2align 6
