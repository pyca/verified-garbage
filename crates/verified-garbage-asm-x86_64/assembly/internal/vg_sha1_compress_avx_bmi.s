// The functions of `src/internal/vg_sha1_compress_avx_bmi.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha1_compress_avx_bmi:
	mov QWORD PTR [rcx+64], rbx
	mov QWORD PTR [rcx+72], rbp
	mov QWORD PTR [rcx+80], r12
	mov QWORD PTR [rcx+88], r13
	mov QWORD PTR [rcx+96], r14
	mov QWORD PTR [rcx+104], r15
	movabs rax, 289644378169868803
	vmovq xmm6, rax
	movabs rax, 868365760874482187
	vmovq xmm7, rax
	vpunpcklqdq xmm6, xmm6, xmm7
	movabs rax, 6521908909941356953
	vmovq xmm8, rax
	movabs rax, 6521908909941356953
	vmovq xmm7, rax
	vpunpcklqdq xmm8, xmm8, xmm7
	movabs rax, 7987674492700322721
	vmovq xmm9, rax
	movabs rax, 7987674492700322721
	vmovq xmm7, rax
	vpunpcklqdq xmm9, xmm9, xmm7
	movabs rax, -8134700646434882340
	vmovq xmm10, rax
	movabs rax, -8134700646434882340
	vmovq xmm7, rax
	vpunpcklqdq xmm10, xmm10, xmm7
	movabs rax, -3863312402067832362
	vmovq xmm11, rax
	movabs rax, -3863312402067832362
	vmovq xmm7, rax
	vpunpcklqdq xmm11, xmm11, xmm7
	test rdx, rdx
	je 20f
22:
	vmovdqu xmm0, XMMWORD PTR [rsi]
	vpshufb xmm0, xmm0, xmm6
	vpaddd xmm4, xmm0, xmm8
	vmovdqu XMMWORD PTR [rcx], xmm4
	vmovdqu xmm1, XMMWORD PTR [rsi+16]
	vpshufb xmm1, xmm1, xmm6
	vpaddd xmm4, xmm1, xmm8
	vmovdqu XMMWORD PTR [rcx+16], xmm4
	vmovdqu xmm2, XMMWORD PTR [rsi+32]
	vpshufb xmm2, xmm2, xmm6
	vpaddd xmm4, xmm2, xmm8
	vmovdqu XMMWORD PTR [rcx+32], xmm4
	vmovdqu xmm3, XMMWORD PTR [rsi+48]
	vpshufb xmm3, xmm3, xmm6
	vpaddd xmm4, xmm3, xmm8
	vmovdqu XMMWORD PTR [rcx+48], xmm4
	mov eax, DWORD PTR [rdi]
	mov ebx, DWORD PTR [rdi+4]
	mov ebp, DWORD PTR [rdi+8]
	mov r8d, DWORD PTR [rdi+12]
	mov r9d, DWORD PTR [rdi+16]
	add r9d, DWORD PTR [rcx]
	andn r14d, ebx, r8d
	add r9d, r14d
	mov r14d, ebp
	and r14d, ebx
	add r9d, r14d
	rorx r14d, eax, 27
	add r9d, r14d
	rorx ebx, ebx, 2
	add r8d, DWORD PTR [rcx+4]
	andn r14d, eax, ebp
	add r8d, r14d
	mov r14d, ebx
	and r14d, eax
	add r8d, r14d
	rorx r14d, r9d, 27
	add r8d, r14d
	rorx eax, eax, 2
	add ebp, DWORD PTR [rcx+8]
	andn r14d, r9d, ebx
	add ebp, r14d
	mov r14d, eax
	and r14d, r9d
	add ebp, r14d
	rorx r14d, r8d, 27
	add ebp, r14d
	rorx r9d, r9d, 2
	add ebx, DWORD PTR [rcx+12]
	andn r14d, r8d, eax
	add ebx, r14d
	mov r14d, r9d
	and r14d, r8d
	add ebx, r14d
	rorx r14d, ebp, 27
	add ebx, r14d
	rorx r8d, r8d, 2
	vpalignr xmm4, xmm1, xmm0, 8
	vpsrldq xmm5, xmm3, 4
	vpxor xmm0, xmm0, xmm2
	vpxor xmm4, xmm4, xmm5
	vpxor xmm0, xmm0, xmm4
	vpsrld xmm5, xmm0, 31
	vpslld xmm0, xmm0, 1
	vpor xmm0, xmm0, xmm5
	vpslldq xmm4, xmm0, 12
	vpsrld xmm5, xmm4, 31
	vpslld xmm4, xmm4, 1
	vpxor xmm0, xmm0, xmm5
	vpxor xmm0, xmm0, xmm4
	vpaddd xmm4, xmm0, xmm8
	vmovdqu XMMWORD PTR [rcx], xmm4
	add eax, DWORD PTR [rcx+16]
	andn r14d, ebp, r9d
	add eax, r14d
	mov r14d, r8d
	and r14d, ebp
	add eax, r14d
	rorx r14d, ebx, 27
	add eax, r14d
	rorx ebp, ebp, 2
	add r9d, DWORD PTR [rcx+20]
	andn r14d, ebx, r8d
	add r9d, r14d
	mov r14d, ebp
	and r14d, ebx
	add r9d, r14d
	rorx r14d, eax, 27
	add r9d, r14d
	rorx ebx, ebx, 2
	add r8d, DWORD PTR [rcx+24]
	andn r14d, eax, ebp
	add r8d, r14d
	mov r14d, ebx
	and r14d, eax
	add r8d, r14d
	rorx r14d, r9d, 27
	add r8d, r14d
	rorx eax, eax, 2
	add ebp, DWORD PTR [rcx+28]
	andn r14d, r9d, ebx
	add ebp, r14d
	mov r14d, eax
	and r14d, r9d
	add ebp, r14d
	rorx r14d, r8d, 27
	add ebp, r14d
	rorx r9d, r9d, 2
	vpalignr xmm4, xmm2, xmm1, 8
	vpsrldq xmm5, xmm0, 4
	vpxor xmm1, xmm1, xmm3
	vpxor xmm4, xmm4, xmm5
	vpxor xmm1, xmm1, xmm4
	vpsrld xmm5, xmm1, 31
	vpslld xmm1, xmm1, 1
	vpor xmm1, xmm1, xmm5
	vpslldq xmm4, xmm1, 12
	vpsrld xmm5, xmm4, 31
	vpslld xmm4, xmm4, 1
	vpxor xmm1, xmm1, xmm5
	vpxor xmm1, xmm1, xmm4
	vpaddd xmm4, xmm1, xmm9
	vmovdqu XMMWORD PTR [rcx+16], xmm4
	add ebx, DWORD PTR [rcx+32]
	andn r14d, r8d, eax
	add ebx, r14d
	mov r14d, r9d
	and r14d, r8d
	add ebx, r14d
	rorx r14d, ebp, 27
	add ebx, r14d
	rorx r8d, r8d, 2
	add eax, DWORD PTR [rcx+36]
	andn r14d, ebp, r9d
	add eax, r14d
	mov r14d, r8d
	and r14d, ebp
	add eax, r14d
	rorx r14d, ebx, 27
	add eax, r14d
	rorx ebp, ebp, 2
	add r9d, DWORD PTR [rcx+40]
	andn r14d, ebx, r8d
	add r9d, r14d
	mov r14d, ebp
	and r14d, ebx
	add r9d, r14d
	rorx r14d, eax, 27
	add r9d, r14d
	rorx ebx, ebx, 2
	add r8d, DWORD PTR [rcx+44]
	andn r14d, eax, ebp
	add r8d, r14d
	mov r14d, ebx
	and r14d, eax
	add r8d, r14d
	rorx r14d, r9d, 27
	add r8d, r14d
	rorx eax, eax, 2
	vpalignr xmm4, xmm3, xmm2, 8
	vpsrldq xmm5, xmm1, 4
	vpxor xmm2, xmm2, xmm0
	vpxor xmm4, xmm4, xmm5
	vpxor xmm2, xmm2, xmm4
	vpsrld xmm5, xmm2, 31
	vpslld xmm2, xmm2, 1
	vpor xmm2, xmm2, xmm5
	vpslldq xmm4, xmm2, 12
	vpsrld xmm5, xmm4, 31
	vpslld xmm4, xmm4, 1
	vpxor xmm2, xmm2, xmm5
	vpxor xmm2, xmm2, xmm4
	vpaddd xmm4, xmm2, xmm9
	vmovdqu XMMWORD PTR [rcx+32], xmm4
	add ebp, DWORD PTR [rcx+48]
	andn r14d, r9d, ebx
	add ebp, r14d
	mov r14d, eax
	and r14d, r9d
	add ebp, r14d
	rorx r14d, r8d, 27
	add ebp, r14d
	rorx r9d, r9d, 2
	add ebx, DWORD PTR [rcx+52]
	andn r14d, r8d, eax
	add ebx, r14d
	mov r14d, r9d
	and r14d, r8d
	add ebx, r14d
	rorx r14d, ebp, 27
	add ebx, r14d
	rorx r8d, r8d, 2
	add eax, DWORD PTR [rcx+56]
	andn r14d, ebp, r9d
	add eax, r14d
	mov r14d, r8d
	and r14d, ebp
	add eax, r14d
	rorx r14d, ebx, 27
	add eax, r14d
	rorx ebp, ebp, 2
	add r9d, DWORD PTR [rcx+60]
	andn r14d, ebx, r8d
	add r9d, r14d
	mov r14d, ebp
	and r14d, ebx
	add r9d, r14d
	rorx r14d, eax, 27
	add r9d, r14d
	rorx ebx, ebx, 2
	vpalignr xmm4, xmm0, xmm3, 8
	vpsrldq xmm5, xmm2, 4
	vpxor xmm3, xmm3, xmm1
	vpxor xmm4, xmm4, xmm5
	vpxor xmm3, xmm3, xmm4
	vpsrld xmm5, xmm3, 31
	vpslld xmm3, xmm3, 1
	vpor xmm3, xmm3, xmm5
	vpslldq xmm4, xmm3, 12
	vpsrld xmm5, xmm4, 31
	vpslld xmm4, xmm4, 1
	vpxor xmm3, xmm3, xmm5
	vpxor xmm3, xmm3, xmm4
	vpaddd xmm4, xmm3, xmm9
	vmovdqu XMMWORD PTR [rcx+48], xmm4
	add r8d, DWORD PTR [rcx]
	andn r14d, eax, ebp
	add r8d, r14d
	mov r14d, ebx
	and r14d, eax
	add r8d, r14d
	rorx r14d, r9d, 27
	add r8d, r14d
	rorx eax, eax, 2
	add ebp, DWORD PTR [rcx+4]
	andn r14d, r9d, ebx
	add ebp, r14d
	mov r14d, eax
	and r14d, r9d
	add ebp, r14d
	rorx r14d, r8d, 27
	add ebp, r14d
	rorx r9d, r9d, 2
	add ebx, DWORD PTR [rcx+8]
	andn r14d, r8d, eax
	add ebx, r14d
	mov r14d, r9d
	and r14d, r8d
	add ebx, r14d
	rorx r14d, ebp, 27
	add ebx, r14d
	rorx r8d, r8d, 2
	add eax, DWORD PTR [rcx+12]
	andn r14d, ebp, r9d
	add eax, r14d
	mov r14d, r8d
	and r14d, ebp
	add eax, r14d
	rorx r14d, ebx, 27
	add eax, r14d
	rorx ebp, ebp, 2
	vpalignr xmm4, xmm1, xmm0, 8
	vpsrldq xmm5, xmm3, 4
	vpxor xmm0, xmm0, xmm2
	vpxor xmm4, xmm4, xmm5
	vpxor xmm0, xmm0, xmm4
	vpsrld xmm5, xmm0, 31
	vpslld xmm0, xmm0, 1
	vpor xmm0, xmm0, xmm5
	vpslldq xmm4, xmm0, 12
	vpsrld xmm5, xmm4, 31
	vpslld xmm4, xmm4, 1
	vpxor xmm0, xmm0, xmm5
	vpxor xmm0, xmm0, xmm4
	vpaddd xmm4, xmm0, xmm9
	vmovdqu XMMWORD PTR [rcx], xmm4
	add r9d, DWORD PTR [rcx+16]
	mov r14d, ebx
	xor r14d, ebp
	xor r14d, r8d
	add r9d, r14d
	rorx r14d, eax, 27
	add r9d, r14d
	rorx ebx, ebx, 2
	add r8d, DWORD PTR [rcx+20]
	mov r14d, eax
	xor r14d, ebx
	xor r14d, ebp
	add r8d, r14d
	rorx r14d, r9d, 27
	add r8d, r14d
	rorx eax, eax, 2
	add ebp, DWORD PTR [rcx+24]
	mov r14d, r9d
	xor r14d, eax
	xor r14d, ebx
	add ebp, r14d
	rorx r14d, r8d, 27
	add ebp, r14d
	rorx r9d, r9d, 2
	add ebx, DWORD PTR [rcx+28]
	mov r14d, r8d
	xor r14d, r9d
	xor r14d, eax
	add ebx, r14d
	rorx r14d, ebp, 27
	add ebx, r14d
	rorx r8d, r8d, 2
	vpalignr xmm4, xmm2, xmm1, 8
	vpsrldq xmm5, xmm0, 4
	vpxor xmm1, xmm1, xmm3
	vpxor xmm4, xmm4, xmm5
	vpxor xmm1, xmm1, xmm4
	vpsrld xmm5, xmm1, 31
	vpslld xmm1, xmm1, 1
	vpor xmm1, xmm1, xmm5
	vpslldq xmm4, xmm1, 12
	vpsrld xmm5, xmm4, 31
	vpslld xmm4, xmm4, 1
	vpxor xmm1, xmm1, xmm5
	vpxor xmm1, xmm1, xmm4
	vpaddd xmm4, xmm1, xmm9
	vmovdqu XMMWORD PTR [rcx+16], xmm4
	add eax, DWORD PTR [rcx+32]
	mov r14d, ebp
	xor r14d, r8d
	xor r14d, r9d
	add eax, r14d
	rorx r14d, ebx, 27
	add eax, r14d
	rorx ebp, ebp, 2
	add r9d, DWORD PTR [rcx+36]
	mov r14d, ebx
	xor r14d, ebp
	xor r14d, r8d
	add r9d, r14d
	rorx r14d, eax, 27
	add r9d, r14d
	rorx ebx, ebx, 2
	add r8d, DWORD PTR [rcx+40]
	mov r14d, eax
	xor r14d, ebx
	xor r14d, ebp
	add r8d, r14d
	rorx r14d, r9d, 27
	add r8d, r14d
	rorx eax, eax, 2
	add ebp, DWORD PTR [rcx+44]
	mov r14d, r9d
	xor r14d, eax
	xor r14d, ebx
	add ebp, r14d
	rorx r14d, r8d, 27
	add ebp, r14d
	rorx r9d, r9d, 2
	vpalignr xmm4, xmm3, xmm2, 8
	vpsrldq xmm5, xmm1, 4
	vpxor xmm2, xmm2, xmm0
	vpxor xmm4, xmm4, xmm5
	vpxor xmm2, xmm2, xmm4
	vpsrld xmm5, xmm2, 31
	vpslld xmm2, xmm2, 1
	vpor xmm2, xmm2, xmm5
	vpslldq xmm4, xmm2, 12
	vpsrld xmm5, xmm4, 31
	vpslld xmm4, xmm4, 1
	vpxor xmm2, xmm2, xmm5
	vpxor xmm2, xmm2, xmm4
	vpaddd xmm4, xmm2, xmm10
	vmovdqu XMMWORD PTR [rcx+32], xmm4
	add ebx, DWORD PTR [rcx+48]
	mov r14d, r8d
	xor r14d, r9d
	xor r14d, eax
	add ebx, r14d
	rorx r14d, ebp, 27
	add ebx, r14d
	rorx r8d, r8d, 2
	add eax, DWORD PTR [rcx+52]
	mov r14d, ebp
	xor r14d, r8d
	xor r14d, r9d
	add eax, r14d
	rorx r14d, ebx, 27
	add eax, r14d
	rorx ebp, ebp, 2
	add r9d, DWORD PTR [rcx+56]
	mov r14d, ebx
	xor r14d, ebp
	xor r14d, r8d
	add r9d, r14d
	rorx r14d, eax, 27
	add r9d, r14d
	rorx ebx, ebx, 2
	add r8d, DWORD PTR [rcx+60]
	mov r14d, eax
	xor r14d, ebx
	xor r14d, ebp
	add r8d, r14d
	rorx r14d, r9d, 27
	add r8d, r14d
	rorx eax, eax, 2
	vpalignr xmm4, xmm0, xmm3, 8
	vpsrldq xmm5, xmm2, 4
	vpxor xmm3, xmm3, xmm1
	vpxor xmm4, xmm4, xmm5
	vpxor xmm3, xmm3, xmm4
	vpsrld xmm5, xmm3, 31
	vpslld xmm3, xmm3, 1
	vpor xmm3, xmm3, xmm5
	vpslldq xmm4, xmm3, 12
	vpsrld xmm5, xmm4, 31
	vpslld xmm4, xmm4, 1
	vpxor xmm3, xmm3, xmm5
	vpxor xmm3, xmm3, xmm4
	vpaddd xmm4, xmm3, xmm10
	vmovdqu XMMWORD PTR [rcx+48], xmm4
	add ebp, DWORD PTR [rcx]
	mov r14d, r9d
	xor r14d, eax
	xor r14d, ebx
	add ebp, r14d
	rorx r14d, r8d, 27
	add ebp, r14d
	rorx r9d, r9d, 2
	add ebx, DWORD PTR [rcx+4]
	mov r14d, r8d
	xor r14d, r9d
	xor r14d, eax
	add ebx, r14d
	rorx r14d, ebp, 27
	add ebx, r14d
	rorx r8d, r8d, 2
	add eax, DWORD PTR [rcx+8]
	mov r14d, ebp
	xor r14d, r8d
	xor r14d, r9d
	add eax, r14d
	rorx r14d, ebx, 27
	add eax, r14d
	rorx ebp, ebp, 2
	add r9d, DWORD PTR [rcx+12]
	mov r14d, ebx
	xor r14d, ebp
	xor r14d, r8d
	add r9d, r14d
	rorx r14d, eax, 27
	add r9d, r14d
	rorx ebx, ebx, 2
	vpalignr xmm4, xmm1, xmm0, 8
	vpsrldq xmm5, xmm3, 4
	vpxor xmm0, xmm0, xmm2
	vpxor xmm4, xmm4, xmm5
	vpxor xmm0, xmm0, xmm4
	vpsrld xmm5, xmm0, 31
	vpslld xmm0, xmm0, 1
	vpor xmm0, xmm0, xmm5
	vpslldq xmm4, xmm0, 12
	vpsrld xmm5, xmm4, 31
	vpslld xmm4, xmm4, 1
	vpxor xmm0, xmm0, xmm5
	vpxor xmm0, xmm0, xmm4
	vpaddd xmm4, xmm0, xmm10
	vmovdqu XMMWORD PTR [rcx], xmm4
	add r8d, DWORD PTR [rcx+16]
	mov r14d, eax
	xor r14d, ebx
	xor r14d, ebp
	add r8d, r14d
	rorx r14d, r9d, 27
	add r8d, r14d
	rorx eax, eax, 2
	add ebp, DWORD PTR [rcx+20]
	mov r14d, r9d
	xor r14d, eax
	xor r14d, ebx
	add ebp, r14d
	rorx r14d, r8d, 27
	add ebp, r14d
	rorx r9d, r9d, 2
	add ebx, DWORD PTR [rcx+24]
	mov r14d, r8d
	xor r14d, r9d
	xor r14d, eax
	add ebx, r14d
	rorx r14d, ebp, 27
	add ebx, r14d
	rorx r8d, r8d, 2
	add eax, DWORD PTR [rcx+28]
	mov r14d, ebp
	xor r14d, r8d
	xor r14d, r9d
	add eax, r14d
	rorx r14d, ebx, 27
	add eax, r14d
	rorx ebp, ebp, 2
	vpalignr xmm4, xmm2, xmm1, 8
	vpsrldq xmm5, xmm0, 4
	vpxor xmm1, xmm1, xmm3
	vpxor xmm4, xmm4, xmm5
	vpxor xmm1, xmm1, xmm4
	vpsrld xmm5, xmm1, 31
	vpslld xmm1, xmm1, 1
	vpor xmm1, xmm1, xmm5
	vpslldq xmm4, xmm1, 12
	vpsrld xmm5, xmm4, 31
	vpslld xmm4, xmm4, 1
	vpxor xmm1, xmm1, xmm5
	vpxor xmm1, xmm1, xmm4
	vpaddd xmm4, xmm1, xmm10
	vmovdqu XMMWORD PTR [rcx+16], xmm4
	add r9d, DWORD PTR [rcx+32]
	mov r14d, ebx
	and r14d, ebp
	add r9d, r14d
	mov r14d, ebx
	xor r14d, ebp
	and r14d, r8d
	add r9d, r14d
	rorx r14d, eax, 27
	add r9d, r14d
	rorx ebx, ebx, 2
	add r8d, DWORD PTR [rcx+36]
	mov r14d, eax
	and r14d, ebx
	add r8d, r14d
	mov r14d, eax
	xor r14d, ebx
	and r14d, ebp
	add r8d, r14d
	rorx r14d, r9d, 27
	add r8d, r14d
	rorx eax, eax, 2
	add ebp, DWORD PTR [rcx+40]
	mov r14d, r9d
	and r14d, eax
	add ebp, r14d
	mov r14d, r9d
	xor r14d, eax
	and r14d, ebx
	add ebp, r14d
	rorx r14d, r8d, 27
	add ebp, r14d
	rorx r9d, r9d, 2
	add ebx, DWORD PTR [rcx+44]
	mov r14d, r8d
	and r14d, r9d
	add ebx, r14d
	mov r14d, r8d
	xor r14d, r9d
	and r14d, eax
	add ebx, r14d
	rorx r14d, ebp, 27
	add ebx, r14d
	rorx r8d, r8d, 2
	vpalignr xmm4, xmm3, xmm2, 8
	vpsrldq xmm5, xmm1, 4
	vpxor xmm2, xmm2, xmm0
	vpxor xmm4, xmm4, xmm5
	vpxor xmm2, xmm2, xmm4
	vpsrld xmm5, xmm2, 31
	vpslld xmm2, xmm2, 1
	vpor xmm2, xmm2, xmm5
	vpslldq xmm4, xmm2, 12
	vpsrld xmm5, xmm4, 31
	vpslld xmm4, xmm4, 1
	vpxor xmm2, xmm2, xmm5
	vpxor xmm2, xmm2, xmm4
	vpaddd xmm4, xmm2, xmm10
	vmovdqu XMMWORD PTR [rcx+32], xmm4
	add eax, DWORD PTR [rcx+48]
	mov r14d, ebp
	and r14d, r8d
	add eax, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r14d, r9d
	add eax, r14d
	rorx r14d, ebx, 27
	add eax, r14d
	rorx ebp, ebp, 2
	add r9d, DWORD PTR [rcx+52]
	mov r14d, ebx
	and r14d, ebp
	add r9d, r14d
	mov r14d, ebx
	xor r14d, ebp
	and r14d, r8d
	add r9d, r14d
	rorx r14d, eax, 27
	add r9d, r14d
	rorx ebx, ebx, 2
	add r8d, DWORD PTR [rcx+56]
	mov r14d, eax
	and r14d, ebx
	add r8d, r14d
	mov r14d, eax
	xor r14d, ebx
	and r14d, ebp
	add r8d, r14d
	rorx r14d, r9d, 27
	add r8d, r14d
	rorx eax, eax, 2
	add ebp, DWORD PTR [rcx+60]
	mov r14d, r9d
	and r14d, eax
	add ebp, r14d
	mov r14d, r9d
	xor r14d, eax
	and r14d, ebx
	add ebp, r14d
	rorx r14d, r8d, 27
	add ebp, r14d
	rorx r9d, r9d, 2
	vpalignr xmm4, xmm0, xmm3, 8
	vpsrldq xmm5, xmm2, 4
	vpxor xmm3, xmm3, xmm1
	vpxor xmm4, xmm4, xmm5
	vpxor xmm3, xmm3, xmm4
	vpsrld xmm5, xmm3, 31
	vpslld xmm3, xmm3, 1
	vpor xmm3, xmm3, xmm5
	vpslldq xmm4, xmm3, 12
	vpsrld xmm5, xmm4, 31
	vpslld xmm4, xmm4, 1
	vpxor xmm3, xmm3, xmm5
	vpxor xmm3, xmm3, xmm4
	vpaddd xmm4, xmm3, xmm11
	vmovdqu XMMWORD PTR [rcx+48], xmm4
	add ebx, DWORD PTR [rcx]
	mov r14d, r8d
	and r14d, r9d
	add ebx, r14d
	mov r14d, r8d
	xor r14d, r9d
	and r14d, eax
	add ebx, r14d
	rorx r14d, ebp, 27
	add ebx, r14d
	rorx r8d, r8d, 2
	add eax, DWORD PTR [rcx+4]
	mov r14d, ebp
	and r14d, r8d
	add eax, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r14d, r9d
	add eax, r14d
	rorx r14d, ebx, 27
	add eax, r14d
	rorx ebp, ebp, 2
	add r9d, DWORD PTR [rcx+8]
	mov r14d, ebx
	and r14d, ebp
	add r9d, r14d
	mov r14d, ebx
	xor r14d, ebp
	and r14d, r8d
	add r9d, r14d
	rorx r14d, eax, 27
	add r9d, r14d
	rorx ebx, ebx, 2
	add r8d, DWORD PTR [rcx+12]
	mov r14d, eax
	and r14d, ebx
	add r8d, r14d
	mov r14d, eax
	xor r14d, ebx
	and r14d, ebp
	add r8d, r14d
	rorx r14d, r9d, 27
	add r8d, r14d
	rorx eax, eax, 2
	vpalignr xmm4, xmm1, xmm0, 8
	vpsrldq xmm5, xmm3, 4
	vpxor xmm0, xmm0, xmm2
	vpxor xmm4, xmm4, xmm5
	vpxor xmm0, xmm0, xmm4
	vpsrld xmm5, xmm0, 31
	vpslld xmm0, xmm0, 1
	vpor xmm0, xmm0, xmm5
	vpslldq xmm4, xmm0, 12
	vpsrld xmm5, xmm4, 31
	vpslld xmm4, xmm4, 1
	vpxor xmm0, xmm0, xmm5
	vpxor xmm0, xmm0, xmm4
	vpaddd xmm4, xmm0, xmm11
	vmovdqu XMMWORD PTR [rcx], xmm4
	add ebp, DWORD PTR [rcx+16]
	mov r14d, r9d
	and r14d, eax
	add ebp, r14d
	mov r14d, r9d
	xor r14d, eax
	and r14d, ebx
	add ebp, r14d
	rorx r14d, r8d, 27
	add ebp, r14d
	rorx r9d, r9d, 2
	add ebx, DWORD PTR [rcx+20]
	mov r14d, r8d
	and r14d, r9d
	add ebx, r14d
	mov r14d, r8d
	xor r14d, r9d
	and r14d, eax
	add ebx, r14d
	rorx r14d, ebp, 27
	add ebx, r14d
	rorx r8d, r8d, 2
	add eax, DWORD PTR [rcx+24]
	mov r14d, ebp
	and r14d, r8d
	add eax, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r14d, r9d
	add eax, r14d
	rorx r14d, ebx, 27
	add eax, r14d
	rorx ebp, ebp, 2
	add r9d, DWORD PTR [rcx+28]
	mov r14d, ebx
	and r14d, ebp
	add r9d, r14d
	mov r14d, ebx
	xor r14d, ebp
	and r14d, r8d
	add r9d, r14d
	rorx r14d, eax, 27
	add r9d, r14d
	rorx ebx, ebx, 2
	vpalignr xmm4, xmm2, xmm1, 8
	vpsrldq xmm5, xmm0, 4
	vpxor xmm1, xmm1, xmm3
	vpxor xmm4, xmm4, xmm5
	vpxor xmm1, xmm1, xmm4
	vpsrld xmm5, xmm1, 31
	vpslld xmm1, xmm1, 1
	vpor xmm1, xmm1, xmm5
	vpslldq xmm4, xmm1, 12
	vpsrld xmm5, xmm4, 31
	vpslld xmm4, xmm4, 1
	vpxor xmm1, xmm1, xmm5
	vpxor xmm1, xmm1, xmm4
	vpaddd xmm4, xmm1, xmm11
	vmovdqu XMMWORD PTR [rcx+16], xmm4
	add r8d, DWORD PTR [rcx+32]
	mov r14d, eax
	and r14d, ebx
	add r8d, r14d
	mov r14d, eax
	xor r14d, ebx
	and r14d, ebp
	add r8d, r14d
	rorx r14d, r9d, 27
	add r8d, r14d
	rorx eax, eax, 2
	add ebp, DWORD PTR [rcx+36]
	mov r14d, r9d
	and r14d, eax
	add ebp, r14d
	mov r14d, r9d
	xor r14d, eax
	and r14d, ebx
	add ebp, r14d
	rorx r14d, r8d, 27
	add ebp, r14d
	rorx r9d, r9d, 2
	add ebx, DWORD PTR [rcx+40]
	mov r14d, r8d
	and r14d, r9d
	add ebx, r14d
	mov r14d, r8d
	xor r14d, r9d
	and r14d, eax
	add ebx, r14d
	rorx r14d, ebp, 27
	add ebx, r14d
	rorx r8d, r8d, 2
	add eax, DWORD PTR [rcx+44]
	mov r14d, ebp
	and r14d, r8d
	add eax, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r14d, r9d
	add eax, r14d
	rorx r14d, ebx, 27
	add eax, r14d
	rorx ebp, ebp, 2
	vpalignr xmm4, xmm3, xmm2, 8
	vpsrldq xmm5, xmm1, 4
	vpxor xmm2, xmm2, xmm0
	vpxor xmm4, xmm4, xmm5
	vpxor xmm2, xmm2, xmm4
	vpsrld xmm5, xmm2, 31
	vpslld xmm2, xmm2, 1
	vpor xmm2, xmm2, xmm5
	vpslldq xmm4, xmm2, 12
	vpsrld xmm5, xmm4, 31
	vpslld xmm4, xmm4, 1
	vpxor xmm2, xmm2, xmm5
	vpxor xmm2, xmm2, xmm4
	vpaddd xmm4, xmm2, xmm11
	vmovdqu XMMWORD PTR [rcx+32], xmm4
	add r9d, DWORD PTR [rcx+48]
	mov r14d, ebx
	xor r14d, ebp
	xor r14d, r8d
	add r9d, r14d
	rorx r14d, eax, 27
	add r9d, r14d
	rorx ebx, ebx, 2
	add r8d, DWORD PTR [rcx+52]
	mov r14d, eax
	xor r14d, ebx
	xor r14d, ebp
	add r8d, r14d
	rorx r14d, r9d, 27
	add r8d, r14d
	rorx eax, eax, 2
	add ebp, DWORD PTR [rcx+56]
	mov r14d, r9d
	xor r14d, eax
	xor r14d, ebx
	add ebp, r14d
	rorx r14d, r8d, 27
	add ebp, r14d
	rorx r9d, r9d, 2
	add ebx, DWORD PTR [rcx+60]
	mov r14d, r8d
	xor r14d, r9d
	xor r14d, eax
	add ebx, r14d
	rorx r14d, ebp, 27
	add ebx, r14d
	rorx r8d, r8d, 2
	vpalignr xmm4, xmm0, xmm3, 8
	vpsrldq xmm5, xmm2, 4
	vpxor xmm3, xmm3, xmm1
	vpxor xmm4, xmm4, xmm5
	vpxor xmm3, xmm3, xmm4
	vpsrld xmm5, xmm3, 31
	vpslld xmm3, xmm3, 1
	vpor xmm3, xmm3, xmm5
	vpslldq xmm4, xmm3, 12
	vpsrld xmm5, xmm4, 31
	vpslld xmm4, xmm4, 1
	vpxor xmm3, xmm3, xmm5
	vpxor xmm3, xmm3, xmm4
	vpaddd xmm4, xmm3, xmm11
	vmovdqu XMMWORD PTR [rcx+48], xmm4
	add eax, DWORD PTR [rcx]
	mov r14d, ebp
	xor r14d, r8d
	xor r14d, r9d
	add eax, r14d
	rorx r14d, ebx, 27
	add eax, r14d
	rorx ebp, ebp, 2
	add r9d, DWORD PTR [rcx+4]
	mov r14d, ebx
	xor r14d, ebp
	xor r14d, r8d
	add r9d, r14d
	rorx r14d, eax, 27
	add r9d, r14d
	rorx ebx, ebx, 2
	add r8d, DWORD PTR [rcx+8]
	mov r14d, eax
	xor r14d, ebx
	xor r14d, ebp
	add r8d, r14d
	rorx r14d, r9d, 27
	add r8d, r14d
	rorx eax, eax, 2
	add ebp, DWORD PTR [rcx+12]
	mov r14d, r9d
	xor r14d, eax
	xor r14d, ebx
	add ebp, r14d
	rorx r14d, r8d, 27
	add ebp, r14d
	rorx r9d, r9d, 2
	add ebx, DWORD PTR [rcx+16]
	mov r14d, r8d
	xor r14d, r9d
	xor r14d, eax
	add ebx, r14d
	rorx r14d, ebp, 27
	add ebx, r14d
	rorx r8d, r8d, 2
	add eax, DWORD PTR [rcx+20]
	mov r14d, ebp
	xor r14d, r8d
	xor r14d, r9d
	add eax, r14d
	rorx r14d, ebx, 27
	add eax, r14d
	rorx ebp, ebp, 2
	add r9d, DWORD PTR [rcx+24]
	mov r14d, ebx
	xor r14d, ebp
	xor r14d, r8d
	add r9d, r14d
	rorx r14d, eax, 27
	add r9d, r14d
	rorx ebx, ebx, 2
	add r8d, DWORD PTR [rcx+28]
	mov r14d, eax
	xor r14d, ebx
	xor r14d, ebp
	add r8d, r14d
	rorx r14d, r9d, 27
	add r8d, r14d
	rorx eax, eax, 2
	add ebp, DWORD PTR [rcx+32]
	mov r14d, r9d
	xor r14d, eax
	xor r14d, ebx
	add ebp, r14d
	rorx r14d, r8d, 27
	add ebp, r14d
	rorx r9d, r9d, 2
	add ebx, DWORD PTR [rcx+36]
	mov r14d, r8d
	xor r14d, r9d
	xor r14d, eax
	add ebx, r14d
	rorx r14d, ebp, 27
	add ebx, r14d
	rorx r8d, r8d, 2
	add eax, DWORD PTR [rcx+40]
	mov r14d, ebp
	xor r14d, r8d
	xor r14d, r9d
	add eax, r14d
	rorx r14d, ebx, 27
	add eax, r14d
	rorx ebp, ebp, 2
	add r9d, DWORD PTR [rcx+44]
	mov r14d, ebx
	xor r14d, ebp
	xor r14d, r8d
	add r9d, r14d
	rorx r14d, eax, 27
	add r9d, r14d
	rorx ebx, ebx, 2
	add r8d, DWORD PTR [rcx+48]
	mov r14d, eax
	xor r14d, ebx
	xor r14d, ebp
	add r8d, r14d
	rorx r14d, r9d, 27
	add r8d, r14d
	rorx eax, eax, 2
	add ebp, DWORD PTR [rcx+52]
	mov r14d, r9d
	xor r14d, eax
	xor r14d, ebx
	add ebp, r14d
	rorx r14d, r8d, 27
	add ebp, r14d
	rorx r9d, r9d, 2
	add ebx, DWORD PTR [rcx+56]
	mov r14d, r8d
	xor r14d, r9d
	xor r14d, eax
	add ebx, r14d
	rorx r14d, ebp, 27
	add ebx, r14d
	rorx r8d, r8d, 2
	add eax, DWORD PTR [rcx+60]
	mov r14d, ebp
	xor r14d, r8d
	xor r14d, r9d
	add eax, r14d
	rorx r14d, ebx, 27
	add eax, r14d
	rorx ebp, ebp, 2
	add eax, DWORD PTR [rdi]
	add ebx, DWORD PTR [rdi+4]
	add ebp, DWORD PTR [rdi+8]
	add r8d, DWORD PTR [rdi+12]
	add r9d, DWORD PTR [rdi+16]
	mov DWORD PTR [rdi], eax
	mov DWORD PTR [rdi+4], ebx
	mov DWORD PTR [rdi+8], ebp
	mov DWORD PTR [rdi+12], r8d
	mov DWORD PTR [rdi+16], r9d
	add rsi, 64
	sub rdx, 1
	jne 22b
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [rcx+64]
	mov rbp, QWORD PTR [rcx+72]
	mov r12, QWORD PTR [rcx+80]
	mov r13, QWORD PTR [rcx+88]
	mov r14, QWORD PTR [rcx+96]
	mov r15, QWORD PTR [rcx+104]
	ret
	.p2align 6
