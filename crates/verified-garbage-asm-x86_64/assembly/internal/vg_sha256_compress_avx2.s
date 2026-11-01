// The functions of `src/internal/vg_sha256_compress_avx2.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha256_compress_avx2:
	mov QWORD PTR [rcx+512], rbx
	mov QWORD PTR [rcx+520], rbp
	mov QWORD PTR [rcx+528], r12
	mov QWORD PTR [rcx+536], r13
	mov QWORD PTR [rcx+544], r14
	mov QWORD PTR [rcx+552], r15
	movabs rax, 289644378169868803
	vmovq xmm10, rax
	movabs rax, 868365760874482187
	vmovq xmm11, rax
	vpunpcklqdq xmm10, xmm10, xmm11
	vinserti128 ymm10, ymm10, xmm10, 1
	movabs rax, 795458214199165184
	vmovq xmm8, rax
	movabs rax, -1
	vmovq xmm11, rax
	vpunpcklqdq xmm8, xmm8, xmm11
	vinserti128 ymm8, ymm8, xmm8, 1
	movabs rax, -1
	vmovq xmm9, rax
	movabs rax, 795458214199165184
	vmovq xmm11, rax
	vpunpcklqdq xmm9, xmm9, xmm11
	vinserti128 ymm9, ymm9, xmm9, 1
	test rdx, rdx
	je 20f
22:
	mov r15, rsi
	cmp rdx, 1
	je 23f
	add r15, 64
	jmp 24f
23:
24:
	vmovdqu xmm0, XMMWORD PTR [rsi]
	vmovdqu xmm11, XMMWORD PTR [r15]
	vinserti128 ymm0, ymm0, xmm11, 1
	vpshufb ymm0, ymm0, ymm10
	vmovdqu YMMWORD PTR [rcx], ymm0
	vmovdqu xmm1, XMMWORD PTR [rsi+16]
	vmovdqu xmm11, XMMWORD PTR [r15+16]
	vinserti128 ymm1, ymm1, xmm11, 1
	vpshufb ymm1, ymm1, ymm10
	vmovdqu YMMWORD PTR [rcx+32], ymm1
	vmovdqu xmm2, XMMWORD PTR [rsi+32]
	vmovdqu xmm11, XMMWORD PTR [r15+32]
	vinserti128 ymm2, ymm2, xmm11, 1
	vpshufb ymm2, ymm2, ymm10
	vmovdqu YMMWORD PTR [rcx+64], ymm2
	vmovdqu xmm3, XMMWORD PTR [rsi+48]
	vmovdqu xmm11, XMMWORD PTR [r15+48]
	vinserti128 ymm3, ymm3, xmm11, 1
	vpshufb ymm3, ymm3, ymm10
	vmovdqu YMMWORD PTR [rcx+96], ymm3
	mov eax, DWORD PTR [rdi]
	mov ebx, DWORD PTR [rdi+4]
	mov ebp, DWORD PTR [rdi+8]
	mov r8d, DWORD PTR [rdi+12]
	mov r9d, DWORD PTR [rdi+16]
	mov r10d, DWORD PTR [rdi+20]
	mov r11d, DWORD PTR [rdi+24]
	mov r12d, DWORD PTR [rdi+28]
	mov r13d, ebx
	xor r13d, ebp
	vpalignr ymm4, ymm1, ymm0, 4
	vpalignr ymm7, ymm3, ymm2, 4
	vpsrld ymm6, ymm4, 7
	vpaddd ymm0, ymm0, ymm7
	vpsrld ymm7, ymm4, 3
	vpslld ymm5, ymm4, 14
	vpxor ymm4, ymm7, ymm6
	vpshufd ymm7, ymm3, 250
	vpsrld ymm6, ymm6, 11
	vpxor ymm4, ymm4, ymm5
	vpslld ymm5, ymm5, 11
	vpxor ymm4, ymm4, ymm6
	vpsrld ymm6, ymm7, 10
	vpxor ymm4, ymm4, ymm5
	vpsrlq ymm7, ymm7, 17
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm8
	vpaddd ymm0, ymm0, ymm6
	vpshufd ymm7, ymm0, 80
	vpsrld ymm6, ymm7, 10
	vpsrlq ymm7, ymm7, 17
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm9
	vpaddd ymm0, ymm0, ymm6
	vmovdqu YMMWORD PTR [rcx+128], ymm0
	add r12d, 1116352408
	add r12d, DWORD PTR [rcx]
	andn r15d, r9d, r11d
	add r12d, r15d
	mov r14d, r9d
	and r14d, r10d
	add r12d, r14d
	rorx r14d, r9d, 6
	rorx r15d, r9d, 11
	xor r14d, r15d
	rorx r15d, r9d, 25
	xor r14d, r15d
	add r12d, r14d
	add r8d, r12d
	rorx r14d, eax, 2
	rorx r15d, eax, 13
	xor r14d, r15d
	rorx r15d, eax, 22
	xor r14d, r15d
	add r12d, r14d
	mov r14d, eax
	xor r14d, ebx
	and r13d, r14d
	xor r13d, ebx
	add r12d, r13d
	add r11d, 1899447441
	add r11d, DWORD PTR [rcx+4]
	andn r15d, r8d, r10d
	add r11d, r15d
	mov r13d, r8d
	and r13d, r9d
	add r11d, r13d
	rorx r13d, r8d, 6
	rorx r15d, r8d, 11
	xor r13d, r15d
	rorx r15d, r8d, 25
	xor r13d, r15d
	add r11d, r13d
	add ebp, r11d
	rorx r13d, r12d, 2
	rorx r15d, r12d, 13
	xor r13d, r15d
	rorx r15d, r12d, 22
	xor r13d, r15d
	add r11d, r13d
	mov r13d, r12d
	xor r13d, eax
	and r14d, r13d
	xor r14d, eax
	add r11d, r14d
	add r10d, -1245643825
	add r10d, DWORD PTR [rcx+8]
	andn r15d, ebp, r9d
	add r10d, r15d
	mov r14d, ebp
	and r14d, r8d
	add r10d, r14d
	rorx r14d, ebp, 6
	rorx r15d, ebp, 11
	xor r14d, r15d
	rorx r15d, ebp, 25
	xor r14d, r15d
	add r10d, r14d
	add ebx, r10d
	rorx r14d, r11d, 2
	rorx r15d, r11d, 13
	xor r14d, r15d
	rorx r15d, r11d, 22
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r11d
	xor r14d, r12d
	and r13d, r14d
	xor r13d, r12d
	add r10d, r13d
	add r9d, -373957723
	add r9d, DWORD PTR [rcx+12]
	andn r15d, ebx, r8d
	add r9d, r15d
	mov r13d, ebx
	and r13d, ebp
	add r9d, r13d
	rorx r13d, ebx, 6
	rorx r15d, ebx, 11
	xor r13d, r15d
	rorx r15d, ebx, 25
	xor r13d, r15d
	add r9d, r13d
	add eax, r9d
	rorx r13d, r10d, 2
	rorx r15d, r10d, 13
	xor r13d, r15d
	rorx r15d, r10d, 22
	xor r13d, r15d
	add r9d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r14d, r13d
	xor r14d, r11d
	add r9d, r14d
	vpalignr ymm4, ymm2, ymm1, 4
	vpalignr ymm7, ymm0, ymm3, 4
	vpsrld ymm6, ymm4, 7
	vpaddd ymm1, ymm1, ymm7
	vpsrld ymm7, ymm4, 3
	vpslld ymm5, ymm4, 14
	vpxor ymm4, ymm7, ymm6
	vpshufd ymm7, ymm0, 250
	vpsrld ymm6, ymm6, 11
	vpxor ymm4, ymm4, ymm5
	vpslld ymm5, ymm5, 11
	vpxor ymm4, ymm4, ymm6
	vpsrld ymm6, ymm7, 10
	vpxor ymm4, ymm4, ymm5
	vpsrlq ymm7, ymm7, 17
	vpaddd ymm1, ymm1, ymm4
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm8
	vpaddd ymm1, ymm1, ymm6
	vpshufd ymm7, ymm1, 80
	vpsrld ymm6, ymm7, 10
	vpsrlq ymm7, ymm7, 17
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm9
	vpaddd ymm1, ymm1, ymm6
	vmovdqu YMMWORD PTR [rcx+160], ymm1
	add r8d, 961987163
	add r8d, DWORD PTR [rcx+32]
	andn r15d, eax, ebp
	add r8d, r15d
	mov r14d, eax
	and r14d, ebx
	add r8d, r14d
	rorx r14d, eax, 6
	rorx r15d, eax, 11
	xor r14d, r15d
	rorx r15d, eax, 25
	xor r14d, r15d
	add r8d, r14d
	add r12d, r8d
	rorx r14d, r9d, 2
	rorx r15d, r9d, 13
	xor r14d, r15d
	rorx r15d, r9d, 22
	xor r14d, r15d
	add r8d, r14d
	mov r14d, r9d
	xor r14d, r10d
	and r13d, r14d
	xor r13d, r10d
	add r8d, r13d
	add ebp, 1508970993
	add ebp, DWORD PTR [rcx+36]
	andn r15d, r12d, ebx
	add ebp, r15d
	mov r13d, r12d
	and r13d, eax
	add ebp, r13d
	rorx r13d, r12d, 6
	rorx r15d, r12d, 11
	xor r13d, r15d
	rorx r15d, r12d, 25
	xor r13d, r15d
	add ebp, r13d
	add r11d, ebp
	rorx r13d, r8d, 2
	rorx r15d, r8d, 13
	xor r13d, r15d
	rorx r15d, r8d, 22
	xor r13d, r15d
	add ebp, r13d
	mov r13d, r8d
	xor r13d, r9d
	and r14d, r13d
	xor r14d, r9d
	add ebp, r14d
	add ebx, -1841331548
	add ebx, DWORD PTR [rcx+40]
	andn r15d, r11d, eax
	add ebx, r15d
	mov r14d, r11d
	and r14d, r12d
	add ebx, r14d
	rorx r14d, r11d, 6
	rorx r15d, r11d, 11
	xor r14d, r15d
	rorx r15d, r11d, 25
	xor r14d, r15d
	add ebx, r14d
	add r10d, ebx
	rorx r14d, ebp, 2
	rorx r15d, ebp, 13
	xor r14d, r15d
	rorx r15d, ebp, 22
	xor r14d, r15d
	add ebx, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r13d, r14d
	xor r13d, r8d
	add ebx, r13d
	add eax, -1424204075
	add eax, DWORD PTR [rcx+44]
	andn r15d, r10d, r12d
	add eax, r15d
	mov r13d, r10d
	and r13d, r11d
	add eax, r13d
	rorx r13d, r10d, 6
	rorx r15d, r10d, 11
	xor r13d, r15d
	rorx r15d, r10d, 25
	xor r13d, r15d
	add eax, r13d
	add r9d, eax
	rorx r13d, ebx, 2
	rorx r15d, ebx, 13
	xor r13d, r15d
	rorx r15d, ebx, 22
	xor r13d, r15d
	add eax, r13d
	mov r13d, ebx
	xor r13d, ebp
	and r14d, r13d
	xor r14d, ebp
	add eax, r14d
	vpalignr ymm4, ymm3, ymm2, 4
	vpalignr ymm7, ymm1, ymm0, 4
	vpsrld ymm6, ymm4, 7
	vpaddd ymm2, ymm2, ymm7
	vpsrld ymm7, ymm4, 3
	vpslld ymm5, ymm4, 14
	vpxor ymm4, ymm7, ymm6
	vpshufd ymm7, ymm1, 250
	vpsrld ymm6, ymm6, 11
	vpxor ymm4, ymm4, ymm5
	vpslld ymm5, ymm5, 11
	vpxor ymm4, ymm4, ymm6
	vpsrld ymm6, ymm7, 10
	vpxor ymm4, ymm4, ymm5
	vpsrlq ymm7, ymm7, 17
	vpaddd ymm2, ymm2, ymm4
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm8
	vpaddd ymm2, ymm2, ymm6
	vpshufd ymm7, ymm2, 80
	vpsrld ymm6, ymm7, 10
	vpsrlq ymm7, ymm7, 17
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm9
	vpaddd ymm2, ymm2, ymm6
	vmovdqu YMMWORD PTR [rcx+192], ymm2
	add r12d, -670586216
	add r12d, DWORD PTR [rcx+64]
	andn r15d, r9d, r11d
	add r12d, r15d
	mov r14d, r9d
	and r14d, r10d
	add r12d, r14d
	rorx r14d, r9d, 6
	rorx r15d, r9d, 11
	xor r14d, r15d
	rorx r15d, r9d, 25
	xor r14d, r15d
	add r12d, r14d
	add r8d, r12d
	rorx r14d, eax, 2
	rorx r15d, eax, 13
	xor r14d, r15d
	rorx r15d, eax, 22
	xor r14d, r15d
	add r12d, r14d
	mov r14d, eax
	xor r14d, ebx
	and r13d, r14d
	xor r13d, ebx
	add r12d, r13d
	add r11d, 310598401
	add r11d, DWORD PTR [rcx+68]
	andn r15d, r8d, r10d
	add r11d, r15d
	mov r13d, r8d
	and r13d, r9d
	add r11d, r13d
	rorx r13d, r8d, 6
	rorx r15d, r8d, 11
	xor r13d, r15d
	rorx r15d, r8d, 25
	xor r13d, r15d
	add r11d, r13d
	add ebp, r11d
	rorx r13d, r12d, 2
	rorx r15d, r12d, 13
	xor r13d, r15d
	rorx r15d, r12d, 22
	xor r13d, r15d
	add r11d, r13d
	mov r13d, r12d
	xor r13d, eax
	and r14d, r13d
	xor r14d, eax
	add r11d, r14d
	add r10d, 607225278
	add r10d, DWORD PTR [rcx+72]
	andn r15d, ebp, r9d
	add r10d, r15d
	mov r14d, ebp
	and r14d, r8d
	add r10d, r14d
	rorx r14d, ebp, 6
	rorx r15d, ebp, 11
	xor r14d, r15d
	rorx r15d, ebp, 25
	xor r14d, r15d
	add r10d, r14d
	add ebx, r10d
	rorx r14d, r11d, 2
	rorx r15d, r11d, 13
	xor r14d, r15d
	rorx r15d, r11d, 22
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r11d
	xor r14d, r12d
	and r13d, r14d
	xor r13d, r12d
	add r10d, r13d
	add r9d, 1426881987
	add r9d, DWORD PTR [rcx+76]
	andn r15d, ebx, r8d
	add r9d, r15d
	mov r13d, ebx
	and r13d, ebp
	add r9d, r13d
	rorx r13d, ebx, 6
	rorx r15d, ebx, 11
	xor r13d, r15d
	rorx r15d, ebx, 25
	xor r13d, r15d
	add r9d, r13d
	add eax, r9d
	rorx r13d, r10d, 2
	rorx r15d, r10d, 13
	xor r13d, r15d
	rorx r15d, r10d, 22
	xor r13d, r15d
	add r9d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r14d, r13d
	xor r14d, r11d
	add r9d, r14d
	vpalignr ymm4, ymm0, ymm3, 4
	vpalignr ymm7, ymm2, ymm1, 4
	vpsrld ymm6, ymm4, 7
	vpaddd ymm3, ymm3, ymm7
	vpsrld ymm7, ymm4, 3
	vpslld ymm5, ymm4, 14
	vpxor ymm4, ymm7, ymm6
	vpshufd ymm7, ymm2, 250
	vpsrld ymm6, ymm6, 11
	vpxor ymm4, ymm4, ymm5
	vpslld ymm5, ymm5, 11
	vpxor ymm4, ymm4, ymm6
	vpsrld ymm6, ymm7, 10
	vpxor ymm4, ymm4, ymm5
	vpsrlq ymm7, ymm7, 17
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm8
	vpaddd ymm3, ymm3, ymm6
	vpshufd ymm7, ymm3, 80
	vpsrld ymm6, ymm7, 10
	vpsrlq ymm7, ymm7, 17
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm9
	vpaddd ymm3, ymm3, ymm6
	vmovdqu YMMWORD PTR [rcx+224], ymm3
	add r8d, 1925078388
	add r8d, DWORD PTR [rcx+96]
	andn r15d, eax, ebp
	add r8d, r15d
	mov r14d, eax
	and r14d, ebx
	add r8d, r14d
	rorx r14d, eax, 6
	rorx r15d, eax, 11
	xor r14d, r15d
	rorx r15d, eax, 25
	xor r14d, r15d
	add r8d, r14d
	add r12d, r8d
	rorx r14d, r9d, 2
	rorx r15d, r9d, 13
	xor r14d, r15d
	rorx r15d, r9d, 22
	xor r14d, r15d
	add r8d, r14d
	mov r14d, r9d
	xor r14d, r10d
	and r13d, r14d
	xor r13d, r10d
	add r8d, r13d
	add ebp, -2132889090
	add ebp, DWORD PTR [rcx+100]
	andn r15d, r12d, ebx
	add ebp, r15d
	mov r13d, r12d
	and r13d, eax
	add ebp, r13d
	rorx r13d, r12d, 6
	rorx r15d, r12d, 11
	xor r13d, r15d
	rorx r15d, r12d, 25
	xor r13d, r15d
	add ebp, r13d
	add r11d, ebp
	rorx r13d, r8d, 2
	rorx r15d, r8d, 13
	xor r13d, r15d
	rorx r15d, r8d, 22
	xor r13d, r15d
	add ebp, r13d
	mov r13d, r8d
	xor r13d, r9d
	and r14d, r13d
	xor r14d, r9d
	add ebp, r14d
	add ebx, -1680079193
	add ebx, DWORD PTR [rcx+104]
	andn r15d, r11d, eax
	add ebx, r15d
	mov r14d, r11d
	and r14d, r12d
	add ebx, r14d
	rorx r14d, r11d, 6
	rorx r15d, r11d, 11
	xor r14d, r15d
	rorx r15d, r11d, 25
	xor r14d, r15d
	add ebx, r14d
	add r10d, ebx
	rorx r14d, ebp, 2
	rorx r15d, ebp, 13
	xor r14d, r15d
	rorx r15d, ebp, 22
	xor r14d, r15d
	add ebx, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r13d, r14d
	xor r13d, r8d
	add ebx, r13d
	add eax, -1046744716
	add eax, DWORD PTR [rcx+108]
	andn r15d, r10d, r12d
	add eax, r15d
	mov r13d, r10d
	and r13d, r11d
	add eax, r13d
	rorx r13d, r10d, 6
	rorx r15d, r10d, 11
	xor r13d, r15d
	rorx r15d, r10d, 25
	xor r13d, r15d
	add eax, r13d
	add r9d, eax
	rorx r13d, ebx, 2
	rorx r15d, ebx, 13
	xor r13d, r15d
	rorx r15d, ebx, 22
	xor r13d, r15d
	add eax, r13d
	mov r13d, ebx
	xor r13d, ebp
	and r14d, r13d
	xor r14d, ebp
	add eax, r14d
	vpalignr ymm4, ymm1, ymm0, 4
	vpalignr ymm7, ymm3, ymm2, 4
	vpsrld ymm6, ymm4, 7
	vpaddd ymm0, ymm0, ymm7
	vpsrld ymm7, ymm4, 3
	vpslld ymm5, ymm4, 14
	vpxor ymm4, ymm7, ymm6
	vpshufd ymm7, ymm3, 250
	vpsrld ymm6, ymm6, 11
	vpxor ymm4, ymm4, ymm5
	vpslld ymm5, ymm5, 11
	vpxor ymm4, ymm4, ymm6
	vpsrld ymm6, ymm7, 10
	vpxor ymm4, ymm4, ymm5
	vpsrlq ymm7, ymm7, 17
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm8
	vpaddd ymm0, ymm0, ymm6
	vpshufd ymm7, ymm0, 80
	vpsrld ymm6, ymm7, 10
	vpsrlq ymm7, ymm7, 17
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm9
	vpaddd ymm0, ymm0, ymm6
	vmovdqu YMMWORD PTR [rcx+256], ymm0
	add r12d, -459576895
	add r12d, DWORD PTR [rcx+128]
	andn r15d, r9d, r11d
	add r12d, r15d
	mov r14d, r9d
	and r14d, r10d
	add r12d, r14d
	rorx r14d, r9d, 6
	rorx r15d, r9d, 11
	xor r14d, r15d
	rorx r15d, r9d, 25
	xor r14d, r15d
	add r12d, r14d
	add r8d, r12d
	rorx r14d, eax, 2
	rorx r15d, eax, 13
	xor r14d, r15d
	rorx r15d, eax, 22
	xor r14d, r15d
	add r12d, r14d
	mov r14d, eax
	xor r14d, ebx
	and r13d, r14d
	xor r13d, ebx
	add r12d, r13d
	add r11d, -272742522
	add r11d, DWORD PTR [rcx+132]
	andn r15d, r8d, r10d
	add r11d, r15d
	mov r13d, r8d
	and r13d, r9d
	add r11d, r13d
	rorx r13d, r8d, 6
	rorx r15d, r8d, 11
	xor r13d, r15d
	rorx r15d, r8d, 25
	xor r13d, r15d
	add r11d, r13d
	add ebp, r11d
	rorx r13d, r12d, 2
	rorx r15d, r12d, 13
	xor r13d, r15d
	rorx r15d, r12d, 22
	xor r13d, r15d
	add r11d, r13d
	mov r13d, r12d
	xor r13d, eax
	and r14d, r13d
	xor r14d, eax
	add r11d, r14d
	add r10d, 264347078
	add r10d, DWORD PTR [rcx+136]
	andn r15d, ebp, r9d
	add r10d, r15d
	mov r14d, ebp
	and r14d, r8d
	add r10d, r14d
	rorx r14d, ebp, 6
	rorx r15d, ebp, 11
	xor r14d, r15d
	rorx r15d, ebp, 25
	xor r14d, r15d
	add r10d, r14d
	add ebx, r10d
	rorx r14d, r11d, 2
	rorx r15d, r11d, 13
	xor r14d, r15d
	rorx r15d, r11d, 22
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r11d
	xor r14d, r12d
	and r13d, r14d
	xor r13d, r12d
	add r10d, r13d
	add r9d, 604807628
	add r9d, DWORD PTR [rcx+140]
	andn r15d, ebx, r8d
	add r9d, r15d
	mov r13d, ebx
	and r13d, ebp
	add r9d, r13d
	rorx r13d, ebx, 6
	rorx r15d, ebx, 11
	xor r13d, r15d
	rorx r15d, ebx, 25
	xor r13d, r15d
	add r9d, r13d
	add eax, r9d
	rorx r13d, r10d, 2
	rorx r15d, r10d, 13
	xor r13d, r15d
	rorx r15d, r10d, 22
	xor r13d, r15d
	add r9d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r14d, r13d
	xor r14d, r11d
	add r9d, r14d
	vpalignr ymm4, ymm2, ymm1, 4
	vpalignr ymm7, ymm0, ymm3, 4
	vpsrld ymm6, ymm4, 7
	vpaddd ymm1, ymm1, ymm7
	vpsrld ymm7, ymm4, 3
	vpslld ymm5, ymm4, 14
	vpxor ymm4, ymm7, ymm6
	vpshufd ymm7, ymm0, 250
	vpsrld ymm6, ymm6, 11
	vpxor ymm4, ymm4, ymm5
	vpslld ymm5, ymm5, 11
	vpxor ymm4, ymm4, ymm6
	vpsrld ymm6, ymm7, 10
	vpxor ymm4, ymm4, ymm5
	vpsrlq ymm7, ymm7, 17
	vpaddd ymm1, ymm1, ymm4
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm8
	vpaddd ymm1, ymm1, ymm6
	vpshufd ymm7, ymm1, 80
	vpsrld ymm6, ymm7, 10
	vpsrlq ymm7, ymm7, 17
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm9
	vpaddd ymm1, ymm1, ymm6
	vmovdqu YMMWORD PTR [rcx+288], ymm1
	add r8d, 770255983
	add r8d, DWORD PTR [rcx+160]
	andn r15d, eax, ebp
	add r8d, r15d
	mov r14d, eax
	and r14d, ebx
	add r8d, r14d
	rorx r14d, eax, 6
	rorx r15d, eax, 11
	xor r14d, r15d
	rorx r15d, eax, 25
	xor r14d, r15d
	add r8d, r14d
	add r12d, r8d
	rorx r14d, r9d, 2
	rorx r15d, r9d, 13
	xor r14d, r15d
	rorx r15d, r9d, 22
	xor r14d, r15d
	add r8d, r14d
	mov r14d, r9d
	xor r14d, r10d
	and r13d, r14d
	xor r13d, r10d
	add r8d, r13d
	add ebp, 1249150122
	add ebp, DWORD PTR [rcx+164]
	andn r15d, r12d, ebx
	add ebp, r15d
	mov r13d, r12d
	and r13d, eax
	add ebp, r13d
	rorx r13d, r12d, 6
	rorx r15d, r12d, 11
	xor r13d, r15d
	rorx r15d, r12d, 25
	xor r13d, r15d
	add ebp, r13d
	add r11d, ebp
	rorx r13d, r8d, 2
	rorx r15d, r8d, 13
	xor r13d, r15d
	rorx r15d, r8d, 22
	xor r13d, r15d
	add ebp, r13d
	mov r13d, r8d
	xor r13d, r9d
	and r14d, r13d
	xor r14d, r9d
	add ebp, r14d
	add ebx, 1555081692
	add ebx, DWORD PTR [rcx+168]
	andn r15d, r11d, eax
	add ebx, r15d
	mov r14d, r11d
	and r14d, r12d
	add ebx, r14d
	rorx r14d, r11d, 6
	rorx r15d, r11d, 11
	xor r14d, r15d
	rorx r15d, r11d, 25
	xor r14d, r15d
	add ebx, r14d
	add r10d, ebx
	rorx r14d, ebp, 2
	rorx r15d, ebp, 13
	xor r14d, r15d
	rorx r15d, ebp, 22
	xor r14d, r15d
	add ebx, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r13d, r14d
	xor r13d, r8d
	add ebx, r13d
	add eax, 1996064986
	add eax, DWORD PTR [rcx+172]
	andn r15d, r10d, r12d
	add eax, r15d
	mov r13d, r10d
	and r13d, r11d
	add eax, r13d
	rorx r13d, r10d, 6
	rorx r15d, r10d, 11
	xor r13d, r15d
	rorx r15d, r10d, 25
	xor r13d, r15d
	add eax, r13d
	add r9d, eax
	rorx r13d, ebx, 2
	rorx r15d, ebx, 13
	xor r13d, r15d
	rorx r15d, ebx, 22
	xor r13d, r15d
	add eax, r13d
	mov r13d, ebx
	xor r13d, ebp
	and r14d, r13d
	xor r14d, ebp
	add eax, r14d
	vpalignr ymm4, ymm3, ymm2, 4
	vpalignr ymm7, ymm1, ymm0, 4
	vpsrld ymm6, ymm4, 7
	vpaddd ymm2, ymm2, ymm7
	vpsrld ymm7, ymm4, 3
	vpslld ymm5, ymm4, 14
	vpxor ymm4, ymm7, ymm6
	vpshufd ymm7, ymm1, 250
	vpsrld ymm6, ymm6, 11
	vpxor ymm4, ymm4, ymm5
	vpslld ymm5, ymm5, 11
	vpxor ymm4, ymm4, ymm6
	vpsrld ymm6, ymm7, 10
	vpxor ymm4, ymm4, ymm5
	vpsrlq ymm7, ymm7, 17
	vpaddd ymm2, ymm2, ymm4
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm8
	vpaddd ymm2, ymm2, ymm6
	vpshufd ymm7, ymm2, 80
	vpsrld ymm6, ymm7, 10
	vpsrlq ymm7, ymm7, 17
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm9
	vpaddd ymm2, ymm2, ymm6
	vmovdqu YMMWORD PTR [rcx+320], ymm2
	add r12d, -1740746414
	add r12d, DWORD PTR [rcx+192]
	andn r15d, r9d, r11d
	add r12d, r15d
	mov r14d, r9d
	and r14d, r10d
	add r12d, r14d
	rorx r14d, r9d, 6
	rorx r15d, r9d, 11
	xor r14d, r15d
	rorx r15d, r9d, 25
	xor r14d, r15d
	add r12d, r14d
	add r8d, r12d
	rorx r14d, eax, 2
	rorx r15d, eax, 13
	xor r14d, r15d
	rorx r15d, eax, 22
	xor r14d, r15d
	add r12d, r14d
	mov r14d, eax
	xor r14d, ebx
	and r13d, r14d
	xor r13d, ebx
	add r12d, r13d
	add r11d, -1473132947
	add r11d, DWORD PTR [rcx+196]
	andn r15d, r8d, r10d
	add r11d, r15d
	mov r13d, r8d
	and r13d, r9d
	add r11d, r13d
	rorx r13d, r8d, 6
	rorx r15d, r8d, 11
	xor r13d, r15d
	rorx r15d, r8d, 25
	xor r13d, r15d
	add r11d, r13d
	add ebp, r11d
	rorx r13d, r12d, 2
	rorx r15d, r12d, 13
	xor r13d, r15d
	rorx r15d, r12d, 22
	xor r13d, r15d
	add r11d, r13d
	mov r13d, r12d
	xor r13d, eax
	and r14d, r13d
	xor r14d, eax
	add r11d, r14d
	add r10d, -1341970488
	add r10d, DWORD PTR [rcx+200]
	andn r15d, ebp, r9d
	add r10d, r15d
	mov r14d, ebp
	and r14d, r8d
	add r10d, r14d
	rorx r14d, ebp, 6
	rorx r15d, ebp, 11
	xor r14d, r15d
	rorx r15d, ebp, 25
	xor r14d, r15d
	add r10d, r14d
	add ebx, r10d
	rorx r14d, r11d, 2
	rorx r15d, r11d, 13
	xor r14d, r15d
	rorx r15d, r11d, 22
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r11d
	xor r14d, r12d
	and r13d, r14d
	xor r13d, r12d
	add r10d, r13d
	add r9d, -1084653625
	add r9d, DWORD PTR [rcx+204]
	andn r15d, ebx, r8d
	add r9d, r15d
	mov r13d, ebx
	and r13d, ebp
	add r9d, r13d
	rorx r13d, ebx, 6
	rorx r15d, ebx, 11
	xor r13d, r15d
	rorx r15d, ebx, 25
	xor r13d, r15d
	add r9d, r13d
	add eax, r9d
	rorx r13d, r10d, 2
	rorx r15d, r10d, 13
	xor r13d, r15d
	rorx r15d, r10d, 22
	xor r13d, r15d
	add r9d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r14d, r13d
	xor r14d, r11d
	add r9d, r14d
	vpalignr ymm4, ymm0, ymm3, 4
	vpalignr ymm7, ymm2, ymm1, 4
	vpsrld ymm6, ymm4, 7
	vpaddd ymm3, ymm3, ymm7
	vpsrld ymm7, ymm4, 3
	vpslld ymm5, ymm4, 14
	vpxor ymm4, ymm7, ymm6
	vpshufd ymm7, ymm2, 250
	vpsrld ymm6, ymm6, 11
	vpxor ymm4, ymm4, ymm5
	vpslld ymm5, ymm5, 11
	vpxor ymm4, ymm4, ymm6
	vpsrld ymm6, ymm7, 10
	vpxor ymm4, ymm4, ymm5
	vpsrlq ymm7, ymm7, 17
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm8
	vpaddd ymm3, ymm3, ymm6
	vpshufd ymm7, ymm3, 80
	vpsrld ymm6, ymm7, 10
	vpsrlq ymm7, ymm7, 17
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm9
	vpaddd ymm3, ymm3, ymm6
	vmovdqu YMMWORD PTR [rcx+352], ymm3
	add r8d, -958395405
	add r8d, DWORD PTR [rcx+224]
	andn r15d, eax, ebp
	add r8d, r15d
	mov r14d, eax
	and r14d, ebx
	add r8d, r14d
	rorx r14d, eax, 6
	rorx r15d, eax, 11
	xor r14d, r15d
	rorx r15d, eax, 25
	xor r14d, r15d
	add r8d, r14d
	add r12d, r8d
	rorx r14d, r9d, 2
	rorx r15d, r9d, 13
	xor r14d, r15d
	rorx r15d, r9d, 22
	xor r14d, r15d
	add r8d, r14d
	mov r14d, r9d
	xor r14d, r10d
	and r13d, r14d
	xor r13d, r10d
	add r8d, r13d
	add ebp, -710438585
	add ebp, DWORD PTR [rcx+228]
	andn r15d, r12d, ebx
	add ebp, r15d
	mov r13d, r12d
	and r13d, eax
	add ebp, r13d
	rorx r13d, r12d, 6
	rorx r15d, r12d, 11
	xor r13d, r15d
	rorx r15d, r12d, 25
	xor r13d, r15d
	add ebp, r13d
	add r11d, ebp
	rorx r13d, r8d, 2
	rorx r15d, r8d, 13
	xor r13d, r15d
	rorx r15d, r8d, 22
	xor r13d, r15d
	add ebp, r13d
	mov r13d, r8d
	xor r13d, r9d
	and r14d, r13d
	xor r14d, r9d
	add ebp, r14d
	add ebx, 113926993
	add ebx, DWORD PTR [rcx+232]
	andn r15d, r11d, eax
	add ebx, r15d
	mov r14d, r11d
	and r14d, r12d
	add ebx, r14d
	rorx r14d, r11d, 6
	rorx r15d, r11d, 11
	xor r14d, r15d
	rorx r15d, r11d, 25
	xor r14d, r15d
	add ebx, r14d
	add r10d, ebx
	rorx r14d, ebp, 2
	rorx r15d, ebp, 13
	xor r14d, r15d
	rorx r15d, ebp, 22
	xor r14d, r15d
	add ebx, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r13d, r14d
	xor r13d, r8d
	add ebx, r13d
	add eax, 338241895
	add eax, DWORD PTR [rcx+236]
	andn r15d, r10d, r12d
	add eax, r15d
	mov r13d, r10d
	and r13d, r11d
	add eax, r13d
	rorx r13d, r10d, 6
	rorx r15d, r10d, 11
	xor r13d, r15d
	rorx r15d, r10d, 25
	xor r13d, r15d
	add eax, r13d
	add r9d, eax
	rorx r13d, ebx, 2
	rorx r15d, ebx, 13
	xor r13d, r15d
	rorx r15d, ebx, 22
	xor r13d, r15d
	add eax, r13d
	mov r13d, ebx
	xor r13d, ebp
	and r14d, r13d
	xor r14d, ebp
	add eax, r14d
	vpalignr ymm4, ymm1, ymm0, 4
	vpalignr ymm7, ymm3, ymm2, 4
	vpsrld ymm6, ymm4, 7
	vpaddd ymm0, ymm0, ymm7
	vpsrld ymm7, ymm4, 3
	vpslld ymm5, ymm4, 14
	vpxor ymm4, ymm7, ymm6
	vpshufd ymm7, ymm3, 250
	vpsrld ymm6, ymm6, 11
	vpxor ymm4, ymm4, ymm5
	vpslld ymm5, ymm5, 11
	vpxor ymm4, ymm4, ymm6
	vpsrld ymm6, ymm7, 10
	vpxor ymm4, ymm4, ymm5
	vpsrlq ymm7, ymm7, 17
	vpaddd ymm0, ymm0, ymm4
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm8
	vpaddd ymm0, ymm0, ymm6
	vpshufd ymm7, ymm0, 80
	vpsrld ymm6, ymm7, 10
	vpsrlq ymm7, ymm7, 17
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm9
	vpaddd ymm0, ymm0, ymm6
	vmovdqu YMMWORD PTR [rcx+384], ymm0
	add r12d, 666307205
	add r12d, DWORD PTR [rcx+256]
	andn r15d, r9d, r11d
	add r12d, r15d
	mov r14d, r9d
	and r14d, r10d
	add r12d, r14d
	rorx r14d, r9d, 6
	rorx r15d, r9d, 11
	xor r14d, r15d
	rorx r15d, r9d, 25
	xor r14d, r15d
	add r12d, r14d
	add r8d, r12d
	rorx r14d, eax, 2
	rorx r15d, eax, 13
	xor r14d, r15d
	rorx r15d, eax, 22
	xor r14d, r15d
	add r12d, r14d
	mov r14d, eax
	xor r14d, ebx
	and r13d, r14d
	xor r13d, ebx
	add r12d, r13d
	add r11d, 773529912
	add r11d, DWORD PTR [rcx+260]
	andn r15d, r8d, r10d
	add r11d, r15d
	mov r13d, r8d
	and r13d, r9d
	add r11d, r13d
	rorx r13d, r8d, 6
	rorx r15d, r8d, 11
	xor r13d, r15d
	rorx r15d, r8d, 25
	xor r13d, r15d
	add r11d, r13d
	add ebp, r11d
	rorx r13d, r12d, 2
	rorx r15d, r12d, 13
	xor r13d, r15d
	rorx r15d, r12d, 22
	xor r13d, r15d
	add r11d, r13d
	mov r13d, r12d
	xor r13d, eax
	and r14d, r13d
	xor r14d, eax
	add r11d, r14d
	add r10d, 1294757372
	add r10d, DWORD PTR [rcx+264]
	andn r15d, ebp, r9d
	add r10d, r15d
	mov r14d, ebp
	and r14d, r8d
	add r10d, r14d
	rorx r14d, ebp, 6
	rorx r15d, ebp, 11
	xor r14d, r15d
	rorx r15d, ebp, 25
	xor r14d, r15d
	add r10d, r14d
	add ebx, r10d
	rorx r14d, r11d, 2
	rorx r15d, r11d, 13
	xor r14d, r15d
	rorx r15d, r11d, 22
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r11d
	xor r14d, r12d
	and r13d, r14d
	xor r13d, r12d
	add r10d, r13d
	add r9d, 1396182291
	add r9d, DWORD PTR [rcx+268]
	andn r15d, ebx, r8d
	add r9d, r15d
	mov r13d, ebx
	and r13d, ebp
	add r9d, r13d
	rorx r13d, ebx, 6
	rorx r15d, ebx, 11
	xor r13d, r15d
	rorx r15d, ebx, 25
	xor r13d, r15d
	add r9d, r13d
	add eax, r9d
	rorx r13d, r10d, 2
	rorx r15d, r10d, 13
	xor r13d, r15d
	rorx r15d, r10d, 22
	xor r13d, r15d
	add r9d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r14d, r13d
	xor r14d, r11d
	add r9d, r14d
	vpalignr ymm4, ymm2, ymm1, 4
	vpalignr ymm7, ymm0, ymm3, 4
	vpsrld ymm6, ymm4, 7
	vpaddd ymm1, ymm1, ymm7
	vpsrld ymm7, ymm4, 3
	vpslld ymm5, ymm4, 14
	vpxor ymm4, ymm7, ymm6
	vpshufd ymm7, ymm0, 250
	vpsrld ymm6, ymm6, 11
	vpxor ymm4, ymm4, ymm5
	vpslld ymm5, ymm5, 11
	vpxor ymm4, ymm4, ymm6
	vpsrld ymm6, ymm7, 10
	vpxor ymm4, ymm4, ymm5
	vpsrlq ymm7, ymm7, 17
	vpaddd ymm1, ymm1, ymm4
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm8
	vpaddd ymm1, ymm1, ymm6
	vpshufd ymm7, ymm1, 80
	vpsrld ymm6, ymm7, 10
	vpsrlq ymm7, ymm7, 17
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm9
	vpaddd ymm1, ymm1, ymm6
	vmovdqu YMMWORD PTR [rcx+416], ymm1
	add r8d, 1695183700
	add r8d, DWORD PTR [rcx+288]
	andn r15d, eax, ebp
	add r8d, r15d
	mov r14d, eax
	and r14d, ebx
	add r8d, r14d
	rorx r14d, eax, 6
	rorx r15d, eax, 11
	xor r14d, r15d
	rorx r15d, eax, 25
	xor r14d, r15d
	add r8d, r14d
	add r12d, r8d
	rorx r14d, r9d, 2
	rorx r15d, r9d, 13
	xor r14d, r15d
	rorx r15d, r9d, 22
	xor r14d, r15d
	add r8d, r14d
	mov r14d, r9d
	xor r14d, r10d
	and r13d, r14d
	xor r13d, r10d
	add r8d, r13d
	add ebp, 1986661051
	add ebp, DWORD PTR [rcx+292]
	andn r15d, r12d, ebx
	add ebp, r15d
	mov r13d, r12d
	and r13d, eax
	add ebp, r13d
	rorx r13d, r12d, 6
	rorx r15d, r12d, 11
	xor r13d, r15d
	rorx r15d, r12d, 25
	xor r13d, r15d
	add ebp, r13d
	add r11d, ebp
	rorx r13d, r8d, 2
	rorx r15d, r8d, 13
	xor r13d, r15d
	rorx r15d, r8d, 22
	xor r13d, r15d
	add ebp, r13d
	mov r13d, r8d
	xor r13d, r9d
	and r14d, r13d
	xor r14d, r9d
	add ebp, r14d
	add ebx, -2117940946
	add ebx, DWORD PTR [rcx+296]
	andn r15d, r11d, eax
	add ebx, r15d
	mov r14d, r11d
	and r14d, r12d
	add ebx, r14d
	rorx r14d, r11d, 6
	rorx r15d, r11d, 11
	xor r14d, r15d
	rorx r15d, r11d, 25
	xor r14d, r15d
	add ebx, r14d
	add r10d, ebx
	rorx r14d, ebp, 2
	rorx r15d, ebp, 13
	xor r14d, r15d
	rorx r15d, ebp, 22
	xor r14d, r15d
	add ebx, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r13d, r14d
	xor r13d, r8d
	add ebx, r13d
	add eax, -1838011259
	add eax, DWORD PTR [rcx+300]
	andn r15d, r10d, r12d
	add eax, r15d
	mov r13d, r10d
	and r13d, r11d
	add eax, r13d
	rorx r13d, r10d, 6
	rorx r15d, r10d, 11
	xor r13d, r15d
	rorx r15d, r10d, 25
	xor r13d, r15d
	add eax, r13d
	add r9d, eax
	rorx r13d, ebx, 2
	rorx r15d, ebx, 13
	xor r13d, r15d
	rorx r15d, ebx, 22
	xor r13d, r15d
	add eax, r13d
	mov r13d, ebx
	xor r13d, ebp
	and r14d, r13d
	xor r14d, ebp
	add eax, r14d
	vpalignr ymm4, ymm3, ymm2, 4
	vpalignr ymm7, ymm1, ymm0, 4
	vpsrld ymm6, ymm4, 7
	vpaddd ymm2, ymm2, ymm7
	vpsrld ymm7, ymm4, 3
	vpslld ymm5, ymm4, 14
	vpxor ymm4, ymm7, ymm6
	vpshufd ymm7, ymm1, 250
	vpsrld ymm6, ymm6, 11
	vpxor ymm4, ymm4, ymm5
	vpslld ymm5, ymm5, 11
	vpxor ymm4, ymm4, ymm6
	vpsrld ymm6, ymm7, 10
	vpxor ymm4, ymm4, ymm5
	vpsrlq ymm7, ymm7, 17
	vpaddd ymm2, ymm2, ymm4
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm8
	vpaddd ymm2, ymm2, ymm6
	vpshufd ymm7, ymm2, 80
	vpsrld ymm6, ymm7, 10
	vpsrlq ymm7, ymm7, 17
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm9
	vpaddd ymm2, ymm2, ymm6
	vmovdqu YMMWORD PTR [rcx+448], ymm2
	add r12d, -1564481375
	add r12d, DWORD PTR [rcx+320]
	andn r15d, r9d, r11d
	add r12d, r15d
	mov r14d, r9d
	and r14d, r10d
	add r12d, r14d
	rorx r14d, r9d, 6
	rorx r15d, r9d, 11
	xor r14d, r15d
	rorx r15d, r9d, 25
	xor r14d, r15d
	add r12d, r14d
	add r8d, r12d
	rorx r14d, eax, 2
	rorx r15d, eax, 13
	xor r14d, r15d
	rorx r15d, eax, 22
	xor r14d, r15d
	add r12d, r14d
	mov r14d, eax
	xor r14d, ebx
	and r13d, r14d
	xor r13d, ebx
	add r12d, r13d
	add r11d, -1474664885
	add r11d, DWORD PTR [rcx+324]
	andn r15d, r8d, r10d
	add r11d, r15d
	mov r13d, r8d
	and r13d, r9d
	add r11d, r13d
	rorx r13d, r8d, 6
	rorx r15d, r8d, 11
	xor r13d, r15d
	rorx r15d, r8d, 25
	xor r13d, r15d
	add r11d, r13d
	add ebp, r11d
	rorx r13d, r12d, 2
	rorx r15d, r12d, 13
	xor r13d, r15d
	rorx r15d, r12d, 22
	xor r13d, r15d
	add r11d, r13d
	mov r13d, r12d
	xor r13d, eax
	and r14d, r13d
	xor r14d, eax
	add r11d, r14d
	add r10d, -1035236496
	add r10d, DWORD PTR [rcx+328]
	andn r15d, ebp, r9d
	add r10d, r15d
	mov r14d, ebp
	and r14d, r8d
	add r10d, r14d
	rorx r14d, ebp, 6
	rorx r15d, ebp, 11
	xor r14d, r15d
	rorx r15d, ebp, 25
	xor r14d, r15d
	add r10d, r14d
	add ebx, r10d
	rorx r14d, r11d, 2
	rorx r15d, r11d, 13
	xor r14d, r15d
	rorx r15d, r11d, 22
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r11d
	xor r14d, r12d
	and r13d, r14d
	xor r13d, r12d
	add r10d, r13d
	add r9d, -949202525
	add r9d, DWORD PTR [rcx+332]
	andn r15d, ebx, r8d
	add r9d, r15d
	mov r13d, ebx
	and r13d, ebp
	add r9d, r13d
	rorx r13d, ebx, 6
	rorx r15d, ebx, 11
	xor r13d, r15d
	rorx r15d, ebx, 25
	xor r13d, r15d
	add r9d, r13d
	add eax, r9d
	rorx r13d, r10d, 2
	rorx r15d, r10d, 13
	xor r13d, r15d
	rorx r15d, r10d, 22
	xor r13d, r15d
	add r9d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r14d, r13d
	xor r14d, r11d
	add r9d, r14d
	vpalignr ymm4, ymm0, ymm3, 4
	vpalignr ymm7, ymm2, ymm1, 4
	vpsrld ymm6, ymm4, 7
	vpaddd ymm3, ymm3, ymm7
	vpsrld ymm7, ymm4, 3
	vpslld ymm5, ymm4, 14
	vpxor ymm4, ymm7, ymm6
	vpshufd ymm7, ymm2, 250
	vpsrld ymm6, ymm6, 11
	vpxor ymm4, ymm4, ymm5
	vpslld ymm5, ymm5, 11
	vpxor ymm4, ymm4, ymm6
	vpsrld ymm6, ymm7, 10
	vpxor ymm4, ymm4, ymm5
	vpsrlq ymm7, ymm7, 17
	vpaddd ymm3, ymm3, ymm4
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm8
	vpaddd ymm3, ymm3, ymm6
	vpshufd ymm7, ymm3, 80
	vpsrld ymm6, ymm7, 10
	vpsrlq ymm7, ymm7, 17
	vpxor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm7, 2
	vpxor ymm6, ymm6, ymm7
	vpshufb ymm6, ymm6, ymm9
	vpaddd ymm3, ymm3, ymm6
	vmovdqu YMMWORD PTR [rcx+480], ymm3
	add r8d, -778901479
	add r8d, DWORD PTR [rcx+352]
	andn r15d, eax, ebp
	add r8d, r15d
	mov r14d, eax
	and r14d, ebx
	add r8d, r14d
	rorx r14d, eax, 6
	rorx r15d, eax, 11
	xor r14d, r15d
	rorx r15d, eax, 25
	xor r14d, r15d
	add r8d, r14d
	add r12d, r8d
	rorx r14d, r9d, 2
	rorx r15d, r9d, 13
	xor r14d, r15d
	rorx r15d, r9d, 22
	xor r14d, r15d
	add r8d, r14d
	mov r14d, r9d
	xor r14d, r10d
	and r13d, r14d
	xor r13d, r10d
	add r8d, r13d
	add ebp, -694614492
	add ebp, DWORD PTR [rcx+356]
	andn r15d, r12d, ebx
	add ebp, r15d
	mov r13d, r12d
	and r13d, eax
	add ebp, r13d
	rorx r13d, r12d, 6
	rorx r15d, r12d, 11
	xor r13d, r15d
	rorx r15d, r12d, 25
	xor r13d, r15d
	add ebp, r13d
	add r11d, ebp
	rorx r13d, r8d, 2
	rorx r15d, r8d, 13
	xor r13d, r15d
	rorx r15d, r8d, 22
	xor r13d, r15d
	add ebp, r13d
	mov r13d, r8d
	xor r13d, r9d
	and r14d, r13d
	xor r14d, r9d
	add ebp, r14d
	add ebx, -200395387
	add ebx, DWORD PTR [rcx+360]
	andn r15d, r11d, eax
	add ebx, r15d
	mov r14d, r11d
	and r14d, r12d
	add ebx, r14d
	rorx r14d, r11d, 6
	rorx r15d, r11d, 11
	xor r14d, r15d
	rorx r15d, r11d, 25
	xor r14d, r15d
	add ebx, r14d
	add r10d, ebx
	rorx r14d, ebp, 2
	rorx r15d, ebp, 13
	xor r14d, r15d
	rorx r15d, ebp, 22
	xor r14d, r15d
	add ebx, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r13d, r14d
	xor r13d, r8d
	add ebx, r13d
	add eax, 275423344
	add eax, DWORD PTR [rcx+364]
	andn r15d, r10d, r12d
	add eax, r15d
	mov r13d, r10d
	and r13d, r11d
	add eax, r13d
	rorx r13d, r10d, 6
	rorx r15d, r10d, 11
	xor r13d, r15d
	rorx r15d, r10d, 25
	xor r13d, r15d
	add eax, r13d
	add r9d, eax
	rorx r13d, ebx, 2
	rorx r15d, ebx, 13
	xor r13d, r15d
	rorx r15d, ebx, 22
	xor r13d, r15d
	add eax, r13d
	mov r13d, ebx
	xor r13d, ebp
	and r14d, r13d
	xor r14d, ebp
	add eax, r14d
	add r12d, 430227734
	add r12d, DWORD PTR [rcx+384]
	andn r15d, r9d, r11d
	add r12d, r15d
	mov r14d, r9d
	and r14d, r10d
	add r12d, r14d
	rorx r14d, r9d, 6
	rorx r15d, r9d, 11
	xor r14d, r15d
	rorx r15d, r9d, 25
	xor r14d, r15d
	add r12d, r14d
	add r8d, r12d
	rorx r14d, eax, 2
	rorx r15d, eax, 13
	xor r14d, r15d
	rorx r15d, eax, 22
	xor r14d, r15d
	add r12d, r14d
	mov r14d, eax
	xor r14d, ebx
	and r13d, r14d
	xor r13d, ebx
	add r12d, r13d
	add r11d, 506948616
	add r11d, DWORD PTR [rcx+388]
	andn r15d, r8d, r10d
	add r11d, r15d
	mov r13d, r8d
	and r13d, r9d
	add r11d, r13d
	rorx r13d, r8d, 6
	rorx r15d, r8d, 11
	xor r13d, r15d
	rorx r15d, r8d, 25
	xor r13d, r15d
	add r11d, r13d
	add ebp, r11d
	rorx r13d, r12d, 2
	rorx r15d, r12d, 13
	xor r13d, r15d
	rorx r15d, r12d, 22
	xor r13d, r15d
	add r11d, r13d
	mov r13d, r12d
	xor r13d, eax
	and r14d, r13d
	xor r14d, eax
	add r11d, r14d
	add r10d, 659060556
	add r10d, DWORD PTR [rcx+392]
	andn r15d, ebp, r9d
	add r10d, r15d
	mov r14d, ebp
	and r14d, r8d
	add r10d, r14d
	rorx r14d, ebp, 6
	rorx r15d, ebp, 11
	xor r14d, r15d
	rorx r15d, ebp, 25
	xor r14d, r15d
	add r10d, r14d
	add ebx, r10d
	rorx r14d, r11d, 2
	rorx r15d, r11d, 13
	xor r14d, r15d
	rorx r15d, r11d, 22
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r11d
	xor r14d, r12d
	and r13d, r14d
	xor r13d, r12d
	add r10d, r13d
	add r9d, 883997877
	add r9d, DWORD PTR [rcx+396]
	andn r15d, ebx, r8d
	add r9d, r15d
	mov r13d, ebx
	and r13d, ebp
	add r9d, r13d
	rorx r13d, ebx, 6
	rorx r15d, ebx, 11
	xor r13d, r15d
	rorx r15d, ebx, 25
	xor r13d, r15d
	add r9d, r13d
	add eax, r9d
	rorx r13d, r10d, 2
	rorx r15d, r10d, 13
	xor r13d, r15d
	rorx r15d, r10d, 22
	xor r13d, r15d
	add r9d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r14d, r13d
	xor r14d, r11d
	add r9d, r14d
	add r8d, 958139571
	add r8d, DWORD PTR [rcx+416]
	andn r15d, eax, ebp
	add r8d, r15d
	mov r14d, eax
	and r14d, ebx
	add r8d, r14d
	rorx r14d, eax, 6
	rorx r15d, eax, 11
	xor r14d, r15d
	rorx r15d, eax, 25
	xor r14d, r15d
	add r8d, r14d
	add r12d, r8d
	rorx r14d, r9d, 2
	rorx r15d, r9d, 13
	xor r14d, r15d
	rorx r15d, r9d, 22
	xor r14d, r15d
	add r8d, r14d
	mov r14d, r9d
	xor r14d, r10d
	and r13d, r14d
	xor r13d, r10d
	add r8d, r13d
	add ebp, 1322822218
	add ebp, DWORD PTR [rcx+420]
	andn r15d, r12d, ebx
	add ebp, r15d
	mov r13d, r12d
	and r13d, eax
	add ebp, r13d
	rorx r13d, r12d, 6
	rorx r15d, r12d, 11
	xor r13d, r15d
	rorx r15d, r12d, 25
	xor r13d, r15d
	add ebp, r13d
	add r11d, ebp
	rorx r13d, r8d, 2
	rorx r15d, r8d, 13
	xor r13d, r15d
	rorx r15d, r8d, 22
	xor r13d, r15d
	add ebp, r13d
	mov r13d, r8d
	xor r13d, r9d
	and r14d, r13d
	xor r14d, r9d
	add ebp, r14d
	add ebx, 1537002063
	add ebx, DWORD PTR [rcx+424]
	andn r15d, r11d, eax
	add ebx, r15d
	mov r14d, r11d
	and r14d, r12d
	add ebx, r14d
	rorx r14d, r11d, 6
	rorx r15d, r11d, 11
	xor r14d, r15d
	rorx r15d, r11d, 25
	xor r14d, r15d
	add ebx, r14d
	add r10d, ebx
	rorx r14d, ebp, 2
	rorx r15d, ebp, 13
	xor r14d, r15d
	rorx r15d, ebp, 22
	xor r14d, r15d
	add ebx, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r13d, r14d
	xor r13d, r8d
	add ebx, r13d
	add eax, 1747873779
	add eax, DWORD PTR [rcx+428]
	andn r15d, r10d, r12d
	add eax, r15d
	mov r13d, r10d
	and r13d, r11d
	add eax, r13d
	rorx r13d, r10d, 6
	rorx r15d, r10d, 11
	xor r13d, r15d
	rorx r15d, r10d, 25
	xor r13d, r15d
	add eax, r13d
	add r9d, eax
	rorx r13d, ebx, 2
	rorx r15d, ebx, 13
	xor r13d, r15d
	rorx r15d, ebx, 22
	xor r13d, r15d
	add eax, r13d
	mov r13d, ebx
	xor r13d, ebp
	and r14d, r13d
	xor r14d, ebp
	add eax, r14d
	add r12d, 1955562222
	add r12d, DWORD PTR [rcx+448]
	andn r15d, r9d, r11d
	add r12d, r15d
	mov r14d, r9d
	and r14d, r10d
	add r12d, r14d
	rorx r14d, r9d, 6
	rorx r15d, r9d, 11
	xor r14d, r15d
	rorx r15d, r9d, 25
	xor r14d, r15d
	add r12d, r14d
	add r8d, r12d
	rorx r14d, eax, 2
	rorx r15d, eax, 13
	xor r14d, r15d
	rorx r15d, eax, 22
	xor r14d, r15d
	add r12d, r14d
	mov r14d, eax
	xor r14d, ebx
	and r13d, r14d
	xor r13d, ebx
	add r12d, r13d
	add r11d, 2024104815
	add r11d, DWORD PTR [rcx+452]
	andn r15d, r8d, r10d
	add r11d, r15d
	mov r13d, r8d
	and r13d, r9d
	add r11d, r13d
	rorx r13d, r8d, 6
	rorx r15d, r8d, 11
	xor r13d, r15d
	rorx r15d, r8d, 25
	xor r13d, r15d
	add r11d, r13d
	add ebp, r11d
	rorx r13d, r12d, 2
	rorx r15d, r12d, 13
	xor r13d, r15d
	rorx r15d, r12d, 22
	xor r13d, r15d
	add r11d, r13d
	mov r13d, r12d
	xor r13d, eax
	and r14d, r13d
	xor r14d, eax
	add r11d, r14d
	add r10d, -2067236844
	add r10d, DWORD PTR [rcx+456]
	andn r15d, ebp, r9d
	add r10d, r15d
	mov r14d, ebp
	and r14d, r8d
	add r10d, r14d
	rorx r14d, ebp, 6
	rorx r15d, ebp, 11
	xor r14d, r15d
	rorx r15d, ebp, 25
	xor r14d, r15d
	add r10d, r14d
	add ebx, r10d
	rorx r14d, r11d, 2
	rorx r15d, r11d, 13
	xor r14d, r15d
	rorx r15d, r11d, 22
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r11d
	xor r14d, r12d
	and r13d, r14d
	xor r13d, r12d
	add r10d, r13d
	add r9d, -1933114872
	add r9d, DWORD PTR [rcx+460]
	andn r15d, ebx, r8d
	add r9d, r15d
	mov r13d, ebx
	and r13d, ebp
	add r9d, r13d
	rorx r13d, ebx, 6
	rorx r15d, ebx, 11
	xor r13d, r15d
	rorx r15d, ebx, 25
	xor r13d, r15d
	add r9d, r13d
	add eax, r9d
	rorx r13d, r10d, 2
	rorx r15d, r10d, 13
	xor r13d, r15d
	rorx r15d, r10d, 22
	xor r13d, r15d
	add r9d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r14d, r13d
	xor r14d, r11d
	add r9d, r14d
	add r8d, -1866530822
	add r8d, DWORD PTR [rcx+480]
	andn r15d, eax, ebp
	add r8d, r15d
	mov r14d, eax
	and r14d, ebx
	add r8d, r14d
	rorx r14d, eax, 6
	rorx r15d, eax, 11
	xor r14d, r15d
	rorx r15d, eax, 25
	xor r14d, r15d
	add r8d, r14d
	add r12d, r8d
	rorx r14d, r9d, 2
	rorx r15d, r9d, 13
	xor r14d, r15d
	rorx r15d, r9d, 22
	xor r14d, r15d
	add r8d, r14d
	mov r14d, r9d
	xor r14d, r10d
	and r13d, r14d
	xor r13d, r10d
	add r8d, r13d
	add ebp, -1538233109
	add ebp, DWORD PTR [rcx+484]
	andn r15d, r12d, ebx
	add ebp, r15d
	mov r13d, r12d
	and r13d, eax
	add ebp, r13d
	rorx r13d, r12d, 6
	rorx r15d, r12d, 11
	xor r13d, r15d
	rorx r15d, r12d, 25
	xor r13d, r15d
	add ebp, r13d
	add r11d, ebp
	rorx r13d, r8d, 2
	rorx r15d, r8d, 13
	xor r13d, r15d
	rorx r15d, r8d, 22
	xor r13d, r15d
	add ebp, r13d
	mov r13d, r8d
	xor r13d, r9d
	and r14d, r13d
	xor r14d, r9d
	add ebp, r14d
	add ebx, -1090935817
	add ebx, DWORD PTR [rcx+488]
	andn r15d, r11d, eax
	add ebx, r15d
	mov r14d, r11d
	and r14d, r12d
	add ebx, r14d
	rorx r14d, r11d, 6
	rorx r15d, r11d, 11
	xor r14d, r15d
	rorx r15d, r11d, 25
	xor r14d, r15d
	add ebx, r14d
	add r10d, ebx
	rorx r14d, ebp, 2
	rorx r15d, ebp, 13
	xor r14d, r15d
	rorx r15d, ebp, 22
	xor r14d, r15d
	add ebx, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r13d, r14d
	xor r13d, r8d
	add ebx, r13d
	add eax, -965641998
	add eax, DWORD PTR [rcx+492]
	andn r15d, r10d, r12d
	add eax, r15d
	mov r13d, r10d
	and r13d, r11d
	add eax, r13d
	rorx r13d, r10d, 6
	rorx r15d, r10d, 11
	xor r13d, r15d
	rorx r15d, r10d, 25
	xor r13d, r15d
	add eax, r13d
	add r9d, eax
	rorx r13d, ebx, 2
	rorx r15d, ebx, 13
	xor r13d, r15d
	rorx r15d, ebx, 22
	xor r13d, r15d
	add eax, r13d
	mov r13d, ebx
	xor r13d, ebp
	and r14d, r13d
	xor r14d, ebp
	add eax, r14d
	add eax, DWORD PTR [rdi]
	add ebx, DWORD PTR [rdi+4]
	add ebp, DWORD PTR [rdi+8]
	add r8d, DWORD PTR [rdi+12]
	add r9d, DWORD PTR [rdi+16]
	add r10d, DWORD PTR [rdi+20]
	add r11d, DWORD PTR [rdi+24]
	add r12d, DWORD PTR [rdi+28]
	mov DWORD PTR [rdi], eax
	mov DWORD PTR [rdi+4], ebx
	mov DWORD PTR [rdi+8], ebp
	mov DWORD PTR [rdi+12], r8d
	mov DWORD PTR [rdi+16], r9d
	mov DWORD PTR [rdi+20], r10d
	mov DWORD PTR [rdi+24], r11d
	mov DWORD PTR [rdi+28], r12d
	cmp rdx, 1
	je 25f
	mov r13d, ebx
	xor r13d, ebp
	add r12d, 1116352408
	add r12d, DWORD PTR [rcx+16]
	andn r15d, r9d, r11d
	add r12d, r15d
	mov r14d, r9d
	and r14d, r10d
	add r12d, r14d
	rorx r14d, r9d, 6
	rorx r15d, r9d, 11
	xor r14d, r15d
	rorx r15d, r9d, 25
	xor r14d, r15d
	add r12d, r14d
	add r8d, r12d
	rorx r14d, eax, 2
	rorx r15d, eax, 13
	xor r14d, r15d
	rorx r15d, eax, 22
	xor r14d, r15d
	add r12d, r14d
	mov r14d, eax
	xor r14d, ebx
	and r13d, r14d
	xor r13d, ebx
	add r12d, r13d
	add r11d, 1899447441
	add r11d, DWORD PTR [rcx+20]
	andn r15d, r8d, r10d
	add r11d, r15d
	mov r13d, r8d
	and r13d, r9d
	add r11d, r13d
	rorx r13d, r8d, 6
	rorx r15d, r8d, 11
	xor r13d, r15d
	rorx r15d, r8d, 25
	xor r13d, r15d
	add r11d, r13d
	add ebp, r11d
	rorx r13d, r12d, 2
	rorx r15d, r12d, 13
	xor r13d, r15d
	rorx r15d, r12d, 22
	xor r13d, r15d
	add r11d, r13d
	mov r13d, r12d
	xor r13d, eax
	and r14d, r13d
	xor r14d, eax
	add r11d, r14d
	add r10d, -1245643825
	add r10d, DWORD PTR [rcx+24]
	andn r15d, ebp, r9d
	add r10d, r15d
	mov r14d, ebp
	and r14d, r8d
	add r10d, r14d
	rorx r14d, ebp, 6
	rorx r15d, ebp, 11
	xor r14d, r15d
	rorx r15d, ebp, 25
	xor r14d, r15d
	add r10d, r14d
	add ebx, r10d
	rorx r14d, r11d, 2
	rorx r15d, r11d, 13
	xor r14d, r15d
	rorx r15d, r11d, 22
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r11d
	xor r14d, r12d
	and r13d, r14d
	xor r13d, r12d
	add r10d, r13d
	add r9d, -373957723
	add r9d, DWORD PTR [rcx+28]
	andn r15d, ebx, r8d
	add r9d, r15d
	mov r13d, ebx
	and r13d, ebp
	add r9d, r13d
	rorx r13d, ebx, 6
	rorx r15d, ebx, 11
	xor r13d, r15d
	rorx r15d, ebx, 25
	xor r13d, r15d
	add r9d, r13d
	add eax, r9d
	rorx r13d, r10d, 2
	rorx r15d, r10d, 13
	xor r13d, r15d
	rorx r15d, r10d, 22
	xor r13d, r15d
	add r9d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r14d, r13d
	xor r14d, r11d
	add r9d, r14d
	add r8d, 961987163
	add r8d, DWORD PTR [rcx+48]
	andn r15d, eax, ebp
	add r8d, r15d
	mov r14d, eax
	and r14d, ebx
	add r8d, r14d
	rorx r14d, eax, 6
	rorx r15d, eax, 11
	xor r14d, r15d
	rorx r15d, eax, 25
	xor r14d, r15d
	add r8d, r14d
	add r12d, r8d
	rorx r14d, r9d, 2
	rorx r15d, r9d, 13
	xor r14d, r15d
	rorx r15d, r9d, 22
	xor r14d, r15d
	add r8d, r14d
	mov r14d, r9d
	xor r14d, r10d
	and r13d, r14d
	xor r13d, r10d
	add r8d, r13d
	add ebp, 1508970993
	add ebp, DWORD PTR [rcx+52]
	andn r15d, r12d, ebx
	add ebp, r15d
	mov r13d, r12d
	and r13d, eax
	add ebp, r13d
	rorx r13d, r12d, 6
	rorx r15d, r12d, 11
	xor r13d, r15d
	rorx r15d, r12d, 25
	xor r13d, r15d
	add ebp, r13d
	add r11d, ebp
	rorx r13d, r8d, 2
	rorx r15d, r8d, 13
	xor r13d, r15d
	rorx r15d, r8d, 22
	xor r13d, r15d
	add ebp, r13d
	mov r13d, r8d
	xor r13d, r9d
	and r14d, r13d
	xor r14d, r9d
	add ebp, r14d
	add ebx, -1841331548
	add ebx, DWORD PTR [rcx+56]
	andn r15d, r11d, eax
	add ebx, r15d
	mov r14d, r11d
	and r14d, r12d
	add ebx, r14d
	rorx r14d, r11d, 6
	rorx r15d, r11d, 11
	xor r14d, r15d
	rorx r15d, r11d, 25
	xor r14d, r15d
	add ebx, r14d
	add r10d, ebx
	rorx r14d, ebp, 2
	rorx r15d, ebp, 13
	xor r14d, r15d
	rorx r15d, ebp, 22
	xor r14d, r15d
	add ebx, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r13d, r14d
	xor r13d, r8d
	add ebx, r13d
	add eax, -1424204075
	add eax, DWORD PTR [rcx+60]
	andn r15d, r10d, r12d
	add eax, r15d
	mov r13d, r10d
	and r13d, r11d
	add eax, r13d
	rorx r13d, r10d, 6
	rorx r15d, r10d, 11
	xor r13d, r15d
	rorx r15d, r10d, 25
	xor r13d, r15d
	add eax, r13d
	add r9d, eax
	rorx r13d, ebx, 2
	rorx r15d, ebx, 13
	xor r13d, r15d
	rorx r15d, ebx, 22
	xor r13d, r15d
	add eax, r13d
	mov r13d, ebx
	xor r13d, ebp
	and r14d, r13d
	xor r14d, ebp
	add eax, r14d
	add r12d, -670586216
	add r12d, DWORD PTR [rcx+80]
	andn r15d, r9d, r11d
	add r12d, r15d
	mov r14d, r9d
	and r14d, r10d
	add r12d, r14d
	rorx r14d, r9d, 6
	rorx r15d, r9d, 11
	xor r14d, r15d
	rorx r15d, r9d, 25
	xor r14d, r15d
	add r12d, r14d
	add r8d, r12d
	rorx r14d, eax, 2
	rorx r15d, eax, 13
	xor r14d, r15d
	rorx r15d, eax, 22
	xor r14d, r15d
	add r12d, r14d
	mov r14d, eax
	xor r14d, ebx
	and r13d, r14d
	xor r13d, ebx
	add r12d, r13d
	add r11d, 310598401
	add r11d, DWORD PTR [rcx+84]
	andn r15d, r8d, r10d
	add r11d, r15d
	mov r13d, r8d
	and r13d, r9d
	add r11d, r13d
	rorx r13d, r8d, 6
	rorx r15d, r8d, 11
	xor r13d, r15d
	rorx r15d, r8d, 25
	xor r13d, r15d
	add r11d, r13d
	add ebp, r11d
	rorx r13d, r12d, 2
	rorx r15d, r12d, 13
	xor r13d, r15d
	rorx r15d, r12d, 22
	xor r13d, r15d
	add r11d, r13d
	mov r13d, r12d
	xor r13d, eax
	and r14d, r13d
	xor r14d, eax
	add r11d, r14d
	add r10d, 607225278
	add r10d, DWORD PTR [rcx+88]
	andn r15d, ebp, r9d
	add r10d, r15d
	mov r14d, ebp
	and r14d, r8d
	add r10d, r14d
	rorx r14d, ebp, 6
	rorx r15d, ebp, 11
	xor r14d, r15d
	rorx r15d, ebp, 25
	xor r14d, r15d
	add r10d, r14d
	add ebx, r10d
	rorx r14d, r11d, 2
	rorx r15d, r11d, 13
	xor r14d, r15d
	rorx r15d, r11d, 22
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r11d
	xor r14d, r12d
	and r13d, r14d
	xor r13d, r12d
	add r10d, r13d
	add r9d, 1426881987
	add r9d, DWORD PTR [rcx+92]
	andn r15d, ebx, r8d
	add r9d, r15d
	mov r13d, ebx
	and r13d, ebp
	add r9d, r13d
	rorx r13d, ebx, 6
	rorx r15d, ebx, 11
	xor r13d, r15d
	rorx r15d, ebx, 25
	xor r13d, r15d
	add r9d, r13d
	add eax, r9d
	rorx r13d, r10d, 2
	rorx r15d, r10d, 13
	xor r13d, r15d
	rorx r15d, r10d, 22
	xor r13d, r15d
	add r9d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r14d, r13d
	xor r14d, r11d
	add r9d, r14d
	add r8d, 1925078388
	add r8d, DWORD PTR [rcx+112]
	andn r15d, eax, ebp
	add r8d, r15d
	mov r14d, eax
	and r14d, ebx
	add r8d, r14d
	rorx r14d, eax, 6
	rorx r15d, eax, 11
	xor r14d, r15d
	rorx r15d, eax, 25
	xor r14d, r15d
	add r8d, r14d
	add r12d, r8d
	rorx r14d, r9d, 2
	rorx r15d, r9d, 13
	xor r14d, r15d
	rorx r15d, r9d, 22
	xor r14d, r15d
	add r8d, r14d
	mov r14d, r9d
	xor r14d, r10d
	and r13d, r14d
	xor r13d, r10d
	add r8d, r13d
	add ebp, -2132889090
	add ebp, DWORD PTR [rcx+116]
	andn r15d, r12d, ebx
	add ebp, r15d
	mov r13d, r12d
	and r13d, eax
	add ebp, r13d
	rorx r13d, r12d, 6
	rorx r15d, r12d, 11
	xor r13d, r15d
	rorx r15d, r12d, 25
	xor r13d, r15d
	add ebp, r13d
	add r11d, ebp
	rorx r13d, r8d, 2
	rorx r15d, r8d, 13
	xor r13d, r15d
	rorx r15d, r8d, 22
	xor r13d, r15d
	add ebp, r13d
	mov r13d, r8d
	xor r13d, r9d
	and r14d, r13d
	xor r14d, r9d
	add ebp, r14d
	add ebx, -1680079193
	add ebx, DWORD PTR [rcx+120]
	andn r15d, r11d, eax
	add ebx, r15d
	mov r14d, r11d
	and r14d, r12d
	add ebx, r14d
	rorx r14d, r11d, 6
	rorx r15d, r11d, 11
	xor r14d, r15d
	rorx r15d, r11d, 25
	xor r14d, r15d
	add ebx, r14d
	add r10d, ebx
	rorx r14d, ebp, 2
	rorx r15d, ebp, 13
	xor r14d, r15d
	rorx r15d, ebp, 22
	xor r14d, r15d
	add ebx, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r13d, r14d
	xor r13d, r8d
	add ebx, r13d
	add eax, -1046744716
	add eax, DWORD PTR [rcx+124]
	andn r15d, r10d, r12d
	add eax, r15d
	mov r13d, r10d
	and r13d, r11d
	add eax, r13d
	rorx r13d, r10d, 6
	rorx r15d, r10d, 11
	xor r13d, r15d
	rorx r15d, r10d, 25
	xor r13d, r15d
	add eax, r13d
	add r9d, eax
	rorx r13d, ebx, 2
	rorx r15d, ebx, 13
	xor r13d, r15d
	rorx r15d, ebx, 22
	xor r13d, r15d
	add eax, r13d
	mov r13d, ebx
	xor r13d, ebp
	and r14d, r13d
	xor r14d, ebp
	add eax, r14d
	add r12d, -459576895
	add r12d, DWORD PTR [rcx+144]
	andn r15d, r9d, r11d
	add r12d, r15d
	mov r14d, r9d
	and r14d, r10d
	add r12d, r14d
	rorx r14d, r9d, 6
	rorx r15d, r9d, 11
	xor r14d, r15d
	rorx r15d, r9d, 25
	xor r14d, r15d
	add r12d, r14d
	add r8d, r12d
	rorx r14d, eax, 2
	rorx r15d, eax, 13
	xor r14d, r15d
	rorx r15d, eax, 22
	xor r14d, r15d
	add r12d, r14d
	mov r14d, eax
	xor r14d, ebx
	and r13d, r14d
	xor r13d, ebx
	add r12d, r13d
	add r11d, -272742522
	add r11d, DWORD PTR [rcx+148]
	andn r15d, r8d, r10d
	add r11d, r15d
	mov r13d, r8d
	and r13d, r9d
	add r11d, r13d
	rorx r13d, r8d, 6
	rorx r15d, r8d, 11
	xor r13d, r15d
	rorx r15d, r8d, 25
	xor r13d, r15d
	add r11d, r13d
	add ebp, r11d
	rorx r13d, r12d, 2
	rorx r15d, r12d, 13
	xor r13d, r15d
	rorx r15d, r12d, 22
	xor r13d, r15d
	add r11d, r13d
	mov r13d, r12d
	xor r13d, eax
	and r14d, r13d
	xor r14d, eax
	add r11d, r14d
	add r10d, 264347078
	add r10d, DWORD PTR [rcx+152]
	andn r15d, ebp, r9d
	add r10d, r15d
	mov r14d, ebp
	and r14d, r8d
	add r10d, r14d
	rorx r14d, ebp, 6
	rorx r15d, ebp, 11
	xor r14d, r15d
	rorx r15d, ebp, 25
	xor r14d, r15d
	add r10d, r14d
	add ebx, r10d
	rorx r14d, r11d, 2
	rorx r15d, r11d, 13
	xor r14d, r15d
	rorx r15d, r11d, 22
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r11d
	xor r14d, r12d
	and r13d, r14d
	xor r13d, r12d
	add r10d, r13d
	add r9d, 604807628
	add r9d, DWORD PTR [rcx+156]
	andn r15d, ebx, r8d
	add r9d, r15d
	mov r13d, ebx
	and r13d, ebp
	add r9d, r13d
	rorx r13d, ebx, 6
	rorx r15d, ebx, 11
	xor r13d, r15d
	rorx r15d, ebx, 25
	xor r13d, r15d
	add r9d, r13d
	add eax, r9d
	rorx r13d, r10d, 2
	rorx r15d, r10d, 13
	xor r13d, r15d
	rorx r15d, r10d, 22
	xor r13d, r15d
	add r9d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r14d, r13d
	xor r14d, r11d
	add r9d, r14d
	add r8d, 770255983
	add r8d, DWORD PTR [rcx+176]
	andn r15d, eax, ebp
	add r8d, r15d
	mov r14d, eax
	and r14d, ebx
	add r8d, r14d
	rorx r14d, eax, 6
	rorx r15d, eax, 11
	xor r14d, r15d
	rorx r15d, eax, 25
	xor r14d, r15d
	add r8d, r14d
	add r12d, r8d
	rorx r14d, r9d, 2
	rorx r15d, r9d, 13
	xor r14d, r15d
	rorx r15d, r9d, 22
	xor r14d, r15d
	add r8d, r14d
	mov r14d, r9d
	xor r14d, r10d
	and r13d, r14d
	xor r13d, r10d
	add r8d, r13d
	add ebp, 1249150122
	add ebp, DWORD PTR [rcx+180]
	andn r15d, r12d, ebx
	add ebp, r15d
	mov r13d, r12d
	and r13d, eax
	add ebp, r13d
	rorx r13d, r12d, 6
	rorx r15d, r12d, 11
	xor r13d, r15d
	rorx r15d, r12d, 25
	xor r13d, r15d
	add ebp, r13d
	add r11d, ebp
	rorx r13d, r8d, 2
	rorx r15d, r8d, 13
	xor r13d, r15d
	rorx r15d, r8d, 22
	xor r13d, r15d
	add ebp, r13d
	mov r13d, r8d
	xor r13d, r9d
	and r14d, r13d
	xor r14d, r9d
	add ebp, r14d
	add ebx, 1555081692
	add ebx, DWORD PTR [rcx+184]
	andn r15d, r11d, eax
	add ebx, r15d
	mov r14d, r11d
	and r14d, r12d
	add ebx, r14d
	rorx r14d, r11d, 6
	rorx r15d, r11d, 11
	xor r14d, r15d
	rorx r15d, r11d, 25
	xor r14d, r15d
	add ebx, r14d
	add r10d, ebx
	rorx r14d, ebp, 2
	rorx r15d, ebp, 13
	xor r14d, r15d
	rorx r15d, ebp, 22
	xor r14d, r15d
	add ebx, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r13d, r14d
	xor r13d, r8d
	add ebx, r13d
	add eax, 1996064986
	add eax, DWORD PTR [rcx+188]
	andn r15d, r10d, r12d
	add eax, r15d
	mov r13d, r10d
	and r13d, r11d
	add eax, r13d
	rorx r13d, r10d, 6
	rorx r15d, r10d, 11
	xor r13d, r15d
	rorx r15d, r10d, 25
	xor r13d, r15d
	add eax, r13d
	add r9d, eax
	rorx r13d, ebx, 2
	rorx r15d, ebx, 13
	xor r13d, r15d
	rorx r15d, ebx, 22
	xor r13d, r15d
	add eax, r13d
	mov r13d, ebx
	xor r13d, ebp
	and r14d, r13d
	xor r14d, ebp
	add eax, r14d
	add r12d, -1740746414
	add r12d, DWORD PTR [rcx+208]
	andn r15d, r9d, r11d
	add r12d, r15d
	mov r14d, r9d
	and r14d, r10d
	add r12d, r14d
	rorx r14d, r9d, 6
	rorx r15d, r9d, 11
	xor r14d, r15d
	rorx r15d, r9d, 25
	xor r14d, r15d
	add r12d, r14d
	add r8d, r12d
	rorx r14d, eax, 2
	rorx r15d, eax, 13
	xor r14d, r15d
	rorx r15d, eax, 22
	xor r14d, r15d
	add r12d, r14d
	mov r14d, eax
	xor r14d, ebx
	and r13d, r14d
	xor r13d, ebx
	add r12d, r13d
	add r11d, -1473132947
	add r11d, DWORD PTR [rcx+212]
	andn r15d, r8d, r10d
	add r11d, r15d
	mov r13d, r8d
	and r13d, r9d
	add r11d, r13d
	rorx r13d, r8d, 6
	rorx r15d, r8d, 11
	xor r13d, r15d
	rorx r15d, r8d, 25
	xor r13d, r15d
	add r11d, r13d
	add ebp, r11d
	rorx r13d, r12d, 2
	rorx r15d, r12d, 13
	xor r13d, r15d
	rorx r15d, r12d, 22
	xor r13d, r15d
	add r11d, r13d
	mov r13d, r12d
	xor r13d, eax
	and r14d, r13d
	xor r14d, eax
	add r11d, r14d
	add r10d, -1341970488
	add r10d, DWORD PTR [rcx+216]
	andn r15d, ebp, r9d
	add r10d, r15d
	mov r14d, ebp
	and r14d, r8d
	add r10d, r14d
	rorx r14d, ebp, 6
	rorx r15d, ebp, 11
	xor r14d, r15d
	rorx r15d, ebp, 25
	xor r14d, r15d
	add r10d, r14d
	add ebx, r10d
	rorx r14d, r11d, 2
	rorx r15d, r11d, 13
	xor r14d, r15d
	rorx r15d, r11d, 22
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r11d
	xor r14d, r12d
	and r13d, r14d
	xor r13d, r12d
	add r10d, r13d
	add r9d, -1084653625
	add r9d, DWORD PTR [rcx+220]
	andn r15d, ebx, r8d
	add r9d, r15d
	mov r13d, ebx
	and r13d, ebp
	add r9d, r13d
	rorx r13d, ebx, 6
	rorx r15d, ebx, 11
	xor r13d, r15d
	rorx r15d, ebx, 25
	xor r13d, r15d
	add r9d, r13d
	add eax, r9d
	rorx r13d, r10d, 2
	rorx r15d, r10d, 13
	xor r13d, r15d
	rorx r15d, r10d, 22
	xor r13d, r15d
	add r9d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r14d, r13d
	xor r14d, r11d
	add r9d, r14d
	add r8d, -958395405
	add r8d, DWORD PTR [rcx+240]
	andn r15d, eax, ebp
	add r8d, r15d
	mov r14d, eax
	and r14d, ebx
	add r8d, r14d
	rorx r14d, eax, 6
	rorx r15d, eax, 11
	xor r14d, r15d
	rorx r15d, eax, 25
	xor r14d, r15d
	add r8d, r14d
	add r12d, r8d
	rorx r14d, r9d, 2
	rorx r15d, r9d, 13
	xor r14d, r15d
	rorx r15d, r9d, 22
	xor r14d, r15d
	add r8d, r14d
	mov r14d, r9d
	xor r14d, r10d
	and r13d, r14d
	xor r13d, r10d
	add r8d, r13d
	add ebp, -710438585
	add ebp, DWORD PTR [rcx+244]
	andn r15d, r12d, ebx
	add ebp, r15d
	mov r13d, r12d
	and r13d, eax
	add ebp, r13d
	rorx r13d, r12d, 6
	rorx r15d, r12d, 11
	xor r13d, r15d
	rorx r15d, r12d, 25
	xor r13d, r15d
	add ebp, r13d
	add r11d, ebp
	rorx r13d, r8d, 2
	rorx r15d, r8d, 13
	xor r13d, r15d
	rorx r15d, r8d, 22
	xor r13d, r15d
	add ebp, r13d
	mov r13d, r8d
	xor r13d, r9d
	and r14d, r13d
	xor r14d, r9d
	add ebp, r14d
	add ebx, 113926993
	add ebx, DWORD PTR [rcx+248]
	andn r15d, r11d, eax
	add ebx, r15d
	mov r14d, r11d
	and r14d, r12d
	add ebx, r14d
	rorx r14d, r11d, 6
	rorx r15d, r11d, 11
	xor r14d, r15d
	rorx r15d, r11d, 25
	xor r14d, r15d
	add ebx, r14d
	add r10d, ebx
	rorx r14d, ebp, 2
	rorx r15d, ebp, 13
	xor r14d, r15d
	rorx r15d, ebp, 22
	xor r14d, r15d
	add ebx, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r13d, r14d
	xor r13d, r8d
	add ebx, r13d
	add eax, 338241895
	add eax, DWORD PTR [rcx+252]
	andn r15d, r10d, r12d
	add eax, r15d
	mov r13d, r10d
	and r13d, r11d
	add eax, r13d
	rorx r13d, r10d, 6
	rorx r15d, r10d, 11
	xor r13d, r15d
	rorx r15d, r10d, 25
	xor r13d, r15d
	add eax, r13d
	add r9d, eax
	rorx r13d, ebx, 2
	rorx r15d, ebx, 13
	xor r13d, r15d
	rorx r15d, ebx, 22
	xor r13d, r15d
	add eax, r13d
	mov r13d, ebx
	xor r13d, ebp
	and r14d, r13d
	xor r14d, ebp
	add eax, r14d
	add r12d, 666307205
	add r12d, DWORD PTR [rcx+272]
	andn r15d, r9d, r11d
	add r12d, r15d
	mov r14d, r9d
	and r14d, r10d
	add r12d, r14d
	rorx r14d, r9d, 6
	rorx r15d, r9d, 11
	xor r14d, r15d
	rorx r15d, r9d, 25
	xor r14d, r15d
	add r12d, r14d
	add r8d, r12d
	rorx r14d, eax, 2
	rorx r15d, eax, 13
	xor r14d, r15d
	rorx r15d, eax, 22
	xor r14d, r15d
	add r12d, r14d
	mov r14d, eax
	xor r14d, ebx
	and r13d, r14d
	xor r13d, ebx
	add r12d, r13d
	add r11d, 773529912
	add r11d, DWORD PTR [rcx+276]
	andn r15d, r8d, r10d
	add r11d, r15d
	mov r13d, r8d
	and r13d, r9d
	add r11d, r13d
	rorx r13d, r8d, 6
	rorx r15d, r8d, 11
	xor r13d, r15d
	rorx r15d, r8d, 25
	xor r13d, r15d
	add r11d, r13d
	add ebp, r11d
	rorx r13d, r12d, 2
	rorx r15d, r12d, 13
	xor r13d, r15d
	rorx r15d, r12d, 22
	xor r13d, r15d
	add r11d, r13d
	mov r13d, r12d
	xor r13d, eax
	and r14d, r13d
	xor r14d, eax
	add r11d, r14d
	add r10d, 1294757372
	add r10d, DWORD PTR [rcx+280]
	andn r15d, ebp, r9d
	add r10d, r15d
	mov r14d, ebp
	and r14d, r8d
	add r10d, r14d
	rorx r14d, ebp, 6
	rorx r15d, ebp, 11
	xor r14d, r15d
	rorx r15d, ebp, 25
	xor r14d, r15d
	add r10d, r14d
	add ebx, r10d
	rorx r14d, r11d, 2
	rorx r15d, r11d, 13
	xor r14d, r15d
	rorx r15d, r11d, 22
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r11d
	xor r14d, r12d
	and r13d, r14d
	xor r13d, r12d
	add r10d, r13d
	add r9d, 1396182291
	add r9d, DWORD PTR [rcx+284]
	andn r15d, ebx, r8d
	add r9d, r15d
	mov r13d, ebx
	and r13d, ebp
	add r9d, r13d
	rorx r13d, ebx, 6
	rorx r15d, ebx, 11
	xor r13d, r15d
	rorx r15d, ebx, 25
	xor r13d, r15d
	add r9d, r13d
	add eax, r9d
	rorx r13d, r10d, 2
	rorx r15d, r10d, 13
	xor r13d, r15d
	rorx r15d, r10d, 22
	xor r13d, r15d
	add r9d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r14d, r13d
	xor r14d, r11d
	add r9d, r14d
	add r8d, 1695183700
	add r8d, DWORD PTR [rcx+304]
	andn r15d, eax, ebp
	add r8d, r15d
	mov r14d, eax
	and r14d, ebx
	add r8d, r14d
	rorx r14d, eax, 6
	rorx r15d, eax, 11
	xor r14d, r15d
	rorx r15d, eax, 25
	xor r14d, r15d
	add r8d, r14d
	add r12d, r8d
	rorx r14d, r9d, 2
	rorx r15d, r9d, 13
	xor r14d, r15d
	rorx r15d, r9d, 22
	xor r14d, r15d
	add r8d, r14d
	mov r14d, r9d
	xor r14d, r10d
	and r13d, r14d
	xor r13d, r10d
	add r8d, r13d
	add ebp, 1986661051
	add ebp, DWORD PTR [rcx+308]
	andn r15d, r12d, ebx
	add ebp, r15d
	mov r13d, r12d
	and r13d, eax
	add ebp, r13d
	rorx r13d, r12d, 6
	rorx r15d, r12d, 11
	xor r13d, r15d
	rorx r15d, r12d, 25
	xor r13d, r15d
	add ebp, r13d
	add r11d, ebp
	rorx r13d, r8d, 2
	rorx r15d, r8d, 13
	xor r13d, r15d
	rorx r15d, r8d, 22
	xor r13d, r15d
	add ebp, r13d
	mov r13d, r8d
	xor r13d, r9d
	and r14d, r13d
	xor r14d, r9d
	add ebp, r14d
	add ebx, -2117940946
	add ebx, DWORD PTR [rcx+312]
	andn r15d, r11d, eax
	add ebx, r15d
	mov r14d, r11d
	and r14d, r12d
	add ebx, r14d
	rorx r14d, r11d, 6
	rorx r15d, r11d, 11
	xor r14d, r15d
	rorx r15d, r11d, 25
	xor r14d, r15d
	add ebx, r14d
	add r10d, ebx
	rorx r14d, ebp, 2
	rorx r15d, ebp, 13
	xor r14d, r15d
	rorx r15d, ebp, 22
	xor r14d, r15d
	add ebx, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r13d, r14d
	xor r13d, r8d
	add ebx, r13d
	add eax, -1838011259
	add eax, DWORD PTR [rcx+316]
	andn r15d, r10d, r12d
	add eax, r15d
	mov r13d, r10d
	and r13d, r11d
	add eax, r13d
	rorx r13d, r10d, 6
	rorx r15d, r10d, 11
	xor r13d, r15d
	rorx r15d, r10d, 25
	xor r13d, r15d
	add eax, r13d
	add r9d, eax
	rorx r13d, ebx, 2
	rorx r15d, ebx, 13
	xor r13d, r15d
	rorx r15d, ebx, 22
	xor r13d, r15d
	add eax, r13d
	mov r13d, ebx
	xor r13d, ebp
	and r14d, r13d
	xor r14d, ebp
	add eax, r14d
	add r12d, -1564481375
	add r12d, DWORD PTR [rcx+336]
	andn r15d, r9d, r11d
	add r12d, r15d
	mov r14d, r9d
	and r14d, r10d
	add r12d, r14d
	rorx r14d, r9d, 6
	rorx r15d, r9d, 11
	xor r14d, r15d
	rorx r15d, r9d, 25
	xor r14d, r15d
	add r12d, r14d
	add r8d, r12d
	rorx r14d, eax, 2
	rorx r15d, eax, 13
	xor r14d, r15d
	rorx r15d, eax, 22
	xor r14d, r15d
	add r12d, r14d
	mov r14d, eax
	xor r14d, ebx
	and r13d, r14d
	xor r13d, ebx
	add r12d, r13d
	add r11d, -1474664885
	add r11d, DWORD PTR [rcx+340]
	andn r15d, r8d, r10d
	add r11d, r15d
	mov r13d, r8d
	and r13d, r9d
	add r11d, r13d
	rorx r13d, r8d, 6
	rorx r15d, r8d, 11
	xor r13d, r15d
	rorx r15d, r8d, 25
	xor r13d, r15d
	add r11d, r13d
	add ebp, r11d
	rorx r13d, r12d, 2
	rorx r15d, r12d, 13
	xor r13d, r15d
	rorx r15d, r12d, 22
	xor r13d, r15d
	add r11d, r13d
	mov r13d, r12d
	xor r13d, eax
	and r14d, r13d
	xor r14d, eax
	add r11d, r14d
	add r10d, -1035236496
	add r10d, DWORD PTR [rcx+344]
	andn r15d, ebp, r9d
	add r10d, r15d
	mov r14d, ebp
	and r14d, r8d
	add r10d, r14d
	rorx r14d, ebp, 6
	rorx r15d, ebp, 11
	xor r14d, r15d
	rorx r15d, ebp, 25
	xor r14d, r15d
	add r10d, r14d
	add ebx, r10d
	rorx r14d, r11d, 2
	rorx r15d, r11d, 13
	xor r14d, r15d
	rorx r15d, r11d, 22
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r11d
	xor r14d, r12d
	and r13d, r14d
	xor r13d, r12d
	add r10d, r13d
	add r9d, -949202525
	add r9d, DWORD PTR [rcx+348]
	andn r15d, ebx, r8d
	add r9d, r15d
	mov r13d, ebx
	and r13d, ebp
	add r9d, r13d
	rorx r13d, ebx, 6
	rorx r15d, ebx, 11
	xor r13d, r15d
	rorx r15d, ebx, 25
	xor r13d, r15d
	add r9d, r13d
	add eax, r9d
	rorx r13d, r10d, 2
	rorx r15d, r10d, 13
	xor r13d, r15d
	rorx r15d, r10d, 22
	xor r13d, r15d
	add r9d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r14d, r13d
	xor r14d, r11d
	add r9d, r14d
	add r8d, -778901479
	add r8d, DWORD PTR [rcx+368]
	andn r15d, eax, ebp
	add r8d, r15d
	mov r14d, eax
	and r14d, ebx
	add r8d, r14d
	rorx r14d, eax, 6
	rorx r15d, eax, 11
	xor r14d, r15d
	rorx r15d, eax, 25
	xor r14d, r15d
	add r8d, r14d
	add r12d, r8d
	rorx r14d, r9d, 2
	rorx r15d, r9d, 13
	xor r14d, r15d
	rorx r15d, r9d, 22
	xor r14d, r15d
	add r8d, r14d
	mov r14d, r9d
	xor r14d, r10d
	and r13d, r14d
	xor r13d, r10d
	add r8d, r13d
	add ebp, -694614492
	add ebp, DWORD PTR [rcx+372]
	andn r15d, r12d, ebx
	add ebp, r15d
	mov r13d, r12d
	and r13d, eax
	add ebp, r13d
	rorx r13d, r12d, 6
	rorx r15d, r12d, 11
	xor r13d, r15d
	rorx r15d, r12d, 25
	xor r13d, r15d
	add ebp, r13d
	add r11d, ebp
	rorx r13d, r8d, 2
	rorx r15d, r8d, 13
	xor r13d, r15d
	rorx r15d, r8d, 22
	xor r13d, r15d
	add ebp, r13d
	mov r13d, r8d
	xor r13d, r9d
	and r14d, r13d
	xor r14d, r9d
	add ebp, r14d
	add ebx, -200395387
	add ebx, DWORD PTR [rcx+376]
	andn r15d, r11d, eax
	add ebx, r15d
	mov r14d, r11d
	and r14d, r12d
	add ebx, r14d
	rorx r14d, r11d, 6
	rorx r15d, r11d, 11
	xor r14d, r15d
	rorx r15d, r11d, 25
	xor r14d, r15d
	add ebx, r14d
	add r10d, ebx
	rorx r14d, ebp, 2
	rorx r15d, ebp, 13
	xor r14d, r15d
	rorx r15d, ebp, 22
	xor r14d, r15d
	add ebx, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r13d, r14d
	xor r13d, r8d
	add ebx, r13d
	add eax, 275423344
	add eax, DWORD PTR [rcx+380]
	andn r15d, r10d, r12d
	add eax, r15d
	mov r13d, r10d
	and r13d, r11d
	add eax, r13d
	rorx r13d, r10d, 6
	rorx r15d, r10d, 11
	xor r13d, r15d
	rorx r15d, r10d, 25
	xor r13d, r15d
	add eax, r13d
	add r9d, eax
	rorx r13d, ebx, 2
	rorx r15d, ebx, 13
	xor r13d, r15d
	rorx r15d, ebx, 22
	xor r13d, r15d
	add eax, r13d
	mov r13d, ebx
	xor r13d, ebp
	and r14d, r13d
	xor r14d, ebp
	add eax, r14d
	add r12d, 430227734
	add r12d, DWORD PTR [rcx+400]
	andn r15d, r9d, r11d
	add r12d, r15d
	mov r14d, r9d
	and r14d, r10d
	add r12d, r14d
	rorx r14d, r9d, 6
	rorx r15d, r9d, 11
	xor r14d, r15d
	rorx r15d, r9d, 25
	xor r14d, r15d
	add r12d, r14d
	add r8d, r12d
	rorx r14d, eax, 2
	rorx r15d, eax, 13
	xor r14d, r15d
	rorx r15d, eax, 22
	xor r14d, r15d
	add r12d, r14d
	mov r14d, eax
	xor r14d, ebx
	and r13d, r14d
	xor r13d, ebx
	add r12d, r13d
	add r11d, 506948616
	add r11d, DWORD PTR [rcx+404]
	andn r15d, r8d, r10d
	add r11d, r15d
	mov r13d, r8d
	and r13d, r9d
	add r11d, r13d
	rorx r13d, r8d, 6
	rorx r15d, r8d, 11
	xor r13d, r15d
	rorx r15d, r8d, 25
	xor r13d, r15d
	add r11d, r13d
	add ebp, r11d
	rorx r13d, r12d, 2
	rorx r15d, r12d, 13
	xor r13d, r15d
	rorx r15d, r12d, 22
	xor r13d, r15d
	add r11d, r13d
	mov r13d, r12d
	xor r13d, eax
	and r14d, r13d
	xor r14d, eax
	add r11d, r14d
	add r10d, 659060556
	add r10d, DWORD PTR [rcx+408]
	andn r15d, ebp, r9d
	add r10d, r15d
	mov r14d, ebp
	and r14d, r8d
	add r10d, r14d
	rorx r14d, ebp, 6
	rorx r15d, ebp, 11
	xor r14d, r15d
	rorx r15d, ebp, 25
	xor r14d, r15d
	add r10d, r14d
	add ebx, r10d
	rorx r14d, r11d, 2
	rorx r15d, r11d, 13
	xor r14d, r15d
	rorx r15d, r11d, 22
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r11d
	xor r14d, r12d
	and r13d, r14d
	xor r13d, r12d
	add r10d, r13d
	add r9d, 883997877
	add r9d, DWORD PTR [rcx+412]
	andn r15d, ebx, r8d
	add r9d, r15d
	mov r13d, ebx
	and r13d, ebp
	add r9d, r13d
	rorx r13d, ebx, 6
	rorx r15d, ebx, 11
	xor r13d, r15d
	rorx r15d, ebx, 25
	xor r13d, r15d
	add r9d, r13d
	add eax, r9d
	rorx r13d, r10d, 2
	rorx r15d, r10d, 13
	xor r13d, r15d
	rorx r15d, r10d, 22
	xor r13d, r15d
	add r9d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r14d, r13d
	xor r14d, r11d
	add r9d, r14d
	add r8d, 958139571
	add r8d, DWORD PTR [rcx+432]
	andn r15d, eax, ebp
	add r8d, r15d
	mov r14d, eax
	and r14d, ebx
	add r8d, r14d
	rorx r14d, eax, 6
	rorx r15d, eax, 11
	xor r14d, r15d
	rorx r15d, eax, 25
	xor r14d, r15d
	add r8d, r14d
	add r12d, r8d
	rorx r14d, r9d, 2
	rorx r15d, r9d, 13
	xor r14d, r15d
	rorx r15d, r9d, 22
	xor r14d, r15d
	add r8d, r14d
	mov r14d, r9d
	xor r14d, r10d
	and r13d, r14d
	xor r13d, r10d
	add r8d, r13d
	add ebp, 1322822218
	add ebp, DWORD PTR [rcx+436]
	andn r15d, r12d, ebx
	add ebp, r15d
	mov r13d, r12d
	and r13d, eax
	add ebp, r13d
	rorx r13d, r12d, 6
	rorx r15d, r12d, 11
	xor r13d, r15d
	rorx r15d, r12d, 25
	xor r13d, r15d
	add ebp, r13d
	add r11d, ebp
	rorx r13d, r8d, 2
	rorx r15d, r8d, 13
	xor r13d, r15d
	rorx r15d, r8d, 22
	xor r13d, r15d
	add ebp, r13d
	mov r13d, r8d
	xor r13d, r9d
	and r14d, r13d
	xor r14d, r9d
	add ebp, r14d
	add ebx, 1537002063
	add ebx, DWORD PTR [rcx+440]
	andn r15d, r11d, eax
	add ebx, r15d
	mov r14d, r11d
	and r14d, r12d
	add ebx, r14d
	rorx r14d, r11d, 6
	rorx r15d, r11d, 11
	xor r14d, r15d
	rorx r15d, r11d, 25
	xor r14d, r15d
	add ebx, r14d
	add r10d, ebx
	rorx r14d, ebp, 2
	rorx r15d, ebp, 13
	xor r14d, r15d
	rorx r15d, ebp, 22
	xor r14d, r15d
	add ebx, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r13d, r14d
	xor r13d, r8d
	add ebx, r13d
	add eax, 1747873779
	add eax, DWORD PTR [rcx+444]
	andn r15d, r10d, r12d
	add eax, r15d
	mov r13d, r10d
	and r13d, r11d
	add eax, r13d
	rorx r13d, r10d, 6
	rorx r15d, r10d, 11
	xor r13d, r15d
	rorx r15d, r10d, 25
	xor r13d, r15d
	add eax, r13d
	add r9d, eax
	rorx r13d, ebx, 2
	rorx r15d, ebx, 13
	xor r13d, r15d
	rorx r15d, ebx, 22
	xor r13d, r15d
	add eax, r13d
	mov r13d, ebx
	xor r13d, ebp
	and r14d, r13d
	xor r14d, ebp
	add eax, r14d
	add r12d, 1955562222
	add r12d, DWORD PTR [rcx+464]
	andn r15d, r9d, r11d
	add r12d, r15d
	mov r14d, r9d
	and r14d, r10d
	add r12d, r14d
	rorx r14d, r9d, 6
	rorx r15d, r9d, 11
	xor r14d, r15d
	rorx r15d, r9d, 25
	xor r14d, r15d
	add r12d, r14d
	add r8d, r12d
	rorx r14d, eax, 2
	rorx r15d, eax, 13
	xor r14d, r15d
	rorx r15d, eax, 22
	xor r14d, r15d
	add r12d, r14d
	mov r14d, eax
	xor r14d, ebx
	and r13d, r14d
	xor r13d, ebx
	add r12d, r13d
	add r11d, 2024104815
	add r11d, DWORD PTR [rcx+468]
	andn r15d, r8d, r10d
	add r11d, r15d
	mov r13d, r8d
	and r13d, r9d
	add r11d, r13d
	rorx r13d, r8d, 6
	rorx r15d, r8d, 11
	xor r13d, r15d
	rorx r15d, r8d, 25
	xor r13d, r15d
	add r11d, r13d
	add ebp, r11d
	rorx r13d, r12d, 2
	rorx r15d, r12d, 13
	xor r13d, r15d
	rorx r15d, r12d, 22
	xor r13d, r15d
	add r11d, r13d
	mov r13d, r12d
	xor r13d, eax
	and r14d, r13d
	xor r14d, eax
	add r11d, r14d
	add r10d, -2067236844
	add r10d, DWORD PTR [rcx+472]
	andn r15d, ebp, r9d
	add r10d, r15d
	mov r14d, ebp
	and r14d, r8d
	add r10d, r14d
	rorx r14d, ebp, 6
	rorx r15d, ebp, 11
	xor r14d, r15d
	rorx r15d, ebp, 25
	xor r14d, r15d
	add r10d, r14d
	add ebx, r10d
	rorx r14d, r11d, 2
	rorx r15d, r11d, 13
	xor r14d, r15d
	rorx r15d, r11d, 22
	xor r14d, r15d
	add r10d, r14d
	mov r14d, r11d
	xor r14d, r12d
	and r13d, r14d
	xor r13d, r12d
	add r10d, r13d
	add r9d, -1933114872
	add r9d, DWORD PTR [rcx+476]
	andn r15d, ebx, r8d
	add r9d, r15d
	mov r13d, ebx
	and r13d, ebp
	add r9d, r13d
	rorx r13d, ebx, 6
	rorx r15d, ebx, 11
	xor r13d, r15d
	rorx r15d, ebx, 25
	xor r13d, r15d
	add r9d, r13d
	add eax, r9d
	rorx r13d, r10d, 2
	rorx r15d, r10d, 13
	xor r13d, r15d
	rorx r15d, r10d, 22
	xor r13d, r15d
	add r9d, r13d
	mov r13d, r10d
	xor r13d, r11d
	and r14d, r13d
	xor r14d, r11d
	add r9d, r14d
	add r8d, -1866530822
	add r8d, DWORD PTR [rcx+496]
	andn r15d, eax, ebp
	add r8d, r15d
	mov r14d, eax
	and r14d, ebx
	add r8d, r14d
	rorx r14d, eax, 6
	rorx r15d, eax, 11
	xor r14d, r15d
	rorx r15d, eax, 25
	xor r14d, r15d
	add r8d, r14d
	add r12d, r8d
	rorx r14d, r9d, 2
	rorx r15d, r9d, 13
	xor r14d, r15d
	rorx r15d, r9d, 22
	xor r14d, r15d
	add r8d, r14d
	mov r14d, r9d
	xor r14d, r10d
	and r13d, r14d
	xor r13d, r10d
	add r8d, r13d
	add ebp, -1538233109
	add ebp, DWORD PTR [rcx+500]
	andn r15d, r12d, ebx
	add ebp, r15d
	mov r13d, r12d
	and r13d, eax
	add ebp, r13d
	rorx r13d, r12d, 6
	rorx r15d, r12d, 11
	xor r13d, r15d
	rorx r15d, r12d, 25
	xor r13d, r15d
	add ebp, r13d
	add r11d, ebp
	rorx r13d, r8d, 2
	rorx r15d, r8d, 13
	xor r13d, r15d
	rorx r15d, r8d, 22
	xor r13d, r15d
	add ebp, r13d
	mov r13d, r8d
	xor r13d, r9d
	and r14d, r13d
	xor r14d, r9d
	add ebp, r14d
	add ebx, -1090935817
	add ebx, DWORD PTR [rcx+504]
	andn r15d, r11d, eax
	add ebx, r15d
	mov r14d, r11d
	and r14d, r12d
	add ebx, r14d
	rorx r14d, r11d, 6
	rorx r15d, r11d, 11
	xor r14d, r15d
	rorx r15d, r11d, 25
	xor r14d, r15d
	add ebx, r14d
	add r10d, ebx
	rorx r14d, ebp, 2
	rorx r15d, ebp, 13
	xor r14d, r15d
	rorx r15d, ebp, 22
	xor r14d, r15d
	add ebx, r14d
	mov r14d, ebp
	xor r14d, r8d
	and r13d, r14d
	xor r13d, r8d
	add ebx, r13d
	add eax, -965641998
	add eax, DWORD PTR [rcx+508]
	andn r15d, r10d, r12d
	add eax, r15d
	mov r13d, r10d
	and r13d, r11d
	add eax, r13d
	rorx r13d, r10d, 6
	rorx r15d, r10d, 11
	xor r13d, r15d
	rorx r15d, r10d, 25
	xor r13d, r15d
	add eax, r13d
	add r9d, eax
	rorx r13d, ebx, 2
	rorx r15d, ebx, 13
	xor r13d, r15d
	rorx r15d, ebx, 22
	xor r13d, r15d
	add eax, r13d
	mov r13d, ebx
	xor r13d, ebp
	and r14d, r13d
	xor r14d, ebp
	add eax, r14d
	add eax, DWORD PTR [rdi]
	add ebx, DWORD PTR [rdi+4]
	add ebp, DWORD PTR [rdi+8]
	add r8d, DWORD PTR [rdi+12]
	add r9d, DWORD PTR [rdi+16]
	add r10d, DWORD PTR [rdi+20]
	add r11d, DWORD PTR [rdi+24]
	add r12d, DWORD PTR [rdi+28]
	mov DWORD PTR [rdi], eax
	mov DWORD PTR [rdi+4], ebx
	mov DWORD PTR [rdi+8], ebp
	mov DWORD PTR [rdi+12], r8d
	mov DWORD PTR [rdi+16], r9d
	mov DWORD PTR [rdi+20], r10d
	mov DWORD PTR [rdi+24], r11d
	mov DWORD PTR [rdi+28], r12d
	add rsi, 128
	sub rdx, 2
	jmp 26f
25:
	add rsi, 64
	sub rdx, 1
26:
	jne 22b
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [rcx+512]
	mov rbp, QWORD PTR [rcx+520]
	mov r12, QWORD PTR [rcx+528]
	mov r13, QWORD PTR [rcx+536]
	mov r14, QWORD PTR [rcx+544]
	mov r15, QWORD PTR [rcx+552]
	vzeroupper
	ret
	.p2align 6
