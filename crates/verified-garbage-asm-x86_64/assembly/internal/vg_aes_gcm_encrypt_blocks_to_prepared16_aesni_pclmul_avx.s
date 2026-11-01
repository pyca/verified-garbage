// The functions of `src/internal/vg_aes_gcm_encrypt_blocks_to_prepared16_aesni_pclmul_avx.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_gcm_encrypt_blocks_to_prepared16_aesni_pclmul_avx:
	mov r11, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [r11], rdi
	mov QWORD PTR [r11+8], rsi
	mov QWORD PTR [r11+16], rdx
	mov QWORD PTR [r11+24], rcx
	mov QWORD PTR [r11+32], r8
	mov QWORD PTR [r11+40], r9
	mov QWORD PTR [r11+48], r10
	cmp r9, 16
	jb 20f
	mov rax, r9
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r8
	mov QWORD PTR [r11+32], rax
	mov rax, r9
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, r10
	mov QWORD PTR [r11+48], rax
	mov eax, 0
	mov QWORD PTR [r11+40], rax
	add r11, 127
	and r11, -64
	mov QWORD PTR [r11+816], rbx
	mov rbx, r8
	sub rbx, r10
	mov r8, r10
	movabs rax, 579005069656919567
	vmovq xmm0, rax
	movabs rax, 283686952306183
	vmovq xmm12, rax
	vpunpcklqdq xmm0, xmm0, xmm12
	movabs rax, 0
	vmovq xmm1, rax
	movabs rax, -4467570830351532032
	vmovq xmm12, rax
	vpunpcklqdq xmm1, xmm1, xmm12
	vmovdqu xmm3, XMMWORD PTR [rdi+272]
	vmovdqu xmm4, XMMWORD PTR [rdi+256]
	vmovdqu xmm5, XMMWORD PTR [rdi+304]
	vmovdqu xmm6, XMMWORD PTR [rdi+288]
	vmovdqu xmm12, XMMWORD PTR [rdi+336]
	vmovdqu xmm13, XMMWORD PTR [rdi+320]
	vmovdqu xmm14, XMMWORD PTR [rdi+368]
	vmovdqu xmm15, XMMWORD PTR [rdi+352]
	vmovdqu XMMWORD PTR [r11+240], xmm3
	vmovdqu XMMWORD PTR [r11+224], xmm4
	vmovdqu XMMWORD PTR [r11+208], xmm5
	vmovdqu XMMWORD PTR [r11+192], xmm6
	vmovdqu XMMWORD PTR [r11+176], xmm12
	vmovdqu XMMWORD PTR [r11+160], xmm13
	vmovdqu XMMWORD PTR [r11+144], xmm14
	vmovdqu XMMWORD PTR [r11+128], xmm15
	vmovdqu xmm2, XMMWORD PTR [rcx]
	vpshufb xmm2, xmm2, xmm0
	mov r10, rsi
	shl r10, 4
	add r10, rdi
	mov rax, rdx
	mov rdx, r8
	vmovdqu XMMWORD PTR [r11+768], xmm0
	vmovdqu XMMWORD PTR [r11+784], xmm1
	mov QWORD PTR [r11+808], rdx
	mov QWORD PTR [r11+800], rsi
	mov rsi, rax
	vmovdqu xmm7, XMMWORD PTR [rax]
	mov r8d, DWORD PTR [rax+12]
	bswap r8d
	vmovdqu XMMWORD PTR [r11+640], xmm7
	vmovdqu XMMWORD PTR [r11+656], xmm7
	vmovdqu XMMWORD PTR [r11+672], xmm7
	vmovdqu XMMWORD PTR [r11+688], xmm7
	vmovdqu XMMWORD PTR [r11+704], xmm7
	vmovdqu XMMWORD PTR [r11+720], xmm7
	vmovdqu XMMWORD PTR [r11+736], xmm7
	vmovdqu XMMWORD PTR [r11+752], xmm7
	mov eax, r8d
	add eax, 0
	bswap eax
	mov DWORD PTR [r11+652], eax
	mov eax, r8d
	add eax, 1
	bswap eax
	mov DWORD PTR [r11+668], eax
	mov eax, r8d
	add eax, 2
	bswap eax
	mov DWORD PTR [r11+684], eax
	mov eax, r8d
	add eax, 3
	bswap eax
	mov DWORD PTR [r11+700], eax
	mov eax, r8d
	add eax, 4
	bswap eax
	mov DWORD PTR [r11+716], eax
	mov eax, r8d
	add eax, 5
	bswap eax
	mov DWORD PTR [r11+732], eax
	mov eax, r8d
	add eax, 6
	bswap eax
	mov DWORD PTR [r11+748], eax
	mov eax, r8d
	add eax, 7
	bswap eax
	mov DWORD PTR [r11+764], eax
	add r8d, 8
	mov rax, rdi
	add rax, 160
	cmp r10, rax
	je 22f
	add rax, 32
	cmp r10, rax
	je 24f
	vpshufb xmm11, xmm7, xmm0
	movabs rax, 1
	vmovq xmm12, rax
	vpaddd xmm11, xmm11, xmm12
	vpshufb xmm3, xmm11, xmm0
	vpaddd xmm11, xmm11, xmm12
	vpshufb xmm4, xmm11, xmm0
	vpaddd xmm11, xmm11, xmm12
	vpshufb xmm5, xmm11, xmm0
	vpaddd xmm11, xmm11, xmm12
	vpshufb xmm6, xmm11, xmm0
	vpaddd xmm11, xmm11, xmm12
	vpshufb xmm13, xmm11, xmm0
	vpaddd xmm11, xmm11, xmm12
	vpshufb xmm14, xmm11, xmm0
	vpaddd xmm11, xmm11, xmm12
	vpshufb xmm15, xmm11, xmm0
	vpor xmm0, xmm7, xmm7
	vmovdqu xmm1, XMMWORD PTR [rdi]
	vpxor xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm1
	vpxor xmm4, xmm4, xmm1
	vpxor xmm5, xmm5, xmm1
	vpxor xmm6, xmm6, xmm1
	vpxor xmm13, xmm13, xmm1
	vpxor xmm14, xmm14, xmm1
	vpxor xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+16]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	mov eax, r8d
	add eax, 0
	bswap eax
	mov DWORD PTR [r11+652], eax
	mov eax, r8d
	add eax, 1
	bswap eax
	mov DWORD PTR [r11+668], eax
	mov eax, r8d
	add eax, 2
	bswap eax
	mov DWORD PTR [r11+684], eax
	mov eax, r8d
	add eax, 3
	bswap eax
	mov DWORD PTR [r11+700], eax
	vmovdqu xmm1, XMMWORD PTR [rdi+32]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	mov eax, r8d
	add eax, 4
	bswap eax
	mov DWORD PTR [r11+716], eax
	mov eax, r8d
	add eax, 5
	bswap eax
	mov DWORD PTR [r11+732], eax
	mov eax, r8d
	add eax, 6
	bswap eax
	mov DWORD PTR [r11+748], eax
	mov eax, r8d
	add eax, 7
	bswap eax
	mov DWORD PTR [r11+764], eax
	vmovdqu xmm1, XMMWORD PTR [rdi+48]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+64]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+80]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+96]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+112]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+128]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+144]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+160]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+176]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+192]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+208]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [r10]
	vaesenclast xmm0, xmm0, xmm1
	vaesenclast xmm3, xmm3, xmm1
	vaesenclast xmm4, xmm4, xmm1
	vaesenclast xmm5, xmm5, xmm1
	vaesenclast xmm6, xmm6, xmm1
	vaesenclast xmm13, xmm13, xmm1
	vaesenclast xmm14, xmm14, xmm1
	vaesenclast xmm15, xmm15, xmm1
	vpxor xmm0, xmm0, XMMWORD PTR [rdx+rbx*1]
	vmovdqu XMMWORD PTR [rdx], xmm0
	vpxor xmm3, xmm3, XMMWORD PTR [rdx+rbx*1+16]
	vmovdqu XMMWORD PTR [rdx+16], xmm3
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+rbx*1+32]
	vmovdqu XMMWORD PTR [rdx+32], xmm4
	vpxor xmm5, xmm5, XMMWORD PTR [rdx+rbx*1+48]
	vmovdqu XMMWORD PTR [rdx+48], xmm5
	vpxor xmm6, xmm6, XMMWORD PTR [rdx+rbx*1+64]
	vmovdqu XMMWORD PTR [rdx+64], xmm6
	vpxor xmm13, xmm13, XMMWORD PTR [rdx+rbx*1+80]
	vmovdqu XMMWORD PTR [rdx+80], xmm13
	vpxor xmm14, xmm14, XMMWORD PTR [rdx+rbx*1+96]
	vmovdqu XMMWORD PTR [rdx+96], xmm14
	vpxor xmm15, xmm15, XMMWORD PTR [rdx+rbx*1+112]
	vmovdqu XMMWORD PTR [rdx+112], xmm15
	add r8d, 8
	vmovdqu xmm0, XMMWORD PTR [r11+640]
	vmovdqu xmm3, XMMWORD PTR [r11+656]
	vmovdqu xmm4, XMMWORD PTR [r11+672]
	vmovdqu xmm5, XMMWORD PTR [r11+688]
	vmovdqu xmm6, XMMWORD PTR [r11+704]
	vmovdqu xmm13, XMMWORD PTR [r11+720]
	vmovdqu xmm14, XMMWORD PTR [r11+736]
	vmovdqu xmm15, XMMWORD PTR [r11+752]
	vmovdqu xmm1, XMMWORD PTR [rdi]
	vpxor xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm1
	vpxor xmm4, xmm4, xmm1
	vpxor xmm5, xmm5, xmm1
	vpxor xmm6, xmm6, xmm1
	vpxor xmm13, xmm13, xmm1
	vpxor xmm14, xmm14, xmm1
	vpxor xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+16]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	mov eax, r8d
	add eax, 0
	bswap eax
	mov DWORD PTR [r11+652], eax
	mov eax, r8d
	add eax, 1
	bswap eax
	mov DWORD PTR [r11+668], eax
	mov eax, r8d
	add eax, 2
	bswap eax
	mov DWORD PTR [r11+684], eax
	mov eax, r8d
	add eax, 3
	bswap eax
	mov DWORD PTR [r11+700], eax
	vmovdqu xmm1, XMMWORD PTR [rdi+32]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	mov eax, r8d
	add eax, 4
	bswap eax
	mov DWORD PTR [r11+716], eax
	mov eax, r8d
	add eax, 5
	bswap eax
	mov DWORD PTR [r11+732], eax
	mov eax, r8d
	add eax, 6
	bswap eax
	mov DWORD PTR [r11+748], eax
	mov eax, r8d
	add eax, 7
	bswap eax
	mov DWORD PTR [r11+764], eax
	vmovdqu xmm1, XMMWORD PTR [rdi+48]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+64]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+80]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+96]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+112]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+128]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+144]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+160]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+176]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+192]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+208]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [r10]
	vaesenclast xmm0, xmm0, xmm1
	vaesenclast xmm3, xmm3, xmm1
	vaesenclast xmm4, xmm4, xmm1
	vaesenclast xmm5, xmm5, xmm1
	vaesenclast xmm6, xmm6, xmm1
	vaesenclast xmm13, xmm13, xmm1
	vaesenclast xmm14, xmm14, xmm1
	vaesenclast xmm15, xmm15, xmm1
	vpxor xmm0, xmm0, XMMWORD PTR [rdx+rbx*1+128]
	vmovdqu XMMWORD PTR [rdx+128], xmm0
	vpxor xmm3, xmm3, XMMWORD PTR [rdx+rbx*1+144]
	vmovdqu XMMWORD PTR [rdx+144], xmm3
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+rbx*1+160]
	vmovdqu XMMWORD PTR [rdx+160], xmm4
	vpxor xmm5, xmm5, XMMWORD PTR [rdx+rbx*1+176]
	vmovdqu XMMWORD PTR [rdx+176], xmm5
	vpxor xmm6, xmm6, XMMWORD PTR [rdx+rbx*1+192]
	vmovdqu XMMWORD PTR [rdx+192], xmm6
	vpxor xmm13, xmm13, XMMWORD PTR [rdx+rbx*1+208]
	vmovdqu XMMWORD PTR [rdx+208], xmm13
	vpxor xmm14, xmm14, XMMWORD PTR [rdx+rbx*1+224]
	vmovdqu XMMWORD PTR [rdx+224], xmm14
	vpxor xmm15, xmm15, XMMWORD PTR [rdx+rbx*1+240]
	vmovdqu XMMWORD PTR [rdx+240], xmm15
	add r8d, 8
	cmp r9, 24
	jb 26f
28:
	vmovdqu xmm0, XMMWORD PTR [r11+640]
	vmovdqu xmm3, XMMWORD PTR [r11+656]
	vmovdqu xmm4, XMMWORD PTR [r11+672]
	vmovdqu xmm5, XMMWORD PTR [r11+688]
	vmovdqu xmm6, XMMWORD PTR [r11+704]
	vmovdqu xmm13, XMMWORD PTR [r11+720]
	vmovdqu xmm14, XMMWORD PTR [r11+736]
	vmovdqu xmm15, XMMWORD PTR [r11+752]
	vmovdqu xmm1, XMMWORD PTR [rdi]
	vpxor xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm1
	vpxor xmm4, xmm4, xmm1
	vpxor xmm5, xmm5, xmm1
	vpxor xmm6, xmm6, xmm1
	vpxor xmm13, xmm13, xmm1
	vpxor xmm14, xmm14, xmm1
	vpxor xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+16]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+144]
	vmovdqu xmm7, XMMWORD PTR [rdx+16]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm8, xmm7, xmm12, 0
	vpclmulqdq xmm10, xmm7, xmm12, 17
	vpclmulqdq xmm9, xmm7, xmm12, 1
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	mov eax, r8d
	add eax, 0
	bswap eax
	mov DWORD PTR [r11+652], eax
	mov eax, r8d
	add eax, 1
	bswap eax
	mov DWORD PTR [r11+668], eax
	mov eax, r8d
	add eax, 2
	bswap eax
	mov DWORD PTR [r11+684], eax
	mov eax, r8d
	add eax, 3
	bswap eax
	mov DWORD PTR [r11+700], eax
	vmovdqu xmm1, XMMWORD PTR [rdi+32]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+160]
	vmovdqu xmm7, XMMWORD PTR [rdx+32]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	mov eax, r8d
	add eax, 4
	bswap eax
	mov DWORD PTR [r11+716], eax
	mov eax, r8d
	add eax, 5
	bswap eax
	mov DWORD PTR [r11+732], eax
	mov eax, r8d
	add eax, 6
	bswap eax
	mov DWORD PTR [r11+748], eax
	mov eax, r8d
	add eax, 7
	bswap eax
	mov DWORD PTR [r11+764], eax
	vmovdqu xmm1, XMMWORD PTR [rdi+48]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+64]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+176]
	vmovdqu xmm7, XMMWORD PTR [rdx+48]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+80]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+96]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+192]
	vmovdqu xmm7, XMMWORD PTR [rdx+64]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+112]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+128]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+208]
	vmovdqu xmm7, XMMWORD PTR [rdx+80]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+144]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+160]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+224]
	vmovdqu xmm7, XMMWORD PTR [rdx+96]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+176]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+240]
	vmovdqu xmm7, XMMWORD PTR [rdx+112]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+192]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+128]
	vmovdqu xmm7, XMMWORD PTR [rdx]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpxor xmm7, xmm7, xmm2
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+208]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [r11+784]
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm9, xmm9, xmm8
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm9, xmm1, 16
	vpshufd xmm9, xmm9, 78
	vpxor xmm2, xmm10, xmm9
	vpxor xmm2, xmm2, xmm11
	vmovdqu xmm1, XMMWORD PTR [r10]
	vaesenclast xmm0, xmm0, xmm1
	vaesenclast xmm3, xmm3, xmm1
	vaesenclast xmm4, xmm4, xmm1
	vaesenclast xmm5, xmm5, xmm1
	vaesenclast xmm6, xmm6, xmm1
	vaesenclast xmm13, xmm13, xmm1
	vaesenclast xmm14, xmm14, xmm1
	vaesenclast xmm15, xmm15, xmm1
	vpxor xmm0, xmm0, XMMWORD PTR [rdx+rbx*1+256]
	vmovdqu XMMWORD PTR [rdx+256], xmm0
	vpxor xmm3, xmm3, XMMWORD PTR [rdx+rbx*1+272]
	vmovdqu XMMWORD PTR [rdx+272], xmm3
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+rbx*1+288]
	vmovdqu XMMWORD PTR [rdx+288], xmm4
	vpxor xmm5, xmm5, XMMWORD PTR [rdx+rbx*1+304]
	vmovdqu XMMWORD PTR [rdx+304], xmm5
	vpxor xmm6, xmm6, XMMWORD PTR [rdx+rbx*1+320]
	vmovdqu XMMWORD PTR [rdx+320], xmm6
	vpxor xmm13, xmm13, XMMWORD PTR [rdx+rbx*1+336]
	vmovdqu XMMWORD PTR [rdx+336], xmm13
	vpxor xmm14, xmm14, XMMWORD PTR [rdx+rbx*1+352]
	vmovdqu XMMWORD PTR [rdx+352], xmm14
	vpxor xmm15, xmm15, XMMWORD PTR [rdx+rbx*1+368]
	vmovdqu XMMWORD PTR [rdx+368], xmm15
	add r8d, 8
	add rdx, 128
	sub r9, 8
	cmp r9, 24
	jae 28b
	jmp 27f
26:
27:
	vmovdqu xmm12, XMMWORD PTR [r11+144]
	vmovdqu xmm7, XMMWORD PTR [rdx+16]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm8, xmm7, xmm12, 0
	vpclmulqdq xmm10, xmm7, xmm12, 17
	vpclmulqdq xmm9, xmm7, xmm12, 1
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+160]
	vmovdqu xmm7, XMMWORD PTR [rdx+32]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+176]
	vmovdqu xmm7, XMMWORD PTR [rdx+48]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+192]
	vmovdqu xmm7, XMMWORD PTR [rdx+64]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+208]
	vmovdqu xmm7, XMMWORD PTR [rdx+80]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+224]
	vmovdqu xmm7, XMMWORD PTR [rdx+96]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+240]
	vmovdqu xmm7, XMMWORD PTR [rdx+112]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+128]
	vmovdqu xmm7, XMMWORD PTR [rdx]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpxor xmm7, xmm7, xmm2
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [r11+784]
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm9, xmm9, xmm8
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm9, xmm1, 16
	vpshufd xmm9, xmm9, 78
	vpxor xmm2, xmm10, xmm9
	vpxor xmm2, xmm2, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+144]
	vmovdqu xmm7, XMMWORD PTR [rdx+144]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm8, xmm7, xmm12, 0
	vpclmulqdq xmm10, xmm7, xmm12, 17
	vpclmulqdq xmm9, xmm7, xmm12, 1
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+160]
	vmovdqu xmm7, XMMWORD PTR [rdx+160]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+176]
	vmovdqu xmm7, XMMWORD PTR [rdx+176]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+192]
	vmovdqu xmm7, XMMWORD PTR [rdx+192]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+208]
	vmovdqu xmm7, XMMWORD PTR [rdx+208]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+224]
	vmovdqu xmm7, XMMWORD PTR [rdx+224]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+240]
	vmovdqu xmm7, XMMWORD PTR [rdx+240]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+128]
	vmovdqu xmm7, XMMWORD PTR [rdx+128]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpxor xmm7, xmm7, xmm2
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [r11+784]
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm9, xmm9, xmm8
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm9, xmm1, 16
	vpshufd xmm9, xmm9, 78
	vpxor xmm2, xmm10, xmm9
	vpxor xmm2, xmm2, xmm11
	cmp r9, 16
	je 29f
	vmovdqu xmm0, XMMWORD PTR [r11+640]
	vmovdqu xmm3, XMMWORD PTR [r11+656]
	vmovdqu xmm4, XMMWORD PTR [r11+672]
	vmovdqu xmm5, XMMWORD PTR [r11+688]
	vmovdqu xmm6, XMMWORD PTR [r11+704]
	vmovdqu xmm13, XMMWORD PTR [r11+720]
	vmovdqu xmm14, XMMWORD PTR [r11+736]
	vmovdqu xmm15, XMMWORD PTR [r11+752]
	vmovdqu xmm1, XMMWORD PTR [rdi]
	vpxor xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm1
	vpxor xmm4, xmm4, xmm1
	vpxor xmm5, xmm5, xmm1
	vpxor xmm6, xmm6, xmm1
	vpxor xmm13, xmm13, xmm1
	vpxor xmm14, xmm14, xmm1
	vpxor xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+16]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+32]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+48]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+64]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+80]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+96]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+112]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+128]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+144]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+160]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+176]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+192]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+208]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [r10]
	vaesenclast xmm0, xmm0, xmm1
	vaesenclast xmm3, xmm3, xmm1
	vaesenclast xmm4, xmm4, xmm1
	vaesenclast xmm5, xmm5, xmm1
	vaesenclast xmm6, xmm6, xmm1
	vaesenclast xmm13, xmm13, xmm1
	vaesenclast xmm14, xmm14, xmm1
	vaesenclast xmm15, xmm15, xmm1
	vmovdqu XMMWORD PTR [r11+832], xmm0
	vmovdqu XMMWORD PTR [r11+848], xmm3
	vmovdqu XMMWORD PTR [r11+864], xmm4
	vmovdqu XMMWORD PTR [r11+880], xmm5
	vmovdqu XMMWORD PTR [r11+896], xmm6
	vmovdqu XMMWORD PTR [r11+912], xmm13
	vmovdqu XMMWORD PTR [r11+928], xmm14
	vmovdqu XMMWORD PTR [r11+944], xmm15
	mov r10, r9
	sub r10, 16
	add r8d, r10d
	shl r10, 4
	mov rax, r11
	add rax, 256
	sub rax, r10
	add rdx, 256
	mov r10d, 0
	vmovdqu xmm0, XMMWORD PTR [r11+768]
	vmovdqu xmm1, XMMWORD PTR [r11+784]
	add r11, 64
	add rbx, rdx
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
211:
	vmovdqu xmm13, XMMWORD PTR [rbx+r10*1]
	vmovdqu xmm12, XMMWORD PTR [r11+r10*1+768]
	vpxor xmm13, xmm13, xmm12
	vmovdqu XMMWORD PTR [rdx+r10*1], xmm13
	vpshufb xmm13, xmm13, xmm0
	vpxor xmm13, xmm13, xmm2
	vpxor xmm2, xmm2, xmm2
	vmovdqu xmm12, XMMWORD PTR [rax+r10*1]
	vpclmulqdq xmm11, xmm13, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm13, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm13, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm13, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	add r10, 16
	sub r9, 1
	cmp r9, 16
	jne 211b
	sub rbx, rdx
	sub r11, 64
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm9, xmm9, xmm8
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm9, xmm1, 16
	vpshufd xmm9, xmm9, 78
	vpxor xmm2, xmm10, xmm9
	vpxor xmm2, xmm2, xmm11
	mov r10, rdi
	add r10, 224
	jmp 210f
29:
210:
	mov rax, rsi
	sub r8d, 8
	bswap r8d
	mov DWORD PTR [rax+12], r8d
	vmovdqu xmm0, XMMWORD PTR [r11+768]
	vpshufb xmm2, xmm2, xmm0
	vmovdqu XMMWORD PTR [rcx], xmm2
	vzeroupper
	mov r8, QWORD PTR [r11+808]
	mov rsi, QWORD PTR [r11+800]
	jmp 25f
24:
	vpshufb xmm11, xmm7, xmm0
	movabs rax, 1
	vmovq xmm12, rax
	vpaddd xmm11, xmm11, xmm12
	vpshufb xmm3, xmm11, xmm0
	vpaddd xmm11, xmm11, xmm12
	vpshufb xmm4, xmm11, xmm0
	vpaddd xmm11, xmm11, xmm12
	vpshufb xmm5, xmm11, xmm0
	vpaddd xmm11, xmm11, xmm12
	vpshufb xmm6, xmm11, xmm0
	vpaddd xmm11, xmm11, xmm12
	vpshufb xmm13, xmm11, xmm0
	vpaddd xmm11, xmm11, xmm12
	vpshufb xmm14, xmm11, xmm0
	vpaddd xmm11, xmm11, xmm12
	vpshufb xmm15, xmm11, xmm0
	vpor xmm0, xmm7, xmm7
	vmovdqu xmm1, XMMWORD PTR [rdi]
	vpxor xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm1
	vpxor xmm4, xmm4, xmm1
	vpxor xmm5, xmm5, xmm1
	vpxor xmm6, xmm6, xmm1
	vpxor xmm13, xmm13, xmm1
	vpxor xmm14, xmm14, xmm1
	vpxor xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+16]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	mov eax, r8d
	add eax, 0
	bswap eax
	mov DWORD PTR [r11+652], eax
	mov eax, r8d
	add eax, 1
	bswap eax
	mov DWORD PTR [r11+668], eax
	mov eax, r8d
	add eax, 2
	bswap eax
	mov DWORD PTR [r11+684], eax
	mov eax, r8d
	add eax, 3
	bswap eax
	mov DWORD PTR [r11+700], eax
	vmovdqu xmm1, XMMWORD PTR [rdi+32]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	mov eax, r8d
	add eax, 4
	bswap eax
	mov DWORD PTR [r11+716], eax
	mov eax, r8d
	add eax, 5
	bswap eax
	mov DWORD PTR [r11+732], eax
	mov eax, r8d
	add eax, 6
	bswap eax
	mov DWORD PTR [r11+748], eax
	mov eax, r8d
	add eax, 7
	bswap eax
	mov DWORD PTR [r11+764], eax
	vmovdqu xmm1, XMMWORD PTR [rdi+48]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+64]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+80]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+96]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+112]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+128]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+144]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+160]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+176]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [r10]
	vaesenclast xmm0, xmm0, xmm1
	vaesenclast xmm3, xmm3, xmm1
	vaesenclast xmm4, xmm4, xmm1
	vaesenclast xmm5, xmm5, xmm1
	vaesenclast xmm6, xmm6, xmm1
	vaesenclast xmm13, xmm13, xmm1
	vaesenclast xmm14, xmm14, xmm1
	vaesenclast xmm15, xmm15, xmm1
	vpxor xmm0, xmm0, XMMWORD PTR [rdx+rbx*1]
	vmovdqu XMMWORD PTR [rdx], xmm0
	vpxor xmm3, xmm3, XMMWORD PTR [rdx+rbx*1+16]
	vmovdqu XMMWORD PTR [rdx+16], xmm3
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+rbx*1+32]
	vmovdqu XMMWORD PTR [rdx+32], xmm4
	vpxor xmm5, xmm5, XMMWORD PTR [rdx+rbx*1+48]
	vmovdqu XMMWORD PTR [rdx+48], xmm5
	vpxor xmm6, xmm6, XMMWORD PTR [rdx+rbx*1+64]
	vmovdqu XMMWORD PTR [rdx+64], xmm6
	vpxor xmm13, xmm13, XMMWORD PTR [rdx+rbx*1+80]
	vmovdqu XMMWORD PTR [rdx+80], xmm13
	vpxor xmm14, xmm14, XMMWORD PTR [rdx+rbx*1+96]
	vmovdqu XMMWORD PTR [rdx+96], xmm14
	vpxor xmm15, xmm15, XMMWORD PTR [rdx+rbx*1+112]
	vmovdqu XMMWORD PTR [rdx+112], xmm15
	add r8d, 8
	vmovdqu xmm0, XMMWORD PTR [r11+640]
	vmovdqu xmm3, XMMWORD PTR [r11+656]
	vmovdqu xmm4, XMMWORD PTR [r11+672]
	vmovdqu xmm5, XMMWORD PTR [r11+688]
	vmovdqu xmm6, XMMWORD PTR [r11+704]
	vmovdqu xmm13, XMMWORD PTR [r11+720]
	vmovdqu xmm14, XMMWORD PTR [r11+736]
	vmovdqu xmm15, XMMWORD PTR [r11+752]
	vmovdqu xmm1, XMMWORD PTR [rdi]
	vpxor xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm1
	vpxor xmm4, xmm4, xmm1
	vpxor xmm5, xmm5, xmm1
	vpxor xmm6, xmm6, xmm1
	vpxor xmm13, xmm13, xmm1
	vpxor xmm14, xmm14, xmm1
	vpxor xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+16]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	mov eax, r8d
	add eax, 0
	bswap eax
	mov DWORD PTR [r11+652], eax
	mov eax, r8d
	add eax, 1
	bswap eax
	mov DWORD PTR [r11+668], eax
	mov eax, r8d
	add eax, 2
	bswap eax
	mov DWORD PTR [r11+684], eax
	mov eax, r8d
	add eax, 3
	bswap eax
	mov DWORD PTR [r11+700], eax
	vmovdqu xmm1, XMMWORD PTR [rdi+32]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	mov eax, r8d
	add eax, 4
	bswap eax
	mov DWORD PTR [r11+716], eax
	mov eax, r8d
	add eax, 5
	bswap eax
	mov DWORD PTR [r11+732], eax
	mov eax, r8d
	add eax, 6
	bswap eax
	mov DWORD PTR [r11+748], eax
	mov eax, r8d
	add eax, 7
	bswap eax
	mov DWORD PTR [r11+764], eax
	vmovdqu xmm1, XMMWORD PTR [rdi+48]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+64]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+80]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+96]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+112]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+128]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+144]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+160]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+176]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [r10]
	vaesenclast xmm0, xmm0, xmm1
	vaesenclast xmm3, xmm3, xmm1
	vaesenclast xmm4, xmm4, xmm1
	vaesenclast xmm5, xmm5, xmm1
	vaesenclast xmm6, xmm6, xmm1
	vaesenclast xmm13, xmm13, xmm1
	vaesenclast xmm14, xmm14, xmm1
	vaesenclast xmm15, xmm15, xmm1
	vpxor xmm0, xmm0, XMMWORD PTR [rdx+rbx*1+128]
	vmovdqu XMMWORD PTR [rdx+128], xmm0
	vpxor xmm3, xmm3, XMMWORD PTR [rdx+rbx*1+144]
	vmovdqu XMMWORD PTR [rdx+144], xmm3
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+rbx*1+160]
	vmovdqu XMMWORD PTR [rdx+160], xmm4
	vpxor xmm5, xmm5, XMMWORD PTR [rdx+rbx*1+176]
	vmovdqu XMMWORD PTR [rdx+176], xmm5
	vpxor xmm6, xmm6, XMMWORD PTR [rdx+rbx*1+192]
	vmovdqu XMMWORD PTR [rdx+192], xmm6
	vpxor xmm13, xmm13, XMMWORD PTR [rdx+rbx*1+208]
	vmovdqu XMMWORD PTR [rdx+208], xmm13
	vpxor xmm14, xmm14, XMMWORD PTR [rdx+rbx*1+224]
	vmovdqu XMMWORD PTR [rdx+224], xmm14
	vpxor xmm15, xmm15, XMMWORD PTR [rdx+rbx*1+240]
	vmovdqu XMMWORD PTR [rdx+240], xmm15
	add r8d, 8
	cmp r9, 24
	jb 212f
214:
	vmovdqu xmm0, XMMWORD PTR [r11+640]
	vmovdqu xmm3, XMMWORD PTR [r11+656]
	vmovdqu xmm4, XMMWORD PTR [r11+672]
	vmovdqu xmm5, XMMWORD PTR [r11+688]
	vmovdqu xmm6, XMMWORD PTR [r11+704]
	vmovdqu xmm13, XMMWORD PTR [r11+720]
	vmovdqu xmm14, XMMWORD PTR [r11+736]
	vmovdqu xmm15, XMMWORD PTR [r11+752]
	vmovdqu xmm1, XMMWORD PTR [rdi]
	vpxor xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm1
	vpxor xmm4, xmm4, xmm1
	vpxor xmm5, xmm5, xmm1
	vpxor xmm6, xmm6, xmm1
	vpxor xmm13, xmm13, xmm1
	vpxor xmm14, xmm14, xmm1
	vpxor xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+16]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+144]
	vmovdqu xmm7, XMMWORD PTR [rdx+16]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm8, xmm7, xmm12, 0
	vpclmulqdq xmm10, xmm7, xmm12, 17
	vpclmulqdq xmm9, xmm7, xmm12, 1
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	mov eax, r8d
	add eax, 0
	bswap eax
	mov DWORD PTR [r11+652], eax
	mov eax, r8d
	add eax, 1
	bswap eax
	mov DWORD PTR [r11+668], eax
	mov eax, r8d
	add eax, 2
	bswap eax
	mov DWORD PTR [r11+684], eax
	mov eax, r8d
	add eax, 3
	bswap eax
	mov DWORD PTR [r11+700], eax
	vmovdqu xmm1, XMMWORD PTR [rdi+32]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+160]
	vmovdqu xmm7, XMMWORD PTR [rdx+32]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	mov eax, r8d
	add eax, 4
	bswap eax
	mov DWORD PTR [r11+716], eax
	mov eax, r8d
	add eax, 5
	bswap eax
	mov DWORD PTR [r11+732], eax
	mov eax, r8d
	add eax, 6
	bswap eax
	mov DWORD PTR [r11+748], eax
	mov eax, r8d
	add eax, 7
	bswap eax
	mov DWORD PTR [r11+764], eax
	vmovdqu xmm1, XMMWORD PTR [rdi+48]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+176]
	vmovdqu xmm7, XMMWORD PTR [rdx+48]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+64]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+80]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+192]
	vmovdqu xmm7, XMMWORD PTR [rdx+64]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+96]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+208]
	vmovdqu xmm7, XMMWORD PTR [rdx+80]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+112]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+224]
	vmovdqu xmm7, XMMWORD PTR [rdx+96]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+128]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+144]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+240]
	vmovdqu xmm7, XMMWORD PTR [rdx+112]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+160]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+128]
	vmovdqu xmm7, XMMWORD PTR [rdx]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpxor xmm7, xmm7, xmm2
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+176]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [r11+784]
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm9, xmm9, xmm8
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm9, xmm1, 16
	vpshufd xmm9, xmm9, 78
	vpxor xmm2, xmm10, xmm9
	vpxor xmm2, xmm2, xmm11
	vmovdqu xmm1, XMMWORD PTR [r10]
	vaesenclast xmm0, xmm0, xmm1
	vaesenclast xmm3, xmm3, xmm1
	vaesenclast xmm4, xmm4, xmm1
	vaesenclast xmm5, xmm5, xmm1
	vaesenclast xmm6, xmm6, xmm1
	vaesenclast xmm13, xmm13, xmm1
	vaesenclast xmm14, xmm14, xmm1
	vaesenclast xmm15, xmm15, xmm1
	vpxor xmm0, xmm0, XMMWORD PTR [rdx+rbx*1+256]
	vmovdqu XMMWORD PTR [rdx+256], xmm0
	vpxor xmm3, xmm3, XMMWORD PTR [rdx+rbx*1+272]
	vmovdqu XMMWORD PTR [rdx+272], xmm3
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+rbx*1+288]
	vmovdqu XMMWORD PTR [rdx+288], xmm4
	vpxor xmm5, xmm5, XMMWORD PTR [rdx+rbx*1+304]
	vmovdqu XMMWORD PTR [rdx+304], xmm5
	vpxor xmm6, xmm6, XMMWORD PTR [rdx+rbx*1+320]
	vmovdqu XMMWORD PTR [rdx+320], xmm6
	vpxor xmm13, xmm13, XMMWORD PTR [rdx+rbx*1+336]
	vmovdqu XMMWORD PTR [rdx+336], xmm13
	vpxor xmm14, xmm14, XMMWORD PTR [rdx+rbx*1+352]
	vmovdqu XMMWORD PTR [rdx+352], xmm14
	vpxor xmm15, xmm15, XMMWORD PTR [rdx+rbx*1+368]
	vmovdqu XMMWORD PTR [rdx+368], xmm15
	add r8d, 8
	add rdx, 128
	sub r9, 8
	cmp r9, 24
	jae 214b
	jmp 213f
212:
213:
	vmovdqu xmm12, XMMWORD PTR [r11+144]
	vmovdqu xmm7, XMMWORD PTR [rdx+16]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm8, xmm7, xmm12, 0
	vpclmulqdq xmm10, xmm7, xmm12, 17
	vpclmulqdq xmm9, xmm7, xmm12, 1
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+160]
	vmovdqu xmm7, XMMWORD PTR [rdx+32]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+176]
	vmovdqu xmm7, XMMWORD PTR [rdx+48]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+192]
	vmovdqu xmm7, XMMWORD PTR [rdx+64]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+208]
	vmovdqu xmm7, XMMWORD PTR [rdx+80]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+224]
	vmovdqu xmm7, XMMWORD PTR [rdx+96]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+240]
	vmovdqu xmm7, XMMWORD PTR [rdx+112]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+128]
	vmovdqu xmm7, XMMWORD PTR [rdx]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpxor xmm7, xmm7, xmm2
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [r11+784]
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm9, xmm9, xmm8
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm9, xmm1, 16
	vpshufd xmm9, xmm9, 78
	vpxor xmm2, xmm10, xmm9
	vpxor xmm2, xmm2, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+144]
	vmovdqu xmm7, XMMWORD PTR [rdx+144]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm8, xmm7, xmm12, 0
	vpclmulqdq xmm10, xmm7, xmm12, 17
	vpclmulqdq xmm9, xmm7, xmm12, 1
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+160]
	vmovdqu xmm7, XMMWORD PTR [rdx+160]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+176]
	vmovdqu xmm7, XMMWORD PTR [rdx+176]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+192]
	vmovdqu xmm7, XMMWORD PTR [rdx+192]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+208]
	vmovdqu xmm7, XMMWORD PTR [rdx+208]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+224]
	vmovdqu xmm7, XMMWORD PTR [rdx+224]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+240]
	vmovdqu xmm7, XMMWORD PTR [rdx+240]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+128]
	vmovdqu xmm7, XMMWORD PTR [rdx+128]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpxor xmm7, xmm7, xmm2
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [r11+784]
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm9, xmm9, xmm8
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm9, xmm1, 16
	vpshufd xmm9, xmm9, 78
	vpxor xmm2, xmm10, xmm9
	vpxor xmm2, xmm2, xmm11
	cmp r9, 16
	je 215f
	vmovdqu xmm0, XMMWORD PTR [r11+640]
	vmovdqu xmm3, XMMWORD PTR [r11+656]
	vmovdqu xmm4, XMMWORD PTR [r11+672]
	vmovdqu xmm5, XMMWORD PTR [r11+688]
	vmovdqu xmm6, XMMWORD PTR [r11+704]
	vmovdqu xmm13, XMMWORD PTR [r11+720]
	vmovdqu xmm14, XMMWORD PTR [r11+736]
	vmovdqu xmm15, XMMWORD PTR [r11+752]
	vmovdqu xmm1, XMMWORD PTR [rdi]
	vpxor xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm1
	vpxor xmm4, xmm4, xmm1
	vpxor xmm5, xmm5, xmm1
	vpxor xmm6, xmm6, xmm1
	vpxor xmm13, xmm13, xmm1
	vpxor xmm14, xmm14, xmm1
	vpxor xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+16]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+32]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+48]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+64]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+80]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+96]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+112]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+128]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+144]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+160]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+176]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [r10]
	vaesenclast xmm0, xmm0, xmm1
	vaesenclast xmm3, xmm3, xmm1
	vaesenclast xmm4, xmm4, xmm1
	vaesenclast xmm5, xmm5, xmm1
	vaesenclast xmm6, xmm6, xmm1
	vaesenclast xmm13, xmm13, xmm1
	vaesenclast xmm14, xmm14, xmm1
	vaesenclast xmm15, xmm15, xmm1
	vmovdqu XMMWORD PTR [r11+832], xmm0
	vmovdqu XMMWORD PTR [r11+848], xmm3
	vmovdqu XMMWORD PTR [r11+864], xmm4
	vmovdqu XMMWORD PTR [r11+880], xmm5
	vmovdqu XMMWORD PTR [r11+896], xmm6
	vmovdqu XMMWORD PTR [r11+912], xmm13
	vmovdqu XMMWORD PTR [r11+928], xmm14
	vmovdqu XMMWORD PTR [r11+944], xmm15
	mov r10, r9
	sub r10, 16
	add r8d, r10d
	shl r10, 4
	mov rax, r11
	add rax, 256
	sub rax, r10
	add rdx, 256
	mov r10d, 0
	vmovdqu xmm0, XMMWORD PTR [r11+768]
	vmovdqu xmm1, XMMWORD PTR [r11+784]
	add r11, 64
	add rbx, rdx
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
217:
	vmovdqu xmm13, XMMWORD PTR [rbx+r10*1]
	vmovdqu xmm12, XMMWORD PTR [r11+r10*1+768]
	vpxor xmm13, xmm13, xmm12
	vmovdqu XMMWORD PTR [rdx+r10*1], xmm13
	vpshufb xmm13, xmm13, xmm0
	vpxor xmm13, xmm13, xmm2
	vpxor xmm2, xmm2, xmm2
	vmovdqu xmm12, XMMWORD PTR [rax+r10*1]
	vpclmulqdq xmm11, xmm13, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm13, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm13, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm13, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	add r10, 16
	sub r9, 1
	cmp r9, 16
	jne 217b
	sub rbx, rdx
	sub r11, 64
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm9, xmm9, xmm8
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm9, xmm1, 16
	vpshufd xmm9, xmm9, 78
	vpxor xmm2, xmm10, xmm9
	vpxor xmm2, xmm2, xmm11
	mov r10, rdi
	add r10, 192
	jmp 216f
215:
216:
	mov rax, rsi
	sub r8d, 8
	bswap r8d
	mov DWORD PTR [rax+12], r8d
	vmovdqu xmm0, XMMWORD PTR [r11+768]
	vpshufb xmm2, xmm2, xmm0
	vmovdqu XMMWORD PTR [rcx], xmm2
	vzeroupper
	mov r8, QWORD PTR [r11+808]
	mov rsi, QWORD PTR [r11+800]
25:
	jmp 23f
22:
	vpshufb xmm11, xmm7, xmm0
	movabs rax, 1
	vmovq xmm12, rax
	vpaddd xmm11, xmm11, xmm12
	vpshufb xmm3, xmm11, xmm0
	vpaddd xmm11, xmm11, xmm12
	vpshufb xmm4, xmm11, xmm0
	vpaddd xmm11, xmm11, xmm12
	vpshufb xmm5, xmm11, xmm0
	vpaddd xmm11, xmm11, xmm12
	vpshufb xmm6, xmm11, xmm0
	vpaddd xmm11, xmm11, xmm12
	vpshufb xmm13, xmm11, xmm0
	vpaddd xmm11, xmm11, xmm12
	vpshufb xmm14, xmm11, xmm0
	vpaddd xmm11, xmm11, xmm12
	vpshufb xmm15, xmm11, xmm0
	vpor xmm0, xmm7, xmm7
	vmovdqu xmm1, XMMWORD PTR [rdi]
	vpxor xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm1
	vpxor xmm4, xmm4, xmm1
	vpxor xmm5, xmm5, xmm1
	vpxor xmm6, xmm6, xmm1
	vpxor xmm13, xmm13, xmm1
	vpxor xmm14, xmm14, xmm1
	vpxor xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+16]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	mov eax, r8d
	add eax, 0
	bswap eax
	mov DWORD PTR [r11+652], eax
	mov eax, r8d
	add eax, 1
	bswap eax
	mov DWORD PTR [r11+668], eax
	mov eax, r8d
	add eax, 2
	bswap eax
	mov DWORD PTR [r11+684], eax
	mov eax, r8d
	add eax, 3
	bswap eax
	mov DWORD PTR [r11+700], eax
	vmovdqu xmm1, XMMWORD PTR [rdi+32]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	mov eax, r8d
	add eax, 4
	bswap eax
	mov DWORD PTR [r11+716], eax
	mov eax, r8d
	add eax, 5
	bswap eax
	mov DWORD PTR [r11+732], eax
	mov eax, r8d
	add eax, 6
	bswap eax
	mov DWORD PTR [r11+748], eax
	mov eax, r8d
	add eax, 7
	bswap eax
	mov DWORD PTR [r11+764], eax
	vmovdqu xmm1, XMMWORD PTR [rdi+48]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+64]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+80]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+96]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+112]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+128]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+144]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [r10]
	vaesenclast xmm0, xmm0, xmm1
	vaesenclast xmm3, xmm3, xmm1
	vaesenclast xmm4, xmm4, xmm1
	vaesenclast xmm5, xmm5, xmm1
	vaesenclast xmm6, xmm6, xmm1
	vaesenclast xmm13, xmm13, xmm1
	vaesenclast xmm14, xmm14, xmm1
	vaesenclast xmm15, xmm15, xmm1
	vpxor xmm0, xmm0, XMMWORD PTR [rdx+rbx*1]
	vmovdqu XMMWORD PTR [rdx], xmm0
	vpxor xmm3, xmm3, XMMWORD PTR [rdx+rbx*1+16]
	vmovdqu XMMWORD PTR [rdx+16], xmm3
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+rbx*1+32]
	vmovdqu XMMWORD PTR [rdx+32], xmm4
	vpxor xmm5, xmm5, XMMWORD PTR [rdx+rbx*1+48]
	vmovdqu XMMWORD PTR [rdx+48], xmm5
	vpxor xmm6, xmm6, XMMWORD PTR [rdx+rbx*1+64]
	vmovdqu XMMWORD PTR [rdx+64], xmm6
	vpxor xmm13, xmm13, XMMWORD PTR [rdx+rbx*1+80]
	vmovdqu XMMWORD PTR [rdx+80], xmm13
	vpxor xmm14, xmm14, XMMWORD PTR [rdx+rbx*1+96]
	vmovdqu XMMWORD PTR [rdx+96], xmm14
	vpxor xmm15, xmm15, XMMWORD PTR [rdx+rbx*1+112]
	vmovdqu XMMWORD PTR [rdx+112], xmm15
	add r8d, 8
	vmovdqu xmm0, XMMWORD PTR [r11+640]
	vmovdqu xmm3, XMMWORD PTR [r11+656]
	vmovdqu xmm4, XMMWORD PTR [r11+672]
	vmovdqu xmm5, XMMWORD PTR [r11+688]
	vmovdqu xmm6, XMMWORD PTR [r11+704]
	vmovdqu xmm13, XMMWORD PTR [r11+720]
	vmovdqu xmm14, XMMWORD PTR [r11+736]
	vmovdqu xmm15, XMMWORD PTR [r11+752]
	vmovdqu xmm1, XMMWORD PTR [rdi]
	vpxor xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm1
	vpxor xmm4, xmm4, xmm1
	vpxor xmm5, xmm5, xmm1
	vpxor xmm6, xmm6, xmm1
	vpxor xmm13, xmm13, xmm1
	vpxor xmm14, xmm14, xmm1
	vpxor xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+16]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	mov eax, r8d
	add eax, 0
	bswap eax
	mov DWORD PTR [r11+652], eax
	mov eax, r8d
	add eax, 1
	bswap eax
	mov DWORD PTR [r11+668], eax
	mov eax, r8d
	add eax, 2
	bswap eax
	mov DWORD PTR [r11+684], eax
	mov eax, r8d
	add eax, 3
	bswap eax
	mov DWORD PTR [r11+700], eax
	vmovdqu xmm1, XMMWORD PTR [rdi+32]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	mov eax, r8d
	add eax, 4
	bswap eax
	mov DWORD PTR [r11+716], eax
	mov eax, r8d
	add eax, 5
	bswap eax
	mov DWORD PTR [r11+732], eax
	mov eax, r8d
	add eax, 6
	bswap eax
	mov DWORD PTR [r11+748], eax
	mov eax, r8d
	add eax, 7
	bswap eax
	mov DWORD PTR [r11+764], eax
	vmovdqu xmm1, XMMWORD PTR [rdi+48]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+64]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+80]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+96]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+112]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+128]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+144]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [r10]
	vaesenclast xmm0, xmm0, xmm1
	vaesenclast xmm3, xmm3, xmm1
	vaesenclast xmm4, xmm4, xmm1
	vaesenclast xmm5, xmm5, xmm1
	vaesenclast xmm6, xmm6, xmm1
	vaesenclast xmm13, xmm13, xmm1
	vaesenclast xmm14, xmm14, xmm1
	vaesenclast xmm15, xmm15, xmm1
	vpxor xmm0, xmm0, XMMWORD PTR [rdx+rbx*1+128]
	vmovdqu XMMWORD PTR [rdx+128], xmm0
	vpxor xmm3, xmm3, XMMWORD PTR [rdx+rbx*1+144]
	vmovdqu XMMWORD PTR [rdx+144], xmm3
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+rbx*1+160]
	vmovdqu XMMWORD PTR [rdx+160], xmm4
	vpxor xmm5, xmm5, XMMWORD PTR [rdx+rbx*1+176]
	vmovdqu XMMWORD PTR [rdx+176], xmm5
	vpxor xmm6, xmm6, XMMWORD PTR [rdx+rbx*1+192]
	vmovdqu XMMWORD PTR [rdx+192], xmm6
	vpxor xmm13, xmm13, XMMWORD PTR [rdx+rbx*1+208]
	vmovdqu XMMWORD PTR [rdx+208], xmm13
	vpxor xmm14, xmm14, XMMWORD PTR [rdx+rbx*1+224]
	vmovdqu XMMWORD PTR [rdx+224], xmm14
	vpxor xmm15, xmm15, XMMWORD PTR [rdx+rbx*1+240]
	vmovdqu XMMWORD PTR [rdx+240], xmm15
	add r8d, 8
	cmp r9, 24
	jb 218f
220:
	vmovdqu xmm0, XMMWORD PTR [r11+640]
	vmovdqu xmm3, XMMWORD PTR [r11+656]
	vmovdqu xmm4, XMMWORD PTR [r11+672]
	vmovdqu xmm5, XMMWORD PTR [r11+688]
	vmovdqu xmm6, XMMWORD PTR [r11+704]
	vmovdqu xmm13, XMMWORD PTR [r11+720]
	vmovdqu xmm14, XMMWORD PTR [r11+736]
	vmovdqu xmm15, XMMWORD PTR [r11+752]
	vmovdqu xmm1, XMMWORD PTR [rdi]
	vpxor xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm1
	vpxor xmm4, xmm4, xmm1
	vpxor xmm5, xmm5, xmm1
	vpxor xmm6, xmm6, xmm1
	vpxor xmm13, xmm13, xmm1
	vpxor xmm14, xmm14, xmm1
	vpxor xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+16]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+144]
	vmovdqu xmm7, XMMWORD PTR [rdx+16]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm8, xmm7, xmm12, 0
	vpclmulqdq xmm10, xmm7, xmm12, 17
	vpclmulqdq xmm9, xmm7, xmm12, 1
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	mov eax, r8d
	add eax, 0
	bswap eax
	mov DWORD PTR [r11+652], eax
	mov eax, r8d
	add eax, 1
	bswap eax
	mov DWORD PTR [r11+668], eax
	mov eax, r8d
	add eax, 2
	bswap eax
	mov DWORD PTR [r11+684], eax
	mov eax, r8d
	add eax, 3
	bswap eax
	mov DWORD PTR [r11+700], eax
	vmovdqu xmm1, XMMWORD PTR [rdi+32]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+160]
	vmovdqu xmm7, XMMWORD PTR [rdx+32]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	mov eax, r8d
	add eax, 4
	bswap eax
	mov DWORD PTR [r11+716], eax
	mov eax, r8d
	add eax, 5
	bswap eax
	mov DWORD PTR [r11+732], eax
	mov eax, r8d
	add eax, 6
	bswap eax
	mov DWORD PTR [r11+748], eax
	mov eax, r8d
	add eax, 7
	bswap eax
	mov DWORD PTR [r11+764], eax
	vmovdqu xmm1, XMMWORD PTR [rdi+48]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+176]
	vmovdqu xmm7, XMMWORD PTR [rdx+48]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+64]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+192]
	vmovdqu xmm7, XMMWORD PTR [rdx+64]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+80]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+208]
	vmovdqu xmm7, XMMWORD PTR [rdx+80]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+96]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+224]
	vmovdqu xmm7, XMMWORD PTR [rdx+96]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+112]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+240]
	vmovdqu xmm7, XMMWORD PTR [rdx+112]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+128]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+128]
	vmovdqu xmm7, XMMWORD PTR [rdx]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpxor xmm7, xmm7, xmm2
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+144]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [r11+784]
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm9, xmm9, xmm8
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm9, xmm1, 16
	vpshufd xmm9, xmm9, 78
	vpxor xmm2, xmm10, xmm9
	vpxor xmm2, xmm2, xmm11
	vmovdqu xmm1, XMMWORD PTR [r10]
	vaesenclast xmm0, xmm0, xmm1
	vaesenclast xmm3, xmm3, xmm1
	vaesenclast xmm4, xmm4, xmm1
	vaesenclast xmm5, xmm5, xmm1
	vaesenclast xmm6, xmm6, xmm1
	vaesenclast xmm13, xmm13, xmm1
	vaesenclast xmm14, xmm14, xmm1
	vaesenclast xmm15, xmm15, xmm1
	vpxor xmm0, xmm0, XMMWORD PTR [rdx+rbx*1+256]
	vmovdqu XMMWORD PTR [rdx+256], xmm0
	vpxor xmm3, xmm3, XMMWORD PTR [rdx+rbx*1+272]
	vmovdqu XMMWORD PTR [rdx+272], xmm3
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+rbx*1+288]
	vmovdqu XMMWORD PTR [rdx+288], xmm4
	vpxor xmm5, xmm5, XMMWORD PTR [rdx+rbx*1+304]
	vmovdqu XMMWORD PTR [rdx+304], xmm5
	vpxor xmm6, xmm6, XMMWORD PTR [rdx+rbx*1+320]
	vmovdqu XMMWORD PTR [rdx+320], xmm6
	vpxor xmm13, xmm13, XMMWORD PTR [rdx+rbx*1+336]
	vmovdqu XMMWORD PTR [rdx+336], xmm13
	vpxor xmm14, xmm14, XMMWORD PTR [rdx+rbx*1+352]
	vmovdqu XMMWORD PTR [rdx+352], xmm14
	vpxor xmm15, xmm15, XMMWORD PTR [rdx+rbx*1+368]
	vmovdqu XMMWORD PTR [rdx+368], xmm15
	add r8d, 8
	add rdx, 128
	sub r9, 8
	cmp r9, 24
	jae 220b
	jmp 219f
218:
219:
	vmovdqu xmm12, XMMWORD PTR [r11+144]
	vmovdqu xmm7, XMMWORD PTR [rdx+16]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm8, xmm7, xmm12, 0
	vpclmulqdq xmm10, xmm7, xmm12, 17
	vpclmulqdq xmm9, xmm7, xmm12, 1
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+160]
	vmovdqu xmm7, XMMWORD PTR [rdx+32]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+176]
	vmovdqu xmm7, XMMWORD PTR [rdx+48]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+192]
	vmovdqu xmm7, XMMWORD PTR [rdx+64]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+208]
	vmovdqu xmm7, XMMWORD PTR [rdx+80]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+224]
	vmovdqu xmm7, XMMWORD PTR [rdx+96]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+240]
	vmovdqu xmm7, XMMWORD PTR [rdx+112]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+128]
	vmovdqu xmm7, XMMWORD PTR [rdx]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpxor xmm7, xmm7, xmm2
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [r11+784]
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm9, xmm9, xmm8
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm9, xmm1, 16
	vpshufd xmm9, xmm9, 78
	vpxor xmm2, xmm10, xmm9
	vpxor xmm2, xmm2, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+144]
	vmovdqu xmm7, XMMWORD PTR [rdx+144]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm8, xmm7, xmm12, 0
	vpclmulqdq xmm10, xmm7, xmm12, 17
	vpclmulqdq xmm9, xmm7, xmm12, 1
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+160]
	vmovdqu xmm7, XMMWORD PTR [rdx+160]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+176]
	vmovdqu xmm7, XMMWORD PTR [rdx+176]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+192]
	vmovdqu xmm7, XMMWORD PTR [rdx+192]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+208]
	vmovdqu xmm7, XMMWORD PTR [rdx+208]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+224]
	vmovdqu xmm7, XMMWORD PTR [rdx+224]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+240]
	vmovdqu xmm7, XMMWORD PTR [rdx+240]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm12, XMMWORD PTR [r11+128]
	vmovdqu xmm7, XMMWORD PTR [rdx+128]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpxor xmm7, xmm7, xmm2
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [r11+784]
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm9, xmm9, xmm8
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm9, xmm1, 16
	vpshufd xmm9, xmm9, 78
	vpxor xmm2, xmm10, xmm9
	vpxor xmm2, xmm2, xmm11
	cmp r9, 16
	je 221f
	vmovdqu xmm0, XMMWORD PTR [r11+640]
	vmovdqu xmm3, XMMWORD PTR [r11+656]
	vmovdqu xmm4, XMMWORD PTR [r11+672]
	vmovdqu xmm5, XMMWORD PTR [r11+688]
	vmovdqu xmm6, XMMWORD PTR [r11+704]
	vmovdqu xmm13, XMMWORD PTR [r11+720]
	vmovdqu xmm14, XMMWORD PTR [r11+736]
	vmovdqu xmm15, XMMWORD PTR [r11+752]
	vmovdqu xmm1, XMMWORD PTR [rdi]
	vpxor xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm1
	vpxor xmm4, xmm4, xmm1
	vpxor xmm5, xmm5, xmm1
	vpxor xmm6, xmm6, xmm1
	vpxor xmm13, xmm13, xmm1
	vpxor xmm14, xmm14, xmm1
	vpxor xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+16]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+32]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+48]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+64]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+80]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+96]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+112]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+128]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+144]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [r10]
	vaesenclast xmm0, xmm0, xmm1
	vaesenclast xmm3, xmm3, xmm1
	vaesenclast xmm4, xmm4, xmm1
	vaesenclast xmm5, xmm5, xmm1
	vaesenclast xmm6, xmm6, xmm1
	vaesenclast xmm13, xmm13, xmm1
	vaesenclast xmm14, xmm14, xmm1
	vaesenclast xmm15, xmm15, xmm1
	vmovdqu XMMWORD PTR [r11+832], xmm0
	vmovdqu XMMWORD PTR [r11+848], xmm3
	vmovdqu XMMWORD PTR [r11+864], xmm4
	vmovdqu XMMWORD PTR [r11+880], xmm5
	vmovdqu XMMWORD PTR [r11+896], xmm6
	vmovdqu XMMWORD PTR [r11+912], xmm13
	vmovdqu XMMWORD PTR [r11+928], xmm14
	vmovdqu XMMWORD PTR [r11+944], xmm15
	mov r10, r9
	sub r10, 16
	add r8d, r10d
	shl r10, 4
	mov rax, r11
	add rax, 256
	sub rax, r10
	add rdx, 256
	mov r10d, 0
	vmovdqu xmm0, XMMWORD PTR [r11+768]
	vmovdqu xmm1, XMMWORD PTR [r11+784]
	add r11, 64
	add rbx, rdx
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
223:
	vmovdqu xmm13, XMMWORD PTR [rbx+r10*1]
	vmovdqu xmm12, XMMWORD PTR [r11+r10*1+768]
	vpxor xmm13, xmm13, xmm12
	vmovdqu XMMWORD PTR [rdx+r10*1], xmm13
	vpshufb xmm13, xmm13, xmm0
	vpxor xmm13, xmm13, xmm2
	vpxor xmm2, xmm2, xmm2
	vmovdqu xmm12, XMMWORD PTR [rax+r10*1]
	vpclmulqdq xmm11, xmm13, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm13, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm13, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm13, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	add r10, 16
	sub r9, 1
	cmp r9, 16
	jne 223b
	sub rbx, rdx
	sub r11, 64
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm9, xmm9, xmm8
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm9, xmm1, 16
	vpshufd xmm9, xmm9, 78
	vpxor xmm2, xmm10, xmm9
	vpxor xmm2, xmm2, xmm11
	mov r10, rdi
	add r10, 160
	jmp 222f
221:
222:
	mov rax, rsi
	sub r8d, 8
	bswap r8d
	mov DWORD PTR [rax+12], r8d
	vmovdqu xmm0, XMMWORD PTR [r11+768]
	vpshufb xmm2, xmm2, xmm0
	vmovdqu XMMWORD PTR [rcx], xmm2
	vzeroupper
	mov r8, QWORD PTR [r11+808]
	mov rsi, QWORD PTR [r11+800]
23:
	mov rbx, QWORD PTR [r11+816]
	jmp 21f
20:
21:
	mov r11, QWORD PTR [rsp+24]
	mov r8, QWORD PTR [r11+40]
	mov rax, r8
	and r8, 15
	sub rax, r8
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	mov rcx, rax
	add rax, QWORD PTR [r11+32]
	mov QWORD PTR [r11+32], rax
	add rcx, QWORD PTR [r11+48]
	mov QWORD PTR [r11+48], rcx
	mov QWORD PTR [r11+40], r8
	mov r11, QWORD PTR [rsp+24]
	mov rcx, QWORD PTR [r11+40]
	test rcx, rcx
	je 224f
	mov rsi, QWORD PTR [r11+32]
	mov rdi, QWORD PTR [r11+48]
	mov r10d, 0
226:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	sub rcx, 1
	jne 226b
	mov r11, QWORD PTR [rsp+24]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, QWORD PTR [r11+16]
	mov rcx, QWORD PTR [r11+24]
	mov r8, QWORD PTR [r11+48]
	mov r9, QWORD PTR [r11+40]
	mov rax, r11
	push rax
	call {vg_aes_gcm_encrypt_blocks_prepared16_aesni_pclmul_avx}
	pop rax
	jmp 225f
224:
225:
	ret
	.p2align 6
