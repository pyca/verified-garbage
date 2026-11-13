// The functions of `src/internal/vg_aes_gcm_encrypt_blocks_to_prepared_vaes_vpclmul_avx512.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_gcm_encrypt_blocks_to_prepared_vaes_vpclmul_avx512:
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
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	vinserti128 ymm0, ymm0, xmm0, 1
	vinserti128 ymm1, ymm1, xmm1, 1
	vmovdqu ymm3, YMMWORD PTR [rdi+480]
	vmovdqu ymm4, YMMWORD PTR [rdi+448]
	vmovdqu ymm5, YMMWORD PTR [rdi+416]
	vmovdqu ymm6, YMMWORD PTR [rdi+384]
	vmovdqu ymm15, YMMWORD PTR [rdi+352]
	vmovdqu ymm14, YMMWORD PTR [rdi+320]
	vmovdqu ymm13, YMMWORD PTR [rdi+288]
	vmovdqu ymm12, YMMWORD PTR [rdi+256]
	vmovdqu YMMWORD PTR [r11], ymm3
	vmovdqu YMMWORD PTR [r11+32], ymm4
	vmovdqu YMMWORD PTR [r11+64], ymm5
	vmovdqu YMMWORD PTR [r11+96], ymm6
	vmovdqu YMMWORD PTR [r11+128], ymm15
	vmovdqu YMMWORD PTR [r11+160], ymm14
	vmovdqu YMMWORD PTR [r11+192], ymm13
	vmovdqu YMMWORD PTR [r11+224], ymm12
	vmovdqu xmm2, XMMWORD PTR [rcx]
	vpshufb xmm2, xmm2, xmm0
	movabs rax, 1
	vmovq xmm15, rax
	vmovdqu xmm14, XMMWORD PTR [rdx]
	vpshufb xmm14, xmm14, xmm0
	vpaddd xmm13, xmm14, xmm15
	vinserti128 ymm14, ymm14, xmm13, 1
	movabs rax, 2
	vmovq xmm15, rax
	vinserti128 ymm15, ymm15, xmm15, 1
	sub r8, r10
	mov rax, rdx
	mov rdx, r10
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	vpaddd ymm13, ymm14, ymm15
	vshufi32x4 zmm14, zmm14, zmm13, 68
	vpaddd ymm15, ymm15, ymm15
	vshufi32x4 zmm15, zmm15, zmm15, 68
	vshufi32x4 zmm0, zmm0, zmm0, 68
	vshufi32x4 zmm1, zmm1, zmm1, 68
	vmovdqa xmm2, xmm2
	vbroadcasti32x4 zmm16, XMMWORD PTR [rdi]
	vbroadcasti32x4 zmm17, XMMWORD PTR [rdi+16]
	vbroadcasti32x4 zmm18, XMMWORD PTR [rdi+32]
	vbroadcasti32x4 zmm19, XMMWORD PTR [rdi+48]
	vbroadcasti32x4 zmm20, XMMWORD PTR [rdi+64]
	vbroadcasti32x4 zmm21, XMMWORD PTR [rdi+80]
	vbroadcasti32x4 zmm22, XMMWORD PTR [rdi+96]
	vbroadcasti32x4 zmm23, XMMWORD PTR [rdi+112]
	vbroadcasti32x4 zmm24, XMMWORD PTR [rdi+128]
	vbroadcasti32x4 zmm25, XMMWORD PTR [rdi+144]
	cmp rsi, 10
	je 22f
	vbroadcasti32x4 zmm26, XMMWORD PTR [rdi+160]
	vbroadcasti32x4 zmm27, XMMWORD PTR [rdi+176]
	cmp rsi, 12
	je 24f
	vbroadcasti32x4 zmm28, XMMWORD PTR [rdi+192]
	vbroadcasti32x4 zmm29, XMMWORD PTR [rdi+208]
	jmp 25f
24:
25:
	jmp 23f
22:
23:
	vbroadcasti32x4 zmm31, XMMWORD PTR [r10]
	vpshufb zmm3, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm4, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm5, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm6, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpxord zmm3, zmm3, zmm16
	vpxord zmm4, zmm4, zmm16
	vpxord zmm5, zmm5, zmm16
	vpxord zmm6, zmm6, zmm16
	vaesenc zmm3, zmm3, zmm17
	vaesenc zmm4, zmm4, zmm17
	vaesenc zmm5, zmm5, zmm17
	vaesenc zmm6, zmm6, zmm17
	vaesenc zmm3, zmm3, zmm18
	vaesenc zmm4, zmm4, zmm18
	vaesenc zmm5, zmm5, zmm18
	vaesenc zmm6, zmm6, zmm18
	vaesenc zmm3, zmm3, zmm19
	vaesenc zmm4, zmm4, zmm19
	vaesenc zmm5, zmm5, zmm19
	vaesenc zmm6, zmm6, zmm19
	vaesenc zmm3, zmm3, zmm20
	vaesenc zmm4, zmm4, zmm20
	vaesenc zmm5, zmm5, zmm20
	vaesenc zmm6, zmm6, zmm20
	vaesenc zmm3, zmm3, zmm21
	vaesenc zmm4, zmm4, zmm21
	vaesenc zmm5, zmm5, zmm21
	vaesenc zmm6, zmm6, zmm21
	vaesenc zmm3, zmm3, zmm22
	vaesenc zmm4, zmm4, zmm22
	vaesenc zmm5, zmm5, zmm22
	vaesenc zmm6, zmm6, zmm22
	vaesenc zmm3, zmm3, zmm23
	vaesenc zmm4, zmm4, zmm23
	vaesenc zmm5, zmm5, zmm23
	vaesenc zmm6, zmm6, zmm23
	vaesenc zmm3, zmm3, zmm24
	vaesenc zmm4, zmm4, zmm24
	vaesenc zmm5, zmm5, zmm24
	vaesenc zmm6, zmm6, zmm24
	vaesenc zmm3, zmm3, zmm25
	vaesenc zmm4, zmm4, zmm25
	vaesenc zmm5, zmm5, zmm25
	vaesenc zmm6, zmm6, zmm25
	cmp rsi, 10
	je 26f
	vaesenc zmm3, zmm3, zmm26
	vaesenc zmm4, zmm4, zmm26
	vaesenc zmm5, zmm5, zmm26
	vaesenc zmm6, zmm6, zmm26
	vaesenc zmm3, zmm3, zmm27
	vaesenc zmm4, zmm4, zmm27
	vaesenc zmm5, zmm5, zmm27
	vaesenc zmm6, zmm6, zmm27
	cmp rsi, 12
	je 28f
	vaesenc zmm3, zmm3, zmm28
	vaesenc zmm4, zmm4, zmm28
	vaesenc zmm5, zmm5, zmm28
	vaesenc zmm6, zmm6, zmm28
	vaesenc zmm3, zmm3, zmm29
	vaesenc zmm4, zmm4, zmm29
	vaesenc zmm5, zmm5, zmm29
	vaesenc zmm6, zmm6, zmm29
	jmp 29f
28:
29:
	jmp 27f
26:
27:
	vaesenclast zmm3, zmm3, zmm31
	vaesenclast zmm4, zmm4, zmm31
	vaesenclast zmm5, zmm5, zmm31
	vaesenclast zmm6, zmm6, zmm31
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1]
	vpxord zmm3, zmm3, zmm13
	vmovdqu32 ZMMWORD PTR [rdx], zmm3
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+64]
	vpxord zmm4, zmm4, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+64], zmm4
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+128]
	vpxord zmm5, zmm5, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+128], zmm5
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+192]
	vpxord zmm6, zmm6, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+192], zmm6
	cmp r9, 48
	jb 210f
	vmovdqu ymm12, YMMWORD PTR [rdi+736]
	vmovdqu YMMWORD PTR [r11+256], ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+704]
	vmovdqu YMMWORD PTR [r11+288], ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+672]
	vmovdqu YMMWORD PTR [r11+320], ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+640]
	vmovdqu YMMWORD PTR [r11+352], ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+608]
	vmovdqu YMMWORD PTR [r11+384], ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+576]
	vmovdqu YMMWORD PTR [r11+416], ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+544]
	vmovdqu YMMWORD PTR [r11+448], ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+512]
	vmovdqu YMMWORD PTR [r11+480], ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+992]
	vmovdqu YMMWORD PTR [r11+512], ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+960]
	vmovdqu YMMWORD PTR [r11+544], ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+928]
	vmovdqu YMMWORD PTR [r11+576], ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+896]
	vmovdqu YMMWORD PTR [r11+608], ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+864]
	vmovdqu YMMWORD PTR [r11+640], ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+832]
	vmovdqu YMMWORD PTR [r11+672], ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+800]
	vmovdqu YMMWORD PTR [r11+704], ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+768]
	vmovdqu YMMWORD PTR [r11+736], ymm12
	vmovdqu32 ZMMWORD PTR [r11+832], zmm1
	cmp r9, 144
	jb 212f
	vpshufb zmm3, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm4, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm5, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm6, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpxord zmm3, zmm3, zmm16
	vpxord zmm4, zmm4, zmm16
	vpxord zmm5, zmm5, zmm16
	vpxord zmm6, zmm6, zmm16
	vaesenc zmm3, zmm3, zmm17
	vaesenc zmm4, zmm4, zmm17
	vaesenc zmm5, zmm5, zmm17
	vaesenc zmm6, zmm6, zmm17
	vaesenc zmm3, zmm3, zmm18
	vaesenc zmm4, zmm4, zmm18
	vaesenc zmm5, zmm5, zmm18
	vaesenc zmm6, zmm6, zmm18
	vaesenc zmm3, zmm3, zmm19
	vaesenc zmm4, zmm4, zmm19
	vaesenc zmm5, zmm5, zmm19
	vaesenc zmm6, zmm6, zmm19
	vaesenc zmm3, zmm3, zmm20
	vaesenc zmm4, zmm4, zmm20
	vaesenc zmm5, zmm5, zmm20
	vaesenc zmm6, zmm6, zmm20
	vaesenc zmm3, zmm3, zmm21
	vaesenc zmm4, zmm4, zmm21
	vaesenc zmm5, zmm5, zmm21
	vaesenc zmm6, zmm6, zmm21
	vaesenc zmm3, zmm3, zmm22
	vaesenc zmm4, zmm4, zmm22
	vaesenc zmm5, zmm5, zmm22
	vaesenc zmm6, zmm6, zmm22
	vaesenc zmm3, zmm3, zmm23
	vaesenc zmm4, zmm4, zmm23
	vaesenc zmm5, zmm5, zmm23
	vaesenc zmm6, zmm6, zmm23
	vaesenc zmm3, zmm3, zmm24
	vaesenc zmm4, zmm4, zmm24
	vaesenc zmm5, zmm5, zmm24
	vaesenc zmm6, zmm6, zmm24
	vaesenc zmm3, zmm3, zmm25
	vaesenc zmm4, zmm4, zmm25
	vaesenc zmm5, zmm5, zmm25
	vaesenc zmm6, zmm6, zmm25
	cmp rsi, 10
	je 214f
	vaesenc zmm3, zmm3, zmm26
	vaesenc zmm4, zmm4, zmm26
	vaesenc zmm5, zmm5, zmm26
	vaesenc zmm6, zmm6, zmm26
	vaesenc zmm3, zmm3, zmm27
	vaesenc zmm4, zmm4, zmm27
	vaesenc zmm5, zmm5, zmm27
	vaesenc zmm6, zmm6, zmm27
	cmp rsi, 12
	je 216f
	vaesenc zmm3, zmm3, zmm28
	vaesenc zmm4, zmm4, zmm28
	vaesenc zmm5, zmm5, zmm28
	vaesenc zmm6, zmm6, zmm28
	vaesenc zmm3, zmm3, zmm29
	vaesenc zmm4, zmm4, zmm29
	vaesenc zmm5, zmm5, zmm29
	vaesenc zmm6, zmm6, zmm29
	jmp 217f
216:
217:
	jmp 215f
214:
215:
	vaesenclast zmm3, zmm3, zmm31
	vaesenclast zmm4, zmm4, zmm31
	vaesenclast zmm5, zmm5, zmm31
	vaesenclast zmm6, zmm6, zmm31
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+256]
	vpxord zmm3, zmm3, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+256], zmm3
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+320]
	vpxord zmm4, zmm4, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+320], zmm4
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+384]
	vpxord zmm5, zmm5, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+384], zmm5
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+448]
	vpxord zmm6, zmm6, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+448], zmm6
	vpshufb zmm3, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm4, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm5, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm6, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpxord zmm3, zmm3, zmm16
	vpxord zmm4, zmm4, zmm16
	vpxord zmm5, zmm5, zmm16
	vpxord zmm6, zmm6, zmm16
	vaesenc zmm3, zmm3, zmm17
	vaesenc zmm4, zmm4, zmm17
	vaesenc zmm5, zmm5, zmm17
	vaesenc zmm6, zmm6, zmm17
	vaesenc zmm3, zmm3, zmm18
	vaesenc zmm4, zmm4, zmm18
	vaesenc zmm5, zmm5, zmm18
	vaesenc zmm6, zmm6, zmm18
	vaesenc zmm3, zmm3, zmm19
	vaesenc zmm4, zmm4, zmm19
	vaesenc zmm5, zmm5, zmm19
	vaesenc zmm6, zmm6, zmm19
	vaesenc zmm3, zmm3, zmm20
	vaesenc zmm4, zmm4, zmm20
	vaesenc zmm5, zmm5, zmm20
	vaesenc zmm6, zmm6, zmm20
	vaesenc zmm3, zmm3, zmm21
	vaesenc zmm4, zmm4, zmm21
	vaesenc zmm5, zmm5, zmm21
	vaesenc zmm6, zmm6, zmm21
	vaesenc zmm3, zmm3, zmm22
	vaesenc zmm4, zmm4, zmm22
	vaesenc zmm5, zmm5, zmm22
	vaesenc zmm6, zmm6, zmm22
	vaesenc zmm3, zmm3, zmm23
	vaesenc zmm4, zmm4, zmm23
	vaesenc zmm5, zmm5, zmm23
	vaesenc zmm6, zmm6, zmm23
	vaesenc zmm3, zmm3, zmm24
	vaesenc zmm4, zmm4, zmm24
	vaesenc zmm5, zmm5, zmm24
	vaesenc zmm6, zmm6, zmm24
	vaesenc zmm3, zmm3, zmm25
	vaesenc zmm4, zmm4, zmm25
	vaesenc zmm5, zmm5, zmm25
	vaesenc zmm6, zmm6, zmm25
	cmp rsi, 10
	je 218f
	vaesenc zmm3, zmm3, zmm26
	vaesenc zmm4, zmm4, zmm26
	vaesenc zmm5, zmm5, zmm26
	vaesenc zmm6, zmm6, zmm26
	vaesenc zmm3, zmm3, zmm27
	vaesenc zmm4, zmm4, zmm27
	vaesenc zmm5, zmm5, zmm27
	vaesenc zmm6, zmm6, zmm27
	cmp rsi, 12
	je 220f
	vaesenc zmm3, zmm3, zmm28
	vaesenc zmm4, zmm4, zmm28
	vaesenc zmm5, zmm5, zmm28
	vaesenc zmm6, zmm6, zmm28
	vaesenc zmm3, zmm3, zmm29
	vaesenc zmm4, zmm4, zmm29
	vaesenc zmm5, zmm5, zmm29
	vaesenc zmm6, zmm6, zmm29
	jmp 221f
220:
221:
	jmp 219f
218:
219:
	vaesenclast zmm3, zmm3, zmm31
	vaesenclast zmm4, zmm4, zmm31
	vaesenclast zmm5, zmm5, zmm31
	vaesenclast zmm6, zmm6, zmm31
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+512]
	vpxord zmm3, zmm3, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+512], zmm3
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+576]
	vpxord zmm4, zmm4, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+576], zmm4
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+640]
	vpxord zmm5, zmm5, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+640], zmm5
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+704]
	vpxord zmm6, zmm6, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+704], zmm6
222:
	vpshufb zmm3, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm4, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm5, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm6, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpxord zmm3, zmm3, zmm16
	vpxord zmm4, zmm4, zmm16
	vpxord zmm5, zmm5, zmm16
	vpxord zmm6, zmm6, zmm16
	vaesenc zmm3, zmm3, zmm17
	vaesenc zmm4, zmm4, zmm17
	vaesenc zmm5, zmm5, zmm17
	vaesenc zmm6, zmm6, zmm17
	vmovdqu32 zmm12, ZMMWORD PTR [r11+512]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx]
	vmovdqu32 zmm13, ZMMWORD PTR [r11+576]
	vmovdqu32 zmm1, ZMMWORD PTR [rdx+64]
	vpshufb zmm7, zmm7, zmm0
	vpxord zmm7, zmm7, zmm2
	vpshufb zmm1, zmm1, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpclmulqdq zmm2, zmm1, zmm13, 0
	vpxord zmm8, zmm11, zmm2
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpclmulqdq zmm2, zmm1, zmm13, 17
	vpxord zmm10, zmm11, zmm2
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm2, zmm7, zmm12, 16
	vpxord zmm9, zmm11, zmm2
	vpclmulqdq zmm11, zmm1, zmm13, 1
	vpclmulqdq zmm2, zmm1, zmm13, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vaesenc zmm3, zmm3, zmm18
	vaesenc zmm4, zmm4, zmm18
	vaesenc zmm5, zmm5, zmm18
	vaesenc zmm6, zmm6, zmm18
	vaesenc zmm3, zmm3, zmm19
	vaesenc zmm4, zmm4, zmm19
	vaesenc zmm5, zmm5, zmm19
	vaesenc zmm6, zmm6, zmm19
	vmovdqu32 zmm12, ZMMWORD PTR [r11+640]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+128]
	vmovdqu32 zmm13, ZMMWORD PTR [r11+704]
	vmovdqu32 zmm1, ZMMWORD PTR [rdx+192]
	vpshufb zmm7, zmm7, zmm0
	vpshufb zmm1, zmm1, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpclmulqdq zmm2, zmm1, zmm13, 0
	vpternlogd zmm8, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpclmulqdq zmm2, zmm1, zmm13, 17
	vpternlogd zmm10, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm2, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm1, zmm13, 1
	vpclmulqdq zmm2, zmm1, zmm13, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vaesenc zmm3, zmm3, zmm20
	vaesenc zmm4, zmm4, zmm20
	vaesenc zmm5, zmm5, zmm20
	vaesenc zmm6, zmm6, zmm20
	vaesenc zmm3, zmm3, zmm21
	vaesenc zmm4, zmm4, zmm21
	vaesenc zmm5, zmm5, zmm21
	vaesenc zmm6, zmm6, zmm21
	vaesenc zmm3, zmm3, zmm22
	vaesenc zmm4, zmm4, zmm22
	vaesenc zmm5, zmm5, zmm22
	vaesenc zmm6, zmm6, zmm22
	vaesenc zmm3, zmm3, zmm23
	vaesenc zmm4, zmm4, zmm23
	vaesenc zmm5, zmm5, zmm23
	vaesenc zmm6, zmm6, zmm23
	vaesenc zmm3, zmm3, zmm24
	vaesenc zmm4, zmm4, zmm24
	vaesenc zmm5, zmm5, zmm24
	vaesenc zmm6, zmm6, zmm24
	vaesenc zmm3, zmm3, zmm25
	vaesenc zmm4, zmm4, zmm25
	vaesenc zmm5, zmm5, zmm25
	vaesenc zmm6, zmm6, zmm25
	cmp rsi, 10
	je 223f
	vaesenc zmm3, zmm3, zmm26
	vaesenc zmm4, zmm4, zmm26
	vaesenc zmm5, zmm5, zmm26
	vaesenc zmm6, zmm6, zmm26
	vaesenc zmm3, zmm3, zmm27
	vaesenc zmm4, zmm4, zmm27
	vaesenc zmm5, zmm5, zmm27
	vaesenc zmm6, zmm6, zmm27
	cmp rsi, 12
	je 225f
	vaesenc zmm3, zmm3, zmm28
	vaesenc zmm4, zmm4, zmm28
	vaesenc zmm5, zmm5, zmm28
	vaesenc zmm6, zmm6, zmm28
	vaesenc zmm3, zmm3, zmm29
	vaesenc zmm4, zmm4, zmm29
	vaesenc zmm5, zmm5, zmm29
	vaesenc zmm6, zmm6, zmm29
	jmp 226f
225:
226:
	jmp 224f
223:
224:
	vaesenclast zmm3, zmm3, zmm31
	vaesenclast zmm4, zmm4, zmm31
	vaesenclast zmm5, zmm5, zmm31
	vaesenclast zmm6, zmm6, zmm31
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+768]
	vpxord zmm3, zmm3, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+768], zmm3
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+832]
	vpxord zmm4, zmm4, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+832], zmm4
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+896]
	vpxord zmm5, zmm5, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+896], zmm5
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+960]
	vpxord zmm6, zmm6, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+960], zmm6
	vpshufb zmm3, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm4, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm5, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm6, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpxord zmm3, zmm3, zmm16
	vpxord zmm4, zmm4, zmm16
	vpxord zmm5, zmm5, zmm16
	vpxord zmm6, zmm6, zmm16
	vaesenc zmm3, zmm3, zmm17
	vaesenc zmm4, zmm4, zmm17
	vaesenc zmm5, zmm5, zmm17
	vaesenc zmm6, zmm6, zmm17
	vmovdqu32 zmm12, ZMMWORD PTR [r11+256]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+256]
	vmovdqu32 zmm13, ZMMWORD PTR [r11+320]
	vmovdqu32 zmm1, ZMMWORD PTR [rdx+320]
	vpshufb zmm7, zmm7, zmm0
	vpshufb zmm1, zmm1, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpclmulqdq zmm2, zmm1, zmm13, 0
	vpternlogd zmm8, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpclmulqdq zmm2, zmm1, zmm13, 17
	vpternlogd zmm10, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm2, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm1, zmm13, 1
	vpclmulqdq zmm2, zmm1, zmm13, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vaesenc zmm3, zmm3, zmm18
	vaesenc zmm4, zmm4, zmm18
	vaesenc zmm5, zmm5, zmm18
	vaesenc zmm6, zmm6, zmm18
	vaesenc zmm3, zmm3, zmm19
	vaesenc zmm4, zmm4, zmm19
	vaesenc zmm5, zmm5, zmm19
	vaesenc zmm6, zmm6, zmm19
	vmovdqu32 zmm12, ZMMWORD PTR [r11+384]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+384]
	vmovdqu32 zmm13, ZMMWORD PTR [r11+448]
	vmovdqu32 zmm1, ZMMWORD PTR [rdx+448]
	vpshufb zmm7, zmm7, zmm0
	vpshufb zmm1, zmm1, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpclmulqdq zmm2, zmm1, zmm13, 0
	vpternlogd zmm8, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpclmulqdq zmm2, zmm1, zmm13, 17
	vpternlogd zmm10, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm2, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm1, zmm13, 1
	vpclmulqdq zmm2, zmm1, zmm13, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vaesenc zmm3, zmm3, zmm20
	vaesenc zmm4, zmm4, zmm20
	vaesenc zmm5, zmm5, zmm20
	vaesenc zmm6, zmm6, zmm20
	vaesenc zmm3, zmm3, zmm21
	vaesenc zmm4, zmm4, zmm21
	vaesenc zmm5, zmm5, zmm21
	vaesenc zmm6, zmm6, zmm21
	vaesenc zmm3, zmm3, zmm22
	vaesenc zmm4, zmm4, zmm22
	vaesenc zmm5, zmm5, zmm22
	vaesenc zmm6, zmm6, zmm22
	vaesenc zmm3, zmm3, zmm23
	vaesenc zmm4, zmm4, zmm23
	vaesenc zmm5, zmm5, zmm23
	vaesenc zmm6, zmm6, zmm23
	vaesenc zmm3, zmm3, zmm24
	vaesenc zmm4, zmm4, zmm24
	vaesenc zmm5, zmm5, zmm24
	vaesenc zmm6, zmm6, zmm24
	vaesenc zmm3, zmm3, zmm25
	vaesenc zmm4, zmm4, zmm25
	vaesenc zmm5, zmm5, zmm25
	vaesenc zmm6, zmm6, zmm25
	cmp rsi, 10
	je 227f
	vaesenc zmm3, zmm3, zmm26
	vaesenc zmm4, zmm4, zmm26
	vaesenc zmm5, zmm5, zmm26
	vaesenc zmm6, zmm6, zmm26
	vaesenc zmm3, zmm3, zmm27
	vaesenc zmm4, zmm4, zmm27
	vaesenc zmm5, zmm5, zmm27
	vaesenc zmm6, zmm6, zmm27
	cmp rsi, 12
	je 229f
	vaesenc zmm3, zmm3, zmm28
	vaesenc zmm4, zmm4, zmm28
	vaesenc zmm5, zmm5, zmm28
	vaesenc zmm6, zmm6, zmm28
	vaesenc zmm3, zmm3, zmm29
	vaesenc zmm4, zmm4, zmm29
	vaesenc zmm5, zmm5, zmm29
	vaesenc zmm6, zmm6, zmm29
	jmp 230f
229:
230:
	jmp 228f
227:
228:
	vaesenclast zmm3, zmm3, zmm31
	vaesenclast zmm4, zmm4, zmm31
	vaesenclast zmm5, zmm5, zmm31
	vaesenclast zmm6, zmm6, zmm31
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+1024]
	vpxord zmm3, zmm3, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+1024], zmm3
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+1088]
	vpxord zmm4, zmm4, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+1088], zmm4
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+1152]
	vpxord zmm5, zmm5, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+1152], zmm5
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+1216]
	vpxord zmm6, zmm6, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+1216], zmm6
	vpshufb zmm3, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm4, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm5, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm6, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpxord zmm3, zmm3, zmm16
	vpxord zmm4, zmm4, zmm16
	vpxord zmm5, zmm5, zmm16
	vpxord zmm6, zmm6, zmm16
	vaesenc zmm3, zmm3, zmm17
	vaesenc zmm4, zmm4, zmm17
	vaesenc zmm5, zmm5, zmm17
	vaesenc zmm6, zmm6, zmm17
	vmovdqu32 zmm12, ZMMWORD PTR [r11]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+512]
	vmovdqu32 zmm13, ZMMWORD PTR [r11+64]
	vmovdqu32 zmm1, ZMMWORD PTR [rdx+576]
	vpshufb zmm7, zmm7, zmm0
	vpshufb zmm1, zmm1, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpclmulqdq zmm2, zmm1, zmm13, 0
	vpternlogd zmm8, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpclmulqdq zmm2, zmm1, zmm13, 17
	vpternlogd zmm10, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm2, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm1, zmm13, 1
	vpclmulqdq zmm2, zmm1, zmm13, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vaesenc zmm3, zmm3, zmm18
	vaesenc zmm4, zmm4, zmm18
	vaesenc zmm5, zmm5, zmm18
	vaesenc zmm6, zmm6, zmm18
	vaesenc zmm3, zmm3, zmm19
	vaesenc zmm4, zmm4, zmm19
	vaesenc zmm5, zmm5, zmm19
	vaesenc zmm6, zmm6, zmm19
	vmovdqu32 zmm12, ZMMWORD PTR [r11+128]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+640]
	vmovdqu32 zmm13, ZMMWORD PTR [r11+192]
	vmovdqu32 zmm1, ZMMWORD PTR [rdx+704]
	vpshufb zmm7, zmm7, zmm0
	vpshufb zmm1, zmm1, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpclmulqdq zmm2, zmm1, zmm13, 0
	vpternlogd zmm8, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpclmulqdq zmm2, zmm1, zmm13, 17
	vpternlogd zmm10, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm2, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm1, zmm13, 1
	vpclmulqdq zmm2, zmm1, zmm13, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vaesenc zmm3, zmm3, zmm20
	vaesenc zmm4, zmm4, zmm20
	vaesenc zmm5, zmm5, zmm20
	vaesenc zmm6, zmm6, zmm20
	vaesenc zmm3, zmm3, zmm21
	vaesenc zmm4, zmm4, zmm21
	vaesenc zmm5, zmm5, zmm21
	vaesenc zmm6, zmm6, zmm21
	vaesenc zmm3, zmm3, zmm22
	vaesenc zmm4, zmm4, zmm22
	vaesenc zmm5, zmm5, zmm22
	vaesenc zmm6, zmm6, zmm22
	vmovdqu32 zmm1, ZMMWORD PTR [r11+832]
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vshufi32x4 zmm11, zmm10, zmm10, 14
	vpxor ymm10, ymm10, ymm11
	vextracti128 xmm11, ymm10, 1
	vpxor xmm2, xmm10, xmm11
	vaesenc zmm3, zmm3, zmm23
	vaesenc zmm4, zmm4, zmm23
	vaesenc zmm5, zmm5, zmm23
	vaesenc zmm6, zmm6, zmm23
	vaesenc zmm3, zmm3, zmm24
	vaesenc zmm4, zmm4, zmm24
	vaesenc zmm5, zmm5, zmm24
	vaesenc zmm6, zmm6, zmm24
	vaesenc zmm3, zmm3, zmm25
	vaesenc zmm4, zmm4, zmm25
	vaesenc zmm5, zmm5, zmm25
	vaesenc zmm6, zmm6, zmm25
	cmp rsi, 10
	je 231f
	vaesenc zmm3, zmm3, zmm26
	vaesenc zmm4, zmm4, zmm26
	vaesenc zmm5, zmm5, zmm26
	vaesenc zmm6, zmm6, zmm26
	vaesenc zmm3, zmm3, zmm27
	vaesenc zmm4, zmm4, zmm27
	vaesenc zmm5, zmm5, zmm27
	vaesenc zmm6, zmm6, zmm27
	cmp rsi, 12
	je 233f
	vaesenc zmm3, zmm3, zmm28
	vaesenc zmm4, zmm4, zmm28
	vaesenc zmm5, zmm5, zmm28
	vaesenc zmm6, zmm6, zmm28
	vaesenc zmm3, zmm3, zmm29
	vaesenc zmm4, zmm4, zmm29
	vaesenc zmm5, zmm5, zmm29
	vaesenc zmm6, zmm6, zmm29
	jmp 234f
233:
234:
	jmp 232f
231:
232:
	vaesenclast zmm3, zmm3, zmm31
	vaesenclast zmm4, zmm4, zmm31
	vaesenclast zmm5, zmm5, zmm31
	vaesenclast zmm6, zmm6, zmm31
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+1280]
	vpxord zmm3, zmm3, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+1280], zmm3
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+1344]
	vpxord zmm4, zmm4, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+1344], zmm4
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+1408]
	vpxord zmm5, zmm5, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+1408], zmm5
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+1472]
	vpxord zmm6, zmm6, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+1472], zmm6
	add rdx, 768
	sub r9, 48
	cmp r9, 96
	jae 222b
	vmovdqu32 zmm1, ZMMWORD PTR [r11+832]
	vmovdqu32 zmm12, ZMMWORD PTR [r11+64]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+64]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm8, zmm7, zmm12, 0
	vpclmulqdq zmm10, zmm7, zmm12, 17
	vpclmulqdq zmm9, zmm7, zmm12, 1
	vpclmulqdq zmm11, zmm7, zmm12, 16
	vpxord zmm9, zmm9, zmm11
	vmovdqu32 zmm12, ZMMWORD PTR [r11+128]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+128]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vmovdqu32 zmm12, ZMMWORD PTR [r11+192]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+192]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vmovdqu32 zmm12, ZMMWORD PTR [r11]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx]
	vpshufb zmm7, zmm7, zmm0
	vpxord zmm7, zmm7, zmm2
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vshufi32x4 zmm11, zmm10, zmm10, 14
	vpxor ymm10, ymm10, ymm11
	vextracti128 xmm11, ymm10, 1
	vpxor xmm2, xmm10, xmm11
	add rdx, 256
	sub r9, 16
	vmovdqu32 zmm12, ZMMWORD PTR [r11+64]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+64]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm8, zmm7, zmm12, 0
	vpclmulqdq zmm10, zmm7, zmm12, 17
	vpclmulqdq zmm9, zmm7, zmm12, 1
	vpclmulqdq zmm11, zmm7, zmm12, 16
	vpxord zmm9, zmm9, zmm11
	vmovdqu32 zmm12, ZMMWORD PTR [r11+128]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+128]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vmovdqu32 zmm12, ZMMWORD PTR [r11+192]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+192]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vmovdqu32 zmm12, ZMMWORD PTR [r11]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx]
	vpshufb zmm7, zmm7, zmm0
	vpxord zmm7, zmm7, zmm2
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vshufi32x4 zmm11, zmm10, zmm10, 14
	vpxor ymm10, ymm10, ymm11
	vextracti128 xmm11, ymm10, 1
	vpxor xmm2, xmm10, xmm11
	add rdx, 256
	sub r9, 16
	jmp 213f
212:
	vmovdqu32 ZMMWORD PTR [r11+896], zmm15
	vmovdqu32 zmm7, ZMMWORD PTR [rdx]
	vmovdqu32 zmm1, ZMMWORD PTR [rdx+64]
	vmovdqu32 zmm12, ZMMWORD PTR [rdx+128]
	vmovdqu32 zmm15, ZMMWORD PTR [rdx+192]
	vpshufb zmm7, zmm7, zmm0
	vpshufb zmm1, zmm1, zmm0
	vpshufb zmm12, zmm12, zmm0
	vpshufb zmm15, zmm15, zmm0
	cmp r9, 64
	jb 235f
237:
	vmovdqu32 zmm11, ZMMWORD PTR [r11+896]
	vpshufb zmm3, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm11
	vpshufb zmm4, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm11
	vpshufb zmm5, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm11
	vpshufb zmm6, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm11
	vpxord zmm3, zmm3, zmm16
	vpxord zmm4, zmm4, zmm16
	vpxord zmm5, zmm5, zmm16
	vpxord zmm6, zmm6, zmm16
	vaesenc zmm3, zmm3, zmm17
	vaesenc zmm4, zmm4, zmm17
	vaesenc zmm5, zmm5, zmm17
	vaesenc zmm6, zmm6, zmm17
	vaesenc zmm3, zmm3, zmm18
	vaesenc zmm4, zmm4, zmm18
	vaesenc zmm5, zmm5, zmm18
	vaesenc zmm6, zmm6, zmm18
	vaesenc zmm3, zmm3, zmm19
	vaesenc zmm4, zmm4, zmm19
	vaesenc zmm5, zmm5, zmm19
	vaesenc zmm6, zmm6, zmm19
	vaesenc zmm3, zmm3, zmm20
	vaesenc zmm4, zmm4, zmm20
	vaesenc zmm5, zmm5, zmm20
	vaesenc zmm6, zmm6, zmm20
	vmovdqu32 zmm13, ZMMWORD PTR [r11+512]
	vpxord zmm7, zmm7, zmm2
	vpclmulqdq zmm9, zmm7, zmm13, 1
	vpclmulqdq zmm11, zmm7, zmm13, 16
	vpxord zmm9, zmm9, zmm11
	vpclmulqdq zmm8, zmm7, zmm13, 0
	vpclmulqdq zmm7, zmm7, zmm13, 17
	vmovdqu32 zmm13, ZMMWORD PTR [r11+576]
	vpclmulqdq zmm2, zmm1, zmm13, 0
	vpxord zmm8, zmm8, zmm2
	vpclmulqdq zmm10, zmm1, zmm13, 17
	vpxord zmm10, zmm10, zmm7
	vpclmulqdq zmm11, zmm1, zmm13, 1
	vpclmulqdq zmm2, zmm1, zmm13, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vaesenc zmm3, zmm3, zmm21
	vaesenc zmm4, zmm4, zmm21
	vaesenc zmm5, zmm5, zmm21
	vaesenc zmm6, zmm6, zmm21
	vaesenc zmm3, zmm3, zmm22
	vaesenc zmm4, zmm4, zmm22
	vaesenc zmm5, zmm5, zmm22
	vaesenc zmm6, zmm6, zmm22
	vaesenc zmm3, zmm3, zmm23
	vaesenc zmm4, zmm4, zmm23
	vaesenc zmm5, zmm5, zmm23
	vaesenc zmm6, zmm6, zmm23
	vmovdqu32 zmm13, ZMMWORD PTR [r11+640]
	vpclmulqdq zmm11, zmm12, zmm13, 1
	vpclmulqdq zmm2, zmm12, zmm13, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm12, zmm13, 0
	vpclmulqdq zmm12, zmm12, zmm13, 17
	vmovdqu32 zmm13, ZMMWORD PTR [r11+704]
	vpclmulqdq zmm2, zmm15, zmm13, 0
	vpternlogd zmm8, zmm11, zmm2, 150
	vpclmulqdq zmm2, zmm15, zmm13, 17
	vpternlogd zmm10, zmm12, zmm2, 150
	vpclmulqdq zmm11, zmm15, zmm13, 1
	vpclmulqdq zmm2, zmm15, zmm13, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vaesenc zmm3, zmm3, zmm24
	vaesenc zmm4, zmm4, zmm24
	vaesenc zmm5, zmm5, zmm24
	vaesenc zmm6, zmm6, zmm24
	vaesenc zmm3, zmm3, zmm25
	vaesenc zmm4, zmm4, zmm25
	vaesenc zmm5, zmm5, zmm25
	vaesenc zmm6, zmm6, zmm25
	cmp rsi, 10
	je 238f
	vaesenc zmm3, zmm3, zmm26
	vaesenc zmm4, zmm4, zmm26
	vaesenc zmm5, zmm5, zmm26
	vaesenc zmm6, zmm6, zmm26
	vaesenc zmm3, zmm3, zmm27
	vaesenc zmm4, zmm4, zmm27
	vaesenc zmm5, zmm5, zmm27
	vaesenc zmm6, zmm6, zmm27
	cmp rsi, 12
	je 240f
	vaesenc zmm3, zmm3, zmm28
	vaesenc zmm4, zmm4, zmm28
	vaesenc zmm5, zmm5, zmm28
	vaesenc zmm6, zmm6, zmm28
	vaesenc zmm3, zmm3, zmm29
	vaesenc zmm4, zmm4, zmm29
	vaesenc zmm5, zmm5, zmm29
	vaesenc zmm6, zmm6, zmm29
	jmp 241f
240:
241:
	jmp 239f
238:
239:
	vaesenclast zmm3, zmm3, zmm31
	vaesenclast zmm4, zmm4, zmm31
	vaesenclast zmm5, zmm5, zmm31
	vaesenclast zmm6, zmm6, zmm31
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+256]
	vpxord zmm3, zmm3, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+256], zmm3
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+320]
	vpxord zmm4, zmm4, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+320], zmm4
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+384]
	vpxord zmm5, zmm5, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+384], zmm5
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+448]
	vpxord zmm6, zmm6, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+448], zmm6
	vpshufb zmm7, zmm3, zmm0
	vpshufb zmm1, zmm4, zmm0
	vpshufb zmm12, zmm5, zmm0
	vpshufb zmm15, zmm6, zmm0
	vmovdqu32 zmm11, ZMMWORD PTR [r11+896]
	vpshufb zmm3, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm11
	vpshufb zmm4, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm11
	vpshufb zmm5, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm11
	vpshufb zmm6, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm11
	vpxord zmm3, zmm3, zmm16
	vpxord zmm4, zmm4, zmm16
	vpxord zmm5, zmm5, zmm16
	vpxord zmm6, zmm6, zmm16
	vaesenc zmm3, zmm3, zmm17
	vaesenc zmm4, zmm4, zmm17
	vaesenc zmm5, zmm5, zmm17
	vaesenc zmm6, zmm6, zmm17
	vaesenc zmm3, zmm3, zmm18
	vaesenc zmm4, zmm4, zmm18
	vaesenc zmm5, zmm5, zmm18
	vaesenc zmm6, zmm6, zmm18
	vaesenc zmm3, zmm3, zmm19
	vaesenc zmm4, zmm4, zmm19
	vaesenc zmm5, zmm5, zmm19
	vaesenc zmm6, zmm6, zmm19
	vaesenc zmm3, zmm3, zmm20
	vaesenc zmm4, zmm4, zmm20
	vaesenc zmm5, zmm5, zmm20
	vaesenc zmm6, zmm6, zmm20
	vmovdqu32 zmm13, ZMMWORD PTR [r11+256]
	vpclmulqdq zmm11, zmm7, zmm13, 1
	vpclmulqdq zmm2, zmm7, zmm13, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm7, zmm13, 0
	vpclmulqdq zmm7, zmm7, zmm13, 17
	vmovdqu32 zmm13, ZMMWORD PTR [r11+320]
	vpclmulqdq zmm2, zmm1, zmm13, 0
	vpternlogd zmm8, zmm11, zmm2, 150
	vpclmulqdq zmm2, zmm1, zmm13, 17
	vpternlogd zmm10, zmm7, zmm2, 150
	vpclmulqdq zmm11, zmm1, zmm13, 1
	vpclmulqdq zmm2, zmm1, zmm13, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vaesenc zmm3, zmm3, zmm21
	vaesenc zmm4, zmm4, zmm21
	vaesenc zmm5, zmm5, zmm21
	vaesenc zmm6, zmm6, zmm21
	vaesenc zmm3, zmm3, zmm22
	vaesenc zmm4, zmm4, zmm22
	vaesenc zmm5, zmm5, zmm22
	vaesenc zmm6, zmm6, zmm22
	vaesenc zmm3, zmm3, zmm23
	vaesenc zmm4, zmm4, zmm23
	vaesenc zmm5, zmm5, zmm23
	vaesenc zmm6, zmm6, zmm23
	vmovdqu32 zmm13, ZMMWORD PTR [r11+384]
	vpclmulqdq zmm11, zmm12, zmm13, 1
	vpclmulqdq zmm2, zmm12, zmm13, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm12, zmm13, 0
	vpclmulqdq zmm12, zmm12, zmm13, 17
	vmovdqu32 zmm13, ZMMWORD PTR [r11+448]
	vpclmulqdq zmm2, zmm15, zmm13, 0
	vpternlogd zmm8, zmm11, zmm2, 150
	vpclmulqdq zmm2, zmm15, zmm13, 17
	vpternlogd zmm10, zmm12, zmm2, 150
	vpclmulqdq zmm11, zmm15, zmm13, 1
	vpclmulqdq zmm2, zmm15, zmm13, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vaesenc zmm3, zmm3, zmm24
	vaesenc zmm4, zmm4, zmm24
	vaesenc zmm5, zmm5, zmm24
	vaesenc zmm6, zmm6, zmm24
	vaesenc zmm3, zmm3, zmm25
	vaesenc zmm4, zmm4, zmm25
	vaesenc zmm5, zmm5, zmm25
	vaesenc zmm6, zmm6, zmm25
	cmp rsi, 10
	je 242f
	vaesenc zmm3, zmm3, zmm26
	vaesenc zmm4, zmm4, zmm26
	vaesenc zmm5, zmm5, zmm26
	vaesenc zmm6, zmm6, zmm26
	vaesenc zmm3, zmm3, zmm27
	vaesenc zmm4, zmm4, zmm27
	vaesenc zmm5, zmm5, zmm27
	vaesenc zmm6, zmm6, zmm27
	cmp rsi, 12
	je 244f
	vaesenc zmm3, zmm3, zmm28
	vaesenc zmm4, zmm4, zmm28
	vaesenc zmm5, zmm5, zmm28
	vaesenc zmm6, zmm6, zmm28
	vaesenc zmm3, zmm3, zmm29
	vaesenc zmm4, zmm4, zmm29
	vaesenc zmm5, zmm5, zmm29
	vaesenc zmm6, zmm6, zmm29
	jmp 245f
244:
245:
	jmp 243f
242:
243:
	vaesenclast zmm3, zmm3, zmm31
	vaesenclast zmm4, zmm4, zmm31
	vaesenclast zmm5, zmm5, zmm31
	vaesenclast zmm6, zmm6, zmm31
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+512]
	vpxord zmm3, zmm3, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+512], zmm3
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+576]
	vpxord zmm4, zmm4, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+576], zmm4
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+640]
	vpxord zmm5, zmm5, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+640], zmm5
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+704]
	vpxord zmm6, zmm6, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+704], zmm6
	vpshufb zmm7, zmm3, zmm0
	vpshufb zmm1, zmm4, zmm0
	vpshufb zmm12, zmm5, zmm0
	vpshufb zmm15, zmm6, zmm0
	vmovdqu32 zmm11, ZMMWORD PTR [r11+896]
	vpshufb zmm3, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm11
	vpshufb zmm4, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm11
	vpshufb zmm5, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm11
	vpshufb zmm6, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm11
	vpxord zmm3, zmm3, zmm16
	vpxord zmm4, zmm4, zmm16
	vpxord zmm5, zmm5, zmm16
	vpxord zmm6, zmm6, zmm16
	vaesenc zmm3, zmm3, zmm17
	vaesenc zmm4, zmm4, zmm17
	vaesenc zmm5, zmm5, zmm17
	vaesenc zmm6, zmm6, zmm17
	vaesenc zmm3, zmm3, zmm18
	vaesenc zmm4, zmm4, zmm18
	vaesenc zmm5, zmm5, zmm18
	vaesenc zmm6, zmm6, zmm18
	vaesenc zmm3, zmm3, zmm19
	vaesenc zmm4, zmm4, zmm19
	vaesenc zmm5, zmm5, zmm19
	vaesenc zmm6, zmm6, zmm19
	vaesenc zmm3, zmm3, zmm20
	vaesenc zmm4, zmm4, zmm20
	vaesenc zmm5, zmm5, zmm20
	vaesenc zmm6, zmm6, zmm20
	vmovdqu32 zmm13, ZMMWORD PTR [r11]
	vpclmulqdq zmm11, zmm7, zmm13, 1
	vpclmulqdq zmm2, zmm7, zmm13, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm7, zmm13, 0
	vpclmulqdq zmm7, zmm7, zmm13, 17
	vmovdqu32 zmm13, ZMMWORD PTR [r11+64]
	vpclmulqdq zmm2, zmm1, zmm13, 0
	vpternlogd zmm8, zmm11, zmm2, 150
	vpclmulqdq zmm2, zmm1, zmm13, 17
	vpternlogd zmm10, zmm7, zmm2, 150
	vpclmulqdq zmm11, zmm1, zmm13, 1
	vpclmulqdq zmm2, zmm1, zmm13, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vaesenc zmm3, zmm3, zmm21
	vaesenc zmm4, zmm4, zmm21
	vaesenc zmm5, zmm5, zmm21
	vaesenc zmm6, zmm6, zmm21
	vaesenc zmm3, zmm3, zmm22
	vaesenc zmm4, zmm4, zmm22
	vaesenc zmm5, zmm5, zmm22
	vaesenc zmm6, zmm6, zmm22
	vaesenc zmm3, zmm3, zmm23
	vaesenc zmm4, zmm4, zmm23
	vaesenc zmm5, zmm5, zmm23
	vaesenc zmm6, zmm6, zmm23
	vmovdqu32 zmm13, ZMMWORD PTR [r11+128]
	vpclmulqdq zmm11, zmm12, zmm13, 1
	vpclmulqdq zmm2, zmm12, zmm13, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm12, zmm13, 0
	vpclmulqdq zmm12, zmm12, zmm13, 17
	vmovdqu32 zmm13, ZMMWORD PTR [r11+192]
	vpclmulqdq zmm2, zmm15, zmm13, 0
	vpternlogd zmm8, zmm11, zmm2, 150
	vpclmulqdq zmm2, zmm15, zmm13, 17
	vpternlogd zmm10, zmm12, zmm2, 150
	vpclmulqdq zmm11, zmm15, zmm13, 1
	vpclmulqdq zmm2, zmm15, zmm13, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vaesenc zmm3, zmm3, zmm24
	vaesenc zmm4, zmm4, zmm24
	vaesenc zmm5, zmm5, zmm24
	vaesenc zmm6, zmm6, zmm24
	vaesenc zmm3, zmm3, zmm25
	vaesenc zmm4, zmm4, zmm25
	vaesenc zmm5, zmm5, zmm25
	vaesenc zmm6, zmm6, zmm25
	vmovdqu32 zmm1, ZMMWORD PTR [r11+832]
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vshufi32x4 zmm11, zmm10, zmm10, 14
	vpxor ymm10, ymm10, ymm11
	vextracti128 xmm11, ymm10, 1
	vpxor xmm2, xmm10, xmm11
	cmp rsi, 10
	je 246f
	vaesenc zmm3, zmm3, zmm26
	vaesenc zmm4, zmm4, zmm26
	vaesenc zmm5, zmm5, zmm26
	vaesenc zmm6, zmm6, zmm26
	vaesenc zmm3, zmm3, zmm27
	vaesenc zmm4, zmm4, zmm27
	vaesenc zmm5, zmm5, zmm27
	vaesenc zmm6, zmm6, zmm27
	cmp rsi, 12
	je 248f
	vaesenc zmm3, zmm3, zmm28
	vaesenc zmm4, zmm4, zmm28
	vaesenc zmm5, zmm5, zmm28
	vaesenc zmm6, zmm6, zmm28
	vaesenc zmm3, zmm3, zmm29
	vaesenc zmm4, zmm4, zmm29
	vaesenc zmm5, zmm5, zmm29
	vaesenc zmm6, zmm6, zmm29
	jmp 249f
248:
249:
	jmp 247f
246:
247:
	vaesenclast zmm3, zmm3, zmm31
	vaesenclast zmm4, zmm4, zmm31
	vaesenclast zmm5, zmm5, zmm31
	vaesenclast zmm6, zmm6, zmm31
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+768]
	vpxord zmm3, zmm3, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+768], zmm3
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+832]
	vpxord zmm4, zmm4, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+832], zmm4
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+896]
	vpxord zmm5, zmm5, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+896], zmm5
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+960]
	vpxord zmm6, zmm6, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+960], zmm6
	vpshufb zmm7, zmm3, zmm0
	vpshufb zmm1, zmm4, zmm0
	vpshufb zmm12, zmm5, zmm0
	vpshufb zmm15, zmm6, zmm0
	add rdx, 768
	sub r9, 48
	cmp r9, 64
	jae 237b
	jmp 236f
235:
236:
	cmp r9, 48
	jb 250f
	vmovdqu32 zmm11, ZMMWORD PTR [r11+896]
	vpshufb zmm3, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm11
	vpshufb zmm4, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm11
	vpshufb zmm5, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm11
	vpshufb zmm6, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm11
	vpxord zmm3, zmm3, zmm16
	vpxord zmm4, zmm4, zmm16
	vpxord zmm5, zmm5, zmm16
	vpxord zmm6, zmm6, zmm16
	vaesenc zmm3, zmm3, zmm17
	vaesenc zmm4, zmm4, zmm17
	vaesenc zmm5, zmm5, zmm17
	vaesenc zmm6, zmm6, zmm17
	vaesenc zmm3, zmm3, zmm18
	vaesenc zmm4, zmm4, zmm18
	vaesenc zmm5, zmm5, zmm18
	vaesenc zmm6, zmm6, zmm18
	vaesenc zmm3, zmm3, zmm19
	vaesenc zmm4, zmm4, zmm19
	vaesenc zmm5, zmm5, zmm19
	vaesenc zmm6, zmm6, zmm19
	vaesenc zmm3, zmm3, zmm20
	vaesenc zmm4, zmm4, zmm20
	vaesenc zmm5, zmm5, zmm20
	vaesenc zmm6, zmm6, zmm20
	vmovdqu32 zmm13, ZMMWORD PTR [r11+256]
	vpxord zmm7, zmm7, zmm2
	vpclmulqdq zmm9, zmm7, zmm13, 1
	vpclmulqdq zmm11, zmm7, zmm13, 16
	vpxord zmm9, zmm9, zmm11
	vpclmulqdq zmm8, zmm7, zmm13, 0
	vpclmulqdq zmm7, zmm7, zmm13, 17
	vmovdqu32 zmm13, ZMMWORD PTR [r11+320]
	vpclmulqdq zmm2, zmm1, zmm13, 0
	vpxord zmm8, zmm8, zmm2
	vpclmulqdq zmm10, zmm1, zmm13, 17
	vpxord zmm10, zmm10, zmm7
	vpclmulqdq zmm11, zmm1, zmm13, 1
	vpclmulqdq zmm2, zmm1, zmm13, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vaesenc zmm3, zmm3, zmm21
	vaesenc zmm4, zmm4, zmm21
	vaesenc zmm5, zmm5, zmm21
	vaesenc zmm6, zmm6, zmm21
	vaesenc zmm3, zmm3, zmm22
	vaesenc zmm4, zmm4, zmm22
	vaesenc zmm5, zmm5, zmm22
	vaesenc zmm6, zmm6, zmm22
	vaesenc zmm3, zmm3, zmm23
	vaesenc zmm4, zmm4, zmm23
	vaesenc zmm5, zmm5, zmm23
	vaesenc zmm6, zmm6, zmm23
	vmovdqu32 zmm13, ZMMWORD PTR [r11+384]
	vpclmulqdq zmm11, zmm12, zmm13, 1
	vpclmulqdq zmm2, zmm12, zmm13, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm12, zmm13, 0
	vpclmulqdq zmm12, zmm12, zmm13, 17
	vmovdqu32 zmm13, ZMMWORD PTR [r11+448]
	vpclmulqdq zmm2, zmm15, zmm13, 0
	vpternlogd zmm8, zmm11, zmm2, 150
	vpclmulqdq zmm2, zmm15, zmm13, 17
	vpternlogd zmm10, zmm12, zmm2, 150
	vpclmulqdq zmm11, zmm15, zmm13, 1
	vpclmulqdq zmm2, zmm15, zmm13, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vaesenc zmm3, zmm3, zmm24
	vaesenc zmm4, zmm4, zmm24
	vaesenc zmm5, zmm5, zmm24
	vaesenc zmm6, zmm6, zmm24
	vaesenc zmm3, zmm3, zmm25
	vaesenc zmm4, zmm4, zmm25
	vaesenc zmm5, zmm5, zmm25
	vaesenc zmm6, zmm6, zmm25
	cmp rsi, 10
	je 252f
	vaesenc zmm3, zmm3, zmm26
	vaesenc zmm4, zmm4, zmm26
	vaesenc zmm5, zmm5, zmm26
	vaesenc zmm6, zmm6, zmm26
	vaesenc zmm3, zmm3, zmm27
	vaesenc zmm4, zmm4, zmm27
	vaesenc zmm5, zmm5, zmm27
	vaesenc zmm6, zmm6, zmm27
	cmp rsi, 12
	je 254f
	vaesenc zmm3, zmm3, zmm28
	vaesenc zmm4, zmm4, zmm28
	vaesenc zmm5, zmm5, zmm28
	vaesenc zmm6, zmm6, zmm28
	vaesenc zmm3, zmm3, zmm29
	vaesenc zmm4, zmm4, zmm29
	vaesenc zmm5, zmm5, zmm29
	vaesenc zmm6, zmm6, zmm29
	jmp 255f
254:
255:
	jmp 253f
252:
253:
	vaesenclast zmm3, zmm3, zmm31
	vaesenclast zmm4, zmm4, zmm31
	vaesenclast zmm5, zmm5, zmm31
	vaesenclast zmm6, zmm6, zmm31
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+256]
	vpxord zmm3, zmm3, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+256], zmm3
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+320]
	vpxord zmm4, zmm4, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+320], zmm4
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+384]
	vpxord zmm5, zmm5, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+384], zmm5
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+448]
	vpxord zmm6, zmm6, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+448], zmm6
	vpshufb zmm7, zmm3, zmm0
	vpshufb zmm1, zmm4, zmm0
	vpshufb zmm12, zmm5, zmm0
	vpshufb zmm15, zmm6, zmm0
	vmovdqu32 zmm11, ZMMWORD PTR [r11+896]
	vpshufb zmm3, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm11
	vpshufb zmm4, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm11
	vpshufb zmm5, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm11
	vpshufb zmm6, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm11
	vpxord zmm3, zmm3, zmm16
	vpxord zmm4, zmm4, zmm16
	vpxord zmm5, zmm5, zmm16
	vpxord zmm6, zmm6, zmm16
	vaesenc zmm3, zmm3, zmm17
	vaesenc zmm4, zmm4, zmm17
	vaesenc zmm5, zmm5, zmm17
	vaesenc zmm6, zmm6, zmm17
	vaesenc zmm3, zmm3, zmm18
	vaesenc zmm4, zmm4, zmm18
	vaesenc zmm5, zmm5, zmm18
	vaesenc zmm6, zmm6, zmm18
	vaesenc zmm3, zmm3, zmm19
	vaesenc zmm4, zmm4, zmm19
	vaesenc zmm5, zmm5, zmm19
	vaesenc zmm6, zmm6, zmm19
	vaesenc zmm3, zmm3, zmm20
	vaesenc zmm4, zmm4, zmm20
	vaesenc zmm5, zmm5, zmm20
	vaesenc zmm6, zmm6, zmm20
	vmovdqu32 zmm13, ZMMWORD PTR [r11]
	vpclmulqdq zmm11, zmm7, zmm13, 1
	vpclmulqdq zmm2, zmm7, zmm13, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm7, zmm13, 0
	vpclmulqdq zmm7, zmm7, zmm13, 17
	vmovdqu32 zmm13, ZMMWORD PTR [r11+64]
	vpclmulqdq zmm2, zmm1, zmm13, 0
	vpternlogd zmm8, zmm11, zmm2, 150
	vpclmulqdq zmm2, zmm1, zmm13, 17
	vpternlogd zmm10, zmm7, zmm2, 150
	vpclmulqdq zmm11, zmm1, zmm13, 1
	vpclmulqdq zmm2, zmm1, zmm13, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vaesenc zmm3, zmm3, zmm21
	vaesenc zmm4, zmm4, zmm21
	vaesenc zmm5, zmm5, zmm21
	vaesenc zmm6, zmm6, zmm21
	vaesenc zmm3, zmm3, zmm22
	vaesenc zmm4, zmm4, zmm22
	vaesenc zmm5, zmm5, zmm22
	vaesenc zmm6, zmm6, zmm22
	vaesenc zmm3, zmm3, zmm23
	vaesenc zmm4, zmm4, zmm23
	vaesenc zmm5, zmm5, zmm23
	vaesenc zmm6, zmm6, zmm23
	vmovdqu32 zmm13, ZMMWORD PTR [r11+128]
	vpclmulqdq zmm11, zmm12, zmm13, 1
	vpclmulqdq zmm2, zmm12, zmm13, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm12, zmm13, 0
	vpclmulqdq zmm12, zmm12, zmm13, 17
	vmovdqu32 zmm13, ZMMWORD PTR [r11+192]
	vpclmulqdq zmm2, zmm15, zmm13, 0
	vpternlogd zmm8, zmm11, zmm2, 150
	vpclmulqdq zmm2, zmm15, zmm13, 17
	vpternlogd zmm10, zmm12, zmm2, 150
	vpclmulqdq zmm11, zmm15, zmm13, 1
	vpclmulqdq zmm2, zmm15, zmm13, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vaesenc zmm3, zmm3, zmm24
	vaesenc zmm4, zmm4, zmm24
	vaesenc zmm5, zmm5, zmm24
	vaesenc zmm6, zmm6, zmm24
	vaesenc zmm3, zmm3, zmm25
	vaesenc zmm4, zmm4, zmm25
	vaesenc zmm5, zmm5, zmm25
	vaesenc zmm6, zmm6, zmm25
	vmovdqu32 zmm1, ZMMWORD PTR [r11+832]
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vshufi32x4 zmm11, zmm10, zmm10, 14
	vpxor ymm10, ymm10, ymm11
	vextracti128 xmm11, ymm10, 1
	vpxor xmm2, xmm10, xmm11
	cmp rsi, 10
	je 256f
	vaesenc zmm3, zmm3, zmm26
	vaesenc zmm4, zmm4, zmm26
	vaesenc zmm5, zmm5, zmm26
	vaesenc zmm6, zmm6, zmm26
	vaesenc zmm3, zmm3, zmm27
	vaesenc zmm4, zmm4, zmm27
	vaesenc zmm5, zmm5, zmm27
	vaesenc zmm6, zmm6, zmm27
	cmp rsi, 12
	je 258f
	vaesenc zmm3, zmm3, zmm28
	vaesenc zmm4, zmm4, zmm28
	vaesenc zmm5, zmm5, zmm28
	vaesenc zmm6, zmm6, zmm28
	vaesenc zmm3, zmm3, zmm29
	vaesenc zmm4, zmm4, zmm29
	vaesenc zmm5, zmm5, zmm29
	vaesenc zmm6, zmm6, zmm29
	jmp 259f
258:
259:
	jmp 257f
256:
257:
	vaesenclast zmm3, zmm3, zmm31
	vaesenclast zmm4, zmm4, zmm31
	vaesenclast zmm5, zmm5, zmm31
	vaesenclast zmm6, zmm6, zmm31
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+512]
	vpxord zmm3, zmm3, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+512], zmm3
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+576]
	vpxord zmm4, zmm4, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+576], zmm4
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+640]
	vpxord zmm5, zmm5, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+640], zmm5
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+704]
	vpxord zmm6, zmm6, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+704], zmm6
	vpshufb zmm7, zmm3, zmm0
	vpshufb zmm1, zmm4, zmm0
	vpshufb zmm12, zmm5, zmm0
	vpshufb zmm15, zmm6, zmm0
	add rdx, 512
	sub r9, 32
	jmp 251f
250:
251:
	cmp r9, 32
	jb 260f
	vmovdqu32 zmm11, ZMMWORD PTR [r11+896]
	vpshufb zmm3, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm11
	vpshufb zmm4, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm11
	vpshufb zmm5, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm11
	vpshufb zmm6, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm11
	vpxord zmm3, zmm3, zmm16
	vpxord zmm4, zmm4, zmm16
	vpxord zmm5, zmm5, zmm16
	vpxord zmm6, zmm6, zmm16
	vaesenc zmm3, zmm3, zmm17
	vaesenc zmm4, zmm4, zmm17
	vaesenc zmm5, zmm5, zmm17
	vaesenc zmm6, zmm6, zmm17
	vaesenc zmm3, zmm3, zmm18
	vaesenc zmm4, zmm4, zmm18
	vaesenc zmm5, zmm5, zmm18
	vaesenc zmm6, zmm6, zmm18
	vaesenc zmm3, zmm3, zmm19
	vaesenc zmm4, zmm4, zmm19
	vaesenc zmm5, zmm5, zmm19
	vaesenc zmm6, zmm6, zmm19
	vaesenc zmm3, zmm3, zmm20
	vaesenc zmm4, zmm4, zmm20
	vaesenc zmm5, zmm5, zmm20
	vaesenc zmm6, zmm6, zmm20
	vmovdqu32 zmm13, ZMMWORD PTR [r11]
	vpxord zmm7, zmm7, zmm2
	vpclmulqdq zmm9, zmm7, zmm13, 1
	vpclmulqdq zmm11, zmm7, zmm13, 16
	vpxord zmm9, zmm9, zmm11
	vpclmulqdq zmm8, zmm7, zmm13, 0
	vpclmulqdq zmm7, zmm7, zmm13, 17
	vmovdqu32 zmm13, ZMMWORD PTR [r11+64]
	vpclmulqdq zmm2, zmm1, zmm13, 0
	vpxord zmm8, zmm8, zmm2
	vpclmulqdq zmm10, zmm1, zmm13, 17
	vpxord zmm10, zmm10, zmm7
	vpclmulqdq zmm11, zmm1, zmm13, 1
	vpclmulqdq zmm2, zmm1, zmm13, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vaesenc zmm3, zmm3, zmm21
	vaesenc zmm4, zmm4, zmm21
	vaesenc zmm5, zmm5, zmm21
	vaesenc zmm6, zmm6, zmm21
	vaesenc zmm3, zmm3, zmm22
	vaesenc zmm4, zmm4, zmm22
	vaesenc zmm5, zmm5, zmm22
	vaesenc zmm6, zmm6, zmm22
	vaesenc zmm3, zmm3, zmm23
	vaesenc zmm4, zmm4, zmm23
	vaesenc zmm5, zmm5, zmm23
	vaesenc zmm6, zmm6, zmm23
	vmovdqu32 zmm13, ZMMWORD PTR [r11+128]
	vpclmulqdq zmm11, zmm12, zmm13, 1
	vpclmulqdq zmm2, zmm12, zmm13, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm12, zmm13, 0
	vpclmulqdq zmm12, zmm12, zmm13, 17
	vmovdqu32 zmm13, ZMMWORD PTR [r11+192]
	vpclmulqdq zmm2, zmm15, zmm13, 0
	vpternlogd zmm8, zmm11, zmm2, 150
	vpclmulqdq zmm2, zmm15, zmm13, 17
	vpternlogd zmm10, zmm12, zmm2, 150
	vpclmulqdq zmm11, zmm15, zmm13, 1
	vpclmulqdq zmm2, zmm15, zmm13, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vaesenc zmm3, zmm3, zmm24
	vaesenc zmm4, zmm4, zmm24
	vaesenc zmm5, zmm5, zmm24
	vaesenc zmm6, zmm6, zmm24
	vaesenc zmm3, zmm3, zmm25
	vaesenc zmm4, zmm4, zmm25
	vaesenc zmm5, zmm5, zmm25
	vaesenc zmm6, zmm6, zmm25
	vmovdqu32 zmm1, ZMMWORD PTR [r11+832]
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vshufi32x4 zmm11, zmm10, zmm10, 14
	vpxor ymm10, ymm10, ymm11
	vextracti128 xmm11, ymm10, 1
	vpxor xmm2, xmm10, xmm11
	cmp rsi, 10
	je 262f
	vaesenc zmm3, zmm3, zmm26
	vaesenc zmm4, zmm4, zmm26
	vaesenc zmm5, zmm5, zmm26
	vaesenc zmm6, zmm6, zmm26
	vaesenc zmm3, zmm3, zmm27
	vaesenc zmm4, zmm4, zmm27
	vaesenc zmm5, zmm5, zmm27
	vaesenc zmm6, zmm6, zmm27
	cmp rsi, 12
	je 264f
	vaesenc zmm3, zmm3, zmm28
	vaesenc zmm4, zmm4, zmm28
	vaesenc zmm5, zmm5, zmm28
	vaesenc zmm6, zmm6, zmm28
	vaesenc zmm3, zmm3, zmm29
	vaesenc zmm4, zmm4, zmm29
	vaesenc zmm5, zmm5, zmm29
	vaesenc zmm6, zmm6, zmm29
	jmp 265f
264:
265:
	jmp 263f
262:
263:
	vaesenclast zmm3, zmm3, zmm31
	vaesenclast zmm4, zmm4, zmm31
	vaesenclast zmm5, zmm5, zmm31
	vaesenclast zmm6, zmm6, zmm31
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+256]
	vpxord zmm3, zmm3, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+256], zmm3
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+320]
	vpxord zmm4, zmm4, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+320], zmm4
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+384]
	vpxord zmm5, zmm5, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+384], zmm5
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+448]
	vpxord zmm6, zmm6, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+448], zmm6
	vpshufb zmm7, zmm3, zmm0
	vpshufb zmm1, zmm4, zmm0
	vpshufb zmm12, zmm5, zmm0
	vpshufb zmm15, zmm6, zmm0
	add rdx, 256
	sub r9, 16
	jmp 261f
260:
261:
	vmovdqu32 zmm1, ZMMWORD PTR [r11+832]
	vmovdqu32 zmm15, ZMMWORD PTR [r11+896]
213:
	jmp 211f
210:
211:
	cmp r9, 32
	jb 266f
268:
	vpshufb zmm3, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm4, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm5, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm6, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpxord zmm3, zmm3, zmm16
	vpxord zmm4, zmm4, zmm16
	vpxord zmm5, zmm5, zmm16
	vpxord zmm6, zmm6, zmm16
	vaesenc zmm3, zmm3, zmm17
	vaesenc zmm4, zmm4, zmm17
	vaesenc zmm5, zmm5, zmm17
	vaesenc zmm6, zmm6, zmm17
	vmovdqu32 zmm12, ZMMWORD PTR [r11+64]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+64]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm8, zmm7, zmm12, 0
	vpclmulqdq zmm10, zmm7, zmm12, 17
	vpclmulqdq zmm9, zmm7, zmm12, 1
	vpclmulqdq zmm11, zmm7, zmm12, 16
	vpxord zmm9, zmm9, zmm11
	vaesenc zmm3, zmm3, zmm18
	vaesenc zmm4, zmm4, zmm18
	vaesenc zmm5, zmm5, zmm18
	vaesenc zmm6, zmm6, zmm18
	vmovdqu32 zmm12, ZMMWORD PTR [r11+128]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+128]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vaesenc zmm3, zmm3, zmm19
	vaesenc zmm4, zmm4, zmm19
	vaesenc zmm5, zmm5, zmm19
	vaesenc zmm6, zmm6, zmm19
	vmovdqu32 zmm12, ZMMWORD PTR [r11+192]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+192]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vaesenc zmm3, zmm3, zmm20
	vaesenc zmm4, zmm4, zmm20
	vaesenc zmm5, zmm5, zmm20
	vaesenc zmm6, zmm6, zmm20
	vmovdqu32 zmm12, ZMMWORD PTR [r11]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx]
	vpshufb zmm7, zmm7, zmm0
	vpxord zmm7, zmm7, zmm2
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vaesenc zmm3, zmm3, zmm21
	vaesenc zmm4, zmm4, zmm21
	vaesenc zmm5, zmm5, zmm21
	vaesenc zmm6, zmm6, zmm21
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vshufi32x4 zmm11, zmm10, zmm10, 14
	vpxor ymm10, ymm10, ymm11
	vextracti128 xmm11, ymm10, 1
	vpxor xmm2, xmm10, xmm11
	vaesenc zmm3, zmm3, zmm22
	vaesenc zmm4, zmm4, zmm22
	vaesenc zmm5, zmm5, zmm22
	vaesenc zmm6, zmm6, zmm22
	vaesenc zmm3, zmm3, zmm23
	vaesenc zmm4, zmm4, zmm23
	vaesenc zmm5, zmm5, zmm23
	vaesenc zmm6, zmm6, zmm23
	vaesenc zmm3, zmm3, zmm24
	vaesenc zmm4, zmm4, zmm24
	vaesenc zmm5, zmm5, zmm24
	vaesenc zmm6, zmm6, zmm24
	vaesenc zmm3, zmm3, zmm25
	vaesenc zmm4, zmm4, zmm25
	vaesenc zmm5, zmm5, zmm25
	vaesenc zmm6, zmm6, zmm25
	cmp rsi, 10
	je 269f
	vaesenc zmm3, zmm3, zmm26
	vaesenc zmm4, zmm4, zmm26
	vaesenc zmm5, zmm5, zmm26
	vaesenc zmm6, zmm6, zmm26
	vaesenc zmm3, zmm3, zmm27
	vaesenc zmm4, zmm4, zmm27
	vaesenc zmm5, zmm5, zmm27
	vaesenc zmm6, zmm6, zmm27
	cmp rsi, 12
	je 271f
	vaesenc zmm3, zmm3, zmm28
	vaesenc zmm4, zmm4, zmm28
	vaesenc zmm5, zmm5, zmm28
	vaesenc zmm6, zmm6, zmm28
	vaesenc zmm3, zmm3, zmm29
	vaesenc zmm4, zmm4, zmm29
	vaesenc zmm5, zmm5, zmm29
	vaesenc zmm6, zmm6, zmm29
	jmp 272f
271:
272:
	jmp 270f
269:
270:
	vaesenclast zmm3, zmm3, zmm31
	vaesenclast zmm4, zmm4, zmm31
	vaesenclast zmm5, zmm5, zmm31
	vaesenclast zmm6, zmm6, zmm31
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+256]
	vpxord zmm3, zmm3, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+256], zmm3
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+320]
	vpxord zmm4, zmm4, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+320], zmm4
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+384]
	vpxord zmm5, zmm5, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+384], zmm5
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+448]
	vpxord zmm6, zmm6, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+448], zmm6
	add rdx, 256
	sub r9, 16
	cmp r9, 32
	jae 268b
	jmp 267f
266:
267:
	cmp r9, 16
	je 273f
	mov r10, r9
	sub r10, 16
	vmovq xmm13, r10
	vpaddd xmm13, xmm14, xmm13
	vpshufb xmm13, xmm13, xmm0
	vmovdqu XMMWORD PTR [rax], xmm13
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	mov rax, r11
	add rax, 256
	sub rax, r10
	cmp r10, 65
	jb 275f
	cmp r10, 129
	jb 277f
	cmp r10, 193
	jb 279f
	vpshufb zmm3, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm4, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm5, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm6, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpxord zmm3, zmm3, zmm16
	vpxord zmm4, zmm4, zmm16
	vpxord zmm5, zmm5, zmm16
	vpxord zmm6, zmm6, zmm16
	vaesenc zmm3, zmm3, zmm17
	vaesenc zmm4, zmm4, zmm17
	vaesenc zmm5, zmm5, zmm17
	vaesenc zmm6, zmm6, zmm17
	vmovdqu32 zmm12, ZMMWORD PTR [r11+64]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+64]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm8, zmm7, zmm12, 0
	vpclmulqdq zmm10, zmm7, zmm12, 17
	vpclmulqdq zmm9, zmm7, zmm12, 1
	vpclmulqdq zmm11, zmm7, zmm12, 16
	vpxord zmm9, zmm9, zmm11
	vaesenc zmm3, zmm3, zmm18
	vaesenc zmm4, zmm4, zmm18
	vaesenc zmm5, zmm5, zmm18
	vaesenc zmm6, zmm6, zmm18
	vmovdqu32 zmm12, ZMMWORD PTR [r11+128]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+128]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vaesenc zmm3, zmm3, zmm19
	vaesenc zmm4, zmm4, zmm19
	vaesenc zmm5, zmm5, zmm19
	vaesenc zmm6, zmm6, zmm19
	vmovdqu32 zmm12, ZMMWORD PTR [r11+192]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+192]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vaesenc zmm3, zmm3, zmm20
	vaesenc zmm4, zmm4, zmm20
	vaesenc zmm5, zmm5, zmm20
	vaesenc zmm6, zmm6, zmm20
	vmovdqu32 zmm12, ZMMWORD PTR [r11]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx]
	vpshufb zmm7, zmm7, zmm0
	vpxord zmm7, zmm7, zmm2
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vaesenc zmm3, zmm3, zmm21
	vaesenc zmm4, zmm4, zmm21
	vaesenc zmm5, zmm5, zmm21
	vaesenc zmm6, zmm6, zmm21
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vshufi32x4 zmm11, zmm10, zmm10, 14
	vpxor ymm10, ymm10, ymm11
	vextracti128 xmm11, ymm10, 1
	vpxor xmm2, xmm10, xmm11
	vaesenc zmm3, zmm3, zmm22
	vaesenc zmm4, zmm4, zmm22
	vaesenc zmm5, zmm5, zmm22
	vaesenc zmm6, zmm6, zmm22
	vaesenc zmm3, zmm3, zmm23
	vaesenc zmm4, zmm4, zmm23
	vaesenc zmm5, zmm5, zmm23
	vaesenc zmm6, zmm6, zmm23
	vaesenc zmm3, zmm3, zmm24
	vaesenc zmm4, zmm4, zmm24
	vaesenc zmm5, zmm5, zmm24
	vaesenc zmm6, zmm6, zmm24
	vaesenc zmm3, zmm3, zmm25
	vaesenc zmm4, zmm4, zmm25
	vaesenc zmm5, zmm5, zmm25
	vaesenc zmm6, zmm6, zmm25
	cmp rsi, 10
	je 281f
	vaesenc zmm3, zmm3, zmm26
	vaesenc zmm4, zmm4, zmm26
	vaesenc zmm5, zmm5, zmm26
	vaesenc zmm6, zmm6, zmm26
	vaesenc zmm3, zmm3, zmm27
	vaesenc zmm4, zmm4, zmm27
	vaesenc zmm5, zmm5, zmm27
	vaesenc zmm6, zmm6, zmm27
	cmp rsi, 12
	je 283f
	vaesenc zmm3, zmm3, zmm28
	vaesenc zmm4, zmm4, zmm28
	vaesenc zmm5, zmm5, zmm28
	vaesenc zmm6, zmm6, zmm28
	vaesenc zmm3, zmm3, zmm29
	vaesenc zmm4, zmm4, zmm29
	vaesenc zmm5, zmm5, zmm29
	vaesenc zmm6, zmm6, zmm29
	jmp 284f
283:
284:
	jmp 282f
281:
282:
	vaesenclast zmm3, zmm3, zmm31
	vaesenclast zmm4, zmm4, zmm31
	vaesenclast zmm5, zmm5, zmm31
	vaesenclast zmm6, zmm6, zmm31
	add rdx, 256
	add r8, rdx
	test r9, 1
	je 285f
	test r9, 2
	je 287f
	mov r10d, 63
	jmp 288f
287:
	mov r10d, 3
288:
	jmp 286f
285:
	test r9, 2
	je 289f
	mov r10d, 15
	jmp 290f
289:
	mov r10d, 255
290:
286:
	vmovdqu32 zmm13, ZMMWORD PTR [r8]
	vpxord zmm3, zmm3, zmm13
	vmovdqu32 ZMMWORD PTR [rdx], zmm3
	vmovdqu32 zmm13, ZMMWORD PTR [r8+64]
	vpxord zmm4, zmm4, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+64], zmm4
	vmovdqu32 zmm13, ZMMWORD PTR [r8+128]
	vpxord zmm5, zmm5, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+128], zmm5
	kmovw k1, r10d
	vmovdqu64 zmm13 {k1}{z}, ZMMWORD PTR [r8+192]
	vpxord zmm6, zmm6, zmm13
	kmovw k1, r10d
	vmovdqu64 ZMMWORD PTR [rdx+192] {k1}, zmm6
	vmovdqu32 zmm12, ZMMWORD PTR [rax]
	vpshufb zmm7, zmm3, zmm0
	vpxord zmm7, zmm7, zmm2
	vpclmulqdq zmm8, zmm7, zmm12, 0
	vpclmulqdq zmm10, zmm7, zmm12, 17
	vpclmulqdq zmm9, zmm7, zmm12, 1
	vpclmulqdq zmm11, zmm7, zmm12, 16
	vpxord zmm9, zmm9, zmm11
	vmovdqu32 zmm12, ZMMWORD PTR [rax+64]
	vpshufb zmm7, zmm4, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vmovdqu32 zmm12, ZMMWORD PTR [rax+128]
	vpshufb zmm7, zmm5, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	kmovw k1, r10d
	vmovdqu64 zmm12 {k1}{z}, ZMMWORD PTR [rax+192]
	vpshufb zmm7, zmm6, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vshufi32x4 zmm11, zmm10, zmm10, 14
	vpxor ymm10, ymm10, ymm11
	vextracti128 xmm11, ymm10, 1
	vpxor xmm2, xmm10, xmm11
	jmp 280f
279:
	vpshufb zmm3, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm4, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm5, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpxord zmm3, zmm3, zmm16
	vpxord zmm4, zmm4, zmm16
	vpxord zmm5, zmm5, zmm16
	vaesenc zmm3, zmm3, zmm17
	vaesenc zmm4, zmm4, zmm17
	vaesenc zmm5, zmm5, zmm17
	vmovdqu32 zmm12, ZMMWORD PTR [r11+64]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+64]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm8, zmm7, zmm12, 0
	vpclmulqdq zmm10, zmm7, zmm12, 17
	vpclmulqdq zmm9, zmm7, zmm12, 1
	vpclmulqdq zmm11, zmm7, zmm12, 16
	vpxord zmm9, zmm9, zmm11
	vaesenc zmm3, zmm3, zmm18
	vaesenc zmm4, zmm4, zmm18
	vaesenc zmm5, zmm5, zmm18
	vmovdqu32 zmm12, ZMMWORD PTR [r11+128]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+128]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vaesenc zmm3, zmm3, zmm19
	vaesenc zmm4, zmm4, zmm19
	vaesenc zmm5, zmm5, zmm19
	vmovdqu32 zmm12, ZMMWORD PTR [r11+192]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+192]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vaesenc zmm3, zmm3, zmm20
	vaesenc zmm4, zmm4, zmm20
	vaesenc zmm5, zmm5, zmm20
	vmovdqu32 zmm12, ZMMWORD PTR [r11]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx]
	vpshufb zmm7, zmm7, zmm0
	vpxord zmm7, zmm7, zmm2
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vaesenc zmm3, zmm3, zmm21
	vaesenc zmm4, zmm4, zmm21
	vaesenc zmm5, zmm5, zmm21
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vshufi32x4 zmm11, zmm10, zmm10, 14
	vpxor ymm10, ymm10, ymm11
	vextracti128 xmm11, ymm10, 1
	vpxor xmm2, xmm10, xmm11
	vaesenc zmm3, zmm3, zmm22
	vaesenc zmm4, zmm4, zmm22
	vaesenc zmm5, zmm5, zmm22
	vaesenc zmm3, zmm3, zmm23
	vaesenc zmm4, zmm4, zmm23
	vaesenc zmm5, zmm5, zmm23
	vaesenc zmm3, zmm3, zmm24
	vaesenc zmm4, zmm4, zmm24
	vaesenc zmm5, zmm5, zmm24
	vaesenc zmm3, zmm3, zmm25
	vaesenc zmm4, zmm4, zmm25
	vaesenc zmm5, zmm5, zmm25
	cmp rsi, 10
	je 291f
	vaesenc zmm3, zmm3, zmm26
	vaesenc zmm4, zmm4, zmm26
	vaesenc zmm5, zmm5, zmm26
	vaesenc zmm3, zmm3, zmm27
	vaesenc zmm4, zmm4, zmm27
	vaesenc zmm5, zmm5, zmm27
	cmp rsi, 12
	je 293f
	vaesenc zmm3, zmm3, zmm28
	vaesenc zmm4, zmm4, zmm28
	vaesenc zmm5, zmm5, zmm28
	vaesenc zmm3, zmm3, zmm29
	vaesenc zmm4, zmm4, zmm29
	vaesenc zmm5, zmm5, zmm29
	jmp 294f
293:
294:
	jmp 292f
291:
292:
	vaesenclast zmm3, zmm3, zmm31
	vaesenclast zmm4, zmm4, zmm31
	vaesenclast zmm5, zmm5, zmm31
	add rdx, 256
	add r8, rdx
	test r9, 1
	je 295f
	test r9, 2
	je 297f
	mov r10d, 63
	jmp 298f
297:
	mov r10d, 3
298:
	jmp 296f
295:
	test r9, 2
	je 299f
	mov r10d, 15
	jmp 2100f
299:
	mov r10d, 255
2100:
296:
	vmovdqu32 zmm13, ZMMWORD PTR [r8]
	vpxord zmm3, zmm3, zmm13
	vmovdqu32 ZMMWORD PTR [rdx], zmm3
	vmovdqu32 zmm13, ZMMWORD PTR [r8+64]
	vpxord zmm4, zmm4, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+64], zmm4
	kmovw k1, r10d
	vmovdqu64 zmm13 {k1}{z}, ZMMWORD PTR [r8+128]
	vpxord zmm5, zmm5, zmm13
	kmovw k1, r10d
	vmovdqu64 ZMMWORD PTR [rdx+128] {k1}, zmm5
	vmovdqu32 zmm12, ZMMWORD PTR [rax]
	vpshufb zmm7, zmm3, zmm0
	vpxord zmm7, zmm7, zmm2
	vpclmulqdq zmm8, zmm7, zmm12, 0
	vpclmulqdq zmm10, zmm7, zmm12, 17
	vpclmulqdq zmm9, zmm7, zmm12, 1
	vpclmulqdq zmm11, zmm7, zmm12, 16
	vpxord zmm9, zmm9, zmm11
	vmovdqu32 zmm12, ZMMWORD PTR [rax+64]
	vpshufb zmm7, zmm4, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	kmovw k1, r10d
	vmovdqu64 zmm12 {k1}{z}, ZMMWORD PTR [rax+128]
	vpshufb zmm7, zmm5, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vshufi32x4 zmm11, zmm10, zmm10, 14
	vpxor ymm10, ymm10, ymm11
	vextracti128 xmm11, ymm10, 1
	vpxor xmm2, xmm10, xmm11
280:
	jmp 278f
277:
	vpshufb zmm3, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm4, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpxord zmm3, zmm3, zmm16
	vpxord zmm4, zmm4, zmm16
	vaesenc zmm3, zmm3, zmm17
	vaesenc zmm4, zmm4, zmm17
	vmovdqu32 zmm12, ZMMWORD PTR [r11+64]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+64]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm8, zmm7, zmm12, 0
	vpclmulqdq zmm10, zmm7, zmm12, 17
	vpclmulqdq zmm9, zmm7, zmm12, 1
	vpclmulqdq zmm11, zmm7, zmm12, 16
	vpxord zmm9, zmm9, zmm11
	vaesenc zmm3, zmm3, zmm18
	vaesenc zmm4, zmm4, zmm18
	vmovdqu32 zmm12, ZMMWORD PTR [r11+128]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+128]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vaesenc zmm3, zmm3, zmm19
	vaesenc zmm4, zmm4, zmm19
	vmovdqu32 zmm12, ZMMWORD PTR [r11+192]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+192]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vaesenc zmm3, zmm3, zmm20
	vaesenc zmm4, zmm4, zmm20
	vmovdqu32 zmm12, ZMMWORD PTR [r11]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx]
	vpshufb zmm7, zmm7, zmm0
	vpxord zmm7, zmm7, zmm2
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vaesenc zmm3, zmm3, zmm21
	vaesenc zmm4, zmm4, zmm21
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vshufi32x4 zmm11, zmm10, zmm10, 14
	vpxor ymm10, ymm10, ymm11
	vextracti128 xmm11, ymm10, 1
	vpxor xmm2, xmm10, xmm11
	vaesenc zmm3, zmm3, zmm22
	vaesenc zmm4, zmm4, zmm22
	vaesenc zmm3, zmm3, zmm23
	vaesenc zmm4, zmm4, zmm23
	vaesenc zmm3, zmm3, zmm24
	vaesenc zmm4, zmm4, zmm24
	vaesenc zmm3, zmm3, zmm25
	vaesenc zmm4, zmm4, zmm25
	cmp rsi, 10
	je 2101f
	vaesenc zmm3, zmm3, zmm26
	vaesenc zmm4, zmm4, zmm26
	vaesenc zmm3, zmm3, zmm27
	vaesenc zmm4, zmm4, zmm27
	cmp rsi, 12
	je 2103f
	vaesenc zmm3, zmm3, zmm28
	vaesenc zmm4, zmm4, zmm28
	vaesenc zmm3, zmm3, zmm29
	vaesenc zmm4, zmm4, zmm29
	jmp 2104f
2103:
2104:
	jmp 2102f
2101:
2102:
	vaesenclast zmm3, zmm3, zmm31
	vaesenclast zmm4, zmm4, zmm31
	add rdx, 256
	add r8, rdx
	test r9, 1
	je 2105f
	test r9, 2
	je 2107f
	mov r10d, 63
	jmp 2108f
2107:
	mov r10d, 3
2108:
	jmp 2106f
2105:
	test r9, 2
	je 2109f
	mov r10d, 15
	jmp 2110f
2109:
	mov r10d, 255
2110:
2106:
	vmovdqu32 zmm13, ZMMWORD PTR [r8]
	vpxord zmm3, zmm3, zmm13
	vmovdqu32 ZMMWORD PTR [rdx], zmm3
	kmovw k1, r10d
	vmovdqu64 zmm13 {k1}{z}, ZMMWORD PTR [r8+64]
	vpxord zmm4, zmm4, zmm13
	kmovw k1, r10d
	vmovdqu64 ZMMWORD PTR [rdx+64] {k1}, zmm4
	vmovdqu32 zmm12, ZMMWORD PTR [rax]
	vpshufb zmm7, zmm3, zmm0
	vpxord zmm7, zmm7, zmm2
	vpclmulqdq zmm8, zmm7, zmm12, 0
	vpclmulqdq zmm10, zmm7, zmm12, 17
	vpclmulqdq zmm9, zmm7, zmm12, 1
	vpclmulqdq zmm11, zmm7, zmm12, 16
	vpxord zmm9, zmm9, zmm11
	kmovw k1, r10d
	vmovdqu64 zmm12 {k1}{z}, ZMMWORD PTR [rax+64]
	vpshufb zmm7, zmm4, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vshufi32x4 zmm11, zmm10, zmm10, 14
	vpxor ymm10, ymm10, ymm11
	vextracti128 xmm11, ymm10, 1
	vpxor xmm2, xmm10, xmm11
278:
	jmp 276f
275:
	vpshufb zmm3, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpxord zmm3, zmm3, zmm16
	vaesenc zmm3, zmm3, zmm17
	vmovdqu32 zmm12, ZMMWORD PTR [r11+64]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+64]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm8, zmm7, zmm12, 0
	vpclmulqdq zmm10, zmm7, zmm12, 17
	vpclmulqdq zmm9, zmm7, zmm12, 1
	vpclmulqdq zmm11, zmm7, zmm12, 16
	vpxord zmm9, zmm9, zmm11
	vaesenc zmm3, zmm3, zmm18
	vmovdqu32 zmm12, ZMMWORD PTR [r11+128]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+128]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vaesenc zmm3, zmm3, zmm19
	vmovdqu32 zmm12, ZMMWORD PTR [r11+192]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+192]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vaesenc zmm3, zmm3, zmm20
	vmovdqu32 zmm12, ZMMWORD PTR [r11]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx]
	vpshufb zmm7, zmm7, zmm0
	vpxord zmm7, zmm7, zmm2
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vaesenc zmm3, zmm3, zmm21
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vshufi32x4 zmm11, zmm10, zmm10, 14
	vpxor ymm10, ymm10, ymm11
	vextracti128 xmm11, ymm10, 1
	vpxor xmm2, xmm10, xmm11
	vaesenc zmm3, zmm3, zmm22
	vaesenc zmm3, zmm3, zmm23
	vaesenc zmm3, zmm3, zmm24
	vaesenc zmm3, zmm3, zmm25
	cmp rsi, 10
	je 2111f
	vaesenc zmm3, zmm3, zmm26
	vaesenc zmm3, zmm3, zmm27
	cmp rsi, 12
	je 2113f
	vaesenc zmm3, zmm3, zmm28
	vaesenc zmm3, zmm3, zmm29
	jmp 2114f
2113:
2114:
	jmp 2112f
2111:
2112:
	vaesenclast zmm3, zmm3, zmm31
	add rdx, 256
	add r8, rdx
	test r9, 1
	je 2115f
	test r9, 2
	je 2117f
	mov r10d, 63
	jmp 2118f
2117:
	mov r10d, 3
2118:
	jmp 2116f
2115:
	test r9, 2
	je 2119f
	mov r10d, 15
	jmp 2120f
2119:
	mov r10d, 255
2120:
2116:
	kmovw k1, r10d
	vmovdqu64 zmm13 {k1}{z}, ZMMWORD PTR [r8]
	vpxord zmm3, zmm3, zmm13
	kmovw k1, r10d
	vmovdqu64 ZMMWORD PTR [rdx] {k1}, zmm3
	kmovw k1, r10d
	vmovdqu64 zmm12 {k1}{z}, ZMMWORD PTR [rax]
	vpshufb zmm7, zmm3, zmm0
	vpxord zmm7, zmm7, zmm2
	vpclmulqdq zmm8, zmm7, zmm12, 0
	vpclmulqdq zmm10, zmm7, zmm12, 17
	vpclmulqdq zmm9, zmm7, zmm12, 1
	vpclmulqdq zmm11, zmm7, zmm12, 16
	vpxord zmm9, zmm9, zmm11
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vshufi32x4 zmm11, zmm10, zmm10, 14
	vpxor ymm10, ymm10, ymm11
	vextracti128 xmm11, ymm10, 1
	vpxor xmm2, xmm10, xmm11
276:
	vpshufb xmm2, xmm2, xmm0
	vmovdqu XMMWORD PTR [rcx], xmm2
	vzeroupper
	jmp 274f
273:
	vpshufb xmm13, xmm14, xmm0
	vmovdqu XMMWORD PTR [rax], xmm13
	vmovdqu32 zmm12, ZMMWORD PTR [r11+64]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+64]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm8, zmm7, zmm12, 0
	vpclmulqdq zmm10, zmm7, zmm12, 17
	vpclmulqdq zmm9, zmm7, zmm12, 1
	vpclmulqdq zmm11, zmm7, zmm12, 16
	vpxord zmm9, zmm9, zmm11
	vmovdqu32 zmm12, ZMMWORD PTR [r11+128]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+128]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vmovdqu32 zmm12, ZMMWORD PTR [r11+192]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+192]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vmovdqu32 zmm12, ZMMWORD PTR [r11]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx]
	vpshufb zmm7, zmm7, zmm0
	vpxord zmm7, zmm7, zmm2
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vshufi32x4 zmm11, zmm10, zmm10, 14
	vpxor ymm10, ymm10, ymm11
	vextracti128 xmm11, ymm10, 1
	vpxor xmm2, xmm10, xmm11
	vpshufb xmm2, xmm2, xmm0
	vmovdqu XMMWORD PTR [rcx], xmm2
	vzeroupper
274:
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
	je 2121f
	mov rsi, QWORD PTR [r11+32]
	mov rdi, QWORD PTR [r11+48]
	mov r10d, 0
2123:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	sub rcx, 1
	jne 2123b
	mov r11, QWORD PTR [rsp+24]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, QWORD PTR [r11+16]
	mov rcx, QWORD PTR [r11+24]
	mov r8, QWORD PTR [r11+48]
	mov r9, QWORD PTR [r11+40]
	mov rax, r11
	push rax
	call {vg_aes_gcm_encrypt_blocks_prepared_vaes_vpclmul_avx512}
	pop rax
	jmp 2122f
2121:
2122:
	ret
	.p2align 6
