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
	cmp r9, 144
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
	je 212f
	vaesenc zmm3, zmm3, zmm26
	vaesenc zmm4, zmm4, zmm26
	vaesenc zmm5, zmm5, zmm26
	vaesenc zmm6, zmm6, zmm26
	vaesenc zmm3, zmm3, zmm27
	vaesenc zmm4, zmm4, zmm27
	vaesenc zmm5, zmm5, zmm27
	vaesenc zmm6, zmm6, zmm27
	cmp rsi, 12
	je 214f
	vaesenc zmm3, zmm3, zmm28
	vaesenc zmm4, zmm4, zmm28
	vaesenc zmm5, zmm5, zmm28
	vaesenc zmm6, zmm6, zmm28
	vaesenc zmm3, zmm3, zmm29
	vaesenc zmm4, zmm4, zmm29
	vaesenc zmm5, zmm5, zmm29
	vaesenc zmm6, zmm6, zmm29
	jmp 215f
214:
215:
	jmp 213f
212:
213:
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
	je 216f
	vaesenc zmm3, zmm3, zmm26
	vaesenc zmm4, zmm4, zmm26
	vaesenc zmm5, zmm5, zmm26
	vaesenc zmm6, zmm6, zmm26
	vaesenc zmm3, zmm3, zmm27
	vaesenc zmm4, zmm4, zmm27
	vaesenc zmm5, zmm5, zmm27
	vaesenc zmm6, zmm6, zmm27
	cmp rsi, 12
	je 218f
	vaesenc zmm3, zmm3, zmm28
	vaesenc zmm4, zmm4, zmm28
	vaesenc zmm5, zmm5, zmm28
	vaesenc zmm6, zmm6, zmm28
	vaesenc zmm3, zmm3, zmm29
	vaesenc zmm4, zmm4, zmm29
	vaesenc zmm5, zmm5, zmm29
	vaesenc zmm6, zmm6, zmm29
	jmp 219f
218:
219:
	jmp 217f
216:
217:
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
220:
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
	je 221f
	vaesenc zmm3, zmm3, zmm26
	vaesenc zmm4, zmm4, zmm26
	vaesenc zmm5, zmm5, zmm26
	vaesenc zmm6, zmm6, zmm26
	vaesenc zmm3, zmm3, zmm27
	vaesenc zmm4, zmm4, zmm27
	vaesenc zmm5, zmm5, zmm27
	vaesenc zmm6, zmm6, zmm27
	cmp rsi, 12
	je 223f
	vaesenc zmm3, zmm3, zmm28
	vaesenc zmm4, zmm4, zmm28
	vaesenc zmm5, zmm5, zmm28
	vaesenc zmm6, zmm6, zmm28
	vaesenc zmm3, zmm3, zmm29
	vaesenc zmm4, zmm4, zmm29
	vaesenc zmm5, zmm5, zmm29
	vaesenc zmm6, zmm6, zmm29
	jmp 224f
223:
224:
	jmp 222f
221:
222:
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
	je 225f
	vaesenc zmm3, zmm3, zmm26
	vaesenc zmm4, zmm4, zmm26
	vaesenc zmm5, zmm5, zmm26
	vaesenc zmm6, zmm6, zmm26
	vaesenc zmm3, zmm3, zmm27
	vaesenc zmm4, zmm4, zmm27
	vaesenc zmm5, zmm5, zmm27
	vaesenc zmm6, zmm6, zmm27
	cmp rsi, 12
	je 227f
	vaesenc zmm3, zmm3, zmm28
	vaesenc zmm4, zmm4, zmm28
	vaesenc zmm5, zmm5, zmm28
	vaesenc zmm6, zmm6, zmm28
	vaesenc zmm3, zmm3, zmm29
	vaesenc zmm4, zmm4, zmm29
	vaesenc zmm5, zmm5, zmm29
	vaesenc zmm6, zmm6, zmm29
	jmp 228f
227:
228:
	jmp 226f
225:
226:
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
	je 229f
	vaesenc zmm3, zmm3, zmm26
	vaesenc zmm4, zmm4, zmm26
	vaesenc zmm5, zmm5, zmm26
	vaesenc zmm6, zmm6, zmm26
	vaesenc zmm3, zmm3, zmm27
	vaesenc zmm4, zmm4, zmm27
	vaesenc zmm5, zmm5, zmm27
	vaesenc zmm6, zmm6, zmm27
	cmp rsi, 12
	je 231f
	vaesenc zmm3, zmm3, zmm28
	vaesenc zmm4, zmm4, zmm28
	vaesenc zmm5, zmm5, zmm28
	vaesenc zmm6, zmm6, zmm28
	vaesenc zmm3, zmm3, zmm29
	vaesenc zmm4, zmm4, zmm29
	vaesenc zmm5, zmm5, zmm29
	vaesenc zmm6, zmm6, zmm29
	jmp 232f
231:
232:
	jmp 230f
229:
230:
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
	jae 220b
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
	jmp 211f
210:
211:
	cmp r9, 32
	jb 233f
235:
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
	je 236f
	vaesenc zmm3, zmm3, zmm26
	vaesenc zmm4, zmm4, zmm26
	vaesenc zmm5, zmm5, zmm26
	vaesenc zmm6, zmm6, zmm26
	vaesenc zmm3, zmm3, zmm27
	vaesenc zmm4, zmm4, zmm27
	vaesenc zmm5, zmm5, zmm27
	vaesenc zmm6, zmm6, zmm27
	cmp rsi, 12
	je 238f
	vaesenc zmm3, zmm3, zmm28
	vaesenc zmm4, zmm4, zmm28
	vaesenc zmm5, zmm5, zmm28
	vaesenc zmm6, zmm6, zmm28
	vaesenc zmm3, zmm3, zmm29
	vaesenc zmm4, zmm4, zmm29
	vaesenc zmm5, zmm5, zmm29
	vaesenc zmm6, zmm6, zmm29
	jmp 239f
238:
239:
	jmp 237f
236:
237:
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
	jae 235b
	jmp 234f
233:
234:
	cmp r9, 16
	je 240f
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
	jb 242f
	cmp r10, 129
	jb 244f
	cmp r10, 193
	jb 246f
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
	je 248f
	vaesenc zmm3, zmm3, zmm26
	vaesenc zmm4, zmm4, zmm26
	vaesenc zmm5, zmm5, zmm26
	vaesenc zmm6, zmm6, zmm26
	vaesenc zmm3, zmm3, zmm27
	vaesenc zmm4, zmm4, zmm27
	vaesenc zmm5, zmm5, zmm27
	vaesenc zmm6, zmm6, zmm27
	cmp rsi, 12
	je 250f
	vaesenc zmm3, zmm3, zmm28
	vaesenc zmm4, zmm4, zmm28
	vaesenc zmm5, zmm5, zmm28
	vaesenc zmm6, zmm6, zmm28
	vaesenc zmm3, zmm3, zmm29
	vaesenc zmm4, zmm4, zmm29
	vaesenc zmm5, zmm5, zmm29
	vaesenc zmm6, zmm6, zmm29
	jmp 251f
250:
251:
	jmp 249f
248:
249:
	vaesenclast zmm3, zmm3, zmm31
	vaesenclast zmm4, zmm4, zmm31
	vaesenclast zmm5, zmm5, zmm31
	vaesenclast zmm6, zmm6, zmm31
	add rdx, 256
	add r8, rdx
	test r9, 1
	je 252f
	test r9, 2
	je 254f
	mov r10d, 63
	jmp 255f
254:
	mov r10d, 3
255:
	jmp 253f
252:
	test r9, 2
	je 256f
	mov r10d, 15
	jmp 257f
256:
	mov r10d, 255
257:
253:
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
	jmp 247f
246:
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
	je 258f
	vaesenc zmm3, zmm3, zmm26
	vaesenc zmm4, zmm4, zmm26
	vaesenc zmm5, zmm5, zmm26
	vaesenc zmm3, zmm3, zmm27
	vaesenc zmm4, zmm4, zmm27
	vaesenc zmm5, zmm5, zmm27
	cmp rsi, 12
	je 260f
	vaesenc zmm3, zmm3, zmm28
	vaesenc zmm4, zmm4, zmm28
	vaesenc zmm5, zmm5, zmm28
	vaesenc zmm3, zmm3, zmm29
	vaesenc zmm4, zmm4, zmm29
	vaesenc zmm5, zmm5, zmm29
	jmp 261f
260:
261:
	jmp 259f
258:
259:
	vaesenclast zmm3, zmm3, zmm31
	vaesenclast zmm4, zmm4, zmm31
	vaesenclast zmm5, zmm5, zmm31
	add rdx, 256
	add r8, rdx
	test r9, 1
	je 262f
	test r9, 2
	je 264f
	mov r10d, 63
	jmp 265f
264:
	mov r10d, 3
265:
	jmp 263f
262:
	test r9, 2
	je 266f
	mov r10d, 15
	jmp 267f
266:
	mov r10d, 255
267:
263:
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
247:
	jmp 245f
244:
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
	je 268f
	vaesenc zmm3, zmm3, zmm26
	vaesenc zmm4, zmm4, zmm26
	vaesenc zmm3, zmm3, zmm27
	vaesenc zmm4, zmm4, zmm27
	cmp rsi, 12
	je 270f
	vaesenc zmm3, zmm3, zmm28
	vaesenc zmm4, zmm4, zmm28
	vaesenc zmm3, zmm3, zmm29
	vaesenc zmm4, zmm4, zmm29
	jmp 271f
270:
271:
	jmp 269f
268:
269:
	vaesenclast zmm3, zmm3, zmm31
	vaesenclast zmm4, zmm4, zmm31
	add rdx, 256
	add r8, rdx
	test r9, 1
	je 272f
	test r9, 2
	je 274f
	mov r10d, 63
	jmp 275f
274:
	mov r10d, 3
275:
	jmp 273f
272:
	test r9, 2
	je 276f
	mov r10d, 15
	jmp 277f
276:
	mov r10d, 255
277:
273:
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
245:
	jmp 243f
242:
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
	je 278f
	vaesenc zmm3, zmm3, zmm26
	vaesenc zmm3, zmm3, zmm27
	cmp rsi, 12
	je 280f
	vaesenc zmm3, zmm3, zmm28
	vaesenc zmm3, zmm3, zmm29
	jmp 281f
280:
281:
	jmp 279f
278:
279:
	vaesenclast zmm3, zmm3, zmm31
	add rdx, 256
	add r8, rdx
	test r9, 1
	je 282f
	test r9, 2
	je 284f
	mov r10d, 63
	jmp 285f
284:
	mov r10d, 3
285:
	jmp 283f
282:
	test r9, 2
	je 286f
	mov r10d, 15
	jmp 287f
286:
	mov r10d, 255
287:
283:
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
243:
	vpshufb xmm2, xmm2, xmm0
	vmovdqu XMMWORD PTR [rcx], xmm2
	vzeroupper
	jmp 241f
240:
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
241:
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
	je 288f
	mov rsi, QWORD PTR [r11+32]
	mov rdi, QWORD PTR [r11+48]
	mov r10d, 0
290:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	sub rcx, 1
	jne 290b
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
	jmp 289f
288:
289:
	ret
	.p2align 6
