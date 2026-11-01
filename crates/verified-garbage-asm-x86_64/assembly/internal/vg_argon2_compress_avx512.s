// The functions of `src/internal/vg_argon2_compress_avx512.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_argon2_compress_avx512:
	stmxcsr DWORD PTR [rcx+2048]
	mov r11d, DWORD PTR [rcx+2048]
	and r11d, 65535
	mov eax, 8127
	mov DWORD PTR [rcx+2052], eax
	ldmxcsr DWORD PTR [rcx+2052]
	lfence
	vmovdqu32 zmm0, ZMMWORD PTR [rdi]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi]
	vpxord zmm0, zmm0, zmm1
	vmovdqu32 ZMMWORD PTR [rcx], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rdi+64]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+64]
	vpxord zmm0, zmm0, zmm1
	vmovdqu32 ZMMWORD PTR [rcx+64], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rdi+128]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+128]
	vpxord zmm0, zmm0, zmm1
	vmovdqu32 ZMMWORD PTR [rcx+128], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rdi+192]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+192]
	vpxord zmm0, zmm0, zmm1
	vmovdqu32 ZMMWORD PTR [rcx+192], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rdi+256]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+256]
	vpxord zmm0, zmm0, zmm1
	vmovdqu32 ZMMWORD PTR [rcx+256], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rdi+320]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+320]
	vpxord zmm0, zmm0, zmm1
	vmovdqu32 ZMMWORD PTR [rcx+320], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rdi+384]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+384]
	vpxord zmm0, zmm0, zmm1
	vmovdqu32 ZMMWORD PTR [rcx+384], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rdi+448]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+448]
	vpxord zmm0, zmm0, zmm1
	vmovdqu32 ZMMWORD PTR [rcx+448], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rdi+512]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+512]
	vpxord zmm0, zmm0, zmm1
	vmovdqu32 ZMMWORD PTR [rcx+512], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rdi+576]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+576]
	vpxord zmm0, zmm0, zmm1
	vmovdqu32 ZMMWORD PTR [rcx+576], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rdi+640]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+640]
	vpxord zmm0, zmm0, zmm1
	vmovdqu32 ZMMWORD PTR [rcx+640], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rdi+704]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+704]
	vpxord zmm0, zmm0, zmm1
	vmovdqu32 ZMMWORD PTR [rcx+704], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rdi+768]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+768]
	vpxord zmm0, zmm0, zmm1
	vmovdqu32 ZMMWORD PTR [rcx+768], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rdi+832]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+832]
	vpxord zmm0, zmm0, zmm1
	vmovdqu32 ZMMWORD PTR [rcx+832], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rdi+896]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+896]
	vpxord zmm0, zmm0, zmm1
	vmovdqu32 ZMMWORD PTR [rcx+896], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rdi+960]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+960]
	vpxord zmm0, zmm0, zmm1
	vmovdqu32 ZMMWORD PTR [rcx+960], zmm0
	vmovdqu32 zmm4, ZMMWORD PTR [rcx]
	vmovdqu32 zmm5, ZMMWORD PTR [rcx+64]
	vmovdqu32 zmm6, ZMMWORD PTR [rcx+128]
	vmovdqu32 zmm7, ZMMWORD PTR [rcx+192]
	vshufi32x4 zmm0, zmm4, zmm6, 68
	vshufi32x4 zmm1, zmm4, zmm6, 238
	vshufi32x4 zmm2, zmm5, zmm7, 68
	vshufi32x4 zmm3, zmm5, zmm7, 238
	vpmuludq zmm4, zmm0, zmm1
	vpaddq zmm0, zmm0, zmm1
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm0, zmm0, zmm4
	vpxord zmm3, zmm3, zmm0
	vprorq zmm3, zmm3, 32
	vpmuludq zmm4, zmm2, zmm3
	vpaddq zmm2, zmm2, zmm3
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm2, zmm2, zmm4
	vpxord zmm1, zmm1, zmm2
	vprorq zmm1, zmm1, 24
	vpmuludq zmm4, zmm0, zmm1
	vpaddq zmm0, zmm0, zmm1
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm0, zmm0, zmm4
	vpxord zmm3, zmm3, zmm0
	vprorq zmm3, zmm3, 16
	vpmuludq zmm4, zmm2, zmm3
	vpaddq zmm2, zmm2, zmm3
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm2, zmm2, zmm4
	vpxord zmm1, zmm1, zmm2
	vprorq zmm1, zmm1, 63
	vpermq zmm1, zmm1, 57
	vpermq zmm2, zmm2, 78
	vpermq zmm3, zmm3, 147
	vpmuludq zmm4, zmm0, zmm1
	vpaddq zmm0, zmm0, zmm1
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm0, zmm0, zmm4
	vpxord zmm3, zmm3, zmm0
	vprorq zmm3, zmm3, 32
	vpmuludq zmm4, zmm2, zmm3
	vpaddq zmm2, zmm2, zmm3
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm2, zmm2, zmm4
	vpxord zmm1, zmm1, zmm2
	vprorq zmm1, zmm1, 24
	vpmuludq zmm4, zmm0, zmm1
	vpaddq zmm0, zmm0, zmm1
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm0, zmm0, zmm4
	vpxord zmm3, zmm3, zmm0
	vprorq zmm3, zmm3, 16
	vpmuludq zmm4, zmm2, zmm3
	vpaddq zmm2, zmm2, zmm3
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm2, zmm2, zmm4
	vpxord zmm1, zmm1, zmm2
	vprorq zmm1, zmm1, 63
	vpermq zmm1, zmm1, 147
	vpermq zmm2, zmm2, 78
	vpermq zmm3, zmm3, 57
	vshufi32x4 zmm4, zmm0, zmm0, 216
	vmovdqu32 ZMMWORD PTR [rcx+1024], zmm4
	vshufi32x4 zmm4, zmm1, zmm1, 216
	vmovdqu32 ZMMWORD PTR [rcx+1280], zmm4
	vshufi32x4 zmm4, zmm2, zmm2, 216
	vmovdqu32 ZMMWORD PTR [rcx+1536], zmm4
	vshufi32x4 zmm4, zmm3, zmm3, 216
	vmovdqu32 ZMMWORD PTR [rcx+1792], zmm4
	vmovdqu32 zmm4, ZMMWORD PTR [rcx+256]
	vmovdqu32 zmm5, ZMMWORD PTR [rcx+320]
	vmovdqu32 zmm6, ZMMWORD PTR [rcx+384]
	vmovdqu32 zmm7, ZMMWORD PTR [rcx+448]
	vshufi32x4 zmm0, zmm4, zmm6, 68
	vshufi32x4 zmm1, zmm4, zmm6, 238
	vshufi32x4 zmm2, zmm5, zmm7, 68
	vshufi32x4 zmm3, zmm5, zmm7, 238
	vpmuludq zmm4, zmm0, zmm1
	vpaddq zmm0, zmm0, zmm1
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm0, zmm0, zmm4
	vpxord zmm3, zmm3, zmm0
	vprorq zmm3, zmm3, 32
	vpmuludq zmm4, zmm2, zmm3
	vpaddq zmm2, zmm2, zmm3
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm2, zmm2, zmm4
	vpxord zmm1, zmm1, zmm2
	vprorq zmm1, zmm1, 24
	vpmuludq zmm4, zmm0, zmm1
	vpaddq zmm0, zmm0, zmm1
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm0, zmm0, zmm4
	vpxord zmm3, zmm3, zmm0
	vprorq zmm3, zmm3, 16
	vpmuludq zmm4, zmm2, zmm3
	vpaddq zmm2, zmm2, zmm3
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm2, zmm2, zmm4
	vpxord zmm1, zmm1, zmm2
	vprorq zmm1, zmm1, 63
	vpermq zmm1, zmm1, 57
	vpermq zmm2, zmm2, 78
	vpermq zmm3, zmm3, 147
	vpmuludq zmm4, zmm0, zmm1
	vpaddq zmm0, zmm0, zmm1
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm0, zmm0, zmm4
	vpxord zmm3, zmm3, zmm0
	vprorq zmm3, zmm3, 32
	vpmuludq zmm4, zmm2, zmm3
	vpaddq zmm2, zmm2, zmm3
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm2, zmm2, zmm4
	vpxord zmm1, zmm1, zmm2
	vprorq zmm1, zmm1, 24
	vpmuludq zmm4, zmm0, zmm1
	vpaddq zmm0, zmm0, zmm1
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm0, zmm0, zmm4
	vpxord zmm3, zmm3, zmm0
	vprorq zmm3, zmm3, 16
	vpmuludq zmm4, zmm2, zmm3
	vpaddq zmm2, zmm2, zmm3
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm2, zmm2, zmm4
	vpxord zmm1, zmm1, zmm2
	vprorq zmm1, zmm1, 63
	vpermq zmm1, zmm1, 147
	vpermq zmm2, zmm2, 78
	vpermq zmm3, zmm3, 57
	vshufi32x4 zmm4, zmm0, zmm0, 216
	vmovdqu32 ZMMWORD PTR [rcx+1088], zmm4
	vshufi32x4 zmm4, zmm1, zmm1, 216
	vmovdqu32 ZMMWORD PTR [rcx+1344], zmm4
	vshufi32x4 zmm4, zmm2, zmm2, 216
	vmovdqu32 ZMMWORD PTR [rcx+1600], zmm4
	vshufi32x4 zmm4, zmm3, zmm3, 216
	vmovdqu32 ZMMWORD PTR [rcx+1856], zmm4
	vmovdqu32 zmm4, ZMMWORD PTR [rcx+512]
	vmovdqu32 zmm5, ZMMWORD PTR [rcx+576]
	vmovdqu32 zmm6, ZMMWORD PTR [rcx+640]
	vmovdqu32 zmm7, ZMMWORD PTR [rcx+704]
	vshufi32x4 zmm0, zmm4, zmm6, 68
	vshufi32x4 zmm1, zmm4, zmm6, 238
	vshufi32x4 zmm2, zmm5, zmm7, 68
	vshufi32x4 zmm3, zmm5, zmm7, 238
	vpmuludq zmm4, zmm0, zmm1
	vpaddq zmm0, zmm0, zmm1
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm0, zmm0, zmm4
	vpxord zmm3, zmm3, zmm0
	vprorq zmm3, zmm3, 32
	vpmuludq zmm4, zmm2, zmm3
	vpaddq zmm2, zmm2, zmm3
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm2, zmm2, zmm4
	vpxord zmm1, zmm1, zmm2
	vprorq zmm1, zmm1, 24
	vpmuludq zmm4, zmm0, zmm1
	vpaddq zmm0, zmm0, zmm1
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm0, zmm0, zmm4
	vpxord zmm3, zmm3, zmm0
	vprorq zmm3, zmm3, 16
	vpmuludq zmm4, zmm2, zmm3
	vpaddq zmm2, zmm2, zmm3
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm2, zmm2, zmm4
	vpxord zmm1, zmm1, zmm2
	vprorq zmm1, zmm1, 63
	vpermq zmm1, zmm1, 57
	vpermq zmm2, zmm2, 78
	vpermq zmm3, zmm3, 147
	vpmuludq zmm4, zmm0, zmm1
	vpaddq zmm0, zmm0, zmm1
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm0, zmm0, zmm4
	vpxord zmm3, zmm3, zmm0
	vprorq zmm3, zmm3, 32
	vpmuludq zmm4, zmm2, zmm3
	vpaddq zmm2, zmm2, zmm3
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm2, zmm2, zmm4
	vpxord zmm1, zmm1, zmm2
	vprorq zmm1, zmm1, 24
	vpmuludq zmm4, zmm0, zmm1
	vpaddq zmm0, zmm0, zmm1
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm0, zmm0, zmm4
	vpxord zmm3, zmm3, zmm0
	vprorq zmm3, zmm3, 16
	vpmuludq zmm4, zmm2, zmm3
	vpaddq zmm2, zmm2, zmm3
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm2, zmm2, zmm4
	vpxord zmm1, zmm1, zmm2
	vprorq zmm1, zmm1, 63
	vpermq zmm1, zmm1, 147
	vpermq zmm2, zmm2, 78
	vpermq zmm3, zmm3, 57
	vshufi32x4 zmm4, zmm0, zmm0, 216
	vmovdqu32 ZMMWORD PTR [rcx+1152], zmm4
	vshufi32x4 zmm4, zmm1, zmm1, 216
	vmovdqu32 ZMMWORD PTR [rcx+1408], zmm4
	vshufi32x4 zmm4, zmm2, zmm2, 216
	vmovdqu32 ZMMWORD PTR [rcx+1664], zmm4
	vshufi32x4 zmm4, zmm3, zmm3, 216
	vmovdqu32 ZMMWORD PTR [rcx+1920], zmm4
	vmovdqu32 zmm4, ZMMWORD PTR [rcx+768]
	vmovdqu32 zmm5, ZMMWORD PTR [rcx+832]
	vmovdqu32 zmm6, ZMMWORD PTR [rcx+896]
	vmovdqu32 zmm7, ZMMWORD PTR [rcx+960]
	vshufi32x4 zmm0, zmm4, zmm6, 68
	vshufi32x4 zmm1, zmm4, zmm6, 238
	vshufi32x4 zmm2, zmm5, zmm7, 68
	vshufi32x4 zmm3, zmm5, zmm7, 238
	vpmuludq zmm4, zmm0, zmm1
	vpaddq zmm0, zmm0, zmm1
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm0, zmm0, zmm4
	vpxord zmm3, zmm3, zmm0
	vprorq zmm3, zmm3, 32
	vpmuludq zmm4, zmm2, zmm3
	vpaddq zmm2, zmm2, zmm3
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm2, zmm2, zmm4
	vpxord zmm1, zmm1, zmm2
	vprorq zmm1, zmm1, 24
	vpmuludq zmm4, zmm0, zmm1
	vpaddq zmm0, zmm0, zmm1
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm0, zmm0, zmm4
	vpxord zmm3, zmm3, zmm0
	vprorq zmm3, zmm3, 16
	vpmuludq zmm4, zmm2, zmm3
	vpaddq zmm2, zmm2, zmm3
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm2, zmm2, zmm4
	vpxord zmm1, zmm1, zmm2
	vprorq zmm1, zmm1, 63
	vpermq zmm1, zmm1, 57
	vpermq zmm2, zmm2, 78
	vpermq zmm3, zmm3, 147
	vpmuludq zmm4, zmm0, zmm1
	vpaddq zmm0, zmm0, zmm1
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm0, zmm0, zmm4
	vpxord zmm3, zmm3, zmm0
	vprorq zmm3, zmm3, 32
	vpmuludq zmm4, zmm2, zmm3
	vpaddq zmm2, zmm2, zmm3
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm2, zmm2, zmm4
	vpxord zmm1, zmm1, zmm2
	vprorq zmm1, zmm1, 24
	vpmuludq zmm4, zmm0, zmm1
	vpaddq zmm0, zmm0, zmm1
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm0, zmm0, zmm4
	vpxord zmm3, zmm3, zmm0
	vprorq zmm3, zmm3, 16
	vpmuludq zmm4, zmm2, zmm3
	vpaddq zmm2, zmm2, zmm3
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm2, zmm2, zmm4
	vpxord zmm1, zmm1, zmm2
	vprorq zmm1, zmm1, 63
	vpermq zmm1, zmm1, 147
	vpermq zmm2, zmm2, 78
	vpermq zmm3, zmm3, 57
	vshufi32x4 zmm4, zmm0, zmm0, 216
	vmovdqu32 ZMMWORD PTR [rcx+1216], zmm4
	vshufi32x4 zmm4, zmm1, zmm1, 216
	vmovdqu32 ZMMWORD PTR [rcx+1472], zmm4
	vshufi32x4 zmm4, zmm2, zmm2, 216
	vmovdqu32 ZMMWORD PTR [rcx+1728], zmm4
	vshufi32x4 zmm4, zmm3, zmm3, 216
	vmovdqu32 ZMMWORD PTR [rcx+1984], zmm4
	vmovdqu32 zmm0, ZMMWORD PTR [rcx+1024]
	vmovdqu32 zmm1, ZMMWORD PTR [rcx+1088]
	vmovdqu32 zmm2, ZMMWORD PTR [rcx+1152]
	vmovdqu32 zmm3, ZMMWORD PTR [rcx+1216]
	vpmuludq zmm4, zmm0, zmm1
	vpaddq zmm0, zmm0, zmm1
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm0, zmm0, zmm4
	vpxord zmm3, zmm3, zmm0
	vprorq zmm3, zmm3, 32
	vpmuludq zmm4, zmm2, zmm3
	vpaddq zmm2, zmm2, zmm3
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm2, zmm2, zmm4
	vpxord zmm1, zmm1, zmm2
	vprorq zmm1, zmm1, 24
	vpmuludq zmm4, zmm0, zmm1
	vpaddq zmm0, zmm0, zmm1
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm0, zmm0, zmm4
	vpxord zmm3, zmm3, zmm0
	vprorq zmm3, zmm3, 16
	vpmuludq zmm4, zmm2, zmm3
	vpaddq zmm2, zmm2, zmm3
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm2, zmm2, zmm4
	vpxord zmm1, zmm1, zmm2
	vprorq zmm1, zmm1, 63
	vpermq zmm1, zmm1, 57
	vpermq zmm2, zmm2, 78
	vpermq zmm3, zmm3, 147
	vpmuludq zmm4, zmm0, zmm1
	vpaddq zmm0, zmm0, zmm1
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm0, zmm0, zmm4
	vpxord zmm3, zmm3, zmm0
	vprorq zmm3, zmm3, 32
	vpmuludq zmm4, zmm2, zmm3
	vpaddq zmm2, zmm2, zmm3
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm2, zmm2, zmm4
	vpxord zmm1, zmm1, zmm2
	vprorq zmm1, zmm1, 24
	vpmuludq zmm4, zmm0, zmm1
	vpaddq zmm0, zmm0, zmm1
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm0, zmm0, zmm4
	vpxord zmm3, zmm3, zmm0
	vprorq zmm3, zmm3, 16
	vpmuludq zmm4, zmm2, zmm3
	vpaddq zmm2, zmm2, zmm3
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm2, zmm2, zmm4
	vpxord zmm1, zmm1, zmm2
	vprorq zmm1, zmm1, 63
	vpermq zmm1, zmm1, 147
	vpermq zmm2, zmm2, 78
	vpermq zmm3, zmm3, 57
	vmovdqu32 ZMMWORD PTR [rcx+1024], zmm0
	vmovdqu32 ZMMWORD PTR [rcx+1088], zmm1
	vmovdqu32 ZMMWORD PTR [rcx+1152], zmm2
	vmovdqu32 ZMMWORD PTR [rcx+1216], zmm3
	vmovdqu32 zmm0, ZMMWORD PTR [rcx+1280]
	vmovdqu32 zmm1, ZMMWORD PTR [rcx+1344]
	vmovdqu32 zmm2, ZMMWORD PTR [rcx+1408]
	vmovdqu32 zmm3, ZMMWORD PTR [rcx+1472]
	vpmuludq zmm4, zmm0, zmm1
	vpaddq zmm0, zmm0, zmm1
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm0, zmm0, zmm4
	vpxord zmm3, zmm3, zmm0
	vprorq zmm3, zmm3, 32
	vpmuludq zmm4, zmm2, zmm3
	vpaddq zmm2, zmm2, zmm3
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm2, zmm2, zmm4
	vpxord zmm1, zmm1, zmm2
	vprorq zmm1, zmm1, 24
	vpmuludq zmm4, zmm0, zmm1
	vpaddq zmm0, zmm0, zmm1
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm0, zmm0, zmm4
	vpxord zmm3, zmm3, zmm0
	vprorq zmm3, zmm3, 16
	vpmuludq zmm4, zmm2, zmm3
	vpaddq zmm2, zmm2, zmm3
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm2, zmm2, zmm4
	vpxord zmm1, zmm1, zmm2
	vprorq zmm1, zmm1, 63
	vpermq zmm1, zmm1, 57
	vpermq zmm2, zmm2, 78
	vpermq zmm3, zmm3, 147
	vpmuludq zmm4, zmm0, zmm1
	vpaddq zmm0, zmm0, zmm1
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm0, zmm0, zmm4
	vpxord zmm3, zmm3, zmm0
	vprorq zmm3, zmm3, 32
	vpmuludq zmm4, zmm2, zmm3
	vpaddq zmm2, zmm2, zmm3
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm2, zmm2, zmm4
	vpxord zmm1, zmm1, zmm2
	vprorq zmm1, zmm1, 24
	vpmuludq zmm4, zmm0, zmm1
	vpaddq zmm0, zmm0, zmm1
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm0, zmm0, zmm4
	vpxord zmm3, zmm3, zmm0
	vprorq zmm3, zmm3, 16
	vpmuludq zmm4, zmm2, zmm3
	vpaddq zmm2, zmm2, zmm3
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm2, zmm2, zmm4
	vpxord zmm1, zmm1, zmm2
	vprorq zmm1, zmm1, 63
	vpermq zmm1, zmm1, 147
	vpermq zmm2, zmm2, 78
	vpermq zmm3, zmm3, 57
	vmovdqu32 ZMMWORD PTR [rcx+1280], zmm0
	vmovdqu32 ZMMWORD PTR [rcx+1344], zmm1
	vmovdqu32 ZMMWORD PTR [rcx+1408], zmm2
	vmovdqu32 ZMMWORD PTR [rcx+1472], zmm3
	vmovdqu32 zmm0, ZMMWORD PTR [rcx+1536]
	vmovdqu32 zmm1, ZMMWORD PTR [rcx+1600]
	vmovdqu32 zmm2, ZMMWORD PTR [rcx+1664]
	vmovdqu32 zmm3, ZMMWORD PTR [rcx+1728]
	vpmuludq zmm4, zmm0, zmm1
	vpaddq zmm0, zmm0, zmm1
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm0, zmm0, zmm4
	vpxord zmm3, zmm3, zmm0
	vprorq zmm3, zmm3, 32
	vpmuludq zmm4, zmm2, zmm3
	vpaddq zmm2, zmm2, zmm3
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm2, zmm2, zmm4
	vpxord zmm1, zmm1, zmm2
	vprorq zmm1, zmm1, 24
	vpmuludq zmm4, zmm0, zmm1
	vpaddq zmm0, zmm0, zmm1
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm0, zmm0, zmm4
	vpxord zmm3, zmm3, zmm0
	vprorq zmm3, zmm3, 16
	vpmuludq zmm4, zmm2, zmm3
	vpaddq zmm2, zmm2, zmm3
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm2, zmm2, zmm4
	vpxord zmm1, zmm1, zmm2
	vprorq zmm1, zmm1, 63
	vpermq zmm1, zmm1, 57
	vpermq zmm2, zmm2, 78
	vpermq zmm3, zmm3, 147
	vpmuludq zmm4, zmm0, zmm1
	vpaddq zmm0, zmm0, zmm1
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm0, zmm0, zmm4
	vpxord zmm3, zmm3, zmm0
	vprorq zmm3, zmm3, 32
	vpmuludq zmm4, zmm2, zmm3
	vpaddq zmm2, zmm2, zmm3
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm2, zmm2, zmm4
	vpxord zmm1, zmm1, zmm2
	vprorq zmm1, zmm1, 24
	vpmuludq zmm4, zmm0, zmm1
	vpaddq zmm0, zmm0, zmm1
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm0, zmm0, zmm4
	vpxord zmm3, zmm3, zmm0
	vprorq zmm3, zmm3, 16
	vpmuludq zmm4, zmm2, zmm3
	vpaddq zmm2, zmm2, zmm3
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm2, zmm2, zmm4
	vpxord zmm1, zmm1, zmm2
	vprorq zmm1, zmm1, 63
	vpermq zmm1, zmm1, 147
	vpermq zmm2, zmm2, 78
	vpermq zmm3, zmm3, 57
	vmovdqu32 ZMMWORD PTR [rcx+1536], zmm0
	vmovdqu32 ZMMWORD PTR [rcx+1600], zmm1
	vmovdqu32 ZMMWORD PTR [rcx+1664], zmm2
	vmovdqu32 ZMMWORD PTR [rcx+1728], zmm3
	vmovdqu32 zmm0, ZMMWORD PTR [rcx+1792]
	vmovdqu32 zmm1, ZMMWORD PTR [rcx+1856]
	vmovdqu32 zmm2, ZMMWORD PTR [rcx+1920]
	vmovdqu32 zmm3, ZMMWORD PTR [rcx+1984]
	vpmuludq zmm4, zmm0, zmm1
	vpaddq zmm0, zmm0, zmm1
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm0, zmm0, zmm4
	vpxord zmm3, zmm3, zmm0
	vprorq zmm3, zmm3, 32
	vpmuludq zmm4, zmm2, zmm3
	vpaddq zmm2, zmm2, zmm3
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm2, zmm2, zmm4
	vpxord zmm1, zmm1, zmm2
	vprorq zmm1, zmm1, 24
	vpmuludq zmm4, zmm0, zmm1
	vpaddq zmm0, zmm0, zmm1
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm0, zmm0, zmm4
	vpxord zmm3, zmm3, zmm0
	vprorq zmm3, zmm3, 16
	vpmuludq zmm4, zmm2, zmm3
	vpaddq zmm2, zmm2, zmm3
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm2, zmm2, zmm4
	vpxord zmm1, zmm1, zmm2
	vprorq zmm1, zmm1, 63
	vpermq zmm1, zmm1, 57
	vpermq zmm2, zmm2, 78
	vpermq zmm3, zmm3, 147
	vpmuludq zmm4, zmm0, zmm1
	vpaddq zmm0, zmm0, zmm1
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm0, zmm0, zmm4
	vpxord zmm3, zmm3, zmm0
	vprorq zmm3, zmm3, 32
	vpmuludq zmm4, zmm2, zmm3
	vpaddq zmm2, zmm2, zmm3
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm2, zmm2, zmm4
	vpxord zmm1, zmm1, zmm2
	vprorq zmm1, zmm1, 24
	vpmuludq zmm4, zmm0, zmm1
	vpaddq zmm0, zmm0, zmm1
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm0, zmm0, zmm4
	vpxord zmm3, zmm3, zmm0
	vprorq zmm3, zmm3, 16
	vpmuludq zmm4, zmm2, zmm3
	vpaddq zmm2, zmm2, zmm3
	vpaddq zmm4, zmm4, zmm4
	vpaddq zmm2, zmm2, zmm4
	vpxord zmm1, zmm1, zmm2
	vprorq zmm1, zmm1, 63
	vpermq zmm1, zmm1, 147
	vpermq zmm2, zmm2, 78
	vpermq zmm3, zmm3, 57
	vmovdqu32 ZMMWORD PTR [rcx+1792], zmm0
	vmovdqu32 ZMMWORD PTR [rcx+1856], zmm1
	vmovdqu32 ZMMWORD PTR [rcx+1920], zmm2
	vmovdqu32 ZMMWORD PTR [rcx+1984], zmm3
	vmovdqu32 zmm0, ZMMWORD PTR [rcx+1024]
	vmovdqu32 zmm1, ZMMWORD PTR [rcx+1280]
	vmovdqu32 zmm4, ZMMWORD PTR [rcx]
	vmovdqu32 zmm5, ZMMWORD PTR [rcx+128]
	vshufi32x4 zmm2, zmm0, zmm1, 136
	vshufi32x4 zmm3, zmm0, zmm1, 221
	vpxord zmm2, zmm2, zmm4
	vpxord zmm3, zmm3, zmm5
	vmovdqu32 ZMMWORD PTR [rdx], zmm2
	vmovdqu32 ZMMWORD PTR [rdx+128], zmm3
	vmovdqu32 zmm0, ZMMWORD PTR [rcx+1088]
	vmovdqu32 zmm1, ZMMWORD PTR [rcx+1344]
	vmovdqu32 zmm4, ZMMWORD PTR [rcx+256]
	vmovdqu32 zmm5, ZMMWORD PTR [rcx+384]
	vshufi32x4 zmm2, zmm0, zmm1, 136
	vshufi32x4 zmm3, zmm0, zmm1, 221
	vpxord zmm2, zmm2, zmm4
	vpxord zmm3, zmm3, zmm5
	vmovdqu32 ZMMWORD PTR [rdx+256], zmm2
	vmovdqu32 ZMMWORD PTR [rdx+384], zmm3
	vmovdqu32 zmm0, ZMMWORD PTR [rcx+1152]
	vmovdqu32 zmm1, ZMMWORD PTR [rcx+1408]
	vmovdqu32 zmm4, ZMMWORD PTR [rcx+512]
	vmovdqu32 zmm5, ZMMWORD PTR [rcx+640]
	vshufi32x4 zmm2, zmm0, zmm1, 136
	vshufi32x4 zmm3, zmm0, zmm1, 221
	vpxord zmm2, zmm2, zmm4
	vpxord zmm3, zmm3, zmm5
	vmovdqu32 ZMMWORD PTR [rdx+512], zmm2
	vmovdqu32 ZMMWORD PTR [rdx+640], zmm3
	vmovdqu32 zmm0, ZMMWORD PTR [rcx+1216]
	vmovdqu32 zmm1, ZMMWORD PTR [rcx+1472]
	vmovdqu32 zmm4, ZMMWORD PTR [rcx+768]
	vmovdqu32 zmm5, ZMMWORD PTR [rcx+896]
	vshufi32x4 zmm2, zmm0, zmm1, 136
	vshufi32x4 zmm3, zmm0, zmm1, 221
	vpxord zmm2, zmm2, zmm4
	vpxord zmm3, zmm3, zmm5
	vmovdqu32 ZMMWORD PTR [rdx+768], zmm2
	vmovdqu32 ZMMWORD PTR [rdx+896], zmm3
	vmovdqu32 zmm0, ZMMWORD PTR [rcx+1536]
	vmovdqu32 zmm1, ZMMWORD PTR [rcx+1792]
	vmovdqu32 zmm4, ZMMWORD PTR [rcx+64]
	vmovdqu32 zmm5, ZMMWORD PTR [rcx+192]
	vshufi32x4 zmm2, zmm0, zmm1, 136
	vshufi32x4 zmm3, zmm0, zmm1, 221
	vpxord zmm2, zmm2, zmm4
	vpxord zmm3, zmm3, zmm5
	vmovdqu32 ZMMWORD PTR [rdx+64], zmm2
	vmovdqu32 ZMMWORD PTR [rdx+192], zmm3
	vmovdqu32 zmm0, ZMMWORD PTR [rcx+1600]
	vmovdqu32 zmm1, ZMMWORD PTR [rcx+1856]
	vmovdqu32 zmm4, ZMMWORD PTR [rcx+320]
	vmovdqu32 zmm5, ZMMWORD PTR [rcx+448]
	vshufi32x4 zmm2, zmm0, zmm1, 136
	vshufi32x4 zmm3, zmm0, zmm1, 221
	vpxord zmm2, zmm2, zmm4
	vpxord zmm3, zmm3, zmm5
	vmovdqu32 ZMMWORD PTR [rdx+320], zmm2
	vmovdqu32 ZMMWORD PTR [rdx+448], zmm3
	vmovdqu32 zmm0, ZMMWORD PTR [rcx+1664]
	vmovdqu32 zmm1, ZMMWORD PTR [rcx+1920]
	vmovdqu32 zmm4, ZMMWORD PTR [rcx+576]
	vmovdqu32 zmm5, ZMMWORD PTR [rcx+704]
	vshufi32x4 zmm2, zmm0, zmm1, 136
	vshufi32x4 zmm3, zmm0, zmm1, 221
	vpxord zmm2, zmm2, zmm4
	vpxord zmm3, zmm3, zmm5
	vmovdqu32 ZMMWORD PTR [rdx+576], zmm2
	vmovdqu32 ZMMWORD PTR [rdx+704], zmm3
	vmovdqu32 zmm0, ZMMWORD PTR [rcx+1728]
	vmovdqu32 zmm1, ZMMWORD PTR [rcx+1984]
	vmovdqu32 zmm4, ZMMWORD PTR [rcx+832]
	vmovdqu32 zmm5, ZMMWORD PTR [rcx+960]
	vshufi32x4 zmm2, zmm0, zmm1, 136
	vshufi32x4 zmm3, zmm0, zmm1, 221
	vpxord zmm2, zmm2, zmm4
	vpxord zmm3, zmm3, zmm5
	vmovdqu32 ZMMWORD PTR [rdx+832], zmm2
	vmovdqu32 ZMMWORD PTR [rdx+960], zmm3
	vzeroupper
	lfence
	mov DWORD PTR [rcx+2048], r11d
	ldmxcsr DWORD PTR [rcx+2048]
	ret
	.p2align 6
