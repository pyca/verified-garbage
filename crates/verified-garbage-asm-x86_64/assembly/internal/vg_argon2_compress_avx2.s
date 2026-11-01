// The functions of `src/internal/vg_argon2_compress_avx2.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_argon2_compress_avx2:
	stmxcsr DWORD PTR [rcx+2048]
	mov r11d, DWORD PTR [rcx+2048]
	and r11d, 65535
	mov eax, 8127
	mov DWORD PTR [rcx+2052], eax
	ldmxcsr DWORD PTR [rcx+2052]
	lfence
	movabs rax, 144396693218329603
	vmovq xmm14, rax
	movabs rax, 723118075922942987
	vmovq xmm13, rax
	vpunpcklqdq xmm14, xmm14, xmm13
	vpermq ymm14, ymm14, 68
	movabs rax, 72065316473275138
	vmovq xmm15, rax
	movabs rax, 650786699177888522
	vmovq xmm13, rax
	vpunpcklqdq xmm15, xmm15, xmm13
	vpermq ymm15, ymm15, 68
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vmovdqu ymm1, YMMWORD PTR [rsi]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rcx], ymm0
	vmovdqu YMMWORD PTR [rcx+1024], ymm0
	vmovdqu ymm0, YMMWORD PTR [rdi+32]
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rcx+32], ymm0
	vmovdqu YMMWORD PTR [rcx+1056], ymm0
	vmovdqu ymm0, YMMWORD PTR [rdi+64]
	vmovdqu ymm1, YMMWORD PTR [rsi+64]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rcx+64], ymm0
	vmovdqu YMMWORD PTR [rcx+1088], ymm0
	vmovdqu ymm0, YMMWORD PTR [rdi+96]
	vmovdqu ymm1, YMMWORD PTR [rsi+96]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rcx+96], ymm0
	vmovdqu YMMWORD PTR [rcx+1120], ymm0
	vmovdqu ymm0, YMMWORD PTR [rdi+128]
	vmovdqu ymm1, YMMWORD PTR [rsi+128]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rcx+128], ymm0
	vmovdqu YMMWORD PTR [rcx+1152], ymm0
	vmovdqu ymm0, YMMWORD PTR [rdi+160]
	vmovdqu ymm1, YMMWORD PTR [rsi+160]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rcx+160], ymm0
	vmovdqu YMMWORD PTR [rcx+1184], ymm0
	vmovdqu ymm0, YMMWORD PTR [rdi+192]
	vmovdqu ymm1, YMMWORD PTR [rsi+192]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rcx+192], ymm0
	vmovdqu YMMWORD PTR [rcx+1216], ymm0
	vmovdqu ymm0, YMMWORD PTR [rdi+224]
	vmovdqu ymm1, YMMWORD PTR [rsi+224]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rcx+224], ymm0
	vmovdqu YMMWORD PTR [rcx+1248], ymm0
	vmovdqu ymm0, YMMWORD PTR [rdi+256]
	vmovdqu ymm1, YMMWORD PTR [rsi+256]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rcx+256], ymm0
	vmovdqu YMMWORD PTR [rcx+1280], ymm0
	vmovdqu ymm0, YMMWORD PTR [rdi+288]
	vmovdqu ymm1, YMMWORD PTR [rsi+288]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rcx+288], ymm0
	vmovdqu YMMWORD PTR [rcx+1312], ymm0
	vmovdqu ymm0, YMMWORD PTR [rdi+320]
	vmovdqu ymm1, YMMWORD PTR [rsi+320]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rcx+320], ymm0
	vmovdqu YMMWORD PTR [rcx+1344], ymm0
	vmovdqu ymm0, YMMWORD PTR [rdi+352]
	vmovdqu ymm1, YMMWORD PTR [rsi+352]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rcx+352], ymm0
	vmovdqu YMMWORD PTR [rcx+1376], ymm0
	vmovdqu ymm0, YMMWORD PTR [rdi+384]
	vmovdqu ymm1, YMMWORD PTR [rsi+384]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rcx+384], ymm0
	vmovdqu YMMWORD PTR [rcx+1408], ymm0
	vmovdqu ymm0, YMMWORD PTR [rdi+416]
	vmovdqu ymm1, YMMWORD PTR [rsi+416]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rcx+416], ymm0
	vmovdqu YMMWORD PTR [rcx+1440], ymm0
	vmovdqu ymm0, YMMWORD PTR [rdi+448]
	vmovdqu ymm1, YMMWORD PTR [rsi+448]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rcx+448], ymm0
	vmovdqu YMMWORD PTR [rcx+1472], ymm0
	vmovdqu ymm0, YMMWORD PTR [rdi+480]
	vmovdqu ymm1, YMMWORD PTR [rsi+480]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rcx+480], ymm0
	vmovdqu YMMWORD PTR [rcx+1504], ymm0
	vmovdqu ymm0, YMMWORD PTR [rdi+512]
	vmovdqu ymm1, YMMWORD PTR [rsi+512]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rcx+512], ymm0
	vmovdqu YMMWORD PTR [rcx+1536], ymm0
	vmovdqu ymm0, YMMWORD PTR [rdi+544]
	vmovdqu ymm1, YMMWORD PTR [rsi+544]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rcx+544], ymm0
	vmovdqu YMMWORD PTR [rcx+1568], ymm0
	vmovdqu ymm0, YMMWORD PTR [rdi+576]
	vmovdqu ymm1, YMMWORD PTR [rsi+576]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rcx+576], ymm0
	vmovdqu YMMWORD PTR [rcx+1600], ymm0
	vmovdqu ymm0, YMMWORD PTR [rdi+608]
	vmovdqu ymm1, YMMWORD PTR [rsi+608]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rcx+608], ymm0
	vmovdqu YMMWORD PTR [rcx+1632], ymm0
	vmovdqu ymm0, YMMWORD PTR [rdi+640]
	vmovdqu ymm1, YMMWORD PTR [rsi+640]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rcx+640], ymm0
	vmovdqu YMMWORD PTR [rcx+1664], ymm0
	vmovdqu ymm0, YMMWORD PTR [rdi+672]
	vmovdqu ymm1, YMMWORD PTR [rsi+672]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rcx+672], ymm0
	vmovdqu YMMWORD PTR [rcx+1696], ymm0
	vmovdqu ymm0, YMMWORD PTR [rdi+704]
	vmovdqu ymm1, YMMWORD PTR [rsi+704]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rcx+704], ymm0
	vmovdqu YMMWORD PTR [rcx+1728], ymm0
	vmovdqu ymm0, YMMWORD PTR [rdi+736]
	vmovdqu ymm1, YMMWORD PTR [rsi+736]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rcx+736], ymm0
	vmovdqu YMMWORD PTR [rcx+1760], ymm0
	vmovdqu ymm0, YMMWORD PTR [rdi+768]
	vmovdqu ymm1, YMMWORD PTR [rsi+768]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rcx+768], ymm0
	vmovdqu YMMWORD PTR [rcx+1792], ymm0
	vmovdqu ymm0, YMMWORD PTR [rdi+800]
	vmovdqu ymm1, YMMWORD PTR [rsi+800]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rcx+800], ymm0
	vmovdqu YMMWORD PTR [rcx+1824], ymm0
	vmovdqu ymm0, YMMWORD PTR [rdi+832]
	vmovdqu ymm1, YMMWORD PTR [rsi+832]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rcx+832], ymm0
	vmovdqu YMMWORD PTR [rcx+1856], ymm0
	vmovdqu ymm0, YMMWORD PTR [rdi+864]
	vmovdqu ymm1, YMMWORD PTR [rsi+864]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rcx+864], ymm0
	vmovdqu YMMWORD PTR [rcx+1888], ymm0
	vmovdqu ymm0, YMMWORD PTR [rdi+896]
	vmovdqu ymm1, YMMWORD PTR [rsi+896]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rcx+896], ymm0
	vmovdqu YMMWORD PTR [rcx+1920], ymm0
	vmovdqu ymm0, YMMWORD PTR [rdi+928]
	vmovdqu ymm1, YMMWORD PTR [rsi+928]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rcx+928], ymm0
	vmovdqu YMMWORD PTR [rcx+1952], ymm0
	vmovdqu ymm0, YMMWORD PTR [rdi+960]
	vmovdqu ymm1, YMMWORD PTR [rsi+960]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rcx+960], ymm0
	vmovdqu YMMWORD PTR [rcx+1984], ymm0
	vmovdqu ymm0, YMMWORD PTR [rdi+992]
	vmovdqu ymm1, YMMWORD PTR [rsi+992]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rcx+992], ymm0
	vmovdqu YMMWORD PTR [rcx+2016], ymm0
	vmovdqu ymm0, YMMWORD PTR [rcx+1024]
	vmovdqu ymm1, YMMWORD PTR [rcx+1056]
	vmovdqu ymm2, YMMWORD PTR [rcx+1088]
	vmovdqu ymm3, YMMWORD PTR [rcx+1120]
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufd ymm3, ymm3, 177
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm14
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm15
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpsrlq ymm4, ymm1, 63
	vpaddq ymm1, ymm1, ymm1
	vpxor ymm1, ymm1, ymm4
	vpermq ymm1, ymm1, 57
	vpermq ymm2, ymm2, 78
	vpermq ymm3, ymm3, 147
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufd ymm3, ymm3, 177
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm14
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm15
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpsrlq ymm4, ymm1, 63
	vpaddq ymm1, ymm1, ymm1
	vpxor ymm1, ymm1, ymm4
	vpermq ymm1, ymm1, 147
	vpermq ymm2, ymm2, 78
	vpermq ymm3, ymm3, 57
	vmovdqu YMMWORD PTR [rcx+1024], ymm0
	vmovdqu YMMWORD PTR [rcx+1056], ymm1
	vmovdqu YMMWORD PTR [rcx+1088], ymm2
	vmovdqu YMMWORD PTR [rcx+1120], ymm3
	vmovdqu ymm0, YMMWORD PTR [rcx+1152]
	vmovdqu ymm1, YMMWORD PTR [rcx+1184]
	vmovdqu ymm2, YMMWORD PTR [rcx+1216]
	vmovdqu ymm3, YMMWORD PTR [rcx+1248]
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufd ymm3, ymm3, 177
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm14
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm15
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpsrlq ymm4, ymm1, 63
	vpaddq ymm1, ymm1, ymm1
	vpxor ymm1, ymm1, ymm4
	vpermq ymm1, ymm1, 57
	vpermq ymm2, ymm2, 78
	vpermq ymm3, ymm3, 147
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufd ymm3, ymm3, 177
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm14
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm15
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpsrlq ymm4, ymm1, 63
	vpaddq ymm1, ymm1, ymm1
	vpxor ymm1, ymm1, ymm4
	vpermq ymm1, ymm1, 147
	vpermq ymm2, ymm2, 78
	vpermq ymm3, ymm3, 57
	vmovdqu YMMWORD PTR [rcx+1152], ymm0
	vmovdqu YMMWORD PTR [rcx+1184], ymm1
	vmovdqu YMMWORD PTR [rcx+1216], ymm2
	vmovdqu YMMWORD PTR [rcx+1248], ymm3
	vmovdqu ymm0, YMMWORD PTR [rcx+1280]
	vmovdqu ymm1, YMMWORD PTR [rcx+1312]
	vmovdqu ymm2, YMMWORD PTR [rcx+1344]
	vmovdqu ymm3, YMMWORD PTR [rcx+1376]
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufd ymm3, ymm3, 177
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm14
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm15
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpsrlq ymm4, ymm1, 63
	vpaddq ymm1, ymm1, ymm1
	vpxor ymm1, ymm1, ymm4
	vpermq ymm1, ymm1, 57
	vpermq ymm2, ymm2, 78
	vpermq ymm3, ymm3, 147
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufd ymm3, ymm3, 177
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm14
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm15
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpsrlq ymm4, ymm1, 63
	vpaddq ymm1, ymm1, ymm1
	vpxor ymm1, ymm1, ymm4
	vpermq ymm1, ymm1, 147
	vpermq ymm2, ymm2, 78
	vpermq ymm3, ymm3, 57
	vmovdqu YMMWORD PTR [rcx+1280], ymm0
	vmovdqu YMMWORD PTR [rcx+1312], ymm1
	vmovdqu YMMWORD PTR [rcx+1344], ymm2
	vmovdqu YMMWORD PTR [rcx+1376], ymm3
	vmovdqu ymm0, YMMWORD PTR [rcx+1408]
	vmovdqu ymm1, YMMWORD PTR [rcx+1440]
	vmovdqu ymm2, YMMWORD PTR [rcx+1472]
	vmovdqu ymm3, YMMWORD PTR [rcx+1504]
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufd ymm3, ymm3, 177
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm14
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm15
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpsrlq ymm4, ymm1, 63
	vpaddq ymm1, ymm1, ymm1
	vpxor ymm1, ymm1, ymm4
	vpermq ymm1, ymm1, 57
	vpermq ymm2, ymm2, 78
	vpermq ymm3, ymm3, 147
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufd ymm3, ymm3, 177
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm14
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm15
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpsrlq ymm4, ymm1, 63
	vpaddq ymm1, ymm1, ymm1
	vpxor ymm1, ymm1, ymm4
	vpermq ymm1, ymm1, 147
	vpermq ymm2, ymm2, 78
	vpermq ymm3, ymm3, 57
	vmovdqu YMMWORD PTR [rcx+1408], ymm0
	vmovdqu YMMWORD PTR [rcx+1440], ymm1
	vmovdqu YMMWORD PTR [rcx+1472], ymm2
	vmovdqu YMMWORD PTR [rcx+1504], ymm3
	vmovdqu ymm0, YMMWORD PTR [rcx+1536]
	vmovdqu ymm1, YMMWORD PTR [rcx+1568]
	vmovdqu ymm2, YMMWORD PTR [rcx+1600]
	vmovdqu ymm3, YMMWORD PTR [rcx+1632]
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufd ymm3, ymm3, 177
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm14
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm15
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpsrlq ymm4, ymm1, 63
	vpaddq ymm1, ymm1, ymm1
	vpxor ymm1, ymm1, ymm4
	vpermq ymm1, ymm1, 57
	vpermq ymm2, ymm2, 78
	vpermq ymm3, ymm3, 147
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufd ymm3, ymm3, 177
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm14
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm15
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpsrlq ymm4, ymm1, 63
	vpaddq ymm1, ymm1, ymm1
	vpxor ymm1, ymm1, ymm4
	vpermq ymm1, ymm1, 147
	vpermq ymm2, ymm2, 78
	vpermq ymm3, ymm3, 57
	vmovdqu YMMWORD PTR [rcx+1536], ymm0
	vmovdqu YMMWORD PTR [rcx+1568], ymm1
	vmovdqu YMMWORD PTR [rcx+1600], ymm2
	vmovdqu YMMWORD PTR [rcx+1632], ymm3
	vmovdqu ymm0, YMMWORD PTR [rcx+1664]
	vmovdqu ymm1, YMMWORD PTR [rcx+1696]
	vmovdqu ymm2, YMMWORD PTR [rcx+1728]
	vmovdqu ymm3, YMMWORD PTR [rcx+1760]
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufd ymm3, ymm3, 177
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm14
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm15
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpsrlq ymm4, ymm1, 63
	vpaddq ymm1, ymm1, ymm1
	vpxor ymm1, ymm1, ymm4
	vpermq ymm1, ymm1, 57
	vpermq ymm2, ymm2, 78
	vpermq ymm3, ymm3, 147
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufd ymm3, ymm3, 177
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm14
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm15
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpsrlq ymm4, ymm1, 63
	vpaddq ymm1, ymm1, ymm1
	vpxor ymm1, ymm1, ymm4
	vpermq ymm1, ymm1, 147
	vpermq ymm2, ymm2, 78
	vpermq ymm3, ymm3, 57
	vmovdqu YMMWORD PTR [rcx+1664], ymm0
	vmovdqu YMMWORD PTR [rcx+1696], ymm1
	vmovdqu YMMWORD PTR [rcx+1728], ymm2
	vmovdqu YMMWORD PTR [rcx+1760], ymm3
	vmovdqu ymm0, YMMWORD PTR [rcx+1792]
	vmovdqu ymm1, YMMWORD PTR [rcx+1824]
	vmovdqu ymm2, YMMWORD PTR [rcx+1856]
	vmovdqu ymm3, YMMWORD PTR [rcx+1888]
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufd ymm3, ymm3, 177
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm14
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm15
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpsrlq ymm4, ymm1, 63
	vpaddq ymm1, ymm1, ymm1
	vpxor ymm1, ymm1, ymm4
	vpermq ymm1, ymm1, 57
	vpermq ymm2, ymm2, 78
	vpermq ymm3, ymm3, 147
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufd ymm3, ymm3, 177
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm14
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm15
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpsrlq ymm4, ymm1, 63
	vpaddq ymm1, ymm1, ymm1
	vpxor ymm1, ymm1, ymm4
	vpermq ymm1, ymm1, 147
	vpermq ymm2, ymm2, 78
	vpermq ymm3, ymm3, 57
	vmovdqu YMMWORD PTR [rcx+1792], ymm0
	vmovdqu YMMWORD PTR [rcx+1824], ymm1
	vmovdqu YMMWORD PTR [rcx+1856], ymm2
	vmovdqu YMMWORD PTR [rcx+1888], ymm3
	vmovdqu ymm0, YMMWORD PTR [rcx+1920]
	vmovdqu ymm1, YMMWORD PTR [rcx+1952]
	vmovdqu ymm2, YMMWORD PTR [rcx+1984]
	vmovdqu ymm3, YMMWORD PTR [rcx+2016]
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufd ymm3, ymm3, 177
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm14
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm15
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpsrlq ymm4, ymm1, 63
	vpaddq ymm1, ymm1, ymm1
	vpxor ymm1, ymm1, ymm4
	vpermq ymm1, ymm1, 57
	vpermq ymm2, ymm2, 78
	vpermq ymm3, ymm3, 147
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufd ymm3, ymm3, 177
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm14
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm15
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpsrlq ymm4, ymm1, 63
	vpaddq ymm1, ymm1, ymm1
	vpxor ymm1, ymm1, ymm4
	vpermq ymm1, ymm1, 147
	vpermq ymm2, ymm2, 78
	vpermq ymm3, ymm3, 57
	vmovdqu YMMWORD PTR [rcx+1920], ymm0
	vmovdqu YMMWORD PTR [rcx+1952], ymm1
	vmovdqu YMMWORD PTR [rcx+1984], ymm2
	vmovdqu YMMWORD PTR [rcx+2016], ymm3
	vmovdqu xmm0, XMMWORD PTR [rcx+1024]
	vmovdqu xmm4, XMMWORD PTR [rcx+1152]
	vinserti128 ymm0, ymm0, xmm4, 1
	vmovdqu xmm1, XMMWORD PTR [rcx+1280]
	vmovdqu xmm4, XMMWORD PTR [rcx+1408]
	vinserti128 ymm1, ymm1, xmm4, 1
	vmovdqu xmm2, XMMWORD PTR [rcx+1536]
	vmovdqu xmm4, XMMWORD PTR [rcx+1664]
	vinserti128 ymm2, ymm2, xmm4, 1
	vmovdqu xmm3, XMMWORD PTR [rcx+1792]
	vmovdqu xmm4, XMMWORD PTR [rcx+1920]
	vinserti128 ymm3, ymm3, xmm4, 1
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufd ymm3, ymm3, 177
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm14
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm15
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpsrlq ymm4, ymm1, 63
	vpaddq ymm1, ymm1, ymm1
	vpxor ymm1, ymm1, ymm4
	vpermq ymm1, ymm1, 57
	vpermq ymm2, ymm2, 78
	vpermq ymm3, ymm3, 147
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufd ymm3, ymm3, 177
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm14
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm15
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpsrlq ymm4, ymm1, 63
	vpaddq ymm1, ymm1, ymm1
	vpxor ymm1, ymm1, ymm4
	vpermq ymm1, ymm1, 147
	vpermq ymm2, ymm2, 78
	vpermq ymm3, ymm3, 57
	vmovdqu XMMWORD PTR [rcx+1024], xmm0
	vextracti128 xmm4, ymm0, 1
	vmovdqu XMMWORD PTR [rcx+1152], xmm4
	vmovdqu XMMWORD PTR [rcx+1280], xmm1
	vextracti128 xmm4, ymm1, 1
	vmovdqu XMMWORD PTR [rcx+1408], xmm4
	vmovdqu XMMWORD PTR [rcx+1536], xmm2
	vextracti128 xmm4, ymm2, 1
	vmovdqu XMMWORD PTR [rcx+1664], xmm4
	vmovdqu XMMWORD PTR [rcx+1792], xmm3
	vextracti128 xmm4, ymm3, 1
	vmovdqu XMMWORD PTR [rcx+1920], xmm4
	vmovdqu xmm0, XMMWORD PTR [rcx+1040]
	vmovdqu xmm4, XMMWORD PTR [rcx+1168]
	vinserti128 ymm0, ymm0, xmm4, 1
	vmovdqu xmm1, XMMWORD PTR [rcx+1296]
	vmovdqu xmm4, XMMWORD PTR [rcx+1424]
	vinserti128 ymm1, ymm1, xmm4, 1
	vmovdqu xmm2, XMMWORD PTR [rcx+1552]
	vmovdqu xmm4, XMMWORD PTR [rcx+1680]
	vinserti128 ymm2, ymm2, xmm4, 1
	vmovdqu xmm3, XMMWORD PTR [rcx+1808]
	vmovdqu xmm4, XMMWORD PTR [rcx+1936]
	vinserti128 ymm3, ymm3, xmm4, 1
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufd ymm3, ymm3, 177
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm14
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm15
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpsrlq ymm4, ymm1, 63
	vpaddq ymm1, ymm1, ymm1
	vpxor ymm1, ymm1, ymm4
	vpermq ymm1, ymm1, 57
	vpermq ymm2, ymm2, 78
	vpermq ymm3, ymm3, 147
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufd ymm3, ymm3, 177
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm14
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm15
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpsrlq ymm4, ymm1, 63
	vpaddq ymm1, ymm1, ymm1
	vpxor ymm1, ymm1, ymm4
	vpermq ymm1, ymm1, 147
	vpermq ymm2, ymm2, 78
	vpermq ymm3, ymm3, 57
	vmovdqu XMMWORD PTR [rcx+1040], xmm0
	vextracti128 xmm4, ymm0, 1
	vmovdqu XMMWORD PTR [rcx+1168], xmm4
	vmovdqu XMMWORD PTR [rcx+1296], xmm1
	vextracti128 xmm4, ymm1, 1
	vmovdqu XMMWORD PTR [rcx+1424], xmm4
	vmovdqu XMMWORD PTR [rcx+1552], xmm2
	vextracti128 xmm4, ymm2, 1
	vmovdqu XMMWORD PTR [rcx+1680], xmm4
	vmovdqu XMMWORD PTR [rcx+1808], xmm3
	vextracti128 xmm4, ymm3, 1
	vmovdqu XMMWORD PTR [rcx+1936], xmm4
	vmovdqu xmm0, XMMWORD PTR [rcx+1056]
	vmovdqu xmm4, XMMWORD PTR [rcx+1184]
	vinserti128 ymm0, ymm0, xmm4, 1
	vmovdqu xmm1, XMMWORD PTR [rcx+1312]
	vmovdqu xmm4, XMMWORD PTR [rcx+1440]
	vinserti128 ymm1, ymm1, xmm4, 1
	vmovdqu xmm2, XMMWORD PTR [rcx+1568]
	vmovdqu xmm4, XMMWORD PTR [rcx+1696]
	vinserti128 ymm2, ymm2, xmm4, 1
	vmovdqu xmm3, XMMWORD PTR [rcx+1824]
	vmovdqu xmm4, XMMWORD PTR [rcx+1952]
	vinserti128 ymm3, ymm3, xmm4, 1
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufd ymm3, ymm3, 177
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm14
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm15
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpsrlq ymm4, ymm1, 63
	vpaddq ymm1, ymm1, ymm1
	vpxor ymm1, ymm1, ymm4
	vpermq ymm1, ymm1, 57
	vpermq ymm2, ymm2, 78
	vpermq ymm3, ymm3, 147
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufd ymm3, ymm3, 177
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm14
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm15
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpsrlq ymm4, ymm1, 63
	vpaddq ymm1, ymm1, ymm1
	vpxor ymm1, ymm1, ymm4
	vpermq ymm1, ymm1, 147
	vpermq ymm2, ymm2, 78
	vpermq ymm3, ymm3, 57
	vmovdqu XMMWORD PTR [rcx+1056], xmm0
	vextracti128 xmm4, ymm0, 1
	vmovdqu XMMWORD PTR [rcx+1184], xmm4
	vmovdqu XMMWORD PTR [rcx+1312], xmm1
	vextracti128 xmm4, ymm1, 1
	vmovdqu XMMWORD PTR [rcx+1440], xmm4
	vmovdqu XMMWORD PTR [rcx+1568], xmm2
	vextracti128 xmm4, ymm2, 1
	vmovdqu XMMWORD PTR [rcx+1696], xmm4
	vmovdqu XMMWORD PTR [rcx+1824], xmm3
	vextracti128 xmm4, ymm3, 1
	vmovdqu XMMWORD PTR [rcx+1952], xmm4
	vmovdqu xmm0, XMMWORD PTR [rcx+1072]
	vmovdqu xmm4, XMMWORD PTR [rcx+1200]
	vinserti128 ymm0, ymm0, xmm4, 1
	vmovdqu xmm1, XMMWORD PTR [rcx+1328]
	vmovdqu xmm4, XMMWORD PTR [rcx+1456]
	vinserti128 ymm1, ymm1, xmm4, 1
	vmovdqu xmm2, XMMWORD PTR [rcx+1584]
	vmovdqu xmm4, XMMWORD PTR [rcx+1712]
	vinserti128 ymm2, ymm2, xmm4, 1
	vmovdqu xmm3, XMMWORD PTR [rcx+1840]
	vmovdqu xmm4, XMMWORD PTR [rcx+1968]
	vinserti128 ymm3, ymm3, xmm4, 1
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufd ymm3, ymm3, 177
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm14
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm15
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpsrlq ymm4, ymm1, 63
	vpaddq ymm1, ymm1, ymm1
	vpxor ymm1, ymm1, ymm4
	vpermq ymm1, ymm1, 57
	vpermq ymm2, ymm2, 78
	vpermq ymm3, ymm3, 147
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufd ymm3, ymm3, 177
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm14
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm15
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpsrlq ymm4, ymm1, 63
	vpaddq ymm1, ymm1, ymm1
	vpxor ymm1, ymm1, ymm4
	vpermq ymm1, ymm1, 147
	vpermq ymm2, ymm2, 78
	vpermq ymm3, ymm3, 57
	vmovdqu XMMWORD PTR [rcx+1072], xmm0
	vextracti128 xmm4, ymm0, 1
	vmovdqu XMMWORD PTR [rcx+1200], xmm4
	vmovdqu XMMWORD PTR [rcx+1328], xmm1
	vextracti128 xmm4, ymm1, 1
	vmovdqu XMMWORD PTR [rcx+1456], xmm4
	vmovdqu XMMWORD PTR [rcx+1584], xmm2
	vextracti128 xmm4, ymm2, 1
	vmovdqu XMMWORD PTR [rcx+1712], xmm4
	vmovdqu XMMWORD PTR [rcx+1840], xmm3
	vextracti128 xmm4, ymm3, 1
	vmovdqu XMMWORD PTR [rcx+1968], xmm4
	vmovdqu xmm0, XMMWORD PTR [rcx+1088]
	vmovdqu xmm4, XMMWORD PTR [rcx+1216]
	vinserti128 ymm0, ymm0, xmm4, 1
	vmovdqu xmm1, XMMWORD PTR [rcx+1344]
	vmovdqu xmm4, XMMWORD PTR [rcx+1472]
	vinserti128 ymm1, ymm1, xmm4, 1
	vmovdqu xmm2, XMMWORD PTR [rcx+1600]
	vmovdqu xmm4, XMMWORD PTR [rcx+1728]
	vinserti128 ymm2, ymm2, xmm4, 1
	vmovdqu xmm3, XMMWORD PTR [rcx+1856]
	vmovdqu xmm4, XMMWORD PTR [rcx+1984]
	vinserti128 ymm3, ymm3, xmm4, 1
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufd ymm3, ymm3, 177
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm14
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm15
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpsrlq ymm4, ymm1, 63
	vpaddq ymm1, ymm1, ymm1
	vpxor ymm1, ymm1, ymm4
	vpermq ymm1, ymm1, 57
	vpermq ymm2, ymm2, 78
	vpermq ymm3, ymm3, 147
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufd ymm3, ymm3, 177
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm14
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm15
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpsrlq ymm4, ymm1, 63
	vpaddq ymm1, ymm1, ymm1
	vpxor ymm1, ymm1, ymm4
	vpermq ymm1, ymm1, 147
	vpermq ymm2, ymm2, 78
	vpermq ymm3, ymm3, 57
	vmovdqu XMMWORD PTR [rcx+1088], xmm0
	vextracti128 xmm4, ymm0, 1
	vmovdqu XMMWORD PTR [rcx+1216], xmm4
	vmovdqu XMMWORD PTR [rcx+1344], xmm1
	vextracti128 xmm4, ymm1, 1
	vmovdqu XMMWORD PTR [rcx+1472], xmm4
	vmovdqu XMMWORD PTR [rcx+1600], xmm2
	vextracti128 xmm4, ymm2, 1
	vmovdqu XMMWORD PTR [rcx+1728], xmm4
	vmovdqu XMMWORD PTR [rcx+1856], xmm3
	vextracti128 xmm4, ymm3, 1
	vmovdqu XMMWORD PTR [rcx+1984], xmm4
	vmovdqu xmm0, XMMWORD PTR [rcx+1104]
	vmovdqu xmm4, XMMWORD PTR [rcx+1232]
	vinserti128 ymm0, ymm0, xmm4, 1
	vmovdqu xmm1, XMMWORD PTR [rcx+1360]
	vmovdqu xmm4, XMMWORD PTR [rcx+1488]
	vinserti128 ymm1, ymm1, xmm4, 1
	vmovdqu xmm2, XMMWORD PTR [rcx+1616]
	vmovdqu xmm4, XMMWORD PTR [rcx+1744]
	vinserti128 ymm2, ymm2, xmm4, 1
	vmovdqu xmm3, XMMWORD PTR [rcx+1872]
	vmovdqu xmm4, XMMWORD PTR [rcx+2000]
	vinserti128 ymm3, ymm3, xmm4, 1
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufd ymm3, ymm3, 177
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm14
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm15
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpsrlq ymm4, ymm1, 63
	vpaddq ymm1, ymm1, ymm1
	vpxor ymm1, ymm1, ymm4
	vpermq ymm1, ymm1, 57
	vpermq ymm2, ymm2, 78
	vpermq ymm3, ymm3, 147
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufd ymm3, ymm3, 177
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm14
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm15
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpsrlq ymm4, ymm1, 63
	vpaddq ymm1, ymm1, ymm1
	vpxor ymm1, ymm1, ymm4
	vpermq ymm1, ymm1, 147
	vpermq ymm2, ymm2, 78
	vpermq ymm3, ymm3, 57
	vmovdqu XMMWORD PTR [rcx+1104], xmm0
	vextracti128 xmm4, ymm0, 1
	vmovdqu XMMWORD PTR [rcx+1232], xmm4
	vmovdqu XMMWORD PTR [rcx+1360], xmm1
	vextracti128 xmm4, ymm1, 1
	vmovdqu XMMWORD PTR [rcx+1488], xmm4
	vmovdqu XMMWORD PTR [rcx+1616], xmm2
	vextracti128 xmm4, ymm2, 1
	vmovdqu XMMWORD PTR [rcx+1744], xmm4
	vmovdqu XMMWORD PTR [rcx+1872], xmm3
	vextracti128 xmm4, ymm3, 1
	vmovdqu XMMWORD PTR [rcx+2000], xmm4
	vmovdqu xmm0, XMMWORD PTR [rcx+1120]
	vmovdqu xmm4, XMMWORD PTR [rcx+1248]
	vinserti128 ymm0, ymm0, xmm4, 1
	vmovdqu xmm1, XMMWORD PTR [rcx+1376]
	vmovdqu xmm4, XMMWORD PTR [rcx+1504]
	vinserti128 ymm1, ymm1, xmm4, 1
	vmovdqu xmm2, XMMWORD PTR [rcx+1632]
	vmovdqu xmm4, XMMWORD PTR [rcx+1760]
	vinserti128 ymm2, ymm2, xmm4, 1
	vmovdqu xmm3, XMMWORD PTR [rcx+1888]
	vmovdqu xmm4, XMMWORD PTR [rcx+2016]
	vinserti128 ymm3, ymm3, xmm4, 1
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufd ymm3, ymm3, 177
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm14
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm15
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpsrlq ymm4, ymm1, 63
	vpaddq ymm1, ymm1, ymm1
	vpxor ymm1, ymm1, ymm4
	vpermq ymm1, ymm1, 57
	vpermq ymm2, ymm2, 78
	vpermq ymm3, ymm3, 147
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufd ymm3, ymm3, 177
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm14
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm15
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpsrlq ymm4, ymm1, 63
	vpaddq ymm1, ymm1, ymm1
	vpxor ymm1, ymm1, ymm4
	vpermq ymm1, ymm1, 147
	vpermq ymm2, ymm2, 78
	vpermq ymm3, ymm3, 57
	vmovdqu XMMWORD PTR [rcx+1120], xmm0
	vextracti128 xmm4, ymm0, 1
	vmovdqu XMMWORD PTR [rcx+1248], xmm4
	vmovdqu XMMWORD PTR [rcx+1376], xmm1
	vextracti128 xmm4, ymm1, 1
	vmovdqu XMMWORD PTR [rcx+1504], xmm4
	vmovdqu XMMWORD PTR [rcx+1632], xmm2
	vextracti128 xmm4, ymm2, 1
	vmovdqu XMMWORD PTR [rcx+1760], xmm4
	vmovdqu XMMWORD PTR [rcx+1888], xmm3
	vextracti128 xmm4, ymm3, 1
	vmovdqu XMMWORD PTR [rcx+2016], xmm4
	vmovdqu xmm0, XMMWORD PTR [rcx+1136]
	vmovdqu xmm4, XMMWORD PTR [rcx+1264]
	vinserti128 ymm0, ymm0, xmm4, 1
	vmovdqu xmm1, XMMWORD PTR [rcx+1392]
	vmovdqu xmm4, XMMWORD PTR [rcx+1520]
	vinserti128 ymm1, ymm1, xmm4, 1
	vmovdqu xmm2, XMMWORD PTR [rcx+1648]
	vmovdqu xmm4, XMMWORD PTR [rcx+1776]
	vinserti128 ymm2, ymm2, xmm4, 1
	vmovdqu xmm3, XMMWORD PTR [rcx+1904]
	vmovdqu xmm4, XMMWORD PTR [rcx+2032]
	vinserti128 ymm3, ymm3, xmm4, 1
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufd ymm3, ymm3, 177
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm14
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm15
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpsrlq ymm4, ymm1, 63
	vpaddq ymm1, ymm1, ymm1
	vpxor ymm1, ymm1, ymm4
	vpermq ymm1, ymm1, 57
	vpermq ymm2, ymm2, 78
	vpermq ymm3, ymm3, 147
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufd ymm3, ymm3, 177
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm14
	vpmuludq ymm4, ymm0, ymm1
	vpaddq ymm0, ymm0, ymm1
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm0, ymm0, ymm4
	vpxor ymm3, ymm3, ymm0
	vpshufb ymm3, ymm3, ymm15
	vpmuludq ymm4, ymm2, ymm3
	vpaddq ymm2, ymm2, ymm3
	vpaddq ymm4, ymm4, ymm4
	vpaddq ymm2, ymm2, ymm4
	vpxor ymm1, ymm1, ymm2
	vpsrlq ymm4, ymm1, 63
	vpaddq ymm1, ymm1, ymm1
	vpxor ymm1, ymm1, ymm4
	vpermq ymm1, ymm1, 147
	vpermq ymm2, ymm2, 78
	vpermq ymm3, ymm3, 57
	vmovdqu XMMWORD PTR [rcx+1136], xmm0
	vextracti128 xmm4, ymm0, 1
	vmovdqu XMMWORD PTR [rcx+1264], xmm4
	vmovdqu XMMWORD PTR [rcx+1392], xmm1
	vextracti128 xmm4, ymm1, 1
	vmovdqu XMMWORD PTR [rcx+1520], xmm4
	vmovdqu XMMWORD PTR [rcx+1648], xmm2
	vextracti128 xmm4, ymm2, 1
	vmovdqu XMMWORD PTR [rcx+1776], xmm4
	vmovdqu XMMWORD PTR [rcx+1904], xmm3
	vextracti128 xmm4, ymm3, 1
	vmovdqu XMMWORD PTR [rcx+2032], xmm4
	vmovdqu ymm0, YMMWORD PTR [rcx+1024]
	vmovdqu ymm1, YMMWORD PTR [rcx]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdx], ymm0
	vmovdqu ymm0, YMMWORD PTR [rcx+1056]
	vmovdqu ymm1, YMMWORD PTR [rcx+32]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdx+32], ymm0
	vmovdqu ymm0, YMMWORD PTR [rcx+1088]
	vmovdqu ymm1, YMMWORD PTR [rcx+64]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdx+64], ymm0
	vmovdqu ymm0, YMMWORD PTR [rcx+1120]
	vmovdqu ymm1, YMMWORD PTR [rcx+96]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdx+96], ymm0
	vmovdqu ymm0, YMMWORD PTR [rcx+1152]
	vmovdqu ymm1, YMMWORD PTR [rcx+128]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdx+128], ymm0
	vmovdqu ymm0, YMMWORD PTR [rcx+1184]
	vmovdqu ymm1, YMMWORD PTR [rcx+160]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdx+160], ymm0
	vmovdqu ymm0, YMMWORD PTR [rcx+1216]
	vmovdqu ymm1, YMMWORD PTR [rcx+192]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdx+192], ymm0
	vmovdqu ymm0, YMMWORD PTR [rcx+1248]
	vmovdqu ymm1, YMMWORD PTR [rcx+224]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdx+224], ymm0
	vmovdqu ymm0, YMMWORD PTR [rcx+1280]
	vmovdqu ymm1, YMMWORD PTR [rcx+256]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdx+256], ymm0
	vmovdqu ymm0, YMMWORD PTR [rcx+1312]
	vmovdqu ymm1, YMMWORD PTR [rcx+288]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdx+288], ymm0
	vmovdqu ymm0, YMMWORD PTR [rcx+1344]
	vmovdqu ymm1, YMMWORD PTR [rcx+320]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdx+320], ymm0
	vmovdqu ymm0, YMMWORD PTR [rcx+1376]
	vmovdqu ymm1, YMMWORD PTR [rcx+352]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdx+352], ymm0
	vmovdqu ymm0, YMMWORD PTR [rcx+1408]
	vmovdqu ymm1, YMMWORD PTR [rcx+384]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdx+384], ymm0
	vmovdqu ymm0, YMMWORD PTR [rcx+1440]
	vmovdqu ymm1, YMMWORD PTR [rcx+416]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdx+416], ymm0
	vmovdqu ymm0, YMMWORD PTR [rcx+1472]
	vmovdqu ymm1, YMMWORD PTR [rcx+448]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdx+448], ymm0
	vmovdqu ymm0, YMMWORD PTR [rcx+1504]
	vmovdqu ymm1, YMMWORD PTR [rcx+480]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdx+480], ymm0
	vmovdqu ymm0, YMMWORD PTR [rcx+1536]
	vmovdqu ymm1, YMMWORD PTR [rcx+512]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdx+512], ymm0
	vmovdqu ymm0, YMMWORD PTR [rcx+1568]
	vmovdqu ymm1, YMMWORD PTR [rcx+544]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdx+544], ymm0
	vmovdqu ymm0, YMMWORD PTR [rcx+1600]
	vmovdqu ymm1, YMMWORD PTR [rcx+576]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdx+576], ymm0
	vmovdqu ymm0, YMMWORD PTR [rcx+1632]
	vmovdqu ymm1, YMMWORD PTR [rcx+608]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdx+608], ymm0
	vmovdqu ymm0, YMMWORD PTR [rcx+1664]
	vmovdqu ymm1, YMMWORD PTR [rcx+640]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdx+640], ymm0
	vmovdqu ymm0, YMMWORD PTR [rcx+1696]
	vmovdqu ymm1, YMMWORD PTR [rcx+672]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdx+672], ymm0
	vmovdqu ymm0, YMMWORD PTR [rcx+1728]
	vmovdqu ymm1, YMMWORD PTR [rcx+704]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdx+704], ymm0
	vmovdqu ymm0, YMMWORD PTR [rcx+1760]
	vmovdqu ymm1, YMMWORD PTR [rcx+736]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdx+736], ymm0
	vmovdqu ymm0, YMMWORD PTR [rcx+1792]
	vmovdqu ymm1, YMMWORD PTR [rcx+768]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdx+768], ymm0
	vmovdqu ymm0, YMMWORD PTR [rcx+1824]
	vmovdqu ymm1, YMMWORD PTR [rcx+800]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdx+800], ymm0
	vmovdqu ymm0, YMMWORD PTR [rcx+1856]
	vmovdqu ymm1, YMMWORD PTR [rcx+832]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdx+832], ymm0
	vmovdqu ymm0, YMMWORD PTR [rcx+1888]
	vmovdqu ymm1, YMMWORD PTR [rcx+864]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdx+864], ymm0
	vmovdqu ymm0, YMMWORD PTR [rcx+1920]
	vmovdqu ymm1, YMMWORD PTR [rcx+896]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdx+896], ymm0
	vmovdqu ymm0, YMMWORD PTR [rcx+1952]
	vmovdqu ymm1, YMMWORD PTR [rcx+928]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdx+928], ymm0
	vmovdqu ymm0, YMMWORD PTR [rcx+1984]
	vmovdqu ymm1, YMMWORD PTR [rcx+960]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdx+960], ymm0
	vmovdqu ymm0, YMMWORD PTR [rcx+2016]
	vmovdqu ymm1, YMMWORD PTR [rcx+992]
	vpxor ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdx+992], ymm0
	vzeroupper
	lfence
	mov DWORD PTR [rcx+2048], r11d
	ldmxcsr DWORD PTR [rcx+2048]
	ret
	.p2align 6
