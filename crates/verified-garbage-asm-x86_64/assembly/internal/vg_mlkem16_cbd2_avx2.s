// The functions of `src/internal/vg_mlkem16_cbd2_avx2.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem16_cbd2_avx2:
	mov eax, 218172673
	vmovq xmm15, rax
	vpbroadcastd ymm15, xmm15
	mov eax, 16711935
	vmovq xmm8, rax
	vpbroadcastd ymm8, xmm8
	mov eax, 5570645
	vmovq xmm9, rax
	vpbroadcastd ymm9, xmm9
	mov eax, 3342387
	vmovq xmm10, rax
	vpbroadcastd ymm10, xmm10
	mov eax, 2228258
	vmovq xmm11, rax
	vpbroadcastd ymm11, xmm11
	mov eax, 983055
	vmovq xmm12, rax
	vpbroadcastd ymm12, xmm12
	mov eax, 131074
	vmovq xmm13, rax
	vpbroadcastd ymm13, xmm13
	mov ecx, 4
20:
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpsrlw ymm1, ymm0, 8
	vpand ymm0, ymm0, ymm8
	vpsrlw ymm2, ymm0, 1
	vpand ymm2, ymm2, ymm9
	vpand ymm0, ymm0, ymm9
	vpaddw ymm0, ymm0, ymm2
	vpsrlw ymm2, ymm0, 2
	vpand ymm2, ymm2, ymm10
	vpand ymm0, ymm0, ymm10
	vpaddw ymm0, ymm0, ymm11
	vpsubw ymm0, ymm0, ymm2
	vpsrlw ymm2, ymm0, 4
	vpand ymm0, ymm0, ymm12
	vpsrlw ymm3, ymm1, 1
	vpand ymm3, ymm3, ymm9
	vpand ymm1, ymm1, ymm9
	vpaddw ymm1, ymm1, ymm3
	vpsrlw ymm3, ymm1, 2
	vpand ymm3, ymm3, ymm10
	vpand ymm1, ymm1, ymm10
	vpaddw ymm1, ymm1, ymm11
	vpsubw ymm1, ymm1, ymm3
	vpsrlw ymm3, ymm1, 4
	vpand ymm1, ymm1, ymm12
	vpunpcklwd ymm4, ymm0, ymm2
	vpunpckhwd ymm0, ymm0, ymm2
	vpunpcklwd ymm2, ymm1, ymm3
	vpunpckhwd ymm1, ymm1, ymm3
	vpunpckldq ymm7, ymm4, ymm2
	vpunpckhdq ymm4, ymm4, ymm2
	vpsubw ymm7, ymm7, ymm13
	vpsraw ymm6, ymm7, 15
	vpand ymm6, ymm6, ymm15
	vpaddw ymm7, ymm7, ymm6
	vpsubw ymm4, ymm4, ymm13
	vpsraw ymm6, ymm4, 15
	vpand ymm6, ymm6, ymm15
	vpaddw ymm4, ymm4, ymm6
	vpunpckldq ymm5, ymm0, ymm1
	vpunpckhdq ymm0, ymm0, ymm1
	vpsubw ymm5, ymm5, ymm13
	vpsraw ymm6, ymm5, 15
	vpand ymm6, ymm6, ymm15
	vpaddw ymm5, ymm5, ymm6
	vpsubw ymm0, ymm0, ymm13
	vpsraw ymm6, ymm0, 15
	vpand ymm6, ymm6, ymm15
	vpaddw ymm0, ymm0, ymm6
	vperm2i128 ymm1, ymm7, ymm4, 32
	vperm2i128 ymm2, ymm5, ymm0, 32
	vperm2i128 ymm3, ymm7, ymm4, 49
	vperm2i128 ymm6, ymm5, ymm0, 49
	vmovdqu YMMWORD PTR [rsi], ymm1
	vmovdqu YMMWORD PTR [rsi+32], ymm2
	vmovdqu YMMWORD PTR [rsi+64], ymm3
	vmovdqu YMMWORD PTR [rsi+96], ymm6
	add rdi, 32
	add rsi, 128
	sub rcx, 1
	jne 20b
	vzeroupper
	ret
	.p2align 6
