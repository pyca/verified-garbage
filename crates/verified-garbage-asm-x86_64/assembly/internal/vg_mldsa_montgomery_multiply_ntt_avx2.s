// The functions of `src/internal/vg_mldsa_montgomery_multiply_ntt_avx2.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_montgomery_multiply_ntt_avx2:
	mov r8, rdi
	vmovdqu ymm6, YMMWORD PTR [rdi+992]
	stmxcsr DWORD PTR [r8+1016]
	mov r11d, DWORD PTR [r8+1016]
	and r11d, 65535
	mov eax, 8127
	mov DWORD PTR [r8+1020], eax
	ldmxcsr DWORD PTR [r8+1020]
	lfence
	mov eax, 8380417
	vmovq xmm15, rax
	vpbroadcastd ymm15, xmm15
	mov eax, -58728449
	vmovq xmm14, rax
	vpbroadcastd ymm14, xmm14
	mov eax, 2365951
	vmovq xmm11, rax
	vpbroadcastd ymm11, xmm11
	mov ecx, 31
20:
	vmovdqu ymm3, YMMWORD PTR [rsi]
	vmovdqu ymm13, YMMWORD PTR [rdx]
	vmovdqu ymm5, YMMWORD PTR [rdi]
	vpshufd ymm12, ymm13, 245
	vpshufd ymm4, ymm3, 245
	vpmuludq ymm3, ymm3, ymm13
	vpmuludq ymm4, ymm4, ymm12
	vpmuludq ymm2, ymm3, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm3, ymm3, ymm2
	vpsrlq ymm3, ymm3, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm3, ymm3, ymm4
	vpsubd ymm3, ymm3, ymm15
	vpsrad ymm2, ymm3, 31
	vpand ymm2, ymm2, ymm15
	vpaddd ymm3, ymm3, ymm2
	vmovdqu YMMWORD PTR [rdi], ymm3
	add rdi, 32
	add rsi, 32
	add rdx, 32
	sub rcx, 1
	jne 20b
	vmovdqu ymm3, YMMWORD PTR [rsi]
	vmovdqu ymm13, YMMWORD PTR [rdx]
	vmovdqa ymm5, ymm6
	vpshufd ymm12, ymm13, 245
	vpshufd ymm4, ymm3, 245
	vpmuludq ymm3, ymm3, ymm13
	vpmuludq ymm4, ymm4, ymm12
	vpmuludq ymm2, ymm3, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm3, ymm3, ymm2
	vpsrlq ymm3, ymm3, 32
	vpmuludq ymm2, ymm4, ymm14
	vpmuludq ymm2, ymm2, ymm15
	vpaddq ymm4, ymm4, ymm2
	vpor ymm3, ymm3, ymm4
	vpsubd ymm3, ymm3, ymm15
	vpsrad ymm2, ymm3, 31
	vpand ymm2, ymm2, ymm15
	vpaddd ymm3, ymm3, ymm2
	lfence
	mov DWORD PTR [r8+1016], r11d
	ldmxcsr DWORD PTR [r8+1016]
	vmovdqu YMMWORD PTR [rdi], ymm3
	vzeroupper
	ret
	.p2align 6
