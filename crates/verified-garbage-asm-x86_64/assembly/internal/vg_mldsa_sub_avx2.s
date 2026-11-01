// The functions of `src/internal/vg_mldsa_sub_avx2.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_sub_avx2:
	mov eax, 8380417
	vmovq xmm15, rax
	vpbroadcastd ymm15, xmm15
	mov ecx, 32
20:
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vmovdqu ymm1, YMMWORD PTR [rsi]
	vpsubd ymm0, ymm0, ymm1
	vpsrad ymm2, ymm0, 31
	vpand ymm2, ymm2, ymm15
	vpaddd ymm0, ymm0, ymm2
	vmovdqu YMMWORD PTR [rdi], ymm0
	add rdi, 32
	add rsi, 32
	sub rcx, 1
	jne 20b
	vzeroupper
	ret
	.p2align 6
