// The functions of `src/internal/vg_mldsa_norm_lt_avx2.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_norm_lt_avx2:
	mov esi, esi
	cmp esi, 8380417
	jb 20f
	mov esi, 8380417
	jmp 21f
20:
21:
	mov eax, esi
	vmovq xmm8, rax
	vpbroadcastd ymm8, xmm8
	mov eax, 8380417
	sub eax, esi
	vmovq xmm9, rax
	vpbroadcastd ymm9, xmm9
	mov eax, -1
	vmovq xmm10, rax
	vpbroadcastd ymm10, xmm10
	mov ecx, 32
22:
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpsubd ymm1, ymm0, ymm8
	vpsubd ymm2, ymm9, ymm0
	vpor ymm1, ymm1, ymm2
	vpand ymm10, ymm10, ymm1
	add rdi, 32
	sub rcx, 1
	jne 22b
	vpsrad ymm10, ymm10, 31
	vpmovmskb eax, ymm10
	vzeroupper
	add rax, 1
	shr rax, 32
	ret
	.p2align 6
