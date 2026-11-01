// The functions of `src/internal/vg_mldsa_low_bits_avx2.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_low_bits_avx2:
	mov esi, esi
	cmp esi, 261888
	mov r10, rdx
	je 20f
	mov eax, 127
	vmovq xmm8, rax
	vpbroadcastd ymm8, xmm8
	mov eax, 8388608
	vmovq xmm9, rax
	vpbroadcastd ymm9, xmm9
	mov eax, 44
	vmovq xmm10, rax
	vpbroadcastd ymm10, xmm10
	mov eax, 8380417
	vmovq xmm15, rax
	vpbroadcastd ymm15, xmm15
	mov ecx, 32
22:
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vmovdqa ymm3, ymm0
	vpaddd ymm0, ymm0, ymm8
	vpsrld ymm0, ymm0, 7
	vmovdqa ymm1, ymm0
	vpslld ymm2, ymm1, 1
	vpaddd ymm0, ymm0, ymm2
	vpslld ymm2, ymm1, 3
	vpaddd ymm0, ymm0, ymm2
	vpslld ymm2, ymm1, 10
	vpaddd ymm0, ymm0, ymm2
	vpslld ymm2, ymm1, 11
	vpaddd ymm0, ymm0, ymm2
	vpslld ymm2, ymm1, 13
	vpaddd ymm0, ymm0, ymm2
	vpaddd ymm0, ymm0, ymm9
	vpsrld ymm0, ymm0, 24
	vpsubd ymm1, ymm0, ymm10
	vpsrad ymm1, ymm1, 31
	vpand ymm0, ymm0, ymm1
	vpslld ymm1, ymm0, 11
	vpslld ymm2, ymm0, 13
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 14
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 15
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 17
	vpaddd ymm1, ymm1, ymm2
	vpsubd ymm3, ymm3, ymm1
	vpsrad ymm1, ymm3, 31
	vpand ymm1, ymm1, ymm15
	vpaddd ymm3, ymm3, ymm1
	vmovdqu YMMWORD PTR [r10], ymm3
	add rdi, 32
	add r10, 32
	sub rcx, 1
	jne 22b
	jmp 21f
20:
	mov eax, 127
	vmovq xmm8, rax
	vpbroadcastd ymm8, xmm8
	mov eax, 2097152
	vmovq xmm9, rax
	vpbroadcastd ymm9, xmm9
	mov eax, 16
	vmovq xmm10, rax
	vpbroadcastd ymm10, xmm10
	mov eax, 8380417
	vmovq xmm15, rax
	vpbroadcastd ymm15, xmm15
	mov ecx, 32
23:
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vmovdqa ymm3, ymm0
	vpaddd ymm0, ymm0, ymm8
	vpsrld ymm0, ymm0, 7
	vmovdqa ymm1, ymm0
	vpslld ymm2, ymm1, 10
	vpaddd ymm0, ymm0, ymm2
	vpaddd ymm0, ymm0, ymm9
	vpsrld ymm0, ymm0, 22
	vpsubd ymm1, ymm0, ymm10
	vpsrad ymm1, ymm1, 31
	vpand ymm0, ymm0, ymm1
	vpslld ymm1, ymm0, 19
	vpslld ymm2, ymm0, 9
	vpsubd ymm1, ymm1, ymm2
	vpsubd ymm3, ymm3, ymm1
	vpsrad ymm1, ymm3, 31
	vpand ymm1, ymm1, ymm15
	vpaddd ymm3, ymm3, ymm1
	vmovdqu YMMWORD PTR [r10], ymm3
	add rdi, 32
	add r10, 32
	sub rcx, 1
	jne 23b
21:
	vzeroupper
	ret
	.p2align 6
