// The functions of `src/internal/vg_mldsa_make_hint_avx2.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_make_hint_avx2:
	mov edx, edx
	cmp edx, 261888
	mov r10, rcx
	mov r9d, 0
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
	mov eax, 63
	vmovq xmm11, rax
	vpbroadcastd ymm11, xmm11
	mov ecx, 32
22:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vmovdqu ymm5, YMMWORD PTR [rdi]
	vmovdqa ymm4, ymm0
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
	vmovdqa ymm3, ymm0
	vpaddd ymm0, ymm4, ymm5
	vpsubd ymm0, ymm0, ymm15
	vpsrad ymm1, ymm0, 31
	vpand ymm1, ymm1, ymm15
	vpaddd ymm0, ymm0, ymm1
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
	vpxor ymm0, ymm0, ymm3
	vpaddd ymm0, ymm0, ymm11
	vpsrld ymm0, ymm0, 6
	vpslld ymm1, ymm0, 7
	vmovdqu YMMWORD PTR [r10], ymm0
	vpmovmskb eax, ymm1
	mov edx, eax
	shr edx, 4
	add eax, edx
	mov edx, eax
	shr edx, 8
	add eax, edx
	mov edx, eax
	shr edx, 16
	add eax, edx
	and eax, 15
	add r9, rax
	add rdi, 32
	add rsi, 32
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
	mov eax, 63
	vmovq xmm11, rax
	vpbroadcastd ymm11, xmm11
	mov ecx, 32
23:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vmovdqu ymm5, YMMWORD PTR [rdi]
	vmovdqa ymm4, ymm0
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
	vmovdqa ymm3, ymm0
	vpaddd ymm0, ymm4, ymm5
	vpsubd ymm0, ymm0, ymm15
	vpsrad ymm1, ymm0, 31
	vpand ymm1, ymm1, ymm15
	vpaddd ymm0, ymm0, ymm1
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
	vpxor ymm0, ymm0, ymm3
	vpaddd ymm0, ymm0, ymm11
	vpsrld ymm0, ymm0, 6
	vpslld ymm1, ymm0, 7
	vmovdqu YMMWORD PTR [r10], ymm0
	vpmovmskb eax, ymm1
	mov edx, eax
	shr edx, 4
	add eax, edx
	mov edx, eax
	shr edx, 8
	add eax, edx
	mov edx, eax
	shr edx, 16
	add eax, edx
	and eax, 15
	add r9, rax
	add rdi, 32
	add rsi, 32
	add r10, 32
	sub rcx, 1
	jne 23b
21:
	mov rax, r9
	vzeroupper
	ret
	.p2align 6
