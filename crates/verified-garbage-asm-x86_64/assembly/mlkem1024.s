// The functions of `src/mlkem1024.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem1024_keygen_avx512:
	lea rsp, [rsp-16]
	mov QWORD PTR [rsp+8], rcx
	call {vg_mlkem1024_keygen_body_avx512}
	mov QWORD PTR [rsp], rax
	mov rdi, QWORD PTR [rsp+8]
	mov esi, 37376
	call {vg_zeroize_avx_core}
	mov rax, QWORD PTR [rsp]
	lea rsp, [rsp+16]
	ret
	.p2align 6

vg_mlkem1024_encaps_h_avx512:
	lea rsp, [rsp-16]
	mov QWORD PTR [rsp+8], r9
	call {vg_mlkem1024_encaps_h_body_avx512}
	mov QWORD PTR [rsp], rax
	mov rdi, QWORD PTR [rsp+8]
	mov esi, 37376
	call {vg_zeroize_avx_core}
	mov rax, QWORD PTR [rsp]
	lea rsp, [rsp+16]
	ret
	.p2align 6

vg_mlkem1024_encaps_avx512:
	lea rsp, [rsp-16]
	mov QWORD PTR [rsp+8], r8
	call {vg_mlkem1024_encaps_body_avx512}
	mov QWORD PTR [rsp], rax
	mov rdi, QWORD PTR [rsp+8]
	mov esi, 37376
	call {vg_zeroize_avx_core}
	mov rax, QWORD PTR [rsp]
	lea rsp, [rsp+16]
	ret
	.p2align 6

vg_mlkem1024_decaps_avx512:
	lea rsp, [rsp-16]
	mov QWORD PTR [rsp+8], rcx
	call {vg_mlkem1024_decaps_body_avx512}
	mov QWORD PTR [rsp], rax
	mov rdi, QWORD PTR [rsp+8]
	mov esi, 37376
	call {vg_zeroize_avx_core}
	mov rax, QWORD PTR [rsp]
	lea rsp, [rsp+16]
	ret
	.p2align 6

vg_mlkem1024_keygen_avx2:
	lea rsp, [rsp-16]
	mov QWORD PTR [rsp+8], rcx
	call {vg_mlkem1024_keygen_body_avx2}
	mov QWORD PTR [rsp], rax
	mov rdi, QWORD PTR [rsp+8]
	mov esi, 37376
	call {vg_zeroize_avx_core}
	mov rax, QWORD PTR [rsp]
	lea rsp, [rsp+16]
	ret
	.p2align 6

vg_mlkem1024_encaps_h_avx2:
	lea rsp, [rsp-16]
	mov QWORD PTR [rsp+8], r9
	call {vg_mlkem1024_encaps_h_body_avx2}
	mov QWORD PTR [rsp], rax
	mov rdi, QWORD PTR [rsp+8]
	mov esi, 37376
	call {vg_zeroize_avx_core}
	mov rax, QWORD PTR [rsp]
	lea rsp, [rsp+16]
	ret
	.p2align 6

vg_mlkem1024_encaps_avx2:
	lea rsp, [rsp-16]
	mov QWORD PTR [rsp+8], r8
	call {vg_mlkem1024_encaps_body_avx2}
	mov QWORD PTR [rsp], rax
	mov rdi, QWORD PTR [rsp+8]
	mov esi, 37376
	call {vg_zeroize_avx_core}
	mov rax, QWORD PTR [rsp]
	lea rsp, [rsp+16]
	ret
	.p2align 6

vg_mlkem1024_decaps_avx2:
	lea rsp, [rsp-16]
	mov QWORD PTR [rsp+8], rcx
	call {vg_mlkem1024_decaps_body_avx2}
	mov QWORD PTR [rsp], rax
	mov rdi, QWORD PTR [rsp+8]
	mov esi, 37376
	call {vg_zeroize_avx_core}
	mov rax, QWORD PTR [rsp]
	lea rsp, [rsp+16]
	ret
	.p2align 6

vg_mlkem1024_keygen_avx:
	lea rsp, [rsp-16]
	mov QWORD PTR [rsp+8], rcx
	call {vg_mlkem1024_keygen_body}
	mov QWORD PTR [rsp], rax
	mov rdi, QWORD PTR [rsp+8]
	mov esi, 49152
	call {vg_zeroize_avx_core}
	mov rax, QWORD PTR [rsp]
	lea rsp, [rsp+16]
	ret
	.p2align 6

vg_mlkem1024_encaps_h_avx:
	lea rsp, [rsp-16]
	mov QWORD PTR [rsp+8], r9
	call {vg_mlkem1024_encaps_h_body}
	mov QWORD PTR [rsp], rax
	mov rdi, QWORD PTR [rsp+8]
	mov esi, 49152
	call {vg_zeroize_avx_core}
	mov rax, QWORD PTR [rsp]
	lea rsp, [rsp+16]
	ret
	.p2align 6

vg_mlkem1024_encaps_avx:
	lea rsp, [rsp-16]
	mov QWORD PTR [rsp+8], r8
	call {vg_mlkem1024_encaps_body}
	mov QWORD PTR [rsp], rax
	mov rdi, QWORD PTR [rsp+8]
	mov esi, 49152
	call {vg_zeroize_avx_core}
	mov rax, QWORD PTR [rsp]
	lea rsp, [rsp+16]
	ret
	.p2align 6

vg_mlkem1024_decaps_avx:
	lea rsp, [rsp-16]
	mov QWORD PTR [rsp+8], rcx
	call {vg_mlkem1024_decaps_body}
	mov QWORD PTR [rsp], rax
	mov rdi, QWORD PTR [rsp+8]
	mov esi, 49152
	call {vg_zeroize_avx_core}
	mov rax, QWORD PTR [rsp]
	lea rsp, [rsp+16]
	ret
	.p2align 6

vg_mlkem1024_keygen:
	lea rsp, [rsp-16]
	mov QWORD PTR [rsp+8], rcx
	call {vg_mlkem1024_keygen_body}
	mov QWORD PTR [rsp], rax
	mov rdi, QWORD PTR [rsp+8]
	mov esi, 49152
	call {vg_zeroize_core}
	mov rax, QWORD PTR [rsp]
	lea rsp, [rsp+16]
	ret
	.p2align 6

vg_mlkem1024_encaps_h:
	lea rsp, [rsp-16]
	mov QWORD PTR [rsp+8], r9
	call {vg_mlkem1024_encaps_h_body}
	mov QWORD PTR [rsp], rax
	mov rdi, QWORD PTR [rsp+8]
	mov esi, 49152
	call {vg_zeroize_core}
	mov rax, QWORD PTR [rsp]
	lea rsp, [rsp+16]
	ret
	.p2align 6

vg_mlkem1024_encaps:
	lea rsp, [rsp-16]
	mov QWORD PTR [rsp+8], r8
	call {vg_mlkem1024_encaps_body}
	mov QWORD PTR [rsp], rax
	mov rdi, QWORD PTR [rsp+8]
	mov esi, 49152
	call {vg_zeroize_core}
	mov rax, QWORD PTR [rsp]
	lea rsp, [rsp+16]
	ret
	.p2align 6

vg_mlkem1024_decaps:
	lea rsp, [rsp-16]
	mov QWORD PTR [rsp+8], rcx
	call {vg_mlkem1024_decaps_body}
	mov QWORD PTR [rsp], rax
	mov rdi, QWORD PTR [rsp+8]
	mov esi, 49152
	call {vg_zeroize_core}
	mov rax, QWORD PTR [rsp]
	lea rsp, [rsp+16]
	ret
	.p2align 6

vg_mlkem1024_check_ek:
	mov r8d, 0
	mov ecx, 512
20:
	movzx eax, BYTE PTR [rdi]
	movzx edx, BYTE PTR [rdi+1]
	ror edx, 24
	add eax, edx
	movzx edx, BYTE PTR [rdi+2]
	ror edx, 16
	add eax, edx
	mov edx, eax
	and eax, 4095
	shr edx, 12
	cmp eax, 3329
	adc r8, 0
	cmp edx, 3329
	adc r8, 0
	add rdi, 3
	sub rcx, 1
	jne 20b
	cmp r8, 1024
	sbb rax, rax
	add rax, 1
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor edi, edi
	xor r8d, r8d
	ret
	.p2align 6

vg_mlkem1024_check_ek_avx2:
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm8, YMMWORD PTR [rax+1184]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm12, YMMWORD PTR [rax+1216]
	movabs rax, 17179869184
	vmovq xmm9, rax
	vpbroadcastq ymm9, xmm9
	mov eax, 4095
	vmovq xmm10, rax
	vpbroadcastd ymm10, xmm10
	mov eax, 3329
	vmovq xmm11, rax
	vpbroadcastd ymm11, xmm11
	mov eax, -1
	vmovq xmm2, rax
	vpbroadcastd ymm2, xmm2
	mov ecx, 128
20:
	vbroadcasti128 ymm0, XMMWORD PTR [rdi]
	vpshufb ymm0, ymm0, ymm8
	vpsrlvd ymm0, ymm0, ymm9
	vpand ymm0, ymm0, ymm10
	vpsubd ymm0, ymm0, ymm11
	vpand ymm2, ymm2, ymm0
	add rdi, 12
	sub rcx, 1
	jne 20b
	vpsrad ymm2, ymm2, 31
	vpmovmskb eax, ymm2
	add rax, 1
	shr rax, 32
	vzeroupper
	vpxor xmm0, xmm0, xmm0
	vpxor xmm1, xmm1, xmm1
	vpxor xmm2, xmm2, xmm2
	vpxor xmm3, xmm3, xmm3
	vpxor xmm4, xmm4, xmm4
	vpxor xmm5, xmm5, xmm5
	vpxor xmm6, xmm6, xmm6
	vpxor xmm7, xmm7, xmm7
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	vpxor xmm11, xmm11, xmm11
	vpxor xmm12, xmm12, xmm12
	vpxor xmm13, xmm13, xmm13
	vpxor xmm14, xmm14, xmm14
	vpxor xmm15, xmm15, xmm15
	mov eax, eax
	xor ecx, ecx
	xor edi, edi
	ret
	.p2align 6
