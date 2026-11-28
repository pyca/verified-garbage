// The functions of `src/internal/vg_slhdsa_shake_thash4_n16_avx512vl.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_slhdsa_shake_thash4_n16_avx512vl:
	vpxor ymm0, ymm0, ymm0
	vmovdqu YMMWORD PTR [r8], ymm0
	vmovdqu YMMWORD PTR [r8+32], ymm0
	vmovdqu YMMWORD PTR [r8+64], ymm0
	vmovdqu YMMWORD PTR [r8+96], ymm0
	vmovdqu YMMWORD PTR [r8+128], ymm0
	vmovdqu YMMWORD PTR [r8+160], ymm0
	vmovdqu YMMWORD PTR [r8+192], ymm0
	vmovdqu YMMWORD PTR [r8+224], ymm0
	vmovdqu YMMWORD PTR [r8+256], ymm0
	vmovdqu YMMWORD PTR [r8+288], ymm0
	vmovdqu YMMWORD PTR [r8+320], ymm0
	vmovdqu YMMWORD PTR [r8+352], ymm0
	vmovdqu YMMWORD PTR [r8+384], ymm0
	vmovdqu YMMWORD PTR [r8+416], ymm0
	vmovdqu YMMWORD PTR [r8+448], ymm0
	vmovdqu YMMWORD PTR [r8+480], ymm0
	vmovdqu YMMWORD PTR [r8+512], ymm0
	vmovdqu YMMWORD PTR [r8+544], ymm0
	vmovdqu YMMWORD PTR [r8+576], ymm0
	vmovdqu YMMWORD PTR [r8+608], ymm0
	vmovdqu YMMWORD PTR [r8+640], ymm0
	vmovdqu YMMWORD PTR [r8+672], ymm0
	vmovdqu YMMWORD PTR [r8+704], ymm0
	vmovdqu YMMWORD PTR [r8+736], ymm0
	vmovdqu YMMWORD PTR [r8+768], ymm0
	mov r9, rdi
	add r9, rsi
	mov r10, r9
	add r10, rsi
	mov r11, r10
	add r11, rsi
	mov esi, 0
	mov ecx, 0
20:
	mov rax, QWORD PTR [rdi+rsi*1]
	xor rax, QWORD PTR [r8+rcx*1]
	mov QWORD PTR [r8+rcx*1], rax
	mov rax, QWORD PTR [r9+rsi*1]
	xor rax, QWORD PTR [r8+rcx*1+8]
	mov QWORD PTR [r8+rcx*1+8], rax
	mov rax, QWORD PTR [r10+rsi*1]
	xor rax, QWORD PTR [r8+rcx*1+16]
	mov QWORD PTR [r8+rcx*1+16], rax
	mov rax, QWORD PTR [r11+rsi*1]
	xor rax, QWORD PTR [r8+rcx*1+24]
	mov QWORD PTR [r8+rcx*1+24], rax
	add rsi, 8
	add rcx, 32
	sub rdx, 8
	cmp rcx, 544
	je 21f
	jmp 22f
21:
	mov QWORD PTR [r8+2368], rdi
	mov QWORD PTR [r8+2376], rdx
	mov QWORD PTR [r8+2384], rsi
	mov rdi, r8
	mov rsi, r8
	add rsi, 800
	mov rdx, r8
	add rdx, 1600
	mov rcx, r8
	add rcx, 2368
	vmovdqu64 ymm0, YMMWORD PTR [rdi]
	vmovdqu64 ymm1, YMMWORD PTR [rdi+32]
	vmovdqu64 ymm16, YMMWORD PTR [rdi+64]
	vmovdqu64 ymm17, YMMWORD PTR [rdi+96]
	vmovdqu64 ymm18, YMMWORD PTR [rdi+128]
	vmovdqu64 ymm19, YMMWORD PTR [rdi+160]
	vmovdqu64 ymm20, YMMWORD PTR [rdi+192]
	vmovdqu64 ymm2, YMMWORD PTR [rdi+224]
	vmovdqu64 ymm3, YMMWORD PTR [rdi+256]
	vmovdqu64 ymm21, YMMWORD PTR [rdi+288]
	vmovdqu64 ymm5, YMMWORD PTR [rdi+320]
	vmovdqu64 ymm22, YMMWORD PTR [rdi+352]
	vmovdqu64 ymm23, YMMWORD PTR [rdi+384]
	vmovdqu64 ymm24, YMMWORD PTR [rdi+416]
	vmovdqu64 ymm4, YMMWORD PTR [rdi+448]
	vmovdqu64 ymm25, YMMWORD PTR [rdi+480]
	vmovdqu64 ymm6, YMMWORD PTR [rdi+512]
	vmovdqu64 ymm7, YMMWORD PTR [rdi+544]
	vmovdqu64 ymm26, YMMWORD PTR [rdi+576]
	vmovdqu64 ymm27, YMMWORD PTR [rdi+608]
	vmovdqu64 ymm28, YMMWORD PTR [rdi+640]
	vmovdqu64 ymm29, YMMWORD PTR [rdi+672]
	vmovdqu64 ymm30, YMMWORD PTR [rdi+704]
	vmovdqu64 ymm8, YMMWORD PTR [rdi+736]
	vmovdqu64 ymm9, YMMWORD PTR [rdi+768]
23:
	vmovdqa ymm10, ymm0
	vpternlogq ymm10, ymm19, ymm5, 150
	vpternlogq ymm10, ymm25, ymm28, 150
	vmovdqa ymm11, ymm1
	vpternlogq ymm11, ymm20, ymm22, 150
	vpternlogq ymm11, ymm6, ymm29, 150
	vmovdqa ymm12, ymm2
	vpternlogq ymm12, ymm16, ymm23, 150
	vpternlogq ymm12, ymm7, ymm30, 150
	vmovdqa ymm13, ymm3
	vpternlogq ymm13, ymm17, ymm24, 150
	vpternlogq ymm13, ymm26, ymm8, 150
	vmovdqa ymm14, ymm4
	vpternlogq ymm14, ymm18, ymm21, 150
	vpternlogq ymm14, ymm27, ymm9, 150
	vprorq ymm15, ymm11, 63
	vpternlogq ymm0, ymm14, ymm15, 150
	vpternlogq ymm19, ymm14, ymm15, 150
	vpternlogq ymm5, ymm14, ymm15, 150
	vpternlogq ymm25, ymm14, ymm15, 150
	vpternlogq ymm28, ymm14, ymm15, 150
	vprorq ymm15, ymm12, 63
	vpternlogq ymm1, ymm10, ymm15, 150
	vpternlogq ymm20, ymm10, ymm15, 150
	vpternlogq ymm22, ymm10, ymm15, 150
	vpternlogq ymm6, ymm10, ymm15, 150
	vpternlogq ymm29, ymm10, ymm15, 150
	vprorq ymm15, ymm13, 63
	vpternlogq ymm16, ymm11, ymm15, 150
	vpternlogq ymm2, ymm11, ymm15, 150
	vpternlogq ymm23, ymm11, ymm15, 150
	vpternlogq ymm7, ymm11, ymm15, 150
	vpternlogq ymm30, ymm11, ymm15, 150
	vprorq ymm15, ymm14, 63
	vpternlogq ymm17, ymm12, ymm15, 150
	vpternlogq ymm3, ymm12, ymm15, 150
	vpternlogq ymm24, ymm12, ymm15, 150
	vpternlogq ymm26, ymm12, ymm15, 150
	vpternlogq ymm8, ymm12, ymm15, 150
	vprorq ymm15, ymm10, 63
	vpternlogq ymm18, ymm13, ymm15, 150
	vpternlogq ymm21, ymm13, ymm15, 150
	vpternlogq ymm4, ymm13, ymm15, 150
	vpternlogq ymm27, ymm13, ymm15, 150
	vpternlogq ymm9, ymm13, ymm15, 150
	vmovdqa ymm15, ymm1
	vprorq ymm1, ymm20, 20
	vprorq ymm20, ymm21, 44
	vprorq ymm21, ymm30, 3
	vprorq ymm30, ymm4, 25
	vprorq ymm4, ymm28, 46
	vprorq ymm28, ymm16, 2
	vprorq ymm16, ymm23, 21
	vprorq ymm23, ymm24, 39
	vprorq ymm24, ymm27, 56
	vprorq ymm27, ymm8, 8
	vprorq ymm8, ymm25, 23
	vprorq ymm25, ymm18, 37
	vprorq ymm18, ymm9, 50
	vprorq ymm9, ymm29, 62
	vprorq ymm29, ymm3, 9
	vprorq ymm3, ymm6, 19
	vprorq ymm6, ymm19, 28
	vprorq ymm19, ymm17, 36
	vprorq ymm17, ymm26, 43
	vprorq ymm26, ymm7, 49
	vprorq ymm7, ymm22, 54
	vprorq ymm22, ymm2, 58
	vprorq ymm2, ymm5, 61
	vprorq ymm5, ymm15, 63
	vmovdqa ymm10, ymm0
	vmovdqa ymm11, ymm1
	vpternlogq ymm0, ymm1, ymm16, 210
	vpternlogq ymm1, ymm16, ymm17, 210
	vpternlogq ymm16, ymm17, ymm18, 210
	vpternlogq ymm17, ymm18, ymm10, 210
	vpternlogq ymm18, ymm10, ymm11, 210
	vmovdqa ymm10, ymm2
	vmovdqa ymm11, ymm3
	vpternlogq ymm2, ymm3, ymm21, 210
	vpternlogq ymm3, ymm21, ymm19, 210
	vpternlogq ymm21, ymm19, ymm20, 210
	vpternlogq ymm19, ymm20, ymm10, 210
	vpternlogq ymm20, ymm10, ymm11, 210
	vmovdqa ymm10, ymm4
	vmovdqa ymm11, ymm5
	vpternlogq ymm4, ymm5, ymm22, 210
	vpternlogq ymm5, ymm22, ymm23, 210
	vpternlogq ymm22, ymm23, ymm24, 210
	vpternlogq ymm23, ymm24, ymm10, 210
	vpternlogq ymm24, ymm10, ymm11, 210
	vmovdqa ymm10, ymm6
	vmovdqa ymm11, ymm7
	vpternlogq ymm6, ymm7, ymm26, 210
	vpternlogq ymm7, ymm26, ymm27, 210
	vpternlogq ymm26, ymm27, ymm25, 210
	vpternlogq ymm27, ymm25, ymm10, 210
	vpternlogq ymm25, ymm10, ymm11, 210
	vmovdqa ymm10, ymm8
	vmovdqa ymm11, ymm9
	vpternlogq ymm8, ymm9, ymm28, 210
	vpternlogq ymm9, ymm28, ymm29, 210
	vpternlogq ymm28, ymm29, ymm30, 210
	vpternlogq ymm29, ymm30, ymm10, 210
	vpternlogq ymm30, ymm10, ymm11, 210
	vmovdqu64 ymm15, YMMWORD PTR [rdx]
	vpxorq ymm0, ymm0, ymm15
	add rdx, 32
	cmp rdx, rcx
	jne 23b
	vmovdqu64 YMMWORD PTR [rdi], ymm0
	vmovdqu64 YMMWORD PTR [rdi+32], ymm1
	vmovdqu64 YMMWORD PTR [rdi+64], ymm16
	vmovdqu64 YMMWORD PTR [rdi+96], ymm17
	vmovdqu64 YMMWORD PTR [rdi+128], ymm18
	vmovdqu64 YMMWORD PTR [rdi+160], ymm19
	vmovdqu64 YMMWORD PTR [rdi+192], ymm20
	vmovdqu64 YMMWORD PTR [rdi+224], ymm2
	vmovdqu64 YMMWORD PTR [rdi+256], ymm3
	vmovdqu64 YMMWORD PTR [rdi+288], ymm21
	vmovdqu64 YMMWORD PTR [rdi+320], ymm5
	vmovdqu64 YMMWORD PTR [rdi+352], ymm22
	vmovdqu64 YMMWORD PTR [rdi+384], ymm23
	vmovdqu64 YMMWORD PTR [rdi+416], ymm24
	vmovdqu64 YMMWORD PTR [rdi+448], ymm4
	vmovdqu64 YMMWORD PTR [rdi+480], ymm25
	vmovdqu64 YMMWORD PTR [rdi+512], ymm6
	vmovdqu64 YMMWORD PTR [rdi+544], ymm7
	vmovdqu64 YMMWORD PTR [rdi+576], ymm26
	vmovdqu64 YMMWORD PTR [rdi+608], ymm27
	vmovdqu64 YMMWORD PTR [rdi+640], ymm28
	vmovdqu64 YMMWORD PTR [rdi+672], ymm29
	vmovdqu64 YMMWORD PTR [rdi+704], ymm30
	vmovdqu64 YMMWORD PTR [rdi+736], ymm8
	vmovdqu64 YMMWORD PTR [rdi+768], ymm9
	mov rdi, QWORD PTR [r8+2368]
	mov rdx, QWORD PTR [r8+2376]
	mov rsi, QWORD PTR [r8+2384]
	mov ecx, 0
22:
	test rdx, rdx
	jne 20b
	movabs rsi, -9223372036854775808
	mov rax, QWORD PTR [r8+rcx*1]
	xor rax, 31
	mov QWORD PTR [r8+rcx*1], rax
	mov rax, QWORD PTR [r8+512]
	xor rax, rsi
	mov QWORD PTR [r8+512], rax
	mov rax, QWORD PTR [r8+rcx*1+8]
	xor rax, 31
	mov QWORD PTR [r8+rcx*1+8], rax
	mov rax, QWORD PTR [r8+520]
	xor rax, rsi
	mov QWORD PTR [r8+520], rax
	mov rax, QWORD PTR [r8+rcx*1+16]
	xor rax, 31
	mov QWORD PTR [r8+rcx*1+16], rax
	mov rax, QWORD PTR [r8+528]
	xor rax, rsi
	mov QWORD PTR [r8+528], rax
	mov rax, QWORD PTR [r8+rcx*1+24]
	xor rax, 31
	mov QWORD PTR [r8+rcx*1+24], rax
	mov rax, QWORD PTR [r8+536]
	xor rax, rsi
	mov QWORD PTR [r8+536], rax
	mov QWORD PTR [r8+2368], rdi
	mov QWORD PTR [r8+2376], rdx
	mov QWORD PTR [r8+2384], rsi
	mov rdi, r8
	mov rsi, r8
	add rsi, 800
	mov rdx, r8
	add rdx, 1600
	mov rcx, r8
	add rcx, 2368
	vmovdqu64 ymm0, YMMWORD PTR [rdi]
	vmovdqu64 ymm1, YMMWORD PTR [rdi+32]
	vmovdqu64 ymm16, YMMWORD PTR [rdi+64]
	vmovdqu64 ymm17, YMMWORD PTR [rdi+96]
	vmovdqu64 ymm18, YMMWORD PTR [rdi+128]
	vmovdqu64 ymm19, YMMWORD PTR [rdi+160]
	vmovdqu64 ymm20, YMMWORD PTR [rdi+192]
	vmovdqu64 ymm2, YMMWORD PTR [rdi+224]
	vmovdqu64 ymm3, YMMWORD PTR [rdi+256]
	vmovdqu64 ymm21, YMMWORD PTR [rdi+288]
	vmovdqu64 ymm5, YMMWORD PTR [rdi+320]
	vmovdqu64 ymm22, YMMWORD PTR [rdi+352]
	vmovdqu64 ymm23, YMMWORD PTR [rdi+384]
	vmovdqu64 ymm24, YMMWORD PTR [rdi+416]
	vmovdqu64 ymm4, YMMWORD PTR [rdi+448]
	vmovdqu64 ymm25, YMMWORD PTR [rdi+480]
	vmovdqu64 ymm6, YMMWORD PTR [rdi+512]
	vmovdqu64 ymm7, YMMWORD PTR [rdi+544]
	vmovdqu64 ymm26, YMMWORD PTR [rdi+576]
	vmovdqu64 ymm27, YMMWORD PTR [rdi+608]
	vmovdqu64 ymm28, YMMWORD PTR [rdi+640]
	vmovdqu64 ymm29, YMMWORD PTR [rdi+672]
	vmovdqu64 ymm30, YMMWORD PTR [rdi+704]
	vmovdqu64 ymm8, YMMWORD PTR [rdi+736]
	vmovdqu64 ymm9, YMMWORD PTR [rdi+768]
24:
	vmovdqa ymm10, ymm0
	vpternlogq ymm10, ymm19, ymm5, 150
	vpternlogq ymm10, ymm25, ymm28, 150
	vmovdqa ymm11, ymm1
	vpternlogq ymm11, ymm20, ymm22, 150
	vpternlogq ymm11, ymm6, ymm29, 150
	vmovdqa ymm12, ymm2
	vpternlogq ymm12, ymm16, ymm23, 150
	vpternlogq ymm12, ymm7, ymm30, 150
	vmovdqa ymm13, ymm3
	vpternlogq ymm13, ymm17, ymm24, 150
	vpternlogq ymm13, ymm26, ymm8, 150
	vmovdqa ymm14, ymm4
	vpternlogq ymm14, ymm18, ymm21, 150
	vpternlogq ymm14, ymm27, ymm9, 150
	vprorq ymm15, ymm11, 63
	vpternlogq ymm0, ymm14, ymm15, 150
	vpternlogq ymm19, ymm14, ymm15, 150
	vpternlogq ymm5, ymm14, ymm15, 150
	vpternlogq ymm25, ymm14, ymm15, 150
	vpternlogq ymm28, ymm14, ymm15, 150
	vprorq ymm15, ymm12, 63
	vpternlogq ymm1, ymm10, ymm15, 150
	vpternlogq ymm20, ymm10, ymm15, 150
	vpternlogq ymm22, ymm10, ymm15, 150
	vpternlogq ymm6, ymm10, ymm15, 150
	vpternlogq ymm29, ymm10, ymm15, 150
	vprorq ymm15, ymm13, 63
	vpternlogq ymm16, ymm11, ymm15, 150
	vpternlogq ymm2, ymm11, ymm15, 150
	vpternlogq ymm23, ymm11, ymm15, 150
	vpternlogq ymm7, ymm11, ymm15, 150
	vpternlogq ymm30, ymm11, ymm15, 150
	vprorq ymm15, ymm14, 63
	vpternlogq ymm17, ymm12, ymm15, 150
	vpternlogq ymm3, ymm12, ymm15, 150
	vpternlogq ymm24, ymm12, ymm15, 150
	vpternlogq ymm26, ymm12, ymm15, 150
	vpternlogq ymm8, ymm12, ymm15, 150
	vprorq ymm15, ymm10, 63
	vpternlogq ymm18, ymm13, ymm15, 150
	vpternlogq ymm21, ymm13, ymm15, 150
	vpternlogq ymm4, ymm13, ymm15, 150
	vpternlogq ymm27, ymm13, ymm15, 150
	vpternlogq ymm9, ymm13, ymm15, 150
	vmovdqa ymm15, ymm1
	vprorq ymm1, ymm20, 20
	vprorq ymm20, ymm21, 44
	vprorq ymm21, ymm30, 3
	vprorq ymm30, ymm4, 25
	vprorq ymm4, ymm28, 46
	vprorq ymm28, ymm16, 2
	vprorq ymm16, ymm23, 21
	vprorq ymm23, ymm24, 39
	vprorq ymm24, ymm27, 56
	vprorq ymm27, ymm8, 8
	vprorq ymm8, ymm25, 23
	vprorq ymm25, ymm18, 37
	vprorq ymm18, ymm9, 50
	vprorq ymm9, ymm29, 62
	vprorq ymm29, ymm3, 9
	vprorq ymm3, ymm6, 19
	vprorq ymm6, ymm19, 28
	vprorq ymm19, ymm17, 36
	vprorq ymm17, ymm26, 43
	vprorq ymm26, ymm7, 49
	vprorq ymm7, ymm22, 54
	vprorq ymm22, ymm2, 58
	vprorq ymm2, ymm5, 61
	vprorq ymm5, ymm15, 63
	vmovdqa ymm10, ymm0
	vmovdqa ymm11, ymm1
	vpternlogq ymm0, ymm1, ymm16, 210
	vpternlogq ymm1, ymm16, ymm17, 210
	vpternlogq ymm16, ymm17, ymm18, 210
	vpternlogq ymm17, ymm18, ymm10, 210
	vpternlogq ymm18, ymm10, ymm11, 210
	vmovdqa ymm10, ymm2
	vmovdqa ymm11, ymm3
	vpternlogq ymm2, ymm3, ymm21, 210
	vpternlogq ymm3, ymm21, ymm19, 210
	vpternlogq ymm21, ymm19, ymm20, 210
	vpternlogq ymm19, ymm20, ymm10, 210
	vpternlogq ymm20, ymm10, ymm11, 210
	vmovdqa ymm10, ymm4
	vmovdqa ymm11, ymm5
	vpternlogq ymm4, ymm5, ymm22, 210
	vpternlogq ymm5, ymm22, ymm23, 210
	vpternlogq ymm22, ymm23, ymm24, 210
	vpternlogq ymm23, ymm24, ymm10, 210
	vpternlogq ymm24, ymm10, ymm11, 210
	vmovdqa ymm10, ymm6
	vmovdqa ymm11, ymm7
	vpternlogq ymm6, ymm7, ymm26, 210
	vpternlogq ymm7, ymm26, ymm27, 210
	vpternlogq ymm26, ymm27, ymm25, 210
	vpternlogq ymm27, ymm25, ymm10, 210
	vpternlogq ymm25, ymm10, ymm11, 210
	vmovdqa ymm10, ymm8
	vmovdqa ymm11, ymm9
	vpternlogq ymm8, ymm9, ymm28, 210
	vpternlogq ymm9, ymm28, ymm29, 210
	vpternlogq ymm28, ymm29, ymm30, 210
	vpternlogq ymm29, ymm30, ymm10, 210
	vpternlogq ymm30, ymm10, ymm11, 210
	vmovdqu64 ymm15, YMMWORD PTR [rdx]
	vpxorq ymm0, ymm0, ymm15
	add rdx, 32
	cmp rdx, rcx
	jne 24b
	vmovdqu64 YMMWORD PTR [rdi], ymm0
	vmovdqu64 YMMWORD PTR [rdi+32], ymm1
	vmovdqu64 YMMWORD PTR [rdi+64], ymm16
	vmovdqu64 YMMWORD PTR [rdi+96], ymm17
	vmovdqu64 YMMWORD PTR [rdi+128], ymm18
	vmovdqu64 YMMWORD PTR [rdi+160], ymm19
	vmovdqu64 YMMWORD PTR [rdi+192], ymm20
	vmovdqu64 YMMWORD PTR [rdi+224], ymm2
	vmovdqu64 YMMWORD PTR [rdi+256], ymm3
	vmovdqu64 YMMWORD PTR [rdi+288], ymm21
	vmovdqu64 YMMWORD PTR [rdi+320], ymm5
	vmovdqu64 YMMWORD PTR [rdi+352], ymm22
	vmovdqu64 YMMWORD PTR [rdi+384], ymm23
	vmovdqu64 YMMWORD PTR [rdi+416], ymm24
	vmovdqu64 YMMWORD PTR [rdi+448], ymm4
	vmovdqu64 YMMWORD PTR [rdi+480], ymm25
	vmovdqu64 YMMWORD PTR [rdi+512], ymm6
	vmovdqu64 YMMWORD PTR [rdi+544], ymm7
	vmovdqu64 YMMWORD PTR [rdi+576], ymm26
	vmovdqu64 YMMWORD PTR [rdi+608], ymm27
	vmovdqu64 YMMWORD PTR [rdi+640], ymm28
	vmovdqu64 YMMWORD PTR [rdi+672], ymm29
	vmovdqu64 YMMWORD PTR [rdi+704], ymm30
	vmovdqu64 YMMWORD PTR [rdi+736], ymm8
	vmovdqu64 YMMWORD PTR [rdi+768], ymm9
	mov rdi, QWORD PTR [r8+2368]
	mov rdx, QWORD PTR [r8+2376]
	mov rsi, QWORD PTR [r8+2384]
	mov ecx, 0
	mov rax, QWORD PTR [r8]
	mov QWORD PTR [rdi+48], rax
	mov rax, QWORD PTR [r8+32]
	mov QWORD PTR [rdi+56], rax
	mov rax, QWORD PTR [r8+8]
	mov QWORD PTR [r9+48], rax
	mov rax, QWORD PTR [r8+40]
	mov QWORD PTR [r9+56], rax
	mov rax, QWORD PTR [r8+16]
	mov QWORD PTR [r10+48], rax
	mov rax, QWORD PTR [r8+48]
	mov QWORD PTR [r10+56], rax
	mov rax, QWORD PTR [r8+24]
	mov QWORD PTR [r11+48], rax
	mov rax, QWORD PTR [r8+56]
	mov QWORD PTR [r11+56], rax
	vzeroupper
	ret
	.p2align 6
