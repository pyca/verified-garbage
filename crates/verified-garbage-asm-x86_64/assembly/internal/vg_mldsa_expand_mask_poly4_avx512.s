// The functions of `src/internal/vg_mldsa_expand_mask_poly4_avx512.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_expand_mask_poly4_avx512:
	mov QWORD PTR [rcx+5088], rbx
	mov QWORD PTR [rcx+5096], rbp
	mov QWORD PTR [rcx+5104], r12
	mov QWORD PTR [rcx+5112], r13
	mov QWORD PTR [rcx+5120], r14
	mov rbx, rcx
	mov r12, rdi
	mov r13, rdx
	mov r14, rsi
	movabs rax, 1
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+1600], ymm0
	movabs rax, 32898
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+1632], ymm0
	movabs rax, -9223372036854742902
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+1664], ymm0
	movabs rax, -9223372034707259392
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+1696], ymm0
	movabs rax, 32907
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+1728], ymm0
	movabs rax, 2147483649
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+1760], ymm0
	movabs rax, -9223372034707259263
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+1792], ymm0
	movabs rax, -9223372036854743031
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+1824], ymm0
	movabs rax, 138
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+1856], ymm0
	movabs rax, 136
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+1888], ymm0
	movabs rax, 2147516425
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+1920], ymm0
	movabs rax, 2147483658
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+1952], ymm0
	movabs rax, 2147516555
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+1984], ymm0
	movabs rax, -9223372036854775669
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+2016], ymm0
	movabs rax, -9223372036854742903
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+2048], ymm0
	movabs rax, -9223372036854743037
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+2080], ymm0
	movabs rax, -9223372036854743038
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+2112], ymm0
	movabs rax, -9223372036854775680
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+2144], ymm0
	movabs rax, 32778
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+2176], ymm0
	movabs rax, -9223372034707292150
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+2208], ymm0
	movabs rax, -9223372034707259263
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+2240], ymm0
	movabs rax, -9223372036854742912
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+2272], ymm0
	movabs rax, 2147483649
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+2304], ymm0
	movabs rax, -9223372034707259384
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+2336], ymm0
	vpxor ymm0, ymm0, ymm0
	vmovdqu YMMWORD PTR [rbx], ymm0
	vmovdqu YMMWORD PTR [rbx+32], ymm0
	vmovdqu YMMWORD PTR [rbx+64], ymm0
	vmovdqu YMMWORD PTR [rbx+96], ymm0
	vmovdqu YMMWORD PTR [rbx+128], ymm0
	vmovdqu YMMWORD PTR [rbx+160], ymm0
	vmovdqu YMMWORD PTR [rbx+192], ymm0
	vmovdqu YMMWORD PTR [rbx+224], ymm0
	vmovdqu YMMWORD PTR [rbx+256], ymm0
	vmovdqu YMMWORD PTR [rbx+288], ymm0
	vmovdqu YMMWORD PTR [rbx+320], ymm0
	vmovdqu YMMWORD PTR [rbx+352], ymm0
	vmovdqu YMMWORD PTR [rbx+384], ymm0
	vmovdqu YMMWORD PTR [rbx+416], ymm0
	vmovdqu YMMWORD PTR [rbx+448], ymm0
	vmovdqu YMMWORD PTR [rbx+480], ymm0
	vmovdqu YMMWORD PTR [rbx+512], ymm0
	vmovdqu YMMWORD PTR [rbx+544], ymm0
	vmovdqu YMMWORD PTR [rbx+576], ymm0
	vmovdqu YMMWORD PTR [rbx+608], ymm0
	vmovdqu YMMWORD PTR [rbx+640], ymm0
	vmovdqu YMMWORD PTR [rbx+672], ymm0
	vmovdqu YMMWORD PTR [rbx+704], ymm0
	vmovdqu YMMWORD PTR [rbx+736], ymm0
	vmovdqu YMMWORD PTR [rbx+768], ymm0
	mov rax, QWORD PTR [r12]
	mov QWORD PTR [rbx], rax
	mov rax, QWORD PTR [r12+8]
	mov QWORD PTR [rbx+32], rax
	mov rax, QWORD PTR [r12+16]
	mov QWORD PTR [rbx+64], rax
	mov rax, QWORD PTR [r12+24]
	mov QWORD PTR [rbx+96], rax
	mov rax, QWORD PTR [r12+32]
	mov QWORD PTR [rbx+128], rax
	mov rax, QWORD PTR [r12+40]
	mov QWORD PTR [rbx+160], rax
	mov rax, QWORD PTR [r12+48]
	mov QWORD PTR [rbx+192], rax
	mov rax, QWORD PTR [r12+56]
	mov QWORD PTR [rbx+224], rax
	movzx eax, BYTE PTR [r12+64]
	mov BYTE PTR [rbx+256], al
	movzx eax, BYTE PTR [r12+65]
	mov BYTE PTR [rbx+257], al
	mov rax, QWORD PTR [r12+66]
	mov QWORD PTR [rbx+8], rax
	mov rax, QWORD PTR [r12+74]
	mov QWORD PTR [rbx+40], rax
	mov rax, QWORD PTR [r12+82]
	mov QWORD PTR [rbx+72], rax
	mov rax, QWORD PTR [r12+90]
	mov QWORD PTR [rbx+104], rax
	mov rax, QWORD PTR [r12+98]
	mov QWORD PTR [rbx+136], rax
	mov rax, QWORD PTR [r12+106]
	mov QWORD PTR [rbx+168], rax
	mov rax, QWORD PTR [r12+114]
	mov QWORD PTR [rbx+200], rax
	mov rax, QWORD PTR [r12+122]
	mov QWORD PTR [rbx+232], rax
	movzx eax, BYTE PTR [r12+130]
	mov BYTE PTR [rbx+264], al
	movzx eax, BYTE PTR [r12+131]
	mov BYTE PTR [rbx+265], al
	mov rax, QWORD PTR [r12+132]
	mov QWORD PTR [rbx+16], rax
	mov rax, QWORD PTR [r12+140]
	mov QWORD PTR [rbx+48], rax
	mov rax, QWORD PTR [r12+148]
	mov QWORD PTR [rbx+80], rax
	mov rax, QWORD PTR [r12+156]
	mov QWORD PTR [rbx+112], rax
	mov rax, QWORD PTR [r12+164]
	mov QWORD PTR [rbx+144], rax
	mov rax, QWORD PTR [r12+172]
	mov QWORD PTR [rbx+176], rax
	mov rax, QWORD PTR [r12+180]
	mov QWORD PTR [rbx+208], rax
	mov rax, QWORD PTR [r12+188]
	mov QWORD PTR [rbx+240], rax
	movzx eax, BYTE PTR [r12+196]
	mov BYTE PTR [rbx+272], al
	movzx eax, BYTE PTR [r12+197]
	mov BYTE PTR [rbx+273], al
	mov rax, QWORD PTR [r12+198]
	mov QWORD PTR [rbx+24], rax
	mov rax, QWORD PTR [r12+206]
	mov QWORD PTR [rbx+56], rax
	mov rax, QWORD PTR [r12+214]
	mov QWORD PTR [rbx+88], rax
	mov rax, QWORD PTR [r12+222]
	mov QWORD PTR [rbx+120], rax
	mov rax, QWORD PTR [r12+230]
	mov QWORD PTR [rbx+152], rax
	mov rax, QWORD PTR [r12+238]
	mov QWORD PTR [rbx+184], rax
	mov rax, QWORD PTR [r12+246]
	mov QWORD PTR [rbx+216], rax
	mov rax, QWORD PTR [r12+254]
	mov QWORD PTR [rbx+248], rax
	movzx eax, BYTE PTR [r12+262]
	mov BYTE PTR [rbx+280], al
	movzx eax, BYTE PTR [r12+263]
	mov BYTE PTR [rbx+281], al
	mov eax, 31
	mov BYTE PTR [rbx+258], al
	mov BYTE PTR [rbx+266], al
	mov BYTE PTR [rbx+274], al
	mov BYTE PTR [rbx+282], al
	mov eax, 128
	mov BYTE PTR [rbx+519], al
	mov BYTE PTR [rbx+527], al
	mov BYTE PTR [rbx+535], al
	mov BYTE PTR [rbx+543], al
	mov rbp, rbx
	add rbp, 2368
	mov r10d, 5
20:
	mov rdi, rbx
	mov rsi, rbx
	add rsi, 800
	mov rdx, rbx
	add rdx, 1600
	mov rcx, rbx
	add rcx, 2368
	vmovdqu64 ymm0, YMMWORD PTR [rdi]
	vmovdqu64 ymm1, YMMWORD PTR [rdi+32]
	vmovdqu64 ymm2, YMMWORD PTR [rdi+64]
	vmovdqu64 ymm3, YMMWORD PTR [rdi+96]
	vmovdqu64 ymm4, YMMWORD PTR [rdi+128]
	vmovdqu64 ymm5, YMMWORD PTR [rdi+160]
	vmovdqu64 ymm6, YMMWORD PTR [rdi+192]
	vmovdqu64 ymm7, YMMWORD PTR [rdi+224]
	vmovdqu64 ymm8, YMMWORD PTR [rdi+256]
	vmovdqu64 ymm9, YMMWORD PTR [rdi+288]
	vmovdqu64 ymm10, YMMWORD PTR [rdi+320]
	vmovdqu64 ymm11, YMMWORD PTR [rdi+352]
	vmovdqu64 ymm12, YMMWORD PTR [rdi+384]
	vmovdqu64 ymm13, YMMWORD PTR [rdi+416]
	vmovdqu64 ymm14, YMMWORD PTR [rdi+448]
	vmovdqu64 ymm15, YMMWORD PTR [rdi+480]
	vmovdqu64 ymm16, YMMWORD PTR [rdi+512]
	vmovdqu64 ymm17, YMMWORD PTR [rdi+544]
	vmovdqu64 ymm18, YMMWORD PTR [rdi+576]
	vmovdqu64 ymm19, YMMWORD PTR [rdi+608]
	vmovdqu64 ymm20, YMMWORD PTR [rdi+640]
	vmovdqu64 ymm21, YMMWORD PTR [rdi+672]
	vmovdqu64 ymm22, YMMWORD PTR [rdi+704]
	vmovdqu64 ymm23, YMMWORD PTR [rdi+736]
	vmovdqu64 ymm24, YMMWORD PTR [rdi+768]
21:
	vpxorq ymm25, ymm0, ymm5
	vpternlogq ymm25, ymm10, ymm15, 150
	vpxorq ymm25, ymm25, ymm20
	vpxorq ymm26, ymm1, ymm6
	vpternlogq ymm26, ymm11, ymm16, 150
	vpxorq ymm26, ymm26, ymm21
	vpxorq ymm27, ymm2, ymm7
	vpternlogq ymm27, ymm12, ymm17, 150
	vpxorq ymm27, ymm27, ymm22
	vpxorq ymm28, ymm3, ymm8
	vpternlogq ymm28, ymm13, ymm18, 150
	vpxorq ymm28, ymm28, ymm23
	vpxorq ymm29, ymm4, ymm9
	vpternlogq ymm29, ymm14, ymm19, 150
	vpxorq ymm29, ymm29, ymm24
	vprorq ymm30, ymm26, 63
	vpternlogq ymm0, ymm29, ymm30, 150
	vpternlogq ymm5, ymm29, ymm30, 150
	vpternlogq ymm10, ymm29, ymm30, 150
	vpternlogq ymm15, ymm29, ymm30, 150
	vpternlogq ymm20, ymm29, ymm30, 150
	vprorq ymm30, ymm27, 63
	vpternlogq ymm1, ymm25, ymm30, 150
	vpternlogq ymm6, ymm25, ymm30, 150
	vpternlogq ymm11, ymm25, ymm30, 150
	vpternlogq ymm16, ymm25, ymm30, 150
	vpternlogq ymm21, ymm25, ymm30, 150
	vprorq ymm30, ymm28, 63
	vpternlogq ymm2, ymm26, ymm30, 150
	vpternlogq ymm7, ymm26, ymm30, 150
	vpternlogq ymm12, ymm26, ymm30, 150
	vpternlogq ymm17, ymm26, ymm30, 150
	vpternlogq ymm22, ymm26, ymm30, 150
	vprorq ymm30, ymm29, 63
	vpternlogq ymm3, ymm27, ymm30, 150
	vpternlogq ymm8, ymm27, ymm30, 150
	vpternlogq ymm13, ymm27, ymm30, 150
	vpternlogq ymm18, ymm27, ymm30, 150
	vpternlogq ymm23, ymm27, ymm30, 150
	vprorq ymm30, ymm25, 63
	vpternlogq ymm4, ymm28, ymm30, 150
	vpternlogq ymm9, ymm28, ymm30, 150
	vpternlogq ymm14, ymm28, ymm30, 150
	vpternlogq ymm19, ymm28, ymm30, 150
	vpternlogq ymm24, ymm28, ymm30, 150
	vporq ymm30, ymm1, ymm1
	vprorq ymm1, ymm6, 20
	vprorq ymm6, ymm9, 44
	vprorq ymm9, ymm22, 3
	vprorq ymm22, ymm14, 25
	vprorq ymm14, ymm20, 46
	vprorq ymm20, ymm2, 2
	vprorq ymm2, ymm12, 21
	vprorq ymm12, ymm13, 39
	vprorq ymm13, ymm19, 56
	vprorq ymm19, ymm23, 8
	vprorq ymm23, ymm15, 23
	vprorq ymm15, ymm4, 37
	vprorq ymm4, ymm24, 50
	vprorq ymm24, ymm21, 62
	vprorq ymm21, ymm8, 9
	vprorq ymm8, ymm16, 19
	vprorq ymm16, ymm5, 28
	vprorq ymm5, ymm3, 36
	vprorq ymm3, ymm18, 43
	vprorq ymm18, ymm17, 49
	vprorq ymm17, ymm11, 54
	vprorq ymm11, ymm7, 58
	vprorq ymm7, ymm10, 61
	vprorq ymm10, ymm30, 63
	vporq ymm25, ymm0, ymm0
	vporq ymm26, ymm1, ymm1
	vpternlogq ymm0, ymm1, ymm2, 210
	vpternlogq ymm1, ymm2, ymm3, 210
	vpternlogq ymm2, ymm3, ymm4, 210
	vpternlogq ymm3, ymm4, ymm25, 210
	vpternlogq ymm4, ymm25, ymm26, 210
	vporq ymm25, ymm5, ymm5
	vporq ymm26, ymm6, ymm6
	vpternlogq ymm5, ymm6, ymm7, 210
	vpternlogq ymm6, ymm7, ymm8, 210
	vpternlogq ymm7, ymm8, ymm9, 210
	vpternlogq ymm8, ymm9, ymm25, 210
	vpternlogq ymm9, ymm25, ymm26, 210
	vporq ymm25, ymm10, ymm10
	vporq ymm26, ymm11, ymm11
	vpternlogq ymm10, ymm11, ymm12, 210
	vpternlogq ymm11, ymm12, ymm13, 210
	vpternlogq ymm12, ymm13, ymm14, 210
	vpternlogq ymm13, ymm14, ymm25, 210
	vpternlogq ymm14, ymm25, ymm26, 210
	vporq ymm25, ymm15, ymm15
	vporq ymm26, ymm16, ymm16
	vpternlogq ymm15, ymm16, ymm17, 210
	vpternlogq ymm16, ymm17, ymm18, 210
	vpternlogq ymm17, ymm18, ymm19, 210
	vpternlogq ymm18, ymm19, ymm25, 210
	vpternlogq ymm19, ymm25, ymm26, 210
	vporq ymm25, ymm20, ymm20
	vporq ymm26, ymm21, ymm21
	vpternlogq ymm20, ymm21, ymm22, 210
	vpternlogq ymm21, ymm22, ymm23, 210
	vpternlogq ymm22, ymm23, ymm24, 210
	vpternlogq ymm23, ymm24, ymm25, 210
	vpternlogq ymm24, ymm25, ymm26, 210
	vmovdqu64 ymm30, YMMWORD PTR [rdx]
	vpxorq ymm0, ymm0, ymm30
	add rdx, 32
	cmp rdx, rcx
	jne 21b
	vmovdqu64 YMMWORD PTR [rdi], ymm0
	vmovdqu64 YMMWORD PTR [rdi+32], ymm1
	vmovdqu64 YMMWORD PTR [rdi+64], ymm2
	vmovdqu64 YMMWORD PTR [rdi+96], ymm3
	vmovdqu64 YMMWORD PTR [rdi+128], ymm4
	vmovdqu64 YMMWORD PTR [rdi+160], ymm5
	vmovdqu64 YMMWORD PTR [rdi+192], ymm6
	vmovdqu64 YMMWORD PTR [rdi+224], ymm7
	vmovdqu64 YMMWORD PTR [rdi+256], ymm8
	vmovdqu64 YMMWORD PTR [rdi+288], ymm9
	vmovdqu64 YMMWORD PTR [rdi+320], ymm10
	vmovdqu64 YMMWORD PTR [rdi+352], ymm11
	vmovdqu64 YMMWORD PTR [rdi+384], ymm12
	vmovdqu64 YMMWORD PTR [rdi+416], ymm13
	vmovdqu64 YMMWORD PTR [rdi+448], ymm14
	vmovdqu64 YMMWORD PTR [rdi+480], ymm15
	vmovdqu64 YMMWORD PTR [rdi+512], ymm16
	vmovdqu64 YMMWORD PTR [rdi+544], ymm17
	vmovdqu64 YMMWORD PTR [rdi+576], ymm18
	vmovdqu64 YMMWORD PTR [rdi+608], ymm19
	vmovdqu64 YMMWORD PTR [rdi+640], ymm20
	vmovdqu64 YMMWORD PTR [rdi+672], ymm21
	vmovdqu64 YMMWORD PTR [rdi+704], ymm22
	vmovdqu64 YMMWORD PTR [rdi+736], ymm23
	vmovdqu64 YMMWORD PTR [rdi+768], ymm24
	mov rax, QWORD PTR [rbx]
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+32]
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+64]
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+96]
	mov QWORD PTR [rbp+24], rax
	mov rax, QWORD PTR [rbx+128]
	mov QWORD PTR [rbp+32], rax
	mov rax, QWORD PTR [rbx+160]
	mov QWORD PTR [rbp+40], rax
	mov rax, QWORD PTR [rbx+192]
	mov QWORD PTR [rbp+48], rax
	mov rax, QWORD PTR [rbx+224]
	mov QWORD PTR [rbp+56], rax
	mov rax, QWORD PTR [rbx+256]
	mov QWORD PTR [rbp+64], rax
	mov rax, QWORD PTR [rbx+288]
	mov QWORD PTR [rbp+72], rax
	mov rax, QWORD PTR [rbx+320]
	mov QWORD PTR [rbp+80], rax
	mov rax, QWORD PTR [rbx+352]
	mov QWORD PTR [rbp+88], rax
	mov rax, QWORD PTR [rbx+384]
	mov QWORD PTR [rbp+96], rax
	mov rax, QWORD PTR [rbx+416]
	mov QWORD PTR [rbp+104], rax
	mov rax, QWORD PTR [rbx+448]
	mov QWORD PTR [rbp+112], rax
	mov rax, QWORD PTR [rbx+480]
	mov QWORD PTR [rbp+120], rax
	mov rax, QWORD PTR [rbx+512]
	mov QWORD PTR [rbp+128], rax
	mov rax, QWORD PTR [rbx+8]
	mov QWORD PTR [rbp+680], rax
	mov rax, QWORD PTR [rbx+40]
	mov QWORD PTR [rbp+688], rax
	mov rax, QWORD PTR [rbx+72]
	mov QWORD PTR [rbp+696], rax
	mov rax, QWORD PTR [rbx+104]
	mov QWORD PTR [rbp+704], rax
	mov rax, QWORD PTR [rbx+136]
	mov QWORD PTR [rbp+712], rax
	mov rax, QWORD PTR [rbx+168]
	mov QWORD PTR [rbp+720], rax
	mov rax, QWORD PTR [rbx+200]
	mov QWORD PTR [rbp+728], rax
	mov rax, QWORD PTR [rbx+232]
	mov QWORD PTR [rbp+736], rax
	mov rax, QWORD PTR [rbx+264]
	mov QWORD PTR [rbp+744], rax
	mov rax, QWORD PTR [rbx+296]
	mov QWORD PTR [rbp+752], rax
	mov rax, QWORD PTR [rbx+328]
	mov QWORD PTR [rbp+760], rax
	mov rax, QWORD PTR [rbx+360]
	mov QWORD PTR [rbp+768], rax
	mov rax, QWORD PTR [rbx+392]
	mov QWORD PTR [rbp+776], rax
	mov rax, QWORD PTR [rbx+424]
	mov QWORD PTR [rbp+784], rax
	mov rax, QWORD PTR [rbx+456]
	mov QWORD PTR [rbp+792], rax
	mov rax, QWORD PTR [rbx+488]
	mov QWORD PTR [rbp+800], rax
	mov rax, QWORD PTR [rbx+520]
	mov QWORD PTR [rbp+808], rax
	mov rax, QWORD PTR [rbx+16]
	mov QWORD PTR [rbp+1360], rax
	mov rax, QWORD PTR [rbx+48]
	mov QWORD PTR [rbp+1368], rax
	mov rax, QWORD PTR [rbx+80]
	mov QWORD PTR [rbp+1376], rax
	mov rax, QWORD PTR [rbx+112]
	mov QWORD PTR [rbp+1384], rax
	mov rax, QWORD PTR [rbx+144]
	mov QWORD PTR [rbp+1392], rax
	mov rax, QWORD PTR [rbx+176]
	mov QWORD PTR [rbp+1400], rax
	mov rax, QWORD PTR [rbx+208]
	mov QWORD PTR [rbp+1408], rax
	mov rax, QWORD PTR [rbx+240]
	mov QWORD PTR [rbp+1416], rax
	mov rax, QWORD PTR [rbx+272]
	mov QWORD PTR [rbp+1424], rax
	mov rax, QWORD PTR [rbx+304]
	mov QWORD PTR [rbp+1432], rax
	mov rax, QWORD PTR [rbx+336]
	mov QWORD PTR [rbp+1440], rax
	mov rax, QWORD PTR [rbx+368]
	mov QWORD PTR [rbp+1448], rax
	mov rax, QWORD PTR [rbx+400]
	mov QWORD PTR [rbp+1456], rax
	mov rax, QWORD PTR [rbx+432]
	mov QWORD PTR [rbp+1464], rax
	mov rax, QWORD PTR [rbx+464]
	mov QWORD PTR [rbp+1472], rax
	mov rax, QWORD PTR [rbx+496]
	mov QWORD PTR [rbp+1480], rax
	mov rax, QWORD PTR [rbx+528]
	mov QWORD PTR [rbp+1488], rax
	mov rax, QWORD PTR [rbx+24]
	mov QWORD PTR [rbp+2040], rax
	mov rax, QWORD PTR [rbx+56]
	mov QWORD PTR [rbp+2048], rax
	mov rax, QWORD PTR [rbx+88]
	mov QWORD PTR [rbp+2056], rax
	mov rax, QWORD PTR [rbx+120]
	mov QWORD PTR [rbp+2064], rax
	mov rax, QWORD PTR [rbx+152]
	mov QWORD PTR [rbp+2072], rax
	mov rax, QWORD PTR [rbx+184]
	mov QWORD PTR [rbp+2080], rax
	mov rax, QWORD PTR [rbx+216]
	mov QWORD PTR [rbp+2088], rax
	mov rax, QWORD PTR [rbx+248]
	mov QWORD PTR [rbp+2096], rax
	mov rax, QWORD PTR [rbx+280]
	mov QWORD PTR [rbp+2104], rax
	mov rax, QWORD PTR [rbx+312]
	mov QWORD PTR [rbp+2112], rax
	mov rax, QWORD PTR [rbx+344]
	mov QWORD PTR [rbp+2120], rax
	mov rax, QWORD PTR [rbx+376]
	mov QWORD PTR [rbp+2128], rax
	mov rax, QWORD PTR [rbx+408]
	mov QWORD PTR [rbp+2136], rax
	mov rax, QWORD PTR [rbx+440]
	mov QWORD PTR [rbp+2144], rax
	mov rax, QWORD PTR [rbx+472]
	mov QWORD PTR [rbp+2152], rax
	mov rax, QWORD PTR [rbx+504]
	mov QWORD PTR [rbp+2160], rax
	mov rax, QWORD PTR [rbx+536]
	mov QWORD PTR [rbp+2168], rax
	add rbp, 136
	sub r10, 1
	jne 20b
	vzeroupper
	cmp r14d, 131072
	je 22f
	mov rsi, rbx
	add rsi, 2368
	mov rdi, r13
	add rdi, 0
	mov ecx, 64
24:
	mov eax, DWORD PTR [rsi]
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi], edx
	mov eax, DWORD PTR [rsi+2]
	shr eax, 4
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+4], edx
	mov eax, DWORD PTR [rsi+5]
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+8], edx
	mov eax, DWORD PTR [rsi+7]
	shr eax, 4
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+12], edx
	add rsi, 10
	add rdi, 16
	sub rcx, 1
	jne 24b
	mov rsi, rbx
	add rsi, 3048
	mov rdi, r13
	add rdi, 1024
	mov ecx, 64
25:
	mov eax, DWORD PTR [rsi]
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi], edx
	mov eax, DWORD PTR [rsi+2]
	shr eax, 4
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+4], edx
	mov eax, DWORD PTR [rsi+5]
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+8], edx
	mov eax, DWORD PTR [rsi+7]
	shr eax, 4
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+12], edx
	add rsi, 10
	add rdi, 16
	sub rcx, 1
	jne 25b
	mov rsi, rbx
	add rsi, 3728
	mov rdi, r13
	add rdi, 2048
	mov ecx, 64
26:
	mov eax, DWORD PTR [rsi]
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi], edx
	mov eax, DWORD PTR [rsi+2]
	shr eax, 4
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+4], edx
	mov eax, DWORD PTR [rsi+5]
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+8], edx
	mov eax, DWORD PTR [rsi+7]
	shr eax, 4
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+12], edx
	add rsi, 10
	add rdi, 16
	sub rcx, 1
	jne 26b
	mov rsi, rbx
	add rsi, 4408
	mov rdi, r13
	add rdi, 3072
	mov ecx, 64
27:
	mov eax, DWORD PTR [rsi]
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi], edx
	mov eax, DWORD PTR [rsi+2]
	shr eax, 4
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+4], edx
	mov eax, DWORD PTR [rsi+5]
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+8], edx
	mov eax, DWORD PTR [rsi+7]
	shr eax, 4
	and eax, 1048575
	mov edx, 524288
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+12], edx
	add rsi, 10
	add rdi, 16
	sub rcx, 1
	jne 27b
	jmp 23f
22:
	mov rsi, rbx
	add rsi, 2368
	mov rdi, r13
	add rdi, 0
	mov ecx, 64
28:
	mov eax, DWORD PTR [rsi]
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi], edx
	mov eax, DWORD PTR [rsi+2]
	shr eax, 2
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+4], edx
	mov eax, DWORD PTR [rsi+4]
	shr eax, 4
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+8], edx
	mov eax, DWORD PTR [rsi+6]
	shr eax, 6
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+12], edx
	add rsi, 9
	add rdi, 16
	sub rcx, 1
	jne 28b
	mov rsi, rbx
	add rsi, 3048
	mov rdi, r13
	add rdi, 1024
	mov ecx, 64
29:
	mov eax, DWORD PTR [rsi]
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi], edx
	mov eax, DWORD PTR [rsi+2]
	shr eax, 2
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+4], edx
	mov eax, DWORD PTR [rsi+4]
	shr eax, 4
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+8], edx
	mov eax, DWORD PTR [rsi+6]
	shr eax, 6
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+12], edx
	add rsi, 9
	add rdi, 16
	sub rcx, 1
	jne 29b
	mov rsi, rbx
	add rsi, 3728
	mov rdi, r13
	add rdi, 2048
	mov ecx, 64
210:
	mov eax, DWORD PTR [rsi]
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi], edx
	mov eax, DWORD PTR [rsi+2]
	shr eax, 2
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+4], edx
	mov eax, DWORD PTR [rsi+4]
	shr eax, 4
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+8], edx
	mov eax, DWORD PTR [rsi+6]
	shr eax, 6
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+12], edx
	add rsi, 9
	add rdi, 16
	sub rcx, 1
	jne 210b
	mov rsi, rbx
	add rsi, 4408
	mov rdi, r13
	add rdi, 3072
	mov ecx, 64
211:
	mov eax, DWORD PTR [rsi]
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi], edx
	mov eax, DWORD PTR [rsi+2]
	shr eax, 2
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+4], edx
	mov eax, DWORD PTR [rsi+4]
	shr eax, 4
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+8], edx
	mov eax, DWORD PTR [rsi+6]
	shr eax, 6
	and eax, 262143
	mov edx, 131072
	sub edx, eax
	sbb eax, eax
	and eax, 8380417
	add edx, eax
	mov DWORD PTR [rdi+12], edx
	add rsi, 9
	add rdi, 16
	sub rcx, 1
	jne 211b
23:
	mov r14, QWORD PTR [rbx+5120]
	mov r13, QWORD PTR [rbx+5112]
	mov r12, QWORD PTR [rbx+5104]
	mov rbp, QWORD PTR [rbx+5096]
	mov rbx, QWORD PTR [rbx+5088]
	ret
	.p2align 6
