// The functions of `src/internal/vg_mlkem768_keygen_body_avx512.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem768_keygen_body_avx512:
	mov QWORD PTR [rcx+840], rbx
	mov QWORD PTR [rcx+848], rbp
	mov QWORD PTR [rcx+856], r12
	mov QWORD PTR [rcx+864], r13
	mov QWORD PTR [rcx+872], r14
	mov QWORD PTR [rcx+880], r15
	mov rbx, rcx
	mov rbp, rdi
	mov r12, rsi
	mov r13, rdx
	mov r15d, 1
	mov eax, 3
	mov BYTE PTR [rbx+896], al
	mov eax, 0
	mov QWORD PTR [rbx], rax
	mov QWORD PTR [rbx+8], rax
	mov QWORD PTR [rbx+16], rax
	mov QWORD PTR [rbx+24], rax
	mov QWORD PTR [rbx+32], rax
	mov QWORD PTR [rbx+40], rax
	mov QWORD PTR [rbx+48], rax
	mov QWORD PTR [rbx+56], rax
	mov QWORD PTR [rbx+64], rax
	mov QWORD PTR [rbx+72], rax
	mov QWORD PTR [rbx+80], rax
	mov QWORD PTR [rbx+88], rax
	mov QWORD PTR [rbx+96], rax
	mov QWORD PTR [rbx+104], rax
	mov QWORD PTR [rbx+112], rax
	mov QWORD PTR [rbx+120], rax
	mov QWORD PTR [rbx+128], rax
	mov QWORD PTR [rbx+136], rax
	mov QWORD PTR [rbx+144], rax
	mov QWORD PTR [rbx+152], rax
	mov QWORD PTR [rbx+160], rax
	mov QWORD PTR [rbx+168], rax
	mov QWORD PTR [rbx+176], rax
	mov QWORD PTR [rbx+184], rax
	mov QWORD PTR [rbx+192], rax
	mov rdi, rbx
	add rdi, 0
	mov esi, 72
	mov edx, 0
	mov rcx, rbp
	add rcx, 0
	mov r8d, 32
	mov r9, rbx
	add r9, 200
	call {vg_keccak_absorb_scratch}
	mov rdi, rbx
	add rdi, 0
	mov esi, 72
	mov edx, 32
	mov rcx, rbx
	add rcx, 896
	mov r8d, 1
	mov r9, rbx
	add r9, 200
	call {vg_keccak_absorb_scratch}
	mov rdi, rbx
	add rdi, 0
	mov esi, 72
	mov edx, 33
	mov ecx, 6
	mov r8, rbx
	add r8, 200
	call {vg_keccak_pad_scratch}
	mov rdi, rbx
	add rdi, 0
	mov esi, 72
	mov edx, 0
	mov rcx, rbx
	add rcx, 1024
	mov r8d, 64
	mov r9, rbx
	add r9, 200
	call {vg_keccak_squeeze_scratch}
	mov rdi, rbx
	add rdi, 904
	mov rsi, rbx
	add rsi, 1024
	mov ecx, 4
20:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 20b
	mov r8, rbx
	add r8, 20736
	mov r9d, 2
	mov r10d, 1
21:
	movabs rax, 1
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+13888], ymm0
	movabs rax, 32898
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+13920], ymm0
	movabs rax, -9223372036854742902
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+13952], ymm0
	movabs rax, -9223372034707259392
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+13984], ymm0
	movabs rax, 32907
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+14016], ymm0
	movabs rax, 2147483649
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+14048], ymm0
	movabs rax, -9223372034707259263
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+14080], ymm0
	movabs rax, -9223372036854743031
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+14112], ymm0
	movabs rax, 138
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+14144], ymm0
	movabs rax, 136
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+14176], ymm0
	movabs rax, 2147516425
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+14208], ymm0
	movabs rax, 2147483658
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+14240], ymm0
	movabs rax, 2147516555
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+14272], ymm0
	movabs rax, -9223372036854775669
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+14304], ymm0
	movabs rax, -9223372036854742903
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+14336], ymm0
	movabs rax, -9223372036854743037
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+14368], ymm0
	movabs rax, -9223372036854743038
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+14400], ymm0
	movabs rax, -9223372036854775680
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+14432], ymm0
	movabs rax, 32778
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+14464], ymm0
	movabs rax, -9223372034707292150
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+14496], ymm0
	movabs rax, -9223372034707259263
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+14528], ymm0
	movabs rax, -9223372036854742912
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+14560], ymm0
	movabs rax, 2147483649
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+14592], ymm0
	movabs rax, -9223372034707259384
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+14624], ymm0
	vpxor ymm0, ymm0, ymm0
	vmovdqu YMMWORD PTR [rbx+12288], ymm0
	vmovdqu YMMWORD PTR [rbx+12320], ymm0
	vmovdqu YMMWORD PTR [rbx+12352], ymm0
	vmovdqu YMMWORD PTR [rbx+12384], ymm0
	vmovdqu YMMWORD PTR [rbx+12416], ymm0
	vmovdqu YMMWORD PTR [rbx+12448], ymm0
	vmovdqu YMMWORD PTR [rbx+12480], ymm0
	vmovdqu YMMWORD PTR [rbx+12512], ymm0
	vmovdqu YMMWORD PTR [rbx+12544], ymm0
	vmovdqu YMMWORD PTR [rbx+12576], ymm0
	vmovdqu YMMWORD PTR [rbx+12608], ymm0
	vmovdqu YMMWORD PTR [rbx+12640], ymm0
	vmovdqu YMMWORD PTR [rbx+12672], ymm0
	vmovdqu YMMWORD PTR [rbx+12704], ymm0
	vmovdqu YMMWORD PTR [rbx+12736], ymm0
	vmovdqu YMMWORD PTR [rbx+12768], ymm0
	vmovdqu YMMWORD PTR [rbx+12800], ymm0
	vmovdqu YMMWORD PTR [rbx+12832], ymm0
	vmovdqu YMMWORD PTR [rbx+12864], ymm0
	vmovdqu YMMWORD PTR [rbx+12896], ymm0
	vmovdqu YMMWORD PTR [rbx+12928], ymm0
	vmovdqu YMMWORD PTR [rbx+12960], ymm0
	vmovdqu YMMWORD PTR [rbx+12992], ymm0
	vmovdqu YMMWORD PTR [rbx+13024], ymm0
	vmovdqu YMMWORD PTR [rbx+13056], ymm0
	mov rax, QWORD PTR [rbx+1056]
	mov QWORD PTR [rbx+12288], rax
	mov QWORD PTR [rbx+12296], rax
	mov QWORD PTR [rbx+12304], rax
	mov QWORD PTR [rbx+12312], rax
	mov rax, QWORD PTR [rbx+1064]
	mov QWORD PTR [rbx+12320], rax
	mov QWORD PTR [rbx+12328], rax
	mov QWORD PTR [rbx+12336], rax
	mov QWORD PTR [rbx+12344], rax
	mov rax, QWORD PTR [rbx+1072]
	mov QWORD PTR [rbx+12352], rax
	mov QWORD PTR [rbx+12360], rax
	mov QWORD PTR [rbx+12368], rax
	mov QWORD PTR [rbx+12376], rax
	mov rax, QWORD PTR [rbx+1080]
	mov QWORD PTR [rbx+12384], rax
	mov QWORD PTR [rbx+12392], rax
	mov QWORD PTR [rbx+12400], rax
	mov QWORD PTR [rbx+12408], rax
	mov rax, r9
	mov BYTE PTR [rbx+12416], al
	add rax, 1
	mov BYTE PTR [rbx+12424], al
	add rax, 1
	mov BYTE PTR [rbx+12432], al
	add rax, 1
	mov BYTE PTR [rbx+12440], al
	add rax, 1
	mov eax, 31
	mov BYTE PTR [rbx+12417], al
	mov BYTE PTR [rbx+12425], al
	mov BYTE PTR [rbx+12433], al
	mov BYTE PTR [rbx+12441], al
	mov eax, 128
	mov BYTE PTR [rbx+12807], al
	mov BYTE PTR [rbx+12815], al
	mov BYTE PTR [rbx+12823], al
	mov BYTE PTR [rbx+12831], al
	mov rdi, rbx
	add rdi, 12288
	mov rsi, rbx
	add rsi, 13088
	mov rdx, rbx
	add rdx, 13888
	mov rcx, rbx
	add rcx, 14656
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
22:
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
	jne 22b
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
	mov rax, QWORD PTR [rbx+12288]
	mov QWORD PTR [r8], rax
	mov rax, QWORD PTR [rbx+12320]
	mov QWORD PTR [r8+8], rax
	mov rax, QWORD PTR [rbx+12352]
	mov QWORD PTR [r8+16], rax
	mov rax, QWORD PTR [rbx+12384]
	mov QWORD PTR [r8+24], rax
	mov rax, QWORD PTR [rbx+12416]
	mov QWORD PTR [r8+32], rax
	mov rax, QWORD PTR [rbx+12448]
	mov QWORD PTR [r8+40], rax
	mov rax, QWORD PTR [rbx+12480]
	mov QWORD PTR [r8+48], rax
	mov rax, QWORD PTR [rbx+12512]
	mov QWORD PTR [r8+56], rax
	mov rax, QWORD PTR [rbx+12544]
	mov QWORD PTR [r8+64], rax
	mov rax, QWORD PTR [rbx+12576]
	mov QWORD PTR [r8+72], rax
	mov rax, QWORD PTR [rbx+12608]
	mov QWORD PTR [r8+80], rax
	mov rax, QWORD PTR [rbx+12640]
	mov QWORD PTR [r8+88], rax
	mov rax, QWORD PTR [rbx+12672]
	mov QWORD PTR [r8+96], rax
	mov rax, QWORD PTR [rbx+12704]
	mov QWORD PTR [r8+104], rax
	mov rax, QWORD PTR [rbx+12736]
	mov QWORD PTR [r8+112], rax
	mov rax, QWORD PTR [rbx+12768]
	mov QWORD PTR [r8+120], rax
	mov rax, QWORD PTR [rbx+12296]
	mov QWORD PTR [r8+128], rax
	mov rax, QWORD PTR [rbx+12328]
	mov QWORD PTR [r8+136], rax
	mov rax, QWORD PTR [rbx+12360]
	mov QWORD PTR [r8+144], rax
	mov rax, QWORD PTR [rbx+12392]
	mov QWORD PTR [r8+152], rax
	mov rax, QWORD PTR [rbx+12424]
	mov QWORD PTR [r8+160], rax
	mov rax, QWORD PTR [rbx+12456]
	mov QWORD PTR [r8+168], rax
	mov rax, QWORD PTR [rbx+12488]
	mov QWORD PTR [r8+176], rax
	mov rax, QWORD PTR [rbx+12520]
	mov QWORD PTR [r8+184], rax
	mov rax, QWORD PTR [rbx+12552]
	mov QWORD PTR [r8+192], rax
	mov rax, QWORD PTR [rbx+12584]
	mov QWORD PTR [r8+200], rax
	mov rax, QWORD PTR [rbx+12616]
	mov QWORD PTR [r8+208], rax
	mov rax, QWORD PTR [rbx+12648]
	mov QWORD PTR [r8+216], rax
	mov rax, QWORD PTR [rbx+12680]
	mov QWORD PTR [r8+224], rax
	mov rax, QWORD PTR [rbx+12712]
	mov QWORD PTR [r8+232], rax
	mov rax, QWORD PTR [rbx+12744]
	mov QWORD PTR [r8+240], rax
	mov rax, QWORD PTR [rbx+12776]
	mov QWORD PTR [r8+248], rax
	mov rax, QWORD PTR [rbx+12304]
	mov QWORD PTR [r8+256], rax
	mov rax, QWORD PTR [rbx+12336]
	mov QWORD PTR [r8+264], rax
	mov rax, QWORD PTR [rbx+12368]
	mov QWORD PTR [r8+272], rax
	mov rax, QWORD PTR [rbx+12400]
	mov QWORD PTR [r8+280], rax
	mov rax, QWORD PTR [rbx+12432]
	mov QWORD PTR [r8+288], rax
	mov rax, QWORD PTR [rbx+12464]
	mov QWORD PTR [r8+296], rax
	mov rax, QWORD PTR [rbx+12496]
	mov QWORD PTR [r8+304], rax
	mov rax, QWORD PTR [rbx+12528]
	mov QWORD PTR [r8+312], rax
	mov rax, QWORD PTR [rbx+12560]
	mov QWORD PTR [r8+320], rax
	mov rax, QWORD PTR [rbx+12592]
	mov QWORD PTR [r8+328], rax
	mov rax, QWORD PTR [rbx+12624]
	mov QWORD PTR [r8+336], rax
	mov rax, QWORD PTR [rbx+12656]
	mov QWORD PTR [r8+344], rax
	mov rax, QWORD PTR [rbx+12688]
	mov QWORD PTR [r8+352], rax
	mov rax, QWORD PTR [rbx+12720]
	mov QWORD PTR [r8+360], rax
	mov rax, QWORD PTR [rbx+12752]
	mov QWORD PTR [r8+368], rax
	mov rax, QWORD PTR [rbx+12784]
	mov QWORD PTR [r8+376], rax
	mov rax, QWORD PTR [rbx+12312]
	mov QWORD PTR [r8+384], rax
	mov rax, QWORD PTR [rbx+12344]
	mov QWORD PTR [r8+392], rax
	mov rax, QWORD PTR [rbx+12376]
	mov QWORD PTR [r8+400], rax
	mov rax, QWORD PTR [rbx+12408]
	mov QWORD PTR [r8+408], rax
	mov rax, QWORD PTR [rbx+12440]
	mov QWORD PTR [r8+416], rax
	mov rax, QWORD PTR [rbx+12472]
	mov QWORD PTR [r8+424], rax
	mov rax, QWORD PTR [rbx+12504]
	mov QWORD PTR [r8+432], rax
	mov rax, QWORD PTR [rbx+12536]
	mov QWORD PTR [r8+440], rax
	mov rax, QWORD PTR [rbx+12568]
	mov QWORD PTR [r8+448], rax
	mov rax, QWORD PTR [rbx+12600]
	mov QWORD PTR [r8+456], rax
	mov rax, QWORD PTR [rbx+12632]
	mov QWORD PTR [r8+464], rax
	mov rax, QWORD PTR [rbx+12664]
	mov QWORD PTR [r8+472], rax
	mov rax, QWORD PTR [rbx+12696]
	mov QWORD PTR [r8+480], rax
	mov rax, QWORD PTR [rbx+12728]
	mov QWORD PTR [r8+488], rax
	mov rax, QWORD PTR [rbx+12760]
	mov QWORD PTR [r8+496], rax
	mov rax, QWORD PTR [rbx+12792]
	mov QWORD PTR [r8+504], rax
	vzeroupper
	add r8, 512
	add r9, 4
	sub r10, 1
	jne 21b
	mov rdi, rbx
	add rdi, 20736
	mov rsi, rbx
	add rsi, 9728
	call {vg_mlkem16_cbd2_avx2}
	mov rdi, rbx
	add rdi, 20864
	mov rsi, rbx
	add rsi, 10240
	call {vg_mlkem16_cbd2_avx2}
	mov rdi, rbx
	add rdi, 20992
	mov rsi, rbx
	add rsi, 10752
	call {vg_mlkem16_cbd2_avx2}
	mov rdi, rbx
	add rdi, 21120
	mov rsi, rbx
	add rsi, 11264
	call {vg_mlkem16_cbd2_avx2}
	mov rdi, rbx
	add rdi, 19208
	mov rsi, rbx
	add rsi, 1056
	mov ecx, 4
23:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 23b
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
24:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 24b
	mov eax, 0
	mov BYTE PTR [rbx+32], al
	mov eax, 0
	mov BYTE PTR [rbx+33], al
	mov rdi, rbx
	add rdi, 34
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
25:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 25b
	mov eax, 1
	mov BYTE PTR [rbx+66], al
	mov eax, 0
	mov BYTE PTR [rbx+67], al
	mov rdi, rbx
	add rdi, 68
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
26:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 26b
	mov eax, 2
	mov BYTE PTR [rbx+100], al
	mov eax, 0
	mov BYTE PTR [rbx+101], al
	mov rdi, rbx
	add rdi, 102
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
27:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 27b
	mov eax, 0
	mov BYTE PTR [rbx+134], al
	mov eax, 1
	mov BYTE PTR [rbx+135], al
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbx
	add rsi, 4096
	mov rdx, rbx
	add rdx, 12288
	mov QWORD PTR [rdx+4384], rbx
	mov QWORD PTR [rdx+4392], rbp
	mov QWORD PTR [rdx+4400], r12
	mov QWORD PTR [rdx+4408], r13
	mov QWORD PTR [rdx+4416], r14
	mov rbx, rdx
	mov r12, rdi
	mov r13, rsi
	mov r14d, 1
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
	movzx eax, BYTE PTR [r12+32]
	mov BYTE PTR [rbx+128], al
	movzx eax, BYTE PTR [r12+33]
	mov BYTE PTR [rbx+129], al
	mov rax, QWORD PTR [r12+34]
	mov QWORD PTR [rbx+8], rax
	mov rax, QWORD PTR [r12+42]
	mov QWORD PTR [rbx+40], rax
	mov rax, QWORD PTR [r12+50]
	mov QWORD PTR [rbx+72], rax
	mov rax, QWORD PTR [r12+58]
	mov QWORD PTR [rbx+104], rax
	movzx eax, BYTE PTR [r12+66]
	mov BYTE PTR [rbx+136], al
	movzx eax, BYTE PTR [r12+67]
	mov BYTE PTR [rbx+137], al
	mov rax, QWORD PTR [r12+68]
	mov QWORD PTR [rbx+16], rax
	mov rax, QWORD PTR [r12+76]
	mov QWORD PTR [rbx+48], rax
	mov rax, QWORD PTR [r12+84]
	mov QWORD PTR [rbx+80], rax
	mov rax, QWORD PTR [r12+92]
	mov QWORD PTR [rbx+112], rax
	movzx eax, BYTE PTR [r12+100]
	mov BYTE PTR [rbx+144], al
	movzx eax, BYTE PTR [r12+101]
	mov BYTE PTR [rbx+145], al
	mov rax, QWORD PTR [r12+102]
	mov QWORD PTR [rbx+24], rax
	mov rax, QWORD PTR [r12+110]
	mov QWORD PTR [rbx+56], rax
	mov rax, QWORD PTR [r12+118]
	mov QWORD PTR [rbx+88], rax
	mov rax, QWORD PTR [r12+126]
	mov QWORD PTR [rbx+120], rax
	movzx eax, BYTE PTR [r12+134]
	mov BYTE PTR [rbx+152], al
	movzx eax, BYTE PTR [r12+135]
	mov BYTE PTR [rbx+153], al
	mov eax, 31
	mov BYTE PTR [rbx+130], al
	mov BYTE PTR [rbx+138], al
	mov BYTE PTR [rbx+146], al
	mov BYTE PTR [rbx+154], al
	mov eax, 128
	mov BYTE PTR [rbx+647], al
	mov BYTE PTR [rbx+655], al
	mov BYTE PTR [rbx+663], al
	mov BYTE PTR [rbx+671], al
	mov r8, rbx
	add r8, 7424
	mov r9d, 7936
	mov rbp, rbx
	add rbp, 2368
	mov r10d, 2
28:
	mov rax, QWORD PTR [rbx+6920]
	mov QWORD PTR [rbx+24], rax
	mov rax, QWORD PTR [rbx+6928]
	mov QWORD PTR [rbx+56], rax
	mov rax, QWORD PTR [rbx+6936]
	mov QWORD PTR [rbx+88], rax
	mov rax, QWORD PTR [rbx+6944]
	mov QWORD PTR [rbx+120], rax
	mov QWORD PTR [rbx+152], r9
	mov eax, 0
	mov QWORD PTR [rbx+184], rax
	mov eax, 0
	mov QWORD PTR [rbx+216], rax
	mov eax, 0
	mov QWORD PTR [rbx+248], rax
	mov eax, 0
	mov QWORD PTR [rbx+280], rax
	mov eax, 0
	mov QWORD PTR [rbx+312], rax
	mov eax, 0
	mov QWORD PTR [rbx+344], rax
	mov eax, 0
	mov QWORD PTR [rbx+376], rax
	mov eax, 0
	mov QWORD PTR [rbx+408], rax
	mov eax, 0
	mov QWORD PTR [rbx+440], rax
	mov eax, 0
	mov QWORD PTR [rbx+472], rax
	mov eax, 0
	mov QWORD PTR [rbx+504], rax
	movabs rax, -9223372036854775808
	mov QWORD PTR [rbx+536], rax
	mov eax, 0
	mov QWORD PTR [rbx+568], rax
	mov eax, 0
	mov QWORD PTR [rbx+600], rax
	mov eax, 0
	mov QWORD PTR [rbx+632], rax
	mov eax, 0
	mov QWORD PTR [rbx+664], rax
	mov eax, 0
	mov QWORD PTR [rbx+696], rax
	mov eax, 0
	mov QWORD PTR [rbx+728], rax
	mov eax, 0
	mov QWORD PTR [rbx+760], rax
	mov eax, 0
	mov QWORD PTR [rbx+792], rax
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
29:
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
	jne 29b
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
	mov rax, QWORD PTR [rbx+544]
	mov QWORD PTR [rbp+136], rax
	mov rax, QWORD PTR [rbx+576]
	mov QWORD PTR [rbp+144], rax
	mov rax, QWORD PTR [rbx+608]
	mov QWORD PTR [rbp+152], rax
	mov rax, QWORD PTR [rbx+640]
	mov QWORD PTR [rbp+160], rax
	mov rax, QWORD PTR [rbx+8]
	mov QWORD PTR [rbp+504], rax
	mov rax, QWORD PTR [rbx+40]
	mov QWORD PTR [rbp+512], rax
	mov rax, QWORD PTR [rbx+72]
	mov QWORD PTR [rbp+520], rax
	mov rax, QWORD PTR [rbx+104]
	mov QWORD PTR [rbp+528], rax
	mov rax, QWORD PTR [rbx+136]
	mov QWORD PTR [rbp+536], rax
	mov rax, QWORD PTR [rbx+168]
	mov QWORD PTR [rbp+544], rax
	mov rax, QWORD PTR [rbx+200]
	mov QWORD PTR [rbp+552], rax
	mov rax, QWORD PTR [rbx+232]
	mov QWORD PTR [rbp+560], rax
	mov rax, QWORD PTR [rbx+264]
	mov QWORD PTR [rbp+568], rax
	mov rax, QWORD PTR [rbx+296]
	mov QWORD PTR [rbp+576], rax
	mov rax, QWORD PTR [rbx+328]
	mov QWORD PTR [rbp+584], rax
	mov rax, QWORD PTR [rbx+360]
	mov QWORD PTR [rbp+592], rax
	mov rax, QWORD PTR [rbx+392]
	mov QWORD PTR [rbp+600], rax
	mov rax, QWORD PTR [rbx+424]
	mov QWORD PTR [rbp+608], rax
	mov rax, QWORD PTR [rbx+456]
	mov QWORD PTR [rbp+616], rax
	mov rax, QWORD PTR [rbx+488]
	mov QWORD PTR [rbp+624], rax
	mov rax, QWORD PTR [rbx+520]
	mov QWORD PTR [rbp+632], rax
	mov rax, QWORD PTR [rbx+552]
	mov QWORD PTR [rbp+640], rax
	mov rax, QWORD PTR [rbx+584]
	mov QWORD PTR [rbp+648], rax
	mov rax, QWORD PTR [rbx+616]
	mov QWORD PTR [rbp+656], rax
	mov rax, QWORD PTR [rbx+648]
	mov QWORD PTR [rbp+664], rax
	mov rax, QWORD PTR [rbx+16]
	mov QWORD PTR [rbp+1008], rax
	mov rax, QWORD PTR [rbx+48]
	mov QWORD PTR [rbp+1016], rax
	mov rax, QWORD PTR [rbx+80]
	mov QWORD PTR [rbp+1024], rax
	mov rax, QWORD PTR [rbx+112]
	mov QWORD PTR [rbp+1032], rax
	mov rax, QWORD PTR [rbx+144]
	mov QWORD PTR [rbp+1040], rax
	mov rax, QWORD PTR [rbx+176]
	mov QWORD PTR [rbp+1048], rax
	mov rax, QWORD PTR [rbx+208]
	mov QWORD PTR [rbp+1056], rax
	mov rax, QWORD PTR [rbx+240]
	mov QWORD PTR [rbp+1064], rax
	mov rax, QWORD PTR [rbx+272]
	mov QWORD PTR [rbp+1072], rax
	mov rax, QWORD PTR [rbx+304]
	mov QWORD PTR [rbp+1080], rax
	mov rax, QWORD PTR [rbx+336]
	mov QWORD PTR [rbp+1088], rax
	mov rax, QWORD PTR [rbx+368]
	mov QWORD PTR [rbp+1096], rax
	mov rax, QWORD PTR [rbx+400]
	mov QWORD PTR [rbp+1104], rax
	mov rax, QWORD PTR [rbx+432]
	mov QWORD PTR [rbp+1112], rax
	mov rax, QWORD PTR [rbx+464]
	mov QWORD PTR [rbp+1120], rax
	mov rax, QWORD PTR [rbx+496]
	mov QWORD PTR [rbp+1128], rax
	mov rax, QWORD PTR [rbx+528]
	mov QWORD PTR [rbp+1136], rax
	mov rax, QWORD PTR [rbx+560]
	mov QWORD PTR [rbp+1144], rax
	mov rax, QWORD PTR [rbx+592]
	mov QWORD PTR [rbp+1152], rax
	mov rax, QWORD PTR [rbx+624]
	mov QWORD PTR [rbp+1160], rax
	mov rax, QWORD PTR [rbx+656]
	mov QWORD PTR [rbp+1168], rax
	mov rax, QWORD PTR [rbx+24]
	mov QWORD PTR [rbp+1512], rax
	mov rax, QWORD PTR [rbx+56]
	mov QWORD PTR [rbp+1520], rax
	mov rax, QWORD PTR [rbx+88]
	mov QWORD PTR [rbp+1528], rax
	mov rax, QWORD PTR [rbx+120]
	mov QWORD PTR [rbp+1536], rax
	mov rax, QWORD PTR [rbx+152]
	mov QWORD PTR [rbp+1544], rax
	mov rax, QWORD PTR [rbx+184]
	mov QWORD PTR [rbp+1552], rax
	mov rax, QWORD PTR [rbx+216]
	mov QWORD PTR [rbp+1560], rax
	mov rax, QWORD PTR [rbx+248]
	mov QWORD PTR [rbp+1568], rax
	mov rax, QWORD PTR [rbx+280]
	mov QWORD PTR [rbp+1576], rax
	mov rax, QWORD PTR [rbx+312]
	mov QWORD PTR [rbp+1584], rax
	mov rax, QWORD PTR [rbx+344]
	mov QWORD PTR [rbp+1592], rax
	mov rax, QWORD PTR [rbx+376]
	mov QWORD PTR [rbp+1600], rax
	mov rax, QWORD PTR [rbx+408]
	mov QWORD PTR [rbp+1608], rax
	mov rax, QWORD PTR [rbx+440]
	mov QWORD PTR [rbp+1616], rax
	mov rax, QWORD PTR [rbx+472]
	mov QWORD PTR [rbp+1624], rax
	mov rax, QWORD PTR [rbx+504]
	mov QWORD PTR [rbp+1632], rax
	mov rax, QWORD PTR [rbx+536]
	mov QWORD PTR [rbp+1640], rax
	mov rax, QWORD PTR [rbx+568]
	mov QWORD PTR [rbp+1648], rax
	mov rax, QWORD PTR [rbx+600]
	mov QWORD PTR [rbp+1656], rax
	mov rax, QWORD PTR [rbx+632]
	mov QWORD PTR [rbp+1664], rax
	mov rax, QWORD PTR [rbx+664]
	mov QWORD PTR [rbp+1672], rax
	mov rax, QWORD PTR [rbx+24]
	mov QWORD PTR [r8], rax
	mov rax, QWORD PTR [rbx+56]
	mov QWORD PTR [r8+8], rax
	mov rax, QWORD PTR [rbx+88]
	mov QWORD PTR [r8+16], rax
	mov rax, QWORD PTR [rbx+120]
	mov QWORD PTR [r8+24], rax
	mov rax, QWORD PTR [rbx+152]
	mov QWORD PTR [r8+32], rax
	mov rax, QWORD PTR [rbx+184]
	mov QWORD PTR [r8+40], rax
	mov rax, QWORD PTR [rbx+216]
	mov QWORD PTR [r8+48], rax
	mov rax, QWORD PTR [rbx+248]
	mov QWORD PTR [r8+56], rax
	mov rax, QWORD PTR [rbx+280]
	mov QWORD PTR [r8+64], rax
	mov rax, QWORD PTR [rbx+312]
	mov QWORD PTR [r8+72], rax
	mov rax, QWORD PTR [rbx+344]
	mov QWORD PTR [r8+80], rax
	mov rax, QWORD PTR [rbx+376]
	mov QWORD PTR [r8+88], rax
	mov rax, QWORD PTR [rbx+408]
	mov QWORD PTR [r8+96], rax
	mov rax, QWORD PTR [rbx+440]
	mov QWORD PTR [r8+104], rax
	mov rax, QWORD PTR [rbx+472]
	mov QWORD PTR [r8+112], rax
	mov rax, QWORD PTR [rbx+504]
	mov QWORD PTR [r8+120], rax
	add r8, 128
	add r9, 1
	add rbp, 168
	sub r10, 1
	jne 28b
	mov rbp, rbx
	add rbp, 2704
	mov r10d, 1
210:
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
211:
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
	jne 211b
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
	mov rax, QWORD PTR [rbx+544]
	mov QWORD PTR [rbp+136], rax
	mov rax, QWORD PTR [rbx+576]
	mov QWORD PTR [rbp+144], rax
	mov rax, QWORD PTR [rbx+608]
	mov QWORD PTR [rbp+152], rax
	mov rax, QWORD PTR [rbx+640]
	mov QWORD PTR [rbp+160], rax
	mov rax, QWORD PTR [rbx+8]
	mov QWORD PTR [rbp+504], rax
	mov rax, QWORD PTR [rbx+40]
	mov QWORD PTR [rbp+512], rax
	mov rax, QWORD PTR [rbx+72]
	mov QWORD PTR [rbp+520], rax
	mov rax, QWORD PTR [rbx+104]
	mov QWORD PTR [rbp+528], rax
	mov rax, QWORD PTR [rbx+136]
	mov QWORD PTR [rbp+536], rax
	mov rax, QWORD PTR [rbx+168]
	mov QWORD PTR [rbp+544], rax
	mov rax, QWORD PTR [rbx+200]
	mov QWORD PTR [rbp+552], rax
	mov rax, QWORD PTR [rbx+232]
	mov QWORD PTR [rbp+560], rax
	mov rax, QWORD PTR [rbx+264]
	mov QWORD PTR [rbp+568], rax
	mov rax, QWORD PTR [rbx+296]
	mov QWORD PTR [rbp+576], rax
	mov rax, QWORD PTR [rbx+328]
	mov QWORD PTR [rbp+584], rax
	mov rax, QWORD PTR [rbx+360]
	mov QWORD PTR [rbp+592], rax
	mov rax, QWORD PTR [rbx+392]
	mov QWORD PTR [rbp+600], rax
	mov rax, QWORD PTR [rbx+424]
	mov QWORD PTR [rbp+608], rax
	mov rax, QWORD PTR [rbx+456]
	mov QWORD PTR [rbp+616], rax
	mov rax, QWORD PTR [rbx+488]
	mov QWORD PTR [rbp+624], rax
	mov rax, QWORD PTR [rbx+520]
	mov QWORD PTR [rbp+632], rax
	mov rax, QWORD PTR [rbx+552]
	mov QWORD PTR [rbp+640], rax
	mov rax, QWORD PTR [rbx+584]
	mov QWORD PTR [rbp+648], rax
	mov rax, QWORD PTR [rbx+616]
	mov QWORD PTR [rbp+656], rax
	mov rax, QWORD PTR [rbx+648]
	mov QWORD PTR [rbp+664], rax
	mov rax, QWORD PTR [rbx+16]
	mov QWORD PTR [rbp+1008], rax
	mov rax, QWORD PTR [rbx+48]
	mov QWORD PTR [rbp+1016], rax
	mov rax, QWORD PTR [rbx+80]
	mov QWORD PTR [rbp+1024], rax
	mov rax, QWORD PTR [rbx+112]
	mov QWORD PTR [rbp+1032], rax
	mov rax, QWORD PTR [rbx+144]
	mov QWORD PTR [rbp+1040], rax
	mov rax, QWORD PTR [rbx+176]
	mov QWORD PTR [rbp+1048], rax
	mov rax, QWORD PTR [rbx+208]
	mov QWORD PTR [rbp+1056], rax
	mov rax, QWORD PTR [rbx+240]
	mov QWORD PTR [rbp+1064], rax
	mov rax, QWORD PTR [rbx+272]
	mov QWORD PTR [rbp+1072], rax
	mov rax, QWORD PTR [rbx+304]
	mov QWORD PTR [rbp+1080], rax
	mov rax, QWORD PTR [rbx+336]
	mov QWORD PTR [rbp+1088], rax
	mov rax, QWORD PTR [rbx+368]
	mov QWORD PTR [rbp+1096], rax
	mov rax, QWORD PTR [rbx+400]
	mov QWORD PTR [rbp+1104], rax
	mov rax, QWORD PTR [rbx+432]
	mov QWORD PTR [rbp+1112], rax
	mov rax, QWORD PTR [rbx+464]
	mov QWORD PTR [rbp+1120], rax
	mov rax, QWORD PTR [rbx+496]
	mov QWORD PTR [rbp+1128], rax
	mov rax, QWORD PTR [rbx+528]
	mov QWORD PTR [rbp+1136], rax
	mov rax, QWORD PTR [rbx+560]
	mov QWORD PTR [rbp+1144], rax
	mov rax, QWORD PTR [rbx+592]
	mov QWORD PTR [rbp+1152], rax
	mov rax, QWORD PTR [rbx+624]
	mov QWORD PTR [rbp+1160], rax
	mov rax, QWORD PTR [rbx+656]
	mov QWORD PTR [rbp+1168], rax
	mov rax, QWORD PTR [rbx+24]
	mov QWORD PTR [rbp+1512], rax
	mov rax, QWORD PTR [rbx+56]
	mov QWORD PTR [rbp+1520], rax
	mov rax, QWORD PTR [rbx+88]
	mov QWORD PTR [rbp+1528], rax
	mov rax, QWORD PTR [rbx+120]
	mov QWORD PTR [rbp+1536], rax
	mov rax, QWORD PTR [rbx+152]
	mov QWORD PTR [rbp+1544], rax
	mov rax, QWORD PTR [rbx+184]
	mov QWORD PTR [rbp+1552], rax
	mov rax, QWORD PTR [rbx+216]
	mov QWORD PTR [rbp+1560], rax
	mov rax, QWORD PTR [rbx+248]
	mov QWORD PTR [rbp+1568], rax
	mov rax, QWORD PTR [rbx+280]
	mov QWORD PTR [rbp+1576], rax
	mov rax, QWORD PTR [rbx+312]
	mov QWORD PTR [rbp+1584], rax
	mov rax, QWORD PTR [rbx+344]
	mov QWORD PTR [rbp+1592], rax
	mov rax, QWORD PTR [rbx+376]
	mov QWORD PTR [rbp+1600], rax
	mov rax, QWORD PTR [rbx+408]
	mov QWORD PTR [rbp+1608], rax
	mov rax, QWORD PTR [rbx+440]
	mov QWORD PTR [rbp+1616], rax
	mov rax, QWORD PTR [rbx+472]
	mov QWORD PTR [rbp+1624], rax
	mov rax, QWORD PTR [rbx+504]
	mov QWORD PTR [rbp+1632], rax
	mov rax, QWORD PTR [rbx+536]
	mov QWORD PTR [rbp+1640], rax
	mov rax, QWORD PTR [rbx+568]
	mov QWORD PTR [rbp+1648], rax
	mov rax, QWORD PTR [rbx+600]
	mov QWORD PTR [rbp+1656], rax
	mov rax, QWORD PTR [rbx+632]
	mov QWORD PTR [rbp+1664], rax
	mov rax, QWORD PTR [rbx+664]
	mov QWORD PTR [rbp+1672], rax
	add rbp, 168
	sub r10, 1
	jne 210b
	lea r11, {VG_MLKEM_SAMPLE_TBL}
	mov rsi, rbx
	add rsi, 2368
	mov edi, 0
	mov rbp, r13
	add rbp, 0
	mov r10d, 10
	vmovdqu ymm8, YMMWORD PTR [r11+4096]
	vmovdqu ymm9, YMMWORD PTR [r11+4128]
	vmovdqu ymm10, YMMWORD PTR [r11+4160]
	vmovdqu ymm12, YMMWORD PTR [r11+6240]
	vmovdqu ymm13, YMMWORD PTR [r11+6272]
	vshufi32x4 zmm12, zmm12, zmm13, 68
	vmovdqu ymm13, YMMWORD PTR [r11+6304]
	vshufi32x4 zmm13, zmm13, zmm13, 0
	vshufi32x4 zmm11, zmm8, zmm8, 0
	vshufi32x4 zmm9, zmm9, zmm9, 0
	vshufi32x4 zmm10, zmm10, zmm10, 0
212:
	cmp rdi, 225
	jb 213f
	cmp rdi, 241
	jb 215f
	cmp rdi, 256
	jb 217f
	add rsi, 24
	jmp 218f
217:
	mov ecx, 8
219:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 220f
	jmp 221f
220:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 222f
	jmp 223f
222:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
223:
221:
	add rsi, 3
	sub rcx, 1
	jne 219b
218:
	jmp 216f
215:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
216:
	cmp rdi, 241
	jb 224f
	cmp rdi, 256
	jb 226f
	add rsi, 24
	jmp 227f
226:
	mov ecx, 8
228:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 229f
	jmp 230f
229:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 231f
	jmp 232f
231:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
232:
230:
	add rsi, 3
	sub rcx, 1
	jne 228b
227:
	jmp 225f
224:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
225:
	jmp 214f
213:
	vmovdqu32 zmm0, ZMMWORD PTR [rsi]
	vpermw zmm0, zmm12, zmm0
	vpshufb zmm0, zmm0, zmm11
	vpsrlvw zmm0, zmm0, zmm13
	vpandq zmm0, zmm0, zmm9
	vpcmpuw k1, zmm0, zmm10, 1
	kmovd eax, k1
	mov edx, eax
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vpshufb xmm1, xmm0, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 8
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 1
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 16
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 2
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 24
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 3
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	add rsi, 48
214:
	sub r10, 1
	jne 212b
	cmp rdi, 241
	jb 233f
	cmp rdi, 256
	jb 235f
	add rsi, 24
	jmp 236f
235:
	mov ecx, 8
237:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 238f
	jmp 239f
238:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 240f
	jmp 241f
240:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
241:
239:
	add rsi, 3
	sub rcx, 1
	jne 237b
236:
	jmp 234f
233:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
234:
	mov QWORD PTR [rbx+4424], rdi
	mov rsi, rbx
	add rsi, 2872
	mov edi, 0
	mov rbp, r13
	add rbp, 512
	mov r10d, 10
	vmovdqu ymm8, YMMWORD PTR [r11+4096]
	vmovdqu ymm9, YMMWORD PTR [r11+4128]
	vmovdqu ymm10, YMMWORD PTR [r11+4160]
	vmovdqu ymm12, YMMWORD PTR [r11+6240]
	vmovdqu ymm13, YMMWORD PTR [r11+6272]
	vshufi32x4 zmm12, zmm12, zmm13, 68
	vmovdqu ymm13, YMMWORD PTR [r11+6304]
	vshufi32x4 zmm13, zmm13, zmm13, 0
	vshufi32x4 zmm11, zmm8, zmm8, 0
	vshufi32x4 zmm9, zmm9, zmm9, 0
	vshufi32x4 zmm10, zmm10, zmm10, 0
242:
	cmp rdi, 225
	jb 243f
	cmp rdi, 241
	jb 245f
	cmp rdi, 256
	jb 247f
	add rsi, 24
	jmp 248f
247:
	mov ecx, 8
249:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 250f
	jmp 251f
250:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 252f
	jmp 253f
252:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
253:
251:
	add rsi, 3
	sub rcx, 1
	jne 249b
248:
	jmp 246f
245:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
246:
	cmp rdi, 241
	jb 254f
	cmp rdi, 256
	jb 256f
	add rsi, 24
	jmp 257f
256:
	mov ecx, 8
258:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 259f
	jmp 260f
259:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 261f
	jmp 262f
261:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
262:
260:
	add rsi, 3
	sub rcx, 1
	jne 258b
257:
	jmp 255f
254:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
255:
	jmp 244f
243:
	vmovdqu32 zmm0, ZMMWORD PTR [rsi]
	vpermw zmm0, zmm12, zmm0
	vpshufb zmm0, zmm0, zmm11
	vpsrlvw zmm0, zmm0, zmm13
	vpandq zmm0, zmm0, zmm9
	vpcmpuw k1, zmm0, zmm10, 1
	kmovd eax, k1
	mov edx, eax
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vpshufb xmm1, xmm0, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 8
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 1
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 16
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 2
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 24
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 3
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	add rsi, 48
244:
	sub r10, 1
	jne 242b
	cmp rdi, 241
	jb 263f
	cmp rdi, 256
	jb 265f
	add rsi, 24
	jmp 266f
265:
	mov ecx, 8
267:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 268f
	jmp 269f
268:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 270f
	jmp 271f
270:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
271:
269:
	add rsi, 3
	sub rcx, 1
	jne 267b
266:
	jmp 264f
263:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
264:
	mov QWORD PTR [rbx+4432], rdi
	mov rsi, rbx
	add rsi, 3376
	mov edi, 0
	mov rbp, r13
	add rbp, 1024
	mov r10d, 10
	vmovdqu ymm8, YMMWORD PTR [r11+4096]
	vmovdqu ymm9, YMMWORD PTR [r11+4128]
	vmovdqu ymm10, YMMWORD PTR [r11+4160]
	vmovdqu ymm12, YMMWORD PTR [r11+6240]
	vmovdqu ymm13, YMMWORD PTR [r11+6272]
	vshufi32x4 zmm12, zmm12, zmm13, 68
	vmovdqu ymm13, YMMWORD PTR [r11+6304]
	vshufi32x4 zmm13, zmm13, zmm13, 0
	vshufi32x4 zmm11, zmm8, zmm8, 0
	vshufi32x4 zmm9, zmm9, zmm9, 0
	vshufi32x4 zmm10, zmm10, zmm10, 0
272:
	cmp rdi, 225
	jb 273f
	cmp rdi, 241
	jb 275f
	cmp rdi, 256
	jb 277f
	add rsi, 24
	jmp 278f
277:
	mov ecx, 8
279:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 280f
	jmp 281f
280:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 282f
	jmp 283f
282:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
283:
281:
	add rsi, 3
	sub rcx, 1
	jne 279b
278:
	jmp 276f
275:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
276:
	cmp rdi, 241
	jb 284f
	cmp rdi, 256
	jb 286f
	add rsi, 24
	jmp 287f
286:
	mov ecx, 8
288:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 289f
	jmp 290f
289:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 291f
	jmp 292f
291:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
292:
290:
	add rsi, 3
	sub rcx, 1
	jne 288b
287:
	jmp 285f
284:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
285:
	jmp 274f
273:
	vmovdqu32 zmm0, ZMMWORD PTR [rsi]
	vpermw zmm0, zmm12, zmm0
	vpshufb zmm0, zmm0, zmm11
	vpsrlvw zmm0, zmm0, zmm13
	vpandq zmm0, zmm0, zmm9
	vpcmpuw k1, zmm0, zmm10, 1
	kmovd eax, k1
	mov edx, eax
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vpshufb xmm1, xmm0, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 8
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 1
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 16
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 2
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 24
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 3
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	add rsi, 48
274:
	sub r10, 1
	jne 272b
	cmp rdi, 241
	jb 293f
	cmp rdi, 256
	jb 295f
	add rsi, 24
	jmp 296f
295:
	mov ecx, 8
297:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 298f
	jmp 299f
298:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2100f
	jmp 2101f
2100:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2101:
299:
	add rsi, 3
	sub rcx, 1
	jne 297b
296:
	jmp 294f
293:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
294:
	mov QWORD PTR [rbx+4440], rdi
	mov r14d, 1
	mov rax, QWORD PTR [rbx+4424]
	shr rax, 8
	and r14d, eax
	mov rax, QWORD PTR [rbx+4432]
	shr rax, 8
	and r14d, eax
	mov rax, QWORD PTR [rbx+4440]
	shr rax, 8
	and r14d, eax
	cmp r14d, 0
	je 2102f
	jmp 2103f
2102:
	mov r14d, 1
	mov rbp, rbx
	add rbp, 2368
	mov r10d, 2
2104:
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
2105:
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
	jne 2105b
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
	mov rax, QWORD PTR [rbx+544]
	mov QWORD PTR [rbp+136], rax
	mov rax, QWORD PTR [rbx+576]
	mov QWORD PTR [rbp+144], rax
	mov rax, QWORD PTR [rbx+608]
	mov QWORD PTR [rbp+152], rax
	mov rax, QWORD PTR [rbx+640]
	mov QWORD PTR [rbp+160], rax
	mov rax, QWORD PTR [rbx+8]
	mov QWORD PTR [rbp+504], rax
	mov rax, QWORD PTR [rbx+40]
	mov QWORD PTR [rbp+512], rax
	mov rax, QWORD PTR [rbx+72]
	mov QWORD PTR [rbp+520], rax
	mov rax, QWORD PTR [rbx+104]
	mov QWORD PTR [rbp+528], rax
	mov rax, QWORD PTR [rbx+136]
	mov QWORD PTR [rbp+536], rax
	mov rax, QWORD PTR [rbx+168]
	mov QWORD PTR [rbp+544], rax
	mov rax, QWORD PTR [rbx+200]
	mov QWORD PTR [rbp+552], rax
	mov rax, QWORD PTR [rbx+232]
	mov QWORD PTR [rbp+560], rax
	mov rax, QWORD PTR [rbx+264]
	mov QWORD PTR [rbp+568], rax
	mov rax, QWORD PTR [rbx+296]
	mov QWORD PTR [rbp+576], rax
	mov rax, QWORD PTR [rbx+328]
	mov QWORD PTR [rbp+584], rax
	mov rax, QWORD PTR [rbx+360]
	mov QWORD PTR [rbp+592], rax
	mov rax, QWORD PTR [rbx+392]
	mov QWORD PTR [rbp+600], rax
	mov rax, QWORD PTR [rbx+424]
	mov QWORD PTR [rbp+608], rax
	mov rax, QWORD PTR [rbx+456]
	mov QWORD PTR [rbp+616], rax
	mov rax, QWORD PTR [rbx+488]
	mov QWORD PTR [rbp+624], rax
	mov rax, QWORD PTR [rbx+520]
	mov QWORD PTR [rbp+632], rax
	mov rax, QWORD PTR [rbx+552]
	mov QWORD PTR [rbp+640], rax
	mov rax, QWORD PTR [rbx+584]
	mov QWORD PTR [rbp+648], rax
	mov rax, QWORD PTR [rbx+616]
	mov QWORD PTR [rbp+656], rax
	mov rax, QWORD PTR [rbx+648]
	mov QWORD PTR [rbp+664], rax
	mov rax, QWORD PTR [rbx+16]
	mov QWORD PTR [rbp+1008], rax
	mov rax, QWORD PTR [rbx+48]
	mov QWORD PTR [rbp+1016], rax
	mov rax, QWORD PTR [rbx+80]
	mov QWORD PTR [rbp+1024], rax
	mov rax, QWORD PTR [rbx+112]
	mov QWORD PTR [rbp+1032], rax
	mov rax, QWORD PTR [rbx+144]
	mov QWORD PTR [rbp+1040], rax
	mov rax, QWORD PTR [rbx+176]
	mov QWORD PTR [rbp+1048], rax
	mov rax, QWORD PTR [rbx+208]
	mov QWORD PTR [rbp+1056], rax
	mov rax, QWORD PTR [rbx+240]
	mov QWORD PTR [rbp+1064], rax
	mov rax, QWORD PTR [rbx+272]
	mov QWORD PTR [rbp+1072], rax
	mov rax, QWORD PTR [rbx+304]
	mov QWORD PTR [rbp+1080], rax
	mov rax, QWORD PTR [rbx+336]
	mov QWORD PTR [rbp+1088], rax
	mov rax, QWORD PTR [rbx+368]
	mov QWORD PTR [rbp+1096], rax
	mov rax, QWORD PTR [rbx+400]
	mov QWORD PTR [rbp+1104], rax
	mov rax, QWORD PTR [rbx+432]
	mov QWORD PTR [rbp+1112], rax
	mov rax, QWORD PTR [rbx+464]
	mov QWORD PTR [rbp+1120], rax
	mov rax, QWORD PTR [rbx+496]
	mov QWORD PTR [rbp+1128], rax
	mov rax, QWORD PTR [rbx+528]
	mov QWORD PTR [rbp+1136], rax
	mov rax, QWORD PTR [rbx+560]
	mov QWORD PTR [rbp+1144], rax
	mov rax, QWORD PTR [rbx+592]
	mov QWORD PTR [rbp+1152], rax
	mov rax, QWORD PTR [rbx+624]
	mov QWORD PTR [rbp+1160], rax
	mov rax, QWORD PTR [rbx+656]
	mov QWORD PTR [rbp+1168], rax
	mov rax, QWORD PTR [rbx+24]
	mov QWORD PTR [rbp+1512], rax
	mov rax, QWORD PTR [rbx+56]
	mov QWORD PTR [rbp+1520], rax
	mov rax, QWORD PTR [rbx+88]
	mov QWORD PTR [rbp+1528], rax
	mov rax, QWORD PTR [rbx+120]
	mov QWORD PTR [rbp+1536], rax
	mov rax, QWORD PTR [rbx+152]
	mov QWORD PTR [rbp+1544], rax
	mov rax, QWORD PTR [rbx+184]
	mov QWORD PTR [rbp+1552], rax
	mov rax, QWORD PTR [rbx+216]
	mov QWORD PTR [rbp+1560], rax
	mov rax, QWORD PTR [rbx+248]
	mov QWORD PTR [rbp+1568], rax
	mov rax, QWORD PTR [rbx+280]
	mov QWORD PTR [rbp+1576], rax
	mov rax, QWORD PTR [rbx+312]
	mov QWORD PTR [rbp+1584], rax
	mov rax, QWORD PTR [rbx+344]
	mov QWORD PTR [rbp+1592], rax
	mov rax, QWORD PTR [rbx+376]
	mov QWORD PTR [rbp+1600], rax
	mov rax, QWORD PTR [rbx+408]
	mov QWORD PTR [rbp+1608], rax
	mov rax, QWORD PTR [rbx+440]
	mov QWORD PTR [rbp+1616], rax
	mov rax, QWORD PTR [rbx+472]
	mov QWORD PTR [rbp+1624], rax
	mov rax, QWORD PTR [rbx+504]
	mov QWORD PTR [rbp+1632], rax
	mov rax, QWORD PTR [rbx+536]
	mov QWORD PTR [rbp+1640], rax
	mov rax, QWORD PTR [rbx+568]
	mov QWORD PTR [rbp+1648], rax
	mov rax, QWORD PTR [rbx+600]
	mov QWORD PTR [rbp+1656], rax
	mov rax, QWORD PTR [rbx+632]
	mov QWORD PTR [rbp+1664], rax
	mov rax, QWORD PTR [rbx+664]
	mov QWORD PTR [rbp+1672], rax
	add rbp, 168
	sub r10, 1
	jne 2104b
	lea r11, {VG_MLKEM_SAMPLE_TBL}
	mov rsi, rbx
	add rsi, 2368
	mov rdi, QWORD PTR [rbx+4424]
	mov rbp, r13
	add rbp, 0
	mov r10d, 7
	vmovdqu ymm8, YMMWORD PTR [r11+4096]
	vmovdqu ymm9, YMMWORD PTR [r11+4128]
	vmovdqu ymm10, YMMWORD PTR [r11+4160]
	vmovdqu ymm12, YMMWORD PTR [r11+6240]
	vmovdqu ymm13, YMMWORD PTR [r11+6272]
	vshufi32x4 zmm12, zmm12, zmm13, 68
	vmovdqu ymm13, YMMWORD PTR [r11+6304]
	vshufi32x4 zmm13, zmm13, zmm13, 0
	vshufi32x4 zmm11, zmm8, zmm8, 0
	vshufi32x4 zmm9, zmm9, zmm9, 0
	vshufi32x4 zmm10, zmm10, zmm10, 0
2106:
	cmp rdi, 225
	jb 2107f
	cmp rdi, 241
	jb 2109f
	cmp rdi, 256
	jb 2111f
	add rsi, 24
	jmp 2112f
2111:
	mov ecx, 8
2113:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 2114f
	jmp 2115f
2114:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2116f
	jmp 2117f
2116:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2117:
2115:
	add rsi, 3
	sub rcx, 1
	jne 2113b
2112:
	jmp 2110f
2109:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
2110:
	cmp rdi, 241
	jb 2118f
	cmp rdi, 256
	jb 2120f
	add rsi, 24
	jmp 2121f
2120:
	mov ecx, 8
2122:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 2123f
	jmp 2124f
2123:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2125f
	jmp 2126f
2125:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2126:
2124:
	add rsi, 3
	sub rcx, 1
	jne 2122b
2121:
	jmp 2119f
2118:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
2119:
	jmp 2108f
2107:
	vmovdqu32 zmm0, ZMMWORD PTR [rsi]
	vpermw zmm0, zmm12, zmm0
	vpshufb zmm0, zmm0, zmm11
	vpsrlvw zmm0, zmm0, zmm13
	vpandq zmm0, zmm0, zmm9
	vpcmpuw k1, zmm0, zmm10, 1
	kmovd eax, k1
	mov edx, eax
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vpshufb xmm1, xmm0, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 8
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 1
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 16
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 2
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 24
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 3
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	add rsi, 48
2108:
	sub r10, 1
	jne 2106b
	mov QWORD PTR [rbx+4424], rdi
	mov rsi, rbx
	add rsi, 2872
	mov rdi, QWORD PTR [rbx+4432]
	mov rbp, r13
	add rbp, 512
	mov r10d, 7
	vmovdqu ymm8, YMMWORD PTR [r11+4096]
	vmovdqu ymm9, YMMWORD PTR [r11+4128]
	vmovdqu ymm10, YMMWORD PTR [r11+4160]
	vmovdqu ymm12, YMMWORD PTR [r11+6240]
	vmovdqu ymm13, YMMWORD PTR [r11+6272]
	vshufi32x4 zmm12, zmm12, zmm13, 68
	vmovdqu ymm13, YMMWORD PTR [r11+6304]
	vshufi32x4 zmm13, zmm13, zmm13, 0
	vshufi32x4 zmm11, zmm8, zmm8, 0
	vshufi32x4 zmm9, zmm9, zmm9, 0
	vshufi32x4 zmm10, zmm10, zmm10, 0
2127:
	cmp rdi, 225
	jb 2128f
	cmp rdi, 241
	jb 2130f
	cmp rdi, 256
	jb 2132f
	add rsi, 24
	jmp 2133f
2132:
	mov ecx, 8
2134:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 2135f
	jmp 2136f
2135:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2137f
	jmp 2138f
2137:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2138:
2136:
	add rsi, 3
	sub rcx, 1
	jne 2134b
2133:
	jmp 2131f
2130:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
2131:
	cmp rdi, 241
	jb 2139f
	cmp rdi, 256
	jb 2141f
	add rsi, 24
	jmp 2142f
2141:
	mov ecx, 8
2143:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 2144f
	jmp 2145f
2144:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2146f
	jmp 2147f
2146:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2147:
2145:
	add rsi, 3
	sub rcx, 1
	jne 2143b
2142:
	jmp 2140f
2139:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
2140:
	jmp 2129f
2128:
	vmovdqu32 zmm0, ZMMWORD PTR [rsi]
	vpermw zmm0, zmm12, zmm0
	vpshufb zmm0, zmm0, zmm11
	vpsrlvw zmm0, zmm0, zmm13
	vpandq zmm0, zmm0, zmm9
	vpcmpuw k1, zmm0, zmm10, 1
	kmovd eax, k1
	mov edx, eax
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vpshufb xmm1, xmm0, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 8
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 1
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 16
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 2
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 24
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 3
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	add rsi, 48
2129:
	sub r10, 1
	jne 2127b
	mov QWORD PTR [rbx+4432], rdi
	mov rsi, rbx
	add rsi, 3376
	mov rdi, QWORD PTR [rbx+4440]
	mov rbp, r13
	add rbp, 1024
	mov r10d, 7
	vmovdqu ymm8, YMMWORD PTR [r11+4096]
	vmovdqu ymm9, YMMWORD PTR [r11+4128]
	vmovdqu ymm10, YMMWORD PTR [r11+4160]
	vmovdqu ymm12, YMMWORD PTR [r11+6240]
	vmovdqu ymm13, YMMWORD PTR [r11+6272]
	vshufi32x4 zmm12, zmm12, zmm13, 68
	vmovdqu ymm13, YMMWORD PTR [r11+6304]
	vshufi32x4 zmm13, zmm13, zmm13, 0
	vshufi32x4 zmm11, zmm8, zmm8, 0
	vshufi32x4 zmm9, zmm9, zmm9, 0
	vshufi32x4 zmm10, zmm10, zmm10, 0
2148:
	cmp rdi, 225
	jb 2149f
	cmp rdi, 241
	jb 2151f
	cmp rdi, 256
	jb 2153f
	add rsi, 24
	jmp 2154f
2153:
	mov ecx, 8
2155:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 2156f
	jmp 2157f
2156:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2158f
	jmp 2159f
2158:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2159:
2157:
	add rsi, 3
	sub rcx, 1
	jne 2155b
2154:
	jmp 2152f
2151:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
2152:
	cmp rdi, 241
	jb 2160f
	cmp rdi, 256
	jb 2162f
	add rsi, 24
	jmp 2163f
2162:
	mov ecx, 8
2164:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 2165f
	jmp 2166f
2165:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2167f
	jmp 2168f
2167:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2168:
2166:
	add rsi, 3
	sub rcx, 1
	jne 2164b
2163:
	jmp 2161f
2160:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
2161:
	jmp 2150f
2149:
	vmovdqu32 zmm0, ZMMWORD PTR [rsi]
	vpermw zmm0, zmm12, zmm0
	vpshufb zmm0, zmm0, zmm11
	vpsrlvw zmm0, zmm0, zmm13
	vpandq zmm0, zmm0, zmm9
	vpcmpuw k1, zmm0, zmm10, 1
	kmovd eax, k1
	mov edx, eax
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vpshufb xmm1, xmm0, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 8
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 1
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 16
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 2
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 24
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 3
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	add rsi, 48
2150:
	sub r10, 1
	jne 2148b
	mov QWORD PTR [rbx+4440], rdi
	mov r14d, 1
	mov rax, QWORD PTR [rbx+4424]
	shr rax, 8
	and r14d, eax
	mov rax, QWORD PTR [rbx+4432]
	shr rax, 8
	and r14d, eax
	mov rax, QWORD PTR [rbx+4440]
	shr rax, 8
	and r14d, eax
2103:
	vzeroupper
	mov eax, r14d
	mov r14, QWORD PTR [rbx+4416]
	mov r13, QWORD PTR [rbx+4408]
	mov r12, QWORD PTR [rbx+4400]
	mov rbp, QWORD PTR [rbx+4392]
	mov rbx, QWORD PTR [rbx+4384]
	and r15d, eax
	mov eax, 0
	mov QWORD PTR [rbx+19008], rax
	mov QWORD PTR [rbx+19016], rax
	mov QWORD PTR [rbx+19024], rax
	mov QWORD PTR [rbx+19032], rax
	mov QWORD PTR [rbx+19040], rax
	mov QWORD PTR [rbx+19048], rax
	mov QWORD PTR [rbx+19056], rax
	mov QWORD PTR [rbx+19064], rax
	mov QWORD PTR [rbx+19072], rax
	mov QWORD PTR [rbx+19080], rax
	mov QWORD PTR [rbx+19088], rax
	mov QWORD PTR [rbx+19096], rax
	mov QWORD PTR [rbx+19104], rax
	mov QWORD PTR [rbx+19112], rax
	mov QWORD PTR [rbx+19120], rax
	mov QWORD PTR [rbx+19128], rax
	mov QWORD PTR [rbx+19136], rax
	mov QWORD PTR [rbx+19144], rax
	mov QWORD PTR [rbx+19152], rax
	mov QWORD PTR [rbx+19160], rax
	mov QWORD PTR [rbx+19168], rax
	mov QWORD PTR [rbx+19176], rax
	mov QWORD PTR [rbx+19184], rax
	mov QWORD PTR [rbx+19192], rax
	mov QWORD PTR [rbx+19200], rax
	mov rdi, rbx
	add rdi, 19712
	mov rsi, rbx
	add rsi, 8704
	call {vg_mlkem16_cbd2_avx2}
	mov rdi, rbx
	add rdi, 19840
	mov rsi, rbx
	add rsi, 9216
	call {vg_mlkem16_cbd2_avx2}
	mov rdi, r13
	add rdi, 0
	mov rsi, rbx
	add rsi, 20480
	mov rdx, rbx
	add rdx, 23552
	mov rcx, rbx
	add rcx, 8704
	mov r8, rbx
	add r8, 26624
	call {vg_mlkem768_kpke_keygen_ntt}
	test r15d, r15d
	jne 2169f
	jmp 2170f
2169:
	mov rdi, r12
	add rdi, 0
	mov rsi, rbx
	add rsi, 4096
	mov rdx, rbx
	add rdx, 20480
	mov rcx, rbx
	add rcx, 23552
	mov r8, rbx
	add r8, 26624
	call {vg_mlkem768_kpke_keygen_row}
2170:
	mov rdi, rbx
	add rdi, 19208
	mov rsi, r12
	add rsi, 0
	mov ecx, 34
2171:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2171b
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
2172:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2172b
	mov eax, 0
	mov BYTE PTR [rbx+32], al
	mov eax, 1
	mov BYTE PTR [rbx+33], al
	mov rdi, rbx
	add rdi, 34
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
2173:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2173b
	mov eax, 1
	mov BYTE PTR [rbx+66], al
	mov eax, 1
	mov BYTE PTR [rbx+67], al
	mov rdi, rbx
	add rdi, 68
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
2174:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2174b
	mov eax, 2
	mov BYTE PTR [rbx+100], al
	mov eax, 1
	mov BYTE PTR [rbx+101], al
	mov rdi, rbx
	add rdi, 102
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
2175:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2175b
	mov eax, 0
	mov BYTE PTR [rbx+134], al
	mov eax, 2
	mov BYTE PTR [rbx+135], al
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbx
	add rsi, 5632
	mov rdx, rbx
	add rdx, 12288
	mov QWORD PTR [rdx+4384], rbx
	mov QWORD PTR [rdx+4392], rbp
	mov QWORD PTR [rdx+4400], r12
	mov QWORD PTR [rdx+4408], r13
	mov QWORD PTR [rdx+4416], r14
	mov rbx, rdx
	mov r12, rdi
	mov r13, rsi
	mov r14d, 1
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
	movzx eax, BYTE PTR [r12+32]
	mov BYTE PTR [rbx+128], al
	movzx eax, BYTE PTR [r12+33]
	mov BYTE PTR [rbx+129], al
	mov rax, QWORD PTR [r12+34]
	mov QWORD PTR [rbx+8], rax
	mov rax, QWORD PTR [r12+42]
	mov QWORD PTR [rbx+40], rax
	mov rax, QWORD PTR [r12+50]
	mov QWORD PTR [rbx+72], rax
	mov rax, QWORD PTR [r12+58]
	mov QWORD PTR [rbx+104], rax
	movzx eax, BYTE PTR [r12+66]
	mov BYTE PTR [rbx+136], al
	movzx eax, BYTE PTR [r12+67]
	mov BYTE PTR [rbx+137], al
	mov rax, QWORD PTR [r12+68]
	mov QWORD PTR [rbx+16], rax
	mov rax, QWORD PTR [r12+76]
	mov QWORD PTR [rbx+48], rax
	mov rax, QWORD PTR [r12+84]
	mov QWORD PTR [rbx+80], rax
	mov rax, QWORD PTR [r12+92]
	mov QWORD PTR [rbx+112], rax
	movzx eax, BYTE PTR [r12+100]
	mov BYTE PTR [rbx+144], al
	movzx eax, BYTE PTR [r12+101]
	mov BYTE PTR [rbx+145], al
	mov rax, QWORD PTR [r12+102]
	mov QWORD PTR [rbx+24], rax
	mov rax, QWORD PTR [r12+110]
	mov QWORD PTR [rbx+56], rax
	mov rax, QWORD PTR [r12+118]
	mov QWORD PTR [rbx+88], rax
	mov rax, QWORD PTR [r12+126]
	mov QWORD PTR [rbx+120], rax
	movzx eax, BYTE PTR [r12+134]
	mov BYTE PTR [rbx+152], al
	movzx eax, BYTE PTR [r12+135]
	mov BYTE PTR [rbx+153], al
	mov eax, 31
	mov BYTE PTR [rbx+130], al
	mov BYTE PTR [rbx+138], al
	mov BYTE PTR [rbx+146], al
	mov BYTE PTR [rbx+154], al
	mov eax, 128
	mov BYTE PTR [rbx+647], al
	mov BYTE PTR [rbx+655], al
	mov BYTE PTR [rbx+663], al
	mov BYTE PTR [rbx+671], al
	mov rax, QWORD PTR [rbx+6720]
	mov QWORD PTR [rbx+24], rax
	mov rax, QWORD PTR [rbx+6728]
	mov QWORD PTR [rbx+56], rax
	mov rax, QWORD PTR [rbx+6736]
	mov QWORD PTR [rbx+88], rax
	mov rax, QWORD PTR [rbx+6744]
	mov QWORD PTR [rbx+120], rax
	mov rax, QWORD PTR [rbx+6752]
	mov QWORD PTR [rbx+152], rax
	mov rax, QWORD PTR [rbx+6760]
	mov QWORD PTR [rbx+184], rax
	mov rax, QWORD PTR [rbx+6768]
	mov QWORD PTR [rbx+216], rax
	mov rax, QWORD PTR [rbx+6776]
	mov QWORD PTR [rbx+248], rax
	mov rax, QWORD PTR [rbx+6784]
	mov QWORD PTR [rbx+280], rax
	mov rax, QWORD PTR [rbx+6792]
	mov QWORD PTR [rbx+312], rax
	mov rax, QWORD PTR [rbx+6800]
	mov QWORD PTR [rbx+344], rax
	mov rax, QWORD PTR [rbx+6808]
	mov QWORD PTR [rbx+376], rax
	mov rax, QWORD PTR [rbx+6816]
	mov QWORD PTR [rbx+408], rax
	mov rax, QWORD PTR [rbx+6824]
	mov QWORD PTR [rbx+440], rax
	mov rax, QWORD PTR [rbx+6832]
	mov QWORD PTR [rbx+472], rax
	mov rax, QWORD PTR [rbx+6840]
	mov QWORD PTR [rbx+504], rax
	mov rax, QWORD PTR [rbx+6848]
	mov QWORD PTR [rbx+536], rax
	mov rax, QWORD PTR [rbx+6856]
	mov QWORD PTR [rbx+568], rax
	mov rax, QWORD PTR [rbx+6864]
	mov QWORD PTR [rbx+600], rax
	mov rax, QWORD PTR [rbx+6872]
	mov QWORD PTR [rbx+632], rax
	mov rax, QWORD PTR [rbx+6880]
	mov QWORD PTR [rbx+664], rax
	mov rax, QWORD PTR [rbx+6888]
	mov QWORD PTR [rbx+696], rax
	mov rax, QWORD PTR [rbx+6896]
	mov QWORD PTR [rbx+728], rax
	mov rax, QWORD PTR [rbx+6904]
	mov QWORD PTR [rbx+760], rax
	mov rax, QWORD PTR [rbx+6912]
	mov QWORD PTR [rbx+792], rax
	mov r8, rbx
	add r8, 6920
	mov rbp, rbx
	add rbp, 2368
	mov r10d, 2
2176:
	mov rax, QWORD PTR [r8]
	xor rax, QWORD PTR [rbx+24]
	mov QWORD PTR [rbx+24], rax
	mov rax, QWORD PTR [r8+8]
	xor rax, QWORD PTR [rbx+56]
	mov QWORD PTR [rbx+56], rax
	mov rax, QWORD PTR [r8+16]
	xor rax, QWORD PTR [rbx+88]
	mov QWORD PTR [rbx+88], rax
	mov rax, QWORD PTR [r8+24]
	xor rax, QWORD PTR [rbx+120]
	mov QWORD PTR [rbx+120], rax
	mov rax, QWORD PTR [r8+32]
	xor rax, QWORD PTR [rbx+152]
	mov QWORD PTR [rbx+152], rax
	mov rax, QWORD PTR [r8+40]
	xor rax, QWORD PTR [rbx+184]
	mov QWORD PTR [rbx+184], rax
	mov rax, QWORD PTR [r8+48]
	xor rax, QWORD PTR [rbx+216]
	mov QWORD PTR [rbx+216], rax
	mov rax, QWORD PTR [r8+56]
	xor rax, QWORD PTR [rbx+248]
	mov QWORD PTR [rbx+248], rax
	mov rax, QWORD PTR [r8+64]
	xor rax, QWORD PTR [rbx+280]
	mov QWORD PTR [rbx+280], rax
	mov rax, QWORD PTR [r8+72]
	xor rax, QWORD PTR [rbx+312]
	mov QWORD PTR [rbx+312], rax
	mov rax, QWORD PTR [r8+80]
	xor rax, QWORD PTR [rbx+344]
	mov QWORD PTR [rbx+344], rax
	mov rax, QWORD PTR [r8+88]
	xor rax, QWORD PTR [rbx+376]
	mov QWORD PTR [rbx+376], rax
	mov rax, QWORD PTR [r8+96]
	xor rax, QWORD PTR [rbx+408]
	mov QWORD PTR [rbx+408], rax
	mov rax, QWORD PTR [r8+104]
	xor rax, QWORD PTR [rbx+440]
	mov QWORD PTR [rbx+440], rax
	mov rax, QWORD PTR [r8+112]
	xor rax, QWORD PTR [rbx+472]
	mov QWORD PTR [rbx+472], rax
	mov rax, QWORD PTR [r8+120]
	xor rax, QWORD PTR [rbx+504]
	mov QWORD PTR [rbx+504], rax
	mov rax, QWORD PTR [r8+128]
	xor rax, QWORD PTR [rbx+536]
	mov QWORD PTR [rbx+536], rax
	add r8, 136
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
2177:
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
	jne 2177b
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
	mov rax, QWORD PTR [rbx+544]
	mov QWORD PTR [rbp+136], rax
	mov rax, QWORD PTR [rbx+576]
	mov QWORD PTR [rbp+144], rax
	mov rax, QWORD PTR [rbx+608]
	mov QWORD PTR [rbp+152], rax
	mov rax, QWORD PTR [rbx+640]
	mov QWORD PTR [rbp+160], rax
	mov rax, QWORD PTR [rbx+8]
	mov QWORD PTR [rbp+504], rax
	mov rax, QWORD PTR [rbx+40]
	mov QWORD PTR [rbp+512], rax
	mov rax, QWORD PTR [rbx+72]
	mov QWORD PTR [rbp+520], rax
	mov rax, QWORD PTR [rbx+104]
	mov QWORD PTR [rbp+528], rax
	mov rax, QWORD PTR [rbx+136]
	mov QWORD PTR [rbp+536], rax
	mov rax, QWORD PTR [rbx+168]
	mov QWORD PTR [rbp+544], rax
	mov rax, QWORD PTR [rbx+200]
	mov QWORD PTR [rbp+552], rax
	mov rax, QWORD PTR [rbx+232]
	mov QWORD PTR [rbp+560], rax
	mov rax, QWORD PTR [rbx+264]
	mov QWORD PTR [rbp+568], rax
	mov rax, QWORD PTR [rbx+296]
	mov QWORD PTR [rbp+576], rax
	mov rax, QWORD PTR [rbx+328]
	mov QWORD PTR [rbp+584], rax
	mov rax, QWORD PTR [rbx+360]
	mov QWORD PTR [rbp+592], rax
	mov rax, QWORD PTR [rbx+392]
	mov QWORD PTR [rbp+600], rax
	mov rax, QWORD PTR [rbx+424]
	mov QWORD PTR [rbp+608], rax
	mov rax, QWORD PTR [rbx+456]
	mov QWORD PTR [rbp+616], rax
	mov rax, QWORD PTR [rbx+488]
	mov QWORD PTR [rbp+624], rax
	mov rax, QWORD PTR [rbx+520]
	mov QWORD PTR [rbp+632], rax
	mov rax, QWORD PTR [rbx+552]
	mov QWORD PTR [rbp+640], rax
	mov rax, QWORD PTR [rbx+584]
	mov QWORD PTR [rbp+648], rax
	mov rax, QWORD PTR [rbx+616]
	mov QWORD PTR [rbp+656], rax
	mov rax, QWORD PTR [rbx+648]
	mov QWORD PTR [rbp+664], rax
	mov rax, QWORD PTR [rbx+16]
	mov QWORD PTR [rbp+1008], rax
	mov rax, QWORD PTR [rbx+48]
	mov QWORD PTR [rbp+1016], rax
	mov rax, QWORD PTR [rbx+80]
	mov QWORD PTR [rbp+1024], rax
	mov rax, QWORD PTR [rbx+112]
	mov QWORD PTR [rbp+1032], rax
	mov rax, QWORD PTR [rbx+144]
	mov QWORD PTR [rbp+1040], rax
	mov rax, QWORD PTR [rbx+176]
	mov QWORD PTR [rbp+1048], rax
	mov rax, QWORD PTR [rbx+208]
	mov QWORD PTR [rbp+1056], rax
	mov rax, QWORD PTR [rbx+240]
	mov QWORD PTR [rbp+1064], rax
	mov rax, QWORD PTR [rbx+272]
	mov QWORD PTR [rbp+1072], rax
	mov rax, QWORD PTR [rbx+304]
	mov QWORD PTR [rbp+1080], rax
	mov rax, QWORD PTR [rbx+336]
	mov QWORD PTR [rbp+1088], rax
	mov rax, QWORD PTR [rbx+368]
	mov QWORD PTR [rbp+1096], rax
	mov rax, QWORD PTR [rbx+400]
	mov QWORD PTR [rbp+1104], rax
	mov rax, QWORD PTR [rbx+432]
	mov QWORD PTR [rbp+1112], rax
	mov rax, QWORD PTR [rbx+464]
	mov QWORD PTR [rbp+1120], rax
	mov rax, QWORD PTR [rbx+496]
	mov QWORD PTR [rbp+1128], rax
	mov rax, QWORD PTR [rbx+528]
	mov QWORD PTR [rbp+1136], rax
	mov rax, QWORD PTR [rbx+560]
	mov QWORD PTR [rbp+1144], rax
	mov rax, QWORD PTR [rbx+592]
	mov QWORD PTR [rbp+1152], rax
	mov rax, QWORD PTR [rbx+624]
	mov QWORD PTR [rbp+1160], rax
	mov rax, QWORD PTR [rbx+656]
	mov QWORD PTR [rbp+1168], rax
	mov rax, QWORD PTR [rbx+24]
	mov QWORD PTR [rbp+1512], rax
	mov rax, QWORD PTR [rbx+56]
	mov QWORD PTR [rbp+1520], rax
	mov rax, QWORD PTR [rbx+88]
	mov QWORD PTR [rbp+1528], rax
	mov rax, QWORD PTR [rbx+120]
	mov QWORD PTR [rbp+1536], rax
	mov rax, QWORD PTR [rbx+152]
	mov QWORD PTR [rbp+1544], rax
	mov rax, QWORD PTR [rbx+184]
	mov QWORD PTR [rbp+1552], rax
	mov rax, QWORD PTR [rbx+216]
	mov QWORD PTR [rbp+1560], rax
	mov rax, QWORD PTR [rbx+248]
	mov QWORD PTR [rbp+1568], rax
	mov rax, QWORD PTR [rbx+280]
	mov QWORD PTR [rbp+1576], rax
	mov rax, QWORD PTR [rbx+312]
	mov QWORD PTR [rbp+1584], rax
	mov rax, QWORD PTR [rbx+344]
	mov QWORD PTR [rbp+1592], rax
	mov rax, QWORD PTR [rbx+376]
	mov QWORD PTR [rbp+1600], rax
	mov rax, QWORD PTR [rbx+408]
	mov QWORD PTR [rbp+1608], rax
	mov rax, QWORD PTR [rbx+440]
	mov QWORD PTR [rbp+1616], rax
	mov rax, QWORD PTR [rbx+472]
	mov QWORD PTR [rbp+1624], rax
	mov rax, QWORD PTR [rbx+504]
	mov QWORD PTR [rbp+1632], rax
	mov rax, QWORD PTR [rbx+536]
	mov QWORD PTR [rbp+1640], rax
	mov rax, QWORD PTR [rbx+568]
	mov QWORD PTR [rbp+1648], rax
	mov rax, QWORD PTR [rbx+600]
	mov QWORD PTR [rbp+1656], rax
	mov rax, QWORD PTR [rbx+632]
	mov QWORD PTR [rbp+1664], rax
	mov rax, QWORD PTR [rbx+664]
	mov QWORD PTR [rbp+1672], rax
	add rbp, 168
	sub r10, 1
	jne 2176b
	mov rax, QWORD PTR [rbx+24]
	mov QWORD PTR [rbx+6720], rax
	mov rax, QWORD PTR [rbx+56]
	mov QWORD PTR [rbx+6728], rax
	mov rax, QWORD PTR [rbx+88]
	mov QWORD PTR [rbx+6736], rax
	mov rax, QWORD PTR [rbx+120]
	mov QWORD PTR [rbx+6744], rax
	mov rax, QWORD PTR [rbx+152]
	mov QWORD PTR [rbx+6752], rax
	mov rax, QWORD PTR [rbx+184]
	mov QWORD PTR [rbx+6760], rax
	mov rax, QWORD PTR [rbx+216]
	mov QWORD PTR [rbx+6768], rax
	mov rax, QWORD PTR [rbx+248]
	mov QWORD PTR [rbx+6776], rax
	mov rax, QWORD PTR [rbx+280]
	mov QWORD PTR [rbx+6784], rax
	mov rax, QWORD PTR [rbx+312]
	mov QWORD PTR [rbx+6792], rax
	mov rax, QWORD PTR [rbx+344]
	mov QWORD PTR [rbx+6800], rax
	mov rax, QWORD PTR [rbx+376]
	mov QWORD PTR [rbx+6808], rax
	mov rax, QWORD PTR [rbx+408]
	mov QWORD PTR [rbx+6816], rax
	mov rax, QWORD PTR [rbx+440]
	mov QWORD PTR [rbx+6824], rax
	mov rax, QWORD PTR [rbx+472]
	mov QWORD PTR [rbx+6832], rax
	mov rax, QWORD PTR [rbx+504]
	mov QWORD PTR [rbx+6840], rax
	mov rax, QWORD PTR [rbx+536]
	mov QWORD PTR [rbx+6848], rax
	mov rax, QWORD PTR [rbx+568]
	mov QWORD PTR [rbx+6856], rax
	mov rax, QWORD PTR [rbx+600]
	mov QWORD PTR [rbx+6864], rax
	mov rax, QWORD PTR [rbx+632]
	mov QWORD PTR [rbx+6872], rax
	mov rax, QWORD PTR [rbx+664]
	mov QWORD PTR [rbx+6880], rax
	mov rax, QWORD PTR [rbx+696]
	mov QWORD PTR [rbx+6888], rax
	mov rax, QWORD PTR [rbx+728]
	mov QWORD PTR [rbx+6896], rax
	mov rax, QWORD PTR [rbx+760]
	mov QWORD PTR [rbx+6904], rax
	mov rax, QWORD PTR [rbx+792]
	mov QWORD PTR [rbx+6912], rax
	mov rbp, rbx
	add rbp, 2704
	mov r10d, 1
2178:
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
2179:
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
	jne 2179b
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
	mov rax, QWORD PTR [rbx+544]
	mov QWORD PTR [rbp+136], rax
	mov rax, QWORD PTR [rbx+576]
	mov QWORD PTR [rbp+144], rax
	mov rax, QWORD PTR [rbx+608]
	mov QWORD PTR [rbp+152], rax
	mov rax, QWORD PTR [rbx+640]
	mov QWORD PTR [rbp+160], rax
	mov rax, QWORD PTR [rbx+8]
	mov QWORD PTR [rbp+504], rax
	mov rax, QWORD PTR [rbx+40]
	mov QWORD PTR [rbp+512], rax
	mov rax, QWORD PTR [rbx+72]
	mov QWORD PTR [rbp+520], rax
	mov rax, QWORD PTR [rbx+104]
	mov QWORD PTR [rbp+528], rax
	mov rax, QWORD PTR [rbx+136]
	mov QWORD PTR [rbp+536], rax
	mov rax, QWORD PTR [rbx+168]
	mov QWORD PTR [rbp+544], rax
	mov rax, QWORD PTR [rbx+200]
	mov QWORD PTR [rbp+552], rax
	mov rax, QWORD PTR [rbx+232]
	mov QWORD PTR [rbp+560], rax
	mov rax, QWORD PTR [rbx+264]
	mov QWORD PTR [rbp+568], rax
	mov rax, QWORD PTR [rbx+296]
	mov QWORD PTR [rbp+576], rax
	mov rax, QWORD PTR [rbx+328]
	mov QWORD PTR [rbp+584], rax
	mov rax, QWORD PTR [rbx+360]
	mov QWORD PTR [rbp+592], rax
	mov rax, QWORD PTR [rbx+392]
	mov QWORD PTR [rbp+600], rax
	mov rax, QWORD PTR [rbx+424]
	mov QWORD PTR [rbp+608], rax
	mov rax, QWORD PTR [rbx+456]
	mov QWORD PTR [rbp+616], rax
	mov rax, QWORD PTR [rbx+488]
	mov QWORD PTR [rbp+624], rax
	mov rax, QWORD PTR [rbx+520]
	mov QWORD PTR [rbp+632], rax
	mov rax, QWORD PTR [rbx+552]
	mov QWORD PTR [rbp+640], rax
	mov rax, QWORD PTR [rbx+584]
	mov QWORD PTR [rbp+648], rax
	mov rax, QWORD PTR [rbx+616]
	mov QWORD PTR [rbp+656], rax
	mov rax, QWORD PTR [rbx+648]
	mov QWORD PTR [rbp+664], rax
	mov rax, QWORD PTR [rbx+16]
	mov QWORD PTR [rbp+1008], rax
	mov rax, QWORD PTR [rbx+48]
	mov QWORD PTR [rbp+1016], rax
	mov rax, QWORD PTR [rbx+80]
	mov QWORD PTR [rbp+1024], rax
	mov rax, QWORD PTR [rbx+112]
	mov QWORD PTR [rbp+1032], rax
	mov rax, QWORD PTR [rbx+144]
	mov QWORD PTR [rbp+1040], rax
	mov rax, QWORD PTR [rbx+176]
	mov QWORD PTR [rbp+1048], rax
	mov rax, QWORD PTR [rbx+208]
	mov QWORD PTR [rbp+1056], rax
	mov rax, QWORD PTR [rbx+240]
	mov QWORD PTR [rbp+1064], rax
	mov rax, QWORD PTR [rbx+272]
	mov QWORD PTR [rbp+1072], rax
	mov rax, QWORD PTR [rbx+304]
	mov QWORD PTR [rbp+1080], rax
	mov rax, QWORD PTR [rbx+336]
	mov QWORD PTR [rbp+1088], rax
	mov rax, QWORD PTR [rbx+368]
	mov QWORD PTR [rbp+1096], rax
	mov rax, QWORD PTR [rbx+400]
	mov QWORD PTR [rbp+1104], rax
	mov rax, QWORD PTR [rbx+432]
	mov QWORD PTR [rbp+1112], rax
	mov rax, QWORD PTR [rbx+464]
	mov QWORD PTR [rbp+1120], rax
	mov rax, QWORD PTR [rbx+496]
	mov QWORD PTR [rbp+1128], rax
	mov rax, QWORD PTR [rbx+528]
	mov QWORD PTR [rbp+1136], rax
	mov rax, QWORD PTR [rbx+560]
	mov QWORD PTR [rbp+1144], rax
	mov rax, QWORD PTR [rbx+592]
	mov QWORD PTR [rbp+1152], rax
	mov rax, QWORD PTR [rbx+624]
	mov QWORD PTR [rbp+1160], rax
	mov rax, QWORD PTR [rbx+656]
	mov QWORD PTR [rbp+1168], rax
	mov rax, QWORD PTR [rbx+24]
	mov QWORD PTR [rbp+1512], rax
	mov rax, QWORD PTR [rbx+56]
	mov QWORD PTR [rbp+1520], rax
	mov rax, QWORD PTR [rbx+88]
	mov QWORD PTR [rbp+1528], rax
	mov rax, QWORD PTR [rbx+120]
	mov QWORD PTR [rbp+1536], rax
	mov rax, QWORD PTR [rbx+152]
	mov QWORD PTR [rbp+1544], rax
	mov rax, QWORD PTR [rbx+184]
	mov QWORD PTR [rbp+1552], rax
	mov rax, QWORD PTR [rbx+216]
	mov QWORD PTR [rbp+1560], rax
	mov rax, QWORD PTR [rbx+248]
	mov QWORD PTR [rbp+1568], rax
	mov rax, QWORD PTR [rbx+280]
	mov QWORD PTR [rbp+1576], rax
	mov rax, QWORD PTR [rbx+312]
	mov QWORD PTR [rbp+1584], rax
	mov rax, QWORD PTR [rbx+344]
	mov QWORD PTR [rbp+1592], rax
	mov rax, QWORD PTR [rbx+376]
	mov QWORD PTR [rbp+1600], rax
	mov rax, QWORD PTR [rbx+408]
	mov QWORD PTR [rbp+1608], rax
	mov rax, QWORD PTR [rbx+440]
	mov QWORD PTR [rbp+1616], rax
	mov rax, QWORD PTR [rbx+472]
	mov QWORD PTR [rbp+1624], rax
	mov rax, QWORD PTR [rbx+504]
	mov QWORD PTR [rbp+1632], rax
	mov rax, QWORD PTR [rbx+536]
	mov QWORD PTR [rbp+1640], rax
	mov rax, QWORD PTR [rbx+568]
	mov QWORD PTR [rbp+1648], rax
	mov rax, QWORD PTR [rbx+600]
	mov QWORD PTR [rbp+1656], rax
	mov rax, QWORD PTR [rbx+632]
	mov QWORD PTR [rbp+1664], rax
	mov rax, QWORD PTR [rbx+664]
	mov QWORD PTR [rbp+1672], rax
	add rbp, 168
	sub r10, 1
	jne 2178b
	lea r11, {VG_MLKEM_SAMPLE_TBL}
	mov rsi, rbx
	add rsi, 2368
	mov edi, 0
	mov rbp, r13
	add rbp, 0
	mov r10d, 10
	vmovdqu ymm8, YMMWORD PTR [r11+4096]
	vmovdqu ymm9, YMMWORD PTR [r11+4128]
	vmovdqu ymm10, YMMWORD PTR [r11+4160]
	vmovdqu ymm12, YMMWORD PTR [r11+6240]
	vmovdqu ymm13, YMMWORD PTR [r11+6272]
	vshufi32x4 zmm12, zmm12, zmm13, 68
	vmovdqu ymm13, YMMWORD PTR [r11+6304]
	vshufi32x4 zmm13, zmm13, zmm13, 0
	vshufi32x4 zmm11, zmm8, zmm8, 0
	vshufi32x4 zmm9, zmm9, zmm9, 0
	vshufi32x4 zmm10, zmm10, zmm10, 0
2180:
	cmp rdi, 225
	jb 2181f
	cmp rdi, 241
	jb 2183f
	cmp rdi, 256
	jb 2185f
	add rsi, 24
	jmp 2186f
2185:
	mov ecx, 8
2187:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 2188f
	jmp 2189f
2188:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2190f
	jmp 2191f
2190:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2191:
2189:
	add rsi, 3
	sub rcx, 1
	jne 2187b
2186:
	jmp 2184f
2183:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
2184:
	cmp rdi, 241
	jb 2192f
	cmp rdi, 256
	jb 2194f
	add rsi, 24
	jmp 2195f
2194:
	mov ecx, 8
2196:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 2197f
	jmp 2198f
2197:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2199f
	jmp 2200f
2199:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2200:
2198:
	add rsi, 3
	sub rcx, 1
	jne 2196b
2195:
	jmp 2193f
2192:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
2193:
	jmp 2182f
2181:
	vmovdqu32 zmm0, ZMMWORD PTR [rsi]
	vpermw zmm0, zmm12, zmm0
	vpshufb zmm0, zmm0, zmm11
	vpsrlvw zmm0, zmm0, zmm13
	vpandq zmm0, zmm0, zmm9
	vpcmpuw k1, zmm0, zmm10, 1
	kmovd eax, k1
	mov edx, eax
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vpshufb xmm1, xmm0, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 8
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 1
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 16
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 2
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 24
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 3
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	add rsi, 48
2182:
	sub r10, 1
	jne 2180b
	cmp rdi, 241
	jb 2201f
	cmp rdi, 256
	jb 2203f
	add rsi, 24
	jmp 2204f
2203:
	mov ecx, 8
2205:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 2206f
	jmp 2207f
2206:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2208f
	jmp 2209f
2208:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2209:
2207:
	add rsi, 3
	sub rcx, 1
	jne 2205b
2204:
	jmp 2202f
2201:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
2202:
	mov QWORD PTR [rbx+4424], rdi
	mov rsi, rbx
	add rsi, 2872
	mov edi, 0
	mov rbp, r13
	add rbp, 512
	mov r10d, 10
	vmovdqu ymm8, YMMWORD PTR [r11+4096]
	vmovdqu ymm9, YMMWORD PTR [r11+4128]
	vmovdqu ymm10, YMMWORD PTR [r11+4160]
	vmovdqu ymm12, YMMWORD PTR [r11+6240]
	vmovdqu ymm13, YMMWORD PTR [r11+6272]
	vshufi32x4 zmm12, zmm12, zmm13, 68
	vmovdqu ymm13, YMMWORD PTR [r11+6304]
	vshufi32x4 zmm13, zmm13, zmm13, 0
	vshufi32x4 zmm11, zmm8, zmm8, 0
	vshufi32x4 zmm9, zmm9, zmm9, 0
	vshufi32x4 zmm10, zmm10, zmm10, 0
2210:
	cmp rdi, 225
	jb 2211f
	cmp rdi, 241
	jb 2213f
	cmp rdi, 256
	jb 2215f
	add rsi, 24
	jmp 2216f
2215:
	mov ecx, 8
2217:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 2218f
	jmp 2219f
2218:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2220f
	jmp 2221f
2220:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2221:
2219:
	add rsi, 3
	sub rcx, 1
	jne 2217b
2216:
	jmp 2214f
2213:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
2214:
	cmp rdi, 241
	jb 2222f
	cmp rdi, 256
	jb 2224f
	add rsi, 24
	jmp 2225f
2224:
	mov ecx, 8
2226:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 2227f
	jmp 2228f
2227:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2229f
	jmp 2230f
2229:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2230:
2228:
	add rsi, 3
	sub rcx, 1
	jne 2226b
2225:
	jmp 2223f
2222:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
2223:
	jmp 2212f
2211:
	vmovdqu32 zmm0, ZMMWORD PTR [rsi]
	vpermw zmm0, zmm12, zmm0
	vpshufb zmm0, zmm0, zmm11
	vpsrlvw zmm0, zmm0, zmm13
	vpandq zmm0, zmm0, zmm9
	vpcmpuw k1, zmm0, zmm10, 1
	kmovd eax, k1
	mov edx, eax
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vpshufb xmm1, xmm0, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 8
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 1
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 16
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 2
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 24
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 3
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	add rsi, 48
2212:
	sub r10, 1
	jne 2210b
	cmp rdi, 241
	jb 2231f
	cmp rdi, 256
	jb 2233f
	add rsi, 24
	jmp 2234f
2233:
	mov ecx, 8
2235:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 2236f
	jmp 2237f
2236:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2238f
	jmp 2239f
2238:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2239:
2237:
	add rsi, 3
	sub rcx, 1
	jne 2235b
2234:
	jmp 2232f
2231:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
2232:
	mov QWORD PTR [rbx+4432], rdi
	mov rsi, rbx
	add rsi, 3376
	mov edi, 0
	mov rbp, r13
	add rbp, 1024
	mov r10d, 10
	vmovdqu ymm8, YMMWORD PTR [r11+4096]
	vmovdqu ymm9, YMMWORD PTR [r11+4128]
	vmovdqu ymm10, YMMWORD PTR [r11+4160]
	vmovdqu ymm12, YMMWORD PTR [r11+6240]
	vmovdqu ymm13, YMMWORD PTR [r11+6272]
	vshufi32x4 zmm12, zmm12, zmm13, 68
	vmovdqu ymm13, YMMWORD PTR [r11+6304]
	vshufi32x4 zmm13, zmm13, zmm13, 0
	vshufi32x4 zmm11, zmm8, zmm8, 0
	vshufi32x4 zmm9, zmm9, zmm9, 0
	vshufi32x4 zmm10, zmm10, zmm10, 0
2240:
	cmp rdi, 225
	jb 2241f
	cmp rdi, 241
	jb 2243f
	cmp rdi, 256
	jb 2245f
	add rsi, 24
	jmp 2246f
2245:
	mov ecx, 8
2247:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 2248f
	jmp 2249f
2248:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2250f
	jmp 2251f
2250:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2251:
2249:
	add rsi, 3
	sub rcx, 1
	jne 2247b
2246:
	jmp 2244f
2243:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
2244:
	cmp rdi, 241
	jb 2252f
	cmp rdi, 256
	jb 2254f
	add rsi, 24
	jmp 2255f
2254:
	mov ecx, 8
2256:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 2257f
	jmp 2258f
2257:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2259f
	jmp 2260f
2259:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2260:
2258:
	add rsi, 3
	sub rcx, 1
	jne 2256b
2255:
	jmp 2253f
2252:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
2253:
	jmp 2242f
2241:
	vmovdqu32 zmm0, ZMMWORD PTR [rsi]
	vpermw zmm0, zmm12, zmm0
	vpshufb zmm0, zmm0, zmm11
	vpsrlvw zmm0, zmm0, zmm13
	vpandq zmm0, zmm0, zmm9
	vpcmpuw k1, zmm0, zmm10, 1
	kmovd eax, k1
	mov edx, eax
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vpshufb xmm1, xmm0, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 8
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 1
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 16
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 2
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 24
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 3
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	add rsi, 48
2242:
	sub r10, 1
	jne 2240b
	cmp rdi, 241
	jb 2261f
	cmp rdi, 256
	jb 2263f
	add rsi, 24
	jmp 2264f
2263:
	mov ecx, 8
2265:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 2266f
	jmp 2267f
2266:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2268f
	jmp 2269f
2268:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2269:
2267:
	add rsi, 3
	sub rcx, 1
	jne 2265b
2264:
	jmp 2262f
2261:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
2262:
	mov QWORD PTR [rbx+4440], rdi
	mov r14d, 1
	mov rax, QWORD PTR [rbx+4424]
	shr rax, 8
	and r14d, eax
	mov rax, QWORD PTR [rbx+4432]
	shr rax, 8
	and r14d, eax
	mov rax, QWORD PTR [rbx+4440]
	shr rax, 8
	and r14d, eax
	cmp r14d, 0
	je 2270f
	jmp 2271f
2270:
	mov r14d, 1
	mov rbp, rbx
	add rbp, 2368
	mov r10d, 2
2272:
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
2273:
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
	jne 2273b
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
	mov rax, QWORD PTR [rbx+544]
	mov QWORD PTR [rbp+136], rax
	mov rax, QWORD PTR [rbx+576]
	mov QWORD PTR [rbp+144], rax
	mov rax, QWORD PTR [rbx+608]
	mov QWORD PTR [rbp+152], rax
	mov rax, QWORD PTR [rbx+640]
	mov QWORD PTR [rbp+160], rax
	mov rax, QWORD PTR [rbx+8]
	mov QWORD PTR [rbp+504], rax
	mov rax, QWORD PTR [rbx+40]
	mov QWORD PTR [rbp+512], rax
	mov rax, QWORD PTR [rbx+72]
	mov QWORD PTR [rbp+520], rax
	mov rax, QWORD PTR [rbx+104]
	mov QWORD PTR [rbp+528], rax
	mov rax, QWORD PTR [rbx+136]
	mov QWORD PTR [rbp+536], rax
	mov rax, QWORD PTR [rbx+168]
	mov QWORD PTR [rbp+544], rax
	mov rax, QWORD PTR [rbx+200]
	mov QWORD PTR [rbp+552], rax
	mov rax, QWORD PTR [rbx+232]
	mov QWORD PTR [rbp+560], rax
	mov rax, QWORD PTR [rbx+264]
	mov QWORD PTR [rbp+568], rax
	mov rax, QWORD PTR [rbx+296]
	mov QWORD PTR [rbp+576], rax
	mov rax, QWORD PTR [rbx+328]
	mov QWORD PTR [rbp+584], rax
	mov rax, QWORD PTR [rbx+360]
	mov QWORD PTR [rbp+592], rax
	mov rax, QWORD PTR [rbx+392]
	mov QWORD PTR [rbp+600], rax
	mov rax, QWORD PTR [rbx+424]
	mov QWORD PTR [rbp+608], rax
	mov rax, QWORD PTR [rbx+456]
	mov QWORD PTR [rbp+616], rax
	mov rax, QWORD PTR [rbx+488]
	mov QWORD PTR [rbp+624], rax
	mov rax, QWORD PTR [rbx+520]
	mov QWORD PTR [rbp+632], rax
	mov rax, QWORD PTR [rbx+552]
	mov QWORD PTR [rbp+640], rax
	mov rax, QWORD PTR [rbx+584]
	mov QWORD PTR [rbp+648], rax
	mov rax, QWORD PTR [rbx+616]
	mov QWORD PTR [rbp+656], rax
	mov rax, QWORD PTR [rbx+648]
	mov QWORD PTR [rbp+664], rax
	mov rax, QWORD PTR [rbx+16]
	mov QWORD PTR [rbp+1008], rax
	mov rax, QWORD PTR [rbx+48]
	mov QWORD PTR [rbp+1016], rax
	mov rax, QWORD PTR [rbx+80]
	mov QWORD PTR [rbp+1024], rax
	mov rax, QWORD PTR [rbx+112]
	mov QWORD PTR [rbp+1032], rax
	mov rax, QWORD PTR [rbx+144]
	mov QWORD PTR [rbp+1040], rax
	mov rax, QWORD PTR [rbx+176]
	mov QWORD PTR [rbp+1048], rax
	mov rax, QWORD PTR [rbx+208]
	mov QWORD PTR [rbp+1056], rax
	mov rax, QWORD PTR [rbx+240]
	mov QWORD PTR [rbp+1064], rax
	mov rax, QWORD PTR [rbx+272]
	mov QWORD PTR [rbp+1072], rax
	mov rax, QWORD PTR [rbx+304]
	mov QWORD PTR [rbp+1080], rax
	mov rax, QWORD PTR [rbx+336]
	mov QWORD PTR [rbp+1088], rax
	mov rax, QWORD PTR [rbx+368]
	mov QWORD PTR [rbp+1096], rax
	mov rax, QWORD PTR [rbx+400]
	mov QWORD PTR [rbp+1104], rax
	mov rax, QWORD PTR [rbx+432]
	mov QWORD PTR [rbp+1112], rax
	mov rax, QWORD PTR [rbx+464]
	mov QWORD PTR [rbp+1120], rax
	mov rax, QWORD PTR [rbx+496]
	mov QWORD PTR [rbp+1128], rax
	mov rax, QWORD PTR [rbx+528]
	mov QWORD PTR [rbp+1136], rax
	mov rax, QWORD PTR [rbx+560]
	mov QWORD PTR [rbp+1144], rax
	mov rax, QWORD PTR [rbx+592]
	mov QWORD PTR [rbp+1152], rax
	mov rax, QWORD PTR [rbx+624]
	mov QWORD PTR [rbp+1160], rax
	mov rax, QWORD PTR [rbx+656]
	mov QWORD PTR [rbp+1168], rax
	mov rax, QWORD PTR [rbx+24]
	mov QWORD PTR [rbp+1512], rax
	mov rax, QWORD PTR [rbx+56]
	mov QWORD PTR [rbp+1520], rax
	mov rax, QWORD PTR [rbx+88]
	mov QWORD PTR [rbp+1528], rax
	mov rax, QWORD PTR [rbx+120]
	mov QWORD PTR [rbp+1536], rax
	mov rax, QWORD PTR [rbx+152]
	mov QWORD PTR [rbp+1544], rax
	mov rax, QWORD PTR [rbx+184]
	mov QWORD PTR [rbp+1552], rax
	mov rax, QWORD PTR [rbx+216]
	mov QWORD PTR [rbp+1560], rax
	mov rax, QWORD PTR [rbx+248]
	mov QWORD PTR [rbp+1568], rax
	mov rax, QWORD PTR [rbx+280]
	mov QWORD PTR [rbp+1576], rax
	mov rax, QWORD PTR [rbx+312]
	mov QWORD PTR [rbp+1584], rax
	mov rax, QWORD PTR [rbx+344]
	mov QWORD PTR [rbp+1592], rax
	mov rax, QWORD PTR [rbx+376]
	mov QWORD PTR [rbp+1600], rax
	mov rax, QWORD PTR [rbx+408]
	mov QWORD PTR [rbp+1608], rax
	mov rax, QWORD PTR [rbx+440]
	mov QWORD PTR [rbp+1616], rax
	mov rax, QWORD PTR [rbx+472]
	mov QWORD PTR [rbp+1624], rax
	mov rax, QWORD PTR [rbx+504]
	mov QWORD PTR [rbp+1632], rax
	mov rax, QWORD PTR [rbx+536]
	mov QWORD PTR [rbp+1640], rax
	mov rax, QWORD PTR [rbx+568]
	mov QWORD PTR [rbp+1648], rax
	mov rax, QWORD PTR [rbx+600]
	mov QWORD PTR [rbp+1656], rax
	mov rax, QWORD PTR [rbx+632]
	mov QWORD PTR [rbp+1664], rax
	mov rax, QWORD PTR [rbx+664]
	mov QWORD PTR [rbp+1672], rax
	add rbp, 168
	sub r10, 1
	jne 2272b
	lea r11, {VG_MLKEM_SAMPLE_TBL}
	mov rsi, rbx
	add rsi, 2368
	mov rdi, QWORD PTR [rbx+4424]
	mov rbp, r13
	add rbp, 0
	mov r10d, 7
	vmovdqu ymm8, YMMWORD PTR [r11+4096]
	vmovdqu ymm9, YMMWORD PTR [r11+4128]
	vmovdqu ymm10, YMMWORD PTR [r11+4160]
	vmovdqu ymm12, YMMWORD PTR [r11+6240]
	vmovdqu ymm13, YMMWORD PTR [r11+6272]
	vshufi32x4 zmm12, zmm12, zmm13, 68
	vmovdqu ymm13, YMMWORD PTR [r11+6304]
	vshufi32x4 zmm13, zmm13, zmm13, 0
	vshufi32x4 zmm11, zmm8, zmm8, 0
	vshufi32x4 zmm9, zmm9, zmm9, 0
	vshufi32x4 zmm10, zmm10, zmm10, 0
2274:
	cmp rdi, 225
	jb 2275f
	cmp rdi, 241
	jb 2277f
	cmp rdi, 256
	jb 2279f
	add rsi, 24
	jmp 2280f
2279:
	mov ecx, 8
2281:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 2282f
	jmp 2283f
2282:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2284f
	jmp 2285f
2284:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2285:
2283:
	add rsi, 3
	sub rcx, 1
	jne 2281b
2280:
	jmp 2278f
2277:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
2278:
	cmp rdi, 241
	jb 2286f
	cmp rdi, 256
	jb 2288f
	add rsi, 24
	jmp 2289f
2288:
	mov ecx, 8
2290:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 2291f
	jmp 2292f
2291:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2293f
	jmp 2294f
2293:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2294:
2292:
	add rsi, 3
	sub rcx, 1
	jne 2290b
2289:
	jmp 2287f
2286:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
2287:
	jmp 2276f
2275:
	vmovdqu32 zmm0, ZMMWORD PTR [rsi]
	vpermw zmm0, zmm12, zmm0
	vpshufb zmm0, zmm0, zmm11
	vpsrlvw zmm0, zmm0, zmm13
	vpandq zmm0, zmm0, zmm9
	vpcmpuw k1, zmm0, zmm10, 1
	kmovd eax, k1
	mov edx, eax
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vpshufb xmm1, xmm0, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 8
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 1
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 16
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 2
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 24
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 3
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	add rsi, 48
2276:
	sub r10, 1
	jne 2274b
	mov QWORD PTR [rbx+4424], rdi
	mov rsi, rbx
	add rsi, 2872
	mov rdi, QWORD PTR [rbx+4432]
	mov rbp, r13
	add rbp, 512
	mov r10d, 7
	vmovdqu ymm8, YMMWORD PTR [r11+4096]
	vmovdqu ymm9, YMMWORD PTR [r11+4128]
	vmovdqu ymm10, YMMWORD PTR [r11+4160]
	vmovdqu ymm12, YMMWORD PTR [r11+6240]
	vmovdqu ymm13, YMMWORD PTR [r11+6272]
	vshufi32x4 zmm12, zmm12, zmm13, 68
	vmovdqu ymm13, YMMWORD PTR [r11+6304]
	vshufi32x4 zmm13, zmm13, zmm13, 0
	vshufi32x4 zmm11, zmm8, zmm8, 0
	vshufi32x4 zmm9, zmm9, zmm9, 0
	vshufi32x4 zmm10, zmm10, zmm10, 0
2295:
	cmp rdi, 225
	jb 2296f
	cmp rdi, 241
	jb 2298f
	cmp rdi, 256
	jb 2300f
	add rsi, 24
	jmp 2301f
2300:
	mov ecx, 8
2302:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 2303f
	jmp 2304f
2303:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2305f
	jmp 2306f
2305:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2306:
2304:
	add rsi, 3
	sub rcx, 1
	jne 2302b
2301:
	jmp 2299f
2298:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
2299:
	cmp rdi, 241
	jb 2307f
	cmp rdi, 256
	jb 2309f
	add rsi, 24
	jmp 2310f
2309:
	mov ecx, 8
2311:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 2312f
	jmp 2313f
2312:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2314f
	jmp 2315f
2314:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2315:
2313:
	add rsi, 3
	sub rcx, 1
	jne 2311b
2310:
	jmp 2308f
2307:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
2308:
	jmp 2297f
2296:
	vmovdqu32 zmm0, ZMMWORD PTR [rsi]
	vpermw zmm0, zmm12, zmm0
	vpshufb zmm0, zmm0, zmm11
	vpsrlvw zmm0, zmm0, zmm13
	vpandq zmm0, zmm0, zmm9
	vpcmpuw k1, zmm0, zmm10, 1
	kmovd eax, k1
	mov edx, eax
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vpshufb xmm1, xmm0, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 8
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 1
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 16
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 2
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 24
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 3
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	add rsi, 48
2297:
	sub r10, 1
	jne 2295b
	mov QWORD PTR [rbx+4432], rdi
	mov rsi, rbx
	add rsi, 3376
	mov rdi, QWORD PTR [rbx+4440]
	mov rbp, r13
	add rbp, 1024
	mov r10d, 7
	vmovdqu ymm8, YMMWORD PTR [r11+4096]
	vmovdqu ymm9, YMMWORD PTR [r11+4128]
	vmovdqu ymm10, YMMWORD PTR [r11+4160]
	vmovdqu ymm12, YMMWORD PTR [r11+6240]
	vmovdqu ymm13, YMMWORD PTR [r11+6272]
	vshufi32x4 zmm12, zmm12, zmm13, 68
	vmovdqu ymm13, YMMWORD PTR [r11+6304]
	vshufi32x4 zmm13, zmm13, zmm13, 0
	vshufi32x4 zmm11, zmm8, zmm8, 0
	vshufi32x4 zmm9, zmm9, zmm9, 0
	vshufi32x4 zmm10, zmm10, zmm10, 0
2316:
	cmp rdi, 225
	jb 2317f
	cmp rdi, 241
	jb 2319f
	cmp rdi, 256
	jb 2321f
	add rsi, 24
	jmp 2322f
2321:
	mov ecx, 8
2323:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 2324f
	jmp 2325f
2324:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2326f
	jmp 2327f
2326:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2327:
2325:
	add rsi, 3
	sub rcx, 1
	jne 2323b
2322:
	jmp 2320f
2319:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
2320:
	cmp rdi, 241
	jb 2328f
	cmp rdi, 256
	jb 2330f
	add rsi, 24
	jmp 2331f
2330:
	mov ecx, 8
2332:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 2333f
	jmp 2334f
2333:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2335f
	jmp 2336f
2335:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2336:
2334:
	add rsi, 3
	sub rcx, 1
	jne 2332b
2331:
	jmp 2329f
2328:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
2329:
	jmp 2318f
2317:
	vmovdqu32 zmm0, ZMMWORD PTR [rsi]
	vpermw zmm0, zmm12, zmm0
	vpshufb zmm0, zmm0, zmm11
	vpsrlvw zmm0, zmm0, zmm13
	vpandq zmm0, zmm0, zmm9
	vpcmpuw k1, zmm0, zmm10, 1
	kmovd eax, k1
	mov edx, eax
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vpshufb xmm1, xmm0, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 8
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 1
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 16
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 2
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 24
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 3
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	add rsi, 48
2318:
	sub r10, 1
	jne 2316b
	mov QWORD PTR [rbx+4440], rdi
	mov r14d, 1
	mov rax, QWORD PTR [rbx+4424]
	shr rax, 8
	and r14d, eax
	mov rax, QWORD PTR [rbx+4432]
	shr rax, 8
	and r14d, eax
	mov rax, QWORD PTR [rbx+4440]
	shr rax, 8
	and r14d, eax
2271:
	vzeroupper
	mov eax, r14d
	mov r14, QWORD PTR [rbx+4416]
	mov r13, QWORD PTR [rbx+4408]
	mov r12, QWORD PTR [rbx+4400]
	mov rbp, QWORD PTR [rbx+4392]
	mov rbx, QWORD PTR [rbx+4384]
	and r15d, eax
	test r15d, r15d
	jne 2337f
	jmp 2338f
2337:
	mov rdi, r12
	add rdi, 384
	mov rsi, rbx
	add rsi, 5632
	mov rdx, rbx
	add rdx, 20480
	mov rcx, rbx
	add rcx, 24576
	mov r8, rbx
	add r8, 26624
	call {vg_mlkem768_kpke_keygen_row}
2338:
	mov rdi, rbx
	add rdi, 19208
	mov rsi, r12
	add rsi, 272
	mov ecx, 51
2339:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2339b
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
2340:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2340b
	mov eax, 0
	mov BYTE PTR [rbx+32], al
	mov eax, 2
	mov BYTE PTR [rbx+33], al
	mov rdi, rbx
	add rdi, 34
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
2341:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2341b
	mov eax, 1
	mov BYTE PTR [rbx+66], al
	mov eax, 2
	mov BYTE PTR [rbx+67], al
	mov rdi, rbx
	add rdi, 68
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
2342:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2342b
	mov eax, 2
	mov BYTE PTR [rbx+100], al
	mov eax, 2
	mov BYTE PTR [rbx+101], al
	mov rdi, rbx
	add rdi, 102
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
2343:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2343b
	mov eax, 0
	mov BYTE PTR [rbx+134], al
	mov eax, 3
	mov BYTE PTR [rbx+135], al
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbx
	add rsi, 7168
	mov rdx, rbx
	add rdx, 12288
	mov QWORD PTR [rdx+4384], rbx
	mov QWORD PTR [rdx+4392], rbp
	mov QWORD PTR [rdx+4400], r12
	mov QWORD PTR [rdx+4408], r13
	mov QWORD PTR [rdx+4416], r14
	mov rbx, rdx
	mov r12, rdi
	mov r13, rsi
	mov r14d, 1
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
	movzx eax, BYTE PTR [r12+32]
	mov BYTE PTR [rbx+128], al
	movzx eax, BYTE PTR [r12+33]
	mov BYTE PTR [rbx+129], al
	mov rax, QWORD PTR [r12+34]
	mov QWORD PTR [rbx+8], rax
	mov rax, QWORD PTR [r12+42]
	mov QWORD PTR [rbx+40], rax
	mov rax, QWORD PTR [r12+50]
	mov QWORD PTR [rbx+72], rax
	mov rax, QWORD PTR [r12+58]
	mov QWORD PTR [rbx+104], rax
	movzx eax, BYTE PTR [r12+66]
	mov BYTE PTR [rbx+136], al
	movzx eax, BYTE PTR [r12+67]
	mov BYTE PTR [rbx+137], al
	mov rax, QWORD PTR [r12+68]
	mov QWORD PTR [rbx+16], rax
	mov rax, QWORD PTR [r12+76]
	mov QWORD PTR [rbx+48], rax
	mov rax, QWORD PTR [r12+84]
	mov QWORD PTR [rbx+80], rax
	mov rax, QWORD PTR [r12+92]
	mov QWORD PTR [rbx+112], rax
	movzx eax, BYTE PTR [r12+100]
	mov BYTE PTR [rbx+144], al
	movzx eax, BYTE PTR [r12+101]
	mov BYTE PTR [rbx+145], al
	mov rax, QWORD PTR [r12+102]
	mov QWORD PTR [rbx+24], rax
	mov rax, QWORD PTR [r12+110]
	mov QWORD PTR [rbx+56], rax
	mov rax, QWORD PTR [r12+118]
	mov QWORD PTR [rbx+88], rax
	mov rax, QWORD PTR [r12+126]
	mov QWORD PTR [rbx+120], rax
	movzx eax, BYTE PTR [r12+134]
	mov BYTE PTR [rbx+152], al
	movzx eax, BYTE PTR [r12+135]
	mov BYTE PTR [rbx+153], al
	mov eax, 31
	mov BYTE PTR [rbx+130], al
	mov BYTE PTR [rbx+138], al
	mov BYTE PTR [rbx+146], al
	mov BYTE PTR [rbx+154], al
	mov eax, 128
	mov BYTE PTR [rbx+647], al
	mov BYTE PTR [rbx+655], al
	mov BYTE PTR [rbx+663], al
	mov BYTE PTR [rbx+671], al
	mov rax, QWORD PTR [rbx+6720]
	mov QWORD PTR [rbx+24], rax
	mov rax, QWORD PTR [rbx+6728]
	mov QWORD PTR [rbx+56], rax
	mov rax, QWORD PTR [rbx+6736]
	mov QWORD PTR [rbx+88], rax
	mov rax, QWORD PTR [rbx+6744]
	mov QWORD PTR [rbx+120], rax
	mov rax, QWORD PTR [rbx+6752]
	mov QWORD PTR [rbx+152], rax
	mov rax, QWORD PTR [rbx+6760]
	mov QWORD PTR [rbx+184], rax
	mov rax, QWORD PTR [rbx+6768]
	mov QWORD PTR [rbx+216], rax
	mov rax, QWORD PTR [rbx+6776]
	mov QWORD PTR [rbx+248], rax
	mov rax, QWORD PTR [rbx+6784]
	mov QWORD PTR [rbx+280], rax
	mov rax, QWORD PTR [rbx+6792]
	mov QWORD PTR [rbx+312], rax
	mov rax, QWORD PTR [rbx+6800]
	mov QWORD PTR [rbx+344], rax
	mov rax, QWORD PTR [rbx+6808]
	mov QWORD PTR [rbx+376], rax
	mov rax, QWORD PTR [rbx+6816]
	mov QWORD PTR [rbx+408], rax
	mov rax, QWORD PTR [rbx+6824]
	mov QWORD PTR [rbx+440], rax
	mov rax, QWORD PTR [rbx+6832]
	mov QWORD PTR [rbx+472], rax
	mov rax, QWORD PTR [rbx+6840]
	mov QWORD PTR [rbx+504], rax
	mov rax, QWORD PTR [rbx+6848]
	mov QWORD PTR [rbx+536], rax
	mov rax, QWORD PTR [rbx+6856]
	mov QWORD PTR [rbx+568], rax
	mov rax, QWORD PTR [rbx+6864]
	mov QWORD PTR [rbx+600], rax
	mov rax, QWORD PTR [rbx+6872]
	mov QWORD PTR [rbx+632], rax
	mov rax, QWORD PTR [rbx+6880]
	mov QWORD PTR [rbx+664], rax
	mov rax, QWORD PTR [rbx+6888]
	mov QWORD PTR [rbx+696], rax
	mov rax, QWORD PTR [rbx+6896]
	mov QWORD PTR [rbx+728], rax
	mov rax, QWORD PTR [rbx+6904]
	mov QWORD PTR [rbx+760], rax
	mov rax, QWORD PTR [rbx+6912]
	mov QWORD PTR [rbx+792], rax
	mov r8, rbx
	add r8, 6920
	mov rbp, rbx
	add rbp, 2368
	mov r10d, 3
2344:
	mov rax, QWORD PTR [r8]
	xor rax, QWORD PTR [rbx+24]
	mov QWORD PTR [rbx+24], rax
	mov rax, QWORD PTR [r8+8]
	xor rax, QWORD PTR [rbx+56]
	mov QWORD PTR [rbx+56], rax
	mov rax, QWORD PTR [r8+16]
	xor rax, QWORD PTR [rbx+88]
	mov QWORD PTR [rbx+88], rax
	mov rax, QWORD PTR [r8+24]
	xor rax, QWORD PTR [rbx+120]
	mov QWORD PTR [rbx+120], rax
	mov rax, QWORD PTR [r8+32]
	xor rax, QWORD PTR [rbx+152]
	mov QWORD PTR [rbx+152], rax
	mov rax, QWORD PTR [r8+40]
	xor rax, QWORD PTR [rbx+184]
	mov QWORD PTR [rbx+184], rax
	mov rax, QWORD PTR [r8+48]
	xor rax, QWORD PTR [rbx+216]
	mov QWORD PTR [rbx+216], rax
	mov rax, QWORD PTR [r8+56]
	xor rax, QWORD PTR [rbx+248]
	mov QWORD PTR [rbx+248], rax
	mov rax, QWORD PTR [r8+64]
	xor rax, QWORD PTR [rbx+280]
	mov QWORD PTR [rbx+280], rax
	mov rax, QWORD PTR [r8+72]
	xor rax, QWORD PTR [rbx+312]
	mov QWORD PTR [rbx+312], rax
	mov rax, QWORD PTR [r8+80]
	xor rax, QWORD PTR [rbx+344]
	mov QWORD PTR [rbx+344], rax
	mov rax, QWORD PTR [r8+88]
	xor rax, QWORD PTR [rbx+376]
	mov QWORD PTR [rbx+376], rax
	mov rax, QWORD PTR [r8+96]
	xor rax, QWORD PTR [rbx+408]
	mov QWORD PTR [rbx+408], rax
	mov rax, QWORD PTR [r8+104]
	xor rax, QWORD PTR [rbx+440]
	mov QWORD PTR [rbx+440], rax
	mov rax, QWORD PTR [r8+112]
	xor rax, QWORD PTR [rbx+472]
	mov QWORD PTR [rbx+472], rax
	mov rax, QWORD PTR [r8+120]
	xor rax, QWORD PTR [rbx+504]
	mov QWORD PTR [rbx+504], rax
	mov rax, QWORD PTR [r8+128]
	xor rax, QWORD PTR [rbx+536]
	mov QWORD PTR [rbx+536], rax
	add r8, 136
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
2345:
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
	jne 2345b
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
	mov rax, QWORD PTR [rbx+544]
	mov QWORD PTR [rbp+136], rax
	mov rax, QWORD PTR [rbx+576]
	mov QWORD PTR [rbp+144], rax
	mov rax, QWORD PTR [rbx+608]
	mov QWORD PTR [rbp+152], rax
	mov rax, QWORD PTR [rbx+640]
	mov QWORD PTR [rbp+160], rax
	mov rax, QWORD PTR [rbx+8]
	mov QWORD PTR [rbp+504], rax
	mov rax, QWORD PTR [rbx+40]
	mov QWORD PTR [rbp+512], rax
	mov rax, QWORD PTR [rbx+72]
	mov QWORD PTR [rbp+520], rax
	mov rax, QWORD PTR [rbx+104]
	mov QWORD PTR [rbp+528], rax
	mov rax, QWORD PTR [rbx+136]
	mov QWORD PTR [rbp+536], rax
	mov rax, QWORD PTR [rbx+168]
	mov QWORD PTR [rbp+544], rax
	mov rax, QWORD PTR [rbx+200]
	mov QWORD PTR [rbp+552], rax
	mov rax, QWORD PTR [rbx+232]
	mov QWORD PTR [rbp+560], rax
	mov rax, QWORD PTR [rbx+264]
	mov QWORD PTR [rbp+568], rax
	mov rax, QWORD PTR [rbx+296]
	mov QWORD PTR [rbp+576], rax
	mov rax, QWORD PTR [rbx+328]
	mov QWORD PTR [rbp+584], rax
	mov rax, QWORD PTR [rbx+360]
	mov QWORD PTR [rbp+592], rax
	mov rax, QWORD PTR [rbx+392]
	mov QWORD PTR [rbp+600], rax
	mov rax, QWORD PTR [rbx+424]
	mov QWORD PTR [rbp+608], rax
	mov rax, QWORD PTR [rbx+456]
	mov QWORD PTR [rbp+616], rax
	mov rax, QWORD PTR [rbx+488]
	mov QWORD PTR [rbp+624], rax
	mov rax, QWORD PTR [rbx+520]
	mov QWORD PTR [rbp+632], rax
	mov rax, QWORD PTR [rbx+552]
	mov QWORD PTR [rbp+640], rax
	mov rax, QWORD PTR [rbx+584]
	mov QWORD PTR [rbp+648], rax
	mov rax, QWORD PTR [rbx+616]
	mov QWORD PTR [rbp+656], rax
	mov rax, QWORD PTR [rbx+648]
	mov QWORD PTR [rbp+664], rax
	mov rax, QWORD PTR [rbx+16]
	mov QWORD PTR [rbp+1008], rax
	mov rax, QWORD PTR [rbx+48]
	mov QWORD PTR [rbp+1016], rax
	mov rax, QWORD PTR [rbx+80]
	mov QWORD PTR [rbp+1024], rax
	mov rax, QWORD PTR [rbx+112]
	mov QWORD PTR [rbp+1032], rax
	mov rax, QWORD PTR [rbx+144]
	mov QWORD PTR [rbp+1040], rax
	mov rax, QWORD PTR [rbx+176]
	mov QWORD PTR [rbp+1048], rax
	mov rax, QWORD PTR [rbx+208]
	mov QWORD PTR [rbp+1056], rax
	mov rax, QWORD PTR [rbx+240]
	mov QWORD PTR [rbp+1064], rax
	mov rax, QWORD PTR [rbx+272]
	mov QWORD PTR [rbp+1072], rax
	mov rax, QWORD PTR [rbx+304]
	mov QWORD PTR [rbp+1080], rax
	mov rax, QWORD PTR [rbx+336]
	mov QWORD PTR [rbp+1088], rax
	mov rax, QWORD PTR [rbx+368]
	mov QWORD PTR [rbp+1096], rax
	mov rax, QWORD PTR [rbx+400]
	mov QWORD PTR [rbp+1104], rax
	mov rax, QWORD PTR [rbx+432]
	mov QWORD PTR [rbp+1112], rax
	mov rax, QWORD PTR [rbx+464]
	mov QWORD PTR [rbp+1120], rax
	mov rax, QWORD PTR [rbx+496]
	mov QWORD PTR [rbp+1128], rax
	mov rax, QWORD PTR [rbx+528]
	mov QWORD PTR [rbp+1136], rax
	mov rax, QWORD PTR [rbx+560]
	mov QWORD PTR [rbp+1144], rax
	mov rax, QWORD PTR [rbx+592]
	mov QWORD PTR [rbp+1152], rax
	mov rax, QWORD PTR [rbx+624]
	mov QWORD PTR [rbp+1160], rax
	mov rax, QWORD PTR [rbx+656]
	mov QWORD PTR [rbp+1168], rax
	mov rax, QWORD PTR [rbx+24]
	mov QWORD PTR [rbp+1512], rax
	mov rax, QWORD PTR [rbx+56]
	mov QWORD PTR [rbp+1520], rax
	mov rax, QWORD PTR [rbx+88]
	mov QWORD PTR [rbp+1528], rax
	mov rax, QWORD PTR [rbx+120]
	mov QWORD PTR [rbp+1536], rax
	mov rax, QWORD PTR [rbx+152]
	mov QWORD PTR [rbp+1544], rax
	mov rax, QWORD PTR [rbx+184]
	mov QWORD PTR [rbp+1552], rax
	mov rax, QWORD PTR [rbx+216]
	mov QWORD PTR [rbp+1560], rax
	mov rax, QWORD PTR [rbx+248]
	mov QWORD PTR [rbp+1568], rax
	mov rax, QWORD PTR [rbx+280]
	mov QWORD PTR [rbp+1576], rax
	mov rax, QWORD PTR [rbx+312]
	mov QWORD PTR [rbp+1584], rax
	mov rax, QWORD PTR [rbx+344]
	mov QWORD PTR [rbp+1592], rax
	mov rax, QWORD PTR [rbx+376]
	mov QWORD PTR [rbp+1600], rax
	mov rax, QWORD PTR [rbx+408]
	mov QWORD PTR [rbp+1608], rax
	mov rax, QWORD PTR [rbx+440]
	mov QWORD PTR [rbp+1616], rax
	mov rax, QWORD PTR [rbx+472]
	mov QWORD PTR [rbp+1624], rax
	mov rax, QWORD PTR [rbx+504]
	mov QWORD PTR [rbp+1632], rax
	mov rax, QWORD PTR [rbx+536]
	mov QWORD PTR [rbp+1640], rax
	mov rax, QWORD PTR [rbx+568]
	mov QWORD PTR [rbp+1648], rax
	mov rax, QWORD PTR [rbx+600]
	mov QWORD PTR [rbp+1656], rax
	mov rax, QWORD PTR [rbx+632]
	mov QWORD PTR [rbp+1664], rax
	mov rax, QWORD PTR [rbx+664]
	mov QWORD PTR [rbp+1672], rax
	add rbp, 168
	sub r10, 1
	jne 2344b
	mov rax, QWORD PTR [rbx+24]
	mov QWORD PTR [rbx+6720], rax
	mov rax, QWORD PTR [rbx+56]
	mov QWORD PTR [rbx+6728], rax
	mov rax, QWORD PTR [rbx+88]
	mov QWORD PTR [rbx+6736], rax
	mov rax, QWORD PTR [rbx+120]
	mov QWORD PTR [rbx+6744], rax
	mov rax, QWORD PTR [rbx+152]
	mov QWORD PTR [rbx+6752], rax
	mov rax, QWORD PTR [rbx+184]
	mov QWORD PTR [rbx+6760], rax
	mov rax, QWORD PTR [rbx+216]
	mov QWORD PTR [rbx+6768], rax
	mov rax, QWORD PTR [rbx+248]
	mov QWORD PTR [rbx+6776], rax
	mov rax, QWORD PTR [rbx+280]
	mov QWORD PTR [rbx+6784], rax
	mov rax, QWORD PTR [rbx+312]
	mov QWORD PTR [rbx+6792], rax
	mov rax, QWORD PTR [rbx+344]
	mov QWORD PTR [rbx+6800], rax
	mov rax, QWORD PTR [rbx+376]
	mov QWORD PTR [rbx+6808], rax
	mov rax, QWORD PTR [rbx+408]
	mov QWORD PTR [rbx+6816], rax
	mov rax, QWORD PTR [rbx+440]
	mov QWORD PTR [rbx+6824], rax
	mov rax, QWORD PTR [rbx+472]
	mov QWORD PTR [rbx+6832], rax
	mov rax, QWORD PTR [rbx+504]
	mov QWORD PTR [rbx+6840], rax
	mov rax, QWORD PTR [rbx+536]
	mov QWORD PTR [rbx+6848], rax
	mov rax, QWORD PTR [rbx+568]
	mov QWORD PTR [rbx+6856], rax
	mov rax, QWORD PTR [rbx+600]
	mov QWORD PTR [rbx+6864], rax
	mov rax, QWORD PTR [rbx+632]
	mov QWORD PTR [rbx+6872], rax
	mov rax, QWORD PTR [rbx+664]
	mov QWORD PTR [rbx+6880], rax
	mov rax, QWORD PTR [rbx+696]
	mov QWORD PTR [rbx+6888], rax
	mov rax, QWORD PTR [rbx+728]
	mov QWORD PTR [rbx+6896], rax
	mov rax, QWORD PTR [rbx+760]
	mov QWORD PTR [rbx+6904], rax
	mov rax, QWORD PTR [rbx+792]
	mov QWORD PTR [rbx+6912], rax
	lea r11, {VG_MLKEM_SAMPLE_TBL}
	mov rsi, rbx
	add rsi, 2368
	mov edi, 0
	mov rbp, r13
	add rbp, 0
	mov r10d, 10
	vmovdqu ymm8, YMMWORD PTR [r11+4096]
	vmovdqu ymm9, YMMWORD PTR [r11+4128]
	vmovdqu ymm10, YMMWORD PTR [r11+4160]
	vmovdqu ymm12, YMMWORD PTR [r11+6240]
	vmovdqu ymm13, YMMWORD PTR [r11+6272]
	vshufi32x4 zmm12, zmm12, zmm13, 68
	vmovdqu ymm13, YMMWORD PTR [r11+6304]
	vshufi32x4 zmm13, zmm13, zmm13, 0
	vshufi32x4 zmm11, zmm8, zmm8, 0
	vshufi32x4 zmm9, zmm9, zmm9, 0
	vshufi32x4 zmm10, zmm10, zmm10, 0
2346:
	cmp rdi, 225
	jb 2347f
	cmp rdi, 241
	jb 2349f
	cmp rdi, 256
	jb 2351f
	add rsi, 24
	jmp 2352f
2351:
	mov ecx, 8
2353:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 2354f
	jmp 2355f
2354:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2356f
	jmp 2357f
2356:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2357:
2355:
	add rsi, 3
	sub rcx, 1
	jne 2353b
2352:
	jmp 2350f
2349:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
2350:
	cmp rdi, 241
	jb 2358f
	cmp rdi, 256
	jb 2360f
	add rsi, 24
	jmp 2361f
2360:
	mov ecx, 8
2362:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 2363f
	jmp 2364f
2363:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2365f
	jmp 2366f
2365:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2366:
2364:
	add rsi, 3
	sub rcx, 1
	jne 2362b
2361:
	jmp 2359f
2358:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
2359:
	jmp 2348f
2347:
	vmovdqu32 zmm0, ZMMWORD PTR [rsi]
	vpermw zmm0, zmm12, zmm0
	vpshufb zmm0, zmm0, zmm11
	vpsrlvw zmm0, zmm0, zmm13
	vpandq zmm0, zmm0, zmm9
	vpcmpuw k1, zmm0, zmm10, 1
	kmovd eax, k1
	mov edx, eax
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vpshufb xmm1, xmm0, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 8
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 1
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 16
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 2
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 24
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 3
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	add rsi, 48
2348:
	sub r10, 1
	jne 2346b
	cmp rdi, 241
	jb 2367f
	cmp rdi, 256
	jb 2369f
	add rsi, 24
	jmp 2370f
2369:
	mov ecx, 8
2371:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 2372f
	jmp 2373f
2372:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2374f
	jmp 2375f
2374:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2375:
2373:
	add rsi, 3
	sub rcx, 1
	jne 2371b
2370:
	jmp 2368f
2367:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
2368:
	mov QWORD PTR [rbx+4424], rdi
	mov rsi, rbx
	add rsi, 2872
	mov edi, 0
	mov rbp, r13
	add rbp, 512
	mov r10d, 10
	vmovdqu ymm8, YMMWORD PTR [r11+4096]
	vmovdqu ymm9, YMMWORD PTR [r11+4128]
	vmovdqu ymm10, YMMWORD PTR [r11+4160]
	vmovdqu ymm12, YMMWORD PTR [r11+6240]
	vmovdqu ymm13, YMMWORD PTR [r11+6272]
	vshufi32x4 zmm12, zmm12, zmm13, 68
	vmovdqu ymm13, YMMWORD PTR [r11+6304]
	vshufi32x4 zmm13, zmm13, zmm13, 0
	vshufi32x4 zmm11, zmm8, zmm8, 0
	vshufi32x4 zmm9, zmm9, zmm9, 0
	vshufi32x4 zmm10, zmm10, zmm10, 0
2376:
	cmp rdi, 225
	jb 2377f
	cmp rdi, 241
	jb 2379f
	cmp rdi, 256
	jb 2381f
	add rsi, 24
	jmp 2382f
2381:
	mov ecx, 8
2383:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 2384f
	jmp 2385f
2384:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2386f
	jmp 2387f
2386:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2387:
2385:
	add rsi, 3
	sub rcx, 1
	jne 2383b
2382:
	jmp 2380f
2379:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
2380:
	cmp rdi, 241
	jb 2388f
	cmp rdi, 256
	jb 2390f
	add rsi, 24
	jmp 2391f
2390:
	mov ecx, 8
2392:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 2393f
	jmp 2394f
2393:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2395f
	jmp 2396f
2395:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2396:
2394:
	add rsi, 3
	sub rcx, 1
	jne 2392b
2391:
	jmp 2389f
2388:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
2389:
	jmp 2378f
2377:
	vmovdqu32 zmm0, ZMMWORD PTR [rsi]
	vpermw zmm0, zmm12, zmm0
	vpshufb zmm0, zmm0, zmm11
	vpsrlvw zmm0, zmm0, zmm13
	vpandq zmm0, zmm0, zmm9
	vpcmpuw k1, zmm0, zmm10, 1
	kmovd eax, k1
	mov edx, eax
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vpshufb xmm1, xmm0, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 8
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 1
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 16
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 2
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 24
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 3
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	add rsi, 48
2378:
	sub r10, 1
	jne 2376b
	cmp rdi, 241
	jb 2397f
	cmp rdi, 256
	jb 2399f
	add rsi, 24
	jmp 2400f
2399:
	mov ecx, 8
2401:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 2402f
	jmp 2403f
2402:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2404f
	jmp 2405f
2404:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2405:
2403:
	add rsi, 3
	sub rcx, 1
	jne 2401b
2400:
	jmp 2398f
2397:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
2398:
	mov QWORD PTR [rbx+4432], rdi
	mov rsi, rbx
	add rsi, 3376
	mov edi, 0
	mov rbp, r13
	add rbp, 1024
	mov r10d, 10
	vmovdqu ymm8, YMMWORD PTR [r11+4096]
	vmovdqu ymm9, YMMWORD PTR [r11+4128]
	vmovdqu ymm10, YMMWORD PTR [r11+4160]
	vmovdqu ymm12, YMMWORD PTR [r11+6240]
	vmovdqu ymm13, YMMWORD PTR [r11+6272]
	vshufi32x4 zmm12, zmm12, zmm13, 68
	vmovdqu ymm13, YMMWORD PTR [r11+6304]
	vshufi32x4 zmm13, zmm13, zmm13, 0
	vshufi32x4 zmm11, zmm8, zmm8, 0
	vshufi32x4 zmm9, zmm9, zmm9, 0
	vshufi32x4 zmm10, zmm10, zmm10, 0
2406:
	cmp rdi, 225
	jb 2407f
	cmp rdi, 241
	jb 2409f
	cmp rdi, 256
	jb 2411f
	add rsi, 24
	jmp 2412f
2411:
	mov ecx, 8
2413:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 2414f
	jmp 2415f
2414:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2416f
	jmp 2417f
2416:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2417:
2415:
	add rsi, 3
	sub rcx, 1
	jne 2413b
2412:
	jmp 2410f
2409:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
2410:
	cmp rdi, 241
	jb 2418f
	cmp rdi, 256
	jb 2420f
	add rsi, 24
	jmp 2421f
2420:
	mov ecx, 8
2422:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 2423f
	jmp 2424f
2423:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2425f
	jmp 2426f
2425:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2426:
2424:
	add rsi, 3
	sub rcx, 1
	jne 2422b
2421:
	jmp 2419f
2418:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
2419:
	jmp 2408f
2407:
	vmovdqu32 zmm0, ZMMWORD PTR [rsi]
	vpermw zmm0, zmm12, zmm0
	vpshufb zmm0, zmm0, zmm11
	vpsrlvw zmm0, zmm0, zmm13
	vpandq zmm0, zmm0, zmm9
	vpcmpuw k1, zmm0, zmm10, 1
	kmovd eax, k1
	mov edx, eax
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vpshufb xmm1, xmm0, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 8
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 1
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 16
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 2
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 24
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 3
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	add rsi, 48
2408:
	sub r10, 1
	jne 2406b
	cmp rdi, 241
	jb 2427f
	cmp rdi, 256
	jb 2429f
	add rsi, 24
	jmp 2430f
2429:
	mov ecx, 8
2431:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 2432f
	jmp 2433f
2432:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2434f
	jmp 2435f
2434:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2435:
2433:
	add rsi, 3
	sub rcx, 1
	jne 2431b
2430:
	jmp 2428f
2427:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
2428:
	mov QWORD PTR [rbx+4440], rdi
	mov r14d, 1
	mov rax, QWORD PTR [rbx+4424]
	shr rax, 8
	and r14d, eax
	mov rax, QWORD PTR [rbx+4432]
	shr rax, 8
	and r14d, eax
	mov rax, QWORD PTR [rbx+4440]
	shr rax, 8
	and r14d, eax
	cmp r14d, 0
	je 2436f
	jmp 2437f
2436:
	mov r14d, 1
	mov rbp, rbx
	add rbp, 2368
	mov r10d, 2
2438:
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
2439:
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
	jne 2439b
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
	mov rax, QWORD PTR [rbx+544]
	mov QWORD PTR [rbp+136], rax
	mov rax, QWORD PTR [rbx+576]
	mov QWORD PTR [rbp+144], rax
	mov rax, QWORD PTR [rbx+608]
	mov QWORD PTR [rbp+152], rax
	mov rax, QWORD PTR [rbx+640]
	mov QWORD PTR [rbp+160], rax
	mov rax, QWORD PTR [rbx+8]
	mov QWORD PTR [rbp+504], rax
	mov rax, QWORD PTR [rbx+40]
	mov QWORD PTR [rbp+512], rax
	mov rax, QWORD PTR [rbx+72]
	mov QWORD PTR [rbp+520], rax
	mov rax, QWORD PTR [rbx+104]
	mov QWORD PTR [rbp+528], rax
	mov rax, QWORD PTR [rbx+136]
	mov QWORD PTR [rbp+536], rax
	mov rax, QWORD PTR [rbx+168]
	mov QWORD PTR [rbp+544], rax
	mov rax, QWORD PTR [rbx+200]
	mov QWORD PTR [rbp+552], rax
	mov rax, QWORD PTR [rbx+232]
	mov QWORD PTR [rbp+560], rax
	mov rax, QWORD PTR [rbx+264]
	mov QWORD PTR [rbp+568], rax
	mov rax, QWORD PTR [rbx+296]
	mov QWORD PTR [rbp+576], rax
	mov rax, QWORD PTR [rbx+328]
	mov QWORD PTR [rbp+584], rax
	mov rax, QWORD PTR [rbx+360]
	mov QWORD PTR [rbp+592], rax
	mov rax, QWORD PTR [rbx+392]
	mov QWORD PTR [rbp+600], rax
	mov rax, QWORD PTR [rbx+424]
	mov QWORD PTR [rbp+608], rax
	mov rax, QWORD PTR [rbx+456]
	mov QWORD PTR [rbp+616], rax
	mov rax, QWORD PTR [rbx+488]
	mov QWORD PTR [rbp+624], rax
	mov rax, QWORD PTR [rbx+520]
	mov QWORD PTR [rbp+632], rax
	mov rax, QWORD PTR [rbx+552]
	mov QWORD PTR [rbp+640], rax
	mov rax, QWORD PTR [rbx+584]
	mov QWORD PTR [rbp+648], rax
	mov rax, QWORD PTR [rbx+616]
	mov QWORD PTR [rbp+656], rax
	mov rax, QWORD PTR [rbx+648]
	mov QWORD PTR [rbp+664], rax
	mov rax, QWORD PTR [rbx+16]
	mov QWORD PTR [rbp+1008], rax
	mov rax, QWORD PTR [rbx+48]
	mov QWORD PTR [rbp+1016], rax
	mov rax, QWORD PTR [rbx+80]
	mov QWORD PTR [rbp+1024], rax
	mov rax, QWORD PTR [rbx+112]
	mov QWORD PTR [rbp+1032], rax
	mov rax, QWORD PTR [rbx+144]
	mov QWORD PTR [rbp+1040], rax
	mov rax, QWORD PTR [rbx+176]
	mov QWORD PTR [rbp+1048], rax
	mov rax, QWORD PTR [rbx+208]
	mov QWORD PTR [rbp+1056], rax
	mov rax, QWORD PTR [rbx+240]
	mov QWORD PTR [rbp+1064], rax
	mov rax, QWORD PTR [rbx+272]
	mov QWORD PTR [rbp+1072], rax
	mov rax, QWORD PTR [rbx+304]
	mov QWORD PTR [rbp+1080], rax
	mov rax, QWORD PTR [rbx+336]
	mov QWORD PTR [rbp+1088], rax
	mov rax, QWORD PTR [rbx+368]
	mov QWORD PTR [rbp+1096], rax
	mov rax, QWORD PTR [rbx+400]
	mov QWORD PTR [rbp+1104], rax
	mov rax, QWORD PTR [rbx+432]
	mov QWORD PTR [rbp+1112], rax
	mov rax, QWORD PTR [rbx+464]
	mov QWORD PTR [rbp+1120], rax
	mov rax, QWORD PTR [rbx+496]
	mov QWORD PTR [rbp+1128], rax
	mov rax, QWORD PTR [rbx+528]
	mov QWORD PTR [rbp+1136], rax
	mov rax, QWORD PTR [rbx+560]
	mov QWORD PTR [rbp+1144], rax
	mov rax, QWORD PTR [rbx+592]
	mov QWORD PTR [rbp+1152], rax
	mov rax, QWORD PTR [rbx+624]
	mov QWORD PTR [rbp+1160], rax
	mov rax, QWORD PTR [rbx+656]
	mov QWORD PTR [rbp+1168], rax
	mov rax, QWORD PTR [rbx+24]
	mov QWORD PTR [rbp+1512], rax
	mov rax, QWORD PTR [rbx+56]
	mov QWORD PTR [rbp+1520], rax
	mov rax, QWORD PTR [rbx+88]
	mov QWORD PTR [rbp+1528], rax
	mov rax, QWORD PTR [rbx+120]
	mov QWORD PTR [rbp+1536], rax
	mov rax, QWORD PTR [rbx+152]
	mov QWORD PTR [rbp+1544], rax
	mov rax, QWORD PTR [rbx+184]
	mov QWORD PTR [rbp+1552], rax
	mov rax, QWORD PTR [rbx+216]
	mov QWORD PTR [rbp+1560], rax
	mov rax, QWORD PTR [rbx+248]
	mov QWORD PTR [rbp+1568], rax
	mov rax, QWORD PTR [rbx+280]
	mov QWORD PTR [rbp+1576], rax
	mov rax, QWORD PTR [rbx+312]
	mov QWORD PTR [rbp+1584], rax
	mov rax, QWORD PTR [rbx+344]
	mov QWORD PTR [rbp+1592], rax
	mov rax, QWORD PTR [rbx+376]
	mov QWORD PTR [rbp+1600], rax
	mov rax, QWORD PTR [rbx+408]
	mov QWORD PTR [rbp+1608], rax
	mov rax, QWORD PTR [rbx+440]
	mov QWORD PTR [rbp+1616], rax
	mov rax, QWORD PTR [rbx+472]
	mov QWORD PTR [rbp+1624], rax
	mov rax, QWORD PTR [rbx+504]
	mov QWORD PTR [rbp+1632], rax
	mov rax, QWORD PTR [rbx+536]
	mov QWORD PTR [rbp+1640], rax
	mov rax, QWORD PTR [rbx+568]
	mov QWORD PTR [rbp+1648], rax
	mov rax, QWORD PTR [rbx+600]
	mov QWORD PTR [rbp+1656], rax
	mov rax, QWORD PTR [rbx+632]
	mov QWORD PTR [rbp+1664], rax
	mov rax, QWORD PTR [rbx+664]
	mov QWORD PTR [rbp+1672], rax
	add rbp, 168
	sub r10, 1
	jne 2438b
	lea r11, {VG_MLKEM_SAMPLE_TBL}
	mov rsi, rbx
	add rsi, 2368
	mov rdi, QWORD PTR [rbx+4424]
	mov rbp, r13
	add rbp, 0
	mov r10d, 7
	vmovdqu ymm8, YMMWORD PTR [r11+4096]
	vmovdqu ymm9, YMMWORD PTR [r11+4128]
	vmovdqu ymm10, YMMWORD PTR [r11+4160]
	vmovdqu ymm12, YMMWORD PTR [r11+6240]
	vmovdqu ymm13, YMMWORD PTR [r11+6272]
	vshufi32x4 zmm12, zmm12, zmm13, 68
	vmovdqu ymm13, YMMWORD PTR [r11+6304]
	vshufi32x4 zmm13, zmm13, zmm13, 0
	vshufi32x4 zmm11, zmm8, zmm8, 0
	vshufi32x4 zmm9, zmm9, zmm9, 0
	vshufi32x4 zmm10, zmm10, zmm10, 0
2440:
	cmp rdi, 225
	jb 2441f
	cmp rdi, 241
	jb 2443f
	cmp rdi, 256
	jb 2445f
	add rsi, 24
	jmp 2446f
2445:
	mov ecx, 8
2447:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 2448f
	jmp 2449f
2448:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2450f
	jmp 2451f
2450:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2451:
2449:
	add rsi, 3
	sub rcx, 1
	jne 2447b
2446:
	jmp 2444f
2443:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
2444:
	cmp rdi, 241
	jb 2452f
	cmp rdi, 256
	jb 2454f
	add rsi, 24
	jmp 2455f
2454:
	mov ecx, 8
2456:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 2457f
	jmp 2458f
2457:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2459f
	jmp 2460f
2459:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2460:
2458:
	add rsi, 3
	sub rcx, 1
	jne 2456b
2455:
	jmp 2453f
2452:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
2453:
	jmp 2442f
2441:
	vmovdqu32 zmm0, ZMMWORD PTR [rsi]
	vpermw zmm0, zmm12, zmm0
	vpshufb zmm0, zmm0, zmm11
	vpsrlvw zmm0, zmm0, zmm13
	vpandq zmm0, zmm0, zmm9
	vpcmpuw k1, zmm0, zmm10, 1
	kmovd eax, k1
	mov edx, eax
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vpshufb xmm1, xmm0, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 8
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 1
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 16
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 2
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 24
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 3
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	add rsi, 48
2442:
	sub r10, 1
	jne 2440b
	mov QWORD PTR [rbx+4424], rdi
	mov rsi, rbx
	add rsi, 2872
	mov rdi, QWORD PTR [rbx+4432]
	mov rbp, r13
	add rbp, 512
	mov r10d, 7
	vmovdqu ymm8, YMMWORD PTR [r11+4096]
	vmovdqu ymm9, YMMWORD PTR [r11+4128]
	vmovdqu ymm10, YMMWORD PTR [r11+4160]
	vmovdqu ymm12, YMMWORD PTR [r11+6240]
	vmovdqu ymm13, YMMWORD PTR [r11+6272]
	vshufi32x4 zmm12, zmm12, zmm13, 68
	vmovdqu ymm13, YMMWORD PTR [r11+6304]
	vshufi32x4 zmm13, zmm13, zmm13, 0
	vshufi32x4 zmm11, zmm8, zmm8, 0
	vshufi32x4 zmm9, zmm9, zmm9, 0
	vshufi32x4 zmm10, zmm10, zmm10, 0
2461:
	cmp rdi, 225
	jb 2462f
	cmp rdi, 241
	jb 2464f
	cmp rdi, 256
	jb 2466f
	add rsi, 24
	jmp 2467f
2466:
	mov ecx, 8
2468:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 2469f
	jmp 2470f
2469:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2471f
	jmp 2472f
2471:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2472:
2470:
	add rsi, 3
	sub rcx, 1
	jne 2468b
2467:
	jmp 2465f
2464:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
2465:
	cmp rdi, 241
	jb 2473f
	cmp rdi, 256
	jb 2475f
	add rsi, 24
	jmp 2476f
2475:
	mov ecx, 8
2477:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 2478f
	jmp 2479f
2478:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2480f
	jmp 2481f
2480:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2481:
2479:
	add rsi, 3
	sub rcx, 1
	jne 2477b
2476:
	jmp 2474f
2473:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
2474:
	jmp 2463f
2462:
	vmovdqu32 zmm0, ZMMWORD PTR [rsi]
	vpermw zmm0, zmm12, zmm0
	vpshufb zmm0, zmm0, zmm11
	vpsrlvw zmm0, zmm0, zmm13
	vpandq zmm0, zmm0, zmm9
	vpcmpuw k1, zmm0, zmm10, 1
	kmovd eax, k1
	mov edx, eax
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vpshufb xmm1, xmm0, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 8
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 1
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 16
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 2
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 24
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 3
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	add rsi, 48
2463:
	sub r10, 1
	jne 2461b
	mov QWORD PTR [rbx+4432], rdi
	mov rsi, rbx
	add rsi, 3376
	mov rdi, QWORD PTR [rbx+4440]
	mov rbp, r13
	add rbp, 1024
	mov r10d, 7
	vmovdqu ymm8, YMMWORD PTR [r11+4096]
	vmovdqu ymm9, YMMWORD PTR [r11+4128]
	vmovdqu ymm10, YMMWORD PTR [r11+4160]
	vmovdqu ymm12, YMMWORD PTR [r11+6240]
	vmovdqu ymm13, YMMWORD PTR [r11+6272]
	vshufi32x4 zmm12, zmm12, zmm13, 68
	vmovdqu ymm13, YMMWORD PTR [r11+6304]
	vshufi32x4 zmm13, zmm13, zmm13, 0
	vshufi32x4 zmm11, zmm8, zmm8, 0
	vshufi32x4 zmm9, zmm9, zmm9, 0
	vshufi32x4 zmm10, zmm10, zmm10, 0
2482:
	cmp rdi, 225
	jb 2483f
	cmp rdi, 241
	jb 2485f
	cmp rdi, 256
	jb 2487f
	add rsi, 24
	jmp 2488f
2487:
	mov ecx, 8
2489:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 2490f
	jmp 2491f
2490:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2492f
	jmp 2493f
2492:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2493:
2491:
	add rsi, 3
	sub rcx, 1
	jne 2489b
2488:
	jmp 2486f
2485:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
2486:
	cmp rdi, 241
	jb 2494f
	cmp rdi, 256
	jb 2496f
	add rsi, 24
	jmp 2497f
2496:
	mov ecx, 8
2498:
	movzx eax, BYTE PTR [rsi]
	movzx edx, BYTE PTR [rsi+1]
	movzx r8d, BYTE PTR [rsi+2]
	mov r9d, edx
	and r9d, 15
	ror r9d, 24
	add r9d, eax
	shr edx, 4
	ror r8d, 28
	add r8d, edx
	cmp rdi, 256
	jb 2499f
	jmp 2500f
2499:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2501f
	jmp 2502f
2501:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2502:
2500:
	add rsi, 3
	sub rcx, 1
	jne 2498b
2497:
	jmp 2495f
2494:
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vpermq ymm0, ymm0, 148
	vpshufb ymm0, ymm0, ymm8
	vpsrlw ymm1, ymm0, 4
	vpblendw ymm0, ymm0, ymm1, 170
	vpand ymm0, ymm0, ymm9
	vpcmpgtw ymm1, ymm10, ymm0
	vpacksswb ymm1, ymm1, ymm1
	vpmovmskb eax, ymm1
	mov edx, eax
	and edx, 255
	shr eax, 24
	add edx, edx
	add eax, eax
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vmovdqu ymm3, YMMWORD PTR [r11+rax*8]
	vinserti128 ymm2, ymm2, xmm3, 1
	vpshufb ymm0, ymm0, ymm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rdx*4+4192]
	vextracti128 xmm0, ymm0, 1
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm0
	add rdi, QWORD PTR [r11+rax*4+4192]
	add rsi, 24
2495:
	jmp 2484f
2483:
	vmovdqu32 zmm0, ZMMWORD PTR [rsi]
	vpermw zmm0, zmm12, zmm0
	vpshufb zmm0, zmm0, zmm11
	vpsrlvw zmm0, zmm0, zmm13
	vpandq zmm0, zmm0, zmm9
	vpcmpuw k1, zmm0, zmm10, 1
	kmovd eax, k1
	mov edx, eax
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vpshufb xmm1, xmm0, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 8
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 1
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 16
	and edx, 255
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 2
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	mov edx, eax
	shr edx, 24
	add edx, edx
	vmovdqu ymm2, YMMWORD PTR [r11+rdx*8]
	vextracti32x4 xmm1, zmm0, 3
	vpshufb xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [rbp+rdi*2], xmm1
	add rdi, QWORD PTR [r11+rdx*4+4192]
	add rsi, 48
2484:
	sub r10, 1
	jne 2482b
	mov QWORD PTR [rbx+4440], rdi
	mov r14d, 1
	mov rax, QWORD PTR [rbx+4424]
	shr rax, 8
	and r14d, eax
	mov rax, QWORD PTR [rbx+4432]
	shr rax, 8
	and r14d, eax
	mov rax, QWORD PTR [rbx+4440]
	shr rax, 8
	and r14d, eax
2437:
	vzeroupper
	mov eax, r14d
	mov r14, QWORD PTR [rbx+4416]
	mov r13, QWORD PTR [rbx+4408]
	mov r12, QWORD PTR [rbx+4400]
	mov rbp, QWORD PTR [rbx+4392]
	mov rbx, QWORD PTR [rbx+4384]
	and r15d, eax
	test r15d, r15d
	jne 2503f
	jmp 2504f
2503:
	mov rdi, r12
	add rdi, 768
	mov rsi, rbx
	add rsi, 7168
	mov rdx, rbx
	add rdx, 20480
	mov rcx, rbx
	add rcx, 25600
	mov r8, rbx
	add r8, 26624
	call {vg_mlkem768_kpke_keygen_row}
	mov rdi, r12
	add rdi, 1152
	mov rsi, rbx
	add rsi, 1024
	mov ecx, 4
2505:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2505b
	mov rdi, r13
	add rdi, 1152
	mov rsi, r12
	add rsi, 0
	mov ecx, 148
2506:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2506b
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbx
	add rsi, 19008
	mov ecx, 25
2507:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2507b
	mov rdi, rbx
	add rdi, 0
	mov esi, 136
	mov edx, 0
	mov rcx, r12
	add rcx, 680
	mov r8d, 504
	mov r9, rbx
	add r9, 200
	call {vg_keccak_absorb_scratch}
	mov rdi, rbx
	add rdi, 0
	mov esi, 136
	mov edx, 96
	mov ecx, 6
	mov r8, rbx
	add r8, 200
	call {vg_keccak_pad_scratch}
	mov rdi, rbx
	add rdi, 0
	mov esi, 136
	mov edx, 0
	mov rcx, r13
	add rcx, 2336
	mov r8d, 32
	mov r9, rbx
	add r9, 200
	call {vg_keccak_squeeze_scratch}
	mov rdi, r13
	add rdi, 2368
	mov rsi, rbp
	add rsi, 32
	mov ecx, 4
2508:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2508b
2504:
	mov eax, r15d
	mov r15, QWORD PTR [rbx+880]
	mov r14, QWORD PTR [rbx+872]
	mov r13, QWORD PTR [rbx+864]
	mov r12, QWORD PTR [rbx+856]
	mov rbp, QWORD PTR [rbx+848]
	mov rbx, QWORD PTR [rbx+840]
	ret
	.p2align 6
