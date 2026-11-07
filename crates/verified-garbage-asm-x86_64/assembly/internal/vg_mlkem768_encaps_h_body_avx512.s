// The functions of `src/internal/vg_mlkem768_encaps_h_body_avx512.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem768_encaps_h_body_avx512:
	mov QWORD PTR [r9+840], rbx
	mov QWORD PTR [r9+848], rbp
	mov QWORD PTR [r9+856], r12
	mov QWORD PTR [r9+864], r13
	mov QWORD PTR [r9+872], r14
	mov QWORD PTR [r9+880], r15
	mov rbx, r9
	mov rbp, rdx
	mov r12, rcx
	mov r13, r8
	mov r14, rdi
	mov r15d, 1
	mov rdi, rbx
	add rdi, 1088
	mov rsi, rsi
	add rsi, 0
	mov ecx, 4
20:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 20b
	mov rdi, rbx
	add rdi, 1248
	mov rsi, rbp
	add rsi, 0
	mov ecx, 4
21:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 21b
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
	mov rcx, rbx
	add rcx, 1248
	mov r8d, 32
	mov r9, rbx
	add r9, 200
	call {vg_keccak_absorb_scratch}
	mov rdi, rbx
	add rdi, 0
	mov esi, 72
	mov edx, 32
	mov rcx, rbx
	add rcx, 1088
	mov r8d, 32
	mov r9, rbx
	add r9, 200
	call {vg_keccak_absorb_scratch}
	mov rdi, rbx
	add rdi, 0
	mov esi, 72
	mov edx, 64
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
	mov rsi, r14
	add rsi, 1152
	mov ecx, 4
22:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 22b
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
	mov r9d, 7937
	mov rbp, rbx
	add rbp, 2368
	mov r10d, 3
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
210:
	cmp rdi, 225
	jb 211f
	cmp rdi, 241
	jb 213f
	cmp rdi, 256
	jb 215f
	add rsi, 24
	jmp 216f
215:
	mov ecx, 8
217:
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
	jb 218f
	jmp 219f
218:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 220f
	jmp 221f
220:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
221:
219:
	add rsi, 3
	sub rcx, 1
	jne 217b
216:
	jmp 214f
213:
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
214:
	cmp rdi, 241
	jb 222f
	cmp rdi, 256
	jb 224f
	add rsi, 24
	jmp 225f
224:
	mov ecx, 8
226:
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
	jb 227f
	jmp 228f
227:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 229f
	jmp 230f
229:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
230:
228:
	add rsi, 3
	sub rcx, 1
	jne 226b
225:
	jmp 223f
222:
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
223:
	jmp 212f
211:
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
212:
	sub r10, 1
	jne 210b
	cmp rdi, 241
	jb 231f
	cmp rdi, 256
	jb 233f
	add rsi, 24
	jmp 234f
233:
	mov ecx, 8
235:
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
	jb 236f
	jmp 237f
236:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 238f
	jmp 239f
238:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
239:
237:
	add rsi, 3
	sub rcx, 1
	jne 235b
234:
	jmp 232f
231:
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
232:
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
240:
	cmp rdi, 225
	jb 241f
	cmp rdi, 241
	jb 243f
	cmp rdi, 256
	jb 245f
	add rsi, 24
	jmp 246f
245:
	mov ecx, 8
247:
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
	jb 248f
	jmp 249f
248:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 250f
	jmp 251f
250:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
251:
249:
	add rsi, 3
	sub rcx, 1
	jne 247b
246:
	jmp 244f
243:
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
244:
	cmp rdi, 241
	jb 252f
	cmp rdi, 256
	jb 254f
	add rsi, 24
	jmp 255f
254:
	mov ecx, 8
256:
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
	jb 257f
	jmp 258f
257:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 259f
	jmp 260f
259:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
260:
258:
	add rsi, 3
	sub rcx, 1
	jne 256b
255:
	jmp 253f
252:
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
253:
	jmp 242f
241:
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
242:
	sub r10, 1
	jne 240b
	cmp rdi, 241
	jb 261f
	cmp rdi, 256
	jb 263f
	add rsi, 24
	jmp 264f
263:
	mov ecx, 8
265:
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
	jb 266f
	jmp 267f
266:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 268f
	jmp 269f
268:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
269:
267:
	add rsi, 3
	sub rcx, 1
	jne 265b
264:
	jmp 262f
261:
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
262:
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
270:
	cmp rdi, 225
	jb 271f
	cmp rdi, 241
	jb 273f
	cmp rdi, 256
	jb 275f
	add rsi, 24
	jmp 276f
275:
	mov ecx, 8
277:
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
	jb 278f
	jmp 279f
278:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 280f
	jmp 281f
280:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
281:
279:
	add rsi, 3
	sub rcx, 1
	jne 277b
276:
	jmp 274f
273:
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
274:
	cmp rdi, 241
	jb 282f
	cmp rdi, 256
	jb 284f
	add rsi, 24
	jmp 285f
284:
	mov ecx, 8
286:
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
	jb 287f
	jmp 288f
287:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 289f
	jmp 290f
289:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
290:
288:
	add rsi, 3
	sub rcx, 1
	jne 286b
285:
	jmp 283f
282:
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
283:
	jmp 272f
271:
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
272:
	sub r10, 1
	jne 270b
	cmp rdi, 241
	jb 291f
	cmp rdi, 256
	jb 293f
	add rsi, 24
	jmp 294f
293:
	mov ecx, 8
295:
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
	jb 296f
	jmp 297f
296:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 298f
	jmp 299f
298:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
299:
297:
	add rsi, 3
	sub rcx, 1
	jne 295b
294:
	jmp 292f
291:
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
292:
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
	je 2100f
	jmp 2101f
2100:
	mov r14d, 1
	mov rbp, rbx
	add rbp, 2368
	mov r10d, 2
2102:
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
2103:
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
	jne 2103b
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
	jne 2102b
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
2104:
	cmp rdi, 225
	jb 2105f
	cmp rdi, 241
	jb 2107f
	cmp rdi, 256
	jb 2109f
	add rsi, 24
	jmp 2110f
2109:
	mov ecx, 8
2111:
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
	jb 2112f
	jmp 2113f
2112:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2114f
	jmp 2115f
2114:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2115:
2113:
	add rsi, 3
	sub rcx, 1
	jne 2111b
2110:
	jmp 2108f
2107:
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
2108:
	cmp rdi, 241
	jb 2116f
	cmp rdi, 256
	jb 2118f
	add rsi, 24
	jmp 2119f
2118:
	mov ecx, 8
2120:
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
	jb 2121f
	jmp 2122f
2121:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2123f
	jmp 2124f
2123:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2124:
2122:
	add rsi, 3
	sub rcx, 1
	jne 2120b
2119:
	jmp 2117f
2116:
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
2117:
	jmp 2106f
2105:
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
2106:
	sub r10, 1
	jne 2104b
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
2125:
	cmp rdi, 225
	jb 2126f
	cmp rdi, 241
	jb 2128f
	cmp rdi, 256
	jb 2130f
	add rsi, 24
	jmp 2131f
2130:
	mov ecx, 8
2132:
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
	jb 2133f
	jmp 2134f
2133:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2135f
	jmp 2136f
2135:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2136:
2134:
	add rsi, 3
	sub rcx, 1
	jne 2132b
2131:
	jmp 2129f
2128:
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
2129:
	cmp rdi, 241
	jb 2137f
	cmp rdi, 256
	jb 2139f
	add rsi, 24
	jmp 2140f
2139:
	mov ecx, 8
2141:
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
	jb 2142f
	jmp 2143f
2142:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2144f
	jmp 2145f
2144:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2145:
2143:
	add rsi, 3
	sub rcx, 1
	jne 2141b
2140:
	jmp 2138f
2137:
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
2138:
	jmp 2127f
2126:
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
2127:
	sub r10, 1
	jne 2125b
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
2146:
	cmp rdi, 225
	jb 2147f
	cmp rdi, 241
	jb 2149f
	cmp rdi, 256
	jb 2151f
	add rsi, 24
	jmp 2152f
2151:
	mov ecx, 8
2153:
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
	jb 2154f
	jmp 2155f
2154:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2156f
	jmp 2157f
2156:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2157:
2155:
	add rsi, 3
	sub rcx, 1
	jne 2153b
2152:
	jmp 2150f
2149:
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
2150:
	cmp rdi, 241
	jb 2158f
	cmp rdi, 256
	jb 2160f
	add rsi, 24
	jmp 2161f
2160:
	mov ecx, 8
2162:
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
	jb 2163f
	jmp 2164f
2163:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2165f
	jmp 2166f
2165:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2166:
2164:
	add rsi, 3
	sub rcx, 1
	jne 2162b
2161:
	jmp 2159f
2158:
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
2159:
	jmp 2148f
2147:
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
2148:
	sub r10, 1
	jne 2146b
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
2101:
	vzeroupper
	mov eax, r14d
	mov r14, QWORD PTR [rbx+4416]
	mov r13, QWORD PTR [rbx+4408]
	mov r12, QWORD PTR [rbx+4400]
	mov rbp, QWORD PTR [rbx+4392]
	mov rbx, QWORD PTR [rbx+4384]
	and r15d, eax
	mov rdi, rbx
	add rdi, 19712
	mov rsi, rbx
	add rsi, 9216
	call {vg_mlkem16_cbd2_avx2}
	mov rdi, rbx
	add rdi, 19840
	mov rsi, rbx
	add rsi, 9728
	call {vg_mlkem16_cbd2_avx2}
	mov rdi, rbx
	add rdi, 19968
	mov rsi, rbx
	add rsi, 10240
	call {vg_mlkem16_cbd2_avx2}
	mov rdi, rbx
	add rdi, 19208
	mov rsi, rbx
	add rsi, 1056
	mov ecx, 4
2167:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2167b
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
2168:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2168b
	mov eax, 0
	mov BYTE PTR [rbx+32], al
	mov eax, 1
	mov BYTE PTR [rbx+33], al
	mov rdi, rbx
	add rdi, 34
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
2169:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2169b
	mov eax, 1
	mov BYTE PTR [rbx+66], al
	mov eax, 1
	mov BYTE PTR [rbx+67], al
	mov rdi, rbx
	add rdi, 68
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
2170:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2170b
	mov eax, 2
	mov BYTE PTR [rbx+100], al
	mov eax, 1
	mov BYTE PTR [rbx+101], al
	mov rdi, rbx
	add rdi, 102
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
2171:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2171b
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
	mov r8, rbx
	add r8, 7424
	mov r9d, 7940
	mov rbp, rbx
	add rbp, 2368
	mov r10d, 3
2172:
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
2173:
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
	jne 2173b
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
	jne 2172b
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
2174:
	cmp rdi, 225
	jb 2175f
	cmp rdi, 241
	jb 2177f
	cmp rdi, 256
	jb 2179f
	add rsi, 24
	jmp 2180f
2179:
	mov ecx, 8
2181:
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
	jb 2182f
	jmp 2183f
2182:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2184f
	jmp 2185f
2184:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2185:
2183:
	add rsi, 3
	sub rcx, 1
	jne 2181b
2180:
	jmp 2178f
2177:
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
2178:
	cmp rdi, 241
	jb 2186f
	cmp rdi, 256
	jb 2188f
	add rsi, 24
	jmp 2189f
2188:
	mov ecx, 8
2190:
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
	jb 2191f
	jmp 2192f
2191:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2193f
	jmp 2194f
2193:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2194:
2192:
	add rsi, 3
	sub rcx, 1
	jne 2190b
2189:
	jmp 2187f
2186:
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
2187:
	jmp 2176f
2175:
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
2176:
	sub r10, 1
	jne 2174b
	cmp rdi, 241
	jb 2195f
	cmp rdi, 256
	jb 2197f
	add rsi, 24
	jmp 2198f
2197:
	mov ecx, 8
2199:
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
	jb 2200f
	jmp 2201f
2200:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2202f
	jmp 2203f
2202:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2203:
2201:
	add rsi, 3
	sub rcx, 1
	jne 2199b
2198:
	jmp 2196f
2195:
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
2196:
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
2204:
	cmp rdi, 225
	jb 2205f
	cmp rdi, 241
	jb 2207f
	cmp rdi, 256
	jb 2209f
	add rsi, 24
	jmp 2210f
2209:
	mov ecx, 8
2211:
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
	jb 2212f
	jmp 2213f
2212:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2214f
	jmp 2215f
2214:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2215:
2213:
	add rsi, 3
	sub rcx, 1
	jne 2211b
2210:
	jmp 2208f
2207:
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
2208:
	cmp rdi, 241
	jb 2216f
	cmp rdi, 256
	jb 2218f
	add rsi, 24
	jmp 2219f
2218:
	mov ecx, 8
2220:
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
	jb 2221f
	jmp 2222f
2221:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2223f
	jmp 2224f
2223:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2224:
2222:
	add rsi, 3
	sub rcx, 1
	jne 2220b
2219:
	jmp 2217f
2216:
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
2217:
	jmp 2206f
2205:
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
2206:
	sub r10, 1
	jne 2204b
	cmp rdi, 241
	jb 2225f
	cmp rdi, 256
	jb 2227f
	add rsi, 24
	jmp 2228f
2227:
	mov ecx, 8
2229:
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
	jb 2230f
	jmp 2231f
2230:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2232f
	jmp 2233f
2232:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2233:
2231:
	add rsi, 3
	sub rcx, 1
	jne 2229b
2228:
	jmp 2226f
2225:
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
2226:
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
2234:
	cmp rdi, 225
	jb 2235f
	cmp rdi, 241
	jb 2237f
	cmp rdi, 256
	jb 2239f
	add rsi, 24
	jmp 2240f
2239:
	mov ecx, 8
2241:
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
	jb 2242f
	jmp 2243f
2242:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2244f
	jmp 2245f
2244:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2245:
2243:
	add rsi, 3
	sub rcx, 1
	jne 2241b
2240:
	jmp 2238f
2237:
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
2238:
	cmp rdi, 241
	jb 2246f
	cmp rdi, 256
	jb 2248f
	add rsi, 24
	jmp 2249f
2248:
	mov ecx, 8
2250:
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
	jb 2251f
	jmp 2252f
2251:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2253f
	jmp 2254f
2253:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2254:
2252:
	add rsi, 3
	sub rcx, 1
	jne 2250b
2249:
	jmp 2247f
2246:
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
2247:
	jmp 2236f
2235:
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
2236:
	sub r10, 1
	jne 2234b
	cmp rdi, 241
	jb 2255f
	cmp rdi, 256
	jb 2257f
	add rsi, 24
	jmp 2258f
2257:
	mov ecx, 8
2259:
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
	jb 2260f
	jmp 2261f
2260:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2262f
	jmp 2263f
2262:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2263:
2261:
	add rsi, 3
	sub rcx, 1
	jne 2259b
2258:
	jmp 2256f
2255:
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
2256:
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
	je 2264f
	jmp 2265f
2264:
	mov r14d, 1
	mov rbp, rbx
	add rbp, 2368
	mov r10d, 2
2266:
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
2267:
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
	jne 2267b
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
	jne 2266b
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
2268:
	cmp rdi, 225
	jb 2269f
	cmp rdi, 241
	jb 2271f
	cmp rdi, 256
	jb 2273f
	add rsi, 24
	jmp 2274f
2273:
	mov ecx, 8
2275:
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
	jb 2276f
	jmp 2277f
2276:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2278f
	jmp 2279f
2278:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2279:
2277:
	add rsi, 3
	sub rcx, 1
	jne 2275b
2274:
	jmp 2272f
2271:
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
2272:
	cmp rdi, 241
	jb 2280f
	cmp rdi, 256
	jb 2282f
	add rsi, 24
	jmp 2283f
2282:
	mov ecx, 8
2284:
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
	jb 2285f
	jmp 2286f
2285:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2287f
	jmp 2288f
2287:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2288:
2286:
	add rsi, 3
	sub rcx, 1
	jne 2284b
2283:
	jmp 2281f
2280:
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
2281:
	jmp 2270f
2269:
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
2270:
	sub r10, 1
	jne 2268b
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
2289:
	cmp rdi, 225
	jb 2290f
	cmp rdi, 241
	jb 2292f
	cmp rdi, 256
	jb 2294f
	add rsi, 24
	jmp 2295f
2294:
	mov ecx, 8
2296:
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
	jb 2297f
	jmp 2298f
2297:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2299f
	jmp 2300f
2299:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2300:
2298:
	add rsi, 3
	sub rcx, 1
	jne 2296b
2295:
	jmp 2293f
2292:
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
2293:
	cmp rdi, 241
	jb 2301f
	cmp rdi, 256
	jb 2303f
	add rsi, 24
	jmp 2304f
2303:
	mov ecx, 8
2305:
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
	jb 2306f
	jmp 2307f
2306:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2308f
	jmp 2309f
2308:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2309:
2307:
	add rsi, 3
	sub rcx, 1
	jne 2305b
2304:
	jmp 2302f
2301:
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
2302:
	jmp 2291f
2290:
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
2291:
	sub r10, 1
	jne 2289b
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
2310:
	cmp rdi, 225
	jb 2311f
	cmp rdi, 241
	jb 2313f
	cmp rdi, 256
	jb 2315f
	add rsi, 24
	jmp 2316f
2315:
	mov ecx, 8
2317:
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
	jb 2318f
	jmp 2319f
2318:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2320f
	jmp 2321f
2320:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2321:
2319:
	add rsi, 3
	sub rcx, 1
	jne 2317b
2316:
	jmp 2314f
2313:
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
2314:
	cmp rdi, 241
	jb 2322f
	cmp rdi, 256
	jb 2324f
	add rsi, 24
	jmp 2325f
2324:
	mov ecx, 8
2326:
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
	jb 2327f
	jmp 2328f
2327:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2329f
	jmp 2330f
2329:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2330:
2328:
	add rsi, 3
	sub rcx, 1
	jne 2326b
2325:
	jmp 2323f
2322:
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
2323:
	jmp 2312f
2311:
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
2312:
	sub r10, 1
	jne 2310b
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
2265:
	vzeroupper
	mov eax, r14d
	mov r14, QWORD PTR [rbx+4416]
	mov r13, QWORD PTR [rbx+4408]
	mov r12, QWORD PTR [rbx+4400]
	mov rbp, QWORD PTR [rbx+4392]
	mov rbx, QWORD PTR [rbx+4384]
	and r15d, eax
	mov rdi, rbx
	add rdi, 19712
	mov rsi, rbx
	add rsi, 10752
	call {vg_mlkem16_cbd2_avx2}
	mov rdi, rbx
	add rdi, 19840
	mov rsi, rbx
	add rsi, 11264
	call {vg_mlkem16_cbd2_avx2}
	mov rdi, rbx
	add rdi, 19968
	mov rsi, rbx
	add rsi, 11776
	call {vg_mlkem16_cbd2_avx2}
	mov rdi, rbx
	add rdi, 19208
	mov rsi, rbx
	add rsi, 1056
	mov ecx, 4
2331:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2331b
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
2332:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2332b
	mov eax, 0
	mov BYTE PTR [rbx+32], al
	mov eax, 2
	mov BYTE PTR [rbx+33], al
	mov rdi, rbx
	add rdi, 34
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
2333:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2333b
	mov eax, 1
	mov BYTE PTR [rbx+66], al
	mov eax, 2
	mov BYTE PTR [rbx+67], al
	mov rdi, rbx
	add rdi, 68
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
2334:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2334b
	mov eax, 2
	mov BYTE PTR [rbx+100], al
	mov eax, 2
	mov BYTE PTR [rbx+101], al
	mov rdi, rbx
	add rdi, 102
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
2335:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2335b
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
	mov r8, rbx
	add r8, 7424
	mov r9d, 7936
	mov rbp, rbx
	add rbp, 2368
	mov r10d, 1
2336:
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
2337:
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
	jne 2337b
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
	jne 2336b
	mov rbp, rbx
	add rbp, 2536
	mov r10d, 2
2338:
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
2339:
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
	jne 2339b
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
	jne 2338b
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
2340:
	cmp rdi, 225
	jb 2341f
	cmp rdi, 241
	jb 2343f
	cmp rdi, 256
	jb 2345f
	add rsi, 24
	jmp 2346f
2345:
	mov ecx, 8
2347:
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
	jb 2348f
	jmp 2349f
2348:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2350f
	jmp 2351f
2350:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2351:
2349:
	add rsi, 3
	sub rcx, 1
	jne 2347b
2346:
	jmp 2344f
2343:
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
2344:
	cmp rdi, 241
	jb 2352f
	cmp rdi, 256
	jb 2354f
	add rsi, 24
	jmp 2355f
2354:
	mov ecx, 8
2356:
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
	jb 2357f
	jmp 2358f
2357:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2359f
	jmp 2360f
2359:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2360:
2358:
	add rsi, 3
	sub rcx, 1
	jne 2356b
2355:
	jmp 2353f
2352:
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
2353:
	jmp 2342f
2341:
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
2342:
	sub r10, 1
	jne 2340b
	cmp rdi, 241
	jb 2361f
	cmp rdi, 256
	jb 2363f
	add rsi, 24
	jmp 2364f
2363:
	mov ecx, 8
2365:
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
	jb 2366f
	jmp 2367f
2366:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2368f
	jmp 2369f
2368:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2369:
2367:
	add rsi, 3
	sub rcx, 1
	jne 2365b
2364:
	jmp 2362f
2361:
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
2362:
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
2370:
	cmp rdi, 225
	jb 2371f
	cmp rdi, 241
	jb 2373f
	cmp rdi, 256
	jb 2375f
	add rsi, 24
	jmp 2376f
2375:
	mov ecx, 8
2377:
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
	jb 2378f
	jmp 2379f
2378:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2380f
	jmp 2381f
2380:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2381:
2379:
	add rsi, 3
	sub rcx, 1
	jne 2377b
2376:
	jmp 2374f
2373:
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
2374:
	cmp rdi, 241
	jb 2382f
	cmp rdi, 256
	jb 2384f
	add rsi, 24
	jmp 2385f
2384:
	mov ecx, 8
2386:
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
	jb 2387f
	jmp 2388f
2387:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2389f
	jmp 2390f
2389:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2390:
2388:
	add rsi, 3
	sub rcx, 1
	jne 2386b
2385:
	jmp 2383f
2382:
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
2383:
	jmp 2372f
2371:
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
2372:
	sub r10, 1
	jne 2370b
	cmp rdi, 241
	jb 2391f
	cmp rdi, 256
	jb 2393f
	add rsi, 24
	jmp 2394f
2393:
	mov ecx, 8
2395:
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
	jb 2396f
	jmp 2397f
2396:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2398f
	jmp 2399f
2398:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2399:
2397:
	add rsi, 3
	sub rcx, 1
	jne 2395b
2394:
	jmp 2392f
2391:
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
2392:
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
2400:
	cmp rdi, 225
	jb 2401f
	cmp rdi, 241
	jb 2403f
	cmp rdi, 256
	jb 2405f
	add rsi, 24
	jmp 2406f
2405:
	mov ecx, 8
2407:
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
	jb 2408f
	jmp 2409f
2408:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2410f
	jmp 2411f
2410:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2411:
2409:
	add rsi, 3
	sub rcx, 1
	jne 2407b
2406:
	jmp 2404f
2403:
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
2404:
	cmp rdi, 241
	jb 2412f
	cmp rdi, 256
	jb 2414f
	add rsi, 24
	jmp 2415f
2414:
	mov ecx, 8
2416:
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
	jb 2417f
	jmp 2418f
2417:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2419f
	jmp 2420f
2419:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2420:
2418:
	add rsi, 3
	sub rcx, 1
	jne 2416b
2415:
	jmp 2413f
2412:
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
2413:
	jmp 2402f
2401:
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
2402:
	sub r10, 1
	jne 2400b
	cmp rdi, 241
	jb 2421f
	cmp rdi, 256
	jb 2423f
	add rsi, 24
	jmp 2424f
2423:
	mov ecx, 8
2425:
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
	jb 2426f
	jmp 2427f
2426:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2428f
	jmp 2429f
2428:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2429:
2427:
	add rsi, 3
	sub rcx, 1
	jne 2425b
2424:
	jmp 2422f
2421:
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
2422:
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
	je 2430f
	jmp 2431f
2430:
	mov r14d, 1
	mov rbp, rbx
	add rbp, 2368
	mov r10d, 2
2432:
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
2433:
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
	jne 2433b
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
	jne 2432b
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
2434:
	cmp rdi, 225
	jb 2435f
	cmp rdi, 241
	jb 2437f
	cmp rdi, 256
	jb 2439f
	add rsi, 24
	jmp 2440f
2439:
	mov ecx, 8
2441:
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
	jb 2442f
	jmp 2443f
2442:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2444f
	jmp 2445f
2444:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2445:
2443:
	add rsi, 3
	sub rcx, 1
	jne 2441b
2440:
	jmp 2438f
2437:
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
2438:
	cmp rdi, 241
	jb 2446f
	cmp rdi, 256
	jb 2448f
	add rsi, 24
	jmp 2449f
2448:
	mov ecx, 8
2450:
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
	jb 2451f
	jmp 2452f
2451:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2453f
	jmp 2454f
2453:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2454:
2452:
	add rsi, 3
	sub rcx, 1
	jne 2450b
2449:
	jmp 2447f
2446:
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
2447:
	jmp 2436f
2435:
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
2436:
	sub r10, 1
	jne 2434b
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
2455:
	cmp rdi, 225
	jb 2456f
	cmp rdi, 241
	jb 2458f
	cmp rdi, 256
	jb 2460f
	add rsi, 24
	jmp 2461f
2460:
	mov ecx, 8
2462:
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
	jb 2463f
	jmp 2464f
2463:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2465f
	jmp 2466f
2465:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2466:
2464:
	add rsi, 3
	sub rcx, 1
	jne 2462b
2461:
	jmp 2459f
2458:
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
2459:
	cmp rdi, 241
	jb 2467f
	cmp rdi, 256
	jb 2469f
	add rsi, 24
	jmp 2470f
2469:
	mov ecx, 8
2471:
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
	jb 2472f
	jmp 2473f
2472:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2474f
	jmp 2475f
2474:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2475:
2473:
	add rsi, 3
	sub rcx, 1
	jne 2471b
2470:
	jmp 2468f
2467:
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
2468:
	jmp 2457f
2456:
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
2457:
	sub r10, 1
	jne 2455b
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
2476:
	cmp rdi, 225
	jb 2477f
	cmp rdi, 241
	jb 2479f
	cmp rdi, 256
	jb 2481f
	add rsi, 24
	jmp 2482f
2481:
	mov ecx, 8
2483:
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
	jb 2484f
	jmp 2485f
2484:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2486f
	jmp 2487f
2486:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2487:
2485:
	add rsi, 3
	sub rcx, 1
	jne 2483b
2482:
	jmp 2480f
2479:
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
2480:
	cmp rdi, 241
	jb 2488f
	cmp rdi, 256
	jb 2490f
	add rsi, 24
	jmp 2491f
2490:
	mov ecx, 8
2492:
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
	jb 2493f
	jmp 2494f
2493:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2495f
	jmp 2496f
2495:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2496:
2494:
	add rsi, 3
	sub rcx, 1
	jne 2492b
2491:
	jmp 2489f
2488:
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
2489:
	jmp 2478f
2477:
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
2478:
	sub r10, 1
	jne 2476b
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
2431:
	vzeroupper
	mov eax, r14d
	mov r14, QWORD PTR [rbx+4416]
	mov r13, QWORD PTR [rbx+4408]
	mov r12, QWORD PTR [rbx+4400]
	mov rbp, QWORD PTR [rbx+4392]
	mov rbx, QWORD PTR [rbx+4384]
	and r15d, eax
	mov rdi, rbx
	add rdi, 19712
	mov rsi, rbx
	add rsi, 8704
	call {vg_mlkem16_cbd2_avx2}
	test r15d, r15d
	jne 2497f
	jmp 2498f
2497:
	mov rdi, r13
	add rdi, 0
	mov rsi, rbx
	add rsi, 4096
	mov rdx, r14
	add rdx, 0
	mov rcx, rbx
	add rcx, 8704
	mov r8, rbx
	add r8, 1248
	mov r9, rbx
	add r9, 12288
	call {vg_mlkem768_kpke_encrypt}
2498:
	mov rdi, r12
	add rdi, 0
	mov rsi, rbx
	add rsi, 1024
	mov ecx, 4
2499:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2499b
	mov eax, r15d
	mov r15, QWORD PTR [rbx+880]
	mov r14, QWORD PTR [rbx+872]
	mov r13, QWORD PTR [rbx+864]
	mov r12, QWORD PTR [rbx+856]
	mov rbp, QWORD PTR [rbx+848]
	mov rbx, QWORD PTR [rbx+840]
	ret
	.p2align 6
