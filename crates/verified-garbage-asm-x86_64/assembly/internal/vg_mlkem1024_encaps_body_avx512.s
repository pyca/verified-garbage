// The functions of `src/internal/vg_mlkem1024_encaps_body_avx512.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem1024_encaps_body_avx512:
	mov QWORD PTR [r8+840], rbx
	mov QWORD PTR [r8+848], rbp
	mov QWORD PTR [r8+856], r12
	mov QWORD PTR [r8+864], r13
	mov QWORD PTR [r8+872], r14
	mov QWORD PTR [r8+880], r15
	mov rbx, r8
	mov rbp, rsi
	mov r12, rdx
	mov r13, rcx
	mov r14, rdi
	mov r15d, 1
	mov rdi, rbx
	add rdi, 904
	mov rsi, r14
	add rsi, 1536
	mov ecx, 4
20:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 20b
	mov eax, 0
	mov QWORD PTR [rbx+23616], rax
	mov QWORD PTR [rbx+23624], rax
	mov QWORD PTR [rbx+23632], rax
	mov QWORD PTR [rbx+23640], rax
	mov QWORD PTR [rbx+23648], rax
	mov QWORD PTR [rbx+23656], rax
	mov QWORD PTR [rbx+23664], rax
	mov QWORD PTR [rbx+23672], rax
	mov QWORD PTR [rbx+23680], rax
	mov QWORD PTR [rbx+23688], rax
	mov QWORD PTR [rbx+23696], rax
	mov QWORD PTR [rbx+23704], rax
	mov QWORD PTR [rbx+23712], rax
	mov QWORD PTR [rbx+23720], rax
	mov QWORD PTR [rbx+23728], rax
	mov QWORD PTR [rbx+23736], rax
	mov QWORD PTR [rbx+23744], rax
	mov QWORD PTR [rbx+23752], rax
	mov QWORD PTR [rbx+23760], rax
	mov QWORD PTR [rbx+23768], rax
	mov QWORD PTR [rbx+23776], rax
	mov QWORD PTR [rbx+23784], rax
	mov QWORD PTR [rbx+23792], rax
	mov QWORD PTR [rbx+23800], rax
	mov QWORD PTR [rbx+23808], rax
	mov rdi, rbx
	add rdi, 23816
	mov rsi, r14
	add rsi, 0
	mov ecx, 51
21:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 21b
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
22:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 22b
	mov eax, 0
	mov BYTE PTR [rbx+32], al
	mov eax, 0
	mov BYTE PTR [rbx+33], al
	mov rdi, rbx
	add rdi, 34
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
23:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 23b
	mov eax, 1
	mov BYTE PTR [rbx+66], al
	mov eax, 0
	mov BYTE PTR [rbx+67], al
	mov rdi, rbx
	add rdi, 68
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
	mov eax, 2
	mov BYTE PTR [rbx+100], al
	mov eax, 0
	mov BYTE PTR [rbx+101], al
	mov rdi, rbx
	add rdi, 102
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
	mov eax, 3
	mov BYTE PTR [rbx+134], al
	mov eax, 0
	mov BYTE PTR [rbx+135], al
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbx
	add rsi, 4096
	mov rdx, rbx
	add rdx, 16896
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
26:
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
27:
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
	jne 27b
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
	jne 26b
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
28:
	cmp rdi, 225
	jb 29f
	cmp rdi, 241
	jb 211f
	cmp rdi, 256
	jb 213f
	add rsi, 24
	jmp 214f
213:
	mov ecx, 8
215:
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
	jb 216f
	jmp 217f
216:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 218f
	jmp 219f
218:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
219:
217:
	add rsi, 3
	sub rcx, 1
	jne 215b
214:
	jmp 212f
211:
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
212:
	cmp rdi, 241
	jb 220f
	cmp rdi, 256
	jb 222f
	add rsi, 24
	jmp 223f
222:
	mov ecx, 8
224:
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
	jb 225f
	jmp 226f
225:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 227f
	jmp 228f
227:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
228:
226:
	add rsi, 3
	sub rcx, 1
	jne 224b
223:
	jmp 221f
220:
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
221:
	jmp 210f
29:
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
210:
	sub r10, 1
	jne 28b
	cmp rdi, 241
	jb 229f
	cmp rdi, 256
	jb 231f
	add rsi, 24
	jmp 232f
231:
	mov ecx, 8
233:
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
	jb 234f
	jmp 235f
234:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 236f
	jmp 237f
236:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
237:
235:
	add rsi, 3
	sub rcx, 1
	jne 233b
232:
	jmp 230f
229:
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
230:
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
238:
	cmp rdi, 225
	jb 239f
	cmp rdi, 241
	jb 241f
	cmp rdi, 256
	jb 243f
	add rsi, 24
	jmp 244f
243:
	mov ecx, 8
245:
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
	jb 246f
	jmp 247f
246:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 248f
	jmp 249f
248:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
249:
247:
	add rsi, 3
	sub rcx, 1
	jne 245b
244:
	jmp 242f
241:
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
242:
	cmp rdi, 241
	jb 250f
	cmp rdi, 256
	jb 252f
	add rsi, 24
	jmp 253f
252:
	mov ecx, 8
254:
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
	jb 255f
	jmp 256f
255:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 257f
	jmp 258f
257:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
258:
256:
	add rsi, 3
	sub rcx, 1
	jne 254b
253:
	jmp 251f
250:
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
251:
	jmp 240f
239:
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
240:
	sub r10, 1
	jne 238b
	cmp rdi, 241
	jb 259f
	cmp rdi, 256
	jb 261f
	add rsi, 24
	jmp 262f
261:
	mov ecx, 8
263:
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
	jb 264f
	jmp 265f
264:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 266f
	jmp 267f
266:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
267:
265:
	add rsi, 3
	sub rcx, 1
	jne 263b
262:
	jmp 260f
259:
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
260:
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
268:
	cmp rdi, 225
	jb 269f
	cmp rdi, 241
	jb 271f
	cmp rdi, 256
	jb 273f
	add rsi, 24
	jmp 274f
273:
	mov ecx, 8
275:
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
	jb 276f
	jmp 277f
276:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 278f
	jmp 279f
278:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
279:
277:
	add rsi, 3
	sub rcx, 1
	jne 275b
274:
	jmp 272f
271:
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
272:
	cmp rdi, 241
	jb 280f
	cmp rdi, 256
	jb 282f
	add rsi, 24
	jmp 283f
282:
	mov ecx, 8
284:
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
	jb 285f
	jmp 286f
285:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 287f
	jmp 288f
287:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
288:
286:
	add rsi, 3
	sub rcx, 1
	jne 284b
283:
	jmp 281f
280:
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
281:
	jmp 270f
269:
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
270:
	sub r10, 1
	jne 268b
	cmp rdi, 241
	jb 289f
	cmp rdi, 256
	jb 291f
	add rsi, 24
	jmp 292f
291:
	mov ecx, 8
293:
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
	jb 294f
	jmp 295f
294:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 296f
	jmp 297f
296:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
297:
295:
	add rsi, 3
	sub rcx, 1
	jne 293b
292:
	jmp 290f
289:
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
290:
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
	je 298f
	jmp 299f
298:
	mov r14d, 1
	mov rbp, rbx
	add rbp, 2368
	mov r10d, 2
2100:
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
2101:
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
	jne 2101b
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
	jne 2100b
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
2102:
	cmp rdi, 225
	jb 2103f
	cmp rdi, 241
	jb 2105f
	cmp rdi, 256
	jb 2107f
	add rsi, 24
	jmp 2108f
2107:
	mov ecx, 8
2109:
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
	jb 2110f
	jmp 2111f
2110:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2112f
	jmp 2113f
2112:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2113:
2111:
	add rsi, 3
	sub rcx, 1
	jne 2109b
2108:
	jmp 2106f
2105:
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
2106:
	cmp rdi, 241
	jb 2114f
	cmp rdi, 256
	jb 2116f
	add rsi, 24
	jmp 2117f
2116:
	mov ecx, 8
2118:
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
	jb 2119f
	jmp 2120f
2119:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2121f
	jmp 2122f
2121:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2122:
2120:
	add rsi, 3
	sub rcx, 1
	jne 2118b
2117:
	jmp 2115f
2114:
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
2115:
	jmp 2104f
2103:
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
2104:
	sub r10, 1
	jne 2102b
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
2123:
	cmp rdi, 225
	jb 2124f
	cmp rdi, 241
	jb 2126f
	cmp rdi, 256
	jb 2128f
	add rsi, 24
	jmp 2129f
2128:
	mov ecx, 8
2130:
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
	jb 2131f
	jmp 2132f
2131:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2133f
	jmp 2134f
2133:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2134:
2132:
	add rsi, 3
	sub rcx, 1
	jne 2130b
2129:
	jmp 2127f
2126:
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
2127:
	cmp rdi, 241
	jb 2135f
	cmp rdi, 256
	jb 2137f
	add rsi, 24
	jmp 2138f
2137:
	mov ecx, 8
2139:
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
	jb 2140f
	jmp 2141f
2140:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2142f
	jmp 2143f
2142:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2143:
2141:
	add rsi, 3
	sub rcx, 1
	jne 2139b
2138:
	jmp 2136f
2135:
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
2136:
	jmp 2125f
2124:
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
2125:
	sub r10, 1
	jne 2123b
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
2144:
	cmp rdi, 225
	jb 2145f
	cmp rdi, 241
	jb 2147f
	cmp rdi, 256
	jb 2149f
	add rsi, 24
	jmp 2150f
2149:
	mov ecx, 8
2151:
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
	jb 2152f
	jmp 2153f
2152:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2154f
	jmp 2155f
2154:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2155:
2153:
	add rsi, 3
	sub rcx, 1
	jne 2151b
2150:
	jmp 2148f
2147:
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
2148:
	cmp rdi, 241
	jb 2156f
	cmp rdi, 256
	jb 2158f
	add rsi, 24
	jmp 2159f
2158:
	mov ecx, 8
2160:
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
	jb 2161f
	jmp 2162f
2161:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2163f
	jmp 2164f
2163:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2164:
2162:
	add rsi, 3
	sub rcx, 1
	jne 2160b
2159:
	jmp 2157f
2156:
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
2157:
	jmp 2146f
2145:
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
2146:
	sub r10, 1
	jne 2144b
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
299:
	vzeroupper
	mov eax, r14d
	mov r14, QWORD PTR [rbx+4416]
	mov r13, QWORD PTR [rbx+4408]
	mov r12, QWORD PTR [rbx+4400]
	mov rbp, QWORD PTR [rbx+4392]
	mov rbx, QWORD PTR [rbx+4384]
	and r15d, eax
	mov rdi, rbx
	add rdi, 23816
	mov rsi, r14
	add rsi, 408
	mov ecx, 51
2165:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2165b
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
2166:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2166b
	mov eax, 3
	mov BYTE PTR [rbx+32], al
	mov eax, 0
	mov BYTE PTR [rbx+33], al
	mov rdi, rbx
	add rdi, 34
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
2167:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2167b
	mov eax, 0
	mov BYTE PTR [rbx+66], al
	mov eax, 1
	mov BYTE PTR [rbx+67], al
	mov rdi, rbx
	add rdi, 68
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
	mov eax, 1
	mov BYTE PTR [rbx+100], al
	mov eax, 1
	mov BYTE PTR [rbx+101], al
	mov rdi, rbx
	add rdi, 102
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
	mov eax, 2
	mov BYTE PTR [rbx+134], al
	mov eax, 1
	mov BYTE PTR [rbx+135], al
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbx
	add rsi, 5632
	mov rdx, rbx
	add rdx, 16896
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
2170:
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
2171:
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
	jne 2171b
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
	jne 2170b
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
2172:
	cmp rdi, 225
	jb 2173f
	cmp rdi, 241
	jb 2175f
	cmp rdi, 256
	jb 2177f
	add rsi, 24
	jmp 2178f
2177:
	mov ecx, 8
2179:
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
	jb 2180f
	jmp 2181f
2180:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2182f
	jmp 2183f
2182:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2183:
2181:
	add rsi, 3
	sub rcx, 1
	jne 2179b
2178:
	jmp 2176f
2175:
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
2176:
	cmp rdi, 241
	jb 2184f
	cmp rdi, 256
	jb 2186f
	add rsi, 24
	jmp 2187f
2186:
	mov ecx, 8
2188:
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
	jb 2189f
	jmp 2190f
2189:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2191f
	jmp 2192f
2191:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2192:
2190:
	add rsi, 3
	sub rcx, 1
	jne 2188b
2187:
	jmp 2185f
2184:
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
2185:
	jmp 2174f
2173:
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
2174:
	sub r10, 1
	jne 2172b
	cmp rdi, 241
	jb 2193f
	cmp rdi, 256
	jb 2195f
	add rsi, 24
	jmp 2196f
2195:
	mov ecx, 8
2197:
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
	jb 2198f
	jmp 2199f
2198:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2200f
	jmp 2201f
2200:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2201:
2199:
	add rsi, 3
	sub rcx, 1
	jne 2197b
2196:
	jmp 2194f
2193:
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
2194:
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
2202:
	cmp rdi, 225
	jb 2203f
	cmp rdi, 241
	jb 2205f
	cmp rdi, 256
	jb 2207f
	add rsi, 24
	jmp 2208f
2207:
	mov ecx, 8
2209:
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
	jb 2210f
	jmp 2211f
2210:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2212f
	jmp 2213f
2212:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2213:
2211:
	add rsi, 3
	sub rcx, 1
	jne 2209b
2208:
	jmp 2206f
2205:
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
2206:
	cmp rdi, 241
	jb 2214f
	cmp rdi, 256
	jb 2216f
	add rsi, 24
	jmp 2217f
2216:
	mov ecx, 8
2218:
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
	jb 2219f
	jmp 2220f
2219:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2221f
	jmp 2222f
2221:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2222:
2220:
	add rsi, 3
	sub rcx, 1
	jne 2218b
2217:
	jmp 2215f
2214:
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
2215:
	jmp 2204f
2203:
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
2204:
	sub r10, 1
	jne 2202b
	cmp rdi, 241
	jb 2223f
	cmp rdi, 256
	jb 2225f
	add rsi, 24
	jmp 2226f
2225:
	mov ecx, 8
2227:
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
	jb 2228f
	jmp 2229f
2228:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2230f
	jmp 2231f
2230:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2231:
2229:
	add rsi, 3
	sub rcx, 1
	jne 2227b
2226:
	jmp 2224f
2223:
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
2224:
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
2232:
	cmp rdi, 225
	jb 2233f
	cmp rdi, 241
	jb 2235f
	cmp rdi, 256
	jb 2237f
	add rsi, 24
	jmp 2238f
2237:
	mov ecx, 8
2239:
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
	jb 2240f
	jmp 2241f
2240:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2242f
	jmp 2243f
2242:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2243:
2241:
	add rsi, 3
	sub rcx, 1
	jne 2239b
2238:
	jmp 2236f
2235:
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
2236:
	cmp rdi, 241
	jb 2244f
	cmp rdi, 256
	jb 2246f
	add rsi, 24
	jmp 2247f
2246:
	mov ecx, 8
2248:
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
	jb 2249f
	jmp 2250f
2249:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2251f
	jmp 2252f
2251:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2252:
2250:
	add rsi, 3
	sub rcx, 1
	jne 2248b
2247:
	jmp 2245f
2244:
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
2245:
	jmp 2234f
2233:
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
2234:
	sub r10, 1
	jne 2232b
	cmp rdi, 241
	jb 2253f
	cmp rdi, 256
	jb 2255f
	add rsi, 24
	jmp 2256f
2255:
	mov ecx, 8
2257:
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
	jb 2258f
	jmp 2259f
2258:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2260f
	jmp 2261f
2260:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2261:
2259:
	add rsi, 3
	sub rcx, 1
	jne 2257b
2256:
	jmp 2254f
2253:
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
2254:
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
	je 2262f
	jmp 2263f
2262:
	mov r14d, 1
	mov rbp, rbx
	add rbp, 2368
	mov r10d, 2
2264:
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
2265:
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
	jne 2265b
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
	jne 2264b
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
2266:
	cmp rdi, 225
	jb 2267f
	cmp rdi, 241
	jb 2269f
	cmp rdi, 256
	jb 2271f
	add rsi, 24
	jmp 2272f
2271:
	mov ecx, 8
2273:
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
	jb 2274f
	jmp 2275f
2274:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2276f
	jmp 2277f
2276:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2277:
2275:
	add rsi, 3
	sub rcx, 1
	jne 2273b
2272:
	jmp 2270f
2269:
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
2270:
	cmp rdi, 241
	jb 2278f
	cmp rdi, 256
	jb 2280f
	add rsi, 24
	jmp 2281f
2280:
	mov ecx, 8
2282:
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
	jb 2283f
	jmp 2284f
2283:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2285f
	jmp 2286f
2285:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2286:
2284:
	add rsi, 3
	sub rcx, 1
	jne 2282b
2281:
	jmp 2279f
2278:
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
2279:
	jmp 2268f
2267:
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
2268:
	sub r10, 1
	jne 2266b
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
2287:
	cmp rdi, 225
	jb 2288f
	cmp rdi, 241
	jb 2290f
	cmp rdi, 256
	jb 2292f
	add rsi, 24
	jmp 2293f
2292:
	mov ecx, 8
2294:
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
	jb 2295f
	jmp 2296f
2295:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2297f
	jmp 2298f
2297:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2298:
2296:
	add rsi, 3
	sub rcx, 1
	jne 2294b
2293:
	jmp 2291f
2290:
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
2291:
	cmp rdi, 241
	jb 2299f
	cmp rdi, 256
	jb 2301f
	add rsi, 24
	jmp 2302f
2301:
	mov ecx, 8
2303:
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
	jb 2304f
	jmp 2305f
2304:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2306f
	jmp 2307f
2306:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2307:
2305:
	add rsi, 3
	sub rcx, 1
	jne 2303b
2302:
	jmp 2300f
2299:
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
2300:
	jmp 2289f
2288:
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
2289:
	sub r10, 1
	jne 2287b
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
2308:
	cmp rdi, 225
	jb 2309f
	cmp rdi, 241
	jb 2311f
	cmp rdi, 256
	jb 2313f
	add rsi, 24
	jmp 2314f
2313:
	mov ecx, 8
2315:
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
	jb 2316f
	jmp 2317f
2316:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2318f
	jmp 2319f
2318:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2319:
2317:
	add rsi, 3
	sub rcx, 1
	jne 2315b
2314:
	jmp 2312f
2311:
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
2312:
	cmp rdi, 241
	jb 2320f
	cmp rdi, 256
	jb 2322f
	add rsi, 24
	jmp 2323f
2322:
	mov ecx, 8
2324:
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
	jb 2325f
	jmp 2326f
2325:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2327f
	jmp 2328f
2327:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2328:
2326:
	add rsi, 3
	sub rcx, 1
	jne 2324b
2323:
	jmp 2321f
2320:
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
2321:
	jmp 2310f
2309:
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
2310:
	sub r10, 1
	jne 2308b
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
2263:
	vzeroupper
	mov eax, r14d
	mov r14, QWORD PTR [rbx+4416]
	mov r13, QWORD PTR [rbx+4408]
	mov r12, QWORD PTR [rbx+4400]
	mov rbp, QWORD PTR [rbx+4392]
	mov rbx, QWORD PTR [rbx+4384]
	and r15d, eax
	mov rdi, rbx
	add rdi, 23816
	mov rsi, r14
	add rsi, 816
	mov ecx, 51
2329:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2329b
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
2330:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2330b
	mov eax, 2
	mov BYTE PTR [rbx+32], al
	mov eax, 1
	mov BYTE PTR [rbx+33], al
	mov rdi, rbx
	add rdi, 34
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
2331:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2331b
	mov eax, 3
	mov BYTE PTR [rbx+66], al
	mov eax, 1
	mov BYTE PTR [rbx+67], al
	mov rdi, rbx
	add rdi, 68
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
	mov BYTE PTR [rbx+100], al
	mov eax, 2
	mov BYTE PTR [rbx+101], al
	mov rdi, rbx
	add rdi, 102
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
	mov BYTE PTR [rbx+134], al
	mov eax, 2
	mov BYTE PTR [rbx+135], al
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbx
	add rsi, 7168
	mov rdx, rbx
	add rdx, 16896
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
2334:
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
2335:
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
	jne 2335b
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
	jne 2334b
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
2336:
	cmp rdi, 225
	jb 2337f
	cmp rdi, 241
	jb 2339f
	cmp rdi, 256
	jb 2341f
	add rsi, 24
	jmp 2342f
2341:
	mov ecx, 8
2343:
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
	jb 2344f
	jmp 2345f
2344:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2346f
	jmp 2347f
2346:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2347:
2345:
	add rsi, 3
	sub rcx, 1
	jne 2343b
2342:
	jmp 2340f
2339:
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
2340:
	cmp rdi, 241
	jb 2348f
	cmp rdi, 256
	jb 2350f
	add rsi, 24
	jmp 2351f
2350:
	mov ecx, 8
2352:
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
	jb 2353f
	jmp 2354f
2353:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2355f
	jmp 2356f
2355:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2356:
2354:
	add rsi, 3
	sub rcx, 1
	jne 2352b
2351:
	jmp 2349f
2348:
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
2349:
	jmp 2338f
2337:
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
2338:
	sub r10, 1
	jne 2336b
	cmp rdi, 241
	jb 2357f
	cmp rdi, 256
	jb 2359f
	add rsi, 24
	jmp 2360f
2359:
	mov ecx, 8
2361:
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
	jb 2362f
	jmp 2363f
2362:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2364f
	jmp 2365f
2364:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2365:
2363:
	add rsi, 3
	sub rcx, 1
	jne 2361b
2360:
	jmp 2358f
2357:
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
2358:
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
2366:
	cmp rdi, 225
	jb 2367f
	cmp rdi, 241
	jb 2369f
	cmp rdi, 256
	jb 2371f
	add rsi, 24
	jmp 2372f
2371:
	mov ecx, 8
2373:
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
	jb 2374f
	jmp 2375f
2374:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2376f
	jmp 2377f
2376:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2377:
2375:
	add rsi, 3
	sub rcx, 1
	jne 2373b
2372:
	jmp 2370f
2369:
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
2370:
	cmp rdi, 241
	jb 2378f
	cmp rdi, 256
	jb 2380f
	add rsi, 24
	jmp 2381f
2380:
	mov ecx, 8
2382:
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
	jb 2383f
	jmp 2384f
2383:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2385f
	jmp 2386f
2385:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2386:
2384:
	add rsi, 3
	sub rcx, 1
	jne 2382b
2381:
	jmp 2379f
2378:
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
2379:
	jmp 2368f
2367:
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
2368:
	sub r10, 1
	jne 2366b
	cmp rdi, 241
	jb 2387f
	cmp rdi, 256
	jb 2389f
	add rsi, 24
	jmp 2390f
2389:
	mov ecx, 8
2391:
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
	jb 2392f
	jmp 2393f
2392:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2394f
	jmp 2395f
2394:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2395:
2393:
	add rsi, 3
	sub rcx, 1
	jne 2391b
2390:
	jmp 2388f
2387:
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
2388:
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
2396:
	cmp rdi, 225
	jb 2397f
	cmp rdi, 241
	jb 2399f
	cmp rdi, 256
	jb 2401f
	add rsi, 24
	jmp 2402f
2401:
	mov ecx, 8
2403:
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
	jb 2404f
	jmp 2405f
2404:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2406f
	jmp 2407f
2406:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2407:
2405:
	add rsi, 3
	sub rcx, 1
	jne 2403b
2402:
	jmp 2400f
2399:
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
2400:
	cmp rdi, 241
	jb 2408f
	cmp rdi, 256
	jb 2410f
	add rsi, 24
	jmp 2411f
2410:
	mov ecx, 8
2412:
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
	jb 2413f
	jmp 2414f
2413:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2415f
	jmp 2416f
2415:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2416:
2414:
	add rsi, 3
	sub rcx, 1
	jne 2412b
2411:
	jmp 2409f
2408:
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
2409:
	jmp 2398f
2397:
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
2398:
	sub r10, 1
	jne 2396b
	cmp rdi, 241
	jb 2417f
	cmp rdi, 256
	jb 2419f
	add rsi, 24
	jmp 2420f
2419:
	mov ecx, 8
2421:
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
	jb 2422f
	jmp 2423f
2422:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2424f
	jmp 2425f
2424:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2425:
2423:
	add rsi, 3
	sub rcx, 1
	jne 2421b
2420:
	jmp 2418f
2417:
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
2418:
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
	je 2426f
	jmp 2427f
2426:
	mov r14d, 1
	mov rbp, rbx
	add rbp, 2368
	mov r10d, 2
2428:
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
2429:
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
	jne 2429b
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
	jne 2428b
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
2430:
	cmp rdi, 225
	jb 2431f
	cmp rdi, 241
	jb 2433f
	cmp rdi, 256
	jb 2435f
	add rsi, 24
	jmp 2436f
2435:
	mov ecx, 8
2437:
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
	jb 2438f
	jmp 2439f
2438:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2440f
	jmp 2441f
2440:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2441:
2439:
	add rsi, 3
	sub rcx, 1
	jne 2437b
2436:
	jmp 2434f
2433:
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
2434:
	cmp rdi, 241
	jb 2442f
	cmp rdi, 256
	jb 2444f
	add rsi, 24
	jmp 2445f
2444:
	mov ecx, 8
2446:
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
	jb 2447f
	jmp 2448f
2447:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2449f
	jmp 2450f
2449:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2450:
2448:
	add rsi, 3
	sub rcx, 1
	jne 2446b
2445:
	jmp 2443f
2442:
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
2443:
	jmp 2432f
2431:
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
2432:
	sub r10, 1
	jne 2430b
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
2451:
	cmp rdi, 225
	jb 2452f
	cmp rdi, 241
	jb 2454f
	cmp rdi, 256
	jb 2456f
	add rsi, 24
	jmp 2457f
2456:
	mov ecx, 8
2458:
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
	jb 2459f
	jmp 2460f
2459:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2461f
	jmp 2462f
2461:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2462:
2460:
	add rsi, 3
	sub rcx, 1
	jne 2458b
2457:
	jmp 2455f
2454:
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
2455:
	cmp rdi, 241
	jb 2463f
	cmp rdi, 256
	jb 2465f
	add rsi, 24
	jmp 2466f
2465:
	mov ecx, 8
2467:
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
	jb 2468f
	jmp 2469f
2468:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2470f
	jmp 2471f
2470:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2471:
2469:
	add rsi, 3
	sub rcx, 1
	jne 2467b
2466:
	jmp 2464f
2463:
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
2464:
	jmp 2453f
2452:
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
2453:
	sub r10, 1
	jne 2451b
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
2472:
	cmp rdi, 225
	jb 2473f
	cmp rdi, 241
	jb 2475f
	cmp rdi, 256
	jb 2477f
	add rsi, 24
	jmp 2478f
2477:
	mov ecx, 8
2479:
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
	jb 2480f
	jmp 2481f
2480:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2482f
	jmp 2483f
2482:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2483:
2481:
	add rsi, 3
	sub rcx, 1
	jne 2479b
2478:
	jmp 2476f
2475:
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
2476:
	cmp rdi, 241
	jb 2484f
	cmp rdi, 256
	jb 2486f
	add rsi, 24
	jmp 2487f
2486:
	mov ecx, 8
2488:
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
	jb 2489f
	jmp 2490f
2489:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2491f
	jmp 2492f
2491:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2492:
2490:
	add rsi, 3
	sub rcx, 1
	jne 2488b
2487:
	jmp 2485f
2484:
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
2485:
	jmp 2474f
2473:
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
2474:
	sub r10, 1
	jne 2472b
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
2427:
	vzeroupper
	mov eax, r14d
	mov r14, QWORD PTR [rbx+4416]
	mov r13, QWORD PTR [rbx+4408]
	mov r12, QWORD PTR [rbx+4400]
	mov rbp, QWORD PTR [rbx+4392]
	mov rbx, QWORD PTR [rbx+4384]
	and r15d, eax
	mov rdi, rbx
	add rdi, 23816
	mov rsi, r14
	add rsi, 1224
	mov ecx, 43
2493:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2493b
	mov eax, 0
	mov QWORD PTR [rbx+24160], rax
	mov QWORD PTR [rbx+24168], rax
	mov QWORD PTR [rbx+24176], rax
	mov QWORD PTR [rbx+24184], rax
	mov QWORD PTR [rbx+24192], rax
	mov QWORD PTR [rbx+24200], rax
	mov QWORD PTR [rbx+24208], rax
	mov QWORD PTR [rbx+24216], rax
	mov eax, 6
	mov BYTE PTR [rbx+24160], al
	mov eax, 128
	mov BYTE PTR [rbx+24223], al
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
2494:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2494b
	mov eax, 1
	mov BYTE PTR [rbx+32], al
	mov eax, 2
	mov BYTE PTR [rbx+33], al
	mov rdi, rbx
	add rdi, 34
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
2495:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2495b
	mov eax, 2
	mov BYTE PTR [rbx+66], al
	mov eax, 2
	mov BYTE PTR [rbx+67], al
	mov rdi, rbx
	add rdi, 68
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
2496:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2496b
	mov eax, 3
	mov BYTE PTR [rbx+100], al
	mov eax, 2
	mov BYTE PTR [rbx+101], al
	mov rdi, rbx
	add rdi, 102
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
2497:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2497b
	mov eax, 0
	mov BYTE PTR [rbx+134], al
	mov eax, 3
	mov BYTE PTR [rbx+135], al
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbx
	add rsi, 8704
	mov rdx, rbx
	add rdx, 16896
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
2498:
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
2499:
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
	jne 2499b
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
	jne 2498b
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
2500:
	cmp rdi, 225
	jb 2501f
	cmp rdi, 241
	jb 2503f
	cmp rdi, 256
	jb 2505f
	add rsi, 24
	jmp 2506f
2505:
	mov ecx, 8
2507:
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
	jb 2508f
	jmp 2509f
2508:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2510f
	jmp 2511f
2510:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2511:
2509:
	add rsi, 3
	sub rcx, 1
	jne 2507b
2506:
	jmp 2504f
2503:
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
2504:
	cmp rdi, 241
	jb 2512f
	cmp rdi, 256
	jb 2514f
	add rsi, 24
	jmp 2515f
2514:
	mov ecx, 8
2516:
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
	jb 2517f
	jmp 2518f
2517:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2519f
	jmp 2520f
2519:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2520:
2518:
	add rsi, 3
	sub rcx, 1
	jne 2516b
2515:
	jmp 2513f
2512:
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
2513:
	jmp 2502f
2501:
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
2502:
	sub r10, 1
	jne 2500b
	cmp rdi, 241
	jb 2521f
	cmp rdi, 256
	jb 2523f
	add rsi, 24
	jmp 2524f
2523:
	mov ecx, 8
2525:
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
	jb 2526f
	jmp 2527f
2526:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2528f
	jmp 2529f
2528:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2529:
2527:
	add rsi, 3
	sub rcx, 1
	jne 2525b
2524:
	jmp 2522f
2521:
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
2522:
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
2530:
	cmp rdi, 225
	jb 2531f
	cmp rdi, 241
	jb 2533f
	cmp rdi, 256
	jb 2535f
	add rsi, 24
	jmp 2536f
2535:
	mov ecx, 8
2537:
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
	jb 2538f
	jmp 2539f
2538:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2540f
	jmp 2541f
2540:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2541:
2539:
	add rsi, 3
	sub rcx, 1
	jne 2537b
2536:
	jmp 2534f
2533:
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
2534:
	cmp rdi, 241
	jb 2542f
	cmp rdi, 256
	jb 2544f
	add rsi, 24
	jmp 2545f
2544:
	mov ecx, 8
2546:
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
	jb 2547f
	jmp 2548f
2547:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2549f
	jmp 2550f
2549:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2550:
2548:
	add rsi, 3
	sub rcx, 1
	jne 2546b
2545:
	jmp 2543f
2542:
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
2543:
	jmp 2532f
2531:
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
2532:
	sub r10, 1
	jne 2530b
	cmp rdi, 241
	jb 2551f
	cmp rdi, 256
	jb 2553f
	add rsi, 24
	jmp 2554f
2553:
	mov ecx, 8
2555:
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
	jb 2556f
	jmp 2557f
2556:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2558f
	jmp 2559f
2558:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2559:
2557:
	add rsi, 3
	sub rcx, 1
	jne 2555b
2554:
	jmp 2552f
2551:
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
2552:
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
2560:
	cmp rdi, 225
	jb 2561f
	cmp rdi, 241
	jb 2563f
	cmp rdi, 256
	jb 2565f
	add rsi, 24
	jmp 2566f
2565:
	mov ecx, 8
2567:
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
	jb 2568f
	jmp 2569f
2568:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2570f
	jmp 2571f
2570:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2571:
2569:
	add rsi, 3
	sub rcx, 1
	jne 2567b
2566:
	jmp 2564f
2563:
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
2564:
	cmp rdi, 241
	jb 2572f
	cmp rdi, 256
	jb 2574f
	add rsi, 24
	jmp 2575f
2574:
	mov ecx, 8
2576:
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
	jb 2577f
	jmp 2578f
2577:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2579f
	jmp 2580f
2579:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2580:
2578:
	add rsi, 3
	sub rcx, 1
	jne 2576b
2575:
	jmp 2573f
2572:
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
2573:
	jmp 2562f
2561:
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
2562:
	sub r10, 1
	jne 2560b
	cmp rdi, 241
	jb 2581f
	cmp rdi, 256
	jb 2583f
	add rsi, 24
	jmp 2584f
2583:
	mov ecx, 8
2585:
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
	jb 2586f
	jmp 2587f
2586:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2588f
	jmp 2589f
2588:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2589:
2587:
	add rsi, 3
	sub rcx, 1
	jne 2585b
2584:
	jmp 2582f
2581:
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
2582:
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
	je 2590f
	jmp 2591f
2590:
	mov r14d, 1
	mov rbp, rbx
	add rbp, 2368
	mov r10d, 2
2592:
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
2593:
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
	jne 2593b
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
	jne 2592b
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
2594:
	cmp rdi, 225
	jb 2595f
	cmp rdi, 241
	jb 2597f
	cmp rdi, 256
	jb 2599f
	add rsi, 24
	jmp 2600f
2599:
	mov ecx, 8
2601:
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
	jb 2602f
	jmp 2603f
2602:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2604f
	jmp 2605f
2604:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2605:
2603:
	add rsi, 3
	sub rcx, 1
	jne 2601b
2600:
	jmp 2598f
2597:
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
2598:
	cmp rdi, 241
	jb 2606f
	cmp rdi, 256
	jb 2608f
	add rsi, 24
	jmp 2609f
2608:
	mov ecx, 8
2610:
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
	jb 2611f
	jmp 2612f
2611:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2613f
	jmp 2614f
2613:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2614:
2612:
	add rsi, 3
	sub rcx, 1
	jne 2610b
2609:
	jmp 2607f
2606:
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
2607:
	jmp 2596f
2595:
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
2596:
	sub r10, 1
	jne 2594b
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
2615:
	cmp rdi, 225
	jb 2616f
	cmp rdi, 241
	jb 2618f
	cmp rdi, 256
	jb 2620f
	add rsi, 24
	jmp 2621f
2620:
	mov ecx, 8
2622:
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
	jb 2623f
	jmp 2624f
2623:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2625f
	jmp 2626f
2625:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2626:
2624:
	add rsi, 3
	sub rcx, 1
	jne 2622b
2621:
	jmp 2619f
2618:
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
2619:
	cmp rdi, 241
	jb 2627f
	cmp rdi, 256
	jb 2629f
	add rsi, 24
	jmp 2630f
2629:
	mov ecx, 8
2631:
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
	jb 2632f
	jmp 2633f
2632:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2634f
	jmp 2635f
2634:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2635:
2633:
	add rsi, 3
	sub rcx, 1
	jne 2631b
2630:
	jmp 2628f
2627:
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
2628:
	jmp 2617f
2616:
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
2617:
	sub r10, 1
	jne 2615b
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
2636:
	cmp rdi, 225
	jb 2637f
	cmp rdi, 241
	jb 2639f
	cmp rdi, 256
	jb 2641f
	add rsi, 24
	jmp 2642f
2641:
	mov ecx, 8
2643:
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
	jb 2644f
	jmp 2645f
2644:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2646f
	jmp 2647f
2646:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2647:
2645:
	add rsi, 3
	sub rcx, 1
	jne 2643b
2642:
	jmp 2640f
2639:
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
2640:
	cmp rdi, 241
	jb 2648f
	cmp rdi, 256
	jb 2650f
	add rsi, 24
	jmp 2651f
2650:
	mov ecx, 8
2652:
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
	jb 2653f
	jmp 2654f
2653:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2655f
	jmp 2656f
2655:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2656:
2654:
	add rsi, 3
	sub rcx, 1
	jne 2652b
2651:
	jmp 2649f
2648:
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
2649:
	jmp 2638f
2637:
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
2638:
	sub r10, 1
	jne 2636b
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
2591:
	vzeroupper
	mov eax, r14d
	mov r14, QWORD PTR [rbx+4416]
	mov r13, QWORD PTR [rbx+4408]
	mov r12, QWORD PTR [rbx+4400]
	mov rbp, QWORD PTR [rbx+4392]
	mov rbx, QWORD PTR [rbx+4384]
	and r15d, eax
	mov rdi, rbx
	add rdi, 1088
	mov rsi, rbx
	add rsi, 23616
	mov ecx, 4
2657:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2657b
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
2658:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2658b
	mov eax, 0
	mov BYTE PTR [rbx+32], al
	mov eax, 3
	mov BYTE PTR [rbx+33], al
	mov rdi, rbx
	add rdi, 34
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
2659:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2659b
	mov eax, 1
	mov BYTE PTR [rbx+66], al
	mov eax, 3
	mov BYTE PTR [rbx+67], al
	mov rdi, rbx
	add rdi, 68
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
2660:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2660b
	mov eax, 2
	mov BYTE PTR [rbx+100], al
	mov eax, 3
	mov BYTE PTR [rbx+101], al
	mov rdi, rbx
	add rdi, 102
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
2661:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2661b
	mov eax, 3
	mov BYTE PTR [rbx+134], al
	mov eax, 3
	mov BYTE PTR [rbx+135], al
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbx
	add rsi, 10240
	mov rdx, rbx
	add rdx, 16896
	call {vg_mlkem16_sample_ntt4_avx512}
	and r15d, eax
	mov rdi, rbx
	add rdi, 1248
	mov rsi, rbp
	add rsi, 0
	mov ecx, 4
2662:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2662b
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
	test r15d, r15d
	jne 2663f
	jmp 2664f
2663:
	mov eax, 0
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
	mov esi, 136
	mov edx, 0
	mov rcx, rbx
	add rcx, 1056
	mov r8d, 32
	mov r9, rbx
	add r9, 200
	call {vg_keccak_absorb_scratch}
	mov rdi, rbx
	add rdi, 0
	mov esi, 136
	mov edx, 32
	mov rcx, rbx
	add rcx, 896
	mov r8d, 1
	mov r9, rbx
	add r9, 200
	call {vg_keccak_absorb_scratch}
	mov rdi, rbx
	add rdi, 0
	mov esi, 136
	mov edx, 33
	mov ecx, 31
	mov r8, rbx
	add r8, 200
	call {vg_keccak_pad_scratch}
	mov rdi, rbx
	add rdi, 0
	mov esi, 136
	mov edx, 0
	mov rcx, rbx
	add rcx, 25088
	mov r8d, 128
	mov r9, rbx
	add r9, 200
	call {vg_keccak_squeeze_scratch}
	mov r8, rbx
	add r8, 25216
	mov r9d, 1
	mov r10d, 2
2665:
	movabs rax, 1
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+18496], ymm0
	movabs rax, 32898
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+18528], ymm0
	movabs rax, -9223372036854742902
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+18560], ymm0
	movabs rax, -9223372034707259392
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+18592], ymm0
	movabs rax, 32907
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+18624], ymm0
	movabs rax, 2147483649
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+18656], ymm0
	movabs rax, -9223372034707259263
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+18688], ymm0
	movabs rax, -9223372036854743031
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+18720], ymm0
	movabs rax, 138
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+18752], ymm0
	movabs rax, 136
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+18784], ymm0
	movabs rax, 2147516425
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+18816], ymm0
	movabs rax, 2147483658
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+18848], ymm0
	movabs rax, 2147516555
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+18880], ymm0
	movabs rax, -9223372036854775669
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+18912], ymm0
	movabs rax, -9223372036854742903
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+18944], ymm0
	movabs rax, -9223372036854743037
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+18976], ymm0
	movabs rax, -9223372036854743038
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+19008], ymm0
	movabs rax, -9223372036854775680
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+19040], ymm0
	movabs rax, 32778
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+19072], ymm0
	movabs rax, -9223372034707292150
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+19104], ymm0
	movabs rax, -9223372034707259263
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+19136], ymm0
	movabs rax, -9223372036854742912
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+19168], ymm0
	movabs rax, 2147483649
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+19200], ymm0
	movabs rax, -9223372034707259384
	vmovq xmm0, rax
	vpbroadcastq ymm0, xmm0
	vmovdqu YMMWORD PTR [rbx+19232], ymm0
	vpxor ymm0, ymm0, ymm0
	vmovdqu YMMWORD PTR [rbx+16896], ymm0
	vmovdqu YMMWORD PTR [rbx+16928], ymm0
	vmovdqu YMMWORD PTR [rbx+16960], ymm0
	vmovdqu YMMWORD PTR [rbx+16992], ymm0
	vmovdqu YMMWORD PTR [rbx+17024], ymm0
	vmovdqu YMMWORD PTR [rbx+17056], ymm0
	vmovdqu YMMWORD PTR [rbx+17088], ymm0
	vmovdqu YMMWORD PTR [rbx+17120], ymm0
	vmovdqu YMMWORD PTR [rbx+17152], ymm0
	vmovdqu YMMWORD PTR [rbx+17184], ymm0
	vmovdqu YMMWORD PTR [rbx+17216], ymm0
	vmovdqu YMMWORD PTR [rbx+17248], ymm0
	vmovdqu YMMWORD PTR [rbx+17280], ymm0
	vmovdqu YMMWORD PTR [rbx+17312], ymm0
	vmovdqu YMMWORD PTR [rbx+17344], ymm0
	vmovdqu YMMWORD PTR [rbx+17376], ymm0
	vmovdqu YMMWORD PTR [rbx+17408], ymm0
	vmovdqu YMMWORD PTR [rbx+17440], ymm0
	vmovdqu YMMWORD PTR [rbx+17472], ymm0
	vmovdqu YMMWORD PTR [rbx+17504], ymm0
	vmovdqu YMMWORD PTR [rbx+17536], ymm0
	vmovdqu YMMWORD PTR [rbx+17568], ymm0
	vmovdqu YMMWORD PTR [rbx+17600], ymm0
	vmovdqu YMMWORD PTR [rbx+17632], ymm0
	vmovdqu YMMWORD PTR [rbx+17664], ymm0
	mov rax, QWORD PTR [rbx+1056]
	mov QWORD PTR [rbx+16896], rax
	mov QWORD PTR [rbx+16904], rax
	mov QWORD PTR [rbx+16912], rax
	mov QWORD PTR [rbx+16920], rax
	mov rax, QWORD PTR [rbx+1064]
	mov QWORD PTR [rbx+16928], rax
	mov QWORD PTR [rbx+16936], rax
	mov QWORD PTR [rbx+16944], rax
	mov QWORD PTR [rbx+16952], rax
	mov rax, QWORD PTR [rbx+1072]
	mov QWORD PTR [rbx+16960], rax
	mov QWORD PTR [rbx+16968], rax
	mov QWORD PTR [rbx+16976], rax
	mov QWORD PTR [rbx+16984], rax
	mov rax, QWORD PTR [rbx+1080]
	mov QWORD PTR [rbx+16992], rax
	mov QWORD PTR [rbx+17000], rax
	mov QWORD PTR [rbx+17008], rax
	mov QWORD PTR [rbx+17016], rax
	mov rax, r9
	mov BYTE PTR [rbx+17024], al
	add rax, 1
	mov BYTE PTR [rbx+17032], al
	add rax, 1
	mov BYTE PTR [rbx+17040], al
	add rax, 1
	mov BYTE PTR [rbx+17048], al
	add rax, 1
	mov eax, 31
	mov BYTE PTR [rbx+17025], al
	mov BYTE PTR [rbx+17033], al
	mov BYTE PTR [rbx+17041], al
	mov BYTE PTR [rbx+17049], al
	mov eax, 128
	mov BYTE PTR [rbx+17415], al
	mov BYTE PTR [rbx+17423], al
	mov BYTE PTR [rbx+17431], al
	mov BYTE PTR [rbx+17439], al
	mov rdi, rbx
	add rdi, 16896
	mov rsi, rbx
	add rsi, 17696
	mov rdx, rbx
	add rdx, 18496
	mov rcx, rbx
	add rcx, 19264
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
2666:
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
	jne 2666b
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
	mov rax, QWORD PTR [rbx+16896]
	mov QWORD PTR [r8], rax
	mov rax, QWORD PTR [rbx+16928]
	mov QWORD PTR [r8+8], rax
	mov rax, QWORD PTR [rbx+16960]
	mov QWORD PTR [r8+16], rax
	mov rax, QWORD PTR [rbx+16992]
	mov QWORD PTR [r8+24], rax
	mov rax, QWORD PTR [rbx+17024]
	mov QWORD PTR [r8+32], rax
	mov rax, QWORD PTR [rbx+17056]
	mov QWORD PTR [r8+40], rax
	mov rax, QWORD PTR [rbx+17088]
	mov QWORD PTR [r8+48], rax
	mov rax, QWORD PTR [rbx+17120]
	mov QWORD PTR [r8+56], rax
	mov rax, QWORD PTR [rbx+17152]
	mov QWORD PTR [r8+64], rax
	mov rax, QWORD PTR [rbx+17184]
	mov QWORD PTR [r8+72], rax
	mov rax, QWORD PTR [rbx+17216]
	mov QWORD PTR [r8+80], rax
	mov rax, QWORD PTR [rbx+17248]
	mov QWORD PTR [r8+88], rax
	mov rax, QWORD PTR [rbx+17280]
	mov QWORD PTR [r8+96], rax
	mov rax, QWORD PTR [rbx+17312]
	mov QWORD PTR [r8+104], rax
	mov rax, QWORD PTR [rbx+17344]
	mov QWORD PTR [r8+112], rax
	mov rax, QWORD PTR [rbx+17376]
	mov QWORD PTR [r8+120], rax
	mov rax, QWORD PTR [rbx+16904]
	mov QWORD PTR [r8+128], rax
	mov rax, QWORD PTR [rbx+16936]
	mov QWORD PTR [r8+136], rax
	mov rax, QWORD PTR [rbx+16968]
	mov QWORD PTR [r8+144], rax
	mov rax, QWORD PTR [rbx+17000]
	mov QWORD PTR [r8+152], rax
	mov rax, QWORD PTR [rbx+17032]
	mov QWORD PTR [r8+160], rax
	mov rax, QWORD PTR [rbx+17064]
	mov QWORD PTR [r8+168], rax
	mov rax, QWORD PTR [rbx+17096]
	mov QWORD PTR [r8+176], rax
	mov rax, QWORD PTR [rbx+17128]
	mov QWORD PTR [r8+184], rax
	mov rax, QWORD PTR [rbx+17160]
	mov QWORD PTR [r8+192], rax
	mov rax, QWORD PTR [rbx+17192]
	mov QWORD PTR [r8+200], rax
	mov rax, QWORD PTR [rbx+17224]
	mov QWORD PTR [r8+208], rax
	mov rax, QWORD PTR [rbx+17256]
	mov QWORD PTR [r8+216], rax
	mov rax, QWORD PTR [rbx+17288]
	mov QWORD PTR [r8+224], rax
	mov rax, QWORD PTR [rbx+17320]
	mov QWORD PTR [r8+232], rax
	mov rax, QWORD PTR [rbx+17352]
	mov QWORD PTR [r8+240], rax
	mov rax, QWORD PTR [rbx+17384]
	mov QWORD PTR [r8+248], rax
	mov rax, QWORD PTR [rbx+16912]
	mov QWORD PTR [r8+256], rax
	mov rax, QWORD PTR [rbx+16944]
	mov QWORD PTR [r8+264], rax
	mov rax, QWORD PTR [rbx+16976]
	mov QWORD PTR [r8+272], rax
	mov rax, QWORD PTR [rbx+17008]
	mov QWORD PTR [r8+280], rax
	mov rax, QWORD PTR [rbx+17040]
	mov QWORD PTR [r8+288], rax
	mov rax, QWORD PTR [rbx+17072]
	mov QWORD PTR [r8+296], rax
	mov rax, QWORD PTR [rbx+17104]
	mov QWORD PTR [r8+304], rax
	mov rax, QWORD PTR [rbx+17136]
	mov QWORD PTR [r8+312], rax
	mov rax, QWORD PTR [rbx+17168]
	mov QWORD PTR [r8+320], rax
	mov rax, QWORD PTR [rbx+17200]
	mov QWORD PTR [r8+328], rax
	mov rax, QWORD PTR [rbx+17232]
	mov QWORD PTR [r8+336], rax
	mov rax, QWORD PTR [rbx+17264]
	mov QWORD PTR [r8+344], rax
	mov rax, QWORD PTR [rbx+17296]
	mov QWORD PTR [r8+352], rax
	mov rax, QWORD PTR [rbx+17328]
	mov QWORD PTR [r8+360], rax
	mov rax, QWORD PTR [rbx+17360]
	mov QWORD PTR [r8+368], rax
	mov rax, QWORD PTR [rbx+17392]
	mov QWORD PTR [r8+376], rax
	mov rax, QWORD PTR [rbx+16920]
	mov QWORD PTR [r8+384], rax
	mov rax, QWORD PTR [rbx+16952]
	mov QWORD PTR [r8+392], rax
	mov rax, QWORD PTR [rbx+16984]
	mov QWORD PTR [r8+400], rax
	mov rax, QWORD PTR [rbx+17016]
	mov QWORD PTR [r8+408], rax
	mov rax, QWORD PTR [rbx+17048]
	mov QWORD PTR [r8+416], rax
	mov rax, QWORD PTR [rbx+17080]
	mov QWORD PTR [r8+424], rax
	mov rax, QWORD PTR [rbx+17112]
	mov QWORD PTR [r8+432], rax
	mov rax, QWORD PTR [rbx+17144]
	mov QWORD PTR [r8+440], rax
	mov rax, QWORD PTR [rbx+17176]
	mov QWORD PTR [r8+448], rax
	mov rax, QWORD PTR [rbx+17208]
	mov QWORD PTR [r8+456], rax
	mov rax, QWORD PTR [rbx+17240]
	mov QWORD PTR [r8+464], rax
	mov rax, QWORD PTR [rbx+17272]
	mov QWORD PTR [r8+472], rax
	mov rax, QWORD PTR [rbx+17304]
	mov QWORD PTR [r8+480], rax
	mov rax, QWORD PTR [rbx+17336]
	mov QWORD PTR [r8+488], rax
	mov rax, QWORD PTR [rbx+17368]
	mov QWORD PTR [r8+496], rax
	mov rax, QWORD PTR [rbx+17400]
	mov QWORD PTR [r8+504], rax
	vzeroupper
	add r8, 512
	add r9, 4
	sub r10, 1
	jne 2665b
	mov rdi, rbx
	add rdi, 25088
	mov rsi, rbx
	add rsi, 12288
	call {vg_mlkem16_cbd2_avx2}
	mov rdi, rbx
	add rdi, 25216
	mov rsi, rbx
	add rsi, 12800
	call {vg_mlkem16_cbd2_avx2}
	mov rdi, rbx
	add rdi, 25344
	mov rsi, rbx
	add rsi, 13312
	call {vg_mlkem16_cbd2_avx2}
	mov rdi, rbx
	add rdi, 25472
	mov rsi, rbx
	add rsi, 13824
	call {vg_mlkem16_cbd2_avx2}
	mov rdi, rbx
	add rdi, 25600
	mov rsi, rbx
	add rsi, 14336
	call {vg_mlkem16_cbd2_avx2}
	mov rdi, rbx
	add rdi, 25728
	mov rsi, rbx
	add rsi, 14848
	call {vg_mlkem16_cbd2_avx2}
	mov rdi, rbx
	add rdi, 25856
	mov rsi, rbx
	add rsi, 15360
	call {vg_mlkem16_cbd2_avx2}
	mov rdi, rbx
	add rdi, 25984
	mov rsi, rbx
	add rsi, 15872
	call {vg_mlkem16_cbd2_avx2}
	mov rdi, rbx
	add rdi, 26112
	mov rsi, rbx
	add rsi, 16384
	call {vg_mlkem16_cbd2_avx2}
	mov rdi, r13
	add rdi, 0
	mov rsi, rbx
	add rsi, 4096
	mov rdx, r14
	add rdx, 0
	mov rcx, rbx
	add rcx, 12288
	mov r8, rbx
	add r8, 1248
	mov r9, rbx
	add r9, 16896
	call {vg_mlkem1024_kpke_encrypt}
2664:
	mov rdi, r12
	add rdi, 0
	mov rsi, rbx
	add rsi, 1024
	mov ecx, 4
2667:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2667b
	mov eax, r15d
	mov r15, QWORD PTR [rbx+880]
	mov r14, QWORD PTR [rbx+872]
	mov r13, QWORD PTR [rbx+864]
	mov r12, QWORD PTR [rbx+856]
	mov rbp, QWORD PTR [rbx+848]
	mov rbx, QWORD PTR [rbx+840]
	ret
	.p2align 6
