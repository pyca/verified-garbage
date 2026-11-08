// The functions of `src/internal/vg_mlkem768_encaps_body_avx2.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem768_encaps_body_avx2:
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
	add rsi, 1152
	mov ecx, 4
20:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 20b
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
	add rdi, 19208
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
	vmovdqu ymm11, YMMWORD PTR [rdi]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+160]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+320]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+480]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+640]
	vmovdqu ymm12, YMMWORD PTR [rdi+32]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+192]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+352]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+512]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+672]
	vmovdqu ymm13, YMMWORD PTR [rdi+64]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+224]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+384]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+544]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+704]
	vmovdqu ymm14, YMMWORD PTR [rdi+96]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+256]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+416]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+576]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+736]
	vmovdqu ymm15, YMMWORD PTR [rdi+128]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+288]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+448]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+608]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+768]
27:
	vpsllq ymm10, ymm12, 1
	vpsrlq ymm5, ymm12, 63
	vpor ymm5, ymm5, ymm10
	vpxor ymm5, ymm5, ymm15
	vpsllq ymm10, ymm13, 1
	vpsrlq ymm6, ymm13, 63
	vpor ymm6, ymm6, ymm10
	vpxor ymm6, ymm6, ymm11
	vpsllq ymm10, ymm14, 1
	vpsrlq ymm7, ymm14, 63
	vpor ymm7, ymm7, ymm10
	vpxor ymm7, ymm7, ymm12
	vpsllq ymm10, ymm15, 1
	vpsrlq ymm8, ymm15, 63
	vpor ymm8, ymm8, ymm10
	vpxor ymm8, ymm8, ymm13
	vpsllq ymm10, ymm11, 1
	vpsrlq ymm9, ymm11, 63
	vpor ymm9, ymm9, ymm10
	vpxor ymm9, ymm9, ymm14
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpxor ymm0, ymm0, ymm5
	vmovdqu ymm1, YMMWORD PTR [rdi+192]
	vpxor ymm1, ymm1, ymm6
	vpsllq ymm10, ymm1, 44
	vpsrlq ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+384]
	vpxor ymm2, ymm2, ymm7
	vpsllq ymm10, ymm2, 43
	vpsrlq ymm2, ymm2, 21
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+576]
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm10, ymm3, 21
	vpsrlq ymm3, ymm3, 43
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+768]
	vpxor ymm4, ymm4, ymm9
	vpsllq ymm10, ymm4, 14
	vpsrlq ymm4, ymm4, 50
	vpor ymm4, ymm4, ymm10
	vpandn ymm11, ymm1, ymm2
	vpxor ymm11, ymm11, ymm0
	vpxor ymm11, ymm11, YMMWORD PTR [rdx]
	vmovdqu YMMWORD PTR [rsi], ymm11
	vpandn ymm12, ymm2, ymm3
	vpxor ymm12, ymm12, ymm1
	vmovdqu YMMWORD PTR [rsi+32], ymm12
	vpandn ymm13, ymm3, ymm4
	vpxor ymm13, ymm13, ymm2
	vmovdqu YMMWORD PTR [rsi+64], ymm13
	vpandn ymm14, ymm4, ymm0
	vpxor ymm14, ymm14, ymm3
	vmovdqu YMMWORD PTR [rsi+96], ymm14
	vpandn ymm15, ymm0, ymm1
	vpxor ymm15, ymm15, ymm4
	vmovdqu YMMWORD PTR [rsi+128], ymm15
	vmovdqu ymm0, YMMWORD PTR [rdi+96]
	vpxor ymm0, ymm0, ymm8
	vpsllq ymm10, ymm0, 28
	vpsrlq ymm0, ymm0, 36
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+288]
	vpxor ymm1, ymm1, ymm9
	vpsllq ymm10, ymm1, 20
	vpsrlq ymm1, ymm1, 44
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+320]
	vpxor ymm2, ymm2, ymm5
	vpsllq ymm10, ymm2, 3
	vpsrlq ymm2, ymm2, 61
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+512]
	vpxor ymm3, ymm3, ymm6
	vpsllq ymm10, ymm3, 45
	vpsrlq ymm3, ymm3, 19
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+704]
	vpxor ymm4, ymm4, ymm7
	vpsllq ymm10, ymm4, 61
	vpsrlq ymm4, ymm4, 3
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+160], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+192], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+224], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+256], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+288], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+32]
	vpxor ymm0, ymm0, ymm6
	vpsllq ymm10, ymm0, 1
	vpsrlq ymm0, ymm0, 63
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+224]
	vpxor ymm1, ymm1, ymm7
	vpsllq ymm10, ymm1, 6
	vpsrlq ymm1, ymm1, 58
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+416]
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm10, ymm2, 25
	vpsrlq ymm2, ymm2, 39
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+608]
	vpxor ymm3, ymm3, ymm9
	vpsllq ymm10, ymm3, 8
	vpsrlq ymm3, ymm3, 56
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+640]
	vpxor ymm4, ymm4, ymm5
	vpsllq ymm10, ymm4, 18
	vpsrlq ymm4, ymm4, 46
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+320], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+352], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+384], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+416], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+448], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+128]
	vpxor ymm0, ymm0, ymm9
	vpsllq ymm10, ymm0, 27
	vpsrlq ymm0, ymm0, 37
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+160]
	vpxor ymm1, ymm1, ymm5
	vpsllq ymm10, ymm1, 36
	vpsrlq ymm1, ymm1, 28
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+352]
	vpxor ymm2, ymm2, ymm6
	vpsllq ymm10, ymm2, 10
	vpsrlq ymm2, ymm2, 54
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+544]
	vpxor ymm3, ymm3, ymm7
	vpsllq ymm10, ymm3, 15
	vpsrlq ymm3, ymm3, 49
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+736]
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm10, ymm4, 56
	vpsrlq ymm4, ymm4, 8
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+480], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+512], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+544], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+576], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+608], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+64]
	vpxor ymm0, ymm0, ymm7
	vpsllq ymm10, ymm0, 62
	vpsrlq ymm0, ymm0, 2
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+256]
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm10, ymm1, 55
	vpsrlq ymm1, ymm1, 9
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+448]
	vpxor ymm2, ymm2, ymm9
	vpsllq ymm10, ymm2, 39
	vpsrlq ymm2, ymm2, 25
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+480]
	vpxor ymm3, ymm3, ymm5
	vpsllq ymm10, ymm3, 41
	vpsrlq ymm3, ymm3, 23
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+672]
	vpxor ymm4, ymm4, ymm6
	vpsllq ymm10, ymm4, 2
	vpsrlq ymm4, ymm4, 62
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+640], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+672], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+704], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+736], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+768], ymm10
	vpxor ymm15, ymm15, ymm10
	mov rax, rdi
	mov rdi, rsi
	mov rsi, rax
	add rdx, 32
	cmp rdx, rcx
	vpsllq ymm10, ymm12, 1
	vpsrlq ymm5, ymm12, 63
	vpor ymm5, ymm5, ymm10
	vpxor ymm5, ymm5, ymm15
	vpsllq ymm10, ymm13, 1
	vpsrlq ymm6, ymm13, 63
	vpor ymm6, ymm6, ymm10
	vpxor ymm6, ymm6, ymm11
	vpsllq ymm10, ymm14, 1
	vpsrlq ymm7, ymm14, 63
	vpor ymm7, ymm7, ymm10
	vpxor ymm7, ymm7, ymm12
	vpsllq ymm10, ymm15, 1
	vpsrlq ymm8, ymm15, 63
	vpor ymm8, ymm8, ymm10
	vpxor ymm8, ymm8, ymm13
	vpsllq ymm10, ymm11, 1
	vpsrlq ymm9, ymm11, 63
	vpor ymm9, ymm9, ymm10
	vpxor ymm9, ymm9, ymm14
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpxor ymm0, ymm0, ymm5
	vmovdqu ymm1, YMMWORD PTR [rdi+192]
	vpxor ymm1, ymm1, ymm6
	vpsllq ymm10, ymm1, 44
	vpsrlq ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+384]
	vpxor ymm2, ymm2, ymm7
	vpsllq ymm10, ymm2, 43
	vpsrlq ymm2, ymm2, 21
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+576]
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm10, ymm3, 21
	vpsrlq ymm3, ymm3, 43
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+768]
	vpxor ymm4, ymm4, ymm9
	vpsllq ymm10, ymm4, 14
	vpsrlq ymm4, ymm4, 50
	vpor ymm4, ymm4, ymm10
	vpandn ymm11, ymm1, ymm2
	vpxor ymm11, ymm11, ymm0
	vpxor ymm11, ymm11, YMMWORD PTR [rdx]
	vmovdqu YMMWORD PTR [rsi], ymm11
	vpandn ymm12, ymm2, ymm3
	vpxor ymm12, ymm12, ymm1
	vmovdqu YMMWORD PTR [rsi+32], ymm12
	vpandn ymm13, ymm3, ymm4
	vpxor ymm13, ymm13, ymm2
	vmovdqu YMMWORD PTR [rsi+64], ymm13
	vpandn ymm14, ymm4, ymm0
	vpxor ymm14, ymm14, ymm3
	vmovdqu YMMWORD PTR [rsi+96], ymm14
	vpandn ymm15, ymm0, ymm1
	vpxor ymm15, ymm15, ymm4
	vmovdqu YMMWORD PTR [rsi+128], ymm15
	vmovdqu ymm0, YMMWORD PTR [rdi+96]
	vpxor ymm0, ymm0, ymm8
	vpsllq ymm10, ymm0, 28
	vpsrlq ymm0, ymm0, 36
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+288]
	vpxor ymm1, ymm1, ymm9
	vpsllq ymm10, ymm1, 20
	vpsrlq ymm1, ymm1, 44
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+320]
	vpxor ymm2, ymm2, ymm5
	vpsllq ymm10, ymm2, 3
	vpsrlq ymm2, ymm2, 61
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+512]
	vpxor ymm3, ymm3, ymm6
	vpsllq ymm10, ymm3, 45
	vpsrlq ymm3, ymm3, 19
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+704]
	vpxor ymm4, ymm4, ymm7
	vpsllq ymm10, ymm4, 61
	vpsrlq ymm4, ymm4, 3
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+160], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+192], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+224], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+256], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+288], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+32]
	vpxor ymm0, ymm0, ymm6
	vpsllq ymm10, ymm0, 1
	vpsrlq ymm0, ymm0, 63
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+224]
	vpxor ymm1, ymm1, ymm7
	vpsllq ymm10, ymm1, 6
	vpsrlq ymm1, ymm1, 58
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+416]
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm10, ymm2, 25
	vpsrlq ymm2, ymm2, 39
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+608]
	vpxor ymm3, ymm3, ymm9
	vpsllq ymm10, ymm3, 8
	vpsrlq ymm3, ymm3, 56
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+640]
	vpxor ymm4, ymm4, ymm5
	vpsllq ymm10, ymm4, 18
	vpsrlq ymm4, ymm4, 46
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+320], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+352], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+384], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+416], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+448], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+128]
	vpxor ymm0, ymm0, ymm9
	vpsllq ymm10, ymm0, 27
	vpsrlq ymm0, ymm0, 37
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+160]
	vpxor ymm1, ymm1, ymm5
	vpsllq ymm10, ymm1, 36
	vpsrlq ymm1, ymm1, 28
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+352]
	vpxor ymm2, ymm2, ymm6
	vpsllq ymm10, ymm2, 10
	vpsrlq ymm2, ymm2, 54
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+544]
	vpxor ymm3, ymm3, ymm7
	vpsllq ymm10, ymm3, 15
	vpsrlq ymm3, ymm3, 49
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+736]
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm10, ymm4, 56
	vpsrlq ymm4, ymm4, 8
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+480], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+512], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+544], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+576], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+608], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+64]
	vpxor ymm0, ymm0, ymm7
	vpsllq ymm10, ymm0, 62
	vpsrlq ymm0, ymm0, 2
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+256]
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm10, ymm1, 55
	vpsrlq ymm1, ymm1, 9
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+448]
	vpxor ymm2, ymm2, ymm9
	vpsllq ymm10, ymm2, 39
	vpsrlq ymm2, ymm2, 25
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+480]
	vpxor ymm3, ymm3, ymm5
	vpsllq ymm10, ymm3, 41
	vpsrlq ymm3, ymm3, 23
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+672]
	vpxor ymm4, ymm4, ymm6
	vpsllq ymm10, ymm4, 2
	vpsrlq ymm4, ymm4, 62
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+640], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+672], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+704], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+736], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+768], ymm10
	vpxor ymm15, ymm15, ymm10
	mov rax, rdi
	mov rdi, rsi
	mov rsi, rax
	add rdx, 32
	cmp rdx, rcx
	jne 27b
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
	mov r10d, 21
	vmovdqu ymm8, YMMWORD PTR [r11+4096]
	vmovdqu ymm9, YMMWORD PTR [r11+4128]
	vmovdqu ymm10, YMMWORD PTR [r11+4160]
28:
	cmp rdi, 241
	jb 29f
	cmp rdi, 256
	jb 211f
	add rsi, 24
	jmp 212f
211:
	mov ecx, 8
213:
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
	jb 214f
	jmp 215f
214:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 216f
	jmp 217f
216:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
217:
215:
	add rsi, 3
	sub rcx, 1
	jne 213b
212:
	jmp 210f
29:
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
210:
	sub r10, 1
	jne 28b
	mov QWORD PTR [rbx+4424], rdi
	mov rsi, rbx
	add rsi, 2872
	mov edi, 0
	mov rbp, r13
	add rbp, 512
	mov r10d, 21
	vmovdqu ymm8, YMMWORD PTR [r11+4096]
	vmovdqu ymm9, YMMWORD PTR [r11+4128]
	vmovdqu ymm10, YMMWORD PTR [r11+4160]
218:
	cmp rdi, 241
	jb 219f
	cmp rdi, 256
	jb 221f
	add rsi, 24
	jmp 222f
221:
	mov ecx, 8
223:
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
	jb 224f
	jmp 225f
224:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 226f
	jmp 227f
226:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
227:
225:
	add rsi, 3
	sub rcx, 1
	jne 223b
222:
	jmp 220f
219:
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
220:
	sub r10, 1
	jne 218b
	mov QWORD PTR [rbx+4432], rdi
	mov rsi, rbx
	add rsi, 3376
	mov edi, 0
	mov rbp, r13
	add rbp, 1024
	mov r10d, 21
	vmovdqu ymm8, YMMWORD PTR [r11+4096]
	vmovdqu ymm9, YMMWORD PTR [r11+4128]
	vmovdqu ymm10, YMMWORD PTR [r11+4160]
228:
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
	sub r10, 1
	jne 228b
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
	je 238f
	jmp 239f
238:
	mov r14d, 1
	mov rbp, rbx
	add rbp, 2368
	mov r10d, 2
240:
	mov rdi, rbx
	mov rsi, rbx
	add rsi, 800
	mov rdx, rbx
	add rdx, 1600
	mov rcx, rbx
	add rcx, 2368
	vmovdqu ymm11, YMMWORD PTR [rdi]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+160]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+320]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+480]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+640]
	vmovdqu ymm12, YMMWORD PTR [rdi+32]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+192]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+352]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+512]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+672]
	vmovdqu ymm13, YMMWORD PTR [rdi+64]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+224]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+384]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+544]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+704]
	vmovdqu ymm14, YMMWORD PTR [rdi+96]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+256]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+416]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+576]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+736]
	vmovdqu ymm15, YMMWORD PTR [rdi+128]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+288]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+448]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+608]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+768]
241:
	vpsllq ymm10, ymm12, 1
	vpsrlq ymm5, ymm12, 63
	vpor ymm5, ymm5, ymm10
	vpxor ymm5, ymm5, ymm15
	vpsllq ymm10, ymm13, 1
	vpsrlq ymm6, ymm13, 63
	vpor ymm6, ymm6, ymm10
	vpxor ymm6, ymm6, ymm11
	vpsllq ymm10, ymm14, 1
	vpsrlq ymm7, ymm14, 63
	vpor ymm7, ymm7, ymm10
	vpxor ymm7, ymm7, ymm12
	vpsllq ymm10, ymm15, 1
	vpsrlq ymm8, ymm15, 63
	vpor ymm8, ymm8, ymm10
	vpxor ymm8, ymm8, ymm13
	vpsllq ymm10, ymm11, 1
	vpsrlq ymm9, ymm11, 63
	vpor ymm9, ymm9, ymm10
	vpxor ymm9, ymm9, ymm14
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpxor ymm0, ymm0, ymm5
	vmovdqu ymm1, YMMWORD PTR [rdi+192]
	vpxor ymm1, ymm1, ymm6
	vpsllq ymm10, ymm1, 44
	vpsrlq ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+384]
	vpxor ymm2, ymm2, ymm7
	vpsllq ymm10, ymm2, 43
	vpsrlq ymm2, ymm2, 21
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+576]
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm10, ymm3, 21
	vpsrlq ymm3, ymm3, 43
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+768]
	vpxor ymm4, ymm4, ymm9
	vpsllq ymm10, ymm4, 14
	vpsrlq ymm4, ymm4, 50
	vpor ymm4, ymm4, ymm10
	vpandn ymm11, ymm1, ymm2
	vpxor ymm11, ymm11, ymm0
	vpxor ymm11, ymm11, YMMWORD PTR [rdx]
	vmovdqu YMMWORD PTR [rsi], ymm11
	vpandn ymm12, ymm2, ymm3
	vpxor ymm12, ymm12, ymm1
	vmovdqu YMMWORD PTR [rsi+32], ymm12
	vpandn ymm13, ymm3, ymm4
	vpxor ymm13, ymm13, ymm2
	vmovdqu YMMWORD PTR [rsi+64], ymm13
	vpandn ymm14, ymm4, ymm0
	vpxor ymm14, ymm14, ymm3
	vmovdqu YMMWORD PTR [rsi+96], ymm14
	vpandn ymm15, ymm0, ymm1
	vpxor ymm15, ymm15, ymm4
	vmovdqu YMMWORD PTR [rsi+128], ymm15
	vmovdqu ymm0, YMMWORD PTR [rdi+96]
	vpxor ymm0, ymm0, ymm8
	vpsllq ymm10, ymm0, 28
	vpsrlq ymm0, ymm0, 36
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+288]
	vpxor ymm1, ymm1, ymm9
	vpsllq ymm10, ymm1, 20
	vpsrlq ymm1, ymm1, 44
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+320]
	vpxor ymm2, ymm2, ymm5
	vpsllq ymm10, ymm2, 3
	vpsrlq ymm2, ymm2, 61
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+512]
	vpxor ymm3, ymm3, ymm6
	vpsllq ymm10, ymm3, 45
	vpsrlq ymm3, ymm3, 19
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+704]
	vpxor ymm4, ymm4, ymm7
	vpsllq ymm10, ymm4, 61
	vpsrlq ymm4, ymm4, 3
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+160], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+192], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+224], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+256], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+288], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+32]
	vpxor ymm0, ymm0, ymm6
	vpsllq ymm10, ymm0, 1
	vpsrlq ymm0, ymm0, 63
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+224]
	vpxor ymm1, ymm1, ymm7
	vpsllq ymm10, ymm1, 6
	vpsrlq ymm1, ymm1, 58
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+416]
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm10, ymm2, 25
	vpsrlq ymm2, ymm2, 39
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+608]
	vpxor ymm3, ymm3, ymm9
	vpsllq ymm10, ymm3, 8
	vpsrlq ymm3, ymm3, 56
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+640]
	vpxor ymm4, ymm4, ymm5
	vpsllq ymm10, ymm4, 18
	vpsrlq ymm4, ymm4, 46
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+320], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+352], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+384], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+416], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+448], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+128]
	vpxor ymm0, ymm0, ymm9
	vpsllq ymm10, ymm0, 27
	vpsrlq ymm0, ymm0, 37
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+160]
	vpxor ymm1, ymm1, ymm5
	vpsllq ymm10, ymm1, 36
	vpsrlq ymm1, ymm1, 28
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+352]
	vpxor ymm2, ymm2, ymm6
	vpsllq ymm10, ymm2, 10
	vpsrlq ymm2, ymm2, 54
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+544]
	vpxor ymm3, ymm3, ymm7
	vpsllq ymm10, ymm3, 15
	vpsrlq ymm3, ymm3, 49
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+736]
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm10, ymm4, 56
	vpsrlq ymm4, ymm4, 8
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+480], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+512], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+544], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+576], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+608], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+64]
	vpxor ymm0, ymm0, ymm7
	vpsllq ymm10, ymm0, 62
	vpsrlq ymm0, ymm0, 2
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+256]
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm10, ymm1, 55
	vpsrlq ymm1, ymm1, 9
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+448]
	vpxor ymm2, ymm2, ymm9
	vpsllq ymm10, ymm2, 39
	vpsrlq ymm2, ymm2, 25
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+480]
	vpxor ymm3, ymm3, ymm5
	vpsllq ymm10, ymm3, 41
	vpsrlq ymm3, ymm3, 23
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+672]
	vpxor ymm4, ymm4, ymm6
	vpsllq ymm10, ymm4, 2
	vpsrlq ymm4, ymm4, 62
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+640], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+672], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+704], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+736], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+768], ymm10
	vpxor ymm15, ymm15, ymm10
	mov rax, rdi
	mov rdi, rsi
	mov rsi, rax
	add rdx, 32
	cmp rdx, rcx
	vpsllq ymm10, ymm12, 1
	vpsrlq ymm5, ymm12, 63
	vpor ymm5, ymm5, ymm10
	vpxor ymm5, ymm5, ymm15
	vpsllq ymm10, ymm13, 1
	vpsrlq ymm6, ymm13, 63
	vpor ymm6, ymm6, ymm10
	vpxor ymm6, ymm6, ymm11
	vpsllq ymm10, ymm14, 1
	vpsrlq ymm7, ymm14, 63
	vpor ymm7, ymm7, ymm10
	vpxor ymm7, ymm7, ymm12
	vpsllq ymm10, ymm15, 1
	vpsrlq ymm8, ymm15, 63
	vpor ymm8, ymm8, ymm10
	vpxor ymm8, ymm8, ymm13
	vpsllq ymm10, ymm11, 1
	vpsrlq ymm9, ymm11, 63
	vpor ymm9, ymm9, ymm10
	vpxor ymm9, ymm9, ymm14
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpxor ymm0, ymm0, ymm5
	vmovdqu ymm1, YMMWORD PTR [rdi+192]
	vpxor ymm1, ymm1, ymm6
	vpsllq ymm10, ymm1, 44
	vpsrlq ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+384]
	vpxor ymm2, ymm2, ymm7
	vpsllq ymm10, ymm2, 43
	vpsrlq ymm2, ymm2, 21
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+576]
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm10, ymm3, 21
	vpsrlq ymm3, ymm3, 43
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+768]
	vpxor ymm4, ymm4, ymm9
	vpsllq ymm10, ymm4, 14
	vpsrlq ymm4, ymm4, 50
	vpor ymm4, ymm4, ymm10
	vpandn ymm11, ymm1, ymm2
	vpxor ymm11, ymm11, ymm0
	vpxor ymm11, ymm11, YMMWORD PTR [rdx]
	vmovdqu YMMWORD PTR [rsi], ymm11
	vpandn ymm12, ymm2, ymm3
	vpxor ymm12, ymm12, ymm1
	vmovdqu YMMWORD PTR [rsi+32], ymm12
	vpandn ymm13, ymm3, ymm4
	vpxor ymm13, ymm13, ymm2
	vmovdqu YMMWORD PTR [rsi+64], ymm13
	vpandn ymm14, ymm4, ymm0
	vpxor ymm14, ymm14, ymm3
	vmovdqu YMMWORD PTR [rsi+96], ymm14
	vpandn ymm15, ymm0, ymm1
	vpxor ymm15, ymm15, ymm4
	vmovdqu YMMWORD PTR [rsi+128], ymm15
	vmovdqu ymm0, YMMWORD PTR [rdi+96]
	vpxor ymm0, ymm0, ymm8
	vpsllq ymm10, ymm0, 28
	vpsrlq ymm0, ymm0, 36
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+288]
	vpxor ymm1, ymm1, ymm9
	vpsllq ymm10, ymm1, 20
	vpsrlq ymm1, ymm1, 44
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+320]
	vpxor ymm2, ymm2, ymm5
	vpsllq ymm10, ymm2, 3
	vpsrlq ymm2, ymm2, 61
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+512]
	vpxor ymm3, ymm3, ymm6
	vpsllq ymm10, ymm3, 45
	vpsrlq ymm3, ymm3, 19
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+704]
	vpxor ymm4, ymm4, ymm7
	vpsllq ymm10, ymm4, 61
	vpsrlq ymm4, ymm4, 3
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+160], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+192], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+224], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+256], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+288], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+32]
	vpxor ymm0, ymm0, ymm6
	vpsllq ymm10, ymm0, 1
	vpsrlq ymm0, ymm0, 63
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+224]
	vpxor ymm1, ymm1, ymm7
	vpsllq ymm10, ymm1, 6
	vpsrlq ymm1, ymm1, 58
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+416]
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm10, ymm2, 25
	vpsrlq ymm2, ymm2, 39
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+608]
	vpxor ymm3, ymm3, ymm9
	vpsllq ymm10, ymm3, 8
	vpsrlq ymm3, ymm3, 56
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+640]
	vpxor ymm4, ymm4, ymm5
	vpsllq ymm10, ymm4, 18
	vpsrlq ymm4, ymm4, 46
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+320], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+352], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+384], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+416], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+448], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+128]
	vpxor ymm0, ymm0, ymm9
	vpsllq ymm10, ymm0, 27
	vpsrlq ymm0, ymm0, 37
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+160]
	vpxor ymm1, ymm1, ymm5
	vpsllq ymm10, ymm1, 36
	vpsrlq ymm1, ymm1, 28
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+352]
	vpxor ymm2, ymm2, ymm6
	vpsllq ymm10, ymm2, 10
	vpsrlq ymm2, ymm2, 54
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+544]
	vpxor ymm3, ymm3, ymm7
	vpsllq ymm10, ymm3, 15
	vpsrlq ymm3, ymm3, 49
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+736]
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm10, ymm4, 56
	vpsrlq ymm4, ymm4, 8
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+480], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+512], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+544], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+576], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+608], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+64]
	vpxor ymm0, ymm0, ymm7
	vpsllq ymm10, ymm0, 62
	vpsrlq ymm0, ymm0, 2
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+256]
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm10, ymm1, 55
	vpsrlq ymm1, ymm1, 9
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+448]
	vpxor ymm2, ymm2, ymm9
	vpsllq ymm10, ymm2, 39
	vpsrlq ymm2, ymm2, 25
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+480]
	vpxor ymm3, ymm3, ymm5
	vpsllq ymm10, ymm3, 41
	vpsrlq ymm3, ymm3, 23
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+672]
	vpxor ymm4, ymm4, ymm6
	vpsllq ymm10, ymm4, 2
	vpsrlq ymm4, ymm4, 62
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+640], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+672], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+704], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+736], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+768], ymm10
	vpxor ymm15, ymm15, ymm10
	mov rax, rdi
	mov rdi, rsi
	mov rsi, rax
	add rdx, 32
	cmp rdx, rcx
	jne 241b
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
	jne 240b
	lea r11, {VG_MLKEM_SAMPLE_TBL}
	mov rsi, rbx
	add rsi, 2368
	mov rdi, QWORD PTR [rbx+4424]
	mov rbp, r13
	add rbp, 0
	mov r10d, 14
	vmovdqu ymm8, YMMWORD PTR [r11+4096]
	vmovdqu ymm9, YMMWORD PTR [r11+4128]
	vmovdqu ymm10, YMMWORD PTR [r11+4160]
242:
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
	sub r10, 1
	jne 242b
	mov QWORD PTR [rbx+4424], rdi
	mov rsi, rbx
	add rsi, 2872
	mov rdi, QWORD PTR [rbx+4432]
	mov rbp, r13
	add rbp, 512
	mov r10d, 14
	vmovdqu ymm8, YMMWORD PTR [r11+4096]
	vmovdqu ymm9, YMMWORD PTR [r11+4128]
	vmovdqu ymm10, YMMWORD PTR [r11+4160]
252:
	cmp rdi, 241
	jb 253f
	cmp rdi, 256
	jb 255f
	add rsi, 24
	jmp 256f
255:
	mov ecx, 8
257:
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
	jb 258f
	jmp 259f
258:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 260f
	jmp 261f
260:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
261:
259:
	add rsi, 3
	sub rcx, 1
	jne 257b
256:
	jmp 254f
253:
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
254:
	sub r10, 1
	jne 252b
	mov QWORD PTR [rbx+4432], rdi
	mov rsi, rbx
	add rsi, 3376
	mov rdi, QWORD PTR [rbx+4440]
	mov rbp, r13
	add rbp, 1024
	mov r10d, 14
	vmovdqu ymm8, YMMWORD PTR [r11+4096]
	vmovdqu ymm9, YMMWORD PTR [r11+4128]
	vmovdqu ymm10, YMMWORD PTR [r11+4160]
262:
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
	sub r10, 1
	jne 262b
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
239:
	vzeroupper
	mov eax, r14d
	mov r14, QWORD PTR [rbx+4416]
	mov r13, QWORD PTR [rbx+4408]
	mov r12, QWORD PTR [rbx+4400]
	mov rbp, QWORD PTR [rbx+4392]
	mov rbx, QWORD PTR [rbx+4384]
	and r15d, eax
	mov rdi, rbx
	add rdi, 19208
	mov rsi, r14
	add rsi, 408
	mov ecx, 51
272:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 272b
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
273:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 273b
	mov eax, 0
	mov BYTE PTR [rbx+32], al
	mov eax, 1
	mov BYTE PTR [rbx+33], al
	mov rdi, rbx
	add rdi, 34
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
274:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 274b
	mov eax, 1
	mov BYTE PTR [rbx+66], al
	mov eax, 1
	mov BYTE PTR [rbx+67], al
	mov rdi, rbx
	add rdi, 68
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
275:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 275b
	mov eax, 2
	mov BYTE PTR [rbx+100], al
	mov eax, 1
	mov BYTE PTR [rbx+101], al
	mov rdi, rbx
	add rdi, 102
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
276:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 276b
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
	mov r10d, 3
277:
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
	vmovdqu ymm11, YMMWORD PTR [rdi]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+160]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+320]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+480]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+640]
	vmovdqu ymm12, YMMWORD PTR [rdi+32]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+192]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+352]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+512]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+672]
	vmovdqu ymm13, YMMWORD PTR [rdi+64]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+224]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+384]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+544]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+704]
	vmovdqu ymm14, YMMWORD PTR [rdi+96]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+256]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+416]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+576]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+736]
	vmovdqu ymm15, YMMWORD PTR [rdi+128]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+288]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+448]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+608]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+768]
278:
	vpsllq ymm10, ymm12, 1
	vpsrlq ymm5, ymm12, 63
	vpor ymm5, ymm5, ymm10
	vpxor ymm5, ymm5, ymm15
	vpsllq ymm10, ymm13, 1
	vpsrlq ymm6, ymm13, 63
	vpor ymm6, ymm6, ymm10
	vpxor ymm6, ymm6, ymm11
	vpsllq ymm10, ymm14, 1
	vpsrlq ymm7, ymm14, 63
	vpor ymm7, ymm7, ymm10
	vpxor ymm7, ymm7, ymm12
	vpsllq ymm10, ymm15, 1
	vpsrlq ymm8, ymm15, 63
	vpor ymm8, ymm8, ymm10
	vpxor ymm8, ymm8, ymm13
	vpsllq ymm10, ymm11, 1
	vpsrlq ymm9, ymm11, 63
	vpor ymm9, ymm9, ymm10
	vpxor ymm9, ymm9, ymm14
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpxor ymm0, ymm0, ymm5
	vmovdqu ymm1, YMMWORD PTR [rdi+192]
	vpxor ymm1, ymm1, ymm6
	vpsllq ymm10, ymm1, 44
	vpsrlq ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+384]
	vpxor ymm2, ymm2, ymm7
	vpsllq ymm10, ymm2, 43
	vpsrlq ymm2, ymm2, 21
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+576]
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm10, ymm3, 21
	vpsrlq ymm3, ymm3, 43
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+768]
	vpxor ymm4, ymm4, ymm9
	vpsllq ymm10, ymm4, 14
	vpsrlq ymm4, ymm4, 50
	vpor ymm4, ymm4, ymm10
	vpandn ymm11, ymm1, ymm2
	vpxor ymm11, ymm11, ymm0
	vpxor ymm11, ymm11, YMMWORD PTR [rdx]
	vmovdqu YMMWORD PTR [rsi], ymm11
	vpandn ymm12, ymm2, ymm3
	vpxor ymm12, ymm12, ymm1
	vmovdqu YMMWORD PTR [rsi+32], ymm12
	vpandn ymm13, ymm3, ymm4
	vpxor ymm13, ymm13, ymm2
	vmovdqu YMMWORD PTR [rsi+64], ymm13
	vpandn ymm14, ymm4, ymm0
	vpxor ymm14, ymm14, ymm3
	vmovdqu YMMWORD PTR [rsi+96], ymm14
	vpandn ymm15, ymm0, ymm1
	vpxor ymm15, ymm15, ymm4
	vmovdqu YMMWORD PTR [rsi+128], ymm15
	vmovdqu ymm0, YMMWORD PTR [rdi+96]
	vpxor ymm0, ymm0, ymm8
	vpsllq ymm10, ymm0, 28
	vpsrlq ymm0, ymm0, 36
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+288]
	vpxor ymm1, ymm1, ymm9
	vpsllq ymm10, ymm1, 20
	vpsrlq ymm1, ymm1, 44
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+320]
	vpxor ymm2, ymm2, ymm5
	vpsllq ymm10, ymm2, 3
	vpsrlq ymm2, ymm2, 61
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+512]
	vpxor ymm3, ymm3, ymm6
	vpsllq ymm10, ymm3, 45
	vpsrlq ymm3, ymm3, 19
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+704]
	vpxor ymm4, ymm4, ymm7
	vpsllq ymm10, ymm4, 61
	vpsrlq ymm4, ymm4, 3
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+160], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+192], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+224], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+256], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+288], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+32]
	vpxor ymm0, ymm0, ymm6
	vpsllq ymm10, ymm0, 1
	vpsrlq ymm0, ymm0, 63
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+224]
	vpxor ymm1, ymm1, ymm7
	vpsllq ymm10, ymm1, 6
	vpsrlq ymm1, ymm1, 58
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+416]
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm10, ymm2, 25
	vpsrlq ymm2, ymm2, 39
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+608]
	vpxor ymm3, ymm3, ymm9
	vpsllq ymm10, ymm3, 8
	vpsrlq ymm3, ymm3, 56
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+640]
	vpxor ymm4, ymm4, ymm5
	vpsllq ymm10, ymm4, 18
	vpsrlq ymm4, ymm4, 46
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+320], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+352], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+384], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+416], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+448], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+128]
	vpxor ymm0, ymm0, ymm9
	vpsllq ymm10, ymm0, 27
	vpsrlq ymm0, ymm0, 37
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+160]
	vpxor ymm1, ymm1, ymm5
	vpsllq ymm10, ymm1, 36
	vpsrlq ymm1, ymm1, 28
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+352]
	vpxor ymm2, ymm2, ymm6
	vpsllq ymm10, ymm2, 10
	vpsrlq ymm2, ymm2, 54
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+544]
	vpxor ymm3, ymm3, ymm7
	vpsllq ymm10, ymm3, 15
	vpsrlq ymm3, ymm3, 49
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+736]
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm10, ymm4, 56
	vpsrlq ymm4, ymm4, 8
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+480], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+512], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+544], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+576], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+608], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+64]
	vpxor ymm0, ymm0, ymm7
	vpsllq ymm10, ymm0, 62
	vpsrlq ymm0, ymm0, 2
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+256]
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm10, ymm1, 55
	vpsrlq ymm1, ymm1, 9
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+448]
	vpxor ymm2, ymm2, ymm9
	vpsllq ymm10, ymm2, 39
	vpsrlq ymm2, ymm2, 25
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+480]
	vpxor ymm3, ymm3, ymm5
	vpsllq ymm10, ymm3, 41
	vpsrlq ymm3, ymm3, 23
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+672]
	vpxor ymm4, ymm4, ymm6
	vpsllq ymm10, ymm4, 2
	vpsrlq ymm4, ymm4, 62
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+640], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+672], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+704], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+736], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+768], ymm10
	vpxor ymm15, ymm15, ymm10
	mov rax, rdi
	mov rdi, rsi
	mov rsi, rax
	add rdx, 32
	cmp rdx, rcx
	vpsllq ymm10, ymm12, 1
	vpsrlq ymm5, ymm12, 63
	vpor ymm5, ymm5, ymm10
	vpxor ymm5, ymm5, ymm15
	vpsllq ymm10, ymm13, 1
	vpsrlq ymm6, ymm13, 63
	vpor ymm6, ymm6, ymm10
	vpxor ymm6, ymm6, ymm11
	vpsllq ymm10, ymm14, 1
	vpsrlq ymm7, ymm14, 63
	vpor ymm7, ymm7, ymm10
	vpxor ymm7, ymm7, ymm12
	vpsllq ymm10, ymm15, 1
	vpsrlq ymm8, ymm15, 63
	vpor ymm8, ymm8, ymm10
	vpxor ymm8, ymm8, ymm13
	vpsllq ymm10, ymm11, 1
	vpsrlq ymm9, ymm11, 63
	vpor ymm9, ymm9, ymm10
	vpxor ymm9, ymm9, ymm14
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpxor ymm0, ymm0, ymm5
	vmovdqu ymm1, YMMWORD PTR [rdi+192]
	vpxor ymm1, ymm1, ymm6
	vpsllq ymm10, ymm1, 44
	vpsrlq ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+384]
	vpxor ymm2, ymm2, ymm7
	vpsllq ymm10, ymm2, 43
	vpsrlq ymm2, ymm2, 21
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+576]
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm10, ymm3, 21
	vpsrlq ymm3, ymm3, 43
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+768]
	vpxor ymm4, ymm4, ymm9
	vpsllq ymm10, ymm4, 14
	vpsrlq ymm4, ymm4, 50
	vpor ymm4, ymm4, ymm10
	vpandn ymm11, ymm1, ymm2
	vpxor ymm11, ymm11, ymm0
	vpxor ymm11, ymm11, YMMWORD PTR [rdx]
	vmovdqu YMMWORD PTR [rsi], ymm11
	vpandn ymm12, ymm2, ymm3
	vpxor ymm12, ymm12, ymm1
	vmovdqu YMMWORD PTR [rsi+32], ymm12
	vpandn ymm13, ymm3, ymm4
	vpxor ymm13, ymm13, ymm2
	vmovdqu YMMWORD PTR [rsi+64], ymm13
	vpandn ymm14, ymm4, ymm0
	vpxor ymm14, ymm14, ymm3
	vmovdqu YMMWORD PTR [rsi+96], ymm14
	vpandn ymm15, ymm0, ymm1
	vpxor ymm15, ymm15, ymm4
	vmovdqu YMMWORD PTR [rsi+128], ymm15
	vmovdqu ymm0, YMMWORD PTR [rdi+96]
	vpxor ymm0, ymm0, ymm8
	vpsllq ymm10, ymm0, 28
	vpsrlq ymm0, ymm0, 36
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+288]
	vpxor ymm1, ymm1, ymm9
	vpsllq ymm10, ymm1, 20
	vpsrlq ymm1, ymm1, 44
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+320]
	vpxor ymm2, ymm2, ymm5
	vpsllq ymm10, ymm2, 3
	vpsrlq ymm2, ymm2, 61
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+512]
	vpxor ymm3, ymm3, ymm6
	vpsllq ymm10, ymm3, 45
	vpsrlq ymm3, ymm3, 19
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+704]
	vpxor ymm4, ymm4, ymm7
	vpsllq ymm10, ymm4, 61
	vpsrlq ymm4, ymm4, 3
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+160], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+192], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+224], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+256], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+288], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+32]
	vpxor ymm0, ymm0, ymm6
	vpsllq ymm10, ymm0, 1
	vpsrlq ymm0, ymm0, 63
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+224]
	vpxor ymm1, ymm1, ymm7
	vpsllq ymm10, ymm1, 6
	vpsrlq ymm1, ymm1, 58
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+416]
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm10, ymm2, 25
	vpsrlq ymm2, ymm2, 39
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+608]
	vpxor ymm3, ymm3, ymm9
	vpsllq ymm10, ymm3, 8
	vpsrlq ymm3, ymm3, 56
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+640]
	vpxor ymm4, ymm4, ymm5
	vpsllq ymm10, ymm4, 18
	vpsrlq ymm4, ymm4, 46
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+320], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+352], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+384], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+416], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+448], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+128]
	vpxor ymm0, ymm0, ymm9
	vpsllq ymm10, ymm0, 27
	vpsrlq ymm0, ymm0, 37
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+160]
	vpxor ymm1, ymm1, ymm5
	vpsllq ymm10, ymm1, 36
	vpsrlq ymm1, ymm1, 28
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+352]
	vpxor ymm2, ymm2, ymm6
	vpsllq ymm10, ymm2, 10
	vpsrlq ymm2, ymm2, 54
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+544]
	vpxor ymm3, ymm3, ymm7
	vpsllq ymm10, ymm3, 15
	vpsrlq ymm3, ymm3, 49
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+736]
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm10, ymm4, 56
	vpsrlq ymm4, ymm4, 8
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+480], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+512], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+544], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+576], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+608], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+64]
	vpxor ymm0, ymm0, ymm7
	vpsllq ymm10, ymm0, 62
	vpsrlq ymm0, ymm0, 2
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+256]
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm10, ymm1, 55
	vpsrlq ymm1, ymm1, 9
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+448]
	vpxor ymm2, ymm2, ymm9
	vpsllq ymm10, ymm2, 39
	vpsrlq ymm2, ymm2, 25
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+480]
	vpxor ymm3, ymm3, ymm5
	vpsllq ymm10, ymm3, 41
	vpsrlq ymm3, ymm3, 23
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+672]
	vpxor ymm4, ymm4, ymm6
	vpsllq ymm10, ymm4, 2
	vpsrlq ymm4, ymm4, 62
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+640], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+672], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+704], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+736], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+768], ymm10
	vpxor ymm15, ymm15, ymm10
	mov rax, rdi
	mov rdi, rsi
	mov rsi, rax
	add rdx, 32
	cmp rdx, rcx
	jne 278b
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
	jne 277b
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
	mov r10d, 21
	vmovdqu ymm8, YMMWORD PTR [r11+4096]
	vmovdqu ymm9, YMMWORD PTR [r11+4128]
	vmovdqu ymm10, YMMWORD PTR [r11+4160]
279:
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
	sub r10, 1
	jne 279b
	mov QWORD PTR [rbx+4424], rdi
	mov rsi, rbx
	add rsi, 2872
	mov edi, 0
	mov rbp, r13
	add rbp, 512
	mov r10d, 21
	vmovdqu ymm8, YMMWORD PTR [r11+4096]
	vmovdqu ymm9, YMMWORD PTR [r11+4128]
	vmovdqu ymm10, YMMWORD PTR [r11+4160]
289:
	cmp rdi, 241
	jb 290f
	cmp rdi, 256
	jb 292f
	add rsi, 24
	jmp 293f
292:
	mov ecx, 8
294:
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
	jb 295f
	jmp 296f
295:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 297f
	jmp 298f
297:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
298:
296:
	add rsi, 3
	sub rcx, 1
	jne 294b
293:
	jmp 291f
290:
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
291:
	sub r10, 1
	jne 289b
	mov QWORD PTR [rbx+4432], rdi
	mov rsi, rbx
	add rsi, 3376
	mov edi, 0
	mov rbp, r13
	add rbp, 1024
	mov r10d, 21
	vmovdqu ymm8, YMMWORD PTR [r11+4096]
	vmovdqu ymm9, YMMWORD PTR [r11+4128]
	vmovdqu ymm10, YMMWORD PTR [r11+4160]
299:
	cmp rdi, 241
	jb 2100f
	cmp rdi, 256
	jb 2102f
	add rsi, 24
	jmp 2103f
2102:
	mov ecx, 8
2104:
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
	jb 2105f
	jmp 2106f
2105:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2107f
	jmp 2108f
2107:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2108:
2106:
	add rsi, 3
	sub rcx, 1
	jne 2104b
2103:
	jmp 2101f
2100:
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
2101:
	sub r10, 1
	jne 299b
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
	je 2109f
	jmp 2110f
2109:
	mov r14d, 1
	mov rbp, rbx
	add rbp, 2368
	mov r10d, 2
2111:
	mov rdi, rbx
	mov rsi, rbx
	add rsi, 800
	mov rdx, rbx
	add rdx, 1600
	mov rcx, rbx
	add rcx, 2368
	vmovdqu ymm11, YMMWORD PTR [rdi]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+160]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+320]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+480]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+640]
	vmovdqu ymm12, YMMWORD PTR [rdi+32]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+192]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+352]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+512]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+672]
	vmovdqu ymm13, YMMWORD PTR [rdi+64]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+224]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+384]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+544]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+704]
	vmovdqu ymm14, YMMWORD PTR [rdi+96]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+256]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+416]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+576]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+736]
	vmovdqu ymm15, YMMWORD PTR [rdi+128]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+288]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+448]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+608]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+768]
2112:
	vpsllq ymm10, ymm12, 1
	vpsrlq ymm5, ymm12, 63
	vpor ymm5, ymm5, ymm10
	vpxor ymm5, ymm5, ymm15
	vpsllq ymm10, ymm13, 1
	vpsrlq ymm6, ymm13, 63
	vpor ymm6, ymm6, ymm10
	vpxor ymm6, ymm6, ymm11
	vpsllq ymm10, ymm14, 1
	vpsrlq ymm7, ymm14, 63
	vpor ymm7, ymm7, ymm10
	vpxor ymm7, ymm7, ymm12
	vpsllq ymm10, ymm15, 1
	vpsrlq ymm8, ymm15, 63
	vpor ymm8, ymm8, ymm10
	vpxor ymm8, ymm8, ymm13
	vpsllq ymm10, ymm11, 1
	vpsrlq ymm9, ymm11, 63
	vpor ymm9, ymm9, ymm10
	vpxor ymm9, ymm9, ymm14
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpxor ymm0, ymm0, ymm5
	vmovdqu ymm1, YMMWORD PTR [rdi+192]
	vpxor ymm1, ymm1, ymm6
	vpsllq ymm10, ymm1, 44
	vpsrlq ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+384]
	vpxor ymm2, ymm2, ymm7
	vpsllq ymm10, ymm2, 43
	vpsrlq ymm2, ymm2, 21
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+576]
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm10, ymm3, 21
	vpsrlq ymm3, ymm3, 43
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+768]
	vpxor ymm4, ymm4, ymm9
	vpsllq ymm10, ymm4, 14
	vpsrlq ymm4, ymm4, 50
	vpor ymm4, ymm4, ymm10
	vpandn ymm11, ymm1, ymm2
	vpxor ymm11, ymm11, ymm0
	vpxor ymm11, ymm11, YMMWORD PTR [rdx]
	vmovdqu YMMWORD PTR [rsi], ymm11
	vpandn ymm12, ymm2, ymm3
	vpxor ymm12, ymm12, ymm1
	vmovdqu YMMWORD PTR [rsi+32], ymm12
	vpandn ymm13, ymm3, ymm4
	vpxor ymm13, ymm13, ymm2
	vmovdqu YMMWORD PTR [rsi+64], ymm13
	vpandn ymm14, ymm4, ymm0
	vpxor ymm14, ymm14, ymm3
	vmovdqu YMMWORD PTR [rsi+96], ymm14
	vpandn ymm15, ymm0, ymm1
	vpxor ymm15, ymm15, ymm4
	vmovdqu YMMWORD PTR [rsi+128], ymm15
	vmovdqu ymm0, YMMWORD PTR [rdi+96]
	vpxor ymm0, ymm0, ymm8
	vpsllq ymm10, ymm0, 28
	vpsrlq ymm0, ymm0, 36
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+288]
	vpxor ymm1, ymm1, ymm9
	vpsllq ymm10, ymm1, 20
	vpsrlq ymm1, ymm1, 44
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+320]
	vpxor ymm2, ymm2, ymm5
	vpsllq ymm10, ymm2, 3
	vpsrlq ymm2, ymm2, 61
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+512]
	vpxor ymm3, ymm3, ymm6
	vpsllq ymm10, ymm3, 45
	vpsrlq ymm3, ymm3, 19
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+704]
	vpxor ymm4, ymm4, ymm7
	vpsllq ymm10, ymm4, 61
	vpsrlq ymm4, ymm4, 3
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+160], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+192], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+224], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+256], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+288], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+32]
	vpxor ymm0, ymm0, ymm6
	vpsllq ymm10, ymm0, 1
	vpsrlq ymm0, ymm0, 63
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+224]
	vpxor ymm1, ymm1, ymm7
	vpsllq ymm10, ymm1, 6
	vpsrlq ymm1, ymm1, 58
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+416]
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm10, ymm2, 25
	vpsrlq ymm2, ymm2, 39
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+608]
	vpxor ymm3, ymm3, ymm9
	vpsllq ymm10, ymm3, 8
	vpsrlq ymm3, ymm3, 56
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+640]
	vpxor ymm4, ymm4, ymm5
	vpsllq ymm10, ymm4, 18
	vpsrlq ymm4, ymm4, 46
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+320], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+352], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+384], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+416], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+448], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+128]
	vpxor ymm0, ymm0, ymm9
	vpsllq ymm10, ymm0, 27
	vpsrlq ymm0, ymm0, 37
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+160]
	vpxor ymm1, ymm1, ymm5
	vpsllq ymm10, ymm1, 36
	vpsrlq ymm1, ymm1, 28
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+352]
	vpxor ymm2, ymm2, ymm6
	vpsllq ymm10, ymm2, 10
	vpsrlq ymm2, ymm2, 54
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+544]
	vpxor ymm3, ymm3, ymm7
	vpsllq ymm10, ymm3, 15
	vpsrlq ymm3, ymm3, 49
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+736]
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm10, ymm4, 56
	vpsrlq ymm4, ymm4, 8
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+480], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+512], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+544], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+576], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+608], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+64]
	vpxor ymm0, ymm0, ymm7
	vpsllq ymm10, ymm0, 62
	vpsrlq ymm0, ymm0, 2
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+256]
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm10, ymm1, 55
	vpsrlq ymm1, ymm1, 9
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+448]
	vpxor ymm2, ymm2, ymm9
	vpsllq ymm10, ymm2, 39
	vpsrlq ymm2, ymm2, 25
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+480]
	vpxor ymm3, ymm3, ymm5
	vpsllq ymm10, ymm3, 41
	vpsrlq ymm3, ymm3, 23
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+672]
	vpxor ymm4, ymm4, ymm6
	vpsllq ymm10, ymm4, 2
	vpsrlq ymm4, ymm4, 62
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+640], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+672], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+704], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+736], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+768], ymm10
	vpxor ymm15, ymm15, ymm10
	mov rax, rdi
	mov rdi, rsi
	mov rsi, rax
	add rdx, 32
	cmp rdx, rcx
	vpsllq ymm10, ymm12, 1
	vpsrlq ymm5, ymm12, 63
	vpor ymm5, ymm5, ymm10
	vpxor ymm5, ymm5, ymm15
	vpsllq ymm10, ymm13, 1
	vpsrlq ymm6, ymm13, 63
	vpor ymm6, ymm6, ymm10
	vpxor ymm6, ymm6, ymm11
	vpsllq ymm10, ymm14, 1
	vpsrlq ymm7, ymm14, 63
	vpor ymm7, ymm7, ymm10
	vpxor ymm7, ymm7, ymm12
	vpsllq ymm10, ymm15, 1
	vpsrlq ymm8, ymm15, 63
	vpor ymm8, ymm8, ymm10
	vpxor ymm8, ymm8, ymm13
	vpsllq ymm10, ymm11, 1
	vpsrlq ymm9, ymm11, 63
	vpor ymm9, ymm9, ymm10
	vpxor ymm9, ymm9, ymm14
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpxor ymm0, ymm0, ymm5
	vmovdqu ymm1, YMMWORD PTR [rdi+192]
	vpxor ymm1, ymm1, ymm6
	vpsllq ymm10, ymm1, 44
	vpsrlq ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+384]
	vpxor ymm2, ymm2, ymm7
	vpsllq ymm10, ymm2, 43
	vpsrlq ymm2, ymm2, 21
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+576]
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm10, ymm3, 21
	vpsrlq ymm3, ymm3, 43
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+768]
	vpxor ymm4, ymm4, ymm9
	vpsllq ymm10, ymm4, 14
	vpsrlq ymm4, ymm4, 50
	vpor ymm4, ymm4, ymm10
	vpandn ymm11, ymm1, ymm2
	vpxor ymm11, ymm11, ymm0
	vpxor ymm11, ymm11, YMMWORD PTR [rdx]
	vmovdqu YMMWORD PTR [rsi], ymm11
	vpandn ymm12, ymm2, ymm3
	vpxor ymm12, ymm12, ymm1
	vmovdqu YMMWORD PTR [rsi+32], ymm12
	vpandn ymm13, ymm3, ymm4
	vpxor ymm13, ymm13, ymm2
	vmovdqu YMMWORD PTR [rsi+64], ymm13
	vpandn ymm14, ymm4, ymm0
	vpxor ymm14, ymm14, ymm3
	vmovdqu YMMWORD PTR [rsi+96], ymm14
	vpandn ymm15, ymm0, ymm1
	vpxor ymm15, ymm15, ymm4
	vmovdqu YMMWORD PTR [rsi+128], ymm15
	vmovdqu ymm0, YMMWORD PTR [rdi+96]
	vpxor ymm0, ymm0, ymm8
	vpsllq ymm10, ymm0, 28
	vpsrlq ymm0, ymm0, 36
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+288]
	vpxor ymm1, ymm1, ymm9
	vpsllq ymm10, ymm1, 20
	vpsrlq ymm1, ymm1, 44
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+320]
	vpxor ymm2, ymm2, ymm5
	vpsllq ymm10, ymm2, 3
	vpsrlq ymm2, ymm2, 61
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+512]
	vpxor ymm3, ymm3, ymm6
	vpsllq ymm10, ymm3, 45
	vpsrlq ymm3, ymm3, 19
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+704]
	vpxor ymm4, ymm4, ymm7
	vpsllq ymm10, ymm4, 61
	vpsrlq ymm4, ymm4, 3
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+160], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+192], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+224], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+256], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+288], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+32]
	vpxor ymm0, ymm0, ymm6
	vpsllq ymm10, ymm0, 1
	vpsrlq ymm0, ymm0, 63
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+224]
	vpxor ymm1, ymm1, ymm7
	vpsllq ymm10, ymm1, 6
	vpsrlq ymm1, ymm1, 58
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+416]
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm10, ymm2, 25
	vpsrlq ymm2, ymm2, 39
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+608]
	vpxor ymm3, ymm3, ymm9
	vpsllq ymm10, ymm3, 8
	vpsrlq ymm3, ymm3, 56
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+640]
	vpxor ymm4, ymm4, ymm5
	vpsllq ymm10, ymm4, 18
	vpsrlq ymm4, ymm4, 46
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+320], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+352], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+384], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+416], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+448], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+128]
	vpxor ymm0, ymm0, ymm9
	vpsllq ymm10, ymm0, 27
	vpsrlq ymm0, ymm0, 37
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+160]
	vpxor ymm1, ymm1, ymm5
	vpsllq ymm10, ymm1, 36
	vpsrlq ymm1, ymm1, 28
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+352]
	vpxor ymm2, ymm2, ymm6
	vpsllq ymm10, ymm2, 10
	vpsrlq ymm2, ymm2, 54
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+544]
	vpxor ymm3, ymm3, ymm7
	vpsllq ymm10, ymm3, 15
	vpsrlq ymm3, ymm3, 49
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+736]
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm10, ymm4, 56
	vpsrlq ymm4, ymm4, 8
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+480], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+512], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+544], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+576], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+608], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+64]
	vpxor ymm0, ymm0, ymm7
	vpsllq ymm10, ymm0, 62
	vpsrlq ymm0, ymm0, 2
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+256]
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm10, ymm1, 55
	vpsrlq ymm1, ymm1, 9
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+448]
	vpxor ymm2, ymm2, ymm9
	vpsllq ymm10, ymm2, 39
	vpsrlq ymm2, ymm2, 25
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+480]
	vpxor ymm3, ymm3, ymm5
	vpsllq ymm10, ymm3, 41
	vpsrlq ymm3, ymm3, 23
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+672]
	vpxor ymm4, ymm4, ymm6
	vpsllq ymm10, ymm4, 2
	vpsrlq ymm4, ymm4, 62
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+640], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+672], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+704], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+736], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+768], ymm10
	vpxor ymm15, ymm15, ymm10
	mov rax, rdi
	mov rdi, rsi
	mov rsi, rax
	add rdx, 32
	cmp rdx, rcx
	jne 2112b
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
	jne 2111b
	lea r11, {VG_MLKEM_SAMPLE_TBL}
	mov rsi, rbx
	add rsi, 2368
	mov rdi, QWORD PTR [rbx+4424]
	mov rbp, r13
	add rbp, 0
	mov r10d, 14
	vmovdqu ymm8, YMMWORD PTR [r11+4096]
	vmovdqu ymm9, YMMWORD PTR [r11+4128]
	vmovdqu ymm10, YMMWORD PTR [r11+4160]
2113:
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
	sub r10, 1
	jne 2113b
	mov QWORD PTR [rbx+4424], rdi
	mov rsi, rbx
	add rsi, 2872
	mov rdi, QWORD PTR [rbx+4432]
	mov rbp, r13
	add rbp, 512
	mov r10d, 14
	vmovdqu ymm8, YMMWORD PTR [r11+4096]
	vmovdqu ymm9, YMMWORD PTR [r11+4128]
	vmovdqu ymm10, YMMWORD PTR [r11+4160]
2123:
	cmp rdi, 241
	jb 2124f
	cmp rdi, 256
	jb 2126f
	add rsi, 24
	jmp 2127f
2126:
	mov ecx, 8
2128:
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
	jb 2129f
	jmp 2130f
2129:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2131f
	jmp 2132f
2131:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2132:
2130:
	add rsi, 3
	sub rcx, 1
	jne 2128b
2127:
	jmp 2125f
2124:
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
2125:
	sub r10, 1
	jne 2123b
	mov QWORD PTR [rbx+4432], rdi
	mov rsi, rbx
	add rsi, 3376
	mov rdi, QWORD PTR [rbx+4440]
	mov rbp, r13
	add rbp, 1024
	mov r10d, 14
	vmovdqu ymm8, YMMWORD PTR [r11+4096]
	vmovdqu ymm9, YMMWORD PTR [r11+4128]
	vmovdqu ymm10, YMMWORD PTR [r11+4160]
2133:
	cmp rdi, 241
	jb 2134f
	cmp rdi, 256
	jb 2136f
	add rsi, 24
	jmp 2137f
2136:
	mov ecx, 8
2138:
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
	jb 2139f
	jmp 2140f
2139:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2141f
	jmp 2142f
2141:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2142:
2140:
	add rsi, 3
	sub rcx, 1
	jne 2138b
2137:
	jmp 2135f
2134:
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
2135:
	sub r10, 1
	jne 2133b
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
2110:
	vzeroupper
	mov eax, r14d
	mov r14, QWORD PTR [rbx+4416]
	mov r13, QWORD PTR [rbx+4408]
	mov r12, QWORD PTR [rbx+4400]
	mov rbp, QWORD PTR [rbx+4392]
	mov rbx, QWORD PTR [rbx+4384]
	and r15d, eax
	mov rdi, rbx
	add rdi, 19208
	mov rsi, r14
	add rsi, 816
	mov ecx, 46
2143:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2143b
	mov eax, 0
	mov QWORD PTR [rbx+19576], rax
	mov QWORD PTR [rbx+19584], rax
	mov QWORD PTR [rbx+19592], rax
	mov QWORD PTR [rbx+19600], rax
	mov QWORD PTR [rbx+19608], rax
	mov eax, 6
	mov BYTE PTR [rbx+19576], al
	mov eax, 128
	mov BYTE PTR [rbx+19615], al
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
2144:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2144b
	mov eax, 0
	mov BYTE PTR [rbx+32], al
	mov eax, 2
	mov BYTE PTR [rbx+33], al
	mov rdi, rbx
	add rdi, 34
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
2145:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2145b
	mov eax, 1
	mov BYTE PTR [rbx+66], al
	mov eax, 2
	mov BYTE PTR [rbx+67], al
	mov rdi, rbx
	add rdi, 68
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
2146:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2146b
	mov eax, 2
	mov BYTE PTR [rbx+100], al
	mov eax, 2
	mov BYTE PTR [rbx+101], al
	mov rdi, rbx
	add rdi, 102
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
2147:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2147b
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
2148:
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
	vmovdqu ymm11, YMMWORD PTR [rdi]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+160]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+320]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+480]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+640]
	vmovdqu ymm12, YMMWORD PTR [rdi+32]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+192]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+352]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+512]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+672]
	vmovdqu ymm13, YMMWORD PTR [rdi+64]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+224]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+384]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+544]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+704]
	vmovdqu ymm14, YMMWORD PTR [rdi+96]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+256]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+416]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+576]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+736]
	vmovdqu ymm15, YMMWORD PTR [rdi+128]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+288]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+448]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+608]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+768]
2149:
	vpsllq ymm10, ymm12, 1
	vpsrlq ymm5, ymm12, 63
	vpor ymm5, ymm5, ymm10
	vpxor ymm5, ymm5, ymm15
	vpsllq ymm10, ymm13, 1
	vpsrlq ymm6, ymm13, 63
	vpor ymm6, ymm6, ymm10
	vpxor ymm6, ymm6, ymm11
	vpsllq ymm10, ymm14, 1
	vpsrlq ymm7, ymm14, 63
	vpor ymm7, ymm7, ymm10
	vpxor ymm7, ymm7, ymm12
	vpsllq ymm10, ymm15, 1
	vpsrlq ymm8, ymm15, 63
	vpor ymm8, ymm8, ymm10
	vpxor ymm8, ymm8, ymm13
	vpsllq ymm10, ymm11, 1
	vpsrlq ymm9, ymm11, 63
	vpor ymm9, ymm9, ymm10
	vpxor ymm9, ymm9, ymm14
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpxor ymm0, ymm0, ymm5
	vmovdqu ymm1, YMMWORD PTR [rdi+192]
	vpxor ymm1, ymm1, ymm6
	vpsllq ymm10, ymm1, 44
	vpsrlq ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+384]
	vpxor ymm2, ymm2, ymm7
	vpsllq ymm10, ymm2, 43
	vpsrlq ymm2, ymm2, 21
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+576]
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm10, ymm3, 21
	vpsrlq ymm3, ymm3, 43
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+768]
	vpxor ymm4, ymm4, ymm9
	vpsllq ymm10, ymm4, 14
	vpsrlq ymm4, ymm4, 50
	vpor ymm4, ymm4, ymm10
	vpandn ymm11, ymm1, ymm2
	vpxor ymm11, ymm11, ymm0
	vpxor ymm11, ymm11, YMMWORD PTR [rdx]
	vmovdqu YMMWORD PTR [rsi], ymm11
	vpandn ymm12, ymm2, ymm3
	vpxor ymm12, ymm12, ymm1
	vmovdqu YMMWORD PTR [rsi+32], ymm12
	vpandn ymm13, ymm3, ymm4
	vpxor ymm13, ymm13, ymm2
	vmovdqu YMMWORD PTR [rsi+64], ymm13
	vpandn ymm14, ymm4, ymm0
	vpxor ymm14, ymm14, ymm3
	vmovdqu YMMWORD PTR [rsi+96], ymm14
	vpandn ymm15, ymm0, ymm1
	vpxor ymm15, ymm15, ymm4
	vmovdqu YMMWORD PTR [rsi+128], ymm15
	vmovdqu ymm0, YMMWORD PTR [rdi+96]
	vpxor ymm0, ymm0, ymm8
	vpsllq ymm10, ymm0, 28
	vpsrlq ymm0, ymm0, 36
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+288]
	vpxor ymm1, ymm1, ymm9
	vpsllq ymm10, ymm1, 20
	vpsrlq ymm1, ymm1, 44
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+320]
	vpxor ymm2, ymm2, ymm5
	vpsllq ymm10, ymm2, 3
	vpsrlq ymm2, ymm2, 61
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+512]
	vpxor ymm3, ymm3, ymm6
	vpsllq ymm10, ymm3, 45
	vpsrlq ymm3, ymm3, 19
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+704]
	vpxor ymm4, ymm4, ymm7
	vpsllq ymm10, ymm4, 61
	vpsrlq ymm4, ymm4, 3
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+160], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+192], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+224], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+256], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+288], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+32]
	vpxor ymm0, ymm0, ymm6
	vpsllq ymm10, ymm0, 1
	vpsrlq ymm0, ymm0, 63
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+224]
	vpxor ymm1, ymm1, ymm7
	vpsllq ymm10, ymm1, 6
	vpsrlq ymm1, ymm1, 58
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+416]
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm10, ymm2, 25
	vpsrlq ymm2, ymm2, 39
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+608]
	vpxor ymm3, ymm3, ymm9
	vpsllq ymm10, ymm3, 8
	vpsrlq ymm3, ymm3, 56
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+640]
	vpxor ymm4, ymm4, ymm5
	vpsllq ymm10, ymm4, 18
	vpsrlq ymm4, ymm4, 46
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+320], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+352], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+384], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+416], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+448], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+128]
	vpxor ymm0, ymm0, ymm9
	vpsllq ymm10, ymm0, 27
	vpsrlq ymm0, ymm0, 37
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+160]
	vpxor ymm1, ymm1, ymm5
	vpsllq ymm10, ymm1, 36
	vpsrlq ymm1, ymm1, 28
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+352]
	vpxor ymm2, ymm2, ymm6
	vpsllq ymm10, ymm2, 10
	vpsrlq ymm2, ymm2, 54
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+544]
	vpxor ymm3, ymm3, ymm7
	vpsllq ymm10, ymm3, 15
	vpsrlq ymm3, ymm3, 49
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+736]
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm10, ymm4, 56
	vpsrlq ymm4, ymm4, 8
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+480], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+512], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+544], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+576], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+608], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+64]
	vpxor ymm0, ymm0, ymm7
	vpsllq ymm10, ymm0, 62
	vpsrlq ymm0, ymm0, 2
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+256]
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm10, ymm1, 55
	vpsrlq ymm1, ymm1, 9
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+448]
	vpxor ymm2, ymm2, ymm9
	vpsllq ymm10, ymm2, 39
	vpsrlq ymm2, ymm2, 25
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+480]
	vpxor ymm3, ymm3, ymm5
	vpsllq ymm10, ymm3, 41
	vpsrlq ymm3, ymm3, 23
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+672]
	vpxor ymm4, ymm4, ymm6
	vpsllq ymm10, ymm4, 2
	vpsrlq ymm4, ymm4, 62
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+640], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+672], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+704], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+736], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+768], ymm10
	vpxor ymm15, ymm15, ymm10
	mov rax, rdi
	mov rdi, rsi
	mov rsi, rax
	add rdx, 32
	cmp rdx, rcx
	vpsllq ymm10, ymm12, 1
	vpsrlq ymm5, ymm12, 63
	vpor ymm5, ymm5, ymm10
	vpxor ymm5, ymm5, ymm15
	vpsllq ymm10, ymm13, 1
	vpsrlq ymm6, ymm13, 63
	vpor ymm6, ymm6, ymm10
	vpxor ymm6, ymm6, ymm11
	vpsllq ymm10, ymm14, 1
	vpsrlq ymm7, ymm14, 63
	vpor ymm7, ymm7, ymm10
	vpxor ymm7, ymm7, ymm12
	vpsllq ymm10, ymm15, 1
	vpsrlq ymm8, ymm15, 63
	vpor ymm8, ymm8, ymm10
	vpxor ymm8, ymm8, ymm13
	vpsllq ymm10, ymm11, 1
	vpsrlq ymm9, ymm11, 63
	vpor ymm9, ymm9, ymm10
	vpxor ymm9, ymm9, ymm14
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpxor ymm0, ymm0, ymm5
	vmovdqu ymm1, YMMWORD PTR [rdi+192]
	vpxor ymm1, ymm1, ymm6
	vpsllq ymm10, ymm1, 44
	vpsrlq ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+384]
	vpxor ymm2, ymm2, ymm7
	vpsllq ymm10, ymm2, 43
	vpsrlq ymm2, ymm2, 21
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+576]
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm10, ymm3, 21
	vpsrlq ymm3, ymm3, 43
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+768]
	vpxor ymm4, ymm4, ymm9
	vpsllq ymm10, ymm4, 14
	vpsrlq ymm4, ymm4, 50
	vpor ymm4, ymm4, ymm10
	vpandn ymm11, ymm1, ymm2
	vpxor ymm11, ymm11, ymm0
	vpxor ymm11, ymm11, YMMWORD PTR [rdx]
	vmovdqu YMMWORD PTR [rsi], ymm11
	vpandn ymm12, ymm2, ymm3
	vpxor ymm12, ymm12, ymm1
	vmovdqu YMMWORD PTR [rsi+32], ymm12
	vpandn ymm13, ymm3, ymm4
	vpxor ymm13, ymm13, ymm2
	vmovdqu YMMWORD PTR [rsi+64], ymm13
	vpandn ymm14, ymm4, ymm0
	vpxor ymm14, ymm14, ymm3
	vmovdqu YMMWORD PTR [rsi+96], ymm14
	vpandn ymm15, ymm0, ymm1
	vpxor ymm15, ymm15, ymm4
	vmovdqu YMMWORD PTR [rsi+128], ymm15
	vmovdqu ymm0, YMMWORD PTR [rdi+96]
	vpxor ymm0, ymm0, ymm8
	vpsllq ymm10, ymm0, 28
	vpsrlq ymm0, ymm0, 36
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+288]
	vpxor ymm1, ymm1, ymm9
	vpsllq ymm10, ymm1, 20
	vpsrlq ymm1, ymm1, 44
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+320]
	vpxor ymm2, ymm2, ymm5
	vpsllq ymm10, ymm2, 3
	vpsrlq ymm2, ymm2, 61
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+512]
	vpxor ymm3, ymm3, ymm6
	vpsllq ymm10, ymm3, 45
	vpsrlq ymm3, ymm3, 19
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+704]
	vpxor ymm4, ymm4, ymm7
	vpsllq ymm10, ymm4, 61
	vpsrlq ymm4, ymm4, 3
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+160], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+192], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+224], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+256], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+288], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+32]
	vpxor ymm0, ymm0, ymm6
	vpsllq ymm10, ymm0, 1
	vpsrlq ymm0, ymm0, 63
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+224]
	vpxor ymm1, ymm1, ymm7
	vpsllq ymm10, ymm1, 6
	vpsrlq ymm1, ymm1, 58
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+416]
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm10, ymm2, 25
	vpsrlq ymm2, ymm2, 39
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+608]
	vpxor ymm3, ymm3, ymm9
	vpsllq ymm10, ymm3, 8
	vpsrlq ymm3, ymm3, 56
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+640]
	vpxor ymm4, ymm4, ymm5
	vpsllq ymm10, ymm4, 18
	vpsrlq ymm4, ymm4, 46
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+320], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+352], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+384], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+416], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+448], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+128]
	vpxor ymm0, ymm0, ymm9
	vpsllq ymm10, ymm0, 27
	vpsrlq ymm0, ymm0, 37
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+160]
	vpxor ymm1, ymm1, ymm5
	vpsllq ymm10, ymm1, 36
	vpsrlq ymm1, ymm1, 28
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+352]
	vpxor ymm2, ymm2, ymm6
	vpsllq ymm10, ymm2, 10
	vpsrlq ymm2, ymm2, 54
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+544]
	vpxor ymm3, ymm3, ymm7
	vpsllq ymm10, ymm3, 15
	vpsrlq ymm3, ymm3, 49
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+736]
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm10, ymm4, 56
	vpsrlq ymm4, ymm4, 8
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+480], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+512], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+544], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+576], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+608], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+64]
	vpxor ymm0, ymm0, ymm7
	vpsllq ymm10, ymm0, 62
	vpsrlq ymm0, ymm0, 2
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+256]
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm10, ymm1, 55
	vpsrlq ymm1, ymm1, 9
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+448]
	vpxor ymm2, ymm2, ymm9
	vpsllq ymm10, ymm2, 39
	vpsrlq ymm2, ymm2, 25
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+480]
	vpxor ymm3, ymm3, ymm5
	vpsllq ymm10, ymm3, 41
	vpsrlq ymm3, ymm3, 23
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+672]
	vpxor ymm4, ymm4, ymm6
	vpsllq ymm10, ymm4, 2
	vpsrlq ymm4, ymm4, 62
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+640], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+672], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+704], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+736], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+768], ymm10
	vpxor ymm15, ymm15, ymm10
	mov rax, rdi
	mov rdi, rsi
	mov rsi, rax
	add rdx, 32
	cmp rdx, rcx
	jne 2149b
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
	jne 2148b
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
	mov r10d, 21
	vmovdqu ymm8, YMMWORD PTR [r11+4096]
	vmovdqu ymm9, YMMWORD PTR [r11+4128]
	vmovdqu ymm10, YMMWORD PTR [r11+4160]
2150:
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
	sub r10, 1
	jne 2150b
	mov QWORD PTR [rbx+4424], rdi
	mov rsi, rbx
	add rsi, 2872
	mov edi, 0
	mov rbp, r13
	add rbp, 512
	mov r10d, 21
	vmovdqu ymm8, YMMWORD PTR [r11+4096]
	vmovdqu ymm9, YMMWORD PTR [r11+4128]
	vmovdqu ymm10, YMMWORD PTR [r11+4160]
2160:
	cmp rdi, 241
	jb 2161f
	cmp rdi, 256
	jb 2163f
	add rsi, 24
	jmp 2164f
2163:
	mov ecx, 8
2165:
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
	jb 2166f
	jmp 2167f
2166:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2168f
	jmp 2169f
2168:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2169:
2167:
	add rsi, 3
	sub rcx, 1
	jne 2165b
2164:
	jmp 2162f
2161:
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
2162:
	sub r10, 1
	jne 2160b
	mov QWORD PTR [rbx+4432], rdi
	mov rsi, rbx
	add rsi, 3376
	mov edi, 0
	mov rbp, r13
	add rbp, 1024
	mov r10d, 21
	vmovdqu ymm8, YMMWORD PTR [r11+4096]
	vmovdqu ymm9, YMMWORD PTR [r11+4128]
	vmovdqu ymm10, YMMWORD PTR [r11+4160]
2170:
	cmp rdi, 241
	jb 2171f
	cmp rdi, 256
	jb 2173f
	add rsi, 24
	jmp 2174f
2173:
	mov ecx, 8
2175:
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
	jb 2176f
	jmp 2177f
2176:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2178f
	jmp 2179f
2178:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2179:
2177:
	add rsi, 3
	sub rcx, 1
	jne 2175b
2174:
	jmp 2172f
2171:
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
2172:
	sub r10, 1
	jne 2170b
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
	je 2180f
	jmp 2181f
2180:
	mov r14d, 1
	mov rbp, rbx
	add rbp, 2368
	mov r10d, 2
2182:
	mov rdi, rbx
	mov rsi, rbx
	add rsi, 800
	mov rdx, rbx
	add rdx, 1600
	mov rcx, rbx
	add rcx, 2368
	vmovdqu ymm11, YMMWORD PTR [rdi]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+160]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+320]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+480]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+640]
	vmovdqu ymm12, YMMWORD PTR [rdi+32]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+192]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+352]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+512]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+672]
	vmovdqu ymm13, YMMWORD PTR [rdi+64]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+224]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+384]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+544]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+704]
	vmovdqu ymm14, YMMWORD PTR [rdi+96]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+256]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+416]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+576]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+736]
	vmovdqu ymm15, YMMWORD PTR [rdi+128]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+288]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+448]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+608]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+768]
2183:
	vpsllq ymm10, ymm12, 1
	vpsrlq ymm5, ymm12, 63
	vpor ymm5, ymm5, ymm10
	vpxor ymm5, ymm5, ymm15
	vpsllq ymm10, ymm13, 1
	vpsrlq ymm6, ymm13, 63
	vpor ymm6, ymm6, ymm10
	vpxor ymm6, ymm6, ymm11
	vpsllq ymm10, ymm14, 1
	vpsrlq ymm7, ymm14, 63
	vpor ymm7, ymm7, ymm10
	vpxor ymm7, ymm7, ymm12
	vpsllq ymm10, ymm15, 1
	vpsrlq ymm8, ymm15, 63
	vpor ymm8, ymm8, ymm10
	vpxor ymm8, ymm8, ymm13
	vpsllq ymm10, ymm11, 1
	vpsrlq ymm9, ymm11, 63
	vpor ymm9, ymm9, ymm10
	vpxor ymm9, ymm9, ymm14
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpxor ymm0, ymm0, ymm5
	vmovdqu ymm1, YMMWORD PTR [rdi+192]
	vpxor ymm1, ymm1, ymm6
	vpsllq ymm10, ymm1, 44
	vpsrlq ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+384]
	vpxor ymm2, ymm2, ymm7
	vpsllq ymm10, ymm2, 43
	vpsrlq ymm2, ymm2, 21
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+576]
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm10, ymm3, 21
	vpsrlq ymm3, ymm3, 43
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+768]
	vpxor ymm4, ymm4, ymm9
	vpsllq ymm10, ymm4, 14
	vpsrlq ymm4, ymm4, 50
	vpor ymm4, ymm4, ymm10
	vpandn ymm11, ymm1, ymm2
	vpxor ymm11, ymm11, ymm0
	vpxor ymm11, ymm11, YMMWORD PTR [rdx]
	vmovdqu YMMWORD PTR [rsi], ymm11
	vpandn ymm12, ymm2, ymm3
	vpxor ymm12, ymm12, ymm1
	vmovdqu YMMWORD PTR [rsi+32], ymm12
	vpandn ymm13, ymm3, ymm4
	vpxor ymm13, ymm13, ymm2
	vmovdqu YMMWORD PTR [rsi+64], ymm13
	vpandn ymm14, ymm4, ymm0
	vpxor ymm14, ymm14, ymm3
	vmovdqu YMMWORD PTR [rsi+96], ymm14
	vpandn ymm15, ymm0, ymm1
	vpxor ymm15, ymm15, ymm4
	vmovdqu YMMWORD PTR [rsi+128], ymm15
	vmovdqu ymm0, YMMWORD PTR [rdi+96]
	vpxor ymm0, ymm0, ymm8
	vpsllq ymm10, ymm0, 28
	vpsrlq ymm0, ymm0, 36
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+288]
	vpxor ymm1, ymm1, ymm9
	vpsllq ymm10, ymm1, 20
	vpsrlq ymm1, ymm1, 44
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+320]
	vpxor ymm2, ymm2, ymm5
	vpsllq ymm10, ymm2, 3
	vpsrlq ymm2, ymm2, 61
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+512]
	vpxor ymm3, ymm3, ymm6
	vpsllq ymm10, ymm3, 45
	vpsrlq ymm3, ymm3, 19
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+704]
	vpxor ymm4, ymm4, ymm7
	vpsllq ymm10, ymm4, 61
	vpsrlq ymm4, ymm4, 3
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+160], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+192], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+224], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+256], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+288], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+32]
	vpxor ymm0, ymm0, ymm6
	vpsllq ymm10, ymm0, 1
	vpsrlq ymm0, ymm0, 63
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+224]
	vpxor ymm1, ymm1, ymm7
	vpsllq ymm10, ymm1, 6
	vpsrlq ymm1, ymm1, 58
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+416]
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm10, ymm2, 25
	vpsrlq ymm2, ymm2, 39
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+608]
	vpxor ymm3, ymm3, ymm9
	vpsllq ymm10, ymm3, 8
	vpsrlq ymm3, ymm3, 56
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+640]
	vpxor ymm4, ymm4, ymm5
	vpsllq ymm10, ymm4, 18
	vpsrlq ymm4, ymm4, 46
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+320], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+352], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+384], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+416], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+448], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+128]
	vpxor ymm0, ymm0, ymm9
	vpsllq ymm10, ymm0, 27
	vpsrlq ymm0, ymm0, 37
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+160]
	vpxor ymm1, ymm1, ymm5
	vpsllq ymm10, ymm1, 36
	vpsrlq ymm1, ymm1, 28
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+352]
	vpxor ymm2, ymm2, ymm6
	vpsllq ymm10, ymm2, 10
	vpsrlq ymm2, ymm2, 54
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+544]
	vpxor ymm3, ymm3, ymm7
	vpsllq ymm10, ymm3, 15
	vpsrlq ymm3, ymm3, 49
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+736]
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm10, ymm4, 56
	vpsrlq ymm4, ymm4, 8
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+480], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+512], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+544], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+576], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+608], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+64]
	vpxor ymm0, ymm0, ymm7
	vpsllq ymm10, ymm0, 62
	vpsrlq ymm0, ymm0, 2
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+256]
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm10, ymm1, 55
	vpsrlq ymm1, ymm1, 9
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+448]
	vpxor ymm2, ymm2, ymm9
	vpsllq ymm10, ymm2, 39
	vpsrlq ymm2, ymm2, 25
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+480]
	vpxor ymm3, ymm3, ymm5
	vpsllq ymm10, ymm3, 41
	vpsrlq ymm3, ymm3, 23
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+672]
	vpxor ymm4, ymm4, ymm6
	vpsllq ymm10, ymm4, 2
	vpsrlq ymm4, ymm4, 62
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+640], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+672], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+704], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+736], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+768], ymm10
	vpxor ymm15, ymm15, ymm10
	mov rax, rdi
	mov rdi, rsi
	mov rsi, rax
	add rdx, 32
	cmp rdx, rcx
	vpsllq ymm10, ymm12, 1
	vpsrlq ymm5, ymm12, 63
	vpor ymm5, ymm5, ymm10
	vpxor ymm5, ymm5, ymm15
	vpsllq ymm10, ymm13, 1
	vpsrlq ymm6, ymm13, 63
	vpor ymm6, ymm6, ymm10
	vpxor ymm6, ymm6, ymm11
	vpsllq ymm10, ymm14, 1
	vpsrlq ymm7, ymm14, 63
	vpor ymm7, ymm7, ymm10
	vpxor ymm7, ymm7, ymm12
	vpsllq ymm10, ymm15, 1
	vpsrlq ymm8, ymm15, 63
	vpor ymm8, ymm8, ymm10
	vpxor ymm8, ymm8, ymm13
	vpsllq ymm10, ymm11, 1
	vpsrlq ymm9, ymm11, 63
	vpor ymm9, ymm9, ymm10
	vpxor ymm9, ymm9, ymm14
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpxor ymm0, ymm0, ymm5
	vmovdqu ymm1, YMMWORD PTR [rdi+192]
	vpxor ymm1, ymm1, ymm6
	vpsllq ymm10, ymm1, 44
	vpsrlq ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+384]
	vpxor ymm2, ymm2, ymm7
	vpsllq ymm10, ymm2, 43
	vpsrlq ymm2, ymm2, 21
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+576]
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm10, ymm3, 21
	vpsrlq ymm3, ymm3, 43
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+768]
	vpxor ymm4, ymm4, ymm9
	vpsllq ymm10, ymm4, 14
	vpsrlq ymm4, ymm4, 50
	vpor ymm4, ymm4, ymm10
	vpandn ymm11, ymm1, ymm2
	vpxor ymm11, ymm11, ymm0
	vpxor ymm11, ymm11, YMMWORD PTR [rdx]
	vmovdqu YMMWORD PTR [rsi], ymm11
	vpandn ymm12, ymm2, ymm3
	vpxor ymm12, ymm12, ymm1
	vmovdqu YMMWORD PTR [rsi+32], ymm12
	vpandn ymm13, ymm3, ymm4
	vpxor ymm13, ymm13, ymm2
	vmovdqu YMMWORD PTR [rsi+64], ymm13
	vpandn ymm14, ymm4, ymm0
	vpxor ymm14, ymm14, ymm3
	vmovdqu YMMWORD PTR [rsi+96], ymm14
	vpandn ymm15, ymm0, ymm1
	vpxor ymm15, ymm15, ymm4
	vmovdqu YMMWORD PTR [rsi+128], ymm15
	vmovdqu ymm0, YMMWORD PTR [rdi+96]
	vpxor ymm0, ymm0, ymm8
	vpsllq ymm10, ymm0, 28
	vpsrlq ymm0, ymm0, 36
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+288]
	vpxor ymm1, ymm1, ymm9
	vpsllq ymm10, ymm1, 20
	vpsrlq ymm1, ymm1, 44
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+320]
	vpxor ymm2, ymm2, ymm5
	vpsllq ymm10, ymm2, 3
	vpsrlq ymm2, ymm2, 61
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+512]
	vpxor ymm3, ymm3, ymm6
	vpsllq ymm10, ymm3, 45
	vpsrlq ymm3, ymm3, 19
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+704]
	vpxor ymm4, ymm4, ymm7
	vpsllq ymm10, ymm4, 61
	vpsrlq ymm4, ymm4, 3
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+160], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+192], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+224], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+256], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+288], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+32]
	vpxor ymm0, ymm0, ymm6
	vpsllq ymm10, ymm0, 1
	vpsrlq ymm0, ymm0, 63
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+224]
	vpxor ymm1, ymm1, ymm7
	vpsllq ymm10, ymm1, 6
	vpsrlq ymm1, ymm1, 58
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+416]
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm10, ymm2, 25
	vpsrlq ymm2, ymm2, 39
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+608]
	vpxor ymm3, ymm3, ymm9
	vpsllq ymm10, ymm3, 8
	vpsrlq ymm3, ymm3, 56
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+640]
	vpxor ymm4, ymm4, ymm5
	vpsllq ymm10, ymm4, 18
	vpsrlq ymm4, ymm4, 46
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+320], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+352], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+384], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+416], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+448], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+128]
	vpxor ymm0, ymm0, ymm9
	vpsllq ymm10, ymm0, 27
	vpsrlq ymm0, ymm0, 37
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+160]
	vpxor ymm1, ymm1, ymm5
	vpsllq ymm10, ymm1, 36
	vpsrlq ymm1, ymm1, 28
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+352]
	vpxor ymm2, ymm2, ymm6
	vpsllq ymm10, ymm2, 10
	vpsrlq ymm2, ymm2, 54
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+544]
	vpxor ymm3, ymm3, ymm7
	vpsllq ymm10, ymm3, 15
	vpsrlq ymm3, ymm3, 49
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+736]
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm10, ymm4, 56
	vpsrlq ymm4, ymm4, 8
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+480], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+512], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+544], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+576], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+608], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+64]
	vpxor ymm0, ymm0, ymm7
	vpsllq ymm10, ymm0, 62
	vpsrlq ymm0, ymm0, 2
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+256]
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm10, ymm1, 55
	vpsrlq ymm1, ymm1, 9
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+448]
	vpxor ymm2, ymm2, ymm9
	vpsllq ymm10, ymm2, 39
	vpsrlq ymm2, ymm2, 25
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+480]
	vpxor ymm3, ymm3, ymm5
	vpsllq ymm10, ymm3, 41
	vpsrlq ymm3, ymm3, 23
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+672]
	vpxor ymm4, ymm4, ymm6
	vpsllq ymm10, ymm4, 2
	vpsrlq ymm4, ymm4, 62
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+640], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+672], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+704], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+736], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+768], ymm10
	vpxor ymm15, ymm15, ymm10
	mov rax, rdi
	mov rdi, rsi
	mov rsi, rax
	add rdx, 32
	cmp rdx, rcx
	jne 2183b
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
	jne 2182b
	lea r11, {VG_MLKEM_SAMPLE_TBL}
	mov rsi, rbx
	add rsi, 2368
	mov rdi, QWORD PTR [rbx+4424]
	mov rbp, r13
	add rbp, 0
	mov r10d, 14
	vmovdqu ymm8, YMMWORD PTR [r11+4096]
	vmovdqu ymm9, YMMWORD PTR [r11+4128]
	vmovdqu ymm10, YMMWORD PTR [r11+4160]
2184:
	cmp rdi, 241
	jb 2185f
	cmp rdi, 256
	jb 2187f
	add rsi, 24
	jmp 2188f
2187:
	mov ecx, 8
2189:
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
	jb 2190f
	jmp 2191f
2190:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2192f
	jmp 2193f
2192:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2193:
2191:
	add rsi, 3
	sub rcx, 1
	jne 2189b
2188:
	jmp 2186f
2185:
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
2186:
	sub r10, 1
	jne 2184b
	mov QWORD PTR [rbx+4424], rdi
	mov rsi, rbx
	add rsi, 2872
	mov rdi, QWORD PTR [rbx+4432]
	mov rbp, r13
	add rbp, 512
	mov r10d, 14
	vmovdqu ymm8, YMMWORD PTR [r11+4096]
	vmovdqu ymm9, YMMWORD PTR [r11+4128]
	vmovdqu ymm10, YMMWORD PTR [r11+4160]
2194:
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
	sub r10, 1
	jne 2194b
	mov QWORD PTR [rbx+4432], rdi
	mov rsi, rbx
	add rsi, 3376
	mov rdi, QWORD PTR [rbx+4440]
	mov rbp, r13
	add rbp, 1024
	mov r10d, 14
	vmovdqu ymm8, YMMWORD PTR [r11+4096]
	vmovdqu ymm9, YMMWORD PTR [r11+4128]
	vmovdqu ymm10, YMMWORD PTR [r11+4160]
2204:
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
	sub r10, 1
	jne 2204b
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
2181:
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
	add rsi, 19008
	mov ecx, 4
2214:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2214b
	mov rdi, rbx
	add rdi, 1248
	mov rsi, rbp
	add rsi, 0
	mov ecx, 4
2215:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2215b
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
	jne 2216f
	jmp 2217f
2216:
	mov r8, rbx
	add r8, 20480
	mov r9d, 0
	mov r10d, 1
2218:
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
	vmovdqu ymm11, YMMWORD PTR [rdi]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+160]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+320]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+480]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+640]
	vmovdqu ymm12, YMMWORD PTR [rdi+32]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+192]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+352]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+512]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+672]
	vmovdqu ymm13, YMMWORD PTR [rdi+64]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+224]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+384]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+544]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+704]
	vmovdqu ymm14, YMMWORD PTR [rdi+96]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+256]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+416]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+576]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+736]
	vmovdqu ymm15, YMMWORD PTR [rdi+128]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+288]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+448]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+608]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+768]
2219:
	vpsllq ymm10, ymm12, 1
	vpsrlq ymm5, ymm12, 63
	vpor ymm5, ymm5, ymm10
	vpxor ymm5, ymm5, ymm15
	vpsllq ymm10, ymm13, 1
	vpsrlq ymm6, ymm13, 63
	vpor ymm6, ymm6, ymm10
	vpxor ymm6, ymm6, ymm11
	vpsllq ymm10, ymm14, 1
	vpsrlq ymm7, ymm14, 63
	vpor ymm7, ymm7, ymm10
	vpxor ymm7, ymm7, ymm12
	vpsllq ymm10, ymm15, 1
	vpsrlq ymm8, ymm15, 63
	vpor ymm8, ymm8, ymm10
	vpxor ymm8, ymm8, ymm13
	vpsllq ymm10, ymm11, 1
	vpsrlq ymm9, ymm11, 63
	vpor ymm9, ymm9, ymm10
	vpxor ymm9, ymm9, ymm14
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpxor ymm0, ymm0, ymm5
	vmovdqu ymm1, YMMWORD PTR [rdi+192]
	vpxor ymm1, ymm1, ymm6
	vpsllq ymm10, ymm1, 44
	vpsrlq ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+384]
	vpxor ymm2, ymm2, ymm7
	vpsllq ymm10, ymm2, 43
	vpsrlq ymm2, ymm2, 21
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+576]
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm10, ymm3, 21
	vpsrlq ymm3, ymm3, 43
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+768]
	vpxor ymm4, ymm4, ymm9
	vpsllq ymm10, ymm4, 14
	vpsrlq ymm4, ymm4, 50
	vpor ymm4, ymm4, ymm10
	vpandn ymm11, ymm1, ymm2
	vpxor ymm11, ymm11, ymm0
	vpxor ymm11, ymm11, YMMWORD PTR [rdx]
	vmovdqu YMMWORD PTR [rsi], ymm11
	vpandn ymm12, ymm2, ymm3
	vpxor ymm12, ymm12, ymm1
	vmovdqu YMMWORD PTR [rsi+32], ymm12
	vpandn ymm13, ymm3, ymm4
	vpxor ymm13, ymm13, ymm2
	vmovdqu YMMWORD PTR [rsi+64], ymm13
	vpandn ymm14, ymm4, ymm0
	vpxor ymm14, ymm14, ymm3
	vmovdqu YMMWORD PTR [rsi+96], ymm14
	vpandn ymm15, ymm0, ymm1
	vpxor ymm15, ymm15, ymm4
	vmovdqu YMMWORD PTR [rsi+128], ymm15
	vmovdqu ymm0, YMMWORD PTR [rdi+96]
	vpxor ymm0, ymm0, ymm8
	vpsllq ymm10, ymm0, 28
	vpsrlq ymm0, ymm0, 36
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+288]
	vpxor ymm1, ymm1, ymm9
	vpsllq ymm10, ymm1, 20
	vpsrlq ymm1, ymm1, 44
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+320]
	vpxor ymm2, ymm2, ymm5
	vpsllq ymm10, ymm2, 3
	vpsrlq ymm2, ymm2, 61
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+512]
	vpxor ymm3, ymm3, ymm6
	vpsllq ymm10, ymm3, 45
	vpsrlq ymm3, ymm3, 19
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+704]
	vpxor ymm4, ymm4, ymm7
	vpsllq ymm10, ymm4, 61
	vpsrlq ymm4, ymm4, 3
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+160], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+192], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+224], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+256], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+288], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+32]
	vpxor ymm0, ymm0, ymm6
	vpsllq ymm10, ymm0, 1
	vpsrlq ymm0, ymm0, 63
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+224]
	vpxor ymm1, ymm1, ymm7
	vpsllq ymm10, ymm1, 6
	vpsrlq ymm1, ymm1, 58
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+416]
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm10, ymm2, 25
	vpsrlq ymm2, ymm2, 39
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+608]
	vpxor ymm3, ymm3, ymm9
	vpsllq ymm10, ymm3, 8
	vpsrlq ymm3, ymm3, 56
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+640]
	vpxor ymm4, ymm4, ymm5
	vpsllq ymm10, ymm4, 18
	vpsrlq ymm4, ymm4, 46
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+320], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+352], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+384], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+416], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+448], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+128]
	vpxor ymm0, ymm0, ymm9
	vpsllq ymm10, ymm0, 27
	vpsrlq ymm0, ymm0, 37
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+160]
	vpxor ymm1, ymm1, ymm5
	vpsllq ymm10, ymm1, 36
	vpsrlq ymm1, ymm1, 28
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+352]
	vpxor ymm2, ymm2, ymm6
	vpsllq ymm10, ymm2, 10
	vpsrlq ymm2, ymm2, 54
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+544]
	vpxor ymm3, ymm3, ymm7
	vpsllq ymm10, ymm3, 15
	vpsrlq ymm3, ymm3, 49
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+736]
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm10, ymm4, 56
	vpsrlq ymm4, ymm4, 8
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+480], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+512], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+544], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+576], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+608], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+64]
	vpxor ymm0, ymm0, ymm7
	vpsllq ymm10, ymm0, 62
	vpsrlq ymm0, ymm0, 2
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+256]
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm10, ymm1, 55
	vpsrlq ymm1, ymm1, 9
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+448]
	vpxor ymm2, ymm2, ymm9
	vpsllq ymm10, ymm2, 39
	vpsrlq ymm2, ymm2, 25
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+480]
	vpxor ymm3, ymm3, ymm5
	vpsllq ymm10, ymm3, 41
	vpsrlq ymm3, ymm3, 23
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+672]
	vpxor ymm4, ymm4, ymm6
	vpsllq ymm10, ymm4, 2
	vpsrlq ymm4, ymm4, 62
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+640], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+672], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+704], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+736], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+768], ymm10
	vpxor ymm15, ymm15, ymm10
	mov rax, rdi
	mov rdi, rsi
	mov rsi, rax
	add rdx, 32
	cmp rdx, rcx
	vpsllq ymm10, ymm12, 1
	vpsrlq ymm5, ymm12, 63
	vpor ymm5, ymm5, ymm10
	vpxor ymm5, ymm5, ymm15
	vpsllq ymm10, ymm13, 1
	vpsrlq ymm6, ymm13, 63
	vpor ymm6, ymm6, ymm10
	vpxor ymm6, ymm6, ymm11
	vpsllq ymm10, ymm14, 1
	vpsrlq ymm7, ymm14, 63
	vpor ymm7, ymm7, ymm10
	vpxor ymm7, ymm7, ymm12
	vpsllq ymm10, ymm15, 1
	vpsrlq ymm8, ymm15, 63
	vpor ymm8, ymm8, ymm10
	vpxor ymm8, ymm8, ymm13
	vpsllq ymm10, ymm11, 1
	vpsrlq ymm9, ymm11, 63
	vpor ymm9, ymm9, ymm10
	vpxor ymm9, ymm9, ymm14
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpxor ymm0, ymm0, ymm5
	vmovdqu ymm1, YMMWORD PTR [rdi+192]
	vpxor ymm1, ymm1, ymm6
	vpsllq ymm10, ymm1, 44
	vpsrlq ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+384]
	vpxor ymm2, ymm2, ymm7
	vpsllq ymm10, ymm2, 43
	vpsrlq ymm2, ymm2, 21
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+576]
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm10, ymm3, 21
	vpsrlq ymm3, ymm3, 43
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+768]
	vpxor ymm4, ymm4, ymm9
	vpsllq ymm10, ymm4, 14
	vpsrlq ymm4, ymm4, 50
	vpor ymm4, ymm4, ymm10
	vpandn ymm11, ymm1, ymm2
	vpxor ymm11, ymm11, ymm0
	vpxor ymm11, ymm11, YMMWORD PTR [rdx]
	vmovdqu YMMWORD PTR [rsi], ymm11
	vpandn ymm12, ymm2, ymm3
	vpxor ymm12, ymm12, ymm1
	vmovdqu YMMWORD PTR [rsi+32], ymm12
	vpandn ymm13, ymm3, ymm4
	vpxor ymm13, ymm13, ymm2
	vmovdqu YMMWORD PTR [rsi+64], ymm13
	vpandn ymm14, ymm4, ymm0
	vpxor ymm14, ymm14, ymm3
	vmovdqu YMMWORD PTR [rsi+96], ymm14
	vpandn ymm15, ymm0, ymm1
	vpxor ymm15, ymm15, ymm4
	vmovdqu YMMWORD PTR [rsi+128], ymm15
	vmovdqu ymm0, YMMWORD PTR [rdi+96]
	vpxor ymm0, ymm0, ymm8
	vpsllq ymm10, ymm0, 28
	vpsrlq ymm0, ymm0, 36
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+288]
	vpxor ymm1, ymm1, ymm9
	vpsllq ymm10, ymm1, 20
	vpsrlq ymm1, ymm1, 44
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+320]
	vpxor ymm2, ymm2, ymm5
	vpsllq ymm10, ymm2, 3
	vpsrlq ymm2, ymm2, 61
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+512]
	vpxor ymm3, ymm3, ymm6
	vpsllq ymm10, ymm3, 45
	vpsrlq ymm3, ymm3, 19
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+704]
	vpxor ymm4, ymm4, ymm7
	vpsllq ymm10, ymm4, 61
	vpsrlq ymm4, ymm4, 3
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+160], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+192], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+224], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+256], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+288], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+32]
	vpxor ymm0, ymm0, ymm6
	vpsllq ymm10, ymm0, 1
	vpsrlq ymm0, ymm0, 63
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+224]
	vpxor ymm1, ymm1, ymm7
	vpsllq ymm10, ymm1, 6
	vpsrlq ymm1, ymm1, 58
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+416]
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm10, ymm2, 25
	vpsrlq ymm2, ymm2, 39
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+608]
	vpxor ymm3, ymm3, ymm9
	vpsllq ymm10, ymm3, 8
	vpsrlq ymm3, ymm3, 56
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+640]
	vpxor ymm4, ymm4, ymm5
	vpsllq ymm10, ymm4, 18
	vpsrlq ymm4, ymm4, 46
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+320], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+352], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+384], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+416], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+448], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+128]
	vpxor ymm0, ymm0, ymm9
	vpsllq ymm10, ymm0, 27
	vpsrlq ymm0, ymm0, 37
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+160]
	vpxor ymm1, ymm1, ymm5
	vpsllq ymm10, ymm1, 36
	vpsrlq ymm1, ymm1, 28
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+352]
	vpxor ymm2, ymm2, ymm6
	vpsllq ymm10, ymm2, 10
	vpsrlq ymm2, ymm2, 54
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+544]
	vpxor ymm3, ymm3, ymm7
	vpsllq ymm10, ymm3, 15
	vpsrlq ymm3, ymm3, 49
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+736]
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm10, ymm4, 56
	vpsrlq ymm4, ymm4, 8
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+480], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+512], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+544], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+576], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+608], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+64]
	vpxor ymm0, ymm0, ymm7
	vpsllq ymm10, ymm0, 62
	vpsrlq ymm0, ymm0, 2
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+256]
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm10, ymm1, 55
	vpsrlq ymm1, ymm1, 9
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+448]
	vpxor ymm2, ymm2, ymm9
	vpsllq ymm10, ymm2, 39
	vpsrlq ymm2, ymm2, 25
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+480]
	vpxor ymm3, ymm3, ymm5
	vpsllq ymm10, ymm3, 41
	vpsrlq ymm3, ymm3, 23
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+672]
	vpxor ymm4, ymm4, ymm6
	vpsllq ymm10, ymm4, 2
	vpsrlq ymm4, ymm4, 62
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+640], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+672], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+704], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+736], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+768], ymm10
	vpxor ymm15, ymm15, ymm10
	mov rax, rdi
	mov rdi, rsi
	mov rsi, rax
	add rdx, 32
	cmp rdx, rcx
	jne 2219b
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
	jne 2218b
	mov r8, rbx
	add r8, 20992
	mov r9d, 4
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
	vmovdqu ymm11, YMMWORD PTR [rdi]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+160]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+320]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+480]
	vpxor ymm11, ymm11, YMMWORD PTR [rdi+640]
	vmovdqu ymm12, YMMWORD PTR [rdi+32]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+192]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+352]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+512]
	vpxor ymm12, ymm12, YMMWORD PTR [rdi+672]
	vmovdqu ymm13, YMMWORD PTR [rdi+64]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+224]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+384]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+544]
	vpxor ymm13, ymm13, YMMWORD PTR [rdi+704]
	vmovdqu ymm14, YMMWORD PTR [rdi+96]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+256]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+416]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+576]
	vpxor ymm14, ymm14, YMMWORD PTR [rdi+736]
	vmovdqu ymm15, YMMWORD PTR [rdi+128]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+288]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+448]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+608]
	vpxor ymm15, ymm15, YMMWORD PTR [rdi+768]
2220:
	vpsllq ymm10, ymm12, 1
	vpsrlq ymm5, ymm12, 63
	vpor ymm5, ymm5, ymm10
	vpxor ymm5, ymm5, ymm15
	vpsllq ymm10, ymm13, 1
	vpsrlq ymm6, ymm13, 63
	vpor ymm6, ymm6, ymm10
	vpxor ymm6, ymm6, ymm11
	vpsllq ymm10, ymm14, 1
	vpsrlq ymm7, ymm14, 63
	vpor ymm7, ymm7, ymm10
	vpxor ymm7, ymm7, ymm12
	vpsllq ymm10, ymm15, 1
	vpsrlq ymm8, ymm15, 63
	vpor ymm8, ymm8, ymm10
	vpxor ymm8, ymm8, ymm13
	vpsllq ymm10, ymm11, 1
	vpsrlq ymm9, ymm11, 63
	vpor ymm9, ymm9, ymm10
	vpxor ymm9, ymm9, ymm14
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpxor ymm0, ymm0, ymm5
	vmovdqu ymm1, YMMWORD PTR [rdi+192]
	vpxor ymm1, ymm1, ymm6
	vpsllq ymm10, ymm1, 44
	vpsrlq ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+384]
	vpxor ymm2, ymm2, ymm7
	vpsllq ymm10, ymm2, 43
	vpsrlq ymm2, ymm2, 21
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+576]
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm10, ymm3, 21
	vpsrlq ymm3, ymm3, 43
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+768]
	vpxor ymm4, ymm4, ymm9
	vpsllq ymm10, ymm4, 14
	vpsrlq ymm4, ymm4, 50
	vpor ymm4, ymm4, ymm10
	vpandn ymm11, ymm1, ymm2
	vpxor ymm11, ymm11, ymm0
	vpxor ymm11, ymm11, YMMWORD PTR [rdx]
	vmovdqu YMMWORD PTR [rsi], ymm11
	vpandn ymm12, ymm2, ymm3
	vpxor ymm12, ymm12, ymm1
	vmovdqu YMMWORD PTR [rsi+32], ymm12
	vpandn ymm13, ymm3, ymm4
	vpxor ymm13, ymm13, ymm2
	vmovdqu YMMWORD PTR [rsi+64], ymm13
	vpandn ymm14, ymm4, ymm0
	vpxor ymm14, ymm14, ymm3
	vmovdqu YMMWORD PTR [rsi+96], ymm14
	vpandn ymm15, ymm0, ymm1
	vpxor ymm15, ymm15, ymm4
	vmovdqu YMMWORD PTR [rsi+128], ymm15
	vmovdqu ymm0, YMMWORD PTR [rdi+96]
	vpxor ymm0, ymm0, ymm8
	vpsllq ymm10, ymm0, 28
	vpsrlq ymm0, ymm0, 36
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+288]
	vpxor ymm1, ymm1, ymm9
	vpsllq ymm10, ymm1, 20
	vpsrlq ymm1, ymm1, 44
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+320]
	vpxor ymm2, ymm2, ymm5
	vpsllq ymm10, ymm2, 3
	vpsrlq ymm2, ymm2, 61
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+512]
	vpxor ymm3, ymm3, ymm6
	vpsllq ymm10, ymm3, 45
	vpsrlq ymm3, ymm3, 19
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+704]
	vpxor ymm4, ymm4, ymm7
	vpsllq ymm10, ymm4, 61
	vpsrlq ymm4, ymm4, 3
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+160], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+192], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+224], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+256], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+288], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+32]
	vpxor ymm0, ymm0, ymm6
	vpsllq ymm10, ymm0, 1
	vpsrlq ymm0, ymm0, 63
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+224]
	vpxor ymm1, ymm1, ymm7
	vpsllq ymm10, ymm1, 6
	vpsrlq ymm1, ymm1, 58
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+416]
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm10, ymm2, 25
	vpsrlq ymm2, ymm2, 39
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+608]
	vpxor ymm3, ymm3, ymm9
	vpsllq ymm10, ymm3, 8
	vpsrlq ymm3, ymm3, 56
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+640]
	vpxor ymm4, ymm4, ymm5
	vpsllq ymm10, ymm4, 18
	vpsrlq ymm4, ymm4, 46
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+320], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+352], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+384], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+416], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+448], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+128]
	vpxor ymm0, ymm0, ymm9
	vpsllq ymm10, ymm0, 27
	vpsrlq ymm0, ymm0, 37
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+160]
	vpxor ymm1, ymm1, ymm5
	vpsllq ymm10, ymm1, 36
	vpsrlq ymm1, ymm1, 28
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+352]
	vpxor ymm2, ymm2, ymm6
	vpsllq ymm10, ymm2, 10
	vpsrlq ymm2, ymm2, 54
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+544]
	vpxor ymm3, ymm3, ymm7
	vpsllq ymm10, ymm3, 15
	vpsrlq ymm3, ymm3, 49
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+736]
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm10, ymm4, 56
	vpsrlq ymm4, ymm4, 8
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+480], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+512], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+544], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+576], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+608], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+64]
	vpxor ymm0, ymm0, ymm7
	vpsllq ymm10, ymm0, 62
	vpsrlq ymm0, ymm0, 2
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+256]
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm10, ymm1, 55
	vpsrlq ymm1, ymm1, 9
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+448]
	vpxor ymm2, ymm2, ymm9
	vpsllq ymm10, ymm2, 39
	vpsrlq ymm2, ymm2, 25
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+480]
	vpxor ymm3, ymm3, ymm5
	vpsllq ymm10, ymm3, 41
	vpsrlq ymm3, ymm3, 23
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+672]
	vpxor ymm4, ymm4, ymm6
	vpsllq ymm10, ymm4, 2
	vpsrlq ymm4, ymm4, 62
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+640], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+672], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+704], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+736], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+768], ymm10
	vpxor ymm15, ymm15, ymm10
	mov rax, rdi
	mov rdi, rsi
	mov rsi, rax
	add rdx, 32
	cmp rdx, rcx
	vpsllq ymm10, ymm12, 1
	vpsrlq ymm5, ymm12, 63
	vpor ymm5, ymm5, ymm10
	vpxor ymm5, ymm5, ymm15
	vpsllq ymm10, ymm13, 1
	vpsrlq ymm6, ymm13, 63
	vpor ymm6, ymm6, ymm10
	vpxor ymm6, ymm6, ymm11
	vpsllq ymm10, ymm14, 1
	vpsrlq ymm7, ymm14, 63
	vpor ymm7, ymm7, ymm10
	vpxor ymm7, ymm7, ymm12
	vpsllq ymm10, ymm15, 1
	vpsrlq ymm8, ymm15, 63
	vpor ymm8, ymm8, ymm10
	vpxor ymm8, ymm8, ymm13
	vpsllq ymm10, ymm11, 1
	vpsrlq ymm9, ymm11, 63
	vpor ymm9, ymm9, ymm10
	vpxor ymm9, ymm9, ymm14
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpxor ymm0, ymm0, ymm5
	vmovdqu ymm1, YMMWORD PTR [rdi+192]
	vpxor ymm1, ymm1, ymm6
	vpsllq ymm10, ymm1, 44
	vpsrlq ymm1, ymm1, 20
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+384]
	vpxor ymm2, ymm2, ymm7
	vpsllq ymm10, ymm2, 43
	vpsrlq ymm2, ymm2, 21
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+576]
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm10, ymm3, 21
	vpsrlq ymm3, ymm3, 43
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+768]
	vpxor ymm4, ymm4, ymm9
	vpsllq ymm10, ymm4, 14
	vpsrlq ymm4, ymm4, 50
	vpor ymm4, ymm4, ymm10
	vpandn ymm11, ymm1, ymm2
	vpxor ymm11, ymm11, ymm0
	vpxor ymm11, ymm11, YMMWORD PTR [rdx]
	vmovdqu YMMWORD PTR [rsi], ymm11
	vpandn ymm12, ymm2, ymm3
	vpxor ymm12, ymm12, ymm1
	vmovdqu YMMWORD PTR [rsi+32], ymm12
	vpandn ymm13, ymm3, ymm4
	vpxor ymm13, ymm13, ymm2
	vmovdqu YMMWORD PTR [rsi+64], ymm13
	vpandn ymm14, ymm4, ymm0
	vpxor ymm14, ymm14, ymm3
	vmovdqu YMMWORD PTR [rsi+96], ymm14
	vpandn ymm15, ymm0, ymm1
	vpxor ymm15, ymm15, ymm4
	vmovdqu YMMWORD PTR [rsi+128], ymm15
	vmovdqu ymm0, YMMWORD PTR [rdi+96]
	vpxor ymm0, ymm0, ymm8
	vpsllq ymm10, ymm0, 28
	vpsrlq ymm0, ymm0, 36
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+288]
	vpxor ymm1, ymm1, ymm9
	vpsllq ymm10, ymm1, 20
	vpsrlq ymm1, ymm1, 44
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+320]
	vpxor ymm2, ymm2, ymm5
	vpsllq ymm10, ymm2, 3
	vpsrlq ymm2, ymm2, 61
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+512]
	vpxor ymm3, ymm3, ymm6
	vpsllq ymm10, ymm3, 45
	vpsrlq ymm3, ymm3, 19
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+704]
	vpxor ymm4, ymm4, ymm7
	vpsllq ymm10, ymm4, 61
	vpsrlq ymm4, ymm4, 3
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+160], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+192], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+224], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+256], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+288], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+32]
	vpxor ymm0, ymm0, ymm6
	vpsllq ymm10, ymm0, 1
	vpsrlq ymm0, ymm0, 63
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+224]
	vpxor ymm1, ymm1, ymm7
	vpsllq ymm10, ymm1, 6
	vpsrlq ymm1, ymm1, 58
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+416]
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm10, ymm2, 25
	vpsrlq ymm2, ymm2, 39
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+608]
	vpxor ymm3, ymm3, ymm9
	vpsllq ymm10, ymm3, 8
	vpsrlq ymm3, ymm3, 56
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+640]
	vpxor ymm4, ymm4, ymm5
	vpsllq ymm10, ymm4, 18
	vpsrlq ymm4, ymm4, 46
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+320], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+352], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+384], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+416], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+448], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+128]
	vpxor ymm0, ymm0, ymm9
	vpsllq ymm10, ymm0, 27
	vpsrlq ymm0, ymm0, 37
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+160]
	vpxor ymm1, ymm1, ymm5
	vpsllq ymm10, ymm1, 36
	vpsrlq ymm1, ymm1, 28
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+352]
	vpxor ymm2, ymm2, ymm6
	vpsllq ymm10, ymm2, 10
	vpsrlq ymm2, ymm2, 54
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+544]
	vpxor ymm3, ymm3, ymm7
	vpsllq ymm10, ymm3, 15
	vpsrlq ymm3, ymm3, 49
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+736]
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm10, ymm4, 56
	vpsrlq ymm4, ymm4, 8
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+480], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+512], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+544], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+576], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+608], ymm10
	vpxor ymm15, ymm15, ymm10
	vmovdqu ymm0, YMMWORD PTR [rdi+64]
	vpxor ymm0, ymm0, ymm7
	vpsllq ymm10, ymm0, 62
	vpsrlq ymm0, ymm0, 2
	vpor ymm0, ymm0, ymm10
	vmovdqu ymm1, YMMWORD PTR [rdi+256]
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm10, ymm1, 55
	vpsrlq ymm1, ymm1, 9
	vpor ymm1, ymm1, ymm10
	vmovdqu ymm2, YMMWORD PTR [rdi+448]
	vpxor ymm2, ymm2, ymm9
	vpsllq ymm10, ymm2, 39
	vpsrlq ymm2, ymm2, 25
	vpor ymm2, ymm2, ymm10
	vmovdqu ymm3, YMMWORD PTR [rdi+480]
	vpxor ymm3, ymm3, ymm5
	vpsllq ymm10, ymm3, 41
	vpsrlq ymm3, ymm3, 23
	vpor ymm3, ymm3, ymm10
	vmovdqu ymm4, YMMWORD PTR [rdi+672]
	vpxor ymm4, ymm4, ymm6
	vpsllq ymm10, ymm4, 2
	vpsrlq ymm4, ymm4, 62
	vpor ymm4, ymm4, ymm10
	vpandn ymm10, ymm1, ymm2
	vpxor ymm10, ymm10, ymm0
	vmovdqu YMMWORD PTR [rsi+640], ymm10
	vpxor ymm11, ymm11, ymm10
	vpandn ymm10, ymm2, ymm3
	vpxor ymm10, ymm10, ymm1
	vmovdqu YMMWORD PTR [rsi+672], ymm10
	vpxor ymm12, ymm12, ymm10
	vpandn ymm10, ymm3, ymm4
	vpxor ymm10, ymm10, ymm2
	vmovdqu YMMWORD PTR [rsi+704], ymm10
	vpxor ymm13, ymm13, ymm10
	vpandn ymm10, ymm4, ymm0
	vpxor ymm10, ymm10, ymm3
	vmovdqu YMMWORD PTR [rsi+736], ymm10
	vpxor ymm14, ymm14, ymm10
	vpandn ymm10, ymm0, ymm1
	vpxor ymm10, ymm10, ymm4
	vmovdqu YMMWORD PTR [rsi+768], ymm10
	vpxor ymm15, ymm15, ymm10
	mov rax, rdi
	mov rdi, rsi
	mov rsi, rax
	add rdx, 32
	cmp rdx, rcx
	jne 2220b
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
	vzeroupper
	mov rdi, rbx
	add rdi, 20480
	mov rsi, rbx
	add rsi, 8704
	call {vg_mlkem16_cbd2_avx2}
	mov rdi, rbx
	add rdi, 20608
	mov rsi, rbx
	add rsi, 9216
	call {vg_mlkem16_cbd2_avx2}
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
	add rdi, 21248
	mov rsi, rbx
	add rsi, 11776
	call {vg_mlkem16_cbd2_avx2}
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
2217:
	mov rdi, r12
	add rdi, 0
	mov rsi, rbx
	add rsi, 1024
	mov ecx, 4
2221:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2221b
	mov eax, r15d
	mov r15, QWORD PTR [rbx+880]
	mov r14, QWORD PTR [rbx+872]
	mov r13, QWORD PTR [rbx+864]
	mov r12, QWORD PTR [rbx+856]
	mov rbp, QWORD PTR [rbx+848]
	mov rbx, QWORD PTR [rbx+840]
	ret
	.p2align 6
