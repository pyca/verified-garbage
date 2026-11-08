// The functions of `src/internal/vg_mlkem768_encaps_h_body_avx2.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem768_encaps_h_body_avx2:
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
29:
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
	jne 29b
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
	mov r10d, 21
	vmovdqu ymm8, YMMWORD PTR [r11+4096]
	vmovdqu ymm9, YMMWORD PTR [r11+4128]
	vmovdqu ymm10, YMMWORD PTR [r11+4160]
210:
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
	sub r10, 1
	jne 210b
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
220:
	cmp rdi, 241
	jb 221f
	cmp rdi, 256
	jb 223f
	add rsi, 24
	jmp 224f
223:
	mov ecx, 8
225:
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
	jb 226f
	jmp 227f
226:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 228f
	jmp 229f
228:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
229:
227:
	add rsi, 3
	sub rcx, 1
	jne 225b
224:
	jmp 222f
221:
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
222:
	sub r10, 1
	jne 220b
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
230:
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
	sub r10, 1
	jne 230b
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
	je 240f
	jmp 241f
240:
	mov r14d, 1
	mov rbp, rbx
	add rbp, 2368
	mov r10d, 2
242:
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
243:
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
	jne 243b
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
	jne 242b
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
244:
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
	sub r10, 1
	jne 244b
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
254:
	cmp rdi, 241
	jb 255f
	cmp rdi, 256
	jb 257f
	add rsi, 24
	jmp 258f
257:
	mov ecx, 8
259:
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
	jb 260f
	jmp 261f
260:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 262f
	jmp 263f
262:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
263:
261:
	add rsi, 3
	sub rcx, 1
	jne 259b
258:
	jmp 256f
255:
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
256:
	sub r10, 1
	jne 254b
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
264:
	cmp rdi, 241
	jb 265f
	cmp rdi, 256
	jb 267f
	add rsi, 24
	jmp 268f
267:
	mov ecx, 8
269:
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
	jb 270f
	jmp 271f
270:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 272f
	jmp 273f
272:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
273:
271:
	add rsi, 3
	sub rcx, 1
	jne 269b
268:
	jmp 266f
265:
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
266:
	sub r10, 1
	jne 264b
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
241:
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
274:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 274b
	mov rdi, rbx
	add rdi, 0
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
	mov eax, 0
	mov BYTE PTR [rbx+32], al
	mov eax, 1
	mov BYTE PTR [rbx+33], al
	mov rdi, rbx
	add rdi, 34
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
	mov eax, 1
	mov BYTE PTR [rbx+66], al
	mov eax, 1
	mov BYTE PTR [rbx+67], al
	mov rdi, rbx
	add rdi, 68
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
277:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 277b
	mov eax, 2
	mov BYTE PTR [rbx+100], al
	mov eax, 1
	mov BYTE PTR [rbx+101], al
	mov rdi, rbx
	add rdi, 102
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
278:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 278b
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
279:
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
280:
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
	jne 280b
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
	jne 279b
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
281:
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
	sub r10, 1
	jne 281b
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
291:
	cmp rdi, 241
	jb 292f
	cmp rdi, 256
	jb 294f
	add rsi, 24
	jmp 295f
294:
	mov ecx, 8
296:
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
	jb 297f
	jmp 298f
297:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 299f
	jmp 2100f
299:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2100:
298:
	add rsi, 3
	sub rcx, 1
	jne 296b
295:
	jmp 293f
292:
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
293:
	sub r10, 1
	jne 291b
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
2101:
	cmp rdi, 241
	jb 2102f
	cmp rdi, 256
	jb 2104f
	add rsi, 24
	jmp 2105f
2104:
	mov ecx, 8
2106:
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
	jb 2107f
	jmp 2108f
2107:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2109f
	jmp 2110f
2109:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2110:
2108:
	add rsi, 3
	sub rcx, 1
	jne 2106b
2105:
	jmp 2103f
2102:
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
2103:
	sub r10, 1
	jne 2101b
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
	je 2111f
	jmp 2112f
2111:
	mov r14d, 1
	mov rbp, rbx
	add rbp, 2368
	mov r10d, 2
2113:
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
2114:
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
	jne 2114b
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
	jne 2113b
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
2115:
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
	sub r10, 1
	jne 2115b
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
2125:
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
	sub r10, 1
	jne 2125b
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
2135:
	cmp rdi, 241
	jb 2136f
	cmp rdi, 256
	jb 2138f
	add rsi, 24
	jmp 2139f
2138:
	mov ecx, 8
2140:
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
	jb 2141f
	jmp 2142f
2141:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2143f
	jmp 2144f
2143:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2144:
2142:
	add rsi, 3
	sub rcx, 1
	jne 2140b
2139:
	jmp 2137f
2136:
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
2137:
	sub r10, 1
	jne 2135b
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
2112:
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
2145:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2145b
	mov rdi, rbx
	add rdi, 0
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
	mov eax, 0
	mov BYTE PTR [rbx+32], al
	mov eax, 2
	mov BYTE PTR [rbx+33], al
	mov rdi, rbx
	add rdi, 34
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
	mov eax, 1
	mov BYTE PTR [rbx+66], al
	mov eax, 2
	mov BYTE PTR [rbx+67], al
	mov rdi, rbx
	add rdi, 68
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
2148:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2148b
	mov eax, 2
	mov BYTE PTR [rbx+100], al
	mov eax, 2
	mov BYTE PTR [rbx+101], al
	mov rdi, rbx
	add rdi, 102
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
2149:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2149b
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
2150:
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
2151:
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
	jne 2151b
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
	jne 2150b
	mov rbp, rbx
	add rbp, 2536
	mov r10d, 2
2152:
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
2153:
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
	jne 2153b
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
	jne 2152b
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
2154:
	cmp rdi, 241
	jb 2155f
	cmp rdi, 256
	jb 2157f
	add rsi, 24
	jmp 2158f
2157:
	mov ecx, 8
2159:
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
	jb 2160f
	jmp 2161f
2160:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2162f
	jmp 2163f
2162:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2163:
2161:
	add rsi, 3
	sub rcx, 1
	jne 2159b
2158:
	jmp 2156f
2155:
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
2156:
	sub r10, 1
	jne 2154b
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
2164:
	cmp rdi, 241
	jb 2165f
	cmp rdi, 256
	jb 2167f
	add rsi, 24
	jmp 2168f
2167:
	mov ecx, 8
2169:
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
	jb 2170f
	jmp 2171f
2170:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2172f
	jmp 2173f
2172:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2173:
2171:
	add rsi, 3
	sub rcx, 1
	jne 2169b
2168:
	jmp 2166f
2165:
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
2166:
	sub r10, 1
	jne 2164b
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
2174:
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
	sub r10, 1
	jne 2174b
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
	je 2184f
	jmp 2185f
2184:
	mov r14d, 1
	mov rbp, rbx
	add rbp, 2368
	mov r10d, 2
2186:
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
2187:
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
	jne 2187b
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
	jne 2186b
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
2188:
	cmp rdi, 241
	jb 2189f
	cmp rdi, 256
	jb 2191f
	add rsi, 24
	jmp 2192f
2191:
	mov ecx, 8
2193:
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
	jb 2194f
	jmp 2195f
2194:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2196f
	jmp 2197f
2196:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2197:
2195:
	add rsi, 3
	sub rcx, 1
	jne 2193b
2192:
	jmp 2190f
2189:
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
2190:
	sub r10, 1
	jne 2188b
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
2198:
	cmp rdi, 241
	jb 2199f
	cmp rdi, 256
	jb 2201f
	add rsi, 24
	jmp 2202f
2201:
	mov ecx, 8
2203:
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
	jb 2204f
	jmp 2205f
2204:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2206f
	jmp 2207f
2206:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2207:
2205:
	add rsi, 3
	sub rcx, 1
	jne 2203b
2202:
	jmp 2200f
2199:
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
2200:
	sub r10, 1
	jne 2198b
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
2208:
	cmp rdi, 241
	jb 2209f
	cmp rdi, 256
	jb 2211f
	add rsi, 24
	jmp 2212f
2211:
	mov ecx, 8
2213:
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
	jb 2214f
	jmp 2215f
2214:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2216f
	jmp 2217f
2216:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2217:
2215:
	add rsi, 3
	sub rcx, 1
	jne 2213b
2212:
	jmp 2210f
2209:
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
2210:
	sub r10, 1
	jne 2208b
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
2185:
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
	jne 2218f
	jmp 2219f
2218:
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
2219:
	mov rdi, r12
	add rdi, 0
	mov rsi, rbx
	add rsi, 1024
	mov ecx, 4
2220:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2220b
	mov eax, r15d
	mov r15, QWORD PTR [rbx+880]
	mov r14, QWORD PTR [rbx+872]
	mov r13, QWORD PTR [rbx+864]
	mov r12, QWORD PTR [rbx+856]
	mov rbp, QWORD PTR [rbx+848]
	mov rbx, QWORD PTR [rbx+840]
	ret
	.p2align 6
