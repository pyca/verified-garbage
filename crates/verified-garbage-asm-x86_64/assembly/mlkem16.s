// The functions of `src/mlkem16.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem16_sample_ntt:
	mov QWORD PTR [rdx+1680], rbx
	mov QWORD PTR [rdx+1688], rbp
	mov QWORD PTR [rdx+1696], rdi
	mov rbx, rdx
	mov rbp, rsi
	mov rcx, rdi
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
	mov esi, 168
	mov edx, 0
	mov r8d, 34
	mov r9, rbx
	add r9, 200
	call {vg_keccak_absorb_scratch}
	mov rdi, rbx
	mov esi, 168
	mov edx, 34
	mov ecx, 31
	mov r8, rbx
	add r8, 200
	call {vg_keccak_pad_scratch}
	mov rdi, rbx
	mov esi, 168
	mov edx, 0
	mov rcx, rbx
	add rcx, 840
	mov r8d, 504
	mov r9, rbx
	add r9, 200
	call {vg_keccak_squeeze_scratch}
	mov rsi, rbx
	add rsi, 840
	mov edi, 0
	mov ecx, 168
20:
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
	jb 21f
	jmp 22f
21:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 23f
	jmp 24f
23:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
24:
22:
	add rsi, 3
	sub rcx, 1
	jne 20b
	cmp rdi, 256
	jb 25f
	jmp 26f
25:
	mov rcx, QWORD PTR [rbx+1696]
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
	mov esi, 168
	mov edx, 0
	mov r8d, 34
	mov r9, rbx
	add r9, 200
	call {vg_keccak_absorb_scratch}
	mov rdi, rbx
	mov esi, 168
	mov edx, 34
	mov ecx, 31
	mov r8, rbx
	add r8, 200
	call {vg_keccak_pad_scratch}
	mov rdi, rbx
	mov esi, 168
	mov edx, 0
	mov rcx, rbx
	add rcx, 840
	mov r8d, 840
	mov r9, rbx
	add r9, 200
	call {vg_keccak_squeeze_scratch}
	mov rsi, rbx
	add rsi, 840
	mov edi, 0
	mov ecx, 280
27:
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
	jb 28f
	jmp 29f
28:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 210f
	jmp 211f
210:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
211:
29:
	add rsi, 3
	sub rcx, 1
	jne 27b
26:
	mov rax, rdi
	shr rax, 8
	mov rbp, QWORD PTR [rbx+1688]
	mov rbx, QWORD PTR [rbx+1680]
	ret
	.p2align 6

vg_mlkem16_sample_ntt4_avx2:
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
	mov rbp, rbx
	add rbp, 2368
	mov r10d, 3
20:
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
21:
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
	jne 21b
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
	jne 20b
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
22:
	cmp rdi, 241
	jb 23f
	cmp rdi, 256
	jb 25f
	add rsi, 24
	jmp 26f
25:
	mov ecx, 8
27:
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
	jb 28f
	jmp 29f
28:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 210f
	jmp 211f
210:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
211:
29:
	add rsi, 3
	sub rcx, 1
	jne 27b
26:
	jmp 24f
23:
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
24:
	sub r10, 1
	jne 22b
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
212:
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
	sub r10, 1
	jne 212b
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
222:
	cmp rdi, 241
	jb 223f
	cmp rdi, 256
	jb 225f
	add rsi, 24
	jmp 226f
225:
	mov ecx, 8
227:
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
	jb 228f
	jmp 229f
228:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 230f
	jmp 231f
230:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
231:
229:
	add rsi, 3
	sub rcx, 1
	jne 227b
226:
	jmp 224f
223:
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
224:
	sub r10, 1
	jne 222b
	mov QWORD PTR [rbx+4440], rdi
	mov rsi, rbx
	add rsi, 3880
	mov edi, 0
	mov rbp, r13
	add rbp, 1536
	mov r10d, 21
	vmovdqu ymm8, YMMWORD PTR [r11+4096]
	vmovdqu ymm9, YMMWORD PTR [r11+4128]
	vmovdqu ymm10, YMMWORD PTR [r11+4160]
232:
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
	sub r10, 1
	jne 232b
	mov QWORD PTR [rbx+4448], rdi
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
	mov rax, QWORD PTR [rbx+4448]
	shr rax, 8
	and r14d, eax
	cmp r14d, 0
	je 242f
	jmp 243f
242:
	mov r14d, 1
	mov rbp, rbx
	add rbp, 2368
	mov r10d, 2
244:
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
245:
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
	jne 245b
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
	jne 244b
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
246:
	cmp rdi, 241
	jb 247f
	cmp rdi, 256
	jb 249f
	add rsi, 24
	jmp 250f
249:
	mov ecx, 8
251:
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
	jb 252f
	jmp 253f
252:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 254f
	jmp 255f
254:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
255:
253:
	add rsi, 3
	sub rcx, 1
	jne 251b
250:
	jmp 248f
247:
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
248:
	sub r10, 1
	jne 246b
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
256:
	cmp rdi, 241
	jb 257f
	cmp rdi, 256
	jb 259f
	add rsi, 24
	jmp 260f
259:
	mov ecx, 8
261:
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
	jb 262f
	jmp 263f
262:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 264f
	jmp 265f
264:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
265:
263:
	add rsi, 3
	sub rcx, 1
	jne 261b
260:
	jmp 258f
257:
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
258:
	sub r10, 1
	jne 256b
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
266:
	cmp rdi, 241
	jb 267f
	cmp rdi, 256
	jb 269f
	add rsi, 24
	jmp 270f
269:
	mov ecx, 8
271:
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
	jb 272f
	jmp 273f
272:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 274f
	jmp 275f
274:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
275:
273:
	add rsi, 3
	sub rcx, 1
	jne 271b
270:
	jmp 268f
267:
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
268:
	sub r10, 1
	jne 266b
	mov QWORD PTR [rbx+4440], rdi
	mov rsi, rbx
	add rsi, 3880
	mov rdi, QWORD PTR [rbx+4448]
	mov rbp, r13
	add rbp, 1536
	mov r10d, 14
	vmovdqu ymm8, YMMWORD PTR [r11+4096]
	vmovdqu ymm9, YMMWORD PTR [r11+4128]
	vmovdqu ymm10, YMMWORD PTR [r11+4160]
276:
	cmp rdi, 241
	jb 277f
	cmp rdi, 256
	jb 279f
	add rsi, 24
	jmp 280f
279:
	mov ecx, 8
281:
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
	jb 282f
	jmp 283f
282:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 284f
	jmp 285f
284:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
285:
283:
	add rsi, 3
	sub rcx, 1
	jne 281b
280:
	jmp 278f
277:
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
278:
	sub r10, 1
	jne 276b
	mov QWORD PTR [rbx+4448], rdi
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
	mov rax, QWORD PTR [rbx+4448]
	shr rax, 8
	and r14d, eax
243:
	vzeroupper
	mov eax, r14d
	mov r14, QWORD PTR [rbx+4416]
	mov r13, QWORD PTR [rbx+4408]
	mov r12, QWORD PTR [rbx+4400]
	mov rbp, QWORD PTR [rbx+4392]
	mov rbx, QWORD PTR [rbx+4384]
	ret
	.p2align 6

vg_mlkem16_sample_ntt4_avx512:
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
	mov rbp, rbx
	add rbp, 2368
	mov r10d, 3
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
	jne 20b
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
22:
	cmp rdi, 241
	jb 23f
	cmp rdi, 256
	jb 25f
	add rsi, 24
	jmp 26f
25:
	mov ecx, 8
27:
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
	jb 28f
	jmp 29f
28:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 210f
	jmp 211f
210:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
211:
29:
	add rsi, 3
	sub rcx, 1
	jne 27b
26:
	jmp 24f
23:
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
24:
	sub r10, 1
	jne 22b
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
212:
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
	sub r10, 1
	jne 212b
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
222:
	cmp rdi, 241
	jb 223f
	cmp rdi, 256
	jb 225f
	add rsi, 24
	jmp 226f
225:
	mov ecx, 8
227:
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
	jb 228f
	jmp 229f
228:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 230f
	jmp 231f
230:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
231:
229:
	add rsi, 3
	sub rcx, 1
	jne 227b
226:
	jmp 224f
223:
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
224:
	sub r10, 1
	jne 222b
	mov QWORD PTR [rbx+4440], rdi
	mov rsi, rbx
	add rsi, 3880
	mov edi, 0
	mov rbp, r13
	add rbp, 1536
	mov r10d, 21
	vmovdqu ymm8, YMMWORD PTR [r11+4096]
	vmovdqu ymm9, YMMWORD PTR [r11+4128]
	vmovdqu ymm10, YMMWORD PTR [r11+4160]
232:
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
	sub r10, 1
	jne 232b
	mov QWORD PTR [rbx+4448], rdi
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
	mov rax, QWORD PTR [rbx+4448]
	shr rax, 8
	and r14d, eax
	cmp r14d, 0
	je 242f
	jmp 243f
242:
	mov r14d, 1
	mov rbp, rbx
	add rbp, 2368
	mov r10d, 2
244:
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
245:
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
	jne 245b
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
	jne 244b
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
246:
	cmp rdi, 241
	jb 247f
	cmp rdi, 256
	jb 249f
	add rsi, 24
	jmp 250f
249:
	mov ecx, 8
251:
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
	jb 252f
	jmp 253f
252:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 254f
	jmp 255f
254:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
255:
253:
	add rsi, 3
	sub rcx, 1
	jne 251b
250:
	jmp 248f
247:
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
248:
	sub r10, 1
	jne 246b
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
256:
	cmp rdi, 241
	jb 257f
	cmp rdi, 256
	jb 259f
	add rsi, 24
	jmp 260f
259:
	mov ecx, 8
261:
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
	jb 262f
	jmp 263f
262:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 264f
	jmp 265f
264:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
265:
263:
	add rsi, 3
	sub rcx, 1
	jne 261b
260:
	jmp 258f
257:
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
258:
	sub r10, 1
	jne 256b
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
266:
	cmp rdi, 241
	jb 267f
	cmp rdi, 256
	jb 269f
	add rsi, 24
	jmp 270f
269:
	mov ecx, 8
271:
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
	jb 272f
	jmp 273f
272:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 274f
	jmp 275f
274:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
275:
273:
	add rsi, 3
	sub rcx, 1
	jne 271b
270:
	jmp 268f
267:
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
268:
	sub r10, 1
	jne 266b
	mov QWORD PTR [rbx+4440], rdi
	mov rsi, rbx
	add rsi, 3880
	mov rdi, QWORD PTR [rbx+4448]
	mov rbp, r13
	add rbp, 1536
	mov r10d, 14
	vmovdqu ymm8, YMMWORD PTR [r11+4096]
	vmovdqu ymm9, YMMWORD PTR [r11+4128]
	vmovdqu ymm10, YMMWORD PTR [r11+4160]
276:
	cmp rdi, 241
	jb 277f
	cmp rdi, 256
	jb 279f
	add rsi, 24
	jmp 280f
279:
	mov ecx, 8
281:
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
	jb 282f
	jmp 283f
282:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 284f
	jmp 285f
284:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
285:
283:
	add rsi, 3
	sub rcx, 1
	jne 281b
280:
	jmp 278f
277:
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
278:
	sub r10, 1
	jne 276b
	mov QWORD PTR [rbx+4448], rdi
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
	mov rax, QWORD PTR [rbx+4448]
	shr rax, 8
	and r14d, eax
243:
	vzeroupper
	mov eax, r14d
	mov r14, QWORD PTR [rbx+4416]
	mov r13, QWORD PTR [rbx+4408]
	mov r12, QWORD PTR [rbx+4400]
	mov rbp, QWORD PTR [rbx+4392]
	mov rbx, QWORD PTR [rbx+4384]
	ret
	.p2align 6

vg_mlkem16_cbd2_avx2:
	mov eax, 218172673
	vmovq xmm15, rax
	vpbroadcastd ymm15, xmm15
	mov eax, 16711935
	vmovq xmm8, rax
	vpbroadcastd ymm8, xmm8
	mov eax, 5570645
	vmovq xmm9, rax
	vpbroadcastd ymm9, xmm9
	mov eax, 3342387
	vmovq xmm10, rax
	vpbroadcastd ymm10, xmm10
	mov eax, 2228258
	vmovq xmm11, rax
	vpbroadcastd ymm11, xmm11
	mov eax, 983055
	vmovq xmm12, rax
	vpbroadcastd ymm12, xmm12
	mov eax, 131074
	vmovq xmm13, rax
	vpbroadcastd ymm13, xmm13
	mov ecx, 4
20:
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpsrlw ymm1, ymm0, 8
	vpand ymm0, ymm0, ymm8
	vpsrlw ymm2, ymm0, 1
	vpand ymm2, ymm2, ymm9
	vpand ymm0, ymm0, ymm9
	vpaddw ymm0, ymm0, ymm2
	vpsrlw ymm2, ymm0, 2
	vpand ymm2, ymm2, ymm10
	vpand ymm0, ymm0, ymm10
	vpaddw ymm0, ymm0, ymm11
	vpsubw ymm0, ymm0, ymm2
	vpsrlw ymm2, ymm0, 4
	vpand ymm0, ymm0, ymm12
	vpsrlw ymm3, ymm1, 1
	vpand ymm3, ymm3, ymm9
	vpand ymm1, ymm1, ymm9
	vpaddw ymm1, ymm1, ymm3
	vpsrlw ymm3, ymm1, 2
	vpand ymm3, ymm3, ymm10
	vpand ymm1, ymm1, ymm10
	vpaddw ymm1, ymm1, ymm11
	vpsubw ymm1, ymm1, ymm3
	vpsrlw ymm3, ymm1, 4
	vpand ymm1, ymm1, ymm12
	vpunpcklwd ymm4, ymm0, ymm2
	vpunpckhwd ymm0, ymm0, ymm2
	vpunpcklwd ymm2, ymm1, ymm3
	vpunpckhwd ymm1, ymm1, ymm3
	vpunpckldq ymm7, ymm4, ymm2
	vpunpckhdq ymm4, ymm4, ymm2
	vpsubw ymm7, ymm7, ymm13
	vpsraw ymm6, ymm7, 15
	vpand ymm6, ymm6, ymm15
	vpaddw ymm7, ymm7, ymm6
	vpsubw ymm4, ymm4, ymm13
	vpsraw ymm6, ymm4, 15
	vpand ymm6, ymm6, ymm15
	vpaddw ymm4, ymm4, ymm6
	vpunpckldq ymm5, ymm0, ymm1
	vpunpckhdq ymm0, ymm0, ymm1
	vpsubw ymm5, ymm5, ymm13
	vpsraw ymm6, ymm5, 15
	vpand ymm6, ymm6, ymm15
	vpaddw ymm5, ymm5, ymm6
	vpsubw ymm0, ymm0, ymm13
	vpsraw ymm6, ymm0, 15
	vpand ymm6, ymm6, ymm15
	vpaddw ymm0, ymm0, ymm6
	vperm2i128 ymm1, ymm7, ymm4, 32
	vperm2i128 ymm2, ymm5, ymm0, 32
	vperm2i128 ymm3, ymm7, ymm4, 49
	vperm2i128 ymm6, ymm5, ymm0, 49
	vmovdqu YMMWORD PTR [rsi], ymm1
	vmovdqu YMMWORD PTR [rsi+32], ymm2
	vmovdqu YMMWORD PTR [rsi+64], ymm3
	vmovdqu YMMWORD PTR [rsi+96], ymm6
	add rdi, 32
	add rsi, 128
	sub rcx, 1
	jne 20b
	vzeroupper
	ret
	.p2align 6
