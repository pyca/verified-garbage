// The functions of `src/internal/vg_mlkem768_keygen_body_avx2.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem768_keygen_body_avx2:
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
22:
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
	jne 22b
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
211:
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
	jne 211b
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
243:
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
	jne 276f
	jmp 277f
276:
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
277:
	mov rdi, rbx
	add rdi, 19208
	mov rsi, r12
	add rsi, 0
	mov ecx, 34
278:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 278b
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
279:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 279b
	mov eax, 0
	mov BYTE PTR [rbx+32], al
	mov eax, 1
	mov BYTE PTR [rbx+33], al
	mov rdi, rbx
	add rdi, 34
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
280:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 280b
	mov eax, 1
	mov BYTE PTR [rbx+66], al
	mov eax, 1
	mov BYTE PTR [rbx+67], al
	mov rdi, rbx
	add rdi, 68
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
281:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 281b
	mov eax, 2
	mov BYTE PTR [rbx+100], al
	mov eax, 1
	mov BYTE PTR [rbx+101], al
	mov rdi, rbx
	add rdi, 102
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
282:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 282b
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
283:
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
284:
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
	jne 284b
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
	jne 283b
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
285:
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
286:
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
	jne 286b
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
	jne 285b
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
287:
	cmp rdi, 241
	jb 288f
	cmp rdi, 256
	jb 290f
	add rsi, 24
	jmp 291f
290:
	mov ecx, 8
292:
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
	jb 293f
	jmp 294f
293:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 295f
	jmp 296f
295:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
296:
294:
	add rsi, 3
	sub rcx, 1
	jne 292b
291:
	jmp 289f
288:
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
289:
	sub r10, 1
	jne 287b
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
297:
	cmp rdi, 241
	jb 298f
	cmp rdi, 256
	jb 2100f
	add rsi, 24
	jmp 2101f
2100:
	mov ecx, 8
2102:
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
	jb 2103f
	jmp 2104f
2103:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2105f
	jmp 2106f
2105:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2106:
2104:
	add rsi, 3
	sub rcx, 1
	jne 2102b
2101:
	jmp 299f
298:
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
299:
	sub r10, 1
	jne 297b
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
2107:
	cmp rdi, 241
	jb 2108f
	cmp rdi, 256
	jb 2110f
	add rsi, 24
	jmp 2111f
2110:
	mov ecx, 8
2112:
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
	jb 2113f
	jmp 2114f
2113:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2115f
	jmp 2116f
2115:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2116:
2114:
	add rsi, 3
	sub rcx, 1
	jne 2112b
2111:
	jmp 2109f
2108:
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
2109:
	sub r10, 1
	jne 2107b
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
	je 2117f
	jmp 2118f
2117:
	mov r14d, 1
	mov rbp, rbx
	add rbp, 2368
	mov r10d, 2
2119:
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
2120:
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
	jne 2120b
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
	jne 2119b
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
2121:
	cmp rdi, 241
	jb 2122f
	cmp rdi, 256
	jb 2124f
	add rsi, 24
	jmp 2125f
2124:
	mov ecx, 8
2126:
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
	jb 2127f
	jmp 2128f
2127:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2129f
	jmp 2130f
2129:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2130:
2128:
	add rsi, 3
	sub rcx, 1
	jne 2126b
2125:
	jmp 2123f
2122:
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
2123:
	sub r10, 1
	jne 2121b
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
2131:
	cmp rdi, 241
	jb 2132f
	cmp rdi, 256
	jb 2134f
	add rsi, 24
	jmp 2135f
2134:
	mov ecx, 8
2136:
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
	jb 2137f
	jmp 2138f
2137:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2139f
	jmp 2140f
2139:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2140:
2138:
	add rsi, 3
	sub rcx, 1
	jne 2136b
2135:
	jmp 2133f
2132:
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
2133:
	sub r10, 1
	jne 2131b
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
2141:
	cmp rdi, 241
	jb 2142f
	cmp rdi, 256
	jb 2144f
	add rsi, 24
	jmp 2145f
2144:
	mov ecx, 8
2146:
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
	jb 2147f
	jmp 2148f
2147:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2149f
	jmp 2150f
2149:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2150:
2148:
	add rsi, 3
	sub rcx, 1
	jne 2146b
2145:
	jmp 2143f
2142:
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
2143:
	sub r10, 1
	jne 2141b
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
2118:
	vzeroupper
	mov eax, r14d
	mov r14, QWORD PTR [rbx+4416]
	mov r13, QWORD PTR [rbx+4408]
	mov r12, QWORD PTR [rbx+4400]
	mov rbp, QWORD PTR [rbx+4392]
	mov rbx, QWORD PTR [rbx+4384]
	and r15d, eax
	test r15d, r15d
	jne 2151f
	jmp 2152f
2151:
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
2152:
	mov rdi, rbx
	add rdi, 19208
	mov rsi, r12
	add rsi, 272
	mov ecx, 51
2153:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2153b
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
2154:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2154b
	mov eax, 0
	mov BYTE PTR [rbx+32], al
	mov eax, 2
	mov BYTE PTR [rbx+33], al
	mov rdi, rbx
	add rdi, 34
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
2155:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2155b
	mov eax, 1
	mov BYTE PTR [rbx+66], al
	mov eax, 2
	mov BYTE PTR [rbx+67], al
	mov rdi, rbx
	add rdi, 68
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
2156:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2156b
	mov eax, 2
	mov BYTE PTR [rbx+100], al
	mov eax, 2
	mov BYTE PTR [rbx+101], al
	mov rdi, rbx
	add rdi, 102
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
2157:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2157b
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
2158:
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
2159:
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
	jne 2159b
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
	jne 2158b
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
2180:
	cmp rdi, 241
	jb 2181f
	cmp rdi, 256
	jb 2183f
	add rsi, 24
	jmp 2184f
2183:
	mov ecx, 8
2185:
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
	jb 2186f
	jmp 2187f
2186:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2188f
	jmp 2189f
2188:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2189:
2187:
	add rsi, 3
	sub rcx, 1
	jne 2185b
2184:
	jmp 2182f
2181:
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
2182:
	sub r10, 1
	jne 2180b
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
	je 2190f
	jmp 2191f
2190:
	mov r14d, 1
	mov rbp, rbx
	add rbp, 2368
	mov r10d, 2
2192:
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
2193:
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
	jne 2193b
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
	jne 2192b
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
2214:
	cmp rdi, 241
	jb 2215f
	cmp rdi, 256
	jb 2217f
	add rsi, 24
	jmp 2218f
2217:
	mov ecx, 8
2219:
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
	jb 2220f
	jmp 2221f
2220:
	mov WORD PTR [rbp+rdi*2], r9w
	cmp r9d, 3329
	adc rdi, 0
	cmp rdi, 256
	jb 2222f
	jmp 2223f
2222:
	mov WORD PTR [rbp+rdi*2], r8w
	cmp r8d, 3329
	adc rdi, 0
2223:
2221:
	add rsi, 3
	sub rcx, 1
	jne 2219b
2218:
	jmp 2216f
2215:
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
2216:
	sub r10, 1
	jne 2214b
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
2191:
	vzeroupper
	mov eax, r14d
	mov r14, QWORD PTR [rbx+4416]
	mov r13, QWORD PTR [rbx+4408]
	mov r12, QWORD PTR [rbx+4400]
	mov rbp, QWORD PTR [rbx+4392]
	mov rbx, QWORD PTR [rbx+4384]
	and r15d, eax
	test r15d, r15d
	jne 2224f
	jmp 2225f
2224:
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
2226:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2226b
	mov rdi, r13
	add rdi, 1152
	mov rsi, r12
	add rsi, 0
	mov ecx, 148
2227:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2227b
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbx
	add rsi, 19008
	mov ecx, 25
2228:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2228b
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
2229:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 2229b
2225:
	mov eax, r15d
	mov r15, QWORD PTR [rbx+880]
	mov r14, QWORD PTR [rbx+872]
	mov r13, QWORD PTR [rbx+864]
	mov r12, QWORD PTR [rbx+856]
	mov rbp, QWORD PTR [rbx+848]
	mov rbx, QWORD PTR [rbx+840]
	ret
	.p2align 6
