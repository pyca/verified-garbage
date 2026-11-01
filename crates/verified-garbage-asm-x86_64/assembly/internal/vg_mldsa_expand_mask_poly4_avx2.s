// The functions of `src/internal/vg_mldsa_expand_mask_poly4_avx2.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_expand_mask_poly4_avx2:
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
