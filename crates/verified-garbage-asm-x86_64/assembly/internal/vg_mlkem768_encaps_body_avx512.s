// The functions of `src/internal/vg_mlkem768_encaps_body_avx512.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem768_encaps_body_avx512:
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
	call {vg_mlkem16_sample_hash_avx512}
	and r15d, eax
	mov rdi, rbx
	add rdi, 19208
	mov rsi, r14
	add rsi, 408
	mov ecx, 51
26:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 26b
	mov rdi, rbx
	add rdi, 0
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
	mov BYTE PTR [rbx+32], al
	mov eax, 1
	mov BYTE PTR [rbx+33], al
	mov rdi, rbx
	add rdi, 34
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
28:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 28b
	mov eax, 1
	mov BYTE PTR [rbx+66], al
	mov eax, 1
	mov BYTE PTR [rbx+67], al
	mov rdi, rbx
	add rdi, 68
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
29:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 29b
	mov eax, 2
	mov BYTE PTR [rbx+100], al
	mov eax, 1
	mov BYTE PTR [rbx+101], al
	mov rdi, rbx
	add rdi, 102
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
210:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 210b
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
	call {vg_mlkem16_sample_hash_avx512}
	and r15d, eax
	mov rdi, rbx
	add rdi, 19208
	mov rsi, r14
	add rsi, 816
	mov ecx, 46
211:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 211b
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
212:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 212b
	mov eax, 0
	mov BYTE PTR [rbx+32], al
	mov eax, 2
	mov BYTE PTR [rbx+33], al
	mov rdi, rbx
	add rdi, 34
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
213:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 213b
	mov eax, 1
	mov BYTE PTR [rbx+66], al
	mov eax, 2
	mov BYTE PTR [rbx+67], al
	mov rdi, rbx
	add rdi, 68
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
214:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 214b
	mov eax, 2
	mov BYTE PTR [rbx+100], al
	mov eax, 2
	mov BYTE PTR [rbx+101], al
	mov rdi, rbx
	add rdi, 102
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
215:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 215b
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
	call {vg_mlkem16_sample_hash_avx512}
	and r15d, eax
	mov rdi, rbx
	add rdi, 1088
	mov rsi, rbx
	add rsi, 19008
	mov ecx, 4
216:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 216b
	mov rdi, rbx
	add rdi, 1248
	mov rsi, rbp
	add rsi, 0
	mov ecx, 4
217:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 217b
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
	jne 218f
	jmp 219f
218:
	mov r8, rbx
	add r8, 20480
	mov r9d, 0
	mov r10d, 1
220:
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
221:
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
	jne 221b
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
	jne 220b
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
222:
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
	jne 222b
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
219:
	mov rdi, r12
	add rdi, 0
	mov rsi, rbx
	add rsi, 1024
	mov ecx, 4
223:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 223b
	mov eax, r15d
	mov r15, QWORD PTR [rbx+880]
	mov r14, QWORD PTR [rbx+872]
	mov r13, QWORD PTR [rbx+864]
	mov r12, QWORD PTR [rbx+856]
	mov rbp, QWORD PTR [rbx+848]
	mov rbx, QWORD PTR [rbx+840]
	ret
	.p2align 6
