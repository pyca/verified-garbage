// The functions of `src/internal/vg_mlkem1024_encaps_h_body_avx512.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem1024_encaps_h_body_avx512:
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
	add rsi, 1536
	mov ecx, 4
22:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 22b
	mov rdi, rbx
	add rdi, 0
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
	mov eax, 0
	mov BYTE PTR [rbx+32], al
	mov eax, 0
	mov BYTE PTR [rbx+33], al
	mov rdi, rbx
	add rdi, 34
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
	mov eax, 1
	mov BYTE PTR [rbx+66], al
	mov eax, 0
	mov BYTE PTR [rbx+67], al
	mov rdi, rbx
	add rdi, 68
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
	mov eax, 2
	mov BYTE PTR [rbx+100], al
	mov eax, 0
	mov BYTE PTR [rbx+101], al
	mov rdi, rbx
	add rdi, 102
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
	call {vg_mlkem16_sample_ntt4_avx512}
	and r15d, eax
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
	mov eax, 3
	mov BYTE PTR [rbx+134], al
	mov eax, 1
	mov BYTE PTR [rbx+135], al
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbx
	add rsi, 6144
	mov rdx, rbx
	add rdx, 16896
	call {vg_mlkem16_sample_ntt4_avx512}
	and r15d, eax
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
211:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 211b
	mov eax, 0
	mov BYTE PTR [rbx+32], al
	mov eax, 2
	mov BYTE PTR [rbx+33], al
	mov rdi, rbx
	add rdi, 34
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
	mov eax, 1
	mov BYTE PTR [rbx+66], al
	mov eax, 2
	mov BYTE PTR [rbx+67], al
	mov rdi, rbx
	add rdi, 68
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
	mov eax, 2
	mov BYTE PTR [rbx+100], al
	mov eax, 2
	mov BYTE PTR [rbx+101], al
	mov rdi, rbx
	add rdi, 102
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
	mov eax, 3
	mov BYTE PTR [rbx+134], al
	mov eax, 2
	mov BYTE PTR [rbx+135], al
	mov rdi, rbx
	add rdi, 0
	mov rsi, rbx
	add rsi, 8192
	mov rdx, rbx
	add rdx, 16896
	call {vg_mlkem16_sample_ntt4_avx512}
	and r15d, eax
	mov rdi, rbx
	add rdi, 0
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
	mov BYTE PTR [rbx+32], al
	mov eax, 3
	mov BYTE PTR [rbx+33], al
	mov rdi, rbx
	add rdi, 34
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
216:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 216b
	mov eax, 1
	mov BYTE PTR [rbx+66], al
	mov eax, 3
	mov BYTE PTR [rbx+67], al
	mov rdi, rbx
	add rdi, 68
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
217:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 217b
	mov eax, 2
	mov BYTE PTR [rbx+100], al
	mov eax, 3
	mov BYTE PTR [rbx+101], al
	mov rdi, rbx
	add rdi, 102
	mov rsi, rbx
	add rsi, 904
	mov ecx, 4
218:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdi], rax
	add rdi, 8
	add rsi, 8
	sub rcx, 1
	jne 218b
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
	test r15d, r15d
	jne 219f
	jmp 220f
219:
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
221:
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
222:
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
	jne 222b
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
	jne 221b
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
220:
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
