// The functions of `src/internal/vg_mlkem768_kpke_encrypt.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem768_kpke_encrypt:
	mov QWORD PTR [r9+19456], rbx
	mov QWORD PTR [r9+19464], rbp
	mov QWORD PTR [r9+19472], r12
	mov QWORD PTR [r9+19480], r13
	mov QWORD PTR [r9+19488], r14
	mov QWORD PTR [r9+19496], r15
	mov rbx, r9
	mov r15, rdi
	mov rbp, rsi
	mov r12, rdx
	mov r13, rcx
	mov r14, r8
	mov rdi, r12
	add rdi, 0
	mov rsi, rbx
	add rsi, 7168
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm8, YMMWORD PTR [rax+1184]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm12, YMMWORD PTR [rax+1216]
	movabs rax, 17179869184
	vmovq xmm9, rax
	vpbroadcastq ymm9, xmm9
	mov eax, 4095
	vmovq xmm10, rax
	vpbroadcastd ymm10, xmm10
	mov eax, 3329
	vmovq xmm11, rax
	vpbroadcastd ymm11, xmm11
	mov ecx, 31
20:
	vbroadcasti128 ymm0, XMMWORD PTR [rdi]
	vpshufb ymm0, ymm0, ymm8
	vpsrlvd ymm0, ymm0, ymm9
	vpand ymm0, ymm0, ymm10
	vpsubd ymm0, ymm0, ymm11
	vpsrad ymm1, ymm0, 31
	vpand ymm1, ymm1, ymm11
	vpaddd ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rsi], ymm0
	add rdi, 12
	add rsi, 32
	sub rcx, 1
	jne 20b
	sub rdi, 4
	vbroadcasti128 ymm0, XMMWORD PTR [rdi]
	vpshufb ymm0, ymm0, ymm12
	vpsrlvd ymm0, ymm0, ymm9
	vpand ymm0, ymm0, ymm10
	vpsubd ymm0, ymm0, ymm11
	vpsrad ymm1, ymm0, 31
	vpand ymm1, ymm1, ymm11
	vpaddd ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rsi], ymm0
	vzeroupper
	mov rdi, r12
	add rdi, 384
	mov rsi, rbx
	add rsi, 8192
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm8, YMMWORD PTR [rax+1184]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm12, YMMWORD PTR [rax+1216]
	movabs rax, 17179869184
	vmovq xmm9, rax
	vpbroadcastq ymm9, xmm9
	mov eax, 4095
	vmovq xmm10, rax
	vpbroadcastd ymm10, xmm10
	mov eax, 3329
	vmovq xmm11, rax
	vpbroadcastd ymm11, xmm11
	mov ecx, 31
21:
	vbroadcasti128 ymm0, XMMWORD PTR [rdi]
	vpshufb ymm0, ymm0, ymm8
	vpsrlvd ymm0, ymm0, ymm9
	vpand ymm0, ymm0, ymm10
	vpsubd ymm0, ymm0, ymm11
	vpsrad ymm1, ymm0, 31
	vpand ymm1, ymm1, ymm11
	vpaddd ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rsi], ymm0
	add rdi, 12
	add rsi, 32
	sub rcx, 1
	jne 21b
	sub rdi, 4
	vbroadcasti128 ymm0, XMMWORD PTR [rdi]
	vpshufb ymm0, ymm0, ymm12
	vpsrlvd ymm0, ymm0, ymm9
	vpand ymm0, ymm0, ymm10
	vpsubd ymm0, ymm0, ymm11
	vpsrad ymm1, ymm0, 31
	vpand ymm1, ymm1, ymm11
	vpaddd ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rsi], ymm0
	vzeroupper
	mov rdi, r12
	add rdi, 768
	mov rsi, rbx
	add rsi, 9216
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm8, YMMWORD PTR [rax+1184]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm12, YMMWORD PTR [rax+1216]
	movabs rax, 17179869184
	vmovq xmm9, rax
	vpbroadcastq ymm9, xmm9
	mov eax, 4095
	vmovq xmm10, rax
	vpbroadcastd ymm10, xmm10
	mov eax, 3329
	vmovq xmm11, rax
	vpbroadcastd ymm11, xmm11
	mov ecx, 31
22:
	vbroadcasti128 ymm0, XMMWORD PTR [rdi]
	vpshufb ymm0, ymm0, ymm8
	vpsrlvd ymm0, ymm0, ymm9
	vpand ymm0, ymm0, ymm10
	vpsubd ymm0, ymm0, ymm11
	vpsrad ymm1, ymm0, 31
	vpand ymm1, ymm1, ymm11
	vpaddd ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rsi], ymm0
	add rdi, 12
	add rsi, 32
	sub rcx, 1
	jne 22b
	sub rdi, 4
	vbroadcasti128 ymm0, XMMWORD PTR [rdi]
	vpshufb ymm0, ymm0, ymm12
	vpsrlvd ymm0, ymm0, ymm9
	vpand ymm0, ymm0, ymm10
	vpsubd ymm0, ymm0, ymm11
	vpsrad ymm1, ymm0, 31
	vpand ymm1, ymm1, ymm11
	vpaddd ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rsi], ymm0
	vzeroupper
	mov rdi, rbx
	add rdi, 10240
	mov rsi, rbp
	add rsi, 0
	mov rdx, rbx
	add rdx, 7168
	mov rcx, r13
	add rcx, 0
	mov r8, rbx
	add r8, 0
	mov QWORD PTR [r8+3072], rbp
	mov QWORD PTR [r8+3080], r12
	mov QWORD PTR [r8+3088], r13
	mov QWORD PTR [r8+3096], r14
	mov QWORD PTR [r8+3104], r15
	mov QWORD PTR [r8+3112], rbx
	mov rbx, r8
	mov rbp, rdi
	mov r12, rsi
	mov r13, rcx
	mov r15, rdx
	mov r14d, 3
	stmxcsr DWORD PTR [rbx+768]
	mov r11d, DWORD PTR [rbx+768]
	and r11d, 65535
	mov eax, 8127
	mov DWORD PTR [rbx+772], eax
	ldmxcsr DWORD PTR [rbx+772]
	lfence
	mov rcx, rbx
	mov r10, rcx
	add r10, 3328
	movabs r9, 780813969174497458
	mov QWORD PTR [r10], r9
	movabs r9, 500750640849553438
	mov QWORD PTR [r10+8], r9
	movabs r9, 699750412950110638
	mov QWORD PTR [r10+16], r9
	movabs r9, 907475776047809383
	mov QWORD PTR [r10+24], r9
	movabs r9, 887209886991712678
	mov QWORD PTR [r10+32], r9
	movabs r9, 493995344424799198
	mov QWORD PTR [r10+40], r9
	movabs r9, 66159908335518283
	mov QWORD PTR [r10+48], r9
	movabs r9, 471759160578149173
	mov QWORD PTR [r10+56], r9
	movabs r9, 610805677345344523
	mov QWORD PTR [r10+64], r9
	movabs r9, 169459648406555128
	mov QWORD PTR [r10+72], r9
	movabs r9, 41390488329585418
	mov QWORD PTR [r10+80], r9
	movabs r9, 622064504719934923
	mov QWORD PTR [r10+88], r9
	movabs r9, 245456732530542283
	mov QWORD PTR [r10+96], r9
	movabs r9, 43923724488868258
	mov QWORD PTR [r10+104], r9
	movabs r9, 838796929717305988
	mov QWORD PTR [r10+112], r9
	movabs r9, 21124599273488713
	mov QWORD PTR [r10+120], r9
	movabs r9, 767303376543154993
	mov QWORD PTR [r10+128], r9
	movabs r9, 412368846831682858
	mov QWORD PTR [r10+136], r9
	movabs r9, 765333081752601673
	mov QWORD PTR [r10+144], r9
	movabs r9, 828945455764539388
	mov QWORD PTR [r10+152], r9
	movabs r9, 594198907185989698
	mov QWORD PTR [r10+160], r9
	movabs r9, 334119997232777623
	mov QWORD PTR [r10+168], r9
	movabs r9, 375777658082430073
	mov QWORD PTR [r10+176], r9
	movabs r9, 466974159162114268
	mov QWORD PTR [r10+184], r9
	movabs r9, 359733829291804768
	mov QWORD PTR [r10+192], r9
	movabs r9, 244893791161812763
	mov QWORD PTR [r10+200], r9
	movabs r9, 713542476265817863
	mov QWORD PTR [r10+208], r9
	movabs r9, 802487211652417963
	mov QWORD PTR [r10+216], r9
	movabs r9, 656685398460468373
	mov QWORD PTR [r10+224], r9
	movabs r9, 508631820011766718
	mov QWORD PTR [r10+232], r9
	movabs r9, 658092751882292173
	mov QWORD PTR [r10+240], r9
	movabs r9, 478795927687268173
	mov QWORD PTR [r10+248], r9
	mov r9, rbx
	add r9, 1024
23:
	mov rdi, r13
	mov rsi, rbx
	mov r10, r9
	mov eax, 218172673
	vmovq xmm15, rax
	vpbroadcastd ymm15, xmm15
	lea r8, {VG_MLKEM_NTT_ZETAS}
	vmovdqu ymm12, YMMWORD PTR [r8+64]
	vmovdqu ymm13, YMMWORD PTR [r8+96]
	vmovdqu ymm4, YMMWORD PTR [rdi]
	vmovdqu ymm5, YMMWORD PTR [rdi+256]
	vpmullw ymm2, ymm5, ymm13
	vpmulhw ymm5, ymm5, ymm12
	vpmulhw ymm2, ymm2, ymm15
	vpsubw ymm5, ymm5, ymm2
	vpsubw ymm6, ymm4, ymm5
	vpaddw ymm4, ymm4, ymm5
	vmovdqu YMMWORD PTR [rsi+256], ymm4
	vmovdqu YMMWORD PTR [rsi+512], ymm6
	vmovdqu ymm4, YMMWORD PTR [rdi+32]
	vmovdqu ymm5, YMMWORD PTR [rdi+288]
	vpmullw ymm2, ymm5, ymm13
	vpmulhw ymm5, ymm5, ymm12
	vpmulhw ymm2, ymm2, ymm15
	vpsubw ymm5, ymm5, ymm2
	vpsubw ymm6, ymm4, ymm5
	vpaddw ymm4, ymm4, ymm5
	vmovdqu YMMWORD PTR [rsi+288], ymm4
	vmovdqu YMMWORD PTR [rsi+544], ymm6
	vmovdqu ymm4, YMMWORD PTR [rdi+64]
	vmovdqu ymm5, YMMWORD PTR [rdi+320]
	vpmullw ymm2, ymm5, ymm13
	vpmulhw ymm5, ymm5, ymm12
	vpmulhw ymm2, ymm2, ymm15
	vpsubw ymm5, ymm5, ymm2
	vpsubw ymm6, ymm4, ymm5
	vpaddw ymm4, ymm4, ymm5
	vmovdqu YMMWORD PTR [rsi+320], ymm4
	vmovdqu YMMWORD PTR [rsi+576], ymm6
	vmovdqu ymm4, YMMWORD PTR [rdi+96]
	vmovdqu ymm5, YMMWORD PTR [rdi+352]
	vpmullw ymm2, ymm5, ymm13
	vpmulhw ymm5, ymm5, ymm12
	vpmulhw ymm2, ymm2, ymm15
	vpsubw ymm5, ymm5, ymm2
	vpsubw ymm6, ymm4, ymm5
	vpaddw ymm4, ymm4, ymm5
	vmovdqu YMMWORD PTR [rsi+352], ymm4
	vmovdqu YMMWORD PTR [rsi+608], ymm6
	vmovdqu ymm4, YMMWORD PTR [rdi+128]
	vmovdqu ymm5, YMMWORD PTR [rdi+384]
	vpmullw ymm2, ymm5, ymm13
	vpmulhw ymm5, ymm5, ymm12
	vpmulhw ymm2, ymm2, ymm15
	vpsubw ymm5, ymm5, ymm2
	vpsubw ymm6, ymm4, ymm5
	vpaddw ymm4, ymm4, ymm5
	vmovdqu YMMWORD PTR [rsi+384], ymm4
	vmovdqu YMMWORD PTR [rsi+640], ymm6
	vmovdqu ymm4, YMMWORD PTR [rdi+160]
	vmovdqu ymm5, YMMWORD PTR [rdi+416]
	vpmullw ymm2, ymm5, ymm13
	vpmulhw ymm5, ymm5, ymm12
	vpmulhw ymm2, ymm2, ymm15
	vpsubw ymm5, ymm5, ymm2
	vpsubw ymm6, ymm4, ymm5
	vpaddw ymm4, ymm4, ymm5
	vmovdqu YMMWORD PTR [rsi+416], ymm4
	vmovdqu YMMWORD PTR [rsi+672], ymm6
	vmovdqu ymm4, YMMWORD PTR [rdi+192]
	vmovdqu ymm5, YMMWORD PTR [rdi+448]
	vpmullw ymm2, ymm5, ymm13
	vpmulhw ymm5, ymm5, ymm12
	vpmulhw ymm2, ymm2, ymm15
	vpsubw ymm5, ymm5, ymm2
	vpsubw ymm6, ymm4, ymm5
	vpaddw ymm4, ymm4, ymm5
	vmovdqu YMMWORD PTR [rsi+448], ymm4
	vmovdqu YMMWORD PTR [rsi+704], ymm6
	vmovdqu ymm4, YMMWORD PTR [rdi+224]
	vmovdqu ymm5, YMMWORD PTR [rdi+480]
	vpmullw ymm2, ymm5, ymm13
	vpmulhw ymm5, ymm5, ymm12
	vpmulhw ymm2, ymm2, ymm15
	vpsubw ymm5, ymm5, ymm2
	vpsubw ymm6, ymm4, ymm5
	vpaddw ymm4, ymm4, ymm5
	vmovdqu YMMWORD PTR [rsi+480], ymm4
	vmovdqu YMMWORD PTR [rsi+736], ymm6
	vmovdqu ymm0, YMMWORD PTR [rsi+256]
	vmovdqu ymm1, YMMWORD PTR [rsi+288]
	vmovdqu ymm2, YMMWORD PTR [rsi+320]
	vmovdqu ymm3, YMMWORD PTR [rsi+352]
	vmovdqu ymm4, YMMWORD PTR [rsi+384]
	vmovdqu ymm5, YMMWORD PTR [rsi+416]
	vmovdqu ymm6, YMMWORD PTR [rsi+448]
	vmovdqu ymm7, YMMWORD PTR [rsi+480]
	vmovdqu ymm8, YMMWORD PTR [r8+128]
	vmovdqu ymm9, YMMWORD PTR [r8+160]
	vpmullw ymm10, ymm4, ymm9
	vpmullw ymm12, ymm5, ymm9
	vpmulhw ymm4, ymm4, ymm8
	vpmulhw ymm5, ymm5, ymm8
	vpmulhw ymm10, ymm10, ymm15
	vpmulhw ymm12, ymm12, ymm15
	vpsubw ymm4, ymm4, ymm10
	vpsubw ymm5, ymm5, ymm12
	vpsubw ymm11, ymm0, ymm4
	vpsubw ymm13, ymm1, ymm5
	vpaddw ymm0, ymm0, ymm4
	vpaddw ymm1, ymm1, ymm5
	vmovdqu ymm14, YMMWORD PTR [r8+128]
	vmovdqu ymm10, YMMWORD PTR [r8+160]
	vpmullw ymm4, ymm6, ymm10
	vpmullw ymm5, ymm7, ymm10
	vpmulhw ymm6, ymm6, ymm14
	vpmulhw ymm7, ymm7, ymm14
	vpmulhw ymm4, ymm4, ymm15
	vpmulhw ymm5, ymm5, ymm15
	vpsubw ymm6, ymm6, ymm4
	vpsubw ymm7, ymm7, ymm5
	vpsubw ymm12, ymm2, ymm6
	vpsubw ymm8, ymm3, ymm7
	vpaddw ymm2, ymm2, ymm6
	vpaddw ymm3, ymm3, ymm7
	vmovdqu ymm9, YMMWORD PTR [r8+192]
	vmovdqu ymm4, YMMWORD PTR [r8+224]
	vpmullw ymm6, ymm2, ymm4
	vpmullw ymm7, ymm3, ymm4
	vpmulhw ymm2, ymm2, ymm9
	vpmulhw ymm3, ymm3, ymm9
	vpmulhw ymm6, ymm6, ymm15
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm2, ymm2, ymm6
	vpsubw ymm3, ymm3, ymm7
	vpsubw ymm5, ymm0, ymm2
	vpsubw ymm14, ymm1, ymm3
	vpaddw ymm0, ymm0, ymm2
	vpaddw ymm1, ymm1, ymm3
	vmovdqu ymm10, YMMWORD PTR [r8+256]
	vmovdqu ymm6, YMMWORD PTR [r8+288]
	vpmullw ymm2, ymm12, ymm6
	vpmullw ymm3, ymm8, ymm6
	vpmulhw ymm12, ymm12, ymm10
	vpmulhw ymm8, ymm8, ymm10
	vpmulhw ymm2, ymm2, ymm15
	vpmulhw ymm3, ymm3, ymm15
	vpsubw ymm12, ymm12, ymm2
	vpsubw ymm8, ymm8, ymm3
	vpsubw ymm7, ymm11, ymm12
	vpsubw ymm9, ymm13, ymm8
	vpaddw ymm11, ymm11, ymm12
	vpaddw ymm13, ymm13, ymm8
	vmovdqu ymm4, YMMWORD PTR [r8+320]
	vmovdqu ymm2, YMMWORD PTR [r8+352]
	vpmullw ymm12, ymm1, ymm2
	vpmulhw ymm1, ymm1, ymm4
	vpmulhw ymm12, ymm12, ymm15
	vpsubw ymm1, ymm1, ymm12
	vpsubw ymm3, ymm0, ymm1
	vpaddw ymm0, ymm0, ymm1
	vmovdqu ymm8, YMMWORD PTR [r8+384]
	vmovdqu ymm10, YMMWORD PTR [r8+416]
	vpmullw ymm6, ymm14, ymm10
	vpmulhw ymm14, ymm14, ymm8
	vpmulhw ymm6, ymm6, ymm15
	vpsubw ymm14, ymm14, ymm6
	vpsubw ymm12, ymm5, ymm14
	vpaddw ymm5, ymm5, ymm14
	vmovdqu ymm1, YMMWORD PTR [r8+448]
	vmovdqu ymm4, YMMWORD PTR [r8+480]
	vpmullw ymm2, ymm13, ymm4
	vpmulhw ymm13, ymm13, ymm1
	vpmulhw ymm2, ymm2, ymm15
	vpsubw ymm13, ymm13, ymm2
	vpsubw ymm6, ymm11, ymm13
	vpaddw ymm11, ymm11, ymm13
	vmovdqu ymm14, YMMWORD PTR [r8+512]
	vmovdqu ymm8, YMMWORD PTR [r8+544]
	vpmullw ymm10, ymm9, ymm8
	vpmulhw ymm9, ymm9, ymm14
	vpmulhw ymm10, ymm10, ymm15
	vpsubw ymm9, ymm9, ymm10
	vpsubw ymm2, ymm7, ymm9
	vpaddw ymm7, ymm7, ymm9
	vperm2i128 ymm13, ymm0, ymm3, 32
	vperm2i128 ymm3, ymm0, ymm3, 49
	vperm2i128 ymm1, ymm5, ymm12, 32
	vperm2i128 ymm12, ymm5, ymm12, 49
	vperm2i128 ymm4, ymm11, ymm6, 32
	vperm2i128 ymm6, ymm11, ymm6, 49
	vperm2i128 ymm10, ymm7, ymm2, 32
	vperm2i128 ymm2, ymm7, ymm2, 49
	vmovdqu ymm9, YMMWORD PTR [r8+576]
	vmovdqu ymm14, YMMWORD PTR [r8+608]
	vpmullw ymm8, ymm3, ymm14
	vpmulhw ymm3, ymm3, ymm9
	vpmulhw ymm8, ymm8, ymm15
	vpsubw ymm3, ymm3, ymm8
	vpsubw ymm0, ymm13, ymm3
	vpaddw ymm13, ymm13, ymm3
	vmovdqu ymm5, YMMWORD PTR [r8+640]
	vmovdqu ymm11, YMMWORD PTR [r8+672]
	vpmullw ymm7, ymm12, ymm11
	vpmulhw ymm12, ymm12, ymm5
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm12, ymm12, ymm7
	vpsubw ymm8, ymm1, ymm12
	vpaddw ymm1, ymm1, ymm12
	vmovdqu ymm3, YMMWORD PTR [r8+704]
	vmovdqu ymm9, YMMWORD PTR [r8+736]
	vpmullw ymm14, ymm6, ymm9
	vpmulhw ymm6, ymm6, ymm3
	vpmulhw ymm14, ymm14, ymm15
	vpsubw ymm6, ymm6, ymm14
	vpsubw ymm7, ymm4, ymm6
	vpaddw ymm4, ymm4, ymm6
	vmovdqu ymm12, YMMWORD PTR [r8+768]
	vmovdqu ymm5, YMMWORD PTR [r8+800]
	vpmullw ymm11, ymm2, ymm5
	vpmulhw ymm2, ymm2, ymm12
	vpmulhw ymm11, ymm11, ymm15
	vpsubw ymm2, ymm2, ymm11
	vpsubw ymm14, ymm10, ymm2
	vpaddw ymm10, ymm10, ymm2
	vpunpcklqdq ymm6, ymm13, ymm0
	vpunpckhqdq ymm0, ymm13, ymm0
	vpunpcklqdq ymm3, ymm1, ymm8
	vpunpckhqdq ymm8, ymm1, ymm8
	vpunpcklqdq ymm9, ymm4, ymm7
	vpunpckhqdq ymm7, ymm4, ymm7
	vpunpcklqdq ymm11, ymm10, ymm14
	vpunpckhqdq ymm14, ymm10, ymm14
	vmovdqu ymm2, YMMWORD PTR [r8+832]
	vmovdqu ymm12, YMMWORD PTR [r8+864]
	vpmullw ymm5, ymm0, ymm12
	vpmulhw ymm0, ymm0, ymm2
	vpmulhw ymm5, ymm5, ymm15
	vpsubw ymm0, ymm0, ymm5
	vpsubw ymm13, ymm6, ymm0
	vpaddw ymm6, ymm6, ymm0
	vmovdqu ymm1, YMMWORD PTR [r8+896]
	vmovdqu ymm4, YMMWORD PTR [r8+928]
	vpmullw ymm10, ymm8, ymm4
	vpmulhw ymm8, ymm8, ymm1
	vpmulhw ymm10, ymm10, ymm15
	vpsubw ymm8, ymm8, ymm10
	vpsubw ymm5, ymm3, ymm8
	vpaddw ymm3, ymm3, ymm8
	vmovdqu ymm0, YMMWORD PTR [r8+960]
	vmovdqu ymm2, YMMWORD PTR [r8+992]
	vpmullw ymm12, ymm7, ymm2
	vpmulhw ymm7, ymm7, ymm0
	vpmulhw ymm12, ymm12, ymm15
	vpsubw ymm7, ymm7, ymm12
	vpsubw ymm10, ymm9, ymm7
	vpaddw ymm9, ymm9, ymm7
	vmovdqu ymm8, YMMWORD PTR [r8+1024]
	vmovdqu ymm1, YMMWORD PTR [r8+1056]
	vpmullw ymm4, ymm14, ymm1
	vpmulhw ymm14, ymm14, ymm8
	vpmulhw ymm4, ymm4, ymm15
	vpsubw ymm14, ymm14, ymm4
	vpsubw ymm12, ymm11, ymm14
	vpaddw ymm11, ymm11, ymm14
	vpsllq ymm7, ymm13, 32
	vpblendd ymm7, ymm6, ymm7, 170
	vpsrlq ymm6, ymm6, 32
	vpblendd ymm13, ymm6, ymm13, 170
	vpsllq ymm0, ymm5, 32
	vpblendd ymm0, ymm3, ymm0, 170
	vpsrlq ymm3, ymm3, 32
	vpblendd ymm5, ymm3, ymm5, 170
	vpsllq ymm2, ymm10, 32
	vpblendd ymm2, ymm9, ymm2, 170
	vpsrlq ymm9, ymm9, 32
	vpblendd ymm10, ymm9, ymm10, 170
	vpsllq ymm4, ymm12, 32
	vpblendd ymm4, ymm11, ymm4, 170
	vpsrlq ymm11, ymm11, 32
	vpblendd ymm12, ymm11, ymm12, 170
	vmovdqu ymm14, YMMWORD PTR [r8+1088]
	vmovdqu ymm8, YMMWORD PTR [r8+1120]
	vpmullw ymm1, ymm13, ymm8
	vpmulhw ymm13, ymm13, ymm14
	vpmulhw ymm1, ymm1, ymm15
	vpsubw ymm13, ymm13, ymm1
	vpsubw ymm6, ymm7, ymm13
	vpaddw ymm7, ymm7, ymm13
	vmovdqu ymm3, YMMWORD PTR [r8+1152]
	vmovdqu ymm9, YMMWORD PTR [r8+1184]
	vpmullw ymm11, ymm5, ymm9
	vpmulhw ymm5, ymm5, ymm3
	vpmulhw ymm11, ymm11, ymm15
	vpsubw ymm5, ymm5, ymm11
	vpsubw ymm1, ymm0, ymm5
	vpaddw ymm0, ymm0, ymm5
	vmovdqu ymm13, YMMWORD PTR [r8+1216]
	vmovdqu ymm14, YMMWORD PTR [r8+1248]
	vpmullw ymm8, ymm10, ymm14
	vpmulhw ymm10, ymm10, ymm13
	vpmulhw ymm8, ymm8, ymm15
	vpsubw ymm10, ymm10, ymm8
	vpsubw ymm11, ymm2, ymm10
	vpaddw ymm2, ymm2, ymm10
	vmovdqu ymm5, YMMWORD PTR [r8+1280]
	vmovdqu ymm3, YMMWORD PTR [r8+1312]
	vpmullw ymm9, ymm12, ymm3
	vpmulhw ymm12, ymm12, ymm5
	vpmulhw ymm9, ymm9, ymm15
	vpsubw ymm12, ymm12, ymm9
	vpsubw ymm8, ymm4, ymm12
	vpaddw ymm4, ymm4, ymm12
	vmovdqu ymm10, YMMWORD PTR [r8]
	vmovdqu ymm13, YMMWORD PTR [r8+32]
	vpmullw ymm14, ymm7, ymm13
	vpmulhw ymm7, ymm7, ymm10
	vpmulhw ymm14, ymm14, ymm15
	vpsubw ymm7, ymm7, ymm14
	vpsraw ymm14, ymm7, 15
	vpand ymm14, ymm14, ymm15
	vpaddw ymm7, ymm7, ymm14
	vpmullw ymm9, ymm6, ymm13
	vpmulhw ymm6, ymm6, ymm10
	vpmulhw ymm9, ymm9, ymm15
	vpsubw ymm6, ymm6, ymm9
	vpsraw ymm9, ymm6, 15
	vpand ymm9, ymm9, ymm15
	vpaddw ymm6, ymm6, ymm9
	vpmullw ymm12, ymm0, ymm13
	vpmulhw ymm0, ymm0, ymm10
	vpmulhw ymm12, ymm12, ymm15
	vpsubw ymm0, ymm0, ymm12
	vpsraw ymm12, ymm0, 15
	vpand ymm12, ymm12, ymm15
	vpaddw ymm0, ymm0, ymm12
	vpmullw ymm5, ymm1, ymm13
	vpmulhw ymm1, ymm1, ymm10
	vpmulhw ymm5, ymm5, ymm15
	vpsubw ymm1, ymm1, ymm5
	vpsraw ymm5, ymm1, 15
	vpand ymm5, ymm5, ymm15
	vpaddw ymm1, ymm1, ymm5
	vpmullw ymm3, ymm2, ymm13
	vpmulhw ymm2, ymm2, ymm10
	vpmulhw ymm3, ymm3, ymm15
	vpsubw ymm2, ymm2, ymm3
	vpsraw ymm3, ymm2, 15
	vpand ymm3, ymm3, ymm15
	vpaddw ymm2, ymm2, ymm3
	vpmullw ymm14, ymm11, ymm13
	vpmulhw ymm11, ymm11, ymm10
	vpmulhw ymm14, ymm14, ymm15
	vpsubw ymm11, ymm11, ymm14
	vpsraw ymm14, ymm11, 15
	vpand ymm14, ymm14, ymm15
	vpaddw ymm11, ymm11, ymm14
	vpmullw ymm9, ymm4, ymm13
	vpmulhw ymm4, ymm4, ymm10
	vpmulhw ymm9, ymm9, ymm15
	vpsubw ymm4, ymm4, ymm9
	vpsraw ymm9, ymm4, 15
	vpand ymm9, ymm9, ymm15
	vpaddw ymm4, ymm4, ymm9
	vpmullw ymm12, ymm8, ymm13
	vpmulhw ymm8, ymm8, ymm10
	vpmulhw ymm12, ymm12, ymm15
	vpsubw ymm8, ymm8, ymm12
	vpsraw ymm12, ymm8, 15
	vpand ymm12, ymm12, ymm15
	vpaddw ymm8, ymm8, ymm12
	vpunpcklwd ymm5, ymm7, ymm6
	vpunpckhwd ymm6, ymm7, ymm6
	vpunpckldq ymm3, ymm5, ymm6
	vpunpckhdq ymm6, ymm5, ymm6
	vpunpcklqdq ymm14, ymm3, ymm6
	vpunpckhqdq ymm6, ymm3, ymm6
	vpermq ymm14, ymm14, 216
	vpermq ymm6, ymm6, 216
	vmovdqu YMMWORD PTR [r10], ymm14
	vmovdqu YMMWORD PTR [r10+32], ymm6
	vpunpcklwd ymm9, ymm0, ymm1
	vpunpckhwd ymm1, ymm0, ymm1
	vpunpckldq ymm12, ymm9, ymm1
	vpunpckhdq ymm1, ymm9, ymm1
	vpunpcklqdq ymm10, ymm12, ymm1
	vpunpckhqdq ymm1, ymm12, ymm1
	vpermq ymm10, ymm10, 216
	vpermq ymm1, ymm1, 216
	vmovdqu YMMWORD PTR [r10+64], ymm10
	vmovdqu YMMWORD PTR [r10+96], ymm1
	vpunpcklwd ymm13, ymm2, ymm11
	vpunpckhwd ymm11, ymm2, ymm11
	vpunpckldq ymm7, ymm13, ymm11
	vpunpckhdq ymm11, ymm13, ymm11
	vpunpcklqdq ymm5, ymm7, ymm11
	vpunpckhqdq ymm11, ymm7, ymm11
	vpermq ymm5, ymm5, 216
	vpermq ymm11, ymm11, 216
	vmovdqu YMMWORD PTR [r10+128], ymm5
	vmovdqu YMMWORD PTR [r10+160], ymm11
	vpunpcklwd ymm3, ymm4, ymm8
	vpunpckhwd ymm8, ymm4, ymm8
	vpunpckldq ymm0, ymm3, ymm8
	vpunpckhdq ymm8, ymm3, ymm8
	vpunpcklqdq ymm9, ymm0, ymm8
	vpunpckhqdq ymm8, ymm0, ymm8
	vpermq ymm9, ymm9, 216
	vpermq ymm8, ymm8, 216
	vmovdqu YMMWORD PTR [r10+192], ymm9
	vmovdqu YMMWORD PTR [r10+224], ymm8
	vmovdqu ymm0, YMMWORD PTR [rsi+512]
	vmovdqu ymm1, YMMWORD PTR [rsi+544]
	vmovdqu ymm2, YMMWORD PTR [rsi+576]
	vmovdqu ymm3, YMMWORD PTR [rsi+608]
	vmovdqu ymm4, YMMWORD PTR [rsi+640]
	vmovdqu ymm5, YMMWORD PTR [rsi+672]
	vmovdqu ymm6, YMMWORD PTR [rsi+704]
	vmovdqu ymm7, YMMWORD PTR [rsi+736]
	vmovdqu ymm8, YMMWORD PTR [r8+1344]
	vmovdqu ymm9, YMMWORD PTR [r8+1376]
	vpmullw ymm10, ymm4, ymm9
	vpmullw ymm12, ymm5, ymm9
	vpmulhw ymm4, ymm4, ymm8
	vpmulhw ymm5, ymm5, ymm8
	vpmulhw ymm10, ymm10, ymm15
	vpmulhw ymm12, ymm12, ymm15
	vpsubw ymm4, ymm4, ymm10
	vpsubw ymm5, ymm5, ymm12
	vpsubw ymm11, ymm0, ymm4
	vpsubw ymm13, ymm1, ymm5
	vpaddw ymm0, ymm0, ymm4
	vpaddw ymm1, ymm1, ymm5
	vmovdqu ymm14, YMMWORD PTR [r8+1344]
	vmovdqu ymm10, YMMWORD PTR [r8+1376]
	vpmullw ymm4, ymm6, ymm10
	vpmullw ymm5, ymm7, ymm10
	vpmulhw ymm6, ymm6, ymm14
	vpmulhw ymm7, ymm7, ymm14
	vpmulhw ymm4, ymm4, ymm15
	vpmulhw ymm5, ymm5, ymm15
	vpsubw ymm6, ymm6, ymm4
	vpsubw ymm7, ymm7, ymm5
	vpsubw ymm12, ymm2, ymm6
	vpsubw ymm8, ymm3, ymm7
	vpaddw ymm2, ymm2, ymm6
	vpaddw ymm3, ymm3, ymm7
	vmovdqu ymm9, YMMWORD PTR [r8+1408]
	vmovdqu ymm4, YMMWORD PTR [r8+1440]
	vpmullw ymm6, ymm2, ymm4
	vpmullw ymm7, ymm3, ymm4
	vpmulhw ymm2, ymm2, ymm9
	vpmulhw ymm3, ymm3, ymm9
	vpmulhw ymm6, ymm6, ymm15
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm2, ymm2, ymm6
	vpsubw ymm3, ymm3, ymm7
	vpsubw ymm5, ymm0, ymm2
	vpsubw ymm14, ymm1, ymm3
	vpaddw ymm0, ymm0, ymm2
	vpaddw ymm1, ymm1, ymm3
	vmovdqu ymm10, YMMWORD PTR [r8+1472]
	vmovdqu ymm6, YMMWORD PTR [r8+1504]
	vpmullw ymm2, ymm12, ymm6
	vpmullw ymm3, ymm8, ymm6
	vpmulhw ymm12, ymm12, ymm10
	vpmulhw ymm8, ymm8, ymm10
	vpmulhw ymm2, ymm2, ymm15
	vpmulhw ymm3, ymm3, ymm15
	vpsubw ymm12, ymm12, ymm2
	vpsubw ymm8, ymm8, ymm3
	vpsubw ymm7, ymm11, ymm12
	vpsubw ymm9, ymm13, ymm8
	vpaddw ymm11, ymm11, ymm12
	vpaddw ymm13, ymm13, ymm8
	vmovdqu ymm4, YMMWORD PTR [r8+1536]
	vmovdqu ymm2, YMMWORD PTR [r8+1568]
	vpmullw ymm12, ymm1, ymm2
	vpmulhw ymm1, ymm1, ymm4
	vpmulhw ymm12, ymm12, ymm15
	vpsubw ymm1, ymm1, ymm12
	vpsubw ymm3, ymm0, ymm1
	vpaddw ymm0, ymm0, ymm1
	vmovdqu ymm8, YMMWORD PTR [r8+1600]
	vmovdqu ymm10, YMMWORD PTR [r8+1632]
	vpmullw ymm6, ymm14, ymm10
	vpmulhw ymm14, ymm14, ymm8
	vpmulhw ymm6, ymm6, ymm15
	vpsubw ymm14, ymm14, ymm6
	vpsubw ymm12, ymm5, ymm14
	vpaddw ymm5, ymm5, ymm14
	vmovdqu ymm1, YMMWORD PTR [r8+1664]
	vmovdqu ymm4, YMMWORD PTR [r8+1696]
	vpmullw ymm2, ymm13, ymm4
	vpmulhw ymm13, ymm13, ymm1
	vpmulhw ymm2, ymm2, ymm15
	vpsubw ymm13, ymm13, ymm2
	vpsubw ymm6, ymm11, ymm13
	vpaddw ymm11, ymm11, ymm13
	vmovdqu ymm14, YMMWORD PTR [r8+1728]
	vmovdqu ymm8, YMMWORD PTR [r8+1760]
	vpmullw ymm10, ymm9, ymm8
	vpmulhw ymm9, ymm9, ymm14
	vpmulhw ymm10, ymm10, ymm15
	vpsubw ymm9, ymm9, ymm10
	vpsubw ymm2, ymm7, ymm9
	vpaddw ymm7, ymm7, ymm9
	vperm2i128 ymm13, ymm0, ymm3, 32
	vperm2i128 ymm3, ymm0, ymm3, 49
	vperm2i128 ymm1, ymm5, ymm12, 32
	vperm2i128 ymm12, ymm5, ymm12, 49
	vperm2i128 ymm4, ymm11, ymm6, 32
	vperm2i128 ymm6, ymm11, ymm6, 49
	vperm2i128 ymm10, ymm7, ymm2, 32
	vperm2i128 ymm2, ymm7, ymm2, 49
	vmovdqu ymm9, YMMWORD PTR [r8+1792]
	vmovdqu ymm14, YMMWORD PTR [r8+1824]
	vpmullw ymm8, ymm3, ymm14
	vpmulhw ymm3, ymm3, ymm9
	vpmulhw ymm8, ymm8, ymm15
	vpsubw ymm3, ymm3, ymm8
	vpsubw ymm0, ymm13, ymm3
	vpaddw ymm13, ymm13, ymm3
	vmovdqu ymm5, YMMWORD PTR [r8+1856]
	vmovdqu ymm11, YMMWORD PTR [r8+1888]
	vpmullw ymm7, ymm12, ymm11
	vpmulhw ymm12, ymm12, ymm5
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm12, ymm12, ymm7
	vpsubw ymm8, ymm1, ymm12
	vpaddw ymm1, ymm1, ymm12
	vmovdqu ymm3, YMMWORD PTR [r8+1920]
	vmovdqu ymm9, YMMWORD PTR [r8+1952]
	vpmullw ymm14, ymm6, ymm9
	vpmulhw ymm6, ymm6, ymm3
	vpmulhw ymm14, ymm14, ymm15
	vpsubw ymm6, ymm6, ymm14
	vpsubw ymm7, ymm4, ymm6
	vpaddw ymm4, ymm4, ymm6
	vmovdqu ymm12, YMMWORD PTR [r8+1984]
	vmovdqu ymm5, YMMWORD PTR [r8+2016]
	vpmullw ymm11, ymm2, ymm5
	vpmulhw ymm2, ymm2, ymm12
	vpmulhw ymm11, ymm11, ymm15
	vpsubw ymm2, ymm2, ymm11
	vpsubw ymm14, ymm10, ymm2
	vpaddw ymm10, ymm10, ymm2
	vpunpcklqdq ymm6, ymm13, ymm0
	vpunpckhqdq ymm0, ymm13, ymm0
	vpunpcklqdq ymm3, ymm1, ymm8
	vpunpckhqdq ymm8, ymm1, ymm8
	vpunpcklqdq ymm9, ymm4, ymm7
	vpunpckhqdq ymm7, ymm4, ymm7
	vpunpcklqdq ymm11, ymm10, ymm14
	vpunpckhqdq ymm14, ymm10, ymm14
	vmovdqu ymm2, YMMWORD PTR [r8+2048]
	vmovdqu ymm12, YMMWORD PTR [r8+2080]
	vpmullw ymm5, ymm0, ymm12
	vpmulhw ymm0, ymm0, ymm2
	vpmulhw ymm5, ymm5, ymm15
	vpsubw ymm0, ymm0, ymm5
	vpsubw ymm13, ymm6, ymm0
	vpaddw ymm6, ymm6, ymm0
	vmovdqu ymm1, YMMWORD PTR [r8+2112]
	vmovdqu ymm4, YMMWORD PTR [r8+2144]
	vpmullw ymm10, ymm8, ymm4
	vpmulhw ymm8, ymm8, ymm1
	vpmulhw ymm10, ymm10, ymm15
	vpsubw ymm8, ymm8, ymm10
	vpsubw ymm5, ymm3, ymm8
	vpaddw ymm3, ymm3, ymm8
	vmovdqu ymm0, YMMWORD PTR [r8+2176]
	vmovdqu ymm2, YMMWORD PTR [r8+2208]
	vpmullw ymm12, ymm7, ymm2
	vpmulhw ymm7, ymm7, ymm0
	vpmulhw ymm12, ymm12, ymm15
	vpsubw ymm7, ymm7, ymm12
	vpsubw ymm10, ymm9, ymm7
	vpaddw ymm9, ymm9, ymm7
	vmovdqu ymm8, YMMWORD PTR [r8+2240]
	vmovdqu ymm1, YMMWORD PTR [r8+2272]
	vpmullw ymm4, ymm14, ymm1
	vpmulhw ymm14, ymm14, ymm8
	vpmulhw ymm4, ymm4, ymm15
	vpsubw ymm14, ymm14, ymm4
	vpsubw ymm12, ymm11, ymm14
	vpaddw ymm11, ymm11, ymm14
	vpsllq ymm7, ymm13, 32
	vpblendd ymm7, ymm6, ymm7, 170
	vpsrlq ymm6, ymm6, 32
	vpblendd ymm13, ymm6, ymm13, 170
	vpsllq ymm0, ymm5, 32
	vpblendd ymm0, ymm3, ymm0, 170
	vpsrlq ymm3, ymm3, 32
	vpblendd ymm5, ymm3, ymm5, 170
	vpsllq ymm2, ymm10, 32
	vpblendd ymm2, ymm9, ymm2, 170
	vpsrlq ymm9, ymm9, 32
	vpblendd ymm10, ymm9, ymm10, 170
	vpsllq ymm4, ymm12, 32
	vpblendd ymm4, ymm11, ymm4, 170
	vpsrlq ymm11, ymm11, 32
	vpblendd ymm12, ymm11, ymm12, 170
	vmovdqu ymm14, YMMWORD PTR [r8+2304]
	vmovdqu ymm8, YMMWORD PTR [r8+2336]
	vpmullw ymm1, ymm13, ymm8
	vpmulhw ymm13, ymm13, ymm14
	vpmulhw ymm1, ymm1, ymm15
	vpsubw ymm13, ymm13, ymm1
	vpsubw ymm6, ymm7, ymm13
	vpaddw ymm7, ymm7, ymm13
	vmovdqu ymm3, YMMWORD PTR [r8+2368]
	vmovdqu ymm9, YMMWORD PTR [r8+2400]
	vpmullw ymm11, ymm5, ymm9
	vpmulhw ymm5, ymm5, ymm3
	vpmulhw ymm11, ymm11, ymm15
	vpsubw ymm5, ymm5, ymm11
	vpsubw ymm1, ymm0, ymm5
	vpaddw ymm0, ymm0, ymm5
	vmovdqu ymm13, YMMWORD PTR [r8+2432]
	vmovdqu ymm14, YMMWORD PTR [r8+2464]
	vpmullw ymm8, ymm10, ymm14
	vpmulhw ymm10, ymm10, ymm13
	vpmulhw ymm8, ymm8, ymm15
	vpsubw ymm10, ymm10, ymm8
	vpsubw ymm11, ymm2, ymm10
	vpaddw ymm2, ymm2, ymm10
	vmovdqu ymm5, YMMWORD PTR [r8+2496]
	vmovdqu ymm3, YMMWORD PTR [r8+2528]
	vpmullw ymm9, ymm12, ymm3
	vpmulhw ymm12, ymm12, ymm5
	vpmulhw ymm9, ymm9, ymm15
	vpsubw ymm12, ymm12, ymm9
	vpsubw ymm8, ymm4, ymm12
	vpaddw ymm4, ymm4, ymm12
	vmovdqu ymm10, YMMWORD PTR [r8]
	vmovdqu ymm13, YMMWORD PTR [r8+32]
	vpmullw ymm14, ymm7, ymm13
	vpmulhw ymm7, ymm7, ymm10
	vpmulhw ymm14, ymm14, ymm15
	vpsubw ymm7, ymm7, ymm14
	vpsraw ymm14, ymm7, 15
	vpand ymm14, ymm14, ymm15
	vpaddw ymm7, ymm7, ymm14
	vpmullw ymm9, ymm6, ymm13
	vpmulhw ymm6, ymm6, ymm10
	vpmulhw ymm9, ymm9, ymm15
	vpsubw ymm6, ymm6, ymm9
	vpsraw ymm9, ymm6, 15
	vpand ymm9, ymm9, ymm15
	vpaddw ymm6, ymm6, ymm9
	vpmullw ymm12, ymm0, ymm13
	vpmulhw ymm0, ymm0, ymm10
	vpmulhw ymm12, ymm12, ymm15
	vpsubw ymm0, ymm0, ymm12
	vpsraw ymm12, ymm0, 15
	vpand ymm12, ymm12, ymm15
	vpaddw ymm0, ymm0, ymm12
	vpmullw ymm5, ymm1, ymm13
	vpmulhw ymm1, ymm1, ymm10
	vpmulhw ymm5, ymm5, ymm15
	vpsubw ymm1, ymm1, ymm5
	vpsraw ymm5, ymm1, 15
	vpand ymm5, ymm5, ymm15
	vpaddw ymm1, ymm1, ymm5
	vpmullw ymm3, ymm2, ymm13
	vpmulhw ymm2, ymm2, ymm10
	vpmulhw ymm3, ymm3, ymm15
	vpsubw ymm2, ymm2, ymm3
	vpsraw ymm3, ymm2, 15
	vpand ymm3, ymm3, ymm15
	vpaddw ymm2, ymm2, ymm3
	vpmullw ymm14, ymm11, ymm13
	vpmulhw ymm11, ymm11, ymm10
	vpmulhw ymm14, ymm14, ymm15
	vpsubw ymm11, ymm11, ymm14
	vpsraw ymm14, ymm11, 15
	vpand ymm14, ymm14, ymm15
	vpaddw ymm11, ymm11, ymm14
	vpmullw ymm9, ymm4, ymm13
	vpmulhw ymm4, ymm4, ymm10
	vpmulhw ymm9, ymm9, ymm15
	vpsubw ymm4, ymm4, ymm9
	vpsraw ymm9, ymm4, 15
	vpand ymm9, ymm9, ymm15
	vpaddw ymm4, ymm4, ymm9
	vpmullw ymm12, ymm8, ymm13
	vpmulhw ymm8, ymm8, ymm10
	vpmulhw ymm12, ymm12, ymm15
	vpsubw ymm8, ymm8, ymm12
	vpsraw ymm12, ymm8, 15
	vpand ymm12, ymm12, ymm15
	vpaddw ymm8, ymm8, ymm12
	vpunpcklwd ymm5, ymm7, ymm6
	vpunpckhwd ymm6, ymm7, ymm6
	vpunpckldq ymm3, ymm5, ymm6
	vpunpckhdq ymm6, ymm5, ymm6
	vpunpcklqdq ymm14, ymm3, ymm6
	vpunpckhqdq ymm6, ymm3, ymm6
	vpermq ymm14, ymm14, 216
	vpermq ymm6, ymm6, 216
	vmovdqu YMMWORD PTR [r10+256], ymm14
	vmovdqu YMMWORD PTR [r10+288], ymm6
	vpunpcklwd ymm9, ymm0, ymm1
	vpunpckhwd ymm1, ymm0, ymm1
	vpunpckldq ymm12, ymm9, ymm1
	vpunpckhdq ymm1, ymm9, ymm1
	vpunpcklqdq ymm10, ymm12, ymm1
	vpunpckhqdq ymm1, ymm12, ymm1
	vpermq ymm10, ymm10, 216
	vpermq ymm1, ymm1, 216
	vmovdqu YMMWORD PTR [r10+320], ymm10
	vmovdqu YMMWORD PTR [r10+352], ymm1
	vpunpcklwd ymm13, ymm2, ymm11
	vpunpckhwd ymm11, ymm2, ymm11
	vpunpckldq ymm7, ymm13, ymm11
	vpunpckhdq ymm11, ymm13, ymm11
	vpunpcklqdq ymm5, ymm7, ymm11
	vpunpckhqdq ymm11, ymm7, ymm11
	vpermq ymm5, ymm5, 216
	vpermq ymm11, ymm11, 216
	vmovdqu YMMWORD PTR [r10+384], ymm5
	vmovdqu YMMWORD PTR [r10+416], ymm11
	vpunpcklwd ymm3, ymm4, ymm8
	vpunpckhwd ymm8, ymm4, ymm8
	vpunpckldq ymm0, ymm3, ymm8
	vpunpckhdq ymm8, ymm3, ymm8
	vpunpcklqdq ymm9, ymm0, ymm8
	vpunpckhqdq ymm8, ymm0, ymm8
	vpermq ymm9, ymm9, 216
	vpermq ymm8, ymm8, 216
	vmovdqu YMMWORD PTR [r10+448], ymm9
	vmovdqu YMMWORD PTR [r10+480], ymm8
	vzeroupper
	add r13, 512
	add r9, 512
	sub r14, 1
	jne 23b
	mov r14d, 3
24:
	mov rdi, rbp
	mov rsi, r12
	mov rdx, rbx
	add rdx, 1024
	mov rcx, rbx
	mov eax, 218172673
	vmovq xmm15, rax
	vpbroadcastd ymm15, xmm15
	mov eax, -217976063
	vmovq xmm14, rax
	vpbroadcastd ymm14, xmm14
	mov r8, rcx
	add r8, 3328
	mov ecx, 8
25:
	vmovdqu ymm13, YMMWORD PTR [r8]
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vpermq ymm0, ymm0, 216
	vpermq ymm1, ymm1, 216
	vpsrld ymm4, ymm0, 16
	vpsrld ymm5, ymm1, 16
	vpslld ymm0, ymm0, 16
	vpsrld ymm0, ymm0, 16
	vpslld ymm1, ymm1, 16
	vpsrld ymm1, ymm1, 16
	vpackssdw ymm0, ymm0, ymm1
	vpackssdw ymm4, ymm4, ymm5
	vmovdqu ymm6, YMMWORD PTR [rdx]
	vmovdqu ymm10, YMMWORD PTR [rdx+32]
	vmovdqa ymm1, ymm4
	vpmullw ymm2, ymm1, ymm10
	vpmullw ymm2, ymm2, ymm14
	vpmulhw ymm1, ymm1, ymm10
	vpmulhw ymm2, ymm2, ymm15
	vpsubw ymm1, ymm1, ymm2
	vpmullw ymm2, ymm1, ymm13
	vpmullw ymm2, ymm2, ymm14
	vpmulhw ymm1, ymm1, ymm13
	vpmulhw ymm2, ymm2, ymm15
	vpsubw ymm1, ymm1, ymm2
	vmovdqa ymm2, ymm0
	vpmullw ymm3, ymm2, ymm6
	vpmullw ymm3, ymm3, ymm14
	vpmulhw ymm2, ymm2, ymm6
	vpmulhw ymm3, ymm3, ymm15
	vpsubw ymm2, ymm2, ymm3
	vpaddw ymm1, ymm1, ymm2
	vmovdqa ymm2, ymm0
	vpmullw ymm3, ymm2, ymm10
	vpmullw ymm3, ymm3, ymm14
	vpmulhw ymm2, ymm2, ymm10
	vpmulhw ymm3, ymm3, ymm15
	vpsubw ymm2, ymm2, ymm3
	vpmullw ymm3, ymm4, ymm6
	vpmullw ymm3, ymm3, ymm14
	vpmulhw ymm4, ymm4, ymm6
	vpmulhw ymm3, ymm3, ymm15
	vpsubw ymm4, ymm4, ymm3
	vpaddw ymm2, ymm2, ymm4
	vmovdqa ymm11, ymm1
	vmovdqa ymm12, ymm2
	vmovdqu ymm0, YMMWORD PTR [rsi+1536]
	vmovdqu ymm1, YMMWORD PTR [rsi+1568]
	vpermq ymm0, ymm0, 216
	vpermq ymm1, ymm1, 216
	vpsrld ymm4, ymm0, 16
	vpsrld ymm5, ymm1, 16
	vpslld ymm0, ymm0, 16
	vpsrld ymm0, ymm0, 16
	vpslld ymm1, ymm1, 16
	vpsrld ymm1, ymm1, 16
	vpackssdw ymm0, ymm0, ymm1
	vpackssdw ymm4, ymm4, ymm5
	vmovdqu ymm6, YMMWORD PTR [rdx+512]
	vmovdqu ymm10, YMMWORD PTR [rdx+544]
	vmovdqa ymm1, ymm4
	vpmullw ymm2, ymm1, ymm10
	vpmullw ymm2, ymm2, ymm14
	vpmulhw ymm1, ymm1, ymm10
	vpmulhw ymm2, ymm2, ymm15
	vpsubw ymm1, ymm1, ymm2
	vpmullw ymm2, ymm1, ymm13
	vpmullw ymm2, ymm2, ymm14
	vpmulhw ymm1, ymm1, ymm13
	vpmulhw ymm2, ymm2, ymm15
	vpsubw ymm1, ymm1, ymm2
	vmovdqa ymm2, ymm0
	vpmullw ymm3, ymm2, ymm6
	vpmullw ymm3, ymm3, ymm14
	vpmulhw ymm2, ymm2, ymm6
	vpmulhw ymm3, ymm3, ymm15
	vpsubw ymm2, ymm2, ymm3
	vpaddw ymm1, ymm1, ymm2
	vmovdqa ymm2, ymm0
	vpmullw ymm3, ymm2, ymm10
	vpmullw ymm3, ymm3, ymm14
	vpmulhw ymm2, ymm2, ymm10
	vpmulhw ymm3, ymm3, ymm15
	vpsubw ymm2, ymm2, ymm3
	vpmullw ymm3, ymm4, ymm6
	vpmullw ymm3, ymm3, ymm14
	vpmulhw ymm4, ymm4, ymm6
	vpmulhw ymm3, ymm3, ymm15
	vpsubw ymm4, ymm4, ymm3
	vpaddw ymm2, ymm2, ymm4
	vpaddw ymm11, ymm11, ymm1
	vpaddw ymm12, ymm12, ymm2
	vmovdqu ymm0, YMMWORD PTR [rsi+3072]
	vmovdqu ymm1, YMMWORD PTR [rsi+3104]
	vpermq ymm0, ymm0, 216
	vpermq ymm1, ymm1, 216
	vpsrld ymm4, ymm0, 16
	vpsrld ymm5, ymm1, 16
	vpslld ymm0, ymm0, 16
	vpsrld ymm0, ymm0, 16
	vpslld ymm1, ymm1, 16
	vpsrld ymm1, ymm1, 16
	vpackssdw ymm0, ymm0, ymm1
	vpackssdw ymm4, ymm4, ymm5
	vmovdqu ymm6, YMMWORD PTR [rdx+1024]
	vmovdqu ymm10, YMMWORD PTR [rdx+1056]
	vmovdqa ymm1, ymm4
	vpmullw ymm2, ymm1, ymm10
	vpmullw ymm2, ymm2, ymm14
	vpmulhw ymm1, ymm1, ymm10
	vpmulhw ymm2, ymm2, ymm15
	vpsubw ymm1, ymm1, ymm2
	vpmullw ymm2, ymm1, ymm13
	vpmullw ymm2, ymm2, ymm14
	vpmulhw ymm1, ymm1, ymm13
	vpmulhw ymm2, ymm2, ymm15
	vpsubw ymm1, ymm1, ymm2
	vmovdqa ymm2, ymm0
	vpmullw ymm3, ymm2, ymm6
	vpmullw ymm3, ymm3, ymm14
	vpmulhw ymm2, ymm2, ymm6
	vpmulhw ymm3, ymm3, ymm15
	vpsubw ymm2, ymm2, ymm3
	vpaddw ymm1, ymm1, ymm2
	vmovdqa ymm2, ymm0
	vpmullw ymm3, ymm2, ymm10
	vpmullw ymm3, ymm3, ymm14
	vpmulhw ymm2, ymm2, ymm10
	vpmulhw ymm3, ymm3, ymm15
	vpsubw ymm2, ymm2, ymm3
	vpmullw ymm3, ymm4, ymm6
	vpmullw ymm3, ymm3, ymm14
	vpmulhw ymm4, ymm4, ymm6
	vpmulhw ymm3, ymm3, ymm15
	vpsubw ymm4, ymm4, ymm3
	vpaddw ymm2, ymm2, ymm4
	vpaddw ymm11, ymm11, ymm1
	vpaddw ymm12, ymm12, ymm2
	mov eax, 88671561
	vmovq xmm13, rax
	vpbroadcastd ymm13, xmm13
	vpmullw ymm3, ymm11, ymm13
	vpmullw ymm3, ymm3, ymm14
	vpmulhw ymm11, ymm11, ymm13
	vpmulhw ymm3, ymm3, ymm15
	vpsubw ymm11, ymm11, ymm3
	vpsraw ymm3, ymm11, 15
	vpand ymm3, ymm3, ymm15
	vpaddw ymm11, ymm11, ymm3
	vpmullw ymm3, ymm12, ymm13
	vpmullw ymm3, ymm3, ymm14
	vpmulhw ymm12, ymm12, ymm13
	vpmulhw ymm3, ymm3, ymm15
	vpsubw ymm12, ymm12, ymm3
	vpsraw ymm3, ymm12, 15
	vpand ymm3, ymm3, ymm15
	vpaddw ymm12, ymm12, ymm3
	vmovdqu YMMWORD PTR [rdi], ymm11
	vmovdqu YMMWORD PTR [rdi+32], ymm12
	add rsi, 64
	add rdx, 64
	add rdi, 64
	add r8, 32
	sub rcx, 1
	jne 25b
	mov rdi, rbp
	mov rsi, rbx
	mov eax, 218172673
	vmovq xmm15, rax
	vpbroadcastd ymm15, xmm15
	lea r8, {VG_MLKEM_NTT_ZETAS}
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vmovdqu ymm1, YMMWORD PTR [rdi+32]
	vpunpcklwd ymm8, ymm0, ymm1
	vpunpckhwd ymm1, ymm0, ymm1
	vmovdqu ymm2, YMMWORD PTR [rdi+64]
	vmovdqu ymm3, YMMWORD PTR [rdi+96]
	vpunpcklwd ymm9, ymm2, ymm3
	vpunpckhwd ymm3, ymm2, ymm3
	vmovdqu ymm4, YMMWORD PTR [rdi+128]
	vmovdqu ymm5, YMMWORD PTR [rdi+160]
	vpunpcklwd ymm10, ymm4, ymm5
	vpunpckhwd ymm5, ymm4, ymm5
	vmovdqu ymm6, YMMWORD PTR [rdi+192]
	vmovdqu ymm7, YMMWORD PTR [rdi+224]
	vpunpcklwd ymm11, ymm6, ymm7
	vpunpckhwd ymm7, ymm6, ymm7
	vperm2i128 ymm12, ymm8, ymm1, 32
	vperm2i128 ymm1, ymm8, ymm1, 49
	vperm2i128 ymm13, ymm9, ymm3, 32
	vperm2i128 ymm3, ymm9, ymm3, 49
	vperm2i128 ymm14, ymm10, ymm5, 32
	vperm2i128 ymm5, ymm10, ymm5, 49
	vperm2i128 ymm0, ymm11, ymm7, 32
	vperm2i128 ymm7, ymm11, ymm7, 49
	vpsllq ymm2, ymm1, 32
	vpblendd ymm2, ymm12, ymm2, 170
	vpsrlq ymm12, ymm12, 32
	vpblendd ymm1, ymm12, ymm1, 170
	vpsllq ymm4, ymm3, 32
	vpblendd ymm4, ymm13, ymm4, 170
	vpsrlq ymm13, ymm13, 32
	vpblendd ymm3, ymm13, ymm3, 170
	vpsllq ymm6, ymm5, 32
	vpblendd ymm6, ymm14, ymm6, 170
	vpsrlq ymm14, ymm14, 32
	vpblendd ymm5, ymm14, ymm5, 170
	vpsllq ymm8, ymm7, 32
	vpblendd ymm8, ymm0, ymm8, 170
	vpsrlq ymm0, ymm0, 32
	vpblendd ymm7, ymm0, ymm7, 170
	vmovdqu ymm9, YMMWORD PTR [r8+2688]
	vmovdqu ymm10, YMMWORD PTR [r8+2720]
	vpsubw ymm12, ymm1, ymm2
	vpaddw ymm2, ymm2, ymm1
	vpmullw ymm11, ymm12, ymm10
	vpmulhw ymm12, ymm12, ymm9
	vpmulhw ymm11, ymm11, ymm15
	vpsubw ymm12, ymm12, ymm11
	vmovdqu ymm13, YMMWORD PTR [r8+2752]
	vmovdqu ymm14, YMMWORD PTR [r8+2784]
	vpsubw ymm11, ymm3, ymm4
	vpaddw ymm4, ymm4, ymm3
	vpmullw ymm0, ymm11, ymm14
	vpmulhw ymm11, ymm11, ymm13
	vpmulhw ymm0, ymm0, ymm15
	vpsubw ymm11, ymm11, ymm0
	vmovdqu ymm1, YMMWORD PTR [r8+2816]
	vmovdqu ymm9, YMMWORD PTR [r8+2848]
	vpsubw ymm0, ymm5, ymm6
	vpaddw ymm6, ymm6, ymm5
	vpmullw ymm10, ymm0, ymm9
	vpmulhw ymm0, ymm0, ymm1
	vpmulhw ymm10, ymm10, ymm15
	vpsubw ymm0, ymm0, ymm10
	vmovdqu ymm3, YMMWORD PTR [r8+2880]
	vmovdqu ymm13, YMMWORD PTR [r8+2912]
	vpsubw ymm10, ymm7, ymm8
	vpaddw ymm8, ymm8, ymm7
	vpmullw ymm14, ymm10, ymm13
	vpmulhw ymm10, ymm10, ymm3
	vpmulhw ymm14, ymm14, ymm15
	vpsubw ymm10, ymm10, ymm14
	vpsllq ymm5, ymm12, 32
	vpblendd ymm5, ymm2, ymm5, 170
	vpsrlq ymm2, ymm2, 32
	vpblendd ymm12, ymm2, ymm12, 170
	vpsllq ymm1, ymm11, 32
	vpblendd ymm1, ymm4, ymm1, 170
	vpsrlq ymm4, ymm4, 32
	vpblendd ymm11, ymm4, ymm11, 170
	vpsllq ymm9, ymm0, 32
	vpblendd ymm9, ymm6, ymm9, 170
	vpsrlq ymm6, ymm6, 32
	vpblendd ymm0, ymm6, ymm0, 170
	vpsllq ymm14, ymm10, 32
	vpblendd ymm14, ymm8, ymm14, 170
	vpsrlq ymm8, ymm8, 32
	vpblendd ymm10, ymm8, ymm10, 170
	vmovdqu ymm7, YMMWORD PTR [r8+2944]
	vmovdqu ymm3, YMMWORD PTR [r8+2976]
	vpsubw ymm2, ymm12, ymm5
	vpaddw ymm5, ymm5, ymm12
	vpmullw ymm13, ymm2, ymm3
	vpmulhw ymm2, ymm2, ymm7
	vpmulhw ymm13, ymm13, ymm15
	vpsubw ymm2, ymm2, ymm13
	vmovdqu ymm4, YMMWORD PTR [r8+3008]
	vmovdqu ymm6, YMMWORD PTR [r8+3040]
	vpsubw ymm13, ymm11, ymm1
	vpaddw ymm1, ymm1, ymm11
	vpmullw ymm8, ymm13, ymm6
	vpmulhw ymm13, ymm13, ymm4
	vpmulhw ymm8, ymm8, ymm15
	vpsubw ymm13, ymm13, ymm8
	vmovdqu ymm12, YMMWORD PTR [r8+3072]
	vmovdqu ymm7, YMMWORD PTR [r8+3104]
	vpsubw ymm8, ymm0, ymm9
	vpaddw ymm9, ymm9, ymm0
	vpmullw ymm3, ymm8, ymm7
	vpmulhw ymm8, ymm8, ymm12
	vpmulhw ymm3, ymm3, ymm15
	vpsubw ymm8, ymm8, ymm3
	vmovdqu ymm11, YMMWORD PTR [r8+3136]
	vmovdqu ymm4, YMMWORD PTR [r8+3168]
	vpsubw ymm3, ymm10, ymm14
	vpaddw ymm14, ymm14, ymm10
	vpmullw ymm6, ymm3, ymm4
	vpmulhw ymm3, ymm3, ymm11
	vpmulhw ymm6, ymm6, ymm15
	vpsubw ymm3, ymm3, ymm6
	vpunpcklqdq ymm0, ymm5, ymm2
	vpunpckhqdq ymm2, ymm5, ymm2
	vpunpcklqdq ymm12, ymm1, ymm13
	vpunpckhqdq ymm13, ymm1, ymm13
	vpunpcklqdq ymm7, ymm9, ymm8
	vpunpckhqdq ymm8, ymm9, ymm8
	vpunpcklqdq ymm6, ymm14, ymm3
	vpunpckhqdq ymm3, ymm14, ymm3
	vmovdqu ymm10, YMMWORD PTR [r8+3200]
	vmovdqu ymm11, YMMWORD PTR [r8+3232]
	vpsubw ymm5, ymm2, ymm0
	vpaddw ymm0, ymm0, ymm2
	vpmullw ymm4, ymm5, ymm11
	vpmulhw ymm5, ymm5, ymm10
	vpmulhw ymm4, ymm4, ymm15
	vpsubw ymm5, ymm5, ymm4
	vmovdqu ymm1, YMMWORD PTR [r8+3264]
	vmovdqu ymm9, YMMWORD PTR [r8+3296]
	vpsubw ymm4, ymm13, ymm12
	vpaddw ymm12, ymm12, ymm13
	vpmullw ymm14, ymm4, ymm9
	vpmulhw ymm4, ymm4, ymm1
	vpmulhw ymm14, ymm14, ymm15
	vpsubw ymm4, ymm4, ymm14
	vmovdqu ymm2, YMMWORD PTR [r8+3328]
	vmovdqu ymm10, YMMWORD PTR [r8+3360]
	vpsubw ymm14, ymm8, ymm7
	vpaddw ymm7, ymm7, ymm8
	vpmullw ymm11, ymm14, ymm10
	vpmulhw ymm14, ymm14, ymm2
	vpmulhw ymm11, ymm11, ymm15
	vpsubw ymm14, ymm14, ymm11
	vmovdqu ymm13, YMMWORD PTR [r8+3392]
	vmovdqu ymm1, YMMWORD PTR [r8+3424]
	vpsubw ymm11, ymm3, ymm6
	vpaddw ymm6, ymm6, ymm3
	vpmullw ymm9, ymm11, ymm1
	vpmulhw ymm11, ymm11, ymm13
	vpmulhw ymm9, ymm9, ymm15
	vpsubw ymm11, ymm11, ymm9
	vperm2i128 ymm8, ymm0, ymm5, 32
	vperm2i128 ymm5, ymm0, ymm5, 49
	vperm2i128 ymm2, ymm12, ymm4, 32
	vperm2i128 ymm4, ymm12, ymm4, 49
	vperm2i128 ymm10, ymm7, ymm14, 32
	vperm2i128 ymm14, ymm7, ymm14, 49
	vperm2i128 ymm9, ymm6, ymm11, 32
	vperm2i128 ymm11, ymm6, ymm11, 49
	vmovdqu ymm3, YMMWORD PTR [r8]
	vmovdqu ymm13, YMMWORD PTR [r8+32]
	vpmullw ymm1, ymm8, ymm13
	vpmulhw ymm8, ymm8, ymm3
	vpmulhw ymm1, ymm1, ymm15
	vpsubw ymm8, ymm8, ymm1
	vpmullw ymm0, ymm5, ymm13
	vpmulhw ymm5, ymm5, ymm3
	vpmulhw ymm0, ymm0, ymm15
	vpsubw ymm5, ymm5, ymm0
	vpmullw ymm12, ymm2, ymm13
	vpmulhw ymm2, ymm2, ymm3
	vpmulhw ymm12, ymm12, ymm15
	vpsubw ymm2, ymm2, ymm12
	vpmullw ymm7, ymm4, ymm13
	vpmulhw ymm4, ymm4, ymm3
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm4, ymm4, ymm7
	vpmullw ymm6, ymm10, ymm13
	vpmulhw ymm10, ymm10, ymm3
	vpmulhw ymm6, ymm6, ymm15
	vpsubw ymm10, ymm10, ymm6
	vpmullw ymm1, ymm14, ymm13
	vpmulhw ymm14, ymm14, ymm3
	vpmulhw ymm1, ymm1, ymm15
	vpsubw ymm14, ymm14, ymm1
	vpmullw ymm0, ymm9, ymm13
	vpmulhw ymm9, ymm9, ymm3
	vpmulhw ymm0, ymm0, ymm15
	vpsubw ymm9, ymm9, ymm0
	vpmullw ymm12, ymm11, ymm13
	vpmulhw ymm11, ymm11, ymm3
	vpmulhw ymm12, ymm12, ymm15
	vpsubw ymm11, ymm11, ymm12
	vmovdqu ymm7, YMMWORD PTR [r8+3456]
	vmovdqu ymm6, YMMWORD PTR [r8+3488]
	vpsubw ymm0, ymm5, ymm8
	vpaddw ymm8, ymm8, ymm5
	vpmullw ymm1, ymm0, ymm6
	vpmulhw ymm0, ymm0, ymm7
	vpmulhw ymm1, ymm1, ymm15
	vpsubw ymm0, ymm0, ymm1
	vmovdqu ymm12, YMMWORD PTR [r8+3520]
	vmovdqu ymm3, YMMWORD PTR [r8+3552]
	vpsubw ymm1, ymm4, ymm2
	vpaddw ymm2, ymm2, ymm4
	vpmullw ymm13, ymm1, ymm3
	vpmulhw ymm1, ymm1, ymm12
	vpmulhw ymm13, ymm13, ymm15
	vpsubw ymm1, ymm1, ymm13
	vmovdqu ymm5, YMMWORD PTR [r8+3584]
	vmovdqu ymm7, YMMWORD PTR [r8+3616]
	vpsubw ymm13, ymm14, ymm10
	vpaddw ymm10, ymm10, ymm14
	vpmullw ymm6, ymm13, ymm7
	vpmulhw ymm13, ymm13, ymm5
	vpmulhw ymm6, ymm6, ymm15
	vpsubw ymm13, ymm13, ymm6
	vmovdqu ymm4, YMMWORD PTR [r8+3648]
	vmovdqu ymm12, YMMWORD PTR [r8+3680]
	vpsubw ymm6, ymm11, ymm9
	vpaddw ymm9, ymm9, ymm11
	vpmullw ymm3, ymm6, ymm12
	vpmulhw ymm6, ymm6, ymm4
	vpmulhw ymm3, ymm3, ymm15
	vpsubw ymm6, ymm6, ymm3
	vmovdqu ymm14, YMMWORD PTR [r8+3712]
	vmovdqu ymm5, YMMWORD PTR [r8+3744]
	vpsubw ymm3, ymm2, ymm8
	vpsubw ymm4, ymm1, ymm0
	vpaddw ymm8, ymm8, ymm2
	vpaddw ymm0, ymm0, ymm1
	vpmullw ymm7, ymm3, ymm5
	vpmullw ymm11, ymm4, ymm5
	vpmulhw ymm3, ymm3, ymm14
	vpmulhw ymm4, ymm4, ymm14
	vpmulhw ymm7, ymm7, ymm15
	vpmulhw ymm11, ymm11, ymm15
	vpsubw ymm3, ymm3, ymm7
	vpsubw ymm4, ymm4, ymm11
	vmovdqu ymm12, YMMWORD PTR [r8+3776]
	vmovdqu ymm7, YMMWORD PTR [r8+3808]
	vpsubw ymm11, ymm9, ymm10
	vpsubw ymm14, ymm6, ymm13
	vpaddw ymm10, ymm10, ymm9
	vpaddw ymm13, ymm13, ymm6
	vpmullw ymm2, ymm11, ymm7
	vpmullw ymm1, ymm14, ymm7
	vpmulhw ymm11, ymm11, ymm12
	vpmulhw ymm14, ymm14, ymm12
	vpmulhw ymm2, ymm2, ymm15
	vpmulhw ymm1, ymm1, ymm15
	vpsubw ymm11, ymm11, ymm2
	vpsubw ymm14, ymm14, ymm1
	vmovdqu ymm5, YMMWORD PTR [r8]
	vmovdqu ymm2, YMMWORD PTR [r8+32]
	vpmullw ymm9, ymm8, ymm2
	vpmulhw ymm8, ymm8, ymm5
	vpmulhw ymm9, ymm9, ymm15
	vpsubw ymm8, ymm8, ymm9
	vpmullw ymm1, ymm0, ymm2
	vpmulhw ymm0, ymm0, ymm5
	vpmulhw ymm1, ymm1, ymm15
	vpsubw ymm0, ymm0, ymm1
	vpmullw ymm6, ymm3, ymm2
	vpmulhw ymm3, ymm3, ymm5
	vpmulhw ymm6, ymm6, ymm15
	vpsubw ymm3, ymm3, ymm6
	vpmullw ymm12, ymm4, ymm2
	vpmulhw ymm4, ymm4, ymm5
	vpmulhw ymm12, ymm12, ymm15
	vpsubw ymm4, ymm4, ymm12
	vpmullw ymm7, ymm10, ymm2
	vpmulhw ymm10, ymm10, ymm5
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm10, ymm10, ymm7
	vpmullw ymm9, ymm13, ymm2
	vpmulhw ymm13, ymm13, ymm5
	vpmulhw ymm9, ymm9, ymm15
	vpsubw ymm13, ymm13, ymm9
	vpmullw ymm1, ymm11, ymm2
	vpmulhw ymm11, ymm11, ymm5
	vpmulhw ymm1, ymm1, ymm15
	vpsubw ymm11, ymm11, ymm1
	vpmullw ymm6, ymm14, ymm2
	vpmulhw ymm14, ymm14, ymm5
	vpmulhw ymm6, ymm6, ymm15
	vpsubw ymm14, ymm14, ymm6
	vmovdqu ymm12, YMMWORD PTR [r8+3840]
	vmovdqu ymm7, YMMWORD PTR [r8+3872]
	vpsubw ymm1, ymm10, ymm8
	vpsubw ymm5, ymm13, ymm0
	vpaddw ymm8, ymm8, ymm10
	vpaddw ymm0, ymm0, ymm13
	vpmullw ymm9, ymm1, ymm7
	vpmullw ymm6, ymm5, ymm7
	vpmulhw ymm1, ymm1, ymm12
	vpmulhw ymm5, ymm5, ymm12
	vpmulhw ymm9, ymm9, ymm15
	vpmulhw ymm6, ymm6, ymm15
	vpsubw ymm1, ymm1, ymm9
	vpsubw ymm5, ymm5, ymm6
	vmovdqu ymm2, YMMWORD PTR [r8+3840]
	vmovdqu ymm9, YMMWORD PTR [r8+3872]
	vpsubw ymm6, ymm11, ymm3
	vpsubw ymm12, ymm14, ymm4
	vpaddw ymm3, ymm3, ymm11
	vpaddw ymm4, ymm4, ymm14
	vpmullw ymm10, ymm6, ymm9
	vpmullw ymm13, ymm12, ymm9
	vpmulhw ymm6, ymm6, ymm2
	vpmulhw ymm12, ymm12, ymm2
	vpmulhw ymm10, ymm10, ymm15
	vpmulhw ymm13, ymm13, ymm15
	vpsubw ymm6, ymm6, ymm10
	vpsubw ymm12, ymm12, ymm13
	vmovdqu YMMWORD PTR [rsi+256], ymm8
	vmovdqu YMMWORD PTR [rsi+288], ymm0
	vmovdqu YMMWORD PTR [rsi+320], ymm3
	vmovdqu YMMWORD PTR [rsi+352], ymm4
	vmovdqu YMMWORD PTR [rsi+384], ymm1
	vmovdqu YMMWORD PTR [rsi+416], ymm5
	vmovdqu YMMWORD PTR [rsi+448], ymm6
	vmovdqu YMMWORD PTR [rsi+480], ymm12
	vmovdqu ymm0, YMMWORD PTR [rdi+256]
	vmovdqu ymm1, YMMWORD PTR [rdi+288]
	vpunpcklwd ymm8, ymm0, ymm1
	vpunpckhwd ymm1, ymm0, ymm1
	vmovdqu ymm2, YMMWORD PTR [rdi+320]
	vmovdqu ymm3, YMMWORD PTR [rdi+352]
	vpunpcklwd ymm9, ymm2, ymm3
	vpunpckhwd ymm3, ymm2, ymm3
	vmovdqu ymm4, YMMWORD PTR [rdi+384]
	vmovdqu ymm5, YMMWORD PTR [rdi+416]
	vpunpcklwd ymm10, ymm4, ymm5
	vpunpckhwd ymm5, ymm4, ymm5
	vmovdqu ymm6, YMMWORD PTR [rdi+448]
	vmovdqu ymm7, YMMWORD PTR [rdi+480]
	vpunpcklwd ymm11, ymm6, ymm7
	vpunpckhwd ymm7, ymm6, ymm7
	vperm2i128 ymm12, ymm8, ymm1, 32
	vperm2i128 ymm1, ymm8, ymm1, 49
	vperm2i128 ymm13, ymm9, ymm3, 32
	vperm2i128 ymm3, ymm9, ymm3, 49
	vperm2i128 ymm14, ymm10, ymm5, 32
	vperm2i128 ymm5, ymm10, ymm5, 49
	vperm2i128 ymm0, ymm11, ymm7, 32
	vperm2i128 ymm7, ymm11, ymm7, 49
	vpsllq ymm2, ymm1, 32
	vpblendd ymm2, ymm12, ymm2, 170
	vpsrlq ymm12, ymm12, 32
	vpblendd ymm1, ymm12, ymm1, 170
	vpsllq ymm4, ymm3, 32
	vpblendd ymm4, ymm13, ymm4, 170
	vpsrlq ymm13, ymm13, 32
	vpblendd ymm3, ymm13, ymm3, 170
	vpsllq ymm6, ymm5, 32
	vpblendd ymm6, ymm14, ymm6, 170
	vpsrlq ymm14, ymm14, 32
	vpblendd ymm5, ymm14, ymm5, 170
	vpsllq ymm8, ymm7, 32
	vpblendd ymm8, ymm0, ymm8, 170
	vpsrlq ymm0, ymm0, 32
	vpblendd ymm7, ymm0, ymm7, 170
	vmovdqu ymm9, YMMWORD PTR [r8+3904]
	vmovdqu ymm10, YMMWORD PTR [r8+3936]
	vpsubw ymm12, ymm1, ymm2
	vpaddw ymm2, ymm2, ymm1
	vpmullw ymm11, ymm12, ymm10
	vpmulhw ymm12, ymm12, ymm9
	vpmulhw ymm11, ymm11, ymm15
	vpsubw ymm12, ymm12, ymm11
	vmovdqu ymm13, YMMWORD PTR [r8+3968]
	vmovdqu ymm14, YMMWORD PTR [r8+4000]
	vpsubw ymm11, ymm3, ymm4
	vpaddw ymm4, ymm4, ymm3
	vpmullw ymm0, ymm11, ymm14
	vpmulhw ymm11, ymm11, ymm13
	vpmulhw ymm0, ymm0, ymm15
	vpsubw ymm11, ymm11, ymm0
	vmovdqu ymm1, YMMWORD PTR [r8+4032]
	vmovdqu ymm9, YMMWORD PTR [r8+4064]
	vpsubw ymm0, ymm5, ymm6
	vpaddw ymm6, ymm6, ymm5
	vpmullw ymm10, ymm0, ymm9
	vpmulhw ymm0, ymm0, ymm1
	vpmulhw ymm10, ymm10, ymm15
	vpsubw ymm0, ymm0, ymm10
	vmovdqu ymm3, YMMWORD PTR [r8+4096]
	vmovdqu ymm13, YMMWORD PTR [r8+4128]
	vpsubw ymm10, ymm7, ymm8
	vpaddw ymm8, ymm8, ymm7
	vpmullw ymm14, ymm10, ymm13
	vpmulhw ymm10, ymm10, ymm3
	vpmulhw ymm14, ymm14, ymm15
	vpsubw ymm10, ymm10, ymm14
	vpsllq ymm5, ymm12, 32
	vpblendd ymm5, ymm2, ymm5, 170
	vpsrlq ymm2, ymm2, 32
	vpblendd ymm12, ymm2, ymm12, 170
	vpsllq ymm1, ymm11, 32
	vpblendd ymm1, ymm4, ymm1, 170
	vpsrlq ymm4, ymm4, 32
	vpblendd ymm11, ymm4, ymm11, 170
	vpsllq ymm9, ymm0, 32
	vpblendd ymm9, ymm6, ymm9, 170
	vpsrlq ymm6, ymm6, 32
	vpblendd ymm0, ymm6, ymm0, 170
	vpsllq ymm14, ymm10, 32
	vpblendd ymm14, ymm8, ymm14, 170
	vpsrlq ymm8, ymm8, 32
	vpblendd ymm10, ymm8, ymm10, 170
	vmovdqu ymm7, YMMWORD PTR [r8+4160]
	vmovdqu ymm3, YMMWORD PTR [r8+4192]
	vpsubw ymm2, ymm12, ymm5
	vpaddw ymm5, ymm5, ymm12
	vpmullw ymm13, ymm2, ymm3
	vpmulhw ymm2, ymm2, ymm7
	vpmulhw ymm13, ymm13, ymm15
	vpsubw ymm2, ymm2, ymm13
	vmovdqu ymm4, YMMWORD PTR [r8+4224]
	vmovdqu ymm6, YMMWORD PTR [r8+4256]
	vpsubw ymm13, ymm11, ymm1
	vpaddw ymm1, ymm1, ymm11
	vpmullw ymm8, ymm13, ymm6
	vpmulhw ymm13, ymm13, ymm4
	vpmulhw ymm8, ymm8, ymm15
	vpsubw ymm13, ymm13, ymm8
	vmovdqu ymm12, YMMWORD PTR [r8+4288]
	vmovdqu ymm7, YMMWORD PTR [r8+4320]
	vpsubw ymm8, ymm0, ymm9
	vpaddw ymm9, ymm9, ymm0
	vpmullw ymm3, ymm8, ymm7
	vpmulhw ymm8, ymm8, ymm12
	vpmulhw ymm3, ymm3, ymm15
	vpsubw ymm8, ymm8, ymm3
	vmovdqu ymm11, YMMWORD PTR [r8+4352]
	vmovdqu ymm4, YMMWORD PTR [r8+4384]
	vpsubw ymm3, ymm10, ymm14
	vpaddw ymm14, ymm14, ymm10
	vpmullw ymm6, ymm3, ymm4
	vpmulhw ymm3, ymm3, ymm11
	vpmulhw ymm6, ymm6, ymm15
	vpsubw ymm3, ymm3, ymm6
	vpunpcklqdq ymm0, ymm5, ymm2
	vpunpckhqdq ymm2, ymm5, ymm2
	vpunpcklqdq ymm12, ymm1, ymm13
	vpunpckhqdq ymm13, ymm1, ymm13
	vpunpcklqdq ymm7, ymm9, ymm8
	vpunpckhqdq ymm8, ymm9, ymm8
	vpunpcklqdq ymm6, ymm14, ymm3
	vpunpckhqdq ymm3, ymm14, ymm3
	vmovdqu ymm10, YMMWORD PTR [r8+4416]
	vmovdqu ymm11, YMMWORD PTR [r8+4448]
	vpsubw ymm5, ymm2, ymm0
	vpaddw ymm0, ymm0, ymm2
	vpmullw ymm4, ymm5, ymm11
	vpmulhw ymm5, ymm5, ymm10
	vpmulhw ymm4, ymm4, ymm15
	vpsubw ymm5, ymm5, ymm4
	vmovdqu ymm1, YMMWORD PTR [r8+4480]
	vmovdqu ymm9, YMMWORD PTR [r8+4512]
	vpsubw ymm4, ymm13, ymm12
	vpaddw ymm12, ymm12, ymm13
	vpmullw ymm14, ymm4, ymm9
	vpmulhw ymm4, ymm4, ymm1
	vpmulhw ymm14, ymm14, ymm15
	vpsubw ymm4, ymm4, ymm14
	vmovdqu ymm2, YMMWORD PTR [r8+4544]
	vmovdqu ymm10, YMMWORD PTR [r8+4576]
	vpsubw ymm14, ymm8, ymm7
	vpaddw ymm7, ymm7, ymm8
	vpmullw ymm11, ymm14, ymm10
	vpmulhw ymm14, ymm14, ymm2
	vpmulhw ymm11, ymm11, ymm15
	vpsubw ymm14, ymm14, ymm11
	vmovdqu ymm13, YMMWORD PTR [r8+4608]
	vmovdqu ymm1, YMMWORD PTR [r8+4640]
	vpsubw ymm11, ymm3, ymm6
	vpaddw ymm6, ymm6, ymm3
	vpmullw ymm9, ymm11, ymm1
	vpmulhw ymm11, ymm11, ymm13
	vpmulhw ymm9, ymm9, ymm15
	vpsubw ymm11, ymm11, ymm9
	vperm2i128 ymm8, ymm0, ymm5, 32
	vperm2i128 ymm5, ymm0, ymm5, 49
	vperm2i128 ymm2, ymm12, ymm4, 32
	vperm2i128 ymm4, ymm12, ymm4, 49
	vperm2i128 ymm10, ymm7, ymm14, 32
	vperm2i128 ymm14, ymm7, ymm14, 49
	vperm2i128 ymm9, ymm6, ymm11, 32
	vperm2i128 ymm11, ymm6, ymm11, 49
	vmovdqu ymm3, YMMWORD PTR [r8]
	vmovdqu ymm13, YMMWORD PTR [r8+32]
	vpmullw ymm1, ymm8, ymm13
	vpmulhw ymm8, ymm8, ymm3
	vpmulhw ymm1, ymm1, ymm15
	vpsubw ymm8, ymm8, ymm1
	vpmullw ymm0, ymm5, ymm13
	vpmulhw ymm5, ymm5, ymm3
	vpmulhw ymm0, ymm0, ymm15
	vpsubw ymm5, ymm5, ymm0
	vpmullw ymm12, ymm2, ymm13
	vpmulhw ymm2, ymm2, ymm3
	vpmulhw ymm12, ymm12, ymm15
	vpsubw ymm2, ymm2, ymm12
	vpmullw ymm7, ymm4, ymm13
	vpmulhw ymm4, ymm4, ymm3
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm4, ymm4, ymm7
	vpmullw ymm6, ymm10, ymm13
	vpmulhw ymm10, ymm10, ymm3
	vpmulhw ymm6, ymm6, ymm15
	vpsubw ymm10, ymm10, ymm6
	vpmullw ymm1, ymm14, ymm13
	vpmulhw ymm14, ymm14, ymm3
	vpmulhw ymm1, ymm1, ymm15
	vpsubw ymm14, ymm14, ymm1
	vpmullw ymm0, ymm9, ymm13
	vpmulhw ymm9, ymm9, ymm3
	vpmulhw ymm0, ymm0, ymm15
	vpsubw ymm9, ymm9, ymm0
	vpmullw ymm12, ymm11, ymm13
	vpmulhw ymm11, ymm11, ymm3
	vpmulhw ymm12, ymm12, ymm15
	vpsubw ymm11, ymm11, ymm12
	vmovdqu ymm7, YMMWORD PTR [r8+4672]
	vmovdqu ymm6, YMMWORD PTR [r8+4704]
	vpsubw ymm0, ymm5, ymm8
	vpaddw ymm8, ymm8, ymm5
	vpmullw ymm1, ymm0, ymm6
	vpmulhw ymm0, ymm0, ymm7
	vpmulhw ymm1, ymm1, ymm15
	vpsubw ymm0, ymm0, ymm1
	vmovdqu ymm12, YMMWORD PTR [r8+4736]
	vmovdqu ymm3, YMMWORD PTR [r8+4768]
	vpsubw ymm1, ymm4, ymm2
	vpaddw ymm2, ymm2, ymm4
	vpmullw ymm13, ymm1, ymm3
	vpmulhw ymm1, ymm1, ymm12
	vpmulhw ymm13, ymm13, ymm15
	vpsubw ymm1, ymm1, ymm13
	vmovdqu ymm5, YMMWORD PTR [r8+4800]
	vmovdqu ymm7, YMMWORD PTR [r8+4832]
	vpsubw ymm13, ymm14, ymm10
	vpaddw ymm10, ymm10, ymm14
	vpmullw ymm6, ymm13, ymm7
	vpmulhw ymm13, ymm13, ymm5
	vpmulhw ymm6, ymm6, ymm15
	vpsubw ymm13, ymm13, ymm6
	vmovdqu ymm4, YMMWORD PTR [r8+4864]
	vmovdqu ymm12, YMMWORD PTR [r8+4896]
	vpsubw ymm6, ymm11, ymm9
	vpaddw ymm9, ymm9, ymm11
	vpmullw ymm3, ymm6, ymm12
	vpmulhw ymm6, ymm6, ymm4
	vpmulhw ymm3, ymm3, ymm15
	vpsubw ymm6, ymm6, ymm3
	vmovdqu ymm14, YMMWORD PTR [r8+4928]
	vmovdqu ymm5, YMMWORD PTR [r8+4960]
	vpsubw ymm3, ymm2, ymm8
	vpsubw ymm4, ymm1, ymm0
	vpaddw ymm8, ymm8, ymm2
	vpaddw ymm0, ymm0, ymm1
	vpmullw ymm7, ymm3, ymm5
	vpmullw ymm11, ymm4, ymm5
	vpmulhw ymm3, ymm3, ymm14
	vpmulhw ymm4, ymm4, ymm14
	vpmulhw ymm7, ymm7, ymm15
	vpmulhw ymm11, ymm11, ymm15
	vpsubw ymm3, ymm3, ymm7
	vpsubw ymm4, ymm4, ymm11
	vmovdqu ymm12, YMMWORD PTR [r8+4992]
	vmovdqu ymm7, YMMWORD PTR [r8+5024]
	vpsubw ymm11, ymm9, ymm10
	vpsubw ymm14, ymm6, ymm13
	vpaddw ymm10, ymm10, ymm9
	vpaddw ymm13, ymm13, ymm6
	vpmullw ymm2, ymm11, ymm7
	vpmullw ymm1, ymm14, ymm7
	vpmulhw ymm11, ymm11, ymm12
	vpmulhw ymm14, ymm14, ymm12
	vpmulhw ymm2, ymm2, ymm15
	vpmulhw ymm1, ymm1, ymm15
	vpsubw ymm11, ymm11, ymm2
	vpsubw ymm14, ymm14, ymm1
	vmovdqu ymm5, YMMWORD PTR [r8]
	vmovdqu ymm2, YMMWORD PTR [r8+32]
	vpmullw ymm9, ymm8, ymm2
	vpmulhw ymm8, ymm8, ymm5
	vpmulhw ymm9, ymm9, ymm15
	vpsubw ymm8, ymm8, ymm9
	vpmullw ymm1, ymm0, ymm2
	vpmulhw ymm0, ymm0, ymm5
	vpmulhw ymm1, ymm1, ymm15
	vpsubw ymm0, ymm0, ymm1
	vpmullw ymm6, ymm3, ymm2
	vpmulhw ymm3, ymm3, ymm5
	vpmulhw ymm6, ymm6, ymm15
	vpsubw ymm3, ymm3, ymm6
	vpmullw ymm12, ymm4, ymm2
	vpmulhw ymm4, ymm4, ymm5
	vpmulhw ymm12, ymm12, ymm15
	vpsubw ymm4, ymm4, ymm12
	vpmullw ymm7, ymm10, ymm2
	vpmulhw ymm10, ymm10, ymm5
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm10, ymm10, ymm7
	vpmullw ymm9, ymm13, ymm2
	vpmulhw ymm13, ymm13, ymm5
	vpmulhw ymm9, ymm9, ymm15
	vpsubw ymm13, ymm13, ymm9
	vpmullw ymm1, ymm11, ymm2
	vpmulhw ymm11, ymm11, ymm5
	vpmulhw ymm1, ymm1, ymm15
	vpsubw ymm11, ymm11, ymm1
	vpmullw ymm6, ymm14, ymm2
	vpmulhw ymm14, ymm14, ymm5
	vpmulhw ymm6, ymm6, ymm15
	vpsubw ymm14, ymm14, ymm6
	vmovdqu ymm12, YMMWORD PTR [r8+5056]
	vmovdqu ymm7, YMMWORD PTR [r8+5088]
	vpsubw ymm1, ymm10, ymm8
	vpsubw ymm5, ymm13, ymm0
	vpaddw ymm8, ymm8, ymm10
	vpaddw ymm0, ymm0, ymm13
	vpmullw ymm9, ymm1, ymm7
	vpmullw ymm6, ymm5, ymm7
	vpmulhw ymm1, ymm1, ymm12
	vpmulhw ymm5, ymm5, ymm12
	vpmulhw ymm9, ymm9, ymm15
	vpmulhw ymm6, ymm6, ymm15
	vpsubw ymm1, ymm1, ymm9
	vpsubw ymm5, ymm5, ymm6
	vmovdqu ymm2, YMMWORD PTR [r8+5056]
	vmovdqu ymm9, YMMWORD PTR [r8+5088]
	vpsubw ymm6, ymm11, ymm3
	vpsubw ymm12, ymm14, ymm4
	vpaddw ymm3, ymm3, ymm11
	vpaddw ymm4, ymm4, ymm14
	vpmullw ymm10, ymm6, ymm9
	vpmullw ymm13, ymm12, ymm9
	vpmulhw ymm6, ymm6, ymm2
	vpmulhw ymm12, ymm12, ymm2
	vpmulhw ymm10, ymm10, ymm15
	vpmulhw ymm13, ymm13, ymm15
	vpsubw ymm6, ymm6, ymm10
	vpsubw ymm12, ymm12, ymm13
	vmovdqu YMMWORD PTR [rsi+512], ymm8
	vmovdqu YMMWORD PTR [rsi+544], ymm0
	vmovdqu YMMWORD PTR [rsi+576], ymm3
	vmovdqu YMMWORD PTR [rsi+608], ymm4
	vmovdqu YMMWORD PTR [rsi+640], ymm1
	vmovdqu YMMWORD PTR [rsi+672], ymm5
	vmovdqu YMMWORD PTR [rsi+704], ymm6
	vmovdqu YMMWORD PTR [rsi+736], ymm12
	vmovdqu ymm12, YMMWORD PTR [r8+2560]
	vmovdqu ymm13, YMMWORD PTR [r8+2592]
	vmovdqu ymm10, YMMWORD PTR [r8+2624]
	vmovdqu ymm11, YMMWORD PTR [r8+2656]
	vpxor ymm9, ymm9, ymm9
	vmovdqu ymm4, YMMWORD PTR [rsi+256]
	vmovdqu ymm5, YMMWORD PTR [rsi+512]
	vpsubw ymm6, ymm5, ymm4
	vpaddw ymm4, ymm4, ymm5
	vpmullw ymm7, ymm6, ymm13
	vpmulhw ymm6, ymm6, ymm12
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm6, ymm6, ymm7
	vpmullw ymm7, ymm4, ymm11
	vpmulhw ymm4, ymm4, ymm10
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm4, ymm4, ymm7
	vpsraw ymm7, ymm4, 15
	vpand ymm7, ymm7, ymm15
	vpaddw ymm4, ymm4, ymm7
	vpmullw ymm7, ymm6, ymm11
	vpmulhw ymm6, ymm6, ymm10
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm6, ymm6, ymm7
	vpsraw ymm7, ymm6, 15
	vpand ymm7, ymm7, ymm15
	vpaddw ymm6, ymm6, ymm7
	vpermq ymm4, ymm4, 216
	vpunpckhwd ymm7, ymm4, ymm9
	vpunpcklwd ymm4, ymm4, ymm9
	vmovdqu YMMWORD PTR [rdi], ymm4
	vmovdqu YMMWORD PTR [rdi+32], ymm7
	vpermq ymm6, ymm6, 216
	vpunpckhwd ymm7, ymm6, ymm9
	vpunpcklwd ymm6, ymm6, ymm9
	vmovdqu YMMWORD PTR [rdi+512], ymm6
	vmovdqu YMMWORD PTR [rdi+544], ymm7
	vmovdqu ymm4, YMMWORD PTR [rsi+288]
	vmovdqu ymm5, YMMWORD PTR [rsi+544]
	vpsubw ymm6, ymm5, ymm4
	vpaddw ymm4, ymm4, ymm5
	vpmullw ymm7, ymm6, ymm13
	vpmulhw ymm6, ymm6, ymm12
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm6, ymm6, ymm7
	vpmullw ymm7, ymm4, ymm11
	vpmulhw ymm4, ymm4, ymm10
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm4, ymm4, ymm7
	vpsraw ymm7, ymm4, 15
	vpand ymm7, ymm7, ymm15
	vpaddw ymm4, ymm4, ymm7
	vpmullw ymm7, ymm6, ymm11
	vpmulhw ymm6, ymm6, ymm10
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm6, ymm6, ymm7
	vpsraw ymm7, ymm6, 15
	vpand ymm7, ymm7, ymm15
	vpaddw ymm6, ymm6, ymm7
	vpermq ymm4, ymm4, 216
	vpunpckhwd ymm7, ymm4, ymm9
	vpunpcklwd ymm4, ymm4, ymm9
	vmovdqu YMMWORD PTR [rdi+64], ymm4
	vmovdqu YMMWORD PTR [rdi+96], ymm7
	vpermq ymm6, ymm6, 216
	vpunpckhwd ymm7, ymm6, ymm9
	vpunpcklwd ymm6, ymm6, ymm9
	vmovdqu YMMWORD PTR [rdi+576], ymm6
	vmovdqu YMMWORD PTR [rdi+608], ymm7
	vmovdqu ymm4, YMMWORD PTR [rsi+320]
	vmovdqu ymm5, YMMWORD PTR [rsi+576]
	vpsubw ymm6, ymm5, ymm4
	vpaddw ymm4, ymm4, ymm5
	vpmullw ymm7, ymm6, ymm13
	vpmulhw ymm6, ymm6, ymm12
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm6, ymm6, ymm7
	vpmullw ymm7, ymm4, ymm11
	vpmulhw ymm4, ymm4, ymm10
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm4, ymm4, ymm7
	vpsraw ymm7, ymm4, 15
	vpand ymm7, ymm7, ymm15
	vpaddw ymm4, ymm4, ymm7
	vpmullw ymm7, ymm6, ymm11
	vpmulhw ymm6, ymm6, ymm10
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm6, ymm6, ymm7
	vpsraw ymm7, ymm6, 15
	vpand ymm7, ymm7, ymm15
	vpaddw ymm6, ymm6, ymm7
	vpermq ymm4, ymm4, 216
	vpunpckhwd ymm7, ymm4, ymm9
	vpunpcklwd ymm4, ymm4, ymm9
	vmovdqu YMMWORD PTR [rdi+128], ymm4
	vmovdqu YMMWORD PTR [rdi+160], ymm7
	vpermq ymm6, ymm6, 216
	vpunpckhwd ymm7, ymm6, ymm9
	vpunpcklwd ymm6, ymm6, ymm9
	vmovdqu YMMWORD PTR [rdi+640], ymm6
	vmovdqu YMMWORD PTR [rdi+672], ymm7
	vmovdqu ymm4, YMMWORD PTR [rsi+352]
	vmovdqu ymm5, YMMWORD PTR [rsi+608]
	vpsubw ymm6, ymm5, ymm4
	vpaddw ymm4, ymm4, ymm5
	vpmullw ymm7, ymm6, ymm13
	vpmulhw ymm6, ymm6, ymm12
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm6, ymm6, ymm7
	vpmullw ymm7, ymm4, ymm11
	vpmulhw ymm4, ymm4, ymm10
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm4, ymm4, ymm7
	vpsraw ymm7, ymm4, 15
	vpand ymm7, ymm7, ymm15
	vpaddw ymm4, ymm4, ymm7
	vpmullw ymm7, ymm6, ymm11
	vpmulhw ymm6, ymm6, ymm10
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm6, ymm6, ymm7
	vpsraw ymm7, ymm6, 15
	vpand ymm7, ymm7, ymm15
	vpaddw ymm6, ymm6, ymm7
	vpermq ymm4, ymm4, 216
	vpunpckhwd ymm7, ymm4, ymm9
	vpunpcklwd ymm4, ymm4, ymm9
	vmovdqu YMMWORD PTR [rdi+192], ymm4
	vmovdqu YMMWORD PTR [rdi+224], ymm7
	vpermq ymm6, ymm6, 216
	vpunpckhwd ymm7, ymm6, ymm9
	vpunpcklwd ymm6, ymm6, ymm9
	vmovdqu YMMWORD PTR [rdi+704], ymm6
	vmovdqu YMMWORD PTR [rdi+736], ymm7
	vmovdqu ymm4, YMMWORD PTR [rsi+384]
	vmovdqu ymm5, YMMWORD PTR [rsi+640]
	vpsubw ymm6, ymm5, ymm4
	vpaddw ymm4, ymm4, ymm5
	vpmullw ymm7, ymm6, ymm13
	vpmulhw ymm6, ymm6, ymm12
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm6, ymm6, ymm7
	vpmullw ymm7, ymm4, ymm11
	vpmulhw ymm4, ymm4, ymm10
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm4, ymm4, ymm7
	vpsraw ymm7, ymm4, 15
	vpand ymm7, ymm7, ymm15
	vpaddw ymm4, ymm4, ymm7
	vpmullw ymm7, ymm6, ymm11
	vpmulhw ymm6, ymm6, ymm10
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm6, ymm6, ymm7
	vpsraw ymm7, ymm6, 15
	vpand ymm7, ymm7, ymm15
	vpaddw ymm6, ymm6, ymm7
	vpermq ymm4, ymm4, 216
	vpunpckhwd ymm7, ymm4, ymm9
	vpunpcklwd ymm4, ymm4, ymm9
	vmovdqu YMMWORD PTR [rdi+256], ymm4
	vmovdqu YMMWORD PTR [rdi+288], ymm7
	vpermq ymm6, ymm6, 216
	vpunpckhwd ymm7, ymm6, ymm9
	vpunpcklwd ymm6, ymm6, ymm9
	vmovdqu YMMWORD PTR [rdi+768], ymm6
	vmovdqu YMMWORD PTR [rdi+800], ymm7
	vmovdqu ymm4, YMMWORD PTR [rsi+416]
	vmovdqu ymm5, YMMWORD PTR [rsi+672]
	vpsubw ymm6, ymm5, ymm4
	vpaddw ymm4, ymm4, ymm5
	vpmullw ymm7, ymm6, ymm13
	vpmulhw ymm6, ymm6, ymm12
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm6, ymm6, ymm7
	vpmullw ymm7, ymm4, ymm11
	vpmulhw ymm4, ymm4, ymm10
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm4, ymm4, ymm7
	vpsraw ymm7, ymm4, 15
	vpand ymm7, ymm7, ymm15
	vpaddw ymm4, ymm4, ymm7
	vpmullw ymm7, ymm6, ymm11
	vpmulhw ymm6, ymm6, ymm10
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm6, ymm6, ymm7
	vpsraw ymm7, ymm6, 15
	vpand ymm7, ymm7, ymm15
	vpaddw ymm6, ymm6, ymm7
	vpermq ymm4, ymm4, 216
	vpunpckhwd ymm7, ymm4, ymm9
	vpunpcklwd ymm4, ymm4, ymm9
	vmovdqu YMMWORD PTR [rdi+320], ymm4
	vmovdqu YMMWORD PTR [rdi+352], ymm7
	vpermq ymm6, ymm6, 216
	vpunpckhwd ymm7, ymm6, ymm9
	vpunpcklwd ymm6, ymm6, ymm9
	vmovdqu YMMWORD PTR [rdi+832], ymm6
	vmovdqu YMMWORD PTR [rdi+864], ymm7
	vmovdqu ymm4, YMMWORD PTR [rsi+448]
	vmovdqu ymm5, YMMWORD PTR [rsi+704]
	vpsubw ymm6, ymm5, ymm4
	vpaddw ymm4, ymm4, ymm5
	vpmullw ymm7, ymm6, ymm13
	vpmulhw ymm6, ymm6, ymm12
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm6, ymm6, ymm7
	vpmullw ymm7, ymm4, ymm11
	vpmulhw ymm4, ymm4, ymm10
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm4, ymm4, ymm7
	vpsraw ymm7, ymm4, 15
	vpand ymm7, ymm7, ymm15
	vpaddw ymm4, ymm4, ymm7
	vpmullw ymm7, ymm6, ymm11
	vpmulhw ymm6, ymm6, ymm10
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm6, ymm6, ymm7
	vpsraw ymm7, ymm6, 15
	vpand ymm7, ymm7, ymm15
	vpaddw ymm6, ymm6, ymm7
	vpermq ymm4, ymm4, 216
	vpunpckhwd ymm7, ymm4, ymm9
	vpunpcklwd ymm4, ymm4, ymm9
	vmovdqu YMMWORD PTR [rdi+384], ymm4
	vmovdqu YMMWORD PTR [rdi+416], ymm7
	vpermq ymm6, ymm6, 216
	vpunpckhwd ymm7, ymm6, ymm9
	vpunpcklwd ymm6, ymm6, ymm9
	vmovdqu YMMWORD PTR [rdi+896], ymm6
	vmovdqu YMMWORD PTR [rdi+928], ymm7
	vmovdqu ymm4, YMMWORD PTR [rsi+480]
	vmovdqu ymm5, YMMWORD PTR [rsi+736]
	vpsubw ymm6, ymm5, ymm4
	vpaddw ymm4, ymm4, ymm5
	vpmullw ymm7, ymm6, ymm13
	vpmulhw ymm6, ymm6, ymm12
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm6, ymm6, ymm7
	vpmullw ymm7, ymm4, ymm11
	vpmulhw ymm4, ymm4, ymm10
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm4, ymm4, ymm7
	vpsraw ymm7, ymm4, 15
	vpand ymm7, ymm7, ymm15
	vpaddw ymm4, ymm4, ymm7
	vpmullw ymm7, ymm6, ymm11
	vpmulhw ymm6, ymm6, ymm10
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm6, ymm6, ymm7
	vpsraw ymm7, ymm6, 15
	vpand ymm7, ymm7, ymm15
	vpaddw ymm6, ymm6, ymm7
	vpermq ymm4, ymm4, 216
	vpunpckhwd ymm7, ymm4, ymm9
	vpunpcklwd ymm4, ymm4, ymm9
	vmovdqu YMMWORD PTR [rdi+448], ymm4
	vmovdqu YMMWORD PTR [rdi+480], ymm7
	vpermq ymm6, ymm6, 216
	vpunpckhwd ymm7, ymm6, ymm9
	vpunpcklwd ymm6, ymm6, ymm9
	vmovdqu YMMWORD PTR [rdi+960], ymm6
	vmovdqu YMMWORD PTR [rdi+992], ymm7
	vzeroupper
	add rbp, 1024
	add r12, 512
	sub r14, 1
	jne 24b
	mov rdi, rbp
	mov rsi, r15
	mov rdx, rbx
	add rdx, 1024
	mov rcx, rbx
	mov eax, 218172673
	vmovq xmm15, rax
	vpbroadcastd ymm15, xmm15
	mov eax, -217976063
	vmovq xmm14, rax
	vpbroadcastd ymm14, xmm14
	mov r8, rcx
	add r8, 3328
	mov ecx, 8
26:
	vmovdqu ymm13, YMMWORD PTR [r8]
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vmovdqu ymm2, YMMWORD PTR [rsi+64]
	vmovdqu ymm3, YMMWORD PTR [rsi+96]
	vpshufd ymm0, ymm0, 216
	vpshufd ymm1, ymm1, 216
	vpshufd ymm2, ymm2, 216
	vpshufd ymm3, ymm3, 216
	vpunpckhqdq ymm4, ymm0, ymm1
	vpunpcklqdq ymm0, ymm0, ymm1
	vpunpckhqdq ymm5, ymm2, ymm3
	vpunpcklqdq ymm2, ymm2, ymm3
	vpackssdw ymm0, ymm0, ymm2
	vpackssdw ymm4, ymm4, ymm5
	vmovdqu ymm6, YMMWORD PTR [rdx]
	vmovdqu ymm10, YMMWORD PTR [rdx+32]
	vmovdqa ymm1, ymm4
	vpmullw ymm2, ymm1, ymm10
	vpmullw ymm2, ymm2, ymm14
	vpmulhw ymm1, ymm1, ymm10
	vpmulhw ymm2, ymm2, ymm15
	vpsubw ymm1, ymm1, ymm2
	vpmullw ymm2, ymm1, ymm13
	vpmullw ymm2, ymm2, ymm14
	vpmulhw ymm1, ymm1, ymm13
	vpmulhw ymm2, ymm2, ymm15
	vpsubw ymm1, ymm1, ymm2
	vmovdqa ymm2, ymm0
	vpmullw ymm3, ymm2, ymm6
	vpmullw ymm3, ymm3, ymm14
	vpmulhw ymm2, ymm2, ymm6
	vpmulhw ymm3, ymm3, ymm15
	vpsubw ymm2, ymm2, ymm3
	vpaddw ymm1, ymm1, ymm2
	vmovdqa ymm2, ymm0
	vpmullw ymm3, ymm2, ymm10
	vpmullw ymm3, ymm3, ymm14
	vpmulhw ymm2, ymm2, ymm10
	vpmulhw ymm3, ymm3, ymm15
	vpsubw ymm2, ymm2, ymm3
	vpmullw ymm3, ymm4, ymm6
	vpmullw ymm3, ymm3, ymm14
	vpmulhw ymm4, ymm4, ymm6
	vpmulhw ymm3, ymm3, ymm15
	vpsubw ymm4, ymm4, ymm3
	vpaddw ymm2, ymm2, ymm4
	vmovdqa ymm11, ymm1
	vmovdqa ymm12, ymm2
	vmovdqu ymm0, YMMWORD PTR [rsi+1024]
	vmovdqu ymm1, YMMWORD PTR [rsi+1056]
	vmovdqu ymm2, YMMWORD PTR [rsi+1088]
	vmovdqu ymm3, YMMWORD PTR [rsi+1120]
	vpshufd ymm0, ymm0, 216
	vpshufd ymm1, ymm1, 216
	vpshufd ymm2, ymm2, 216
	vpshufd ymm3, ymm3, 216
	vpunpckhqdq ymm4, ymm0, ymm1
	vpunpcklqdq ymm0, ymm0, ymm1
	vpunpckhqdq ymm5, ymm2, ymm3
	vpunpcklqdq ymm2, ymm2, ymm3
	vpackssdw ymm0, ymm0, ymm2
	vpackssdw ymm4, ymm4, ymm5
	vmovdqu ymm6, YMMWORD PTR [rdx+512]
	vmovdqu ymm10, YMMWORD PTR [rdx+544]
	vmovdqa ymm1, ymm4
	vpmullw ymm2, ymm1, ymm10
	vpmullw ymm2, ymm2, ymm14
	vpmulhw ymm1, ymm1, ymm10
	vpmulhw ymm2, ymm2, ymm15
	vpsubw ymm1, ymm1, ymm2
	vpmullw ymm2, ymm1, ymm13
	vpmullw ymm2, ymm2, ymm14
	vpmulhw ymm1, ymm1, ymm13
	vpmulhw ymm2, ymm2, ymm15
	vpsubw ymm1, ymm1, ymm2
	vmovdqa ymm2, ymm0
	vpmullw ymm3, ymm2, ymm6
	vpmullw ymm3, ymm3, ymm14
	vpmulhw ymm2, ymm2, ymm6
	vpmulhw ymm3, ymm3, ymm15
	vpsubw ymm2, ymm2, ymm3
	vpaddw ymm1, ymm1, ymm2
	vmovdqa ymm2, ymm0
	vpmullw ymm3, ymm2, ymm10
	vpmullw ymm3, ymm3, ymm14
	vpmulhw ymm2, ymm2, ymm10
	vpmulhw ymm3, ymm3, ymm15
	vpsubw ymm2, ymm2, ymm3
	vpmullw ymm3, ymm4, ymm6
	vpmullw ymm3, ymm3, ymm14
	vpmulhw ymm4, ymm4, ymm6
	vpmulhw ymm3, ymm3, ymm15
	vpsubw ymm4, ymm4, ymm3
	vpaddw ymm2, ymm2, ymm4
	vpaddw ymm11, ymm11, ymm1
	vpaddw ymm12, ymm12, ymm2
	vmovdqu ymm0, YMMWORD PTR [rsi+2048]
	vmovdqu ymm1, YMMWORD PTR [rsi+2080]
	vmovdqu ymm2, YMMWORD PTR [rsi+2112]
	vmovdqu ymm3, YMMWORD PTR [rsi+2144]
	vpshufd ymm0, ymm0, 216
	vpshufd ymm1, ymm1, 216
	vpshufd ymm2, ymm2, 216
	vpshufd ymm3, ymm3, 216
	vpunpckhqdq ymm4, ymm0, ymm1
	vpunpcklqdq ymm0, ymm0, ymm1
	vpunpckhqdq ymm5, ymm2, ymm3
	vpunpcklqdq ymm2, ymm2, ymm3
	vpackssdw ymm0, ymm0, ymm2
	vpackssdw ymm4, ymm4, ymm5
	vmovdqu ymm6, YMMWORD PTR [rdx+1024]
	vmovdqu ymm10, YMMWORD PTR [rdx+1056]
	vmovdqa ymm1, ymm4
	vpmullw ymm2, ymm1, ymm10
	vpmullw ymm2, ymm2, ymm14
	vpmulhw ymm1, ymm1, ymm10
	vpmulhw ymm2, ymm2, ymm15
	vpsubw ymm1, ymm1, ymm2
	vpmullw ymm2, ymm1, ymm13
	vpmullw ymm2, ymm2, ymm14
	vpmulhw ymm1, ymm1, ymm13
	vpmulhw ymm2, ymm2, ymm15
	vpsubw ymm1, ymm1, ymm2
	vmovdqa ymm2, ymm0
	vpmullw ymm3, ymm2, ymm6
	vpmullw ymm3, ymm3, ymm14
	vpmulhw ymm2, ymm2, ymm6
	vpmulhw ymm3, ymm3, ymm15
	vpsubw ymm2, ymm2, ymm3
	vpaddw ymm1, ymm1, ymm2
	vmovdqa ymm2, ymm0
	vpmullw ymm3, ymm2, ymm10
	vpmullw ymm3, ymm3, ymm14
	vpmulhw ymm2, ymm2, ymm10
	vpmulhw ymm3, ymm3, ymm15
	vpsubw ymm2, ymm2, ymm3
	vpmullw ymm3, ymm4, ymm6
	vpmullw ymm3, ymm3, ymm14
	vpmulhw ymm4, ymm4, ymm6
	vpmulhw ymm3, ymm3, ymm15
	vpsubw ymm4, ymm4, ymm3
	vpaddw ymm2, ymm2, ymm4
	vpaddw ymm11, ymm11, ymm1
	vpaddw ymm12, ymm12, ymm2
	mov eax, 88671561
	vmovq xmm13, rax
	vpbroadcastd ymm13, xmm13
	vpmullw ymm3, ymm11, ymm13
	vpmullw ymm3, ymm3, ymm14
	vpmulhw ymm11, ymm11, ymm13
	vpmulhw ymm3, ymm3, ymm15
	vpsubw ymm11, ymm11, ymm3
	vpsraw ymm3, ymm11, 15
	vpand ymm3, ymm3, ymm15
	vpaddw ymm11, ymm11, ymm3
	vpmullw ymm3, ymm12, ymm13
	vpmullw ymm3, ymm3, ymm14
	vpmulhw ymm12, ymm12, ymm13
	vpmulhw ymm3, ymm3, ymm15
	vpsubw ymm12, ymm12, ymm3
	vpsraw ymm3, ymm12, 15
	vpand ymm3, ymm3, ymm15
	vpaddw ymm12, ymm12, ymm3
	vmovdqu YMMWORD PTR [rdi], ymm11
	vmovdqu YMMWORD PTR [rdi+32], ymm12
	add rsi, 128
	add rdx, 64
	add rdi, 64
	add r8, 32
	sub rcx, 1
	jne 26b
	mov rdi, rbp
	mov rsi, rbx
	mov eax, 218172673
	vmovq xmm15, rax
	vpbroadcastd ymm15, xmm15
	lea r8, {VG_MLKEM_NTT_ZETAS}
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vmovdqu ymm1, YMMWORD PTR [rdi+32]
	vpunpcklwd ymm8, ymm0, ymm1
	vpunpckhwd ymm1, ymm0, ymm1
	vmovdqu ymm2, YMMWORD PTR [rdi+64]
	vmovdqu ymm3, YMMWORD PTR [rdi+96]
	vpunpcklwd ymm9, ymm2, ymm3
	vpunpckhwd ymm3, ymm2, ymm3
	vmovdqu ymm4, YMMWORD PTR [rdi+128]
	vmovdqu ymm5, YMMWORD PTR [rdi+160]
	vpunpcklwd ymm10, ymm4, ymm5
	vpunpckhwd ymm5, ymm4, ymm5
	vmovdqu ymm6, YMMWORD PTR [rdi+192]
	vmovdqu ymm7, YMMWORD PTR [rdi+224]
	vpunpcklwd ymm11, ymm6, ymm7
	vpunpckhwd ymm7, ymm6, ymm7
	vperm2i128 ymm12, ymm8, ymm1, 32
	vperm2i128 ymm1, ymm8, ymm1, 49
	vperm2i128 ymm13, ymm9, ymm3, 32
	vperm2i128 ymm3, ymm9, ymm3, 49
	vperm2i128 ymm14, ymm10, ymm5, 32
	vperm2i128 ymm5, ymm10, ymm5, 49
	vperm2i128 ymm0, ymm11, ymm7, 32
	vperm2i128 ymm7, ymm11, ymm7, 49
	vpsllq ymm2, ymm1, 32
	vpblendd ymm2, ymm12, ymm2, 170
	vpsrlq ymm12, ymm12, 32
	vpblendd ymm1, ymm12, ymm1, 170
	vpsllq ymm4, ymm3, 32
	vpblendd ymm4, ymm13, ymm4, 170
	vpsrlq ymm13, ymm13, 32
	vpblendd ymm3, ymm13, ymm3, 170
	vpsllq ymm6, ymm5, 32
	vpblendd ymm6, ymm14, ymm6, 170
	vpsrlq ymm14, ymm14, 32
	vpblendd ymm5, ymm14, ymm5, 170
	vpsllq ymm8, ymm7, 32
	vpblendd ymm8, ymm0, ymm8, 170
	vpsrlq ymm0, ymm0, 32
	vpblendd ymm7, ymm0, ymm7, 170
	vmovdqu ymm9, YMMWORD PTR [r8+2688]
	vmovdqu ymm10, YMMWORD PTR [r8+2720]
	vpsubw ymm12, ymm1, ymm2
	vpaddw ymm2, ymm2, ymm1
	vpmullw ymm11, ymm12, ymm10
	vpmulhw ymm12, ymm12, ymm9
	vpmulhw ymm11, ymm11, ymm15
	vpsubw ymm12, ymm12, ymm11
	vmovdqu ymm13, YMMWORD PTR [r8+2752]
	vmovdqu ymm14, YMMWORD PTR [r8+2784]
	vpsubw ymm11, ymm3, ymm4
	vpaddw ymm4, ymm4, ymm3
	vpmullw ymm0, ymm11, ymm14
	vpmulhw ymm11, ymm11, ymm13
	vpmulhw ymm0, ymm0, ymm15
	vpsubw ymm11, ymm11, ymm0
	vmovdqu ymm1, YMMWORD PTR [r8+2816]
	vmovdqu ymm9, YMMWORD PTR [r8+2848]
	vpsubw ymm0, ymm5, ymm6
	vpaddw ymm6, ymm6, ymm5
	vpmullw ymm10, ymm0, ymm9
	vpmulhw ymm0, ymm0, ymm1
	vpmulhw ymm10, ymm10, ymm15
	vpsubw ymm0, ymm0, ymm10
	vmovdqu ymm3, YMMWORD PTR [r8+2880]
	vmovdqu ymm13, YMMWORD PTR [r8+2912]
	vpsubw ymm10, ymm7, ymm8
	vpaddw ymm8, ymm8, ymm7
	vpmullw ymm14, ymm10, ymm13
	vpmulhw ymm10, ymm10, ymm3
	vpmulhw ymm14, ymm14, ymm15
	vpsubw ymm10, ymm10, ymm14
	vpsllq ymm5, ymm12, 32
	vpblendd ymm5, ymm2, ymm5, 170
	vpsrlq ymm2, ymm2, 32
	vpblendd ymm12, ymm2, ymm12, 170
	vpsllq ymm1, ymm11, 32
	vpblendd ymm1, ymm4, ymm1, 170
	vpsrlq ymm4, ymm4, 32
	vpblendd ymm11, ymm4, ymm11, 170
	vpsllq ymm9, ymm0, 32
	vpblendd ymm9, ymm6, ymm9, 170
	vpsrlq ymm6, ymm6, 32
	vpblendd ymm0, ymm6, ymm0, 170
	vpsllq ymm14, ymm10, 32
	vpblendd ymm14, ymm8, ymm14, 170
	vpsrlq ymm8, ymm8, 32
	vpblendd ymm10, ymm8, ymm10, 170
	vmovdqu ymm7, YMMWORD PTR [r8+2944]
	vmovdqu ymm3, YMMWORD PTR [r8+2976]
	vpsubw ymm2, ymm12, ymm5
	vpaddw ymm5, ymm5, ymm12
	vpmullw ymm13, ymm2, ymm3
	vpmulhw ymm2, ymm2, ymm7
	vpmulhw ymm13, ymm13, ymm15
	vpsubw ymm2, ymm2, ymm13
	vmovdqu ymm4, YMMWORD PTR [r8+3008]
	vmovdqu ymm6, YMMWORD PTR [r8+3040]
	vpsubw ymm13, ymm11, ymm1
	vpaddw ymm1, ymm1, ymm11
	vpmullw ymm8, ymm13, ymm6
	vpmulhw ymm13, ymm13, ymm4
	vpmulhw ymm8, ymm8, ymm15
	vpsubw ymm13, ymm13, ymm8
	vmovdqu ymm12, YMMWORD PTR [r8+3072]
	vmovdqu ymm7, YMMWORD PTR [r8+3104]
	vpsubw ymm8, ymm0, ymm9
	vpaddw ymm9, ymm9, ymm0
	vpmullw ymm3, ymm8, ymm7
	vpmulhw ymm8, ymm8, ymm12
	vpmulhw ymm3, ymm3, ymm15
	vpsubw ymm8, ymm8, ymm3
	vmovdqu ymm11, YMMWORD PTR [r8+3136]
	vmovdqu ymm4, YMMWORD PTR [r8+3168]
	vpsubw ymm3, ymm10, ymm14
	vpaddw ymm14, ymm14, ymm10
	vpmullw ymm6, ymm3, ymm4
	vpmulhw ymm3, ymm3, ymm11
	vpmulhw ymm6, ymm6, ymm15
	vpsubw ymm3, ymm3, ymm6
	vpunpcklqdq ymm0, ymm5, ymm2
	vpunpckhqdq ymm2, ymm5, ymm2
	vpunpcklqdq ymm12, ymm1, ymm13
	vpunpckhqdq ymm13, ymm1, ymm13
	vpunpcklqdq ymm7, ymm9, ymm8
	vpunpckhqdq ymm8, ymm9, ymm8
	vpunpcklqdq ymm6, ymm14, ymm3
	vpunpckhqdq ymm3, ymm14, ymm3
	vmovdqu ymm10, YMMWORD PTR [r8+3200]
	vmovdqu ymm11, YMMWORD PTR [r8+3232]
	vpsubw ymm5, ymm2, ymm0
	vpaddw ymm0, ymm0, ymm2
	vpmullw ymm4, ymm5, ymm11
	vpmulhw ymm5, ymm5, ymm10
	vpmulhw ymm4, ymm4, ymm15
	vpsubw ymm5, ymm5, ymm4
	vmovdqu ymm1, YMMWORD PTR [r8+3264]
	vmovdqu ymm9, YMMWORD PTR [r8+3296]
	vpsubw ymm4, ymm13, ymm12
	vpaddw ymm12, ymm12, ymm13
	vpmullw ymm14, ymm4, ymm9
	vpmulhw ymm4, ymm4, ymm1
	vpmulhw ymm14, ymm14, ymm15
	vpsubw ymm4, ymm4, ymm14
	vmovdqu ymm2, YMMWORD PTR [r8+3328]
	vmovdqu ymm10, YMMWORD PTR [r8+3360]
	vpsubw ymm14, ymm8, ymm7
	vpaddw ymm7, ymm7, ymm8
	vpmullw ymm11, ymm14, ymm10
	vpmulhw ymm14, ymm14, ymm2
	vpmulhw ymm11, ymm11, ymm15
	vpsubw ymm14, ymm14, ymm11
	vmovdqu ymm13, YMMWORD PTR [r8+3392]
	vmovdqu ymm1, YMMWORD PTR [r8+3424]
	vpsubw ymm11, ymm3, ymm6
	vpaddw ymm6, ymm6, ymm3
	vpmullw ymm9, ymm11, ymm1
	vpmulhw ymm11, ymm11, ymm13
	vpmulhw ymm9, ymm9, ymm15
	vpsubw ymm11, ymm11, ymm9
	vperm2i128 ymm8, ymm0, ymm5, 32
	vperm2i128 ymm5, ymm0, ymm5, 49
	vperm2i128 ymm2, ymm12, ymm4, 32
	vperm2i128 ymm4, ymm12, ymm4, 49
	vperm2i128 ymm10, ymm7, ymm14, 32
	vperm2i128 ymm14, ymm7, ymm14, 49
	vperm2i128 ymm9, ymm6, ymm11, 32
	vperm2i128 ymm11, ymm6, ymm11, 49
	vmovdqu ymm3, YMMWORD PTR [r8]
	vmovdqu ymm13, YMMWORD PTR [r8+32]
	vpmullw ymm1, ymm8, ymm13
	vpmulhw ymm8, ymm8, ymm3
	vpmulhw ymm1, ymm1, ymm15
	vpsubw ymm8, ymm8, ymm1
	vpmullw ymm0, ymm5, ymm13
	vpmulhw ymm5, ymm5, ymm3
	vpmulhw ymm0, ymm0, ymm15
	vpsubw ymm5, ymm5, ymm0
	vpmullw ymm12, ymm2, ymm13
	vpmulhw ymm2, ymm2, ymm3
	vpmulhw ymm12, ymm12, ymm15
	vpsubw ymm2, ymm2, ymm12
	vpmullw ymm7, ymm4, ymm13
	vpmulhw ymm4, ymm4, ymm3
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm4, ymm4, ymm7
	vpmullw ymm6, ymm10, ymm13
	vpmulhw ymm10, ymm10, ymm3
	vpmulhw ymm6, ymm6, ymm15
	vpsubw ymm10, ymm10, ymm6
	vpmullw ymm1, ymm14, ymm13
	vpmulhw ymm14, ymm14, ymm3
	vpmulhw ymm1, ymm1, ymm15
	vpsubw ymm14, ymm14, ymm1
	vpmullw ymm0, ymm9, ymm13
	vpmulhw ymm9, ymm9, ymm3
	vpmulhw ymm0, ymm0, ymm15
	vpsubw ymm9, ymm9, ymm0
	vpmullw ymm12, ymm11, ymm13
	vpmulhw ymm11, ymm11, ymm3
	vpmulhw ymm12, ymm12, ymm15
	vpsubw ymm11, ymm11, ymm12
	vmovdqu ymm7, YMMWORD PTR [r8+3456]
	vmovdqu ymm6, YMMWORD PTR [r8+3488]
	vpsubw ymm0, ymm5, ymm8
	vpaddw ymm8, ymm8, ymm5
	vpmullw ymm1, ymm0, ymm6
	vpmulhw ymm0, ymm0, ymm7
	vpmulhw ymm1, ymm1, ymm15
	vpsubw ymm0, ymm0, ymm1
	vmovdqu ymm12, YMMWORD PTR [r8+3520]
	vmovdqu ymm3, YMMWORD PTR [r8+3552]
	vpsubw ymm1, ymm4, ymm2
	vpaddw ymm2, ymm2, ymm4
	vpmullw ymm13, ymm1, ymm3
	vpmulhw ymm1, ymm1, ymm12
	vpmulhw ymm13, ymm13, ymm15
	vpsubw ymm1, ymm1, ymm13
	vmovdqu ymm5, YMMWORD PTR [r8+3584]
	vmovdqu ymm7, YMMWORD PTR [r8+3616]
	vpsubw ymm13, ymm14, ymm10
	vpaddw ymm10, ymm10, ymm14
	vpmullw ymm6, ymm13, ymm7
	vpmulhw ymm13, ymm13, ymm5
	vpmulhw ymm6, ymm6, ymm15
	vpsubw ymm13, ymm13, ymm6
	vmovdqu ymm4, YMMWORD PTR [r8+3648]
	vmovdqu ymm12, YMMWORD PTR [r8+3680]
	vpsubw ymm6, ymm11, ymm9
	vpaddw ymm9, ymm9, ymm11
	vpmullw ymm3, ymm6, ymm12
	vpmulhw ymm6, ymm6, ymm4
	vpmulhw ymm3, ymm3, ymm15
	vpsubw ymm6, ymm6, ymm3
	vmovdqu ymm14, YMMWORD PTR [r8+3712]
	vmovdqu ymm5, YMMWORD PTR [r8+3744]
	vpsubw ymm3, ymm2, ymm8
	vpsubw ymm4, ymm1, ymm0
	vpaddw ymm8, ymm8, ymm2
	vpaddw ymm0, ymm0, ymm1
	vpmullw ymm7, ymm3, ymm5
	vpmullw ymm11, ymm4, ymm5
	vpmulhw ymm3, ymm3, ymm14
	vpmulhw ymm4, ymm4, ymm14
	vpmulhw ymm7, ymm7, ymm15
	vpmulhw ymm11, ymm11, ymm15
	vpsubw ymm3, ymm3, ymm7
	vpsubw ymm4, ymm4, ymm11
	vmovdqu ymm12, YMMWORD PTR [r8+3776]
	vmovdqu ymm7, YMMWORD PTR [r8+3808]
	vpsubw ymm11, ymm9, ymm10
	vpsubw ymm14, ymm6, ymm13
	vpaddw ymm10, ymm10, ymm9
	vpaddw ymm13, ymm13, ymm6
	vpmullw ymm2, ymm11, ymm7
	vpmullw ymm1, ymm14, ymm7
	vpmulhw ymm11, ymm11, ymm12
	vpmulhw ymm14, ymm14, ymm12
	vpmulhw ymm2, ymm2, ymm15
	vpmulhw ymm1, ymm1, ymm15
	vpsubw ymm11, ymm11, ymm2
	vpsubw ymm14, ymm14, ymm1
	vmovdqu ymm5, YMMWORD PTR [r8]
	vmovdqu ymm2, YMMWORD PTR [r8+32]
	vpmullw ymm9, ymm8, ymm2
	vpmulhw ymm8, ymm8, ymm5
	vpmulhw ymm9, ymm9, ymm15
	vpsubw ymm8, ymm8, ymm9
	vpmullw ymm1, ymm0, ymm2
	vpmulhw ymm0, ymm0, ymm5
	vpmulhw ymm1, ymm1, ymm15
	vpsubw ymm0, ymm0, ymm1
	vpmullw ymm6, ymm3, ymm2
	vpmulhw ymm3, ymm3, ymm5
	vpmulhw ymm6, ymm6, ymm15
	vpsubw ymm3, ymm3, ymm6
	vpmullw ymm12, ymm4, ymm2
	vpmulhw ymm4, ymm4, ymm5
	vpmulhw ymm12, ymm12, ymm15
	vpsubw ymm4, ymm4, ymm12
	vpmullw ymm7, ymm10, ymm2
	vpmulhw ymm10, ymm10, ymm5
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm10, ymm10, ymm7
	vpmullw ymm9, ymm13, ymm2
	vpmulhw ymm13, ymm13, ymm5
	vpmulhw ymm9, ymm9, ymm15
	vpsubw ymm13, ymm13, ymm9
	vpmullw ymm1, ymm11, ymm2
	vpmulhw ymm11, ymm11, ymm5
	vpmulhw ymm1, ymm1, ymm15
	vpsubw ymm11, ymm11, ymm1
	vpmullw ymm6, ymm14, ymm2
	vpmulhw ymm14, ymm14, ymm5
	vpmulhw ymm6, ymm6, ymm15
	vpsubw ymm14, ymm14, ymm6
	vmovdqu ymm12, YMMWORD PTR [r8+3840]
	vmovdqu ymm7, YMMWORD PTR [r8+3872]
	vpsubw ymm1, ymm10, ymm8
	vpsubw ymm5, ymm13, ymm0
	vpaddw ymm8, ymm8, ymm10
	vpaddw ymm0, ymm0, ymm13
	vpmullw ymm9, ymm1, ymm7
	vpmullw ymm6, ymm5, ymm7
	vpmulhw ymm1, ymm1, ymm12
	vpmulhw ymm5, ymm5, ymm12
	vpmulhw ymm9, ymm9, ymm15
	vpmulhw ymm6, ymm6, ymm15
	vpsubw ymm1, ymm1, ymm9
	vpsubw ymm5, ymm5, ymm6
	vmovdqu ymm2, YMMWORD PTR [r8+3840]
	vmovdqu ymm9, YMMWORD PTR [r8+3872]
	vpsubw ymm6, ymm11, ymm3
	vpsubw ymm12, ymm14, ymm4
	vpaddw ymm3, ymm3, ymm11
	vpaddw ymm4, ymm4, ymm14
	vpmullw ymm10, ymm6, ymm9
	vpmullw ymm13, ymm12, ymm9
	vpmulhw ymm6, ymm6, ymm2
	vpmulhw ymm12, ymm12, ymm2
	vpmulhw ymm10, ymm10, ymm15
	vpmulhw ymm13, ymm13, ymm15
	vpsubw ymm6, ymm6, ymm10
	vpsubw ymm12, ymm12, ymm13
	vmovdqu YMMWORD PTR [rsi+256], ymm8
	vmovdqu YMMWORD PTR [rsi+288], ymm0
	vmovdqu YMMWORD PTR [rsi+320], ymm3
	vmovdqu YMMWORD PTR [rsi+352], ymm4
	vmovdqu YMMWORD PTR [rsi+384], ymm1
	vmovdqu YMMWORD PTR [rsi+416], ymm5
	vmovdqu YMMWORD PTR [rsi+448], ymm6
	vmovdqu YMMWORD PTR [rsi+480], ymm12
	vmovdqu ymm0, YMMWORD PTR [rdi+256]
	vmovdqu ymm1, YMMWORD PTR [rdi+288]
	vpunpcklwd ymm8, ymm0, ymm1
	vpunpckhwd ymm1, ymm0, ymm1
	vmovdqu ymm2, YMMWORD PTR [rdi+320]
	vmovdqu ymm3, YMMWORD PTR [rdi+352]
	vpunpcklwd ymm9, ymm2, ymm3
	vpunpckhwd ymm3, ymm2, ymm3
	vmovdqu ymm4, YMMWORD PTR [rdi+384]
	vmovdqu ymm5, YMMWORD PTR [rdi+416]
	vpunpcklwd ymm10, ymm4, ymm5
	vpunpckhwd ymm5, ymm4, ymm5
	vmovdqu ymm6, YMMWORD PTR [rdi+448]
	vmovdqu ymm7, YMMWORD PTR [rdi+480]
	vpunpcklwd ymm11, ymm6, ymm7
	vpunpckhwd ymm7, ymm6, ymm7
	vperm2i128 ymm12, ymm8, ymm1, 32
	vperm2i128 ymm1, ymm8, ymm1, 49
	vperm2i128 ymm13, ymm9, ymm3, 32
	vperm2i128 ymm3, ymm9, ymm3, 49
	vperm2i128 ymm14, ymm10, ymm5, 32
	vperm2i128 ymm5, ymm10, ymm5, 49
	vperm2i128 ymm0, ymm11, ymm7, 32
	vperm2i128 ymm7, ymm11, ymm7, 49
	vpsllq ymm2, ymm1, 32
	vpblendd ymm2, ymm12, ymm2, 170
	vpsrlq ymm12, ymm12, 32
	vpblendd ymm1, ymm12, ymm1, 170
	vpsllq ymm4, ymm3, 32
	vpblendd ymm4, ymm13, ymm4, 170
	vpsrlq ymm13, ymm13, 32
	vpblendd ymm3, ymm13, ymm3, 170
	vpsllq ymm6, ymm5, 32
	vpblendd ymm6, ymm14, ymm6, 170
	vpsrlq ymm14, ymm14, 32
	vpblendd ymm5, ymm14, ymm5, 170
	vpsllq ymm8, ymm7, 32
	vpblendd ymm8, ymm0, ymm8, 170
	vpsrlq ymm0, ymm0, 32
	vpblendd ymm7, ymm0, ymm7, 170
	vmovdqu ymm9, YMMWORD PTR [r8+3904]
	vmovdqu ymm10, YMMWORD PTR [r8+3936]
	vpsubw ymm12, ymm1, ymm2
	vpaddw ymm2, ymm2, ymm1
	vpmullw ymm11, ymm12, ymm10
	vpmulhw ymm12, ymm12, ymm9
	vpmulhw ymm11, ymm11, ymm15
	vpsubw ymm12, ymm12, ymm11
	vmovdqu ymm13, YMMWORD PTR [r8+3968]
	vmovdqu ymm14, YMMWORD PTR [r8+4000]
	vpsubw ymm11, ymm3, ymm4
	vpaddw ymm4, ymm4, ymm3
	vpmullw ymm0, ymm11, ymm14
	vpmulhw ymm11, ymm11, ymm13
	vpmulhw ymm0, ymm0, ymm15
	vpsubw ymm11, ymm11, ymm0
	vmovdqu ymm1, YMMWORD PTR [r8+4032]
	vmovdqu ymm9, YMMWORD PTR [r8+4064]
	vpsubw ymm0, ymm5, ymm6
	vpaddw ymm6, ymm6, ymm5
	vpmullw ymm10, ymm0, ymm9
	vpmulhw ymm0, ymm0, ymm1
	vpmulhw ymm10, ymm10, ymm15
	vpsubw ymm0, ymm0, ymm10
	vmovdqu ymm3, YMMWORD PTR [r8+4096]
	vmovdqu ymm13, YMMWORD PTR [r8+4128]
	vpsubw ymm10, ymm7, ymm8
	vpaddw ymm8, ymm8, ymm7
	vpmullw ymm14, ymm10, ymm13
	vpmulhw ymm10, ymm10, ymm3
	vpmulhw ymm14, ymm14, ymm15
	vpsubw ymm10, ymm10, ymm14
	vpsllq ymm5, ymm12, 32
	vpblendd ymm5, ymm2, ymm5, 170
	vpsrlq ymm2, ymm2, 32
	vpblendd ymm12, ymm2, ymm12, 170
	vpsllq ymm1, ymm11, 32
	vpblendd ymm1, ymm4, ymm1, 170
	vpsrlq ymm4, ymm4, 32
	vpblendd ymm11, ymm4, ymm11, 170
	vpsllq ymm9, ymm0, 32
	vpblendd ymm9, ymm6, ymm9, 170
	vpsrlq ymm6, ymm6, 32
	vpblendd ymm0, ymm6, ymm0, 170
	vpsllq ymm14, ymm10, 32
	vpblendd ymm14, ymm8, ymm14, 170
	vpsrlq ymm8, ymm8, 32
	vpblendd ymm10, ymm8, ymm10, 170
	vmovdqu ymm7, YMMWORD PTR [r8+4160]
	vmovdqu ymm3, YMMWORD PTR [r8+4192]
	vpsubw ymm2, ymm12, ymm5
	vpaddw ymm5, ymm5, ymm12
	vpmullw ymm13, ymm2, ymm3
	vpmulhw ymm2, ymm2, ymm7
	vpmulhw ymm13, ymm13, ymm15
	vpsubw ymm2, ymm2, ymm13
	vmovdqu ymm4, YMMWORD PTR [r8+4224]
	vmovdqu ymm6, YMMWORD PTR [r8+4256]
	vpsubw ymm13, ymm11, ymm1
	vpaddw ymm1, ymm1, ymm11
	vpmullw ymm8, ymm13, ymm6
	vpmulhw ymm13, ymm13, ymm4
	vpmulhw ymm8, ymm8, ymm15
	vpsubw ymm13, ymm13, ymm8
	vmovdqu ymm12, YMMWORD PTR [r8+4288]
	vmovdqu ymm7, YMMWORD PTR [r8+4320]
	vpsubw ymm8, ymm0, ymm9
	vpaddw ymm9, ymm9, ymm0
	vpmullw ymm3, ymm8, ymm7
	vpmulhw ymm8, ymm8, ymm12
	vpmulhw ymm3, ymm3, ymm15
	vpsubw ymm8, ymm8, ymm3
	vmovdqu ymm11, YMMWORD PTR [r8+4352]
	vmovdqu ymm4, YMMWORD PTR [r8+4384]
	vpsubw ymm3, ymm10, ymm14
	vpaddw ymm14, ymm14, ymm10
	vpmullw ymm6, ymm3, ymm4
	vpmulhw ymm3, ymm3, ymm11
	vpmulhw ymm6, ymm6, ymm15
	vpsubw ymm3, ymm3, ymm6
	vpunpcklqdq ymm0, ymm5, ymm2
	vpunpckhqdq ymm2, ymm5, ymm2
	vpunpcklqdq ymm12, ymm1, ymm13
	vpunpckhqdq ymm13, ymm1, ymm13
	vpunpcklqdq ymm7, ymm9, ymm8
	vpunpckhqdq ymm8, ymm9, ymm8
	vpunpcklqdq ymm6, ymm14, ymm3
	vpunpckhqdq ymm3, ymm14, ymm3
	vmovdqu ymm10, YMMWORD PTR [r8+4416]
	vmovdqu ymm11, YMMWORD PTR [r8+4448]
	vpsubw ymm5, ymm2, ymm0
	vpaddw ymm0, ymm0, ymm2
	vpmullw ymm4, ymm5, ymm11
	vpmulhw ymm5, ymm5, ymm10
	vpmulhw ymm4, ymm4, ymm15
	vpsubw ymm5, ymm5, ymm4
	vmovdqu ymm1, YMMWORD PTR [r8+4480]
	vmovdqu ymm9, YMMWORD PTR [r8+4512]
	vpsubw ymm4, ymm13, ymm12
	vpaddw ymm12, ymm12, ymm13
	vpmullw ymm14, ymm4, ymm9
	vpmulhw ymm4, ymm4, ymm1
	vpmulhw ymm14, ymm14, ymm15
	vpsubw ymm4, ymm4, ymm14
	vmovdqu ymm2, YMMWORD PTR [r8+4544]
	vmovdqu ymm10, YMMWORD PTR [r8+4576]
	vpsubw ymm14, ymm8, ymm7
	vpaddw ymm7, ymm7, ymm8
	vpmullw ymm11, ymm14, ymm10
	vpmulhw ymm14, ymm14, ymm2
	vpmulhw ymm11, ymm11, ymm15
	vpsubw ymm14, ymm14, ymm11
	vmovdqu ymm13, YMMWORD PTR [r8+4608]
	vmovdqu ymm1, YMMWORD PTR [r8+4640]
	vpsubw ymm11, ymm3, ymm6
	vpaddw ymm6, ymm6, ymm3
	vpmullw ymm9, ymm11, ymm1
	vpmulhw ymm11, ymm11, ymm13
	vpmulhw ymm9, ymm9, ymm15
	vpsubw ymm11, ymm11, ymm9
	vperm2i128 ymm8, ymm0, ymm5, 32
	vperm2i128 ymm5, ymm0, ymm5, 49
	vperm2i128 ymm2, ymm12, ymm4, 32
	vperm2i128 ymm4, ymm12, ymm4, 49
	vperm2i128 ymm10, ymm7, ymm14, 32
	vperm2i128 ymm14, ymm7, ymm14, 49
	vperm2i128 ymm9, ymm6, ymm11, 32
	vperm2i128 ymm11, ymm6, ymm11, 49
	vmovdqu ymm3, YMMWORD PTR [r8]
	vmovdqu ymm13, YMMWORD PTR [r8+32]
	vpmullw ymm1, ymm8, ymm13
	vpmulhw ymm8, ymm8, ymm3
	vpmulhw ymm1, ymm1, ymm15
	vpsubw ymm8, ymm8, ymm1
	vpmullw ymm0, ymm5, ymm13
	vpmulhw ymm5, ymm5, ymm3
	vpmulhw ymm0, ymm0, ymm15
	vpsubw ymm5, ymm5, ymm0
	vpmullw ymm12, ymm2, ymm13
	vpmulhw ymm2, ymm2, ymm3
	vpmulhw ymm12, ymm12, ymm15
	vpsubw ymm2, ymm2, ymm12
	vpmullw ymm7, ymm4, ymm13
	vpmulhw ymm4, ymm4, ymm3
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm4, ymm4, ymm7
	vpmullw ymm6, ymm10, ymm13
	vpmulhw ymm10, ymm10, ymm3
	vpmulhw ymm6, ymm6, ymm15
	vpsubw ymm10, ymm10, ymm6
	vpmullw ymm1, ymm14, ymm13
	vpmulhw ymm14, ymm14, ymm3
	vpmulhw ymm1, ymm1, ymm15
	vpsubw ymm14, ymm14, ymm1
	vpmullw ymm0, ymm9, ymm13
	vpmulhw ymm9, ymm9, ymm3
	vpmulhw ymm0, ymm0, ymm15
	vpsubw ymm9, ymm9, ymm0
	vpmullw ymm12, ymm11, ymm13
	vpmulhw ymm11, ymm11, ymm3
	vpmulhw ymm12, ymm12, ymm15
	vpsubw ymm11, ymm11, ymm12
	vmovdqu ymm7, YMMWORD PTR [r8+4672]
	vmovdqu ymm6, YMMWORD PTR [r8+4704]
	vpsubw ymm0, ymm5, ymm8
	vpaddw ymm8, ymm8, ymm5
	vpmullw ymm1, ymm0, ymm6
	vpmulhw ymm0, ymm0, ymm7
	vpmulhw ymm1, ymm1, ymm15
	vpsubw ymm0, ymm0, ymm1
	vmovdqu ymm12, YMMWORD PTR [r8+4736]
	vmovdqu ymm3, YMMWORD PTR [r8+4768]
	vpsubw ymm1, ymm4, ymm2
	vpaddw ymm2, ymm2, ymm4
	vpmullw ymm13, ymm1, ymm3
	vpmulhw ymm1, ymm1, ymm12
	vpmulhw ymm13, ymm13, ymm15
	vpsubw ymm1, ymm1, ymm13
	vmovdqu ymm5, YMMWORD PTR [r8+4800]
	vmovdqu ymm7, YMMWORD PTR [r8+4832]
	vpsubw ymm13, ymm14, ymm10
	vpaddw ymm10, ymm10, ymm14
	vpmullw ymm6, ymm13, ymm7
	vpmulhw ymm13, ymm13, ymm5
	vpmulhw ymm6, ymm6, ymm15
	vpsubw ymm13, ymm13, ymm6
	vmovdqu ymm4, YMMWORD PTR [r8+4864]
	vmovdqu ymm12, YMMWORD PTR [r8+4896]
	vpsubw ymm6, ymm11, ymm9
	vpaddw ymm9, ymm9, ymm11
	vpmullw ymm3, ymm6, ymm12
	vpmulhw ymm6, ymm6, ymm4
	vpmulhw ymm3, ymm3, ymm15
	vpsubw ymm6, ymm6, ymm3
	vmovdqu ymm14, YMMWORD PTR [r8+4928]
	vmovdqu ymm5, YMMWORD PTR [r8+4960]
	vpsubw ymm3, ymm2, ymm8
	vpsubw ymm4, ymm1, ymm0
	vpaddw ymm8, ymm8, ymm2
	vpaddw ymm0, ymm0, ymm1
	vpmullw ymm7, ymm3, ymm5
	vpmullw ymm11, ymm4, ymm5
	vpmulhw ymm3, ymm3, ymm14
	vpmulhw ymm4, ymm4, ymm14
	vpmulhw ymm7, ymm7, ymm15
	vpmulhw ymm11, ymm11, ymm15
	vpsubw ymm3, ymm3, ymm7
	vpsubw ymm4, ymm4, ymm11
	vmovdqu ymm12, YMMWORD PTR [r8+4992]
	vmovdqu ymm7, YMMWORD PTR [r8+5024]
	vpsubw ymm11, ymm9, ymm10
	vpsubw ymm14, ymm6, ymm13
	vpaddw ymm10, ymm10, ymm9
	vpaddw ymm13, ymm13, ymm6
	vpmullw ymm2, ymm11, ymm7
	vpmullw ymm1, ymm14, ymm7
	vpmulhw ymm11, ymm11, ymm12
	vpmulhw ymm14, ymm14, ymm12
	vpmulhw ymm2, ymm2, ymm15
	vpmulhw ymm1, ymm1, ymm15
	vpsubw ymm11, ymm11, ymm2
	vpsubw ymm14, ymm14, ymm1
	vmovdqu ymm5, YMMWORD PTR [r8]
	vmovdqu ymm2, YMMWORD PTR [r8+32]
	vpmullw ymm9, ymm8, ymm2
	vpmulhw ymm8, ymm8, ymm5
	vpmulhw ymm9, ymm9, ymm15
	vpsubw ymm8, ymm8, ymm9
	vpmullw ymm1, ymm0, ymm2
	vpmulhw ymm0, ymm0, ymm5
	vpmulhw ymm1, ymm1, ymm15
	vpsubw ymm0, ymm0, ymm1
	vpmullw ymm6, ymm3, ymm2
	vpmulhw ymm3, ymm3, ymm5
	vpmulhw ymm6, ymm6, ymm15
	vpsubw ymm3, ymm3, ymm6
	vpmullw ymm12, ymm4, ymm2
	vpmulhw ymm4, ymm4, ymm5
	vpmulhw ymm12, ymm12, ymm15
	vpsubw ymm4, ymm4, ymm12
	vpmullw ymm7, ymm10, ymm2
	vpmulhw ymm10, ymm10, ymm5
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm10, ymm10, ymm7
	vpmullw ymm9, ymm13, ymm2
	vpmulhw ymm13, ymm13, ymm5
	vpmulhw ymm9, ymm9, ymm15
	vpsubw ymm13, ymm13, ymm9
	vpmullw ymm1, ymm11, ymm2
	vpmulhw ymm11, ymm11, ymm5
	vpmulhw ymm1, ymm1, ymm15
	vpsubw ymm11, ymm11, ymm1
	vpmullw ymm6, ymm14, ymm2
	vpmulhw ymm14, ymm14, ymm5
	vpmulhw ymm6, ymm6, ymm15
	vpsubw ymm14, ymm14, ymm6
	vmovdqu ymm12, YMMWORD PTR [r8+5056]
	vmovdqu ymm7, YMMWORD PTR [r8+5088]
	vpsubw ymm1, ymm10, ymm8
	vpsubw ymm5, ymm13, ymm0
	vpaddw ymm8, ymm8, ymm10
	vpaddw ymm0, ymm0, ymm13
	vpmullw ymm9, ymm1, ymm7
	vpmullw ymm6, ymm5, ymm7
	vpmulhw ymm1, ymm1, ymm12
	vpmulhw ymm5, ymm5, ymm12
	vpmulhw ymm9, ymm9, ymm15
	vpmulhw ymm6, ymm6, ymm15
	vpsubw ymm1, ymm1, ymm9
	vpsubw ymm5, ymm5, ymm6
	vmovdqu ymm2, YMMWORD PTR [r8+5056]
	vmovdqu ymm9, YMMWORD PTR [r8+5088]
	vpsubw ymm6, ymm11, ymm3
	vpsubw ymm12, ymm14, ymm4
	vpaddw ymm3, ymm3, ymm11
	vpaddw ymm4, ymm4, ymm14
	vpmullw ymm10, ymm6, ymm9
	vpmullw ymm13, ymm12, ymm9
	vpmulhw ymm6, ymm6, ymm2
	vpmulhw ymm12, ymm12, ymm2
	vpmulhw ymm10, ymm10, ymm15
	vpmulhw ymm13, ymm13, ymm15
	vpsubw ymm6, ymm6, ymm10
	vpsubw ymm12, ymm12, ymm13
	vmovdqu YMMWORD PTR [rsi+512], ymm8
	vmovdqu YMMWORD PTR [rsi+544], ymm0
	vmovdqu YMMWORD PTR [rsi+576], ymm3
	vmovdqu YMMWORD PTR [rsi+608], ymm4
	vmovdqu YMMWORD PTR [rsi+640], ymm1
	vmovdqu YMMWORD PTR [rsi+672], ymm5
	vmovdqu YMMWORD PTR [rsi+704], ymm6
	vmovdqu YMMWORD PTR [rsi+736], ymm12
	vmovdqu ymm12, YMMWORD PTR [r8+2560]
	vmovdqu ymm13, YMMWORD PTR [r8+2592]
	vmovdqu ymm10, YMMWORD PTR [r8+2624]
	vmovdqu ymm11, YMMWORD PTR [r8+2656]
	vpxor ymm9, ymm9, ymm9
	vmovdqu ymm4, YMMWORD PTR [rsi+256]
	vmovdqu ymm5, YMMWORD PTR [rsi+512]
	vpsubw ymm6, ymm5, ymm4
	vpaddw ymm4, ymm4, ymm5
	vpmullw ymm7, ymm6, ymm13
	vpmulhw ymm6, ymm6, ymm12
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm6, ymm6, ymm7
	vpmullw ymm7, ymm4, ymm11
	vpmulhw ymm4, ymm4, ymm10
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm4, ymm4, ymm7
	vpsraw ymm7, ymm4, 15
	vpand ymm7, ymm7, ymm15
	vpaddw ymm4, ymm4, ymm7
	vpmullw ymm7, ymm6, ymm11
	vpmulhw ymm6, ymm6, ymm10
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm6, ymm6, ymm7
	vpsraw ymm7, ymm6, 15
	vpand ymm7, ymm7, ymm15
	vpaddw ymm6, ymm6, ymm7
	vpermq ymm4, ymm4, 216
	vpunpckhwd ymm7, ymm4, ymm9
	vpunpcklwd ymm4, ymm4, ymm9
	vmovdqu YMMWORD PTR [rdi], ymm4
	vmovdqu YMMWORD PTR [rdi+32], ymm7
	vpermq ymm6, ymm6, 216
	vpunpckhwd ymm7, ymm6, ymm9
	vpunpcklwd ymm6, ymm6, ymm9
	vmovdqu YMMWORD PTR [rdi+512], ymm6
	vmovdqu YMMWORD PTR [rdi+544], ymm7
	vmovdqu ymm4, YMMWORD PTR [rsi+288]
	vmovdqu ymm5, YMMWORD PTR [rsi+544]
	vpsubw ymm6, ymm5, ymm4
	vpaddw ymm4, ymm4, ymm5
	vpmullw ymm7, ymm6, ymm13
	vpmulhw ymm6, ymm6, ymm12
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm6, ymm6, ymm7
	vpmullw ymm7, ymm4, ymm11
	vpmulhw ymm4, ymm4, ymm10
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm4, ymm4, ymm7
	vpsraw ymm7, ymm4, 15
	vpand ymm7, ymm7, ymm15
	vpaddw ymm4, ymm4, ymm7
	vpmullw ymm7, ymm6, ymm11
	vpmulhw ymm6, ymm6, ymm10
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm6, ymm6, ymm7
	vpsraw ymm7, ymm6, 15
	vpand ymm7, ymm7, ymm15
	vpaddw ymm6, ymm6, ymm7
	vpermq ymm4, ymm4, 216
	vpunpckhwd ymm7, ymm4, ymm9
	vpunpcklwd ymm4, ymm4, ymm9
	vmovdqu YMMWORD PTR [rdi+64], ymm4
	vmovdqu YMMWORD PTR [rdi+96], ymm7
	vpermq ymm6, ymm6, 216
	vpunpckhwd ymm7, ymm6, ymm9
	vpunpcklwd ymm6, ymm6, ymm9
	vmovdqu YMMWORD PTR [rdi+576], ymm6
	vmovdqu YMMWORD PTR [rdi+608], ymm7
	vmovdqu ymm4, YMMWORD PTR [rsi+320]
	vmovdqu ymm5, YMMWORD PTR [rsi+576]
	vpsubw ymm6, ymm5, ymm4
	vpaddw ymm4, ymm4, ymm5
	vpmullw ymm7, ymm6, ymm13
	vpmulhw ymm6, ymm6, ymm12
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm6, ymm6, ymm7
	vpmullw ymm7, ymm4, ymm11
	vpmulhw ymm4, ymm4, ymm10
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm4, ymm4, ymm7
	vpsraw ymm7, ymm4, 15
	vpand ymm7, ymm7, ymm15
	vpaddw ymm4, ymm4, ymm7
	vpmullw ymm7, ymm6, ymm11
	vpmulhw ymm6, ymm6, ymm10
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm6, ymm6, ymm7
	vpsraw ymm7, ymm6, 15
	vpand ymm7, ymm7, ymm15
	vpaddw ymm6, ymm6, ymm7
	vpermq ymm4, ymm4, 216
	vpunpckhwd ymm7, ymm4, ymm9
	vpunpcklwd ymm4, ymm4, ymm9
	vmovdqu YMMWORD PTR [rdi+128], ymm4
	vmovdqu YMMWORD PTR [rdi+160], ymm7
	vpermq ymm6, ymm6, 216
	vpunpckhwd ymm7, ymm6, ymm9
	vpunpcklwd ymm6, ymm6, ymm9
	vmovdqu YMMWORD PTR [rdi+640], ymm6
	vmovdqu YMMWORD PTR [rdi+672], ymm7
	vmovdqu ymm4, YMMWORD PTR [rsi+352]
	vmovdqu ymm5, YMMWORD PTR [rsi+608]
	vpsubw ymm6, ymm5, ymm4
	vpaddw ymm4, ymm4, ymm5
	vpmullw ymm7, ymm6, ymm13
	vpmulhw ymm6, ymm6, ymm12
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm6, ymm6, ymm7
	vpmullw ymm7, ymm4, ymm11
	vpmulhw ymm4, ymm4, ymm10
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm4, ymm4, ymm7
	vpsraw ymm7, ymm4, 15
	vpand ymm7, ymm7, ymm15
	vpaddw ymm4, ymm4, ymm7
	vpmullw ymm7, ymm6, ymm11
	vpmulhw ymm6, ymm6, ymm10
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm6, ymm6, ymm7
	vpsraw ymm7, ymm6, 15
	vpand ymm7, ymm7, ymm15
	vpaddw ymm6, ymm6, ymm7
	vpermq ymm4, ymm4, 216
	vpunpckhwd ymm7, ymm4, ymm9
	vpunpcklwd ymm4, ymm4, ymm9
	vmovdqu YMMWORD PTR [rdi+192], ymm4
	vmovdqu YMMWORD PTR [rdi+224], ymm7
	vpermq ymm6, ymm6, 216
	vpunpckhwd ymm7, ymm6, ymm9
	vpunpcklwd ymm6, ymm6, ymm9
	vmovdqu YMMWORD PTR [rdi+704], ymm6
	vmovdqu YMMWORD PTR [rdi+736], ymm7
	vmovdqu ymm4, YMMWORD PTR [rsi+384]
	vmovdqu ymm5, YMMWORD PTR [rsi+640]
	vpsubw ymm6, ymm5, ymm4
	vpaddw ymm4, ymm4, ymm5
	vpmullw ymm7, ymm6, ymm13
	vpmulhw ymm6, ymm6, ymm12
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm6, ymm6, ymm7
	vpmullw ymm7, ymm4, ymm11
	vpmulhw ymm4, ymm4, ymm10
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm4, ymm4, ymm7
	vpsraw ymm7, ymm4, 15
	vpand ymm7, ymm7, ymm15
	vpaddw ymm4, ymm4, ymm7
	vpmullw ymm7, ymm6, ymm11
	vpmulhw ymm6, ymm6, ymm10
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm6, ymm6, ymm7
	vpsraw ymm7, ymm6, 15
	vpand ymm7, ymm7, ymm15
	vpaddw ymm6, ymm6, ymm7
	vpermq ymm4, ymm4, 216
	vpunpckhwd ymm7, ymm4, ymm9
	vpunpcklwd ymm4, ymm4, ymm9
	vmovdqu YMMWORD PTR [rdi+256], ymm4
	vmovdqu YMMWORD PTR [rdi+288], ymm7
	vpermq ymm6, ymm6, 216
	vpunpckhwd ymm7, ymm6, ymm9
	vpunpcklwd ymm6, ymm6, ymm9
	vmovdqu YMMWORD PTR [rdi+768], ymm6
	vmovdqu YMMWORD PTR [rdi+800], ymm7
	vmovdqu ymm4, YMMWORD PTR [rsi+416]
	vmovdqu ymm5, YMMWORD PTR [rsi+672]
	vpsubw ymm6, ymm5, ymm4
	vpaddw ymm4, ymm4, ymm5
	vpmullw ymm7, ymm6, ymm13
	vpmulhw ymm6, ymm6, ymm12
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm6, ymm6, ymm7
	vpmullw ymm7, ymm4, ymm11
	vpmulhw ymm4, ymm4, ymm10
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm4, ymm4, ymm7
	vpsraw ymm7, ymm4, 15
	vpand ymm7, ymm7, ymm15
	vpaddw ymm4, ymm4, ymm7
	vpmullw ymm7, ymm6, ymm11
	vpmulhw ymm6, ymm6, ymm10
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm6, ymm6, ymm7
	vpsraw ymm7, ymm6, 15
	vpand ymm7, ymm7, ymm15
	vpaddw ymm6, ymm6, ymm7
	vpermq ymm4, ymm4, 216
	vpunpckhwd ymm7, ymm4, ymm9
	vpunpcklwd ymm4, ymm4, ymm9
	vmovdqu YMMWORD PTR [rdi+320], ymm4
	vmovdqu YMMWORD PTR [rdi+352], ymm7
	vpermq ymm6, ymm6, 216
	vpunpckhwd ymm7, ymm6, ymm9
	vpunpcklwd ymm6, ymm6, ymm9
	vmovdqu YMMWORD PTR [rdi+832], ymm6
	vmovdqu YMMWORD PTR [rdi+864], ymm7
	vmovdqu ymm4, YMMWORD PTR [rsi+448]
	vmovdqu ymm5, YMMWORD PTR [rsi+704]
	vpsubw ymm6, ymm5, ymm4
	vpaddw ymm4, ymm4, ymm5
	vpmullw ymm7, ymm6, ymm13
	vpmulhw ymm6, ymm6, ymm12
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm6, ymm6, ymm7
	vpmullw ymm7, ymm4, ymm11
	vpmulhw ymm4, ymm4, ymm10
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm4, ymm4, ymm7
	vpsraw ymm7, ymm4, 15
	vpand ymm7, ymm7, ymm15
	vpaddw ymm4, ymm4, ymm7
	vpmullw ymm7, ymm6, ymm11
	vpmulhw ymm6, ymm6, ymm10
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm6, ymm6, ymm7
	vpsraw ymm7, ymm6, 15
	vpand ymm7, ymm7, ymm15
	vpaddw ymm6, ymm6, ymm7
	vpermq ymm4, ymm4, 216
	vpunpckhwd ymm7, ymm4, ymm9
	vpunpcklwd ymm4, ymm4, ymm9
	vmovdqu YMMWORD PTR [rdi+384], ymm4
	vmovdqu YMMWORD PTR [rdi+416], ymm7
	vpermq ymm6, ymm6, 216
	vpunpckhwd ymm7, ymm6, ymm9
	vpunpcklwd ymm6, ymm6, ymm9
	vmovdqu YMMWORD PTR [rdi+896], ymm6
	vmovdqu YMMWORD PTR [rdi+928], ymm7
	vmovdqu ymm4, YMMWORD PTR [rsi+480]
	vmovdqu ymm5, YMMWORD PTR [rsi+736]
	vpsubw ymm6, ymm5, ymm4
	vpaddw ymm4, ymm4, ymm5
	vpmullw ymm7, ymm6, ymm13
	vpmulhw ymm6, ymm6, ymm12
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm6, ymm6, ymm7
	vpmullw ymm7, ymm4, ymm11
	vpmulhw ymm4, ymm4, ymm10
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm4, ymm4, ymm7
	vpsraw ymm7, ymm4, 15
	vpand ymm7, ymm7, ymm15
	vpaddw ymm4, ymm4, ymm7
	vpmullw ymm7, ymm6, ymm11
	vpmulhw ymm6, ymm6, ymm10
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm6, ymm6, ymm7
	vpsraw ymm7, ymm6, 15
	vpand ymm7, ymm7, ymm15
	vpaddw ymm6, ymm6, ymm7
	vpermq ymm4, ymm4, 216
	vpunpckhwd ymm7, ymm4, ymm9
	vpunpcklwd ymm4, ymm4, ymm9
	vmovdqu YMMWORD PTR [rdi+448], ymm4
	vmovdqu YMMWORD PTR [rdi+480], ymm7
	vpermq ymm6, ymm6, 216
	vpunpckhwd ymm7, ymm6, ymm9
	vpunpcklwd ymm6, ymm6, ymm9
	vmovdqu YMMWORD PTR [rdi+960], ymm6
	vmovdqu YMMWORD PTR [rdi+992], ymm7
	vzeroupper
	lfence
	mov DWORD PTR [rbx+768], r11d
	ldmxcsr DWORD PTR [rbx+768]
	mov rbp, QWORD PTR [rbx+3072]
	mov r12, QWORD PTR [rbx+3080]
	mov r13, QWORD PTR [rbx+3088]
	mov r14, QWORD PTR [rbx+3096]
	mov r15, QWORD PTR [rbx+3104]
	mov rbx, QWORD PTR [rbx+3112]
	mov rdi, rbx
	add rdi, 10240
	mov rsi, r13
	add rsi, 1536
	mov eax, 3329
	vmovq xmm15, rax
	vpbroadcastd ymm15, xmm15
	vpxor ymm14, ymm14, ymm14
	mov ecx, 16
27:
	vmovdqu ymm2, YMMWORD PTR [rsi]
	vpermq ymm2, ymm2, 216
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpunpcklwd ymm1, ymm2, ymm14
	vpaddd ymm0, ymm0, ymm1
	vpsubd ymm0, ymm0, ymm15
	vpsrad ymm1, ymm0, 31
	vpand ymm1, ymm1, ymm15
	vpaddd ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rdi+32]
	vpunpckhwd ymm1, ymm2, ymm14
	vpaddd ymm0, ymm0, ymm1
	vpsubd ymm0, ymm0, ymm15
	vpsrad ymm1, ymm0, 31
	vpand ymm1, ymm1, ymm15
	vpaddd ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rdi, 64
	add rsi, 32
	sub rcx, 1
	jne 27b
	vzeroupper
	mov rdi, rbx
	add rdi, 10240
	mov esi, 10
	mov rdx, r15
	add rdx, 0
	mov ecx, 320
	mov esi, esi
	mov r8, rdx
	cmp esi, 1
	je 28f
	cmp esi, 4
	je 210f
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm8, YMMWORD PTR [rax+512]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm9, YMMWORD PTR [rax+544]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm10, YMMWORD PTR [rax+576]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm11, YMMWORD PTR [rax+608]
	mov eax, 262080
	vmovq xmm12, rax
	vpbroadcastd ymm12, xmm12
	mov eax, 1023
	vmovq xmm13, rax
	vpbroadcastd ymm13, xmm13
	mov ecx, 31
212:
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpslld ymm1, ymm0, 17
	vpslld ymm2, ymm0, 15
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 11
	vpslld ymm3, ymm0, 9
	vpaddd ymm2, ymm2, ymm3
	vpsubd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 3
	vpaddd ymm2, ymm2, ymm0
	vpsubd ymm1, ymm1, ymm2
	vpaddd ymm1, ymm1, ymm12
	vpsrld ymm1, ymm1, 19
	vpand ymm1, ymm1, ymm13
	vpsllvd ymm1, ymm1, ymm8
	vpsrlq ymm2, ymm1, 32
	vpaddd ymm1, ymm1, ymm2
	vpand ymm1, ymm1, ymm9
	vpsllvq ymm1, ymm1, ymm10
	vpsrldq ymm2, ymm1, 8
	vpaddq ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm11
	vextracti128 xmm2, ymm1, 1
	vpor xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [r8], xmm1
	add rdi, 32
	add r8, 10
	sub rcx, 1
	jne 212b
	vpsrldq xmm4, xmm1, 4
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpslld ymm1, ymm0, 17
	vpslld ymm2, ymm0, 15
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 11
	vpslld ymm3, ymm0, 9
	vpaddd ymm2, ymm2, ymm3
	vpsubd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 3
	vpaddd ymm2, ymm2, ymm0
	vpsubd ymm1, ymm1, ymm2
	vpaddd ymm1, ymm1, ymm12
	vpsrld ymm1, ymm1, 19
	vpand ymm1, ymm1, ymm13
	vpsllvd ymm1, ymm1, ymm8
	vpsrlq ymm2, ymm1, 32
	vpaddd ymm1, ymm1, ymm2
	vpand ymm1, ymm1, ymm9
	vpsllvq ymm1, ymm1, ymm10
	vpsrldq ymm2, ymm1, 8
	vpaddq ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm11
	vextracti128 xmm2, ymm1, 1
	vpor xmm1, xmm1, xmm2
	vpslldq xmm1, xmm1, 6
	vpor xmm1, xmm1, xmm4
	sub r8, 6
	vmovdqu XMMWORD PTR [r8], xmm1
	vzeroupper
	jmp 211f
210:
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm8, YMMWORD PTR [rax+640]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm11, YMMWORD PTR [rax+672]
	mov eax, 262080
	vmovq xmm12, rax
	vpbroadcastd ymm12, xmm12
	mov eax, 15
	vmovq xmm13, rax
	vpbroadcastd ymm13, xmm13
	mov ecx, 8
213:
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpslld ymm1, ymm0, 11
	vpslld ymm2, ymm0, 9
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 5
	vpslld ymm3, ymm0, 3
	vpaddd ymm2, ymm2, ymm3
	vpsubd ymm1, ymm1, ymm2
	vpaddd ymm1, ymm1, ymm12
	vpsrld ymm1, ymm1, 19
	vpand ymm1, ymm1, ymm13
	vpsllvd ymm1, ymm1, ymm8
	vpsrlq ymm2, ymm1, 32
	vpaddd ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm11
	vextracti128 xmm2, ymm1, 1
	vpor xmm1, xmm1, xmm2
	vmovdqa xmm4, xmm1
	vmovdqu ymm0, YMMWORD PTR [rdi+32]
	vpslld ymm1, ymm0, 11
	vpslld ymm2, ymm0, 9
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 5
	vpslld ymm3, ymm0, 3
	vpaddd ymm2, ymm2, ymm3
	vpsubd ymm1, ymm1, ymm2
	vpaddd ymm1, ymm1, ymm12
	vpsrld ymm1, ymm1, 19
	vpand ymm1, ymm1, ymm13
	vpsllvd ymm1, ymm1, ymm8
	vpsrlq ymm2, ymm1, 32
	vpaddd ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm11
	vextracti128 xmm2, ymm1, 1
	vpor xmm1, xmm1, xmm2
	vmovdqa xmm5, xmm1
	vmovdqu ymm0, YMMWORD PTR [rdi+64]
	vpslld ymm1, ymm0, 11
	vpslld ymm2, ymm0, 9
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 5
	vpslld ymm3, ymm0, 3
	vpaddd ymm2, ymm2, ymm3
	vpsubd ymm1, ymm1, ymm2
	vpaddd ymm1, ymm1, ymm12
	vpsrld ymm1, ymm1, 19
	vpand ymm1, ymm1, ymm13
	vpsllvd ymm1, ymm1, ymm8
	vpsrlq ymm2, ymm1, 32
	vpaddd ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm11
	vextracti128 xmm2, ymm1, 1
	vpor xmm1, xmm1, xmm2
	vmovdqa xmm6, xmm1
	vmovdqu ymm0, YMMWORD PTR [rdi+96]
	vpslld ymm1, ymm0, 11
	vpslld ymm2, ymm0, 9
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 5
	vpslld ymm3, ymm0, 3
	vpaddd ymm2, ymm2, ymm3
	vpsubd ymm1, ymm1, ymm2
	vpaddd ymm1, ymm1, ymm12
	vpsrld ymm1, ymm1, 19
	vpand ymm1, ymm1, ymm13
	vpsllvd ymm1, ymm1, ymm8
	vpsrlq ymm2, ymm1, 32
	vpaddd ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm11
	vextracti128 xmm2, ymm1, 1
	vpor xmm1, xmm1, xmm2
	vpunpckldq xmm4, xmm4, xmm5
	vpunpckldq xmm6, xmm6, xmm1
	vpunpcklqdq xmm4, xmm4, xmm6
	vmovdqu XMMWORD PTR [r8], xmm4
	add rdi, 128
	add r8, 16
	sub rcx, 1
	jne 213b
	vzeroupper
211:
	jmp 29f
28:
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm8, YMMWORD PTR [rax+704]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm9, YMMWORD PTR [rax+736]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm10, YMMWORD PTR [rax+768]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm11, YMMWORD PTR [rax+800]
	mov eax, 262080
	vmovq xmm12, rax
	vpbroadcastd ymm12, xmm12
	mov eax, 1
	vmovq xmm13, rax
	vpbroadcastd ymm13, xmm13
	mov ecx, 8
214:
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpslld ymm1, ymm0, 8
	vpslld ymm2, ymm0, 6
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 2
	vpaddd ymm2, ymm2, ymm0
	vpsubd ymm1, ymm1, ymm2
	vpaddd ymm1, ymm1, ymm12
	vpsrld ymm1, ymm1, 19
	vpand ymm1, ymm1, ymm13
	vpsllvd ymm4, ymm1, ymm8
	vmovdqu ymm0, YMMWORD PTR [rdi+32]
	vpslld ymm1, ymm0, 8
	vpslld ymm2, ymm0, 6
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 2
	vpaddd ymm2, ymm2, ymm0
	vpsubd ymm1, ymm1, ymm2
	vpaddd ymm1, ymm1, ymm12
	vpsrld ymm1, ymm1, 19
	vpand ymm1, ymm1, ymm13
	vpsllvd ymm1, ymm1, ymm9
	vpaddd ymm4, ymm4, ymm1
	vmovdqu ymm0, YMMWORD PTR [rdi+64]
	vpslld ymm1, ymm0, 8
	vpslld ymm2, ymm0, 6
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 2
	vpaddd ymm2, ymm2, ymm0
	vpsubd ymm1, ymm1, ymm2
	vpaddd ymm1, ymm1, ymm12
	vpsrld ymm1, ymm1, 19
	vpand ymm1, ymm1, ymm13
	vpsllvd ymm1, ymm1, ymm10
	vpaddd ymm4, ymm4, ymm1
	vmovdqu ymm0, YMMWORD PTR [rdi+96]
	vpslld ymm1, ymm0, 8
	vpslld ymm2, ymm0, 6
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 2
	vpaddd ymm2, ymm2, ymm0
	vpsubd ymm1, ymm1, ymm2
	vpaddd ymm1, ymm1, ymm12
	vpsrld ymm1, ymm1, 19
	vpand ymm1, ymm1, ymm13
	vpsllvd ymm1, ymm1, ymm11
	vpaddd ymm4, ymm4, ymm1
	vpsrlq ymm1, ymm4, 32
	vpaddd ymm4, ymm4, ymm1
	vpsrldq ymm1, ymm4, 8
	vpaddd ymm4, ymm4, ymm1
	vextracti128 xmm1, ymm4, 1
	vpaddd xmm4, xmm4, xmm1
	movq rax, xmm4
	mov DWORD PTR [r8], eax
	add rdi, 128
	add r8, 4
	sub rcx, 1
	jne 214b
	vzeroupper
29:
	mov rdi, rbx
	add rdi, 11264
	mov rsi, r13
	add rsi, 2048
	mov eax, 3329
	vmovq xmm15, rax
	vpbroadcastd ymm15, xmm15
	vpxor ymm14, ymm14, ymm14
	mov ecx, 16
215:
	vmovdqu ymm2, YMMWORD PTR [rsi]
	vpermq ymm2, ymm2, 216
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpunpcklwd ymm1, ymm2, ymm14
	vpaddd ymm0, ymm0, ymm1
	vpsubd ymm0, ymm0, ymm15
	vpsrad ymm1, ymm0, 31
	vpand ymm1, ymm1, ymm15
	vpaddd ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rdi+32]
	vpunpckhwd ymm1, ymm2, ymm14
	vpaddd ymm0, ymm0, ymm1
	vpsubd ymm0, ymm0, ymm15
	vpsrad ymm1, ymm0, 31
	vpand ymm1, ymm1, ymm15
	vpaddd ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rdi, 64
	add rsi, 32
	sub rcx, 1
	jne 215b
	vzeroupper
	mov rdi, rbx
	add rdi, 11264
	mov esi, 10
	mov rdx, r15
	add rdx, 320
	mov ecx, 320
	mov esi, esi
	mov r8, rdx
	cmp esi, 1
	je 216f
	cmp esi, 4
	je 218f
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm8, YMMWORD PTR [rax+512]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm9, YMMWORD PTR [rax+544]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm10, YMMWORD PTR [rax+576]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm11, YMMWORD PTR [rax+608]
	mov eax, 262080
	vmovq xmm12, rax
	vpbroadcastd ymm12, xmm12
	mov eax, 1023
	vmovq xmm13, rax
	vpbroadcastd ymm13, xmm13
	mov ecx, 31
220:
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpslld ymm1, ymm0, 17
	vpslld ymm2, ymm0, 15
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 11
	vpslld ymm3, ymm0, 9
	vpaddd ymm2, ymm2, ymm3
	vpsubd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 3
	vpaddd ymm2, ymm2, ymm0
	vpsubd ymm1, ymm1, ymm2
	vpaddd ymm1, ymm1, ymm12
	vpsrld ymm1, ymm1, 19
	vpand ymm1, ymm1, ymm13
	vpsllvd ymm1, ymm1, ymm8
	vpsrlq ymm2, ymm1, 32
	vpaddd ymm1, ymm1, ymm2
	vpand ymm1, ymm1, ymm9
	vpsllvq ymm1, ymm1, ymm10
	vpsrldq ymm2, ymm1, 8
	vpaddq ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm11
	vextracti128 xmm2, ymm1, 1
	vpor xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [r8], xmm1
	add rdi, 32
	add r8, 10
	sub rcx, 1
	jne 220b
	vpsrldq xmm4, xmm1, 4
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpslld ymm1, ymm0, 17
	vpslld ymm2, ymm0, 15
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 11
	vpslld ymm3, ymm0, 9
	vpaddd ymm2, ymm2, ymm3
	vpsubd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 3
	vpaddd ymm2, ymm2, ymm0
	vpsubd ymm1, ymm1, ymm2
	vpaddd ymm1, ymm1, ymm12
	vpsrld ymm1, ymm1, 19
	vpand ymm1, ymm1, ymm13
	vpsllvd ymm1, ymm1, ymm8
	vpsrlq ymm2, ymm1, 32
	vpaddd ymm1, ymm1, ymm2
	vpand ymm1, ymm1, ymm9
	vpsllvq ymm1, ymm1, ymm10
	vpsrldq ymm2, ymm1, 8
	vpaddq ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm11
	vextracti128 xmm2, ymm1, 1
	vpor xmm1, xmm1, xmm2
	vpslldq xmm1, xmm1, 6
	vpor xmm1, xmm1, xmm4
	sub r8, 6
	vmovdqu XMMWORD PTR [r8], xmm1
	vzeroupper
	jmp 219f
218:
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm8, YMMWORD PTR [rax+640]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm11, YMMWORD PTR [rax+672]
	mov eax, 262080
	vmovq xmm12, rax
	vpbroadcastd ymm12, xmm12
	mov eax, 15
	vmovq xmm13, rax
	vpbroadcastd ymm13, xmm13
	mov ecx, 8
221:
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpslld ymm1, ymm0, 11
	vpslld ymm2, ymm0, 9
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 5
	vpslld ymm3, ymm0, 3
	vpaddd ymm2, ymm2, ymm3
	vpsubd ymm1, ymm1, ymm2
	vpaddd ymm1, ymm1, ymm12
	vpsrld ymm1, ymm1, 19
	vpand ymm1, ymm1, ymm13
	vpsllvd ymm1, ymm1, ymm8
	vpsrlq ymm2, ymm1, 32
	vpaddd ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm11
	vextracti128 xmm2, ymm1, 1
	vpor xmm1, xmm1, xmm2
	vmovdqa xmm4, xmm1
	vmovdqu ymm0, YMMWORD PTR [rdi+32]
	vpslld ymm1, ymm0, 11
	vpslld ymm2, ymm0, 9
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 5
	vpslld ymm3, ymm0, 3
	vpaddd ymm2, ymm2, ymm3
	vpsubd ymm1, ymm1, ymm2
	vpaddd ymm1, ymm1, ymm12
	vpsrld ymm1, ymm1, 19
	vpand ymm1, ymm1, ymm13
	vpsllvd ymm1, ymm1, ymm8
	vpsrlq ymm2, ymm1, 32
	vpaddd ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm11
	vextracti128 xmm2, ymm1, 1
	vpor xmm1, xmm1, xmm2
	vmovdqa xmm5, xmm1
	vmovdqu ymm0, YMMWORD PTR [rdi+64]
	vpslld ymm1, ymm0, 11
	vpslld ymm2, ymm0, 9
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 5
	vpslld ymm3, ymm0, 3
	vpaddd ymm2, ymm2, ymm3
	vpsubd ymm1, ymm1, ymm2
	vpaddd ymm1, ymm1, ymm12
	vpsrld ymm1, ymm1, 19
	vpand ymm1, ymm1, ymm13
	vpsllvd ymm1, ymm1, ymm8
	vpsrlq ymm2, ymm1, 32
	vpaddd ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm11
	vextracti128 xmm2, ymm1, 1
	vpor xmm1, xmm1, xmm2
	vmovdqa xmm6, xmm1
	vmovdqu ymm0, YMMWORD PTR [rdi+96]
	vpslld ymm1, ymm0, 11
	vpslld ymm2, ymm0, 9
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 5
	vpslld ymm3, ymm0, 3
	vpaddd ymm2, ymm2, ymm3
	vpsubd ymm1, ymm1, ymm2
	vpaddd ymm1, ymm1, ymm12
	vpsrld ymm1, ymm1, 19
	vpand ymm1, ymm1, ymm13
	vpsllvd ymm1, ymm1, ymm8
	vpsrlq ymm2, ymm1, 32
	vpaddd ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm11
	vextracti128 xmm2, ymm1, 1
	vpor xmm1, xmm1, xmm2
	vpunpckldq xmm4, xmm4, xmm5
	vpunpckldq xmm6, xmm6, xmm1
	vpunpcklqdq xmm4, xmm4, xmm6
	vmovdqu XMMWORD PTR [r8], xmm4
	add rdi, 128
	add r8, 16
	sub rcx, 1
	jne 221b
	vzeroupper
219:
	jmp 217f
216:
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm8, YMMWORD PTR [rax+704]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm9, YMMWORD PTR [rax+736]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm10, YMMWORD PTR [rax+768]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm11, YMMWORD PTR [rax+800]
	mov eax, 262080
	vmovq xmm12, rax
	vpbroadcastd ymm12, xmm12
	mov eax, 1
	vmovq xmm13, rax
	vpbroadcastd ymm13, xmm13
	mov ecx, 8
222:
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpslld ymm1, ymm0, 8
	vpslld ymm2, ymm0, 6
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 2
	vpaddd ymm2, ymm2, ymm0
	vpsubd ymm1, ymm1, ymm2
	vpaddd ymm1, ymm1, ymm12
	vpsrld ymm1, ymm1, 19
	vpand ymm1, ymm1, ymm13
	vpsllvd ymm4, ymm1, ymm8
	vmovdqu ymm0, YMMWORD PTR [rdi+32]
	vpslld ymm1, ymm0, 8
	vpslld ymm2, ymm0, 6
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 2
	vpaddd ymm2, ymm2, ymm0
	vpsubd ymm1, ymm1, ymm2
	vpaddd ymm1, ymm1, ymm12
	vpsrld ymm1, ymm1, 19
	vpand ymm1, ymm1, ymm13
	vpsllvd ymm1, ymm1, ymm9
	vpaddd ymm4, ymm4, ymm1
	vmovdqu ymm0, YMMWORD PTR [rdi+64]
	vpslld ymm1, ymm0, 8
	vpslld ymm2, ymm0, 6
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 2
	vpaddd ymm2, ymm2, ymm0
	vpsubd ymm1, ymm1, ymm2
	vpaddd ymm1, ymm1, ymm12
	vpsrld ymm1, ymm1, 19
	vpand ymm1, ymm1, ymm13
	vpsllvd ymm1, ymm1, ymm10
	vpaddd ymm4, ymm4, ymm1
	vmovdqu ymm0, YMMWORD PTR [rdi+96]
	vpslld ymm1, ymm0, 8
	vpslld ymm2, ymm0, 6
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 2
	vpaddd ymm2, ymm2, ymm0
	vpsubd ymm1, ymm1, ymm2
	vpaddd ymm1, ymm1, ymm12
	vpsrld ymm1, ymm1, 19
	vpand ymm1, ymm1, ymm13
	vpsllvd ymm1, ymm1, ymm11
	vpaddd ymm4, ymm4, ymm1
	vpsrlq ymm1, ymm4, 32
	vpaddd ymm4, ymm4, ymm1
	vpsrldq ymm1, ymm4, 8
	vpaddd ymm4, ymm4, ymm1
	vextracti128 xmm1, ymm4, 1
	vpaddd xmm4, xmm4, xmm1
	movq rax, xmm4
	mov DWORD PTR [r8], eax
	add rdi, 128
	add r8, 4
	sub rcx, 1
	jne 222b
	vzeroupper
217:
	mov rdi, rbx
	add rdi, 12288
	mov rsi, r13
	add rsi, 2560
	mov eax, 3329
	vmovq xmm15, rax
	vpbroadcastd ymm15, xmm15
	vpxor ymm14, ymm14, ymm14
	mov ecx, 16
223:
	vmovdqu ymm2, YMMWORD PTR [rsi]
	vpermq ymm2, ymm2, 216
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpunpcklwd ymm1, ymm2, ymm14
	vpaddd ymm0, ymm0, ymm1
	vpsubd ymm0, ymm0, ymm15
	vpsrad ymm1, ymm0, 31
	vpand ymm1, ymm1, ymm15
	vpaddd ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rdi+32]
	vpunpckhwd ymm1, ymm2, ymm14
	vpaddd ymm0, ymm0, ymm1
	vpsubd ymm0, ymm0, ymm15
	vpsrad ymm1, ymm0, 31
	vpand ymm1, ymm1, ymm15
	vpaddd ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rdi, 64
	add rsi, 32
	sub rcx, 1
	jne 223b
	vzeroupper
	mov rdi, rbx
	add rdi, 12288
	mov esi, 10
	mov rdx, r15
	add rdx, 640
	mov ecx, 320
	mov esi, esi
	mov r8, rdx
	cmp esi, 1
	je 224f
	cmp esi, 4
	je 226f
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm8, YMMWORD PTR [rax+512]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm9, YMMWORD PTR [rax+544]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm10, YMMWORD PTR [rax+576]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm11, YMMWORD PTR [rax+608]
	mov eax, 262080
	vmovq xmm12, rax
	vpbroadcastd ymm12, xmm12
	mov eax, 1023
	vmovq xmm13, rax
	vpbroadcastd ymm13, xmm13
	mov ecx, 31
228:
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpslld ymm1, ymm0, 17
	vpslld ymm2, ymm0, 15
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 11
	vpslld ymm3, ymm0, 9
	vpaddd ymm2, ymm2, ymm3
	vpsubd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 3
	vpaddd ymm2, ymm2, ymm0
	vpsubd ymm1, ymm1, ymm2
	vpaddd ymm1, ymm1, ymm12
	vpsrld ymm1, ymm1, 19
	vpand ymm1, ymm1, ymm13
	vpsllvd ymm1, ymm1, ymm8
	vpsrlq ymm2, ymm1, 32
	vpaddd ymm1, ymm1, ymm2
	vpand ymm1, ymm1, ymm9
	vpsllvq ymm1, ymm1, ymm10
	vpsrldq ymm2, ymm1, 8
	vpaddq ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm11
	vextracti128 xmm2, ymm1, 1
	vpor xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [r8], xmm1
	add rdi, 32
	add r8, 10
	sub rcx, 1
	jne 228b
	vpsrldq xmm4, xmm1, 4
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpslld ymm1, ymm0, 17
	vpslld ymm2, ymm0, 15
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 11
	vpslld ymm3, ymm0, 9
	vpaddd ymm2, ymm2, ymm3
	vpsubd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 3
	vpaddd ymm2, ymm2, ymm0
	vpsubd ymm1, ymm1, ymm2
	vpaddd ymm1, ymm1, ymm12
	vpsrld ymm1, ymm1, 19
	vpand ymm1, ymm1, ymm13
	vpsllvd ymm1, ymm1, ymm8
	vpsrlq ymm2, ymm1, 32
	vpaddd ymm1, ymm1, ymm2
	vpand ymm1, ymm1, ymm9
	vpsllvq ymm1, ymm1, ymm10
	vpsrldq ymm2, ymm1, 8
	vpaddq ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm11
	vextracti128 xmm2, ymm1, 1
	vpor xmm1, xmm1, xmm2
	vpslldq xmm1, xmm1, 6
	vpor xmm1, xmm1, xmm4
	sub r8, 6
	vmovdqu XMMWORD PTR [r8], xmm1
	vzeroupper
	jmp 227f
226:
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm8, YMMWORD PTR [rax+640]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm11, YMMWORD PTR [rax+672]
	mov eax, 262080
	vmovq xmm12, rax
	vpbroadcastd ymm12, xmm12
	mov eax, 15
	vmovq xmm13, rax
	vpbroadcastd ymm13, xmm13
	mov ecx, 8
229:
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpslld ymm1, ymm0, 11
	vpslld ymm2, ymm0, 9
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 5
	vpslld ymm3, ymm0, 3
	vpaddd ymm2, ymm2, ymm3
	vpsubd ymm1, ymm1, ymm2
	vpaddd ymm1, ymm1, ymm12
	vpsrld ymm1, ymm1, 19
	vpand ymm1, ymm1, ymm13
	vpsllvd ymm1, ymm1, ymm8
	vpsrlq ymm2, ymm1, 32
	vpaddd ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm11
	vextracti128 xmm2, ymm1, 1
	vpor xmm1, xmm1, xmm2
	vmovdqa xmm4, xmm1
	vmovdqu ymm0, YMMWORD PTR [rdi+32]
	vpslld ymm1, ymm0, 11
	vpslld ymm2, ymm0, 9
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 5
	vpslld ymm3, ymm0, 3
	vpaddd ymm2, ymm2, ymm3
	vpsubd ymm1, ymm1, ymm2
	vpaddd ymm1, ymm1, ymm12
	vpsrld ymm1, ymm1, 19
	vpand ymm1, ymm1, ymm13
	vpsllvd ymm1, ymm1, ymm8
	vpsrlq ymm2, ymm1, 32
	vpaddd ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm11
	vextracti128 xmm2, ymm1, 1
	vpor xmm1, xmm1, xmm2
	vmovdqa xmm5, xmm1
	vmovdqu ymm0, YMMWORD PTR [rdi+64]
	vpslld ymm1, ymm0, 11
	vpslld ymm2, ymm0, 9
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 5
	vpslld ymm3, ymm0, 3
	vpaddd ymm2, ymm2, ymm3
	vpsubd ymm1, ymm1, ymm2
	vpaddd ymm1, ymm1, ymm12
	vpsrld ymm1, ymm1, 19
	vpand ymm1, ymm1, ymm13
	vpsllvd ymm1, ymm1, ymm8
	vpsrlq ymm2, ymm1, 32
	vpaddd ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm11
	vextracti128 xmm2, ymm1, 1
	vpor xmm1, xmm1, xmm2
	vmovdqa xmm6, xmm1
	vmovdqu ymm0, YMMWORD PTR [rdi+96]
	vpslld ymm1, ymm0, 11
	vpslld ymm2, ymm0, 9
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 5
	vpslld ymm3, ymm0, 3
	vpaddd ymm2, ymm2, ymm3
	vpsubd ymm1, ymm1, ymm2
	vpaddd ymm1, ymm1, ymm12
	vpsrld ymm1, ymm1, 19
	vpand ymm1, ymm1, ymm13
	vpsllvd ymm1, ymm1, ymm8
	vpsrlq ymm2, ymm1, 32
	vpaddd ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm11
	vextracti128 xmm2, ymm1, 1
	vpor xmm1, xmm1, xmm2
	vpunpckldq xmm4, xmm4, xmm5
	vpunpckldq xmm6, xmm6, xmm1
	vpunpcklqdq xmm4, xmm4, xmm6
	vmovdqu XMMWORD PTR [r8], xmm4
	add rdi, 128
	add r8, 16
	sub rcx, 1
	jne 229b
	vzeroupper
227:
	jmp 225f
224:
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm8, YMMWORD PTR [rax+704]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm9, YMMWORD PTR [rax+736]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm10, YMMWORD PTR [rax+768]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm11, YMMWORD PTR [rax+800]
	mov eax, 262080
	vmovq xmm12, rax
	vpbroadcastd ymm12, xmm12
	mov eax, 1
	vmovq xmm13, rax
	vpbroadcastd ymm13, xmm13
	mov ecx, 8
230:
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpslld ymm1, ymm0, 8
	vpslld ymm2, ymm0, 6
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 2
	vpaddd ymm2, ymm2, ymm0
	vpsubd ymm1, ymm1, ymm2
	vpaddd ymm1, ymm1, ymm12
	vpsrld ymm1, ymm1, 19
	vpand ymm1, ymm1, ymm13
	vpsllvd ymm4, ymm1, ymm8
	vmovdqu ymm0, YMMWORD PTR [rdi+32]
	vpslld ymm1, ymm0, 8
	vpslld ymm2, ymm0, 6
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 2
	vpaddd ymm2, ymm2, ymm0
	vpsubd ymm1, ymm1, ymm2
	vpaddd ymm1, ymm1, ymm12
	vpsrld ymm1, ymm1, 19
	vpand ymm1, ymm1, ymm13
	vpsllvd ymm1, ymm1, ymm9
	vpaddd ymm4, ymm4, ymm1
	vmovdqu ymm0, YMMWORD PTR [rdi+64]
	vpslld ymm1, ymm0, 8
	vpslld ymm2, ymm0, 6
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 2
	vpaddd ymm2, ymm2, ymm0
	vpsubd ymm1, ymm1, ymm2
	vpaddd ymm1, ymm1, ymm12
	vpsrld ymm1, ymm1, 19
	vpand ymm1, ymm1, ymm13
	vpsllvd ymm1, ymm1, ymm10
	vpaddd ymm4, ymm4, ymm1
	vmovdqu ymm0, YMMWORD PTR [rdi+96]
	vpslld ymm1, ymm0, 8
	vpslld ymm2, ymm0, 6
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 2
	vpaddd ymm2, ymm2, ymm0
	vpsubd ymm1, ymm1, ymm2
	vpaddd ymm1, ymm1, ymm12
	vpsrld ymm1, ymm1, 19
	vpand ymm1, ymm1, ymm13
	vpsllvd ymm1, ymm1, ymm11
	vpaddd ymm4, ymm4, ymm1
	vpsrlq ymm1, ymm4, 32
	vpaddd ymm4, ymm4, ymm1
	vpsrldq ymm1, ymm4, 8
	vpaddd ymm4, ymm4, ymm1
	vextracti128 xmm1, ymm4, 1
	vpaddd xmm4, xmm4, xmm1
	movq rax, xmm4
	mov DWORD PTR [r8], eax
	add rdi, 128
	add r8, 4
	sub rcx, 1
	jne 230b
	vzeroupper
225:
	mov rdi, rbx
	add rdi, 13312
	mov rsi, r13
	add rsi, 3072
	mov eax, 3329
	vmovq xmm15, rax
	vpbroadcastd ymm15, xmm15
	vpxor ymm14, ymm14, ymm14
	mov ecx, 16
231:
	vmovdqu ymm2, YMMWORD PTR [rsi]
	vpermq ymm2, ymm2, 216
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpunpcklwd ymm1, ymm2, ymm14
	vpaddd ymm0, ymm0, ymm1
	vpsubd ymm0, ymm0, ymm15
	vpsrad ymm1, ymm0, 31
	vpand ymm1, ymm1, ymm15
	vpaddd ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rdi+32]
	vpunpckhwd ymm1, ymm2, ymm14
	vpaddd ymm0, ymm0, ymm1
	vpsubd ymm0, ymm0, ymm15
	vpsrad ymm1, ymm0, 31
	vpand ymm1, ymm1, ymm15
	vpaddd ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	add rdi, 64
	add rsi, 32
	sub rcx, 1
	jne 231b
	vzeroupper
	mov rdi, r14
	add rdi, 0
	mov esi, 32
	mov edx, 1
	mov rcx, rbx
	add rcx, 14336
	mov edx, edx
	mov rsi, rcx
	cmp edx, 1
	je 232f
	cmp edx, 4
	je 234f
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm8, YMMWORD PTR [rax+832]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm12, YMMWORD PTR [rax+864]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm9, YMMWORD PTR [rax+896]
	mov eax, 1023
	vmovq xmm10, rax
	vpbroadcastd ymm10, xmm10
	mov eax, 512
	vmovq xmm11, rax
	vpbroadcastd ymm11, xmm11
	mov ecx, 31
236:
	vbroadcasti128 ymm0, XMMWORD PTR [rdi]
	vpshufb ymm0, ymm0, ymm8
	vpsrlvd ymm0, ymm0, ymm9
	vpand ymm0, ymm0, ymm10
	vpslld ymm1, ymm0, 8
	vpaddd ymm1, ymm1, ymm0
	vpslld ymm2, ymm0, 12
	vpslld ymm3, ymm0, 10
	vpsubd ymm2, ymm2, ymm3
	vpaddd ymm1, ymm1, ymm2
	vpaddd ymm1, ymm1, ymm11
	vpsrld ymm1, ymm1, 10
	vmovdqu YMMWORD PTR [rsi], ymm1
	add rdi, 10
	add rsi, 32
	sub rcx, 1
	jne 236b
	sub rdi, 6
	vbroadcasti128 ymm0, XMMWORD PTR [rdi]
	vpshufb ymm0, ymm0, ymm12
	vpsrlvd ymm0, ymm0, ymm9
	vpand ymm0, ymm0, ymm10
	vpslld ymm1, ymm0, 8
	vpaddd ymm1, ymm1, ymm0
	vpslld ymm2, ymm0, 12
	vpslld ymm3, ymm0, 10
	vpsubd ymm2, ymm2, ymm3
	vpaddd ymm1, ymm1, ymm2
	vpaddd ymm1, ymm1, ymm11
	vpsrld ymm1, ymm1, 10
	vmovdqu YMMWORD PTR [rsi], ymm1
	vzeroupper
	jmp 235f
234:
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm8, YMMWORD PTR [rax+928]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm9, YMMWORD PTR [rax+960]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm10, YMMWORD PTR [rax+992]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm11, YMMWORD PTR [rax+1024]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm12, YMMWORD PTR [rax+640]
	mov eax, 15
	vmovq xmm13, rax
	vpbroadcastd ymm13, xmm13
	mov eax, 8
	vmovq xmm14, rax
	vpbroadcastd ymm14, xmm14
	mov ecx, 8
237:
	vbroadcasti128 ymm0, XMMWORD PTR [rdi]
	vpshufb ymm1, ymm0, ymm8
	vpsrlvd ymm1, ymm1, ymm12
	vpand ymm1, ymm1, ymm13
	vpslld ymm2, ymm1, 8
	vpaddd ymm2, ymm2, ymm1
	vpslld ymm3, ymm1, 12
	vpslld ymm4, ymm1, 10
	vpsubd ymm3, ymm3, ymm4
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm2, ymm2, ymm14
	vpsrld ymm2, ymm2, 4
	vmovdqu YMMWORD PTR [rsi], ymm2
	vpshufb ymm1, ymm0, ymm9
	vpsrlvd ymm1, ymm1, ymm12
	vpand ymm1, ymm1, ymm13
	vpslld ymm2, ymm1, 8
	vpaddd ymm2, ymm2, ymm1
	vpslld ymm3, ymm1, 12
	vpslld ymm4, ymm1, 10
	vpsubd ymm3, ymm3, ymm4
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm2, ymm2, ymm14
	vpsrld ymm2, ymm2, 4
	vmovdqu YMMWORD PTR [rsi+32], ymm2
	vpshufb ymm1, ymm0, ymm10
	vpsrlvd ymm1, ymm1, ymm12
	vpand ymm1, ymm1, ymm13
	vpslld ymm2, ymm1, 8
	vpaddd ymm2, ymm2, ymm1
	vpslld ymm3, ymm1, 12
	vpslld ymm4, ymm1, 10
	vpsubd ymm3, ymm3, ymm4
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm2, ymm2, ymm14
	vpsrld ymm2, ymm2, 4
	vmovdqu YMMWORD PTR [rsi+64], ymm2
	vpshufb ymm1, ymm0, ymm11
	vpsrlvd ymm1, ymm1, ymm12
	vpand ymm1, ymm1, ymm13
	vpslld ymm2, ymm1, 8
	vpaddd ymm2, ymm2, ymm1
	vpslld ymm3, ymm1, 12
	vpslld ymm4, ymm1, 10
	vpsubd ymm3, ymm3, ymm4
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm2, ymm2, ymm14
	vpsrld ymm2, ymm2, 4
	vmovdqu YMMWORD PTR [rsi+96], ymm2
	add rdi, 16
	add rsi, 128
	sub rcx, 1
	jne 237b
	vzeroupper
235:
	jmp 233f
232:
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm8, YMMWORD PTR [rax+1056]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm9, YMMWORD PTR [rax+1088]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm10, YMMWORD PTR [rax+1120]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm11, YMMWORD PTR [rax+1152]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm12, YMMWORD PTR [rax+704]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm13, YMMWORD PTR [rax+736]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm14, YMMWORD PTR [rax+768]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm15, YMMWORD PTR [rax+800]
	mov eax, 1
	vmovq xmm6, rax
	vpbroadcastd ymm6, xmm6
	mov ecx, 2
238:
	vbroadcasti128 ymm0, XMMWORD PTR [rdi]
	vpshufb ymm1, ymm0, ymm8
	vpsrlvd ymm1, ymm1, ymm12
	vpand ymm1, ymm1, ymm6
	vpslld ymm2, ymm1, 8
	vpaddd ymm2, ymm2, ymm1
	vpslld ymm3, ymm1, 12
	vpslld ymm4, ymm1, 10
	vpsubd ymm3, ymm3, ymm4
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm2, ymm2, ymm6
	vpsrld ymm2, ymm2, 1
	vmovdqu YMMWORD PTR [rsi], ymm2
	vpshufb ymm1, ymm0, ymm8
	vpsrlvd ymm1, ymm1, ymm13
	vpand ymm1, ymm1, ymm6
	vpslld ymm2, ymm1, 8
	vpaddd ymm2, ymm2, ymm1
	vpslld ymm3, ymm1, 12
	vpslld ymm4, ymm1, 10
	vpsubd ymm3, ymm3, ymm4
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm2, ymm2, ymm6
	vpsrld ymm2, ymm2, 1
	vmovdqu YMMWORD PTR [rsi+32], ymm2
	vpshufb ymm1, ymm0, ymm8
	vpsrlvd ymm1, ymm1, ymm14
	vpand ymm1, ymm1, ymm6
	vpslld ymm2, ymm1, 8
	vpaddd ymm2, ymm2, ymm1
	vpslld ymm3, ymm1, 12
	vpslld ymm4, ymm1, 10
	vpsubd ymm3, ymm3, ymm4
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm2, ymm2, ymm6
	vpsrld ymm2, ymm2, 1
	vmovdqu YMMWORD PTR [rsi+64], ymm2
	vpshufb ymm1, ymm0, ymm8
	vpsrlvd ymm1, ymm1, ymm15
	vpand ymm1, ymm1, ymm6
	vpslld ymm2, ymm1, 8
	vpaddd ymm2, ymm2, ymm1
	vpslld ymm3, ymm1, 12
	vpslld ymm4, ymm1, 10
	vpsubd ymm3, ymm3, ymm4
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm2, ymm2, ymm6
	vpsrld ymm2, ymm2, 1
	vmovdqu YMMWORD PTR [rsi+96], ymm2
	vpshufb ymm1, ymm0, ymm9
	vpsrlvd ymm1, ymm1, ymm12
	vpand ymm1, ymm1, ymm6
	vpslld ymm2, ymm1, 8
	vpaddd ymm2, ymm2, ymm1
	vpslld ymm3, ymm1, 12
	vpslld ymm4, ymm1, 10
	vpsubd ymm3, ymm3, ymm4
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm2, ymm2, ymm6
	vpsrld ymm2, ymm2, 1
	vmovdqu YMMWORD PTR [rsi+128], ymm2
	vpshufb ymm1, ymm0, ymm9
	vpsrlvd ymm1, ymm1, ymm13
	vpand ymm1, ymm1, ymm6
	vpslld ymm2, ymm1, 8
	vpaddd ymm2, ymm2, ymm1
	vpslld ymm3, ymm1, 12
	vpslld ymm4, ymm1, 10
	vpsubd ymm3, ymm3, ymm4
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm2, ymm2, ymm6
	vpsrld ymm2, ymm2, 1
	vmovdqu YMMWORD PTR [rsi+160], ymm2
	vpshufb ymm1, ymm0, ymm9
	vpsrlvd ymm1, ymm1, ymm14
	vpand ymm1, ymm1, ymm6
	vpslld ymm2, ymm1, 8
	vpaddd ymm2, ymm2, ymm1
	vpslld ymm3, ymm1, 12
	vpslld ymm4, ymm1, 10
	vpsubd ymm3, ymm3, ymm4
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm2, ymm2, ymm6
	vpsrld ymm2, ymm2, 1
	vmovdqu YMMWORD PTR [rsi+192], ymm2
	vpshufb ymm1, ymm0, ymm9
	vpsrlvd ymm1, ymm1, ymm15
	vpand ymm1, ymm1, ymm6
	vpslld ymm2, ymm1, 8
	vpaddd ymm2, ymm2, ymm1
	vpslld ymm3, ymm1, 12
	vpslld ymm4, ymm1, 10
	vpsubd ymm3, ymm3, ymm4
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm2, ymm2, ymm6
	vpsrld ymm2, ymm2, 1
	vmovdqu YMMWORD PTR [rsi+224], ymm2
	vpshufb ymm1, ymm0, ymm10
	vpsrlvd ymm1, ymm1, ymm12
	vpand ymm1, ymm1, ymm6
	vpslld ymm2, ymm1, 8
	vpaddd ymm2, ymm2, ymm1
	vpslld ymm3, ymm1, 12
	vpslld ymm4, ymm1, 10
	vpsubd ymm3, ymm3, ymm4
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm2, ymm2, ymm6
	vpsrld ymm2, ymm2, 1
	vmovdqu YMMWORD PTR [rsi+256], ymm2
	vpshufb ymm1, ymm0, ymm10
	vpsrlvd ymm1, ymm1, ymm13
	vpand ymm1, ymm1, ymm6
	vpslld ymm2, ymm1, 8
	vpaddd ymm2, ymm2, ymm1
	vpslld ymm3, ymm1, 12
	vpslld ymm4, ymm1, 10
	vpsubd ymm3, ymm3, ymm4
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm2, ymm2, ymm6
	vpsrld ymm2, ymm2, 1
	vmovdqu YMMWORD PTR [rsi+288], ymm2
	vpshufb ymm1, ymm0, ymm10
	vpsrlvd ymm1, ymm1, ymm14
	vpand ymm1, ymm1, ymm6
	vpslld ymm2, ymm1, 8
	vpaddd ymm2, ymm2, ymm1
	vpslld ymm3, ymm1, 12
	vpslld ymm4, ymm1, 10
	vpsubd ymm3, ymm3, ymm4
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm2, ymm2, ymm6
	vpsrld ymm2, ymm2, 1
	vmovdqu YMMWORD PTR [rsi+320], ymm2
	vpshufb ymm1, ymm0, ymm10
	vpsrlvd ymm1, ymm1, ymm15
	vpand ymm1, ymm1, ymm6
	vpslld ymm2, ymm1, 8
	vpaddd ymm2, ymm2, ymm1
	vpslld ymm3, ymm1, 12
	vpslld ymm4, ymm1, 10
	vpsubd ymm3, ymm3, ymm4
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm2, ymm2, ymm6
	vpsrld ymm2, ymm2, 1
	vmovdqu YMMWORD PTR [rsi+352], ymm2
	vpshufb ymm1, ymm0, ymm11
	vpsrlvd ymm1, ymm1, ymm12
	vpand ymm1, ymm1, ymm6
	vpslld ymm2, ymm1, 8
	vpaddd ymm2, ymm2, ymm1
	vpslld ymm3, ymm1, 12
	vpslld ymm4, ymm1, 10
	vpsubd ymm3, ymm3, ymm4
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm2, ymm2, ymm6
	vpsrld ymm2, ymm2, 1
	vmovdqu YMMWORD PTR [rsi+384], ymm2
	vpshufb ymm1, ymm0, ymm11
	vpsrlvd ymm1, ymm1, ymm13
	vpand ymm1, ymm1, ymm6
	vpslld ymm2, ymm1, 8
	vpaddd ymm2, ymm2, ymm1
	vpslld ymm3, ymm1, 12
	vpslld ymm4, ymm1, 10
	vpsubd ymm3, ymm3, ymm4
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm2, ymm2, ymm6
	vpsrld ymm2, ymm2, 1
	vmovdqu YMMWORD PTR [rsi+416], ymm2
	vpshufb ymm1, ymm0, ymm11
	vpsrlvd ymm1, ymm1, ymm14
	vpand ymm1, ymm1, ymm6
	vpslld ymm2, ymm1, 8
	vpaddd ymm2, ymm2, ymm1
	vpslld ymm3, ymm1, 12
	vpslld ymm4, ymm1, 10
	vpsubd ymm3, ymm3, ymm4
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm2, ymm2, ymm6
	vpsrld ymm2, ymm2, 1
	vmovdqu YMMWORD PTR [rsi+448], ymm2
	vpshufb ymm1, ymm0, ymm11
	vpsrlvd ymm1, ymm1, ymm15
	vpand ymm1, ymm1, ymm6
	vpslld ymm2, ymm1, 8
	vpaddd ymm2, ymm2, ymm1
	vpslld ymm3, ymm1, 12
	vpslld ymm4, ymm1, 10
	vpsubd ymm3, ymm3, ymm4
	vpaddd ymm2, ymm2, ymm3
	vpaddd ymm2, ymm2, ymm6
	vpsrld ymm2, ymm2, 1
	vmovdqu YMMWORD PTR [rsi+480], ymm2
	add rdi, 16
	add rsi, 512
	sub rcx, 1
	jne 238b
	vzeroupper
233:
	mov rdi, rbx
	add rdi, 13312
	mov rsi, rbx
	add rsi, 14336
	mov eax, 3329
	vmovq xmm15, rax
	vpbroadcastd ymm15, xmm15
	mov ecx, 32
239:
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vmovdqu ymm1, YMMWORD PTR [rsi]
	vpaddd ymm0, ymm0, ymm1
	vpsubd ymm0, ymm0, ymm15
	vpsrad ymm1, ymm0, 31
	vpand ymm1, ymm1, ymm15
	vpaddd ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	add rdi, 32
	add rsi, 32
	sub rcx, 1
	jne 239b
	vzeroupper
	mov rdi, rbx
	add rdi, 13312
	mov esi, 4
	mov rdx, r15
	add rdx, 960
	mov ecx, 128
	mov esi, esi
	mov r8, rdx
	cmp esi, 1
	je 240f
	cmp esi, 4
	je 242f
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm8, YMMWORD PTR [rax+512]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm9, YMMWORD PTR [rax+544]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm10, YMMWORD PTR [rax+576]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm11, YMMWORD PTR [rax+608]
	mov eax, 262080
	vmovq xmm12, rax
	vpbroadcastd ymm12, xmm12
	mov eax, 1023
	vmovq xmm13, rax
	vpbroadcastd ymm13, xmm13
	mov ecx, 31
244:
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpslld ymm1, ymm0, 17
	vpslld ymm2, ymm0, 15
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 11
	vpslld ymm3, ymm0, 9
	vpaddd ymm2, ymm2, ymm3
	vpsubd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 3
	vpaddd ymm2, ymm2, ymm0
	vpsubd ymm1, ymm1, ymm2
	vpaddd ymm1, ymm1, ymm12
	vpsrld ymm1, ymm1, 19
	vpand ymm1, ymm1, ymm13
	vpsllvd ymm1, ymm1, ymm8
	vpsrlq ymm2, ymm1, 32
	vpaddd ymm1, ymm1, ymm2
	vpand ymm1, ymm1, ymm9
	vpsllvq ymm1, ymm1, ymm10
	vpsrldq ymm2, ymm1, 8
	vpaddq ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm11
	vextracti128 xmm2, ymm1, 1
	vpor xmm1, xmm1, xmm2
	vmovdqu XMMWORD PTR [r8], xmm1
	add rdi, 32
	add r8, 10
	sub rcx, 1
	jne 244b
	vpsrldq xmm4, xmm1, 4
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpslld ymm1, ymm0, 17
	vpslld ymm2, ymm0, 15
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 11
	vpslld ymm3, ymm0, 9
	vpaddd ymm2, ymm2, ymm3
	vpsubd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 3
	vpaddd ymm2, ymm2, ymm0
	vpsubd ymm1, ymm1, ymm2
	vpaddd ymm1, ymm1, ymm12
	vpsrld ymm1, ymm1, 19
	vpand ymm1, ymm1, ymm13
	vpsllvd ymm1, ymm1, ymm8
	vpsrlq ymm2, ymm1, 32
	vpaddd ymm1, ymm1, ymm2
	vpand ymm1, ymm1, ymm9
	vpsllvq ymm1, ymm1, ymm10
	vpsrldq ymm2, ymm1, 8
	vpaddq ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm11
	vextracti128 xmm2, ymm1, 1
	vpor xmm1, xmm1, xmm2
	vpslldq xmm1, xmm1, 6
	vpor xmm1, xmm1, xmm4
	sub r8, 6
	vmovdqu XMMWORD PTR [r8], xmm1
	vzeroupper
	jmp 243f
242:
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm8, YMMWORD PTR [rax+640]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm11, YMMWORD PTR [rax+672]
	mov eax, 262080
	vmovq xmm12, rax
	vpbroadcastd ymm12, xmm12
	mov eax, 15
	vmovq xmm13, rax
	vpbroadcastd ymm13, xmm13
	mov ecx, 8
245:
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpslld ymm1, ymm0, 11
	vpslld ymm2, ymm0, 9
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 5
	vpslld ymm3, ymm0, 3
	vpaddd ymm2, ymm2, ymm3
	vpsubd ymm1, ymm1, ymm2
	vpaddd ymm1, ymm1, ymm12
	vpsrld ymm1, ymm1, 19
	vpand ymm1, ymm1, ymm13
	vpsllvd ymm1, ymm1, ymm8
	vpsrlq ymm2, ymm1, 32
	vpaddd ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm11
	vextracti128 xmm2, ymm1, 1
	vpor xmm1, xmm1, xmm2
	vmovdqa xmm4, xmm1
	vmovdqu ymm0, YMMWORD PTR [rdi+32]
	vpslld ymm1, ymm0, 11
	vpslld ymm2, ymm0, 9
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 5
	vpslld ymm3, ymm0, 3
	vpaddd ymm2, ymm2, ymm3
	vpsubd ymm1, ymm1, ymm2
	vpaddd ymm1, ymm1, ymm12
	vpsrld ymm1, ymm1, 19
	vpand ymm1, ymm1, ymm13
	vpsllvd ymm1, ymm1, ymm8
	vpsrlq ymm2, ymm1, 32
	vpaddd ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm11
	vextracti128 xmm2, ymm1, 1
	vpor xmm1, xmm1, xmm2
	vmovdqa xmm5, xmm1
	vmovdqu ymm0, YMMWORD PTR [rdi+64]
	vpslld ymm1, ymm0, 11
	vpslld ymm2, ymm0, 9
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 5
	vpslld ymm3, ymm0, 3
	vpaddd ymm2, ymm2, ymm3
	vpsubd ymm1, ymm1, ymm2
	vpaddd ymm1, ymm1, ymm12
	vpsrld ymm1, ymm1, 19
	vpand ymm1, ymm1, ymm13
	vpsllvd ymm1, ymm1, ymm8
	vpsrlq ymm2, ymm1, 32
	vpaddd ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm11
	vextracti128 xmm2, ymm1, 1
	vpor xmm1, xmm1, xmm2
	vmovdqa xmm6, xmm1
	vmovdqu ymm0, YMMWORD PTR [rdi+96]
	vpslld ymm1, ymm0, 11
	vpslld ymm2, ymm0, 9
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 5
	vpslld ymm3, ymm0, 3
	vpaddd ymm2, ymm2, ymm3
	vpsubd ymm1, ymm1, ymm2
	vpaddd ymm1, ymm1, ymm12
	vpsrld ymm1, ymm1, 19
	vpand ymm1, ymm1, ymm13
	vpsllvd ymm1, ymm1, ymm8
	vpsrlq ymm2, ymm1, 32
	vpaddd ymm1, ymm1, ymm2
	vpshufb ymm1, ymm1, ymm11
	vextracti128 xmm2, ymm1, 1
	vpor xmm1, xmm1, xmm2
	vpunpckldq xmm4, xmm4, xmm5
	vpunpckldq xmm6, xmm6, xmm1
	vpunpcklqdq xmm4, xmm4, xmm6
	vmovdqu XMMWORD PTR [r8], xmm4
	add rdi, 128
	add r8, 16
	sub rcx, 1
	jne 245b
	vzeroupper
243:
	jmp 241f
240:
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm8, YMMWORD PTR [rax+704]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm9, YMMWORD PTR [rax+736]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm10, YMMWORD PTR [rax+768]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm11, YMMWORD PTR [rax+800]
	mov eax, 262080
	vmovq xmm12, rax
	vpbroadcastd ymm12, xmm12
	mov eax, 1
	vmovq xmm13, rax
	vpbroadcastd ymm13, xmm13
	mov ecx, 8
246:
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpslld ymm1, ymm0, 8
	vpslld ymm2, ymm0, 6
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 2
	vpaddd ymm2, ymm2, ymm0
	vpsubd ymm1, ymm1, ymm2
	vpaddd ymm1, ymm1, ymm12
	vpsrld ymm1, ymm1, 19
	vpand ymm1, ymm1, ymm13
	vpsllvd ymm4, ymm1, ymm8
	vmovdqu ymm0, YMMWORD PTR [rdi+32]
	vpslld ymm1, ymm0, 8
	vpslld ymm2, ymm0, 6
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 2
	vpaddd ymm2, ymm2, ymm0
	vpsubd ymm1, ymm1, ymm2
	vpaddd ymm1, ymm1, ymm12
	vpsrld ymm1, ymm1, 19
	vpand ymm1, ymm1, ymm13
	vpsllvd ymm1, ymm1, ymm9
	vpaddd ymm4, ymm4, ymm1
	vmovdqu ymm0, YMMWORD PTR [rdi+64]
	vpslld ymm1, ymm0, 8
	vpslld ymm2, ymm0, 6
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 2
	vpaddd ymm2, ymm2, ymm0
	vpsubd ymm1, ymm1, ymm2
	vpaddd ymm1, ymm1, ymm12
	vpsrld ymm1, ymm1, 19
	vpand ymm1, ymm1, ymm13
	vpsllvd ymm1, ymm1, ymm10
	vpaddd ymm4, ymm4, ymm1
	vmovdqu ymm0, YMMWORD PTR [rdi+96]
	vpslld ymm1, ymm0, 8
	vpslld ymm2, ymm0, 6
	vpaddd ymm1, ymm1, ymm2
	vpslld ymm2, ymm0, 2
	vpaddd ymm2, ymm2, ymm0
	vpsubd ymm1, ymm1, ymm2
	vpaddd ymm1, ymm1, ymm12
	vpsrld ymm1, ymm1, 19
	vpand ymm1, ymm1, ymm13
	vpsllvd ymm1, ymm1, ymm11
	vpaddd ymm4, ymm4, ymm1
	vpsrlq ymm1, ymm4, 32
	vpaddd ymm4, ymm4, ymm1
	vpsrldq ymm1, ymm4, 8
	vpaddd ymm4, ymm4, ymm1
	vextracti128 xmm1, ymm4, 1
	vpaddd xmm4, xmm4, xmm1
	movq rax, xmm4
	mov DWORD PTR [r8], eax
	add rdi, 128
	add r8, 4
	sub rcx, 1
	jne 246b
	vzeroupper
241:
	mov r15, QWORD PTR [rbx+19496]
	mov r14, QWORD PTR [rbx+19488]
	mov r13, QWORD PTR [rbx+19480]
	mov r12, QWORD PTR [rbx+19472]
	mov rbp, QWORD PTR [rbx+19464]
	mov rbx, QWORD PTR [rbx+19456]
	ret
	.p2align 6
