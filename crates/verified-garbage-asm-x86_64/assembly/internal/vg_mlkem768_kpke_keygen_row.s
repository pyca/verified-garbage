// The functions of `src/internal/vg_mlkem768_kpke_keygen_row.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem768_kpke_keygen_row:
	mov QWORD PTR [r8+3072], rbp
	mov QWORD PTR [r8+3080], r12
	mov QWORD PTR [r8+3088], r13
	mov QWORD PTR [r8+3096], r14
	mov QWORD PTR [r8+3104], r15
	mov QWORD PTR [r8+3112], rbx
	mov rbx, r8
	mov r12, rdi
	mov rbp, rsi
	mov r15, rdx
	mov r13, rcx
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
	stmxcsr DWORD PTR [rbx+768]
	mov r11d, DWORD PTR [rbx+768]
	and r11d, 65535
	mov eax, 8127
	mov DWORD PTR [rbx+772], eax
	ldmxcsr DWORD PTR [rbx+772]
	lfence
	mov rdi, r13
	mov rsi, rbp
	mov rdx, r15
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
20:
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
	vmovdqu ymm7, YMMWORD PTR [rdx+32]
	vmovdqu ymm8, YMMWORD PTR [rdx+64]
	vmovdqu ymm9, YMMWORD PTR [rdx+96]
	vpshufd ymm6, ymm6, 216
	vpshufd ymm7, ymm7, 216
	vpshufd ymm8, ymm8, 216
	vpshufd ymm9, ymm9, 216
	vpunpckhqdq ymm10, ymm6, ymm7
	vpunpcklqdq ymm6, ymm6, ymm7
	vpunpckhqdq ymm5, ymm8, ymm9
	vpunpcklqdq ymm8, ymm8, ymm9
	vpackssdw ymm6, ymm6, ymm8
	vpackssdw ymm10, ymm10, ymm5
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
	vmovdqu ymm0, YMMWORD PTR [rsi+512]
	vmovdqu ymm1, YMMWORD PTR [rsi+544]
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
	vmovdqu ymm7, YMMWORD PTR [rdx+1056]
	vmovdqu ymm8, YMMWORD PTR [rdx+1088]
	vmovdqu ymm9, YMMWORD PTR [rdx+1120]
	vpshufd ymm6, ymm6, 216
	vpshufd ymm7, ymm7, 216
	vpshufd ymm8, ymm8, 216
	vpshufd ymm9, ymm9, 216
	vpunpckhqdq ymm10, ymm6, ymm7
	vpunpcklqdq ymm6, ymm6, ymm7
	vpunpckhqdq ymm5, ymm8, ymm9
	vpunpcklqdq ymm8, ymm8, ymm9
	vpackssdw ymm6, ymm6, ymm8
	vpackssdw ymm10, ymm10, ymm5
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
	vmovdqu ymm0, YMMWORD PTR [rsi+1024]
	vmovdqu ymm1, YMMWORD PTR [rsi+1056]
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
	vmovdqu ymm6, YMMWORD PTR [rdx+2048]
	vmovdqu ymm7, YMMWORD PTR [rdx+2080]
	vmovdqu ymm8, YMMWORD PTR [rdx+2112]
	vmovdqu ymm9, YMMWORD PTR [rdx+2144]
	vpshufd ymm6, ymm6, 216
	vpshufd ymm7, ymm7, 216
	vpshufd ymm8, ymm8, 216
	vpshufd ymm9, ymm9, 216
	vpunpckhqdq ymm10, ymm6, ymm7
	vpunpcklqdq ymm6, ymm6, ymm7
	vpunpckhqdq ymm5, ymm8, ymm9
	vpunpcklqdq ymm8, ymm8, ymm9
	vpackssdw ymm6, ymm6, ymm8
	vpackssdw ymm10, ymm10, ymm5
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
	mov eax, 3329
	vmovq xmm15, rax
	vpbroadcastd ymm15, xmm15
	vpxor ymm14, ymm14, ymm14
	vpunpcklwd ymm10, ymm11, ymm12
	vpunpckhwd ymm9, ymm11, ymm12
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vpunpcklwd ymm1, ymm10, ymm14
	vpaddd ymm0, ymm0, ymm1
	vpsubd ymm0, ymm0, ymm15
	vpsrad ymm1, ymm0, 31
	vpand ymm1, ymm1, ymm15
	vpaddd ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm0, YMMWORD PTR [rdi+32]
	vpunpckhwd ymm1, ymm10, ymm14
	vpaddd ymm0, ymm0, ymm1
	vpsubd ymm0, ymm0, ymm15
	vpsrad ymm1, ymm0, 31
	vpand ymm1, ymm1, ymm15
	vpaddd ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	vmovdqu ymm0, YMMWORD PTR [rdi+64]
	vpunpcklwd ymm1, ymm9, ymm14
	vpaddd ymm0, ymm0, ymm1
	vpsubd ymm0, ymm0, ymm15
	vpsrad ymm1, ymm0, 31
	vpand ymm1, ymm1, ymm15
	vpaddd ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+64], ymm0
	vmovdqu ymm0, YMMWORD PTR [rdi+96]
	vpunpckhwd ymm1, ymm9, ymm14
	vpaddd ymm0, ymm0, ymm1
	vpsubd ymm0, ymm0, ymm15
	vpsrad ymm1, ymm0, 31
	vpand ymm1, ymm1, ymm15
	vpaddd ymm0, ymm0, ymm1
	vmovdqu YMMWORD PTR [rdi+96], ymm0
	mov eax, 218172673
	vmovq xmm15, rax
	vpbroadcastd ymm15, xmm15
	mov eax, -217976063
	vmovq xmm14, rax
	vpbroadcastd ymm14, xmm14
	add rsi, 64
	add rdx, 128
	add rdi, 128
	add r8, 32
	sub rcx, 1
	jne 20b
	vzeroupper
	lfence
	mov DWORD PTR [rbx+768], r11d
	ldmxcsr DWORD PTR [rbx+768]
	mov rdi, r13
	add rdi, 0
	mov rsi, r12
	add rsi, 0
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm8, YMMWORD PTR [rax+1248]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm9, YMMWORD PTR [rax+1280]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm10, YMMWORD PTR [rax+1312]
	mov ecx, 8
21:
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vmovdqu ymm1, YMMWORD PTR [rdi+32]
	vpackssdw ymm0, ymm0, ymm1
	vpermq ymm0, ymm0, 216
	vpsrld ymm1, ymm0, 16
	vpslld ymm1, ymm1, 12
	vpslld ymm0, ymm0, 16
	vpsrld ymm0, ymm0, 16
	vpaddd ymm0, ymm0, ymm1
	vpshufb ymm0, ymm0, ymm8
	vmovdqu ymm2, YMMWORD PTR [rdi+64]
	vmovdqu ymm3, YMMWORD PTR [rdi+96]
	vpackssdw ymm2, ymm2, ymm3
	vpermq ymm2, ymm2, 216
	vpsrld ymm3, ymm2, 16
	vpslld ymm3, ymm3, 12
	vpslld ymm2, ymm2, 16
	vpsrld ymm2, ymm2, 16
	vpaddd ymm2, ymm2, ymm3
	vpshufb ymm2, ymm2, ymm8
	vpermd ymm0, ymm9, ymm0
	vpermd ymm2, ymm10, ymm2
	vpblendd ymm0, ymm0, ymm2, 192
	vmovdqu YMMWORD PTR [rsi], ymm0
	vmovdqu XMMWORD PTR [rsi+32], xmm2
	add rdi, 128
	add rsi, 48
	sub rcx, 1
	jne 21b
	vzeroupper
	mov rbp, QWORD PTR [rbx+3072]
	mov r12, QWORD PTR [rbx+3080]
	mov r13, QWORD PTR [rbx+3088]
	mov r14, QWORD PTR [rbx+3096]
	mov r15, QWORD PTR [rbx+3104]
	mov rbx, QWORD PTR [rbx+3112]
	ret
	.p2align 6
