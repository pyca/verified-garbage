// The functions of `src/internal/vg_ed25519_scalar_base_ifma.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed25519_scalar_base_ifma:
	mov QWORD PTR [rdx], rbx
	mov QWORD PTR [rdx+8], rbp
	mov QWORD PTR [rdx+16], r12
	mov QWORD PTR [rdx+24], r13
	mov QWORD PTR [rdx+32], r14
	mov QWORD PTR [rdx+40], r15
	mov QWORD PTR [rdx+48], rdi
	mov rdi, rdx
	mov ebx, 0
20:
	movzx eax, BYTE PTR [rsi+rbx*1]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+768], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+769], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+770], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+771], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+772], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+773], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+774], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+775], dl
	add rbx, 1
	movabs rax, 32
	cmp rbx, rax
	jne 20b
	movabs r8, 8496970652267935907
	movabs r9, 31536524315187371
	movabs r10, -8302596497594521448
	movabs r11, 5909686906226998899
	mov QWORD PTR [rdi+576], r8
	mov QWORD PTR [rdi+584], r9
	mov QWORD PTR [rdi+592], r10
	mov QWORD PTR [rdi+600], r11
	movabs r8, -3938910931347188454
	movabs r9, 7578651490590762930
	movabs r10, -4565275417906848676
	movabs r11, 2407515759118799870
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	movabs r8, 7378697629483820632
	movabs r9, 7378697629483820646
	movabs r10, 7378697629483820646
	movabs r11, 7378697629483820646
	mov QWORD PTR [rdi+96], r8
	mov QWORD PTR [rdi+104], r9
	mov QWORD PTR [rdi+112], r10
	mov QWORD PTR [rdi+120], r11
	movabs r8, 1
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	movabs r8, 7916917699147980195
	movabs r9, 2373572377730700021
	movabs r10, 7415826109900252029
	movabs r11, 7460035829407905381
	mov QWORD PTR [rdi+160], r8
	mov QWORD PTR [rdi+168], r9
	mov QWORD PTR [rdi+176], r10
	mov QWORD PTR [rdi+184], r11
	movabs r8, 3330543494210916119
	movabs r9, 1902264825305813167
	movabs r10, -3748029775530025619
	movabs r11, 4374419823296718264
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	movabs r8, -8092793657155591786
	movabs r9, -6965495218658762494
	movabs r10, 8277918600102524416
	movabs r11, 4481628782694999499
	mov QWORD PTR [rdi+96], r8
	mov QWORD PTR [rdi+104], r9
	mov QWORD PTR [rdi+112], r10
	mov QWORD PTR [rdi+120], r11
	movabs r8, 1
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	movabs r8, -197556581686363558
	movabs r9, 4578187817228758724
	movabs r10, -3794667859600543564
	movabs r11, 813975834179366073
	mov QWORD PTR [rdi+160], r8
	mov QWORD PTR [rdi+168], r9
	mov QWORD PTR [rdi+176], r10
	mov QWORD PTR [rdi+184], r11
	movabs r8, 1
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	mov QWORD PTR [rdi+448], r8
	mov QWORD PTR [rdi+456], r9
	mov QWORD PTR [rdi+464], r10
	mov QWORD PTR [rdi+472], r11
	movabs r8, 1
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	mov QWORD PTR [rdi+480], r8
	mov QWORD PTR [rdi+488], r9
	mov QWORD PTR [rdi+496], r10
	mov QWORD PTR [rdi+504], r11
	movabs r8, -1452802769173679783
	movabs r9, 63073048630374742
	movabs r10, 1841551078520508720
	movabs r11, 2596001775599221991
	mov QWORD PTR [rdi+512], r8
	mov QWORD PTR [rdi+520], r9
	mov QWORD PTR [rdi+528], r10
	mov QWORD PTR [rdi+536], r11
	movabs r8, 2
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	mov QWORD PTR [rdi+544], r8
	mov QWORD PTR [rdi+552], r9
	mov QWORD PTR [rdi+560], r10
	mov QWORD PTR [rdi+568], r11
	movabs rax, 2251799813685247
	mov ecx, 19
	movabs rdx, 4611686018427348992
	movabs rbp, 4611686018427385856
	mov r8d, 8191
	mov r9d, 67108863
	movabs r10, 549755813887
	mov r11d, 1
	mov r12d, 121665
	vmovq xmm9, rax
	vpbroadcastq ymm9, xmm9
	vmovdqu YMMWORD PTR [rdi+1664], ymm9
	vmovq xmm10, rcx
	vpbroadcastq ymm10, xmm10
	vmovdqu YMMWORD PTR [rdi+1696], ymm10
	vmovq xmm10, rdx
	vpbroadcastq ymm10, xmm10
	vmovdqu YMMWORD PTR [rdi+1728], ymm10
	vmovq xmm10, rbp
	vpbroadcastq ymm10, xmm10
	vmovdqu YMMWORD PTR [rdi+1760], ymm10
	vmovq xmm10, r8
	vpbroadcastq ymm10, xmm10
	vmovdqu YMMWORD PTR [rdi+1792], ymm10
	vmovq xmm10, r9
	vpbroadcastq ymm10, xmm10
	vmovdqu YMMWORD PTR [rdi+1824], ymm10
	vmovq xmm10, r10
	vpbroadcastq ymm10, xmm10
	vmovdqu YMMWORD PTR [rdi+1856], ymm10
	vmovdqu ymm11, YMMWORD PTR [rdi+64]
	vmovdqu ymm12, YMMWORD PTR [rdi+96]
	vmovdqu ymm13, YMMWORD PTR [rdi+128]
	vmovdqu ymm14, YMMWORD PTR [rdi+160]
	vpunpcklqdq ymm0, ymm11, ymm12
	vpunpckhqdq ymm1, ymm11, ymm12
	vpunpcklqdq ymm2, ymm13, ymm14
	vpunpckhqdq ymm3, ymm13, ymm14
	vperm2i128 ymm5, ymm0, ymm2, 32
	vperm2i128 ymm6, ymm1, ymm3, 32
	vperm2i128 ymm7, ymm0, ymm2, 49
	vperm2i128 ymm8, ymm1, ymm3, 49
	vpand ymm0, ymm5, ymm9
	vpsrlq ymm1, ymm5, 51
	vpsrlq ymm11, ymm9, 13
	vpand ymm11, ymm6, ymm11
	vpsllq ymm11, ymm11, 13
	vpor ymm1, ymm1, ymm11
	vpsrlq ymm2, ymm6, 38
	vpsrlq ymm11, ymm9, 26
	vpand ymm11, ymm7, ymm11
	vpsllq ymm11, ymm11, 26
	vpor ymm2, ymm2, ymm11
	vpsrlq ymm3, ymm7, 25
	vpsrlq ymm11, ymm9, 39
	vpand ymm11, ymm8, ymm11
	vpsllq ymm11, ymm11, 39
	vpor ymm3, ymm3, ymm11
	vpsrlq ymm4, ymm8, 12
	vmovdqu ymm9, YMMWORD PTR [rdi+1664]
	vshufi32x4 zmm9, zmm9, zmm9, 68
	vmovdqu32 ZMMWORD PTR [rdi+5504], zmm9
	vmovdqu ymm9, YMMWORD PTR [rdi+1696]
	vshufi32x4 zmm9, zmm9, zmm9, 68
	vmovdqu32 ZMMWORD PTR [rdi+5568], zmm9
	vmovdqu ymm9, YMMWORD PTR [rdi+1728]
	vshufi32x4 zmm9, zmm9, zmm9, 68
	vmovdqu32 ZMMWORD PTR [rdi+5632], zmm9
	vmovdqu ymm9, YMMWORD PTR [rdi+1760]
	vshufi32x4 zmm9, zmm9, zmm9, 68
	vmovdqu32 ZMMWORD PTR [rdi+5696], zmm9
	vmovdqu ymm9, YMMWORD PTR [rdi+544]
	vshufi32x4 zmm9, zmm9, zmm9, 68
	vmovdqu32 ZMMWORD PTR [rdi+6016], zmm9
	vpxor ymm10, ymm10, ymm10
	vpcmpeqd ymm11, ymm11, ymm11
	vpblendd ymm9, ymm10, ymm11, 3
	vshufi32x4 zmm9, zmm9, zmm9, 68
	vmovdqu32 ZMMWORD PTR [rdi+5760], zmm9
	vpblendd ymm9, ymm10, ymm11, 240
	vshufi32x4 zmm9, zmm9, zmm9, 68
	vmovdqu32 ZMMWORD PTR [rdi+5824], zmm9
	vpblendd ymm9, ymm10, ymm11, 51
	vshufi32x4 zmm9, zmm9, zmm9, 68
	vmovdqu32 ZMMWORD PTR [rdi+5888], zmm9
	vpblendd ymm9, ymm10, ymm11, 48
	vshufi32x4 zmm9, zmm9, zmm9, 68
	vmovdqu32 ZMMWORD PTR [rdi+5952], zmm9
	vshufi32x4 zmm0, zmm0, zmm0, 68
	vshufi32x4 zmm1, zmm1, zmm1, 68
	vshufi32x4 zmm2, zmm2, zmm2, 68
	vshufi32x4 zmm3, zmm3, zmm3, 68
	vshufi32x4 zmm4, zmm4, zmm4, 68
	stmxcsr DWORD PTR [rdi+1600]
	mov r11d, DWORD PTR [rdi+1600]
	and r11d, 65535
	mov eax, 8127
	mov DWORD PTR [rdi+1604], eax
	ldmxcsr DWORD PTR [rdi+1604]
	lfence
	mov ebx, 0
21:
	add rbx, 26
	mov rcx, rbx
	add rcx, rcx
	mov r9, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, r9
	mov r9, rbx
	cmp rbx, 26
	jb 22f
	sub rcx, 260
	sub r9, 26
	jmp 23f
22:
	add rcx, 5
23:
	cmp rbx, 25
	je 24f
	movzx eax, BYTE PTR [rdi+rcx*1+772]
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+771]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+770]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+769]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+768]
	add rax, rdx
	jmp 25f
24:
	movzx eax, BYTE PTR [rdi+rcx*1+768]
25:
	sub rbx, 26
	sub rax, 16
	sbb rdx, rdx
	mov QWORD PTR [rdi+1152], rdx
	xor rax, rdx
	sub rax, rdx
	mov r10, rax
	mov QWORD PTR [rdi+6568], rdx
	mov rcx, rbx
	add rcx, rcx
	mov r9, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, r9
	mov r9, rbx
	cmp rbx, 26
	jb 26f
	sub rcx, 260
	sub r9, 26
	jmp 27f
26:
	add rcx, 5
27:
	cmp rbx, 25
	je 28f
	movzx eax, BYTE PTR [rdi+rcx*1+772]
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+771]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+770]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+769]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+768]
	add rax, rdx
	jmp 29f
28:
	movzx eax, BYTE PTR [rdi+rcx*1+768]
29:
	sub rax, 16
	sbb rdx, rdx
	mov QWORD PTR [rdi+1152], rdx
	xor rax, rdx
	sub rax, rdx
	mov r8, rax
	mov QWORD PTR [rdi+6560], rdx
	mov rdx, r9
	mov rax, rdx
	mov ecx, 1536
	mul rcx
	lea rdx, {VG_ED25519_COMB}
	add rdx, rax
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	mov ecx, 1
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	vmovq xmm15, rcx
	vpbroadcastq zmm15, xmm15
	mov ecx, 1
	xor rcx, r10
	cmp rcx, 1
	sbb rcx, rcx
	vmovq xmm14, rcx
	vpbroadcastq zmm14, xmm14
	vshufi32x4 zmm15, zmm15, zmm14, 68
	vmovdqu ymm10, YMMWORD PTR [rdx]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm11, zmm11, zmm10
	vmovdqu ymm10, YMMWORD PTR [rdx+32]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm12, zmm12, zmm10
	vmovdqu ymm10, YMMWORD PTR [rdx+64]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm13, zmm13, zmm10
	mov ecx, 2
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	vmovq xmm15, rcx
	vpbroadcastq zmm15, xmm15
	mov ecx, 2
	xor rcx, r10
	cmp rcx, 1
	sbb rcx, rcx
	vmovq xmm14, rcx
	vpbroadcastq zmm14, xmm14
	vshufi32x4 zmm15, zmm15, zmm14, 68
	vmovdqu ymm10, YMMWORD PTR [rdx+96]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm11, zmm11, zmm10
	vmovdqu ymm10, YMMWORD PTR [rdx+128]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm12, zmm12, zmm10
	vmovdqu ymm10, YMMWORD PTR [rdx+160]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm13, zmm13, zmm10
	mov ecx, 3
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	vmovq xmm15, rcx
	vpbroadcastq zmm15, xmm15
	mov ecx, 3
	xor rcx, r10
	cmp rcx, 1
	sbb rcx, rcx
	vmovq xmm14, rcx
	vpbroadcastq zmm14, xmm14
	vshufi32x4 zmm15, zmm15, zmm14, 68
	vmovdqu ymm10, YMMWORD PTR [rdx+192]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm11, zmm11, zmm10
	vmovdqu ymm10, YMMWORD PTR [rdx+224]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm12, zmm12, zmm10
	vmovdqu ymm10, YMMWORD PTR [rdx+256]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm13, zmm13, zmm10
	mov ecx, 4
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	vmovq xmm15, rcx
	vpbroadcastq zmm15, xmm15
	mov ecx, 4
	xor rcx, r10
	cmp rcx, 1
	sbb rcx, rcx
	vmovq xmm14, rcx
	vpbroadcastq zmm14, xmm14
	vshufi32x4 zmm15, zmm15, zmm14, 68
	vmovdqu ymm10, YMMWORD PTR [rdx+288]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm11, zmm11, zmm10
	vmovdqu ymm10, YMMWORD PTR [rdx+320]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm12, zmm12, zmm10
	vmovdqu ymm10, YMMWORD PTR [rdx+352]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm13, zmm13, zmm10
	mov ecx, 5
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	vmovq xmm15, rcx
	vpbroadcastq zmm15, xmm15
	mov ecx, 5
	xor rcx, r10
	cmp rcx, 1
	sbb rcx, rcx
	vmovq xmm14, rcx
	vpbroadcastq zmm14, xmm14
	vshufi32x4 zmm15, zmm15, zmm14, 68
	vmovdqu ymm10, YMMWORD PTR [rdx+384]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm11, zmm11, zmm10
	vmovdqu ymm10, YMMWORD PTR [rdx+416]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm12, zmm12, zmm10
	vmovdqu ymm10, YMMWORD PTR [rdx+448]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm13, zmm13, zmm10
	mov ecx, 6
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	vmovq xmm15, rcx
	vpbroadcastq zmm15, xmm15
	mov ecx, 6
	xor rcx, r10
	cmp rcx, 1
	sbb rcx, rcx
	vmovq xmm14, rcx
	vpbroadcastq zmm14, xmm14
	vshufi32x4 zmm15, zmm15, zmm14, 68
	vmovdqu ymm10, YMMWORD PTR [rdx+480]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm11, zmm11, zmm10
	vmovdqu ymm10, YMMWORD PTR [rdx+512]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm12, zmm12, zmm10
	vmovdqu ymm10, YMMWORD PTR [rdx+544]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm13, zmm13, zmm10
	mov ecx, 7
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	vmovq xmm15, rcx
	vpbroadcastq zmm15, xmm15
	mov ecx, 7
	xor rcx, r10
	cmp rcx, 1
	sbb rcx, rcx
	vmovq xmm14, rcx
	vpbroadcastq zmm14, xmm14
	vshufi32x4 zmm15, zmm15, zmm14, 68
	vmovdqu ymm10, YMMWORD PTR [rdx+576]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm11, zmm11, zmm10
	vmovdqu ymm10, YMMWORD PTR [rdx+608]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm12, zmm12, zmm10
	vmovdqu ymm10, YMMWORD PTR [rdx+640]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm13, zmm13, zmm10
	mov ecx, 8
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	vmovq xmm15, rcx
	vpbroadcastq zmm15, xmm15
	mov ecx, 8
	xor rcx, r10
	cmp rcx, 1
	sbb rcx, rcx
	vmovq xmm14, rcx
	vpbroadcastq zmm14, xmm14
	vshufi32x4 zmm15, zmm15, zmm14, 68
	vmovdqu ymm10, YMMWORD PTR [rdx+672]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm11, zmm11, zmm10
	vmovdqu ymm10, YMMWORD PTR [rdx+704]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm12, zmm12, zmm10
	vmovdqu ymm10, YMMWORD PTR [rdx+736]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm13, zmm13, zmm10
	mov ecx, 9
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	vmovq xmm15, rcx
	vpbroadcastq zmm15, xmm15
	mov ecx, 9
	xor rcx, r10
	cmp rcx, 1
	sbb rcx, rcx
	vmovq xmm14, rcx
	vpbroadcastq zmm14, xmm14
	vshufi32x4 zmm15, zmm15, zmm14, 68
	vmovdqu ymm10, YMMWORD PTR [rdx+768]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm11, zmm11, zmm10
	vmovdqu ymm10, YMMWORD PTR [rdx+800]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm12, zmm12, zmm10
	vmovdqu ymm10, YMMWORD PTR [rdx+832]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm13, zmm13, zmm10
	mov ecx, 10
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	vmovq xmm15, rcx
	vpbroadcastq zmm15, xmm15
	mov ecx, 10
	xor rcx, r10
	cmp rcx, 1
	sbb rcx, rcx
	vmovq xmm14, rcx
	vpbroadcastq zmm14, xmm14
	vshufi32x4 zmm15, zmm15, zmm14, 68
	vmovdqu ymm10, YMMWORD PTR [rdx+864]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm11, zmm11, zmm10
	vmovdqu ymm10, YMMWORD PTR [rdx+896]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm12, zmm12, zmm10
	vmovdqu ymm10, YMMWORD PTR [rdx+928]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm13, zmm13, zmm10
	mov ecx, 11
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	vmovq xmm15, rcx
	vpbroadcastq zmm15, xmm15
	mov ecx, 11
	xor rcx, r10
	cmp rcx, 1
	sbb rcx, rcx
	vmovq xmm14, rcx
	vpbroadcastq zmm14, xmm14
	vshufi32x4 zmm15, zmm15, zmm14, 68
	vmovdqu ymm10, YMMWORD PTR [rdx+960]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm11, zmm11, zmm10
	vmovdqu ymm10, YMMWORD PTR [rdx+992]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm12, zmm12, zmm10
	vmovdqu ymm10, YMMWORD PTR [rdx+1024]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm13, zmm13, zmm10
	mov ecx, 12
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	vmovq xmm15, rcx
	vpbroadcastq zmm15, xmm15
	mov ecx, 12
	xor rcx, r10
	cmp rcx, 1
	sbb rcx, rcx
	vmovq xmm14, rcx
	vpbroadcastq zmm14, xmm14
	vshufi32x4 zmm15, zmm15, zmm14, 68
	vmovdqu ymm10, YMMWORD PTR [rdx+1056]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm11, zmm11, zmm10
	vmovdqu ymm10, YMMWORD PTR [rdx+1088]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm12, zmm12, zmm10
	vmovdqu ymm10, YMMWORD PTR [rdx+1120]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm13, zmm13, zmm10
	mov ecx, 13
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	vmovq xmm15, rcx
	vpbroadcastq zmm15, xmm15
	mov ecx, 13
	xor rcx, r10
	cmp rcx, 1
	sbb rcx, rcx
	vmovq xmm14, rcx
	vpbroadcastq zmm14, xmm14
	vshufi32x4 zmm15, zmm15, zmm14, 68
	vmovdqu ymm10, YMMWORD PTR [rdx+1152]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm11, zmm11, zmm10
	vmovdqu ymm10, YMMWORD PTR [rdx+1184]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm12, zmm12, zmm10
	vmovdqu ymm10, YMMWORD PTR [rdx+1216]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm13, zmm13, zmm10
	mov ecx, 14
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	vmovq xmm15, rcx
	vpbroadcastq zmm15, xmm15
	mov ecx, 14
	xor rcx, r10
	cmp rcx, 1
	sbb rcx, rcx
	vmovq xmm14, rcx
	vpbroadcastq zmm14, xmm14
	vshufi32x4 zmm15, zmm15, zmm14, 68
	vmovdqu ymm10, YMMWORD PTR [rdx+1248]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm11, zmm11, zmm10
	vmovdqu ymm10, YMMWORD PTR [rdx+1280]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm12, zmm12, zmm10
	vmovdqu ymm10, YMMWORD PTR [rdx+1312]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm13, zmm13, zmm10
	mov ecx, 15
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	vmovq xmm15, rcx
	vpbroadcastq zmm15, xmm15
	mov ecx, 15
	xor rcx, r10
	cmp rcx, 1
	sbb rcx, rcx
	vmovq xmm14, rcx
	vpbroadcastq zmm14, xmm14
	vshufi32x4 zmm15, zmm15, zmm14, 68
	vmovdqu ymm10, YMMWORD PTR [rdx+1344]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm11, zmm11, zmm10
	vmovdqu ymm10, YMMWORD PTR [rdx+1376]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm12, zmm12, zmm10
	vmovdqu ymm10, YMMWORD PTR [rdx+1408]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm13, zmm13, zmm10
	mov ecx, 16
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	vmovq xmm15, rcx
	vpbroadcastq zmm15, xmm15
	mov ecx, 16
	xor rcx, r10
	cmp rcx, 1
	sbb rcx, rcx
	vmovq xmm14, rcx
	vpbroadcastq zmm14, xmm14
	vshufi32x4 zmm15, zmm15, zmm14, 68
	vmovdqu ymm10, YMMWORD PTR [rdx+1440]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm11, zmm11, zmm10
	vmovdqu ymm10, YMMWORD PTR [rdx+1472]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm12, zmm12, zmm10
	vmovdqu ymm10, YMMWORD PTR [rdx+1504]
	vshufi32x4 zmm10, zmm10, zmm10, 68
	vpandq zmm10, zmm10, zmm15
	vporq zmm13, zmm13, zmm10
	mov rax, r8
	cmp rax, 1
	sbb rax, rax
	and rax, 1
	vmovq xmm10, rax
	mov rax, r10
	cmp rax, 1
	sbb rax, rax
	and rax, 1
	vmovq xmm9, rax
	vshufi32x4 zmm10, zmm10, zmm9, 68
	vporq zmm11, zmm11, zmm10
	vporq zmm12, zmm12, zmm10
	vmovdqu32 zmm14, ZMMWORD PTR [rdi+6016]
	vpunpcklqdq zmm5, zmm11, zmm12
	vpunpckhqdq zmm6, zmm11, zmm12
	vpunpcklqdq zmm7, zmm13, zmm14
	vpunpckhqdq zmm8, zmm13, zmm14
	vshufi32x4 zmm11, zmm5, zmm7, 136
	vshufi32x4 zmm11, zmm11, zmm11, 216
	vshufi32x4 zmm12, zmm6, zmm8, 136
	vshufi32x4 zmm12, zmm12, zmm12, 216
	vshufi32x4 zmm13, zmm5, zmm7, 221
	vshufi32x4 zmm13, zmm13, zmm13, 216
	vshufi32x4 zmm14, zmm6, zmm8, 221
	vshufi32x4 zmm14, zmm14, zmm14, 216
	vmovdqu32 zmm15, ZMMWORD PTR [rdi+5504]
	vpandq zmm5, zmm11, zmm15
	vpsrlq zmm6, zmm11, 51
	vpsrlq zmm10, zmm15, 13
	vpandq zmm10, zmm12, zmm10
	vpsllq zmm10, zmm10, 13
	vporq zmm6, zmm6, zmm10
	vpsrlq zmm7, zmm12, 38
	vpsrlq zmm10, zmm15, 26
	vpandq zmm10, zmm13, zmm10
	vpsllq zmm10, zmm10, 26
	vporq zmm7, zmm7, zmm10
	vpsrlq zmm8, zmm13, 25
	vpsrlq zmm10, zmm15, 39
	vpandq zmm10, zmm14, zmm10
	vpsllq zmm10, zmm10, 39
	vporq zmm8, zmm8, zmm10
	vpsrlq zmm9, zmm14, 12
	mov rcx, QWORD PTR [rdi+6560]
	vmovq xmm14, rcx
	vpbroadcastq zmm14, xmm14
	mov rcx, QWORD PTR [rdi+6568]
	vmovq xmm15, rcx
	vpbroadcastq zmm15, xmm15
	vshufi32x4 zmm15, zmm14, zmm15, 68
	vpermq zmm10, zmm5, 225
	vmovdqu32 zmm11, ZMMWORD PTR [rdi+5632]
	vpsubq zmm11, zmm11, zmm5
	vmovdqu32 zmm12, ZMMWORD PTR [rdi+5952]
	vpternlogd zmm12, zmm10, zmm11, 172
	vmovdqa64 zmm10, zmm12
	vpxord zmm10, zmm10, zmm5
	vpandq zmm10, zmm10, zmm15
	vpxord zmm5, zmm5, zmm10
	vpermq zmm10, zmm6, 225
	vmovdqu32 zmm11, ZMMWORD PTR [rdi+5696]
	vpsubq zmm11, zmm11, zmm6
	vmovdqu32 zmm12, ZMMWORD PTR [rdi+5952]
	vpternlogd zmm12, zmm10, zmm11, 172
	vmovdqa64 zmm10, zmm12
	vpxord zmm10, zmm10, zmm6
	vpandq zmm10, zmm10, zmm15
	vpxord zmm6, zmm6, zmm10
	vpermq zmm10, zmm7, 225
	vmovdqu32 zmm11, ZMMWORD PTR [rdi+5696]
	vpsubq zmm11, zmm11, zmm7
	vmovdqu32 zmm12, ZMMWORD PTR [rdi+5952]
	vpternlogd zmm12, zmm10, zmm11, 172
	vmovdqa64 zmm10, zmm12
	vpxord zmm10, zmm10, zmm7
	vpandq zmm10, zmm10, zmm15
	vpxord zmm7, zmm7, zmm10
	vpermq zmm10, zmm8, 225
	vmovdqu32 zmm11, ZMMWORD PTR [rdi+5696]
	vpsubq zmm11, zmm11, zmm8
	vmovdqu32 zmm12, ZMMWORD PTR [rdi+5952]
	vpternlogd zmm12, zmm10, zmm11, 172
	vmovdqa64 zmm10, zmm12
	vpxord zmm10, zmm10, zmm8
	vpandq zmm10, zmm10, zmm15
	vpxord zmm8, zmm8, zmm10
	vpermq zmm10, zmm9, 225
	vmovdqu32 zmm11, ZMMWORD PTR [rdi+5696]
	vpsubq zmm11, zmm11, zmm9
	vmovdqu32 zmm12, ZMMWORD PTR [rdi+5952]
	vpternlogd zmm12, zmm10, zmm11, 172
	vmovdqa64 zmm10, zmm12
	vpxord zmm10, zmm10, zmm9
	vpandq zmm10, zmm10, zmm15
	vpxord zmm9, zmm9, zmm10
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+5504]
	vpsrlq zmm11, zmm9, 51
	vpandq zmm9, zmm9, zmm10
	vpsrlq zmm12, zmm8, 51
	vpandq zmm8, zmm8, zmm10
	vpaddq zmm9, zmm9, zmm12
	vpsrlq zmm12, zmm7, 51
	vpandq zmm7, zmm7, zmm10
	vpaddq zmm8, zmm8, zmm12
	vpsrlq zmm12, zmm6, 51
	vpandq zmm6, zmm6, zmm10
	vpaddq zmm7, zmm7, zmm12
	vpsrlq zmm12, zmm5, 51
	vpandq zmm5, zmm5, zmm10
	vpaddq zmm6, zmm6, zmm12
	vmovdqu32 zmm12, ZMMWORD PTR [rdi+5568]
	vpmadd52luq zmm5, zmm11, zmm12
	vpxord zmm13, zmm13, zmm13
	vpermq zmm10, zmm0, 181
	vpermq zmm11, zmm0, 0
	vmovdqu32 zmm12, ZMMWORD PTR [rdi+5632]
	vpsubq zmm12, zmm12, zmm11
	vmovdqu32 zmm15, ZMMWORD PTR [rdi+5760]
	vpternlogd zmm15, zmm11, zmm12, 172
	vmovdqa64 zmm11, zmm15
	vmovdqu32 zmm15, ZMMWORD PTR [rdi+5824]
	vpternlogd zmm15, zmm11, zmm13, 172
	vmovdqa64 zmm11, zmm15
	vpaddq zmm0, zmm10, zmm11
	vpermq zmm10, zmm1, 181
	vpermq zmm11, zmm1, 0
	vmovdqu32 zmm12, ZMMWORD PTR [rdi+5696]
	vpsubq zmm12, zmm12, zmm11
	vmovdqu32 zmm15, ZMMWORD PTR [rdi+5760]
	vpternlogd zmm15, zmm11, zmm12, 172
	vmovdqa64 zmm11, zmm15
	vmovdqu32 zmm15, ZMMWORD PTR [rdi+5824]
	vpternlogd zmm15, zmm11, zmm13, 172
	vmovdqa64 zmm11, zmm15
	vpaddq zmm1, zmm10, zmm11
	vpermq zmm10, zmm2, 181
	vpermq zmm11, zmm2, 0
	vmovdqu32 zmm12, ZMMWORD PTR [rdi+5696]
	vpsubq zmm12, zmm12, zmm11
	vmovdqu32 zmm15, ZMMWORD PTR [rdi+5760]
	vpternlogd zmm15, zmm11, zmm12, 172
	vmovdqa64 zmm11, zmm15
	vmovdqu32 zmm15, ZMMWORD PTR [rdi+5824]
	vpternlogd zmm15, zmm11, zmm13, 172
	vmovdqa64 zmm11, zmm15
	vpaddq zmm2, zmm10, zmm11
	vpermq zmm10, zmm3, 181
	vpermq zmm11, zmm3, 0
	vmovdqu32 zmm12, ZMMWORD PTR [rdi+5696]
	vpsubq zmm12, zmm12, zmm11
	vmovdqu32 zmm15, ZMMWORD PTR [rdi+5760]
	vpternlogd zmm15, zmm11, zmm12, 172
	vmovdqa64 zmm11, zmm15
	vmovdqu32 zmm15, ZMMWORD PTR [rdi+5824]
	vpternlogd zmm15, zmm11, zmm13, 172
	vmovdqa64 zmm11, zmm15
	vpaddq zmm3, zmm10, zmm11
	vpermq zmm10, zmm4, 181
	vpermq zmm11, zmm4, 0
	vmovdqu32 zmm12, ZMMWORD PTR [rdi+5696]
	vpsubq zmm12, zmm12, zmm11
	vmovdqu32 zmm15, ZMMWORD PTR [rdi+5760]
	vpternlogd zmm15, zmm11, zmm12, 172
	vmovdqa64 zmm11, zmm15
	vmovdqu32 zmm15, ZMMWORD PTR [rdi+5824]
	vpternlogd zmm15, zmm11, zmm13, 172
	vmovdqa64 zmm11, zmm15
	vpaddq zmm4, zmm10, zmm11
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+5504]
	vpsrlq zmm11, zmm4, 51
	vpandq zmm4, zmm4, zmm10
	vpsrlq zmm12, zmm3, 51
	vpandq zmm3, zmm3, zmm10
	vpaddq zmm4, zmm4, zmm12
	vpsrlq zmm12, zmm2, 51
	vpandq zmm2, zmm2, zmm10
	vpaddq zmm3, zmm3, zmm12
	vpsrlq zmm12, zmm1, 51
	vpandq zmm1, zmm1, zmm10
	vpaddq zmm2, zmm2, zmm12
	vpsrlq zmm12, zmm0, 51
	vpandq zmm0, zmm0, zmm10
	vpaddq zmm1, zmm1, zmm12
	vmovdqu32 zmm12, ZMMWORD PTR [rdi+5568]
	vpmadd52luq zmm0, zmm11, zmm12
	vmovdqu32 ZMMWORD PTR [rdi+4224], zmm0
	vmovdqu32 ZMMWORD PTR [rdi+4288], zmm1
	vmovdqu32 ZMMWORD PTR [rdi+4352], zmm2
	vmovdqu32 ZMMWORD PTR [rdi+4416], zmm3
	vmovdqu32 ZMMWORD PTR [rdi+4480], zmm4
	vpxord zmm11, zmm11, zmm11
	vpxord zmm12, zmm12, zmm12
	vpxord zmm13, zmm13, zmm13
	vpxord zmm14, zmm14, zmm14
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4224]
	vpmadd52luq zmm11, zmm10, zmm5
	vpmadd52huq zmm14, zmm10, zmm9
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4288]
	vpmadd52luq zmm13, zmm10, zmm9
	vpmadd52huq zmm14, zmm10, zmm8
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4352]
	vpmadd52luq zmm13, zmm10, zmm8
	vpmadd52huq zmm14, zmm10, zmm7
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4416]
	vpmadd52luq zmm13, zmm10, zmm7
	vpmadd52huq zmm14, zmm10, zmm6
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4480]
	vpmadd52luq zmm13, zmm10, zmm6
	vpmadd52huq zmm14, zmm10, zmm5
	vpsllq zmm12, zmm12, 1
	vpaddq zmm11, zmm11, zmm12
	vpsllq zmm14, zmm14, 1
	vpaddq zmm13, zmm13, zmm14
	vpaddq zmm11, zmm11, zmm13
	vpsllq zmm12, zmm13, 1
	vpaddq zmm11, zmm11, zmm12
	vpsllq zmm12, zmm13, 4
	vpaddq zmm0, zmm11, zmm12
	vpxord zmm11, zmm11, zmm11
	vpxord zmm12, zmm12, zmm12
	vpxord zmm13, zmm13, zmm13
	vpxord zmm14, zmm14, zmm14
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4224]
	vpmadd52luq zmm11, zmm10, zmm6
	vpmadd52huq zmm12, zmm10, zmm5
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4288]
	vpmadd52luq zmm11, zmm10, zmm5
	vpmadd52huq zmm14, zmm10, zmm9
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4352]
	vpmadd52luq zmm13, zmm10, zmm9
	vpmadd52huq zmm14, zmm10, zmm8
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4416]
	vpmadd52luq zmm13, zmm10, zmm8
	vpmadd52huq zmm14, zmm10, zmm7
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4480]
	vpmadd52luq zmm13, zmm10, zmm7
	vpmadd52huq zmm14, zmm10, zmm6
	vpsllq zmm12, zmm12, 1
	vpaddq zmm11, zmm11, zmm12
	vpsllq zmm14, zmm14, 1
	vpaddq zmm13, zmm13, zmm14
	vpaddq zmm11, zmm11, zmm13
	vpsllq zmm12, zmm13, 1
	vpaddq zmm11, zmm11, zmm12
	vpsllq zmm12, zmm13, 4
	vpaddq zmm1, zmm11, zmm12
	vpxord zmm11, zmm11, zmm11
	vpxord zmm12, zmm12, zmm12
	vpxord zmm13, zmm13, zmm13
	vpxord zmm14, zmm14, zmm14
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4224]
	vpmadd52luq zmm11, zmm10, zmm7
	vpmadd52huq zmm12, zmm10, zmm6
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4288]
	vpmadd52luq zmm11, zmm10, zmm6
	vpmadd52huq zmm12, zmm10, zmm5
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4352]
	vpmadd52luq zmm11, zmm10, zmm5
	vpmadd52huq zmm14, zmm10, zmm9
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4416]
	vpmadd52luq zmm13, zmm10, zmm9
	vpmadd52huq zmm14, zmm10, zmm8
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4480]
	vpmadd52luq zmm13, zmm10, zmm8
	vpmadd52huq zmm14, zmm10, zmm7
	vpsllq zmm12, zmm12, 1
	vpaddq zmm11, zmm11, zmm12
	vpsllq zmm14, zmm14, 1
	vpaddq zmm13, zmm13, zmm14
	vpaddq zmm11, zmm11, zmm13
	vpsllq zmm12, zmm13, 1
	vpaddq zmm11, zmm11, zmm12
	vpsllq zmm12, zmm13, 4
	vpaddq zmm2, zmm11, zmm12
	vpxord zmm11, zmm11, zmm11
	vpxord zmm12, zmm12, zmm12
	vpxord zmm13, zmm13, zmm13
	vpxord zmm14, zmm14, zmm14
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4224]
	vpmadd52luq zmm11, zmm10, zmm8
	vpmadd52huq zmm12, zmm10, zmm7
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4288]
	vpmadd52luq zmm11, zmm10, zmm7
	vpmadd52huq zmm12, zmm10, zmm6
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4352]
	vpmadd52luq zmm11, zmm10, zmm6
	vpmadd52huq zmm12, zmm10, zmm5
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4416]
	vpmadd52luq zmm11, zmm10, zmm5
	vpmadd52huq zmm14, zmm10, zmm9
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4480]
	vpmadd52luq zmm13, zmm10, zmm9
	vpmadd52huq zmm14, zmm10, zmm8
	vpsllq zmm12, zmm12, 1
	vpaddq zmm11, zmm11, zmm12
	vpsllq zmm14, zmm14, 1
	vpaddq zmm13, zmm13, zmm14
	vpaddq zmm11, zmm11, zmm13
	vpsllq zmm12, zmm13, 1
	vpaddq zmm11, zmm11, zmm12
	vpsllq zmm12, zmm13, 4
	vpaddq zmm3, zmm11, zmm12
	vpxord zmm11, zmm11, zmm11
	vpxord zmm12, zmm12, zmm12
	vpxord zmm13, zmm13, zmm13
	vpxord zmm14, zmm14, zmm14
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4224]
	vpmadd52luq zmm11, zmm10, zmm9
	vpmadd52huq zmm12, zmm10, zmm8
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4288]
	vpmadd52luq zmm11, zmm10, zmm8
	vpmadd52huq zmm12, zmm10, zmm7
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4352]
	vpmadd52luq zmm11, zmm10, zmm7
	vpmadd52huq zmm12, zmm10, zmm6
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4416]
	vpmadd52luq zmm11, zmm10, zmm6
	vpmadd52huq zmm12, zmm10, zmm5
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4480]
	vpmadd52luq zmm11, zmm10, zmm5
	vpmadd52huq zmm14, zmm10, zmm9
	vpsllq zmm12, zmm12, 1
	vpaddq zmm11, zmm11, zmm12
	vpsllq zmm14, zmm14, 1
	vpaddq zmm13, zmm13, zmm14
	vpaddq zmm11, zmm11, zmm13
	vpsllq zmm12, zmm13, 1
	vpaddq zmm11, zmm11, zmm12
	vpsllq zmm12, zmm13, 4
	vpaddq zmm4, zmm11, zmm12
	vpermq zmm10, zmm0, 125
	vpermq zmm11, zmm0, 40
	vmovdqu32 zmm12, ZMMWORD PTR [rdi+5632]
	vpsubq zmm12, zmm12, zmm11
	vmovdqu32 zmm15, ZMMWORD PTR [rdi+5888]
	vpternlogd zmm15, zmm11, zmm12, 172
	vmovdqa64 zmm11, zmm15
	vpaddq zmm10, zmm10, zmm11
	vpermq zmm0, zmm10, 36
	vpermq zmm5, zmm10, 222
	vpermq zmm10, zmm1, 125
	vpermq zmm11, zmm1, 40
	vmovdqu32 zmm12, ZMMWORD PTR [rdi+5696]
	vpsubq zmm12, zmm12, zmm11
	vmovdqu32 zmm15, ZMMWORD PTR [rdi+5888]
	vpternlogd zmm15, zmm11, zmm12, 172
	vmovdqa64 zmm11, zmm15
	vpaddq zmm10, zmm10, zmm11
	vpermq zmm1, zmm10, 36
	vpermq zmm6, zmm10, 222
	vpermq zmm10, zmm2, 125
	vpermq zmm11, zmm2, 40
	vmovdqu32 zmm12, ZMMWORD PTR [rdi+5696]
	vpsubq zmm12, zmm12, zmm11
	vmovdqu32 zmm15, ZMMWORD PTR [rdi+5888]
	vpternlogd zmm15, zmm11, zmm12, 172
	vmovdqa64 zmm11, zmm15
	vpaddq zmm10, zmm10, zmm11
	vpermq zmm2, zmm10, 36
	vpermq zmm7, zmm10, 222
	vpermq zmm10, zmm3, 125
	vpermq zmm11, zmm3, 40
	vmovdqu32 zmm12, ZMMWORD PTR [rdi+5696]
	vpsubq zmm12, zmm12, zmm11
	vmovdqu32 zmm15, ZMMWORD PTR [rdi+5888]
	vpternlogd zmm15, zmm11, zmm12, 172
	vmovdqa64 zmm11, zmm15
	vpaddq zmm10, zmm10, zmm11
	vpermq zmm3, zmm10, 36
	vpermq zmm8, zmm10, 222
	vpermq zmm10, zmm4, 125
	vpermq zmm11, zmm4, 40
	vmovdqu32 zmm12, ZMMWORD PTR [rdi+5696]
	vpsubq zmm12, zmm12, zmm11
	vmovdqu32 zmm15, ZMMWORD PTR [rdi+5888]
	vpternlogd zmm15, zmm11, zmm12, 172
	vmovdqa64 zmm11, zmm15
	vpaddq zmm10, zmm10, zmm11
	vpermq zmm4, zmm10, 36
	vpermq zmm9, zmm10, 222
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+5504]
	vpsrlq zmm11, zmm9, 51
	vpandq zmm9, zmm9, zmm10
	vpsrlq zmm12, zmm8, 51
	vpandq zmm8, zmm8, zmm10
	vpaddq zmm9, zmm9, zmm12
	vpsrlq zmm12, zmm7, 51
	vpandq zmm7, zmm7, zmm10
	vpaddq zmm8, zmm8, zmm12
	vpsrlq zmm12, zmm6, 51
	vpandq zmm6, zmm6, zmm10
	vpaddq zmm7, zmm7, zmm12
	vpsrlq zmm12, zmm5, 51
	vpandq zmm5, zmm5, zmm10
	vpaddq zmm6, zmm6, zmm12
	vmovdqu32 zmm12, ZMMWORD PTR [rdi+5568]
	vpmadd52luq zmm5, zmm11, zmm12
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+5504]
	vpsrlq zmm11, zmm4, 51
	vpandq zmm4, zmm4, zmm10
	vpsrlq zmm12, zmm3, 51
	vpandq zmm3, zmm3, zmm10
	vpaddq zmm4, zmm4, zmm12
	vpsrlq zmm12, zmm2, 51
	vpandq zmm2, zmm2, zmm10
	vpaddq zmm3, zmm3, zmm12
	vpsrlq zmm12, zmm1, 51
	vpandq zmm1, zmm1, zmm10
	vpaddq zmm2, zmm2, zmm12
	vpsrlq zmm12, zmm0, 51
	vpandq zmm0, zmm0, zmm10
	vpaddq zmm1, zmm1, zmm12
	vmovdqu32 zmm12, ZMMWORD PTR [rdi+5568]
	vpmadd52luq zmm0, zmm11, zmm12
	vmovdqu32 ZMMWORD PTR [rdi+4544], zmm0
	vmovdqu32 ZMMWORD PTR [rdi+4608], zmm1
	vmovdqu32 ZMMWORD PTR [rdi+4672], zmm2
	vmovdqu32 ZMMWORD PTR [rdi+4736], zmm3
	vmovdqu32 ZMMWORD PTR [rdi+4800], zmm4
	vpxord zmm11, zmm11, zmm11
	vpxord zmm12, zmm12, zmm12
	vpxord zmm13, zmm13, zmm13
	vpxord zmm14, zmm14, zmm14
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4544]
	vpmadd52luq zmm11, zmm10, zmm5
	vpmadd52huq zmm14, zmm10, zmm9
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4608]
	vpmadd52luq zmm13, zmm10, zmm9
	vpmadd52huq zmm14, zmm10, zmm8
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4672]
	vpmadd52luq zmm13, zmm10, zmm8
	vpmadd52huq zmm14, zmm10, zmm7
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4736]
	vpmadd52luq zmm13, zmm10, zmm7
	vpmadd52huq zmm14, zmm10, zmm6
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4800]
	vpmadd52luq zmm13, zmm10, zmm6
	vpmadd52huq zmm14, zmm10, zmm5
	vpsllq zmm12, zmm12, 1
	vpaddq zmm11, zmm11, zmm12
	vpsllq zmm14, zmm14, 1
	vpaddq zmm13, zmm13, zmm14
	vpaddq zmm11, zmm11, zmm13
	vpsllq zmm12, zmm13, 1
	vpaddq zmm11, zmm11, zmm12
	vpsllq zmm12, zmm13, 4
	vpaddq zmm0, zmm11, zmm12
	vpxord zmm11, zmm11, zmm11
	vpxord zmm12, zmm12, zmm12
	vpxord zmm13, zmm13, zmm13
	vpxord zmm14, zmm14, zmm14
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4544]
	vpmadd52luq zmm11, zmm10, zmm6
	vpmadd52huq zmm12, zmm10, zmm5
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4608]
	vpmadd52luq zmm11, zmm10, zmm5
	vpmadd52huq zmm14, zmm10, zmm9
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4672]
	vpmadd52luq zmm13, zmm10, zmm9
	vpmadd52huq zmm14, zmm10, zmm8
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4736]
	vpmadd52luq zmm13, zmm10, zmm8
	vpmadd52huq zmm14, zmm10, zmm7
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4800]
	vpmadd52luq zmm13, zmm10, zmm7
	vpmadd52huq zmm14, zmm10, zmm6
	vpsllq zmm12, zmm12, 1
	vpaddq zmm11, zmm11, zmm12
	vpsllq zmm14, zmm14, 1
	vpaddq zmm13, zmm13, zmm14
	vpaddq zmm11, zmm11, zmm13
	vpsllq zmm12, zmm13, 1
	vpaddq zmm11, zmm11, zmm12
	vpsllq zmm12, zmm13, 4
	vpaddq zmm1, zmm11, zmm12
	vpxord zmm11, zmm11, zmm11
	vpxord zmm12, zmm12, zmm12
	vpxord zmm13, zmm13, zmm13
	vpxord zmm14, zmm14, zmm14
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4544]
	vpmadd52luq zmm11, zmm10, zmm7
	vpmadd52huq zmm12, zmm10, zmm6
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4608]
	vpmadd52luq zmm11, zmm10, zmm6
	vpmadd52huq zmm12, zmm10, zmm5
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4672]
	vpmadd52luq zmm11, zmm10, zmm5
	vpmadd52huq zmm14, zmm10, zmm9
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4736]
	vpmadd52luq zmm13, zmm10, zmm9
	vpmadd52huq zmm14, zmm10, zmm8
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4800]
	vpmadd52luq zmm13, zmm10, zmm8
	vpmadd52huq zmm14, zmm10, zmm7
	vpsllq zmm12, zmm12, 1
	vpaddq zmm11, zmm11, zmm12
	vpsllq zmm14, zmm14, 1
	vpaddq zmm13, zmm13, zmm14
	vpaddq zmm11, zmm11, zmm13
	vpsllq zmm12, zmm13, 1
	vpaddq zmm11, zmm11, zmm12
	vpsllq zmm12, zmm13, 4
	vpaddq zmm2, zmm11, zmm12
	vpxord zmm11, zmm11, zmm11
	vpxord zmm12, zmm12, zmm12
	vpxord zmm13, zmm13, zmm13
	vpxord zmm14, zmm14, zmm14
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4544]
	vpmadd52luq zmm11, zmm10, zmm8
	vpmadd52huq zmm12, zmm10, zmm7
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4608]
	vpmadd52luq zmm11, zmm10, zmm7
	vpmadd52huq zmm12, zmm10, zmm6
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4672]
	vpmadd52luq zmm11, zmm10, zmm6
	vpmadd52huq zmm12, zmm10, zmm5
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4736]
	vpmadd52luq zmm11, zmm10, zmm5
	vpmadd52huq zmm14, zmm10, zmm9
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4800]
	vpmadd52luq zmm13, zmm10, zmm9
	vpmadd52huq zmm14, zmm10, zmm8
	vpsllq zmm12, zmm12, 1
	vpaddq zmm11, zmm11, zmm12
	vpsllq zmm14, zmm14, 1
	vpaddq zmm13, zmm13, zmm14
	vpaddq zmm11, zmm11, zmm13
	vpsllq zmm12, zmm13, 1
	vpaddq zmm11, zmm11, zmm12
	vpsllq zmm12, zmm13, 4
	vpaddq zmm3, zmm11, zmm12
	vpxord zmm11, zmm11, zmm11
	vpxord zmm12, zmm12, zmm12
	vpxord zmm13, zmm13, zmm13
	vpxord zmm14, zmm14, zmm14
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4544]
	vpmadd52luq zmm11, zmm10, zmm9
	vpmadd52huq zmm12, zmm10, zmm8
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4608]
	vpmadd52luq zmm11, zmm10, zmm8
	vpmadd52huq zmm12, zmm10, zmm7
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4672]
	vpmadd52luq zmm11, zmm10, zmm7
	vpmadd52huq zmm12, zmm10, zmm6
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4736]
	vpmadd52luq zmm11, zmm10, zmm6
	vpmadd52huq zmm12, zmm10, zmm5
	vmovdqu32 zmm10, ZMMWORD PTR [rdi+4800]
	vpmadd52luq zmm11, zmm10, zmm5
	vpmadd52huq zmm14, zmm10, zmm9
	vpsllq zmm12, zmm12, 1
	vpaddq zmm11, zmm11, zmm12
	vpsllq zmm14, zmm14, 1
	vpaddq zmm13, zmm13, zmm14
	vpaddq zmm11, zmm11, zmm13
	vpsllq zmm12, zmm13, 1
	vpaddq zmm11, zmm11, zmm12
	vpsllq zmm12, zmm13, 4
	vpaddq zmm4, zmm11, zmm12
	add rbx, 1
	cmp rbx, 26
	jne 21b
	vmovdqu32 ZMMWORD PTR [rdi+6080], zmm0
	vmovdqu32 ZMMWORD PTR [rdi+6144], zmm1
	vmovdqu32 ZMMWORD PTR [rdi+6208], zmm2
	vmovdqu32 ZMMWORD PTR [rdi+6272], zmm3
	vmovdqu32 ZMMWORD PTR [rdi+6336], zmm4
	mov esi, 4
210:
	vmovdqu ymm10, YMMWORD PTR [rdi+1664]
	vpsrlq ymm11, ymm4, 51
	vpand ymm4, ymm4, ymm10
	vpsrlq ymm12, ymm3, 51
	vpand ymm3, ymm3, ymm10
	vpaddq ymm4, ymm4, ymm12
	vpsrlq ymm12, ymm2, 51
	vpand ymm2, ymm2, ymm10
	vpaddq ymm3, ymm3, ymm12
	vpsrlq ymm12, ymm1, 51
	vpand ymm1, ymm1, ymm10
	vpaddq ymm2, ymm2, ymm12
	vpsrlq ymm12, ymm0, 51
	vpand ymm0, ymm0, ymm10
	vpaddq ymm1, ymm1, ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+1696]
	vpmadd52luq ymm0, ymm11, ymm12
	vpermq ymm10, ymm0, 36
	vmovdqu YMMWORD PTR [rdi+1024], ymm10
	vpermq ymm5, ymm0, 100
	vpermq ymm10, ymm1, 36
	vmovdqu YMMWORD PTR [rdi+1056], ymm10
	vpermq ymm6, ymm1, 100
	vpermq ymm10, ymm2, 36
	vmovdqu YMMWORD PTR [rdi+1088], ymm10
	vpermq ymm7, ymm2, 100
	vpermq ymm10, ymm3, 36
	vmovdqu YMMWORD PTR [rdi+1120], ymm10
	vpermq ymm8, ymm3, 100
	vpermq ymm10, ymm4, 36
	vmovdqu YMMWORD PTR [rdi+1152], ymm10
	vpermq ymm9, ymm4, 100
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm13, ymm10, ymm7
	vpmadd52huq ymm14, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm13, ymm10, ymm6
	vpmadd52huq ymm14, ymm10, ymm5
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm0, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm13, ymm10, ymm7
	vpmadd52huq ymm14, ymm10, ymm6
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm1, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm2, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm8
	vpmadd52huq ymm12, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm3, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm9
	vpmadd52huq ymm12, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm11, ymm10, ymm8
	vpmadd52huq ymm12, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm4, ymm11, ymm12
	vpermq ymm10, ymm0, 225
	vpaddq ymm11, ymm0, ymm10
	vmovdqu ymm12, YMMWORD PTR [rdi+1728]
	vpaddq ymm12, ymm12, ymm0
	vpsubq ymm12, ymm12, ymm10
	vpermq ymm13, ymm12, 0
	vpermq ymm10, ymm11, 170
	vpaddq ymm10, ymm10, ymm13
	vpermq ymm13, ymm11, 255
	vpblendd ymm13, ymm13, ymm12, 12
	vpblendd ymm0, ymm13, ymm10, 48
	vpermq ymm13, ymm12, 85
	vpermq ymm11, ymm11, 0
	vpblendd ymm10, ymm10, ymm11, 204
	vpblendd ymm5, ymm10, ymm13, 48
	vpermq ymm10, ymm1, 225
	vpaddq ymm11, ymm1, ymm10
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpaddq ymm12, ymm12, ymm1
	vpsubq ymm12, ymm12, ymm10
	vpermq ymm13, ymm12, 0
	vpermq ymm10, ymm11, 170
	vpaddq ymm10, ymm10, ymm13
	vpermq ymm13, ymm11, 255
	vpblendd ymm13, ymm13, ymm12, 12
	vpblendd ymm1, ymm13, ymm10, 48
	vpermq ymm13, ymm12, 85
	vpermq ymm11, ymm11, 0
	vpblendd ymm10, ymm10, ymm11, 204
	vpblendd ymm6, ymm10, ymm13, 48
	vpermq ymm10, ymm2, 225
	vpaddq ymm11, ymm2, ymm10
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpaddq ymm12, ymm12, ymm2
	vpsubq ymm12, ymm12, ymm10
	vpermq ymm13, ymm12, 0
	vpermq ymm10, ymm11, 170
	vpaddq ymm10, ymm10, ymm13
	vpermq ymm13, ymm11, 255
	vpblendd ymm13, ymm13, ymm12, 12
	vpblendd ymm2, ymm13, ymm10, 48
	vpermq ymm13, ymm12, 85
	vpermq ymm11, ymm11, 0
	vpblendd ymm10, ymm10, ymm11, 204
	vpblendd ymm7, ymm10, ymm13, 48
	vpermq ymm10, ymm3, 225
	vpaddq ymm11, ymm3, ymm10
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpaddq ymm12, ymm12, ymm3
	vpsubq ymm12, ymm12, ymm10
	vpermq ymm13, ymm12, 0
	vpermq ymm10, ymm11, 170
	vpaddq ymm10, ymm10, ymm13
	vpermq ymm13, ymm11, 255
	vpblendd ymm13, ymm13, ymm12, 12
	vpblendd ymm3, ymm13, ymm10, 48
	vpermq ymm13, ymm12, 85
	vpermq ymm11, ymm11, 0
	vpblendd ymm10, ymm10, ymm11, 204
	vpblendd ymm8, ymm10, ymm13, 48
	vpermq ymm10, ymm4, 225
	vpaddq ymm11, ymm4, ymm10
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpaddq ymm12, ymm12, ymm4
	vpsubq ymm12, ymm12, ymm10
	vpermq ymm13, ymm12, 0
	vpermq ymm10, ymm11, 170
	vpaddq ymm10, ymm10, ymm13
	vpermq ymm13, ymm11, 255
	vpblendd ymm13, ymm13, ymm12, 12
	vpblendd ymm4, ymm13, ymm10, 48
	vpermq ymm13, ymm12, 85
	vpermq ymm11, ymm11, 0
	vpblendd ymm10, ymm10, ymm11, 204
	vpblendd ymm9, ymm10, ymm13, 48
	vmovdqu ymm10, YMMWORD PTR [rdi+1664]
	vpsrlq ymm11, ymm9, 51
	vpand ymm9, ymm9, ymm10
	vpsrlq ymm12, ymm8, 51
	vpand ymm8, ymm8, ymm10
	vpaddq ymm9, ymm9, ymm12
	vpsrlq ymm12, ymm7, 51
	vpand ymm7, ymm7, ymm10
	vpaddq ymm8, ymm8, ymm12
	vpsrlq ymm12, ymm6, 51
	vpand ymm6, ymm6, ymm10
	vpaddq ymm7, ymm7, ymm12
	vpsrlq ymm12, ymm5, 51
	vpand ymm5, ymm5, ymm10
	vpaddq ymm6, ymm6, ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+1696]
	vpmadd52luq ymm5, ymm11, ymm12
	vmovdqu ymm10, YMMWORD PTR [rdi+1664]
	vpsrlq ymm11, ymm4, 51
	vpand ymm4, ymm4, ymm10
	vpsrlq ymm12, ymm3, 51
	vpand ymm3, ymm3, ymm10
	vpaddq ymm4, ymm4, ymm12
	vpsrlq ymm12, ymm2, 51
	vpand ymm2, ymm2, ymm10
	vpaddq ymm3, ymm3, ymm12
	vpsrlq ymm12, ymm1, 51
	vpand ymm1, ymm1, ymm10
	vpaddq ymm2, ymm2, ymm12
	vpsrlq ymm12, ymm0, 51
	vpand ymm0, ymm0, ymm10
	vpaddq ymm1, ymm1, ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+1696]
	vpmadd52luq ymm0, ymm11, ymm12
	vmovdqu YMMWORD PTR [rdi+1184], ymm0
	vmovdqu YMMWORD PTR [rdi+1216], ymm1
	vmovdqu YMMWORD PTR [rdi+1248], ymm2
	vmovdqu YMMWORD PTR [rdi+1280], ymm3
	vmovdqu YMMWORD PTR [rdi+1312], ymm4
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1184]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1216]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1248]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1280]
	vpmadd52luq ymm13, ymm10, ymm7
	vpmadd52huq ymm14, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1312]
	vpmadd52luq ymm13, ymm10, ymm6
	vpmadd52huq ymm14, ymm10, ymm5
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm0, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1184]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1216]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1248]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1280]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1312]
	vpmadd52luq ymm13, ymm10, ymm7
	vpmadd52huq ymm14, ymm10, ymm6
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm1, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1184]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1216]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1248]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1280]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1312]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm2, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1184]
	vpmadd52luq ymm11, ymm10, ymm8
	vpmadd52huq ymm12, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1216]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1248]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1280]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1312]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm3, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1184]
	vpmadd52luq ymm11, ymm10, ymm9
	vpmadd52huq ymm12, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1216]
	vpmadd52luq ymm11, ymm10, ymm8
	vpmadd52huq ymm12, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1248]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1280]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1312]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm4, ymm11, ymm12
	sub rsi, 1
	jne 210b
	vmovdqu ymm10, YMMWORD PTR [rdi+1664]
	vpsrlq ymm11, ymm4, 51
	vpand ymm4, ymm4, ymm10
	vpsrlq ymm12, ymm3, 51
	vpand ymm3, ymm3, ymm10
	vpaddq ymm4, ymm4, ymm12
	vpsrlq ymm12, ymm2, 51
	vpand ymm2, ymm2, ymm10
	vpaddq ymm3, ymm3, ymm12
	vpsrlq ymm12, ymm1, 51
	vpand ymm1, ymm1, ymm10
	vpaddq ymm2, ymm2, ymm12
	vpsrlq ymm12, ymm0, 51
	vpand ymm0, ymm0, ymm10
	vpaddq ymm1, ymm1, ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+1696]
	vpmadd52luq ymm0, ymm11, ymm12
	vpermq ymm10, ymm0, 36
	vmovdqu YMMWORD PTR [rdi+1024], ymm10
	vpermq ymm5, ymm0, 100
	vpermq ymm10, ymm1, 36
	vmovdqu YMMWORD PTR [rdi+1056], ymm10
	vpermq ymm6, ymm1, 100
	vpermq ymm10, ymm2, 36
	vmovdqu YMMWORD PTR [rdi+1088], ymm10
	vpermq ymm7, ymm2, 100
	vpermq ymm10, ymm3, 36
	vmovdqu YMMWORD PTR [rdi+1120], ymm10
	vpermq ymm8, ymm3, 100
	vpermq ymm10, ymm4, 36
	vmovdqu YMMWORD PTR [rdi+1152], ymm10
	vpermq ymm9, ymm4, 100
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm13, ymm10, ymm7
	vpmadd52huq ymm14, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm13, ymm10, ymm6
	vpmadd52huq ymm14, ymm10, ymm5
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm0, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm13, ymm10, ymm7
	vpmadd52huq ymm14, ymm10, ymm6
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm1, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm2, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm8
	vpmadd52huq ymm12, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm3, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm9
	vpmadd52huq ymm12, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm11, ymm10, ymm8
	vpmadd52huq ymm12, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm4, ymm11, ymm12
	vpermq ymm10, ymm0, 225
	vpaddq ymm11, ymm0, ymm10
	vmovdqu ymm12, YMMWORD PTR [rdi+1728]
	vpaddq ymm12, ymm12, ymm0
	vpsubq ymm12, ymm12, ymm10
	vpermq ymm13, ymm12, 0
	vpermq ymm10, ymm11, 170
	vpaddq ymm10, ymm10, ymm13
	vpermq ymm13, ymm11, 255
	vpblendd ymm13, ymm13, ymm12, 12
	vpblendd ymm0, ymm13, ymm10, 48
	vpermq ymm13, ymm12, 85
	vpermq ymm11, ymm11, 0
	vpblendd ymm10, ymm10, ymm11, 204
	vpblendd ymm5, ymm10, ymm13, 48
	vpermq ymm10, ymm1, 225
	vpaddq ymm11, ymm1, ymm10
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpaddq ymm12, ymm12, ymm1
	vpsubq ymm12, ymm12, ymm10
	vpermq ymm13, ymm12, 0
	vpermq ymm10, ymm11, 170
	vpaddq ymm10, ymm10, ymm13
	vpermq ymm13, ymm11, 255
	vpblendd ymm13, ymm13, ymm12, 12
	vpblendd ymm1, ymm13, ymm10, 48
	vpermq ymm13, ymm12, 85
	vpermq ymm11, ymm11, 0
	vpblendd ymm10, ymm10, ymm11, 204
	vpblendd ymm6, ymm10, ymm13, 48
	vpermq ymm10, ymm2, 225
	vpaddq ymm11, ymm2, ymm10
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpaddq ymm12, ymm12, ymm2
	vpsubq ymm12, ymm12, ymm10
	vpermq ymm13, ymm12, 0
	vpermq ymm10, ymm11, 170
	vpaddq ymm10, ymm10, ymm13
	vpermq ymm13, ymm11, 255
	vpblendd ymm13, ymm13, ymm12, 12
	vpblendd ymm2, ymm13, ymm10, 48
	vpermq ymm13, ymm12, 85
	vpermq ymm11, ymm11, 0
	vpblendd ymm10, ymm10, ymm11, 204
	vpblendd ymm7, ymm10, ymm13, 48
	vpermq ymm10, ymm3, 225
	vpaddq ymm11, ymm3, ymm10
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpaddq ymm12, ymm12, ymm3
	vpsubq ymm12, ymm12, ymm10
	vpermq ymm13, ymm12, 0
	vpermq ymm10, ymm11, 170
	vpaddq ymm10, ymm10, ymm13
	vpermq ymm13, ymm11, 255
	vpblendd ymm13, ymm13, ymm12, 12
	vpblendd ymm3, ymm13, ymm10, 48
	vpermq ymm13, ymm12, 85
	vpermq ymm11, ymm11, 0
	vpblendd ymm10, ymm10, ymm11, 204
	vpblendd ymm8, ymm10, ymm13, 48
	vpermq ymm10, ymm4, 225
	vpaddq ymm11, ymm4, ymm10
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpaddq ymm12, ymm12, ymm4
	vpsubq ymm12, ymm12, ymm10
	vpermq ymm13, ymm12, 0
	vpermq ymm10, ymm11, 170
	vpaddq ymm10, ymm10, ymm13
	vpermq ymm13, ymm11, 255
	vpblendd ymm13, ymm13, ymm12, 12
	vpblendd ymm4, ymm13, ymm10, 48
	vpermq ymm13, ymm12, 85
	vpermq ymm11, ymm11, 0
	vpblendd ymm10, ymm10, ymm11, 204
	vpblendd ymm9, ymm10, ymm13, 48
	vmovdqu ymm10, YMMWORD PTR [rdi+1664]
	vpsrlq ymm11, ymm9, 51
	vpand ymm9, ymm9, ymm10
	vpsrlq ymm12, ymm8, 51
	vpand ymm8, ymm8, ymm10
	vpaddq ymm9, ymm9, ymm12
	vpsrlq ymm12, ymm7, 51
	vpand ymm7, ymm7, ymm10
	vpaddq ymm8, ymm8, ymm12
	vpsrlq ymm12, ymm6, 51
	vpand ymm6, ymm6, ymm10
	vpaddq ymm7, ymm7, ymm12
	vpsrlq ymm12, ymm5, 51
	vpand ymm5, ymm5, ymm10
	vpaddq ymm6, ymm6, ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+1696]
	vpmadd52luq ymm5, ymm11, ymm12
	vmovdqu ymm10, YMMWORD PTR [rdi+1664]
	vpsrlq ymm11, ymm4, 51
	vpand ymm4, ymm4, ymm10
	vpsrlq ymm12, ymm3, 51
	vpand ymm3, ymm3, ymm10
	vpaddq ymm4, ymm4, ymm12
	vpsrlq ymm12, ymm2, 51
	vpand ymm2, ymm2, ymm10
	vpaddq ymm3, ymm3, ymm12
	vpsrlq ymm12, ymm1, 51
	vpand ymm1, ymm1, ymm10
	vpaddq ymm2, ymm2, ymm12
	vpsrlq ymm12, ymm0, 51
	vpand ymm0, ymm0, ymm10
	vpaddq ymm1, ymm1, ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+1696]
	vpmadd52luq ymm0, ymm11, ymm12
	vmovdqu YMMWORD PTR [rdi+1184], ymm0
	vmovdqu YMMWORD PTR [rdi+1216], ymm1
	vmovdqu YMMWORD PTR [rdi+1248], ymm2
	vmovdqu YMMWORD PTR [rdi+1280], ymm3
	vmovdqu YMMWORD PTR [rdi+1312], ymm4
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1184]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1216]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1248]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1280]
	vpmadd52luq ymm13, ymm10, ymm7
	vpmadd52huq ymm14, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1312]
	vpmadd52luq ymm13, ymm10, ymm6
	vpmadd52huq ymm14, ymm10, ymm5
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm0, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1184]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1216]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1248]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1280]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1312]
	vpmadd52luq ymm13, ymm10, ymm7
	vpmadd52huq ymm14, ymm10, ymm6
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm1, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1184]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1216]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1248]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1280]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1312]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm2, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1184]
	vpmadd52luq ymm11, ymm10, ymm8
	vpmadd52huq ymm12, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1216]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1248]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1280]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1312]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm3, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1184]
	vpmadd52luq ymm11, ymm10, ymm9
	vpmadd52huq ymm12, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1216]
	vpmadd52luq ymm11, ymm10, ymm8
	vpmadd52huq ymm12, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1248]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1280]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1312]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm4, ymm11, ymm12
	vmovdqu YMMWORD PTR [rdi+6080], ymm0
	vmovdqu YMMWORD PTR [rdi+6144], ymm1
	vmovdqu YMMWORD PTR [rdi+6208], ymm2
	vmovdqu YMMWORD PTR [rdi+6272], ymm3
	vmovdqu YMMWORD PTR [rdi+6336], ymm4
	vmovdqu ymm0, YMMWORD PTR [rdi+6112]
	vmovdqu ymm1, YMMWORD PTR [rdi+6176]
	vmovdqu ymm2, YMMWORD PTR [rdi+6240]
	vmovdqu ymm3, YMMWORD PTR [rdi+6304]
	vmovdqu ymm4, YMMWORD PTR [rdi+6368]
	vpxor ymm13, ymm13, ymm13
	vpermq ymm10, ymm0, 181
	vpermq ymm11, ymm0, 0
	vmovdqu ymm12, YMMWORD PTR [rdi+1728]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 3
	vpblendd ymm11, ymm11, ymm13, 240
	vpaddq ymm0, ymm10, ymm11
	vpermq ymm10, ymm1, 181
	vpermq ymm11, ymm1, 0
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 3
	vpblendd ymm11, ymm11, ymm13, 240
	vpaddq ymm1, ymm10, ymm11
	vpermq ymm10, ymm2, 181
	vpermq ymm11, ymm2, 0
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 3
	vpblendd ymm11, ymm11, ymm13, 240
	vpaddq ymm2, ymm10, ymm11
	vpermq ymm10, ymm3, 181
	vpermq ymm11, ymm3, 0
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 3
	vpblendd ymm11, ymm11, ymm13, 240
	vpaddq ymm3, ymm10, ymm11
	vpermq ymm10, ymm4, 181
	vpermq ymm11, ymm4, 0
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 3
	vpblendd ymm11, ymm11, ymm13, 240
	vpaddq ymm4, ymm10, ymm11
	vmovdqu ymm10, YMMWORD PTR [rdi+1664]
	vpsrlq ymm11, ymm4, 51
	vpand ymm4, ymm4, ymm10
	vpsrlq ymm12, ymm3, 51
	vpand ymm3, ymm3, ymm10
	vpaddq ymm4, ymm4, ymm12
	vpsrlq ymm12, ymm2, 51
	vpand ymm2, ymm2, ymm10
	vpaddq ymm3, ymm3, ymm12
	vpsrlq ymm12, ymm1, 51
	vpand ymm1, ymm1, ymm10
	vpaddq ymm2, ymm2, ymm12
	vpsrlq ymm12, ymm0, 51
	vpand ymm0, ymm0, ymm10
	vpaddq ymm1, ymm1, ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+1696]
	vpmadd52luq ymm0, ymm11, ymm12
	vmovdqu YMMWORD PTR [rdi+1024], ymm0
	vmovdqu YMMWORD PTR [rdi+1056], ymm1
	vmovdqu YMMWORD PTR [rdi+1088], ymm2
	vmovdqu YMMWORD PTR [rdi+1120], ymm3
	vmovdqu YMMWORD PTR [rdi+1152], ymm4
	vmovdqu ymm11, YMMWORD PTR [rdi+448]
	vmovdqu ymm12, YMMWORD PTR [rdi+480]
	vmovdqu ymm13, YMMWORD PTR [rdi+512]
	vmovdqu ymm14, YMMWORD PTR [rdi+544]
	vpunpcklqdq ymm5, ymm11, ymm12
	vpunpckhqdq ymm6, ymm11, ymm12
	vpunpcklqdq ymm7, ymm13, ymm14
	vpunpckhqdq ymm8, ymm13, ymm14
	vperm2i128 ymm11, ymm5, ymm7, 32
	vperm2i128 ymm12, ymm6, ymm8, 32
	vperm2i128 ymm13, ymm5, ymm7, 49
	vperm2i128 ymm14, ymm6, ymm8, 49
	vmovdqu ymm15, YMMWORD PTR [rdi+1664]
	vpand ymm5, ymm11, ymm15
	vpsrlq ymm6, ymm11, 51
	vpsrlq ymm10, ymm15, 13
	vpand ymm10, ymm12, ymm10
	vpsllq ymm10, ymm10, 13
	vpor ymm6, ymm6, ymm10
	vpsrlq ymm7, ymm12, 38
	vpsrlq ymm10, ymm15, 26
	vpand ymm10, ymm13, ymm10
	vpsllq ymm10, ymm10, 26
	vpor ymm7, ymm7, ymm10
	vpsrlq ymm8, ymm13, 25
	vpsrlq ymm10, ymm15, 39
	vpand ymm10, ymm14, ymm10
	vpsllq ymm10, ymm10, 39
	vpor ymm8, ymm8, ymm10
	vpsrlq ymm9, ymm14, 12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm13, ymm10, ymm7
	vpmadd52huq ymm14, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm13, ymm10, ymm6
	vpmadd52huq ymm14, ymm10, ymm5
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm0, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm13, ymm10, ymm7
	vpmadd52huq ymm14, ymm10, ymm6
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm1, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm2, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm8
	vpmadd52huq ymm12, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm3, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm9
	vpmadd52huq ymm12, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm11, ymm10, ymm8
	vpmadd52huq ymm12, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm4, ymm11, ymm12
	vmovdqa ymm5, ymm0
	vmovdqa ymm6, ymm1
	vmovdqa ymm7, ymm2
	vmovdqa ymm8, ymm3
	vmovdqa ymm9, ymm4
	vmovdqu ymm10, YMMWORD PTR [rdi+1664]
	vpsrlq ymm11, ymm9, 51
	vpand ymm9, ymm9, ymm10
	vpsrlq ymm12, ymm8, 51
	vpand ymm8, ymm8, ymm10
	vpaddq ymm9, ymm9, ymm12
	vpsrlq ymm12, ymm7, 51
	vpand ymm7, ymm7, ymm10
	vpaddq ymm8, ymm8, ymm12
	vpsrlq ymm12, ymm6, 51
	vpand ymm6, ymm6, ymm10
	vpaddq ymm7, ymm7, ymm12
	vpsrlq ymm12, ymm5, 51
	vpand ymm5, ymm5, ymm10
	vpaddq ymm6, ymm6, ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+1696]
	vpmadd52luq ymm5, ymm11, ymm12
	vmovdqu ymm0, YMMWORD PTR [rdi+6080]
	vmovdqu ymm1, YMMWORD PTR [rdi+6144]
	vmovdqu ymm2, YMMWORD PTR [rdi+6208]
	vmovdqu ymm3, YMMWORD PTR [rdi+6272]
	vmovdqu ymm4, YMMWORD PTR [rdi+6336]
	vpxor ymm13, ymm13, ymm13
	vpermq ymm10, ymm0, 181
	vpermq ymm11, ymm0, 0
	vmovdqu ymm12, YMMWORD PTR [rdi+1728]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 3
	vpblendd ymm11, ymm11, ymm13, 240
	vpaddq ymm0, ymm10, ymm11
	vpermq ymm10, ymm1, 181
	vpermq ymm11, ymm1, 0
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 3
	vpblendd ymm11, ymm11, ymm13, 240
	vpaddq ymm1, ymm10, ymm11
	vpermq ymm10, ymm2, 181
	vpermq ymm11, ymm2, 0
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 3
	vpblendd ymm11, ymm11, ymm13, 240
	vpaddq ymm2, ymm10, ymm11
	vpermq ymm10, ymm3, 181
	vpermq ymm11, ymm3, 0
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 3
	vpblendd ymm11, ymm11, ymm13, 240
	vpaddq ymm3, ymm10, ymm11
	vpermq ymm10, ymm4, 181
	vpermq ymm11, ymm4, 0
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 3
	vpblendd ymm11, ymm11, ymm13, 240
	vpaddq ymm4, ymm10, ymm11
	vmovdqu ymm10, YMMWORD PTR [rdi+1664]
	vpsrlq ymm11, ymm4, 51
	vpand ymm4, ymm4, ymm10
	vpsrlq ymm12, ymm3, 51
	vpand ymm3, ymm3, ymm10
	vpaddq ymm4, ymm4, ymm12
	vpsrlq ymm12, ymm2, 51
	vpand ymm2, ymm2, ymm10
	vpaddq ymm3, ymm3, ymm12
	vpsrlq ymm12, ymm1, 51
	vpand ymm1, ymm1, ymm10
	vpaddq ymm2, ymm2, ymm12
	vpsrlq ymm12, ymm0, 51
	vpand ymm0, ymm0, ymm10
	vpaddq ymm1, ymm1, ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+1696]
	vpmadd52luq ymm0, ymm11, ymm12
	vmovdqu YMMWORD PTR [rdi+1024], ymm0
	vmovdqu YMMWORD PTR [rdi+1056], ymm1
	vmovdqu YMMWORD PTR [rdi+1088], ymm2
	vmovdqu YMMWORD PTR [rdi+1120], ymm3
	vmovdqu YMMWORD PTR [rdi+1152], ymm4
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm13, ymm10, ymm7
	vpmadd52huq ymm14, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm13, ymm10, ymm6
	vpmadd52huq ymm14, ymm10, ymm5
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm0, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm13, ymm10, ymm7
	vpmadd52huq ymm14, ymm10, ymm6
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm1, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm2, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm8
	vpmadd52huq ymm12, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm3, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1024]
	vpmadd52luq ymm11, ymm10, ymm9
	vpmadd52huq ymm12, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1056]
	vpmadd52luq ymm11, ymm10, ymm8
	vpmadd52huq ymm12, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1088]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1120]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1152]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm4, ymm11, ymm12
	vpermq ymm10, ymm0, 125
	vpermq ymm11, ymm0, 40
	vmovdqu ymm12, YMMWORD PTR [rdi+1728]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 51
	vpaddq ymm10, ymm10, ymm11
	vpermq ymm0, ymm10, 36
	vpermq ymm5, ymm10, 222
	vpermq ymm10, ymm1, 125
	vpermq ymm11, ymm1, 40
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 51
	vpaddq ymm10, ymm10, ymm11
	vpermq ymm1, ymm10, 36
	vpermq ymm6, ymm10, 222
	vpermq ymm10, ymm2, 125
	vpermq ymm11, ymm2, 40
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 51
	vpaddq ymm10, ymm10, ymm11
	vpermq ymm2, ymm10, 36
	vpermq ymm7, ymm10, 222
	vpermq ymm10, ymm3, 125
	vpermq ymm11, ymm3, 40
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 51
	vpaddq ymm10, ymm10, ymm11
	vpermq ymm3, ymm10, 36
	vpermq ymm8, ymm10, 222
	vpermq ymm10, ymm4, 125
	vpermq ymm11, ymm4, 40
	vmovdqu ymm12, YMMWORD PTR [rdi+1760]
	vpsubq ymm12, ymm12, ymm11
	vpblendd ymm11, ymm11, ymm12, 51
	vpaddq ymm10, ymm10, ymm11
	vpermq ymm4, ymm10, 36
	vpermq ymm9, ymm10, 222
	vmovdqu ymm10, YMMWORD PTR [rdi+1664]
	vpsrlq ymm11, ymm9, 51
	vpand ymm9, ymm9, ymm10
	vpsrlq ymm12, ymm8, 51
	vpand ymm8, ymm8, ymm10
	vpaddq ymm9, ymm9, ymm12
	vpsrlq ymm12, ymm7, 51
	vpand ymm7, ymm7, ymm10
	vpaddq ymm8, ymm8, ymm12
	vpsrlq ymm12, ymm6, 51
	vpand ymm6, ymm6, ymm10
	vpaddq ymm7, ymm7, ymm12
	vpsrlq ymm12, ymm5, 51
	vpand ymm5, ymm5, ymm10
	vpaddq ymm6, ymm6, ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+1696]
	vpmadd52luq ymm5, ymm11, ymm12
	vmovdqu ymm10, YMMWORD PTR [rdi+1664]
	vpsrlq ymm11, ymm4, 51
	vpand ymm4, ymm4, ymm10
	vpsrlq ymm12, ymm3, 51
	vpand ymm3, ymm3, ymm10
	vpaddq ymm4, ymm4, ymm12
	vpsrlq ymm12, ymm2, 51
	vpand ymm2, ymm2, ymm10
	vpaddq ymm3, ymm3, ymm12
	vpsrlq ymm12, ymm1, 51
	vpand ymm1, ymm1, ymm10
	vpaddq ymm2, ymm2, ymm12
	vpsrlq ymm12, ymm0, 51
	vpand ymm0, ymm0, ymm10
	vpaddq ymm1, ymm1, ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+1696]
	vpmadd52luq ymm0, ymm11, ymm12
	vmovdqu YMMWORD PTR [rdi+1184], ymm0
	vmovdqu YMMWORD PTR [rdi+1216], ymm1
	vmovdqu YMMWORD PTR [rdi+1248], ymm2
	vmovdqu YMMWORD PTR [rdi+1280], ymm3
	vmovdqu YMMWORD PTR [rdi+1312], ymm4
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1184]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1216]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1248]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1280]
	vpmadd52luq ymm13, ymm10, ymm7
	vpmadd52huq ymm14, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1312]
	vpmadd52luq ymm13, ymm10, ymm6
	vpmadd52huq ymm14, ymm10, ymm5
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm0, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1184]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1216]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1248]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1280]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1312]
	vpmadd52luq ymm13, ymm10, ymm7
	vpmadd52huq ymm14, ymm10, ymm6
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm1, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1184]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1216]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1248]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1280]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1312]
	vpmadd52luq ymm13, ymm10, ymm8
	vpmadd52huq ymm14, ymm10, ymm7
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm2, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1184]
	vpmadd52luq ymm11, ymm10, ymm8
	vpmadd52huq ymm12, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1216]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1248]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1280]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vmovdqu ymm10, YMMWORD PTR [rdi+1312]
	vpmadd52luq ymm13, ymm10, ymm9
	vpmadd52huq ymm14, ymm10, ymm8
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm3, ymm11, ymm12
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpxor ymm14, ymm14, ymm14
	vmovdqu ymm10, YMMWORD PTR [rdi+1184]
	vpmadd52luq ymm11, ymm10, ymm9
	vpmadd52huq ymm12, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rdi+1216]
	vpmadd52luq ymm11, ymm10, ymm8
	vpmadd52huq ymm12, ymm10, ymm7
	vmovdqu ymm10, YMMWORD PTR [rdi+1248]
	vpmadd52luq ymm11, ymm10, ymm7
	vpmadd52huq ymm12, ymm10, ymm6
	vmovdqu ymm10, YMMWORD PTR [rdi+1280]
	vpmadd52luq ymm11, ymm10, ymm6
	vpmadd52huq ymm12, ymm10, ymm5
	vmovdqu ymm10, YMMWORD PTR [rdi+1312]
	vpmadd52luq ymm11, ymm10, ymm5
	vpmadd52huq ymm14, ymm10, ymm9
	vpsllq ymm12, ymm12, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm14, ymm14, 1
	vpaddq ymm13, ymm13, ymm14
	vpaddq ymm11, ymm11, ymm13
	vpsllq ymm12, ymm13, 1
	vpaddq ymm11, ymm11, ymm12
	vpsllq ymm12, ymm13, 4
	vpaddq ymm4, ymm11, ymm12
	vmovdqu ymm10, YMMWORD PTR [rdi+1664]
	vpsrlq ymm11, ymm4, 51
	vpand ymm4, ymm4, ymm10
	vpsrlq ymm12, ymm3, 51
	vpand ymm3, ymm3, ymm10
	vpaddq ymm4, ymm4, ymm12
	vpsrlq ymm12, ymm2, 51
	vpand ymm2, ymm2, ymm10
	vpaddq ymm3, ymm3, ymm12
	vpsrlq ymm12, ymm1, 51
	vpand ymm1, ymm1, ymm10
	vpaddq ymm2, ymm2, ymm12
	vpsrlq ymm12, ymm0, 51
	vpand ymm0, ymm0, ymm10
	vpaddq ymm1, ymm1, ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+1696]
	vpmadd52luq ymm0, ymm11, ymm12
	vmovdqu ymm10, YMMWORD PTR [rdi+1664]
	vpsrlq ymm11, ymm4, 51
	vpand ymm4, ymm4, ymm10
	vpsrlq ymm12, ymm3, 51
	vpand ymm3, ymm3, ymm10
	vpaddq ymm4, ymm4, ymm12
	vpsrlq ymm12, ymm2, 51
	vpand ymm2, ymm2, ymm10
	vpaddq ymm3, ymm3, ymm12
	vpsrlq ymm12, ymm1, 51
	vpand ymm1, ymm1, ymm10
	vpaddq ymm2, ymm2, ymm12
	vpsrlq ymm12, ymm0, 51
	vpand ymm0, ymm0, ymm10
	vpaddq ymm1, ymm1, ymm12
	vmovdqu ymm12, YMMWORD PTR [rdi+1696]
	vpmadd52luq ymm0, ymm11, ymm12
	vmovdqu ymm10, YMMWORD PTR [rdi+1664]
	vpsrlq ymm11, ymm0, 51
	vpand ymm0, ymm0, ymm10
	vpaddq ymm1, ymm1, ymm11
	vpsrlq ymm11, ymm1, 51
	vpand ymm1, ymm1, ymm10
	vpaddq ymm2, ymm2, ymm11
	vpsrlq ymm11, ymm2, 51
	vpand ymm2, ymm2, ymm10
	vpaddq ymm3, ymm3, ymm11
	vpsrlq ymm11, ymm3, 51
	vpand ymm3, ymm3, ymm10
	vpaddq ymm4, ymm4, ymm11
	vmovdqu ymm11, YMMWORD PTR [rdi+1792]
	vpand ymm12, ymm1, ymm11
	vpsllq ymm12, ymm12, 51
	vpor ymm5, ymm0, ymm12
	vpsrlq ymm6, ymm1, 13
	vmovdqu ymm11, YMMWORD PTR [rdi+1824]
	vpand ymm12, ymm2, ymm11
	vpsllq ymm12, ymm12, 38
	vpor ymm6, ymm6, ymm12
	vpsrlq ymm7, ymm2, 26
	vmovdqu ymm11, YMMWORD PTR [rdi+1856]
	vpand ymm12, ymm3, ymm11
	vpsllq ymm12, ymm12, 25
	vpor ymm7, ymm7, ymm12
	vpsrlq ymm8, ymm3, 39
	vpsllq ymm12, ymm4, 12
	vpor ymm8, ymm8, ymm12
	vpunpcklqdq ymm0, ymm5, ymm6
	vpunpckhqdq ymm1, ymm5, ymm6
	vpunpcklqdq ymm2, ymm7, ymm8
	vpunpckhqdq ymm3, ymm7, ymm8
	vperm2i128 ymm5, ymm0, ymm2, 32
	vperm2i128 ymm6, ymm1, ymm3, 32
	vperm2i128 ymm7, ymm0, ymm2, 49
	vperm2i128 ymm8, ymm1, ymm3, 49
	vmovdqu YMMWORD PTR [rdi+64], ymm5
	vmovdqu YMMWORD PTR [rdi+96], ymm6
	vmovdqu YMMWORD PTR [rdi+128], ymm7
	vmovdqu YMMWORD PTR [rdi+160], ymm8
	vzeroupper
	lfence
	mov DWORD PTR [rdi+1600], r11d
	ldmxcsr DWORD PTR [rdi+1600]
	call {vg_gf25519_r64_invert}
	mov rdx, QWORD PTR [rdi+544]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+64]
	mulx r10, rax, QWORD PTR [rdi+72]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+80]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+88]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+552]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+72]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+80]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+88]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+560]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+72]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+80]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+88]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+568]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+72]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+80]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+88]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov edx, 38
	xor ebp, ebp
	mulx rcx, rax, r12
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, r13
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, r14
	adox r10, rax
	adcx r11, rcx
	mulx r12, rax, r15
	adox r11, rax
	adcx r12, rbp
	adox r12, rbp
	mulx rcx, rax, r12
	shl r11, 1
	sbb rbp, rbp
	shr r11, 1
	and rbp, 19
	add rax, rbp
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	mov rdx, QWORD PTR [rdi+544]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+96]
	mulx r10, rax, QWORD PTR [rdi+104]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+112]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+120]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+552]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+96]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+104]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+120]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+560]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+96]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+104]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+120]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+568]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+96]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+104]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+112]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+120]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov edx, 38
	xor ebp, ebp
	mulx rcx, rax, r12
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, r13
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, r14
	adox r10, rax
	adcx r11, rcx
	mulx r12, rax, r15
	adox r11, rax
	adcx r12, rbp
	adox r12, rbp
	mulx rcx, rax, r12
	shl r11, 1
	sbb rbp, rbp
	shr r11, 1
	and rbp, 19
	add rax, rbp
	add r8, rax
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov QWORD PTR [rdi+96], r8
	mov QWORD PTR [rdi+104], r9
	mov QWORD PTR [rdi+112], r10
	mov QWORD PTR [rdi+120], r11
	mov r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+88]
	mov rax, r11
	shr rax, 63
	movabs rdx, 9223372036854775807
	and r11, rdx
	mov ecx, 0
	sub rcx, rax
	and rcx, 19
	add r8, rcx
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov r12, r8
	add r12, 19
	mov r13, r9
	adc r13, 0
	mov r14, r10
	adc r14, 0
	mov r15, r11
	adc r15, 0
	mov rax, r15
	shr rax, 63
	and r15, rdx
	mov ecx, 0
	sub rcx, rax
	xor r12, r8
	and r12, rcx
	xor r8, r12
	xor r13, r9
	and r13, rcx
	xor r9, r13
	xor r14, r10
	and r14, rcx
	xor r10, r14
	xor r15, r11
	and r15, rcx
	xor r11, r15
	mov rbx, r8
	and rbx, 1
	ror rbx, 1
	mov r8, QWORD PTR [rdi+96]
	mov r9, QWORD PTR [rdi+104]
	mov r10, QWORD PTR [rdi+112]
	mov r11, QWORD PTR [rdi+120]
	mov rax, r11
	shr rax, 63
	movabs rdx, 9223372036854775807
	and r11, rdx
	mov ecx, 0
	sub rcx, rax
	and rcx, 19
	add r8, rcx
	adc r9, 0
	adc r10, 0
	adc r11, 0
	mov r12, r8
	add r12, 19
	mov r13, r9
	adc r13, 0
	mov r14, r10
	adc r14, 0
	mov r15, r11
	adc r15, 0
	mov rax, r15
	shr rax, 63
	and r15, rdx
	mov ecx, 0
	sub rcx, rax
	xor r12, r8
	and r12, rcx
	xor r8, r12
	xor r13, r9
	and r13, rcx
	xor r9, r13
	xor r14, r10
	and r14, rcx
	xor r10, r14
	xor r15, r11
	and r15, rcx
	xor r11, r15
	add r11, rbx
	mov rdx, rdi
	mov rdi, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdx]
	mov rbp, QWORD PTR [rdx+8]
	mov r12, QWORD PTR [rdx+16]
	mov r13, QWORD PTR [rdx+24]
	mov r14, QWORD PTR [rdx+32]
	mov r15, QWORD PTR [rdx+40]
	mov QWORD PTR [rdi], r8
	mov QWORD PTR [rdi+8], r9
	mov QWORD PTR [rdi+16], r10
	mov QWORD PTR [rdi+24], r11
	ret
	.p2align 6
