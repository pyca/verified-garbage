// The functions of `src/internal/vg_ed25519_scalar_base_adx.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed25519_scalar_base_adx:
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
	movabs r8, 7823031704397949478
	movabs r9, -7597533027662568039
	movabs r10, -6764740812712532373
	movabs r11, 7134411796825635086
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	movabs r8, 7462577410509771378
	movabs r9, -601909034585697455
	movabs r10, -7060168469185226901
	movabs r11, 3295207565379300510
	mov QWORD PTR [rdi+96], r8
	mov QWORD PTR [rdi+104], r9
	mov QWORD PTR [rdi+112], r10
	mov QWORD PTR [rdi+120], r11
	movzx eax, BYTE PTR [rdi+1023]
	mov ecx, 0
	sub rcx, rax
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm0, XMMWORD PTR [rdi+64]
	movdqu xmm1, XMMWORD PTR [rdi+96]
	movdqa xmm2, xmm0
	pxor xmm2, xmm1
	pand xmm2, xmm15
	pxor xmm0, xmm2
	pxor xmm1, xmm2
	movdqu XMMWORD PTR [rdi+64], xmm0
	movdqu XMMWORD PTR [rdi+96], xmm1
	movdqu xmm0, XMMWORD PTR [rdi+80]
	movdqu xmm1, XMMWORD PTR [rdi+112]
	movdqa xmm2, xmm0
	pxor xmm2, xmm1
	pand xmm2, xmm15
	pxor xmm0, xmm2
	pxor xmm1, xmm2
	movdqu XMMWORD PTR [rdi+80], xmm0
	movdqu XMMWORD PTR [rdi+112], xmm1
	movabs r8, -4018442001146854144
	movabs r9, -7119228594722234432
	movabs r10, -3000187961379265294
	movabs r11, 7475646097258766663
	mov QWORD PTR [rdi+96], r8
	mov QWORD PTR [rdi+104], r9
	mov QWORD PTR [rdi+112], r10
	mov QWORD PTR [rdi+120], r11
	movabs r8, -1548687225747868975
	movabs r9, 435511593044674468
	movabs r10, -6455493640763011980
	movabs r11, 4197973734148213833
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	movzx eax, BYTE PTR [rdi+1023]
	mov ecx, 0
	sub rcx, rax
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm0, XMMWORD PTR [rdi+96]
	movdqu xmm1, XMMWORD PTR [rdi+128]
	movdqa xmm2, xmm0
	pxor xmm2, xmm1
	pand xmm2, xmm15
	pxor xmm0, xmm2
	pxor xmm1, xmm2
	movdqu XMMWORD PTR [rdi+96], xmm0
	movdqu XMMWORD PTR [rdi+128], xmm1
	movdqu xmm0, XMMWORD PTR [rdi+112]
	movdqu xmm1, XMMWORD PTR [rdi+144]
	movdqa xmm2, xmm0
	pxor xmm2, xmm1
	pand xmm2, xmm15
	pxor xmm0, xmm2
	pxor xmm1, xmm2
	movdqu XMMWORD PTR [rdi+112], xmm0
	movdqu XMMWORD PTR [rdi+144], xmm1
	movabs r8, 1
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	movabs r8, 1
	movabs r9, 0
	movabs r10, 0
	movabs r11, 0
	mov QWORD PTR [rdi+160], r8
	mov QWORD PTR [rdi+168], r9
	mov QWORD PTR [rdi+176], r10
	mov QWORD PTR [rdi+184], r11
	movzx eax, BYTE PTR [rdi+1023]
	mov ecx, 0
	sub rcx, rax
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm0, XMMWORD PTR [rdi+128]
	movdqu xmm1, XMMWORD PTR [rdi+160]
	movdqa xmm2, xmm0
	pxor xmm2, xmm1
	pand xmm2, xmm15
	pxor xmm0, xmm2
	pxor xmm1, xmm2
	movdqu XMMWORD PTR [rdi+128], xmm0
	movdqu XMMWORD PTR [rdi+160], xmm1
	movdqu xmm0, XMMWORD PTR [rdi+144]
	movdqu xmm1, XMMWORD PTR [rdi+176]
	movdqa xmm2, xmm0
	pxor xmm2, xmm1
	pand xmm2, xmm15
	pxor xmm0, xmm2
	pxor xmm1, xmm2
	movdqu XMMWORD PTR [rdi+144], xmm0
	movdqu XMMWORD PTR [rdi+176], xmm1
	movabs r8, 7604676615052082113
	movabs r9, 403824292993866609
	movabs r10, 3945042064111362700
	movabs r11, 4865775283739911641
	mov QWORD PTR [rdi+160], r8
	mov QWORD PTR [rdi+168], r9
	mov QWORD PTR [rdi+176], r10
	mov QWORD PTR [rdi+184], r11
	movabs r8, -5371342369254820366
	movabs r9, 9005726412798474692
	movabs r10, 3550782887848559701
	movabs r11, 6049656988310836243
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	movzx eax, BYTE PTR [rdi+1023]
	mov ecx, 0
	sub rcx, rax
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm0, XMMWORD PTR [rdi+160]
	movdqu xmm1, XMMWORD PTR [rdi+192]
	movdqa xmm2, xmm0
	pxor xmm2, xmm1
	pand xmm2, xmm15
	pxor xmm0, xmm2
	pxor xmm1, xmm2
	movdqu XMMWORD PTR [rdi+160], xmm0
	movdqu XMMWORD PTR [rdi+192], xmm1
	movdqu xmm0, XMMWORD PTR [rdi+176]
	movdqu xmm1, XMMWORD PTR [rdi+208]
	movdqa xmm2, xmm0
	pxor xmm2, xmm1
	pand xmm2, xmm15
	pxor xmm0, xmm2
	pxor xmm1, xmm2
	movdqu XMMWORD PTR [rdi+176], xmm0
	movdqu XMMWORD PTR [rdi+208], xmm1
	mov ebx, 0
21:
	cmp rbx, 26
	je 22f
	jmp 23f
22:
	call {vg_ed25519_r64_double_ext_adx}
	call {vg_ed25519_r64_double_ext_adx}
	call {vg_ed25519_r64_double_ext_adx}
	call {vg_ed25519_r64_double_ext_adx}
	call {vg_ed25519_r64_double_ext_adx}
23:
	cmp rbx, 25
	je 24f
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
	sub rax, 16
	sbb rdx, rdx
	mov QWORD PTR [rdi+1152], rdx
	xor rax, rdx
	sub rax, rdx
	mov r8, rax
	mov rdx, r9
	mov rax, rdx
	mov ecx, 1536
	mul rcx
	lea rdx, {VG_ED25519_COMB}
	add rdx, rax
	lea rax, {VG_ED25519_COMB}
	vmovq xmm14, r8
	vpbroadcastd ymm14, xmm14
	vpxor ymm11, ymm11, ymm11
	vpxor ymm12, ymm12, ymm12
	vpxor ymm13, ymm13, ymm13
	vpcmpeqd ymm15, ymm14, YMMWORD PTR [rax+39936]
	vmovdqu ymm10, YMMWORD PTR [rdx]
	vpand ymm10, ymm10, ymm15
	vpor ymm11, ymm11, ymm10
	vmovdqu ymm10, YMMWORD PTR [rdx+32]
	vpand ymm10, ymm10, ymm15
	vpor ymm12, ymm12, ymm10
	vmovdqu ymm10, YMMWORD PTR [rdx+64]
	vpand ymm10, ymm10, ymm15
	vpor ymm13, ymm13, ymm10
	vpcmpeqd ymm15, ymm14, YMMWORD PTR [rax+39968]
	vmovdqu ymm10, YMMWORD PTR [rdx+96]
	vpand ymm10, ymm10, ymm15
	vpor ymm11, ymm11, ymm10
	vmovdqu ymm10, YMMWORD PTR [rdx+128]
	vpand ymm10, ymm10, ymm15
	vpor ymm12, ymm12, ymm10
	vmovdqu ymm10, YMMWORD PTR [rdx+160]
	vpand ymm10, ymm10, ymm15
	vpor ymm13, ymm13, ymm10
	vpcmpeqd ymm15, ymm14, YMMWORD PTR [rax+40000]
	vmovdqu ymm10, YMMWORD PTR [rdx+192]
	vpand ymm10, ymm10, ymm15
	vpor ymm11, ymm11, ymm10
	vmovdqu ymm10, YMMWORD PTR [rdx+224]
	vpand ymm10, ymm10, ymm15
	vpor ymm12, ymm12, ymm10
	vmovdqu ymm10, YMMWORD PTR [rdx+256]
	vpand ymm10, ymm10, ymm15
	vpor ymm13, ymm13, ymm10
	vpcmpeqd ymm15, ymm14, YMMWORD PTR [rax+40032]
	vmovdqu ymm10, YMMWORD PTR [rdx+288]
	vpand ymm10, ymm10, ymm15
	vpor ymm11, ymm11, ymm10
	vmovdqu ymm10, YMMWORD PTR [rdx+320]
	vpand ymm10, ymm10, ymm15
	vpor ymm12, ymm12, ymm10
	vmovdqu ymm10, YMMWORD PTR [rdx+352]
	vpand ymm10, ymm10, ymm15
	vpor ymm13, ymm13, ymm10
	vpcmpeqd ymm15, ymm14, YMMWORD PTR [rax+40064]
	vmovdqu ymm10, YMMWORD PTR [rdx+384]
	vpand ymm10, ymm10, ymm15
	vpor ymm11, ymm11, ymm10
	vmovdqu ymm10, YMMWORD PTR [rdx+416]
	vpand ymm10, ymm10, ymm15
	vpor ymm12, ymm12, ymm10
	vmovdqu ymm10, YMMWORD PTR [rdx+448]
	vpand ymm10, ymm10, ymm15
	vpor ymm13, ymm13, ymm10
	vpcmpeqd ymm15, ymm14, YMMWORD PTR [rax+40096]
	vmovdqu ymm10, YMMWORD PTR [rdx+480]
	vpand ymm10, ymm10, ymm15
	vpor ymm11, ymm11, ymm10
	vmovdqu ymm10, YMMWORD PTR [rdx+512]
	vpand ymm10, ymm10, ymm15
	vpor ymm12, ymm12, ymm10
	vmovdqu ymm10, YMMWORD PTR [rdx+544]
	vpand ymm10, ymm10, ymm15
	vpor ymm13, ymm13, ymm10
	vpcmpeqd ymm15, ymm14, YMMWORD PTR [rax+40128]
	vmovdqu ymm10, YMMWORD PTR [rdx+576]
	vpand ymm10, ymm10, ymm15
	vpor ymm11, ymm11, ymm10
	vmovdqu ymm10, YMMWORD PTR [rdx+608]
	vpand ymm10, ymm10, ymm15
	vpor ymm12, ymm12, ymm10
	vmovdqu ymm10, YMMWORD PTR [rdx+640]
	vpand ymm10, ymm10, ymm15
	vpor ymm13, ymm13, ymm10
	vpcmpeqd ymm15, ymm14, YMMWORD PTR [rax+40160]
	vmovdqu ymm10, YMMWORD PTR [rdx+672]
	vpand ymm10, ymm10, ymm15
	vpor ymm11, ymm11, ymm10
	vmovdqu ymm10, YMMWORD PTR [rdx+704]
	vpand ymm10, ymm10, ymm15
	vpor ymm12, ymm12, ymm10
	vmovdqu ymm10, YMMWORD PTR [rdx+736]
	vpand ymm10, ymm10, ymm15
	vpor ymm13, ymm13, ymm10
	vpcmpeqd ymm15, ymm14, YMMWORD PTR [rax+40192]
	vmovdqu ymm10, YMMWORD PTR [rdx+768]
	vpand ymm10, ymm10, ymm15
	vpor ymm11, ymm11, ymm10
	vmovdqu ymm10, YMMWORD PTR [rdx+800]
	vpand ymm10, ymm10, ymm15
	vpor ymm12, ymm12, ymm10
	vmovdqu ymm10, YMMWORD PTR [rdx+832]
	vpand ymm10, ymm10, ymm15
	vpor ymm13, ymm13, ymm10
	vpcmpeqd ymm15, ymm14, YMMWORD PTR [rax+40224]
	vmovdqu ymm10, YMMWORD PTR [rdx+864]
	vpand ymm10, ymm10, ymm15
	vpor ymm11, ymm11, ymm10
	vmovdqu ymm10, YMMWORD PTR [rdx+896]
	vpand ymm10, ymm10, ymm15
	vpor ymm12, ymm12, ymm10
	vmovdqu ymm10, YMMWORD PTR [rdx+928]
	vpand ymm10, ymm10, ymm15
	vpor ymm13, ymm13, ymm10
	vpcmpeqd ymm15, ymm14, YMMWORD PTR [rax+40256]
	vmovdqu ymm10, YMMWORD PTR [rdx+960]
	vpand ymm10, ymm10, ymm15
	vpor ymm11, ymm11, ymm10
	vmovdqu ymm10, YMMWORD PTR [rdx+992]
	vpand ymm10, ymm10, ymm15
	vpor ymm12, ymm12, ymm10
	vmovdqu ymm10, YMMWORD PTR [rdx+1024]
	vpand ymm10, ymm10, ymm15
	vpor ymm13, ymm13, ymm10
	vpcmpeqd ymm15, ymm14, YMMWORD PTR [rax+40288]
	vmovdqu ymm10, YMMWORD PTR [rdx+1056]
	vpand ymm10, ymm10, ymm15
	vpor ymm11, ymm11, ymm10
	vmovdqu ymm10, YMMWORD PTR [rdx+1088]
	vpand ymm10, ymm10, ymm15
	vpor ymm12, ymm12, ymm10
	vmovdqu ymm10, YMMWORD PTR [rdx+1120]
	vpand ymm10, ymm10, ymm15
	vpor ymm13, ymm13, ymm10
	vpcmpeqd ymm15, ymm14, YMMWORD PTR [rax+40320]
	vmovdqu ymm10, YMMWORD PTR [rdx+1152]
	vpand ymm10, ymm10, ymm15
	vpor ymm11, ymm11, ymm10
	vmovdqu ymm10, YMMWORD PTR [rdx+1184]
	vpand ymm10, ymm10, ymm15
	vpor ymm12, ymm12, ymm10
	vmovdqu ymm10, YMMWORD PTR [rdx+1216]
	vpand ymm10, ymm10, ymm15
	vpor ymm13, ymm13, ymm10
	vpcmpeqd ymm15, ymm14, YMMWORD PTR [rax+40352]
	vmovdqu ymm10, YMMWORD PTR [rdx+1248]
	vpand ymm10, ymm10, ymm15
	vpor ymm11, ymm11, ymm10
	vmovdqu ymm10, YMMWORD PTR [rdx+1280]
	vpand ymm10, ymm10, ymm15
	vpor ymm12, ymm12, ymm10
	vmovdqu ymm10, YMMWORD PTR [rdx+1312]
	vpand ymm10, ymm10, ymm15
	vpor ymm13, ymm13, ymm10
	vpcmpeqd ymm15, ymm14, YMMWORD PTR [rax+40384]
	vmovdqu ymm10, YMMWORD PTR [rdx+1344]
	vpand ymm10, ymm10, ymm15
	vpor ymm11, ymm11, ymm10
	vmovdqu ymm10, YMMWORD PTR [rdx+1376]
	vpand ymm10, ymm10, ymm15
	vpor ymm12, ymm12, ymm10
	vmovdqu ymm10, YMMWORD PTR [rdx+1408]
	vpand ymm10, ymm10, ymm15
	vpor ymm13, ymm13, ymm10
	vpcmpeqd ymm15, ymm14, YMMWORD PTR [rax+40416]
	vmovdqu ymm10, YMMWORD PTR [rdx+1440]
	vpand ymm10, ymm10, ymm15
	vpor ymm11, ymm11, ymm10
	vmovdqu ymm10, YMMWORD PTR [rdx+1472]
	vpand ymm10, ymm10, ymm15
	vpor ymm12, ymm12, ymm10
	vmovdqu ymm10, YMMWORD PTR [rdx+1504]
	vpand ymm10, ymm10, ymm15
	vpor ymm13, ymm13, ymm10
	vmovdqu YMMWORD PTR [rdi+192], ymm11
	vmovdqu YMMWORD PTR [rdi+224], ymm12
	vmovdqu YMMWORD PTR [rdi+256], ymm13
	vzeroupper
	mov rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	and rcx, 1
	mov rax, QWORD PTR [rdi+192]
	or rax, rcx
	mov QWORD PTR [rdi+192], rax
	mov rax, QWORD PTR [rdi+224]
	or rax, rcx
	mov QWORD PTR [rdi+224], rax
	mov rcx, QWORD PTR [rdi+1152]
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm0, XMMWORD PTR [rdi+192]
	movdqu xmm1, XMMWORD PTR [rdi+224]
	movdqa xmm2, xmm0
	pxor xmm2, xmm1
	pand xmm2, xmm15
	pxor xmm0, xmm2
	pxor xmm1, xmm2
	movdqu XMMWORD PTR [rdi+192], xmm0
	movdqu XMMWORD PTR [rdi+224], xmm1
	movdqu xmm0, XMMWORD PTR [rdi+208]
	movdqu xmm1, XMMWORD PTR [rdi+240]
	movdqa xmm2, xmm0
	pxor xmm2, xmm1
	pand xmm2, xmm15
	pxor xmm0, xmm2
	pxor xmm1, xmm2
	movdqu XMMWORD PTR [rdi+208], xmm0
	movdqu XMMWORD PTR [rdi+240], xmm1
	movabs r8, -38
	sub r8, QWORD PTR [rdi+256]
	movabs r9, -1
	sbb r9, QWORD PTR [rdi+264]
	movabs r10, -1
	sbb r10, QWORD PTR [rdi+272]
	movabs r11, -1
	sbb r11, QWORD PTR [rdi+280]
	sbb rax, rax
	and rax, 38
	sub r8, rax
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb rax, rax
	and rax, 38
	test rcx, rcx
	cmove r8, QWORD PTR [rdi+256]
	cmove r9, QWORD PTR [rdi+264]
	cmove r10, QWORD PTR [rdi+272]
	cmove r11, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+256], r8
	mov QWORD PTR [rdi+264], r9
	mov QWORD PTR [rdi+272], r10
	mov QWORD PTR [rdi+280], r11
	call {vg_ed25519_r64_add_affine_ext_adx}
	jmp 25f
24:
25:
	add rbx, 1
	cmp rbx, 52
	jne 21b
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
