// The functions of `src/hmac_sha1.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_sha1_init_shani:
	cmp rcx, 65
	jae 20f
	lea rsp, [rsp-104]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+48], rbx
	mov QWORD PTR [r8+56], rbp
	mov QWORD PTR [r8+64], r12
	mov QWORD PTR [r8+72], r13
	mov QWORD PTR [r8+80], r14
	mov QWORD PTR [r8+88], r15
	mov rbx, rdi
	mov r12, rsi
	mov r15, r8
	mov rbp, rdx
	mov r13, rcx
	mov rdi, rbx
	call {vg_sha1_init_core}
	mov rdi, r12
	call {vg_sha1_init_core}
	movabs rax, 3906369333256140342
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqu XMMWORD PTR [rbx+20], xmm0
	movdqu XMMWORD PTR [rbx+36], xmm0
	movdqu XMMWORD PTR [rbx+52], xmm0
	movdqu XMMWORD PTR [rbx+68], xmm0
	mov r14d, 0
	mov rcx, r13
	shr rcx, 4
	test rcx, rcx
	je 22f
24:
	movdqu xmm1, XMMWORD PTR [rbp+r14*1]
	pxor xmm1, xmm0
	mov r10, r14
	and r10, 48
	movdqu XMMWORD PTR [rbx+r10*1+20], xmm1
	add r14, 16
	sub rcx, 1
	jne 24b
	jmp 23f
22:
23:
	cmp r14, r13
	je 25f
27:
	movzx eax, BYTE PTR [rbp+r14*1]
	xor eax, 54
	mov r10, r14
	and r10, 63
	mov BYTE PTR [rbx+r10*1+20], al
	add r14, 1
	cmp r14, r13
	jne 27b
	jmp 26f
25:
26:
	movabs rax, 7668058320836127338
	movq xmm1, rax
	punpcklqdq xmm1, xmm1
	movdqu xmm2, XMMWORD PTR [rbx+20]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [r12+20], xmm2
	movdqu xmm2, XMMWORD PTR [rbx+36]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [r12+36], xmm2
	movdqu xmm2, XMMWORD PTR [rbx+52]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [r12+52], xmm2
	movdqu xmm2, XMMWORD PTR [rbx+68]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [r12+68], xmm2
	mov rsi, rbx
	add rsi, 20
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha1_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov rbx, r12
	mov rsi, r12
	add rsi, 20
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha1_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov rbx, QWORD PTR [r15+48]
	mov rbp, QWORD PTR [r15+56]
	mov r12, QWORD PTR [r15+64]
	mov r13, QWORD PTR [r15+72]
	mov r14, QWORD PTR [r15+80]
	mov r15, QWORD PTR [r15+88]
	lea rsp, [rsp+104]
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	pxor xmm12, xmm12
	pxor xmm13, xmm13
	pxor xmm14, xmm14
	pxor xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-120]
	movdqu XMMWORD PTR [rsp+104], xmm0
	movdqu XMMWORD PTR [rsp+88], xmm0
	movdqu XMMWORD PTR [rsp+72], xmm0
	movdqu XMMWORD PTR [rsp+56], xmm0
	movdqu XMMWORD PTR [rsp+40], xmm0
	movdqu XMMWORD PTR [rsp+24], xmm0
	movdqu XMMWORD PTR [rsp+8], xmm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+120]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r10d, r10d
21:
	ret
20:
	lea rsp, [rsp-1128]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+448], rbx
	mov QWORD PTR [r8+456], rbp
	mov QWORD PTR [r8+464], r12
	mov QWORD PTR [r8+472], r13
	mov QWORD PTR [r8+480], r14
	mov QWORD PTR [r8+488], r15
	mov r15, r8
	mov rbx, rdx
	mov rbp, rcx
	mov r12, rdi
	mov r13, rsi
	cmp rbp, 65
	jae 28f
	mov rdx, rbx
	mov rcx, rbp
	jmp 29f
28:
	mov rdi, r15
	add rdi, 764
	call {vg_sha1_init_core}
	mov rdi, r15
	add rdi, 764
	mov esi, 0
	mov rdx, rbx
	mov rcx, rbp
	mov r8, r15
	call {vg_sha1_update_scratch_shani}
	mov rdi, r15
	add rdi, 764
	mov rsi, rbp
	mov rdx, r15
	add rdx, 888
	mov rcx, r15
	call {vg_sha1_finalize_scratch_shani}
	mov rdx, r15
	add rdx, 888
	mov ecx, 20
29:
	mov rdi, r12
	mov rsi, r13
	mov r8, r15
	call {vg_hmac_sha1_init_scratch_shani}
	mov rbx, QWORD PTR [r15+448]
	mov rbp, QWORD PTR [r15+456]
	mov r12, QWORD PTR [r15+464]
	mov r13, QWORD PTR [r15+472]
	mov r14, QWORD PTR [r15+480]
	mov r15, QWORD PTR [r15+488]
	mov r11d, 0
	mov QWORD PTR [rsp+8], r11
	mov QWORD PTR [rsp+16], r11
	mov QWORD PTR [rsp+24], r11
	mov QWORD PTR [rsp+32], r11
	mov QWORD PTR [rsp+40], r11
	mov QWORD PTR [rsp+48], r11
	mov QWORD PTR [rsp+56], r11
	mov QWORD PTR [rsp+64], r11
	mov QWORD PTR [rsp+72], r11
	mov QWORD PTR [rsp+80], r11
	mov QWORD PTR [rsp+88], r11
	mov QWORD PTR [rsp+96], r11
	mov QWORD PTR [rsp+104], r11
	mov QWORD PTR [rsp+112], r11
	mov QWORD PTR [rsp+120], r11
	mov QWORD PTR [rsp+128], r11
	mov QWORD PTR [rsp+136], r11
	mov QWORD PTR [rsp+144], r11
	mov QWORD PTR [rsp+152], r11
	mov QWORD PTR [rsp+160], r11
	mov QWORD PTR [rsp+168], r11
	mov QWORD PTR [rsp+176], r11
	mov QWORD PTR [rsp+184], r11
	mov QWORD PTR [rsp+192], r11
	mov QWORD PTR [rsp+200], r11
	mov QWORD PTR [rsp+208], r11
	mov QWORD PTR [rsp+216], r11
	mov QWORD PTR [rsp+224], r11
	mov QWORD PTR [rsp+232], r11
	mov QWORD PTR [rsp+240], r11
	mov QWORD PTR [rsp+248], r11
	mov QWORD PTR [rsp+256], r11
	mov QWORD PTR [rsp+264], r11
	mov QWORD PTR [rsp+272], r11
	mov QWORD PTR [rsp+280], r11
	mov QWORD PTR [rsp+288], r11
	mov QWORD PTR [rsp+296], r11
	mov QWORD PTR [rsp+304], r11
	mov QWORD PTR [rsp+312], r11
	mov QWORD PTR [rsp+320], r11
	mov QWORD PTR [rsp+328], r11
	mov QWORD PTR [rsp+336], r11
	mov QWORD PTR [rsp+344], r11
	mov QWORD PTR [rsp+352], r11
	mov QWORD PTR [rsp+360], r11
	mov QWORD PTR [rsp+368], r11
	mov QWORD PTR [rsp+376], r11
	mov QWORD PTR [rsp+384], r11
	mov QWORD PTR [rsp+392], r11
	mov QWORD PTR [rsp+400], r11
	mov QWORD PTR [rsp+408], r11
	mov QWORD PTR [rsp+416], r11
	mov QWORD PTR [rsp+424], r11
	mov QWORD PTR [rsp+432], r11
	mov QWORD PTR [rsp+440], r11
	mov QWORD PTR [rsp+448], r11
	mov QWORD PTR [rsp+456], r11
	mov QWORD PTR [rsp+464], r11
	mov QWORD PTR [rsp+472], r11
	mov QWORD PTR [rsp+480], r11
	mov QWORD PTR [rsp+488], r11
	mov QWORD PTR [rsp+496], r11
	mov QWORD PTR [rsp+504], r11
	mov QWORD PTR [rsp+512], r11
	mov QWORD PTR [rsp+520], r11
	mov QWORD PTR [rsp+528], r11
	mov QWORD PTR [rsp+536], r11
	mov QWORD PTR [rsp+544], r11
	mov QWORD PTR [rsp+552], r11
	mov QWORD PTR [rsp+560], r11
	mov QWORD PTR [rsp+568], r11
	mov QWORD PTR [rsp+576], r11
	mov QWORD PTR [rsp+584], r11
	mov QWORD PTR [rsp+592], r11
	mov QWORD PTR [rsp+600], r11
	mov QWORD PTR [rsp+608], r11
	mov QWORD PTR [rsp+616], r11
	mov QWORD PTR [rsp+624], r11
	mov QWORD PTR [rsp+632], r11
	mov QWORD PTR [rsp+640], r11
	mov QWORD PTR [rsp+648], r11
	mov QWORD PTR [rsp+656], r11
	mov QWORD PTR [rsp+664], r11
	mov QWORD PTR [rsp+672], r11
	mov QWORD PTR [rsp+680], r11
	mov QWORD PTR [rsp+688], r11
	mov QWORD PTR [rsp+696], r11
	mov QWORD PTR [rsp+704], r11
	mov QWORD PTR [rsp+712], r11
	mov QWORD PTR [rsp+720], r11
	mov QWORD PTR [rsp+728], r11
	mov QWORD PTR [rsp+736], r11
	mov QWORD PTR [rsp+744], r11
	mov QWORD PTR [rsp+752], r11
	mov QWORD PTR [rsp+760], r11
	mov QWORD PTR [rsp+768], r11
	mov QWORD PTR [rsp+776], r11
	mov QWORD PTR [rsp+784], r11
	mov QWORD PTR [rsp+792], r11
	mov QWORD PTR [rsp+800], r11
	mov QWORD PTR [rsp+808], r11
	mov QWORD PTR [rsp+816], r11
	mov QWORD PTR [rsp+824], r11
	mov QWORD PTR [rsp+832], r11
	mov QWORD PTR [rsp+840], r11
	mov QWORD PTR [rsp+848], r11
	mov QWORD PTR [rsp+856], r11
	mov QWORD PTR [rsp+864], r11
	mov QWORD PTR [rsp+872], r11
	mov QWORD PTR [rsp+880], r11
	mov QWORD PTR [rsp+888], r11
	mov QWORD PTR [rsp+896], r11
	mov QWORD PTR [rsp+904], r11
	mov QWORD PTR [rsp+912], r11
	mov QWORD PTR [rsp+920], r11
	mov QWORD PTR [rsp+928], r11
	mov QWORD PTR [rsp+936], r11
	mov QWORD PTR [rsp+944], r11
	mov QWORD PTR [rsp+952], r11
	mov QWORD PTR [rsp+960], r11
	mov QWORD PTR [rsp+968], r11
	mov QWORD PTR [rsp+976], r11
	mov QWORD PTR [rsp+984], r11
	mov QWORD PTR [rsp+992], r11
	mov QWORD PTR [rsp+1000], r11
	mov QWORD PTR [rsp+1008], r11
	mov QWORD PTR [rsp+1016], r11
	mov QWORD PTR [rsp+1024], r11
	mov QWORD PTR [rsp+1032], r11
	mov QWORD PTR [rsp+1040], r11
	mov QWORD PTR [rsp+1048], r11
	mov QWORD PTR [rsp+1056], r11
	mov QWORD PTR [rsp+1064], r11
	mov QWORD PTR [rsp+1072], r11
	mov QWORD PTR [rsp+1080], r11
	mov QWORD PTR [rsp+1088], r11
	mov QWORD PTR [rsp+1096], r11
	mov QWORD PTR [rsp+1104], r11
	mov QWORD PTR [rsp+1112], r11
	mov QWORD PTR [rsp+1120], r11
	lea rsp, [rsp+1128]
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	pxor xmm12, xmm12
	pxor xmm13, xmm13
	pxor xmm14, xmm14
	pxor xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-1152]
	movdqu XMMWORD PTR [rsp+1136], xmm0
	movdqu XMMWORD PTR [rsp+1120], xmm0
	movdqu XMMWORD PTR [rsp+1104], xmm0
	movdqu XMMWORD PTR [rsp+1088], xmm0
	movdqu XMMWORD PTR [rsp+1072], xmm0
	movdqu XMMWORD PTR [rsp+1056], xmm0
	movdqu XMMWORD PTR [rsp+1040], xmm0
	movdqu XMMWORD PTR [rsp+1024], xmm0
	movdqu XMMWORD PTR [rsp+1008], xmm0
	movdqu XMMWORD PTR [rsp+992], xmm0
	movdqu XMMWORD PTR [rsp+976], xmm0
	movdqu XMMWORD PTR [rsp+960], xmm0
	movdqu XMMWORD PTR [rsp+944], xmm0
	movdqu XMMWORD PTR [rsp+928], xmm0
	movdqu XMMWORD PTR [rsp+912], xmm0
	movdqu XMMWORD PTR [rsp+896], xmm0
	movdqu XMMWORD PTR [rsp+880], xmm0
	movdqu XMMWORD PTR [rsp+864], xmm0
	movdqu XMMWORD PTR [rsp+848], xmm0
	movdqu XMMWORD PTR [rsp+832], xmm0
	movdqu XMMWORD PTR [rsp+816], xmm0
	movdqu XMMWORD PTR [rsp+800], xmm0
	movdqu XMMWORD PTR [rsp+784], xmm0
	movdqu XMMWORD PTR [rsp+768], xmm0
	movdqu XMMWORD PTR [rsp+752], xmm0
	movdqu XMMWORD PTR [rsp+736], xmm0
	movdqu XMMWORD PTR [rsp+720], xmm0
	movdqu XMMWORD PTR [rsp+704], xmm0
	movdqu XMMWORD PTR [rsp+688], xmm0
	movdqu XMMWORD PTR [rsp+672], xmm0
	movdqu XMMWORD PTR [rsp+656], xmm0
	movdqu XMMWORD PTR [rsp+640], xmm0
	movdqu XMMWORD PTR [rsp+624], xmm0
	movdqu XMMWORD PTR [rsp+608], xmm0
	movdqu XMMWORD PTR [rsp+592], xmm0
	movdqu XMMWORD PTR [rsp+576], xmm0
	movdqu XMMWORD PTR [rsp+560], xmm0
	movdqu XMMWORD PTR [rsp+544], xmm0
	movdqu XMMWORD PTR [rsp+528], xmm0
	movdqu XMMWORD PTR [rsp+512], xmm0
	movdqu XMMWORD PTR [rsp+496], xmm0
	movdqu XMMWORD PTR [rsp+480], xmm0
	movdqu XMMWORD PTR [rsp+464], xmm0
	movdqu XMMWORD PTR [rsp+448], xmm0
	movdqu XMMWORD PTR [rsp+432], xmm0
	movdqu XMMWORD PTR [rsp+416], xmm0
	movdqu XMMWORD PTR [rsp+400], xmm0
	movdqu XMMWORD PTR [rsp+384], xmm0
	movdqu XMMWORD PTR [rsp+368], xmm0
	movdqu XMMWORD PTR [rsp+352], xmm0
	movdqu XMMWORD PTR [rsp+336], xmm0
	movdqu XMMWORD PTR [rsp+320], xmm0
	movdqu XMMWORD PTR [rsp+304], xmm0
	movdqu XMMWORD PTR [rsp+288], xmm0
	movdqu XMMWORD PTR [rsp+272], xmm0
	movdqu XMMWORD PTR [rsp+256], xmm0
	movdqu XMMWORD PTR [rsp+240], xmm0
	movdqu XMMWORD PTR [rsp+224], xmm0
	movdqu XMMWORD PTR [rsp+208], xmm0
	movdqu XMMWORD PTR [rsp+192], xmm0
	movdqu XMMWORD PTR [rsp+176], xmm0
	movdqu XMMWORD PTR [rsp+160], xmm0
	movdqu XMMWORD PTR [rsp+144], xmm0
	movdqu XMMWORD PTR [rsp+128], xmm0
	movdqu XMMWORD PTR [rsp+112], xmm0
	movdqu XMMWORD PTR [rsp+96], xmm0
	movdqu XMMWORD PTR [rsp+80], xmm0
	movdqu XMMWORD PTR [rsp+64], xmm0
	movdqu XMMWORD PTR [rsp+48], xmm0
	movdqu XMMWORD PTR [rsp+32], xmm0
	movdqu XMMWORD PTR [rsp+16], xmm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+1152]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	jmp 21b
	.p2align 6

vg_hmac_sha1_init_avx_bmi:
	cmp rcx, 65
	jae 20f
	lea rsp, [rsp-216]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+160], rbx
	mov QWORD PTR [r8+168], rbp
	mov QWORD PTR [r8+176], r12
	mov QWORD PTR [r8+184], r13
	mov QWORD PTR [r8+192], r14
	mov QWORD PTR [r8+200], r15
	mov rbx, rdi
	mov r12, rsi
	mov r15, r8
	mov rbp, rdx
	mov r13, rcx
	mov rdi, rbx
	call {vg_sha1_init_core}
	mov rdi, r12
	call {vg_sha1_init_core}
	movabs rax, 3906369333256140342
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqu XMMWORD PTR [rbx+20], xmm0
	movdqu XMMWORD PTR [rbx+36], xmm0
	movdqu XMMWORD PTR [rbx+52], xmm0
	movdqu XMMWORD PTR [rbx+68], xmm0
	mov r14d, 0
	mov rcx, r13
	shr rcx, 4
	test rcx, rcx
	je 22f
24:
	movdqu xmm1, XMMWORD PTR [rbp+r14*1]
	pxor xmm1, xmm0
	mov r10, r14
	and r10, 48
	movdqu XMMWORD PTR [rbx+r10*1+20], xmm1
	add r14, 16
	sub rcx, 1
	jne 24b
	jmp 23f
22:
23:
	cmp r14, r13
	je 25f
27:
	movzx eax, BYTE PTR [rbp+r14*1]
	xor eax, 54
	mov r10, r14
	and r10, 63
	mov BYTE PTR [rbx+r10*1+20], al
	add r14, 1
	cmp r14, r13
	jne 27b
	jmp 26f
25:
26:
	movabs rax, 7668058320836127338
	movq xmm1, rax
	punpcklqdq xmm1, xmm1
	movdqu xmm2, XMMWORD PTR [rbx+20]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [r12+20], xmm2
	movdqu xmm2, XMMWORD PTR [rbx+36]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [r12+36], xmm2
	movdqu xmm2, XMMWORD PTR [rbx+52]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [r12+52], xmm2
	movdqu xmm2, XMMWORD PTR [rbx+68]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [r12+68], xmm2
	mov rsi, rbx
	add rsi, 20
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha1_compress_avx_bmi}
	mov rbx, rdi
	mov r15, rcx
	mov rbx, r12
	mov rsi, r12
	add rsi, 20
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha1_compress_avx_bmi}
	mov rbx, rdi
	mov r15, rcx
	mov rbx, QWORD PTR [r15+160]
	mov rbp, QWORD PTR [r15+168]
	mov r12, QWORD PTR [r15+176]
	mov r13, QWORD PTR [r15+184]
	mov r14, QWORD PTR [r15+192]
	mov r15, QWORD PTR [r15+200]
	lea rsp, [rsp+216]
	vpxor xmm0, xmm0, xmm0
	vpxor xmm1, xmm1, xmm1
	vpxor xmm2, xmm2, xmm2
	vpxor xmm3, xmm3, xmm3
	vpxor xmm4, xmm4, xmm4
	vpxor xmm5, xmm5, xmm5
	vpxor xmm6, xmm6, xmm6
	vpxor xmm7, xmm7, xmm7
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	vpxor xmm11, xmm11, xmm11
	vpxor xmm12, xmm12, xmm12
	vpxor xmm13, xmm13, xmm13
	vpxor xmm14, xmm14, xmm14
	vpxor xmm15, xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-232]
	vmovdqu YMMWORD PTR [rsp+200], ymm0
	vmovdqu YMMWORD PTR [rsp+168], ymm0
	vmovdqu YMMWORD PTR [rsp+136], ymm0
	vmovdqu YMMWORD PTR [rsp+104], ymm0
	vmovdqu YMMWORD PTR [rsp+72], ymm0
	vmovdqu YMMWORD PTR [rsp+40], ymm0
	vmovdqu YMMWORD PTR [rsp+8], ymm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+232]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
21:
	ret
20:
	lea rsp, [rsp-1128]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+448], rbx
	mov QWORD PTR [r8+456], rbp
	mov QWORD PTR [r8+464], r12
	mov QWORD PTR [r8+472], r13
	mov QWORD PTR [r8+480], r14
	mov QWORD PTR [r8+488], r15
	mov r15, r8
	mov rbx, rdx
	mov rbp, rcx
	mov r12, rdi
	mov r13, rsi
	cmp rbp, 65
	jae 28f
	mov rdx, rbx
	mov rcx, rbp
	jmp 29f
28:
	mov rdi, r15
	add rdi, 764
	call {vg_sha1_init_core}
	mov rdi, r15
	add rdi, 764
	mov esi, 0
	mov rdx, rbx
	mov rcx, rbp
	mov r8, r15
	call {vg_sha1_update_scratch_avx_bmi}
	mov rdi, r15
	add rdi, 764
	mov rsi, rbp
	mov rdx, r15
	add rdx, 888
	mov rcx, r15
	call {vg_sha1_finalize_scratch_avx_bmi}
	mov rdx, r15
	add rdx, 888
	mov ecx, 20
29:
	mov rdi, r12
	mov rsi, r13
	mov r8, r15
	call {vg_hmac_sha1_init_scratch_avx_bmi}
	mov rbx, QWORD PTR [r15+448]
	mov rbp, QWORD PTR [r15+456]
	mov r12, QWORD PTR [r15+464]
	mov r13, QWORD PTR [r15+472]
	mov r14, QWORD PTR [r15+480]
	mov r15, QWORD PTR [r15+488]
	mov r11d, 0
	mov QWORD PTR [rsp+8], r11
	mov QWORD PTR [rsp+16], r11
	mov QWORD PTR [rsp+24], r11
	mov QWORD PTR [rsp+32], r11
	mov QWORD PTR [rsp+40], r11
	mov QWORD PTR [rsp+48], r11
	mov QWORD PTR [rsp+56], r11
	mov QWORD PTR [rsp+64], r11
	mov QWORD PTR [rsp+72], r11
	mov QWORD PTR [rsp+80], r11
	mov QWORD PTR [rsp+88], r11
	mov QWORD PTR [rsp+96], r11
	mov QWORD PTR [rsp+104], r11
	mov QWORD PTR [rsp+112], r11
	mov QWORD PTR [rsp+120], r11
	mov QWORD PTR [rsp+128], r11
	mov QWORD PTR [rsp+136], r11
	mov QWORD PTR [rsp+144], r11
	mov QWORD PTR [rsp+152], r11
	mov QWORD PTR [rsp+160], r11
	mov QWORD PTR [rsp+168], r11
	mov QWORD PTR [rsp+176], r11
	mov QWORD PTR [rsp+184], r11
	mov QWORD PTR [rsp+192], r11
	mov QWORD PTR [rsp+200], r11
	mov QWORD PTR [rsp+208], r11
	mov QWORD PTR [rsp+216], r11
	mov QWORD PTR [rsp+224], r11
	mov QWORD PTR [rsp+232], r11
	mov QWORD PTR [rsp+240], r11
	mov QWORD PTR [rsp+248], r11
	mov QWORD PTR [rsp+256], r11
	mov QWORD PTR [rsp+264], r11
	mov QWORD PTR [rsp+272], r11
	mov QWORD PTR [rsp+280], r11
	mov QWORD PTR [rsp+288], r11
	mov QWORD PTR [rsp+296], r11
	mov QWORD PTR [rsp+304], r11
	mov QWORD PTR [rsp+312], r11
	mov QWORD PTR [rsp+320], r11
	mov QWORD PTR [rsp+328], r11
	mov QWORD PTR [rsp+336], r11
	mov QWORD PTR [rsp+344], r11
	mov QWORD PTR [rsp+352], r11
	mov QWORD PTR [rsp+360], r11
	mov QWORD PTR [rsp+368], r11
	mov QWORD PTR [rsp+376], r11
	mov QWORD PTR [rsp+384], r11
	mov QWORD PTR [rsp+392], r11
	mov QWORD PTR [rsp+400], r11
	mov QWORD PTR [rsp+408], r11
	mov QWORD PTR [rsp+416], r11
	mov QWORD PTR [rsp+424], r11
	mov QWORD PTR [rsp+432], r11
	mov QWORD PTR [rsp+440], r11
	mov QWORD PTR [rsp+448], r11
	mov QWORD PTR [rsp+456], r11
	mov QWORD PTR [rsp+464], r11
	mov QWORD PTR [rsp+472], r11
	mov QWORD PTR [rsp+480], r11
	mov QWORD PTR [rsp+488], r11
	mov QWORD PTR [rsp+496], r11
	mov QWORD PTR [rsp+504], r11
	mov QWORD PTR [rsp+512], r11
	mov QWORD PTR [rsp+520], r11
	mov QWORD PTR [rsp+528], r11
	mov QWORD PTR [rsp+536], r11
	mov QWORD PTR [rsp+544], r11
	mov QWORD PTR [rsp+552], r11
	mov QWORD PTR [rsp+560], r11
	mov QWORD PTR [rsp+568], r11
	mov QWORD PTR [rsp+576], r11
	mov QWORD PTR [rsp+584], r11
	mov QWORD PTR [rsp+592], r11
	mov QWORD PTR [rsp+600], r11
	mov QWORD PTR [rsp+608], r11
	mov QWORD PTR [rsp+616], r11
	mov QWORD PTR [rsp+624], r11
	mov QWORD PTR [rsp+632], r11
	mov QWORD PTR [rsp+640], r11
	mov QWORD PTR [rsp+648], r11
	mov QWORD PTR [rsp+656], r11
	mov QWORD PTR [rsp+664], r11
	mov QWORD PTR [rsp+672], r11
	mov QWORD PTR [rsp+680], r11
	mov QWORD PTR [rsp+688], r11
	mov QWORD PTR [rsp+696], r11
	mov QWORD PTR [rsp+704], r11
	mov QWORD PTR [rsp+712], r11
	mov QWORD PTR [rsp+720], r11
	mov QWORD PTR [rsp+728], r11
	mov QWORD PTR [rsp+736], r11
	mov QWORD PTR [rsp+744], r11
	mov QWORD PTR [rsp+752], r11
	mov QWORD PTR [rsp+760], r11
	mov QWORD PTR [rsp+768], r11
	mov QWORD PTR [rsp+776], r11
	mov QWORD PTR [rsp+784], r11
	mov QWORD PTR [rsp+792], r11
	mov QWORD PTR [rsp+800], r11
	mov QWORD PTR [rsp+808], r11
	mov QWORD PTR [rsp+816], r11
	mov QWORD PTR [rsp+824], r11
	mov QWORD PTR [rsp+832], r11
	mov QWORD PTR [rsp+840], r11
	mov QWORD PTR [rsp+848], r11
	mov QWORD PTR [rsp+856], r11
	mov QWORD PTR [rsp+864], r11
	mov QWORD PTR [rsp+872], r11
	mov QWORD PTR [rsp+880], r11
	mov QWORD PTR [rsp+888], r11
	mov QWORD PTR [rsp+896], r11
	mov QWORD PTR [rsp+904], r11
	mov QWORD PTR [rsp+912], r11
	mov QWORD PTR [rsp+920], r11
	mov QWORD PTR [rsp+928], r11
	mov QWORD PTR [rsp+936], r11
	mov QWORD PTR [rsp+944], r11
	mov QWORD PTR [rsp+952], r11
	mov QWORD PTR [rsp+960], r11
	mov QWORD PTR [rsp+968], r11
	mov QWORD PTR [rsp+976], r11
	mov QWORD PTR [rsp+984], r11
	mov QWORD PTR [rsp+992], r11
	mov QWORD PTR [rsp+1000], r11
	mov QWORD PTR [rsp+1008], r11
	mov QWORD PTR [rsp+1016], r11
	mov QWORD PTR [rsp+1024], r11
	mov QWORD PTR [rsp+1032], r11
	mov QWORD PTR [rsp+1040], r11
	mov QWORD PTR [rsp+1048], r11
	mov QWORD PTR [rsp+1056], r11
	mov QWORD PTR [rsp+1064], r11
	mov QWORD PTR [rsp+1072], r11
	mov QWORD PTR [rsp+1080], r11
	mov QWORD PTR [rsp+1088], r11
	mov QWORD PTR [rsp+1096], r11
	mov QWORD PTR [rsp+1104], r11
	mov QWORD PTR [rsp+1112], r11
	mov QWORD PTR [rsp+1120], r11
	lea rsp, [rsp+1128]
	vpxor xmm0, xmm0, xmm0
	vpxor xmm1, xmm1, xmm1
	vpxor xmm2, xmm2, xmm2
	vpxor xmm3, xmm3, xmm3
	vpxor xmm4, xmm4, xmm4
	vpxor xmm5, xmm5, xmm5
	vpxor xmm6, xmm6, xmm6
	vpxor xmm7, xmm7, xmm7
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	vpxor xmm11, xmm11, xmm11
	vpxor xmm12, xmm12, xmm12
	vpxor xmm13, xmm13, xmm13
	vpxor xmm14, xmm14, xmm14
	vpxor xmm15, xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-1152]
	vmovdqu YMMWORD PTR [rsp+1120], ymm0
	vmovdqu YMMWORD PTR [rsp+1088], ymm0
	vmovdqu YMMWORD PTR [rsp+1056], ymm0
	vmovdqu YMMWORD PTR [rsp+1024], ymm0
	vmovdqu YMMWORD PTR [rsp+992], ymm0
	vmovdqu YMMWORD PTR [rsp+960], ymm0
	vmovdqu YMMWORD PTR [rsp+928], ymm0
	vmovdqu YMMWORD PTR [rsp+896], ymm0
	vmovdqu YMMWORD PTR [rsp+864], ymm0
	vmovdqu YMMWORD PTR [rsp+832], ymm0
	vmovdqu YMMWORD PTR [rsp+800], ymm0
	vmovdqu YMMWORD PTR [rsp+768], ymm0
	vmovdqu YMMWORD PTR [rsp+736], ymm0
	vmovdqu YMMWORD PTR [rsp+704], ymm0
	vmovdqu YMMWORD PTR [rsp+672], ymm0
	vmovdqu YMMWORD PTR [rsp+640], ymm0
	vmovdqu YMMWORD PTR [rsp+608], ymm0
	vmovdqu YMMWORD PTR [rsp+576], ymm0
	vmovdqu YMMWORD PTR [rsp+544], ymm0
	vmovdqu YMMWORD PTR [rsp+512], ymm0
	vmovdqu YMMWORD PTR [rsp+480], ymm0
	vmovdqu YMMWORD PTR [rsp+448], ymm0
	vmovdqu YMMWORD PTR [rsp+416], ymm0
	vmovdqu YMMWORD PTR [rsp+384], ymm0
	vmovdqu YMMWORD PTR [rsp+352], ymm0
	vmovdqu YMMWORD PTR [rsp+320], ymm0
	vmovdqu YMMWORD PTR [rsp+288], ymm0
	vmovdqu YMMWORD PTR [rsp+256], ymm0
	vmovdqu YMMWORD PTR [rsp+224], ymm0
	vmovdqu YMMWORD PTR [rsp+192], ymm0
	vmovdqu YMMWORD PTR [rsp+160], ymm0
	vmovdqu YMMWORD PTR [rsp+128], ymm0
	vmovdqu YMMWORD PTR [rsp+96], ymm0
	vmovdqu YMMWORD PTR [rsp+64], ymm0
	vmovdqu YMMWORD PTR [rsp+32], ymm0
	vmovdqu YMMWORD PTR [rsp], ymm0
	lea rsp, [rsp+1152]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	jmp 21b
	.p2align 6

vg_hmac_sha1_init:
	cmp rcx, 65
	jae 20f
	lea rsp, [rsp-216]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+160], rbx
	mov QWORD PTR [r8+168], rbp
	mov QWORD PTR [r8+176], r12
	mov QWORD PTR [r8+184], r13
	mov QWORD PTR [r8+192], r14
	mov QWORD PTR [r8+200], r15
	mov rbx, rdi
	mov r12, rsi
	mov r15, r8
	mov rbp, rdx
	mov r13, rcx
	mov rdi, rbx
	call {vg_sha1_init_core}
	mov rdi, r12
	call {vg_sha1_init_core}
	movabs rax, 3906369333256140342
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqu XMMWORD PTR [rbx+20], xmm0
	movdqu XMMWORD PTR [rbx+36], xmm0
	movdqu XMMWORD PTR [rbx+52], xmm0
	movdqu XMMWORD PTR [rbx+68], xmm0
	mov r14d, 0
	mov rcx, r13
	shr rcx, 4
	test rcx, rcx
	je 22f
24:
	movdqu xmm1, XMMWORD PTR [rbp+r14*1]
	pxor xmm1, xmm0
	mov r10, r14
	and r10, 48
	movdqu XMMWORD PTR [rbx+r10*1+20], xmm1
	add r14, 16
	sub rcx, 1
	jne 24b
	jmp 23f
22:
23:
	cmp r14, r13
	je 25f
27:
	movzx eax, BYTE PTR [rbp+r14*1]
	xor eax, 54
	mov r10, r14
	and r10, 63
	mov BYTE PTR [rbx+r10*1+20], al
	add r14, 1
	cmp r14, r13
	jne 27b
	jmp 26f
25:
26:
	movabs rax, 7668058320836127338
	movq xmm1, rax
	punpcklqdq xmm1, xmm1
	movdqu xmm2, XMMWORD PTR [rbx+20]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [r12+20], xmm2
	movdqu xmm2, XMMWORD PTR [rbx+36]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [r12+36], xmm2
	movdqu xmm2, XMMWORD PTR [rbx+52]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [r12+52], xmm2
	movdqu xmm2, XMMWORD PTR [rbx+68]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [r12+68], xmm2
	mov rsi, rbx
	add rsi, 20
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha1_compress}
	mov rbx, rdi
	mov r15, rcx
	mov rbx, r12
	mov rsi, r12
	add rsi, 20
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha1_compress}
	mov rbx, rdi
	mov r15, rcx
	mov rbx, QWORD PTR [r15+160]
	mov rbp, QWORD PTR [r15+168]
	mov r12, QWORD PTR [r15+176]
	mov r13, QWORD PTR [r15+184]
	mov r14, QWORD PTR [r15+192]
	mov r15, QWORD PTR [r15+200]
	lea rsp, [rsp+216]
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	pxor xmm12, xmm12
	pxor xmm13, xmm13
	pxor xmm14, xmm14
	pxor xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-232]
	movdqu XMMWORD PTR [rsp+216], xmm0
	movdqu XMMWORD PTR [rsp+200], xmm0
	movdqu XMMWORD PTR [rsp+184], xmm0
	movdqu XMMWORD PTR [rsp+168], xmm0
	movdqu XMMWORD PTR [rsp+152], xmm0
	movdqu XMMWORD PTR [rsp+136], xmm0
	movdqu XMMWORD PTR [rsp+120], xmm0
	movdqu XMMWORD PTR [rsp+104], xmm0
	movdqu XMMWORD PTR [rsp+88], xmm0
	movdqu XMMWORD PTR [rsp+72], xmm0
	movdqu XMMWORD PTR [rsp+56], xmm0
	movdqu XMMWORD PTR [rsp+40], xmm0
	movdqu XMMWORD PTR [rsp+24], xmm0
	movdqu XMMWORD PTR [rsp+8], xmm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+232]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
21:
	ret
20:
	lea rsp, [rsp-1128]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+448], rbx
	mov QWORD PTR [r8+456], rbp
	mov QWORD PTR [r8+464], r12
	mov QWORD PTR [r8+472], r13
	mov QWORD PTR [r8+480], r14
	mov QWORD PTR [r8+488], r15
	mov r15, r8
	mov rbx, rdx
	mov rbp, rcx
	mov r12, rdi
	mov r13, rsi
	cmp rbp, 65
	jae 28f
	mov rdx, rbx
	mov rcx, rbp
	jmp 29f
28:
	mov rdi, r15
	add rdi, 764
	call {vg_sha1_init_core}
	mov rdi, r15
	add rdi, 764
	mov esi, 0
	mov rdx, rbx
	mov rcx, rbp
	mov r8, r15
	call {vg_sha1_update_scratch}
	mov rdi, r15
	add rdi, 764
	mov rsi, rbp
	mov rdx, r15
	add rdx, 888
	mov rcx, r15
	call {vg_sha1_finalize_scratch}
	mov rdx, r15
	add rdx, 888
	mov ecx, 20
29:
	mov rdi, r12
	mov rsi, r13
	mov r8, r15
	call {vg_hmac_sha1_init_scratch}
	mov rbx, QWORD PTR [r15+448]
	mov rbp, QWORD PTR [r15+456]
	mov r12, QWORD PTR [r15+464]
	mov r13, QWORD PTR [r15+472]
	mov r14, QWORD PTR [r15+480]
	mov r15, QWORD PTR [r15+488]
	mov r11d, 0
	mov QWORD PTR [rsp+8], r11
	mov QWORD PTR [rsp+16], r11
	mov QWORD PTR [rsp+24], r11
	mov QWORD PTR [rsp+32], r11
	mov QWORD PTR [rsp+40], r11
	mov QWORD PTR [rsp+48], r11
	mov QWORD PTR [rsp+56], r11
	mov QWORD PTR [rsp+64], r11
	mov QWORD PTR [rsp+72], r11
	mov QWORD PTR [rsp+80], r11
	mov QWORD PTR [rsp+88], r11
	mov QWORD PTR [rsp+96], r11
	mov QWORD PTR [rsp+104], r11
	mov QWORD PTR [rsp+112], r11
	mov QWORD PTR [rsp+120], r11
	mov QWORD PTR [rsp+128], r11
	mov QWORD PTR [rsp+136], r11
	mov QWORD PTR [rsp+144], r11
	mov QWORD PTR [rsp+152], r11
	mov QWORD PTR [rsp+160], r11
	mov QWORD PTR [rsp+168], r11
	mov QWORD PTR [rsp+176], r11
	mov QWORD PTR [rsp+184], r11
	mov QWORD PTR [rsp+192], r11
	mov QWORD PTR [rsp+200], r11
	mov QWORD PTR [rsp+208], r11
	mov QWORD PTR [rsp+216], r11
	mov QWORD PTR [rsp+224], r11
	mov QWORD PTR [rsp+232], r11
	mov QWORD PTR [rsp+240], r11
	mov QWORD PTR [rsp+248], r11
	mov QWORD PTR [rsp+256], r11
	mov QWORD PTR [rsp+264], r11
	mov QWORD PTR [rsp+272], r11
	mov QWORD PTR [rsp+280], r11
	mov QWORD PTR [rsp+288], r11
	mov QWORD PTR [rsp+296], r11
	mov QWORD PTR [rsp+304], r11
	mov QWORD PTR [rsp+312], r11
	mov QWORD PTR [rsp+320], r11
	mov QWORD PTR [rsp+328], r11
	mov QWORD PTR [rsp+336], r11
	mov QWORD PTR [rsp+344], r11
	mov QWORD PTR [rsp+352], r11
	mov QWORD PTR [rsp+360], r11
	mov QWORD PTR [rsp+368], r11
	mov QWORD PTR [rsp+376], r11
	mov QWORD PTR [rsp+384], r11
	mov QWORD PTR [rsp+392], r11
	mov QWORD PTR [rsp+400], r11
	mov QWORD PTR [rsp+408], r11
	mov QWORD PTR [rsp+416], r11
	mov QWORD PTR [rsp+424], r11
	mov QWORD PTR [rsp+432], r11
	mov QWORD PTR [rsp+440], r11
	mov QWORD PTR [rsp+448], r11
	mov QWORD PTR [rsp+456], r11
	mov QWORD PTR [rsp+464], r11
	mov QWORD PTR [rsp+472], r11
	mov QWORD PTR [rsp+480], r11
	mov QWORD PTR [rsp+488], r11
	mov QWORD PTR [rsp+496], r11
	mov QWORD PTR [rsp+504], r11
	mov QWORD PTR [rsp+512], r11
	mov QWORD PTR [rsp+520], r11
	mov QWORD PTR [rsp+528], r11
	mov QWORD PTR [rsp+536], r11
	mov QWORD PTR [rsp+544], r11
	mov QWORD PTR [rsp+552], r11
	mov QWORD PTR [rsp+560], r11
	mov QWORD PTR [rsp+568], r11
	mov QWORD PTR [rsp+576], r11
	mov QWORD PTR [rsp+584], r11
	mov QWORD PTR [rsp+592], r11
	mov QWORD PTR [rsp+600], r11
	mov QWORD PTR [rsp+608], r11
	mov QWORD PTR [rsp+616], r11
	mov QWORD PTR [rsp+624], r11
	mov QWORD PTR [rsp+632], r11
	mov QWORD PTR [rsp+640], r11
	mov QWORD PTR [rsp+648], r11
	mov QWORD PTR [rsp+656], r11
	mov QWORD PTR [rsp+664], r11
	mov QWORD PTR [rsp+672], r11
	mov QWORD PTR [rsp+680], r11
	mov QWORD PTR [rsp+688], r11
	mov QWORD PTR [rsp+696], r11
	mov QWORD PTR [rsp+704], r11
	mov QWORD PTR [rsp+712], r11
	mov QWORD PTR [rsp+720], r11
	mov QWORD PTR [rsp+728], r11
	mov QWORD PTR [rsp+736], r11
	mov QWORD PTR [rsp+744], r11
	mov QWORD PTR [rsp+752], r11
	mov QWORD PTR [rsp+760], r11
	mov QWORD PTR [rsp+768], r11
	mov QWORD PTR [rsp+776], r11
	mov QWORD PTR [rsp+784], r11
	mov QWORD PTR [rsp+792], r11
	mov QWORD PTR [rsp+800], r11
	mov QWORD PTR [rsp+808], r11
	mov QWORD PTR [rsp+816], r11
	mov QWORD PTR [rsp+824], r11
	mov QWORD PTR [rsp+832], r11
	mov QWORD PTR [rsp+840], r11
	mov QWORD PTR [rsp+848], r11
	mov QWORD PTR [rsp+856], r11
	mov QWORD PTR [rsp+864], r11
	mov QWORD PTR [rsp+872], r11
	mov QWORD PTR [rsp+880], r11
	mov QWORD PTR [rsp+888], r11
	mov QWORD PTR [rsp+896], r11
	mov QWORD PTR [rsp+904], r11
	mov QWORD PTR [rsp+912], r11
	mov QWORD PTR [rsp+920], r11
	mov QWORD PTR [rsp+928], r11
	mov QWORD PTR [rsp+936], r11
	mov QWORD PTR [rsp+944], r11
	mov QWORD PTR [rsp+952], r11
	mov QWORD PTR [rsp+960], r11
	mov QWORD PTR [rsp+968], r11
	mov QWORD PTR [rsp+976], r11
	mov QWORD PTR [rsp+984], r11
	mov QWORD PTR [rsp+992], r11
	mov QWORD PTR [rsp+1000], r11
	mov QWORD PTR [rsp+1008], r11
	mov QWORD PTR [rsp+1016], r11
	mov QWORD PTR [rsp+1024], r11
	mov QWORD PTR [rsp+1032], r11
	mov QWORD PTR [rsp+1040], r11
	mov QWORD PTR [rsp+1048], r11
	mov QWORD PTR [rsp+1056], r11
	mov QWORD PTR [rsp+1064], r11
	mov QWORD PTR [rsp+1072], r11
	mov QWORD PTR [rsp+1080], r11
	mov QWORD PTR [rsp+1088], r11
	mov QWORD PTR [rsp+1096], r11
	mov QWORD PTR [rsp+1104], r11
	mov QWORD PTR [rsp+1112], r11
	mov QWORD PTR [rsp+1120], r11
	lea rsp, [rsp+1128]
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	pxor xmm12, xmm12
	pxor xmm13, xmm13
	pxor xmm14, xmm14
	pxor xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-1152]
	movdqu XMMWORD PTR [rsp+1136], xmm0
	movdqu XMMWORD PTR [rsp+1120], xmm0
	movdqu XMMWORD PTR [rsp+1104], xmm0
	movdqu XMMWORD PTR [rsp+1088], xmm0
	movdqu XMMWORD PTR [rsp+1072], xmm0
	movdqu XMMWORD PTR [rsp+1056], xmm0
	movdqu XMMWORD PTR [rsp+1040], xmm0
	movdqu XMMWORD PTR [rsp+1024], xmm0
	movdqu XMMWORD PTR [rsp+1008], xmm0
	movdqu XMMWORD PTR [rsp+992], xmm0
	movdqu XMMWORD PTR [rsp+976], xmm0
	movdqu XMMWORD PTR [rsp+960], xmm0
	movdqu XMMWORD PTR [rsp+944], xmm0
	movdqu XMMWORD PTR [rsp+928], xmm0
	movdqu XMMWORD PTR [rsp+912], xmm0
	movdqu XMMWORD PTR [rsp+896], xmm0
	movdqu XMMWORD PTR [rsp+880], xmm0
	movdqu XMMWORD PTR [rsp+864], xmm0
	movdqu XMMWORD PTR [rsp+848], xmm0
	movdqu XMMWORD PTR [rsp+832], xmm0
	movdqu XMMWORD PTR [rsp+816], xmm0
	movdqu XMMWORD PTR [rsp+800], xmm0
	movdqu XMMWORD PTR [rsp+784], xmm0
	movdqu XMMWORD PTR [rsp+768], xmm0
	movdqu XMMWORD PTR [rsp+752], xmm0
	movdqu XMMWORD PTR [rsp+736], xmm0
	movdqu XMMWORD PTR [rsp+720], xmm0
	movdqu XMMWORD PTR [rsp+704], xmm0
	movdqu XMMWORD PTR [rsp+688], xmm0
	movdqu XMMWORD PTR [rsp+672], xmm0
	movdqu XMMWORD PTR [rsp+656], xmm0
	movdqu XMMWORD PTR [rsp+640], xmm0
	movdqu XMMWORD PTR [rsp+624], xmm0
	movdqu XMMWORD PTR [rsp+608], xmm0
	movdqu XMMWORD PTR [rsp+592], xmm0
	movdqu XMMWORD PTR [rsp+576], xmm0
	movdqu XMMWORD PTR [rsp+560], xmm0
	movdqu XMMWORD PTR [rsp+544], xmm0
	movdqu XMMWORD PTR [rsp+528], xmm0
	movdqu XMMWORD PTR [rsp+512], xmm0
	movdqu XMMWORD PTR [rsp+496], xmm0
	movdqu XMMWORD PTR [rsp+480], xmm0
	movdqu XMMWORD PTR [rsp+464], xmm0
	movdqu XMMWORD PTR [rsp+448], xmm0
	movdqu XMMWORD PTR [rsp+432], xmm0
	movdqu XMMWORD PTR [rsp+416], xmm0
	movdqu XMMWORD PTR [rsp+400], xmm0
	movdqu XMMWORD PTR [rsp+384], xmm0
	movdqu XMMWORD PTR [rsp+368], xmm0
	movdqu XMMWORD PTR [rsp+352], xmm0
	movdqu XMMWORD PTR [rsp+336], xmm0
	movdqu XMMWORD PTR [rsp+320], xmm0
	movdqu XMMWORD PTR [rsp+304], xmm0
	movdqu XMMWORD PTR [rsp+288], xmm0
	movdqu XMMWORD PTR [rsp+272], xmm0
	movdqu XMMWORD PTR [rsp+256], xmm0
	movdqu XMMWORD PTR [rsp+240], xmm0
	movdqu XMMWORD PTR [rsp+224], xmm0
	movdqu XMMWORD PTR [rsp+208], xmm0
	movdqu XMMWORD PTR [rsp+192], xmm0
	movdqu XMMWORD PTR [rsp+176], xmm0
	movdqu XMMWORD PTR [rsp+160], xmm0
	movdqu XMMWORD PTR [rsp+144], xmm0
	movdqu XMMWORD PTR [rsp+128], xmm0
	movdqu XMMWORD PTR [rsp+112], xmm0
	movdqu XMMWORD PTR [rsp+96], xmm0
	movdqu XMMWORD PTR [rsp+80], xmm0
	movdqu XMMWORD PTR [rsp+64], xmm0
	movdqu XMMWORD PTR [rsp+48], xmm0
	movdqu XMMWORD PTR [rsp+32], xmm0
	movdqu XMMWORD PTR [rsp+16], xmm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+1152]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	jmp 21b
	.p2align 6

vg_hmac_sha1_finalize_shani:
	lea rsp, [rsp-456]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+160], rbx
	mov QWORD PTR [r8+168], rbp
	mov QWORD PTR [r8+176], r12
	mov QWORD PTR [r8+184], r13
	mov QWORD PTR [r8+192], r14
	mov QWORD PTR [r8+200], r15
	mov rbx, rdi
	mov r12, rsi
	mov r13, rcx
	mov r15, r8
	mov rsi, rdx
	mov rdx, r15
	add rdx, 208
	mov rcx, r15
	call {vg_sha1_finalize_scratch_shani}
	mov eax, DWORD PTR [r12]
	mov DWORD PTR [rbx], eax
	mov eax, DWORD PTR [r12+4]
	mov DWORD PTR [rbx+4], eax
	mov eax, DWORD PTR [r12+8]
	mov DWORD PTR [rbx+8], eax
	mov eax, DWORD PTR [r12+12]
	mov DWORD PTR [rbx+12], eax
	mov eax, DWORD PTR [r12+16]
	mov DWORD PTR [rbx+16], eax
	mov eax, DWORD PTR [r15+208]
	mov DWORD PTR [rbx+20], eax
	mov eax, DWORD PTR [r15+212]
	mov DWORD PTR [rbx+24], eax
	mov eax, DWORD PTR [r15+216]
	mov DWORD PTR [rbx+28], eax
	mov eax, DWORD PTR [r15+220]
	mov DWORD PTR [rbx+32], eax
	mov eax, DWORD PTR [r15+224]
	mov DWORD PTR [rbx+36], eax
	mov rbp, rbx
	add rbp, 20
	mov eax, 128
	mov DWORD PTR [rbp+20], eax
	mov eax, 0
	mov DWORD PTR [rbp+24], eax
	mov DWORD PTR [rbp+28], eax
	mov DWORD PTR [rbp+32], eax
	mov DWORD PTR [rbp+36], eax
	mov DWORD PTR [rbp+40], eax
	mov DWORD PTR [rbp+44], eax
	mov DWORD PTR [rbp+48], eax
	mov DWORD PTR [rbp+52], eax
	mov r12d, 84
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+76], rax
	mov rsi, rbp
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha1_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov rbp, r13
	mov eax, DWORD PTR [rbx]
	bswap eax
	mov DWORD PTR [rbp], eax
	mov eax, DWORD PTR [rbx+4]
	bswap eax
	mov DWORD PTR [rbp+4], eax
	mov eax, DWORD PTR [rbx+8]
	bswap eax
	mov DWORD PTR [rbp+8], eax
	mov eax, DWORD PTR [rbx+12]
	bswap eax
	mov DWORD PTR [rbp+12], eax
	mov eax, DWORD PTR [rbx+16]
	bswap eax
	mov DWORD PTR [rbp+16], eax
	mov rbx, QWORD PTR [r15+160]
	mov rbp, QWORD PTR [r15+168]
	mov r12, QWORD PTR [r15+176]
	mov r13, QWORD PTR [r15+184]
	mov r14, QWORD PTR [r15+192]
	mov r15, QWORD PTR [r15+200]
	lea rsp, [rsp+456]
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	pxor xmm12, xmm12
	pxor xmm13, xmm13
	pxor xmm14, xmm14
	pxor xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-472]
	movdqu XMMWORD PTR [rsp+248], xmm0
	movdqu XMMWORD PTR [rsp+232], xmm0
	lea rsp, [rsp+472]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	ret
	.p2align 6

vg_hmac_sha1_finalize_avx_bmi:
	lea rsp, [rsp-456]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+160], rbx
	mov QWORD PTR [r8+168], rbp
	mov QWORD PTR [r8+176], r12
	mov QWORD PTR [r8+184], r13
	mov QWORD PTR [r8+192], r14
	mov QWORD PTR [r8+200], r15
	mov rbx, rdi
	mov r12, rsi
	mov r13, rcx
	mov r15, r8
	mov rsi, rdx
	mov rdx, r15
	add rdx, 208
	mov rcx, r15
	call {vg_sha1_finalize_scratch_avx_bmi}
	mov eax, DWORD PTR [r12]
	mov DWORD PTR [rbx], eax
	mov eax, DWORD PTR [r12+4]
	mov DWORD PTR [rbx+4], eax
	mov eax, DWORD PTR [r12+8]
	mov DWORD PTR [rbx+8], eax
	mov eax, DWORD PTR [r12+12]
	mov DWORD PTR [rbx+12], eax
	mov eax, DWORD PTR [r12+16]
	mov DWORD PTR [rbx+16], eax
	mov eax, DWORD PTR [r15+208]
	mov DWORD PTR [rbx+20], eax
	mov eax, DWORD PTR [r15+212]
	mov DWORD PTR [rbx+24], eax
	mov eax, DWORD PTR [r15+216]
	mov DWORD PTR [rbx+28], eax
	mov eax, DWORD PTR [r15+220]
	mov DWORD PTR [rbx+32], eax
	mov eax, DWORD PTR [r15+224]
	mov DWORD PTR [rbx+36], eax
	mov rbp, rbx
	add rbp, 20
	mov eax, 128
	mov DWORD PTR [rbp+20], eax
	mov eax, 0
	mov DWORD PTR [rbp+24], eax
	mov DWORD PTR [rbp+28], eax
	mov DWORD PTR [rbp+32], eax
	mov DWORD PTR [rbp+36], eax
	mov DWORD PTR [rbp+40], eax
	mov DWORD PTR [rbp+44], eax
	mov DWORD PTR [rbp+48], eax
	mov DWORD PTR [rbp+52], eax
	mov r12d, 84
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+76], rax
	mov rsi, rbp
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha1_compress_avx_bmi}
	mov rbx, rdi
	mov r15, rcx
	mov rbp, r13
	mov eax, DWORD PTR [rbx]
	bswap eax
	mov DWORD PTR [rbp], eax
	mov eax, DWORD PTR [rbx+4]
	bswap eax
	mov DWORD PTR [rbp+4], eax
	mov eax, DWORD PTR [rbx+8]
	bswap eax
	mov DWORD PTR [rbp+8], eax
	mov eax, DWORD PTR [rbx+12]
	bswap eax
	mov DWORD PTR [rbp+12], eax
	mov eax, DWORD PTR [rbx+16]
	bswap eax
	mov DWORD PTR [rbp+16], eax
	mov rbx, QWORD PTR [r15+160]
	mov rbp, QWORD PTR [r15+168]
	mov r12, QWORD PTR [r15+176]
	mov r13, QWORD PTR [r15+184]
	mov r14, QWORD PTR [r15+192]
	mov r15, QWORD PTR [r15+200]
	lea rsp, [rsp+456]
	vpxor xmm0, xmm0, xmm0
	vpxor xmm1, xmm1, xmm1
	vpxor xmm2, xmm2, xmm2
	vpxor xmm3, xmm3, xmm3
	vpxor xmm4, xmm4, xmm4
	vpxor xmm5, xmm5, xmm5
	vpxor xmm6, xmm6, xmm6
	vpxor xmm7, xmm7, xmm7
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	vpxor xmm11, xmm11, xmm11
	vpxor xmm12, xmm12, xmm12
	vpxor xmm13, xmm13, xmm13
	vpxor xmm14, xmm14, xmm14
	vpxor xmm15, xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-472]
	vmovdqu YMMWORD PTR [rsp+232], ymm0
	vmovdqu YMMWORD PTR [rsp+56], ymm0
	vmovdqu YMMWORD PTR [rsp+24], ymm0
	movdqu XMMWORD PTR [rsp+8], xmm0
	lea rsp, [rsp+472]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	ret
	.p2align 6

vg_hmac_sha1_finalize:
	lea rsp, [rsp-456]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+160], rbx
	mov QWORD PTR [r8+168], rbp
	mov QWORD PTR [r8+176], r12
	mov QWORD PTR [r8+184], r13
	mov QWORD PTR [r8+192], r14
	mov QWORD PTR [r8+200], r15
	mov rbx, rdi
	mov r12, rsi
	mov r13, rcx
	mov r15, r8
	mov rsi, rdx
	mov rdx, r15
	add rdx, 208
	mov rcx, r15
	call {vg_sha1_finalize_scratch}
	mov eax, DWORD PTR [r12]
	mov DWORD PTR [rbx], eax
	mov eax, DWORD PTR [r12+4]
	mov DWORD PTR [rbx+4], eax
	mov eax, DWORD PTR [r12+8]
	mov DWORD PTR [rbx+8], eax
	mov eax, DWORD PTR [r12+12]
	mov DWORD PTR [rbx+12], eax
	mov eax, DWORD PTR [r12+16]
	mov DWORD PTR [rbx+16], eax
	mov eax, DWORD PTR [r15+208]
	mov DWORD PTR [rbx+20], eax
	mov eax, DWORD PTR [r15+212]
	mov DWORD PTR [rbx+24], eax
	mov eax, DWORD PTR [r15+216]
	mov DWORD PTR [rbx+28], eax
	mov eax, DWORD PTR [r15+220]
	mov DWORD PTR [rbx+32], eax
	mov eax, DWORD PTR [r15+224]
	mov DWORD PTR [rbx+36], eax
	mov rbp, rbx
	add rbp, 20
	mov eax, 128
	mov DWORD PTR [rbp+20], eax
	mov eax, 0
	mov DWORD PTR [rbp+24], eax
	mov DWORD PTR [rbp+28], eax
	mov DWORD PTR [rbp+32], eax
	mov DWORD PTR [rbp+36], eax
	mov DWORD PTR [rbp+40], eax
	mov DWORD PTR [rbp+44], eax
	mov DWORD PTR [rbp+48], eax
	mov DWORD PTR [rbp+52], eax
	mov r12d, 84
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+76], rax
	mov rsi, rbp
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha1_compress}
	mov rbx, rdi
	mov r15, rcx
	mov rbp, r13
	mov eax, DWORD PTR [rbx]
	bswap eax
	mov DWORD PTR [rbp], eax
	mov eax, DWORD PTR [rbx+4]
	bswap eax
	mov DWORD PTR [rbp+4], eax
	mov eax, DWORD PTR [rbx+8]
	bswap eax
	mov DWORD PTR [rbp+8], eax
	mov eax, DWORD PTR [rbx+12]
	bswap eax
	mov DWORD PTR [rbp+12], eax
	mov eax, DWORD PTR [rbx+16]
	bswap eax
	mov DWORD PTR [rbp+16], eax
	mov rbx, QWORD PTR [r15+160]
	mov rbp, QWORD PTR [r15+168]
	mov r12, QWORD PTR [r15+176]
	mov r13, QWORD PTR [r15+184]
	mov r14, QWORD PTR [r15+192]
	mov r15, QWORD PTR [r15+200]
	lea rsp, [rsp+456]
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	pxor xmm12, xmm12
	pxor xmm13, xmm13
	pxor xmm14, xmm14
	pxor xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-472]
	movdqu XMMWORD PTR [rsp+248], xmm0
	movdqu XMMWORD PTR [rsp+232], xmm0
	movdqu XMMWORD PTR [rsp+72], xmm0
	movdqu XMMWORD PTR [rsp+56], xmm0
	movdqu XMMWORD PTR [rsp+40], xmm0
	movdqu XMMWORD PTR [rsp+24], xmm0
	movdqu XMMWORD PTR [rsp+8], xmm0
	lea rsp, [rsp+472]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	ret
	.p2align 6
