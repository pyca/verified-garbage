// The functions of `src/hmac_sha224.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_sha224_init_shani:
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
	call {vg_sha224_init_core}
	mov rdi, r12
	call {vg_sha224_init_core}
	movabs rax, 3906369333256140342
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
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
	movdqu XMMWORD PTR [rbx+r10*1+32], xmm1
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
	mov BYTE PTR [rbx+r10*1+32], al
	add r14, 1
	cmp r14, r13
	jne 27b
	jmp 26f
25:
26:
	movabs rax, 7668058320836127338
	movq xmm1, rax
	punpcklqdq xmm1, xmm1
	movdqu xmm2, XMMWORD PTR [rbx+32]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [r12+32], xmm2
	movdqu xmm2, XMMWORD PTR [rbx+48]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [r12+48], xmm2
	movdqu xmm2, XMMWORD PTR [rbx+64]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [r12+64], xmm2
	movdqu xmm2, XMMWORD PTR [rbx+80]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [r12+80], xmm2
	mov rsi, rbx
	add rsi, 32
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov rbx, r12
	mov rsi, r12
	add rsi, 32
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress_shani}
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
	lea rsp, [rsp-8]
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp-112]
	movdqu XMMWORD PTR [rsp+96], xmm0
	movdqu XMMWORD PTR [rsp+80], xmm0
	movdqu XMMWORD PTR [rsp+64], xmm0
	movdqu XMMWORD PTR [rsp+48], xmm0
	movdqu XMMWORD PTR [rsp+32], xmm0
	movdqu XMMWORD PTR [rsp+16], xmm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+112]
	lea rsp, [rsp+8]
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
	lea rsp, [rsp-920]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+144], rbx
	mov QWORD PTR [r8+152], rbp
	mov QWORD PTR [r8+160], r12
	mov QWORD PTR [r8+168], r13
	mov QWORD PTR [r8+176], r14
	mov QWORD PTR [r8+184], r15
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
	add rdi, 496
	call {vg_sha224_init_core}
	mov rdi, r15
	add rdi, 496
	mov esi, 0
	mov rdx, rbx
	mov rcx, rbp
	mov r8, r15
	call {vg_sha256_update_scratch_shani}
	mov rdi, r15
	add rdi, 496
	mov rsi, rbp
	mov rdx, r15
	add rdx, 648
	mov rcx, r15
	call {vg_sha256_finalize_scratch_shani}
	mov rdx, r15
	add rdx, 648
	mov ecx, 28
29:
	mov rdi, r12
	mov rsi, r13
	mov r8, r15
	call {vg_hmac_sha224_init_scratch_shani}
	mov rbx, QWORD PTR [r15+144]
	mov rbp, QWORD PTR [r15+152]
	mov r12, QWORD PTR [r15+160]
	mov r13, QWORD PTR [r15+168]
	mov r14, QWORD PTR [r15+176]
	mov r15, QWORD PTR [r15+184]
	pxor xmm0, xmm0
	mov r11d, 0
	movdqu XMMWORD PTR [rsp+8], xmm0
	movdqu XMMWORD PTR [rsp+24], xmm0
	movdqu XMMWORD PTR [rsp+40], xmm0
	movdqu XMMWORD PTR [rsp+56], xmm0
	movdqu XMMWORD PTR [rsp+72], xmm0
	movdqu XMMWORD PTR [rsp+88], xmm0
	movdqu XMMWORD PTR [rsp+104], xmm0
	movdqu XMMWORD PTR [rsp+120], xmm0
	movdqu XMMWORD PTR [rsp+136], xmm0
	movdqu XMMWORD PTR [rsp+152], xmm0
	movdqu XMMWORD PTR [rsp+168], xmm0
	movdqu XMMWORD PTR [rsp+184], xmm0
	movdqu XMMWORD PTR [rsp+200], xmm0
	movdqu XMMWORD PTR [rsp+216], xmm0
	movdqu XMMWORD PTR [rsp+232], xmm0
	movdqu XMMWORD PTR [rsp+248], xmm0
	movdqu XMMWORD PTR [rsp+264], xmm0
	movdqu XMMWORD PTR [rsp+280], xmm0
	movdqu XMMWORD PTR [rsp+296], xmm0
	movdqu XMMWORD PTR [rsp+312], xmm0
	movdqu XMMWORD PTR [rsp+328], xmm0
	movdqu XMMWORD PTR [rsp+344], xmm0
	movdqu XMMWORD PTR [rsp+360], xmm0
	movdqu XMMWORD PTR [rsp+376], xmm0
	movdqu XMMWORD PTR [rsp+392], xmm0
	movdqu XMMWORD PTR [rsp+408], xmm0
	movdqu XMMWORD PTR [rsp+424], xmm0
	movdqu XMMWORD PTR [rsp+440], xmm0
	movdqu XMMWORD PTR [rsp+456], xmm0
	movdqu XMMWORD PTR [rsp+472], xmm0
	movdqu XMMWORD PTR [rsp+488], xmm0
	movdqu XMMWORD PTR [rsp+504], xmm0
	movdqu XMMWORD PTR [rsp+520], xmm0
	movdqu XMMWORD PTR [rsp+536], xmm0
	movdqu XMMWORD PTR [rsp+552], xmm0
	movdqu XMMWORD PTR [rsp+568], xmm0
	movdqu XMMWORD PTR [rsp+584], xmm0
	movdqu XMMWORD PTR [rsp+600], xmm0
	movdqu XMMWORD PTR [rsp+616], xmm0
	movdqu XMMWORD PTR [rsp+632], xmm0
	movdqu XMMWORD PTR [rsp+648], xmm0
	movdqu XMMWORD PTR [rsp+664], xmm0
	movdqu XMMWORD PTR [rsp+680], xmm0
	movdqu XMMWORD PTR [rsp+696], xmm0
	movdqu XMMWORD PTR [rsp+712], xmm0
	movdqu XMMWORD PTR [rsp+728], xmm0
	movdqu XMMWORD PTR [rsp+744], xmm0
	movdqu XMMWORD PTR [rsp+760], xmm0
	movdqu XMMWORD PTR [rsp+776], xmm0
	movdqu XMMWORD PTR [rsp+792], xmm0
	movdqu XMMWORD PTR [rsp+808], xmm0
	movdqu XMMWORD PTR [rsp+824], xmm0
	movdqu XMMWORD PTR [rsp+840], xmm0
	movdqu XMMWORD PTR [rsp+856], xmm0
	movdqu XMMWORD PTR [rsp+872], xmm0
	movdqu XMMWORD PTR [rsp+888], xmm0
	movdqu XMMWORD PTR [rsp+904], xmm0
	lea rsp, [rsp+920]
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
	lea rsp, [rsp-8]
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp-936]
	movdqu XMMWORD PTR [rsp+920], xmm0
	movdqu XMMWORD PTR [rsp+904], xmm0
	movdqu XMMWORD PTR [rsp+888], xmm0
	movdqu XMMWORD PTR [rsp+872], xmm0
	movdqu XMMWORD PTR [rsp+856], xmm0
	movdqu XMMWORD PTR [rsp+840], xmm0
	movdqu XMMWORD PTR [rsp+824], xmm0
	movdqu XMMWORD PTR [rsp+808], xmm0
	movdqu XMMWORD PTR [rsp+792], xmm0
	movdqu XMMWORD PTR [rsp+776], xmm0
	movdqu XMMWORD PTR [rsp+760], xmm0
	movdqu XMMWORD PTR [rsp+744], xmm0
	movdqu XMMWORD PTR [rsp+728], xmm0
	movdqu XMMWORD PTR [rsp+712], xmm0
	movdqu XMMWORD PTR [rsp+696], xmm0
	movdqu XMMWORD PTR [rsp+680], xmm0
	movdqu XMMWORD PTR [rsp+664], xmm0
	movdqu XMMWORD PTR [rsp+648], xmm0
	movdqu XMMWORD PTR [rsp+632], xmm0
	movdqu XMMWORD PTR [rsp+616], xmm0
	movdqu XMMWORD PTR [rsp+600], xmm0
	movdqu XMMWORD PTR [rsp+584], xmm0
	movdqu XMMWORD PTR [rsp+568], xmm0
	movdqu XMMWORD PTR [rsp+552], xmm0
	movdqu XMMWORD PTR [rsp+536], xmm0
	movdqu XMMWORD PTR [rsp+520], xmm0
	movdqu XMMWORD PTR [rsp+504], xmm0
	movdqu XMMWORD PTR [rsp+488], xmm0
	movdqu XMMWORD PTR [rsp+472], xmm0
	movdqu XMMWORD PTR [rsp+456], xmm0
	movdqu XMMWORD PTR [rsp+440], xmm0
	movdqu XMMWORD PTR [rsp+424], xmm0
	movdqu XMMWORD PTR [rsp+408], xmm0
	movdqu XMMWORD PTR [rsp+392], xmm0
	movdqu XMMWORD PTR [rsp+376], xmm0
	movdqu XMMWORD PTR [rsp+360], xmm0
	movdqu XMMWORD PTR [rsp+344], xmm0
	movdqu XMMWORD PTR [rsp+328], xmm0
	movdqu XMMWORD PTR [rsp+312], xmm0
	movdqu XMMWORD PTR [rsp+296], xmm0
	movdqu XMMWORD PTR [rsp+280], xmm0
	movdqu XMMWORD PTR [rsp+264], xmm0
	movdqu XMMWORD PTR [rsp+248], xmm0
	movdqu XMMWORD PTR [rsp+232], xmm0
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
	lea rsp, [rsp+936]
	lea rsp, [rsp+8]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	jmp 21b
	.p2align 6

vg_hmac_sha224_init_avx2:
	cmp rcx, 65
	jae 20f
	lea rsp, [rsp-664]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+608], rbx
	mov QWORD PTR [r8+616], rbp
	mov QWORD PTR [r8+624], r12
	mov QWORD PTR [r8+632], r13
	mov QWORD PTR [r8+640], r14
	mov QWORD PTR [r8+648], r15
	mov rbx, rdi
	mov r12, rsi
	mov r15, r8
	mov rbp, rdx
	mov r13, rcx
	mov rdi, rbx
	call {vg_sha224_init_core}
	mov rdi, r12
	call {vg_sha224_init_core}
	movabs rax, 3906369333256140342
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
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
	movdqu XMMWORD PTR [rbx+r10*1+32], xmm1
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
	mov BYTE PTR [rbx+r10*1+32], al
	add r14, 1
	cmp r14, r13
	jne 27b
	jmp 26f
25:
26:
	movabs rax, 7668058320836127338
	movq xmm1, rax
	punpcklqdq xmm1, xmm1
	movdqu xmm2, XMMWORD PTR [rbx+32]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [r12+32], xmm2
	movdqu xmm2, XMMWORD PTR [rbx+48]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [r12+48], xmm2
	movdqu xmm2, XMMWORD PTR [rbx+64]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [r12+64], xmm2
	movdqu xmm2, XMMWORD PTR [rbx+80]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [r12+80], xmm2
	mov rsi, rbx
	add rsi, 32
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov rbx, r12
	mov rsi, r12
	add rsi, 32
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov rbx, QWORD PTR [r15+608]
	mov rbp, QWORD PTR [r15+616]
	mov r12, QWORD PTR [r15+624]
	mov r13, QWORD PTR [r15+632]
	mov r14, QWORD PTR [r15+640]
	mov r15, QWORD PTR [r15+648]
	lea rsp, [rsp+664]
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
	lea rsp, [rsp-8]
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp-672]
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
	lea rsp, [rsp+672]
	lea rsp, [rsp+8]
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
	lea rsp, [rsp-1480]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+704], rbx
	mov QWORD PTR [r8+712], rbp
	mov QWORD PTR [r8+720], r12
	mov QWORD PTR [r8+728], r13
	mov QWORD PTR [r8+736], r14
	mov QWORD PTR [r8+744], r15
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
	add rdi, 1056
	call {vg_sha224_init_core}
	mov rdi, r15
	add rdi, 1056
	mov esi, 0
	mov rdx, rbx
	mov rcx, rbp
	mov r8, r15
	call {vg_sha256_update_scratch_avx2}
	mov rdi, r15
	add rdi, 1056
	mov rsi, rbp
	mov rdx, r15
	add rdx, 1208
	mov rcx, r15
	call {vg_sha256_finalize_scratch_avx2}
	mov rdx, r15
	add rdx, 1208
	mov ecx, 28
29:
	mov rdi, r12
	mov rsi, r13
	mov r8, r15
	call {vg_hmac_sha224_init_scratch_avx2}
	mov rbx, QWORD PTR [r15+704]
	mov rbp, QWORD PTR [r15+712]
	mov r12, QWORD PTR [r15+720]
	mov r13, QWORD PTR [r15+728]
	mov r14, QWORD PTR [r15+736]
	mov r15, QWORD PTR [r15+744]
	pxor xmm0, xmm0
	mov r11d, 0
	movdqu XMMWORD PTR [rsp+8], xmm0
	movdqu XMMWORD PTR [rsp+24], xmm0
	movdqu XMMWORD PTR [rsp+40], xmm0
	movdqu XMMWORD PTR [rsp+56], xmm0
	movdqu XMMWORD PTR [rsp+72], xmm0
	movdqu XMMWORD PTR [rsp+88], xmm0
	movdqu XMMWORD PTR [rsp+104], xmm0
	movdqu XMMWORD PTR [rsp+120], xmm0
	movdqu XMMWORD PTR [rsp+136], xmm0
	movdqu XMMWORD PTR [rsp+152], xmm0
	movdqu XMMWORD PTR [rsp+168], xmm0
	movdqu XMMWORD PTR [rsp+184], xmm0
	movdqu XMMWORD PTR [rsp+200], xmm0
	movdqu XMMWORD PTR [rsp+216], xmm0
	movdqu XMMWORD PTR [rsp+232], xmm0
	movdqu XMMWORD PTR [rsp+248], xmm0
	movdqu XMMWORD PTR [rsp+264], xmm0
	movdqu XMMWORD PTR [rsp+280], xmm0
	movdqu XMMWORD PTR [rsp+296], xmm0
	movdqu XMMWORD PTR [rsp+312], xmm0
	movdqu XMMWORD PTR [rsp+328], xmm0
	movdqu XMMWORD PTR [rsp+344], xmm0
	movdqu XMMWORD PTR [rsp+360], xmm0
	movdqu XMMWORD PTR [rsp+376], xmm0
	movdqu XMMWORD PTR [rsp+392], xmm0
	movdqu XMMWORD PTR [rsp+408], xmm0
	movdqu XMMWORD PTR [rsp+424], xmm0
	movdqu XMMWORD PTR [rsp+440], xmm0
	movdqu XMMWORD PTR [rsp+456], xmm0
	movdqu XMMWORD PTR [rsp+472], xmm0
	movdqu XMMWORD PTR [rsp+488], xmm0
	movdqu XMMWORD PTR [rsp+504], xmm0
	movdqu XMMWORD PTR [rsp+520], xmm0
	movdqu XMMWORD PTR [rsp+536], xmm0
	movdqu XMMWORD PTR [rsp+552], xmm0
	movdqu XMMWORD PTR [rsp+568], xmm0
	movdqu XMMWORD PTR [rsp+584], xmm0
	movdqu XMMWORD PTR [rsp+600], xmm0
	movdqu XMMWORD PTR [rsp+616], xmm0
	movdqu XMMWORD PTR [rsp+632], xmm0
	movdqu XMMWORD PTR [rsp+648], xmm0
	movdqu XMMWORD PTR [rsp+664], xmm0
	movdqu XMMWORD PTR [rsp+680], xmm0
	movdqu XMMWORD PTR [rsp+696], xmm0
	movdqu XMMWORD PTR [rsp+712], xmm0
	movdqu XMMWORD PTR [rsp+728], xmm0
	movdqu XMMWORD PTR [rsp+744], xmm0
	movdqu XMMWORD PTR [rsp+760], xmm0
	movdqu XMMWORD PTR [rsp+776], xmm0
	movdqu XMMWORD PTR [rsp+792], xmm0
	movdqu XMMWORD PTR [rsp+808], xmm0
	movdqu XMMWORD PTR [rsp+824], xmm0
	movdqu XMMWORD PTR [rsp+840], xmm0
	movdqu XMMWORD PTR [rsp+856], xmm0
	movdqu XMMWORD PTR [rsp+872], xmm0
	movdqu XMMWORD PTR [rsp+888], xmm0
	movdqu XMMWORD PTR [rsp+904], xmm0
	movdqu XMMWORD PTR [rsp+920], xmm0
	movdqu XMMWORD PTR [rsp+936], xmm0
	movdqu XMMWORD PTR [rsp+952], xmm0
	movdqu XMMWORD PTR [rsp+968], xmm0
	movdqu XMMWORD PTR [rsp+984], xmm0
	movdqu XMMWORD PTR [rsp+1000], xmm0
	movdqu XMMWORD PTR [rsp+1016], xmm0
	movdqu XMMWORD PTR [rsp+1032], xmm0
	movdqu XMMWORD PTR [rsp+1048], xmm0
	movdqu XMMWORD PTR [rsp+1064], xmm0
	movdqu XMMWORD PTR [rsp+1080], xmm0
	movdqu XMMWORD PTR [rsp+1096], xmm0
	movdqu XMMWORD PTR [rsp+1112], xmm0
	movdqu XMMWORD PTR [rsp+1128], xmm0
	movdqu XMMWORD PTR [rsp+1144], xmm0
	movdqu XMMWORD PTR [rsp+1160], xmm0
	movdqu XMMWORD PTR [rsp+1176], xmm0
	movdqu XMMWORD PTR [rsp+1192], xmm0
	movdqu XMMWORD PTR [rsp+1208], xmm0
	movdqu XMMWORD PTR [rsp+1224], xmm0
	movdqu XMMWORD PTR [rsp+1240], xmm0
	movdqu XMMWORD PTR [rsp+1256], xmm0
	movdqu XMMWORD PTR [rsp+1272], xmm0
	movdqu XMMWORD PTR [rsp+1288], xmm0
	movdqu XMMWORD PTR [rsp+1304], xmm0
	movdqu XMMWORD PTR [rsp+1320], xmm0
	movdqu XMMWORD PTR [rsp+1336], xmm0
	movdqu XMMWORD PTR [rsp+1352], xmm0
	movdqu XMMWORD PTR [rsp+1368], xmm0
	movdqu XMMWORD PTR [rsp+1384], xmm0
	movdqu XMMWORD PTR [rsp+1400], xmm0
	movdqu XMMWORD PTR [rsp+1416], xmm0
	movdqu XMMWORD PTR [rsp+1432], xmm0
	movdqu XMMWORD PTR [rsp+1448], xmm0
	movdqu XMMWORD PTR [rsp+1464], xmm0
	lea rsp, [rsp+1480]
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
	lea rsp, [rsp-8]
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp-1496]
	vmovdqu YMMWORD PTR [rsp+1464], ymm0
	vmovdqu YMMWORD PTR [rsp+1432], ymm0
	vmovdqu YMMWORD PTR [rsp+1400], ymm0
	vmovdqu YMMWORD PTR [rsp+1368], ymm0
	vmovdqu YMMWORD PTR [rsp+1336], ymm0
	vmovdqu YMMWORD PTR [rsp+1304], ymm0
	vmovdqu YMMWORD PTR [rsp+1272], ymm0
	vmovdqu YMMWORD PTR [rsp+1240], ymm0
	vmovdqu YMMWORD PTR [rsp+1208], ymm0
	vmovdqu YMMWORD PTR [rsp+1176], ymm0
	vmovdqu YMMWORD PTR [rsp+1144], ymm0
	vmovdqu YMMWORD PTR [rsp+1112], ymm0
	vmovdqu YMMWORD PTR [rsp+1080], ymm0
	vmovdqu YMMWORD PTR [rsp+1048], ymm0
	vmovdqu YMMWORD PTR [rsp+1016], ymm0
	vmovdqu YMMWORD PTR [rsp+984], ymm0
	vmovdqu YMMWORD PTR [rsp+952], ymm0
	vmovdqu YMMWORD PTR [rsp+920], ymm0
	vmovdqu YMMWORD PTR [rsp+888], ymm0
	vmovdqu YMMWORD PTR [rsp+856], ymm0
	vmovdqu YMMWORD PTR [rsp+824], ymm0
	vmovdqu YMMWORD PTR [rsp+792], ymm0
	vmovdqu YMMWORD PTR [rsp+760], ymm0
	vmovdqu YMMWORD PTR [rsp+728], ymm0
	vmovdqu YMMWORD PTR [rsp+696], ymm0
	vmovdqu YMMWORD PTR [rsp+664], ymm0
	vmovdqu YMMWORD PTR [rsp+632], ymm0
	vmovdqu YMMWORD PTR [rsp+600], ymm0
	vmovdqu YMMWORD PTR [rsp+568], ymm0
	vmovdqu YMMWORD PTR [rsp+536], ymm0
	vmovdqu YMMWORD PTR [rsp+504], ymm0
	vmovdqu YMMWORD PTR [rsp+472], ymm0
	vmovdqu YMMWORD PTR [rsp+440], ymm0
	vmovdqu YMMWORD PTR [rsp+408], ymm0
	vmovdqu YMMWORD PTR [rsp+376], ymm0
	vmovdqu YMMWORD PTR [rsp+344], ymm0
	vmovdqu YMMWORD PTR [rsp+312], ymm0
	vmovdqu YMMWORD PTR [rsp+280], ymm0
	vmovdqu YMMWORD PTR [rsp+248], ymm0
	vmovdqu YMMWORD PTR [rsp+216], ymm0
	vmovdqu YMMWORD PTR [rsp+184], ymm0
	vmovdqu YMMWORD PTR [rsp+152], ymm0
	vmovdqu YMMWORD PTR [rsp+120], ymm0
	vmovdqu YMMWORD PTR [rsp+88], ymm0
	vmovdqu YMMWORD PTR [rsp+56], ymm0
	vmovdqu YMMWORD PTR [rsp+24], ymm0
	movdqu XMMWORD PTR [rsp+8], xmm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+1496]
	lea rsp, [rsp+8]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	jmp 21b
	.p2align 6

vg_hmac_sha224_init:
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
	call {vg_sha224_init_core}
	mov rdi, r12
	call {vg_sha224_init_core}
	movabs rax, 3906369333256140342
	movq xmm0, rax
	punpcklqdq xmm0, xmm0
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu XMMWORD PTR [rbx+80], xmm0
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
	movdqu XMMWORD PTR [rbx+r10*1+32], xmm1
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
	mov BYTE PTR [rbx+r10*1+32], al
	add r14, 1
	cmp r14, r13
	jne 27b
	jmp 26f
25:
26:
	movabs rax, 7668058320836127338
	movq xmm1, rax
	punpcklqdq xmm1, xmm1
	movdqu xmm2, XMMWORD PTR [rbx+32]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [r12+32], xmm2
	movdqu xmm2, XMMWORD PTR [rbx+48]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [r12+48], xmm2
	movdqu xmm2, XMMWORD PTR [rbx+64]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [r12+64], xmm2
	movdqu xmm2, XMMWORD PTR [rbx+80]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [r12+80], xmm2
	mov rsi, rbx
	add rsi, 32
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress}
	mov rbx, rdi
	mov r15, rcx
	mov rbx, r12
	mov rsi, r12
	add rsi, 32
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress}
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
	lea rsp, [rsp-8]
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp-224]
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
	lea rsp, [rsp+224]
	lea rsp, [rsp+8]
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
	lea rsp, [rsp-1032]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+256], rbx
	mov QWORD PTR [r8+264], rbp
	mov QWORD PTR [r8+272], r12
	mov QWORD PTR [r8+280], r13
	mov QWORD PTR [r8+288], r14
	mov QWORD PTR [r8+296], r15
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
	add rdi, 608
	call {vg_sha224_init_core}
	mov rdi, r15
	add rdi, 608
	mov esi, 0
	mov rdx, rbx
	mov rcx, rbp
	mov r8, r15
	call {vg_sha256_update_scratch}
	mov rdi, r15
	add rdi, 608
	mov rsi, rbp
	mov rdx, r15
	add rdx, 760
	mov rcx, r15
	call {vg_sha256_finalize_scratch}
	mov rdx, r15
	add rdx, 760
	mov ecx, 28
29:
	mov rdi, r12
	mov rsi, r13
	mov r8, r15
	call {vg_hmac_sha224_init_scratch}
	mov rbx, QWORD PTR [r15+256]
	mov rbp, QWORD PTR [r15+264]
	mov r12, QWORD PTR [r15+272]
	mov r13, QWORD PTR [r15+280]
	mov r14, QWORD PTR [r15+288]
	mov r15, QWORD PTR [r15+296]
	pxor xmm0, xmm0
	mov r11d, 0
	movdqu XMMWORD PTR [rsp+8], xmm0
	movdqu XMMWORD PTR [rsp+24], xmm0
	movdqu XMMWORD PTR [rsp+40], xmm0
	movdqu XMMWORD PTR [rsp+56], xmm0
	movdqu XMMWORD PTR [rsp+72], xmm0
	movdqu XMMWORD PTR [rsp+88], xmm0
	movdqu XMMWORD PTR [rsp+104], xmm0
	movdqu XMMWORD PTR [rsp+120], xmm0
	movdqu XMMWORD PTR [rsp+136], xmm0
	movdqu XMMWORD PTR [rsp+152], xmm0
	movdqu XMMWORD PTR [rsp+168], xmm0
	movdqu XMMWORD PTR [rsp+184], xmm0
	movdqu XMMWORD PTR [rsp+200], xmm0
	movdqu XMMWORD PTR [rsp+216], xmm0
	movdqu XMMWORD PTR [rsp+232], xmm0
	movdqu XMMWORD PTR [rsp+248], xmm0
	movdqu XMMWORD PTR [rsp+264], xmm0
	movdqu XMMWORD PTR [rsp+280], xmm0
	movdqu XMMWORD PTR [rsp+296], xmm0
	movdqu XMMWORD PTR [rsp+312], xmm0
	movdqu XMMWORD PTR [rsp+328], xmm0
	movdqu XMMWORD PTR [rsp+344], xmm0
	movdqu XMMWORD PTR [rsp+360], xmm0
	movdqu XMMWORD PTR [rsp+376], xmm0
	movdqu XMMWORD PTR [rsp+392], xmm0
	movdqu XMMWORD PTR [rsp+408], xmm0
	movdqu XMMWORD PTR [rsp+424], xmm0
	movdqu XMMWORD PTR [rsp+440], xmm0
	movdqu XMMWORD PTR [rsp+456], xmm0
	movdqu XMMWORD PTR [rsp+472], xmm0
	movdqu XMMWORD PTR [rsp+488], xmm0
	movdqu XMMWORD PTR [rsp+504], xmm0
	movdqu XMMWORD PTR [rsp+520], xmm0
	movdqu XMMWORD PTR [rsp+536], xmm0
	movdqu XMMWORD PTR [rsp+552], xmm0
	movdqu XMMWORD PTR [rsp+568], xmm0
	movdqu XMMWORD PTR [rsp+584], xmm0
	movdqu XMMWORD PTR [rsp+600], xmm0
	movdqu XMMWORD PTR [rsp+616], xmm0
	movdqu XMMWORD PTR [rsp+632], xmm0
	movdqu XMMWORD PTR [rsp+648], xmm0
	movdqu XMMWORD PTR [rsp+664], xmm0
	movdqu XMMWORD PTR [rsp+680], xmm0
	movdqu XMMWORD PTR [rsp+696], xmm0
	movdqu XMMWORD PTR [rsp+712], xmm0
	movdqu XMMWORD PTR [rsp+728], xmm0
	movdqu XMMWORD PTR [rsp+744], xmm0
	movdqu XMMWORD PTR [rsp+760], xmm0
	movdqu XMMWORD PTR [rsp+776], xmm0
	movdqu XMMWORD PTR [rsp+792], xmm0
	movdqu XMMWORD PTR [rsp+808], xmm0
	movdqu XMMWORD PTR [rsp+824], xmm0
	movdqu XMMWORD PTR [rsp+840], xmm0
	movdqu XMMWORD PTR [rsp+856], xmm0
	movdqu XMMWORD PTR [rsp+872], xmm0
	movdqu XMMWORD PTR [rsp+888], xmm0
	movdqu XMMWORD PTR [rsp+904], xmm0
	movdqu XMMWORD PTR [rsp+920], xmm0
	movdqu XMMWORD PTR [rsp+936], xmm0
	movdqu XMMWORD PTR [rsp+952], xmm0
	movdqu XMMWORD PTR [rsp+968], xmm0
	movdqu XMMWORD PTR [rsp+984], xmm0
	movdqu XMMWORD PTR [rsp+1000], xmm0
	movdqu XMMWORD PTR [rsp+1016], xmm0
	lea rsp, [rsp+1032]
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
	lea rsp, [rsp-8]
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp-1048]
	movdqu XMMWORD PTR [rsp+1032], xmm0
	movdqu XMMWORD PTR [rsp+1016], xmm0
	movdqu XMMWORD PTR [rsp+1000], xmm0
	movdqu XMMWORD PTR [rsp+984], xmm0
	movdqu XMMWORD PTR [rsp+968], xmm0
	movdqu XMMWORD PTR [rsp+952], xmm0
	movdqu XMMWORD PTR [rsp+936], xmm0
	movdqu XMMWORD PTR [rsp+920], xmm0
	movdqu XMMWORD PTR [rsp+904], xmm0
	movdqu XMMWORD PTR [rsp+888], xmm0
	movdqu XMMWORD PTR [rsp+872], xmm0
	movdqu XMMWORD PTR [rsp+856], xmm0
	movdqu XMMWORD PTR [rsp+840], xmm0
	movdqu XMMWORD PTR [rsp+824], xmm0
	movdqu XMMWORD PTR [rsp+808], xmm0
	movdqu XMMWORD PTR [rsp+792], xmm0
	movdqu XMMWORD PTR [rsp+776], xmm0
	movdqu XMMWORD PTR [rsp+760], xmm0
	movdqu XMMWORD PTR [rsp+744], xmm0
	movdqu XMMWORD PTR [rsp+728], xmm0
	movdqu XMMWORD PTR [rsp+712], xmm0
	movdqu XMMWORD PTR [rsp+696], xmm0
	movdqu XMMWORD PTR [rsp+680], xmm0
	movdqu XMMWORD PTR [rsp+664], xmm0
	movdqu XMMWORD PTR [rsp+648], xmm0
	movdqu XMMWORD PTR [rsp+632], xmm0
	movdqu XMMWORD PTR [rsp+616], xmm0
	movdqu XMMWORD PTR [rsp+600], xmm0
	movdqu XMMWORD PTR [rsp+584], xmm0
	movdqu XMMWORD PTR [rsp+568], xmm0
	movdqu XMMWORD PTR [rsp+552], xmm0
	movdqu XMMWORD PTR [rsp+536], xmm0
	movdqu XMMWORD PTR [rsp+520], xmm0
	movdqu XMMWORD PTR [rsp+504], xmm0
	movdqu XMMWORD PTR [rsp+488], xmm0
	movdqu XMMWORD PTR [rsp+472], xmm0
	movdqu XMMWORD PTR [rsp+456], xmm0
	movdqu XMMWORD PTR [rsp+440], xmm0
	movdqu XMMWORD PTR [rsp+424], xmm0
	movdqu XMMWORD PTR [rsp+408], xmm0
	movdqu XMMWORD PTR [rsp+392], xmm0
	movdqu XMMWORD PTR [rsp+376], xmm0
	movdqu XMMWORD PTR [rsp+360], xmm0
	movdqu XMMWORD PTR [rsp+344], xmm0
	movdqu XMMWORD PTR [rsp+328], xmm0
	movdqu XMMWORD PTR [rsp+312], xmm0
	movdqu XMMWORD PTR [rsp+296], xmm0
	movdqu XMMWORD PTR [rsp+280], xmm0
	movdqu XMMWORD PTR [rsp+264], xmm0
	movdqu XMMWORD PTR [rsp+248], xmm0
	movdqu XMMWORD PTR [rsp+232], xmm0
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
	lea rsp, [rsp+1048]
	lea rsp, [rsp+8]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	jmp 21b
	.p2align 6

vg_hmac_sha224_finalize_shani:
	lea rsp, [rsp-152]
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
	mov r13, rcx
	mov r15, r8
	mov rsi, rdx
	mov rdx, r15
	add rdx, 96
	mov rcx, r15
	call {vg_sha256_finalize_scratch_shani}
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
	mov eax, DWORD PTR [r12+20]
	mov DWORD PTR [rbx+20], eax
	mov eax, DWORD PTR [r12+24]
	mov DWORD PTR [rbx+24], eax
	mov eax, DWORD PTR [r12+28]
	mov DWORD PTR [rbx+28], eax
	mov eax, DWORD PTR [r15+96]
	mov DWORD PTR [rbx+32], eax
	mov eax, DWORD PTR [r15+100]
	mov DWORD PTR [rbx+36], eax
	mov eax, DWORD PTR [r15+104]
	mov DWORD PTR [rbx+40], eax
	mov eax, DWORD PTR [r15+108]
	mov DWORD PTR [rbx+44], eax
	mov eax, DWORD PTR [r15+112]
	mov DWORD PTR [rbx+48], eax
	mov eax, DWORD PTR [r15+116]
	mov DWORD PTR [rbx+52], eax
	mov eax, DWORD PTR [r15+120]
	mov DWORD PTR [rbx+56], eax
	mov rbp, rbx
	add rbp, 32
	mov eax, 128
	mov DWORD PTR [rbp+28], eax
	mov eax, 0
	mov DWORD PTR [rbp+32], eax
	mov DWORD PTR [rbp+36], eax
	mov DWORD PTR [rbp+40], eax
	mov DWORD PTR [rbp+44], eax
	mov DWORD PTR [rbp+48], eax
	mov DWORD PTR [rbp+52], eax
	mov r12d, 92
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+88], rax
	mov rsi, rbp
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress_shani}
	mov rbx, rdi
	mov r15, rcx
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
	mov eax, DWORD PTR [rbx+20]
	bswap eax
	mov DWORD PTR [rbp+20], eax
	mov eax, DWORD PTR [rbx+24]
	bswap eax
	mov DWORD PTR [rbp+24], eax
	mov eax, DWORD PTR [rbx+28]
	bswap eax
	mov DWORD PTR [rbp+28], eax
	mov eax, DWORD PTR [rbp]
	mov DWORD PTR [r13], eax
	mov eax, DWORD PTR [rbp+4]
	mov DWORD PTR [r13+4], eax
	mov eax, DWORD PTR [rbp+8]
	mov DWORD PTR [r13+8], eax
	mov eax, DWORD PTR [rbp+12]
	mov DWORD PTR [r13+12], eax
	mov eax, DWORD PTR [rbp+16]
	mov DWORD PTR [r13+16], eax
	mov eax, DWORD PTR [rbp+20]
	mov DWORD PTR [r13+20], eax
	mov eax, DWORD PTR [rbp+24]
	mov DWORD PTR [r13+24], eax
	mov rbx, QWORD PTR [r15+48]
	mov rbp, QWORD PTR [r15+56]
	mov r12, QWORD PTR [r15+64]
	mov r13, QWORD PTR [r15+72]
	mov r14, QWORD PTR [r15+80]
	mov r15, QWORD PTR [r15+88]
	lea rsp, [rsp+152]
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
	lea rsp, [rsp-8]
	lea rsp, [rsp-160]
	movdqu XMMWORD PTR [rsp+144], xmm0
	movdqu XMMWORD PTR [rsp+128], xmm0
	movdqu XMMWORD PTR [rsp+112], xmm0
	lea rsp, [rsp+160]
	lea rsp, [rsp+8]
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

vg_hmac_sha224_finalize_avx2:
	lea rsp, [rsp-712]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+608], rbx
	mov QWORD PTR [r8+616], rbp
	mov QWORD PTR [r8+624], r12
	mov QWORD PTR [r8+632], r13
	mov QWORD PTR [r8+640], r14
	mov QWORD PTR [r8+648], r15
	mov rbx, rdi
	mov r12, rsi
	mov r13, rcx
	mov r15, r8
	mov rsi, rdx
	mov rdx, r15
	add rdx, 656
	mov rcx, r15
	call {vg_sha256_finalize_scratch_avx2}
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
	mov eax, DWORD PTR [r12+20]
	mov DWORD PTR [rbx+20], eax
	mov eax, DWORD PTR [r12+24]
	mov DWORD PTR [rbx+24], eax
	mov eax, DWORD PTR [r12+28]
	mov DWORD PTR [rbx+28], eax
	mov eax, DWORD PTR [r15+656]
	mov DWORD PTR [rbx+32], eax
	mov eax, DWORD PTR [r15+660]
	mov DWORD PTR [rbx+36], eax
	mov eax, DWORD PTR [r15+664]
	mov DWORD PTR [rbx+40], eax
	mov eax, DWORD PTR [r15+668]
	mov DWORD PTR [rbx+44], eax
	mov eax, DWORD PTR [r15+672]
	mov DWORD PTR [rbx+48], eax
	mov eax, DWORD PTR [r15+676]
	mov DWORD PTR [rbx+52], eax
	mov eax, DWORD PTR [r15+680]
	mov DWORD PTR [rbx+56], eax
	mov rbp, rbx
	add rbp, 32
	mov eax, 128
	mov DWORD PTR [rbp+28], eax
	mov eax, 0
	mov DWORD PTR [rbp+32], eax
	mov DWORD PTR [rbp+36], eax
	mov DWORD PTR [rbp+40], eax
	mov DWORD PTR [rbp+44], eax
	mov DWORD PTR [rbp+48], eax
	mov DWORD PTR [rbp+52], eax
	mov r12d, 92
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+88], rax
	mov rsi, rbp
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
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
	mov eax, DWORD PTR [rbx+20]
	bswap eax
	mov DWORD PTR [rbp+20], eax
	mov eax, DWORD PTR [rbx+24]
	bswap eax
	mov DWORD PTR [rbp+24], eax
	mov eax, DWORD PTR [rbx+28]
	bswap eax
	mov DWORD PTR [rbp+28], eax
	mov eax, DWORD PTR [rbp]
	mov DWORD PTR [r13], eax
	mov eax, DWORD PTR [rbp+4]
	mov DWORD PTR [r13+4], eax
	mov eax, DWORD PTR [rbp+8]
	mov DWORD PTR [r13+8], eax
	mov eax, DWORD PTR [rbp+12]
	mov DWORD PTR [r13+12], eax
	mov eax, DWORD PTR [rbp+16]
	mov DWORD PTR [r13+16], eax
	mov eax, DWORD PTR [rbp+20]
	mov DWORD PTR [r13+20], eax
	mov eax, DWORD PTR [rbp+24]
	mov DWORD PTR [r13+24], eax
	mov rbx, QWORD PTR [r15+608]
	mov rbp, QWORD PTR [r15+616]
	mov r12, QWORD PTR [r15+624]
	mov r13, QWORD PTR [r15+632]
	mov r14, QWORD PTR [r15+640]
	mov r15, QWORD PTR [r15+648]
	lea rsp, [rsp+712]
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
	lea rsp, [rsp-8]
	lea rsp, [rsp-720]
	vmovdqu YMMWORD PTR [rsp+688], ymm0
	movdqu XMMWORD PTR [rsp+672], xmm0
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
	movdqu XMMWORD PTR [rsp+16], xmm0
	lea rsp, [rsp+720]
	lea rsp, [rsp+8]
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

vg_hmac_sha224_finalize:
	lea rsp, [rsp-264]
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
	call {vg_sha256_finalize_scratch}
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
	mov eax, DWORD PTR [r12+20]
	mov DWORD PTR [rbx+20], eax
	mov eax, DWORD PTR [r12+24]
	mov DWORD PTR [rbx+24], eax
	mov eax, DWORD PTR [r12+28]
	mov DWORD PTR [rbx+28], eax
	mov eax, DWORD PTR [r15+208]
	mov DWORD PTR [rbx+32], eax
	mov eax, DWORD PTR [r15+212]
	mov DWORD PTR [rbx+36], eax
	mov eax, DWORD PTR [r15+216]
	mov DWORD PTR [rbx+40], eax
	mov eax, DWORD PTR [r15+220]
	mov DWORD PTR [rbx+44], eax
	mov eax, DWORD PTR [r15+224]
	mov DWORD PTR [rbx+48], eax
	mov eax, DWORD PTR [r15+228]
	mov DWORD PTR [rbx+52], eax
	mov eax, DWORD PTR [r15+232]
	mov DWORD PTR [rbx+56], eax
	mov rbp, rbx
	add rbp, 32
	mov eax, 128
	mov DWORD PTR [rbp+28], eax
	mov eax, 0
	mov DWORD PTR [rbp+32], eax
	mov DWORD PTR [rbp+36], eax
	mov DWORD PTR [rbp+40], eax
	mov DWORD PTR [rbp+44], eax
	mov DWORD PTR [rbp+48], eax
	mov DWORD PTR [rbp+52], eax
	mov r12d, 92
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+88], rax
	mov rsi, rbp
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress}
	mov rbx, rdi
	mov r15, rcx
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
	mov eax, DWORD PTR [rbx+20]
	bswap eax
	mov DWORD PTR [rbp+20], eax
	mov eax, DWORD PTR [rbx+24]
	bswap eax
	mov DWORD PTR [rbp+24], eax
	mov eax, DWORD PTR [rbx+28]
	bswap eax
	mov DWORD PTR [rbp+28], eax
	mov eax, DWORD PTR [rbp]
	mov DWORD PTR [r13], eax
	mov eax, DWORD PTR [rbp+4]
	mov DWORD PTR [r13+4], eax
	mov eax, DWORD PTR [rbp+8]
	mov DWORD PTR [r13+8], eax
	mov eax, DWORD PTR [rbp+12]
	mov DWORD PTR [r13+12], eax
	mov eax, DWORD PTR [rbp+16]
	mov DWORD PTR [r13+16], eax
	mov eax, DWORD PTR [rbp+20]
	mov DWORD PTR [r13+20], eax
	mov eax, DWORD PTR [rbp+24]
	mov DWORD PTR [r13+24], eax
	mov rbx, QWORD PTR [r15+160]
	mov rbp, QWORD PTR [r15+168]
	mov r12, QWORD PTR [r15+176]
	mov r13, QWORD PTR [r15+184]
	mov r14, QWORD PTR [r15+192]
	mov r15, QWORD PTR [r15+200]
	lea rsp, [rsp+264]
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
	lea rsp, [rsp-8]
	lea rsp, [rsp-272]
	movdqu XMMWORD PTR [rsp+256], xmm0
	movdqu XMMWORD PTR [rsp+240], xmm0
	movdqu XMMWORD PTR [rsp+224], xmm0
	movdqu XMMWORD PTR [rsp+80], xmm0
	movdqu XMMWORD PTR [rsp+64], xmm0
	movdqu XMMWORD PTR [rsp+48], xmm0
	movdqu XMMWORD PTR [rsp+32], xmm0
	movdqu XMMWORD PTR [rsp+16], xmm0
	lea rsp, [rsp+272]
	lea rsp, [rsp+8]
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
