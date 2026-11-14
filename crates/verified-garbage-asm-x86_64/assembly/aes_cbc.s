// The functions of `src/aes_cbc.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_cbc_decrypt_vaes_avx512:
	lea rsp, [rsp-16]
	mov QWORD PTR [rsp+8], r9
	call {vg_aes_cbc_decrypt_unwiped_vaes_avx512}
	mov QWORD PTR [rsp], rax
	mov rdi, QWORD PTR [rsp+8]
	mov esi, 224
	call {vg_zeroize_avx_core}
	mov rax, QWORD PTR [rsp]
	lea rsp, [rsp+16]
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
	lea rsp, [rsp-32]
	vmovdqu YMMWORD PTR [rsp], ymm0
	lea rsp, [rsp+32]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6

vg_aes_cbc_decrypt_vaes:
	lea rsp, [rsp-16]
	mov QWORD PTR [rsp+8], r9
	call {vg_aes_cbc_decrypt_unwiped_vaes}
	mov QWORD PTR [rsp], rax
	mov rdi, QWORD PTR [rsp+8]
	mov esi, 224
	call {vg_zeroize_avx_core}
	mov rax, QWORD PTR [rsp]
	lea rsp, [rsp+16]
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
	lea rsp, [rsp-32]
	vmovdqu YMMWORD PTR [rsp], ymm0
	lea rsp, [rsp+32]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6

vg_aes_cbc_decrypt_aesni_avx:
	lea rsp, [rsp-16]
	mov QWORD PTR [rsp+8], r9
	call {vg_aes_cbc_decrypt_unwiped_aesni}
	mov QWORD PTR [rsp], rax
	mov rdi, QWORD PTR [rsp+8]
	mov esi, 224
	call {vg_zeroize_avx_core}
	mov rax, QWORD PTR [rsp]
	lea rsp, [rsp+16]
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
	lea rsp, [rsp-32]
	vmovdqu YMMWORD PTR [rsp], ymm0
	lea rsp, [rsp+32]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6

vg_aes_cbc_encrypt_aesni:
	test r8, r8
	je 20f
	movdqu xmm1, XMMWORD PTR [rdi]
	movdqu xmm0, XMMWORD PTR [rdx]
	pxor xmm0, xmm1
	movdqu xmm2, XMMWORD PTR [rdi+16]
	movdqu xmm3, XMMWORD PTR [rdi+32]
	movdqu xmm4, XMMWORD PTR [rdi+48]
	movdqu xmm5, XMMWORD PTR [rdi+64]
	movdqu xmm6, XMMWORD PTR [rdi+80]
	movdqu xmm7, XMMWORD PTR [rdi+96]
	movdqu xmm8, XMMWORD PTR [rdi+112]
	movdqu xmm9, XMMWORD PTR [rdi+128]
	movdqu xmm10, XMMWORD PTR [rdi+144]
	movdqu xmm11, XMMWORD PTR [rdi+160]
	movdqu xmm12, XMMWORD PTR [rdi+176]
	movdqu xmm13, XMMWORD PTR [rdi+192]
	movdqu xmm14, XMMWORD PTR [rdi+208]
	cmp rsi, 10
	je 22f
	cmp rsi, 12
	je 24f
	movdqu xmm15, XMMWORD PTR [rdi+224]
	pxor xmm15, xmm1
26:
	movdqu xmm1, XMMWORD PTR [rcx]
	pxor xmm0, xmm1
	aesenc xmm0, xmm2
	aesenc xmm0, xmm3
	aesenc xmm0, xmm4
	aesenc xmm0, xmm5
	aesenc xmm0, xmm6
	aesenc xmm0, xmm7
	aesenc xmm0, xmm8
	aesenc xmm0, xmm9
	aesenc xmm0, xmm10
	aesenc xmm0, xmm11
	aesenc xmm0, xmm12
	aesenc xmm0, xmm13
	aesenc xmm0, xmm14
	aesenclast xmm0, xmm15
	add rcx, 16
	sub r8, 1
	movdqu xmm1, XMMWORD PTR [rdi]
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [rcx-16], xmm1
	jne 26b
	jmp 25f
24:
	movdqu xmm15, XMMWORD PTR [rdi+192]
	pxor xmm15, xmm1
27:
	movdqu xmm1, XMMWORD PTR [rcx]
	pxor xmm0, xmm1
	aesenc xmm0, xmm2
	aesenc xmm0, xmm3
	aesenc xmm0, xmm4
	aesenc xmm0, xmm5
	aesenc xmm0, xmm6
	aesenc xmm0, xmm7
	aesenc xmm0, xmm8
	aesenc xmm0, xmm9
	aesenc xmm0, xmm10
	aesenc xmm0, xmm11
	aesenc xmm0, xmm12
	aesenclast xmm0, xmm15
	add rcx, 16
	sub r8, 1
	movdqu xmm1, XMMWORD PTR [rdi]
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [rcx-16], xmm1
	jne 27b
25:
	jmp 23f
22:
	movdqu xmm15, XMMWORD PTR [rdi+160]
	pxor xmm15, xmm1
28:
	movdqu xmm1, XMMWORD PTR [rcx]
	pxor xmm0, xmm1
	aesenc xmm0, xmm2
	aesenc xmm0, xmm3
	aesenc xmm0, xmm4
	aesenc xmm0, xmm5
	aesenc xmm0, xmm6
	aesenc xmm0, xmm7
	aesenc xmm0, xmm8
	aesenc xmm0, xmm9
	aesenc xmm0, xmm10
	aesenclast xmm0, xmm15
	add rcx, 16
	sub r8, 1
	movdqu xmm1, XMMWORD PTR [rdi]
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [rcx-16], xmm1
	jne 28b
23:
	movdqu xmm1, XMMWORD PTR [rdi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [rdx], xmm0
	jmp 21f
20:
21:
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
	lea rsp, [rsp+8]
	xor eax, eax
	xor ecx, ecx
	xor esi, esi
	xor r8d, r8d
	ret
	.p2align 6

vg_aes_cbc_decrypt_aesni:
	lea rsp, [rsp-16]
	mov QWORD PTR [rsp+8], r9
	call {vg_aes_cbc_decrypt_unwiped_aesni}
	mov QWORD PTR [rsp], rax
	mov rdi, QWORD PTR [rsp+8]
	mov esi, 224
	call {vg_zeroize_core}
	mov rax, QWORD PTR [rsp]
	lea rsp, [rsp+16]
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
	lea rsp, [rsp-32]
	movdqu XMMWORD PTR [rsp+16], xmm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+32]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6

vg_aes_cbc_encrypt_avx:
	lea rsp, [rsp-16]
	mov QWORD PTR [rsp+8], r9
	call {vg_aes_cbc_encrypt_unwiped}
	mov QWORD PTR [rsp], rax
	mov rdi, QWORD PTR [rsp+8]
	mov esi, 2176
	call {vg_zeroize_avx_core}
	mov rax, QWORD PTR [rsp]
	lea rsp, [rsp+16]
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
	lea rsp, [rsp-32]
	vmovdqu YMMWORD PTR [rsp], ymm0
	lea rsp, [rsp+32]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6

vg_aes_cbc_decrypt_avx:
	lea rsp, [rsp-16]
	mov QWORD PTR [rsp+8], r9
	call {vg_aes_cbc_decrypt_unwiped}
	mov QWORD PTR [rsp], rax
	mov rdi, QWORD PTR [rsp+8]
	mov esi, 2176
	call {vg_zeroize_avx_core}
	mov rax, QWORD PTR [rsp]
	lea rsp, [rsp+16]
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
	lea rsp, [rsp-32]
	vmovdqu YMMWORD PTR [rsp], ymm0
	lea rsp, [rsp+32]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6

vg_aes_cbc_encrypt:
	lea rsp, [rsp-16]
	mov QWORD PTR [rsp+8], r9
	call {vg_aes_cbc_encrypt_unwiped}
	mov QWORD PTR [rsp], rax
	mov rdi, QWORD PTR [rsp+8]
	mov esi, 2176
	call {vg_zeroize_core}
	mov rax, QWORD PTR [rsp]
	lea rsp, [rsp+16]
	pxor xmm0, xmm0
	xor r11d, r11d
	lea rsp, [rsp-32]
	movdqu XMMWORD PTR [rsp+16], xmm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+32]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6

vg_aes_cbc_decrypt:
	lea rsp, [rsp-16]
	mov QWORD PTR [rsp+8], r9
	call {vg_aes_cbc_decrypt_unwiped}
	mov QWORD PTR [rsp], rax
	mov rdi, QWORD PTR [rsp+8]
	mov esi, 2176
	call {vg_zeroize_core}
	mov rax, QWORD PTR [rsp]
	lea rsp, [rsp+16]
	pxor xmm0, xmm0
	xor r11d, r11d
	lea rsp, [rsp-32]
	movdqu XMMWORD PTR [rsp+16], xmm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+32]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6
