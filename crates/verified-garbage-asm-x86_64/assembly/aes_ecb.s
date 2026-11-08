// The functions of `src/aes_ecb.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ecb_decrypt_aesni_avx:
	lea rsp, [rsp-16]
	mov QWORD PTR [rsp+8], r8
	call {vg_aes_decrypt_blocks_aesni}
	mov QWORD PTR [rsp], rax
	mov rdi, QWORD PTR [rsp+8]
	mov esi, 224
	call {vg_zeroize_avx}
	mov rax, QWORD PTR [rsp]
	lea rsp, [rsp+16]
	ret
	.p2align 6

vg_aes_ecb_encrypt_aesni:
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	cmp rcx, 8
	jb 20f
22:
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu xmm1, XMMWORD PTR [rdx+16]
	movdqu xmm2, XMMWORD PTR [rdx+32]
	movdqu xmm3, XMMWORD PTR [rdx+48]
	movdqu xmm4, XMMWORD PTR [rdx+64]
	movdqu xmm5, XMMWORD PTR [rdx+80]
	movdqu xmm6, XMMWORD PTR [rdx+96]
	movdqu xmm7, XMMWORD PTR [rdx+112]
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	pxor xmm2, xmm8
	pxor xmm3, xmm8
	pxor xmm4, xmm8
	pxor xmm5, xmm8
	pxor xmm6, xmm8
	pxor xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	cmp rsi, 10
	je 23f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	cmp rsi, 12
	je 25f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	jmp 26f
25:
26:
	jmp 24f
23:
24:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	aesenclast xmm2, xmm8
	aesenclast xmm3, xmm8
	aesenclast xmm4, xmm8
	aesenclast xmm5, xmm8
	aesenclast xmm6, xmm8
	aesenclast xmm7, xmm8
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu XMMWORD PTR [rdx+16], xmm1
	movdqu XMMWORD PTR [rdx+32], xmm2
	movdqu XMMWORD PTR [rdx+48], xmm3
	movdqu XMMWORD PTR [rdx+64], xmm4
	movdqu XMMWORD PTR [rdx+80], xmm5
	movdqu XMMWORD PTR [rdx+96], xmm6
	movdqu XMMWORD PTR [rdx+112], xmm7
	add rdx, 128
	sub rcx, 8
	cmp rcx, 8
	jae 22b
	jmp 21f
20:
21:
	test rcx, rcx
	je 27f
29:
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	cmp rsi, 10
	je 210f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 212f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 213f
212:
213:
	jmp 211f
210:
211:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	movdqu XMMWORD PTR [rdx], xmm0
	add rdx, 16
	sub rcx, 1
	jne 29b
	jmp 28f
27:
28:
	ret
	.p2align 6

vg_aes_ecb_decrypt_aesni:
	lea rsp, [rsp-16]
	mov QWORD PTR [rsp+8], r8
	call {vg_aes_decrypt_blocks_aesni}
	mov QWORD PTR [rsp], rax
	mov rdi, QWORD PTR [rsp+8]
	mov esi, 224
	call {vg_zeroize}
	mov rax, QWORD PTR [rsp]
	lea rsp, [rsp+16]
	ret
	.p2align 6

vg_aes_ecb_encrypt_avx:
	lea rsp, [rsp-16]
	mov QWORD PTR [rsp+8], r8
	call {vg_aes_encrypt_blocks}
	mov QWORD PTR [rsp], rax
	mov rdi, QWORD PTR [rsp+8]
	mov esi, 2048
	call {vg_zeroize_avx}
	mov rax, QWORD PTR [rsp]
	lea rsp, [rsp+16]
	ret
	.p2align 6

vg_aes_ecb_decrypt_avx:
	lea rsp, [rsp-16]
	mov QWORD PTR [rsp+8], r8
	call {vg_aes_decrypt_blocks}
	mov QWORD PTR [rsp], rax
	mov rdi, QWORD PTR [rsp+8]
	mov esi, 2048
	call {vg_zeroize_avx}
	mov rax, QWORD PTR [rsp]
	lea rsp, [rsp+16]
	ret
	.p2align 6

vg_aes_ecb_encrypt:
	lea rsp, [rsp-16]
	mov QWORD PTR [rsp+8], r8
	call {vg_aes_encrypt_blocks}
	mov QWORD PTR [rsp], rax
	mov rdi, QWORD PTR [rsp+8]
	mov esi, 2048
	call {vg_zeroize}
	mov rax, QWORD PTR [rsp]
	lea rsp, [rsp+16]
	ret
	.p2align 6

vg_aes_ecb_decrypt:
	lea rsp, [rsp-16]
	mov QWORD PTR [rsp+8], r8
	call {vg_aes_decrypt_blocks}
	mov QWORD PTR [rsp], rax
	mov rdi, QWORD PTR [rsp+8]
	mov esi, 2048
	call {vg_zeroize}
	mov rax, QWORD PTR [rsp]
	lea rsp, [rsp+16]
	ret
	.p2align 6

vg_aes_ecb_decrypt_vaes:
	lea rsp, [rsp-16]
	mov QWORD PTR [rsp+8], r8
	call {vg_aes_decrypt_blocks_vaes}
	mov QWORD PTR [rsp], rax
	mov rdi, QWORD PTR [rsp+8]
	mov esi, 224
	call {vg_zeroize_avx}
	mov rax, QWORD PTR [rsp]
	lea rsp, [rsp+16]
	ret
	.p2align 6

vg_aes_ecb_encrypt_vaes:
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	cmp rcx, 16
	jb 20f
22:
	vmovdqu ymm0, YMMWORD PTR [rdx]
	vmovdqu ymm1, YMMWORD PTR [rdx+32]
	vmovdqu ymm2, YMMWORD PTR [rdx+64]
	vmovdqu ymm3, YMMWORD PTR [rdx+96]
	vmovdqu ymm4, YMMWORD PTR [rdx+128]
	vmovdqu ymm5, YMMWORD PTR [rdx+160]
	vmovdqu ymm6, YMMWORD PTR [rdx+192]
	vmovdqu ymm7, YMMWORD PTR [rdx+224]
	vbroadcasti128 ymm8, XMMWORD PTR [rdi]
	vpxor ymm0, ymm0, ymm8
	vpxor ymm1, ymm1, ymm8
	vpxor ymm2, ymm2, ymm8
	vpxor ymm3, ymm3, ymm8
	vpxor ymm4, ymm4, ymm8
	vpxor ymm5, ymm5, ymm8
	vpxor ymm6, ymm6, ymm8
	vpxor ymm7, ymm7, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [rdi+16]
	vaesenc ymm0, ymm0, ymm8
	vaesenc ymm1, ymm1, ymm8
	vaesenc ymm2, ymm2, ymm8
	vaesenc ymm3, ymm3, ymm8
	vaesenc ymm4, ymm4, ymm8
	vaesenc ymm5, ymm5, ymm8
	vaesenc ymm6, ymm6, ymm8
	vaesenc ymm7, ymm7, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [rdi+32]
	vaesenc ymm0, ymm0, ymm8
	vaesenc ymm1, ymm1, ymm8
	vaesenc ymm2, ymm2, ymm8
	vaesenc ymm3, ymm3, ymm8
	vaesenc ymm4, ymm4, ymm8
	vaesenc ymm5, ymm5, ymm8
	vaesenc ymm6, ymm6, ymm8
	vaesenc ymm7, ymm7, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [rdi+48]
	vaesenc ymm0, ymm0, ymm8
	vaesenc ymm1, ymm1, ymm8
	vaesenc ymm2, ymm2, ymm8
	vaesenc ymm3, ymm3, ymm8
	vaesenc ymm4, ymm4, ymm8
	vaesenc ymm5, ymm5, ymm8
	vaesenc ymm6, ymm6, ymm8
	vaesenc ymm7, ymm7, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [rdi+64]
	vaesenc ymm0, ymm0, ymm8
	vaesenc ymm1, ymm1, ymm8
	vaesenc ymm2, ymm2, ymm8
	vaesenc ymm3, ymm3, ymm8
	vaesenc ymm4, ymm4, ymm8
	vaesenc ymm5, ymm5, ymm8
	vaesenc ymm6, ymm6, ymm8
	vaesenc ymm7, ymm7, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [rdi+80]
	vaesenc ymm0, ymm0, ymm8
	vaesenc ymm1, ymm1, ymm8
	vaesenc ymm2, ymm2, ymm8
	vaesenc ymm3, ymm3, ymm8
	vaesenc ymm4, ymm4, ymm8
	vaesenc ymm5, ymm5, ymm8
	vaesenc ymm6, ymm6, ymm8
	vaesenc ymm7, ymm7, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [rdi+96]
	vaesenc ymm0, ymm0, ymm8
	vaesenc ymm1, ymm1, ymm8
	vaesenc ymm2, ymm2, ymm8
	vaesenc ymm3, ymm3, ymm8
	vaesenc ymm4, ymm4, ymm8
	vaesenc ymm5, ymm5, ymm8
	vaesenc ymm6, ymm6, ymm8
	vaesenc ymm7, ymm7, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [rdi+112]
	vaesenc ymm0, ymm0, ymm8
	vaesenc ymm1, ymm1, ymm8
	vaesenc ymm2, ymm2, ymm8
	vaesenc ymm3, ymm3, ymm8
	vaesenc ymm4, ymm4, ymm8
	vaesenc ymm5, ymm5, ymm8
	vaesenc ymm6, ymm6, ymm8
	vaesenc ymm7, ymm7, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [rdi+128]
	vaesenc ymm0, ymm0, ymm8
	vaesenc ymm1, ymm1, ymm8
	vaesenc ymm2, ymm2, ymm8
	vaesenc ymm3, ymm3, ymm8
	vaesenc ymm4, ymm4, ymm8
	vaesenc ymm5, ymm5, ymm8
	vaesenc ymm6, ymm6, ymm8
	vaesenc ymm7, ymm7, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [rdi+144]
	vaesenc ymm0, ymm0, ymm8
	vaesenc ymm1, ymm1, ymm8
	vaesenc ymm2, ymm2, ymm8
	vaesenc ymm3, ymm3, ymm8
	vaesenc ymm4, ymm4, ymm8
	vaesenc ymm5, ymm5, ymm8
	vaesenc ymm6, ymm6, ymm8
	vaesenc ymm7, ymm7, ymm8
	cmp rsi, 10
	je 23f
	vbroadcasti128 ymm8, XMMWORD PTR [rdi+160]
	vaesenc ymm0, ymm0, ymm8
	vaesenc ymm1, ymm1, ymm8
	vaesenc ymm2, ymm2, ymm8
	vaesenc ymm3, ymm3, ymm8
	vaesenc ymm4, ymm4, ymm8
	vaesenc ymm5, ymm5, ymm8
	vaesenc ymm6, ymm6, ymm8
	vaesenc ymm7, ymm7, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [rdi+176]
	vaesenc ymm0, ymm0, ymm8
	vaesenc ymm1, ymm1, ymm8
	vaesenc ymm2, ymm2, ymm8
	vaesenc ymm3, ymm3, ymm8
	vaesenc ymm4, ymm4, ymm8
	vaesenc ymm5, ymm5, ymm8
	vaesenc ymm6, ymm6, ymm8
	vaesenc ymm7, ymm7, ymm8
	cmp rsi, 12
	je 25f
	vbroadcasti128 ymm8, XMMWORD PTR [rdi+192]
	vaesenc ymm0, ymm0, ymm8
	vaesenc ymm1, ymm1, ymm8
	vaesenc ymm2, ymm2, ymm8
	vaesenc ymm3, ymm3, ymm8
	vaesenc ymm4, ymm4, ymm8
	vaesenc ymm5, ymm5, ymm8
	vaesenc ymm6, ymm6, ymm8
	vaesenc ymm7, ymm7, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [rdi+208]
	vaesenc ymm0, ymm0, ymm8
	vaesenc ymm1, ymm1, ymm8
	vaesenc ymm2, ymm2, ymm8
	vaesenc ymm3, ymm3, ymm8
	vaesenc ymm4, ymm4, ymm8
	vaesenc ymm5, ymm5, ymm8
	vaesenc ymm6, ymm6, ymm8
	vaesenc ymm7, ymm7, ymm8
	jmp 26f
25:
26:
	jmp 24f
23:
24:
	vbroadcasti128 ymm8, XMMWORD PTR [r10]
	vaesenclast ymm0, ymm0, ymm8
	vaesenclast ymm1, ymm1, ymm8
	vaesenclast ymm2, ymm2, ymm8
	vaesenclast ymm3, ymm3, ymm8
	vaesenclast ymm4, ymm4, ymm8
	vaesenclast ymm5, ymm5, ymm8
	vaesenclast ymm6, ymm6, ymm8
	vaesenclast ymm7, ymm7, ymm8
	vmovdqu YMMWORD PTR [rdx], ymm0
	vmovdqu YMMWORD PTR [rdx+32], ymm1
	vmovdqu YMMWORD PTR [rdx+64], ymm2
	vmovdqu YMMWORD PTR [rdx+96], ymm3
	vmovdqu YMMWORD PTR [rdx+128], ymm4
	vmovdqu YMMWORD PTR [rdx+160], ymm5
	vmovdqu YMMWORD PTR [rdx+192], ymm6
	vmovdqu YMMWORD PTR [rdx+224], ymm7
	add rdx, 256
	sub rcx, 16
	cmp rcx, 16
	jae 22b
	jmp 21f
20:
21:
	vzeroupper
	cmp rcx, 8
	jb 27f
29:
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu xmm1, XMMWORD PTR [rdx+16]
	movdqu xmm2, XMMWORD PTR [rdx+32]
	movdqu xmm3, XMMWORD PTR [rdx+48]
	movdqu xmm4, XMMWORD PTR [rdx+64]
	movdqu xmm5, XMMWORD PTR [rdx+80]
	movdqu xmm6, XMMWORD PTR [rdx+96]
	movdqu xmm7, XMMWORD PTR [rdx+112]
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	pxor xmm2, xmm8
	pxor xmm3, xmm8
	pxor xmm4, xmm8
	pxor xmm5, xmm8
	pxor xmm6, xmm8
	pxor xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	cmp rsi, 10
	je 210f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	cmp rsi, 12
	je 212f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	jmp 213f
212:
213:
	jmp 211f
210:
211:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	aesenclast xmm2, xmm8
	aesenclast xmm3, xmm8
	aesenclast xmm4, xmm8
	aesenclast xmm5, xmm8
	aesenclast xmm6, xmm8
	aesenclast xmm7, xmm8
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu XMMWORD PTR [rdx+16], xmm1
	movdqu XMMWORD PTR [rdx+32], xmm2
	movdqu XMMWORD PTR [rdx+48], xmm3
	movdqu XMMWORD PTR [rdx+64], xmm4
	movdqu XMMWORD PTR [rdx+80], xmm5
	movdqu XMMWORD PTR [rdx+96], xmm6
	movdqu XMMWORD PTR [rdx+112], xmm7
	add rdx, 128
	sub rcx, 8
	cmp rcx, 8
	jae 29b
	jmp 28f
27:
28:
	test rcx, rcx
	je 214f
216:
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	cmp rsi, 10
	je 217f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 219f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 220f
219:
220:
	jmp 218f
217:
218:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	movdqu XMMWORD PTR [rdx], xmm0
	add rdx, 16
	sub rcx, 1
	jne 216b
	jmp 215f
214:
215:
	ret
	.p2align 6
