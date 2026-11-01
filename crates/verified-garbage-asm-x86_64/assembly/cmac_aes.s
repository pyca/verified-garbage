// The functions of `src/cmac_aes.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cmac_aes_update_aesni_cbc:
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
	jne 28b
23:
	movdqu xmm1, XMMWORD PTR [rdi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [rdx], xmm0
	jmp 21f
20:
21:
	ret
	.p2align 6

vg_cmac_aes_subkeys_aesni:
	mov QWORD PTR [rcx+2064], rbx
	mov QWORD PTR [rcx+2072], rbp
	mov rbx, rdx
	mov rbp, rcx
	mov eax, 0
	mov QWORD PTR [rcx+2048], rax
	mov QWORD PTR [rcx+2056], rax
	mov QWORD PTR [rdx], rax
	mov QWORD PTR [rdx+8], rax
	mov r9, rbp
	mov rdx, rbp
	add rdx, 2048
	mov rcx, rbx
	mov r8d, 1
	call {vg_aes_ctr32_aesni}
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov rdx, QWORD PTR [rbx+8]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	mov r8d, 0
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rax
	mov QWORD PTR [rbx+8], rdx
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov rdx, QWORD PTR [rbx+8]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	mov r8d, 0
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx+16], rax
	mov QWORD PTR [rbx+24], rdx
	mov rbx, QWORD PTR [rbp+2064]
	mov rbp, QWORD PTR [rbp+2072]
	ret
	.p2align 6

vg_cmac_aes_update_aesni:
	mov QWORD PTR [r9+2064], rbx
	mov QWORD PTR [r9+2072], rbp
	mov QWORD PTR [r9+2080], r12
	mov QWORD PTR [r9+2088], r13
	mov QWORD PTR [r9+2096], r14
	mov QWORD PTR [r9+2104], r15
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rdx
	mov r13, rcx
	mov r14, r8
	mov r15, r9
	test r14, r14
	je 20f
22:
	mov rax, QWORD PTR [r12]
	xor rax, QWORD PTR [r13]
	mov QWORD PTR [r15+2048], rax
	mov rax, QWORD PTR [r12+8]
	xor rax, QWORD PTR [r13+8]
	mov QWORD PTR [r15+2056], rax
	mov eax, 0
	mov QWORD PTR [r12], rax
	mov QWORD PTR [r12+8], rax
	mov rdi, rbx
	mov rsi, rbp
	mov r9, r15
	mov rdx, r15
	add rdx, 2048
	mov rcx, r12
	mov r8d, 1
	call {vg_aes_ctr32_aesni}
	add r13, 16
	sub r14, 1
	jne 22b
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+2064]
	mov rbp, QWORD PTR [r15+2072]
	mov r12, QWORD PTR [r15+2080]
	mov r13, QWORD PTR [r15+2088]
	mov r14, QWORD PTR [r15+2096]
	mov r15, QWORD PTR [r15+2104]
	ret
	.p2align 6

vg_cmac_aes_finalize_aesni:
	cmp r8, 16
	je 20f
	mov eax, 0
	mov QWORD PTR [r9+2048], rax
	mov QWORD PTR [r9+2056], rax
	test r8, r8
	je 22f
	mov r10d, 0
24:
	movzx eax, BYTE PTR [rcx+r10*1]
	mov BYTE PTR [r9+r10*1+2048], al
	add r10, 1
	cmp r10, r8
	jne 24b
	jmp 23f
22:
23:
	mov eax, 128
	mov BYTE PTR [r9+r8*1+2048], al
	mov rax, QWORD PTR [r9+2048]
	xor rax, QWORD PTR [rdi+256]
	mov QWORD PTR [r9+2048], rax
	mov rax, QWORD PTR [r9+2056]
	xor rax, QWORD PTR [rdi+264]
	mov QWORD PTR [r9+2056], rax
	jmp 21f
20:
	mov rax, QWORD PTR [rcx]
	xor rax, QWORD PTR [rdi+240]
	mov QWORD PTR [r9+2048], rax
	mov rax, QWORD PTR [rcx+8]
	xor rax, QWORD PTR [rdi+248]
	mov QWORD PTR [r9+2056], rax
21:
	mov rax, QWORD PTR [r9+2048]
	xor rax, QWORD PTR [rdx]
	mov QWORD PTR [r9+2048], rax
	mov rax, QWORD PTR [r9+2056]
	xor rax, QWORD PTR [rdx+8]
	mov QWORD PTR [r9+2056], rax
	mov eax, 0
	mov QWORD PTR [rdx], rax
	mov QWORD PTR [rdx+8], rax
	mov rcx, rdx
	mov rdx, r9
	add rdx, 2048
	mov r8d, 1
	call {vg_aes_ctr32_aesni}
	ret
	.p2align 6

vg_cmac_aes_init_aesni:
	lea rsp, [rsp-2312]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+2176], rbx
	mov QWORD PTR [rcx+2184], rbp
	mov QWORD PTR [rcx+2192], r12
	mov rbx, rdi
	mov rbp, rcx
	mov r12, rdx
	shr r12, 2
	add r12, 6
	mov rdi, rsi
	mov rsi, rdx
	mov rdx, rbx
	call {vg_aes_expand_key_scratch_aesni}
	mov rdi, rbx
	mov rsi, r12
	mov rdx, rbx
	add rdx, 240
	mov rcx, rbp
	call {vg_cmac_aes_subkeys_aesni}
	mov eax, 0
	mov QWORD PTR [rbx+272], rax
	mov QWORD PTR [rbx+280], rax
	mov rbx, QWORD PTR [rbp+2176]
	mov r12, QWORD PTR [rbp+2192]
	mov rbp, QWORD PTR [rbp+2184]
	lea rsp, [rsp+2312]
	ret
	.p2align 6

vg_cmac_aes_finish_aesni:
	lea rsp, [rsp-2312]
	mov r8, rsp
	add r8, 8
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rcx], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rcx+8], rax
	mov r9, r8
	mov r8, rdx
	mov rdx, rcx
	mov rcx, rdi
	add rcx, 288
	test r8, r8
	je 20f
	sub r8, 1
	and r8, 15
	add r8, 1
	jmp 21f
20:
21:
	call {vg_cmac_aes_finalize_aesni}
	lea rsp, [rsp+2312]
	ret
	.p2align 6

vg_cmac_aes_subkeys:
	mov QWORD PTR [rcx+2064], rbx
	mov QWORD PTR [rcx+2072], rbp
	mov rbx, rdx
	mov rbp, rcx
	mov eax, 0
	mov QWORD PTR [rcx+2048], rax
	mov QWORD PTR [rcx+2056], rax
	mov QWORD PTR [rdx], rax
	mov QWORD PTR [rdx+8], rax
	mov r9, rbp
	mov rdx, rbp
	add rdx, 2048
	mov rcx, rbx
	mov r8d, 1
	call {vg_aes_ctr32}
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov rdx, QWORD PTR [rbx+8]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	mov r8d, 0
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rax
	mov QWORD PTR [rbx+8], rdx
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov rdx, QWORD PTR [rbx+8]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	mov r8d, 0
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx+16], rax
	mov QWORD PTR [rbx+24], rdx
	mov rbx, QWORD PTR [rbp+2064]
	mov rbp, QWORD PTR [rbp+2072]
	ret
	.p2align 6

vg_cmac_aes_update:
	mov QWORD PTR [r9+2064], rbx
	mov QWORD PTR [r9+2072], rbp
	mov QWORD PTR [r9+2080], r12
	mov QWORD PTR [r9+2088], r13
	mov QWORD PTR [r9+2096], r14
	mov QWORD PTR [r9+2104], r15
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rdx
	mov r13, rcx
	mov r14, r8
	mov r15, r9
	test r14, r14
	je 20f
22:
	mov rax, QWORD PTR [r12]
	xor rax, QWORD PTR [r13]
	mov QWORD PTR [r15+2048], rax
	mov rax, QWORD PTR [r12+8]
	xor rax, QWORD PTR [r13+8]
	mov QWORD PTR [r15+2056], rax
	mov eax, 0
	mov QWORD PTR [r12], rax
	mov QWORD PTR [r12+8], rax
	mov rdi, rbx
	mov rsi, rbp
	mov r9, r15
	mov rdx, r15
	add rdx, 2048
	mov rcx, r12
	mov r8d, 1
	call {vg_aes_ctr32}
	add r13, 16
	sub r14, 1
	jne 22b
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+2064]
	mov rbp, QWORD PTR [r15+2072]
	mov r12, QWORD PTR [r15+2080]
	mov r13, QWORD PTR [r15+2088]
	mov r14, QWORD PTR [r15+2096]
	mov r15, QWORD PTR [r15+2104]
	ret
	.p2align 6

vg_cmac_aes_finalize:
	cmp r8, 16
	je 20f
	mov eax, 0
	mov QWORD PTR [r9+2048], rax
	mov QWORD PTR [r9+2056], rax
	test r8, r8
	je 22f
	mov r10d, 0
24:
	movzx eax, BYTE PTR [rcx+r10*1]
	mov BYTE PTR [r9+r10*1+2048], al
	add r10, 1
	cmp r10, r8
	jne 24b
	jmp 23f
22:
23:
	mov eax, 128
	mov BYTE PTR [r9+r8*1+2048], al
	mov rax, QWORD PTR [r9+2048]
	xor rax, QWORD PTR [rdi+256]
	mov QWORD PTR [r9+2048], rax
	mov rax, QWORD PTR [r9+2056]
	xor rax, QWORD PTR [rdi+264]
	mov QWORD PTR [r9+2056], rax
	jmp 21f
20:
	mov rax, QWORD PTR [rcx]
	xor rax, QWORD PTR [rdi+240]
	mov QWORD PTR [r9+2048], rax
	mov rax, QWORD PTR [rcx+8]
	xor rax, QWORD PTR [rdi+248]
	mov QWORD PTR [r9+2056], rax
21:
	mov rax, QWORD PTR [r9+2048]
	xor rax, QWORD PTR [rdx]
	mov QWORD PTR [r9+2048], rax
	mov rax, QWORD PTR [r9+2056]
	xor rax, QWORD PTR [rdx+8]
	mov QWORD PTR [r9+2056], rax
	mov eax, 0
	mov QWORD PTR [rdx], rax
	mov QWORD PTR [rdx+8], rax
	mov rcx, rdx
	mov rdx, r9
	add rdx, 2048
	mov r8d, 1
	call {vg_aes_ctr32}
	ret
	.p2align 6

vg_cmac_aes_init:
	lea rsp, [rsp-2312]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+2176], rbx
	mov QWORD PTR [rcx+2184], rbp
	mov QWORD PTR [rcx+2192], r12
	mov rbx, rdi
	mov rbp, rcx
	mov r12, rdx
	shr r12, 2
	add r12, 6
	mov rdi, rsi
	mov rsi, rdx
	mov rdx, rbx
	call {vg_aes_expand_key_scratch}
	mov rdi, rbx
	mov rsi, r12
	mov rdx, rbx
	add rdx, 240
	mov rcx, rbp
	call {vg_cmac_aes_subkeys}
	mov eax, 0
	mov QWORD PTR [rbx+272], rax
	mov QWORD PTR [rbx+280], rax
	mov rbx, QWORD PTR [rbp+2176]
	mov r12, QWORD PTR [rbp+2192]
	mov rbp, QWORD PTR [rbp+2184]
	lea rsp, [rsp+2312]
	ret
	.p2align 6

vg_cmac_aes_finish:
	lea rsp, [rsp-2312]
	mov r8, rsp
	add r8, 8
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rcx], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rcx+8], rax
	mov r9, r8
	mov r8, rdx
	mov rdx, rcx
	mov rcx, rdi
	add rcx, 288
	test r8, r8
	je 20f
	sub r8, 1
	and r8, 15
	add r8, 1
	jmp 21f
20:
21:
	call {vg_cmac_aes_finalize}
	lea rsp, [rsp+2312]
	ret
	.p2align 6

vg_cmac_aes_subkeys_vaes:
	mov QWORD PTR [rcx+2064], rbx
	mov QWORD PTR [rcx+2072], rbp
	mov rbx, rdx
	mov rbp, rcx
	mov eax, 0
	mov QWORD PTR [rcx+2048], rax
	mov QWORD PTR [rcx+2056], rax
	mov QWORD PTR [rdx], rax
	mov QWORD PTR [rdx+8], rax
	mov r9, rbp
	mov rdx, rbp
	add rdx, 2048
	mov rcx, rbx
	mov r8d, 1
	call {vg_aes_ctr32_vaes}
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov rdx, QWORD PTR [rbx+8]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	mov r8d, 0
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rax
	mov QWORD PTR [rbx+8], rdx
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov rdx, QWORD PTR [rbx+8]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	mov r8d, 0
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx+16], rax
	mov QWORD PTR [rbx+24], rdx
	mov rbx, QWORD PTR [rbp+2064]
	mov rbp, QWORD PTR [rbp+2072]
	ret
	.p2align 6

vg_cmac_aes_update_vaes:
	mov QWORD PTR [r9+2064], rbx
	mov QWORD PTR [r9+2072], rbp
	mov QWORD PTR [r9+2080], r12
	mov QWORD PTR [r9+2088], r13
	mov QWORD PTR [r9+2096], r14
	mov QWORD PTR [r9+2104], r15
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rdx
	mov r13, rcx
	mov r14, r8
	mov r15, r9
	test r14, r14
	je 20f
22:
	mov rax, QWORD PTR [r12]
	xor rax, QWORD PTR [r13]
	mov QWORD PTR [r15+2048], rax
	mov rax, QWORD PTR [r12+8]
	xor rax, QWORD PTR [r13+8]
	mov QWORD PTR [r15+2056], rax
	mov eax, 0
	mov QWORD PTR [r12], rax
	mov QWORD PTR [r12+8], rax
	mov rdi, rbx
	mov rsi, rbp
	mov r9, r15
	mov rdx, r15
	add rdx, 2048
	mov rcx, r12
	mov r8d, 1
	call {vg_aes_ctr32_vaes}
	add r13, 16
	sub r14, 1
	jne 22b
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+2064]
	mov rbp, QWORD PTR [r15+2072]
	mov r12, QWORD PTR [r15+2080]
	mov r13, QWORD PTR [r15+2088]
	mov r14, QWORD PTR [r15+2096]
	mov r15, QWORD PTR [r15+2104]
	ret
	.p2align 6

vg_cmac_aes_finalize_vaes:
	cmp r8, 16
	je 20f
	mov eax, 0
	mov QWORD PTR [r9+2048], rax
	mov QWORD PTR [r9+2056], rax
	test r8, r8
	je 22f
	mov r10d, 0
24:
	movzx eax, BYTE PTR [rcx+r10*1]
	mov BYTE PTR [r9+r10*1+2048], al
	add r10, 1
	cmp r10, r8
	jne 24b
	jmp 23f
22:
23:
	mov eax, 128
	mov BYTE PTR [r9+r8*1+2048], al
	mov rax, QWORD PTR [r9+2048]
	xor rax, QWORD PTR [rdi+256]
	mov QWORD PTR [r9+2048], rax
	mov rax, QWORD PTR [r9+2056]
	xor rax, QWORD PTR [rdi+264]
	mov QWORD PTR [r9+2056], rax
	jmp 21f
20:
	mov rax, QWORD PTR [rcx]
	xor rax, QWORD PTR [rdi+240]
	mov QWORD PTR [r9+2048], rax
	mov rax, QWORD PTR [rcx+8]
	xor rax, QWORD PTR [rdi+248]
	mov QWORD PTR [r9+2056], rax
21:
	mov rax, QWORD PTR [r9+2048]
	xor rax, QWORD PTR [rdx]
	mov QWORD PTR [r9+2048], rax
	mov rax, QWORD PTR [r9+2056]
	xor rax, QWORD PTR [rdx+8]
	mov QWORD PTR [r9+2056], rax
	mov eax, 0
	mov QWORD PTR [rdx], rax
	mov QWORD PTR [rdx+8], rax
	mov rcx, rdx
	mov rdx, r9
	add rdx, 2048
	mov r8d, 1
	call {vg_aes_ctr32_vaes}
	ret
	.p2align 6

vg_cmac_aes_init_vaes:
	lea rsp, [rsp-2312]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+2176], rbx
	mov QWORD PTR [rcx+2184], rbp
	mov QWORD PTR [rcx+2192], r12
	mov rbx, rdi
	mov rbp, rcx
	mov r12, rdx
	shr r12, 2
	add r12, 6
	mov rdi, rsi
	mov rsi, rdx
	mov rdx, rbx
	call {vg_aes_expand_key_scratch_aesni}
	mov rdi, rbx
	mov rsi, r12
	mov rdx, rbx
	add rdx, 240
	mov rcx, rbp
	call {vg_cmac_aes_subkeys_vaes}
	mov eax, 0
	mov QWORD PTR [rbx+272], rax
	mov QWORD PTR [rbx+280], rax
	mov rbx, QWORD PTR [rbp+2176]
	mov r12, QWORD PTR [rbp+2192]
	mov rbp, QWORD PTR [rbp+2184]
	lea rsp, [rsp+2312]
	ret
	.p2align 6

vg_cmac_aes_finish_vaes:
	lea rsp, [rsp-2312]
	mov r8, rsp
	add r8, 8
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rcx], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rcx+8], rax
	mov r9, r8
	mov r8, rdx
	mov rdx, rcx
	mov rcx, rdi
	add rcx, 288
	test r8, r8
	je 20f
	sub r8, 1
	and r8, 15
	add r8, 1
	jmp 21f
20:
21:
	call {vg_cmac_aes_finalize_vaes}
	lea rsp, [rsp+2312]
	ret
	.p2align 6

vg_cmac_aes_absorb_aesni:
	lea rsp, [rsp-2312]
	mov r9, rsp
	add r9, 8
	mov QWORD PTR [r9+2176], rbx
	mov QWORD PTR [r9+2184], rbp
	mov QWORD PTR [r9+2192], r12
	mov QWORD PTR [r9+2200], r13
	mov QWORD PTR [r9+2208], r14
	mov QWORD PTR [r9+2216], r15
	mov rbx, rdi
	mov rbp, rsi
	mov r13, rcx
	mov r14, r8
	mov r15, r9
	test rdx, rdx
	je 20f
	mov rax, rdx
	sub rax, 1
	and rax, 15
	add rax, 1
	jmp 21f
20:
	mov eax, 0
21:
	mov ecx, 16
	sub rcx, rax
	cmp r14, rcx
	jb 22f
	jmp 23f
22:
	mov rcx, r14
23:
	mov rdx, rbx
	add rdx, 288
	add rdx, rax
	mov r10d, 0
	test rcx, rcx
	je 24f
26:
	movzx eax, BYTE PTR [r13+r10*1]
	mov BYTE PTR [rdx+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 26b
	jmp 25f
24:
25:
	add r13, rcx
	mov r8d, 0
	sub r14, rcx
	je 27f
	mov r8d, 1
	jmp 28f
27:
28:
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, rbx
	add rdx, 272
	mov rcx, rbx
	add rcx, 288
	mov r9, r15
	call {vg_cmac_aes_update_aesni}
	mov r12d, 0
	test r14, r14
	je 29f
	mov r12, r14
	sub r12, 1
	mov rax, r12
	and rax, 15
	sub r12, rax
	jmp 210f
29:
210:
	mov r8, r12
	shr r8, 4
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, rbx
	add rdx, 272
	mov rcx, r13
	mov r9, r15
	call {vg_cmac_aes_update_aesni}
	add r13, r12
	sub r14, r12
	mov rdx, rbx
	add rdx, 288
	mov rcx, r14
	mov r10d, 0
	test rcx, rcx
	je 211f
213:
	movzx eax, BYTE PTR [r13+r10*1]
	mov BYTE PTR [rdx+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 213b
	jmp 212f
211:
212:
	mov rbx, QWORD PTR [r15+2176]
	mov rbp, QWORD PTR [r15+2184]
	mov r12, QWORD PTR [r15+2192]
	mov r13, QWORD PTR [r15+2200]
	mov r14, QWORD PTR [r15+2208]
	mov r15, QWORD PTR [r15+2216]
	lea rsp, [rsp+2312]
	ret
	.p2align 6

vg_cmac_aes_absorb_aesni_cbc:
	lea rsp, [rsp-2312]
	mov r9, rsp
	add r9, 8
	mov QWORD PTR [r9+2176], rbx
	mov QWORD PTR [r9+2184], rbp
	mov QWORD PTR [r9+2192], r12
	mov QWORD PTR [r9+2200], r13
	mov QWORD PTR [r9+2208], r14
	mov QWORD PTR [r9+2216], r15
	mov rbx, rdi
	mov rbp, rsi
	mov r13, rcx
	mov r14, r8
	mov r15, r9
	test rdx, rdx
	je 20f
	mov rax, rdx
	sub rax, 1
	and rax, 15
	add rax, 1
	jmp 21f
20:
	mov eax, 0
21:
	mov ecx, 16
	sub rcx, rax
	cmp r14, rcx
	jb 22f
	jmp 23f
22:
	mov rcx, r14
23:
	mov rdx, rbx
	add rdx, 288
	add rdx, rax
	mov r10d, 0
	test rcx, rcx
	je 24f
26:
	movzx eax, BYTE PTR [r13+r10*1]
	mov BYTE PTR [rdx+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 26b
	jmp 25f
24:
25:
	add r13, rcx
	mov r8d, 0
	sub r14, rcx
	je 27f
	mov r8d, 1
	jmp 28f
27:
28:
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, rbx
	add rdx, 272
	mov rcx, rbx
	add rcx, 288
	mov r9, r15
	call {vg_cmac_aes_update_aesni_cbc}
	mov r12d, 0
	test r14, r14
	je 29f
	mov r12, r14
	sub r12, 1
	mov rax, r12
	and rax, 15
	sub r12, rax
	jmp 210f
29:
210:
	mov r8, r12
	shr r8, 4
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, rbx
	add rdx, 272
	mov rcx, r13
	mov r9, r15
	call {vg_cmac_aes_update_aesni_cbc}
	add r13, r12
	sub r14, r12
	mov rdx, rbx
	add rdx, 288
	mov rcx, r14
	mov r10d, 0
	test rcx, rcx
	je 211f
213:
	movzx eax, BYTE PTR [r13+r10*1]
	mov BYTE PTR [rdx+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 213b
	jmp 212f
211:
212:
	mov rbx, QWORD PTR [r15+2176]
	mov rbp, QWORD PTR [r15+2184]
	mov r12, QWORD PTR [r15+2192]
	mov r13, QWORD PTR [r15+2200]
	mov r14, QWORD PTR [r15+2208]
	mov r15, QWORD PTR [r15+2216]
	lea rsp, [rsp+2312]
	ret
	.p2align 6

vg_cmac_aes_absorb:
	lea rsp, [rsp-2312]
	mov r9, rsp
	add r9, 8
	mov QWORD PTR [r9+2176], rbx
	mov QWORD PTR [r9+2184], rbp
	mov QWORD PTR [r9+2192], r12
	mov QWORD PTR [r9+2200], r13
	mov QWORD PTR [r9+2208], r14
	mov QWORD PTR [r9+2216], r15
	mov rbx, rdi
	mov rbp, rsi
	mov r13, rcx
	mov r14, r8
	mov r15, r9
	test rdx, rdx
	je 20f
	mov rax, rdx
	sub rax, 1
	and rax, 15
	add rax, 1
	jmp 21f
20:
	mov eax, 0
21:
	mov ecx, 16
	sub rcx, rax
	cmp r14, rcx
	jb 22f
	jmp 23f
22:
	mov rcx, r14
23:
	mov rdx, rbx
	add rdx, 288
	add rdx, rax
	mov r10d, 0
	test rcx, rcx
	je 24f
26:
	movzx eax, BYTE PTR [r13+r10*1]
	mov BYTE PTR [rdx+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 26b
	jmp 25f
24:
25:
	add r13, rcx
	mov r8d, 0
	sub r14, rcx
	je 27f
	mov r8d, 1
	jmp 28f
27:
28:
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, rbx
	add rdx, 272
	mov rcx, rbx
	add rcx, 288
	mov r9, r15
	call {vg_cmac_aes_update}
	mov r12d, 0
	test r14, r14
	je 29f
	mov r12, r14
	sub r12, 1
	mov rax, r12
	and rax, 15
	sub r12, rax
	jmp 210f
29:
210:
	mov r8, r12
	shr r8, 4
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, rbx
	add rdx, 272
	mov rcx, r13
	mov r9, r15
	call {vg_cmac_aes_update}
	add r13, r12
	sub r14, r12
	mov rdx, rbx
	add rdx, 288
	mov rcx, r14
	mov r10d, 0
	test rcx, rcx
	je 211f
213:
	movzx eax, BYTE PTR [r13+r10*1]
	mov BYTE PTR [rdx+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 213b
	jmp 212f
211:
212:
	mov rbx, QWORD PTR [r15+2176]
	mov rbp, QWORD PTR [r15+2184]
	mov r12, QWORD PTR [r15+2192]
	mov r13, QWORD PTR [r15+2200]
	mov r14, QWORD PTR [r15+2208]
	mov r15, QWORD PTR [r15+2216]
	lea rsp, [rsp+2312]
	ret
	.p2align 6

vg_cmac_aes_absorb_vaes:
	lea rsp, [rsp-2312]
	mov r9, rsp
	add r9, 8
	mov QWORD PTR [r9+2176], rbx
	mov QWORD PTR [r9+2184], rbp
	mov QWORD PTR [r9+2192], r12
	mov QWORD PTR [r9+2200], r13
	mov QWORD PTR [r9+2208], r14
	mov QWORD PTR [r9+2216], r15
	mov rbx, rdi
	mov rbp, rsi
	mov r13, rcx
	mov r14, r8
	mov r15, r9
	test rdx, rdx
	je 20f
	mov rax, rdx
	sub rax, 1
	and rax, 15
	add rax, 1
	jmp 21f
20:
	mov eax, 0
21:
	mov ecx, 16
	sub rcx, rax
	cmp r14, rcx
	jb 22f
	jmp 23f
22:
	mov rcx, r14
23:
	mov rdx, rbx
	add rdx, 288
	add rdx, rax
	mov r10d, 0
	test rcx, rcx
	je 24f
26:
	movzx eax, BYTE PTR [r13+r10*1]
	mov BYTE PTR [rdx+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 26b
	jmp 25f
24:
25:
	add r13, rcx
	mov r8d, 0
	sub r14, rcx
	je 27f
	mov r8d, 1
	jmp 28f
27:
28:
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, rbx
	add rdx, 272
	mov rcx, rbx
	add rcx, 288
	mov r9, r15
	call {vg_cmac_aes_update_vaes}
	mov r12d, 0
	test r14, r14
	je 29f
	mov r12, r14
	sub r12, 1
	mov rax, r12
	and rax, 15
	sub r12, rax
	jmp 210f
29:
210:
	mov r8, r12
	shr r8, 4
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, rbx
	add rdx, 272
	mov rcx, r13
	mov r9, r15
	call {vg_cmac_aes_update_vaes}
	add r13, r12
	sub r14, r12
	mov rdx, rbx
	add rdx, 288
	mov rcx, r14
	mov r10d, 0
	test rcx, rcx
	je 211f
213:
	movzx eax, BYTE PTR [r13+r10*1]
	mov BYTE PTR [rdx+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 213b
	jmp 212f
211:
212:
	mov rbx, QWORD PTR [r15+2176]
	mov rbp, QWORD PTR [r15+2184]
	mov r12, QWORD PTR [r15+2192]
	mov r13, QWORD PTR [r15+2200]
	mov r14, QWORD PTR [r15+2208]
	mov r15, QWORD PTR [r15+2216]
	lea rsp, [rsp+2312]
	ret
	.p2align 6
