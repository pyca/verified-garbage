// The functions of `src/aes_ofb.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ofb_vaes:
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
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r12
	mov ecx, 1
	mov r8, r15
	call {vg_aes_encrypt_blocks_vaes}
	mov rax, QWORD PTR [r13]
	xor rax, QWORD PTR [r12]
	mov QWORD PTR [r13], rax
	mov rax, QWORD PTR [r13+8]
	xor rax, QWORD PTR [r12+8]
	mov QWORD PTR [r13+8], rax
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
	lea rsp, [rsp-8]
	lea rsp, [rsp+8]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r10d, r10d
	ret
	.p2align 6

vg_aes_ofb_final_vaes:
	lea rsp, [rsp-64]
	mov rax, rsp
	add rax, 16
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [rax], rbx
	mov QWORD PTR [rax+8], rbp
	mov QWORD PTR [rax+16], r12
	mov QWORD PTR [rax+24], r13
	mov QWORD PTR [rax+32], r14
	mov QWORD PTR [rax+40], r15
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rdx
	mov r15, r9
	mov r14, r8
	and r14, 15
	mov r13, r8
	sub r13, r14
	add r13, rcx
	shr r8, 4
	call {vg_aes_ofb_vaes_core}
	test r14, r14
	je 20f
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r12
	mov ecx, 1
	mov r8, r15
	call {vg_aes_encrypt_blocks_vaes}
	mov rax, r12
22:
	movzx r10d, BYTE PTR [rax]
	movzx ecx, BYTE PTR [r13]
	xor rcx, r10
	mov BYTE PTR [r13], cl
	add rax, 1
	add r13, 1
	sub r14, 1
	jne 22b
	jmp 21f
20:
21:
	mov rax, QWORD PTR [rsp+8]
	mov rbx, QWORD PTR [rax]
	mov rbp, QWORD PTR [rax+8]
	mov r12, QWORD PTR [rax+16]
	mov r13, QWORD PTR [rax+24]
	mov r14, QWORD PTR [rax+32]
	mov r15, QWORD PTR [rax+40]
	mov r11d, 0
	mov QWORD PTR [rsp+16], r11
	mov QWORD PTR [rsp+24], r11
	mov QWORD PTR [rsp+32], r11
	mov QWORD PTR [rsp+40], r11
	mov QWORD PTR [rsp+48], r11
	mov QWORD PTR [rsp+56], r11
	lea rsp, [rsp+64]
	ret
	.p2align 6

vg_aes_ofb_aesni:
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
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r12
	mov ecx, 1
	mov r8, r15
	call {vg_aes_encrypt_blocks_aesni}
	mov rax, QWORD PTR [r13]
	xor rax, QWORD PTR [r12]
	mov QWORD PTR [r13], rax
	mov rax, QWORD PTR [r13+8]
	xor rax, QWORD PTR [r12+8]
	mov QWORD PTR [r13+8], rax
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
	lea rsp, [rsp-8]
	lea rsp, [rsp+8]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r10d, r10d
	ret
	.p2align 6

vg_aes_ofb_final_aesni:
	lea rsp, [rsp-64]
	mov rax, rsp
	add rax, 16
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [rax], rbx
	mov QWORD PTR [rax+8], rbp
	mov QWORD PTR [rax+16], r12
	mov QWORD PTR [rax+24], r13
	mov QWORD PTR [rax+32], r14
	mov QWORD PTR [rax+40], r15
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rdx
	mov r15, r9
	mov r14, r8
	and r14, 15
	mov r13, r8
	sub r13, r14
	add r13, rcx
	shr r8, 4
	call {vg_aes_ofb_aesni_core}
	test r14, r14
	je 20f
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r12
	mov ecx, 1
	mov r8, r15
	call {vg_aes_encrypt_blocks_aesni}
	mov rax, r12
22:
	movzx r10d, BYTE PTR [rax]
	movzx ecx, BYTE PTR [r13]
	xor rcx, r10
	mov BYTE PTR [r13], cl
	add rax, 1
	add r13, 1
	sub r14, 1
	jne 22b
	jmp 21f
20:
21:
	mov rax, QWORD PTR [rsp+8]
	mov rbx, QWORD PTR [rax]
	mov rbp, QWORD PTR [rax+8]
	mov r12, QWORD PTR [rax+16]
	mov r13, QWORD PTR [rax+24]
	mov r14, QWORD PTR [rax+32]
	mov r15, QWORD PTR [rax+40]
	mov r11d, 0
	mov QWORD PTR [rsp+16], r11
	mov QWORD PTR [rsp+24], r11
	mov QWORD PTR [rsp+32], r11
	mov QWORD PTR [rsp+40], r11
	mov QWORD PTR [rsp+48], r11
	mov QWORD PTR [rsp+56], r11
	lea rsp, [rsp+64]
	ret
	.p2align 6

vg_aes_ofb:
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
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r12
	mov ecx, 1
	mov r8, r15
	call {vg_aes_encrypt_blocks}
	mov rax, QWORD PTR [r13]
	xor rax, QWORD PTR [r12]
	mov QWORD PTR [r13], rax
	mov rax, QWORD PTR [r13+8]
	xor rax, QWORD PTR [r12+8]
	mov QWORD PTR [r13+8], rax
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
	pxor xmm0, xmm0
	xor r11d, r11d
	lea rsp, [rsp-8]
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+8]
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

vg_aes_ofb_final:
	lea rsp, [rsp-64]
	mov rax, rsp
	add rax, 16
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [rax], rbx
	mov QWORD PTR [rax+8], rbp
	mov QWORD PTR [rax+16], r12
	mov QWORD PTR [rax+24], r13
	mov QWORD PTR [rax+32], r14
	mov QWORD PTR [rax+40], r15
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rdx
	mov r15, r9
	mov r14, r8
	and r14, 15
	mov r13, r8
	sub r13, r14
	add r13, rcx
	shr r8, 4
	call {vg_aes_ofb_core}
	test r14, r14
	je 20f
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r12
	mov ecx, 1
	mov r8, r15
	call {vg_aes_encrypt_blocks}
	mov rax, r12
22:
	movzx r10d, BYTE PTR [rax]
	movzx ecx, BYTE PTR [r13]
	xor rcx, r10
	mov BYTE PTR [r13], cl
	add rax, 1
	add r13, 1
	sub r14, 1
	jne 22b
	jmp 21f
20:
21:
	mov rax, QWORD PTR [rsp+8]
	mov rbx, QWORD PTR [rax]
	mov rbp, QWORD PTR [rax+8]
	mov r12, QWORD PTR [rax+16]
	mov r13, QWORD PTR [rax+24]
	mov r14, QWORD PTR [rax+32]
	mov r15, QWORD PTR [rax+40]
	mov r11d, 0
	mov QWORD PTR [rsp+16], r11
	mov QWORD PTR [rsp+24], r11
	mov QWORD PTR [rsp+32], r11
	mov QWORD PTR [rsp+40], r11
	mov QWORD PTR [rsp+48], r11
	mov QWORD PTR [rsp+56], r11
	lea rsp, [rsp+64]
	ret
	.p2align 6
