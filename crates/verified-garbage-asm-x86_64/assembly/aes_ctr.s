// The functions of `src/aes_ctr.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ctr_aesni:
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
	mov eax, DWORD PTR [r12+12]
	bswap eax
	movabs rcx, 4294967296
	sub rcx, rax
	cmp r14, rcx
	cmovb rcx, r14
	mov QWORD PTR [r15+2048], rcx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r12
	mov r8, rcx
	mov rcx, r13
	mov r9, r15
	call {vg_aes_ctr32_aesni}
	mov rax, QWORD PTR [r15+2048]
	sub r14, rax
	shl rax, 4
	add r13, rax
	mov eax, DWORD PTR [r12+12]
	test eax, eax
	je 23f
	jmp 24f
23:
	mov rax, QWORD PTR [r12+8]
	bswap rax
	mov rcx, QWORD PTR [r12]
	bswap rcx
	movabs rdx, 4294967296
	add rax, rdx
	adc rcx, 0
	bswap rax
	bswap rcx
	mov QWORD PTR [r12+8], rax
	mov QWORD PTR [r12], rcx
24:
	test r14, r14
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

vg_aes_ctr_final_aesni:
	lea rsp, [rsp-80]
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
	call {vg_aes_ctr_aesni}
	test r14, r14
	je 20f
	mov rax, QWORD PTR [rsp+8]
	mov r10d, 0
	mov QWORD PTR [rax+48], r10
	mov QWORD PTR [rax+56], r10
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r12
	mov rcx, rax
	add rcx, 48
	mov r8d, 1
	mov r9, r15
	call {vg_aes_ctr_aesni}
	mov rax, QWORD PTR [rsp+8]
	add rax, 48
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
	mov QWORD PTR [rsp+64], r11
	mov QWORD PTR [rsp+72], r11
	lea rsp, [rsp+80]
	ret
	.p2align 6

vg_aes_ctr:
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
	mov eax, DWORD PTR [r12+12]
	bswap eax
	movabs rcx, 4294967296
	sub rcx, rax
	cmp r14, rcx
	cmovb rcx, r14
	mov QWORD PTR [r15+2048], rcx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r12
	mov r8, rcx
	mov rcx, r13
	mov r9, r15
	call {vg_aes_ctr32}
	mov rax, QWORD PTR [r15+2048]
	sub r14, rax
	shl rax, 4
	add r13, rax
	mov eax, DWORD PTR [r12+12]
	test eax, eax
	je 23f
	jmp 24f
23:
	mov rax, QWORD PTR [r12+8]
	bswap rax
	mov rcx, QWORD PTR [r12]
	bswap rcx
	movabs rdx, 4294967296
	add rax, rdx
	adc rcx, 0
	bswap rax
	bswap rcx
	mov QWORD PTR [r12+8], rax
	mov QWORD PTR [r12], rcx
24:
	test r14, r14
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

vg_aes_ctr_final:
	lea rsp, [rsp-80]
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
	call {vg_aes_ctr}
	test r14, r14
	je 20f
	mov rax, QWORD PTR [rsp+8]
	mov r10d, 0
	mov QWORD PTR [rax+48], r10
	mov QWORD PTR [rax+56], r10
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r12
	mov rcx, rax
	add rcx, 48
	mov r8d, 1
	mov r9, r15
	call {vg_aes_ctr}
	mov rax, QWORD PTR [rsp+8]
	add rax, 48
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
	mov QWORD PTR [rsp+64], r11
	mov QWORD PTR [rsp+72], r11
	lea rsp, [rsp+80]
	ret
	.p2align 6

vg_aes_ctr_vaes:
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
	mov eax, DWORD PTR [r12+12]
	bswap eax
	movabs rcx, 4294967296
	sub rcx, rax
	cmp r14, rcx
	cmovb rcx, r14
	mov QWORD PTR [r15+2048], rcx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r12
	mov r8, rcx
	mov rcx, r13
	mov r9, r15
	call {vg_aes_ctr32_vaes}
	mov rax, QWORD PTR [r15+2048]
	sub r14, rax
	shl rax, 4
	add r13, rax
	mov eax, DWORD PTR [r12+12]
	test eax, eax
	je 23f
	jmp 24f
23:
	mov rax, QWORD PTR [r12+8]
	bswap rax
	mov rcx, QWORD PTR [r12]
	bswap rcx
	movabs rdx, 4294967296
	add rax, rdx
	adc rcx, 0
	bswap rax
	bswap rcx
	mov QWORD PTR [r12+8], rax
	mov QWORD PTR [r12], rcx
24:
	test r14, r14
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

vg_aes_ctr_final_vaes:
	lea rsp, [rsp-80]
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
	call {vg_aes_ctr_vaes}
	test r14, r14
	je 20f
	mov rax, QWORD PTR [rsp+8]
	mov r10d, 0
	mov QWORD PTR [rax+48], r10
	mov QWORD PTR [rax+56], r10
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r12
	mov rcx, rax
	add rcx, 48
	mov r8d, 1
	mov r9, r15
	call {vg_aes_ctr_vaes}
	mov rax, QWORD PTR [rsp+8]
	add rax, 48
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
	mov QWORD PTR [rsp+64], r11
	mov QWORD PTR [rsp+72], r11
	lea rsp, [rsp+80]
	ret
	.p2align 6
