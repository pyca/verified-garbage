// The functions of `src/cmac_aes.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cmac_aes_absorb_aesni:
	lea rsp, [rsp-56]
	mov r9, rsp
	add r9, 8
	sub r9, 2176
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
	lea rsp, [rsp+56]
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
	lea rsp, [rsp-72]
	movdqu XMMWORD PTR [rsp+56], xmm0
	movdqu XMMWORD PTR [rsp+40], xmm0
	movdqu XMMWORD PTR [rsp+24], xmm0
	movdqu XMMWORD PTR [rsp+8], xmm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+72]
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

vg_cmac_aes_init_vaes:
	lea rsp, [rsp-168]
	mov rcx, rsp
	add rcx, 8
	sub rcx, 2048
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
	lea rsp, [rsp+168]
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
	lea rsp, [rsp-184]
	vmovdqu YMMWORD PTR [rsp+152], ymm0
	vmovdqu YMMWORD PTR [rsp+120], ymm0
	vmovdqu YMMWORD PTR [rsp+88], ymm0
	vmovdqu YMMWORD PTR [rsp+56], ymm0
	vmovdqu YMMWORD PTR [rsp+24], ymm0
	movdqu XMMWORD PTR [rsp+8], xmm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+184]
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

vg_cmac_aes_finish_vaes:
	lea rsp, [rsp-24]
	mov r8, rsp
	add r8, 8
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rcx], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rcx+8], rax
	mov r9, r8
	sub r9, 2048
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
	lea rsp, [rsp+24]
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
	lea rsp, [rsp-40]
	vmovdqu YMMWORD PTR [rsp+8], ymm0
	lea rsp, [rsp+40]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	ret
	.p2align 6

vg_cmac_aes_init_aesni:
	lea rsp, [rsp-168]
	mov rcx, rsp
	add rcx, 8
	sub rcx, 2048
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
	lea rsp, [rsp+168]
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
	lea rsp, [rsp-184]
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
	lea rsp, [rsp+184]
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

vg_cmac_aes_finish_aesni:
	lea rsp, [rsp-24]
	mov r8, rsp
	add r8, 8
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rcx], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rcx+8], rax
	mov r9, r8
	sub r9, 2048
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
	lea rsp, [rsp+24]
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
	lea rsp, [rsp-40]
	movdqu XMMWORD PTR [rsp+24], xmm0
	movdqu XMMWORD PTR [rsp+8], xmm0
	lea rsp, [rsp+40]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
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
