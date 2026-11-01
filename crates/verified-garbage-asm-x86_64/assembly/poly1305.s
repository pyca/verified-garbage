// The functions of `src/poly1305.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_poly1305_init:
	mov rax, QWORD PTR [rsi]
	mov rcx, QWORD PTR [rsi+8]
	mov rdx, QWORD PTR [rsi+16]
	mov r8, QWORD PTR [rsi+24]
	mov QWORD PTR [rdi+24], rax
	mov QWORD PTR [rdi+32], rcx
	mov QWORD PTR [rdi+40], rdx
	mov QWORD PTR [rdi+48], r8
	mov eax, 0
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rax
	mov QWORD PTR [rdi+16], rax
	ret
	.p2align 6

vg_poly1305_finalize:
	lea rsp, [rsp-136]
	mov rcx, rsp
	add rcx, 8
	mov rcx, rdx
	mov rdx, rsi
	and rdx, 15
	mov QWORD PTR [rdi+72], rbx
	mov QWORD PTR [rdi+80], rbp
	mov QWORD PTR [rdi+88], r12
	mov QWORD PTR [rdi+96], r13
	mov QWORD PTR [rdi+104], r14
	mov QWORD PTR [rdi+112], r15
	movabs rax, 1152921487695413247
	mov r8, QWORD PTR [rdi+24]
	and r8, rax
	movabs rax, 1152921487695413244
	mov r9, QWORD PTR [rdi+32]
	and r9, rax
	mov r10, r9
	shr r10, 2
	add r10, r9
	mov r11, QWORD PTR [rdi]
	mov rbx, QWORD PTR [rdi+8]
	mov rbp, QWORD PTR [rdi+16]
	test rdx, rdx
	je 20f
	mov eax, 0
	mov r12, rdx
22:
	mov BYTE PTR [rdi+r12*1+56], al
	add r12, 1
	cmp r12, 16
	jne 22b
	mov eax, 1
	mov BYTE PTR [rdi+rdx*1+56], al
	add r11, QWORD PTR [rdi+56]
	adc rbx, QWORD PTR [rdi+64]
	adc rbp, 0
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, r11
	mul r8
	mov r11, rax
	mov r13, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbx
	mul r10
	add r11, rax
	adc r13, rdx
	mov rbx, rbp
	imul rbx, r10
	add r14, rbx
	adc r15, 0
	mov rbx, r13
	imul rbp, r8
	add rbx, r14
	adc r15, rbp
	mov rax, r15
	and rax, -4
	mov rbp, r15
	and rbp, 3
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	jmp 21f
20:
21:
	mov rax, r11
	add rax, 5
	mov rdx, rbx
	adc rdx, 0
	mov r12, rbp
	adc r12, 0
	mov r13, r12
	shr r13, 2
	mov r14d, 0
	sub r14, r13
	and r12, 3
	xor rax, r11
	and rax, r14
	xor r11, rax
	xor rdx, rbx
	and rdx, r14
	xor rbx, rdx
	xor r12, rbp
	and r12, r14
	xor rbp, r12
	add r11, QWORD PTR [rdi+40]
	adc rbx, QWORD PTR [rdi+48]
	mov QWORD PTR [rcx], r11
	mov QWORD PTR [rcx+8], rbx
	mov rbx, QWORD PTR [rdi+72]
	mov rbp, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+88]
	mov r13, QWORD PTR [rdi+96]
	mov r14, QWORD PTR [rdi+104]
	mov r15, QWORD PTR [rdi+112]
	lea rsp, [rsp+136]
	ret
	.p2align 6

vg_poly1305_update_avx2:
	lea rsp, [rsp-136]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8], rbx
	mov QWORD PTR [r8+8], rbp
	mov QWORD PTR [r8+16], r12
	mov QWORD PTR [r8+24], r13
	mov QWORD PTR [r8+32], r14
	mov QWORD PTR [r8+40], r15
	mov r12, rsi
	and r12, 15
	mov rsi, rdx
	test r12, r12
	je 20f
	mov eax, 16
	sub rax, r12
	cmp rcx, rax
	jb 22f
	jmp 23f
22:
	mov rax, rcx
23:
	sub rcx, rax
	test rax, rax
	je 24f
26:
	movzx r13d, BYTE PTR [rsi]
	mov BYTE PTR [rdi+r12*1+56], r13b
	add rsi, 1
	add r12, 1
	sub rax, 1
	jne 26b
	jmp 25f
24:
25:
	cmp r12, 16
	je 27f
	jmp 28f
27:
	mov QWORD PTR [rdi+72], rsi
	mov QWORD PTR [rdi+80], rcx
	mov QWORD PTR [rdi+88], r8
	movabs rax, 1152921487695413247
	mov r8, QWORD PTR [rdi+24]
	and r8, rax
	movabs rax, 1152921487695413244
	mov r9, QWORD PTR [rdi+32]
	and r9, rax
	mov r10, r9
	shr r10, 2
	add r10, r9
	mov r11, QWORD PTR [rdi]
	mov rbx, QWORD PTR [rdi+8]
	mov rbp, QWORD PTR [rdi+16]
	add r11, QWORD PTR [rdi+56]
	adc rbx, QWORD PTR [rdi+64]
	adc rbp, 1
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, r11
	mul r8
	mov r11, rax
	mov r13, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbx
	mul r10
	add r11, rax
	adc r13, rdx
	mov rbx, rbp
	imul rbx, r10
	add r14, rbx
	adc r15, 0
	mov rbx, r13
	imul rbp, r8
	add rbx, r14
	adc r15, rbp
	mov rax, r15
	and rax, -4
	mov rbp, r15
	and rbp, 3
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	mov rax, r11
	add rax, 5
	mov rdx, rbx
	adc rdx, 0
	mov r12, rbp
	adc r12, 0
	mov r13, r12
	shr r13, 2
	mov r14d, 0
	sub r14, r13
	and r12, 3
	xor rax, r11
	and rax, r14
	xor r11, rax
	xor rdx, rbx
	and rdx, r14
	xor rbx, rdx
	xor r12, rbp
	and r12, r14
	xor rbp, r12
	mov QWORD PTR [rdi], r11
	mov QWORD PTR [rdi+8], rbx
	mov QWORD PTR [rdi+16], rbp
	mov rsi, QWORD PTR [rdi+72]
	mov rcx, QWORD PTR [rdi+80]
	mov r8, QWORD PTR [rdi+88]
28:
	jmp 21f
20:
21:
	mov r15, r8
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rcx
	mov rdx, rcx
	shr rdx, 4
	cmp rcx, 16
	jb 29f
	call {vg_poly1305_blocks_avx2}
	jmp 210f
29:
210:
	mov rdi, rbx
	mov rcx, r12
	and rcx, 15
	mov rsi, r12
	sub rsi, rcx
	add rsi, rbp
	test rcx, rcx
	je 211f
	mov r12d, 0
	mov rax, rcx
213:
	movzx r13d, BYTE PTR [rsi]
	mov BYTE PTR [rdi+r12*1+56], r13b
	add rsi, 1
	add r12, 1
	sub rax, 1
	jne 213b
	jmp 212f
211:
212:
	mov rbx, QWORD PTR [r15]
	mov rbp, QWORD PTR [r15+8]
	mov r12, QWORD PTR [r15+16]
	mov r13, QWORD PTR [r15+24]
	mov r14, QWORD PTR [r15+32]
	mov r15, QWORD PTR [r15+40]
	lea rsp, [rsp+136]
	ret
	.p2align 6

vg_poly1305_update_avx512:
	lea rsp, [rsp-136]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8], rbx
	mov QWORD PTR [r8+8], rbp
	mov QWORD PTR [r8+16], r12
	mov QWORD PTR [r8+24], r13
	mov QWORD PTR [r8+32], r14
	mov QWORD PTR [r8+40], r15
	mov r12, rsi
	and r12, 15
	mov rsi, rdx
	test r12, r12
	je 20f
	mov eax, 16
	sub rax, r12
	cmp rcx, rax
	jb 22f
	jmp 23f
22:
	mov rax, rcx
23:
	sub rcx, rax
	test rax, rax
	je 24f
26:
	movzx r13d, BYTE PTR [rsi]
	mov BYTE PTR [rdi+r12*1+56], r13b
	add rsi, 1
	add r12, 1
	sub rax, 1
	jne 26b
	jmp 25f
24:
25:
	cmp r12, 16
	je 27f
	jmp 28f
27:
	mov QWORD PTR [rdi+72], rsi
	mov QWORD PTR [rdi+80], rcx
	mov QWORD PTR [rdi+88], r8
	movabs rax, 1152921487695413247
	mov r8, QWORD PTR [rdi+24]
	and r8, rax
	movabs rax, 1152921487695413244
	mov r9, QWORD PTR [rdi+32]
	and r9, rax
	mov r10, r9
	shr r10, 2
	add r10, r9
	mov r11, QWORD PTR [rdi]
	mov rbx, QWORD PTR [rdi+8]
	mov rbp, QWORD PTR [rdi+16]
	add r11, QWORD PTR [rdi+56]
	adc rbx, QWORD PTR [rdi+64]
	adc rbp, 1
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, r11
	mul r8
	mov r11, rax
	mov r13, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbx
	mul r10
	add r11, rax
	adc r13, rdx
	mov rbx, rbp
	imul rbx, r10
	add r14, rbx
	adc r15, 0
	mov rbx, r13
	imul rbp, r8
	add rbx, r14
	adc r15, rbp
	mov rax, r15
	and rax, -4
	mov rbp, r15
	and rbp, 3
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	mov rax, r11
	add rax, 5
	mov rdx, rbx
	adc rdx, 0
	mov r12, rbp
	adc r12, 0
	mov r13, r12
	shr r13, 2
	mov r14d, 0
	sub r14, r13
	and r12, 3
	xor rax, r11
	and rax, r14
	xor r11, rax
	xor rdx, rbx
	and rdx, r14
	xor rbx, rdx
	xor r12, rbp
	and r12, r14
	xor rbp, r12
	mov QWORD PTR [rdi], r11
	mov QWORD PTR [rdi+8], rbx
	mov QWORD PTR [rdi+16], rbp
	mov rsi, QWORD PTR [rdi+72]
	mov rcx, QWORD PTR [rdi+80]
	mov r8, QWORD PTR [rdi+88]
28:
	jmp 21f
20:
21:
	mov r15, r8
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rcx
	mov rdx, rcx
	shr rdx, 4
	cmp rcx, 16
	jb 29f
	call {vg_poly1305_blocks_avx512}
	jmp 210f
29:
210:
	mov rdi, rbx
	mov rcx, r12
	and rcx, 15
	mov rsi, r12
	sub rsi, rcx
	add rsi, rbp
	test rcx, rcx
	je 211f
	mov r12d, 0
	mov rax, rcx
213:
	movzx r13d, BYTE PTR [rsi]
	mov BYTE PTR [rdi+r12*1+56], r13b
	add rsi, 1
	add r12, 1
	sub rax, 1
	jne 213b
	jmp 212f
211:
212:
	mov rbx, QWORD PTR [r15]
	mov rbp, QWORD PTR [r15+8]
	mov r12, QWORD PTR [r15+16]
	mov r13, QWORD PTR [r15+24]
	mov r14, QWORD PTR [r15+32]
	mov r15, QWORD PTR [r15+40]
	lea rsp, [rsp+136]
	ret
	.p2align 6

vg_poly1305_update_ifma:
	lea rsp, [rsp-136]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8], rbx
	mov QWORD PTR [r8+8], rbp
	mov QWORD PTR [r8+16], r12
	mov QWORD PTR [r8+24], r13
	mov QWORD PTR [r8+32], r14
	mov QWORD PTR [r8+40], r15
	mov r12, rsi
	and r12, 15
	mov rsi, rdx
	test r12, r12
	je 20f
	mov eax, 16
	sub rax, r12
	cmp rcx, rax
	jb 22f
	jmp 23f
22:
	mov rax, rcx
23:
	sub rcx, rax
	test rax, rax
	je 24f
26:
	movzx r13d, BYTE PTR [rsi]
	mov BYTE PTR [rdi+r12*1+56], r13b
	add rsi, 1
	add r12, 1
	sub rax, 1
	jne 26b
	jmp 25f
24:
25:
	cmp r12, 16
	je 27f
	jmp 28f
27:
	mov QWORD PTR [rdi+72], rsi
	mov QWORD PTR [rdi+80], rcx
	mov QWORD PTR [rdi+88], r8
	movabs rax, 1152921487695413247
	mov r8, QWORD PTR [rdi+24]
	and r8, rax
	movabs rax, 1152921487695413244
	mov r9, QWORD PTR [rdi+32]
	and r9, rax
	mov r10, r9
	shr r10, 2
	add r10, r9
	mov r11, QWORD PTR [rdi]
	mov rbx, QWORD PTR [rdi+8]
	mov rbp, QWORD PTR [rdi+16]
	add r11, QWORD PTR [rdi+56]
	adc rbx, QWORD PTR [rdi+64]
	adc rbp, 1
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, r11
	mul r8
	mov r11, rax
	mov r13, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbx
	mul r10
	add r11, rax
	adc r13, rdx
	mov rbx, rbp
	imul rbx, r10
	add r14, rbx
	adc r15, 0
	mov rbx, r13
	imul rbp, r8
	add rbx, r14
	adc r15, rbp
	mov rax, r15
	and rax, -4
	mov rbp, r15
	and rbp, 3
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	mov rax, r11
	add rax, 5
	mov rdx, rbx
	adc rdx, 0
	mov r12, rbp
	adc r12, 0
	mov r13, r12
	shr r13, 2
	mov r14d, 0
	sub r14, r13
	and r12, 3
	xor rax, r11
	and rax, r14
	xor r11, rax
	xor rdx, rbx
	and rdx, r14
	xor rbx, rdx
	xor r12, rbp
	and r12, r14
	xor rbp, r12
	mov QWORD PTR [rdi], r11
	mov QWORD PTR [rdi+8], rbx
	mov QWORD PTR [rdi+16], rbp
	mov rsi, QWORD PTR [rdi+72]
	mov rcx, QWORD PTR [rdi+80]
	mov r8, QWORD PTR [rdi+88]
28:
	jmp 21f
20:
21:
	mov r15, r8
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rcx
	mov rdx, rcx
	shr rdx, 4
	cmp rcx, 16
	jb 29f
	call {vg_poly1305_blocks_ifma}
	jmp 210f
29:
210:
	mov rdi, rbx
	mov rcx, r12
	and rcx, 15
	mov rsi, r12
	sub rsi, rcx
	add rsi, rbp
	test rcx, rcx
	je 211f
	mov r12d, 0
	mov rax, rcx
213:
	movzx r13d, BYTE PTR [rsi]
	mov BYTE PTR [rdi+r12*1+56], r13b
	add rsi, 1
	add r12, 1
	sub rax, 1
	jne 213b
	jmp 212f
211:
212:
	mov rbx, QWORD PTR [r15]
	mov rbp, QWORD PTR [r15+8]
	mov r12, QWORD PTR [r15+16]
	mov r13, QWORD PTR [r15+24]
	mov r14, QWORD PTR [r15+32]
	mov r15, QWORD PTR [r15+40]
	lea rsp, [rsp+136]
	ret
	.p2align 6

vg_poly1305_update:
	lea rsp, [rsp-136]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8], rbx
	mov QWORD PTR [r8+8], rbp
	mov QWORD PTR [r8+16], r12
	mov QWORD PTR [r8+24], r13
	mov QWORD PTR [r8+32], r14
	mov QWORD PTR [r8+40], r15
	mov r12, rsi
	and r12, 15
	mov rsi, rdx
	test r12, r12
	je 20f
	mov eax, 16
	sub rax, r12
	cmp rcx, rax
	jb 22f
	jmp 23f
22:
	mov rax, rcx
23:
	sub rcx, rax
	test rax, rax
	je 24f
26:
	movzx r13d, BYTE PTR [rsi]
	mov BYTE PTR [rdi+r12*1+56], r13b
	add rsi, 1
	add r12, 1
	sub rax, 1
	jne 26b
	jmp 25f
24:
25:
	cmp r12, 16
	je 27f
	jmp 28f
27:
	mov QWORD PTR [rdi+72], rsi
	mov QWORD PTR [rdi+80], rcx
	mov QWORD PTR [rdi+88], r8
	movabs rax, 1152921487695413247
	mov r8, QWORD PTR [rdi+24]
	and r8, rax
	movabs rax, 1152921487695413244
	mov r9, QWORD PTR [rdi+32]
	and r9, rax
	mov r10, r9
	shr r10, 2
	add r10, r9
	mov r11, QWORD PTR [rdi]
	mov rbx, QWORD PTR [rdi+8]
	mov rbp, QWORD PTR [rdi+16]
	add r11, QWORD PTR [rdi+56]
	adc rbx, QWORD PTR [rdi+64]
	adc rbp, 1
	mov rax, r11
	mul r9
	mov r14, rax
	mov r15, rdx
	mov rax, r11
	mul r8
	mov r11, rax
	mov r13, rdx
	mov rax, rbx
	mul r8
	add r14, rax
	adc r15, rdx
	mov rax, rbx
	mul r10
	add r11, rax
	adc r13, rdx
	mov rbx, rbp
	imul rbx, r10
	add r14, rbx
	adc r15, 0
	mov rbx, r13
	imul rbp, r8
	add rbx, r14
	adc r15, rbp
	mov rax, r15
	and rax, -4
	mov rbp, r15
	and rbp, 3
	shr r15, 2
	add rax, r15
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	mov rax, r11
	add rax, 5
	mov rdx, rbx
	adc rdx, 0
	mov r12, rbp
	adc r12, 0
	mov r13, r12
	shr r13, 2
	mov r14d, 0
	sub r14, r13
	and r12, 3
	xor rax, r11
	and rax, r14
	xor r11, rax
	xor rdx, rbx
	and rdx, r14
	xor rbx, rdx
	xor r12, rbp
	and r12, r14
	xor rbp, r12
	mov QWORD PTR [rdi], r11
	mov QWORD PTR [rdi+8], rbx
	mov QWORD PTR [rdi+16], rbp
	mov rsi, QWORD PTR [rdi+72]
	mov rcx, QWORD PTR [rdi+80]
	mov r8, QWORD PTR [rdi+88]
28:
	jmp 21f
20:
21:
	mov r15, r8
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rcx
	mov rdx, rcx
	shr rdx, 4
	cmp rcx, 16
	jb 29f
	call {vg_poly1305_blocks}
	jmp 210f
29:
210:
	mov rdi, rbx
	mov rcx, r12
	and rcx, 15
	mov rsi, r12
	sub rsi, rcx
	add rsi, rbp
	test rcx, rcx
	je 211f
	mov r12d, 0
	mov rax, rcx
213:
	movzx r13d, BYTE PTR [rsi]
	mov BYTE PTR [rdi+r12*1+56], r13b
	add rsi, 1
	add r12, 1
	sub rax, 1
	jne 213b
	jmp 212f
211:
212:
	mov rbx, QWORD PTR [r15]
	mov rbp, QWORD PTR [r15+8]
	mov r12, QWORD PTR [r15+16]
	mov r13, QWORD PTR [r15+24]
	mov r14, QWORD PTR [r15+32]
	mov r15, QWORD PTR [r15+40]
	lea rsp, [rsp+136]
	ret
	.p2align 6
