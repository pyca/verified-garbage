// The functions of `src/internal/vg_poly1305_finalize_scratch.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_poly1305_finalize_scratch:
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
	ret
	.p2align 6
