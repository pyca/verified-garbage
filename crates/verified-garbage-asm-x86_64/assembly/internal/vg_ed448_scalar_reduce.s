// The functions of `src/internal/vg_ed448_scalar_reduce.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed448_scalar_reduce:
	mov QWORD PTR [rdx], rbx
	mov QWORD PTR [rdx+8], rbp
	mov QWORD PTR [rdx+16], r12
	mov QWORD PTR [rdx+24], r13
	mov QWORD PTR [rdx+32], r14
	mov QWORD PTR [rdx+40], r15
	mov QWORD PTR [rdx+48], rdi
	mov rdi, rdx
	movabs r8, -2556006723728458995
	movabs r9, -2408513697996967766
	movabs r10, 4301259484579875183
	movabs r11, 2201345046
	movabs r12, 0
	movabs r13, 0
	movabs r14, -4611686018427387904
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov QWORD PTR [rdi+160], r12
	mov QWORD PTR [rdi+168], r13
	mov QWORD PTR [rdi+176], r14
	movzx r8d, BYTE PTR [rsi+112]
	movzx eax, BYTE PTR [rsi+113]
	ror rax, 56
	add r8, rax
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov ebx, 112
20:
	sub rbx, 8
	mov rax, QWORD PTR [rsi+rbx*1]
	mov rcx, r13
	shr rcx, 62
	mov rbp, r14
	ror rbp, 62
	add rcx, rbp
	movabs rbp, 4611686018427387903
	and r13, rbp
	mov r14, r13
	mov r13, r12
	mov r12, r11
	mov r11, r10
	mov r10, r9
	mov r9, r8
	mov r8, rax
	mov ebp, 0
	movabs rax, -2556006723728458995
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	movabs rax, -2408513697996967766
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	movabs rax, 4301259484579875183
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	movabs rax, 2201345046
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	adc r14, 0
	mov QWORD PTR [rdi+192], r8
	mov QWORD PTR [rdi+200], r9
	mov QWORD PTR [rdi+208], r10
	mov QWORD PTR [rdi+216], r11
	mov QWORD PTR [rdi+224], r12
	mov QWORD PTR [rdi+232], r13
	mov QWORD PTR [rdi+240], r14
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	adc r12, QWORD PTR [rdi+160]
	adc r13, QWORD PTR [rdi+168]
	adc r14, QWORD PTR [rdi+176]
	sbb r15, r15
	mov rax, QWORD PTR [rdi+192]
	xor r8, rax
	and r8, r15
	xor r8, rax
	mov rax, QWORD PTR [rdi+200]
	xor r9, rax
	and r9, r15
	xor r9, rax
	mov rax, QWORD PTR [rdi+208]
	xor r10, rax
	and r10, r15
	xor r10, rax
	mov rax, QWORD PTR [rdi+216]
	xor r11, rax
	and r11, r15
	xor r11, rax
	mov rax, QWORD PTR [rdi+224]
	xor r12, rax
	and r12, r15
	xor r12, rax
	mov rax, QWORD PTR [rdi+232]
	xor r13, rax
	and r13, r15
	xor r13, rax
	mov rax, QWORD PTR [rdi+240]
	xor r14, rax
	and r14, r15
	xor r14, rax
	test rbx, rbx
	jne 20b
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [rax], r8
	mov QWORD PTR [rax+8], r9
	mov QWORD PTR [rax+16], r10
	mov QWORD PTR [rax+24], r11
	mov QWORD PTR [rax+32], r12
	mov QWORD PTR [rax+40], r13
	mov QWORD PTR [rax+48], r14
	mov ecx, 0
	mov BYTE PTR [rax+56], cl
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	ret
	.p2align 6
