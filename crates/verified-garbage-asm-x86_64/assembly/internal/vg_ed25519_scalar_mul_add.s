// The functions of `src/internal/vg_ed25519_scalar_mul_add.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed25519_scalar_mul_add:
	mov QWORD PTR [r8], rbx
	mov QWORD PTR [r8+8], rbp
	mov QWORD PTR [r8+16], r12
	mov QWORD PTR [r8+24], r13
	mov QWORD PTR [r8+32], r14
	mov QWORD PTR [r8+40], r15
	mov rbx, rdi
	mov rdi, r8
	mov r8, QWORD PTR [rdx]
	mov r9, QWORD PTR [rdx+8]
	mov r10, QWORD PTR [rdx+16]
	mov r11, QWORD PTR [rdx+24]
	mov QWORD PTR [rdi+64], r8
	mov QWORD PTR [rdi+72], r9
	mov QWORD PTR [rdi+80], r10
	mov QWORD PTR [rdi+88], r11
	mov r8, QWORD PTR [rcx]
	mov r9, QWORD PTR [rcx+8]
	mov r10, QWORD PTR [rcx+16]
	mov r11, QWORD PTR [rcx+24]
	mov QWORD PTR [rdi+96], r8
	mov QWORD PTR [rdi+104], r9
	mov QWORD PTR [rdi+112], r10
	mov QWORD PTR [rdi+120], r11
	mov r8, QWORD PTR [rsi]
	mov r9, QWORD PTR [rsi+8]
	mov r10, QWORD PTR [rsi+16]
	mov r11, QWORD PTR [rsi+24]
	mov rcx, QWORD PTR [rdi+64]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov r12, rbp
	mov rcx, QWORD PTR [rdi+72]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov r13, rbp
	mov rcx, QWORD PTR [rdi+80]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov r14, rbp
	mov rcx, QWORD PTR [rdi+88]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+96]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+104]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+112]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+120]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov r15, rbp
	mov QWORD PTR [rdi+128], r8
	mov QWORD PTR [rdi+136], r9
	mov QWORD PTR [rdi+144], r10
	mov QWORD PTR [rdi+152], r11
	mov QWORD PTR [rdi+160], r12
	mov QWORD PTR [rdi+168], r13
	mov QWORD PTR [rdi+176], r14
	mov QWORD PTR [rdi+184], r15
	mov rsi, rdi
	add rsi, 128
	mov QWORD PTR [rdi+48], rbx
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov ebx, 64
20:
	sub rbx, 8
	mov rax, QWORD PTR [rsi+rbx*1]
	mov rbp, r10
	shr rbp, 60
	mov rcx, r11
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	or rbp, rcx
	mov r12, r11
	shr r12, 60
	movabs rcx, 1152921504606846975
	and r10, rcx
	mov r11, r10
	mov r10, r9
	mov r9, r8
	mov r8, rax
	mov rax, rbp
	movabs rcx, 6346243789798364141
	mul rcx
	mov r13, rax
	mov r14, rdx
	mov rax, rbp
	movabs rcx, 1503914060200516822
	mul rcx
	add r14, rax
	adc rdx, 0
	mov r15, rdx
	mov ecx, 0
	sub rcx, r12
	movabs rax, 6346243789798364141
	and rax, rcx
	movabs rdx, 1503914060200516822
	and rdx, rcx
	add r14, rax
	adc r15, rdx
	movabs rax, 6346243789798364141
	sub rax, r13
	movabs rcx, 1503914060200516822
	sbb rcx, r14
	mov edx, 0
	sbb rdx, r15
	movabs rbp, 1152921504606846976
	sbb rbp, 0
	add r8, rax
	adc r9, rcx
	adc r10, rdx
	adc r11, rbp
	mov r12, r8
	mov r13, r9
	mov r14, r10
	mov r15, r11
	movabs rcx, 6346243789798364141
	sub r8, rcx
	movabs rcx, 1503914060200516822
	sbb r9, rcx
	sbb r10, 0
	movabs rcx, 1152921504606846976
	sbb r11, rcx
	sbb rax, rax
	xor r12, r8
	and r12, rax
	xor r8, r12
	xor r13, r9
	and r13, rax
	xor r9, r13
	xor r14, r10
	and r14, rax
	xor r10, r14
	xor r15, r11
	and r15, rax
	xor r11, r15
	test rbx, rbx
	jne 20b
	mov rdx, rdi
	mov rdi, QWORD PTR [rdx+48]
	mov rbx, QWORD PTR [rdx]
	mov rbp, QWORD PTR [rdx+8]
	mov r12, QWORD PTR [rdx+16]
	mov r13, QWORD PTR [rdx+24]
	mov r14, QWORD PTR [rdx+32]
	mov r15, QWORD PTR [rdx+40]
	mov QWORD PTR [rdi], r8
	mov QWORD PTR [rdi+8], r9
	mov QWORD PTR [rdi+16], r10
	mov QWORD PTR [rdi+24], r11
	ret
	.p2align 6
