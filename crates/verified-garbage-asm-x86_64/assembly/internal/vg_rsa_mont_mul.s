// The functions of `src/internal/vg_rsa_mont_mul.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_mont_mul:
	mov edx, edx
	mov ecx, ecx
	mov r8d, r8d
	movq xmm8, rbx
	movq xmm9, rbp
	movq xmm10, r12
	movq xmm11, r13
	movq xmm12, r14
	movq xmm13, r15
	mov rbx, QWORD PTR [rdi+rdx*8+64]
	mov r11, QWORD PTR [rdi+rcx*8+64]
	mov r9, QWORD PTR [rdi+r8*8+64]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov r15, QWORD PTR [rdi+56]
	mov rsi, QWORD PTR [rdi+88]
	cmp r11, r9
	je 20f
	mov eax, 0
	mov r14, 0
22:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 22b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
23:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
24:
	mov rax, QWORD PTR [r9+r14*8]
	mul rcx
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rbp
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rbp, rdx
	add r14, 1
	cmp r14, r12
	jne 24b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [r8]
	mul r15
	mov rcx, rax
	mov rax, QWORD PTR [r10]
	mul rcx
	add rax, QWORD PTR [r8]
	adc rdx, 0
	mov rbp, rdx
	mov r14, 1
25:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rbp
	adc rdx, 0
	mov QWORD PTR [r8+r14*8-8], rax
	mov rbp, rdx
	add r14, 1
	cmp r14, r12
	jne 25b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8-8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov eax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	add r13, 1
	cmp r13, r12
	jne 23b
	mov ebp, 0
	mov r14, 0
26:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 26b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
27:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 27b
	jmp 21f
20:
	movq xmm14, rbx
	movq xmm15, r15
	movq xmm0, r12
	movq xmm1, r8
	movq xmm2, r10
	movq xmm3, rsi
	mov rbx, r12
	add r8, 16
	mov eax, 0
	mov rcx, rbx
	add rcx, rcx
	add rcx, 2
	mov r14d, 0
28:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, rcx
	jne 28b
	mov r10, rbx
	mov ebp, 1
	add r8, 8
29:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
210:
	mov rax, QWORD PTR [r9+r14*8]
	mul r13
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rcx
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rcx, rdx
	add r14, 1
	cmp r14, rbp
	jne 210b
	mov rdx, r13
	mov QWORD PTR [r8+r14*8], rcx
	add r8, 8
	add rbp, 1
	cmp rbp, r10
	jne 29b
	movq r8, xmm1
	add r8, 16
	movq r10, xmm0
	mov r15d, 0
	mov ebp, 0
	mov r14d, 0
211:
	mov rdx, QWORD PTR [r9+rbp*8]
	mov r11, QWORD PTR [r8+r14*8]
	mov r12, QWORD PTR [r8+r14*8+8]
	mov rax, rdx
	mov rsi, rdx
	mul rsi
	mov ebx, 0
	add r11, r11
	adc r12, r12
	adc rbx, 0
	add r11, rax
	adc r12, rdx
	adc rbx, 0
	add r11, r15
	adc r12, 0
	adc rbx, 0
	mov rdx, rsi
	mov QWORD PTR [r8+r14*8], r11
	mov QWORD PTR [r8+r14*8+8], r12
	mov r15, rbx
	add rbp, 1
	add r14, 2
	cmp rbp, r10
	jne 211b
	movq r9, xmm2
	movq rbp, xmm0
	mov r10d, 0
212:
	movq rax, xmm15
	mov rdx, QWORD PTR [r8]
	imul rdx, rax
	mov r13, rdx
	mov ecx, 0
	mov r14d, 0
213:
	mov rax, QWORD PTR [r9+r14*8]
	mul r13
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rcx
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rcx, rdx
	add r14, 1
	cmp r14, rbp
	jne 213b
	mov rdx, r13
	mov rax, QWORD PTR [r8+r14*8]
	mov esi, 0
	add rax, rcx
	adc rsi, 0
	add rax, r10
	adc rsi, 0
	mov QWORD PTR [r8+r14*8], rax
	mov r10, rsi
	add r8, 8
	movq rax, xmm3
	cmp r8, rax
	jne 212b
	mov QWORD PTR [r8+rbp*8], r10
	mov eax, 0
	mov QWORD PTR [r8+rbp*8+8], rax
	movq r12, xmm0
	movq rsi, xmm1
	movq r10, xmm2
	movq rbx, xmm14
	mov ebp, 0
	mov r14, 0
214:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 214b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
215:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 215b
21:
	movq rbx, xmm8
	movq rbp, xmm9
	movq r12, xmm10
	movq r13, xmm11
	movq r14, xmm12
	movq r15, xmm13
	ret
	.p2align 6
