// The functions of `src/internal/vg_keccak_squeeze_scratch.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_keccak_squeeze_scratch:
	mov QWORD PTR [r9+512], rbx
	mov QWORD PTR [r9+520], rbp
	mov QWORD PTR [r9+528], r12
	mov QWORD PTR [r9+536], r13
	mov QWORD PTR [r9+544], r14
	mov QWORD PTR [r9+552], r15
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rdx
	mov r13, rcx
	mov r14, r8
	mov r15, r9
	test r14, r14
	je 20f
22:
	cmp r12, rbp
	je 23f
	jmp 24f
23:
	mov r12d, 0
	mov rdi, rbx
	mov rsi, r15
	call {vg_keccak_f1600}
	mov rbx, rdi
	mov r15, rsi
24:
	mov r10, r12
	mov r11d, 7
	and r10, r11
	mov r11, r14
	sub r11, 8
	shr r11, 63
	or r10, r11
	test r10, r10
	je 25f
	movzx eax, BYTE PTR [rbx+r12*1]
	mov BYTE PTR [r13], al
	add r13, 1
	add r12, 1
	sub r14, 1
	jmp 26f
25:
	mov rax, QWORD PTR [rbx+r12*1]
	mov QWORD PTR [r13], rax
	add r13, 8
	add r12, 8
	sub r14, 8
26:
	jne 22b
	jmp 21f
20:
21:
	mov rax, r12
	mov rbx, QWORD PTR [r15+512]
	mov rbp, QWORD PTR [r15+520]
	mov r12, QWORD PTR [r15+528]
	mov r13, QWORD PTR [r15+536]
	mov r14, QWORD PTR [r15+544]
	mov r15, QWORD PTR [r15+552]
	ret
	.p2align 6
