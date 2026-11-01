// The functions of `src/internal/vg_chacha20_xor.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chacha20_xor:
	mov QWORD PTR [rcx+256], rbx
	mov QWORD PTR [rcx+264], rbp
	mov QWORD PTR [rcx+272], r12
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rdx
	mov rsi, rcx
	test r12, r12
	je 20f
22:
	mov rdi, rbx
	call {vg_chacha20_block}
	mov rdx, r12
	cmp r12, 64
	jb 23f
	mov edx, 64
	jmp 24f
23:
24:
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 25f
27:
	mov r8, QWORD PTR [rbp+rcx*1]
	xor r8, QWORD PTR [rsi+rcx*1]
	mov QWORD PTR [rbp+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 27b
	jmp 26f
25:
26:
	cmp rcx, rdx
	je 28f
210:
	movzx eax, BYTE PTR [rbp+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	mov BYTE PTR [rbp+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 210b
	jmp 29f
28:
29:
	mov eax, DWORD PTR [rbx+48]
	add eax, 1
	mov DWORD PTR [rbx+48], eax
	add rbp, rdx
	sub r12, rdx
	jne 22b
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [rsi+256]
	mov rbp, QWORD PTR [rsi+264]
	mov r12, QWORD PTR [rsi+272]
	ret
	.p2align 6
