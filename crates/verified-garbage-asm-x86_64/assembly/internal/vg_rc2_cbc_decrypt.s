// The functions of `src/internal/vg_rc2_cbc_decrypt.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rc2_cbc_decrypt:
	mov QWORD PTR [r8+264], rbx
	mov QWORD PTR [r8+272], rbp
	mov rbx, rsi
	mov rbp, rcx
	mov rsi, rdx
	mov rdx, r8
	cmp rbp, 0
	je 20f
22:
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [rdx+256], rax
	call {vg_rc2_decrypt_block}
	mov rax, QWORD PTR [rsi]
	xor rax, QWORD PTR [rbx]
	mov QWORD PTR [rsi], rax
	mov rax, QWORD PTR [rdx+256]
	mov QWORD PTR [rbx], rax
	add rsi, 8
	sub rbp, 1
	jne 22b
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [rdx+264]
	mov rbp, QWORD PTR [rdx+272]
	ret
	.p2align 6
