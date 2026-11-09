// The functions of `src/internal/vg_poly1305_init_core.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_poly1305_init_core:
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
