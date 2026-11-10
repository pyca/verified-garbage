// The functions of `src/internal/vg_sha512_256_init_core.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha512_256_init_core:
	movabs rax, 2463787394917988140
	mov QWORD PTR [rdi], rax
	movabs rax, -6965556091613846334
	mov QWORD PTR [rdi+8], rax
	movabs rax, 2563595384472711505
	mov QWORD PTR [rdi+16], rax
	movabs rax, -7622211418569250115
	mov QWORD PTR [rdi+24], rax
	movabs rax, -7626776825740460061
	mov QWORD PTR [rdi+32], rax
	movabs rax, -4729309413028513390
	mov QWORD PTR [rdi+40], rax
	movabs rax, 3098927326965381290
	mov QWORD PTR [rdi+48], rax
	movabs rax, 1060366662362279074
	mov QWORD PTR [rdi+56], rax
	ret
	.p2align 6
