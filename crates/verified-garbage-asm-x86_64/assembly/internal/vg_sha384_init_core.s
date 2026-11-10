// The functions of `src/internal/vg_sha384_init_core.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha384_init_core:
	movabs rax, -3766243637369397544
	mov QWORD PTR [rdi], rax
	movabs rax, 7105036623409894663
	mov QWORD PTR [rdi+8], rax
	movabs rax, -7973340178411365097
	mov QWORD PTR [rdi+16], rax
	movabs rax, 1526699215303891257
	mov QWORD PTR [rdi+24], rax
	movabs rax, 7436329637833083697
	mov QWORD PTR [rdi+32], rax
	movabs rax, -8163818279084223215
	mov QWORD PTR [rdi+40], rax
	movabs rax, -2662702644619276377
	mov QWORD PTR [rdi+48], rax
	movabs rax, 5167115440072839076
	mov QWORD PTR [rdi+56], rax
	ret
	.p2align 6
