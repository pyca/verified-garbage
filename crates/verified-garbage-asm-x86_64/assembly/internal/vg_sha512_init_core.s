// The functions of `src/internal/vg_sha512_init_core.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha512_init_core:
	movabs rax, 7640891576956012808
	mov QWORD PTR [rdi], rax
	movabs rax, -4942790177534073029
	mov QWORD PTR [rdi+8], rax
	movabs rax, 4354685564936845355
	mov QWORD PTR [rdi+16], rax
	movabs rax, -6534734903238641935
	mov QWORD PTR [rdi+24], rax
	movabs rax, 5840696475078001361
	mov QWORD PTR [rdi+32], rax
	movabs rax, -7276294671716946913
	mov QWORD PTR [rdi+40], rax
	movabs rax, 2270897969802886507
	mov QWORD PTR [rdi+48], rax
	movabs rax, 6620516959819538809
	mov QWORD PTR [rdi+56], rax
	ret
	.p2align 6
