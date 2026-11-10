// The functions of `src/internal/vg_sha512_224_init_core.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha512_224_init_core:
	movabs rax, -8341449602262348382
	mov QWORD PTR [rdi], rax
	movabs rax, 8350123849800275158
	mov QWORD PTR [rdi+8], rax
	movabs rax, 2160240930085379202
	mov QWORD PTR [rdi+16], rax
	movabs rax, 7466358040605728719
	mov QWORD PTR [rdi+24], rax
	movabs rax, 1111592415079452072
	mov QWORD PTR [rdi+32], rax
	movabs rax, 8638871050018654530
	mov QWORD PTR [rdi+40], rax
	movabs rax, 4583966954114332360
	mov QWORD PTR [rdi+48], rax
	movabs rax, 1230299281376055969
	mov QWORD PTR [rdi+56], rax
	ret
	.p2align 6
