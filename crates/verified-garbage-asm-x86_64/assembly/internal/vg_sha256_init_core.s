// The functions of `src/internal/vg_sha256_init_core.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha256_init_core:
	movabs rax, -4942790177982912921
	movq xmm0, rax
	movabs rax, -6534734903820487822
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	movabs rax, -7276294671082564993
	movq xmm0, rax
	movabs rax, 6620516960021240235
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi+16], xmm0
	ret
	.p2align 6
