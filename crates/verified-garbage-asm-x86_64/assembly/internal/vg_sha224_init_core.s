// The functions of `src/internal/vg_sha224_init_core.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha224_init_core:
	movabs rax, 3926247204440088280
	movq xmm0, rax
	movabs rax, -644479594506691305
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi], xmm0
	movabs rax, 7518782744944446257
	movq xmm0, rax
	movabs rax, -4685344894838272089
	movq xmm1, rax
	punpcklqdq xmm0, xmm1
	movdqu XMMWORD PTR [rdi+16], xmm0
	ret
	.p2align 6
