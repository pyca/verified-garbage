// The functions of `src/internal/vg_chacha20_poly1305_seal_core.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chacha20_poly1305_seal_core:
	lea rsp, [rsp-8]
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rsp], rax
	call {vg_chacha20_poly1305_seal_body}
	lea rsp, [rsp+8]
	ret
	.p2align 6
