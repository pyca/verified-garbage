// The functions of `src/internal/vg_dsa_check_parameters_adx.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_dsa_check_parameters_adx:
	lea rsp, [rsp-56]
	lea rax, {vg_rsa_mont_mul_adx}
	mov QWORD PTR [rsp], rax
	lea rax, {vg_rsa_lazy_mont_mul_adx}
	mov QWORD PTR [rsp+8], rax
	call {vg_dsa_check_parameters_shared}
	lea rsp, [rsp+56]
	ret
	.p2align 6
