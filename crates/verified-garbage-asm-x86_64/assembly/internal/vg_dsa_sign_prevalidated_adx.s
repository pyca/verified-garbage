// The functions of `src/internal/vg_dsa_sign_prevalidated_adx.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_dsa_sign_prevalidated_adx:
	lea rsp, [rsp-56]
	mov rax, QWORD PTR [rsp+64]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+80]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+88]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rsp+32], rax
	lea rax, {vg_rsa_mont_mul_adx}
	mov QWORD PTR [rsp+40], rax
	lea rax, {vg_rsa_lazy_mont_mul_adx}
	mov QWORD PTR [rsp+48], rax
	call {vg_dsa_sign_prevalidated_shared}
	lea rsp, [rsp+56]
	ret
	.p2align 6
