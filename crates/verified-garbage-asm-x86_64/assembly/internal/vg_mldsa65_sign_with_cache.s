// The functions of `src/internal/vg_mldsa65_sign_with_cache.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa65_sign_with_cache:
	lea rsp, [rsp-104]
	lea rax, {vg_mldsa_ntt}
	mov QWORD PTR [rsp], rax
	lea rax, {vg_mldsa_inv_ntt}
	mov QWORD PTR [rsp+8], rax
	lea rax, {vg_mldsa_dot_inverse5}
	mov QWORD PTR [rsp+16], rax
	lea rax, {vg_mldsa_multiply_ntt}
	mov QWORD PTR [rsp+24], rax
	lea rax, {vg_mldsa_add}
	mov QWORD PTR [rsp+32], rax
	lea rax, {vg_mldsa_sub}
	mov QWORD PTR [rsp+40], rax
	lea rax, {vg_mldsa_rej_ntt_poly4}
	mov QWORD PTR [rsp+48], rax
	lea rax, {vg_mldsa_expand_mask_poly4}
	mov QWORD PTR [rsp+56], rax
	lea rax, {vg_mldsa_high_bits}
	mov QWORD PTR [rsp+64], rax
	lea rax, {vg_mldsa_low_bits}
	mov QWORD PTR [rsp+72], rax
	lea rax, {vg_mldsa_norm_lt}
	mov QWORD PTR [rsp+80], rax
	lea rax, {vg_mldsa_make_hint}
	mov QWORD PTR [rsp+88], rax
	call {vg_mldsa65_sign_with_cache_body}
	lea rsp, [rsp+104]
	ret
	.p2align 6
