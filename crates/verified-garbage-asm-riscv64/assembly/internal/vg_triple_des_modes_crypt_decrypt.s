// The functions of `src/internal/vg_triple_des_modes_crypt_decrypt.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_triple_des_modes_crypt_decrypt:
	.option push
	.option arch, +m, +c
	addi t0, s4, 48
	sd ra, 968(t0)
	sd a0, 1032(t0)
	sd s5, 976(t0)
	sd s6, 984(t0)
	sd s7, 992(t0)
	sd s8, 1000(t0)
	sd s9, 1008(t0)
	sd s10, 1016(t0)
	sd s11, 1024(t0)
	sd s0, 1040(t0)
	addi s0, t0, 0
	addi a1, s1, 0
	addi a2, s2, 0
	addi s11, s3, 0
	call {vg_triple_des_transpose}
	addi a3, s0, 888
	call {vg_triple_des_pass_decrypt}
	addi a3, s0, 640
	call {vg_triple_des_pass_encrypt}
	addi a3, s0, 632
	call {vg_triple_des_pass_decrypt}
	call {vg_triple_des_transpose}
	addi s1, a1, 0
	addi s2, a2, 0
	addi s3, s11, 0
	addi s4, s0, -48
	ld ra, 968(s0)
	ld a0, 1032(s0)
	ld s5, 976(s0)
	ld s6, 984(s0)
	ld s7, 992(s0)
	ld s8, 1000(s0)
	ld s9, 1008(s0)
	ld s10, 1016(s0)
	ld s11, 1024(s0)
	ld s0, 1040(s0)
	ret
	.option pop
