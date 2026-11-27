// The functions of `src/internal/vg_sha512_digest_core.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha512_digest_core:
	.option push
	.option arch, +m, +c
	addi sp, sp, -240
	addi t0, sp, 0
	sd ra, 192(t0)
	sd s7, 200(t0)
	sd s8, 208(t0)
	sd s9, 216(t0)
	sd s10, 224(t0)
	sd s11, 232(t0)
	addi s8, t0, 0
	addi s9, a2, 0
	addi s10, a0, 0
	addi s11, a1, 0
	addi a0, s8, 0
	call {vg_sha512_init_core}
	addi a0, s8, 0
	addi a1, zero, 0
	addi a2, s10, 0
	addi a3, s11, 0
	call {vg_sha512_update_core}
	addi a0, s8, 0
	addi a1, s11, 0
	addi a2, s9, 0
	call {vg_sha512_finalize_core}
	addi t1, zero, 0
	sd t1, 0(s8)
	sd t1, 8(s8)
	sd t1, 16(s8)
	sd t1, 24(s8)
	sd t1, 32(s8)
	sd t1, 40(s8)
	sd t1, 48(s8)
	sd t1, 56(s8)
	sd t1, 64(s8)
	sd t1, 72(s8)
	sd t1, 80(s8)
	sd t1, 88(s8)
	sd t1, 96(s8)
	sd t1, 104(s8)
	sd t1, 112(s8)
	sd t1, 120(s8)
	sd t1, 128(s8)
	sd t1, 136(s8)
	sd t1, 144(s8)
	sd t1, 152(s8)
	sd t1, 160(s8)
	sd t1, 168(s8)
	sd t1, 176(s8)
	sd t1, 184(s8)
	ld ra, 192(s8)
	ld s7, 200(s8)
	ld s9, 216(s8)
	ld s10, 224(s8)
	ld s11, 232(s8)
	ld s8, 208(s8)
	addi sp, sp, 240
	ret
	.option pop
