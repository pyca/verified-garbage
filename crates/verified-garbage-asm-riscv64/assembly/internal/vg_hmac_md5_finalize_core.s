// The functions of `src/internal/vg_hmac_md5_finalize_core.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_md5_finalize_core:
	.option push
	.option arch, +m, +c
	addi sp, sp, -64
	addi t0, sp, 0
	sd ra, 16(t0)
	sd s7, 24(t0)
	sd s8, 32(t0)
	sd s9, 40(t0)
	sd s10, 48(t0)
	sd s11, 56(t0)
	addi s7, a0, 0
	addi s8, t0, 0
	addi s9, a1, 0
	addi s10, a3, 0
	addi a1, a2, 0
	addi a2, t0, 0
	call {vg_md5_finalize_core}
	lbu t1, 0(s9)
	sb t1, 0(s7)
	lbu t1, 1(s9)
	sb t1, 1(s7)
	lbu t1, 2(s9)
	sb t1, 2(s7)
	lbu t1, 3(s9)
	sb t1, 3(s7)
	lbu t1, 4(s9)
	sb t1, 4(s7)
	lbu t1, 5(s9)
	sb t1, 5(s7)
	lbu t1, 6(s9)
	sb t1, 6(s7)
	lbu t1, 7(s9)
	sb t1, 7(s7)
	lbu t1, 8(s9)
	sb t1, 8(s7)
	lbu t1, 9(s9)
	sb t1, 9(s7)
	lbu t1, 10(s9)
	sb t1, 10(s7)
	lbu t1, 11(s9)
	sb t1, 11(s7)
	lbu t1, 12(s9)
	sb t1, 12(s7)
	lbu t1, 13(s9)
	sb t1, 13(s7)
	lbu t1, 14(s9)
	sb t1, 14(s7)
	lbu t1, 15(s9)
	sb t1, 15(s7)
	addi a0, s7, 0
	addi a1, zero, 64
	addi a2, s8, 0
	addi a3, zero, 16
	call {vg_md5_update_core}
	addi a0, s7, 0
	addi a1, zero, 80
	addi a2, s10, 0
	call {vg_md5_finalize_core}
	ld ra, 16(s8)
	ld s7, 24(s8)
	ld s9, 40(s8)
	ld s10, 48(s8)
	ld s11, 56(s8)
	ld s8, 32(s8)
	addi sp, sp, 64
	ret
	.option pop
