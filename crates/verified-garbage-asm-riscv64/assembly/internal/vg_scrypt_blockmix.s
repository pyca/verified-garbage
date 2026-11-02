// The functions of `src/internal/vg_scrypt_blockmix.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_scrypt_blockmix:
	.option push
	.option arch, +m, +c
	sd ra, 0(a3)
	sd s5, 8(a3)
	sd s6, 16(a3)
	sd s7, 24(a3)
	sd s8, 32(a3)
	sd s9, 40(a3)
	sd s10, 48(a3)
	addi s8, a1, 0
	addi s5, a0, 0
	addi s6, a2, 0
	addi s10, a3, 0
	slli t1, a1, 6
	add s7, a2, t1
	slli t1, a1, 7
	add s9, a0, t1
	addi s9, s9, -64
20:
	ld t0, 0(s9)
	ld t1, 0(s5)
	xor t0, t0, t1
	sd t0, 0(s6)
	ld t0, 8(s9)
	ld t1, 8(s5)
	xor t0, t0, t1
	sd t0, 8(s6)
	ld t0, 16(s9)
	ld t1, 16(s5)
	xor t0, t0, t1
	sd t0, 16(s6)
	ld t0, 24(s9)
	ld t1, 24(s5)
	xor t0, t0, t1
	sd t0, 24(s6)
	ld t0, 32(s9)
	ld t1, 32(s5)
	xor t0, t0, t1
	sd t0, 32(s6)
	ld t0, 40(s9)
	ld t1, 40(s5)
	xor t0, t0, t1
	sd t0, 40(s6)
	ld t0, 48(s9)
	ld t1, 48(s5)
	xor t0, t0, t1
	sd t0, 48(s6)
	ld t0, 56(s9)
	ld t1, 56(s5)
	xor t0, t0, t1
	sd t0, 56(s6)
	addi a0, s6, 0
	addi a1, s10, 56
	call {vg_salsa20_8}
	addi s5, s5, 64
	ld t0, 0(s6)
	ld t1, 0(s5)
	xor t0, t0, t1
	sd t0, 0(s7)
	ld t0, 8(s6)
	ld t1, 8(s5)
	xor t0, t0, t1
	sd t0, 8(s7)
	ld t0, 16(s6)
	ld t1, 16(s5)
	xor t0, t0, t1
	sd t0, 16(s7)
	ld t0, 24(s6)
	ld t1, 24(s5)
	xor t0, t0, t1
	sd t0, 24(s7)
	ld t0, 32(s6)
	ld t1, 32(s5)
	xor t0, t0, t1
	sd t0, 32(s7)
	ld t0, 40(s6)
	ld t1, 40(s5)
	xor t0, t0, t1
	sd t0, 40(s7)
	ld t0, 48(s6)
	ld t1, 48(s5)
	xor t0, t0, t1
	sd t0, 48(s7)
	ld t0, 56(s6)
	ld t1, 56(s5)
	xor t0, t0, t1
	sd t0, 56(s7)
	addi a0, s7, 0
	addi a1, s10, 56
	call {vg_salsa20_8}
	addi s9, s7, 0
	addi s5, s5, 64
	addi s6, s6, 64
	addi s7, s7, 64
	addi s8, s8, -1
	bnez s8, 20b
	ld ra, 0(s10)
	ld s5, 8(s10)
	ld s6, 16(s10)
	ld s7, 24(s10)
	ld s8, 32(s10)
	ld s9, 40(s10)
	ld s10, 48(s10)
	ret
	.option pop
