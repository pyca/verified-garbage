// The functions of `src/internal/vg_scrypt_blockmix.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_scrypt_blockmix:
	.option push
	.option arch, +m, +c
	addi sp, sp, -48
	addi t0, sp, 0
	sd ra, 0(t0)
	sd s4, 8(t0)
	sd s5, 16(t0)
	sd s6, 24(t0)
	sd s7, 32(t0)
	sd s8, 40(t0)
	addi s7, a1, 0
	addi s4, a0, 0
	addi s5, a2, 0
	slli t1, a1, 6
	add s6, a2, t1
	slli t1, a1, 7
	add s8, a0, t1
	addi s8, s8, -64
20:
	ld t0, 0(s8)
	ld t1, 0(s4)
	xor t0, t0, t1
	sd t0, 0(s5)
	ld t0, 8(s8)
	ld t1, 8(s4)
	xor t0, t0, t1
	sd t0, 8(s5)
	ld t0, 16(s8)
	ld t1, 16(s4)
	xor t0, t0, t1
	sd t0, 16(s5)
	ld t0, 24(s8)
	ld t1, 24(s4)
	xor t0, t0, t1
	sd t0, 24(s5)
	ld t0, 32(s8)
	ld t1, 32(s4)
	xor t0, t0, t1
	sd t0, 32(s5)
	ld t0, 40(s8)
	ld t1, 40(s4)
	xor t0, t0, t1
	sd t0, 40(s5)
	ld t0, 48(s8)
	ld t1, 48(s4)
	xor t0, t0, t1
	sd t0, 48(s5)
	ld t0, 56(s8)
	ld t1, 56(s4)
	xor t0, t0, t1
	sd t0, 56(s5)
	addi a0, s5, 0
	call {vg_salsa20_8}
	addi s4, s4, 64
	ld t0, 0(s5)
	ld t1, 0(s4)
	xor t0, t0, t1
	sd t0, 0(s6)
	ld t0, 8(s5)
	ld t1, 8(s4)
	xor t0, t0, t1
	sd t0, 8(s6)
	ld t0, 16(s5)
	ld t1, 16(s4)
	xor t0, t0, t1
	sd t0, 16(s6)
	ld t0, 24(s5)
	ld t1, 24(s4)
	xor t0, t0, t1
	sd t0, 24(s6)
	ld t0, 32(s5)
	ld t1, 32(s4)
	xor t0, t0, t1
	sd t0, 32(s6)
	ld t0, 40(s5)
	ld t1, 40(s4)
	xor t0, t0, t1
	sd t0, 40(s6)
	ld t0, 48(s5)
	ld t1, 48(s4)
	xor t0, t0, t1
	sd t0, 48(s6)
	ld t0, 56(s5)
	ld t1, 56(s4)
	xor t0, t0, t1
	sd t0, 56(s6)
	addi a0, s6, 0
	call {vg_salsa20_8}
	addi s8, s6, 0
	addi s4, s4, 64
	addi s5, s5, 64
	addi s6, s6, 64
	addi s7, s7, -1
	bnez s7, 20b
	addi t0, sp, 0
	ld ra, 0(t0)
	ld s4, 8(t0)
	ld s5, 16(t0)
	ld s6, 24(t0)
	ld s7, 32(t0)
	ld s8, 40(t0)
	addi sp, sp, 48
	ret
	.option pop
