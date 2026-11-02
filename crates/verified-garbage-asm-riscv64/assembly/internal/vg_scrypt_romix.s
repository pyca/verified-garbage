// The functions of `src/internal/vg_scrypt_romix.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_scrypt_romix:
	.option push
	.option arch, +m, +c
	addi sp, sp, -64
	addi t0, sp, 0
	sd ra, 0(t0)
	sd s4, 8(t0)
	sd s5, 16(t0)
	sd s6, 24(t0)
	sd s7, 32(t0)
	sd s8, 40(t0)
	sd s9, 48(t0)
	addi s4, a0, 0
	addi s5, a2, 0
	addi s9, a4, 0
	slli s6, a1, 7
	addi t0, a1, 0
	addi t1, zero, 1
	add t2, a3, a3
20:
	add t0, t0, t0
	add t1, t1, t1
	sub t3, t0, t2
	bnez t3, 20b
	srli t1, t1, 1
	addi t0, sp, 0
	sd t1, 56(t0)
	addi s7, t1, 0
	addi s8, s5, 0
21:
	addi t0, s4, 0
	addi t1, s8, 0
	srli t2, s6, 3
22:
	ld t3, 0(t0)
	sd t3, 0(t1)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t2, t2, -1
	bnez t2, 22b
	addi a0, s8, 0
	srli a1, s6, 7
	addi a2, s4, 0
	call {vg_scrypt_blockmix}
	add s8, s8, s6
	addi s7, s7, -1
	bnez s7, 21b
	addi t0, sp, 0
	ld s7, 56(t0)
	addi s8, s7, -1
23:
	add t1, s4, s6
	addi t1, t1, -64
	ld t0, 0(t1)
	and t0, t0, s8
	mul t1, t0, s6
	add t1, t1, s5
	addi t0, s4, 0
	addi t2, s9, 0
	srli t3, s6, 3
24:
	ld t4, 0(t0)
	ld t5, 0(t1)
	xor t4, t4, t5
	sd t4, 0(t2)
	addi t0, t0, 8
	addi t1, t1, 8
	addi t2, t2, 8
	addi t3, t3, -1
	bnez t3, 24b
	addi a0, s9, 0
	srli a1, s6, 7
	addi a2, s4, 0
	call {vg_scrypt_blockmix}
	addi s7, s7, -1
	bnez s7, 23b
	addi t0, sp, 0
	ld ra, 0(t0)
	ld s4, 8(t0)
	ld s5, 16(t0)
	ld s6, 24(t0)
	ld s7, 32(t0)
	ld s8, 40(t0)
	ld s9, 48(t0)
	addi sp, sp, 64
	ret
	.option pop
