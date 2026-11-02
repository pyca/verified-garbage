// The functions of `src/internal/vg_scrypt_romix.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_scrypt_romix:
	.option push
	.option arch, +m, +c
	sd ra, 0(a5)
	sd s4, 8(a5)
	sd s5, 16(a5)
	sd s6, 24(a5)
	sd s7, 32(a5)
	sd s8, 40(a5)
	sd s9, 48(a5)
	sd s10, 56(a5)
	addi s4, a0, 0
	addi s5, a2, 0
	addi s9, a4, 0
	addi s10, a5, 0
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
	sd t1, 64(s10)
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
	addi a3, s10, 72
	call {vg_scrypt_blockmix}
	add s8, s8, s6
	addi s7, s7, -1
	bnez s7, 21b
	ld s7, 64(s10)
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
	addi a3, s10, 72
	call {vg_scrypt_blockmix}
	addi s7, s7, -1
	bnez s7, 23b
	ld ra, 0(s10)
	ld s4, 8(s10)
	ld s5, 16(s10)
	ld s6, 24(s10)
	ld s7, 32(s10)
	ld s8, 40(s10)
	ld s9, 48(s10)
	ld s10, 56(s10)
	ret
	.option pop
