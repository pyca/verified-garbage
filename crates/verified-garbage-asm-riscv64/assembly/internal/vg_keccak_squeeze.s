// The functions of `src/internal/vg_keccak_squeeze.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_keccak_squeeze:
	.option push
	.option arch, +m, +c
	addi sp, sp, -560
	addi t0, sp, 0
	sd ra, 512(t0)
	sd s2, 520(t0)
	sd s3, 528(t0)
	sd s4, 536(t0)
	sd s5, 544(t0)
	sd s6, 552(t0)
	addi s2, a0, 0
	addi s3, a1, 0
	addi s4, a2, 0
	addi s5, a3, 0
	addi s6, a4, 0
	beqz s6, 20f
22:
	sub t1, s4, s3
	beqz t1, 23f
	j 24f
23:
	addi s4, zero, 0
	addi a0, s2, 0
	addi a1, sp, 0
	call {vg_keccak_f1600}
24:
	add t2, s2, s4
	or t1, t2, s4
	andi t1, t1, 7
	addi t4, zero, 8
	sltu t3, s6, t4
	or t1, t1, t3
	andi t4, s5, 7
	beqz t1, 25f
	add t2, s2, s4
	lbu t1, 0(t2)
	sb t1, 0(s5)
	addi s5, s5, 1
	addi s4, s4, 1
	addi s6, s6, -1
	j 26f
25:
	beqz t4, 27f
	ld t1, 0(t2)
	sb t1, 0(s5)
	srli t3, t1, 8
	sb t3, 1(s5)
	srli t3, t1, 16
	sb t3, 2(s5)
	srli t3, t1, 24
	sb t3, 3(s5)
	srli t3, t1, 32
	sb t3, 4(s5)
	srli t4, t3, 8
	sb t4, 5(s5)
	srli t4, t3, 16
	sb t4, 6(s5)
	srli t4, t3, 24
	sb t4, 7(s5)
	addi s5, s5, 8
	addi s4, s4, 8
	addi s6, s6, -8
	j 28f
27:
	ld t1, 0(t2)
	sd t1, 0(s5)
	addi s5, s5, 8
	addi s4, s4, 8
	addi s6, s6, -8
28:
26:
	bnez s6, 22b
	j 21f
20:
21:
	addi a0, s4, 0
	addi t0, sp, 0
	ld ra, 512(t0)
	ld s2, 520(t0)
	ld s3, 528(t0)
	ld s4, 536(t0)
	ld s5, 544(t0)
	ld s6, 552(t0)
	addi sp, sp, 560
	ret
	.option pop
