// The functions of `src/sha3.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_keccak_absorb:
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
	lbu t1, 0(s5)
	add t2, s2, s4
	lbu t3, 0(t2)
	xor t1, t1, t3
	sb t1, 0(t2)
	addi s5, s5, 1
	addi s4, s4, 1
	addi s6, s6, -1
	sub t1, s4, s3
	beqz t1, 23f
	j 24f
23:
	addi s4, zero, 0
	addi a0, s2, 0
	addi a1, sp, 0
	call {vg_keccak_f1600}
24:
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

vg_keccak_pad:
	.option push
	.option arch, +m, +c
	addi sp, sp, -528
	addi t0, sp, 0
	sd ra, 512(t0)
	add t1, a0, a2
	lbu t2, 0(t1)
	xor t2, t2, a3
	sb t2, 0(t1)
	add t1, a0, a1
	addi t1, t1, -1
	lbu t2, 0(t1)
	xori t2, t2, 128
	sb t2, 0(t1)
	addi a1, sp, 0
	call {vg_keccak_f1600}
	addi t0, sp, 0
	ld ra, 512(t0)
	addi sp, sp, 528
	ret
	.option pop

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
	lbu t1, 0(t2)
	sb t1, 0(s5)
	addi s5, s5, 1
	addi s4, s4, 1
	addi s6, s6, -1
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
