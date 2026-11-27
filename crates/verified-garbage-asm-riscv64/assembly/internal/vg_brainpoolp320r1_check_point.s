// The functions of `src/internal/vg_brainpoolp320r1_check_point.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp320r1_check_point:
	.option push
	.option arch, +m, +c
	sd s0, 144(a0)
	sd ra, 152(a0)
	addi s0, a0, 0
	addi t5, zero, 0
	ld t3, 1384(s0)
	ld t4, 64(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1392(s0)
	ld t4, 72(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1400(s0)
	ld t4, 80(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1408(s0)
	ld t4, 88(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1416(s0)
	ld t4, 96(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t6, zero, 0
	sub a7, t6, t5
	ld t0, 1824(s0)
	and t0, t0, a7
	sd t0, 1824(s0)
	addi t5, zero, 0
	ld t3, 1504(s0)
	ld t4, 64(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1512(s0)
	ld t4, 72(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1520(s0)
	ld t4, 80(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1528(s0)
	ld t4, 88(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1536(s0)
	ld t4, 96(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t6, zero, 0
	sub a7, t6, t5
	ld t0, 1824(s0)
	and t0, t0, a7
	sd t0, 1824(s0)
	addi a0, s0, 0
	addi a1, zero, 1424
	addi a2, zero, 1384
	addi a3, zero, 1624
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1464
	addi a2, zero, 1504
	addi a3, zero, 1624
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1544
	addi a2, zero, 1464
	addi a3, zero, 1464
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1704
	addi a2, zero, 1424
	addi a3, zero, 1424
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1744
	addi a2, zero, 1704
	addi a3, zero, 1424
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1704
	addi a2, zero, 304
	addi a3, zero, 1424
	call {vg_brainpoolp320r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1584
	addi a2, zero, 1744
	addi a3, zero, 1704
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1744
	addi a2, zero, 1584
	addi a3, zero, 1664
	call {vg_brainpoolp320r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1704
	addi a2, zero, 1544
	addi a3, zero, 1744
	call {vg_brainpoolp320r1_sub_mod_p}
	addi t3, zero, 0
	ld t4, 1704(s0)
	or t3, t3, t4
	ld t4, 1712(s0)
	or t3, t3, t4
	ld t4, 1720(s0)
	or t3, t3, t4
	ld t4, 1728(s0)
	or t3, t3, t4
	ld t4, 1736(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	ld t0, 1824(s0)
	and t0, t0, a7
	sd t0, 1824(s0)
	ld a7, 1824(s0)
	ld t0, 384(s0)
	ld t1, 1424(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1584(s0)
	ld t0, 392(s0)
	ld t1, 1432(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1592(s0)
	ld t0, 400(s0)
	ld t1, 1440(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1600(s0)
	ld t0, 408(s0)
	ld t1, 1448(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1608(s0)
	ld t0, 416(s0)
	ld t1, 1456(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1616(s0)
	ld t0, 424(s0)
	ld t1, 1464(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1784(s0)
	ld t0, 432(s0)
	ld t1, 1472(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1792(s0)
	ld t0, 440(s0)
	ld t1, 1480(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1800(s0)
	ld t0, 448(s0)
	ld t1, 1488(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1808(s0)
	ld t0, 456(s0)
	ld t1, 1496(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1816(s0)
	ld ra, 152(s0)
	ld s0, 144(s0)
	ret
	.option pop
