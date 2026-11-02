// The functions of `src/internal/vg_p384_check_point.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p384_check_point:
	.option push
	.option arch, +m, +c
	sd s0, 160(a0)
	sd ra, 168(a0)
	addi s0, a0, 0
	addi t5, zero, 0
	ld t3, 1648(s0)
	ld t4, 64(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1656(s0)
	ld t4, 72(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1664(s0)
	ld t4, 80(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1672(s0)
	ld t4, 88(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1680(s0)
	ld t4, 96(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1688(s0)
	ld t4, 104(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t6, zero, 0
	sub a7, t6, t5
	addi t0, s0, 2047
	ld t0, 129(t0)
	and t0, t0, a7
	addi s0, s0, 2047
	sd t0, 129(s0)
	addi s0, s0, -2047
	addi t5, zero, 0
	ld t3, 1792(s0)
	ld t4, 64(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1800(s0)
	ld t4, 72(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1808(s0)
	ld t4, 80(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1816(s0)
	ld t4, 88(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1824(s0)
	ld t4, 96(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1832(s0)
	ld t4, 104(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t6, zero, 0
	sub a7, t6, t5
	addi t0, s0, 2047
	ld t0, 129(t0)
	and t0, t0, a7
	addi s0, s0, 2047
	sd t0, 129(s0)
	addi s0, s0, -2047
	addi a0, s0, 0
	addi a1, zero, 1696
	addi a2, zero, 1648
	addi a3, zero, 1936
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1744
	addi a2, zero, 1792
	addi a3, zero, 1936
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1840
	addi a2, zero, 1744
	addi a3, zero, 1744
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2032
	addi a2, zero, 1696
	addi a3, zero, 1696
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 33
	addi a2, zero, 2032
	addi a3, zero, 1696
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2032
	addi a2, zero, 352
	addi a3, zero, 1696
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1888
	addi a2, zero, 2047
	addi a2, a2, 33
	addi a3, zero, 2032
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 33
	addi a2, zero, 1888
	addi a3, zero, 1984
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2032
	addi a2, zero, 1840
	addi a3, zero, 2047
	addi a3, a3, 33
	call {vg_p384_sub_mod_p}
	addi t3, zero, 0
	ld t4, 2032(s0)
	or t3, t3, t4
	ld t4, 2040(s0)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 1(t4)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 9(t4)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 17(t4)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 25(t4)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	addi t0, s0, 2047
	ld t0, 129(t0)
	and t0, t0, a7
	addi s0, s0, 2047
	sd t0, 129(s0)
	addi s0, s0, -2047
	addi a7, s0, 2047
	ld a7, 129(a7)
	ld t0, 448(s0)
	ld t1, 1696(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1888(s0)
	ld t0, 456(s0)
	ld t1, 1704(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1896(s0)
	ld t0, 464(s0)
	ld t1, 1712(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1904(s0)
	ld t0, 472(s0)
	ld t1, 1720(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1912(s0)
	ld t0, 480(s0)
	ld t1, 1728(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1920(s0)
	ld t0, 488(s0)
	ld t1, 1736(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1928(s0)
	ld t0, 496(s0)
	ld t1, 1744(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 81(s0)
	addi s0, s0, -2047
	ld t0, 504(s0)
	ld t1, 1752(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 89(s0)
	addi s0, s0, -2047
	ld t0, 512(s0)
	ld t1, 1760(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 97(s0)
	addi s0, s0, -2047
	ld t0, 520(s0)
	ld t1, 1768(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 105(s0)
	addi s0, s0, -2047
	ld t0, 528(s0)
	ld t1, 1776(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 113(s0)
	addi s0, s0, -2047
	ld t0, 536(s0)
	ld t1, 1784(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 121(s0)
	addi s0, s0, -2047
	ld ra, 168(s0)
	ld s0, 160(s0)
	ret
	.option pop
