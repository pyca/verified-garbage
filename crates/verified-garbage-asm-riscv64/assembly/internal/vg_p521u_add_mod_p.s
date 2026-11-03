// The functions of `src/internal/vg_p521u_add_mod_p.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p521u_add_mod_p:
	.option push
	.option arch, +m, +c
	slli a1, a1, 32
	srli a1, a1, 32
	slli a2, a2, 32
	srli a2, a2, 32
	slli a3, a3, 32
	srli a3, a3, 32
	add t2, a0, a1
	add t4, a0, a2
	add t5, a0, a3
	addi a3, a0, 2047
	addi a3, a3, 2047
	addi a3, a3, 2047
	addi a3, a3, 3
	or t0, t2, t4
	or t0, t0, t5
	andi t0, t0, 7
	beqz t0, 20f
	addi t1, t2, 0
	lbu a4, 0(t4)
	lbu a5, 1(t4)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 2(t4)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 3(t4)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1632(a3)
	lbu a4, 4(t4)
	lbu a5, 5(t4)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 6(t4)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 7(t4)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1636(a3)
	lbu a4, 8(t4)
	lbu a5, 9(t4)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 10(t4)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 11(t4)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1640(a3)
	lbu a4, 12(t4)
	lbu a5, 13(t4)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 14(t4)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 15(t4)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1644(a3)
	lbu a4, 16(t4)
	lbu a5, 17(t4)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 18(t4)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 19(t4)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1648(a3)
	lbu a4, 20(t4)
	lbu a5, 21(t4)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 22(t4)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 23(t4)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1652(a3)
	lbu a4, 24(t4)
	lbu a5, 25(t4)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 26(t4)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 27(t4)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1656(a3)
	lbu a4, 28(t4)
	lbu a5, 29(t4)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 30(t4)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 31(t4)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1660(a3)
	lbu a4, 32(t4)
	lbu a5, 33(t4)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 34(t4)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 35(t4)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1664(a3)
	lbu a4, 36(t4)
	lbu a5, 37(t4)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 38(t4)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 39(t4)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1668(a3)
	lbu a4, 40(t4)
	lbu a5, 41(t4)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 42(t4)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 43(t4)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1672(a3)
	lbu a4, 44(t4)
	lbu a5, 45(t4)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 46(t4)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 47(t4)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1676(a3)
	lbu a4, 48(t4)
	lbu a5, 49(t4)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 50(t4)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 51(t4)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1680(a3)
	lbu a4, 52(t4)
	lbu a5, 53(t4)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 54(t4)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 55(t4)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1684(a3)
	lbu a4, 56(t4)
	lbu a5, 57(t4)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 58(t4)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 59(t4)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1688(a3)
	lbu a4, 60(t4)
	lbu a5, 61(t4)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 62(t4)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 63(t4)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1692(a3)
	lbu a4, 64(t4)
	lbu a5, 65(t4)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 66(t4)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 67(t4)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1696(a3)
	lbu a4, 68(t4)
	lbu a5, 69(t4)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 70(t4)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 71(t4)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1700(a3)
	lbu a4, 0(t5)
	lbu a5, 1(t5)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 2(t5)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 3(t5)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1704(a3)
	lbu a4, 4(t5)
	lbu a5, 5(t5)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 6(t5)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 7(t5)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1708(a3)
	lbu a4, 8(t5)
	lbu a5, 9(t5)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 10(t5)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 11(t5)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1712(a3)
	lbu a4, 12(t5)
	lbu a5, 13(t5)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 14(t5)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 15(t5)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1716(a3)
	lbu a4, 16(t5)
	lbu a5, 17(t5)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 18(t5)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 19(t5)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1720(a3)
	lbu a4, 20(t5)
	lbu a5, 21(t5)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 22(t5)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 23(t5)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1724(a3)
	lbu a4, 24(t5)
	lbu a5, 25(t5)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 26(t5)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 27(t5)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1728(a3)
	lbu a4, 28(t5)
	lbu a5, 29(t5)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 30(t5)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 31(t5)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1732(a3)
	lbu a4, 32(t5)
	lbu a5, 33(t5)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 34(t5)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 35(t5)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1736(a3)
	lbu a4, 36(t5)
	lbu a5, 37(t5)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 38(t5)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 39(t5)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1740(a3)
	lbu a4, 40(t5)
	lbu a5, 41(t5)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 42(t5)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 43(t5)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1744(a3)
	lbu a4, 44(t5)
	lbu a5, 45(t5)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 46(t5)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 47(t5)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1748(a3)
	lbu a4, 48(t5)
	lbu a5, 49(t5)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 50(t5)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 51(t5)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1752(a3)
	lbu a4, 52(t5)
	lbu a5, 53(t5)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 54(t5)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 55(t5)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1756(a3)
	lbu a4, 56(t5)
	lbu a5, 57(t5)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 58(t5)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 59(t5)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1760(a3)
	lbu a4, 60(t5)
	lbu a5, 61(t5)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 62(t5)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 63(t5)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1764(a3)
	lbu a4, 64(t5)
	lbu a5, 65(t5)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 66(t5)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 67(t5)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1768(a3)
	lbu a4, 68(t5)
	lbu a5, 69(t5)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 70(t5)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 71(t5)
	slli a5, a5, 24
	or a4, a4, a5
	sw a4, 1772(a3)
	addi t4, a3, 1632
	addi t5, a3, 1704
	addi t2, a3, 1776
	addi a6, zero, -1
	srli a6, a6, 6
	addi a4, zero, 0
	ld a1, 0(t4)
	ld a2, 0(t5)
	add a1, a1, a2
	add a1, a1, a4
	srli a4, a1, 58
	and a1, a1, a6
	sd a1, 1472(a3)
	ld a1, 8(t4)
	ld a2, 8(t5)
	add a1, a1, a2
	add a1, a1, a4
	srli a4, a1, 58
	and a1, a1, a6
	sd a1, 1480(a3)
	ld a1, 16(t4)
	ld a2, 16(t5)
	add a1, a1, a2
	add a1, a1, a4
	srli a4, a1, 58
	and a1, a1, a6
	sd a1, 1488(a3)
	ld a1, 24(t4)
	ld a2, 24(t5)
	add a1, a1, a2
	add a1, a1, a4
	srli a4, a1, 58
	and a1, a1, a6
	sd a1, 1496(a3)
	ld a1, 32(t4)
	ld a2, 32(t5)
	add a1, a1, a2
	add a1, a1, a4
	srli a4, a1, 58
	and a1, a1, a6
	sd a1, 1504(a3)
	ld a1, 40(t4)
	ld a2, 40(t5)
	add a1, a1, a2
	add a1, a1, a4
	srli a4, a1, 58
	and a1, a1, a6
	sd a1, 1512(a3)
	ld a1, 48(t4)
	ld a2, 48(t5)
	add a1, a1, a2
	add a1, a1, a4
	srli a4, a1, 58
	and a1, a1, a6
	sd a1, 1520(a3)
	ld a1, 56(t4)
	ld a2, 56(t5)
	add a1, a1, a2
	add a1, a1, a4
	srli a4, a1, 58
	and a1, a1, a6
	sd a1, 1528(a3)
	ld a1, 64(t4)
	ld a2, 64(t5)
	add a1, a1, a2
	add a1, a1, a4
	srli a4, a1, 58
	and a1, a1, a6
	sd a1, 1536(a3)
	ld a1, 1472(a3)
	slli a4, a4, 1
	add a1, a1, a4
	sd a1, 0(t2)
	ld a1, 1480(a3)
	sd a1, 8(t2)
	ld a1, 1488(a3)
	sd a1, 16(t2)
	ld a1, 1496(a3)
	sd a1, 24(t2)
	ld a1, 1504(a3)
	sd a1, 32(t2)
	ld a1, 1512(a3)
	sd a1, 40(t2)
	ld a1, 1520(a3)
	sd a1, 48(t2)
	ld a1, 1528(a3)
	sd a1, 56(t2)
	ld a1, 1536(a3)
	sd a1, 64(t2)
	lwu a4, 1776(a3)
	sb a4, 0(t1)
	srli a5, a4, 8
	sb a5, 1(t1)
	srli a5, a4, 16
	sb a5, 2(t1)
	srli a5, a4, 24
	sb a5, 3(t1)
	lwu a4, 1780(a3)
	sb a4, 4(t1)
	srli a5, a4, 8
	sb a5, 5(t1)
	srli a5, a4, 16
	sb a5, 6(t1)
	srli a5, a4, 24
	sb a5, 7(t1)
	lwu a4, 1784(a3)
	sb a4, 8(t1)
	srli a5, a4, 8
	sb a5, 9(t1)
	srli a5, a4, 16
	sb a5, 10(t1)
	srli a5, a4, 24
	sb a5, 11(t1)
	lwu a4, 1788(a3)
	sb a4, 12(t1)
	srli a5, a4, 8
	sb a5, 13(t1)
	srli a5, a4, 16
	sb a5, 14(t1)
	srli a5, a4, 24
	sb a5, 15(t1)
	lwu a4, 1792(a3)
	sb a4, 16(t1)
	srli a5, a4, 8
	sb a5, 17(t1)
	srli a5, a4, 16
	sb a5, 18(t1)
	srli a5, a4, 24
	sb a5, 19(t1)
	lwu a4, 1796(a3)
	sb a4, 20(t1)
	srli a5, a4, 8
	sb a5, 21(t1)
	srli a5, a4, 16
	sb a5, 22(t1)
	srli a5, a4, 24
	sb a5, 23(t1)
	lwu a4, 1800(a3)
	sb a4, 24(t1)
	srli a5, a4, 8
	sb a5, 25(t1)
	srli a5, a4, 16
	sb a5, 26(t1)
	srli a5, a4, 24
	sb a5, 27(t1)
	lwu a4, 1804(a3)
	sb a4, 28(t1)
	srli a5, a4, 8
	sb a5, 29(t1)
	srli a5, a4, 16
	sb a5, 30(t1)
	srli a5, a4, 24
	sb a5, 31(t1)
	lwu a4, 1808(a3)
	sb a4, 32(t1)
	srli a5, a4, 8
	sb a5, 33(t1)
	srli a5, a4, 16
	sb a5, 34(t1)
	srli a5, a4, 24
	sb a5, 35(t1)
	lwu a4, 1812(a3)
	sb a4, 36(t1)
	srli a5, a4, 8
	sb a5, 37(t1)
	srli a5, a4, 16
	sb a5, 38(t1)
	srli a5, a4, 24
	sb a5, 39(t1)
	lwu a4, 1816(a3)
	sb a4, 40(t1)
	srli a5, a4, 8
	sb a5, 41(t1)
	srli a5, a4, 16
	sb a5, 42(t1)
	srli a5, a4, 24
	sb a5, 43(t1)
	lwu a4, 1820(a3)
	sb a4, 44(t1)
	srli a5, a4, 8
	sb a5, 45(t1)
	srli a5, a4, 16
	sb a5, 46(t1)
	srli a5, a4, 24
	sb a5, 47(t1)
	lwu a4, 1824(a3)
	sb a4, 48(t1)
	srli a5, a4, 8
	sb a5, 49(t1)
	srli a5, a4, 16
	sb a5, 50(t1)
	srli a5, a4, 24
	sb a5, 51(t1)
	lwu a4, 1828(a3)
	sb a4, 52(t1)
	srli a5, a4, 8
	sb a5, 53(t1)
	srli a5, a4, 16
	sb a5, 54(t1)
	srli a5, a4, 24
	sb a5, 55(t1)
	lwu a4, 1832(a3)
	sb a4, 56(t1)
	srli a5, a4, 8
	sb a5, 57(t1)
	srli a5, a4, 16
	sb a5, 58(t1)
	srli a5, a4, 24
	sb a5, 59(t1)
	lwu a4, 1836(a3)
	sb a4, 60(t1)
	srli a5, a4, 8
	sb a5, 61(t1)
	srli a5, a4, 16
	sb a5, 62(t1)
	srli a5, a4, 24
	sb a5, 63(t1)
	lwu a4, 1840(a3)
	sb a4, 64(t1)
	srli a5, a4, 8
	sb a5, 65(t1)
	srli a5, a4, 16
	sb a5, 66(t1)
	srli a5, a4, 24
	sb a5, 67(t1)
	lwu a4, 1844(a3)
	sb a4, 68(t1)
	srli a5, a4, 8
	sb a5, 69(t1)
	srli a5, a4, 16
	sb a5, 70(t1)
	srli a5, a4, 24
	sb a5, 71(t1)
	j 21f
20:
	addi a6, zero, -1
	srli a6, a6, 6
	addi a4, zero, 0
	ld a1, 0(t4)
	ld a2, 0(t5)
	add a1, a1, a2
	add a1, a1, a4
	srli a4, a1, 58
	and a1, a1, a6
	sd a1, 1472(a3)
	ld a1, 8(t4)
	ld a2, 8(t5)
	add a1, a1, a2
	add a1, a1, a4
	srli a4, a1, 58
	and a1, a1, a6
	sd a1, 1480(a3)
	ld a1, 16(t4)
	ld a2, 16(t5)
	add a1, a1, a2
	add a1, a1, a4
	srli a4, a1, 58
	and a1, a1, a6
	sd a1, 1488(a3)
	ld a1, 24(t4)
	ld a2, 24(t5)
	add a1, a1, a2
	add a1, a1, a4
	srli a4, a1, 58
	and a1, a1, a6
	sd a1, 1496(a3)
	ld a1, 32(t4)
	ld a2, 32(t5)
	add a1, a1, a2
	add a1, a1, a4
	srli a4, a1, 58
	and a1, a1, a6
	sd a1, 1504(a3)
	ld a1, 40(t4)
	ld a2, 40(t5)
	add a1, a1, a2
	add a1, a1, a4
	srli a4, a1, 58
	and a1, a1, a6
	sd a1, 1512(a3)
	ld a1, 48(t4)
	ld a2, 48(t5)
	add a1, a1, a2
	add a1, a1, a4
	srli a4, a1, 58
	and a1, a1, a6
	sd a1, 1520(a3)
	ld a1, 56(t4)
	ld a2, 56(t5)
	add a1, a1, a2
	add a1, a1, a4
	srli a4, a1, 58
	and a1, a1, a6
	sd a1, 1528(a3)
	ld a1, 64(t4)
	ld a2, 64(t5)
	add a1, a1, a2
	add a1, a1, a4
	srli a4, a1, 58
	and a1, a1, a6
	sd a1, 1536(a3)
	ld a1, 1472(a3)
	slli a4, a4, 1
	add a1, a1, a4
	sd a1, 0(t2)
	ld a1, 1480(a3)
	sd a1, 8(t2)
	ld a1, 1488(a3)
	sd a1, 16(t2)
	ld a1, 1496(a3)
	sd a1, 24(t2)
	ld a1, 1504(a3)
	sd a1, 32(t2)
	ld a1, 1512(a3)
	sd a1, 40(t2)
	ld a1, 1520(a3)
	sd a1, 48(t2)
	ld a1, 1528(a3)
	sd a1, 56(t2)
	ld a1, 1536(a3)
	sd a1, 64(t2)
21:
	ret
	.option pop
