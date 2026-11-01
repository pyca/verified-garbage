// The functions of `src/chacha20.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chacha20_block:
	.option push
	.option arch, +m, +c
	addi t0, a1, 71
	andi t0, t0, -8
	sd s0, 0(t0)
	sd s1, 8(t0)
	sd s2, 16(t0)
	sd s3, 24(t0)
	sd s4, 32(t0)
	lbu t0, 0(a0)
	lbu s3, 1(a0)
	slli s3, s3, 8
	or t0, t0, s3
	lbu s3, 2(a0)
	slli s3, s3, 16
	or t0, t0, s3
	lbu s3, 3(a0)
	slli s3, s3, 24
	or t0, t0, s3
	lbu t1, 4(a0)
	lbu s3, 5(a0)
	slli s3, s3, 8
	or t1, t1, s3
	lbu s3, 6(a0)
	slli s3, s3, 16
	or t1, t1, s3
	lbu s3, 7(a0)
	slli s3, s3, 24
	or t1, t1, s3
	lbu t2, 8(a0)
	lbu s3, 9(a0)
	slli s3, s3, 8
	or t2, t2, s3
	lbu s3, 10(a0)
	slli s3, s3, 16
	or t2, t2, s3
	lbu s3, 11(a0)
	slli s3, s3, 24
	or t2, t2, s3
	lbu t3, 12(a0)
	lbu s3, 13(a0)
	slli s3, s3, 8
	or t3, t3, s3
	lbu s3, 14(a0)
	slli s3, s3, 16
	or t3, t3, s3
	lbu s3, 15(a0)
	slli s3, s3, 24
	or t3, t3, s3
	lbu t4, 16(a0)
	lbu s3, 17(a0)
	slli s3, s3, 8
	or t4, t4, s3
	lbu s3, 18(a0)
	slli s3, s3, 16
	or t4, t4, s3
	lbu s3, 19(a0)
	slli s3, s3, 24
	or t4, t4, s3
	lbu t5, 20(a0)
	lbu s3, 21(a0)
	slli s3, s3, 8
	or t5, t5, s3
	lbu s3, 22(a0)
	slli s3, s3, 16
	or t5, t5, s3
	lbu s3, 23(a0)
	slli s3, s3, 24
	or t5, t5, s3
	lbu t6, 24(a0)
	lbu s3, 25(a0)
	slli s3, s3, 8
	or t6, t6, s3
	lbu s3, 26(a0)
	slli s3, s3, 16
	or t6, t6, s3
	lbu s3, 27(a0)
	slli s3, s3, 24
	or t6, t6, s3
	lbu a2, 28(a0)
	lbu s3, 29(a0)
	slli s3, s3, 8
	or a2, a2, s3
	lbu s3, 30(a0)
	slli s3, s3, 16
	or a2, a2, s3
	lbu s3, 31(a0)
	slli s3, s3, 24
	or a2, a2, s3
	lbu a3, 32(a0)
	lbu s3, 33(a0)
	slli s3, s3, 8
	or a3, a3, s3
	lbu s3, 34(a0)
	slli s3, s3, 16
	or a3, a3, s3
	lbu s3, 35(a0)
	slli s3, s3, 24
	or a3, a3, s3
	lbu a4, 36(a0)
	lbu s3, 37(a0)
	slli s3, s3, 8
	or a4, a4, s3
	lbu s3, 38(a0)
	slli s3, s3, 16
	or a4, a4, s3
	lbu s3, 39(a0)
	slli s3, s3, 24
	or a4, a4, s3
	lbu a5, 40(a0)
	lbu s3, 41(a0)
	slli s3, s3, 8
	or a5, a5, s3
	lbu s3, 42(a0)
	slli s3, s3, 16
	or a5, a5, s3
	lbu s3, 43(a0)
	slli s3, s3, 24
	or a5, a5, s3
	lbu a6, 44(a0)
	lbu s3, 45(a0)
	slli s3, s3, 8
	or a6, a6, s3
	lbu s3, 46(a0)
	slli s3, s3, 16
	or a6, a6, s3
	lbu s3, 47(a0)
	slli s3, s3, 24
	or a6, a6, s3
	lbu a7, 48(a0)
	lbu s3, 49(a0)
	slli s3, s3, 8
	or a7, a7, s3
	lbu s3, 50(a0)
	slli s3, s3, 16
	or a7, a7, s3
	lbu s3, 51(a0)
	slli s3, s3, 24
	or a7, a7, s3
	lbu s0, 52(a0)
	lbu s3, 53(a0)
	slli s3, s3, 8
	or s0, s0, s3
	lbu s3, 54(a0)
	slli s3, s3, 16
	or s0, s0, s3
	lbu s3, 55(a0)
	slli s3, s3, 24
	or s0, s0, s3
	lbu s1, 56(a0)
	lbu s3, 57(a0)
	slli s3, s3, 8
	or s1, s1, s3
	lbu s3, 58(a0)
	slli s3, s3, 16
	or s1, s1, s3
	lbu s3, 59(a0)
	slli s3, s3, 24
	or s1, s1, s3
	lbu s2, 60(a0)
	lbu s3, 61(a0)
	slli s3, s3, 8
	or s2, s2, s3
	lbu s3, 62(a0)
	slli s3, s3, 16
	or s2, s2, s3
	lbu s3, 63(a0)
	slli s3, s3, 24
	or s2, s2, s3
	addi s4, zero, 10
20:
	add t0, t0, t4
	xor a7, a7, t0
	slliw s3, a7, 16
	srliw a7, a7, 16
	or a7, a7, s3
	add a3, a3, a7
	xor t4, t4, a3
	slliw s3, t4, 12
	srliw t4, t4, 20
	or t4, t4, s3
	add t0, t0, t4
	xor a7, a7, t0
	slliw s3, a7, 8
	srliw a7, a7, 24
	or a7, a7, s3
	add a3, a3, a7
	xor t4, t4, a3
	slliw s3, t4, 7
	srliw t4, t4, 25
	or t4, t4, s3
	add t1, t1, t5
	xor s0, s0, t1
	slliw s3, s0, 16
	srliw s0, s0, 16
	or s0, s0, s3
	add a4, a4, s0
	xor t5, t5, a4
	slliw s3, t5, 12
	srliw t5, t5, 20
	or t5, t5, s3
	add t1, t1, t5
	xor s0, s0, t1
	slliw s3, s0, 8
	srliw s0, s0, 24
	or s0, s0, s3
	add a4, a4, s0
	xor t5, t5, a4
	slliw s3, t5, 7
	srliw t5, t5, 25
	or t5, t5, s3
	add t2, t2, t6
	xor s1, s1, t2
	slliw s3, s1, 16
	srliw s1, s1, 16
	or s1, s1, s3
	add a5, a5, s1
	xor t6, t6, a5
	slliw s3, t6, 12
	srliw t6, t6, 20
	or t6, t6, s3
	add t2, t2, t6
	xor s1, s1, t2
	slliw s3, s1, 8
	srliw s1, s1, 24
	or s1, s1, s3
	add a5, a5, s1
	xor t6, t6, a5
	slliw s3, t6, 7
	srliw t6, t6, 25
	or t6, t6, s3
	add t3, t3, a2
	xor s2, s2, t3
	slliw s3, s2, 16
	srliw s2, s2, 16
	or s2, s2, s3
	add a6, a6, s2
	xor a2, a2, a6
	slliw s3, a2, 12
	srliw a2, a2, 20
	or a2, a2, s3
	add t3, t3, a2
	xor s2, s2, t3
	slliw s3, s2, 8
	srliw s2, s2, 24
	or s2, s2, s3
	add a6, a6, s2
	xor a2, a2, a6
	slliw s3, a2, 7
	srliw a2, a2, 25
	or a2, a2, s3
	add t0, t0, t5
	xor s2, s2, t0
	slliw s3, s2, 16
	srliw s2, s2, 16
	or s2, s2, s3
	add a5, a5, s2
	xor t5, t5, a5
	slliw s3, t5, 12
	srliw t5, t5, 20
	or t5, t5, s3
	add t0, t0, t5
	xor s2, s2, t0
	slliw s3, s2, 8
	srliw s2, s2, 24
	or s2, s2, s3
	add a5, a5, s2
	xor t5, t5, a5
	slliw s3, t5, 7
	srliw t5, t5, 25
	or t5, t5, s3
	add t1, t1, t6
	xor a7, a7, t1
	slliw s3, a7, 16
	srliw a7, a7, 16
	or a7, a7, s3
	add a6, a6, a7
	xor t6, t6, a6
	slliw s3, t6, 12
	srliw t6, t6, 20
	or t6, t6, s3
	add t1, t1, t6
	xor a7, a7, t1
	slliw s3, a7, 8
	srliw a7, a7, 24
	or a7, a7, s3
	add a6, a6, a7
	xor t6, t6, a6
	slliw s3, t6, 7
	srliw t6, t6, 25
	or t6, t6, s3
	add t2, t2, a2
	xor s0, s0, t2
	slliw s3, s0, 16
	srliw s0, s0, 16
	or s0, s0, s3
	add a3, a3, s0
	xor a2, a2, a3
	slliw s3, a2, 12
	srliw a2, a2, 20
	or a2, a2, s3
	add t2, t2, a2
	xor s0, s0, t2
	slliw s3, s0, 8
	srliw s0, s0, 24
	or s0, s0, s3
	add a3, a3, s0
	xor a2, a2, a3
	slliw s3, a2, 7
	srliw a2, a2, 25
	or a2, a2, s3
	add t3, t3, t4
	xor s1, s1, t3
	slliw s3, s1, 16
	srliw s1, s1, 16
	or s1, s1, s3
	add a4, a4, s1
	xor t4, t4, a4
	slliw s3, t4, 12
	srliw t4, t4, 20
	or t4, t4, s3
	add t3, t3, t4
	xor s1, s1, t3
	slliw s3, s1, 8
	srliw s1, s1, 24
	or s1, s1, s3
	add a4, a4, s1
	xor t4, t4, a4
	slliw s3, t4, 7
	srliw t4, t4, 25
	or t4, t4, s3
	addi s4, s4, -1
	bnez s4, 20b
	lbu s3, 0(a0)
	lbu s4, 1(a0)
	slli s4, s4, 8
	or s3, s3, s4
	lbu s4, 2(a0)
	slli s4, s4, 16
	or s3, s3, s4
	lbu s4, 3(a0)
	slli s4, s4, 24
	or s3, s3, s4
	add t0, t0, s3
	sb t0, 0(a1)
	srli s3, t0, 8
	sb s3, 1(a1)
	srli s3, t0, 16
	sb s3, 2(a1)
	srli s3, t0, 24
	sb s3, 3(a1)
	lbu s3, 4(a0)
	lbu s4, 5(a0)
	slli s4, s4, 8
	or s3, s3, s4
	lbu s4, 6(a0)
	slli s4, s4, 16
	or s3, s3, s4
	lbu s4, 7(a0)
	slli s4, s4, 24
	or s3, s3, s4
	add t1, t1, s3
	sb t1, 4(a1)
	srli s3, t1, 8
	sb s3, 5(a1)
	srli s3, t1, 16
	sb s3, 6(a1)
	srli s3, t1, 24
	sb s3, 7(a1)
	lbu s3, 8(a0)
	lbu s4, 9(a0)
	slli s4, s4, 8
	or s3, s3, s4
	lbu s4, 10(a0)
	slli s4, s4, 16
	or s3, s3, s4
	lbu s4, 11(a0)
	slli s4, s4, 24
	or s3, s3, s4
	add t2, t2, s3
	sb t2, 8(a1)
	srli s3, t2, 8
	sb s3, 9(a1)
	srli s3, t2, 16
	sb s3, 10(a1)
	srli s3, t2, 24
	sb s3, 11(a1)
	lbu s3, 12(a0)
	lbu s4, 13(a0)
	slli s4, s4, 8
	or s3, s3, s4
	lbu s4, 14(a0)
	slli s4, s4, 16
	or s3, s3, s4
	lbu s4, 15(a0)
	slli s4, s4, 24
	or s3, s3, s4
	add t3, t3, s3
	sb t3, 12(a1)
	srli s3, t3, 8
	sb s3, 13(a1)
	srli s3, t3, 16
	sb s3, 14(a1)
	srli s3, t3, 24
	sb s3, 15(a1)
	lbu s3, 16(a0)
	lbu s4, 17(a0)
	slli s4, s4, 8
	or s3, s3, s4
	lbu s4, 18(a0)
	slli s4, s4, 16
	or s3, s3, s4
	lbu s4, 19(a0)
	slli s4, s4, 24
	or s3, s3, s4
	add t4, t4, s3
	sb t4, 16(a1)
	srli s3, t4, 8
	sb s3, 17(a1)
	srli s3, t4, 16
	sb s3, 18(a1)
	srli s3, t4, 24
	sb s3, 19(a1)
	lbu s3, 20(a0)
	lbu s4, 21(a0)
	slli s4, s4, 8
	or s3, s3, s4
	lbu s4, 22(a0)
	slli s4, s4, 16
	or s3, s3, s4
	lbu s4, 23(a0)
	slli s4, s4, 24
	or s3, s3, s4
	add t5, t5, s3
	sb t5, 20(a1)
	srli s3, t5, 8
	sb s3, 21(a1)
	srli s3, t5, 16
	sb s3, 22(a1)
	srli s3, t5, 24
	sb s3, 23(a1)
	lbu s3, 24(a0)
	lbu s4, 25(a0)
	slli s4, s4, 8
	or s3, s3, s4
	lbu s4, 26(a0)
	slli s4, s4, 16
	or s3, s3, s4
	lbu s4, 27(a0)
	slli s4, s4, 24
	or s3, s3, s4
	add t6, t6, s3
	sb t6, 24(a1)
	srli s3, t6, 8
	sb s3, 25(a1)
	srli s3, t6, 16
	sb s3, 26(a1)
	srli s3, t6, 24
	sb s3, 27(a1)
	lbu s3, 28(a0)
	lbu s4, 29(a0)
	slli s4, s4, 8
	or s3, s3, s4
	lbu s4, 30(a0)
	slli s4, s4, 16
	or s3, s3, s4
	lbu s4, 31(a0)
	slli s4, s4, 24
	or s3, s3, s4
	add a2, a2, s3
	sb a2, 28(a1)
	srli s3, a2, 8
	sb s3, 29(a1)
	srli s3, a2, 16
	sb s3, 30(a1)
	srli s3, a2, 24
	sb s3, 31(a1)
	lbu s3, 32(a0)
	lbu s4, 33(a0)
	slli s4, s4, 8
	or s3, s3, s4
	lbu s4, 34(a0)
	slli s4, s4, 16
	or s3, s3, s4
	lbu s4, 35(a0)
	slli s4, s4, 24
	or s3, s3, s4
	add a3, a3, s3
	sb a3, 32(a1)
	srli s3, a3, 8
	sb s3, 33(a1)
	srli s3, a3, 16
	sb s3, 34(a1)
	srli s3, a3, 24
	sb s3, 35(a1)
	lbu s3, 36(a0)
	lbu s4, 37(a0)
	slli s4, s4, 8
	or s3, s3, s4
	lbu s4, 38(a0)
	slli s4, s4, 16
	or s3, s3, s4
	lbu s4, 39(a0)
	slli s4, s4, 24
	or s3, s3, s4
	add a4, a4, s3
	sb a4, 36(a1)
	srli s3, a4, 8
	sb s3, 37(a1)
	srli s3, a4, 16
	sb s3, 38(a1)
	srli s3, a4, 24
	sb s3, 39(a1)
	lbu s3, 40(a0)
	lbu s4, 41(a0)
	slli s4, s4, 8
	or s3, s3, s4
	lbu s4, 42(a0)
	slli s4, s4, 16
	or s3, s3, s4
	lbu s4, 43(a0)
	slli s4, s4, 24
	or s3, s3, s4
	add a5, a5, s3
	sb a5, 40(a1)
	srli s3, a5, 8
	sb s3, 41(a1)
	srli s3, a5, 16
	sb s3, 42(a1)
	srli s3, a5, 24
	sb s3, 43(a1)
	lbu s3, 44(a0)
	lbu s4, 45(a0)
	slli s4, s4, 8
	or s3, s3, s4
	lbu s4, 46(a0)
	slli s4, s4, 16
	or s3, s3, s4
	lbu s4, 47(a0)
	slli s4, s4, 24
	or s3, s3, s4
	add a6, a6, s3
	sb a6, 44(a1)
	srli s3, a6, 8
	sb s3, 45(a1)
	srli s3, a6, 16
	sb s3, 46(a1)
	srli s3, a6, 24
	sb s3, 47(a1)
	lbu s3, 48(a0)
	lbu s4, 49(a0)
	slli s4, s4, 8
	or s3, s3, s4
	lbu s4, 50(a0)
	slli s4, s4, 16
	or s3, s3, s4
	lbu s4, 51(a0)
	slli s4, s4, 24
	or s3, s3, s4
	add a7, a7, s3
	sb a7, 48(a1)
	srli s3, a7, 8
	sb s3, 49(a1)
	srli s3, a7, 16
	sb s3, 50(a1)
	srli s3, a7, 24
	sb s3, 51(a1)
	lbu s3, 52(a0)
	lbu s4, 53(a0)
	slli s4, s4, 8
	or s3, s3, s4
	lbu s4, 54(a0)
	slli s4, s4, 16
	or s3, s3, s4
	lbu s4, 55(a0)
	slli s4, s4, 24
	or s3, s3, s4
	add s0, s0, s3
	sb s0, 52(a1)
	srli s3, s0, 8
	sb s3, 53(a1)
	srli s3, s0, 16
	sb s3, 54(a1)
	srli s3, s0, 24
	sb s3, 55(a1)
	lbu s3, 56(a0)
	lbu s4, 57(a0)
	slli s4, s4, 8
	or s3, s3, s4
	lbu s4, 58(a0)
	slli s4, s4, 16
	or s3, s3, s4
	lbu s4, 59(a0)
	slli s4, s4, 24
	or s3, s3, s4
	add s1, s1, s3
	sb s1, 56(a1)
	srli s3, s1, 8
	sb s3, 57(a1)
	srli s3, s1, 16
	sb s3, 58(a1)
	srli s3, s1, 24
	sb s3, 59(a1)
	lbu s3, 60(a0)
	lbu s4, 61(a0)
	slli s4, s4, 8
	or s3, s3, s4
	lbu s4, 62(a0)
	slli s4, s4, 16
	or s3, s3, s4
	lbu s4, 63(a0)
	slli s4, s4, 24
	or s3, s3, s4
	add s2, s2, s3
	sb s2, 60(a1)
	srli s3, s2, 8
	sb s3, 61(a1)
	srli s3, s2, 16
	sb s3, 62(a1)
	srli s3, s2, 24
	sb s3, 63(a1)
	addi t0, a1, 71
	andi t0, t0, -8
	ld s0, 0(t0)
	ld s1, 8(t0)
	ld s2, 16(t0)
	ld s3, 24(t0)
	ld s4, 32(t0)
	ret
	.option pop

vg_chacha20_xor:
	.option push
	.option arch, +m, +c
	addi t0, a3, 263
	andi t0, t0, -8
	sd s5, 0(t0)
	sd s6, 8(t0)
	sd ra, 16(t0)
	addi s5, a1, 0
	addi s6, a2, 0
	addi a1, a3, 0
	beqz s6, 20f
22:
	call {vg_chacha20_block}
	srli t1, s6, 6
	addi a2, s6, 0
	beqz t1, 23f
	addi a2, zero, 64
	j 24f
23:
24:
	sub s6, s6, a2
	addi t2, a1, 0
25:
	lbu t3, 0(s5)
	lbu t4, 0(t2)
	xor t3, t3, t4
	sb t3, 0(s5)
	addi s5, s5, 1
	addi t2, t2, 1
	addi a2, a2, -1
	bnez a2, 25b
	lbu t1, 48(a0)
	lbu t3, 49(a0)
	slli t3, t3, 8
	or t1, t1, t3
	lbu t3, 50(a0)
	slli t3, t3, 16
	or t1, t1, t3
	lbu t3, 51(a0)
	slli t3, t3, 24
	or t1, t1, t3
	addi t1, t1, 1
	sb t1, 48(a0)
	srli t3, t1, 8
	sb t3, 49(a0)
	srli t3, t1, 16
	sb t3, 50(a0)
	srli t3, t1, 24
	sb t3, 51(a0)
	bnez s6, 22b
	j 21f
20:
21:
	addi t0, a1, 263
	andi t0, t0, -8
	ld ra, 16(t0)
	ld s5, 0(t0)
	ld s6, 8(t0)
	ret
	.option pop

vg_chacha20_init:
	.option push
	.option arch, +m, +c
	lbu t1, 0(a1)
	sb t1, 16(a0)
	lbu t1, 1(a1)
	sb t1, 17(a0)
	lbu t1, 2(a1)
	sb t1, 18(a0)
	lbu t1, 3(a1)
	sb t1, 19(a0)
	lbu t1, 4(a1)
	sb t1, 20(a0)
	lbu t1, 5(a1)
	sb t1, 21(a0)
	lbu t1, 6(a1)
	sb t1, 22(a0)
	lbu t1, 7(a1)
	sb t1, 23(a0)
	lbu t1, 8(a1)
	sb t1, 24(a0)
	lbu t1, 9(a1)
	sb t1, 25(a0)
	lbu t1, 10(a1)
	sb t1, 26(a0)
	lbu t1, 11(a1)
	sb t1, 27(a0)
	lbu t1, 12(a1)
	sb t1, 28(a0)
	lbu t1, 13(a1)
	sb t1, 29(a0)
	lbu t1, 14(a1)
	sb t1, 30(a0)
	lbu t1, 15(a1)
	sb t1, 31(a0)
	lbu t1, 16(a1)
	sb t1, 32(a0)
	lbu t1, 17(a1)
	sb t1, 33(a0)
	lbu t1, 18(a1)
	sb t1, 34(a0)
	lbu t1, 19(a1)
	sb t1, 35(a0)
	lbu t1, 20(a1)
	sb t1, 36(a0)
	lbu t1, 21(a1)
	sb t1, 37(a0)
	lbu t1, 22(a1)
	sb t1, 38(a0)
	lbu t1, 23(a1)
	sb t1, 39(a0)
	lbu t1, 24(a1)
	sb t1, 40(a0)
	lbu t1, 25(a1)
	sb t1, 41(a0)
	lbu t1, 26(a1)
	sb t1, 42(a0)
	lbu t1, 27(a1)
	sb t1, 43(a0)
	lbu t1, 28(a1)
	sb t1, 44(a0)
	lbu t1, 29(a1)
	sb t1, 45(a0)
	lbu t1, 30(a1)
	sb t1, 46(a0)
	lbu t1, 31(a1)
	sb t1, 47(a0)
	addi a1, a2, 0
	lbu t1, 0(a1)
	sb t1, 48(a0)
	lbu t1, 1(a1)
	sb t1, 49(a0)
	lbu t1, 2(a1)
	sb t1, 50(a0)
	lbu t1, 3(a1)
	sb t1, 51(a0)
	lbu t1, 4(a1)
	sb t1, 52(a0)
	lbu t1, 5(a1)
	sb t1, 53(a0)
	lbu t1, 6(a1)
	sb t1, 54(a0)
	lbu t1, 7(a1)
	sb t1, 55(a0)
	lbu t1, 8(a1)
	sb t1, 56(a0)
	lbu t1, 9(a1)
	sb t1, 57(a0)
	lbu t1, 10(a1)
	sb t1, 58(a0)
	lbu t1, 11(a1)
	sb t1, 59(a0)
	lbu t1, 12(a1)
	sb t1, 60(a0)
	lbu t1, 13(a1)
	sb t1, 61(a0)
	lbu t1, 14(a1)
	sb t1, 62(a0)
	lbu t1, 15(a1)
	sb t1, 63(a0)
	addi t1, zero, 101
	sb t1, 0(a0)
	addi t1, zero, 120
	sb t1, 1(a0)
	addi t1, zero, 112
	sb t1, 2(a0)
	addi t1, zero, 97
	sb t1, 3(a0)
	addi t1, zero, 110
	sb t1, 4(a0)
	addi t1, zero, 100
	sb t1, 5(a0)
	addi t1, zero, 32
	sb t1, 6(a0)
	addi t1, zero, 51
	sb t1, 7(a0)
	addi t1, zero, 50
	sb t1, 8(a0)
	addi t1, zero, 45
	sb t1, 9(a0)
	addi t1, zero, 98
	sb t1, 10(a0)
	addi t1, zero, 121
	sb t1, 11(a0)
	addi t1, zero, 116
	sb t1, 12(a0)
	addi t1, zero, 101
	sb t1, 13(a0)
	addi t1, zero, 32
	sb t1, 14(a0)
	addi t1, zero, 107
	sb t1, 15(a0)
	lbu t1, 0(a1)
	lbu t2, 1(a1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(a1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(a1)
	slli t2, t2, 24
	or t1, t1, t2
	addi t2, zero, 1
	slli t2, t2, 32
	sub t2, t2, t1
	slli t2, t2, 6
	sb t2, 128(a0)
	srli t1, t2, 8
	sb t1, 129(a0)
	srli t1, t2, 16
	sb t1, 130(a0)
	srli t1, t2, 24
	sb t1, 131(a0)
	srli t3, t2, 32
	sb t3, 132(a0)
	srli t1, t3, 8
	sb t1, 133(a0)
	srli t1, t3, 16
	sb t1, 134(a0)
	srli t1, t3, 24
	sb t1, 135(a0)
	ret
	.option pop

vg_chacha20_set_nonce:
	.option push
	.option arch, +m, +c
	lbu t1, 0(a1)
	sb t1, 48(a0)
	lbu t1, 1(a1)
	sb t1, 49(a0)
	lbu t1, 2(a1)
	sb t1, 50(a0)
	lbu t1, 3(a1)
	sb t1, 51(a0)
	lbu t1, 4(a1)
	sb t1, 52(a0)
	lbu t1, 5(a1)
	sb t1, 53(a0)
	lbu t1, 6(a1)
	sb t1, 54(a0)
	lbu t1, 7(a1)
	sb t1, 55(a0)
	lbu t1, 8(a1)
	sb t1, 56(a0)
	lbu t1, 9(a1)
	sb t1, 57(a0)
	lbu t1, 10(a1)
	sb t1, 58(a0)
	lbu t1, 11(a1)
	sb t1, 59(a0)
	lbu t1, 12(a1)
	sb t1, 60(a0)
	lbu t1, 13(a1)
	sb t1, 61(a0)
	lbu t1, 14(a1)
	sb t1, 62(a0)
	lbu t1, 15(a1)
	sb t1, 63(a0)
	addi t1, zero, 101
	sb t1, 0(a0)
	addi t1, zero, 120
	sb t1, 1(a0)
	addi t1, zero, 112
	sb t1, 2(a0)
	addi t1, zero, 97
	sb t1, 3(a0)
	addi t1, zero, 110
	sb t1, 4(a0)
	addi t1, zero, 100
	sb t1, 5(a0)
	addi t1, zero, 32
	sb t1, 6(a0)
	addi t1, zero, 51
	sb t1, 7(a0)
	addi t1, zero, 50
	sb t1, 8(a0)
	addi t1, zero, 45
	sb t1, 9(a0)
	addi t1, zero, 98
	sb t1, 10(a0)
	addi t1, zero, 121
	sb t1, 11(a0)
	addi t1, zero, 116
	sb t1, 12(a0)
	addi t1, zero, 101
	sb t1, 13(a0)
	addi t1, zero, 32
	sb t1, 14(a0)
	addi t1, zero, 107
	sb t1, 15(a0)
	lbu t1, 0(a1)
	lbu t2, 1(a1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(a1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(a1)
	slli t2, t2, 24
	or t1, t1, t2
	addi t2, zero, 1
	slli t2, t2, 32
	sub t2, t2, t1
	slli t2, t2, 6
	sb t2, 128(a0)
	srli t1, t2, 8
	sb t1, 129(a0)
	srli t1, t2, 16
	sb t1, 130(a0)
	srli t1, t2, 24
	sb t1, 131(a0)
	srli t3, t2, 32
	sb t3, 132(a0)
	srli t1, t3, 8
	sb t1, 133(a0)
	srli t1, t3, 16
	sb t1, 134(a0)
	srli t1, t3, 24
	sb t1, 135(a0)
	ret
	.option pop

vg_chacha20_apply:
	.option push
	.option arch, +m, +c
	lbu t1, 128(a0)
	lbu t2, 129(a0)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 130(a0)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 131(a0)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t3, 132(a0)
	lbu t2, 133(a0)
	slli t2, t2, 8
	or t3, t3, t2
	lbu t2, 134(a0)
	slli t2, t2, 16
	or t3, t3, t2
	lbu t2, 135(a0)
	slli t2, t2, 24
	or t3, t3, t2
	slli t3, t3, 32
	or t1, t1, t3
	andi t3, t1, 63
	sltu t4, t1, a2
	sltu t5, t3, a2
	bnez t4, 20f
	addi t0, a0, 583
	andi t0, t0, -8
	sd ra, 0(t0)
	sd s5, 8(t0)
	sd s6, 16(t0)
	sd s7, 24(t0)
	sd s8, 32(t0)
	addi s5, a0, 0
	addi s6, a1, 0
	addi s7, a2, 0
	sub s8, t1, a2
	bnez t5, 22f
	j 23f
22:
	addi a2, t3, 0
23:
	addi t2, s5, 128
	sub t2, t2, t3
	beqz a2, 24f
26:
	lbu t3, 0(s6)
	lbu t4, 0(t2)
	xor t3, t3, t4
	sb t3, 0(s6)
	addi s6, s6, 1
	addi t2, t2, 1
	addi a2, a2, -1
	addi s7, s7, -1
	bnez a2, 26b
	j 25f
24:
25:
	srli a2, s7, 6
	slli a2, a2, 6
	beqz a2, 27f
	lbu t1, 0(s5)
	sb t1, 192(s5)
	lbu t1, 1(s5)
	sb t1, 193(s5)
	lbu t1, 2(s5)
	sb t1, 194(s5)
	lbu t1, 3(s5)
	sb t1, 195(s5)
	lbu t1, 4(s5)
	sb t1, 196(s5)
	lbu t1, 5(s5)
	sb t1, 197(s5)
	lbu t1, 6(s5)
	sb t1, 198(s5)
	lbu t1, 7(s5)
	sb t1, 199(s5)
	lbu t1, 8(s5)
	sb t1, 200(s5)
	lbu t1, 9(s5)
	sb t1, 201(s5)
	lbu t1, 10(s5)
	sb t1, 202(s5)
	lbu t1, 11(s5)
	sb t1, 203(s5)
	lbu t1, 12(s5)
	sb t1, 204(s5)
	lbu t1, 13(s5)
	sb t1, 205(s5)
	lbu t1, 14(s5)
	sb t1, 206(s5)
	lbu t1, 15(s5)
	sb t1, 207(s5)
	lbu t1, 16(s5)
	sb t1, 208(s5)
	lbu t1, 17(s5)
	sb t1, 209(s5)
	lbu t1, 18(s5)
	sb t1, 210(s5)
	lbu t1, 19(s5)
	sb t1, 211(s5)
	lbu t1, 20(s5)
	sb t1, 212(s5)
	lbu t1, 21(s5)
	sb t1, 213(s5)
	lbu t1, 22(s5)
	sb t1, 214(s5)
	lbu t1, 23(s5)
	sb t1, 215(s5)
	lbu t1, 24(s5)
	sb t1, 216(s5)
	lbu t1, 25(s5)
	sb t1, 217(s5)
	lbu t1, 26(s5)
	sb t1, 218(s5)
	lbu t1, 27(s5)
	sb t1, 219(s5)
	lbu t1, 28(s5)
	sb t1, 220(s5)
	lbu t1, 29(s5)
	sb t1, 221(s5)
	lbu t1, 30(s5)
	sb t1, 222(s5)
	lbu t1, 31(s5)
	sb t1, 223(s5)
	lbu t1, 32(s5)
	sb t1, 224(s5)
	lbu t1, 33(s5)
	sb t1, 225(s5)
	lbu t1, 34(s5)
	sb t1, 226(s5)
	lbu t1, 35(s5)
	sb t1, 227(s5)
	lbu t1, 36(s5)
	sb t1, 228(s5)
	lbu t1, 37(s5)
	sb t1, 229(s5)
	lbu t1, 38(s5)
	sb t1, 230(s5)
	lbu t1, 39(s5)
	sb t1, 231(s5)
	lbu t1, 40(s5)
	sb t1, 232(s5)
	lbu t1, 41(s5)
	sb t1, 233(s5)
	lbu t1, 42(s5)
	sb t1, 234(s5)
	lbu t1, 43(s5)
	sb t1, 235(s5)
	lbu t1, 44(s5)
	sb t1, 236(s5)
	lbu t1, 45(s5)
	sb t1, 237(s5)
	lbu t1, 46(s5)
	sb t1, 238(s5)
	lbu t1, 47(s5)
	sb t1, 239(s5)
	lbu t1, 48(s5)
	sb t1, 240(s5)
	lbu t1, 49(s5)
	sb t1, 241(s5)
	lbu t1, 50(s5)
	sb t1, 242(s5)
	lbu t1, 51(s5)
	sb t1, 243(s5)
	lbu t1, 52(s5)
	sb t1, 244(s5)
	lbu t1, 53(s5)
	sb t1, 245(s5)
	lbu t1, 54(s5)
	sb t1, 246(s5)
	lbu t1, 55(s5)
	sb t1, 247(s5)
	lbu t1, 56(s5)
	sb t1, 248(s5)
	lbu t1, 57(s5)
	sb t1, 249(s5)
	lbu t1, 58(s5)
	sb t1, 250(s5)
	lbu t1, 59(s5)
	sb t1, 251(s5)
	lbu t1, 60(s5)
	sb t1, 252(s5)
	lbu t1, 61(s5)
	sb t1, 253(s5)
	lbu t1, 62(s5)
	sb t1, 254(s5)
	lbu t1, 63(s5)
	sb t1, 255(s5)
	srli t4, a2, 6
	lbu t1, 48(s5)
	lbu t3, 49(s5)
	slli t3, t3, 8
	or t1, t1, t3
	lbu t3, 50(s5)
	slli t3, t3, 16
	or t1, t1, t3
	lbu t3, 51(s5)
	slli t3, t3, 24
	or t1, t1, t3
	add t1, t1, t4
	sb t1, 48(s5)
	srli t3, t1, 8
	sb t3, 49(s5)
	srli t3, t1, 16
	sb t3, 50(s5)
	srli t3, t1, 24
	sb t3, 51(s5)
	addi a0, s5, 192
	addi a1, s6, 0
	addi a3, s5, 256
	add s6, s6, a2
	sub s7, s7, a2
	call {vg_chacha20_xor}
	j 28f
27:
28:
	beqz s7, 29f
	addi a0, s5, 0
	addi a1, s5, 64
	call {vg_chacha20_block}
	lbu t1, 48(s5)
	lbu t3, 49(s5)
	slli t3, t3, 8
	or t1, t1, t3
	lbu t3, 50(s5)
	slli t3, t3, 16
	or t1, t1, t3
	lbu t3, 51(s5)
	slli t3, t3, 24
	or t1, t1, t3
	addi t1, t1, 1
	sb t1, 48(s5)
	srli t3, t1, 8
	sb t3, 49(s5)
	srli t3, t1, 16
	sb t3, 50(s5)
	srli t3, t1, 24
	sb t3, 51(s5)
	addi t2, s5, 64
	addi a2, s7, 0
	beqz a2, 211f
213:
	lbu t3, 0(s6)
	lbu t4, 0(t2)
	xor t3, t3, t4
	sb t3, 0(s6)
	addi s6, s6, 1
	addi t2, t2, 1
	addi a2, a2, -1
	addi s7, s7, -1
	bnez a2, 213b
	j 212f
211:
212:
	j 210f
29:
210:
	sb s8, 128(s5)
	srli t1, s8, 8
	sb t1, 129(s5)
	srli t1, s8, 16
	sb t1, 130(s5)
	srli t1, s8, 24
	sb t1, 131(s5)
	srli t2, s8, 32
	sb t2, 132(s5)
	srli t1, t2, 8
	sb t1, 133(s5)
	srli t1, t2, 16
	sb t1, 134(s5)
	srli t1, t2, 24
	sb t1, 135(s5)
	addi t0, s5, 583
	andi t0, t0, -8
	ld ra, 0(t0)
	ld s6, 16(t0)
	ld s7, 24(t0)
	ld s8, 32(t0)
	ld s5, 8(t0)
	addi a0, zero, 1
	j 21f
20:
	addi a0, zero, 0
21:
	ret
	.option pop
