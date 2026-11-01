// The functions of `src/internal/vg_blake2s_compress.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blake2s_compress:
	.option push
	.option arch, +m, +c
	addi a5, a5, 7
	andi a5, a5, -8
	sd s0, 0(a5)
	sd s1, 8(a5)
	sd s2, 16(a5)
	sd s3, 24(a5)
	sd s4, 32(a5)
	sd s5, 40(a5)
	sd s6, 48(a5)
	sd a3, 56(a5)
	addi t6, zero, 0
	sd t6, 64(a5)
	slli a4, a4, 32
	srli a4, a4, 32
	sub a3, t6, a4
	or a4, a4, a3
	srli a4, a4, 63
	sub a4, t6, a4
	sd a4, 72(a5)
	lbu t6, 0(a0)
	lbu a3, 1(a0)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 2(a0)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 3(a0)
	slli a3, a3, 24
	or t6, t6, a3
	sw t6, 80(a5)
	lbu t6, 4(a0)
	lbu a3, 5(a0)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 6(a0)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 7(a0)
	slli a3, a3, 24
	or t6, t6, a3
	sw t6, 84(a5)
	lbu t6, 8(a0)
	lbu a3, 9(a0)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 10(a0)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 11(a0)
	slli a3, a3, 24
	or t6, t6, a3
	sw t6, 88(a5)
	lbu t6, 12(a0)
	lbu a3, 13(a0)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 14(a0)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 15(a0)
	slli a3, a3, 24
	or t6, t6, a3
	sw t6, 92(a5)
	lbu t6, 16(a0)
	lbu a3, 17(a0)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 18(a0)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 19(a0)
	slli a3, a3, 24
	or t6, t6, a3
	sw t6, 96(a5)
	lbu t6, 20(a0)
	lbu a3, 21(a0)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 22(a0)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 23(a0)
	slli a3, a3, 24
	or t6, t6, a3
	sw t6, 100(a5)
	lbu t6, 24(a0)
	lbu a3, 25(a0)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 26(a0)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 27(a0)
	slli a3, a3, 24
	or t6, t6, a3
	sw t6, 104(a5)
	lbu t6, 28(a0)
	lbu a3, 29(a0)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 30(a0)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 31(a0)
	slli a3, a3, 24
	or t6, t6, a3
	sw t6, 108(a5)
	beqz a2, 20f
22:
	lbu t6, 0(a1)
	lbu a3, 1(a1)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 2(a1)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 3(a1)
	slli a3, a3, 24
	or t6, t6, a3
	sw t6, 144(a5)
	lbu t6, 4(a1)
	lbu a3, 5(a1)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 6(a1)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 7(a1)
	slli a3, a3, 24
	or t6, t6, a3
	sw t6, 148(a5)
	lbu t6, 8(a1)
	lbu a3, 9(a1)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 10(a1)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 11(a1)
	slli a3, a3, 24
	or t6, t6, a3
	sw t6, 152(a5)
	lbu t6, 12(a1)
	lbu a3, 13(a1)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 14(a1)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 15(a1)
	slli a3, a3, 24
	or t6, t6, a3
	sw t6, 156(a5)
	lbu t6, 16(a1)
	lbu a3, 17(a1)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 18(a1)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 19(a1)
	slli a3, a3, 24
	or t6, t6, a3
	sw t6, 160(a5)
	lbu t6, 20(a1)
	lbu a3, 21(a1)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 22(a1)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 23(a1)
	slli a3, a3, 24
	or t6, t6, a3
	sw t6, 164(a5)
	lbu t6, 24(a1)
	lbu a3, 25(a1)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 26(a1)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 27(a1)
	slli a3, a3, 24
	or t6, t6, a3
	sw t6, 168(a5)
	lbu t6, 28(a1)
	lbu a3, 29(a1)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 30(a1)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 31(a1)
	slli a3, a3, 24
	or t6, t6, a3
	sw t6, 172(a5)
	lbu t6, 32(a1)
	lbu a3, 33(a1)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 34(a1)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 35(a1)
	slli a3, a3, 24
	or t6, t6, a3
	sw t6, 176(a5)
	lbu t6, 36(a1)
	lbu a3, 37(a1)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 38(a1)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 39(a1)
	slli a3, a3, 24
	or t6, t6, a3
	sw t6, 180(a5)
	lbu t6, 40(a1)
	lbu a3, 41(a1)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 42(a1)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 43(a1)
	slli a3, a3, 24
	or t6, t6, a3
	sw t6, 184(a5)
	lbu t6, 44(a1)
	lbu a3, 45(a1)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 46(a1)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 47(a1)
	slli a3, a3, 24
	or t6, t6, a3
	sw t6, 188(a5)
	lbu t6, 48(a1)
	lbu a3, 49(a1)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 50(a1)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 51(a1)
	slli a3, a3, 24
	or t6, t6, a3
	sw t6, 192(a5)
	lbu t6, 52(a1)
	lbu a3, 53(a1)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 54(a1)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 55(a1)
	slli a3, a3, 24
	or t6, t6, a3
	sw t6, 196(a5)
	lbu t6, 56(a1)
	lbu a3, 57(a1)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 58(a1)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 59(a1)
	slli a3, a3, 24
	or t6, t6, a3
	sw t6, 200(a5)
	lbu t6, 60(a1)
	lbu a3, 61(a1)
	slli a3, a3, 8
	or t6, t6, a3
	lbu a3, 62(a1)
	slli a3, a3, 16
	or t6, t6, a3
	lbu a3, 63(a1)
	slli a3, a3, 24
	or t6, t6, a3
	sw t6, 204(a5)
	lwu a3, 80(a5)
	lwu a4, 84(a5)
	lwu a6, 88(a5)
	lwu a7, 92(a5)
	lwu t0, 96(a5)
	lwu t1, 100(a5)
	lwu t2, 104(a5)
	lwu t3, 108(a5)
	lui t4, 434334
	addiw t4, t4, 1639
	lui t5, 767611
	addiw t5, t5, -379
	lui s0, 247535
	addiw s0, s0, 882
	lui s1, 677119
	addiw s1, s1, 1338
	lui s2, 332005
	addiw s2, s2, 639
	lui s3, 634967
	addiw s3, s3, -1908
	lui s4, 129086
	addiw s4, s4, -1621
	lui s5, 376333
	addiw s5, s5, -743
	ld t6, 56(a5)
	xor s2, s2, t6
	ld t6, 56(a5)
	srli t6, t6, 32
	xor s3, s3, t6
	ld t6, 72(a5)
	xor s4, s4, t6
	lwu t6, 144(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srliw s6, s2, 16
	slliw s2, s2, 16
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srliw s6, t0, 12
	slliw t0, t0, 20
	or t0, t0, s6
	lwu t6, 148(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srliw s6, s2, 8
	slliw s2, s2, 24
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srliw s6, t0, 7
	slliw t0, t0, 25
	or t0, t0, s6
	lwu t6, 152(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srliw s6, s3, 16
	slliw s3, s3, 16
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srliw s6, t1, 12
	slliw t1, t1, 20
	or t1, t1, s6
	lwu t6, 156(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srliw s6, s3, 8
	slliw s3, s3, 24
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srliw s6, t1, 7
	slliw t1, t1, 25
	or t1, t1, s6
	lwu t6, 160(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srliw s6, s4, 16
	slliw s4, s4, 16
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srliw s6, t2, 12
	slliw t2, t2, 20
	or t2, t2, s6
	lwu t6, 164(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srliw s6, s4, 8
	slliw s4, s4, 24
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srliw s6, t2, 7
	slliw t2, t2, 25
	or t2, t2, s6
	lwu t6, 168(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srliw s6, s5, 16
	slliw s5, s5, 16
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srliw s6, t3, 12
	slliw t3, t3, 20
	or t3, t3, s6
	lwu t6, 172(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srliw s6, s5, 8
	slliw s5, s5, 24
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srliw s6, t3, 7
	slliw t3, t3, 25
	or t3, t3, s6
	lwu t6, 176(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srliw s6, s5, 16
	slliw s5, s5, 16
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srliw s6, t1, 12
	slliw t1, t1, 20
	or t1, t1, s6
	lwu t6, 180(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srliw s6, s5, 8
	slliw s5, s5, 24
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srliw s6, t1, 7
	slliw t1, t1, 25
	or t1, t1, s6
	lwu t6, 184(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srliw s6, s2, 16
	slliw s2, s2, 16
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srliw s6, t2, 12
	slliw t2, t2, 20
	or t2, t2, s6
	lwu t6, 188(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srliw s6, s2, 8
	slliw s2, s2, 24
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srliw s6, t2, 7
	slliw t2, t2, 25
	or t2, t2, s6
	lwu t6, 192(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srliw s6, s3, 16
	slliw s3, s3, 16
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srliw s6, t3, 12
	slliw t3, t3, 20
	or t3, t3, s6
	lwu t6, 196(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srliw s6, s3, 8
	slliw s3, s3, 24
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srliw s6, t3, 7
	slliw t3, t3, 25
	or t3, t3, s6
	lwu t6, 200(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srliw s6, s4, 16
	slliw s4, s4, 16
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srliw s6, t0, 12
	slliw t0, t0, 20
	or t0, t0, s6
	lwu t6, 204(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srliw s6, s4, 8
	slliw s4, s4, 24
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srliw s6, t0, 7
	slliw t0, t0, 25
	or t0, t0, s6
	lwu t6, 200(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srliw s6, s2, 16
	slliw s2, s2, 16
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srliw s6, t0, 12
	slliw t0, t0, 20
	or t0, t0, s6
	lwu t6, 184(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srliw s6, s2, 8
	slliw s2, s2, 24
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srliw s6, t0, 7
	slliw t0, t0, 25
	or t0, t0, s6
	lwu t6, 160(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srliw s6, s3, 16
	slliw s3, s3, 16
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srliw s6, t1, 12
	slliw t1, t1, 20
	or t1, t1, s6
	lwu t6, 176(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srliw s6, s3, 8
	slliw s3, s3, 24
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srliw s6, t1, 7
	slliw t1, t1, 25
	or t1, t1, s6
	lwu t6, 180(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srliw s6, s4, 16
	slliw s4, s4, 16
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srliw s6, t2, 12
	slliw t2, t2, 20
	or t2, t2, s6
	lwu t6, 204(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srliw s6, s4, 8
	slliw s4, s4, 24
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srliw s6, t2, 7
	slliw t2, t2, 25
	or t2, t2, s6
	lwu t6, 196(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srliw s6, s5, 16
	slliw s5, s5, 16
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srliw s6, t3, 12
	slliw t3, t3, 20
	or t3, t3, s6
	lwu t6, 168(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srliw s6, s5, 8
	slliw s5, s5, 24
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srliw s6, t3, 7
	slliw t3, t3, 25
	or t3, t3, s6
	lwu t6, 148(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srliw s6, s5, 16
	slliw s5, s5, 16
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srliw s6, t1, 12
	slliw t1, t1, 20
	or t1, t1, s6
	lwu t6, 192(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srliw s6, s5, 8
	slliw s5, s5, 24
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srliw s6, t1, 7
	slliw t1, t1, 25
	or t1, t1, s6
	lwu t6, 144(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srliw s6, s2, 16
	slliw s2, s2, 16
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srliw s6, t2, 12
	slliw t2, t2, 20
	or t2, t2, s6
	lwu t6, 152(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srliw s6, s2, 8
	slliw s2, s2, 24
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srliw s6, t2, 7
	slliw t2, t2, 25
	or t2, t2, s6
	lwu t6, 188(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srliw s6, s3, 16
	slliw s3, s3, 16
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srliw s6, t3, 12
	slliw t3, t3, 20
	or t3, t3, s6
	lwu t6, 172(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srliw s6, s3, 8
	slliw s3, s3, 24
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srliw s6, t3, 7
	slliw t3, t3, 25
	or t3, t3, s6
	lwu t6, 164(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srliw s6, s4, 16
	slliw s4, s4, 16
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srliw s6, t0, 12
	slliw t0, t0, 20
	or t0, t0, s6
	lwu t6, 156(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srliw s6, s4, 8
	slliw s4, s4, 24
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srliw s6, t0, 7
	slliw t0, t0, 25
	or t0, t0, s6
	lwu t6, 188(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srliw s6, s2, 16
	slliw s2, s2, 16
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srliw s6, t0, 12
	slliw t0, t0, 20
	or t0, t0, s6
	lwu t6, 176(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srliw s6, s2, 8
	slliw s2, s2, 24
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srliw s6, t0, 7
	slliw t0, t0, 25
	or t0, t0, s6
	lwu t6, 192(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srliw s6, s3, 16
	slliw s3, s3, 16
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srliw s6, t1, 12
	slliw t1, t1, 20
	or t1, t1, s6
	lwu t6, 144(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srliw s6, s3, 8
	slliw s3, s3, 24
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srliw s6, t1, 7
	slliw t1, t1, 25
	or t1, t1, s6
	lwu t6, 164(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srliw s6, s4, 16
	slliw s4, s4, 16
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srliw s6, t2, 12
	slliw t2, t2, 20
	or t2, t2, s6
	lwu t6, 152(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srliw s6, s4, 8
	slliw s4, s4, 24
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srliw s6, t2, 7
	slliw t2, t2, 25
	or t2, t2, s6
	lwu t6, 204(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srliw s6, s5, 16
	slliw s5, s5, 16
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srliw s6, t3, 12
	slliw t3, t3, 20
	or t3, t3, s6
	lwu t6, 196(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srliw s6, s5, 8
	slliw s5, s5, 24
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srliw s6, t3, 7
	slliw t3, t3, 25
	or t3, t3, s6
	lwu t6, 184(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srliw s6, s5, 16
	slliw s5, s5, 16
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srliw s6, t1, 12
	slliw t1, t1, 20
	or t1, t1, s6
	lwu t6, 200(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srliw s6, s5, 8
	slliw s5, s5, 24
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srliw s6, t1, 7
	slliw t1, t1, 25
	or t1, t1, s6
	lwu t6, 156(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srliw s6, s2, 16
	slliw s2, s2, 16
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srliw s6, t2, 12
	slliw t2, t2, 20
	or t2, t2, s6
	lwu t6, 168(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srliw s6, s2, 8
	slliw s2, s2, 24
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srliw s6, t2, 7
	slliw t2, t2, 25
	or t2, t2, s6
	lwu t6, 172(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srliw s6, s3, 16
	slliw s3, s3, 16
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srliw s6, t3, 12
	slliw t3, t3, 20
	or t3, t3, s6
	lwu t6, 148(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srliw s6, s3, 8
	slliw s3, s3, 24
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srliw s6, t3, 7
	slliw t3, t3, 25
	or t3, t3, s6
	lwu t6, 180(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srliw s6, s4, 16
	slliw s4, s4, 16
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srliw s6, t0, 12
	slliw t0, t0, 20
	or t0, t0, s6
	lwu t6, 160(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srliw s6, s4, 8
	slliw s4, s4, 24
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srliw s6, t0, 7
	slliw t0, t0, 25
	or t0, t0, s6
	lwu t6, 172(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srliw s6, s2, 16
	slliw s2, s2, 16
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srliw s6, t0, 12
	slliw t0, t0, 20
	or t0, t0, s6
	lwu t6, 180(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srliw s6, s2, 8
	slliw s2, s2, 24
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srliw s6, t0, 7
	slliw t0, t0, 25
	or t0, t0, s6
	lwu t6, 156(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srliw s6, s3, 16
	slliw s3, s3, 16
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srliw s6, t1, 12
	slliw t1, t1, 20
	or t1, t1, s6
	lwu t6, 148(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srliw s6, s3, 8
	slliw s3, s3, 24
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srliw s6, t1, 7
	slliw t1, t1, 25
	or t1, t1, s6
	lwu t6, 196(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srliw s6, s4, 16
	slliw s4, s4, 16
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srliw s6, t2, 12
	slliw t2, t2, 20
	or t2, t2, s6
	lwu t6, 192(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srliw s6, s4, 8
	slliw s4, s4, 24
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srliw s6, t2, 7
	slliw t2, t2, 25
	or t2, t2, s6
	lwu t6, 188(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srliw s6, s5, 16
	slliw s5, s5, 16
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srliw s6, t3, 12
	slliw t3, t3, 20
	or t3, t3, s6
	lwu t6, 200(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srliw s6, s5, 8
	slliw s5, s5, 24
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srliw s6, t3, 7
	slliw t3, t3, 25
	or t3, t3, s6
	lwu t6, 152(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srliw s6, s5, 16
	slliw s5, s5, 16
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srliw s6, t1, 12
	slliw t1, t1, 20
	or t1, t1, s6
	lwu t6, 168(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srliw s6, s5, 8
	slliw s5, s5, 24
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srliw s6, t1, 7
	slliw t1, t1, 25
	or t1, t1, s6
	lwu t6, 164(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srliw s6, s2, 16
	slliw s2, s2, 16
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srliw s6, t2, 12
	slliw t2, t2, 20
	or t2, t2, s6
	lwu t6, 184(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srliw s6, s2, 8
	slliw s2, s2, 24
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srliw s6, t2, 7
	slliw t2, t2, 25
	or t2, t2, s6
	lwu t6, 160(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srliw s6, s3, 16
	slliw s3, s3, 16
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srliw s6, t3, 12
	slliw t3, t3, 20
	or t3, t3, s6
	lwu t6, 144(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srliw s6, s3, 8
	slliw s3, s3, 24
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srliw s6, t3, 7
	slliw t3, t3, 25
	or t3, t3, s6
	lwu t6, 204(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srliw s6, s4, 16
	slliw s4, s4, 16
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srliw s6, t0, 12
	slliw t0, t0, 20
	or t0, t0, s6
	lwu t6, 176(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srliw s6, s4, 8
	slliw s4, s4, 24
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srliw s6, t0, 7
	slliw t0, t0, 25
	or t0, t0, s6
	lwu t6, 180(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srliw s6, s2, 16
	slliw s2, s2, 16
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srliw s6, t0, 12
	slliw t0, t0, 20
	or t0, t0, s6
	lwu t6, 144(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srliw s6, s2, 8
	slliw s2, s2, 24
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srliw s6, t0, 7
	slliw t0, t0, 25
	or t0, t0, s6
	lwu t6, 164(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srliw s6, s3, 16
	slliw s3, s3, 16
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srliw s6, t1, 12
	slliw t1, t1, 20
	or t1, t1, s6
	lwu t6, 172(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srliw s6, s3, 8
	slliw s3, s3, 24
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srliw s6, t1, 7
	slliw t1, t1, 25
	or t1, t1, s6
	lwu t6, 152(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srliw s6, s4, 16
	slliw s4, s4, 16
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srliw s6, t2, 12
	slliw t2, t2, 20
	or t2, t2, s6
	lwu t6, 160(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srliw s6, s4, 8
	slliw s4, s4, 24
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srliw s6, t2, 7
	slliw t2, t2, 25
	or t2, t2, s6
	lwu t6, 184(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srliw s6, s5, 16
	slliw s5, s5, 16
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srliw s6, t3, 12
	slliw t3, t3, 20
	or t3, t3, s6
	lwu t6, 204(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srliw s6, s5, 8
	slliw s5, s5, 24
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srliw s6, t3, 7
	slliw t3, t3, 25
	or t3, t3, s6
	lwu t6, 200(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srliw s6, s5, 16
	slliw s5, s5, 16
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srliw s6, t1, 12
	slliw t1, t1, 20
	or t1, t1, s6
	lwu t6, 148(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srliw s6, s5, 8
	slliw s5, s5, 24
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srliw s6, t1, 7
	slliw t1, t1, 25
	or t1, t1, s6
	lwu t6, 188(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srliw s6, s2, 16
	slliw s2, s2, 16
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srliw s6, t2, 12
	slliw t2, t2, 20
	or t2, t2, s6
	lwu t6, 192(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srliw s6, s2, 8
	slliw s2, s2, 24
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srliw s6, t2, 7
	slliw t2, t2, 25
	or t2, t2, s6
	lwu t6, 168(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srliw s6, s3, 16
	slliw s3, s3, 16
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srliw s6, t3, 12
	slliw t3, t3, 20
	or t3, t3, s6
	lwu t6, 176(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srliw s6, s3, 8
	slliw s3, s3, 24
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srliw s6, t3, 7
	slliw t3, t3, 25
	or t3, t3, s6
	lwu t6, 156(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srliw s6, s4, 16
	slliw s4, s4, 16
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srliw s6, t0, 12
	slliw t0, t0, 20
	or t0, t0, s6
	lwu t6, 196(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srliw s6, s4, 8
	slliw s4, s4, 24
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srliw s6, t0, 7
	slliw t0, t0, 25
	or t0, t0, s6
	lwu t6, 152(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srliw s6, s2, 16
	slliw s2, s2, 16
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srliw s6, t0, 12
	slliw t0, t0, 20
	or t0, t0, s6
	lwu t6, 192(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srliw s6, s2, 8
	slliw s2, s2, 24
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srliw s6, t0, 7
	slliw t0, t0, 25
	or t0, t0, s6
	lwu t6, 168(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srliw s6, s3, 16
	slliw s3, s3, 16
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srliw s6, t1, 12
	slliw t1, t1, 20
	or t1, t1, s6
	lwu t6, 184(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srliw s6, s3, 8
	slliw s3, s3, 24
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srliw s6, t1, 7
	slliw t1, t1, 25
	or t1, t1, s6
	lwu t6, 144(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srliw s6, s4, 16
	slliw s4, s4, 16
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srliw s6, t2, 12
	slliw t2, t2, 20
	or t2, t2, s6
	lwu t6, 188(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srliw s6, s4, 8
	slliw s4, s4, 24
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srliw s6, t2, 7
	slliw t2, t2, 25
	or t2, t2, s6
	lwu t6, 176(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srliw s6, s5, 16
	slliw s5, s5, 16
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srliw s6, t3, 12
	slliw t3, t3, 20
	or t3, t3, s6
	lwu t6, 156(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srliw s6, s5, 8
	slliw s5, s5, 24
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srliw s6, t3, 7
	slliw t3, t3, 25
	or t3, t3, s6
	lwu t6, 160(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srliw s6, s5, 16
	slliw s5, s5, 16
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srliw s6, t1, 12
	slliw t1, t1, 20
	or t1, t1, s6
	lwu t6, 196(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srliw s6, s5, 8
	slliw s5, s5, 24
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srliw s6, t1, 7
	slliw t1, t1, 25
	or t1, t1, s6
	lwu t6, 172(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srliw s6, s2, 16
	slliw s2, s2, 16
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srliw s6, t2, 12
	slliw t2, t2, 20
	or t2, t2, s6
	lwu t6, 164(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srliw s6, s2, 8
	slliw s2, s2, 24
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srliw s6, t2, 7
	slliw t2, t2, 25
	or t2, t2, s6
	lwu t6, 204(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srliw s6, s3, 16
	slliw s3, s3, 16
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srliw s6, t3, 12
	slliw t3, t3, 20
	or t3, t3, s6
	lwu t6, 200(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srliw s6, s3, 8
	slliw s3, s3, 24
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srliw s6, t3, 7
	slliw t3, t3, 25
	or t3, t3, s6
	lwu t6, 148(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srliw s6, s4, 16
	slliw s4, s4, 16
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srliw s6, t0, 12
	slliw t0, t0, 20
	or t0, t0, s6
	lwu t6, 180(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srliw s6, s4, 8
	slliw s4, s4, 24
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srliw s6, t0, 7
	slliw t0, t0, 25
	or t0, t0, s6
	lwu t6, 192(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srliw s6, s2, 16
	slliw s2, s2, 16
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srliw s6, t0, 12
	slliw t0, t0, 20
	or t0, t0, s6
	lwu t6, 164(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srliw s6, s2, 8
	slliw s2, s2, 24
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srliw s6, t0, 7
	slliw t0, t0, 25
	or t0, t0, s6
	lwu t6, 148(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srliw s6, s3, 16
	slliw s3, s3, 16
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srliw s6, t1, 12
	slliw t1, t1, 20
	or t1, t1, s6
	lwu t6, 204(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srliw s6, s3, 8
	slliw s3, s3, 24
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srliw s6, t1, 7
	slliw t1, t1, 25
	or t1, t1, s6
	lwu t6, 200(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srliw s6, s4, 16
	slliw s4, s4, 16
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srliw s6, t2, 12
	slliw t2, t2, 20
	or t2, t2, s6
	lwu t6, 196(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srliw s6, s4, 8
	slliw s4, s4, 24
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srliw s6, t2, 7
	slliw t2, t2, 25
	or t2, t2, s6
	lwu t6, 160(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srliw s6, s5, 16
	slliw s5, s5, 16
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srliw s6, t3, 12
	slliw t3, t3, 20
	or t3, t3, s6
	lwu t6, 184(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srliw s6, s5, 8
	slliw s5, s5, 24
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srliw s6, t3, 7
	slliw t3, t3, 25
	or t3, t3, s6
	lwu t6, 144(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srliw s6, s5, 16
	slliw s5, s5, 16
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srliw s6, t1, 12
	slliw t1, t1, 20
	or t1, t1, s6
	lwu t6, 172(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srliw s6, s5, 8
	slliw s5, s5, 24
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srliw s6, t1, 7
	slliw t1, t1, 25
	or t1, t1, s6
	lwu t6, 168(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srliw s6, s2, 16
	slliw s2, s2, 16
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srliw s6, t2, 12
	slliw t2, t2, 20
	or t2, t2, s6
	lwu t6, 156(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srliw s6, s2, 8
	slliw s2, s2, 24
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srliw s6, t2, 7
	slliw t2, t2, 25
	or t2, t2, s6
	lwu t6, 180(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srliw s6, s3, 16
	slliw s3, s3, 16
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srliw s6, t3, 12
	slliw t3, t3, 20
	or t3, t3, s6
	lwu t6, 152(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srliw s6, s3, 8
	slliw s3, s3, 24
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srliw s6, t3, 7
	slliw t3, t3, 25
	or t3, t3, s6
	lwu t6, 176(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srliw s6, s4, 16
	slliw s4, s4, 16
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srliw s6, t0, 12
	slliw t0, t0, 20
	or t0, t0, s6
	lwu t6, 188(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srliw s6, s4, 8
	slliw s4, s4, 24
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srliw s6, t0, 7
	slliw t0, t0, 25
	or t0, t0, s6
	lwu t6, 196(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srliw s6, s2, 16
	slliw s2, s2, 16
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srliw s6, t0, 12
	slliw t0, t0, 20
	or t0, t0, s6
	lwu t6, 188(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srliw s6, s2, 8
	slliw s2, s2, 24
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srliw s6, t0, 7
	slliw t0, t0, 25
	or t0, t0, s6
	lwu t6, 172(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srliw s6, s3, 16
	slliw s3, s3, 16
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srliw s6, t1, 12
	slliw t1, t1, 20
	or t1, t1, s6
	lwu t6, 200(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srliw s6, s3, 8
	slliw s3, s3, 24
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srliw s6, t1, 7
	slliw t1, t1, 25
	or t1, t1, s6
	lwu t6, 192(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srliw s6, s4, 16
	slliw s4, s4, 16
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srliw s6, t2, 12
	slliw t2, t2, 20
	or t2, t2, s6
	lwu t6, 148(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srliw s6, s4, 8
	slliw s4, s4, 24
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srliw s6, t2, 7
	slliw t2, t2, 25
	or t2, t2, s6
	lwu t6, 156(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srliw s6, s5, 16
	slliw s5, s5, 16
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srliw s6, t3, 12
	slliw t3, t3, 20
	or t3, t3, s6
	lwu t6, 180(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srliw s6, s5, 8
	slliw s5, s5, 24
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srliw s6, t3, 7
	slliw t3, t3, 25
	or t3, t3, s6
	lwu t6, 164(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srliw s6, s5, 16
	slliw s5, s5, 16
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srliw s6, t1, 12
	slliw t1, t1, 20
	or t1, t1, s6
	lwu t6, 144(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srliw s6, s5, 8
	slliw s5, s5, 24
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srliw s6, t1, 7
	slliw t1, t1, 25
	or t1, t1, s6
	lwu t6, 204(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srliw s6, s2, 16
	slliw s2, s2, 16
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srliw s6, t2, 12
	slliw t2, t2, 20
	or t2, t2, s6
	lwu t6, 160(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srliw s6, s2, 8
	slliw s2, s2, 24
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srliw s6, t2, 7
	slliw t2, t2, 25
	or t2, t2, s6
	lwu t6, 176(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srliw s6, s3, 16
	slliw s3, s3, 16
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srliw s6, t3, 12
	slliw t3, t3, 20
	or t3, t3, s6
	lwu t6, 168(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srliw s6, s3, 8
	slliw s3, s3, 24
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srliw s6, t3, 7
	slliw t3, t3, 25
	or t3, t3, s6
	lwu t6, 152(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srliw s6, s4, 16
	slliw s4, s4, 16
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srliw s6, t0, 12
	slliw t0, t0, 20
	or t0, t0, s6
	lwu t6, 184(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srliw s6, s4, 8
	slliw s4, s4, 24
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srliw s6, t0, 7
	slliw t0, t0, 25
	or t0, t0, s6
	lwu t6, 168(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srliw s6, s2, 16
	slliw s2, s2, 16
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srliw s6, t0, 12
	slliw t0, t0, 20
	or t0, t0, s6
	lwu t6, 204(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srliw s6, s2, 8
	slliw s2, s2, 24
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srliw s6, t0, 7
	slliw t0, t0, 25
	or t0, t0, s6
	lwu t6, 200(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srliw s6, s3, 16
	slliw s3, s3, 16
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srliw s6, t1, 12
	slliw t1, t1, 20
	or t1, t1, s6
	lwu t6, 180(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srliw s6, s3, 8
	slliw s3, s3, 24
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srliw s6, t1, 7
	slliw t1, t1, 25
	or t1, t1, s6
	lwu t6, 188(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srliw s6, s4, 16
	slliw s4, s4, 16
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srliw s6, t2, 12
	slliw t2, t2, 20
	or t2, t2, s6
	lwu t6, 156(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srliw s6, s4, 8
	slliw s4, s4, 24
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srliw s6, t2, 7
	slliw t2, t2, 25
	or t2, t2, s6
	lwu t6, 144(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srliw s6, s5, 16
	slliw s5, s5, 16
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srliw s6, t3, 12
	slliw t3, t3, 20
	or t3, t3, s6
	lwu t6, 176(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srliw s6, s5, 8
	slliw s5, s5, 24
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srliw s6, t3, 7
	slliw t3, t3, 25
	or t3, t3, s6
	lwu t6, 192(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srliw s6, s5, 16
	slliw s5, s5, 16
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srliw s6, t1, 12
	slliw t1, t1, 20
	or t1, t1, s6
	lwu t6, 152(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srliw s6, s5, 8
	slliw s5, s5, 24
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srliw s6, t1, 7
	slliw t1, t1, 25
	or t1, t1, s6
	lwu t6, 196(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srliw s6, s2, 16
	slliw s2, s2, 16
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srliw s6, t2, 12
	slliw t2, t2, 20
	or t2, t2, s6
	lwu t6, 172(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srliw s6, s2, 8
	slliw s2, s2, 24
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srliw s6, t2, 7
	slliw t2, t2, 25
	or t2, t2, s6
	lwu t6, 148(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srliw s6, s3, 16
	slliw s3, s3, 16
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srliw s6, t3, 12
	slliw t3, t3, 20
	or t3, t3, s6
	lwu t6, 160(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srliw s6, s3, 8
	slliw s3, s3, 24
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srliw s6, t3, 7
	slliw t3, t3, 25
	or t3, t3, s6
	lwu t6, 184(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srliw s6, s4, 16
	slliw s4, s4, 16
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srliw s6, t0, 12
	slliw t0, t0, 20
	or t0, t0, s6
	lwu t6, 164(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srliw s6, s4, 8
	slliw s4, s4, 24
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srliw s6, t0, 7
	slliw t0, t0, 25
	or t0, t0, s6
	lwu t6, 184(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srliw s6, s2, 16
	slliw s2, s2, 16
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srliw s6, t0, 12
	slliw t0, t0, 20
	or t0, t0, s6
	lwu t6, 152(a5)
	add a3, a3, t0
	add a3, a3, t6
	xor s2, s2, a3
	srliw s6, s2, 8
	slliw s2, s2, 24
	or s2, s2, s6
	add t4, t4, s2
	xor t0, t0, t4
	srliw s6, t0, 7
	slliw t0, t0, 25
	or t0, t0, s6
	lwu t6, 176(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srliw s6, s3, 16
	slliw s3, s3, 16
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srliw s6, t1, 12
	slliw t1, t1, 20
	or t1, t1, s6
	lwu t6, 160(a5)
	add a4, a4, t1
	add a4, a4, t6
	xor s3, s3, a4
	srliw s6, s3, 8
	slliw s3, s3, 24
	or s3, s3, s6
	add t5, t5, s3
	xor t1, t1, t5
	srliw s6, t1, 7
	slliw t1, t1, 25
	or t1, t1, s6
	lwu t6, 172(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srliw s6, s4, 16
	slliw s4, s4, 16
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srliw s6, t2, 12
	slliw t2, t2, 20
	or t2, t2, s6
	lwu t6, 168(a5)
	add a6, a6, t2
	add a6, a6, t6
	xor s4, s4, a6
	srliw s6, s4, 8
	slliw s4, s4, 24
	or s4, s4, s6
	add s0, s0, s4
	xor t2, t2, s0
	srliw s6, t2, 7
	slliw t2, t2, 25
	or t2, t2, s6
	lwu t6, 148(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srliw s6, s5, 16
	slliw s5, s5, 16
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srliw s6, t3, 12
	slliw t3, t3, 20
	or t3, t3, s6
	lwu t6, 164(a5)
	add a7, a7, t3
	add a7, a7, t6
	xor s5, s5, a7
	srliw s6, s5, 8
	slliw s5, s5, 24
	or s5, s5, s6
	add s1, s1, s5
	xor t3, t3, s1
	srliw s6, t3, 7
	slliw t3, t3, 25
	or t3, t3, s6
	lwu t6, 204(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srliw s6, s5, 16
	slliw s5, s5, 16
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srliw s6, t1, 12
	slliw t1, t1, 20
	or t1, t1, s6
	lwu t6, 188(a5)
	add a3, a3, t1
	add a3, a3, t6
	xor s5, s5, a3
	srliw s6, s5, 8
	slliw s5, s5, 24
	or s5, s5, s6
	add s0, s0, s5
	xor t1, t1, s0
	srliw s6, t1, 7
	slliw t1, t1, 25
	or t1, t1, s6
	lwu t6, 180(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srliw s6, s2, 16
	slliw s2, s2, 16
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srliw s6, t2, 12
	slliw t2, t2, 20
	or t2, t2, s6
	lwu t6, 200(a5)
	add a4, a4, t2
	add a4, a4, t6
	xor s2, s2, a4
	srliw s6, s2, 8
	slliw s2, s2, 24
	or s2, s2, s6
	add s1, s1, s2
	xor t2, t2, s1
	srliw s6, t2, 7
	slliw t2, t2, 25
	or t2, t2, s6
	lwu t6, 156(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srliw s6, s3, 16
	slliw s3, s3, 16
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srliw s6, t3, 12
	slliw t3, t3, 20
	or t3, t3, s6
	lwu t6, 192(a5)
	add a6, a6, t3
	add a6, a6, t6
	xor s3, s3, a6
	srliw s6, s3, 8
	slliw s3, s3, 24
	or s3, s3, s6
	add t4, t4, s3
	xor t3, t3, t4
	srliw s6, t3, 7
	slliw t3, t3, 25
	or t3, t3, s6
	lwu t6, 196(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srliw s6, s4, 16
	slliw s4, s4, 16
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srliw s6, t0, 12
	slliw t0, t0, 20
	or t0, t0, s6
	lwu t6, 144(a5)
	add a7, a7, t0
	add a7, a7, t6
	xor s4, s4, a7
	srliw s6, s4, 8
	slliw s4, s4, 24
	or s4, s4, s6
	add t5, t5, s4
	xor t0, t0, t5
	srliw s6, t0, 7
	slliw t0, t0, 25
	or t0, t0, s6
	lwu t6, 80(a5)
	xor t6, t6, a3
	xor t6, t6, t4
	sw t6, 80(a5)
	lwu t6, 84(a5)
	xor t6, t6, a4
	xor t6, t6, t5
	sw t6, 84(a5)
	lwu t6, 88(a5)
	xor t6, t6, a6
	xor t6, t6, s0
	sw t6, 88(a5)
	lwu t6, 92(a5)
	xor t6, t6, a7
	xor t6, t6, s1
	sw t6, 92(a5)
	lwu t6, 96(a5)
	xor t6, t6, t0
	xor t6, t6, s2
	sw t6, 96(a5)
	lwu t6, 100(a5)
	xor t6, t6, t1
	xor t6, t6, s3
	sw t6, 100(a5)
	lwu t6, 104(a5)
	xor t6, t6, t2
	xor t6, t6, s4
	sw t6, 104(a5)
	lwu t6, 108(a5)
	xor t6, t6, t3
	xor t6, t6, s5
	sw t6, 108(a5)
	addi a1, a1, 64
	ld a3, 56(a5)
	addi a3, a3, 64
	sd a3, 56(a5)
	srli a4, a3, 6
	addi a4, a4, -1
	srli a4, a4, 63
	ld a6, 64(a5)
	add a6, a6, a4
	sd a6, 64(a5)
	addi a2, a2, -1
	bnez a2, 22b
	j 21f
20:
21:
	lwu t6, 80(a5)
	sb t6, 0(a0)
	srli a3, t6, 8
	sb a3, 1(a0)
	srli a3, t6, 16
	sb a3, 2(a0)
	srli a3, t6, 24
	sb a3, 3(a0)
	lwu t6, 84(a5)
	sb t6, 4(a0)
	srli a3, t6, 8
	sb a3, 5(a0)
	srli a3, t6, 16
	sb a3, 6(a0)
	srli a3, t6, 24
	sb a3, 7(a0)
	lwu t6, 88(a5)
	sb t6, 8(a0)
	srli a3, t6, 8
	sb a3, 9(a0)
	srli a3, t6, 16
	sb a3, 10(a0)
	srli a3, t6, 24
	sb a3, 11(a0)
	lwu t6, 92(a5)
	sb t6, 12(a0)
	srli a3, t6, 8
	sb a3, 13(a0)
	srli a3, t6, 16
	sb a3, 14(a0)
	srli a3, t6, 24
	sb a3, 15(a0)
	lwu t6, 96(a5)
	sb t6, 16(a0)
	srli a3, t6, 8
	sb a3, 17(a0)
	srli a3, t6, 16
	sb a3, 18(a0)
	srli a3, t6, 24
	sb a3, 19(a0)
	lwu t6, 100(a5)
	sb t6, 20(a0)
	srli a3, t6, 8
	sb a3, 21(a0)
	srli a3, t6, 16
	sb a3, 22(a0)
	srli a3, t6, 24
	sb a3, 23(a0)
	lwu t6, 104(a5)
	sb t6, 24(a0)
	srli a3, t6, 8
	sb a3, 25(a0)
	srli a3, t6, 16
	sb a3, 26(a0)
	srli a3, t6, 24
	sb a3, 27(a0)
	lwu t6, 108(a5)
	sb t6, 28(a0)
	srli a3, t6, 8
	sb a3, 29(a0)
	srli a3, t6, 16
	sb a3, 30(a0)
	srli a3, t6, 24
	sb a3, 31(a0)
	ld s0, 0(a5)
	ld s1, 8(a5)
	ld s2, 16(a5)
	ld s3, 24(a5)
	ld s4, 32(a5)
	ld s5, 40(a5)
	ld s6, 48(a5)
	ret
	.option pop
