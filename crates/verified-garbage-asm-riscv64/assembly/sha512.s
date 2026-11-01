// The functions of `src/sha512.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha512_compress:
	.option push
	.option arch, +m, +c
	addi a3, a3, 7
	andi a3, a3, -8
	sd s0, 128(a3)
	beqz a2, 20f
22:
	lbu t0, 0(a0)
	lbu a5, 1(a0)
	slli a5, a5, 8
	or t0, t0, a5
	lbu a5, 2(a0)
	slli a5, a5, 16
	or t0, t0, a5
	lbu a5, 3(a0)
	slli a5, a5, 24
	or t0, t0, a5
	lbu a6, 4(a0)
	lbu a5, 5(a0)
	slli a5, a5, 8
	or a6, a6, a5
	lbu a5, 6(a0)
	slli a5, a5, 16
	or a6, a6, a5
	lbu a5, 7(a0)
	slli a5, a5, 24
	or a6, a6, a5
	slli a6, a6, 32
	or t0, t0, a6
	lbu t1, 8(a0)
	lbu a5, 9(a0)
	slli a5, a5, 8
	or t1, t1, a5
	lbu a5, 10(a0)
	slli a5, a5, 16
	or t1, t1, a5
	lbu a5, 11(a0)
	slli a5, a5, 24
	or t1, t1, a5
	lbu a6, 12(a0)
	lbu a5, 13(a0)
	slli a5, a5, 8
	or a6, a6, a5
	lbu a5, 14(a0)
	slli a5, a5, 16
	or a6, a6, a5
	lbu a5, 15(a0)
	slli a5, a5, 24
	or a6, a6, a5
	slli a6, a6, 32
	or t1, t1, a6
	lbu t2, 16(a0)
	lbu a5, 17(a0)
	slli a5, a5, 8
	or t2, t2, a5
	lbu a5, 18(a0)
	slli a5, a5, 16
	or t2, t2, a5
	lbu a5, 19(a0)
	slli a5, a5, 24
	or t2, t2, a5
	lbu a6, 20(a0)
	lbu a5, 21(a0)
	slli a5, a5, 8
	or a6, a6, a5
	lbu a5, 22(a0)
	slli a5, a5, 16
	or a6, a6, a5
	lbu a5, 23(a0)
	slli a5, a5, 24
	or a6, a6, a5
	slli a6, a6, 32
	or t2, t2, a6
	lbu t3, 24(a0)
	lbu a5, 25(a0)
	slli a5, a5, 8
	or t3, t3, a5
	lbu a5, 26(a0)
	slli a5, a5, 16
	or t3, t3, a5
	lbu a5, 27(a0)
	slli a5, a5, 24
	or t3, t3, a5
	lbu a6, 28(a0)
	lbu a5, 29(a0)
	slli a5, a5, 8
	or a6, a6, a5
	lbu a5, 30(a0)
	slli a5, a5, 16
	or a6, a6, a5
	lbu a5, 31(a0)
	slli a5, a5, 24
	or a6, a6, a5
	slli a6, a6, 32
	or t3, t3, a6
	lbu t4, 32(a0)
	lbu a5, 33(a0)
	slli a5, a5, 8
	or t4, t4, a5
	lbu a5, 34(a0)
	slli a5, a5, 16
	or t4, t4, a5
	lbu a5, 35(a0)
	slli a5, a5, 24
	or t4, t4, a5
	lbu a6, 36(a0)
	lbu a5, 37(a0)
	slli a5, a5, 8
	or a6, a6, a5
	lbu a5, 38(a0)
	slli a5, a5, 16
	or a6, a6, a5
	lbu a5, 39(a0)
	slli a5, a5, 24
	or a6, a6, a5
	slli a6, a6, 32
	or t4, t4, a6
	lbu t5, 40(a0)
	lbu a5, 41(a0)
	slli a5, a5, 8
	or t5, t5, a5
	lbu a5, 42(a0)
	slli a5, a5, 16
	or t5, t5, a5
	lbu a5, 43(a0)
	slli a5, a5, 24
	or t5, t5, a5
	lbu a6, 44(a0)
	lbu a5, 45(a0)
	slli a5, a5, 8
	or a6, a6, a5
	lbu a5, 46(a0)
	slli a5, a5, 16
	or a6, a6, a5
	lbu a5, 47(a0)
	slli a5, a5, 24
	or a6, a6, a5
	slli a6, a6, 32
	or t5, t5, a6
	lbu t6, 48(a0)
	lbu a5, 49(a0)
	slli a5, a5, 8
	or t6, t6, a5
	lbu a5, 50(a0)
	slli a5, a5, 16
	or t6, t6, a5
	lbu a5, 51(a0)
	slli a5, a5, 24
	or t6, t6, a5
	lbu a6, 52(a0)
	lbu a5, 53(a0)
	slli a5, a5, 8
	or a6, a6, a5
	lbu a5, 54(a0)
	slli a5, a5, 16
	or a6, a6, a5
	lbu a5, 55(a0)
	slli a5, a5, 24
	or a6, a6, a5
	slli a6, a6, 32
	or t6, t6, a6
	lbu a4, 56(a0)
	lbu a5, 57(a0)
	slli a5, a5, 8
	or a4, a4, a5
	lbu a5, 58(a0)
	slli a5, a5, 16
	or a4, a4, a5
	lbu a5, 59(a0)
	slli a5, a5, 24
	or a4, a4, a5
	lbu a6, 60(a0)
	lbu a5, 61(a0)
	slli a5, a5, 8
	or a6, a6, a5
	lbu a5, 62(a0)
	slli a5, a5, 16
	or a6, a6, a5
	lbu a5, 63(a0)
	slli a5, a5, 24
	or a6, a6, a5
	slli a6, a6, 32
	or a4, a4, a6
	lbu a5, 0(a1)
	slli a5, a5, 8
	lbu a6, 1(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 2(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 3(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 4(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 5(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 6(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 7(a1)
	or a5, a5, a6
	sd a5, 0(a3)
	srli a6, t4, 14
	slli a7, t4, 50
	xor a6, a6, a7
	srli a7, t4, 18
	xor a6, a6, a7
	slli a7, t4, 46
	xor a6, a6, a7
	srli a7, t4, 41
	xor a6, a6, a7
	slli a7, t4, 23
	xor a6, a6, a7
	add a4, a4, a6
	xor a6, t5, t6
	and a6, a6, t4
	xor a6, a6, t6
	add a4, a4, a6
	lui a6, 272547
	addiw a6, a6, -103
	slli a6, a6, 32
	lui a7, 881291
	addiw a7, a7, -478
	add a6, a6, a7
	add a4, a4, a6
	add a4, a4, a5
	add t3, t3, a4
	srli a6, t0, 28
	slli a7, t0, 36
	xor a6, a6, a7
	srli a7, t0, 34
	xor a6, a6, a7
	slli a7, t0, 30
	xor a6, a6, a7
	srli a7, t0, 39
	xor a6, a6, a7
	slli a7, t0, 25
	xor a6, a6, a7
	add a4, a4, a6
	or a6, t0, t1
	and a6, a6, t2
	and a7, t0, t1
	or a6, a6, a7
	add a4, a4, a6
	lbu a5, 8(a1)
	slli a5, a5, 8
	lbu a6, 9(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 10(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 11(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 12(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 13(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 14(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 15(a1)
	or a5, a5, a6
	sd a5, 8(a3)
	srli a6, t3, 14
	slli a7, t3, 50
	xor a6, a6, a7
	srli a7, t3, 18
	xor a6, a6, a7
	slli a7, t3, 46
	xor a6, a6, a7
	srli a7, t3, 41
	xor a6, a6, a7
	slli a7, t3, 23
	xor a6, a6, a7
	add t6, t6, a6
	xor a6, t4, t5
	and a6, a6, t3
	xor a6, a6, t5
	add t6, t6, a6
	lui a6, 463732
	addiw a6, a6, 1169
	slli a6, a6, 32
	lui a7, 147190
	addiw a7, a7, 1485
	add a6, a6, a7
	add t6, t6, a6
	add t6, t6, a5
	add t2, t2, t6
	srli a6, a4, 28
	slli a7, a4, 36
	xor a6, a6, a7
	srli a7, a4, 34
	xor a6, a6, a7
	slli a7, a4, 30
	xor a6, a6, a7
	srli a7, a4, 39
	xor a6, a6, a7
	slli a7, a4, 25
	xor a6, a6, a7
	add t6, t6, a6
	or a6, a4, t0
	and a6, a6, t1
	and a7, a4, t0
	or a6, a6, a7
	add t6, t6, a6
	lbu a5, 16(a1)
	slli a5, a5, 8
	lbu a6, 17(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 18(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 19(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 20(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 21(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 22(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 23(a1)
	or a5, a5, a6
	sd a5, 16(a3)
	srli a6, t2, 14
	slli a7, t2, 50
	xor a6, a6, a7
	srli a7, t2, 18
	xor a6, a6, a7
	slli a7, t2, 46
	xor a6, a6, a7
	srli a7, t2, 41
	xor a6, a6, a7
	slli a7, t2, 23
	xor a6, a6, a7
	add t5, t5, a6
	xor a6, t3, t4
	and a6, a6, t2
	xor a6, a6, t4
	add t5, t5, a6
	lui a6, 744464
	addiw a6, a6, -1072
	slli a6, a6, 32
	lui a7, 967892
	addiw a7, a7, -1233
	add a6, a6, a7
	add t5, t5, a6
	add t5, t5, a5
	add t1, t1, t5
	srli a6, t6, 28
	slli a7, t6, 36
	xor a6, a6, a7
	srli a7, t6, 34
	xor a6, a6, a7
	slli a7, t6, 30
	xor a6, a6, a7
	srli a7, t6, 39
	xor a6, a6, a7
	slli a7, t6, 25
	xor a6, a6, a7
	add t5, t5, a6
	or a6, t6, a4
	and a6, a6, t0
	and a7, t6, a4
	or a6, a6, a7
	add t5, t5, a6
	lbu a5, 24(a1)
	slli a5, a5, 8
	lbu a6, 25(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 26(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 27(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 28(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 29(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 30(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 31(a1)
	or a5, a5, a6
	sd a5, 24(a3)
	srli a6, t1, 14
	slli a7, t1, 50
	xor a6, a6, a7
	srli a7, t1, 18
	xor a6, a6, a7
	slli a7, t1, 46
	xor a6, a6, a7
	srli a7, t1, 41
	xor a6, a6, a7
	slli a7, t1, 23
	xor a6, a6, a7
	add t4, t4, a6
	xor a6, t2, t3
	and a6, a6, t1
	xor a6, a6, t3
	add t4, t4, a6
	lui a6, 957278
	addiw a6, a6, -1114
	slli a6, a6, 32
	lui a7, 530590
	addiw a7, a7, -1092
	add a6, a6, a7
	add t4, t4, a6
	add t4, t4, a5
	add t0, t0, t4
	srli a6, t5, 28
	slli a7, t5, 36
	xor a6, a6, a7
	srli a7, t5, 34
	xor a6, a6, a7
	slli a7, t5, 30
	xor a6, a6, a7
	srli a7, t5, 39
	xor a6, a6, a7
	slli a7, t5, 25
	xor a6, a6, a7
	add t4, t4, a6
	or a6, t5, t6
	and a6, a6, a4
	and a7, t5, t6
	or a6, a6, a7
	add t4, t4, a6
	lbu a5, 32(a1)
	slli a5, a5, 8
	lbu a6, 33(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 34(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 35(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 36(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 37(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 38(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 39(a1)
	or a5, a5, a6
	sd a5, 32(a3)
	srli a6, t0, 14
	slli a7, t0, 50
	xor a6, a6, a7
	srli a7, t0, 18
	xor a6, a6, a7
	slli a7, t0, 46
	xor a6, a6, a7
	srli a7, t0, 41
	xor a6, a6, a7
	slli a7, t0, 23
	xor a6, a6, a7
	add t3, t3, a6
	xor a6, t1, t2
	and a6, a6, t0
	xor a6, a6, t2
	add t3, t3, a6
	lui a6, 234860
	addiw a6, a6, 604
	slli a6, a6, 32
	lui a7, 996491
	addiw a7, a7, 1336
	add a6, a6, a7
	add t3, t3, a6
	add t3, t3, a5
	add a4, a4, t3
	srli a6, t4, 28
	slli a7, t4, 36
	xor a6, a6, a7
	srli a7, t4, 34
	xor a6, a6, a7
	slli a7, t4, 30
	xor a6, a6, a7
	srli a7, t4, 39
	xor a6, a6, a7
	slli a7, t4, 25
	xor a6, a6, a7
	add t3, t3, a6
	or a6, t4, t5
	and a6, a6, t6
	and a7, t4, t5
	or a6, a6, a7
	add t3, t3, a6
	lbu a5, 40(a1)
	slli a5, a5, 8
	lbu a6, 41(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 42(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 43(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 44(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 45(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 46(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 47(a1)
	or a5, a5, a6
	sd a5, 40(a3)
	srli a6, a4, 14
	slli a7, a4, 50
	xor a6, a6, a7
	srli a7, a4, 18
	xor a6, a6, a7
	slli a7, a4, 46
	xor a6, a6, a7
	srli a7, a4, 41
	xor a6, a6, a7
	slli a7, a4, 23
	xor a6, a6, a7
	add t2, t2, a6
	xor a6, t0, t1
	and a6, a6, a4
	xor a6, a6, t1
	add t2, t2, a6
	lui a6, 368401
	addiw a6, a6, 498
	slli a6, a6, 32
	lui a7, 745565
	addiw a7, a7, 25
	add a6, a6, a7
	add t2, t2, a6
	add t2, t2, a5
	add t6, t6, t2
	srli a6, t3, 28
	slli a7, t3, 36
	xor a6, a6, a7
	srli a7, t3, 34
	xor a6, a6, a7
	slli a7, t3, 30
	xor a6, a6, a7
	srli a7, t3, 39
	xor a6, a6, a7
	slli a7, t3, 25
	xor a6, a6, a7
	add t2, t2, a6
	or a6, t3, t4
	and a6, a6, t5
	and a7, t3, t4
	or a6, a6, a7
	add t2, t2, a6
	lbu a5, 48(a1)
	slli a5, a5, 8
	lbu a6, 49(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 50(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 51(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 52(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 53(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 54(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 55(a1)
	or a5, a5, a6
	sd a5, 48(a3)
	srli a6, t6, 14
	slli a7, t6, 50
	xor a6, a6, a7
	srli a7, t6, 18
	xor a6, a6, a7
	slli a7, t6, 46
	xor a6, a6, a7
	srli a7, t6, 41
	xor a6, a6, a7
	slli a7, t6, 23
	xor a6, a6, a7
	add t1, t1, a6
	xor a6, a4, t0
	and a6, a6, t6
	xor a6, a6, t0
	add t1, t1, a6
	lui a6, 599032
	addiw a6, a6, 677
	slli a6, a6, 32
	lui a7, 717205
	addiw a7, a7, -101
	add a6, a6, a7
	add t1, t1, a6
	add t1, t1, a5
	add t5, t5, t1
	srli a6, t2, 28
	slli a7, t2, 36
	xor a6, a6, a7
	srli a7, t2, 34
	xor a6, a6, a7
	slli a7, t2, 30
	xor a6, a6, a7
	srli a7, t2, 39
	xor a6, a6, a7
	slli a7, t2, 25
	xor a6, a6, a7
	add t1, t1, a6
	or a6, t2, t3
	and a6, a6, t4
	and a7, t2, t3
	or a6, a6, a7
	add t1, t1, a6
	lbu a5, 56(a1)
	slli a5, a5, 8
	lbu a6, 57(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 58(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 59(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 60(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 61(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 62(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 63(a1)
	or a5, a5, a6
	sd a5, 56(a3)
	srli a6, t5, 14
	slli a7, t5, 50
	xor a6, a6, a7
	srli a7, t5, 18
	xor a6, a6, a7
	slli a7, t5, 46
	xor a6, a6, a7
	srli a7, t5, 41
	xor a6, a6, a7
	slli a7, t5, 23
	xor a6, a6, a7
	add t0, t0, a6
	xor a6, t6, a4
	and a6, a6, t5
	xor a6, a6, a4
	add t0, t0, a6
	lui a6, 700870
	addiw a6, a6, -298
	slli a6, a6, 32
	lui a7, 894680
	addiw a7, a7, 280
	add a6, a6, a7
	add t0, t0, a6
	add t0, t0, a5
	add t4, t4, t0
	srli a6, t1, 28
	slli a7, t1, 36
	xor a6, a6, a7
	srli a7, t1, 34
	xor a6, a6, a7
	slli a7, t1, 30
	xor a6, a6, a7
	srli a7, t1, 39
	xor a6, a6, a7
	slli a7, t1, 25
	xor a6, a6, a7
	add t0, t0, a6
	or a6, t1, t2
	and a6, a6, t3
	and a7, t1, t2
	or a6, a6, a7
	add t0, t0, a6
	lbu a5, 64(a1)
	slli a5, a5, 8
	lbu a6, 65(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 66(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 67(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 68(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 69(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 70(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 71(a1)
	or a5, a5, a6
	sd a5, 64(a3)
	srli a6, t4, 14
	slli a7, t4, 50
	xor a6, a6, a7
	srli a7, t4, 18
	xor a6, a6, a7
	slli a7, t4, 46
	xor a6, a6, a7
	srli a7, t4, 41
	xor a6, a6, a7
	slli a7, t4, 23
	xor a6, a6, a7
	add a4, a4, a6
	xor a6, t5, t6
	and a6, a6, t4
	xor a6, a6, t6
	add a4, a4, a6
	lui a6, 884859
	addiw a6, a6, -1383
	slli a6, a6, 32
	lui a7, 667696
	addiw a7, a7, 578
	add a6, a6, a7
	add a4, a4, a6
	add a4, a4, a5
	add t3, t3, a4
	srli a6, t0, 28
	slli a7, t0, 36
	xor a6, a6, a7
	srli a7, t0, 34
	xor a6, a6, a7
	slli a7, t0, 30
	xor a6, a6, a7
	srli a7, t0, 39
	xor a6, a6, a7
	slli a7, t0, 25
	xor a6, a6, a7
	add a4, a4, a6
	or a6, t0, t1
	and a6, a6, t2
	and a7, t0, t1
	or a6, a6, a7
	add a4, a4, a6
	lbu a5, 72(a1)
	slli a5, a5, 8
	lbu a6, 73(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 74(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 75(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 76(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 77(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 78(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 79(a1)
	or a5, a5, a6
	sd a5, 72(a3)
	srli a6, t3, 14
	slli a7, t3, 50
	xor a6, a6, a7
	srli a7, t3, 18
	xor a6, a6, a7
	slli a7, t3, 46
	xor a6, a6, a7
	srli a7, t3, 41
	xor a6, a6, a7
	slli a7, t3, 23
	xor a6, a6, a7
	add t6, t6, a6
	xor a6, t4, t5
	and a6, a6, t3
	xor a6, a6, t5
	add t6, t6, a6
	lui a6, 75830
	addiw a6, a6, -1279
	slli a6, a6, 32
	lui a7, 284423
	addiw a7, a7, -66
	add a6, a6, a7
	add t6, t6, a6
	add t6, t6, a5
	add t2, t2, t6
	srli a6, a4, 28
	slli a7, a4, 36
	xor a6, a6, a7
	srli a7, a4, 34
	xor a6, a6, a7
	slli a7, a4, 30
	xor a6, a6, a7
	srli a7, a4, 39
	xor a6, a6, a7
	slli a7, a4, 25
	xor a6, a6, a7
	add t6, t6, a6
	or a6, a4, t0
	and a6, a6, t1
	and a7, a4, t0
	or a6, a6, a7
	add t6, t6, a6
	lbu a5, 80(a1)
	slli a5, a5, 8
	lbu a6, 81(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 82(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 83(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 84(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 85(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 86(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 87(a1)
	or a5, a5, a6
	sd a5, 80(a3)
	srli a6, t2, 14
	slli a7, t2, 50
	xor a6, a6, a7
	srli a7, t2, 18
	xor a6, a6, a7
	slli a7, t2, 46
	xor a6, a6, a7
	srli a7, t2, 41
	xor a6, a6, a7
	slli a7, t2, 23
	xor a6, a6, a7
	add t5, t5, a6
	xor a6, t3, t4
	and a6, a6, t2
	xor a6, a6, t4
	add t5, t5, a6
	lui a6, 148248
	addiw a6, a6, 1470
	slli a6, a6, 32
	lui a7, 323147
	addiw a7, a7, 652
	add a6, a6, a7
	add t5, t5, a6
	add t5, t5, a5
	add t1, t1, t5
	srli a6, t6, 28
	slli a7, t6, 36
	xor a6, a6, a7
	srli a7, t6, 34
	xor a6, a6, a7
	slli a7, t6, 30
	xor a6, a6, a7
	srli a7, t6, 39
	xor a6, a6, a7
	slli a7, t6, 25
	xor a6, a6, a7
	add t5, t5, a6
	or a6, t6, a4
	and a6, a6, t0
	and a7, t6, a4
	or a6, a6, a7
	add t5, t5, a6
	lbu a5, 88(a1)
	slli a5, a5, 8
	lbu a6, 89(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 90(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 91(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 92(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 93(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 94(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 95(a1)
	or a5, a5, a6
	sd a5, 88(a3)
	srli a6, t1, 14
	slli a7, t1, 50
	xor a6, a6, a7
	srli a7, t1, 18
	xor a6, a6, a7
	slli a7, t1, 46
	xor a6, a6, a7
	srli a7, t1, 41
	xor a6, a6, a7
	slli a7, t1, 23
	xor a6, a6, a7
	add t4, t4, a6
	xor a6, t2, t3
	and a6, a6, t1
	xor a6, a6, t3
	add t4, t4, a6
	lui a6, 348360
	addiw a6, a6, -572
	slli a6, a6, 32
	lui a7, 876539
	addiw a7, a7, 1250
	add a6, a6, a7
	add t4, t4, a6
	add t4, t4, a5
	add t0, t0, t4
	srli a6, t5, 28
	slli a7, t5, 36
	xor a6, a6, a7
	srli a7, t5, 34
	xor a6, a6, a7
	slli a7, t5, 30
	xor a6, a6, a7
	srli a7, t5, 39
	xor a6, a6, a7
	slli a7, t5, 25
	xor a6, a6, a7
	add t4, t4, a6
	or a6, t5, t6
	and a6, a6, a4
	and a7, t5, t6
	or a6, a6, a7
	add t4, t4, a6
	lbu a5, 96(a1)
	slli a5, a5, 8
	lbu a6, 97(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 98(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 99(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 100(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 101(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 102(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 103(a1)
	or a5, a5, a6
	sd a5, 96(a3)
	srli a6, t0, 14
	slli a7, t0, 50
	xor a6, a6, a7
	srli a7, t0, 18
	xor a6, a6, a7
	slli a7, t0, 46
	xor a6, a6, a7
	srli a7, t0, 41
	xor a6, a6, a7
	slli a7, t0, 23
	xor a6, a6, a7
	add t3, t3, a6
	xor a6, t1, t2
	and a6, a6, t0
	xor a6, a6, t2
	add t3, t3, a6
	lui a6, 469990
	addiw a6, a6, -651
	slli a6, a6, 32
	lui a7, 993209
	addiw a7, a7, -1681
	add a6, a6, a7
	add t3, t3, a6
	add t3, t3, a5
	add a4, a4, t3
	srli a6, t4, 28
	slli a7, t4, 36
	xor a6, a6, a7
	srli a7, t4, 34
	xor a6, a6, a7
	slli a7, t4, 30
	xor a6, a6, a7
	srli a7, t4, 39
	xor a6, a6, a7
	slli a7, t4, 25
	xor a6, a6, a7
	add t3, t3, a6
	or a6, t4, t5
	and a6, a6, t6
	and a7, t4, t5
	or a6, a6, a7
	add t3, t3, a6
	lbu a5, 104(a1)
	slli a5, a5, 8
	lbu a6, 105(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 106(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 107(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 108(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 109(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 110(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 111(a1)
	or a5, a5, a6
	sd a5, 104(a3)
	srli a6, a4, 14
	slli a7, a4, 50
	xor a6, a6, a7
	srli a7, a4, 18
	xor a6, a6, a7
	slli a7, a4, 46
	xor a6, a6, a7
	srli a7, a4, 41
	xor a6, a6, a7
	slli a7, a4, 23
	xor a6, a6, a7
	add t2, t2, a6
	xor a6, t0, t1
	and a6, a6, a4
	xor a6, a6, t1
	add t2, t2, a6
	lui a6, 527851
	addiw a6, a6, 510
	slli a6, a6, 32
	lui a7, 242025
	addiw a7, a7, 1713
	add a6, a6, a7
	add t2, t2, a6
	add t2, t2, a5
	add t6, t6, t2
	srli a6, t3, 28
	slli a7, t3, 36
	xor a6, a6, a7
	srli a7, t3, 34
	xor a6, a6, a7
	slli a7, t3, 30
	xor a6, a6, a7
	srli a7, t3, 39
	xor a6, a6, a7
	slli a7, t3, 25
	xor a6, a6, a7
	add t2, t2, a6
	or a6, t3, t4
	and a6, a6, t5
	and a7, t3, t4
	or a6, a6, a7
	add t2, t2, a6
	lbu a5, 112(a1)
	slli a5, a5, 8
	lbu a6, 113(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 114(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 115(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 116(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 117(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 118(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 119(a1)
	or a5, a5, a6
	sd a5, 112(a3)
	srli a6, t6, 14
	slli a7, t6, 50
	xor a6, a6, a7
	srli a7, t6, 18
	xor a6, a6, a7
	slli a7, t6, 46
	xor a6, a6, a7
	srli a7, t6, 41
	xor a6, a6, a7
	slli a7, t6, 23
	xor a6, a6, a7
	add t1, t1, a6
	xor a6, a4, t0
	and a6, a6, t6
	xor a6, a6, t0
	add t1, t1, a6
	lui a6, 638400
	addiw a6, a6, 1703
	slli a6, a6, 32
	lui a7, 154737
	addiw a7, a7, 565
	add a6, a6, a7
	add t1, t1, a6
	add t1, t1, a5
	add t5, t5, t1
	srli a6, t2, 28
	slli a7, t2, 36
	xor a6, a6, a7
	srli a7, t2, 34
	xor a6, a6, a7
	slli a7, t2, 30
	xor a6, a6, a7
	srli a7, t2, 39
	xor a6, a6, a7
	slli a7, t2, 25
	xor a6, a6, a7
	add t1, t1, a6
	or a6, t2, t3
	and a6, a6, t4
	and a7, t2, t3
	or a6, a6, a7
	add t1, t1, a6
	lbu a5, 120(a1)
	slli a5, a5, 8
	lbu a6, 121(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 122(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 123(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 124(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 125(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 126(a1)
	or a5, a5, a6
	slli a5, a5, 8
	lbu a6, 127(a1)
	or a5, a5, a6
	sd a5, 120(a3)
	srli a6, t5, 14
	slli a7, t5, 50
	xor a6, a6, a7
	srli a7, t5, 18
	xor a6, a6, a7
	slli a7, t5, 46
	xor a6, a6, a7
	srli a7, t5, 41
	xor a6, a6, a7
	slli a7, t5, 23
	xor a6, a6, a7
	add t0, t0, a6
	xor a6, t6, a4
	and a6, a6, t5
	xor a6, a6, a4
	add t0, t0, a6
	lui a6, 793023
	addiw a6, a6, 373
	slli a6, a6, 32
	lui a7, 849554
	addiw a7, a7, 1684
	add a6, a6, a7
	add t0, t0, a6
	add t0, t0, a5
	add t4, t4, t0
	srli a6, t1, 28
	slli a7, t1, 36
	xor a6, a6, a7
	srli a7, t1, 34
	xor a6, a6, a7
	slli a7, t1, 30
	xor a6, a6, a7
	srli a7, t1, 39
	xor a6, a6, a7
	slli a7, t1, 25
	xor a6, a6, a7
	add t0, t0, a6
	or a6, t1, t2
	and a6, a6, t3
	and a7, t1, t2
	or a6, a6, a7
	add t0, t0, a6
	ld a6, 112(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 72(a3)
	add a5, a5, a7
	ld a6, 8(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 0(a3)
	add a5, a5, a7
	sd a5, 0(a3)
	srli a6, t4, 14
	slli a7, t4, 50
	xor a6, a6, a7
	srli a7, t4, 18
	xor a6, a6, a7
	slli a7, t4, 46
	xor a6, a6, a7
	srli a7, t4, 41
	xor a6, a6, a7
	slli a7, t4, 23
	xor a6, a6, a7
	add a4, a4, a6
	xor a6, t5, t6
	and a6, a6, t4
	xor a6, a6, t6
	add a4, a4, a6
	lui a6, 936375
	addiw a6, a6, -1598
	slli a6, a6, 32
	lui a7, 651029
	addiw a7, a7, -1326
	add a6, a6, a7
	add a4, a4, a6
	add a4, a4, a5
	add t3, t3, a4
	srli a6, t0, 28
	slli a7, t0, 36
	xor a6, a6, a7
	srli a7, t0, 34
	xor a6, a6, a7
	slli a7, t0, 30
	xor a6, a6, a7
	srli a7, t0, 39
	xor a6, a6, a7
	slli a7, t0, 25
	xor a6, a6, a7
	add a4, a4, a6
	or a6, t0, t1
	and a6, a6, t2
	and a7, t0, t1
	or a6, a6, a7
	add a4, a4, a6
	ld a6, 120(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 80(a3)
	add a5, a5, a7
	ld a6, 16(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 8(a3)
	add a5, a5, a7
	sd a5, 8(a3)
	srli a6, t3, 14
	slli a7, t3, 50
	xor a6, a6, a7
	srli a7, t3, 18
	xor a6, a6, a7
	slli a7, t3, 46
	xor a6, a6, a7
	srli a7, t3, 41
	xor a6, a6, a7
	slli a7, t3, 23
	xor a6, a6, a7
	add t6, t6, a6
	xor a6, t4, t5
	and a6, a6, t3
	xor a6, a6, t5
	add t6, t6, a6
	lui a6, 981988
	addiw a6, a6, 1926
	slli a6, a6, 32
	lui a7, 230642
	addiw a7, a7, 1507
	add a6, a6, a7
	add t6, t6, a6
	add t6, t6, a5
	add t2, t2, t6
	srli a6, a4, 28
	slli a7, a4, 36
	xor a6, a6, a7
	srli a7, a4, 34
	xor a6, a6, a7
	slli a7, a4, 30
	xor a6, a6, a7
	srli a7, a4, 39
	xor a6, a6, a7
	slli a7, a4, 25
	xor a6, a6, a7
	add t6, t6, a6
	or a6, a4, t0
	and a6, a6, t1
	and a7, a4, t0
	or a6, a6, a7
	add t6, t6, a6
	ld a6, 0(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 88(a3)
	add a5, a5, a7
	ld a6, 24(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 16(a3)
	add a5, a5, a7
	sd a5, 16(a3)
	srli a6, t2, 14
	slli a7, t2, 50
	xor a6, a6, a7
	srli a7, t2, 18
	xor a6, a6, a7
	slli a7, t2, 46
	xor a6, a6, a7
	srli a7, t2, 41
	xor a6, a6, a7
	slli a7, t2, 23
	xor a6, a6, a7
	add t5, t5, a6
	xor a6, t3, t4
	and a6, a6, t2
	xor a6, a6, t4
	add t5, t5, a6
	lui a6, 64538
	addiw a6, a6, -569
	slli a6, a6, 32
	lui a7, 571597
	addiw a7, a7, 1461
	add a6, a6, a7
	add t5, t5, a6
	add t5, t5, a5
	add t1, t1, t5
	srli a6, t6, 28
	slli a7, t6, 36
	xor a6, a6, a7
	srli a7, t6, 34
	xor a6, a6, a7
	slli a7, t6, 30
	xor a6, a6, a7
	srli a7, t6, 39
	xor a6, a6, a7
	slli a7, t6, 25
	xor a6, a6, a7
	add t5, t5, a6
	or a6, t6, a4
	and a6, a6, t0
	and a7, t6, a4
	or a6, a6, a7
	add t5, t5, a6
	ld a6, 8(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 96(a3)
	add a5, a5, a7
	ld a6, 32(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 24(a3)
	add a5, a5, a7
	sd a5, 24(a3)
	srli a6, t1, 14
	slli a7, t1, 50
	xor a6, a6, a7
	srli a7, t1, 18
	xor a6, a6, a7
	slli a7, t1, 46
	xor a6, a6, a7
	srli a7, t1, 41
	xor a6, a6, a7
	slli a7, t1, 23
	xor a6, a6, a7
	add t4, t4, a6
	xor a6, t2, t3
	and a6, a6, t1
	xor a6, a6, t3
	add t4, t4, a6
	lui a6, 147658
	addiw a6, a6, 460
	slli a6, a6, 32
	lui a7, 490186
	addiw a7, a7, -923
	add a6, a6, a7
	add t4, t4, a6
	add t4, t4, a5
	add t0, t0, t4
	srli a6, t5, 28
	slli a7, t5, 36
	xor a6, a6, a7
	srli a7, t5, 34
	xor a6, a6, a7
	slli a7, t5, 30
	xor a6, a6, a7
	srli a7, t5, 39
	xor a6, a6, a7
	slli a7, t5, 25
	xor a6, a6, a7
	add t4, t4, a6
	or a6, t5, t6
	and a6, a6, a4
	and a7, t5, t6
	or a6, a6, a7
	add t4, t4, a6
	ld a6, 16(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 104(a3)
	add a5, a5, a7
	ld a6, 40(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 32(a3)
	add a5, a5, a7
	sd a5, 32(a3)
	srli a6, t0, 14
	slli a7, t0, 50
	xor a6, a6, a7
	srli a7, t0, 18
	xor a6, a6, a7
	slli a7, t0, 46
	xor a6, a6, a7
	srli a7, t0, 41
	xor a6, a6, a7
	slli a7, t0, 23
	xor a6, a6, a7
	add t3, t3, a6
	xor a6, t1, t2
	and a6, a6, t0
	xor a6, a6, t2
	add t3, t3, a6
	lui a6, 188051
	addiw a6, a6, -913
	slli a6, a6, 32
	lui a7, 365232
	addiw a7, a7, 629
	add a6, a6, a7
	add t3, t3, a6
	add t3, t3, a5
	add a4, a4, t3
	srli a6, t4, 28
	slli a7, t4, 36
	xor a6, a6, a7
	srli a7, t4, 34
	xor a6, a6, a7
	slli a7, t4, 30
	xor a6, a6, a7
	srli a7, t4, 39
	xor a6, a6, a7
	slli a7, t4, 25
	xor a6, a6, a7
	add t3, t3, a6
	or a6, t4, t5
	and a6, a6, t6
	and a7, t4, t5
	or a6, a6, a7
	add t3, t3, a6
	ld a6, 24(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 112(a3)
	add a5, a5, a7
	ld a6, 48(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 40(a3)
	add a5, a5, a7
	sd a5, 40(a3)
	srli a6, a4, 14
	slli a7, a4, 50
	xor a6, a6, a7
	srli a7, a4, 18
	xor a6, a6, a7
	slli a7, a4, 46
	xor a6, a6, a7
	srli a7, a4, 41
	xor a6, a6, a7
	slli a7, a4, 23
	xor a6, a6, a7
	add t2, t2, a6
	xor a6, t0, t1
	and a6, a6, a4
	xor a6, a6, t1
	add t2, t2, a6
	lui a6, 304968
	addiw a6, a6, 1194
	slli a6, a6, 32
	lui a7, 453230
	addiw a7, a7, 1155
	add a6, a6, a7
	add t2, t2, a6
	add t2, t2, a5
	add t6, t6, t2
	srli a6, t3, 28
	slli a7, t3, 36
	xor a6, a6, a7
	srli a7, t3, 34
	xor a6, a6, a7
	slli a7, t3, 30
	xor a6, a6, a7
	srli a7, t3, 39
	xor a6, a6, a7
	slli a7, t3, 25
	xor a6, a6, a7
	add t2, t2, a6
	or a6, t3, t4
	and a6, a6, t5
	and a7, t3, t4
	or a6, a6, a7
	add t2, t2, a6
	ld a6, 32(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 120(a3)
	add a5, a5, a7
	ld a6, 56(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 48(a3)
	add a5, a5, a7
	sd a5, 48(a3)
	srli a6, t6, 14
	slli a7, t6, 50
	xor a6, a6, a7
	srli a7, t6, 18
	xor a6, a6, a7
	slli a7, t6, 46
	xor a6, a6, a7
	srli a7, t6, 41
	xor a6, a6, a7
	slli a7, t6, 23
	xor a6, a6, a7
	add t1, t1, a6
	xor a6, a4, t0
	and a6, a6, t6
	xor a6, a6, t0
	add t1, t1, a6
	lui a6, 379659
	addiw a6, a6, -1571
	slli a6, a6, 32
	lui a7, 775200
	addiw a7, a7, -1068
	add a6, a6, a7
	add t1, t1, a6
	add t1, t1, a5
	add t5, t5, t1
	srli a6, t2, 28
	slli a7, t2, 36
	xor a6, a6, a7
	srli a7, t2, 34
	xor a6, a6, a7
	slli a7, t2, 30
	xor a6, a6, a7
	srli a7, t2, 39
	xor a6, a6, a7
	slli a7, t2, 25
	xor a6, a6, a7
	add t1, t1, a6
	or a6, t2, t3
	and a6, a6, t4
	and a7, t2, t3
	or a6, a6, a7
	add t1, t1, a6
	ld a6, 40(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 0(a3)
	add a5, a5, a7
	ld a6, 64(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 56(a3)
	add a5, a5, a7
	sd a5, 56(a3)
	srli a6, t5, 14
	slli a7, t5, 50
	xor a6, a6, a7
	srli a7, t5, 18
	xor a6, a6, a7
	slli a7, t5, 46
	xor a6, a6, a7
	srli a7, t5, 41
	xor a6, a6, a7
	slli a7, t5, 23
	xor a6, a6, a7
	add t0, t0, a6
	xor a6, t6, a4
	and a6, a6, t5
	xor a6, a6, a4
	add t0, t0, a6
	lui a6, 487321
	addiw a6, a6, -1829
	slli a6, a6, 32
	lui a7, 536853
	addiw a7, a7, 949
	add a6, a6, a7
	add t0, t0, a6
	add t0, t0, a5
	add t4, t4, t0
	srli a6, t1, 28
	slli a7, t1, 36
	xor a6, a6, a7
	srli a7, t1, 34
	xor a6, a6, a7
	slli a7, t1, 30
	xor a6, a6, a7
	srli a7, t1, 39
	xor a6, a6, a7
	slli a7, t1, 25
	xor a6, a6, a7
	add t0, t0, a6
	or a6, t1, t2
	and a6, a6, t3
	and a7, t1, t2
	or a6, a6, a7
	add t0, t0, a6
	ld a6, 48(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 8(a3)
	add a5, a5, a7
	ld a6, 72(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 64(a3)
	add a5, a5, a7
	sd a5, 64(a3)
	srli a6, t4, 14
	slli a7, t4, 50
	xor a6, a6, a7
	srli a7, t4, 18
	xor a6, a6, a7
	slli a7, t4, 46
	xor a6, a6, a7
	srli a7, t4, 41
	xor a6, a6, a7
	slli a7, t4, 23
	xor a6, a6, a7
	add a4, a4, a6
	xor a6, t5, t6
	and a6, a6, t4
	xor a6, a6, t6
	add a4, a4, a6
	lui a6, 623589
	addiw a6, a6, 339
	slli a6, a6, 32
	lui a7, 976494
	addiw a7, a7, -85
	add a6, a6, a7
	add a4, a4, a6
	add a4, a4, a5
	add t3, t3, a4
	srli a6, t0, 28
	slli a7, t0, 36
	xor a6, a6, a7
	srli a7, t0, 34
	xor a6, a6, a7
	slli a7, t0, 30
	xor a6, a6, a7
	srli a7, t0, 39
	xor a6, a6, a7
	slli a7, t0, 25
	xor a6, a6, a7
	add a4, a4, a6
	or a6, t0, t1
	and a6, a6, t2
	and a7, t0, t1
	or a6, a6, a7
	add a4, a4, a6
	ld a6, 56(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 16(a3)
	add a5, a5, a7
	ld a6, 80(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 72(a3)
	add a5, a5, a7
	sd a5, 72(a3)
	srli a6, t3, 14
	slli a7, t3, 50
	xor a6, a6, a7
	srli a7, t3, 18
	xor a6, a6, a7
	slli a7, t3, 46
	xor a6, a6, a7
	srli a7, t3, 41
	xor a6, a6, a7
	slli a7, t3, 23
	xor a6, a6, a7
	add t6, t6, a6
	xor a6, t4, t5
	and a6, a6, t3
	xor a6, a6, t5
	add t6, t6, a6
	lui a6, 688924
	addiw a6, a6, 1645
	slli a6, a6, 32
	lui a7, 187203
	addiw a7, a7, 528
	add a6, a6, a7
	add t6, t6, a6
	add t6, t6, a5
	add t2, t2, t6
	srli a6, a4, 28
	slli a7, a4, 36
	xor a6, a6, a7
	srli a7, a4, 34
	xor a6, a6, a7
	slli a7, a4, 30
	xor a6, a6, a7
	srli a7, a4, 39
	xor a6, a6, a7
	slli a7, a4, 25
	xor a6, a6, a7
	add t6, t6, a6
	or a6, a4, t0
	and a6, a6, t1
	and a7, a4, t0
	or a6, a6, a7
	add t6, t6, a6
	ld a6, 64(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 24(a3)
	add a5, a5, a7
	ld a6, 88(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 80(a3)
	add a5, a5, a7
	sd a5, 80(a3)
	srli a6, t2, 14
	slli a7, t2, 50
	xor a6, a6, a7
	srli a7, t2, 18
	xor a6, a6, a7
	slli a7, t2, 46
	xor a6, a6, a7
	srli a7, t2, 41
	xor a6, a6, a7
	slli a7, t2, 23
	xor a6, a6, a7
	add t5, t5, a6
	xor a6, t3, t4
	and a6, a6, t2
	xor a6, a6, t4
	add t5, t5, a6
	lui a6, 720946
	addiw a6, a6, 1993
	slli a6, a6, 32
	lui a7, 626610
	addiw a7, a7, 319
	add a6, a6, a7
	add t5, t5, a6
	add t5, t5, a5
	add t1, t1, t5
	srli a6, t6, 28
	slli a7, t6, 36
	xor a6, a6, a7
	srli a7, t6, 34
	xor a6, a6, a7
	slli a7, t6, 30
	xor a6, a6, a7
	srli a7, t6, 39
	xor a6, a6, a7
	slli a7, t6, 25
	xor a6, a6, a7
	add t5, t5, a6
	or a6, t6, a4
	and a6, a6, t0
	and a7, t6, a4
	or a6, a6, a7
	add t5, t5, a6
	ld a6, 72(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 32(a3)
	add a5, a5, a7
	ld a6, 96(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 88(a3)
	add a5, a5, a7
	sd a5, 88(a3)
	srli a6, t1, 14
	slli a7, t1, 50
	xor a6, a6, a7
	srli a7, t1, 18
	xor a6, a6, a7
	slli a7, t1, 46
	xor a6, a6, a7
	srli a7, t1, 41
	xor a6, a6, a7
	slli a7, t1, 23
	xor a6, a6, a7
	add t4, t4, a6
	xor a6, t2, t3
	and a6, a6, t1
	xor a6, a6, t3
	add t4, t4, a6
	lui a6, 783768
	addiw a6, a6, -56
	slli a6, a6, 32
	lui a7, 782065
	addiw a7, a7, -284
	add a6, a6, a7
	add t4, t4, a6
	add t4, t4, a5
	add t0, t0, t4
	srli a6, t5, 28
	slli a7, t5, 36
	xor a6, a6, a7
	srli a7, t5, 34
	xor a6, a6, a7
	slli a7, t5, 30
	xor a6, a6, a7
	srli a7, t5, 39
	xor a6, a6, a7
	slli a7, t5, 25
	xor a6, a6, a7
	add t4, t4, a6
	or a6, t5, t6
	and a6, a6, a4
	and a7, t5, t6
	or a6, a6, a7
	add t4, t4, a6
	ld a6, 80(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 40(a3)
	add a5, a5, a7
	ld a6, 104(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 96(a3)
	add a5, a5, a7
	sd a5, 96(a3)
	srli a6, t0, 14
	slli a7, t0, 50
	xor a6, a6, a7
	srli a7, t0, 18
	xor a6, a6, a7
	slli a7, t0, 46
	xor a6, a6, a7
	srli a7, t0, 41
	xor a6, a6, a7
	slli a7, t0, 23
	xor a6, a6, a7
	add t3, t3, a6
	xor a6, t1, t2
	and a6, a6, t0
	xor a6, a6, t2
	add t3, t3, a6
	lui a6, 814593
	addiw a6, a6, -1037
	slli a6, a6, 32
	lui a7, 252553
	addiw a7, a7, -62
	add a6, a6, a7
	add t3, t3, a6
	add t3, t3, a5
	add a4, a4, t3
	srli a6, t4, 28
	slli a7, t4, 36
	xor a6, a6, a7
	srli a7, t4, 34
	xor a6, a6, a7
	slli a7, t4, 30
	xor a6, a6, a7
	srli a7, t4, 39
	xor a6, a6, a7
	slli a7, t4, 25
	xor a6, a6, a7
	add t3, t3, a6
	or a6, t4, t5
	and a6, a6, t6
	and a7, t4, t5
	or a6, a6, a7
	add t3, t3, a6
	ld a6, 88(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 48(a3)
	add a5, a5, a7
	ld a6, 112(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 104(a3)
	add a5, a5, a7
	sd a5, 104(a3)
	srli a6, a4, 14
	slli a7, a4, 50
	xor a6, a6, a7
	srli a7, a4, 18
	xor a6, a6, a7
	slli a7, a4, 46
	xor a6, a6, a7
	srli a7, a4, 41
	xor a6, a6, a7
	slli a7, a4, 23
	xor a6, a6, a7
	add t2, t2, a6
	xor a6, t0, t1
	and a6, a6, a4
	xor a6, a6, t1
	add t2, t2, a6
	lui a6, 875129
	addiw a6, a6, 328
	slli a6, a6, 32
	lui a7, 602282
	addiw a7, a7, 1829
	add a6, a6, a7
	add t2, t2, a6
	add t2, t2, a5
	add t6, t6, t2
	srli a6, t3, 28
	slli a7, t3, 36
	xor a6, a6, a7
	srli a7, t3, 34
	xor a6, a6, a7
	slli a7, t3, 30
	xor a6, a6, a7
	srli a7, t3, 39
	xor a6, a6, a7
	slli a7, t3, 25
	xor a6, a6, a7
	add t2, t2, a6
	or a6, t3, t4
	and a6, a6, t5
	and a7, t3, t4
	or a6, a6, a7
	add t2, t2, a6
	ld a6, 96(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 56(a3)
	add a5, a5, a7
	ld a6, 120(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 112(a3)
	add a5, a5, a7
	sd a5, 112(a3)
	srli a6, t6, 14
	slli a7, t6, 50
	xor a6, a6, a7
	srli a7, t6, 18
	xor a6, a6, a7
	slli a7, t6, 46
	xor a6, a6, a7
	srli a7, t6, 41
	xor a6, a6, a7
	slli a7, t6, 23
	xor a6, a6, a7
	add t1, t1, a6
	xor a6, a4, t0
	and a6, a6, t6
	xor a6, a6, t0
	add t1, t1, a6
	lui a6, 27814
	addiw a6, a6, 850
	slli a6, a6, 32
	lui a7, 917560
	addiw a7, a7, 623
	add a6, a6, a7
	add t1, t1, a6
	add t1, t1, a5
	add t5, t5, t1
	srli a6, t2, 28
	slli a7, t2, 36
	xor a6, a6, a7
	srli a7, t2, 34
	xor a6, a6, a7
	slli a7, t2, 30
	xor a6, a6, a7
	srli a7, t2, 39
	xor a6, a6, a7
	slli a7, t2, 25
	xor a6, a6, a7
	add t1, t1, a6
	or a6, t2, t3
	and a6, a6, t4
	and a7, t2, t3
	or a6, a6, a7
	add t1, t1, a6
	ld a6, 104(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 64(a3)
	add a5, a5, a7
	ld a6, 0(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 120(a3)
	add a5, a5, a7
	sd a5, 120(a3)
	srli a6, t5, 14
	slli a7, t5, 50
	xor a6, a6, a7
	srli a7, t5, 18
	xor a6, a6, a7
	slli a7, t5, 46
	xor a6, a6, a7
	srli a7, t5, 41
	xor a6, a6, a7
	slli a7, t5, 23
	xor a6, a6, a7
	add t0, t0, a6
	xor a6, t6, a4
	and a6, a6, t5
	xor a6, a6, a4
	add t0, t0, a6
	lui a6, 82579
	addiw a6, a6, -1689
	slli a6, a6, 32
	lui a7, 41191
	addiw a7, a7, -400
	add a6, a6, a7
	add t0, t0, a6
	add t0, t0, a5
	add t4, t4, t0
	srli a6, t1, 28
	slli a7, t1, 36
	xor a6, a6, a7
	srli a7, t1, 34
	xor a6, a6, a7
	slli a7, t1, 30
	xor a6, a6, a7
	srli a7, t1, 39
	xor a6, a6, a7
	slli a7, t1, 25
	xor a6, a6, a7
	add t0, t0, a6
	or a6, t1, t2
	and a6, a6, t3
	and a7, t1, t2
	or a6, a6, a7
	add t0, t0, a6
	ld a6, 112(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 72(a3)
	add a5, a5, a7
	ld a6, 8(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 0(a3)
	add a5, a5, a7
	sd a5, 0(a3)
	srli a6, t4, 14
	slli a7, t4, 50
	xor a6, a6, a7
	srli a7, t4, 18
	xor a6, a6, a7
	slli a7, t4, 46
	xor a6, a6, a7
	srli a7, t4, 41
	xor a6, a6, a7
	slli a7, t4, 23
	xor a6, a6, a7
	add a4, a4, a6
	xor a6, t5, t6
	and a6, a6, t4
	xor a6, a6, t6
	add a4, a4, a6
	lui a6, 162673
	addiw a6, a6, -1403
	slli a6, a6, 32
	lui a7, 290083
	addiw a7, a7, -4
	add a6, a6, a7
	add a4, a4, a6
	add a4, a4, a5
	add t3, t3, a4
	srli a6, t0, 28
	slli a7, t0, 36
	xor a6, a6, a7
	srli a7, t0, 34
	xor a6, a6, a7
	slli a7, t0, 30
	xor a6, a6, a7
	srli a7, t0, 39
	xor a6, a6, a7
	slli a7, t0, 25
	xor a6, a6, a7
	add a4, a4, a6
	or a6, t0, t1
	and a6, a6, t2
	and a7, t0, t1
	or a6, a6, a7
	add a4, a4, a6
	ld a6, 120(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 80(a3)
	add a5, a5, a7
	ld a6, 16(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 8(a3)
	add a5, a5, a7
	sd a5, 8(a3)
	srli a6, t3, 14
	slli a7, t3, 50
	xor a6, a6, a7
	srli a7, t3, 18
	xor a6, a6, a7
	slli a7, t3, 46
	xor a6, a6, a7
	srli a7, t3, 41
	xor a6, a6, a7
	slli a7, t3, 23
	xor a6, a6, a7
	add t6, t6, a6
	xor a6, t4, t5
	and a6, a6, t3
	xor a6, a6, t5
	add t6, t6, a6
	lui a6, 188850
	addiw a6, a6, 312
	slli a6, a6, 32
	lui a7, 377453
	addiw a7, a7, -1754
	add a6, a6, a7
	add t6, t6, a6
	add t6, t6, a5
	add t2, t2, t6
	srli a6, a4, 28
	slli a7, a4, 36
	xor a6, a6, a7
	srli a7, a4, 34
	xor a6, a6, a7
	slli a7, a4, 30
	xor a6, a6, a7
	srli a7, a4, 39
	xor a6, a6, a7
	slli a7, a4, 25
	xor a6, a6, a7
	add t6, t6, a6
	or a6, a4, t0
	and a6, a6, t1
	and a7, a4, t0
	or a6, a6, a7
	add t6, t6, a6
	ld a6, 0(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 88(a3)
	add a5, a5, a7
	ld a6, 24(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 16(a3)
	add a5, a5, a7
	sd a5, 16(a3)
	srli a6, t2, 14
	slli a7, t2, 50
	xor a6, a6, a7
	srli a7, t2, 18
	xor a6, a6, a7
	slli a7, t2, 46
	xor a6, a6, a7
	srli a7, t2, 41
	xor a6, a6, a7
	slli a7, t2, 23
	xor a6, a6, a7
	add t5, t5, a6
	xor a6, t3, t4
	and a6, a6, t2
	xor a6, a6, t4
	add t5, t5, a6
	lui a6, 316103
	addiw a6, a6, -516
	slli a6, a6, 32
	lui a7, 371779
	addiw a7, a7, -1299
	add a6, a6, a7
	add t5, t5, a6
	add t5, t5, a5
	add t1, t1, t5
	srli a6, t6, 28
	slli a7, t6, 36
	xor a6, a6, a7
	srli a7, t6, 34
	xor a6, a6, a7
	slli a7, t6, 30
	xor a6, a6, a7
	srli a7, t6, 39
	xor a6, a6, a7
	slli a7, t6, 25
	xor a6, a6, a7
	add t5, t5, a6
	or a6, t6, a4
	and a6, a6, t0
	and a7, t6, a4
	or a6, a6, a7
	add t5, t5, a6
	ld a6, 8(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 96(a3)
	add a5, a5, a7
	ld a6, 32(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 24(a3)
	add a5, a5, a7
	sd a5, 24(a3)
	srli a6, t1, 14
	slli a7, t1, 50
	xor a6, a6, a7
	srli a7, t1, 18
	xor a6, a6, a7
	slli a7, t1, 46
	xor a6, a6, a7
	srli a7, t1, 41
	xor a6, a6, a7
	slli a7, t1, 23
	xor a6, a6, a7
	add t4, t4, a6
	xor a6, t2, t3
	and a6, a6, t1
	xor a6, a6, t3
	add t4, t4, a6
	lui a6, 340865
	addiw a6, a6, -748
	slli a6, a6, 32
	lui a7, 645467
	addiw a7, a7, 991
	add a6, a6, a7
	add t4, t4, a6
	add t4, t4, a5
	add t0, t0, t4
	srli a6, t5, 28
	slli a7, t5, 36
	xor a6, a6, a7
	srli a7, t5, 34
	xor a6, a6, a7
	slli a7, t5, 30
	xor a6, a6, a7
	srli a7, t5, 39
	xor a6, a6, a7
	slli a7, t5, 25
	xor a6, a6, a7
	add t4, t4, a6
	or a6, t5, t6
	and a6, a6, a4
	and a7, t5, t6
	or a6, a6, a7
	add t4, t4, a6
	ld a6, 16(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 104(a3)
	add a5, a5, a7
	ld a6, 40(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 32(a3)
	add a5, a5, a7
	sd a5, 32(a3)
	srli a6, t0, 14
	slli a7, t0, 50
	xor a6, a6, a7
	srli a7, t0, 18
	xor a6, a6, a7
	slli a7, t0, 46
	xor a6, a6, a7
	srli a7, t0, 41
	xor a6, a6, a7
	slli a7, t0, 23
	xor a6, a6, a7
	add t3, t3, a6
	xor a6, t1, t2
	and a6, a6, t0
	xor a6, a6, t2
	add t3, t3, a6
	lui a6, 413863
	addiw a6, a6, 853
	slli a6, a6, 32
	lui a7, 572150
	addiw a7, a7, 990
	add a6, a6, a7
	add t3, t3, a6
	add t3, t3, a5
	add a4, a4, t3
	srli a6, t4, 28
	slli a7, t4, 36
	xor a6, a6, a7
	srli a7, t4, 34
	xor a6, a6, a7
	slli a7, t4, 30
	xor a6, a6, a7
	srli a7, t4, 39
	xor a6, a6, a7
	slli a7, t4, 25
	xor a6, a6, a7
	add t3, t3, a6
	or a6, t4, t5
	and a6, a6, t6
	and a7, t4, t5
	or a6, a6, a7
	add t3, t3, a6
	ld a6, 24(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 112(a3)
	add a5, a5, a7
	ld a6, 48(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 40(a3)
	add a5, a5, a7
	sd a5, 40(a3)
	srli a6, a4, 14
	slli a7, a4, 50
	xor a6, a6, a7
	srli a7, a4, 18
	xor a6, a6, a7
	slli a7, a4, 46
	xor a6, a6, a7
	srli a7, a4, 41
	xor a6, a6, a7
	slli a7, a4, 23
	xor a6, a6, a7
	add t2, t2, a6
	xor a6, t0, t1
	and a6, a6, a4
	xor a6, a6, t1
	add t2, t2, a6
	lui a6, 485025
	addiw a6, a6, -1349
	slli a6, a6, 32
	lui a7, 247675
	addiw a7, a7, 680
	add a6, a6, a7
	add t2, t2, a6
	add t2, t2, a5
	add t6, t6, t2
	srli a6, t3, 28
	slli a7, t3, 36
	xor a6, a6, a7
	srli a7, t3, 34
	xor a6, a6, a7
	slli a7, t3, 30
	xor a6, a6, a7
	srli a7, t3, 39
	xor a6, a6, a7
	slli a7, t3, 25
	xor a6, a6, a7
	add t2, t2, a6
	or a6, t3, t4
	and a6, a6, t5
	and a7, t3, t4
	or a6, a6, a7
	add t2, t2, a6
	ld a6, 32(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 120(a3)
	add a5, a5, a7
	ld a6, 56(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 48(a3)
	add a5, a5, a7
	sd a5, 48(a3)
	srli a6, t6, 14
	slli a7, t6, 50
	xor a6, a6, a7
	srli a7, t6, 18
	xor a6, a6, a7
	slli a7, t6, 46
	xor a6, a6, a7
	srli a7, t6, 41
	xor a6, a6, a7
	slli a7, t6, 23
	xor a6, a6, a7
	add t1, t1, a6
	xor a6, a4, t0
	and a6, a6, t6
	xor a6, a6, t0
	add t1, t1, a6
	lui a6, 531501
	addiw a6, a6, -1746
	slli a6, a6, 32
	lui a7, 294619
	addiw a7, a7, -282
	add a6, a6, a7
	add t1, t1, a6
	add t1, t1, a5
	add t5, t5, t1
	srli a6, t2, 28
	slli a7, t2, 36
	xor a6, a6, a7
	srli a7, t2, 34
	xor a6, a6, a7
	slli a7, t2, 30
	xor a6, a6, a7
	srli a7, t2, 39
	xor a6, a6, a7
	slli a7, t2, 25
	xor a6, a6, a7
	add t1, t1, a6
	or a6, t2, t3
	and a6, a6, t4
	and a7, t2, t3
	or a6, a6, a7
	add t1, t1, a6
	ld a6, 40(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 0(a3)
	add a5, a5, a7
	ld a6, 64(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 56(a3)
	add a5, a5, a7
	sd a5, 56(a3)
	srli a6, t5, 14
	slli a7, t5, 50
	xor a6, a6, a7
	srli a7, t5, 18
	xor a6, a6, a7
	slli a7, t5, 46
	xor a6, a6, a7
	srli a7, t5, 41
	xor a6, a6, a7
	slli a7, t5, 23
	xor a6, a6, a7
	add t0, t0, a6
	xor a6, t6, a4
	and a6, a6, t5
	xor a6, a6, a4
	add t0, t0, a6
	lui a6, 599843
	addiw a6, a6, -891
	slli a6, a6, 32
	lui a7, 84003
	addiw a7, a7, 1339
	add a6, a6, a7
	add t0, t0, a6
	add t0, t0, a5
	add t4, t4, t0
	srli a6, t1, 28
	slli a7, t1, 36
	xor a6, a6, a7
	srli a7, t1, 34
	xor a6, a6, a7
	slli a7, t1, 30
	xor a6, a6, a7
	srli a7, t1, 39
	xor a6, a6, a7
	slli a7, t1, 25
	xor a6, a6, a7
	add t0, t0, a6
	or a6, t1, t2
	and a6, a6, t3
	and a7, t1, t2
	or a6, a6, a7
	add t0, t0, a6
	ld a6, 48(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 8(a3)
	add a5, a5, a7
	ld a6, 72(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 64(a3)
	add a5, a5, a7
	sd a5, 64(a3)
	srli a6, t4, 14
	slli a7, t4, 50
	xor a6, a6, a7
	srli a7, t4, 18
	xor a6, a6, a7
	slli a7, t4, 46
	xor a6, a6, a7
	srli a7, t4, 41
	xor a6, a6, a7
	slli a7, t4, 23
	xor a6, a6, a7
	add a4, a4, a6
	xor a6, t5, t6
	and a6, a6, t4
	xor a6, a6, t6
	add a4, a4, a6
	lui a6, 666623
	addiw a6, a6, -1887
	slli a6, a6, 32
	lui a7, 315152
	addiw a7, a7, 868
	add a6, a6, a7
	add a4, a4, a6
	add a4, a4, a5
	add t3, t3, a4
	srli a6, t0, 28
	slli a7, t0, 36
	xor a6, a6, a7
	srli a7, t0, 34
	xor a6, a6, a7
	slli a7, t0, 30
	xor a6, a6, a7
	srli a7, t0, 39
	xor a6, a6, a7
	slli a7, t0, 25
	xor a6, a6, a7
	add a4, a4, a6
	or a6, t0, t1
	and a6, a6, t2
	and a7, t0, t1
	or a6, a6, a7
	add a4, a4, a6
	ld a6, 56(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 16(a3)
	add a5, a5, a7
	ld a6, 80(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 72(a3)
	add a5, a5, a7
	sd a5, 72(a3)
	srli a6, t3, 14
	slli a7, t3, 50
	xor a6, a6, a7
	srli a7, t3, 18
	xor a6, a6, a7
	slli a7, t3, 46
	xor a6, a6, a7
	srli a7, t3, 41
	xor a6, a6, a7
	slli a7, t3, 23
	xor a6, a6, a7
	add t6, t6, a6
	xor a6, t4, t5
	and a6, a6, t3
	xor a6, a6, t5
	add t6, t6, a6
	lui a6, 688550
	addiw a6, a6, 1612
	slli a6, a6, 32
	lui a7, 771107
	addiw a7, a7, 1
	add a6, a6, a7
	add t6, t6, a6
	add t6, t6, a5
	add t2, t2, t6
	srli a6, a4, 28
	slli a7, a4, 36
	xor a6, a6, a7
	srli a7, a4, 34
	xor a6, a6, a7
	slli a7, a4, 30
	xor a6, a6, a7
	srli a7, a4, 39
	xor a6, a6, a7
	slli a7, a4, 25
	xor a6, a6, a7
	add t6, t6, a6
	or a6, a4, t0
	and a6, a6, t1
	and a7, a4, t0
	or a6, a6, a7
	add t6, t6, a6
	ld a6, 64(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 24(a3)
	add a5, a5, a7
	ld a6, 88(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 80(a3)
	add a5, a5, a7
	sd a5, 80(a3)
	srli a6, t2, 14
	slli a7, t2, 50
	xor a6, a6, a7
	srli a7, t2, 18
	xor a6, a6, a7
	slli a7, t2, 46
	xor a6, a6, a7
	srli a7, t2, 41
	xor a6, a6, a7
	slli a7, t2, 23
	xor a6, a6, a7
	add t5, t5, a6
	xor a6, t3, t4
	and a6, a6, t2
	xor a6, a6, t4
	add t5, t5, a6
	lui a6, 795833
	addiw a6, a6, -1167
	slli a6, a6, 32
	lui a7, 855945
	addiw a7, a7, 1937
	add a6, a6, a7
	add t5, t5, a6
	add t5, t5, a5
	add t1, t1, t5
	srli a6, t6, 28
	slli a7, t6, 36
	xor a6, a6, a7
	srli a7, t6, 34
	xor a6, a6, a7
	slli a7, t6, 30
	xor a6, a6, a7
	srli a7, t6, 39
	xor a6, a6, a7
	slli a7, t6, 25
	xor a6, a6, a7
	add t5, t5, a6
	or a6, t6, a4
	and a6, a6, t0
	and a7, t6, a4
	or a6, a6, a7
	add t5, t5, a6
	ld a6, 72(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 32(a3)
	add a5, a5, a7
	ld a6, 96(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 88(a3)
	add a5, a5, a7
	sd a5, 88(a3)
	srli a6, t1, 14
	slli a7, t1, 50
	xor a6, a6, a7
	srli a7, t1, 18
	xor a6, a6, a7
	slli a7, t1, 46
	xor a6, a6, a7
	srli a7, t1, 41
	xor a6, a6, a7
	slli a7, t1, 23
	xor a6, a6, a7
	add t4, t4, a6
	xor a6, t2, t3
	and a6, a6, t1
	xor a6, a6, t3
	add t4, t4, a6
	lui a6, 816837
	addiw a6, a6, 419
	slli a6, a6, 32
	lui a7, 25932
	addiw a7, a7, -464
	add a6, a6, a7
	add t4, t4, a6
	add t4, t4, a5
	add t0, t0, t4
	srli a6, t5, 28
	slli a7, t5, 36
	xor a6, a6, a7
	srli a7, t5, 34
	xor a6, a6, a7
	slli a7, t5, 30
	xor a6, a6, a7
	srli a7, t5, 39
	xor a6, a6, a7
	slli a7, t5, 25
	xor a6, a6, a7
	add t4, t4, a6
	or a6, t5, t6
	and a6, a6, a4
	and a7, t5, t6
	or a6, a6, a7
	add t4, t4, a6
	ld a6, 80(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 40(a3)
	add a5, a5, a7
	ld a6, 104(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 96(a3)
	add a5, a5, a7
	sd a5, 96(a3)
	srli a6, t0, 14
	slli a7, t0, 50
	xor a6, a6, a7
	srli a7, t0, 18
	xor a6, a6, a7
	slli a7, t0, 46
	xor a6, a6, a7
	srli a7, t0, 41
	xor a6, a6, a7
	slli a7, t0, 23
	xor a6, a6, a7
	add t3, t3, a6
	xor a6, t1, t2
	and a6, a6, t0
	xor a6, a6, t2
	add t3, t3, a6
	lui a6, 858415
	addiw a6, a6, -2022
	slli a6, a6, 32
	lui a7, 880373
	addiw a7, a7, 536
	add a6, a6, a7
	add t3, t3, a6
	add t3, t3, a5
	add a4, a4, t3
	srli a6, t4, 28
	slli a7, t4, 36
	xor a6, a6, a7
	srli a7, t4, 34
	xor a6, a6, a7
	slli a7, t4, 30
	xor a6, a6, a7
	srli a7, t4, 39
	xor a6, a6, a7
	slli a7, t4, 25
	xor a6, a6, a7
	add t3, t3, a6
	or a6, t4, t5
	and a6, a6, t6
	and a7, t4, t5
	or a6, a6, a7
	add t3, t3, a6
	ld a6, 88(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 48(a3)
	add a5, a5, a7
	ld a6, 112(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 104(a3)
	add a5, a5, a7
	sd a5, 104(a3)
	srli a6, a4, 14
	slli a7, a4, 50
	xor a6, a6, a7
	srli a7, a4, 18
	xor a6, a6, a7
	slli a7, a4, 46
	xor a6, a6, a7
	srli a7, a4, 41
	xor a6, a6, a7
	slli a7, a4, 23
	xor a6, a6, a7
	add t2, t2, a6
	xor a6, t0, t1
	and a6, a6, a4
	xor a6, a6, t1
	add t2, t2, a6
	lui a6, 878992
	addiw a6, a6, 1572
	slli a6, a6, 32
	lui a7, 349787
	addiw a7, a7, -1776
	add a6, a6, a7
	add t2, t2, a6
	add t2, t2, a5
	add t6, t6, t2
	srli a6, t3, 28
	slli a7, t3, 36
	xor a6, a6, a7
	srli a7, t3, 34
	xor a6, a6, a7
	slli a7, t3, 30
	xor a6, a6, a7
	srli a7, t3, 39
	xor a6, a6, a7
	slli a7, t3, 25
	xor a6, a6, a7
	add t2, t2, a6
	or a6, t3, t4
	and a6, a6, t5
	and a7, t3, t4
	or a6, a6, a7
	add t2, t2, a6
	ld a6, 96(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 56(a3)
	add a5, a5, a7
	ld a6, 120(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 112(a3)
	add a5, a5, a7
	sd a5, 112(a3)
	srli a6, t6, 14
	slli a7, t6, 50
	xor a6, a6, a7
	srli a7, t6, 18
	xor a6, a6, a7
	slli a7, t6, 46
	xor a6, a6, a7
	srli a7, t6, 41
	xor a6, a6, a7
	slli a7, t6, 23
	xor a6, a6, a7
	add t1, t1, a6
	xor a6, a4, t0
	and a6, a6, t6
	xor a6, a6, t0
	add t1, t1, a6
	lui a6, 999651
	addiw a6, a6, 1413
	slli a6, a6, 32
	lui a7, 358162
	addiw a7, a7, 42
	add a6, a6, a7
	add t1, t1, a6
	add t1, t1, a5
	add t5, t5, t1
	srli a6, t2, 28
	slli a7, t2, 36
	xor a6, a6, a7
	srli a7, t2, 34
	xor a6, a6, a7
	slli a7, t2, 30
	xor a6, a6, a7
	srli a7, t2, 39
	xor a6, a6, a7
	slli a7, t2, 25
	xor a6, a6, a7
	add t1, t1, a6
	or a6, t2, t3
	and a6, a6, t4
	and a7, t2, t3
	or a6, a6, a7
	add t1, t1, a6
	ld a6, 104(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 64(a3)
	add a5, a5, a7
	ld a6, 0(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 120(a3)
	add a5, a5, a7
	sd a5, 120(a3)
	srli a6, t5, 14
	slli a7, t5, 50
	xor a6, a6, a7
	srli a7, t5, 18
	xor a6, a6, a7
	slli a7, t5, 46
	xor a6, a6, a7
	srli a7, t5, 41
	xor a6, a6, a7
	slli a7, t5, 23
	xor a6, a6, a7
	add t0, t0, a6
	xor a6, t6, a4
	and a6, a6, t5
	xor a6, a6, a4
	add t0, t0, a6
	lui a6, 67242
	addiw a6, a6, 112
	slli a6, a6, 32
	lui a7, 207805
	addiw a7, a7, 440
	add a6, a6, a7
	add t0, t0, a6
	add t0, t0, a5
	add t4, t4, t0
	srli a6, t1, 28
	slli a7, t1, 36
	xor a6, a6, a7
	srli a7, t1, 34
	xor a6, a6, a7
	slli a7, t1, 30
	xor a6, a6, a7
	srli a7, t1, 39
	xor a6, a6, a7
	slli a7, t1, 25
	xor a6, a6, a7
	add t0, t0, a6
	or a6, t1, t2
	and a6, a6, t3
	and a7, t1, t2
	or a6, a6, a7
	add t0, t0, a6
	ld a6, 112(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 72(a3)
	add a5, a5, a7
	ld a6, 8(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 0(a3)
	add a5, a5, a7
	sd a5, 0(a3)
	srli a6, t4, 14
	slli a7, t4, 50
	xor a6, a6, a7
	srli a7, t4, 18
	xor a6, a6, a7
	slli a7, t4, 46
	xor a6, a6, a7
	srli a7, t4, 41
	xor a6, a6, a7
	slli a7, t4, 23
	xor a6, a6, a7
	add a4, a4, a6
	xor a6, t5, t6
	and a6, a6, t4
	xor a6, a6, t6
	add a4, a4, a6
	lui a6, 105036
	addiw a6, a6, 279
	slli a6, a6, 32
	lui a7, 757037
	addiw a7, a7, 200
	add a6, a6, a7
	add a4, a4, a6
	add a4, a4, a5
	add t3, t3, a4
	srli a6, t0, 28
	slli a7, t0, 36
	xor a6, a6, a7
	srli a7, t0, 34
	xor a6, a6, a7
	slli a7, t0, 30
	xor a6, a6, a7
	srli a7, t0, 39
	xor a6, a6, a7
	slli a7, t0, 25
	xor a6, a6, a7
	add a4, a4, a6
	or a6, t0, t1
	and a6, a6, t2
	and a7, t0, t1
	or a6, a6, a7
	add a4, a4, a6
	ld a6, 120(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 80(a3)
	add a5, a5, a7
	ld a6, 16(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 8(a3)
	add a5, a5, a7
	sd a5, 8(a3)
	srli a6, t3, 14
	slli a7, t3, 50
	xor a6, a6, a7
	srli a7, t3, 18
	xor a6, a6, a7
	slli a7, t3, 46
	xor a6, a6, a7
	srli a7, t3, 41
	xor a6, a6, a7
	slli a7, t3, 23
	xor a6, a6, a7
	add t6, t6, a6
	xor a6, t4, t5
	and a6, a6, t3
	xor a6, a6, t5
	add t6, t6, a6
	lui a6, 123767
	addiw a6, a6, -1016
	slli a6, a6, 32
	lui a7, 332827
	addiw a7, a7, -1197
	add a6, a6, a7
	add t6, t6, a6
	add t6, t6, a5
	add t2, t2, t6
	srli a6, a4, 28
	slli a7, a4, 36
	xor a6, a6, a7
	srli a7, a4, 34
	xor a6, a6, a7
	slli a7, a4, 30
	xor a6, a6, a7
	srli a7, a4, 39
	xor a6, a6, a7
	slli a7, a4, 25
	xor a6, a6, a7
	add t6, t6, a6
	or a6, a4, t0
	and a6, a6, t1
	and a7, a4, t0
	or a6, a6, a7
	add t6, t6, a6
	ld a6, 0(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 88(a3)
	add a5, a5, a7
	ld a6, 24(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 16(a3)
	add a5, a5, a7
	sd a5, 16(a3)
	srli a6, t2, 14
	slli a7, t2, 50
	xor a6, a6, a7
	srli a7, t2, 18
	xor a6, a6, a7
	slli a7, t2, 46
	xor a6, a6, a7
	srli a7, t2, 41
	xor a6, a6, a7
	slli a7, t2, 23
	xor a6, a6, a7
	add t5, t5, a6
	xor a6, t3, t4
	and a6, a6, t2
	xor a6, a6, t4
	add t5, t5, a6
	lui a6, 160903
	addiw a6, a6, 1869
	slli a6, a6, 32
	lui a7, 915695
	addiw a7, a7, -1127
	add a6, a6, a7
	add t5, t5, a6
	add t5, t5, a5
	add t1, t1, t5
	srli a6, t6, 28
	slli a7, t6, 36
	xor a6, a6, a7
	srli a7, t6, 34
	xor a6, a6, a7
	slli a7, t6, 30
	xor a6, a6, a7
	srli a7, t6, 39
	xor a6, a6, a7
	slli a7, t6, 25
	xor a6, a6, a7
	add t5, t5, a6
	or a6, t6, a4
	and a6, a6, t0
	and a7, t6, a4
	or a6, a6, a7
	add t5, t5, a6
	ld a6, 8(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 96(a3)
	add a5, a5, a7
	ld a6, 32(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 24(a3)
	add a5, a5, a7
	sd a5, 24(a3)
	srli a6, t1, 14
	slli a7, t1, 50
	xor a6, a6, a7
	srli a7, t1, 18
	xor a6, a6, a7
	slli a7, t1, 46
	xor a6, a6, a7
	srli a7, t1, 41
	xor a6, a6, a7
	slli a7, t1, 23
	xor a6, a6, a7
	add t4, t4, a6
	xor a6, t2, t3
	and a6, a6, t1
	xor a6, a6, t3
	add t4, t4, a6
	lui a6, 215820
	addiw a6, a6, -842
	slli a6, a6, 32
	lui a7, 924085
	addiw a7, a7, -1880
	add a6, a6, a7
	add t4, t4, a6
	add t4, t4, a5
	add t0, t0, t4
	srli a6, t5, 28
	slli a7, t5, 36
	xor a6, a6, a7
	srli a7, t5, 34
	xor a6, a6, a7
	slli a7, t5, 30
	xor a6, a6, a7
	srli a7, t5, 39
	xor a6, a6, a7
	slli a7, t5, 25
	xor a6, a6, a7
	add t4, t4, a6
	or a6, t5, t6
	and a6, a6, a4
	and a7, t5, t6
	or a6, a6, a7
	add t4, t4, a6
	ld a6, 16(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 104(a3)
	add a5, a5, a7
	ld a6, 40(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 32(a3)
	add a5, a5, a7
	sd a5, 32(a3)
	srli a6, t0, 14
	slli a7, t0, 50
	xor a6, a6, a7
	srli a7, t0, 18
	xor a6, a6, a7
	slli a7, t0, 46
	xor a6, a6, a7
	srli a7, t0, 41
	xor a6, a6, a7
	slli a7, t0, 23
	xor a6, a6, a7
	add t3, t3, a6
	xor a6, t1, t2
	and a6, a6, t0
	xor a6, a6, t2
	add t3, t3, a6
	lui a6, 233921
	addiw a6, a6, -844
	slli a6, a6, 32
	lui a7, 810134
	addiw a7, a7, -1437
	add a6, a6, a7
	add t3, t3, a6
	add t3, t3, a5
	add a4, a4, t3
	srli a6, t4, 28
	slli a7, t4, 36
	xor a6, a6, a7
	srli a7, t4, 34
	xor a6, a6, a7
	slli a7, t4, 30
	xor a6, a6, a7
	srli a7, t4, 39
	xor a6, a6, a7
	slli a7, t4, 25
	xor a6, a6, a7
	add t3, t3, a6
	or a6, t4, t5
	and a6, a6, t6
	and a7, t4, t5
	or a6, a6, a7
	add t3, t3, a6
	ld a6, 24(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 112(a3)
	add a5, a5, a7
	ld a6, 48(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 40(a3)
	add a5, a5, a7
	sd a5, 40(a3)
	srli a6, a4, 14
	slli a7, a4, 50
	xor a6, a6, a7
	srli a7, a4, 18
	xor a6, a6, a7
	slli a7, a4, 46
	xor a6, a6, a7
	srli a7, a4, 41
	xor a6, a6, a7
	slli a7, a4, 23
	xor a6, a6, a7
	add t2, t2, a6
	xor a6, t0, t1
	and a6, a6, a4
	xor a6, a6, t1
	add t2, t2, a6
	lui a6, 322955
	addiw a6, a6, -1461
	slli a6, a6, 32
	lui a7, 930841
	addiw a7, a7, -1333
	add a6, a6, a7
	add t2, t2, a6
	add t2, t2, a5
	add t6, t6, t2
	srli a6, t3, 28
	slli a7, t3, 36
	xor a6, a6, a7
	srli a7, t3, 34
	xor a6, a6, a7
	slli a7, t3, 30
	xor a6, a6, a7
	srli a7, t3, 39
	xor a6, a6, a7
	slli a7, t3, 25
	xor a6, a6, a7
	add t2, t2, a6
	or a6, t3, t4
	and a6, a6, t5
	and a7, t3, t4
	or a6, a6, a7
	add t2, t2, a6
	ld a6, 32(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 120(a3)
	add a5, a5, a7
	ld a6, 56(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 48(a3)
	add a5, a5, a7
	sd a5, 48(a3)
	srli a6, t6, 14
	slli a7, t6, 50
	xor a6, a6, a7
	srli a7, t6, 18
	xor a6, a6, a7
	slli a7, t6, 46
	xor a6, a6, a7
	srli a7, t6, 41
	xor a6, a6, a7
	slli a7, t6, 23
	xor a6, a6, a7
	add t1, t1, a6
	xor a6, a4, t0
	and a6, a6, t6
	xor a6, a6, t0
	add t1, t1, a6
	lui a6, 375245
	addiw a6, a6, -1457
	slli a6, a6, 32
	lui a7, 489022
	addiw a7, a7, 883
	add a6, a6, a7
	add t1, t1, a6
	add t1, t1, a5
	add t5, t5, t1
	srli a6, t2, 28
	slli a7, t2, 36
	xor a6, a6, a7
	srli a7, t2, 34
	xor a6, a6, a7
	slli a7, t2, 30
	xor a6, a6, a7
	srli a7, t2, 39
	xor a6, a6, a7
	slli a7, t2, 25
	xor a6, a6, a7
	add t1, t1, a6
	or a6, t2, t3
	and a6, a6, t4
	and a7, t2, t3
	or a6, a6, a7
	add t1, t1, a6
	ld a6, 40(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 0(a3)
	add a5, a5, a7
	ld a6, 64(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 56(a3)
	add a5, a5, a7
	sd a5, 56(a3)
	srli a6, t5, 14
	slli a7, t5, 50
	xor a6, a6, a7
	srli a7, t5, 18
	xor a6, a6, a7
	slli a7, t5, 46
	xor a6, a6, a7
	srli a7, t5, 41
	xor a6, a6, a7
	slli a7, t5, 23
	xor a6, a6, a7
	add t0, t0, a6
	xor a6, t6, a4
	and a6, a6, t5
	xor a6, a6, a4
	add t0, t0, a6
	lui a6, 426727
	addiw a6, a6, -12
	slli a6, a6, 32
	lui a7, 879404
	addiw a7, a7, -1885
	add a6, a6, a7
	add t0, t0, a6
	add t0, t0, a5
	add t4, t4, t0
	srli a6, t1, 28
	slli a7, t1, 36
	xor a6, a6, a7
	srli a7, t1, 34
	xor a6, a6, a7
	slli a7, t1, 30
	xor a6, a6, a7
	srli a7, t1, 39
	xor a6, a6, a7
	slli a7, t1, 25
	xor a6, a6, a7
	add t0, t0, a6
	or a6, t1, t2
	and a6, a6, t3
	and a7, t1, t2
	or a6, a6, a7
	add t0, t0, a6
	ld a6, 48(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 8(a3)
	add a5, a5, a7
	ld a6, 72(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 64(a3)
	add a5, a5, a7
	sd a5, 64(a3)
	srli a6, t4, 14
	slli a7, t4, 50
	xor a6, a6, a7
	srli a7, t4, 18
	xor a6, a6, a7
	slli a7, t4, 46
	xor a6, a6, a7
	srli a7, t4, 41
	xor a6, a6, a7
	slli a7, t4, 23
	xor a6, a6, a7
	add a4, a4, a6
	xor a6, t5, t6
	and a6, a6, t4
	xor a6, a6, t6
	add a4, a4, a6
	lui a6, 477432
	addiw a6, a6, 750
	slli a6, a6, 32
	lui a7, 384763
	addiw a7, a7, 764
	add a6, a6, a7
	add a4, a4, a6
	add a4, a4, a5
	add t3, t3, a4
	srli a6, t0, 28
	slli a7, t0, 36
	xor a6, a6, a7
	srli a7, t0, 34
	xor a6, a6, a7
	slli a7, t0, 30
	xor a6, a6, a7
	srli a7, t0, 39
	xor a6, a6, a7
	slli a7, t0, 25
	xor a6, a6, a7
	add a4, a4, a6
	or a6, t0, t1
	and a6, a6, t2
	and a7, t0, t1
	or a6, a6, a7
	add a4, a4, a6
	ld a6, 56(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 16(a3)
	add a5, a5, a7
	ld a6, 80(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 72(a3)
	add a5, a5, a7
	sd a5, 72(a3)
	srli a6, t3, 14
	slli a7, t3, 50
	xor a6, a6, a7
	srli a7, t3, 18
	xor a6, a6, a7
	slli a7, t3, 46
	xor a6, a6, a7
	srli a7, t3, 41
	xor a6, a6, a7
	slli a7, t3, 23
	xor a6, a6, a7
	add t6, t6, a6
	xor a6, t4, t5
	and a6, a6, t3
	xor a6, a6, t5
	add t6, t6, a6
	lui a6, 494166
	addiw a6, a6, 879
	slli a6, a6, 32
	lui a7, 274803
	addiw a7, a7, -160
	add a6, a6, a7
	add t6, t6, a6
	add t6, t6, a5
	add t2, t2, t6
	srli a6, a4, 28
	slli a7, a4, 36
	xor a6, a6, a7
	srli a7, a4, 34
	xor a6, a6, a7
	slli a7, a4, 30
	xor a6, a6, a7
	srli a7, a4, 39
	xor a6, a6, a7
	slli a7, a4, 25
	xor a6, a6, a7
	add t6, t6, a6
	or a6, a4, t0
	and a6, a6, t1
	and a7, a4, t0
	or a6, a6, a7
	add t6, t6, a6
	ld a6, 64(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 24(a3)
	add a5, a5, a7
	ld a6, 88(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 80(a3)
	add a5, a5, a7
	sd a5, 80(a3)
	srli a6, t2, 14
	slli a7, t2, 50
	xor a6, a6, a7
	srli a7, t2, 18
	xor a6, a6, a7
	slli a7, t2, 46
	xor a6, a6, a7
	srli a7, t2, 41
	xor a6, a6, a7
	slli a7, t2, 23
	xor a6, a6, a7
	add t5, t5, a6
	xor a6, t3, t4
	and a6, a6, t2
	xor a6, a6, t4
	add t5, t5, a6
	lui a6, 543880
	addiw a6, a6, -2027
	slli a6, a6, 32
	lui a7, 663307
	addiw a7, a7, -1166
	add a6, a6, a7
	add t5, t5, a6
	add t5, t5, a5
	add t1, t1, t5
	srli a6, t6, 28
	slli a7, t6, 36
	xor a6, a6, a7
	srli a7, t6, 34
	xor a6, a6, a7
	slli a7, t6, 30
	xor a6, a6, a7
	srli a7, t6, 39
	xor a6, a6, a7
	slli a7, t6, 25
	xor a6, a6, a7
	add t5, t5, a6
	or a6, t6, a4
	and a6, a6, t0
	and a7, t6, a4
	or a6, a6, a7
	add t5, t5, a6
	ld a6, 72(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 32(a3)
	add a5, a5, a7
	ld a6, 96(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 88(a3)
	add a5, a5, a7
	sd a5, 88(a3)
	srli a6, t1, 14
	slli a7, t1, 50
	xor a6, a6, a7
	srli a7, t1, 18
	xor a6, a6, a7
	slli a7, t1, 46
	xor a6, a6, a7
	srli a7, t1, 41
	xor a6, a6, a7
	slli a7, t1, 23
	xor a6, a6, a7
	add t4, t4, a6
	xor a6, t2, t3
	and a6, a6, t1
	xor a6, a6, t3
	add t4, t4, a6
	lui a6, 576624
	addiw a6, a6, 520
	slli a6, a6, 32
	lui a7, 108100
	addiw a7, a7, -1556
	add a6, a6, a7
	add t4, t4, a6
	add t4, t4, a5
	add t0, t0, t4
	srli a6, t5, 28
	slli a7, t5, 36
	xor a6, a6, a7
	srli a7, t5, 34
	xor a6, a6, a7
	slli a7, t5, 30
	xor a6, a6, a7
	srli a7, t5, 39
	xor a6, a6, a7
	slli a7, t5, 25
	xor a6, a6, a7
	add t4, t4, a6
	or a6, t5, t6
	and a6, a6, a4
	and a7, t5, t6
	or a6, a6, a7
	add t4, t4, a6
	ld a6, 80(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 40(a3)
	add a5, a5, a7
	ld a6, 104(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 96(a3)
	add a5, a5, a7
	sd a5, 96(a3)
	srli a6, t0, 14
	slli a7, t0, 50
	xor a6, a6, a7
	srli a7, t0, 18
	xor a6, a6, a7
	slli a7, t0, 46
	xor a6, a6, a7
	srli a7, t0, 41
	xor a6, a6, a7
	slli a7, t0, 23
	xor a6, a6, a7
	add t3, t3, a6
	xor a6, t1, t2
	and a6, a6, t0
	xor a6, a6, t2
	add t3, t3, a6
	lui a6, 592880
	addiw a6, a6, -6
	slli a6, a6, 32
	lui a7, 144946
	addiw a7, a7, -472
	add a6, a6, a7
	add t3, t3, a6
	add t3, t3, a5
	add a4, a4, t3
	srli a6, t4, 28
	slli a7, t4, 36
	xor a6, a6, a7
	srli a7, t4, 34
	xor a6, a6, a7
	slli a7, t4, 30
	xor a6, a6, a7
	srli a7, t4, 39
	xor a6, a6, a7
	slli a7, t4, 25
	xor a6, a6, a7
	add t3, t3, a6
	or a6, t4, t5
	and a6, a6, t6
	and a7, t4, t5
	or a6, a6, a7
	add t3, t3, a6
	ld a6, 88(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 48(a3)
	add a5, a5, a7
	ld a6, 112(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 104(a3)
	add a5, a5, a7
	sd a5, 104(a3)
	srli a6, a4, 14
	slli a7, a4, 50
	xor a6, a6, a7
	srli a7, a4, 18
	xor a6, a6, a7
	slli a7, a4, 46
	xor a6, a6, a7
	srli a7, a4, 41
	xor a6, a6, a7
	slli a7, a4, 23
	xor a6, a6, a7
	add t2, t2, a6
	xor a6, t0, t1
	and a6, a6, a4
	xor a6, a6, t1
	add t2, t2, a6
	lui a6, 673031
	addiw a6, a6, -788
	slli a6, a6, 32
	lui a7, 911404
	addiw a7, a7, -535
	add a6, a6, a7
	add t2, t2, a6
	add t2, t2, a5
	add t6, t6, t2
	srli a6, t3, 28
	slli a7, t3, 36
	xor a6, a6, a7
	srli a7, t3, 34
	xor a6, a6, a7
	slli a7, t3, 30
	xor a6, a6, a7
	srli a7, t3, 39
	xor a6, a6, a7
	slli a7, t3, 25
	xor a6, a6, a7
	add t2, t2, a6
	or a6, t3, t4
	and a6, a6, t5
	and a7, t3, t4
	or a6, a6, a7
	add t2, t2, a6
	ld a6, 96(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 56(a3)
	add a5, a5, a7
	ld a6, 120(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 112(a3)
	add a5, a5, a7
	sd a5, 112(a3)
	srli a6, t6, 14
	slli a7, t6, 50
	xor a6, a6, a7
	srli a7, t6, 18
	xor a6, a6, a7
	slli a7, t6, 46
	xor a6, a6, a7
	srli a7, t6, 41
	xor a6, a6, a7
	slli a7, t6, 23
	xor a6, a6, a7
	add t1, t1, a6
	xor a6, a4, t0
	and a6, a6, t6
	xor a6, a6, t0
	add t1, t1, a6
	lui a6, 782234
	addiw a6, a6, 1016
	slli a6, a6, 32
	lui a7, 732264
	addiw a7, a7, -1771
	add a6, a6, a7
	add t1, t1, a6
	add t1, t1, a5
	add t5, t5, t1
	srli a6, t2, 28
	slli a7, t2, 36
	xor a6, a6, a7
	srli a7, t2, 34
	xor a6, a6, a7
	slli a7, t2, 30
	xor a6, a6, a7
	srli a7, t2, 39
	xor a6, a6, a7
	slli a7, t2, 25
	xor a6, a6, a7
	add t1, t1, a6
	or a6, t2, t3
	and a6, a6, t4
	and a7, t2, t3
	or a6, a6, a7
	add t1, t1, a6
	ld a6, 104(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 64(a3)
	add a5, a5, a7
	ld a6, 0(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 120(a3)
	add a5, a5, a7
	sd a5, 120(a3)
	srli a6, t5, 14
	slli a7, t5, 50
	xor a6, a6, a7
	srli a7, t5, 18
	xor a6, a6, a7
	slli a7, t5, 46
	xor a6, a6, a7
	srli a7, t5, 41
	xor a6, a6, a7
	slli a7, t5, 23
	xor a6, a6, a7
	add t0, t0, a6
	xor a6, t6, a4
	and a6, a6, t5
	xor a6, a6, a4
	add t0, t0, a6
	lui a6, 812824
	addiw a6, a6, -1805
	slli a6, a6, 32
	lui a7, 931621
	addiw a7, a7, 811
	add a6, a6, a7
	add t0, t0, a6
	add t0, t0, a5
	add t4, t4, t0
	srli a6, t1, 28
	slli a7, t1, 36
	xor a6, a6, a7
	srli a7, t1, 34
	xor a6, a6, a7
	slli a7, t1, 30
	xor a6, a6, a7
	srli a7, t1, 39
	xor a6, a6, a7
	slli a7, t1, 25
	xor a6, a6, a7
	add t0, t0, a6
	or a6, t1, t2
	and a6, a6, t3
	and a7, t1, t2
	or a6, a6, a7
	add t0, t0, a6
	ld a6, 112(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 72(a3)
	add a5, a5, a7
	ld a6, 8(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 0(a3)
	add a5, a5, a7
	sd a5, 0(a3)
	srli a6, t4, 14
	slli a7, t4, 50
	xor a6, a6, a7
	srli a7, t4, 18
	xor a6, a6, a7
	slli a7, t4, 46
	xor a6, a6, a7
	srli a7, t4, 41
	xor a6, a6, a7
	slli a7, t4, 23
	xor a6, a6, a7
	add a4, a4, a6
	xor a6, t5, t6
	and a6, a6, t4
	xor a6, a6, t6
	add a4, a4, a6
	lui a6, 828020
	addiw a6, a6, -305
	slli a6, a6, 32
	lui a7, 959078
	addiw a7, a7, 412
	add a6, a6, a7
	add a4, a4, a6
	add a4, a4, a5
	add t3, t3, a4
	srli a6, t0, 28
	slli a7, t0, 36
	xor a6, a6, a7
	srli a7, t0, 34
	xor a6, a6, a7
	slli a7, t0, 30
	xor a6, a6, a7
	srli a7, t0, 39
	xor a6, a6, a7
	slli a7, t0, 25
	xor a6, a6, a7
	add a4, a4, a6
	or a6, t0, t1
	and a6, a6, t2
	and a7, t0, t1
	or a6, a6, a7
	add a4, a4, a6
	ld a6, 120(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 80(a3)
	add a5, a5, a7
	ld a6, 16(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 8(a3)
	add a5, a5, a7
	sd a5, 8(a3)
	srli a6, t3, 14
	slli a7, t3, 50
	xor a6, a6, a7
	srli a7, t3, 18
	xor a6, a6, a7
	slli a7, t3, 46
	xor a6, a6, a7
	srli a7, t3, 41
	xor a6, a6, a7
	slli a7, t3, 23
	xor a6, a6, a7
	add t6, t6, a6
	xor a6, t4, t5
	and a6, a6, t3
	xor a6, a6, t5
	add t6, t6, a6
	lui a6, 858220
	addiw a6, a6, -1849
	slli a6, a6, 32
	lui a7, 138252
	addiw a7, a7, 519
	add a6, a6, a7
	add t6, t6, a6
	add t6, t6, a5
	add t2, t2, t6
	srli a6, a4, 28
	slli a7, a4, 36
	xor a6, a6, a7
	srli a7, a4, 34
	xor a6, a6, a7
	slli a7, a4, 30
	xor a6, a6, a7
	srli a7, a4, 39
	xor a6, a6, a7
	slli a7, a4, 25
	xor a6, a6, a7
	add t6, t6, a6
	or a6, a4, t0
	and a6, a6, t1
	and a7, a4, t0
	or a6, a6, a7
	add t6, t6, a6
	ld a6, 0(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 88(a3)
	add a5, a5, a7
	ld a6, 24(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 16(a3)
	add a5, a5, a7
	sd a5, 16(a3)
	srli a6, t2, 14
	slli a7, t2, 50
	xor a6, a6, a7
	srli a7, t2, 18
	xor a6, a6, a7
	slli a7, t2, 46
	xor a6, a6, a7
	srli a7, t2, 41
	xor a6, a6, a7
	slli a7, t2, 23
	xor a6, a6, a7
	add t5, t5, a6
	xor a6, t3, t4
	and a6, a6, t2
	xor a6, a6, t4
	add t5, t5, a6
	lui a6, 961960
	addiw a6, a6, -553
	slli a6, a6, 32
	lui a7, 843279
	addiw a7, a7, -1250
	add a6, a6, a7
	add t5, t5, a6
	add t5, t5, a5
	add t1, t1, t5
	srli a6, t6, 28
	slli a7, t6, 36
	xor a6, a6, a7
	srli a7, t6, 34
	xor a6, a6, a7
	slli a7, t6, 30
	xor a6, a6, a7
	srli a7, t6, 39
	xor a6, a6, a7
	slli a7, t6, 25
	xor a6, a6, a7
	add t5, t5, a6
	or a6, t6, a4
	and a6, a6, t0
	and a7, t6, a4
	or a6, a6, a7
	add t5, t5, a6
	ld a6, 8(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 96(a3)
	add a5, a5, a7
	ld a6, 32(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 24(a3)
	add a5, a5, a7
	sd a5, 24(a3)
	srli a6, t1, 14
	slli a7, t1, 50
	xor a6, a6, a7
	srli a7, t1, 18
	xor a6, a6, a7
	slli a7, t1, 46
	xor a6, a6, a7
	srli a7, t1, 41
	xor a6, a6, a7
	slli a7, t1, 23
	xor a6, a6, a7
	add t4, t4, a6
	xor a6, t2, t3
	and a6, a6, t1
	xor a6, a6, t3
	add t4, t4, a6
	lui a6, 1005525
	addiw a6, a6, -128
	slli a6, a6, 32
	lui a7, 976621
	addiw a7, a7, 376
	add a6, a6, a7
	add t4, t4, a6
	add t4, t4, a5
	add t0, t0, t4
	srli a6, t5, 28
	slli a7, t5, 36
	xor a6, a6, a7
	srli a7, t5, 34
	xor a6, a6, a7
	slli a7, t5, 30
	xor a6, a6, a7
	srli a7, t5, 39
	xor a6, a6, a7
	slli a7, t5, 25
	xor a6, a6, a7
	add t4, t4, a6
	or a6, t5, t6
	and a6, a6, a4
	and a7, t5, t6
	or a6, a6, a7
	add t4, t4, a6
	ld a6, 16(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 104(a3)
	add a5, a5, a7
	ld a6, 40(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 32(a3)
	add a5, a5, a7
	sd a5, 32(a3)
	srli a6, t0, 14
	slli a7, t0, 50
	xor a6, a6, a7
	srli a7, t0, 18
	xor a6, a6, a7
	slli a7, t0, 46
	xor a6, a6, a7
	srli a7, t0, 41
	xor a6, a6, a7
	slli a7, t0, 23
	xor a6, a6, a7
	add t3, t3, a6
	xor a6, t1, t2
	and a6, a6, t0
	xor a6, a6, t2
	add t3, t3, a6
	lui a6, 28422
	addiw a6, a6, 1962
	slli a6, a6, 32
	lui a7, 467319
	addiw a7, a7, -70
	add a6, a6, a7
	add t3, t3, a6
	add t3, t3, a5
	add a4, a4, t3
	srli a6, t4, 28
	slli a7, t4, 36
	xor a6, a6, a7
	srli a7, t4, 34
	xor a6, a6, a7
	slli a7, t4, 30
	xor a6, a6, a7
	srli a7, t4, 39
	xor a6, a6, a7
	slli a7, t4, 25
	xor a6, a6, a7
	add t3, t3, a6
	or a6, t4, t5
	and a6, a6, t6
	and a7, t4, t5
	or a6, a6, a7
	add t3, t3, a6
	ld a6, 24(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 112(a3)
	add a5, a5, a7
	ld a6, 48(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 40(a3)
	add a5, a5, a7
	sd a5, 40(a3)
	srli a6, a4, 14
	slli a7, a4, 50
	xor a6, a6, a7
	srli a7, a4, 18
	xor a6, a6, a7
	slli a7, a4, 46
	xor a6, a6, a7
	srli a7, a4, 41
	xor a6, a6, a7
	slli a7, a4, 23
	xor a6, a6, a7
	add t2, t2, a6
	xor a6, t0, t1
	and a6, a6, a4
	xor a6, a6, t1
	add t2, t2, a6
	lui a6, 42552
	addiw a6, a6, -570
	slli a6, a6, 32
	lui a7, 666762
	addiw a7, a7, -1882
	add a6, a6, a7
	add t2, t2, a6
	add t2, t2, a5
	add t6, t6, t2
	srli a6, t3, 28
	slli a7, t3, 36
	xor a6, a6, a7
	srli a7, t3, 34
	xor a6, a6, a7
	slli a7, t3, 30
	xor a6, a6, a7
	srli a7, t3, 39
	xor a6, a6, a7
	slli a7, t3, 25
	xor a6, a6, a7
	add t2, t2, a6
	or a6, t3, t4
	and a6, a6, t5
	and a7, t3, t4
	or a6, a6, a7
	add t2, t2, a6
	ld a6, 32(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 120(a3)
	add a5, a5, a7
	ld a6, 56(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 48(a3)
	add a5, a5, a7
	sd a5, 48(a3)
	srli a6, t6, 14
	slli a7, t6, 50
	xor a6, a6, a7
	srli a7, t6, 18
	xor a6, a6, a7
	slli a7, t6, 46
	xor a6, a6, a7
	srli a7, t6, 41
	xor a6, a6, a7
	slli a7, t6, 23
	xor a6, a6, a7
	add t1, t1, a6
	xor a6, a4, t0
	and a6, a6, t6
	xor a6, a6, t0
	add t1, t1, a6
	lui a6, 70650
	addiw a6, a6, -2043
	slli a6, a6, 32
	lui a7, 782225
	addiw a7, a7, -594
	add a6, a6, a7
	add t1, t1, a6
	add t1, t1, a5
	add t5, t5, t1
	srli a6, t2, 28
	slli a7, t2, 36
	xor a6, a6, a7
	srli a7, t2, 34
	xor a6, a6, a7
	slli a7, t2, 30
	xor a6, a6, a7
	srli a7, t2, 39
	xor a6, a6, a7
	slli a7, t2, 25
	xor a6, a6, a7
	add t1, t1, a6
	or a6, t2, t3
	and a6, a6, t4
	and a7, t2, t3
	or a6, a6, a7
	add t1, t1, a6
	ld a6, 40(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 0(a3)
	add a5, a5, a7
	ld a6, 64(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 56(a3)
	add a5, a5, a7
	sd a5, 56(a3)
	srli a6, t5, 14
	slli a7, t5, 50
	xor a6, a6, a7
	srli a7, t5, 18
	xor a6, a6, a7
	slli a7, t5, 46
	xor a6, a6, a7
	srli a7, t5, 41
	xor a6, a6, a7
	slli a7, t5, 23
	xor a6, a6, a7
	add t0, t0, a6
	xor a6, t6, a4
	and a6, a6, t5
	xor a6, a6, a4
	add t0, t0, a6
	lui a6, 112401
	addiw a6, a6, -1227
	slli a6, a6, 32
	lui a7, 78276
	addiw a7, a7, 1819
	add a6, a6, a7
	add t0, t0, a6
	add t0, t0, a5
	add t4, t4, t0
	srli a6, t1, 28
	slli a7, t1, 36
	xor a6, a6, a7
	srli a7, t1, 34
	xor a6, a6, a7
	slli a7, t1, 30
	xor a6, a6, a7
	srli a7, t1, 39
	xor a6, a6, a7
	slli a7, t1, 25
	xor a6, a6, a7
	add t0, t0, a6
	or a6, t1, t2
	and a6, a6, t3
	and a7, t1, t2
	or a6, a6, a7
	add t0, t0, a6
	ld a6, 48(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 8(a3)
	add a5, a5, a7
	ld a6, 72(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 64(a3)
	add a5, a5, a7
	sd a5, 64(a3)
	srli a6, t4, 14
	slli a7, t4, 50
	xor a6, a6, a7
	srli a7, t4, 18
	xor a6, a6, a7
	slli a7, t4, 46
	xor a6, a6, a7
	srli a7, t4, 41
	xor a6, a6, a7
	slli a7, t4, 23
	xor a6, a6, a7
	add a4, a4, a6
	xor a6, t5, t6
	and a6, a6, t4
	xor a6, a6, t6
	add a4, a4, a6
	lui a6, 167351
	addiw a6, a6, 2037
	slli a6, a6, 32
	lui a7, 143432
	addiw a7, a7, -636
	add a6, a6, a7
	add a4, a4, a6
	add a4, a4, a5
	add t3, t3, a4
	srli a6, t0, 28
	slli a7, t0, 36
	xor a6, a6, a7
	srli a7, t0, 34
	xor a6, a6, a7
	slli a7, t0, 30
	xor a6, a6, a7
	srli a7, t0, 39
	xor a6, a6, a7
	slli a7, t0, 25
	xor a6, a6, a7
	add a4, a4, a6
	or a6, t0, t1
	and a6, a6, t2
	and a7, t0, t1
	or a6, a6, a7
	add a4, a4, a6
	ld a6, 56(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 16(a3)
	add a5, a5, a7
	ld a6, 80(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 72(a3)
	add a5, a5, a7
	sd a5, 72(a3)
	srli a6, t3, 14
	slli a7, t3, 50
	xor a6, a6, a7
	srli a7, t3, 18
	xor a6, a6, a7
	slli a7, t3, 46
	xor a6, a6, a7
	srli a7, t3, 41
	xor a6, a6, a7
	slli a7, t3, 23
	xor a6, a6, a7
	add t6, t6, a6
	xor a6, t4, t5
	and a6, a6, t3
	xor a6, a6, t5
	add t6, t6, a6
	lui a6, 208043
	addiw a6, a6, -1157
	slli a6, a6, 32
	lui a7, 265330
	addiw a7, a7, 1171
	add a6, a6, a7
	add t6, t6, a6
	add t6, t6, a5
	add t2, t2, t6
	srli a6, a4, 28
	slli a7, a4, 36
	xor a6, a6, a7
	srli a7, a4, 34
	xor a6, a6, a7
	slli a7, a4, 30
	xor a6, a6, a7
	srli a7, a4, 39
	xor a6, a6, a7
	slli a7, a4, 25
	xor a6, a6, a7
	add t6, t6, a6
	or a6, a4, t0
	and a6, a6, t1
	and a7, a4, t0
	or a6, a6, a7
	add t6, t6, a6
	ld a6, 64(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 24(a3)
	add a5, a5, a7
	ld a6, 88(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 80(a3)
	add a5, a5, a7
	sd a5, 80(a3)
	srli a6, t2, 14
	slli a7, t2, 50
	xor a6, a6, a7
	srli a7, t2, 18
	xor a6, a6, a7
	slli a7, t2, 46
	xor a6, a6, a7
	srli a7, t2, 41
	xor a6, a6, a7
	slli a7, t2, 23
	xor a6, a6, a7
	add t5, t5, a6
	xor a6, t3, t4
	and a6, a6, t2
	xor a6, a6, t4
	add t5, t5, a6
	lui a6, 248300
	addiw a6, a6, -502
	slli a6, a6, 32
	lui a7, 89244
	addiw a7, a7, -324
	add a6, a6, a7
	add t5, t5, a6
	add t5, t5, a5
	add t1, t1, t5
	srli a6, t6, 28
	slli a7, t6, 36
	xor a6, a6, a7
	srli a7, t6, 34
	xor a6, a6, a7
	slli a7, t6, 30
	xor a6, a6, a7
	srli a7, t6, 39
	xor a6, a6, a7
	slli a7, t6, 25
	xor a6, a6, a7
	add t5, t5, a6
	or a6, t6, a4
	and a6, a6, t0
	and a7, t6, a4
	or a6, a6, a7
	add t5, t5, a6
	ld a6, 72(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 32(a3)
	add a5, a5, a7
	ld a6, 96(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 88(a3)
	add a5, a5, a7
	sd a5, 88(a3)
	srli a6, t1, 14
	slli a7, t1, 50
	xor a6, a6, a7
	srli a7, t1, 18
	xor a6, a6, a7
	slli a7, t1, 46
	xor a6, a6, a7
	srli a7, t1, 41
	xor a6, a6, a7
	slli a7, t1, 23
	xor a6, a6, a7
	add t4, t4, a6
	xor a6, t2, t3
	and a6, a6, t1
	xor a6, a6, t3
	add t4, t4, a6
	lui a6, 274902
	addiw a6, a6, 1989
	slli a6, a6, 32
	lui a7, 639233
	addiw a7, a7, -692
	add a6, a6, a7
	add t4, t4, a6
	add t4, t4, a5
	add t0, t0, t4
	srli a6, t5, 28
	slli a7, t5, 36
	xor a6, a6, a7
	srli a7, t5, 34
	xor a6, a6, a7
	slli a7, t5, 30
	xor a6, a6, a7
	srli a7, t5, 39
	xor a6, a6, a7
	slli a7, t5, 25
	xor a6, a6, a7
	add t4, t4, a6
	or a6, t5, t6
	and a6, a6, a4
	and a7, t5, t6
	or a6, a6, a7
	add t4, t4, a6
	ld a6, 80(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 40(a3)
	add a5, a5, a7
	ld a6, 104(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 96(a3)
	add a5, a5, a7
	sd a5, 96(a3)
	srli a6, t0, 14
	slli a7, t0, 50
	xor a6, a6, a7
	srli a7, t0, 18
	xor a6, a6, a7
	slli a7, t0, 46
	xor a6, a6, a7
	srli a7, t0, 41
	xor a6, a6, a7
	slli a7, t0, 23
	xor a6, a6, a7
	add t3, t3, a6
	xor a6, t1, t2
	and a6, a6, t0
	xor a6, a6, t2
	add t3, t3, a6
	lui a6, 314461
	addiw a6, a6, 1215
	slli a6, a6, 32
	lui a7, 832484
	addiw a7, a7, 694
	add a6, a6, a7
	add t3, t3, a6
	add t3, t3, a5
	add a4, a4, t3
	srli a6, t4, 28
	slli a7, t4, 36
	xor a6, a6, a7
	srli a7, t4, 34
	xor a6, a6, a7
	slli a7, t4, 30
	xor a6, a6, a7
	srli a7, t4, 39
	xor a6, a6, a7
	slli a7, t4, 25
	xor a6, a6, a7
	add t3, t3, a6
	or a6, t4, t5
	and a6, a6, t6
	and a7, t4, t5
	or a6, a6, a7
	add t3, t3, a6
	ld a6, 88(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 48(a3)
	add a5, a5, a7
	ld a6, 112(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 104(a3)
	add a5, a5, a7
	sd a5, 104(a3)
	srli a6, a4, 14
	slli a7, a4, 50
	xor a6, a6, a7
	srli a7, a4, 18
	xor a6, a6, a7
	slli a7, a4, 46
	xor a6, a6, a7
	srli a7, a4, 41
	xor a6, a6, a7
	slli a7, a4, 23
	xor a6, a6, a7
	add t2, t2, a6
	xor a6, t0, t1
	and a6, a6, a4
	xor a6, a6, t1
	add t2, t2, a6
	lui a6, 366579
	addiw a6, a6, -1635
	slli a6, a6, 32
	lui a7, 1033816
	addiw a7, a7, -470
	add a6, a6, a7
	add t2, t2, a6
	add t2, t2, a5
	add t6, t6, t2
	srli a6, t3, 28
	slli a7, t3, 36
	xor a6, a6, a7
	srli a7, t3, 34
	xor a6, a6, a7
	slli a7, t3, 30
	xor a6, a6, a7
	srli a7, t3, 39
	xor a6, a6, a7
	slli a7, t3, 25
	xor a6, a6, a7
	add t2, t2, a6
	or a6, t3, t4
	and a6, a6, t5
	and a7, t3, t4
	or a6, a6, a7
	add t2, t2, a6
	ld a6, 96(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 56(a3)
	add a5, a5, a7
	ld a6, 120(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 112(a3)
	add a5, a5, a7
	sd a5, 112(a3)
	srli a6, t6, 14
	slli a7, t6, 50
	xor a6, a6, a7
	srli a7, t6, 18
	xor a6, a6, a7
	slli a7, t6, 46
	xor a6, a6, a7
	srli a7, t6, 41
	xor a6, a6, a7
	slli a7, t6, 23
	xor a6, a6, a7
	add t1, t1, a6
	xor a6, a4, t0
	and a6, a6, t6
	xor a6, a6, t0
	add t1, t1, a6
	lui a6, 392375
	addiw a6, a6, -85
	slli a6, a6, 32
	lui a7, 241008
	addiw a7, a7, -1300
	add a6, a6, a7
	add t1, t1, a6
	add t1, t1, a5
	add t5, t5, t1
	srli a6, t2, 28
	slli a7, t2, 36
	xor a6, a6, a7
	srli a7, t2, 34
	xor a6, a6, a7
	slli a7, t2, 30
	xor a6, a6, a7
	srli a7, t2, 39
	xor a6, a6, a7
	slli a7, t2, 25
	xor a6, a6, a7
	add t1, t1, a6
	or a6, t2, t3
	and a6, a6, t4
	and a7, t2, t3
	or a6, a6, a7
	add t1, t1, a6
	ld a6, 104(a3)
	srli a5, a6, 19
	slli a7, a6, 45
	xor a5, a5, a7
	srli a7, a6, 61
	xor a5, a5, a7
	slli a7, a6, 3
	xor a5, a5, a7
	srli a7, a6, 6
	xor a5, a5, a7
	ld a7, 64(a3)
	add a5, a5, a7
	ld a6, 0(a3)
	srli a7, a6, 1
	slli s0, a6, 63
	xor a7, a7, s0
	srli s0, a6, 8
	xor a7, a7, s0
	slli s0, a6, 56
	xor a7, a7, s0
	srli s0, a6, 7
	xor a7, a7, s0
	add a5, a5, a7
	ld a7, 120(a3)
	add a5, a5, a7
	sd a5, 120(a3)
	srli a6, t5, 14
	slli a7, t5, 50
	xor a6, a6, a7
	srli a7, t5, 18
	xor a6, a6, a7
	slli a7, t5, 46
	xor a6, a6, a7
	srli a7, t5, 41
	xor a6, a6, a7
	slli a7, t5, 23
	xor a6, a6, a7
	add t0, t0, a6
	xor a6, t6, a4
	and a6, a6, t5
	xor a6, a6, a4
	add t0, t0, a6
	lui a6, 443458
	addiw a6, a6, -1652
	slli a6, a6, 32
	lui a7, 304246
	addiw a7, a7, -2025
	add a6, a6, a7
	add t0, t0, a6
	add t0, t0, a5
	add t4, t4, t0
	srli a6, t1, 28
	slli a7, t1, 36
	xor a6, a6, a7
	srli a7, t1, 34
	xor a6, a6, a7
	slli a7, t1, 30
	xor a6, a6, a7
	srli a7, t1, 39
	xor a6, a6, a7
	slli a7, t1, 25
	xor a6, a6, a7
	add t0, t0, a6
	or a6, t1, t2
	and a6, a6, t3
	and a7, t1, t2
	or a6, a6, a7
	add t0, t0, a6
	lbu a5, 0(a0)
	lbu a6, 1(a0)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 2(a0)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 3(a0)
	slli a6, a6, 24
	or a5, a5, a6
	lbu a7, 4(a0)
	lbu a6, 5(a0)
	slli a6, a6, 8
	or a7, a7, a6
	lbu a6, 6(a0)
	slli a6, a6, 16
	or a7, a7, a6
	lbu a6, 7(a0)
	slli a6, a6, 24
	or a7, a7, a6
	slli a7, a7, 32
	or a5, a5, a7
	add t0, t0, a5
	sb t0, 0(a0)
	srli a5, t0, 8
	sb a5, 1(a0)
	srli a5, t0, 16
	sb a5, 2(a0)
	srli a5, t0, 24
	sb a5, 3(a0)
	srli a5, t0, 32
	sb a5, 4(a0)
	srli a6, a5, 8
	sb a6, 5(a0)
	srli a6, a5, 16
	sb a6, 6(a0)
	srli a6, a5, 24
	sb a6, 7(a0)
	lbu a5, 8(a0)
	lbu a6, 9(a0)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 10(a0)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 11(a0)
	slli a6, a6, 24
	or a5, a5, a6
	lbu a7, 12(a0)
	lbu a6, 13(a0)
	slli a6, a6, 8
	or a7, a7, a6
	lbu a6, 14(a0)
	slli a6, a6, 16
	or a7, a7, a6
	lbu a6, 15(a0)
	slli a6, a6, 24
	or a7, a7, a6
	slli a7, a7, 32
	or a5, a5, a7
	add t1, t1, a5
	sb t1, 8(a0)
	srli a5, t1, 8
	sb a5, 9(a0)
	srli a5, t1, 16
	sb a5, 10(a0)
	srli a5, t1, 24
	sb a5, 11(a0)
	srli a5, t1, 32
	sb a5, 12(a0)
	srli a6, a5, 8
	sb a6, 13(a0)
	srli a6, a5, 16
	sb a6, 14(a0)
	srli a6, a5, 24
	sb a6, 15(a0)
	lbu a5, 16(a0)
	lbu a6, 17(a0)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 18(a0)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 19(a0)
	slli a6, a6, 24
	or a5, a5, a6
	lbu a7, 20(a0)
	lbu a6, 21(a0)
	slli a6, a6, 8
	or a7, a7, a6
	lbu a6, 22(a0)
	slli a6, a6, 16
	or a7, a7, a6
	lbu a6, 23(a0)
	slli a6, a6, 24
	or a7, a7, a6
	slli a7, a7, 32
	or a5, a5, a7
	add t2, t2, a5
	sb t2, 16(a0)
	srli a5, t2, 8
	sb a5, 17(a0)
	srli a5, t2, 16
	sb a5, 18(a0)
	srli a5, t2, 24
	sb a5, 19(a0)
	srli a5, t2, 32
	sb a5, 20(a0)
	srli a6, a5, 8
	sb a6, 21(a0)
	srli a6, a5, 16
	sb a6, 22(a0)
	srli a6, a5, 24
	sb a6, 23(a0)
	lbu a5, 24(a0)
	lbu a6, 25(a0)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 26(a0)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 27(a0)
	slli a6, a6, 24
	or a5, a5, a6
	lbu a7, 28(a0)
	lbu a6, 29(a0)
	slli a6, a6, 8
	or a7, a7, a6
	lbu a6, 30(a0)
	slli a6, a6, 16
	or a7, a7, a6
	lbu a6, 31(a0)
	slli a6, a6, 24
	or a7, a7, a6
	slli a7, a7, 32
	or a5, a5, a7
	add t3, t3, a5
	sb t3, 24(a0)
	srli a5, t3, 8
	sb a5, 25(a0)
	srli a5, t3, 16
	sb a5, 26(a0)
	srli a5, t3, 24
	sb a5, 27(a0)
	srli a5, t3, 32
	sb a5, 28(a0)
	srli a6, a5, 8
	sb a6, 29(a0)
	srli a6, a5, 16
	sb a6, 30(a0)
	srli a6, a5, 24
	sb a6, 31(a0)
	lbu a5, 32(a0)
	lbu a6, 33(a0)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 34(a0)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 35(a0)
	slli a6, a6, 24
	or a5, a5, a6
	lbu a7, 36(a0)
	lbu a6, 37(a0)
	slli a6, a6, 8
	or a7, a7, a6
	lbu a6, 38(a0)
	slli a6, a6, 16
	or a7, a7, a6
	lbu a6, 39(a0)
	slli a6, a6, 24
	or a7, a7, a6
	slli a7, a7, 32
	or a5, a5, a7
	add t4, t4, a5
	sb t4, 32(a0)
	srli a5, t4, 8
	sb a5, 33(a0)
	srli a5, t4, 16
	sb a5, 34(a0)
	srli a5, t4, 24
	sb a5, 35(a0)
	srli a5, t4, 32
	sb a5, 36(a0)
	srli a6, a5, 8
	sb a6, 37(a0)
	srli a6, a5, 16
	sb a6, 38(a0)
	srli a6, a5, 24
	sb a6, 39(a0)
	lbu a5, 40(a0)
	lbu a6, 41(a0)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 42(a0)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 43(a0)
	slli a6, a6, 24
	or a5, a5, a6
	lbu a7, 44(a0)
	lbu a6, 45(a0)
	slli a6, a6, 8
	or a7, a7, a6
	lbu a6, 46(a0)
	slli a6, a6, 16
	or a7, a7, a6
	lbu a6, 47(a0)
	slli a6, a6, 24
	or a7, a7, a6
	slli a7, a7, 32
	or a5, a5, a7
	add t5, t5, a5
	sb t5, 40(a0)
	srli a5, t5, 8
	sb a5, 41(a0)
	srli a5, t5, 16
	sb a5, 42(a0)
	srli a5, t5, 24
	sb a5, 43(a0)
	srli a5, t5, 32
	sb a5, 44(a0)
	srli a6, a5, 8
	sb a6, 45(a0)
	srli a6, a5, 16
	sb a6, 46(a0)
	srli a6, a5, 24
	sb a6, 47(a0)
	lbu a5, 48(a0)
	lbu a6, 49(a0)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 50(a0)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 51(a0)
	slli a6, a6, 24
	or a5, a5, a6
	lbu a7, 52(a0)
	lbu a6, 53(a0)
	slli a6, a6, 8
	or a7, a7, a6
	lbu a6, 54(a0)
	slli a6, a6, 16
	or a7, a7, a6
	lbu a6, 55(a0)
	slli a6, a6, 24
	or a7, a7, a6
	slli a7, a7, 32
	or a5, a5, a7
	add t6, t6, a5
	sb t6, 48(a0)
	srli a5, t6, 8
	sb a5, 49(a0)
	srli a5, t6, 16
	sb a5, 50(a0)
	srli a5, t6, 24
	sb a5, 51(a0)
	srli a5, t6, 32
	sb a5, 52(a0)
	srli a6, a5, 8
	sb a6, 53(a0)
	srli a6, a5, 16
	sb a6, 54(a0)
	srli a6, a5, 24
	sb a6, 55(a0)
	lbu a5, 56(a0)
	lbu a6, 57(a0)
	slli a6, a6, 8
	or a5, a5, a6
	lbu a6, 58(a0)
	slli a6, a6, 16
	or a5, a5, a6
	lbu a6, 59(a0)
	slli a6, a6, 24
	or a5, a5, a6
	lbu a7, 60(a0)
	lbu a6, 61(a0)
	slli a6, a6, 8
	or a7, a7, a6
	lbu a6, 62(a0)
	slli a6, a6, 16
	or a7, a7, a6
	lbu a6, 63(a0)
	slli a6, a6, 24
	or a7, a7, a6
	slli a7, a7, 32
	or a5, a5, a7
	add a4, a4, a5
	sb a4, 56(a0)
	srli a5, a4, 8
	sb a5, 57(a0)
	srli a5, a4, 16
	sb a5, 58(a0)
	srli a5, a4, 24
	sb a5, 59(a0)
	srli a5, a4, 32
	sb a5, 60(a0)
	srli a6, a5, 8
	sb a6, 61(a0)
	srli a6, a5, 16
	sb a6, 62(a0)
	srli a6, a5, 24
	sb a6, 63(a0)
	addi a1, a1, 128
	addi a2, a2, -1
	bnez a2, 22b
	j 21f
20:
21:
	ld s0, 128(a3)
	ret
	.option pop

vg_sha384_init:
	.option push
	.option arch, +m, +c
	lui t0, 834490
	addiw t0, t0, -674
	slli t0, t0, 32
	lui t1, 790618
	addiw t1, t1, -296
	add t0, t0, t1
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	srli t1, t0, 32
	sb t1, 4(a0)
	srli t2, t1, 8
	sb t2, 5(a0)
	srli t2, t1, 16
	sb t2, 6(a0)
	srli t2, t1, 24
	sb t2, 7(a0)
	lui t0, 403875
	addiw t0, t0, -1750
	slli t0, t0, 32
	lui t1, 223181
	addiw t1, t1, 1287
	add t0, t0, t1
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	srli t1, t0, 32
	sb t1, 12(a0)
	srli t2, t1, 8
	sb t2, 13(a0)
	srli t2, t1, 16
	sb t2, 14(a0)
	srli t2, t1, 24
	sb t2, 15(a0)
	lui t0, 595344
	addiw t0, t0, 346
	slli t0, t0, 32
	lui t1, 198414
	addiw t1, t1, -745
	add t0, t0, t1
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	srli t1, t0, 32
	sb t1, 20(a0)
	srli t2, t1, 8
	sb t2, 21(a0)
	srli t2, t1, 16
	sb t2, 22(a0)
	srli t2, t1, 24
	sb t2, 23(a0)
	lui t0, 86783
	addiw t0, t0, -807
	slli t0, t0, 32
	lui t1, 1011942
	addiw t1, t1, -1735
	add t0, t0, t1
	sb t0, 24(a0)
	srli t1, t0, 8
	sb t1, 25(a0)
	srli t1, t0, 16
	sb t1, 26(a0)
	srli t1, t0, 24
	sb t1, 27(a0)
	srli t1, t0, 32
	sb t1, 28(a0)
	srli t2, t1, 8
	sb t2, 29(a0)
	srli t2, t1, 16
	sb t2, 30(a0)
	srli t2, t1, 24
	sb t2, 31(a0)
	lui t0, 422706
	addiw t0, t0, 1640
	slli t0, t0, 32
	lui t1, 1047553
	addiw t1, t1, -1231
	add t0, t0, t1
	sb t0, 32(a0)
	srli t1, t0, 8
	sb t1, 33(a0)
	srli t1, t0, 16
	sb t1, 34(a0)
	srli t1, t0, 24
	sb t1, 35(a0)
	srli t1, t0, 32
	sb t1, 36(a0)
	srli t2, t1, 8
	sb t2, 37(a0)
	srli t2, t1, 16
	sb t2, 38(a0)
	srli t2, t1, 24
	sb t2, 39(a0)
	lui t0, 584517
	addiw t0, t0, -1401
	slli t0, t0, 32
	lui t1, 427393
	addiw t1, t1, 1297
	add t0, t0, t1
	sb t0, 40(a0)
	srli t1, t0, 8
	sb t1, 41(a0)
	srli t1, t0, 16
	sb t1, 42(a0)
	srli t1, t0, 24
	sb t1, 43(a0)
	srli t1, t0, 32
	sb t1, 44(a0)
	srli t2, t1, 8
	sb t2, 45(a0)
	srli t2, t1, 16
	sb t2, 46(a0)
	srli t2, t1, 24
	sb t2, 47(a0)
	lui t0, 897219
	addiw t0, t0, -499
	slli t0, t0, 32
	lui t1, 413593
	addiw t1, t1, -89
	add t0, t0, t1
	sb t0, 48(a0)
	srli t1, t0, 8
	sb t1, 49(a0)
	srli t1, t0, 16
	sb t1, 50(a0)
	srli t1, t0, 24
	sb t1, 51(a0)
	srli t1, t0, 32
	sb t1, 52(a0)
	srli t2, t1, 8
	sb t2, 53(a0)
	srli t2, t1, 16
	sb t2, 54(a0)
	srli t2, t1, 24
	sb t2, 55(a0)
	lui t0, 293717
	addiw t0, t0, -2018
	slli t0, t0, 32
	lui t1, 782245
	addiw t1, t1, -92
	add t0, t0, t1
	sb t0, 56(a0)
	srli t1, t0, 8
	sb t1, 57(a0)
	srli t1, t0, 16
	sb t1, 58(a0)
	srli t1, t0, 24
	sb t1, 59(a0)
	srli t1, t0, 32
	sb t1, 60(a0)
	srli t2, t1, 8
	sb t2, 61(a0)
	srli t2, t1, 16
	sb t2, 62(a0)
	srli t2, t1, 24
	sb t2, 63(a0)
	ret
	.option pop

vg_sha512_init:
	.option push
	.option arch, +m, +c
	lui t0, 434334
	addiw t0, t0, 1640
	slli t0, t0, 32
	lui t1, 998349
	addiw t1, t1, -1784
	add t0, t0, t1
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	srli t1, t0, 32
	sb t1, 4(a0)
	srli t2, t1, 8
	sb t2, 5(a0)
	srli t2, t1, 16
	sb t2, 6(a0)
	srli t2, t1, 24
	sb t2, 7(a0)
	lui t0, 767611
	addiw t0, t0, -378
	slli t0, t0, 32
	lui t1, 543914
	addiw t1, t1, 1851
	add t0, t0, t1
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	srli t1, t0, 32
	sb t1, 12(a0)
	srli t2, t1, 8
	sb t2, 13(a0)
	srli t2, t1, 16
	sb t2, 14(a0)
	srli t2, t1, 24
	sb t2, 15(a0)
	lui t0, 247535
	addiw t0, t0, 883
	slli t0, t0, 32
	lui t1, 1042768
	addiw t1, t1, -2005
	add t0, t0, t1
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	srli t1, t0, 32
	sb t1, 20(a0)
	srli t2, t1, 8
	sb t2, 21(a0)
	srli t2, t1, 16
	sb t2, 22(a0)
	srli t2, t1, 24
	sb t2, 23(a0)
	lui t0, 677119
	addiw t0, t0, 1338
	slli t0, t0, 32
	lui t1, 389587
	addiw t1, t1, 1777
	add t0, t0, t1
	sb t0, 24(a0)
	srli t1, t0, 8
	sb t1, 25(a0)
	srli t1, t0, 16
	sb t1, 26(a0)
	srli t1, t0, 24
	sb t1, 27(a0)
	srli t1, t0, 32
	sb t1, 28(a0)
	srli t2, t1, 8
	sb t2, 29(a0)
	srli t2, t1, 16
	sb t2, 30(a0)
	srli t2, t1, 24
	sb t2, 31(a0)
	lui t0, 332005
	addiw t0, t0, 640
	slli t0, t0, 32
	lui t1, 712296
	addiw t1, t1, 721
	add t0, t0, t1
	sb t0, 32(a0)
	srli t1, t0, 8
	sb t1, 33(a0)
	srli t1, t0, 16
	sb t1, 34(a0)
	srli t1, t0, 24
	sb t1, 35(a0)
	srli t1, t0, 32
	sb t1, 36(a0)
	srli t2, t1, 8
	sb t2, 37(a0)
	srli t2, t1, 16
	sb t2, 38(a0)
	srli t2, t1, 24
	sb t2, 39(a0)
	lui t0, 634967
	addiw t0, t0, -1908
	slli t0, t0, 32
	lui t1, 177127
	addiw t1, t1, -993
	add t0, t0, t1
	sb t0, 40(a0)
	srli t1, t0, 8
	sb t1, 41(a0)
	srli t1, t0, 16
	sb t1, 42(a0)
	srli t1, t0, 24
	sb t1, 43(a0)
	srli t1, t0, 32
	sb t1, 44(a0)
	srli t2, t1, 8
	sb t2, 45(a0)
	srli t2, t1, 16
	sb t2, 46(a0)
	srli t2, t1, 24
	sb t2, 47(a0)
	lui t0, 129086
	addiw t0, t0, -1620
	slli t0, t0, 32
	lui t1, 1029148
	addiw t1, t1, -661
	add t0, t0, t1
	sb t0, 48(a0)
	srli t1, t0, 8
	sb t1, 49(a0)
	srli t1, t0, 16
	sb t1, 50(a0)
	srli t1, t0, 24
	sb t1, 51(a0)
	srli t1, t0, 32
	sb t1, 52(a0)
	srli t2, t1, 8
	sb t2, 53(a0)
	srli t2, t1, 16
	sb t2, 54(a0)
	srli t2, t1, 24
	sb t2, 55(a0)
	lui t0, 376333
	addiw t0, t0, -743
	slli t0, t0, 32
	lui t1, 79842
	addiw t1, t1, 377
	add t0, t0, t1
	sb t0, 56(a0)
	srli t1, t0, 8
	sb t1, 57(a0)
	srli t1, t0, 16
	sb t1, 58(a0)
	srli t1, t0, 24
	sb t1, 59(a0)
	srli t1, t0, 32
	sb t1, 60(a0)
	srli t2, t1, 8
	sb t2, 61(a0)
	srli t2, t1, 16
	sb t2, 62(a0)
	srli t2, t1, 24
	sb t2, 63(a0)
	ret
	.option pop

vg_sha512_224_init:
	.option push
	.option arch, +m, +c
	lui t0, 574419
	addiw t0, t0, 1992
	slli t0, t0, 32
	lui t1, 103749
	addiw t1, t1, -606
	add t0, t0, t1
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	srli t1, t0, 32
	sb t1, 4(a0)
	srli t2, t1, 8
	sb t2, 5(a0)
	srli t2, t1, 16
	sb t2, 6(a0)
	srli t2, t1, 24
	sb t2, 7(a0)
	lui t0, 474650
	addiw t0, t0, -1689
	slli t0, t0, 32
	lui t1, 564685
	addiw t1, t1, 1238
	add t0, t0, t1
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	srli t1, t0, 32
	sb t1, 12(a0)
	srli t2, t1, 8
	sb t2, 13(a0)
	srli t2, t1, 16
	sb t2, 14(a0)
	srli t2, t1, 24
	sb t2, 15(a0)
	lui t0, 122795
	addiw t0, t0, 1966
	slli t0, t0, 32
	lui t1, 208890
	addiw t1, t1, -894
	add t0, t0, t1
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	srli t1, t0, 32
	sb t1, 20(a0)
	srli t2, t1, 8
	sb t2, 21(a0)
	srli t2, t1, 16
	sb t2, 22(a0)
	srli t2, t1, 24
	sb t2, 23(a0)
	lui t0, 424413
	addiw t0, t0, 1300
	slli t0, t0, 32
	lui t1, 361210
	addiw t1, t1, -49
	add t0, t0, t1
	sb t0, 24(a0)
	srli t1, t0, 8
	sb t1, 25(a0)
	srli t1, t0, 16
	sb t1, 26(a0)
	srli t1, t0, 24
	sb t1, 27(a0)
	srli t1, t0, 32
	sb t1, 28(a0)
	srli t2, t1, 8
	sb t2, 29(a0)
	srli t2, t1, 16
	sb t2, 30(a0)
	srli t2, t1, 24
	sb t2, 31(a0)
	lui t0, 63187
	addiw t0, t0, -1175
	slli t0, t0, 32
	lui t1, 507205
	addiw t1, t1, -600
	add t0, t0, t1
	sb t0, 32(a0)
	srli t1, t0, 8
	sb t1, 33(a0)
	srli t1, t0, 16
	sb t1, 34(a0)
	srli t1, t0, 24
	sb t1, 35(a0)
	srli t1, t0, 32
	sb t1, 36(a0)
	srli t2, t1, 8
	sb t2, 37(a0)
	srli t2, t1, 16
	sb t2, 38(a0)
	srli t2, t1, 24
	sb t2, 39(a0)
	lui t0, 491063
	addiw t0, t0, -141
	slli t0, t0, 32
	lui t1, 19529
	addiw t1, t1, -1726
	add t0, t0, t1
	sb t0, 40(a0)
	srli t1, t0, 8
	sb t1, 41(a0)
	srli t1, t0, 16
	sb t1, 42(a0)
	srli t1, t0, 24
	sb t1, 43(a0)
	srli t1, t0, 32
	sb t1, 44(a0)
	srli t2, t1, 8
	sb t2, 45(a0)
	srli t2, t1, 16
	sb t2, 46(a0)
	srli t2, t1, 24
	sb t2, 47(a0)
	lui t0, 260568
	addiw t0, t0, 1448
	slli t0, t0, 32
	lui t1, 434643
	addiw t1, t1, 1736
	add t0, t0, t1
	sb t0, 48(a0)
	srli t1, t0, 8
	sb t1, 49(a0)
	srli t1, t0, 16
	sb t1, 50(a0)
	srli t1, t0, 24
	sb t1, 51(a0)
	srli t1, t0, 32
	sb t1, 52(a0)
	srli t2, t1, 8
	sb t2, 53(a0)
	srli t2, t1, 16
	sb t2, 54(a0)
	srli t2, t1, 24
	sb t2, 55(a0)
	lui t0, 69934
	addiw t0, t0, 1710
	slli t0, t0, 32
	lui t1, 597353
	addiw t1, t1, 673
	add t0, t0, t1
	sb t0, 56(a0)
	srli t1, t0, 8
	sb t1, 57(a0)
	srli t1, t0, 16
	sb t1, 58(a0)
	srli t1, t0, 24
	sb t1, 59(a0)
	srli t1, t0, 32
	sb t1, 60(a0)
	srli t2, t1, 8
	sb t2, 61(a0)
	srli t2, t1, 16
	sb t2, 62(a0)
	srli t2, t1, 24
	sb t2, 63(a0)
	ret
	.option pop

vg_sha512_256_init:
	.option push
	.option arch, +m, +c
	lui t0, 140050
	addiw t0, t0, 405
	slli t0, t0, 32
	lui t1, 1032895
	addiw t1, t1, 1836
	add t0, t0, t1
	sb t0, 0(a0)
	srli t1, t0, 8
	sb t1, 1(a0)
	srli t1, t0, 16
	sb t1, 2(a0)
	srli t1, t0, 24
	sb t1, 3(a0)
	srli t1, t0, 32
	sb t1, 4(a0)
	srli t2, t1, 8
	sb t2, 5(a0)
	srli t2, t1, 16
	sb t2, 6(a0)
	srli t2, t1, 24
	sb t2, 7(a0)
	lui t0, 652630
	addiw t0, t0, -92
	slli t0, t0, 32
	lui t1, 820422
	addiw t1, t1, 1218
	add t0, t0, t1
	sb t0, 8(a0)
	srli t1, t0, 8
	sb t1, 9(a0)
	srli t1, t0, 16
	sb t1, 10(a0)
	srli t1, t0, 24
	sb t1, 11(a0)
	srli t1, t0, 32
	sb t1, 12(a0)
	srli t2, t1, 8
	sb t2, 13(a0)
	srli t2, t1, 16
	sb t2, 14(a0)
	srli t2, t1, 24
	sb t2, 15(a0)
	lui t0, 145724
	addiw t0, t0, -1941
	slli t0, t0, 32
	lui t1, 455995
	addiw t1, t1, 337
	add t0, t0, t1
	sb t0, 16(a0)
	srli t1, t0, 8
	sb t1, 17(a0)
	srli t1, t0, 16
	sb t1, 18(a0)
	srli t1, t0, 24
	sb t1, 19(a0)
	srli t1, t0, 32
	sb t1, 20(a0)
	srli t2, t1, 8
	sb t2, 21(a0)
	srli t2, t1, 16
	sb t2, 22(a0)
	srli t2, t1, 24
	sb t2, 23(a0)
	lui t0, 615303
	addiw t0, t0, 1817
	slli t0, t0, 32
	lui t1, 365583
	addiw t1, t1, -1347
	add t0, t0, t1
	sb t0, 24(a0)
	srli t1, t0, 8
	sb t1, 25(a0)
	srli t1, t0, 16
	sb t1, 26(a0)
	srli t1, t0, 24
	sb t1, 27(a0)
	srli t1, t0, 32
	sb t1, 28(a0)
	srli t2, t1, 8
	sb t2, 29(a0)
	srli t2, t1, 16
	sb t2, 30(a0)
	srli t2, t1, 24
	sb t2, 31(a0)
	lui t0, 615044
	addiw t0, t0, -285
	slli t0, t0, 32
	lui t1, 690416
	addiw t1, t1, -29
	add t0, t0, t1
	sb t0, 32(a0)
	srli t1, t0, 8
	sb t1, 33(a0)
	srli t1, t0, 16
	sb t1, 34(a0)
	srli t1, t0, 24
	sb t1, 35(a0)
	srli t1, t0, 32
	sb t1, 36(a0)
	srli t2, t1, 8
	sb t2, 37(a0)
	srli t2, t1, 16
	sb t2, 38(a0)
	srli t2, t1, 24
	sb t2, 39(a0)
	lui t0, 779746
	addiw t0, t0, -475
	slli t0, t0, 32
	lui t1, 342116
	addiw t1, t1, -1646
	add t0, t0, t1
	sb t0, 40(a0)
	srli t1, t0, 8
	sb t1, 41(a0)
	srli t1, t0, 16
	sb t1, 42(a0)
	srli t1, t0, 24
	sb t1, 43(a0)
	srli t1, t0, 32
	sb t1, 44(a0)
	srli t2, t1, 8
	sb t2, 45(a0)
	srli t2, t1, 16
	sb t2, 46(a0)
	srli t2, t1, 24
	sb t2, 47(a0)
	lui t0, 176154
	addiw t0, t0, -1540
	slli t0, t0, 32
	lui t1, 182364
	addiw t1, t1, -1878
	add t0, t0, t1
	sb t0, 48(a0)
	srli t1, t0, 8
	sb t1, 49(a0)
	srli t1, t0, 16
	sb t1, 50(a0)
	srli t1, t0, 24
	sb t1, 51(a0)
	srli t1, t0, 32
	sb t1, 52(a0)
	srli t2, t1, 8
	sb t2, 53(a0)
	srli t2, t1, 16
	sb t2, 54(a0)
	srli t2, t1, 24
	sb t2, 55(a0)
	lui t0, 60275
	addiw t0, t0, -547
	slli t0, t0, 32
	lui t1, 531539
	addiw t1, t1, -862
	add t0, t0, t1
	sb t0, 56(a0)
	srli t1, t0, 8
	sb t1, 57(a0)
	srli t1, t0, 16
	sb t1, 58(a0)
	srli t1, t0, 24
	sb t1, 59(a0)
	srli t1, t0, 32
	sb t1, 60(a0)
	srli t2, t1, 8
	sb t2, 61(a0)
	srli t2, t1, 16
	sb t2, 62(a0)
	srli t2, t1, 24
	sb t2, 63(a0)
	ret
	.option pop

vg_sha512_update:
	.option push
	.option arch, +m, +c
	addi sp, sp, -208
	addi t0, sp, 0
	sd ra, 144(t0)
	sd s1, 152(t0)
	sd s2, 160(t0)
	sd s3, 168(t0)
	sd s4, 176(t0)
	sd s5, 184(t0)
	sd s6, 192(t0)
	addi s1, a0, 0
	addi s2, t0, 0
	addi s3, a2, 0
	addi s4, a3, 0
	andi s5, a1, 127
	beqz s4, 20f
22:
	addi t0, zero, 0
	beqz s5, 23f
	addi t2, zero, 128
	sub t2, t2, s5
	srli t1, s4, 7
	beqz t1, 25f
	j 26f
25:
	add t1, s4, s5
	srli t1, t1, 7
	beqz t1, 27f
	j 28f
27:
	addi t2, s4, 0
28:
26:
	sub s4, s4, t2
29:
	lbu t1, 0(s3)
	add t3, s1, s5
	sb t1, 64(t3)
	addi s3, s3, 1
	addi s5, s5, 1
	addi t2, t2, -1
	bnez t2, 29b
	addi t1, s5, -128
	beqz t1, 210f
	j 211f
210:
	addi a1, s1, 64
	addi s5, zero, 0
	addi t0, zero, 1
211:
	j 24f
23:
	srli t1, s4, 7
	beqz t1, 212f
	addi a1, s3, 0
	addi s3, s3, 128
	addi s4, s4, -128
	addi t0, zero, 1
	j 213f
212:
	addi t2, zero, 128
	sub t2, t2, s5
	srli t1, s4, 7
	beqz t1, 214f
	j 215f
214:
	add t1, s4, s5
	srli t1, t1, 7
	beqz t1, 216f
	j 217f
216:
	addi t2, s4, 0
217:
215:
	sub s4, s4, t2
218:
	lbu t1, 0(s3)
	add t3, s1, s5
	sb t1, 64(t3)
	addi s3, s3, 1
	addi s5, s5, 1
	addi t2, t2, -1
	bnez t2, 218b
	addi t1, s5, -128
	beqz t1, 219f
	j 220f
219:
	addi a1, s1, 64
	addi s5, zero, 0
	addi t0, zero, 1
220:
213:
24:
	beqz t0, 221f
	addi a0, s1, 0
	addi a2, zero, 1
	addi a3, s2, 0
	call {vg_sha512_compress}
	j 222f
221:
222:
	bnez s4, 22b
	j 21f
20:
21:
	ld ra, 144(s2)
	ld s1, 152(s2)
	ld s3, 168(s2)
	ld s4, 176(s2)
	ld s5, 184(s2)
	ld s6, 192(s2)
	ld s2, 160(s2)
	addi sp, sp, 208
	ret
	.option pop

vg_sha512_finalize:
	.option push
	.option arch, +m, +c
	addi sp, sp, -208
	addi t0, sp, 0
	sd ra, 144(t0)
	sd s1, 152(t0)
	sd s2, 160(t0)
	sd s3, 168(t0)
	sd s4, 176(t0)
	sd s5, 184(t0)
	sd s6, 192(t0)
	addi s1, a0, 0
	addi s2, t0, 0
	addi s3, a2, 0
	addi s4, a1, 0
	andi s5, s4, 127
	addi t1, zero, 128
	add t3, s1, s5
	sb t1, 64(t3)
	addi s5, s5, 1
	addi s6, s5, 15
	srli s6, s6, 7
20:
	addi t2, zero, 128
	beqz s6, 21f
	j 22f
21:
	addi t2, zero, 112
22:
	addi t1, zero, 0
	sub t2, t2, s5
	beqz t2, 23f
25:
	add t3, s1, s5
	sb t1, 64(t3)
	addi s5, s5, 1
	addi t2, t2, -1
	bnez t2, 25b
	j 24f
23:
24:
	beqz s6, 26f
	j 27f
26:
	srli t1, s4, 61
	srli t3, t1, 56
	sb t3, 176(s1)
	srli t3, t1, 48
	sb t3, 177(s1)
	srli t3, t1, 40
	sb t3, 178(s1)
	srli t3, t1, 32
	sb t3, 179(s1)
	srli t3, t1, 24
	sb t3, 180(s1)
	srli t3, t1, 16
	sb t3, 181(s1)
	srli t3, t1, 8
	sb t3, 182(s1)
	srli t3, t1, 0
	sb t3, 183(s1)
	slli t1, s4, 3
	srli t3, t1, 56
	sb t3, 184(s1)
	srli t3, t1, 48
	sb t3, 185(s1)
	srli t3, t1, 40
	sb t3, 186(s1)
	srli t3, t1, 32
	sb t3, 187(s1)
	srli t3, t1, 24
	sb t3, 188(s1)
	srli t3, t1, 16
	sb t3, 189(s1)
	srli t3, t1, 8
	sb t3, 190(s1)
	srli t3, t1, 0
	sb t3, 191(s1)
27:
	addi a1, s1, 64
	addi a0, s1, 0
	addi a2, zero, 1
	addi a3, s2, 0
	call {vg_sha512_compress}
	addi s5, zero, 0
	addi s6, s6, -1
	beqz s6, 20b
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 0(s3)
	srli t2, t1, 48
	sb t2, 1(s3)
	srli t2, t1, 40
	sb t2, 2(s3)
	srli t2, t1, 32
	sb t2, 3(s3)
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 8(s3)
	srli t2, t1, 48
	sb t2, 9(s3)
	srli t2, t1, 40
	sb t2, 10(s3)
	srli t2, t1, 32
	sb t2, 11(s3)
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 20(s1)
	lbu t2, 21(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 22(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 23(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 16(s3)
	srli t2, t1, 48
	sb t2, 17(s3)
	srli t2, t1, 40
	sb t2, 18(s3)
	srli t2, t1, 32
	sb t2, 19(s3)
	srli t2, t1, 24
	sb t2, 20(s3)
	srli t2, t1, 16
	sb t2, 21(s3)
	srli t2, t1, 8
	sb t2, 22(s3)
	srli t2, t1, 0
	sb t2, 23(s3)
	lbu t1, 24(s1)
	lbu t2, 25(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 26(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 27(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 28(s1)
	lbu t2, 29(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 30(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 31(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 24(s3)
	srli t2, t1, 48
	sb t2, 25(s3)
	srli t2, t1, 40
	sb t2, 26(s3)
	srli t2, t1, 32
	sb t2, 27(s3)
	srli t2, t1, 24
	sb t2, 28(s3)
	srli t2, t1, 16
	sb t2, 29(s3)
	srli t2, t1, 8
	sb t2, 30(s3)
	srli t2, t1, 0
	sb t2, 31(s3)
	lbu t1, 32(s1)
	lbu t2, 33(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 34(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 35(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 36(s1)
	lbu t2, 37(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 38(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 39(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 32(s3)
	srli t2, t1, 48
	sb t2, 33(s3)
	srli t2, t1, 40
	sb t2, 34(s3)
	srli t2, t1, 32
	sb t2, 35(s3)
	srli t2, t1, 24
	sb t2, 36(s3)
	srli t2, t1, 16
	sb t2, 37(s3)
	srli t2, t1, 8
	sb t2, 38(s3)
	srli t2, t1, 0
	sb t2, 39(s3)
	lbu t1, 40(s1)
	lbu t2, 41(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 42(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 43(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 44(s1)
	lbu t2, 45(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 46(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 47(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 40(s3)
	srli t2, t1, 48
	sb t2, 41(s3)
	srli t2, t1, 40
	sb t2, 42(s3)
	srli t2, t1, 32
	sb t2, 43(s3)
	srli t2, t1, 24
	sb t2, 44(s3)
	srli t2, t1, 16
	sb t2, 45(s3)
	srli t2, t1, 8
	sb t2, 46(s3)
	srli t2, t1, 0
	sb t2, 47(s3)
	lbu t1, 48(s1)
	lbu t2, 49(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 50(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 51(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 52(s1)
	lbu t2, 53(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 54(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 55(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 48(s3)
	srli t2, t1, 48
	sb t2, 49(s3)
	srli t2, t1, 40
	sb t2, 50(s3)
	srli t2, t1, 32
	sb t2, 51(s3)
	srli t2, t1, 24
	sb t2, 52(s3)
	srli t2, t1, 16
	sb t2, 53(s3)
	srli t2, t1, 8
	sb t2, 54(s3)
	srli t2, t1, 0
	sb t2, 55(s3)
	lbu t1, 56(s1)
	lbu t2, 57(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 58(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 59(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 60(s1)
	lbu t2, 61(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 62(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 63(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 56(s3)
	srli t2, t1, 48
	sb t2, 57(s3)
	srli t2, t1, 40
	sb t2, 58(s3)
	srli t2, t1, 32
	sb t2, 59(s3)
	srli t2, t1, 24
	sb t2, 60(s3)
	srli t2, t1, 16
	sb t2, 61(s3)
	srli t2, t1, 8
	sb t2, 62(s3)
	srli t2, t1, 0
	sb t2, 63(s3)
	ld ra, 144(s2)
	ld s1, 152(s2)
	ld s3, 168(s2)
	ld s4, 176(s2)
	ld s5, 184(s2)
	ld s6, 192(s2)
	ld s2, 160(s2)
	addi sp, sp, 208
	ret
	.option pop

vg_sha384_finalize:
	.option push
	.option arch, +m, +c
	addi sp, sp, -208
	addi t0, sp, 0
	sd ra, 144(t0)
	sd s1, 152(t0)
	sd s2, 160(t0)
	sd s3, 168(t0)
	sd s4, 176(t0)
	sd s5, 184(t0)
	sd s6, 192(t0)
	addi s1, a0, 0
	addi s2, t0, 0
	addi s3, a2, 0
	addi s4, a1, 0
	andi s5, s4, 127
	addi t1, zero, 128
	add t3, s1, s5
	sb t1, 64(t3)
	addi s5, s5, 1
	addi s6, s5, 15
	srli s6, s6, 7
20:
	addi t2, zero, 128
	beqz s6, 21f
	j 22f
21:
	addi t2, zero, 112
22:
	addi t1, zero, 0
	sub t2, t2, s5
	beqz t2, 23f
25:
	add t3, s1, s5
	sb t1, 64(t3)
	addi s5, s5, 1
	addi t2, t2, -1
	bnez t2, 25b
	j 24f
23:
24:
	beqz s6, 26f
	j 27f
26:
	srli t1, s4, 61
	srli t3, t1, 56
	sb t3, 176(s1)
	srli t3, t1, 48
	sb t3, 177(s1)
	srli t3, t1, 40
	sb t3, 178(s1)
	srli t3, t1, 32
	sb t3, 179(s1)
	srli t3, t1, 24
	sb t3, 180(s1)
	srli t3, t1, 16
	sb t3, 181(s1)
	srli t3, t1, 8
	sb t3, 182(s1)
	srli t3, t1, 0
	sb t3, 183(s1)
	slli t1, s4, 3
	srli t3, t1, 56
	sb t3, 184(s1)
	srli t3, t1, 48
	sb t3, 185(s1)
	srli t3, t1, 40
	sb t3, 186(s1)
	srli t3, t1, 32
	sb t3, 187(s1)
	srli t3, t1, 24
	sb t3, 188(s1)
	srli t3, t1, 16
	sb t3, 189(s1)
	srli t3, t1, 8
	sb t3, 190(s1)
	srli t3, t1, 0
	sb t3, 191(s1)
27:
	addi a1, s1, 64
	addi a0, s1, 0
	addi a2, zero, 1
	addi a3, s2, 0
	call {vg_sha512_compress}
	addi s5, zero, 0
	addi s6, s6, -1
	beqz s6, 20b
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 0(s3)
	srli t2, t1, 48
	sb t2, 1(s3)
	srli t2, t1, 40
	sb t2, 2(s3)
	srli t2, t1, 32
	sb t2, 3(s3)
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 8(s3)
	srli t2, t1, 48
	sb t2, 9(s3)
	srli t2, t1, 40
	sb t2, 10(s3)
	srli t2, t1, 32
	sb t2, 11(s3)
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 20(s1)
	lbu t2, 21(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 22(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 23(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 16(s3)
	srli t2, t1, 48
	sb t2, 17(s3)
	srli t2, t1, 40
	sb t2, 18(s3)
	srli t2, t1, 32
	sb t2, 19(s3)
	srli t2, t1, 24
	sb t2, 20(s3)
	srli t2, t1, 16
	sb t2, 21(s3)
	srli t2, t1, 8
	sb t2, 22(s3)
	srli t2, t1, 0
	sb t2, 23(s3)
	lbu t1, 24(s1)
	lbu t2, 25(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 26(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 27(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 28(s1)
	lbu t2, 29(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 30(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 31(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 24(s3)
	srli t2, t1, 48
	sb t2, 25(s3)
	srli t2, t1, 40
	sb t2, 26(s3)
	srli t2, t1, 32
	sb t2, 27(s3)
	srli t2, t1, 24
	sb t2, 28(s3)
	srli t2, t1, 16
	sb t2, 29(s3)
	srli t2, t1, 8
	sb t2, 30(s3)
	srli t2, t1, 0
	sb t2, 31(s3)
	lbu t1, 32(s1)
	lbu t2, 33(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 34(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 35(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 36(s1)
	lbu t2, 37(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 38(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 39(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 32(s3)
	srli t2, t1, 48
	sb t2, 33(s3)
	srli t2, t1, 40
	sb t2, 34(s3)
	srli t2, t1, 32
	sb t2, 35(s3)
	srli t2, t1, 24
	sb t2, 36(s3)
	srli t2, t1, 16
	sb t2, 37(s3)
	srli t2, t1, 8
	sb t2, 38(s3)
	srli t2, t1, 0
	sb t2, 39(s3)
	lbu t1, 40(s1)
	lbu t2, 41(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 42(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 43(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 44(s1)
	lbu t2, 45(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 46(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 47(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 40(s3)
	srli t2, t1, 48
	sb t2, 41(s3)
	srli t2, t1, 40
	sb t2, 42(s3)
	srli t2, t1, 32
	sb t2, 43(s3)
	srli t2, t1, 24
	sb t2, 44(s3)
	srli t2, t1, 16
	sb t2, 45(s3)
	srli t2, t1, 8
	sb t2, 46(s3)
	srli t2, t1, 0
	sb t2, 47(s3)
	ld ra, 144(s2)
	ld s1, 152(s2)
	ld s3, 168(s2)
	ld s4, 176(s2)
	ld s5, 184(s2)
	ld s6, 192(s2)
	ld s2, 160(s2)
	addi sp, sp, 208
	ret
	.option pop

vg_sha512_256_finalize:
	.option push
	.option arch, +m, +c
	addi sp, sp, -208
	addi t0, sp, 0
	sd ra, 144(t0)
	sd s1, 152(t0)
	sd s2, 160(t0)
	sd s3, 168(t0)
	sd s4, 176(t0)
	sd s5, 184(t0)
	sd s6, 192(t0)
	addi s1, a0, 0
	addi s2, t0, 0
	addi s3, a2, 0
	addi s4, a1, 0
	andi s5, s4, 127
	addi t1, zero, 128
	add t3, s1, s5
	sb t1, 64(t3)
	addi s5, s5, 1
	addi s6, s5, 15
	srli s6, s6, 7
20:
	addi t2, zero, 128
	beqz s6, 21f
	j 22f
21:
	addi t2, zero, 112
22:
	addi t1, zero, 0
	sub t2, t2, s5
	beqz t2, 23f
25:
	add t3, s1, s5
	sb t1, 64(t3)
	addi s5, s5, 1
	addi t2, t2, -1
	bnez t2, 25b
	j 24f
23:
24:
	beqz s6, 26f
	j 27f
26:
	srli t1, s4, 61
	srli t3, t1, 56
	sb t3, 176(s1)
	srli t3, t1, 48
	sb t3, 177(s1)
	srli t3, t1, 40
	sb t3, 178(s1)
	srli t3, t1, 32
	sb t3, 179(s1)
	srli t3, t1, 24
	sb t3, 180(s1)
	srli t3, t1, 16
	sb t3, 181(s1)
	srli t3, t1, 8
	sb t3, 182(s1)
	srli t3, t1, 0
	sb t3, 183(s1)
	slli t1, s4, 3
	srli t3, t1, 56
	sb t3, 184(s1)
	srli t3, t1, 48
	sb t3, 185(s1)
	srli t3, t1, 40
	sb t3, 186(s1)
	srli t3, t1, 32
	sb t3, 187(s1)
	srli t3, t1, 24
	sb t3, 188(s1)
	srli t3, t1, 16
	sb t3, 189(s1)
	srli t3, t1, 8
	sb t3, 190(s1)
	srli t3, t1, 0
	sb t3, 191(s1)
27:
	addi a1, s1, 64
	addi a0, s1, 0
	addi a2, zero, 1
	addi a3, s2, 0
	call {vg_sha512_compress}
	addi s5, zero, 0
	addi s6, s6, -1
	beqz s6, 20b
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 0(s3)
	srli t2, t1, 48
	sb t2, 1(s3)
	srli t2, t1, 40
	sb t2, 2(s3)
	srli t2, t1, 32
	sb t2, 3(s3)
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 8(s3)
	srli t2, t1, 48
	sb t2, 9(s3)
	srli t2, t1, 40
	sb t2, 10(s3)
	srli t2, t1, 32
	sb t2, 11(s3)
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 20(s1)
	lbu t2, 21(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 22(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 23(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 16(s3)
	srli t2, t1, 48
	sb t2, 17(s3)
	srli t2, t1, 40
	sb t2, 18(s3)
	srli t2, t1, 32
	sb t2, 19(s3)
	srli t2, t1, 24
	sb t2, 20(s3)
	srli t2, t1, 16
	sb t2, 21(s3)
	srli t2, t1, 8
	sb t2, 22(s3)
	srli t2, t1, 0
	sb t2, 23(s3)
	lbu t1, 24(s1)
	lbu t2, 25(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 26(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 27(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 28(s1)
	lbu t2, 29(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 30(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 31(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 24(s3)
	srli t2, t1, 48
	sb t2, 25(s3)
	srli t2, t1, 40
	sb t2, 26(s3)
	srli t2, t1, 32
	sb t2, 27(s3)
	srli t2, t1, 24
	sb t2, 28(s3)
	srli t2, t1, 16
	sb t2, 29(s3)
	srli t2, t1, 8
	sb t2, 30(s3)
	srli t2, t1, 0
	sb t2, 31(s3)
	ld ra, 144(s2)
	ld s1, 152(s2)
	ld s3, 168(s2)
	ld s4, 176(s2)
	ld s5, 184(s2)
	ld s6, 192(s2)
	ld s2, 160(s2)
	addi sp, sp, 208
	ret
	.option pop

vg_sha512_224_finalize:
	.option push
	.option arch, +m, +c
	addi sp, sp, -208
	addi t0, sp, 0
	sd ra, 144(t0)
	sd s1, 152(t0)
	sd s2, 160(t0)
	sd s3, 168(t0)
	sd s4, 176(t0)
	sd s5, 184(t0)
	sd s6, 192(t0)
	addi s1, a0, 0
	addi s2, t0, 0
	addi s3, a2, 0
	addi s4, a1, 0
	andi s5, s4, 127
	addi t1, zero, 128
	add t3, s1, s5
	sb t1, 64(t3)
	addi s5, s5, 1
	addi s6, s5, 15
	srli s6, s6, 7
20:
	addi t2, zero, 128
	beqz s6, 21f
	j 22f
21:
	addi t2, zero, 112
22:
	addi t1, zero, 0
	sub t2, t2, s5
	beqz t2, 23f
25:
	add t3, s1, s5
	sb t1, 64(t3)
	addi s5, s5, 1
	addi t2, t2, -1
	bnez t2, 25b
	j 24f
23:
24:
	beqz s6, 26f
	j 27f
26:
	srli t1, s4, 61
	srli t3, t1, 56
	sb t3, 176(s1)
	srli t3, t1, 48
	sb t3, 177(s1)
	srli t3, t1, 40
	sb t3, 178(s1)
	srli t3, t1, 32
	sb t3, 179(s1)
	srli t3, t1, 24
	sb t3, 180(s1)
	srli t3, t1, 16
	sb t3, 181(s1)
	srli t3, t1, 8
	sb t3, 182(s1)
	srli t3, t1, 0
	sb t3, 183(s1)
	slli t1, s4, 3
	srli t3, t1, 56
	sb t3, 184(s1)
	srli t3, t1, 48
	sb t3, 185(s1)
	srli t3, t1, 40
	sb t3, 186(s1)
	srli t3, t1, 32
	sb t3, 187(s1)
	srli t3, t1, 24
	sb t3, 188(s1)
	srli t3, t1, 16
	sb t3, 189(s1)
	srli t3, t1, 8
	sb t3, 190(s1)
	srli t3, t1, 0
	sb t3, 191(s1)
27:
	addi a1, s1, 64
	addi a0, s1, 0
	addi a2, zero, 1
	addi a3, s2, 0
	call {vg_sha512_compress}
	addi s5, zero, 0
	addi s6, s6, -1
	beqz s6, 20b
	lbu t1, 0(s1)
	lbu t2, 1(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 2(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 3(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 4(s1)
	lbu t2, 5(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 6(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 7(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 0(s3)
	srli t2, t1, 48
	sb t2, 1(s3)
	srli t2, t1, 40
	sb t2, 2(s3)
	srli t2, t1, 32
	sb t2, 3(s3)
	srli t2, t1, 24
	sb t2, 4(s3)
	srli t2, t1, 16
	sb t2, 5(s3)
	srli t2, t1, 8
	sb t2, 6(s3)
	srli t2, t1, 0
	sb t2, 7(s3)
	lbu t1, 8(s1)
	lbu t2, 9(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 10(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 11(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 12(s1)
	lbu t2, 13(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 14(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 15(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 8(s3)
	srli t2, t1, 48
	sb t2, 9(s3)
	srli t2, t1, 40
	sb t2, 10(s3)
	srli t2, t1, 32
	sb t2, 11(s3)
	srli t2, t1, 24
	sb t2, 12(s3)
	srli t2, t1, 16
	sb t2, 13(s3)
	srli t2, t1, 8
	sb t2, 14(s3)
	srli t2, t1, 0
	sb t2, 15(s3)
	lbu t1, 16(s1)
	lbu t2, 17(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 18(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 19(s1)
	slli t2, t2, 24
	or t1, t1, t2
	lbu t4, 20(s1)
	lbu t2, 21(s1)
	slli t2, t2, 8
	or t4, t4, t2
	lbu t2, 22(s1)
	slli t2, t2, 16
	or t4, t4, t2
	lbu t2, 23(s1)
	slli t2, t2, 24
	or t4, t4, t2
	slli t4, t4, 32
	or t1, t1, t4
	srli t2, t1, 56
	sb t2, 16(s3)
	srli t2, t1, 48
	sb t2, 17(s3)
	srli t2, t1, 40
	sb t2, 18(s3)
	srli t2, t1, 32
	sb t2, 19(s3)
	srli t2, t1, 24
	sb t2, 20(s3)
	srli t2, t1, 16
	sb t2, 21(s3)
	srli t2, t1, 8
	sb t2, 22(s3)
	srli t2, t1, 0
	sb t2, 23(s3)
	lbu t1, 28(s1)
	lbu t2, 29(s1)
	slli t2, t2, 8
	or t1, t1, t2
	lbu t2, 30(s1)
	slli t2, t2, 16
	or t1, t1, t2
	lbu t2, 31(s1)
	slli t2, t2, 24
	or t1, t1, t2
	srli t2, t1, 24
	sb t2, 24(s3)
	srli t2, t1, 16
	sb t2, 25(s3)
	srli t2, t1, 8
	sb t2, 26(s3)
	srli t2, t1, 0
	sb t2, 27(s3)
	ld ra, 144(s2)
	ld s1, 152(s2)
	ld s3, 168(s2)
	ld s4, 176(s2)
	ld s5, 184(s2)
	ld s6, 192(s2)
	ld s2, 160(s2)
	addi sp, sp, 208
	ret
	.option pop
