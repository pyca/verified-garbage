// The functions of `src/internal/vg_sha512_compress.rs` of `verified-garbage-asm-riscv64`, as text: generated from
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
