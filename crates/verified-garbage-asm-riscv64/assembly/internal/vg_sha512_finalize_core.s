// The functions of `src/internal/vg_sha512_finalize_core.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha512_finalize_core:
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
