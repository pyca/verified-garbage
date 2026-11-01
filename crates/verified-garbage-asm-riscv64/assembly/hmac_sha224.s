// The functions of `src/hmac_sha224.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_sha224_init:
	.option push
	.option arch, +m, +c
	addi sp, sp, -176
	addi t0, sp, 0
	sd ra, 128(t0)
	sd s7, 136(t0)
	sd s8, 144(t0)
	sd s9, 152(t0)
	sd s10, 160(t0)
	sd s11, 168(t0)
	addi s7, a0, 0
	addi s8, t0, 0
	addi s9, a1, 0
	addi s10, a2, 0
	addi s11, a3, 0
	srli t1, a3, 7
	andi t2, a3, 127
	addi t2, t2, 63
	srli t2, t2, 7
	add t1, t1, t2
	beqz t1, 20f
	addi a0, s8, 0
	call {vg_sha224_init}
	addi a0, s8, 0
	addi a1, zero, 0
	addi a2, s10, 0
	addi a3, s11, 0
	call {vg_sha256_update}
	addi a0, s8, 0
	addi a1, s11, 0
	addi a2, s8, 96
	call {vg_sha224_finalize}
	addi s10, s8, 96
	addi s11, zero, 28
	j 21f
20:
21:
	addi a0, s7, 0
	call {vg_sha224_init}
	addi a0, s9, 0
	call {vg_sha224_init}
	addi t5, zero, 54
	addi t6, zero, 0
	addi t2, s10, 0
	addi t3, s11, 0
	beqz t3, 22f
24:
	lbu t1, 0(t2)
	xor t1, t1, t5
	add t4, s9, t6
	sb t1, 32(t4)
	addi t2, t2, 1
	addi t6, t6, 1
	addi t3, t3, -1
	bnez t3, 24b
	j 23f
22:
23:
	addi t3, zero, 64
	sub t3, t3, t6
	beqz t3, 25f
27:
	add t4, s9, t6
	sb t5, 32(t4)
	addi t6, t6, 1
	addi t3, t3, -1
	bnez t3, 27b
	j 26f
25:
26:
	addi a0, s7, 0
	addi a1, zero, 0
	addi a2, s9, 32
	addi a3, zero, 64
	call {vg_sha256_update}
	addi t5, zero, 92
	addi t6, zero, 0
	addi t2, s10, 0
	addi t3, s11, 0
	beqz t3, 28f
210:
	lbu t1, 0(t2)
	xor t1, t1, t5
	add t4, s7, t6
	sb t1, 32(t4)
	addi t2, t2, 1
	addi t6, t6, 1
	addi t3, t3, -1
	bnez t3, 210b
	j 29f
28:
29:
	addi t3, zero, 64
	sub t3, t3, t6
	beqz t3, 211f
213:
	add t4, s7, t6
	sb t5, 32(t4)
	addi t6, t6, 1
	addi t3, t3, -1
	bnez t3, 213b
	j 212f
211:
212:
	addi a0, s9, 0
	addi a1, zero, 0
	addi a2, s7, 32
	addi a3, zero, 64
	call {vg_sha256_update}
	addi t1, zero, 0
	sd t1, 0(s8)
	sd t1, 8(s8)
	sd t1, 16(s8)
	sd t1, 24(s8)
	sd t1, 32(s8)
	sd t1, 40(s8)
	sd t1, 48(s8)
	sd t1, 56(s8)
	sd t1, 64(s8)
	sd t1, 72(s8)
	sd t1, 80(s8)
	sd t1, 88(s8)
	sd t1, 96(s8)
	sd t1, 104(s8)
	sd t1, 112(s8)
	sd t1, 120(s8)
	ld ra, 128(s8)
	ld s7, 136(s8)
	ld s9, 152(s8)
	ld s10, 160(s8)
	ld s11, 168(s8)
	ld s8, 144(s8)
	addi sp, sp, 176
	ret
	.option pop

vg_hmac_sha224_finalize:
	.option push
	.option arch, +m, +c
	addi sp, sp, -80
	addi t0, sp, 0
	sd ra, 32(t0)
	sd s7, 40(t0)
	sd s8, 48(t0)
	sd s9, 56(t0)
	sd s10, 64(t0)
	sd s11, 72(t0)
	addi s7, a0, 0
	addi s8, t0, 0
	addi s9, a1, 0
	addi s10, a3, 0
	addi a1, a2, 0
	addi a2, t0, 0
	call {vg_sha224_finalize}
	lbu t1, 0(s9)
	sb t1, 0(s7)
	lbu t1, 1(s9)
	sb t1, 1(s7)
	lbu t1, 2(s9)
	sb t1, 2(s7)
	lbu t1, 3(s9)
	sb t1, 3(s7)
	lbu t1, 4(s9)
	sb t1, 4(s7)
	lbu t1, 5(s9)
	sb t1, 5(s7)
	lbu t1, 6(s9)
	sb t1, 6(s7)
	lbu t1, 7(s9)
	sb t1, 7(s7)
	lbu t1, 8(s9)
	sb t1, 8(s7)
	lbu t1, 9(s9)
	sb t1, 9(s7)
	lbu t1, 10(s9)
	sb t1, 10(s7)
	lbu t1, 11(s9)
	sb t1, 11(s7)
	lbu t1, 12(s9)
	sb t1, 12(s7)
	lbu t1, 13(s9)
	sb t1, 13(s7)
	lbu t1, 14(s9)
	sb t1, 14(s7)
	lbu t1, 15(s9)
	sb t1, 15(s7)
	lbu t1, 16(s9)
	sb t1, 16(s7)
	lbu t1, 17(s9)
	sb t1, 17(s7)
	lbu t1, 18(s9)
	sb t1, 18(s7)
	lbu t1, 19(s9)
	sb t1, 19(s7)
	lbu t1, 20(s9)
	sb t1, 20(s7)
	lbu t1, 21(s9)
	sb t1, 21(s7)
	lbu t1, 22(s9)
	sb t1, 22(s7)
	lbu t1, 23(s9)
	sb t1, 23(s7)
	lbu t1, 24(s9)
	sb t1, 24(s7)
	lbu t1, 25(s9)
	sb t1, 25(s7)
	lbu t1, 26(s9)
	sb t1, 26(s7)
	lbu t1, 27(s9)
	sb t1, 27(s7)
	lbu t1, 28(s9)
	sb t1, 28(s7)
	lbu t1, 29(s9)
	sb t1, 29(s7)
	lbu t1, 30(s9)
	sb t1, 30(s7)
	lbu t1, 31(s9)
	sb t1, 31(s7)
	addi a0, s7, 0
	addi a1, zero, 64
	addi a2, s8, 0
	addi a3, zero, 28
	call {vg_sha256_update}
	addi a0, s7, 0
	addi a1, zero, 92
	addi a2, s10, 0
	call {vg_sha224_finalize}
	ld ra, 32(s8)
	ld s7, 40(s8)
	ld s9, 56(s8)
	ld s10, 64(s8)
	ld s11, 72(s8)
	ld s8, 48(s8)
	addi sp, sp, 80
	ret
	.option pop
