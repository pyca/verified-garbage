// The functions of `src/hmac_md5.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_md5_init:
	.option push
	.option arch, +m, +c
	addi sp, sp, -144
	addi t0, sp, 0
	sd ra, 96(t0)
	sd s7, 104(t0)
	sd s8, 112(t0)
	sd s9, 120(t0)
	sd s10, 128(t0)
	sd s11, 136(t0)
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
	call {vg_md5_init_core}
	addi a0, s8, 0
	addi a1, zero, 0
	addi a2, s10, 0
	addi a3, s11, 0
	call {vg_md5_update_core}
	addi a0, s8, 0
	addi a1, s11, 0
	addi a2, s8, 80
	call {vg_md5_finalize_core}
	addi s10, s8, 80
	addi s11, zero, 16
	j 21f
20:
21:
	addi a0, s7, 0
	call {vg_md5_init_core}
	addi a0, s9, 0
	call {vg_md5_init_core}
	addi t5, zero, 54
	addi t6, zero, 0
	addi t2, s10, 0
	addi t3, s11, 0
	beqz t3, 22f
24:
	lbu t1, 0(t2)
	xor t1, t1, t5
	add t4, s9, t6
	sb t1, 16(t4)
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
	sb t5, 16(t4)
	addi t6, t6, 1
	addi t3, t3, -1
	bnez t3, 27b
	j 26f
25:
26:
	addi a0, s7, 0
	addi a1, zero, 0
	addi a2, s9, 16
	addi a3, zero, 64
	call {vg_md5_update_core}
	addi t5, zero, 92
	addi t6, zero, 0
	addi t2, s10, 0
	addi t3, s11, 0
	beqz t3, 28f
210:
	lbu t1, 0(t2)
	xor t1, t1, t5
	add t4, s7, t6
	sb t1, 16(t4)
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
	sb t5, 16(t4)
	addi t6, t6, 1
	addi t3, t3, -1
	bnez t3, 213b
	j 212f
211:
212:
	addi a0, s9, 0
	addi a1, zero, 0
	addi a2, s7, 16
	addi a3, zero, 64
	call {vg_md5_update_core}
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
	ld ra, 96(s8)
	ld s7, 104(s8)
	ld s9, 120(s8)
	ld s10, 128(s8)
	ld s11, 136(s8)
	ld s8, 112(s8)
	addi sp, sp, 144
	addi t0, zero, 0
	addi sp, sp, -288
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	sd t0, 80(t1)
	sd t0, 88(t1)
	sd t0, 96(t1)
	sd t0, 104(t1)
	sd t0, 112(t1)
	sd t0, 120(t1)
	sd t0, 128(t1)
	sd t0, 136(t1)
	sd t0, 144(t1)
	sd t0, 152(t1)
	sd t0, 160(t1)
	sd t0, 168(t1)
	sd t0, 176(t1)
	sd t0, 184(t1)
	sd t0, 192(t1)
	sd t0, 200(t1)
	sd t0, 208(t1)
	sd t0, 216(t1)
	sd t0, 224(t1)
	sd t0, 232(t1)
	sd t0, 240(t1)
	sd t0, 248(t1)
	sd t0, 256(t1)
	sd t0, 264(t1)
	sd t0, 272(t1)
	sd t0, 280(t1)
	addi sp, sp, 288
	addi a0, zero, 0
	addi a1, zero, 0
	addi a2, zero, 0
	addi a3, zero, 0
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	addi a7, zero, 0
	addi t0, zero, 0
	addi t1, zero, 0
	addi t2, zero, 0
	addi t3, zero, 0
	addi t4, zero, 0
	addi t5, zero, 0
	addi t6, zero, 0
	ret
	.option pop

vg_hmac_md5_finalize:
	.option push
	.option arch, +m, +c
	addi sp, sp, -64
	addi t0, sp, 0
	sd ra, 16(t0)
	sd s7, 24(t0)
	sd s8, 32(t0)
	sd s9, 40(t0)
	sd s10, 48(t0)
	sd s11, 56(t0)
	addi s7, a0, 0
	addi s8, t0, 0
	addi s9, a1, 0
	addi s10, a3, 0
	addi a1, a2, 0
	addi a2, t0, 0
	call {vg_md5_finalize_core}
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
	addi a0, s7, 0
	addi a1, zero, 64
	addi a2, s8, 0
	addi a3, zero, 16
	call {vg_md5_update_core}
	addi a0, s7, 0
	addi a1, zero, 80
	addi a2, s10, 0
	call {vg_md5_finalize_core}
	ld ra, 16(s8)
	ld s7, 24(s8)
	ld s9, 40(s8)
	ld s10, 48(s8)
	ld s11, 56(s8)
	ld s8, 32(s8)
	addi sp, sp, 64
	addi t0, zero, 0
	addi sp, sp, -208
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	sd t0, 80(t1)
	sd t0, 88(t1)
	sd t0, 96(t1)
	sd t0, 104(t1)
	sd t0, 112(t1)
	sd t0, 120(t1)
	sd t0, 128(t1)
	sd t0, 136(t1)
	sd t0, 144(t1)
	sd t0, 152(t1)
	sd t0, 160(t1)
	sd t0, 168(t1)
	sd t0, 176(t1)
	sd t0, 184(t1)
	sd t0, 192(t1)
	sd t0, 200(t1)
	addi sp, sp, 208
	addi a0, zero, 0
	addi a1, zero, 0
	addi a2, zero, 0
	addi a3, zero, 0
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	addi a7, zero, 0
	addi t0, zero, 0
	addi t1, zero, 0
	addi t2, zero, 0
	addi t3, zero, 0
	addi t4, zero, 0
	addi t5, zero, 0
	addi t6, zero, 0
	ret
	.option pop
