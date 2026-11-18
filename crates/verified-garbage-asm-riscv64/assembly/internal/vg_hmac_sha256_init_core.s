// The functions of `src/internal/vg_hmac_sha256_init_core.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_sha256_init_core:
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
	call {vg_sha256_init_core}
	addi a0, s8, 0
	addi a1, zero, 0
	addi a2, s10, 0
	addi a3, s11, 0
	call {vg_sha256_update_core}
	addi a0, s8, 0
	addi a1, s11, 0
	addi a2, s8, 96
	call {vg_sha256_finalize_core}
	addi s10, s8, 96
	addi s11, zero, 32
	j 21f
20:
21:
	addi a0, s7, 0
	call {vg_sha256_init_core}
	addi a0, s9, 0
	call {vg_sha256_init_core}
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
	call {vg_sha256_update_core}
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
	call {vg_sha256_update_core}
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
