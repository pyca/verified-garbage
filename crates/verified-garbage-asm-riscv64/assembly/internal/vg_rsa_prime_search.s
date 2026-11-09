// The functions of `src/internal/vg_rsa_prime_search.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_prime_search:
	.option push
	.option arch, +m, +c
	addi sp, sp, -160
	addi t6, sp, 0
	ld t0, 160(t6)
	ld t1, 168(t6)
	ld t2, 176(t6)
	ld t3, 184(t6)
	ld t4, 0(t3)
	sd s0, 32(t6)
	addi s0, t6, 0
	sd a0, 40(s0)
	sd a1, 48(s0)
	sd a2, 56(s0)
	sd a3, 64(s0)
	sd a4, 72(s0)
	sd a5, 80(s0)
	sd a6, 88(s0)
	sd a7, 96(s0)
	sd t0, 104(s0)
	sd t1, 112(s0)
	sd t2, 120(s0)
	sd t3, 144(s0)
	sd t4, 0(s0)
	sd a1, 8(s0)
	slli t4, a1, 15
	add t4, t4, a1
	sd t4, 16(s0)
	addi t5, zero, 0
	sd t5, 24(s0)
	sd t5, 128(s0)
	addi sp, sp, -16
	sd ra, 8(sp)
20:
	ld t1, 0(s0)
	beqz t1, 21f
	addi sp, sp, -32
	ld a0, 40(s0)
	ld a1, 48(s0)
	ld a2, 56(s0)
	ld a3, 64(s0)
	ld a4, 72(s0)
	ld a5, 80(s0)
	ld a6, 88(s0)
	ld a7, 96(s0)
	ld t1, 104(s0)
	ld t2, 112(s0)
	ld t3, 120(s0)
	addi t0, sp, 0
	sd t1, 0(t0)
	sd t2, 8(t0)
	sd t3, 16(t0)
	call {vg_rsa_keygen_candidate}
	addi sp, sp, 32
	slli t1, a0, 32
	srli t1, t1, 32
	ld t3, 56(s0)
	ld t2, 0(t3)
	addi t4, t1, -1
	beqz t4, 23f
	beqz t1, 25f
	beqz t2, 27f
	ld t3, 96(s0)
	ld t4, 104(s0)
	ld t5, 128(s0)
	add t3, t3, t2
	sub t4, t4, t2
	add t5, t5, t2
	addi t6, zero, 4
	sd t3, 96(s0)
	sd t4, 104(s0)
	sd t5, 128(s0)
	sd t6, 136(s0)
	addi t5, t1, -2
	beqz t5, 29f
	ld t3, 0(s0)
	addi t3, t3, -1
	sd t3, 0(s0)
	j 210f
29:
210:
	j 28f
27:
	addi t2, zero, 0
	addi t3, zero, 3
	sd t2, 0(s0)
	sd t2, 24(s0)
	sd t3, 136(s0)
	ld a1, 40(s0)
	ld a2, 48(s0)
	addi a3, zero, 0
211:
	sb a3, 0(a1)
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 211b
28:
	j 26f
25:
	ld t2, 104(s0)
	ld t3, 16(s0)
	sltu t4, t2, t3
	beqz t4, 212f
	ld t4, 8(s0)
	slli t4, t4, 4
	sltu t0, t2, t4
	addi t5, zero, 0
	sub t0, t5, t0
	xor t5, t2, t4
	and t5, t5, t0
	xor t5, t5, t2
	add t5, t5, t5
	sltu t0, t5, t3
	addi t6, zero, 0
	sub t0, t6, t0
	xor t6, t5, t3
	and t6, t6, t0
	xor t6, t6, t3
	addi t4, zero, 0
	sd t6, 24(s0)
	sd t4, 136(s0)
	j 213f
212:
	addi t2, zero, 0
	addi t3, zero, 3
	sd t2, 0(s0)
	sd t2, 24(s0)
	sd t3, 136(s0)
	ld a1, 40(s0)
	ld a2, 48(s0)
	addi a3, zero, 0
214:
	sb a3, 0(a1)
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 214b
213:
26:
	j 24f
23:
	ld t3, 128(s0)
	add t3, t3, t2
	sd t3, 128(s0)
	addi t2, zero, 0
	addi t3, zero, 1
	sd t2, 0(s0)
	sd t2, 24(s0)
	sd t3, 136(s0)
24:
	j 22f
21:
	addi t2, zero, 0
	addi t3, zero, 3
	sd t2, 0(s0)
	sd t2, 24(s0)
	sd t3, 136(s0)
	ld a1, 40(s0)
	ld a2, 48(s0)
	addi a3, zero, 0
215:
	sb a3, 0(a1)
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 215b
22:
	ld t1, 136(s0)
	addi t1, t1, -4
	beqz t1, 20b
	ld ra, 8(sp)
	addi sp, sp, 16
	ld t0, 144(s0)
	ld t1, 0(s0)
	ld t2, 8(s0)
	ld t3, 16(s0)
	ld t4, 24(s0)
	ld t5, 56(s0)
	ld t6, 128(s0)
	ld a0, 136(s0)
	ld s0, 32(s0)
	sd t1, 0(t0)
	sd t2, 8(t0)
	sd t3, 16(t0)
	sd t4, 24(t0)
	sd t6, 0(t5)
	addi sp, sp, 160
	ret
	.option pop
