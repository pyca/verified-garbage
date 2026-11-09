// The functions of `src/rsa_keygen.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_generate_init:
	.option push
	.option arch, +m, +c
	addi t3, zero, 0
	addi t4, zero, 0
	beqz a3, 20f
22:
	lbu t1, 0(a2)
	slli t3, t3, 8
	add t3, t3, t1
	srli t0, t3, 32
	or t4, t4, t0
	slli t3, t3, 32
	srli t3, t3, 32
	addi a2, a2, 1
	addi a3, a3, -1
	bnez a3, 22b
	j 21f
20:
21:
	addi t0, zero, 1
	sltu t5, t4, t0
	andi t0, t3, 1
	and t5, t5, t0
	addi t0, zero, 3
	sltu t0, t3, t0
	xori t0, t0, 1
	and t5, t5, t0
	addi t0, zero, 1
	slli t0, t0, 13
	addi t0, t0, 1
	sltu t6, a1, t0
	addi t0, zero, 512
	sltu t0, a1, t0
	xori t0, t0, 1
	and t6, t6, t0
	addi t2, zero, 2
	sub t2, t2, t6
	mul t2, t2, t5
	mul t1, t5, t6
	srli a1, a1, 7
	slli a1, a1, 3
	xori t0, t3, 3
	addi a3, zero, 1
	sltu t0, t0, a3
	slli a4, a1, 3
	slli a5, a1, 5
	add a4, a4, a5
	slli a5, a1, 4
	slli a6, a1, 3
	add a5, a5, a6
	mul a5, a5, t0
	add a4, a4, a5
	mul a4, a4, t1
	sd a4, 0(a0)
	mul a5, a1, t1
	sd a5, 8(a0)
	slli a5, a1, 15
	add a5, a5, a1
	mul a5, a5, t1
	sd a5, 16(a0)
	slli a5, a1, 5
	mul a5, a5, t1
	sd a5, 24(a0)
	addi a5, zero, 0
	sd a5, 32(a0)
	slli a5, t1, 2
	sd a5, 40(a0)
	mul a5, t3, t1
	srli a6, a5, 56
	sb a6, 48(a0)
	srli a6, a5, 48
	sb a6, 49(a0)
	srli a6, a5, 40
	sb a6, 50(a0)
	srli a6, a5, 32
	sb a6, 51(a0)
	srli a6, a5, 24
	sb a6, 52(a0)
	srli a6, a5, 16
	sb a6, 53(a0)
	srli a6, a5, 8
	sb a6, 54(a0)
	srli a6, a5, 0
	sb a6, 55(a0)
	addi a0, t2, 0
	ret
	.option pop

vg_rsa_generate:
	.option push
	.option arch, +m, +c
	addi sp, sp, -112
	addi t1, sp, 0
	sd s0, 72(t1)
	addi s0, t1, 0
	sd a0, 0(s0)
	sd a2, 16(s0)
	sd a3, 24(s0)
	sd a4, 32(s0)
	sd a5, 40(s0)
	sd a6, 48(s0)
	sd a7, 56(s0)
	ld a1, 8(a7)
	ld a6, 48(a7)
	sd a1, 8(s0)
	addi t0, zero, 0
	sd t0, 64(s0)
	slli a2, a1, 3
	slli a3, a1, 5
	add a2, a2, a3
	slli a3, a1, 4
	slli a4, a1, 3
	add a3, a3, a4
	addi a4, zero, 3
	slli a4, a4, 56
	xor a5, a6, a4
	addi a4, zero, 1
	sltu a4, a5, a4
	mul a3, a3, a4
	add a2, a2, a3
	sd a2, 88(s0)
	addi sp, sp, -16
	sd ra, 8(sp)
	ld a0, 0(s0)
	sd a0, 96(s0)
	ld a1, 8(s0)
	slli a1, a1, 2
	sd a1, 104(s0)
	ld a1, 96(s0)
	ld a2, 104(s0)
	addi a3, zero, 0
20:
	sb a3, 0(a1)
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 20b
	ld a1, 8(s0)
	slli a2, a1, 2
	add a1, a1, a2
	ld a0, 0(s0)
	add a0, a0, a1
	sd a0, 96(s0)
	ld a1, 8(s0)
	slli a1, a1, 2
	sd a1, 104(s0)
	ld a1, 96(s0)
	ld a2, 104(s0)
	addi a3, zero, 0
21:
	sb a3, 0(a1)
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 21b
22:
	addi sp, sp, -32
	ld t2, 56(s0)
	ld a0, 32(s0)
	ld a1, 64(s0)
	ld a2, 40(s0)
	ld a3, 48(s0)
	sub a0, a0, a1
	addi t1, sp, 0
	sd a0, 0(t1)
	sd a2, 8(t1)
	sd a3, 16(t1)
	sd t2, 24(t1)
	ld t2, 56(s0)
	ld t1, 32(t2)
	ld a1, 8(s0)
	slli a5, a1, 2
	ld a0, 0(s0)
	add a5, a5, a0
	mul a6, a1, t1
	add a0, a5, a6
	ld a2, 16(s0)
	addi a3, t2, 48
	addi a4, zero, 8
	ld a7, 24(s0)
	ld t0, 64(s0)
	add a7, a7, t0
	call {vg_rsa_prime_search}
	addi sp, sp, 32
	slli a0, a0, 32
	srli a0, a0, 32
	ld t1, 16(s0)
	ld t1, 0(t1)
	ld t2, 64(s0)
	add t2, t2, t1
	sd t2, 64(s0)
	beqz a0, 23f
	addi t2, a0, -3
	beqz t2, 25f
	beqz t1, 27f
	ld t2, 56(s0)
	ld t1, 32(t2)
	beqz t1, 29f
	addi sp, sp, -80
	ld a0, 0(s0)
	ld a1, 8(s0)
	ld t2, 56(s0)
	ld a2, 40(s0)
	ld a3, 48(s0)
	slli a4, a1, 2
	slli a5, a1, 1
	add a4, a4, a5
	add a4, a0, a4
	add a5, a4, a1
	add a6, a5, a1
	addi a7, t2, 48
	addi t0, zero, 8
	addi t1, sp, 0
	sd a4, 0(t1)
	sd a1, 8(t1)
	sd a5, 16(t1)
	sd a1, 24(t1)
	sd a6, 32(t1)
	sd a1, 40(t1)
	sd a7, 48(t1)
	sd t0, 56(t1)
	sd a2, 64(t1)
	sd a3, 72(t1)
	ld a5, 8(s0)
	ld a0, 0(s0)
	slli a1, a5, 1
	add a2, a0, a1
	addi a3, a1, 0
	add a4, a2, a1
	add a6, a4, a5
	addi a7, a5, 0
	call {vg_rsa_keygen_key}
	addi sp, sp, 80
	slli a0, a0, 32
	srli a0, a0, 32
	addi t1, a0, -1
	beqz t1, 211f
	addi t1, a0, -2
	beqz t1, 213f
	ld a0, 0(s0)
	sd a0, 96(s0)
	ld a1, 8(s0)
	slli a2, a1, 3
	add a2, a2, a1
	sd a2, 104(s0)
	ld a1, 96(s0)
	ld a2, 104(s0)
	addi a3, zero, 0
215:
	sb a3, 0(a1)
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 215b
	ld t2, 56(s0)
	addi t1, zero, 0
	sd t1, 32(t2)
	sd t1, 40(t2)
	addi t1, zero, 2
	sd t1, 80(s0)
	j 214f
213:
	ld t2, 56(s0)
	ld t1, 88(s0)
	sd t1, 0(t2)
	addi t1, zero, 0
	sd t1, 32(t2)
	addi t1, zero, 4
	sd t1, 80(s0)
214:
	j 212f
211:
	ld t2, 56(s0)
	addi t1, zero, 0
	sd t1, 32(t2)
	sd t1, 40(t2)
	addi t1, zero, 1
	sd t1, 80(s0)
212:
	j 210f
29:
	ld t2, 56(s0)
	ld t1, 88(s0)
	sd t1, 0(t2)
	addi t1, zero, 1
	sd t1, 32(t2)
	addi t1, zero, 4
	sd t1, 80(s0)
210:
	j 28f
27:
	ld a0, 0(s0)
	sd a0, 96(s0)
	ld a1, 8(s0)
	slli a2, a1, 3
	add a2, a2, a1
	sd a2, 104(s0)
	ld a1, 96(s0)
	ld a2, 104(s0)
	addi a3, zero, 0
216:
	sb a3, 0(a1)
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 216b
	ld t2, 56(s0)
	addi t1, zero, 0
	sd t1, 32(t2)
	sd t1, 40(t2)
	addi t1, zero, 3
	sd t1, 80(s0)
28:
	j 26f
25:
	ld t2, 56(s0)
	ld t1, 40(t2)
	srli a7, t1, 1
	beqz a7, 217f
	addi t1, t1, -1
	sd t1, 40(t2)
	ld t2, 56(s0)
	ld t1, 88(s0)
	sd t1, 0(t2)
	addi t1, zero, 0
	sd t1, 32(t2)
	addi t1, zero, 4
	sd t1, 80(s0)
	j 218f
217:
	ld a0, 0(s0)
	sd a0, 96(s0)
	ld a1, 8(s0)
	slli a2, a1, 3
	add a2, a2, a1
	sd a2, 104(s0)
	ld a1, 96(s0)
	ld a2, 104(s0)
	addi a3, zero, 0
219:
	sb a3, 0(a1)
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 219b
	ld t2, 56(s0)
	addi t1, zero, 0
	sd t1, 32(t2)
	sd t1, 40(t2)
	addi t1, zero, 3
	sd t1, 80(s0)
218:
26:
	j 24f
23:
	sd a0, 80(s0)
24:
	ld a6, 80(s0)
	addi a6, a6, -4
	beqz a6, 22b
	ld ra, 8(sp)
	addi sp, sp, 16
	ld a2, 16(s0)
	ld a3, 64(s0)
	sd a3, 0(a2)
	ld a0, 80(s0)
	ld s0, 72(s0)
	addi sp, sp, 112
	ret
	.option pop
