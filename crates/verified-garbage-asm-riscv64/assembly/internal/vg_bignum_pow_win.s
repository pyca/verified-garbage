// The functions of `src/internal/vg_bignum_pow_win.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_bignum_pow_win:
	.option push
	.option arch, +m, +c
	srli t0, s5, 3
	addi t0, t0, -2
	ld s3, 0(a7)
	addi s0, s3, 0
	mul s1, s3, s0
	addi s2, zero, 2
	sub s1, s2, s1
	mul s0, s0, s1
	mul s1, s3, s0
	addi s2, zero, 2
	sub s1, s2, s1
	mul s0, s0, s1
	mul s1, s3, s0
	addi s2, zero, 2
	sub s1, s2, s1
	mul s0, s0, s1
	mul s1, s3, s0
	addi s2, zero, 2
	sub s1, s2, s1
	mul s0, s0, s1
	mul s1, s3, s0
	addi s2, zero, 2
	sub s1, s2, s1
	mul s0, s0, s1
	addi s1, zero, 0
	sub t1, s1, s0
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t5, t0, 0
	addi s0, zero, 0
20:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 20b
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi s0, zero, 1
	sd s0, 0(t3)
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	addi a4, a7, 0
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
	addi a0, a7, 0
21:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 21b
22:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	ld a6, 8(a4)
	ld a7, 8(a0)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a0)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 23f
25:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 25b
	j 24f
23:
24:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 26f
28:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 16(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 24(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 24(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 8(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 24(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 32(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 32(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 16(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 32(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 40(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 40(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 28b
	j 27f
26:
27:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 22b
	slli s2, t0, 3
	addi s2, s2, 16
	add a6, a5, s2
	slli s3, s2, 1
	sub a7, a5, s3
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
29:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 29b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
210:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 210b
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a4, a7, 0
	add a4, a4, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
	addi a0, a7, 0
211:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 211b
212:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	ld a6, 8(a4)
	ld a7, 8(a0)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a0)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 213f
215:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 215b
	j 214f
213:
214:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 216f
218:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 16(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 24(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 24(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 8(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 24(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 32(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 32(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 16(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 32(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 40(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 40(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 218b
	j 217f
216:
217:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 212b
	slli s2, t0, 3
	addi s2, s2, 16
	add a6, a5, s2
	slli s3, s2, 1
	sub a7, a5, s3
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
219:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 219b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
220:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 220b
	addi s4, zero, -1
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
221:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 221b
	addi s7, zero, 2
222:
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a4, a7, 0
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
	addi a0, a7, 0
223:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 223b
224:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	ld a6, 8(a4)
	ld a7, 8(a0)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a0)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 225f
227:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 227b
	j 226f
225:
226:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 228f
230:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 16(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 24(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 24(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 8(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 24(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 32(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 32(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 16(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 32(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 40(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 40(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 230b
	j 229f
228:
229:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 224b
	slli s2, t0, 3
	addi s2, s2, 16
	add a6, a5, s2
	slli s3, s2, 1
	sub a7, a5, s3
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
231:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 231b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
232:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 232b
	addi s4, zero, -1
	addi t2, s7, 8
	mul t2, t2, s5
	add a2, t2, a7
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
233:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 233b
	addi s7, s7, 1
	addi t2, s7, -16
	bnez t2, 222b
	addi s4, zero, -1
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
234:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 234b
235:
	lbu s7, 0(s9)
	slli s7, s7, 56
	addi s9, s9, 1
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
236:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 236b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
237:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 238f
240:
	ld s2, 0(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 8(a0)
	sltu s1, a4, s1
	sd a4, 0(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 8(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 16(a0)
	add s3, a4, s3
	sd s4, 8(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 16(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 24(a0)
	sltu s1, a4, s1
	sd a4, 16(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 24(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 32(a0)
	add s3, a4, s3
	sd s4, 24(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 32(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 40(a0)
	sltu s1, a4, s1
	sd a4, 32(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 40(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 48(a0)
	add s3, a4, s3
	sd s4, 40(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 48(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 56(a0)
	sltu s1, a4, s1
	sd a4, 48(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 56(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 64(a0)
	add s3, a4, s3
	sd s4, 56(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 240b
	j 239f
238:
239:
	beqz t6, 241f
243:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 243b
	j 242f
241:
242:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 237b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
244:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 244b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
245:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 246f
248:
	ld s2, 0(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 8(a0)
	sltu s1, a4, s1
	sd a4, 0(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 8(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 16(a0)
	add s3, a4, s3
	sd s4, 8(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 16(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 24(a0)
	sltu s1, a4, s1
	sd a4, 16(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 24(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 32(a0)
	add s3, a4, s3
	sd s4, 24(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 32(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 40(a0)
	sltu s1, a4, s1
	sd a4, 32(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 40(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 48(a0)
	add s3, a4, s3
	sd s4, 40(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 48(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 56(a0)
	sltu s1, a4, s1
	sd a4, 48(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 56(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 64(a0)
	add s3, a4, s3
	sd s4, 56(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 248b
	j 247f
246:
247:
	beqz t6, 249f
251:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 251b
	j 250f
249:
250:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	slli s2, t0, 3
	sub a0, a0, s2
	bnez t2, 245b
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a7, a5, s2
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
252:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 252b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
253:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 253b
	slli t3, t0, 3
	sub a5, a5, t3
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
254:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 254b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
255:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 256f
258:
	ld s2, 0(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 8(a0)
	sltu s1, a4, s1
	sd a4, 0(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 8(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 16(a0)
	add s3, a4, s3
	sd s4, 8(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 16(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 24(a0)
	sltu s1, a4, s1
	sd a4, 16(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 24(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 32(a0)
	add s3, a4, s3
	sd s4, 24(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 32(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 40(a0)
	sltu s1, a4, s1
	sd a4, 32(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 40(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 48(a0)
	add s3, a4, s3
	sd s4, 40(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 48(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 56(a0)
	sltu s1, a4, s1
	sd a4, 48(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 56(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 64(a0)
	add s3, a4, s3
	sd s4, 56(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 258b
	j 257f
256:
257:
	beqz t6, 259f
261:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 261b
	j 260f
259:
260:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 255b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
262:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 262b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
263:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 264f
266:
	ld s2, 0(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 8(a0)
	sltu s1, a4, s1
	sd a4, 0(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 8(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 16(a0)
	add s3, a4, s3
	sd s4, 8(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 16(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 24(a0)
	sltu s1, a4, s1
	sd a4, 16(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 24(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 32(a0)
	add s3, a4, s3
	sd s4, 24(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 32(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 40(a0)
	sltu s1, a4, s1
	sd a4, 32(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 40(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 48(a0)
	add s3, a4, s3
	sd s4, 40(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 48(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 56(a0)
	sltu s1, a4, s1
	sd a4, 48(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 56(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 64(a0)
	add s3, a4, s3
	sd s4, 56(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 266b
	j 265f
264:
265:
	beqz t6, 267f
269:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 269b
	j 268f
267:
268:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	slli s2, t0, 3
	sub a0, a0, s2
	bnez t2, 263b
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a7, a5, s2
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
270:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 270b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
271:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 271b
	slli t3, t0, 3
	sub a5, a5, t3
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
272:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 272b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
273:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 274f
276:
	ld s2, 0(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 8(a0)
	sltu s1, a4, s1
	sd a4, 0(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 8(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 16(a0)
	add s3, a4, s3
	sd s4, 8(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 16(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 24(a0)
	sltu s1, a4, s1
	sd a4, 16(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 24(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 32(a0)
	add s3, a4, s3
	sd s4, 24(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 32(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 40(a0)
	sltu s1, a4, s1
	sd a4, 32(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 40(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 48(a0)
	add s3, a4, s3
	sd s4, 40(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 48(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 56(a0)
	sltu s1, a4, s1
	sd a4, 48(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 56(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 64(a0)
	add s3, a4, s3
	sd s4, 56(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 276b
	j 275f
274:
275:
	beqz t6, 277f
279:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 279b
	j 278f
277:
278:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 273b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
280:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 280b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
281:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 282f
284:
	ld s2, 0(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 8(a0)
	sltu s1, a4, s1
	sd a4, 0(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 8(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 16(a0)
	add s3, a4, s3
	sd s4, 8(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 16(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 24(a0)
	sltu s1, a4, s1
	sd a4, 16(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 24(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 32(a0)
	add s3, a4, s3
	sd s4, 24(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 32(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 40(a0)
	sltu s1, a4, s1
	sd a4, 32(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 40(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 48(a0)
	add s3, a4, s3
	sd s4, 40(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 48(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 56(a0)
	sltu s1, a4, s1
	sd a4, 48(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 56(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 64(a0)
	add s3, a4, s3
	sd s4, 56(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 284b
	j 283f
282:
283:
	beqz t6, 285f
287:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 287b
	j 286f
285:
286:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	slli s2, t0, 3
	sub a0, a0, s2
	bnez t2, 281b
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a7, a5, s2
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
288:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 288b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
289:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 289b
	slli t3, t0, 3
	sub a5, a5, t3
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
290:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 290b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
291:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 292f
294:
	ld s2, 0(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 8(a0)
	sltu s1, a4, s1
	sd a4, 0(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 8(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 16(a0)
	add s3, a4, s3
	sd s4, 8(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 16(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 24(a0)
	sltu s1, a4, s1
	sd a4, 16(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 24(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 32(a0)
	add s3, a4, s3
	sd s4, 24(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 32(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 40(a0)
	sltu s1, a4, s1
	sd a4, 32(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 40(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 48(a0)
	add s3, a4, s3
	sd s4, 40(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 48(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 56(a0)
	sltu s1, a4, s1
	sd a4, 48(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 56(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 64(a0)
	add s3, a4, s3
	sd s4, 56(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 294b
	j 293f
292:
293:
	beqz t6, 295f
297:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 297b
	j 296f
295:
296:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 291b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
298:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 298b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
299:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2100f
2102:
	ld s2, 0(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 8(a0)
	sltu s1, a4, s1
	sd a4, 0(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 8(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 16(a0)
	add s3, a4, s3
	sd s4, 8(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 16(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 24(a0)
	sltu s1, a4, s1
	sd a4, 16(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 24(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 32(a0)
	add s3, a4, s3
	sd s4, 24(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 32(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 40(a0)
	sltu s1, a4, s1
	sd a4, 32(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 40(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 48(a0)
	add s3, a4, s3
	sd s4, 40(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 48(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 56(a0)
	sltu s1, a4, s1
	sd a4, 48(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 56(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 64(a0)
	add s3, a4, s3
	sd s4, 56(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2102b
	j 2101f
2100:
2101:
	beqz t6, 2103f
2105:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2105b
	j 2104f
2103:
2104:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	slli s2, t0, 3
	sub a0, a0, s2
	bnez t2, 299b
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a7, a5, s2
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2106:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2106b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2107:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2107b
	slli t3, t0, 3
	sub a5, a5, t3
	srli a1, s7, 60
	slli t3, s5, 3
	add t3, a7, t3
	slli s4, s5, 2
	add s4, s4, s5
	add s4, a7, s4
	addi t5, t0, 0
2108:
	addi s1, t3, 0
	addi s0, zero, 0
	addi s3, zero, 0
	addi t6, zero, 1
	sll t6, t6, a1
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	sd s0, 0(s4)
	addi s4, s4, 8
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2108b
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a4, a7, 0
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
	addi a0, a7, 0
2109:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2109b
2110:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	ld a6, 8(a4)
	ld a7, 8(a0)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a0)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2111f
2113:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2113b
	j 2112f
2111:
2112:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2114f
2116:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 16(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 24(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 24(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 8(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 24(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 32(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 32(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 16(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 32(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 40(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 40(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2116b
	j 2115f
2114:
2115:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 2110b
	slli s2, t0, 3
	addi s2, s2, 16
	add a6, a5, s2
	slli s3, s2, 1
	sub a7, a5, s3
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2117:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2117b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2118:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2118b
	slli s7, s7, 4
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
2119:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2119b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2120:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2121f
2123:
	ld s2, 0(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 8(a0)
	sltu s1, a4, s1
	sd a4, 0(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 8(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 16(a0)
	add s3, a4, s3
	sd s4, 8(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 16(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 24(a0)
	sltu s1, a4, s1
	sd a4, 16(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 24(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 32(a0)
	add s3, a4, s3
	sd s4, 24(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 32(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 40(a0)
	sltu s1, a4, s1
	sd a4, 32(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 40(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 48(a0)
	add s3, a4, s3
	sd s4, 40(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 48(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 56(a0)
	sltu s1, a4, s1
	sd a4, 48(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 56(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 64(a0)
	add s3, a4, s3
	sd s4, 56(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2123b
	j 2122f
2121:
2122:
	beqz t6, 2124f
2126:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2126b
	j 2125f
2124:
2125:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2120b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2127:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2127b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2128:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2129f
2131:
	ld s2, 0(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 8(a0)
	sltu s1, a4, s1
	sd a4, 0(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 8(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 16(a0)
	add s3, a4, s3
	sd s4, 8(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 16(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 24(a0)
	sltu s1, a4, s1
	sd a4, 16(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 24(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 32(a0)
	add s3, a4, s3
	sd s4, 24(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 32(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 40(a0)
	sltu s1, a4, s1
	sd a4, 32(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 40(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 48(a0)
	add s3, a4, s3
	sd s4, 40(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 48(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 56(a0)
	sltu s1, a4, s1
	sd a4, 48(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 56(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 64(a0)
	add s3, a4, s3
	sd s4, 56(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2131b
	j 2130f
2129:
2130:
	beqz t6, 2132f
2134:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2134b
	j 2133f
2132:
2133:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	slli s2, t0, 3
	sub a0, a0, s2
	bnez t2, 2128b
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a7, a5, s2
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2135:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2135b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2136:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2136b
	slli t3, t0, 3
	sub a5, a5, t3
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
2137:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2137b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2138:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2139f
2141:
	ld s2, 0(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 8(a0)
	sltu s1, a4, s1
	sd a4, 0(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 8(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 16(a0)
	add s3, a4, s3
	sd s4, 8(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 16(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 24(a0)
	sltu s1, a4, s1
	sd a4, 16(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 24(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 32(a0)
	add s3, a4, s3
	sd s4, 24(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 32(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 40(a0)
	sltu s1, a4, s1
	sd a4, 32(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 40(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 48(a0)
	add s3, a4, s3
	sd s4, 40(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 48(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 56(a0)
	sltu s1, a4, s1
	sd a4, 48(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 56(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 64(a0)
	add s3, a4, s3
	sd s4, 56(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2141b
	j 2140f
2139:
2140:
	beqz t6, 2142f
2144:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2144b
	j 2143f
2142:
2143:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2138b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2145:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2145b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2146:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2147f
2149:
	ld s2, 0(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 8(a0)
	sltu s1, a4, s1
	sd a4, 0(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 8(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 16(a0)
	add s3, a4, s3
	sd s4, 8(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 16(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 24(a0)
	sltu s1, a4, s1
	sd a4, 16(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 24(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 32(a0)
	add s3, a4, s3
	sd s4, 24(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 32(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 40(a0)
	sltu s1, a4, s1
	sd a4, 32(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 40(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 48(a0)
	add s3, a4, s3
	sd s4, 40(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 48(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 56(a0)
	sltu s1, a4, s1
	sd a4, 48(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 56(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 64(a0)
	add s3, a4, s3
	sd s4, 56(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2149b
	j 2148f
2147:
2148:
	beqz t6, 2150f
2152:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2152b
	j 2151f
2150:
2151:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	slli s2, t0, 3
	sub a0, a0, s2
	bnez t2, 2146b
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a7, a5, s2
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2153:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2153b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2154:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2154b
	slli t3, t0, 3
	sub a5, a5, t3
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
2155:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2155b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2156:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2157f
2159:
	ld s2, 0(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 8(a0)
	sltu s1, a4, s1
	sd a4, 0(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 8(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 16(a0)
	add s3, a4, s3
	sd s4, 8(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 16(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 24(a0)
	sltu s1, a4, s1
	sd a4, 16(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 24(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 32(a0)
	add s3, a4, s3
	sd s4, 24(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 32(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 40(a0)
	sltu s1, a4, s1
	sd a4, 32(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 40(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 48(a0)
	add s3, a4, s3
	sd s4, 40(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 48(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 56(a0)
	sltu s1, a4, s1
	sd a4, 48(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 56(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 64(a0)
	add s3, a4, s3
	sd s4, 56(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2159b
	j 2158f
2157:
2158:
	beqz t6, 2160f
2162:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2162b
	j 2161f
2160:
2161:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2156b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2163:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2163b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2164:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2165f
2167:
	ld s2, 0(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 8(a0)
	sltu s1, a4, s1
	sd a4, 0(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 8(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 16(a0)
	add s3, a4, s3
	sd s4, 8(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 16(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 24(a0)
	sltu s1, a4, s1
	sd a4, 16(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 24(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 32(a0)
	add s3, a4, s3
	sd s4, 24(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 32(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 40(a0)
	sltu s1, a4, s1
	sd a4, 32(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 40(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 48(a0)
	add s3, a4, s3
	sd s4, 40(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 48(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 56(a0)
	sltu s1, a4, s1
	sd a4, 48(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 56(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 64(a0)
	add s3, a4, s3
	sd s4, 56(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2167b
	j 2166f
2165:
2166:
	beqz t6, 2168f
2170:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2170b
	j 2169f
2168:
2169:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	slli s2, t0, 3
	sub a0, a0, s2
	bnez t2, 2164b
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a7, a5, s2
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2171:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2171b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2172:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2172b
	slli t3, t0, 3
	sub a5, a5, t3
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi t3, a5, 0
	add t5, t0, t0
	addi t5, t5, 2
	addi s0, zero, 0
2173:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2173b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2174:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2175f
2177:
	ld s2, 0(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 8(a0)
	sltu s1, a4, s1
	sd a4, 0(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 8(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 16(a0)
	add s3, a4, s3
	sd s4, 8(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 16(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 24(a0)
	sltu s1, a4, s1
	sd a4, 16(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 24(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 32(a0)
	add s3, a4, s3
	sd s4, 24(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 32(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 40(a0)
	sltu s1, a4, s1
	sd a4, 32(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 40(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 48(a0)
	add s3, a4, s3
	sd s4, 40(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 48(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 56(a0)
	sltu s1, a4, s1
	sd a4, 48(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 56(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 64(a0)
	add s3, a4, s3
	sd s4, 56(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2177b
	j 2176f
2175:
2176:
	beqz t6, 2178f
2180:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2180b
	j 2179f
2178:
2179:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2174b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2181:
	ld s2, 0(t3)
	ld s3, 8(t3)
	srli s4, s2, 63
	slli s2, s2, 1
	add s2, s2, t2
	srli t2, s3, 63
	slli s3, s3, 1
	add s3, s3, s4
	ld s4, 0(a0)
	add s1, s1, s2
	sltu s2, s1, s2
	mul s0, s4, s4
	mulhu s4, s4, s4
	add s4, s4, s2
	add s0, s0, s1
	sltu s2, s0, s1
	add s4, s4, s2
	add s3, s3, s4
	sltu s1, s3, s4
	sd s0, 0(t3)
	sd s3, 8(t3)
	addi t3, t3, 16
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2181b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2182:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2183f
2185:
	ld s2, 0(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 8(a0)
	sltu s1, a4, s1
	sd a4, 0(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 8(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 16(a0)
	add s3, a4, s3
	sd s4, 8(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 16(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 24(a0)
	sltu s1, a4, s1
	sd a4, 16(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 24(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 32(a0)
	add s3, a4, s3
	sd s4, 24(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 32(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 40(a0)
	sltu s1, a4, s1
	sd a4, 32(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 40(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 48(a0)
	add s3, a4, s3
	sd s4, 40(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	ld s2, 48(t4)
	mul s3, s0, a7
	mulhu s4, s0, a7
	add s3, s3, s2
	add a4, s3, s1
	ld a7, 56(a0)
	sltu s1, a4, s1
	sd a4, 48(t4)
	mul a4, s0, a7
	sltu s2, s3, s2
	add s2, s4, s2
	add s2, s2, s1
	ld s3, 56(t4)
	add s4, a4, s3
	mulhu a4, s0, a7
	sltu s3, s4, s3
	add s4, s4, s2
	ld a7, 64(a0)
	add s3, a4, s3
	sd s4, 56(t4)
	sltu s2, s4, s2
	add s1, s3, s2
	addi t4, t4, 64
	addi a0, a0, 64
	addi t5, t5, -1
	bnez t5, 2185b
	j 2184f
2183:
2184:
	beqz t6, 2186f
2188:
	ld s4, 0(t4)
	mul s3, s0, a7
	mulhu s2, s0, a7
	ld a7, 8(a0)
	add s3, s3, s4
	sltu s4, s3, s4
	add s2, s2, s4
	add s3, s3, s1
	sltu s4, s3, s1
	add s1, s2, s4
	sd s3, 0(t4)
	addi t4, t4, 8
	addi a0, a0, 8
	addi t6, t6, -1
	bnez t6, 2188b
	j 2187f
2186:
2187:
	ld s2, 0(t4)
	add s1, s1, s2
	sltu s3, s1, s2
	add s1, s1, a1
	sltu s2, s1, a1
	add a1, s3, s2
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, -1
	slli s2, t0, 3
	sub a0, a0, s2
	bnez t2, 2182b
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a7, a5, s2
	slli t3, t0, 3
	add a5, a5, t3
	add t4, a5, t3
	sd a1, 0(t4)
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2189:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2189b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2190:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2190b
	slli t3, t0, 3
	sub a5, a5, t3
	srli a1, s7, 60
	slli t3, s5, 3
	add t3, a7, t3
	slli s4, s5, 2
	add s4, s4, s5
	add s4, a7, s4
	addi t5, t0, 0
2191:
	addi s1, t3, 0
	addi s0, zero, 0
	addi s3, zero, 0
	addi t6, zero, 1
	sll t6, t6, a1
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	srli t6, t6, 1
	add s1, s1, s5
	ld s2, 0(s1)
	andi t2, t6, 1
	sub t2, s3, t2
	and s2, s2, t2
	or s0, s0, s2
	sd s0, 0(s4)
	addi s4, s4, 8
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2191b
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a4, a7, 0
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
	addi a0, a7, 0
2192:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2192b
2193:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	ld a6, 8(a4)
	ld a7, 8(a0)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a0)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2194f
2196:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2196b
	j 2195f
2194:
2195:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2197f
2199:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 16(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 24(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 24(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 8(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 24(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 32(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 32(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 16(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 32(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 40(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 40(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2199b
	j 2198f
2197:
2198:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 2193b
	slli s2, t0, 3
	addi s2, s2, 16
	add a6, a5, s2
	slli s3, s2, 1
	sub a7, a5, s3
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2200:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2200b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2201:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2201b
	slli s7, s7, 4
	addi s10, s10, -1
	bnez s10, 235b
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	add a3, a3, s5
	addi a4, a7, 0
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	add a4, a4, s5
	addi a5, a7, 0
	add a5, a5, s5
	add a5, a5, s5
	addi a6, a7, 0
	add a6, a6, s5
	add a6, a6, s5
	add a6, a6, s5
	addi a1, t0, 0
	addi t3, a5, 0
	addi t5, t0, 1
	addi s0, zero, 0
	addi a0, a7, 0
2202:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2202b
2203:
	ld t6, 0(a3)
	addi a3, a3, 8
	ld s3, 0(a4)
	ld s2, 0(a5)
	ld a6, 8(a4)
	ld a7, 8(a0)
	mul s0, t6, s3
	mulhu s3, t6, s3
	add s2, s2, s0
	sltu s4, s2, s0
	add s0, s3, s4
	mul t2, s2, t1
	ld s3, 0(a0)
	mul s1, t2, s3
	mulhu s3, t2, s3
	add s1, s1, s2
	sltu s4, s1, s2
	add s1, s3, s4
	addi t3, a5, 0
	addi t4, a4, 0
	addi t5, t0, -1
	andi t5, t5, 3
	beqz t5, 2204f
2206:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2206b
	j 2205f
2204:
2205:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2207f
2209:
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 8(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 16(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 16(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 0(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 16(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 24(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 24(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 8(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 24(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 32(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 32(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 16(t3)
	mul s2, t6, a6
	mulhu s3, t6, a6
	mul s4, t2, a7
	ld a6, 32(t3)
	add s0, s0, a6
	sltu a6, s0, a6
	add s2, s2, s0
	mulhu a7, t2, a7
	add s1, s1, s2
	sltu s0, s2, s0
	add s4, s4, s1
	add s3, s3, a6
	add s0, s3, s0
	ld a6, 40(t4)
	sltu s2, s1, s2
	add s2, a7, s2
	ld a7, 40(a0)
	sltu s3, s4, s1
	add s1, s2, s3
	sd s4, 24(t3)
	addi t3, t3, 32
	addi t4, t4, 32
	addi a0, a0, 32
	addi t5, t5, -1
	bnez t5, 2209b
	j 2208f
2207:
2208:
	ld s2, 8(t3)
	add s0, s0, s2
	sltu s4, s0, s2
	add s0, s0, s1
	sltu s3, s0, s1
	add s4, s4, s3
	sd s0, 0(t3)
	sd s4, 8(t3)
	slli s2, t0, 3
	sub a0, a0, s2
	addi a0, a0, 8
	addi a1, a1, -1
	bnez a1, 2203b
	slli s2, t0, 3
	addi s2, s2, 16
	add a6, a5, s2
	slli s3, s2, 1
	sub a7, a5, s3
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a7, 0
	addi t5, t0, 0
	addi s4, zero, 0
2210:
	ld s2, 0(t3)
	ld s3, 0(a0)
	sltu s0, s2, s3
	sub s2, s2, s3
	sltu s1, s2, s4
	sub s2, s2, s4
	or s4, s0, s1
	sd s2, 0(t4)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2210b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2211:
	ld s2, 0(t4)
	ld s3, 0(t3)
	xor s3, s3, s2
	and s3, s3, s4
	xor s3, s3, s2
	sd s3, 0(a0)
	addi t3, t3, 8
	addi t4, t4, 8
	addi a0, a0, 8
	addi t5, t5, -1
	bnez t5, 2211b
	ret
	.option pop
