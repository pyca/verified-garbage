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
	andi t2, t0, 7
	addi t3, t0, -16
	addi t4, zero, 33
	sltu t3, t3, t4
	xori t3, t3, 1
	or t2, t2, t3
	srli t3, s10, 32
	or t2, t2, t3
	beqz t2, 20f
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
22:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 22b
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
23:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 23b
24:
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
	beqz t5, 25f
27:
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
	bnez t5, 27b
	j 26f
25:
26:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 28f
210:
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
	bnez t5, 210b
	j 29f
28:
29:
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
	bnez a1, 24b
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
211:
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
	bnez t5, 211b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
212:
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
	bnez t5, 212b
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
213:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 213b
214:
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
	beqz t5, 215f
217:
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
	bnez t5, 217b
	j 216f
215:
216:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 218f
220:
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
	bnez t5, 220b
	j 219f
218:
219:
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
	bnez a1, 214b
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
221:
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
	bnez t5, 221b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
222:
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
	bnez t5, 222b
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
223:
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
	bnez t5, 223b
	addi s7, zero, 2
224:
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
225:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 225b
226:
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
	beqz t5, 227f
229:
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
	bnez t5, 229b
	j 228f
227:
228:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 230f
232:
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
	bnez t5, 232b
	j 231f
230:
231:
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
	bnez a1, 226b
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
233:
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
	bnez t5, 233b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
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
235:
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
	bnez t5, 235b
	addi s7, s7, 1
	addi t2, s7, -16
	bnez t2, 224b
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
236:
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
	bnez t5, 236b
237:
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
238:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 238b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
239:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 240f
242:
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
	bnez t5, 242b
	j 241f
240:
241:
	beqz t6, 243f
245:
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
	bnez t6, 245b
	j 244f
243:
244:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 239b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
246:
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
	bnez t5, 246b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
247:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 248f
250:
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
	bnez t5, 250b
	j 249f
248:
249:
	beqz t6, 251f
253:
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
	bnez t6, 253b
	j 252f
251:
252:
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
	bnez t2, 247b
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
254:
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
	bnez t5, 254b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
255:
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
	bnez t5, 255b
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
256:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 256b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
257:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 258f
260:
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
	bnez t5, 260b
	j 259f
258:
259:
	beqz t6, 261f
263:
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
	bnez t6, 263b
	j 262f
261:
262:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 257b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
264:
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
	bnez t5, 264b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
265:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 266f
268:
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
	bnez t5, 268b
	j 267f
266:
267:
	beqz t6, 269f
271:
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
	bnez t6, 271b
	j 270f
269:
270:
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
	bnez t2, 265b
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
272:
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
	bnez t5, 272b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
273:
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
	bnez t5, 273b
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
274:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 274b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
275:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 276f
278:
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
	bnez t5, 278b
	j 277f
276:
277:
	beqz t6, 279f
281:
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
	bnez t6, 281b
	j 280f
279:
280:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 275b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
282:
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
	bnez t5, 282b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
283:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 284f
286:
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
	bnez t5, 286b
	j 285f
284:
285:
	beqz t6, 287f
289:
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
	bnez t6, 289b
	j 288f
287:
288:
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
	bnez t2, 283b
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
290:
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
	bnez t5, 290b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
291:
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
	bnez t5, 291b
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
292:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 292b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
293:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 294f
296:
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
	bnez t5, 296b
	j 295f
294:
295:
	beqz t6, 297f
299:
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
	bnez t6, 299b
	j 298f
297:
298:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 293b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2100:
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
	bnez t5, 2100b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2101:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2102f
2104:
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
	bnez t5, 2104b
	j 2103f
2102:
2103:
	beqz t6, 2105f
2107:
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
	bnez t6, 2107b
	j 2106f
2105:
2106:
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
	bnez t2, 2101b
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
2108:
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
	bnez t5, 2108b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2109:
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
	bnez t5, 2109b
	slli t3, t0, 3
	sub a5, a5, t3
	srli a1, s7, 60
	addi t6, a1, 0
	slli s4, t6, 60
	srai s4, s4, 63
	andi t5, t6, 7
	addi t4, zero, 1
	sll t4, t4, t5
	slli a0, t4, 63
	srai a0, a0, 63
	slli a1, t4, 62
	srai a1, a1, 63
	slli a2, t4, 61
	srai a2, a2, 63
	slli a3, t4, 60
	srai a3, a3, 63
	slli a4, t4, 59
	srai a4, a4, 63
	slli a5, t4, 58
	srai a5, a5, 63
	slli a6, t4, 57
	srai a6, a6, 63
	slli t2, t4, 56
	srai t2, t2, 63
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t4, a7, 0
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	addi t5, t0, 1
	srli t5, t5, 1
2110:
	ld s0, 0(t3)
	and s0, s0, a0
	ld s1, 8(t3)
	and s1, s1, a0
	add t3, t3, s5
	ld t6, 0(t3)
	and t6, t6, a1
	or s0, s0, t6
	ld t6, 8(t3)
	and t6, t6, a1
	or s1, s1, t6
	add t3, t3, s5
	ld t6, 0(t3)
	and t6, t6, a2
	or s0, s0, t6
	ld t6, 8(t3)
	and t6, t6, a2
	or s1, s1, t6
	add t3, t3, s5
	ld t6, 0(t3)
	and t6, t6, a3
	or s0, s0, t6
	ld t6, 8(t3)
	and t6, t6, a3
	or s1, s1, t6
	add t3, t3, s5
	ld t6, 0(t3)
	and t6, t6, a4
	or s0, s0, t6
	ld t6, 8(t3)
	and t6, t6, a4
	or s1, s1, t6
	add t3, t3, s5
	ld t6, 0(t3)
	and t6, t6, a5
	or s0, s0, t6
	ld t6, 8(t3)
	and t6, t6, a5
	or s1, s1, t6
	add t3, t3, s5
	ld t6, 0(t3)
	and t6, t6, a6
	or s0, s0, t6
	ld t6, 8(t3)
	and t6, t6, a6
	or s1, s1, t6
	add t3, t3, s5
	ld t6, 0(t3)
	and t6, t6, t2
	or s0, s0, t6
	ld t6, 8(t3)
	and t6, t6, t2
	or s1, s1, t6
	add t3, t3, s5
	ld s2, 0(t3)
	and s2, s2, a0
	ld s3, 8(t3)
	and s3, s3, a0
	add t3, t3, s5
	ld t6, 0(t3)
	and t6, t6, a1
	or s2, s2, t6
	ld t6, 8(t3)
	and t6, t6, a1
	or s3, s3, t6
	add t3, t3, s5
	ld t6, 0(t3)
	and t6, t6, a2
	or s2, s2, t6
	ld t6, 8(t3)
	and t6, t6, a2
	or s3, s3, t6
	add t3, t3, s5
	ld t6, 0(t3)
	and t6, t6, a3
	or s2, s2, t6
	ld t6, 8(t3)
	and t6, t6, a3
	or s3, s3, t6
	add t3, t3, s5
	ld t6, 0(t3)
	and t6, t6, a4
	or s2, s2, t6
	ld t6, 8(t3)
	and t6, t6, a4
	or s3, s3, t6
	add t3, t3, s5
	ld t6, 0(t3)
	and t6, t6, a5
	or s2, s2, t6
	ld t6, 8(t3)
	and t6, t6, a5
	or s3, s3, t6
	add t3, t3, s5
	ld t6, 0(t3)
	and t6, t6, a6
	or s2, s2, t6
	ld t6, 8(t3)
	and t6, t6, a6
	or s3, s3, t6
	add t3, t3, s5
	ld t6, 0(t3)
	and t6, t6, t2
	or s2, s2, t6
	ld t6, 8(t3)
	and t6, t6, t2
	or s3, s3, t6
	add t3, t3, s5
	xor s2, s2, s0
	and s2, s2, s4
	xor s0, s0, s2
	xor s3, s3, s1
	and s3, s3, s4
	xor s1, s1, s3
	sd s0, 0(t4)
	sd s1, 8(t4)
	addi t4, t4, 16
	slli t6, s5, 4
	sub t3, t3, t6
	addi t3, t3, 16
	addi t5, t5, -1
	bnez t5, 2110b
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
2111:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2111b
2112:
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
	beqz t5, 2113f
2115:
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
	bnez t5, 2115b
	j 2114f
2113:
2114:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2116f
2118:
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
	bnez t5, 2118b
	j 2117f
2116:
2117:
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
	bnez a1, 2112b
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
2119:
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
	bnez t5, 2119b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2120:
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
	bnez t5, 2120b
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
2121:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2121b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2122:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2123f
2125:
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
	bnez t5, 2125b
	j 2124f
2123:
2124:
	beqz t6, 2126f
2128:
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
	bnez t6, 2128b
	j 2127f
2126:
2127:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2122b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2129:
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
	bnez t5, 2129b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2130:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2131f
2133:
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
	bnez t5, 2133b
	j 2132f
2131:
2132:
	beqz t6, 2134f
2136:
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
	bnez t6, 2136b
	j 2135f
2134:
2135:
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
	bnez t2, 2130b
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
2137:
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
	bnez t5, 2137b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2138:
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
	bnez t5, 2138b
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
2139:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2139b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2140:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2141f
2143:
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
	bnez t5, 2143b
	j 2142f
2141:
2142:
	beqz t6, 2144f
2146:
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
	bnez t6, 2146b
	j 2145f
2144:
2145:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2140b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2147:
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
	bnez t5, 2147b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2148:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2149f
2151:
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
	bnez t5, 2151b
	j 2150f
2149:
2150:
	beqz t6, 2152f
2154:
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
	bnez t6, 2154b
	j 2153f
2152:
2153:
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
	bnez t2, 2148b
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
2155:
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
	bnez t5, 2155b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2156:
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
	bnez t5, 2156b
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
2157:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2157b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2158:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2159f
2161:
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
	bnez t5, 2161b
	j 2160f
2159:
2160:
	beqz t6, 2162f
2164:
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
	bnez t6, 2164b
	j 2163f
2162:
2163:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2158b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2165:
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
	bnez t5, 2165b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2166:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2167f
2169:
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
	bnez t5, 2169b
	j 2168f
2167:
2168:
	beqz t6, 2170f
2172:
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
	bnez t6, 2172b
	j 2171f
2170:
2171:
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
	bnez t2, 2166b
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
2173:
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
	bnez t5, 2173b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2174:
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
	bnez t5, 2174b
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
2175:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2175b
	addi t3, a3, 0
	addi a1, t0, -1
	addi t2, a5, 8
2176:
	ld s0, 0(t3)
	addi s1, zero, 0
	addi a0, t3, 8
	addi t4, t2, 0
	addi t5, a1, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2177f
2179:
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
	bnez t5, 2179b
	j 2178f
2177:
2178:
	beqz t6, 2180f
2182:
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
	bnez t6, 2182b
	j 2181f
2180:
2181:
	sd s1, 0(t4)
	addi t3, t3, 8
	addi t2, t2, 16
	addi a1, a1, -1
	bnez a1, 2176b
	addi t3, a5, 0
	addi a0, a3, 0
	addi t5, t0, 0
	addi t2, zero, 0
	addi s1, zero, 0
2183:
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
	bnez t5, 2183b
	addi t3, a5, 0
	addi t2, t0, 0
	addi a1, zero, 0
	slli s2, t0, 3
	addi s2, s2, 16
	slli s2, s2, 1
	sub a0, a5, s2
2184:
	ld s0, 0(t3)
	mul s0, s0, t1
	addi s1, zero, 0
	addi t4, t3, 0
	addi t5, t0, 0
	andi t6, t5, 7
	srli t5, t5, 3
	ld a7, 0(a0)
	beqz t5, 2185f
2187:
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
	bnez t5, 2187b
	j 2186f
2185:
2186:
	beqz t6, 2188f
2190:
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
	bnez t6, 2190b
	j 2189f
2188:
2189:
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
	bnez t2, 2184b
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
2191:
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
	bnez t5, 2191b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2192:
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
	bnez t5, 2192b
	slli t3, t0, 3
	sub a5, a5, t3
	srli a1, s7, 60
	addi t6, a1, 0
	slli s4, t6, 60
	srai s4, s4, 63
	andi t5, t6, 7
	addi t4, zero, 1
	sll t4, t4, t5
	slli a0, t4, 63
	srai a0, a0, 63
	slli a1, t4, 62
	srai a1, a1, 63
	slli a2, t4, 61
	srai a2, a2, 63
	slli a3, t4, 60
	srai a3, a3, 63
	slli a4, t4, 59
	srai a4, a4, 63
	slli a5, t4, 58
	srai a5, a5, 63
	slli a6, t4, 57
	srai a6, a6, 63
	slli t2, t4, 56
	srai t2, t2, 63
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t4, a7, 0
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	addi t5, t0, 1
	srli t5, t5, 1
2193:
	ld s0, 0(t3)
	and s0, s0, a0
	ld s1, 8(t3)
	and s1, s1, a0
	add t3, t3, s5
	ld t6, 0(t3)
	and t6, t6, a1
	or s0, s0, t6
	ld t6, 8(t3)
	and t6, t6, a1
	or s1, s1, t6
	add t3, t3, s5
	ld t6, 0(t3)
	and t6, t6, a2
	or s0, s0, t6
	ld t6, 8(t3)
	and t6, t6, a2
	or s1, s1, t6
	add t3, t3, s5
	ld t6, 0(t3)
	and t6, t6, a3
	or s0, s0, t6
	ld t6, 8(t3)
	and t6, t6, a3
	or s1, s1, t6
	add t3, t3, s5
	ld t6, 0(t3)
	and t6, t6, a4
	or s0, s0, t6
	ld t6, 8(t3)
	and t6, t6, a4
	or s1, s1, t6
	add t3, t3, s5
	ld t6, 0(t3)
	and t6, t6, a5
	or s0, s0, t6
	ld t6, 8(t3)
	and t6, t6, a5
	or s1, s1, t6
	add t3, t3, s5
	ld t6, 0(t3)
	and t6, t6, a6
	or s0, s0, t6
	ld t6, 8(t3)
	and t6, t6, a6
	or s1, s1, t6
	add t3, t3, s5
	ld t6, 0(t3)
	and t6, t6, t2
	or s0, s0, t6
	ld t6, 8(t3)
	and t6, t6, t2
	or s1, s1, t6
	add t3, t3, s5
	ld s2, 0(t3)
	and s2, s2, a0
	ld s3, 8(t3)
	and s3, s3, a0
	add t3, t3, s5
	ld t6, 0(t3)
	and t6, t6, a1
	or s2, s2, t6
	ld t6, 8(t3)
	and t6, t6, a1
	or s3, s3, t6
	add t3, t3, s5
	ld t6, 0(t3)
	and t6, t6, a2
	or s2, s2, t6
	ld t6, 8(t3)
	and t6, t6, a2
	or s3, s3, t6
	add t3, t3, s5
	ld t6, 0(t3)
	and t6, t6, a3
	or s2, s2, t6
	ld t6, 8(t3)
	and t6, t6, a3
	or s3, s3, t6
	add t3, t3, s5
	ld t6, 0(t3)
	and t6, t6, a4
	or s2, s2, t6
	ld t6, 8(t3)
	and t6, t6, a4
	or s3, s3, t6
	add t3, t3, s5
	ld t6, 0(t3)
	and t6, t6, a5
	or s2, s2, t6
	ld t6, 8(t3)
	and t6, t6, a5
	or s3, s3, t6
	add t3, t3, s5
	ld t6, 0(t3)
	and t6, t6, a6
	or s2, s2, t6
	ld t6, 8(t3)
	and t6, t6, a6
	or s3, s3, t6
	add t3, t3, s5
	ld t6, 0(t3)
	and t6, t6, t2
	or s2, s2, t6
	ld t6, 8(t3)
	and t6, t6, t2
	or s3, s3, t6
	add t3, t3, s5
	xor s2, s2, s0
	and s2, s2, s4
	xor s0, s0, s2
	xor s3, s3, s1
	and s3, s3, s4
	xor s1, s1, s3
	sd s0, 0(t4)
	sd s1, 8(t4)
	addi t4, t4, 16
	slli t6, s5, 4
	sub t3, t3, t6
	addi t3, t3, 16
	addi t5, t5, -1
	bnez t5, 2193b
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
2194:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2194b
2195:
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
	beqz t5, 2196f
2198:
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
	bnez t5, 2198b
	j 2197f
2196:
2197:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2199f
2201:
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
	bnez t5, 2201b
	j 2200f
2199:
2200:
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
	bnez a1, 2195b
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
2202:
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
	bnez t5, 2202b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2203:
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
	bnez t5, 2203b
	slli s7, s7, 4
	addi s10, s10, -1
	bnez s10, 237b
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
2204:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2204b
2205:
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
	beqz t5, 2206f
2208:
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
	bnez t5, 2208b
	j 2207f
2206:
2207:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2209f
2211:
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
	bnez t5, 2211b
	j 2210f
2209:
2210:
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
	bnez a1, 2205b
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
2212:
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
	bnez t5, 2212b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2213:
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
	bnez t5, 2213b
	j 21f
20:
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
2214:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2214b
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
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	srli t2, t0, 3
	addi s0, zero, 1
	sll s0, s0, t2
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
	add a3, a3, s5
	add a3, a3, s5
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
2215:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2215b
2216:
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
	beqz t5, 2217f
2219:
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
	bnez t5, 2219b
	j 2218f
2217:
2218:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2220f
2222:
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
	bnez t5, 2222b
	j 2221f
2220:
2221:
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
	bnez a1, 2216b
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
2223:
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
	bnez t5, 2223b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2224:
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
	bnez t5, 2224b
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
2225:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2225b
2226:
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
	beqz t5, 2227f
2229:
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
	bnez t5, 2229b
	j 2228f
2227:
2228:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2230f
2232:
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
	bnez t5, 2232b
	j 2231f
2230:
2231:
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
	bnez a1, 2226b
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
2233:
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
	bnez t5, 2233b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2234:
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
	bnez t5, 2234b
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
2235:
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
	bnez t5, 2235b
	addi s7, zero, 1
2236:
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
2237:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2237b
2238:
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
	beqz t5, 2239f
2241:
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
	bnez t5, 2241b
	j 2240f
2239:
2240:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2242f
2244:
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
	bnez t5, 2244b
	j 2243f
2242:
2243:
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
	bnez a1, 2238b
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
2245:
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
	bnez t5, 2245b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2246:
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
	bnez t5, 2246b
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
2247:
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
	bnez t5, 2247b
	addi s7, s7, 1
	addi t2, s7, -16
	bnez t2, 2236b
	add t4, a7, s5
	add t4, t4, s5
	srli t2, s5, 3
	add t2, t2, s5
	addi t2, t2, -18
	addi s0, zero, 0
	add t4, t4, t2
	sd s0, 0(t4)
	sd s0, 8(t4)
	sd s0, 16(t4)
	add t4, t4, t2
	sd s0, 24(t4)
	sd s0, 32(t4)
	sd s0, 40(t4)
	addi s4, zero, -1
	addi a5, a7, 0
	addi a6, a7, 0
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2248:
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
	bnez t5, 2248b
	slli t3, s5, 2
	add t3, t3, s5
	add t3, t3, a7
	add t5, t3, s5
	addi t5, t5, -16
	addi s0, zero, 0
	sd s0, 0(t5)
	srli t2, s5, 3
	add t2, t2, s5
	addi t2, t2, -18
	srli t5, t2, 3
	add t4, a7, s5
	add t4, t4, s5
	addi s4, zero, -1
	srli s4, s4, 7
	addi t2, zero, 0
2249:
	srli s0, t2, 6
	slli s0, s0, 3
	add s0, s0, t3
	ld s1, 0(s0)
	ld s2, 8(s0)
	srl s1, s1, t2
	xori s3, t2, -1
	slli s2, s2, 1
	sll s2, s2, s3
	add s1, s1, s2
	and s1, s1, s4
	sd s1, 0(t4)
	addi t4, t4, 8
	addi t2, t2, 57
	addi t5, t5, -1
	bnez t5, 2249b
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
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2250:
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
	bnez t5, 2250b
	slli t3, s5, 2
	add t3, t3, s5
	add t3, t3, a7
	add t5, t3, s5
	addi t5, t5, -16
	addi s0, zero, 0
	sd s0, 0(t5)
	srli t2, s5, 3
	add t2, t2, s5
	addi t2, t2, -18
	srli t5, t2, 3
	add t4, a7, s5
	add t4, t4, s5
	add t4, t4, t2
	addi t4, t4, 24
	addi s4, zero, -1
	srli s4, s4, 7
	addi t2, zero, 0
2251:
	srli s0, t2, 6
	slli s0, s0, 3
	add s0, s0, t3
	ld s1, 0(s0)
	ld s2, 8(s0)
	srl s1, s1, t2
	xori s3, t2, -1
	slli s2, s2, 1
	sll s2, s2, s3
	add s1, s1, s2
	and s1, s1, s4
	sd s1, 0(t4)
	addi t4, t4, 8
	addi t2, t2, 57
	addi t5, t5, -1
	bnez t5, 2251b
	slli s10, s10, 3
2252:
2253:
	srli t2, s5, 3
	add t2, t2, s5
	addi t2, t2, -18
	add t3, a7, s5
	add t3, t3, s5
	add a7, t3, t2
	addi a7, a7, 24
	add s5, a7, t2
	addi s5, s5, 24
	sub t2, s5, a7
	addi t2, t2, -24
	slli t2, t2, 1
	add t4, s5, t2
	addi t3, s5, 0
	addi s0, zero, 0
2254:
	sd s0, 0(t3)
	sd s0, 8(t3)
	sd s0, 16(t3)
	addi t3, t3, 24
	bne t3, t4, 2254b
	addi t4, zero, 0
2255:
	add a2, a7, t4
	add a0, s5, t4
	add a0, a0, t4
	ld s2, 0(a2)
	ld s3, 8(a2)
	ld s4, 16(a2)
	addi a1, a2, 24
	slli t2, s2, 7
	slli t3, s3, 7
	slli t4, s4, 7
	mulhu s1, t2, s3
	mul s0, s2, s3
	slli t0, s1, 57
	sub s0, s0, t0
	mulhu a3, t2, s4
	mul a2, s2, s4
	slli t0, a3, 57
	sub a2, a2, t0
	mulhu a5, t3, s4
	mul a4, s3, s4
	slli t0, a5, 57
	sub a4, a4, t0
	ld t0, 8(a0)
	ld t5, 16(a0)
	ld t6, 32(a0)
	add t0, t0, s0
	add t5, t5, s1
	add t5, t5, a2
	add s7, a3, a4
	add t6, t6, a5
	sd t0, 8(a0)
	sd t5, 16(a0)
	sd t6, 32(a0)
	addi t5, zero, 0
	addi t6, zero, 0
	addi a0, a0, 24
2256:
	mul s0, s4, t6
	mul s1, s3, t5
	mulhu a2, t3, t5
	ld a3, 0(a1)
	ld a4, 0(a0)
	mul a5, s2, a3
	mulhu a6, t4, t6
	add a2, a6, a2
	add s0, s0, s1
	mulhu s1, t2, a3
	add s1, a2, s1
	ld a2, 8(a0)
	mul a6, s4, t5
	slli t0, s1, 57
	add s0, s0, a5
	mul a5, s3, a3
	sub s0, s0, t0
	mulhu t0, t4, t5
	add a4, a4, s7
	add a5, a6, a5
	ld t6, 8(a1)
	add s0, a4, s0
	sd s0, 0(a0)
	mulhu s0, t3, a3
	mulhu a4, t2, t6
	mul a6, s2, t6
	add a5, a5, a6
	add s0, t0, s0
	mul a6, s4, a3
	add s0, s0, a4
	mulhu a3, t4, a3
	ld a4, 16(a0)
	slli t0, s0, 57
	sub a5, a5, t0
	mulhu t0, t3, t6
	add s1, a2, s1
	mul a2, s3, t6
	add s1, s1, a5
	sd s1, 8(a0)
	ld t5, 16(a1)
	mulhu s1, t2, t5
	add a2, a6, a2
	add a3, a3, t0
	mul a5, s2, t5
	add a2, a2, a5
	add s7, a3, s1
	add s0, a4, s0
	slli s1, s7, 57
	sub s1, a2, s1
	add s0, s0, s1
	sd s0, 16(a0)
	addi a0, a0, 24
	addi a1, a1, 24
	bne a1, s5, 2256b
	sub t2, s5, a7
	addi t2, t2, -24
	sub t4, a0, s5
	sub t4, t4, t2
	bne t4, t2, 2255b
	addi t6, zero, -1
	srli t6, t6, 7
	addi t5, zero, 0
	addi a0, s5, 0
	sub t2, s5, a7
	addi t2, t2, -24
	addi a1, a7, 0
	add t3, a7, t2
2257:
	ld s2, 0(a1)
	slli t2, s2, 7
	mulhu s1, t2, s2
	mul s0, s2, s2
	slli a2, s1, 57
	sub s0, s0, a2
	ld a3, 0(a0)
	ld a4, 8(a0)
	slli a3, a3, 1
	slli a4, a4, 1
	add a3, a3, t5
	add a3, a3, s0
	and a5, a3, t6
	srli t5, a3, 57
	sd a5, 0(a0)
	add a4, a4, s1
	add a4, a4, t5
	and a5, a4, t6
	srli t5, a4, 57
	sd a5, 8(a0)
	addi a0, a0, 16
	addi a1, a1, 8
	bne a1, t3, 2257b
	addi a0, s5, 0
2258:
	sub t2, s5, a7
	addi t2, t2, -24
	sub t2, a7, t2
	addi a1, t2, -24
	ld a4, 0(a1)
	ld a5, 8(a1)
	ld a6, 16(a1)
	addi t6, zero, -1
	srli t6, t6, 7
	ld s0, 0(a0)
	mul s2, s0, t1
	add s0, s0, t6
	slli t2, s2, 7
	and s2, s2, t6
	srli s0, s0, 57
	mulhu a3, t2, a4
	ld s1, 8(a0)
	add s0, s0, a3
	add s0, s0, s1
	mulhu a3, t2, a5
	mul a2, s2, a5
	slli t0, a3, 57
	sub a2, a2, t0
	add s0, s0, a2
	mul s3, s0, t1
	add s0, s0, t6
	slli t3, s3, 7
	and s3, s3, t6
	srli s0, s0, 57
	mulhu s1, t3, a4
	ld t5, 16(a0)
	add s0, s0, a3
	add s0, s0, t5
	add s0, s0, s1
	mulhu s7, t2, a6
	mul a2, s2, a6
	slli t0, s7, 57
	sub a2, a2, t0
	add s0, s0, a2
	mulhu a3, t3, a5
	mul a2, s3, a5
	slli t0, a3, 57
	sub a2, a2, t0
	add s0, s0, a2
	add s7, s7, a3
	mul s4, s0, t1
	add s0, s0, t6
	slli t4, s4, 7
	and s4, s4, t6
	srli s0, s0, 57
	mulhu a3, t4, a4
	add s7, s7, s0
	add s7, s7, a3
	addi t5, a6, 0
	addi t6, a5, 0
	addi a0, a0, 24
	addi a1, a1, 24
2259:
	mul s0, s4, t6
	mul s1, s3, t5
	mulhu a2, t3, t5
	ld a3, 0(a1)
	ld a4, 0(a0)
	mul a5, s2, a3
	mulhu a6, t4, t6
	add a2, a6, a2
	add s0, s0, s1
	mulhu s1, t2, a3
	add s1, a2, s1
	ld a2, 8(a0)
	mul a6, s4, t5
	slli t0, s1, 57
	add s0, s0, a5
	mul a5, s3, a3
	sub s0, s0, t0
	mulhu t0, t4, t5
	add a4, a4, s7
	add a5, a6, a5
	ld t6, 8(a1)
	add s0, a4, s0
	sd s0, 0(a0)
	mulhu s0, t3, a3
	mulhu a4, t2, t6
	mul a6, s2, t6
	add a5, a5, a6
	add s0, t0, s0
	mul a6, s4, a3
	add s0, s0, a4
	mulhu a3, t4, a3
	ld a4, 16(a0)
	slli t0, s0, 57
	sub a5, a5, t0
	mulhu t0, t3, t6
	add s1, a2, s1
	mul a2, s3, t6
	add s1, s1, a5
	sd s1, 8(a0)
	ld t5, 16(a1)
	mulhu s1, t2, t5
	add a2, a6, a2
	add a3, a3, t0
	mul a5, s2, t5
	add a2, a2, a5
	add s7, a3, s1
	add s0, a4, s0
	slli s1, s7, 57
	sub s1, a2, s1
	add s0, s0, s1
	sd s0, 16(a0)
	addi a0, a0, 24
	addi a1, a1, 24
	bne a1, a7, 2259b
	sub t2, s5, a7
	addi t2, t2, -24
	sub a0, a0, t2
	add t3, s5, t2
	bne a0, t3, 2258b
	sub t2, s5, a7
	addi t2, t2, -24
	add a0, s5, t2
	addi a1, a7, 0
	add t3, a0, t2
	addi t6, zero, -1
	srli t6, t6, 7
	addi t5, zero, 0
2260:
	ld s0, 0(a0)
	add s0, s0, t5
	and s1, s0, t6
	srli t5, s0, 57
	sd s1, 0(a1)
	ld s0, 8(a0)
	add s0, s0, t5
	and s1, s0, t6
	srli t5, s0, 57
	sd s1, 8(a1)
	ld s0, 16(a0)
	add s0, s0, t5
	and s1, s0, t6
	srli t5, s0, 57
	sd s1, 16(a1)
	addi a0, a0, 24
	addi a1, a1, 24
	bne a0, t3, 2260b
	sub t2, s5, a7
	addi t2, t2, -24
	sub t3, a7, t2
	addi t3, t3, -24
	addi t4, zero, 57
	mul t2, t2, t4
	srli t2, t2, 6
	addi s5, t2, 16
	sub a7, t3, s5
	sub a7, a7, s5
	srli t0, s5, 3
	addi t0, t0, -2
	addi s10, s10, -1
	andi t2, s10, 3
	bnez t2, 2253b
	lbu t6, 0(s9)
	srli t2, s10, 2
	andi t2, t2, 1
	slli s0, t2, 2
	srl t6, t6, s0
	andi t6, t6, 15
	xori t2, t2, 1
	add s9, s9, t2
	slli s4, t6, 60
	srai s4, s4, 63
	andi t5, t6, 7
	addi t4, zero, 1
	sll t4, t4, t5
	slli a0, t4, 63
	srai a0, a0, 63
	slli a1, t4, 62
	srai a1, a1, 63
	slli a2, t4, 61
	srai a2, a2, 63
	slli a3, t4, 60
	srai a3, a3, 63
	slli a4, t4, 59
	srai a4, a4, 63
	slli a5, t4, 58
	srai a5, a5, 63
	slli a6, t4, 57
	srai a6, a6, 63
	slli t2, t4, 56
	srai t2, t2, 63
	addi t3, a7, 0
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, s5
	addi t4, a7, 0
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	add t4, t4, s5
	addi t5, t0, 1
	srli t5, t5, 1
2261:
	ld s0, 0(t3)
	and s0, s0, a0
	ld s1, 8(t3)
	and s1, s1, a0
	add t3, t3, s5
	ld t6, 0(t3)
	and t6, t6, a1
	or s0, s0, t6
	ld t6, 8(t3)
	and t6, t6, a1
	or s1, s1, t6
	add t3, t3, s5
	ld t6, 0(t3)
	and t6, t6, a2
	or s0, s0, t6
	ld t6, 8(t3)
	and t6, t6, a2
	or s1, s1, t6
	add t3, t3, s5
	ld t6, 0(t3)
	and t6, t6, a3
	or s0, s0, t6
	ld t6, 8(t3)
	and t6, t6, a3
	or s1, s1, t6
	add t3, t3, s5
	ld t6, 0(t3)
	and t6, t6, a4
	or s0, s0, t6
	ld t6, 8(t3)
	and t6, t6, a4
	or s1, s1, t6
	add t3, t3, s5
	ld t6, 0(t3)
	and t6, t6, a5
	or s0, s0, t6
	ld t6, 8(t3)
	and t6, t6, a5
	or s1, s1, t6
	add t3, t3, s5
	ld t6, 0(t3)
	and t6, t6, a6
	or s0, s0, t6
	ld t6, 8(t3)
	and t6, t6, a6
	or s1, s1, t6
	add t3, t3, s5
	ld t6, 0(t3)
	and t6, t6, t2
	or s0, s0, t6
	ld t6, 8(t3)
	and t6, t6, t2
	or s1, s1, t6
	add t3, t3, s5
	ld s2, 0(t3)
	and s2, s2, a0
	ld s3, 8(t3)
	and s3, s3, a0
	add t3, t3, s5
	ld t6, 0(t3)
	and t6, t6, a1
	or s2, s2, t6
	ld t6, 8(t3)
	and t6, t6, a1
	or s3, s3, t6
	add t3, t3, s5
	ld t6, 0(t3)
	and t6, t6, a2
	or s2, s2, t6
	ld t6, 8(t3)
	and t6, t6, a2
	or s3, s3, t6
	add t3, t3, s5
	ld t6, 0(t3)
	and t6, t6, a3
	or s2, s2, t6
	ld t6, 8(t3)
	and t6, t6, a3
	or s3, s3, t6
	add t3, t3, s5
	ld t6, 0(t3)
	and t6, t6, a4
	or s2, s2, t6
	ld t6, 8(t3)
	and t6, t6, a4
	or s3, s3, t6
	add t3, t3, s5
	ld t6, 0(t3)
	and t6, t6, a5
	or s2, s2, t6
	ld t6, 8(t3)
	and t6, t6, a5
	or s3, s3, t6
	add t3, t3, s5
	ld t6, 0(t3)
	and t6, t6, a6
	or s2, s2, t6
	ld t6, 8(t3)
	and t6, t6, a6
	or s3, s3, t6
	add t3, t3, s5
	ld t6, 0(t3)
	and t6, t6, t2
	or s2, s2, t6
	ld t6, 8(t3)
	and t6, t6, t2
	or s3, s3, t6
	add t3, t3, s5
	xor s2, s2, s0
	and s2, s2, s4
	xor s0, s0, s2
	xor s3, s3, s1
	and s3, s3, s4
	xor s1, s1, s3
	sd s0, 0(t4)
	sd s1, 8(t4)
	addi t4, t4, 16
	slli t6, s5, 4
	sub t3, t3, t6
	addi t3, t3, 16
	addi t5, t5, -1
	bnez t5, 2261b
	slli t3, s5, 2
	add t3, t3, s5
	add t3, t3, a7
	add t5, t3, s5
	addi t5, t5, -16
	addi s0, zero, 0
	sd s0, 0(t5)
	srli t2, s5, 3
	add t2, t2, s5
	addi t2, t2, -18
	srli t5, t2, 3
	add t4, a7, s5
	add t4, t4, s5
	add t4, t4, t2
	addi t4, t4, 24
	add t4, t4, t2
	addi t4, t4, 24
	add t4, t4, t2
	add t4, t4, t2
	addi s4, zero, -1
	srli s4, s4, 7
	addi t2, zero, 0
2262:
	srli s0, t2, 6
	slli s0, s0, 3
	add s0, s0, t3
	ld s1, 0(s0)
	ld s2, 8(s0)
	srl s1, s1, t2
	xori s3, t2, -1
	slli s2, s2, 1
	sll s2, s2, s3
	add s1, s1, s2
	and s1, s1, s4
	sd s1, 0(t4)
	addi t4, t4, 8
	addi t2, t2, 57
	addi t5, t5, -1
	bnez t5, 2262b
	srli t2, s5, 3
	add t2, t2, s5
	addi t2, t2, -18
	add t3, a7, s5
	add t3, t3, s5
	add a7, t3, t2
	addi a7, a7, 24
	add s5, a7, t2
	addi s5, s5, 24
	sub t2, s5, a7
	addi t2, t2, -24
	slli t2, t2, 1
	add t4, s5, t2
	addi t3, s5, 0
	addi s0, zero, 0
2263:
	sd s0, 0(t3)
	sd s0, 8(t3)
	sd s0, 16(t3)
	addi t3, t3, 24
	bne t3, t4, 2263b
	addi a0, s5, 0
2264:
	sub t2, s5, a7
	addi t2, t2, -24
	slli t2, t2, 1
	add a2, a0, t2
	ld s2, 0(a2)
	ld s3, 8(a2)
	ld s4, 16(a2)
	slli t2, s2, 7
	slli t3, s3, 7
	slli t4, s4, 7
	addi t5, zero, 0
	addi t6, zero, 0
	addi s7, zero, 0
	addi a1, a7, 0
2265:
	mul s0, s4, t6
	mul s1, s3, t5
	mulhu a2, t3, t5
	ld a3, 0(a1)
	ld a4, 0(a0)
	mul a5, s2, a3
	mulhu a6, t4, t6
	add a2, a6, a2
	add s0, s0, s1
	mulhu s1, t2, a3
	add s1, a2, s1
	ld a2, 8(a0)
	mul a6, s4, t5
	slli t0, s1, 57
	add s0, s0, a5
	mul a5, s3, a3
	sub s0, s0, t0
	mulhu t0, t4, t5
	add a4, a4, s7
	add a5, a6, a5
	ld t6, 8(a1)
	add s0, a4, s0
	sd s0, 0(a0)
	mulhu s0, t3, a3
	mulhu a4, t2, t6
	mul a6, s2, t6
	add a5, a5, a6
	add s0, t0, s0
	mul a6, s4, a3
	add s0, s0, a4
	mulhu a3, t4, a3
	ld a4, 16(a0)
	slli t0, s0, 57
	sub a5, a5, t0
	mulhu t0, t3, t6
	add s1, a2, s1
	mul a2, s3, t6
	add s1, s1, a5
	sd s1, 8(a0)
	ld t5, 16(a1)
	mulhu s1, t2, t5
	add a2, a6, a2
	add a3, a3, t0
	mul a5, s2, t5
	add a2, a2, a5
	add s7, a3, s1
	add s0, a4, s0
	slli s1, s7, 57
	sub s1, a2, s1
	add s0, s0, s1
	sd s0, 16(a0)
	addi a0, a0, 24
	addi a1, a1, 24
	bne a1, s5, 2265b
	sub t2, s5, a7
	addi t2, t2, -24
	sub a0, a0, t2
	add t3, s5, t2
	bne a0, t3, 2264b
	sub t2, s5, a7
	addi t2, t2, -24
	addi a0, s5, 0
	addi a1, s5, 0
	slli t2, t2, 1
	add t3, a0, t2
	addi t6, zero, -1
	srli t6, t6, 7
	addi t5, zero, 0
2266:
	ld s0, 0(a0)
	add s0, s0, t5
	and s1, s0, t6
	srli t5, s0, 57
	sd s1, 0(a1)
	ld s0, 8(a0)
	add s0, s0, t5
	and s1, s0, t6
	srli t5, s0, 57
	sd s1, 8(a1)
	ld s0, 16(a0)
	add s0, s0, t5
	and s1, s0, t6
	srli t5, s0, 57
	sd s1, 16(a1)
	addi a0, a0, 24
	addi a1, a1, 24
	bne a0, t3, 2266b
	addi a0, s5, 0
2267:
	sub t2, s5, a7
	addi t2, t2, -24
	sub t2, a7, t2
	addi a1, t2, -24
	ld a4, 0(a1)
	ld a5, 8(a1)
	ld a6, 16(a1)
	addi t6, zero, -1
	srli t6, t6, 7
	ld s0, 0(a0)
	mul s2, s0, t1
	add s0, s0, t6
	slli t2, s2, 7
	and s2, s2, t6
	srli s0, s0, 57
	mulhu a3, t2, a4
	ld s1, 8(a0)
	add s0, s0, a3
	add s0, s0, s1
	mulhu a3, t2, a5
	mul a2, s2, a5
	slli t0, a3, 57
	sub a2, a2, t0
	add s0, s0, a2
	mul s3, s0, t1
	add s0, s0, t6
	slli t3, s3, 7
	and s3, s3, t6
	srli s0, s0, 57
	mulhu s1, t3, a4
	ld t5, 16(a0)
	add s0, s0, a3
	add s0, s0, t5
	add s0, s0, s1
	mulhu s7, t2, a6
	mul a2, s2, a6
	slli t0, s7, 57
	sub a2, a2, t0
	add s0, s0, a2
	mulhu a3, t3, a5
	mul a2, s3, a5
	slli t0, a3, 57
	sub a2, a2, t0
	add s0, s0, a2
	add s7, s7, a3
	mul s4, s0, t1
	add s0, s0, t6
	slli t4, s4, 7
	and s4, s4, t6
	srli s0, s0, 57
	mulhu a3, t4, a4
	add s7, s7, s0
	add s7, s7, a3
	addi t5, a6, 0
	addi t6, a5, 0
	addi a0, a0, 24
	addi a1, a1, 24
2268:
	mul s0, s4, t6
	mul s1, s3, t5
	mulhu a2, t3, t5
	ld a3, 0(a1)
	ld a4, 0(a0)
	mul a5, s2, a3
	mulhu a6, t4, t6
	add a2, a6, a2
	add s0, s0, s1
	mulhu s1, t2, a3
	add s1, a2, s1
	ld a2, 8(a0)
	mul a6, s4, t5
	slli t0, s1, 57
	add s0, s0, a5
	mul a5, s3, a3
	sub s0, s0, t0
	mulhu t0, t4, t5
	add a4, a4, s7
	add a5, a6, a5
	ld t6, 8(a1)
	add s0, a4, s0
	sd s0, 0(a0)
	mulhu s0, t3, a3
	mulhu a4, t2, t6
	mul a6, s2, t6
	add a5, a5, a6
	add s0, t0, s0
	mul a6, s4, a3
	add s0, s0, a4
	mulhu a3, t4, a3
	ld a4, 16(a0)
	slli t0, s0, 57
	sub a5, a5, t0
	mulhu t0, t3, t6
	add s1, a2, s1
	mul a2, s3, t6
	add s1, s1, a5
	sd s1, 8(a0)
	ld t5, 16(a1)
	mulhu s1, t2, t5
	add a2, a6, a2
	add a3, a3, t0
	mul a5, s2, t5
	add a2, a2, a5
	add s7, a3, s1
	add s0, a4, s0
	slli s1, s7, 57
	sub s1, a2, s1
	add s0, s0, s1
	sd s0, 16(a0)
	addi a0, a0, 24
	addi a1, a1, 24
	bne a1, a7, 2268b
	sub t2, s5, a7
	addi t2, t2, -24
	sub a0, a0, t2
	add t3, s5, t2
	bne a0, t3, 2267b
	sub t2, s5, a7
	addi t2, t2, -24
	add a0, s5, t2
	addi a1, a7, 0
	add t3, a0, t2
	addi t6, zero, -1
	srli t6, t6, 7
	addi t5, zero, 0
2269:
	ld s0, 0(a0)
	add s0, s0, t5
	and s1, s0, t6
	srli t5, s0, 57
	sd s1, 0(a1)
	ld s0, 8(a0)
	add s0, s0, t5
	and s1, s0, t6
	srli t5, s0, 57
	sd s1, 8(a1)
	ld s0, 16(a0)
	add s0, s0, t5
	and s1, s0, t6
	srli t5, s0, 57
	sd s1, 16(a1)
	addi a0, a0, 24
	addi a1, a1, 24
	bne a0, t3, 2269b
	sub t2, s5, a7
	addi t2, t2, -24
	sub t3, a7, t2
	addi t3, t3, -24
	addi t4, zero, 57
	mul t2, t2, t4
	srli t2, t2, 6
	addi s5, t2, 16
	sub a7, t3, s5
	sub a7, a7, s5
	srli t0, s5, 3
	addi t0, t0, -2
	bnez s10, 2252b
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
2270:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2270b
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
	addi s4, zero, -1
	addi a5, a7, 0
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
	addi a2, a7, 0
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	add a2, a2, s5
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2271:
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
	bnez t5, 2271b
	slli t3, s5, 2
	add t3, t3, s5
	add t3, t3, a7
	add t5, t3, s5
	addi t5, t5, -16
	addi s0, zero, 0
	sd s0, 0(t5)
	srli t2, s5, 3
	add t2, t2, s5
	addi t2, t2, -18
	srli t5, t2, 3
	add t4, a7, s5
	add t4, t4, s5
	add t4, t4, t2
	addi t4, t4, 24
	add t4, t4, t2
	addi t4, t4, 24
	add t4, t4, t2
	add t4, t4, t2
	addi s4, zero, -1
	srli s4, s4, 7
	addi t2, zero, 0
2272:
	srli s0, t2, 6
	slli s0, s0, 3
	add s0, s0, t3
	ld s1, 0(s0)
	ld s2, 8(s0)
	srl s1, s1, t2
	xori s3, t2, -1
	slli s2, s2, 1
	sll s2, s2, s3
	add s1, s1, s2
	and s1, s1, s4
	sd s1, 0(t4)
	addi t4, t4, 8
	addi t2, t2, 57
	addi t5, t5, -1
	bnez t5, 2272b
	srli t2, s5, 3
	add t2, t2, s5
	addi t2, t2, -18
	add t3, a7, s5
	add t3, t3, s5
	add a7, t3, t2
	addi a7, a7, 24
	add s5, a7, t2
	addi s5, s5, 24
	sub t2, s5, a7
	addi t2, t2, -24
	slli t2, t2, 1
	add t4, s5, t2
	addi t3, s5, 0
	addi s0, zero, 0
2273:
	sd s0, 0(t3)
	sd s0, 8(t3)
	sd s0, 16(t3)
	addi t3, t3, 24
	bne t3, t4, 2273b
	addi a0, s5, 0
2274:
	sub t2, s5, a7
	addi t2, t2, -24
	slli t2, t2, 1
	add a2, a0, t2
	ld s2, 0(a2)
	ld s3, 8(a2)
	ld s4, 16(a2)
	slli t2, s2, 7
	slli t3, s3, 7
	slli t4, s4, 7
	addi t5, zero, 0
	addi t6, zero, 0
	addi s7, zero, 0
	addi a1, a7, 0
2275:
	mul s0, s4, t6
	mul s1, s3, t5
	mulhu a2, t3, t5
	ld a3, 0(a1)
	ld a4, 0(a0)
	mul a5, s2, a3
	mulhu a6, t4, t6
	add a2, a6, a2
	add s0, s0, s1
	mulhu s1, t2, a3
	add s1, a2, s1
	ld a2, 8(a0)
	mul a6, s4, t5
	slli t0, s1, 57
	add s0, s0, a5
	mul a5, s3, a3
	sub s0, s0, t0
	mulhu t0, t4, t5
	add a4, a4, s7
	add a5, a6, a5
	ld t6, 8(a1)
	add s0, a4, s0
	sd s0, 0(a0)
	mulhu s0, t3, a3
	mulhu a4, t2, t6
	mul a6, s2, t6
	add a5, a5, a6
	add s0, t0, s0
	mul a6, s4, a3
	add s0, s0, a4
	mulhu a3, t4, a3
	ld a4, 16(a0)
	slli t0, s0, 57
	sub a5, a5, t0
	mulhu t0, t3, t6
	add s1, a2, s1
	mul a2, s3, t6
	add s1, s1, a5
	sd s1, 8(a0)
	ld t5, 16(a1)
	mulhu s1, t2, t5
	add a2, a6, a2
	add a3, a3, t0
	mul a5, s2, t5
	add a2, a2, a5
	add s7, a3, s1
	add s0, a4, s0
	slli s1, s7, 57
	sub s1, a2, s1
	add s0, s0, s1
	sd s0, 16(a0)
	addi a0, a0, 24
	addi a1, a1, 24
	bne a1, s5, 2275b
	sub t2, s5, a7
	addi t2, t2, -24
	sub a0, a0, t2
	add t3, s5, t2
	bne a0, t3, 2274b
	sub t2, s5, a7
	addi t2, t2, -24
	addi a0, s5, 0
	addi a1, s5, 0
	slli t2, t2, 1
	add t3, a0, t2
	addi t6, zero, -1
	srli t6, t6, 7
	addi t5, zero, 0
2276:
	ld s0, 0(a0)
	add s0, s0, t5
	and s1, s0, t6
	srli t5, s0, 57
	sd s1, 0(a1)
	ld s0, 8(a0)
	add s0, s0, t5
	and s1, s0, t6
	srli t5, s0, 57
	sd s1, 8(a1)
	ld s0, 16(a0)
	add s0, s0, t5
	and s1, s0, t6
	srli t5, s0, 57
	sd s1, 16(a1)
	addi a0, a0, 24
	addi a1, a1, 24
	bne a0, t3, 2276b
	addi a0, s5, 0
2277:
	sub t2, s5, a7
	addi t2, t2, -24
	sub t2, a7, t2
	addi a1, t2, -24
	ld a4, 0(a1)
	ld a5, 8(a1)
	ld a6, 16(a1)
	addi t6, zero, -1
	srli t6, t6, 7
	ld s0, 0(a0)
	mul s2, s0, t1
	add s0, s0, t6
	slli t2, s2, 7
	and s2, s2, t6
	srli s0, s0, 57
	mulhu a3, t2, a4
	ld s1, 8(a0)
	add s0, s0, a3
	add s0, s0, s1
	mulhu a3, t2, a5
	mul a2, s2, a5
	slli t0, a3, 57
	sub a2, a2, t0
	add s0, s0, a2
	mul s3, s0, t1
	add s0, s0, t6
	slli t3, s3, 7
	and s3, s3, t6
	srli s0, s0, 57
	mulhu s1, t3, a4
	ld t5, 16(a0)
	add s0, s0, a3
	add s0, s0, t5
	add s0, s0, s1
	mulhu s7, t2, a6
	mul a2, s2, a6
	slli t0, s7, 57
	sub a2, a2, t0
	add s0, s0, a2
	mulhu a3, t3, a5
	mul a2, s3, a5
	slli t0, a3, 57
	sub a2, a2, t0
	add s0, s0, a2
	add s7, s7, a3
	mul s4, s0, t1
	add s0, s0, t6
	slli t4, s4, 7
	and s4, s4, t6
	srli s0, s0, 57
	mulhu a3, t4, a4
	add s7, s7, s0
	add s7, s7, a3
	addi t5, a6, 0
	addi t6, a5, 0
	addi a0, a0, 24
	addi a1, a1, 24
2278:
	mul s0, s4, t6
	mul s1, s3, t5
	mulhu a2, t3, t5
	ld a3, 0(a1)
	ld a4, 0(a0)
	mul a5, s2, a3
	mulhu a6, t4, t6
	add a2, a6, a2
	add s0, s0, s1
	mulhu s1, t2, a3
	add s1, a2, s1
	ld a2, 8(a0)
	mul a6, s4, t5
	slli t0, s1, 57
	add s0, s0, a5
	mul a5, s3, a3
	sub s0, s0, t0
	mulhu t0, t4, t5
	add a4, a4, s7
	add a5, a6, a5
	ld t6, 8(a1)
	add s0, a4, s0
	sd s0, 0(a0)
	mulhu s0, t3, a3
	mulhu a4, t2, t6
	mul a6, s2, t6
	add a5, a5, a6
	add s0, t0, s0
	mul a6, s4, a3
	add s0, s0, a4
	mulhu a3, t4, a3
	ld a4, 16(a0)
	slli t0, s0, 57
	sub a5, a5, t0
	mulhu t0, t3, t6
	add s1, a2, s1
	mul a2, s3, t6
	add s1, s1, a5
	sd s1, 8(a0)
	ld t5, 16(a1)
	mulhu s1, t2, t5
	add a2, a6, a2
	add a3, a3, t0
	mul a5, s2, t5
	add a2, a2, a5
	add s7, a3, s1
	add s0, a4, s0
	slli s1, s7, 57
	sub s1, a2, s1
	add s0, s0, s1
	sd s0, 16(a0)
	addi a0, a0, 24
	addi a1, a1, 24
	bne a1, a7, 2278b
	sub t2, s5, a7
	addi t2, t2, -24
	sub a0, a0, t2
	add t3, s5, t2
	bne a0, t3, 2277b
	sub t2, s5, a7
	addi t2, t2, -24
	add a0, s5, t2
	addi a1, a7, 0
	add t3, a0, t2
	addi t6, zero, -1
	srli t6, t6, 7
	addi t5, zero, 0
2279:
	ld s0, 0(a0)
	add s0, s0, t5
	and s1, s0, t6
	srli t5, s0, 57
	sd s1, 0(a1)
	ld s0, 8(a0)
	add s0, s0, t5
	and s1, s0, t6
	srli t5, s0, 57
	sd s1, 8(a1)
	ld s0, 16(a0)
	add s0, s0, t5
	and s1, s0, t6
	srli t5, s0, 57
	sd s1, 16(a1)
	addi a0, a0, 24
	addi a1, a1, 24
	bne a0, t3, 2279b
	sub t2, s5, a7
	addi t2, t2, -24
	sub t3, a7, t2
	addi t3, t3, -24
	addi t4, zero, 57
	mul t2, t2, t4
	srli t2, t2, 6
	addi s5, t2, 16
	sub a7, t3, s5
	sub a7, a7, s5
	srli t0, s5, 3
	addi t0, t0, -2
	srli t2, s5, 3
	add t2, t2, s5
	addi t2, t2, -18
	add t4, a7, s5
	add t4, t4, s5
	add t4, t4, t2
	addi t4, t4, 24
	slli t3, s5, 2
	add t3, t3, s5
	add t3, t3, s5
	add t3, t3, a7
	addi t6, zero, 0
	addi s4, zero, 57
	addi a2, zero, 1150
	addi t5, t0, 0
2280:
	mul a3, t6, a2
	srli a3, a3, 16
	mul a4, a3, s4
	sub a4, t6, a4
	sub a5, s4, a4
	slli a3, a3, 3
	add a3, a3, t4
	ld s1, 0(a3)
	ld s2, 8(a3)
	ld s3, 16(a3)
	srl s1, s1, a4
	sll s2, s2, a5
	slli s3, s3, 57
	sll s3, s3, a5
	add s1, s1, s2
	add s1, s1, s3
	sd s1, 0(t3)
	addi t3, t3, 8
	addi t6, t6, 64
	addi t5, t5, -1
	bnez t5, 2280b
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
2281:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2281b
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
	addi a3, a7, 0
	add a3, a3, s5
	add a3, a3, s5
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
2282:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2282b
2283:
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
	beqz t5, 2284f
2286:
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
	bnez t5, 2286b
	j 2285f
2284:
2285:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2287f
2289:
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
	bnez t5, 2289b
	j 2288f
2287:
2288:
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
	bnez a1, 2283b
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
2290:
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
	bnez t5, 2290b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2291:
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
	bnez t5, 2291b
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
	add a3, a3, s5
	addi a4, a7, 0
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
2292:
	sd s0, 0(t3)
	addi t3, t3, 8
	addi t5, t5, -1
	bnez t5, 2292b
2293:
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
	beqz t5, 2294f
2296:
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
	bnez t5, 2296b
	j 2295f
2294:
2295:
	addi t5, t0, -1
	srli t5, t5, 2
	beqz t5, 2297f
2299:
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
	bnez t5, 2299b
	j 2298f
2297:
2298:
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
	bnez a1, 2293b
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
2300:
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
	bnez t5, 2300b
	ld s2, 0(t3)
	sltu s0, s2, s4
	addi s1, zero, 0
	sub s4, s1, s0
	addi t3, a5, 0
	addi t4, a6, 0
	addi a0, a2, 0
	addi t5, t0, 0
2301:
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
	bnez t5, 2301b
21:
	ret
	.option pop
