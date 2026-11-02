// The functions of `src/poly1305.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_poly1305_init:
	.option push
	.option arch, +m, +c
	lbu t0, 0(a1)
	sb t0, 24(a0)
	lbu t0, 1(a1)
	sb t0, 25(a0)
	lbu t0, 2(a1)
	sb t0, 26(a0)
	lbu t0, 3(a1)
	sb t0, 27(a0)
	lbu t0, 4(a1)
	sb t0, 28(a0)
	lbu t0, 5(a1)
	sb t0, 29(a0)
	lbu t0, 6(a1)
	sb t0, 30(a0)
	lbu t0, 7(a1)
	sb t0, 31(a0)
	lbu t0, 8(a1)
	sb t0, 32(a0)
	lbu t0, 9(a1)
	sb t0, 33(a0)
	lbu t0, 10(a1)
	sb t0, 34(a0)
	lbu t0, 11(a1)
	sb t0, 35(a0)
	lbu t0, 12(a1)
	sb t0, 36(a0)
	lbu t0, 13(a1)
	sb t0, 37(a0)
	lbu t0, 14(a1)
	sb t0, 38(a0)
	lbu t0, 15(a1)
	sb t0, 39(a0)
	lbu t0, 16(a1)
	sb t0, 40(a0)
	lbu t0, 17(a1)
	sb t0, 41(a0)
	lbu t0, 18(a1)
	sb t0, 42(a0)
	lbu t0, 19(a1)
	sb t0, 43(a0)
	lbu t0, 20(a1)
	sb t0, 44(a0)
	lbu t0, 21(a1)
	sb t0, 45(a0)
	lbu t0, 22(a1)
	sb t0, 46(a0)
	lbu t0, 23(a1)
	sb t0, 47(a0)
	lbu t0, 24(a1)
	sb t0, 48(a0)
	lbu t0, 25(a1)
	sb t0, 49(a0)
	lbu t0, 26(a1)
	sb t0, 50(a0)
	lbu t0, 27(a1)
	sb t0, 51(a0)
	lbu t0, 28(a1)
	sb t0, 52(a0)
	lbu t0, 29(a1)
	sb t0, 53(a0)
	lbu t0, 30(a1)
	sb t0, 54(a0)
	lbu t0, 31(a1)
	sb t0, 55(a0)
	addi t0, zero, 0
	sb t0, 0(a0)
	addi t0, zero, 0
	sb t0, 1(a0)
	addi t0, zero, 0
	sb t0, 2(a0)
	addi t0, zero, 0
	sb t0, 3(a0)
	addi t0, zero, 0
	sb t0, 4(a0)
	addi t0, zero, 0
	sb t0, 5(a0)
	addi t0, zero, 0
	sb t0, 6(a0)
	addi t0, zero, 0
	sb t0, 7(a0)
	addi t0, zero, 0
	sb t0, 8(a0)
	addi t0, zero, 0
	sb t0, 9(a0)
	addi t0, zero, 0
	sb t0, 10(a0)
	addi t0, zero, 0
	sb t0, 11(a0)
	addi t0, zero, 0
	sb t0, 12(a0)
	addi t0, zero, 0
	sb t0, 13(a0)
	addi t0, zero, 0
	sb t0, 14(a0)
	addi t0, zero, 0
	sb t0, 15(a0)
	addi t0, zero, 0
	sb t0, 16(a0)
	addi t0, zero, 0
	sb t0, 17(a0)
	addi t0, zero, 0
	sb t0, 18(a0)
	addi t0, zero, 0
	sb t0, 19(a0)
	addi t0, zero, 0
	sb t0, 20(a0)
	addi t0, zero, 0
	sb t0, 21(a0)
	addi t0, zero, 0
	sb t0, 22(a0)
	addi t0, zero, 0
	sb t0, 23(a0)
	ret
	.option pop

vg_poly1305_update:
	.option push
	.option arch, +m, +c
	andi t6, a1, 15
	ld a5, 24(a0)
	ld a6, 32(a0)
	lui a4, 65536
	addiw a4, a4, -4
	slli a4, a4, 32
	lui a1, 65536
	addiw a1, a1, -1
	slli a1, a1, 32
	srli a1, a1, 32
	or a4, a4, a1
	and a5, a5, a4
	andi a4, a4, -4
	and a6, a6, a4
	srli a7, a6, 2
	add a7, a7, a6
	ld t0, 0(a0)
	ld t1, 8(a0)
	ld t2, 16(a0)
	beqz t6, 20f
	addi t3, zero, 16
	sub t3, t3, t6
	bltu a3, t3, 22f
	j 23f
22:
	addi t3, a3, 0
23:
	sub a3, a3, t3
	addi t4, a0, 56
	add t4, t4, t6
	add t6, t6, t3
	addi a4, a2, 0
	add a2, a2, t3
	beqz t3, 24f
26:
	lbu t5, 0(a4)
	sb t5, 0(t4)
	addi a4, a4, 1
	addi t4, t4, 1
	addi t3, t3, -1
	bnez t3, 26b
	j 25f
24:
25:
	addi t3, t6, -16
	beqz t3, 27f
	j 28f
27:
	lbu t3, 56(a0)
	lbu a4, 57(a0)
	slli a4, a4, 8
	or t3, t3, a4
	lbu a4, 58(a0)
	slli a4, a4, 16
	or t3, t3, a4
	lbu a4, 59(a0)
	slli a4, a4, 24
	or t3, t3, a4
	lbu a1, 60(a0)
	lbu a4, 61(a0)
	slli a4, a4, 8
	or a1, a1, a4
	lbu a4, 62(a0)
	slli a4, a4, 16
	or a1, a1, a4
	lbu a4, 63(a0)
	slli a4, a4, 24
	or a1, a1, a4
	slli a1, a1, 32
	or t3, t3, a1
	lbu t4, 64(a0)
	lbu a4, 65(a0)
	slli a4, a4, 8
	or t4, t4, a4
	lbu a4, 66(a0)
	slli a4, a4, 16
	or t4, t4, a4
	lbu a4, 67(a0)
	slli a4, a4, 24
	or t4, t4, a4
	lbu a1, 68(a0)
	lbu a4, 69(a0)
	slli a4, a4, 8
	or a1, a1, a4
	lbu a4, 70(a0)
	slli a4, a4, 16
	or a1, a1, a4
	lbu a4, 71(a0)
	slli a4, a4, 24
	or a1, a1, a4
	slli a1, a1, 32
	or t4, t4, a1
	add t0, t0, t3
	sltu t3, t0, t3
	add t1, t1, t4
	sltu t4, t1, t4
	add t1, t1, t3
	sltu t3, t1, t3
	add t2, t2, t4
	add t2, t2, t3
	addi t2, t2, 1
	mul t3, t0, a5
	mulhu t4, t0, a5
	mul t5, t0, a6
	mulhu t6, t0, a6
	mul a4, t1, a7
	mulhu a1, t1, a7
	add t3, t3, a4
	sltu a4, t3, a4
	add t4, t4, a1
	add t4, t4, a4
	mul a4, t1, a5
	mulhu a1, t1, a5
	add t5, t5, a4
	sltu a4, t5, a4
	add t6, t6, a1
	add t6, t6, a4
	mul a4, t2, a7
	add t5, t5, a4
	sltu a4, t5, a4
	add t6, t6, a4
	mul a1, t2, a5
	add t5, t5, t4
	sltu t4, t5, t4
	add t6, t6, a1
	add t6, t6, t4
	andi t2, t6, 3
	andi a4, t6, -4
	srli a1, t6, 2
	add a4, a4, a1
	add t0, t3, a4
	sltu a4, t0, a4
	add t1, t5, a4
	sltu a4, t1, a4
	add t2, t2, a4
28:
	j 21f
20:
21:
	srli t3, a3, 4
	beqz t3, 29f
	andi a4, a2, 7
	beqz a4, 211f
213:
	lbu t3, 0(a2)
	lbu a4, 1(a2)
	slli a4, a4, 8
	or t3, t3, a4
	lbu a4, 2(a2)
	slli a4, a4, 16
	or t3, t3, a4
	lbu a4, 3(a2)
	slli a4, a4, 24
	or t3, t3, a4
	lbu a1, 4(a2)
	lbu a4, 5(a2)
	slli a4, a4, 8
	or a1, a1, a4
	lbu a4, 6(a2)
	slli a4, a4, 16
	or a1, a1, a4
	lbu a4, 7(a2)
	slli a4, a4, 24
	or a1, a1, a4
	slli a1, a1, 32
	or t3, t3, a1
	lbu t4, 8(a2)
	lbu a4, 9(a2)
	slli a4, a4, 8
	or t4, t4, a4
	lbu a4, 10(a2)
	slli a4, a4, 16
	or t4, t4, a4
	lbu a4, 11(a2)
	slli a4, a4, 24
	or t4, t4, a4
	lbu a1, 12(a2)
	lbu a4, 13(a2)
	slli a4, a4, 8
	or a1, a1, a4
	lbu a4, 14(a2)
	slli a4, a4, 16
	or a1, a1, a4
	lbu a4, 15(a2)
	slli a4, a4, 24
	or a1, a1, a4
	slli a1, a1, 32
	or t4, t4, a1
	add t0, t0, t3
	sltu t3, t0, t3
	add t1, t1, t4
	sltu t4, t1, t4
	add t1, t1, t3
	sltu t3, t1, t3
	add t2, t2, t4
	add t2, t2, t3
	addi t2, t2, 1
	mul t3, t0, a5
	mulhu t4, t0, a5
	mul t5, t0, a6
	mulhu t6, t0, a6
	mul a4, t1, a7
	mulhu a1, t1, a7
	add t3, t3, a4
	sltu a4, t3, a4
	add t4, t4, a1
	add t4, t4, a4
	mul a4, t1, a5
	mulhu a1, t1, a5
	add t5, t5, a4
	sltu a4, t5, a4
	add t6, t6, a1
	add t6, t6, a4
	mul a4, t2, a7
	add t5, t5, a4
	sltu a4, t5, a4
	add t6, t6, a4
	mul a1, t2, a5
	add t5, t5, t4
	sltu t4, t5, t4
	add t6, t6, a1
	add t6, t6, t4
	andi t2, t6, 3
	andi a4, t6, -4
	srli a1, t6, 2
	add a4, a4, a1
	add t0, t3, a4
	sltu a4, t0, a4
	add t1, t5, a4
	sltu a4, t1, a4
	add t2, t2, a4
	addi a2, a2, 16
	addi a3, a3, -16
	srli t3, a3, 4
	bnez t3, 213b
	j 212f
211:
214:
	ld t3, 0(a2)
	ld t4, 8(a2)
	add t0, t0, t3
	sltu t3, t0, t3
	add t1, t1, t4
	sltu t4, t1, t4
	add t1, t1, t3
	sltu t3, t1, t3
	add t2, t2, t4
	add t2, t2, t3
	addi t2, t2, 1
	mul t3, t0, a5
	mulhu t4, t0, a5
	mul t5, t0, a6
	mulhu t6, t0, a6
	mul a4, t1, a7
	mulhu a1, t1, a7
	add t3, t3, a4
	sltu a4, t3, a4
	add t4, t4, a1
	add t4, t4, a4
	mul a4, t1, a5
	mulhu a1, t1, a5
	add t5, t5, a4
	sltu a4, t5, a4
	add t6, t6, a1
	add t6, t6, a4
	mul a4, t2, a7
	add t5, t5, a4
	sltu a4, t5, a4
	add t6, t6, a4
	mul a1, t2, a5
	add t5, t5, t4
	sltu t4, t5, t4
	add t6, t6, a1
	add t6, t6, t4
	andi t2, t6, 3
	andi a4, t6, -4
	srli a1, t6, 2
	add a4, a4, a1
	add t0, t3, a4
	sltu a4, t0, a4
	add t1, t5, a4
	sltu a4, t1, a4
	add t2, t2, a4
	addi a2, a2, 16
	addi a3, a3, -16
	srli t3, a3, 4
	bnez t3, 214b
212:
	j 210f
29:
210:
	beqz a3, 215f
	addi t4, a0, 56
217:
	lbu t5, 0(a2)
	sb t5, 0(t4)
	addi a2, a2, 1
	addi t4, t4, 1
	addi a3, a3, -1
	bnez a3, 217b
	j 216f
215:
216:
	addi a4, zero, 5
	add t3, t0, a4
	sltu a4, t3, a4
	add t4, t1, a4
	sltu a4, t4, a4
	add t5, t2, a4
	srli a4, t5, 2
	addi a4, a4, -1
	andi t5, t5, 3
	xor a1, t0, t3
	and a1, a1, a4
	xor t0, t3, a1
	xor a1, t1, t4
	and a1, a1, a4
	xor t1, t4, a1
	xor a1, t2, t5
	and a1, a1, a4
	xor t2, t5, a1
	sd t0, 0(a0)
	sd t1, 8(a0)
	sd t2, 16(a0)
	ret
	.option pop

vg_poly1305_finalize:
	.option push
	.option arch, +m, +c
	andi t6, a1, 15
	ld a5, 24(a0)
	ld a6, 32(a0)
	lui a4, 65536
	addiw a4, a4, -4
	slli a4, a4, 32
	lui a1, 65536
	addiw a1, a1, -1
	slli a1, a1, 32
	srli a1, a1, 32
	or a4, a4, a1
	and a5, a5, a4
	andi a4, a4, -4
	and a6, a6, a4
	srli a7, a6, 2
	add a7, a7, a6
	ld t0, 0(a0)
	ld t1, 8(a0)
	ld t2, 16(a0)
	beqz t6, 20f
	addi t5, zero, 0
	addi t4, a0, 56
	add t4, t4, t6
	addi t3, zero, 16
	sub t3, t3, t6
22:
	sb t5, 0(t4)
	addi t4, t4, 1
	addi t3, t3, -1
	bnez t3, 22b
	addi t5, zero, 1
	addi t4, a0, 56
	add t4, t4, t6
	sb t5, 0(t4)
	lbu t3, 56(a0)
	lbu a4, 57(a0)
	slli a4, a4, 8
	or t3, t3, a4
	lbu a4, 58(a0)
	slli a4, a4, 16
	or t3, t3, a4
	lbu a4, 59(a0)
	slli a4, a4, 24
	or t3, t3, a4
	lbu a1, 60(a0)
	lbu a4, 61(a0)
	slli a4, a4, 8
	or a1, a1, a4
	lbu a4, 62(a0)
	slli a4, a4, 16
	or a1, a1, a4
	lbu a4, 63(a0)
	slli a4, a4, 24
	or a1, a1, a4
	slli a1, a1, 32
	or t3, t3, a1
	lbu t4, 64(a0)
	lbu a4, 65(a0)
	slli a4, a4, 8
	or t4, t4, a4
	lbu a4, 66(a0)
	slli a4, a4, 16
	or t4, t4, a4
	lbu a4, 67(a0)
	slli a4, a4, 24
	or t4, t4, a4
	lbu a1, 68(a0)
	lbu a4, 69(a0)
	slli a4, a4, 8
	or a1, a1, a4
	lbu a4, 70(a0)
	slli a4, a4, 16
	or a1, a1, a4
	lbu a4, 71(a0)
	slli a4, a4, 24
	or a1, a1, a4
	slli a1, a1, 32
	or t4, t4, a1
	add t0, t0, t3
	sltu t3, t0, t3
	add t1, t1, t4
	sltu t4, t1, t4
	add t1, t1, t3
	sltu t3, t1, t3
	add t2, t2, t4
	add t2, t2, t3
	mul t3, t0, a5
	mulhu t4, t0, a5
	mul t5, t0, a6
	mulhu t6, t0, a6
	mul a4, t1, a7
	mulhu a1, t1, a7
	add t3, t3, a4
	sltu a4, t3, a4
	add t4, t4, a1
	add t4, t4, a4
	mul a4, t1, a5
	mulhu a1, t1, a5
	add t5, t5, a4
	sltu a4, t5, a4
	add t6, t6, a1
	add t6, t6, a4
	mul a4, t2, a7
	add t5, t5, a4
	sltu a4, t5, a4
	add t6, t6, a4
	mul a1, t2, a5
	add t5, t5, t4
	sltu t4, t5, t4
	add t6, t6, a1
	add t6, t6, t4
	andi t2, t6, 3
	andi a4, t6, -4
	srli a1, t6, 2
	add a4, a4, a1
	add t0, t3, a4
	sltu a4, t0, a4
	add t1, t5, a4
	sltu a4, t1, a4
	add t2, t2, a4
	j 21f
20:
21:
	addi a4, zero, 5
	add t3, t0, a4
	sltu a4, t3, a4
	add t4, t1, a4
	sltu a4, t4, a4
	add t5, t2, a4
	srli a4, t5, 2
	addi a4, a4, -1
	andi t5, t5, 3
	xor a1, t0, t3
	and a1, a1, a4
	xor t0, t3, a1
	xor a1, t1, t4
	and a1, a1, a4
	xor t1, t4, a1
	xor a1, t2, t5
	and a1, a1, a4
	xor t2, t5, a1
	ld t3, 40(a0)
	ld t4, 48(a0)
	add t0, t0, t3
	sltu t3, t0, t3
	add t1, t1, t4
	add t1, t1, t3
	sb t0, 0(a2)
	srli a4, t0, 8
	sb a4, 1(a2)
	srli a4, t0, 16
	sb a4, 2(a2)
	srli a4, t0, 24
	sb a4, 3(a2)
	srli a4, t0, 32
	sb a4, 4(a2)
	srli a1, a4, 8
	sb a1, 5(a2)
	srli a1, a4, 16
	sb a1, 6(a2)
	srli a1, a4, 24
	sb a1, 7(a2)
	sb t1, 8(a2)
	srli a4, t1, 8
	sb a4, 9(a2)
	srli a4, t1, 16
	sb a4, 10(a2)
	srli a4, t1, 24
	sb a4, 11(a2)
	srli a4, t1, 32
	sb a4, 12(a2)
	srli a1, a4, 8
	sb a1, 13(a2)
	srli a1, a4, 16
	sb a1, 14(a2)
	srli a1, a4, 24
	sb a1, 15(a2)
	ret
	.option pop
