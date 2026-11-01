// The functions of `src/cmac_triple_des.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cmac_triple_des_stream_init:
	.option push
	.option arch, +m, +c
	addi sp, sp, -640
	addi a3, sp, 0
	addi t0, a3, 7
	andi t0, t0, -8
	sd ra, 0(t0)
	sd s1, 8(t0)
	sd s2, 16(t0)
	addi s1, a0, 0
	addi s2, a3, 0
	addi a0, a1, 0
	addi a1, a2, 0
	addi a2, s1, 0
	call {vg_triple_des_expand_key}
	addi t0, zero, 0
	sb t0, 384(s1)
	addi t0, zero, 0
	sb t0, 385(s1)
	addi t0, zero, 0
	sb t0, 386(s1)
	addi t0, zero, 0
	sb t0, 387(s1)
	addi t0, zero, 0
	sb t0, 388(s1)
	addi t0, zero, 0
	sb t0, 389(s1)
	addi t0, zero, 0
	sb t0, 390(s1)
	addi t0, zero, 0
	sb t0, 391(s1)
	addi a0, s1, 0
	addi a1, s1, 384
	addi a2, zero, 1
	call {vg_triple_des_ecb_encrypt}
	lbu t1, 384(s1)
	srli t2, t1, 7
	addi t2, t2, -1
	andi t2, t2, 27
	xori t2, t2, 27
	lbu t3, 385(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 384(s1)
	addi t1, t3, 0
	lbu t3, 386(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 385(s1)
	addi t1, t3, 0
	lbu t3, 387(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 386(s1)
	addi t1, t3, 0
	lbu t3, 388(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 387(s1)
	addi t1, t3, 0
	lbu t3, 389(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 388(s1)
	addi t1, t3, 0
	lbu t3, 390(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 389(s1)
	addi t1, t3, 0
	lbu t3, 391(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 390(s1)
	addi t1, t3, 0
	slli t1, t1, 1
	xor t1, t1, t2
	sb t1, 391(s1)
	lbu t1, 384(s1)
	srli t2, t1, 7
	addi t2, t2, -1
	andi t2, t2, 27
	xori t2, t2, 27
	lbu t3, 385(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 392(s1)
	addi t1, t3, 0
	lbu t3, 386(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 393(s1)
	addi t1, t3, 0
	lbu t3, 387(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 394(s1)
	addi t1, t3, 0
	lbu t3, 388(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 395(s1)
	addi t1, t3, 0
	lbu t3, 389(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 396(s1)
	addi t1, t3, 0
	lbu t3, 390(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 397(s1)
	addi t1, t3, 0
	lbu t3, 391(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 398(s1)
	addi t1, t3, 0
	slli t1, t1, 1
	xor t1, t1, t2
	sb t1, 399(s1)
	addi t0, zero, 0
	sb t0, 400(s1)
	addi t0, zero, 0
	sb t0, 401(s1)
	addi t0, zero, 0
	sb t0, 402(s1)
	addi t0, zero, 0
	sb t0, 403(s1)
	addi t0, zero, 0
	sb t0, 404(s1)
	addi t0, zero, 0
	sb t0, 405(s1)
	addi t0, zero, 0
	sb t0, 406(s1)
	addi t0, zero, 0
	sb t0, 407(s1)
	addi t0, s2, 7
	andi t0, t0, -8
	ld ra, 0(t0)
	ld s1, 8(t0)
	ld s2, 16(t0)
	addi sp, sp, 640
	ret
	.option pop

vg_cmac_triple_des_absorb:
	.option push
	.option arch, +m, +c
	addi sp, sp, -688
	addi a4, sp, 0
	addi t0, a4, 7
	andi t0, t0, -8
	sd ra, 0(t0)
	sd s1, 8(t0)
	sd s2, 16(t0)
	sd s3, 24(t0)
	sd s4, 32(t0)
	sd s5, 40(t0)
	addi s1, a0, 0
	addi s2, a4, 0
	addi s3, a2, 0
	beqz a1, 20f
	addi t0, a1, -1
	andi t0, t0, 7
	addi t0, t0, 1
	j 21f
20:
	addi t0, zero, 0
21:
	addi t1, zero, 8
	sub t1, t1, t0
	sltu t2, t1, a3
	bnez t2, 22f
	addi t3, s1, 408
	add t3, t3, t0
	addi t4, s3, 0
	addi t5, a3, 0
	beqz t5, 24f
26:
	lbu t6, 0(t4)
	sb t6, 0(t3)
	addi t4, t4, 1
	addi t3, t3, 1
	addi t5, t5, -1
	bnez t5, 26b
	j 25f
24:
25:
	j 23f
22:
	sub s4, a3, t1
	addi t3, s1, 408
	add t3, t3, t0
	addi t4, s3, 0
	addi t5, t1, 0
	beqz t5, 27f
29:
	lbu t6, 0(t4)
	sb t6, 0(t3)
	addi t4, t4, 1
	addi t3, t3, 1
	addi t5, t5, -1
	bnez t5, 29b
	j 28f
27:
28:
	add s3, s3, t1
	addi t2, s4, -1
	srli s5, t2, 3
	slli t2, s5, 3
	sub s4, s4, t2
	addi a0, s1, 400
	addi a1, s1, 408
	lbu t0, 0(a0)
	lbu t1, 0(a1)
	xor t0, t0, t1
	sb t0, 0(a0)
	lbu t0, 1(a0)
	lbu t1, 1(a1)
	xor t0, t0, t1
	sb t0, 1(a0)
	lbu t0, 2(a0)
	lbu t1, 2(a1)
	xor t0, t0, t1
	sb t0, 2(a0)
	lbu t0, 3(a0)
	lbu t1, 3(a1)
	xor t0, t0, t1
	sb t0, 3(a0)
	lbu t0, 4(a0)
	lbu t1, 4(a1)
	xor t0, t0, t1
	sb t0, 4(a0)
	lbu t0, 5(a0)
	lbu t1, 5(a1)
	xor t0, t0, t1
	sb t0, 5(a0)
	lbu t0, 6(a0)
	lbu t1, 6(a1)
	xor t0, t0, t1
	sb t0, 6(a0)
	lbu t0, 7(a0)
	lbu t1, 7(a1)
	xor t0, t0, t1
	sb t0, 7(a0)
	addi a0, s1, 0
	addi a1, s1, 400
	addi a2, zero, 1
	call {vg_triple_des_ecb_encrypt}
	beqz s5, 210f
212:
	addi t3, s1, 400
	lbu t0, 0(t3)
	lbu t1, 0(s3)
	xor t0, t0, t1
	sb t0, 0(t3)
	lbu t0, 1(t3)
	lbu t1, 1(s3)
	xor t0, t0, t1
	sb t0, 1(t3)
	lbu t0, 2(t3)
	lbu t1, 2(s3)
	xor t0, t0, t1
	sb t0, 2(t3)
	lbu t0, 3(t3)
	lbu t1, 3(s3)
	xor t0, t0, t1
	sb t0, 3(t3)
	lbu t0, 4(t3)
	lbu t1, 4(s3)
	xor t0, t0, t1
	sb t0, 4(t3)
	lbu t0, 5(t3)
	lbu t1, 5(s3)
	xor t0, t0, t1
	sb t0, 5(t3)
	lbu t0, 6(t3)
	lbu t1, 6(s3)
	xor t0, t0, t1
	sb t0, 6(t3)
	lbu t0, 7(t3)
	lbu t1, 7(s3)
	xor t0, t0, t1
	sb t0, 7(t3)
	addi s3, s3, 8
	addi s5, s5, -1
	addi a0, s1, 0
	addi a1, s1, 400
	addi a2, zero, 1
	call {vg_triple_des_ecb_encrypt}
	bnez s5, 212b
	j 211f
210:
211:
	addi t3, s1, 408
	addi t4, s3, 0
	addi t5, s4, 0
	beqz t5, 213f
215:
	lbu t6, 0(t4)
	sb t6, 0(t3)
	addi t4, t4, 1
	addi t3, t3, 1
	addi t5, t5, -1
	bnez t5, 215b
	j 214f
213:
214:
23:
	addi t0, s2, 7
	andi t0, t0, -8
	ld ra, 0(t0)
	ld s1, 8(t0)
	ld s2, 16(t0)
	ld s3, 24(t0)
	ld s4, 32(t0)
	ld s5, 40(t0)
	addi sp, sp, 688
	ret
	.option pop

vg_cmac_triple_des_finish:
	.option push
	.option arch, +m, +c
	addi sp, sp, -640
	addi a3, sp, 0
	addi t0, a3, 7
	andi t0, t0, -8
	sd ra, 0(t0)
	sd s1, 8(t0)
	sd s2, 16(t0)
	sd s3, 24(t0)
	addi s1, a0, 0
	addi s2, a3, 0
	addi s3, a2, 0
	beqz a1, 20f
	addi t0, a1, -1
	andi t0, t0, 7
	addi t0, t0, 1
	j 21f
20:
	addi t0, zero, 0
21:
	addi t1, t0, -8
	beqz t1, 22f
	addi t2, zero, 0
	sb t2, 64(s2)
	addi t2, zero, 0
	sb t2, 65(s2)
	addi t2, zero, 0
	sb t2, 66(s2)
	addi t2, zero, 0
	sb t2, 67(s2)
	addi t2, zero, 0
	sb t2, 68(s2)
	addi t2, zero, 0
	sb t2, 69(s2)
	addi t2, zero, 0
	sb t2, 70(s2)
	addi t2, zero, 0
	sb t2, 71(s2)
	addi t3, s2, 64
	addi t4, s1, 408
	addi t5, t0, 0
	beqz t5, 24f
26:
	lbu t6, 0(t4)
	sb t6, 0(t3)
	addi t4, t4, 1
	addi t3, t3, 1
	addi t5, t5, -1
	bnez t5, 26b
	j 25f
24:
25:
	addi t3, s2, 64
	add t3, t3, t0
	addi t2, zero, 128
	sb t2, 0(t3)
	addi t5, s2, 64
	addi t6, s1, 392
	j 23f
22:
	addi t5, s1, 408
	addi t6, s1, 384
23:
	addi a0, s1, 400
	lbu t2, 0(a0)
	lbu t3, 0(t5)
	xor t2, t2, t3
	sb t2, 0(a0)
	lbu t2, 1(a0)
	lbu t3, 1(t5)
	xor t2, t2, t3
	sb t2, 1(a0)
	lbu t2, 2(a0)
	lbu t3, 2(t5)
	xor t2, t2, t3
	sb t2, 2(a0)
	lbu t2, 3(a0)
	lbu t3, 3(t5)
	xor t2, t2, t3
	sb t2, 3(a0)
	lbu t2, 4(a0)
	lbu t3, 4(t5)
	xor t2, t2, t3
	sb t2, 4(a0)
	lbu t2, 5(a0)
	lbu t3, 5(t5)
	xor t2, t2, t3
	sb t2, 5(a0)
	lbu t2, 6(a0)
	lbu t3, 6(t5)
	xor t2, t2, t3
	sb t2, 6(a0)
	lbu t2, 7(a0)
	lbu t3, 7(t5)
	xor t2, t2, t3
	sb t2, 7(a0)
	lbu t2, 0(a0)
	lbu t3, 0(t6)
	xor t2, t2, t3
	sb t2, 0(a0)
	lbu t2, 1(a0)
	lbu t3, 1(t6)
	xor t2, t2, t3
	sb t2, 1(a0)
	lbu t2, 2(a0)
	lbu t3, 2(t6)
	xor t2, t2, t3
	sb t2, 2(a0)
	lbu t2, 3(a0)
	lbu t3, 3(t6)
	xor t2, t2, t3
	sb t2, 3(a0)
	lbu t2, 4(a0)
	lbu t3, 4(t6)
	xor t2, t2, t3
	sb t2, 4(a0)
	lbu t2, 5(a0)
	lbu t3, 5(t6)
	xor t2, t2, t3
	sb t2, 5(a0)
	lbu t2, 6(a0)
	lbu t3, 6(t6)
	xor t2, t2, t3
	sb t2, 6(a0)
	lbu t2, 7(a0)
	lbu t3, 7(t6)
	xor t2, t2, t3
	sb t2, 7(a0)
	addi a0, s1, 0
	addi a1, s1, 400
	addi a2, zero, 1
	call {vg_triple_des_ecb_encrypt}
	lbu t0, 400(s1)
	sb t0, 0(s3)
	lbu t0, 401(s1)
	sb t0, 1(s3)
	lbu t0, 402(s1)
	sb t0, 2(s3)
	lbu t0, 403(s1)
	sb t0, 3(s3)
	lbu t0, 404(s1)
	sb t0, 4(s3)
	lbu t0, 405(s1)
	sb t0, 5(s3)
	lbu t0, 406(s1)
	sb t0, 6(s3)
	lbu t0, 407(s1)
	sb t0, 7(s3)
	addi t0, s2, 7
	andi t0, t0, -8
	ld ra, 0(t0)
	ld s1, 8(t0)
	ld s2, 16(t0)
	ld s3, 24(t0)
	addi sp, sp, 640
	ret
	.option pop
