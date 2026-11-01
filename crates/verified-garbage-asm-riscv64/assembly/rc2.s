// The functions of `src/rc2.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rc2_cbc_init:
	.option push
	.option arch, +m, +c
	addi sp, sp, -608
	addi a6, sp, 0
	addi t0, a1, -1
	srli t0, t0, 7
	bnez t0, 20f
	addi t0, a2, -1
	srli t0, t0, 10
	bnez t0, 22f
	addi t0, a4, -8
	bnez t0, 24f
	j 25f
24:
	addi a0, zero, 3
25:
	j 23f
22:
	addi a0, zero, 2
23:
	j 21f
20:
	addi a0, zero, 1
21:
	bnez t0, 26f
	sd ra, 512(a6)
	sd s7, 520(a6)
	addi s7, a6, 0
	lbu t0, 0(a3)
	lbu a7, 1(a3)
	slli a7, a7, 8
	or t0, t0, a7
	lbu a7, 2(a3)
	slli a7, a7, 16
	or t0, t0, a7
	lbu a7, 3(a3)
	slli a7, a7, 24
	or t0, t0, a7
	lbu t1, 4(a3)
	lbu a7, 5(a3)
	slli a7, a7, 8
	or t1, t1, a7
	lbu a7, 6(a3)
	slli a7, a7, 16
	or t1, t1, a7
	lbu a7, 7(a3)
	slli a7, a7, 24
	or t1, t1, a7
	slli t1, t1, 32
	or t0, t0, t1
	addi t2, a5, 128
	sb t0, 0(t2)
	srli a7, t0, 8
	sb a7, 1(t2)
	srli a7, t0, 16
	sb a7, 2(t2)
	srli a7, t0, 24
	sb a7, 3(t2)
	srli t1, t0, 32
	sb t1, 4(t2)
	srli a7, t1, 8
	sb a7, 5(t2)
	srli a7, t1, 16
	sb a7, 6(t2)
	srli a7, t1, 24
	sb a7, 7(t2)
	addi a3, a5, 0
	addi a4, a6, 0
	call {vg_rc2_expand_key}
	addi a0, zero, 0
	ld ra, 512(s7)
	ld s7, 520(s7)
	j 27f
26:
27:
	addi t5, sp, 0
	addi t6, zero, 0
	sd t6, 0(t5)
	sd t6, 8(t5)
	sd t6, 16(t5)
	sd t6, 24(t5)
	sd t6, 32(t5)
	sd t6, 40(t5)
	sd t6, 48(t5)
	sd t6, 56(t5)
	sd t6, 64(t5)
	sd t6, 72(t5)
	sd t6, 80(t5)
	sd t6, 88(t5)
	sd t6, 96(t5)
	sd t6, 104(t5)
	sd t6, 112(t5)
	sd t6, 120(t5)
	sd t6, 128(t5)
	sd t6, 136(t5)
	sd t6, 144(t5)
	sd t6, 152(t5)
	sd t6, 160(t5)
	sd t6, 168(t5)
	sd t6, 176(t5)
	sd t6, 184(t5)
	sd t6, 192(t5)
	sd t6, 200(t5)
	sd t6, 208(t5)
	sd t6, 216(t5)
	sd t6, 224(t5)
	sd t6, 232(t5)
	sd t6, 240(t5)
	sd t6, 248(t5)
	sd t6, 256(t5)
	sd t6, 264(t5)
	sd t6, 272(t5)
	sd t6, 280(t5)
	sd t6, 288(t5)
	sd t6, 296(t5)
	sd t6, 304(t5)
	sd t6, 312(t5)
	sd t6, 320(t5)
	sd t6, 328(t5)
	sd t6, 336(t5)
	sd t6, 344(t5)
	sd t6, 352(t5)
	sd t6, 360(t5)
	sd t6, 368(t5)
	sd t6, 376(t5)
	sd t6, 384(t5)
	sd t6, 392(t5)
	sd t6, 400(t5)
	sd t6, 408(t5)
	sd t6, 416(t5)
	sd t6, 424(t5)
	sd t6, 432(t5)
	sd t6, 440(t5)
	sd t6, 448(t5)
	sd t6, 456(t5)
	sd t6, 464(t5)
	sd t6, 472(t5)
	sd t6, 480(t5)
	sd t6, 488(t5)
	sd t6, 496(t5)
	sd t6, 504(t5)
	sd t6, 512(t5)
	sd t6, 520(t5)
	sd t6, 528(t5)
	sd t6, 536(t5)
	sd t6, 544(t5)
	sd t6, 552(t5)
	sd t6, 560(t5)
	sd t6, 568(t5)
	addi sp, sp, 608
	ret
	.option pop

vg_rc2_cbc_encrypt_update:
	.option push
	.option arch, +m, +c
	addi sp, sp, -608
	addi a6, sp, 0
	beqz a5, 20f
	sd ra, 512(a6)
	sd s7, 520(a6)
	addi s7, a6, 0
	addi t0, a0, 136
	addi t1, a4, 0
	addi t2, a1, 0
	beqz t2, 22f
24:
	lbu a7, 0(t0)
	sb a7, 0(t1)
	addi t0, t0, 1
	addi t1, t1, 1
	addi t2, t2, -1
	bnez t2, 24b
	j 23f
22:
23:
	sub t2, a5, a1
	beqz t2, 25f
27:
	lbu a7, 0(a2)
	sb a7, 0(t1)
	addi a2, a2, 1
	addi t1, t1, 1
	addi t2, t2, -1
	bnez t2, 27b
	j 26f
25:
26:
	addi t0, a0, 136
	sub t2, a3, a5
	add t2, t2, a1
	beqz t2, 28f
210:
	lbu a7, 0(a2)
	sb a7, 0(t0)
	addi a2, a2, 1
	addi t0, t0, 1
	addi t2, t2, -1
	bnez t2, 210b
	j 29f
28:
29:
	addi a1, a0, 128
	addi a2, a4, 0
	srli a3, a5, 3
	addi a4, a6, 0
	call {vg_rc2_cbc_encrypt}
	ld ra, 512(s7)
	ld s7, 520(s7)
	j 21f
20:
	add t0, a0, a1
	beqz a3, 211f
213:
	lbu a7, 0(a2)
	sb a7, 136(t0)
	addi a2, a2, 1
	addi t0, t0, 1
	addi a3, a3, -1
	bnez a3, 213b
	j 212f
211:
212:
21:
	addi t5, sp, 0
	addi t6, zero, 0
	sd t6, 0(t5)
	sd t6, 8(t5)
	sd t6, 16(t5)
	sd t6, 24(t5)
	sd t6, 32(t5)
	sd t6, 40(t5)
	sd t6, 48(t5)
	sd t6, 56(t5)
	sd t6, 64(t5)
	sd t6, 72(t5)
	sd t6, 80(t5)
	sd t6, 88(t5)
	sd t6, 96(t5)
	sd t6, 104(t5)
	sd t6, 112(t5)
	sd t6, 120(t5)
	sd t6, 128(t5)
	sd t6, 136(t5)
	sd t6, 144(t5)
	sd t6, 152(t5)
	sd t6, 160(t5)
	sd t6, 168(t5)
	sd t6, 176(t5)
	sd t6, 184(t5)
	sd t6, 192(t5)
	sd t6, 200(t5)
	sd t6, 208(t5)
	sd t6, 216(t5)
	sd t6, 224(t5)
	sd t6, 232(t5)
	sd t6, 240(t5)
	sd t6, 248(t5)
	sd t6, 256(t5)
	sd t6, 264(t5)
	sd t6, 272(t5)
	sd t6, 280(t5)
	sd t6, 288(t5)
	sd t6, 296(t5)
	sd t6, 304(t5)
	sd t6, 312(t5)
	sd t6, 320(t5)
	sd t6, 328(t5)
	sd t6, 336(t5)
	sd t6, 344(t5)
	sd t6, 352(t5)
	sd t6, 360(t5)
	sd t6, 368(t5)
	sd t6, 376(t5)
	sd t6, 384(t5)
	sd t6, 392(t5)
	sd t6, 400(t5)
	sd t6, 408(t5)
	sd t6, 416(t5)
	sd t6, 424(t5)
	sd t6, 432(t5)
	sd t6, 440(t5)
	sd t6, 448(t5)
	sd t6, 456(t5)
	sd t6, 464(t5)
	sd t6, 472(t5)
	sd t6, 480(t5)
	sd t6, 488(t5)
	sd t6, 496(t5)
	sd t6, 504(t5)
	sd t6, 512(t5)
	sd t6, 520(t5)
	sd t6, 528(t5)
	sd t6, 536(t5)
	sd t6, 544(t5)
	sd t6, 552(t5)
	sd t6, 560(t5)
	sd t6, 568(t5)
	addi sp, sp, 608
	ret
	.option pop

vg_rc2_cbc_decrypt_update:
	.option push
	.option arch, +m, +c
	addi sp, sp, -608
	addi a6, sp, 0
	beqz a5, 20f
	sd ra, 512(a6)
	sd s7, 520(a6)
	addi s7, a6, 0
	addi t0, a0, 136
	addi t1, a4, 0
	addi t2, a1, 0
	beqz t2, 22f
24:
	lbu a7, 0(t0)
	sb a7, 0(t1)
	addi t0, t0, 1
	addi t1, t1, 1
	addi t2, t2, -1
	bnez t2, 24b
	j 23f
22:
23:
	sub t2, a5, a1
	beqz t2, 25f
27:
	lbu a7, 0(a2)
	sb a7, 0(t1)
	addi a2, a2, 1
	addi t1, t1, 1
	addi t2, t2, -1
	bnez t2, 27b
	j 26f
25:
26:
	addi t0, a0, 136
	sub t2, a3, a5
	add t2, t2, a1
	beqz t2, 28f
210:
	lbu a7, 0(a2)
	sb a7, 0(t0)
	addi a2, a2, 1
	addi t0, t0, 1
	addi t2, t2, -1
	bnez t2, 210b
	j 29f
28:
29:
	addi a1, a0, 128
	addi a2, a4, 0
	srli a3, a5, 3
	addi a4, a6, 0
	call {vg_rc2_cbc_decrypt}
	ld ra, 512(s7)
	ld s7, 520(s7)
	j 21f
20:
	add t0, a0, a1
	beqz a3, 211f
213:
	lbu a7, 0(a2)
	sb a7, 136(t0)
	addi a2, a2, 1
	addi t0, t0, 1
	addi a3, a3, -1
	bnez a3, 213b
	j 212f
211:
212:
21:
	addi t5, sp, 0
	addi t6, zero, 0
	sd t6, 0(t5)
	sd t6, 8(t5)
	sd t6, 16(t5)
	sd t6, 24(t5)
	sd t6, 32(t5)
	sd t6, 40(t5)
	sd t6, 48(t5)
	sd t6, 56(t5)
	sd t6, 64(t5)
	sd t6, 72(t5)
	sd t6, 80(t5)
	sd t6, 88(t5)
	sd t6, 96(t5)
	sd t6, 104(t5)
	sd t6, 112(t5)
	sd t6, 120(t5)
	sd t6, 128(t5)
	sd t6, 136(t5)
	sd t6, 144(t5)
	sd t6, 152(t5)
	sd t6, 160(t5)
	sd t6, 168(t5)
	sd t6, 176(t5)
	sd t6, 184(t5)
	sd t6, 192(t5)
	sd t6, 200(t5)
	sd t6, 208(t5)
	sd t6, 216(t5)
	sd t6, 224(t5)
	sd t6, 232(t5)
	sd t6, 240(t5)
	sd t6, 248(t5)
	sd t6, 256(t5)
	sd t6, 264(t5)
	sd t6, 272(t5)
	sd t6, 280(t5)
	sd t6, 288(t5)
	sd t6, 296(t5)
	sd t6, 304(t5)
	sd t6, 312(t5)
	sd t6, 320(t5)
	sd t6, 328(t5)
	sd t6, 336(t5)
	sd t6, 344(t5)
	sd t6, 352(t5)
	sd t6, 360(t5)
	sd t6, 368(t5)
	sd t6, 376(t5)
	sd t6, 384(t5)
	sd t6, 392(t5)
	sd t6, 400(t5)
	sd t6, 408(t5)
	sd t6, 416(t5)
	sd t6, 424(t5)
	sd t6, 432(t5)
	sd t6, 440(t5)
	sd t6, 448(t5)
	sd t6, 456(t5)
	sd t6, 464(t5)
	sd t6, 472(t5)
	sd t6, 480(t5)
	sd t6, 488(t5)
	sd t6, 496(t5)
	sd t6, 504(t5)
	sd t6, 512(t5)
	sd t6, 520(t5)
	sd t6, 528(t5)
	sd t6, 536(t5)
	sd t6, 544(t5)
	sd t6, 552(t5)
	sd t6, 560(t5)
	sd t6, 568(t5)
	addi sp, sp, 608
	ret
	.option pop
