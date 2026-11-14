// The functions of `src/rc2_cbc.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rc2_cbc_encrypt_chained:
	.option push
	.option arch, +m, +c
	addi sp, sp, -512
	addi a4, sp, 0
	sd s1, 256(a4)
	sd s2, 264(a4)
	sd s3, 272(a4)
	sd s4, 280(a4)
	sd s6, 296(a4)
	sd ra, 304(a4)
	sd s5, 288(a4)
	addi s1, a0, 0
	addi s2, a1, 0
	addi s3, a2, 0
	addi s4, a3, 0
	addi s5, a4, 0
	beqz s4, 20f
22:
	lbu t0, 0(s3)
	lbu a7, 1(s3)
	slli a7, a7, 8
	or t0, t0, a7
	lbu a7, 2(s3)
	slli a7, a7, 16
	or t0, t0, a7
	lbu a7, 3(s3)
	slli a7, a7, 24
	or t0, t0, a7
	lbu t1, 4(s3)
	lbu a7, 5(s3)
	slli a7, a7, 8
	or t1, t1, a7
	lbu a7, 6(s3)
	slli a7, a7, 16
	or t1, t1, a7
	lbu a7, 7(s3)
	slli a7, a7, 24
	or t1, t1, a7
	slli t1, t1, 32
	or t0, t0, t1
	lbu t2, 0(s2)
	lbu a7, 1(s2)
	slli a7, a7, 8
	or t2, t2, a7
	lbu a7, 2(s2)
	slli a7, a7, 16
	or t2, t2, a7
	lbu a7, 3(s2)
	slli a7, a7, 24
	or t2, t2, a7
	lbu t1, 4(s2)
	lbu a7, 5(s2)
	slli a7, a7, 8
	or t1, t1, a7
	lbu a7, 6(s2)
	slli a7, a7, 16
	or t1, t1, a7
	lbu a7, 7(s2)
	slli a7, a7, 24
	or t1, t1, a7
	slli t1, t1, 32
	or t2, t2, t1
	xor t0, t0, t2
	sb t0, 0(s3)
	srli a7, t0, 8
	sb a7, 1(s3)
	srli a7, t0, 16
	sb a7, 2(s3)
	srli a7, t0, 24
	sb a7, 3(s3)
	srli t1, t0, 32
	sb t1, 4(s3)
	srli a7, t1, 8
	sb a7, 5(s3)
	srli a7, t1, 16
	sb a7, 6(s3)
	srli a7, t1, 24
	sb a7, 7(s3)
	addi a0, s1, 0
	addi a1, s3, 0
	addi a2, s5, 0
	call {vg_rc2_encrypt_block}
	lbu t0, 0(s3)
	lbu a7, 1(s3)
	slli a7, a7, 8
	or t0, t0, a7
	lbu a7, 2(s3)
	slli a7, a7, 16
	or t0, t0, a7
	lbu a7, 3(s3)
	slli a7, a7, 24
	or t0, t0, a7
	lbu t1, 4(s3)
	lbu a7, 5(s3)
	slli a7, a7, 8
	or t1, t1, a7
	lbu a7, 6(s3)
	slli a7, a7, 16
	or t1, t1, a7
	lbu a7, 7(s3)
	slli a7, a7, 24
	or t1, t1, a7
	slli t1, t1, 32
	or t0, t0, t1
	sb t0, 0(s2)
	srli a7, t0, 8
	sb a7, 1(s2)
	srli a7, t0, 16
	sb a7, 2(s2)
	srli a7, t0, 24
	sb a7, 3(s2)
	srli t1, t0, 32
	sb t1, 4(s2)
	srli a7, t1, 8
	sb a7, 5(s2)
	srli a7, t1, 16
	sb a7, 6(s2)
	srli a7, t1, 24
	sb a7, 7(s2)
	addi s3, s3, 8
	addi s4, s4, -1
	bnez s4, 22b
	j 21f
20:
21:
	ld s1, 256(s5)
	ld s2, 264(s5)
	ld s3, 272(s5)
	ld s4, 280(s5)
	ld s6, 296(s5)
	ld ra, 304(s5)
	ld s5, 288(s5)
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
	addi sp, sp, 512
	ret
	.option pop

vg_rc2_cbc_decrypt_chained:
	.option push
	.option arch, +m, +c
	addi sp, sp, -512
	addi a4, sp, 0
	sd s1, 256(a4)
	sd s2, 264(a4)
	sd s3, 272(a4)
	sd s4, 280(a4)
	sd s6, 296(a4)
	sd ra, 304(a4)
	sd s5, 288(a4)
	addi s1, a0, 0
	addi s2, a1, 0
	addi s3, a2, 0
	addi s4, a3, 0
	addi s5, a4, 0
	beqz s4, 20f
22:
	lbu s6, 0(s3)
	lbu a7, 1(s3)
	slli a7, a7, 8
	or s6, s6, a7
	lbu a7, 2(s3)
	slli a7, a7, 16
	or s6, s6, a7
	lbu a7, 3(s3)
	slli a7, a7, 24
	or s6, s6, a7
	lbu t1, 4(s3)
	lbu a7, 5(s3)
	slli a7, a7, 8
	or t1, t1, a7
	lbu a7, 6(s3)
	slli a7, a7, 16
	or t1, t1, a7
	lbu a7, 7(s3)
	slli a7, a7, 24
	or t1, t1, a7
	slli t1, t1, 32
	or s6, s6, t1
	addi a0, s1, 0
	addi a1, s3, 0
	addi a2, s5, 0
	call {vg_rc2_decrypt_block}
	lbu t0, 0(s3)
	lbu a7, 1(s3)
	slli a7, a7, 8
	or t0, t0, a7
	lbu a7, 2(s3)
	slli a7, a7, 16
	or t0, t0, a7
	lbu a7, 3(s3)
	slli a7, a7, 24
	or t0, t0, a7
	lbu t1, 4(s3)
	lbu a7, 5(s3)
	slli a7, a7, 8
	or t1, t1, a7
	lbu a7, 6(s3)
	slli a7, a7, 16
	or t1, t1, a7
	lbu a7, 7(s3)
	slli a7, a7, 24
	or t1, t1, a7
	slli t1, t1, 32
	or t0, t0, t1
	lbu t2, 0(s2)
	lbu a7, 1(s2)
	slli a7, a7, 8
	or t2, t2, a7
	lbu a7, 2(s2)
	slli a7, a7, 16
	or t2, t2, a7
	lbu a7, 3(s2)
	slli a7, a7, 24
	or t2, t2, a7
	lbu t1, 4(s2)
	lbu a7, 5(s2)
	slli a7, a7, 8
	or t1, t1, a7
	lbu a7, 6(s2)
	slli a7, a7, 16
	or t1, t1, a7
	lbu a7, 7(s2)
	slli a7, a7, 24
	or t1, t1, a7
	slli t1, t1, 32
	or t2, t2, t1
	xor t0, t0, t2
	sb t0, 0(s3)
	srli a7, t0, 8
	sb a7, 1(s3)
	srli a7, t0, 16
	sb a7, 2(s3)
	srli a7, t0, 24
	sb a7, 3(s3)
	srli t1, t0, 32
	sb t1, 4(s3)
	srli a7, t1, 8
	sb a7, 5(s3)
	srli a7, t1, 16
	sb a7, 6(s3)
	srli a7, t1, 24
	sb a7, 7(s3)
	sb s6, 0(s2)
	srli a7, s6, 8
	sb a7, 1(s2)
	srli a7, s6, 16
	sb a7, 2(s2)
	srli a7, s6, 24
	sb a7, 3(s2)
	srli t1, s6, 32
	sb t1, 4(s2)
	srli a7, t1, 8
	sb a7, 5(s2)
	srli a7, t1, 16
	sb a7, 6(s2)
	srli a7, t1, 24
	sb a7, 7(s2)
	addi s3, s3, 8
	addi s4, s4, -1
	bnez s4, 22b
	j 21f
20:
21:
	ld s1, 256(s5)
	ld s2, 264(s5)
	ld s3, 272(s5)
	ld s4, 280(s5)
	ld s6, 296(s5)
	ld ra, 304(s5)
	ld s5, 288(s5)
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
	addi sp, sp, 512
	ret
	.option pop
