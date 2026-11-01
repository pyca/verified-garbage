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

vg_rc2_cbc_encrypt:
	.option push
	.option arch, +m, +c
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
	ret
	.option pop

vg_rc2_cbc_decrypt:
	.option push
	.option arch, +m, +c
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
	ret
	.option pop

vg_rc2_expand_key:
	.option push
	.option arch, +m, +c
	lui t0, 973662
	addiw t0, t0, -742
	slli t0, t0, 32
	lui t1, 806808
	addiw t1, t1, -1831
	add t0, t0, t1
	sd t0, 0(a4)
	lui t0, 646538
	addiw t0, t0, 74
	slli t0, t0, 32
	lui t1, 499679
	addiw t1, t1, -1752
	add t0, t0, t1
	sd t0, 8(a4)
	lui t0, 582967
	addiw t0, t0, 1580
	slli t0, t0, 32
	lui t1, 537464
	addiw t1, t1, -314
	add t0, t0, t1
	sd t0, 16(a4)
	lui t0, 667577
	addiw t0, t0, -1211
	slli t0, t0, 32
	lui t1, 558661
	addiw t1, t1, -926
	add t0, t0, t1
	sd t0, 24(a4)
	lui t0, 79099
	addiw t0, t0, 904
	slli t0, t0, 32
	lui t1, 1004954
	addiw t1, t1, -1513
	add t0, t0, t1
	sd t0, 32(a4)
	lui t0, 206808
	addiw t0, t0, 266
	slli t0, t0, 32
	lui t1, 579284
	addiw t1, t1, 1377
	add t0, t0, t1
	sd t0, 40(a4)
	lui t0, 47035
	addiw t0, t0, 1927
	slli t0, t0, 32
	lui t1, 963593
	addiw t1, t1, -67
	add t0, t0, t1
	sd t0, 48(a4)
	lui t0, 533735
	addiw t0, t0, -1188
	slli t0, t0, 32
	lui t1, 139801
	addiw t1, t1, 1520
	add t0, t0, t1
	sd t0, 56(a4)
	lui t0, 117542
	addiw t0, t0, 207
	slli t0, t0, 32
	lui t1, 603741
	addiw t1, t1, 1620
	add t0, t0, t1
	sd t0, 64(a4)
	lui t0, 904985
	addiw t0, t0, -857
	slli t0, t0, 32
	lui t1, 84997
	addiw t1, t1, 1651
	add t0, t0, t1
	sd t0, 72(a4)
	lui t0, 859724
	addiw t0, t0, -453
	slli t0, t0, 32
	lui t1, 130215
	addiw t1, t1, 1298
	add t0, t0, t1
	sd t0, 80(a4)
	lui t0, 158564
	addiw t0, t0, -861
	slli t0, t0, 32
	lui t1, 200004
	addiw t1, t1, -702
	add t0, t0, t1
	sd t0, 88(a4)
	lui t0, 356471
	addiw t0, t0, -1721
	slli t0, t0, 32
	lui t1, 893164
	addiw t1, t1, -145
	add t0, t0, t1
	sd t0, 96(a4)
	lui t0, 13369
	addiw t0, t0, 1213
	slli t0, t0, 32
	lui t1, 635359
	addiw t1, t1, 551
	add t0, t0, t1
	sd t0, 104(a4)
	lui t0, 947183
	addiw t0, t0, -111
	slli t0, t0, 32
	lui t1, 1010801
	addiw t1, t1, 504
	add t0, t0, t1
	sd t0, 112(a4)
	lui t0, 881126
	addiw t0, t0, 1736
	slli t0, t0, 32
	lui t1, 195932
	addiw t1, t1, 774
	add t0, t0, t1
	sd t0, 120(a4)
	lui t0, 1015525
	addiw t0, t0, 641
	slli t0, t0, 32
	lui t1, 913071
	addiw t1, t1, -2040
	add t0, t0, t1
	sd t0, 128(a4)
	lui t0, 173733
	addiw t0, t0, -714
	slli t0, t0, 32
	lui t1, 706347
	addiw t1, t1, -1404
	add t0, t0, t1
	sd t0, 136(a4)
	lui t0, 476305
	addiw t0, t0, 1370
	slli t0, t0, 32
	lui t1, 466210
	addiw t1, t1, -1386
	add t0, t0, t1
	sd t0, 144(a4)
	lui t0, 969282
	addiw t0, t0, -2044
	slli t0, t0, 32
	lui t1, 388362
	addiw t1, t1, -181
	add t0, t0, t1
	sd t0, 152(a4)
	lui t0, 838837
	addiw t0, t0, 271
	slli t0, t0, 32
	lui t1, 451614
	addiw t1, t1, 194
	add t0, t0, t1
	sd t0, 160(a4)
	lui t0, 235279
	addiw t0, t0, 1185
	slli t0, t0, 32
	lui t1, 330489
	addiw t1, t1, 292
	add t0, t0, t1
	sd t0, 168(a4)
	lui t0, 502604
	addiw t0, t0, -2012
	slli t0, t0, 32
	lui t1, 545704
	addiw t1, t1, -871
	add t0, t0, t1
	sd t0, 176(a4)
	lui t0, 203125
	addiw t0, t0, 1317
	slli t0, t0, 32
	lui t1, 373600
	addiw t1, t1, 764
	add t0, t0, t1
	sd t0, 184(a4)
	lui t0, 715049
	addiw t0, t0, -1308
	slli t0, t0, 32
	lui t1, 626598
	addiw t1, t1, -723
	add t0, t0, t1
	sd t0, 192(a4)
	lui t0, 826279
	addiw t0, t0, -921
	slli t0, t0, 32
	lui t1, 66206
	addiw t1, t1, -251
	add t0, t0, t1
	sd t0, 200(a4)
	lui t0, 182922
	addiw t0, t0, -286
	slli t0, t0, 32
	lui t1, 851552
	addiw t1, t1, 211
	add t0, t0, t1
	sd t0, 208(a4)
	lui t0, 694430
	addiw t0, t0, 600
	slli t0, t0, 32
	lui t1, 258065
	addiw t1, t1, 1635
	add t0, t0, t1
	sd t0, 216(a4)
	lui t0, 724979
	addiw t0, t0, 939
	slli t0, t0, 32
	lui t1, 111428
	addiw t1, t1, -2035
	add t0, t0, t1
	sd t0, 224(a4)
	lui t0, 191707
	addiw t0, t0, 441
	slli t0, t0, 32
	lui t1, 389317
	addiw t1, t1, -1861
	add t0, t0, t1
	sd t0, 232(a4)
	lui t0, 489930
	addiw t0, t0, 1509
	slli t0, t0, 32
	lui t1, 294335
	addiw t1, t1, 965
	add t0, t0, t1
	sd t0, 240(a4)
	lui t0, 711704
	addiw t0, t0, -2
	slli t0, t0, 32
	lui t1, 426506
	addiw t1, t1, 1546
	add t0, t0, t1
	sd t0, 248(a4)
	addi a5, zero, 0
20:
	add a6, a0, a5
	lbu t2, 0(a6)
	add a6, a3, a5
	sb t2, 0(a6)
	addi a5, a5, 1
	sub a7, a5, a1
	bnez a7, 20b
	addi a7, zero, 128
	sub a7, a5, a7
	beqz a7, 21f
23:
	add a6, a3, a5
	addi a6, a6, -1
	lbu t0, 0(a6)
	sub a6, a5, a1
	add a6, a3, a6
	lbu t1, 0(a6)
	add t0, t0, t1
	slli t0, t0, 56
	srli t0, t0, 56
	srli t3, t0, 3
	addi t2, zero, 1
	sll t3, t2, t3
	slli t2, t3, 63
	srai t2, t2, 63
	ld t1, 0(a4)
	and t1, t1, t2
	slli t2, t3, 62
	srai t2, t2, 63
	ld a7, 8(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 61
	srai t2, t2, 63
	ld a7, 16(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 60
	srai t2, t2, 63
	ld a7, 24(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 59
	srai t2, t2, 63
	ld a7, 32(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 58
	srai t2, t2, 63
	ld a7, 40(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 57
	srai t2, t2, 63
	ld a7, 48(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 56
	srai t2, t2, 63
	ld a7, 56(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 55
	srai t2, t2, 63
	ld a7, 64(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 54
	srai t2, t2, 63
	ld a7, 72(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 53
	srai t2, t2, 63
	ld a7, 80(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 52
	srai t2, t2, 63
	ld a7, 88(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 51
	srai t2, t2, 63
	ld a7, 96(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 50
	srai t2, t2, 63
	ld a7, 104(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 49
	srai t2, t2, 63
	ld a7, 112(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 48
	srai t2, t2, 63
	ld a7, 120(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 47
	srai t2, t2, 63
	ld a7, 128(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 46
	srai t2, t2, 63
	ld a7, 136(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 45
	srai t2, t2, 63
	ld a7, 144(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 44
	srai t2, t2, 63
	ld a7, 152(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 43
	srai t2, t2, 63
	ld a7, 160(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 42
	srai t2, t2, 63
	ld a7, 168(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 41
	srai t2, t2, 63
	ld a7, 176(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 40
	srai t2, t2, 63
	ld a7, 184(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 39
	srai t2, t2, 63
	ld a7, 192(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 38
	srai t2, t2, 63
	ld a7, 200(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 37
	srai t2, t2, 63
	ld a7, 208(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 36
	srai t2, t2, 63
	ld a7, 216(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 35
	srai t2, t2, 63
	ld a7, 224(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 34
	srai t2, t2, 63
	ld a7, 232(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 33
	srai t2, t2, 63
	ld a7, 240(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 32
	srai t2, t2, 63
	ld a7, 248(a4)
	and a7, a7, t2
	or t1, t1, a7
	andi t2, t0, 7
	slli t2, t2, 3
	srl t1, t1, t2
	slli t1, t1, 56
	srli t1, t1, 56
	add a6, a3, a5
	sb t1, 0(a6)
	addi a5, a5, 1
	addi a7, zero, 128
	sub a7, a5, a7
	bnez a7, 23b
	j 22f
21:
22:
	addi t4, a2, 7
	srli t4, t4, 3
	addi a5, zero, 128
	sub a5, a5, t4
	slli a6, a2, 61
	srli a6, a6, 61
	addi t2, zero, 255
	addi t0, a6, -1
	beqz t0, 24f
	j 25f
24:
	addi t2, zero, 1
25:
	addi t0, a6, -2
	beqz t0, 26f
	j 27f
26:
	addi t2, zero, 3
27:
	addi t0, a6, -3
	beqz t0, 28f
	j 29f
28:
	addi t2, zero, 7
29:
	addi t0, a6, -4
	beqz t0, 210f
	j 211f
210:
	addi t2, zero, 15
211:
	addi t0, a6, -5
	beqz t0, 212f
	j 213f
212:
	addi t2, zero, 31
213:
	addi t0, a6, -6
	beqz t0, 214f
	j 215f
214:
	addi t2, zero, 63
215:
	addi t0, a6, -7
	beqz t0, 216f
	j 217f
216:
	addi t2, zero, 127
217:
	add a6, a3, a5
	lbu t0, 0(a6)
	and t0, t0, t2
	srli t3, t0, 3
	addi t2, zero, 1
	sll t3, t2, t3
	slli t2, t3, 63
	srai t2, t2, 63
	ld t1, 0(a4)
	and t1, t1, t2
	slli t2, t3, 62
	srai t2, t2, 63
	ld a7, 8(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 61
	srai t2, t2, 63
	ld a7, 16(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 60
	srai t2, t2, 63
	ld a7, 24(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 59
	srai t2, t2, 63
	ld a7, 32(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 58
	srai t2, t2, 63
	ld a7, 40(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 57
	srai t2, t2, 63
	ld a7, 48(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 56
	srai t2, t2, 63
	ld a7, 56(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 55
	srai t2, t2, 63
	ld a7, 64(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 54
	srai t2, t2, 63
	ld a7, 72(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 53
	srai t2, t2, 63
	ld a7, 80(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 52
	srai t2, t2, 63
	ld a7, 88(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 51
	srai t2, t2, 63
	ld a7, 96(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 50
	srai t2, t2, 63
	ld a7, 104(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 49
	srai t2, t2, 63
	ld a7, 112(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 48
	srai t2, t2, 63
	ld a7, 120(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 47
	srai t2, t2, 63
	ld a7, 128(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 46
	srai t2, t2, 63
	ld a7, 136(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 45
	srai t2, t2, 63
	ld a7, 144(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 44
	srai t2, t2, 63
	ld a7, 152(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 43
	srai t2, t2, 63
	ld a7, 160(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 42
	srai t2, t2, 63
	ld a7, 168(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 41
	srai t2, t2, 63
	ld a7, 176(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 40
	srai t2, t2, 63
	ld a7, 184(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 39
	srai t2, t2, 63
	ld a7, 192(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 38
	srai t2, t2, 63
	ld a7, 200(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 37
	srai t2, t2, 63
	ld a7, 208(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 36
	srai t2, t2, 63
	ld a7, 216(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 35
	srai t2, t2, 63
	ld a7, 224(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 34
	srai t2, t2, 63
	ld a7, 232(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 33
	srai t2, t2, 63
	ld a7, 240(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 32
	srai t2, t2, 63
	ld a7, 248(a4)
	and a7, a7, t2
	or t1, t1, a7
	andi t2, t0, 7
	slli t2, t2, 3
	srl t1, t1, t2
	slli t1, t1, 56
	srli t1, t1, 56
	add a6, a3, a5
	sb t1, 0(a6)
	beqz a5, 218f
220:
	addi a5, a5, -1
	add a6, a3, a5
	lbu t0, 1(a6)
	add a6, a5, t4
	add a6, a3, a6
	lbu t1, 0(a6)
	xor t0, t0, t1
	srli t3, t0, 3
	addi t2, zero, 1
	sll t3, t2, t3
	slli t2, t3, 63
	srai t2, t2, 63
	ld t1, 0(a4)
	and t1, t1, t2
	slli t2, t3, 62
	srai t2, t2, 63
	ld a7, 8(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 61
	srai t2, t2, 63
	ld a7, 16(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 60
	srai t2, t2, 63
	ld a7, 24(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 59
	srai t2, t2, 63
	ld a7, 32(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 58
	srai t2, t2, 63
	ld a7, 40(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 57
	srai t2, t2, 63
	ld a7, 48(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 56
	srai t2, t2, 63
	ld a7, 56(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 55
	srai t2, t2, 63
	ld a7, 64(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 54
	srai t2, t2, 63
	ld a7, 72(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 53
	srai t2, t2, 63
	ld a7, 80(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 52
	srai t2, t2, 63
	ld a7, 88(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 51
	srai t2, t2, 63
	ld a7, 96(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 50
	srai t2, t2, 63
	ld a7, 104(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 49
	srai t2, t2, 63
	ld a7, 112(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 48
	srai t2, t2, 63
	ld a7, 120(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 47
	srai t2, t2, 63
	ld a7, 128(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 46
	srai t2, t2, 63
	ld a7, 136(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 45
	srai t2, t2, 63
	ld a7, 144(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 44
	srai t2, t2, 63
	ld a7, 152(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 43
	srai t2, t2, 63
	ld a7, 160(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 42
	srai t2, t2, 63
	ld a7, 168(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 41
	srai t2, t2, 63
	ld a7, 176(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 40
	srai t2, t2, 63
	ld a7, 184(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 39
	srai t2, t2, 63
	ld a7, 192(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 38
	srai t2, t2, 63
	ld a7, 200(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 37
	srai t2, t2, 63
	ld a7, 208(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 36
	srai t2, t2, 63
	ld a7, 216(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 35
	srai t2, t2, 63
	ld a7, 224(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 34
	srai t2, t2, 63
	ld a7, 232(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 33
	srai t2, t2, 63
	ld a7, 240(a4)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 32
	srai t2, t2, 63
	ld a7, 248(a4)
	and a7, a7, t2
	or t1, t1, a7
	andi t2, t0, 7
	slli t2, t2, 3
	srl t1, t1, t2
	slli t1, t1, 56
	srli t1, t1, 56
	add a6, a3, a5
	sb t1, 0(a6)
	bnez a5, 220b
	j 219f
218:
219:
	ret
	.option pop

vg_rc2_encrypt_block:
	.option push
	.option arch, +m, +c
	andi t0, a0, 7
	beqz t0, 20f
	addi t3, a0, 0
	addi t4, a2, 0
	addi t5, zero, 128
22:
	lbu a7, 0(t3)
	sb a7, 0(t4)
	addi t3, t3, 1
	addi t4, t4, 1
	addi t5, t5, -1
	bnez t5, 22b
	j 21f
20:
	addi a2, a0, 0
21:
	lbu t1, 0(a1)
	lbu a7, 1(a1)
	slli a7, a7, 8
	or t1, t1, a7
	lbu a7, 2(a1)
	slli a7, a7, 16
	or t1, t1, a7
	lbu a7, 3(a1)
	slli a7, a7, 24
	or t1, t1, a7
	lbu t2, 4(a1)
	lbu a7, 5(a1)
	slli a7, a7, 8
	or t2, t2, a7
	lbu a7, 6(a1)
	slli a7, a7, 16
	or t2, t2, a7
	lbu a7, 7(a1)
	slli a7, a7, 24
	or t2, t2, a7
	slli t2, t2, 32
	or t1, t1, t2
	slli a3, t1, 48
	srli a3, a3, 48
	slli a4, t1, 32
	srli a4, a4, 48
	slli a5, t1, 16
	srli a5, a5, 48
	srli a6, t1, 48
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 0(a2)
	add a3, a3, t2
	add a3, a3, t0
	add a3, a3, t1
	slli a7, a3, 49
	srli a7, a7, 48
	slli a3, a3, 48
	srli a3, a3, 63
	or a3, a3, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 2(a2)
	add a4, a4, t2
	add a4, a4, t0
	add a4, a4, t1
	slli a7, a4, 50
	srli a7, a7, 48
	slli a4, a4, 48
	srli a4, a4, 62
	or a4, a4, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 4(a2)
	add a5, a5, t2
	add a5, a5, t0
	add a5, a5, t1
	slli a7, a5, 51
	srli a7, a7, 48
	slli a5, a5, 48
	srli a5, a5, 61
	or a5, a5, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 6(a2)
	add a6, a6, t2
	add a6, a6, t0
	add a6, a6, t1
	slli a7, a6, 53
	srli a7, a7, 48
	slli a6, a6, 48
	srli a6, a6, 59
	or a6, a6, a7
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 8(a2)
	add a3, a3, t2
	add a3, a3, t0
	add a3, a3, t1
	slli a7, a3, 49
	srli a7, a7, 48
	slli a3, a3, 48
	srli a3, a3, 63
	or a3, a3, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 10(a2)
	add a4, a4, t2
	add a4, a4, t0
	add a4, a4, t1
	slli a7, a4, 50
	srli a7, a7, 48
	slli a4, a4, 48
	srli a4, a4, 62
	or a4, a4, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 12(a2)
	add a5, a5, t2
	add a5, a5, t0
	add a5, a5, t1
	slli a7, a5, 51
	srli a7, a7, 48
	slli a5, a5, 48
	srli a5, a5, 61
	or a5, a5, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 14(a2)
	add a6, a6, t2
	add a6, a6, t0
	add a6, a6, t1
	slli a7, a6, 53
	srli a7, a7, 48
	slli a6, a6, 48
	srli a6, a6, 59
	or a6, a6, a7
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 16(a2)
	add a3, a3, t2
	add a3, a3, t0
	add a3, a3, t1
	slli a7, a3, 49
	srli a7, a7, 48
	slli a3, a3, 48
	srli a3, a3, 63
	or a3, a3, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 18(a2)
	add a4, a4, t2
	add a4, a4, t0
	add a4, a4, t1
	slli a7, a4, 50
	srli a7, a7, 48
	slli a4, a4, 48
	srli a4, a4, 62
	or a4, a4, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 20(a2)
	add a5, a5, t2
	add a5, a5, t0
	add a5, a5, t1
	slli a7, a5, 51
	srli a7, a7, 48
	slli a5, a5, 48
	srli a5, a5, 61
	or a5, a5, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 22(a2)
	add a6, a6, t2
	add a6, a6, t0
	add a6, a6, t1
	slli a7, a6, 53
	srli a7, a7, 48
	slli a6, a6, 48
	srli a6, a6, 59
	or a6, a6, a7
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 24(a2)
	add a3, a3, t2
	add a3, a3, t0
	add a3, a3, t1
	slli a7, a3, 49
	srli a7, a7, 48
	slli a3, a3, 48
	srli a3, a3, 63
	or a3, a3, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 26(a2)
	add a4, a4, t2
	add a4, a4, t0
	add a4, a4, t1
	slli a7, a4, 50
	srli a7, a7, 48
	slli a4, a4, 48
	srli a4, a4, 62
	or a4, a4, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 28(a2)
	add a5, a5, t2
	add a5, a5, t0
	add a5, a5, t1
	slli a7, a5, 51
	srli a7, a7, 48
	slli a5, a5, 48
	srli a5, a5, 61
	or a5, a5, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 30(a2)
	add a6, a6, t2
	add a6, a6, t0
	add a6, a6, t1
	slli a7, a6, 53
	srli a7, a7, 48
	slli a6, a6, 48
	srli a6, a6, 59
	or a6, a6, a7
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 32(a2)
	add a3, a3, t2
	add a3, a3, t0
	add a3, a3, t1
	slli a7, a3, 49
	srli a7, a7, 48
	slli a3, a3, 48
	srli a3, a3, 63
	or a3, a3, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 34(a2)
	add a4, a4, t2
	add a4, a4, t0
	add a4, a4, t1
	slli a7, a4, 50
	srli a7, a7, 48
	slli a4, a4, 48
	srli a4, a4, 62
	or a4, a4, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 36(a2)
	add a5, a5, t2
	add a5, a5, t0
	add a5, a5, t1
	slli a7, a5, 51
	srli a7, a7, 48
	slli a5, a5, 48
	srli a5, a5, 61
	or a5, a5, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 38(a2)
	add a6, a6, t2
	add a6, a6, t0
	add a6, a6, t1
	slli a7, a6, 53
	srli a7, a7, 48
	slli a6, a6, 48
	srli a6, a6, 59
	or a6, a6, a7
	slli t0, a6, 58
	srli t0, t0, 57
	srli t3, t0, 3
	addi t2, zero, 1
	sll t3, t2, t3
	slli t2, t3, 63
	srai t2, t2, 63
	ld t1, 0(a2)
	and t1, t1, t2
	slli t2, t3, 62
	srai t2, t2, 63
	ld a7, 8(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 61
	srai t2, t2, 63
	ld a7, 16(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 60
	srai t2, t2, 63
	ld a7, 24(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 59
	srai t2, t2, 63
	ld a7, 32(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 58
	srai t2, t2, 63
	ld a7, 40(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 57
	srai t2, t2, 63
	ld a7, 48(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 56
	srai t2, t2, 63
	ld a7, 56(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 55
	srai t2, t2, 63
	ld a7, 64(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 54
	srai t2, t2, 63
	ld a7, 72(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 53
	srai t2, t2, 63
	ld a7, 80(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 52
	srai t2, t2, 63
	ld a7, 88(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 51
	srai t2, t2, 63
	ld a7, 96(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 50
	srai t2, t2, 63
	ld a7, 104(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 49
	srai t2, t2, 63
	ld a7, 112(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 48
	srai t2, t2, 63
	ld a7, 120(a2)
	and a7, a7, t2
	or t1, t1, a7
	andi t2, t0, 6
	slli t2, t2, 3
	srl t1, t1, t2
	slli t1, t1, 48
	srli t1, t1, 48
	add a3, a3, t1
	slli a3, a3, 48
	srli a3, a3, 48
	slli t0, a3, 58
	srli t0, t0, 57
	srli t3, t0, 3
	addi t2, zero, 1
	sll t3, t2, t3
	slli t2, t3, 63
	srai t2, t2, 63
	ld t1, 0(a2)
	and t1, t1, t2
	slli t2, t3, 62
	srai t2, t2, 63
	ld a7, 8(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 61
	srai t2, t2, 63
	ld a7, 16(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 60
	srai t2, t2, 63
	ld a7, 24(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 59
	srai t2, t2, 63
	ld a7, 32(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 58
	srai t2, t2, 63
	ld a7, 40(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 57
	srai t2, t2, 63
	ld a7, 48(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 56
	srai t2, t2, 63
	ld a7, 56(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 55
	srai t2, t2, 63
	ld a7, 64(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 54
	srai t2, t2, 63
	ld a7, 72(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 53
	srai t2, t2, 63
	ld a7, 80(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 52
	srai t2, t2, 63
	ld a7, 88(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 51
	srai t2, t2, 63
	ld a7, 96(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 50
	srai t2, t2, 63
	ld a7, 104(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 49
	srai t2, t2, 63
	ld a7, 112(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 48
	srai t2, t2, 63
	ld a7, 120(a2)
	and a7, a7, t2
	or t1, t1, a7
	andi t2, t0, 6
	slli t2, t2, 3
	srl t1, t1, t2
	slli t1, t1, 48
	srli t1, t1, 48
	add a4, a4, t1
	slli a4, a4, 48
	srli a4, a4, 48
	slli t0, a4, 58
	srli t0, t0, 57
	srli t3, t0, 3
	addi t2, zero, 1
	sll t3, t2, t3
	slli t2, t3, 63
	srai t2, t2, 63
	ld t1, 0(a2)
	and t1, t1, t2
	slli t2, t3, 62
	srai t2, t2, 63
	ld a7, 8(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 61
	srai t2, t2, 63
	ld a7, 16(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 60
	srai t2, t2, 63
	ld a7, 24(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 59
	srai t2, t2, 63
	ld a7, 32(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 58
	srai t2, t2, 63
	ld a7, 40(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 57
	srai t2, t2, 63
	ld a7, 48(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 56
	srai t2, t2, 63
	ld a7, 56(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 55
	srai t2, t2, 63
	ld a7, 64(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 54
	srai t2, t2, 63
	ld a7, 72(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 53
	srai t2, t2, 63
	ld a7, 80(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 52
	srai t2, t2, 63
	ld a7, 88(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 51
	srai t2, t2, 63
	ld a7, 96(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 50
	srai t2, t2, 63
	ld a7, 104(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 49
	srai t2, t2, 63
	ld a7, 112(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 48
	srai t2, t2, 63
	ld a7, 120(a2)
	and a7, a7, t2
	or t1, t1, a7
	andi t2, t0, 6
	slli t2, t2, 3
	srl t1, t1, t2
	slli t1, t1, 48
	srli t1, t1, 48
	add a5, a5, t1
	slli a5, a5, 48
	srli a5, a5, 48
	slli t0, a5, 58
	srli t0, t0, 57
	srli t3, t0, 3
	addi t2, zero, 1
	sll t3, t2, t3
	slli t2, t3, 63
	srai t2, t2, 63
	ld t1, 0(a2)
	and t1, t1, t2
	slli t2, t3, 62
	srai t2, t2, 63
	ld a7, 8(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 61
	srai t2, t2, 63
	ld a7, 16(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 60
	srai t2, t2, 63
	ld a7, 24(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 59
	srai t2, t2, 63
	ld a7, 32(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 58
	srai t2, t2, 63
	ld a7, 40(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 57
	srai t2, t2, 63
	ld a7, 48(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 56
	srai t2, t2, 63
	ld a7, 56(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 55
	srai t2, t2, 63
	ld a7, 64(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 54
	srai t2, t2, 63
	ld a7, 72(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 53
	srai t2, t2, 63
	ld a7, 80(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 52
	srai t2, t2, 63
	ld a7, 88(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 51
	srai t2, t2, 63
	ld a7, 96(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 50
	srai t2, t2, 63
	ld a7, 104(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 49
	srai t2, t2, 63
	ld a7, 112(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 48
	srai t2, t2, 63
	ld a7, 120(a2)
	and a7, a7, t2
	or t1, t1, a7
	andi t2, t0, 6
	slli t2, t2, 3
	srl t1, t1, t2
	slli t1, t1, 48
	srli t1, t1, 48
	add a6, a6, t1
	slli a6, a6, 48
	srli a6, a6, 48
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 40(a2)
	add a3, a3, t2
	add a3, a3, t0
	add a3, a3, t1
	slli a7, a3, 49
	srli a7, a7, 48
	slli a3, a3, 48
	srli a3, a3, 63
	or a3, a3, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 42(a2)
	add a4, a4, t2
	add a4, a4, t0
	add a4, a4, t1
	slli a7, a4, 50
	srli a7, a7, 48
	slli a4, a4, 48
	srli a4, a4, 62
	or a4, a4, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 44(a2)
	add a5, a5, t2
	add a5, a5, t0
	add a5, a5, t1
	slli a7, a5, 51
	srli a7, a7, 48
	slli a5, a5, 48
	srli a5, a5, 61
	or a5, a5, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 46(a2)
	add a6, a6, t2
	add a6, a6, t0
	add a6, a6, t1
	slli a7, a6, 53
	srli a7, a7, 48
	slli a6, a6, 48
	srli a6, a6, 59
	or a6, a6, a7
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 48(a2)
	add a3, a3, t2
	add a3, a3, t0
	add a3, a3, t1
	slli a7, a3, 49
	srli a7, a7, 48
	slli a3, a3, 48
	srli a3, a3, 63
	or a3, a3, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 50(a2)
	add a4, a4, t2
	add a4, a4, t0
	add a4, a4, t1
	slli a7, a4, 50
	srli a7, a7, 48
	slli a4, a4, 48
	srli a4, a4, 62
	or a4, a4, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 52(a2)
	add a5, a5, t2
	add a5, a5, t0
	add a5, a5, t1
	slli a7, a5, 51
	srli a7, a7, 48
	slli a5, a5, 48
	srli a5, a5, 61
	or a5, a5, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 54(a2)
	add a6, a6, t2
	add a6, a6, t0
	add a6, a6, t1
	slli a7, a6, 53
	srli a7, a7, 48
	slli a6, a6, 48
	srli a6, a6, 59
	or a6, a6, a7
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 56(a2)
	add a3, a3, t2
	add a3, a3, t0
	add a3, a3, t1
	slli a7, a3, 49
	srli a7, a7, 48
	slli a3, a3, 48
	srli a3, a3, 63
	or a3, a3, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 58(a2)
	add a4, a4, t2
	add a4, a4, t0
	add a4, a4, t1
	slli a7, a4, 50
	srli a7, a7, 48
	slli a4, a4, 48
	srli a4, a4, 62
	or a4, a4, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 60(a2)
	add a5, a5, t2
	add a5, a5, t0
	add a5, a5, t1
	slli a7, a5, 51
	srli a7, a7, 48
	slli a5, a5, 48
	srli a5, a5, 61
	or a5, a5, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 62(a2)
	add a6, a6, t2
	add a6, a6, t0
	add a6, a6, t1
	slli a7, a6, 53
	srli a7, a7, 48
	slli a6, a6, 48
	srli a6, a6, 59
	or a6, a6, a7
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 64(a2)
	add a3, a3, t2
	add a3, a3, t0
	add a3, a3, t1
	slli a7, a3, 49
	srli a7, a7, 48
	slli a3, a3, 48
	srli a3, a3, 63
	or a3, a3, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 66(a2)
	add a4, a4, t2
	add a4, a4, t0
	add a4, a4, t1
	slli a7, a4, 50
	srli a7, a7, 48
	slli a4, a4, 48
	srli a4, a4, 62
	or a4, a4, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 68(a2)
	add a5, a5, t2
	add a5, a5, t0
	add a5, a5, t1
	slli a7, a5, 51
	srli a7, a7, 48
	slli a5, a5, 48
	srli a5, a5, 61
	or a5, a5, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 70(a2)
	add a6, a6, t2
	add a6, a6, t0
	add a6, a6, t1
	slli a7, a6, 53
	srli a7, a7, 48
	slli a6, a6, 48
	srli a6, a6, 59
	or a6, a6, a7
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 72(a2)
	add a3, a3, t2
	add a3, a3, t0
	add a3, a3, t1
	slli a7, a3, 49
	srli a7, a7, 48
	slli a3, a3, 48
	srli a3, a3, 63
	or a3, a3, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 74(a2)
	add a4, a4, t2
	add a4, a4, t0
	add a4, a4, t1
	slli a7, a4, 50
	srli a7, a7, 48
	slli a4, a4, 48
	srli a4, a4, 62
	or a4, a4, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 76(a2)
	add a5, a5, t2
	add a5, a5, t0
	add a5, a5, t1
	slli a7, a5, 51
	srli a7, a7, 48
	slli a5, a5, 48
	srli a5, a5, 61
	or a5, a5, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 78(a2)
	add a6, a6, t2
	add a6, a6, t0
	add a6, a6, t1
	slli a7, a6, 53
	srli a7, a7, 48
	slli a6, a6, 48
	srli a6, a6, 59
	or a6, a6, a7
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 80(a2)
	add a3, a3, t2
	add a3, a3, t0
	add a3, a3, t1
	slli a7, a3, 49
	srli a7, a7, 48
	slli a3, a3, 48
	srli a3, a3, 63
	or a3, a3, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 82(a2)
	add a4, a4, t2
	add a4, a4, t0
	add a4, a4, t1
	slli a7, a4, 50
	srli a7, a7, 48
	slli a4, a4, 48
	srli a4, a4, 62
	or a4, a4, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 84(a2)
	add a5, a5, t2
	add a5, a5, t0
	add a5, a5, t1
	slli a7, a5, 51
	srli a7, a7, 48
	slli a5, a5, 48
	srli a5, a5, 61
	or a5, a5, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 86(a2)
	add a6, a6, t2
	add a6, a6, t0
	add a6, a6, t1
	slli a7, a6, 53
	srli a7, a7, 48
	slli a6, a6, 48
	srli a6, a6, 59
	or a6, a6, a7
	slli t0, a6, 58
	srli t0, t0, 57
	srli t3, t0, 3
	addi t2, zero, 1
	sll t3, t2, t3
	slli t2, t3, 63
	srai t2, t2, 63
	ld t1, 0(a2)
	and t1, t1, t2
	slli t2, t3, 62
	srai t2, t2, 63
	ld a7, 8(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 61
	srai t2, t2, 63
	ld a7, 16(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 60
	srai t2, t2, 63
	ld a7, 24(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 59
	srai t2, t2, 63
	ld a7, 32(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 58
	srai t2, t2, 63
	ld a7, 40(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 57
	srai t2, t2, 63
	ld a7, 48(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 56
	srai t2, t2, 63
	ld a7, 56(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 55
	srai t2, t2, 63
	ld a7, 64(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 54
	srai t2, t2, 63
	ld a7, 72(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 53
	srai t2, t2, 63
	ld a7, 80(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 52
	srai t2, t2, 63
	ld a7, 88(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 51
	srai t2, t2, 63
	ld a7, 96(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 50
	srai t2, t2, 63
	ld a7, 104(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 49
	srai t2, t2, 63
	ld a7, 112(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 48
	srai t2, t2, 63
	ld a7, 120(a2)
	and a7, a7, t2
	or t1, t1, a7
	andi t2, t0, 6
	slli t2, t2, 3
	srl t1, t1, t2
	slli t1, t1, 48
	srli t1, t1, 48
	add a3, a3, t1
	slli a3, a3, 48
	srli a3, a3, 48
	slli t0, a3, 58
	srli t0, t0, 57
	srli t3, t0, 3
	addi t2, zero, 1
	sll t3, t2, t3
	slli t2, t3, 63
	srai t2, t2, 63
	ld t1, 0(a2)
	and t1, t1, t2
	slli t2, t3, 62
	srai t2, t2, 63
	ld a7, 8(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 61
	srai t2, t2, 63
	ld a7, 16(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 60
	srai t2, t2, 63
	ld a7, 24(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 59
	srai t2, t2, 63
	ld a7, 32(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 58
	srai t2, t2, 63
	ld a7, 40(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 57
	srai t2, t2, 63
	ld a7, 48(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 56
	srai t2, t2, 63
	ld a7, 56(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 55
	srai t2, t2, 63
	ld a7, 64(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 54
	srai t2, t2, 63
	ld a7, 72(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 53
	srai t2, t2, 63
	ld a7, 80(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 52
	srai t2, t2, 63
	ld a7, 88(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 51
	srai t2, t2, 63
	ld a7, 96(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 50
	srai t2, t2, 63
	ld a7, 104(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 49
	srai t2, t2, 63
	ld a7, 112(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 48
	srai t2, t2, 63
	ld a7, 120(a2)
	and a7, a7, t2
	or t1, t1, a7
	andi t2, t0, 6
	slli t2, t2, 3
	srl t1, t1, t2
	slli t1, t1, 48
	srli t1, t1, 48
	add a4, a4, t1
	slli a4, a4, 48
	srli a4, a4, 48
	slli t0, a4, 58
	srli t0, t0, 57
	srli t3, t0, 3
	addi t2, zero, 1
	sll t3, t2, t3
	slli t2, t3, 63
	srai t2, t2, 63
	ld t1, 0(a2)
	and t1, t1, t2
	slli t2, t3, 62
	srai t2, t2, 63
	ld a7, 8(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 61
	srai t2, t2, 63
	ld a7, 16(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 60
	srai t2, t2, 63
	ld a7, 24(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 59
	srai t2, t2, 63
	ld a7, 32(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 58
	srai t2, t2, 63
	ld a7, 40(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 57
	srai t2, t2, 63
	ld a7, 48(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 56
	srai t2, t2, 63
	ld a7, 56(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 55
	srai t2, t2, 63
	ld a7, 64(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 54
	srai t2, t2, 63
	ld a7, 72(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 53
	srai t2, t2, 63
	ld a7, 80(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 52
	srai t2, t2, 63
	ld a7, 88(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 51
	srai t2, t2, 63
	ld a7, 96(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 50
	srai t2, t2, 63
	ld a7, 104(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 49
	srai t2, t2, 63
	ld a7, 112(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 48
	srai t2, t2, 63
	ld a7, 120(a2)
	and a7, a7, t2
	or t1, t1, a7
	andi t2, t0, 6
	slli t2, t2, 3
	srl t1, t1, t2
	slli t1, t1, 48
	srli t1, t1, 48
	add a5, a5, t1
	slli a5, a5, 48
	srli a5, a5, 48
	slli t0, a5, 58
	srli t0, t0, 57
	srli t3, t0, 3
	addi t2, zero, 1
	sll t3, t2, t3
	slli t2, t3, 63
	srai t2, t2, 63
	ld t1, 0(a2)
	and t1, t1, t2
	slli t2, t3, 62
	srai t2, t2, 63
	ld a7, 8(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 61
	srai t2, t2, 63
	ld a7, 16(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 60
	srai t2, t2, 63
	ld a7, 24(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 59
	srai t2, t2, 63
	ld a7, 32(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 58
	srai t2, t2, 63
	ld a7, 40(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 57
	srai t2, t2, 63
	ld a7, 48(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 56
	srai t2, t2, 63
	ld a7, 56(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 55
	srai t2, t2, 63
	ld a7, 64(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 54
	srai t2, t2, 63
	ld a7, 72(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 53
	srai t2, t2, 63
	ld a7, 80(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 52
	srai t2, t2, 63
	ld a7, 88(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 51
	srai t2, t2, 63
	ld a7, 96(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 50
	srai t2, t2, 63
	ld a7, 104(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 49
	srai t2, t2, 63
	ld a7, 112(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 48
	srai t2, t2, 63
	ld a7, 120(a2)
	and a7, a7, t2
	or t1, t1, a7
	andi t2, t0, 6
	slli t2, t2, 3
	srl t1, t1, t2
	slli t1, t1, 48
	srli t1, t1, 48
	add a6, a6, t1
	slli a6, a6, 48
	srli a6, a6, 48
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 88(a2)
	add a3, a3, t2
	add a3, a3, t0
	add a3, a3, t1
	slli a7, a3, 49
	srli a7, a7, 48
	slli a3, a3, 48
	srli a3, a3, 63
	or a3, a3, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 90(a2)
	add a4, a4, t2
	add a4, a4, t0
	add a4, a4, t1
	slli a7, a4, 50
	srli a7, a7, 48
	slli a4, a4, 48
	srli a4, a4, 62
	or a4, a4, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 92(a2)
	add a5, a5, t2
	add a5, a5, t0
	add a5, a5, t1
	slli a7, a5, 51
	srli a7, a7, 48
	slli a5, a5, 48
	srli a5, a5, 61
	or a5, a5, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 94(a2)
	add a6, a6, t2
	add a6, a6, t0
	add a6, a6, t1
	slli a7, a6, 53
	srli a7, a7, 48
	slli a6, a6, 48
	srli a6, a6, 59
	or a6, a6, a7
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 96(a2)
	add a3, a3, t2
	add a3, a3, t0
	add a3, a3, t1
	slli a7, a3, 49
	srli a7, a7, 48
	slli a3, a3, 48
	srli a3, a3, 63
	or a3, a3, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 98(a2)
	add a4, a4, t2
	add a4, a4, t0
	add a4, a4, t1
	slli a7, a4, 50
	srli a7, a7, 48
	slli a4, a4, 48
	srli a4, a4, 62
	or a4, a4, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 100(a2)
	add a5, a5, t2
	add a5, a5, t0
	add a5, a5, t1
	slli a7, a5, 51
	srli a7, a7, 48
	slli a5, a5, 48
	srli a5, a5, 61
	or a5, a5, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 102(a2)
	add a6, a6, t2
	add a6, a6, t0
	add a6, a6, t1
	slli a7, a6, 53
	srli a7, a7, 48
	slli a6, a6, 48
	srli a6, a6, 59
	or a6, a6, a7
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 104(a2)
	add a3, a3, t2
	add a3, a3, t0
	add a3, a3, t1
	slli a7, a3, 49
	srli a7, a7, 48
	slli a3, a3, 48
	srli a3, a3, 63
	or a3, a3, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 106(a2)
	add a4, a4, t2
	add a4, a4, t0
	add a4, a4, t1
	slli a7, a4, 50
	srli a7, a7, 48
	slli a4, a4, 48
	srli a4, a4, 62
	or a4, a4, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 108(a2)
	add a5, a5, t2
	add a5, a5, t0
	add a5, a5, t1
	slli a7, a5, 51
	srli a7, a7, 48
	slli a5, a5, 48
	srli a5, a5, 61
	or a5, a5, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 110(a2)
	add a6, a6, t2
	add a6, a6, t0
	add a6, a6, t1
	slli a7, a6, 53
	srli a7, a7, 48
	slli a6, a6, 48
	srli a6, a6, 59
	or a6, a6, a7
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 112(a2)
	add a3, a3, t2
	add a3, a3, t0
	add a3, a3, t1
	slli a7, a3, 49
	srli a7, a7, 48
	slli a3, a3, 48
	srli a3, a3, 63
	or a3, a3, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 114(a2)
	add a4, a4, t2
	add a4, a4, t0
	add a4, a4, t1
	slli a7, a4, 50
	srli a7, a7, 48
	slli a4, a4, 48
	srli a4, a4, 62
	or a4, a4, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 116(a2)
	add a5, a5, t2
	add a5, a5, t0
	add a5, a5, t1
	slli a7, a5, 51
	srli a7, a7, 48
	slli a5, a5, 48
	srli a5, a5, 61
	or a5, a5, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 118(a2)
	add a6, a6, t2
	add a6, a6, t0
	add a6, a6, t1
	slli a7, a6, 53
	srli a7, a7, 48
	slli a6, a6, 48
	srli a6, a6, 59
	or a6, a6, a7
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 120(a2)
	add a3, a3, t2
	add a3, a3, t0
	add a3, a3, t1
	slli a7, a3, 49
	srli a7, a7, 48
	slli a3, a3, 48
	srli a3, a3, 63
	or a3, a3, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 122(a2)
	add a4, a4, t2
	add a4, a4, t0
	add a4, a4, t1
	slli a7, a4, 50
	srli a7, a7, 48
	slli a4, a4, 48
	srli a4, a4, 62
	or a4, a4, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 124(a2)
	add a5, a5, t2
	add a5, a5, t0
	add a5, a5, t1
	slli a7, a5, 51
	srli a7, a7, 48
	slli a5, a5, 48
	srli a5, a5, 61
	or a5, a5, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 126(a2)
	add a6, a6, t2
	add a6, a6, t0
	add a6, a6, t1
	slli a7, a6, 53
	srli a7, a7, 48
	slli a6, a6, 48
	srli a6, a6, 59
	or a6, a6, a7
	slli t1, a4, 16
	or t1, t1, a3
	slli t2, a5, 32
	or t1, t1, t2
	slli t2, a6, 48
	or t1, t1, t2
	sb t1, 0(a1)
	srli a7, t1, 8
	sb a7, 1(a1)
	srli a7, t1, 16
	sb a7, 2(a1)
	srli a7, t1, 24
	sb a7, 3(a1)
	srli t2, t1, 32
	sb t2, 4(a1)
	srli a7, t2, 8
	sb a7, 5(a1)
	srli a7, t2, 16
	sb a7, 6(a1)
	srli a7, t2, 24
	sb a7, 7(a1)
	ret
	.option pop

vg_rc2_decrypt_block:
	.option push
	.option arch, +m, +c
	andi t0, a0, 7
	beqz t0, 20f
	addi t3, a0, 0
	addi t4, a2, 0
	addi t5, zero, 128
22:
	lbu a7, 0(t3)
	sb a7, 0(t4)
	addi t3, t3, 1
	addi t4, t4, 1
	addi t5, t5, -1
	bnez t5, 22b
	j 21f
20:
	addi a2, a0, 0
21:
	lbu t1, 0(a1)
	lbu a7, 1(a1)
	slli a7, a7, 8
	or t1, t1, a7
	lbu a7, 2(a1)
	slli a7, a7, 16
	or t1, t1, a7
	lbu a7, 3(a1)
	slli a7, a7, 24
	or t1, t1, a7
	lbu t2, 4(a1)
	lbu a7, 5(a1)
	slli a7, a7, 8
	or t2, t2, a7
	lbu a7, 6(a1)
	slli a7, a7, 16
	or t2, t2, a7
	lbu a7, 7(a1)
	slli a7, a7, 24
	or t2, t2, a7
	slli t2, t2, 32
	or t1, t1, t2
	slli a3, t1, 48
	srli a3, a3, 48
	slli a4, t1, 32
	srli a4, a4, 48
	slli a5, t1, 16
	srli a5, a5, 48
	srli a6, t1, 48
	slli a7, a6, 59
	srli a7, a7, 48
	srli a6, a6, 5
	or a6, a6, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 126(a2)
	sub a6, a6, t2
	sub a6, a6, t0
	sub a6, a6, t1
	slli a6, a6, 48
	srli a6, a6, 48
	slli a7, a5, 61
	srli a7, a7, 48
	srli a5, a5, 3
	or a5, a5, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 124(a2)
	sub a5, a5, t2
	sub a5, a5, t0
	sub a5, a5, t1
	slli a5, a5, 48
	srli a5, a5, 48
	slli a7, a4, 62
	srli a7, a7, 48
	srli a4, a4, 2
	or a4, a4, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 122(a2)
	sub a4, a4, t2
	sub a4, a4, t0
	sub a4, a4, t1
	slli a4, a4, 48
	srli a4, a4, 48
	slli a7, a3, 63
	srli a7, a7, 48
	srli a3, a3, 1
	or a3, a3, a7
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 120(a2)
	sub a3, a3, t2
	sub a3, a3, t0
	sub a3, a3, t1
	slli a3, a3, 48
	srli a3, a3, 48
	slli a7, a6, 59
	srli a7, a7, 48
	srli a6, a6, 5
	or a6, a6, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 118(a2)
	sub a6, a6, t2
	sub a6, a6, t0
	sub a6, a6, t1
	slli a6, a6, 48
	srli a6, a6, 48
	slli a7, a5, 61
	srli a7, a7, 48
	srli a5, a5, 3
	or a5, a5, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 116(a2)
	sub a5, a5, t2
	sub a5, a5, t0
	sub a5, a5, t1
	slli a5, a5, 48
	srli a5, a5, 48
	slli a7, a4, 62
	srli a7, a7, 48
	srli a4, a4, 2
	or a4, a4, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 114(a2)
	sub a4, a4, t2
	sub a4, a4, t0
	sub a4, a4, t1
	slli a4, a4, 48
	srli a4, a4, 48
	slli a7, a3, 63
	srli a7, a7, 48
	srli a3, a3, 1
	or a3, a3, a7
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 112(a2)
	sub a3, a3, t2
	sub a3, a3, t0
	sub a3, a3, t1
	slli a3, a3, 48
	srli a3, a3, 48
	slli a7, a6, 59
	srli a7, a7, 48
	srli a6, a6, 5
	or a6, a6, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 110(a2)
	sub a6, a6, t2
	sub a6, a6, t0
	sub a6, a6, t1
	slli a6, a6, 48
	srli a6, a6, 48
	slli a7, a5, 61
	srli a7, a7, 48
	srli a5, a5, 3
	or a5, a5, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 108(a2)
	sub a5, a5, t2
	sub a5, a5, t0
	sub a5, a5, t1
	slli a5, a5, 48
	srli a5, a5, 48
	slli a7, a4, 62
	srli a7, a7, 48
	srli a4, a4, 2
	or a4, a4, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 106(a2)
	sub a4, a4, t2
	sub a4, a4, t0
	sub a4, a4, t1
	slli a4, a4, 48
	srli a4, a4, 48
	slli a7, a3, 63
	srli a7, a7, 48
	srli a3, a3, 1
	or a3, a3, a7
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 104(a2)
	sub a3, a3, t2
	sub a3, a3, t0
	sub a3, a3, t1
	slli a3, a3, 48
	srli a3, a3, 48
	slli a7, a6, 59
	srli a7, a7, 48
	srli a6, a6, 5
	or a6, a6, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 102(a2)
	sub a6, a6, t2
	sub a6, a6, t0
	sub a6, a6, t1
	slli a6, a6, 48
	srli a6, a6, 48
	slli a7, a5, 61
	srli a7, a7, 48
	srli a5, a5, 3
	or a5, a5, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 100(a2)
	sub a5, a5, t2
	sub a5, a5, t0
	sub a5, a5, t1
	slli a5, a5, 48
	srli a5, a5, 48
	slli a7, a4, 62
	srli a7, a7, 48
	srli a4, a4, 2
	or a4, a4, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 98(a2)
	sub a4, a4, t2
	sub a4, a4, t0
	sub a4, a4, t1
	slli a4, a4, 48
	srli a4, a4, 48
	slli a7, a3, 63
	srli a7, a7, 48
	srli a3, a3, 1
	or a3, a3, a7
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 96(a2)
	sub a3, a3, t2
	sub a3, a3, t0
	sub a3, a3, t1
	slli a3, a3, 48
	srli a3, a3, 48
	slli a7, a6, 59
	srli a7, a7, 48
	srli a6, a6, 5
	or a6, a6, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 94(a2)
	sub a6, a6, t2
	sub a6, a6, t0
	sub a6, a6, t1
	slli a6, a6, 48
	srli a6, a6, 48
	slli a7, a5, 61
	srli a7, a7, 48
	srli a5, a5, 3
	or a5, a5, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 92(a2)
	sub a5, a5, t2
	sub a5, a5, t0
	sub a5, a5, t1
	slli a5, a5, 48
	srli a5, a5, 48
	slli a7, a4, 62
	srli a7, a7, 48
	srli a4, a4, 2
	or a4, a4, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 90(a2)
	sub a4, a4, t2
	sub a4, a4, t0
	sub a4, a4, t1
	slli a4, a4, 48
	srli a4, a4, 48
	slli a7, a3, 63
	srli a7, a7, 48
	srli a3, a3, 1
	or a3, a3, a7
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 88(a2)
	sub a3, a3, t2
	sub a3, a3, t0
	sub a3, a3, t1
	slli a3, a3, 48
	srli a3, a3, 48
	slli t0, a5, 58
	srli t0, t0, 57
	srli t3, t0, 3
	addi t2, zero, 1
	sll t3, t2, t3
	slli t2, t3, 63
	srai t2, t2, 63
	ld t1, 0(a2)
	and t1, t1, t2
	slli t2, t3, 62
	srai t2, t2, 63
	ld a7, 8(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 61
	srai t2, t2, 63
	ld a7, 16(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 60
	srai t2, t2, 63
	ld a7, 24(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 59
	srai t2, t2, 63
	ld a7, 32(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 58
	srai t2, t2, 63
	ld a7, 40(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 57
	srai t2, t2, 63
	ld a7, 48(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 56
	srai t2, t2, 63
	ld a7, 56(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 55
	srai t2, t2, 63
	ld a7, 64(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 54
	srai t2, t2, 63
	ld a7, 72(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 53
	srai t2, t2, 63
	ld a7, 80(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 52
	srai t2, t2, 63
	ld a7, 88(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 51
	srai t2, t2, 63
	ld a7, 96(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 50
	srai t2, t2, 63
	ld a7, 104(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 49
	srai t2, t2, 63
	ld a7, 112(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 48
	srai t2, t2, 63
	ld a7, 120(a2)
	and a7, a7, t2
	or t1, t1, a7
	andi t2, t0, 6
	slli t2, t2, 3
	srl t1, t1, t2
	slli t1, t1, 48
	srli t1, t1, 48
	sub a6, a6, t1
	slli a6, a6, 48
	srli a6, a6, 48
	slli t0, a4, 58
	srli t0, t0, 57
	srli t3, t0, 3
	addi t2, zero, 1
	sll t3, t2, t3
	slli t2, t3, 63
	srai t2, t2, 63
	ld t1, 0(a2)
	and t1, t1, t2
	slli t2, t3, 62
	srai t2, t2, 63
	ld a7, 8(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 61
	srai t2, t2, 63
	ld a7, 16(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 60
	srai t2, t2, 63
	ld a7, 24(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 59
	srai t2, t2, 63
	ld a7, 32(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 58
	srai t2, t2, 63
	ld a7, 40(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 57
	srai t2, t2, 63
	ld a7, 48(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 56
	srai t2, t2, 63
	ld a7, 56(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 55
	srai t2, t2, 63
	ld a7, 64(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 54
	srai t2, t2, 63
	ld a7, 72(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 53
	srai t2, t2, 63
	ld a7, 80(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 52
	srai t2, t2, 63
	ld a7, 88(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 51
	srai t2, t2, 63
	ld a7, 96(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 50
	srai t2, t2, 63
	ld a7, 104(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 49
	srai t2, t2, 63
	ld a7, 112(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 48
	srai t2, t2, 63
	ld a7, 120(a2)
	and a7, a7, t2
	or t1, t1, a7
	andi t2, t0, 6
	slli t2, t2, 3
	srl t1, t1, t2
	slli t1, t1, 48
	srli t1, t1, 48
	sub a5, a5, t1
	slli a5, a5, 48
	srli a5, a5, 48
	slli t0, a3, 58
	srli t0, t0, 57
	srli t3, t0, 3
	addi t2, zero, 1
	sll t3, t2, t3
	slli t2, t3, 63
	srai t2, t2, 63
	ld t1, 0(a2)
	and t1, t1, t2
	slli t2, t3, 62
	srai t2, t2, 63
	ld a7, 8(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 61
	srai t2, t2, 63
	ld a7, 16(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 60
	srai t2, t2, 63
	ld a7, 24(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 59
	srai t2, t2, 63
	ld a7, 32(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 58
	srai t2, t2, 63
	ld a7, 40(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 57
	srai t2, t2, 63
	ld a7, 48(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 56
	srai t2, t2, 63
	ld a7, 56(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 55
	srai t2, t2, 63
	ld a7, 64(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 54
	srai t2, t2, 63
	ld a7, 72(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 53
	srai t2, t2, 63
	ld a7, 80(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 52
	srai t2, t2, 63
	ld a7, 88(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 51
	srai t2, t2, 63
	ld a7, 96(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 50
	srai t2, t2, 63
	ld a7, 104(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 49
	srai t2, t2, 63
	ld a7, 112(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 48
	srai t2, t2, 63
	ld a7, 120(a2)
	and a7, a7, t2
	or t1, t1, a7
	andi t2, t0, 6
	slli t2, t2, 3
	srl t1, t1, t2
	slli t1, t1, 48
	srli t1, t1, 48
	sub a4, a4, t1
	slli a4, a4, 48
	srli a4, a4, 48
	slli t0, a6, 58
	srli t0, t0, 57
	srli t3, t0, 3
	addi t2, zero, 1
	sll t3, t2, t3
	slli t2, t3, 63
	srai t2, t2, 63
	ld t1, 0(a2)
	and t1, t1, t2
	slli t2, t3, 62
	srai t2, t2, 63
	ld a7, 8(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 61
	srai t2, t2, 63
	ld a7, 16(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 60
	srai t2, t2, 63
	ld a7, 24(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 59
	srai t2, t2, 63
	ld a7, 32(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 58
	srai t2, t2, 63
	ld a7, 40(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 57
	srai t2, t2, 63
	ld a7, 48(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 56
	srai t2, t2, 63
	ld a7, 56(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 55
	srai t2, t2, 63
	ld a7, 64(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 54
	srai t2, t2, 63
	ld a7, 72(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 53
	srai t2, t2, 63
	ld a7, 80(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 52
	srai t2, t2, 63
	ld a7, 88(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 51
	srai t2, t2, 63
	ld a7, 96(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 50
	srai t2, t2, 63
	ld a7, 104(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 49
	srai t2, t2, 63
	ld a7, 112(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 48
	srai t2, t2, 63
	ld a7, 120(a2)
	and a7, a7, t2
	or t1, t1, a7
	andi t2, t0, 6
	slli t2, t2, 3
	srl t1, t1, t2
	slli t1, t1, 48
	srli t1, t1, 48
	sub a3, a3, t1
	slli a3, a3, 48
	srli a3, a3, 48
	slli a7, a6, 59
	srli a7, a7, 48
	srli a6, a6, 5
	or a6, a6, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 86(a2)
	sub a6, a6, t2
	sub a6, a6, t0
	sub a6, a6, t1
	slli a6, a6, 48
	srli a6, a6, 48
	slli a7, a5, 61
	srli a7, a7, 48
	srli a5, a5, 3
	or a5, a5, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 84(a2)
	sub a5, a5, t2
	sub a5, a5, t0
	sub a5, a5, t1
	slli a5, a5, 48
	srli a5, a5, 48
	slli a7, a4, 62
	srli a7, a7, 48
	srli a4, a4, 2
	or a4, a4, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 82(a2)
	sub a4, a4, t2
	sub a4, a4, t0
	sub a4, a4, t1
	slli a4, a4, 48
	srli a4, a4, 48
	slli a7, a3, 63
	srli a7, a7, 48
	srli a3, a3, 1
	or a3, a3, a7
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 80(a2)
	sub a3, a3, t2
	sub a3, a3, t0
	sub a3, a3, t1
	slli a3, a3, 48
	srli a3, a3, 48
	slli a7, a6, 59
	srli a7, a7, 48
	srli a6, a6, 5
	or a6, a6, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 78(a2)
	sub a6, a6, t2
	sub a6, a6, t0
	sub a6, a6, t1
	slli a6, a6, 48
	srli a6, a6, 48
	slli a7, a5, 61
	srli a7, a7, 48
	srli a5, a5, 3
	or a5, a5, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 76(a2)
	sub a5, a5, t2
	sub a5, a5, t0
	sub a5, a5, t1
	slli a5, a5, 48
	srli a5, a5, 48
	slli a7, a4, 62
	srli a7, a7, 48
	srli a4, a4, 2
	or a4, a4, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 74(a2)
	sub a4, a4, t2
	sub a4, a4, t0
	sub a4, a4, t1
	slli a4, a4, 48
	srli a4, a4, 48
	slli a7, a3, 63
	srli a7, a7, 48
	srli a3, a3, 1
	or a3, a3, a7
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 72(a2)
	sub a3, a3, t2
	sub a3, a3, t0
	sub a3, a3, t1
	slli a3, a3, 48
	srli a3, a3, 48
	slli a7, a6, 59
	srli a7, a7, 48
	srli a6, a6, 5
	or a6, a6, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 70(a2)
	sub a6, a6, t2
	sub a6, a6, t0
	sub a6, a6, t1
	slli a6, a6, 48
	srli a6, a6, 48
	slli a7, a5, 61
	srli a7, a7, 48
	srli a5, a5, 3
	or a5, a5, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 68(a2)
	sub a5, a5, t2
	sub a5, a5, t0
	sub a5, a5, t1
	slli a5, a5, 48
	srli a5, a5, 48
	slli a7, a4, 62
	srli a7, a7, 48
	srli a4, a4, 2
	or a4, a4, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 66(a2)
	sub a4, a4, t2
	sub a4, a4, t0
	sub a4, a4, t1
	slli a4, a4, 48
	srli a4, a4, 48
	slli a7, a3, 63
	srli a7, a7, 48
	srli a3, a3, 1
	or a3, a3, a7
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 64(a2)
	sub a3, a3, t2
	sub a3, a3, t0
	sub a3, a3, t1
	slli a3, a3, 48
	srli a3, a3, 48
	slli a7, a6, 59
	srli a7, a7, 48
	srli a6, a6, 5
	or a6, a6, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 62(a2)
	sub a6, a6, t2
	sub a6, a6, t0
	sub a6, a6, t1
	slli a6, a6, 48
	srli a6, a6, 48
	slli a7, a5, 61
	srli a7, a7, 48
	srli a5, a5, 3
	or a5, a5, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 60(a2)
	sub a5, a5, t2
	sub a5, a5, t0
	sub a5, a5, t1
	slli a5, a5, 48
	srli a5, a5, 48
	slli a7, a4, 62
	srli a7, a7, 48
	srli a4, a4, 2
	or a4, a4, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 58(a2)
	sub a4, a4, t2
	sub a4, a4, t0
	sub a4, a4, t1
	slli a4, a4, 48
	srli a4, a4, 48
	slli a7, a3, 63
	srli a7, a7, 48
	srli a3, a3, 1
	or a3, a3, a7
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 56(a2)
	sub a3, a3, t2
	sub a3, a3, t0
	sub a3, a3, t1
	slli a3, a3, 48
	srli a3, a3, 48
	slli a7, a6, 59
	srli a7, a7, 48
	srli a6, a6, 5
	or a6, a6, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 54(a2)
	sub a6, a6, t2
	sub a6, a6, t0
	sub a6, a6, t1
	slli a6, a6, 48
	srli a6, a6, 48
	slli a7, a5, 61
	srli a7, a7, 48
	srli a5, a5, 3
	or a5, a5, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 52(a2)
	sub a5, a5, t2
	sub a5, a5, t0
	sub a5, a5, t1
	slli a5, a5, 48
	srli a5, a5, 48
	slli a7, a4, 62
	srli a7, a7, 48
	srli a4, a4, 2
	or a4, a4, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 50(a2)
	sub a4, a4, t2
	sub a4, a4, t0
	sub a4, a4, t1
	slli a4, a4, 48
	srli a4, a4, 48
	slli a7, a3, 63
	srli a7, a7, 48
	srli a3, a3, 1
	or a3, a3, a7
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 48(a2)
	sub a3, a3, t2
	sub a3, a3, t0
	sub a3, a3, t1
	slli a3, a3, 48
	srli a3, a3, 48
	slli a7, a6, 59
	srli a7, a7, 48
	srli a6, a6, 5
	or a6, a6, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 46(a2)
	sub a6, a6, t2
	sub a6, a6, t0
	sub a6, a6, t1
	slli a6, a6, 48
	srli a6, a6, 48
	slli a7, a5, 61
	srli a7, a7, 48
	srli a5, a5, 3
	or a5, a5, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 44(a2)
	sub a5, a5, t2
	sub a5, a5, t0
	sub a5, a5, t1
	slli a5, a5, 48
	srli a5, a5, 48
	slli a7, a4, 62
	srli a7, a7, 48
	srli a4, a4, 2
	or a4, a4, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 42(a2)
	sub a4, a4, t2
	sub a4, a4, t0
	sub a4, a4, t1
	slli a4, a4, 48
	srli a4, a4, 48
	slli a7, a3, 63
	srli a7, a7, 48
	srli a3, a3, 1
	or a3, a3, a7
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 40(a2)
	sub a3, a3, t2
	sub a3, a3, t0
	sub a3, a3, t1
	slli a3, a3, 48
	srli a3, a3, 48
	slli t0, a5, 58
	srli t0, t0, 57
	srli t3, t0, 3
	addi t2, zero, 1
	sll t3, t2, t3
	slli t2, t3, 63
	srai t2, t2, 63
	ld t1, 0(a2)
	and t1, t1, t2
	slli t2, t3, 62
	srai t2, t2, 63
	ld a7, 8(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 61
	srai t2, t2, 63
	ld a7, 16(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 60
	srai t2, t2, 63
	ld a7, 24(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 59
	srai t2, t2, 63
	ld a7, 32(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 58
	srai t2, t2, 63
	ld a7, 40(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 57
	srai t2, t2, 63
	ld a7, 48(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 56
	srai t2, t2, 63
	ld a7, 56(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 55
	srai t2, t2, 63
	ld a7, 64(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 54
	srai t2, t2, 63
	ld a7, 72(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 53
	srai t2, t2, 63
	ld a7, 80(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 52
	srai t2, t2, 63
	ld a7, 88(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 51
	srai t2, t2, 63
	ld a7, 96(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 50
	srai t2, t2, 63
	ld a7, 104(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 49
	srai t2, t2, 63
	ld a7, 112(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 48
	srai t2, t2, 63
	ld a7, 120(a2)
	and a7, a7, t2
	or t1, t1, a7
	andi t2, t0, 6
	slli t2, t2, 3
	srl t1, t1, t2
	slli t1, t1, 48
	srli t1, t1, 48
	sub a6, a6, t1
	slli a6, a6, 48
	srli a6, a6, 48
	slli t0, a4, 58
	srli t0, t0, 57
	srli t3, t0, 3
	addi t2, zero, 1
	sll t3, t2, t3
	slli t2, t3, 63
	srai t2, t2, 63
	ld t1, 0(a2)
	and t1, t1, t2
	slli t2, t3, 62
	srai t2, t2, 63
	ld a7, 8(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 61
	srai t2, t2, 63
	ld a7, 16(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 60
	srai t2, t2, 63
	ld a7, 24(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 59
	srai t2, t2, 63
	ld a7, 32(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 58
	srai t2, t2, 63
	ld a7, 40(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 57
	srai t2, t2, 63
	ld a7, 48(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 56
	srai t2, t2, 63
	ld a7, 56(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 55
	srai t2, t2, 63
	ld a7, 64(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 54
	srai t2, t2, 63
	ld a7, 72(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 53
	srai t2, t2, 63
	ld a7, 80(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 52
	srai t2, t2, 63
	ld a7, 88(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 51
	srai t2, t2, 63
	ld a7, 96(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 50
	srai t2, t2, 63
	ld a7, 104(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 49
	srai t2, t2, 63
	ld a7, 112(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 48
	srai t2, t2, 63
	ld a7, 120(a2)
	and a7, a7, t2
	or t1, t1, a7
	andi t2, t0, 6
	slli t2, t2, 3
	srl t1, t1, t2
	slli t1, t1, 48
	srli t1, t1, 48
	sub a5, a5, t1
	slli a5, a5, 48
	srli a5, a5, 48
	slli t0, a3, 58
	srli t0, t0, 57
	srli t3, t0, 3
	addi t2, zero, 1
	sll t3, t2, t3
	slli t2, t3, 63
	srai t2, t2, 63
	ld t1, 0(a2)
	and t1, t1, t2
	slli t2, t3, 62
	srai t2, t2, 63
	ld a7, 8(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 61
	srai t2, t2, 63
	ld a7, 16(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 60
	srai t2, t2, 63
	ld a7, 24(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 59
	srai t2, t2, 63
	ld a7, 32(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 58
	srai t2, t2, 63
	ld a7, 40(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 57
	srai t2, t2, 63
	ld a7, 48(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 56
	srai t2, t2, 63
	ld a7, 56(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 55
	srai t2, t2, 63
	ld a7, 64(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 54
	srai t2, t2, 63
	ld a7, 72(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 53
	srai t2, t2, 63
	ld a7, 80(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 52
	srai t2, t2, 63
	ld a7, 88(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 51
	srai t2, t2, 63
	ld a7, 96(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 50
	srai t2, t2, 63
	ld a7, 104(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 49
	srai t2, t2, 63
	ld a7, 112(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 48
	srai t2, t2, 63
	ld a7, 120(a2)
	and a7, a7, t2
	or t1, t1, a7
	andi t2, t0, 6
	slli t2, t2, 3
	srl t1, t1, t2
	slli t1, t1, 48
	srli t1, t1, 48
	sub a4, a4, t1
	slli a4, a4, 48
	srli a4, a4, 48
	slli t0, a6, 58
	srli t0, t0, 57
	srli t3, t0, 3
	addi t2, zero, 1
	sll t3, t2, t3
	slli t2, t3, 63
	srai t2, t2, 63
	ld t1, 0(a2)
	and t1, t1, t2
	slli t2, t3, 62
	srai t2, t2, 63
	ld a7, 8(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 61
	srai t2, t2, 63
	ld a7, 16(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 60
	srai t2, t2, 63
	ld a7, 24(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 59
	srai t2, t2, 63
	ld a7, 32(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 58
	srai t2, t2, 63
	ld a7, 40(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 57
	srai t2, t2, 63
	ld a7, 48(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 56
	srai t2, t2, 63
	ld a7, 56(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 55
	srai t2, t2, 63
	ld a7, 64(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 54
	srai t2, t2, 63
	ld a7, 72(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 53
	srai t2, t2, 63
	ld a7, 80(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 52
	srai t2, t2, 63
	ld a7, 88(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 51
	srai t2, t2, 63
	ld a7, 96(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 50
	srai t2, t2, 63
	ld a7, 104(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 49
	srai t2, t2, 63
	ld a7, 112(a2)
	and a7, a7, t2
	or t1, t1, a7
	slli t2, t3, 48
	srai t2, t2, 63
	ld a7, 120(a2)
	and a7, a7, t2
	or t1, t1, a7
	andi t2, t0, 6
	slli t2, t2, 3
	srl t1, t1, t2
	slli t1, t1, 48
	srli t1, t1, 48
	sub a3, a3, t1
	slli a3, a3, 48
	srli a3, a3, 48
	slli a7, a6, 59
	srli a7, a7, 48
	srli a6, a6, 5
	or a6, a6, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 38(a2)
	sub a6, a6, t2
	sub a6, a6, t0
	sub a6, a6, t1
	slli a6, a6, 48
	srli a6, a6, 48
	slli a7, a5, 61
	srli a7, a7, 48
	srli a5, a5, 3
	or a5, a5, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 36(a2)
	sub a5, a5, t2
	sub a5, a5, t0
	sub a5, a5, t1
	slli a5, a5, 48
	srli a5, a5, 48
	slli a7, a4, 62
	srli a7, a7, 48
	srli a4, a4, 2
	or a4, a4, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 34(a2)
	sub a4, a4, t2
	sub a4, a4, t0
	sub a4, a4, t1
	slli a4, a4, 48
	srli a4, a4, 48
	slli a7, a3, 63
	srli a7, a7, 48
	srli a3, a3, 1
	or a3, a3, a7
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 32(a2)
	sub a3, a3, t2
	sub a3, a3, t0
	sub a3, a3, t1
	slli a3, a3, 48
	srli a3, a3, 48
	slli a7, a6, 59
	srli a7, a7, 48
	srli a6, a6, 5
	or a6, a6, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 30(a2)
	sub a6, a6, t2
	sub a6, a6, t0
	sub a6, a6, t1
	slli a6, a6, 48
	srli a6, a6, 48
	slli a7, a5, 61
	srli a7, a7, 48
	srli a5, a5, 3
	or a5, a5, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 28(a2)
	sub a5, a5, t2
	sub a5, a5, t0
	sub a5, a5, t1
	slli a5, a5, 48
	srli a5, a5, 48
	slli a7, a4, 62
	srli a7, a7, 48
	srli a4, a4, 2
	or a4, a4, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 26(a2)
	sub a4, a4, t2
	sub a4, a4, t0
	sub a4, a4, t1
	slli a4, a4, 48
	srli a4, a4, 48
	slli a7, a3, 63
	srli a7, a7, 48
	srli a3, a3, 1
	or a3, a3, a7
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 24(a2)
	sub a3, a3, t2
	sub a3, a3, t0
	sub a3, a3, t1
	slli a3, a3, 48
	srli a3, a3, 48
	slli a7, a6, 59
	srli a7, a7, 48
	srli a6, a6, 5
	or a6, a6, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 22(a2)
	sub a6, a6, t2
	sub a6, a6, t0
	sub a6, a6, t1
	slli a6, a6, 48
	srli a6, a6, 48
	slli a7, a5, 61
	srli a7, a7, 48
	srli a5, a5, 3
	or a5, a5, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 20(a2)
	sub a5, a5, t2
	sub a5, a5, t0
	sub a5, a5, t1
	slli a5, a5, 48
	srli a5, a5, 48
	slli a7, a4, 62
	srli a7, a7, 48
	srli a4, a4, 2
	or a4, a4, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 18(a2)
	sub a4, a4, t2
	sub a4, a4, t0
	sub a4, a4, t1
	slli a4, a4, 48
	srli a4, a4, 48
	slli a7, a3, 63
	srli a7, a7, 48
	srli a3, a3, 1
	or a3, a3, a7
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 16(a2)
	sub a3, a3, t2
	sub a3, a3, t0
	sub a3, a3, t1
	slli a3, a3, 48
	srli a3, a3, 48
	slli a7, a6, 59
	srli a7, a7, 48
	srli a6, a6, 5
	or a6, a6, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 14(a2)
	sub a6, a6, t2
	sub a6, a6, t0
	sub a6, a6, t1
	slli a6, a6, 48
	srli a6, a6, 48
	slli a7, a5, 61
	srli a7, a7, 48
	srli a5, a5, 3
	or a5, a5, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 12(a2)
	sub a5, a5, t2
	sub a5, a5, t0
	sub a5, a5, t1
	slli a5, a5, 48
	srli a5, a5, 48
	slli a7, a4, 62
	srli a7, a7, 48
	srli a4, a4, 2
	or a4, a4, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 10(a2)
	sub a4, a4, t2
	sub a4, a4, t0
	sub a4, a4, t1
	slli a4, a4, 48
	srli a4, a4, 48
	slli a7, a3, 63
	srli a7, a7, 48
	srli a3, a3, 1
	or a3, a3, a7
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 8(a2)
	sub a3, a3, t2
	sub a3, a3, t0
	sub a3, a3, t1
	slli a3, a3, 48
	srli a3, a3, 48
	slli a7, a6, 59
	srli a7, a7, 48
	srli a6, a6, 5
	or a6, a6, a7
	and t0, a5, a4
	and t1, a5, a3
	xor t1, a3, t1
	lhu t2, 6(a2)
	sub a6, a6, t2
	sub a6, a6, t0
	sub a6, a6, t1
	slli a6, a6, 48
	srli a6, a6, 48
	slli a7, a5, 61
	srli a7, a7, 48
	srli a5, a5, 3
	or a5, a5, a7
	and t0, a4, a3
	and t1, a4, a6
	xor t1, a6, t1
	lhu t2, 4(a2)
	sub a5, a5, t2
	sub a5, a5, t0
	sub a5, a5, t1
	slli a5, a5, 48
	srli a5, a5, 48
	slli a7, a4, 62
	srli a7, a7, 48
	srli a4, a4, 2
	or a4, a4, a7
	and t0, a3, a6
	and t1, a3, a5
	xor t1, a5, t1
	lhu t2, 2(a2)
	sub a4, a4, t2
	sub a4, a4, t0
	sub a4, a4, t1
	slli a4, a4, 48
	srli a4, a4, 48
	slli a7, a3, 63
	srli a7, a7, 48
	srli a3, a3, 1
	or a3, a3, a7
	and t0, a6, a5
	and t1, a6, a4
	xor t1, a4, t1
	lhu t2, 0(a2)
	sub a3, a3, t2
	sub a3, a3, t0
	sub a3, a3, t1
	slli a3, a3, 48
	srli a3, a3, 48
	slli t1, a4, 16
	or t1, t1, a3
	slli t2, a5, 32
	or t1, t1, t2
	slli t2, a6, 48
	or t1, t1, t2
	sb t1, 0(a1)
	srli a7, t1, 8
	sb a7, 1(a1)
	srli a7, t1, 16
	sb a7, 2(a1)
	srli a7, t1, 24
	sb a7, 3(a1)
	srli t2, t1, 32
	sb t2, 4(a1)
	srli a7, t2, 8
	sb a7, 5(a1)
	srli a7, t2, 16
	sb a7, 6(a1)
	srli a7, t2, 24
	sb a7, 7(a1)
	ret
	.option pop
