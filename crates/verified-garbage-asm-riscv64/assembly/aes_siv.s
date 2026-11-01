// The functions of `src/aes_siv.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_siv_init:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -528
	addi a3, sp, 0
	addi t0, a3, 2047
	addi t0, t0, 136
	andi t0, t0, -8
	sd ra, 0(t0)
	sd s1, 8(t0)
	sd s2, 16(t0)
	sd s3, 24(t0)
	sd s4, 32(t0)
	addi s1, a0, 0
	srli s2, a1, 1
	addi s3, a2, 0
	addi s4, a3, 0
	addi a1, s2, 0
	call {vg_aes_expand_key_scratch}
	addi a0, s3, 0
	srli a1, s2, 2
	addi a1, a1, 6
	addi a2, s3, 240
	addi a3, s4, 0
	call {vg_cmac_aes_subkeys}
	add a0, s1, s2
	addi a1, s2, 0
	addi a2, s3, 272
	addi a3, s4, 0
	call {vg_aes_expand_key_scratch}
	addi t0, s4, 2047
	addi t0, t0, 136
	andi t0, t0, -8
	ld ra, 0(t0)
	ld s1, 8(t0)
	ld s2, 16(t0)
	ld s3, 24(t0)
	ld s4, 32(t0)
	addi sp, sp, 528
	addi sp, sp, 2032
	ret
	.option pop

vg_aes_siv_encrypt:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -544
	addi a7, sp, 0
	sd s2, 136(a7)
	sd s3, 144(a7)
	sd s4, 152(a7)
	sd s5, 160(a7)
	sd s6, 168(a7)
	sd s7, 176(a7)
	sd s8, 184(a7)
	sd s9, 192(a7)
	sd s10, 200(a7)
	sd s11, 208(a7)
	sd s0, 216(a7)
	sd s1, 128(a7)
	sd ra, 224(a7)
	addi s1, a7, 0
	addi s2, a0, 0
	addi s3, a1, 0
	addi s4, a2, 0
	addi s5, a3, 0
	addi s9, a4, 0
	addi s10, a5, 0
	addi s11, a6, 0
	addi t0, zero, 0
	sd t0, 16(s1)
	sd t0, 24(s1)
	addi t0, zero, 0
	sd t0, 256(s1)
	sd t0, 264(s1)
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 256
	addi a5, s1, 384
	addi a3, s1, 16
	addi a4, zero, 16
	call {vg_cmac_aes_finalize}
	beqz s5, 20f
22:
	lbu s6, 0(s4)
	lbu t0, 1(s4)
	slli t0, t0, 8
	or s6, s6, t0
	lbu t0, 2(s4)
	slli t0, t0, 16
	or s6, s6, t0
	lbu t0, 3(s4)
	slli t0, t0, 24
	or s6, s6, t0
	lbu t1, 4(s4)
	lbu t0, 5(s4)
	slli t0, t0, 8
	or t1, t1, t0
	lbu t0, 6(s4)
	slli t0, t0, 16
	or t1, t1, t0
	lbu t0, 7(s4)
	slli t0, t0, 24
	or t1, t1, t0
	slli t1, t1, 32
	or s6, s6, t1
	lbu s7, 8(s4)
	lbu t0, 9(s4)
	slli t0, t0, 8
	or s7, s7, t0
	lbu t0, 10(s4)
	slli t0, t0, 16
	or s7, s7, t0
	lbu t0, 11(s4)
	slli t0, t0, 24
	or s7, s7, t0
	lbu t1, 12(s4)
	lbu t0, 13(s4)
	slli t0, t0, 8
	or t1, t1, t0
	lbu t0, 14(s4)
	slli t0, t0, 16
	or t1, t1, t0
	lbu t0, 15(s4)
	slli t0, t0, 24
	or t1, t1, t0
	slli t1, t1, 32
	or s7, s7, t1
	addi t0, zero, 0
	sd t0, 240(s1)
	sd t0, 248(s1)
	addi s8, zero, 0
	beqz s7, 23f
	addi s8, s7, -1
	srli s8, s8, 4
	slli s8, s8, 4
	j 24f
23:
24:
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 240
	addi a5, s1, 384
	addi a3, s6, 0
	srli a4, s8, 4
	call {vg_cmac_aes_update}
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 240
	addi a5, s1, 384
	add a3, s6, s8
	sub a4, s7, s8
	call {vg_cmac_aes_finalize}
	lbu t1, 256(s1)
	srli t2, t1, 7
	addi t2, t2, -1
	andi t2, t2, 135
	xori t2, t2, 135
	lbu t3, 257(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 256(s1)
	addi t1, t3, 0
	lbu t3, 258(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 257(s1)
	addi t1, t3, 0
	lbu t3, 259(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 258(s1)
	addi t1, t3, 0
	lbu t3, 260(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 259(s1)
	addi t1, t3, 0
	lbu t3, 261(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 260(s1)
	addi t1, t3, 0
	lbu t3, 262(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 261(s1)
	addi t1, t3, 0
	lbu t3, 263(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 262(s1)
	addi t1, t3, 0
	lbu t3, 264(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 263(s1)
	addi t1, t3, 0
	lbu t3, 265(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 264(s1)
	addi t1, t3, 0
	lbu t3, 266(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 265(s1)
	addi t1, t3, 0
	lbu t3, 267(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 266(s1)
	addi t1, t3, 0
	lbu t3, 268(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 267(s1)
	addi t1, t3, 0
	lbu t3, 269(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 268(s1)
	addi t1, t3, 0
	lbu t3, 270(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 269(s1)
	addi t1, t3, 0
	lbu t3, 271(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 270(s1)
	addi t1, t3, 0
	slli t1, t1, 1
	xor t1, t1, t2
	sb t1, 271(s1)
	ld t0, 256(s1)
	ld t1, 240(s1)
	xor t0, t0, t1
	sd t0, 256(s1)
	ld t0, 264(s1)
	ld t1, 248(s1)
	xor t0, t0, t1
	sd t0, 264(s1)
	addi s4, s4, 16
	addi s5, s5, -1
	bnez s5, 22b
	j 21f
20:
21:
	addi s6, s9, 0
	addi s7, s10, 0
	srli t0, s7, 4
	beqz t0, 25f
	addi t0, s7, -1
	srli t0, t0, 4
	addi s8, zero, 0
	beqz t0, 27f
	addi t0, t0, -1
	slli s8, t0, 4
	j 28f
27:
28:
	add a0, s6, s8
	addi a1, s1, 32
	sub a2, s7, s8
29:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 29b
	addi a0, s1, 256
	sub a1, s7, s8
	add a1, s1, a1
	addi a1, a1, 16
	addi a2, zero, 16
210:
	lbu t0, 0(a0)
	lbu t1, 0(a1)
	xor t0, t0, t1
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 210b
	addi t0, zero, 0
	sd t0, 0(s1)
	sd t0, 8(s1)
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 0
	addi a5, s1, 384
	addi a3, s6, 0
	srli a4, s8, 4
	call {vg_cmac_aes_update}
	addi t0, s7, -1
	srli t0, t0, 4
	addi s0, zero, 0
	beqz t0, 211f
	addi s0, zero, 1
	j 212f
211:
212:
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 0
	addi a5, s1, 384
	addi a3, s1, 32
	addi a4, s0, 0
	call {vg_cmac_aes_update}
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 0
	addi a5, s1, 384
	addi a3, s1, 32
	slli t0, s0, 4
	add a3, a3, t0
	sub a4, s7, s8
	sub a4, a4, t0
	call {vg_cmac_aes_finalize}
	j 26f
25:
	addi t0, zero, 0
	sd t0, 32(s1)
	sd t0, 40(s1)
	beqz s7, 213f
	addi a0, s6, 0
	addi a1, s1, 32
	addi a2, s7, 0
215:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 215b
	j 214f
213:
214:
	add t0, s1, s7
	addi t1, zero, 128
	sb t1, 32(t0)
	lbu t1, 256(s1)
	srli t2, t1, 7
	addi t2, t2, -1
	andi t2, t2, 135
	xori t2, t2, 135
	lbu t3, 257(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 272(s1)
	addi t1, t3, 0
	lbu t3, 258(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 273(s1)
	addi t1, t3, 0
	lbu t3, 259(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 274(s1)
	addi t1, t3, 0
	lbu t3, 260(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 275(s1)
	addi t1, t3, 0
	lbu t3, 261(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 276(s1)
	addi t1, t3, 0
	lbu t3, 262(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 277(s1)
	addi t1, t3, 0
	lbu t3, 263(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 278(s1)
	addi t1, t3, 0
	lbu t3, 264(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 279(s1)
	addi t1, t3, 0
	lbu t3, 265(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 280(s1)
	addi t1, t3, 0
	lbu t3, 266(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 281(s1)
	addi t1, t3, 0
	lbu t3, 267(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 282(s1)
	addi t1, t3, 0
	lbu t3, 268(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 283(s1)
	addi t1, t3, 0
	lbu t3, 269(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 284(s1)
	addi t1, t3, 0
	lbu t3, 270(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 285(s1)
	addi t1, t3, 0
	lbu t3, 271(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 286(s1)
	addi t1, t3, 0
	slli t1, t1, 1
	xor t1, t1, t2
	sb t1, 287(s1)
	ld t0, 32(s1)
	ld t1, 272(s1)
	xor t0, t0, t1
	sd t0, 32(s1)
	ld t0, 40(s1)
	ld t1, 280(s1)
	xor t0, t0, t1
	sd t0, 40(s1)
	addi t0, zero, 0
	sd t0, 0(s1)
	sd t0, 8(s1)
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 0
	addi a5, s1, 384
	addi a3, s1, 32
	addi a4, zero, 16
	call {vg_cmac_aes_finalize}
26:
	ld t0, 0(s1)
	sd t0, 64(s1)
	ld t0, 8(s1)
	addi t1, zero, 128
	slli t2, t1, 32
	or t1, t1, t2
	or t0, t0, t1
	xor t0, t0, t1
	sd t0, 72(s1)
	addi s6, s9, 0
	addi s7, s10, 0
	ld t0, 64(s1)
	sd t0, 96(s1)
	ld t0, 72(s1)
	sd t0, 104(s1)
	srli a4, s7, 4
	slli a4, a4, 33
	srli a4, a4, 33
	addi a0, s2, 272
	addi a1, s3, 0
	addi a2, s1, 96
	addi a5, s1, 384
	addi a3, s6, 0
	call {vg_aes_ctr32}
	srli t0, s7, 4
	slli t0, t0, 33
	srli t0, t0, 33
	lbu t1, 72(s1)
	slli t1, t1, 8
	lbu t2, 73(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 74(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 75(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 76(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 77(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 78(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 79(s1)
	or t1, t1, t2
	add t1, t1, t0
	srli t2, t1, 56
	sb t2, 72(s1)
	srli t2, t1, 48
	sb t2, 73(s1)
	srli t2, t1, 40
	sb t2, 74(s1)
	srli t2, t1, 32
	sb t2, 75(s1)
	srli t2, t1, 24
	sb t2, 76(s1)
	srli t2, t1, 16
	sb t2, 77(s1)
	srli t2, t1, 8
	sb t2, 78(s1)
	srli t2, t1, 0
	sb t2, 79(s1)
	slli t0, t0, 4
	add s6, s6, t0
	sub s7, s7, t0
	beqz s7, 216f
218:
	addi t0, zero, 0
	sd t0, 80(s1)
	sd t0, 88(s1)
	ld t0, 64(s1)
	sd t0, 96(s1)
	ld t0, 72(s1)
	sd t0, 104(s1)
	addi a0, s2, 272
	addi a1, s3, 0
	addi a2, s1, 96
	addi a5, s1, 384
	addi a3, s1, 80
	addi a4, zero, 1
	call {vg_aes_ctr32}
	srli t1, s7, 4
	addi a2, s7, 0
	addi a0, s1, 80
	addi a1, s6, 0
	beqz t1, 219f
	addi a2, zero, 16
	j 220f
219:
220:
221:
	lbu t0, 0(a0)
	lbu t1, 0(a1)
	xor t0, t0, t1
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 221b
	lbu t1, 72(s1)
	slli t1, t1, 8
	lbu t2, 73(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 74(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 75(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 76(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 77(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 78(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 79(s1)
	or t1, t1, t2
	addi t1, t1, 1
	srli t2, t1, 56
	sb t2, 72(s1)
	srli t2, t1, 48
	sb t2, 73(s1)
	srli t2, t1, 40
	sb t2, 74(s1)
	srli t2, t1, 32
	sb t2, 75(s1)
	srli t2, t1, 24
	sb t2, 76(s1)
	srli t2, t1, 16
	sb t2, 77(s1)
	srli t2, t1, 8
	sb t2, 78(s1)
	srli t2, t1, 0
	sb t2, 79(s1)
	addi s6, s6, 16
	srli t0, s7, 4
	beqz t0, 222f
	addi s7, s7, -16
	j 223f
222:
	addi s7, zero, 0
223:
	bnez s7, 218b
	j 217f
216:
217:
	lbu t0, 0(s1)
	sb t0, 0(s11)
	lbu t0, 1(s1)
	sb t0, 1(s11)
	lbu t0, 2(s1)
	sb t0, 2(s11)
	lbu t0, 3(s1)
	sb t0, 3(s11)
	lbu t0, 4(s1)
	sb t0, 4(s11)
	lbu t0, 5(s1)
	sb t0, 5(s11)
	lbu t0, 6(s1)
	sb t0, 6(s11)
	lbu t0, 7(s1)
	sb t0, 7(s11)
	lbu t0, 8(s1)
	sb t0, 8(s11)
	lbu t0, 9(s1)
	sb t0, 9(s11)
	lbu t0, 10(s1)
	sb t0, 10(s11)
	lbu t0, 11(s1)
	sb t0, 11(s11)
	lbu t0, 12(s1)
	sb t0, 12(s11)
	lbu t0, 13(s1)
	sb t0, 13(s11)
	lbu t0, 14(s1)
	sb t0, 14(s11)
	lbu t0, 15(s1)
	sb t0, 15(s11)
	ld ra, 224(s1)
	ld s2, 136(s1)
	ld s3, 144(s1)
	ld s4, 152(s1)
	ld s5, 160(s1)
	ld s6, 168(s1)
	ld s7, 176(s1)
	ld s8, 184(s1)
	ld s9, 192(s1)
	ld s10, 200(s1)
	ld s11, 208(s1)
	ld s0, 216(s1)
	ld s1, 128(s1)
	addi sp, sp, 544
	addi sp, sp, 2032
	ret
	.option pop

vg_aes_siv_decrypt:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -544
	addi a7, sp, 0
	sd s2, 136(a7)
	sd s3, 144(a7)
	sd s4, 152(a7)
	sd s5, 160(a7)
	sd s6, 168(a7)
	sd s7, 176(a7)
	sd s8, 184(a7)
	sd s9, 192(a7)
	sd s10, 200(a7)
	sd s11, 208(a7)
	sd s0, 216(a7)
	sd s1, 128(a7)
	sd ra, 224(a7)
	addi s1, a7, 0
	addi s2, a0, 0
	addi s3, a1, 0
	addi s4, a2, 0
	addi s5, a3, 0
	addi s9, a4, 0
	addi s10, a5, 0
	addi s11, a6, 0
	addi t0, zero, 0
	sd t0, 16(s1)
	sd t0, 24(s1)
	addi t0, zero, 0
	sd t0, 256(s1)
	sd t0, 264(s1)
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 256
	addi a5, s1, 384
	addi a3, s1, 16
	addi a4, zero, 16
	call {vg_cmac_aes_finalize}
	beqz s5, 20f
22:
	lbu s6, 0(s4)
	lbu t0, 1(s4)
	slli t0, t0, 8
	or s6, s6, t0
	lbu t0, 2(s4)
	slli t0, t0, 16
	or s6, s6, t0
	lbu t0, 3(s4)
	slli t0, t0, 24
	or s6, s6, t0
	lbu t1, 4(s4)
	lbu t0, 5(s4)
	slli t0, t0, 8
	or t1, t1, t0
	lbu t0, 6(s4)
	slli t0, t0, 16
	or t1, t1, t0
	lbu t0, 7(s4)
	slli t0, t0, 24
	or t1, t1, t0
	slli t1, t1, 32
	or s6, s6, t1
	lbu s7, 8(s4)
	lbu t0, 9(s4)
	slli t0, t0, 8
	or s7, s7, t0
	lbu t0, 10(s4)
	slli t0, t0, 16
	or s7, s7, t0
	lbu t0, 11(s4)
	slli t0, t0, 24
	or s7, s7, t0
	lbu t1, 12(s4)
	lbu t0, 13(s4)
	slli t0, t0, 8
	or t1, t1, t0
	lbu t0, 14(s4)
	slli t0, t0, 16
	or t1, t1, t0
	lbu t0, 15(s4)
	slli t0, t0, 24
	or t1, t1, t0
	slli t1, t1, 32
	or s7, s7, t1
	addi t0, zero, 0
	sd t0, 240(s1)
	sd t0, 248(s1)
	addi s8, zero, 0
	beqz s7, 23f
	addi s8, s7, -1
	srli s8, s8, 4
	slli s8, s8, 4
	j 24f
23:
24:
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 240
	addi a5, s1, 384
	addi a3, s6, 0
	srli a4, s8, 4
	call {vg_cmac_aes_update}
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 240
	addi a5, s1, 384
	add a3, s6, s8
	sub a4, s7, s8
	call {vg_cmac_aes_finalize}
	lbu t1, 256(s1)
	srli t2, t1, 7
	addi t2, t2, -1
	andi t2, t2, 135
	xori t2, t2, 135
	lbu t3, 257(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 256(s1)
	addi t1, t3, 0
	lbu t3, 258(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 257(s1)
	addi t1, t3, 0
	lbu t3, 259(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 258(s1)
	addi t1, t3, 0
	lbu t3, 260(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 259(s1)
	addi t1, t3, 0
	lbu t3, 261(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 260(s1)
	addi t1, t3, 0
	lbu t3, 262(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 261(s1)
	addi t1, t3, 0
	lbu t3, 263(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 262(s1)
	addi t1, t3, 0
	lbu t3, 264(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 263(s1)
	addi t1, t3, 0
	lbu t3, 265(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 264(s1)
	addi t1, t3, 0
	lbu t3, 266(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 265(s1)
	addi t1, t3, 0
	lbu t3, 267(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 266(s1)
	addi t1, t3, 0
	lbu t3, 268(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 267(s1)
	addi t1, t3, 0
	lbu t3, 269(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 268(s1)
	addi t1, t3, 0
	lbu t3, 270(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 269(s1)
	addi t1, t3, 0
	lbu t3, 271(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 270(s1)
	addi t1, t3, 0
	slli t1, t1, 1
	xor t1, t1, t2
	sb t1, 271(s1)
	ld t0, 256(s1)
	ld t1, 240(s1)
	xor t0, t0, t1
	sd t0, 256(s1)
	ld t0, 264(s1)
	ld t1, 248(s1)
	xor t0, t0, t1
	sd t0, 264(s1)
	addi s4, s4, 16
	addi s5, s5, -1
	bnez s5, 22b
	j 21f
20:
21:
	addi s6, s9, 0
	addi s7, s10, 0
	lbu t0, 0(s11)
	sb t0, 0(s1)
	lbu t0, 1(s11)
	sb t0, 1(s1)
	lbu t0, 2(s11)
	sb t0, 2(s1)
	lbu t0, 3(s11)
	sb t0, 3(s1)
	lbu t0, 4(s11)
	sb t0, 4(s1)
	lbu t0, 5(s11)
	sb t0, 5(s1)
	lbu t0, 6(s11)
	sb t0, 6(s1)
	lbu t0, 7(s11)
	sb t0, 7(s1)
	lbu t0, 8(s11)
	sb t0, 8(s1)
	lbu t0, 9(s11)
	sb t0, 9(s1)
	lbu t0, 10(s11)
	sb t0, 10(s1)
	lbu t0, 11(s11)
	sb t0, 11(s1)
	lbu t0, 12(s11)
	sb t0, 12(s1)
	lbu t0, 13(s11)
	sb t0, 13(s1)
	lbu t0, 14(s11)
	sb t0, 14(s1)
	lbu t0, 15(s11)
	sb t0, 15(s1)
	ld t0, 0(s1)
	sd t0, 64(s1)
	ld t0, 8(s1)
	addi t1, zero, 128
	slli t2, t1, 32
	or t1, t1, t2
	or t0, t0, t1
	xor t0, t0, t1
	sd t0, 72(s1)
	addi s6, s9, 0
	addi s7, s10, 0
	ld t0, 64(s1)
	sd t0, 96(s1)
	ld t0, 72(s1)
	sd t0, 104(s1)
	srli a4, s7, 4
	slli a4, a4, 33
	srli a4, a4, 33
	addi a0, s2, 272
	addi a1, s3, 0
	addi a2, s1, 96
	addi a5, s1, 384
	addi a3, s6, 0
	call {vg_aes_ctr32}
	srli t0, s7, 4
	slli t0, t0, 33
	srli t0, t0, 33
	lbu t1, 72(s1)
	slli t1, t1, 8
	lbu t2, 73(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 74(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 75(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 76(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 77(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 78(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 79(s1)
	or t1, t1, t2
	add t1, t1, t0
	srli t2, t1, 56
	sb t2, 72(s1)
	srli t2, t1, 48
	sb t2, 73(s1)
	srli t2, t1, 40
	sb t2, 74(s1)
	srli t2, t1, 32
	sb t2, 75(s1)
	srli t2, t1, 24
	sb t2, 76(s1)
	srli t2, t1, 16
	sb t2, 77(s1)
	srli t2, t1, 8
	sb t2, 78(s1)
	srli t2, t1, 0
	sb t2, 79(s1)
	slli t0, t0, 4
	add s6, s6, t0
	sub s7, s7, t0
	beqz s7, 25f
27:
	addi t0, zero, 0
	sd t0, 80(s1)
	sd t0, 88(s1)
	ld t0, 64(s1)
	sd t0, 96(s1)
	ld t0, 72(s1)
	sd t0, 104(s1)
	addi a0, s2, 272
	addi a1, s3, 0
	addi a2, s1, 96
	addi a5, s1, 384
	addi a3, s1, 80
	addi a4, zero, 1
	call {vg_aes_ctr32}
	srli t1, s7, 4
	addi a2, s7, 0
	addi a0, s1, 80
	addi a1, s6, 0
	beqz t1, 28f
	addi a2, zero, 16
	j 29f
28:
29:
210:
	lbu t0, 0(a0)
	lbu t1, 0(a1)
	xor t0, t0, t1
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 210b
	lbu t1, 72(s1)
	slli t1, t1, 8
	lbu t2, 73(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 74(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 75(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 76(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 77(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 78(s1)
	or t1, t1, t2
	slli t1, t1, 8
	lbu t2, 79(s1)
	or t1, t1, t2
	addi t1, t1, 1
	srli t2, t1, 56
	sb t2, 72(s1)
	srli t2, t1, 48
	sb t2, 73(s1)
	srli t2, t1, 40
	sb t2, 74(s1)
	srli t2, t1, 32
	sb t2, 75(s1)
	srli t2, t1, 24
	sb t2, 76(s1)
	srli t2, t1, 16
	sb t2, 77(s1)
	srli t2, t1, 8
	sb t2, 78(s1)
	srli t2, t1, 0
	sb t2, 79(s1)
	addi s6, s6, 16
	srli t0, s7, 4
	beqz t0, 211f
	addi s7, s7, -16
	j 212f
211:
	addi s7, zero, 0
212:
	bnez s7, 27b
	j 26f
25:
26:
	addi s6, s9, 0
	addi s7, s10, 0
	srli t0, s7, 4
	beqz t0, 213f
	addi t0, s7, -1
	srli t0, t0, 4
	addi s8, zero, 0
	beqz t0, 215f
	addi t0, t0, -1
	slli s8, t0, 4
	j 216f
215:
216:
	add a0, s6, s8
	addi a1, s1, 32
	sub a2, s7, s8
217:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 217b
	addi a0, s1, 256
	sub a1, s7, s8
	add a1, s1, a1
	addi a1, a1, 16
	addi a2, zero, 16
218:
	lbu t0, 0(a0)
	lbu t1, 0(a1)
	xor t0, t0, t1
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 218b
	addi t0, zero, 0
	sd t0, 112(s1)
	sd t0, 120(s1)
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 112
	addi a5, s1, 384
	addi a3, s6, 0
	srli a4, s8, 4
	call {vg_cmac_aes_update}
	addi t0, s7, -1
	srli t0, t0, 4
	addi s0, zero, 0
	beqz t0, 219f
	addi s0, zero, 1
	j 220f
219:
220:
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 112
	addi a5, s1, 384
	addi a3, s1, 32
	addi a4, s0, 0
	call {vg_cmac_aes_update}
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 112
	addi a5, s1, 384
	addi a3, s1, 32
	slli t0, s0, 4
	add a3, a3, t0
	sub a4, s7, s8
	sub a4, a4, t0
	call {vg_cmac_aes_finalize}
	j 214f
213:
	addi t0, zero, 0
	sd t0, 32(s1)
	sd t0, 40(s1)
	beqz s7, 221f
	addi a0, s6, 0
	addi a1, s1, 32
	addi a2, s7, 0
223:
	lbu t0, 0(a0)
	sb t0, 0(a1)
	addi a0, a0, 1
	addi a1, a1, 1
	addi a2, a2, -1
	bnez a2, 223b
	j 222f
221:
222:
	add t0, s1, s7
	addi t1, zero, 128
	sb t1, 32(t0)
	lbu t1, 256(s1)
	srli t2, t1, 7
	addi t2, t2, -1
	andi t2, t2, 135
	xori t2, t2, 135
	lbu t3, 257(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 272(s1)
	addi t1, t3, 0
	lbu t3, 258(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 273(s1)
	addi t1, t3, 0
	lbu t3, 259(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 274(s1)
	addi t1, t3, 0
	lbu t3, 260(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 275(s1)
	addi t1, t3, 0
	lbu t3, 261(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 276(s1)
	addi t1, t3, 0
	lbu t3, 262(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 277(s1)
	addi t1, t3, 0
	lbu t3, 263(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 278(s1)
	addi t1, t3, 0
	lbu t3, 264(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 279(s1)
	addi t1, t3, 0
	lbu t3, 265(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 280(s1)
	addi t1, t3, 0
	lbu t3, 266(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 281(s1)
	addi t1, t3, 0
	lbu t3, 267(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 282(s1)
	addi t1, t3, 0
	lbu t3, 268(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 283(s1)
	addi t1, t3, 0
	lbu t3, 269(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 284(s1)
	addi t1, t3, 0
	lbu t3, 270(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 285(s1)
	addi t1, t3, 0
	lbu t3, 271(s1)
	slli t1, t1, 1
	srli t4, t3, 7
	or t1, t1, t4
	sb t1, 286(s1)
	addi t1, t3, 0
	slli t1, t1, 1
	xor t1, t1, t2
	sb t1, 287(s1)
	ld t0, 32(s1)
	ld t1, 272(s1)
	xor t0, t0, t1
	sd t0, 32(s1)
	ld t0, 40(s1)
	ld t1, 280(s1)
	xor t0, t0, t1
	sd t0, 40(s1)
	addi t0, zero, 0
	sd t0, 112(s1)
	sd t0, 120(s1)
	addi a0, s2, 0
	addi a1, s3, 0
	addi a2, s1, 112
	addi a5, s1, 384
	addi a3, s1, 32
	addi a4, zero, 16
	call {vg_cmac_aes_finalize}
214:
	ld t0, 0(s1)
	ld t1, 112(s1)
	xor t0, t0, t1
	ld t1, 8(s1)
	ld t2, 120(s1)
	xor t1, t1, t2
	or t0, t0, t1
	addi t1, zero, 0
	sltu t0, t1, t0
	addi s0, zero, 1
	sub s0, s0, t0
	addi t1, zero, 0
	sub t1, t1, s0
	addi a0, s9, 0
	addi a2, s10, 0
	beqz a2, 224f
226:
	lbu t0, 0(a0)
	and t0, t0, t1
	sb t0, 0(a0)
	addi a0, a0, 1
	addi a2, a2, -1
	bnez a2, 226b
	j 225f
224:
225:
	addi a0, s0, 0
	ld ra, 224(s1)
	ld s2, 136(s1)
	ld s3, 144(s1)
	ld s4, 152(s1)
	ld s5, 160(s1)
	ld s6, 168(s1)
	ld s7, 176(s1)
	ld s8, 184(s1)
	ld s9, 192(s1)
	ld s10, 200(s1)
	ld s11, 208(s1)
	ld s0, 216(s1)
	ld s1, 128(s1)
	addi sp, sp, 544
	addi sp, sp, 2032
	ret
	.option pop
