// The functions of `src/internal/vg_p256_check_point.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p256_check_point:
	.option push
	.option arch, +m, +c
	sd s0, 128(a0)
	sd ra, 136(a0)
	addi s0, a0, 0
	addi t5, zero, 0
	ld t3, 1120(s0)
	ld t4, 64(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1128(s0)
	ld t4, 72(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1136(s0)
	ld t4, 80(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1144(s0)
	ld t4, 88(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t6, zero, 0
	sub a7, t6, t5
	ld t0, 1472(s0)
	and t0, t0, a7
	sd t0, 1472(s0)
	addi t5, zero, 0
	ld t3, 1216(s0)
	ld t4, 64(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1224(s0)
	ld t4, 72(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1232(s0)
	ld t4, 80(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	ld t3, 1240(s0)
	ld t4, 88(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t6, zero, 0
	sub a7, t6, t5
	ld t0, 1472(s0)
	and t0, t0, a7
	sd t0, 1472(s0)
	addi a0, s0, 0
	addi a1, zero, 1152
	addi a2, zero, 1120
	addi a3, zero, 1312
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1184
	addi a2, zero, 1216
	addi a3, zero, 1312
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1248
	addi a2, zero, 1184
	addi a3, zero, 1184
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1376
	addi a2, zero, 1152
	addi a3, zero, 1152
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1376
	addi a3, zero, 1152
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1376
	addi a2, zero, 256
	addi a3, zero, 1152
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1280
	addi a2, zero, 1408
	addi a3, zero, 1376
	call {vg_p256_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1408
	addi a2, zero, 1280
	addi a3, zero, 1344
	call {vg_p256_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1376
	addi a2, zero, 1248
	addi a3, zero, 1408
	call {vg_p256_sub_mod_p}
	addi t3, zero, 0
	ld t4, 1376(s0)
	or t3, t3, t4
	ld t4, 1384(s0)
	or t3, t3, t4
	ld t4, 1392(s0)
	or t3, t3, t4
	ld t4, 1400(s0)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	ld t0, 1472(s0)
	and t0, t0, a7
	sd t0, 1472(s0)
	ld a7, 1472(s0)
	ld t0, 320(s0)
	ld t1, 1152(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1280(s0)
	ld t0, 328(s0)
	ld t1, 1160(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1288(s0)
	ld t0, 336(s0)
	ld t1, 1168(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1296(s0)
	ld t0, 344(s0)
	ld t1, 1176(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1304(s0)
	ld t0, 352(s0)
	ld t1, 1184(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1440(s0)
	ld t0, 360(s0)
	ld t1, 1192(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1448(s0)
	ld t0, 368(s0)
	ld t1, 1200(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1456(s0)
	ld t0, 376(s0)
	ld t1, 1208(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1464(s0)
	ld ra, 136(s0)
	ld s0, 128(s0)
	ret
	.option pop
