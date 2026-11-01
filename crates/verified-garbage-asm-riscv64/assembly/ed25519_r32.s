// The functions of `src/ed25519_r32.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed25519_r32_point_add:
	.option push
	.option arch, +m, +c
	addi a3, a0, 0
	ld t3, 96(a3)
	ld a7, 64(a3)
	sltu a5, t3, a7
	sub t3, t3, a7
	ld t4, 104(a3)
	ld a7, 72(a3)
	sltu a6, t4, a7
	sub t4, t4, a7
	sltu a7, t4, a5
	sub t4, t4, a5
	add a5, a6, a7
	ld t5, 112(a3)
	ld a7, 80(a3)
	sltu a6, t5, a7
	sub t5, t5, a7
	sltu a7, t5, a5
	sub t5, t5, a5
	add a5, a6, a7
	ld t6, 120(a3)
	ld a7, 88(a3)
	sltu a6, t6, a7
	sub t6, t6, a7
	sltu a7, t6, a5
	sub t6, t6, a5
	add a5, a6, a7
	addi a4, zero, 38
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	sd t3, 320(a3)
	sd t4, 328(a3)
	sd t5, 336(a3)
	sd t6, 344(a3)
	ld t3, 224(a3)
	ld a7, 192(a3)
	sltu a5, t3, a7
	sub t3, t3, a7
	ld t4, 232(a3)
	ld a7, 200(a3)
	sltu a6, t4, a7
	sub t4, t4, a7
	sltu a7, t4, a5
	sub t4, t4, a5
	add a5, a6, a7
	ld t5, 240(a3)
	ld a7, 208(a3)
	sltu a6, t5, a7
	sub t5, t5, a7
	sltu a7, t5, a5
	sub t5, t5, a5
	add a5, a6, a7
	ld t6, 248(a3)
	ld a7, 216(a3)
	sltu a6, t6, a7
	sub t6, t6, a7
	sltu a7, t6, a5
	sub t6, t6, a5
	add a5, a6, a7
	addi a4, zero, 38
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	sd t3, 352(a3)
	sd t4, 360(a3)
	sd t5, 368(a3)
	sd t6, 376(a3)
	ld t3, 352(a3)
	ld t4, 360(a3)
	ld t5, 368(a3)
	ld t6, 376(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	ld t0, 320(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 864(a3)
	addi a4, zero, 0
	ld t0, 328(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 320(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 872(a3)
	addi a5, zero, 0
	ld t0, 336(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 328(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 320(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 880(a3)
	addi a6, zero, 0
	ld t0, 344(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 336(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 328(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 320(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 888(a3)
	addi a4, zero, 0
	ld t0, 344(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 336(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 328(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 896(a3)
	addi a5, zero, 0
	ld t0, 344(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 336(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 904(a3)
	addi a6, zero, 0
	ld t0, 344(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 912(a3)
	addi a4, zero, 0
	sd a5, 920(a3)
	addi a5, zero, 0
	addi a4, zero, 38
	ld t3, 864(a3)
	ld a7, 896(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t3, t3, t0
	sltu a5, t3, t0
	ld t4, 872(a3)
	ld a7, 904(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t4, t4, t0
	sltu a6, t4, t0
	add t4, t4, a1
	sltu a7, t4, a1
	add a6, a6, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a6, a6, a7
	ld t5, 880(a3)
	ld a7, 912(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t5, t5, t0
	sltu a5, t5, t0
	add t5, t5, a2
	sltu a7, t5, a2
	add a5, a5, a7
	add t5, t5, a6
	sltu a7, t5, a6
	add a5, a5, a7
	ld t6, 888(a3)
	ld a7, 920(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t6, t6, t0
	sltu a6, t6, t0
	add t6, t6, a1
	sltu a7, t6, a1
	add a6, a6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a6, a6, a7
	add a5, a2, a6
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 320(a3)
	sd t4, 328(a3)
	sd t5, 336(a3)
	sd t6, 344(a3)
	ld t3, 96(a3)
	ld a7, 64(a3)
	add t3, t3, a7
	sltu a5, t3, a7
	ld t4, 104(a3)
	ld a7, 72(a3)
	add t4, t4, a7
	sltu a6, t4, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a5, a6, a7
	ld t5, 112(a3)
	ld a7, 80(a3)
	add t5, t5, a7
	sltu a6, t5, a7
	add t5, t5, a5
	sltu a7, t5, a5
	add a5, a6, a7
	ld t6, 120(a3)
	ld a7, 88(a3)
	add t6, t6, a7
	sltu a6, t6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a5, a6, a7
	addi a4, zero, 38
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 352(a3)
	sd t4, 360(a3)
	sd t5, 368(a3)
	sd t6, 376(a3)
	ld t3, 224(a3)
	ld a7, 192(a3)
	add t3, t3, a7
	sltu a5, t3, a7
	ld t4, 232(a3)
	ld a7, 200(a3)
	add t4, t4, a7
	sltu a6, t4, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a5, a6, a7
	ld t5, 240(a3)
	ld a7, 208(a3)
	add t5, t5, a7
	sltu a6, t5, a7
	add t5, t5, a5
	sltu a7, t5, a5
	add a5, a6, a7
	ld t6, 248(a3)
	ld a7, 216(a3)
	add t6, t6, a7
	sltu a6, t6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a5, a6, a7
	addi a4, zero, 38
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 384(a3)
	sd t4, 392(a3)
	sd t5, 400(a3)
	sd t6, 408(a3)
	ld t3, 384(a3)
	ld t4, 392(a3)
	ld t5, 400(a3)
	ld t6, 408(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	ld t0, 352(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 864(a3)
	addi a4, zero, 0
	ld t0, 360(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 352(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 872(a3)
	addi a5, zero, 0
	ld t0, 368(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 360(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 352(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 880(a3)
	addi a6, zero, 0
	ld t0, 376(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 368(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 360(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 352(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 888(a3)
	addi a4, zero, 0
	ld t0, 376(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 368(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 360(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 896(a3)
	addi a5, zero, 0
	ld t0, 376(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 368(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 904(a3)
	addi a6, zero, 0
	ld t0, 376(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 912(a3)
	addi a4, zero, 0
	sd a5, 920(a3)
	addi a5, zero, 0
	addi a4, zero, 38
	ld t3, 864(a3)
	ld a7, 896(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t3, t3, t0
	sltu a5, t3, t0
	ld t4, 872(a3)
	ld a7, 904(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t4, t4, t0
	sltu a6, t4, t0
	add t4, t4, a1
	sltu a7, t4, a1
	add a6, a6, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a6, a6, a7
	ld t5, 880(a3)
	ld a7, 912(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t5, t5, t0
	sltu a5, t5, t0
	add t5, t5, a2
	sltu a7, t5, a2
	add a5, a5, a7
	add t5, t5, a6
	sltu a7, t5, a6
	add a5, a5, a7
	ld t6, 888(a3)
	ld a7, 920(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t6, t6, t0
	sltu a6, t6, t0
	add t6, t6, a1
	sltu a7, t6, a1
	add a6, a6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a6, a6, a7
	add a5, a2, a6
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 352(a3)
	sd t4, 360(a3)
	sd t5, 368(a3)
	sd t6, 376(a3)
	ld t3, 576(a3)
	ld t4, 584(a3)
	ld t5, 592(a3)
	ld t6, 600(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	ld t0, 160(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 864(a3)
	addi a4, zero, 0
	ld t0, 168(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 160(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 872(a3)
	addi a5, zero, 0
	ld t0, 176(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 168(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 160(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 880(a3)
	addi a6, zero, 0
	ld t0, 184(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 176(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 168(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 160(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 888(a3)
	addi a4, zero, 0
	ld t0, 184(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 176(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 168(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 896(a3)
	addi a5, zero, 0
	ld t0, 184(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 176(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 904(a3)
	addi a6, zero, 0
	ld t0, 184(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 912(a3)
	addi a4, zero, 0
	sd a5, 920(a3)
	addi a5, zero, 0
	addi a4, zero, 38
	ld t3, 864(a3)
	ld a7, 896(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t3, t3, t0
	sltu a5, t3, t0
	ld t4, 872(a3)
	ld a7, 904(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t4, t4, t0
	sltu a6, t4, t0
	add t4, t4, a1
	sltu a7, t4, a1
	add a6, a6, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a6, a6, a7
	ld t5, 880(a3)
	ld a7, 912(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t5, t5, t0
	sltu a5, t5, t0
	add t5, t5, a2
	sltu a7, t5, a2
	add a5, a5, a7
	add t5, t5, a6
	sltu a7, t5, a6
	add a5, a5, a7
	ld t6, 888(a3)
	ld a7, 920(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t6, t6, t0
	sltu a6, t6, t0
	add t6, t6, a1
	sltu a7, t6, a1
	add a6, a6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a6, a6, a7
	add a5, a2, a6
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 384(a3)
	sd t4, 392(a3)
	sd t5, 400(a3)
	sd t6, 408(a3)
	ld t3, 384(a3)
	ld a7, 384(a3)
	add t3, t3, a7
	sltu a5, t3, a7
	ld t4, 392(a3)
	ld a7, 392(a3)
	add t4, t4, a7
	sltu a6, t4, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a5, a6, a7
	ld t5, 400(a3)
	ld a7, 400(a3)
	add t5, t5, a7
	sltu a6, t5, a7
	add t5, t5, a5
	sltu a7, t5, a5
	add a5, a6, a7
	ld t6, 408(a3)
	ld a7, 408(a3)
	add t6, t6, a7
	sltu a6, t6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a5, a6, a7
	addi a4, zero, 38
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 384(a3)
	sd t4, 392(a3)
	sd t5, 400(a3)
	sd t6, 408(a3)
	ld t3, 288(a3)
	ld t4, 296(a3)
	ld t5, 304(a3)
	ld t6, 312(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	ld t0, 384(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 864(a3)
	addi a4, zero, 0
	ld t0, 392(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 384(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 872(a3)
	addi a5, zero, 0
	ld t0, 400(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 392(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 384(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 880(a3)
	addi a6, zero, 0
	ld t0, 408(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 400(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 392(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 384(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 888(a3)
	addi a4, zero, 0
	ld t0, 408(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 400(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 392(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 896(a3)
	addi a5, zero, 0
	ld t0, 408(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 400(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 904(a3)
	addi a6, zero, 0
	ld t0, 408(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 912(a3)
	addi a4, zero, 0
	sd a5, 920(a3)
	addi a5, zero, 0
	addi a4, zero, 38
	ld t3, 864(a3)
	ld a7, 896(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t3, t3, t0
	sltu a5, t3, t0
	ld t4, 872(a3)
	ld a7, 904(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t4, t4, t0
	sltu a6, t4, t0
	add t4, t4, a1
	sltu a7, t4, a1
	add a6, a6, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a6, a6, a7
	ld t5, 880(a3)
	ld a7, 912(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t5, t5, t0
	sltu a5, t5, t0
	add t5, t5, a2
	sltu a7, t5, a2
	add a5, a5, a7
	add t5, t5, a6
	sltu a7, t5, a6
	add a5, a5, a7
	ld t6, 888(a3)
	ld a7, 920(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t6, t6, t0
	sltu a6, t6, t0
	add t6, t6, a1
	sltu a7, t6, a1
	add a6, a6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a6, a6, a7
	add a5, a2, a6
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 384(a3)
	sd t4, 392(a3)
	sd t5, 400(a3)
	sd t6, 408(a3)
	ld t3, 128(a3)
	ld a7, 128(a3)
	add t3, t3, a7
	sltu a5, t3, a7
	ld t4, 136(a3)
	ld a7, 136(a3)
	add t4, t4, a7
	sltu a6, t4, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a5, a6, a7
	ld t5, 144(a3)
	ld a7, 144(a3)
	add t5, t5, a7
	sltu a6, t5, a7
	add t5, t5, a5
	sltu a7, t5, a5
	add a5, a6, a7
	ld t6, 152(a3)
	ld a7, 152(a3)
	add t6, t6, a7
	sltu a6, t6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a5, a6, a7
	addi a4, zero, 38
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 416(a3)
	sd t4, 424(a3)
	sd t5, 432(a3)
	sd t6, 440(a3)
	ld t3, 256(a3)
	ld t4, 264(a3)
	ld t5, 272(a3)
	ld t6, 280(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	ld t0, 416(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 864(a3)
	addi a4, zero, 0
	ld t0, 424(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 416(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 872(a3)
	addi a5, zero, 0
	ld t0, 432(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 424(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 416(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 880(a3)
	addi a6, zero, 0
	ld t0, 440(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 432(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 424(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 416(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 888(a3)
	addi a4, zero, 0
	ld t0, 440(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 432(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 424(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 896(a3)
	addi a5, zero, 0
	ld t0, 440(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 432(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 904(a3)
	addi a6, zero, 0
	ld t0, 440(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 912(a3)
	addi a4, zero, 0
	sd a5, 920(a3)
	addi a5, zero, 0
	addi a4, zero, 38
	ld t3, 864(a3)
	ld a7, 896(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t3, t3, t0
	sltu a5, t3, t0
	ld t4, 872(a3)
	ld a7, 904(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t4, t4, t0
	sltu a6, t4, t0
	add t4, t4, a1
	sltu a7, t4, a1
	add a6, a6, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a6, a6, a7
	ld t5, 880(a3)
	ld a7, 912(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t5, t5, t0
	sltu a5, t5, t0
	add t5, t5, a2
	sltu a7, t5, a2
	add a5, a5, a7
	add t5, t5, a6
	sltu a7, t5, a6
	add a5, a5, a7
	ld t6, 888(a3)
	ld a7, 920(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t6, t6, t0
	sltu a6, t6, t0
	add t6, t6, a1
	sltu a7, t6, a1
	add a6, a6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a6, a6, a7
	add a5, a2, a6
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 416(a3)
	sd t4, 424(a3)
	sd t5, 432(a3)
	sd t6, 440(a3)
	ld t3, 352(a3)
	ld a7, 320(a3)
	sltu a5, t3, a7
	sub t3, t3, a7
	ld t4, 360(a3)
	ld a7, 328(a3)
	sltu a6, t4, a7
	sub t4, t4, a7
	sltu a7, t4, a5
	sub t4, t4, a5
	add a5, a6, a7
	ld t5, 368(a3)
	ld a7, 336(a3)
	sltu a6, t5, a7
	sub t5, t5, a7
	sltu a7, t5, a5
	sub t5, t5, a5
	add a5, a6, a7
	ld t6, 376(a3)
	ld a7, 344(a3)
	sltu a6, t6, a7
	sub t6, t6, a7
	sltu a7, t6, a5
	sub t6, t6, a5
	add a5, a6, a7
	addi a4, zero, 38
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	sd t3, 448(a3)
	sd t4, 456(a3)
	sd t5, 464(a3)
	sd t6, 472(a3)
	ld t3, 416(a3)
	ld a7, 384(a3)
	sltu a5, t3, a7
	sub t3, t3, a7
	ld t4, 424(a3)
	ld a7, 392(a3)
	sltu a6, t4, a7
	sub t4, t4, a7
	sltu a7, t4, a5
	sub t4, t4, a5
	add a5, a6, a7
	ld t5, 432(a3)
	ld a7, 400(a3)
	sltu a6, t5, a7
	sub t5, t5, a7
	sltu a7, t5, a5
	sub t5, t5, a5
	add a5, a6, a7
	ld t6, 440(a3)
	ld a7, 408(a3)
	sltu a6, t6, a7
	sub t6, t6, a7
	sltu a7, t6, a5
	sub t6, t6, a5
	add a5, a6, a7
	addi a4, zero, 38
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	mul a7, a5, a4
	sltu t0, t3, a7
	sub t3, t3, a7
	sltu a7, t4, t0
	sub t4, t4, t0
	sltu t0, t5, a7
	sub t5, t5, a7
	sltu a5, t6, t0
	sub t6, t6, t0
	sd t3, 480(a3)
	sd t4, 488(a3)
	sd t5, 496(a3)
	sd t6, 504(a3)
	ld t3, 416(a3)
	ld a7, 384(a3)
	add t3, t3, a7
	sltu a5, t3, a7
	ld t4, 424(a3)
	ld a7, 392(a3)
	add t4, t4, a7
	sltu a6, t4, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a5, a6, a7
	ld t5, 432(a3)
	ld a7, 400(a3)
	add t5, t5, a7
	sltu a6, t5, a7
	add t5, t5, a5
	sltu a7, t5, a5
	add a5, a6, a7
	ld t6, 440(a3)
	ld a7, 408(a3)
	add t6, t6, a7
	sltu a6, t6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a5, a6, a7
	addi a4, zero, 38
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 512(a3)
	sd t4, 520(a3)
	sd t5, 528(a3)
	sd t6, 536(a3)
	ld t3, 352(a3)
	ld a7, 320(a3)
	add t3, t3, a7
	sltu a5, t3, a7
	ld t4, 360(a3)
	ld a7, 328(a3)
	add t4, t4, a7
	sltu a6, t4, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a5, a6, a7
	ld t5, 368(a3)
	ld a7, 336(a3)
	add t5, t5, a7
	sltu a6, t5, a7
	add t5, t5, a5
	sltu a7, t5, a5
	add a5, a6, a7
	ld t6, 376(a3)
	ld a7, 344(a3)
	add t6, t6, a7
	sltu a6, t6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a5, a6, a7
	addi a4, zero, 38
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 544(a3)
	sd t4, 552(a3)
	sd t5, 560(a3)
	sd t6, 568(a3)
	ld t3, 480(a3)
	ld t4, 488(a3)
	ld t5, 496(a3)
	ld t6, 504(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	ld t0, 448(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 864(a3)
	addi a4, zero, 0
	ld t0, 456(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 448(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 872(a3)
	addi a5, zero, 0
	ld t0, 464(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 456(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 448(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 880(a3)
	addi a6, zero, 0
	ld t0, 472(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 464(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 456(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 448(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 888(a3)
	addi a4, zero, 0
	ld t0, 472(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 464(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 456(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 896(a3)
	addi a5, zero, 0
	ld t0, 472(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 464(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 904(a3)
	addi a6, zero, 0
	ld t0, 472(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 912(a3)
	addi a4, zero, 0
	sd a5, 920(a3)
	addi a5, zero, 0
	addi a4, zero, 38
	ld t3, 864(a3)
	ld a7, 896(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t3, t3, t0
	sltu a5, t3, t0
	ld t4, 872(a3)
	ld a7, 904(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t4, t4, t0
	sltu a6, t4, t0
	add t4, t4, a1
	sltu a7, t4, a1
	add a6, a6, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a6, a6, a7
	ld t5, 880(a3)
	ld a7, 912(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t5, t5, t0
	sltu a5, t5, t0
	add t5, t5, a2
	sltu a7, t5, a2
	add a5, a5, a7
	add t5, t5, a6
	sltu a7, t5, a6
	add a5, a5, a7
	ld t6, 888(a3)
	ld a7, 920(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t6, t6, t0
	sltu a6, t6, t0
	add t6, t6, a1
	sltu a7, t6, a1
	add a6, a6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a6, a6, a7
	add a5, a2, a6
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 64(a3)
	sd t4, 72(a3)
	sd t5, 80(a3)
	sd t6, 88(a3)
	ld t3, 544(a3)
	ld t4, 552(a3)
	ld t5, 560(a3)
	ld t6, 568(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	ld t0, 512(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 864(a3)
	addi a4, zero, 0
	ld t0, 520(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 512(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 872(a3)
	addi a5, zero, 0
	ld t0, 528(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 520(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 512(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 880(a3)
	addi a6, zero, 0
	ld t0, 536(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 528(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 520(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 512(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 888(a3)
	addi a4, zero, 0
	ld t0, 536(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 528(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 520(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 896(a3)
	addi a5, zero, 0
	ld t0, 536(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 528(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 904(a3)
	addi a6, zero, 0
	ld t0, 536(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 912(a3)
	addi a4, zero, 0
	sd a5, 920(a3)
	addi a5, zero, 0
	addi a4, zero, 38
	ld t3, 864(a3)
	ld a7, 896(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t3, t3, t0
	sltu a5, t3, t0
	ld t4, 872(a3)
	ld a7, 904(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t4, t4, t0
	sltu a6, t4, t0
	add t4, t4, a1
	sltu a7, t4, a1
	add a6, a6, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a6, a6, a7
	ld t5, 880(a3)
	ld a7, 912(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t5, t5, t0
	sltu a5, t5, t0
	add t5, t5, a2
	sltu a7, t5, a2
	add a5, a5, a7
	add t5, t5, a6
	sltu a7, t5, a6
	add a5, a5, a7
	ld t6, 888(a3)
	ld a7, 920(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t6, t6, t0
	sltu a6, t6, t0
	add t6, t6, a1
	sltu a7, t6, a1
	add a6, a6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a6, a6, a7
	add a5, a2, a6
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 96(a3)
	sd t4, 104(a3)
	sd t5, 112(a3)
	sd t6, 120(a3)
	ld t3, 512(a3)
	ld t4, 520(a3)
	ld t5, 528(a3)
	ld t6, 536(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	ld t0, 480(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 864(a3)
	addi a4, zero, 0
	ld t0, 488(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 480(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 872(a3)
	addi a5, zero, 0
	ld t0, 496(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 488(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 480(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 880(a3)
	addi a6, zero, 0
	ld t0, 504(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 496(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 488(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 480(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 888(a3)
	addi a4, zero, 0
	ld t0, 504(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 496(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 488(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 896(a3)
	addi a5, zero, 0
	ld t0, 504(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 496(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 904(a3)
	addi a6, zero, 0
	ld t0, 504(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 912(a3)
	addi a4, zero, 0
	sd a5, 920(a3)
	addi a5, zero, 0
	addi a4, zero, 38
	ld t3, 864(a3)
	ld a7, 896(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t3, t3, t0
	sltu a5, t3, t0
	ld t4, 872(a3)
	ld a7, 904(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t4, t4, t0
	sltu a6, t4, t0
	add t4, t4, a1
	sltu a7, t4, a1
	add a6, a6, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a6, a6, a7
	ld t5, 880(a3)
	ld a7, 912(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t5, t5, t0
	sltu a5, t5, t0
	add t5, t5, a2
	sltu a7, t5, a2
	add a5, a5, a7
	add t5, t5, a6
	sltu a7, t5, a6
	add a5, a5, a7
	ld t6, 888(a3)
	ld a7, 920(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t6, t6, t0
	sltu a6, t6, t0
	add t6, t6, a1
	sltu a7, t6, a1
	add a6, a6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a6, a6, a7
	add a5, a2, a6
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 128(a3)
	sd t4, 136(a3)
	sd t5, 144(a3)
	sd t6, 152(a3)
	ld t3, 544(a3)
	ld t4, 552(a3)
	ld t5, 560(a3)
	ld t6, 568(a3)
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	ld t0, 448(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 864(a3)
	addi a4, zero, 0
	ld t0, 456(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 448(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 872(a3)
	addi a5, zero, 0
	ld t0, 464(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 456(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 448(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 880(a3)
	addi a6, zero, 0
	ld t0, 472(a3)
	mul a7, t0, t3
	mulhu t0, t0, t3
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 464(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 456(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	ld t0, 448(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 888(a3)
	addi a4, zero, 0
	ld t0, 472(a3)
	mul a7, t0, t4
	mulhu t0, t0, t4
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 464(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	ld t0, 456(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a5, a5, a7
	sltu a7, a5, a7
	add t0, t0, a7
	add a6, a6, t0
	sltu t0, a6, t0
	add a4, a4, t0
	sd a5, 896(a3)
	addi a5, zero, 0
	ld t0, 472(a3)
	mul a7, t0, t5
	mulhu t0, t0, t5
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	ld t0, 464(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a6, a6, a7
	sltu a7, a6, a7
	add t0, t0, a7
	add a4, a4, t0
	sltu t0, a4, t0
	add a5, a5, t0
	sd a6, 904(a3)
	addi a6, zero, 0
	ld t0, 472(a3)
	mul a7, t0, t6
	mulhu t0, t0, t6
	add a4, a4, a7
	sltu a7, a4, a7
	add t0, t0, a7
	add a5, a5, t0
	sltu t0, a5, t0
	add a6, a6, t0
	sd a4, 912(a3)
	addi a4, zero, 0
	sd a5, 920(a3)
	addi a5, zero, 0
	addi a4, zero, 38
	ld t3, 864(a3)
	ld a7, 896(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t3, t3, t0
	sltu a5, t3, t0
	ld t4, 872(a3)
	ld a7, 904(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t4, t4, t0
	sltu a6, t4, t0
	add t4, t4, a1
	sltu a7, t4, a1
	add a6, a6, a7
	add t4, t4, a5
	sltu a7, t4, a5
	add a6, a6, a7
	ld t5, 880(a3)
	ld a7, 912(a3)
	mul t0, a7, a4
	mulhu a1, a7, a4
	add t5, t5, t0
	sltu a5, t5, t0
	add t5, t5, a2
	sltu a7, t5, a2
	add a5, a5, a7
	add t5, t5, a6
	sltu a7, t5, a6
	add a5, a5, a7
	ld t6, 888(a3)
	ld a7, 920(a3)
	mul t0, a7, a4
	mulhu a2, a7, a4
	add t6, t6, t0
	sltu a6, t6, t0
	add t6, t6, a1
	sltu a7, t6, a1
	add a6, a6, a7
	add t6, t6, a5
	sltu a7, t6, a5
	add a6, a6, a7
	add a5, a2, a6
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	mul a7, a5, a4
	add t3, t3, a7
	sltu t0, t3, a7
	add t4, t4, t0
	sltu t0, t4, t0
	add t5, t5, t0
	sltu t0, t5, t0
	add t6, t6, t0
	sltu a5, t6, t0
	sd t3, 160(a3)
	sd t4, 168(a3)
	sd t5, 176(a3)
	sd t6, 184(a3)
	ret
	.option pop
