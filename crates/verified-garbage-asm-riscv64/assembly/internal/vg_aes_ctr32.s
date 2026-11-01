// The functions of `src/internal/vg_aes_ctr32.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ctr32:
	.option push
	.option arch, +m, +c
	addi a5, a5, 7
	andi a5, a5, -8
	sd s0, 320(a5)
	sd s1, 328(a5)
	sd s2, 336(a5)
	sd s3, 344(a5)
	sd s4, 352(a5)
	sd s5, 360(a5)
	sd s6, 368(a5)
	sd s7, 376(a5)
	sd s8, 384(a5)
	sd s9, 392(a5)
	sd s10, 400(a5)
	sd s11, 408(a5)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 416(a5)
	lui t0, 16
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -256
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 424(a5)
	lui t0, 4080
	addiw t0, t0, 255
	slli t0, t0, 32
	lui t1, 4080
	addiw t1, t1, 255
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 432(a5)
	lui t0, 349525
	addiw t0, t0, 1365
	slli t0, t0, 32
	lui t1, 349525
	addiw t1, t1, 1365
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 440(a5)
	lui t0, 209715
	addiw t0, t0, 819
	slli t0, t0, 32
	lui t1, 209715
	addiw t1, t1, 819
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 448(a5)
	lui t0, 61681
	addiw t0, t0, -241
	slli t0, t0, 32
	lui t1, 61681
	addiw t1, t1, -241
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 456(a5)
	lui t0, 16
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 512(a5)
	lui t0, 65520
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 65520
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 520(a5)
	lui t0, 983040
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 983040
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 528(a5)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 536(a5)
	lui t0, 4080
	addiw t0, t0, 255
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 544(a5)
	lui t0, 1044496
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 552(a5)
	lui t0, 16
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 560(a5)
	lui t0, 1048320
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1048320
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 568(a5)
	lui t0, 240
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 240
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 576(a5)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 584(a5)
	lui t0, 4080
	addiw t0, t0, 255
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 592(a5)
	lui t0, 1044496
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	slli t1, t1, 32
	srli t1, t1, 32
	or t0, t0, t1
	sd t0, 600(a5)
	lbu t0, 0(a2)
	lbu t1, 1(a2)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 2(a2)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 3(a2)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 4(a2)
	lbu t1, 5(a2)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 6(a2)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 7(a2)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	sd t0, 472(a5)
	lbu t0, 8(a2)
	lbu t1, 9(a2)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 10(a2)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 11(a2)
	slli t1, t1, 24
	or t0, t0, t1
	sd t0, 480(a5)
	lbu t0, 12(a2)
	slli t0, t0, 24
	lbu t1, 13(a2)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 14(a2)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 15(a2)
	or t0, t0, t1
	sd t0, 488(a5)
	add t0, t0, a4
	srli t1, t0, 24
	sb t1, 12(a2)
	srli t1, t0, 16
	sb t1, 13(a2)
	srli t1, t0, 8
	sb t1, 14(a2)
	srli t1, t0, 0
	sb t1, 15(a2)
	slli t0, a1, 4
	add a0, a0, t0
	addi a2, a5, 1920
	addi a1, a1, 1
20:
	lbu s0, 0(a0)
	lbu t0, 1(a0)
	slli t0, t0, 8
	or s0, s0, t0
	lbu t0, 2(a0)
	slli t0, t0, 16
	or s0, s0, t0
	lbu t0, 3(a0)
	slli t0, t0, 24
	or s0, s0, t0
	lbu t1, 4(a0)
	lbu t0, 5(a0)
	slli t0, t0, 8
	or t1, t1, t0
	lbu t0, 6(a0)
	slli t0, t0, 16
	or t1, t1, t0
	lbu t0, 7(a0)
	slli t0, t0, 24
	or t1, t1, t0
	slli t1, t1, 32
	or s0, s0, t1
	lbu s4, 8(a0)
	lbu t0, 9(a0)
	slli t0, t0, 8
	or s4, s4, t0
	lbu t0, 10(a0)
	slli t0, t0, 16
	or s4, s4, t0
	lbu t0, 11(a0)
	slli t0, t0, 24
	or s4, s4, t0
	lbu t1, 12(a0)
	lbu t0, 13(a0)
	slli t0, t0, 8
	or t1, t1, t0
	lbu t0, 14(a0)
	slli t0, t0, 16
	or t1, t1, t0
	lbu t0, 15(a0)
	slli t0, t0, 24
	or t1, t1, t0
	slli t1, t1, 32
	or s4, s4, t1
	addi s1, s0, 0
	addi s2, s0, 0
	addi s3, s0, 0
	addi s5, s4, 0
	addi s6, s4, 0
	addi s7, s4, 0
	ld t3, 416(a5)
	ld t4, 424(a5)
	ld t5, 432(a5)
	ld t6, 440(a5)
	ld a6, 448(a5)
	ld a7, 456(a5)
	srli t0, s0, 16
	xor t0, t0, s0
	and t0, t0, t3
	xor s0, s0, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s1
	and t0, t0, t3
	xor s1, s1, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s2
	and t0, t0, t3
	xor s2, s2, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s3
	and t0, t0, t3
	xor s3, s3, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s4, 16
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 16
	xor s4, s4, t0
	srli t0, s5, 16
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 16
	xor s5, s5, t0
	srli t0, s6, 16
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 16
	xor s6, s6, t0
	srli t0, s7, 16
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 16
	xor s7, s7, t0
	srli t0, s0, 8
	xor t0, t0, s0
	and t0, t0, t4
	xor s0, s0, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s1
	and t0, t0, t4
	xor s1, s1, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s2
	and t0, t0, t4
	xor s2, s2, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s3
	and t0, t0, t4
	xor s3, s3, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s4, 8
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 8
	xor s4, s4, t0
	srli t0, s5, 8
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 8
	xor s5, s5, t0
	srli t0, s6, 8
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 8
	xor s6, s6, t0
	srli t0, s7, 8
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 8
	xor s7, s7, t0
	srli t0, s0, 8
	xor t0, t0, s4
	and t0, t0, t5
	xor s4, s4, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s5
	and t0, t0, t5
	xor s5, s5, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s6
	and t0, t0, t5
	xor s6, s6, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s7
	and t0, t0, t5
	xor s7, s7, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, a7
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, a7
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, a7
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, a7
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	sd s0, 0(a2)
	sd s1, 8(a2)
	sd s2, 16(a2)
	sd s3, 24(a2)
	sd s4, 32(a2)
	sd s5, 40(a2)
	sd s6, 48(a2)
	sd s7, 56(a2)
	addi a0, a0, -16
	addi a2, a2, -64
	addi a1, a1, -1
	bnez a1, 20b
	addi a0, a2, 64
	beqz a4, 21f
23:
	ld s0, 472(a5)
	ld t0, 488(a5)
	addi t0, t0, 0
	srli t1, t0, 24
	sb t1, 484(a5)
	srli t1, t0, 16
	sb t1, 485(a5)
	srli t1, t0, 8
	sb t1, 486(a5)
	srli t1, t0, 0
	sb t1, 487(a5)
	ld s4, 480(a5)
	ld s1, 472(a5)
	ld t0, 488(a5)
	addi t0, t0, 1
	srli t1, t0, 24
	sb t1, 484(a5)
	srli t1, t0, 16
	sb t1, 485(a5)
	srli t1, t0, 8
	sb t1, 486(a5)
	srli t1, t0, 0
	sb t1, 487(a5)
	ld s5, 480(a5)
	ld s2, 472(a5)
	ld t0, 488(a5)
	addi t0, t0, 2
	srli t1, t0, 24
	sb t1, 484(a5)
	srli t1, t0, 16
	sb t1, 485(a5)
	srli t1, t0, 8
	sb t1, 486(a5)
	srli t1, t0, 0
	sb t1, 487(a5)
	ld s6, 480(a5)
	ld s3, 472(a5)
	ld t0, 488(a5)
	addi t0, t0, 3
	srli t1, t0, 24
	sb t1, 484(a5)
	srli t1, t0, 16
	sb t1, 485(a5)
	srli t1, t0, 8
	sb t1, 486(a5)
	srli t1, t0, 0
	sb t1, 487(a5)
	ld s7, 480(a5)
	ld t0, 488(a5)
	addi t0, t0, 4
	sd t0, 488(a5)
	ld t3, 416(a5)
	ld t4, 424(a5)
	ld t5, 432(a5)
	ld t6, 440(a5)
	ld a6, 448(a5)
	ld a7, 456(a5)
	srli t0, s0, 16
	xor t0, t0, s0
	and t0, t0, t3
	xor s0, s0, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s1
	and t0, t0, t3
	xor s1, s1, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s2
	and t0, t0, t3
	xor s2, s2, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s3
	and t0, t0, t3
	xor s3, s3, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s4, 16
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 16
	xor s4, s4, t0
	srli t0, s5, 16
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 16
	xor s5, s5, t0
	srli t0, s6, 16
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 16
	xor s6, s6, t0
	srli t0, s7, 16
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 16
	xor s7, s7, t0
	srli t0, s0, 8
	xor t0, t0, s0
	and t0, t0, t4
	xor s0, s0, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s1
	and t0, t0, t4
	xor s1, s1, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s2
	and t0, t0, t4
	xor s2, s2, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s3
	and t0, t0, t4
	xor s3, s3, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s4, 8
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 8
	xor s4, s4, t0
	srli t0, s5, 8
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 8
	xor s5, s5, t0
	srli t0, s6, 8
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 8
	xor s6, s6, t0
	srli t0, s7, 8
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 8
	xor s7, s7, t0
	srli t0, s0, 8
	xor t0, t0, s4
	and t0, t0, t5
	xor s4, s4, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s5
	and t0, t0, t5
	xor s5, s5, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s6
	and t0, t0, t5
	xor s6, s6, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s7
	and t0, t0, t5
	xor s7, s7, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, a7
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, a7
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, a7
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, a7
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	addi a1, a0, 0
	ld t0, 0(a1)
	xor s0, s0, t0
	ld t0, 8(a1)
	xor s1, s1, t0
	ld t0, 16(a1)
	xor s2, s2, t0
	ld t0, 24(a1)
	xor s3, s3, t0
	ld t0, 32(a1)
	xor s4, s4, t0
	ld t0, 40(a1)
	xor s5, s5, t0
	ld t0, 48(a1)
	xor s6, s6, t0
	ld t0, 56(a1)
	xor s7, s7, t0
24:
	addi a1, a1, 64
	xor t0, s4, s2
	xor t1, s7, s1
	xor t2, s7, s4
	xor t3, s7, s2
	xor s5, s6, s5
	xor t4, s5, s0
	xor s4, t4, s4
	xor t5, t1, t0
	xor t6, t4, s7
	xor s1, t4, s1
	xor a6, s1, t3
	xor s3, s3, t5
	xor s2, s3, s2
	xor s3, s3, s6
	xor s6, s2, s0
	xor a7, s2, s5
	xor s8, s3, t2
	xor s9, s0, s8
	xor s10, a7, s8
	xor s11, a7, t3
	xor s5, s5, s8
	sd s11, 0(a5)
	xor s11, t1, s5
	xor s7, s7, s5
	sd s7, 8(a5)
	and s7, t5, s2
	sd t5, 16(a5)
	and t5, a6, s6
	xor t5, t5, s7
	sd a6, 24(a5)
	and a6, s4, s0
	xor a6, a6, s7
	and s7, t1, s5
	sd t1, 32(a5)
	and t1, s1, t4
	xor t1, t1, s7
	sd s1, 40(a5)
	and s1, t6, s9
	xor s1, s1, s7
	and s7, t2, s8
	sd t2, 48(a5)
	and t2, t0, s10
	xor t2, t2, s7
	sd t0, 56(a5)
	and t0, t3, a7
	xor t0, t0, s7
	xor t5, t5, t2
	xor a6, a6, t0
	xor t1, t1, t2
	xor s1, s1, t0
	xor t5, t5, s3
	ld s3, 0(a5)
	xor a6, a6, s3
	xor t1, t1, s11
	ld s11, 8(a5)
	xor s1, s1, s11
	xor s11, t5, a6
	and t5, t5, t1
	xor s3, s1, t5
	and t0, s11, s3
	xor t0, t0, a6
	xor t2, t1, s1
	xor a6, a6, t5
	and a6, a6, t2
	xor a6, a6, s1
	xor t1, t1, a6
	xor t2, s3, a6
	and s1, s1, t2
	xor t1, s1, t1
	xor s3, s3, s1
	and s3, t0, s3
	xor s11, s11, s3
	xor s3, s11, t1
	xor s1, t0, a6
	xor t2, t0, s11
	xor t5, a6, t1
	xor s7, s1, s3
	and s2, t5, s2
	and s6, t1, s6
	and s0, a6, s0
	and s5, t2, s5
	and t4, s11, t4
	and s9, t0, s9
	and s8, s1, s8
	and s10, s7, s10
	and a7, s3, a7
	sd s6, 8(a5)
	ld s6, 16(a5)
	and t5, t5, s6
	ld s6, 24(a5)
	and t1, t1, s6
	and a6, a6, s4
	ld s4, 32(a5)
	and t2, t2, s4
	ld s4, 40(a5)
	and s11, s11, s4
	and t0, t0, t6
	ld t6, 48(a5)
	and s1, s1, t6
	ld t6, 56(a5)
	and s7, s7, t6
	and s3, s3, t3
	xor s1, s1, s7
	xor a6, t1, a6
	xor s11, s9, s11
	xor t5, t5, t1
	xor t1, s0, t2
	xor s0, s0, s9
	xor a7, s10, a7
	xor s2, s2, s5
	xor s8, s8, s10
	xor s7, s7, s3
	xor t2, t2, s11
	xor t1, t1, s2
	xor s3, t4, s1
	xor s5, s5, s8
	xor s1, s1, t1
	xor t0, t0, t1
	xor a7, a7, s3
	xor t5, t5, s3
	xor t4, t4, s5
	xor t0, t0, a7
	ld s3, 8(a5)
	xor s3, s3, t5
	xor s5, s5, t5
	xor t2, t2, a7
	xori t2, t2, -1
	xor s11, s11, s1
	xori s11, s11, -1
	xor s1, t4, t0
	xor s4, s2, s3
	xor s3, s0, s3
	xor s2, a6, t0
	xor s6, t4, s4
	xori s6, s6, -1
	xor s7, s7, s1
	xori s7, s7, -1
	sd s7, 8(a5)
	addi s7, s5, 0
	ld s5, 8(a5)
	addi s1, t2, 0
	addi s0, s11, 0
	ld t3, 512(a5)
	ld t4, 520(a5)
	ld t5, 528(a5)
	ld t6, 536(a5)
	ld a6, 544(a5)
	ld a7, 552(a5)
	srli t0, s0, 4
	and t0, t0, t4
	slli t1, s0, 12
	and t1, t1, t5
	and s0, s0, t3
	xor s0, s0, t0
	xor s0, s0, t1
	srli t0, s0, 8
	and t0, t0, a6
	slli t1, s0, 8
	and t1, t1, a7
	and s0, s0, t6
	xor s0, s0, t0
	xor s0, s0, t1
	srli t0, s1, 4
	and t0, t0, t4
	slli t1, s1, 12
	and t1, t1, t5
	and s1, s1, t3
	xor s1, s1, t0
	xor s1, s1, t1
	srli t0, s1, 8
	and t0, t0, a6
	slli t1, s1, 8
	and t1, t1, a7
	and s1, s1, t6
	xor s1, s1, t0
	xor s1, s1, t1
	srli t0, s2, 4
	and t0, t0, t4
	slli t1, s2, 12
	and t1, t1, t5
	and s2, s2, t3
	xor s2, s2, t0
	xor s2, s2, t1
	srli t0, s2, 8
	and t0, t0, a6
	slli t1, s2, 8
	and t1, t1, a7
	and s2, s2, t6
	xor s2, s2, t0
	xor s2, s2, t1
	srli t0, s3, 4
	and t0, t0, t4
	slli t1, s3, 12
	and t1, t1, t5
	and s3, s3, t3
	xor s3, s3, t0
	xor s3, s3, t1
	srli t0, s3, 8
	and t0, t0, a6
	slli t1, s3, 8
	and t1, t1, a7
	and s3, s3, t6
	xor s3, s3, t0
	xor s3, s3, t1
	srli t0, s4, 4
	and t0, t0, t4
	slli t1, s4, 12
	and t1, t1, t5
	and s4, s4, t3
	xor s4, s4, t0
	xor s4, s4, t1
	srli t0, s4, 8
	and t0, t0, a6
	slli t1, s4, 8
	and t1, t1, a7
	and s4, s4, t6
	xor s4, s4, t0
	xor s4, s4, t1
	srli t0, s5, 4
	and t0, t0, t4
	slli t1, s5, 12
	and t1, t1, t5
	and s5, s5, t3
	xor s5, s5, t0
	xor s5, s5, t1
	srli t0, s5, 8
	and t0, t0, a6
	slli t1, s5, 8
	and t1, t1, a7
	and s5, s5, t6
	xor s5, s5, t0
	xor s5, s5, t1
	srli t0, s6, 4
	and t0, t0, t4
	slli t1, s6, 12
	and t1, t1, t5
	and s6, s6, t3
	xor s6, s6, t0
	xor s6, s6, t1
	srli t0, s6, 8
	and t0, t0, a6
	slli t1, s6, 8
	and t1, t1, a7
	and s6, s6, t6
	xor s6, s6, t0
	xor s6, s6, t1
	srli t0, s7, 4
	and t0, t0, t4
	slli t1, s7, 12
	and t1, t1, t5
	and s7, s7, t3
	xor s7, s7, t0
	xor s7, s7, t1
	srli t0, s7, 8
	and t0, t0, a6
	slli t1, s7, 8
	and t1, t1, a7
	and s7, s7, t6
	xor s7, s7, t0
	xor s7, s7, t1
	srli t4, s7, 16
	slli t3, s7, 48
	xor t3, t3, t4
	xor t3, t3, s7
	srli t4, s0, 16
	slli t0, s0, 48
	xor t0, t0, t4
	xor s0, s0, t0
	xor t0, t0, t3
	srli t4, s0, 32
	slli t2, s0, 32
	xor t2, t2, t4
	xor t0, t0, t2
	srli t4, s1, 16
	slli t1, s1, 48
	xor t1, t1, t4
	xor s1, s1, t1
	xor t1, t1, s0
	xor t1, t1, t3
	srli t4, s1, 32
	slli t2, s1, 32
	xor t2, t2, t4
	xor t1, t1, t2
	srli t4, s2, 16
	slli s0, s2, 48
	xor s0, s0, t4
	xor s2, s2, s0
	xor s0, s0, s1
	srli t4, s2, 32
	slli t2, s2, 32
	xor t2, t2, t4
	xor s0, s0, t2
	srli t4, s3, 16
	slli s1, s3, 48
	xor s1, s1, t4
	xor s3, s3, s1
	xor s1, s1, s2
	xor s1, s1, t3
	srli t4, s3, 32
	slli t2, s3, 32
	xor t2, t2, t4
	xor s1, s1, t2
	srli t4, s4, 16
	slli s2, s4, 48
	xor s2, s2, t4
	xor s4, s4, s2
	xor s2, s2, s3
	xor s2, s2, t3
	srli t4, s4, 32
	slli t2, s4, 32
	xor t2, t2, t4
	xor s2, s2, t2
	srli t4, s5, 16
	slli s3, s5, 48
	xor s3, s3, t4
	xor s5, s5, s3
	xor s3, s3, s4
	srli t4, s5, 32
	slli t2, s5, 32
	xor t2, t2, t4
	xor s3, s3, t2
	srli t4, s6, 16
	slli s4, s6, 48
	xor s4, s4, t4
	xor s6, s6, s4
	xor s4, s4, s5
	srli t4, s6, 32
	slli t2, s6, 32
	xor t2, t2, t4
	xor s4, s4, t2
	srli t4, s7, 16
	slli s5, s7, 48
	xor s5, s5, t4
	xor s7, s7, s5
	xor s5, s5, s6
	srli t4, s7, 32
	slli t2, s7, 32
	xor t2, t2, t4
	xor s5, s5, t2
	addi s7, s5, 0
	addi s6, s4, 0
	addi s5, s3, 0
	addi s4, s2, 0
	addi s3, s1, 0
	addi s2, s0, 0
	addi s1, t1, 0
	addi s0, t0, 0
	ld t0, 0(a1)
	xor s0, s0, t0
	ld t0, 8(a1)
	xor s1, s1, t0
	ld t0, 16(a1)
	xor s2, s2, t0
	ld t0, 24(a1)
	xor s3, s3, t0
	ld t0, 32(a1)
	xor s4, s4, t0
	ld t0, 40(a1)
	xor s5, s5, t0
	ld t0, 48(a1)
	xor s6, s6, t0
	ld t0, 56(a1)
	xor s7, s7, t0
	sub t0, a1, a5
	addi t0, t0, -1856
	bnez t0, 24b
	addi a1, a1, 64
	xor t0, s4, s2
	xor t1, s7, s1
	xor t2, s7, s4
	xor t3, s7, s2
	xor s5, s6, s5
	xor t4, s5, s0
	xor s4, t4, s4
	xor t5, t1, t0
	xor t6, t4, s7
	xor s1, t4, s1
	xor a6, s1, t3
	xor s3, s3, t5
	xor s2, s3, s2
	xor s3, s3, s6
	xor s6, s2, s0
	xor a7, s2, s5
	xor s8, s3, t2
	xor s9, s0, s8
	xor s10, a7, s8
	xor s11, a7, t3
	xor s5, s5, s8
	sd s11, 0(a5)
	xor s11, t1, s5
	xor s7, s7, s5
	sd s7, 8(a5)
	and s7, t5, s2
	sd t5, 16(a5)
	and t5, a6, s6
	xor t5, t5, s7
	sd a6, 24(a5)
	and a6, s4, s0
	xor a6, a6, s7
	and s7, t1, s5
	sd t1, 32(a5)
	and t1, s1, t4
	xor t1, t1, s7
	sd s1, 40(a5)
	and s1, t6, s9
	xor s1, s1, s7
	and s7, t2, s8
	sd t2, 48(a5)
	and t2, t0, s10
	xor t2, t2, s7
	sd t0, 56(a5)
	and t0, t3, a7
	xor t0, t0, s7
	xor t5, t5, t2
	xor a6, a6, t0
	xor t1, t1, t2
	xor s1, s1, t0
	xor t5, t5, s3
	ld s3, 0(a5)
	xor a6, a6, s3
	xor t1, t1, s11
	ld s11, 8(a5)
	xor s1, s1, s11
	xor s11, t5, a6
	and t5, t5, t1
	xor s3, s1, t5
	and t0, s11, s3
	xor t0, t0, a6
	xor t2, t1, s1
	xor a6, a6, t5
	and a6, a6, t2
	xor a6, a6, s1
	xor t1, t1, a6
	xor t2, s3, a6
	and s1, s1, t2
	xor t1, s1, t1
	xor s3, s3, s1
	and s3, t0, s3
	xor s11, s11, s3
	xor s3, s11, t1
	xor s1, t0, a6
	xor t2, t0, s11
	xor t5, a6, t1
	xor s7, s1, s3
	and s2, t5, s2
	and s6, t1, s6
	and s0, a6, s0
	and s5, t2, s5
	and t4, s11, t4
	and s9, t0, s9
	and s8, s1, s8
	and s10, s7, s10
	and a7, s3, a7
	sd s6, 8(a5)
	ld s6, 16(a5)
	and t5, t5, s6
	ld s6, 24(a5)
	and t1, t1, s6
	and a6, a6, s4
	ld s4, 32(a5)
	and t2, t2, s4
	ld s4, 40(a5)
	and s11, s11, s4
	and t0, t0, t6
	ld t6, 48(a5)
	and s1, s1, t6
	ld t6, 56(a5)
	and s7, s7, t6
	and s3, s3, t3
	xor s1, s1, s7
	xor a6, t1, a6
	xor s11, s9, s11
	xor t5, t5, t1
	xor t1, s0, t2
	xor s0, s0, s9
	xor a7, s10, a7
	xor s2, s2, s5
	xor s8, s8, s10
	xor s7, s7, s3
	xor t2, t2, s11
	xor t1, t1, s2
	xor s3, t4, s1
	xor s5, s5, s8
	xor s1, s1, t1
	xor t0, t0, t1
	xor a7, a7, s3
	xor t5, t5, s3
	xor t4, t4, s5
	xor t0, t0, a7
	ld s3, 8(a5)
	xor s3, s3, t5
	xor s5, s5, t5
	xor t2, t2, a7
	xori t2, t2, -1
	xor s11, s11, s1
	xori s11, s11, -1
	xor s1, t4, t0
	xor s4, s2, s3
	xor s3, s0, s3
	xor s2, a6, t0
	xor s6, t4, s4
	xori s6, s6, -1
	xor s7, s7, s1
	xori s7, s7, -1
	sd s7, 8(a5)
	addi s7, s5, 0
	ld s5, 8(a5)
	addi s1, t2, 0
	addi s0, s11, 0
	ld t3, 512(a5)
	ld t4, 520(a5)
	ld t5, 528(a5)
	ld t6, 536(a5)
	ld a6, 544(a5)
	ld a7, 552(a5)
	srli t0, s0, 4
	and t0, t0, t4
	slli t1, s0, 12
	and t1, t1, t5
	and s0, s0, t3
	xor s0, s0, t0
	xor s0, s0, t1
	srli t0, s0, 8
	and t0, t0, a6
	slli t1, s0, 8
	and t1, t1, a7
	and s0, s0, t6
	xor s0, s0, t0
	xor s0, s0, t1
	srli t0, s1, 4
	and t0, t0, t4
	slli t1, s1, 12
	and t1, t1, t5
	and s1, s1, t3
	xor s1, s1, t0
	xor s1, s1, t1
	srli t0, s1, 8
	and t0, t0, a6
	slli t1, s1, 8
	and t1, t1, a7
	and s1, s1, t6
	xor s1, s1, t0
	xor s1, s1, t1
	srli t0, s2, 4
	and t0, t0, t4
	slli t1, s2, 12
	and t1, t1, t5
	and s2, s2, t3
	xor s2, s2, t0
	xor s2, s2, t1
	srli t0, s2, 8
	and t0, t0, a6
	slli t1, s2, 8
	and t1, t1, a7
	and s2, s2, t6
	xor s2, s2, t0
	xor s2, s2, t1
	srli t0, s3, 4
	and t0, t0, t4
	slli t1, s3, 12
	and t1, t1, t5
	and s3, s3, t3
	xor s3, s3, t0
	xor s3, s3, t1
	srli t0, s3, 8
	and t0, t0, a6
	slli t1, s3, 8
	and t1, t1, a7
	and s3, s3, t6
	xor s3, s3, t0
	xor s3, s3, t1
	srli t0, s4, 4
	and t0, t0, t4
	slli t1, s4, 12
	and t1, t1, t5
	and s4, s4, t3
	xor s4, s4, t0
	xor s4, s4, t1
	srli t0, s4, 8
	and t0, t0, a6
	slli t1, s4, 8
	and t1, t1, a7
	and s4, s4, t6
	xor s4, s4, t0
	xor s4, s4, t1
	srli t0, s5, 4
	and t0, t0, t4
	slli t1, s5, 12
	and t1, t1, t5
	and s5, s5, t3
	xor s5, s5, t0
	xor s5, s5, t1
	srli t0, s5, 8
	and t0, t0, a6
	slli t1, s5, 8
	and t1, t1, a7
	and s5, s5, t6
	xor s5, s5, t0
	xor s5, s5, t1
	srli t0, s6, 4
	and t0, t0, t4
	slli t1, s6, 12
	and t1, t1, t5
	and s6, s6, t3
	xor s6, s6, t0
	xor s6, s6, t1
	srli t0, s6, 8
	and t0, t0, a6
	slli t1, s6, 8
	and t1, t1, a7
	and s6, s6, t6
	xor s6, s6, t0
	xor s6, s6, t1
	srli t0, s7, 4
	and t0, t0, t4
	slli t1, s7, 12
	and t1, t1, t5
	and s7, s7, t3
	xor s7, s7, t0
	xor s7, s7, t1
	srli t0, s7, 8
	and t0, t0, a6
	slli t1, s7, 8
	and t1, t1, a7
	and s7, s7, t6
	xor s7, s7, t0
	xor s7, s7, t1
	ld t0, 0(a1)
	xor s0, s0, t0
	ld t0, 8(a1)
	xor s1, s1, t0
	ld t0, 16(a1)
	xor s2, s2, t0
	ld t0, 24(a1)
	xor s3, s3, t0
	ld t0, 32(a1)
	xor s4, s4, t0
	ld t0, 40(a1)
	xor s5, s5, t0
	ld t0, 48(a1)
	xor s6, s6, t0
	ld t0, 56(a1)
	xor s7, s7, t0
	ld t3, 416(a5)
	ld t4, 424(a5)
	ld t5, 432(a5)
	ld t6, 440(a5)
	ld a6, 448(a5)
	ld a7, 456(a5)
	srli t0, s0, 1
	xor t0, t0, s1
	and t0, t0, t6
	xor s1, s1, t0
	slli t0, t0, 1
	xor s0, s0, t0
	srli t0, s2, 1
	xor t0, t0, s3
	and t0, t0, t6
	xor s3, s3, t0
	slli t0, t0, 1
	xor s2, s2, t0
	srli t0, s4, 1
	xor t0, t0, s5
	and t0, t0, t6
	xor s5, s5, t0
	slli t0, t0, 1
	xor s4, s4, t0
	srli t0, s6, 1
	xor t0, t0, s7
	and t0, t0, t6
	xor s7, s7, t0
	slli t0, t0, 1
	xor s6, s6, t0
	srli t0, s0, 2
	xor t0, t0, s2
	and t0, t0, a6
	xor s2, s2, t0
	slli t0, t0, 2
	xor s0, s0, t0
	srli t0, s1, 2
	xor t0, t0, s3
	and t0, t0, a6
	xor s3, s3, t0
	slli t0, t0, 2
	xor s1, s1, t0
	srli t0, s4, 2
	xor t0, t0, s6
	and t0, t0, a6
	xor s6, s6, t0
	slli t0, t0, 2
	xor s4, s4, t0
	srli t0, s5, 2
	xor t0, t0, s7
	and t0, t0, a6
	xor s7, s7, t0
	slli t0, t0, 2
	xor s5, s5, t0
	srli t0, s0, 4
	xor t0, t0, s4
	and t0, t0, a7
	xor s4, s4, t0
	slli t0, t0, 4
	xor s0, s0, t0
	srli t0, s1, 4
	xor t0, t0, s5
	and t0, t0, a7
	xor s5, s5, t0
	slli t0, t0, 4
	xor s1, s1, t0
	srli t0, s2, 4
	xor t0, t0, s6
	and t0, t0, a7
	xor s6, s6, t0
	slli t0, t0, 4
	xor s2, s2, t0
	srli t0, s3, 4
	xor t0, t0, s7
	and t0, t0, a7
	xor s7, s7, t0
	slli t0, t0, 4
	xor s3, s3, t0
	srli t0, s0, 8
	xor t0, t0, s4
	and t0, t0, t5
	xor s4, s4, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s5
	and t0, t0, t5
	xor s5, s5, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s6
	and t0, t0, t5
	xor s6, s6, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s7
	and t0, t0, t5
	xor s7, s7, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s0, 8
	xor t0, t0, s0
	and t0, t0, t4
	xor s0, s0, t0
	slli t0, t0, 8
	xor s0, s0, t0
	srli t0, s1, 8
	xor t0, t0, s1
	and t0, t0, t4
	xor s1, s1, t0
	slli t0, t0, 8
	xor s1, s1, t0
	srli t0, s2, 8
	xor t0, t0, s2
	and t0, t0, t4
	xor s2, s2, t0
	slli t0, t0, 8
	xor s2, s2, t0
	srli t0, s3, 8
	xor t0, t0, s3
	and t0, t0, t4
	xor s3, s3, t0
	slli t0, t0, 8
	xor s3, s3, t0
	srli t0, s4, 8
	xor t0, t0, s4
	and t0, t0, t4
	xor s4, s4, t0
	slli t0, t0, 8
	xor s4, s4, t0
	srli t0, s5, 8
	xor t0, t0, s5
	and t0, t0, t4
	xor s5, s5, t0
	slli t0, t0, 8
	xor s5, s5, t0
	srli t0, s6, 8
	xor t0, t0, s6
	and t0, t0, t4
	xor s6, s6, t0
	slli t0, t0, 8
	xor s6, s6, t0
	srli t0, s7, 8
	xor t0, t0, s7
	and t0, t0, t4
	xor s7, s7, t0
	slli t0, t0, 8
	xor s7, s7, t0
	srli t0, s0, 16
	xor t0, t0, s0
	and t0, t0, t3
	xor s0, s0, t0
	slli t0, t0, 16
	xor s0, s0, t0
	srli t0, s1, 16
	xor t0, t0, s1
	and t0, t0, t3
	xor s1, s1, t0
	slli t0, t0, 16
	xor s1, s1, t0
	srli t0, s2, 16
	xor t0, t0, s2
	and t0, t0, t3
	xor s2, s2, t0
	slli t0, t0, 16
	xor s2, s2, t0
	srli t0, s3, 16
	xor t0, t0, s3
	and t0, t0, t3
	xor s3, s3, t0
	slli t0, t0, 16
	xor s3, s3, t0
	srli t0, s4, 16
	xor t0, t0, s4
	and t0, t0, t3
	xor s4, s4, t0
	slli t0, t0, 16
	xor s4, s4, t0
	srli t0, s5, 16
	xor t0, t0, s5
	and t0, t0, t3
	xor s5, s5, t0
	slli t0, t0, 16
	xor s5, s5, t0
	srli t0, s6, 16
	xor t0, t0, s6
	and t0, t0, t3
	xor s6, s6, t0
	slli t0, t0, 16
	xor s6, s6, t0
	srli t0, s7, 16
	xor t0, t0, s7
	and t0, t0, t3
	xor s7, s7, t0
	slli t0, t0, 16
	xor s7, s7, t0
	srli t0, a4, 2
	bnez t0, 25f
	lbu t0, 0(a3)
	lbu t1, 1(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 2(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 3(a3)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 4(a3)
	lbu t1, 5(a3)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 6(a3)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 7(a3)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	xor t0, t0, s0
	sb t0, 0(a3)
	srli t1, t0, 8
	sb t1, 1(a3)
	srli t1, t0, 16
	sb t1, 2(a3)
	srli t1, t0, 24
	sb t1, 3(a3)
	srli t2, t0, 32
	sb t2, 4(a3)
	srli t1, t2, 8
	sb t1, 5(a3)
	srli t1, t2, 16
	sb t1, 6(a3)
	srli t1, t2, 24
	sb t1, 7(a3)
	lbu t0, 8(a3)
	lbu t1, 9(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 10(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 11(a3)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 12(a3)
	lbu t1, 13(a3)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 14(a3)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 15(a3)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	xor t0, t0, s4
	sb t0, 8(a3)
	srli t1, t0, 8
	sb t1, 9(a3)
	srli t1, t0, 16
	sb t1, 10(a3)
	srli t1, t0, 24
	sb t1, 11(a3)
	srli t2, t0, 32
	sb t2, 12(a3)
	srli t1, t2, 8
	sb t1, 13(a3)
	srli t1, t2, 16
	sb t1, 14(a3)
	srli t1, t2, 24
	sb t1, 15(a3)
	addi t0, a4, -1
	bnez t0, 27f
	j 28f
27:
	lbu t0, 16(a3)
	lbu t1, 17(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 18(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 19(a3)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 20(a3)
	lbu t1, 21(a3)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 22(a3)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 23(a3)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	xor t0, t0, s1
	sb t0, 16(a3)
	srli t1, t0, 8
	sb t1, 17(a3)
	srli t1, t0, 16
	sb t1, 18(a3)
	srli t1, t0, 24
	sb t1, 19(a3)
	srli t2, t0, 32
	sb t2, 20(a3)
	srli t1, t2, 8
	sb t1, 21(a3)
	srli t1, t2, 16
	sb t1, 22(a3)
	srli t1, t2, 24
	sb t1, 23(a3)
	lbu t0, 24(a3)
	lbu t1, 25(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 26(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 27(a3)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 28(a3)
	lbu t1, 29(a3)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 30(a3)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 31(a3)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	xor t0, t0, s5
	sb t0, 24(a3)
	srli t1, t0, 8
	sb t1, 25(a3)
	srli t1, t0, 16
	sb t1, 26(a3)
	srli t1, t0, 24
	sb t1, 27(a3)
	srli t2, t0, 32
	sb t2, 28(a3)
	srli t1, t2, 8
	sb t1, 29(a3)
	srli t1, t2, 16
	sb t1, 30(a3)
	srli t1, t2, 24
	sb t1, 31(a3)
	addi t0, a4, -3
	beqz t0, 29f
	j 210f
29:
	lbu t0, 32(a3)
	lbu t1, 33(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 34(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 35(a3)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 36(a3)
	lbu t1, 37(a3)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 38(a3)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 39(a3)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	xor t0, t0, s2
	sb t0, 32(a3)
	srli t1, t0, 8
	sb t1, 33(a3)
	srli t1, t0, 16
	sb t1, 34(a3)
	srli t1, t0, 24
	sb t1, 35(a3)
	srli t2, t0, 32
	sb t2, 36(a3)
	srli t1, t2, 8
	sb t1, 37(a3)
	srli t1, t2, 16
	sb t1, 38(a3)
	srli t1, t2, 24
	sb t1, 39(a3)
	lbu t0, 40(a3)
	lbu t1, 41(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 42(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 43(a3)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 44(a3)
	lbu t1, 45(a3)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 46(a3)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 47(a3)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	xor t0, t0, s6
	sb t0, 40(a3)
	srli t1, t0, 8
	sb t1, 41(a3)
	srli t1, t0, 16
	sb t1, 42(a3)
	srli t1, t0, 24
	sb t1, 43(a3)
	srli t2, t0, 32
	sb t2, 44(a3)
	srli t1, t2, 8
	sb t1, 45(a3)
	srli t1, t2, 16
	sb t1, 46(a3)
	srli t1, t2, 24
	sb t1, 47(a3)
210:
28:
	addi a4, zero, 0
	j 26f
25:
	lbu t0, 0(a3)
	lbu t1, 1(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 2(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 3(a3)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 4(a3)
	lbu t1, 5(a3)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 6(a3)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 7(a3)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	xor t0, t0, s0
	sb t0, 0(a3)
	srli t1, t0, 8
	sb t1, 1(a3)
	srli t1, t0, 16
	sb t1, 2(a3)
	srli t1, t0, 24
	sb t1, 3(a3)
	srli t2, t0, 32
	sb t2, 4(a3)
	srli t1, t2, 8
	sb t1, 5(a3)
	srli t1, t2, 16
	sb t1, 6(a3)
	srli t1, t2, 24
	sb t1, 7(a3)
	lbu t0, 8(a3)
	lbu t1, 9(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 10(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 11(a3)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 12(a3)
	lbu t1, 13(a3)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 14(a3)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 15(a3)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	xor t0, t0, s4
	sb t0, 8(a3)
	srli t1, t0, 8
	sb t1, 9(a3)
	srli t1, t0, 16
	sb t1, 10(a3)
	srli t1, t0, 24
	sb t1, 11(a3)
	srli t2, t0, 32
	sb t2, 12(a3)
	srli t1, t2, 8
	sb t1, 13(a3)
	srli t1, t2, 16
	sb t1, 14(a3)
	srli t1, t2, 24
	sb t1, 15(a3)
	lbu t0, 16(a3)
	lbu t1, 17(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 18(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 19(a3)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 20(a3)
	lbu t1, 21(a3)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 22(a3)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 23(a3)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	xor t0, t0, s1
	sb t0, 16(a3)
	srli t1, t0, 8
	sb t1, 17(a3)
	srli t1, t0, 16
	sb t1, 18(a3)
	srli t1, t0, 24
	sb t1, 19(a3)
	srli t2, t0, 32
	sb t2, 20(a3)
	srli t1, t2, 8
	sb t1, 21(a3)
	srli t1, t2, 16
	sb t1, 22(a3)
	srli t1, t2, 24
	sb t1, 23(a3)
	lbu t0, 24(a3)
	lbu t1, 25(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 26(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 27(a3)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 28(a3)
	lbu t1, 29(a3)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 30(a3)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 31(a3)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	xor t0, t0, s5
	sb t0, 24(a3)
	srli t1, t0, 8
	sb t1, 25(a3)
	srli t1, t0, 16
	sb t1, 26(a3)
	srli t1, t0, 24
	sb t1, 27(a3)
	srli t2, t0, 32
	sb t2, 28(a3)
	srli t1, t2, 8
	sb t1, 29(a3)
	srli t1, t2, 16
	sb t1, 30(a3)
	srli t1, t2, 24
	sb t1, 31(a3)
	lbu t0, 32(a3)
	lbu t1, 33(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 34(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 35(a3)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 36(a3)
	lbu t1, 37(a3)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 38(a3)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 39(a3)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	xor t0, t0, s2
	sb t0, 32(a3)
	srli t1, t0, 8
	sb t1, 33(a3)
	srli t1, t0, 16
	sb t1, 34(a3)
	srli t1, t0, 24
	sb t1, 35(a3)
	srli t2, t0, 32
	sb t2, 36(a3)
	srli t1, t2, 8
	sb t1, 37(a3)
	srli t1, t2, 16
	sb t1, 38(a3)
	srli t1, t2, 24
	sb t1, 39(a3)
	lbu t0, 40(a3)
	lbu t1, 41(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 42(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 43(a3)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 44(a3)
	lbu t1, 45(a3)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 46(a3)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 47(a3)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	xor t0, t0, s6
	sb t0, 40(a3)
	srli t1, t0, 8
	sb t1, 41(a3)
	srli t1, t0, 16
	sb t1, 42(a3)
	srli t1, t0, 24
	sb t1, 43(a3)
	srli t2, t0, 32
	sb t2, 44(a3)
	srli t1, t2, 8
	sb t1, 45(a3)
	srli t1, t2, 16
	sb t1, 46(a3)
	srli t1, t2, 24
	sb t1, 47(a3)
	lbu t0, 48(a3)
	lbu t1, 49(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 50(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 51(a3)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 52(a3)
	lbu t1, 53(a3)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 54(a3)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 55(a3)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	xor t0, t0, s3
	sb t0, 48(a3)
	srli t1, t0, 8
	sb t1, 49(a3)
	srli t1, t0, 16
	sb t1, 50(a3)
	srli t1, t0, 24
	sb t1, 51(a3)
	srli t2, t0, 32
	sb t2, 52(a3)
	srli t1, t2, 8
	sb t1, 53(a3)
	srli t1, t2, 16
	sb t1, 54(a3)
	srli t1, t2, 24
	sb t1, 55(a3)
	lbu t0, 56(a3)
	lbu t1, 57(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 58(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 59(a3)
	slli t1, t1, 24
	or t0, t0, t1
	lbu t2, 60(a3)
	lbu t1, 61(a3)
	slli t1, t1, 8
	or t2, t2, t1
	lbu t1, 62(a3)
	slli t1, t1, 16
	or t2, t2, t1
	lbu t1, 63(a3)
	slli t1, t1, 24
	or t2, t2, t1
	slli t2, t2, 32
	or t0, t0, t2
	xor t0, t0, s7
	sb t0, 56(a3)
	srli t1, t0, 8
	sb t1, 57(a3)
	srli t1, t0, 16
	sb t1, 58(a3)
	srli t1, t0, 24
	sb t1, 59(a3)
	srli t2, t0, 32
	sb t2, 60(a3)
	srli t1, t2, 8
	sb t1, 61(a3)
	srli t1, t2, 16
	sb t1, 62(a3)
	srli t1, t2, 24
	sb t1, 63(a3)
	addi a3, a3, 64
	addi a4, a4, -4
26:
	bnez a4, 23b
	j 22f
21:
22:
	ld s0, 320(a5)
	ld s1, 328(a5)
	ld s2, 336(a5)
	ld s3, 344(a5)
	ld s4, 352(a5)
	ld s5, 360(a5)
	ld s6, 368(a5)
	ld s7, 376(a5)
	ld s8, 384(a5)
	ld s9, 392(a5)
	ld s10, 400(a5)
	ld s11, 408(a5)
	ret
	.option pop
