// The functions of `src/internal/vg_brainpoolp512r1_check_point.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp512r1_check_point:
	.option push
	.option arch, +m, +c
	sd s0, 192(a0)
	sd ra, 200(a0)
	addi s0, a0, 0
	addi t5, zero, 0
	addi t3, s0, 2047
	ld t3, 129(t3)
	ld t4, 64(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 137(t3)
	ld t4, 72(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 145(t3)
	ld t4, 80(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 153(t3)
	ld t4, 88(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 161(t3)
	ld t4, 96(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 169(t3)
	ld t4, 104(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 177(t3)
	ld t4, 112(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 185(t3)
	ld t4, 120(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t6, zero, 0
	sub a7, t6, t5
	addi t0, s0, 2047
	ld t0, 833(t0)
	and t0, t0, a7
	addi s0, s0, 2047
	sd t0, 833(s0)
	addi s0, s0, -2047
	addi t5, zero, 0
	addi t3, s0, 2047
	ld t3, 321(t3)
	ld t4, 64(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 329(t3)
	ld t4, 72(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 337(t3)
	ld t4, 80(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 345(t3)
	ld t4, 88(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 353(t3)
	ld t4, 96(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 361(t3)
	ld t4, 104(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 369(t3)
	ld t4, 112(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 377(t3)
	ld t4, 120(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t6, zero, 0
	sub a7, t6, t5
	addi t0, s0, 2047
	ld t0, 833(t0)
	and t0, t0, a7
	addi s0, s0, 2047
	sd t0, 833(s0)
	addi s0, s0, -2047
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 193
	addi a2, zero, 2047
	addi a2, a2, 129
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 257
	addi a2, zero, 2047
	addi a2, a2, 321
	addi a3, zero, 2047
	addi a3, a3, 513
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 385
	addi a2, zero, 2047
	addi a2, a2, 257
	addi a3, zero, 2047
	addi a3, a3, 257
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 641
	addi a2, zero, 2047
	addi a2, a2, 193
	addi a3, zero, 2047
	addi a3, a3, 193
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 705
	addi a2, zero, 2047
	addi a2, a2, 641
	addi a3, zero, 2047
	addi a3, a3, 193
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 641
	addi a2, zero, 448
	addi a3, zero, 2047
	addi a3, a3, 193
	call {vg_brainpoolp512r1_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 449
	addi a2, zero, 2047
	addi a2, a2, 705
	addi a3, zero, 2047
	addi a3, a3, 641
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 705
	addi a2, zero, 2047
	addi a2, a2, 449
	addi a3, zero, 2047
	addi a3, a3, 577
	call {vg_brainpoolp512r1_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 641
	addi a2, zero, 2047
	addi a2, a2, 385
	addi a3, zero, 2047
	addi a3, a3, 705
	call {vg_brainpoolp512r1_sub_mod_p}
	addi t3, zero, 0
	addi t4, s0, 2047
	ld t4, 641(t4)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 649(t4)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 657(t4)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 665(t4)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 673(t4)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 681(t4)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 689(t4)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 697(t4)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	addi t0, s0, 2047
	ld t0, 833(t0)
	and t0, t0, a7
	addi s0, s0, 2047
	sd t0, 833(s0)
	addi s0, s0, -2047
	addi a7, s0, 2047
	ld a7, 833(a7)
	ld t0, 576(s0)
	addi t1, s0, 2047
	ld t1, 193(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 449(s0)
	addi s0, s0, -2047
	ld t0, 584(s0)
	addi t1, s0, 2047
	ld t1, 201(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 457(s0)
	addi s0, s0, -2047
	ld t0, 592(s0)
	addi t1, s0, 2047
	ld t1, 209(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 465(s0)
	addi s0, s0, -2047
	ld t0, 600(s0)
	addi t1, s0, 2047
	ld t1, 217(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 473(s0)
	addi s0, s0, -2047
	ld t0, 608(s0)
	addi t1, s0, 2047
	ld t1, 225(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 481(s0)
	addi s0, s0, -2047
	ld t0, 616(s0)
	addi t1, s0, 2047
	ld t1, 233(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 489(s0)
	addi s0, s0, -2047
	ld t0, 624(s0)
	addi t1, s0, 2047
	ld t1, 241(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 497(s0)
	addi s0, s0, -2047
	ld t0, 632(s0)
	addi t1, s0, 2047
	ld t1, 249(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 505(s0)
	addi s0, s0, -2047
	ld t0, 640(s0)
	addi t1, s0, 2047
	ld t1, 257(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 769(s0)
	addi s0, s0, -2047
	ld t0, 648(s0)
	addi t1, s0, 2047
	ld t1, 265(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 777(s0)
	addi s0, s0, -2047
	ld t0, 656(s0)
	addi t1, s0, 2047
	ld t1, 273(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 785(s0)
	addi s0, s0, -2047
	ld t0, 664(s0)
	addi t1, s0, 2047
	ld t1, 281(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 793(s0)
	addi s0, s0, -2047
	ld t0, 672(s0)
	addi t1, s0, 2047
	ld t1, 289(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 801(s0)
	addi s0, s0, -2047
	ld t0, 680(s0)
	addi t1, s0, 2047
	ld t1, 297(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 809(s0)
	addi s0, s0, -2047
	ld t0, 688(s0)
	addi t1, s0, 2047
	ld t1, 305(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 817(s0)
	addi s0, s0, -2047
	ld t0, 696(s0)
	addi t1, s0, 2047
	ld t1, 313(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 825(s0)
	addi s0, s0, -2047
	ld ra, 200(s0)
	ld s0, 192(s0)
	ret
	.option pop
