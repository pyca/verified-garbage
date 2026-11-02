// The functions of `src/internal/vg_p521_check_point.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p521_check_point:
	.option push
	.option arch, +m, +c
	sd s0, 208(a0)
	sd ra, 216(a0)
	addi s0, a0, 0
	addi t5, zero, 0
	addi t3, s0, 2047
	ld t3, 393(t3)
	ld t4, 64(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 401(t3)
	ld t4, 72(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 409(t3)
	ld t4, 80(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 417(t3)
	ld t4, 88(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 425(t3)
	ld t4, 96(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 433(t3)
	ld t4, 104(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 441(t3)
	ld t4, 112(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 449(t3)
	ld t4, 120(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 457(t3)
	ld t4, 128(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t6, zero, 0
	sub a7, t6, t5
	addi t0, s0, 2047
	ld t0, 1185(t0)
	and t0, t0, a7
	addi s0, s0, 2047
	sd t0, 1185(s0)
	addi s0, s0, -2047
	addi t5, zero, 0
	addi t3, s0, 2047
	ld t3, 609(t3)
	ld t4, 64(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 617(t3)
	ld t4, 72(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 625(t3)
	ld t4, 80(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 633(t3)
	ld t4, 88(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 641(t3)
	ld t4, 96(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 649(t3)
	ld t4, 104(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 657(t3)
	ld t4, 112(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 665(t3)
	ld t4, 120(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t3, s0, 2047
	ld t3, 673(t3)
	ld t4, 128(s0)
	sltu t6, t3, t4
	sub t3, t3, t4
	sltu a4, t3, t5
	sub t3, t3, t5
	add t5, t6, a4
	addi t6, zero, 0
	sub a7, t6, t5
	addi t0, s0, 2047
	ld t0, 1185(t0)
	and t0, t0, a7
	addi s0, s0, 2047
	sd t0, 1185(s0)
	addi s0, s0, -2047
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 465
	addi a2, zero, 2047
	addi a2, a2, 393
	addi a3, zero, 2047
	addi a3, a3, 825
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 537
	addi a2, zero, 2047
	addi a2, a2, 609
	addi a3, zero, 2047
	addi a3, a3, 825
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 681
	addi a2, zero, 2047
	addi a2, a2, 537
	addi a3, zero, 2047
	addi a3, a3, 537
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 969
	addi a2, zero, 2047
	addi a2, a2, 465
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1041
	addi a2, zero, 2047
	addi a2, a2, 969
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 969
	addi a2, zero, 496
	addi a3, zero, 2047
	addi a3, a3, 465
	call {vg_p521_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 753
	addi a2, zero, 2047
	addi a2, a2, 1041
	addi a3, zero, 2047
	addi a3, a3, 969
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1041
	addi a2, zero, 2047
	addi a2, a2, 753
	addi a3, zero, 2047
	addi a3, a3, 897
	call {vg_p521_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 969
	addi a2, zero, 2047
	addi a2, a2, 681
	addi a3, zero, 2047
	addi a3, a3, 1041
	call {vg_p521_sub_mod_p}
	addi t3, zero, 0
	addi t4, s0, 2047
	ld t4, 969(t4)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 977(t4)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 985(t4)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 993(t4)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 1001(t4)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 1009(t4)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 1017(t4)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 1025(t4)
	or t3, t3, t4
	addi t4, s0, 2047
	ld t4, 1033(t4)
	or t3, t3, t4
	addi t4, zero, 0
	sub t4, t4, t3
	or t4, t4, t3
	srli t4, t4, 63
	addi a7, t4, -1
	addi t0, s0, 2047
	ld t0, 1185(t0)
	and t0, t0, a7
	addi s0, s0, 2047
	sd t0, 1185(s0)
	addi s0, s0, -2047
	addi a7, s0, 2047
	ld a7, 1185(a7)
	ld t0, 640(s0)
	addi t1, s0, 2047
	ld t1, 465(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 753(s0)
	addi s0, s0, -2047
	ld t0, 648(s0)
	addi t1, s0, 2047
	ld t1, 473(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 761(s0)
	addi s0, s0, -2047
	ld t0, 656(s0)
	addi t1, s0, 2047
	ld t1, 481(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 769(s0)
	addi s0, s0, -2047
	ld t0, 664(s0)
	addi t1, s0, 2047
	ld t1, 489(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 777(s0)
	addi s0, s0, -2047
	ld t0, 672(s0)
	addi t1, s0, 2047
	ld t1, 497(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 785(s0)
	addi s0, s0, -2047
	ld t0, 680(s0)
	addi t1, s0, 2047
	ld t1, 505(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 793(s0)
	addi s0, s0, -2047
	ld t0, 688(s0)
	addi t1, s0, 2047
	ld t1, 513(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 801(s0)
	addi s0, s0, -2047
	ld t0, 696(s0)
	addi t1, s0, 2047
	ld t1, 521(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 809(s0)
	addi s0, s0, -2047
	ld t0, 704(s0)
	addi t1, s0, 2047
	ld t1, 529(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 817(s0)
	addi s0, s0, -2047
	ld t0, 712(s0)
	addi t1, s0, 2047
	ld t1, 537(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 1113(s0)
	addi s0, s0, -2047
	ld t0, 720(s0)
	addi t1, s0, 2047
	ld t1, 545(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 1121(s0)
	addi s0, s0, -2047
	ld t0, 728(s0)
	addi t1, s0, 2047
	ld t1, 553(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 1129(s0)
	addi s0, s0, -2047
	ld t0, 736(s0)
	addi t1, s0, 2047
	ld t1, 561(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 1137(s0)
	addi s0, s0, -2047
	ld t0, 744(s0)
	addi t1, s0, 2047
	ld t1, 569(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 1145(s0)
	addi s0, s0, -2047
	ld t0, 752(s0)
	addi t1, s0, 2047
	ld t1, 577(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 1153(s0)
	addi s0, s0, -2047
	ld t0, 760(s0)
	addi t1, s0, 2047
	ld t1, 585(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 1161(s0)
	addi s0, s0, -2047
	ld t0, 768(s0)
	addi t1, s0, 2047
	ld t1, 593(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 1169(s0)
	addi s0, s0, -2047
	ld t0, 776(s0)
	addi t1, s0, 2047
	ld t1, 601(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	addi s0, s0, 2047
	sd t0, 1177(s0)
	addi s0, s0, -2047
	ld ra, 216(s0)
	ld s0, 208(s0)
	ret
	.option pop
