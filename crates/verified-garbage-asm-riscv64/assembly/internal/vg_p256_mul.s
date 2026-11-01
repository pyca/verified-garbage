// The functions of `src/internal/vg_p256_mul.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p256_mul:
	.option push
	.option arch, +m, +c
	sd s0, 1504(a0)
	sd s1, 1512(a0)
	sd ra, 1520(a0)
	addi s0, a0, 0
	ld t0, 512(s0)
	sd t0, 992(s0)
	ld t0, 520(s0)
	sd t0, 1000(s0)
	ld t0, 528(s0)
	sd t0, 1008(s0)
	ld t0, 536(s0)
	sd t0, 1016(s0)
	ld t0, 544(s0)
	sd t0, 1024(s0)
	ld t0, 552(s0)
	sd t0, 1032(s0)
	ld t0, 560(s0)
	sd t0, 1040(s0)
	ld t0, 568(s0)
	sd t0, 1048(s0)
	ld t0, 160(s0)
	sd t0, 512(s0)
	ld t0, 168(s0)
	sd t0, 520(s0)
	ld t0, 176(s0)
	sd t0, 528(s0)
	ld t0, 184(s0)
	sd t0, 536(s0)
	ld t0, 224(s0)
	sd t0, 544(s0)
	ld t0, 232(s0)
	sd t0, 552(s0)
	ld t0, 240(s0)
	sd t0, 560(s0)
	ld t0, 248(s0)
	sd t0, 568(s0)
	ld t0, 160(s0)
	sd t0, 576(s0)
	ld t0, 168(s0)
	sd t0, 584(s0)
	ld t0, 176(s0)
	sd t0, 592(s0)
	ld t0, 184(s0)
	sd t0, 600(s0)
	addi s1, zero, 256
20:
	addi s1, s1, -1
	addi a0, s0, 0
	addi a1, zero, 800
	addi a2, zero, 512
	addi a3, zero, 512
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 832
	addi a2, zero, 544
	addi a3, zero, 544
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 576
	addi a3, zero, 576
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 896
	addi a2, zero, 512
	addi a3, zero, 544
	call {vg_p256_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 512
	addi a3, zero, 544
	call {vg_p256_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 896
	addi a2, zero, 896
	addi a3, zero, 928
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 800
	addi a3, zero, 832
	call {vg_p256_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 896
	addi a2, zero, 896
	addi a3, zero, 928
	call {vg_p256_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 512
	addi a3, zero, 576
	call {vg_p256_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 960
	addi a2, zero, 512
	addi a3, zero, 576
	call {vg_p256_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 928
	addi a3, zero, 960
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 960
	addi a2, zero, 800
	addi a3, zero, 864
	call {vg_p256_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 928
	addi a3, zero, 960
	call {vg_p256_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 960
	addi a2, zero, 544
	addi a3, zero, 576
	call {vg_p256_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 608
	addi a2, zero, 544
	addi a3, zero, 576
	call {vg_p256_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 960
	addi a2, zero, 960
	addi a3, zero, 608
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 608
	addi a2, zero, 832
	addi a3, zero, 864
	call {vg_p256_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 960
	addi a2, zero, 960
	addi a3, zero, 608
	call {vg_p256_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 672
	addi a2, zero, 256
	addi a3, zero, 928
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 608
	addi a2, zero, 288
	addi a3, zero, 864
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 672
	addi a2, zero, 608
	addi a3, zero, 672
	call {vg_p256_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 608
	addi a2, zero, 832
	addi a3, zero, 672
	call {vg_p256_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 672
	addi a2, zero, 832
	addi a3, zero, 672
	call {vg_p256_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 640
	addi a2, zero, 608
	addi a3, zero, 672
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 832
	addi a2, zero, 800
	addi a3, zero, 800
	call {vg_p256_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 832
	addi a2, zero, 832
	addi a3, zero, 800
	call {vg_p256_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 256
	addi a3, zero, 864
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 288
	addi a3, zero, 928
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 832
	addi a2, zero, 832
	addi a3, zero, 864
	call {vg_p256_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 800
	addi a3, zero, 864
	call {vg_p256_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 256
	addi a3, zero, 864
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 928
	addi a3, zero, 864
	call {vg_p256_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 800
	addi a2, zero, 832
	addi a3, zero, 928
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 640
	addi a2, zero, 640
	addi a3, zero, 800
	call {vg_p256_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 800
	addi a2, zero, 960
	addi a3, zero, 928
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 608
	addi a2, zero, 896
	addi a3, zero, 608
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 608
	addi a2, zero, 608
	addi a3, zero, 800
	call {vg_p256_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 800
	addi a2, zero, 896
	addi a3, zero, 832
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 672
	addi a2, zero, 960
	addi a3, zero, 672
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 672
	addi a2, zero, 672
	addi a3, zero, 800
	call {vg_p256_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 800
	addi a2, zero, 608
	addi a3, zero, 992
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 832
	addi a2, zero, 640
	addi a3, zero, 1024
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 672
	addi a3, zero, 224
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 896
	addi a2, zero, 608
	addi a3, zero, 640
	call {vg_p256_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 992
	addi a3, zero, 1024
	call {vg_p256_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 896
	addi a2, zero, 896
	addi a3, zero, 928
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 800
	addi a3, zero, 832
	call {vg_p256_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 896
	addi a2, zero, 896
	addi a3, zero, 928
	call {vg_p256_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 608
	addi a3, zero, 672
	call {vg_p256_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 960
	addi a2, zero, 992
	addi a3, zero, 224
	call {vg_p256_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 928
	addi a3, zero, 960
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 960
	addi a2, zero, 800
	addi a3, zero, 864
	call {vg_p256_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 928
	addi a3, zero, 960
	call {vg_p256_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 960
	addi a2, zero, 640
	addi a3, zero, 672
	call {vg_p256_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 704
	addi a2, zero, 1024
	addi a3, zero, 224
	call {vg_p256_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 960
	addi a2, zero, 960
	addi a3, zero, 704
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 704
	addi a2, zero, 832
	addi a3, zero, 864
	call {vg_p256_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 960
	addi a2, zero, 960
	addi a3, zero, 704
	call {vg_p256_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 256
	addi a3, zero, 928
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 704
	addi a2, zero, 288
	addi a3, zero, 864
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 704
	addi a3, zero, 768
	call {vg_p256_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 704
	addi a2, zero, 832
	addi a3, zero, 768
	call {vg_p256_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 832
	addi a3, zero, 768
	call {vg_p256_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 736
	addi a2, zero, 704
	addi a3, zero, 768
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 832
	addi a2, zero, 800
	addi a3, zero, 800
	call {vg_p256_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 832
	addi a2, zero, 832
	addi a3, zero, 800
	call {vg_p256_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 256
	addi a3, zero, 864
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 288
	addi a3, zero, 928
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 832
	addi a2, zero, 832
	addi a3, zero, 864
	call {vg_p256_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 800
	addi a3, zero, 864
	call {vg_p256_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 256
	addi a3, zero, 864
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 928
	addi a3, zero, 864
	call {vg_p256_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 800
	addi a2, zero, 832
	addi a3, zero, 928
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 736
	addi a2, zero, 736
	addi a3, zero, 800
	call {vg_p256_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 800
	addi a2, zero, 960
	addi a3, zero, 928
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 704
	addi a2, zero, 896
	addi a3, zero, 704
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 704
	addi a2, zero, 704
	addi a3, zero, 800
	call {vg_p256_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 800
	addi a2, zero, 896
	addi a3, zero, 832
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 960
	addi a3, zero, 768
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 768
	addi a2, zero, 768
	addi a3, zero, 800
	call {vg_p256_add_mod_p}
	srli t0, s1, 6
	slli t0, t0, 3
	add t0, t0, s0
	ld t1, 1056(t0)
	srl t1, t1, s1
	andi t1, t1, 1
	addi t2, zero, 0
	sub a7, t2, t1
	ld t0, 608(s0)
	ld t1, 704(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 512(s0)
	ld t0, 616(s0)
	ld t1, 712(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 520(s0)
	ld t0, 624(s0)
	ld t1, 720(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 528(s0)
	ld t0, 632(s0)
	ld t1, 728(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 536(s0)
	ld t0, 640(s0)
	ld t1, 736(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 544(s0)
	ld t0, 648(s0)
	ld t1, 744(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 552(s0)
	ld t0, 656(s0)
	ld t1, 752(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 560(s0)
	ld t0, 664(s0)
	ld t1, 760(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 568(s0)
	ld t0, 672(s0)
	ld t1, 768(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 576(s0)
	ld t0, 680(s0)
	ld t1, 776(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 584(s0)
	ld t0, 688(s0)
	ld t1, 784(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 592(s0)
	ld t0, 696(s0)
	ld t1, 792(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 600(s0)
	bnez s1, 20b
	ld ra, 1520(s0)
	ld s1, 1512(s0)
	ld s0, 1504(s0)
	ret
	.option pop
