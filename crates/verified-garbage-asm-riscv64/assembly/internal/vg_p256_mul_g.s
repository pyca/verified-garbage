// The functions of `src/internal/vg_p256_mul_g.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p256_mul_g:
	.option push
	.option arch, +m, +c
	lla t0, {VG_P256_COMB}
	sd s0, 1504(a0)
	sd s1, 1512(a0)
	sd ra, 1520(a0)
	sd s4, 1528(a0)
	addi s0, a0, 0
	addi s4, t0, 0
	ld t0, 1056(s0)
	sd t0, 1536(s0)
	ld t0, 1064(s0)
	sd t0, 1544(s0)
	ld t0, 1072(s0)
	sd t0, 1552(s0)
	ld t0, 1080(s0)
	sd t0, 1560(s0)
	addi t0, zero, 0
	sd t0, 1568(s0)
	lui t0, 97923
	addiw t0, t0, -958
	slli t0, t0, 32
	lui t1, 779584
	addiw t1, t1, -699
	add t0, t0, t1
	sd t0, 512(s0)
	lui t0, 118883
	addiw t0, t0, 108
	slli t0, t0, 32
	lui t1, 972897
	addiw t1, t1, -1523
	add t0, t0, t1
	sd t0, 520(s0)
	lui t0, 419607
	addiw t0, t0, 299
	slli t0, t0, 32
	lui t1, 220785
	addiw t1, t1, 400
	add t0, t0, t1
	sd t0, 528(s0)
	lui t0, 856522
	addiw t0, t0, 307
	slli t0, t0, 32
	lui t1, 876835
	addiw t1, t1, 662
	add t0, t0, t1
	sd t0, 536(s0)
	lui t0, 641999
	addiw t0, t0, 1967
	slli t0, t0, 32
	lui t1, 128247
	addiw t1, t1, -1019
	add t0, t0, t1
	sd t0, 544(s0)
	lui t0, 406914
	addiw t0, t0, 551
	slli t0, t0, 32
	lui t1, 110683
	addiw t1, t1, -249
	add t0, t0, t1
	sd t0, 552(s0)
	lui t0, 376498
	addiw t0, t0, 1794
	slli t0, t0, 32
	lui t1, 415978
	addiw t1, t1, -1678
	add t0, t0, t1
	sd t0, 560(s0)
	lui t0, 480662
	addiw t0, t0, 1625
	slli t0, t0, 32
	lui t1, 426048
	addiw t1, t1, -708
	add t0, t0, t1
	sd t0, 568(s0)
	ld t0, 224(s0)
	sd t0, 576(s0)
	ld t0, 232(s0)
	sd t0, 584(s0)
	ld t0, 240(s0)
	sd t0, 592(s0)
	ld t0, 248(s0)
	sd t0, 600(s0)
	addi s1, zero, 37
20:
	addi s1, s1, -1
	slli t0, s1, 3
	sub t0, t0, s1
	srli t1, t0, 6
	slli t1, t1, 3
	add t1, t1, s0
	ld t2, 1536(t1)
	ld t3, 1544(t1)
	srl t2, t2, t0
	xori t4, t0, 63
	slli t3, t3, 1
	sll t3, t3, t4
	or t2, t2, t3
	andi t2, t2, 127
	addi t2, t2, -64
	srai t3, t2, 63
	xor t2, t2, t3
	sub t2, t2, t3
	addi t2, t2, -1
	srai t4, t2, 63
	sd t3, 1024(s0)
	sd t4, 1032(s0)
	slli a1, t2, 63
	srai a1, a1, 63
	slli a2, t2, 62
	srai a2, a2, 63
	slli a3, t2, 61
	srai a3, a3, 63
	slli a4, t2, 60
	srai a4, a4, 63
	slli a5, t2, 59
	srai a5, a5, 63
	slli a6, t2, 58
	srai a6, a6, 63
	slli t0, s1, 12
	add a0, s4, t0
	addi a7, a0, 2047
	addi a7, a7, 1
	ld t0, 0(a0)
	ld t1, 64(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 128(a0)
	ld t2, 192(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 256(a0)
	ld t2, 320(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 384(a0)
	ld t3, 448(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 512(a0)
	ld t2, 576(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 640(a0)
	ld t3, 704(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 768(a0)
	ld t3, 832(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 896(a0)
	ld t4, 960(a0)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	ld t1, 1024(a0)
	ld t2, 1088(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1152(a0)
	ld t3, 1216(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1280(a0)
	ld t3, 1344(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1408(a0)
	ld t4, 1472(a0)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	ld t2, 1536(a0)
	ld t3, 1600(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1664(a0)
	ld t4, 1728(a0)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 1792(a0)
	ld t4, 1856(a0)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1920(a0)
	ld t5, 1984(a0)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a5
	xor t0, t0, t1
	ld t1, 0(a7)
	ld t2, 64(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 128(a7)
	ld t3, 192(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 256(a7)
	ld t3, 320(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 384(a7)
	ld t4, 448(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	ld t2, 512(a7)
	ld t3, 576(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 640(a7)
	ld t4, 704(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 768(a7)
	ld t4, 832(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 896(a7)
	ld t5, 960(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	ld t2, 1024(a7)
	ld t3, 1088(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1152(a7)
	ld t4, 1216(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 1280(a7)
	ld t4, 1344(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1408(a7)
	ld t5, 1472(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	ld t3, 1536(a7)
	ld t4, 1600(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1664(a7)
	ld t5, 1728(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	ld t4, 1792(a7)
	ld t5, 1856(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	ld t5, 1920(a7)
	ld t6, 1984(a7)
	xor t6, t6, t5
	and t6, t6, a1
	xor t5, t5, t6
	xor t5, t5, t4
	and t5, t5, a2
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a3
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a4
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a5
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a6
	xor t0, t0, t1
	sd t0, 608(s0)
	ld t0, 8(a0)
	ld t1, 72(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 136(a0)
	ld t2, 200(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 264(a0)
	ld t2, 328(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 392(a0)
	ld t3, 456(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 520(a0)
	ld t2, 584(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 648(a0)
	ld t3, 712(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 776(a0)
	ld t3, 840(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 904(a0)
	ld t4, 968(a0)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	ld t1, 1032(a0)
	ld t2, 1096(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1160(a0)
	ld t3, 1224(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1288(a0)
	ld t3, 1352(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1416(a0)
	ld t4, 1480(a0)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	ld t2, 1544(a0)
	ld t3, 1608(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1672(a0)
	ld t4, 1736(a0)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 1800(a0)
	ld t4, 1864(a0)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1928(a0)
	ld t5, 1992(a0)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a5
	xor t0, t0, t1
	ld t1, 8(a7)
	ld t2, 72(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 136(a7)
	ld t3, 200(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 264(a7)
	ld t3, 328(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 392(a7)
	ld t4, 456(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	ld t2, 520(a7)
	ld t3, 584(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 648(a7)
	ld t4, 712(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 776(a7)
	ld t4, 840(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 904(a7)
	ld t5, 968(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	ld t2, 1032(a7)
	ld t3, 1096(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1160(a7)
	ld t4, 1224(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 1288(a7)
	ld t4, 1352(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1416(a7)
	ld t5, 1480(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	ld t3, 1544(a7)
	ld t4, 1608(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1672(a7)
	ld t5, 1736(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	ld t4, 1800(a7)
	ld t5, 1864(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	ld t5, 1928(a7)
	ld t6, 1992(a7)
	xor t6, t6, t5
	and t6, t6, a1
	xor t5, t5, t6
	xor t5, t5, t4
	and t5, t5, a2
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a3
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a4
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a5
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a6
	xor t0, t0, t1
	sd t0, 616(s0)
	ld t0, 16(a0)
	ld t1, 80(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 144(a0)
	ld t2, 208(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 272(a0)
	ld t2, 336(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 400(a0)
	ld t3, 464(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 528(a0)
	ld t2, 592(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 656(a0)
	ld t3, 720(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 784(a0)
	ld t3, 848(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 912(a0)
	ld t4, 976(a0)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	ld t1, 1040(a0)
	ld t2, 1104(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1168(a0)
	ld t3, 1232(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1296(a0)
	ld t3, 1360(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1424(a0)
	ld t4, 1488(a0)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	ld t2, 1552(a0)
	ld t3, 1616(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1680(a0)
	ld t4, 1744(a0)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 1808(a0)
	ld t4, 1872(a0)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1936(a0)
	ld t5, 2000(a0)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a5
	xor t0, t0, t1
	ld t1, 16(a7)
	ld t2, 80(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 144(a7)
	ld t3, 208(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 272(a7)
	ld t3, 336(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 400(a7)
	ld t4, 464(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	ld t2, 528(a7)
	ld t3, 592(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 656(a7)
	ld t4, 720(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 784(a7)
	ld t4, 848(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 912(a7)
	ld t5, 976(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	ld t2, 1040(a7)
	ld t3, 1104(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1168(a7)
	ld t4, 1232(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 1296(a7)
	ld t4, 1360(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1424(a7)
	ld t5, 1488(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	ld t3, 1552(a7)
	ld t4, 1616(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1680(a7)
	ld t5, 1744(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	ld t4, 1808(a7)
	ld t5, 1872(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	ld t5, 1936(a7)
	ld t6, 2000(a7)
	xor t6, t6, t5
	and t6, t6, a1
	xor t5, t5, t6
	xor t5, t5, t4
	and t5, t5, a2
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a3
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a4
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a5
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a6
	xor t0, t0, t1
	sd t0, 624(s0)
	ld t0, 24(a0)
	ld t1, 88(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 152(a0)
	ld t2, 216(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 280(a0)
	ld t2, 344(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 408(a0)
	ld t3, 472(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 536(a0)
	ld t2, 600(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 664(a0)
	ld t3, 728(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 792(a0)
	ld t3, 856(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 920(a0)
	ld t4, 984(a0)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	ld t1, 1048(a0)
	ld t2, 1112(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1176(a0)
	ld t3, 1240(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1304(a0)
	ld t3, 1368(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1432(a0)
	ld t4, 1496(a0)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	ld t2, 1560(a0)
	ld t3, 1624(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1688(a0)
	ld t4, 1752(a0)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 1816(a0)
	ld t4, 1880(a0)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1944(a0)
	ld t5, 2008(a0)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a5
	xor t0, t0, t1
	ld t1, 24(a7)
	ld t2, 88(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 152(a7)
	ld t3, 216(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 280(a7)
	ld t3, 344(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 408(a7)
	ld t4, 472(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	ld t2, 536(a7)
	ld t3, 600(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 664(a7)
	ld t4, 728(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 792(a7)
	ld t4, 856(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 920(a7)
	ld t5, 984(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	ld t2, 1048(a7)
	ld t3, 1112(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1176(a7)
	ld t4, 1240(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 1304(a7)
	ld t4, 1368(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1432(a7)
	ld t5, 1496(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	ld t3, 1560(a7)
	ld t4, 1624(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1688(a7)
	ld t5, 1752(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	ld t4, 1816(a7)
	ld t5, 1880(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	ld t5, 1944(a7)
	ld t6, 2008(a7)
	xor t6, t6, t5
	and t6, t6, a1
	xor t5, t5, t6
	xor t5, t5, t4
	and t5, t5, a2
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a3
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a4
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a5
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a6
	xor t0, t0, t1
	sd t0, 632(s0)
	ld t0, 32(a0)
	ld t1, 96(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 160(a0)
	ld t2, 224(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 288(a0)
	ld t2, 352(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 416(a0)
	ld t3, 480(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 544(a0)
	ld t2, 608(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 672(a0)
	ld t3, 736(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 800(a0)
	ld t3, 864(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 928(a0)
	ld t4, 992(a0)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	ld t1, 1056(a0)
	ld t2, 1120(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1184(a0)
	ld t3, 1248(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1312(a0)
	ld t3, 1376(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1440(a0)
	ld t4, 1504(a0)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	ld t2, 1568(a0)
	ld t3, 1632(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1696(a0)
	ld t4, 1760(a0)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 1824(a0)
	ld t4, 1888(a0)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1952(a0)
	ld t5, 2016(a0)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a5
	xor t0, t0, t1
	ld t1, 32(a7)
	ld t2, 96(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 160(a7)
	ld t3, 224(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 288(a7)
	ld t3, 352(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 416(a7)
	ld t4, 480(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	ld t2, 544(a7)
	ld t3, 608(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 672(a7)
	ld t4, 736(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 800(a7)
	ld t4, 864(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 928(a7)
	ld t5, 992(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	ld t2, 1056(a7)
	ld t3, 1120(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1184(a7)
	ld t4, 1248(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 1312(a7)
	ld t4, 1376(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1440(a7)
	ld t5, 1504(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	ld t3, 1568(a7)
	ld t4, 1632(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1696(a7)
	ld t5, 1760(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	ld t4, 1824(a7)
	ld t5, 1888(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	ld t5, 1952(a7)
	ld t6, 2016(a7)
	xor t6, t6, t5
	and t6, t6, a1
	xor t5, t5, t6
	xor t5, t5, t4
	and t5, t5, a2
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a3
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a4
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a5
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a6
	xor t0, t0, t1
	sd t0, 640(s0)
	ld t0, 40(a0)
	ld t1, 104(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 168(a0)
	ld t2, 232(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 296(a0)
	ld t2, 360(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 424(a0)
	ld t3, 488(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 552(a0)
	ld t2, 616(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 680(a0)
	ld t3, 744(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 808(a0)
	ld t3, 872(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 936(a0)
	ld t4, 1000(a0)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	ld t1, 1064(a0)
	ld t2, 1128(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1192(a0)
	ld t3, 1256(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1320(a0)
	ld t3, 1384(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1448(a0)
	ld t4, 1512(a0)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	ld t2, 1576(a0)
	ld t3, 1640(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1704(a0)
	ld t4, 1768(a0)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 1832(a0)
	ld t4, 1896(a0)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1960(a0)
	ld t5, 2024(a0)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a5
	xor t0, t0, t1
	ld t1, 40(a7)
	ld t2, 104(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 168(a7)
	ld t3, 232(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 296(a7)
	ld t3, 360(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 424(a7)
	ld t4, 488(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	ld t2, 552(a7)
	ld t3, 616(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 680(a7)
	ld t4, 744(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 808(a7)
	ld t4, 872(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 936(a7)
	ld t5, 1000(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	ld t2, 1064(a7)
	ld t3, 1128(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1192(a7)
	ld t4, 1256(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 1320(a7)
	ld t4, 1384(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1448(a7)
	ld t5, 1512(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	ld t3, 1576(a7)
	ld t4, 1640(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1704(a7)
	ld t5, 1768(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	ld t4, 1832(a7)
	ld t5, 1896(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	ld t5, 1960(a7)
	ld t6, 2024(a7)
	xor t6, t6, t5
	and t6, t6, a1
	xor t5, t5, t6
	xor t5, t5, t4
	and t5, t5, a2
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a3
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a4
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a5
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a6
	xor t0, t0, t1
	sd t0, 648(s0)
	ld t0, 48(a0)
	ld t1, 112(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 176(a0)
	ld t2, 240(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 304(a0)
	ld t2, 368(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 432(a0)
	ld t3, 496(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 560(a0)
	ld t2, 624(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 688(a0)
	ld t3, 752(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 816(a0)
	ld t3, 880(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 944(a0)
	ld t4, 1008(a0)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	ld t1, 1072(a0)
	ld t2, 1136(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1200(a0)
	ld t3, 1264(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1328(a0)
	ld t3, 1392(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1456(a0)
	ld t4, 1520(a0)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	ld t2, 1584(a0)
	ld t3, 1648(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1712(a0)
	ld t4, 1776(a0)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 1840(a0)
	ld t4, 1904(a0)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1968(a0)
	ld t5, 2032(a0)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a5
	xor t0, t0, t1
	ld t1, 48(a7)
	ld t2, 112(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 176(a7)
	ld t3, 240(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 304(a7)
	ld t3, 368(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 432(a7)
	ld t4, 496(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	ld t2, 560(a7)
	ld t3, 624(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 688(a7)
	ld t4, 752(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 816(a7)
	ld t4, 880(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 944(a7)
	ld t5, 1008(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	ld t2, 1072(a7)
	ld t3, 1136(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1200(a7)
	ld t4, 1264(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 1328(a7)
	ld t4, 1392(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1456(a7)
	ld t5, 1520(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	ld t3, 1584(a7)
	ld t4, 1648(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1712(a7)
	ld t5, 1776(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	ld t4, 1840(a7)
	ld t5, 1904(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	ld t5, 1968(a7)
	ld t6, 2032(a7)
	xor t6, t6, t5
	and t6, t6, a1
	xor t5, t5, t6
	xor t5, t5, t4
	and t5, t5, a2
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a3
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a4
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a5
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a6
	xor t0, t0, t1
	sd t0, 656(s0)
	ld t0, 56(a0)
	ld t1, 120(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 184(a0)
	ld t2, 248(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 312(a0)
	ld t2, 376(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 440(a0)
	ld t3, 504(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 568(a0)
	ld t2, 632(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 696(a0)
	ld t3, 760(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 824(a0)
	ld t3, 888(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 952(a0)
	ld t4, 1016(a0)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	ld t1, 1080(a0)
	ld t2, 1144(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1208(a0)
	ld t3, 1272(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1336(a0)
	ld t3, 1400(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1464(a0)
	ld t4, 1528(a0)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	ld t2, 1592(a0)
	ld t3, 1656(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1720(a0)
	ld t4, 1784(a0)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 1848(a0)
	ld t4, 1912(a0)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1976(a0)
	ld t5, 2040(a0)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a5
	xor t0, t0, t1
	ld t1, 56(a7)
	ld t2, 120(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 184(a7)
	ld t3, 248(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 312(a7)
	ld t3, 376(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 440(a7)
	ld t4, 504(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	ld t2, 568(a7)
	ld t3, 632(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 696(a7)
	ld t4, 760(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 824(a7)
	ld t4, 888(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 952(a7)
	ld t5, 1016(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	ld t2, 1080(a7)
	ld t3, 1144(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1208(a7)
	ld t4, 1272(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 1336(a7)
	ld t4, 1400(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1464(a7)
	ld t5, 1528(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	ld t3, 1592(a7)
	ld t4, 1656(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1720(a7)
	ld t5, 1784(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	ld t4, 1848(a7)
	ld t5, 1912(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	ld t5, 1976(a7)
	ld t6, 2040(a7)
	xor t6, t6, t5
	and t6, t6, a1
	xor t5, t5, t6
	xor t5, t5, t4
	and t5, t5, a2
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a3
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a4
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a5
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a6
	xor t0, t0, t1
	sd t0, 664(s0)
	ld t0, 224(s0)
	sd t0, 672(s0)
	ld t0, 232(s0)
	sd t0, 680(s0)
	ld t0, 240(s0)
	sd t0, 688(s0)
	ld t0, 248(s0)
	sd t0, 696(s0)
	ld a7, 1032(s0)
	ld t0, 608(s0)
	ld t1, 160(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 608(s0)
	ld t0, 616(s0)
	ld t1, 168(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 616(s0)
	ld t0, 624(s0)
	ld t1, 176(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 624(s0)
	ld t0, 632(s0)
	ld t1, 184(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 632(s0)
	ld t0, 640(s0)
	ld t1, 224(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 640(s0)
	ld t0, 648(s0)
	ld t1, 232(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 648(s0)
	ld t0, 656(s0)
	ld t1, 240(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 656(s0)
	ld t0, 664(s0)
	ld t1, 248(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 664(s0)
	ld t0, 672(s0)
	ld t1, 160(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 672(s0)
	ld t0, 680(s0)
	ld t1, 168(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 680(s0)
	ld t0, 688(s0)
	ld t1, 176(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 688(s0)
	ld t0, 696(s0)
	ld t1, 184(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 696(s0)
	addi a0, s0, 0
	addi a1, zero, 992
	addi a2, zero, 160
	addi a3, zero, 640
	call {vg_p256_sub_mod_p}
	ld a7, 1024(s0)
	ld t0, 640(s0)
	ld t1, 992(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 640(s0)
	ld t0, 648(s0)
	ld t1, 1000(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 648(s0)
	ld t0, 656(s0)
	ld t1, 1008(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 656(s0)
	ld t0, 664(s0)
	ld t1, 1016(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 664(s0)
	addi a0, s0, 0
	addi a1, zero, 800
	addi a2, zero, 512
	addi a3, zero, 608
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 832
	addi a2, zero, 544
	addi a3, zero, 640
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 864
	addi a2, zero, 576
	addi a3, zero, 672
	call {vg_p256_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 896
	addi a2, zero, 512
	addi a3, zero, 544
	call {vg_p256_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 928
	addi a2, zero, 608
	addi a3, zero, 640
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
	addi a2, zero, 608
	addi a3, zero, 672
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
	addi a1, zero, 704
	addi a2, zero, 640
	addi a3, zero, 672
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
	ld t0, 704(s0)
	sd t0, 512(s0)
	ld t0, 712(s0)
	sd t0, 520(s0)
	ld t0, 720(s0)
	sd t0, 528(s0)
	ld t0, 728(s0)
	sd t0, 536(s0)
	ld t0, 736(s0)
	sd t0, 544(s0)
	ld t0, 744(s0)
	sd t0, 552(s0)
	ld t0, 752(s0)
	sd t0, 560(s0)
	ld t0, 760(s0)
	sd t0, 568(s0)
	ld t0, 768(s0)
	sd t0, 576(s0)
	ld t0, 776(s0)
	sd t0, 584(s0)
	ld t0, 784(s0)
	sd t0, 592(s0)
	ld t0, 792(s0)
	sd t0, 600(s0)
	bnez s1, 20b
	ld ra, 1520(s0)
	ld s4, 1528(s0)
	ld s1, 1512(s0)
	ld s0, 1504(s0)
	ret
	.option pop
