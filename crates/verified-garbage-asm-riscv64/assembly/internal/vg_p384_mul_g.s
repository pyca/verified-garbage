// The functions of `src/internal/vg_p384_mul_g.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p384_mul_g:
	.option push
	.option arch, +m, +c
	lla t0, {VG_P384_COMB}
	addi a0, a0, 2047
	sd s0, 177(a0)
	addi a0, a0, -2047
	addi a0, a0, 2047
	sd s1, 185(a0)
	addi a0, a0, -2047
	addi a0, a0, 2047
	sd ra, 193(a0)
	addi a0, a0, -2047
	addi a0, a0, 2047
	sd s4, 201(a0)
	addi a0, a0, -2047
	addi s0, a0, 0
	addi s4, t0, 0
	ld t0, 1552(s0)
	addi s0, s0, 2047
	sd t0, 225(s0)
	addi s0, s0, -2047
	ld t0, 1560(s0)
	addi s0, s0, 2047
	sd t0, 233(s0)
	addi s0, s0, -2047
	ld t0, 1568(s0)
	addi s0, s0, 2047
	sd t0, 241(s0)
	addi s0, s0, -2047
	ld t0, 1576(s0)
	addi s0, s0, 2047
	sd t0, 249(s0)
	addi s0, s0, -2047
	ld t0, 1584(s0)
	addi s0, s0, 2047
	sd t0, 257(s0)
	addi s0, s0, -2047
	ld t0, 1592(s0)
	addi s0, s0, 2047
	sd t0, 265(s0)
	addi s0, s0, -2047
	addi t0, zero, 0
	addi s0, s0, 2047
	sd t0, 273(s0)
	addi s0, s0, -2047
	lui t0, 720489
	addiw t0, t0, 1326
	slli t0, t0, 32
	lui t1, 983678
	addiw t1, t1, -428
	add t0, t0, t1
	sd t0, 736(s0)
	lui t0, 378065
	addiw t0, t0, -1496
	slli t0, t0, 32
	lui t1, 551785
	addiw t1, t1, -847
	add t0, t0, t1
	sd t0, 744(s0)
	lui t0, 448887
	addiw t0, t0, 119
	slli t0, t0, 32
	lui t1, 409615
	addiw t1, t1, -2015
	add t0, t0, t1
	sd t0, 752(s0)
	lui t0, 272841
	addiw t0, t0, -137
	slli t0, t0, 32
	lui t1, 310275
	addiw t1, t1, 1408
	add t0, t0, t1
	sd t0, 760(s0)
	lui t0, 807578
	addiw t0, t0, -2043
	slli t0, t0, 32
	lui t1, 620478
	addiw t1, t1, 1241
	add t0, t0, t1
	sd t0, 768(s0)
	lui t0, 896419
	addiw t0, t0, -509
	slli t0, t0, 32
	lui t1, 332944
	addiw t1, t1, 1254
	add t0, t0, t1
	sd t0, 776(s0)
	lui t0, 294191
	addiw t0, t0, -972
	slli t0, t0, 32
	lui t1, 439149
	addiw t1, t1, 952
	add t0, t0, t1
	sd t0, 784(s0)
	lui t0, 21814
	addiw t0, t0, -2021
	slli t0, t0, 32
	lui t1, 575433
	addiw t1, t1, 145
	add t0, t0, t1
	sd t0, 792(s0)
	lui t0, 770663
	addiw t0, t0, -440
	slli t0, t0, 32
	lui t1, 423799
	addiw t1, t1, 447
	add t0, t0, t1
	sd t0, 800(s0)
	lui t0, 228854
	addiw t0, t0, 1175
	slli t0, t0, 32
	lui t1, 532989
	addiw t1, t1, 1495
	add t0, t0, t1
	sd t0, 808(s0)
	lui t0, 158655
	addiw t0, t0, -1227
	slli t0, t0, 32
	lui t1, 363264
	addiw t1, t1, -1829
	add t0, t0, t1
	sd t0, 816(s0)
	lui t0, 869146
	addiw t0, t0, -1012
	slli t0, t0, 32
	lui t1, 305178
	addiw t1, t1, 1538
	add t0, t0, t1
	sd t0, 824(s0)
	ld t0, 304(s0)
	sd t0, 832(s0)
	ld t0, 312(s0)
	sd t0, 840(s0)
	ld t0, 320(s0)
	sd t0, 848(s0)
	ld t0, 328(s0)
	sd t0, 856(s0)
	ld t0, 336(s0)
	sd t0, 864(s0)
	ld t0, 344(s0)
	sd t0, 872(s0)
	addi s1, zero, 55
20:
	addi s1, s1, -1
	slli t0, s1, 3
	sub t0, t0, s1
	srli t1, t0, 6
	slli t1, t1, 3
	add t1, t1, s0
	addi t2, t1, 2047
	ld t2, 225(t2)
	addi t3, t1, 2047
	ld t3, 233(t3)
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
	sd t3, 1504(s0)
	sd t4, 1512(s0)
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
	slli t1, s1, 11
	add t0, t0, t1
	add a0, s4, t0
	ld t0, 0(a0)
	ld t1, 96(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 192(a0)
	ld t2, 288(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 384(a0)
	ld t2, 480(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 576(a0)
	ld t3, 672(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 768(a0)
	ld t2, 864(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 960(a0)
	ld t3, 1056(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1152(a0)
	ld t3, 1248(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1344(a0)
	ld t4, 1440(a0)
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
	addi a7, a0, 1536
	ld t1, 0(a7)
	ld t2, 96(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 192(a7)
	ld t3, 288(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 384(a7)
	ld t3, 480(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 576(a7)
	ld t4, 672(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	ld t2, 768(a7)
	ld t3, 864(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 960(a7)
	ld t4, 1056(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 1152(a7)
	ld t4, 1248(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1344(a7)
	ld t5, 1440(a7)
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
	addi a7, a0, 2047
	addi a7, a7, 1025
	ld t1, 0(a7)
	ld t2, 96(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 192(a7)
	ld t3, 288(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 384(a7)
	ld t3, 480(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 576(a7)
	ld t4, 672(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	ld t2, 768(a7)
	ld t3, 864(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 960(a7)
	ld t4, 1056(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 1152(a7)
	ld t4, 1248(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1344(a7)
	ld t5, 1440(a7)
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
	addi a7, a0, 2047
	addi a7, a7, 2047
	addi a7, a7, 514
	ld t2, 0(a7)
	ld t3, 96(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 192(a7)
	ld t4, 288(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 384(a7)
	ld t4, 480(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 576(a7)
	ld t5, 672(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	ld t3, 768(a7)
	ld t4, 864(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 960(a7)
	ld t5, 1056(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	ld t4, 1152(a7)
	ld t5, 1248(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	ld t5, 1344(a7)
	ld t6, 1440(a7)
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
	sd t0, 880(s0)
	ld t0, 8(a0)
	ld t1, 104(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 200(a0)
	ld t2, 296(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 392(a0)
	ld t2, 488(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 584(a0)
	ld t3, 680(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 776(a0)
	ld t2, 872(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 968(a0)
	ld t3, 1064(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1160(a0)
	ld t3, 1256(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1352(a0)
	ld t4, 1448(a0)
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
	addi a7, a0, 1536
	ld t1, 8(a7)
	ld t2, 104(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 200(a7)
	ld t3, 296(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 392(a7)
	ld t3, 488(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 584(a7)
	ld t4, 680(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	ld t2, 776(a7)
	ld t3, 872(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 968(a7)
	ld t4, 1064(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 1160(a7)
	ld t4, 1256(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1352(a7)
	ld t5, 1448(a7)
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
	addi a7, a0, 2047
	addi a7, a7, 1025
	ld t1, 8(a7)
	ld t2, 104(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 200(a7)
	ld t3, 296(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 392(a7)
	ld t3, 488(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 584(a7)
	ld t4, 680(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	ld t2, 776(a7)
	ld t3, 872(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 968(a7)
	ld t4, 1064(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 1160(a7)
	ld t4, 1256(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1352(a7)
	ld t5, 1448(a7)
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
	addi a7, a0, 2047
	addi a7, a7, 2047
	addi a7, a7, 514
	ld t2, 8(a7)
	ld t3, 104(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 200(a7)
	ld t4, 296(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 392(a7)
	ld t4, 488(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 584(a7)
	ld t5, 680(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	ld t3, 776(a7)
	ld t4, 872(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 968(a7)
	ld t5, 1064(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	ld t4, 1160(a7)
	ld t5, 1256(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	ld t5, 1352(a7)
	ld t6, 1448(a7)
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
	sd t0, 888(s0)
	ld t0, 16(a0)
	ld t1, 112(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 208(a0)
	ld t2, 304(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 400(a0)
	ld t2, 496(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 592(a0)
	ld t3, 688(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 784(a0)
	ld t2, 880(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 976(a0)
	ld t3, 1072(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1168(a0)
	ld t3, 1264(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1360(a0)
	ld t4, 1456(a0)
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
	addi a7, a0, 1536
	ld t1, 16(a7)
	ld t2, 112(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 208(a7)
	ld t3, 304(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 400(a7)
	ld t3, 496(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 592(a7)
	ld t4, 688(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	ld t2, 784(a7)
	ld t3, 880(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 976(a7)
	ld t4, 1072(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 1168(a7)
	ld t4, 1264(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1360(a7)
	ld t5, 1456(a7)
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
	addi a7, a0, 2047
	addi a7, a7, 1025
	ld t1, 16(a7)
	ld t2, 112(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 208(a7)
	ld t3, 304(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 400(a7)
	ld t3, 496(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 592(a7)
	ld t4, 688(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	ld t2, 784(a7)
	ld t3, 880(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 976(a7)
	ld t4, 1072(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 1168(a7)
	ld t4, 1264(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1360(a7)
	ld t5, 1456(a7)
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
	addi a7, a0, 2047
	addi a7, a7, 2047
	addi a7, a7, 514
	ld t2, 16(a7)
	ld t3, 112(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 208(a7)
	ld t4, 304(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 400(a7)
	ld t4, 496(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 592(a7)
	ld t5, 688(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	ld t3, 784(a7)
	ld t4, 880(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 976(a7)
	ld t5, 1072(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	ld t4, 1168(a7)
	ld t5, 1264(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	ld t5, 1360(a7)
	ld t6, 1456(a7)
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
	sd t0, 896(s0)
	ld t0, 24(a0)
	ld t1, 120(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 216(a0)
	ld t2, 312(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 408(a0)
	ld t2, 504(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 600(a0)
	ld t3, 696(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 792(a0)
	ld t2, 888(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 984(a0)
	ld t3, 1080(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1176(a0)
	ld t3, 1272(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1368(a0)
	ld t4, 1464(a0)
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
	addi a7, a0, 1536
	ld t1, 24(a7)
	ld t2, 120(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 216(a7)
	ld t3, 312(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 408(a7)
	ld t3, 504(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 600(a7)
	ld t4, 696(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	ld t2, 792(a7)
	ld t3, 888(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 984(a7)
	ld t4, 1080(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 1176(a7)
	ld t4, 1272(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1368(a7)
	ld t5, 1464(a7)
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
	addi a7, a0, 2047
	addi a7, a7, 1025
	ld t1, 24(a7)
	ld t2, 120(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 216(a7)
	ld t3, 312(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 408(a7)
	ld t3, 504(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 600(a7)
	ld t4, 696(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	ld t2, 792(a7)
	ld t3, 888(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 984(a7)
	ld t4, 1080(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 1176(a7)
	ld t4, 1272(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1368(a7)
	ld t5, 1464(a7)
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
	addi a7, a0, 2047
	addi a7, a7, 2047
	addi a7, a7, 514
	ld t2, 24(a7)
	ld t3, 120(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 216(a7)
	ld t4, 312(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 408(a7)
	ld t4, 504(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 600(a7)
	ld t5, 696(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	ld t3, 792(a7)
	ld t4, 888(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 984(a7)
	ld t5, 1080(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	ld t4, 1176(a7)
	ld t5, 1272(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	ld t5, 1368(a7)
	ld t6, 1464(a7)
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
	sd t0, 904(s0)
	ld t0, 32(a0)
	ld t1, 128(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 224(a0)
	ld t2, 320(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 416(a0)
	ld t2, 512(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 608(a0)
	ld t3, 704(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 800(a0)
	ld t2, 896(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 992(a0)
	ld t3, 1088(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1184(a0)
	ld t3, 1280(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1376(a0)
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
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi a7, a0, 1536
	ld t1, 32(a7)
	ld t2, 128(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 224(a7)
	ld t3, 320(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 416(a7)
	ld t3, 512(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 608(a7)
	ld t4, 704(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	ld t2, 800(a7)
	ld t3, 896(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 992(a7)
	ld t4, 1088(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 1184(a7)
	ld t4, 1280(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1376(a7)
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
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a5
	xor t0, t0, t1
	addi a7, a0, 2047
	addi a7, a7, 1025
	ld t1, 32(a7)
	ld t2, 128(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 224(a7)
	ld t3, 320(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 416(a7)
	ld t3, 512(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 608(a7)
	ld t4, 704(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	ld t2, 800(a7)
	ld t3, 896(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 992(a7)
	ld t4, 1088(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 1184(a7)
	ld t4, 1280(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1376(a7)
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
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	addi a7, a0, 2047
	addi a7, a7, 2047
	addi a7, a7, 514
	ld t2, 32(a7)
	ld t3, 128(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 224(a7)
	ld t4, 320(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 416(a7)
	ld t4, 512(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 608(a7)
	ld t5, 704(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	ld t3, 800(a7)
	ld t4, 896(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 992(a7)
	ld t5, 1088(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	ld t4, 1184(a7)
	ld t5, 1280(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	ld t5, 1376(a7)
	ld t6, 1472(a7)
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
	sd t0, 912(s0)
	ld t0, 40(a0)
	ld t1, 136(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 232(a0)
	ld t2, 328(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 424(a0)
	ld t2, 520(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 616(a0)
	ld t3, 712(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 808(a0)
	ld t2, 904(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1000(a0)
	ld t3, 1096(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1192(a0)
	ld t3, 1288(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1384(a0)
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
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi a7, a0, 1536
	ld t1, 40(a7)
	ld t2, 136(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 232(a7)
	ld t3, 328(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 424(a7)
	ld t3, 520(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 616(a7)
	ld t4, 712(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	ld t2, 808(a7)
	ld t3, 904(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1000(a7)
	ld t4, 1096(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 1192(a7)
	ld t4, 1288(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1384(a7)
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
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a5
	xor t0, t0, t1
	addi a7, a0, 2047
	addi a7, a7, 1025
	ld t1, 40(a7)
	ld t2, 136(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 232(a7)
	ld t3, 328(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 424(a7)
	ld t3, 520(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 616(a7)
	ld t4, 712(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	ld t2, 808(a7)
	ld t3, 904(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1000(a7)
	ld t4, 1096(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 1192(a7)
	ld t4, 1288(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1384(a7)
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
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	addi a7, a0, 2047
	addi a7, a7, 2047
	addi a7, a7, 514
	ld t2, 40(a7)
	ld t3, 136(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 232(a7)
	ld t4, 328(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 424(a7)
	ld t4, 520(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 616(a7)
	ld t5, 712(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	ld t3, 808(a7)
	ld t4, 904(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1000(a7)
	ld t5, 1096(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	ld t4, 1192(a7)
	ld t5, 1288(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	ld t5, 1384(a7)
	ld t6, 1480(a7)
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
	sd t0, 920(s0)
	ld t0, 48(a0)
	ld t1, 144(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 240(a0)
	ld t2, 336(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 432(a0)
	ld t2, 528(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 624(a0)
	ld t3, 720(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 816(a0)
	ld t2, 912(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1008(a0)
	ld t3, 1104(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1200(a0)
	ld t3, 1296(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1392(a0)
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
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi a7, a0, 1536
	ld t1, 48(a7)
	ld t2, 144(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 240(a7)
	ld t3, 336(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 432(a7)
	ld t3, 528(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 624(a7)
	ld t4, 720(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	ld t2, 816(a7)
	ld t3, 912(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1008(a7)
	ld t4, 1104(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 1200(a7)
	ld t4, 1296(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1392(a7)
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
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a5
	xor t0, t0, t1
	addi a7, a0, 2047
	addi a7, a7, 1025
	ld t1, 48(a7)
	ld t2, 144(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 240(a7)
	ld t3, 336(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 432(a7)
	ld t3, 528(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 624(a7)
	ld t4, 720(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	ld t2, 816(a7)
	ld t3, 912(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1008(a7)
	ld t4, 1104(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 1200(a7)
	ld t4, 1296(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1392(a7)
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
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	addi a7, a0, 2047
	addi a7, a7, 2047
	addi a7, a7, 514
	ld t2, 48(a7)
	ld t3, 144(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 240(a7)
	ld t4, 336(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 432(a7)
	ld t4, 528(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 624(a7)
	ld t5, 720(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	ld t3, 816(a7)
	ld t4, 912(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1008(a7)
	ld t5, 1104(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	ld t4, 1200(a7)
	ld t5, 1296(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	ld t5, 1392(a7)
	ld t6, 1488(a7)
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
	sd t0, 928(s0)
	ld t0, 56(a0)
	ld t1, 152(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 248(a0)
	ld t2, 344(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 440(a0)
	ld t2, 536(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 632(a0)
	ld t3, 728(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 824(a0)
	ld t2, 920(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1016(a0)
	ld t3, 1112(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1208(a0)
	ld t3, 1304(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1400(a0)
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
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi a7, a0, 1536
	ld t1, 56(a7)
	ld t2, 152(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 248(a7)
	ld t3, 344(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 440(a7)
	ld t3, 536(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 632(a7)
	ld t4, 728(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	ld t2, 824(a7)
	ld t3, 920(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1016(a7)
	ld t4, 1112(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 1208(a7)
	ld t4, 1304(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1400(a7)
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
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a5
	xor t0, t0, t1
	addi a7, a0, 2047
	addi a7, a7, 1025
	ld t1, 56(a7)
	ld t2, 152(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 248(a7)
	ld t3, 344(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 440(a7)
	ld t3, 536(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 632(a7)
	ld t4, 728(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	ld t2, 824(a7)
	ld t3, 920(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1016(a7)
	ld t4, 1112(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 1208(a7)
	ld t4, 1304(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1400(a7)
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
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	addi a7, a0, 2047
	addi a7, a7, 2047
	addi a7, a7, 514
	ld t2, 56(a7)
	ld t3, 152(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 248(a7)
	ld t4, 344(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 440(a7)
	ld t4, 536(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 632(a7)
	ld t5, 728(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	ld t3, 824(a7)
	ld t4, 920(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1016(a7)
	ld t5, 1112(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	ld t4, 1208(a7)
	ld t5, 1304(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	ld t5, 1400(a7)
	ld t6, 1496(a7)
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
	sd t0, 936(s0)
	ld t0, 64(a0)
	ld t1, 160(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 256(a0)
	ld t2, 352(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 448(a0)
	ld t2, 544(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 640(a0)
	ld t3, 736(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 832(a0)
	ld t2, 928(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1024(a0)
	ld t3, 1120(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1216(a0)
	ld t3, 1312(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1408(a0)
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
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi a7, a0, 1536
	ld t1, 64(a7)
	ld t2, 160(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 256(a7)
	ld t3, 352(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 448(a7)
	ld t3, 544(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 640(a7)
	ld t4, 736(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	ld t2, 832(a7)
	ld t3, 928(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1024(a7)
	ld t4, 1120(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 1216(a7)
	ld t4, 1312(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1408(a7)
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
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a5
	xor t0, t0, t1
	addi a7, a0, 2047
	addi a7, a7, 1025
	ld t1, 64(a7)
	ld t2, 160(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 256(a7)
	ld t3, 352(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 448(a7)
	ld t3, 544(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 640(a7)
	ld t4, 736(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	ld t2, 832(a7)
	ld t3, 928(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1024(a7)
	ld t4, 1120(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 1216(a7)
	ld t4, 1312(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1408(a7)
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
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	addi a7, a0, 2047
	addi a7, a7, 2047
	addi a7, a7, 514
	ld t2, 64(a7)
	ld t3, 160(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 256(a7)
	ld t4, 352(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 448(a7)
	ld t4, 544(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 640(a7)
	ld t5, 736(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	ld t3, 832(a7)
	ld t4, 928(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1024(a7)
	ld t5, 1120(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	ld t4, 1216(a7)
	ld t5, 1312(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	ld t5, 1408(a7)
	ld t6, 1504(a7)
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
	sd t0, 944(s0)
	ld t0, 72(a0)
	ld t1, 168(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 264(a0)
	ld t2, 360(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 456(a0)
	ld t2, 552(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 648(a0)
	ld t3, 744(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 840(a0)
	ld t2, 936(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1032(a0)
	ld t3, 1128(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1224(a0)
	ld t3, 1320(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1416(a0)
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
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi a7, a0, 1536
	ld t1, 72(a7)
	ld t2, 168(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 264(a7)
	ld t3, 360(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 456(a7)
	ld t3, 552(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 648(a7)
	ld t4, 744(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	ld t2, 840(a7)
	ld t3, 936(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1032(a7)
	ld t4, 1128(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 1224(a7)
	ld t4, 1320(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1416(a7)
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
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a5
	xor t0, t0, t1
	addi a7, a0, 2047
	addi a7, a7, 1025
	ld t1, 72(a7)
	ld t2, 168(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 264(a7)
	ld t3, 360(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 456(a7)
	ld t3, 552(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 648(a7)
	ld t4, 744(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	ld t2, 840(a7)
	ld t3, 936(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1032(a7)
	ld t4, 1128(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 1224(a7)
	ld t4, 1320(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1416(a7)
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
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	addi a7, a0, 2047
	addi a7, a7, 2047
	addi a7, a7, 514
	ld t2, 72(a7)
	ld t3, 168(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 264(a7)
	ld t4, 360(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 456(a7)
	ld t4, 552(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 648(a7)
	ld t5, 744(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	ld t3, 840(a7)
	ld t4, 936(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1032(a7)
	ld t5, 1128(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	ld t4, 1224(a7)
	ld t5, 1320(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	ld t5, 1416(a7)
	ld t6, 1512(a7)
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
	sd t0, 952(s0)
	ld t0, 80(a0)
	ld t1, 176(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 272(a0)
	ld t2, 368(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 464(a0)
	ld t2, 560(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 656(a0)
	ld t3, 752(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 848(a0)
	ld t2, 944(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1040(a0)
	ld t3, 1136(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1232(a0)
	ld t3, 1328(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1424(a0)
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
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi a7, a0, 1536
	ld t1, 80(a7)
	ld t2, 176(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 272(a7)
	ld t3, 368(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 464(a7)
	ld t3, 560(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 656(a7)
	ld t4, 752(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	ld t2, 848(a7)
	ld t3, 944(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1040(a7)
	ld t4, 1136(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 1232(a7)
	ld t4, 1328(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1424(a7)
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
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a5
	xor t0, t0, t1
	addi a7, a0, 2047
	addi a7, a7, 1025
	ld t1, 80(a7)
	ld t2, 176(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 272(a7)
	ld t3, 368(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 464(a7)
	ld t3, 560(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 656(a7)
	ld t4, 752(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	ld t2, 848(a7)
	ld t3, 944(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1040(a7)
	ld t4, 1136(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 1232(a7)
	ld t4, 1328(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1424(a7)
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
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	addi a7, a0, 2047
	addi a7, a7, 2047
	addi a7, a7, 514
	ld t2, 80(a7)
	ld t3, 176(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 272(a7)
	ld t4, 368(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 464(a7)
	ld t4, 560(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 656(a7)
	ld t5, 752(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	ld t3, 848(a7)
	ld t4, 944(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1040(a7)
	ld t5, 1136(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	ld t4, 1232(a7)
	ld t5, 1328(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	ld t5, 1424(a7)
	ld t6, 1520(a7)
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
	sd t0, 960(s0)
	ld t0, 88(a0)
	ld t1, 184(a0)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 280(a0)
	ld t2, 376(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 472(a0)
	ld t2, 568(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 664(a0)
	ld t3, 760(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	ld t1, 856(a0)
	ld t2, 952(a0)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1048(a0)
	ld t3, 1144(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 1240(a0)
	ld t3, 1336(a0)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1432(a0)
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
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	addi a7, a0, 1536
	ld t1, 88(a7)
	ld t2, 184(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 280(a7)
	ld t3, 376(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 472(a7)
	ld t3, 568(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 664(a7)
	ld t4, 760(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	ld t2, 856(a7)
	ld t3, 952(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1048(a7)
	ld t4, 1144(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 1240(a7)
	ld t4, 1336(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1432(a7)
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
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a5
	xor t0, t0, t1
	addi a7, a0, 2047
	addi a7, a7, 1025
	ld t1, 88(a7)
	ld t2, 184(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 280(a7)
	ld t3, 376(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 472(a7)
	ld t3, 568(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 664(a7)
	ld t4, 760(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	ld t2, 856(a7)
	ld t3, 952(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1048(a7)
	ld t4, 1144(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 1240(a7)
	ld t4, 1336(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1432(a7)
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
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	addi a7, a0, 2047
	addi a7, a7, 2047
	addi a7, a7, 514
	ld t2, 88(a7)
	ld t3, 184(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 280(a7)
	ld t4, 376(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 472(a7)
	ld t4, 568(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 664(a7)
	ld t5, 760(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	ld t3, 856(a7)
	ld t4, 952(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1048(a7)
	ld t5, 1144(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	ld t4, 1240(a7)
	ld t5, 1336(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	ld t5, 1432(a7)
	ld t6, 1528(a7)
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
	sd t0, 968(s0)
	ld t0, 304(s0)
	sd t0, 976(s0)
	ld t0, 312(s0)
	sd t0, 984(s0)
	ld t0, 320(s0)
	sd t0, 992(s0)
	ld t0, 328(s0)
	sd t0, 1000(s0)
	ld t0, 336(s0)
	sd t0, 1008(s0)
	ld t0, 344(s0)
	sd t0, 1016(s0)
	ld a7, 1512(s0)
	ld t0, 880(s0)
	ld t1, 208(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 880(s0)
	ld t0, 888(s0)
	ld t1, 216(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 888(s0)
	ld t0, 896(s0)
	ld t1, 224(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 896(s0)
	ld t0, 904(s0)
	ld t1, 232(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 904(s0)
	ld t0, 912(s0)
	ld t1, 240(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 912(s0)
	ld t0, 920(s0)
	ld t1, 248(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 920(s0)
	ld t0, 928(s0)
	ld t1, 304(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 928(s0)
	ld t0, 936(s0)
	ld t1, 312(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 936(s0)
	ld t0, 944(s0)
	ld t1, 320(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 944(s0)
	ld t0, 952(s0)
	ld t1, 328(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 952(s0)
	ld t0, 960(s0)
	ld t1, 336(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 960(s0)
	ld t0, 968(s0)
	ld t1, 344(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 968(s0)
	ld t0, 976(s0)
	ld t1, 208(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 976(s0)
	ld t0, 984(s0)
	ld t1, 216(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 984(s0)
	ld t0, 992(s0)
	ld t1, 224(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 992(s0)
	ld t0, 1000(s0)
	ld t1, 232(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1000(s0)
	ld t0, 1008(s0)
	ld t1, 240(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1008(s0)
	ld t0, 1016(s0)
	ld t1, 248(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1016(s0)
	addi a0, s0, 0
	addi a1, zero, 1456
	addi a2, zero, 208
	addi a3, zero, 928
	call {vg_p384_sub_mod_p}
	ld a7, 1504(s0)
	ld t0, 928(s0)
	ld t1, 1456(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 928(s0)
	ld t0, 936(s0)
	ld t1, 1464(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 936(s0)
	ld t0, 944(s0)
	ld t1, 1472(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 944(s0)
	ld t0, 952(s0)
	ld t1, 1480(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 952(s0)
	ld t0, 960(s0)
	ld t1, 1488(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 960(s0)
	ld t0, 968(s0)
	ld t1, 1496(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 968(s0)
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 736
	addi a3, zero, 880
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 784
	addi a3, zero, 928
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 832
	addi a3, zero, 976
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 736
	addi a3, zero, 784
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 880
	addi a3, zero, 928
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1168
	addi a3, zero, 1216
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1312
	addi a2, zero, 1312
	addi a3, zero, 1360
	call {vg_p384_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 784
	addi a3, zero, 832
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 928
	addi a3, zero, 976
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1024
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 1024
	call {vg_p384_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 736
	addi a3, zero, 832
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 880
	addi a3, zero, 976
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1072
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1024
	addi a3, zero, 1072
	call {vg_p384_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1984
	addi a3, zero, 1264
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1072
	addi a3, zero, 1120
	call {vg_p384_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1024
	addi a3, zero, 1024
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1216
	addi a3, zero, 1024
	call {vg_p384_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1216
	addi a3, zero, 1024
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1984
	addi a3, zero, 1072
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1264
	addi a3, zero, 1264
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1216
	addi a3, zero, 1264
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1072
	addi a3, zero, 1264
	call {vg_p384_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1072
	addi a3, zero, 1168
	call {vg_p384_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1072
	addi a3, zero, 1072
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1216
	addi a3, zero, 1072
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1168
	addi a3, zero, 1168
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1216
	addi a3, zero, 1168
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1168
	addi a2, zero, 1168
	addi a3, zero, 1264
	call {vg_p384_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1360
	addi a3, zero, 1072
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1264
	addi a2, zero, 1168
	addi a3, zero, 1072
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1024
	addi a3, zero, 1120
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1072
	addi a3, zero, 1264
	call {vg_p384_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1312
	addi a3, zero, 1024
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1024
	addi a2, zero, 1024
	addi a3, zero, 1216
	call {vg_p384_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1360
	addi a3, zero, 1120
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1312
	addi a3, zero, 1168
	call {vg_p384_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1120
	addi a2, zero, 1120
	addi a3, zero, 1216
	call {vg_p384_add_mod_p}
	ld t0, 1024(s0)
	sd t0, 736(s0)
	ld t0, 1032(s0)
	sd t0, 744(s0)
	ld t0, 1040(s0)
	sd t0, 752(s0)
	ld t0, 1048(s0)
	sd t0, 760(s0)
	ld t0, 1056(s0)
	sd t0, 768(s0)
	ld t0, 1064(s0)
	sd t0, 776(s0)
	ld t0, 1072(s0)
	sd t0, 784(s0)
	ld t0, 1080(s0)
	sd t0, 792(s0)
	ld t0, 1088(s0)
	sd t0, 800(s0)
	ld t0, 1096(s0)
	sd t0, 808(s0)
	ld t0, 1104(s0)
	sd t0, 816(s0)
	ld t0, 1112(s0)
	sd t0, 824(s0)
	ld t0, 1120(s0)
	sd t0, 832(s0)
	ld t0, 1128(s0)
	sd t0, 840(s0)
	ld t0, 1136(s0)
	sd t0, 848(s0)
	ld t0, 1144(s0)
	sd t0, 856(s0)
	ld t0, 1152(s0)
	sd t0, 864(s0)
	ld t0, 1160(s0)
	sd t0, 872(s0)
	bnez s1, 20b
	addi ra, s0, 2047
	ld ra, 193(ra)
	addi s4, s0, 2047
	ld s4, 201(s4)
	addi s1, s0, 2047
	ld s1, 185(s1)
	addi s0, s0, 2047
	ld s0, 177(s0)
	ret
	.option pop
