// The functions of `src/internal/vg_p521_mul_g.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p521_mul_g:
	.option push
	.option arch, +m, +c
	lla t0, {VG_P521_COMB}
	addi a0, a0, 2047
	sd s0, 1257(a0)
	addi a0, a0, -2047
	addi a0, a0, 2047
	sd s1, 1265(a0)
	addi a0, a0, -2047
	addi a0, a0, 2047
	sd ra, 1273(a0)
	addi a0, a0, -2047
	addi a0, a0, 2047
	sd s4, 1281(a0)
	addi a0, a0, -2047
	addi s0, a0, 0
	addi s4, t0, 0
	addi t0, s0, 2047
	ld t0, 249(t0)
	addi s0, s0, 2047
	sd t0, 1329(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 257(t0)
	addi s0, s0, 2047
	sd t0, 1337(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 265(t0)
	addi s0, s0, 2047
	sd t0, 1345(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 273(t0)
	addi s0, s0, 2047
	sd t0, 1353(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 281(t0)
	addi s0, s0, 2047
	sd t0, 1361(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 289(t0)
	addi s0, s0, 2047
	sd t0, 1369(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 297(t0)
	addi s0, s0, 2047
	sd t0, 1377(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 305(t0)
	addi s0, s0, 2047
	sd t0, 1385(s0)
	addi s0, s0, -2047
	addi t0, s0, 2047
	ld t0, 313(t0)
	addi s0, s0, 2047
	sd t0, 1393(s0)
	addi s0, s0, -2047
	addi t0, zero, 0
	addi s0, s0, 2047
	sd t0, 1401(s0)
	addi s0, s0, -2047
	lui t0, 883082
	addiw t0, t0, 648
	slli t0, t0, 32
	lui t1, 938543
	addiw t1, t1, 150
	add t0, t0, t1
	sd t0, 1072(s0)
	lui t0, 899487
	addiw t0, t0, -1038
	slli t0, t0, 32
	lui t1, 11525
	addiw t1, t1, -1965
	add t0, t0, t1
	sd t0, 1080(s0)
	lui t0, 664380
	addiw t0, t0, -1883
	slli t0, t0, 32
	lui t1, 279158
	addiw t1, t1, -34
	add t0, t0, t1
	sd t0, 1088(s0)
	lui t0, 858150
	addiw t0, t0, -1120
	slli t0, t0, 32
	lui t1, 78740
	addiw t1, t1, -434
	add t0, t0, t1
	sd t0, 1096(s0)
	lui t0, 522118
	addiw t0, t0, 1439
	slli t0, t0, 32
	lui t1, 459077
	addiw t1, t1, -333
	add t0, t0, t1
	sd t0, 1104(s0)
	lui t0, 889780
	addiw t0, t0, -125
	slli t0, t0, 32
	lui t1, 688412
	addiw t1, t1, 376
	add t0, t0, t1
	sd t0, 1112(s0)
	lui t0, 533426
	addiw t0, t0, 1545
	slli t0, t0, 32
	lui t1, 596663
	addiw t1, t1, 261
	add t0, t0, t1
	sd t0, 1120(s0)
	lui t0, 198821
	addiw t0, t0, 741
	slli t0, t0, 32
	lui t1, 586808
	addiw t1, t1, 336
	add t0, t0, t1
	sd t0, 1128(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 458
	add t0, t0, t1
	sd t0, 1136(s0)
	lui t0, 307423
	addiw t0, t0, 1942
	slli t0, t0, 32
	lui t1, 375570
	addiw t1, t1, 2024
	add t0, t0, t1
	sd t0, 1144(s0)
	lui t0, 1033346
	addiw t0, t0, -795
	slli t0, t0, 32
	lui t1, 88327
	addiw t1, t1, -1608
	add t0, t0, t1
	sd t0, 1152(s0)
	lui t0, 543476
	addiw t0, t0, 1299
	slli t0, t0, 32
	lui t1, 7590
	addiw t1, t1, -1934
	add t0, t0, t1
	sd t0, 1160(s0)
	lui t0, 489680
	addiw t0, t0, 900
	slli t0, t0, 32
	lui t1, 589217
	addiw t1, t1, 276
	add t0, t0, t1
	sd t0, 1168(s0)
	lui t0, 239477
	addiw t0, t0, -960
	slli t0, t0, 32
	lui t1, 1016104
	addiw t1, t1, -486
	add t0, t0, t1
	sd t0, 1176(s0)
	lui t0, 628976
	addiw t0, t0, -1458
	slli t0, t0, 32
	lui t1, 27283
	addiw t1, t1, 1323
	add t0, t0, t1
	sd t0, 1184(s0)
	lui t0, 806600
	addiw t0, t0, 2038
	slli t0, t0, 32
	lui t1, 1044228
	addiw t1, t1, 1828
	add t0, t0, t1
	sd t0, 1192(s0)
	lui t0, 920102
	addiw t0, t0, 854
	slli t0, t0, 32
	lui t1, 962345
	addiw t1, t1, -617
	add t0, t0, t1
	sd t0, 1200(s0)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 209
	add t0, t0, t1
	sd t0, 1208(s0)
	ld t0, 280(s0)
	addi s0, s0, 2047
	sd t0, 1761(s0)
	addi s0, s0, -2047
	ld t0, 288(s0)
	addi s0, s0, 2047
	sd t0, 1769(s0)
	addi s0, s0, -2047
	ld t0, 296(s0)
	addi s0, s0, 2047
	sd t0, 1777(s0)
	addi s0, s0, -2047
	ld t0, 304(s0)
	addi s0, s0, 2047
	sd t0, 1785(s0)
	addi s0, s0, -2047
	ld t0, 312(s0)
	addi s0, s0, 2047
	sd t0, 1793(s0)
	addi s0, s0, -2047
	ld t0, 320(s0)
	addi s0, s0, 2047
	sd t0, 1801(s0)
	addi s0, s0, -2047
	ld t0, 328(s0)
	addi s0, s0, 2047
	sd t0, 1809(s0)
	addi s0, s0, -2047
	ld t0, 336(s0)
	addi s0, s0, 2047
	sd t0, 1817(s0)
	addi s0, s0, -2047
	ld t0, 344(s0)
	addi s0, s0, 2047
	sd t0, 1825(s0)
	addi s0, s0, -2047
	addi t0, zero, 4
	addi s0, s0, 2047
	sd t0, 1825(s0)
	addi s0, s0, -2047
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1072
	addi a3, zero, 0
	call {vg_p521u_unpack_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1072
	addi a3, zero, 2047
	addi a3, a3, 1761
	call {vg_p521u_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 0
	call {vg_p521u_unpack_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 2047
	addi a3, a3, 1761
	call {vg_p521u_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1689
	addi a2, zero, 424
	addi a3, zero, 0
	call {vg_p521u_unpack_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1689
	addi a2, zero, 2047
	addi a2, a2, 1689
	addi a3, zero, 2047
	addi a3, a3, 1761
	call {vg_p521u_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1545
	addi a2, zero, 496
	addi a3, zero, 0
	call {vg_p521u_unpack_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1545
	addi a2, zero, 2047
	addi a2, a2, 1545
	addi a3, zero, 2047
	addi a3, a3, 1761
	call {vg_p521u_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1617
	addi a2, zero, 568
	addi a3, zero, 0
	call {vg_p521u_unpack_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 1617
	addi a2, zero, 2047
	addi a2, a2, 1617
	addi a3, zero, 2047
	addi a3, a3, 1761
	call {vg_p521u_mul_mod_p}
	addi t0, s0, 2047
	ld t0, 1689(t0)
	sd t0, 1216(s0)
	addi t0, s0, 2047
	ld t0, 1697(t0)
	sd t0, 1224(s0)
	addi t0, s0, 2047
	ld t0, 1705(t0)
	sd t0, 1232(s0)
	addi t0, s0, 2047
	ld t0, 1713(t0)
	sd t0, 1240(s0)
	addi t0, s0, 2047
	ld t0, 1721(t0)
	sd t0, 1248(s0)
	addi t0, s0, 2047
	ld t0, 1729(t0)
	sd t0, 1256(s0)
	addi t0, s0, 2047
	ld t0, 1737(t0)
	sd t0, 1264(s0)
	addi t0, s0, 2047
	ld t0, 1745(t0)
	sd t0, 1272(s0)
	addi t0, s0, 2047
	ld t0, 1753(t0)
	sd t0, 1280(s0)
	addi s1, zero, 83
20:
	addi s1, s1, -1
	slli t0, s1, 3
	sub t0, t0, s1
	srli t1, t0, 6
	slli t1, t1, 3
	add t1, t1, s0
	addi t2, t1, 2047
	ld t2, 1329(t2)
	addi t3, t1, 2047
	ld t3, 1337(t3)
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
	addi s0, s0, 2047
	sd t3, 1409(s0)
	addi s0, s0, -2047
	addi s0, s0, 2047
	sd t4, 1417(s0)
	addi s0, s0, -2047
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
	slli t0, s1, 13
	slli t1, s1, 10
	add t0, t0, t1
	add a0, s4, t0
	addi a7, a0, 0
	ld t0, 0(a7)
	ld t1, 144(a7)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 288(a7)
	ld t2, 432(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 576(a7)
	ld t2, 720(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 864(a7)
	ld t3, 1008(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	addi a7, a7, 1152
	ld t1, 0(a7)
	ld t2, 144(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 288(a7)
	ld t3, 432(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 576(a7)
	ld t3, 720(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 864(a7)
	ld t4, 1008(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	ld t1, 0(a7)
	ld t2, 144(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 288(a7)
	ld t3, 432(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 576(a7)
	ld t3, 720(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 864(a7)
	ld t4, 1008(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	ld t2, 0(a7)
	ld t3, 144(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 288(a7)
	ld t4, 432(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 576(a7)
	ld t4, 720(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 864(a7)
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
	addi a7, a7, 1152
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a5
	xor t0, t0, t1
	ld t1, 0(a7)
	ld t2, 144(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 288(a7)
	ld t3, 432(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 576(a7)
	ld t3, 720(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 864(a7)
	ld t4, 1008(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	ld t2, 0(a7)
	ld t3, 144(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 288(a7)
	ld t4, 432(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 576(a7)
	ld t4, 720(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 864(a7)
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
	addi a7, a7, 1152
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	ld t2, 0(a7)
	ld t3, 144(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 288(a7)
	ld t4, 432(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 576(a7)
	ld t4, 720(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 864(a7)
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
	addi a7, a7, 1152
	ld t3, 0(a7)
	ld t4, 144(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 288(a7)
	ld t5, 432(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	ld t4, 576(a7)
	ld t5, 720(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	ld t5, 864(a7)
	ld t6, 1008(a7)
	xor t6, t6, t5
	and t6, t6, a1
	xor t5, t5, t6
	xor t5, t5, t4
	and t5, t5, a2
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a3
	xor t3, t3, t4
	addi a7, a7, 1152
	xor t3, t3, t2
	and t3, t3, a4
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a5
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a6
	xor t0, t0, t1
	sd t0, 1288(s0)
	addi a7, a0, 0
	ld t0, 8(a7)
	ld t1, 152(a7)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 296(a7)
	ld t2, 440(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 584(a7)
	ld t2, 728(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 872(a7)
	ld t3, 1016(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	addi a7, a7, 1152
	ld t1, 8(a7)
	ld t2, 152(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 296(a7)
	ld t3, 440(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 584(a7)
	ld t3, 728(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 872(a7)
	ld t4, 1016(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	ld t1, 8(a7)
	ld t2, 152(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 296(a7)
	ld t3, 440(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 584(a7)
	ld t3, 728(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 872(a7)
	ld t4, 1016(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	ld t2, 8(a7)
	ld t3, 152(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 296(a7)
	ld t4, 440(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 584(a7)
	ld t4, 728(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 872(a7)
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
	addi a7, a7, 1152
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a5
	xor t0, t0, t1
	ld t1, 8(a7)
	ld t2, 152(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 296(a7)
	ld t3, 440(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 584(a7)
	ld t3, 728(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 872(a7)
	ld t4, 1016(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	ld t2, 8(a7)
	ld t3, 152(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 296(a7)
	ld t4, 440(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 584(a7)
	ld t4, 728(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 872(a7)
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
	addi a7, a7, 1152
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	ld t2, 8(a7)
	ld t3, 152(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 296(a7)
	ld t4, 440(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 584(a7)
	ld t4, 728(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 872(a7)
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
	addi a7, a7, 1152
	ld t3, 8(a7)
	ld t4, 152(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 296(a7)
	ld t5, 440(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	ld t4, 584(a7)
	ld t5, 728(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	ld t5, 872(a7)
	ld t6, 1016(a7)
	xor t6, t6, t5
	and t6, t6, a1
	xor t5, t5, t6
	xor t5, t5, t4
	and t5, t5, a2
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a3
	xor t3, t3, t4
	addi a7, a7, 1152
	xor t3, t3, t2
	and t3, t3, a4
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a5
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a6
	xor t0, t0, t1
	sd t0, 1296(s0)
	addi a7, a0, 0
	ld t0, 16(a7)
	ld t1, 160(a7)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 304(a7)
	ld t2, 448(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 592(a7)
	ld t2, 736(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 880(a7)
	ld t3, 1024(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	addi a7, a7, 1152
	ld t1, 16(a7)
	ld t2, 160(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 304(a7)
	ld t3, 448(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 592(a7)
	ld t3, 736(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 880(a7)
	ld t4, 1024(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	ld t1, 16(a7)
	ld t2, 160(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 304(a7)
	ld t3, 448(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 592(a7)
	ld t3, 736(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 880(a7)
	ld t4, 1024(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	ld t2, 16(a7)
	ld t3, 160(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 304(a7)
	ld t4, 448(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 592(a7)
	ld t4, 736(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 880(a7)
	ld t5, 1024(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a5
	xor t0, t0, t1
	ld t1, 16(a7)
	ld t2, 160(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 304(a7)
	ld t3, 448(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 592(a7)
	ld t3, 736(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 880(a7)
	ld t4, 1024(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	ld t2, 16(a7)
	ld t3, 160(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 304(a7)
	ld t4, 448(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 592(a7)
	ld t4, 736(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 880(a7)
	ld t5, 1024(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	ld t2, 16(a7)
	ld t3, 160(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 304(a7)
	ld t4, 448(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 592(a7)
	ld t4, 736(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 880(a7)
	ld t5, 1024(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	ld t3, 16(a7)
	ld t4, 160(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 304(a7)
	ld t5, 448(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	ld t4, 592(a7)
	ld t5, 736(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	ld t5, 880(a7)
	ld t6, 1024(a7)
	xor t6, t6, t5
	and t6, t6, a1
	xor t5, t5, t6
	xor t5, t5, t4
	and t5, t5, a2
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a3
	xor t3, t3, t4
	addi a7, a7, 1152
	xor t3, t3, t2
	and t3, t3, a4
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a5
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a6
	xor t0, t0, t1
	sd t0, 1304(s0)
	addi a7, a0, 0
	ld t0, 24(a7)
	ld t1, 168(a7)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 312(a7)
	ld t2, 456(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 600(a7)
	ld t2, 744(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 888(a7)
	ld t3, 1032(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	addi a7, a7, 1152
	ld t1, 24(a7)
	ld t2, 168(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 312(a7)
	ld t3, 456(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 600(a7)
	ld t3, 744(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 888(a7)
	ld t4, 1032(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	ld t1, 24(a7)
	ld t2, 168(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 312(a7)
	ld t3, 456(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 600(a7)
	ld t3, 744(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 888(a7)
	ld t4, 1032(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	ld t2, 24(a7)
	ld t3, 168(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 312(a7)
	ld t4, 456(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 600(a7)
	ld t4, 744(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 888(a7)
	ld t5, 1032(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a5
	xor t0, t0, t1
	ld t1, 24(a7)
	ld t2, 168(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 312(a7)
	ld t3, 456(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 600(a7)
	ld t3, 744(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 888(a7)
	ld t4, 1032(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	ld t2, 24(a7)
	ld t3, 168(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 312(a7)
	ld t4, 456(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 600(a7)
	ld t4, 744(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 888(a7)
	ld t5, 1032(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	ld t2, 24(a7)
	ld t3, 168(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 312(a7)
	ld t4, 456(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 600(a7)
	ld t4, 744(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 888(a7)
	ld t5, 1032(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	ld t3, 24(a7)
	ld t4, 168(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 312(a7)
	ld t5, 456(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	ld t4, 600(a7)
	ld t5, 744(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	ld t5, 888(a7)
	ld t6, 1032(a7)
	xor t6, t6, t5
	and t6, t6, a1
	xor t5, t5, t6
	xor t5, t5, t4
	and t5, t5, a2
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a3
	xor t3, t3, t4
	addi a7, a7, 1152
	xor t3, t3, t2
	and t3, t3, a4
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a5
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a6
	xor t0, t0, t1
	sd t0, 1312(s0)
	addi a7, a0, 0
	ld t0, 32(a7)
	ld t1, 176(a7)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 320(a7)
	ld t2, 464(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 608(a7)
	ld t2, 752(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 896(a7)
	ld t3, 1040(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	addi a7, a7, 1152
	ld t1, 32(a7)
	ld t2, 176(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 320(a7)
	ld t3, 464(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 608(a7)
	ld t3, 752(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 896(a7)
	ld t4, 1040(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	ld t1, 32(a7)
	ld t2, 176(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 320(a7)
	ld t3, 464(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 608(a7)
	ld t3, 752(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 896(a7)
	ld t4, 1040(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	ld t2, 32(a7)
	ld t3, 176(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 320(a7)
	ld t4, 464(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 608(a7)
	ld t4, 752(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 896(a7)
	ld t5, 1040(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a5
	xor t0, t0, t1
	ld t1, 32(a7)
	ld t2, 176(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 320(a7)
	ld t3, 464(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 608(a7)
	ld t3, 752(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 896(a7)
	ld t4, 1040(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	ld t2, 32(a7)
	ld t3, 176(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 320(a7)
	ld t4, 464(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 608(a7)
	ld t4, 752(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 896(a7)
	ld t5, 1040(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	ld t2, 32(a7)
	ld t3, 176(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 320(a7)
	ld t4, 464(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 608(a7)
	ld t4, 752(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 896(a7)
	ld t5, 1040(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	ld t3, 32(a7)
	ld t4, 176(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 320(a7)
	ld t5, 464(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	ld t4, 608(a7)
	ld t5, 752(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	ld t5, 896(a7)
	ld t6, 1040(a7)
	xor t6, t6, t5
	and t6, t6, a1
	xor t5, t5, t6
	xor t5, t5, t4
	and t5, t5, a2
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a3
	xor t3, t3, t4
	addi a7, a7, 1152
	xor t3, t3, t2
	and t3, t3, a4
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a5
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a6
	xor t0, t0, t1
	sd t0, 1320(s0)
	addi a7, a0, 0
	ld t0, 40(a7)
	ld t1, 184(a7)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 328(a7)
	ld t2, 472(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 616(a7)
	ld t2, 760(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 904(a7)
	ld t3, 1048(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	addi a7, a7, 1152
	ld t1, 40(a7)
	ld t2, 184(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 328(a7)
	ld t3, 472(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 616(a7)
	ld t3, 760(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 904(a7)
	ld t4, 1048(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	ld t1, 40(a7)
	ld t2, 184(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 328(a7)
	ld t3, 472(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 616(a7)
	ld t3, 760(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 904(a7)
	ld t4, 1048(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	ld t2, 40(a7)
	ld t3, 184(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 328(a7)
	ld t4, 472(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 616(a7)
	ld t4, 760(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 904(a7)
	ld t5, 1048(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a5
	xor t0, t0, t1
	ld t1, 40(a7)
	ld t2, 184(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 328(a7)
	ld t3, 472(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 616(a7)
	ld t3, 760(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 904(a7)
	ld t4, 1048(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	ld t2, 40(a7)
	ld t3, 184(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 328(a7)
	ld t4, 472(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 616(a7)
	ld t4, 760(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 904(a7)
	ld t5, 1048(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	ld t2, 40(a7)
	ld t3, 184(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 328(a7)
	ld t4, 472(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 616(a7)
	ld t4, 760(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 904(a7)
	ld t5, 1048(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	ld t3, 40(a7)
	ld t4, 184(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 328(a7)
	ld t5, 472(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	ld t4, 616(a7)
	ld t5, 760(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	ld t5, 904(a7)
	ld t6, 1048(a7)
	xor t6, t6, t5
	and t6, t6, a1
	xor t5, t5, t6
	xor t5, t5, t4
	and t5, t5, a2
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a3
	xor t3, t3, t4
	addi a7, a7, 1152
	xor t3, t3, t2
	and t3, t3, a4
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a5
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a6
	xor t0, t0, t1
	sd t0, 1328(s0)
	addi a7, a0, 0
	ld t0, 48(a7)
	ld t1, 192(a7)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 336(a7)
	ld t2, 480(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 624(a7)
	ld t2, 768(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 912(a7)
	ld t3, 1056(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	addi a7, a7, 1152
	ld t1, 48(a7)
	ld t2, 192(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 336(a7)
	ld t3, 480(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 624(a7)
	ld t3, 768(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 912(a7)
	ld t4, 1056(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	ld t1, 48(a7)
	ld t2, 192(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 336(a7)
	ld t3, 480(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 624(a7)
	ld t3, 768(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 912(a7)
	ld t4, 1056(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	ld t2, 48(a7)
	ld t3, 192(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 336(a7)
	ld t4, 480(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 624(a7)
	ld t4, 768(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 912(a7)
	ld t5, 1056(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a5
	xor t0, t0, t1
	ld t1, 48(a7)
	ld t2, 192(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 336(a7)
	ld t3, 480(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 624(a7)
	ld t3, 768(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 912(a7)
	ld t4, 1056(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	ld t2, 48(a7)
	ld t3, 192(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 336(a7)
	ld t4, 480(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 624(a7)
	ld t4, 768(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 912(a7)
	ld t5, 1056(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	ld t2, 48(a7)
	ld t3, 192(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 336(a7)
	ld t4, 480(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 624(a7)
	ld t4, 768(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 912(a7)
	ld t5, 1056(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	ld t3, 48(a7)
	ld t4, 192(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 336(a7)
	ld t5, 480(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	ld t4, 624(a7)
	ld t5, 768(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	ld t5, 912(a7)
	ld t6, 1056(a7)
	xor t6, t6, t5
	and t6, t6, a1
	xor t5, t5, t6
	xor t5, t5, t4
	and t5, t5, a2
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a3
	xor t3, t3, t4
	addi a7, a7, 1152
	xor t3, t3, t2
	and t3, t3, a4
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a5
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a6
	xor t0, t0, t1
	sd t0, 1336(s0)
	addi a7, a0, 0
	ld t0, 56(a7)
	ld t1, 200(a7)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 344(a7)
	ld t2, 488(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 632(a7)
	ld t2, 776(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 920(a7)
	ld t3, 1064(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	addi a7, a7, 1152
	ld t1, 56(a7)
	ld t2, 200(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 344(a7)
	ld t3, 488(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 632(a7)
	ld t3, 776(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 920(a7)
	ld t4, 1064(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	ld t1, 56(a7)
	ld t2, 200(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 344(a7)
	ld t3, 488(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 632(a7)
	ld t3, 776(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 920(a7)
	ld t4, 1064(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	ld t2, 56(a7)
	ld t3, 200(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 344(a7)
	ld t4, 488(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 632(a7)
	ld t4, 776(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 920(a7)
	ld t5, 1064(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a5
	xor t0, t0, t1
	ld t1, 56(a7)
	ld t2, 200(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 344(a7)
	ld t3, 488(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 632(a7)
	ld t3, 776(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 920(a7)
	ld t4, 1064(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	ld t2, 56(a7)
	ld t3, 200(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 344(a7)
	ld t4, 488(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 632(a7)
	ld t4, 776(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 920(a7)
	ld t5, 1064(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	ld t2, 56(a7)
	ld t3, 200(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 344(a7)
	ld t4, 488(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 632(a7)
	ld t4, 776(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 920(a7)
	ld t5, 1064(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	ld t3, 56(a7)
	ld t4, 200(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 344(a7)
	ld t5, 488(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	ld t4, 632(a7)
	ld t5, 776(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	ld t5, 920(a7)
	ld t6, 1064(a7)
	xor t6, t6, t5
	and t6, t6, a1
	xor t5, t5, t6
	xor t5, t5, t4
	and t5, t5, a2
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a3
	xor t3, t3, t4
	addi a7, a7, 1152
	xor t3, t3, t2
	and t3, t3, a4
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a5
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a6
	xor t0, t0, t1
	sd t0, 1344(s0)
	addi a7, a0, 0
	ld t0, 64(a7)
	ld t1, 208(a7)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 352(a7)
	ld t2, 496(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 640(a7)
	ld t2, 784(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 928(a7)
	ld t3, 1072(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	addi a7, a7, 1152
	ld t1, 64(a7)
	ld t2, 208(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 352(a7)
	ld t3, 496(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 640(a7)
	ld t3, 784(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 928(a7)
	ld t4, 1072(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	ld t1, 64(a7)
	ld t2, 208(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 352(a7)
	ld t3, 496(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 640(a7)
	ld t3, 784(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 928(a7)
	ld t4, 1072(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	ld t2, 64(a7)
	ld t3, 208(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 352(a7)
	ld t4, 496(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 640(a7)
	ld t4, 784(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 928(a7)
	ld t5, 1072(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a5
	xor t0, t0, t1
	ld t1, 64(a7)
	ld t2, 208(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 352(a7)
	ld t3, 496(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 640(a7)
	ld t3, 784(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 928(a7)
	ld t4, 1072(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	ld t2, 64(a7)
	ld t3, 208(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 352(a7)
	ld t4, 496(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 640(a7)
	ld t4, 784(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 928(a7)
	ld t5, 1072(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	ld t2, 64(a7)
	ld t3, 208(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 352(a7)
	ld t4, 496(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 640(a7)
	ld t4, 784(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 928(a7)
	ld t5, 1072(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	ld t3, 64(a7)
	ld t4, 208(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 352(a7)
	ld t5, 496(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	ld t4, 640(a7)
	ld t5, 784(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	ld t5, 928(a7)
	ld t6, 1072(a7)
	xor t6, t6, t5
	and t6, t6, a1
	xor t5, t5, t6
	xor t5, t5, t4
	and t5, t5, a2
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a3
	xor t3, t3, t4
	addi a7, a7, 1152
	xor t3, t3, t2
	and t3, t3, a4
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a5
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a6
	xor t0, t0, t1
	sd t0, 1352(s0)
	addi a7, a0, 0
	ld t0, 72(a7)
	ld t1, 216(a7)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 360(a7)
	ld t2, 504(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 648(a7)
	ld t2, 792(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 936(a7)
	ld t3, 1080(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	addi a7, a7, 1152
	ld t1, 72(a7)
	ld t2, 216(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 360(a7)
	ld t3, 504(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 648(a7)
	ld t3, 792(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 936(a7)
	ld t4, 1080(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	ld t1, 72(a7)
	ld t2, 216(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 360(a7)
	ld t3, 504(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 648(a7)
	ld t3, 792(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 936(a7)
	ld t4, 1080(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	ld t2, 72(a7)
	ld t3, 216(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 360(a7)
	ld t4, 504(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 648(a7)
	ld t4, 792(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 936(a7)
	ld t5, 1080(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a5
	xor t0, t0, t1
	ld t1, 72(a7)
	ld t2, 216(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 360(a7)
	ld t3, 504(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 648(a7)
	ld t3, 792(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 936(a7)
	ld t4, 1080(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	ld t2, 72(a7)
	ld t3, 216(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 360(a7)
	ld t4, 504(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 648(a7)
	ld t4, 792(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 936(a7)
	ld t5, 1080(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	ld t2, 72(a7)
	ld t3, 216(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 360(a7)
	ld t4, 504(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 648(a7)
	ld t4, 792(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 936(a7)
	ld t5, 1080(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	ld t3, 72(a7)
	ld t4, 216(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 360(a7)
	ld t5, 504(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	ld t4, 648(a7)
	ld t5, 792(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	ld t5, 936(a7)
	ld t6, 1080(a7)
	xor t6, t6, t5
	and t6, t6, a1
	xor t5, t5, t6
	xor t5, t5, t4
	and t5, t5, a2
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a3
	xor t3, t3, t4
	addi a7, a7, 1152
	xor t3, t3, t2
	and t3, t3, a4
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a5
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a6
	xor t0, t0, t1
	sd t0, 1360(s0)
	addi a7, a0, 0
	ld t0, 80(a7)
	ld t1, 224(a7)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 368(a7)
	ld t2, 512(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 656(a7)
	ld t2, 800(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 944(a7)
	ld t3, 1088(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	addi a7, a7, 1152
	ld t1, 80(a7)
	ld t2, 224(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 368(a7)
	ld t3, 512(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 656(a7)
	ld t3, 800(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 944(a7)
	ld t4, 1088(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	ld t1, 80(a7)
	ld t2, 224(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 368(a7)
	ld t3, 512(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 656(a7)
	ld t3, 800(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 944(a7)
	ld t4, 1088(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	ld t2, 80(a7)
	ld t3, 224(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 368(a7)
	ld t4, 512(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 656(a7)
	ld t4, 800(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 944(a7)
	ld t5, 1088(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a5
	xor t0, t0, t1
	ld t1, 80(a7)
	ld t2, 224(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 368(a7)
	ld t3, 512(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 656(a7)
	ld t3, 800(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 944(a7)
	ld t4, 1088(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	ld t2, 80(a7)
	ld t3, 224(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 368(a7)
	ld t4, 512(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 656(a7)
	ld t4, 800(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 944(a7)
	ld t5, 1088(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	ld t2, 80(a7)
	ld t3, 224(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 368(a7)
	ld t4, 512(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 656(a7)
	ld t4, 800(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 944(a7)
	ld t5, 1088(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	ld t3, 80(a7)
	ld t4, 224(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 368(a7)
	ld t5, 512(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	ld t4, 656(a7)
	ld t5, 800(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	ld t5, 944(a7)
	ld t6, 1088(a7)
	xor t6, t6, t5
	and t6, t6, a1
	xor t5, t5, t6
	xor t5, t5, t4
	and t5, t5, a2
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a3
	xor t3, t3, t4
	addi a7, a7, 1152
	xor t3, t3, t2
	and t3, t3, a4
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a5
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a6
	xor t0, t0, t1
	sd t0, 1368(s0)
	addi a7, a0, 0
	ld t0, 88(a7)
	ld t1, 232(a7)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 376(a7)
	ld t2, 520(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 664(a7)
	ld t2, 808(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 952(a7)
	ld t3, 1096(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	addi a7, a7, 1152
	ld t1, 88(a7)
	ld t2, 232(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 376(a7)
	ld t3, 520(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 664(a7)
	ld t3, 808(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 952(a7)
	ld t4, 1096(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	ld t1, 88(a7)
	ld t2, 232(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 376(a7)
	ld t3, 520(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 664(a7)
	ld t3, 808(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 952(a7)
	ld t4, 1096(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	ld t2, 88(a7)
	ld t3, 232(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 376(a7)
	ld t4, 520(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 664(a7)
	ld t4, 808(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 952(a7)
	ld t5, 1096(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a5
	xor t0, t0, t1
	ld t1, 88(a7)
	ld t2, 232(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 376(a7)
	ld t3, 520(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 664(a7)
	ld t3, 808(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 952(a7)
	ld t4, 1096(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	ld t2, 88(a7)
	ld t3, 232(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 376(a7)
	ld t4, 520(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 664(a7)
	ld t4, 808(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 952(a7)
	ld t5, 1096(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	ld t2, 88(a7)
	ld t3, 232(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 376(a7)
	ld t4, 520(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 664(a7)
	ld t4, 808(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 952(a7)
	ld t5, 1096(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	ld t3, 88(a7)
	ld t4, 232(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 376(a7)
	ld t5, 520(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	ld t4, 664(a7)
	ld t5, 808(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	ld t5, 952(a7)
	ld t6, 1096(a7)
	xor t6, t6, t5
	and t6, t6, a1
	xor t5, t5, t6
	xor t5, t5, t4
	and t5, t5, a2
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a3
	xor t3, t3, t4
	addi a7, a7, 1152
	xor t3, t3, t2
	and t3, t3, a4
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a5
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a6
	xor t0, t0, t1
	sd t0, 1376(s0)
	addi a7, a0, 0
	ld t0, 96(a7)
	ld t1, 240(a7)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 384(a7)
	ld t2, 528(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 672(a7)
	ld t2, 816(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 960(a7)
	ld t3, 1104(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	addi a7, a7, 1152
	ld t1, 96(a7)
	ld t2, 240(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 384(a7)
	ld t3, 528(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 672(a7)
	ld t3, 816(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 960(a7)
	ld t4, 1104(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	ld t1, 96(a7)
	ld t2, 240(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 384(a7)
	ld t3, 528(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 672(a7)
	ld t3, 816(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 960(a7)
	ld t4, 1104(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	ld t2, 96(a7)
	ld t3, 240(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 384(a7)
	ld t4, 528(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 672(a7)
	ld t4, 816(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 960(a7)
	ld t5, 1104(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a5
	xor t0, t0, t1
	ld t1, 96(a7)
	ld t2, 240(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 384(a7)
	ld t3, 528(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 672(a7)
	ld t3, 816(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 960(a7)
	ld t4, 1104(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	ld t2, 96(a7)
	ld t3, 240(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 384(a7)
	ld t4, 528(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 672(a7)
	ld t4, 816(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 960(a7)
	ld t5, 1104(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	ld t2, 96(a7)
	ld t3, 240(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 384(a7)
	ld t4, 528(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 672(a7)
	ld t4, 816(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 960(a7)
	ld t5, 1104(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	ld t3, 96(a7)
	ld t4, 240(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 384(a7)
	ld t5, 528(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	ld t4, 672(a7)
	ld t5, 816(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	ld t5, 960(a7)
	ld t6, 1104(a7)
	xor t6, t6, t5
	and t6, t6, a1
	xor t5, t5, t6
	xor t5, t5, t4
	and t5, t5, a2
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a3
	xor t3, t3, t4
	addi a7, a7, 1152
	xor t3, t3, t2
	and t3, t3, a4
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a5
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a6
	xor t0, t0, t1
	sd t0, 1384(s0)
	addi a7, a0, 0
	ld t0, 104(a7)
	ld t1, 248(a7)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 392(a7)
	ld t2, 536(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 680(a7)
	ld t2, 824(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 968(a7)
	ld t3, 1112(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	addi a7, a7, 1152
	ld t1, 104(a7)
	ld t2, 248(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 392(a7)
	ld t3, 536(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 680(a7)
	ld t3, 824(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 968(a7)
	ld t4, 1112(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	ld t1, 104(a7)
	ld t2, 248(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 392(a7)
	ld t3, 536(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 680(a7)
	ld t3, 824(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 968(a7)
	ld t4, 1112(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	ld t2, 104(a7)
	ld t3, 248(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 392(a7)
	ld t4, 536(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 680(a7)
	ld t4, 824(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 968(a7)
	ld t5, 1112(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a5
	xor t0, t0, t1
	ld t1, 104(a7)
	ld t2, 248(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 392(a7)
	ld t3, 536(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 680(a7)
	ld t3, 824(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 968(a7)
	ld t4, 1112(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	ld t2, 104(a7)
	ld t3, 248(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 392(a7)
	ld t4, 536(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 680(a7)
	ld t4, 824(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 968(a7)
	ld t5, 1112(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	ld t2, 104(a7)
	ld t3, 248(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 392(a7)
	ld t4, 536(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 680(a7)
	ld t4, 824(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 968(a7)
	ld t5, 1112(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	ld t3, 104(a7)
	ld t4, 248(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 392(a7)
	ld t5, 536(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	ld t4, 680(a7)
	ld t5, 824(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	ld t5, 968(a7)
	ld t6, 1112(a7)
	xor t6, t6, t5
	and t6, t6, a1
	xor t5, t5, t6
	xor t5, t5, t4
	and t5, t5, a2
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a3
	xor t3, t3, t4
	addi a7, a7, 1152
	xor t3, t3, t2
	and t3, t3, a4
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a5
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a6
	xor t0, t0, t1
	sd t0, 1392(s0)
	addi a7, a0, 0
	ld t0, 112(a7)
	ld t1, 256(a7)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 400(a7)
	ld t2, 544(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 688(a7)
	ld t2, 832(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 976(a7)
	ld t3, 1120(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	addi a7, a7, 1152
	ld t1, 112(a7)
	ld t2, 256(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 400(a7)
	ld t3, 544(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 688(a7)
	ld t3, 832(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 976(a7)
	ld t4, 1120(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	ld t1, 112(a7)
	ld t2, 256(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 400(a7)
	ld t3, 544(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 688(a7)
	ld t3, 832(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 976(a7)
	ld t4, 1120(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	ld t2, 112(a7)
	ld t3, 256(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 400(a7)
	ld t4, 544(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 688(a7)
	ld t4, 832(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 976(a7)
	ld t5, 1120(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a5
	xor t0, t0, t1
	ld t1, 112(a7)
	ld t2, 256(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 400(a7)
	ld t3, 544(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 688(a7)
	ld t3, 832(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 976(a7)
	ld t4, 1120(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	ld t2, 112(a7)
	ld t3, 256(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 400(a7)
	ld t4, 544(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 688(a7)
	ld t4, 832(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 976(a7)
	ld t5, 1120(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	ld t2, 112(a7)
	ld t3, 256(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 400(a7)
	ld t4, 544(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 688(a7)
	ld t4, 832(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 976(a7)
	ld t5, 1120(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	ld t3, 112(a7)
	ld t4, 256(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 400(a7)
	ld t5, 544(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	ld t4, 688(a7)
	ld t5, 832(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	ld t5, 976(a7)
	ld t6, 1120(a7)
	xor t6, t6, t5
	and t6, t6, a1
	xor t5, t5, t6
	xor t5, t5, t4
	and t5, t5, a2
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a3
	xor t3, t3, t4
	addi a7, a7, 1152
	xor t3, t3, t2
	and t3, t3, a4
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a5
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a6
	xor t0, t0, t1
	sd t0, 1400(s0)
	addi a7, a0, 0
	ld t0, 120(a7)
	ld t1, 264(a7)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 408(a7)
	ld t2, 552(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 696(a7)
	ld t2, 840(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 984(a7)
	ld t3, 1128(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	addi a7, a7, 1152
	ld t1, 120(a7)
	ld t2, 264(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 408(a7)
	ld t3, 552(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 696(a7)
	ld t3, 840(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 984(a7)
	ld t4, 1128(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	ld t1, 120(a7)
	ld t2, 264(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 408(a7)
	ld t3, 552(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 696(a7)
	ld t3, 840(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 984(a7)
	ld t4, 1128(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	ld t2, 120(a7)
	ld t3, 264(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 408(a7)
	ld t4, 552(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 696(a7)
	ld t4, 840(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 984(a7)
	ld t5, 1128(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a5
	xor t0, t0, t1
	ld t1, 120(a7)
	ld t2, 264(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 408(a7)
	ld t3, 552(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 696(a7)
	ld t3, 840(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 984(a7)
	ld t4, 1128(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	ld t2, 120(a7)
	ld t3, 264(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 408(a7)
	ld t4, 552(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 696(a7)
	ld t4, 840(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 984(a7)
	ld t5, 1128(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	ld t2, 120(a7)
	ld t3, 264(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 408(a7)
	ld t4, 552(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 696(a7)
	ld t4, 840(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 984(a7)
	ld t5, 1128(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	ld t3, 120(a7)
	ld t4, 264(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 408(a7)
	ld t5, 552(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	ld t4, 696(a7)
	ld t5, 840(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	ld t5, 984(a7)
	ld t6, 1128(a7)
	xor t6, t6, t5
	and t6, t6, a1
	xor t5, t5, t6
	xor t5, t5, t4
	and t5, t5, a2
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a3
	xor t3, t3, t4
	addi a7, a7, 1152
	xor t3, t3, t2
	and t3, t3, a4
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a5
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a6
	xor t0, t0, t1
	sd t0, 1408(s0)
	addi a7, a0, 0
	ld t0, 128(a7)
	ld t1, 272(a7)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 416(a7)
	ld t2, 560(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 704(a7)
	ld t2, 848(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 992(a7)
	ld t3, 1136(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	addi a7, a7, 1152
	ld t1, 128(a7)
	ld t2, 272(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 416(a7)
	ld t3, 560(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 704(a7)
	ld t3, 848(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 992(a7)
	ld t4, 1136(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	ld t1, 128(a7)
	ld t2, 272(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 416(a7)
	ld t3, 560(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 704(a7)
	ld t3, 848(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 992(a7)
	ld t4, 1136(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	ld t2, 128(a7)
	ld t3, 272(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 416(a7)
	ld t4, 560(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 704(a7)
	ld t4, 848(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 992(a7)
	ld t5, 1136(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a5
	xor t0, t0, t1
	ld t1, 128(a7)
	ld t2, 272(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 416(a7)
	ld t3, 560(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 704(a7)
	ld t3, 848(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 992(a7)
	ld t4, 1136(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	ld t2, 128(a7)
	ld t3, 272(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 416(a7)
	ld t4, 560(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 704(a7)
	ld t4, 848(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 992(a7)
	ld t5, 1136(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	ld t2, 128(a7)
	ld t3, 272(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 416(a7)
	ld t4, 560(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 704(a7)
	ld t4, 848(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 992(a7)
	ld t5, 1136(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	ld t3, 128(a7)
	ld t4, 272(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 416(a7)
	ld t5, 560(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	ld t4, 704(a7)
	ld t5, 848(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	ld t5, 992(a7)
	ld t6, 1136(a7)
	xor t6, t6, t5
	and t6, t6, a1
	xor t5, t5, t6
	xor t5, t5, t4
	and t5, t5, a2
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a3
	xor t3, t3, t4
	addi a7, a7, 1152
	xor t3, t3, t2
	and t3, t3, a4
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a5
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a6
	xor t0, t0, t1
	sd t0, 1416(s0)
	addi a7, a0, 0
	ld t0, 136(a7)
	ld t1, 280(a7)
	xor t1, t1, t0
	and t1, t1, a1
	xor t0, t0, t1
	ld t1, 424(a7)
	ld t2, 568(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a2
	xor t0, t0, t1
	ld t1, 712(a7)
	ld t2, 856(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 1000(a7)
	ld t3, 1144(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a3
	xor t0, t0, t1
	addi a7, a7, 1152
	ld t1, 136(a7)
	ld t2, 280(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 424(a7)
	ld t3, 568(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 712(a7)
	ld t3, 856(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1000(a7)
	ld t4, 1144(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	xor t1, t1, t0
	and t1, t1, a4
	xor t0, t0, t1
	ld t1, 136(a7)
	ld t2, 280(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 424(a7)
	ld t3, 568(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 712(a7)
	ld t3, 856(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1000(a7)
	ld t4, 1144(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	ld t2, 136(a7)
	ld t3, 280(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 424(a7)
	ld t4, 568(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 712(a7)
	ld t4, 856(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1000(a7)
	ld t5, 1144(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a5
	xor t0, t0, t1
	ld t1, 136(a7)
	ld t2, 280(a7)
	xor t2, t2, t1
	and t2, t2, a1
	xor t1, t1, t2
	ld t2, 424(a7)
	ld t3, 568(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a2
	xor t1, t1, t2
	ld t2, 712(a7)
	ld t3, 856(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 1000(a7)
	ld t4, 1144(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a3
	xor t1, t1, t2
	addi a7, a7, 1152
	ld t2, 136(a7)
	ld t3, 280(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 424(a7)
	ld t4, 568(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 712(a7)
	ld t4, 856(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1000(a7)
	ld t5, 1144(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	xor t2, t2, t1
	and t2, t2, a4
	xor t1, t1, t2
	ld t2, 136(a7)
	ld t3, 280(a7)
	xor t3, t3, t2
	and t3, t3, a1
	xor t2, t2, t3
	ld t3, 424(a7)
	ld t4, 568(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a2
	xor t2, t2, t3
	ld t3, 712(a7)
	ld t4, 856(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 1000(a7)
	ld t5, 1144(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	xor t3, t3, t2
	and t3, t3, a3
	xor t2, t2, t3
	addi a7, a7, 1152
	ld t3, 136(a7)
	ld t4, 280(a7)
	xor t4, t4, t3
	and t4, t4, a1
	xor t3, t3, t4
	ld t4, 424(a7)
	ld t5, 568(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a2
	xor t3, t3, t4
	ld t4, 712(a7)
	ld t5, 856(a7)
	xor t5, t5, t4
	and t5, t5, a1
	xor t4, t4, t5
	ld t5, 1000(a7)
	ld t6, 1144(a7)
	xor t6, t6, t5
	and t6, t6, a1
	xor t5, t5, t6
	xor t5, t5, t4
	and t5, t5, a2
	xor t4, t4, t5
	xor t4, t4, t3
	and t4, t4, a3
	xor t3, t3, t4
	addi a7, a7, 1152
	xor t3, t3, t2
	and t3, t3, a4
	xor t2, t2, t3
	xor t2, t2, t1
	and t2, t2, a5
	xor t1, t1, t2
	xor t1, t1, t0
	and t1, t1, a6
	xor t0, t0, t1
	sd t0, 1424(s0)
	addi a0, s0, 0
	addi a1, zero, 1288
	addi a2, zero, 1288
	addi a3, zero, 0
	call {vg_p521u_unpack_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1288
	addi a2, zero, 1288
	addi a3, zero, 2047
	addi a3, a3, 1761
	call {vg_p521u_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 0
	call {vg_p521u_unpack_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1360
	addi a2, zero, 1360
	addi a3, zero, 2047
	addi a3, a3, 1761
	call {vg_p521u_mul_mod_p}
	addi a7, s0, 2047
	ld a7, 1417(a7)
	ld t0, 1288(s0)
	ld t1, 280(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1288(s0)
	ld t0, 1296(s0)
	ld t1, 288(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1296(s0)
	ld t0, 1304(s0)
	ld t1, 296(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1304(s0)
	ld t0, 1312(s0)
	ld t1, 304(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1312(s0)
	ld t0, 1320(s0)
	ld t1, 312(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1320(s0)
	ld t0, 1328(s0)
	ld t1, 320(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1328(s0)
	ld t0, 1336(s0)
	ld t1, 328(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1336(s0)
	ld t0, 1344(s0)
	ld t1, 336(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1344(s0)
	ld t0, 1352(s0)
	ld t1, 344(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1352(s0)
	ld t0, 1360(s0)
	addi t1, s0, 2047
	ld t1, 1689(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1360(s0)
	ld t0, 1368(s0)
	addi t1, s0, 2047
	ld t1, 1697(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1368(s0)
	ld t0, 1376(s0)
	addi t1, s0, 2047
	ld t1, 1705(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1376(s0)
	ld t0, 1384(s0)
	addi t1, s0, 2047
	ld t1, 1713(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1384(s0)
	ld t0, 1392(s0)
	addi t1, s0, 2047
	ld t1, 1721(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1392(s0)
	ld t0, 1400(s0)
	addi t1, s0, 2047
	ld t1, 1729(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1400(s0)
	ld t0, 1408(s0)
	addi t1, s0, 2047
	ld t1, 1737(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1408(s0)
	ld t0, 1416(s0)
	addi t1, s0, 2047
	ld t1, 1745(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1416(s0)
	ld t0, 1424(s0)
	addi t1, s0, 2047
	ld t1, 1753(t1)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1424(s0)
	addi t0, s0, 2047
	ld t0, 1689(t0)
	ld t1, 280(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1432(s0)
	addi t0, s0, 2047
	ld t0, 1697(t0)
	ld t1, 288(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1440(s0)
	addi t0, s0, 2047
	ld t0, 1705(t0)
	ld t1, 296(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1448(s0)
	addi t0, s0, 2047
	ld t0, 1713(t0)
	ld t1, 304(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1456(s0)
	addi t0, s0, 2047
	ld t0, 1721(t0)
	ld t1, 312(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1464(s0)
	addi t0, s0, 2047
	ld t0, 1729(t0)
	ld t1, 320(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1472(s0)
	addi t0, s0, 2047
	ld t0, 1737(t0)
	ld t1, 328(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1480(s0)
	addi t0, s0, 2047
	ld t0, 1745(t0)
	ld t1, 336(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1488(s0)
	addi t0, s0, 2047
	ld t0, 1753(t0)
	ld t1, 344(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1496(s0)
	addi a0, s0, 0
	addi a1, zero, 1504
	addi a2, zero, 280
	addi a3, zero, 1360
	call {vg_p521u_sub_mod_p}
	addi a7, s0, 2047
	ld a7, 1409(a7)
	ld t0, 1360(s0)
	ld t1, 1504(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1360(s0)
	ld t0, 1368(s0)
	ld t1, 1512(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1368(s0)
	ld t0, 1376(s0)
	ld t1, 1520(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1376(s0)
	ld t0, 1384(s0)
	ld t1, 1528(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1384(s0)
	ld t0, 1392(s0)
	ld t1, 1536(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1392(s0)
	ld t0, 1400(s0)
	ld t1, 1544(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1400(s0)
	ld t0, 1408(s0)
	ld t1, 1552(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1408(s0)
	ld t0, 1416(s0)
	ld t1, 1560(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1416(s0)
	ld t0, 1424(s0)
	ld t1, 1568(s0)
	xor t1, t1, t0
	and t1, t1, a7
	xor t0, t0, t1
	sd t0, 1424(s0)
	addi a0, s0, 0
	addi a1, zero, 1720
	addi a2, zero, 1072
	addi a3, zero, 1288
	call {vg_p521u_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1144
	addi a3, zero, 1360
	call {vg_p521u_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1864
	addi a2, zero, 1216
	addi a3, zero, 1432
	call {vg_p521u_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1936
	addi a2, zero, 1072
	addi a3, zero, 1144
	call {vg_p521u_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2008
	addi a2, zero, 1288
	addi a3, zero, 1360
	call {vg_p521u_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1936
	addi a2, zero, 1936
	addi a3, zero, 2008
	call {vg_p521u_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2008
	addi a2, zero, 1720
	addi a3, zero, 1792
	call {vg_p521u_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1936
	addi a2, zero, 1936
	addi a3, zero, 2008
	call {vg_p521u_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2008
	addi a2, zero, 1072
	addi a3, zero, 1216
	call {vg_p521u_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 33
	addi a2, zero, 1288
	addi a3, zero, 1432
	call {vg_p521u_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2008
	addi a2, zero, 2008
	addi a3, zero, 2047
	addi a3, a3, 33
	call {vg_p521u_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 33
	addi a2, zero, 1720
	addi a3, zero, 1864
	call {vg_p521u_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2008
	addi a2, zero, 2008
	addi a3, zero, 2047
	addi a3, a3, 33
	call {vg_p521u_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 33
	addi a2, zero, 1144
	addi a3, zero, 1216
	call {vg_p521u_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1504
	addi a2, zero, 1360
	addi a3, zero, 1432
	call {vg_p521u_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 33
	addi a2, zero, 2047
	addi a2, a2, 33
	addi a3, zero, 1504
	call {vg_p521u_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1504
	addi a2, zero, 1792
	addi a3, zero, 1864
	call {vg_p521u_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2047
	addi a1, a1, 33
	addi a2, zero, 2047
	addi a2, a2, 33
	addi a3, zero, 1504
	call {vg_p521u_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1648
	addi a2, zero, 2047
	addi a2, a2, 1545
	addi a3, zero, 2008
	call {vg_p521u_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1504
	addi a2, zero, 2047
	addi a2, a2, 1617
	addi a3, zero, 1864
	call {vg_p521u_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1648
	addi a2, zero, 1504
	addi a3, zero, 1648
	call {vg_p521u_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1504
	addi a2, zero, 1792
	addi a3, zero, 1648
	call {vg_p521u_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1648
	addi a2, zero, 1792
	addi a3, zero, 1648
	call {vg_p521u_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1576
	addi a2, zero, 1504
	addi a3, zero, 1648
	call {vg_p521u_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1720
	addi a3, zero, 1720
	call {vg_p521u_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1720
	call {vg_p521u_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1864
	addi a2, zero, 2047
	addi a2, a2, 1545
	addi a3, zero, 1864
	call {vg_p521u_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2008
	addi a2, zero, 2047
	addi a2, a2, 1617
	addi a3, zero, 2008
	call {vg_p521u_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1792
	addi a2, zero, 1792
	addi a3, zero, 1864
	call {vg_p521u_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1864
	addi a2, zero, 1720
	addi a3, zero, 1864
	call {vg_p521u_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1864
	addi a2, zero, 2047
	addi a2, a2, 1545
	addi a3, zero, 1864
	call {vg_p521u_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 2008
	addi a2, zero, 2008
	addi a3, zero, 1864
	call {vg_p521u_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1720
	addi a2, zero, 1792
	addi a3, zero, 2008
	call {vg_p521u_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1576
	addi a2, zero, 1576
	addi a3, zero, 1720
	call {vg_p521u_add_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1720
	addi a2, zero, 2047
	addi a2, a2, 33
	addi a3, zero, 2008
	call {vg_p521u_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1504
	addi a2, zero, 1936
	addi a3, zero, 1504
	call {vg_p521u_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1504
	addi a2, zero, 1504
	addi a3, zero, 1720
	call {vg_p521u_sub_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1720
	addi a2, zero, 1936
	addi a3, zero, 1792
	call {vg_p521u_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1648
	addi a2, zero, 2047
	addi a2, a2, 33
	addi a3, zero, 1648
	call {vg_p521u_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1648
	addi a2, zero, 1648
	addi a3, zero, 1720
	call {vg_p521u_add_mod_p}
	ld t0, 1504(s0)
	sd t0, 1072(s0)
	ld t0, 1512(s0)
	sd t0, 1080(s0)
	ld t0, 1520(s0)
	sd t0, 1088(s0)
	ld t0, 1528(s0)
	sd t0, 1096(s0)
	ld t0, 1536(s0)
	sd t0, 1104(s0)
	ld t0, 1544(s0)
	sd t0, 1112(s0)
	ld t0, 1552(s0)
	sd t0, 1120(s0)
	ld t0, 1560(s0)
	sd t0, 1128(s0)
	ld t0, 1568(s0)
	sd t0, 1136(s0)
	ld t0, 1576(s0)
	sd t0, 1144(s0)
	ld t0, 1584(s0)
	sd t0, 1152(s0)
	ld t0, 1592(s0)
	sd t0, 1160(s0)
	ld t0, 1600(s0)
	sd t0, 1168(s0)
	ld t0, 1608(s0)
	sd t0, 1176(s0)
	ld t0, 1616(s0)
	sd t0, 1184(s0)
	ld t0, 1624(s0)
	sd t0, 1192(s0)
	ld t0, 1632(s0)
	sd t0, 1200(s0)
	ld t0, 1640(s0)
	sd t0, 1208(s0)
	ld t0, 1648(s0)
	sd t0, 1216(s0)
	ld t0, 1656(s0)
	sd t0, 1224(s0)
	ld t0, 1664(s0)
	sd t0, 1232(s0)
	ld t0, 1672(s0)
	sd t0, 1240(s0)
	ld t0, 1680(s0)
	sd t0, 1248(s0)
	ld t0, 1688(s0)
	sd t0, 1256(s0)
	ld t0, 1696(s0)
	sd t0, 1264(s0)
	ld t0, 1704(s0)
	sd t0, 1272(s0)
	ld t0, 1712(s0)
	sd t0, 1280(s0)
	bnez s1, 20b
	ld t0, 280(s0)
	addi s0, s0, 2047
	sd t0, 1761(s0)
	addi s0, s0, -2047
	ld t0, 288(s0)
	addi s0, s0, 2047
	sd t0, 1769(s0)
	addi s0, s0, -2047
	ld t0, 296(s0)
	addi s0, s0, 2047
	sd t0, 1777(s0)
	addi s0, s0, -2047
	ld t0, 304(s0)
	addi s0, s0, 2047
	sd t0, 1785(s0)
	addi s0, s0, -2047
	ld t0, 312(s0)
	addi s0, s0, 2047
	sd t0, 1793(s0)
	addi s0, s0, -2047
	ld t0, 320(s0)
	addi s0, s0, 2047
	sd t0, 1801(s0)
	addi s0, s0, -2047
	ld t0, 328(s0)
	addi s0, s0, 2047
	sd t0, 1809(s0)
	addi s0, s0, -2047
	ld t0, 336(s0)
	addi s0, s0, 2047
	sd t0, 1817(s0)
	addi s0, s0, -2047
	ld t0, 344(s0)
	addi s0, s0, 2047
	sd t0, 1825(s0)
	addi s0, s0, -2047
	addi t0, zero, 1
	slli t0, t0, 55
	addi s0, s0, 2047
	sd t0, 1761(s0)
	addi s0, s0, -2047
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1072
	addi a3, zero, 2047
	addi a3, a3, 1761
	call {vg_p521u_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1072
	addi a2, zero, 1072
	addi a3, zero, 0
	call {vg_p521u_pack_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 2047
	addi a3, a3, 1761
	call {vg_p521u_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1144
	addi a2, zero, 1144
	addi a3, zero, 0
	call {vg_p521u_pack_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 2047
	addi a3, a3, 1761
	call {vg_p521u_mul_mod_p}
	addi a0, s0, 0
	addi a1, zero, 1216
	addi a2, zero, 1216
	addi a3, zero, 0
	call {vg_p521u_pack_mod_p}
	addi ra, s0, 2047
	ld ra, 1273(ra)
	addi s4, s0, 2047
	ld s4, 1281(s4)
	addi s1, s0, 2047
	ld s1, 1265(s1)
	addi s0, s0, 2047
	ld s0, 1257(s0)
	ret
	.option pop
