// The functions of `src/cast5.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cast5_expand_key:
	.option push
	.option arch, +m, +c
	addi a3, a3, 7
	andi a3, a3, -8
	sd s0, 64(a3)
	sd s1, 72(a3)
	sd s2, 80(a3)
	sd s3, 88(a3)
	sd s4, 96(a3)
	sd s5, 104(a3)
	sd s6, 112(a3)
	sd s7, 120(a3)
	sd s8, 128(a3)
	sd s9, 136(a3)
	sd s10, 144(a3)
	lla t4, {VG_CAST5_S5678}
	addi t0, zero, 0
	sd t0, 16(a3)
	sd t0, 24(a3)
	addi a4, a3, 16
20:
	lbu t0, 0(a0)
	sb t0, 0(a4)
	addi a0, a0, 1
	addi a4, a4, 1
	addi a1, a1, -1
	bnez a1, 20b
	addi a7, zero, 2
21:
	addi a6, zero, 0
22:
	addi t0, a6, 0
	beqz t0, 23f
	addi t0, a6, -1
	beqz t0, 25f
	addi t0, a6, -2
	beqz t0, 27f
	addi t0, a6, -3
	beqz t0, 29f
	addi t0, a6, -4
	beqz t0, 211f
	addi t0, a6, -5
	beqz t0, 213f
	addi t0, a6, -6
	beqz t0, 215f
	addi t0, a6, -7
	beqz t0, 217f
	addi t0, a6, -8
	beqz t0, 219f
	addi t0, a6, -9
	beqz t0, 221f
	addi t0, a6, -10
	beqz t0, 223f
	addi t0, a6, -11
	beqz t0, 225f
	addi t0, a6, -12
	beqz t0, 227f
	addi t0, a6, -13
	beqz t0, 229f
	addi t0, a6, -14
	beqz t0, 231f
	addi t0, a6, -15
	beqz t0, 233f
	addi t0, a6, -16
	beqz t0, 235f
	addi t0, a6, -17
	beqz t0, 237f
	addi t0, a6, -18
	beqz t0, 239f
	addi t0, a6, -19
	beqz t0, 241f
	addi t0, a6, -20
	beqz t0, 243f
	addi t0, a6, -21
	beqz t0, 245f
	addi t0, a6, -22
	beqz t0, 247f
	addi t0, a6, -23
	beqz t0, 249f
	addi t0, a6, -24
	beqz t0, 251f
	addi t0, a6, -25
	beqz t0, 253f
	addi t0, a6, -26
	beqz t0, 255f
	addi t0, a6, -27
	beqz t0, 257f
	addi t0, a6, -28
	beqz t0, 259f
	addi t0, a6, -29
	beqz t0, 261f
	addi t0, a6, -30
	beqz t0, 263f
	addi t0, a6, -31
	beqz t0, 265f
	addi t0, a6, -32
	beqz t0, 267f
	addi t0, a6, -33
	beqz t0, 269f
	addi t0, a6, -34
	beqz t0, 271f
	addi t0, a6, -35
	beqz t0, 273f
	addi t0, a6, -36
	beqz t0, 275f
	addi t0, a6, -37
	beqz t0, 277f
	addi t0, a6, -38
	beqz t0, 279f
	addi t0, a6, -39
	beqz t0, 281f
	j 282f
281:
	lbu s0, 16(a3)
	lbu s1, 17(a3)
	lbu s2, 31(a3)
	lbu s3, 30(a3)
282:
	j 280f
279:
	lbu s0, 18(a3)
	lbu s1, 19(a3)
	lbu s2, 29(a3)
	lbu s3, 28(a3)
280:
	j 278f
277:
	lbu s0, 20(a3)
	lbu s1, 21(a3)
	lbu s2, 27(a3)
	lbu s3, 26(a3)
278:
	j 276f
275:
	lbu s0, 22(a3)
	lbu s1, 23(a3)
	lbu s2, 25(a3)
	lbu s3, 24(a3)
276:
	j 274f
273:
	lbu s0, 29(a3)
	lbu s1, 24(a3)
	lbu s2, 23(a3)
	lbu s3, 19(a3)
274:
	j 272f
271:
	lbu s0, 24(a3)
	lbu s1, 27(a3)
	lbu s2, 25(a3)
	lbu s3, 26(a3)
272:
	j 270f
269:
	lbu s0, 20(a3)
	lbu s1, 21(a3)
	lbu s2, 22(a3)
	lbu s3, 23(a3)
270:
	j 268f
267:
	lbu s0, 19(a3)
	lbu s1, 17(a3)
	lbu s2, 18(a3)
	lbu s3, 16(a3)
268:
	j 266f
265:
	lbu s0, 38(a3)
	lbu s1, 36(a3)
	lbu s2, 39(a3)
	lbu s3, 37(a3)
266:
	j 264f
263:
	lbu s0, 34(a3)
	lbu s1, 32(a3)
	lbu s2, 35(a3)
	lbu s3, 33(a3)
264:
	j 262f
261:
	lbu s0, 43(a3)
	lbu s1, 42(a3)
	lbu s2, 36(a3)
	lbu s3, 37(a3)
262:
	j 260f
259:
	lbu s0, 41(a3)
	lbu s1, 40(a3)
	lbu s2, 38(a3)
	lbu s3, 39(a3)
260:
	j 258f
257:
	lbu s0, 47(a3)
	lbu s1, 46(a3)
	lbu s2, 32(a3)
	lbu s3, 33(a3)
258:
	j 256f
255:
	lbu s0, 45(a3)
	lbu s1, 44(a3)
	lbu s2, 34(a3)
	lbu s3, 35(a3)
256:
	j 254f
253:
	lbu s0, 38(a3)
	lbu s1, 34(a3)
	lbu s2, 44(a3)
	lbu s3, 41(a3)
254:
	j 252f
251:
	lbu s0, 40(a3)
	lbu s1, 43(a3)
	lbu s2, 41(a3)
	lbu s3, 42(a3)
252:
	j 250f
249:
	lbu s0, 36(a3)
	lbu s1, 37(a3)
	lbu s2, 38(a3)
	lbu s3, 39(a3)
250:
	j 248f
247:
	lbu s0, 35(a3)
	lbu s1, 33(a3)
	lbu s2, 34(a3)
	lbu s3, 32(a3)
248:
	j 246f
245:
	lbu s0, 30(a3)
	lbu s1, 28(a3)
	lbu s2, 31(a3)
	lbu s3, 29(a3)
246:
	j 244f
243:
	lbu s0, 26(a3)
	lbu s1, 24(a3)
	lbu s2, 27(a3)
	lbu s3, 25(a3)
244:
	j 242f
241:
	lbu s0, 27(a3)
	lbu s1, 26(a3)
	lbu s2, 20(a3)
	lbu s3, 21(a3)
242:
	j 240f
239:
	lbu s0, 25(a3)
	lbu s1, 24(a3)
	lbu s2, 22(a3)
	lbu s3, 23(a3)
240:
	j 238f
237:
	lbu s0, 31(a3)
	lbu s1, 30(a3)
	lbu s2, 16(a3)
	lbu s3, 17(a3)
238:
	j 236f
235:
	lbu s0, 29(a3)
	lbu s1, 28(a3)
	lbu s2, 18(a3)
	lbu s3, 19(a3)
236:
	j 234f
233:
	lbu s0, 23(a3)
	lbu s1, 19(a3)
	lbu s2, 29(a3)
	lbu s3, 24(a3)
234:
	j 232f
231:
	lbu s0, 24(a3)
	lbu s1, 27(a3)
	lbu s2, 25(a3)
	lbu s3, 26(a3)
232:
	j 230f
229:
	lbu s0, 20(a3)
	lbu s1, 21(a3)
	lbu s2, 22(a3)
	lbu s3, 23(a3)
230:
	j 228f
227:
	lbu s0, 19(a3)
	lbu s1, 17(a3)
	lbu s2, 18(a3)
	lbu s3, 16(a3)
228:
	j 226f
225:
	lbu s0, 38(a3)
	lbu s1, 36(a3)
	lbu s2, 39(a3)
	lbu s3, 37(a3)
226:
	j 224f
223:
	lbu s0, 34(a3)
	lbu s1, 32(a3)
	lbu s2, 35(a3)
	lbu s3, 33(a3)
224:
	j 222f
221:
	lbu s0, 32(a3)
	lbu s1, 33(a3)
	lbu s2, 47(a3)
	lbu s3, 46(a3)
222:
	j 220f
219:
	lbu s0, 34(a3)
	lbu s1, 35(a3)
	lbu s2, 45(a3)
	lbu s3, 44(a3)
220:
	j 218f
217:
	lbu s0, 36(a3)
	lbu s1, 37(a3)
	lbu s2, 43(a3)
	lbu s3, 42(a3)
218:
	j 216f
215:
	lbu s0, 38(a3)
	lbu s1, 39(a3)
	lbu s2, 41(a3)
	lbu s3, 40(a3)
216:
	j 214f
213:
	lbu s0, 44(a3)
	lbu s1, 41(a3)
	lbu s2, 38(a3)
	lbu s3, 34(a3)
214:
	j 212f
211:
	lbu s0, 40(a3)
	lbu s1, 43(a3)
	lbu s2, 41(a3)
	lbu s3, 42(a3)
212:
	j 210f
29:
	lbu s0, 36(a3)
	lbu s1, 37(a3)
	lbu s2, 38(a3)
	lbu s3, 39(a3)
210:
	j 28f
27:
	lbu s0, 35(a3)
	lbu s1, 33(a3)
	lbu s2, 34(a3)
	lbu s3, 32(a3)
28:
	j 26f
25:
	lbu s0, 30(a3)
	lbu s1, 28(a3)
	lbu s2, 31(a3)
	lbu s3, 29(a3)
26:
	j 24f
23:
	lbu s0, 26(a3)
	lbu s1, 24(a3)
	lbu s2, 27(a3)
	lbu s3, 25(a3)
24:
	slli t0, s0, 63
	srai t0, t0, 63
	srli t0, t0, 32
	slli a5, s1, 63
	srai a5, a5, 63
	slli a5, a5, 32
	or t0, t0, a5
	slli t1, s0, 62
	srai t1, t1, 63
	srli t1, t1, 32
	slli a5, s1, 62
	srai a5, a5, 63
	slli a5, a5, 32
	or t1, t1, a5
	slli t2, s0, 61
	srai t2, t2, 63
	srli t2, t2, 32
	slli a5, s1, 61
	srai a5, a5, 63
	slli a5, a5, 32
	or t2, t2, a5
	slli t5, s0, 60
	srai t5, t5, 63
	srli t5, t5, 32
	slli a5, s1, 60
	srai a5, a5, 63
	slli a5, a5, 32
	or t5, t5, a5
	srli s0, s0, 4
	addi s0, s0, -17
	srli s1, s1, 4
	addi s1, s1, -17
	addi t3, t4, 2047
	addi t3, t3, 2047
	addi t3, t3, 2
283:
	addi t3, t3, -256
	addi s0, s0, 1
	addi s1, s1, 1
	ld s5, 0(t3)
	ld s6, 16(t3)
	xor s6, s6, s5
	and s6, s6, t0
	xor s5, s5, s6
	ld s6, 32(t3)
	ld a5, 48(t3)
	xor a5, a5, s6
	and a5, a5, t0
	xor s6, s6, a5
	xor s6, s6, s5
	and s6, s6, t1
	xor s5, s5, s6
	ld s6, 64(t3)
	ld a5, 80(t3)
	xor a5, a5, s6
	and a5, a5, t0
	xor s6, s6, a5
	ld a5, 96(t3)
	ld t6, 112(t3)
	xor t6, t6, a5
	and t6, t6, t0
	xor a5, a5, t6
	xor a5, a5, s6
	and a5, a5, t1
	xor s6, s6, a5
	xor s6, s6, s5
	and s6, s6, t2
	xor s5, s5, s6
	ld s6, 128(t3)
	ld a5, 144(t3)
	xor a5, a5, s6
	and a5, a5, t0
	xor s6, s6, a5
	ld a5, 160(t3)
	ld t6, 176(t3)
	xor t6, t6, a5
	and t6, t6, t0
	xor a5, a5, t6
	xor a5, a5, s6
	and a5, a5, t1
	xor s6, s6, a5
	ld a5, 192(t3)
	ld t6, 208(t3)
	xor t6, t6, a5
	and t6, t6, t0
	xor a5, a5, t6
	ld t6, 224(t3)
	ld s7, 240(t3)
	xor s7, s7, t6
	and s7, s7, t0
	xor t6, t6, s7
	xor t6, t6, a5
	and t6, t6, t1
	xor a5, a5, t6
	xor a5, a5, s6
	and a5, a5, t2
	xor s6, s6, a5
	xor s6, s6, s5
	and s6, s6, t5
	xor s5, s5, s6
	srli s6, s0, 32
	srai a5, s1, 63
	slli a5, a5, 32
	or s6, s6, a5
	xor s5, s5, s4
	and s5, s5, s6
	xor s4, s4, s5
	bne t3, t4, 283b
	srli s5, s4, 32
	slli s4, s4, 32
	srli s4, s4, 32
	slli t0, s2, 63
	srai t0, t0, 63
	srli t0, t0, 32
	slli a5, s3, 63
	srai a5, a5, 63
	slli a5, a5, 32
	or t0, t0, a5
	slli t1, s2, 62
	srai t1, t1, 63
	srli t1, t1, 32
	slli a5, s3, 62
	srai a5, a5, 63
	slli a5, a5, 32
	or t1, t1, a5
	slli t2, s2, 61
	srai t2, t2, 63
	srli t2, t2, 32
	slli a5, s3, 61
	srai a5, a5, 63
	slli a5, a5, 32
	or t2, t2, a5
	slli t5, s2, 60
	srai t5, t5, 63
	srli t5, t5, 32
	slli a5, s3, 60
	srai a5, a5, 63
	slli a5, a5, 32
	or t5, t5, a5
	srli s2, s2, 4
	addi s2, s2, -17
	srli s3, s3, 4
	addi s3, s3, -17
	addi t3, t4, 2047
	addi t3, t3, 2047
	addi t3, t3, 2
284:
	addi t3, t3, -256
	addi s2, s2, 1
	addi s3, s3, 1
	ld s0, 8(t3)
	ld s1, 24(t3)
	xor s1, s1, s0
	and s1, s1, t0
	xor s0, s0, s1
	ld s1, 40(t3)
	ld a5, 56(t3)
	xor a5, a5, s1
	and a5, a5, t0
	xor s1, s1, a5
	xor s1, s1, s0
	and s1, s1, t1
	xor s0, s0, s1
	ld s1, 72(t3)
	ld a5, 88(t3)
	xor a5, a5, s1
	and a5, a5, t0
	xor s1, s1, a5
	ld a5, 104(t3)
	ld t6, 120(t3)
	xor t6, t6, a5
	and t6, t6, t0
	xor a5, a5, t6
	xor a5, a5, s1
	and a5, a5, t1
	xor s1, s1, a5
	xor s1, s1, s0
	and s1, s1, t2
	xor s0, s0, s1
	ld s1, 136(t3)
	ld a5, 152(t3)
	xor a5, a5, s1
	and a5, a5, t0
	xor s1, s1, a5
	ld a5, 168(t3)
	ld t6, 184(t3)
	xor t6, t6, a5
	and t6, t6, t0
	xor a5, a5, t6
	xor a5, a5, s1
	and a5, a5, t1
	xor s1, s1, a5
	ld a5, 200(t3)
	ld t6, 216(t3)
	xor t6, t6, a5
	and t6, t6, t0
	xor a5, a5, t6
	ld t6, 232(t3)
	ld s7, 248(t3)
	xor s7, s7, t6
	and s7, s7, t0
	xor t6, t6, s7
	xor t6, t6, a5
	and t6, t6, t1
	xor a5, a5, t6
	xor a5, a5, s1
	and a5, a5, t2
	xor s1, s1, a5
	xor s1, s1, s0
	and s1, s1, t5
	xor s0, s0, s1
	srli s1, s2, 32
	srai a5, s3, 63
	slli a5, a5, 32
	or s1, s1, a5
	xor s0, s0, s6
	and s0, s0, s1
	xor s6, s6, s0
	bne t3, t4, 284b
	srli s7, s6, 32
	slli s6, s6, 32
	srli s6, s6, 32
	addi t0, a6, 0
	beqz t0, 285f
	addi t0, a6, -1
	beqz t0, 287f
	addi t0, a6, -2
	beqz t0, 289f
	addi t0, a6, -3
	beqz t0, 291f
	addi t0, a6, -4
	beqz t0, 293f
	addi t0, a6, -5
	beqz t0, 295f
	addi t0, a6, -6
	beqz t0, 297f
	addi t0, a6, -7
	beqz t0, 299f
	addi t0, a6, -8
	beqz t0, 2101f
	addi t0, a6, -9
	beqz t0, 2103f
	addi t0, a6, -10
	beqz t0, 2105f
	addi t0, a6, -11
	beqz t0, 2107f
	addi t0, a6, -12
	beqz t0, 2109f
	addi t0, a6, -13
	beqz t0, 2111f
	addi t0, a6, -14
	beqz t0, 2113f
	addi t0, a6, -15
	beqz t0, 2115f
	addi t0, a6, -16
	beqz t0, 2117f
	addi t0, a6, -17
	beqz t0, 2119f
	addi t0, a6, -18
	beqz t0, 2121f
	addi t0, a6, -19
	beqz t0, 2123f
	addi t0, a6, -20
	beqz t0, 2125f
	addi t0, a6, -21
	beqz t0, 2127f
	addi t0, a6, -22
	beqz t0, 2129f
	addi t0, a6, -23
	beqz t0, 2131f
	addi t0, a6, -24
	beqz t0, 2133f
	addi t0, a6, -25
	beqz t0, 2135f
	addi t0, a6, -26
	beqz t0, 2137f
	addi t0, a6, -27
	beqz t0, 2139f
	addi t0, a6, -28
	beqz t0, 2141f
	addi t0, a6, -29
	beqz t0, 2143f
	addi t0, a6, -30
	beqz t0, 2145f
	addi t0, a6, -31
	beqz t0, 2147f
	addi t0, a6, -32
	beqz t0, 2149f
	addi t0, a6, -33
	beqz t0, 2151f
	addi t0, a6, -34
	beqz t0, 2153f
	addi t0, a6, -35
	beqz t0, 2155f
	addi t0, a6, -36
	beqz t0, 2157f
	addi t0, a6, -37
	beqz t0, 2159f
	addi t0, a6, -38
	beqz t0, 2161f
	addi t0, a6, -39
	beqz t0, 2163f
	j 2164f
2163:
	xor t5, s4, s5
	xor t5, t5, s6
	xor t5, t5, s7
	lwu t0, 48(a3)
	xor t5, t5, t0
	sb t5, 60(a2)
	srli t0, t5, 8
	sb t0, 61(a2)
	srli t0, t5, 16
	sb t0, 62(a2)
	srli t0, t5, 24
	sb t0, 63(a2)
2164:
	j 2162f
2161:
	xor t5, s4, s5
	xor t5, t5, s6
	xor t5, t5, s7
	lwu t0, 52(a3)
	xor t5, t5, t0
	sb t5, 56(a2)
	srli t0, t5, 8
	sb t0, 57(a2)
	srli t0, t5, 16
	sb t0, 58(a2)
	srli t0, t5, 24
	sb t0, 59(a2)
2162:
	j 2160f
2159:
	xor t5, s4, s5
	xor t5, t5, s6
	xor t5, t5, s7
	lwu t0, 56(a3)
	xor t5, t5, t0
	sb t5, 52(a2)
	srli t0, t5, 8
	sb t0, 53(a2)
	srli t0, t5, 16
	sb t0, 54(a2)
	srli t0, t5, 24
	sb t0, 55(a2)
2160:
	j 2158f
2157:
	xor t5, s4, s5
	xor t5, t5, s6
	xor t5, t5, s7
	lwu t0, 60(a3)
	xor t5, t5, t0
	sb t5, 48(a2)
	srli t0, t5, 8
	sb t0, 49(a2)
	srli t0, t5, 16
	sb t0, 50(a2)
	srli t0, t5, 24
	sb t0, 51(a2)
2158:
	j 2156f
2155:
	sw s4, 48(a3)
	sw s5, 52(a3)
	sw s6, 56(a3)
	sw s7, 60(a3)
2156:
	j 2154f
2153:
	xor t5, s4, s5
	xor t5, t5, s6
	xor t5, t5, s7
	lwu t0, 56(a3)
	xor t5, t5, t0
	lbu t0, 44(a3)
	slli t0, t0, 24
	lbu t1, 45(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 46(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 47(a3)
	or t0, t0, t1
	xor t5, t5, t0
	srli t1, t5, 24
	sb t1, 28(a3)
	srli t1, t5, 16
	sb t1, 29(a3)
	srli t1, t5, 8
	sb t1, 30(a3)
	srli t1, t5, 0
	sb t1, 31(a3)
2154:
	j 2152f
2151:
	xor t5, s4, s5
	xor t5, t5, s6
	xor t5, t5, s7
	lwu t0, 60(a3)
	xor t5, t5, t0
	lbu t0, 36(a3)
	slli t0, t0, 24
	lbu t1, 37(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 38(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 39(a3)
	or t0, t0, t1
	xor t5, t5, t0
	srli t1, t5, 24
	sb t1, 24(a3)
	srli t1, t5, 16
	sb t1, 25(a3)
	srli t1, t5, 8
	sb t1, 26(a3)
	srli t1, t5, 0
	sb t1, 27(a3)
2152:
	j 2150f
2149:
	xor t5, s4, s5
	xor t5, t5, s6
	xor t5, t5, s7
	lwu t0, 48(a3)
	xor t5, t5, t0
	lbu t0, 32(a3)
	slli t0, t0, 24
	lbu t1, 33(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 34(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 35(a3)
	or t0, t0, t1
	xor t5, t5, t0
	srli t1, t5, 24
	sb t1, 20(a3)
	srli t1, t5, 16
	sb t1, 21(a3)
	srli t1, t5, 8
	sb t1, 22(a3)
	srli t1, t5, 0
	sb t1, 23(a3)
2150:
	j 2148f
2147:
	xor t5, s4, s5
	xor t5, t5, s6
	xor t5, t5, s7
	lwu t0, 52(a3)
	xor t5, t5, t0
	lbu t0, 40(a3)
	slli t0, t0, 24
	lbu t1, 41(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 42(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 43(a3)
	or t0, t0, t1
	xor t5, t5, t0
	srli t1, t5, 24
	sb t1, 16(a3)
	srli t1, t5, 16
	sb t1, 17(a3)
	srli t1, t5, 8
	sb t1, 18(a3)
	srli t1, t5, 0
	sb t1, 19(a3)
2148:
	j 2146f
2145:
	sw s4, 48(a3)
	sw s5, 52(a3)
	sw s6, 56(a3)
	sw s7, 60(a3)
2146:
	j 2144f
2143:
	xor t5, s4, s5
	xor t5, t5, s6
	xor t5, t5, s7
	lwu t0, 48(a3)
	xor t5, t5, t0
	sb t5, 44(a2)
	srli t0, t5, 8
	sb t0, 45(a2)
	srli t0, t5, 16
	sb t0, 46(a2)
	srli t0, t5, 24
	sb t0, 47(a2)
2144:
	j 2142f
2141:
	xor t5, s4, s5
	xor t5, t5, s6
	xor t5, t5, s7
	lwu t0, 52(a3)
	xor t5, t5, t0
	sb t5, 40(a2)
	srli t0, t5, 8
	sb t0, 41(a2)
	srli t0, t5, 16
	sb t0, 42(a2)
	srli t0, t5, 24
	sb t0, 43(a2)
2142:
	j 2140f
2139:
	xor t5, s4, s5
	xor t5, t5, s6
	xor t5, t5, s7
	lwu t0, 56(a3)
	xor t5, t5, t0
	sb t5, 36(a2)
	srli t0, t5, 8
	sb t0, 37(a2)
	srli t0, t5, 16
	sb t0, 38(a2)
	srli t0, t5, 24
	sb t0, 39(a2)
2140:
	j 2138f
2137:
	xor t5, s4, s5
	xor t5, t5, s6
	xor t5, t5, s7
	lwu t0, 60(a3)
	xor t5, t5, t0
	sb t5, 32(a2)
	srli t0, t5, 8
	sb t0, 33(a2)
	srli t0, t5, 16
	sb t0, 34(a2)
	srli t0, t5, 24
	sb t0, 35(a2)
2138:
	j 2136f
2135:
	sw s4, 48(a3)
	sw s5, 52(a3)
	sw s6, 56(a3)
	sw s7, 60(a3)
2136:
	j 2134f
2133:
	xor t5, s4, s5
	xor t5, t5, s6
	xor t5, t5, s7
	lwu t0, 56(a3)
	xor t5, t5, t0
	lbu t0, 20(a3)
	slli t0, t0, 24
	lbu t1, 21(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 22(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 23(a3)
	or t0, t0, t1
	xor t5, t5, t0
	srli t1, t5, 24
	sb t1, 44(a3)
	srli t1, t5, 16
	sb t1, 45(a3)
	srli t1, t5, 8
	sb t1, 46(a3)
	srli t1, t5, 0
	sb t1, 47(a3)
2134:
	j 2132f
2131:
	xor t5, s4, s5
	xor t5, t5, s6
	xor t5, t5, s7
	lwu t0, 60(a3)
	xor t5, t5, t0
	lbu t0, 28(a3)
	slli t0, t0, 24
	lbu t1, 29(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 30(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 31(a3)
	or t0, t0, t1
	xor t5, t5, t0
	srli t1, t5, 24
	sb t1, 40(a3)
	srli t1, t5, 16
	sb t1, 41(a3)
	srli t1, t5, 8
	sb t1, 42(a3)
	srli t1, t5, 0
	sb t1, 43(a3)
2132:
	j 2130f
2129:
	xor t5, s4, s5
	xor t5, t5, s6
	xor t5, t5, s7
	lwu t0, 48(a3)
	xor t5, t5, t0
	lbu t0, 24(a3)
	slli t0, t0, 24
	lbu t1, 25(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 26(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 27(a3)
	or t0, t0, t1
	xor t5, t5, t0
	srli t1, t5, 24
	sb t1, 36(a3)
	srli t1, t5, 16
	sb t1, 37(a3)
	srli t1, t5, 8
	sb t1, 38(a3)
	srli t1, t5, 0
	sb t1, 39(a3)
2130:
	j 2128f
2127:
	xor t5, s4, s5
	xor t5, t5, s6
	xor t5, t5, s7
	lwu t0, 52(a3)
	xor t5, t5, t0
	lbu t0, 16(a3)
	slli t0, t0, 24
	lbu t1, 17(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 18(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 19(a3)
	or t0, t0, t1
	xor t5, t5, t0
	srli t1, t5, 24
	sb t1, 32(a3)
	srli t1, t5, 16
	sb t1, 33(a3)
	srli t1, t5, 8
	sb t1, 34(a3)
	srli t1, t5, 0
	sb t1, 35(a3)
2128:
	j 2126f
2125:
	sw s4, 48(a3)
	sw s5, 52(a3)
	sw s6, 56(a3)
	sw s7, 60(a3)
2126:
	j 2124f
2123:
	xor t5, s4, s5
	xor t5, t5, s6
	xor t5, t5, s7
	lwu t0, 48(a3)
	xor t5, t5, t0
	sb t5, 28(a2)
	srli t0, t5, 8
	sb t0, 29(a2)
	srli t0, t5, 16
	sb t0, 30(a2)
	srli t0, t5, 24
	sb t0, 31(a2)
2124:
	j 2122f
2121:
	xor t5, s4, s5
	xor t5, t5, s6
	xor t5, t5, s7
	lwu t0, 52(a3)
	xor t5, t5, t0
	sb t5, 24(a2)
	srli t0, t5, 8
	sb t0, 25(a2)
	srli t0, t5, 16
	sb t0, 26(a2)
	srli t0, t5, 24
	sb t0, 27(a2)
2122:
	j 2120f
2119:
	xor t5, s4, s5
	xor t5, t5, s6
	xor t5, t5, s7
	lwu t0, 56(a3)
	xor t5, t5, t0
	sb t5, 20(a2)
	srli t0, t5, 8
	sb t0, 21(a2)
	srli t0, t5, 16
	sb t0, 22(a2)
	srli t0, t5, 24
	sb t0, 23(a2)
2120:
	j 2118f
2117:
	xor t5, s4, s5
	xor t5, t5, s6
	xor t5, t5, s7
	lwu t0, 60(a3)
	xor t5, t5, t0
	sb t5, 16(a2)
	srli t0, t5, 8
	sb t0, 17(a2)
	srli t0, t5, 16
	sb t0, 18(a2)
	srli t0, t5, 24
	sb t0, 19(a2)
2118:
	j 2116f
2115:
	sw s4, 48(a3)
	sw s5, 52(a3)
	sw s6, 56(a3)
	sw s7, 60(a3)
2116:
	j 2114f
2113:
	xor t5, s4, s5
	xor t5, t5, s6
	xor t5, t5, s7
	lwu t0, 56(a3)
	xor t5, t5, t0
	lbu t0, 44(a3)
	slli t0, t0, 24
	lbu t1, 45(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 46(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 47(a3)
	or t0, t0, t1
	xor t5, t5, t0
	srli t1, t5, 24
	sb t1, 28(a3)
	srli t1, t5, 16
	sb t1, 29(a3)
	srli t1, t5, 8
	sb t1, 30(a3)
	srli t1, t5, 0
	sb t1, 31(a3)
2114:
	j 2112f
2111:
	xor t5, s4, s5
	xor t5, t5, s6
	xor t5, t5, s7
	lwu t0, 60(a3)
	xor t5, t5, t0
	lbu t0, 36(a3)
	slli t0, t0, 24
	lbu t1, 37(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 38(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 39(a3)
	or t0, t0, t1
	xor t5, t5, t0
	srli t1, t5, 24
	sb t1, 24(a3)
	srli t1, t5, 16
	sb t1, 25(a3)
	srli t1, t5, 8
	sb t1, 26(a3)
	srli t1, t5, 0
	sb t1, 27(a3)
2112:
	j 2110f
2109:
	xor t5, s4, s5
	xor t5, t5, s6
	xor t5, t5, s7
	lwu t0, 48(a3)
	xor t5, t5, t0
	lbu t0, 32(a3)
	slli t0, t0, 24
	lbu t1, 33(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 34(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 35(a3)
	or t0, t0, t1
	xor t5, t5, t0
	srli t1, t5, 24
	sb t1, 20(a3)
	srli t1, t5, 16
	sb t1, 21(a3)
	srli t1, t5, 8
	sb t1, 22(a3)
	srli t1, t5, 0
	sb t1, 23(a3)
2110:
	j 2108f
2107:
	xor t5, s4, s5
	xor t5, t5, s6
	xor t5, t5, s7
	lwu t0, 52(a3)
	xor t5, t5, t0
	lbu t0, 40(a3)
	slli t0, t0, 24
	lbu t1, 41(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 42(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 43(a3)
	or t0, t0, t1
	xor t5, t5, t0
	srli t1, t5, 24
	sb t1, 16(a3)
	srli t1, t5, 16
	sb t1, 17(a3)
	srli t1, t5, 8
	sb t1, 18(a3)
	srli t1, t5, 0
	sb t1, 19(a3)
2108:
	j 2106f
2105:
	sw s4, 48(a3)
	sw s5, 52(a3)
	sw s6, 56(a3)
	sw s7, 60(a3)
2106:
	j 2104f
2103:
	xor t5, s4, s5
	xor t5, t5, s6
	xor t5, t5, s7
	lwu t0, 48(a3)
	xor t5, t5, t0
	sb t5, 12(a2)
	srli t0, t5, 8
	sb t0, 13(a2)
	srli t0, t5, 16
	sb t0, 14(a2)
	srli t0, t5, 24
	sb t0, 15(a2)
2104:
	j 2102f
2101:
	xor t5, s4, s5
	xor t5, t5, s6
	xor t5, t5, s7
	lwu t0, 52(a3)
	xor t5, t5, t0
	sb t5, 8(a2)
	srli t0, t5, 8
	sb t0, 9(a2)
	srli t0, t5, 16
	sb t0, 10(a2)
	srli t0, t5, 24
	sb t0, 11(a2)
2102:
	j 2100f
299:
	xor t5, s4, s5
	xor t5, t5, s6
	xor t5, t5, s7
	lwu t0, 56(a3)
	xor t5, t5, t0
	sb t5, 4(a2)
	srli t0, t5, 8
	sb t0, 5(a2)
	srli t0, t5, 16
	sb t0, 6(a2)
	srli t0, t5, 24
	sb t0, 7(a2)
2100:
	j 298f
297:
	xor t5, s4, s5
	xor t5, t5, s6
	xor t5, t5, s7
	lwu t0, 60(a3)
	xor t5, t5, t0
	sb t5, 0(a2)
	srli t0, t5, 8
	sb t0, 1(a2)
	srli t0, t5, 16
	sb t0, 2(a2)
	srli t0, t5, 24
	sb t0, 3(a2)
298:
	j 296f
295:
	sw s4, 48(a3)
	sw s5, 52(a3)
	sw s6, 56(a3)
	sw s7, 60(a3)
296:
	j 294f
293:
	xor t5, s4, s5
	xor t5, t5, s6
	xor t5, t5, s7
	lwu t0, 56(a3)
	xor t5, t5, t0
	lbu t0, 20(a3)
	slli t0, t0, 24
	lbu t1, 21(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 22(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 23(a3)
	or t0, t0, t1
	xor t5, t5, t0
	srli t1, t5, 24
	sb t1, 44(a3)
	srli t1, t5, 16
	sb t1, 45(a3)
	srli t1, t5, 8
	sb t1, 46(a3)
	srli t1, t5, 0
	sb t1, 47(a3)
294:
	j 292f
291:
	xor t5, s4, s5
	xor t5, t5, s6
	xor t5, t5, s7
	lwu t0, 60(a3)
	xor t5, t5, t0
	lbu t0, 28(a3)
	slli t0, t0, 24
	lbu t1, 29(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 30(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 31(a3)
	or t0, t0, t1
	xor t5, t5, t0
	srli t1, t5, 24
	sb t1, 40(a3)
	srli t1, t5, 16
	sb t1, 41(a3)
	srli t1, t5, 8
	sb t1, 42(a3)
	srli t1, t5, 0
	sb t1, 43(a3)
292:
	j 290f
289:
	xor t5, s4, s5
	xor t5, t5, s6
	xor t5, t5, s7
	lwu t0, 48(a3)
	xor t5, t5, t0
	lbu t0, 24(a3)
	slli t0, t0, 24
	lbu t1, 25(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 26(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 27(a3)
	or t0, t0, t1
	xor t5, t5, t0
	srli t1, t5, 24
	sb t1, 36(a3)
	srli t1, t5, 16
	sb t1, 37(a3)
	srli t1, t5, 8
	sb t1, 38(a3)
	srli t1, t5, 0
	sb t1, 39(a3)
290:
	j 288f
287:
	xor t5, s4, s5
	xor t5, t5, s6
	xor t5, t5, s7
	lwu t0, 52(a3)
	xor t5, t5, t0
	lbu t0, 16(a3)
	slli t0, t0, 24
	lbu t1, 17(a3)
	slli t1, t1, 16
	or t0, t0, t1
	lbu t1, 18(a3)
	slli t1, t1, 8
	or t0, t0, t1
	lbu t1, 19(a3)
	or t0, t0, t1
	xor t5, t5, t0
	srli t1, t5, 24
	sb t1, 32(a3)
	srli t1, t5, 16
	sb t1, 33(a3)
	srli t1, t5, 8
	sb t1, 34(a3)
	srli t1, t5, 0
	sb t1, 35(a3)
288:
	j 286f
285:
	sw s4, 48(a3)
	sw s5, 52(a3)
	sw s6, 56(a3)
	sw s7, 60(a3)
286:
	addi a6, a6, 1
	addi t0, a6, -40
	bnez t0, 22b
	addi a2, a2, 64
	addi a7, a7, -1
	bnez a7, 21b
	ld s0, 64(a3)
	ld s1, 72(a3)
	ld s2, 80(a3)
	ld s3, 88(a3)
	ld s4, 96(a3)
	ld s5, 104(a3)
	ld s6, 112(a3)
	ld s7, 120(a3)
	ld s8, 128(a3)
	ld s9, 136(a3)
	ld s10, 144(a3)
	ret
	.option pop

vg_cast5_ecb_encrypt:
	.option push
	.option arch, +m, +c
	addi a4, a4, 7
	andi a4, a4, -8
	sd s0, 64(a4)
	sd s1, 72(a4)
	sd s2, 80(a4)
	sd s3, 88(a4)
	sd s4, 96(a4)
	sd s5, 104(a4)
	sd s6, 112(a4)
	sd s7, 120(a4)
	sd s8, 128(a4)
	sd s9, 136(a4)
	sd s10, 144(a4)
	lla t4, {VG_CAST5_S1234}
	beqz a3, 20f
22:
	lbu a6, 0(a2)
	slli a6, a6, 24
	lbu t0, 1(a2)
	slli t0, t0, 16
	or a6, a6, t0
	lbu t0, 2(a2)
	slli t0, t0, 8
	or a6, a6, t0
	lbu t0, 3(a2)
	or a6, a6, t0
	lbu a7, 4(a2)
	slli a7, a7, 24
	lbu t0, 5(a2)
	slli t0, t0, 16
	or a7, a7, t0
	lbu t0, 6(a2)
	slli t0, t0, 8
	or a7, a7, t0
	lbu t0, 7(a2)
	or a7, a7, t0
	addi s8, a0, 0
	addi s9, a1, 0
	addi s10, zero, 1
23:
	beqz s10, 24f
	addi t0, s10, -1
	beqz t0, 26f
	lbu t5, 0(s8)
	lbu t0, 1(s8)
	slli t0, t0, 8
	or t5, t5, t0
	lbu t0, 2(s8)
	slli t0, t0, 16
	or t5, t5, t0
	lbu t0, 3(s8)
	slli t0, t0, 24
	or t5, t5, t0
	xor t5, t5, a7
	j 27f
26:
	lbu t5, 0(s8)
	lbu t0, 1(s8)
	slli t0, t0, 8
	or t5, t5, t0
	lbu t0, 2(s8)
	slli t0, t0, 16
	or t5, t5, t0
	lbu t0, 3(s8)
	slli t0, t0, 24
	or t5, t5, t0
	add t5, t5, a7
27:
	j 25f
24:
	lbu t5, 0(s8)
	lbu t0, 1(s8)
	slli t0, t0, 8
	or t5, t5, t0
	lbu t0, 2(s8)
	slli t0, t0, 16
	or t5, t5, t0
	lbu t0, 3(s8)
	slli t0, t0, 24
	or t5, t5, t0
	sub t5, t5, a7
25:
	lbu t6, 64(s8)
	addi t1, zero, 32
	sub t1, t1, t6
	srlw t1, t5, t1
	sllw t5, t5, t6
	or t5, t5, t1
	andi s0, t5, 255
	srliw s1, t5, 8
	andi s1, s1, 255
	srliw s2, t5, 16
	andi s2, s2, 255
	srliw s3, t5, 24
	slli t0, s0, 63
	srai t0, t0, 63
	srli t0, t0, 32
	slli a5, s1, 63
	srai a5, a5, 63
	slli a5, a5, 32
	or t0, t0, a5
	slli t1, s0, 62
	srai t1, t1, 63
	srli t1, t1, 32
	slli a5, s1, 62
	srai a5, a5, 63
	slli a5, a5, 32
	or t1, t1, a5
	slli t2, s0, 61
	srai t2, t2, 63
	srli t2, t2, 32
	slli a5, s1, 61
	srai a5, a5, 63
	slli a5, a5, 32
	or t2, t2, a5
	slli t5, s0, 60
	srai t5, t5, 63
	srli t5, t5, 32
	slli a5, s1, 60
	srai a5, a5, 63
	slli a5, a5, 32
	or t5, t5, a5
	srli s0, s0, 4
	addi s0, s0, -17
	srli s1, s1, 4
	addi s1, s1, -17
	addi t3, t4, 2047
	addi t3, t3, 2047
	addi t3, t3, 2
28:
	addi t3, t3, -256
	addi s0, s0, 1
	addi s1, s1, 1
	ld s5, 0(t3)
	ld s6, 16(t3)
	xor s6, s6, s5
	and s6, s6, t0
	xor s5, s5, s6
	ld s6, 32(t3)
	ld a5, 48(t3)
	xor a5, a5, s6
	and a5, a5, t0
	xor s6, s6, a5
	xor s6, s6, s5
	and s6, s6, t1
	xor s5, s5, s6
	ld s6, 64(t3)
	ld a5, 80(t3)
	xor a5, a5, s6
	and a5, a5, t0
	xor s6, s6, a5
	ld a5, 96(t3)
	ld t6, 112(t3)
	xor t6, t6, a5
	and t6, t6, t0
	xor a5, a5, t6
	xor a5, a5, s6
	and a5, a5, t1
	xor s6, s6, a5
	xor s6, s6, s5
	and s6, s6, t2
	xor s5, s5, s6
	ld s6, 128(t3)
	ld a5, 144(t3)
	xor a5, a5, s6
	and a5, a5, t0
	xor s6, s6, a5
	ld a5, 160(t3)
	ld t6, 176(t3)
	xor t6, t6, a5
	and t6, t6, t0
	xor a5, a5, t6
	xor a5, a5, s6
	and a5, a5, t1
	xor s6, s6, a5
	ld a5, 192(t3)
	ld t6, 208(t3)
	xor t6, t6, a5
	and t6, t6, t0
	xor a5, a5, t6
	ld t6, 224(t3)
	ld s7, 240(t3)
	xor s7, s7, t6
	and s7, s7, t0
	xor t6, t6, s7
	xor t6, t6, a5
	and t6, t6, t1
	xor a5, a5, t6
	xor a5, a5, s6
	and a5, a5, t2
	xor s6, s6, a5
	xor s6, s6, s5
	and s6, s6, t5
	xor s5, s5, s6
	srli s6, s0, 32
	srai a5, s1, 63
	slli a5, a5, 32
	or s6, s6, a5
	xor s5, s5, s4
	and s5, s5, s6
	xor s4, s4, s5
	bne t3, t4, 28b
	srli s5, s4, 32
	slli s4, s4, 32
	srli s4, s4, 32
	slli t0, s2, 63
	srai t0, t0, 63
	srli t0, t0, 32
	slli a5, s3, 63
	srai a5, a5, 63
	slli a5, a5, 32
	or t0, t0, a5
	slli t1, s2, 62
	srai t1, t1, 63
	srli t1, t1, 32
	slli a5, s3, 62
	srai a5, a5, 63
	slli a5, a5, 32
	or t1, t1, a5
	slli t2, s2, 61
	srai t2, t2, 63
	srli t2, t2, 32
	slli a5, s3, 61
	srai a5, a5, 63
	slli a5, a5, 32
	or t2, t2, a5
	slli t5, s2, 60
	srai t5, t5, 63
	srli t5, t5, 32
	slli a5, s3, 60
	srai a5, a5, 63
	slli a5, a5, 32
	or t5, t5, a5
	srli s2, s2, 4
	addi s2, s2, -17
	srli s3, s3, 4
	addi s3, s3, -17
	addi t3, t4, 2047
	addi t3, t3, 2047
	addi t3, t3, 2
29:
	addi t3, t3, -256
	addi s2, s2, 1
	addi s3, s3, 1
	ld s0, 8(t3)
	ld s1, 24(t3)
	xor s1, s1, s0
	and s1, s1, t0
	xor s0, s0, s1
	ld s1, 40(t3)
	ld a5, 56(t3)
	xor a5, a5, s1
	and a5, a5, t0
	xor s1, s1, a5
	xor s1, s1, s0
	and s1, s1, t1
	xor s0, s0, s1
	ld s1, 72(t3)
	ld a5, 88(t3)
	xor a5, a5, s1
	and a5, a5, t0
	xor s1, s1, a5
	ld a5, 104(t3)
	ld t6, 120(t3)
	xor t6, t6, a5
	and t6, t6, t0
	xor a5, a5, t6
	xor a5, a5, s1
	and a5, a5, t1
	xor s1, s1, a5
	xor s1, s1, s0
	and s1, s1, t2
	xor s0, s0, s1
	ld s1, 136(t3)
	ld a5, 152(t3)
	xor a5, a5, s1
	and a5, a5, t0
	xor s1, s1, a5
	ld a5, 168(t3)
	ld t6, 184(t3)
	xor t6, t6, a5
	and t6, t6, t0
	xor a5, a5, t6
	xor a5, a5, s1
	and a5, a5, t1
	xor s1, s1, a5
	ld a5, 200(t3)
	ld t6, 216(t3)
	xor t6, t6, a5
	and t6, t6, t0
	xor a5, a5, t6
	ld t6, 232(t3)
	ld s7, 248(t3)
	xor s7, s7, t6
	and s7, s7, t0
	xor t6, t6, s7
	xor t6, t6, a5
	and t6, t6, t1
	xor a5, a5, t6
	xor a5, a5, s1
	and a5, a5, t2
	xor s1, s1, a5
	xor s1, s1, s0
	and s1, s1, t5
	xor s0, s0, s1
	srli s1, s2, 32
	srai a5, s3, 63
	slli a5, a5, 32
	or s1, s1, a5
	xor s0, s0, s6
	and s0, s0, s1
	xor s6, s6, s0
	bne t3, t4, 29b
	srli s7, s6, 32
	slli s6, s6, 32
	srli s6, s6, 32
	beqz s10, 210f
	addi t0, s10, -1
	beqz t0, 212f
	sub t5, s7, s6
	add t5, t5, s5
	xor t5, t5, s4
	j 213f
212:
	xor t5, s7, s6
	sub t5, t5, s5
	add t5, t5, s4
213:
	j 211f
210:
	add t5, s7, s6
	xor t5, t5, s5
	sub t5, t5, s4
211:
	xor t5, t5, a6
	addi a6, a7, 0
	addi a7, t5, 0
	addi s8, s8, 4
	addi t0, s10, -2
	beqz t0, 214f
	addi s10, s10, 1
	j 215f
214:
	addi s10, zero, 0
215:
	addi s9, s9, -1
	bnez s9, 23b
	srli t0, a7, 24
	sb t0, 0(a2)
	srli t0, a7, 16
	sb t0, 1(a2)
	srli t0, a7, 8
	sb t0, 2(a2)
	srli t0, a7, 0
	sb t0, 3(a2)
	srli t0, a6, 24
	sb t0, 4(a2)
	srli t0, a6, 16
	sb t0, 5(a2)
	srli t0, a6, 8
	sb t0, 6(a2)
	srli t0, a6, 0
	sb t0, 7(a2)
	addi a2, a2, 8
	addi a3, a3, -1
	bnez a3, 22b
	j 21f
20:
21:
	ld s0, 64(a4)
	ld s1, 72(a4)
	ld s2, 80(a4)
	ld s3, 88(a4)
	ld s4, 96(a4)
	ld s5, 104(a4)
	ld s6, 112(a4)
	ld s7, 120(a4)
	ld s8, 128(a4)
	ld s9, 136(a4)
	ld s10, 144(a4)
	ret
	.option pop

vg_cast5_ecb_decrypt:
	.option push
	.option arch, +m, +c
	addi a4, a4, 7
	andi a4, a4, -8
	sd s0, 64(a4)
	sd s1, 72(a4)
	sd s2, 80(a4)
	sd s3, 88(a4)
	sd s4, 96(a4)
	sd s5, 104(a4)
	sd s6, 112(a4)
	sd s7, 120(a4)
	sd s8, 128(a4)
	sd s9, 136(a4)
	sd s10, 144(a4)
	lla t4, {VG_CAST5_S1234}
	beqz a3, 20f
22:
	lbu a6, 0(a2)
	slli a6, a6, 24
	lbu t0, 1(a2)
	slli t0, t0, 16
	or a6, a6, t0
	lbu t0, 2(a2)
	slli t0, t0, 8
	or a6, a6, t0
	lbu t0, 3(a2)
	or a6, a6, t0
	lbu a7, 4(a2)
	slli a7, a7, 24
	lbu t0, 5(a2)
	slli t0, t0, 16
	or a7, a7, t0
	lbu t0, 6(a2)
	slli t0, t0, 8
	or a7, a7, t0
	lbu t0, 7(a2)
	or a7, a7, t0
	slli t0, a1, 2
	add s8, a0, t0
	addi s8, s8, -4
	addi s9, a1, 0
	srli t0, a1, 2
	addi s10, t0, -3
23:
	beqz s10, 24f
	addi t0, s10, -1
	beqz t0, 26f
	lbu t5, 0(s8)
	lbu t0, 1(s8)
	slli t0, t0, 8
	or t5, t5, t0
	lbu t0, 2(s8)
	slli t0, t0, 16
	or t5, t5, t0
	lbu t0, 3(s8)
	slli t0, t0, 24
	or t5, t5, t0
	xor t5, t5, a7
	j 27f
26:
	lbu t5, 0(s8)
	lbu t0, 1(s8)
	slli t0, t0, 8
	or t5, t5, t0
	lbu t0, 2(s8)
	slli t0, t0, 16
	or t5, t5, t0
	lbu t0, 3(s8)
	slli t0, t0, 24
	or t5, t5, t0
	add t5, t5, a7
27:
	j 25f
24:
	lbu t5, 0(s8)
	lbu t0, 1(s8)
	slli t0, t0, 8
	or t5, t5, t0
	lbu t0, 2(s8)
	slli t0, t0, 16
	or t5, t5, t0
	lbu t0, 3(s8)
	slli t0, t0, 24
	or t5, t5, t0
	sub t5, t5, a7
25:
	lbu t6, 64(s8)
	addi t1, zero, 32
	sub t1, t1, t6
	srlw t1, t5, t1
	sllw t5, t5, t6
	or t5, t5, t1
	andi s0, t5, 255
	srliw s1, t5, 8
	andi s1, s1, 255
	srliw s2, t5, 16
	andi s2, s2, 255
	srliw s3, t5, 24
	slli t0, s0, 63
	srai t0, t0, 63
	srli t0, t0, 32
	slli a5, s1, 63
	srai a5, a5, 63
	slli a5, a5, 32
	or t0, t0, a5
	slli t1, s0, 62
	srai t1, t1, 63
	srli t1, t1, 32
	slli a5, s1, 62
	srai a5, a5, 63
	slli a5, a5, 32
	or t1, t1, a5
	slli t2, s0, 61
	srai t2, t2, 63
	srli t2, t2, 32
	slli a5, s1, 61
	srai a5, a5, 63
	slli a5, a5, 32
	or t2, t2, a5
	slli t5, s0, 60
	srai t5, t5, 63
	srli t5, t5, 32
	slli a5, s1, 60
	srai a5, a5, 63
	slli a5, a5, 32
	or t5, t5, a5
	srli s0, s0, 4
	addi s0, s0, -17
	srli s1, s1, 4
	addi s1, s1, -17
	addi t3, t4, 2047
	addi t3, t3, 2047
	addi t3, t3, 2
28:
	addi t3, t3, -256
	addi s0, s0, 1
	addi s1, s1, 1
	ld s5, 0(t3)
	ld s6, 16(t3)
	xor s6, s6, s5
	and s6, s6, t0
	xor s5, s5, s6
	ld s6, 32(t3)
	ld a5, 48(t3)
	xor a5, a5, s6
	and a5, a5, t0
	xor s6, s6, a5
	xor s6, s6, s5
	and s6, s6, t1
	xor s5, s5, s6
	ld s6, 64(t3)
	ld a5, 80(t3)
	xor a5, a5, s6
	and a5, a5, t0
	xor s6, s6, a5
	ld a5, 96(t3)
	ld t6, 112(t3)
	xor t6, t6, a5
	and t6, t6, t0
	xor a5, a5, t6
	xor a5, a5, s6
	and a5, a5, t1
	xor s6, s6, a5
	xor s6, s6, s5
	and s6, s6, t2
	xor s5, s5, s6
	ld s6, 128(t3)
	ld a5, 144(t3)
	xor a5, a5, s6
	and a5, a5, t0
	xor s6, s6, a5
	ld a5, 160(t3)
	ld t6, 176(t3)
	xor t6, t6, a5
	and t6, t6, t0
	xor a5, a5, t6
	xor a5, a5, s6
	and a5, a5, t1
	xor s6, s6, a5
	ld a5, 192(t3)
	ld t6, 208(t3)
	xor t6, t6, a5
	and t6, t6, t0
	xor a5, a5, t6
	ld t6, 224(t3)
	ld s7, 240(t3)
	xor s7, s7, t6
	and s7, s7, t0
	xor t6, t6, s7
	xor t6, t6, a5
	and t6, t6, t1
	xor a5, a5, t6
	xor a5, a5, s6
	and a5, a5, t2
	xor s6, s6, a5
	xor s6, s6, s5
	and s6, s6, t5
	xor s5, s5, s6
	srli s6, s0, 32
	srai a5, s1, 63
	slli a5, a5, 32
	or s6, s6, a5
	xor s5, s5, s4
	and s5, s5, s6
	xor s4, s4, s5
	bne t3, t4, 28b
	srli s5, s4, 32
	slli s4, s4, 32
	srli s4, s4, 32
	slli t0, s2, 63
	srai t0, t0, 63
	srli t0, t0, 32
	slli a5, s3, 63
	srai a5, a5, 63
	slli a5, a5, 32
	or t0, t0, a5
	slli t1, s2, 62
	srai t1, t1, 63
	srli t1, t1, 32
	slli a5, s3, 62
	srai a5, a5, 63
	slli a5, a5, 32
	or t1, t1, a5
	slli t2, s2, 61
	srai t2, t2, 63
	srli t2, t2, 32
	slli a5, s3, 61
	srai a5, a5, 63
	slli a5, a5, 32
	or t2, t2, a5
	slli t5, s2, 60
	srai t5, t5, 63
	srli t5, t5, 32
	slli a5, s3, 60
	srai a5, a5, 63
	slli a5, a5, 32
	or t5, t5, a5
	srli s2, s2, 4
	addi s2, s2, -17
	srli s3, s3, 4
	addi s3, s3, -17
	addi t3, t4, 2047
	addi t3, t3, 2047
	addi t3, t3, 2
29:
	addi t3, t3, -256
	addi s2, s2, 1
	addi s3, s3, 1
	ld s0, 8(t3)
	ld s1, 24(t3)
	xor s1, s1, s0
	and s1, s1, t0
	xor s0, s0, s1
	ld s1, 40(t3)
	ld a5, 56(t3)
	xor a5, a5, s1
	and a5, a5, t0
	xor s1, s1, a5
	xor s1, s1, s0
	and s1, s1, t1
	xor s0, s0, s1
	ld s1, 72(t3)
	ld a5, 88(t3)
	xor a5, a5, s1
	and a5, a5, t0
	xor s1, s1, a5
	ld a5, 104(t3)
	ld t6, 120(t3)
	xor t6, t6, a5
	and t6, t6, t0
	xor a5, a5, t6
	xor a5, a5, s1
	and a5, a5, t1
	xor s1, s1, a5
	xor s1, s1, s0
	and s1, s1, t2
	xor s0, s0, s1
	ld s1, 136(t3)
	ld a5, 152(t3)
	xor a5, a5, s1
	and a5, a5, t0
	xor s1, s1, a5
	ld a5, 168(t3)
	ld t6, 184(t3)
	xor t6, t6, a5
	and t6, t6, t0
	xor a5, a5, t6
	xor a5, a5, s1
	and a5, a5, t1
	xor s1, s1, a5
	ld a5, 200(t3)
	ld t6, 216(t3)
	xor t6, t6, a5
	and t6, t6, t0
	xor a5, a5, t6
	ld t6, 232(t3)
	ld s7, 248(t3)
	xor s7, s7, t6
	and s7, s7, t0
	xor t6, t6, s7
	xor t6, t6, a5
	and t6, t6, t1
	xor a5, a5, t6
	xor a5, a5, s1
	and a5, a5, t2
	xor s1, s1, a5
	xor s1, s1, s0
	and s1, s1, t5
	xor s0, s0, s1
	srli s1, s2, 32
	srai a5, s3, 63
	slli a5, a5, 32
	or s1, s1, a5
	xor s0, s0, s6
	and s0, s0, s1
	xor s6, s6, s0
	bne t3, t4, 29b
	srli s7, s6, 32
	slli s6, s6, 32
	srli s6, s6, 32
	beqz s10, 210f
	addi t0, s10, -1
	beqz t0, 212f
	sub t5, s7, s6
	add t5, t5, s5
	xor t5, t5, s4
	j 213f
212:
	xor t5, s7, s6
	sub t5, t5, s5
	add t5, t5, s4
213:
	j 211f
210:
	add t5, s7, s6
	xor t5, t5, s5
	sub t5, t5, s4
211:
	xor t5, t5, a6
	addi a6, a7, 0
	addi a7, t5, 0
	addi s8, s8, -4
	beqz s10, 214f
	addi s10, s10, -1
	j 215f
214:
	addi s10, zero, 2
215:
	addi s9, s9, -1
	bnez s9, 23b
	srli t0, a7, 24
	sb t0, 0(a2)
	srli t0, a7, 16
	sb t0, 1(a2)
	srli t0, a7, 8
	sb t0, 2(a2)
	srli t0, a7, 0
	sb t0, 3(a2)
	srli t0, a6, 24
	sb t0, 4(a2)
	srli t0, a6, 16
	sb t0, 5(a2)
	srli t0, a6, 8
	sb t0, 6(a2)
	srli t0, a6, 0
	sb t0, 7(a2)
	addi a2, a2, 8
	addi a3, a3, -1
	bnez a3, 22b
	j 21f
20:
21:
	ld s0, 64(a4)
	ld s1, 72(a4)
	ld s2, 80(a4)
	ld s3, 88(a4)
	ld s4, 96(a4)
	ld s5, 104(a4)
	ld s6, 112(a4)
	ld s7, 120(a4)
	ld s8, 128(a4)
	ld s9, 136(a4)
	ld s10, 144(a4)
	ret
	.option pop
