// The functions of `src/cast5.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cast5_expand_key:
	mflr %r0
	std %r0, 200(%r6)
	std %r14, 64(%r6)
	std %r15, 72(%r6)
	std %r16, 80(%r6)
	std %r17, 88(%r6)
	std %r18, 96(%r6)
	std %r19, 104(%r6)
	std %r20, 112(%r6)
	std %r21, 120(%r6)
	std %r22, 128(%r6)
	std %r23, 136(%r6)
	std %r24, 144(%r6)
	std %r25, 152(%r6)
	std %r26, 160(%r6)
	std %r27, 168(%r6)
	std %r28, 176(%r6)
	std %r29, 184(%r6)
	std %r30, 192(%r6)
	bcl 20, 31, 2f
2:
	mflr %r27
	addis %r27, %r27, ({VG_CAST5_S5678}
	addi %r27, %r27, ({VG_CAST5_S5678}
	li %r26, 255
	li %r0, 0
	std %r0, 16(%r6)
	std %r0, 24(%r6)
	addi %r7, %r6, 16
20:
	lbz %r24, 0(%r3)
	stb %r24, 0(%r7)
	addi %r3, %r3, 1
	addi %r7, %r7, 1
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 20b
	li %r12, 2
21:
	li %r11, 0
22:
	addi %r24, %r11, -0
	cmpldi %cr0, %r24, 0
	beq %cr0, 23f
	addi %r24, %r11, -1
	cmpldi %cr0, %r24, 0
	beq %cr0, 25f
	addi %r24, %r11, -2
	cmpldi %cr0, %r24, 0
	beq %cr0, 27f
	addi %r24, %r11, -3
	cmpldi %cr0, %r24, 0
	beq %cr0, 29f
	addi %r24, %r11, -4
	cmpldi %cr0, %r24, 0
	beq %cr0, 211f
	addi %r24, %r11, -5
	cmpldi %cr0, %r24, 0
	beq %cr0, 213f
	addi %r24, %r11, -6
	cmpldi %cr0, %r24, 0
	beq %cr0, 215f
	addi %r24, %r11, -7
	cmpldi %cr0, %r24, 0
	beq %cr0, 217f
	addi %r24, %r11, -8
	cmpldi %cr0, %r24, 0
	beq %cr0, 219f
	addi %r24, %r11, -9
	cmpldi %cr0, %r24, 0
	beq %cr0, 221f
	addi %r24, %r11, -10
	cmpldi %cr0, %r24, 0
	beq %cr0, 223f
	addi %r24, %r11, -11
	cmpldi %cr0, %r24, 0
	beq %cr0, 225f
	addi %r24, %r11, -12
	cmpldi %cr0, %r24, 0
	beq %cr0, 227f
	addi %r24, %r11, -13
	cmpldi %cr0, %r24, 0
	beq %cr0, 229f
	addi %r24, %r11, -14
	cmpldi %cr0, %r24, 0
	beq %cr0, 231f
	addi %r24, %r11, -15
	cmpldi %cr0, %r24, 0
	beq %cr0, 233f
	addi %r24, %r11, -16
	cmpldi %cr0, %r24, 0
	beq %cr0, 235f
	addi %r24, %r11, -17
	cmpldi %cr0, %r24, 0
	beq %cr0, 237f
	addi %r24, %r11, -18
	cmpldi %cr0, %r24, 0
	beq %cr0, 239f
	addi %r24, %r11, -19
	cmpldi %cr0, %r24, 0
	beq %cr0, 241f
	addi %r24, %r11, -20
	cmpldi %cr0, %r24, 0
	beq %cr0, 243f
	addi %r24, %r11, -21
	cmpldi %cr0, %r24, 0
	beq %cr0, 245f
	addi %r24, %r11, -22
	cmpldi %cr0, %r24, 0
	beq %cr0, 247f
	addi %r24, %r11, -23
	cmpldi %cr0, %r24, 0
	beq %cr0, 249f
	addi %r24, %r11, -24
	cmpldi %cr0, %r24, 0
	beq %cr0, 251f
	addi %r24, %r11, -25
	cmpldi %cr0, %r24, 0
	beq %cr0, 253f
	addi %r24, %r11, -26
	cmpldi %cr0, %r24, 0
	beq %cr0, 255f
	addi %r24, %r11, -27
	cmpldi %cr0, %r24, 0
	beq %cr0, 257f
	addi %r24, %r11, -28
	cmpldi %cr0, %r24, 0
	beq %cr0, 259f
	addi %r24, %r11, -29
	cmpldi %cr0, %r24, 0
	beq %cr0, 261f
	addi %r24, %r11, -30
	cmpldi %cr0, %r24, 0
	beq %cr0, 263f
	addi %r24, %r11, -31
	cmpldi %cr0, %r24, 0
	beq %cr0, 265f
	addi %r24, %r11, -32
	cmpldi %cr0, %r24, 0
	beq %cr0, 267f
	addi %r24, %r11, -33
	cmpldi %cr0, %r24, 0
	beq %cr0, 269f
	addi %r24, %r11, -34
	cmpldi %cr0, %r24, 0
	beq %cr0, 271f
	addi %r24, %r11, -35
	cmpldi %cr0, %r24, 0
	beq %cr0, 273f
	addi %r24, %r11, -36
	cmpldi %cr0, %r24, 0
	beq %cr0, 275f
	addi %r24, %r11, -37
	cmpldi %cr0, %r24, 0
	beq %cr0, 277f
	addi %r24, %r11, -38
	cmpldi %cr0, %r24, 0
	beq %cr0, 279f
	addi %r24, %r11, -39
	cmpldi %cr0, %r24, 0
	beq %cr0, 281f
	b 282f
281:
	lbz %r14, 16(%r6)
	lbz %r15, 17(%r6)
	lbz %r16, 31(%r6)
	lbz %r17, 30(%r6)
282:
	b 280f
279:
	lbz %r14, 18(%r6)
	lbz %r15, 19(%r6)
	lbz %r16, 29(%r6)
	lbz %r17, 28(%r6)
280:
	b 278f
277:
	lbz %r14, 20(%r6)
	lbz %r15, 21(%r6)
	lbz %r16, 27(%r6)
	lbz %r17, 26(%r6)
278:
	b 276f
275:
	lbz %r14, 22(%r6)
	lbz %r15, 23(%r6)
	lbz %r16, 25(%r6)
	lbz %r17, 24(%r6)
276:
	b 274f
273:
	lbz %r14, 29(%r6)
	lbz %r15, 24(%r6)
	lbz %r16, 23(%r6)
	lbz %r17, 19(%r6)
274:
	b 272f
271:
	lbz %r14, 24(%r6)
	lbz %r15, 27(%r6)
	lbz %r16, 25(%r6)
	lbz %r17, 26(%r6)
272:
	b 270f
269:
	lbz %r14, 20(%r6)
	lbz %r15, 21(%r6)
	lbz %r16, 22(%r6)
	lbz %r17, 23(%r6)
270:
	b 268f
267:
	lbz %r14, 19(%r6)
	lbz %r15, 17(%r6)
	lbz %r16, 18(%r6)
	lbz %r17, 16(%r6)
268:
	b 266f
265:
	lbz %r14, 38(%r6)
	lbz %r15, 36(%r6)
	lbz %r16, 39(%r6)
	lbz %r17, 37(%r6)
266:
	b 264f
263:
	lbz %r14, 34(%r6)
	lbz %r15, 32(%r6)
	lbz %r16, 35(%r6)
	lbz %r17, 33(%r6)
264:
	b 262f
261:
	lbz %r14, 43(%r6)
	lbz %r15, 42(%r6)
	lbz %r16, 36(%r6)
	lbz %r17, 37(%r6)
262:
	b 260f
259:
	lbz %r14, 41(%r6)
	lbz %r15, 40(%r6)
	lbz %r16, 38(%r6)
	lbz %r17, 39(%r6)
260:
	b 258f
257:
	lbz %r14, 47(%r6)
	lbz %r15, 46(%r6)
	lbz %r16, 32(%r6)
	lbz %r17, 33(%r6)
258:
	b 256f
255:
	lbz %r14, 45(%r6)
	lbz %r15, 44(%r6)
	lbz %r16, 34(%r6)
	lbz %r17, 35(%r6)
256:
	b 254f
253:
	lbz %r14, 38(%r6)
	lbz %r15, 34(%r6)
	lbz %r16, 44(%r6)
	lbz %r17, 41(%r6)
254:
	b 252f
251:
	lbz %r14, 40(%r6)
	lbz %r15, 43(%r6)
	lbz %r16, 41(%r6)
	lbz %r17, 42(%r6)
252:
	b 250f
249:
	lbz %r14, 36(%r6)
	lbz %r15, 37(%r6)
	lbz %r16, 38(%r6)
	lbz %r17, 39(%r6)
250:
	b 248f
247:
	lbz %r14, 35(%r6)
	lbz %r15, 33(%r6)
	lbz %r16, 34(%r6)
	lbz %r17, 32(%r6)
248:
	b 246f
245:
	lbz %r14, 30(%r6)
	lbz %r15, 28(%r6)
	lbz %r16, 31(%r6)
	lbz %r17, 29(%r6)
246:
	b 244f
243:
	lbz %r14, 26(%r6)
	lbz %r15, 24(%r6)
	lbz %r16, 27(%r6)
	lbz %r17, 25(%r6)
244:
	b 242f
241:
	lbz %r14, 27(%r6)
	lbz %r15, 26(%r6)
	lbz %r16, 20(%r6)
	lbz %r17, 21(%r6)
242:
	b 240f
239:
	lbz %r14, 25(%r6)
	lbz %r15, 24(%r6)
	lbz %r16, 22(%r6)
	lbz %r17, 23(%r6)
240:
	b 238f
237:
	lbz %r14, 31(%r6)
	lbz %r15, 30(%r6)
	lbz %r16, 16(%r6)
	lbz %r17, 17(%r6)
238:
	b 236f
235:
	lbz %r14, 29(%r6)
	lbz %r15, 28(%r6)
	lbz %r16, 18(%r6)
	lbz %r17, 19(%r6)
236:
	b 234f
233:
	lbz %r14, 23(%r6)
	lbz %r15, 19(%r6)
	lbz %r16, 29(%r6)
	lbz %r17, 24(%r6)
234:
	b 232f
231:
	lbz %r14, 24(%r6)
	lbz %r15, 27(%r6)
	lbz %r16, 25(%r6)
	lbz %r17, 26(%r6)
232:
	b 230f
229:
	lbz %r14, 20(%r6)
	lbz %r15, 21(%r6)
	lbz %r16, 22(%r6)
	lbz %r17, 23(%r6)
230:
	b 228f
227:
	lbz %r14, 19(%r6)
	lbz %r15, 17(%r6)
	lbz %r16, 18(%r6)
	lbz %r17, 16(%r6)
228:
	b 226f
225:
	lbz %r14, 38(%r6)
	lbz %r15, 36(%r6)
	lbz %r16, 39(%r6)
	lbz %r17, 37(%r6)
226:
	b 224f
223:
	lbz %r14, 34(%r6)
	lbz %r15, 32(%r6)
	lbz %r16, 35(%r6)
	lbz %r17, 33(%r6)
224:
	b 222f
221:
	lbz %r14, 32(%r6)
	lbz %r15, 33(%r6)
	lbz %r16, 47(%r6)
	lbz %r17, 46(%r6)
222:
	b 220f
219:
	lbz %r14, 34(%r6)
	lbz %r15, 35(%r6)
	lbz %r16, 45(%r6)
	lbz %r17, 44(%r6)
220:
	b 218f
217:
	lbz %r14, 36(%r6)
	lbz %r15, 37(%r6)
	lbz %r16, 43(%r6)
	lbz %r17, 42(%r6)
218:
	b 216f
215:
	lbz %r14, 38(%r6)
	lbz %r15, 39(%r6)
	lbz %r16, 41(%r6)
	lbz %r17, 40(%r6)
216:
	b 214f
213:
	lbz %r14, 44(%r6)
	lbz %r15, 41(%r6)
	lbz %r16, 38(%r6)
	lbz %r17, 34(%r6)
214:
	b 212f
211:
	lbz %r14, 40(%r6)
	lbz %r15, 43(%r6)
	lbz %r16, 41(%r6)
	lbz %r17, 42(%r6)
212:
	b 210f
29:
	lbz %r14, 36(%r6)
	lbz %r15, 37(%r6)
	lbz %r16, 38(%r6)
	lbz %r17, 39(%r6)
210:
	b 28f
27:
	lbz %r14, 35(%r6)
	lbz %r15, 33(%r6)
	lbz %r16, 34(%r6)
	lbz %r17, 32(%r6)
28:
	b 26f
25:
	lbz %r14, 30(%r6)
	lbz %r15, 28(%r6)
	lbz %r16, 31(%r6)
	lbz %r17, 29(%r6)
26:
	b 24f
23:
	lbz %r14, 26(%r6)
	lbz %r15, 24(%r6)
	lbz %r16, 27(%r6)
	lbz %r17, 25(%r6)
24:
	or %r23, %r27, %r27
	li %r22, 0
	li %r18, 0
	li %r19, 0
	li %r20, 0
	li %r21, 0
283:
	lwz %r25, 0(%r23)
	xor %r24, %r14, %r22
	addi %r24, %r24, -1
	rldicl %r24, %r24, 1, 63
	subf %r24, %r24, %r0
	and %r25, %r25, %r24
	or %r18, %r18, %r25
	lwz %r25, 4(%r23)
	xor %r24, %r15, %r22
	addi %r24, %r24, -1
	rldicl %r24, %r24, 1, 63
	subf %r24, %r24, %r0
	and %r25, %r25, %r24
	or %r19, %r19, %r25
	lwz %r25, 8(%r23)
	xor %r24, %r16, %r22
	addi %r24, %r24, -1
	rldicl %r24, %r24, 1, 63
	subf %r24, %r24, %r0
	and %r25, %r25, %r24
	or %r20, %r20, %r25
	lwz %r25, 12(%r23)
	xor %r24, %r17, %r22
	addi %r24, %r24, -1
	rldicl %r24, %r24, 1, 63
	subf %r24, %r24, %r0
	and %r25, %r25, %r24
	or %r21, %r21, %r25
	addi %r23, %r23, 16
	addi %r22, %r22, 1
	addi %r24, %r22, -256
	cmpldi %cr0, %r24, 0
	bne %cr0, 283b
	addi %r24, %r11, -0
	cmpldi %cr0, %r24, 0
	beq %cr0, 284f
	addi %r24, %r11, -1
	cmpldi %cr0, %r24, 0
	beq %cr0, 286f
	addi %r24, %r11, -2
	cmpldi %cr0, %r24, 0
	beq %cr0, 288f
	addi %r24, %r11, -3
	cmpldi %cr0, %r24, 0
	beq %cr0, 290f
	addi %r24, %r11, -4
	cmpldi %cr0, %r24, 0
	beq %cr0, 292f
	addi %r24, %r11, -5
	cmpldi %cr0, %r24, 0
	beq %cr0, 294f
	addi %r24, %r11, -6
	cmpldi %cr0, %r24, 0
	beq %cr0, 296f
	addi %r24, %r11, -7
	cmpldi %cr0, %r24, 0
	beq %cr0, 298f
	addi %r24, %r11, -8
	cmpldi %cr0, %r24, 0
	beq %cr0, 2100f
	addi %r24, %r11, -9
	cmpldi %cr0, %r24, 0
	beq %cr0, 2102f
	addi %r24, %r11, -10
	cmpldi %cr0, %r24, 0
	beq %cr0, 2104f
	addi %r24, %r11, -11
	cmpldi %cr0, %r24, 0
	beq %cr0, 2106f
	addi %r24, %r11, -12
	cmpldi %cr0, %r24, 0
	beq %cr0, 2108f
	addi %r24, %r11, -13
	cmpldi %cr0, %r24, 0
	beq %cr0, 2110f
	addi %r24, %r11, -14
	cmpldi %cr0, %r24, 0
	beq %cr0, 2112f
	addi %r24, %r11, -15
	cmpldi %cr0, %r24, 0
	beq %cr0, 2114f
	addi %r24, %r11, -16
	cmpldi %cr0, %r24, 0
	beq %cr0, 2116f
	addi %r24, %r11, -17
	cmpldi %cr0, %r24, 0
	beq %cr0, 2118f
	addi %r24, %r11, -18
	cmpldi %cr0, %r24, 0
	beq %cr0, 2120f
	addi %r24, %r11, -19
	cmpldi %cr0, %r24, 0
	beq %cr0, 2122f
	addi %r24, %r11, -20
	cmpldi %cr0, %r24, 0
	beq %cr0, 2124f
	addi %r24, %r11, -21
	cmpldi %cr0, %r24, 0
	beq %cr0, 2126f
	addi %r24, %r11, -22
	cmpldi %cr0, %r24, 0
	beq %cr0, 2128f
	addi %r24, %r11, -23
	cmpldi %cr0, %r24, 0
	beq %cr0, 2130f
	addi %r24, %r11, -24
	cmpldi %cr0, %r24, 0
	beq %cr0, 2132f
	addi %r24, %r11, -25
	cmpldi %cr0, %r24, 0
	beq %cr0, 2134f
	addi %r24, %r11, -26
	cmpldi %cr0, %r24, 0
	beq %cr0, 2136f
	addi %r24, %r11, -27
	cmpldi %cr0, %r24, 0
	beq %cr0, 2138f
	addi %r24, %r11, -28
	cmpldi %cr0, %r24, 0
	beq %cr0, 2140f
	addi %r24, %r11, -29
	cmpldi %cr0, %r24, 0
	beq %cr0, 2142f
	addi %r24, %r11, -30
	cmpldi %cr0, %r24, 0
	beq %cr0, 2144f
	addi %r24, %r11, -31
	cmpldi %cr0, %r24, 0
	beq %cr0, 2146f
	addi %r24, %r11, -32
	cmpldi %cr0, %r24, 0
	beq %cr0, 2148f
	addi %r24, %r11, -33
	cmpldi %cr0, %r24, 0
	beq %cr0, 2150f
	addi %r24, %r11, -34
	cmpldi %cr0, %r24, 0
	beq %cr0, 2152f
	addi %r24, %r11, -35
	cmpldi %cr0, %r24, 0
	beq %cr0, 2154f
	addi %r24, %r11, -36
	cmpldi %cr0, %r24, 0
	beq %cr0, 2156f
	addi %r24, %r11, -37
	cmpldi %cr0, %r24, 0
	beq %cr0, 2158f
	addi %r24, %r11, -38
	cmpldi %cr0, %r24, 0
	beq %cr0, 2160f
	addi %r24, %r11, -39
	cmpldi %cr0, %r24, 0
	beq %cr0, 2162f
	b 2163f
2162:
	xor %r28, %r18, %r19
	xor %r28, %r28, %r20
	xor %r28, %r28, %r21
	lwz %r24, 48(%r6)
	xor %r28, %r28, %r24
	stw %r28, 60(%r5)
2163:
	b 2161f
2160:
	xor %r28, %r18, %r19
	xor %r28, %r28, %r20
	xor %r28, %r28, %r21
	lwz %r24, 52(%r6)
	xor %r28, %r28, %r24
	stw %r28, 56(%r5)
2161:
	b 2159f
2158:
	xor %r28, %r18, %r19
	xor %r28, %r28, %r20
	xor %r28, %r28, %r21
	lwz %r24, 56(%r6)
	xor %r28, %r28, %r24
	stw %r28, 52(%r5)
2159:
	b 2157f
2156:
	xor %r28, %r18, %r19
	xor %r28, %r28, %r20
	xor %r28, %r28, %r21
	lwz %r24, 60(%r6)
	xor %r28, %r28, %r24
	stw %r28, 48(%r5)
2157:
	b 2155f
2154:
	stw %r18, 48(%r6)
	stw %r19, 52(%r6)
	stw %r20, 56(%r6)
	stw %r21, 60(%r6)
2155:
	b 2153f
2152:
	xor %r28, %r18, %r19
	xor %r28, %r28, %r20
	xor %r28, %r28, %r21
	lwz %r24, 56(%r6)
	xor %r28, %r28, %r24
	li %r25, 44
	lwbrx %r24, %r6, %r25
	xor %r28, %r28, %r24
	li %r25, 28
	stwbrx %r28, %r6, %r25
2153:
	b 2151f
2150:
	xor %r28, %r18, %r19
	xor %r28, %r28, %r20
	xor %r28, %r28, %r21
	lwz %r24, 60(%r6)
	xor %r28, %r28, %r24
	li %r25, 36
	lwbrx %r24, %r6, %r25
	xor %r28, %r28, %r24
	li %r25, 24
	stwbrx %r28, %r6, %r25
2151:
	b 2149f
2148:
	xor %r28, %r18, %r19
	xor %r28, %r28, %r20
	xor %r28, %r28, %r21
	lwz %r24, 48(%r6)
	xor %r28, %r28, %r24
	li %r25, 32
	lwbrx %r24, %r6, %r25
	xor %r28, %r28, %r24
	li %r25, 20
	stwbrx %r28, %r6, %r25
2149:
	b 2147f
2146:
	xor %r28, %r18, %r19
	xor %r28, %r28, %r20
	xor %r28, %r28, %r21
	lwz %r24, 52(%r6)
	xor %r28, %r28, %r24
	li %r25, 40
	lwbrx %r24, %r6, %r25
	xor %r28, %r28, %r24
	li %r25, 16
	stwbrx %r28, %r6, %r25
2147:
	b 2145f
2144:
	stw %r18, 48(%r6)
	stw %r19, 52(%r6)
	stw %r20, 56(%r6)
	stw %r21, 60(%r6)
2145:
	b 2143f
2142:
	xor %r28, %r18, %r19
	xor %r28, %r28, %r20
	xor %r28, %r28, %r21
	lwz %r24, 48(%r6)
	xor %r28, %r28, %r24
	stw %r28, 44(%r5)
2143:
	b 2141f
2140:
	xor %r28, %r18, %r19
	xor %r28, %r28, %r20
	xor %r28, %r28, %r21
	lwz %r24, 52(%r6)
	xor %r28, %r28, %r24
	stw %r28, 40(%r5)
2141:
	b 2139f
2138:
	xor %r28, %r18, %r19
	xor %r28, %r28, %r20
	xor %r28, %r28, %r21
	lwz %r24, 56(%r6)
	xor %r28, %r28, %r24
	stw %r28, 36(%r5)
2139:
	b 2137f
2136:
	xor %r28, %r18, %r19
	xor %r28, %r28, %r20
	xor %r28, %r28, %r21
	lwz %r24, 60(%r6)
	xor %r28, %r28, %r24
	stw %r28, 32(%r5)
2137:
	b 2135f
2134:
	stw %r18, 48(%r6)
	stw %r19, 52(%r6)
	stw %r20, 56(%r6)
	stw %r21, 60(%r6)
2135:
	b 2133f
2132:
	xor %r28, %r18, %r19
	xor %r28, %r28, %r20
	xor %r28, %r28, %r21
	lwz %r24, 56(%r6)
	xor %r28, %r28, %r24
	li %r25, 20
	lwbrx %r24, %r6, %r25
	xor %r28, %r28, %r24
	li %r25, 44
	stwbrx %r28, %r6, %r25
2133:
	b 2131f
2130:
	xor %r28, %r18, %r19
	xor %r28, %r28, %r20
	xor %r28, %r28, %r21
	lwz %r24, 60(%r6)
	xor %r28, %r28, %r24
	li %r25, 28
	lwbrx %r24, %r6, %r25
	xor %r28, %r28, %r24
	li %r25, 40
	stwbrx %r28, %r6, %r25
2131:
	b 2129f
2128:
	xor %r28, %r18, %r19
	xor %r28, %r28, %r20
	xor %r28, %r28, %r21
	lwz %r24, 48(%r6)
	xor %r28, %r28, %r24
	li %r25, 24
	lwbrx %r24, %r6, %r25
	xor %r28, %r28, %r24
	li %r25, 36
	stwbrx %r28, %r6, %r25
2129:
	b 2127f
2126:
	xor %r28, %r18, %r19
	xor %r28, %r28, %r20
	xor %r28, %r28, %r21
	lwz %r24, 52(%r6)
	xor %r28, %r28, %r24
	li %r25, 16
	lwbrx %r24, %r6, %r25
	xor %r28, %r28, %r24
	li %r25, 32
	stwbrx %r28, %r6, %r25
2127:
	b 2125f
2124:
	stw %r18, 48(%r6)
	stw %r19, 52(%r6)
	stw %r20, 56(%r6)
	stw %r21, 60(%r6)
2125:
	b 2123f
2122:
	xor %r28, %r18, %r19
	xor %r28, %r28, %r20
	xor %r28, %r28, %r21
	lwz %r24, 48(%r6)
	xor %r28, %r28, %r24
	stw %r28, 28(%r5)
2123:
	b 2121f
2120:
	xor %r28, %r18, %r19
	xor %r28, %r28, %r20
	xor %r28, %r28, %r21
	lwz %r24, 52(%r6)
	xor %r28, %r28, %r24
	stw %r28, 24(%r5)
2121:
	b 2119f
2118:
	xor %r28, %r18, %r19
	xor %r28, %r28, %r20
	xor %r28, %r28, %r21
	lwz %r24, 56(%r6)
	xor %r28, %r28, %r24
	stw %r28, 20(%r5)
2119:
	b 2117f
2116:
	xor %r28, %r18, %r19
	xor %r28, %r28, %r20
	xor %r28, %r28, %r21
	lwz %r24, 60(%r6)
	xor %r28, %r28, %r24
	stw %r28, 16(%r5)
2117:
	b 2115f
2114:
	stw %r18, 48(%r6)
	stw %r19, 52(%r6)
	stw %r20, 56(%r6)
	stw %r21, 60(%r6)
2115:
	b 2113f
2112:
	xor %r28, %r18, %r19
	xor %r28, %r28, %r20
	xor %r28, %r28, %r21
	lwz %r24, 56(%r6)
	xor %r28, %r28, %r24
	li %r25, 44
	lwbrx %r24, %r6, %r25
	xor %r28, %r28, %r24
	li %r25, 28
	stwbrx %r28, %r6, %r25
2113:
	b 2111f
2110:
	xor %r28, %r18, %r19
	xor %r28, %r28, %r20
	xor %r28, %r28, %r21
	lwz %r24, 60(%r6)
	xor %r28, %r28, %r24
	li %r25, 36
	lwbrx %r24, %r6, %r25
	xor %r28, %r28, %r24
	li %r25, 24
	stwbrx %r28, %r6, %r25
2111:
	b 2109f
2108:
	xor %r28, %r18, %r19
	xor %r28, %r28, %r20
	xor %r28, %r28, %r21
	lwz %r24, 48(%r6)
	xor %r28, %r28, %r24
	li %r25, 32
	lwbrx %r24, %r6, %r25
	xor %r28, %r28, %r24
	li %r25, 20
	stwbrx %r28, %r6, %r25
2109:
	b 2107f
2106:
	xor %r28, %r18, %r19
	xor %r28, %r28, %r20
	xor %r28, %r28, %r21
	lwz %r24, 52(%r6)
	xor %r28, %r28, %r24
	li %r25, 40
	lwbrx %r24, %r6, %r25
	xor %r28, %r28, %r24
	li %r25, 16
	stwbrx %r28, %r6, %r25
2107:
	b 2105f
2104:
	stw %r18, 48(%r6)
	stw %r19, 52(%r6)
	stw %r20, 56(%r6)
	stw %r21, 60(%r6)
2105:
	b 2103f
2102:
	xor %r28, %r18, %r19
	xor %r28, %r28, %r20
	xor %r28, %r28, %r21
	lwz %r24, 48(%r6)
	xor %r28, %r28, %r24
	stw %r28, 12(%r5)
2103:
	b 2101f
2100:
	xor %r28, %r18, %r19
	xor %r28, %r28, %r20
	xor %r28, %r28, %r21
	lwz %r24, 52(%r6)
	xor %r28, %r28, %r24
	stw %r28, 8(%r5)
2101:
	b 299f
298:
	xor %r28, %r18, %r19
	xor %r28, %r28, %r20
	xor %r28, %r28, %r21
	lwz %r24, 56(%r6)
	xor %r28, %r28, %r24
	stw %r28, 4(%r5)
299:
	b 297f
296:
	xor %r28, %r18, %r19
	xor %r28, %r28, %r20
	xor %r28, %r28, %r21
	lwz %r24, 60(%r6)
	xor %r28, %r28, %r24
	stw %r28, 0(%r5)
297:
	b 295f
294:
	stw %r18, 48(%r6)
	stw %r19, 52(%r6)
	stw %r20, 56(%r6)
	stw %r21, 60(%r6)
295:
	b 293f
292:
	xor %r28, %r18, %r19
	xor %r28, %r28, %r20
	xor %r28, %r28, %r21
	lwz %r24, 56(%r6)
	xor %r28, %r28, %r24
	li %r25, 20
	lwbrx %r24, %r6, %r25
	xor %r28, %r28, %r24
	li %r25, 44
	stwbrx %r28, %r6, %r25
293:
	b 291f
290:
	xor %r28, %r18, %r19
	xor %r28, %r28, %r20
	xor %r28, %r28, %r21
	lwz %r24, 60(%r6)
	xor %r28, %r28, %r24
	li %r25, 28
	lwbrx %r24, %r6, %r25
	xor %r28, %r28, %r24
	li %r25, 40
	stwbrx %r28, %r6, %r25
291:
	b 289f
288:
	xor %r28, %r18, %r19
	xor %r28, %r28, %r20
	xor %r28, %r28, %r21
	lwz %r24, 48(%r6)
	xor %r28, %r28, %r24
	li %r25, 24
	lwbrx %r24, %r6, %r25
	xor %r28, %r28, %r24
	li %r25, 36
	stwbrx %r28, %r6, %r25
289:
	b 287f
286:
	xor %r28, %r18, %r19
	xor %r28, %r28, %r20
	xor %r28, %r28, %r21
	lwz %r24, 52(%r6)
	xor %r28, %r28, %r24
	li %r25, 16
	lwbrx %r24, %r6, %r25
	xor %r28, %r28, %r24
	li %r25, 32
	stwbrx %r28, %r6, %r25
287:
	b 285f
284:
	stw %r18, 48(%r6)
	stw %r19, 52(%r6)
	stw %r20, 56(%r6)
	stw %r21, 60(%r6)
285:
	addi %r11, %r11, 1
	addi %r24, %r11, -40
	cmpldi %cr0, %r24, 0
	bne %cr0, 22b
	addi %r5, %r5, 64
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 21b
	ld %r14, 64(%r6)
	ld %r15, 72(%r6)
	ld %r16, 80(%r6)
	ld %r17, 88(%r6)
	ld %r18, 96(%r6)
	ld %r19, 104(%r6)
	ld %r20, 112(%r6)
	ld %r21, 120(%r6)
	ld %r22, 128(%r6)
	ld %r23, 136(%r6)
	ld %r24, 144(%r6)
	ld %r25, 152(%r6)
	ld %r26, 160(%r6)
	ld %r27, 168(%r6)
	ld %r28, 176(%r6)
	ld %r29, 184(%r6)
	ld %r30, 192(%r6)
	ld %r0, 200(%r6)
	mtlr %r0
	blr

vg_cast5_ecb_encrypt:
	mflr %r0
	std %r0, 200(%r7)
	std %r14, 64(%r7)
	std %r15, 72(%r7)
	std %r16, 80(%r7)
	std %r17, 88(%r7)
	std %r18, 96(%r7)
	std %r19, 104(%r7)
	std %r20, 112(%r7)
	std %r21, 120(%r7)
	std %r22, 128(%r7)
	std %r23, 136(%r7)
	std %r24, 144(%r7)
	std %r25, 152(%r7)
	std %r26, 160(%r7)
	std %r27, 168(%r7)
	std %r28, 176(%r7)
	std %r29, 184(%r7)
	std %r30, 192(%r7)
	bcl 20, 31, 2f
2:
	mflr %r27
	addis %r27, %r27, ({VG_CAST5_S1234}
	addi %r27, %r27, ({VG_CAST5_S1234}
	li %r26, 255
	li %r0, 0
	cmpldi %cr0, %r6, 0
	beq %cr0, 20f
22:
	lwbrx %r8, %r5, %r0
	addi %r24, %r5, 4
	lwbrx %r9, %r24, %r0
	or %r10, %r3, %r3
	or %r11, %r4, %r4
	li %r12, 1
23:
	cmpldi %cr0, %r12, 0
	beq %cr0, 24f
	addi %r24, %r12, -1
	cmpldi %cr0, %r24, 0
	beq %cr0, 26f
	lwz %r28, 0(%r10)
	xor %r28, %r28, %r9
	b 27f
26:
	lwz %r28, 0(%r10)
	add %r28, %r28, %r9
27:
	b 25f
24:
	lwz %r28, 0(%r10)
	subf %r28, %r9, %r28
25:
	lwz %r29, 64(%r10)
	rldicr %r30, %r29, 63, 0
	rldicl %r30, %r30, 1, 63
	addi %r30, %r30, -1
	rlwinm %r24, %r28, 1, 0, 31
	xor %r25, %r28, %r24
	and %r25, %r25, %r30
	xor %r28, %r24, %r25
	rldicr %r30, %r29, 62, 1
	rldicl %r30, %r30, 1, 63
	addi %r30, %r30, -1
	rlwinm %r24, %r28, 2, 0, 31
	xor %r25, %r28, %r24
	and %r25, %r25, %r30
	xor %r28, %r24, %r25
	rldicr %r30, %r29, 61, 2
	rldicl %r30, %r30, 1, 63
	addi %r30, %r30, -1
	rlwinm %r24, %r28, 4, 0, 31
	xor %r25, %r28, %r24
	and %r25, %r25, %r30
	xor %r28, %r24, %r25
	rldicr %r30, %r29, 60, 3
	rldicl %r30, %r30, 1, 63
	addi %r30, %r30, -1
	rlwinm %r24, %r28, 8, 0, 31
	xor %r25, %r28, %r24
	and %r25, %r25, %r30
	xor %r28, %r24, %r25
	rldicr %r30, %r29, 59, 4
	rldicl %r30, %r30, 1, 63
	addi %r30, %r30, -1
	rlwinm %r24, %r28, 16, 0, 31
	xor %r25, %r28, %r24
	and %r25, %r25, %r30
	xor %r28, %r24, %r25
	and %r14, %r28, %r26
	rlwinm %r15, %r28, 24, 8, 31
	and %r15, %r15, %r26
	rlwinm %r16, %r28, 16, 16, 31
	and %r16, %r16, %r26
	rlwinm %r17, %r28, 8, 24, 31
	or %r23, %r27, %r27
	li %r22, 0
	li %r18, 0
	li %r19, 0
	li %r20, 0
	li %r21, 0
28:
	lwz %r25, 0(%r23)
	xor %r24, %r14, %r22
	addi %r24, %r24, -1
	rldicl %r24, %r24, 1, 63
	subf %r24, %r24, %r0
	and %r25, %r25, %r24
	or %r18, %r18, %r25
	lwz %r25, 4(%r23)
	xor %r24, %r15, %r22
	addi %r24, %r24, -1
	rldicl %r24, %r24, 1, 63
	subf %r24, %r24, %r0
	and %r25, %r25, %r24
	or %r19, %r19, %r25
	lwz %r25, 8(%r23)
	xor %r24, %r16, %r22
	addi %r24, %r24, -1
	rldicl %r24, %r24, 1, 63
	subf %r24, %r24, %r0
	and %r25, %r25, %r24
	or %r20, %r20, %r25
	lwz %r25, 12(%r23)
	xor %r24, %r17, %r22
	addi %r24, %r24, -1
	rldicl %r24, %r24, 1, 63
	subf %r24, %r24, %r0
	and %r25, %r25, %r24
	or %r21, %r21, %r25
	addi %r23, %r23, 16
	addi %r22, %r22, 1
	addi %r24, %r22, -256
	cmpldi %cr0, %r24, 0
	bne %cr0, 28b
	cmpldi %cr0, %r12, 0
	beq %cr0, 29f
	addi %r24, %r12, -1
	cmpldi %cr0, %r24, 0
	beq %cr0, 211f
	subf %r28, %r20, %r21
	add %r28, %r28, %r19
	xor %r28, %r28, %r18
	b 212f
211:
	xor %r28, %r21, %r20
	subf %r28, %r19, %r28
	add %r28, %r28, %r18
212:
	b 210f
29:
	add %r28, %r21, %r20
	xor %r28, %r28, %r19
	subf %r28, %r18, %r28
210:
	xor %r28, %r28, %r8
	or %r8, %r9, %r9
	or %r9, %r28, %r28
	addi %r10, %r10, 4
	addi %r24, %r12, -2
	cmpldi %cr0, %r24, 0
	beq %cr0, 213f
	addi %r12, %r12, 1
	b 214f
213:
	li %r12, 0
214:
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 23b
	stwbrx %r9, %r5, %r0
	addi %r24, %r5, 4
	stwbrx %r8, %r24, %r0
	addi %r5, %r5, 8
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 22b
	b 21f
20:
21:
	ld %r14, 64(%r7)
	ld %r15, 72(%r7)
	ld %r16, 80(%r7)
	ld %r17, 88(%r7)
	ld %r18, 96(%r7)
	ld %r19, 104(%r7)
	ld %r20, 112(%r7)
	ld %r21, 120(%r7)
	ld %r22, 128(%r7)
	ld %r23, 136(%r7)
	ld %r24, 144(%r7)
	ld %r25, 152(%r7)
	ld %r26, 160(%r7)
	ld %r27, 168(%r7)
	ld %r28, 176(%r7)
	ld %r29, 184(%r7)
	ld %r30, 192(%r7)
	ld %r0, 200(%r7)
	mtlr %r0
	blr

vg_cast5_ecb_decrypt:
	mflr %r0
	std %r0, 200(%r7)
	std %r14, 64(%r7)
	std %r15, 72(%r7)
	std %r16, 80(%r7)
	std %r17, 88(%r7)
	std %r18, 96(%r7)
	std %r19, 104(%r7)
	std %r20, 112(%r7)
	std %r21, 120(%r7)
	std %r22, 128(%r7)
	std %r23, 136(%r7)
	std %r24, 144(%r7)
	std %r25, 152(%r7)
	std %r26, 160(%r7)
	std %r27, 168(%r7)
	std %r28, 176(%r7)
	std %r29, 184(%r7)
	std %r30, 192(%r7)
	bcl 20, 31, 2f
2:
	mflr %r27
	addis %r27, %r27, ({VG_CAST5_S1234}
	addi %r27, %r27, ({VG_CAST5_S1234}
	li %r26, 255
	li %r0, 0
	cmpldi %cr0, %r6, 0
	beq %cr0, 20f
22:
	lwbrx %r8, %r5, %r0
	addi %r24, %r5, 4
	lwbrx %r9, %r24, %r0
	rldicr %r24, %r4, 2, 61
	add %r10, %r3, %r24
	addi %r10, %r10, -4
	or %r11, %r4, %r4
	rldicl %r24, %r4, 62, 2
	addi %r12, %r24, -3
23:
	cmpldi %cr0, %r12, 0
	beq %cr0, 24f
	addi %r24, %r12, -1
	cmpldi %cr0, %r24, 0
	beq %cr0, 26f
	lwz %r28, 0(%r10)
	xor %r28, %r28, %r9
	b 27f
26:
	lwz %r28, 0(%r10)
	add %r28, %r28, %r9
27:
	b 25f
24:
	lwz %r28, 0(%r10)
	subf %r28, %r9, %r28
25:
	lwz %r29, 64(%r10)
	rldicr %r30, %r29, 63, 0
	rldicl %r30, %r30, 1, 63
	addi %r30, %r30, -1
	rlwinm %r24, %r28, 1, 0, 31
	xor %r25, %r28, %r24
	and %r25, %r25, %r30
	xor %r28, %r24, %r25
	rldicr %r30, %r29, 62, 1
	rldicl %r30, %r30, 1, 63
	addi %r30, %r30, -1
	rlwinm %r24, %r28, 2, 0, 31
	xor %r25, %r28, %r24
	and %r25, %r25, %r30
	xor %r28, %r24, %r25
	rldicr %r30, %r29, 61, 2
	rldicl %r30, %r30, 1, 63
	addi %r30, %r30, -1
	rlwinm %r24, %r28, 4, 0, 31
	xor %r25, %r28, %r24
	and %r25, %r25, %r30
	xor %r28, %r24, %r25
	rldicr %r30, %r29, 60, 3
	rldicl %r30, %r30, 1, 63
	addi %r30, %r30, -1
	rlwinm %r24, %r28, 8, 0, 31
	xor %r25, %r28, %r24
	and %r25, %r25, %r30
	xor %r28, %r24, %r25
	rldicr %r30, %r29, 59, 4
	rldicl %r30, %r30, 1, 63
	addi %r30, %r30, -1
	rlwinm %r24, %r28, 16, 0, 31
	xor %r25, %r28, %r24
	and %r25, %r25, %r30
	xor %r28, %r24, %r25
	and %r14, %r28, %r26
	rlwinm %r15, %r28, 24, 8, 31
	and %r15, %r15, %r26
	rlwinm %r16, %r28, 16, 16, 31
	and %r16, %r16, %r26
	rlwinm %r17, %r28, 8, 24, 31
	or %r23, %r27, %r27
	li %r22, 0
	li %r18, 0
	li %r19, 0
	li %r20, 0
	li %r21, 0
28:
	lwz %r25, 0(%r23)
	xor %r24, %r14, %r22
	addi %r24, %r24, -1
	rldicl %r24, %r24, 1, 63
	subf %r24, %r24, %r0
	and %r25, %r25, %r24
	or %r18, %r18, %r25
	lwz %r25, 4(%r23)
	xor %r24, %r15, %r22
	addi %r24, %r24, -1
	rldicl %r24, %r24, 1, 63
	subf %r24, %r24, %r0
	and %r25, %r25, %r24
	or %r19, %r19, %r25
	lwz %r25, 8(%r23)
	xor %r24, %r16, %r22
	addi %r24, %r24, -1
	rldicl %r24, %r24, 1, 63
	subf %r24, %r24, %r0
	and %r25, %r25, %r24
	or %r20, %r20, %r25
	lwz %r25, 12(%r23)
	xor %r24, %r17, %r22
	addi %r24, %r24, -1
	rldicl %r24, %r24, 1, 63
	subf %r24, %r24, %r0
	and %r25, %r25, %r24
	or %r21, %r21, %r25
	addi %r23, %r23, 16
	addi %r22, %r22, 1
	addi %r24, %r22, -256
	cmpldi %cr0, %r24, 0
	bne %cr0, 28b
	cmpldi %cr0, %r12, 0
	beq %cr0, 29f
	addi %r24, %r12, -1
	cmpldi %cr0, %r24, 0
	beq %cr0, 211f
	subf %r28, %r20, %r21
	add %r28, %r28, %r19
	xor %r28, %r28, %r18
	b 212f
211:
	xor %r28, %r21, %r20
	subf %r28, %r19, %r28
	add %r28, %r28, %r18
212:
	b 210f
29:
	add %r28, %r21, %r20
	xor %r28, %r28, %r19
	subf %r28, %r18, %r28
210:
	xor %r28, %r28, %r8
	or %r8, %r9, %r9
	or %r9, %r28, %r28
	addi %r10, %r10, -4
	cmpldi %cr0, %r12, 0
	beq %cr0, 213f
	addi %r12, %r12, -1
	b 214f
213:
	li %r12, 2
214:
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 23b
	stwbrx %r9, %r5, %r0
	addi %r24, %r5, 4
	stwbrx %r8, %r24, %r0
	addi %r5, %r5, 8
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 22b
	b 21f
20:
21:
	ld %r14, 64(%r7)
	ld %r15, 72(%r7)
	ld %r16, 80(%r7)
	ld %r17, 88(%r7)
	ld %r18, 96(%r7)
	ld %r19, 104(%r7)
	ld %r20, 112(%r7)
	ld %r21, 120(%r7)
	ld %r22, 128(%r7)
	ld %r23, 136(%r7)
	ld %r24, 144(%r7)
	ld %r25, 152(%r7)
	ld %r26, 160(%r7)
	ld %r27, 168(%r7)
	ld %r28, 176(%r7)
	ld %r29, 184(%r7)
	ld %r30, 192(%r7)
	ld %r0, 200(%r7)
	mtlr %r0
	blr
