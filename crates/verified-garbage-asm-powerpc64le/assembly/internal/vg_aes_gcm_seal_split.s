// The functions of `src/internal/vg_aes_gcm_seal_split.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_gcm_seal_split:
	stdu %r1, -2688(%r1)
	addi %r12, %r1, 0
	ld %r0, 2784(%r12)
	std %r0, 96(%r12)
	ld %r0, 2792(%r12)
	std %r0, 104(%r12)
	ld %r0, 2800(%r12)
	std %r0, 112(%r12)
	addi %r0, %r12, 128
	std %r0, 120(%r12)
	stdu %r1, -112(%r1)
	addi %r12, %r1, 0
	ld %r11, 232(%r12)
	std %r9, 112(%r11)
	std %r10, 120(%r11)
	ld %r9, 208(%r12)
	ld %r10, 216(%r12)
	ld %r0, 224(%r12)
	std %r0, 96(%r12)
	std %r11, 104(%r12)
	addi %r12, %r1, 0
	ld %r12, 104(%r12)
	std %r18, 128(%r12)
	std %r19, 136(%r12)
	std %r20, 144(%r12)
	std %r21, 152(%r12)
	std %r22, 160(%r12)
	std %r23, 168(%r12)
	std %r24, 176(%r12)
	std %r25, 184(%r12)
	std %r26, 192(%r12)
	std %r27, 200(%r12)
	std %r28, 208(%r12)
	std %r29, 216(%r12)
	std %r30, 224(%r12)
	std %r31, 232(%r12)
	mflr %r0
	std %r0, 240(%r12)
	or %r31, %r12, %r12
	or %r29, %r3, %r3
	or %r28, %r4, %r4
	addi %r30, %r31, 16
	or %r24, %r5, %r5
	or %r25, %r6, %r6
	or %r18, %r6, %r6
	or %r21, %r7, %r7
	or %r22, %r8, %r8
	or %r27, %r9, %r9
	or %r23, %r10, %r10
	addi %r12, %r1, 0
	ld %r20, 96(%r12)
	addi %r6, %r25, -12
	cmpldi %cr0, %r6, 0
	beq %cr0, 20f
	li %r0, 0
	std %r0, 0(%r30)
	std %r0, 8(%r30)
	li %r26, 0
	cmpldi %cr0, %r25, 0
	beq %cr0, 22f
	cmpldi %cr0, %r26, 0
	beq %cr0, 24f
	li %r5, 16
	subf %r5, %r26, %r5
	rldicl %r6, %r25, 60, 4
	cmpldi %cr0, %r6, 0
	bne %cr0, 26f
	subf %r6, %r5, %r25
	rldicl %r6, %r6, 1, 63
	cmpldi %cr0, %r6, 0
	bne %cr0, 28f
	b 29f
28:
	or %r5, %r25, %r25
29:
	b 27f
26:
27:
	addi %r4, %r30, 32
	add %r4, %r4, %r26
	or %r3, %r24, %r24
	add %r24, %r24, %r5
	subf %r25, %r5, %r25
	add %r26, %r26, %r5
210:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 210b
	addi %r6, %r26, -16
	cmpldi %cr0, %r6, 0
	beq %cr0, 211f
	b 212f
211:
	addi %r3, %r29, 240
	addi %r4, %r30, 0
	addi %r5, %r30, 32
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
212:
	b 25f
24:
25:
	or %r5, %r24, %r24
	rldicl %r6, %r25, 60, 4
	li %r0, 15
	and %r8, %r25, %r0
	subf %r9, %r8, %r25
	add %r24, %r24, %r9
	or %r25, %r8, %r8
	cmpldi %cr0, %r6, 0
	beq %cr0, 213f
	addi %r3, %r29, 240
	addi %r4, %r30, 0
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 214f
213:
214:
	cmpldi %cr0, %r25, 0
	beq %cr0, 215f
	or %r3, %r24, %r24
	addi %r4, %r30, 32
	or %r5, %r25, %r25
217:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 217b
	b 216f
215:
216:
	b 23f
22:
23:
	li %r0, 15
	and %r26, %r18, %r0
	cmpldi %cr0, %r26, 0
	beq %cr0, 218f
	li %r0, 0
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	addi %r3, %r30, 32
	addi %r4, %r31, 96
	or %r5, %r26, %r26
220:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 220b
	addi %r3, %r29, 240
	addi %r4, %r30, 0
	addi %r5, %r31, 96
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 219f
218:
219:
	li %r24, 0
	or %r26, %r18, %r18
	rldicr %r3, %r24, 3, 60
	rldicr %r4, %r26, 3, 60
	addi %r5, %r31, 96
	li %r6, 0
	stdbrx %r3, %r5, %r6
	li %r6, 8
	stdbrx %r4, %r5, %r6
	addi %r3, %r29, 240
	addi %r4, %r30, 0
	addi %r5, %r31, 96
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 21f
20:
	lwz %r3, 0(%r24)
	lwz %r4, 4(%r24)
	lwz %r5, 8(%r24)
	lis %r6, 256
	stw %r3, 0(%r30)
	stw %r4, 4(%r30)
	stw %r5, 8(%r30)
	stw %r6, 12(%r30)
21:
	lwz %r3, 0(%r30)
	lwz %r4, 4(%r30)
	lwz %r5, 8(%r30)
	addi %r7, %r30, 12
	li %r8, 0
	lwbrx %r6, %r7, %r8
	addi %r6, %r6, 1
	stw %r3, 48(%r30)
	stw %r4, 52(%r30)
	stw %r5, 56(%r30)
	addi %r7, %r30, 60
	stwbrx %r6, %r7, %r8
	std %r8, 16(%r30)
	std %r8, 24(%r30)
	or %r24, %r21, %r21
	or %r25, %r22, %r22
	li %r26, 0
	cmpldi %cr0, %r25, 0
	beq %cr0, 221f
	cmpldi %cr0, %r26, 0
	beq %cr0, 223f
	li %r5, 16
	subf %r5, %r26, %r5
	rldicl %r6, %r25, 60, 4
	cmpldi %cr0, %r6, 0
	bne %cr0, 225f
	subf %r6, %r5, %r25
	rldicl %r6, %r6, 1, 63
	cmpldi %cr0, %r6, 0
	bne %cr0, 227f
	b 228f
227:
	or %r5, %r25, %r25
228:
	b 226f
225:
226:
	addi %r4, %r30, 32
	add %r4, %r4, %r26
	or %r3, %r24, %r24
	add %r24, %r24, %r5
	subf %r25, %r5, %r25
	add %r26, %r26, %r5
229:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 229b
	addi %r6, %r26, -16
	cmpldi %cr0, %r6, 0
	beq %cr0, 230f
	b 231f
230:
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r30, 32
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
231:
	b 224f
223:
224:
	or %r5, %r24, %r24
	rldicl %r6, %r25, 60, 4
	li %r0, 15
	and %r8, %r25, %r0
	subf %r9, %r8, %r25
	add %r24, %r24, %r9
	or %r25, %r8, %r8
	cmpldi %cr0, %r6, 0
	beq %cr0, 232f
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 233f
232:
233:
	cmpldi %cr0, %r25, 0
	beq %cr0, 234f
	or %r3, %r24, %r24
	addi %r4, %r30, 32
	or %r5, %r25, %r25
236:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 236b
	b 235f
234:
235:
	b 222f
221:
222:
	li %r0, 15
	and %r26, %r22, %r0
	cmpldi %cr0, %r26, 0
	beq %cr0, 237f
	li %r0, 0
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	addi %r3, %r30, 32
	addi %r4, %r31, 96
	or %r5, %r26, %r26
239:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 239b
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r31, 96
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 238f
237:
238:
	cmpldi %cr0, %r23, 0
	beq %cr0, 240f
	ld %r7, 112(%r31)
	ld %r8, 120(%r31)
	li %r0, 15
	and %r5, %r8, %r0
	subf %r11, %r5, %r8
	add %r3, %r7, %r11
	add %r4, %r27, %r11
	cmpldi %cr0, %r5, 0
	beq %cr0, 242f
244:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 244b
	b 243f
242:
243:
	or %r3, %r29, %r29
	or %r4, %r28, %r28
	addi %r5, %r30, 48
	addi %r6, %r30, 16
	rldicl %r8, %r8, 60, 4
	or %r9, %r27, %r27
	rldicl %r10, %r23, 60, 4
	addi %r0, %r31, 448
	addi %r12, %r1, 0
	std %r0, 96(%r12)
	bl {vg_aes_gcm_encrypt_blocks_split}
	li %r0, 15
	and %r25, %r23, %r0
	subf %r12, %r25, %r23
	add %r24, %r27, %r12
	li %r26, 0
	cmpldi %cr0, %r25, 0
	beq %cr0, 245f
	li %r0, 0
	std %r0, 64(%r30)
	std %r0, 72(%r30)
	addi %r6, %r30, 64
	li %r7, 1
	or %r3, %r29, %r29
	or %r4, %r28, %r28
	addi %r5, %r30, 48
	addi %r8, %r31, 512
	bl {vg_aes_ctr32}
	addi %r3, %r30, 64
	or %r4, %r24, %r24
	or %r5, %r25, %r25
247:
	lbz %r0, 0(%r4)
	lbz %r6, 0(%r3)
	xor %r0, %r0, %r6
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 247b
	b 246f
245:
246:
	cmpldi %cr0, %r25, 0
	beq %cr0, 248f
	cmpldi %cr0, %r26, 0
	beq %cr0, 250f
	li %r5, 16
	subf %r5, %r26, %r5
	rldicl %r6, %r25, 60, 4
	cmpldi %cr0, %r6, 0
	bne %cr0, 252f
	subf %r6, %r5, %r25
	rldicl %r6, %r6, 1, 63
	cmpldi %cr0, %r6, 0
	bne %cr0, 254f
	b 255f
254:
	or %r5, %r25, %r25
255:
	b 253f
252:
253:
	addi %r4, %r30, 32
	add %r4, %r4, %r26
	or %r3, %r24, %r24
	add %r24, %r24, %r5
	subf %r25, %r5, %r25
	add %r26, %r26, %r5
256:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 256b
	addi %r6, %r26, -16
	cmpldi %cr0, %r6, 0
	beq %cr0, 257f
	b 258f
257:
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r30, 32
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
258:
	b 251f
250:
251:
	or %r5, %r24, %r24
	rldicl %r6, %r25, 60, 4
	li %r0, 15
	and %r8, %r25, %r0
	subf %r9, %r8, %r25
	add %r24, %r24, %r9
	or %r25, %r8, %r8
	cmpldi %cr0, %r6, 0
	beq %cr0, 259f
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 260f
259:
260:
	cmpldi %cr0, %r25, 0
	beq %cr0, 261f
	or %r3, %r24, %r24
	addi %r4, %r30, 32
	or %r5, %r25, %r25
263:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 263b
	b 262f
261:
262:
	b 249f
248:
249:
	cmpldi %cr0, %r23, 0
	beq %cr0, 264f
	li %r0, 15
	and %r26, %r23, %r0
	b 265f
264:
	li %r0, 15
	and %r26, %r22, %r0
265:
	cmpldi %cr0, %r26, 0
	beq %cr0, 266f
	li %r0, 0
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	addi %r3, %r30, 32
	addi %r4, %r31, 96
	or %r5, %r26, %r26
268:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 268b
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r31, 96
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 267f
266:
267:
	or %r24, %r22, %r22
	or %r26, %r23, %r23
	rldicr %r3, %r24, 3, 60
	rldicr %r4, %r26, 3, 60
	addi %r5, %r31, 96
	li %r6, 0
	stdbrx %r3, %r5, %r6
	li %r6, 8
	stdbrx %r4, %r5, %r6
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r31, 96
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
	ld %r3, 16(%r30)
	std %r3, 0(%r31)
	ld %r3, 24(%r30)
	std %r3, 8(%r31)
	or %r3, %r29, %r29
	or %r4, %r28, %r28
	or %r5, %r30, %r30
	addi %r6, %r31, 0
	li %r7, 1
	addi %r8, %r31, 512
	bl {vg_aes_ctr32}
	b 241f
240:
	or %r24, %r27, %r27
	or %r25, %r23, %r23
	li %r26, 0
	cmpldi %cr0, %r25, 0
	beq %cr0, 269f
	cmpldi %cr0, %r26, 0
	beq %cr0, 271f
	li %r5, 16
	subf %r5, %r26, %r5
	rldicl %r6, %r25, 60, 4
	cmpldi %cr0, %r6, 0
	bne %cr0, 273f
	subf %r6, %r5, %r25
	rldicl %r6, %r6, 1, 63
	cmpldi %cr0, %r6, 0
	bne %cr0, 275f
	b 276f
275:
	or %r5, %r25, %r25
276:
	b 274f
273:
274:
	addi %r3, %r30, 64
	add %r3, %r3, %r26
	or %r4, %r24, %r24
	add %r24, %r24, %r5
	subf %r25, %r5, %r25
277:
	lbz %r0, 0(%r4)
	lbz %r6, 0(%r3)
	xor %r0, %r0, %r6
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 277b
	b 272f
271:
272:
	or %r6, %r24, %r24
	rldicl %r7, %r25, 60, 4
	li %r0, 15
	and %r8, %r25, %r0
	subf %r9, %r8, %r25
	add %r24, %r24, %r9
	or %r25, %r8, %r8
	cmpldi %cr0, %r7, 0
	beq %cr0, 278f
	or %r3, %r29, %r29
	or %r4, %r28, %r28
	addi %r5, %r30, 48
	addi %r8, %r31, 512
	bl {vg_aes_ctr32}
	b 279f
278:
279:
	cmpldi %cr0, %r25, 0
	beq %cr0, 280f
	li %r0, 0
	std %r0, 64(%r30)
	std %r0, 72(%r30)
	addi %r6, %r30, 64
	li %r7, 1
	or %r3, %r29, %r29
	or %r4, %r28, %r28
	addi %r5, %r30, 48
	addi %r8, %r31, 512
	bl {vg_aes_ctr32}
	addi %r3, %r30, 64
	or %r4, %r24, %r24
	or %r5, %r25, %r25
282:
	lbz %r0, 0(%r4)
	lbz %r6, 0(%r3)
	xor %r0, %r0, %r6
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 282b
	b 281f
280:
281:
	b 270f
269:
270:
	or %r24, %r27, %r27
	or %r25, %r23, %r23
	li %r26, 0
	cmpldi %cr0, %r25, 0
	beq %cr0, 283f
	cmpldi %cr0, %r26, 0
	beq %cr0, 285f
	li %r5, 16
	subf %r5, %r26, %r5
	rldicl %r6, %r25, 60, 4
	cmpldi %cr0, %r6, 0
	bne %cr0, 287f
	subf %r6, %r5, %r25
	rldicl %r6, %r6, 1, 63
	cmpldi %cr0, %r6, 0
	bne %cr0, 289f
	b 290f
289:
	or %r5, %r25, %r25
290:
	b 288f
287:
288:
	addi %r4, %r30, 32
	add %r4, %r4, %r26
	or %r3, %r24, %r24
	add %r24, %r24, %r5
	subf %r25, %r5, %r25
	add %r26, %r26, %r5
291:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 291b
	addi %r6, %r26, -16
	cmpldi %cr0, %r6, 0
	beq %cr0, 292f
	b 293f
292:
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r30, 32
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
293:
	b 286f
285:
286:
	or %r5, %r24, %r24
	rldicl %r6, %r25, 60, 4
	li %r0, 15
	and %r8, %r25, %r0
	subf %r9, %r8, %r25
	add %r24, %r24, %r9
	or %r25, %r8, %r8
	cmpldi %cr0, %r6, 0
	beq %cr0, 294f
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 295f
294:
295:
	cmpldi %cr0, %r25, 0
	beq %cr0, 296f
	or %r3, %r24, %r24
	addi %r4, %r30, 32
	or %r5, %r25, %r25
298:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 298b
	b 297f
296:
297:
	b 284f
283:
284:
	li %r0, 15
	and %r26, %r23, %r0
	cmpldi %cr0, %r26, 0
	beq %cr0, 299f
	li %r0, 0
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	addi %r3, %r30, 32
	addi %r4, %r31, 96
	or %r5, %r26, %r26
2101:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2101b
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r31, 96
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 2100f
299:
2100:
	or %r24, %r22, %r22
	or %r26, %r23, %r23
	rldicr %r3, %r24, 3, 60
	rldicr %r4, %r26, 3, 60
	addi %r5, %r31, 96
	li %r6, 0
	stdbrx %r3, %r5, %r6
	li %r6, 8
	stdbrx %r4, %r5, %r6
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r31, 96
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
	ld %r3, 16(%r30)
	std %r3, 0(%r31)
	ld %r3, 24(%r30)
	std %r3, 8(%r31)
	or %r3, %r29, %r29
	or %r4, %r28, %r28
	or %r5, %r30, %r30
	addi %r6, %r31, 0
	li %r7, 1
	addi %r8, %r31, 512
	bl {vg_aes_ctr32}
241:
	ld %r3, 0(%r31)
	std %r3, 0(%r20)
	ld %r3, 8(%r31)
	std %r3, 8(%r20)
	or %r12, %r31, %r31
	ld %r0, 240(%r12)
	mtlr %r0
	ld %r18, 128(%r12)
	ld %r19, 136(%r12)
	ld %r20, 144(%r12)
	ld %r21, 152(%r12)
	ld %r22, 160(%r12)
	ld %r23, 168(%r12)
	ld %r24, 176(%r12)
	ld %r25, 184(%r12)
	ld %r26, 192(%r12)
	ld %r27, 200(%r12)
	ld %r28, 208(%r12)
	ld %r29, 216(%r12)
	ld %r30, 224(%r12)
	ld %r31, 232(%r12)
	addi %r1, %r1, 112
	addi %r1, %r1, 2688
	blr
