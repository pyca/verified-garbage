// The functions of `src/internal/vg_aes_gcm_open_split.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_gcm_open_split:
	addi %r12, %r1, 0
	ld %r12, 112(%r12)
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
	ld %r19, 104(%r12)
	li %r25, 0
	rldicl %r0, %r19, 62, 2
	cmpldi %cr0, %r0, 0
	beq %cr0, 20f
	rldicl %r0, %r19, 60, 4
	cmpldi %cr0, %r0, 0
	beq %cr0, 22f
	addi %r0, %r19, -16
	cmpldi %cr0, %r0, 0
	beq %cr0, 24f
	b 25f
24:
	li %r25, 1
25:
	b 23f
22:
	li %r25, 1
23:
	b 21f
20:
21:
	cmpldi %cr0, %r25, 0
	beq %cr0, 26f
	or %r25, %r18, %r18
	addi %r6, %r25, -12
	cmpldi %cr0, %r6, 0
	beq %cr0, 28f
	li %r0, 0
	std %r0, 0(%r30)
	std %r0, 8(%r30)
	li %r26, 0
	cmpldi %cr0, %r25, 0
	beq %cr0, 210f
	cmpldi %cr0, %r26, 0
	beq %cr0, 212f
	li %r5, 16
	subf %r5, %r26, %r5
	rldicl %r6, %r25, 60, 4
	cmpldi %cr0, %r6, 0
	bne %cr0, 214f
	subf %r6, %r5, %r25
	rldicl %r6, %r6, 1, 63
	cmpldi %cr0, %r6, 0
	bne %cr0, 216f
	b 217f
216:
	or %r5, %r25, %r25
217:
	b 215f
214:
215:
	addi %r4, %r30, 32
	add %r4, %r4, %r26
	or %r3, %r24, %r24
	add %r24, %r24, %r5
	subf %r25, %r5, %r25
	add %r26, %r26, %r5
218:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 218b
	addi %r6, %r26, -16
	cmpldi %cr0, %r6, 0
	beq %cr0, 219f
	b 220f
219:
	addi %r3, %r29, 240
	addi %r4, %r30, 0
	addi %r5, %r30, 32
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
220:
	b 213f
212:
213:
	or %r5, %r24, %r24
	rldicl %r6, %r25, 60, 4
	li %r0, 15
	and %r8, %r25, %r0
	subf %r9, %r8, %r25
	add %r24, %r24, %r9
	or %r25, %r8, %r8
	cmpldi %cr0, %r6, 0
	beq %cr0, 221f
	addi %r3, %r29, 240
	addi %r4, %r30, 0
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 222f
221:
222:
	cmpldi %cr0, %r25, 0
	beq %cr0, 223f
	or %r3, %r24, %r24
	addi %r4, %r30, 32
	or %r5, %r25, %r25
225:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 225b
	b 224f
223:
224:
	b 211f
210:
211:
	li %r0, 15
	and %r26, %r18, %r0
	cmpldi %cr0, %r26, 0
	beq %cr0, 226f
	li %r0, 0
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	addi %r3, %r30, 32
	addi %r4, %r31, 96
	or %r5, %r26, %r26
228:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 228b
	addi %r3, %r29, 240
	addi %r4, %r30, 0
	addi %r5, %r31, 96
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 227f
226:
227:
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
	b 29f
28:
	lwz %r3, 0(%r24)
	lwz %r4, 4(%r24)
	lwz %r5, 8(%r24)
	lis %r6, 256
	stw %r3, 0(%r30)
	stw %r4, 4(%r30)
	stw %r5, 8(%r30)
	stw %r6, 12(%r30)
29:
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
	beq %cr0, 229f
	cmpldi %cr0, %r26, 0
	beq %cr0, 231f
	li %r5, 16
	subf %r5, %r26, %r5
	rldicl %r6, %r25, 60, 4
	cmpldi %cr0, %r6, 0
	bne %cr0, 233f
	subf %r6, %r5, %r25
	rldicl %r6, %r6, 1, 63
	cmpldi %cr0, %r6, 0
	bne %cr0, 235f
	b 236f
235:
	or %r5, %r25, %r25
236:
	b 234f
233:
234:
	addi %r4, %r30, 32
	add %r4, %r4, %r26
	or %r3, %r24, %r24
	add %r24, %r24, %r5
	subf %r25, %r5, %r25
	add %r26, %r26, %r5
237:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 237b
	addi %r6, %r26, -16
	cmpldi %cr0, %r6, 0
	beq %cr0, 238f
	b 239f
238:
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r30, 32
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
239:
	b 232f
231:
232:
	or %r5, %r24, %r24
	rldicl %r6, %r25, 60, 4
	li %r0, 15
	and %r8, %r25, %r0
	subf %r9, %r8, %r25
	add %r24, %r24, %r9
	or %r25, %r8, %r8
	cmpldi %cr0, %r6, 0
	beq %cr0, 240f
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 241f
240:
241:
	cmpldi %cr0, %r25, 0
	beq %cr0, 242f
	or %r3, %r24, %r24
	addi %r4, %r30, 32
	or %r5, %r25, %r25
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
	b 230f
229:
230:
	li %r0, 15
	and %r26, %r22, %r0
	cmpldi %cr0, %r26, 0
	beq %cr0, 245f
	li %r0, 0
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	addi %r3, %r30, 32
	addi %r4, %r31, 96
	or %r5, %r26, %r26
247:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 247b
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r31, 96
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 246f
245:
246:
	li %r0, 0
	std %r0, 256(%r31)
	std %r0, 264(%r31)
	or %r3, %r20, %r20
	addi %r4, %r31, 256
	or %r5, %r19, %r19
248:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 248b
	cmpldi %cr0, %r23, 0
	beq %cr0, 249f
	addi %r12, %r1, 0
	ld %r26, 120(%r12)
	or %r3, %r29, %r29
	or %r4, %r28, %r28
	addi %r5, %r30, 16
	or %r6, %r27, %r27
	rldicl %r7, %r23, 60, 4
	or %r8, %r26, %r26
	or %r9, %r7, %r7
	addi %r10, %r31, 448
	bl {vg_aes_gcm_decrypt_blocks_to}
	li %r0, 15
	and %r25, %r23, %r0
	subf %r12, %r25, %r23
	add %r24, %r27, %r12
	add %r26, %r26, %r12
	cmpldi %cr0, %r25, 0
	beq %cr0, 251f
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
	or %r7, %r26, %r26
253:
	lbz %r0, 0(%r4)
	lbz %r6, 0(%r3)
	xor %r0, %r0, %r6
	stb %r0, 0(%r7)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r7, %r7, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 253b
	b 252f
251:
252:
	li %r0, 15
	and %r25, %r23, %r0
	subf %r12, %r25, %r23
	add %r24, %r27, %r12
	li %r26, 0
	cmpldi %cr0, %r25, 0
	beq %cr0, 254f
	cmpldi %cr0, %r26, 0
	beq %cr0, 256f
	li %r5, 16
	subf %r5, %r26, %r5
	rldicl %r6, %r25, 60, 4
	cmpldi %cr0, %r6, 0
	bne %cr0, 258f
	subf %r6, %r5, %r25
	rldicl %r6, %r6, 1, 63
	cmpldi %cr0, %r6, 0
	bne %cr0, 260f
	b 261f
260:
	or %r5, %r25, %r25
261:
	b 259f
258:
259:
	addi %r4, %r30, 32
	add %r4, %r4, %r26
	or %r3, %r24, %r24
	add %r24, %r24, %r5
	subf %r25, %r5, %r25
	add %r26, %r26, %r5
262:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 262b
	addi %r6, %r26, -16
	cmpldi %cr0, %r6, 0
	beq %cr0, 263f
	b 264f
263:
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r30, 32
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
264:
	b 257f
256:
257:
	or %r5, %r24, %r24
	rldicl %r6, %r25, 60, 4
	li %r0, 15
	and %r8, %r25, %r0
	subf %r9, %r8, %r25
	add %r24, %r24, %r9
	or %r25, %r8, %r8
	cmpldi %cr0, %r6, 0
	beq %cr0, 265f
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 266f
265:
266:
	cmpldi %cr0, %r25, 0
	beq %cr0, 267f
	or %r3, %r24, %r24
	addi %r4, %r30, 32
	or %r5, %r25, %r25
269:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 269b
	b 268f
267:
268:
	b 255f
254:
255:
	cmpldi %cr0, %r23, 0
	beq %cr0, 270f
	li %r0, 15
	and %r26, %r23, %r0
	b 271f
270:
	li %r0, 15
	and %r26, %r22, %r0
271:
	cmpldi %cr0, %r26, 0
	beq %cr0, 272f
	li %r0, 0
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	addi %r3, %r30, 32
	addi %r4, %r31, 96
	or %r5, %r26, %r26
274:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 274b
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r31, 96
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 273f
272:
273:
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
	std %r3, 112(%r31)
	ld %r3, 24(%r30)
	std %r3, 120(%r31)
	or %r3, %r29, %r29
	or %r4, %r28, %r28
	or %r5, %r30, %r30
	addi %r6, %r31, 112
	li %r7, 1
	addi %r8, %r31, 512
	bl {vg_aes_ctr32}
	b 250f
249:
	or %r24, %r27, %r27
	or %r25, %r23, %r23
	li %r26, 0
	cmpldi %cr0, %r25, 0
	beq %cr0, 275f
	cmpldi %cr0, %r26, 0
	beq %cr0, 277f
	li %r5, 16
	subf %r5, %r26, %r5
	rldicl %r6, %r25, 60, 4
	cmpldi %cr0, %r6, 0
	bne %cr0, 279f
	subf %r6, %r5, %r25
	rldicl %r6, %r6, 1, 63
	cmpldi %cr0, %r6, 0
	bne %cr0, 281f
	b 282f
281:
	or %r5, %r25, %r25
282:
	b 280f
279:
280:
	addi %r4, %r30, 32
	add %r4, %r4, %r26
	or %r3, %r24, %r24
	add %r24, %r24, %r5
	subf %r25, %r5, %r25
	add %r26, %r26, %r5
283:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 283b
	addi %r6, %r26, -16
	cmpldi %cr0, %r6, 0
	beq %cr0, 284f
	b 285f
284:
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r30, 32
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
285:
	b 278f
277:
278:
	or %r5, %r24, %r24
	rldicl %r6, %r25, 60, 4
	li %r0, 15
	and %r8, %r25, %r0
	subf %r9, %r8, %r25
	add %r24, %r24, %r9
	or %r25, %r8, %r8
	cmpldi %cr0, %r6, 0
	beq %cr0, 286f
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 287f
286:
287:
	cmpldi %cr0, %r25, 0
	beq %cr0, 288f
	or %r3, %r24, %r24
	addi %r4, %r30, 32
	or %r5, %r25, %r25
290:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 290b
	b 289f
288:
289:
	b 276f
275:
276:
	li %r0, 15
	and %r26, %r23, %r0
	cmpldi %cr0, %r26, 0
	beq %cr0, 291f
	li %r0, 0
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	addi %r3, %r30, 32
	addi %r4, %r31, 96
	or %r5, %r26, %r26
293:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 293b
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r31, 96
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 292f
291:
292:
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
	std %r3, 112(%r31)
	ld %r3, 24(%r30)
	std %r3, 120(%r31)
	or %r3, %r29, %r29
	or %r4, %r28, %r28
	or %r5, %r30, %r30
	addi %r6, %r31, 112
	li %r7, 1
	addi %r8, %r31, 512
	bl {vg_aes_ctr32}
250:
	li %r0, 0
	std %r0, 272(%r31)
	std %r0, 280(%r31)
	addi %r3, %r31, 112
	addi %r4, %r31, 272
	or %r5, %r19, %r19
294:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 294b
	ld %r3, 272(%r31)
	ld %r4, 256(%r31)
	xor %r3, %r3, %r4
	ld %r4, 280(%r31)
	ld %r5, 264(%r31)
	xor %r4, %r4, %r5
	or %r3, %r3, %r4
	li %r4, 0
	subf %r4, %r3, %r4
	or %r3, %r3, %r4
	rldicl %r3, %r3, 1, 63
	li %r4, 1
	subf %r3, %r3, %r4
	b 27f
26:
	li %r3, 0
27:
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
	blr
