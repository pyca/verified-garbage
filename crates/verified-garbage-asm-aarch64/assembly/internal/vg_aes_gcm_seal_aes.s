// The functions of `src/internal/vg_aes_gcm_seal_aes.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_gcm_seal_aes:
	sub sp, sp, #784
	add x16, sp, #0
	ldr x17, [sp, #784]
	str x17, [x16, #0]
	add x17, sp, #16
	str x17, [x16, #8]
	ldr x9, [sp, #8]
	str x20, [x9, #136]
	str x21, [x9, #144]
	str x22, [x9, #152]
	str x23, [x9, #160]
	str x24, [x9, #168]
	str x25, [x9, #176]
	str x26, [x9, #184]
	str x27, [x9, #192]
	str x28, [x9, #200]
	str x30, [x9, #208]
	str x19, [x9, #128]
	add x19, x9, #0
	add x20, x19, #16
	add x21, x0, #0
	add x22, x1, #0
	str x4, [x19, #216]
	str x5, [x19, #224]
	str x6, [x19, #232]
	str x7, [x19, #240]
	add x23, x2, #0
	add x24, x3, #0
	add x26, x3, #0
	movz x27, #0, lsl #0
	ldr x10, [sp, #0]
	str x10, [x19, #248]
	add x28, x10, #0
	movz x10, #0, lsl #0
	lsr x9, x5, #4
	cbz x9, 20f
	sub x9, x5, #16
	cbz x9, 22f
	movz x10, #1, lsl #0
	b 23f
22:
23:
	b 21f
20:
21:
	sub x9, x24, #12
	cbz x9, 24f
	movz x10, #1, lsl #0
	b 25f
24:
25:
	cbz x10, 26f
	sub x9, x24, #12
	cbz x9, 28f
	movz x9, #0, lsl #0
	str x9, [x20, #0]
	str x9, [x20, #8]
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	movz x10, #15, lsl #0
	and x25, x24, x10
	bl {vg_ghash_aes}
	add x12, x23, #0
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 210f
	lsr x14, x13, #2
	cbz x14, 212f
	lsr x14, x13, #3
	cbz x14, 214f
216:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 216b
	b 215f
214:
215:
	lsr x14, x13, #2
	cbz x14, 217f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 218f
217:
218:
	cbz x13, 219f
221:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 221b
	b 220f
219:
220:
	b 213f
212:
222:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 222b
213:
	b 211f
210:
211:
	cbz x25, 223f
	movz x3, #1, lsl #0
	b 224f
223:
	movz x3, #0, lsl #0
224:
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	lsl x9, x27, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #104]
	movz x3, #1, lsl #0
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	b 29f
28:
	ldr w9, [x23, #0]
	ldr w10, [x23, #4]
	ldr w11, [x23, #8]
	movz w12, #256, lsl #16
	str w9, [x20, #0]
	str w10, [x20, #4]
	str w11, [x20, #8]
	str w12, [x20, #12]
29:
	ldr w9, [x20, #0]
	ldr w10, [x20, #4]
	ldr w11, [x20, #8]
	ldr w12, [x20, #12]
	rev w12, w12
	add w12, w12, #1
	rev w12, w12
	str w9, [x20, #48]
	str w10, [x20, #52]
	str w11, [x20, #56]
	str w12, [x20, #60]
	movz x9, #0, lsl #0
	str x9, [x20, #16]
	str x9, [x20, #24]
	ldr x23, [x19, #216]
	ldr x24, [x19, #224]
	movz x25, #0, lsl #0
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_ghash_aes}
	add x11, x20, #32
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 225f
	lsr x14, x13, #2
	cbz x14, 227f
	lsr x14, x13, #3
	cbz x14, 229f
231:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 231b
	b 230f
229:
230:
	lsr x14, x13, #2
	cbz x14, 232f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 233f
232:
233:
	cbz x13, 234f
236:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 236b
	b 235f
234:
235:
	b 228f
227:
237:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 237b
228:
	b 226f
225:
226:
	ldr x9, [x19, #224]
	movz x10, #15, lsl #0
	and x25, x9, x10
	ldr x26, [x19, #240]
	movz x27, #0, lsl #0
	ldr x28, [x19, #232]
	cbz x26, 238f
	cbz x27, 240f
	movz x25, #0, lsl #0
	b 241f
240:
241:
	b 239f
238:
	movz x25, #0, lsl #0
239:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 242f
	lsr x14, x13, #2
	cbz x14, 244f
	lsr x14, x13, #3
	cbz x14, 246f
248:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 248b
	b 247f
246:
247:
	lsr x14, x13, #2
	cbz x14, 249f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 250f
249:
250:
	cbz x13, 251f
253:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 253b
	b 252f
251:
252:
	b 245f
244:
254:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 254b
245:
	b 243f
242:
243:
	cbz x25, 255f
	movz x3, #1, lsl #0
	b 256f
255:
	movz x3, #0, lsl #0
256:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	movz x9, #15, lsl #0
	and x25, x27, x9
	add x23, x28, #0
	add x24, x26, #0
	cbz x25, 257f
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 259f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 261f
	add x10, x9, #0
	b 262f
261:
	add x10, x24, #0
262:
	b 260f
259:
	add x10, x9, #0
260:
	b 258f
257:
	movz x10, #0, lsl #0
258:
	add x11, x20, x25
	add x11, x11, #64
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 263f
265:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 265b
	b 264f
263:
264:
	add x23, x23, x10
	sub x24, x24, x10
	lsr x4, x24, #4
	add x3, x23, #0
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	lsl x9, x4, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_aes_ctr32_aes}
	cbz x24, 266f
	movz x4, #1, lsl #0
	movz x9, #0, lsl #0
	str x9, [x20, #64]
	str x9, [x20, #72]
	b 267f
266:
	movz x4, #0, lsl #0
267:
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	add x3, x20, #64
	bl {vg_aes_ctr32_aes}
	add x11, x20, #64
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 268f
	lsr x14, x13, #2
	cbz x14, 270f
	lsr x14, x13, #3
	cbz x14, 272f
274:
	ldr x14, [x12, #0]
	ldr x15, [x11, #0]
	eor x14, x14, x15
	str x14, [x12, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 274b
	b 273f
272:
273:
	lsr x14, x13, #2
	cbz x14, 275f
	ldr w14, [x12, #0]
	ldr w15, [x11, #0]
	eor w14, w14, w15
	str w14, [x12, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 276f
275:
276:
	cbz x13, 277f
279:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 279b
	b 278f
277:
278:
	b 271f
270:
280:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 280b
271:
	b 269f
268:
269:
	add x23, x28, #0
	add x24, x26, #0
	cbz x26, 281f
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 283f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 285f
	add x10, x9, #0
	b 286f
285:
	add x10, x24, #0
286:
	b 284f
283:
	add x10, x9, #0
284:
	add x11, x20, x25
	add x11, x11, #32
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 287f
289:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 289b
	b 288f
287:
288:
	add x23, x23, x10
	sub x24, x24, x10
	add x9, x25, x10
	sub x9, x9, #16
	cbz x9, 290f
	movz x3, #0, lsl #0
	b 291f
290:
	movz x3, #1, lsl #0
291:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x20, #32
	bl {vg_ghash_aes}
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_ghash_aes}
	add x11, x20, #32
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 292f
	lsr x14, x13, #2
	cbz x14, 294f
	lsr x14, x13, #3
	cbz x14, 296f
298:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 298b
	b 297f
296:
297:
	lsr x14, x13, #2
	cbz x14, 299f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2100f
299:
2100:
	cbz x13, 2101f
2103:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2103b
	b 2102f
2101:
2102:
	b 295f
294:
2104:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2104b
295:
	b 293f
292:
293:
	b 282f
281:
282:
	ldr x26, [x19, #224]
	ldr x27, [x19, #240]
	ldr x28, [x19, #248]
	cbz x27, 2105f
	movz x9, #15, lsl #0
	and x25, x27, x9
	b 2106f
2105:
	movz x9, #15, lsl #0
	and x25, x26, x9
2106:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 2107f
	lsr x14, x13, #2
	cbz x14, 2109f
	lsr x14, x13, #3
	cbz x14, 2111f
2113:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2113b
	b 2112f
2111:
2112:
	lsr x14, x13, #2
	cbz x14, 2114f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2115f
2114:
2115:
	cbz x13, 2116f
2118:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2118b
	b 2117f
2116:
2117:
	b 2110f
2109:
2119:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2119b
2110:
	b 2108f
2107:
2108:
	cbz x25, 2120f
	movz x3, #1, lsl #0
	b 2121f
2120:
	movz x3, #0, lsl #0
2121:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x27, #3
	rev x9, x9
	str x9, [x19, #104]
	movz x3, #1, lsl #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	ldr x9, [x20, #16]
	str x9, [x19, #0]
	ldr x9, [x20, #24]
	str x9, [x19, #8]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #0
	add x3, x19, #0
	movz x4, #1, lsl #0
	add x5, x19, #512
	bl {vg_aes_ctr32_aes}
	ldr x9, [x19, #0]
	str x9, [x28, #0]
	ldr x9, [x19, #8]
	str x9, [x28, #8]
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
	b 27f
26:
	ldr w9, [x23, #0]
	ldr w10, [x23, #4]
	ldr w11, [x23, #8]
	movz w12, #256, lsl #16
	str w9, [x20, #0]
	str w10, [x20, #4]
	str w11, [x20, #8]
	str w12, [x20, #12]
	add x25, x5, #0
	add x27, x4, #0
	add x23, x6, #0
	add x26, x7, #0
	ldr w9, [x20, #0]
	ldr w10, [x20, #4]
	ldr w11, [x20, #8]
	ldr w12, [x20, #12]
	rev w12, w12
	add w12, w12, #1
	rev w12, w12
	str w9, [x20, #48]
	str w10, [x20, #52]
	str w11, [x20, #56]
	str w12, [x20, #60]
	movz x9, #0, lsl #0
	str x9, [x20, #16]
	str x9, [x20, #24]
	add x0, x21, #240
	ldr q6, [x0, #0]
	rev64 v6.16b, v6.16b
	movz x5, #49664, lsl #48
	dup v1.2d, x5
	movz x6, #3, lsl #0
	movz x7, #17920, lsl #48
	mov v17.d[0], x6
	mov v17.d[1], x7
	mov v25.d[0], x7
	mov v25.d[1], x6
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	pmull v7.1q, v6.1d, v25.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v6.2d, v25.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v6.1d, v17.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v6.2d, v17.2d
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v3.1d, v1.1d
	ext v3.16b, v3.16b, v3.16b, #8
	eor v4.16b, v4.16b, v3.16b
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v4.1d, v1.1d
	ext v5.16b, v5.16b, v5.16b, #8
	eor v5.16b, v5.16b, v4.16b
	ext v7.16b, v7.16b, v7.16b, #8
	eor v24.16b, v5.16b, v7.16b
	ext v16.16b, v24.16b, v24.16b, #8
	str q16, [x19, #288]
	str q24, [x19, #304]
	movi v0.2d, #0
	add x13, x25, #0
	add x12, x27, #0
	cbz x13, 2122f
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	cbz x13, 2124f
	lsr x14, x13, #2
	cbz x14, 2126f
	lsr x14, x13, #3
	cbz x14, 2128f
2130:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2130b
	b 2129f
2128:
2129:
	lsr x14, x13, #2
	cbz x14, 2131f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2132f
2131:
2132:
	cbz x13, 2133f
2135:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2135b
	b 2134f
2133:
2134:
	b 2127f
2126:
2136:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2136b
2127:
	b 2125f
2124:
2125:
	ldr q6, [x19, #96]
	rev64 v6.16b, v6.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	pmull v7.1q, v6.1d, v24.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v6.2d, v24.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v6.1d, v16.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v6.2d, v16.2d
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v3.1d, v1.1d
	ext v3.16b, v3.16b, v3.16b, #8
	eor v4.16b, v4.16b, v3.16b
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v4.1d, v1.1d
	ext v5.16b, v5.16b, v5.16b, #8
	eor v5.16b, v5.16b, v4.16b
	ext v7.16b, v7.16b, v7.16b, #8
	eor v0.16b, v5.16b, v7.16b
	b 2123f
2122:
2123:
	rev64 v0.16b, v0.16b
	str q0, [x20, #16]
	add x27, x23, #0
	add x24, x26, #0
	movz x25, #0, lsl #0
	lsr x4, x24, #4
	add x3, x23, #0
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	lsl x9, x4, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_aes_ctr32_aes}
	cbz x24, 2137f
	movz x4, #1, lsl #0
	movi v0.2d, #0
	str q0, [x20, #64]
	b 2138f
2137:
	movz x4, #0, lsl #0
2138:
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	add x3, x20, #64
	bl {vg_aes_ctr32_aes}
	cbz x24, 2139f
	lsr x9, x26, #4
	cbz x9, 2141f
	movz x9, #16, lsl #0
	sub x9, x9, x24
	dup v1.16b, w9
	adrp x10, {VG_GCM_TAIL_IDX}
	add x10, x10, {VG_GCM_TAIL_IDX}
	ldr q0, [x10, #0]
	sub v0.16b, v0.16b, v1.16b
	ldr q2, [x20, #64]
	tbl v2.16b, {v2.16b}, v0.16b
	sub x10, x23, x9
	ldr q3, [x10, #0]
	eor v3.16b, v3.16b, v2.16b
	str q3, [x10, #0]
	b 2142f
2141:
	add x11, x20, #64
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 2143f
	lsr x14, x13, #2
	cbz x14, 2145f
	lsr x14, x13, #3
	cbz x14, 2147f
2149:
	ldr x14, [x12, #0]
	ldr x15, [x11, #0]
	eor x14, x14, x15
	str x14, [x12, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2149b
	b 2148f
2147:
2148:
	lsr x14, x13, #2
	cbz x14, 2150f
	ldr w14, [x12, #0]
	ldr w15, [x11, #0]
	eor w14, w14, w15
	str w14, [x12, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2151f
2150:
2151:
	cbz x13, 2152f
2154:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2154b
	b 2153f
2152:
2153:
	b 2146f
2145:
2155:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2155b
2146:
	b 2144f
2143:
2144:
2142:
	b 2140f
2139:
2140:
	add x23, x27, #0
	add x24, x26, #0
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_ghash_aes}
	ldr q16, [x19, #288]
	ldr q24, [x19, #304]
	movz x5, #49664, lsl #48
	dup v1.2d, x5
	ldr q0, [x20, #16]
	rev64 v0.16b, v0.16b
	add x13, x24, #0
	add x12, x23, #0
	cbz x13, 2156f
	lsr x9, x26, #4
	cbz x9, 2158f
	movz x9, #16, lsl #0
	sub x9, x9, x13
	dup v6.16b, w9
	adrp x11, {VG_GCM_TAIL_IDX}
	add x11, x11, {VG_GCM_TAIL_IDX}
	ldr q7, [x11, #16]
	add v7.16b, v7.16b, v6.16b
	sub x11, x12, x9
	ldr q6, [x11, #0]
	tbl v6.16b, {v6.16b}, v7.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	pmull v7.1q, v6.1d, v24.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v6.2d, v24.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v6.1d, v16.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v6.2d, v16.2d
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v3.1d, v1.1d
	ext v3.16b, v3.16b, v3.16b, #8
	eor v4.16b, v4.16b, v3.16b
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v4.1d, v1.1d
	ext v5.16b, v5.16b, v5.16b, #8
	eor v5.16b, v5.16b, v4.16b
	ext v7.16b, v7.16b, v7.16b, #8
	eor v0.16b, v5.16b, v7.16b
	b 2159f
2158:
	cbz x13, 2160f
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	cbz x13, 2162f
	lsr x14, x13, #2
	cbz x14, 2164f
	lsr x14, x13, #3
	cbz x14, 2166f
2168:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2168b
	b 2167f
2166:
2167:
	lsr x14, x13, #2
	cbz x14, 2169f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2170f
2169:
2170:
	cbz x13, 2171f
2173:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2173b
	b 2172f
2171:
2172:
	b 2165f
2164:
2174:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2174b
2165:
	b 2163f
2162:
2163:
	ldr q6, [x19, #96]
	rev64 v6.16b, v6.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	pmull v7.1q, v6.1d, v24.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v6.2d, v24.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v6.1d, v16.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v6.2d, v16.2d
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v3.1d, v1.1d
	ext v3.16b, v3.16b, v3.16b, #8
	eor v4.16b, v4.16b, v3.16b
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v4.1d, v1.1d
	ext v5.16b, v5.16b, v5.16b, #8
	eor v5.16b, v5.16b, v4.16b
	ext v7.16b, v7.16b, v7.16b, #8
	eor v0.16b, v5.16b, v7.16b
	b 2161f
2160:
2161:
2159:
	b 2157f
2156:
2157:
	ldr x10, [x19, #224]
	lsl x9, x10, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #104]
	ldr q6, [x19, #96]
	rev64 v6.16b, v6.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	pmull v7.1q, v6.1d, v24.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v6.2d, v24.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v6.1d, v16.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v6.2d, v16.2d
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v3.1d, v1.1d
	ext v3.16b, v3.16b, v3.16b, #8
	eor v4.16b, v4.16b, v3.16b
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v4.1d, v1.1d
	ext v5.16b, v5.16b, v5.16b, #8
	eor v5.16b, v5.16b, v4.16b
	ext v7.16b, v7.16b, v7.16b, #8
	eor v0.16b, v5.16b, v7.16b
	rev64 v0.16b, v0.16b
	str q0, [x20, #16]
	ldr x9, [x20, #16]
	str x9, [x19, #0]
	ldr x9, [x20, #24]
	str x9, [x19, #8]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #0
	add x3, x19, #0
	movz x4, #1, lsl #0
	add x5, x19, #512
	bl {vg_aes_ctr32_aes}
	ldr x9, [x19, #0]
	str x9, [x28, #0]
	ldr x9, [x19, #8]
	str x9, [x28, #8]
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
27:
	add sp, sp, #784
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	movz x0, #0, lsl #0
	sub sp, sp, #784
	movi v31.2d, #0
	add x9, sp, #0
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	str q31, [x9, #64]
	str q31, [x9, #80]
	str q31, [x9, #96]
	str q31, [x9, #112]
	str q31, [x9, #128]
	str q31, [x9, #144]
	str q31, [x9, #160]
	str q31, [x9, #176]
	str q31, [x9, #192]
	str q31, [x9, #208]
	str q31, [x9, #224]
	str q31, [x9, #240]
	str q31, [x9, #256]
	str q31, [x9, #272]
	str q31, [x9, #288]
	str q31, [x9, #304]
	str q31, [x9, #320]
	str q31, [x9, #336]
	str q31, [x9, #352]
	str q31, [x9, #368]
	str q31, [x9, #384]
	str q31, [x9, #400]
	str q31, [x9, #416]
	str q31, [x9, #432]
	str q31, [x9, #448]
	str q31, [x9, #464]
	str q31, [x9, #480]
	str q31, [x9, #496]
	str q31, [x9, #512]
	str q31, [x9, #528]
	str q31, [x9, #544]
	str q31, [x9, #560]
	str q31, [x9, #576]
	str q31, [x9, #592]
	str q31, [x9, #608]
	str q31, [x9, #624]
	str q31, [x9, #640]
	str q31, [x9, #656]
	str q31, [x9, #672]
	str q31, [x9, #688]
	str q31, [x9, #704]
	str q31, [x9, #720]
	str q31, [x9, #736]
	str q31, [x9, #752]
	str q31, [x9, #768]
	add sp, sp, #784
	ret
	.p2align 6
