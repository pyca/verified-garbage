// The functions of `src/internal/vg_sm4_gcm_seal_core.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_gcm_seal_core:
	sub sp, sp, #784
	add x16, sp, #0
	add x17, sp, #16
	str x17, [x16, #0]
	ldr x9, [sp, #0]
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
	str x3, [x19, #216]
	str x4, [x19, #224]
	str x5, [x19, #232]
	str x6, [x19, #240]
	add x23, x1, #0
	add x24, x2, #0
	add x26, x2, #0
	movz x27, #0, lsl #0
	str x7, [x19, #248]
	add x28, x7, #0
	sub x9, x24, #12
	cbz x9, 20f
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
	umov x16, v8.d[0]
	blr x16
	add x12, x23, #0
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 22f
	lsr x14, x13, #2
	cbz x14, 24f
	lsr x14, x13, #3
	cbz x14, 26f
28:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 28b
	b 27f
26:
27:
	lsr x14, x13, #2
	cbz x14, 29f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 210f
29:
210:
	cbz x13, 211f
213:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 213b
	b 212f
211:
212:
	b 25f
24:
214:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 214b
25:
	b 23f
22:
23:
	cbz x25, 215f
	movz x3, #1, lsl #0
	b 216f
215:
	movz x3, #0, lsl #0
216:
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	add x2, x19, #96
	umov x16, v8.d[0]
	blr x16
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
	umov x16, v8.d[0]
	blr x16
	b 21f
20:
	ldr w9, [x23, #0]
	ldr w10, [x23, #4]
	ldr w11, [x23, #8]
	movz w12, #256, lsl #16
	str w9, [x20, #0]
	str w10, [x20, #4]
	str w11, [x20, #8]
	str w12, [x20, #12]
21:
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
	umov x16, v8.d[0]
	blr x16
	add x11, x20, #32
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 217f
	lsr x14, x13, #2
	cbz x14, 219f
	lsr x14, x13, #3
	cbz x14, 221f
223:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 223b
	b 222f
221:
222:
	lsr x14, x13, #2
	cbz x14, 224f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 225f
224:
225:
	cbz x13, 226f
228:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 228b
	b 227f
226:
227:
	b 220f
219:
229:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 229b
220:
	b 218f
217:
218:
	ldr x9, [x19, #224]
	movz x10, #15, lsl #0
	and x25, x9, x10
	ldr x26, [x19, #240]
	movz x27, #0, lsl #0
	ldr x28, [x19, #232]
	cbz x26, 230f
	cbz x27, 232f
	movz x25, #0, lsl #0
	b 233f
232:
233:
	b 231f
230:
	movz x25, #0, lsl #0
231:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 234f
	lsr x14, x13, #2
	cbz x14, 236f
	lsr x14, x13, #3
	cbz x14, 238f
240:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 240b
	b 239f
238:
239:
	lsr x14, x13, #2
	cbz x14, 241f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 242f
241:
242:
	cbz x13, 243f
245:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 245b
	b 244f
243:
244:
	b 237f
236:
246:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 246b
237:
	b 235f
234:
235:
	cbz x25, 247f
	movz x3, #1, lsl #0
	b 248f
247:
	movz x3, #0, lsl #0
248:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	umov x16, v8.d[0]
	blr x16
	movz x9, #15, lsl #0
	and x25, x27, x9
	add x23, x28, #0
	add x24, x26, #0
	cbz x25, 249f
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 251f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 253f
	add x10, x9, #0
	b 254f
253:
	add x10, x24, #0
254:
	b 252f
251:
	add x10, x9, #0
252:
	b 250f
249:
	movz x10, #0, lsl #0
250:
	add x11, x20, x25
	add x11, x11, #64
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 255f
257:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 257b
	b 256f
255:
256:
	add x23, x23, x10
	sub x24, x24, x10
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #0
	add x1, x20, #48
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_sm4_ctr32}
	cbz x24, 258f
	movz x3, #1, lsl #0
	movz x9, #0, lsl #0
	str x9, [x20, #64]
	str x9, [x20, #72]
	b 259f
258:
	movz x3, #0, lsl #0
259:
	add x0, x21, #0
	add x1, x20, #48
	add x2, x20, #64
	bl {vg_sm4_ctr32}
	add x11, x20, #64
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 260f
	lsr x14, x13, #2
	cbz x14, 262f
	lsr x14, x13, #3
	cbz x14, 264f
266:
	ldr x14, [x12, #0]
	ldr x15, [x11, #0]
	eor x14, x14, x15
	str x14, [x12, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 266b
	b 265f
264:
265:
	lsr x14, x13, #2
	cbz x14, 267f
	ldr w14, [x12, #0]
	ldr w15, [x11, #0]
	eor w14, w14, w15
	str w14, [x12, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 268f
267:
268:
	cbz x13, 269f
271:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 271b
	b 270f
269:
270:
	b 263f
262:
272:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 272b
263:
	b 261f
260:
261:
	add x23, x28, #0
	add x24, x26, #0
	cbz x26, 273f
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 275f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 277f
	add x10, x9, #0
	b 278f
277:
	add x10, x24, #0
278:
	b 276f
275:
	add x10, x9, #0
276:
	add x11, x20, x25
	add x11, x11, #32
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 279f
281:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 281b
	b 280f
279:
280:
	add x23, x23, x10
	sub x24, x24, x10
	add x9, x25, x10
	sub x9, x9, #16
	cbz x9, 282f
	movz x3, #0, lsl #0
	b 283f
282:
	movz x3, #1, lsl #0
283:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x20, #32
	umov x16, v8.d[0]
	blr x16
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	umov x16, v8.d[0]
	blr x16
	add x11, x20, #32
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 284f
	lsr x14, x13, #2
	cbz x14, 286f
	lsr x14, x13, #3
	cbz x14, 288f
290:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 290b
	b 289f
288:
289:
	lsr x14, x13, #2
	cbz x14, 291f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 292f
291:
292:
	cbz x13, 293f
295:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 295b
	b 294f
293:
294:
	b 287f
286:
296:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 296b
287:
	b 285f
284:
285:
	b 274f
273:
274:
	ldr x26, [x19, #224]
	ldr x27, [x19, #240]
	ldr x28, [x19, #248]
	cbz x27, 297f
	movz x9, #15, lsl #0
	and x25, x27, x9
	b 298f
297:
	movz x9, #15, lsl #0
	and x25, x26, x9
298:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 299f
	lsr x14, x13, #2
	cbz x14, 2101f
	lsr x14, x13, #3
	cbz x14, 2103f
2105:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2105b
	b 2104f
2103:
2104:
	lsr x14, x13, #2
	cbz x14, 2106f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2107f
2106:
2107:
	cbz x13, 2108f
2110:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2110b
	b 2109f
2108:
2109:
	b 2102f
2101:
2111:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2111b
2102:
	b 2100f
299:
2100:
	cbz x25, 2112f
	movz x3, #1, lsl #0
	b 2113f
2112:
	movz x3, #0, lsl #0
2113:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	umov x16, v8.d[0]
	blr x16
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
	umov x16, v8.d[0]
	blr x16
	ldr x9, [x20, #16]
	str x9, [x19, #0]
	ldr x9, [x20, #24]
	str x9, [x19, #8]
	add x0, x21, #0
	add x1, x20, #0
	add x2, x19, #0
	movz x3, #1, lsl #0
	bl {vg_sm4_ctr32}
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
	add sp, sp, #784
	ret
	.p2align 6
