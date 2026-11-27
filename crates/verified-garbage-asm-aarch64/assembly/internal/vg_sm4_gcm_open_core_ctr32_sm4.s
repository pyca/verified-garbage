// The functions of `src/internal/vg_sm4_gcm_open_core_ctr32_sm4.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_gcm_open_core_ctr32_sm4:
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
	str x3, [x19, #216]
	str x4, [x19, #224]
	str x5, [x19, #232]
	str x6, [x19, #240]
	add x23, x1, #0
	add x24, x2, #0
	add x26, x2, #0
	movz x27, #0, lsl #0
	ldr x10, [sp, #0]
	str x10, [x19, #248]
	add x28, x10, #0
	add x12, x7, #0
	sub x10, x28, #4
	movz x9, #13, lsl #0
	subs x10, x10, x9
	movz x9, #0, lsl #0
	movz x10, #1, lsl #0
	csel x9, x9, x10, hs
	cbz x9, 20f
	lsr x13, x28, #4
	cbz x13, 22f
	ldr q0, [x12, #0]
	str q0, [x19, #0]
	b 23f
22:
	add x11, x19, #0
	add x13, x28, #0
	cbz x13, 24f
26:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 26b
	b 25f
24:
25:
23:
	sub x9, x24, #12
	cbz x9, 27f
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
	cbz x13, 29f
	lsr x14, x13, #2
	cbz x14, 211f
	lsr x14, x13, #3
	cbz x14, 213f
215:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 215b
	b 214f
213:
214:
	lsr x14, x13, #2
	cbz x14, 216f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 217f
216:
217:
	cbz x13, 218f
220:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 220b
	b 219f
218:
219:
	b 212f
211:
221:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 221b
212:
	b 210f
29:
210:
	cbz x25, 222f
	movz x3, #1, lsl #0
	b 223f
222:
	movz x3, #0, lsl #0
223:
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
	b 28f
27:
	ldr w9, [x23, #0]
	ldr w10, [x23, #4]
	ldr w11, [x23, #8]
	movz w12, #256, lsl #16
	str w9, [x20, #0]
	str w10, [x20, #4]
	str w11, [x20, #8]
	str w12, [x20, #12]
28:
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
	cbz x13, 224f
	lsr x14, x13, #2
	cbz x14, 226f
	lsr x14, x13, #3
	cbz x14, 228f
230:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 230b
	b 229f
228:
229:
	lsr x14, x13, #2
	cbz x14, 231f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 232f
231:
232:
	cbz x13, 233f
235:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 235b
	b 234f
233:
234:
	b 227f
226:
236:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 236b
227:
	b 225f
224:
225:
	ldr x9, [x19, #224]
	movz x10, #15, lsl #0
	and x25, x9, x10
	ldr x26, [x19, #240]
	movz x27, #0, lsl #0
	ldr x28, [x19, #232]
	cbz x26, 237f
	cbz x27, 239f
	movz x25, #0, lsl #0
	b 240f
239:
240:
	b 238f
237:
	movz x25, #0, lsl #0
238:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 241f
	lsr x14, x13, #2
	cbz x14, 243f
	lsr x14, x13, #3
	cbz x14, 245f
247:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 247b
	b 246f
245:
246:
	lsr x14, x13, #2
	cbz x14, 248f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 249f
248:
249:
	cbz x13, 250f
252:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 252b
	b 251f
250:
251:
	b 244f
243:
253:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 253b
244:
	b 242f
241:
242:
	cbz x25, 254f
	movz x3, #1, lsl #0
	b 255f
254:
	movz x3, #0, lsl #0
255:
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
	cbz x26, 256f
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 258f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 260f
	add x10, x9, #0
	b 261f
260:
	add x10, x24, #0
261:
	b 259f
258:
	add x10, x9, #0
259:
	add x11, x20, x25
	add x11, x11, #32
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 262f
264:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 264b
	b 263f
262:
263:
	add x23, x23, x10
	sub x24, x24, x10
	add x9, x25, x10
	sub x9, x9, #16
	cbz x9, 265f
	movz x3, #0, lsl #0
	b 266f
265:
	movz x3, #1, lsl #0
266:
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
	cbz x13, 267f
	lsr x14, x13, #2
	cbz x14, 269f
	lsr x14, x13, #3
	cbz x14, 271f
273:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 273b
	b 272f
271:
272:
	lsr x14, x13, #2
	cbz x14, 274f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 275f
274:
275:
	cbz x13, 276f
278:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 278b
	b 277f
276:
277:
	b 270f
269:
279:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 279b
270:
	b 268f
267:
268:
	b 257f
256:
257:
	ldr x26, [x19, #224]
	ldr x27, [x19, #240]
	cbz x27, 280f
	movz x9, #15, lsl #0
	and x25, x27, x9
	b 281f
280:
	movz x9, #15, lsl #0
	and x25, x26, x9
281:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 282f
	lsr x14, x13, #2
	cbz x14, 284f
	lsr x14, x13, #3
	cbz x14, 286f
288:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 288b
	b 287f
286:
287:
	lsr x14, x13, #2
	cbz x14, 289f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 290f
289:
290:
	cbz x13, 291f
293:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 293b
	b 292f
291:
292:
	b 285f
284:
294:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 294b
285:
	b 283f
282:
283:
	cbz x25, 295f
	movz x3, #1, lsl #0
	b 296f
295:
	movz x3, #0, lsl #0
296:
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
	str x9, [x19, #112]
	ldr x9, [x20, #24]
	str x9, [x19, #120]
	add x0, x21, #0
	add x1, x20, #0
	add x2, x19, #112
	movz x3, #1, lsl #0
	bl {vg_sm4_ctr32_sm4}
	ldr x28, [x19, #248]
	lsr x9, x28, #4
	cbz x9, 297f
	ldr x9, [x19, #112]
	ldr x10, [x19, #0]
	eor x9, x9, x10
	ldr x10, [x19, #120]
	ldr x11, [x19, #8]
	eor x10, x10, x11
	orr x9, x9, x10
	movz x11, #0, lsl #0
	sub x12, x11, #1
	adds x9, x9, x12
	adcs x10, x11, x11
	b 298f
297:
	movz x9, #0, lsl #0
	str x9, [x19, #256]
	str x9, [x19, #264]
	str x9, [x19, #272]
	str x9, [x19, #280]
	add x11, x19, #272
	add x12, x19, #0
	add x13, x28, #0
	cbz x13, 299f
2101:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2101b
	b 2100f
299:
2100:
	add x11, x19, #256
	add x12, x19, #112
	add x13, x28, #0
	cbz x13, 2102f
2104:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2104b
	b 2103f
2102:
2103:
	ldr x9, [x19, #256]
	ldr x10, [x19, #272]
	eor x9, x9, x10
	ldr x10, [x19, #264]
	ldr x11, [x19, #280]
	eor x10, x10, x11
	orr x9, x9, x10
	movz x11, #0, lsl #0
	sub x12, x11, #1
	adds x9, x9, x12
	adcs x10, x11, x11
298:
	movz x27, #1, lsl #0
	sub x27, x27, x10
	cbz x27, 2105f
	ldr x23, [x19, #232]
	ldr x24, [x19, #240]
	movz x25, #0, lsl #0
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #0
	add x1, x20, #48
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_sm4_ctr32_sm4}
	cbz x24, 2107f
	movz x3, #1, lsl #0
	movz x9, #0, lsl #0
	str x9, [x20, #64]
	str x9, [x20, #72]
	b 2108f
2107:
	movz x3, #0, lsl #0
2108:
	add x0, x21, #0
	add x1, x20, #48
	add x2, x20, #64
	bl {vg_sm4_ctr32_sm4}
	add x11, x20, #64
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 2109f
	lsr x14, x13, #2
	cbz x14, 2111f
	lsr x14, x13, #3
	cbz x14, 2113f
2115:
	ldr x14, [x12, #0]
	ldr x15, [x11, #0]
	eor x14, x14, x15
	str x14, [x12, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2115b
	b 2114f
2113:
2114:
	lsr x14, x13, #2
	cbz x14, 2116f
	ldr w14, [x12, #0]
	ldr w15, [x11, #0]
	eor w14, w14, w15
	str w14, [x12, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2117f
2116:
2117:
	cbz x13, 2118f
2120:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2120b
	b 2119f
2118:
2119:
	b 2112f
2111:
2121:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2121b
2112:
	b 2110f
2109:
2110:
	b 2106f
2105:
2106:
	add x0, x27, #0
	b 21f
20:
	movz x0, #0, lsl #0
21:
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
