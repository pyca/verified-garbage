// The functions of `src/internal/vg_aes_gcm_stream_encrypt_core.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_gcm_stream_encrypt_core:
	sub sp, sp, #2560
	add x7, sp, #0
	str x20, [x7, #136]
	str x21, [x7, #144]
	str x22, [x7, #152]
	str x23, [x7, #160]
	str x24, [x7, #168]
	str x25, [x7, #176]
	str x26, [x7, #184]
	str x27, [x7, #192]
	str x28, [x7, #200]
	str x30, [x7, #208]
	str x19, [x7, #128]
	add x19, x7, #0
	add x20, x2, #0
	add x21, x0, #0
	add x22, x1, #0
	add x26, x6, #0
	add x27, x4, #0
	add x28, x5, #0
	movz x9, #15, lsl #0
	and x25, x3, x9
	cbz x26, 20f
	cbz x27, 22f
	movz x25, #0, lsl #0
	b 23f
22:
23:
	b 21f
20:
	movz x25, #0, lsl #0
21:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 24f
	lsr x14, x13, #2
	cbz x14, 26f
	lsr x14, x13, #3
	cbz x14, 28f
210:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 210b
	b 29f
28:
29:
	lsr x14, x13, #2
	cbz x14, 211f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 212f
211:
212:
	cbz x13, 213f
215:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 215b
	b 214f
213:
214:
	b 27f
26:
216:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 216b
27:
	b 25f
24:
25:
	cbz x25, 217f
	movz x3, #1, lsl #0
	b 218f
217:
	movz x3, #0, lsl #0
218:
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
	cbz x25, 219f
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 221f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 223f
	add x10, x9, #0
	b 224f
223:
	add x10, x24, #0
224:
	b 222f
221:
	add x10, x9, #0
222:
	b 220f
219:
	movz x10, #0, lsl #0
220:
	add x11, x20, x25
	add x11, x11, #64
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 225f
227:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 227b
	b 226f
225:
226:
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
	umov x16, v9.d[0]
	blr x16
	cbz x24, 228f
	movz x4, #1, lsl #0
	movz x9, #0, lsl #0
	str x9, [x20, #64]
	str x9, [x20, #72]
	b 229f
228:
	movz x4, #0, lsl #0
229:
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	add x3, x20, #64
	umov x16, v9.d[0]
	blr x16
	add x11, x20, #64
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 230f
	lsr x14, x13, #2
	cbz x14, 232f
	lsr x14, x13, #3
	cbz x14, 234f
236:
	ldr x14, [x12, #0]
	ldr x15, [x11, #0]
	eor x14, x14, x15
	str x14, [x12, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 236b
	b 235f
234:
235:
	lsr x14, x13, #2
	cbz x14, 237f
	ldr w14, [x12, #0]
	ldr w15, [x11, #0]
	eor w14, w14, w15
	str w14, [x12, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 238f
237:
238:
	cbz x13, 239f
241:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 241b
	b 240f
239:
240:
	b 233f
232:
242:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 242b
233:
	b 231f
230:
231:
	add x23, x28, #0
	add x24, x26, #0
	cbz x26, 243f
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 245f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 247f
	add x10, x9, #0
	b 248f
247:
	add x10, x24, #0
248:
	b 246f
245:
	add x10, x9, #0
246:
	add x11, x20, x25
	add x11, x11, #32
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 249f
251:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 251b
	b 250f
249:
250:
	add x23, x23, x10
	sub x24, x24, x10
	add x9, x25, x10
	sub x9, x9, #16
	cbz x9, 252f
	movz x3, #0, lsl #0
	b 253f
252:
	movz x3, #1, lsl #0
253:
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
	cbz x13, 254f
	lsr x14, x13, #2
	cbz x14, 256f
	lsr x14, x13, #3
	cbz x14, 258f
260:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 260b
	b 259f
258:
259:
	lsr x14, x13, #2
	cbz x14, 261f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 262f
261:
262:
	cbz x13, 263f
265:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 265b
	b 264f
263:
264:
	b 257f
256:
266:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 266b
257:
	b 255f
254:
255:
	b 244f
243:
244:
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
	add sp, sp, #2560
	ret
	.p2align 6
