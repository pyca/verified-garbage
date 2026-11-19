// The functions of `src/rsa_pkcs1_sig.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pkcs1_sign_precomputed:
	sub sp, sp, #1152
	add x16, sp, #0
	str x19, [x16, #112]
	str x30, [x16, #120]
	add x19, x3, #0
	add x17, x0, #0
	add x8, sp, #128
	add x9, x3, #0
	add w10, w6, #0
	add x11, x7, #0
	ldr x12, [sp, #1152]
	sub w0, w10, #0
	cbz w0, 20f
	sub w0, w10, #1
	cbz w0, 22f
	sub w0, w10, #2
	cbz w0, 24f
	sub w0, w10, #3
	cbz w0, 26f
	sub w0, w10, #4
	cbz w0, 28f
	sub w0, w10, #5
	cbz w0, 210f
	sub w0, w10, #6
	cbz w0, 212f
	sub w0, w10, #7
	cbz w0, 214f
	sub w0, w10, #8
	cbz w0, 216f
	sub w0, w10, #9
	cbz w0, 218f
	sub w0, w10, #10
	cbz w0, 220f
	sub w0, w10, #11
	cbz w0, 222f
	movz x13, #2048, lsl #0
	movz x15, #0, lsl #0
	b 223f
222:
	movz x13, #83, lsl #0
	movz x15, #64, lsl #0
223:
	b 221f
220:
	movz x13, #67, lsl #0
	movz x15, #48, lsl #0
221:
	b 219f
218:
	movz x13, #51, lsl #0
	movz x15, #32, lsl #0
219:
	b 217f
216:
	movz x13, #47, lsl #0
	movz x15, #28, lsl #0
217:
	b 215f
214:
	movz x13, #51, lsl #0
	movz x15, #32, lsl #0
215:
	b 213f
212:
	movz x13, #47, lsl #0
	movz x15, #28, lsl #0
213:
	b 211f
210:
	movz x13, #83, lsl #0
	movz x15, #64, lsl #0
211:
	b 29f
28:
	movz x13, #67, lsl #0
	movz x15, #48, lsl #0
29:
	b 27f
26:
	movz x13, #51, lsl #0
	movz x15, #32, lsl #0
27:
	b 25f
24:
	movz x13, #47, lsl #0
	movz x15, #28, lsl #0
25:
	b 23f
22:
	movz x13, #35, lsl #0
	movz x15, #20, lsl #0
23:
	b 21f
20:
	movz x13, #34, lsl #0
	movz x15, #16, lsl #0
21:
	sub x0, x12, x15
	cbnz x0, 224f
	add x0, x13, #11
	sub x0, x9, x0
	lsr x0, x0, #63
	cbnz x0, 226f
	add x14, x8, #0
	movz x15, #0, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #1, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	sub x13, x9, x13
	sub x13, x13, #3
	movz x15, #255, lsl #0
228:
	strb w15, [x14, #0]
	add x14, x14, #1
	sub x13, x13, #1
	cbnz x13, 228b
	movz x15, #0, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	sub w0, w10, #0
	cbz w0, 229f
	sub w0, w10, #1
	cbz w0, 231f
	sub w0, w10, #2
	cbz w0, 233f
	sub w0, w10, #3
	cbz w0, 235f
	sub w0, w10, #4
	cbz w0, 237f
	sub w0, w10, #5
	cbz w0, 239f
	sub w0, w10, #6
	cbz w0, 241f
	sub w0, w10, #7
	cbz w0, 243f
	sub w0, w10, #8
	cbz w0, 245f
	sub w0, w10, #9
	cbz w0, 247f
	sub w0, w10, #10
	cbz w0, 249f
	sub w0, w10, #11
	cbz w0, 251f
	b 252f
251:
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #81, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #13, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #6, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #9, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #96, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #134, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #72, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #1, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #101, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #3, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #2, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #10, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #0, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #64, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
252:
	b 250f
249:
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #65, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #13, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #6, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #9, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #96, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #134, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #72, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #1, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #101, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #3, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #2, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #9, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #0, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
250:
	b 248f
247:
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #49, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #13, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #6, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #9, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #96, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #134, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #72, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #1, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #101, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #3, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #2, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #8, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #0, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #32, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
248:
	b 246f
245:
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #45, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #13, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #6, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #9, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #96, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #134, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #72, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #1, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #101, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #3, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #2, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #7, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #0, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #28, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
246:
	b 244f
243:
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #49, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #13, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #6, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #9, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #96, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #134, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #72, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #1, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #101, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #3, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #2, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #6, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #0, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #32, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
244:
	b 242f
241:
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #45, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #13, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #6, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #9, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #96, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #134, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #72, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #1, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #101, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #3, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #2, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #0, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #28, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
242:
	b 240f
239:
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #81, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #13, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #6, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #9, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #96, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #134, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #72, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #1, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #101, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #3, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #2, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #3, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #0, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #64, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
240:
	b 238f
237:
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #65, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #13, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #6, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #9, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #96, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #134, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #72, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #1, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #101, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #3, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #2, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #2, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #0, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
238:
	b 236f
235:
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #49, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #13, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #6, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #9, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #96, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #134, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #72, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #1, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #101, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #3, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #2, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #1, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #0, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #32, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
236:
	b 234f
233:
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #45, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #13, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #6, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #9, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #96, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #134, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #72, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #1, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #101, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #3, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #2, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #0, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #28, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
234:
	b 232f
231:
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #33, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #9, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #6, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #43, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #14, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #3, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #2, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #26, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #0, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #20, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
232:
	b 230f
229:
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #32, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #12, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #6, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #8, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #42, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #134, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #72, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #134, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #247, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #13, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #2, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #0, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #16, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
230:
253:
	ldrb w15, [x11, #0]
	strb w15, [x14, #0]
	add x11, x11, #1
	add x14, x14, #1
	sub x12, x12, #1
	cbnz x12, 253b
	movz x0, #1, lsl #0
	b 227f
226:
	movz x0, #0, lsl #0
227:
	b 225f
224:
	movz x0, #0, lsl #0
225:
	cbz x0, 254f
	ldr x15, [sp, #1160]
	str x15, [x16, #0]
	ldr x15, [sp, #1168]
	str x15, [x16, #8]
	ldr x15, [sp, #1176]
	str x15, [x16, #16]
	ldr x15, [sp, #1184]
	str x15, [x16, #24]
	ldr x15, [sp, #1192]
	str x15, [x16, #32]
	ldr x15, [sp, #1200]
	str x15, [x16, #40]
	ldr x15, [sp, #1208]
	str x15, [x16, #48]
	ldr x15, [sp, #1216]
	str x15, [x16, #56]
	ldr x15, [sp, #1224]
	str x15, [x16, #64]
	ldr x15, [sp, #1232]
	str x15, [x16, #72]
	ldr x15, [sp, #1240]
	str x15, [x16, #80]
	ldr x15, [sp, #1248]
	str x15, [x16, #88]
	ldr x15, [sp, #1256]
	str x15, [x16, #96]
	ldr x15, [sp, #1264]
	str x15, [x16, #104]
	add x0, x17, #0
	add x6, x8, #0
	add x7, x19, #0
	bl {vg_rsa_private_checked_precomputed}
	add x14, sp, #128
	add x13, x19, #0
	movz x15, #0, lsl #0
256:
	strb w15, [x14, #0]
	add x14, x14, #1
	sub x13, x13, #1
	cbnz x13, 256b
	b 255f
254:
	add x14, x17, #0
	add x13, x19, #0
	movz x15, #0, lsl #0
257:
	strb w15, [x14, #0]
	add x14, x14, #1
	sub x13, x13, #1
	cbnz x13, 257b
	movz x0, #0, lsl #0
255:
	add x16, sp, #0
	ldr x19, [x16, #112]
	ldr x30, [x16, #120]
	add sp, sp, #1152
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
	add w0, w0, #0
	sub sp, sp, #320
	sub sp, sp, #4080
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
	str q31, [x9, #784]
	str q31, [x9, #800]
	str q31, [x9, #816]
	str q31, [x9, #832]
	str q31, [x9, #848]
	str q31, [x9, #864]
	str q31, [x9, #880]
	str q31, [x9, #896]
	str q31, [x9, #912]
	str q31, [x9, #928]
	str q31, [x9, #944]
	str q31, [x9, #960]
	str q31, [x9, #976]
	str q31, [x9, #992]
	str q31, [x9, #1008]
	str q31, [x9, #1024]
	str q31, [x9, #1040]
	str q31, [x9, #1056]
	str q31, [x9, #1072]
	str q31, [x9, #1088]
	str q31, [x9, #1104]
	str q31, [x9, #1120]
	str q31, [x9, #1136]
	str q31, [x9, #1152]
	str q31, [x9, #1168]
	str q31, [x9, #1184]
	str q31, [x9, #1200]
	str q31, [x9, #1216]
	str q31, [x9, #1232]
	str q31, [x9, #1248]
	str q31, [x9, #1264]
	str q31, [x9, #1280]
	str q31, [x9, #1296]
	str q31, [x9, #1312]
	str q31, [x9, #1328]
	str q31, [x9, #1344]
	str q31, [x9, #1360]
	str q31, [x9, #1376]
	str q31, [x9, #1392]
	str q31, [x9, #1408]
	str q31, [x9, #1424]
	str q31, [x9, #1440]
	str q31, [x9, #1456]
	str q31, [x9, #1472]
	str q31, [x9, #1488]
	str q31, [x9, #1504]
	str q31, [x9, #1520]
	str q31, [x9, #1536]
	str q31, [x9, #1552]
	str q31, [x9, #1568]
	str q31, [x9, #1584]
	str q31, [x9, #1600]
	str q31, [x9, #1616]
	str q31, [x9, #1632]
	str q31, [x9, #1648]
	str q31, [x9, #1664]
	str q31, [x9, #1680]
	str q31, [x9, #1696]
	str q31, [x9, #1712]
	str q31, [x9, #1728]
	str q31, [x9, #1744]
	str q31, [x9, #1760]
	str q31, [x9, #1776]
	str q31, [x9, #1792]
	str q31, [x9, #1808]
	str q31, [x9, #1824]
	str q31, [x9, #1840]
	str q31, [x9, #1856]
	str q31, [x9, #1872]
	str q31, [x9, #1888]
	str q31, [x9, #1904]
	str q31, [x9, #1920]
	str q31, [x9, #1936]
	str q31, [x9, #1952]
	str q31, [x9, #1968]
	str q31, [x9, #1984]
	str q31, [x9, #2000]
	str q31, [x9, #2016]
	str q31, [x9, #2032]
	str q31, [x9, #2048]
	str q31, [x9, #2064]
	str q31, [x9, #2080]
	str q31, [x9, #2096]
	str q31, [x9, #2112]
	str q31, [x9, #2128]
	str q31, [x9, #2144]
	str q31, [x9, #2160]
	str q31, [x9, #2176]
	str q31, [x9, #2192]
	str q31, [x9, #2208]
	str q31, [x9, #2224]
	str q31, [x9, #2240]
	str q31, [x9, #2256]
	str q31, [x9, #2272]
	str q31, [x9, #2288]
	str q31, [x9, #2304]
	str q31, [x9, #2320]
	str q31, [x9, #2336]
	str q31, [x9, #2352]
	str q31, [x9, #2368]
	str q31, [x9, #2384]
	str q31, [x9, #2400]
	str q31, [x9, #2416]
	str q31, [x9, #2432]
	str q31, [x9, #2448]
	str q31, [x9, #2464]
	str q31, [x9, #2480]
	str q31, [x9, #2496]
	str q31, [x9, #2512]
	str q31, [x9, #2528]
	str q31, [x9, #2544]
	str q31, [x9, #2560]
	str q31, [x9, #2576]
	str q31, [x9, #2592]
	str q31, [x9, #2608]
	str q31, [x9, #2624]
	str q31, [x9, #2640]
	str q31, [x9, #2656]
	str q31, [x9, #2672]
	str q31, [x9, #2688]
	str q31, [x9, #2704]
	str q31, [x9, #2720]
	str q31, [x9, #2736]
	str q31, [x9, #2752]
	str q31, [x9, #2768]
	str q31, [x9, #2784]
	str q31, [x9, #2800]
	str q31, [x9, #2816]
	str q31, [x9, #2832]
	str q31, [x9, #2848]
	str q31, [x9, #2864]
	str q31, [x9, #2880]
	str q31, [x9, #2896]
	str q31, [x9, #2912]
	str q31, [x9, #2928]
	str q31, [x9, #2944]
	str q31, [x9, #2960]
	str q31, [x9, #2976]
	str q31, [x9, #2992]
	str q31, [x9, #3008]
	str q31, [x9, #3024]
	str q31, [x9, #3040]
	str q31, [x9, #3056]
	str q31, [x9, #3072]
	str q31, [x9, #3088]
	str q31, [x9, #3104]
	str q31, [x9, #3120]
	str q31, [x9, #3136]
	str q31, [x9, #3152]
	str q31, [x9, #3168]
	str q31, [x9, #3184]
	str q31, [x9, #3200]
	str q31, [x9, #3216]
	str q31, [x9, #3232]
	str q31, [x9, #3248]
	str q31, [x9, #3264]
	str q31, [x9, #3280]
	str q31, [x9, #3296]
	str q31, [x9, #3312]
	str q31, [x9, #3328]
	str q31, [x9, #3344]
	str q31, [x9, #3360]
	str q31, [x9, #3376]
	str q31, [x9, #3392]
	str q31, [x9, #3408]
	str q31, [x9, #3424]
	str q31, [x9, #3440]
	str q31, [x9, #3456]
	str q31, [x9, #3472]
	str q31, [x9, #3488]
	str q31, [x9, #3504]
	str q31, [x9, #3520]
	str q31, [x9, #3536]
	str q31, [x9, #3552]
	str q31, [x9, #3568]
	str q31, [x9, #3584]
	str q31, [x9, #3600]
	str q31, [x9, #3616]
	str q31, [x9, #3632]
	str q31, [x9, #3648]
	str q31, [x9, #3664]
	str q31, [x9, #3680]
	str q31, [x9, #3696]
	str q31, [x9, #3712]
	str q31, [x9, #3728]
	str q31, [x9, #3744]
	str q31, [x9, #3760]
	str q31, [x9, #3776]
	str q31, [x9, #3792]
	str q31, [x9, #3808]
	str q31, [x9, #3824]
	str q31, [x9, #3840]
	str q31, [x9, #3856]
	str q31, [x9, #3872]
	str q31, [x9, #3888]
	str q31, [x9, #3904]
	str q31, [x9, #3920]
	str q31, [x9, #3936]
	str q31, [x9, #3952]
	str q31, [x9, #3968]
	str q31, [x9, #3984]
	str q31, [x9, #4000]
	str q31, [x9, #4016]
	str q31, [x9, #4032]
	str q31, [x9, #4048]
	str q31, [x9, #4064]
	str q31, [x9, #4080]
	str q31, [x9, #4096]
	str q31, [x9, #4112]
	str q31, [x9, #4128]
	str q31, [x9, #4144]
	str q31, [x9, #4160]
	str q31, [x9, #4176]
	str q31, [x9, #4192]
	str q31, [x9, #4208]
	str q31, [x9, #4224]
	str q31, [x9, #4240]
	str q31, [x9, #4256]
	str q31, [x9, #4272]
	str q31, [x9, #4288]
	str q31, [x9, #4304]
	str q31, [x9, #4320]
	str q31, [x9, #4336]
	str q31, [x9, #4352]
	str q31, [x9, #4368]
	str q31, [x9, #4384]
	add sp, sp, #4080
	add sp, sp, #320
	ret
	.p2align 6

vg_rsa_pkcs1_verify_precomputed:
	ldr x8, [sp, #0]
	sub x8, x8, x1
	cbnz x8, 20f
	sub sp, sp, #2128
	add x16, sp, #0
	str x19, [x16, #16]
	str x20, [x16, #24]
	str x21, [x16, #32]
	str x22, [x16, #40]
	str x30, [x16, #48]
	add x19, x1, #0
	add w20, w4, #0
	add x21, x5, #0
	add x22, x6, #0
	ldr x8, [sp, #2136]
	str x8, [x16, #0]
	ldr x8, [sp, #2144]
	str x8, [x16, #8]
	add x4, x2, #0
	add x5, x3, #0
	add x2, x0, #0
	add x3, x1, #0
	add x6, x7, #0
	add x7, x1, #0
	add x0, sp, #80
	ldr x2, [sp, #2152]
	ldr x3, [sp, #2160]
	bl {vg_rsa_public_precomputed_checked}
	add x16, sp, #0
	str x0, [x16, #56]
	add x8, sp, #1104
	add x9, x19, #0
	add x10, x20, #0
	add x11, x21, #0
	add x12, x22, #0
	sub w0, w10, #0
	cbz w0, 22f
	sub w0, w10, #1
	cbz w0, 24f
	sub w0, w10, #2
	cbz w0, 26f
	sub w0, w10, #3
	cbz w0, 28f
	sub w0, w10, #4
	cbz w0, 210f
	sub w0, w10, #5
	cbz w0, 212f
	sub w0, w10, #6
	cbz w0, 214f
	sub w0, w10, #7
	cbz w0, 216f
	sub w0, w10, #8
	cbz w0, 218f
	sub w0, w10, #9
	cbz w0, 220f
	sub w0, w10, #10
	cbz w0, 222f
	sub w0, w10, #11
	cbz w0, 224f
	movz x13, #2048, lsl #0
	movz x15, #0, lsl #0
	b 225f
224:
	movz x13, #83, lsl #0
	movz x15, #64, lsl #0
225:
	b 223f
222:
	movz x13, #67, lsl #0
	movz x15, #48, lsl #0
223:
	b 221f
220:
	movz x13, #51, lsl #0
	movz x15, #32, lsl #0
221:
	b 219f
218:
	movz x13, #47, lsl #0
	movz x15, #28, lsl #0
219:
	b 217f
216:
	movz x13, #51, lsl #0
	movz x15, #32, lsl #0
217:
	b 215f
214:
	movz x13, #47, lsl #0
	movz x15, #28, lsl #0
215:
	b 213f
212:
	movz x13, #83, lsl #0
	movz x15, #64, lsl #0
213:
	b 211f
210:
	movz x13, #67, lsl #0
	movz x15, #48, lsl #0
211:
	b 29f
28:
	movz x13, #51, lsl #0
	movz x15, #32, lsl #0
29:
	b 27f
26:
	movz x13, #47, lsl #0
	movz x15, #28, lsl #0
27:
	b 25f
24:
	movz x13, #35, lsl #0
	movz x15, #20, lsl #0
25:
	b 23f
22:
	movz x13, #34, lsl #0
	movz x15, #16, lsl #0
23:
	sub x0, x12, x15
	cbnz x0, 226f
	add x0, x13, #11
	sub x0, x9, x0
	lsr x0, x0, #63
	cbnz x0, 228f
	add x14, x8, #0
	movz x15, #0, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #1, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	sub x13, x9, x13
	sub x13, x13, #3
	movz x15, #255, lsl #0
230:
	strb w15, [x14, #0]
	add x14, x14, #1
	sub x13, x13, #1
	cbnz x13, 230b
	movz x15, #0, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	sub w0, w10, #0
	cbz w0, 231f
	sub w0, w10, #1
	cbz w0, 233f
	sub w0, w10, #2
	cbz w0, 235f
	sub w0, w10, #3
	cbz w0, 237f
	sub w0, w10, #4
	cbz w0, 239f
	sub w0, w10, #5
	cbz w0, 241f
	sub w0, w10, #6
	cbz w0, 243f
	sub w0, w10, #7
	cbz w0, 245f
	sub w0, w10, #8
	cbz w0, 247f
	sub w0, w10, #9
	cbz w0, 249f
	sub w0, w10, #10
	cbz w0, 251f
	sub w0, w10, #11
	cbz w0, 253f
	b 254f
253:
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #81, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #13, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #6, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #9, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #96, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #134, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #72, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #1, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #101, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #3, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #2, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #10, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #0, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #64, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
254:
	b 252f
251:
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #65, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #13, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #6, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #9, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #96, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #134, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #72, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #1, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #101, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #3, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #2, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #9, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #0, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
252:
	b 250f
249:
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #49, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #13, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #6, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #9, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #96, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #134, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #72, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #1, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #101, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #3, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #2, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #8, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #0, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #32, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
250:
	b 248f
247:
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #45, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #13, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #6, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #9, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #96, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #134, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #72, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #1, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #101, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #3, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #2, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #7, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #0, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #28, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
248:
	b 246f
245:
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #49, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #13, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #6, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #9, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #96, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #134, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #72, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #1, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #101, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #3, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #2, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #6, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #0, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #32, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
246:
	b 244f
243:
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #45, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #13, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #6, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #9, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #96, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #134, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #72, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #1, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #101, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #3, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #2, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #0, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #28, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
244:
	b 242f
241:
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #81, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #13, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #6, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #9, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #96, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #134, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #72, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #1, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #101, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #3, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #2, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #3, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #0, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #64, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
242:
	b 240f
239:
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #65, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #13, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #6, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #9, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #96, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #134, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #72, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #1, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #101, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #3, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #2, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #2, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #0, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
240:
	b 238f
237:
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #49, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #13, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #6, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #9, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #96, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #134, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #72, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #1, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #101, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #3, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #2, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #1, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #0, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #32, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
238:
	b 236f
235:
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #45, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #13, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #6, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #9, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #96, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #134, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #72, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #1, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #101, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #3, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #2, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #0, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #28, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
236:
	b 234f
233:
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #33, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #9, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #6, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #43, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #14, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #3, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #2, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #26, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #0, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #20, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
234:
	b 232f
231:
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #32, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #12, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #6, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #8, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #42, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #134, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #72, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #134, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #247, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #13, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #2, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #0, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #16, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
232:
255:
	ldrb w15, [x11, #0]
	strb w15, [x14, #0]
	add x11, x11, #1
	add x14, x14, #1
	sub x12, x12, #1
	cbnz x12, 255b
	movz x0, #1, lsl #0
	b 229f
228:
	movz x0, #0, lsl #0
229:
	b 227f
226:
	movz x0, #0, lsl #0
227:
	cbz x0, 256f
	add x14, sp, #80
	add x15, sp, #1104
	add x13, x19, #0
	movz x12, #0, lsl #0
258:
	ldrb w10, [x14, #0]
	ldrb w11, [x15, #0]
	eor x10, x10, x11
	orr x12, x12, x10
	add x14, x14, #1
	add x15, x15, #1
	sub x13, x13, #1
	cbnz x13, 258b
	sub x0, x12, #1
	lsr x0, x0, #63
	b 257f
256:
	movz x0, #0, lsl #0
257:
	add x16, sp, #0
	ldr x8, [x16, #56]
	and w0, w0, w8
	add x16, sp, #0
	ldr x19, [x16, #16]
	ldr x20, [x16, #24]
	ldr x21, [x16, #32]
	ldr x22, [x16, #40]
	ldr x30, [x16, #48]
	add sp, sp, #2128
	b 21f
20:
	movz x0, #0, lsl #0
21:
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
	movi v31.2d, #0
	tst x1, x1
	add w0, w0, #0
	sub sp, sp, #2144
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
	str q31, [x9, #784]
	str q31, [x9, #800]
	str q31, [x9, #816]
	str q31, [x9, #832]
	str q31, [x9, #848]
	str q31, [x9, #864]
	str q31, [x9, #880]
	str q31, [x9, #896]
	str q31, [x9, #912]
	str q31, [x9, #928]
	str q31, [x9, #944]
	str q31, [x9, #960]
	str q31, [x9, #976]
	str q31, [x9, #992]
	str q31, [x9, #1008]
	str q31, [x9, #1024]
	str q31, [x9, #1040]
	str q31, [x9, #1056]
	str q31, [x9, #1072]
	str q31, [x9, #1088]
	str q31, [x9, #1104]
	str q31, [x9, #1120]
	str q31, [x9, #1136]
	str q31, [x9, #1152]
	str q31, [x9, #1168]
	str q31, [x9, #1184]
	str q31, [x9, #1200]
	str q31, [x9, #1216]
	str q31, [x9, #1232]
	str q31, [x9, #1248]
	str q31, [x9, #1264]
	str q31, [x9, #1280]
	str q31, [x9, #1296]
	str q31, [x9, #1312]
	str q31, [x9, #1328]
	str q31, [x9, #1344]
	str q31, [x9, #1360]
	str q31, [x9, #1376]
	str q31, [x9, #1392]
	str q31, [x9, #1408]
	str q31, [x9, #1424]
	str q31, [x9, #1440]
	str q31, [x9, #1456]
	str q31, [x9, #1472]
	str q31, [x9, #1488]
	str q31, [x9, #1504]
	str q31, [x9, #1520]
	str q31, [x9, #1536]
	str q31, [x9, #1552]
	str q31, [x9, #1568]
	str q31, [x9, #1584]
	str q31, [x9, #1600]
	str q31, [x9, #1616]
	str q31, [x9, #1632]
	str q31, [x9, #1648]
	str q31, [x9, #1664]
	str q31, [x9, #1680]
	str q31, [x9, #1696]
	str q31, [x9, #1712]
	str q31, [x9, #1728]
	str q31, [x9, #1744]
	str q31, [x9, #1760]
	str q31, [x9, #1776]
	str q31, [x9, #1792]
	str q31, [x9, #1808]
	str q31, [x9, #1824]
	str q31, [x9, #1840]
	str q31, [x9, #1856]
	str q31, [x9, #1872]
	str q31, [x9, #1888]
	str q31, [x9, #1904]
	str q31, [x9, #1920]
	str q31, [x9, #1936]
	str q31, [x9, #1952]
	str q31, [x9, #1968]
	str q31, [x9, #1984]
	str q31, [x9, #2000]
	str q31, [x9, #2016]
	str q31, [x9, #2032]
	str q31, [x9, #2048]
	str q31, [x9, #2064]
	str q31, [x9, #2080]
	str q31, [x9, #2096]
	str q31, [x9, #2112]
	str q31, [x9, #2128]
	add sp, sp, #2144
	ret
	.p2align 6

vg_rsa_pkcs1_recover_precomputed:
	ldr x8, [sp, #0]
	sub x8, x8, x3
	cbnz x8, 20f
	sub sp, sp, #2128
	add x16, sp, #0
	str x19, [x16, #16]
	str x20, [x16, #24]
	str x21, [x16, #32]
	str x22, [x16, #40]
	str x30, [x16, #48]
	add x19, x0, #0
	add x20, x1, #0
	add x21, x3, #0
	add w22, w6, #0
	ldr x8, [sp, #2136]
	str x8, [x16, #0]
	ldr x8, [sp, #2144]
	str x8, [x16, #8]
	add x1, x3, #0
	add x6, x7, #0
	add x7, x3, #0
	add x0, sp, #80
	ldr x2, [sp, #2152]
	ldr x3, [sp, #2160]
	bl {vg_rsa_public_precomputed_checked}
	add x16, sp, #0
	str x0, [x16, #56]
	add x8, sp, #1104
	add x9, x21, #0
	add x10, x22, #0
	add x12, x20, #0
	add x11, sp, #80
	add x11, x11, x21
	sub x11, x11, x20
	sub w0, w10, #0
	cbz w0, 22f
	sub w0, w10, #1
	cbz w0, 24f
	sub w0, w10, #2
	cbz w0, 26f
	sub w0, w10, #3
	cbz w0, 28f
	sub w0, w10, #4
	cbz w0, 210f
	sub w0, w10, #5
	cbz w0, 212f
	sub w0, w10, #6
	cbz w0, 214f
	sub w0, w10, #7
	cbz w0, 216f
	sub w0, w10, #8
	cbz w0, 218f
	sub w0, w10, #9
	cbz w0, 220f
	sub w0, w10, #10
	cbz w0, 222f
	sub w0, w10, #11
	cbz w0, 224f
	movz x13, #2048, lsl #0
	movz x15, #0, lsl #0
	b 225f
224:
	movz x13, #83, lsl #0
	movz x15, #64, lsl #0
225:
	b 223f
222:
	movz x13, #67, lsl #0
	movz x15, #48, lsl #0
223:
	b 221f
220:
	movz x13, #51, lsl #0
	movz x15, #32, lsl #0
221:
	b 219f
218:
	movz x13, #47, lsl #0
	movz x15, #28, lsl #0
219:
	b 217f
216:
	movz x13, #51, lsl #0
	movz x15, #32, lsl #0
217:
	b 215f
214:
	movz x13, #47, lsl #0
	movz x15, #28, lsl #0
215:
	b 213f
212:
	movz x13, #83, lsl #0
	movz x15, #64, lsl #0
213:
	b 211f
210:
	movz x13, #67, lsl #0
	movz x15, #48, lsl #0
211:
	b 29f
28:
	movz x13, #51, lsl #0
	movz x15, #32, lsl #0
29:
	b 27f
26:
	movz x13, #47, lsl #0
	movz x15, #28, lsl #0
27:
	b 25f
24:
	movz x13, #35, lsl #0
	movz x15, #20, lsl #0
25:
	b 23f
22:
	movz x13, #34, lsl #0
	movz x15, #16, lsl #0
23:
	sub x0, x12, x15
	cbnz x0, 226f
	add x0, x13, #11
	sub x0, x9, x0
	lsr x0, x0, #63
	cbnz x0, 228f
	add x14, x8, #0
	movz x15, #0, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #1, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	sub x13, x9, x13
	sub x13, x13, #3
	movz x15, #255, lsl #0
230:
	strb w15, [x14, #0]
	add x14, x14, #1
	sub x13, x13, #1
	cbnz x13, 230b
	movz x15, #0, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	sub w0, w10, #0
	cbz w0, 231f
	sub w0, w10, #1
	cbz w0, 233f
	sub w0, w10, #2
	cbz w0, 235f
	sub w0, w10, #3
	cbz w0, 237f
	sub w0, w10, #4
	cbz w0, 239f
	sub w0, w10, #5
	cbz w0, 241f
	sub w0, w10, #6
	cbz w0, 243f
	sub w0, w10, #7
	cbz w0, 245f
	sub w0, w10, #8
	cbz w0, 247f
	sub w0, w10, #9
	cbz w0, 249f
	sub w0, w10, #10
	cbz w0, 251f
	sub w0, w10, #11
	cbz w0, 253f
	b 254f
253:
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #81, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #13, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #6, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #9, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #96, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #134, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #72, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #1, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #101, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #3, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #2, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #10, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #0, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #64, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
254:
	b 252f
251:
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #65, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #13, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #6, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #9, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #96, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #134, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #72, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #1, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #101, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #3, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #2, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #9, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #0, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
252:
	b 250f
249:
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #49, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #13, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #6, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #9, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #96, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #134, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #72, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #1, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #101, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #3, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #2, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #8, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #0, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #32, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
250:
	b 248f
247:
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #45, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #13, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #6, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #9, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #96, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #134, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #72, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #1, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #101, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #3, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #2, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #7, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #0, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #28, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
248:
	b 246f
245:
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #49, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #13, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #6, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #9, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #96, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #134, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #72, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #1, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #101, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #3, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #2, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #6, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #0, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #32, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
246:
	b 244f
243:
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #45, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #13, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #6, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #9, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #96, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #134, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #72, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #1, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #101, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #3, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #2, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #0, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #28, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
244:
	b 242f
241:
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #81, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #13, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #6, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #9, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #96, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #134, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #72, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #1, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #101, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #3, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #2, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #3, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #0, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #64, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
242:
	b 240f
239:
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #65, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #13, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #6, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #9, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #96, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #134, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #72, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #1, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #101, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #3, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #2, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #2, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #0, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
240:
	b 238f
237:
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #49, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #13, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #6, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #9, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #96, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #134, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #72, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #1, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #101, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #3, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #2, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #1, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #0, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #32, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
238:
	b 236f
235:
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #45, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #13, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #6, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #9, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #96, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #134, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #72, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #1, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #101, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #3, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #2, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #0, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #28, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
236:
	b 234f
233:
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #33, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #9, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #6, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #43, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #14, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #3, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #2, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #26, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #0, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #20, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
234:
	b 232f
231:
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #32, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #48, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #12, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #6, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #8, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #42, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #134, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #72, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #134, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #247, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #13, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #2, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #5, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #0, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #4, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
	movz x15, #16, lsl #0
	strb w15, [x14, #0]
	add x14, x14, #1
232:
255:
	ldrb w15, [x11, #0]
	strb w15, [x14, #0]
	add x11, x11, #1
	add x14, x14, #1
	sub x12, x12, #1
	cbnz x12, 255b
	movz x0, #1, lsl #0
	b 229f
228:
	movz x0, #0, lsl #0
229:
	b 227f
226:
	movz x0, #0, lsl #0
227:
	cbz x0, 256f
	add x14, sp, #80
	add x15, sp, #1104
	add x13, x21, #0
	movz x12, #0, lsl #0
258:
	ldrb w10, [x14, #0]
	ldrb w11, [x15, #0]
	eor x10, x10, x11
	orr x12, x12, x10
	add x14, x14, #1
	add x15, x15, #1
	sub x13, x13, #1
	cbnz x13, 258b
	movz x13, #1, lsl #0
	subs x12, x12, x13
	sbc x12, x12, x12
	add x16, sp, #0
	ldr x8, [x16, #56]
	subs w8, w8, w13
	sbc x8, x8, x8
	bic x12, x12, x8, ror #0
	str x12, [x16, #64]
	add x14, x19, #0
	add x12, x20, #0
	add x11, sp, #80
	add x11, x11, x21
	sub x11, x11, x20
259:
	ldrb w15, [x11, #0]
	strb w15, [x14, #0]
	add x11, x11, #1
	add x14, x14, #1
	sub x12, x12, #1
	cbnz x12, 259b
	movz x0, #1, lsl #0
	add x16, sp, #0
	ldr x9, [x16, #64]
	add x11, x19, #0
	add x12, x20, #0
260:
	ldrb w10, [x11, #0]
	and x10, x10, x9
	strb w10, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 260b
	and x0, x0, x9
	b 257f
256:
	add x14, x19, #0
	add x13, x20, #0
	movz x15, #0, lsl #0
261:
	strb w15, [x14, #0]
	add x14, x14, #1
	sub x13, x13, #1
	cbnz x13, 261b
	movz x0, #0, lsl #0
257:
	add x16, sp, #0
	ldr x19, [x16, #16]
	ldr x20, [x16, #24]
	ldr x21, [x16, #32]
	ldr x22, [x16, #40]
	ldr x30, [x16, #48]
	add sp, sp, #2128
	b 21f
20:
	add x14, x0, #0
	add x13, x1, #0
	movz x15, #0, lsl #0
262:
	strb w15, [x14, #0]
	add x14, x14, #1
	sub x13, x13, #1
	cbnz x13, 262b
	movz x0, #0, lsl #0
21:
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
	movi v31.2d, #0
	tst x1, x1
	add w0, w0, #0
	sub sp, sp, #2144
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
	str q31, [x9, #784]
	str q31, [x9, #800]
	str q31, [x9, #816]
	str q31, [x9, #832]
	str q31, [x9, #848]
	str q31, [x9, #864]
	str q31, [x9, #880]
	str q31, [x9, #896]
	str q31, [x9, #912]
	str q31, [x9, #928]
	str q31, [x9, #944]
	str q31, [x9, #960]
	str q31, [x9, #976]
	str q31, [x9, #992]
	str q31, [x9, #1008]
	str q31, [x9, #1024]
	str q31, [x9, #1040]
	str q31, [x9, #1056]
	str q31, [x9, #1072]
	str q31, [x9, #1088]
	str q31, [x9, #1104]
	str q31, [x9, #1120]
	str q31, [x9, #1136]
	str q31, [x9, #1152]
	str q31, [x9, #1168]
	str q31, [x9, #1184]
	str q31, [x9, #1200]
	str q31, [x9, #1216]
	str q31, [x9, #1232]
	str q31, [x9, #1248]
	str q31, [x9, #1264]
	str q31, [x9, #1280]
	str q31, [x9, #1296]
	str q31, [x9, #1312]
	str q31, [x9, #1328]
	str q31, [x9, #1344]
	str q31, [x9, #1360]
	str q31, [x9, #1376]
	str q31, [x9, #1392]
	str q31, [x9, #1408]
	str q31, [x9, #1424]
	str q31, [x9, #1440]
	str q31, [x9, #1456]
	str q31, [x9, #1472]
	str q31, [x9, #1488]
	str q31, [x9, #1504]
	str q31, [x9, #1520]
	str q31, [x9, #1536]
	str q31, [x9, #1552]
	str q31, [x9, #1568]
	str q31, [x9, #1584]
	str q31, [x9, #1600]
	str q31, [x9, #1616]
	str q31, [x9, #1632]
	str q31, [x9, #1648]
	str q31, [x9, #1664]
	str q31, [x9, #1680]
	str q31, [x9, #1696]
	str q31, [x9, #1712]
	str q31, [x9, #1728]
	str q31, [x9, #1744]
	str q31, [x9, #1760]
	str q31, [x9, #1776]
	str q31, [x9, #1792]
	str q31, [x9, #1808]
	str q31, [x9, #1824]
	str q31, [x9, #1840]
	str q31, [x9, #1856]
	str q31, [x9, #1872]
	str q31, [x9, #1888]
	str q31, [x9, #1904]
	str q31, [x9, #1920]
	str q31, [x9, #1936]
	str q31, [x9, #1952]
	str q31, [x9, #1968]
	str q31, [x9, #1984]
	str q31, [x9, #2000]
	str q31, [x9, #2016]
	str q31, [x9, #2032]
	str q31, [x9, #2048]
	str q31, [x9, #2064]
	str q31, [x9, #2080]
	str q31, [x9, #2096]
	str q31, [x9, #2112]
	str q31, [x9, #2128]
	add sp, sp, #2144
	ret
	.p2align 6
