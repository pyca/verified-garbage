// The functions of `src/cast5.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cast5_expand_key:
	mov r12, r3
	str r4, [r12, #64]
	str r5, [r12, #68]
	str r6, [r12, #72]
	str r7, [r12, #76]
	str r8, [r12, #80]
	str r9, [r12, #84]
	str r10, [r12, #88]
	str r11, [r12, #92]
	str lr, [r12, #96]
	mov r3, #0
	str r3, [r12, #16]
	str r3, [r12, #20]
	str r3, [r12, #24]
	str r3, [r12, #28]
	add r3, r12, #16
20:
	ldrb r4, [r0, #0]
	strb r4, [r3, #0]
	add r0, r0, #1
	add r3, r3, #1
	subs r1, r1, #1
	bne 20b
	mov lr, r2
	mov r3, #2
21:
	mov r2, #0
22:
	cmp r2, #0
	beq 23f
	cmp r2, #1
	beq 25f
	cmp r2, #2
	beq 27f
	cmp r2, #3
	beq 29f
	cmp r2, #4
	beq 211f
	cmp r2, #5
	beq 213f
	cmp r2, #6
	beq 215f
	cmp r2, #7
	beq 217f
	cmp r2, #8
	beq 219f
	cmp r2, #9
	beq 221f
	cmp r2, #10
	beq 223f
	cmp r2, #11
	beq 225f
	cmp r2, #12
	beq 227f
	cmp r2, #13
	beq 229f
	cmp r2, #14
	beq 231f
	cmp r2, #15
	beq 233f
	cmp r2, #16
	beq 235f
	cmp r2, #17
	beq 237f
	cmp r2, #18
	beq 239f
	cmp r2, #19
	beq 241f
	cmp r2, #20
	beq 243f
	cmp r2, #21
	beq 245f
	cmp r2, #22
	beq 247f
	cmp r2, #23
	beq 249f
	cmp r2, #24
	beq 251f
	cmp r2, #25
	beq 253f
	cmp r2, #26
	beq 255f
	cmp r2, #27
	beq 257f
	cmp r2, #28
	beq 259f
	cmp r2, #29
	beq 261f
	cmp r2, #30
	beq 263f
	cmp r2, #31
	beq 265f
	cmp r2, #32
	beq 267f
	cmp r2, #33
	beq 269f
	cmp r2, #34
	beq 271f
	cmp r2, #35
	beq 273f
	cmp r2, #36
	beq 275f
	cmp r2, #37
	beq 277f
	cmp r2, #38
	beq 279f
	cmp r2, #39
	beq 281f
	b 282f
281:
	ldrb r4, [r12, #16]
	ldrb r5, [r12, #17]
	ldrb r6, [r12, #31]
	ldrb r7, [r12, #30]
282:
	b 280f
279:
	ldrb r4, [r12, #18]
	ldrb r5, [r12, #19]
	ldrb r6, [r12, #29]
	ldrb r7, [r12, #28]
280:
	b 278f
277:
	ldrb r4, [r12, #20]
	ldrb r5, [r12, #21]
	ldrb r6, [r12, #27]
	ldrb r7, [r12, #26]
278:
	b 276f
275:
	ldrb r4, [r12, #22]
	ldrb r5, [r12, #23]
	ldrb r6, [r12, #25]
	ldrb r7, [r12, #24]
276:
	b 274f
273:
	ldrb r4, [r12, #29]
	ldrb r5, [r12, #24]
	ldrb r6, [r12, #23]
	ldrb r7, [r12, #19]
274:
	b 272f
271:
	ldrb r4, [r12, #24]
	ldrb r5, [r12, #27]
	ldrb r6, [r12, #25]
	ldrb r7, [r12, #26]
272:
	b 270f
269:
	ldrb r4, [r12, #20]
	ldrb r5, [r12, #21]
	ldrb r6, [r12, #22]
	ldrb r7, [r12, #23]
270:
	b 268f
267:
	ldrb r4, [r12, #19]
	ldrb r5, [r12, #17]
	ldrb r6, [r12, #18]
	ldrb r7, [r12, #16]
268:
	b 266f
265:
	ldrb r4, [r12, #38]
	ldrb r5, [r12, #36]
	ldrb r6, [r12, #39]
	ldrb r7, [r12, #37]
266:
	b 264f
263:
	ldrb r4, [r12, #34]
	ldrb r5, [r12, #32]
	ldrb r6, [r12, #35]
	ldrb r7, [r12, #33]
264:
	b 262f
261:
	ldrb r4, [r12, #43]
	ldrb r5, [r12, #42]
	ldrb r6, [r12, #36]
	ldrb r7, [r12, #37]
262:
	b 260f
259:
	ldrb r4, [r12, #41]
	ldrb r5, [r12, #40]
	ldrb r6, [r12, #38]
	ldrb r7, [r12, #39]
260:
	b 258f
257:
	ldrb r4, [r12, #47]
	ldrb r5, [r12, #46]
	ldrb r6, [r12, #32]
	ldrb r7, [r12, #33]
258:
	b 256f
255:
	ldrb r4, [r12, #45]
	ldrb r5, [r12, #44]
	ldrb r6, [r12, #34]
	ldrb r7, [r12, #35]
256:
	b 254f
253:
	ldrb r4, [r12, #38]
	ldrb r5, [r12, #34]
	ldrb r6, [r12, #44]
	ldrb r7, [r12, #41]
254:
	b 252f
251:
	ldrb r4, [r12, #40]
	ldrb r5, [r12, #43]
	ldrb r6, [r12, #41]
	ldrb r7, [r12, #42]
252:
	b 250f
249:
	ldrb r4, [r12, #36]
	ldrb r5, [r12, #37]
	ldrb r6, [r12, #38]
	ldrb r7, [r12, #39]
250:
	b 248f
247:
	ldrb r4, [r12, #35]
	ldrb r5, [r12, #33]
	ldrb r6, [r12, #34]
	ldrb r7, [r12, #32]
248:
	b 246f
245:
	ldrb r4, [r12, #30]
	ldrb r5, [r12, #28]
	ldrb r6, [r12, #31]
	ldrb r7, [r12, #29]
246:
	b 244f
243:
	ldrb r4, [r12, #26]
	ldrb r5, [r12, #24]
	ldrb r6, [r12, #27]
	ldrb r7, [r12, #25]
244:
	b 242f
241:
	ldrb r4, [r12, #27]
	ldrb r5, [r12, #26]
	ldrb r6, [r12, #20]
	ldrb r7, [r12, #21]
242:
	b 240f
239:
	ldrb r4, [r12, #25]
	ldrb r5, [r12, #24]
	ldrb r6, [r12, #22]
	ldrb r7, [r12, #23]
240:
	b 238f
237:
	ldrb r4, [r12, #31]
	ldrb r5, [r12, #30]
	ldrb r6, [r12, #16]
	ldrb r7, [r12, #17]
238:
	b 236f
235:
	ldrb r4, [r12, #29]
	ldrb r5, [r12, #28]
	ldrb r6, [r12, #18]
	ldrb r7, [r12, #19]
236:
	b 234f
233:
	ldrb r4, [r12, #23]
	ldrb r5, [r12, #19]
	ldrb r6, [r12, #29]
	ldrb r7, [r12, #24]
234:
	b 232f
231:
	ldrb r4, [r12, #24]
	ldrb r5, [r12, #27]
	ldrb r6, [r12, #25]
	ldrb r7, [r12, #26]
232:
	b 230f
229:
	ldrb r4, [r12, #20]
	ldrb r5, [r12, #21]
	ldrb r6, [r12, #22]
	ldrb r7, [r12, #23]
230:
	b 228f
227:
	ldrb r4, [r12, #19]
	ldrb r5, [r12, #17]
	ldrb r6, [r12, #18]
	ldrb r7, [r12, #16]
228:
	b 226f
225:
	ldrb r4, [r12, #38]
	ldrb r5, [r12, #36]
	ldrb r6, [r12, #39]
	ldrb r7, [r12, #37]
226:
	b 224f
223:
	ldrb r4, [r12, #34]
	ldrb r5, [r12, #32]
	ldrb r6, [r12, #35]
	ldrb r7, [r12, #33]
224:
	b 222f
221:
	ldrb r4, [r12, #32]
	ldrb r5, [r12, #33]
	ldrb r6, [r12, #47]
	ldrb r7, [r12, #46]
222:
	b 220f
219:
	ldrb r4, [r12, #34]
	ldrb r5, [r12, #35]
	ldrb r6, [r12, #45]
	ldrb r7, [r12, #44]
220:
	b 218f
217:
	ldrb r4, [r12, #36]
	ldrb r5, [r12, #37]
	ldrb r6, [r12, #43]
	ldrb r7, [r12, #42]
218:
	b 216f
215:
	ldrb r4, [r12, #38]
	ldrb r5, [r12, #39]
	ldrb r6, [r12, #41]
	ldrb r7, [r12, #40]
216:
	b 214f
213:
	ldrb r4, [r12, #44]
	ldrb r5, [r12, #41]
	ldrb r6, [r12, #38]
	ldrb r7, [r12, #34]
214:
	b 212f
211:
	ldrb r4, [r12, #40]
	ldrb r5, [r12, #43]
	ldrb r6, [r12, #41]
	ldrb r7, [r12, #42]
212:
	b 210f
29:
	ldrb r4, [r12, #36]
	ldrb r5, [r12, #37]
	ldrb r6, [r12, #38]
	ldrb r7, [r12, #39]
210:
	b 28f
27:
	ldrb r4, [r12, #35]
	ldrb r5, [r12, #33]
	ldrb r6, [r12, #34]
	ldrb r7, [r12, #32]
28:
	b 26f
25:
	ldrb r4, [r12, #30]
	ldrb r5, [r12, #28]
	ldrb r6, [r12, #31]
	ldrb r7, [r12, #29]
26:
	b 24f
23:
	ldrb r4, [r12, #26]
	ldrb r5, [r12, #24]
	ldrb r6, [r12, #27]
	ldrb r7, [r12, #25]
24:
	str r2, [r12, #104]
	str r3, [r12, #108]
	str lr, [r12, #112]
	add r4, r4, r5, lsl #8
	add r4, r4, r6, lsl #16
	add r4, r4, r7, lsl #24
	str r4, [r12, #116]
	mov r0, #0
	str r0, [r12, #120]
283:
	ldr r0, [r12, #116]
	and r0, r0, #255
	mov r3, #1
	and r1, r3, r0, lsr #3
	add r2, r3, r1
	and r1, r3, r0, lsr #4
	add lr, r3, r1, lsl #2
	sub lr, lr, r1
	mul r2, r2, lr
	and r1, r3, r0, lsr #5
	add lr, r3, r1, lsl #4
	sub lr, lr, r1
	mul r2, r2, lr
	and r1, r3, r0, lsr #6
	add lr, r3, r1, lsl #8
	sub lr, lr, r1
	mul r2, r2, lr
	and r1, r3, r0, lsr #7
	add lr, r3, r1, lsl #16
	sub lr, lr, r1
	mul r2, r2, lr
	mov r4, #0
	mov r5, #0
	mov r6, #0
	mov r7, #0
	mov r8, #0
	mov r9, #0
	mov r10, #0
	mov r11, #0
	movw lr, #:lower16:({VG_CAST5_S5678}
	movt lr, #:upper16:({VG_CAST5_S5678}
2:
	add lr, pc
3:
	ldr r0, [r12, #120]
	add lr, lr, r0
	mov r0, #4
	str r0, [r12, #124]
284:
	bic r1, r3, r2
	sub r1, r1, #1
	ldr r0, [lr, #0]
	and r0, r0, r1
	orr r4, r4, r0
	ldr r0, [lr, #16]
	and r0, r0, r1
	orr r5, r5, r0
	ldr r0, [lr, #32]
	mla r6, r0, r1, r6
	ldr r0, [lr, #48]
	mla r7, r0, r1, r7
	ldr r0, [lr, #64]
	and r0, r0, r1
	orr r8, r8, r0
	ldr r0, [lr, #80]
	and r0, r0, r1
	orr r9, r9, r0
	ldr r0, [lr, #96]
	mla r10, r0, r1, r10
	ldr r0, [lr, #112]
	mla r11, r0, r1, r11
	bic r1, r3, r2, lsr #1
	sub r1, r1, #1
	ldr r0, [lr, #128]
	and r0, r0, r1
	orr r4, r4, r0
	ldr r0, [lr, #144]
	and r0, r0, r1
	orr r5, r5, r0
	ldr r0, [lr, #160]
	mla r6, r0, r1, r6
	ldr r0, [lr, #176]
	mla r7, r0, r1, r7
	ldr r0, [lr, #192]
	and r0, r0, r1
	orr r8, r8, r0
	ldr r0, [lr, #208]
	and r0, r0, r1
	orr r9, r9, r0
	ldr r0, [lr, #224]
	mla r10, r0, r1, r10
	ldr r0, [lr, #240]
	mla r11, r0, r1, r11
	bic r1, r3, r2, lsr #2
	sub r1, r1, #1
	ldr r0, [lr, #256]
	and r0, r0, r1
	orr r4, r4, r0
	ldr r0, [lr, #272]
	and r0, r0, r1
	orr r5, r5, r0
	ldr r0, [lr, #288]
	mla r6, r0, r1, r6
	ldr r0, [lr, #304]
	mla r7, r0, r1, r7
	ldr r0, [lr, #320]
	and r0, r0, r1
	orr r8, r8, r0
	ldr r0, [lr, #336]
	and r0, r0, r1
	orr r9, r9, r0
	ldr r0, [lr, #352]
	mla r10, r0, r1, r10
	ldr r0, [lr, #368]
	mla r11, r0, r1, r11
	bic r1, r3, r2, lsr #3
	sub r1, r1, #1
	ldr r0, [lr, #384]
	and r0, r0, r1
	orr r4, r4, r0
	ldr r0, [lr, #400]
	and r0, r0, r1
	orr r5, r5, r0
	ldr r0, [lr, #416]
	mla r6, r0, r1, r6
	ldr r0, [lr, #432]
	mla r7, r0, r1, r7
	ldr r0, [lr, #448]
	and r0, r0, r1
	orr r8, r8, r0
	ldr r0, [lr, #464]
	and r0, r0, r1
	orr r9, r9, r0
	ldr r0, [lr, #480]
	mla r10, r0, r1, r10
	ldr r0, [lr, #496]
	mla r11, r0, r1, r11
	bic r1, r3, r2, lsr #4
	sub r1, r1, #1
	ldr r0, [lr, #512]
	and r0, r0, r1
	orr r4, r4, r0
	ldr r0, [lr, #528]
	and r0, r0, r1
	orr r5, r5, r0
	ldr r0, [lr, #544]
	mla r6, r0, r1, r6
	ldr r0, [lr, #560]
	mla r7, r0, r1, r7
	ldr r0, [lr, #576]
	and r0, r0, r1
	orr r8, r8, r0
	ldr r0, [lr, #592]
	and r0, r0, r1
	orr r9, r9, r0
	ldr r0, [lr, #608]
	mla r10, r0, r1, r10
	ldr r0, [lr, #624]
	mla r11, r0, r1, r11
	bic r1, r3, r2, lsr #5
	sub r1, r1, #1
	ldr r0, [lr, #640]
	and r0, r0, r1
	orr r4, r4, r0
	ldr r0, [lr, #656]
	and r0, r0, r1
	orr r5, r5, r0
	ldr r0, [lr, #672]
	mla r6, r0, r1, r6
	ldr r0, [lr, #688]
	mla r7, r0, r1, r7
	ldr r0, [lr, #704]
	and r0, r0, r1
	orr r8, r8, r0
	ldr r0, [lr, #720]
	and r0, r0, r1
	orr r9, r9, r0
	ldr r0, [lr, #736]
	mla r10, r0, r1, r10
	ldr r0, [lr, #752]
	mla r11, r0, r1, r11
	bic r1, r3, r2, lsr #6
	sub r1, r1, #1
	ldr r0, [lr, #768]
	and r0, r0, r1
	orr r4, r4, r0
	ldr r0, [lr, #784]
	and r0, r0, r1
	orr r5, r5, r0
	ldr r0, [lr, #800]
	mla r6, r0, r1, r6
	ldr r0, [lr, #816]
	mla r7, r0, r1, r7
	ldr r0, [lr, #832]
	and r0, r0, r1
	orr r8, r8, r0
	ldr r0, [lr, #848]
	and r0, r0, r1
	orr r9, r9, r0
	ldr r0, [lr, #864]
	mla r10, r0, r1, r10
	ldr r0, [lr, #880]
	mla r11, r0, r1, r11
	bic r1, r3, r2, lsr #7
	sub r1, r1, #1
	ldr r0, [lr, #896]
	and r0, r0, r1
	orr r4, r4, r0
	ldr r0, [lr, #912]
	and r0, r0, r1
	orr r5, r5, r0
	ldr r0, [lr, #928]
	mla r6, r0, r1, r6
	ldr r0, [lr, #944]
	mla r7, r0, r1, r7
	ldr r0, [lr, #960]
	and r0, r0, r1
	orr r8, r8, r0
	ldr r0, [lr, #976]
	and r0, r0, r1
	orr r9, r9, r0
	ldr r0, [lr, #992]
	mla r10, r0, r1, r10
	ldr r0, [lr, #1008]
	mla r11, r0, r1, r11
	lsr r2, r2, #8
	add lr, lr, #1024
	ldr r0, [r12, #124]
	subs r0, r0, #1
	str r0, [r12, #124]
	bne 284b
	ldr r2, [r12, #116]
	and lr, r2, #7
	lsr r2, r2, #8
	str r2, [r12, #116]
	mov r1, #0
	mov r3, #0
	eor r0, lr, #0
	sub r0, r0, #1
	lsr r0, r0, #31
	mla r1, r4, r0, r1
	eor r0, lr, #1
	sub r0, r0, #1
	lsr r0, r0, #31
	mla r1, r5, r0, r1
	eor r0, lr, #2
	sub r0, r0, #1
	lsr r0, r0, #31
	mla r3, r6, r0, r3
	eor r0, lr, #3
	sub r0, r0, #1
	lsr r0, r0, #31
	mla r3, r7, r0, r3
	eor r0, lr, #4
	sub r0, r0, #1
	lsr r0, r0, #31
	mla r1, r8, r0, r1
	eor r0, lr, #5
	sub r0, r0, #1
	lsr r0, r0, #31
	mla r1, r9, r0, r1
	eor r0, lr, #6
	sub r0, r0, #1
	lsr r0, r0, #31
	mla r3, r10, r0, r3
	eor r0, lr, #7
	sub r0, r0, #1
	lsr r0, r0, #31
	mla r3, r11, r0, r3
	sub r1, r1, r3
	ldr r0, [r12, #136]
	str r0, [r12, #140]
	ldr r0, [r12, #132]
	str r0, [r12, #136]
	ldr r0, [r12, #128]
	str r0, [r12, #132]
	str r1, [r12, #128]
	ldr r0, [r12, #120]
	add r0, r0, #4
	str r0, [r12, #120]
	cmp r0, #16
	bne 283b
	ldr r8, [r12, #140]
	ldr r9, [r12, #136]
	ldr r10, [r12, #132]
	ldr r11, [r12, #128]
	ldr r2, [r12, #104]
	ldr r3, [r12, #108]
	ldr lr, [r12, #112]
	cmp r2, #0
	beq 285f
	cmp r2, #1
	beq 287f
	cmp r2, #2
	beq 289f
	cmp r2, #3
	beq 291f
	cmp r2, #4
	beq 293f
	cmp r2, #5
	beq 295f
	cmp r2, #6
	beq 297f
	cmp r2, #7
	beq 299f
	cmp r2, #8
	beq 2101f
	cmp r2, #9
	beq 2103f
	cmp r2, #10
	beq 2105f
	cmp r2, #11
	beq 2107f
	cmp r2, #12
	beq 2109f
	cmp r2, #13
	beq 2111f
	cmp r2, #14
	beq 2113f
	cmp r2, #15
	beq 2115f
	cmp r2, #16
	beq 2117f
	cmp r2, #17
	beq 2119f
	cmp r2, #18
	beq 2121f
	cmp r2, #19
	beq 2123f
	cmp r2, #20
	beq 2125f
	cmp r2, #21
	beq 2127f
	cmp r2, #22
	beq 2129f
	cmp r2, #23
	beq 2131f
	cmp r2, #24
	beq 2133f
	cmp r2, #25
	beq 2135f
	cmp r2, #26
	beq 2137f
	cmp r2, #27
	beq 2139f
	cmp r2, #28
	beq 2141f
	cmp r2, #29
	beq 2143f
	cmp r2, #30
	beq 2145f
	cmp r2, #31
	beq 2147f
	cmp r2, #32
	beq 2149f
	cmp r2, #33
	beq 2151f
	cmp r2, #34
	beq 2153f
	cmp r2, #35
	beq 2155f
	cmp r2, #36
	beq 2157f
	cmp r2, #37
	beq 2159f
	cmp r2, #38
	beq 2161f
	cmp r2, #39
	beq 2163f
	b 2164f
2163:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #48]
	eor r0, r0, r1
	str r0, [lr, #60]
2164:
	b 2162f
2161:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #52]
	eor r0, r0, r1
	str r0, [lr, #56]
2162:
	b 2160f
2159:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #56]
	eor r0, r0, r1
	str r0, [lr, #52]
2160:
	b 2158f
2157:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #60]
	eor r0, r0, r1
	str r0, [lr, #48]
2158:
	b 2156f
2155:
	str r8, [r12, #48]
	str r9, [r12, #52]
	str r10, [r12, #56]
	str r11, [r12, #60]
2156:
	b 2154f
2153:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #56]
	eor r0, r0, r1
	ldr r1, [r12, #44]
	rev r1, r1
	eor r0, r0, r1
	rev r0, r0
	str r0, [r12, #28]
2154:
	b 2152f
2151:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #60]
	eor r0, r0, r1
	ldr r1, [r12, #36]
	rev r1, r1
	eor r0, r0, r1
	rev r0, r0
	str r0, [r12, #24]
2152:
	b 2150f
2149:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #48]
	eor r0, r0, r1
	ldr r1, [r12, #32]
	rev r1, r1
	eor r0, r0, r1
	rev r0, r0
	str r0, [r12, #20]
2150:
	b 2148f
2147:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #52]
	eor r0, r0, r1
	ldr r1, [r12, #40]
	rev r1, r1
	eor r0, r0, r1
	rev r0, r0
	str r0, [r12, #16]
2148:
	b 2146f
2145:
	str r8, [r12, #48]
	str r9, [r12, #52]
	str r10, [r12, #56]
	str r11, [r12, #60]
2146:
	b 2144f
2143:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #48]
	eor r0, r0, r1
	str r0, [lr, #44]
2144:
	b 2142f
2141:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #52]
	eor r0, r0, r1
	str r0, [lr, #40]
2142:
	b 2140f
2139:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #56]
	eor r0, r0, r1
	str r0, [lr, #36]
2140:
	b 2138f
2137:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #60]
	eor r0, r0, r1
	str r0, [lr, #32]
2138:
	b 2136f
2135:
	str r8, [r12, #48]
	str r9, [r12, #52]
	str r10, [r12, #56]
	str r11, [r12, #60]
2136:
	b 2134f
2133:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #56]
	eor r0, r0, r1
	ldr r1, [r12, #20]
	rev r1, r1
	eor r0, r0, r1
	rev r0, r0
	str r0, [r12, #44]
2134:
	b 2132f
2131:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #60]
	eor r0, r0, r1
	ldr r1, [r12, #28]
	rev r1, r1
	eor r0, r0, r1
	rev r0, r0
	str r0, [r12, #40]
2132:
	b 2130f
2129:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #48]
	eor r0, r0, r1
	ldr r1, [r12, #24]
	rev r1, r1
	eor r0, r0, r1
	rev r0, r0
	str r0, [r12, #36]
2130:
	b 2128f
2127:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #52]
	eor r0, r0, r1
	ldr r1, [r12, #16]
	rev r1, r1
	eor r0, r0, r1
	rev r0, r0
	str r0, [r12, #32]
2128:
	b 2126f
2125:
	str r8, [r12, #48]
	str r9, [r12, #52]
	str r10, [r12, #56]
	str r11, [r12, #60]
2126:
	b 2124f
2123:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #48]
	eor r0, r0, r1
	str r0, [lr, #28]
2124:
	b 2122f
2121:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #52]
	eor r0, r0, r1
	str r0, [lr, #24]
2122:
	b 2120f
2119:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #56]
	eor r0, r0, r1
	str r0, [lr, #20]
2120:
	b 2118f
2117:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #60]
	eor r0, r0, r1
	str r0, [lr, #16]
2118:
	b 2116f
2115:
	str r8, [r12, #48]
	str r9, [r12, #52]
	str r10, [r12, #56]
	str r11, [r12, #60]
2116:
	b 2114f
2113:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #56]
	eor r0, r0, r1
	ldr r1, [r12, #44]
	rev r1, r1
	eor r0, r0, r1
	rev r0, r0
	str r0, [r12, #28]
2114:
	b 2112f
2111:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #60]
	eor r0, r0, r1
	ldr r1, [r12, #36]
	rev r1, r1
	eor r0, r0, r1
	rev r0, r0
	str r0, [r12, #24]
2112:
	b 2110f
2109:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #48]
	eor r0, r0, r1
	ldr r1, [r12, #32]
	rev r1, r1
	eor r0, r0, r1
	rev r0, r0
	str r0, [r12, #20]
2110:
	b 2108f
2107:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #52]
	eor r0, r0, r1
	ldr r1, [r12, #40]
	rev r1, r1
	eor r0, r0, r1
	rev r0, r0
	str r0, [r12, #16]
2108:
	b 2106f
2105:
	str r8, [r12, #48]
	str r9, [r12, #52]
	str r10, [r12, #56]
	str r11, [r12, #60]
2106:
	b 2104f
2103:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #48]
	eor r0, r0, r1
	str r0, [lr, #12]
2104:
	b 2102f
2101:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #52]
	eor r0, r0, r1
	str r0, [lr, #8]
2102:
	b 2100f
299:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #56]
	eor r0, r0, r1
	str r0, [lr, #4]
2100:
	b 298f
297:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #60]
	eor r0, r0, r1
	str r0, [lr, #0]
298:
	b 296f
295:
	str r8, [r12, #48]
	str r9, [r12, #52]
	str r10, [r12, #56]
	str r11, [r12, #60]
296:
	b 294f
293:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #56]
	eor r0, r0, r1
	ldr r1, [r12, #20]
	rev r1, r1
	eor r0, r0, r1
	rev r0, r0
	str r0, [r12, #44]
294:
	b 292f
291:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #60]
	eor r0, r0, r1
	ldr r1, [r12, #28]
	rev r1, r1
	eor r0, r0, r1
	rev r0, r0
	str r0, [r12, #40]
292:
	b 290f
289:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #48]
	eor r0, r0, r1
	ldr r1, [r12, #24]
	rev r1, r1
	eor r0, r0, r1
	rev r0, r0
	str r0, [r12, #36]
290:
	b 288f
287:
	eor r0, r8, r9
	eor r0, r0, r10
	eor r0, r0, r11
	ldr r1, [r12, #52]
	eor r0, r0, r1
	ldr r1, [r12, #16]
	rev r1, r1
	eor r0, r0, r1
	rev r0, r0
	str r0, [r12, #32]
288:
	b 286f
285:
	str r8, [r12, #48]
	str r9, [r12, #52]
	str r10, [r12, #56]
	str r11, [r12, #60]
286:
	add r2, r2, #1
	cmp r2, #40
	bne 22b
	add lr, lr, #64
	subs r3, r3, #1
	bne 21b
	ldr r4, [r12, #64]
	ldr r5, [r12, #68]
	ldr r6, [r12, #72]
	ldr r7, [r12, #76]
	ldr r8, [r12, #80]
	ldr r9, [r12, #84]
	ldr r10, [r12, #88]
	ldr r11, [r12, #92]
	ldr lr, [r12, #96]
	bx lr

vg_cast5_ecb_encrypt:
	ldr r12, [sp, #0]
	str r4, [r12, #64]
	str r5, [r12, #68]
	str r6, [r12, #72]
	str r7, [r12, #76]
	str r8, [r12, #80]
	str r9, [r12, #84]
	str r10, [r12, #88]
	str r11, [r12, #92]
	str lr, [r12, #96]
	str r2, [r12, #0]
	str r3, [r12, #4]
	str r0, [r12, #8]
	str r1, [r12, #12]
	cmp r3, #0
	beq 20f
22:
	ldr r0, [r12, #0]
	ldr r2, [r0, #0]
	rev r2, r2
	ldr r3, [r0, #4]
	rev r3, r3
	ldr lr, [r12, #8]
	ldr r1, [r12, #12]
	str r1, [r12, #16]
	mov r1, #1
	str r1, [r12, #20]
23:
	ldr r0, [r12, #20]
	cmp r0, #1
	beq 24f
	cmp r0, #2
	beq 26f
	ldr r1, [lr, #0]
	sub r1, r1, r3
	b 27f
26:
	ldr r1, [lr, #0]
	eor r1, r1, r3
27:
	b 25f
24:
	ldr r1, [lr, #0]
	add r1, r1, r3
25:
	ldr r0, [lr, #64]
	and r4, r0, #1
	sub r4, r4, #1
	ror r5, r1, #31
	eor r1, r1, r5
	and r1, r1, r4
	eor r1, r1, r5
	lsr r0, r0, #1
	and r4, r0, #1
	sub r4, r4, #1
	ror r5, r1, #30
	eor r1, r1, r5
	and r1, r1, r4
	eor r1, r1, r5
	lsr r0, r0, #1
	and r4, r0, #1
	sub r4, r4, #1
	ror r5, r1, #28
	eor r1, r1, r5
	and r1, r1, r4
	eor r1, r1, r5
	lsr r0, r0, #1
	and r4, r0, #1
	sub r4, r4, #1
	ror r5, r1, #24
	eor r1, r1, r5
	and r1, r1, r4
	eor r1, r1, r5
	lsr r0, r0, #1
	and r4, r0, #1
	sub r4, r4, #1
	ror r5, r1, #16
	eor r1, r1, r5
	and r1, r1, r4
	eor r1, r1, r5
	and r4, r1, #255
	lsr r5, r1, #8
	and r5, r5, #255
	lsr r6, r1, #16
	and r6, r6, #255
	lsr r7, r1, #24
	str r2, [r12, #24]
	str r3, [r12, #28]
	str lr, [r12, #32]
	add r4, r4, r5, lsl #8
	add r4, r4, r6, lsl #16
	add r4, r4, r7, lsl #24
	str r4, [r12, #36]
	mov r0, #0
	str r0, [r12, #40]
28:
	ldr r0, [r12, #36]
	and r0, r0, #255
	mov r3, #1
	and r1, r3, r0, lsr #3
	add r2, r3, r1
	and r1, r3, r0, lsr #4
	add lr, r3, r1, lsl #2
	sub lr, lr, r1
	mul r2, r2, lr
	and r1, r3, r0, lsr #5
	add lr, r3, r1, lsl #4
	sub lr, lr, r1
	mul r2, r2, lr
	and r1, r3, r0, lsr #6
	add lr, r3, r1, lsl #8
	sub lr, lr, r1
	mul r2, r2, lr
	and r1, r3, r0, lsr #7
	add lr, r3, r1, lsl #16
	sub lr, lr, r1
	mul r2, r2, lr
	mov r4, #0
	mov r5, #0
	mov r6, #0
	mov r7, #0
	mov r8, #0
	mov r9, #0
	mov r10, #0
	mov r11, #0
	movw lr, #:lower16:({VG_CAST5_S1234}
	movt lr, #:upper16:({VG_CAST5_S1234}
2:
	add lr, pc
3:
	ldr r0, [r12, #40]
	add lr, lr, r0
	mov r0, #4
	str r0, [r12, #44]
29:
	bic r1, r3, r2
	sub r1, r1, #1
	ldr r0, [lr, #0]
	and r0, r0, r1
	orr r4, r4, r0
	ldr r0, [lr, #16]
	and r0, r0, r1
	orr r5, r5, r0
	ldr r0, [lr, #32]
	mla r6, r0, r1, r6
	ldr r0, [lr, #48]
	mla r7, r0, r1, r7
	ldr r0, [lr, #64]
	and r0, r0, r1
	orr r8, r8, r0
	ldr r0, [lr, #80]
	and r0, r0, r1
	orr r9, r9, r0
	ldr r0, [lr, #96]
	mla r10, r0, r1, r10
	ldr r0, [lr, #112]
	mla r11, r0, r1, r11
	bic r1, r3, r2, lsr #1
	sub r1, r1, #1
	ldr r0, [lr, #128]
	and r0, r0, r1
	orr r4, r4, r0
	ldr r0, [lr, #144]
	and r0, r0, r1
	orr r5, r5, r0
	ldr r0, [lr, #160]
	mla r6, r0, r1, r6
	ldr r0, [lr, #176]
	mla r7, r0, r1, r7
	ldr r0, [lr, #192]
	and r0, r0, r1
	orr r8, r8, r0
	ldr r0, [lr, #208]
	and r0, r0, r1
	orr r9, r9, r0
	ldr r0, [lr, #224]
	mla r10, r0, r1, r10
	ldr r0, [lr, #240]
	mla r11, r0, r1, r11
	bic r1, r3, r2, lsr #2
	sub r1, r1, #1
	ldr r0, [lr, #256]
	and r0, r0, r1
	orr r4, r4, r0
	ldr r0, [lr, #272]
	and r0, r0, r1
	orr r5, r5, r0
	ldr r0, [lr, #288]
	mla r6, r0, r1, r6
	ldr r0, [lr, #304]
	mla r7, r0, r1, r7
	ldr r0, [lr, #320]
	and r0, r0, r1
	orr r8, r8, r0
	ldr r0, [lr, #336]
	and r0, r0, r1
	orr r9, r9, r0
	ldr r0, [lr, #352]
	mla r10, r0, r1, r10
	ldr r0, [lr, #368]
	mla r11, r0, r1, r11
	bic r1, r3, r2, lsr #3
	sub r1, r1, #1
	ldr r0, [lr, #384]
	and r0, r0, r1
	orr r4, r4, r0
	ldr r0, [lr, #400]
	and r0, r0, r1
	orr r5, r5, r0
	ldr r0, [lr, #416]
	mla r6, r0, r1, r6
	ldr r0, [lr, #432]
	mla r7, r0, r1, r7
	ldr r0, [lr, #448]
	and r0, r0, r1
	orr r8, r8, r0
	ldr r0, [lr, #464]
	and r0, r0, r1
	orr r9, r9, r0
	ldr r0, [lr, #480]
	mla r10, r0, r1, r10
	ldr r0, [lr, #496]
	mla r11, r0, r1, r11
	bic r1, r3, r2, lsr #4
	sub r1, r1, #1
	ldr r0, [lr, #512]
	and r0, r0, r1
	orr r4, r4, r0
	ldr r0, [lr, #528]
	and r0, r0, r1
	orr r5, r5, r0
	ldr r0, [lr, #544]
	mla r6, r0, r1, r6
	ldr r0, [lr, #560]
	mla r7, r0, r1, r7
	ldr r0, [lr, #576]
	and r0, r0, r1
	orr r8, r8, r0
	ldr r0, [lr, #592]
	and r0, r0, r1
	orr r9, r9, r0
	ldr r0, [lr, #608]
	mla r10, r0, r1, r10
	ldr r0, [lr, #624]
	mla r11, r0, r1, r11
	bic r1, r3, r2, lsr #5
	sub r1, r1, #1
	ldr r0, [lr, #640]
	and r0, r0, r1
	orr r4, r4, r0
	ldr r0, [lr, #656]
	and r0, r0, r1
	orr r5, r5, r0
	ldr r0, [lr, #672]
	mla r6, r0, r1, r6
	ldr r0, [lr, #688]
	mla r7, r0, r1, r7
	ldr r0, [lr, #704]
	and r0, r0, r1
	orr r8, r8, r0
	ldr r0, [lr, #720]
	and r0, r0, r1
	orr r9, r9, r0
	ldr r0, [lr, #736]
	mla r10, r0, r1, r10
	ldr r0, [lr, #752]
	mla r11, r0, r1, r11
	bic r1, r3, r2, lsr #6
	sub r1, r1, #1
	ldr r0, [lr, #768]
	and r0, r0, r1
	orr r4, r4, r0
	ldr r0, [lr, #784]
	and r0, r0, r1
	orr r5, r5, r0
	ldr r0, [lr, #800]
	mla r6, r0, r1, r6
	ldr r0, [lr, #816]
	mla r7, r0, r1, r7
	ldr r0, [lr, #832]
	and r0, r0, r1
	orr r8, r8, r0
	ldr r0, [lr, #848]
	and r0, r0, r1
	orr r9, r9, r0
	ldr r0, [lr, #864]
	mla r10, r0, r1, r10
	ldr r0, [lr, #880]
	mla r11, r0, r1, r11
	bic r1, r3, r2, lsr #7
	sub r1, r1, #1
	ldr r0, [lr, #896]
	and r0, r0, r1
	orr r4, r4, r0
	ldr r0, [lr, #912]
	and r0, r0, r1
	orr r5, r5, r0
	ldr r0, [lr, #928]
	mla r6, r0, r1, r6
	ldr r0, [lr, #944]
	mla r7, r0, r1, r7
	ldr r0, [lr, #960]
	and r0, r0, r1
	orr r8, r8, r0
	ldr r0, [lr, #976]
	and r0, r0, r1
	orr r9, r9, r0
	ldr r0, [lr, #992]
	mla r10, r0, r1, r10
	ldr r0, [lr, #1008]
	mla r11, r0, r1, r11
	lsr r2, r2, #8
	add lr, lr, #1024
	ldr r0, [r12, #44]
	subs r0, r0, #1
	str r0, [r12, #44]
	bne 29b
	ldr r2, [r12, #36]
	and lr, r2, #7
	lsr r2, r2, #8
	str r2, [r12, #36]
	mov r1, #0
	mov r3, #0
	eor r0, lr, #0
	sub r0, r0, #1
	lsr r0, r0, #31
	mla r1, r4, r0, r1
	eor r0, lr, #1
	sub r0, r0, #1
	lsr r0, r0, #31
	mla r1, r5, r0, r1
	eor r0, lr, #2
	sub r0, r0, #1
	lsr r0, r0, #31
	mla r3, r6, r0, r3
	eor r0, lr, #3
	sub r0, r0, #1
	lsr r0, r0, #31
	mla r3, r7, r0, r3
	eor r0, lr, #4
	sub r0, r0, #1
	lsr r0, r0, #31
	mla r1, r8, r0, r1
	eor r0, lr, #5
	sub r0, r0, #1
	lsr r0, r0, #31
	mla r1, r9, r0, r1
	eor r0, lr, #6
	sub r0, r0, #1
	lsr r0, r0, #31
	mla r3, r10, r0, r3
	eor r0, lr, #7
	sub r0, r0, #1
	lsr r0, r0, #31
	mla r3, r11, r0, r3
	sub r1, r1, r3
	ldr r0, [r12, #56]
	str r0, [r12, #60]
	ldr r0, [r12, #52]
	str r0, [r12, #56]
	ldr r0, [r12, #48]
	str r0, [r12, #52]
	str r1, [r12, #48]
	ldr r0, [r12, #40]
	add r0, r0, #4
	str r0, [r12, #40]
	cmp r0, #16
	bne 28b
	ldr r8, [r12, #60]
	ldr r9, [r12, #56]
	ldr r10, [r12, #52]
	ldr r11, [r12, #48]
	ldr r2, [r12, #24]
	ldr r3, [r12, #28]
	ldr lr, [r12, #32]
	ldr r0, [r12, #20]
	cmp r0, #1
	beq 210f
	cmp r0, #2
	beq 212f
	add r1, r11, r10
	eor r1, r1, r9
	sub r1, r1, r8
	b 213f
212:
	sub r1, r11, r10
	add r1, r1, r9
	eor r1, r1, r8
213:
	b 211f
210:
	eor r1, r11, r10
	sub r1, r1, r9
	add r1, r1, r8
211:
	eor r1, r1, r2
	mov r2, r3
	mov r3, r1
	add lr, lr, #4
	ldr r0, [r12, #20]
	cmp r0, #3
	beq 214f
	add r0, r0, #1
	b 215f
214:
	mov r0, #1
215:
	str r0, [r12, #20]
	ldr r0, [r12, #16]
	subs r0, r0, #1
	str r0, [r12, #16]
	bne 23b
	ldr r0, [r12, #0]
	ldr r1, [r12, #4]
	ldr r4, [r12, #8]
	ldr r5, [r12, #12]
	rev r3, r3
	str r3, [r0, #0]
	rev r2, r2
	str r2, [r0, #4]
	str r0, [r12, #0]
	str r1, [r12, #4]
	str r4, [r12, #8]
	str r5, [r12, #12]
	ldr r0, [r12, #0]
	add r0, r0, #8
	str r0, [r12, #0]
	ldr r0, [r12, #4]
	subs r0, r0, #1
	str r0, [r12, #4]
	bne 22b
	b 21f
20:
21:
	ldr r4, [r12, #64]
	ldr r5, [r12, #68]
	ldr r6, [r12, #72]
	ldr r7, [r12, #76]
	ldr r8, [r12, #80]
	ldr r9, [r12, #84]
	ldr r10, [r12, #88]
	ldr r11, [r12, #92]
	ldr lr, [r12, #96]
	bx lr

vg_cast5_ecb_decrypt:
	ldr r12, [sp, #0]
	str r4, [r12, #64]
	str r5, [r12, #68]
	str r6, [r12, #72]
	str r7, [r12, #76]
	str r8, [r12, #80]
	str r9, [r12, #84]
	str r10, [r12, #88]
	str r11, [r12, #92]
	str lr, [r12, #96]
	str r2, [r12, #0]
	str r3, [r12, #4]
	str r0, [r12, #8]
	str r1, [r12, #12]
	cmp r3, #0
	beq 20f
22:
	ldr r0, [r12, #0]
	ldr r2, [r0, #0]
	rev r2, r2
	ldr r3, [r0, #4]
	rev r3, r3
	ldr lr, [r12, #8]
	ldr r1, [r12, #12]
	str r1, [r12, #16]
	add lr, lr, r1, lsl #2
	sub lr, lr, #4
	lsr r0, r1, #1
	movw r1, #9
	sub r1, r1, r0
	str r1, [r12, #20]
23:
	ldr r0, [r12, #20]
	cmp r0, #1
	beq 24f
	cmp r0, #2
	beq 26f
	ldr r1, [lr, #0]
	sub r1, r1, r3
	b 27f
26:
	ldr r1, [lr, #0]
	eor r1, r1, r3
27:
	b 25f
24:
	ldr r1, [lr, #0]
	add r1, r1, r3
25:
	ldr r0, [lr, #64]
	and r4, r0, #1
	sub r4, r4, #1
	ror r5, r1, #31
	eor r1, r1, r5
	and r1, r1, r4
	eor r1, r1, r5
	lsr r0, r0, #1
	and r4, r0, #1
	sub r4, r4, #1
	ror r5, r1, #30
	eor r1, r1, r5
	and r1, r1, r4
	eor r1, r1, r5
	lsr r0, r0, #1
	and r4, r0, #1
	sub r4, r4, #1
	ror r5, r1, #28
	eor r1, r1, r5
	and r1, r1, r4
	eor r1, r1, r5
	lsr r0, r0, #1
	and r4, r0, #1
	sub r4, r4, #1
	ror r5, r1, #24
	eor r1, r1, r5
	and r1, r1, r4
	eor r1, r1, r5
	lsr r0, r0, #1
	and r4, r0, #1
	sub r4, r4, #1
	ror r5, r1, #16
	eor r1, r1, r5
	and r1, r1, r4
	eor r1, r1, r5
	and r4, r1, #255
	lsr r5, r1, #8
	and r5, r5, #255
	lsr r6, r1, #16
	and r6, r6, #255
	lsr r7, r1, #24
	str r2, [r12, #24]
	str r3, [r12, #28]
	str lr, [r12, #32]
	add r4, r4, r5, lsl #8
	add r4, r4, r6, lsl #16
	add r4, r4, r7, lsl #24
	str r4, [r12, #36]
	mov r0, #0
	str r0, [r12, #40]
28:
	ldr r0, [r12, #36]
	and r0, r0, #255
	mov r3, #1
	and r1, r3, r0, lsr #3
	add r2, r3, r1
	and r1, r3, r0, lsr #4
	add lr, r3, r1, lsl #2
	sub lr, lr, r1
	mul r2, r2, lr
	and r1, r3, r0, lsr #5
	add lr, r3, r1, lsl #4
	sub lr, lr, r1
	mul r2, r2, lr
	and r1, r3, r0, lsr #6
	add lr, r3, r1, lsl #8
	sub lr, lr, r1
	mul r2, r2, lr
	and r1, r3, r0, lsr #7
	add lr, r3, r1, lsl #16
	sub lr, lr, r1
	mul r2, r2, lr
	mov r4, #0
	mov r5, #0
	mov r6, #0
	mov r7, #0
	mov r8, #0
	mov r9, #0
	mov r10, #0
	mov r11, #0
	movw lr, #:lower16:({VG_CAST5_S1234}
	movt lr, #:upper16:({VG_CAST5_S1234}
2:
	add lr, pc
3:
	ldr r0, [r12, #40]
	add lr, lr, r0
	mov r0, #4
	str r0, [r12, #44]
29:
	bic r1, r3, r2
	sub r1, r1, #1
	ldr r0, [lr, #0]
	and r0, r0, r1
	orr r4, r4, r0
	ldr r0, [lr, #16]
	and r0, r0, r1
	orr r5, r5, r0
	ldr r0, [lr, #32]
	mla r6, r0, r1, r6
	ldr r0, [lr, #48]
	mla r7, r0, r1, r7
	ldr r0, [lr, #64]
	and r0, r0, r1
	orr r8, r8, r0
	ldr r0, [lr, #80]
	and r0, r0, r1
	orr r9, r9, r0
	ldr r0, [lr, #96]
	mla r10, r0, r1, r10
	ldr r0, [lr, #112]
	mla r11, r0, r1, r11
	bic r1, r3, r2, lsr #1
	sub r1, r1, #1
	ldr r0, [lr, #128]
	and r0, r0, r1
	orr r4, r4, r0
	ldr r0, [lr, #144]
	and r0, r0, r1
	orr r5, r5, r0
	ldr r0, [lr, #160]
	mla r6, r0, r1, r6
	ldr r0, [lr, #176]
	mla r7, r0, r1, r7
	ldr r0, [lr, #192]
	and r0, r0, r1
	orr r8, r8, r0
	ldr r0, [lr, #208]
	and r0, r0, r1
	orr r9, r9, r0
	ldr r0, [lr, #224]
	mla r10, r0, r1, r10
	ldr r0, [lr, #240]
	mla r11, r0, r1, r11
	bic r1, r3, r2, lsr #2
	sub r1, r1, #1
	ldr r0, [lr, #256]
	and r0, r0, r1
	orr r4, r4, r0
	ldr r0, [lr, #272]
	and r0, r0, r1
	orr r5, r5, r0
	ldr r0, [lr, #288]
	mla r6, r0, r1, r6
	ldr r0, [lr, #304]
	mla r7, r0, r1, r7
	ldr r0, [lr, #320]
	and r0, r0, r1
	orr r8, r8, r0
	ldr r0, [lr, #336]
	and r0, r0, r1
	orr r9, r9, r0
	ldr r0, [lr, #352]
	mla r10, r0, r1, r10
	ldr r0, [lr, #368]
	mla r11, r0, r1, r11
	bic r1, r3, r2, lsr #3
	sub r1, r1, #1
	ldr r0, [lr, #384]
	and r0, r0, r1
	orr r4, r4, r0
	ldr r0, [lr, #400]
	and r0, r0, r1
	orr r5, r5, r0
	ldr r0, [lr, #416]
	mla r6, r0, r1, r6
	ldr r0, [lr, #432]
	mla r7, r0, r1, r7
	ldr r0, [lr, #448]
	and r0, r0, r1
	orr r8, r8, r0
	ldr r0, [lr, #464]
	and r0, r0, r1
	orr r9, r9, r0
	ldr r0, [lr, #480]
	mla r10, r0, r1, r10
	ldr r0, [lr, #496]
	mla r11, r0, r1, r11
	bic r1, r3, r2, lsr #4
	sub r1, r1, #1
	ldr r0, [lr, #512]
	and r0, r0, r1
	orr r4, r4, r0
	ldr r0, [lr, #528]
	and r0, r0, r1
	orr r5, r5, r0
	ldr r0, [lr, #544]
	mla r6, r0, r1, r6
	ldr r0, [lr, #560]
	mla r7, r0, r1, r7
	ldr r0, [lr, #576]
	and r0, r0, r1
	orr r8, r8, r0
	ldr r0, [lr, #592]
	and r0, r0, r1
	orr r9, r9, r0
	ldr r0, [lr, #608]
	mla r10, r0, r1, r10
	ldr r0, [lr, #624]
	mla r11, r0, r1, r11
	bic r1, r3, r2, lsr #5
	sub r1, r1, #1
	ldr r0, [lr, #640]
	and r0, r0, r1
	orr r4, r4, r0
	ldr r0, [lr, #656]
	and r0, r0, r1
	orr r5, r5, r0
	ldr r0, [lr, #672]
	mla r6, r0, r1, r6
	ldr r0, [lr, #688]
	mla r7, r0, r1, r7
	ldr r0, [lr, #704]
	and r0, r0, r1
	orr r8, r8, r0
	ldr r0, [lr, #720]
	and r0, r0, r1
	orr r9, r9, r0
	ldr r0, [lr, #736]
	mla r10, r0, r1, r10
	ldr r0, [lr, #752]
	mla r11, r0, r1, r11
	bic r1, r3, r2, lsr #6
	sub r1, r1, #1
	ldr r0, [lr, #768]
	and r0, r0, r1
	orr r4, r4, r0
	ldr r0, [lr, #784]
	and r0, r0, r1
	orr r5, r5, r0
	ldr r0, [lr, #800]
	mla r6, r0, r1, r6
	ldr r0, [lr, #816]
	mla r7, r0, r1, r7
	ldr r0, [lr, #832]
	and r0, r0, r1
	orr r8, r8, r0
	ldr r0, [lr, #848]
	and r0, r0, r1
	orr r9, r9, r0
	ldr r0, [lr, #864]
	mla r10, r0, r1, r10
	ldr r0, [lr, #880]
	mla r11, r0, r1, r11
	bic r1, r3, r2, lsr #7
	sub r1, r1, #1
	ldr r0, [lr, #896]
	and r0, r0, r1
	orr r4, r4, r0
	ldr r0, [lr, #912]
	and r0, r0, r1
	orr r5, r5, r0
	ldr r0, [lr, #928]
	mla r6, r0, r1, r6
	ldr r0, [lr, #944]
	mla r7, r0, r1, r7
	ldr r0, [lr, #960]
	and r0, r0, r1
	orr r8, r8, r0
	ldr r0, [lr, #976]
	and r0, r0, r1
	orr r9, r9, r0
	ldr r0, [lr, #992]
	mla r10, r0, r1, r10
	ldr r0, [lr, #1008]
	mla r11, r0, r1, r11
	lsr r2, r2, #8
	add lr, lr, #1024
	ldr r0, [r12, #44]
	subs r0, r0, #1
	str r0, [r12, #44]
	bne 29b
	ldr r2, [r12, #36]
	and lr, r2, #7
	lsr r2, r2, #8
	str r2, [r12, #36]
	mov r1, #0
	mov r3, #0
	eor r0, lr, #0
	sub r0, r0, #1
	lsr r0, r0, #31
	mla r1, r4, r0, r1
	eor r0, lr, #1
	sub r0, r0, #1
	lsr r0, r0, #31
	mla r1, r5, r0, r1
	eor r0, lr, #2
	sub r0, r0, #1
	lsr r0, r0, #31
	mla r3, r6, r0, r3
	eor r0, lr, #3
	sub r0, r0, #1
	lsr r0, r0, #31
	mla r3, r7, r0, r3
	eor r0, lr, #4
	sub r0, r0, #1
	lsr r0, r0, #31
	mla r1, r8, r0, r1
	eor r0, lr, #5
	sub r0, r0, #1
	lsr r0, r0, #31
	mla r1, r9, r0, r1
	eor r0, lr, #6
	sub r0, r0, #1
	lsr r0, r0, #31
	mla r3, r10, r0, r3
	eor r0, lr, #7
	sub r0, r0, #1
	lsr r0, r0, #31
	mla r3, r11, r0, r3
	sub r1, r1, r3
	ldr r0, [r12, #56]
	str r0, [r12, #60]
	ldr r0, [r12, #52]
	str r0, [r12, #56]
	ldr r0, [r12, #48]
	str r0, [r12, #52]
	str r1, [r12, #48]
	ldr r0, [r12, #40]
	add r0, r0, #4
	str r0, [r12, #40]
	cmp r0, #16
	bne 28b
	ldr r8, [r12, #60]
	ldr r9, [r12, #56]
	ldr r10, [r12, #52]
	ldr r11, [r12, #48]
	ldr r2, [r12, #24]
	ldr r3, [r12, #28]
	ldr lr, [r12, #32]
	ldr r0, [r12, #20]
	cmp r0, #1
	beq 210f
	cmp r0, #2
	beq 212f
	add r1, r11, r10
	eor r1, r1, r9
	sub r1, r1, r8
	b 213f
212:
	sub r1, r11, r10
	add r1, r1, r9
	eor r1, r1, r8
213:
	b 211f
210:
	eor r1, r11, r10
	sub r1, r1, r9
	add r1, r1, r8
211:
	eor r1, r1, r2
	mov r2, r3
	mov r3, r1
	sub lr, lr, #4
	ldr r0, [r12, #20]
	cmp r0, #1
	beq 214f
	sub r0, r0, #1
	b 215f
214:
	mov r0, #3
215:
	str r0, [r12, #20]
	ldr r0, [r12, #16]
	subs r0, r0, #1
	str r0, [r12, #16]
	bne 23b
	ldr r0, [r12, #0]
	ldr r1, [r12, #4]
	ldr r4, [r12, #8]
	ldr r5, [r12, #12]
	rev r3, r3
	str r3, [r0, #0]
	rev r2, r2
	str r2, [r0, #4]
	str r0, [r12, #0]
	str r1, [r12, #4]
	str r4, [r12, #8]
	str r5, [r12, #12]
	ldr r0, [r12, #0]
	add r0, r0, #8
	str r0, [r12, #0]
	ldr r0, [r12, #4]
	subs r0, r0, #1
	str r0, [r12, #4]
	bne 22b
	b 21f
20:
21:
	ldr r4, [r12, #64]
	ldr r5, [r12, #68]
	ldr r6, [r12, #72]
	ldr r7, [r12, #76]
	ldr r8, [r12, #80]
	ldr r9, [r12, #84]
	ldr r10, [r12, #88]
	ldr r11, [r12, #92]
	ldr lr, [r12, #96]
	bx lr
