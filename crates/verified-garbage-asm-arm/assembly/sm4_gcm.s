// The functions of `src/sm4_gcm.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_gcm_init:
	sub sp, sp, #768
	add r2, sp, #0
	str r4, [r2, #128]
	str r5, [r2, #132]
	str r6, [r2, #136]
	str r7, [r2, #140]
	str r8, [r2, #144]
	str r9, [r2, #148]
	str r10, [r2, #152]
	str r11, [r2, #156]
	str lr, [r2, #160]
	mov r11, r2
	mov r9, r1
	bl {vg_sm4_expand_key}
	mov r0, #0
	str r0, [r9, #240]
	str r0, [r9, #244]
	str r0, [r9, #248]
	str r0, [r9, #252]
	str r0, [r11, #96]
	str r0, [r11, #100]
	str r0, [r11, #104]
	str r0, [r11, #108]
	mov r0, r9
	add r2, r11, #96
	add r3, r9, #240
	mov r12, #1
	mov r1, r2
	mov r2, r3
	mov r3, r12
	bl {vg_sm4_ctr32}
	ldr r4, [r11, #128]
	ldr r5, [r11, #132]
	ldr r6, [r11, #136]
	ldr r7, [r11, #140]
	ldr r8, [r11, #144]
	ldr r9, [r11, #148]
	ldr r10, [r11, #152]
	ldr lr, [r11, #160]
	ldr r11, [r11, #156]
	add sp, sp, #768
	bx lr

vg_sm4_gcm_seal:
	sub sp, sp, #800
	add r12, sp, #0
	str lr, [r12, #20]
	ldr lr, [sp, #800]
	str lr, [r12, #0]
	ldr lr, [sp, #804]
	str lr, [r12, #4]
	ldr lr, [sp, #808]
	str lr, [r12, #8]
	ldr lr, [sp, #812]
	str lr, [r12, #12]
	add lr, sp, #24
	str lr, [r12, #16]
	ldr lr, [sp, #20]
	ldr r12, [sp, #16]
	str r4, [r12, #128]
	str r5, [r12, #132]
	str r6, [r12, #136]
	str r7, [r12, #140]
	str r8, [r12, #144]
	str r9, [r12, #148]
	str r10, [r12, #152]
	str r11, [r12, #156]
	str lr, [r12, #160]
	mov r11, r12
	add r10, r11, #16
	mov r9, r0
	mov r8, r3
	mov r4, r1
	mov r5, r2
	cmp r5, #12
	beq 20f
	mov r0, #0
	str r0, [r10, #0]
	str r0, [r10, #4]
	str r0, [r10, #8]
	str r0, [r10, #12]
	mov r7, r5
	mov r6, #0
	cmp r5, #0
	beq 22f
	cmp r6, #0
	beq 24f
	mov r3, #16
	sub r3, r3, r6
	cmp r5, r3
	mov r12, #0
	adc r12, r12, #0
	cmp r12, #0
	beq 26f
	b 27f
26:
	mov r3, r5
27:
	add r2, r10, #32
	add r2, r2, r6
	mov r1, r4
	add r4, r4, r3
	sub r5, r5, r3
	add r6, r6, r3
28:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 28b
	cmp r6, #16
	beq 29f
	b 210f
29:
	add r0, r9, #240
	add r1, r10, #0
	add r2, r10, #32
	mov r3, #1
	add r12, r11, #512
	push {r12, lr}
	bl {vg_ghash}
	ldr r12, [sp], #8
210:
	b 25f
24:
25:
	mov r2, r4
	lsr r3, r5, #4
	and r12, r5, #15
	sub r0, r5, r12
	add r4, r4, r0
	mov r5, r12
	cmp r3, #0
	beq 211f
	add r0, r9, #240
	add r1, r10, #0
	add r12, r11, #512
	push {r12, lr}
	bl {vg_ghash}
	ldr r12, [sp], #8
	b 212f
211:
212:
	cmp r5, #0
	beq 213f
	mov r1, r4
	add r2, r10, #32
	mov r3, r5
215:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 215b
	b 214f
213:
214:
	b 23f
22:
23:
	and r6, r7, #15
	cmp r6, #0
	beq 216f
	mov r12, #0
	str r12, [r11, #96]
	str r12, [r11, #100]
	str r12, [r11, #104]
	str r12, [r11, #108]
	add r1, r10, #32
	add r2, r11, #96
	mov r3, r6
218:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 218b
	add r0, r9, #240
	add r1, r10, #0
	add r2, r11, #96
	mov r3, #1
	add r12, r11, #512
	push {r12, lr}
	bl {vg_ghash}
	ldr r12, [sp], #8
	b 217f
216:
217:
	mov r4, #0
	mov r5, #0
	mov r6, r7
	mov r7, #0
	lsl r0, r5, #3
	orr r0, r0, r4, lsr #29
	rev r0, r0
	str r0, [r11, #96]
	lsl r0, r4, #3
	rev r0, r0
	str r0, [r11, #100]
	lsl r0, r7, #3
	orr r0, r0, r6, lsr #29
	rev r0, r0
	str r0, [r11, #104]
	lsl r0, r6, #3
	rev r0, r0
	str r0, [r11, #108]
	add r0, r9, #240
	add r1, r10, #0
	add r2, r11, #96
	mov r3, #1
	add r12, r11, #512
	push {r12, lr}
	bl {vg_ghash}
	ldr r12, [sp], #8
	b 21f
20:
	ldr r0, [r4, #0]
	ldr r1, [r4, #4]
	ldr r2, [r4, #8]
	mov r3, #16777216
	str r0, [r10, #0]
	str r1, [r10, #4]
	str r2, [r10, #8]
	str r3, [r10, #12]
21:
	ldr r0, [r10, #0]
	ldr r1, [r10, #4]
	ldr r2, [r10, #8]
	ldr r3, [r10, #12]
	rev r3, r3
	add r3, r3, #1
	rev r3, r3
	str r0, [r10, #48]
	str r1, [r10, #52]
	str r2, [r10, #56]
	str r3, [r10, #60]
	mov r0, #0
	str r0, [r10, #16]
	str r0, [r10, #20]
	str r0, [r10, #24]
	str r0, [r10, #28]
	mov r4, r8
	ldr r5, [sp, #0]
	mov r6, #0
	cmp r5, #0
	beq 219f
	cmp r6, #0
	beq 221f
	mov r3, #16
	sub r3, r3, r6
	cmp r5, r3
	mov r12, #0
	adc r12, r12, #0
	cmp r12, #0
	beq 223f
	b 224f
223:
	mov r3, r5
224:
	add r2, r10, #32
	add r2, r2, r6
	mov r1, r4
	add r4, r4, r3
	sub r5, r5, r3
	add r6, r6, r3
225:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 225b
	cmp r6, #16
	beq 226f
	b 227f
226:
	add r0, r9, #240
	add r1, r10, #16
	add r2, r10, #32
	mov r3, #1
	add r12, r11, #512
	push {r12, lr}
	bl {vg_ghash}
	ldr r12, [sp], #8
227:
	b 222f
221:
222:
	mov r2, r4
	lsr r3, r5, #4
	and r12, r5, #15
	sub r0, r5, r12
	add r4, r4, r0
	mov r5, r12
	cmp r3, #0
	beq 228f
	add r0, r9, #240
	add r1, r10, #16
	add r12, r11, #512
	push {r12, lr}
	bl {vg_ghash}
	ldr r12, [sp], #8
	b 229f
228:
229:
	cmp r5, #0
	beq 230f
	mov r1, r4
	add r2, r10, #32
	mov r3, r5
232:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 232b
	b 231f
230:
231:
	b 220f
219:
220:
	ldr r6, [sp, #0]
	and r6, r6, #15
	cmp r6, #0
	beq 233f
	mov r12, #0
	str r12, [r11, #96]
	str r12, [r11, #100]
	str r12, [r11, #104]
	str r12, [r11, #108]
	add r1, r10, #32
	add r2, r11, #96
	mov r3, r6
235:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 235b
	add r0, r9, #240
	add r1, r10, #16
	add r2, r11, #96
	mov r3, #1
	add r12, r11, #512
	push {r12, lr}
	bl {vg_ghash}
	ldr r12, [sp], #8
	b 234f
233:
234:
	ldr r4, [sp, #4]
	ldr r5, [sp, #8]
	mov r6, #0
	cmp r5, #0
	beq 236f
	cmp r6, #0
	beq 238f
	mov r3, #16
	sub r3, r3, r6
	cmp r5, r3
	mov r12, #0
	adc r12, r12, #0
	cmp r12, #0
	beq 240f
	b 241f
240:
	mov r3, r5
241:
	add r1, r10, #64
	add r1, r1, r6
	mov r2, r4
	add r4, r4, r3
	sub r5, r5, r3
242:
	ldrb r12, [r2, #0]
	ldrb r0, [r1, #0]
	eor r12, r12, r0
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 242b
	b 239f
238:
239:
	mov r3, r4
	lsr r12, r5, #4
	and r0, r5, #15
	sub r1, r5, r0
	add r4, r4, r1
	mov r5, r0
	cmp r12, #0
	beq 243f
	mov r0, r9
	add r2, r10, #48
	mov r1, r2
	mov r2, r3
	mov r3, r12
	bl {vg_sm4_ctr32}
	b 244f
243:
244:
	cmp r5, #0
	beq 245f
	mov r12, #0
	str r12, [r10, #64]
	str r12, [r10, #68]
	str r12, [r10, #72]
	str r12, [r10, #76]
	mov r0, r9
	add r2, r10, #48
	add r3, r10, #64
	mov r12, #1
	mov r1, r2
	mov r2, r3
	mov r3, r12
	bl {vg_sm4_ctr32}
	add r1, r10, #64
	mov r2, r4
	mov r3, r5
247:
	ldrb r12, [r2, #0]
	ldrb r0, [r1, #0]
	eor r12, r12, r0
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 247b
	b 246f
245:
246:
	b 237f
236:
237:
	ldr r4, [sp, #4]
	ldr r5, [sp, #8]
	mov r6, #0
	cmp r5, #0
	beq 248f
	cmp r6, #0
	beq 250f
	mov r3, #16
	sub r3, r3, r6
	cmp r5, r3
	mov r12, #0
	adc r12, r12, #0
	cmp r12, #0
	beq 252f
	b 253f
252:
	mov r3, r5
253:
	add r2, r10, #32
	add r2, r2, r6
	mov r1, r4
	add r4, r4, r3
	sub r5, r5, r3
	add r6, r6, r3
254:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 254b
	cmp r6, #16
	beq 255f
	b 256f
255:
	add r0, r9, #240
	add r1, r10, #16
	add r2, r10, #32
	mov r3, #1
	add r12, r11, #512
	push {r12, lr}
	bl {vg_ghash}
	ldr r12, [sp], #8
256:
	b 251f
250:
251:
	mov r2, r4
	lsr r3, r5, #4
	and r12, r5, #15
	sub r0, r5, r12
	add r4, r4, r0
	mov r5, r12
	cmp r3, #0
	beq 257f
	add r0, r9, #240
	add r1, r10, #16
	add r12, r11, #512
	push {r12, lr}
	bl {vg_ghash}
	ldr r12, [sp], #8
	b 258f
257:
258:
	cmp r5, #0
	beq 259f
	mov r1, r4
	add r2, r10, #32
	mov r3, r5
261:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 261b
	b 260f
259:
260:
	b 249f
248:
249:
	ldr r6, [sp, #8]
	and r6, r6, #15
	cmp r6, #0
	beq 262f
	mov r12, #0
	str r12, [r11, #96]
	str r12, [r11, #100]
	str r12, [r11, #104]
	str r12, [r11, #108]
	add r1, r10, #32
	add r2, r11, #96
	mov r3, r6
264:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 264b
	add r0, r9, #240
	add r1, r10, #16
	add r2, r11, #96
	mov r3, #1
	add r12, r11, #512
	push {r12, lr}
	bl {vg_ghash}
	ldr r12, [sp], #8
	b 263f
262:
263:
	ldr r4, [sp, #0]
	mov r5, #0
	ldr r6, [sp, #8]
	mov r7, #0
	lsl r0, r5, #3
	orr r0, r0, r4, lsr #29
	rev r0, r0
	str r0, [r11, #96]
	lsl r0, r4, #3
	rev r0, r0
	str r0, [r11, #100]
	lsl r0, r7, #3
	orr r0, r0, r6, lsr #29
	rev r0, r0
	str r0, [r11, #104]
	lsl r0, r6, #3
	rev r0, r0
	str r0, [r11, #108]
	add r0, r9, #240
	add r1, r10, #16
	add r2, r11, #96
	mov r3, #1
	add r12, r11, #512
	push {r12, lr}
	bl {vg_ghash}
	ldr r12, [sp], #8
	ldr r0, [r10, #16]
	str r0, [r11, #0]
	ldr r0, [r10, #20]
	str r0, [r11, #4]
	ldr r0, [r10, #24]
	str r0, [r11, #8]
	ldr r0, [r10, #28]
	str r0, [r11, #12]
	mov r0, r9
	mov r2, r10
	add r3, r11, #0
	mov r12, #1
	mov r1, r2
	mov r2, r3
	mov r3, r12
	bl {vg_sm4_ctr32}
	ldr r1, [sp, #12]
	ldr r0, [r11, #0]
	str r0, [r1, #0]
	ldr r0, [r11, #4]
	str r0, [r1, #4]
	ldr r0, [r11, #8]
	str r0, [r1, #8]
	ldr r0, [r11, #12]
	str r0, [r1, #12]
	ldr r4, [r11, #128]
	ldr r5, [r11, #132]
	ldr r6, [r11, #136]
	ldr r7, [r11, #140]
	ldr r8, [r11, #144]
	ldr r9, [r11, #148]
	ldr r10, [r11, #152]
	ldr lr, [r11, #160]
	ldr r11, [r11, #156]
	add sp, sp, #800
	bx lr

vg_sm4_gcm_open:
	sub sp, sp, #800
	add r12, sp, #0
	str lr, [r12, #24]
	ldr lr, [sp, #800]
	str lr, [r12, #0]
	ldr lr, [sp, #804]
	str lr, [r12, #4]
	ldr lr, [sp, #808]
	str lr, [r12, #8]
	ldr lr, [sp, #812]
	str lr, [r12, #12]
	ldr lr, [sp, #816]
	str lr, [r12, #16]
	add lr, sp, #28
	str lr, [r12, #20]
	ldr lr, [sp, #24]
	ldr r12, [sp, #20]
	str r4, [r12, #128]
	str r5, [r12, #132]
	str r6, [r12, #136]
	str r7, [r12, #140]
	str r8, [r12, #144]
	str r9, [r12, #148]
	str r10, [r12, #152]
	str r11, [r12, #156]
	str lr, [r12, #160]
	mov r11, r12
	add r10, r11, #16
	mov r9, r0
	mov r8, r3
	mov r4, r1
	mov r5, r2
	ldr r6, [sp, #16]
	sub r0, r6, #4
	cmp r0, #13
	mov r0, #0
	adc r0, r0, #0
	cmp r0, #1
	beq 20f
	cmp r5, #12
	beq 22f
	mov r0, #0
	str r0, [r10, #0]
	str r0, [r10, #4]
	str r0, [r10, #8]
	str r0, [r10, #12]
	mov r7, r5
	mov r6, #0
	cmp r5, #0
	beq 24f
	cmp r6, #0
	beq 26f
	mov r3, #16
	sub r3, r3, r6
	cmp r5, r3
	mov r12, #0
	adc r12, r12, #0
	cmp r12, #0
	beq 28f
	b 29f
28:
	mov r3, r5
29:
	add r2, r10, #32
	add r2, r2, r6
	mov r1, r4
	add r4, r4, r3
	sub r5, r5, r3
	add r6, r6, r3
210:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 210b
	cmp r6, #16
	beq 211f
	b 212f
211:
	add r0, r9, #240
	add r1, r10, #0
	add r2, r10, #32
	mov r3, #1
	add r12, r11, #512
	push {r12, lr}
	bl {vg_ghash}
	ldr r12, [sp], #8
212:
	b 27f
26:
27:
	mov r2, r4
	lsr r3, r5, #4
	and r12, r5, #15
	sub r0, r5, r12
	add r4, r4, r0
	mov r5, r12
	cmp r3, #0
	beq 213f
	add r0, r9, #240
	add r1, r10, #0
	add r12, r11, #512
	push {r12, lr}
	bl {vg_ghash}
	ldr r12, [sp], #8
	b 214f
213:
214:
	cmp r5, #0
	beq 215f
	mov r1, r4
	add r2, r10, #32
	mov r3, r5
217:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 217b
	b 216f
215:
216:
	b 25f
24:
25:
	and r6, r7, #15
	cmp r6, #0
	beq 218f
	mov r12, #0
	str r12, [r11, #96]
	str r12, [r11, #100]
	str r12, [r11, #104]
	str r12, [r11, #108]
	add r1, r10, #32
	add r2, r11, #96
	mov r3, r6
220:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 220b
	add r0, r9, #240
	add r1, r10, #0
	add r2, r11, #96
	mov r3, #1
	add r12, r11, #512
	push {r12, lr}
	bl {vg_ghash}
	ldr r12, [sp], #8
	b 219f
218:
219:
	mov r4, #0
	mov r5, #0
	mov r6, r7
	mov r7, #0
	lsl r0, r5, #3
	orr r0, r0, r4, lsr #29
	rev r0, r0
	str r0, [r11, #96]
	lsl r0, r4, #3
	rev r0, r0
	str r0, [r11, #100]
	lsl r0, r7, #3
	orr r0, r0, r6, lsr #29
	rev r0, r0
	str r0, [r11, #104]
	lsl r0, r6, #3
	rev r0, r0
	str r0, [r11, #108]
	add r0, r9, #240
	add r1, r10, #0
	add r2, r11, #96
	mov r3, #1
	add r12, r11, #512
	push {r12, lr}
	bl {vg_ghash}
	ldr r12, [sp], #8
	b 23f
22:
	ldr r0, [r4, #0]
	ldr r1, [r4, #4]
	ldr r2, [r4, #8]
	mov r3, #16777216
	str r0, [r10, #0]
	str r1, [r10, #4]
	str r2, [r10, #8]
	str r3, [r10, #12]
23:
	ldr r0, [r10, #0]
	ldr r1, [r10, #4]
	ldr r2, [r10, #8]
	ldr r3, [r10, #12]
	rev r3, r3
	add r3, r3, #1
	rev r3, r3
	str r0, [r10, #48]
	str r1, [r10, #52]
	str r2, [r10, #56]
	str r3, [r10, #60]
	mov r0, #0
	str r0, [r10, #16]
	str r0, [r10, #20]
	str r0, [r10, #24]
	str r0, [r10, #28]
	mov r4, r8
	ldr r5, [sp, #0]
	mov r6, #0
	cmp r5, #0
	beq 221f
	cmp r6, #0
	beq 223f
	mov r3, #16
	sub r3, r3, r6
	cmp r5, r3
	mov r12, #0
	adc r12, r12, #0
	cmp r12, #0
	beq 225f
	b 226f
225:
	mov r3, r5
226:
	add r2, r10, #32
	add r2, r2, r6
	mov r1, r4
	add r4, r4, r3
	sub r5, r5, r3
	add r6, r6, r3
227:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 227b
	cmp r6, #16
	beq 228f
	b 229f
228:
	add r0, r9, #240
	add r1, r10, #16
	add r2, r10, #32
	mov r3, #1
	add r12, r11, #512
	push {r12, lr}
	bl {vg_ghash}
	ldr r12, [sp], #8
229:
	b 224f
223:
224:
	mov r2, r4
	lsr r3, r5, #4
	and r12, r5, #15
	sub r0, r5, r12
	add r4, r4, r0
	mov r5, r12
	cmp r3, #0
	beq 230f
	add r0, r9, #240
	add r1, r10, #16
	add r12, r11, #512
	push {r12, lr}
	bl {vg_ghash}
	ldr r12, [sp], #8
	b 231f
230:
231:
	cmp r5, #0
	beq 232f
	mov r1, r4
	add r2, r10, #32
	mov r3, r5
234:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 234b
	b 233f
232:
233:
	b 222f
221:
222:
	ldr r6, [sp, #0]
	and r6, r6, #15
	cmp r6, #0
	beq 235f
	mov r12, #0
	str r12, [r11, #96]
	str r12, [r11, #100]
	str r12, [r11, #104]
	str r12, [r11, #108]
	add r1, r10, #32
	add r2, r11, #96
	mov r3, r6
237:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 237b
	add r0, r9, #240
	add r1, r10, #16
	add r2, r11, #96
	mov r3, #1
	add r12, r11, #512
	push {r12, lr}
	bl {vg_ghash}
	ldr r12, [sp], #8
	b 236f
235:
236:
	ldr r4, [sp, #4]
	ldr r5, [sp, #8]
	mov r6, #0
	cmp r5, #0
	beq 238f
	cmp r6, #0
	beq 240f
	mov r3, #16
	sub r3, r3, r6
	cmp r5, r3
	mov r12, #0
	adc r12, r12, #0
	cmp r12, #0
	beq 242f
	b 243f
242:
	mov r3, r5
243:
	add r2, r10, #32
	add r2, r2, r6
	mov r1, r4
	add r4, r4, r3
	sub r5, r5, r3
	add r6, r6, r3
244:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 244b
	cmp r6, #16
	beq 245f
	b 246f
245:
	add r0, r9, #240
	add r1, r10, #16
	add r2, r10, #32
	mov r3, #1
	add r12, r11, #512
	push {r12, lr}
	bl {vg_ghash}
	ldr r12, [sp], #8
246:
	b 241f
240:
241:
	mov r2, r4
	lsr r3, r5, #4
	and r12, r5, #15
	sub r0, r5, r12
	add r4, r4, r0
	mov r5, r12
	cmp r3, #0
	beq 247f
	add r0, r9, #240
	add r1, r10, #16
	add r12, r11, #512
	push {r12, lr}
	bl {vg_ghash}
	ldr r12, [sp], #8
	b 248f
247:
248:
	cmp r5, #0
	beq 249f
	mov r1, r4
	add r2, r10, #32
	mov r3, r5
251:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 251b
	b 250f
249:
250:
	b 239f
238:
239:
	ldr r6, [sp, #8]
	and r6, r6, #15
	cmp r6, #0
	beq 252f
	mov r12, #0
	str r12, [r11, #96]
	str r12, [r11, #100]
	str r12, [r11, #104]
	str r12, [r11, #108]
	add r1, r10, #32
	add r2, r11, #96
	mov r3, r6
254:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 254b
	add r0, r9, #240
	add r1, r10, #16
	add r2, r11, #96
	mov r3, #1
	add r12, r11, #512
	push {r12, lr}
	bl {vg_ghash}
	ldr r12, [sp], #8
	b 253f
252:
253:
	ldr r4, [sp, #0]
	mov r5, #0
	ldr r6, [sp, #8]
	mov r7, #0
	lsl r0, r5, #3
	orr r0, r0, r4, lsr #29
	rev r0, r0
	str r0, [r11, #96]
	lsl r0, r4, #3
	rev r0, r0
	str r0, [r11, #100]
	lsl r0, r7, #3
	orr r0, r0, r6, lsr #29
	rev r0, r0
	str r0, [r11, #104]
	lsl r0, r6, #3
	rev r0, r0
	str r0, [r11, #108]
	add r0, r9, #240
	add r1, r10, #16
	add r2, r11, #96
	mov r3, #1
	add r12, r11, #512
	push {r12, lr}
	bl {vg_ghash}
	ldr r12, [sp], #8
	ldr r0, [r10, #16]
	str r0, [r11, #112]
	ldr r0, [r10, #20]
	str r0, [r11, #116]
	ldr r0, [r10, #24]
	str r0, [r11, #120]
	ldr r0, [r10, #28]
	str r0, [r11, #124]
	mov r0, r9
	mov r2, r10
	add r3, r11, #112
	mov r12, #1
	mov r1, r2
	mov r2, r3
	mov r3, r12
	bl {vg_sm4_ctr32}
	ldr r6, [sp, #16]
	ldr r1, [sp, #12]
	mov r0, #0
	str r0, [r11, #256]
	str r0, [r11, #260]
	str r0, [r11, #264]
	str r0, [r11, #268]
	add r2, r11, #256
	mov r3, r6
255:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 255b
	mov r0, #0
	str r0, [r11, #240]
	str r0, [r11, #244]
	str r0, [r11, #248]
	str r0, [r11, #252]
	add r1, r11, #112
	add r2, r11, #240
	mov r3, r6
256:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 256b
	ldr r0, [r11, #240]
	ldr r2, [r11, #256]
	eor r0, r0, r2
	ldr r1, [r11, #244]
	ldr r2, [r11, #260]
	eor r1, r1, r2
	orr r0, r0, r1
	ldr r1, [r11, #248]
	ldr r2, [r11, #264]
	eor r1, r1, r2
	orr r0, r0, r1
	ldr r1, [r11, #252]
	ldr r2, [r11, #268]
	eor r1, r1, r2
	orr r0, r0, r1
	mov r1, #0
	sub r1, r1, r0
	orr r0, r0, r1
	lsr r0, r0, #31
	mov r1, #1
	sub r0, r1, r0
	mov r7, r0
	cmp r0, #0
	beq 257f
	ldr r4, [sp, #4]
	ldr r5, [sp, #8]
	mov r6, #0
	cmp r5, #0
	beq 259f
	cmp r6, #0
	beq 261f
	mov r3, #16
	sub r3, r3, r6
	cmp r5, r3
	mov r12, #0
	adc r12, r12, #0
	cmp r12, #0
	beq 263f
	b 264f
263:
	mov r3, r5
264:
	add r1, r10, #64
	add r1, r1, r6
	mov r2, r4
	add r4, r4, r3
	sub r5, r5, r3
265:
	ldrb r12, [r2, #0]
	ldrb r0, [r1, #0]
	eor r12, r12, r0
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 265b
	b 262f
261:
262:
	mov r3, r4
	lsr r12, r5, #4
	and r0, r5, #15
	sub r1, r5, r0
	add r4, r4, r1
	mov r5, r0
	cmp r12, #0
	beq 266f
	mov r0, r9
	add r2, r10, #48
	mov r1, r2
	mov r2, r3
	mov r3, r12
	bl {vg_sm4_ctr32}
	b 267f
266:
267:
	cmp r5, #0
	beq 268f
	mov r12, #0
	str r12, [r10, #64]
	str r12, [r10, #68]
	str r12, [r10, #72]
	str r12, [r10, #76]
	mov r0, r9
	add r2, r10, #48
	add r3, r10, #64
	mov r12, #1
	mov r1, r2
	mov r2, r3
	mov r3, r12
	bl {vg_sm4_ctr32}
	add r1, r10, #64
	mov r2, r4
	mov r3, r5
270:
	ldrb r12, [r2, #0]
	ldrb r0, [r1, #0]
	eor r12, r12, r0
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 270b
	b 269f
268:
269:
	b 260f
259:
260:
	b 258f
257:
258:
	mov r0, r7
	b 21f
20:
	mov r0, #0
21:
	ldr r4, [r11, #128]
	ldr r5, [r11, #132]
	ldr r6, [r11, #136]
	ldr r7, [r11, #140]
	ldr r8, [r11, #144]
	ldr r9, [r11, #148]
	ldr r10, [r11, #152]
	ldr lr, [r11, #160]
	ldr r11, [r11, #156]
	add sp, sp, #800
	bx lr

vg_sm4_gcm_stream_init:
	sub sp, sp, #784
	add r12, sp, #0
	str lr, [r12, #4]
	add lr, sp, #8
	str lr, [r12, #0]
	ldr lr, [sp, #4]
	ldr r12, [sp, #0]
	str r4, [r12, #128]
	str r5, [r12, #132]
	str r6, [r12, #136]
	str r7, [r12, #140]
	str r8, [r12, #144]
	str r9, [r12, #148]
	str r10, [r12, #152]
	str r11, [r12, #156]
	str lr, [r12, #160]
	mov r11, r12
	mov r10, r3
	mov r9, r0
	mov r4, r1
	mov r5, r2
	cmp r5, #12
	beq 20f
	mov r0, #0
	str r0, [r10, #0]
	str r0, [r10, #4]
	str r0, [r10, #8]
	str r0, [r10, #12]
	mov r7, r5
	mov r6, #0
	cmp r5, #0
	beq 22f
	cmp r6, #0
	beq 24f
	mov r3, #16
	sub r3, r3, r6
	cmp r5, r3
	mov r12, #0
	adc r12, r12, #0
	cmp r12, #0
	beq 26f
	b 27f
26:
	mov r3, r5
27:
	add r2, r10, #32
	add r2, r2, r6
	mov r1, r4
	add r4, r4, r3
	sub r5, r5, r3
	add r6, r6, r3
28:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 28b
	cmp r6, #16
	beq 29f
	b 210f
29:
	add r0, r9, #240
	add r1, r10, #0
	add r2, r10, #32
	mov r3, #1
	add r12, r11, #512
	push {r12, lr}
	bl {vg_ghash}
	ldr r12, [sp], #8
210:
	b 25f
24:
25:
	mov r2, r4
	lsr r3, r5, #4
	and r12, r5, #15
	sub r0, r5, r12
	add r4, r4, r0
	mov r5, r12
	cmp r3, #0
	beq 211f
	add r0, r9, #240
	add r1, r10, #0
	add r12, r11, #512
	push {r12, lr}
	bl {vg_ghash}
	ldr r12, [sp], #8
	b 212f
211:
212:
	cmp r5, #0
	beq 213f
	mov r1, r4
	add r2, r10, #32
	mov r3, r5
215:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 215b
	b 214f
213:
214:
	b 23f
22:
23:
	and r6, r7, #15
	cmp r6, #0
	beq 216f
	mov r12, #0
	str r12, [r11, #96]
	str r12, [r11, #100]
	str r12, [r11, #104]
	str r12, [r11, #108]
	add r1, r10, #32
	add r2, r11, #96
	mov r3, r6
218:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 218b
	add r0, r9, #240
	add r1, r10, #0
	add r2, r11, #96
	mov r3, #1
	add r12, r11, #512
	push {r12, lr}
	bl {vg_ghash}
	ldr r12, [sp], #8
	b 217f
216:
217:
	mov r4, #0
	mov r5, #0
	mov r6, r7
	mov r7, #0
	lsl r0, r5, #3
	orr r0, r0, r4, lsr #29
	rev r0, r0
	str r0, [r11, #96]
	lsl r0, r4, #3
	rev r0, r0
	str r0, [r11, #100]
	lsl r0, r7, #3
	orr r0, r0, r6, lsr #29
	rev r0, r0
	str r0, [r11, #104]
	lsl r0, r6, #3
	rev r0, r0
	str r0, [r11, #108]
	add r0, r9, #240
	add r1, r10, #0
	add r2, r11, #96
	mov r3, #1
	add r12, r11, #512
	push {r12, lr}
	bl {vg_ghash}
	ldr r12, [sp], #8
	b 21f
20:
	ldr r0, [r4, #0]
	ldr r1, [r4, #4]
	ldr r2, [r4, #8]
	mov r3, #16777216
	str r0, [r10, #0]
	str r1, [r10, #4]
	str r2, [r10, #8]
	str r3, [r10, #12]
21:
	ldr r0, [r10, #0]
	ldr r1, [r10, #4]
	ldr r2, [r10, #8]
	ldr r3, [r10, #12]
	rev r3, r3
	add r3, r3, #1
	rev r3, r3
	str r0, [r10, #48]
	str r1, [r10, #52]
	str r2, [r10, #56]
	str r3, [r10, #60]
	mov r0, #0
	str r0, [r10, #16]
	str r0, [r10, #20]
	str r0, [r10, #24]
	str r0, [r10, #28]
	ldr r4, [r11, #128]
	ldr r5, [r11, #132]
	ldr r6, [r11, #136]
	ldr r7, [r11, #140]
	ldr r8, [r11, #144]
	ldr r9, [r11, #148]
	ldr r10, [r11, #152]
	ldr lr, [r11, #160]
	ldr r11, [r11, #156]
	add sp, sp, #784
	bx lr

vg_sm4_gcm_stream_aad:
	sub sp, sp, #784
	add r12, sp, #0
	str lr, [r12, #12]
	ldr lr, [sp, #784]
	str lr, [r12, #0]
	ldr lr, [sp, #788]
	str lr, [r12, #4]
	add lr, sp, #16
	str lr, [r12, #8]
	ldr lr, [sp, #12]
	ldr r12, [sp, #8]
	str r4, [r12, #128]
	str r5, [r12, #132]
	str r6, [r12, #136]
	str r7, [r12, #140]
	str r8, [r12, #144]
	str r9, [r12, #148]
	str r10, [r12, #152]
	str r11, [r12, #156]
	str lr, [r12, #160]
	mov r11, r12
	mov r10, r1
	mov r9, r0
	ldr r4, [sp, #0]
	ldr r5, [sp, #4]
	and r6, r2, #15
	cmp r5, #0
	beq 20f
	cmp r6, #0
	beq 22f
	mov r3, #16
	sub r3, r3, r6
	cmp r5, r3
	mov r12, #0
	adc r12, r12, #0
	cmp r12, #0
	beq 24f
	b 25f
24:
	mov r3, r5
25:
	add r2, r10, #32
	add r2, r2, r6
	mov r1, r4
	add r4, r4, r3
	sub r5, r5, r3
	add r6, r6, r3
26:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 26b
	cmp r6, #16
	beq 27f
	b 28f
27:
	add r0, r9, #240
	add r1, r10, #16
	add r2, r10, #32
	mov r3, #1
	add r12, r11, #512
	push {r12, lr}
	bl {vg_ghash}
	ldr r12, [sp], #8
28:
	b 23f
22:
23:
	mov r2, r4
	lsr r3, r5, #4
	and r12, r5, #15
	sub r0, r5, r12
	add r4, r4, r0
	mov r5, r12
	cmp r3, #0
	beq 29f
	add r0, r9, #240
	add r1, r10, #16
	add r12, r11, #512
	push {r12, lr}
	bl {vg_ghash}
	ldr r12, [sp], #8
	b 210f
29:
210:
	cmp r5, #0
	beq 211f
	mov r1, r4
	add r2, r10, #32
	mov r3, r5
213:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 213b
	b 212f
211:
212:
	b 21f
20:
21:
	ldr r4, [r11, #128]
	ldr r5, [r11, #132]
	ldr r6, [r11, #136]
	ldr r7, [r11, #140]
	ldr r8, [r11, #144]
	ldr r9, [r11, #148]
	ldr r10, [r11, #152]
	ldr lr, [r11, #160]
	ldr r11, [r11, #156]
	add sp, sp, #784
	bx lr

vg_sm4_gcm_stream_encrypt:
	sub sp, sp, #800
	add r12, sp, #0
	str lr, [r12, #20]
	ldr lr, [sp, #800]
	str lr, [r12, #0]
	ldr lr, [sp, #804]
	str lr, [r12, #4]
	ldr lr, [sp, #808]
	str lr, [r12, #8]
	ldr lr, [sp, #812]
	str lr, [r12, #12]
	add lr, sp, #24
	str lr, [r12, #16]
	ldr lr, [sp, #20]
	ldr r12, [sp, #16]
	str r4, [r12, #128]
	str r5, [r12, #132]
	str r6, [r12, #136]
	str r7, [r12, #140]
	str r8, [r12, #144]
	str r9, [r12, #148]
	str r10, [r12, #152]
	str r11, [r12, #156]
	str lr, [r12, #160]
	mov r11, r12
	mov r10, r1
	mov r9, r0
	mov r8, r2
	ldr r4, [sp, #8]
	ldr r5, [sp, #12]
	ldr r6, [sp, #0]
	and r6, r6, #15
	cmp r5, #0
	beq 20f
	cmp r6, #0
	beq 22f
	mov r3, #16
	sub r3, r3, r6
	cmp r5, r3
	mov r12, #0
	adc r12, r12, #0
	cmp r12, #0
	beq 24f
	b 25f
24:
	mov r3, r5
25:
	add r1, r10, #64
	add r1, r1, r6
	mov r2, r4
	add r4, r4, r3
	sub r5, r5, r3
26:
	ldrb r12, [r2, #0]
	ldrb r0, [r1, #0]
	eor r12, r12, r0
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 26b
	b 23f
22:
23:
	mov r3, r4
	lsr r12, r5, #4
	and r0, r5, #15
	sub r1, r5, r0
	add r4, r4, r1
	mov r5, r0
	cmp r12, #0
	beq 27f
	mov r0, r9
	add r2, r10, #48
	mov r1, r2
	mov r2, r3
	mov r3, r12
	bl {vg_sm4_ctr32}
	b 28f
27:
28:
	cmp r5, #0
	beq 29f
	mov r12, #0
	str r12, [r10, #64]
	str r12, [r10, #68]
	str r12, [r10, #72]
	str r12, [r10, #76]
	mov r0, r9
	add r2, r10, #48
	add r3, r10, #64
	mov r12, #1
	mov r1, r2
	mov r2, r3
	mov r3, r12
	bl {vg_sm4_ctr32}
	add r1, r10, #64
	mov r2, r4
	mov r3, r5
211:
	ldrb r12, [r2, #0]
	ldrb r0, [r1, #0]
	eor r12, r12, r0
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 211b
	b 210f
29:
210:
	b 21f
20:
21:
	ldr r5, [sp, #12]
	cmp r5, #0
	beq 212f
	ldr r0, [sp, #0]
	ldr r1, [sp, #4]
	orr r0, r0, r1
	cmp r0, #0
	beq 214f
	b 215f
214:
	and r6, r8, #15
	cmp r6, #0
	beq 216f
	mov r12, #0
	str r12, [r11, #96]
	str r12, [r11, #100]
	str r12, [r11, #104]
	str r12, [r11, #108]
	add r1, r10, #32
	add r2, r11, #96
	mov r3, r6
218:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 218b
	add r0, r9, #240
	add r1, r10, #16
	add r2, r11, #96
	mov r3, #1
	add r12, r11, #512
	push {r12, lr}
	bl {vg_ghash}
	ldr r12, [sp], #8
	b 217f
216:
217:
215:
	ldr r4, [sp, #8]
	ldr r5, [sp, #12]
	ldr r6, [sp, #0]
	and r6, r6, #15
	cmp r5, #0
	beq 219f
	cmp r6, #0
	beq 221f
	mov r3, #16
	sub r3, r3, r6
	cmp r5, r3
	mov r12, #0
	adc r12, r12, #0
	cmp r12, #0
	beq 223f
	b 224f
223:
	mov r3, r5
224:
	add r2, r10, #32
	add r2, r2, r6
	mov r1, r4
	add r4, r4, r3
	sub r5, r5, r3
	add r6, r6, r3
225:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 225b
	cmp r6, #16
	beq 226f
	b 227f
226:
	add r0, r9, #240
	add r1, r10, #16
	add r2, r10, #32
	mov r3, #1
	add r12, r11, #512
	push {r12, lr}
	bl {vg_ghash}
	ldr r12, [sp], #8
227:
	b 222f
221:
222:
	mov r2, r4
	lsr r3, r5, #4
	and r12, r5, #15
	sub r0, r5, r12
	add r4, r4, r0
	mov r5, r12
	cmp r3, #0
	beq 228f
	add r0, r9, #240
	add r1, r10, #16
	add r12, r11, #512
	push {r12, lr}
	bl {vg_ghash}
	ldr r12, [sp], #8
	b 229f
228:
229:
	cmp r5, #0
	beq 230f
	mov r1, r4
	add r2, r10, #32
	mov r3, r5
232:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 232b
	b 231f
230:
231:
	b 220f
219:
220:
	b 213f
212:
213:
	ldr r4, [r11, #128]
	ldr r5, [r11, #132]
	ldr r6, [r11, #136]
	ldr r7, [r11, #140]
	ldr r8, [r11, #144]
	ldr r9, [r11, #148]
	ldr r10, [r11, #152]
	ldr lr, [r11, #160]
	ldr r11, [r11, #156]
	add sp, sp, #800
	bx lr

vg_sm4_gcm_stream_decrypt:
	sub sp, sp, #800
	add r12, sp, #0
	str lr, [r12, #20]
	ldr lr, [sp, #800]
	str lr, [r12, #0]
	ldr lr, [sp, #804]
	str lr, [r12, #4]
	ldr lr, [sp, #808]
	str lr, [r12, #8]
	ldr lr, [sp, #812]
	str lr, [r12, #12]
	add lr, sp, #24
	str lr, [r12, #16]
	ldr lr, [sp, #20]
	ldr r12, [sp, #16]
	str r4, [r12, #128]
	str r5, [r12, #132]
	str r6, [r12, #136]
	str r7, [r12, #140]
	str r8, [r12, #144]
	str r9, [r12, #148]
	str r10, [r12, #152]
	str r11, [r12, #156]
	str lr, [r12, #160]
	mov r11, r12
	mov r10, r1
	mov r9, r0
	mov r8, r2
	ldr r5, [sp, #12]
	cmp r5, #0
	beq 20f
	ldr r0, [sp, #0]
	ldr r1, [sp, #4]
	orr r0, r0, r1
	cmp r0, #0
	beq 22f
	b 23f
22:
	and r6, r8, #15
	cmp r6, #0
	beq 24f
	mov r12, #0
	str r12, [r11, #96]
	str r12, [r11, #100]
	str r12, [r11, #104]
	str r12, [r11, #108]
	add r1, r10, #32
	add r2, r11, #96
	mov r3, r6
26:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 26b
	add r0, r9, #240
	add r1, r10, #16
	add r2, r11, #96
	mov r3, #1
	add r12, r11, #512
	push {r12, lr}
	bl {vg_ghash}
	ldr r12, [sp], #8
	b 25f
24:
25:
23:
	ldr r4, [sp, #8]
	ldr r5, [sp, #12]
	ldr r6, [sp, #0]
	and r6, r6, #15
	cmp r5, #0
	beq 27f
	cmp r6, #0
	beq 29f
	mov r3, #16
	sub r3, r3, r6
	cmp r5, r3
	mov r12, #0
	adc r12, r12, #0
	cmp r12, #0
	beq 211f
	b 212f
211:
	mov r3, r5
212:
	add r2, r10, #32
	add r2, r2, r6
	mov r1, r4
	add r4, r4, r3
	sub r5, r5, r3
	add r6, r6, r3
213:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 213b
	cmp r6, #16
	beq 214f
	b 215f
214:
	add r0, r9, #240
	add r1, r10, #16
	add r2, r10, #32
	mov r3, #1
	add r12, r11, #512
	push {r12, lr}
	bl {vg_ghash}
	ldr r12, [sp], #8
215:
	b 210f
29:
210:
	mov r2, r4
	lsr r3, r5, #4
	and r12, r5, #15
	sub r0, r5, r12
	add r4, r4, r0
	mov r5, r12
	cmp r3, #0
	beq 216f
	add r0, r9, #240
	add r1, r10, #16
	add r12, r11, #512
	push {r12, lr}
	bl {vg_ghash}
	ldr r12, [sp], #8
	b 217f
216:
217:
	cmp r5, #0
	beq 218f
	mov r1, r4
	add r2, r10, #32
	mov r3, r5
220:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 220b
	b 219f
218:
219:
	b 28f
27:
28:
	b 21f
20:
21:
	ldr r4, [sp, #8]
	ldr r5, [sp, #12]
	ldr r6, [sp, #0]
	and r6, r6, #15
	cmp r5, #0
	beq 221f
	cmp r6, #0
	beq 223f
	mov r3, #16
	sub r3, r3, r6
	cmp r5, r3
	mov r12, #0
	adc r12, r12, #0
	cmp r12, #0
	beq 225f
	b 226f
225:
	mov r3, r5
226:
	add r1, r10, #64
	add r1, r1, r6
	mov r2, r4
	add r4, r4, r3
	sub r5, r5, r3
227:
	ldrb r12, [r2, #0]
	ldrb r0, [r1, #0]
	eor r12, r12, r0
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 227b
	b 224f
223:
224:
	mov r3, r4
	lsr r12, r5, #4
	and r0, r5, #15
	sub r1, r5, r0
	add r4, r4, r1
	mov r5, r0
	cmp r12, #0
	beq 228f
	mov r0, r9
	add r2, r10, #48
	mov r1, r2
	mov r2, r3
	mov r3, r12
	bl {vg_sm4_ctr32}
	b 229f
228:
229:
	cmp r5, #0
	beq 230f
	mov r12, #0
	str r12, [r10, #64]
	str r12, [r10, #68]
	str r12, [r10, #72]
	str r12, [r10, #76]
	mov r0, r9
	add r2, r10, #48
	add r3, r10, #64
	mov r12, #1
	mov r1, r2
	mov r2, r3
	mov r3, r12
	bl {vg_sm4_ctr32}
	add r1, r10, #64
	mov r2, r4
	mov r3, r5
232:
	ldrb r12, [r2, #0]
	ldrb r0, [r1, #0]
	eor r12, r12, r0
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 232b
	b 231f
230:
231:
	b 222f
221:
222:
	ldr r4, [r11, #128]
	ldr r5, [r11, #132]
	ldr r6, [r11, #136]
	ldr r7, [r11, #140]
	ldr r8, [r11, #144]
	ldr r9, [r11, #148]
	ldr r10, [r11, #152]
	ldr lr, [r11, #160]
	ldr r11, [r11, #156]
	add sp, sp, #800
	bx lr

vg_sm4_gcm_stream_finish:
	sub sp, sp, #800
	add r12, sp, #0
	str lr, [r12, #16]
	ldr lr, [sp, #800]
	str lr, [r12, #0]
	ldr lr, [sp, #804]
	str lr, [r12, #4]
	ldr lr, [sp, #808]
	str lr, [r12, #8]
	add lr, sp, #20
	str lr, [r12, #12]
	ldr lr, [sp, #16]
	ldr r12, [sp, #12]
	str r4, [r12, #128]
	str r5, [r12, #132]
	str r6, [r12, #136]
	str r7, [r12, #140]
	str r8, [r12, #144]
	str r9, [r12, #148]
	str r10, [r12, #152]
	str r11, [r12, #156]
	str lr, [r12, #160]
	mov r11, r12
	mov r10, r1
	mov r9, r0
	mov r8, r2
	mov r7, r3
	ldr r0, [sp, #0]
	ldr r1, [sp, #4]
	orr r0, r0, r1
	cmp r0, #0
	beq 20f
	ldr r6, [sp, #0]
	b 21f
20:
	mov r6, r8
21:
	and r6, r6, #15
	cmp r6, #0
	beq 22f
	mov r12, #0
	str r12, [r11, #96]
	str r12, [r11, #100]
	str r12, [r11, #104]
	str r12, [r11, #108]
	add r1, r10, #32
	add r2, r11, #96
	mov r3, r6
24:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 24b
	add r0, r9, #240
	add r1, r10, #16
	add r2, r11, #96
	mov r3, #1
	add r12, r11, #512
	push {r12, lr}
	bl {vg_ghash}
	ldr r12, [sp], #8
	b 23f
22:
23:
	mov r4, r8
	mov r5, r7
	ldr r6, [sp, #0]
	ldr r7, [sp, #4]
	lsl r0, r5, #3
	orr r0, r0, r4, lsr #29
	rev r0, r0
	str r0, [r11, #96]
	lsl r0, r4, #3
	rev r0, r0
	str r0, [r11, #100]
	lsl r0, r7, #3
	orr r0, r0, r6, lsr #29
	rev r0, r0
	str r0, [r11, #104]
	lsl r0, r6, #3
	rev r0, r0
	str r0, [r11, #108]
	add r0, r9, #240
	add r1, r10, #16
	add r2, r11, #96
	mov r3, #1
	add r12, r11, #512
	push {r12, lr}
	bl {vg_ghash}
	ldr r12, [sp], #8
	ldr r0, [r10, #16]
	str r0, [r11, #0]
	ldr r0, [r10, #20]
	str r0, [r11, #4]
	ldr r0, [r10, #24]
	str r0, [r11, #8]
	ldr r0, [r10, #28]
	str r0, [r11, #12]
	mov r0, r9
	mov r2, r10
	add r3, r11, #0
	mov r12, #1
	mov r1, r2
	mov r2, r3
	mov r3, r12
	bl {vg_sm4_ctr32}
	ldr r1, [sp, #8]
	ldr r0, [r11, #0]
	str r0, [r1, #0]
	ldr r0, [r11, #4]
	str r0, [r1, #4]
	ldr r0, [r11, #8]
	str r0, [r1, #8]
	ldr r0, [r11, #12]
	str r0, [r1, #12]
	ldr r4, [r11, #128]
	ldr r5, [r11, #132]
	ldr r6, [r11, #136]
	ldr r7, [r11, #140]
	ldr r8, [r11, #144]
	ldr r9, [r11, #148]
	ldr r10, [r11, #152]
	ldr lr, [r11, #160]
	ldr r11, [r11, #156]
	add sp, sp, #800
	bx lr

vg_sm4_gcm_stream_verify:
	sub sp, sp, #800
	add r12, sp, #0
	str lr, [r12, #20]
	ldr lr, [sp, #800]
	str lr, [r12, #0]
	ldr lr, [sp, #804]
	str lr, [r12, #4]
	ldr lr, [sp, #808]
	str lr, [r12, #8]
	ldr lr, [sp, #812]
	str lr, [r12, #12]
	add lr, sp, #24
	str lr, [r12, #16]
	ldr lr, [sp, #20]
	ldr r12, [sp, #16]
	str r4, [r12, #128]
	str r5, [r12, #132]
	str r6, [r12, #136]
	str r7, [r12, #140]
	str r8, [r12, #144]
	str r9, [r12, #148]
	str r10, [r12, #152]
	str r11, [r12, #156]
	str lr, [r12, #160]
	mov r11, r12
	mov r10, r1
	mov r9, r0
	mov r8, r2
	mov r7, r3
	ldr r6, [sp, #12]
	sub r0, r6, #4
	cmp r0, #13
	mov r0, #0
	adc r0, r0, #0
	cmp r0, #1
	beq 20f
	ldr r1, [sp, #8]
	mov r0, #0
	str r0, [r11, #256]
	str r0, [r11, #260]
	str r0, [r11, #264]
	str r0, [r11, #268]
	add r2, r11, #256
	mov r3, r6
22:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 22b
	ldr r0, [sp, #0]
	ldr r1, [sp, #4]
	orr r0, r0, r1
	cmp r0, #0
	beq 23f
	ldr r6, [sp, #0]
	b 24f
23:
	mov r6, r8
24:
	and r6, r6, #15
	cmp r6, #0
	beq 25f
	mov r12, #0
	str r12, [r11, #96]
	str r12, [r11, #100]
	str r12, [r11, #104]
	str r12, [r11, #108]
	add r1, r10, #32
	add r2, r11, #96
	mov r3, r6
27:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 27b
	add r0, r9, #240
	add r1, r10, #16
	add r2, r11, #96
	mov r3, #1
	add r12, r11, #512
	push {r12, lr}
	bl {vg_ghash}
	ldr r12, [sp], #8
	b 26f
25:
26:
	mov r4, r8
	mov r5, r7
	ldr r6, [sp, #0]
	ldr r7, [sp, #4]
	lsl r0, r5, #3
	orr r0, r0, r4, lsr #29
	rev r0, r0
	str r0, [r11, #96]
	lsl r0, r4, #3
	rev r0, r0
	str r0, [r11, #100]
	lsl r0, r7, #3
	orr r0, r0, r6, lsr #29
	rev r0, r0
	str r0, [r11, #104]
	lsl r0, r6, #3
	rev r0, r0
	str r0, [r11, #108]
	add r0, r9, #240
	add r1, r10, #16
	add r2, r11, #96
	mov r3, #1
	add r12, r11, #512
	push {r12, lr}
	bl {vg_ghash}
	ldr r12, [sp], #8
	ldr r0, [r10, #16]
	str r0, [r11, #0]
	ldr r0, [r10, #20]
	str r0, [r11, #4]
	ldr r0, [r10, #24]
	str r0, [r11, #8]
	ldr r0, [r10, #28]
	str r0, [r11, #12]
	mov r0, r9
	mov r2, r10
	add r3, r11, #0
	mov r12, #1
	mov r1, r2
	mov r2, r3
	mov r3, r12
	bl {vg_sm4_ctr32}
	ldr r6, [sp, #12]
	mov r0, #0
	str r0, [r11, #240]
	str r0, [r11, #244]
	str r0, [r11, #248]
	str r0, [r11, #252]
	add r1, r11, #0
	add r2, r11, #240
	mov r3, r6
28:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 28b
	ldr r0, [r11, #240]
	ldr r2, [r11, #256]
	eor r0, r0, r2
	ldr r1, [r11, #244]
	ldr r2, [r11, #260]
	eor r1, r1, r2
	orr r0, r0, r1
	ldr r1, [r11, #248]
	ldr r2, [r11, #264]
	eor r1, r1, r2
	orr r0, r0, r1
	ldr r1, [r11, #252]
	ldr r2, [r11, #268]
	eor r1, r1, r2
	orr r0, r0, r1
	mov r1, #0
	sub r1, r1, r0
	orr r0, r0, r1
	lsr r0, r0, #31
	mov r1, #1
	sub r0, r1, r0
	b 21f
20:
	mov r0, #0
21:
	ldr r4, [r11, #128]
	ldr r5, [r11, #132]
	ldr r6, [r11, #136]
	ldr r7, [r11, #140]
	ldr r8, [r11, #144]
	ldr r9, [r11, #148]
	ldr r10, [r11, #152]
	ldr lr, [r11, #160]
	ldr r11, [r11, #156]
	add sp, sp, #800
	bx lr
