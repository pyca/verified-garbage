// The functions of `src/internal/vg_dsa_sign_prevalidated.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_dsa_sign_prevalidated:
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
	str r0, [r12, #96]
	str r2, [r12, #64]
	ldr r4, [sp, #0]
	str r4, [r12, #100]
	ldr r4, [sp, #4]
	str r4, [r12, #88]
	ldr r4, [sp, #8]
	str r4, [r12, #104]
	ldr r4, [sp, #12]
	str r4, [r12, #92]
	ldr r4, [sp, #16]
	str r4, [r12, #108]
	ldr r4, [r12, #64]
	ldr r5, [r12, #100]
	add r4, r4, r5
	str r4, [r12, #68]
	ldr r5, [r12, #104]
	add r4, r4, r5
	str r4, [r12, #72]
	ldr r5, [r12, #100]
	add r4, r4, r5
	str r4, [r12, #76]
	ldr r5, [r12, #100]
	add r4, r4, r5
	str r4, [r12, #80]
	ldr r4, [r12, #100]
	movw r5, #128
	cmp r4, r5
	beq 20f
	mov r4, #0
	cmp r4, #1
	b 21f
20:
	ldr r4, [r12, #104]
	movw r5, #20
	cmp r4, r5
21:
	beq 22f
	ldr r4, [r12, #100]
	movw r5, #256
	cmp r4, r5
	beq 24f
	mov r4, #0
	cmp r4, #1
	b 25f
24:
	ldr r4, [r12, #104]
	movw r5, #28
	cmp r4, r5
25:
	beq 26f
	ldr r4, [r12, #100]
	movw r5, #256
	cmp r4, r5
	beq 28f
	mov r4, #0
	cmp r4, #1
	b 29f
28:
	ldr r4, [r12, #104]
	movw r5, #32
	cmp r4, r5
29:
	beq 210f
	ldr r4, [r12, #100]
	movw r5, #384
	cmp r4, r5
	beq 212f
	mov r4, #0
	cmp r4, #1
	b 213f
212:
	ldr r4, [r12, #104]
	movw r5, #32
	cmp r4, r5
213:
	beq 214f
	ldr r4, [r12, #100]
	movw r5, #256
	cmp r4, r5
	beq 216f
	mov r4, #0
	cmp r4, #1
	b 217f
216:
	ldr r4, [r12, #104]
	movw r5, #20
	cmp r4, r5
217:
	beq 218f
	ldr r11, [r12, #96]
	ldr r4, [r12, #104]
	add lr, r11, r4
	add lr, lr, r4
	mov r4, #0
220:
	strb r4, [r11, #0]
	add r11, r11, #1
	cmp r11, lr
	bne 220b
	mov r0, #0
	b 219f
218:
	ldr r11, [r12, #64]
	movw r8, #252
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #512
	add r9, r12, r9
221:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 221b
	movw r10, #3160
	add r10, r12, r10
	movw r9, #3416
	add r9, r12, r9
	mov r7, #0
222:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 222b
	movw r10, #3160
	add r10, r12, r10
	movw r4, #0
	movt r4, #32768
	str r4, [r10, #124]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #3160
	add r1, r12, r1
	movw r9, #512
	add r9, r12, r9
223:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	add r10, r10, #4
	add r1, r1, #4
	cmp r10, r9
	bne 223b
	sub r2, r3, #1
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
	mov r11, r2
	movw r10, #3160
	add r10, r12, r10
	movw r9, #3416
	add r9, r12, r9
	mov r7, #0
224:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 224b
	movw r10, #3160
	add r10, r12, r10
	movw r4, #1
	movt r4, #0
	str r4, [r10, #128]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #3160
	add r1, r12, r1
	movw r9, #512
	add r9, r12, r9
225:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	add r10, r10, #4
	add r1, r1, #4
	cmp r10, r9
	bne 225b
	sub r2, r3, #1
	and r2, r2, r11
	str r2, [r12, #8]
	movw r10, #3160
	add r10, r12, r10
	movw r9, #3416
	add r9, r12, r9
	mov r7, #0
226:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 226b
	movw r10, #3160
	add r10, r12, r10
	movw r4, #0
	movt r4, #32768
	str r4, [r10, #252]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #3160
	add r1, r12, r1
	movw r9, #512
	add r9, r12, r9
227:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	add r10, r10, #4
	add r1, r1, #4
	cmp r10, r9
	bne 227b
	sub r2, r3, #1
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
	mov r11, r2
	mov r2, r11
	str r2, [r12, #12]
	mov r2, #0
	str r2, [r12, #16]
	movw r10, #256
	add r10, r12, r10
	ldr r4, [r10, #0]
	str r4, [r12, #32]
	ldr r11, [r12, #68]
	movw r8, #16
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #276
	add r9, r12, r9
228:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 228b
	mov r4, #0
	str r4, [r10, #0]
	movw r10, #608
	add r10, r12, r10
	movw r9, #632
	add r9, r12, r9
	mov r7, #0
229:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 229b
	movw r10, #608
	add r10, r12, r10
	movw r4, #0
	movt r4, #32768
	str r4, [r10, #16]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #608
	add r1, r12, r1
	movw r9, #280
	add r9, r12, r9
230:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	add r10, r10, #4
	add r1, r1, #4
	cmp r10, r9
	bne 230b
	sub r2, r3, #1
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
	mov r11, r2
	movw r10, #608
	add r10, r12, r10
	movw r9, #632
	add r9, r12, r9
	mov r7, #0
231:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 231b
	movw r10, #608
	add r10, r12, r10
	movw r4, #1
	movt r4, #0
	str r4, [r10, #20]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #608
	add r1, r12, r1
	movw r9, #280
	add r9, r12, r9
232:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	add r10, r10, #4
	add r1, r1, #4
	cmp r10, r9
	bne 232b
	sub r2, r3, #1
	and r2, r2, r11
	str r2, [r12, #20]
	mov r2, #0
	str r2, [r12, #24]
	mov r2, #0
	str r2, [r12, #28]
	movw r10, #256
	add r10, r12, r10
	ldr r2, [r10, #0]
	ldr r4, [r12, #32]
	and r2, r2, r4
	and r2, r2, #1
	mov r4, #0
	sub r4, r4, r2
	str r4, [r12, #32]
	ldr r4, [r12, #8]
	ldr r5, [r12, #20]
	and r4, r4, r5
	ldr r5, [r12, #24]
	ldr r7, [r12, #28]
	orr r5, r5, r7
	ldr r7, [r12, #20]
	orr r5, r5, r7
	ldr r7, [r12, #12]
	and r5, r5, r7
	orr r4, r4, r5
	ldr r5, [r12, #16]
	ldr r7, [r12, #28]
	and r5, r5, r7
	orr r4, r4, r5
	ldr r5, [r12, #32]
	and r4, r4, r5
	str r4, [r12, #116]
	ldr r4, [r12, #20]
	and r4, r4, #20
	ldr r2, [r12, #24]
	and r2, r2, #28
	orr r2, r2, r4
	ldr r4, [r12, #28]
	and r4, r4, #32
	orr r2, r2, r4
	ldr r7, [r12, #108]
	movw r6, #65535
	mov r3, #1
	mov r5, r2
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	sub r3, r3, #1
	eor r7, r7, r2
	and r7, r7, r3
	eor r2, r2, r7
	str r2, [r12, #112]
	ldr r4, [r12, #116]
	cmp r4, #0
	beq 233f
	ldr r11, [r12, #68]
	movw r8, #16
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #276
	add r9, r12, r9
235:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 235b
	mov r4, #0
	str r4, [r10, #0]
	movw r1, #256
	add r1, r12, r1
	ldr r5, [r1, #0]
	movw r6, #65535
	and r5, r5, r6
	mov r7, r5
	mul r4, r5, r7
	movw r2, #2
	sub r4, r2, r4
	mul r7, r7, r4
	mul r4, r5, r7
	movw r2, #2
	sub r4, r2, r4
	mul r7, r7, r4
	mul r4, r5, r7
	movw r2, #2
	sub r4, r2, r4
	mul r7, r7, r4
	mov r4, #0
	sub r4, r4, r7
	and r4, r4, r6
	str r4, [r12, #0]
	movw r10, #576
	add r10, r12, r10
	movw r9, #600
	add r9, r12, r9
	mov r7, #0
236:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 236b
	movw r10, #576
	add r10, r12, r10
	movw r4, #2
	movt r4, #0
	str r4, [r10, #0]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #576
	add r1, r12, r1
	movw r8, #544
	add r8, r12, r8
	movw r9, #280
	add r9, r12, r9
237:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	and r2, r4, r6
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	orr r2, r2, r4, lsl #16
	str r2, [r8, #0]
	add r10, r10, #4
	add r1, r1, #4
	add r8, r8, #4
	cmp r10, r9
	bne 237b
	movw r11, #14912
	add r11, r12, r11
	mov r4, #0
	sub r4, r4, #1
	mov r3, r4
	movw r8, #16
	add r8, r11, r8
	movw r10, #544
	add r10, r12, r10
	movw r9, #564
	add r9, r12, r9
238:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 238b
	ldr r11, [r12, #68]
	movw r8, #16
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #276
	add r9, r12, r9
239:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 239b
	mov r4, #0
	str r4, [r10, #0]
	ldr r11, [r12, #88]
	movw r8, #16
	add r8, r11, r8
	movw r10, #512
	add r10, r12, r10
	movw r9, #532
	add r9, r12, r9
240:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 240b
	mov r4, #0
	str r4, [r10, #0]
	movw r6, #65535
	mov r3, #1
	movw r10, #512
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r9, #536
	add r9, r12, r9
241:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	add r10, r10, #4
	add r1, r1, #4
	cmp r10, r9
	bne 241b
	sub r2, r3, #1
	mov r8, r2
	mov r3, #0
	movw r10, #512
	add r10, r12, r10
	movw r9, #536
	add r9, r12, r9
242:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 242b
	mov r4, #0
	sub r4, r4, r3
	orr r4, r4, r3
	lsr r4, r4, #31
	mov r2, #0
	sub r2, r2, r4
	and r2, r2, r8
	ldr r4, [r12, #116]
	and r4, r4, r2
	str r4, [r12, #116]
	ldr r11, [r12, #64]
	movw r8, #252
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #512
	add r9, r12, r9
243:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 243b
	ldr r11, [r12, #72]
	movw r8, #252
	add r8, r11, r8
	movw r10, #2368
	add r10, r12, r10
	movw r9, #2624
	add r9, r12, r9
244:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 244b
	ldr r11, [r12, #88]
	movw r8, #16
	add r8, r11, r8
	movw r10, #3160
	add r10, r12, r10
	movw r9, #3180
	add r9, r12, r9
245:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 245b
	movw r9, #236
	add r9, r10, r9
	mov r4, #0
246:
	str r4, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 246b
	mov r11, r12
	mov r0, r12
	movw r1, #428
	bl {vg_dsa_pow_32_5}
	mov r12, r11
	movw r11, #14944
	add r11, r12, r11
	mov r4, #0
	sub r4, r4, #1
	mov r3, r4
	movw r8, #252
	add r8, r11, r8
	movw r10, #2632
	add r10, r12, r10
	movw r9, #2888
	add r9, r12, r9
247:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 247b
	ldr r11, [r12, #68]
	movw r8, #16
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #276
	add r9, r12, r9
248:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 248b
	mov r4, #0
	str r4, [r10, #0]
	movw r11, #14944
	add r11, r12, r11
	movw lr, #256
	add lr, lr, r11
	mov r2, r11
	sub r3, lr, r11
	mov r11, r12
	mov r0, r12
	movw r1, #80
	bl {vg_dsa_reduce_3}
	mov r12, r11
	movw r11, #14720
	add r11, r12, r11
	mov r4, #0
	sub r4, r4, #1
	mov r3, r4
	movw r8, #16
	add r8, r11, r8
	movw r10, #544
	add r10, r12, r10
	movw r9, #564
	add r9, r12, r9
249:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 249b
	ldr r11, [r12, #68]
	movw r8, #16
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #276
	add r9, r12, r9
250:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 250b
	mov r4, #0
	str r4, [r10, #0]
	ldr r11, [r12, #88]
	movw r8, #16
	add r8, r11, r8
	movw r10, #512
	add r10, r12, r10
	movw r9, #532
	add r9, r12, r9
251:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 251b
	mov r4, #0
	str r4, [r10, #0]
	movw r11, #14912
	add r11, r12, r11
	movw r8, #16
	add r8, r11, r8
	movw r10, #608
	add r10, r12, r10
	movw r9, #628
	add r9, r12, r9
252:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 252b
	mov r4, #0
	str r4, [r10, #0]
	mov r11, r12
	mov r0, r12
	movw r1, #80
	bl {vg_dsa_pow_3_5}
	mov r12, r11
	movw r11, #14784
	add r11, r12, r11
	mov r4, #0
	sub r4, r4, #1
	mov r3, r4
	movw r8, #16
	add r8, r11, r8
	movw r10, #544
	add r10, r12, r10
	movw r9, #564
	add r9, r12, r9
253:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 253b
	ldr r11, [r12, #68]
	movw r8, #16
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #276
	add r9, r12, r9
254:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 254b
	mov r4, #0
	str r4, [r10, #0]
	ldr r11, [r12, #80]
	movw r8, #16
	add r8, r11, r8
	movw r10, #512
	add r10, r12, r10
	movw r9, #532
	add r9, r12, r9
255:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 255b
	mov r4, #0
	str r4, [r10, #0]
	movw r11, #14720
	add r11, r12, r11
	movw r8, #16
	add r8, r11, r8
	movw r10, #608
	add r10, r12, r10
	movw r9, #628
	add r9, r12, r9
256:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 256b
	mov r4, #0
	str r4, [r10, #0]
	mov r11, r12
	mov r0, r12
	movw r1, #80
	bl {vg_dsa_mulmod_3}
	mov r12, r11
	movw r11, #14816
	add r11, r12, r11
	mov r4, #0
	sub r4, r4, #1
	mov r3, r4
	movw r8, #16
	add r8, r11, r8
	movw r10, #544
	add r10, r12, r10
	movw r9, #564
	add r9, r12, r9
257:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 257b
	ldr r11, [r12, #68]
	movw r8, #16
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #276
	add r9, r12, r9
258:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 258b
	mov r4, #0
	str r4, [r10, #0]
	ldr r11, [r12, #92]
	ldr lr, [r12, #112]
	add lr, lr, r11
	mov r2, r11
	sub r3, lr, r11
	mov r11, r12
	mov r0, r12
	movw r1, #80
	bl {vg_dsa_reduce_3}
	mov r12, r11
	movw r11, #14880
	add r11, r12, r11
	mov r4, #0
	sub r4, r4, #1
	mov r3, r4
	movw r8, #16
	add r8, r11, r8
	movw r10, #544
	add r10, r12, r10
	movw r9, #564
	add r9, r12, r9
259:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 259b
	ldr r11, [r12, #68]
	movw r8, #16
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #276
	add r9, r12, r9
260:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 260b
	mov r4, #0
	str r4, [r10, #0]
	movw r1, #256
	add r1, r12, r1
	ldr r5, [r1, #0]
	movw r6, #65535
	and r5, r5, r6
	mov r7, r5
	mul r4, r5, r7
	movw r2, #2
	sub r4, r2, r4
	mul r7, r7, r4
	mul r4, r5, r7
	movw r2, #2
	sub r4, r2, r4
	mul r7, r7, r4
	mul r4, r5, r7
	movw r2, #2
	sub r4, r2, r4
	mul r7, r7, r4
	mov r4, #0
	sub r4, r4, r7
	and r4, r4, r6
	str r4, [r12, #0]
	movw r11, #14880
	add r11, r12, r11
	movw r8, #16
	add r8, r11, r8
	movw r10, #512
	add r10, r12, r10
	movw r9, #532
	add r9, r12, r9
261:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 261b
	mov r4, #0
	str r4, [r10, #0]
	movw r11, #14816
	add r11, r12, r11
	movw r8, #16
	add r8, r11, r8
	movw r10, #608
	add r10, r12, r10
	movw r9, #628
	add r9, r12, r9
262:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 262b
	mov r4, #0
	str r4, [r10, #0]
	movw r6, #65535
	mov r3, #0
	movw r10, #512
	add r10, r12, r10
	movw r0, #608
	add r0, r12, r0
	movw r8, #320
	add r8, r12, r8
	movw r9, #536
	add r9, r12, r9
263:
	ldr r7, [r10, #0]
	ldr r2, [r0, #0]
	and r4, r7, r6
	and r5, r2, r6
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r8, #0]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r2, #16
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r8, #4]
	lsr r3, r4, #16
	add r10, r10, #4
	add r0, r0, #4
	add r8, r8, #8
	cmp r10, r9
	bne 263b
	str r3, [r8, #0]
	movw r6, #65535
	mov r3, #1
	movw r10, #320
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r8, #288
	add r8, r12, r8
	movw r9, #280
	add r9, r12, r9
264:
	ldr r7, [r1, #0]
	ldr r5, [r10, #0]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r2, r5, r6
	ldr r5, [r10, #4]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r2, r2, r5, lsl #16
	str r2, [r8, #0]
	add r10, r10, #8
	add r1, r1, #4
	add r8, r8, #4
	cmp r1, r9
	bne 264b
	ldr r5, [r10, #0]
	add r3, r3, r5
	mov r4, #0
	sub r3, r4, r3
	movw r10, #320
	add r10, r12, r10
	movw r8, #288
	add r8, r12, r8
	movw r1, #544
	add r1, r12, r1
	movw r9, #312
	add r9, r12, r9
265:
	ldr r5, [r10, #0]
	ldr r7, [r10, #4]
	orr r5, r5, r7, lsl #16
	ldr r7, [r8, #0]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [r1, #0]
	add r10, r10, #8
	add r8, r8, #4
	add r1, r1, #4
	cmp r8, r9
	bne 265b
	movw r11, #14848
	add r11, r12, r11
	mov r4, #0
	sub r4, r4, #1
	mov r3, r4
	movw r8, #16
	add r8, r11, r8
	movw r10, #544
	add r10, r12, r10
	movw r9, #564
	add r9, r12, r9
266:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 266b
	ldr r11, [r12, #68]
	movw r8, #16
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #276
	add r9, r12, r9
267:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 267b
	mov r4, #0
	str r4, [r10, #0]
	movw r11, #14784
	add r11, r12, r11
	movw r8, #16
	add r8, r11, r8
	movw r10, #512
	add r10, r12, r10
	movw r9, #532
	add r9, r12, r9
268:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 268b
	mov r4, #0
	str r4, [r10, #0]
	movw r11, #14848
	add r11, r12, r11
	movw r8, #16
	add r8, r11, r8
	movw r10, #608
	add r10, r12, r10
	movw r9, #628
	add r9, r12, r9
269:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 269b
	mov r4, #0
	str r4, [r10, #0]
	mov r11, r12
	mov r0, r12
	movw r1, #80
	bl {vg_dsa_mulmod_3}
	mov r12, r11
	movw r11, #14752
	add r11, r12, r11
	mov r4, #0
	sub r4, r4, #1
	mov r3, r4
	movw r8, #16
	add r8, r11, r8
	movw r10, #544
	add r10, r12, r10
	movw r9, #564
	add r9, r12, r9
270:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 270b
	movw r11, #14720
	add r11, r12, r11
	movw r8, #16
	add r8, r11, r8
	movw r10, #512
	add r10, r12, r10
	movw r9, #532
	add r9, r12, r9
271:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 271b
	mov r4, #0
	str r4, [r10, #0]
	mov r3, #0
	movw r10, #512
	add r10, r12, r10
	movw r9, #536
	add r9, r12, r9
272:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 272b
	mov r4, #0
	sub r4, r4, r3
	orr r4, r4, r3
	lsr r4, r4, #31
	mov r2, #0
	sub r2, r2, r4
	ldr r4, [r12, #116]
	and r4, r4, r2
	str r4, [r12, #116]
	movw r11, #14752
	add r11, r12, r11
	movw r8, #16
	add r8, r11, r8
	movw r10, #512
	add r10, r12, r10
	movw r9, #532
	add r9, r12, r9
273:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 273b
	mov r4, #0
	str r4, [r10, #0]
	mov r3, #0
	movw r10, #512
	add r10, r12, r10
	movw r9, #536
	add r9, r12, r9
274:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 274b
	mov r4, #0
	sub r4, r4, r3
	orr r4, r4, r3
	lsr r4, r4, #31
	mov r2, #0
	sub r2, r2, r4
	ldr r4, [r12, #116]
	and r4, r4, r2
	str r4, [r12, #116]
	movw r11, #14720
	add r11, r12, r11
	movw r8, #16
	add r8, r11, r8
	movw r10, #512
	add r10, r12, r10
	movw r9, #532
	add r9, r12, r9
275:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 275b
	mov r4, #0
	str r4, [r10, #0]
	ldr r11, [r12, #96]
	ldr r3, [r12, #116]
	movw r8, #16
	add r8, r11, r8
	movw r10, #512
	add r10, r12, r10
	movw r9, #532
	add r9, r12, r9
276:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 276b
	movw r11, #14752
	add r11, r12, r11
	movw r8, #16
	add r8, r11, r8
	movw r10, #512
	add r10, r12, r10
	movw r9, #532
	add r9, r12, r9
277:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 277b
	mov r4, #0
	str r4, [r10, #0]
	ldr r11, [r12, #96]
	movw r4, #20
	add r11, r11, r4
	ldr r3, [r12, #116]
	movw r8, #16
	add r8, r11, r8
	movw r10, #512
	add r10, r12, r10
	movw r9, #532
	add r9, r12, r9
278:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 278b
	ldr r0, [r12, #116]
	and r0, r0, #1
	b 234f
233:
	ldr r11, [r12, #96]
	ldr r4, [r12, #104]
	add lr, r11, r4
	add lr, lr, r4
	mov r4, #0
279:
	strb r4, [r11, #0]
	add r11, r11, #1
	cmp r11, lr
	bne 279b
	mov r0, #0
234:
219:
	b 215f
214:
	ldr r11, [r12, #64]
	movw r8, #380
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #640
	add r9, r12, r9
280:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 280b
	movw r10, #4568
	add r10, r12, r10
	movw r9, #4952
	add r9, r12, r9
	mov r7, #0
281:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 281b
	movw r10, #4568
	add r10, r12, r10
	movw r4, #0
	movt r4, #32768
	str r4, [r10, #124]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #4568
	add r1, r12, r1
	movw r9, #640
	add r9, r12, r9
282:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	add r10, r10, #4
	add r1, r1, #4
	cmp r10, r9
	bne 282b
	sub r2, r3, #1
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
	mov r11, r2
	movw r10, #4568
	add r10, r12, r10
	movw r9, #4952
	add r9, r12, r9
	mov r7, #0
283:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 283b
	movw r10, #4568
	add r10, r12, r10
	movw r4, #1
	movt r4, #0
	str r4, [r10, #128]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #4568
	add r1, r12, r1
	movw r9, #640
	add r9, r12, r9
284:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	add r10, r10, #4
	add r1, r1, #4
	cmp r10, r9
	bne 284b
	sub r2, r3, #1
	and r2, r2, r11
	str r2, [r12, #8]
	movw r10, #4568
	add r10, r12, r10
	movw r9, #4952
	add r9, r12, r9
	mov r7, #0
285:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 285b
	movw r10, #4568
	add r10, r12, r10
	movw r4, #0
	movt r4, #32768
	str r4, [r10, #252]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #4568
	add r1, r12, r1
	movw r9, #640
	add r9, r12, r9
286:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	add r10, r10, #4
	add r1, r1, #4
	cmp r10, r9
	bne 286b
	sub r2, r3, #1
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
	mov r11, r2
	movw r10, #4568
	add r10, r12, r10
	movw r9, #4952
	add r9, r12, r9
	mov r7, #0
287:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 287b
	movw r10, #4568
	add r10, r12, r10
	movw r4, #1
	movt r4, #0
	str r4, [r10, #256]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #4568
	add r1, r12, r1
	movw r9, #640
	add r9, r12, r9
288:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	add r10, r10, #4
	add r1, r1, #4
	cmp r10, r9
	bne 288b
	sub r2, r3, #1
	and r2, r2, r11
	str r2, [r12, #12]
	movw r10, #4568
	add r10, r12, r10
	movw r9, #4952
	add r9, r12, r9
	mov r7, #0
289:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 289b
	movw r10, #4568
	add r10, r12, r10
	movw r4, #0
	movt r4, #32768
	str r4, [r10, #380]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #4568
	add r1, r12, r1
	movw r9, #640
	add r9, r12, r9
290:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	add r10, r10, #4
	add r1, r1, #4
	cmp r10, r9
	bne 290b
	sub r2, r3, #1
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
	mov r11, r2
	mov r2, r11
	str r2, [r12, #16]
	movw r10, #256
	add r10, r12, r10
	ldr r4, [r10, #0]
	str r4, [r12, #32]
	ldr r11, [r12, #68]
	movw r8, #28
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #288
	add r9, r12, r9
291:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 291b
	movw r10, #696
	add r10, r12, r10
	movw r9, #728
	add r9, r12, r9
	mov r7, #0
292:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 292b
	movw r10, #696
	add r10, r12, r10
	movw r4, #0
	movt r4, #32768
	str r4, [r10, #16]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #696
	add r1, r12, r1
	movw r9, #288
	add r9, r12, r9
293:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	add r10, r10, #4
	add r1, r1, #4
	cmp r10, r9
	bne 293b
	sub r2, r3, #1
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
	mov r11, r2
	movw r10, #696
	add r10, r12, r10
	movw r9, #728
	add r9, r12, r9
	mov r7, #0
294:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 294b
	movw r10, #696
	add r10, r12, r10
	movw r4, #1
	movt r4, #0
	str r4, [r10, #20]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #696
	add r1, r12, r1
	movw r9, #288
	add r9, r12, r9
295:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	add r10, r10, #4
	add r1, r1, #4
	cmp r10, r9
	bne 295b
	sub r2, r3, #1
	and r2, r2, r11
	str r2, [r12, #20]
	movw r10, #696
	add r10, r12, r10
	movw r9, #728
	add r9, r12, r9
	mov r7, #0
296:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 296b
	movw r10, #696
	add r10, r12, r10
	movw r4, #0
	movt r4, #32768
	str r4, [r10, #24]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #696
	add r1, r12, r1
	movw r9, #288
	add r9, r12, r9
297:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	add r10, r10, #4
	add r1, r1, #4
	cmp r10, r9
	bne 297b
	sub r2, r3, #1
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
	mov r11, r2
	movw r10, #696
	add r10, r12, r10
	movw r9, #728
	add r9, r12, r9
	mov r7, #0
298:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 298b
	movw r10, #696
	add r10, r12, r10
	movw r4, #1
	movt r4, #0
	str r4, [r10, #28]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #696
	add r1, r12, r1
	movw r9, #288
	add r9, r12, r9
299:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	add r10, r10, #4
	add r1, r1, #4
	cmp r10, r9
	bne 299b
	sub r2, r3, #1
	and r2, r2, r11
	str r2, [r12, #24]
	movw r10, #696
	add r10, r12, r10
	movw r9, #728
	add r9, r12, r9
	mov r7, #0
2100:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2100b
	movw r10, #696
	add r10, r12, r10
	movw r4, #0
	movt r4, #32768
	str r4, [r10, #28]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #696
	add r1, r12, r1
	movw r9, #288
	add r9, r12, r9
2101:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	add r10, r10, #4
	add r1, r1, #4
	cmp r10, r9
	bne 2101b
	sub r2, r3, #1
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
	mov r11, r2
	mov r2, r11
	str r2, [r12, #28]
	movw r10, #256
	add r10, r12, r10
	ldr r2, [r10, #0]
	ldr r4, [r12, #32]
	and r2, r2, r4
	and r2, r2, #1
	mov r4, #0
	sub r4, r4, r2
	str r4, [r12, #32]
	ldr r4, [r12, #8]
	ldr r5, [r12, #20]
	and r4, r4, r5
	ldr r5, [r12, #24]
	ldr r7, [r12, #28]
	orr r5, r5, r7
	ldr r7, [r12, #20]
	orr r5, r5, r7
	ldr r7, [r12, #12]
	and r5, r5, r7
	orr r4, r4, r5
	ldr r5, [r12, #16]
	ldr r7, [r12, #28]
	and r5, r5, r7
	orr r4, r4, r5
	ldr r5, [r12, #32]
	and r4, r4, r5
	str r4, [r12, #116]
	ldr r4, [r12, #20]
	and r4, r4, #20
	ldr r2, [r12, #24]
	and r2, r2, #28
	orr r2, r2, r4
	ldr r4, [r12, #28]
	and r4, r4, #32
	orr r2, r2, r4
	ldr r7, [r12, #108]
	movw r6, #65535
	mov r3, #1
	mov r5, r2
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	sub r3, r3, #1
	eor r7, r7, r2
	and r7, r7, r3
	eor r2, r2, r7
	str r2, [r12, #112]
	ldr r4, [r12, #116]
	cmp r4, #0
	beq 2102f
	ldr r11, [r12, #68]
	movw r8, #28
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #288
	add r9, r12, r9
2104:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2104b
	movw r1, #256
	add r1, r12, r1
	ldr r5, [r1, #0]
	movw r6, #65535
	and r5, r5, r6
	mov r7, r5
	mul r4, r5, r7
	movw r2, #2
	sub r4, r2, r4
	mul r7, r7, r4
	mul r4, r5, r7
	movw r2, #2
	sub r4, r2, r4
	mul r7, r7, r4
	mul r4, r5, r7
	movw r2, #2
	sub r4, r2, r4
	mul r7, r7, r4
	mov r4, #0
	sub r4, r4, r7
	and r4, r4, r6
	str r4, [r12, #0]
	movw r10, #656
	add r10, r12, r10
	movw r9, #688
	add r9, r12, r9
	mov r7, #0
2105:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2105b
	movw r10, #656
	add r10, r12, r10
	movw r4, #2
	movt r4, #0
	str r4, [r10, #0]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #656
	add r1, r12, r1
	movw r8, #616
	add r8, r12, r8
	movw r9, #288
	add r9, r12, r9
2106:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	and r2, r4, r6
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	orr r2, r2, r4, lsl #16
	str r2, [r8, #0]
	add r10, r10, #4
	add r1, r1, #4
	add r8, r8, #4
	cmp r10, r9
	bne 2106b
	movw r11, #14912
	add r11, r12, r11
	mov r4, #0
	sub r4, r4, #1
	mov r3, r4
	movw r8, #28
	add r8, r11, r8
	movw r10, #616
	add r10, r12, r10
	movw r9, #648
	add r9, r12, r9
2107:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2107b
	ldr r11, [r12, #68]
	movw r8, #28
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #288
	add r9, r12, r9
2108:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2108b
	ldr r11, [r12, #88]
	movw r8, #28
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2109:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2109b
	movw r6, #65535
	mov r3, #1
	movw r10, #576
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r9, #608
	add r9, r12, r9
2110:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	add r10, r10, #4
	add r1, r1, #4
	cmp r10, r9
	bne 2110b
	sub r2, r3, #1
	mov r8, r2
	mov r3, #0
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2111:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 2111b
	mov r4, #0
	sub r4, r4, r3
	orr r4, r4, r3
	lsr r4, r4, #31
	mov r2, #0
	sub r2, r2, r4
	and r2, r2, r8
	ldr r4, [r12, #116]
	and r4, r4, r2
	str r4, [r12, #116]
	ldr r11, [r12, #64]
	movw r8, #380
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #640
	add r9, r12, r9
2112:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2112b
	ldr r11, [r12, #72]
	movw r8, #380
	add r8, r11, r8
	movw r10, #3392
	add r10, r12, r10
	movw r9, #3776
	add r9, r12, r9
2113:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2113b
	ldr r11, [r12, #88]
	movw r8, #28
	add r8, r11, r8
	movw r10, #4568
	add r10, r12, r10
	movw r9, #4600
	add r9, r12, r9
2114:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2114b
	movw r9, #352
	add r9, r10, r9
	mov r4, #0
2115:
	str r4, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2115b
	mov r11, r12
	mov r0, r12
	movw r1, #620
	bl {vg_dsa_pow_48_8}
	mov r12, r11
	movw r11, #14944
	add r11, r12, r11
	mov r4, #0
	sub r4, r4, #1
	mov r3, r4
	movw r8, #380
	add r8, r11, r8
	movw r10, #3784
	add r10, r12, r10
	movw r9, #4168
	add r9, r12, r9
2116:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2116b
	ldr r11, [r12, #68]
	movw r8, #28
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #288
	add r9, r12, r9
2117:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2117b
	movw r11, #14944
	add r11, r12, r11
	movw lr, #384
	add lr, lr, r11
	mov r2, r11
	sub r3, lr, r11
	mov r11, r12
	mov r0, r12
	movw r1, #92
	bl {vg_dsa_reduce_4}
	mov r12, r11
	movw r11, #14720
	add r11, r12, r11
	mov r4, #0
	sub r4, r4, #1
	mov r3, r4
	movw r8, #28
	add r8, r11, r8
	movw r10, #616
	add r10, r12, r10
	movw r9, #648
	add r9, r12, r9
2118:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2118b
	ldr r11, [r12, #68]
	movw r8, #28
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #288
	add r9, r12, r9
2119:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2119b
	ldr r11, [r12, #88]
	movw r8, #28
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2120:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2120b
	movw r11, #14912
	add r11, r12, r11
	movw r8, #28
	add r8, r11, r8
	movw r10, #696
	add r10, r12, r10
	movw r9, #728
	add r9, r12, r9
2121:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2121b
	mov r11, r12
	mov r0, r12
	movw r1, #92
	bl {vg_dsa_pow_4_8}
	mov r12, r11
	movw r11, #14784
	add r11, r12, r11
	mov r4, #0
	sub r4, r4, #1
	mov r3, r4
	movw r8, #28
	add r8, r11, r8
	movw r10, #616
	add r10, r12, r10
	movw r9, #648
	add r9, r12, r9
2122:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2122b
	ldr r11, [r12, #68]
	movw r8, #28
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #288
	add r9, r12, r9
2123:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2123b
	ldr r11, [r12, #80]
	movw r8, #28
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2124:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2124b
	movw r11, #14720
	add r11, r12, r11
	movw r8, #28
	add r8, r11, r8
	movw r10, #696
	add r10, r12, r10
	movw r9, #728
	add r9, r12, r9
2125:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2125b
	mov r11, r12
	mov r0, r12
	movw r1, #92
	bl {vg_dsa_mulmod_4}
	mov r12, r11
	movw r11, #14816
	add r11, r12, r11
	mov r4, #0
	sub r4, r4, #1
	mov r3, r4
	movw r8, #28
	add r8, r11, r8
	movw r10, #616
	add r10, r12, r10
	movw r9, #648
	add r9, r12, r9
2126:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2126b
	ldr r11, [r12, #68]
	movw r8, #28
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #288
	add r9, r12, r9
2127:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2127b
	ldr r11, [r12, #92]
	ldr lr, [r12, #112]
	add lr, lr, r11
	mov r2, r11
	sub r3, lr, r11
	mov r11, r12
	mov r0, r12
	movw r1, #92
	bl {vg_dsa_reduce_4}
	mov r12, r11
	movw r11, #14880
	add r11, r12, r11
	mov r4, #0
	sub r4, r4, #1
	mov r3, r4
	movw r8, #28
	add r8, r11, r8
	movw r10, #616
	add r10, r12, r10
	movw r9, #648
	add r9, r12, r9
2128:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2128b
	ldr r11, [r12, #68]
	movw r8, #28
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #288
	add r9, r12, r9
2129:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2129b
	movw r1, #256
	add r1, r12, r1
	ldr r5, [r1, #0]
	movw r6, #65535
	and r5, r5, r6
	mov r7, r5
	mul r4, r5, r7
	movw r2, #2
	sub r4, r2, r4
	mul r7, r7, r4
	mul r4, r5, r7
	movw r2, #2
	sub r4, r2, r4
	mul r7, r7, r4
	mul r4, r5, r7
	movw r2, #2
	sub r4, r2, r4
	mul r7, r7, r4
	mov r4, #0
	sub r4, r4, r7
	and r4, r4, r6
	str r4, [r12, #0]
	movw r11, #14880
	add r11, r12, r11
	movw r8, #28
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2130:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2130b
	movw r11, #14816
	add r11, r12, r11
	movw r8, #28
	add r8, r11, r8
	movw r10, #696
	add r10, r12, r10
	movw r9, #728
	add r9, r12, r9
2131:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2131b
	movw r6, #65535
	mov r3, #0
	movw r10, #576
	add r10, r12, r10
	movw r0, #696
	add r0, r12, r0
	movw r8, #336
	add r8, r12, r8
	movw r9, #608
	add r9, r12, r9
2132:
	ldr r7, [r10, #0]
	ldr r2, [r0, #0]
	and r4, r7, r6
	and r5, r2, r6
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r8, #0]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r2, #16
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r8, #4]
	lsr r3, r4, #16
	add r10, r10, #4
	add r0, r0, #4
	add r8, r8, #8
	cmp r10, r9
	bne 2132b
	str r3, [r8, #0]
	movw r6, #65535
	mov r3, #1
	movw r10, #336
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r8, #296
	add r8, r12, r8
	movw r9, #288
	add r9, r12, r9
2133:
	ldr r7, [r1, #0]
	ldr r5, [r10, #0]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r2, r5, r6
	ldr r5, [r10, #4]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r2, r2, r5, lsl #16
	str r2, [r8, #0]
	add r10, r10, #8
	add r1, r1, #4
	add r8, r8, #4
	cmp r1, r9
	bne 2133b
	ldr r5, [r10, #0]
	add r3, r3, r5
	mov r4, #0
	sub r3, r4, r3
	movw r10, #336
	add r10, r12, r10
	movw r8, #296
	add r8, r12, r8
	movw r1, #616
	add r1, r12, r1
	movw r9, #328
	add r9, r12, r9
2134:
	ldr r5, [r10, #0]
	ldr r7, [r10, #4]
	orr r5, r5, r7, lsl #16
	ldr r7, [r8, #0]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [r1, #0]
	add r10, r10, #8
	add r8, r8, #4
	add r1, r1, #4
	cmp r8, r9
	bne 2134b
	movw r11, #14848
	add r11, r12, r11
	mov r4, #0
	sub r4, r4, #1
	mov r3, r4
	movw r8, #28
	add r8, r11, r8
	movw r10, #616
	add r10, r12, r10
	movw r9, #648
	add r9, r12, r9
2135:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2135b
	ldr r11, [r12, #68]
	movw r8, #28
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #288
	add r9, r12, r9
2136:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2136b
	movw r11, #14784
	add r11, r12, r11
	movw r8, #28
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2137:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2137b
	movw r11, #14848
	add r11, r12, r11
	movw r8, #28
	add r8, r11, r8
	movw r10, #696
	add r10, r12, r10
	movw r9, #728
	add r9, r12, r9
2138:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2138b
	mov r11, r12
	mov r0, r12
	movw r1, #92
	bl {vg_dsa_mulmod_4}
	mov r12, r11
	movw r11, #14752
	add r11, r12, r11
	mov r4, #0
	sub r4, r4, #1
	mov r3, r4
	movw r8, #28
	add r8, r11, r8
	movw r10, #616
	add r10, r12, r10
	movw r9, #648
	add r9, r12, r9
2139:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2139b
	movw r11, #14720
	add r11, r12, r11
	movw r8, #28
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2140:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2140b
	mov r3, #0
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2141:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 2141b
	mov r4, #0
	sub r4, r4, r3
	orr r4, r4, r3
	lsr r4, r4, #31
	mov r2, #0
	sub r2, r2, r4
	ldr r4, [r12, #116]
	and r4, r4, r2
	str r4, [r12, #116]
	movw r11, #14752
	add r11, r12, r11
	movw r8, #28
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2142:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2142b
	mov r3, #0
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2143:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 2143b
	mov r4, #0
	sub r4, r4, r3
	orr r4, r4, r3
	lsr r4, r4, #31
	mov r2, #0
	sub r2, r2, r4
	ldr r4, [r12, #116]
	and r4, r4, r2
	str r4, [r12, #116]
	movw r11, #14720
	add r11, r12, r11
	movw r8, #28
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2144:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2144b
	ldr r11, [r12, #96]
	ldr r3, [r12, #116]
	movw r8, #28
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2145:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2145b
	movw r11, #14752
	add r11, r12, r11
	movw r8, #28
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2146:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2146b
	ldr r11, [r12, #96]
	movw r4, #32
	add r11, r11, r4
	ldr r3, [r12, #116]
	movw r8, #28
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2147:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2147b
	ldr r0, [r12, #116]
	and r0, r0, #1
	b 2103f
2102:
	ldr r11, [r12, #96]
	ldr r4, [r12, #104]
	add lr, r11, r4
	add lr, lr, r4
	mov r4, #0
2148:
	strb r4, [r11, #0]
	add r11, r11, #1
	cmp r11, lr
	bne 2148b
	mov r0, #0
2103:
215:
	b 211f
210:
	ldr r11, [r12, #64]
	movw r8, #252
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #512
	add r9, r12, r9
2149:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2149b
	movw r10, #3160
	add r10, r12, r10
	movw r9, #3416
	add r9, r12, r9
	mov r7, #0
2150:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2150b
	movw r10, #3160
	add r10, r12, r10
	movw r4, #0
	movt r4, #32768
	str r4, [r10, #124]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #3160
	add r1, r12, r1
	movw r9, #512
	add r9, r12, r9
2151:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	add r10, r10, #4
	add r1, r1, #4
	cmp r10, r9
	bne 2151b
	sub r2, r3, #1
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
	mov r11, r2
	movw r10, #3160
	add r10, r12, r10
	movw r9, #3416
	add r9, r12, r9
	mov r7, #0
2152:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2152b
	movw r10, #3160
	add r10, r12, r10
	movw r4, #1
	movt r4, #0
	str r4, [r10, #128]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #3160
	add r1, r12, r1
	movw r9, #512
	add r9, r12, r9
2153:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	add r10, r10, #4
	add r1, r1, #4
	cmp r10, r9
	bne 2153b
	sub r2, r3, #1
	and r2, r2, r11
	str r2, [r12, #8]
	movw r10, #3160
	add r10, r12, r10
	movw r9, #3416
	add r9, r12, r9
	mov r7, #0
2154:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2154b
	movw r10, #3160
	add r10, r12, r10
	movw r4, #0
	movt r4, #32768
	str r4, [r10, #252]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #3160
	add r1, r12, r1
	movw r9, #512
	add r9, r12, r9
2155:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	add r10, r10, #4
	add r1, r1, #4
	cmp r10, r9
	bne 2155b
	sub r2, r3, #1
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
	mov r11, r2
	mov r2, r11
	str r2, [r12, #12]
	mov r2, #0
	str r2, [r12, #16]
	movw r10, #256
	add r10, r12, r10
	ldr r4, [r10, #0]
	str r4, [r12, #32]
	ldr r11, [r12, #68]
	movw r8, #28
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #288
	add r9, r12, r9
2156:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2156b
	movw r10, #696
	add r10, r12, r10
	movw r9, #728
	add r9, r12, r9
	mov r7, #0
2157:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2157b
	movw r10, #696
	add r10, r12, r10
	movw r4, #0
	movt r4, #32768
	str r4, [r10, #16]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #696
	add r1, r12, r1
	movw r9, #288
	add r9, r12, r9
2158:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	add r10, r10, #4
	add r1, r1, #4
	cmp r10, r9
	bne 2158b
	sub r2, r3, #1
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
	mov r11, r2
	movw r10, #696
	add r10, r12, r10
	movw r9, #728
	add r9, r12, r9
	mov r7, #0
2159:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2159b
	movw r10, #696
	add r10, r12, r10
	movw r4, #1
	movt r4, #0
	str r4, [r10, #20]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #696
	add r1, r12, r1
	movw r9, #288
	add r9, r12, r9
2160:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	add r10, r10, #4
	add r1, r1, #4
	cmp r10, r9
	bne 2160b
	sub r2, r3, #1
	and r2, r2, r11
	str r2, [r12, #20]
	movw r10, #696
	add r10, r12, r10
	movw r9, #728
	add r9, r12, r9
	mov r7, #0
2161:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2161b
	movw r10, #696
	add r10, r12, r10
	movw r4, #0
	movt r4, #32768
	str r4, [r10, #24]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #696
	add r1, r12, r1
	movw r9, #288
	add r9, r12, r9
2162:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	add r10, r10, #4
	add r1, r1, #4
	cmp r10, r9
	bne 2162b
	sub r2, r3, #1
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
	mov r11, r2
	movw r10, #696
	add r10, r12, r10
	movw r9, #728
	add r9, r12, r9
	mov r7, #0
2163:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2163b
	movw r10, #696
	add r10, r12, r10
	movw r4, #1
	movt r4, #0
	str r4, [r10, #28]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #696
	add r1, r12, r1
	movw r9, #288
	add r9, r12, r9
2164:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	add r10, r10, #4
	add r1, r1, #4
	cmp r10, r9
	bne 2164b
	sub r2, r3, #1
	and r2, r2, r11
	str r2, [r12, #24]
	movw r10, #696
	add r10, r12, r10
	movw r9, #728
	add r9, r12, r9
	mov r7, #0
2165:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2165b
	movw r10, #696
	add r10, r12, r10
	movw r4, #0
	movt r4, #32768
	str r4, [r10, #28]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #696
	add r1, r12, r1
	movw r9, #288
	add r9, r12, r9
2166:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	add r10, r10, #4
	add r1, r1, #4
	cmp r10, r9
	bne 2166b
	sub r2, r3, #1
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
	mov r11, r2
	mov r2, r11
	str r2, [r12, #28]
	movw r10, #256
	add r10, r12, r10
	ldr r2, [r10, #0]
	ldr r4, [r12, #32]
	and r2, r2, r4
	and r2, r2, #1
	mov r4, #0
	sub r4, r4, r2
	str r4, [r12, #32]
	ldr r4, [r12, #8]
	ldr r5, [r12, #20]
	and r4, r4, r5
	ldr r5, [r12, #24]
	ldr r7, [r12, #28]
	orr r5, r5, r7
	ldr r7, [r12, #20]
	orr r5, r5, r7
	ldr r7, [r12, #12]
	and r5, r5, r7
	orr r4, r4, r5
	ldr r5, [r12, #16]
	ldr r7, [r12, #28]
	and r5, r5, r7
	orr r4, r4, r5
	ldr r5, [r12, #32]
	and r4, r4, r5
	str r4, [r12, #116]
	ldr r4, [r12, #20]
	and r4, r4, #20
	ldr r2, [r12, #24]
	and r2, r2, #28
	orr r2, r2, r4
	ldr r4, [r12, #28]
	and r4, r4, #32
	orr r2, r2, r4
	ldr r7, [r12, #108]
	movw r6, #65535
	mov r3, #1
	mov r5, r2
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	sub r3, r3, #1
	eor r7, r7, r2
	and r7, r7, r3
	eor r2, r2, r7
	str r2, [r12, #112]
	ldr r4, [r12, #116]
	cmp r4, #0
	beq 2167f
	ldr r11, [r12, #68]
	movw r8, #28
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #288
	add r9, r12, r9
2169:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2169b
	movw r1, #256
	add r1, r12, r1
	ldr r5, [r1, #0]
	movw r6, #65535
	and r5, r5, r6
	mov r7, r5
	mul r4, r5, r7
	movw r2, #2
	sub r4, r2, r4
	mul r7, r7, r4
	mul r4, r5, r7
	movw r2, #2
	sub r4, r2, r4
	mul r7, r7, r4
	mul r4, r5, r7
	movw r2, #2
	sub r4, r2, r4
	mul r7, r7, r4
	mov r4, #0
	sub r4, r4, r7
	and r4, r4, r6
	str r4, [r12, #0]
	movw r10, #656
	add r10, r12, r10
	movw r9, #688
	add r9, r12, r9
	mov r7, #0
2170:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2170b
	movw r10, #656
	add r10, r12, r10
	movw r4, #2
	movt r4, #0
	str r4, [r10, #0]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #656
	add r1, r12, r1
	movw r8, #616
	add r8, r12, r8
	movw r9, #288
	add r9, r12, r9
2171:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	and r2, r4, r6
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	orr r2, r2, r4, lsl #16
	str r2, [r8, #0]
	add r10, r10, #4
	add r1, r1, #4
	add r8, r8, #4
	cmp r10, r9
	bne 2171b
	movw r11, #14912
	add r11, r12, r11
	mov r4, #0
	sub r4, r4, #1
	mov r3, r4
	movw r8, #28
	add r8, r11, r8
	movw r10, #616
	add r10, r12, r10
	movw r9, #648
	add r9, r12, r9
2172:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2172b
	ldr r11, [r12, #68]
	movw r8, #28
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #288
	add r9, r12, r9
2173:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2173b
	ldr r11, [r12, #88]
	movw r8, #28
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2174:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2174b
	movw r6, #65535
	mov r3, #1
	movw r10, #576
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r9, #608
	add r9, r12, r9
2175:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	add r10, r10, #4
	add r1, r1, #4
	cmp r10, r9
	bne 2175b
	sub r2, r3, #1
	mov r8, r2
	mov r3, #0
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2176:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 2176b
	mov r4, #0
	sub r4, r4, r3
	orr r4, r4, r3
	lsr r4, r4, #31
	mov r2, #0
	sub r2, r2, r4
	and r2, r2, r8
	ldr r4, [r12, #116]
	and r4, r4, r2
	str r4, [r12, #116]
	ldr r11, [r12, #64]
	movw r8, #252
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #512
	add r9, r12, r9
2177:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2177b
	ldr r11, [r12, #72]
	movw r8, #252
	add r8, r11, r8
	movw r10, #2368
	add r10, r12, r10
	movw r9, #2624
	add r9, r12, r9
2178:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2178b
	ldr r11, [r12, #88]
	movw r8, #28
	add r8, r11, r8
	movw r10, #3160
	add r10, r12, r10
	movw r9, #3192
	add r9, r12, r9
2179:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2179b
	movw r9, #224
	add r9, r10, r9
	mov r4, #0
2180:
	str r4, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2180b
	mov r11, r12
	mov r0, r12
	movw r1, #428
	bl {vg_dsa_pow_32_8}
	mov r12, r11
	movw r11, #14944
	add r11, r12, r11
	mov r4, #0
	sub r4, r4, #1
	mov r3, r4
	movw r8, #252
	add r8, r11, r8
	movw r10, #2632
	add r10, r12, r10
	movw r9, #2888
	add r9, r12, r9
2181:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2181b
	ldr r11, [r12, #68]
	movw r8, #28
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #288
	add r9, r12, r9
2182:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2182b
	movw r11, #14944
	add r11, r12, r11
	movw lr, #256
	add lr, lr, r11
	mov r2, r11
	sub r3, lr, r11
	mov r11, r12
	mov r0, r12
	movw r1, #92
	bl {vg_dsa_reduce_4}
	mov r12, r11
	movw r11, #14720
	add r11, r12, r11
	mov r4, #0
	sub r4, r4, #1
	mov r3, r4
	movw r8, #28
	add r8, r11, r8
	movw r10, #616
	add r10, r12, r10
	movw r9, #648
	add r9, r12, r9
2183:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2183b
	ldr r11, [r12, #68]
	movw r8, #28
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #288
	add r9, r12, r9
2184:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2184b
	ldr r11, [r12, #88]
	movw r8, #28
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2185:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2185b
	movw r11, #14912
	add r11, r12, r11
	movw r8, #28
	add r8, r11, r8
	movw r10, #696
	add r10, r12, r10
	movw r9, #728
	add r9, r12, r9
2186:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2186b
	mov r11, r12
	mov r0, r12
	movw r1, #92
	bl {vg_dsa_pow_4_8}
	mov r12, r11
	movw r11, #14784
	add r11, r12, r11
	mov r4, #0
	sub r4, r4, #1
	mov r3, r4
	movw r8, #28
	add r8, r11, r8
	movw r10, #616
	add r10, r12, r10
	movw r9, #648
	add r9, r12, r9
2187:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2187b
	ldr r11, [r12, #68]
	movw r8, #28
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #288
	add r9, r12, r9
2188:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2188b
	ldr r11, [r12, #80]
	movw r8, #28
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2189:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2189b
	movw r11, #14720
	add r11, r12, r11
	movw r8, #28
	add r8, r11, r8
	movw r10, #696
	add r10, r12, r10
	movw r9, #728
	add r9, r12, r9
2190:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2190b
	mov r11, r12
	mov r0, r12
	movw r1, #92
	bl {vg_dsa_mulmod_4}
	mov r12, r11
	movw r11, #14816
	add r11, r12, r11
	mov r4, #0
	sub r4, r4, #1
	mov r3, r4
	movw r8, #28
	add r8, r11, r8
	movw r10, #616
	add r10, r12, r10
	movw r9, #648
	add r9, r12, r9
2191:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2191b
	ldr r11, [r12, #68]
	movw r8, #28
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #288
	add r9, r12, r9
2192:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2192b
	ldr r11, [r12, #92]
	ldr lr, [r12, #112]
	add lr, lr, r11
	mov r2, r11
	sub r3, lr, r11
	mov r11, r12
	mov r0, r12
	movw r1, #92
	bl {vg_dsa_reduce_4}
	mov r12, r11
	movw r11, #14880
	add r11, r12, r11
	mov r4, #0
	sub r4, r4, #1
	mov r3, r4
	movw r8, #28
	add r8, r11, r8
	movw r10, #616
	add r10, r12, r10
	movw r9, #648
	add r9, r12, r9
2193:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2193b
	ldr r11, [r12, #68]
	movw r8, #28
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #288
	add r9, r12, r9
2194:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2194b
	movw r1, #256
	add r1, r12, r1
	ldr r5, [r1, #0]
	movw r6, #65535
	and r5, r5, r6
	mov r7, r5
	mul r4, r5, r7
	movw r2, #2
	sub r4, r2, r4
	mul r7, r7, r4
	mul r4, r5, r7
	movw r2, #2
	sub r4, r2, r4
	mul r7, r7, r4
	mul r4, r5, r7
	movw r2, #2
	sub r4, r2, r4
	mul r7, r7, r4
	mov r4, #0
	sub r4, r4, r7
	and r4, r4, r6
	str r4, [r12, #0]
	movw r11, #14880
	add r11, r12, r11
	movw r8, #28
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2195:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2195b
	movw r11, #14816
	add r11, r12, r11
	movw r8, #28
	add r8, r11, r8
	movw r10, #696
	add r10, r12, r10
	movw r9, #728
	add r9, r12, r9
2196:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2196b
	movw r6, #65535
	mov r3, #0
	movw r10, #576
	add r10, r12, r10
	movw r0, #696
	add r0, r12, r0
	movw r8, #336
	add r8, r12, r8
	movw r9, #608
	add r9, r12, r9
2197:
	ldr r7, [r10, #0]
	ldr r2, [r0, #0]
	and r4, r7, r6
	and r5, r2, r6
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r8, #0]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r2, #16
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r8, #4]
	lsr r3, r4, #16
	add r10, r10, #4
	add r0, r0, #4
	add r8, r8, #8
	cmp r10, r9
	bne 2197b
	str r3, [r8, #0]
	movw r6, #65535
	mov r3, #1
	movw r10, #336
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r8, #296
	add r8, r12, r8
	movw r9, #288
	add r9, r12, r9
2198:
	ldr r7, [r1, #0]
	ldr r5, [r10, #0]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r2, r5, r6
	ldr r5, [r10, #4]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r2, r2, r5, lsl #16
	str r2, [r8, #0]
	add r10, r10, #8
	add r1, r1, #4
	add r8, r8, #4
	cmp r1, r9
	bne 2198b
	ldr r5, [r10, #0]
	add r3, r3, r5
	mov r4, #0
	sub r3, r4, r3
	movw r10, #336
	add r10, r12, r10
	movw r8, #296
	add r8, r12, r8
	movw r1, #616
	add r1, r12, r1
	movw r9, #328
	add r9, r12, r9
2199:
	ldr r5, [r10, #0]
	ldr r7, [r10, #4]
	orr r5, r5, r7, lsl #16
	ldr r7, [r8, #0]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [r1, #0]
	add r10, r10, #8
	add r8, r8, #4
	add r1, r1, #4
	cmp r8, r9
	bne 2199b
	movw r11, #14848
	add r11, r12, r11
	mov r4, #0
	sub r4, r4, #1
	mov r3, r4
	movw r8, #28
	add r8, r11, r8
	movw r10, #616
	add r10, r12, r10
	movw r9, #648
	add r9, r12, r9
2200:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2200b
	ldr r11, [r12, #68]
	movw r8, #28
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #288
	add r9, r12, r9
2201:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2201b
	movw r11, #14784
	add r11, r12, r11
	movw r8, #28
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2202:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2202b
	movw r11, #14848
	add r11, r12, r11
	movw r8, #28
	add r8, r11, r8
	movw r10, #696
	add r10, r12, r10
	movw r9, #728
	add r9, r12, r9
2203:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2203b
	mov r11, r12
	mov r0, r12
	movw r1, #92
	bl {vg_dsa_mulmod_4}
	mov r12, r11
	movw r11, #14752
	add r11, r12, r11
	mov r4, #0
	sub r4, r4, #1
	mov r3, r4
	movw r8, #28
	add r8, r11, r8
	movw r10, #616
	add r10, r12, r10
	movw r9, #648
	add r9, r12, r9
2204:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2204b
	movw r11, #14720
	add r11, r12, r11
	movw r8, #28
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2205:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2205b
	mov r3, #0
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2206:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 2206b
	mov r4, #0
	sub r4, r4, r3
	orr r4, r4, r3
	lsr r4, r4, #31
	mov r2, #0
	sub r2, r2, r4
	ldr r4, [r12, #116]
	and r4, r4, r2
	str r4, [r12, #116]
	movw r11, #14752
	add r11, r12, r11
	movw r8, #28
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2207:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2207b
	mov r3, #0
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2208:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 2208b
	mov r4, #0
	sub r4, r4, r3
	orr r4, r4, r3
	lsr r4, r4, #31
	mov r2, #0
	sub r2, r2, r4
	ldr r4, [r12, #116]
	and r4, r4, r2
	str r4, [r12, #116]
	movw r11, #14720
	add r11, r12, r11
	movw r8, #28
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2209:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2209b
	ldr r11, [r12, #96]
	ldr r3, [r12, #116]
	movw r8, #28
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2210:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2210b
	movw r11, #14752
	add r11, r12, r11
	movw r8, #28
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2211:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2211b
	ldr r11, [r12, #96]
	movw r4, #32
	add r11, r11, r4
	ldr r3, [r12, #116]
	movw r8, #28
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2212:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2212b
	ldr r0, [r12, #116]
	and r0, r0, #1
	b 2168f
2167:
	ldr r11, [r12, #96]
	ldr r4, [r12, #104]
	add lr, r11, r4
	add lr, lr, r4
	mov r4, #0
2213:
	strb r4, [r11, #0]
	add r11, r11, #1
	cmp r11, lr
	bne 2213b
	mov r0, #0
2168:
211:
	b 27f
26:
	ldr r11, [r12, #64]
	movw r8, #252
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #512
	add r9, r12, r9
2214:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2214b
	movw r10, #3160
	add r10, r12, r10
	movw r9, #3416
	add r9, r12, r9
	mov r7, #0
2215:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2215b
	movw r10, #3160
	add r10, r12, r10
	movw r4, #0
	movt r4, #32768
	str r4, [r10, #124]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #3160
	add r1, r12, r1
	movw r9, #512
	add r9, r12, r9
2216:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	add r10, r10, #4
	add r1, r1, #4
	cmp r10, r9
	bne 2216b
	sub r2, r3, #1
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
	mov r11, r2
	movw r10, #3160
	add r10, r12, r10
	movw r9, #3416
	add r9, r12, r9
	mov r7, #0
2217:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2217b
	movw r10, #3160
	add r10, r12, r10
	movw r4, #1
	movt r4, #0
	str r4, [r10, #128]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #3160
	add r1, r12, r1
	movw r9, #512
	add r9, r12, r9
2218:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	add r10, r10, #4
	add r1, r1, #4
	cmp r10, r9
	bne 2218b
	sub r2, r3, #1
	and r2, r2, r11
	str r2, [r12, #8]
	movw r10, #3160
	add r10, r12, r10
	movw r9, #3416
	add r9, r12, r9
	mov r7, #0
2219:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2219b
	movw r10, #3160
	add r10, r12, r10
	movw r4, #0
	movt r4, #32768
	str r4, [r10, #252]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #3160
	add r1, r12, r1
	movw r9, #512
	add r9, r12, r9
2220:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	add r10, r10, #4
	add r1, r1, #4
	cmp r10, r9
	bne 2220b
	sub r2, r3, #1
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
	mov r11, r2
	mov r2, r11
	str r2, [r12, #12]
	mov r2, #0
	str r2, [r12, #16]
	movw r10, #256
	add r10, r12, r10
	ldr r4, [r10, #0]
	str r4, [r12, #32]
	ldr r11, [r12, #68]
	movw r8, #24
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #284
	add r9, r12, r9
2221:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2221b
	mov r4, #0
	str r4, [r10, #0]
	movw r10, #696
	add r10, r12, r10
	movw r9, #728
	add r9, r12, r9
	mov r7, #0
2222:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2222b
	movw r10, #696
	add r10, r12, r10
	movw r4, #0
	movt r4, #32768
	str r4, [r10, #16]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #696
	add r1, r12, r1
	movw r9, #288
	add r9, r12, r9
2223:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	add r10, r10, #4
	add r1, r1, #4
	cmp r10, r9
	bne 2223b
	sub r2, r3, #1
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
	mov r11, r2
	movw r10, #696
	add r10, r12, r10
	movw r9, #728
	add r9, r12, r9
	mov r7, #0
2224:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2224b
	movw r10, #696
	add r10, r12, r10
	movw r4, #1
	movt r4, #0
	str r4, [r10, #20]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #696
	add r1, r12, r1
	movw r9, #288
	add r9, r12, r9
2225:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	add r10, r10, #4
	add r1, r1, #4
	cmp r10, r9
	bne 2225b
	sub r2, r3, #1
	and r2, r2, r11
	str r2, [r12, #20]
	movw r10, #696
	add r10, r12, r10
	movw r9, #728
	add r9, r12, r9
	mov r7, #0
2226:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2226b
	movw r10, #696
	add r10, r12, r10
	movw r4, #0
	movt r4, #32768
	str r4, [r10, #24]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #696
	add r1, r12, r1
	movw r9, #288
	add r9, r12, r9
2227:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	add r10, r10, #4
	add r1, r1, #4
	cmp r10, r9
	bne 2227b
	sub r2, r3, #1
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
	mov r11, r2
	movw r10, #696
	add r10, r12, r10
	movw r9, #728
	add r9, r12, r9
	mov r7, #0
2228:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2228b
	movw r10, #696
	add r10, r12, r10
	movw r4, #1
	movt r4, #0
	str r4, [r10, #28]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #696
	add r1, r12, r1
	movw r9, #288
	add r9, r12, r9
2229:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	add r10, r10, #4
	add r1, r1, #4
	cmp r10, r9
	bne 2229b
	sub r2, r3, #1
	and r2, r2, r11
	str r2, [r12, #24]
	movw r10, #696
	add r10, r12, r10
	movw r9, #728
	add r9, r12, r9
	mov r7, #0
2230:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2230b
	movw r10, #696
	add r10, r12, r10
	movw r4, #0
	movt r4, #32768
	str r4, [r10, #28]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #696
	add r1, r12, r1
	movw r9, #288
	add r9, r12, r9
2231:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	add r10, r10, #4
	add r1, r1, #4
	cmp r10, r9
	bne 2231b
	sub r2, r3, #1
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
	mov r11, r2
	mov r2, r11
	str r2, [r12, #28]
	movw r10, #256
	add r10, r12, r10
	ldr r2, [r10, #0]
	ldr r4, [r12, #32]
	and r2, r2, r4
	and r2, r2, #1
	mov r4, #0
	sub r4, r4, r2
	str r4, [r12, #32]
	ldr r4, [r12, #8]
	ldr r5, [r12, #20]
	and r4, r4, r5
	ldr r5, [r12, #24]
	ldr r7, [r12, #28]
	orr r5, r5, r7
	ldr r7, [r12, #20]
	orr r5, r5, r7
	ldr r7, [r12, #12]
	and r5, r5, r7
	orr r4, r4, r5
	ldr r5, [r12, #16]
	ldr r7, [r12, #28]
	and r5, r5, r7
	orr r4, r4, r5
	ldr r5, [r12, #32]
	and r4, r4, r5
	str r4, [r12, #116]
	ldr r4, [r12, #20]
	and r4, r4, #20
	ldr r2, [r12, #24]
	and r2, r2, #28
	orr r2, r2, r4
	ldr r4, [r12, #28]
	and r4, r4, #32
	orr r2, r2, r4
	ldr r7, [r12, #108]
	movw r6, #65535
	mov r3, #1
	mov r5, r2
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	sub r3, r3, #1
	eor r7, r7, r2
	and r7, r7, r3
	eor r2, r2, r7
	str r2, [r12, #112]
	ldr r4, [r12, #116]
	cmp r4, #0
	beq 2232f
	ldr r11, [r12, #68]
	movw r8, #24
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #284
	add r9, r12, r9
2234:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2234b
	mov r4, #0
	str r4, [r10, #0]
	movw r1, #256
	add r1, r12, r1
	ldr r5, [r1, #0]
	movw r6, #65535
	and r5, r5, r6
	mov r7, r5
	mul r4, r5, r7
	movw r2, #2
	sub r4, r2, r4
	mul r7, r7, r4
	mul r4, r5, r7
	movw r2, #2
	sub r4, r2, r4
	mul r7, r7, r4
	mul r4, r5, r7
	movw r2, #2
	sub r4, r2, r4
	mul r7, r7, r4
	mov r4, #0
	sub r4, r4, r7
	and r4, r4, r6
	str r4, [r12, #0]
	movw r10, #656
	add r10, r12, r10
	movw r9, #688
	add r9, r12, r9
	mov r7, #0
2235:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2235b
	movw r10, #656
	add r10, r12, r10
	movw r4, #2
	movt r4, #0
	str r4, [r10, #0]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #656
	add r1, r12, r1
	movw r8, #616
	add r8, r12, r8
	movw r9, #288
	add r9, r12, r9
2236:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	and r2, r4, r6
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	orr r2, r2, r4, lsl #16
	str r2, [r8, #0]
	add r10, r10, #4
	add r1, r1, #4
	add r8, r8, #4
	cmp r10, r9
	bne 2236b
	movw r11, #14912
	add r11, r12, r11
	mov r4, #0
	sub r4, r4, #1
	mov r3, r4
	movw r8, #24
	add r8, r11, r8
	movw r10, #616
	add r10, r12, r10
	movw r9, #644
	add r9, r12, r9
2237:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2237b
	ldr r11, [r12, #68]
	movw r8, #24
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #284
	add r9, r12, r9
2238:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2238b
	mov r4, #0
	str r4, [r10, #0]
	ldr r11, [r12, #88]
	movw r8, #24
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #604
	add r9, r12, r9
2239:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2239b
	mov r4, #0
	str r4, [r10, #0]
	movw r6, #65535
	mov r3, #1
	movw r10, #576
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r9, #608
	add r9, r12, r9
2240:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	add r10, r10, #4
	add r1, r1, #4
	cmp r10, r9
	bne 2240b
	sub r2, r3, #1
	mov r8, r2
	mov r3, #0
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2241:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 2241b
	mov r4, #0
	sub r4, r4, r3
	orr r4, r4, r3
	lsr r4, r4, #31
	mov r2, #0
	sub r2, r2, r4
	and r2, r2, r8
	ldr r4, [r12, #116]
	and r4, r4, r2
	str r4, [r12, #116]
	ldr r11, [r12, #64]
	movw r8, #252
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #512
	add r9, r12, r9
2242:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2242b
	ldr r11, [r12, #72]
	movw r8, #252
	add r8, r11, r8
	movw r10, #2368
	add r10, r12, r10
	movw r9, #2624
	add r9, r12, r9
2243:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2243b
	ldr r11, [r12, #88]
	movw r8, #24
	add r8, r11, r8
	movw r10, #3160
	add r10, r12, r10
	movw r9, #3188
	add r9, r12, r9
2244:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2244b
	movw r9, #228
	add r9, r10, r9
	mov r4, #0
2245:
	str r4, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2245b
	mov r11, r12
	mov r0, r12
	movw r1, #428
	bl {vg_dsa_pow_32_7}
	mov r12, r11
	movw r11, #14944
	add r11, r12, r11
	mov r4, #0
	sub r4, r4, #1
	mov r3, r4
	movw r8, #252
	add r8, r11, r8
	movw r10, #2632
	add r10, r12, r10
	movw r9, #2888
	add r9, r12, r9
2246:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2246b
	ldr r11, [r12, #68]
	movw r8, #24
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #284
	add r9, r12, r9
2247:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2247b
	mov r4, #0
	str r4, [r10, #0]
	movw r11, #14944
	add r11, r12, r11
	movw lr, #256
	add lr, lr, r11
	mov r2, r11
	sub r3, lr, r11
	mov r11, r12
	mov r0, r12
	movw r1, #92
	bl {vg_dsa_reduce_4}
	mov r12, r11
	movw r11, #14720
	add r11, r12, r11
	mov r4, #0
	sub r4, r4, #1
	mov r3, r4
	movw r8, #24
	add r8, r11, r8
	movw r10, #616
	add r10, r12, r10
	movw r9, #644
	add r9, r12, r9
2248:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2248b
	ldr r11, [r12, #68]
	movw r8, #24
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #284
	add r9, r12, r9
2249:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2249b
	mov r4, #0
	str r4, [r10, #0]
	ldr r11, [r12, #88]
	movw r8, #24
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #604
	add r9, r12, r9
2250:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2250b
	mov r4, #0
	str r4, [r10, #0]
	movw r11, #14912
	add r11, r12, r11
	movw r8, #24
	add r8, r11, r8
	movw r10, #696
	add r10, r12, r10
	movw r9, #724
	add r9, r12, r9
2251:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2251b
	mov r4, #0
	str r4, [r10, #0]
	mov r11, r12
	mov r0, r12
	movw r1, #92
	bl {vg_dsa_pow_4_7}
	mov r12, r11
	movw r11, #14784
	add r11, r12, r11
	mov r4, #0
	sub r4, r4, #1
	mov r3, r4
	movw r8, #24
	add r8, r11, r8
	movw r10, #616
	add r10, r12, r10
	movw r9, #644
	add r9, r12, r9
2252:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2252b
	ldr r11, [r12, #68]
	movw r8, #24
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #284
	add r9, r12, r9
2253:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2253b
	mov r4, #0
	str r4, [r10, #0]
	ldr r11, [r12, #80]
	movw r8, #24
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #604
	add r9, r12, r9
2254:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2254b
	mov r4, #0
	str r4, [r10, #0]
	movw r11, #14720
	add r11, r12, r11
	movw r8, #24
	add r8, r11, r8
	movw r10, #696
	add r10, r12, r10
	movw r9, #724
	add r9, r12, r9
2255:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2255b
	mov r4, #0
	str r4, [r10, #0]
	mov r11, r12
	mov r0, r12
	movw r1, #92
	bl {vg_dsa_mulmod_4}
	mov r12, r11
	movw r11, #14816
	add r11, r12, r11
	mov r4, #0
	sub r4, r4, #1
	mov r3, r4
	movw r8, #24
	add r8, r11, r8
	movw r10, #616
	add r10, r12, r10
	movw r9, #644
	add r9, r12, r9
2256:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2256b
	ldr r11, [r12, #68]
	movw r8, #24
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #284
	add r9, r12, r9
2257:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2257b
	mov r4, #0
	str r4, [r10, #0]
	ldr r11, [r12, #92]
	ldr lr, [r12, #112]
	add lr, lr, r11
	mov r2, r11
	sub r3, lr, r11
	mov r11, r12
	mov r0, r12
	movw r1, #92
	bl {vg_dsa_reduce_4}
	mov r12, r11
	movw r11, #14880
	add r11, r12, r11
	mov r4, #0
	sub r4, r4, #1
	mov r3, r4
	movw r8, #24
	add r8, r11, r8
	movw r10, #616
	add r10, r12, r10
	movw r9, #644
	add r9, r12, r9
2258:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2258b
	ldr r11, [r12, #68]
	movw r8, #24
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #284
	add r9, r12, r9
2259:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2259b
	mov r4, #0
	str r4, [r10, #0]
	movw r1, #256
	add r1, r12, r1
	ldr r5, [r1, #0]
	movw r6, #65535
	and r5, r5, r6
	mov r7, r5
	mul r4, r5, r7
	movw r2, #2
	sub r4, r2, r4
	mul r7, r7, r4
	mul r4, r5, r7
	movw r2, #2
	sub r4, r2, r4
	mul r7, r7, r4
	mul r4, r5, r7
	movw r2, #2
	sub r4, r2, r4
	mul r7, r7, r4
	mov r4, #0
	sub r4, r4, r7
	and r4, r4, r6
	str r4, [r12, #0]
	movw r11, #14880
	add r11, r12, r11
	movw r8, #24
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #604
	add r9, r12, r9
2260:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2260b
	mov r4, #0
	str r4, [r10, #0]
	movw r11, #14816
	add r11, r12, r11
	movw r8, #24
	add r8, r11, r8
	movw r10, #696
	add r10, r12, r10
	movw r9, #724
	add r9, r12, r9
2261:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2261b
	mov r4, #0
	str r4, [r10, #0]
	movw r6, #65535
	mov r3, #0
	movw r10, #576
	add r10, r12, r10
	movw r0, #696
	add r0, r12, r0
	movw r8, #336
	add r8, r12, r8
	movw r9, #608
	add r9, r12, r9
2262:
	ldr r7, [r10, #0]
	ldr r2, [r0, #0]
	and r4, r7, r6
	and r5, r2, r6
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r8, #0]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r2, #16
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r8, #4]
	lsr r3, r4, #16
	add r10, r10, #4
	add r0, r0, #4
	add r8, r8, #8
	cmp r10, r9
	bne 2262b
	str r3, [r8, #0]
	movw r6, #65535
	mov r3, #1
	movw r10, #336
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r8, #296
	add r8, r12, r8
	movw r9, #288
	add r9, r12, r9
2263:
	ldr r7, [r1, #0]
	ldr r5, [r10, #0]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r2, r5, r6
	ldr r5, [r10, #4]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r2, r2, r5, lsl #16
	str r2, [r8, #0]
	add r10, r10, #8
	add r1, r1, #4
	add r8, r8, #4
	cmp r1, r9
	bne 2263b
	ldr r5, [r10, #0]
	add r3, r3, r5
	mov r4, #0
	sub r3, r4, r3
	movw r10, #336
	add r10, r12, r10
	movw r8, #296
	add r8, r12, r8
	movw r1, #616
	add r1, r12, r1
	movw r9, #328
	add r9, r12, r9
2264:
	ldr r5, [r10, #0]
	ldr r7, [r10, #4]
	orr r5, r5, r7, lsl #16
	ldr r7, [r8, #0]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [r1, #0]
	add r10, r10, #8
	add r8, r8, #4
	add r1, r1, #4
	cmp r8, r9
	bne 2264b
	movw r11, #14848
	add r11, r12, r11
	mov r4, #0
	sub r4, r4, #1
	mov r3, r4
	movw r8, #24
	add r8, r11, r8
	movw r10, #616
	add r10, r12, r10
	movw r9, #644
	add r9, r12, r9
2265:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2265b
	ldr r11, [r12, #68]
	movw r8, #24
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #284
	add r9, r12, r9
2266:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2266b
	mov r4, #0
	str r4, [r10, #0]
	movw r11, #14784
	add r11, r12, r11
	movw r8, #24
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #604
	add r9, r12, r9
2267:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2267b
	mov r4, #0
	str r4, [r10, #0]
	movw r11, #14848
	add r11, r12, r11
	movw r8, #24
	add r8, r11, r8
	movw r10, #696
	add r10, r12, r10
	movw r9, #724
	add r9, r12, r9
2268:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2268b
	mov r4, #0
	str r4, [r10, #0]
	mov r11, r12
	mov r0, r12
	movw r1, #92
	bl {vg_dsa_mulmod_4}
	mov r12, r11
	movw r11, #14752
	add r11, r12, r11
	mov r4, #0
	sub r4, r4, #1
	mov r3, r4
	movw r8, #24
	add r8, r11, r8
	movw r10, #616
	add r10, r12, r10
	movw r9, #644
	add r9, r12, r9
2269:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2269b
	movw r11, #14720
	add r11, r12, r11
	movw r8, #24
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #604
	add r9, r12, r9
2270:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2270b
	mov r4, #0
	str r4, [r10, #0]
	mov r3, #0
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2271:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 2271b
	mov r4, #0
	sub r4, r4, r3
	orr r4, r4, r3
	lsr r4, r4, #31
	mov r2, #0
	sub r2, r2, r4
	ldr r4, [r12, #116]
	and r4, r4, r2
	str r4, [r12, #116]
	movw r11, #14752
	add r11, r12, r11
	movw r8, #24
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #604
	add r9, r12, r9
2272:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2272b
	mov r4, #0
	str r4, [r10, #0]
	mov r3, #0
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2273:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 2273b
	mov r4, #0
	sub r4, r4, r3
	orr r4, r4, r3
	lsr r4, r4, #31
	mov r2, #0
	sub r2, r2, r4
	ldr r4, [r12, #116]
	and r4, r4, r2
	str r4, [r12, #116]
	movw r11, #14720
	add r11, r12, r11
	movw r8, #24
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #604
	add r9, r12, r9
2274:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2274b
	mov r4, #0
	str r4, [r10, #0]
	ldr r11, [r12, #96]
	ldr r3, [r12, #116]
	movw r8, #24
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #604
	add r9, r12, r9
2275:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2275b
	movw r11, #14752
	add r11, r12, r11
	movw r8, #24
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #604
	add r9, r12, r9
2276:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2276b
	mov r4, #0
	str r4, [r10, #0]
	ldr r11, [r12, #96]
	movw r4, #28
	add r11, r11, r4
	ldr r3, [r12, #116]
	movw r8, #24
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #604
	add r9, r12, r9
2277:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2277b
	ldr r0, [r12, #116]
	and r0, r0, #1
	b 2233f
2232:
	ldr r11, [r12, #96]
	ldr r4, [r12, #104]
	add lr, r11, r4
	add lr, lr, r4
	mov r4, #0
2278:
	strb r4, [r11, #0]
	add r11, r11, #1
	cmp r11, lr
	bne 2278b
	mov r0, #0
2233:
27:
	b 23f
22:
	ldr r11, [r12, #64]
	movw r8, #124
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #384
	add r9, r12, r9
2279:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2279b
	movw r10, #1752
	add r10, r12, r10
	movw r9, #1880
	add r9, r12, r9
	mov r7, #0
2280:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2280b
	movw r10, #1752
	add r10, r12, r10
	movw r4, #0
	movt r4, #32768
	str r4, [r10, #124]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #1752
	add r1, r12, r1
	movw r9, #384
	add r9, r12, r9
2281:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	add r10, r10, #4
	add r1, r1, #4
	cmp r10, r9
	bne 2281b
	sub r2, r3, #1
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
	mov r11, r2
	mov r2, r11
	str r2, [r12, #8]
	mov r2, #0
	str r2, [r12, #12]
	mov r2, #0
	str r2, [r12, #16]
	movw r10, #256
	add r10, r12, r10
	ldr r4, [r10, #0]
	str r4, [r12, #32]
	ldr r11, [r12, #68]
	movw r8, #16
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #276
	add r9, r12, r9
2282:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2282b
	mov r4, #0
	str r4, [r10, #0]
	movw r10, #608
	add r10, r12, r10
	movw r9, #632
	add r9, r12, r9
	mov r7, #0
2283:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2283b
	movw r10, #608
	add r10, r12, r10
	movw r4, #0
	movt r4, #32768
	str r4, [r10, #16]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #608
	add r1, r12, r1
	movw r9, #280
	add r9, r12, r9
2284:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	add r10, r10, #4
	add r1, r1, #4
	cmp r10, r9
	bne 2284b
	sub r2, r3, #1
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
	mov r11, r2
	movw r10, #608
	add r10, r12, r10
	movw r9, #632
	add r9, r12, r9
	mov r7, #0
2285:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2285b
	movw r10, #608
	add r10, r12, r10
	movw r4, #1
	movt r4, #0
	str r4, [r10, #20]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #608
	add r1, r12, r1
	movw r9, #280
	add r9, r12, r9
2286:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	add r10, r10, #4
	add r1, r1, #4
	cmp r10, r9
	bne 2286b
	sub r2, r3, #1
	and r2, r2, r11
	str r2, [r12, #20]
	mov r2, #0
	str r2, [r12, #24]
	mov r2, #0
	str r2, [r12, #28]
	movw r10, #256
	add r10, r12, r10
	ldr r2, [r10, #0]
	ldr r4, [r12, #32]
	and r2, r2, r4
	and r2, r2, #1
	mov r4, #0
	sub r4, r4, r2
	str r4, [r12, #32]
	ldr r4, [r12, #8]
	ldr r5, [r12, #20]
	and r4, r4, r5
	ldr r5, [r12, #24]
	ldr r7, [r12, #28]
	orr r5, r5, r7
	ldr r7, [r12, #20]
	orr r5, r5, r7
	ldr r7, [r12, #12]
	and r5, r5, r7
	orr r4, r4, r5
	ldr r5, [r12, #16]
	ldr r7, [r12, #28]
	and r5, r5, r7
	orr r4, r4, r5
	ldr r5, [r12, #32]
	and r4, r4, r5
	str r4, [r12, #116]
	ldr r4, [r12, #20]
	and r4, r4, #20
	ldr r2, [r12, #24]
	and r2, r2, #28
	orr r2, r2, r4
	ldr r4, [r12, #28]
	and r4, r4, #32
	orr r2, r2, r4
	ldr r7, [r12, #108]
	movw r6, #65535
	mov r3, #1
	mov r5, r2
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	sub r3, r3, #1
	eor r7, r7, r2
	and r7, r7, r3
	eor r2, r2, r7
	str r2, [r12, #112]
	ldr r4, [r12, #116]
	cmp r4, #0
	beq 2287f
	ldr r11, [r12, #68]
	movw r8, #16
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #276
	add r9, r12, r9
2289:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2289b
	mov r4, #0
	str r4, [r10, #0]
	movw r1, #256
	add r1, r12, r1
	ldr r5, [r1, #0]
	movw r6, #65535
	and r5, r5, r6
	mov r7, r5
	mul r4, r5, r7
	movw r2, #2
	sub r4, r2, r4
	mul r7, r7, r4
	mul r4, r5, r7
	movw r2, #2
	sub r4, r2, r4
	mul r7, r7, r4
	mul r4, r5, r7
	movw r2, #2
	sub r4, r2, r4
	mul r7, r7, r4
	mov r4, #0
	sub r4, r4, r7
	and r4, r4, r6
	str r4, [r12, #0]
	movw r10, #576
	add r10, r12, r10
	movw r9, #600
	add r9, r12, r9
	mov r7, #0
2290:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2290b
	movw r10, #576
	add r10, r12, r10
	movw r4, #2
	movt r4, #0
	str r4, [r10, #0]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #576
	add r1, r12, r1
	movw r8, #544
	add r8, r12, r8
	movw r9, #280
	add r9, r12, r9
2291:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	and r2, r4, r6
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	orr r2, r2, r4, lsl #16
	str r2, [r8, #0]
	add r10, r10, #4
	add r1, r1, #4
	add r8, r8, #4
	cmp r10, r9
	bne 2291b
	movw r11, #14912
	add r11, r12, r11
	mov r4, #0
	sub r4, r4, #1
	mov r3, r4
	movw r8, #16
	add r8, r11, r8
	movw r10, #544
	add r10, r12, r10
	movw r9, #564
	add r9, r12, r9
2292:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2292b
	ldr r11, [r12, #68]
	movw r8, #16
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #276
	add r9, r12, r9
2293:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2293b
	mov r4, #0
	str r4, [r10, #0]
	ldr r11, [r12, #88]
	movw r8, #16
	add r8, r11, r8
	movw r10, #512
	add r10, r12, r10
	movw r9, #532
	add r9, r12, r9
2294:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2294b
	mov r4, #0
	str r4, [r10, #0]
	movw r6, #65535
	mov r3, #1
	movw r10, #512
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r9, #536
	add r9, r12, r9
2295:
	ldr r7, [r10, #0]
	ldr r5, [r1, #0]
	and r4, r7, r6
	add r4, r4, r6
	and r0, r5, r6
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	add r10, r10, #4
	add r1, r1, #4
	cmp r10, r9
	bne 2295b
	sub r2, r3, #1
	mov r8, r2
	mov r3, #0
	movw r10, #512
	add r10, r12, r10
	movw r9, #536
	add r9, r12, r9
2296:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 2296b
	mov r4, #0
	sub r4, r4, r3
	orr r4, r4, r3
	lsr r4, r4, #31
	mov r2, #0
	sub r2, r2, r4
	and r2, r2, r8
	ldr r4, [r12, #116]
	and r4, r4, r2
	str r4, [r12, #116]
	ldr r11, [r12, #64]
	movw r8, #124
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #384
	add r9, r12, r9
2297:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2297b
	ldr r11, [r12, #72]
	movw r8, #124
	add r8, r11, r8
	movw r10, #1344
	add r10, r12, r10
	movw r9, #1472
	add r9, r12, r9
2298:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2298b
	ldr r11, [r12, #88]
	movw r8, #16
	add r8, r11, r8
	movw r10, #1752
	add r10, r12, r10
	movw r9, #1772
	add r9, r12, r9
2299:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2299b
	movw r9, #108
	add r9, r10, r9
	mov r4, #0
2300:
	str r4, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2300b
	mov r11, r12
	mov r0, r12
	movw r1, #236
	bl {vg_dsa_pow_16_5}
	mov r12, r11
	movw r11, #14944
	add r11, r12, r11
	mov r4, #0
	sub r4, r4, #1
	mov r3, r4
	movw r8, #124
	add r8, r11, r8
	movw r10, #1480
	add r10, r12, r10
	movw r9, #1608
	add r9, r12, r9
2301:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2301b
	ldr r11, [r12, #68]
	movw r8, #16
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #276
	add r9, r12, r9
2302:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2302b
	mov r4, #0
	str r4, [r10, #0]
	movw r11, #14944
	add r11, r12, r11
	movw lr, #128
	add lr, lr, r11
	mov r2, r11
	sub r3, lr, r11
	mov r11, r12
	mov r0, r12
	movw r1, #80
	bl {vg_dsa_reduce_3}
	mov r12, r11
	movw r11, #14720
	add r11, r12, r11
	mov r4, #0
	sub r4, r4, #1
	mov r3, r4
	movw r8, #16
	add r8, r11, r8
	movw r10, #544
	add r10, r12, r10
	movw r9, #564
	add r9, r12, r9
2303:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2303b
	ldr r11, [r12, #68]
	movw r8, #16
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #276
	add r9, r12, r9
2304:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2304b
	mov r4, #0
	str r4, [r10, #0]
	ldr r11, [r12, #88]
	movw r8, #16
	add r8, r11, r8
	movw r10, #512
	add r10, r12, r10
	movw r9, #532
	add r9, r12, r9
2305:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2305b
	mov r4, #0
	str r4, [r10, #0]
	movw r11, #14912
	add r11, r12, r11
	movw r8, #16
	add r8, r11, r8
	movw r10, #608
	add r10, r12, r10
	movw r9, #628
	add r9, r12, r9
2306:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2306b
	mov r4, #0
	str r4, [r10, #0]
	mov r11, r12
	mov r0, r12
	movw r1, #80
	bl {vg_dsa_pow_3_5}
	mov r12, r11
	movw r11, #14784
	add r11, r12, r11
	mov r4, #0
	sub r4, r4, #1
	mov r3, r4
	movw r8, #16
	add r8, r11, r8
	movw r10, #544
	add r10, r12, r10
	movw r9, #564
	add r9, r12, r9
2307:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2307b
	ldr r11, [r12, #68]
	movw r8, #16
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #276
	add r9, r12, r9
2308:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2308b
	mov r4, #0
	str r4, [r10, #0]
	ldr r11, [r12, #80]
	movw r8, #16
	add r8, r11, r8
	movw r10, #512
	add r10, r12, r10
	movw r9, #532
	add r9, r12, r9
2309:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2309b
	mov r4, #0
	str r4, [r10, #0]
	movw r11, #14720
	add r11, r12, r11
	movw r8, #16
	add r8, r11, r8
	movw r10, #608
	add r10, r12, r10
	movw r9, #628
	add r9, r12, r9
2310:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2310b
	mov r4, #0
	str r4, [r10, #0]
	mov r11, r12
	mov r0, r12
	movw r1, #80
	bl {vg_dsa_mulmod_3}
	mov r12, r11
	movw r11, #14816
	add r11, r12, r11
	mov r4, #0
	sub r4, r4, #1
	mov r3, r4
	movw r8, #16
	add r8, r11, r8
	movw r10, #544
	add r10, r12, r10
	movw r9, #564
	add r9, r12, r9
2311:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2311b
	ldr r11, [r12, #68]
	movw r8, #16
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #276
	add r9, r12, r9
2312:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2312b
	mov r4, #0
	str r4, [r10, #0]
	ldr r11, [r12, #92]
	ldr lr, [r12, #112]
	add lr, lr, r11
	mov r2, r11
	sub r3, lr, r11
	mov r11, r12
	mov r0, r12
	movw r1, #80
	bl {vg_dsa_reduce_3}
	mov r12, r11
	movw r11, #14880
	add r11, r12, r11
	mov r4, #0
	sub r4, r4, #1
	mov r3, r4
	movw r8, #16
	add r8, r11, r8
	movw r10, #544
	add r10, r12, r10
	movw r9, #564
	add r9, r12, r9
2313:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2313b
	ldr r11, [r12, #68]
	movw r8, #16
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #276
	add r9, r12, r9
2314:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2314b
	mov r4, #0
	str r4, [r10, #0]
	movw r1, #256
	add r1, r12, r1
	ldr r5, [r1, #0]
	movw r6, #65535
	and r5, r5, r6
	mov r7, r5
	mul r4, r5, r7
	movw r2, #2
	sub r4, r2, r4
	mul r7, r7, r4
	mul r4, r5, r7
	movw r2, #2
	sub r4, r2, r4
	mul r7, r7, r4
	mul r4, r5, r7
	movw r2, #2
	sub r4, r2, r4
	mul r7, r7, r4
	mov r4, #0
	sub r4, r4, r7
	and r4, r4, r6
	str r4, [r12, #0]
	movw r11, #14880
	add r11, r12, r11
	movw r8, #16
	add r8, r11, r8
	movw r10, #512
	add r10, r12, r10
	movw r9, #532
	add r9, r12, r9
2315:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2315b
	mov r4, #0
	str r4, [r10, #0]
	movw r11, #14816
	add r11, r12, r11
	movw r8, #16
	add r8, r11, r8
	movw r10, #608
	add r10, r12, r10
	movw r9, #628
	add r9, r12, r9
2316:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2316b
	mov r4, #0
	str r4, [r10, #0]
	movw r6, #65535
	mov r3, #0
	movw r10, #512
	add r10, r12, r10
	movw r0, #608
	add r0, r12, r0
	movw r8, #320
	add r8, r12, r8
	movw r9, #536
	add r9, r12, r9
2317:
	ldr r7, [r10, #0]
	ldr r2, [r0, #0]
	and r4, r7, r6
	and r5, r2, r6
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r8, #0]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r2, #16
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r8, #4]
	lsr r3, r4, #16
	add r10, r10, #4
	add r0, r0, #4
	add r8, r8, #8
	cmp r10, r9
	bne 2317b
	str r3, [r8, #0]
	movw r6, #65535
	mov r3, #1
	movw r10, #320
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r8, #288
	add r8, r12, r8
	movw r9, #280
	add r9, r12, r9
2318:
	ldr r7, [r1, #0]
	ldr r5, [r10, #0]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r2, r5, r6
	ldr r5, [r10, #4]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r2, r2, r5, lsl #16
	str r2, [r8, #0]
	add r10, r10, #8
	add r1, r1, #4
	add r8, r8, #4
	cmp r1, r9
	bne 2318b
	ldr r5, [r10, #0]
	add r3, r3, r5
	mov r4, #0
	sub r3, r4, r3
	movw r10, #320
	add r10, r12, r10
	movw r8, #288
	add r8, r12, r8
	movw r1, #544
	add r1, r12, r1
	movw r9, #312
	add r9, r12, r9
2319:
	ldr r5, [r10, #0]
	ldr r7, [r10, #4]
	orr r5, r5, r7, lsl #16
	ldr r7, [r8, #0]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [r1, #0]
	add r10, r10, #8
	add r8, r8, #4
	add r1, r1, #4
	cmp r8, r9
	bne 2319b
	movw r11, #14848
	add r11, r12, r11
	mov r4, #0
	sub r4, r4, #1
	mov r3, r4
	movw r8, #16
	add r8, r11, r8
	movw r10, #544
	add r10, r12, r10
	movw r9, #564
	add r9, r12, r9
2320:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2320b
	ldr r11, [r12, #68]
	movw r8, #16
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #276
	add r9, r12, r9
2321:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2321b
	mov r4, #0
	str r4, [r10, #0]
	movw r11, #14784
	add r11, r12, r11
	movw r8, #16
	add r8, r11, r8
	movw r10, #512
	add r10, r12, r10
	movw r9, #532
	add r9, r12, r9
2322:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2322b
	mov r4, #0
	str r4, [r10, #0]
	movw r11, #14848
	add r11, r12, r11
	movw r8, #16
	add r8, r11, r8
	movw r10, #608
	add r10, r12, r10
	movw r9, #628
	add r9, r12, r9
2323:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2323b
	mov r4, #0
	str r4, [r10, #0]
	mov r11, r12
	mov r0, r12
	movw r1, #80
	bl {vg_dsa_mulmod_3}
	mov r12, r11
	movw r11, #14752
	add r11, r12, r11
	mov r4, #0
	sub r4, r4, #1
	mov r3, r4
	movw r8, #16
	add r8, r11, r8
	movw r10, #544
	add r10, r12, r10
	movw r9, #564
	add r9, r12, r9
2324:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2324b
	movw r11, #14720
	add r11, r12, r11
	movw r8, #16
	add r8, r11, r8
	movw r10, #512
	add r10, r12, r10
	movw r9, #532
	add r9, r12, r9
2325:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2325b
	mov r4, #0
	str r4, [r10, #0]
	mov r3, #0
	movw r10, #512
	add r10, r12, r10
	movw r9, #536
	add r9, r12, r9
2326:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 2326b
	mov r4, #0
	sub r4, r4, r3
	orr r4, r4, r3
	lsr r4, r4, #31
	mov r2, #0
	sub r2, r2, r4
	ldr r4, [r12, #116]
	and r4, r4, r2
	str r4, [r12, #116]
	movw r11, #14752
	add r11, r12, r11
	movw r8, #16
	add r8, r11, r8
	movw r10, #512
	add r10, r12, r10
	movw r9, #532
	add r9, r12, r9
2327:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2327b
	mov r4, #0
	str r4, [r10, #0]
	mov r3, #0
	movw r10, #512
	add r10, r12, r10
	movw r9, #536
	add r9, r12, r9
2328:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 2328b
	mov r4, #0
	sub r4, r4, r3
	orr r4, r4, r3
	lsr r4, r4, #31
	mov r2, #0
	sub r2, r2, r4
	ldr r4, [r12, #116]
	and r4, r4, r2
	str r4, [r12, #116]
	movw r11, #14720
	add r11, r12, r11
	movw r8, #16
	add r8, r11, r8
	movw r10, #512
	add r10, r12, r10
	movw r9, #532
	add r9, r12, r9
2329:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2329b
	mov r4, #0
	str r4, [r10, #0]
	ldr r11, [r12, #96]
	ldr r3, [r12, #116]
	movw r8, #16
	add r8, r11, r8
	movw r10, #512
	add r10, r12, r10
	movw r9, #532
	add r9, r12, r9
2330:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2330b
	movw r11, #14752
	add r11, r12, r11
	movw r8, #16
	add r8, r11, r8
	movw r10, #512
	add r10, r12, r10
	movw r9, #532
	add r9, r12, r9
2331:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2331b
	mov r4, #0
	str r4, [r10, #0]
	ldr r11, [r12, #96]
	movw r4, #20
	add r11, r11, r4
	ldr r3, [r12, #116]
	movw r8, #16
	add r8, r11, r8
	movw r10, #512
	add r10, r12, r10
	movw r9, #532
	add r9, r12, r9
2332:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2332b
	ldr r0, [r12, #116]
	and r0, r0, #1
	b 2288f
2287:
	ldr r11, [r12, #96]
	ldr r4, [r12, #104]
	add lr, r11, r4
	add lr, lr, r4
	mov r4, #0
2333:
	strb r4, [r11, #0]
	add r11, r11, #1
	cmp r11, lr
	bne 2333b
	mov r0, #0
2288:
23:
	ldr r4, [r12, #128]
	ldr r5, [r12, #132]
	ldr r6, [r12, #136]
	ldr r7, [r12, #140]
	ldr r8, [r12, #144]
	ldr r9, [r12, #148]
	ldr r10, [r12, #152]
	ldr r11, [r12, #156]
	ldr lr, [r12, #160]
	bx lr
