// The functions of `src/internal/vg_dsa_sign.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_dsa_sign:
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
	ldr r11, [r12, #64]
	movw r8, #252
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #512
	add r9, r12, r9
235:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 235b
	ldr r11, [r12, #72]
	movw r8, #252
	add r8, r11, r8
	movw r10, #2368
	add r10, r12, r10
	movw r9, #2624
	add r9, r12, r9
236:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 236b
	movw r6, #65535
	mov r3, #1
	movw r10, #2368
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r9, #2624
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
	lsr r4, r7, #16
	add r4, r4, r6
	lsr r0, r5, #16
	sub r4, r4, r0
	add r4, r4, r3
	lsr r3, r4, #16
	add r10, r10, #4
	add r1, r1, #4
	cmp r10, r9
	bne 237b
	sub r2, r3, #1
	mov r8, r2
	mov r3, #0
	movw r10, #2368
	add r10, r12, r10
	movw r9, #2624
	add r9, r12, r9
238:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 238b
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
	movw r10, #2896
	add r10, r12, r10
	movw r9, #3152
	add r9, r12, r9
	mov r7, #0
239:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 239b
	movw r10, #2896
	add r10, r12, r10
	movw r4, #2
	movt r4, #0
	str r4, [r10, #0]
	movw r6, #65535
	mov r3, #1
	movw r10, #2368
	add r10, r12, r10
	movw r1, #2896
	add r1, r12, r1
	movw r9, #2624
	add r9, r12, r9
240:
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
	bne 240b
	sub r2, r3, #1
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
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
241:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 241b
	ldr r11, [r12, #76]
	movw r8, #252
	add r8, r11, r8
	movw r10, #2368
	add r10, r12, r10
	movw r9, #2624
	add r9, r12, r9
242:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 242b
	movw r6, #65535
	mov r3, #1
	movw r10, #2368
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r9, #2624
	add r9, r12, r9
243:
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
	bne 243b
	sub r2, r3, #1
	mov r8, r2
	mov r3, #0
	movw r10, #2368
	add r10, r12, r10
	movw r9, #2624
	add r9, r12, r9
244:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 244b
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
	movw r10, #2896
	add r10, r12, r10
	movw r9, #3152
	add r9, r12, r9
	mov r7, #0
245:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 245b
	movw r10, #2896
	add r10, r12, r10
	movw r4, #2
	movt r4, #0
	str r4, [r10, #0]
	movw r6, #65535
	mov r3, #1
	movw r10, #2368
	add r10, r12, r10
	movw r1, #2896
	add r1, r12, r1
	movw r9, #2624
	add r9, r12, r9
246:
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
	bne 246b
	sub r2, r3, #1
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
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
247:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 247b
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
	movw r10, #2896
	add r10, r12, r10
	movw r9, #3152
	add r9, r12, r9
	mov r7, #0
248:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 248b
	movw r10, #2896
	add r10, r12, r10
	movw r4, #1
	movt r4, #0
	str r4, [r10, #0]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #2896
	add r1, r12, r1
	movw r8, #2632
	add r8, r12, r8
	movw r9, #512
	add r9, r12, r9
249:
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
	bne 249b
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
250:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 250b
	ldr r11, [r12, #68]
	movw r8, #16
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #276
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
252:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 252b
	movw r11, #14816
	add r11, r12, r11
	movw r8, #16
	add r8, r11, r8
	movw r10, #512
	add r10, r12, r10
	movw r9, #532
	add r9, r12, r9
253:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 253b
	mov r4, #0
	str r4, [r10, #0]
	mov r3, #0
	movw r10, #512
	add r10, r12, r10
	movw r9, #536
	add r9, r12, r9
254:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 254b
	mov r4, #0
	sub r4, r4, r3
	orr r4, r4, r3
	lsr r4, r4, #31
	mov r2, #0
	sub r2, r2, r4
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
	ldr r4, [r12, #116]
	and r4, r4, r2
	str r4, [r12, #116]
	ldr r11, [r12, #68]
	movw r8, #16
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #276
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
256:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 256b
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
257:
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
	bne 257b
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
258:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 258b
	ldr r11, [r12, #64]
	movw r8, #252
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #512
	add r9, r12, r9
259:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 259b
	ldr r11, [r12, #72]
	movw r8, #252
	add r8, r11, r8
	movw r10, #2368
	add r10, r12, r10
	movw r9, #2624
	add r9, r12, r9
260:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 260b
	ldr r11, [r12, #68]
	movw r8, #16
	add r8, r11, r8
	movw r10, #3160
	add r10, r12, r10
	movw r9, #3180
	add r9, r12, r9
261:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 261b
	movw r9, #236
	add r9, r10, r9
	mov r4, #0
262:
	str r4, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 262b
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
263:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 263b
	movw r11, #14944
	add r11, r12, r11
	movw r8, #252
	add r8, r11, r8
	movw r10, #2368
	add r10, r12, r10
	movw r9, #2624
	add r9, r12, r9
264:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 264b
	movw r10, #3160
	add r10, r12, r10
	movw r9, #3416
	add r9, r12, r9
	mov r7, #0
265:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 265b
	movw r10, #3160
	add r10, r12, r10
	movw r4, #1
	movt r4, #0
	str r4, [r10, #0]
	movw r6, #65535
	mov r3, #1
	movw r10, #2368
	add r10, r12, r10
	movw r1, #3160
	add r1, r12, r1
	movw r9, #2624
	add r9, r12, r9
266:
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
	bne 266b
	sub r2, r3, #1
	mov r8, r2
	movw r6, #65535
	mov r3, #1
	movw r10, #3160
	add r10, r12, r10
	movw r1, #2368
	add r1, r12, r1
	movw r9, #3416
	add r9, r12, r9
267:
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
	bne 267b
	sub r2, r3, #1
	orr r2, r2, r8
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
	ldr r4, [r12, #116]
	and r4, r4, r2
	str r4, [r12, #116]
	ldr r11, [r12, #68]
	movw r8, #16
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #276
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
	ldr r11, [r12, #80]
	movw r8, #16
	add r8, r11, r8
	movw r10, #512
	add r10, r12, r10
	movw r9, #532
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
	movw r6, #65535
	mov r3, #1
	movw r10, #512
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r9, #536
	add r9, r12, r9
270:
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
	bne 270b
	sub r2, r3, #1
	mov r8, r2
	mov r3, #0
	movw r10, #512
	add r10, r12, r10
	movw r9, #536
	add r9, r12, r9
271:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 271b
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
	ldr r11, [r12, #68]
	movw r8, #16
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #276
	add r9, r12, r9
272:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 272b
	mov r4, #0
	str r4, [r10, #0]
	ldr r11, [r12, #88]
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
	movw r6, #65535
	mov r3, #1
	movw r10, #512
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r9, #536
	add r9, r12, r9
274:
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
	bne 274b
	sub r2, r3, #1
	mov r8, r2
	mov r3, #0
	movw r10, #512
	add r10, r12, r10
	movw r9, #536
	add r9, r12, r9
275:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 275b
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
276:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 276b
	ldr r11, [r12, #72]
	movw r8, #252
	add r8, r11, r8
	movw r10, #2368
	add r10, r12, r10
	movw r9, #2624
	add r9, r12, r9
277:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 277b
	ldr r11, [r12, #80]
	movw r8, #16
	add r8, r11, r8
	movw r10, #3160
	add r10, r12, r10
	movw r9, #3180
	add r9, r12, r9
278:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 278b
	movw r9, #236
	add r9, r10, r9
	mov r4, #0
279:
	str r4, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 279b
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
280:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 280b
	movw r11, #14944
	add r11, r12, r11
	movw r8, #252
	add r8, r11, r8
	movw r10, #2368
	add r10, r12, r10
	movw r9, #2624
	add r9, r12, r9
281:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 281b
	ldr r11, [r12, #76]
	movw r8, #252
	add r8, r11, r8
	movw r10, #3160
	add r10, r12, r10
	movw r9, #3416
	add r9, r12, r9
282:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 282b
	movw r6, #65535
	mov r3, #1
	movw r10, #2368
	add r10, r12, r10
	movw r1, #3160
	add r1, r12, r1
	movw r9, #2624
	add r9, r12, r9
283:
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
	bne 283b
	sub r2, r3, #1
	mov r8, r2
	movw r6, #65535
	mov r3, #1
	movw r10, #3160
	add r10, r12, r10
	movw r1, #2368
	add r1, r12, r1
	movw r9, #3416
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
	orr r2, r2, r8
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
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
285:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 285b
	ldr r11, [r12, #72]
	movw r8, #252
	add r8, r11, r8
	movw r10, #2368
	add r10, r12, r10
	movw r9, #2624
	add r9, r12, r9
286:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 286b
	ldr r11, [r12, #88]
	movw r8, #16
	add r8, r11, r8
	movw r10, #3160
	add r10, r12, r10
	movw r9, #3180
	add r9, r12, r9
287:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 287b
	movw r9, #236
	add r9, r10, r9
	mov r4, #0
288:
	str r4, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 288b
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
289:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 289b
	ldr r11, [r12, #68]
	movw r8, #16
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #276
	add r9, r12, r9
290:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 290b
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
291:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 291b
	ldr r11, [r12, #68]
	movw r8, #16
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #276
	add r9, r12, r9
292:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 292b
	mov r4, #0
	str r4, [r10, #0]
	ldr r11, [r12, #88]
	movw r8, #16
	add r8, r11, r8
	movw r10, #512
	add r10, r12, r10
	movw r9, #532
	add r9, r12, r9
293:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 293b
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
294:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 294b
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
295:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 295b
	ldr r11, [r12, #68]
	movw r8, #16
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #276
	add r9, r12, r9
296:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 296b
	mov r4, #0
	str r4, [r10, #0]
	ldr r11, [r12, #80]
	movw r8, #16
	add r8, r11, r8
	movw r10, #512
	add r10, r12, r10
	movw r9, #532
	add r9, r12, r9
297:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 297b
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
298:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 298b
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
299:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 299b
	ldr r11, [r12, #68]
	movw r8, #16
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #276
	add r9, r12, r9
2100:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2100b
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
2101:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2101b
	ldr r11, [r12, #68]
	movw r8, #16
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #276
	add r9, r12, r9
2102:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2102b
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
2103:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2103b
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
2104:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2104b
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
2105:
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
	bne 2105b
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
2106:
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
	bne 2106b
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
2107:
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
	bne 2107b
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
2108:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2108b
	ldr r11, [r12, #68]
	movw r8, #16
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #276
	add r9, r12, r9
2109:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2109b
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
2110:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2110b
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
2111:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2111b
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
2112:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2112b
	movw r11, #14720
	add r11, r12, r11
	movw r8, #16
	add r8, r11, r8
	movw r10, #512
	add r10, r12, r10
	movw r9, #532
	add r9, r12, r9
2113:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2113b
	mov r4, #0
	str r4, [r10, #0]
	mov r3, #0
	movw r10, #512
	add r10, r12, r10
	movw r9, #536
	add r9, r12, r9
2114:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 2114b
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
2115:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2115b
	mov r4, #0
	str r4, [r10, #0]
	mov r3, #0
	movw r10, #512
	add r10, r12, r10
	movw r9, #536
	add r9, r12, r9
2116:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 2116b
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
2117:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2117b
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
2118:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2118b
	movw r11, #14752
	add r11, r12, r11
	movw r8, #16
	add r8, r11, r8
	movw r10, #512
	add r10, r12, r10
	movw r9, #532
	add r9, r12, r9
2119:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2119b
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
2120:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2120b
	ldr r0, [r12, #116]
	and r0, r0, #1
	b 234f
233:
	ldr r11, [r12, #96]
	ldr r4, [r12, #104]
	add lr, r11, r4
	add lr, lr, r4
	mov r4, #0
2121:
	strb r4, [r11, #0]
	add r11, r11, #1
	cmp r11, lr
	bne 2121b
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
2122:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2122b
	movw r10, #4568
	add r10, r12, r10
	movw r9, #4952
	add r9, r12, r9
	mov r7, #0
2123:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2123b
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
2124:
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
	bne 2124b
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
2125:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2125b
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
2126:
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
	bne 2126b
	sub r2, r3, #1
	and r2, r2, r11
	str r2, [r12, #8]
	movw r10, #4568
	add r10, r12, r10
	movw r9, #4952
	add r9, r12, r9
	mov r7, #0
2127:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2127b
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
2128:
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
	bne 2128b
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
2129:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2129b
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
2130:
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
	bne 2130b
	sub r2, r3, #1
	and r2, r2, r11
	str r2, [r12, #12]
	movw r10, #4568
	add r10, r12, r10
	movw r9, #4952
	add r9, r12, r9
	mov r7, #0
2131:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2131b
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
2132:
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
	bne 2132b
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
2133:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2133b
	movw r10, #696
	add r10, r12, r10
	movw r9, #728
	add r9, r12, r9
	mov r7, #0
2134:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2134b
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
2135:
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
	bne 2135b
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
2136:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2136b
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
2137:
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
	bne 2137b
	sub r2, r3, #1
	and r2, r2, r11
	str r2, [r12, #20]
	movw r10, #696
	add r10, r12, r10
	movw r9, #728
	add r9, r12, r9
	mov r7, #0
2138:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2138b
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
2139:
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
	bne 2139b
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
2140:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2140b
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
2141:
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
	bne 2141b
	sub r2, r3, #1
	and r2, r2, r11
	str r2, [r12, #24]
	movw r10, #696
	add r10, r12, r10
	movw r9, #728
	add r9, r12, r9
	mov r7, #0
2142:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2142b
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
2143:
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
	bne 2143b
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
	beq 2144f
	ldr r11, [r12, #64]
	movw r8, #380
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #640
	add r9, r12, r9
2146:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2146b
	ldr r11, [r12, #72]
	movw r8, #380
	add r8, r11, r8
	movw r10, #3392
	add r10, r12, r10
	movw r9, #3776
	add r9, r12, r9
2147:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2147b
	movw r6, #65535
	mov r3, #1
	movw r10, #3392
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r9, #3776
	add r9, r12, r9
2148:
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
	bne 2148b
	sub r2, r3, #1
	mov r8, r2
	mov r3, #0
	movw r10, #3392
	add r10, r12, r10
	movw r9, #3776
	add r9, r12, r9
2149:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 2149b
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
	movw r10, #4176
	add r10, r12, r10
	movw r9, #4560
	add r9, r12, r9
	mov r7, #0
2150:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2150b
	movw r10, #4176
	add r10, r12, r10
	movw r4, #2
	movt r4, #0
	str r4, [r10, #0]
	movw r6, #65535
	mov r3, #1
	movw r10, #3392
	add r10, r12, r10
	movw r1, #4176
	add r1, r12, r1
	movw r9, #3776
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
2152:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2152b
	ldr r11, [r12, #76]
	movw r8, #380
	add r8, r11, r8
	movw r10, #3392
	add r10, r12, r10
	movw r9, #3776
	add r9, r12, r9
2153:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2153b
	movw r6, #65535
	mov r3, #1
	movw r10, #3392
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r9, #3776
	add r9, r12, r9
2154:
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
	bne 2154b
	sub r2, r3, #1
	mov r8, r2
	mov r3, #0
	movw r10, #3392
	add r10, r12, r10
	movw r9, #3776
	add r9, r12, r9
2155:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 2155b
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
	movw r10, #4176
	add r10, r12, r10
	movw r9, #4560
	add r9, r12, r9
	mov r7, #0
2156:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2156b
	movw r10, #4176
	add r10, r12, r10
	movw r4, #2
	movt r4, #0
	str r4, [r10, #0]
	movw r6, #65535
	mov r3, #1
	movw r10, #3392
	add r10, r12, r10
	movw r1, #4176
	add r1, r12, r1
	movw r9, #3776
	add r9, r12, r9
2157:
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
	bne 2157b
	sub r2, r3, #1
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
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
2158:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2158b
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
	movw r10, #4176
	add r10, r12, r10
	movw r9, #4560
	add r9, r12, r9
	mov r7, #0
2159:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2159b
	movw r10, #4176
	add r10, r12, r10
	movw r4, #1
	movt r4, #0
	str r4, [r10, #0]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #4176
	add r1, r12, r1
	movw r8, #3784
	add r8, r12, r8
	movw r9, #640
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
	bne 2160b
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
2161:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2161b
	ldr r11, [r12, #68]
	movw r8, #28
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #288
	add r9, r12, r9
2162:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2162b
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
2163:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2163b
	movw r11, #14816
	add r11, r12, r11
	movw r8, #28
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2164:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2164b
	mov r3, #0
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2165:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 2165b
	mov r4, #0
	sub r4, r4, r3
	orr r4, r4, r3
	lsr r4, r4, #31
	mov r2, #0
	sub r2, r2, r4
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
	ldr r4, [r12, #116]
	and r4, r4, r2
	str r4, [r12, #116]
	ldr r11, [r12, #68]
	movw r8, #28
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #288
	add r9, r12, r9
2166:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2166b
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
2167:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2167b
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
2168:
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
	bne 2168b
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
2169:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2169b
	ldr r11, [r12, #64]
	movw r8, #380
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #640
	add r9, r12, r9
2170:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2170b
	ldr r11, [r12, #72]
	movw r8, #380
	add r8, r11, r8
	movw r10, #3392
	add r10, r12, r10
	movw r9, #3776
	add r9, r12, r9
2171:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2171b
	ldr r11, [r12, #68]
	movw r8, #28
	add r8, r11, r8
	movw r10, #4568
	add r10, r12, r10
	movw r9, #4600
	add r9, r12, r9
2172:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2172b
	movw r9, #352
	add r9, r10, r9
	mov r4, #0
2173:
	str r4, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2173b
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
2174:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2174b
	movw r11, #14944
	add r11, r12, r11
	movw r8, #380
	add r8, r11, r8
	movw r10, #3392
	add r10, r12, r10
	movw r9, #3776
	add r9, r12, r9
2175:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2175b
	movw r10, #4568
	add r10, r12, r10
	movw r9, #4952
	add r9, r12, r9
	mov r7, #0
2176:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2176b
	movw r10, #4568
	add r10, r12, r10
	movw r4, #1
	movt r4, #0
	str r4, [r10, #0]
	movw r6, #65535
	mov r3, #1
	movw r10, #3392
	add r10, r12, r10
	movw r1, #4568
	add r1, r12, r1
	movw r9, #3776
	add r9, r12, r9
2177:
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
	bne 2177b
	sub r2, r3, #1
	mov r8, r2
	movw r6, #65535
	mov r3, #1
	movw r10, #4568
	add r10, r12, r10
	movw r1, #3392
	add r1, r12, r1
	movw r9, #4952
	add r9, r12, r9
2178:
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
	bne 2178b
	sub r2, r3, #1
	orr r2, r2, r8
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
	ldr r4, [r12, #116]
	and r4, r4, r2
	str r4, [r12, #116]
	ldr r11, [r12, #68]
	movw r8, #28
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #288
	add r9, r12, r9
2179:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2179b
	ldr r11, [r12, #80]
	movw r8, #28
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2180:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2180b
	movw r6, #65535
	mov r3, #1
	movw r10, #576
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r9, #608
	add r9, r12, r9
2181:
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
	bne 2181b
	sub r2, r3, #1
	mov r8, r2
	mov r3, #0
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2182:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 2182b
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
	ldr r11, [r12, #68]
	movw r8, #28
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #288
	add r9, r12, r9
2183:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2183b
	ldr r11, [r12, #88]
	movw r8, #28
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2184:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2184b
	movw r6, #65535
	mov r3, #1
	movw r10, #576
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r9, #608
	add r9, r12, r9
2185:
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
	bne 2185b
	sub r2, r3, #1
	mov r8, r2
	mov r3, #0
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2186:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 2186b
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
2187:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2187b
	ldr r11, [r12, #72]
	movw r8, #380
	add r8, r11, r8
	movw r10, #3392
	add r10, r12, r10
	movw r9, #3776
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
	movw r10, #4568
	add r10, r12, r10
	movw r9, #4600
	add r9, r12, r9
2189:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2189b
	movw r9, #352
	add r9, r10, r9
	mov r4, #0
2190:
	str r4, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2190b
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
2191:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2191b
	movw r11, #14944
	add r11, r12, r11
	movw r8, #380
	add r8, r11, r8
	movw r10, #3392
	add r10, r12, r10
	movw r9, #3776
	add r9, r12, r9
2192:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2192b
	ldr r11, [r12, #76]
	movw r8, #380
	add r8, r11, r8
	movw r10, #4568
	add r10, r12, r10
	movw r9, #4952
	add r9, r12, r9
2193:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2193b
	movw r6, #65535
	mov r3, #1
	movw r10, #3392
	add r10, r12, r10
	movw r1, #4568
	add r1, r12, r1
	movw r9, #3776
	add r9, r12, r9
2194:
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
	bne 2194b
	sub r2, r3, #1
	mov r8, r2
	movw r6, #65535
	mov r3, #1
	movw r10, #4568
	add r10, r12, r10
	movw r1, #3392
	add r1, r12, r1
	movw r9, #4952
	add r9, r12, r9
2195:
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
	bne 2195b
	sub r2, r3, #1
	orr r2, r2, r8
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
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
2196:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2196b
	ldr r11, [r12, #72]
	movw r8, #380
	add r8, r11, r8
	movw r10, #3392
	add r10, r12, r10
	movw r9, #3776
	add r9, r12, r9
2197:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2197b
	ldr r11, [r12, #88]
	movw r8, #28
	add r8, r11, r8
	movw r10, #4568
	add r10, r12, r10
	movw r9, #4600
	add r9, r12, r9
2198:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2198b
	movw r9, #352
	add r9, r10, r9
	mov r4, #0
2199:
	str r4, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2199b
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
2202:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2202b
	ldr r11, [r12, #68]
	movw r8, #28
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #288
	add r9, r12, r9
2203:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2203b
	ldr r11, [r12, #88]
	movw r8, #28
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2204:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2204b
	movw r11, #14912
	add r11, r12, r11
	movw r8, #28
	add r8, r11, r8
	movw r10, #696
	add r10, r12, r10
	movw r9, #728
	add r9, r12, r9
2205:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2205b
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
2206:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2206b
	ldr r11, [r12, #68]
	movw r8, #28
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #288
	add r9, r12, r9
2207:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2207b
	ldr r11, [r12, #80]
	movw r8, #28
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2208:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2208b
	movw r11, #14720
	add r11, r12, r11
	movw r8, #28
	add r8, r11, r8
	movw r10, #696
	add r10, r12, r10
	movw r9, #728
	add r9, r12, r9
2209:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2209b
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
2210:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2210b
	ldr r11, [r12, #68]
	movw r8, #28
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #288
	add r9, r12, r9
2211:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2211b
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
2212:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2212b
	ldr r11, [r12, #68]
	movw r8, #28
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #288
	add r9, r12, r9
2213:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2213b
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
2214:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2214b
	movw r11, #14816
	add r11, r12, r11
	movw r8, #28
	add r8, r11, r8
	movw r10, #696
	add r10, r12, r10
	movw r9, #728
	add r9, r12, r9
2215:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2215b
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
2216:
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
	bne 2216b
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
2217:
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
	bne 2217b
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
2218:
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
	bne 2218b
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
2219:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2219b
	ldr r11, [r12, #68]
	movw r8, #28
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #288
	add r9, r12, r9
2220:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2220b
	movw r11, #14784
	add r11, r12, r11
	movw r8, #28
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2221:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2221b
	movw r11, #14848
	add r11, r12, r11
	movw r8, #28
	add r8, r11, r8
	movw r10, #696
	add r10, r12, r10
	movw r9, #728
	add r9, r12, r9
2222:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2222b
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
2223:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2223b
	movw r11, #14720
	add r11, r12, r11
	movw r8, #28
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2224:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2224b
	mov r3, #0
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2225:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 2225b
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
2226:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2226b
	mov r3, #0
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2227:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 2227b
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
2228:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2228b
	ldr r11, [r12, #96]
	ldr r3, [r12, #116]
	movw r8, #28
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2229:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2229b
	movw r11, #14752
	add r11, r12, r11
	movw r8, #28
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2230:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2230b
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
2231:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2231b
	ldr r0, [r12, #116]
	and r0, r0, #1
	b 2145f
2144:
	ldr r11, [r12, #96]
	ldr r4, [r12, #104]
	add lr, r11, r4
	add lr, lr, r4
	mov r4, #0
2232:
	strb r4, [r11, #0]
	add r11, r11, #1
	cmp r11, lr
	bne 2232b
	mov r0, #0
2145:
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
2233:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2233b
	movw r10, #3160
	add r10, r12, r10
	movw r9, #3416
	add r9, r12, r9
	mov r7, #0
2234:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2234b
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
2235:
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
	bne 2235b
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
2236:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2236b
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
2237:
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
	bne 2237b
	sub r2, r3, #1
	and r2, r2, r11
	str r2, [r12, #8]
	movw r10, #3160
	add r10, r12, r10
	movw r9, #3416
	add r9, r12, r9
	mov r7, #0
2238:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2238b
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
2239:
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
	bne 2239b
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
2240:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2240b
	movw r10, #696
	add r10, r12, r10
	movw r9, #728
	add r9, r12, r9
	mov r7, #0
2241:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2241b
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
2242:
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
	bne 2242b
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
2243:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2243b
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
2244:
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
	bne 2244b
	sub r2, r3, #1
	and r2, r2, r11
	str r2, [r12, #20]
	movw r10, #696
	add r10, r12, r10
	movw r9, #728
	add r9, r12, r9
	mov r7, #0
2245:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2245b
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
2246:
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
	bne 2246b
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
2247:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2247b
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
2248:
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
	bne 2248b
	sub r2, r3, #1
	and r2, r2, r11
	str r2, [r12, #24]
	movw r10, #696
	add r10, r12, r10
	movw r9, #728
	add r9, r12, r9
	mov r7, #0
2249:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2249b
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
2250:
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
	bne 2250b
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
	beq 2251f
	ldr r11, [r12, #64]
	movw r8, #252
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #512
	add r9, r12, r9
2253:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2253b
	ldr r11, [r12, #72]
	movw r8, #252
	add r8, r11, r8
	movw r10, #2368
	add r10, r12, r10
	movw r9, #2624
	add r9, r12, r9
2254:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2254b
	movw r6, #65535
	mov r3, #1
	movw r10, #2368
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r9, #2624
	add r9, r12, r9
2255:
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
	bne 2255b
	sub r2, r3, #1
	mov r8, r2
	mov r3, #0
	movw r10, #2368
	add r10, r12, r10
	movw r9, #2624
	add r9, r12, r9
2256:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 2256b
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
	movw r10, #2896
	add r10, r12, r10
	movw r9, #3152
	add r9, r12, r9
	mov r7, #0
2257:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2257b
	movw r10, #2896
	add r10, r12, r10
	movw r4, #2
	movt r4, #0
	str r4, [r10, #0]
	movw r6, #65535
	mov r3, #1
	movw r10, #2368
	add r10, r12, r10
	movw r1, #2896
	add r1, r12, r1
	movw r9, #2624
	add r9, r12, r9
2258:
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
	bne 2258b
	sub r2, r3, #1
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
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
2259:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2259b
	ldr r11, [r12, #76]
	movw r8, #252
	add r8, r11, r8
	movw r10, #2368
	add r10, r12, r10
	movw r9, #2624
	add r9, r12, r9
2260:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2260b
	movw r6, #65535
	mov r3, #1
	movw r10, #2368
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r9, #2624
	add r9, r12, r9
2261:
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
	bne 2261b
	sub r2, r3, #1
	mov r8, r2
	mov r3, #0
	movw r10, #2368
	add r10, r12, r10
	movw r9, #2624
	add r9, r12, r9
2262:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 2262b
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
	movw r10, #2896
	add r10, r12, r10
	movw r9, #3152
	add r9, r12, r9
	mov r7, #0
2263:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2263b
	movw r10, #2896
	add r10, r12, r10
	movw r4, #2
	movt r4, #0
	str r4, [r10, #0]
	movw r6, #65535
	mov r3, #1
	movw r10, #2368
	add r10, r12, r10
	movw r1, #2896
	add r1, r12, r1
	movw r9, #2624
	add r9, r12, r9
2264:
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
	bne 2264b
	sub r2, r3, #1
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
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
2265:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2265b
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
	movw r10, #2896
	add r10, r12, r10
	movw r9, #3152
	add r9, r12, r9
	mov r7, #0
2266:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2266b
	movw r10, #2896
	add r10, r12, r10
	movw r4, #1
	movt r4, #0
	str r4, [r10, #0]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #2896
	add r1, r12, r1
	movw r8, #2632
	add r8, r12, r8
	movw r9, #512
	add r9, r12, r9
2267:
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
	bne 2267b
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
2268:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2268b
	ldr r11, [r12, #68]
	movw r8, #28
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #288
	add r9, r12, r9
2269:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2269b
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
2270:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2270b
	movw r11, #14816
	add r11, r12, r11
	movw r8, #28
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2271:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2271b
	mov r3, #0
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2272:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 2272b
	mov r4, #0
	sub r4, r4, r3
	orr r4, r4, r3
	lsr r4, r4, #31
	mov r2, #0
	sub r2, r2, r4
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
	ldr r4, [r12, #116]
	and r4, r4, r2
	str r4, [r12, #116]
	ldr r11, [r12, #68]
	movw r8, #28
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #288
	add r9, r12, r9
2273:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2273b
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
2274:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2274b
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
2275:
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
	bne 2275b
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
2276:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2276b
	ldr r11, [r12, #64]
	movw r8, #252
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #512
	add r9, r12, r9
2277:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2277b
	ldr r11, [r12, #72]
	movw r8, #252
	add r8, r11, r8
	movw r10, #2368
	add r10, r12, r10
	movw r9, #2624
	add r9, r12, r9
2278:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2278b
	ldr r11, [r12, #68]
	movw r8, #28
	add r8, r11, r8
	movw r10, #3160
	add r10, r12, r10
	movw r9, #3192
	add r9, r12, r9
2279:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2279b
	movw r9, #224
	add r9, r10, r9
	mov r4, #0
2280:
	str r4, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2280b
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
2281:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2281b
	movw r11, #14944
	add r11, r12, r11
	movw r8, #252
	add r8, r11, r8
	movw r10, #2368
	add r10, r12, r10
	movw r9, #2624
	add r9, r12, r9
2282:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2282b
	movw r10, #3160
	add r10, r12, r10
	movw r9, #3416
	add r9, r12, r9
	mov r7, #0
2283:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2283b
	movw r10, #3160
	add r10, r12, r10
	movw r4, #1
	movt r4, #0
	str r4, [r10, #0]
	movw r6, #65535
	mov r3, #1
	movw r10, #2368
	add r10, r12, r10
	movw r1, #3160
	add r1, r12, r1
	movw r9, #2624
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
	mov r8, r2
	movw r6, #65535
	mov r3, #1
	movw r10, #3160
	add r10, r12, r10
	movw r1, #2368
	add r1, r12, r1
	movw r9, #3416
	add r9, r12, r9
2285:
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
	bne 2285b
	sub r2, r3, #1
	orr r2, r2, r8
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
	ldr r4, [r12, #116]
	and r4, r4, r2
	str r4, [r12, #116]
	ldr r11, [r12, #68]
	movw r8, #28
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #288
	add r9, r12, r9
2286:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2286b
	ldr r11, [r12, #80]
	movw r8, #28
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2287:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2287b
	movw r6, #65535
	mov r3, #1
	movw r10, #576
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r9, #608
	add r9, r12, r9
2288:
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
	bne 2288b
	sub r2, r3, #1
	mov r8, r2
	mov r3, #0
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2289:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 2289b
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
	ldr r11, [r12, #68]
	movw r8, #28
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #288
	add r9, r12, r9
2290:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2290b
	ldr r11, [r12, #88]
	movw r8, #28
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2291:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2291b
	movw r6, #65535
	mov r3, #1
	movw r10, #576
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r9, #608
	add r9, r12, r9
2292:
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
	bne 2292b
	sub r2, r3, #1
	mov r8, r2
	mov r3, #0
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2293:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 2293b
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
2294:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2294b
	ldr r11, [r12, #72]
	movw r8, #252
	add r8, r11, r8
	movw r10, #2368
	add r10, r12, r10
	movw r9, #2624
	add r9, r12, r9
2295:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2295b
	ldr r11, [r12, #80]
	movw r8, #28
	add r8, r11, r8
	movw r10, #3160
	add r10, r12, r10
	movw r9, #3192
	add r9, r12, r9
2296:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2296b
	movw r9, #224
	add r9, r10, r9
	mov r4, #0
2297:
	str r4, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2297b
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
2298:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2298b
	movw r11, #14944
	add r11, r12, r11
	movw r8, #252
	add r8, r11, r8
	movw r10, #2368
	add r10, r12, r10
	movw r9, #2624
	add r9, r12, r9
2299:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2299b
	ldr r11, [r12, #76]
	movw r8, #252
	add r8, r11, r8
	movw r10, #3160
	add r10, r12, r10
	movw r9, #3416
	add r9, r12, r9
2300:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2300b
	movw r6, #65535
	mov r3, #1
	movw r10, #2368
	add r10, r12, r10
	movw r1, #3160
	add r1, r12, r1
	movw r9, #2624
	add r9, r12, r9
2301:
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
	bne 2301b
	sub r2, r3, #1
	mov r8, r2
	movw r6, #65535
	mov r3, #1
	movw r10, #3160
	add r10, r12, r10
	movw r1, #2368
	add r1, r12, r1
	movw r9, #3416
	add r9, r12, r9
2302:
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
	bne 2302b
	sub r2, r3, #1
	orr r2, r2, r8
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
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
2303:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2303b
	ldr r11, [r12, #72]
	movw r8, #252
	add r8, r11, r8
	movw r10, #2368
	add r10, r12, r10
	movw r9, #2624
	add r9, r12, r9
2304:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2304b
	ldr r11, [r12, #88]
	movw r8, #28
	add r8, r11, r8
	movw r10, #3160
	add r10, r12, r10
	movw r9, #3192
	add r9, r12, r9
2305:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2305b
	movw r9, #224
	add r9, r10, r9
	mov r4, #0
2306:
	str r4, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2306b
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
	movw r8, #28
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #288
	add r9, r12, r9
2308:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2308b
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
2309:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2309b
	ldr r11, [r12, #68]
	movw r8, #28
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #288
	add r9, r12, r9
2310:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2310b
	ldr r11, [r12, #88]
	movw r8, #28
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2311:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2311b
	movw r11, #14912
	add r11, r12, r11
	movw r8, #28
	add r8, r11, r8
	movw r10, #696
	add r10, r12, r10
	movw r9, #728
	add r9, r12, r9
2312:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2312b
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
	movw r8, #28
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #288
	add r9, r12, r9
2314:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2314b
	ldr r11, [r12, #80]
	movw r8, #28
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2315:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2315b
	movw r11, #14720
	add r11, r12, r11
	movw r8, #28
	add r8, r11, r8
	movw r10, #696
	add r10, r12, r10
	movw r9, #728
	add r9, r12, r9
2316:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2316b
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
2317:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2317b
	ldr r11, [r12, #68]
	movw r8, #28
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #288
	add r9, r12, r9
2318:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2318b
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
2319:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2319b
	ldr r11, [r12, #68]
	movw r8, #28
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #288
	add r9, r12, r9
2320:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2320b
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
2321:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2321b
	movw r11, #14816
	add r11, r12, r11
	movw r8, #28
	add r8, r11, r8
	movw r10, #696
	add r10, r12, r10
	movw r9, #728
	add r9, r12, r9
2322:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2322b
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
2323:
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
	bne 2323b
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
2324:
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
	bne 2324b
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
2325:
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
	bne 2325b
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
2326:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2326b
	ldr r11, [r12, #68]
	movw r8, #28
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #288
	add r9, r12, r9
2327:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2327b
	movw r11, #14784
	add r11, r12, r11
	movw r8, #28
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2328:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2328b
	movw r11, #14848
	add r11, r12, r11
	movw r8, #28
	add r8, r11, r8
	movw r10, #696
	add r10, r12, r10
	movw r9, #728
	add r9, r12, r9
2329:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2329b
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
2330:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2330b
	movw r11, #14720
	add r11, r12, r11
	movw r8, #28
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2331:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2331b
	mov r3, #0
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2332:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 2332b
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
2333:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2333b
	mov r3, #0
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2334:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 2334b
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
2335:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2335b
	ldr r11, [r12, #96]
	ldr r3, [r12, #116]
	movw r8, #28
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2336:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2336b
	movw r11, #14752
	add r11, r12, r11
	movw r8, #28
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2337:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2337b
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
2338:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2338b
	ldr r0, [r12, #116]
	and r0, r0, #1
	b 2252f
2251:
	ldr r11, [r12, #96]
	ldr r4, [r12, #104]
	add lr, r11, r4
	add lr, lr, r4
	mov r4, #0
2339:
	strb r4, [r11, #0]
	add r11, r11, #1
	cmp r11, lr
	bne 2339b
	mov r0, #0
2252:
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
2340:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2340b
	movw r10, #3160
	add r10, r12, r10
	movw r9, #3416
	add r9, r12, r9
	mov r7, #0
2341:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2341b
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
2342:
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
	bne 2342b
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
2343:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2343b
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
2344:
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
	bne 2344b
	sub r2, r3, #1
	and r2, r2, r11
	str r2, [r12, #8]
	movw r10, #3160
	add r10, r12, r10
	movw r9, #3416
	add r9, r12, r9
	mov r7, #0
2345:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2345b
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
2346:
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
	bne 2346b
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
2347:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2347b
	mov r4, #0
	str r4, [r10, #0]
	movw r10, #696
	add r10, r12, r10
	movw r9, #728
	add r9, r12, r9
	mov r7, #0
2348:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2348b
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
2349:
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
	bne 2349b
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
2350:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2350b
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
2351:
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
	bne 2351b
	sub r2, r3, #1
	and r2, r2, r11
	str r2, [r12, #20]
	movw r10, #696
	add r10, r12, r10
	movw r9, #728
	add r9, r12, r9
	mov r7, #0
2352:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2352b
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
2353:
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
	bne 2353b
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
2354:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2354b
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
2355:
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
	bne 2355b
	sub r2, r3, #1
	and r2, r2, r11
	str r2, [r12, #24]
	movw r10, #696
	add r10, r12, r10
	movw r9, #728
	add r9, r12, r9
	mov r7, #0
2356:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2356b
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
2357:
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
	bne 2357b
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
	beq 2358f
	ldr r11, [r12, #64]
	movw r8, #252
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #512
	add r9, r12, r9
2360:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2360b
	ldr r11, [r12, #72]
	movw r8, #252
	add r8, r11, r8
	movw r10, #2368
	add r10, r12, r10
	movw r9, #2624
	add r9, r12, r9
2361:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2361b
	movw r6, #65535
	mov r3, #1
	movw r10, #2368
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r9, #2624
	add r9, r12, r9
2362:
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
	bne 2362b
	sub r2, r3, #1
	mov r8, r2
	mov r3, #0
	movw r10, #2368
	add r10, r12, r10
	movw r9, #2624
	add r9, r12, r9
2363:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 2363b
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
	movw r10, #2896
	add r10, r12, r10
	movw r9, #3152
	add r9, r12, r9
	mov r7, #0
2364:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2364b
	movw r10, #2896
	add r10, r12, r10
	movw r4, #2
	movt r4, #0
	str r4, [r10, #0]
	movw r6, #65535
	mov r3, #1
	movw r10, #2368
	add r10, r12, r10
	movw r1, #2896
	add r1, r12, r1
	movw r9, #2624
	add r9, r12, r9
2365:
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
	bne 2365b
	sub r2, r3, #1
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
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
2366:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2366b
	ldr r11, [r12, #76]
	movw r8, #252
	add r8, r11, r8
	movw r10, #2368
	add r10, r12, r10
	movw r9, #2624
	add r9, r12, r9
2367:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2367b
	movw r6, #65535
	mov r3, #1
	movw r10, #2368
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r9, #2624
	add r9, r12, r9
2368:
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
	bne 2368b
	sub r2, r3, #1
	mov r8, r2
	mov r3, #0
	movw r10, #2368
	add r10, r12, r10
	movw r9, #2624
	add r9, r12, r9
2369:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 2369b
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
	movw r10, #2896
	add r10, r12, r10
	movw r9, #3152
	add r9, r12, r9
	mov r7, #0
2370:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2370b
	movw r10, #2896
	add r10, r12, r10
	movw r4, #2
	movt r4, #0
	str r4, [r10, #0]
	movw r6, #65535
	mov r3, #1
	movw r10, #2368
	add r10, r12, r10
	movw r1, #2896
	add r1, r12, r1
	movw r9, #2624
	add r9, r12, r9
2371:
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
	bne 2371b
	sub r2, r3, #1
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
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
2372:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2372b
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
	movw r10, #2896
	add r10, r12, r10
	movw r9, #3152
	add r9, r12, r9
	mov r7, #0
2373:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2373b
	movw r10, #2896
	add r10, r12, r10
	movw r4, #1
	movt r4, #0
	str r4, [r10, #0]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #2896
	add r1, r12, r1
	movw r8, #2632
	add r8, r12, r8
	movw r9, #512
	add r9, r12, r9
2374:
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
	bne 2374b
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
2375:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2375b
	ldr r11, [r12, #68]
	movw r8, #24
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #284
	add r9, r12, r9
2376:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2376b
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
2377:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2377b
	movw r11, #14816
	add r11, r12, r11
	movw r8, #24
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #604
	add r9, r12, r9
2378:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2378b
	mov r4, #0
	str r4, [r10, #0]
	mov r3, #0
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2379:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 2379b
	mov r4, #0
	sub r4, r4, r3
	orr r4, r4, r3
	lsr r4, r4, #31
	mov r2, #0
	sub r2, r2, r4
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
	ldr r4, [r12, #116]
	and r4, r4, r2
	str r4, [r12, #116]
	ldr r11, [r12, #68]
	movw r8, #24
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #284
	add r9, r12, r9
2380:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2380b
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
2381:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2381b
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
2382:
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
	bne 2382b
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
2383:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2383b
	ldr r11, [r12, #64]
	movw r8, #252
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #512
	add r9, r12, r9
2384:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2384b
	ldr r11, [r12, #72]
	movw r8, #252
	add r8, r11, r8
	movw r10, #2368
	add r10, r12, r10
	movw r9, #2624
	add r9, r12, r9
2385:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2385b
	ldr r11, [r12, #68]
	movw r8, #24
	add r8, r11, r8
	movw r10, #3160
	add r10, r12, r10
	movw r9, #3188
	add r9, r12, r9
2386:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2386b
	movw r9, #228
	add r9, r10, r9
	mov r4, #0
2387:
	str r4, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2387b
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
2388:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2388b
	movw r11, #14944
	add r11, r12, r11
	movw r8, #252
	add r8, r11, r8
	movw r10, #2368
	add r10, r12, r10
	movw r9, #2624
	add r9, r12, r9
2389:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2389b
	movw r10, #3160
	add r10, r12, r10
	movw r9, #3416
	add r9, r12, r9
	mov r7, #0
2390:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2390b
	movw r10, #3160
	add r10, r12, r10
	movw r4, #1
	movt r4, #0
	str r4, [r10, #0]
	movw r6, #65535
	mov r3, #1
	movw r10, #2368
	add r10, r12, r10
	movw r1, #3160
	add r1, r12, r1
	movw r9, #2624
	add r9, r12, r9
2391:
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
	bne 2391b
	sub r2, r3, #1
	mov r8, r2
	movw r6, #65535
	mov r3, #1
	movw r10, #3160
	add r10, r12, r10
	movw r1, #2368
	add r1, r12, r1
	movw r9, #3416
	add r9, r12, r9
2392:
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
	bne 2392b
	sub r2, r3, #1
	orr r2, r2, r8
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
	ldr r4, [r12, #116]
	and r4, r4, r2
	str r4, [r12, #116]
	ldr r11, [r12, #68]
	movw r8, #24
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #284
	add r9, r12, r9
2393:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2393b
	mov r4, #0
	str r4, [r10, #0]
	ldr r11, [r12, #80]
	movw r8, #24
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #604
	add r9, r12, r9
2394:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2394b
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
2395:
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
	bne 2395b
	sub r2, r3, #1
	mov r8, r2
	mov r3, #0
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2396:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 2396b
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
	ldr r11, [r12, #68]
	movw r8, #24
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #284
	add r9, r12, r9
2397:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2397b
	mov r4, #0
	str r4, [r10, #0]
	ldr r11, [r12, #88]
	movw r8, #24
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #604
	add r9, r12, r9
2398:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2398b
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
2399:
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
	bne 2399b
	sub r2, r3, #1
	mov r8, r2
	mov r3, #0
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2400:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 2400b
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
2401:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2401b
	ldr r11, [r12, #72]
	movw r8, #252
	add r8, r11, r8
	movw r10, #2368
	add r10, r12, r10
	movw r9, #2624
	add r9, r12, r9
2402:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2402b
	ldr r11, [r12, #80]
	movw r8, #24
	add r8, r11, r8
	movw r10, #3160
	add r10, r12, r10
	movw r9, #3188
	add r9, r12, r9
2403:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2403b
	movw r9, #228
	add r9, r10, r9
	mov r4, #0
2404:
	str r4, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2404b
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
2405:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2405b
	movw r11, #14944
	add r11, r12, r11
	movw r8, #252
	add r8, r11, r8
	movw r10, #2368
	add r10, r12, r10
	movw r9, #2624
	add r9, r12, r9
2406:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2406b
	ldr r11, [r12, #76]
	movw r8, #252
	add r8, r11, r8
	movw r10, #3160
	add r10, r12, r10
	movw r9, #3416
	add r9, r12, r9
2407:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2407b
	movw r6, #65535
	mov r3, #1
	movw r10, #2368
	add r10, r12, r10
	movw r1, #3160
	add r1, r12, r1
	movw r9, #2624
	add r9, r12, r9
2408:
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
	bne 2408b
	sub r2, r3, #1
	mov r8, r2
	movw r6, #65535
	mov r3, #1
	movw r10, #3160
	add r10, r12, r10
	movw r1, #2368
	add r1, r12, r1
	movw r9, #3416
	add r9, r12, r9
2409:
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
	bne 2409b
	sub r2, r3, #1
	orr r2, r2, r8
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
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
2410:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2410b
	ldr r11, [r12, #72]
	movw r8, #252
	add r8, r11, r8
	movw r10, #2368
	add r10, r12, r10
	movw r9, #2624
	add r9, r12, r9
2411:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2411b
	ldr r11, [r12, #88]
	movw r8, #24
	add r8, r11, r8
	movw r10, #3160
	add r10, r12, r10
	movw r9, #3188
	add r9, r12, r9
2412:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2412b
	movw r9, #228
	add r9, r10, r9
	mov r4, #0
2413:
	str r4, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2413b
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
2414:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2414b
	ldr r11, [r12, #68]
	movw r8, #24
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #284
	add r9, r12, r9
2415:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2415b
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
2416:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2416b
	ldr r11, [r12, #68]
	movw r8, #24
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #284
	add r9, r12, r9
2417:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2417b
	mov r4, #0
	str r4, [r10, #0]
	ldr r11, [r12, #88]
	movw r8, #24
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #604
	add r9, r12, r9
2418:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2418b
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
2419:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2419b
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
2420:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2420b
	ldr r11, [r12, #68]
	movw r8, #24
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #284
	add r9, r12, r9
2421:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2421b
	mov r4, #0
	str r4, [r10, #0]
	ldr r11, [r12, #80]
	movw r8, #24
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #604
	add r9, r12, r9
2422:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2422b
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
2423:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2423b
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
2424:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2424b
	ldr r11, [r12, #68]
	movw r8, #24
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #284
	add r9, r12, r9
2425:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2425b
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
2426:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2426b
	ldr r11, [r12, #68]
	movw r8, #24
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #284
	add r9, r12, r9
2427:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2427b
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
2428:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2428b
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
2429:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2429b
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
2430:
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
	bne 2430b
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
2431:
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
	bne 2431b
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
2432:
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
	bne 2432b
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
2433:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2433b
	ldr r11, [r12, #68]
	movw r8, #24
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #284
	add r9, r12, r9
2434:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2434b
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
2435:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2435b
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
2436:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2436b
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
2437:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2437b
	movw r11, #14720
	add r11, r12, r11
	movw r8, #24
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #604
	add r9, r12, r9
2438:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2438b
	mov r4, #0
	str r4, [r10, #0]
	mov r3, #0
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2439:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 2439b
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
2440:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2440b
	mov r4, #0
	str r4, [r10, #0]
	mov r3, #0
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
2441:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 2441b
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
2442:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2442b
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
2443:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2443b
	movw r11, #14752
	add r11, r12, r11
	movw r8, #24
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #604
	add r9, r12, r9
2444:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2444b
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
2445:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2445b
	ldr r0, [r12, #116]
	and r0, r0, #1
	b 2359f
2358:
	ldr r11, [r12, #96]
	ldr r4, [r12, #104]
	add lr, r11, r4
	add lr, lr, r4
	mov r4, #0
2446:
	strb r4, [r11, #0]
	add r11, r11, #1
	cmp r11, lr
	bne 2446b
	mov r0, #0
2359:
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
2447:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2447b
	movw r10, #1752
	add r10, r12, r10
	movw r9, #1880
	add r9, r12, r9
	mov r7, #0
2448:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2448b
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
2449:
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
	bne 2449b
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
2450:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2450b
	mov r4, #0
	str r4, [r10, #0]
	movw r10, #608
	add r10, r12, r10
	movw r9, #632
	add r9, r12, r9
	mov r7, #0
2451:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2451b
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
2452:
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
	bne 2452b
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
2453:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2453b
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
2454:
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
	bne 2454b
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
	beq 2455f
	ldr r11, [r12, #64]
	movw r8, #124
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #384
	add r9, r12, r9
2457:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2457b
	ldr r11, [r12, #72]
	movw r8, #124
	add r8, r11, r8
	movw r10, #1344
	add r10, r12, r10
	movw r9, #1472
	add r9, r12, r9
2458:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2458b
	movw r6, #65535
	mov r3, #1
	movw r10, #1344
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r9, #1472
	add r9, r12, r9
2459:
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
	bne 2459b
	sub r2, r3, #1
	mov r8, r2
	mov r3, #0
	movw r10, #1344
	add r10, r12, r10
	movw r9, #1472
	add r9, r12, r9
2460:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 2460b
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
	movw r10, #1616
	add r10, r12, r10
	movw r9, #1744
	add r9, r12, r9
	mov r7, #0
2461:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2461b
	movw r10, #1616
	add r10, r12, r10
	movw r4, #2
	movt r4, #0
	str r4, [r10, #0]
	movw r6, #65535
	mov r3, #1
	movw r10, #1344
	add r10, r12, r10
	movw r1, #1616
	add r1, r12, r1
	movw r9, #1472
	add r9, r12, r9
2462:
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
	bne 2462b
	sub r2, r3, #1
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
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
2463:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2463b
	ldr r11, [r12, #76]
	movw r8, #124
	add r8, r11, r8
	movw r10, #1344
	add r10, r12, r10
	movw r9, #1472
	add r9, r12, r9
2464:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2464b
	movw r6, #65535
	mov r3, #1
	movw r10, #1344
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r9, #1472
	add r9, r12, r9
2465:
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
	bne 2465b
	sub r2, r3, #1
	mov r8, r2
	mov r3, #0
	movw r10, #1344
	add r10, r12, r10
	movw r9, #1472
	add r9, r12, r9
2466:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 2466b
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
	movw r10, #1616
	add r10, r12, r10
	movw r9, #1744
	add r9, r12, r9
	mov r7, #0
2467:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2467b
	movw r10, #1616
	add r10, r12, r10
	movw r4, #2
	movt r4, #0
	str r4, [r10, #0]
	movw r6, #65535
	mov r3, #1
	movw r10, #1344
	add r10, r12, r10
	movw r1, #1616
	add r1, r12, r1
	movw r9, #1472
	add r9, r12, r9
2468:
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
	bne 2468b
	sub r2, r3, #1
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
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
2469:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2469b
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
	movw r10, #1616
	add r10, r12, r10
	movw r9, #1744
	add r9, r12, r9
	mov r7, #0
2470:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2470b
	movw r10, #1616
	add r10, r12, r10
	movw r4, #1
	movt r4, #0
	str r4, [r10, #0]
	movw r6, #65535
	mov r3, #1
	movw r10, #256
	add r10, r12, r10
	movw r1, #1616
	add r1, r12, r1
	movw r8, #1480
	add r8, r12, r8
	movw r9, #384
	add r9, r12, r9
2471:
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
	bne 2471b
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
2472:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2472b
	ldr r11, [r12, #68]
	movw r8, #16
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #276
	add r9, r12, r9
2473:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2473b
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
2474:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2474b
	movw r11, #14816
	add r11, r12, r11
	movw r8, #16
	add r8, r11, r8
	movw r10, #512
	add r10, r12, r10
	movw r9, #532
	add r9, r12, r9
2475:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2475b
	mov r4, #0
	str r4, [r10, #0]
	mov r3, #0
	movw r10, #512
	add r10, r12, r10
	movw r9, #536
	add r9, r12, r9
2476:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 2476b
	mov r4, #0
	sub r4, r4, r3
	orr r4, r4, r3
	lsr r4, r4, #31
	mov r2, #0
	sub r2, r2, r4
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
	ldr r4, [r12, #116]
	and r4, r4, r2
	str r4, [r12, #116]
	ldr r11, [r12, #68]
	movw r8, #16
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #276
	add r9, r12, r9
2477:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2477b
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
2478:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2478b
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
2479:
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
	bne 2479b
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
2480:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2480b
	ldr r11, [r12, #64]
	movw r8, #124
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #384
	add r9, r12, r9
2481:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2481b
	ldr r11, [r12, #72]
	movw r8, #124
	add r8, r11, r8
	movw r10, #1344
	add r10, r12, r10
	movw r9, #1472
	add r9, r12, r9
2482:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2482b
	ldr r11, [r12, #68]
	movw r8, #16
	add r8, r11, r8
	movw r10, #1752
	add r10, r12, r10
	movw r9, #1772
	add r9, r12, r9
2483:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2483b
	movw r9, #108
	add r9, r10, r9
	mov r4, #0
2484:
	str r4, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2484b
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
2485:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2485b
	movw r11, #14944
	add r11, r12, r11
	movw r8, #124
	add r8, r11, r8
	movw r10, #1344
	add r10, r12, r10
	movw r9, #1472
	add r9, r12, r9
2486:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2486b
	movw r10, #1752
	add r10, r12, r10
	movw r9, #1880
	add r9, r12, r9
	mov r7, #0
2487:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2487b
	movw r10, #1752
	add r10, r12, r10
	movw r4, #1
	movt r4, #0
	str r4, [r10, #0]
	movw r6, #65535
	mov r3, #1
	movw r10, #1344
	add r10, r12, r10
	movw r1, #1752
	add r1, r12, r1
	movw r9, #1472
	add r9, r12, r9
2488:
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
	bne 2488b
	sub r2, r3, #1
	mov r8, r2
	movw r6, #65535
	mov r3, #1
	movw r10, #1752
	add r10, r12, r10
	movw r1, #1344
	add r1, r12, r1
	movw r9, #1880
	add r9, r12, r9
2489:
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
	bne 2489b
	sub r2, r3, #1
	orr r2, r2, r8
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
	ldr r4, [r12, #116]
	and r4, r4, r2
	str r4, [r12, #116]
	ldr r11, [r12, #68]
	movw r8, #16
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #276
	add r9, r12, r9
2490:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2490b
	mov r4, #0
	str r4, [r10, #0]
	ldr r11, [r12, #80]
	movw r8, #16
	add r8, r11, r8
	movw r10, #512
	add r10, r12, r10
	movw r9, #532
	add r9, r12, r9
2491:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2491b
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
2492:
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
	bne 2492b
	sub r2, r3, #1
	mov r8, r2
	mov r3, #0
	movw r10, #512
	add r10, r12, r10
	movw r9, #536
	add r9, r12, r9
2493:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 2493b
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
	ldr r11, [r12, #68]
	movw r8, #16
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #276
	add r9, r12, r9
2494:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2494b
	mov r4, #0
	str r4, [r10, #0]
	ldr r11, [r12, #88]
	movw r8, #16
	add r8, r11, r8
	movw r10, #512
	add r10, r12, r10
	movw r9, #532
	add r9, r12, r9
2495:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2495b
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
2496:
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
	bne 2496b
	sub r2, r3, #1
	mov r8, r2
	mov r3, #0
	movw r10, #512
	add r10, r12, r10
	movw r9, #536
	add r9, r12, r9
2497:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 2497b
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
2498:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2498b
	ldr r11, [r12, #72]
	movw r8, #124
	add r8, r11, r8
	movw r10, #1344
	add r10, r12, r10
	movw r9, #1472
	add r9, r12, r9
2499:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2499b
	ldr r11, [r12, #80]
	movw r8, #16
	add r8, r11, r8
	movw r10, #1752
	add r10, r12, r10
	movw r9, #1772
	add r9, r12, r9
2500:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2500b
	movw r9, #108
	add r9, r10, r9
	mov r4, #0
2501:
	str r4, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2501b
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
2502:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2502b
	movw r11, #14944
	add r11, r12, r11
	movw r8, #124
	add r8, r11, r8
	movw r10, #1344
	add r10, r12, r10
	movw r9, #1472
	add r9, r12, r9
2503:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2503b
	ldr r11, [r12, #76]
	movw r8, #124
	add r8, r11, r8
	movw r10, #1752
	add r10, r12, r10
	movw r9, #1880
	add r9, r12, r9
2504:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2504b
	movw r6, #65535
	mov r3, #1
	movw r10, #1344
	add r10, r12, r10
	movw r1, #1752
	add r1, r12, r1
	movw r9, #1472
	add r9, r12, r9
2505:
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
	bne 2505b
	sub r2, r3, #1
	mov r8, r2
	movw r6, #65535
	mov r3, #1
	movw r10, #1752
	add r10, r12, r10
	movw r1, #1344
	add r1, r12, r1
	movw r9, #1880
	add r9, r12, r9
2506:
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
	bne 2506b
	sub r2, r3, #1
	orr r2, r2, r8
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
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
2507:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2507b
	ldr r11, [r12, #72]
	movw r8, #124
	add r8, r11, r8
	movw r10, #1344
	add r10, r12, r10
	movw r9, #1472
	add r9, r12, r9
2508:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2508b
	ldr r11, [r12, #88]
	movw r8, #16
	add r8, r11, r8
	movw r10, #1752
	add r10, r12, r10
	movw r9, #1772
	add r9, r12, r9
2509:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2509b
	movw r9, #108
	add r9, r10, r9
	mov r4, #0
2510:
	str r4, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 2510b
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
2511:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2511b
	ldr r11, [r12, #68]
	movw r8, #16
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #276
	add r9, r12, r9
2512:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2512b
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
2513:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2513b
	ldr r11, [r12, #68]
	movw r8, #16
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #276
	add r9, r12, r9
2514:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2514b
	mov r4, #0
	str r4, [r10, #0]
	ldr r11, [r12, #88]
	movw r8, #16
	add r8, r11, r8
	movw r10, #512
	add r10, r12, r10
	movw r9, #532
	add r9, r12, r9
2515:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2515b
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
2516:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2516b
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
2517:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2517b
	ldr r11, [r12, #68]
	movw r8, #16
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #276
	add r9, r12, r9
2518:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2518b
	mov r4, #0
	str r4, [r10, #0]
	ldr r11, [r12, #80]
	movw r8, #16
	add r8, r11, r8
	movw r10, #512
	add r10, r12, r10
	movw r9, #532
	add r9, r12, r9
2519:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2519b
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
2520:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2520b
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
2521:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2521b
	ldr r11, [r12, #68]
	movw r8, #16
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #276
	add r9, r12, r9
2522:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2522b
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
2523:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2523b
	ldr r11, [r12, #68]
	movw r8, #16
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #276
	add r9, r12, r9
2524:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2524b
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
2525:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2525b
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
2526:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2526b
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
2527:
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
	bne 2527b
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
2528:
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
	bne 2528b
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
2529:
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
	bne 2529b
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
2530:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2530b
	ldr r11, [r12, #68]
	movw r8, #16
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #276
	add r9, r12, r9
2531:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2531b
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
2532:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2532b
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
2533:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2533b
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
2534:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2534b
	movw r11, #14720
	add r11, r12, r11
	movw r8, #16
	add r8, r11, r8
	movw r10, #512
	add r10, r12, r10
	movw r9, #532
	add r9, r12, r9
2535:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2535b
	mov r4, #0
	str r4, [r10, #0]
	mov r3, #0
	movw r10, #512
	add r10, r12, r10
	movw r9, #536
	add r9, r12, r9
2536:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 2536b
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
2537:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2537b
	mov r4, #0
	str r4, [r10, #0]
	mov r3, #0
	movw r10, #512
	add r10, r12, r10
	movw r9, #536
	add r9, r12, r9
2538:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 2538b
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
2539:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2539b
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
2540:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2540b
	movw r11, #14752
	add r11, r12, r11
	movw r8, #16
	add r8, r11, r8
	movw r10, #512
	add r10, r12, r10
	movw r9, #532
	add r9, r12, r9
2541:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2541b
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
2542:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 2542b
	ldr r0, [r12, #116]
	and r0, r0, #1
	b 2456f
2455:
	ldr r11, [r12, #96]
	ldr r4, [r12, #104]
	add lr, r11, r4
	add lr, lr, r4
	mov r4, #0
2543:
	strb r4, [r11, #0]
	add r11, r11, #1
	cmp r11, lr
	bne 2543b
	mov r0, #0
2456:
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
