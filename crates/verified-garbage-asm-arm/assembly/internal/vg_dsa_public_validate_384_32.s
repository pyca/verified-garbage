// The functions of `src/internal/vg_dsa_public_validate_384_32.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_dsa_public_validate_384_32:
	mov r12, r0
	str r4, [r12, #168]
	str r5, [r12, #172]
	str r6, [r12, #176]
	str r7, [r12, #180]
	str r8, [r12, #184]
	str r9, [r12, #188]
	str r10, [r12, #192]
	str r11, [r12, #196]
	str lr, [r12, #200]
	ldr r11, [r12, #64]
	movw r8, #380
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #640
	add r9, r12, r9
20:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 20b
	ldr r11, [r12, #72]
	movw r8, #380
	add r8, r11, r8
	movw r10, #3392
	add r10, r12, r10
	movw r9, #3776
	add r9, r12, r9
21:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 21b
	movw r6, #65535
	mov r3, #1
	movw r10, #3392
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r9, #3776
	add r9, r12, r9
22:
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
	bne 22b
	sub r2, r3, #1
	mov r8, r2
	mov r3, #0
	movw r10, #3392
	add r10, r12, r10
	movw r9, #3776
	add r9, r12, r9
23:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 23b
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
24:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 24b
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
25:
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
	bne 25b
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
26:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 26b
	ldr r11, [r12, #76]
	movw r8, #380
	add r8, r11, r8
	movw r10, #3392
	add r10, r12, r10
	movw r9, #3776
	add r9, r12, r9
27:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 27b
	movw r6, #65535
	mov r3, #1
	movw r10, #3392
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r9, #3776
	add r9, r12, r9
28:
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
	bne 28b
	sub r2, r3, #1
	mov r8, r2
	mov r3, #0
	movw r10, #3392
	add r10, r12, r10
	movw r9, #3776
	add r9, r12, r9
29:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 29b
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
210:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 210b
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
211:
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
	bne 211b
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
212:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 212b
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
213:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 213b
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
214:
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
	bne 214b
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
215:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 215b
	ldr r11, [r12, #68]
	movw r8, #28
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #288
	add r9, r12, r9
216:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 216b
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
217:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 217b
	movw r11, #14816
	add r11, r12, r11
	movw r8, #28
	add r8, r11, r8
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
218:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 218b
	mov r3, #0
	movw r10, #576
	add r10, r12, r10
	movw r9, #608
	add r9, r12, r9
219:
	ldr r4, [r10, #0]
	orr r3, r3, r4
	add r10, r10, #4
	cmp r10, r9
	bne 219b
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
220:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 220b
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
221:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 221b
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
222:
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
	bne 222b
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
223:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 223b
	ldr r11, [r12, #64]
	movw r8, #380
	add r8, r11, r8
	movw r10, #256
	add r10, r12, r10
	movw r9, #640
	add r9, r12, r9
224:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 224b
	ldr r11, [r12, #72]
	movw r8, #380
	add r8, r11, r8
	movw r10, #3392
	add r10, r12, r10
	movw r9, #3776
	add r9, r12, r9
225:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 225b
	ldr r11, [r12, #68]
	movw r8, #28
	add r8, r11, r8
	movw r10, #4568
	add r10, r12, r10
	movw r9, #4600
	add r9, r12, r9
226:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 226b
	movw r9, #352
	add r9, r10, r9
	mov r4, #0
227:
	str r4, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 227b
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
228:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 228b
	movw r11, #14944
	add r11, r12, r11
	movw r8, #380
	add r8, r11, r8
	movw r10, #3392
	add r10, r12, r10
	movw r9, #3776
	add r9, r12, r9
229:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 229b
	movw r10, #4568
	add r10, r12, r10
	movw r9, #4952
	add r9, r12, r9
	mov r7, #0
230:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 230b
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
231:
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
	bne 231b
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
233:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 233b
	ldr r11, [r12, #76]
	movw r8, #380
	add r8, r11, r8
	movw r10, #3392
	add r10, r12, r10
	movw r9, #3776
	add r9, r12, r9
234:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 234b
	ldr r11, [r12, #68]
	movw r8, #28
	add r8, r11, r8
	movw r10, #4568
	add r10, r12, r10
	movw r9, #4600
	add r9, r12, r9
235:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 235b
	movw r9, #352
	add r9, r10, r9
	mov r4, #0
236:
	str r4, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 236b
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
237:
	ldr r4, [r10, #0]
	and r4, r4, r3
	rev r4, r4
	str r4, [r8, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 237b
	movw r11, #14944
	add r11, r12, r11
	movw r8, #380
	add r8, r11, r8
	movw r10, #3392
	add r10, r12, r10
	movw r9, #3776
	add r9, r12, r9
238:
	ldr r4, [r8, #0]
	rev r4, r4
	str r4, [r10, #0]
	sub r8, r8, #4
	add r10, r10, #4
	cmp r10, r9
	bne 238b
	movw r10, #4568
	add r10, r12, r10
	movw r9, #4952
	add r9, r12, r9
	mov r7, #0
239:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 239b
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
	mov r8, r2
	movw r6, #65535
	mov r3, #1
	movw r10, #4568
	add r10, r12, r10
	movw r1, #3392
	add r1, r12, r1
	movw r9, #4952
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
	orr r2, r2, r8
	mov r4, #0
	sub r4, r4, #1
	eor r2, r2, r4
	ldr r4, [r12, #116]
	and r4, r4, r2
	str r4, [r12, #116]
	ldr r4, [r12, #168]
	ldr r5, [r12, #172]
	ldr r6, [r12, #176]
	ldr r7, [r12, #180]
	ldr r8, [r12, #184]
	ldr r9, [r12, #188]
	ldr r10, [r12, #192]
	ldr r11, [r12, #196]
	ldr lr, [r12, #200]
	bx lr
