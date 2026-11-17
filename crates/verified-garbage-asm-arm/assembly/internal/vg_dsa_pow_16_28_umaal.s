// The functions of `src/internal/vg_dsa_pow_16_28_umaal.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_dsa_pow_16_28_umaal:
	mov r12, r0
	str r4, [r12, #8]
	str r5, [r12, #12]
	str r6, [r12, #16]
	str r7, [r12, #20]
	str r8, [r12, #24]
	str r9, [r12, #28]
	str r10, [r12, #32]
	str r11, [r12, #36]
	str lr, [r12, #40]
	mov r4, r12
	mov r0, r12
	movw r1, #508
	bl {vg_dsa_context_16_umaal}
	mov r12, r4
	movw r10, #528
	add r10, r12, r10
	movw r9, #792
	add r9, r12, r9
	mov r7, #0
20:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 20b
	movw r5, #256
	add r5, r12, r5
	ldr r5, [r5, #0]
	ldr r4, [r12, #0]
	mul r6, r5, r4
	add r6, r6, #2
	mul r6, r6, r4
	mov r4, #0
	movw r0, #528
	add r0, r12, r0
	movw r1, #1208
	add r1, r12, r1
21:
	ldr r2, [r1, #0]
	mov r3, #0
	mov r10, r0
	movw r8, #1072
	add r8, r12, r8
	movw r9, #1200
	add r9, r12, r9
22:
	ldr r7, [r8, #0]
	ldr r5, [r10, #0]
	umaal r5, r3, r7, r2
	str r5, [r10, #0]
	ldr r7, [r8, #4]
	ldr r5, [r10, #4]
	umaal r5, r3, r7, r2
	str r5, [r10, #4]
	add r10, r10, #8
	add r8, r8, #8
	cmp r8, r9
	bne 22b
	ldr r5, [r10, #0]
	umaal r5, r3, r4, r4
	str r5, [r10, #0]
	ldr r7, [r10, #4]
	add r7, r7, r3
	str r7, [r10, #4]
	ldr r2, [r0, #0]
	mul r2, r2, r6
	mov r3, #0
	mov r10, r0
	movw r8, #256
	add r8, r12, r8
	movw r9, #384
	add r9, r12, r9
23:
	ldr r7, [r8, #0]
	ldr r5, [r10, #0]
	umaal r5, r3, r7, r2
	str r5, [r10, #0]
	ldr r7, [r8, #4]
	ldr r5, [r10, #4]
	umaal r5, r3, r7, r2
	str r5, [r10, #4]
	add r10, r10, #8
	add r8, r8, #8
	cmp r8, r9
	bne 23b
	ldr r5, [r10, #0]
	umaal r5, r3, r4, r4
	str r5, [r10, #0]
	ldr r7, [r10, #4]
	add r7, r7, r3
	str r7, [r10, #4]
	add r0, r0, #4
	add r1, r1, #4
	movw r9, #1336
	add r9, r12, r9
	cmp r1, r9
	bne 21b
	mov r3, #1
	mov r2, #1
	movw r10, #656
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r8, #392
	add r8, r12, r8
	movw r9, #384
	add r9, r12, r9
24:
	ldr r7, [r1, #0]
	mvn r7, r7
	ldr r5, [r10, #0]
	umaal r5, r3, r7, r2
	str r5, [r8, #0]
	add r10, r10, #4
	add r1, r1, #4
	add r8, r8, #4
	cmp r1, r9
	bne 24b
	ldr r5, [r10, #0]
	add r3, r3, r5
	mov r4, #0
	sub r3, r4, r3
	movw r10, #656
	add r10, r12, r10
	movw r8, #392
	add r8, r12, r8
	movw r1, #1616
	add r1, r12, r1
	movw r9, #784
	add r9, r12, r9
25:
	ldr r5, [r10, #0]
	ldr r7, [r8, #0]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [r1, #0]
	add r10, r10, #4
	add r8, r8, #4
	add r1, r1, #4
	cmp r10, r9
	bne 25b
	movw r10, #528
	add r10, r12, r10
	movw r9, #792
	add r9, r12, r9
	mov r7, #0
26:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 26b
	movw r5, #256
	add r5, r12, r5
	ldr r5, [r5, #0]
	ldr r4, [r12, #0]
	mul r6, r5, r4
	add r6, r6, #2
	mul r6, r6, r4
	mov r4, #0
	movw r0, #528
	add r0, r12, r0
	movw r1, #1344
	add r1, r12, r1
27:
	ldr r2, [r1, #0]
	mov r3, #0
	mov r10, r0
	movw r8, #1208
	add r8, r12, r8
	movw r9, #1336
	add r9, r12, r9
28:
	ldr r7, [r8, #0]
	ldr r5, [r10, #0]
	umaal r5, r3, r7, r2
	str r5, [r10, #0]
	ldr r7, [r8, #4]
	ldr r5, [r10, #4]
	umaal r5, r3, r7, r2
	str r5, [r10, #4]
	add r10, r10, #8
	add r8, r8, #8
	cmp r8, r9
	bne 28b
	ldr r5, [r10, #0]
	umaal r5, r3, r4, r4
	str r5, [r10, #0]
	ldr r7, [r10, #4]
	add r7, r7, r3
	str r7, [r10, #4]
	ldr r2, [r0, #0]
	mul r2, r2, r6
	mov r3, #0
	mov r10, r0
	movw r8, #256
	add r8, r12, r8
	movw r9, #384
	add r9, r12, r9
29:
	ldr r7, [r8, #0]
	ldr r5, [r10, #0]
	umaal r5, r3, r7, r2
	str r5, [r10, #0]
	ldr r7, [r8, #4]
	ldr r5, [r10, #4]
	umaal r5, r3, r7, r2
	str r5, [r10, #4]
	add r10, r10, #8
	add r8, r8, #8
	cmp r8, r9
	bne 29b
	ldr r5, [r10, #0]
	umaal r5, r3, r4, r4
	str r5, [r10, #0]
	ldr r7, [r10, #4]
	add r7, r7, r3
	str r7, [r10, #4]
	add r0, r0, #4
	add r1, r1, #4
	movw r9, #1472
	add r9, r12, r9
	cmp r1, r9
	bne 27b
	mov r3, #1
	mov r2, #1
	movw r10, #656
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r8, #392
	add r8, r12, r8
	movw r9, #384
	add r9, r12, r9
210:
	ldr r7, [r1, #0]
	mvn r7, r7
	ldr r5, [r10, #0]
	umaal r5, r3, r7, r2
	str r5, [r8, #0]
	add r10, r10, #4
	add r1, r1, #4
	add r8, r8, #4
	cmp r1, r9
	bne 210b
	ldr r5, [r10, #0]
	add r3, r3, r5
	mov r4, #0
	sub r3, r4, r3
	movw r10, #656
	add r10, r12, r10
	movw r8, #392
	add r8, r12, r8
	movw r1, #1344
	add r1, r12, r1
	movw r9, #784
	add r9, r12, r9
211:
	ldr r5, [r10, #0]
	ldr r7, [r8, #0]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [r1, #0]
	add r10, r10, #4
	add r8, r8, #4
	add r1, r1, #4
	cmp r10, r9
	bne 211b
	movw r11, #1888
	add r11, r12, r11
	mov lr, #16
212:
	movw r10, #1616
	add r10, r12, r10
	movw r9, #1744
	add r9, r12, r9
213:
	ldr r5, [r10, #0]
	str r5, [r11, #0]
	add r10, r10, #4
	add r11, r11, #4
	cmp r10, r9
	bne 213b
	movw r10, #528
	add r10, r12, r10
	movw r9, #792
	add r9, r12, r9
	mov r7, #0
214:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 214b
	movw r5, #256
	add r5, r12, r5
	ldr r5, [r5, #0]
	ldr r4, [r12, #0]
	mul r6, r5, r4
	add r6, r6, #2
	mul r6, r6, r4
	mov r4, #0
	movw r0, #528
	add r0, r12, r0
	movw r1, #1616
	add r1, r12, r1
215:
	ldr r2, [r1, #0]
	mov r3, #0
	mov r10, r0
	movw r8, #1344
	add r8, r12, r8
	movw r9, #1472
	add r9, r12, r9
216:
	ldr r7, [r8, #0]
	ldr r5, [r10, #0]
	umaal r5, r3, r7, r2
	str r5, [r10, #0]
	ldr r7, [r8, #4]
	ldr r5, [r10, #4]
	umaal r5, r3, r7, r2
	str r5, [r10, #4]
	add r10, r10, #8
	add r8, r8, #8
	cmp r8, r9
	bne 216b
	ldr r5, [r10, #0]
	umaal r5, r3, r4, r4
	str r5, [r10, #0]
	ldr r7, [r10, #4]
	add r7, r7, r3
	str r7, [r10, #4]
	ldr r2, [r0, #0]
	mul r2, r2, r6
	mov r3, #0
	mov r10, r0
	movw r8, #256
	add r8, r12, r8
	movw r9, #384
	add r9, r12, r9
217:
	ldr r7, [r8, #0]
	ldr r5, [r10, #0]
	umaal r5, r3, r7, r2
	str r5, [r10, #0]
	ldr r7, [r8, #4]
	ldr r5, [r10, #4]
	umaal r5, r3, r7, r2
	str r5, [r10, #4]
	add r10, r10, #8
	add r8, r8, #8
	cmp r8, r9
	bne 217b
	ldr r5, [r10, #0]
	umaal r5, r3, r4, r4
	str r5, [r10, #0]
	ldr r7, [r10, #4]
	add r7, r7, r3
	str r7, [r10, #4]
	add r0, r0, #4
	add r1, r1, #4
	movw r9, #1744
	add r9, r12, r9
	cmp r1, r9
	bne 215b
	mov r3, #1
	mov r2, #1
	movw r10, #656
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r8, #392
	add r8, r12, r8
	movw r9, #384
	add r9, r12, r9
218:
	ldr r7, [r1, #0]
	mvn r7, r7
	ldr r5, [r10, #0]
	umaal r5, r3, r7, r2
	str r5, [r8, #0]
	add r10, r10, #4
	add r1, r1, #4
	add r8, r8, #4
	cmp r1, r9
	bne 218b
	ldr r5, [r10, #0]
	add r3, r3, r5
	mov r4, #0
	sub r3, r4, r3
	movw r10, #656
	add r10, r12, r10
	movw r8, #392
	add r8, r12, r8
	movw r1, #1616
	add r1, r12, r1
	movw r9, #784
	add r9, r12, r9
219:
	ldr r5, [r10, #0]
	ldr r7, [r8, #0]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [r1, #0]
	add r10, r10, #4
	add r8, r8, #4
	add r1, r1, #4
	cmp r10, r9
	bne 219b
	add r11, r11, #8
	subs lr, lr, #1
	bne 212b
	movw r10, #528
	add r10, r12, r10
	movw r9, #792
	add r9, r12, r9
	mov r7, #0
220:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 220b
	movw r5, #256
	add r5, r12, r5
	ldr r5, [r5, #0]
	ldr r4, [r12, #0]
	mul r6, r5, r4
	add r6, r6, #2
	mul r6, r6, r4
	mov r4, #0
	movw r0, #528
	add r0, r12, r0
	movw r1, #1208
	add r1, r12, r1
221:
	ldr r2, [r1, #0]
	mov r3, #0
	mov r10, r0
	movw r8, #1072
	add r8, r12, r8
	movw r9, #1200
	add r9, r12, r9
222:
	ldr r7, [r8, #0]
	ldr r5, [r10, #0]
	umaal r5, r3, r7, r2
	str r5, [r10, #0]
	ldr r7, [r8, #4]
	ldr r5, [r10, #4]
	umaal r5, r3, r7, r2
	str r5, [r10, #4]
	add r10, r10, #8
	add r8, r8, #8
	cmp r8, r9
	bne 222b
	ldr r5, [r10, #0]
	umaal r5, r3, r4, r4
	str r5, [r10, #0]
	ldr r7, [r10, #4]
	add r7, r7, r3
	str r7, [r10, #4]
	ldr r2, [r0, #0]
	mul r2, r2, r6
	mov r3, #0
	mov r10, r0
	movw r8, #256
	add r8, r12, r8
	movw r9, #384
	add r9, r12, r9
223:
	ldr r7, [r8, #0]
	ldr r5, [r10, #0]
	umaal r5, r3, r7, r2
	str r5, [r10, #0]
	ldr r7, [r8, #4]
	ldr r5, [r10, #4]
	umaal r5, r3, r7, r2
	str r5, [r10, #4]
	add r10, r10, #8
	add r8, r8, #8
	cmp r8, r9
	bne 223b
	ldr r5, [r10, #0]
	umaal r5, r3, r4, r4
	str r5, [r10, #0]
	ldr r7, [r10, #4]
	add r7, r7, r3
	str r7, [r10, #4]
	add r0, r0, #4
	add r1, r1, #4
	movw r9, #1336
	add r9, r12, r9
	cmp r1, r9
	bne 221b
	mov r3, #1
	mov r2, #1
	movw r10, #656
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r8, #392
	add r8, r12, r8
	movw r9, #384
	add r9, r12, r9
224:
	ldr r7, [r1, #0]
	mvn r7, r7
	ldr r5, [r10, #0]
	umaal r5, r3, r7, r2
	str r5, [r8, #0]
	add r10, r10, #4
	add r1, r1, #4
	add r8, r8, #4
	cmp r1, r9
	bne 224b
	ldr r5, [r10, #0]
	add r3, r3, r5
	mov r4, #0
	sub r3, r4, r3
	movw r10, #656
	add r10, r12, r10
	movw r8, #392
	add r8, r12, r8
	movw r1, #1480
	add r1, r12, r1
	movw r9, #784
	add r9, r12, r9
225:
	ldr r5, [r10, #0]
	ldr r7, [r8, #0]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [r1, #0]
	add r10, r10, #4
	add r8, r8, #4
	add r1, r1, #4
	cmp r10, r9
	bne 225b
	movw lr, #224
226:
	mov r11, #4
227:
	movw r10, #528
	add r10, r12, r10
	movw r9, #792
	add r9, r12, r9
	mov r7, #0
228:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 228b
	movw r5, #256
	add r5, r12, r5
	ldr r5, [r5, #0]
	ldr r4, [r12, #0]
	mul r6, r5, r4
	add r6, r6, #2
	mul r6, r6, r4
	mov r4, #0
	movw r0, #528
	add r0, r12, r0
	movw r1, #1480
	add r1, r12, r1
229:
	ldr r2, [r1, #0]
	mov r3, #0
	mov r10, r0
	movw r8, #1480
	add r8, r12, r8
	movw r9, #1608
	add r9, r12, r9
230:
	ldr r7, [r8, #0]
	ldr r5, [r10, #0]
	umaal r5, r3, r7, r2
	str r5, [r10, #0]
	ldr r7, [r8, #4]
	ldr r5, [r10, #4]
	umaal r5, r3, r7, r2
	str r5, [r10, #4]
	add r10, r10, #8
	add r8, r8, #8
	cmp r8, r9
	bne 230b
	ldr r5, [r10, #0]
	umaal r5, r3, r4, r4
	str r5, [r10, #0]
	ldr r7, [r10, #4]
	add r7, r7, r3
	str r7, [r10, #4]
	ldr r2, [r0, #0]
	mul r2, r2, r6
	mov r3, #0
	mov r10, r0
	movw r8, #256
	add r8, r12, r8
	movw r9, #384
	add r9, r12, r9
231:
	ldr r7, [r8, #0]
	ldr r5, [r10, #0]
	umaal r5, r3, r7, r2
	str r5, [r10, #0]
	ldr r7, [r8, #4]
	ldr r5, [r10, #4]
	umaal r5, r3, r7, r2
	str r5, [r10, #4]
	add r10, r10, #8
	add r8, r8, #8
	cmp r8, r9
	bne 231b
	ldr r5, [r10, #0]
	umaal r5, r3, r4, r4
	str r5, [r10, #0]
	ldr r7, [r10, #4]
	add r7, r7, r3
	str r7, [r10, #4]
	add r0, r0, #4
	add r1, r1, #4
	movw r9, #1608
	add r9, r12, r9
	cmp r1, r9
	bne 229b
	mov r3, #1
	mov r2, #1
	movw r10, #656
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r8, #392
	add r8, r12, r8
	movw r9, #384
	add r9, r12, r9
232:
	ldr r7, [r1, #0]
	mvn r7, r7
	ldr r5, [r10, #0]
	umaal r5, r3, r7, r2
	str r5, [r8, #0]
	add r10, r10, #4
	add r1, r1, #4
	add r8, r8, #4
	cmp r1, r9
	bne 232b
	ldr r5, [r10, #0]
	add r3, r3, r5
	mov r4, #0
	sub r3, r4, r3
	movw r10, #656
	add r10, r12, r10
	movw r8, #392
	add r8, r12, r8
	movw r1, #1480
	add r1, r12, r1
	movw r9, #784
	add r9, r12, r9
233:
	ldr r5, [r10, #0]
	ldr r7, [r8, #0]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [r1, #0]
	add r10, r10, #4
	add r8, r8, #4
	add r1, r1, #4
	cmp r10, r9
	bne 233b
	subs r11, r11, #1
	bne 227b
	movw r1, #1752
	add r1, r12, r1
	mov r2, #0
	ldr r4, [r1, #0]
	orr r5, r2, r4, lsl #4
	lsr r2, r4, #28
	str r5, [r1, #0]
	ldr r4, [r1, #4]
	orr r5, r2, r4, lsl #4
	lsr r2, r4, #28
	str r5, [r1, #4]
	ldr r4, [r1, #8]
	orr r5, r2, r4, lsl #4
	lsr r2, r4, #28
	str r5, [r1, #8]
	ldr r4, [r1, #12]
	orr r5, r2, r4, lsl #4
	lsr r2, r4, #28
	str r5, [r1, #12]
	ldr r4, [r1, #16]
	orr r5, r2, r4, lsl #4
	lsr r2, r4, #28
	str r5, [r1, #16]
	ldr r4, [r1, #20]
	orr r5, r2, r4, lsl #4
	lsr r2, r4, #28
	str r5, [r1, #20]
	ldr r4, [r1, #24]
	orr r5, r2, r4, lsl #4
	lsr r2, r4, #28
	str r5, [r1, #24]
	ldr r4, [r1, #28]
	orr r5, r2, r4, lsl #4
	lsr r2, r4, #28
	str r5, [r1, #28]
	ldr r4, [r1, #32]
	orr r5, r2, r4, lsl #4
	lsr r2, r4, #28
	str r5, [r1, #32]
	ldr r4, [r1, #36]
	orr r5, r2, r4, lsl #4
	lsr r2, r4, #28
	str r5, [r1, #36]
	ldr r4, [r1, #40]
	orr r5, r2, r4, lsl #4
	lsr r2, r4, #28
	str r5, [r1, #40]
	ldr r4, [r1, #44]
	orr r5, r2, r4, lsl #4
	lsr r2, r4, #28
	str r5, [r1, #44]
	ldr r4, [r1, #48]
	orr r5, r2, r4, lsl #4
	lsr r2, r4, #28
	str r5, [r1, #48]
	ldr r4, [r1, #52]
	orr r5, r2, r4, lsl #4
	lsr r2, r4, #28
	str r5, [r1, #52]
	ldr r4, [r1, #56]
	orr r5, r2, r4, lsl #4
	lsr r2, r4, #28
	str r5, [r1, #56]
	ldr r4, [r1, #60]
	orr r5, r2, r4, lsl #4
	lsr r2, r4, #28
	str r5, [r1, #60]
	ldr r4, [r1, #64]
	orr r5, r2, r4, lsl #4
	lsr r2, r4, #28
	str r5, [r1, #64]
	ldr r4, [r1, #68]
	orr r5, r2, r4, lsl #4
	lsr r2, r4, #28
	str r5, [r1, #68]
	ldr r4, [r1, #72]
	orr r5, r2, r4, lsl #4
	lsr r2, r4, #28
	str r5, [r1, #72]
	ldr r4, [r1, #76]
	orr r5, r2, r4, lsl #4
	lsr r2, r4, #28
	str r5, [r1, #76]
	ldr r4, [r1, #80]
	orr r5, r2, r4, lsl #4
	lsr r2, r4, #28
	str r5, [r1, #80]
	ldr r4, [r1, #84]
	orr r5, r2, r4, lsl #4
	lsr r2, r4, #28
	str r5, [r1, #84]
	ldr r4, [r1, #88]
	orr r5, r2, r4, lsl #4
	lsr r2, r4, #28
	str r5, [r1, #88]
	ldr r4, [r1, #92]
	orr r5, r2, r4, lsl #4
	lsr r2, r4, #28
	str r5, [r1, #92]
	ldr r4, [r1, #96]
	orr r5, r2, r4, lsl #4
	lsr r2, r4, #28
	str r5, [r1, #96]
	ldr r4, [r1, #100]
	orr r5, r2, r4, lsl #4
	lsr r2, r4, #28
	str r5, [r1, #100]
	ldr r4, [r1, #104]
	orr r5, r2, r4, lsl #4
	lsr r2, r4, #28
	str r5, [r1, #104]
	ldr r4, [r1, #108]
	orr r5, r2, r4, lsl #4
	lsr r2, r4, #28
	str r5, [r1, #108]
	eor r3, r2, #0
	sub r3, r3, #1
	lsr r3, r3, #31
	mov r4, #0
	sub r3, r4, r3
	movw r10, #1616
	add r10, r12, r10
	movw r8, #1888
	add r8, r12, r8
	movw r1, #1616
	add r1, r12, r1
	movw r9, #1744
	add r9, r12, r9
234:
	ldr r5, [r10, #0]
	ldr r7, [r8, #0]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [r1, #0]
	add r10, r10, #4
	add r8, r8, #4
	add r1, r1, #4
	cmp r10, r9
	bne 234b
	eor r3, r2, #1
	sub r3, r3, #1
	lsr r3, r3, #31
	mov r4, #0
	sub r3, r4, r3
	movw r10, #1616
	add r10, r12, r10
	movw r8, #2024
	add r8, r12, r8
	movw r1, #1616
	add r1, r12, r1
	movw r9, #1744
	add r9, r12, r9
235:
	ldr r5, [r10, #0]
	ldr r7, [r8, #0]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [r1, #0]
	add r10, r10, #4
	add r8, r8, #4
	add r1, r1, #4
	cmp r10, r9
	bne 235b
	eor r3, r2, #2
	sub r3, r3, #1
	lsr r3, r3, #31
	mov r4, #0
	sub r3, r4, r3
	movw r10, #1616
	add r10, r12, r10
	movw r8, #2160
	add r8, r12, r8
	movw r1, #1616
	add r1, r12, r1
	movw r9, #1744
	add r9, r12, r9
236:
	ldr r5, [r10, #0]
	ldr r7, [r8, #0]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [r1, #0]
	add r10, r10, #4
	add r8, r8, #4
	add r1, r1, #4
	cmp r10, r9
	bne 236b
	eor r3, r2, #3
	sub r3, r3, #1
	lsr r3, r3, #31
	mov r4, #0
	sub r3, r4, r3
	movw r10, #1616
	add r10, r12, r10
	movw r8, #2296
	add r8, r12, r8
	movw r1, #1616
	add r1, r12, r1
	movw r9, #1744
	add r9, r12, r9
237:
	ldr r5, [r10, #0]
	ldr r7, [r8, #0]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [r1, #0]
	add r10, r10, #4
	add r8, r8, #4
	add r1, r1, #4
	cmp r10, r9
	bne 237b
	eor r3, r2, #4
	sub r3, r3, #1
	lsr r3, r3, #31
	mov r4, #0
	sub r3, r4, r3
	movw r10, #1616
	add r10, r12, r10
	movw r8, #2432
	add r8, r12, r8
	movw r1, #1616
	add r1, r12, r1
	movw r9, #1744
	add r9, r12, r9
238:
	ldr r5, [r10, #0]
	ldr r7, [r8, #0]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [r1, #0]
	add r10, r10, #4
	add r8, r8, #4
	add r1, r1, #4
	cmp r10, r9
	bne 238b
	eor r3, r2, #5
	sub r3, r3, #1
	lsr r3, r3, #31
	mov r4, #0
	sub r3, r4, r3
	movw r10, #1616
	add r10, r12, r10
	movw r8, #2568
	add r8, r12, r8
	movw r1, #1616
	add r1, r12, r1
	movw r9, #1744
	add r9, r12, r9
239:
	ldr r5, [r10, #0]
	ldr r7, [r8, #0]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [r1, #0]
	add r10, r10, #4
	add r8, r8, #4
	add r1, r1, #4
	cmp r10, r9
	bne 239b
	eor r3, r2, #6
	sub r3, r3, #1
	lsr r3, r3, #31
	mov r4, #0
	sub r3, r4, r3
	movw r10, #1616
	add r10, r12, r10
	movw r8, #2704
	add r8, r12, r8
	movw r1, #1616
	add r1, r12, r1
	movw r9, #1744
	add r9, r12, r9
240:
	ldr r5, [r10, #0]
	ldr r7, [r8, #0]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [r1, #0]
	add r10, r10, #4
	add r8, r8, #4
	add r1, r1, #4
	cmp r10, r9
	bne 240b
	eor r3, r2, #7
	sub r3, r3, #1
	lsr r3, r3, #31
	mov r4, #0
	sub r3, r4, r3
	movw r10, #1616
	add r10, r12, r10
	movw r8, #2840
	add r8, r12, r8
	movw r1, #1616
	add r1, r12, r1
	movw r9, #1744
	add r9, r12, r9
241:
	ldr r5, [r10, #0]
	ldr r7, [r8, #0]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [r1, #0]
	add r10, r10, #4
	add r8, r8, #4
	add r1, r1, #4
	cmp r10, r9
	bne 241b
	eor r3, r2, #8
	sub r3, r3, #1
	lsr r3, r3, #31
	mov r4, #0
	sub r3, r4, r3
	movw r10, #1616
	add r10, r12, r10
	movw r8, #2976
	add r8, r12, r8
	movw r1, #1616
	add r1, r12, r1
	movw r9, #1744
	add r9, r12, r9
242:
	ldr r5, [r10, #0]
	ldr r7, [r8, #0]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [r1, #0]
	add r10, r10, #4
	add r8, r8, #4
	add r1, r1, #4
	cmp r10, r9
	bne 242b
	eor r3, r2, #9
	sub r3, r3, #1
	lsr r3, r3, #31
	mov r4, #0
	sub r3, r4, r3
	movw r10, #1616
	add r10, r12, r10
	movw r8, #3112
	add r8, r12, r8
	movw r1, #1616
	add r1, r12, r1
	movw r9, #1744
	add r9, r12, r9
243:
	ldr r5, [r10, #0]
	ldr r7, [r8, #0]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [r1, #0]
	add r10, r10, #4
	add r8, r8, #4
	add r1, r1, #4
	cmp r10, r9
	bne 243b
	eor r3, r2, #10
	sub r3, r3, #1
	lsr r3, r3, #31
	mov r4, #0
	sub r3, r4, r3
	movw r10, #1616
	add r10, r12, r10
	movw r8, #3248
	add r8, r12, r8
	movw r1, #1616
	add r1, r12, r1
	movw r9, #1744
	add r9, r12, r9
244:
	ldr r5, [r10, #0]
	ldr r7, [r8, #0]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [r1, #0]
	add r10, r10, #4
	add r8, r8, #4
	add r1, r1, #4
	cmp r10, r9
	bne 244b
	eor r3, r2, #11
	sub r3, r3, #1
	lsr r3, r3, #31
	mov r4, #0
	sub r3, r4, r3
	movw r10, #1616
	add r10, r12, r10
	movw r8, #3384
	add r8, r12, r8
	movw r1, #1616
	add r1, r12, r1
	movw r9, #1744
	add r9, r12, r9
245:
	ldr r5, [r10, #0]
	ldr r7, [r8, #0]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [r1, #0]
	add r10, r10, #4
	add r8, r8, #4
	add r1, r1, #4
	cmp r10, r9
	bne 245b
	eor r3, r2, #12
	sub r3, r3, #1
	lsr r3, r3, #31
	mov r4, #0
	sub r3, r4, r3
	movw r10, #1616
	add r10, r12, r10
	movw r8, #3520
	add r8, r12, r8
	movw r1, #1616
	add r1, r12, r1
	movw r9, #1744
	add r9, r12, r9
246:
	ldr r5, [r10, #0]
	ldr r7, [r8, #0]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [r1, #0]
	add r10, r10, #4
	add r8, r8, #4
	add r1, r1, #4
	cmp r10, r9
	bne 246b
	eor r3, r2, #13
	sub r3, r3, #1
	lsr r3, r3, #31
	mov r4, #0
	sub r3, r4, r3
	movw r10, #1616
	add r10, r12, r10
	movw r8, #3656
	add r8, r12, r8
	movw r1, #1616
	add r1, r12, r1
	movw r9, #1744
	add r9, r12, r9
247:
	ldr r5, [r10, #0]
	ldr r7, [r8, #0]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [r1, #0]
	add r10, r10, #4
	add r8, r8, #4
	add r1, r1, #4
	cmp r10, r9
	bne 247b
	eor r3, r2, #14
	sub r3, r3, #1
	lsr r3, r3, #31
	mov r4, #0
	sub r3, r4, r3
	movw r10, #1616
	add r10, r12, r10
	movw r8, #3792
	add r8, r12, r8
	movw r1, #1616
	add r1, r12, r1
	movw r9, #1744
	add r9, r12, r9
248:
	ldr r5, [r10, #0]
	ldr r7, [r8, #0]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [r1, #0]
	add r10, r10, #4
	add r8, r8, #4
	add r1, r1, #4
	cmp r10, r9
	bne 248b
	eor r3, r2, #15
	sub r3, r3, #1
	lsr r3, r3, #31
	mov r4, #0
	sub r3, r4, r3
	movw r10, #1616
	add r10, r12, r10
	movw r8, #3928
	add r8, r12, r8
	movw r1, #1616
	add r1, r12, r1
	movw r9, #1744
	add r9, r12, r9
249:
	ldr r5, [r10, #0]
	ldr r7, [r8, #0]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [r1, #0]
	add r10, r10, #4
	add r8, r8, #4
	add r1, r1, #4
	cmp r10, r9
	bne 249b
	movw r10, #528
	add r10, r12, r10
	movw r9, #792
	add r9, r12, r9
	mov r7, #0
250:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 250b
	movw r5, #256
	add r5, r12, r5
	ldr r5, [r5, #0]
	ldr r4, [r12, #0]
	mul r6, r5, r4
	add r6, r6, #2
	mul r6, r6, r4
	mov r4, #0
	movw r0, #528
	add r0, r12, r0
	movw r1, #1480
	add r1, r12, r1
251:
	ldr r2, [r1, #0]
	mov r3, #0
	mov r10, r0
	movw r8, #1616
	add r8, r12, r8
	movw r9, #1744
	add r9, r12, r9
252:
	ldr r7, [r8, #0]
	ldr r5, [r10, #0]
	umaal r5, r3, r7, r2
	str r5, [r10, #0]
	ldr r7, [r8, #4]
	ldr r5, [r10, #4]
	umaal r5, r3, r7, r2
	str r5, [r10, #4]
	add r10, r10, #8
	add r8, r8, #8
	cmp r8, r9
	bne 252b
	ldr r5, [r10, #0]
	umaal r5, r3, r4, r4
	str r5, [r10, #0]
	ldr r7, [r10, #4]
	add r7, r7, r3
	str r7, [r10, #4]
	ldr r2, [r0, #0]
	mul r2, r2, r6
	mov r3, #0
	mov r10, r0
	movw r8, #256
	add r8, r12, r8
	movw r9, #384
	add r9, r12, r9
253:
	ldr r7, [r8, #0]
	ldr r5, [r10, #0]
	umaal r5, r3, r7, r2
	str r5, [r10, #0]
	ldr r7, [r8, #4]
	ldr r5, [r10, #4]
	umaal r5, r3, r7, r2
	str r5, [r10, #4]
	add r10, r10, #8
	add r8, r8, #8
	cmp r8, r9
	bne 253b
	ldr r5, [r10, #0]
	umaal r5, r3, r4, r4
	str r5, [r10, #0]
	ldr r7, [r10, #4]
	add r7, r7, r3
	str r7, [r10, #4]
	add r0, r0, #4
	add r1, r1, #4
	movw r9, #1608
	add r9, r12, r9
	cmp r1, r9
	bne 251b
	mov r3, #1
	mov r2, #1
	movw r10, #656
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r8, #392
	add r8, r12, r8
	movw r9, #384
	add r9, r12, r9
254:
	ldr r7, [r1, #0]
	mvn r7, r7
	ldr r5, [r10, #0]
	umaal r5, r3, r7, r2
	str r5, [r8, #0]
	add r10, r10, #4
	add r1, r1, #4
	add r8, r8, #4
	cmp r1, r9
	bne 254b
	ldr r5, [r10, #0]
	add r3, r3, r5
	mov r4, #0
	sub r3, r4, r3
	movw r10, #656
	add r10, r12, r10
	movw r8, #392
	add r8, r12, r8
	movw r1, #1480
	add r1, r12, r1
	movw r9, #784
	add r9, r12, r9
255:
	ldr r5, [r10, #0]
	ldr r7, [r8, #0]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [r1, #0]
	add r10, r10, #4
	add r8, r8, #4
	add r1, r1, #4
	cmp r10, r9
	bne 255b
	subs lr, lr, #1
	bne 226b
	movw r10, #528
	add r10, r12, r10
	movw r9, #792
	add r9, r12, r9
	mov r7, #0
256:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 256b
	movw r5, #256
	add r5, r12, r5
	ldr r5, [r5, #0]
	ldr r4, [r12, #0]
	mul r6, r5, r4
	add r6, r6, #2
	mul r6, r6, r4
	mov r4, #0
	movw r0, #528
	add r0, r12, r0
	movw r1, #1480
	add r1, r12, r1
257:
	ldr r2, [r1, #0]
	mov r3, #0
	mov r10, r0
	movw r8, #1072
	add r8, r12, r8
	movw r9, #1200
	add r9, r12, r9
258:
	ldr r7, [r8, #0]
	ldr r5, [r10, #0]
	umaal r5, r3, r7, r2
	str r5, [r10, #0]
	ldr r7, [r8, #4]
	ldr r5, [r10, #4]
	umaal r5, r3, r7, r2
	str r5, [r10, #4]
	add r10, r10, #8
	add r8, r8, #8
	cmp r8, r9
	bne 258b
	ldr r5, [r10, #0]
	umaal r5, r3, r4, r4
	str r5, [r10, #0]
	ldr r7, [r10, #4]
	add r7, r7, r3
	str r7, [r10, #4]
	ldr r2, [r0, #0]
	mul r2, r2, r6
	mov r3, #0
	mov r10, r0
	movw r8, #256
	add r8, r12, r8
	movw r9, #384
	add r9, r12, r9
259:
	ldr r7, [r8, #0]
	ldr r5, [r10, #0]
	umaal r5, r3, r7, r2
	str r5, [r10, #0]
	ldr r7, [r8, #4]
	ldr r5, [r10, #4]
	umaal r5, r3, r7, r2
	str r5, [r10, #4]
	add r10, r10, #8
	add r8, r8, #8
	cmp r8, r9
	bne 259b
	ldr r5, [r10, #0]
	umaal r5, r3, r4, r4
	str r5, [r10, #0]
	ldr r7, [r10, #4]
	add r7, r7, r3
	str r7, [r10, #4]
	add r0, r0, #4
	add r1, r1, #4
	movw r9, #1608
	add r9, r12, r9
	cmp r1, r9
	bne 257b
	mov r3, #1
	mov r2, #1
	movw r10, #656
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r8, #392
	add r8, r12, r8
	movw r9, #384
	add r9, r12, r9
260:
	ldr r7, [r1, #0]
	mvn r7, r7
	ldr r5, [r10, #0]
	umaal r5, r3, r7, r2
	str r5, [r8, #0]
	add r10, r10, #4
	add r1, r1, #4
	add r8, r8, #4
	cmp r1, r9
	bne 260b
	ldr r5, [r10, #0]
	add r3, r3, r5
	mov r4, #0
	sub r3, r4, r3
	movw r10, #656
	add r10, r12, r10
	movw r8, #392
	add r8, r12, r8
	movw r1, #1480
	add r1, r12, r1
	movw r9, #784
	add r9, r12, r9
261:
	ldr r5, [r10, #0]
	ldr r7, [r8, #0]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [r1, #0]
	add r10, r10, #4
	add r8, r8, #4
	add r1, r1, #4
	cmp r10, r9
	bne 261b
	ldr r4, [r12, #8]
	ldr r5, [r12, #12]
	ldr r6, [r12, #16]
	ldr r7, [r12, #20]
	ldr r8, [r12, #24]
	ldr r9, [r12, #28]
	ldr r10, [r12, #32]
	ldr r11, [r12, #36]
	ldr lr, [r12, #40]
	bx lr
