// The functions of `src/sm4_ofb.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_ofb:
	sub sp, sp, #1520
	add r12, sp, #0
	str lr, [r12, #4]
	add lr, sp, #8
	str lr, [r12, #0]
	ldr lr, [sp, #4]
	ldr r12, [sp, #0]
	str r4, [r12, #1456]
	str r5, [r12, #1460]
	str r6, [r12, #1464]
	str r7, [r12, #1468]
	str r8, [r12, #1472]
	str r9, [r12, #1476]
	str r10, [r12, #1480]
	str r11, [r12, #1484]
	str lr, [r12, #1488]
	mov r8, r12
	mov r4, r0
	mov r5, r1
	mov r6, r2
	mov r7, r3
	mov r0, r4
	mov r1, #0
	mov r2, r8
	mov r3, #182
	bl {vg_sm4_prepare_keys}
	ldr r9, [r5, #0]
	str r9, [r8, #1492]
	ldr r9, [r5, #4]
	str r9, [r8, #1496]
	ldr r9, [r5, #8]
	str r9, [r8, #1500]
	ldr r9, [r5, #12]
	str r9, [r8, #1504]
	cmp r7, #0
	beq 20f
22:
	mov r11, #1
	ldr r9, [r8, #1492]
	str r9, [r8, #256]
	ldr r9, [r8, #1496]
	str r9, [r8, #260]
	ldr r9, [r8, #1500]
	str r9, [r8, #264]
	ldr r9, [r8, #1504]
	str r9, [r8, #268]
	cmp r11, #1
	beq 23f
	ldr r9, [r6, #0]
	str r9, [r8, #272]
	ldr r9, [r6, #4]
	str r9, [r8, #276]
	ldr r9, [r6, #8]
	str r9, [r8, #280]
	ldr r9, [r6, #12]
	str r9, [r8, #284]
	cmp r11, #2
	beq 25f
	ldr r9, [r6, #16]
	str r9, [r8, #288]
	ldr r9, [r6, #20]
	str r9, [r8, #292]
	ldr r9, [r6, #24]
	str r9, [r8, #296]
	ldr r9, [r6, #28]
	str r9, [r8, #300]
	cmp r11, #3
	beq 27f
	ldr r9, [r6, #32]
	str r9, [r8, #304]
	ldr r9, [r6, #36]
	str r9, [r8, #308]
	ldr r9, [r6, #40]
	str r9, [r8, #312]
	ldr r9, [r6, #44]
	str r9, [r8, #316]
	cmp r11, #4
	beq 29f
	ldr r9, [r6, #48]
	str r9, [r8, #320]
	ldr r9, [r6, #52]
	str r9, [r8, #324]
	ldr r9, [r6, #56]
	str r9, [r8, #328]
	ldr r9, [r6, #60]
	str r9, [r8, #332]
	cmp r11, #5
	beq 211f
	ldr r9, [r6, #64]
	str r9, [r8, #336]
	ldr r9, [r6, #68]
	str r9, [r8, #340]
	ldr r9, [r6, #72]
	str r9, [r8, #344]
	ldr r9, [r6, #76]
	str r9, [r8, #348]
	cmp r11, #6
	beq 213f
	ldr r9, [r6, #80]
	str r9, [r8, #352]
	ldr r9, [r6, #84]
	str r9, [r8, #356]
	ldr r9, [r6, #88]
	str r9, [r8, #360]
	ldr r9, [r6, #92]
	str r9, [r8, #364]
	cmp r11, #7
	beq 215f
	ldr r9, [r6, #96]
	str r9, [r8, #368]
	ldr r9, [r6, #100]
	str r9, [r8, #372]
	ldr r9, [r6, #104]
	str r9, [r8, #376]
	ldr r9, [r6, #108]
	str r9, [r8, #380]
	cmp r11, #8
	beq 217f
	ldr r9, [r6, #112]
	str r9, [r8, #384]
	ldr r9, [r6, #116]
	str r9, [r8, #388]
	ldr r9, [r6, #120]
	str r9, [r8, #392]
	ldr r9, [r6, #124]
	str r9, [r8, #396]
	b 218f
217:
	ldr r9, [r6, #112]
	str r9, [r8, #1492]
	ldr r9, [r6, #116]
	str r9, [r8, #1496]
	ldr r9, [r6, #120]
	str r9, [r8, #1500]
	ldr r9, [r6, #124]
	str r9, [r8, #1504]
218:
	b 216f
215:
	ldr r9, [r6, #96]
	str r9, [r8, #1492]
	ldr r9, [r6, #100]
	str r9, [r8, #1496]
	ldr r9, [r6, #104]
	str r9, [r8, #1500]
	ldr r9, [r6, #108]
	str r9, [r8, #1504]
216:
	b 214f
213:
	ldr r9, [r6, #80]
	str r9, [r8, #1492]
	ldr r9, [r6, #84]
	str r9, [r8, #1496]
	ldr r9, [r6, #88]
	str r9, [r8, #1500]
	ldr r9, [r6, #92]
	str r9, [r8, #1504]
214:
	b 212f
211:
	ldr r9, [r6, #64]
	str r9, [r8, #1492]
	ldr r9, [r6, #68]
	str r9, [r8, #1496]
	ldr r9, [r6, #72]
	str r9, [r8, #1500]
	ldr r9, [r6, #76]
	str r9, [r8, #1504]
212:
	b 210f
29:
	ldr r9, [r6, #48]
	str r9, [r8, #1492]
	ldr r9, [r6, #52]
	str r9, [r8, #1496]
	ldr r9, [r6, #56]
	str r9, [r8, #1500]
	ldr r9, [r6, #60]
	str r9, [r8, #1504]
210:
	b 28f
27:
	ldr r9, [r6, #32]
	str r9, [r8, #1492]
	ldr r9, [r6, #36]
	str r9, [r8, #1496]
	ldr r9, [r6, #40]
	str r9, [r8, #1500]
	ldr r9, [r6, #44]
	str r9, [r8, #1504]
28:
	b 26f
25:
	ldr r9, [r6, #16]
	str r9, [r8, #1492]
	ldr r9, [r6, #20]
	str r9, [r8, #1496]
	ldr r9, [r6, #24]
	str r9, [r8, #1500]
	ldr r9, [r6, #28]
	str r9, [r8, #1504]
26:
	b 24f
23:
	ldr r9, [r6, #0]
	str r9, [r8, #1492]
	ldr r9, [r6, #4]
	str r9, [r8, #1496]
	ldr r9, [r6, #8]
	str r9, [r8, #1500]
	ldr r9, [r6, #12]
	str r9, [r8, #1504]
24:
	mov r0, r8
	mov r1, #182
	str r4, [r0, #1408]
	str r5, [r0, #1412]
	str r6, [r0, #1416]
	str r7, [r0, #1420]
	str r8, [r0, #1424]
	str r9, [r0, #1428]
	str r10, [r0, #1432]
	str r11, [r0, #1436]
	str lr, [r0, #1440]
	mov r8, r0
	bl {vg_sm4_crypt8}
	mov r12, r8
	ldr r4, [r12, #1408]
	ldr r5, [r12, #1412]
	ldr r6, [r12, #1416]
	ldr r7, [r12, #1420]
	ldr r8, [r12, #1424]
	ldr r9, [r12, #1428]
	ldr r10, [r12, #1432]
	ldr r11, [r12, #1436]
	ldr lr, [r12, #1440]
	add r0, r8, #256
	mov r1, r11
219:
	ldr r9, [r6, #0]
	ldr r10, [r0, #0]
	eor r9, r9, r10
	str r9, [r6, #0]
	ldr r9, [r6, #4]
	ldr r10, [r0, #4]
	eor r9, r9, r10
	str r9, [r6, #4]
	ldr r9, [r6, #8]
	ldr r10, [r0, #8]
	eor r9, r9, r10
	str r9, [r6, #8]
	ldr r9, [r6, #12]
	ldr r10, [r0, #12]
	eor r9, r9, r10
	str r9, [r6, #12]
	add r0, r0, #16
	add r6, r6, #16
	subs r1, r1, #1
	bne 219b
	ldr r9, [r8, #256]
	str r9, [r8, #1492]
	ldr r9, [r8, #260]
	str r9, [r8, #1496]
	ldr r9, [r8, #264]
	str r9, [r8, #1500]
	ldr r9, [r8, #268]
	str r9, [r8, #1504]
	subs r7, r7, r11
	bne 22b
	b 21f
20:
21:
	ldr r9, [r8, #1492]
	str r9, [r5, #0]
	ldr r9, [r8, #1496]
	str r9, [r5, #4]
	ldr r9, [r8, #1500]
	str r9, [r5, #8]
	ldr r9, [r8, #1504]
	str r9, [r5, #12]
	mov r12, r8
	ldr r4, [r12, #1456]
	ldr r5, [r12, #1460]
	ldr r6, [r12, #1464]
	ldr r7, [r12, #1468]
	ldr r8, [r12, #1472]
	ldr r9, [r12, #1476]
	ldr r10, [r12, #1480]
	ldr r11, [r12, #1484]
	ldr lr, [r12, #1488]
	add sp, sp, #1520
	sub sp, sp, #1520
	add r12, sp, #0
	mov r2, #0
	mov r3, #47
220:
	str r2, [r12, #0]
	str r2, [r12, #4]
	str r2, [r12, #8]
	str r2, [r12, #12]
	str r2, [r12, #16]
	str r2, [r12, #20]
	str r2, [r12, #24]
	str r2, [r12, #28]
	add r12, r12, #32
	subs r3, r3, #1
	bne 220b
	str r2, [r12, #0]
	str r2, [r12, #4]
	str r2, [r12, #8]
	str r2, [r12, #12]
	add sp, sp, #1520
	mov r0, #0
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr

vg_sm4_ofb_final:
	sub sp, sp, #80
	add r12, sp, #0
	str lr, [r12, #4]
	add lr, sp, #8
	str lr, [r12, #0]
	ldr lr, [sp, #4]
	ldr r12, [sp, #0]
	str r4, [r12, #0]
	str r5, [r12, #4]
	str r6, [r12, #8]
	str r7, [r12, #12]
	str r9, [r12, #20]
	str r10, [r12, #24]
	str r11, [r12, #28]
	str lr, [r12, #32]
	str r8, [r12, #16]
	mov r4, r0
	mov r5, r1
	mov r6, r2
	mov r7, r3
	mov r8, r12
	ldr r9, [r5, #0]
	str r9, [r8, #40]
	ldr r9, [r5, #4]
	str r9, [r8, #44]
	ldr r9, [r5, #8]
	str r9, [r8, #48]
	ldr r9, [r5, #12]
	str r9, [r8, #52]
	cmp r7, #0
	beq 20f
22:
	mov r0, r4
	add r1, r8, #40
	mov r2, #1
	bl {vg_sm4_ecb_encrypt_core}
	lsr r9, r7, #4
	cmp r9, #0
	beq 23f
	ldr r9, [r6, #0]
	ldr r10, [r8, #40]
	eor r9, r9, r10
	str r9, [r6, #0]
	ldr r9, [r6, #4]
	ldr r10, [r8, #44]
	eor r9, r9, r10
	str r9, [r6, #4]
	ldr r9, [r6, #8]
	ldr r10, [r8, #48]
	eor r9, r9, r10
	str r9, [r6, #8]
	ldr r9, [r6, #12]
	ldr r10, [r8, #52]
	eor r9, r9, r10
	str r9, [r6, #12]
	add r6, r6, #16
	subs r7, r7, #16
	b 24f
23:
	add r0, r8, #40
25:
	ldrb r9, [r6, #0]
	ldrb r10, [r0, #0]
	eor r9, r9, r10
	strb r9, [r6, #0]
	add r0, r0, #1
	add r6, r6, #1
	subs r7, r7, #1
	bne 25b
24:
	bne 22b
	b 21f
20:
21:
	ldr r9, [r8, #40]
	str r9, [r5, #0]
	ldr r9, [r8, #44]
	str r9, [r5, #4]
	ldr r9, [r8, #48]
	str r9, [r5, #8]
	ldr r9, [r8, #52]
	str r9, [r5, #12]
	ldr r4, [r8, #0]
	ldr r5, [r8, #4]
	ldr r6, [r8, #8]
	ldr r7, [r8, #12]
	ldr r9, [r8, #20]
	ldr r10, [r8, #24]
	ldr r11, [r8, #28]
	ldr lr, [r8, #32]
	ldr r8, [r8, #16]
	add sp, sp, #80
	sub sp, sp, #1568
	add r12, sp, #0
	mov r2, #0
	mov r3, #49
26:
	str r2, [r12, #0]
	str r2, [r12, #4]
	str r2, [r12, #8]
	str r2, [r12, #12]
	str r2, [r12, #16]
	str r2, [r12, #20]
	str r2, [r12, #24]
	str r2, [r12, #28]
	add r12, r12, #32
	subs r3, r3, #1
	bne 26b
	add sp, sp, #1568
	mov r0, #0
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr
