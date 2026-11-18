// The functions of `src/internal/vg_rc2_expand_key.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rc2_expand_key:
	ldr r12, [sp, #0]
	str r8, [r12, #0]
	str r4, [r12, #4]
	str r5, [r12, #8]
	str r6, [r12, #12]
	str r7, [r12, #16]
	str r9, [r12, #20]
	str r10, [r12, #24]
	str r11, [r12, #28]
	str lr, [r12, #32]
	mov r8, r12
	mov r4, r0
	mov r5, r1
	mov r6, r3
	mov r7, r2
	movw r0, #0
20:
	add lr, r4, r0
	ldrb r12, [lr, #0]
	add lr, r6, r0
	strb r12, [lr, #0]
	add r0, r0, #1
	cmp r0, r5
	bne 20b
	cmp r0, #128
	bne 21f
	b 22f
21:
23:
	add lr, r6, r0
	sub lr, lr, #1
	ldrb r12, [lr, #0]
	sub r9, r0, r5
	add lr, r6, r9
	ldrb r3, [lr, #0]
	add r12, r12, r3
	lsl r12, r12, #24
	lsr r12, r12, #24
	movw lr, #:lower16:({VG_RC2_PITABLE}
	movt lr, #:upper16:({VG_RC2_PITABLE}
2:
	add lr, pc
3:
	movw r9, #0
	movw r10, #0
	eor r3, r12, #0
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #0]
	mla r9, r11, r3, r9
	ldr r11, [lr, #4]
	mla r10, r11, r3, r10
	eor r3, r12, #8
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #8]
	mla r9, r11, r3, r9
	ldr r11, [lr, #12]
	mla r10, r11, r3, r10
	eor r3, r12, #16
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #16]
	mla r9, r11, r3, r9
	ldr r11, [lr, #20]
	mla r10, r11, r3, r10
	eor r3, r12, #24
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #24]
	mla r9, r11, r3, r9
	ldr r11, [lr, #28]
	mla r10, r11, r3, r10
	eor r3, r12, #32
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #32]
	mla r9, r11, r3, r9
	ldr r11, [lr, #36]
	mla r10, r11, r3, r10
	eor r3, r12, #40
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #40]
	mla r9, r11, r3, r9
	ldr r11, [lr, #44]
	mla r10, r11, r3, r10
	eor r3, r12, #48
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #48]
	mla r9, r11, r3, r9
	ldr r11, [lr, #52]
	mla r10, r11, r3, r10
	eor r3, r12, #56
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #56]
	mla r9, r11, r3, r9
	ldr r11, [lr, #60]
	mla r10, r11, r3, r10
	eor r3, r12, #64
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #64]
	mla r9, r11, r3, r9
	ldr r11, [lr, #68]
	mla r10, r11, r3, r10
	eor r3, r12, #72
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #72]
	mla r9, r11, r3, r9
	ldr r11, [lr, #76]
	mla r10, r11, r3, r10
	eor r3, r12, #80
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #80]
	mla r9, r11, r3, r9
	ldr r11, [lr, #84]
	mla r10, r11, r3, r10
	eor r3, r12, #88
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #88]
	mla r9, r11, r3, r9
	ldr r11, [lr, #92]
	mla r10, r11, r3, r10
	eor r3, r12, #96
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #96]
	mla r9, r11, r3, r9
	ldr r11, [lr, #100]
	mla r10, r11, r3, r10
	eor r3, r12, #104
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #104]
	mla r9, r11, r3, r9
	ldr r11, [lr, #108]
	mla r10, r11, r3, r10
	eor r3, r12, #112
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #112]
	mla r9, r11, r3, r9
	ldr r11, [lr, #116]
	mla r10, r11, r3, r10
	eor r3, r12, #120
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #120]
	mla r9, r11, r3, r9
	ldr r11, [lr, #124]
	mla r10, r11, r3, r10
	eor r3, r12, #128
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #128]
	mla r9, r11, r3, r9
	ldr r11, [lr, #132]
	mla r10, r11, r3, r10
	eor r3, r12, #136
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #136]
	mla r9, r11, r3, r9
	ldr r11, [lr, #140]
	mla r10, r11, r3, r10
	eor r3, r12, #144
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #144]
	mla r9, r11, r3, r9
	ldr r11, [lr, #148]
	mla r10, r11, r3, r10
	eor r3, r12, #152
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #152]
	mla r9, r11, r3, r9
	ldr r11, [lr, #156]
	mla r10, r11, r3, r10
	eor r3, r12, #160
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #160]
	mla r9, r11, r3, r9
	ldr r11, [lr, #164]
	mla r10, r11, r3, r10
	eor r3, r12, #168
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #168]
	mla r9, r11, r3, r9
	ldr r11, [lr, #172]
	mla r10, r11, r3, r10
	eor r3, r12, #176
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #176]
	mla r9, r11, r3, r9
	ldr r11, [lr, #180]
	mla r10, r11, r3, r10
	eor r3, r12, #184
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #184]
	mla r9, r11, r3, r9
	ldr r11, [lr, #188]
	mla r10, r11, r3, r10
	eor r3, r12, #192
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #192]
	mla r9, r11, r3, r9
	ldr r11, [lr, #196]
	mla r10, r11, r3, r10
	eor r3, r12, #200
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #200]
	mla r9, r11, r3, r9
	ldr r11, [lr, #204]
	mla r10, r11, r3, r10
	eor r3, r12, #208
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #208]
	mla r9, r11, r3, r9
	ldr r11, [lr, #212]
	mla r10, r11, r3, r10
	eor r3, r12, #216
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #216]
	mla r9, r11, r3, r9
	ldr r11, [lr, #220]
	mla r10, r11, r3, r10
	eor r3, r12, #224
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #224]
	mla r9, r11, r3, r9
	ldr r11, [lr, #228]
	mla r10, r11, r3, r10
	eor r3, r12, #232
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #232]
	mla r9, r11, r3, r9
	ldr r11, [lr, #236]
	mla r10, r11, r3, r10
	eor r3, r12, #240
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #240]
	mla r9, r11, r3, r9
	ldr r11, [lr, #244]
	mla r10, r11, r3, r10
	eor r3, r12, #248
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #248]
	mla r9, r11, r3, r9
	ldr r11, [lr, #252]
	mla r10, r11, r3, r10
	lsl r3, r12, #29
	lsr r3, r3, #31
	sub r10, r10, r9
	mla r9, r10, r3, r9
	and r3, r12, #1
	lsr r10, r9, #8
	sub r10, r10, r9
	mla r9, r10, r3, r9
	lsl r3, r12, #30
	lsr r3, r3, #31
	lsr r10, r9, #16
	sub r10, r10, r9
	mla r9, r10, r3, r9
	and r12, r9, #255
	add lr, r6, r0
	strb r12, [lr, #0]
	add r0, r0, #1
	cmp r0, #128
	bne 23b
22:
	add r1, r7, #7
	lsr r1, r1, #3
	movw r0, #128
	sub r0, r0, r1
	mov r9, r7
	lsl r9, r9, #29
	lsr r9, r9, #29
	movw r2, #255
	cmp r9, #1
	beq 24f
	b 25f
24:
	movw r2, #1
25:
	cmp r9, #2
	beq 26f
	b 27f
26:
	movw r2, #3
27:
	cmp r9, #3
	beq 28f
	b 29f
28:
	movw r2, #7
29:
	cmp r9, #4
	beq 210f
	b 211f
210:
	movw r2, #15
211:
	cmp r9, #5
	beq 212f
	b 213f
212:
	movw r2, #31
213:
	cmp r9, #6
	beq 214f
	b 215f
214:
	movw r2, #63
215:
	cmp r9, #7
	beq 216f
	b 217f
216:
	movw r2, #127
217:
	add lr, r6, r0
	ldrb r12, [lr, #0]
	and r12, r12, r2
	lsl r12, r12, #24
	lsr r12, r12, #24
	movw lr, #:lower16:({VG_RC2_PITABLE}
	movt lr, #:upper16:({VG_RC2_PITABLE}
2:
	add lr, pc
3:
	movw r9, #0
	movw r10, #0
	eor r3, r12, #0
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #0]
	mla r9, r11, r3, r9
	ldr r11, [lr, #4]
	mla r10, r11, r3, r10
	eor r3, r12, #8
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #8]
	mla r9, r11, r3, r9
	ldr r11, [lr, #12]
	mla r10, r11, r3, r10
	eor r3, r12, #16
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #16]
	mla r9, r11, r3, r9
	ldr r11, [lr, #20]
	mla r10, r11, r3, r10
	eor r3, r12, #24
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #24]
	mla r9, r11, r3, r9
	ldr r11, [lr, #28]
	mla r10, r11, r3, r10
	eor r3, r12, #32
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #32]
	mla r9, r11, r3, r9
	ldr r11, [lr, #36]
	mla r10, r11, r3, r10
	eor r3, r12, #40
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #40]
	mla r9, r11, r3, r9
	ldr r11, [lr, #44]
	mla r10, r11, r3, r10
	eor r3, r12, #48
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #48]
	mla r9, r11, r3, r9
	ldr r11, [lr, #52]
	mla r10, r11, r3, r10
	eor r3, r12, #56
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #56]
	mla r9, r11, r3, r9
	ldr r11, [lr, #60]
	mla r10, r11, r3, r10
	eor r3, r12, #64
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #64]
	mla r9, r11, r3, r9
	ldr r11, [lr, #68]
	mla r10, r11, r3, r10
	eor r3, r12, #72
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #72]
	mla r9, r11, r3, r9
	ldr r11, [lr, #76]
	mla r10, r11, r3, r10
	eor r3, r12, #80
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #80]
	mla r9, r11, r3, r9
	ldr r11, [lr, #84]
	mla r10, r11, r3, r10
	eor r3, r12, #88
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #88]
	mla r9, r11, r3, r9
	ldr r11, [lr, #92]
	mla r10, r11, r3, r10
	eor r3, r12, #96
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #96]
	mla r9, r11, r3, r9
	ldr r11, [lr, #100]
	mla r10, r11, r3, r10
	eor r3, r12, #104
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #104]
	mla r9, r11, r3, r9
	ldr r11, [lr, #108]
	mla r10, r11, r3, r10
	eor r3, r12, #112
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #112]
	mla r9, r11, r3, r9
	ldr r11, [lr, #116]
	mla r10, r11, r3, r10
	eor r3, r12, #120
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #120]
	mla r9, r11, r3, r9
	ldr r11, [lr, #124]
	mla r10, r11, r3, r10
	eor r3, r12, #128
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #128]
	mla r9, r11, r3, r9
	ldr r11, [lr, #132]
	mla r10, r11, r3, r10
	eor r3, r12, #136
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #136]
	mla r9, r11, r3, r9
	ldr r11, [lr, #140]
	mla r10, r11, r3, r10
	eor r3, r12, #144
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #144]
	mla r9, r11, r3, r9
	ldr r11, [lr, #148]
	mla r10, r11, r3, r10
	eor r3, r12, #152
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #152]
	mla r9, r11, r3, r9
	ldr r11, [lr, #156]
	mla r10, r11, r3, r10
	eor r3, r12, #160
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #160]
	mla r9, r11, r3, r9
	ldr r11, [lr, #164]
	mla r10, r11, r3, r10
	eor r3, r12, #168
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #168]
	mla r9, r11, r3, r9
	ldr r11, [lr, #172]
	mla r10, r11, r3, r10
	eor r3, r12, #176
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #176]
	mla r9, r11, r3, r9
	ldr r11, [lr, #180]
	mla r10, r11, r3, r10
	eor r3, r12, #184
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #184]
	mla r9, r11, r3, r9
	ldr r11, [lr, #188]
	mla r10, r11, r3, r10
	eor r3, r12, #192
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #192]
	mla r9, r11, r3, r9
	ldr r11, [lr, #196]
	mla r10, r11, r3, r10
	eor r3, r12, #200
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #200]
	mla r9, r11, r3, r9
	ldr r11, [lr, #204]
	mla r10, r11, r3, r10
	eor r3, r12, #208
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #208]
	mla r9, r11, r3, r9
	ldr r11, [lr, #212]
	mla r10, r11, r3, r10
	eor r3, r12, #216
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #216]
	mla r9, r11, r3, r9
	ldr r11, [lr, #220]
	mla r10, r11, r3, r10
	eor r3, r12, #224
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #224]
	mla r9, r11, r3, r9
	ldr r11, [lr, #228]
	mla r10, r11, r3, r10
	eor r3, r12, #232
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #232]
	mla r9, r11, r3, r9
	ldr r11, [lr, #236]
	mla r10, r11, r3, r10
	eor r3, r12, #240
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #240]
	mla r9, r11, r3, r9
	ldr r11, [lr, #244]
	mla r10, r11, r3, r10
	eor r3, r12, #248
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #248]
	mla r9, r11, r3, r9
	ldr r11, [lr, #252]
	mla r10, r11, r3, r10
	lsl r3, r12, #29
	lsr r3, r3, #31
	sub r10, r10, r9
	mla r9, r10, r3, r9
	and r3, r12, #1
	lsr r10, r9, #8
	sub r10, r10, r9
	mla r9, r10, r3, r9
	lsl r3, r12, #30
	lsr r3, r3, #31
	lsr r10, r9, #16
	sub r10, r10, r9
	mla r9, r10, r3, r9
	and r12, r9, #255
	add lr, r6, r0
	strb r12, [lr, #0]
	cmp r0, #0
	bne 218f
	b 219f
218:
220:
	sub r0, r0, #1
	add lr, r6, r0
	add lr, lr, #1
	ldrb r12, [lr, #0]
	add r9, r0, r1
	add lr, r6, r9
	ldrb r3, [lr, #0]
	eor r12, r12, r3
	lsl r12, r12, #24
	lsr r12, r12, #24
	movw lr, #:lower16:({VG_RC2_PITABLE}
	movt lr, #:upper16:({VG_RC2_PITABLE}
2:
	add lr, pc
3:
	movw r9, #0
	movw r10, #0
	eor r3, r12, #0
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #0]
	mla r9, r11, r3, r9
	ldr r11, [lr, #4]
	mla r10, r11, r3, r10
	eor r3, r12, #8
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #8]
	mla r9, r11, r3, r9
	ldr r11, [lr, #12]
	mla r10, r11, r3, r10
	eor r3, r12, #16
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #16]
	mla r9, r11, r3, r9
	ldr r11, [lr, #20]
	mla r10, r11, r3, r10
	eor r3, r12, #24
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #24]
	mla r9, r11, r3, r9
	ldr r11, [lr, #28]
	mla r10, r11, r3, r10
	eor r3, r12, #32
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #32]
	mla r9, r11, r3, r9
	ldr r11, [lr, #36]
	mla r10, r11, r3, r10
	eor r3, r12, #40
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #40]
	mla r9, r11, r3, r9
	ldr r11, [lr, #44]
	mla r10, r11, r3, r10
	eor r3, r12, #48
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #48]
	mla r9, r11, r3, r9
	ldr r11, [lr, #52]
	mla r10, r11, r3, r10
	eor r3, r12, #56
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #56]
	mla r9, r11, r3, r9
	ldr r11, [lr, #60]
	mla r10, r11, r3, r10
	eor r3, r12, #64
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #64]
	mla r9, r11, r3, r9
	ldr r11, [lr, #68]
	mla r10, r11, r3, r10
	eor r3, r12, #72
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #72]
	mla r9, r11, r3, r9
	ldr r11, [lr, #76]
	mla r10, r11, r3, r10
	eor r3, r12, #80
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #80]
	mla r9, r11, r3, r9
	ldr r11, [lr, #84]
	mla r10, r11, r3, r10
	eor r3, r12, #88
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #88]
	mla r9, r11, r3, r9
	ldr r11, [lr, #92]
	mla r10, r11, r3, r10
	eor r3, r12, #96
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #96]
	mla r9, r11, r3, r9
	ldr r11, [lr, #100]
	mla r10, r11, r3, r10
	eor r3, r12, #104
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #104]
	mla r9, r11, r3, r9
	ldr r11, [lr, #108]
	mla r10, r11, r3, r10
	eor r3, r12, #112
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #112]
	mla r9, r11, r3, r9
	ldr r11, [lr, #116]
	mla r10, r11, r3, r10
	eor r3, r12, #120
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #120]
	mla r9, r11, r3, r9
	ldr r11, [lr, #124]
	mla r10, r11, r3, r10
	eor r3, r12, #128
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #128]
	mla r9, r11, r3, r9
	ldr r11, [lr, #132]
	mla r10, r11, r3, r10
	eor r3, r12, #136
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #136]
	mla r9, r11, r3, r9
	ldr r11, [lr, #140]
	mla r10, r11, r3, r10
	eor r3, r12, #144
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #144]
	mla r9, r11, r3, r9
	ldr r11, [lr, #148]
	mla r10, r11, r3, r10
	eor r3, r12, #152
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #152]
	mla r9, r11, r3, r9
	ldr r11, [lr, #156]
	mla r10, r11, r3, r10
	eor r3, r12, #160
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #160]
	mla r9, r11, r3, r9
	ldr r11, [lr, #164]
	mla r10, r11, r3, r10
	eor r3, r12, #168
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #168]
	mla r9, r11, r3, r9
	ldr r11, [lr, #172]
	mla r10, r11, r3, r10
	eor r3, r12, #176
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #176]
	mla r9, r11, r3, r9
	ldr r11, [lr, #180]
	mla r10, r11, r3, r10
	eor r3, r12, #184
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #184]
	mla r9, r11, r3, r9
	ldr r11, [lr, #188]
	mla r10, r11, r3, r10
	eor r3, r12, #192
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #192]
	mla r9, r11, r3, r9
	ldr r11, [lr, #196]
	mla r10, r11, r3, r10
	eor r3, r12, #200
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #200]
	mla r9, r11, r3, r9
	ldr r11, [lr, #204]
	mla r10, r11, r3, r10
	eor r3, r12, #208
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #208]
	mla r9, r11, r3, r9
	ldr r11, [lr, #212]
	mla r10, r11, r3, r10
	eor r3, r12, #216
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #216]
	mla r9, r11, r3, r9
	ldr r11, [lr, #220]
	mla r10, r11, r3, r10
	eor r3, r12, #224
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #224]
	mla r9, r11, r3, r9
	ldr r11, [lr, #228]
	mla r10, r11, r3, r10
	eor r3, r12, #232
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #232]
	mla r9, r11, r3, r9
	ldr r11, [lr, #236]
	mla r10, r11, r3, r10
	eor r3, r12, #240
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #240]
	mla r9, r11, r3, r9
	ldr r11, [lr, #244]
	mla r10, r11, r3, r10
	eor r3, r12, #248
	sub r3, r3, #8
	lsr r3, r3, #31
	ldr r11, [lr, #248]
	mla r9, r11, r3, r9
	ldr r11, [lr, #252]
	mla r10, r11, r3, r10
	lsl r3, r12, #29
	lsr r3, r3, #31
	sub r10, r10, r9
	mla r9, r10, r3, r9
	and r3, r12, #1
	lsr r10, r9, #8
	sub r10, r10, r9
	mla r9, r10, r3, r9
	lsl r3, r12, #30
	lsr r3, r3, #31
	lsr r10, r9, #16
	sub r10, r10, r9
	mla r9, r10, r3, r9
	and r12, r9, #255
	add lr, r6, r0
	strb r12, [lr, #0]
	cmp r0, #0
	bne 220b
219:
	mov r12, r8
	ldr r8, [r12, #0]
	ldr r4, [r12, #4]
	ldr r5, [r12, #8]
	ldr r6, [r12, #12]
	ldr r7, [r12, #16]
	ldr r9, [r12, #20]
	ldr r10, [r12, #24]
	ldr r11, [r12, #28]
	ldr lr, [r12, #32]
	bx lr
