// The functions of `src/sha512.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha384_init:
	movw r12, #40664
	movt r12, #49413
	str r12, [r0, #0]
	movw r12, #40285
	movt r12, #52155
	str r12, [r0, #4]
	movw r12, #54535
	movt r12, #13948
	str r12, [r0, #8]
	movw r12, #10538
	movt r12, #25242
	str r12, [r0, #12]
	movw r12, #56599
	movt r12, #12400
	str r12, [r0, #16]
	movw r12, #346
	movt r12, #37209
	str r12, [r0, #20]
	movw r12, #22841
	movt r12, #63246
	str r12, [r0, #24]
	movw r12, #60632
	movt r12, #5423
	str r12, [r0, #28]
	movw r12, #2865
	movt r12, #65472
	str r12, [r0, #32]
	movw r12, #9831
	movt r12, #26419
	str r12, [r0, #36]
	movw r12, #5393
	movt r12, #26712
	str r12, [r0, #40]
	movw r12, #19079
	movt r12, #36532
	str r12, [r0, #44]
	movw r12, #36775
	movt r12, #25849
	str r12, [r0, #48]
	movw r12, #11789
	movt r12, #56076
	str r12, [r0, #52]
	movw r12, #20388
	movt r12, #48890
	str r12, [r0, #56]
	movw r12, #18461
	movt r12, #18357
	str r12, [r0, #60]
	bx lr

vg_sha512_init:
	movw r12, #51464
	movt r12, #62396
	str r12, [r0, #0]
	movw r12, #58983
	movt r12, #27145
	str r12, [r0, #4]
	movw r12, #42811
	movt r12, #33994
	str r12, [r0, #8]
	movw r12, #44677
	movt r12, #47975
	str r12, [r0, #12]
	movw r12, #63531
	movt r12, #65172
	str r12, [r0, #16]
	movw r12, #62322
	movt r12, #15470
	str r12, [r0, #20]
	movw r12, #14065
	movt r12, #24349
	str r12, [r0, #24]
	movw r12, #62778
	movt r12, #42319
	str r12, [r0, #28]
	movw r12, #33489
	movt r12, #44518
	str r12, [r0, #32]
	movw r12, #21119
	movt r12, #20750
	str r12, [r0, #36]
	movw r12, #27679
	movt r12, #11070
	str r12, [r0, #40]
	movw r12, #26764
	movt r12, #39685
	str r12, [r0, #44]
	movw r12, #48491
	movt r12, #64321
	str r12, [r0, #48]
	movw r12, #55723
	movt r12, #8067
	str r12, [r0, #52]
	movw r12, #8569
	movt r12, #4990
	str r12, [r0, #56]
	movw r12, #52505
	movt r12, #23520
	str r12, [r0, #60]
	bx lr

vg_sha512_224_init:
	movw r12, #19874
	movt r12, #6484
	str r12, [r0, #0]
	movw r12, #14280
	movt r12, #35901
	str r12, [r0, #4]
	movw r12, #54486
	movt r12, #35292
	str r12, [r0, #8]
	movw r12, #39270
	movt r12, #29665
	str r12, [r0, #12]
	movw r12, #40066
	movt r12, #13055
	str r12, [r0, #16]
	movw r12, #47022
	movt r12, #7674
	str r12, [r0, #20]
	movw r12, #40911
	movt r12, #22575
	str r12, [r0, #24]
	movw r12, #54548
	movt r12, #26525
	str r12, [r0, #28]
	movw r12, #19880
	movt r12, #31700
	str r12, [r0, #32]
	movw r12, #11113
	movt r12, #3949
	str r12, [r0, #36]
	movw r12, #35138
	movt r12, #1220
	str r12, [r0, #40]
	movw r12, #28531
	movt r12, #30691
	str r12, [r0, #44]
	movw r12, #14024
	movt r12, #27165
	str r12, [r0, #48]
	movw r12, #34216
	movt r12, #16285
	str r12, [r0, #52]
	movw r12, #37537
	movt r12, #37334
	str r12, [r0, #56]
	movw r12, #59053
	movt r12, #4370
	str r12, [r0, #60]
	bx lr

vg_sha512_256_init:
	movw r12, #63276
	movt r12, #64555
	str r12, [r0, #0]
	movw r12, #8596
	movt r12, #8753
	str r12, [r0, #4]
	movw r12, #25794
	movt r12, #51276
	str r12, [r0, #8]
	movw r12, #24483
	movt r12, #40789
	str r12, [r0, #12]
	movw r12, #45393
	movt r12, #28499
	str r12, [r0, #16]
	movw r12, #47211
	movt r12, #9107
	str r12, [r0, #20]
	movw r12, #60093
	movt r12, #22848
	str r12, [r0, #24]
	movw r12, #30489
	movt r12, #38456
	str r12, [r0, #28]
	movw r12, #65507
	movt r12, #43150
	str r12, [r0, #32]
	movw r12, #16098
	movt r12, #38440
	str r12, [r0, #36]
	movw r12, #14738
	movt r12, #21382
	str r12, [r0, #40]
	movw r12, #7717
	movt r12, #48734
	str r12, [r0, #44]
	movw r12, #47274
	movt r12, #11397
	str r12, [r0, #48]
	movw r12, #39420
	movt r12, #11009
	str r12, [r0, #52]
	movw r12, #11426
	movt r12, #33221
	str r12, [r0, #56]
	movw r12, #11740
	movt r12, #3767
	str r12, [r0, #60]
	bx lr

vg_sha512_update:
	sub sp, sp, #1392
	add r12, sp, #0
	str lr, [r12, #12]
	ldr lr, [sp, #1392]
	str lr, [r12, #0]
	ldr lr, [sp, #1396]
	str lr, [r12, #4]
	add lr, sp, #16
	str lr, [r12, #8]
	ldr lr, [sp, #12]
	ldr r12, [sp, #8]
	str r4, [r12, #224]
	str r5, [r12, #228]
	str r6, [r12, #232]
	str r7, [r12, #236]
	str r8, [r12, #240]
	str r9, [r12, #244]
	str r10, [r12, #248]
	str r11, [r12, #252]
	str lr, [r12, #256]
	mov r3, r12
	and r4, r2, #127
	ldr r5, [sp, #0]
	ldr r6, [sp, #4]
	cmp r6, #0
	beq 20f
22:
	mov r7, #0
	cmp r4, #0
	beq 23f
	mov r8, #128
	sub r8, r8, r4
	lsr r12, r6, #7
	cmp r12, #0
	beq 25f
	b 26f
25:
	add r12, r6, r4
	lsr r12, r12, #7
	cmp r12, #0
	beq 27f
	b 28f
27:
	mov r8, r6
28:
26:
	sub r6, r6, r8
29:
	ldrb r12, [r5, #0]
	add r1, r0, r4
	strb r12, [r1, #64]
	add r5, r5, #1
	add r4, r4, #1
	subs r8, r8, #1
	bne 29b
	cmp r4, #128
	beq 210f
	b 211f
210:
	add r1, r0, #64
	mov r4, #0
	mov r7, #1
211:
	b 24f
23:
	lsr r12, r6, #7
	cmp r12, #0
	beq 212f
	mov r1, r5
	lsr r7, r6, #7
	lsl r12, r7, #7
	add r5, r5, r12
	sub r6, r6, r12
	b 213f
212:
	mov r8, #128
	sub r8, r8, r4
	lsr r12, r6, #7
	cmp r12, #0
	beq 214f
	b 215f
214:
	add r12, r6, r4
	lsr r12, r12, #7
	cmp r12, #0
	beq 216f
	b 217f
216:
	mov r8, r6
217:
215:
	sub r6, r6, r8
218:
	ldrb r12, [r5, #0]
	add r1, r0, r4
	strb r12, [r1, #64]
	add r5, r5, #1
	add r4, r4, #1
	subs r8, r8, #1
	bne 218b
	cmp r4, #128
	beq 219f
	b 220f
219:
	add r1, r0, #64
	mov r4, #0
	mov r7, #1
220:
213:
24:
	cmp r7, #0
	beq 221f
	mov r2, r7
	bl {vg_sha512_compress}
	b 222f
221:
222:
	cmp r6, #0
	bne 22b
	b 21f
20:
21:
	ldr r4, [r3, #224]
	ldr r5, [r3, #228]
	ldr r6, [r3, #232]
	ldr r7, [r3, #236]
	ldr r8, [r3, #240]
	ldr r9, [r3, #244]
	ldr r10, [r3, #248]
	ldr r11, [r3, #252]
	ldr lr, [r3, #256]
	add sp, sp, #1392
	bx lr

vg_sha512_finalize:
	sub sp, sp, #1392
	add r12, sp, #0
	str lr, [r12, #8]
	ldr lr, [sp, #1392]
	str lr, [r12, #0]
	add lr, sp, #12
	str lr, [r12, #4]
	ldr lr, [sp, #8]
	ldr r12, [sp, #4]
	str r4, [r12, #224]
	str r5, [r12, #228]
	str r6, [r12, #232]
	str r7, [r12, #236]
	str r8, [r12, #240]
	str r9, [r12, #244]
	str r10, [r12, #248]
	str r11, [r12, #252]
	str lr, [r12, #256]
	mov r4, r2
	mov r5, r3
	mov r3, r12
	ldr r6, [sp, #0]
	and r7, r4, #127
	mov r12, #128
	add r1, r0, r7
	strb r12, [r1, #64]
	add r7, r7, #1
	add r8, r7, #15
	lsr r8, r8, #7
20:
	mov r9, #128
	cmp r8, #0
	beq 21f
	b 22f
21:
	mov r9, #112
22:
	mov r12, #0
	subs r9, r9, r7
	beq 23f
25:
	add r1, r0, r7
	strb r12, [r1, #64]
	add r7, r7, #1
	subs r9, r9, #1
	bne 25b
	b 24f
23:
24:
	cmp r8, #0
	beq 26f
	b 27f
26:
	mov r9, #0
	str r9, [r0, #176]
	lsr r9, r5, #29
	rev r9, r9
	str r9, [r0, #180]
	lsl r9, r5, #3
	orr r9, r9, r4, lsr #29
	rev r9, r9
	str r9, [r0, #184]
	lsl r9, r4, #3
	rev r9, r9
	str r9, [r0, #188]
27:
	add r1, r0, #64
	mov r2, #1
	bl {vg_sha512_compress}
	mov r7, #0
	subs r8, r8, #1
	beq 20b
	ldr r9, [r0, #0]
	ldr r10, [r0, #4]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #0]
	str r9, [r6, #4]
	ldr r9, [r0, #8]
	ldr r10, [r0, #12]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #8]
	str r9, [r6, #12]
	ldr r9, [r0, #16]
	ldr r10, [r0, #20]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #16]
	str r9, [r6, #20]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #24]
	str r9, [r6, #28]
	ldr r9, [r0, #32]
	ldr r10, [r0, #36]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #32]
	str r9, [r6, #36]
	ldr r9, [r0, #40]
	ldr r10, [r0, #44]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #40]
	str r9, [r6, #44]
	ldr r9, [r0, #48]
	ldr r10, [r0, #52]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #48]
	str r9, [r6, #52]
	ldr r9, [r0, #56]
	ldr r10, [r0, #60]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #56]
	str r9, [r6, #60]
	ldr r4, [r3, #224]
	ldr r5, [r3, #228]
	ldr r6, [r3, #232]
	ldr r7, [r3, #236]
	ldr r8, [r3, #240]
	ldr r9, [r3, #244]
	ldr r10, [r3, #248]
	ldr r11, [r3, #252]
	ldr lr, [r3, #256]
	add sp, sp, #1392
	bx lr

vg_sha384_finalize:
	sub sp, sp, #1392
	add r12, sp, #0
	str lr, [r12, #8]
	ldr lr, [sp, #1392]
	str lr, [r12, #0]
	add lr, sp, #12
	str lr, [r12, #4]
	ldr lr, [sp, #8]
	ldr r12, [sp, #4]
	str r4, [r12, #224]
	str r5, [r12, #228]
	str r6, [r12, #232]
	str r7, [r12, #236]
	str r8, [r12, #240]
	str r9, [r12, #244]
	str r10, [r12, #248]
	str r11, [r12, #252]
	str lr, [r12, #256]
	mov r4, r2
	mov r5, r3
	mov r3, r12
	ldr r6, [sp, #0]
	and r7, r4, #127
	mov r12, #128
	add r1, r0, r7
	strb r12, [r1, #64]
	add r7, r7, #1
	add r8, r7, #15
	lsr r8, r8, #7
20:
	mov r9, #128
	cmp r8, #0
	beq 21f
	b 22f
21:
	mov r9, #112
22:
	mov r12, #0
	subs r9, r9, r7
	beq 23f
25:
	add r1, r0, r7
	strb r12, [r1, #64]
	add r7, r7, #1
	subs r9, r9, #1
	bne 25b
	b 24f
23:
24:
	cmp r8, #0
	beq 26f
	b 27f
26:
	mov r9, #0
	str r9, [r0, #176]
	lsr r9, r5, #29
	rev r9, r9
	str r9, [r0, #180]
	lsl r9, r5, #3
	orr r9, r9, r4, lsr #29
	rev r9, r9
	str r9, [r0, #184]
	lsl r9, r4, #3
	rev r9, r9
	str r9, [r0, #188]
27:
	add r1, r0, #64
	mov r2, #1
	bl {vg_sha512_compress}
	mov r7, #0
	subs r8, r8, #1
	beq 20b
	ldr r9, [r0, #0]
	ldr r10, [r0, #4]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #0]
	str r9, [r6, #4]
	ldr r9, [r0, #8]
	ldr r10, [r0, #12]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #8]
	str r9, [r6, #12]
	ldr r9, [r0, #16]
	ldr r10, [r0, #20]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #16]
	str r9, [r6, #20]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #24]
	str r9, [r6, #28]
	ldr r9, [r0, #32]
	ldr r10, [r0, #36]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #32]
	str r9, [r6, #36]
	ldr r9, [r0, #40]
	ldr r10, [r0, #44]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #40]
	str r9, [r6, #44]
	ldr r4, [r3, #224]
	ldr r5, [r3, #228]
	ldr r6, [r3, #232]
	ldr r7, [r3, #236]
	ldr r8, [r3, #240]
	ldr r9, [r3, #244]
	ldr r10, [r3, #248]
	ldr r11, [r3, #252]
	ldr lr, [r3, #256]
	add sp, sp, #1392
	bx lr

vg_sha512_256_finalize:
	sub sp, sp, #1392
	add r12, sp, #0
	str lr, [r12, #8]
	ldr lr, [sp, #1392]
	str lr, [r12, #0]
	add lr, sp, #12
	str lr, [r12, #4]
	ldr lr, [sp, #8]
	ldr r12, [sp, #4]
	str r4, [r12, #224]
	str r5, [r12, #228]
	str r6, [r12, #232]
	str r7, [r12, #236]
	str r8, [r12, #240]
	str r9, [r12, #244]
	str r10, [r12, #248]
	str r11, [r12, #252]
	str lr, [r12, #256]
	mov r4, r2
	mov r5, r3
	mov r3, r12
	ldr r6, [sp, #0]
	and r7, r4, #127
	mov r12, #128
	add r1, r0, r7
	strb r12, [r1, #64]
	add r7, r7, #1
	add r8, r7, #15
	lsr r8, r8, #7
20:
	mov r9, #128
	cmp r8, #0
	beq 21f
	b 22f
21:
	mov r9, #112
22:
	mov r12, #0
	subs r9, r9, r7
	beq 23f
25:
	add r1, r0, r7
	strb r12, [r1, #64]
	add r7, r7, #1
	subs r9, r9, #1
	bne 25b
	b 24f
23:
24:
	cmp r8, #0
	beq 26f
	b 27f
26:
	mov r9, #0
	str r9, [r0, #176]
	lsr r9, r5, #29
	rev r9, r9
	str r9, [r0, #180]
	lsl r9, r5, #3
	orr r9, r9, r4, lsr #29
	rev r9, r9
	str r9, [r0, #184]
	lsl r9, r4, #3
	rev r9, r9
	str r9, [r0, #188]
27:
	add r1, r0, #64
	mov r2, #1
	bl {vg_sha512_compress}
	mov r7, #0
	subs r8, r8, #1
	beq 20b
	ldr r9, [r0, #0]
	ldr r10, [r0, #4]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #0]
	str r9, [r6, #4]
	ldr r9, [r0, #8]
	ldr r10, [r0, #12]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #8]
	str r9, [r6, #12]
	ldr r9, [r0, #16]
	ldr r10, [r0, #20]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #16]
	str r9, [r6, #20]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #24]
	str r9, [r6, #28]
	ldr r4, [r3, #224]
	ldr r5, [r3, #228]
	ldr r6, [r3, #232]
	ldr r7, [r3, #236]
	ldr r8, [r3, #240]
	ldr r9, [r3, #244]
	ldr r10, [r3, #248]
	ldr r11, [r3, #252]
	ldr lr, [r3, #256]
	add sp, sp, #1392
	bx lr

vg_sha512_224_finalize:
	sub sp, sp, #1392
	add r12, sp, #0
	str lr, [r12, #8]
	ldr lr, [sp, #1392]
	str lr, [r12, #0]
	add lr, sp, #12
	str lr, [r12, #4]
	ldr lr, [sp, #8]
	ldr r12, [sp, #4]
	str r4, [r12, #224]
	str r5, [r12, #228]
	str r6, [r12, #232]
	str r7, [r12, #236]
	str r8, [r12, #240]
	str r9, [r12, #244]
	str r10, [r12, #248]
	str r11, [r12, #252]
	str lr, [r12, #256]
	mov r4, r2
	mov r5, r3
	mov r3, r12
	ldr r6, [sp, #0]
	and r7, r4, #127
	mov r12, #128
	add r1, r0, r7
	strb r12, [r1, #64]
	add r7, r7, #1
	add r8, r7, #15
	lsr r8, r8, #7
20:
	mov r9, #128
	cmp r8, #0
	beq 21f
	b 22f
21:
	mov r9, #112
22:
	mov r12, #0
	subs r9, r9, r7
	beq 23f
25:
	add r1, r0, r7
	strb r12, [r1, #64]
	add r7, r7, #1
	subs r9, r9, #1
	bne 25b
	b 24f
23:
24:
	cmp r8, #0
	beq 26f
	b 27f
26:
	mov r9, #0
	str r9, [r0, #176]
	lsr r9, r5, #29
	rev r9, r9
	str r9, [r0, #180]
	lsl r9, r5, #3
	orr r9, r9, r4, lsr #29
	rev r9, r9
	str r9, [r0, #184]
	lsl r9, r4, #3
	rev r9, r9
	str r9, [r0, #188]
27:
	add r1, r0, #64
	mov r2, #1
	bl {vg_sha512_compress}
	mov r7, #0
	subs r8, r8, #1
	beq 20b
	ldr r9, [r0, #0]
	ldr r10, [r0, #4]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #0]
	str r9, [r6, #4]
	ldr r9, [r0, #8]
	ldr r10, [r0, #12]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #8]
	str r9, [r6, #12]
	ldr r9, [r0, #16]
	ldr r10, [r0, #20]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #16]
	str r9, [r6, #20]
	ldr r10, [r0, #28]
	rev r10, r10
	str r10, [r6, #24]
	ldr r4, [r3, #224]
	ldr r5, [r3, #228]
	ldr r6, [r3, #232]
	ldr r7, [r3, #236]
	ldr r8, [r3, #240]
	ldr r9, [r3, #244]
	ldr r10, [r3, #248]
	ldr r11, [r3, #252]
	ldr lr, [r3, #256]
	add sp, sp, #1392
	bx lr
