// The functions of `src/chacha20poly1305.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chacha20_poly1305_seal_umaal:
	sub sp, sp, #656
	add r12, sp, #0
	str lr, [r12, #16]
	ldr lr, [sp, #656]
	str lr, [r12, #0]
	ldr lr, [sp, #660]
	str lr, [r12, #4]
	ldr lr, [sp, #664]
	str lr, [r12, #8]
	add lr, sp, #20
	str lr, [r12, #12]
	ldr lr, [sp, #16]
	ldr r12, [sp, #12]
	str r4, [r12, #464]
	str r5, [r12, #468]
	str r6, [r12, #472]
	str r7, [r12, #476]
	str r8, [r12, #480]
	str r9, [r12, #484]
	str r10, [r12, #488]
	str r11, [r12, #492]
	str lr, [r12, #496]
	mov r7, r12
	mov r8, r2
	mov r9, r3
	ldr r10, [sp, #0]
	ldr r11, [sp, #4]
	ldr r4, [sp, #8]
	mov r6, r10
	movw r12, #30821
	movt r12, #24944
	str r12, [r7, #320]
	movw r12, #25710
	movt r12, #13088
	str r12, [r7, #324]
	movw r12, #11570
	movt r12, #31074
	str r12, [r7, #328]
	movw r12, #25972
	movt r12, #27424
	str r12, [r7, #332]
	ldr r12, [r0, #0]
	str r12, [r7, #336]
	ldr r12, [r0, #4]
	str r12, [r7, #340]
	ldr r12, [r0, #8]
	str r12, [r7, #344]
	ldr r12, [r0, #12]
	str r12, [r7, #348]
	ldr r12, [r0, #16]
	str r12, [r7, #352]
	ldr r12, [r0, #20]
	str r12, [r7, #356]
	ldr r12, [r0, #24]
	str r12, [r7, #360]
	ldr r12, [r0, #28]
	str r12, [r7, #364]
	mov r12, #0
	str r12, [r7, #368]
	ldr r12, [r1, #0]
	str r12, [r7, #372]
	ldr r12, [r1, #4]
	str r12, [r7, #376]
	ldr r12, [r1, #8]
	str r12, [r7, #380]
	add r0, r7, #320
	mov r1, r7
	bl {vg_chacha20_block}
	mov r7, r1
	ldr r12, [r7, #0]
	str r12, [r7, #384]
	ldr r12, [r7, #4]
	str r12, [r7, #388]
	ldr r12, [r7, #8]
	str r12, [r7, #392]
	ldr r12, [r7, #12]
	str r12, [r7, #396]
	ldr r12, [r7, #16]
	str r12, [r7, #400]
	ldr r12, [r7, #20]
	str r12, [r7, #404]
	ldr r12, [r7, #24]
	str r12, [r7, #408]
	ldr r12, [r7, #28]
	str r12, [r7, #412]
	mov r12, #1
	str r12, [r7, #368]
	add r0, r7, #320
	mov r1, r10
	mov r2, r11
	mov r3, r7
	mov r5, r6
	bl {vg_chacha20_xor}
	mov r7, r1
	mov r0, r7
	add r1, r7, #384
	bl {vg_poly1305_init_core}
	mov r7, r0
	mov r1, r8
	lsr r2, r9, #4
	mov r0, r7
	bl {vg_poly1305_blocks_umaal}
	mov r7, r0
	and r3, r9, #15
	cmp r3, #0
	beq 20f
	sub r1, r9, r3
	add r1, r8, r1
	mov r12, #0
	str r12, [r7, #416]
	str r12, [r7, #420]
	str r12, [r7, #424]
	str r12, [r7, #428]
	add r2, r7, #416
22:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 22b
	add r1, r7, #416
	mov r2, #1
	mov r0, r7
	bl {vg_poly1305_blocks_umaal}
	mov r7, r0
	b 21f
20:
21:
	mov r1, r10
	lsr r2, r11, #4
	mov r0, r7
	bl {vg_poly1305_blocks_umaal}
	mov r7, r0
	and r3, r11, #15
	cmp r3, #0
	beq 23f
	sub r1, r11, r3
	add r1, r10, r1
	mov r12, #0
	str r12, [r7, #416]
	str r12, [r7, #420]
	str r12, [r7, #424]
	str r12, [r7, #428]
	add r2, r7, #416
25:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 25b
	add r1, r7, #416
	mov r2, #1
	mov r0, r7
	bl {vg_poly1305_blocks_umaal}
	mov r7, r0
	b 24f
23:
24:
	str r9, [r7, #432]
	mov r12, #0
	str r12, [r7, #436]
	str r11, [r7, #440]
	str r12, [r7, #444]
	add r1, r7, #432
	mov r2, #1
	mov r0, r7
	bl {vg_poly1305_blocks_umaal}
	mov r7, r0
	lsr r2, r9, #4
	and r3, r9, #15
	add r3, r3, #15
	add r2, r2, r3, lsr #4
	lsr r0, r11, #4
	and r1, r11, #15
	add r1, r1, #15
	add r0, r0, r1, lsr #4
	add r2, r2, r0
	add r2, r2, #1
	lsr r3, r2, #28
	lsl r2, r2, #4
	mov r0, r7
	mov r1, r4
	add r12, r7, #500
	push {r1, r12}
	bl {vg_poly1305_finalize_scratch_umaal}
	ldr r1, [sp], #8
	mov r12, r7
	ldr r4, [r12, #464]
	ldr r5, [r12, #468]
	ldr r6, [r12, #472]
	ldr r7, [r12, #476]
	ldr r8, [r12, #480]
	ldr r9, [r12, #484]
	ldr r10, [r12, #488]
	ldr r11, [r12, #492]
	ldr lr, [r12, #496]
	add sp, sp, #656
	sub sp, sp, #664
	add r12, sp, #0
	mov r2, #0
	mov r3, #20
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
	str r2, [r12, #0]
	str r2, [r12, #4]
	str r2, [r12, #8]
	str r2, [r12, #12]
	str r2, [r12, #16]
	str r2, [r12, #20]
	add sp, sp, #664
	mov r0, #0
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr

vg_chacha20_poly1305_open_umaal:
	sub sp, sp, #656
	add r12, sp, #0
	str lr, [r12, #16]
	ldr lr, [sp, #656]
	str lr, [r12, #0]
	ldr lr, [sp, #660]
	str lr, [r12, #4]
	ldr lr, [sp, #664]
	str lr, [r12, #8]
	add lr, sp, #20
	str lr, [r12, #12]
	ldr lr, [sp, #16]
	ldr r12, [sp, #12]
	str r4, [r12, #464]
	str r5, [r12, #468]
	str r6, [r12, #472]
	str r7, [r12, #476]
	str r8, [r12, #480]
	str r9, [r12, #484]
	str r10, [r12, #488]
	str r11, [r12, #492]
	str lr, [r12, #496]
	mov r7, r12
	mov r8, r2
	mov r9, r3
	ldr r10, [sp, #0]
	ldr r11, [sp, #4]
	ldr r4, [sp, #8]
	mov r6, r10
	movw r12, #30821
	movt r12, #24944
	str r12, [r7, #320]
	movw r12, #25710
	movt r12, #13088
	str r12, [r7, #324]
	movw r12, #11570
	movt r12, #31074
	str r12, [r7, #328]
	movw r12, #25972
	movt r12, #27424
	str r12, [r7, #332]
	ldr r12, [r0, #0]
	str r12, [r7, #336]
	ldr r12, [r0, #4]
	str r12, [r7, #340]
	ldr r12, [r0, #8]
	str r12, [r7, #344]
	ldr r12, [r0, #12]
	str r12, [r7, #348]
	ldr r12, [r0, #16]
	str r12, [r7, #352]
	ldr r12, [r0, #20]
	str r12, [r7, #356]
	ldr r12, [r0, #24]
	str r12, [r7, #360]
	ldr r12, [r0, #28]
	str r12, [r7, #364]
	mov r12, #0
	str r12, [r7, #368]
	ldr r12, [r1, #0]
	str r12, [r7, #372]
	ldr r12, [r1, #4]
	str r12, [r7, #376]
	ldr r12, [r1, #8]
	str r12, [r7, #380]
	add r0, r7, #320
	mov r1, r7
	bl {vg_chacha20_block}
	mov r7, r1
	ldr r12, [r7, #0]
	str r12, [r7, #384]
	ldr r12, [r7, #4]
	str r12, [r7, #388]
	ldr r12, [r7, #8]
	str r12, [r7, #392]
	ldr r12, [r7, #12]
	str r12, [r7, #396]
	ldr r12, [r7, #16]
	str r12, [r7, #400]
	ldr r12, [r7, #20]
	str r12, [r7, #404]
	ldr r12, [r7, #24]
	str r12, [r7, #408]
	ldr r12, [r7, #28]
	str r12, [r7, #412]
	mov r0, r7
	add r1, r7, #384
	bl {vg_poly1305_init_core}
	mov r7, r0
	mov r1, r8
	lsr r2, r9, #4
	mov r0, r7
	bl {vg_poly1305_blocks_umaal}
	mov r7, r0
	and r3, r9, #15
	cmp r3, #0
	beq 20f
	sub r1, r9, r3
	add r1, r8, r1
	mov r12, #0
	str r12, [r7, #416]
	str r12, [r7, #420]
	str r12, [r7, #424]
	str r12, [r7, #428]
	add r2, r7, #416
22:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 22b
	add r1, r7, #416
	mov r2, #1
	mov r0, r7
	bl {vg_poly1305_blocks_umaal}
	mov r7, r0
	b 21f
20:
21:
	mov r1, r10
	lsr r2, r11, #4
	mov r0, r7
	bl {vg_poly1305_blocks_umaal}
	mov r7, r0
	and r3, r11, #15
	cmp r3, #0
	beq 23f
	sub r1, r11, r3
	add r1, r10, r1
	mov r12, #0
	str r12, [r7, #416]
	str r12, [r7, #420]
	str r12, [r7, #424]
	str r12, [r7, #428]
	add r2, r7, #416
25:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 25b
	add r1, r7, #416
	mov r2, #1
	mov r0, r7
	bl {vg_poly1305_blocks_umaal}
	mov r7, r0
	b 24f
23:
24:
	str r9, [r7, #432]
	mov r12, #0
	str r12, [r7, #436]
	str r11, [r7, #440]
	str r12, [r7, #444]
	add r1, r7, #432
	mov r2, #1
	mov r0, r7
	bl {vg_poly1305_blocks_umaal}
	mov r7, r0
	lsr r2, r9, #4
	and r3, r9, #15
	add r3, r3, #15
	add r2, r2, r3, lsr #4
	lsr r0, r11, #4
	and r1, r11, #15
	add r1, r1, #15
	add r0, r0, r1, lsr #4
	add r2, r2, r0
	add r2, r2, #1
	lsr r3, r2, #28
	lsl r2, r2, #4
	mov r0, r7
	add r1, r7, #448
	add r12, r7, #500
	push {r1, r12}
	bl {vg_poly1305_finalize_scratch_umaal}
	ldr r1, [sp], #8
	mov r12, #1
	str r12, [r7, #368]
	add r0, r7, #320
	mov r1, r10
	mov r2, r11
	mov r3, r7
	mov r5, r6
	bl {vg_chacha20_xor}
	mov r7, r1
	ldr r0, [r7, #448]
	ldr r1, [r4, #0]
	eor r0, r0, r1
	ldr r1, [r7, #452]
	ldr r2, [r4, #4]
	eor r1, r1, r2
	orr r0, r0, r1
	ldr r1, [r7, #456]
	ldr r2, [r4, #8]
	eor r1, r1, r2
	orr r0, r0, r1
	ldr r1, [r7, #460]
	ldr r2, [r4, #12]
	eor r1, r1, r2
	orr r0, r0, r1
	mov r1, #0
	sub r1, r1, r0
	orr r0, r0, r1
	lsr r0, r0, #31
	mov r1, #1
	sub r0, r1, r0
	cmp r0, #0
	beq 26f
	b 27f
26:
	mov r2, r6
	mov r3, r11
	cmp r3, #0
	beq 28f
210:
	strb r0, [r2, #0]
	add r2, r2, #1
	subs r3, r3, #1
	bne 210b
	b 29f
28:
29:
27:
	mov r12, r7
	ldr r4, [r12, #464]
	ldr r5, [r12, #468]
	ldr r6, [r12, #472]
	ldr r7, [r12, #476]
	ldr r8, [r12, #480]
	ldr r9, [r12, #484]
	ldr r10, [r12, #488]
	ldr r11, [r12, #492]
	ldr lr, [r12, #496]
	add sp, sp, #656
	sub sp, sp, #664
	add r12, sp, #0
	mov r2, #0
	mov r3, #20
211:
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
	bne 211b
	str r2, [r12, #0]
	str r2, [r12, #4]
	str r2, [r12, #8]
	str r2, [r12, #12]
	str r2, [r12, #16]
	str r2, [r12, #20]
	add sp, sp, #664
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr

vg_chacha20_poly1305_open_to_umaal:
	sub sp, sp, #664
	add r12, sp, #0
	str lr, [r12, #24]
	ldr lr, [sp, #664]
	str lr, [r12, #0]
	ldr lr, [sp, #668]
	str lr, [r12, #4]
	ldr lr, [sp, #672]
	str lr, [r12, #8]
	ldr lr, [sp, #676]
	str lr, [r12, #12]
	ldr lr, [sp, #680]
	str lr, [r12, #16]
	add lr, sp, #28
	str lr, [r12, #20]
	ldr lr, [sp, #24]
	ldr r12, [sp, #20]
	str r4, [r12, #464]
	str r5, [r12, #468]
	str r6, [r12, #472]
	str r7, [r12, #476]
	str r8, [r12, #480]
	str r9, [r12, #484]
	str r10, [r12, #488]
	str r11, [r12, #492]
	str lr, [r12, #496]
	mov r7, r12
	mov r8, r2
	mov r9, r3
	ldr r10, [sp, #0]
	ldr r11, [sp, #4]
	ldr r4, [sp, #16]
	ldr r6, [sp, #8]
	movw r12, #30821
	movt r12, #24944
	str r12, [r7, #320]
	movw r12, #25710
	movt r12, #13088
	str r12, [r7, #324]
	movw r12, #11570
	movt r12, #31074
	str r12, [r7, #328]
	movw r12, #25972
	movt r12, #27424
	str r12, [r7, #332]
	ldr r12, [r0, #0]
	str r12, [r7, #336]
	ldr r12, [r0, #4]
	str r12, [r7, #340]
	ldr r12, [r0, #8]
	str r12, [r7, #344]
	ldr r12, [r0, #12]
	str r12, [r7, #348]
	ldr r12, [r0, #16]
	str r12, [r7, #352]
	ldr r12, [r0, #20]
	str r12, [r7, #356]
	ldr r12, [r0, #24]
	str r12, [r7, #360]
	ldr r12, [r0, #28]
	str r12, [r7, #364]
	mov r12, #0
	str r12, [r7, #368]
	ldr r12, [r1, #0]
	str r12, [r7, #372]
	ldr r12, [r1, #4]
	str r12, [r7, #376]
	ldr r12, [r1, #8]
	str r12, [r7, #380]
	add r0, r7, #320
	mov r1, r7
	bl {vg_chacha20_block}
	mov r7, r1
	ldr r12, [r7, #0]
	str r12, [r7, #384]
	ldr r12, [r7, #4]
	str r12, [r7, #388]
	ldr r12, [r7, #8]
	str r12, [r7, #392]
	ldr r12, [r7, #12]
	str r12, [r7, #396]
	ldr r12, [r7, #16]
	str r12, [r7, #400]
	ldr r12, [r7, #20]
	str r12, [r7, #404]
	ldr r12, [r7, #24]
	str r12, [r7, #408]
	ldr r12, [r7, #28]
	str r12, [r7, #412]
	mov r0, r7
	add r1, r7, #384
	bl {vg_poly1305_init_core}
	mov r7, r0
	mov r1, r8
	lsr r2, r9, #4
	mov r0, r7
	bl {vg_poly1305_blocks_umaal}
	mov r7, r0
	and r3, r9, #15
	cmp r3, #0
	beq 20f
	sub r1, r9, r3
	add r1, r8, r1
	mov r12, #0
	str r12, [r7, #416]
	str r12, [r7, #420]
	str r12, [r7, #424]
	str r12, [r7, #428]
	add r2, r7, #416
22:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 22b
	add r1, r7, #416
	mov r2, #1
	mov r0, r7
	bl {vg_poly1305_blocks_umaal}
	mov r7, r0
	b 21f
20:
21:
	mov r1, r10
	lsr r2, r11, #4
	mov r0, r7
	bl {vg_poly1305_blocks_umaal}
	mov r7, r0
	and r3, r11, #15
	cmp r3, #0
	beq 23f
	sub r1, r11, r3
	add r1, r10, r1
	mov r12, #0
	str r12, [r7, #416]
	str r12, [r7, #420]
	str r12, [r7, #424]
	str r12, [r7, #428]
	add r2, r7, #416
25:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 25b
	add r1, r7, #416
	mov r2, #1
	mov r0, r7
	bl {vg_poly1305_blocks_umaal}
	mov r7, r0
	b 24f
23:
24:
	str r9, [r7, #432]
	mov r12, #0
	str r12, [r7, #436]
	str r11, [r7, #440]
	str r12, [r7, #444]
	add r1, r7, #432
	mov r2, #1
	mov r0, r7
	bl {vg_poly1305_blocks_umaal}
	mov r7, r0
	lsr r2, r9, #4
	and r3, r9, #15
	add r3, r3, #15
	add r2, r2, r3, lsr #4
	lsr r0, r11, #4
	and r1, r11, #15
	add r1, r1, #15
	add r0, r0, r1, lsr #4
	add r2, r2, r0
	add r2, r2, #1
	lsr r3, r2, #28
	lsl r2, r2, #4
	mov r0, r7
	add r1, r7, #448
	add r12, r7, #500
	push {r1, r12}
	bl {vg_poly1305_finalize_scratch_umaal}
	ldr r1, [sp], #8
	mov r12, #1
	str r12, [r7, #368]
	add r0, r7, #320
	mov r1, r10
	mov r2, r11
	mov r3, r7
	mov r5, r6
	bl {vg_chacha20_xor}
	mov r7, r1
	ldr r0, [r7, #448]
	ldr r1, [r4, #0]
	eor r0, r0, r1
	ldr r1, [r7, #452]
	ldr r2, [r4, #4]
	eor r1, r1, r2
	orr r0, r0, r1
	ldr r1, [r7, #456]
	ldr r2, [r4, #8]
	eor r1, r1, r2
	orr r0, r0, r1
	ldr r1, [r7, #460]
	ldr r2, [r4, #12]
	eor r1, r1, r2
	orr r0, r0, r1
	mov r1, #0
	sub r1, r1, r0
	orr r0, r0, r1
	lsr r0, r0, #31
	mov r1, #1
	sub r0, r1, r0
	cmp r0, #0
	beq 26f
	b 27f
26:
	mov r2, r6
	mov r3, r11
	cmp r3, #0
	beq 28f
210:
	strb r0, [r2, #0]
	add r2, r2, #1
	subs r3, r3, #1
	bne 210b
	b 29f
28:
29:
27:
	mov r12, r7
	ldr r4, [r12, #464]
	ldr r5, [r12, #468]
	ldr r6, [r12, #472]
	ldr r7, [r12, #476]
	ldr r8, [r12, #480]
	ldr r9, [r12, #484]
	ldr r10, [r12, #488]
	ldr r11, [r12, #492]
	ldr lr, [r12, #496]
	add sp, sp, #664
	sub sp, sp, #672
	add r12, sp, #0
	mov r2, #0
	mov r3, #21
211:
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
	bne 211b
	add sp, sp, #672
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr

vg_chacha20_poly1305_seal_gather_umaal:
	sub sp, sp, #32
	add r12, sp, #0
	str lr, [r12, #12]
	str r0, [r12, #16]
	str r1, [r12, #20]
	str r2, [r12, #24]
	str r3, [r12, #28]
	ldr lr, [r12, #40]
	str lr, [r12, #0]
	ldr lr, [r12, #44]
	str lr, [r12, #4]
	ldr lr, [r12, #48]
	str lr, [r12, #8]
	ldr r0, [r12, #32]
	ldr r2, [r12, #40]
	ldr lr, [r12, #36]
	cmp lr, #0
	beq 20f
22:
	ldr r1, [r0, #0]
	ldr r3, [r0, #4]
	lsr r3, r3, #2
	cmp r3, #0
	beq 23f
25:
	ldr r12, [r1, #0]
	str r12, [r2, #0]
	add r1, r1, #4
	add r2, r2, #4
	subs r3, r3, #1
	bne 25b
	b 24f
23:
24:
	ldr r3, [r0, #4]
	and r3, r3, #3
	cmp r3, #0
	beq 26f
28:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 28b
	b 27f
26:
27:
	add r0, r0, #8
	subs lr, lr, #1
	bne 22b
	b 21f
20:
21:
	add r12, sp, #0
	ldr r0, [r12, #16]
	ldr r1, [r12, #20]
	ldr r2, [r12, #24]
	ldr r3, [r12, #28]
	bl {vg_chacha20_poly1305_seal_umaal_core}
	add r12, sp, #0
	ldr lr, [r12, #12]
	add sp, sp, #32
	sub sp, sp, #696
	add r12, sp, #0
	mov r2, #0
	mov r3, #21
29:
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
	bne 29b
	str r2, [r12, #0]
	str r2, [r12, #4]
	str r2, [r12, #8]
	str r2, [r12, #12]
	str r2, [r12, #16]
	str r2, [r12, #20]
	add sp, sp, #696
	mov r0, #0
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr

vg_chacha20_poly1305_seal:
	sub sp, sp, #656
	add r12, sp, #0
	str lr, [r12, #16]
	ldr lr, [sp, #656]
	str lr, [r12, #0]
	ldr lr, [sp, #660]
	str lr, [r12, #4]
	ldr lr, [sp, #664]
	str lr, [r12, #8]
	add lr, sp, #20
	str lr, [r12, #12]
	ldr lr, [sp, #16]
	ldr r12, [sp, #12]
	str r4, [r12, #464]
	str r5, [r12, #468]
	str r6, [r12, #472]
	str r7, [r12, #476]
	str r8, [r12, #480]
	str r9, [r12, #484]
	str r10, [r12, #488]
	str r11, [r12, #492]
	str lr, [r12, #496]
	mov r7, r12
	mov r8, r2
	mov r9, r3
	ldr r10, [sp, #0]
	ldr r11, [sp, #4]
	ldr r4, [sp, #8]
	mov r6, r10
	movw r12, #30821
	movt r12, #24944
	str r12, [r7, #320]
	movw r12, #25710
	movt r12, #13088
	str r12, [r7, #324]
	movw r12, #11570
	movt r12, #31074
	str r12, [r7, #328]
	movw r12, #25972
	movt r12, #27424
	str r12, [r7, #332]
	ldr r12, [r0, #0]
	str r12, [r7, #336]
	ldr r12, [r0, #4]
	str r12, [r7, #340]
	ldr r12, [r0, #8]
	str r12, [r7, #344]
	ldr r12, [r0, #12]
	str r12, [r7, #348]
	ldr r12, [r0, #16]
	str r12, [r7, #352]
	ldr r12, [r0, #20]
	str r12, [r7, #356]
	ldr r12, [r0, #24]
	str r12, [r7, #360]
	ldr r12, [r0, #28]
	str r12, [r7, #364]
	mov r12, #0
	str r12, [r7, #368]
	ldr r12, [r1, #0]
	str r12, [r7, #372]
	ldr r12, [r1, #4]
	str r12, [r7, #376]
	ldr r12, [r1, #8]
	str r12, [r7, #380]
	add r0, r7, #320
	mov r1, r7
	bl {vg_chacha20_block}
	mov r7, r1
	ldr r12, [r7, #0]
	str r12, [r7, #384]
	ldr r12, [r7, #4]
	str r12, [r7, #388]
	ldr r12, [r7, #8]
	str r12, [r7, #392]
	ldr r12, [r7, #12]
	str r12, [r7, #396]
	ldr r12, [r7, #16]
	str r12, [r7, #400]
	ldr r12, [r7, #20]
	str r12, [r7, #404]
	ldr r12, [r7, #24]
	str r12, [r7, #408]
	ldr r12, [r7, #28]
	str r12, [r7, #412]
	mov r12, #1
	str r12, [r7, #368]
	add r0, r7, #320
	mov r1, r10
	mov r2, r11
	mov r3, r7
	mov r5, r6
	bl {vg_chacha20_xor}
	mov r7, r1
	mov r0, r7
	add r1, r7, #384
	bl {vg_poly1305_init_core}
	mov r7, r0
	mov r1, r8
	lsr r2, r9, #4
	mov r0, r7
	bl {vg_poly1305_blocks}
	mov r7, r0
	and r3, r9, #15
	cmp r3, #0
	beq 20f
	sub r1, r9, r3
	add r1, r8, r1
	mov r12, #0
	str r12, [r7, #416]
	str r12, [r7, #420]
	str r12, [r7, #424]
	str r12, [r7, #428]
	add r2, r7, #416
22:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 22b
	add r1, r7, #416
	mov r2, #1
	mov r0, r7
	bl {vg_poly1305_blocks}
	mov r7, r0
	b 21f
20:
21:
	mov r1, r10
	lsr r2, r11, #4
	mov r0, r7
	bl {vg_poly1305_blocks}
	mov r7, r0
	and r3, r11, #15
	cmp r3, #0
	beq 23f
	sub r1, r11, r3
	add r1, r10, r1
	mov r12, #0
	str r12, [r7, #416]
	str r12, [r7, #420]
	str r12, [r7, #424]
	str r12, [r7, #428]
	add r2, r7, #416
25:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 25b
	add r1, r7, #416
	mov r2, #1
	mov r0, r7
	bl {vg_poly1305_blocks}
	mov r7, r0
	b 24f
23:
24:
	str r9, [r7, #432]
	mov r12, #0
	str r12, [r7, #436]
	str r11, [r7, #440]
	str r12, [r7, #444]
	add r1, r7, #432
	mov r2, #1
	mov r0, r7
	bl {vg_poly1305_blocks}
	mov r7, r0
	lsr r2, r9, #4
	and r3, r9, #15
	add r3, r3, #15
	add r2, r2, r3, lsr #4
	lsr r0, r11, #4
	and r1, r11, #15
	add r1, r1, #15
	add r0, r0, r1, lsr #4
	add r2, r2, r0
	add r2, r2, #1
	lsr r3, r2, #28
	lsl r2, r2, #4
	mov r0, r7
	mov r1, r4
	add r12, r7, #500
	push {r1, r12}
	bl {vg_poly1305_finalize_scratch}
	ldr r1, [sp], #8
	mov r12, r7
	ldr r4, [r12, #464]
	ldr r5, [r12, #468]
	ldr r6, [r12, #472]
	ldr r7, [r12, #476]
	ldr r8, [r12, #480]
	ldr r9, [r12, #484]
	ldr r10, [r12, #488]
	ldr r11, [r12, #492]
	ldr lr, [r12, #496]
	add sp, sp, #656
	sub sp, sp, #664
	add r12, sp, #0
	mov r2, #0
	mov r3, #20
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
	str r2, [r12, #0]
	str r2, [r12, #4]
	str r2, [r12, #8]
	str r2, [r12, #12]
	str r2, [r12, #16]
	str r2, [r12, #20]
	add sp, sp, #664
	mov r0, #0
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr

vg_chacha20_poly1305_open:
	sub sp, sp, #656
	add r12, sp, #0
	str lr, [r12, #16]
	ldr lr, [sp, #656]
	str lr, [r12, #0]
	ldr lr, [sp, #660]
	str lr, [r12, #4]
	ldr lr, [sp, #664]
	str lr, [r12, #8]
	add lr, sp, #20
	str lr, [r12, #12]
	ldr lr, [sp, #16]
	ldr r12, [sp, #12]
	str r4, [r12, #464]
	str r5, [r12, #468]
	str r6, [r12, #472]
	str r7, [r12, #476]
	str r8, [r12, #480]
	str r9, [r12, #484]
	str r10, [r12, #488]
	str r11, [r12, #492]
	str lr, [r12, #496]
	mov r7, r12
	mov r8, r2
	mov r9, r3
	ldr r10, [sp, #0]
	ldr r11, [sp, #4]
	ldr r4, [sp, #8]
	mov r6, r10
	movw r12, #30821
	movt r12, #24944
	str r12, [r7, #320]
	movw r12, #25710
	movt r12, #13088
	str r12, [r7, #324]
	movw r12, #11570
	movt r12, #31074
	str r12, [r7, #328]
	movw r12, #25972
	movt r12, #27424
	str r12, [r7, #332]
	ldr r12, [r0, #0]
	str r12, [r7, #336]
	ldr r12, [r0, #4]
	str r12, [r7, #340]
	ldr r12, [r0, #8]
	str r12, [r7, #344]
	ldr r12, [r0, #12]
	str r12, [r7, #348]
	ldr r12, [r0, #16]
	str r12, [r7, #352]
	ldr r12, [r0, #20]
	str r12, [r7, #356]
	ldr r12, [r0, #24]
	str r12, [r7, #360]
	ldr r12, [r0, #28]
	str r12, [r7, #364]
	mov r12, #0
	str r12, [r7, #368]
	ldr r12, [r1, #0]
	str r12, [r7, #372]
	ldr r12, [r1, #4]
	str r12, [r7, #376]
	ldr r12, [r1, #8]
	str r12, [r7, #380]
	add r0, r7, #320
	mov r1, r7
	bl {vg_chacha20_block}
	mov r7, r1
	ldr r12, [r7, #0]
	str r12, [r7, #384]
	ldr r12, [r7, #4]
	str r12, [r7, #388]
	ldr r12, [r7, #8]
	str r12, [r7, #392]
	ldr r12, [r7, #12]
	str r12, [r7, #396]
	ldr r12, [r7, #16]
	str r12, [r7, #400]
	ldr r12, [r7, #20]
	str r12, [r7, #404]
	ldr r12, [r7, #24]
	str r12, [r7, #408]
	ldr r12, [r7, #28]
	str r12, [r7, #412]
	mov r0, r7
	add r1, r7, #384
	bl {vg_poly1305_init_core}
	mov r7, r0
	mov r1, r8
	lsr r2, r9, #4
	mov r0, r7
	bl {vg_poly1305_blocks}
	mov r7, r0
	and r3, r9, #15
	cmp r3, #0
	beq 20f
	sub r1, r9, r3
	add r1, r8, r1
	mov r12, #0
	str r12, [r7, #416]
	str r12, [r7, #420]
	str r12, [r7, #424]
	str r12, [r7, #428]
	add r2, r7, #416
22:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 22b
	add r1, r7, #416
	mov r2, #1
	mov r0, r7
	bl {vg_poly1305_blocks}
	mov r7, r0
	b 21f
20:
21:
	mov r1, r10
	lsr r2, r11, #4
	mov r0, r7
	bl {vg_poly1305_blocks}
	mov r7, r0
	and r3, r11, #15
	cmp r3, #0
	beq 23f
	sub r1, r11, r3
	add r1, r10, r1
	mov r12, #0
	str r12, [r7, #416]
	str r12, [r7, #420]
	str r12, [r7, #424]
	str r12, [r7, #428]
	add r2, r7, #416
25:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 25b
	add r1, r7, #416
	mov r2, #1
	mov r0, r7
	bl {vg_poly1305_blocks}
	mov r7, r0
	b 24f
23:
24:
	str r9, [r7, #432]
	mov r12, #0
	str r12, [r7, #436]
	str r11, [r7, #440]
	str r12, [r7, #444]
	add r1, r7, #432
	mov r2, #1
	mov r0, r7
	bl {vg_poly1305_blocks}
	mov r7, r0
	lsr r2, r9, #4
	and r3, r9, #15
	add r3, r3, #15
	add r2, r2, r3, lsr #4
	lsr r0, r11, #4
	and r1, r11, #15
	add r1, r1, #15
	add r0, r0, r1, lsr #4
	add r2, r2, r0
	add r2, r2, #1
	lsr r3, r2, #28
	lsl r2, r2, #4
	mov r0, r7
	add r1, r7, #448
	add r12, r7, #500
	push {r1, r12}
	bl {vg_poly1305_finalize_scratch}
	ldr r1, [sp], #8
	mov r12, #1
	str r12, [r7, #368]
	add r0, r7, #320
	mov r1, r10
	mov r2, r11
	mov r3, r7
	mov r5, r6
	bl {vg_chacha20_xor}
	mov r7, r1
	ldr r0, [r7, #448]
	ldr r1, [r4, #0]
	eor r0, r0, r1
	ldr r1, [r7, #452]
	ldr r2, [r4, #4]
	eor r1, r1, r2
	orr r0, r0, r1
	ldr r1, [r7, #456]
	ldr r2, [r4, #8]
	eor r1, r1, r2
	orr r0, r0, r1
	ldr r1, [r7, #460]
	ldr r2, [r4, #12]
	eor r1, r1, r2
	orr r0, r0, r1
	mov r1, #0
	sub r1, r1, r0
	orr r0, r0, r1
	lsr r0, r0, #31
	mov r1, #1
	sub r0, r1, r0
	cmp r0, #0
	beq 26f
	b 27f
26:
	mov r2, r6
	mov r3, r11
	cmp r3, #0
	beq 28f
210:
	strb r0, [r2, #0]
	add r2, r2, #1
	subs r3, r3, #1
	bne 210b
	b 29f
28:
29:
27:
	mov r12, r7
	ldr r4, [r12, #464]
	ldr r5, [r12, #468]
	ldr r6, [r12, #472]
	ldr r7, [r12, #476]
	ldr r8, [r12, #480]
	ldr r9, [r12, #484]
	ldr r10, [r12, #488]
	ldr r11, [r12, #492]
	ldr lr, [r12, #496]
	add sp, sp, #656
	sub sp, sp, #664
	add r12, sp, #0
	mov r2, #0
	mov r3, #20
211:
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
	bne 211b
	str r2, [r12, #0]
	str r2, [r12, #4]
	str r2, [r12, #8]
	str r2, [r12, #12]
	str r2, [r12, #16]
	str r2, [r12, #20]
	add sp, sp, #664
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr

vg_chacha20_poly1305_open_to:
	sub sp, sp, #664
	add r12, sp, #0
	str lr, [r12, #24]
	ldr lr, [sp, #664]
	str lr, [r12, #0]
	ldr lr, [sp, #668]
	str lr, [r12, #4]
	ldr lr, [sp, #672]
	str lr, [r12, #8]
	ldr lr, [sp, #676]
	str lr, [r12, #12]
	ldr lr, [sp, #680]
	str lr, [r12, #16]
	add lr, sp, #28
	str lr, [r12, #20]
	ldr lr, [sp, #24]
	ldr r12, [sp, #20]
	str r4, [r12, #464]
	str r5, [r12, #468]
	str r6, [r12, #472]
	str r7, [r12, #476]
	str r8, [r12, #480]
	str r9, [r12, #484]
	str r10, [r12, #488]
	str r11, [r12, #492]
	str lr, [r12, #496]
	mov r7, r12
	mov r8, r2
	mov r9, r3
	ldr r10, [sp, #0]
	ldr r11, [sp, #4]
	ldr r4, [sp, #16]
	ldr r6, [sp, #8]
	movw r12, #30821
	movt r12, #24944
	str r12, [r7, #320]
	movw r12, #25710
	movt r12, #13088
	str r12, [r7, #324]
	movw r12, #11570
	movt r12, #31074
	str r12, [r7, #328]
	movw r12, #25972
	movt r12, #27424
	str r12, [r7, #332]
	ldr r12, [r0, #0]
	str r12, [r7, #336]
	ldr r12, [r0, #4]
	str r12, [r7, #340]
	ldr r12, [r0, #8]
	str r12, [r7, #344]
	ldr r12, [r0, #12]
	str r12, [r7, #348]
	ldr r12, [r0, #16]
	str r12, [r7, #352]
	ldr r12, [r0, #20]
	str r12, [r7, #356]
	ldr r12, [r0, #24]
	str r12, [r7, #360]
	ldr r12, [r0, #28]
	str r12, [r7, #364]
	mov r12, #0
	str r12, [r7, #368]
	ldr r12, [r1, #0]
	str r12, [r7, #372]
	ldr r12, [r1, #4]
	str r12, [r7, #376]
	ldr r12, [r1, #8]
	str r12, [r7, #380]
	add r0, r7, #320
	mov r1, r7
	bl {vg_chacha20_block}
	mov r7, r1
	ldr r12, [r7, #0]
	str r12, [r7, #384]
	ldr r12, [r7, #4]
	str r12, [r7, #388]
	ldr r12, [r7, #8]
	str r12, [r7, #392]
	ldr r12, [r7, #12]
	str r12, [r7, #396]
	ldr r12, [r7, #16]
	str r12, [r7, #400]
	ldr r12, [r7, #20]
	str r12, [r7, #404]
	ldr r12, [r7, #24]
	str r12, [r7, #408]
	ldr r12, [r7, #28]
	str r12, [r7, #412]
	mov r0, r7
	add r1, r7, #384
	bl {vg_poly1305_init_core}
	mov r7, r0
	mov r1, r8
	lsr r2, r9, #4
	mov r0, r7
	bl {vg_poly1305_blocks}
	mov r7, r0
	and r3, r9, #15
	cmp r3, #0
	beq 20f
	sub r1, r9, r3
	add r1, r8, r1
	mov r12, #0
	str r12, [r7, #416]
	str r12, [r7, #420]
	str r12, [r7, #424]
	str r12, [r7, #428]
	add r2, r7, #416
22:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 22b
	add r1, r7, #416
	mov r2, #1
	mov r0, r7
	bl {vg_poly1305_blocks}
	mov r7, r0
	b 21f
20:
21:
	mov r1, r10
	lsr r2, r11, #4
	mov r0, r7
	bl {vg_poly1305_blocks}
	mov r7, r0
	and r3, r11, #15
	cmp r3, #0
	beq 23f
	sub r1, r11, r3
	add r1, r10, r1
	mov r12, #0
	str r12, [r7, #416]
	str r12, [r7, #420]
	str r12, [r7, #424]
	str r12, [r7, #428]
	add r2, r7, #416
25:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 25b
	add r1, r7, #416
	mov r2, #1
	mov r0, r7
	bl {vg_poly1305_blocks}
	mov r7, r0
	b 24f
23:
24:
	str r9, [r7, #432]
	mov r12, #0
	str r12, [r7, #436]
	str r11, [r7, #440]
	str r12, [r7, #444]
	add r1, r7, #432
	mov r2, #1
	mov r0, r7
	bl {vg_poly1305_blocks}
	mov r7, r0
	lsr r2, r9, #4
	and r3, r9, #15
	add r3, r3, #15
	add r2, r2, r3, lsr #4
	lsr r0, r11, #4
	and r1, r11, #15
	add r1, r1, #15
	add r0, r0, r1, lsr #4
	add r2, r2, r0
	add r2, r2, #1
	lsr r3, r2, #28
	lsl r2, r2, #4
	mov r0, r7
	add r1, r7, #448
	add r12, r7, #500
	push {r1, r12}
	bl {vg_poly1305_finalize_scratch}
	ldr r1, [sp], #8
	mov r12, #1
	str r12, [r7, #368]
	add r0, r7, #320
	mov r1, r10
	mov r2, r11
	mov r3, r7
	mov r5, r6
	bl {vg_chacha20_xor}
	mov r7, r1
	ldr r0, [r7, #448]
	ldr r1, [r4, #0]
	eor r0, r0, r1
	ldr r1, [r7, #452]
	ldr r2, [r4, #4]
	eor r1, r1, r2
	orr r0, r0, r1
	ldr r1, [r7, #456]
	ldr r2, [r4, #8]
	eor r1, r1, r2
	orr r0, r0, r1
	ldr r1, [r7, #460]
	ldr r2, [r4, #12]
	eor r1, r1, r2
	orr r0, r0, r1
	mov r1, #0
	sub r1, r1, r0
	orr r0, r0, r1
	lsr r0, r0, #31
	mov r1, #1
	sub r0, r1, r0
	cmp r0, #0
	beq 26f
	b 27f
26:
	mov r2, r6
	mov r3, r11
	cmp r3, #0
	beq 28f
210:
	strb r0, [r2, #0]
	add r2, r2, #1
	subs r3, r3, #1
	bne 210b
	b 29f
28:
29:
27:
	mov r12, r7
	ldr r4, [r12, #464]
	ldr r5, [r12, #468]
	ldr r6, [r12, #472]
	ldr r7, [r12, #476]
	ldr r8, [r12, #480]
	ldr r9, [r12, #484]
	ldr r10, [r12, #488]
	ldr r11, [r12, #492]
	ldr lr, [r12, #496]
	add sp, sp, #664
	sub sp, sp, #672
	add r12, sp, #0
	mov r2, #0
	mov r3, #21
211:
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
	bne 211b
	add sp, sp, #672
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr

vg_chacha20_poly1305_seal_gather:
	sub sp, sp, #32
	add r12, sp, #0
	str lr, [r12, #12]
	str r0, [r12, #16]
	str r1, [r12, #20]
	str r2, [r12, #24]
	str r3, [r12, #28]
	ldr lr, [r12, #40]
	str lr, [r12, #0]
	ldr lr, [r12, #44]
	str lr, [r12, #4]
	ldr lr, [r12, #48]
	str lr, [r12, #8]
	ldr r0, [r12, #32]
	ldr r2, [r12, #40]
	ldr lr, [r12, #36]
	cmp lr, #0
	beq 20f
22:
	ldr r1, [r0, #0]
	ldr r3, [r0, #4]
	lsr r3, r3, #2
	cmp r3, #0
	beq 23f
25:
	ldr r12, [r1, #0]
	str r12, [r2, #0]
	add r1, r1, #4
	add r2, r2, #4
	subs r3, r3, #1
	bne 25b
	b 24f
23:
24:
	ldr r3, [r0, #4]
	and r3, r3, #3
	cmp r3, #0
	beq 26f
28:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 28b
	b 27f
26:
27:
	add r0, r0, #8
	subs lr, lr, #1
	bne 22b
	b 21f
20:
21:
	add r12, sp, #0
	ldr r0, [r12, #16]
	ldr r1, [r12, #20]
	ldr r2, [r12, #24]
	ldr r3, [r12, #28]
	bl {vg_chacha20_poly1305_seal_core}
	add r12, sp, #0
	ldr lr, [r12, #12]
	add sp, sp, #32
	sub sp, sp, #696
	add r12, sp, #0
	mov r2, #0
	mov r3, #21
29:
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
	bne 29b
	str r2, [r12, #0]
	str r2, [r12, #4]
	str r2, [r12, #8]
	str r2, [r12, #12]
	str r2, [r12, #16]
	str r2, [r12, #20]
	add sp, sp, #696
	mov r0, #0
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr
