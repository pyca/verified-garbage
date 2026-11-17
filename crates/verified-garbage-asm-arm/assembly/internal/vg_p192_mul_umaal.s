// The functions of `src/internal/vg_p192_mul_umaal.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p192_mul_umaal:
	mov r12, r0
	str r4, [r12, #1144]
	str r5, [r12, #1148]
	str r6, [r12, #1152]
	str r7, [r12, #1156]
	str r8, [r12, #1160]
	str r9, [r12, #1164]
	str r11, [r12, #1172]
	str lr, [r12, #1176]
	mov lr, r10
	mov r11, #24
20:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #808]
	add r5, r12, r11, lsl #3
	add r5, r5, #4096
	and r7, r4, #1
	strb r7, [r5, #0]
	lsr r7, r4, #1
	and r7, r7, #1
	strb r7, [r5, #1]
	lsr r7, r4, #2
	and r7, r7, #1
	strb r7, [r5, #2]
	lsr r7, r4, #3
	and r7, r7, #1
	strb r7, [r5, #3]
	lsr r7, r4, #4
	and r7, r7, #1
	strb r7, [r5, #4]
	lsr r7, r4, #5
	and r7, r7, #1
	strb r7, [r5, #5]
	lsr r7, r4, #6
	and r7, r7, #1
	strb r7, [r5, #6]
	lsr r7, r4, #7
	and r7, r7, #1
	strb r7, [r5, #7]
	cmp r11, #0
	bne 20b
	movw r5, #4672
	add r5, r12, r5
	ldr r4, [r12, #136]
	str r4, [r5, #0]
	ldr r4, [r12, #140]
	str r4, [r5, #4]
	ldr r4, [r12, #144]
	str r4, [r5, #8]
	ldr r4, [r12, #148]
	str r4, [r5, #12]
	ldr r4, [r12, #152]
	str r4, [r5, #16]
	ldr r4, [r12, #156]
	str r4, [r5, #20]
	ldr r4, [r12, #184]
	str r4, [r5, #24]
	ldr r4, [r12, #188]
	str r4, [r5, #28]
	ldr r4, [r12, #192]
	str r4, [r5, #32]
	ldr r4, [r12, #196]
	str r4, [r5, #36]
	ldr r4, [r12, #200]
	str r4, [r5, #40]
	ldr r4, [r12, #204]
	str r4, [r5, #44]
	ldr r4, [r12, #136]
	str r4, [r5, #48]
	ldr r4, [r12, #140]
	str r4, [r5, #52]
	ldr r4, [r12, #144]
	str r4, [r5, #56]
	ldr r4, [r12, #148]
	str r4, [r5, #60]
	ldr r4, [r12, #152]
	str r4, [r5, #64]
	ldr r4, [r12, #156]
	str r4, [r5, #68]
	ldr r4, [r12, #400]
	str r4, [r5, #72]
	ldr r4, [r12, #404]
	str r4, [r5, #76]
	ldr r4, [r12, #408]
	str r4, [r5, #80]
	ldr r4, [r12, #412]
	str r4, [r5, #84]
	ldr r4, [r12, #416]
	str r4, [r5, #88]
	ldr r4, [r12, #420]
	str r4, [r5, #92]
	ldr r4, [r12, #424]
	str r4, [r5, #96]
	ldr r4, [r12, #428]
	str r4, [r5, #100]
	ldr r4, [r12, #432]
	str r4, [r5, #104]
	ldr r4, [r12, #436]
	str r4, [r5, #108]
	ldr r4, [r12, #440]
	str r4, [r5, #112]
	ldr r4, [r12, #444]
	str r4, [r5, #116]
	ldr r4, [r12, #184]
	str r4, [r5, #120]
	ldr r4, [r12, #188]
	str r4, [r5, #124]
	ldr r4, [r12, #192]
	str r4, [r5, #128]
	ldr r4, [r12, #196]
	str r4, [r5, #132]
	ldr r4, [r12, #200]
	str r4, [r5, #136]
	ldr r4, [r12, #204]
	str r4, [r5, #140]
	ldr r4, [r12, #400]
	str r4, [r12, #472]
	ldr r4, [r12, #404]
	str r4, [r12, #476]
	ldr r4, [r12, #408]
	str r4, [r12, #480]
	ldr r4, [r12, #412]
	str r4, [r12, #484]
	ldr r4, [r12, #416]
	str r4, [r12, #488]
	ldr r4, [r12, #420]
	str r4, [r12, #492]
	ldr r4, [r12, #424]
	str r4, [r12, #496]
	ldr r4, [r12, #428]
	str r4, [r12, #500]
	ldr r4, [r12, #432]
	str r4, [r12, #504]
	ldr r4, [r12, #436]
	str r4, [r12, #508]
	ldr r4, [r12, #440]
	str r4, [r12, #512]
	ldr r4, [r12, #444]
	str r4, [r12, #516]
	ldr r4, [r12, #184]
	str r4, [r12, #520]
	ldr r4, [r12, #188]
	str r4, [r12, #524]
	ldr r4, [r12, #192]
	str r4, [r12, #528]
	ldr r4, [r12, #196]
	str r4, [r12, #532]
	ldr r4, [r12, #200]
	str r4, [r12, #536]
	ldr r4, [r12, #204]
	str r4, [r12, #540]
	mov r11, #1
21:
	mov r10, lr
	mov r0, r12
	movw r1, #616
	movw r2, #472
	movw r3, #400
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #640
	movw r2, #496
	movw r3, #424
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #664
	movw r2, #520
	movw r3, #184
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #688
	movw r2, #472
	movw r3, #496
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #712
	movw r2, #400
	movw r3, #424
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #688
	movw r2, #688
	movw r3, #712
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #712
	movw r2, #616
	movw r3, #640
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #688
	movw r2, #688
	movw r3, #712
	bl {vg_p192_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #712
	movw r2, #472
	movw r3, #520
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #736
	movw r2, #400
	movw r3, #184
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #712
	movw r2, #712
	movw r3, #736
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #736
	movw r2, #616
	movw r3, #664
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #712
	movw r2, #712
	movw r3, #736
	bl {vg_p192_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #736
	movw r2, #496
	movw r3, #520
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #544
	movw r2, #424
	movw r3, #184
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #736
	movw r2, #736
	movw r3, #544
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #544
	movw r2, #640
	movw r3, #664
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #736
	movw r2, #736
	movw r3, #544
	bl {vg_p192_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #592
	movw r2, #208
	movw r3, #712
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #544
	movw r2, #232
	movw r3, #664
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #592
	movw r2, #544
	movw r3, #592
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #544
	movw r2, #640
	movw r3, #592
	bl {vg_p192_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #592
	movw r2, #640
	movw r3, #592
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #568
	movw r2, #544
	movw r3, #592
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #640
	movw r2, #616
	movw r3, #616
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #640
	movw r2, #640
	movw r3, #616
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #664
	movw r2, #208
	movw r3, #664
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #712
	movw r2, #232
	movw r3, #712
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #640
	movw r2, #640
	movw r3, #664
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #664
	movw r2, #616
	movw r3, #664
	bl {vg_p192_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #664
	movw r2, #208
	movw r3, #664
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #712
	movw r2, #712
	movw r3, #664
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #616
	movw r2, #640
	movw r3, #712
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #568
	movw r2, #568
	movw r3, #616
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #616
	movw r2, #736
	movw r3, #712
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #544
	movw r2, #688
	movw r3, #544
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #544
	movw r2, #544
	movw r3, #616
	bl {vg_p192_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #616
	movw r2, #688
	movw r3, #640
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #592
	movw r2, #736
	movw r3, #592
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #592
	movw r2, #592
	movw r3, #616
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r4, #72
	mul r4, r4, r11
	movw r5, #4744
	add r5, r12, r5
	add r5, r5, r4
	ldr r4, [r12, #544]
	str r4, [r5, #0]
	ldr r4, [r12, #548]
	str r4, [r5, #4]
	ldr r4, [r12, #552]
	str r4, [r5, #8]
	ldr r4, [r12, #556]
	str r4, [r5, #12]
	ldr r4, [r12, #560]
	str r4, [r5, #16]
	ldr r4, [r12, #564]
	str r4, [r5, #20]
	ldr r4, [r12, #568]
	str r4, [r5, #24]
	ldr r4, [r12, #572]
	str r4, [r5, #28]
	ldr r4, [r12, #576]
	str r4, [r5, #32]
	ldr r4, [r12, #580]
	str r4, [r5, #36]
	ldr r4, [r12, #584]
	str r4, [r5, #40]
	ldr r4, [r12, #588]
	str r4, [r5, #44]
	ldr r4, [r12, #592]
	str r4, [r5, #48]
	ldr r4, [r12, #596]
	str r4, [r5, #52]
	ldr r4, [r12, #600]
	str r4, [r5, #56]
	ldr r4, [r12, #604]
	str r4, [r5, #60]
	ldr r4, [r12, #608]
	str r4, [r5, #64]
	ldr r4, [r12, #612]
	str r4, [r5, #68]
	ldr r4, [r12, #544]
	str r4, [r12, #472]
	ldr r4, [r12, #548]
	str r4, [r12, #476]
	ldr r4, [r12, #552]
	str r4, [r12, #480]
	ldr r4, [r12, #556]
	str r4, [r12, #484]
	ldr r4, [r12, #560]
	str r4, [r12, #488]
	ldr r4, [r12, #564]
	str r4, [r12, #492]
	ldr r4, [r12, #568]
	str r4, [r12, #496]
	ldr r4, [r12, #572]
	str r4, [r12, #500]
	ldr r4, [r12, #576]
	str r4, [r12, #504]
	ldr r4, [r12, #580]
	str r4, [r12, #508]
	ldr r4, [r12, #584]
	str r4, [r12, #512]
	ldr r4, [r12, #588]
	str r4, [r12, #516]
	ldr r4, [r12, #592]
	str r4, [r12, #520]
	ldr r4, [r12, #596]
	str r4, [r12, #524]
	ldr r4, [r12, #600]
	str r4, [r12, #528]
	ldr r4, [r12, #604]
	str r4, [r12, #532]
	ldr r4, [r12, #608]
	str r4, [r12, #536]
	ldr r4, [r12, #612]
	str r4, [r12, #540]
	add r11, r11, #1
	cmp r11, #15
	bne 21b
	ldr r4, [r12, #136]
	str r4, [r12, #400]
	ldr r4, [r12, #140]
	str r4, [r12, #404]
	ldr r4, [r12, #144]
	str r4, [r12, #408]
	ldr r4, [r12, #148]
	str r4, [r12, #412]
	ldr r4, [r12, #152]
	str r4, [r12, #416]
	ldr r4, [r12, #156]
	str r4, [r12, #420]
	ldr r4, [r12, #184]
	str r4, [r12, #424]
	ldr r4, [r12, #188]
	str r4, [r12, #428]
	ldr r4, [r12, #192]
	str r4, [r12, #432]
	ldr r4, [r12, #196]
	str r4, [r12, #436]
	ldr r4, [r12, #200]
	str r4, [r12, #440]
	ldr r4, [r12, #204]
	str r4, [r12, #444]
	ldr r4, [r12, #136]
	str r4, [r12, #448]
	ldr r4, [r12, #140]
	str r4, [r12, #452]
	ldr r4, [r12, #144]
	str r4, [r12, #456]
	ldr r4, [r12, #148]
	str r4, [r12, #460]
	ldr r4, [r12, #152]
	str r4, [r12, #464]
	ldr r4, [r12, #156]
	str r4, [r12, #468]
	mov r11, #48
22:
	sub r11, r11, #1
	mov r10, lr
	mov r0, r12
	movw r1, #472
	movw r2, #400
	movw r3, #448
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #616
	movw r2, #448
	movw r3, #448
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #496
	movw r2, #424
	movw r3, #616
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #520
	movw r2, #448
	movw r3, #136
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #616
	movw r2, #520
	movw r3, #520
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #640
	movw r2, #496
	movw r3, #496
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #640
	movw r2, #640
	movw r3, #640
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #664
	movw r2, #472
	movw r3, #640
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #688
	movw r2, #472
	movw r3, #616
	bl {vg_p192_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #544
	movw r2, #472
	movw r3, #616
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #688
	movw r2, #688
	movw r3, #544
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #544
	movw r2, #688
	movw r3, #688
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #688
	movw r2, #544
	movw r3, #688
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #664
	movw r2, #664
	movw r3, #664
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #592
	movw r2, #496
	movw r3, #520
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #592
	movw r2, #592
	movw r3, #592
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #544
	movw r2, #688
	movw r3, #688
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #544
	movw r2, #544
	movw r3, #664
	bl {vg_p192_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #544
	movw r2, #544
	movw r3, #664
	bl {vg_p192_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #568
	movw r2, #664
	movw r3, #544
	bl {vg_p192_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #568
	movw r2, #688
	movw r3, #568
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #640
	movw r2, #640
	movw r3, #640
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #640
	movw r2, #640
	movw r3, #640
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #568
	movw r2, #568
	movw r3, #640
	bl {vg_p192_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #616
	movw r2, #592
	movw r3, #592
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #640
	movw r2, #568
	movw r3, #568
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #640
	movw r2, #640
	movw r3, #640
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #664
	movw r2, #544
	movw r3, #640
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #688
	movw r2, #544
	movw r3, #616
	bl {vg_p192_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #472
	movw r2, #544
	movw r3, #616
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #688
	movw r2, #688
	movw r3, #472
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #472
	movw r2, #688
	movw r3, #688
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #688
	movw r2, #472
	movw r3, #688
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #664
	movw r2, #664
	movw r3, #664
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #520
	movw r2, #568
	movw r3, #592
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #520
	movw r2, #520
	movw r3, #520
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #472
	movw r2, #688
	movw r3, #688
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #472
	movw r2, #472
	movw r3, #664
	bl {vg_p192_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #472
	movw r2, #472
	movw r3, #664
	bl {vg_p192_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #496
	movw r2, #664
	movw r3, #472
	bl {vg_p192_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #496
	movw r2, #688
	movw r3, #496
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #640
	movw r2, #640
	movw r3, #640
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #640
	movw r2, #640
	movw r3, #640
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #496
	movw r2, #496
	movw r3, #640
	bl {vg_p192_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #616
	movw r2, #520
	movw r3, #520
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #640
	movw r2, #496
	movw r3, #496
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #640
	movw r2, #640
	movw r3, #640
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #664
	movw r2, #472
	movw r3, #640
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #688
	movw r2, #472
	movw r3, #616
	bl {vg_p192_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #544
	movw r2, #472
	movw r3, #616
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #688
	movw r2, #688
	movw r3, #544
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #544
	movw r2, #688
	movw r3, #688
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #688
	movw r2, #544
	movw r3, #688
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #664
	movw r2, #664
	movw r3, #664
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #592
	movw r2, #496
	movw r3, #520
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #592
	movw r2, #592
	movw r3, #592
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #544
	movw r2, #688
	movw r3, #688
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #544
	movw r2, #544
	movw r3, #664
	bl {vg_p192_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #544
	movw r2, #544
	movw r3, #664
	bl {vg_p192_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #568
	movw r2, #664
	movw r3, #544
	bl {vg_p192_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #568
	movw r2, #688
	movw r3, #568
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #640
	movw r2, #640
	movw r3, #640
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #640
	movw r2, #640
	movw r3, #640
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #568
	movw r2, #568
	movw r3, #640
	bl {vg_p192_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #616
	movw r2, #592
	movw r3, #592
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #640
	movw r2, #568
	movw r3, #568
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #640
	movw r2, #640
	movw r3, #640
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #664
	movw r2, #544
	movw r3, #640
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #688
	movw r2, #544
	movw r3, #616
	bl {vg_p192_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #472
	movw r2, #544
	movw r3, #616
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #688
	movw r2, #688
	movw r3, #472
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #472
	movw r2, #688
	movw r3, #688
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #688
	movw r2, #472
	movw r3, #688
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #664
	movw r2, #664
	movw r3, #664
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #520
	movw r2, #568
	movw r3, #592
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #520
	movw r2, #520
	movw r3, #520
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #472
	movw r2, #688
	movw r3, #688
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #472
	movw r2, #472
	movw r3, #664
	bl {vg_p192_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #472
	movw r2, #472
	movw r3, #664
	bl {vg_p192_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #496
	movw r2, #664
	movw r3, #472
	bl {vg_p192_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #496
	movw r2, #688
	movw r3, #496
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #640
	movw r2, #640
	movw r3, #640
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #640
	movw r2, #640
	movw r3, #640
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #496
	movw r2, #496
	movw r3, #640
	bl {vg_p192_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #400
	movw r2, #472
	movw r3, #520
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #616
	movw r2, #520
	movw r3, #520
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #448
	movw r2, #616
	movw r3, #520
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #424
	movw r2, #496
	movw r3, #136
	bl {vg_p192_add_mod_p}
	mov lr, r10
	ldr r5, [r12, #448]
	ldr r4, [r12, #452]
	orr r5, r5, r4
	ldr r4, [r12, #456]
	orr r5, r5, r4
	ldr r4, [r12, #460]
	orr r5, r5, r4
	ldr r4, [r12, #464]
	orr r5, r5, r4
	ldr r4, [r12, #468]
	orr r5, r5, r4
	mov r4, #0
	sub r4, r4, r5
	orr r4, r4, r5
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	mov r10, r5
	ldr r4, [r12, #184]
	ldr r5, [r12, #424]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #424]
	ldr r4, [r12, #188]
	ldr r5, [r12, #428]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #428]
	ldr r4, [r12, #192]
	ldr r5, [r12, #432]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #432]
	ldr r4, [r12, #196]
	ldr r5, [r12, #436]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #436]
	ldr r4, [r12, #200]
	ldr r5, [r12, #440]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #440]
	ldr r4, [r12, #204]
	ldr r5, [r12, #444]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #444]
	mov r4, #4
	mul r4, r4, r11
	add r4, r12, r4
	add r4, r4, #4096
	cmp r11, #47
	beq 23f
	mov r9, #0
	add r9, r9, r9
	ldrb r5, [r4, #3]
	add r9, r9, r5
	add r9, r9, r9
	ldrb r5, [r4, #2]
	add r9, r9, r5
	add r9, r9, r9
	ldrb r5, [r4, #1]
	add r9, r9, r5
	add r9, r9, r9
	ldrb r5, [r4, #0]
	add r9, r9, r5
	b 24f
23:
	mov r9, #0
	add r9, r9, r9
	ldrb r5, [r4, #3]
	add r9, r9, r5
	add r9, r9, r9
	ldrb r5, [r4, #2]
	add r9, r9, r5
	add r9, r9, r9
	ldrb r5, [r4, #1]
	add r9, r9, r5
	add r9, r9, r9
	ldrb r5, [r4, #0]
	add r9, r9, r5
24:
	movw r8, #4672
	add r8, r12, r8
	mov r7, #0
25:
	eor r10, r9, r7
	sub r10, r10, #1
	lsr r10, r10, #31
	mov r5, #0
	sub r10, r5, r10
	ldr r4, [r12, #544]
	ldr r5, [r8, #0]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #544]
	ldr r4, [r12, #548]
	ldr r5, [r8, #4]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #548]
	ldr r4, [r12, #552]
	ldr r5, [r8, #8]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #552]
	ldr r4, [r12, #556]
	ldr r5, [r8, #12]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #556]
	ldr r4, [r12, #560]
	ldr r5, [r8, #16]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #560]
	ldr r4, [r12, #564]
	ldr r5, [r8, #20]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #564]
	ldr r4, [r12, #568]
	ldr r5, [r8, #24]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #568]
	ldr r4, [r12, #572]
	ldr r5, [r8, #28]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #572]
	ldr r4, [r12, #576]
	ldr r5, [r8, #32]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #576]
	ldr r4, [r12, #580]
	ldr r5, [r8, #36]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #580]
	ldr r4, [r12, #584]
	ldr r5, [r8, #40]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #584]
	ldr r4, [r12, #588]
	ldr r5, [r8, #44]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #588]
	ldr r4, [r12, #592]
	ldr r5, [r8, #48]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #592]
	ldr r4, [r12, #596]
	ldr r5, [r8, #52]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #596]
	ldr r4, [r12, #600]
	ldr r5, [r8, #56]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #600]
	ldr r4, [r12, #604]
	ldr r5, [r8, #60]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #604]
	ldr r4, [r12, #608]
	ldr r5, [r8, #64]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #608]
	ldr r4, [r12, #612]
	ldr r5, [r8, #68]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #612]
	add r8, r8, #72
	add r7, r7, #1
	cmp r7, #16
	bne 25b
	mov r10, lr
	mov r0, r12
	movw r1, #616
	movw r2, #400
	movw r3, #544
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #640
	movw r2, #424
	movw r3, #568
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #664
	movw r2, #448
	movw r3, #592
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #688
	movw r2, #400
	movw r3, #424
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #712
	movw r2, #544
	movw r3, #568
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #688
	movw r2, #688
	movw r3, #712
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #712
	movw r2, #616
	movw r3, #640
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #688
	movw r2, #688
	movw r3, #712
	bl {vg_p192_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #712
	movw r2, #400
	movw r3, #448
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #736
	movw r2, #544
	movw r3, #592
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #712
	movw r2, #712
	movw r3, #736
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #736
	movw r2, #616
	movw r3, #664
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #712
	movw r2, #712
	movw r3, #736
	bl {vg_p192_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #736
	movw r2, #424
	movw r3, #448
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #472
	movw r2, #568
	movw r3, #592
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #736
	movw r2, #736
	movw r3, #472
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #472
	movw r2, #640
	movw r3, #664
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #736
	movw r2, #736
	movw r3, #472
	bl {vg_p192_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #520
	movw r2, #208
	movw r3, #712
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #472
	movw r2, #232
	movw r3, #664
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #520
	movw r2, #472
	movw r3, #520
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #472
	movw r2, #640
	movw r3, #520
	bl {vg_p192_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #520
	movw r2, #640
	movw r3, #520
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #496
	movw r2, #472
	movw r3, #520
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #640
	movw r2, #616
	movw r3, #616
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #640
	movw r2, #640
	movw r3, #616
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #664
	movw r2, #208
	movw r3, #664
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #712
	movw r2, #232
	movw r3, #712
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #640
	movw r2, #640
	movw r3, #664
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #664
	movw r2, #616
	movw r3, #664
	bl {vg_p192_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #664
	movw r2, #208
	movw r3, #664
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #712
	movw r2, #712
	movw r3, #664
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #616
	movw r2, #640
	movw r3, #712
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #496
	movw r2, #496
	movw r3, #616
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #616
	movw r2, #736
	movw r3, #712
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #472
	movw r2, #688
	movw r3, #472
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #472
	movw r2, #472
	movw r3, #616
	bl {vg_p192_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #616
	movw r2, #688
	movw r3, #640
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #520
	movw r2, #736
	movw r3, #520
	bl {vg_p192_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #520
	movw r2, #520
	movw r3, #616
	bl {vg_p192_add_mod_p}
	mov lr, r10
	ldr r4, [r12, #472]
	str r4, [r12, #400]
	ldr r4, [r12, #476]
	str r4, [r12, #404]
	ldr r4, [r12, #480]
	str r4, [r12, #408]
	ldr r4, [r12, #484]
	str r4, [r12, #412]
	ldr r4, [r12, #488]
	str r4, [r12, #416]
	ldr r4, [r12, #492]
	str r4, [r12, #420]
	ldr r4, [r12, #496]
	str r4, [r12, #424]
	ldr r4, [r12, #500]
	str r4, [r12, #428]
	ldr r4, [r12, #504]
	str r4, [r12, #432]
	ldr r4, [r12, #508]
	str r4, [r12, #436]
	ldr r4, [r12, #512]
	str r4, [r12, #440]
	ldr r4, [r12, #516]
	str r4, [r12, #444]
	ldr r4, [r12, #520]
	str r4, [r12, #448]
	ldr r4, [r12, #524]
	str r4, [r12, #452]
	ldr r4, [r12, #528]
	str r4, [r12, #456]
	ldr r4, [r12, #532]
	str r4, [r12, #460]
	ldr r4, [r12, #536]
	str r4, [r12, #464]
	ldr r4, [r12, #540]
	str r4, [r12, #468]
	cmp r11, #0
	bne 22b
	mov r10, lr
	ldr r4, [r12, #1144]
	ldr r5, [r12, #1148]
	ldr r6, [r12, #1152]
	ldr r7, [r12, #1156]
	ldr r8, [r12, #1160]
	ldr r9, [r12, #1164]
	ldr r11, [r12, #1172]
	ldr lr, [r12, #1176]
	bx lr
