// The functions of `src/internal/vg_p224_mul_umaal.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p224_mul_umaal:
	mov r12, r0
	str r4, [r12, #1504]
	str r5, [r12, #1508]
	str r6, [r12, #1512]
	str r7, [r12, #1516]
	str r8, [r12, #1520]
	str r9, [r12, #1524]
	str r11, [r12, #1532]
	str lr, [r12, #1536]
	mov lr, r10
	mov r11, #32
20:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #1056]
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
	movw r5, #4864
	add r5, r12, r5
	ldr r4, [r12, #160]
	str r4, [r5, #0]
	ldr r4, [r12, #164]
	str r4, [r5, #4]
	ldr r4, [r12, #168]
	str r4, [r5, #8]
	ldr r4, [r12, #172]
	str r4, [r5, #12]
	ldr r4, [r12, #176]
	str r4, [r5, #16]
	ldr r4, [r12, #180]
	str r4, [r5, #20]
	ldr r4, [r12, #184]
	str r4, [r5, #24]
	ldr r4, [r12, #188]
	str r4, [r5, #28]
	ldr r4, [r12, #224]
	str r4, [r5, #32]
	ldr r4, [r12, #228]
	str r4, [r5, #36]
	ldr r4, [r12, #232]
	str r4, [r5, #40]
	ldr r4, [r12, #236]
	str r4, [r5, #44]
	ldr r4, [r12, #240]
	str r4, [r5, #48]
	ldr r4, [r12, #244]
	str r4, [r5, #52]
	ldr r4, [r12, #248]
	str r4, [r5, #56]
	ldr r4, [r12, #252]
	str r4, [r5, #60]
	ldr r4, [r12, #160]
	str r4, [r5, #64]
	ldr r4, [r12, #164]
	str r4, [r5, #68]
	ldr r4, [r12, #168]
	str r4, [r5, #72]
	ldr r4, [r12, #172]
	str r4, [r5, #76]
	ldr r4, [r12, #176]
	str r4, [r5, #80]
	ldr r4, [r12, #180]
	str r4, [r5, #84]
	ldr r4, [r12, #184]
	str r4, [r5, #88]
	ldr r4, [r12, #188]
	str r4, [r5, #92]
	ldr r4, [r12, #512]
	str r4, [r5, #96]
	ldr r4, [r12, #516]
	str r4, [r5, #100]
	ldr r4, [r12, #520]
	str r4, [r5, #104]
	ldr r4, [r12, #524]
	str r4, [r5, #108]
	ldr r4, [r12, #528]
	str r4, [r5, #112]
	ldr r4, [r12, #532]
	str r4, [r5, #116]
	ldr r4, [r12, #536]
	str r4, [r5, #120]
	ldr r4, [r12, #540]
	str r4, [r5, #124]
	ldr r4, [r12, #544]
	str r4, [r5, #128]
	ldr r4, [r12, #548]
	str r4, [r5, #132]
	ldr r4, [r12, #552]
	str r4, [r5, #136]
	ldr r4, [r12, #556]
	str r4, [r5, #140]
	ldr r4, [r12, #560]
	str r4, [r5, #144]
	ldr r4, [r12, #564]
	str r4, [r5, #148]
	ldr r4, [r12, #568]
	str r4, [r5, #152]
	ldr r4, [r12, #572]
	str r4, [r5, #156]
	ldr r4, [r12, #224]
	str r4, [r5, #160]
	ldr r4, [r12, #228]
	str r4, [r5, #164]
	ldr r4, [r12, #232]
	str r4, [r5, #168]
	ldr r4, [r12, #236]
	str r4, [r5, #172]
	ldr r4, [r12, #240]
	str r4, [r5, #176]
	ldr r4, [r12, #244]
	str r4, [r5, #180]
	ldr r4, [r12, #248]
	str r4, [r5, #184]
	ldr r4, [r12, #252]
	str r4, [r5, #188]
	ldr r4, [r12, #512]
	str r4, [r12, #608]
	ldr r4, [r12, #516]
	str r4, [r12, #612]
	ldr r4, [r12, #520]
	str r4, [r12, #616]
	ldr r4, [r12, #524]
	str r4, [r12, #620]
	ldr r4, [r12, #528]
	str r4, [r12, #624]
	ldr r4, [r12, #532]
	str r4, [r12, #628]
	ldr r4, [r12, #536]
	str r4, [r12, #632]
	ldr r4, [r12, #540]
	str r4, [r12, #636]
	ldr r4, [r12, #544]
	str r4, [r12, #640]
	ldr r4, [r12, #548]
	str r4, [r12, #644]
	ldr r4, [r12, #552]
	str r4, [r12, #648]
	ldr r4, [r12, #556]
	str r4, [r12, #652]
	ldr r4, [r12, #560]
	str r4, [r12, #656]
	ldr r4, [r12, #564]
	str r4, [r12, #660]
	ldr r4, [r12, #568]
	str r4, [r12, #664]
	ldr r4, [r12, #572]
	str r4, [r12, #668]
	ldr r4, [r12, #224]
	str r4, [r12, #672]
	ldr r4, [r12, #228]
	str r4, [r12, #676]
	ldr r4, [r12, #232]
	str r4, [r12, #680]
	ldr r4, [r12, #236]
	str r4, [r12, #684]
	ldr r4, [r12, #240]
	str r4, [r12, #688]
	ldr r4, [r12, #244]
	str r4, [r12, #692]
	ldr r4, [r12, #248]
	str r4, [r12, #696]
	ldr r4, [r12, #252]
	str r4, [r12, #700]
	mov r11, #1
21:
	mov r10, lr
	mov r0, r12
	movw r1, #800
	movw r2, #608
	movw r3, #512
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #832
	movw r2, #640
	movw r3, #544
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #864
	movw r2, #672
	movw r3, #224
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #896
	movw r2, #608
	movw r3, #640
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #928
	movw r2, #512
	movw r3, #544
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #896
	movw r2, #896
	movw r3, #928
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #928
	movw r2, #800
	movw r3, #832
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #896
	movw r2, #896
	movw r3, #928
	bl {vg_p224_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #928
	movw r2, #608
	movw r3, #672
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #960
	movw r2, #512
	movw r3, #224
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #928
	movw r2, #928
	movw r3, #960
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #960
	movw r2, #800
	movw r3, #864
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #928
	movw r2, #928
	movw r3, #960
	bl {vg_p224_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #960
	movw r2, #640
	movw r3, #672
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #704
	movw r2, #544
	movw r3, #224
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #960
	movw r2, #960
	movw r3, #704
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #704
	movw r2, #832
	movw r3, #864
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #960
	movw r2, #960
	movw r3, #704
	bl {vg_p224_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #768
	movw r2, #256
	movw r3, #928
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #704
	movw r2, #288
	movw r3, #864
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #768
	movw r2, #704
	movw r3, #768
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #704
	movw r2, #832
	movw r3, #768
	bl {vg_p224_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #768
	movw r2, #832
	movw r3, #768
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #736
	movw r2, #704
	movw r3, #768
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #832
	movw r2, #800
	movw r3, #800
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #832
	movw r2, #832
	movw r3, #800
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #864
	movw r2, #256
	movw r3, #864
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #928
	movw r2, #288
	movw r3, #928
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #832
	movw r2, #832
	movw r3, #864
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #864
	movw r2, #800
	movw r3, #864
	bl {vg_p224_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #864
	movw r2, #256
	movw r3, #864
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #928
	movw r2, #928
	movw r3, #864
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #800
	movw r2, #832
	movw r3, #928
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #736
	movw r2, #736
	movw r3, #800
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #800
	movw r2, #960
	movw r3, #928
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #704
	movw r2, #896
	movw r3, #704
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #704
	movw r2, #704
	movw r3, #800
	bl {vg_p224_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #800
	movw r2, #896
	movw r3, #832
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #768
	movw r2, #960
	movw r3, #768
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #768
	movw r2, #768
	movw r3, #800
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r4, #96
	mul r4, r4, r11
	movw r5, #4960
	add r5, r12, r5
	add r5, r5, r4
	ldr r4, [r12, #704]
	str r4, [r5, #0]
	ldr r4, [r12, #708]
	str r4, [r5, #4]
	ldr r4, [r12, #712]
	str r4, [r5, #8]
	ldr r4, [r12, #716]
	str r4, [r5, #12]
	ldr r4, [r12, #720]
	str r4, [r5, #16]
	ldr r4, [r12, #724]
	str r4, [r5, #20]
	ldr r4, [r12, #728]
	str r4, [r5, #24]
	ldr r4, [r12, #732]
	str r4, [r5, #28]
	ldr r4, [r12, #736]
	str r4, [r5, #32]
	ldr r4, [r12, #740]
	str r4, [r5, #36]
	ldr r4, [r12, #744]
	str r4, [r5, #40]
	ldr r4, [r12, #748]
	str r4, [r5, #44]
	ldr r4, [r12, #752]
	str r4, [r5, #48]
	ldr r4, [r12, #756]
	str r4, [r5, #52]
	ldr r4, [r12, #760]
	str r4, [r5, #56]
	ldr r4, [r12, #764]
	str r4, [r5, #60]
	ldr r4, [r12, #768]
	str r4, [r5, #64]
	ldr r4, [r12, #772]
	str r4, [r5, #68]
	ldr r4, [r12, #776]
	str r4, [r5, #72]
	ldr r4, [r12, #780]
	str r4, [r5, #76]
	ldr r4, [r12, #784]
	str r4, [r5, #80]
	ldr r4, [r12, #788]
	str r4, [r5, #84]
	ldr r4, [r12, #792]
	str r4, [r5, #88]
	ldr r4, [r12, #796]
	str r4, [r5, #92]
	ldr r4, [r12, #704]
	str r4, [r12, #608]
	ldr r4, [r12, #708]
	str r4, [r12, #612]
	ldr r4, [r12, #712]
	str r4, [r12, #616]
	ldr r4, [r12, #716]
	str r4, [r12, #620]
	ldr r4, [r12, #720]
	str r4, [r12, #624]
	ldr r4, [r12, #724]
	str r4, [r12, #628]
	ldr r4, [r12, #728]
	str r4, [r12, #632]
	ldr r4, [r12, #732]
	str r4, [r12, #636]
	ldr r4, [r12, #736]
	str r4, [r12, #640]
	ldr r4, [r12, #740]
	str r4, [r12, #644]
	ldr r4, [r12, #744]
	str r4, [r12, #648]
	ldr r4, [r12, #748]
	str r4, [r12, #652]
	ldr r4, [r12, #752]
	str r4, [r12, #656]
	ldr r4, [r12, #756]
	str r4, [r12, #660]
	ldr r4, [r12, #760]
	str r4, [r12, #664]
	ldr r4, [r12, #764]
	str r4, [r12, #668]
	ldr r4, [r12, #768]
	str r4, [r12, #672]
	ldr r4, [r12, #772]
	str r4, [r12, #676]
	ldr r4, [r12, #776]
	str r4, [r12, #680]
	ldr r4, [r12, #780]
	str r4, [r12, #684]
	ldr r4, [r12, #784]
	str r4, [r12, #688]
	ldr r4, [r12, #788]
	str r4, [r12, #692]
	ldr r4, [r12, #792]
	str r4, [r12, #696]
	ldr r4, [r12, #796]
	str r4, [r12, #700]
	add r11, r11, #1
	cmp r11, #15
	bne 21b
	ldr r4, [r12, #160]
	str r4, [r12, #512]
	ldr r4, [r12, #164]
	str r4, [r12, #516]
	ldr r4, [r12, #168]
	str r4, [r12, #520]
	ldr r4, [r12, #172]
	str r4, [r12, #524]
	ldr r4, [r12, #176]
	str r4, [r12, #528]
	ldr r4, [r12, #180]
	str r4, [r12, #532]
	ldr r4, [r12, #184]
	str r4, [r12, #536]
	ldr r4, [r12, #188]
	str r4, [r12, #540]
	ldr r4, [r12, #224]
	str r4, [r12, #544]
	ldr r4, [r12, #228]
	str r4, [r12, #548]
	ldr r4, [r12, #232]
	str r4, [r12, #552]
	ldr r4, [r12, #236]
	str r4, [r12, #556]
	ldr r4, [r12, #240]
	str r4, [r12, #560]
	ldr r4, [r12, #244]
	str r4, [r12, #564]
	ldr r4, [r12, #248]
	str r4, [r12, #568]
	ldr r4, [r12, #252]
	str r4, [r12, #572]
	ldr r4, [r12, #160]
	str r4, [r12, #576]
	ldr r4, [r12, #164]
	str r4, [r12, #580]
	ldr r4, [r12, #168]
	str r4, [r12, #584]
	ldr r4, [r12, #172]
	str r4, [r12, #588]
	ldr r4, [r12, #176]
	str r4, [r12, #592]
	ldr r4, [r12, #180]
	str r4, [r12, #596]
	ldr r4, [r12, #184]
	str r4, [r12, #600]
	ldr r4, [r12, #188]
	str r4, [r12, #604]
	mov r11, #56
22:
	sub r11, r11, #1
	mov r10, lr
	mov r0, r12
	movw r1, #608
	movw r2, #512
	movw r3, #576
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #800
	movw r2, #576
	movw r3, #576
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #640
	movw r2, #544
	movw r3, #800
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #672
	movw r2, #576
	movw r3, #160
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #800
	movw r2, #672
	movw r3, #672
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #832
	movw r2, #640
	movw r3, #640
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #832
	movw r2, #832
	movw r3, #832
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #864
	movw r2, #608
	movw r3, #832
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #896
	movw r2, #608
	movw r3, #800
	bl {vg_p224_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #704
	movw r2, #608
	movw r3, #800
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #896
	movw r2, #896
	movw r3, #704
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #704
	movw r2, #896
	movw r3, #896
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #896
	movw r2, #704
	movw r3, #896
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #864
	movw r2, #864
	movw r3, #864
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #768
	movw r2, #640
	movw r3, #672
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #768
	movw r2, #768
	movw r3, #768
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #704
	movw r2, #896
	movw r3, #896
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #704
	movw r2, #704
	movw r3, #864
	bl {vg_p224_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #704
	movw r2, #704
	movw r3, #864
	bl {vg_p224_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #736
	movw r2, #864
	movw r3, #704
	bl {vg_p224_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #736
	movw r2, #896
	movw r3, #736
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #832
	movw r2, #832
	movw r3, #832
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #832
	movw r2, #832
	movw r3, #832
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #736
	movw r2, #736
	movw r3, #832
	bl {vg_p224_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #800
	movw r2, #768
	movw r3, #768
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #832
	movw r2, #736
	movw r3, #736
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #832
	movw r2, #832
	movw r3, #832
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #864
	movw r2, #704
	movw r3, #832
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #896
	movw r2, #704
	movw r3, #800
	bl {vg_p224_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #608
	movw r2, #704
	movw r3, #800
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #896
	movw r2, #896
	movw r3, #608
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #608
	movw r2, #896
	movw r3, #896
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #896
	movw r2, #608
	movw r3, #896
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #864
	movw r2, #864
	movw r3, #864
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #672
	movw r2, #736
	movw r3, #768
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #672
	movw r2, #672
	movw r3, #672
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #608
	movw r2, #896
	movw r3, #896
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #608
	movw r2, #608
	movw r3, #864
	bl {vg_p224_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #608
	movw r2, #608
	movw r3, #864
	bl {vg_p224_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #640
	movw r2, #864
	movw r3, #608
	bl {vg_p224_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #640
	movw r2, #896
	movw r3, #640
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #832
	movw r2, #832
	movw r3, #832
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #832
	movw r2, #832
	movw r3, #832
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #640
	movw r2, #640
	movw r3, #832
	bl {vg_p224_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #800
	movw r2, #672
	movw r3, #672
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #832
	movw r2, #640
	movw r3, #640
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #832
	movw r2, #832
	movw r3, #832
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #864
	movw r2, #608
	movw r3, #832
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #896
	movw r2, #608
	movw r3, #800
	bl {vg_p224_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #704
	movw r2, #608
	movw r3, #800
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #896
	movw r2, #896
	movw r3, #704
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #704
	movw r2, #896
	movw r3, #896
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #896
	movw r2, #704
	movw r3, #896
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #864
	movw r2, #864
	movw r3, #864
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #768
	movw r2, #640
	movw r3, #672
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #768
	movw r2, #768
	movw r3, #768
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #704
	movw r2, #896
	movw r3, #896
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #704
	movw r2, #704
	movw r3, #864
	bl {vg_p224_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #704
	movw r2, #704
	movw r3, #864
	bl {vg_p224_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #736
	movw r2, #864
	movw r3, #704
	bl {vg_p224_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #736
	movw r2, #896
	movw r3, #736
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #832
	movw r2, #832
	movw r3, #832
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #832
	movw r2, #832
	movw r3, #832
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #736
	movw r2, #736
	movw r3, #832
	bl {vg_p224_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #800
	movw r2, #768
	movw r3, #768
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #832
	movw r2, #736
	movw r3, #736
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #832
	movw r2, #832
	movw r3, #832
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #864
	movw r2, #704
	movw r3, #832
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #896
	movw r2, #704
	movw r3, #800
	bl {vg_p224_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #608
	movw r2, #704
	movw r3, #800
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #896
	movw r2, #896
	movw r3, #608
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #608
	movw r2, #896
	movw r3, #896
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #896
	movw r2, #608
	movw r3, #896
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #864
	movw r2, #864
	movw r3, #864
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #672
	movw r2, #736
	movw r3, #768
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #672
	movw r2, #672
	movw r3, #672
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #608
	movw r2, #896
	movw r3, #896
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #608
	movw r2, #608
	movw r3, #864
	bl {vg_p224_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #608
	movw r2, #608
	movw r3, #864
	bl {vg_p224_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #640
	movw r2, #864
	movw r3, #608
	bl {vg_p224_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #640
	movw r2, #896
	movw r3, #640
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #832
	movw r2, #832
	movw r3, #832
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #832
	movw r2, #832
	movw r3, #832
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #640
	movw r2, #640
	movw r3, #832
	bl {vg_p224_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #512
	movw r2, #608
	movw r3, #672
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #800
	movw r2, #672
	movw r3, #672
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #576
	movw r2, #800
	movw r3, #672
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #544
	movw r2, #640
	movw r3, #160
	bl {vg_p224_add_mod_p}
	mov lr, r10
	ldr r5, [r12, #576]
	ldr r4, [r12, #580]
	orr r5, r5, r4
	ldr r4, [r12, #584]
	orr r5, r5, r4
	ldr r4, [r12, #588]
	orr r5, r5, r4
	ldr r4, [r12, #592]
	orr r5, r5, r4
	ldr r4, [r12, #596]
	orr r5, r5, r4
	ldr r4, [r12, #600]
	orr r5, r5, r4
	ldr r4, [r12, #604]
	orr r5, r5, r4
	mov r4, #0
	sub r4, r4, r5
	orr r4, r4, r5
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	mov r10, r5
	ldr r4, [r12, #224]
	ldr r5, [r12, #544]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #544]
	ldr r4, [r12, #228]
	ldr r5, [r12, #548]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #548]
	ldr r4, [r12, #232]
	ldr r5, [r12, #552]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #552]
	ldr r4, [r12, #236]
	ldr r5, [r12, #556]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #556]
	ldr r4, [r12, #240]
	ldr r5, [r12, #560]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #560]
	ldr r4, [r12, #244]
	ldr r5, [r12, #564]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #564]
	ldr r4, [r12, #248]
	ldr r5, [r12, #568]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #568]
	ldr r4, [r12, #252]
	ldr r5, [r12, #572]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #572]
	mov r4, #4
	mul r4, r4, r11
	add r4, r12, r4
	add r4, r4, #4096
	cmp r11, #55
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
	movw r8, #4864
	add r8, r12, r8
	mov r7, #0
25:
	eor r10, r9, r7
	sub r10, r10, #1
	lsr r10, r10, #31
	mov r5, #0
	sub r10, r5, r10
	ldr r4, [r12, #704]
	ldr r5, [r8, #0]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #704]
	ldr r4, [r12, #708]
	ldr r5, [r8, #4]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #708]
	ldr r4, [r12, #712]
	ldr r5, [r8, #8]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #712]
	ldr r4, [r12, #716]
	ldr r5, [r8, #12]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #716]
	ldr r4, [r12, #720]
	ldr r5, [r8, #16]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #720]
	ldr r4, [r12, #724]
	ldr r5, [r8, #20]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #724]
	ldr r4, [r12, #728]
	ldr r5, [r8, #24]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #728]
	ldr r4, [r12, #732]
	ldr r5, [r8, #28]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #732]
	ldr r4, [r12, #736]
	ldr r5, [r8, #32]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #736]
	ldr r4, [r12, #740]
	ldr r5, [r8, #36]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #740]
	ldr r4, [r12, #744]
	ldr r5, [r8, #40]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #744]
	ldr r4, [r12, #748]
	ldr r5, [r8, #44]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #748]
	ldr r4, [r12, #752]
	ldr r5, [r8, #48]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #752]
	ldr r4, [r12, #756]
	ldr r5, [r8, #52]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #756]
	ldr r4, [r12, #760]
	ldr r5, [r8, #56]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #760]
	ldr r4, [r12, #764]
	ldr r5, [r8, #60]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #764]
	ldr r4, [r12, #768]
	ldr r5, [r8, #64]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #768]
	ldr r4, [r12, #772]
	ldr r5, [r8, #68]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #772]
	ldr r4, [r12, #776]
	ldr r5, [r8, #72]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #776]
	ldr r4, [r12, #780]
	ldr r5, [r8, #76]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #780]
	ldr r4, [r12, #784]
	ldr r5, [r8, #80]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #784]
	ldr r4, [r12, #788]
	ldr r5, [r8, #84]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #788]
	ldr r4, [r12, #792]
	ldr r5, [r8, #88]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #792]
	ldr r4, [r12, #796]
	ldr r5, [r8, #92]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #796]
	add r8, r8, #96
	add r7, r7, #1
	cmp r7, #16
	bne 25b
	mov r10, lr
	mov r0, r12
	movw r1, #800
	movw r2, #512
	movw r3, #704
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #832
	movw r2, #544
	movw r3, #736
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #864
	movw r2, #576
	movw r3, #768
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #896
	movw r2, #512
	movw r3, #544
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #928
	movw r2, #704
	movw r3, #736
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #896
	movw r2, #896
	movw r3, #928
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #928
	movw r2, #800
	movw r3, #832
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #896
	movw r2, #896
	movw r3, #928
	bl {vg_p224_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #928
	movw r2, #512
	movw r3, #576
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #960
	movw r2, #704
	movw r3, #768
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #928
	movw r2, #928
	movw r3, #960
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #960
	movw r2, #800
	movw r3, #864
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #928
	movw r2, #928
	movw r3, #960
	bl {vg_p224_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #960
	movw r2, #544
	movw r3, #576
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #608
	movw r2, #736
	movw r3, #768
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #960
	movw r2, #960
	movw r3, #608
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #608
	movw r2, #832
	movw r3, #864
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #960
	movw r2, #960
	movw r3, #608
	bl {vg_p224_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #672
	movw r2, #256
	movw r3, #928
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #608
	movw r2, #288
	movw r3, #864
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #672
	movw r2, #608
	movw r3, #672
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #608
	movw r2, #832
	movw r3, #672
	bl {vg_p224_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #672
	movw r2, #832
	movw r3, #672
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #640
	movw r2, #608
	movw r3, #672
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #832
	movw r2, #800
	movw r3, #800
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #832
	movw r2, #832
	movw r3, #800
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #864
	movw r2, #256
	movw r3, #864
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #928
	movw r2, #288
	movw r3, #928
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #832
	movw r2, #832
	movw r3, #864
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #864
	movw r2, #800
	movw r3, #864
	bl {vg_p224_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #864
	movw r2, #256
	movw r3, #864
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #928
	movw r2, #928
	movw r3, #864
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #800
	movw r2, #832
	movw r3, #928
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #640
	movw r2, #640
	movw r3, #800
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #800
	movw r2, #960
	movw r3, #928
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #608
	movw r2, #896
	movw r3, #608
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #608
	movw r2, #608
	movw r3, #800
	bl {vg_p224_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #800
	movw r2, #896
	movw r3, #832
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #672
	movw r2, #960
	movw r3, #672
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #672
	movw r2, #672
	movw r3, #800
	bl {vg_p224_add_mod_p}
	mov lr, r10
	ldr r4, [r12, #608]
	str r4, [r12, #512]
	ldr r4, [r12, #612]
	str r4, [r12, #516]
	ldr r4, [r12, #616]
	str r4, [r12, #520]
	ldr r4, [r12, #620]
	str r4, [r12, #524]
	ldr r4, [r12, #624]
	str r4, [r12, #528]
	ldr r4, [r12, #628]
	str r4, [r12, #532]
	ldr r4, [r12, #632]
	str r4, [r12, #536]
	ldr r4, [r12, #636]
	str r4, [r12, #540]
	ldr r4, [r12, #640]
	str r4, [r12, #544]
	ldr r4, [r12, #644]
	str r4, [r12, #548]
	ldr r4, [r12, #648]
	str r4, [r12, #552]
	ldr r4, [r12, #652]
	str r4, [r12, #556]
	ldr r4, [r12, #656]
	str r4, [r12, #560]
	ldr r4, [r12, #660]
	str r4, [r12, #564]
	ldr r4, [r12, #664]
	str r4, [r12, #568]
	ldr r4, [r12, #668]
	str r4, [r12, #572]
	ldr r4, [r12, #672]
	str r4, [r12, #576]
	ldr r4, [r12, #676]
	str r4, [r12, #580]
	ldr r4, [r12, #680]
	str r4, [r12, #584]
	ldr r4, [r12, #684]
	str r4, [r12, #588]
	ldr r4, [r12, #688]
	str r4, [r12, #592]
	ldr r4, [r12, #692]
	str r4, [r12, #596]
	ldr r4, [r12, #696]
	str r4, [r12, #600]
	ldr r4, [r12, #700]
	str r4, [r12, #604]
	cmp r11, #0
	bne 22b
	mov r10, lr
	ldr r4, [r12, #1504]
	ldr r5, [r12, #1508]
	ldr r6, [r12, #1512]
	ldr r7, [r12, #1516]
	ldr r8, [r12, #1520]
	ldr r9, [r12, #1524]
	ldr r11, [r12, #1532]
	ldr lr, [r12, #1536]
	bx lr
