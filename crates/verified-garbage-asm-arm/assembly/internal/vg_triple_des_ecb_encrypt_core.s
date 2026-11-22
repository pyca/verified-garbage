// The functions of `src/internal/vg_triple_des_ecb_encrypt_core.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_triple_des_ecb_encrypt_core:
	sub sp, sp, #1024
	add r3, sp, #0
	cmp r2, #0
	beq 20f
	str r4, [r3, #320]
	str r5, [r3, #324]
	str r6, [r3, #328]
	str r7, [r3, #332]
	str r8, [r3, #336]
	str r9, [r3, #340]
	str r10, [r3, #344]
	str r11, [r3, #348]
	str lr, [r3, #352]
22:
	lsr r12, r2, #5
	cmp r12, #0
	beq 23f
	mov r12, #32
	b 24f
23:
	mov r12, r2
24:
	add r4, r3, #32
	mov r5, r1
	mov r6, r12
25:
	ldr r7, [r5, #0]
	str r7, [r4, #0]
	ldr r7, [r5, #4]
	str r7, [r4, #128]
	add r5, r5, #8
	add r4, r4, #4
	subs r6, r6, #1
	bne 25b
	str r0, [r3, #304]
	str r1, [r3, #308]
	str r2, [r3, #312]
	str r12, [r3, #316]
	movw r0, #65535
	movt r0, #0
	movw r1, #255
	movt r1, #255
	ldr r4, [r3, #32]
	ldr r5, [r3, #64]
	ldr r6, [r3, #96]
	ldr r7, [r3, #128]
	eor r12, r6, r4, lsr #16
	and r12, r12, r0
	eor r6, r6, r12
	eor r4, r4, r12, ror #16
	eor r12, r7, r5, lsr #16
	and r12, r12, r0
	eor r7, r7, r12
	eor r5, r5, r12, ror #16
	eor r12, r5, r4, lsr #8
	and r12, r12, r1
	eor r5, r5, r12
	eor r4, r4, r12, ror #24
	eor r12, r7, r6, lsr #8
	and r12, r12, r1
	eor r7, r7, r12
	eor r6, r6, r12, ror #24
	str r4, [r3, #32]
	str r5, [r3, #64]
	str r6, [r3, #96]
	str r7, [r3, #128]
	ldr r4, [r3, #36]
	ldr r5, [r3, #68]
	ldr r6, [r3, #100]
	ldr r7, [r3, #132]
	eor r12, r6, r4, lsr #16
	and r12, r12, r0
	eor r6, r6, r12
	eor r4, r4, r12, ror #16
	eor r12, r7, r5, lsr #16
	and r12, r12, r0
	eor r7, r7, r12
	eor r5, r5, r12, ror #16
	eor r12, r5, r4, lsr #8
	and r12, r12, r1
	eor r5, r5, r12
	eor r4, r4, r12, ror #24
	eor r12, r7, r6, lsr #8
	and r12, r12, r1
	eor r7, r7, r12
	eor r6, r6, r12, ror #24
	str r4, [r3, #36]
	str r5, [r3, #68]
	str r6, [r3, #100]
	str r7, [r3, #132]
	ldr r4, [r3, #40]
	ldr r5, [r3, #72]
	ldr r6, [r3, #104]
	ldr r7, [r3, #136]
	eor r12, r6, r4, lsr #16
	and r12, r12, r0
	eor r6, r6, r12
	eor r4, r4, r12, ror #16
	eor r12, r7, r5, lsr #16
	and r12, r12, r0
	eor r7, r7, r12
	eor r5, r5, r12, ror #16
	eor r12, r5, r4, lsr #8
	and r12, r12, r1
	eor r5, r5, r12
	eor r4, r4, r12, ror #24
	eor r12, r7, r6, lsr #8
	and r12, r12, r1
	eor r7, r7, r12
	eor r6, r6, r12, ror #24
	str r4, [r3, #40]
	str r5, [r3, #72]
	str r6, [r3, #104]
	str r7, [r3, #136]
	ldr r4, [r3, #44]
	ldr r5, [r3, #76]
	ldr r6, [r3, #108]
	ldr r7, [r3, #140]
	eor r12, r6, r4, lsr #16
	and r12, r12, r0
	eor r6, r6, r12
	eor r4, r4, r12, ror #16
	eor r12, r7, r5, lsr #16
	and r12, r12, r0
	eor r7, r7, r12
	eor r5, r5, r12, ror #16
	eor r12, r5, r4, lsr #8
	and r12, r12, r1
	eor r5, r5, r12
	eor r4, r4, r12, ror #24
	eor r12, r7, r6, lsr #8
	and r12, r12, r1
	eor r7, r7, r12
	eor r6, r6, r12, ror #24
	str r4, [r3, #44]
	str r5, [r3, #76]
	str r6, [r3, #108]
	str r7, [r3, #140]
	ldr r4, [r3, #48]
	ldr r5, [r3, #80]
	ldr r6, [r3, #112]
	ldr r7, [r3, #144]
	eor r12, r6, r4, lsr #16
	and r12, r12, r0
	eor r6, r6, r12
	eor r4, r4, r12, ror #16
	eor r12, r7, r5, lsr #16
	and r12, r12, r0
	eor r7, r7, r12
	eor r5, r5, r12, ror #16
	eor r12, r5, r4, lsr #8
	and r12, r12, r1
	eor r5, r5, r12
	eor r4, r4, r12, ror #24
	eor r12, r7, r6, lsr #8
	and r12, r12, r1
	eor r7, r7, r12
	eor r6, r6, r12, ror #24
	str r4, [r3, #48]
	str r5, [r3, #80]
	str r6, [r3, #112]
	str r7, [r3, #144]
	ldr r4, [r3, #52]
	ldr r5, [r3, #84]
	ldr r6, [r3, #116]
	ldr r7, [r3, #148]
	eor r12, r6, r4, lsr #16
	and r12, r12, r0
	eor r6, r6, r12
	eor r4, r4, r12, ror #16
	eor r12, r7, r5, lsr #16
	and r12, r12, r0
	eor r7, r7, r12
	eor r5, r5, r12, ror #16
	eor r12, r5, r4, lsr #8
	and r12, r12, r1
	eor r5, r5, r12
	eor r4, r4, r12, ror #24
	eor r12, r7, r6, lsr #8
	and r12, r12, r1
	eor r7, r7, r12
	eor r6, r6, r12, ror #24
	str r4, [r3, #52]
	str r5, [r3, #84]
	str r6, [r3, #116]
	str r7, [r3, #148]
	ldr r4, [r3, #56]
	ldr r5, [r3, #88]
	ldr r6, [r3, #120]
	ldr r7, [r3, #152]
	eor r12, r6, r4, lsr #16
	and r12, r12, r0
	eor r6, r6, r12
	eor r4, r4, r12, ror #16
	eor r12, r7, r5, lsr #16
	and r12, r12, r0
	eor r7, r7, r12
	eor r5, r5, r12, ror #16
	eor r12, r5, r4, lsr #8
	and r12, r12, r1
	eor r5, r5, r12
	eor r4, r4, r12, ror #24
	eor r12, r7, r6, lsr #8
	and r12, r12, r1
	eor r7, r7, r12
	eor r6, r6, r12, ror #24
	str r4, [r3, #56]
	str r5, [r3, #88]
	str r6, [r3, #120]
	str r7, [r3, #152]
	ldr r4, [r3, #60]
	ldr r5, [r3, #92]
	ldr r6, [r3, #124]
	ldr r7, [r3, #156]
	eor r12, r6, r4, lsr #16
	and r12, r12, r0
	eor r6, r6, r12
	eor r4, r4, r12, ror #16
	eor r12, r7, r5, lsr #16
	and r12, r12, r0
	eor r7, r7, r12
	eor r5, r5, r12, ror #16
	eor r12, r5, r4, lsr #8
	and r12, r12, r1
	eor r5, r5, r12
	eor r4, r4, r12, ror #24
	eor r12, r7, r6, lsr #8
	and r12, r12, r1
	eor r7, r7, r12
	eor r6, r6, r12, ror #24
	str r4, [r3, #60]
	str r5, [r3, #92]
	str r6, [r3, #124]
	str r7, [r3, #156]
	ldr r4, [r3, #160]
	ldr r5, [r3, #192]
	ldr r6, [r3, #224]
	ldr r7, [r3, #256]
	eor r12, r6, r4, lsr #16
	and r12, r12, r0
	eor r6, r6, r12
	eor r4, r4, r12, ror #16
	eor r12, r7, r5, lsr #16
	and r12, r12, r0
	eor r7, r7, r12
	eor r5, r5, r12, ror #16
	eor r12, r5, r4, lsr #8
	and r12, r12, r1
	eor r5, r5, r12
	eor r4, r4, r12, ror #24
	eor r12, r7, r6, lsr #8
	and r12, r12, r1
	eor r7, r7, r12
	eor r6, r6, r12, ror #24
	str r4, [r3, #160]
	str r5, [r3, #192]
	str r6, [r3, #224]
	str r7, [r3, #256]
	ldr r4, [r3, #164]
	ldr r5, [r3, #196]
	ldr r6, [r3, #228]
	ldr r7, [r3, #260]
	eor r12, r6, r4, lsr #16
	and r12, r12, r0
	eor r6, r6, r12
	eor r4, r4, r12, ror #16
	eor r12, r7, r5, lsr #16
	and r12, r12, r0
	eor r7, r7, r12
	eor r5, r5, r12, ror #16
	eor r12, r5, r4, lsr #8
	and r12, r12, r1
	eor r5, r5, r12
	eor r4, r4, r12, ror #24
	eor r12, r7, r6, lsr #8
	and r12, r12, r1
	eor r7, r7, r12
	eor r6, r6, r12, ror #24
	str r4, [r3, #164]
	str r5, [r3, #196]
	str r6, [r3, #228]
	str r7, [r3, #260]
	ldr r4, [r3, #168]
	ldr r5, [r3, #200]
	ldr r6, [r3, #232]
	ldr r7, [r3, #264]
	eor r12, r6, r4, lsr #16
	and r12, r12, r0
	eor r6, r6, r12
	eor r4, r4, r12, ror #16
	eor r12, r7, r5, lsr #16
	and r12, r12, r0
	eor r7, r7, r12
	eor r5, r5, r12, ror #16
	eor r12, r5, r4, lsr #8
	and r12, r12, r1
	eor r5, r5, r12
	eor r4, r4, r12, ror #24
	eor r12, r7, r6, lsr #8
	and r12, r12, r1
	eor r7, r7, r12
	eor r6, r6, r12, ror #24
	str r4, [r3, #168]
	str r5, [r3, #200]
	str r6, [r3, #232]
	str r7, [r3, #264]
	ldr r4, [r3, #172]
	ldr r5, [r3, #204]
	ldr r6, [r3, #236]
	ldr r7, [r3, #268]
	eor r12, r6, r4, lsr #16
	and r12, r12, r0
	eor r6, r6, r12
	eor r4, r4, r12, ror #16
	eor r12, r7, r5, lsr #16
	and r12, r12, r0
	eor r7, r7, r12
	eor r5, r5, r12, ror #16
	eor r12, r5, r4, lsr #8
	and r12, r12, r1
	eor r5, r5, r12
	eor r4, r4, r12, ror #24
	eor r12, r7, r6, lsr #8
	and r12, r12, r1
	eor r7, r7, r12
	eor r6, r6, r12, ror #24
	str r4, [r3, #172]
	str r5, [r3, #204]
	str r6, [r3, #236]
	str r7, [r3, #268]
	ldr r4, [r3, #176]
	ldr r5, [r3, #208]
	ldr r6, [r3, #240]
	ldr r7, [r3, #272]
	eor r12, r6, r4, lsr #16
	and r12, r12, r0
	eor r6, r6, r12
	eor r4, r4, r12, ror #16
	eor r12, r7, r5, lsr #16
	and r12, r12, r0
	eor r7, r7, r12
	eor r5, r5, r12, ror #16
	eor r12, r5, r4, lsr #8
	and r12, r12, r1
	eor r5, r5, r12
	eor r4, r4, r12, ror #24
	eor r12, r7, r6, lsr #8
	and r12, r12, r1
	eor r7, r7, r12
	eor r6, r6, r12, ror #24
	str r4, [r3, #176]
	str r5, [r3, #208]
	str r6, [r3, #240]
	str r7, [r3, #272]
	ldr r4, [r3, #180]
	ldr r5, [r3, #212]
	ldr r6, [r3, #244]
	ldr r7, [r3, #276]
	eor r12, r6, r4, lsr #16
	and r12, r12, r0
	eor r6, r6, r12
	eor r4, r4, r12, ror #16
	eor r12, r7, r5, lsr #16
	and r12, r12, r0
	eor r7, r7, r12
	eor r5, r5, r12, ror #16
	eor r12, r5, r4, lsr #8
	and r12, r12, r1
	eor r5, r5, r12
	eor r4, r4, r12, ror #24
	eor r12, r7, r6, lsr #8
	and r12, r12, r1
	eor r7, r7, r12
	eor r6, r6, r12, ror #24
	str r4, [r3, #180]
	str r5, [r3, #212]
	str r6, [r3, #244]
	str r7, [r3, #276]
	ldr r4, [r3, #184]
	ldr r5, [r3, #216]
	ldr r6, [r3, #248]
	ldr r7, [r3, #280]
	eor r12, r6, r4, lsr #16
	and r12, r12, r0
	eor r6, r6, r12
	eor r4, r4, r12, ror #16
	eor r12, r7, r5, lsr #16
	and r12, r12, r0
	eor r7, r7, r12
	eor r5, r5, r12, ror #16
	eor r12, r5, r4, lsr #8
	and r12, r12, r1
	eor r5, r5, r12
	eor r4, r4, r12, ror #24
	eor r12, r7, r6, lsr #8
	and r12, r12, r1
	eor r7, r7, r12
	eor r6, r6, r12, ror #24
	str r4, [r3, #184]
	str r5, [r3, #216]
	str r6, [r3, #248]
	str r7, [r3, #280]
	ldr r4, [r3, #188]
	ldr r5, [r3, #220]
	ldr r6, [r3, #252]
	ldr r7, [r3, #284]
	eor r12, r6, r4, lsr #16
	and r12, r12, r0
	eor r6, r6, r12
	eor r4, r4, r12, ror #16
	eor r12, r7, r5, lsr #16
	and r12, r12, r0
	eor r7, r7, r12
	eor r5, r5, r12, ror #16
	eor r12, r5, r4, lsr #8
	and r12, r12, r1
	eor r5, r5, r12
	eor r4, r4, r12, ror #24
	eor r12, r7, r6, lsr #8
	and r12, r12, r1
	eor r7, r7, r12
	eor r6, r6, r12, ror #24
	str r4, [r3, #188]
	str r5, [r3, #220]
	str r6, [r3, #252]
	str r7, [r3, #284]
	movw r0, #3855
	movt r0, #3855
	movw r1, #13107
	movt r1, #13107
	movw r2, #21845
	movt r2, #21845
	ldr r4, [r3, #32]
	ldr r5, [r3, #36]
	ldr r6, [r3, #40]
	ldr r7, [r3, #44]
	ldr r8, [r3, #48]
	ldr r9, [r3, #52]
	ldr r10, [r3, #56]
	ldr r11, [r3, #60]
	eor r12, r8, r4, lsr #4
	and r12, r12, r0
	eor r8, r8, r12
	eor r4, r4, r12, ror #28
	eor r12, r9, r5, lsr #4
	and r12, r12, r0
	eor r9, r9, r12
	eor r5, r5, r12, ror #28
	eor r12, r10, r6, lsr #4
	and r12, r12, r0
	eor r10, r10, r12
	eor r6, r6, r12, ror #28
	eor r12, r11, r7, lsr #4
	and r12, r12, r0
	eor r11, r11, r12
	eor r7, r7, r12, ror #28
	eor r12, r6, r4, lsr #2
	and r12, r12, r1
	eor r6, r6, r12
	eor r4, r4, r12, ror #30
	eor r12, r7, r5, lsr #2
	and r12, r12, r1
	eor r7, r7, r12
	eor r5, r5, r12, ror #30
	eor r12, r10, r8, lsr #2
	and r12, r12, r1
	eor r10, r10, r12
	eor r8, r8, r12, ror #30
	eor r12, r11, r9, lsr #2
	and r12, r12, r1
	eor r11, r11, r12
	eor r9, r9, r12, ror #30
	eor r12, r5, r4, lsr #1
	and r12, r12, r2
	eor r5, r5, r12
	eor r4, r4, r12, ror #31
	eor r12, r7, r6, lsr #1
	and r12, r12, r2
	eor r7, r7, r12
	eor r6, r6, r12, ror #31
	eor r12, r9, r8, lsr #1
	and r12, r12, r2
	eor r9, r9, r12
	eor r8, r8, r12, ror #31
	eor r12, r11, r10, lsr #1
	and r12, r12, r2
	eor r11, r11, r12
	eor r10, r10, r12, ror #31
	str r4, [r3, #32]
	str r5, [r3, #36]
	str r6, [r3, #40]
	str r7, [r3, #44]
	str r8, [r3, #48]
	str r9, [r3, #52]
	str r10, [r3, #56]
	str r11, [r3, #60]
	ldr r4, [r3, #64]
	ldr r5, [r3, #68]
	ldr r6, [r3, #72]
	ldr r7, [r3, #76]
	ldr r8, [r3, #80]
	ldr r9, [r3, #84]
	ldr r10, [r3, #88]
	ldr r11, [r3, #92]
	eor r12, r8, r4, lsr #4
	and r12, r12, r0
	eor r8, r8, r12
	eor r4, r4, r12, ror #28
	eor r12, r9, r5, lsr #4
	and r12, r12, r0
	eor r9, r9, r12
	eor r5, r5, r12, ror #28
	eor r12, r10, r6, lsr #4
	and r12, r12, r0
	eor r10, r10, r12
	eor r6, r6, r12, ror #28
	eor r12, r11, r7, lsr #4
	and r12, r12, r0
	eor r11, r11, r12
	eor r7, r7, r12, ror #28
	eor r12, r6, r4, lsr #2
	and r12, r12, r1
	eor r6, r6, r12
	eor r4, r4, r12, ror #30
	eor r12, r7, r5, lsr #2
	and r12, r12, r1
	eor r7, r7, r12
	eor r5, r5, r12, ror #30
	eor r12, r10, r8, lsr #2
	and r12, r12, r1
	eor r10, r10, r12
	eor r8, r8, r12, ror #30
	eor r12, r11, r9, lsr #2
	and r12, r12, r1
	eor r11, r11, r12
	eor r9, r9, r12, ror #30
	eor r12, r5, r4, lsr #1
	and r12, r12, r2
	eor r5, r5, r12
	eor r4, r4, r12, ror #31
	eor r12, r7, r6, lsr #1
	and r12, r12, r2
	eor r7, r7, r12
	eor r6, r6, r12, ror #31
	eor r12, r9, r8, lsr #1
	and r12, r12, r2
	eor r9, r9, r12
	eor r8, r8, r12, ror #31
	eor r12, r11, r10, lsr #1
	and r12, r12, r2
	eor r11, r11, r12
	eor r10, r10, r12, ror #31
	str r4, [r3, #64]
	str r5, [r3, #68]
	str r6, [r3, #72]
	str r7, [r3, #76]
	str r8, [r3, #80]
	str r9, [r3, #84]
	str r10, [r3, #88]
	str r11, [r3, #92]
	ldr r4, [r3, #96]
	ldr r5, [r3, #100]
	ldr r6, [r3, #104]
	ldr r7, [r3, #108]
	ldr r8, [r3, #112]
	ldr r9, [r3, #116]
	ldr r10, [r3, #120]
	ldr r11, [r3, #124]
	eor r12, r8, r4, lsr #4
	and r12, r12, r0
	eor r8, r8, r12
	eor r4, r4, r12, ror #28
	eor r12, r9, r5, lsr #4
	and r12, r12, r0
	eor r9, r9, r12
	eor r5, r5, r12, ror #28
	eor r12, r10, r6, lsr #4
	and r12, r12, r0
	eor r10, r10, r12
	eor r6, r6, r12, ror #28
	eor r12, r11, r7, lsr #4
	and r12, r12, r0
	eor r11, r11, r12
	eor r7, r7, r12, ror #28
	eor r12, r6, r4, lsr #2
	and r12, r12, r1
	eor r6, r6, r12
	eor r4, r4, r12, ror #30
	eor r12, r7, r5, lsr #2
	and r12, r12, r1
	eor r7, r7, r12
	eor r5, r5, r12, ror #30
	eor r12, r10, r8, lsr #2
	and r12, r12, r1
	eor r10, r10, r12
	eor r8, r8, r12, ror #30
	eor r12, r11, r9, lsr #2
	and r12, r12, r1
	eor r11, r11, r12
	eor r9, r9, r12, ror #30
	eor r12, r5, r4, lsr #1
	and r12, r12, r2
	eor r5, r5, r12
	eor r4, r4, r12, ror #31
	eor r12, r7, r6, lsr #1
	and r12, r12, r2
	eor r7, r7, r12
	eor r6, r6, r12, ror #31
	eor r12, r9, r8, lsr #1
	and r12, r12, r2
	eor r9, r9, r12
	eor r8, r8, r12, ror #31
	eor r12, r11, r10, lsr #1
	and r12, r12, r2
	eor r11, r11, r12
	eor r10, r10, r12, ror #31
	str r4, [r3, #96]
	str r5, [r3, #100]
	str r6, [r3, #104]
	str r7, [r3, #108]
	str r8, [r3, #112]
	str r9, [r3, #116]
	str r10, [r3, #120]
	str r11, [r3, #124]
	ldr r4, [r3, #128]
	ldr r5, [r3, #132]
	ldr r6, [r3, #136]
	ldr r7, [r3, #140]
	ldr r8, [r3, #144]
	ldr r9, [r3, #148]
	ldr r10, [r3, #152]
	ldr r11, [r3, #156]
	eor r12, r8, r4, lsr #4
	and r12, r12, r0
	eor r8, r8, r12
	eor r4, r4, r12, ror #28
	eor r12, r9, r5, lsr #4
	and r12, r12, r0
	eor r9, r9, r12
	eor r5, r5, r12, ror #28
	eor r12, r10, r6, lsr #4
	and r12, r12, r0
	eor r10, r10, r12
	eor r6, r6, r12, ror #28
	eor r12, r11, r7, lsr #4
	and r12, r12, r0
	eor r11, r11, r12
	eor r7, r7, r12, ror #28
	eor r12, r6, r4, lsr #2
	and r12, r12, r1
	eor r6, r6, r12
	eor r4, r4, r12, ror #30
	eor r12, r7, r5, lsr #2
	and r12, r12, r1
	eor r7, r7, r12
	eor r5, r5, r12, ror #30
	eor r12, r10, r8, lsr #2
	and r12, r12, r1
	eor r10, r10, r12
	eor r8, r8, r12, ror #30
	eor r12, r11, r9, lsr #2
	and r12, r12, r1
	eor r11, r11, r12
	eor r9, r9, r12, ror #30
	eor r12, r5, r4, lsr #1
	and r12, r12, r2
	eor r5, r5, r12
	eor r4, r4, r12, ror #31
	eor r12, r7, r6, lsr #1
	and r12, r12, r2
	eor r7, r7, r12
	eor r6, r6, r12, ror #31
	eor r12, r9, r8, lsr #1
	and r12, r12, r2
	eor r9, r9, r12
	eor r8, r8, r12, ror #31
	eor r12, r11, r10, lsr #1
	and r12, r12, r2
	eor r11, r11, r12
	eor r10, r10, r12, ror #31
	str r4, [r3, #128]
	str r5, [r3, #132]
	str r6, [r3, #136]
	str r7, [r3, #140]
	str r8, [r3, #144]
	str r9, [r3, #148]
	str r10, [r3, #152]
	str r11, [r3, #156]
	ldr r4, [r3, #160]
	ldr r5, [r3, #164]
	ldr r6, [r3, #168]
	ldr r7, [r3, #172]
	ldr r8, [r3, #176]
	ldr r9, [r3, #180]
	ldr r10, [r3, #184]
	ldr r11, [r3, #188]
	eor r12, r8, r4, lsr #4
	and r12, r12, r0
	eor r8, r8, r12
	eor r4, r4, r12, ror #28
	eor r12, r9, r5, lsr #4
	and r12, r12, r0
	eor r9, r9, r12
	eor r5, r5, r12, ror #28
	eor r12, r10, r6, lsr #4
	and r12, r12, r0
	eor r10, r10, r12
	eor r6, r6, r12, ror #28
	eor r12, r11, r7, lsr #4
	and r12, r12, r0
	eor r11, r11, r12
	eor r7, r7, r12, ror #28
	eor r12, r6, r4, lsr #2
	and r12, r12, r1
	eor r6, r6, r12
	eor r4, r4, r12, ror #30
	eor r12, r7, r5, lsr #2
	and r12, r12, r1
	eor r7, r7, r12
	eor r5, r5, r12, ror #30
	eor r12, r10, r8, lsr #2
	and r12, r12, r1
	eor r10, r10, r12
	eor r8, r8, r12, ror #30
	eor r12, r11, r9, lsr #2
	and r12, r12, r1
	eor r11, r11, r12
	eor r9, r9, r12, ror #30
	eor r12, r5, r4, lsr #1
	and r12, r12, r2
	eor r5, r5, r12
	eor r4, r4, r12, ror #31
	eor r12, r7, r6, lsr #1
	and r12, r12, r2
	eor r7, r7, r12
	eor r6, r6, r12, ror #31
	eor r12, r9, r8, lsr #1
	and r12, r12, r2
	eor r9, r9, r12
	eor r8, r8, r12, ror #31
	eor r12, r11, r10, lsr #1
	and r12, r12, r2
	eor r11, r11, r12
	eor r10, r10, r12, ror #31
	str r4, [r3, #160]
	str r5, [r3, #164]
	str r6, [r3, #168]
	str r7, [r3, #172]
	str r8, [r3, #176]
	str r9, [r3, #180]
	str r10, [r3, #184]
	str r11, [r3, #188]
	ldr r4, [r3, #192]
	ldr r5, [r3, #196]
	ldr r6, [r3, #200]
	ldr r7, [r3, #204]
	ldr r8, [r3, #208]
	ldr r9, [r3, #212]
	ldr r10, [r3, #216]
	ldr r11, [r3, #220]
	eor r12, r8, r4, lsr #4
	and r12, r12, r0
	eor r8, r8, r12
	eor r4, r4, r12, ror #28
	eor r12, r9, r5, lsr #4
	and r12, r12, r0
	eor r9, r9, r12
	eor r5, r5, r12, ror #28
	eor r12, r10, r6, lsr #4
	and r12, r12, r0
	eor r10, r10, r12
	eor r6, r6, r12, ror #28
	eor r12, r11, r7, lsr #4
	and r12, r12, r0
	eor r11, r11, r12
	eor r7, r7, r12, ror #28
	eor r12, r6, r4, lsr #2
	and r12, r12, r1
	eor r6, r6, r12
	eor r4, r4, r12, ror #30
	eor r12, r7, r5, lsr #2
	and r12, r12, r1
	eor r7, r7, r12
	eor r5, r5, r12, ror #30
	eor r12, r10, r8, lsr #2
	and r12, r12, r1
	eor r10, r10, r12
	eor r8, r8, r12, ror #30
	eor r12, r11, r9, lsr #2
	and r12, r12, r1
	eor r11, r11, r12
	eor r9, r9, r12, ror #30
	eor r12, r5, r4, lsr #1
	and r12, r12, r2
	eor r5, r5, r12
	eor r4, r4, r12, ror #31
	eor r12, r7, r6, lsr #1
	and r12, r12, r2
	eor r7, r7, r12
	eor r6, r6, r12, ror #31
	eor r12, r9, r8, lsr #1
	and r12, r12, r2
	eor r9, r9, r12
	eor r8, r8, r12, ror #31
	eor r12, r11, r10, lsr #1
	and r12, r12, r2
	eor r11, r11, r12
	eor r10, r10, r12, ror #31
	str r4, [r3, #192]
	str r5, [r3, #196]
	str r6, [r3, #200]
	str r7, [r3, #204]
	str r8, [r3, #208]
	str r9, [r3, #212]
	str r10, [r3, #216]
	str r11, [r3, #220]
	ldr r4, [r3, #224]
	ldr r5, [r3, #228]
	ldr r6, [r3, #232]
	ldr r7, [r3, #236]
	ldr r8, [r3, #240]
	ldr r9, [r3, #244]
	ldr r10, [r3, #248]
	ldr r11, [r3, #252]
	eor r12, r8, r4, lsr #4
	and r12, r12, r0
	eor r8, r8, r12
	eor r4, r4, r12, ror #28
	eor r12, r9, r5, lsr #4
	and r12, r12, r0
	eor r9, r9, r12
	eor r5, r5, r12, ror #28
	eor r12, r10, r6, lsr #4
	and r12, r12, r0
	eor r10, r10, r12
	eor r6, r6, r12, ror #28
	eor r12, r11, r7, lsr #4
	and r12, r12, r0
	eor r11, r11, r12
	eor r7, r7, r12, ror #28
	eor r12, r6, r4, lsr #2
	and r12, r12, r1
	eor r6, r6, r12
	eor r4, r4, r12, ror #30
	eor r12, r7, r5, lsr #2
	and r12, r12, r1
	eor r7, r7, r12
	eor r5, r5, r12, ror #30
	eor r12, r10, r8, lsr #2
	and r12, r12, r1
	eor r10, r10, r12
	eor r8, r8, r12, ror #30
	eor r12, r11, r9, lsr #2
	and r12, r12, r1
	eor r11, r11, r12
	eor r9, r9, r12, ror #30
	eor r12, r5, r4, lsr #1
	and r12, r12, r2
	eor r5, r5, r12
	eor r4, r4, r12, ror #31
	eor r12, r7, r6, lsr #1
	and r12, r12, r2
	eor r7, r7, r12
	eor r6, r6, r12, ror #31
	eor r12, r9, r8, lsr #1
	and r12, r12, r2
	eor r9, r9, r12
	eor r8, r8, r12, ror #31
	eor r12, r11, r10, lsr #1
	and r12, r12, r2
	eor r11, r11, r12
	eor r10, r10, r12, ror #31
	str r4, [r3, #224]
	str r5, [r3, #228]
	str r6, [r3, #232]
	str r7, [r3, #236]
	str r8, [r3, #240]
	str r9, [r3, #244]
	str r10, [r3, #248]
	str r11, [r3, #252]
	ldr r4, [r3, #256]
	ldr r5, [r3, #260]
	ldr r6, [r3, #264]
	ldr r7, [r3, #268]
	ldr r8, [r3, #272]
	ldr r9, [r3, #276]
	ldr r10, [r3, #280]
	ldr r11, [r3, #284]
	eor r12, r8, r4, lsr #4
	and r12, r12, r0
	eor r8, r8, r12
	eor r4, r4, r12, ror #28
	eor r12, r9, r5, lsr #4
	and r12, r12, r0
	eor r9, r9, r12
	eor r5, r5, r12, ror #28
	eor r12, r10, r6, lsr #4
	and r12, r12, r0
	eor r10, r10, r12
	eor r6, r6, r12, ror #28
	eor r12, r11, r7, lsr #4
	and r12, r12, r0
	eor r11, r11, r12
	eor r7, r7, r12, ror #28
	eor r12, r6, r4, lsr #2
	and r12, r12, r1
	eor r6, r6, r12
	eor r4, r4, r12, ror #30
	eor r12, r7, r5, lsr #2
	and r12, r12, r1
	eor r7, r7, r12
	eor r5, r5, r12, ror #30
	eor r12, r10, r8, lsr #2
	and r12, r12, r1
	eor r10, r10, r12
	eor r8, r8, r12, ror #30
	eor r12, r11, r9, lsr #2
	and r12, r12, r1
	eor r11, r11, r12
	eor r9, r9, r12, ror #30
	eor r12, r5, r4, lsr #1
	and r12, r12, r2
	eor r5, r5, r12
	eor r4, r4, r12, ror #31
	eor r12, r7, r6, lsr #1
	and r12, r12, r2
	eor r7, r7, r12
	eor r6, r6, r12, ror #31
	eor r12, r9, r8, lsr #1
	and r12, r12, r2
	eor r9, r9, r12
	eor r8, r8, r12, ror #31
	eor r12, r11, r10, lsr #1
	and r12, r12, r2
	eor r11, r11, r12
	eor r10, r10, r12, ror #31
	str r4, [r3, #256]
	str r5, [r3, #260]
	str r6, [r3, #264]
	str r7, [r3, #268]
	str r8, [r3, #272]
	str r9, [r3, #276]
	str r10, [r3, #280]
	str r11, [r3, #284]
	bl {vg_triple_des_passes_encrypt}
	movw r0, #65535
	movt r0, #0
	movw r1, #255
	movt r1, #255
	ldr r4, [r3, #32]
	ldr r5, [r3, #64]
	ldr r6, [r3, #96]
	ldr r7, [r3, #128]
	eor r12, r6, r4, lsr #16
	and r12, r12, r0
	eor r6, r6, r12
	eor r4, r4, r12, ror #16
	eor r12, r7, r5, lsr #16
	and r12, r12, r0
	eor r7, r7, r12
	eor r5, r5, r12, ror #16
	eor r12, r5, r4, lsr #8
	and r12, r12, r1
	eor r5, r5, r12
	eor r4, r4, r12, ror #24
	eor r12, r7, r6, lsr #8
	and r12, r12, r1
	eor r7, r7, r12
	eor r6, r6, r12, ror #24
	str r4, [r3, #32]
	str r5, [r3, #64]
	str r6, [r3, #96]
	str r7, [r3, #128]
	ldr r4, [r3, #36]
	ldr r5, [r3, #68]
	ldr r6, [r3, #100]
	ldr r7, [r3, #132]
	eor r12, r6, r4, lsr #16
	and r12, r12, r0
	eor r6, r6, r12
	eor r4, r4, r12, ror #16
	eor r12, r7, r5, lsr #16
	and r12, r12, r0
	eor r7, r7, r12
	eor r5, r5, r12, ror #16
	eor r12, r5, r4, lsr #8
	and r12, r12, r1
	eor r5, r5, r12
	eor r4, r4, r12, ror #24
	eor r12, r7, r6, lsr #8
	and r12, r12, r1
	eor r7, r7, r12
	eor r6, r6, r12, ror #24
	str r4, [r3, #36]
	str r5, [r3, #68]
	str r6, [r3, #100]
	str r7, [r3, #132]
	ldr r4, [r3, #40]
	ldr r5, [r3, #72]
	ldr r6, [r3, #104]
	ldr r7, [r3, #136]
	eor r12, r6, r4, lsr #16
	and r12, r12, r0
	eor r6, r6, r12
	eor r4, r4, r12, ror #16
	eor r12, r7, r5, lsr #16
	and r12, r12, r0
	eor r7, r7, r12
	eor r5, r5, r12, ror #16
	eor r12, r5, r4, lsr #8
	and r12, r12, r1
	eor r5, r5, r12
	eor r4, r4, r12, ror #24
	eor r12, r7, r6, lsr #8
	and r12, r12, r1
	eor r7, r7, r12
	eor r6, r6, r12, ror #24
	str r4, [r3, #40]
	str r5, [r3, #72]
	str r6, [r3, #104]
	str r7, [r3, #136]
	ldr r4, [r3, #44]
	ldr r5, [r3, #76]
	ldr r6, [r3, #108]
	ldr r7, [r3, #140]
	eor r12, r6, r4, lsr #16
	and r12, r12, r0
	eor r6, r6, r12
	eor r4, r4, r12, ror #16
	eor r12, r7, r5, lsr #16
	and r12, r12, r0
	eor r7, r7, r12
	eor r5, r5, r12, ror #16
	eor r12, r5, r4, lsr #8
	and r12, r12, r1
	eor r5, r5, r12
	eor r4, r4, r12, ror #24
	eor r12, r7, r6, lsr #8
	and r12, r12, r1
	eor r7, r7, r12
	eor r6, r6, r12, ror #24
	str r4, [r3, #44]
	str r5, [r3, #76]
	str r6, [r3, #108]
	str r7, [r3, #140]
	ldr r4, [r3, #48]
	ldr r5, [r3, #80]
	ldr r6, [r3, #112]
	ldr r7, [r3, #144]
	eor r12, r6, r4, lsr #16
	and r12, r12, r0
	eor r6, r6, r12
	eor r4, r4, r12, ror #16
	eor r12, r7, r5, lsr #16
	and r12, r12, r0
	eor r7, r7, r12
	eor r5, r5, r12, ror #16
	eor r12, r5, r4, lsr #8
	and r12, r12, r1
	eor r5, r5, r12
	eor r4, r4, r12, ror #24
	eor r12, r7, r6, lsr #8
	and r12, r12, r1
	eor r7, r7, r12
	eor r6, r6, r12, ror #24
	str r4, [r3, #48]
	str r5, [r3, #80]
	str r6, [r3, #112]
	str r7, [r3, #144]
	ldr r4, [r3, #52]
	ldr r5, [r3, #84]
	ldr r6, [r3, #116]
	ldr r7, [r3, #148]
	eor r12, r6, r4, lsr #16
	and r12, r12, r0
	eor r6, r6, r12
	eor r4, r4, r12, ror #16
	eor r12, r7, r5, lsr #16
	and r12, r12, r0
	eor r7, r7, r12
	eor r5, r5, r12, ror #16
	eor r12, r5, r4, lsr #8
	and r12, r12, r1
	eor r5, r5, r12
	eor r4, r4, r12, ror #24
	eor r12, r7, r6, lsr #8
	and r12, r12, r1
	eor r7, r7, r12
	eor r6, r6, r12, ror #24
	str r4, [r3, #52]
	str r5, [r3, #84]
	str r6, [r3, #116]
	str r7, [r3, #148]
	ldr r4, [r3, #56]
	ldr r5, [r3, #88]
	ldr r6, [r3, #120]
	ldr r7, [r3, #152]
	eor r12, r6, r4, lsr #16
	and r12, r12, r0
	eor r6, r6, r12
	eor r4, r4, r12, ror #16
	eor r12, r7, r5, lsr #16
	and r12, r12, r0
	eor r7, r7, r12
	eor r5, r5, r12, ror #16
	eor r12, r5, r4, lsr #8
	and r12, r12, r1
	eor r5, r5, r12
	eor r4, r4, r12, ror #24
	eor r12, r7, r6, lsr #8
	and r12, r12, r1
	eor r7, r7, r12
	eor r6, r6, r12, ror #24
	str r4, [r3, #56]
	str r5, [r3, #88]
	str r6, [r3, #120]
	str r7, [r3, #152]
	ldr r4, [r3, #60]
	ldr r5, [r3, #92]
	ldr r6, [r3, #124]
	ldr r7, [r3, #156]
	eor r12, r6, r4, lsr #16
	and r12, r12, r0
	eor r6, r6, r12
	eor r4, r4, r12, ror #16
	eor r12, r7, r5, lsr #16
	and r12, r12, r0
	eor r7, r7, r12
	eor r5, r5, r12, ror #16
	eor r12, r5, r4, lsr #8
	and r12, r12, r1
	eor r5, r5, r12
	eor r4, r4, r12, ror #24
	eor r12, r7, r6, lsr #8
	and r12, r12, r1
	eor r7, r7, r12
	eor r6, r6, r12, ror #24
	str r4, [r3, #60]
	str r5, [r3, #92]
	str r6, [r3, #124]
	str r7, [r3, #156]
	ldr r4, [r3, #160]
	ldr r5, [r3, #192]
	ldr r6, [r3, #224]
	ldr r7, [r3, #256]
	eor r12, r6, r4, lsr #16
	and r12, r12, r0
	eor r6, r6, r12
	eor r4, r4, r12, ror #16
	eor r12, r7, r5, lsr #16
	and r12, r12, r0
	eor r7, r7, r12
	eor r5, r5, r12, ror #16
	eor r12, r5, r4, lsr #8
	and r12, r12, r1
	eor r5, r5, r12
	eor r4, r4, r12, ror #24
	eor r12, r7, r6, lsr #8
	and r12, r12, r1
	eor r7, r7, r12
	eor r6, r6, r12, ror #24
	str r4, [r3, #160]
	str r5, [r3, #192]
	str r6, [r3, #224]
	str r7, [r3, #256]
	ldr r4, [r3, #164]
	ldr r5, [r3, #196]
	ldr r6, [r3, #228]
	ldr r7, [r3, #260]
	eor r12, r6, r4, lsr #16
	and r12, r12, r0
	eor r6, r6, r12
	eor r4, r4, r12, ror #16
	eor r12, r7, r5, lsr #16
	and r12, r12, r0
	eor r7, r7, r12
	eor r5, r5, r12, ror #16
	eor r12, r5, r4, lsr #8
	and r12, r12, r1
	eor r5, r5, r12
	eor r4, r4, r12, ror #24
	eor r12, r7, r6, lsr #8
	and r12, r12, r1
	eor r7, r7, r12
	eor r6, r6, r12, ror #24
	str r4, [r3, #164]
	str r5, [r3, #196]
	str r6, [r3, #228]
	str r7, [r3, #260]
	ldr r4, [r3, #168]
	ldr r5, [r3, #200]
	ldr r6, [r3, #232]
	ldr r7, [r3, #264]
	eor r12, r6, r4, lsr #16
	and r12, r12, r0
	eor r6, r6, r12
	eor r4, r4, r12, ror #16
	eor r12, r7, r5, lsr #16
	and r12, r12, r0
	eor r7, r7, r12
	eor r5, r5, r12, ror #16
	eor r12, r5, r4, lsr #8
	and r12, r12, r1
	eor r5, r5, r12
	eor r4, r4, r12, ror #24
	eor r12, r7, r6, lsr #8
	and r12, r12, r1
	eor r7, r7, r12
	eor r6, r6, r12, ror #24
	str r4, [r3, #168]
	str r5, [r3, #200]
	str r6, [r3, #232]
	str r7, [r3, #264]
	ldr r4, [r3, #172]
	ldr r5, [r3, #204]
	ldr r6, [r3, #236]
	ldr r7, [r3, #268]
	eor r12, r6, r4, lsr #16
	and r12, r12, r0
	eor r6, r6, r12
	eor r4, r4, r12, ror #16
	eor r12, r7, r5, lsr #16
	and r12, r12, r0
	eor r7, r7, r12
	eor r5, r5, r12, ror #16
	eor r12, r5, r4, lsr #8
	and r12, r12, r1
	eor r5, r5, r12
	eor r4, r4, r12, ror #24
	eor r12, r7, r6, lsr #8
	and r12, r12, r1
	eor r7, r7, r12
	eor r6, r6, r12, ror #24
	str r4, [r3, #172]
	str r5, [r3, #204]
	str r6, [r3, #236]
	str r7, [r3, #268]
	ldr r4, [r3, #176]
	ldr r5, [r3, #208]
	ldr r6, [r3, #240]
	ldr r7, [r3, #272]
	eor r12, r6, r4, lsr #16
	and r12, r12, r0
	eor r6, r6, r12
	eor r4, r4, r12, ror #16
	eor r12, r7, r5, lsr #16
	and r12, r12, r0
	eor r7, r7, r12
	eor r5, r5, r12, ror #16
	eor r12, r5, r4, lsr #8
	and r12, r12, r1
	eor r5, r5, r12
	eor r4, r4, r12, ror #24
	eor r12, r7, r6, lsr #8
	and r12, r12, r1
	eor r7, r7, r12
	eor r6, r6, r12, ror #24
	str r4, [r3, #176]
	str r5, [r3, #208]
	str r6, [r3, #240]
	str r7, [r3, #272]
	ldr r4, [r3, #180]
	ldr r5, [r3, #212]
	ldr r6, [r3, #244]
	ldr r7, [r3, #276]
	eor r12, r6, r4, lsr #16
	and r12, r12, r0
	eor r6, r6, r12
	eor r4, r4, r12, ror #16
	eor r12, r7, r5, lsr #16
	and r12, r12, r0
	eor r7, r7, r12
	eor r5, r5, r12, ror #16
	eor r12, r5, r4, lsr #8
	and r12, r12, r1
	eor r5, r5, r12
	eor r4, r4, r12, ror #24
	eor r12, r7, r6, lsr #8
	and r12, r12, r1
	eor r7, r7, r12
	eor r6, r6, r12, ror #24
	str r4, [r3, #180]
	str r5, [r3, #212]
	str r6, [r3, #244]
	str r7, [r3, #276]
	ldr r4, [r3, #184]
	ldr r5, [r3, #216]
	ldr r6, [r3, #248]
	ldr r7, [r3, #280]
	eor r12, r6, r4, lsr #16
	and r12, r12, r0
	eor r6, r6, r12
	eor r4, r4, r12, ror #16
	eor r12, r7, r5, lsr #16
	and r12, r12, r0
	eor r7, r7, r12
	eor r5, r5, r12, ror #16
	eor r12, r5, r4, lsr #8
	and r12, r12, r1
	eor r5, r5, r12
	eor r4, r4, r12, ror #24
	eor r12, r7, r6, lsr #8
	and r12, r12, r1
	eor r7, r7, r12
	eor r6, r6, r12, ror #24
	str r4, [r3, #184]
	str r5, [r3, #216]
	str r6, [r3, #248]
	str r7, [r3, #280]
	ldr r4, [r3, #188]
	ldr r5, [r3, #220]
	ldr r6, [r3, #252]
	ldr r7, [r3, #284]
	eor r12, r6, r4, lsr #16
	and r12, r12, r0
	eor r6, r6, r12
	eor r4, r4, r12, ror #16
	eor r12, r7, r5, lsr #16
	and r12, r12, r0
	eor r7, r7, r12
	eor r5, r5, r12, ror #16
	eor r12, r5, r4, lsr #8
	and r12, r12, r1
	eor r5, r5, r12
	eor r4, r4, r12, ror #24
	eor r12, r7, r6, lsr #8
	and r12, r12, r1
	eor r7, r7, r12
	eor r6, r6, r12, ror #24
	str r4, [r3, #188]
	str r5, [r3, #220]
	str r6, [r3, #252]
	str r7, [r3, #284]
	movw r0, #3855
	movt r0, #3855
	movw r1, #13107
	movt r1, #13107
	movw r2, #21845
	movt r2, #21845
	ldr r4, [r3, #32]
	ldr r5, [r3, #36]
	ldr r6, [r3, #40]
	ldr r7, [r3, #44]
	ldr r8, [r3, #48]
	ldr r9, [r3, #52]
	ldr r10, [r3, #56]
	ldr r11, [r3, #60]
	eor r12, r8, r4, lsr #4
	and r12, r12, r0
	eor r8, r8, r12
	eor r4, r4, r12, ror #28
	eor r12, r9, r5, lsr #4
	and r12, r12, r0
	eor r9, r9, r12
	eor r5, r5, r12, ror #28
	eor r12, r10, r6, lsr #4
	and r12, r12, r0
	eor r10, r10, r12
	eor r6, r6, r12, ror #28
	eor r12, r11, r7, lsr #4
	and r12, r12, r0
	eor r11, r11, r12
	eor r7, r7, r12, ror #28
	eor r12, r6, r4, lsr #2
	and r12, r12, r1
	eor r6, r6, r12
	eor r4, r4, r12, ror #30
	eor r12, r7, r5, lsr #2
	and r12, r12, r1
	eor r7, r7, r12
	eor r5, r5, r12, ror #30
	eor r12, r10, r8, lsr #2
	and r12, r12, r1
	eor r10, r10, r12
	eor r8, r8, r12, ror #30
	eor r12, r11, r9, lsr #2
	and r12, r12, r1
	eor r11, r11, r12
	eor r9, r9, r12, ror #30
	eor r12, r5, r4, lsr #1
	and r12, r12, r2
	eor r5, r5, r12
	eor r4, r4, r12, ror #31
	eor r12, r7, r6, lsr #1
	and r12, r12, r2
	eor r7, r7, r12
	eor r6, r6, r12, ror #31
	eor r12, r9, r8, lsr #1
	and r12, r12, r2
	eor r9, r9, r12
	eor r8, r8, r12, ror #31
	eor r12, r11, r10, lsr #1
	and r12, r12, r2
	eor r11, r11, r12
	eor r10, r10, r12, ror #31
	str r4, [r3, #32]
	str r5, [r3, #36]
	str r6, [r3, #40]
	str r7, [r3, #44]
	str r8, [r3, #48]
	str r9, [r3, #52]
	str r10, [r3, #56]
	str r11, [r3, #60]
	ldr r4, [r3, #64]
	ldr r5, [r3, #68]
	ldr r6, [r3, #72]
	ldr r7, [r3, #76]
	ldr r8, [r3, #80]
	ldr r9, [r3, #84]
	ldr r10, [r3, #88]
	ldr r11, [r3, #92]
	eor r12, r8, r4, lsr #4
	and r12, r12, r0
	eor r8, r8, r12
	eor r4, r4, r12, ror #28
	eor r12, r9, r5, lsr #4
	and r12, r12, r0
	eor r9, r9, r12
	eor r5, r5, r12, ror #28
	eor r12, r10, r6, lsr #4
	and r12, r12, r0
	eor r10, r10, r12
	eor r6, r6, r12, ror #28
	eor r12, r11, r7, lsr #4
	and r12, r12, r0
	eor r11, r11, r12
	eor r7, r7, r12, ror #28
	eor r12, r6, r4, lsr #2
	and r12, r12, r1
	eor r6, r6, r12
	eor r4, r4, r12, ror #30
	eor r12, r7, r5, lsr #2
	and r12, r12, r1
	eor r7, r7, r12
	eor r5, r5, r12, ror #30
	eor r12, r10, r8, lsr #2
	and r12, r12, r1
	eor r10, r10, r12
	eor r8, r8, r12, ror #30
	eor r12, r11, r9, lsr #2
	and r12, r12, r1
	eor r11, r11, r12
	eor r9, r9, r12, ror #30
	eor r12, r5, r4, lsr #1
	and r12, r12, r2
	eor r5, r5, r12
	eor r4, r4, r12, ror #31
	eor r12, r7, r6, lsr #1
	and r12, r12, r2
	eor r7, r7, r12
	eor r6, r6, r12, ror #31
	eor r12, r9, r8, lsr #1
	and r12, r12, r2
	eor r9, r9, r12
	eor r8, r8, r12, ror #31
	eor r12, r11, r10, lsr #1
	and r12, r12, r2
	eor r11, r11, r12
	eor r10, r10, r12, ror #31
	str r4, [r3, #64]
	str r5, [r3, #68]
	str r6, [r3, #72]
	str r7, [r3, #76]
	str r8, [r3, #80]
	str r9, [r3, #84]
	str r10, [r3, #88]
	str r11, [r3, #92]
	ldr r4, [r3, #96]
	ldr r5, [r3, #100]
	ldr r6, [r3, #104]
	ldr r7, [r3, #108]
	ldr r8, [r3, #112]
	ldr r9, [r3, #116]
	ldr r10, [r3, #120]
	ldr r11, [r3, #124]
	eor r12, r8, r4, lsr #4
	and r12, r12, r0
	eor r8, r8, r12
	eor r4, r4, r12, ror #28
	eor r12, r9, r5, lsr #4
	and r12, r12, r0
	eor r9, r9, r12
	eor r5, r5, r12, ror #28
	eor r12, r10, r6, lsr #4
	and r12, r12, r0
	eor r10, r10, r12
	eor r6, r6, r12, ror #28
	eor r12, r11, r7, lsr #4
	and r12, r12, r0
	eor r11, r11, r12
	eor r7, r7, r12, ror #28
	eor r12, r6, r4, lsr #2
	and r12, r12, r1
	eor r6, r6, r12
	eor r4, r4, r12, ror #30
	eor r12, r7, r5, lsr #2
	and r12, r12, r1
	eor r7, r7, r12
	eor r5, r5, r12, ror #30
	eor r12, r10, r8, lsr #2
	and r12, r12, r1
	eor r10, r10, r12
	eor r8, r8, r12, ror #30
	eor r12, r11, r9, lsr #2
	and r12, r12, r1
	eor r11, r11, r12
	eor r9, r9, r12, ror #30
	eor r12, r5, r4, lsr #1
	and r12, r12, r2
	eor r5, r5, r12
	eor r4, r4, r12, ror #31
	eor r12, r7, r6, lsr #1
	and r12, r12, r2
	eor r7, r7, r12
	eor r6, r6, r12, ror #31
	eor r12, r9, r8, lsr #1
	and r12, r12, r2
	eor r9, r9, r12
	eor r8, r8, r12, ror #31
	eor r12, r11, r10, lsr #1
	and r12, r12, r2
	eor r11, r11, r12
	eor r10, r10, r12, ror #31
	str r4, [r3, #96]
	str r5, [r3, #100]
	str r6, [r3, #104]
	str r7, [r3, #108]
	str r8, [r3, #112]
	str r9, [r3, #116]
	str r10, [r3, #120]
	str r11, [r3, #124]
	ldr r4, [r3, #128]
	ldr r5, [r3, #132]
	ldr r6, [r3, #136]
	ldr r7, [r3, #140]
	ldr r8, [r3, #144]
	ldr r9, [r3, #148]
	ldr r10, [r3, #152]
	ldr r11, [r3, #156]
	eor r12, r8, r4, lsr #4
	and r12, r12, r0
	eor r8, r8, r12
	eor r4, r4, r12, ror #28
	eor r12, r9, r5, lsr #4
	and r12, r12, r0
	eor r9, r9, r12
	eor r5, r5, r12, ror #28
	eor r12, r10, r6, lsr #4
	and r12, r12, r0
	eor r10, r10, r12
	eor r6, r6, r12, ror #28
	eor r12, r11, r7, lsr #4
	and r12, r12, r0
	eor r11, r11, r12
	eor r7, r7, r12, ror #28
	eor r12, r6, r4, lsr #2
	and r12, r12, r1
	eor r6, r6, r12
	eor r4, r4, r12, ror #30
	eor r12, r7, r5, lsr #2
	and r12, r12, r1
	eor r7, r7, r12
	eor r5, r5, r12, ror #30
	eor r12, r10, r8, lsr #2
	and r12, r12, r1
	eor r10, r10, r12
	eor r8, r8, r12, ror #30
	eor r12, r11, r9, lsr #2
	and r12, r12, r1
	eor r11, r11, r12
	eor r9, r9, r12, ror #30
	eor r12, r5, r4, lsr #1
	and r12, r12, r2
	eor r5, r5, r12
	eor r4, r4, r12, ror #31
	eor r12, r7, r6, lsr #1
	and r12, r12, r2
	eor r7, r7, r12
	eor r6, r6, r12, ror #31
	eor r12, r9, r8, lsr #1
	and r12, r12, r2
	eor r9, r9, r12
	eor r8, r8, r12, ror #31
	eor r12, r11, r10, lsr #1
	and r12, r12, r2
	eor r11, r11, r12
	eor r10, r10, r12, ror #31
	str r4, [r3, #128]
	str r5, [r3, #132]
	str r6, [r3, #136]
	str r7, [r3, #140]
	str r8, [r3, #144]
	str r9, [r3, #148]
	str r10, [r3, #152]
	str r11, [r3, #156]
	ldr r4, [r3, #160]
	ldr r5, [r3, #164]
	ldr r6, [r3, #168]
	ldr r7, [r3, #172]
	ldr r8, [r3, #176]
	ldr r9, [r3, #180]
	ldr r10, [r3, #184]
	ldr r11, [r3, #188]
	eor r12, r8, r4, lsr #4
	and r12, r12, r0
	eor r8, r8, r12
	eor r4, r4, r12, ror #28
	eor r12, r9, r5, lsr #4
	and r12, r12, r0
	eor r9, r9, r12
	eor r5, r5, r12, ror #28
	eor r12, r10, r6, lsr #4
	and r12, r12, r0
	eor r10, r10, r12
	eor r6, r6, r12, ror #28
	eor r12, r11, r7, lsr #4
	and r12, r12, r0
	eor r11, r11, r12
	eor r7, r7, r12, ror #28
	eor r12, r6, r4, lsr #2
	and r12, r12, r1
	eor r6, r6, r12
	eor r4, r4, r12, ror #30
	eor r12, r7, r5, lsr #2
	and r12, r12, r1
	eor r7, r7, r12
	eor r5, r5, r12, ror #30
	eor r12, r10, r8, lsr #2
	and r12, r12, r1
	eor r10, r10, r12
	eor r8, r8, r12, ror #30
	eor r12, r11, r9, lsr #2
	and r12, r12, r1
	eor r11, r11, r12
	eor r9, r9, r12, ror #30
	eor r12, r5, r4, lsr #1
	and r12, r12, r2
	eor r5, r5, r12
	eor r4, r4, r12, ror #31
	eor r12, r7, r6, lsr #1
	and r12, r12, r2
	eor r7, r7, r12
	eor r6, r6, r12, ror #31
	eor r12, r9, r8, lsr #1
	and r12, r12, r2
	eor r9, r9, r12
	eor r8, r8, r12, ror #31
	eor r12, r11, r10, lsr #1
	and r12, r12, r2
	eor r11, r11, r12
	eor r10, r10, r12, ror #31
	str r4, [r3, #160]
	str r5, [r3, #164]
	str r6, [r3, #168]
	str r7, [r3, #172]
	str r8, [r3, #176]
	str r9, [r3, #180]
	str r10, [r3, #184]
	str r11, [r3, #188]
	ldr r4, [r3, #192]
	ldr r5, [r3, #196]
	ldr r6, [r3, #200]
	ldr r7, [r3, #204]
	ldr r8, [r3, #208]
	ldr r9, [r3, #212]
	ldr r10, [r3, #216]
	ldr r11, [r3, #220]
	eor r12, r8, r4, lsr #4
	and r12, r12, r0
	eor r8, r8, r12
	eor r4, r4, r12, ror #28
	eor r12, r9, r5, lsr #4
	and r12, r12, r0
	eor r9, r9, r12
	eor r5, r5, r12, ror #28
	eor r12, r10, r6, lsr #4
	and r12, r12, r0
	eor r10, r10, r12
	eor r6, r6, r12, ror #28
	eor r12, r11, r7, lsr #4
	and r12, r12, r0
	eor r11, r11, r12
	eor r7, r7, r12, ror #28
	eor r12, r6, r4, lsr #2
	and r12, r12, r1
	eor r6, r6, r12
	eor r4, r4, r12, ror #30
	eor r12, r7, r5, lsr #2
	and r12, r12, r1
	eor r7, r7, r12
	eor r5, r5, r12, ror #30
	eor r12, r10, r8, lsr #2
	and r12, r12, r1
	eor r10, r10, r12
	eor r8, r8, r12, ror #30
	eor r12, r11, r9, lsr #2
	and r12, r12, r1
	eor r11, r11, r12
	eor r9, r9, r12, ror #30
	eor r12, r5, r4, lsr #1
	and r12, r12, r2
	eor r5, r5, r12
	eor r4, r4, r12, ror #31
	eor r12, r7, r6, lsr #1
	and r12, r12, r2
	eor r7, r7, r12
	eor r6, r6, r12, ror #31
	eor r12, r9, r8, lsr #1
	and r12, r12, r2
	eor r9, r9, r12
	eor r8, r8, r12, ror #31
	eor r12, r11, r10, lsr #1
	and r12, r12, r2
	eor r11, r11, r12
	eor r10, r10, r12, ror #31
	str r4, [r3, #192]
	str r5, [r3, #196]
	str r6, [r3, #200]
	str r7, [r3, #204]
	str r8, [r3, #208]
	str r9, [r3, #212]
	str r10, [r3, #216]
	str r11, [r3, #220]
	ldr r4, [r3, #224]
	ldr r5, [r3, #228]
	ldr r6, [r3, #232]
	ldr r7, [r3, #236]
	ldr r8, [r3, #240]
	ldr r9, [r3, #244]
	ldr r10, [r3, #248]
	ldr r11, [r3, #252]
	eor r12, r8, r4, lsr #4
	and r12, r12, r0
	eor r8, r8, r12
	eor r4, r4, r12, ror #28
	eor r12, r9, r5, lsr #4
	and r12, r12, r0
	eor r9, r9, r12
	eor r5, r5, r12, ror #28
	eor r12, r10, r6, lsr #4
	and r12, r12, r0
	eor r10, r10, r12
	eor r6, r6, r12, ror #28
	eor r12, r11, r7, lsr #4
	and r12, r12, r0
	eor r11, r11, r12
	eor r7, r7, r12, ror #28
	eor r12, r6, r4, lsr #2
	and r12, r12, r1
	eor r6, r6, r12
	eor r4, r4, r12, ror #30
	eor r12, r7, r5, lsr #2
	and r12, r12, r1
	eor r7, r7, r12
	eor r5, r5, r12, ror #30
	eor r12, r10, r8, lsr #2
	and r12, r12, r1
	eor r10, r10, r12
	eor r8, r8, r12, ror #30
	eor r12, r11, r9, lsr #2
	and r12, r12, r1
	eor r11, r11, r12
	eor r9, r9, r12, ror #30
	eor r12, r5, r4, lsr #1
	and r12, r12, r2
	eor r5, r5, r12
	eor r4, r4, r12, ror #31
	eor r12, r7, r6, lsr #1
	and r12, r12, r2
	eor r7, r7, r12
	eor r6, r6, r12, ror #31
	eor r12, r9, r8, lsr #1
	and r12, r12, r2
	eor r9, r9, r12
	eor r8, r8, r12, ror #31
	eor r12, r11, r10, lsr #1
	and r12, r12, r2
	eor r11, r11, r12
	eor r10, r10, r12, ror #31
	str r4, [r3, #224]
	str r5, [r3, #228]
	str r6, [r3, #232]
	str r7, [r3, #236]
	str r8, [r3, #240]
	str r9, [r3, #244]
	str r10, [r3, #248]
	str r11, [r3, #252]
	ldr r4, [r3, #256]
	ldr r5, [r3, #260]
	ldr r6, [r3, #264]
	ldr r7, [r3, #268]
	ldr r8, [r3, #272]
	ldr r9, [r3, #276]
	ldr r10, [r3, #280]
	ldr r11, [r3, #284]
	eor r12, r8, r4, lsr #4
	and r12, r12, r0
	eor r8, r8, r12
	eor r4, r4, r12, ror #28
	eor r12, r9, r5, lsr #4
	and r12, r12, r0
	eor r9, r9, r12
	eor r5, r5, r12, ror #28
	eor r12, r10, r6, lsr #4
	and r12, r12, r0
	eor r10, r10, r12
	eor r6, r6, r12, ror #28
	eor r12, r11, r7, lsr #4
	and r12, r12, r0
	eor r11, r11, r12
	eor r7, r7, r12, ror #28
	eor r12, r6, r4, lsr #2
	and r12, r12, r1
	eor r6, r6, r12
	eor r4, r4, r12, ror #30
	eor r12, r7, r5, lsr #2
	and r12, r12, r1
	eor r7, r7, r12
	eor r5, r5, r12, ror #30
	eor r12, r10, r8, lsr #2
	and r12, r12, r1
	eor r10, r10, r12
	eor r8, r8, r12, ror #30
	eor r12, r11, r9, lsr #2
	and r12, r12, r1
	eor r11, r11, r12
	eor r9, r9, r12, ror #30
	eor r12, r5, r4, lsr #1
	and r12, r12, r2
	eor r5, r5, r12
	eor r4, r4, r12, ror #31
	eor r12, r7, r6, lsr #1
	and r12, r12, r2
	eor r7, r7, r12
	eor r6, r6, r12, ror #31
	eor r12, r9, r8, lsr #1
	and r12, r12, r2
	eor r9, r9, r12
	eor r8, r8, r12, ror #31
	eor r12, r11, r10, lsr #1
	and r12, r12, r2
	eor r11, r11, r12
	eor r10, r10, r12, ror #31
	str r4, [r3, #256]
	str r5, [r3, #260]
	str r6, [r3, #264]
	str r7, [r3, #268]
	str r8, [r3, #272]
	str r9, [r3, #276]
	str r10, [r3, #280]
	str r11, [r3, #284]
	ldr r0, [r3, #304]
	ldr r1, [r3, #308]
	ldr r2, [r3, #312]
	ldr r12, [r3, #316]
	add r4, r3, #32
	mov r5, r1
	mov r6, r12
26:
	ldr r7, [r4, #0]
	str r7, [r5, #0]
	ldr r7, [r4, #128]
	str r7, [r5, #4]
	add r5, r5, #8
	add r4, r4, #4
	subs r6, r6, #1
	bne 26b
	add r1, r1, r12, lsl #3
	subs r2, r2, r12
	bne 22b
	ldr r4, [r3, #320]
	ldr r5, [r3, #324]
	ldr r6, [r3, #328]
	ldr r7, [r3, #332]
	ldr r8, [r3, #336]
	ldr r9, [r3, #340]
	ldr r10, [r3, #344]
	ldr r11, [r3, #348]
	ldr lr, [r3, #352]
	b 21f
20:
21:
	add sp, sp, #1024
	bx lr
