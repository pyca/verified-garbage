// The functions of `src/internal/vg_mldsa_rej_ntt_poly.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_rej_ntt_poly:
	str r4, [r2, #2012]
	str r5, [r2, #2016]
	str r6, [r2, #2020]
	str r7, [r2, #2024]
	str r8, [r2, #2028]
	str r9, [r2, #2032]
	str r10, [r2, #2036]
	str r11, [r2, #2040]
	str lr, [r2, #2044]
	mov r5, r1
	mov r6, r2
	mov r7, #0
	mov r8, r0
	mov r9, #34
	mov r12, #0
	str r12, [r6, #0]
	str r12, [r6, #4]
	str r12, [r6, #8]
	str r12, [r6, #12]
	str r12, [r6, #16]
	str r12, [r6, #20]
	str r12, [r6, #24]
	str r12, [r6, #28]
	str r12, [r6, #32]
	str r12, [r6, #36]
	str r12, [r6, #40]
	str r12, [r6, #44]
	str r12, [r6, #48]
	str r12, [r6, #52]
	str r12, [r6, #56]
	str r12, [r6, #60]
	str r12, [r6, #64]
	str r12, [r6, #68]
	str r12, [r6, #72]
	str r12, [r6, #76]
	str r12, [r6, #80]
	str r12, [r6, #84]
	str r12, [r6, #88]
	str r12, [r6, #92]
	str r12, [r6, #96]
	str r12, [r6, #100]
	str r12, [r6, #104]
	str r12, [r6, #108]
	str r12, [r6, #112]
	str r12, [r6, #116]
	str r12, [r6, #120]
	str r12, [r6, #124]
	str r12, [r6, #128]
	str r12, [r6, #132]
	str r12, [r6, #136]
	str r12, [r6, #140]
	str r12, [r6, #144]
	str r12, [r6, #148]
	str r12, [r6, #152]
	str r12, [r6, #156]
	str r12, [r6, #160]
	str r12, [r6, #164]
	str r12, [r6, #168]
	str r12, [r6, #172]
	str r12, [r6, #176]
	str r12, [r6, #180]
	str r12, [r6, #184]
	str r12, [r6, #188]
	str r12, [r6, #192]
	str r12, [r6, #196]
	mov r0, r6
	mov r1, #168
	mov r2, #0
	mov r3, r8
	mov r12, r9
	add lr, r6, #200
	push {r12, lr}
	bl {vg_keccak_absorb_scratch}
	ldr r12, [sp], #8
	mov r2, r0
	mov r0, r6
	mov r1, #168
	mov r3, #31
	add lr, r6, #200
	push {lr}
	bl {vg_keccak_pad_scratch}
	ldr r12, [sp], #4
	mov r0, r6
	mov r1, #168
	mov r2, #0
	add r3, r6, #840
	mov r12, #1008
	add lr, r6, #200
	push {r12, lr}
	bl {vg_keccak_squeeze_scratch}
	ldr r12, [sp], #8
	add r0, r6, #840
	mov r2, #0
	mov r3, #336
	movw r7, #57345
	movt r7, #127
20:
	ldrb r8, [r0, #0]
	ldrb r9, [r0, #1]
	ldrb r10, [r0, #2]
	lsl r10, r10, #25
	add r10, r8, r10, lsr #9
	add r10, r10, r9, lsl #8
	sub r11, r2, #256
	lsr r11, r11, #31
	cmp r11, #0
	beq 21f
	sub r11, r10, r7
	lsr r11, r11, #31
	cmp r11, #0
	beq 23f
	add r11, r5, r2, lsl #2
	str r10, [r11, #0]
	add r2, r2, #1
	b 24f
23:
24:
	b 22f
21:
22:
	add r0, r0, #3
	subs r3, r3, #1
	bne 20b
	lsr r0, r2, #8
	mov r3, r6
	ldr r4, [r3, #2012]
	ldr r5, [r3, #2016]
	ldr r6, [r3, #2020]
	ldr r7, [r3, #2024]
	ldr r8, [r3, #2028]
	ldr r9, [r3, #2032]
	ldr r10, [r3, #2036]
	ldr r11, [r3, #2040]
	ldr lr, [r3, #2044]
	bx lr
