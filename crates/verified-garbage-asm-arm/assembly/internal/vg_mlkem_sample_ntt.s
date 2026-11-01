// The functions of `src/internal/vg_mlkem_sample_ntt.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_sample_ntt:
	str r4, [r2, #1680]
	str r5, [r2, #1684]
	str r6, [r2, #1688]
	str r7, [r2, #1692]
	str r8, [r2, #1696]
	str r9, [r2, #1700]
	str r10, [r2, #1704]
	str r11, [r2, #1708]
	str lr, [r2, #1712]
	mov r4, r0
	mov r5, r1
	mov r6, r2
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
	mov r3, r4
	mov r12, #34
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
	mov r12, #840
	add lr, r6, #200
	push {r12, lr}
	bl {vg_keccak_squeeze_scratch}
	ldr r12, [sp], #8
	add r0, r6, #840
	mov r1, r5
	mov r2, #0
	mov r3, #280
20:
	ldrb r7, [r0, #0]
	ldrb r8, [r0, #1]
	ldrb r9, [r0, #2]
	lsl r10, r8, #28
	add r10, r7, r10, lsr #20
	lsr r11, r8, #4
	add r11, r11, r9, lsl #4
	sub r12, r10, #3328
	sub r12, r12, #1
	lsr r12, r12, #31
	sub r7, r2, #256
	lsr r7, r7, #31
	and r12, r12, r7
	cmp r12, #0
	beq 21f
	str r10, [r1, #0]
	add r1, r1, #4
	add r2, r2, #1
	b 22f
21:
22:
	sub r12, r11, #3328
	sub r12, r12, #1
	lsr r12, r12, #31
	sub r7, r2, #256
	lsr r7, r7, #31
	and r12, r12, r7
	cmp r12, #0
	beq 23f
	str r11, [r1, #0]
	add r1, r1, #4
	add r2, r2, #1
	b 24f
23:
24:
	add r0, r0, #3
	subs r3, r3, #1
	bne 20b
	lsr r0, r2, #8
	mov r3, r6
	ldr r4, [r3, #1680]
	ldr r5, [r3, #1684]
	ldr r6, [r3, #1688]
	ldr r7, [r3, #1692]
	ldr r8, [r3, #1696]
	ldr r9, [r3, #1700]
	ldr r10, [r3, #1704]
	ldr r11, [r3, #1708]
	ldr lr, [r3, #1712]
	bx lr
