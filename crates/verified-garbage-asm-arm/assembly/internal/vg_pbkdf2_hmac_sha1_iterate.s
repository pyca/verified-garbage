// The functions of `src/internal/vg_pbkdf2_hmac_sha1_iterate.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_sha1_iterate:
	ldr r12, [sp, #0]
	str r4, [r12, #160]
	str r5, [r12, #164]
	str r6, [r12, #168]
	str r7, [r12, #172]
	str r8, [r12, #176]
	str r9, [r12, #180]
	str r10, [r12, #184]
	str lr, [r12, #188]
	str r11, [r12, #192]
	mov r11, r12
	mov r7, r3
	mov r3, r12
	mov r4, r0
	mov r5, r2
	movw r12, #196
	add r0, r11, r12
	movw r12, #216
	add r6, r11, r12
	ldr r12, [r1, #0]
	str r12, [r6, #0]
	ldr r12, [r1, #4]
	str r12, [r6, #4]
	ldr r12, [r1, #8]
	str r12, [r6, #8]
	ldr r12, [r1, #12]
	str r12, [r6, #12]
	ldr r12, [r1, #16]
	str r12, [r6, #16]
	mov r12, #128
	str r12, [r6, #20]
	mov r12, #0
	str r12, [r6, #24]
	str r12, [r6, #28]
	str r12, [r6, #32]
	str r12, [r6, #36]
	str r12, [r6, #40]
	str r12, [r6, #44]
	str r12, [r6, #48]
	str r12, [r6, #52]
	movw r12, #0
	movt r12, #0
	str r12, [r6, #56]
	movw r12, #0
	movt r12, #40962
	str r12, [r6, #60]
	cmp r5, #0
	beq 20f
22:
	ldr r12, [r4, #0]
	str r12, [r0, #0]
	ldr r12, [r4, #4]
	str r12, [r0, #4]
	ldr r12, [r4, #8]
	str r12, [r0, #8]
	ldr r12, [r4, #12]
	str r12, [r0, #12]
	ldr r12, [r4, #16]
	str r12, [r0, #16]
	mov r1, r6
	mov r2, #1
	bl {vg_sha1_compress}
	ldr r9, [r0, #0]
	rev r9, r9
	str r9, [r6, #0]
	ldr r9, [r0, #4]
	rev r9, r9
	str r9, [r6, #4]
	ldr r9, [r0, #8]
	rev r9, r9
	str r9, [r6, #8]
	ldr r9, [r0, #12]
	rev r9, r9
	str r9, [r6, #12]
	ldr r9, [r0, #16]
	rev r9, r9
	str r9, [r6, #16]
	ldr r12, [r4, #84]
	str r12, [r0, #0]
	ldr r12, [r4, #88]
	str r12, [r0, #4]
	ldr r12, [r4, #92]
	str r12, [r0, #8]
	ldr r12, [r4, #96]
	str r12, [r0, #12]
	ldr r12, [r4, #100]
	str r12, [r0, #16]
	mov r1, r6
	mov r2, #1
	bl {vg_sha1_compress}
	ldr r9, [r0, #0]
	rev r9, r9
	str r9, [r6, #0]
	ldr r9, [r0, #4]
	rev r9, r9
	str r9, [r6, #4]
	ldr r9, [r0, #8]
	rev r9, r9
	str r9, [r6, #8]
	ldr r9, [r0, #12]
	rev r9, r9
	str r9, [r6, #12]
	ldr r9, [r0, #16]
	rev r9, r9
	str r9, [r6, #16]
	ldr r12, [r6, #0]
	ldr r1, [r7, #0]
	eor r12, r12, r1
	str r12, [r7, #0]
	ldr r12, [r6, #4]
	ldr r1, [r7, #4]
	eor r12, r12, r1
	str r12, [r7, #4]
	ldr r12, [r6, #8]
	ldr r1, [r7, #8]
	eor r12, r12, r1
	str r12, [r7, #8]
	ldr r12, [r6, #12]
	ldr r1, [r7, #12]
	eor r12, r12, r1
	str r12, [r7, #12]
	ldr r12, [r6, #16]
	ldr r1, [r7, #16]
	eor r12, r12, r1
	str r12, [r7, #16]
	subs r5, r5, #1
	bne 22b
	b 21f
20:
21:
	ldr r4, [r11, #160]
	ldr r5, [r11, #164]
	ldr r6, [r11, #168]
	ldr r7, [r11, #172]
	ldr r8, [r11, #176]
	ldr r9, [r11, #180]
	ldr r10, [r11, #184]
	ldr lr, [r11, #188]
	ldr r11, [r11, #192]
	bx lr
