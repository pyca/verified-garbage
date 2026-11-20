// The functions of `src/internal/vg_blowfish_ecb_decrypt_entry.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blowfish_ecb_decrypt_entry:
	sub sp, sp, #256
	add r3, sp, #0
	str r4, [r3, #0]
	str r5, [r3, #4]
	str r6, [r3, #8]
	str r7, [r3, #12]
	str r8, [r3, #16]
	str r9, [r3, #20]
	str r10, [r3, #24]
	str r11, [r3, #28]
	str lr, [r3, #32]
	str r1, [r3, #36]
	str r2, [r3, #40]
	cmp r2, #0
	beq 20f
22:
	ldr r12, [r3, #36]
	ldr r1, [r12, #0]
	rev r1, r1
	ldr r2, [r12, #4]
	rev r2, r2
	add r12, r0, #4160
23:
	ldr r9, [r12, #4]
	eor r1, r1, r9
	str r0, [r3, #48]
	str r1, [r3, #52]
	str r2, [r3, #56]
	str r12, [r3, #60]
	str r1, [r3, #64]
	mov r12, r3
	mov r0, #0
	str r0, [r12, #68]
	str r0, [r12, #76]
24:
	ldr r0, [r12, #64]
	lsr r0, r0, #24
	mov r3, #1
	and r1, r3, r0, lsr #3
	add r2, r3, r1
	and r1, r3, r0, lsr #4
	add lr, r3, r1, lsl #2
	sub lr, lr, r1
	mul r2, r2, lr
	and r1, r3, r0, lsr #5
	add lr, r3, r1, lsl #4
	sub lr, lr, r1
	mul r2, r2, lr
	and r1, r3, r0, lsr #6
	add lr, r3, r1, lsl #8
	sub lr, lr, r1
	mul r2, r2, lr
	and r1, r3, r0, lsr #7
	add lr, r3, r1, lsl #16
	sub lr, lr, r1
	mul r2, r2, lr
	mov r4, #0
	mov r5, #0
	mov r6, #0
	mov r7, #0
	mov r8, #0
	mov r9, #0
	mov r10, #0
	mov r11, #0
	ldr lr, [r12, #48]
	ldr r0, [r12, #68]
	add lr, lr, r0
	mov r0, #4
	str r0, [r12, #72]
25:
	bic r1, r3, r2
	sub r1, r1, #1
	ldr r0, [lr, #0]
	and r0, r0, r1
	orr r4, r4, r0
	ldr r0, [lr, #4]
	and r0, r0, r1
	orr r5, r5, r0
	ldr r0, [lr, #256]
	mla r6, r0, r1, r6
	ldr r0, [lr, #260]
	mla r7, r0, r1, r7
	ldr r0, [lr, #512]
	and r0, r0, r1
	orr r8, r8, r0
	ldr r0, [lr, #516]
	and r0, r0, r1
	orr r9, r9, r0
	ldr r0, [lr, #768]
	mla r10, r0, r1, r10
	ldr r0, [lr, #772]
	mla r11, r0, r1, r11
	bic r1, r3, r2, lsr #1
	sub r1, r1, #1
	ldr r0, [lr, #8]
	and r0, r0, r1
	orr r4, r4, r0
	ldr r0, [lr, #12]
	and r0, r0, r1
	orr r5, r5, r0
	ldr r0, [lr, #264]
	mla r6, r0, r1, r6
	ldr r0, [lr, #268]
	mla r7, r0, r1, r7
	ldr r0, [lr, #520]
	and r0, r0, r1
	orr r8, r8, r0
	ldr r0, [lr, #524]
	and r0, r0, r1
	orr r9, r9, r0
	ldr r0, [lr, #776]
	mla r10, r0, r1, r10
	ldr r0, [lr, #780]
	mla r11, r0, r1, r11
	bic r1, r3, r2, lsr #2
	sub r1, r1, #1
	ldr r0, [lr, #16]
	and r0, r0, r1
	orr r4, r4, r0
	ldr r0, [lr, #20]
	and r0, r0, r1
	orr r5, r5, r0
	ldr r0, [lr, #272]
	mla r6, r0, r1, r6
	ldr r0, [lr, #276]
	mla r7, r0, r1, r7
	ldr r0, [lr, #528]
	and r0, r0, r1
	orr r8, r8, r0
	ldr r0, [lr, #532]
	and r0, r0, r1
	orr r9, r9, r0
	ldr r0, [lr, #784]
	mla r10, r0, r1, r10
	ldr r0, [lr, #788]
	mla r11, r0, r1, r11
	bic r1, r3, r2, lsr #3
	sub r1, r1, #1
	ldr r0, [lr, #24]
	and r0, r0, r1
	orr r4, r4, r0
	ldr r0, [lr, #28]
	and r0, r0, r1
	orr r5, r5, r0
	ldr r0, [lr, #280]
	mla r6, r0, r1, r6
	ldr r0, [lr, #284]
	mla r7, r0, r1, r7
	ldr r0, [lr, #536]
	and r0, r0, r1
	orr r8, r8, r0
	ldr r0, [lr, #540]
	and r0, r0, r1
	orr r9, r9, r0
	ldr r0, [lr, #792]
	mla r10, r0, r1, r10
	ldr r0, [lr, #796]
	mla r11, r0, r1, r11
	bic r1, r3, r2, lsr #4
	sub r1, r1, #1
	ldr r0, [lr, #32]
	and r0, r0, r1
	orr r4, r4, r0
	ldr r0, [lr, #36]
	and r0, r0, r1
	orr r5, r5, r0
	ldr r0, [lr, #288]
	mla r6, r0, r1, r6
	ldr r0, [lr, #292]
	mla r7, r0, r1, r7
	ldr r0, [lr, #544]
	and r0, r0, r1
	orr r8, r8, r0
	ldr r0, [lr, #548]
	and r0, r0, r1
	orr r9, r9, r0
	ldr r0, [lr, #800]
	mla r10, r0, r1, r10
	ldr r0, [lr, #804]
	mla r11, r0, r1, r11
	bic r1, r3, r2, lsr #5
	sub r1, r1, #1
	ldr r0, [lr, #40]
	and r0, r0, r1
	orr r4, r4, r0
	ldr r0, [lr, #44]
	and r0, r0, r1
	orr r5, r5, r0
	ldr r0, [lr, #296]
	mla r6, r0, r1, r6
	ldr r0, [lr, #300]
	mla r7, r0, r1, r7
	ldr r0, [lr, #552]
	and r0, r0, r1
	orr r8, r8, r0
	ldr r0, [lr, #556]
	and r0, r0, r1
	orr r9, r9, r0
	ldr r0, [lr, #808]
	mla r10, r0, r1, r10
	ldr r0, [lr, #812]
	mla r11, r0, r1, r11
	bic r1, r3, r2, lsr #6
	sub r1, r1, #1
	ldr r0, [lr, #48]
	and r0, r0, r1
	orr r4, r4, r0
	ldr r0, [lr, #52]
	and r0, r0, r1
	orr r5, r5, r0
	ldr r0, [lr, #304]
	mla r6, r0, r1, r6
	ldr r0, [lr, #308]
	mla r7, r0, r1, r7
	ldr r0, [lr, #560]
	and r0, r0, r1
	orr r8, r8, r0
	ldr r0, [lr, #564]
	and r0, r0, r1
	orr r9, r9, r0
	ldr r0, [lr, #816]
	mla r10, r0, r1, r10
	ldr r0, [lr, #820]
	mla r11, r0, r1, r11
	bic r1, r3, r2, lsr #7
	sub r1, r1, #1
	ldr r0, [lr, #56]
	and r0, r0, r1
	orr r4, r4, r0
	ldr r0, [lr, #60]
	and r0, r0, r1
	orr r5, r5, r0
	ldr r0, [lr, #312]
	mla r6, r0, r1, r6
	ldr r0, [lr, #316]
	mla r7, r0, r1, r7
	ldr r0, [lr, #568]
	and r0, r0, r1
	orr r8, r8, r0
	ldr r0, [lr, #572]
	and r0, r0, r1
	orr r9, r9, r0
	ldr r0, [lr, #824]
	mla r10, r0, r1, r10
	ldr r0, [lr, #828]
	mla r11, r0, r1, r11
	lsr r2, r2, #8
	add lr, lr, #64
	ldr r0, [r12, #72]
	subs r0, r0, #1
	str r0, [r12, #72]
	bne 25b
	ldr r2, [r12, #64]
	lsr r2, r2, #24
	bic r0, r3, r2, lsr #2
	and r1, r3, r2, lsr #2
	mul r4, r4, r0
	mla r4, r5, r1, r4
	mul r8, r8, r0
	mla r8, r9, r1, r8
	sub r5, r1, #1
	sub r9, r0, #1
	mul r6, r6, r5
	mla r6, r7, r9, r6
	mul r10, r10, r5
	mla r10, r11, r9, r10
	bic r0, r3, r2
	add r1, r3, r0, lsl #8
	sub r1, r1, r0
	bic r0, r3, r2, lsr #1
	add lr, r3, r0, lsl #16
	sub lr, lr, r0
	mul r1, r1, lr
	mul r0, r4, r1
	lsr r0, r0, #24
	mul r5, r6, r1
	lsr r5, r5, #24
	orr r0, r0, r5, lsl #8
	mul r5, r8, r1
	lsr r5, r5, #24
	orr r0, r0, r5, lsl #16
	mul r5, r10, r1
	lsr r5, r5, #24
	orr r0, r0, r5, lsl #24
	ldr r2, [r12, #64]
	lsl r2, r2, #8
	str r2, [r12, #64]
	ldr r1, [r12, #76]
	ldr r2, [r12, #68]
	cmp r2, #2048
	beq 26f
	add r1, r1, r0
	b 27f
26:
	eor r1, r1, r0
27:
	str r1, [r12, #76]
	add r2, r2, #1024
	str r2, [r12, #68]
	cmp r2, #4096
	bne 24b
	ldr lr, [r12, #76]
	ldr r0, [r12, #48]
	ldr r1, [r12, #52]
	ldr r2, [r12, #56]
	mov r3, r12
	ldr r12, [r3, #60]
	eor r2, r2, lr
	mov r9, r1
	mov r1, r2
	mov r2, r9
	sub r12, r12, #4
	sub r9, r12, r0
	cmp r9, #4096
	bne 23b
	ldr r9, [r12, #4]
	eor r9, r1, r9
	ldr r1, [r12, #0]
	eor r1, r1, r2
	mov r2, r9
	ldr r12, [r3, #36]
	ldr r11, [r3, #40]
	rev r1, r1
	str r1, [r12, #0]
	rev r2, r2
	str r2, [r12, #4]
	add r12, r12, #8
	str r12, [r3, #36]
	subs r11, r11, #1
	str r11, [r3, #40]
	bne 22b
	b 21f
20:
21:
	ldr r4, [r3, #0]
	ldr r5, [r3, #4]
	ldr r6, [r3, #8]
	ldr r7, [r3, #12]
	ldr r8, [r3, #16]
	ldr r9, [r3, #20]
	ldr r10, [r3, #24]
	ldr r11, [r3, #28]
	ldr lr, [r3, #32]
	add r12, sp, #0
	mov r2, #0
	str r2, [r12, #0]
	str r2, [r12, #4]
	str r2, [r12, #8]
	str r2, [r12, #12]
	str r2, [r12, #16]
	str r2, [r12, #20]
	str r2, [r12, #24]
	str r2, [r12, #28]
	str r2, [r12, #32]
	str r2, [r12, #36]
	str r2, [r12, #40]
	str r2, [r12, #44]
	str r2, [r12, #48]
	str r2, [r12, #52]
	str r2, [r12, #56]
	str r2, [r12, #60]
	str r2, [r12, #64]
	str r2, [r12, #68]
	str r2, [r12, #72]
	str r2, [r12, #76]
	add sp, sp, #256
	bx lr
