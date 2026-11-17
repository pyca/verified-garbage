// The functions of `src/internal/vg_poly1305_blocks_umaal.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_poly1305_blocks_umaal:
	str r4, [r0, #56]
	str r5, [r0, #60]
	str r6, [r0, #64]
	str r7, [r0, #68]
	str r8, [r0, #72]
	str r9, [r0, #76]
	str r10, [r0, #80]
	str r11, [r0, #84]
	str r1, [r0, #124]
	str r2, [r0, #20]
	movw r2, #65535
	movt r2, #4095
	ldr r1, [r0, #24]
	and r1, r1, r2
	str r1, [r0, #88]
	movw r2, #65532
	movt r2, #4095
	ldr r1, [r0, #28]
	and r1, r1, r2
	str r1, [r0, #92]
	ldr r1, [r0, #32]
	and r1, r1, r2
	str r1, [r0, #96]
	ldr r1, [r0, #36]
	and r1, r1, r2
	str r1, [r0, #100]
	ldr r1, [r0, #92]
	add r1, r1, r1, lsr #2
	str r1, [r0, #104]
	ldr r1, [r0, #96]
	add r1, r1, r1, lsr #2
	str r1, [r0, #108]
	ldr r1, [r0, #100]
	add r1, r1, r1, lsr #2
	str r1, [r0, #112]
	ldr r3, [r0, #0]
	ldr r5, [r0, #4]
	ldr r7, [r0, #8]
	ldr r10, [r0, #12]
	ldr r11, [r0, #16]
	and r11, r11, #3
	ldr r1, [r0, #20]
	cmp r1, #0
	beq 20f
22:
	ldr r1, [r0, #124]
	add r2, r1, #16
	str r2, [r0, #124]
	ldr r4, [r1, #0]
	ldr r6, [r1, #4]
	ldr r8, [r1, #8]
	ldr r9, [r1, #12]
	lsr r1, r11, #2
	add r1, r1, r1, lsl #2
	and r12, r11, #3
	mov r2, #1
	umaal r4, r1, r3, r2
	umaal r6, r1, r5, r2
	umaal r8, r1, r7, r2
	umaal r9, r1, r10, r2
	add r12, r12, r1
	add r12, r12, #1
	ldr r2, [r0, #104]
	mul r7, r12, r2
	ldr r2, [r0, #108]
	mul r10, r12, r2
	ldr r2, [r0, #112]
	mul r11, r12, r2
	mov r3, #0
	mov r5, #0
	ldr r2, [r0, #88]
	umaal r3, r5, r4, r2
	umaal r5, r7, r6, r2
	umaal r7, r10, r8, r2
	umaal r10, r11, r9, r2
	mla r11, r12, r2, r11
	mov r1, #0
	ldr r2, [r0, #104]
	umaal r3, r1, r9, r2
	ldr r2, [r0, #92]
	umaal r5, r1, r4, r2
	umaal r7, r1, r6, r2
	umaal r10, r1, r8, r2
	add r11, r11, r1
	mov r1, #0
	ldr r2, [r0, #108]
	umaal r3, r1, r8, r2
	umaal r5, r1, r9, r2
	ldr r2, [r0, #96]
	umaal r7, r1, r4, r2
	umaal r10, r1, r6, r2
	add r11, r11, r1
	mov r1, #0
	ldr r2, [r0, #112]
	umaal r3, r1, r6, r2
	umaal r5, r1, r8, r2
	umaal r7, r1, r9, r2
	ldr r2, [r0, #100]
	umaal r10, r1, r4, r2
	add r11, r11, r1
	ldr r1, [r0, #20]
	subs r1, r1, #1
	str r1, [r0, #20]
	bne 22b
	b 21f
20:
21:
	lsr r1, r11, #2
	add r1, r1, r1, lsl #2
	and r11, r11, #3
	mov r2, #0
	umaal r3, r1, r2, r2
	umaal r5, r1, r2, r2
	umaal r7, r1, r2, r2
	umaal r10, r1, r2, r2
	add r11, r11, r1
	mov r1, #5
	mov r4, r3
	umaal r4, r1, r2, r2
	mov r4, r5
	umaal r4, r1, r2, r2
	mov r4, r7
	umaal r4, r1, r2, r2
	mov r4, r10
	umaal r4, r1, r2, r2
	add r1, r1, r11
	lsr r1, r1, #2
	add r1, r1, r1, lsl #2
	umaal r3, r1, r2, r2
	umaal r5, r1, r2, r2
	umaal r7, r1, r2, r2
	umaal r10, r1, r2, r2
	add r11, r11, r1
	and r1, r11, #3
	str r3, [r0, #0]
	str r5, [r0, #4]
	str r7, [r0, #8]
	str r10, [r0, #12]
	str r1, [r0, #16]
	mov r2, #0
	str r2, [r0, #20]
	ldr r4, [r0, #56]
	ldr r5, [r0, #60]
	ldr r6, [r0, #64]
	ldr r7, [r0, #68]
	ldr r8, [r0, #72]
	ldr r9, [r0, #76]
	ldr r10, [r0, #80]
	ldr r11, [r0, #84]
	bx lr
