// The functions of `src/internal/vg_hmac_sha512_256_init_any_scratch.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_sha512_256_init_any_scratch:
	ldr r12, [sp, #0]
	str r4, [r12, #1872]
	str r5, [r12, #1876]
	str r6, [r12, #1880]
	str r7, [r12, #1884]
	str r8, [r12, #1888]
	str r9, [r12, #1892]
	str r10, [r12, #1896]
	str lr, [r12, #1900]
	str r11, [r12, #1904]
	mov r11, r12
	mov r8, r2
	mov r9, r3
	mov r5, r0
	mov r6, r1
	subs r12, r9, #129
	mov r12, #0
	adc r12, r12, #0
	cmp r12, #0
	beq 20f
	movw r12, #2484
	add r4, r11, r12
	mov r0, r4
	bl {vg_sha512_256_init_core}
	mov r0, r4
	mov r1, r8
	mov r7, r9
	mov r10, r11
	mov r2, #0
	mov r3, #0
	push {r1, r7, r10, r12}
	bl {vg_sha512_update_scratch}
	ldr r1, [sp], #16
	mov r0, r4
	movw r12, #2740
	add r1, r11, r12
	mov r12, r11
	mov r2, r9
	mov r3, #0
	push {r1, r12}
	bl {vg_sha512_finalize_scratch}
	ldr r1, [sp], #8
	movw r12, #2740
	add r2, r11, r12
	movw r3, #32
	b 21f
20:
	mov r2, r8
	mov r3, r9
21:
	mov r0, r5
	mov r1, r6
	mov r12, r11
	push {r12, lr}
	bl {vg_hmac_sha512_256_init_scratch}
	ldr r12, [sp], #8
	ldr r4, [r11, #1872]
	ldr r5, [r11, #1876]
	ldr r6, [r11, #1880]
	ldr r7, [r11, #1884]
	ldr r8, [r11, #1888]
	ldr r9, [r11, #1892]
	ldr r10, [r11, #1896]
	ldr lr, [r11, #1900]
	ldr r11, [r11, #1904]
	bx lr
