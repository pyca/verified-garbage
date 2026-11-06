// The functions of `src/internal/vg_mldsa87_verify_with_cache.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa87_verify_with_cache:
	str r4, [r3, #840]
	str r5, [r3, #844]
	str r6, [r3, #848]
	str r7, [r3, #852]
	str r8, [r3, #856]
	str r9, [r3, #860]
	str r10, [r3, #864]
	str r11, [r3, #868]
	str lr, [r3, #872]
	mov r4, r0
	mov r5, r1
	mov r6, r2
	mov r7, r3
	mov r11, #1
	ldr r8, [sp, #0]
	movw r0, #4544
	movt r0, #0
	add r0, r6, r0
	movw r1, #83
	movt r1, #0
	movw r2, #75
	movt r2, #0
	movw r3, #8192
	movt r3, #0
	add r3, r7, r3
	movw r12, #2048
	movt r12, #0
	push {r12}
	bl {vg_mldsa_hint_bit_unpack}
	ldr r12, [sp], #4
	mov r11, r0
	cmp r11, #0
	bne 20f
	b 21f
20:
	movw r0, #64
	movt r0, #0
	add r0, r6, r0
	movw r1, #640
	movt r1, #0
	movw r2, #65535
	movt r2, #7
	movw r3, #0
	movt r3, #8
	movw r12, #16384
	movt r12, #0
	add r12, r7, r12
	push {r12}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #4
	movw r0, #16384
	movt r0, #0
	add r0, r7, r0
	movw r1, #65416
	movt r1, #7
	bl {vg_mldsa_norm_lt}
	and r11, r11, r0
	movw r0, #704
	movt r0, #0
	add r0, r6, r0
	movw r1, #640
	movt r1, #0
	movw r2, #65535
	movt r2, #7
	movw r3, #0
	movt r3, #8
	movw r12, #17408
	movt r12, #0
	add r12, r7, r12
	push {r12}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #4
	movw r0, #17408
	movt r0, #0
	add r0, r7, r0
	movw r1, #65416
	movt r1, #7
	bl {vg_mldsa_norm_lt}
	and r11, r11, r0
	movw r0, #1344
	movt r0, #0
	add r0, r6, r0
	movw r1, #640
	movt r1, #0
	movw r2, #65535
	movt r2, #7
	movw r3, #0
	movt r3, #8
	movw r12, #18432
	movt r12, #0
	add r12, r7, r12
	push {r12}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #4
	movw r0, #18432
	movt r0, #0
	add r0, r7, r0
	movw r1, #65416
	movt r1, #7
	bl {vg_mldsa_norm_lt}
	and r11, r11, r0
	movw r0, #1984
	movt r0, #0
	add r0, r6, r0
	movw r1, #640
	movt r1, #0
	movw r2, #65535
	movt r2, #7
	movw r3, #0
	movt r3, #8
	movw r12, #19456
	movt r12, #0
	add r12, r7, r12
	push {r12}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #4
	movw r0, #19456
	movt r0, #0
	add r0, r7, r0
	movw r1, #65416
	movt r1, #7
	bl {vg_mldsa_norm_lt}
	and r11, r11, r0
	movw r0, #2624
	movt r0, #0
	add r0, r6, r0
	movw r1, #640
	movt r1, #0
	movw r2, #65535
	movt r2, #7
	movw r3, #0
	movt r3, #8
	movw r12, #20480
	movt r12, #0
	add r12, r7, r12
	push {r12}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #4
	movw r0, #20480
	movt r0, #0
	add r0, r7, r0
	movw r1, #65416
	movt r1, #7
	bl {vg_mldsa_norm_lt}
	and r11, r11, r0
	movw r0, #3264
	movt r0, #0
	add r0, r6, r0
	movw r1, #640
	movt r1, #0
	movw r2, #65535
	movt r2, #7
	movw r3, #0
	movt r3, #8
	movw r12, #21504
	movt r12, #0
	add r12, r7, r12
	push {r12}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #4
	movw r0, #21504
	movt r0, #0
	add r0, r7, r0
	movw r1, #65416
	movt r1, #7
	bl {vg_mldsa_norm_lt}
	and r11, r11, r0
	movw r0, #3904
	movt r0, #0
	add r0, r6, r0
	movw r1, #640
	movt r1, #0
	movw r2, #65535
	movt r2, #7
	movw r3, #0
	movt r3, #8
	movw r12, #22528
	movt r12, #0
	add r12, r7, r12
	push {r12}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #4
	movw r0, #22528
	movt r0, #0
	add r0, r7, r0
	movw r1, #65416
	movt r1, #7
	bl {vg_mldsa_norm_lt}
	and r11, r11, r0
	cmp r11, #0
	bne 22f
	b 23f
22:
	add r0, r4, #0
	add r1, r7, #896
	mov r2, #32
24:
	ldrb r3, [r0, #0]
	strb r3, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs r2, r2, #1
	bne 24b
	movw r12, #0
	strb r12, [r7, #928]
	movw r12, #0
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #28672
	movt r1, #0
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #28672
	movt r1, #0
	add r1, r7, r1
	mov r2, #256
25:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 25b
	movw r12, #1
	strb r12, [r7, #928]
	movw r12, #0
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #29696
	movt r1, #0
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #29696
	movt r1, #0
	add r1, r7, r1
	mov r2, #256
26:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 26b
	movw r12, #2
	strb r12, [r7, #928]
	movw r12, #0
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #30720
	movt r1, #0
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #30720
	movt r1, #0
	add r1, r7, r1
	mov r2, #256
27:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 27b
	movw r12, #3
	strb r12, [r7, #928]
	movw r12, #0
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #31744
	movt r1, #0
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #31744
	movt r1, #0
	add r1, r7, r1
	mov r2, #256
28:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 28b
	movw r12, #4
	strb r12, [r7, #928]
	movw r12, #0
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #32768
	movt r1, #0
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #32768
	movt r1, #0
	add r1, r7, r1
	mov r2, #256
29:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 29b
	movw r12, #5
	strb r12, [r7, #928]
	movw r12, #0
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #33792
	movt r1, #0
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #33792
	movt r1, #0
	add r1, r7, r1
	mov r2, #256
210:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 210b
	movw r12, #6
	strb r12, [r7, #928]
	movw r12, #0
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #34816
	movt r1, #0
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #34816
	movt r1, #0
	add r1, r7, r1
	mov r2, #256
211:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 211b
	movw r12, #0
	strb r12, [r7, #928]
	movw r12, #1
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #36864
	movt r1, #0
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #36864
	movt r1, #0
	add r1, r7, r1
	mov r2, #256
212:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 212b
	movw r12, #1
	strb r12, [r7, #928]
	movw r12, #1
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #37888
	movt r1, #0
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #37888
	movt r1, #0
	add r1, r7, r1
	mov r2, #256
213:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 213b
	movw r12, #2
	strb r12, [r7, #928]
	movw r12, #1
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #38912
	movt r1, #0
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #38912
	movt r1, #0
	add r1, r7, r1
	mov r2, #256
214:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 214b
	movw r12, #3
	strb r12, [r7, #928]
	movw r12, #1
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #39936
	movt r1, #0
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #39936
	movt r1, #0
	add r1, r7, r1
	mov r2, #256
215:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 215b
	movw r12, #4
	strb r12, [r7, #928]
	movw r12, #1
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #40960
	movt r1, #0
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #40960
	movt r1, #0
	add r1, r7, r1
	mov r2, #256
216:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 216b
	movw r12, #5
	strb r12, [r7, #928]
	movw r12, #1
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #41984
	movt r1, #0
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #41984
	movt r1, #0
	add r1, r7, r1
	mov r2, #256
217:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 217b
	movw r12, #6
	strb r12, [r7, #928]
	movw r12, #1
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #43008
	movt r1, #0
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #43008
	movt r1, #0
	add r1, r7, r1
	mov r2, #256
218:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 218b
	movw r12, #0
	strb r12, [r7, #928]
	movw r12, #2
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #45056
	movt r1, #0
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #45056
	movt r1, #0
	add r1, r7, r1
	mov r2, #256
219:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 219b
	movw r12, #1
	strb r12, [r7, #928]
	movw r12, #2
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #46080
	movt r1, #0
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #46080
	movt r1, #0
	add r1, r7, r1
	mov r2, #256
220:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 220b
	movw r12, #2
	strb r12, [r7, #928]
	movw r12, #2
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #47104
	movt r1, #0
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #47104
	movt r1, #0
	add r1, r7, r1
	mov r2, #256
221:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 221b
	movw r12, #3
	strb r12, [r7, #928]
	movw r12, #2
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #48128
	movt r1, #0
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #48128
	movt r1, #0
	add r1, r7, r1
	mov r2, #256
222:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 222b
	movw r12, #4
	strb r12, [r7, #928]
	movw r12, #2
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #49152
	movt r1, #0
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #49152
	movt r1, #0
	add r1, r7, r1
	mov r2, #256
223:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 223b
	movw r12, #5
	strb r12, [r7, #928]
	movw r12, #2
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #50176
	movt r1, #0
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #50176
	movt r1, #0
	add r1, r7, r1
	mov r2, #256
224:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 224b
	movw r12, #6
	strb r12, [r7, #928]
	movw r12, #2
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #51200
	movt r1, #0
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #51200
	movt r1, #0
	add r1, r7, r1
	mov r2, #256
225:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 225b
	movw r12, #0
	strb r12, [r7, #928]
	movw r12, #3
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #53248
	movt r1, #0
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #53248
	movt r1, #0
	add r1, r7, r1
	mov r2, #256
226:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 226b
	movw r12, #1
	strb r12, [r7, #928]
	movw r12, #3
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #54272
	movt r1, #0
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #54272
	movt r1, #0
	add r1, r7, r1
	mov r2, #256
227:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 227b
	movw r12, #2
	strb r12, [r7, #928]
	movw r12, #3
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #55296
	movt r1, #0
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #55296
	movt r1, #0
	add r1, r7, r1
	mov r2, #256
228:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 228b
	movw r12, #3
	strb r12, [r7, #928]
	movw r12, #3
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #56320
	movt r1, #0
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #56320
	movt r1, #0
	add r1, r7, r1
	mov r2, #256
229:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 229b
	movw r12, #4
	strb r12, [r7, #928]
	movw r12, #3
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #57344
	movt r1, #0
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #57344
	movt r1, #0
	add r1, r7, r1
	mov r2, #256
230:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 230b
	movw r12, #5
	strb r12, [r7, #928]
	movw r12, #3
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #58368
	movt r1, #0
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #58368
	movt r1, #0
	add r1, r7, r1
	mov r2, #256
231:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 231b
	movw r12, #6
	strb r12, [r7, #928]
	movw r12, #3
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #59392
	movt r1, #0
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #59392
	movt r1, #0
	add r1, r7, r1
	mov r2, #256
232:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 232b
	movw r12, #0
	strb r12, [r7, #928]
	movw r12, #4
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #61440
	movt r1, #0
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #61440
	movt r1, #0
	add r1, r7, r1
	mov r2, #256
233:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 233b
	movw r12, #1
	strb r12, [r7, #928]
	movw r12, #4
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #62464
	movt r1, #0
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #62464
	movt r1, #0
	add r1, r7, r1
	mov r2, #256
234:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 234b
	movw r12, #2
	strb r12, [r7, #928]
	movw r12, #4
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #63488
	movt r1, #0
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #63488
	movt r1, #0
	add r1, r7, r1
	mov r2, #256
235:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 235b
	movw r12, #3
	strb r12, [r7, #928]
	movw r12, #4
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #64512
	movt r1, #0
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #64512
	movt r1, #0
	add r1, r7, r1
	mov r2, #256
236:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 236b
	movw r12, #4
	strb r12, [r7, #928]
	movw r12, #4
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #0
	movt r1, #1
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #0
	movt r1, #1
	add r1, r7, r1
	mov r2, #256
237:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 237b
	movw r12, #5
	strb r12, [r7, #928]
	movw r12, #4
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #1024
	movt r1, #1
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #1024
	movt r1, #1
	add r1, r7, r1
	mov r2, #256
238:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 238b
	movw r12, #6
	strb r12, [r7, #928]
	movw r12, #4
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #2048
	movt r1, #1
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #2048
	movt r1, #1
	add r1, r7, r1
	mov r2, #256
239:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 239b
	movw r12, #0
	strb r12, [r7, #928]
	movw r12, #5
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #4096
	movt r1, #1
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #4096
	movt r1, #1
	add r1, r7, r1
	mov r2, #256
240:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 240b
	movw r12, #1
	strb r12, [r7, #928]
	movw r12, #5
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #5120
	movt r1, #1
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #5120
	movt r1, #1
	add r1, r7, r1
	mov r2, #256
241:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 241b
	movw r12, #2
	strb r12, [r7, #928]
	movw r12, #5
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #6144
	movt r1, #1
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #6144
	movt r1, #1
	add r1, r7, r1
	mov r2, #256
242:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 242b
	movw r12, #3
	strb r12, [r7, #928]
	movw r12, #5
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #7168
	movt r1, #1
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #7168
	movt r1, #1
	add r1, r7, r1
	mov r2, #256
243:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 243b
	movw r12, #4
	strb r12, [r7, #928]
	movw r12, #5
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #8192
	movt r1, #1
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #8192
	movt r1, #1
	add r1, r7, r1
	mov r2, #256
244:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 244b
	movw r12, #5
	strb r12, [r7, #928]
	movw r12, #5
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #9216
	movt r1, #1
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #9216
	movt r1, #1
	add r1, r7, r1
	mov r2, #256
245:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 245b
	movw r12, #6
	strb r12, [r7, #928]
	movw r12, #5
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #10240
	movt r1, #1
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #10240
	movt r1, #1
	add r1, r7, r1
	mov r2, #256
246:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 246b
	movw r12, #0
	strb r12, [r7, #928]
	movw r12, #6
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #12288
	movt r1, #1
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #12288
	movt r1, #1
	add r1, r7, r1
	mov r2, #256
247:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 247b
	movw r12, #1
	strb r12, [r7, #928]
	movw r12, #6
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #13312
	movt r1, #1
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #13312
	movt r1, #1
	add r1, r7, r1
	mov r2, #256
248:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 248b
	movw r12, #2
	strb r12, [r7, #928]
	movw r12, #6
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #14336
	movt r1, #1
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #14336
	movt r1, #1
	add r1, r7, r1
	mov r2, #256
249:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 249b
	movw r12, #3
	strb r12, [r7, #928]
	movw r12, #6
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #15360
	movt r1, #1
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #15360
	movt r1, #1
	add r1, r7, r1
	mov r2, #256
250:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 250b
	movw r12, #4
	strb r12, [r7, #928]
	movw r12, #6
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #16384
	movt r1, #1
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #16384
	movt r1, #1
	add r1, r7, r1
	mov r2, #256
251:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 251b
	movw r12, #5
	strb r12, [r7, #928]
	movw r12, #6
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #17408
	movt r1, #1
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #17408
	movt r1, #1
	add r1, r7, r1
	mov r2, #256
252:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 252b
	movw r12, #6
	strb r12, [r7, #928]
	movw r12, #6
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #18432
	movt r1, #1
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #18432
	movt r1, #1
	add r1, r7, r1
	mov r2, #256
253:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 253b
	movw r12, #0
	strb r12, [r7, #928]
	movw r12, #7
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #20480
	movt r1, #1
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #20480
	movt r1, #1
	add r1, r7, r1
	mov r2, #256
254:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 254b
	movw r12, #1
	strb r12, [r7, #928]
	movw r12, #7
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #21504
	movt r1, #1
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #21504
	movt r1, #1
	add r1, r7, r1
	mov r2, #256
255:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 255b
	movw r12, #2
	strb r12, [r7, #928]
	movw r12, #7
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #22528
	movt r1, #1
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #22528
	movt r1, #1
	add r1, r7, r1
	mov r2, #256
256:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 256b
	movw r12, #3
	strb r12, [r7, #928]
	movw r12, #7
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #23552
	movt r1, #1
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #23552
	movt r1, #1
	add r1, r7, r1
	mov r2, #256
257:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 257b
	movw r12, #4
	strb r12, [r7, #928]
	movw r12, #7
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #24576
	movt r1, #1
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #24576
	movt r1, #1
	add r1, r7, r1
	mov r2, #256
258:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 258b
	movw r12, #5
	strb r12, [r7, #928]
	movw r12, #7
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #25600
	movt r1, #1
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #25600
	movt r1, #1
	add r1, r7, r1
	mov r2, #256
259:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 259b
	movw r12, #6
	strb r12, [r7, #928]
	movw r12, #7
	strb r12, [r7, #929]
	movw r0, #896
	movt r0, #0
	add r0, r7, r0
	movw r1, #26624
	movt r1, #1
	add r1, r7, r1
	movw r2, #4096
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #26624
	movt r1, #1
	add r1, r7, r1
	mov r2, #256
260:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 260b
	movw r0, #0
	movt r0, #0
	add r0, r6, r0
	movw r1, #64
	movt r1, #0
	movw r2, #60
	movt r2, #0
	movw r3, #23552
	movt r3, #0
	add r3, r7, r3
	movw r12, #4096
	movt r12, #0
	add r12, r7, r12
	push {r12}
	bl {vg_mldsa_sample_in_ball}
	ldr r12, [sp], #4
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #23552
	movt r1, #0
	add r1, r7, r1
	mov r2, #256
261:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 261b
	movw r0, #16384
	movt r0, #0
	add r0, r7, r0
	movw r1, #4096
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #17408
	movt r0, #0
	add r0, r7, r0
	movw r1, #4096
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #18432
	movt r0, #0
	add r0, r7, r0
	movw r1, #4096
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #19456
	movt r0, #0
	add r0, r7, r0
	movw r1, #4096
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #20480
	movt r0, #0
	add r0, r7, r0
	movw r1, #4096
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #21504
	movt r0, #0
	add r0, r7, r0
	movw r1, #4096
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #22528
	movt r0, #0
	add r0, r7, r0
	movw r1, #4096
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #23552
	movt r0, #0
	add r0, r7, r0
	movw r1, #4096
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #28672
	movt r1, #0
	add r1, r7, r1
	movw r2, #16384
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #29696
	movt r1, #0
	add r1, r7, r1
	movw r2, #17408
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #30720
	movt r1, #0
	add r1, r7, r1
	movw r2, #18432
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #31744
	movt r1, #0
	add r1, r7, r1
	movw r2, #19456
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #32768
	movt r1, #0
	add r1, r7, r1
	movw r2, #20480
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #33792
	movt r1, #0
	add r1, r7, r1
	movw r2, #21504
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #34816
	movt r1, #0
	add r1, r7, r1
	movw r2, #22528
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	cmp r8, #0
	bne 262f
	movw r0, #32
	movt r0, #0
	add r0, r4, r0
	movw r1, #24576
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_unpack_t1}
	movw r0, #24576
	movt r0, #0
	add r0, r7, r0
	movw r1, #4096
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	b 263f
262:
	add r0, r8, #0
	add r1, r7, #24576
	mov r2, #1024
264:
	ldrb r3, [r0, #0]
	strb r3, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs r2, r2, #1
	bne 264b
263:
	movw r0, #25600
	movt r0, #0
	add r0, r7, r0
	movw r1, #23552
	movt r1, #0
	add r1, r7, r1
	movw r2, #24576
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #25600
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_sub}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #4096
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_inv_ntt}
	movw r0, #8192
	movt r0, #0
	add r0, r7, r0
	movw r1, #26624
	movt r1, #0
	add r1, r7, r1
	movw r2, #65280
	movt r2, #3
	movw r3, #27648
	movt r3, #0
	add r3, r7, r3
	bl {vg_mldsa_use_hint}
	movw r0, #27648
	movt r0, #0
	add r0, r7, r0
	movw r1, #15
	movt r1, #0
	movw r2, #1024
	movt r2, #0
	add r2, r7, r2
	movw r3, #128
	movt r3, #0
	bl {vg_mldsa_simple_bit_pack}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #36864
	movt r1, #0
	add r1, r7, r1
	movw r2, #16384
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #37888
	movt r1, #0
	add r1, r7, r1
	movw r2, #17408
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #38912
	movt r1, #0
	add r1, r7, r1
	movw r2, #18432
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #39936
	movt r1, #0
	add r1, r7, r1
	movw r2, #19456
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #40960
	movt r1, #0
	add r1, r7, r1
	movw r2, #20480
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #41984
	movt r1, #0
	add r1, r7, r1
	movw r2, #21504
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #43008
	movt r1, #0
	add r1, r7, r1
	movw r2, #22528
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	cmp r8, #0
	bne 265f
	movw r0, #352
	movt r0, #0
	add r0, r4, r0
	movw r1, #24576
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_unpack_t1}
	movw r0, #24576
	movt r0, #0
	add r0, r7, r0
	movw r1, #4096
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	b 266f
265:
	add r0, r8, #1024
	add r1, r7, #24576
	mov r2, #1024
267:
	ldrb r3, [r0, #0]
	strb r3, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs r2, r2, #1
	bne 267b
266:
	movw r0, #25600
	movt r0, #0
	add r0, r7, r0
	movw r1, #23552
	movt r1, #0
	add r1, r7, r1
	movw r2, #24576
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #25600
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_sub}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #4096
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_inv_ntt}
	movw r0, #9216
	movt r0, #0
	add r0, r7, r0
	movw r1, #26624
	movt r1, #0
	add r1, r7, r1
	movw r2, #65280
	movt r2, #3
	movw r3, #27648
	movt r3, #0
	add r3, r7, r3
	bl {vg_mldsa_use_hint}
	movw r0, #27648
	movt r0, #0
	add r0, r7, r0
	movw r1, #15
	movt r1, #0
	movw r2, #1152
	movt r2, #0
	add r2, r7, r2
	movw r3, #128
	movt r3, #0
	bl {vg_mldsa_simple_bit_pack}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #45056
	movt r1, #0
	add r1, r7, r1
	movw r2, #16384
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #46080
	movt r1, #0
	add r1, r7, r1
	movw r2, #17408
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #47104
	movt r1, #0
	add r1, r7, r1
	movw r2, #18432
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #48128
	movt r1, #0
	add r1, r7, r1
	movw r2, #19456
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #49152
	movt r1, #0
	add r1, r7, r1
	movw r2, #20480
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #50176
	movt r1, #0
	add r1, r7, r1
	movw r2, #21504
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #51200
	movt r1, #0
	add r1, r7, r1
	movw r2, #22528
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	cmp r8, #0
	bne 268f
	movw r0, #672
	movt r0, #0
	add r0, r4, r0
	movw r1, #24576
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_unpack_t1}
	movw r0, #24576
	movt r0, #0
	add r0, r7, r0
	movw r1, #4096
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	b 269f
268:
	add r0, r8, #2048
	add r1, r7, #24576
	mov r2, #1024
270:
	ldrb r3, [r0, #0]
	strb r3, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs r2, r2, #1
	bne 270b
269:
	movw r0, #25600
	movt r0, #0
	add r0, r7, r0
	movw r1, #23552
	movt r1, #0
	add r1, r7, r1
	movw r2, #24576
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #25600
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_sub}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #4096
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_inv_ntt}
	movw r0, #10240
	movt r0, #0
	add r0, r7, r0
	movw r1, #26624
	movt r1, #0
	add r1, r7, r1
	movw r2, #65280
	movt r2, #3
	movw r3, #27648
	movt r3, #0
	add r3, r7, r3
	bl {vg_mldsa_use_hint}
	movw r0, #27648
	movt r0, #0
	add r0, r7, r0
	movw r1, #15
	movt r1, #0
	movw r2, #1280
	movt r2, #0
	add r2, r7, r2
	movw r3, #128
	movt r3, #0
	bl {vg_mldsa_simple_bit_pack}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #53248
	movt r1, #0
	add r1, r7, r1
	movw r2, #16384
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #54272
	movt r1, #0
	add r1, r7, r1
	movw r2, #17408
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #55296
	movt r1, #0
	add r1, r7, r1
	movw r2, #18432
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #56320
	movt r1, #0
	add r1, r7, r1
	movw r2, #19456
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #57344
	movt r1, #0
	add r1, r7, r1
	movw r2, #20480
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #58368
	movt r1, #0
	add r1, r7, r1
	movw r2, #21504
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #59392
	movt r1, #0
	add r1, r7, r1
	movw r2, #22528
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	cmp r8, #0
	bne 271f
	movw r0, #992
	movt r0, #0
	add r0, r4, r0
	movw r1, #24576
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_unpack_t1}
	movw r0, #24576
	movt r0, #0
	add r0, r7, r0
	movw r1, #4096
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	b 272f
271:
	add r0, r8, #3072
	add r1, r7, #24576
	mov r2, #1024
273:
	ldrb r3, [r0, #0]
	strb r3, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs r2, r2, #1
	bne 273b
272:
	movw r0, #25600
	movt r0, #0
	add r0, r7, r0
	movw r1, #23552
	movt r1, #0
	add r1, r7, r1
	movw r2, #24576
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #25600
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_sub}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #4096
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_inv_ntt}
	movw r0, #11264
	movt r0, #0
	add r0, r7, r0
	movw r1, #26624
	movt r1, #0
	add r1, r7, r1
	movw r2, #65280
	movt r2, #3
	movw r3, #27648
	movt r3, #0
	add r3, r7, r3
	bl {vg_mldsa_use_hint}
	movw r0, #27648
	movt r0, #0
	add r0, r7, r0
	movw r1, #15
	movt r1, #0
	movw r2, #1408
	movt r2, #0
	add r2, r7, r2
	movw r3, #128
	movt r3, #0
	bl {vg_mldsa_simple_bit_pack}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #61440
	movt r1, #0
	add r1, r7, r1
	movw r2, #16384
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #62464
	movt r1, #0
	add r1, r7, r1
	movw r2, #17408
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #63488
	movt r1, #0
	add r1, r7, r1
	movw r2, #18432
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #64512
	movt r1, #0
	add r1, r7, r1
	movw r2, #19456
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #0
	movt r1, #1
	add r1, r7, r1
	movw r2, #20480
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #1024
	movt r1, #1
	add r1, r7, r1
	movw r2, #21504
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #2048
	movt r1, #1
	add r1, r7, r1
	movw r2, #22528
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	cmp r8, #0
	bne 274f
	movw r0, #1312
	movt r0, #0
	add r0, r4, r0
	movw r1, #24576
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_unpack_t1}
	movw r0, #24576
	movt r0, #0
	add r0, r7, r0
	movw r1, #4096
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	b 275f
274:
	add r0, r8, #4096
	add r1, r7, #24576
	mov r2, #1024
276:
	ldrb r3, [r0, #0]
	strb r3, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs r2, r2, #1
	bne 276b
275:
	movw r0, #25600
	movt r0, #0
	add r0, r7, r0
	movw r1, #23552
	movt r1, #0
	add r1, r7, r1
	movw r2, #24576
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #25600
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_sub}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #4096
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_inv_ntt}
	movw r0, #12288
	movt r0, #0
	add r0, r7, r0
	movw r1, #26624
	movt r1, #0
	add r1, r7, r1
	movw r2, #65280
	movt r2, #3
	movw r3, #27648
	movt r3, #0
	add r3, r7, r3
	bl {vg_mldsa_use_hint}
	movw r0, #27648
	movt r0, #0
	add r0, r7, r0
	movw r1, #15
	movt r1, #0
	movw r2, #1536
	movt r2, #0
	add r2, r7, r2
	movw r3, #128
	movt r3, #0
	bl {vg_mldsa_simple_bit_pack}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #4096
	movt r1, #1
	add r1, r7, r1
	movw r2, #16384
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #5120
	movt r1, #1
	add r1, r7, r1
	movw r2, #17408
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #6144
	movt r1, #1
	add r1, r7, r1
	movw r2, #18432
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #7168
	movt r1, #1
	add r1, r7, r1
	movw r2, #19456
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #8192
	movt r1, #1
	add r1, r7, r1
	movw r2, #20480
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #9216
	movt r1, #1
	add r1, r7, r1
	movw r2, #21504
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #10240
	movt r1, #1
	add r1, r7, r1
	movw r2, #22528
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	cmp r8, #0
	bne 277f
	movw r0, #1632
	movt r0, #0
	add r0, r4, r0
	movw r1, #24576
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_unpack_t1}
	movw r0, #24576
	movt r0, #0
	add r0, r7, r0
	movw r1, #4096
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	b 278f
277:
	add r0, r8, #5120
	add r1, r7, #24576
	mov r2, #1024
279:
	ldrb r3, [r0, #0]
	strb r3, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs r2, r2, #1
	bne 279b
278:
	movw r0, #25600
	movt r0, #0
	add r0, r7, r0
	movw r1, #23552
	movt r1, #0
	add r1, r7, r1
	movw r2, #24576
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #25600
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_sub}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #4096
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_inv_ntt}
	movw r0, #13312
	movt r0, #0
	add r0, r7, r0
	movw r1, #26624
	movt r1, #0
	add r1, r7, r1
	movw r2, #65280
	movt r2, #3
	movw r3, #27648
	movt r3, #0
	add r3, r7, r3
	bl {vg_mldsa_use_hint}
	movw r0, #27648
	movt r0, #0
	add r0, r7, r0
	movw r1, #15
	movt r1, #0
	movw r2, #1664
	movt r2, #0
	add r2, r7, r2
	movw r3, #128
	movt r3, #0
	bl {vg_mldsa_simple_bit_pack}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #12288
	movt r1, #1
	add r1, r7, r1
	movw r2, #16384
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #13312
	movt r1, #1
	add r1, r7, r1
	movw r2, #17408
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #14336
	movt r1, #1
	add r1, r7, r1
	movw r2, #18432
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #15360
	movt r1, #1
	add r1, r7, r1
	movw r2, #19456
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #16384
	movt r1, #1
	add r1, r7, r1
	movw r2, #20480
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #17408
	movt r1, #1
	add r1, r7, r1
	movw r2, #21504
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #18432
	movt r1, #1
	add r1, r7, r1
	movw r2, #22528
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	cmp r8, #0
	bne 280f
	movw r0, #1952
	movt r0, #0
	add r0, r4, r0
	movw r1, #24576
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_unpack_t1}
	movw r0, #24576
	movt r0, #0
	add r0, r7, r0
	movw r1, #4096
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	b 281f
280:
	add r0, r8, #6144
	add r1, r7, #24576
	mov r2, #1024
282:
	ldrb r3, [r0, #0]
	strb r3, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs r2, r2, #1
	bne 282b
281:
	movw r0, #25600
	movt r0, #0
	add r0, r7, r0
	movw r1, #23552
	movt r1, #0
	add r1, r7, r1
	movw r2, #24576
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #25600
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_sub}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #4096
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_inv_ntt}
	movw r0, #14336
	movt r0, #0
	add r0, r7, r0
	movw r1, #26624
	movt r1, #0
	add r1, r7, r1
	movw r2, #65280
	movt r2, #3
	movw r3, #27648
	movt r3, #0
	add r3, r7, r3
	bl {vg_mldsa_use_hint}
	movw r0, #27648
	movt r0, #0
	add r0, r7, r0
	movw r1, #15
	movt r1, #0
	movw r2, #1792
	movt r2, #0
	add r2, r7, r2
	movw r3, #128
	movt r3, #0
	bl {vg_mldsa_simple_bit_pack}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #20480
	movt r1, #1
	add r1, r7, r1
	movw r2, #16384
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #21504
	movt r1, #1
	add r1, r7, r1
	movw r2, #17408
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #22528
	movt r1, #1
	add r1, r7, r1
	movw r2, #18432
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #23552
	movt r1, #1
	add r1, r7, r1
	movw r2, #19456
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #24576
	movt r1, #1
	add r1, r7, r1
	movw r2, #20480
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #25600
	movt r1, #1
	add r1, r7, r1
	movw r2, #21504
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #26624
	movt r1, #1
	add r1, r7, r1
	movw r2, #22528
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	cmp r8, #0
	bne 283f
	movw r0, #2272
	movt r0, #0
	add r0, r4, r0
	movw r1, #24576
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_unpack_t1}
	movw r0, #24576
	movt r0, #0
	add r0, r7, r0
	movw r1, #4096
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	b 284f
283:
	add r0, r8, #7168
	add r1, r7, #24576
	mov r2, #1024
285:
	ldrb r3, [r0, #0]
	strb r3, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs r2, r2, #1
	bne 285b
284:
	movw r0, #25600
	movt r0, #0
	add r0, r7, r0
	movw r1, #23552
	movt r1, #0
	add r1, r7, r1
	movw r2, #24576
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_ntt}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #25600
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_sub}
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #4096
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_inv_ntt}
	movw r0, #15360
	movt r0, #0
	add r0, r7, r0
	movw r1, #26624
	movt r1, #0
	add r1, r7, r1
	movw r2, #65280
	movt r2, #3
	movw r3, #27648
	movt r3, #0
	add r3, r7, r3
	bl {vg_mldsa_use_hint}
	movw r0, #27648
	movt r0, #0
	add r0, r7, r0
	movw r1, #15
	movt r1, #0
	movw r2, #1920
	movt r2, #0
	add r2, r7, r2
	movw r3, #128
	movt r3, #0
	bl {vg_mldsa_simple_bit_pack}
	mov r12, #0
	str r12, [r7, #0]
	str r12, [r7, #4]
	str r12, [r7, #8]
	str r12, [r7, #12]
	str r12, [r7, #16]
	str r12, [r7, #20]
	str r12, [r7, #24]
	str r12, [r7, #28]
	str r12, [r7, #32]
	str r12, [r7, #36]
	str r12, [r7, #40]
	str r12, [r7, #44]
	str r12, [r7, #48]
	str r12, [r7, #52]
	str r12, [r7, #56]
	str r12, [r7, #60]
	str r12, [r7, #64]
	str r12, [r7, #68]
	str r12, [r7, #72]
	str r12, [r7, #76]
	str r12, [r7, #80]
	str r12, [r7, #84]
	str r12, [r7, #88]
	str r12, [r7, #92]
	str r12, [r7, #96]
	str r12, [r7, #100]
	str r12, [r7, #104]
	str r12, [r7, #108]
	str r12, [r7, #112]
	str r12, [r7, #116]
	str r12, [r7, #120]
	str r12, [r7, #124]
	str r12, [r7, #128]
	str r12, [r7, #132]
	str r12, [r7, #136]
	str r12, [r7, #140]
	str r12, [r7, #144]
	str r12, [r7, #148]
	str r12, [r7, #152]
	str r12, [r7, #156]
	str r12, [r7, #160]
	str r12, [r7, #164]
	str r12, [r7, #168]
	str r12, [r7, #172]
	str r12, [r7, #176]
	str r12, [r7, #180]
	str r12, [r7, #184]
	str r12, [r7, #188]
	str r12, [r7, #192]
	str r12, [r7, #196]
	mov r2, #0
	mov r0, r7
	mov r1, #136
	add lr, r7, #200
	add r3, r5, #0
	mov r12, #64
	push {r12, lr}
	bl {vg_keccak_absorb_scratch}
	ldr r12, [sp], #8
	mov r2, r0
	mov r0, r7
	mov r1, #136
	add lr, r7, #200
	add r3, r7, #1024
	mov r12, #1024
	push {r12, lr}
	bl {vg_keccak_absorb_scratch}
	ldr r12, [sp], #8
	mov r2, r0
	mov r0, r7
	mov r1, #136
	add lr, r7, #200
	mov r3, #31
	push {lr}
	bl {vg_keccak_pad_scratch}
	ldr r12, [sp], #4
	mov r2, #0
	mov r0, r7
	mov r1, #136
	add lr, r7, #200
	add r3, r7, #2048
	mov r12, #64
	push {r12, lr}
	bl {vg_keccak_squeeze_scratch}
	ldr r12, [sp], #8
	movw r0, #2048
	movt r0, #0
	add r0, r7, r0
	movw r1, #0
	movt r1, #0
	add r1, r6, r1
	movw r9, #64
	movt r9, #0
	mov r12, #0
286:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	orr r12, r12, r2
	add r0, r0, #1
	add r1, r1, #1
	subs r9, r9, #1
	bne 286b
	sub r12, r12, #1
	lsr r12, r12, #31
	and r11, r11, r12
23:
21:
	mov r0, r11
	mov r3, r7
	ldr r4, [r3, #840]
	ldr r5, [r3, #844]
	ldr r6, [r3, #848]
	ldr r7, [r3, #852]
	ldr r8, [r3, #856]
	ldr r9, [r3, #860]
	ldr r10, [r3, #864]
	ldr r11, [r3, #868]
	ldr lr, [r3, #872]
	bx lr
