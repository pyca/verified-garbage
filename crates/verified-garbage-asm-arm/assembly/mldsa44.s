// The functions of `src/mldsa44.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa44_keygen:
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
	movw r12, #4
	strb r12, [r7, #896]
	movw r12, #4
	strb r12, [r7, #897]
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
	add r3, r4, #0
	mov r12, #32
	push {r12, lr}
	bl {vg_keccak_absorb_scratch}
	ldr r12, [sp], #8
	mov r2, r0
	mov r0, r7
	mov r1, #136
	add lr, r7, #200
	add r3, r7, #896
	mov r12, #2
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
	add r3, r7, #1024
	mov r12, #128
	push {r12, lr}
	bl {vg_keccak_squeeze_scratch}
	ldr r12, [sp], #8
	add r0, r7, #1024
	add r1, r7, #1152
	mov r2, #32
20:
	ldrb r3, [r0, #0]
	strb r3, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs r2, r2, #1
	bne 20b
	add r0, r7, #1056
	add r1, r7, #1216
	mov r2, #64
21:
	ldrb r3, [r0, #0]
	strb r3, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs r2, r2, #1
	bne 21b
	movw r12, #0
	strb r12, [r7, #1281]
	movw r12, #0
	strb r12, [r7, #1184]
	movw r12, #0
	strb r12, [r7, #1185]
	movw r0, #1152
	movt r0, #0
	add r0, r7, r0
	movw r1, #4096
	movt r1, #0
	add r1, r7, r1
	movw r2, #2048
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #4096
	movt r1, #0
	add r1, r7, r1
	mov r2, #256
22:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 22b
	movw r12, #1
	strb r12, [r7, #1184]
	movw r12, #0
	strb r12, [r7, #1185]
	movw r0, #1152
	movt r0, #0
	add r0, r7, r0
	movw r1, #5120
	movt r1, #0
	add r1, r7, r1
	movw r2, #2048
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #5120
	movt r1, #0
	add r1, r7, r1
	mov r2, #256
23:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 23b
	movw r12, #2
	strb r12, [r7, #1184]
	movw r12, #0
	strb r12, [r7, #1185]
	movw r0, #1152
	movt r0, #0
	add r0, r7, r0
	movw r1, #6144
	movt r1, #0
	add r1, r7, r1
	movw r2, #2048
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #6144
	movt r1, #0
	add r1, r7, r1
	mov r2, #256
24:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 24b
	movw r12, #3
	strb r12, [r7, #1184]
	movw r12, #0
	strb r12, [r7, #1185]
	movw r0, #1152
	movt r0, #0
	add r0, r7, r0
	movw r1, #7168
	movt r1, #0
	add r1, r7, r1
	movw r2, #2048
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #7168
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
	movw r12, #0
	strb r12, [r7, #1184]
	movw r12, #1
	strb r12, [r7, #1185]
	movw r0, #1152
	movt r0, #0
	add r0, r7, r0
	movw r1, #8192
	movt r1, #0
	add r1, r7, r1
	movw r2, #2048
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #8192
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
	movw r12, #1
	strb r12, [r7, #1184]
	movw r12, #1
	strb r12, [r7, #1185]
	movw r0, #1152
	movt r0, #0
	add r0, r7, r0
	movw r1, #9216
	movt r1, #0
	add r1, r7, r1
	movw r2, #2048
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #9216
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
	movw r12, #2
	strb r12, [r7, #1184]
	movw r12, #1
	strb r12, [r7, #1185]
	movw r0, #1152
	movt r0, #0
	add r0, r7, r0
	movw r1, #10240
	movt r1, #0
	add r1, r7, r1
	movw r2, #2048
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #10240
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
	movw r12, #3
	strb r12, [r7, #1184]
	movw r12, #1
	strb r12, [r7, #1185]
	movw r0, #1152
	movt r0, #0
	add r0, r7, r0
	movw r1, #11264
	movt r1, #0
	add r1, r7, r1
	movw r2, #2048
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #11264
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
	movw r12, #0
	strb r12, [r7, #1184]
	movw r12, #2
	strb r12, [r7, #1185]
	movw r0, #1152
	movt r0, #0
	add r0, r7, r0
	movw r1, #12288
	movt r1, #0
	add r1, r7, r1
	movw r2, #2048
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #12288
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
	movw r12, #1
	strb r12, [r7, #1184]
	movw r12, #2
	strb r12, [r7, #1185]
	movw r0, #1152
	movt r0, #0
	add r0, r7, r0
	movw r1, #13312
	movt r1, #0
	add r1, r7, r1
	movw r2, #2048
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #13312
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
	movw r12, #2
	strb r12, [r7, #1184]
	movw r12, #2
	strb r12, [r7, #1185]
	movw r0, #1152
	movt r0, #0
	add r0, r7, r0
	movw r1, #14336
	movt r1, #0
	add r1, r7, r1
	movw r2, #2048
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #14336
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
	movw r12, #3
	strb r12, [r7, #1184]
	movw r12, #2
	strb r12, [r7, #1185]
	movw r0, #1152
	movt r0, #0
	add r0, r7, r0
	movw r1, #15360
	movt r1, #0
	add r1, r7, r1
	movw r2, #2048
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #15360
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
	movw r12, #0
	strb r12, [r7, #1184]
	movw r12, #3
	strb r12, [r7, #1185]
	movw r0, #1152
	movt r0, #0
	add r0, r7, r0
	movw r1, #16384
	movt r1, #0
	add r1, r7, r1
	movw r2, #2048
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #16384
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
	movw r12, #1
	strb r12, [r7, #1184]
	movw r12, #3
	strb r12, [r7, #1185]
	movw r0, #1152
	movt r0, #0
	add r0, r7, r0
	movw r1, #17408
	movt r1, #0
	add r1, r7, r1
	movw r2, #2048
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #17408
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
	movw r12, #2
	strb r12, [r7, #1184]
	movw r12, #3
	strb r12, [r7, #1185]
	movw r0, #1152
	movt r0, #0
	add r0, r7, r0
	movw r1, #18432
	movt r1, #0
	add r1, r7, r1
	movw r2, #2048
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #18432
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
	movw r12, #3
	strb r12, [r7, #1184]
	movw r12, #3
	strb r12, [r7, #1185]
	movw r0, #1152
	movt r0, #0
	add r0, r7, r0
	movw r1, #19456
	movt r1, #0
	add r1, r7, r1
	movw r2, #2048
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #19456
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
	movw r12, #0
	strb r12, [r7, #1280]
	movw r0, #1216
	movt r0, #0
	add r0, r7, r0
	movw r1, #2
	movt r1, #0
	movw r2, #20480
	movt r2, #0
	add r2, r7, r2
	movw r3, #2048
	movt r3, #0
	add r3, r7, r3
	bl {vg_mldsa_rej_bounded_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #20480
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
	movw r12, #1
	strb r12, [r7, #1280]
	movw r0, #1216
	movt r0, #0
	add r0, r7, r0
	movw r1, #2
	movt r1, #0
	movw r2, #21504
	movt r2, #0
	add r2, r7, r2
	movw r3, #2048
	movt r3, #0
	add r3, r7, r3
	bl {vg_mldsa_rej_bounded_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #21504
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
	movw r12, #2
	strb r12, [r7, #1280]
	movw r0, #1216
	movt r0, #0
	add r0, r7, r0
	movw r1, #2
	movt r1, #0
	movw r2, #22528
	movt r2, #0
	add r2, r7, r2
	movw r3, #2048
	movt r3, #0
	add r3, r7, r3
	bl {vg_mldsa_rej_bounded_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #22528
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
	movw r12, #3
	strb r12, [r7, #1280]
	movw r0, #1216
	movt r0, #0
	add r0, r7, r0
	movw r1, #2
	movt r1, #0
	movw r2, #23552
	movt r2, #0
	add r2, r7, r2
	movw r3, #2048
	movt r3, #0
	add r3, r7, r3
	bl {vg_mldsa_rej_bounded_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #23552
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
	movw r12, #4
	strb r12, [r7, #1280]
	movw r0, #1216
	movt r0, #0
	add r0, r7, r0
	movw r1, #2
	movt r1, #0
	movw r2, #24576
	movt r2, #0
	add r2, r7, r2
	movw r3, #2048
	movt r3, #0
	add r3, r7, r3
	bl {vg_mldsa_rej_bounded_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #24576
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
	movw r12, #5
	strb r12, [r7, #1280]
	movw r0, #1216
	movt r0, #0
	add r0, r7, r0
	movw r1, #2
	movt r1, #0
	movw r2, #25600
	movt r2, #0
	add r2, r7, r2
	movw r3, #2048
	movt r3, #0
	add r3, r7, r3
	bl {vg_mldsa_rej_bounded_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #25600
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
	movw r12, #6
	strb r12, [r7, #1280]
	movw r0, #1216
	movt r0, #0
	add r0, r7, r0
	movw r1, #2
	movt r1, #0
	movw r2, #26624
	movt r2, #0
	add r2, r7, r2
	movw r3, #2048
	movt r3, #0
	add r3, r7, r3
	bl {vg_mldsa_rej_bounded_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #26624
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
	movw r12, #7
	strb r12, [r7, #1280]
	movw r0, #1216
	movt r0, #0
	add r0, r7, r0
	movw r1, #2
	movt r1, #0
	movw r2, #27648
	movt r2, #0
	add r2, r7, r2
	movw r3, #2048
	movt r3, #0
	add r3, r7, r3
	bl {vg_mldsa_rej_bounded_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #27648
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
	add r0, r7, #1024
	add r1, r5, #0
	mov r2, #32
226:
	ldrb r3, [r0, #0]
	strb r3, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs r2, r2, #1
	bne 226b
	add r0, r7, #1024
	add r1, r6, #0
	mov r2, #32
227:
	ldrb r3, [r0, #0]
	strb r3, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs r2, r2, #1
	bne 227b
	add r0, r7, #1120
	add r1, r6, #32
	mov r2, #32
228:
	ldrb r3, [r0, #0]
	strb r3, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs r2, r2, #1
	bne 228b
	movw r0, #20480
	movt r0, #0
	add r0, r7, r0
	movw r1, #2
	movt r1, #0
	movw r2, #2
	movt r2, #0
	movw r3, #128
	movt r3, #0
	add r3, r6, r3
	movw r12, #96
	movt r12, #0
	push {r12}
	bl {vg_mldsa_bit_pack}
	ldr r12, [sp], #4
	movw r0, #21504
	movt r0, #0
	add r0, r7, r0
	movw r1, #2
	movt r1, #0
	movw r2, #2
	movt r2, #0
	movw r3, #224
	movt r3, #0
	add r3, r6, r3
	movw r12, #96
	movt r12, #0
	push {r12}
	bl {vg_mldsa_bit_pack}
	ldr r12, [sp], #4
	movw r0, #22528
	movt r0, #0
	add r0, r7, r0
	movw r1, #2
	movt r1, #0
	movw r2, #2
	movt r2, #0
	movw r3, #320
	movt r3, #0
	add r3, r6, r3
	movw r12, #96
	movt r12, #0
	push {r12}
	bl {vg_mldsa_bit_pack}
	ldr r12, [sp], #4
	movw r0, #23552
	movt r0, #0
	add r0, r7, r0
	movw r1, #2
	movt r1, #0
	movw r2, #2
	movt r2, #0
	movw r3, #416
	movt r3, #0
	add r3, r6, r3
	movw r12, #96
	movt r12, #0
	push {r12}
	bl {vg_mldsa_bit_pack}
	ldr r12, [sp], #4
	movw r0, #24576
	movt r0, #0
	add r0, r7, r0
	movw r1, #2
	movt r1, #0
	movw r2, #2
	movt r2, #0
	movw r3, #512
	movt r3, #0
	add r3, r6, r3
	movw r12, #96
	movt r12, #0
	push {r12}
	bl {vg_mldsa_bit_pack}
	ldr r12, [sp], #4
	movw r0, #25600
	movt r0, #0
	add r0, r7, r0
	movw r1, #2
	movt r1, #0
	movw r2, #2
	movt r2, #0
	movw r3, #608
	movt r3, #0
	add r3, r6, r3
	movw r12, #96
	movt r12, #0
	push {r12}
	bl {vg_mldsa_bit_pack}
	ldr r12, [sp], #4
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #2
	movt r1, #0
	movw r2, #2
	movt r2, #0
	movw r3, #704
	movt r3, #0
	add r3, r6, r3
	movw r12, #96
	movt r12, #0
	push {r12}
	bl {vg_mldsa_bit_pack}
	ldr r12, [sp], #4
	movw r0, #27648
	movt r0, #0
	add r0, r7, r0
	movw r1, #2
	movt r1, #0
	movw r2, #2
	movt r2, #0
	movw r3, #800
	movt r3, #0
	add r3, r6, r3
	movw r12, #96
	movt r12, #0
	push {r12}
	bl {vg_mldsa_bit_pack}
	ldr r12, [sp], #4
	movw r0, #20480
	movt r0, #0
	add r0, r7, r0
	movw r1, #2048
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #21504
	movt r0, #0
	add r0, r7, r0
	movw r1, #2048
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #22528
	movt r0, #0
	add r0, r7, r0
	movw r1, #2048
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #23552
	movt r0, #0
	add r0, r7, r0
	movw r1, #2048
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #28672
	movt r0, #0
	add r0, r7, r0
	movw r1, #4096
	movt r1, #0
	add r1, r7, r1
	movw r2, #20480
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_ntt}
	movw r0, #28672
	movt r0, #0
	add r0, r7, r0
	movw r1, #5120
	movt r1, #0
	add r1, r7, r1
	movw r2, #21504
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #28672
	movt r0, #0
	add r0, r7, r0
	movw r1, #6144
	movt r1, #0
	add r1, r7, r1
	movw r2, #22528
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #28672
	movt r0, #0
	add r0, r7, r0
	movw r1, #7168
	movt r1, #0
	add r1, r7, r1
	movw r2, #23552
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #28672
	movt r0, #0
	add r0, r7, r0
	movw r1, #2048
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_inv_ntt}
	movw r0, #28672
	movt r0, #0
	add r0, r7, r0
	movw r1, #24576
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_add}
	movw r0, #28672
	movt r0, #0
	add r0, r7, r0
	movw r1, #29696
	movt r1, #0
	add r1, r7, r1
	movw r2, #30720
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_power2round}
	movw r0, #29696
	movt r0, #0
	add r0, r7, r0
	movw r1, #1023
	movt r1, #0
	movw r2, #32
	movt r2, #0
	add r2, r5, r2
	movw r3, #320
	movt r3, #0
	bl {vg_mldsa_simple_bit_pack}
	movw r0, #30720
	movt r0, #0
	add r0, r7, r0
	movw r1, #4095
	movt r1, #0
	movw r2, #4096
	movt r2, #0
	movw r3, #896
	movt r3, #0
	add r3, r6, r3
	movw r12, #416
	movt r12, #0
	push {r12}
	bl {vg_mldsa_bit_pack}
	ldr r12, [sp], #4
	movw r0, #28672
	movt r0, #0
	add r0, r7, r0
	movw r1, #8192
	movt r1, #0
	add r1, r7, r1
	movw r2, #20480
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_ntt}
	movw r0, #28672
	movt r0, #0
	add r0, r7, r0
	movw r1, #9216
	movt r1, #0
	add r1, r7, r1
	movw r2, #21504
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #28672
	movt r0, #0
	add r0, r7, r0
	movw r1, #10240
	movt r1, #0
	add r1, r7, r1
	movw r2, #22528
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #28672
	movt r0, #0
	add r0, r7, r0
	movw r1, #11264
	movt r1, #0
	add r1, r7, r1
	movw r2, #23552
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #28672
	movt r0, #0
	add r0, r7, r0
	movw r1, #2048
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_inv_ntt}
	movw r0, #28672
	movt r0, #0
	add r0, r7, r0
	movw r1, #25600
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_add}
	movw r0, #28672
	movt r0, #0
	add r0, r7, r0
	movw r1, #29696
	movt r1, #0
	add r1, r7, r1
	movw r2, #30720
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_power2round}
	movw r0, #29696
	movt r0, #0
	add r0, r7, r0
	movw r1, #1023
	movt r1, #0
	movw r2, #352
	movt r2, #0
	add r2, r5, r2
	movw r3, #320
	movt r3, #0
	bl {vg_mldsa_simple_bit_pack}
	movw r0, #30720
	movt r0, #0
	add r0, r7, r0
	movw r1, #4095
	movt r1, #0
	movw r2, #4096
	movt r2, #0
	movw r3, #1312
	movt r3, #0
	add r3, r6, r3
	movw r12, #416
	movt r12, #0
	push {r12}
	bl {vg_mldsa_bit_pack}
	ldr r12, [sp], #4
	movw r0, #28672
	movt r0, #0
	add r0, r7, r0
	movw r1, #12288
	movt r1, #0
	add r1, r7, r1
	movw r2, #20480
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_ntt}
	movw r0, #28672
	movt r0, #0
	add r0, r7, r0
	movw r1, #13312
	movt r1, #0
	add r1, r7, r1
	movw r2, #21504
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #28672
	movt r0, #0
	add r0, r7, r0
	movw r1, #14336
	movt r1, #0
	add r1, r7, r1
	movw r2, #22528
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #28672
	movt r0, #0
	add r0, r7, r0
	movw r1, #15360
	movt r1, #0
	add r1, r7, r1
	movw r2, #23552
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #28672
	movt r0, #0
	add r0, r7, r0
	movw r1, #2048
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_inv_ntt}
	movw r0, #28672
	movt r0, #0
	add r0, r7, r0
	movw r1, #26624
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_add}
	movw r0, #28672
	movt r0, #0
	add r0, r7, r0
	movw r1, #29696
	movt r1, #0
	add r1, r7, r1
	movw r2, #30720
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_power2round}
	movw r0, #29696
	movt r0, #0
	add r0, r7, r0
	movw r1, #1023
	movt r1, #0
	movw r2, #672
	movt r2, #0
	add r2, r5, r2
	movw r3, #320
	movt r3, #0
	bl {vg_mldsa_simple_bit_pack}
	movw r0, #30720
	movt r0, #0
	add r0, r7, r0
	movw r1, #4095
	movt r1, #0
	movw r2, #4096
	movt r2, #0
	movw r3, #1728
	movt r3, #0
	add r3, r6, r3
	movw r12, #416
	movt r12, #0
	push {r12}
	bl {vg_mldsa_bit_pack}
	ldr r12, [sp], #4
	movw r0, #28672
	movt r0, #0
	add r0, r7, r0
	movw r1, #16384
	movt r1, #0
	add r1, r7, r1
	movw r2, #20480
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_ntt}
	movw r0, #28672
	movt r0, #0
	add r0, r7, r0
	movw r1, #17408
	movt r1, #0
	add r1, r7, r1
	movw r2, #21504
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #28672
	movt r0, #0
	add r0, r7, r0
	movw r1, #18432
	movt r1, #0
	add r1, r7, r1
	movw r2, #22528
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #28672
	movt r0, #0
	add r0, r7, r0
	movw r1, #19456
	movt r1, #0
	add r1, r7, r1
	movw r2, #23552
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #28672
	movt r0, #0
	add r0, r7, r0
	movw r1, #2048
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_inv_ntt}
	movw r0, #28672
	movt r0, #0
	add r0, r7, r0
	movw r1, #27648
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_add}
	movw r0, #28672
	movt r0, #0
	add r0, r7, r0
	movw r1, #29696
	movt r1, #0
	add r1, r7, r1
	movw r2, #30720
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_power2round}
	movw r0, #29696
	movt r0, #0
	add r0, r7, r0
	movw r1, #1023
	movt r1, #0
	movw r2, #992
	movt r2, #0
	add r2, r5, r2
	movw r3, #320
	movt r3, #0
	bl {vg_mldsa_simple_bit_pack}
	movw r0, #30720
	movt r0, #0
	add r0, r7, r0
	movw r1, #4095
	movt r1, #0
	movw r2, #4096
	movt r2, #0
	movw r3, #2144
	movt r3, #0
	add r3, r6, r3
	movw r12, #416
	movt r12, #0
	push {r12}
	bl {vg_mldsa_bit_pack}
	ldr r12, [sp], #4
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
	mov r12, #1312
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
	add r3, r6, #64
	mov r12, #64
	push {r12, lr}
	bl {vg_keccak_squeeze_scratch}
	ldr r12, [sp], #8
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

vg_mldsa44_sign:
	ldr r12, [sp, #0]
	str r4, [r12, #840]
	str r5, [r12, #844]
	str r6, [r12, #848]
	str r7, [r12, #852]
	str r8, [r12, #856]
	str r9, [r12, #860]
	str r10, [r12, #864]
	str r11, [r12, #868]
	str lr, [r12, #872]
	mov r7, r12
	mov r4, r0
	mov r5, r1
	mov r6, r2
	mov r8, r3
	mov r11, #1
	movw r0, #0
	movt r0, #0
	add r0, r4, r0
	movw r1, #912
	movt r1, #0
	add r1, r7, r1
	movw r2, #32
	movt r2, #0
20:
	ldrb r3, [r0, #0]
	strb r3, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs r2, r2, #1
	bne 20b
	mov r0, #0
	strb r0, [r7, #944]
	mov r0, #0
	strb r0, [r7, #945]
	movw r0, #912
	movt r0, #0
	add r0, r7, r0
	movw r1, #38912
	movt r1, #0
	add r1, r7, r1
	movw r2, #3072
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r0, #1
	strb r0, [r7, #944]
	mov r0, #0
	strb r0, [r7, #945]
	movw r0, #912
	movt r0, #0
	add r0, r7, r0
	movw r1, #39936
	movt r1, #0
	add r1, r7, r1
	movw r2, #3072
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r0, #2
	strb r0, [r7, #944]
	mov r0, #0
	strb r0, [r7, #945]
	movw r0, #912
	movt r0, #0
	add r0, r7, r0
	movw r1, #40960
	movt r1, #0
	add r1, r7, r1
	movw r2, #3072
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r0, #3
	strb r0, [r7, #944]
	mov r0, #0
	strb r0, [r7, #945]
	movw r0, #912
	movt r0, #0
	add r0, r7, r0
	movw r1, #41984
	movt r1, #0
	add r1, r7, r1
	movw r2, #3072
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r0, #0
	strb r0, [r7, #944]
	mov r0, #1
	strb r0, [r7, #945]
	movw r0, #912
	movt r0, #0
	add r0, r7, r0
	movw r1, #43008
	movt r1, #0
	add r1, r7, r1
	movw r2, #3072
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r0, #1
	strb r0, [r7, #944]
	mov r0, #1
	strb r0, [r7, #945]
	movw r0, #912
	movt r0, #0
	add r0, r7, r0
	movw r1, #44032
	movt r1, #0
	add r1, r7, r1
	movw r2, #3072
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r0, #2
	strb r0, [r7, #944]
	mov r0, #1
	strb r0, [r7, #945]
	movw r0, #912
	movt r0, #0
	add r0, r7, r0
	movw r1, #45056
	movt r1, #0
	add r1, r7, r1
	movw r2, #3072
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r0, #3
	strb r0, [r7, #944]
	mov r0, #1
	strb r0, [r7, #945]
	movw r0, #912
	movt r0, #0
	add r0, r7, r0
	movw r1, #46080
	movt r1, #0
	add r1, r7, r1
	movw r2, #3072
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r0, #0
	strb r0, [r7, #944]
	mov r0, #2
	strb r0, [r7, #945]
	movw r0, #912
	movt r0, #0
	add r0, r7, r0
	movw r1, #47104
	movt r1, #0
	add r1, r7, r1
	movw r2, #3072
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r0, #1
	strb r0, [r7, #944]
	mov r0, #2
	strb r0, [r7, #945]
	movw r0, #912
	movt r0, #0
	add r0, r7, r0
	movw r1, #48128
	movt r1, #0
	add r1, r7, r1
	movw r2, #3072
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r0, #2
	strb r0, [r7, #944]
	mov r0, #2
	strb r0, [r7, #945]
	movw r0, #912
	movt r0, #0
	add r0, r7, r0
	movw r1, #49152
	movt r1, #0
	add r1, r7, r1
	movw r2, #3072
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r0, #3
	strb r0, [r7, #944]
	mov r0, #2
	strb r0, [r7, #945]
	movw r0, #912
	movt r0, #0
	add r0, r7, r0
	movw r1, #50176
	movt r1, #0
	add r1, r7, r1
	movw r2, #3072
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r0, #0
	strb r0, [r7, #944]
	mov r0, #3
	strb r0, [r7, #945]
	movw r0, #912
	movt r0, #0
	add r0, r7, r0
	movw r1, #51200
	movt r1, #0
	add r1, r7, r1
	movw r2, #3072
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r0, #1
	strb r0, [r7, #944]
	mov r0, #3
	strb r0, [r7, #945]
	movw r0, #912
	movt r0, #0
	add r0, r7, r0
	movw r1, #52224
	movt r1, #0
	add r1, r7, r1
	movw r2, #3072
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r0, #2
	strb r0, [r7, #944]
	mov r0, #3
	strb r0, [r7, #945]
	movw r0, #912
	movt r0, #0
	add r0, r7, r0
	movw r1, #53248
	movt r1, #0
	add r1, r7, r1
	movw r2, #3072
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	mov r0, #3
	strb r0, [r7, #944]
	mov r0, #3
	strb r0, [r7, #945]
	movw r0, #912
	movt r0, #0
	add r0, r7, r0
	movw r1, #54272
	movt r1, #0
	add r1, r7, r1
	movw r2, #3072
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
	and r11, r11, r0
	cmp r11, #0
	bne 21f
	b 22f
21:
	movw r0, #128
	movt r0, #0
	add r0, r4, r0
	movw r1, #96
	movt r1, #0
	movw r2, #2
	movt r2, #0
	movw r3, #2
	movt r3, #0
	movw r12, #26624
	movt r12, #0
	add r12, r7, r12
	push {r12, lr}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #8
	movw r0, #26624
	movt r0, #0
	add r0, r7, r0
	movw r1, #3072
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #224
	movt r0, #0
	add r0, r4, r0
	movw r1, #96
	movt r1, #0
	movw r2, #2
	movt r2, #0
	movw r3, #2
	movt r3, #0
	movw r12, #27648
	movt r12, #0
	add r12, r7, r12
	push {r12, lr}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #8
	movw r0, #27648
	movt r0, #0
	add r0, r7, r0
	movw r1, #3072
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #320
	movt r0, #0
	add r0, r4, r0
	movw r1, #96
	movt r1, #0
	movw r2, #2
	movt r2, #0
	movw r3, #2
	movt r3, #0
	movw r12, #28672
	movt r12, #0
	add r12, r7, r12
	push {r12, lr}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #8
	movw r0, #28672
	movt r0, #0
	add r0, r7, r0
	movw r1, #3072
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #416
	movt r0, #0
	add r0, r4, r0
	movw r1, #96
	movt r1, #0
	movw r2, #2
	movt r2, #0
	movw r3, #2
	movt r3, #0
	movw r12, #29696
	movt r12, #0
	add r12, r7, r12
	push {r12, lr}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #8
	movw r0, #29696
	movt r0, #0
	add r0, r7, r0
	movw r1, #3072
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #512
	movt r0, #0
	add r0, r4, r0
	movw r1, #96
	movt r1, #0
	movw r2, #2
	movt r2, #0
	movw r3, #2
	movt r3, #0
	movw r12, #30720
	movt r12, #0
	add r12, r7, r12
	push {r12, lr}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #8
	movw r0, #30720
	movt r0, #0
	add r0, r7, r0
	movw r1, #3072
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #608
	movt r0, #0
	add r0, r4, r0
	movw r1, #96
	movt r1, #0
	movw r2, #2
	movt r2, #0
	movw r3, #2
	movt r3, #0
	movw r12, #31744
	movt r12, #0
	add r12, r7, r12
	push {r12, lr}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #8
	movw r0, #31744
	movt r0, #0
	add r0, r7, r0
	movw r1, #3072
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #704
	movt r0, #0
	add r0, r4, r0
	movw r1, #96
	movt r1, #0
	movw r2, #2
	movt r2, #0
	movw r3, #2
	movt r3, #0
	movw r12, #32768
	movt r12, #0
	add r12, r7, r12
	push {r12, lr}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #8
	movw r0, #32768
	movt r0, #0
	add r0, r7, r0
	movw r1, #3072
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #800
	movt r0, #0
	add r0, r4, r0
	movw r1, #96
	movt r1, #0
	movw r2, #2
	movt r2, #0
	movw r3, #2
	movt r3, #0
	movw r12, #33792
	movt r12, #0
	add r12, r7, r12
	push {r12, lr}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #8
	movw r0, #33792
	movt r0, #0
	add r0, r7, r0
	movw r1, #3072
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #896
	movt r0, #0
	add r0, r4, r0
	movw r1, #416
	movt r1, #0
	movw r2, #4095
	movt r2, #0
	movw r3, #4096
	movt r3, #0
	movw r12, #34816
	movt r12, #0
	add r12, r7, r12
	push {r12, lr}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #8
	movw r0, #34816
	movt r0, #0
	add r0, r7, r0
	movw r1, #3072
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #1312
	movt r0, #0
	add r0, r4, r0
	movw r1, #416
	movt r1, #0
	movw r2, #4095
	movt r2, #0
	movw r3, #4096
	movt r3, #0
	movw r12, #35840
	movt r12, #0
	add r12, r7, r12
	push {r12, lr}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #8
	movw r0, #35840
	movt r0, #0
	add r0, r7, r0
	movw r1, #3072
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #1728
	movt r0, #0
	add r0, r4, r0
	movw r1, #416
	movt r1, #0
	movw r2, #4095
	movt r2, #0
	movw r3, #4096
	movt r3, #0
	movw r12, #36864
	movt r12, #0
	add r12, r7, r12
	push {r12, lr}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #8
	movw r0, #36864
	movt r0, #0
	add r0, r7, r0
	movw r1, #3072
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #2144
	movt r0, #0
	add r0, r4, r0
	movw r1, #416
	movt r1, #0
	movw r2, #4095
	movt r2, #0
	movw r3, #4096
	movt r3, #0
	movw r12, #37888
	movt r12, #0
	add r12, r7, r12
	push {r12, lr}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #8
	movw r0, #37888
	movt r0, #0
	add r0, r7, r0
	movw r1, #3072
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
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
	movw r0, #0
	movt r0, #0
	add r0, r7, r0
	movw r1, #136
	movt r1, #0
	movw r2, #0
	movt r2, #0
	movw r3, #32
	movt r3, #0
	add r3, r4, r3
	movw r12, #32
	movt r12, #0
	movw lr, #200
	movt lr, #0
	add lr, r7, lr
	push {r12, lr}
	bl {vg_keccak_absorb_scratch}
	ldr r12, [sp], #8
	movw r0, #0
	movt r0, #0
	add r0, r7, r0
	movw r1, #136
	movt r1, #0
	movw r2, #32
	movt r2, #0
	movw r3, #0
	movt r3, #0
	add r3, r6, r3
	movw r12, #32
	movt r12, #0
	movw lr, #200
	movt lr, #0
	add lr, r7, lr
	push {r12, lr}
	bl {vg_keccak_absorb_scratch}
	ldr r12, [sp], #8
	movw r0, #0
	movt r0, #0
	add r0, r7, r0
	movw r1, #136
	movt r1, #0
	movw r2, #64
	movt r2, #0
	movw r3, #0
	movt r3, #0
	add r3, r5, r3
	movw r12, #64
	movt r12, #0
	movw lr, #200
	movt lr, #0
	add lr, r7, lr
	push {r12, lr}
	bl {vg_keccak_absorb_scratch}
	ldr r12, [sp], #8
	movw r0, #0
	movt r0, #0
	add r0, r7, r0
	movw r1, #136
	movt r1, #0
	movw r2, #128
	movt r2, #0
	movw r3, #31
	movt r3, #0
	movw lr, #200
	movt lr, #0
	add lr, r7, lr
	push {lr}
	bl {vg_keccak_pad_scratch}
	ldr r12, [sp], #4
	movw r0, #0
	movt r0, #0
	add r0, r7, r0
	movw r1, #136
	movt r1, #0
	movw r2, #0
	movt r2, #0
	movw r3, #960
	movt r3, #0
	add r3, r7, r3
	movw r12, #64
	movt r12, #0
	movw lr, #200
	movt lr, #0
	add lr, r7, lr
	push {r12, lr}
	bl {vg_keccak_squeeze_scratch}
	ldr r12, [sp], #8
	movw r0, #0
	movt r0, #0
	str r0, [r7, #896]
	movw r0, #814
	movt r0, #0
	str r0, [r7, #888]
23:
	ldr r0, [r7, #896]
	add r0, r0, #0
	strb r0, [r7, #1024]
	lsr r0, r0, #8
	strb r0, [r7, #1025]
	movw r0, #960
	movt r0, #0
	add r0, r7, r0
	movw r1, #0
	movt r1, #2
	movw r2, #14336
	movt r2, #0
	add r2, r7, r2
	movw r3, #3072
	movt r3, #0
	add r3, r7, r3
	bl {vg_mldsa_expand_mask_poly}
	movw r0, #14336
	movt r0, #0
	add r0, r7, r0
	movw r1, #18432
	movt r1, #0
	add r1, r7, r1
	movw r2, #1024
	movt r2, #0
24:
	ldrb r3, [r0, #0]
	strb r3, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs r2, r2, #1
	bne 24b
	movw r0, #18432
	movt r0, #0
	add r0, r7, r0
	movw r1, #3072
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	ldr r0, [r7, #896]
	add r0, r0, #1
	strb r0, [r7, #1024]
	lsr r0, r0, #8
	strb r0, [r7, #1025]
	movw r0, #960
	movt r0, #0
	add r0, r7, r0
	movw r1, #0
	movt r1, #2
	movw r2, #15360
	movt r2, #0
	add r2, r7, r2
	movw r3, #3072
	movt r3, #0
	add r3, r7, r3
	bl {vg_mldsa_expand_mask_poly}
	movw r0, #15360
	movt r0, #0
	add r0, r7, r0
	movw r1, #19456
	movt r1, #0
	add r1, r7, r1
	movw r2, #1024
	movt r2, #0
25:
	ldrb r3, [r0, #0]
	strb r3, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs r2, r2, #1
	bne 25b
	movw r0, #19456
	movt r0, #0
	add r0, r7, r0
	movw r1, #3072
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	ldr r0, [r7, #896]
	add r0, r0, #2
	strb r0, [r7, #1024]
	lsr r0, r0, #8
	strb r0, [r7, #1025]
	movw r0, #960
	movt r0, #0
	add r0, r7, r0
	movw r1, #0
	movt r1, #2
	movw r2, #16384
	movt r2, #0
	add r2, r7, r2
	movw r3, #3072
	movt r3, #0
	add r3, r7, r3
	bl {vg_mldsa_expand_mask_poly}
	movw r0, #16384
	movt r0, #0
	add r0, r7, r0
	movw r1, #20480
	movt r1, #0
	add r1, r7, r1
	movw r2, #1024
	movt r2, #0
26:
	ldrb r3, [r0, #0]
	strb r3, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs r2, r2, #1
	bne 26b
	movw r0, #20480
	movt r0, #0
	add r0, r7, r0
	movw r1, #3072
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	ldr r0, [r7, #896]
	add r0, r0, #3
	strb r0, [r7, #1024]
	lsr r0, r0, #8
	strb r0, [r7, #1025]
	movw r0, #960
	movt r0, #0
	add r0, r7, r0
	movw r1, #0
	movt r1, #2
	movw r2, #17408
	movt r2, #0
	add r2, r7, r2
	movw r3, #3072
	movt r3, #0
	add r3, r7, r3
	bl {vg_mldsa_expand_mask_poly}
	movw r0, #17408
	movt r0, #0
	add r0, r7, r0
	movw r1, #21504
	movt r1, #0
	add r1, r7, r1
	movw r2, #1024
	movt r2, #0
27:
	ldrb r3, [r0, #0]
	strb r3, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs r2, r2, #1
	bne 27b
	movw r0, #21504
	movt r0, #0
	add r0, r7, r0
	movw r1, #3072
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #22528
	movt r0, #0
	add r0, r7, r0
	movw r1, #38912
	movt r1, #0
	add r1, r7, r1
	movw r2, #18432
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_ntt}
	movw r0, #22528
	movt r0, #0
	add r0, r7, r0
	movw r1, #39936
	movt r1, #0
	add r1, r7, r1
	movw r2, #19456
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #22528
	movt r0, #0
	add r0, r7, r0
	movw r1, #40960
	movt r1, #0
	add r1, r7, r1
	movw r2, #20480
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #22528
	movt r0, #0
	add r0, r7, r0
	movw r1, #41984
	movt r1, #0
	add r1, r7, r1
	movw r2, #21504
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #22528
	movt r0, #0
	add r0, r7, r0
	movw r1, #3072
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_inv_ntt}
	movw r0, #23552
	movt r0, #0
	add r0, r7, r0
	movw r1, #43008
	movt r1, #0
	add r1, r7, r1
	movw r2, #18432
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_ntt}
	movw r0, #23552
	movt r0, #0
	add r0, r7, r0
	movw r1, #44032
	movt r1, #0
	add r1, r7, r1
	movw r2, #19456
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #23552
	movt r0, #0
	add r0, r7, r0
	movw r1, #45056
	movt r1, #0
	add r1, r7, r1
	movw r2, #20480
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #23552
	movt r0, #0
	add r0, r7, r0
	movw r1, #46080
	movt r1, #0
	add r1, r7, r1
	movw r2, #21504
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #23552
	movt r0, #0
	add r0, r7, r0
	movw r1, #3072
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_inv_ntt}
	movw r0, #24576
	movt r0, #0
	add r0, r7, r0
	movw r1, #47104
	movt r1, #0
	add r1, r7, r1
	movw r2, #18432
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_ntt}
	movw r0, #24576
	movt r0, #0
	add r0, r7, r0
	movw r1, #48128
	movt r1, #0
	add r1, r7, r1
	movw r2, #19456
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #24576
	movt r0, #0
	add r0, r7, r0
	movw r1, #49152
	movt r1, #0
	add r1, r7, r1
	movw r2, #20480
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #24576
	movt r0, #0
	add r0, r7, r0
	movw r1, #50176
	movt r1, #0
	add r1, r7, r1
	movw r2, #21504
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #24576
	movt r0, #0
	add r0, r7, r0
	movw r1, #3072
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_inv_ntt}
	movw r0, #25600
	movt r0, #0
	add r0, r7, r0
	movw r1, #51200
	movt r1, #0
	add r1, r7, r1
	movw r2, #18432
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_ntt}
	movw r0, #25600
	movt r0, #0
	add r0, r7, r0
	movw r1, #52224
	movt r1, #0
	add r1, r7, r1
	movw r2, #19456
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #25600
	movt r0, #0
	add r0, r7, r0
	movw r1, #53248
	movt r1, #0
	add r1, r7, r1
	movw r2, #20480
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #25600
	movt r0, #0
	add r0, r7, r0
	movw r1, #54272
	movt r1, #0
	add r1, r7, r1
	movw r2, #21504
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #25600
	movt r0, #0
	add r0, r7, r0
	movw r1, #3072
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_inv_ntt}
	movw r0, #22528
	movt r0, #0
	add r0, r7, r0
	movw r1, #29696
	movt r1, #1
	movw r2, #6144
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_high_bits}
	movw r0, #6144
	movt r0, #0
	add r0, r7, r0
	movw r1, #43
	movt r1, #0
	movw r2, #2048
	movt r2, #0
	add r2, r7, r2
	movw r3, #192
	movt r3, #0
	bl {vg_mldsa_simple_bit_pack}
	movw r0, #23552
	movt r0, #0
	add r0, r7, r0
	movw r1, #29696
	movt r1, #1
	movw r2, #6144
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_high_bits}
	movw r0, #6144
	movt r0, #0
	add r0, r7, r0
	movw r1, #43
	movt r1, #0
	movw r2, #2240
	movt r2, #0
	add r2, r7, r2
	movw r3, #192
	movt r3, #0
	bl {vg_mldsa_simple_bit_pack}
	movw r0, #24576
	movt r0, #0
	add r0, r7, r0
	movw r1, #29696
	movt r1, #1
	movw r2, #6144
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_high_bits}
	movw r0, #6144
	movt r0, #0
	add r0, r7, r0
	movw r1, #43
	movt r1, #0
	movw r2, #2432
	movt r2, #0
	add r2, r7, r2
	movw r3, #192
	movt r3, #0
	bl {vg_mldsa_simple_bit_pack}
	movw r0, #25600
	movt r0, #0
	add r0, r7, r0
	movw r1, #29696
	movt r1, #1
	movw r2, #6144
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_high_bits}
	movw r0, #6144
	movt r0, #0
	add r0, r7, r0
	movw r1, #43
	movt r1, #0
	movw r2, #2624
	movt r2, #0
	add r2, r7, r2
	movw r3, #192
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
	movw r0, #0
	movt r0, #0
	add r0, r7, r0
	movw r1, #136
	movt r1, #0
	movw r2, #0
	movt r2, #0
	movw r3, #0
	movt r3, #0
	add r3, r5, r3
	movw r12, #64
	movt r12, #0
	movw lr, #200
	movt lr, #0
	add lr, r7, lr
	push {r12, lr}
	bl {vg_keccak_absorb_scratch}
	ldr r12, [sp], #8
	movw r0, #0
	movt r0, #0
	add r0, r7, r0
	movw r1, #136
	movt r1, #0
	movw r2, #64
	movt r2, #0
	movw r3, #2048
	movt r3, #0
	add r3, r7, r3
	movw r12, #768
	movt r12, #0
	movw lr, #200
	movt lr, #0
	add lr, r7, lr
	push {r12, lr}
	bl {vg_keccak_absorb_scratch}
	ldr r12, [sp], #8
	movw r0, #0
	movt r0, #0
	add r0, r7, r0
	movw r1, #136
	movt r1, #0
	movw r2, #16
	movt r2, #0
	movw r3, #31
	movt r3, #0
	movw lr, #200
	movt lr, #0
	add lr, r7, lr
	push {lr}
	bl {vg_keccak_pad_scratch}
	ldr r12, [sp], #4
	movw r0, #0
	movt r0, #0
	add r0, r7, r0
	movw r1, #136
	movt r1, #0
	movw r2, #0
	movt r2, #0
	movw r3, #1040
	movt r3, #0
	add r3, r7, r3
	movw r12, #32
	movt r12, #0
	movw lr, #200
	movt lr, #0
	add lr, r7, lr
	push {r12, lr}
	bl {vg_keccak_squeeze_scratch}
	ldr r12, [sp], #8
	movw r0, #1040
	movt r0, #0
	add r0, r7, r0
	movw r1, #32
	movt r1, #0
	movw r2, #39
	movt r2, #0
	movw r3, #5120
	movt r3, #0
	add r3, r7, r3
	movw r12, #3072
	movt r12, #0
	add r12, r7, r12
	push {r12, lr}
	bl {vg_mldsa_sample_in_ball}
	ldr r12, [sp], #8
	cmp r0, #0
	bne 28f
	mov r11, #0
	movw r0, #1
	movt r0, #0
	str r0, [r7, #888]
	b 29f
28:
	movw r0, #5120
	movt r0, #0
	add r0, r7, r0
	movw r1, #3072
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	mov r11, #1
	movw r0, #0
	movt r0, #0
	str r0, [r7, #904]
	movw r0, #6144
	movt r0, #0
	add r0, r7, r0
	movw r1, #5120
	movt r1, #0
	add r1, r7, r1
	movw r2, #26624
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_ntt}
	movw r0, #6144
	movt r0, #0
	add r0, r7, r0
	movw r1, #3072
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_inv_ntt}
	movw r0, #14336
	movt r0, #0
	add r0, r7, r0
	movw r1, #6144
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_add}
	movw r0, #14336
	movt r0, #0
	add r0, r7, r0
	movw r1, #65458
	movt r1, #1
	bl {vg_mldsa_norm_lt}
	and r11, r11, r0
	cmp r11, #0
	bne 210f
	b 211f
210:
	movw r0, #6144
	movt r0, #0
	add r0, r7, r0
	movw r1, #5120
	movt r1, #0
	add r1, r7, r1
	movw r2, #27648
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_ntt}
	movw r0, #6144
	movt r0, #0
	add r0, r7, r0
	movw r1, #3072
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_inv_ntt}
	movw r0, #15360
	movt r0, #0
	add r0, r7, r0
	movw r1, #6144
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_add}
	movw r0, #15360
	movt r0, #0
	add r0, r7, r0
	movw r1, #65458
	movt r1, #1
	bl {vg_mldsa_norm_lt}
	and r11, r11, r0
	cmp r11, #0
	bne 212f
	b 213f
212:
	movw r0, #6144
	movt r0, #0
	add r0, r7, r0
	movw r1, #5120
	movt r1, #0
	add r1, r7, r1
	movw r2, #28672
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_ntt}
	movw r0, #6144
	movt r0, #0
	add r0, r7, r0
	movw r1, #3072
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_inv_ntt}
	movw r0, #16384
	movt r0, #0
	add r0, r7, r0
	movw r1, #6144
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_add}
	movw r0, #16384
	movt r0, #0
	add r0, r7, r0
	movw r1, #65458
	movt r1, #1
	bl {vg_mldsa_norm_lt}
	and r11, r11, r0
	cmp r11, #0
	bne 214f
	b 215f
214:
	movw r0, #6144
	movt r0, #0
	add r0, r7, r0
	movw r1, #5120
	movt r1, #0
	add r1, r7, r1
	movw r2, #29696
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_ntt}
	movw r0, #6144
	movt r0, #0
	add r0, r7, r0
	movw r1, #3072
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_inv_ntt}
	movw r0, #17408
	movt r0, #0
	add r0, r7, r0
	movw r1, #6144
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_add}
	movw r0, #17408
	movt r0, #0
	add r0, r7, r0
	movw r1, #65458
	movt r1, #1
	bl {vg_mldsa_norm_lt}
	and r11, r11, r0
	cmp r11, #0
	bne 216f
	b 217f
216:
217:
215:
213:
211:
	cmp r11, #0
	bne 218f
	b 219f
218:
	movw r0, #6144
	movt r0, #0
	add r0, r7, r0
	movw r1, #5120
	movt r1, #0
	add r1, r7, r1
	movw r2, #30720
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_ntt}
	movw r0, #6144
	movt r0, #0
	add r0, r7, r0
	movw r1, #3072
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_inv_ntt}
	movw r0, #22528
	movt r0, #0
	add r0, r7, r0
	movw r1, #6144
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_sub}
	movw r0, #22528
	movt r0, #0
	add r0, r7, r0
	movw r1, #29696
	movt r1, #1
	movw r2, #7168
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_low_bits}
	movw r0, #7168
	movt r0, #0
	add r0, r7, r0
	movw r1, #29618
	movt r1, #1
	bl {vg_mldsa_norm_lt}
	and r11, r11, r0
	cmp r11, #0
	bne 220f
	b 221f
220:
	movw r0, #6144
	movt r0, #0
	add r0, r7, r0
	movw r1, #5120
	movt r1, #0
	add r1, r7, r1
	movw r2, #31744
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_ntt}
	movw r0, #6144
	movt r0, #0
	add r0, r7, r0
	movw r1, #3072
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_inv_ntt}
	movw r0, #23552
	movt r0, #0
	add r0, r7, r0
	movw r1, #6144
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_sub}
	movw r0, #23552
	movt r0, #0
	add r0, r7, r0
	movw r1, #29696
	movt r1, #1
	movw r2, #7168
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_low_bits}
	movw r0, #7168
	movt r0, #0
	add r0, r7, r0
	movw r1, #29618
	movt r1, #1
	bl {vg_mldsa_norm_lt}
	and r11, r11, r0
	cmp r11, #0
	bne 222f
	b 223f
222:
	movw r0, #6144
	movt r0, #0
	add r0, r7, r0
	movw r1, #5120
	movt r1, #0
	add r1, r7, r1
	movw r2, #32768
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_ntt}
	movw r0, #6144
	movt r0, #0
	add r0, r7, r0
	movw r1, #3072
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_inv_ntt}
	movw r0, #24576
	movt r0, #0
	add r0, r7, r0
	movw r1, #6144
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_sub}
	movw r0, #24576
	movt r0, #0
	add r0, r7, r0
	movw r1, #29696
	movt r1, #1
	movw r2, #7168
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_low_bits}
	movw r0, #7168
	movt r0, #0
	add r0, r7, r0
	movw r1, #29618
	movt r1, #1
	bl {vg_mldsa_norm_lt}
	and r11, r11, r0
	cmp r11, #0
	bne 224f
	b 225f
224:
	movw r0, #6144
	movt r0, #0
	add r0, r7, r0
	movw r1, #5120
	movt r1, #0
	add r1, r7, r1
	movw r2, #33792
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_ntt}
	movw r0, #6144
	movt r0, #0
	add r0, r7, r0
	movw r1, #3072
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_inv_ntt}
	movw r0, #25600
	movt r0, #0
	add r0, r7, r0
	movw r1, #6144
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_sub}
	movw r0, #25600
	movt r0, #0
	add r0, r7, r0
	movw r1, #29696
	movt r1, #1
	movw r2, #7168
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_low_bits}
	movw r0, #7168
	movt r0, #0
	add r0, r7, r0
	movw r1, #29618
	movt r1, #1
	bl {vg_mldsa_norm_lt}
	and r11, r11, r0
	cmp r11, #0
	bne 226f
	b 227f
226:
227:
225:
223:
221:
	cmp r11, #0
	bne 228f
	b 229f
228:
	movw r0, #8192
	movt r0, #0
	add r0, r7, r0
	movw r1, #5120
	movt r1, #0
	add r1, r7, r1
	movw r2, #34816
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_ntt}
	movw r0, #8192
	movt r0, #0
	add r0, r7, r0
	movw r1, #3072
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_inv_ntt}
	movw r0, #8192
	movt r0, #0
	add r0, r7, r0
	movw r1, #29696
	movt r1, #1
	bl {vg_mldsa_norm_lt}
	and r11, r11, r0
	movw r0, #22528
	movt r0, #0
	add r0, r7, r0
	movw r1, #9216
	movt r1, #0
	add r1, r7, r1
	movw r2, #1024
	movt r2, #0
230:
	ldrb r3, [r0, #0]
	strb r3, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs r2, r2, #1
	bne 230b
	movw r0, #22528
	movt r0, #0
	add r0, r7, r0
	movw r1, #8192
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_add}
	movw r0, #9216
	movt r0, #0
	add r0, r7, r0
	movw r1, #22528
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_sub}
	movw r0, #9216
	movt r0, #0
	add r0, r7, r0
	movw r1, #22528
	movt r1, #0
	add r1, r7, r1
	movw r2, #29696
	movt r2, #1
	movw r3, #10240
	movt r3, #0
	add r3, r7, r3
	bl {vg_mldsa_make_hint}
	ldr r1, [r7, #904]
	add r1, r1, r0
	str r1, [r7, #904]
	movw r0, #8192
	movt r0, #0
	add r0, r7, r0
	movw r1, #5120
	movt r1, #0
	add r1, r7, r1
	movw r2, #35840
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_ntt}
	movw r0, #8192
	movt r0, #0
	add r0, r7, r0
	movw r1, #3072
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_inv_ntt}
	movw r0, #8192
	movt r0, #0
	add r0, r7, r0
	movw r1, #29696
	movt r1, #1
	bl {vg_mldsa_norm_lt}
	and r11, r11, r0
	movw r0, #23552
	movt r0, #0
	add r0, r7, r0
	movw r1, #9216
	movt r1, #0
	add r1, r7, r1
	movw r2, #1024
	movt r2, #0
231:
	ldrb r3, [r0, #0]
	strb r3, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs r2, r2, #1
	bne 231b
	movw r0, #23552
	movt r0, #0
	add r0, r7, r0
	movw r1, #8192
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_add}
	movw r0, #9216
	movt r0, #0
	add r0, r7, r0
	movw r1, #23552
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_sub}
	movw r0, #9216
	movt r0, #0
	add r0, r7, r0
	movw r1, #23552
	movt r1, #0
	add r1, r7, r1
	movw r2, #29696
	movt r2, #1
	movw r3, #11264
	movt r3, #0
	add r3, r7, r3
	bl {vg_mldsa_make_hint}
	ldr r1, [r7, #904]
	add r1, r1, r0
	str r1, [r7, #904]
	movw r0, #8192
	movt r0, #0
	add r0, r7, r0
	movw r1, #5120
	movt r1, #0
	add r1, r7, r1
	movw r2, #36864
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_ntt}
	movw r0, #8192
	movt r0, #0
	add r0, r7, r0
	movw r1, #3072
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_inv_ntt}
	movw r0, #8192
	movt r0, #0
	add r0, r7, r0
	movw r1, #29696
	movt r1, #1
	bl {vg_mldsa_norm_lt}
	and r11, r11, r0
	movw r0, #24576
	movt r0, #0
	add r0, r7, r0
	movw r1, #9216
	movt r1, #0
	add r1, r7, r1
	movw r2, #1024
	movt r2, #0
232:
	ldrb r3, [r0, #0]
	strb r3, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs r2, r2, #1
	bne 232b
	movw r0, #24576
	movt r0, #0
	add r0, r7, r0
	movw r1, #8192
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_add}
	movw r0, #9216
	movt r0, #0
	add r0, r7, r0
	movw r1, #24576
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_sub}
	movw r0, #9216
	movt r0, #0
	add r0, r7, r0
	movw r1, #24576
	movt r1, #0
	add r1, r7, r1
	movw r2, #29696
	movt r2, #1
	movw r3, #12288
	movt r3, #0
	add r3, r7, r3
	bl {vg_mldsa_make_hint}
	ldr r1, [r7, #904]
	add r1, r1, r0
	str r1, [r7, #904]
	movw r0, #8192
	movt r0, #0
	add r0, r7, r0
	movw r1, #5120
	movt r1, #0
	add r1, r7, r1
	movw r2, #37888
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_ntt}
	movw r0, #8192
	movt r0, #0
	add r0, r7, r0
	movw r1, #3072
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_inv_ntt}
	movw r0, #8192
	movt r0, #0
	add r0, r7, r0
	movw r1, #29696
	movt r1, #1
	bl {vg_mldsa_norm_lt}
	and r11, r11, r0
	movw r0, #25600
	movt r0, #0
	add r0, r7, r0
	movw r1, #9216
	movt r1, #0
	add r1, r7, r1
	movw r2, #1024
	movt r2, #0
233:
	ldrb r3, [r0, #0]
	strb r3, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs r2, r2, #1
	bne 233b
	movw r0, #25600
	movt r0, #0
	add r0, r7, r0
	movw r1, #8192
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_add}
	movw r0, #9216
	movt r0, #0
	add r0, r7, r0
	movw r1, #25600
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_sub}
	movw r0, #9216
	movt r0, #0
	add r0, r7, r0
	movw r1, #25600
	movt r1, #0
	add r1, r7, r1
	movw r2, #29696
	movt r2, #1
	movw r3, #13312
	movt r3, #0
	add r3, r7, r3
	bl {vg_mldsa_make_hint}
	ldr r1, [r7, #904]
	add r1, r1, r0
	str r1, [r7, #904]
	ldr r0, [r7, #904]
	sub r0, r0, #81
	lsr r0, r0, #31
	and r11, r11, r0
229:
219:
	cmp r11, #0
	bne 234f
	ldr r0, [r7, #896]
	add r0, r0, #4
	str r0, [r7, #896]
	b 235f
234:
	movw r0, #1
	movt r0, #0
	str r0, [r7, #888]
235:
29:
	ldr r0, [r7, #888]
	subs r0, r0, #1
	str r0, [r7, #888]
	bne 23b
	cmp r11, #0
	bne 236f
	b 237f
236:
	movw r0, #1040
	movt r0, #0
	add r0, r7, r0
	movw r1, #0
	movt r1, #0
	add r1, r8, r1
	movw r2, #32
	movt r2, #0
238:
	ldrb r3, [r0, #0]
	strb r3, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs r2, r2, #1
	bne 238b
	movw r0, #14336
	movt r0, #0
	add r0, r7, r0
	movw r1, #65535
	movt r1, #1
	movw r2, #0
	movt r2, #2
	movw r3, #32
	movt r3, #0
	add r3, r8, r3
	movw r12, #576
	movt r12, #0
	push {r12, lr}
	bl {vg_mldsa_bit_pack}
	ldr r12, [sp], #8
	movw r0, #15360
	movt r0, #0
	add r0, r7, r0
	movw r1, #65535
	movt r1, #1
	movw r2, #0
	movt r2, #2
	movw r3, #608
	movt r3, #0
	add r3, r8, r3
	movw r12, #576
	movt r12, #0
	push {r12, lr}
	bl {vg_mldsa_bit_pack}
	ldr r12, [sp], #8
	movw r0, #16384
	movt r0, #0
	add r0, r7, r0
	movw r1, #65535
	movt r1, #1
	movw r2, #0
	movt r2, #2
	movw r3, #1184
	movt r3, #0
	add r3, r8, r3
	movw r12, #576
	movt r12, #0
	push {r12, lr}
	bl {vg_mldsa_bit_pack}
	ldr r12, [sp], #8
	movw r0, #17408
	movt r0, #0
	add r0, r7, r0
	movw r1, #65535
	movt r1, #1
	movw r2, #0
	movt r2, #2
	movw r3, #1760
	movt r3, #0
	add r3, r8, r3
	movw r12, #576
	movt r12, #0
	push {r12, lr}
	bl {vg_mldsa_bit_pack}
	ldr r12, [sp], #8
	movw r0, #10240
	movt r0, #0
	add r0, r7, r0
	movw r1, #1024
	movt r1, #0
	movw r2, #80
	movt r2, #0
	movw r3, #2336
	movt r3, #0
	add r3, r8, r3
	movw r12, #84
	movt r12, #0
	push {r12, lr}
	bl {vg_mldsa_hint_bit_pack}
	ldr r12, [sp], #8
237:
22:
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

vg_mldsa44_sign_message:
	ldr r12, [sp, #0]
	lsr r12, r12, #8
	cmp r12, #0
	bne 20f
	ldr r12, [sp, #12]
	str r7, [r12, #0]
	movw r7, #12288
	movt r7, #1
	add r7, r12, r7
	ldr r12, [r12, #0]
	str r12, [r7, #904]
	str lr, [r7, #908]
	str r0, [r7, #912]
	str r1, [r7, #916]
	str r2, [r7, #920]
	str r3, [r7, #924]
	ldr r0, [sp, #0]
	ldr r1, [sp, #4]
	ldr r2, [sp, #8]
	ldr r3, [sp, #12]
	str r0, [r7, #928]
	str r1, [r7, #932]
	str r2, [r7, #936]
	str r3, [r7, #940]
	mov r12, #0
	strb r12, [r7, #944]
	strb r0, [r7, #945]
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
	movw r2, #0
	movw r0, #0
	add r0, r7, r0
	movw r1, #136
	ldr r3, [r7, #912]
	add r3, r3, #64
	movw r12, #64
	movw lr, #200
	add lr, r7, lr
	push {r12, lr}
	bl {vg_keccak_absorb_scratch}
	ldr r12, [sp], #8
	movw r2, #64
	movw r0, #0
	add r0, r7, r0
	movw r1, #136
	movw r3, #944
	add r3, r7, r3
	movw r12, #2
	movw lr, #200
	add lr, r7, lr
	push {r12, lr}
	bl {vg_keccak_absorb_scratch}
	ldr r12, [sp], #8
	movw r2, #66
	movw r0, #0
	add r0, r7, r0
	movw r1, #136
	ldr r3, [r7, #924]
	ldr r12, [r7, #928]
	movw lr, #200
	add lr, r7, lr
	push {r12, lr}
	bl {vg_keccak_absorb_scratch}
	ldr r12, [sp], #8
	mov r2, r0
	movw r0, #0
	add r0, r7, r0
	movw r1, #136
	ldr r3, [r7, #916]
	ldr r12, [r7, #920]
	movw lr, #200
	add lr, r7, lr
	push {r12, lr}
	bl {vg_keccak_absorb_scratch}
	ldr r12, [sp], #8
	mov r2, r0
	movw r0, #0
	add r0, r7, r0
	movw r1, #136
	movw r3, #31
	movw lr, #200
	add lr, r7, lr
	push {lr}
	bl {vg_keccak_pad_scratch}
	ldr r12, [sp], #4
	movw r0, #0
	add r0, r7, r0
	movw r1, #136
	movw r2, #0
	movw r3, #840
	add r3, r7, r3
	movw r12, #64
	movw lr, #200
	add lr, r7, lr
	push {r12, lr}
	bl {vg_keccak_squeeze_scratch}
	ldr r12, [sp], #8
	ldr r0, [r7, #912]
	movw r1, #840
	add r1, r7, r1
	ldr r2, [r7, #932]
	ldr r3, [r7, #936]
	ldr r12, [r7, #940]
	push {r12, lr}
	bl {vg_mldsa44_sign}
	ldr r12, [sp], #8
	ldr lr, [r7, #908]
	ldr r7, [r7, #904]
	b 21f
20:
	mov r0, #2
21:
	bx lr

vg_mldsa44_verify:
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
	movw r0, #2336
	movt r0, #0
	add r0, r6, r0
	movw r1, #84
	movt r1, #0
	movw r2, #80
	movt r2, #0
	movw r3, #8192
	movt r3, #0
	add r3, r7, r3
	movw r12, #1024
	movt r12, #0
	push {r12}
	bl {vg_mldsa_hint_bit_unpack}
	ldr r12, [sp], #4
	mov r11, r0
	cmp r11, #0
	bne 20f
	b 21f
20:
	movw r0, #32
	movt r0, #0
	add r0, r6, r0
	movw r1, #576
	movt r1, #0
	movw r2, #65535
	movt r2, #1
	movw r3, #0
	movt r3, #2
	movw r12, #16384
	movt r12, #0
	add r12, r7, r12
	push {r12}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #4
	movw r0, #16384
	movt r0, #0
	add r0, r7, r0
	movw r1, #65458
	movt r1, #1
	bl {vg_mldsa_norm_lt}
	and r11, r11, r0
	movw r0, #608
	movt r0, #0
	add r0, r6, r0
	movw r1, #576
	movt r1, #0
	movw r2, #65535
	movt r2, #1
	movw r3, #0
	movt r3, #2
	movw r12, #17408
	movt r12, #0
	add r12, r7, r12
	push {r12}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #4
	movw r0, #17408
	movt r0, #0
	add r0, r7, r0
	movw r1, #65458
	movt r1, #1
	bl {vg_mldsa_norm_lt}
	and r11, r11, r0
	movw r0, #1184
	movt r0, #0
	add r0, r6, r0
	movw r1, #576
	movt r1, #0
	movw r2, #65535
	movt r2, #1
	movw r3, #0
	movt r3, #2
	movw r12, #18432
	movt r12, #0
	add r12, r7, r12
	push {r12}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #4
	movw r0, #18432
	movt r0, #0
	add r0, r7, r0
	movw r1, #65458
	movt r1, #1
	bl {vg_mldsa_norm_lt}
	and r11, r11, r0
	movw r0, #1760
	movt r0, #0
	add r0, r6, r0
	movw r1, #576
	movt r1, #0
	movw r2, #65535
	movt r2, #1
	movw r3, #0
	movt r3, #2
	movw r12, #19456
	movt r12, #0
	add r12, r7, r12
	push {r12}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #4
	movw r0, #19456
	movt r0, #0
	add r0, r7, r0
	movw r1, #65458
	movt r1, #1
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
29:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 29b
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
210:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 210b
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
211:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 211b
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
212:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 212b
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
213:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 213b
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
214:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 214b
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
215:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 215b
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
216:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 216b
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
217:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 217b
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
218:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 218b
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
219:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 219b
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
220:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 220b
	movw r0, #0
	movt r0, #0
	add r0, r6, r0
	movw r1, #32
	movt r1, #0
	movw r2, #39
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
221:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 221b
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
	movw r2, #29696
	movt r2, #1
	movw r3, #27648
	movt r3, #0
	add r3, r7, r3
	bl {vg_mldsa_use_hint}
	movw r0, #27648
	movt r0, #0
	add r0, r7, r0
	movw r1, #43
	movt r1, #0
	movw r2, #1024
	movt r2, #0
	add r2, r7, r2
	movw r3, #192
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
	movw r2, #29696
	movt r2, #1
	movw r3, #27648
	movt r3, #0
	add r3, r7, r3
	bl {vg_mldsa_use_hint}
	movw r0, #27648
	movt r0, #0
	add r0, r7, r0
	movw r1, #43
	movt r1, #0
	movw r2, #1216
	movt r2, #0
	add r2, r7, r2
	movw r3, #192
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
	movw r2, #29696
	movt r2, #1
	movw r3, #27648
	movt r3, #0
	add r3, r7, r3
	bl {vg_mldsa_use_hint}
	movw r0, #27648
	movt r0, #0
	add r0, r7, r0
	movw r1, #43
	movt r1, #0
	movw r2, #1408
	movt r2, #0
	add r2, r7, r2
	movw r3, #192
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
	movw r2, #29696
	movt r2, #1
	movw r3, #27648
	movt r3, #0
	add r3, r7, r3
	bl {vg_mldsa_use_hint}
	movw r0, #27648
	movt r0, #0
	add r0, r7, r0
	movw r1, #43
	movt r1, #0
	movw r2, #1600
	movt r2, #0
	add r2, r7, r2
	movw r3, #192
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
	mov r12, #768
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
	mov r12, #32
	push {r12, lr}
	bl {vg_keccak_squeeze_scratch}
	ldr r12, [sp], #8
	movw r0, #2048
	movt r0, #0
	add r0, r7, r0
	movw r1, #0
	movt r1, #0
	add r1, r6, r1
	movw r9, #32
	movt r9, #0
	mov r12, #0
222:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	orr r12, r12, r2
	add r0, r0, #1
	add r1, r1, #1
	subs r9, r9, #1
	bne 222b
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

vg_mldsa44_verify_message:
	ldr r12, [sp, #0]
	lsr r12, r12, #8
	cmp r12, #0
	bne 20f
	ldr r12, [sp, #8]
	str r7, [r12, #0]
	movw r7, #12288
	movt r7, #1
	add r7, r12, r7
	ldr r12, [r12, #0]
	str r12, [r7, #904]
	str lr, [r7, #908]
	str r0, [r7, #912]
	str r1, [r7, #916]
	str r2, [r7, #920]
	str r3, [r7, #924]
	ldr r0, [sp, #0]
	ldr r1, [sp, #4]
	ldr r2, [sp, #4]
	ldr r3, [sp, #8]
	str r0, [r7, #928]
	str r1, [r7, #932]
	str r2, [r7, #936]
	str r3, [r7, #940]
	mov r12, #0
	strb r12, [r7, #944]
	strb r0, [r7, #945]
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
	movw r2, #0
	movw r0, #0
	add r0, r7, r0
	movw r1, #136
	ldr r3, [r7, #912]
	movw r12, #1312
	movw lr, #200
	add lr, r7, lr
	push {r12, lr}
	bl {vg_keccak_absorb_scratch}
	ldr r12, [sp], #8
	movw r2, #88
	movw r0, #0
	add r0, r7, r0
	movw r1, #136
	movw r3, #31
	movw lr, #200
	add lr, r7, lr
	push {lr}
	bl {vg_keccak_pad_scratch}
	ldr r12, [sp], #4
	movw r0, #0
	add r0, r7, r0
	movw r1, #136
	movw r2, #0
	movw r3, #840
	add r3, r7, r3
	movw r12, #64
	movw lr, #200
	add lr, r7, lr
	push {r12, lr}
	bl {vg_keccak_squeeze_scratch}
	ldr r12, [sp], #8
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
	movw r2, #0
	movw r0, #0
	add r0, r7, r0
	movw r1, #136
	movw r3, #840
	add r3, r7, r3
	movw r12, #64
	movw lr, #200
	add lr, r7, lr
	push {r12, lr}
	bl {vg_keccak_absorb_scratch}
	ldr r12, [sp], #8
	movw r2, #64
	movw r0, #0
	add r0, r7, r0
	movw r1, #136
	movw r3, #944
	add r3, r7, r3
	movw r12, #2
	movw lr, #200
	add lr, r7, lr
	push {r12, lr}
	bl {vg_keccak_absorb_scratch}
	ldr r12, [sp], #8
	movw r2, #66
	movw r0, #0
	add r0, r7, r0
	movw r1, #136
	ldr r3, [r7, #924]
	ldr r12, [r7, #928]
	movw lr, #200
	add lr, r7, lr
	push {r12, lr}
	bl {vg_keccak_absorb_scratch}
	ldr r12, [sp], #8
	mov r2, r0
	movw r0, #0
	add r0, r7, r0
	movw r1, #136
	ldr r3, [r7, #916]
	ldr r12, [r7, #920]
	movw lr, #200
	add lr, r7, lr
	push {r12, lr}
	bl {vg_keccak_absorb_scratch}
	ldr r12, [sp], #8
	mov r2, r0
	movw r0, #0
	add r0, r7, r0
	movw r1, #136
	movw r3, #31
	movw lr, #200
	add lr, r7, lr
	push {lr}
	bl {vg_keccak_pad_scratch}
	ldr r12, [sp], #4
	movw r0, #0
	add r0, r7, r0
	movw r1, #136
	movw r2, #0
	movw r3, #840
	add r3, r7, r3
	movw r12, #64
	movw lr, #200
	add lr, r7, lr
	push {r12, lr}
	bl {vg_keccak_squeeze_scratch}
	ldr r12, [sp], #8
	ldr r0, [r7, #912]
	movw r1, #840
	add r1, r7, r1
	ldr r2, [r7, #936]
	ldr r3, [r7, #940]
	bl {vg_mldsa44_verify}
	ldr lr, [r7, #908]
	ldr r7, [r7, #904]
	b 21f
20:
	mov r0, #2
21:
	bx lr
