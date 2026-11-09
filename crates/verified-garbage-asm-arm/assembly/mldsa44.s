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

vg_mldsa44_pk_tr:
	str r4, [r2, #840]
	str r5, [r2, #844]
	str r6, [r2, #848]
	str r7, [r2, #852]
	str r8, [r2, #856]
	str r9, [r2, #860]
	str r10, [r2, #864]
	str r11, [r2, #868]
	str lr, [r2, #872]
	mov r4, r0
	mov r5, r0
	mov r6, r1
	mov r7, r2
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
	add r3, r6, #0
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

vg_mldsa44_prepare_verifying_key:
	push {r4, r7, r8, lr}
	mov r4, r0
	mov r8, r1
	mov r7, r2
	movw r0, #0
	movt r0, #0
	add r0, r4, r0
	movw r1, #0
	movt r1, #0
	add r1, r8, r1
	movw r2, #1312
	movt r2, #0
20:
	ldrb r3, [r0, #0]
	strb r3, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs r2, r2, #1
	bne 20b
	movw r0, #32
	movt r0, #0
	add r0, r4, r0
	movw r1, #1312
	movt r1, #0
	add r1, r8, r1
	bl {vg_mldsa_unpack_t1}
	movw r0, #1312
	movt r0, #0
	add r0, r8, r0
	movw r1, #0
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #352
	movt r0, #0
	add r0, r4, r0
	movw r1, #2336
	movt r1, #0
	add r1, r8, r1
	bl {vg_mldsa_unpack_t1}
	movw r0, #2336
	movt r0, #0
	add r0, r8, r0
	movw r1, #0
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #672
	movt r0, #0
	add r0, r4, r0
	movw r1, #3360
	movt r1, #0
	add r1, r8, r1
	bl {vg_mldsa_unpack_t1}
	movw r0, #3360
	movt r0, #0
	add r0, r8, r0
	movw r1, #0
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #992
	movt r0, #0
	add r0, r4, r0
	movw r1, #4384
	movt r1, #0
	add r1, r8, r1
	bl {vg_mldsa_unpack_t1}
	movw r0, #4384
	movt r0, #0
	add r0, r8, r0
	movw r1, #0
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	ldr r7, [sp, #4]
	ldr r8, [sp, #8]
	ldr lr, [sp, #12]
	ldr r4, [sp], #16
	bx lr

vg_mldsa44_prepare_signing_key:
	push {r4, r7, r8, lr}
	mov r4, r0
	mov r8, r1
	mov r7, r2
	movw r0, #0
	movt r0, #0
	add r0, r4, r0
	movw r1, #0
	movt r1, #0
	add r1, r8, r1
	movw r2, #2560
	movt r2, #0
20:
	ldrb r3, [r0, #0]
	strb r3, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs r2, r2, #1
	bne 20b
	movw r0, #128
	movt r0, #0
	add r0, r4, r0
	movw r1, #96
	movt r1, #0
	movw r2, #2
	movt r2, #0
	movw r3, #2
	movt r3, #0
	movw r12, #2560
	movt r12, #0
	add r12, r8, r12
	push {r12, lr}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #8
	movw r0, #2560
	movt r0, #0
	add r0, r8, r0
	movw r1, #0
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
	movw r12, #3584
	movt r12, #0
	add r12, r8, r12
	push {r12, lr}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #8
	movw r0, #3584
	movt r0, #0
	add r0, r8, r0
	movw r1, #0
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
	movw r12, #4608
	movt r12, #0
	add r12, r8, r12
	push {r12, lr}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #8
	movw r0, #4608
	movt r0, #0
	add r0, r8, r0
	movw r1, #0
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
	movw r12, #5632
	movt r12, #0
	add r12, r8, r12
	push {r12, lr}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #8
	movw r0, #5632
	movt r0, #0
	add r0, r8, r0
	movw r1, #0
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
	movw r12, #6656
	movt r12, #0
	add r12, r8, r12
	push {r12, lr}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #8
	movw r0, #6656
	movt r0, #0
	add r0, r8, r0
	movw r1, #0
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
	movw r12, #7680
	movt r12, #0
	add r12, r8, r12
	push {r12, lr}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #8
	movw r0, #7680
	movt r0, #0
	add r0, r8, r0
	movw r1, #0
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
	movw r12, #8704
	movt r12, #0
	add r12, r8, r12
	push {r12, lr}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #8
	movw r0, #8704
	movt r0, #0
	add r0, r8, r0
	movw r1, #0
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
	movw r12, #9728
	movt r12, #0
	add r12, r8, r12
	push {r12, lr}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #8
	movw r0, #9728
	movt r0, #0
	add r0, r8, r0
	movw r1, #0
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
	movw r12, #10752
	movt r12, #0
	add r12, r8, r12
	push {r12, lr}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #8
	movw r0, #10752
	movt r0, #0
	add r0, r8, r0
	movw r1, #0
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
	movw r12, #11776
	movt r12, #0
	add r12, r8, r12
	push {r12, lr}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #8
	movw r0, #11776
	movt r0, #0
	add r0, r8, r0
	movw r1, #0
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
	movw r12, #12800
	movt r12, #0
	add r12, r8, r12
	push {r12, lr}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #8
	movw r0, #12800
	movt r0, #0
	add r0, r8, r0
	movw r1, #0
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
	movw r12, #13824
	movt r12, #0
	add r12, r8, r12
	push {r12, lr}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #8
	movw r0, #13824
	movt r0, #0
	add r0, r8, r0
	movw r1, #0
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	ldr r7, [sp, #4]
	ldr r8, [sp, #8]
	ldr lr, [sp, #12]
	ldr r4, [sp], #16
	bx lr

vg_mldsa44_sign:
	push {r4, lr}
	ldr r12, [sp, #8]
	mov r4, lr
	movw lr, #0
	movt lr, #0
	push {r12, lr}
	bl {vg_mldsa44_sign_with_cache}
	ldr r12, [sp], #8
	mov lr, r4
	ldr r4, [sp], #8
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

vg_mldsa44_sign_message_prepared:
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
	bl {vg_mldsa44_sign_prepared}
	ldr r12, [sp], #8
	ldr lr, [r7, #908]
	ldr r7, [r7, #904]
	b 21f
20:
	mov r0, #2
21:
	bx lr

vg_mldsa44_verify:
	push {r4, lr}
	mov r4, lr
	movw r12, #0
	movt r12, #0
	push {r12, lr}
	bl {vg_mldsa44_verify_with_cache}
	ldr r12, [sp], #8
	mov lr, r4
	ldr r4, [sp], #8
	bx lr

vg_mldsa44_verify_message_cached:
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
	ldr r1, [sp, #12]
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
	ldr r3, [r7, #932]
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

vg_mldsa44_verify_message_prepared:
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
	ldr r1, [sp, #12]
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
	ldr r3, [r7, #932]
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
	bl {vg_mldsa44_verify_prepared}
	ldr lr, [r7, #908]
	ldr r7, [r7, #904]
	b 21f
20:
	mov r0, #2
21:
	bx lr
