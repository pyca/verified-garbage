// The functions of `src/mldsa65.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa65_keygen:
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
	movw r12, #6
	strb r12, [r7, #896]
	movw r12, #5
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
	movw r12, #4
	strb r12, [r7, #1184]
	movw r12, #0
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
	movw r12, #0
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
	movw r12, #1
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
	movw r12, #2
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
	movw r12, #3
	strb r12, [r7, #1184]
	movw r12, #1
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
	movw r12, #4
	strb r12, [r7, #1184]
	movw r12, #1
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
	movw r12, #0
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
	movw r12, #1
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
	movw r12, #2
	strb r12, [r7, #1184]
	movw r12, #2
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
	movw r12, #3
	strb r12, [r7, #1184]
	movw r12, #2
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
	movw r12, #4
	strb r12, [r7, #1184]
	movw r12, #2
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
	movw r12, #0
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
	movw r12, #1
	strb r12, [r7, #1184]
	movw r12, #3
	strb r12, [r7, #1185]
	movw r0, #1152
	movt r0, #0
	add r0, r7, r0
	movw r1, #20480
	movt r1, #0
	add r1, r7, r1
	movw r2, #2048
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
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
	movw r12, #2
	strb r12, [r7, #1184]
	movw r12, #3
	strb r12, [r7, #1185]
	movw r0, #1152
	movt r0, #0
	add r0, r7, r0
	movw r1, #21504
	movt r1, #0
	add r1, r7, r1
	movw r2, #2048
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
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
	movw r12, #3
	strb r12, [r7, #1184]
	movw r12, #3
	strb r12, [r7, #1185]
	movw r0, #1152
	movt r0, #0
	add r0, r7, r0
	movw r1, #22528
	movt r1, #0
	add r1, r7, r1
	movw r2, #2048
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
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
	movw r12, #4
	strb r12, [r7, #1184]
	movw r12, #3
	strb r12, [r7, #1185]
	movw r0, #1152
	movt r0, #0
	add r0, r7, r0
	movw r1, #23552
	movt r1, #0
	add r1, r7, r1
	movw r2, #2048
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
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
	movw r12, #0
	strb r12, [r7, #1184]
	movw r12, #4
	strb r12, [r7, #1185]
	movw r0, #1152
	movt r0, #0
	add r0, r7, r0
	movw r1, #24576
	movt r1, #0
	add r1, r7, r1
	movw r2, #2048
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
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
	movw r12, #1
	strb r12, [r7, #1184]
	movw r12, #4
	strb r12, [r7, #1185]
	movw r0, #1152
	movt r0, #0
	add r0, r7, r0
	movw r1, #25600
	movt r1, #0
	add r1, r7, r1
	movw r2, #2048
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
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
	movw r12, #2
	strb r12, [r7, #1184]
	movw r12, #4
	strb r12, [r7, #1185]
	movw r0, #1152
	movt r0, #0
	add r0, r7, r0
	movw r1, #26624
	movt r1, #0
	add r1, r7, r1
	movw r2, #2048
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
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
	movw r12, #3
	strb r12, [r7, #1184]
	movw r12, #4
	strb r12, [r7, #1185]
	movw r0, #1152
	movt r0, #0
	add r0, r7, r0
	movw r1, #27648
	movt r1, #0
	add r1, r7, r1
	movw r2, #2048
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_rej_ntt_poly}
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
	movw r12, #4
	strb r12, [r7, #1184]
	movw r12, #4
	strb r12, [r7, #1185]
	movw r0, #1152
	movt r0, #0
	add r0, r7, r0
	movw r1, #28672
	movt r1, #0
	add r1, r7, r1
	movw r2, #2048
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
226:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 226b
	movw r12, #0
	strb r12, [r7, #1184]
	movw r12, #5
	strb r12, [r7, #1185]
	movw r0, #1152
	movt r0, #0
	add r0, r7, r0
	movw r1, #29696
	movt r1, #0
	add r1, r7, r1
	movw r2, #2048
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
227:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 227b
	movw r12, #1
	strb r12, [r7, #1184]
	movw r12, #5
	strb r12, [r7, #1185]
	movw r0, #1152
	movt r0, #0
	add r0, r7, r0
	movw r1, #30720
	movt r1, #0
	add r1, r7, r1
	movw r2, #2048
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
228:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 228b
	movw r12, #2
	strb r12, [r7, #1184]
	movw r12, #5
	strb r12, [r7, #1185]
	movw r0, #1152
	movt r0, #0
	add r0, r7, r0
	movw r1, #31744
	movt r1, #0
	add r1, r7, r1
	movw r2, #2048
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
229:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 229b
	movw r12, #3
	strb r12, [r7, #1184]
	movw r12, #5
	strb r12, [r7, #1185]
	movw r0, #1152
	movt r0, #0
	add r0, r7, r0
	movw r1, #32768
	movt r1, #0
	add r1, r7, r1
	movw r2, #2048
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
230:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 230b
	movw r12, #4
	strb r12, [r7, #1184]
	movw r12, #5
	strb r12, [r7, #1185]
	movw r0, #1152
	movt r0, #0
	add r0, r7, r0
	movw r1, #33792
	movt r1, #0
	add r1, r7, r1
	movw r2, #2048
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
231:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 231b
	movw r12, #0
	strb r12, [r7, #1280]
	movw r0, #1216
	movt r0, #0
	add r0, r7, r0
	movw r1, #4
	movt r1, #0
	movw r2, #34816
	movt r2, #0
	add r2, r7, r2
	movw r3, #2048
	movt r3, #0
	add r3, r7, r3
	bl {vg_mldsa_rej_bounded_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #34816
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
	movw r12, #1
	strb r12, [r7, #1280]
	movw r0, #1216
	movt r0, #0
	add r0, r7, r0
	movw r1, #4
	movt r1, #0
	movw r2, #35840
	movt r2, #0
	add r2, r7, r2
	movw r3, #2048
	movt r3, #0
	add r3, r7, r3
	bl {vg_mldsa_rej_bounded_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #35840
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
	movw r12, #2
	strb r12, [r7, #1280]
	movw r0, #1216
	movt r0, #0
	add r0, r7, r0
	movw r1, #4
	movt r1, #0
	movw r2, #36864
	movt r2, #0
	add r2, r7, r2
	movw r3, #2048
	movt r3, #0
	add r3, r7, r3
	bl {vg_mldsa_rej_bounded_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #36864
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
	movw r12, #3
	strb r12, [r7, #1280]
	movw r0, #1216
	movt r0, #0
	add r0, r7, r0
	movw r1, #4
	movt r1, #0
	movw r2, #37888
	movt r2, #0
	add r2, r7, r2
	movw r3, #2048
	movt r3, #0
	add r3, r7, r3
	bl {vg_mldsa_rej_bounded_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #37888
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
	movw r12, #4
	strb r12, [r7, #1280]
	movw r0, #1216
	movt r0, #0
	add r0, r7, r0
	movw r1, #4
	movt r1, #0
	movw r2, #38912
	movt r2, #0
	add r2, r7, r2
	movw r3, #2048
	movt r3, #0
	add r3, r7, r3
	bl {vg_mldsa_rej_bounded_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #38912
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
	movw r12, #5
	strb r12, [r7, #1280]
	movw r0, #1216
	movt r0, #0
	add r0, r7, r0
	movw r1, #4
	movt r1, #0
	movw r2, #39936
	movt r2, #0
	add r2, r7, r2
	movw r3, #2048
	movt r3, #0
	add r3, r7, r3
	bl {vg_mldsa_rej_bounded_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #39936
	movt r1, #0
	add r1, r7, r1
	mov r2, #256
237:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 237b
	movw r12, #6
	strb r12, [r7, #1280]
	movw r0, #1216
	movt r0, #0
	add r0, r7, r0
	movw r1, #4
	movt r1, #0
	movw r2, #40960
	movt r2, #0
	add r2, r7, r2
	movw r3, #2048
	movt r3, #0
	add r3, r7, r3
	bl {vg_mldsa_rej_bounded_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #40960
	movt r1, #0
	add r1, r7, r1
	mov r2, #256
238:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 238b
	movw r12, #7
	strb r12, [r7, #1280]
	movw r0, #1216
	movt r0, #0
	add r0, r7, r0
	movw r1, #4
	movt r1, #0
	movw r2, #41984
	movt r2, #0
	add r2, r7, r2
	movw r3, #2048
	movt r3, #0
	add r3, r7, r3
	bl {vg_mldsa_rej_bounded_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #41984
	movt r1, #0
	add r1, r7, r1
	mov r2, #256
239:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 239b
	movw r12, #8
	strb r12, [r7, #1280]
	movw r0, #1216
	movt r0, #0
	add r0, r7, r0
	movw r1, #4
	movt r1, #0
	movw r2, #43008
	movt r2, #0
	add r2, r7, r2
	movw r3, #2048
	movt r3, #0
	add r3, r7, r3
	bl {vg_mldsa_rej_bounded_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #43008
	movt r1, #0
	add r1, r7, r1
	mov r2, #256
240:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 240b
	movw r12, #9
	strb r12, [r7, #1280]
	movw r0, #1216
	movt r0, #0
	add r0, r7, r0
	movw r1, #4
	movt r1, #0
	movw r2, #44032
	movt r2, #0
	add r2, r7, r2
	movw r3, #2048
	movt r3, #0
	add r3, r7, r3
	bl {vg_mldsa_rej_bounded_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #44032
	movt r1, #0
	add r1, r7, r1
	mov r2, #256
241:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 241b
	movw r12, #10
	strb r12, [r7, #1280]
	movw r0, #1216
	movt r0, #0
	add r0, r7, r0
	movw r1, #4
	movt r1, #0
	movw r2, #45056
	movt r2, #0
	add r2, r7, r2
	movw r3, #2048
	movt r3, #0
	add r3, r7, r3
	bl {vg_mldsa_rej_bounded_poly}
	and r11, r11, r0
	mov r12, #0
	sub r12, r12, r0
	movw r1, #45056
	movt r1, #0
	add r1, r7, r1
	mov r2, #256
242:
	ldr r3, [r1, #0]
	and r3, r3, r12
	str r3, [r1, #0]
	add r1, r1, #4
	subs r2, r2, #1
	bne 242b
	add r0, r7, #1024
	add r1, r5, #0
	mov r2, #32
243:
	ldrb r3, [r0, #0]
	strb r3, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs r2, r2, #1
	bne 243b
	add r0, r7, #1024
	add r1, r6, #0
	mov r2, #32
244:
	ldrb r3, [r0, #0]
	strb r3, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs r2, r2, #1
	bne 244b
	add r0, r7, #1120
	add r1, r6, #32
	mov r2, #32
245:
	ldrb r3, [r0, #0]
	strb r3, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs r2, r2, #1
	bne 245b
	movw r0, #34816
	movt r0, #0
	add r0, r7, r0
	movw r1, #4
	movt r1, #0
	movw r2, #4
	movt r2, #0
	movw r3, #128
	movt r3, #0
	add r3, r6, r3
	movw r12, #128
	movt r12, #0
	push {r12}
	bl {vg_mldsa_bit_pack}
	ldr r12, [sp], #4
	movw r0, #35840
	movt r0, #0
	add r0, r7, r0
	movw r1, #4
	movt r1, #0
	movw r2, #4
	movt r2, #0
	movw r3, #256
	movt r3, #0
	add r3, r6, r3
	movw r12, #128
	movt r12, #0
	push {r12}
	bl {vg_mldsa_bit_pack}
	ldr r12, [sp], #4
	movw r0, #36864
	movt r0, #0
	add r0, r7, r0
	movw r1, #4
	movt r1, #0
	movw r2, #4
	movt r2, #0
	movw r3, #384
	movt r3, #0
	add r3, r6, r3
	movw r12, #128
	movt r12, #0
	push {r12}
	bl {vg_mldsa_bit_pack}
	ldr r12, [sp], #4
	movw r0, #37888
	movt r0, #0
	add r0, r7, r0
	movw r1, #4
	movt r1, #0
	movw r2, #4
	movt r2, #0
	movw r3, #512
	movt r3, #0
	add r3, r6, r3
	movw r12, #128
	movt r12, #0
	push {r12}
	bl {vg_mldsa_bit_pack}
	ldr r12, [sp], #4
	movw r0, #38912
	movt r0, #0
	add r0, r7, r0
	movw r1, #4
	movt r1, #0
	movw r2, #4
	movt r2, #0
	movw r3, #640
	movt r3, #0
	add r3, r6, r3
	movw r12, #128
	movt r12, #0
	push {r12}
	bl {vg_mldsa_bit_pack}
	ldr r12, [sp], #4
	movw r0, #39936
	movt r0, #0
	add r0, r7, r0
	movw r1, #4
	movt r1, #0
	movw r2, #4
	movt r2, #0
	movw r3, #768
	movt r3, #0
	add r3, r6, r3
	movw r12, #128
	movt r12, #0
	push {r12}
	bl {vg_mldsa_bit_pack}
	ldr r12, [sp], #4
	movw r0, #40960
	movt r0, #0
	add r0, r7, r0
	movw r1, #4
	movt r1, #0
	movw r2, #4
	movt r2, #0
	movw r3, #896
	movt r3, #0
	add r3, r6, r3
	movw r12, #128
	movt r12, #0
	push {r12}
	bl {vg_mldsa_bit_pack}
	ldr r12, [sp], #4
	movw r0, #41984
	movt r0, #0
	add r0, r7, r0
	movw r1, #4
	movt r1, #0
	movw r2, #4
	movt r2, #0
	movw r3, #1024
	movt r3, #0
	add r3, r6, r3
	movw r12, #128
	movt r12, #0
	push {r12}
	bl {vg_mldsa_bit_pack}
	ldr r12, [sp], #4
	movw r0, #43008
	movt r0, #0
	add r0, r7, r0
	movw r1, #4
	movt r1, #0
	movw r2, #4
	movt r2, #0
	movw r3, #1152
	movt r3, #0
	add r3, r6, r3
	movw r12, #128
	movt r12, #0
	push {r12}
	bl {vg_mldsa_bit_pack}
	ldr r12, [sp], #4
	movw r0, #44032
	movt r0, #0
	add r0, r7, r0
	movw r1, #4
	movt r1, #0
	movw r2, #4
	movt r2, #0
	movw r3, #1280
	movt r3, #0
	add r3, r6, r3
	movw r12, #128
	movt r12, #0
	push {r12}
	bl {vg_mldsa_bit_pack}
	ldr r12, [sp], #4
	movw r0, #45056
	movt r0, #0
	add r0, r7, r0
	movw r1, #4
	movt r1, #0
	movw r2, #4
	movt r2, #0
	movw r3, #1408
	movt r3, #0
	add r3, r6, r3
	movw r12, #128
	movt r12, #0
	push {r12}
	bl {vg_mldsa_bit_pack}
	ldr r12, [sp], #4
	movw r0, #34816
	movt r0, #0
	add r0, r7, r0
	movw r1, #2048
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #35840
	movt r0, #0
	add r0, r7, r0
	movw r1, #2048
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #36864
	movt r0, #0
	add r0, r7, r0
	movw r1, #2048
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #37888
	movt r0, #0
	add r0, r7, r0
	movw r1, #2048
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #38912
	movt r0, #0
	add r0, r7, r0
	movw r1, #2048
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #4096
	movt r1, #0
	add r1, r7, r1
	movw r2, #34816
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_ntt}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #5120
	movt r1, #0
	add r1, r7, r1
	movw r2, #35840
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #6144
	movt r1, #0
	add r1, r7, r1
	movw r2, #36864
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #7168
	movt r1, #0
	add r1, r7, r1
	movw r2, #37888
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #8192
	movt r1, #0
	add r1, r7, r1
	movw r2, #38912
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #2048
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_inv_ntt}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #39936
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_add}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #47104
	movt r1, #0
	add r1, r7, r1
	movw r2, #48128
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_power2round}
	movw r0, #47104
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
	movw r0, #48128
	movt r0, #0
	add r0, r7, r0
	movw r1, #4095
	movt r1, #0
	movw r2, #4096
	movt r2, #0
	movw r3, #1536
	movt r3, #0
	add r3, r6, r3
	movw r12, #416
	movt r12, #0
	push {r12}
	bl {vg_mldsa_bit_pack}
	ldr r12, [sp], #4
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #9216
	movt r1, #0
	add r1, r7, r1
	movw r2, #34816
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_ntt}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #10240
	movt r1, #0
	add r1, r7, r1
	movw r2, #35840
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #11264
	movt r1, #0
	add r1, r7, r1
	movw r2, #36864
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #12288
	movt r1, #0
	add r1, r7, r1
	movw r2, #37888
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #13312
	movt r1, #0
	add r1, r7, r1
	movw r2, #38912
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #2048
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_inv_ntt}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #40960
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_add}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #47104
	movt r1, #0
	add r1, r7, r1
	movw r2, #48128
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_power2round}
	movw r0, #47104
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
	movw r0, #48128
	movt r0, #0
	add r0, r7, r0
	movw r1, #4095
	movt r1, #0
	movw r2, #4096
	movt r2, #0
	movw r3, #1952
	movt r3, #0
	add r3, r6, r3
	movw r12, #416
	movt r12, #0
	push {r12}
	bl {vg_mldsa_bit_pack}
	ldr r12, [sp], #4
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #14336
	movt r1, #0
	add r1, r7, r1
	movw r2, #34816
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_ntt}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #15360
	movt r1, #0
	add r1, r7, r1
	movw r2, #35840
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #16384
	movt r1, #0
	add r1, r7, r1
	movw r2, #36864
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #17408
	movt r1, #0
	add r1, r7, r1
	movw r2, #37888
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #18432
	movt r1, #0
	add r1, r7, r1
	movw r2, #38912
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #2048
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_inv_ntt}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #41984
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_add}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #47104
	movt r1, #0
	add r1, r7, r1
	movw r2, #48128
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_power2round}
	movw r0, #47104
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
	movw r0, #48128
	movt r0, #0
	add r0, r7, r0
	movw r1, #4095
	movt r1, #0
	movw r2, #4096
	movt r2, #0
	movw r3, #2368
	movt r3, #0
	add r3, r6, r3
	movw r12, #416
	movt r12, #0
	push {r12}
	bl {vg_mldsa_bit_pack}
	ldr r12, [sp], #4
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #19456
	movt r1, #0
	add r1, r7, r1
	movw r2, #34816
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_ntt}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #20480
	movt r1, #0
	add r1, r7, r1
	movw r2, #35840
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #21504
	movt r1, #0
	add r1, r7, r1
	movw r2, #36864
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #22528
	movt r1, #0
	add r1, r7, r1
	movw r2, #37888
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #23552
	movt r1, #0
	add r1, r7, r1
	movw r2, #38912
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #2048
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_inv_ntt}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #43008
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_add}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #47104
	movt r1, #0
	add r1, r7, r1
	movw r2, #48128
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_power2round}
	movw r0, #47104
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
	movw r0, #48128
	movt r0, #0
	add r0, r7, r0
	movw r1, #4095
	movt r1, #0
	movw r2, #4096
	movt r2, #0
	movw r3, #2784
	movt r3, #0
	add r3, r6, r3
	movw r12, #416
	movt r12, #0
	push {r12}
	bl {vg_mldsa_bit_pack}
	ldr r12, [sp], #4
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #24576
	movt r1, #0
	add r1, r7, r1
	movw r2, #34816
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_ntt}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #25600
	movt r1, #0
	add r1, r7, r1
	movw r2, #35840
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #26624
	movt r1, #0
	add r1, r7, r1
	movw r2, #36864
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #27648
	movt r1, #0
	add r1, r7, r1
	movw r2, #37888
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #28672
	movt r1, #0
	add r1, r7, r1
	movw r2, #38912
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #2048
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_inv_ntt}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #44032
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_add}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #47104
	movt r1, #0
	add r1, r7, r1
	movw r2, #48128
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_power2round}
	movw r0, #47104
	movt r0, #0
	add r0, r7, r0
	movw r1, #1023
	movt r1, #0
	movw r2, #1312
	movt r2, #0
	add r2, r5, r2
	movw r3, #320
	movt r3, #0
	bl {vg_mldsa_simple_bit_pack}
	movw r0, #48128
	movt r0, #0
	add r0, r7, r0
	movw r1, #4095
	movt r1, #0
	movw r2, #4096
	movt r2, #0
	movw r3, #3200
	movt r3, #0
	add r3, r6, r3
	movw r12, #416
	movt r12, #0
	push {r12}
	bl {vg_mldsa_bit_pack}
	ldr r12, [sp], #4
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #29696
	movt r1, #0
	add r1, r7, r1
	movw r2, #34816
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_ntt}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #30720
	movt r1, #0
	add r1, r7, r1
	movw r2, #35840
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #31744
	movt r1, #0
	add r1, r7, r1
	movw r2, #36864
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #32768
	movt r1, #0
	add r1, r7, r1
	movw r2, #37888
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #33792
	movt r1, #0
	add r1, r7, r1
	movw r2, #38912
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_multiply_add_ntt}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #2048
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_inv_ntt}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #45056
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_add}
	movw r0, #46080
	movt r0, #0
	add r0, r7, r0
	movw r1, #47104
	movt r1, #0
	add r1, r7, r1
	movw r2, #48128
	movt r2, #0
	add r2, r7, r2
	bl {vg_mldsa_power2round}
	movw r0, #47104
	movt r0, #0
	add r0, r7, r0
	movw r1, #1023
	movt r1, #0
	movw r2, #1632
	movt r2, #0
	add r2, r5, r2
	movw r3, #320
	movt r3, #0
	bl {vg_mldsa_simple_bit_pack}
	movw r0, #48128
	movt r0, #0
	add r0, r7, r0
	movw r1, #4095
	movt r1, #0
	movw r2, #4096
	movt r2, #0
	movw r3, #3616
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
	mov r12, #1952
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

vg_mldsa65_pk_tr:
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
	mov r12, #1952
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

vg_mldsa65_prepare_verifying_key:
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
	movw r2, #1952
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
	movw r1, #1952
	movt r1, #0
	add r1, r8, r1
	bl {vg_mldsa_unpack_t1}
	movw r0, #1952
	movt r0, #0
	add r0, r8, r0
	movw r1, #0
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #352
	movt r0, #0
	add r0, r4, r0
	movw r1, #2976
	movt r1, #0
	add r1, r8, r1
	bl {vg_mldsa_unpack_t1}
	movw r0, #2976
	movt r0, #0
	add r0, r8, r0
	movw r1, #0
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #672
	movt r0, #0
	add r0, r4, r0
	movw r1, #4000
	movt r1, #0
	add r1, r8, r1
	bl {vg_mldsa_unpack_t1}
	movw r0, #4000
	movt r0, #0
	add r0, r8, r0
	movw r1, #0
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #992
	movt r0, #0
	add r0, r4, r0
	movw r1, #5024
	movt r1, #0
	add r1, r8, r1
	bl {vg_mldsa_unpack_t1}
	movw r0, #5024
	movt r0, #0
	add r0, r8, r0
	movw r1, #0
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #1312
	movt r0, #0
	add r0, r4, r0
	movw r1, #6048
	movt r1, #0
	add r1, r8, r1
	bl {vg_mldsa_unpack_t1}
	movw r0, #6048
	movt r0, #0
	add r0, r8, r0
	movw r1, #0
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #1632
	movt r0, #0
	add r0, r4, r0
	movw r1, #7072
	movt r1, #0
	add r1, r8, r1
	bl {vg_mldsa_unpack_t1}
	movw r0, #7072
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

vg_mldsa65_prepare_signing_key:
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
	movw r2, #4032
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
	movw r1, #128
	movt r1, #0
	movw r2, #4
	movt r2, #0
	movw r3, #4
	movt r3, #0
	movw r12, #4032
	movt r12, #0
	add r12, r8, r12
	push {r12, lr}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #8
	movw r0, #4032
	movt r0, #0
	add r0, r8, r0
	movw r1, #0
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #256
	movt r0, #0
	add r0, r4, r0
	movw r1, #128
	movt r1, #0
	movw r2, #4
	movt r2, #0
	movw r3, #4
	movt r3, #0
	movw r12, #5056
	movt r12, #0
	add r12, r8, r12
	push {r12, lr}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #8
	movw r0, #5056
	movt r0, #0
	add r0, r8, r0
	movw r1, #0
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #384
	movt r0, #0
	add r0, r4, r0
	movw r1, #128
	movt r1, #0
	movw r2, #4
	movt r2, #0
	movw r3, #4
	movt r3, #0
	movw r12, #6080
	movt r12, #0
	add r12, r8, r12
	push {r12, lr}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #8
	movw r0, #6080
	movt r0, #0
	add r0, r8, r0
	movw r1, #0
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #512
	movt r0, #0
	add r0, r4, r0
	movw r1, #128
	movt r1, #0
	movw r2, #4
	movt r2, #0
	movw r3, #4
	movt r3, #0
	movw r12, #7104
	movt r12, #0
	add r12, r8, r12
	push {r12, lr}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #8
	movw r0, #7104
	movt r0, #0
	add r0, r8, r0
	movw r1, #0
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #640
	movt r0, #0
	add r0, r4, r0
	movw r1, #128
	movt r1, #0
	movw r2, #4
	movt r2, #0
	movw r3, #4
	movt r3, #0
	movw r12, #8128
	movt r12, #0
	add r12, r8, r12
	push {r12, lr}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #8
	movw r0, #8128
	movt r0, #0
	add r0, r8, r0
	movw r1, #0
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #768
	movt r0, #0
	add r0, r4, r0
	movw r1, #128
	movt r1, #0
	movw r2, #4
	movt r2, #0
	movw r3, #4
	movt r3, #0
	movw r12, #9152
	movt r12, #0
	add r12, r8, r12
	push {r12, lr}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #8
	movw r0, #9152
	movt r0, #0
	add r0, r8, r0
	movw r1, #0
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #896
	movt r0, #0
	add r0, r4, r0
	movw r1, #128
	movt r1, #0
	movw r2, #4
	movt r2, #0
	movw r3, #4
	movt r3, #0
	movw r12, #10176
	movt r12, #0
	add r12, r8, r12
	push {r12, lr}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #8
	movw r0, #10176
	movt r0, #0
	add r0, r8, r0
	movw r1, #0
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #1024
	movt r0, #0
	add r0, r4, r0
	movw r1, #128
	movt r1, #0
	movw r2, #4
	movt r2, #0
	movw r3, #4
	movt r3, #0
	movw r12, #11200
	movt r12, #0
	add r12, r8, r12
	push {r12, lr}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #8
	movw r0, #11200
	movt r0, #0
	add r0, r8, r0
	movw r1, #0
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #1152
	movt r0, #0
	add r0, r4, r0
	movw r1, #128
	movt r1, #0
	movw r2, #4
	movt r2, #0
	movw r3, #4
	movt r3, #0
	movw r12, #12224
	movt r12, #0
	add r12, r8, r12
	push {r12, lr}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #8
	movw r0, #12224
	movt r0, #0
	add r0, r8, r0
	movw r1, #0
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #1280
	movt r0, #0
	add r0, r4, r0
	movw r1, #128
	movt r1, #0
	movw r2, #4
	movt r2, #0
	movw r3, #4
	movt r3, #0
	movw r12, #13248
	movt r12, #0
	add r12, r8, r12
	push {r12, lr}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #8
	movw r0, #13248
	movt r0, #0
	add r0, r8, r0
	movw r1, #0
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #1408
	movt r0, #0
	add r0, r4, r0
	movw r1, #128
	movt r1, #0
	movw r2, #4
	movt r2, #0
	movw r3, #4
	movt r3, #0
	movw r12, #14272
	movt r12, #0
	add r12, r8, r12
	push {r12, lr}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #8
	movw r0, #14272
	movt r0, #0
	add r0, r8, r0
	movw r1, #0
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #1536
	movt r0, #0
	add r0, r4, r0
	movw r1, #416
	movt r1, #0
	movw r2, #4095
	movt r2, #0
	movw r3, #4096
	movt r3, #0
	movw r12, #15296
	movt r12, #0
	add r12, r8, r12
	push {r12, lr}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #8
	movw r0, #15296
	movt r0, #0
	add r0, r8, r0
	movw r1, #0
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #1952
	movt r0, #0
	add r0, r4, r0
	movw r1, #416
	movt r1, #0
	movw r2, #4095
	movt r2, #0
	movw r3, #4096
	movt r3, #0
	movw r12, #16320
	movt r12, #0
	add r12, r8, r12
	push {r12, lr}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #8
	movw r0, #16320
	movt r0, #0
	add r0, r8, r0
	movw r1, #0
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #2368
	movt r0, #0
	add r0, r4, r0
	movw r1, #416
	movt r1, #0
	movw r2, #4095
	movt r2, #0
	movw r3, #4096
	movt r3, #0
	movw r12, #17344
	movt r12, #0
	add r12, r8, r12
	push {r12, lr}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #8
	movw r0, #17344
	movt r0, #0
	add r0, r8, r0
	movw r1, #0
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #2784
	movt r0, #0
	add r0, r4, r0
	movw r1, #416
	movt r1, #0
	movw r2, #4095
	movt r2, #0
	movw r3, #4096
	movt r3, #0
	movw r12, #18368
	movt r12, #0
	add r12, r8, r12
	push {r12, lr}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #8
	movw r0, #18368
	movt r0, #0
	add r0, r8, r0
	movw r1, #0
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #3200
	movt r0, #0
	add r0, r4, r0
	movw r1, #416
	movt r1, #0
	movw r2, #4095
	movt r2, #0
	movw r3, #4096
	movt r3, #0
	movw r12, #19392
	movt r12, #0
	add r12, r8, r12
	push {r12, lr}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #8
	movw r0, #19392
	movt r0, #0
	add r0, r8, r0
	movw r1, #0
	movt r1, #0
	add r1, r7, r1
	bl {vg_mldsa_ntt}
	movw r0, #3616
	movt r0, #0
	add r0, r4, r0
	movw r1, #416
	movt r1, #0
	movw r2, #4095
	movt r2, #0
	movw r3, #4096
	movt r3, #0
	movw r12, #20416
	movt r12, #0
	add r12, r8, r12
	push {r12, lr}
	bl {vg_mldsa_bit_unpack}
	ldr r12, [sp], #8
	movw r0, #20416
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

vg_mldsa65_sign:
	push {r4, lr}
	ldr r12, [sp, #8]
	mov r4, lr
	movw lr, #0
	movt lr, #0
	push {r12, lr}
	bl {vg_mldsa65_sign_with_cache}
	ldr r12, [sp], #8
	mov lr, r4
	ldr r4, [sp], #8
	bx lr

vg_mldsa65_sign_message:
	ldr r12, [sp, #0]
	lsr r12, r12, #8
	cmp r12, #0
	bne 20f
	ldr r12, [sp, #12]
	str r7, [r12, #0]
	movw r7, #37888
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
	bl {vg_mldsa65_sign}
	ldr r12, [sp], #8
	ldr lr, [r7, #908]
	ldr r7, [r7, #904]
	b 21f
20:
	mov r0, #2
21:
	bx lr

vg_mldsa65_sign_message_prepared:
	ldr r12, [sp, #0]
	lsr r12, r12, #8
	cmp r12, #0
	bne 20f
	ldr r12, [sp, #12]
	str r7, [r12, #0]
	movw r7, #37888
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
	bl {vg_mldsa65_sign_prepared}
	ldr r12, [sp], #8
	ldr lr, [r7, #908]
	ldr r7, [r7, #904]
	b 21f
20:
	mov r0, #2
21:
	bx lr

vg_mldsa65_verify:
	push {r4, lr}
	mov r4, lr
	movw r12, #0
	movt r12, #0
	push {r12, lr}
	bl {vg_mldsa65_verify_with_cache}
	ldr r12, [sp], #8
	mov lr, r4
	ldr r4, [sp], #8
	bx lr

vg_mldsa65_verify_message_cached:
	ldr r12, [sp, #0]
	lsr r12, r12, #8
	cmp r12, #0
	bne 20f
	ldr r12, [sp, #8]
	str r7, [r12, #0]
	movw r7, #37888
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
	bl {vg_mldsa65_verify}
	ldr lr, [r7, #908]
	ldr r7, [r7, #904]
	b 21f
20:
	mov r0, #2
21:
	bx lr

vg_mldsa65_verify_message_prepared:
	ldr r12, [sp, #0]
	lsr r12, r12, #8
	cmp r12, #0
	bne 20f
	ldr r12, [sp, #8]
	str r7, [r12, #0]
	movw r7, #37888
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
	bl {vg_mldsa65_verify_prepared}
	ldr lr, [r7, #908]
	ldr r7, [r7, #904]
	b 21f
20:
	mov r0, #2
21:
	bx lr
