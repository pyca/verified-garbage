// The functions of `src/internal/vg_mldsa44_sign_with_cache.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa44_sign_with_cache:
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
	ldr r9, [sp, #4]
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
	cmp r9, #0
	bne 23f
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
	b 24f
23:
	movw r0, #0
	movt r0, #0
	add r0, r9, r0
	movw r1, #26624
	movt r1, #0
	add r1, r7, r1
	movw r2, #12288
	movt r2, #0
25:
	ldrb r3, [r0, #0]
	strb r3, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs r2, r2, #1
	bne 25b
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
24:
	movw r0, #0
	movt r0, #0
	str r0, [r7, #896]
	movw r0, #814
	movt r0, #0
	str r0, [r7, #888]
26:
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
27:
	ldrb r3, [r0, #0]
	strb r3, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs r2, r2, #1
	bne 27b
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
28:
	ldrb r3, [r0, #0]
	strb r3, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs r2, r2, #1
	bne 28b
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
29:
	ldrb r3, [r0, #0]
	strb r3, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs r2, r2, #1
	bne 29b
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
210:
	ldrb r3, [r0, #0]
	strb r3, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs r2, r2, #1
	bne 210b
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
	bne 211f
	mov r11, #0
	movw r0, #1
	movt r0, #0
	str r0, [r7, #888]
	b 212f
211:
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
	bne 213f
	b 214f
213:
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
	bne 215f
	b 216f
215:
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
	bne 217f
	b 218f
217:
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
	bne 219f
	b 220f
219:
220:
218:
216:
214:
	cmp r11, #0
	bne 221f
	b 222f
221:
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
	bne 223f
	b 224f
223:
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
	bne 225f
	b 226f
225:
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
	bne 227f
	b 228f
227:
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
	bne 229f
	b 230f
229:
230:
228:
226:
224:
	cmp r11, #0
	bne 231f
	b 232f
231:
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
233:
	ldrb r3, [r0, #0]
	strb r3, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs r2, r2, #1
	bne 233b
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
234:
	ldrb r3, [r0, #0]
	strb r3, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs r2, r2, #1
	bne 234b
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
235:
	ldrb r3, [r0, #0]
	strb r3, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs r2, r2, #1
	bne 235b
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
236:
	ldrb r3, [r0, #0]
	strb r3, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs r2, r2, #1
	bne 236b
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
232:
222:
	cmp r11, #0
	bne 237f
	ldr r0, [r7, #896]
	add r0, r0, #4
	str r0, [r7, #896]
	b 238f
237:
	movw r0, #1
	movt r0, #0
	str r0, [r7, #888]
238:
212:
	ldr r0, [r7, #888]
	subs r0, r0, #1
	str r0, [r7, #888]
	bne 26b
	cmp r11, #0
	bne 239f
	b 240f
239:
	movw r0, #1040
	movt r0, #0
	add r0, r7, r0
	movw r1, #0
	movt r1, #0
	add r1, r8, r1
	movw r2, #32
	movt r2, #0
241:
	ldrb r3, [r0, #0]
	strb r3, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs r2, r2, #1
	bne 241b
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
240:
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
