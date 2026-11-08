// The functions of `src/internal/vg_mlkem768_decaps_body.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem768_decaps_body:
	str r4, [r3, #840]
	str r5, [r3, #844]
	str r6, [r3, #848]
	str r7, [r3, #852]
	str r8, [r3, #856]
	str r9, [r3, #860]
	str r10, [r3, #864]
	str r11, [r3, #868]
	str lr, [r3, #872]
	str r2, [r3, #876]
	mov r4, r0
	mov r6, r1
	mov r7, r3
	add r0, r6, #0
	add r1, r7, #24576
	mov r2, #1088
20:
	ldrb r3, [r0, #0]
	strb r3, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs r2, r2, #1
	bne 20b
	add r6, r7, #24576
	mov r9, #0
21:
	add r0, r6, r9, lsl #8
	add r0, r0, r9, lsl #6
	mov r1, #320
	mov r2, #10
	add r3, r7, r9, lsl #10
	add r3, r3, #5120
	bl {vg_mlkem_decode_decompress}
	add r0, r7, r9, lsl #10
	add r0, r0, #5120
	add r1, r7, #18432
	bl {vg_mlkem_ntt}
	add r9, r9, #1
	cmp r9, #3
	bne 21b
	mov r9, #0
22:
	add r0, r4, r9, lsl #8
	add r0, r0, r9, lsl #7
	add r1, r7, r9, lsl #10
	add r1, r1, #2048
	bl {vg_mlkem_decode12}
	add r9, r9, #1
	cmp r9, #3
	bne 22b
	add r0, r7, #13312
	mov r1, #0
	mov r2, #256
23:
	str r1, [r0, #0]
	add r0, r0, #4
	subs r2, r2, #1
	bne 23b
	mov r10, #0
24:
	add r0, r7, #14336
	add r1, r7, r10, lsl #10
	add r1, r1, #2048
	add r2, r7, r10, lsl #10
	add r2, r2, #5120
	add r3, r7, #18432
	bl {vg_mlkem_multiply_ntts}
	add r0, r7, #13312
	add r1, r7, #14336
	bl {vg_mlkem_add}
	add r10, r10, #1
	cmp r10, #3
	bne 24b
	add r0, r7, #13312
	add r1, r7, #18432
	bl {vg_mlkem_inv_ntt}
	add r0, r6, #960
	mov r1, #128
	mov r2, #4
	add r3, r7, #11264
	bl {vg_mlkem_decode_decompress}
	add r0, r7, #11264
	add r1, r7, #13312
	bl {vg_mlkem_sub}
	add r0, r7, #11264
	mov r1, #1
	add r2, r7, #992
	mov r3, #32
	bl {vg_mlkem_compress_encode}
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
	mov r1, #72
	add lr, r7, #200
	add r3, r7, #992
	mov r12, #32
	push {r12, lr}
	bl {vg_keccak_absorb_scratch}
	ldr r12, [sp], #8
	mov r2, r0
	mov r0, r7
	mov r1, #72
	add lr, r7, #200
	add r3, r4, #2336
	mov r12, #32
	push {r12, lr}
	bl {vg_keccak_absorb_scratch}
	ldr r12, [sp], #8
	mov r2, r0
	mov r0, r7
	mov r1, #72
	add lr, r7, #200
	mov r3, #6
	push {lr}
	bl {vg_keccak_pad_scratch}
	ldr r12, [sp], #4
	mov r2, #0
	mov r0, r7
	mov r1, #72
	add lr, r7, #200
	add r3, r7, #888
	mov r12, #64
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
	mov r2, #0
	mov r0, r7
	mov r1, #136
	add lr, r7, #200
	add r3, r4, #2368
	mov r12, #32
	push {r12, lr}
	bl {vg_keccak_absorb_scratch}
	ldr r12, [sp], #8
	mov r2, r0
	mov r0, r7
	mov r1, #136
	add lr, r7, #200
	add r3, r7, #24576
	mov r12, #1088
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
	add r3, r7, #1184
	mov r12, #32
	push {r12, lr}
	bl {vg_keccak_squeeze_scratch}
	ldr r12, [sp], #8
	add r4, r4, #1152
	add r5, r7, #992
	add r8, r7, #19456
	add r0, r4, #1152
	add r1, r7, #1216
	mov r2, #32
25:
	ldrb r3, [r0, #0]
	strb r3, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs r2, r2, #1
	bne 25b
	mov r9, #0
26:
	add r0, r4, r9, lsl #8
	add r0, r0, r9, lsl #7
	add r1, r7, r9, lsl #10
	add r1, r1, #2048
	bl {vg_mlkem_decode12}
	add r9, r9, #1
	cmp r9, #3
	bne 26b
	mov r9, #0
27:
	strb r9, [r7, #952]
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
	add r3, r7, #920
	mov r12, #33
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
	add r1, r7, r9, lsl #10
	add r1, r1, #5120
	bl {vg_mlkem_cbd2}
	add r0, r7, r9, lsl #10
	add r0, r0, #5120
	add r1, r7, #18432
	bl {vg_mlkem_ntt}
	add r9, r9, #1
	cmp r9, #3
	bne 27b
	mov r9, #3
28:
	strb r9, [r7, #952]
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
	add r3, r7, #920
	mov r12, #33
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
	add r1, r7, r9, lsl #10
	add r1, r1, #5120
	bl {vg_mlkem_cbd2}
	add r9, r9, #1
	cmp r9, #7
	bne 28b
	mov r0, r5
	mov r1, #32
	mov r2, #1
	add r3, r7, #12288
	bl {vg_mlkem_decode_decompress}
	mov r11, #1
	mov r9, #0
29:
	add r0, r7, #13312
	mov r1, #0
	mov r2, #256
210:
	str r1, [r0, #0]
	add r0, r0, #4
	subs r2, r2, #1
	bne 210b
	mov r10, #0
211:
	strb r9, [r7, #1248]
	strb r10, [r7, #1249]
	add r0, r7, #1216
	add r1, r7, #15360
	add r2, r7, #16384
	bl {vg_mlkem_sample_ntt}
	and r11, r11, r0
	cmp r0, #0
	beq 212f
	add r1, r7, #15360
	b 213f
212:
	add r1, r7, r10, lsl #10
	add r1, r1, #5120
213:
	add r0, r7, #14336
	add r2, r7, r10, lsl #10
	add r2, r2, #5120
	add r3, r7, #18432
	bl {vg_mlkem_multiply_ntts}
	add r0, r7, #13312
	add r1, r7, #14336
	bl {vg_mlkem_add}
	add r10, r10, #1
	cmp r10, #3
	bne 211b
	add r0, r7, #13312
	add r1, r7, #18432
	bl {vg_mlkem_inv_ntt}
	add r0, r7, #13312
	add r1, r7, r9, lsl #10
	add r1, r1, #8192
	bl {vg_mlkem_add}
	add r0, r7, #13312
	mov r1, #10
	add r2, r8, r9, lsl #8
	add r2, r2, r9, lsl #6
	mov r3, #320
	bl {vg_mlkem_compress_encode}
	add r9, r9, #1
	cmp r9, #3
	bne 29b
	add r0, r7, #13312
	mov r1, #0
	mov r2, #256
214:
	str r1, [r0, #0]
	add r0, r0, #4
	subs r2, r2, #1
	bne 214b
	mov r10, #0
215:
	add r0, r7, #14336
	add r1, r7, r10, lsl #10
	add r1, r1, #2048
	add r2, r7, r10, lsl #10
	add r2, r2, #5120
	add r3, r7, #18432
	bl {vg_mlkem_multiply_ntts}
	add r0, r7, #13312
	add r1, r7, #14336
	bl {vg_mlkem_add}
	add r10, r10, #1
	cmp r10, #3
	bne 215b
	add r0, r7, #13312
	add r1, r7, #18432
	bl {vg_mlkem_inv_ntt}
	add r0, r7, #13312
	add r1, r7, #11264
	bl {vg_mlkem_add}
	add r0, r7, #13312
	add r1, r7, #12288
	bl {vg_mlkem_add}
	add r0, r7, #13312
	mov r1, #4
	add r2, r8, #960
	mov r3, #128
	bl {vg_mlkem_compress_encode}
	mov r0, r6
	add r1, r7, #19456
	mov r12, #0
	mov r9, #1088
216:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	orr r12, r12, r2
	add r0, r0, #1
	add r1, r1, #1
	subs r9, r9, #1
	bne 216b
	sub r12, r12, #1
	lsr r12, r12, #31
	mov r3, #0
	sub r12, r3, r12
	add r0, r7, #888
	add r1, r7, #1184
	ldr r2, [r7, #876]
	mov r9, #32
217:
	ldrb r3, [r0, #0]
	ldrb r10, [r1, #0]
	eor r3, r3, r10
	and r3, r3, r12
	eor r3, r3, r10
	strb r3, [r2, #0]
	add r0, r0, #1
	add r1, r1, #1
	add r2, r2, #1
	subs r9, r9, #1
	bne 217b
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
