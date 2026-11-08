// The functions of `src/internal/vg_mlkem1024_decaps_body_x2_sha3.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem1024_decaps_body_x2_sha3:
	str x24, [x3, #30392]
	str x30, [x3, #30400]
	str x25, [x3, #30408]
	str x26, [x3, #30416]
	str x27, [x3, #30424]
	str x28, [x3, #30432]
	add x25, x0, #0
	add x26, x1, #0
	add x27, x2, #0
	add x28, x3, #0
	movz x24, #1, lsl #0
	add x0, x26, #0
	movz x1, #352, lsl #0
	movz x2, #11, lsl #0
	movz x3, #26776, lsl #0
	add x3, x28, x3
	bl {vg_mlkem1024_decode_decompress}
	movz x0, #26776, lsl #0
	add x0, x28, x0
	movz x1, #20632, lsl #0
	add x1, x28, x1
	movz x10, #32, lsl #0
20:
	ldr q0, [x0, #0]
	ldr q1, [x0, #16]
	uzp1 v2.8h, v0.8h, v1.8h
	str q2, [x1, #0]
	add x0, x0, #32
	add x1, x1, #16
	sub x10, x10, #1
	cbnz x10, 20b
	movz x0, #20632, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem16_ntt}
	add x0, x26, #352
	movz x1, #352, lsl #0
	movz x2, #11, lsl #0
	movz x3, #26776, lsl #0
	add x3, x28, x3
	bl {vg_mlkem1024_decode_decompress}
	movz x0, #26776, lsl #0
	add x0, x28, x0
	movz x1, #21656, lsl #0
	add x1, x28, x1
	movz x10, #32, lsl #0
21:
	ldr q0, [x0, #0]
	ldr q1, [x0, #16]
	uzp1 v2.8h, v0.8h, v1.8h
	str q2, [x1, #0]
	add x0, x0, #32
	add x1, x1, #16
	sub x10, x10, #1
	cbnz x10, 21b
	movz x0, #21656, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem16_ntt}
	add x0, x26, #704
	movz x1, #352, lsl #0
	movz x2, #11, lsl #0
	movz x3, #26776, lsl #0
	add x3, x28, x3
	bl {vg_mlkem1024_decode_decompress}
	movz x0, #26776, lsl #0
	add x0, x28, x0
	movz x1, #22680, lsl #0
	add x1, x28, x1
	movz x10, #32, lsl #0
22:
	ldr q0, [x0, #0]
	ldr q1, [x0, #16]
	uzp1 v2.8h, v0.8h, v1.8h
	str q2, [x1, #0]
	add x0, x0, #32
	add x1, x1, #16
	sub x10, x10, #1
	cbnz x10, 22b
	movz x0, #22680, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem16_ntt}
	add x0, x26, #1056
	movz x1, #352, lsl #0
	movz x2, #11, lsl #0
	movz x3, #26776, lsl #0
	add x3, x28, x3
	bl {vg_mlkem1024_decode_decompress}
	movz x0, #26776, lsl #0
	add x0, x28, x0
	movz x1, #23704, lsl #0
	add x1, x28, x1
	movz x10, #32, lsl #0
23:
	ldr q0, [x0, #0]
	ldr q1, [x0, #16]
	uzp1 v2.8h, v0.8h, v1.8h
	str q2, [x1, #0]
	add x0, x0, #32
	add x1, x1, #16
	sub x10, x10, #1
	cbnz x10, 23b
	movz x0, #23704, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem16_ntt}
	add x0, x25, #0
	movz x1, #4248, lsl #0
	add x1, x28, x1
	movz x9, #256, lsl #0
	movk x9, #65282, lsl #16
	movk x9, #1027, lsl #32
	movk x9, #65285, lsl #48
	dup v16.2d, x9
	movz x9, #1798, lsl #0
	movk x9, #65288, lsl #16
	movk x9, #2569, lsl #32
	movk x9, #65291, lsl #48
	mov v16.d[1], x9
	movz x9, #4095, lsl #0
	dup v17.4s, w9
	movz x9, #3329, lsl #0
	dup v18.4s, w9
	movz x11, #32, lsl #0
24:
	ldr x9, [x0, #0]
	ldr w10, [x0, #8]
	dup v0.2d, x9
	mov v0.d[1], x10
	tbl v1.16b, {v0.16b}, v16.16b
	and v2.16b, v1.16b, v17.16b
	ushr v3.4s, v1.4s, #12
	sub v4.4s, v2.4s, v18.4s
	umin v2.4s, v2.4s, v4.4s
	sub v4.4s, v3.4s, v18.4s
	umin v3.4s, v3.4s, v4.4s
	zip1 v0.4s, v2.4s, v3.4s
	zip2 v1.4s, v2.4s, v3.4s
	uzp1 v0.8h, v0.8h, v1.8h
	str q0, [x1, #0]
	add x0, x0, #12
	add x1, x1, #16
	sub x11, x11, #1
	cbnz x11, 24b
	add x0, x25, #384
	movz x1, #5272, lsl #0
	add x1, x28, x1
	movz x9, #256, lsl #0
	movk x9, #65282, lsl #16
	movk x9, #1027, lsl #32
	movk x9, #65285, lsl #48
	dup v16.2d, x9
	movz x9, #1798, lsl #0
	movk x9, #65288, lsl #16
	movk x9, #2569, lsl #32
	movk x9, #65291, lsl #48
	mov v16.d[1], x9
	movz x9, #4095, lsl #0
	dup v17.4s, w9
	movz x9, #3329, lsl #0
	dup v18.4s, w9
	movz x11, #32, lsl #0
25:
	ldr x9, [x0, #0]
	ldr w10, [x0, #8]
	dup v0.2d, x9
	mov v0.d[1], x10
	tbl v1.16b, {v0.16b}, v16.16b
	and v2.16b, v1.16b, v17.16b
	ushr v3.4s, v1.4s, #12
	sub v4.4s, v2.4s, v18.4s
	umin v2.4s, v2.4s, v4.4s
	sub v4.4s, v3.4s, v18.4s
	umin v3.4s, v3.4s, v4.4s
	zip1 v0.4s, v2.4s, v3.4s
	zip2 v1.4s, v2.4s, v3.4s
	uzp1 v0.8h, v0.8h, v1.8h
	str q0, [x1, #0]
	add x0, x0, #12
	add x1, x1, #16
	sub x11, x11, #1
	cbnz x11, 25b
	add x0, x25, #768
	movz x1, #6296, lsl #0
	add x1, x28, x1
	movz x9, #256, lsl #0
	movk x9, #65282, lsl #16
	movk x9, #1027, lsl #32
	movk x9, #65285, lsl #48
	dup v16.2d, x9
	movz x9, #1798, lsl #0
	movk x9, #65288, lsl #16
	movk x9, #2569, lsl #32
	movk x9, #65291, lsl #48
	mov v16.d[1], x9
	movz x9, #4095, lsl #0
	dup v17.4s, w9
	movz x9, #3329, lsl #0
	dup v18.4s, w9
	movz x11, #32, lsl #0
26:
	ldr x9, [x0, #0]
	ldr w10, [x0, #8]
	dup v0.2d, x9
	mov v0.d[1], x10
	tbl v1.16b, {v0.16b}, v16.16b
	and v2.16b, v1.16b, v17.16b
	ushr v3.4s, v1.4s, #12
	sub v4.4s, v2.4s, v18.4s
	umin v2.4s, v2.4s, v4.4s
	sub v4.4s, v3.4s, v18.4s
	umin v3.4s, v3.4s, v4.4s
	zip1 v0.4s, v2.4s, v3.4s
	zip2 v1.4s, v2.4s, v3.4s
	uzp1 v0.8h, v0.8h, v1.8h
	str q0, [x1, #0]
	add x0, x0, #12
	add x1, x1, #16
	sub x11, x11, #1
	cbnz x11, 26b
	add x0, x25, #1152
	movz x1, #7320, lsl #0
	add x1, x28, x1
	movz x9, #256, lsl #0
	movk x9, #65282, lsl #16
	movk x9, #1027, lsl #32
	movk x9, #65285, lsl #48
	dup v16.2d, x9
	movz x9, #1798, lsl #0
	movk x9, #65288, lsl #16
	movk x9, #2569, lsl #32
	movk x9, #65291, lsl #48
	mov v16.d[1], x9
	movz x9, #4095, lsl #0
	dup v17.4s, w9
	movz x9, #3329, lsl #0
	dup v18.4s, w9
	movz x11, #32, lsl #0
27:
	ldr x9, [x0, #0]
	ldr w10, [x0, #8]
	dup v0.2d, x9
	mov v0.d[1], x10
	tbl v1.16b, {v0.16b}, v16.16b
	and v2.16b, v1.16b, v17.16b
	ushr v3.4s, v1.4s, #12
	sub v4.4s, v2.4s, v18.4s
	umin v2.4s, v2.4s, v4.4s
	sub v4.4s, v3.4s, v18.4s
	umin v3.4s, v3.4s, v4.4s
	zip1 v0.4s, v2.4s, v3.4s
	zip2 v1.4s, v2.4s, v3.4s
	uzp1 v0.8h, v0.8h, v1.8h
	str q0, [x1, #0]
	add x0, x0, #12
	add x1, x1, #16
	sub x11, x11, #1
	cbnz x11, 27b
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x9, #3329, lsl #0
	movz x10, #55259, lsl #0
	movk x10, #9, lsl #16
	movk x10, #0, lsl #32
	movk x10, #0, lsl #48
	dup v16.4s, w9
	dup v17.4s, w10
	adrp x3, {VG_MLKEM_GAMMA}
	add x3, x3, {VG_MLKEM_GAMMA}
	movz x11, #16, lsl #0
	movz x12, #0, lsl #0
28:
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movz x1, #4248, lsl #0
	add x1, x28, x1
	movz x2, #20632, lsl #0
	add x2, x28, x2
	add x1, x1, x12
	add x2, x2, x12
	ldr q0, [x1, #0]
	ldr q1, [x1, #16]
	ldr q4, [x2, #0]
	ldr q5, [x2, #16]
	uzp1 v6.8h, v0.8h, v1.8h
	uzp2 v7.8h, v0.8h, v1.8h
	uzp1 v19.8h, v4.8h, v5.8h
	uzp2 v20.8h, v4.8h, v5.8h
	umlal v21.4s, v6.4h, v19.4h
	umlal2 v25.4s, v6.8h, v19.8h
	umlal v22.4s, v7.4h, v20.4h
	umlal2 v26.4s, v7.8h, v20.8h
	umlal v23.4s, v6.4h, v20.4h
	umlal2 v27.4s, v6.8h, v20.8h
	umlal v23.4s, v7.4h, v19.4h
	umlal2 v27.4s, v7.8h, v19.8h
	movz x1, #5272, lsl #0
	add x1, x28, x1
	movz x2, #21656, lsl #0
	add x2, x28, x2
	add x1, x1, x12
	add x2, x2, x12
	ldr q0, [x1, #0]
	ldr q1, [x1, #16]
	ldr q4, [x2, #0]
	ldr q5, [x2, #16]
	uzp1 v6.8h, v0.8h, v1.8h
	uzp2 v7.8h, v0.8h, v1.8h
	uzp1 v19.8h, v4.8h, v5.8h
	uzp2 v20.8h, v4.8h, v5.8h
	umlal v21.4s, v6.4h, v19.4h
	umlal2 v25.4s, v6.8h, v19.8h
	umlal v22.4s, v7.4h, v20.4h
	umlal2 v26.4s, v7.8h, v20.8h
	umlal v23.4s, v6.4h, v20.4h
	umlal2 v27.4s, v6.8h, v20.8h
	umlal v23.4s, v7.4h, v19.4h
	umlal2 v27.4s, v7.8h, v19.8h
	movz x1, #6296, lsl #0
	add x1, x28, x1
	movz x2, #22680, lsl #0
	add x2, x28, x2
	add x1, x1, x12
	add x2, x2, x12
	ldr q0, [x1, #0]
	ldr q1, [x1, #16]
	ldr q4, [x2, #0]
	ldr q5, [x2, #16]
	uzp1 v6.8h, v0.8h, v1.8h
	uzp2 v7.8h, v0.8h, v1.8h
	uzp1 v19.8h, v4.8h, v5.8h
	uzp2 v20.8h, v4.8h, v5.8h
	umlal v21.4s, v6.4h, v19.4h
	umlal2 v25.4s, v6.8h, v19.8h
	umlal v22.4s, v7.4h, v20.4h
	umlal2 v26.4s, v7.8h, v20.8h
	umlal v23.4s, v6.4h, v20.4h
	umlal2 v27.4s, v6.8h, v20.8h
	umlal v23.4s, v7.4h, v19.4h
	umlal2 v27.4s, v7.8h, v19.8h
	movz x1, #7320, lsl #0
	add x1, x28, x1
	movz x2, #23704, lsl #0
	add x2, x28, x2
	add x1, x1, x12
	add x2, x2, x12
	ldr q0, [x1, #0]
	ldr q1, [x1, #16]
	ldr q4, [x2, #0]
	ldr q5, [x2, #16]
	uzp1 v6.8h, v0.8h, v1.8h
	uzp2 v7.8h, v0.8h, v1.8h
	uzp1 v19.8h, v4.8h, v5.8h
	uzp2 v20.8h, v4.8h, v5.8h
	umlal v21.4s, v6.4h, v19.4h
	umlal2 v25.4s, v6.8h, v19.8h
	umlal v22.4s, v7.4h, v20.4h
	umlal2 v26.4s, v7.8h, v20.8h
	umlal v23.4s, v6.4h, v20.4h
	umlal2 v27.4s, v6.8h, v20.8h
	umlal v23.4s, v7.4h, v19.4h
	umlal2 v27.4s, v7.8h, v19.8h
	ldr q18, [x3, #0]
	ldr q28, [x3, #16]
	sqdmulh v24.4s, v22.4s, v17.4s
	mls v22.4s, v24.4s, v16.4s
	mla v21.4s, v22.4s, v18.4s
	sqdmulh v24.4s, v21.4s, v17.4s
	mls v21.4s, v24.4s, v16.4s
	sub v24.4s, v21.4s, v16.4s
	umin v21.4s, v21.4s, v24.4s
	sqdmulh v24.4s, v23.4s, v17.4s
	mls v23.4s, v24.4s, v16.4s
	sub v24.4s, v23.4s, v16.4s
	umin v23.4s, v23.4s, v24.4s
	sqdmulh v24.4s, v26.4s, v17.4s
	mls v26.4s, v24.4s, v16.4s
	mla v25.4s, v26.4s, v28.4s
	sqdmulh v24.4s, v25.4s, v17.4s
	mls v25.4s, v24.4s, v16.4s
	sub v24.4s, v25.4s, v16.4s
	umin v25.4s, v25.4s, v24.4s
	sqdmulh v24.4s, v27.4s, v17.4s
	mls v27.4s, v24.4s, v16.4s
	sub v24.4s, v27.4s, v16.4s
	umin v27.4s, v27.4s, v24.4s
	uzp1 v0.8h, v21.8h, v25.8h
	uzp1 v1.8h, v23.8h, v27.8h
	zip1 v2.8h, v0.8h, v1.8h
	zip2 v3.8h, v0.8h, v1.8h
	str q2, [x0, #0]
	str q3, [x0, #16]
	add x0, x0, #32
	add x3, x3, #32
	add x12, x12, #32
	sub x11, x11, #1
	cbnz x11, 28b
	movz x0, #25752, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem16_inv_ntt}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #26776, lsl #0
	add x1, x28, x1
	movz x10, #32, lsl #0
	movi v29.2d, #0
29:
	ldr q0, [x0, #0]
	zip1 v1.8h, v0.8h, v29.8h
	zip2 v2.8h, v0.8h, v29.8h
	str q1, [x1, #0]
	str q2, [x1, #16]
	add x0, x0, #16
	add x1, x1, #32
	sub x10, x10, #1
	cbnz x10, 29b
	add x0, x26, #1408
	movz x1, #160, lsl #0
	movz x2, #5, lsl #0
	movz x3, #24728, lsl #0
	add x3, x28, x3
	bl {vg_mlkem1024_decode_decompress}
	movz x0, #24728, lsl #0
	add x0, x28, x0
	movz x1, #26776, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_sub}
	movz x0, #24728, lsl #0
	add x0, x28, x0
	movz x1, #1, lsl #0
	add x2, x28, #912
	movz x3, #32, lsl #0
	bl {vg_mlkem_compress_encode}
	add x0, x28, #0
	movz x9, #0, lsl #0
	str x9, [x0, #0]
	str x9, [x0, #8]
	str x9, [x0, #16]
	str x9, [x0, #24]
	str x9, [x0, #32]
	str x9, [x0, #40]
	str x9, [x0, #48]
	str x9, [x0, #56]
	str x9, [x0, #64]
	str x9, [x0, #72]
	str x9, [x0, #80]
	str x9, [x0, #88]
	str x9, [x0, #96]
	str x9, [x0, #104]
	str x9, [x0, #112]
	str x9, [x0, #120]
	str x9, [x0, #128]
	str x9, [x0, #136]
	str x9, [x0, #144]
	str x9, [x0, #152]
	str x9, [x0, #160]
	str x9, [x0, #168]
	str x9, [x0, #176]
	str x9, [x0, #184]
	str x9, [x0, #192]
	str x30, [x28, #800]
	add x2, x28, #912
	ldr x9, [x2, #0]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	add x2, x28, #920
	ldr x9, [x2, #0]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	add x2, x28, #928
	ldr x9, [x2, #0]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	add x2, x28, #936
	ldr x9, [x2, #0]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	add x2, x25, #3104
	ldr x9, [x2, #0]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	add x2, x25, #3112
	ldr x9, [x2, #0]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	add x2, x25, #3120
	ldr x9, [x2, #0]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	add x2, x25, #3128
	ldr x9, [x2, #0]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldrb w9, [x28, #64]
	movz x10, #6, lsl #0
	eor x9, x9, x10
	strb w9, [x28, #64]
	ldrb w9, [x28, #71]
	movz x10, #128, lsl #0
	eor x9, x9, x10
	strb w9, [x28, #71]
	add x0, x28, #0
	add x1, x28, #200
	bl {vg_keccak_f1600}
	ldr x9, [x28, #0]
	add x2, x28, #984
	str x9, [x2, #0]
	ldr x9, [x28, #8]
	add x2, x28, #992
	str x9, [x2, #0]
	ldr x9, [x28, #16]
	add x2, x28, #1000
	str x9, [x2, #0]
	ldr x9, [x28, #24]
	add x2, x28, #1008
	str x9, [x2, #0]
	ldr x9, [x28, #32]
	add x2, x28, #944
	str x9, [x2, #0]
	ldr x9, [x28, #40]
	add x2, x28, #952
	str x9, [x2, #0]
	ldr x9, [x28, #48]
	add x2, x28, #960
	str x9, [x2, #0]
	ldr x9, [x28, #56]
	add x2, x28, #968
	str x9, [x2, #0]
	ldr x30, [x28, #800]
	ldr x9, [x25, #3072]
	str x9, [x28, #840]
	ldr x9, [x25, #3080]
	str x9, [x28, #848]
	ldr x9, [x25, #3088]
	str x9, [x28, #856]
	ldr x9, [x25, #3096]
	str x9, [x28, #864]
	add x0, x28, #0
	movz x9, #0, lsl #0
	str x9, [x0, #0]
	str x9, [x0, #8]
	str x9, [x0, #16]
	str x9, [x0, #24]
	str x9, [x0, #32]
	str x9, [x0, #40]
	str x9, [x0, #48]
	str x9, [x0, #56]
	str x9, [x0, #64]
	str x9, [x0, #72]
	str x9, [x0, #80]
	str x9, [x0, #88]
	str x9, [x0, #96]
	str x9, [x0, #104]
	str x9, [x0, #112]
	str x9, [x0, #120]
	str x9, [x0, #128]
	str x9, [x0, #136]
	str x9, [x0, #144]
	str x9, [x0, #152]
	str x9, [x0, #160]
	str x9, [x0, #168]
	str x9, [x0, #176]
	str x9, [x0, #184]
	str x9, [x0, #192]
	ldr x9, [x25, #3136]
	str x9, [x28, #28792]
	ldr x9, [x25, #3144]
	str x9, [x28, #28800]
	ldr x9, [x25, #3152]
	str x9, [x28, #28808]
	ldr x9, [x25, #3160]
	str x9, [x28, #28816]
	ldr x9, [x26, #0]
	str x9, [x28, #28824]
	ldr x9, [x26, #8]
	str x9, [x28, #28832]
	ldr x9, [x26, #16]
	str x9, [x28, #28840]
	ldr x9, [x26, #24]
	str x9, [x28, #28848]
	ldr x9, [x26, #32]
	str x9, [x28, #28856]
	ldr x9, [x26, #40]
	str x9, [x28, #28864]
	ldr x9, [x26, #48]
	str x9, [x28, #28872]
	ldr x9, [x26, #56]
	str x9, [x28, #28880]
	ldr x9, [x26, #64]
	str x9, [x28, #28888]
	ldr x9, [x26, #72]
	str x9, [x28, #28896]
	ldr x9, [x26, #80]
	str x9, [x28, #28904]
	ldr x9, [x26, #88]
	str x9, [x28, #28912]
	ldr x9, [x26, #96]
	str x9, [x28, #28920]
	ldr x9, [x26, #104]
	str x9, [x28, #28928]
	ldr x9, [x26, #112]
	str x9, [x28, #28936]
	ldr x9, [x26, #120]
	str x9, [x28, #28944]
	ldr x9, [x26, #128]
	str x9, [x28, #28952]
	ldr x9, [x26, #136]
	str x9, [x28, #28960]
	ldr x9, [x26, #144]
	str x9, [x28, #28968]
	ldr x9, [x26, #152]
	str x9, [x28, #28976]
	ldr x9, [x26, #160]
	str x9, [x28, #28984]
	ldr x9, [x26, #168]
	str x9, [x28, #28992]
	ldr x9, [x26, #176]
	str x9, [x28, #29000]
	ldr x9, [x26, #184]
	str x9, [x28, #29008]
	ldr x9, [x26, #192]
	str x9, [x28, #29016]
	ldr x9, [x26, #200]
	str x9, [x28, #29024]
	ldr x9, [x26, #208]
	str x9, [x28, #29032]
	ldr x9, [x26, #216]
	str x9, [x28, #29040]
	ldr x9, [x26, #224]
	str x9, [x28, #29048]
	ldr x9, [x26, #232]
	str x9, [x28, #29056]
	ldr x9, [x26, #240]
	str x9, [x28, #29064]
	ldr x9, [x26, #248]
	str x9, [x28, #29072]
	ldr x9, [x26, #256]
	str x9, [x28, #29080]
	ldr x9, [x26, #264]
	str x9, [x28, #29088]
	ldr x9, [x26, #272]
	str x9, [x28, #29096]
	ldr x9, [x26, #280]
	str x9, [x28, #29104]
	ldr x9, [x26, #288]
	str x9, [x28, #29112]
	ldr x9, [x26, #296]
	str x9, [x28, #29120]
	ldr x9, [x26, #304]
	str x9, [x28, #29128]
	ldr x9, [x26, #312]
	str x9, [x28, #29136]
	ldr x9, [x26, #320]
	str x9, [x28, #29144]
	ldr x9, [x26, #328]
	str x9, [x28, #29152]
	ldr x9, [x26, #336]
	str x9, [x28, #29160]
	ldr x9, [x26, #344]
	str x9, [x28, #29168]
	ldr x9, [x26, #352]
	str x9, [x28, #29176]
	ldr x9, [x26, #360]
	str x9, [x28, #29184]
	ldr x9, [x26, #368]
	str x9, [x28, #29192]
	ldr x9, [x26, #376]
	str x9, [x28, #29200]
	ldr x9, [x26, #384]
	str x9, [x28, #29208]
	ldr x9, [x26, #392]
	str x9, [x28, #29216]
	ldr x9, [x26, #400]
	str x9, [x28, #29224]
	ldr x9, [x26, #408]
	str x9, [x28, #29232]
	ldr x9, [x26, #416]
	str x9, [x28, #29240]
	ldr x9, [x26, #424]
	str x9, [x28, #29248]
	ldr x9, [x26, #432]
	str x9, [x28, #29256]
	ldr x9, [x26, #440]
	str x9, [x28, #29264]
	ldr x9, [x26, #448]
	str x9, [x28, #29272]
	ldr x9, [x26, #456]
	str x9, [x28, #29280]
	ldr x9, [x26, #464]
	str x9, [x28, #29288]
	ldr x9, [x26, #472]
	str x9, [x28, #29296]
	ldr x9, [x26, #480]
	str x9, [x28, #29304]
	ldr x9, [x26, #488]
	str x9, [x28, #29312]
	ldr x9, [x26, #496]
	str x9, [x28, #29320]
	ldr x9, [x26, #504]
	str x9, [x28, #29328]
	ldr x9, [x26, #512]
	str x9, [x28, #29336]
	ldr x9, [x26, #520]
	str x9, [x28, #29344]
	ldr x9, [x26, #528]
	str x9, [x28, #29352]
	ldr x9, [x26, #536]
	str x9, [x28, #29360]
	ldr x9, [x26, #544]
	str x9, [x28, #29368]
	ldr x9, [x26, #552]
	str x9, [x28, #29376]
	ldr x9, [x26, #560]
	str x9, [x28, #29384]
	ldr x9, [x26, #568]
	str x9, [x28, #29392]
	ldr x9, [x26, #576]
	str x9, [x28, #29400]
	ldr x9, [x26, #584]
	str x9, [x28, #29408]
	ldr x9, [x26, #592]
	str x9, [x28, #29416]
	ldr x9, [x26, #600]
	str x9, [x28, #29424]
	ldr x9, [x26, #608]
	str x9, [x28, #29432]
	ldr x9, [x26, #616]
	str x9, [x28, #29440]
	ldr x9, [x26, #624]
	str x9, [x28, #29448]
	ldr x9, [x26, #632]
	str x9, [x28, #29456]
	ldr x9, [x26, #640]
	str x9, [x28, #29464]
	ldr x9, [x26, #648]
	str x9, [x28, #29472]
	ldr x9, [x26, #656]
	str x9, [x28, #29480]
	ldr x9, [x26, #664]
	str x9, [x28, #29488]
	ldr x9, [x26, #672]
	str x9, [x28, #29496]
	ldr x9, [x26, #680]
	str x9, [x28, #29504]
	ldr x9, [x26, #688]
	str x9, [x28, #29512]
	ldr x9, [x26, #696]
	str x9, [x28, #29520]
	ldr x9, [x26, #704]
	str x9, [x28, #29528]
	ldr x9, [x26, #712]
	str x9, [x28, #29536]
	ldr x9, [x26, #720]
	str x9, [x28, #29544]
	ldr x9, [x26, #728]
	str x9, [x28, #29552]
	ldr x9, [x26, #736]
	str x9, [x28, #29560]
	ldr x9, [x26, #744]
	str x9, [x28, #29568]
	ldr x9, [x26, #752]
	str x9, [x28, #29576]
	ldr x9, [x26, #760]
	str x9, [x28, #29584]
	ldr x9, [x26, #768]
	str x9, [x28, #29592]
	ldr x9, [x26, #776]
	str x9, [x28, #29600]
	ldr x9, [x26, #784]
	str x9, [x28, #29608]
	ldr x9, [x26, #792]
	str x9, [x28, #29616]
	ldr x9, [x26, #800]
	str x9, [x28, #29624]
	ldr x9, [x26, #808]
	str x9, [x28, #29632]
	ldr x9, [x26, #816]
	str x9, [x28, #29640]
	ldr x9, [x26, #824]
	str x9, [x28, #29648]
	ldr x9, [x26, #832]
	str x9, [x28, #29656]
	ldr x9, [x26, #840]
	str x9, [x28, #29664]
	ldr x9, [x26, #848]
	str x9, [x28, #29672]
	ldr x9, [x26, #856]
	str x9, [x28, #29680]
	ldr x9, [x26, #864]
	str x9, [x28, #29688]
	ldr x9, [x26, #872]
	str x9, [x28, #29696]
	ldr x9, [x26, #880]
	str x9, [x28, #29704]
	ldr x9, [x26, #888]
	str x9, [x28, #29712]
	ldr x9, [x26, #896]
	str x9, [x28, #29720]
	ldr x9, [x26, #904]
	str x9, [x28, #29728]
	ldr x9, [x26, #912]
	str x9, [x28, #29736]
	ldr x9, [x26, #920]
	str x9, [x28, #29744]
	ldr x9, [x26, #928]
	str x9, [x28, #29752]
	ldr x9, [x26, #936]
	str x9, [x28, #29760]
	ldr x9, [x26, #944]
	str x9, [x28, #29768]
	ldr x9, [x26, #952]
	str x9, [x28, #29776]
	ldr x9, [x26, #960]
	str x9, [x28, #29784]
	ldr x9, [x26, #968]
	str x9, [x28, #29792]
	ldr x9, [x26, #976]
	str x9, [x28, #29800]
	ldr x9, [x26, #984]
	str x9, [x28, #29808]
	ldr x9, [x26, #992]
	str x9, [x28, #29816]
	ldr x9, [x26, #1000]
	str x9, [x28, #29824]
	ldr x9, [x26, #1008]
	str x9, [x28, #29832]
	ldr x9, [x26, #1016]
	str x9, [x28, #29840]
	ldr x9, [x26, #1024]
	str x9, [x28, #29848]
	ldr x9, [x26, #1032]
	str x9, [x28, #29856]
	ldr x9, [x26, #1040]
	str x9, [x28, #29864]
	ldr x9, [x26, #1048]
	str x9, [x28, #29872]
	ldr x9, [x26, #1056]
	str x9, [x28, #29880]
	ldr x9, [x26, #1064]
	str x9, [x28, #29888]
	ldr x9, [x26, #1072]
	str x9, [x28, #29896]
	ldr x9, [x26, #1080]
	str x9, [x28, #29904]
	ldr x9, [x26, #1088]
	str x9, [x28, #29912]
	ldr x9, [x26, #1096]
	str x9, [x28, #29920]
	ldr x9, [x26, #1104]
	str x9, [x28, #29928]
	ldr x9, [x26, #1112]
	str x9, [x28, #29936]
	ldr x9, [x26, #1120]
	str x9, [x28, #29944]
	ldr x9, [x26, #1128]
	str x9, [x28, #29952]
	ldr x9, [x26, #1136]
	str x9, [x28, #29960]
	ldr x9, [x26, #1144]
	str x9, [x28, #29968]
	ldr x9, [x26, #1152]
	str x9, [x28, #29976]
	ldr x9, [x26, #1160]
	str x9, [x28, #29984]
	ldr x9, [x26, #1168]
	str x9, [x28, #29992]
	ldr x9, [x26, #1176]
	str x9, [x28, #30000]
	ldr x9, [x26, #1184]
	str x9, [x28, #30008]
	ldr x9, [x26, #1192]
	str x9, [x28, #30016]
	ldr x9, [x26, #1200]
	str x9, [x28, #30024]
	ldr x9, [x26, #1208]
	str x9, [x28, #30032]
	ldr x9, [x26, #1216]
	str x9, [x28, #30040]
	ldr x9, [x26, #1224]
	str x9, [x28, #30048]
	ldr x9, [x26, #1232]
	str x9, [x28, #30056]
	ldr x9, [x26, #1240]
	str x9, [x28, #30064]
	ldr x9, [x26, #1248]
	str x9, [x28, #30072]
	ldr x9, [x26, #1256]
	str x9, [x28, #30080]
	ldr x9, [x26, #1264]
	str x9, [x28, #30088]
	ldr x9, [x26, #1272]
	str x9, [x28, #30096]
	ldr x9, [x26, #1280]
	str x9, [x28, #30104]
	ldr x9, [x26, #1288]
	str x9, [x28, #30112]
	ldr x9, [x26, #1296]
	str x9, [x28, #30120]
	ldr x9, [x26, #1304]
	str x9, [x28, #30128]
	ldr x9, [x26, #1312]
	str x9, [x28, #30136]
	ldr x9, [x26, #1320]
	str x9, [x28, #30144]
	ldr x9, [x26, #1328]
	str x9, [x28, #30152]
	ldr x9, [x26, #1336]
	str x9, [x28, #30160]
	ldr x9, [x26, #1344]
	str x9, [x28, #30168]
	ldr x9, [x26, #1352]
	str x9, [x28, #30176]
	ldr x9, [x26, #1360]
	str x9, [x28, #30184]
	ldr x9, [x26, #1368]
	str x9, [x28, #30192]
	ldr x9, [x26, #1376]
	str x9, [x28, #30200]
	ldr x9, [x26, #1384]
	str x9, [x28, #30208]
	ldr x9, [x26, #1392]
	str x9, [x28, #30216]
	ldr x9, [x26, #1400]
	str x9, [x28, #30224]
	ldr x9, [x26, #1408]
	str x9, [x28, #30232]
	ldr x9, [x26, #1416]
	str x9, [x28, #30240]
	ldr x9, [x26, #1424]
	str x9, [x28, #30248]
	ldr x9, [x26, #1432]
	str x9, [x28, #30256]
	ldr x9, [x26, #1440]
	str x9, [x28, #30264]
	ldr x9, [x26, #1448]
	str x9, [x28, #30272]
	ldr x9, [x26, #1456]
	str x9, [x28, #30280]
	ldr x9, [x26, #1464]
	str x9, [x28, #30288]
	ldr x9, [x26, #1472]
	str x9, [x28, #30296]
	ldr x9, [x26, #1480]
	str x9, [x28, #30304]
	ldr x9, [x26, #1488]
	str x9, [x28, #30312]
	ldr x9, [x26, #1496]
	str x9, [x28, #30320]
	ldr x9, [x26, #1504]
	str x9, [x28, #30328]
	ldr x9, [x26, #1512]
	str x9, [x28, #30336]
	ldr x9, [x26, #1520]
	str x9, [x28, #30344]
	ldr x9, [x26, #1528]
	str x9, [x28, #30352]
	ldr x9, [x26, #1536]
	str x9, [x28, #30360]
	ldr x9, [x26, #1544]
	str x9, [x28, #30368]
	ldr x9, [x26, #1552]
	str x9, [x28, #30376]
	ldr x9, [x26, #1560]
	str x9, [x28, #30384]
	add x2, x28, #1176
	str x19, [x2, #1800]
	str x20, [x2, #1808]
	str x21, [x2, #1816]
	str x22, [x2, #1824]
	str x23, [x2, #1832]
	str x30, [x2, #1840]
	add x19, x2, #0
	movi v0.2d, #0
	str q0, [x19, #0]
	str q0, [x19, #16]
	str q0, [x19, #32]
	str q0, [x19, #48]
	str q0, [x19, #64]
	str q0, [x19, #80]
	str q0, [x19, #96]
	str q0, [x19, #112]
	str q0, [x19, #128]
	str q0, [x19, #144]
	str q0, [x19, #160]
	str q0, [x19, #176]
	str q0, [x19, #192]
	str q0, [x19, #208]
	str q0, [x19, #224]
	str q0, [x19, #240]
	str q0, [x19, #256]
	str q0, [x19, #272]
	str q0, [x19, #288]
	str q0, [x19, #304]
	str q0, [x19, #320]
	str q0, [x19, #336]
	str q0, [x19, #352]
	str q0, [x19, #368]
	str q0, [x19, #384]
	ldr x6, [x28, #840]
	dup v0.2d, x6
	str q0, [x19, #0]
	ldr x6, [x28, #848]
	dup v0.2d, x6
	str q0, [x19, #16]
	ldr x6, [x28, #856]
	dup v0.2d, x6
	str q0, [x19, #32]
	ldr x6, [x28, #864]
	dup v0.2d, x6
	str q0, [x19, #48]
	movz x6, #0, lsl #0
	movk x6, #31, lsl #16
	movz x7, #1, lsl #0
	movk x7, #31, lsl #16
	dup v0.2d, x6
	mov v0.d[1], x7
	str q0, [x19, #64]
	movz x6, #32768, lsl #48
	dup v0.2d, x6
	str q0, [x19, #320]
	add x20, x19, #400
	add x21, x19, #904
	movz x22, #3, lsl #0
	ldr x9, [x28, #28792]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	ldr x9, [x28, #28800]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	ldr x9, [x28, #28808]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	ldr x9, [x28, #28816]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	ldr x9, [x28, #28824]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	ldr x9, [x28, #28832]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	ldr x9, [x28, #28840]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	ldr x9, [x28, #28848]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldr x9, [x28, #28856]
	ldr x10, [x28, #64]
	eor x9, x9, x10
	str x9, [x28, #64]
	ldr x9, [x28, #28864]
	ldr x10, [x28, #72]
	eor x9, x9, x10
	str x9, [x28, #72]
	ldr x9, [x28, #28872]
	ldr x10, [x28, #80]
	eor x9, x9, x10
	str x9, [x28, #80]
	ldr x9, [x28, #28880]
	ldr x10, [x28, #88]
	eor x9, x9, x10
	str x9, [x28, #88]
	ldr x9, [x28, #28888]
	ldr x10, [x28, #96]
	eor x9, x9, x10
	str x9, [x28, #96]
	ldr x9, [x28, #28896]
	ldr x10, [x28, #104]
	eor x9, x9, x10
	str x9, [x28, #104]
	ldr x9, [x28, #28904]
	ldr x10, [x28, #112]
	eor x9, x9, x10
	str x9, [x28, #112]
	ldr x9, [x28, #28912]
	ldr x10, [x28, #120]
	eor x9, x9, x10
	str x9, [x28, #120]
	ldr x9, [x28, #28920]
	ldr x10, [x28, #128]
	eor x9, x9, x10
	str x9, [x28, #128]
	add x2, x19, #1536
	str x30, [x2, #128]
	add x0, x19, #0
	add x1, x28, #0
	bl {vg_keccak_f1600_x3_sha3}
	ldr x30, [x19, #1664]
	ldr x6, [x19, #0]
	ldr x7, [x19, #8]
	str x6, [x20, #0]
	str x7, [x21, #0]
	ldr x6, [x19, #16]
	ldr x7, [x19, #24]
	str x6, [x20, #8]
	str x7, [x21, #8]
	ldr x6, [x19, #32]
	ldr x7, [x19, #40]
	str x6, [x20, #16]
	str x7, [x21, #16]
	ldr x6, [x19, #48]
	ldr x7, [x19, #56]
	str x6, [x20, #24]
	str x7, [x21, #24]
	ldr x6, [x19, #64]
	ldr x7, [x19, #72]
	str x6, [x20, #32]
	str x7, [x21, #32]
	ldr x6, [x19, #80]
	ldr x7, [x19, #88]
	str x6, [x20, #40]
	str x7, [x21, #40]
	ldr x6, [x19, #96]
	ldr x7, [x19, #104]
	str x6, [x20, #48]
	str x7, [x21, #48]
	ldr x6, [x19, #112]
	ldr x7, [x19, #120]
	str x6, [x20, #56]
	str x7, [x21, #56]
	ldr x6, [x19, #128]
	ldr x7, [x19, #136]
	str x6, [x20, #64]
	str x7, [x21, #64]
	ldr x6, [x19, #144]
	ldr x7, [x19, #152]
	str x6, [x20, #72]
	str x7, [x21, #72]
	ldr x6, [x19, #160]
	ldr x7, [x19, #168]
	str x6, [x20, #80]
	str x7, [x21, #80]
	ldr x6, [x19, #176]
	ldr x7, [x19, #184]
	str x6, [x20, #88]
	str x7, [x21, #88]
	ldr x6, [x19, #192]
	ldr x7, [x19, #200]
	str x6, [x20, #96]
	str x7, [x21, #96]
	ldr x6, [x19, #208]
	ldr x7, [x19, #216]
	str x6, [x20, #104]
	str x7, [x21, #104]
	ldr x6, [x19, #224]
	ldr x7, [x19, #232]
	str x6, [x20, #112]
	str x7, [x21, #112]
	ldr x6, [x19, #240]
	ldr x7, [x19, #248]
	str x6, [x20, #120]
	str x7, [x21, #120]
	ldr x6, [x19, #256]
	ldr x7, [x19, #264]
	str x6, [x20, #128]
	str x7, [x21, #128]
	ldr x6, [x19, #272]
	ldr x7, [x19, #280]
	str x6, [x20, #136]
	str x7, [x21, #136]
	ldr x6, [x19, #288]
	ldr x7, [x19, #296]
	str x6, [x20, #144]
	str x7, [x21, #144]
	ldr x6, [x19, #304]
	ldr x7, [x19, #312]
	str x6, [x20, #152]
	str x7, [x21, #152]
	ldr x6, [x19, #320]
	ldr x7, [x19, #328]
	str x6, [x20, #160]
	str x7, [x21, #160]
	add x20, x20, #168
	add x21, x21, #168
	ldr x9, [x28, #28928]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	ldr x9, [x28, #28936]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	ldr x9, [x28, #28944]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	ldr x9, [x28, #28952]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	ldr x9, [x28, #28960]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	ldr x9, [x28, #28968]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	ldr x9, [x28, #28976]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	ldr x9, [x28, #28984]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldr x9, [x28, #28992]
	ldr x10, [x28, #64]
	eor x9, x9, x10
	str x9, [x28, #64]
	ldr x9, [x28, #29000]
	ldr x10, [x28, #72]
	eor x9, x9, x10
	str x9, [x28, #72]
	ldr x9, [x28, #29008]
	ldr x10, [x28, #80]
	eor x9, x9, x10
	str x9, [x28, #80]
	ldr x9, [x28, #29016]
	ldr x10, [x28, #88]
	eor x9, x9, x10
	str x9, [x28, #88]
	ldr x9, [x28, #29024]
	ldr x10, [x28, #96]
	eor x9, x9, x10
	str x9, [x28, #96]
	ldr x9, [x28, #29032]
	ldr x10, [x28, #104]
	eor x9, x9, x10
	str x9, [x28, #104]
	ldr x9, [x28, #29040]
	ldr x10, [x28, #112]
	eor x9, x9, x10
	str x9, [x28, #112]
	ldr x9, [x28, #29048]
	ldr x10, [x28, #120]
	eor x9, x9, x10
	str x9, [x28, #120]
	ldr x9, [x28, #29056]
	ldr x10, [x28, #128]
	eor x9, x9, x10
	str x9, [x28, #128]
	add x2, x19, #1536
	str x30, [x2, #128]
	add x0, x19, #0
	add x1, x28, #0
	bl {vg_keccak_f1600_x3_sha3}
	ldr x30, [x19, #1664]
	ldr x6, [x19, #0]
	ldr x7, [x19, #8]
	str x6, [x20, #0]
	str x7, [x21, #0]
	ldr x6, [x19, #16]
	ldr x7, [x19, #24]
	str x6, [x20, #8]
	str x7, [x21, #8]
	ldr x6, [x19, #32]
	ldr x7, [x19, #40]
	str x6, [x20, #16]
	str x7, [x21, #16]
	ldr x6, [x19, #48]
	ldr x7, [x19, #56]
	str x6, [x20, #24]
	str x7, [x21, #24]
	ldr x6, [x19, #64]
	ldr x7, [x19, #72]
	str x6, [x20, #32]
	str x7, [x21, #32]
	ldr x6, [x19, #80]
	ldr x7, [x19, #88]
	str x6, [x20, #40]
	str x7, [x21, #40]
	ldr x6, [x19, #96]
	ldr x7, [x19, #104]
	str x6, [x20, #48]
	str x7, [x21, #48]
	ldr x6, [x19, #112]
	ldr x7, [x19, #120]
	str x6, [x20, #56]
	str x7, [x21, #56]
	ldr x6, [x19, #128]
	ldr x7, [x19, #136]
	str x6, [x20, #64]
	str x7, [x21, #64]
	ldr x6, [x19, #144]
	ldr x7, [x19, #152]
	str x6, [x20, #72]
	str x7, [x21, #72]
	ldr x6, [x19, #160]
	ldr x7, [x19, #168]
	str x6, [x20, #80]
	str x7, [x21, #80]
	ldr x6, [x19, #176]
	ldr x7, [x19, #184]
	str x6, [x20, #88]
	str x7, [x21, #88]
	ldr x6, [x19, #192]
	ldr x7, [x19, #200]
	str x6, [x20, #96]
	str x7, [x21, #96]
	ldr x6, [x19, #208]
	ldr x7, [x19, #216]
	str x6, [x20, #104]
	str x7, [x21, #104]
	ldr x6, [x19, #224]
	ldr x7, [x19, #232]
	str x6, [x20, #112]
	str x7, [x21, #112]
	ldr x6, [x19, #240]
	ldr x7, [x19, #248]
	str x6, [x20, #120]
	str x7, [x21, #120]
	ldr x6, [x19, #256]
	ldr x7, [x19, #264]
	str x6, [x20, #128]
	str x7, [x21, #128]
	ldr x6, [x19, #272]
	ldr x7, [x19, #280]
	str x6, [x20, #136]
	str x7, [x21, #136]
	ldr x6, [x19, #288]
	ldr x7, [x19, #296]
	str x6, [x20, #144]
	str x7, [x21, #144]
	ldr x6, [x19, #304]
	ldr x7, [x19, #312]
	str x6, [x20, #152]
	str x7, [x21, #152]
	ldr x6, [x19, #320]
	ldr x7, [x19, #328]
	str x6, [x20, #160]
	str x7, [x21, #160]
	add x20, x20, #168
	add x21, x21, #168
	ldr x9, [x28, #29064]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	ldr x9, [x28, #29072]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	ldr x9, [x28, #29080]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	ldr x9, [x28, #29088]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	ldr x9, [x28, #29096]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	ldr x9, [x28, #29104]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	ldr x9, [x28, #29112]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	ldr x9, [x28, #29120]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldr x9, [x28, #29128]
	ldr x10, [x28, #64]
	eor x9, x9, x10
	str x9, [x28, #64]
	ldr x9, [x28, #29136]
	ldr x10, [x28, #72]
	eor x9, x9, x10
	str x9, [x28, #72]
	ldr x9, [x28, #29144]
	ldr x10, [x28, #80]
	eor x9, x9, x10
	str x9, [x28, #80]
	ldr x9, [x28, #29152]
	ldr x10, [x28, #88]
	eor x9, x9, x10
	str x9, [x28, #88]
	ldr x9, [x28, #29160]
	ldr x10, [x28, #96]
	eor x9, x9, x10
	str x9, [x28, #96]
	ldr x9, [x28, #29168]
	ldr x10, [x28, #104]
	eor x9, x9, x10
	str x9, [x28, #104]
	ldr x9, [x28, #29176]
	ldr x10, [x28, #112]
	eor x9, x9, x10
	str x9, [x28, #112]
	ldr x9, [x28, #29184]
	ldr x10, [x28, #120]
	eor x9, x9, x10
	str x9, [x28, #120]
	ldr x9, [x28, #29192]
	ldr x10, [x28, #128]
	eor x9, x9, x10
	str x9, [x28, #128]
	add x2, x19, #1536
	str x30, [x2, #128]
	add x0, x19, #0
	add x1, x28, #0
	bl {vg_keccak_f1600_x3_sha3}
	ldr x30, [x19, #1664]
	ldr x6, [x19, #0]
	ldr x7, [x19, #8]
	str x6, [x20, #0]
	str x7, [x21, #0]
	ldr x6, [x19, #16]
	ldr x7, [x19, #24]
	str x6, [x20, #8]
	str x7, [x21, #8]
	ldr x6, [x19, #32]
	ldr x7, [x19, #40]
	str x6, [x20, #16]
	str x7, [x21, #16]
	ldr x6, [x19, #48]
	ldr x7, [x19, #56]
	str x6, [x20, #24]
	str x7, [x21, #24]
	ldr x6, [x19, #64]
	ldr x7, [x19, #72]
	str x6, [x20, #32]
	str x7, [x21, #32]
	ldr x6, [x19, #80]
	ldr x7, [x19, #88]
	str x6, [x20, #40]
	str x7, [x21, #40]
	ldr x6, [x19, #96]
	ldr x7, [x19, #104]
	str x6, [x20, #48]
	str x7, [x21, #48]
	ldr x6, [x19, #112]
	ldr x7, [x19, #120]
	str x6, [x20, #56]
	str x7, [x21, #56]
	ldr x6, [x19, #128]
	ldr x7, [x19, #136]
	str x6, [x20, #64]
	str x7, [x21, #64]
	ldr x6, [x19, #144]
	ldr x7, [x19, #152]
	str x6, [x20, #72]
	str x7, [x21, #72]
	ldr x6, [x19, #160]
	ldr x7, [x19, #168]
	str x6, [x20, #80]
	str x7, [x21, #80]
	ldr x6, [x19, #176]
	ldr x7, [x19, #184]
	str x6, [x20, #88]
	str x7, [x21, #88]
	ldr x6, [x19, #192]
	ldr x7, [x19, #200]
	str x6, [x20, #96]
	str x7, [x21, #96]
	ldr x6, [x19, #208]
	ldr x7, [x19, #216]
	str x6, [x20, #104]
	str x7, [x21, #104]
	ldr x6, [x19, #224]
	ldr x7, [x19, #232]
	str x6, [x20, #112]
	str x7, [x21, #112]
	ldr x6, [x19, #240]
	ldr x7, [x19, #248]
	str x6, [x20, #120]
	str x7, [x21, #120]
	ldr x6, [x19, #256]
	ldr x7, [x19, #264]
	str x6, [x20, #128]
	str x7, [x21, #128]
	ldr x6, [x19, #272]
	ldr x7, [x19, #280]
	str x6, [x20, #136]
	str x7, [x21, #136]
	ldr x6, [x19, #288]
	ldr x7, [x19, #296]
	str x6, [x20, #144]
	str x7, [x21, #144]
	ldr x6, [x19, #304]
	ldr x7, [x19, #312]
	str x6, [x20, #152]
	str x7, [x21, #152]
	ldr x6, [x19, #320]
	ldr x7, [x19, #328]
	str x6, [x20, #160]
	str x7, [x21, #160]
	add x20, x20, #168
	add x21, x21, #168
	movz x9, #256, lsl #0
	movk x9, #513, lsl #16
	movk x9, #1027, lsl #32
	movk x9, #1284, lsl #48
	dup v16.2d, x9
	movz x9, #1798, lsl #0
	movk x9, #2055, lsl #16
	movk x9, #2569, lsl #32
	movk x9, #2826, lsl #48
	mov v16.d[1], x9
	movz x9, #4095, lsl #0
	movk x9, #0, lsl #16
	movk x9, #4095, lsl #32
	movk x9, #0, lsl #48
	dup v17.2d, x9
	movz x9, #4095, lsl #0
	movk x9, #0, lsl #16
	movk x9, #4095, lsl #32
	movk x9, #0, lsl #48
	mov v17.d[1], x9
	movz x9, #257, lsl #0
	movk x9, #258, lsl #16
	movk x9, #260, lsl #32
	movk x9, #264, lsl #48
	dup v20.2d, x9
	movz x9, #272, lsl #0
	movk x9, #288, lsl #16
	movk x9, #320, lsl #32
	movk x9, #384, lsl #48
	mov v20.d[1], x9
	movz x9, #3329, lsl #0
	dup v19.8h, w9
	movi v21.2d, #0
	movz x9, #0, lsl #0
	str x9, [x19, #1408]
	adrp x16, {VG_MLKEM_REJ_SHUFFLE}
	add x16, x16, {VG_MLKEM_REJ_SHUFFLE}
	movz x21, #4248, lsl #0
	add x21, x28, x21
	movz x23, #5272, lsl #0
	add x23, x28, x23
	add x20, x19, #400
	add x1, x19, #1680
	movz x22, #1, lsl #0
210:
	add x2, x20, #0
	add x3, x21, #0
	movz x4, #256, lsl #0
	movz x5, #168, lsl #0
	movz x9, #3329, lsl #0
	movz x10, #15, lsl #0
211:
	sub x6, x4, #8
	lsr x6, x6, #63
	cbz x6, 212f
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 214f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 216f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 217f
216:
217:
	b 215f
214:
215:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 218f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 220f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 221f
220:
221:
	b 219f
218:
219:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 222f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 224f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 225f
224:
225:
	b 223f
222:
223:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 226f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 228f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 229f
228:
229:
	b 227f
226:
227:
	cbz x4, 230f
	b 231f
230:
	movz x5, #0, lsl #0
231:
	b 213f
212:
	ldr q0, [x2, #0]
	tbl v0.16b, {v0.16b}, v16.16b
	ushr v1.8h, v0.8h, #4
	bif v0.16b, v1.16b, v17.16b
	cmhi v1.8h, v19.8h, v0.8h
	and v1.16b, v1.16b, v20.16b
	addv h1, v1.8h
	umov w6, v1.s[0]
	movz x7, #255, lsl #0
	and x7, x6, x7
	lsl x7, x7, #4
	add x7, x16, x7
	ldr q2, [x7, #0]
	tbl v0.16b, {v0.16b}, v2.16b
	str q0, [x3, #0]
	lsr x6, x6, #8
	movz x7, #15, lsl #0
	and x6, x6, x7
	sub x4, x4, x6
	lsl x6, x6, #1
	add x3, x3, x6
	add x2, x2, #12
	sub x5, x5, #4
213:
	cbnz x5, 211b
	cbz x4, 232f
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	b 233f
232:
233:
	sub x0, x4, #1
	lsr x0, x0, #63
	str x3, [x1, #0]
	str x4, [x1, #8]
	and x22, x22, x0
	add x20, x20, #504
	add x21, x23, #0
	add x1, x1, #16
	sub x6, x1, x19
	sub x6, x6, #1712
	cbnz x6, 210b
	add x6, x22, #0
	cbz x6, 234f
	b 235f
234:
	movz x30, #1, lsl #0
236:
	add x20, x19, #400
	add x21, x19, #904
	add x1, x19, #768
	add x1, x1, #768
	str x30, [x1, #128]
	add x0, x19, #0
	bl {vg_keccak_f1600_x2_sha3}
	ldr x30, [x1, #128]
	ldr x6, [x19, #0]
	ldr x7, [x19, #8]
	str x6, [x20, #0]
	str x7, [x21, #0]
	ldr x6, [x19, #16]
	ldr x7, [x19, #24]
	str x6, [x20, #8]
	str x7, [x21, #8]
	ldr x6, [x19, #32]
	ldr x7, [x19, #40]
	str x6, [x20, #16]
	str x7, [x21, #16]
	ldr x6, [x19, #48]
	ldr x7, [x19, #56]
	str x6, [x20, #24]
	str x7, [x21, #24]
	ldr x6, [x19, #64]
	ldr x7, [x19, #72]
	str x6, [x20, #32]
	str x7, [x21, #32]
	ldr x6, [x19, #80]
	ldr x7, [x19, #88]
	str x6, [x20, #40]
	str x7, [x21, #40]
	ldr x6, [x19, #96]
	ldr x7, [x19, #104]
	str x6, [x20, #48]
	str x7, [x21, #48]
	ldr x6, [x19, #112]
	ldr x7, [x19, #120]
	str x6, [x20, #56]
	str x7, [x21, #56]
	ldr x6, [x19, #128]
	ldr x7, [x19, #136]
	str x6, [x20, #64]
	str x7, [x21, #64]
	ldr x6, [x19, #144]
	ldr x7, [x19, #152]
	str x6, [x20, #72]
	str x7, [x21, #72]
	ldr x6, [x19, #160]
	ldr x7, [x19, #168]
	str x6, [x20, #80]
	str x7, [x21, #80]
	ldr x6, [x19, #176]
	ldr x7, [x19, #184]
	str x6, [x20, #88]
	str x7, [x21, #88]
	ldr x6, [x19, #192]
	ldr x7, [x19, #200]
	str x6, [x20, #96]
	str x7, [x21, #96]
	ldr x6, [x19, #208]
	ldr x7, [x19, #216]
	str x6, [x20, #104]
	str x7, [x21, #104]
	ldr x6, [x19, #224]
	ldr x7, [x19, #232]
	str x6, [x20, #112]
	str x7, [x21, #112]
	ldr x6, [x19, #240]
	ldr x7, [x19, #248]
	str x6, [x20, #120]
	str x7, [x21, #120]
	ldr x6, [x19, #256]
	ldr x7, [x19, #264]
	str x6, [x20, #128]
	str x7, [x21, #128]
	ldr x6, [x19, #272]
	ldr x7, [x19, #280]
	str x6, [x20, #136]
	str x7, [x21, #136]
	ldr x6, [x19, #288]
	ldr x7, [x19, #296]
	str x6, [x20, #144]
	str x7, [x21, #144]
	ldr x6, [x19, #304]
	ldr x7, [x19, #312]
	str x6, [x20, #152]
	str x7, [x21, #152]
	ldr x6, [x19, #320]
	ldr x7, [x19, #328]
	str x6, [x20, #160]
	str x7, [x21, #160]
	movz x9, #256, lsl #0
	movk x9, #513, lsl #16
	movk x9, #1027, lsl #32
	movk x9, #1284, lsl #48
	dup v16.2d, x9
	movz x9, #1798, lsl #0
	movk x9, #2055, lsl #16
	movk x9, #2569, lsl #32
	movk x9, #2826, lsl #48
	mov v16.d[1], x9
	movz x9, #4095, lsl #0
	movk x9, #0, lsl #16
	movk x9, #4095, lsl #32
	movk x9, #0, lsl #48
	dup v17.2d, x9
	movz x9, #4095, lsl #0
	movk x9, #0, lsl #16
	movk x9, #4095, lsl #32
	movk x9, #0, lsl #48
	mov v17.d[1], x9
	movz x9, #257, lsl #0
	movk x9, #258, lsl #16
	movk x9, #260, lsl #32
	movk x9, #264, lsl #48
	dup v20.2d, x9
	movz x9, #272, lsl #0
	movk x9, #288, lsl #16
	movk x9, #320, lsl #32
	movk x9, #384, lsl #48
	mov v20.d[1], x9
	movz x9, #3329, lsl #0
	dup v19.8h, w9
	movi v21.2d, #0
	movz x9, #0, lsl #0
	str x9, [x19, #1408]
	adrp x16, {VG_MLKEM_REJ_SHUFFLE}
	add x16, x16, {VG_MLKEM_REJ_SHUFFLE}
	add x20, x19, #400
	add x1, x19, #1680
	movz x22, #1, lsl #0
	movz x23, #2, lsl #0
237:
	ldr x3, [x1, #0]
	ldr x4, [x1, #8]
	cbz x4, 238f
	add x2, x20, #0
	movz x5, #56, lsl #0
	movz x9, #3329, lsl #0
	movz x10, #15, lsl #0
240:
	sub x6, x4, #8
	lsr x6, x6, #63
	cbz x6, 241f
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 243f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 245f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 246f
245:
246:
	b 244f
243:
244:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 247f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 249f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 250f
249:
250:
	b 248f
247:
248:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 251f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 253f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 254f
253:
254:
	b 252f
251:
252:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 255f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 257f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 258f
257:
258:
	b 256f
255:
256:
	cbz x4, 259f
	b 260f
259:
	movz x5, #0, lsl #0
260:
	b 242f
241:
	ldr q0, [x2, #0]
	tbl v0.16b, {v0.16b}, v16.16b
	ushr v1.8h, v0.8h, #4
	bif v0.16b, v1.16b, v17.16b
	cmhi v1.8h, v19.8h, v0.8h
	and v1.16b, v1.16b, v20.16b
	addv h1, v1.8h
	umov w6, v1.s[0]
	movz x7, #255, lsl #0
	and x7, x6, x7
	lsl x7, x7, #4
	add x7, x16, x7
	ldr q2, [x7, #0]
	tbl v0.16b, {v0.16b}, v2.16b
	str q0, [x3, #0]
	lsr x6, x6, #8
	movz x7, #15, lsl #0
	and x6, x6, x7
	sub x4, x4, x6
	lsl x6, x6, #1
	add x3, x3, x6
	add x2, x2, #12
	sub x5, x5, #4
242:
	cbnz x5, 240b
	cbz x4, 261f
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	b 262f
261:
262:
	sub x0, x4, #1
	lsr x0, x0, #63
	str x3, [x1, #0]
	str x4, [x1, #8]
	b 239f
238:
	movz x0, #1, lsl #0
239:
	and x22, x22, x0
	add x20, x20, #504
	add x1, x1, #16
	sub x23, x23, #1
	cbnz x23, 237b
	add x6, x22, #0
	sub x7, x6, x30
	lsr x7, x7, #63
	movz x30, #0, lsl #0
	cbnz x7, 236b
	and x24, x24, x6
	ldr x3, [x19, #1680]
	ldr x4, [x19, #1688]
	cbz x4, 263f
265:
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	add x3, x3, #2
	sub x4, x4, #1
	cbnz x4, 265b
	b 264f
263:
264:
	ldr x3, [x19, #1696]
	ldr x4, [x19, #1704]
	cbz x4, 266f
268:
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	add x3, x3, #2
	sub x4, x4, #1
	cbnz x4, 268b
	b 267f
266:
267:
235:
	ldr x30, [x19, #1840]
	ldr x23, [x19, #1832]
	ldr x22, [x19, #1824]
	ldr x21, [x19, #1816]
	ldr x20, [x19, #1808]
	ldr x19, [x19, #1800]
	add x2, x28, #1176
	str x19, [x2, #1800]
	str x20, [x2, #1808]
	str x21, [x2, #1816]
	str x22, [x2, #1824]
	str x23, [x2, #1832]
	str x30, [x2, #1840]
	add x19, x2, #0
	movi v0.2d, #0
	str q0, [x19, #0]
	str q0, [x19, #16]
	str q0, [x19, #32]
	str q0, [x19, #48]
	str q0, [x19, #64]
	str q0, [x19, #80]
	str q0, [x19, #96]
	str q0, [x19, #112]
	str q0, [x19, #128]
	str q0, [x19, #144]
	str q0, [x19, #160]
	str q0, [x19, #176]
	str q0, [x19, #192]
	str q0, [x19, #208]
	str q0, [x19, #224]
	str q0, [x19, #240]
	str q0, [x19, #256]
	str q0, [x19, #272]
	str q0, [x19, #288]
	str q0, [x19, #304]
	str q0, [x19, #320]
	str q0, [x19, #336]
	str q0, [x19, #352]
	str q0, [x19, #368]
	str q0, [x19, #384]
	ldr x6, [x28, #840]
	dup v0.2d, x6
	str q0, [x19, #0]
	ldr x6, [x28, #848]
	dup v0.2d, x6
	str q0, [x19, #16]
	ldr x6, [x28, #856]
	dup v0.2d, x6
	str q0, [x19, #32]
	ldr x6, [x28, #864]
	dup v0.2d, x6
	str q0, [x19, #48]
	movz x6, #2, lsl #0
	movk x6, #31, lsl #16
	movz x7, #3, lsl #0
	movk x7, #31, lsl #16
	dup v0.2d, x6
	mov v0.d[1], x7
	str q0, [x19, #64]
	movz x6, #32768, lsl #48
	dup v0.2d, x6
	str q0, [x19, #320]
	add x20, x19, #400
	add x21, x19, #904
	movz x22, #3, lsl #0
	ldr x9, [x28, #29200]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	ldr x9, [x28, #29208]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	ldr x9, [x28, #29216]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	ldr x9, [x28, #29224]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	ldr x9, [x28, #29232]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	ldr x9, [x28, #29240]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	ldr x9, [x28, #29248]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	ldr x9, [x28, #29256]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldr x9, [x28, #29264]
	ldr x10, [x28, #64]
	eor x9, x9, x10
	str x9, [x28, #64]
	ldr x9, [x28, #29272]
	ldr x10, [x28, #72]
	eor x9, x9, x10
	str x9, [x28, #72]
	ldr x9, [x28, #29280]
	ldr x10, [x28, #80]
	eor x9, x9, x10
	str x9, [x28, #80]
	ldr x9, [x28, #29288]
	ldr x10, [x28, #88]
	eor x9, x9, x10
	str x9, [x28, #88]
	ldr x9, [x28, #29296]
	ldr x10, [x28, #96]
	eor x9, x9, x10
	str x9, [x28, #96]
	ldr x9, [x28, #29304]
	ldr x10, [x28, #104]
	eor x9, x9, x10
	str x9, [x28, #104]
	ldr x9, [x28, #29312]
	ldr x10, [x28, #112]
	eor x9, x9, x10
	str x9, [x28, #112]
	ldr x9, [x28, #29320]
	ldr x10, [x28, #120]
	eor x9, x9, x10
	str x9, [x28, #120]
	ldr x9, [x28, #29328]
	ldr x10, [x28, #128]
	eor x9, x9, x10
	str x9, [x28, #128]
	add x2, x19, #1536
	str x30, [x2, #128]
	add x0, x19, #0
	add x1, x28, #0
	bl {vg_keccak_f1600_x3_sha3}
	ldr x30, [x19, #1664]
	ldr x6, [x19, #0]
	ldr x7, [x19, #8]
	str x6, [x20, #0]
	str x7, [x21, #0]
	ldr x6, [x19, #16]
	ldr x7, [x19, #24]
	str x6, [x20, #8]
	str x7, [x21, #8]
	ldr x6, [x19, #32]
	ldr x7, [x19, #40]
	str x6, [x20, #16]
	str x7, [x21, #16]
	ldr x6, [x19, #48]
	ldr x7, [x19, #56]
	str x6, [x20, #24]
	str x7, [x21, #24]
	ldr x6, [x19, #64]
	ldr x7, [x19, #72]
	str x6, [x20, #32]
	str x7, [x21, #32]
	ldr x6, [x19, #80]
	ldr x7, [x19, #88]
	str x6, [x20, #40]
	str x7, [x21, #40]
	ldr x6, [x19, #96]
	ldr x7, [x19, #104]
	str x6, [x20, #48]
	str x7, [x21, #48]
	ldr x6, [x19, #112]
	ldr x7, [x19, #120]
	str x6, [x20, #56]
	str x7, [x21, #56]
	ldr x6, [x19, #128]
	ldr x7, [x19, #136]
	str x6, [x20, #64]
	str x7, [x21, #64]
	ldr x6, [x19, #144]
	ldr x7, [x19, #152]
	str x6, [x20, #72]
	str x7, [x21, #72]
	ldr x6, [x19, #160]
	ldr x7, [x19, #168]
	str x6, [x20, #80]
	str x7, [x21, #80]
	ldr x6, [x19, #176]
	ldr x7, [x19, #184]
	str x6, [x20, #88]
	str x7, [x21, #88]
	ldr x6, [x19, #192]
	ldr x7, [x19, #200]
	str x6, [x20, #96]
	str x7, [x21, #96]
	ldr x6, [x19, #208]
	ldr x7, [x19, #216]
	str x6, [x20, #104]
	str x7, [x21, #104]
	ldr x6, [x19, #224]
	ldr x7, [x19, #232]
	str x6, [x20, #112]
	str x7, [x21, #112]
	ldr x6, [x19, #240]
	ldr x7, [x19, #248]
	str x6, [x20, #120]
	str x7, [x21, #120]
	ldr x6, [x19, #256]
	ldr x7, [x19, #264]
	str x6, [x20, #128]
	str x7, [x21, #128]
	ldr x6, [x19, #272]
	ldr x7, [x19, #280]
	str x6, [x20, #136]
	str x7, [x21, #136]
	ldr x6, [x19, #288]
	ldr x7, [x19, #296]
	str x6, [x20, #144]
	str x7, [x21, #144]
	ldr x6, [x19, #304]
	ldr x7, [x19, #312]
	str x6, [x20, #152]
	str x7, [x21, #152]
	ldr x6, [x19, #320]
	ldr x7, [x19, #328]
	str x6, [x20, #160]
	str x7, [x21, #160]
	add x20, x20, #168
	add x21, x21, #168
	ldr x9, [x28, #29336]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	ldr x9, [x28, #29344]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	ldr x9, [x28, #29352]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	ldr x9, [x28, #29360]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	ldr x9, [x28, #29368]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	ldr x9, [x28, #29376]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	ldr x9, [x28, #29384]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	ldr x9, [x28, #29392]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldr x9, [x28, #29400]
	ldr x10, [x28, #64]
	eor x9, x9, x10
	str x9, [x28, #64]
	ldr x9, [x28, #29408]
	ldr x10, [x28, #72]
	eor x9, x9, x10
	str x9, [x28, #72]
	ldr x9, [x28, #29416]
	ldr x10, [x28, #80]
	eor x9, x9, x10
	str x9, [x28, #80]
	ldr x9, [x28, #29424]
	ldr x10, [x28, #88]
	eor x9, x9, x10
	str x9, [x28, #88]
	ldr x9, [x28, #29432]
	ldr x10, [x28, #96]
	eor x9, x9, x10
	str x9, [x28, #96]
	ldr x9, [x28, #29440]
	ldr x10, [x28, #104]
	eor x9, x9, x10
	str x9, [x28, #104]
	ldr x9, [x28, #29448]
	ldr x10, [x28, #112]
	eor x9, x9, x10
	str x9, [x28, #112]
	ldr x9, [x28, #29456]
	ldr x10, [x28, #120]
	eor x9, x9, x10
	str x9, [x28, #120]
	ldr x9, [x28, #29464]
	ldr x10, [x28, #128]
	eor x9, x9, x10
	str x9, [x28, #128]
	add x2, x19, #1536
	str x30, [x2, #128]
	add x0, x19, #0
	add x1, x28, #0
	bl {vg_keccak_f1600_x3_sha3}
	ldr x30, [x19, #1664]
	ldr x6, [x19, #0]
	ldr x7, [x19, #8]
	str x6, [x20, #0]
	str x7, [x21, #0]
	ldr x6, [x19, #16]
	ldr x7, [x19, #24]
	str x6, [x20, #8]
	str x7, [x21, #8]
	ldr x6, [x19, #32]
	ldr x7, [x19, #40]
	str x6, [x20, #16]
	str x7, [x21, #16]
	ldr x6, [x19, #48]
	ldr x7, [x19, #56]
	str x6, [x20, #24]
	str x7, [x21, #24]
	ldr x6, [x19, #64]
	ldr x7, [x19, #72]
	str x6, [x20, #32]
	str x7, [x21, #32]
	ldr x6, [x19, #80]
	ldr x7, [x19, #88]
	str x6, [x20, #40]
	str x7, [x21, #40]
	ldr x6, [x19, #96]
	ldr x7, [x19, #104]
	str x6, [x20, #48]
	str x7, [x21, #48]
	ldr x6, [x19, #112]
	ldr x7, [x19, #120]
	str x6, [x20, #56]
	str x7, [x21, #56]
	ldr x6, [x19, #128]
	ldr x7, [x19, #136]
	str x6, [x20, #64]
	str x7, [x21, #64]
	ldr x6, [x19, #144]
	ldr x7, [x19, #152]
	str x6, [x20, #72]
	str x7, [x21, #72]
	ldr x6, [x19, #160]
	ldr x7, [x19, #168]
	str x6, [x20, #80]
	str x7, [x21, #80]
	ldr x6, [x19, #176]
	ldr x7, [x19, #184]
	str x6, [x20, #88]
	str x7, [x21, #88]
	ldr x6, [x19, #192]
	ldr x7, [x19, #200]
	str x6, [x20, #96]
	str x7, [x21, #96]
	ldr x6, [x19, #208]
	ldr x7, [x19, #216]
	str x6, [x20, #104]
	str x7, [x21, #104]
	ldr x6, [x19, #224]
	ldr x7, [x19, #232]
	str x6, [x20, #112]
	str x7, [x21, #112]
	ldr x6, [x19, #240]
	ldr x7, [x19, #248]
	str x6, [x20, #120]
	str x7, [x21, #120]
	ldr x6, [x19, #256]
	ldr x7, [x19, #264]
	str x6, [x20, #128]
	str x7, [x21, #128]
	ldr x6, [x19, #272]
	ldr x7, [x19, #280]
	str x6, [x20, #136]
	str x7, [x21, #136]
	ldr x6, [x19, #288]
	ldr x7, [x19, #296]
	str x6, [x20, #144]
	str x7, [x21, #144]
	ldr x6, [x19, #304]
	ldr x7, [x19, #312]
	str x6, [x20, #152]
	str x7, [x21, #152]
	ldr x6, [x19, #320]
	ldr x7, [x19, #328]
	str x6, [x20, #160]
	str x7, [x21, #160]
	add x20, x20, #168
	add x21, x21, #168
	ldr x9, [x28, #29472]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	ldr x9, [x28, #29480]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	ldr x9, [x28, #29488]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	ldr x9, [x28, #29496]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	ldr x9, [x28, #29504]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	ldr x9, [x28, #29512]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	ldr x9, [x28, #29520]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	ldr x9, [x28, #29528]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldr x9, [x28, #29536]
	ldr x10, [x28, #64]
	eor x9, x9, x10
	str x9, [x28, #64]
	ldr x9, [x28, #29544]
	ldr x10, [x28, #72]
	eor x9, x9, x10
	str x9, [x28, #72]
	ldr x9, [x28, #29552]
	ldr x10, [x28, #80]
	eor x9, x9, x10
	str x9, [x28, #80]
	ldr x9, [x28, #29560]
	ldr x10, [x28, #88]
	eor x9, x9, x10
	str x9, [x28, #88]
	ldr x9, [x28, #29568]
	ldr x10, [x28, #96]
	eor x9, x9, x10
	str x9, [x28, #96]
	ldr x9, [x28, #29576]
	ldr x10, [x28, #104]
	eor x9, x9, x10
	str x9, [x28, #104]
	ldr x9, [x28, #29584]
	ldr x10, [x28, #112]
	eor x9, x9, x10
	str x9, [x28, #112]
	ldr x9, [x28, #29592]
	ldr x10, [x28, #120]
	eor x9, x9, x10
	str x9, [x28, #120]
	ldr x9, [x28, #29600]
	ldr x10, [x28, #128]
	eor x9, x9, x10
	str x9, [x28, #128]
	add x2, x19, #1536
	str x30, [x2, #128]
	add x0, x19, #0
	add x1, x28, #0
	bl {vg_keccak_f1600_x3_sha3}
	ldr x30, [x19, #1664]
	ldr x6, [x19, #0]
	ldr x7, [x19, #8]
	str x6, [x20, #0]
	str x7, [x21, #0]
	ldr x6, [x19, #16]
	ldr x7, [x19, #24]
	str x6, [x20, #8]
	str x7, [x21, #8]
	ldr x6, [x19, #32]
	ldr x7, [x19, #40]
	str x6, [x20, #16]
	str x7, [x21, #16]
	ldr x6, [x19, #48]
	ldr x7, [x19, #56]
	str x6, [x20, #24]
	str x7, [x21, #24]
	ldr x6, [x19, #64]
	ldr x7, [x19, #72]
	str x6, [x20, #32]
	str x7, [x21, #32]
	ldr x6, [x19, #80]
	ldr x7, [x19, #88]
	str x6, [x20, #40]
	str x7, [x21, #40]
	ldr x6, [x19, #96]
	ldr x7, [x19, #104]
	str x6, [x20, #48]
	str x7, [x21, #48]
	ldr x6, [x19, #112]
	ldr x7, [x19, #120]
	str x6, [x20, #56]
	str x7, [x21, #56]
	ldr x6, [x19, #128]
	ldr x7, [x19, #136]
	str x6, [x20, #64]
	str x7, [x21, #64]
	ldr x6, [x19, #144]
	ldr x7, [x19, #152]
	str x6, [x20, #72]
	str x7, [x21, #72]
	ldr x6, [x19, #160]
	ldr x7, [x19, #168]
	str x6, [x20, #80]
	str x7, [x21, #80]
	ldr x6, [x19, #176]
	ldr x7, [x19, #184]
	str x6, [x20, #88]
	str x7, [x21, #88]
	ldr x6, [x19, #192]
	ldr x7, [x19, #200]
	str x6, [x20, #96]
	str x7, [x21, #96]
	ldr x6, [x19, #208]
	ldr x7, [x19, #216]
	str x6, [x20, #104]
	str x7, [x21, #104]
	ldr x6, [x19, #224]
	ldr x7, [x19, #232]
	str x6, [x20, #112]
	str x7, [x21, #112]
	ldr x6, [x19, #240]
	ldr x7, [x19, #248]
	str x6, [x20, #120]
	str x7, [x21, #120]
	ldr x6, [x19, #256]
	ldr x7, [x19, #264]
	str x6, [x20, #128]
	str x7, [x21, #128]
	ldr x6, [x19, #272]
	ldr x7, [x19, #280]
	str x6, [x20, #136]
	str x7, [x21, #136]
	ldr x6, [x19, #288]
	ldr x7, [x19, #296]
	str x6, [x20, #144]
	str x7, [x21, #144]
	ldr x6, [x19, #304]
	ldr x7, [x19, #312]
	str x6, [x20, #152]
	str x7, [x21, #152]
	ldr x6, [x19, #320]
	ldr x7, [x19, #328]
	str x6, [x20, #160]
	str x7, [x21, #160]
	add x20, x20, #168
	add x21, x21, #168
	movz x9, #256, lsl #0
	movk x9, #513, lsl #16
	movk x9, #1027, lsl #32
	movk x9, #1284, lsl #48
	dup v16.2d, x9
	movz x9, #1798, lsl #0
	movk x9, #2055, lsl #16
	movk x9, #2569, lsl #32
	movk x9, #2826, lsl #48
	mov v16.d[1], x9
	movz x9, #4095, lsl #0
	movk x9, #0, lsl #16
	movk x9, #4095, lsl #32
	movk x9, #0, lsl #48
	dup v17.2d, x9
	movz x9, #4095, lsl #0
	movk x9, #0, lsl #16
	movk x9, #4095, lsl #32
	movk x9, #0, lsl #48
	mov v17.d[1], x9
	movz x9, #257, lsl #0
	movk x9, #258, lsl #16
	movk x9, #260, lsl #32
	movk x9, #264, lsl #48
	dup v20.2d, x9
	movz x9, #272, lsl #0
	movk x9, #288, lsl #16
	movk x9, #320, lsl #32
	movk x9, #384, lsl #48
	mov v20.d[1], x9
	movz x9, #3329, lsl #0
	dup v19.8h, w9
	movi v21.2d, #0
	movz x9, #0, lsl #0
	str x9, [x19, #1408]
	adrp x16, {VG_MLKEM_REJ_SHUFFLE}
	add x16, x16, {VG_MLKEM_REJ_SHUFFLE}
	movz x21, #6296, lsl #0
	add x21, x28, x21
	movz x23, #7320, lsl #0
	add x23, x28, x23
	add x20, x19, #400
	add x1, x19, #1680
	movz x22, #1, lsl #0
269:
	add x2, x20, #0
	add x3, x21, #0
	movz x4, #256, lsl #0
	movz x5, #168, lsl #0
	movz x9, #3329, lsl #0
	movz x10, #15, lsl #0
270:
	sub x6, x4, #8
	lsr x6, x6, #63
	cbz x6, 271f
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 273f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 275f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 276f
275:
276:
	b 274f
273:
274:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 277f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 279f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 280f
279:
280:
	b 278f
277:
278:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 281f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 283f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 284f
283:
284:
	b 282f
281:
282:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 285f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 287f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 288f
287:
288:
	b 286f
285:
286:
	cbz x4, 289f
	b 290f
289:
	movz x5, #0, lsl #0
290:
	b 272f
271:
	ldr q0, [x2, #0]
	tbl v0.16b, {v0.16b}, v16.16b
	ushr v1.8h, v0.8h, #4
	bif v0.16b, v1.16b, v17.16b
	cmhi v1.8h, v19.8h, v0.8h
	and v1.16b, v1.16b, v20.16b
	addv h1, v1.8h
	umov w6, v1.s[0]
	movz x7, #255, lsl #0
	and x7, x6, x7
	lsl x7, x7, #4
	add x7, x16, x7
	ldr q2, [x7, #0]
	tbl v0.16b, {v0.16b}, v2.16b
	str q0, [x3, #0]
	lsr x6, x6, #8
	movz x7, #15, lsl #0
	and x6, x6, x7
	sub x4, x4, x6
	lsl x6, x6, #1
	add x3, x3, x6
	add x2, x2, #12
	sub x5, x5, #4
272:
	cbnz x5, 270b
	cbz x4, 291f
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	b 292f
291:
292:
	sub x0, x4, #1
	lsr x0, x0, #63
	str x3, [x1, #0]
	str x4, [x1, #8]
	and x22, x22, x0
	add x20, x20, #504
	add x21, x23, #0
	add x1, x1, #16
	sub x6, x1, x19
	sub x6, x6, #1712
	cbnz x6, 269b
	add x6, x22, #0
	cbz x6, 293f
	b 294f
293:
	movz x30, #1, lsl #0
295:
	add x20, x19, #400
	add x21, x19, #904
	add x1, x19, #768
	add x1, x1, #768
	str x30, [x1, #128]
	add x0, x19, #0
	bl {vg_keccak_f1600_x2_sha3}
	ldr x30, [x1, #128]
	ldr x6, [x19, #0]
	ldr x7, [x19, #8]
	str x6, [x20, #0]
	str x7, [x21, #0]
	ldr x6, [x19, #16]
	ldr x7, [x19, #24]
	str x6, [x20, #8]
	str x7, [x21, #8]
	ldr x6, [x19, #32]
	ldr x7, [x19, #40]
	str x6, [x20, #16]
	str x7, [x21, #16]
	ldr x6, [x19, #48]
	ldr x7, [x19, #56]
	str x6, [x20, #24]
	str x7, [x21, #24]
	ldr x6, [x19, #64]
	ldr x7, [x19, #72]
	str x6, [x20, #32]
	str x7, [x21, #32]
	ldr x6, [x19, #80]
	ldr x7, [x19, #88]
	str x6, [x20, #40]
	str x7, [x21, #40]
	ldr x6, [x19, #96]
	ldr x7, [x19, #104]
	str x6, [x20, #48]
	str x7, [x21, #48]
	ldr x6, [x19, #112]
	ldr x7, [x19, #120]
	str x6, [x20, #56]
	str x7, [x21, #56]
	ldr x6, [x19, #128]
	ldr x7, [x19, #136]
	str x6, [x20, #64]
	str x7, [x21, #64]
	ldr x6, [x19, #144]
	ldr x7, [x19, #152]
	str x6, [x20, #72]
	str x7, [x21, #72]
	ldr x6, [x19, #160]
	ldr x7, [x19, #168]
	str x6, [x20, #80]
	str x7, [x21, #80]
	ldr x6, [x19, #176]
	ldr x7, [x19, #184]
	str x6, [x20, #88]
	str x7, [x21, #88]
	ldr x6, [x19, #192]
	ldr x7, [x19, #200]
	str x6, [x20, #96]
	str x7, [x21, #96]
	ldr x6, [x19, #208]
	ldr x7, [x19, #216]
	str x6, [x20, #104]
	str x7, [x21, #104]
	ldr x6, [x19, #224]
	ldr x7, [x19, #232]
	str x6, [x20, #112]
	str x7, [x21, #112]
	ldr x6, [x19, #240]
	ldr x7, [x19, #248]
	str x6, [x20, #120]
	str x7, [x21, #120]
	ldr x6, [x19, #256]
	ldr x7, [x19, #264]
	str x6, [x20, #128]
	str x7, [x21, #128]
	ldr x6, [x19, #272]
	ldr x7, [x19, #280]
	str x6, [x20, #136]
	str x7, [x21, #136]
	ldr x6, [x19, #288]
	ldr x7, [x19, #296]
	str x6, [x20, #144]
	str x7, [x21, #144]
	ldr x6, [x19, #304]
	ldr x7, [x19, #312]
	str x6, [x20, #152]
	str x7, [x21, #152]
	ldr x6, [x19, #320]
	ldr x7, [x19, #328]
	str x6, [x20, #160]
	str x7, [x21, #160]
	movz x9, #256, lsl #0
	movk x9, #513, lsl #16
	movk x9, #1027, lsl #32
	movk x9, #1284, lsl #48
	dup v16.2d, x9
	movz x9, #1798, lsl #0
	movk x9, #2055, lsl #16
	movk x9, #2569, lsl #32
	movk x9, #2826, lsl #48
	mov v16.d[1], x9
	movz x9, #4095, lsl #0
	movk x9, #0, lsl #16
	movk x9, #4095, lsl #32
	movk x9, #0, lsl #48
	dup v17.2d, x9
	movz x9, #4095, lsl #0
	movk x9, #0, lsl #16
	movk x9, #4095, lsl #32
	movk x9, #0, lsl #48
	mov v17.d[1], x9
	movz x9, #257, lsl #0
	movk x9, #258, lsl #16
	movk x9, #260, lsl #32
	movk x9, #264, lsl #48
	dup v20.2d, x9
	movz x9, #272, lsl #0
	movk x9, #288, lsl #16
	movk x9, #320, lsl #32
	movk x9, #384, lsl #48
	mov v20.d[1], x9
	movz x9, #3329, lsl #0
	dup v19.8h, w9
	movi v21.2d, #0
	movz x9, #0, lsl #0
	str x9, [x19, #1408]
	adrp x16, {VG_MLKEM_REJ_SHUFFLE}
	add x16, x16, {VG_MLKEM_REJ_SHUFFLE}
	add x20, x19, #400
	add x1, x19, #1680
	movz x22, #1, lsl #0
	movz x23, #2, lsl #0
296:
	ldr x3, [x1, #0]
	ldr x4, [x1, #8]
	cbz x4, 297f
	add x2, x20, #0
	movz x5, #56, lsl #0
	movz x9, #3329, lsl #0
	movz x10, #15, lsl #0
299:
	sub x6, x4, #8
	lsr x6, x6, #63
	cbz x6, 2100f
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2102f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2104f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2105f
2104:
2105:
	b 2103f
2102:
2103:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2106f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2108f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2109f
2108:
2109:
	b 2107f
2106:
2107:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2110f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2112f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2113f
2112:
2113:
	b 2111f
2110:
2111:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2114f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2116f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2117f
2116:
2117:
	b 2115f
2114:
2115:
	cbz x4, 2118f
	b 2119f
2118:
	movz x5, #0, lsl #0
2119:
	b 2101f
2100:
	ldr q0, [x2, #0]
	tbl v0.16b, {v0.16b}, v16.16b
	ushr v1.8h, v0.8h, #4
	bif v0.16b, v1.16b, v17.16b
	cmhi v1.8h, v19.8h, v0.8h
	and v1.16b, v1.16b, v20.16b
	addv h1, v1.8h
	umov w6, v1.s[0]
	movz x7, #255, lsl #0
	and x7, x6, x7
	lsl x7, x7, #4
	add x7, x16, x7
	ldr q2, [x7, #0]
	tbl v0.16b, {v0.16b}, v2.16b
	str q0, [x3, #0]
	lsr x6, x6, #8
	movz x7, #15, lsl #0
	and x6, x6, x7
	sub x4, x4, x6
	lsl x6, x6, #1
	add x3, x3, x6
	add x2, x2, #12
	sub x5, x5, #4
2101:
	cbnz x5, 299b
	cbz x4, 2120f
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	b 2121f
2120:
2121:
	sub x0, x4, #1
	lsr x0, x0, #63
	str x3, [x1, #0]
	str x4, [x1, #8]
	b 298f
297:
	movz x0, #1, lsl #0
298:
	and x22, x22, x0
	add x20, x20, #504
	add x1, x1, #16
	sub x23, x23, #1
	cbnz x23, 296b
	add x6, x22, #0
	sub x7, x6, x30
	lsr x7, x7, #63
	movz x30, #0, lsl #0
	cbnz x7, 295b
	and x24, x24, x6
	ldr x3, [x19, #1680]
	ldr x4, [x19, #1688]
	cbz x4, 2122f
2124:
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	add x3, x3, #2
	sub x4, x4, #1
	cbnz x4, 2124b
	b 2123f
2122:
2123:
	ldr x3, [x19, #1696]
	ldr x4, [x19, #1704]
	cbz x4, 2125f
2127:
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	add x3, x3, #2
	sub x4, x4, #1
	cbnz x4, 2127b
	b 2126f
2125:
2126:
294:
	ldr x30, [x19, #1840]
	ldr x23, [x19, #1832]
	ldr x22, [x19, #1824]
	ldr x21, [x19, #1816]
	ldr x20, [x19, #1808]
	ldr x19, [x19, #1800]
	add x2, x28, #1176
	str x19, [x2, #1800]
	str x20, [x2, #1808]
	str x21, [x2, #1816]
	str x22, [x2, #1824]
	str x23, [x2, #1832]
	str x30, [x2, #1840]
	add x19, x2, #0
	movi v0.2d, #0
	str q0, [x19, #0]
	str q0, [x19, #16]
	str q0, [x19, #32]
	str q0, [x19, #48]
	str q0, [x19, #64]
	str q0, [x19, #80]
	str q0, [x19, #96]
	str q0, [x19, #112]
	str q0, [x19, #128]
	str q0, [x19, #144]
	str q0, [x19, #160]
	str q0, [x19, #176]
	str q0, [x19, #192]
	str q0, [x19, #208]
	str q0, [x19, #224]
	str q0, [x19, #240]
	str q0, [x19, #256]
	str q0, [x19, #272]
	str q0, [x19, #288]
	str q0, [x19, #304]
	str q0, [x19, #320]
	str q0, [x19, #336]
	str q0, [x19, #352]
	str q0, [x19, #368]
	str q0, [x19, #384]
	ldr x6, [x28, #840]
	dup v0.2d, x6
	str q0, [x19, #0]
	ldr x6, [x28, #848]
	dup v0.2d, x6
	str q0, [x19, #16]
	ldr x6, [x28, #856]
	dup v0.2d, x6
	str q0, [x19, #32]
	ldr x6, [x28, #864]
	dup v0.2d, x6
	str q0, [x19, #48]
	movz x6, #256, lsl #0
	movk x6, #31, lsl #16
	movz x7, #257, lsl #0
	movk x7, #31, lsl #16
	dup v0.2d, x6
	mov v0.d[1], x7
	str q0, [x19, #64]
	movz x6, #32768, lsl #48
	dup v0.2d, x6
	str q0, [x19, #320]
	add x20, x19, #400
	add x21, x19, #904
	movz x22, #3, lsl #0
	ldr x9, [x28, #29608]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	ldr x9, [x28, #29616]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	ldr x9, [x28, #29624]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	ldr x9, [x28, #29632]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	ldr x9, [x28, #29640]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	ldr x9, [x28, #29648]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	ldr x9, [x28, #29656]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	ldr x9, [x28, #29664]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldr x9, [x28, #29672]
	ldr x10, [x28, #64]
	eor x9, x9, x10
	str x9, [x28, #64]
	ldr x9, [x28, #29680]
	ldr x10, [x28, #72]
	eor x9, x9, x10
	str x9, [x28, #72]
	ldr x9, [x28, #29688]
	ldr x10, [x28, #80]
	eor x9, x9, x10
	str x9, [x28, #80]
	ldr x9, [x28, #29696]
	ldr x10, [x28, #88]
	eor x9, x9, x10
	str x9, [x28, #88]
	ldr x9, [x28, #29704]
	ldr x10, [x28, #96]
	eor x9, x9, x10
	str x9, [x28, #96]
	ldr x9, [x28, #29712]
	ldr x10, [x28, #104]
	eor x9, x9, x10
	str x9, [x28, #104]
	ldr x9, [x28, #29720]
	ldr x10, [x28, #112]
	eor x9, x9, x10
	str x9, [x28, #112]
	ldr x9, [x28, #29728]
	ldr x10, [x28, #120]
	eor x9, x9, x10
	str x9, [x28, #120]
	ldr x9, [x28, #29736]
	ldr x10, [x28, #128]
	eor x9, x9, x10
	str x9, [x28, #128]
	add x2, x19, #1536
	str x30, [x2, #128]
	add x0, x19, #0
	add x1, x28, #0
	bl {vg_keccak_f1600_x3_sha3}
	ldr x30, [x19, #1664]
	ldr x6, [x19, #0]
	ldr x7, [x19, #8]
	str x6, [x20, #0]
	str x7, [x21, #0]
	ldr x6, [x19, #16]
	ldr x7, [x19, #24]
	str x6, [x20, #8]
	str x7, [x21, #8]
	ldr x6, [x19, #32]
	ldr x7, [x19, #40]
	str x6, [x20, #16]
	str x7, [x21, #16]
	ldr x6, [x19, #48]
	ldr x7, [x19, #56]
	str x6, [x20, #24]
	str x7, [x21, #24]
	ldr x6, [x19, #64]
	ldr x7, [x19, #72]
	str x6, [x20, #32]
	str x7, [x21, #32]
	ldr x6, [x19, #80]
	ldr x7, [x19, #88]
	str x6, [x20, #40]
	str x7, [x21, #40]
	ldr x6, [x19, #96]
	ldr x7, [x19, #104]
	str x6, [x20, #48]
	str x7, [x21, #48]
	ldr x6, [x19, #112]
	ldr x7, [x19, #120]
	str x6, [x20, #56]
	str x7, [x21, #56]
	ldr x6, [x19, #128]
	ldr x7, [x19, #136]
	str x6, [x20, #64]
	str x7, [x21, #64]
	ldr x6, [x19, #144]
	ldr x7, [x19, #152]
	str x6, [x20, #72]
	str x7, [x21, #72]
	ldr x6, [x19, #160]
	ldr x7, [x19, #168]
	str x6, [x20, #80]
	str x7, [x21, #80]
	ldr x6, [x19, #176]
	ldr x7, [x19, #184]
	str x6, [x20, #88]
	str x7, [x21, #88]
	ldr x6, [x19, #192]
	ldr x7, [x19, #200]
	str x6, [x20, #96]
	str x7, [x21, #96]
	ldr x6, [x19, #208]
	ldr x7, [x19, #216]
	str x6, [x20, #104]
	str x7, [x21, #104]
	ldr x6, [x19, #224]
	ldr x7, [x19, #232]
	str x6, [x20, #112]
	str x7, [x21, #112]
	ldr x6, [x19, #240]
	ldr x7, [x19, #248]
	str x6, [x20, #120]
	str x7, [x21, #120]
	ldr x6, [x19, #256]
	ldr x7, [x19, #264]
	str x6, [x20, #128]
	str x7, [x21, #128]
	ldr x6, [x19, #272]
	ldr x7, [x19, #280]
	str x6, [x20, #136]
	str x7, [x21, #136]
	ldr x6, [x19, #288]
	ldr x7, [x19, #296]
	str x6, [x20, #144]
	str x7, [x21, #144]
	ldr x6, [x19, #304]
	ldr x7, [x19, #312]
	str x6, [x20, #152]
	str x7, [x21, #152]
	ldr x6, [x19, #320]
	ldr x7, [x19, #328]
	str x6, [x20, #160]
	str x7, [x21, #160]
	add x20, x20, #168
	add x21, x21, #168
	ldr x9, [x28, #29744]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	ldr x9, [x28, #29752]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	ldr x9, [x28, #29760]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	ldr x9, [x28, #29768]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	ldr x9, [x28, #29776]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	ldr x9, [x28, #29784]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	ldr x9, [x28, #29792]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	ldr x9, [x28, #29800]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldr x9, [x28, #29808]
	ldr x10, [x28, #64]
	eor x9, x9, x10
	str x9, [x28, #64]
	ldr x9, [x28, #29816]
	ldr x10, [x28, #72]
	eor x9, x9, x10
	str x9, [x28, #72]
	ldr x9, [x28, #29824]
	ldr x10, [x28, #80]
	eor x9, x9, x10
	str x9, [x28, #80]
	ldr x9, [x28, #29832]
	ldr x10, [x28, #88]
	eor x9, x9, x10
	str x9, [x28, #88]
	ldr x9, [x28, #29840]
	ldr x10, [x28, #96]
	eor x9, x9, x10
	str x9, [x28, #96]
	ldr x9, [x28, #29848]
	ldr x10, [x28, #104]
	eor x9, x9, x10
	str x9, [x28, #104]
	ldr x9, [x28, #29856]
	ldr x10, [x28, #112]
	eor x9, x9, x10
	str x9, [x28, #112]
	ldr x9, [x28, #29864]
	ldr x10, [x28, #120]
	eor x9, x9, x10
	str x9, [x28, #120]
	ldr x9, [x28, #29872]
	ldr x10, [x28, #128]
	eor x9, x9, x10
	str x9, [x28, #128]
	add x2, x19, #1536
	str x30, [x2, #128]
	add x0, x19, #0
	add x1, x28, #0
	bl {vg_keccak_f1600_x3_sha3}
	ldr x30, [x19, #1664]
	ldr x6, [x19, #0]
	ldr x7, [x19, #8]
	str x6, [x20, #0]
	str x7, [x21, #0]
	ldr x6, [x19, #16]
	ldr x7, [x19, #24]
	str x6, [x20, #8]
	str x7, [x21, #8]
	ldr x6, [x19, #32]
	ldr x7, [x19, #40]
	str x6, [x20, #16]
	str x7, [x21, #16]
	ldr x6, [x19, #48]
	ldr x7, [x19, #56]
	str x6, [x20, #24]
	str x7, [x21, #24]
	ldr x6, [x19, #64]
	ldr x7, [x19, #72]
	str x6, [x20, #32]
	str x7, [x21, #32]
	ldr x6, [x19, #80]
	ldr x7, [x19, #88]
	str x6, [x20, #40]
	str x7, [x21, #40]
	ldr x6, [x19, #96]
	ldr x7, [x19, #104]
	str x6, [x20, #48]
	str x7, [x21, #48]
	ldr x6, [x19, #112]
	ldr x7, [x19, #120]
	str x6, [x20, #56]
	str x7, [x21, #56]
	ldr x6, [x19, #128]
	ldr x7, [x19, #136]
	str x6, [x20, #64]
	str x7, [x21, #64]
	ldr x6, [x19, #144]
	ldr x7, [x19, #152]
	str x6, [x20, #72]
	str x7, [x21, #72]
	ldr x6, [x19, #160]
	ldr x7, [x19, #168]
	str x6, [x20, #80]
	str x7, [x21, #80]
	ldr x6, [x19, #176]
	ldr x7, [x19, #184]
	str x6, [x20, #88]
	str x7, [x21, #88]
	ldr x6, [x19, #192]
	ldr x7, [x19, #200]
	str x6, [x20, #96]
	str x7, [x21, #96]
	ldr x6, [x19, #208]
	ldr x7, [x19, #216]
	str x6, [x20, #104]
	str x7, [x21, #104]
	ldr x6, [x19, #224]
	ldr x7, [x19, #232]
	str x6, [x20, #112]
	str x7, [x21, #112]
	ldr x6, [x19, #240]
	ldr x7, [x19, #248]
	str x6, [x20, #120]
	str x7, [x21, #120]
	ldr x6, [x19, #256]
	ldr x7, [x19, #264]
	str x6, [x20, #128]
	str x7, [x21, #128]
	ldr x6, [x19, #272]
	ldr x7, [x19, #280]
	str x6, [x20, #136]
	str x7, [x21, #136]
	ldr x6, [x19, #288]
	ldr x7, [x19, #296]
	str x6, [x20, #144]
	str x7, [x21, #144]
	ldr x6, [x19, #304]
	ldr x7, [x19, #312]
	str x6, [x20, #152]
	str x7, [x21, #152]
	ldr x6, [x19, #320]
	ldr x7, [x19, #328]
	str x6, [x20, #160]
	str x7, [x21, #160]
	add x20, x20, #168
	add x21, x21, #168
	ldr x9, [x28, #29880]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	ldr x9, [x28, #29888]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	ldr x9, [x28, #29896]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	ldr x9, [x28, #29904]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	ldr x9, [x28, #29912]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	ldr x9, [x28, #29920]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	ldr x9, [x28, #29928]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	ldr x9, [x28, #29936]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldr x9, [x28, #29944]
	ldr x10, [x28, #64]
	eor x9, x9, x10
	str x9, [x28, #64]
	ldr x9, [x28, #29952]
	ldr x10, [x28, #72]
	eor x9, x9, x10
	str x9, [x28, #72]
	ldr x9, [x28, #29960]
	ldr x10, [x28, #80]
	eor x9, x9, x10
	str x9, [x28, #80]
	ldr x9, [x28, #29968]
	ldr x10, [x28, #88]
	eor x9, x9, x10
	str x9, [x28, #88]
	ldr x9, [x28, #29976]
	ldr x10, [x28, #96]
	eor x9, x9, x10
	str x9, [x28, #96]
	ldr x9, [x28, #29984]
	ldr x10, [x28, #104]
	eor x9, x9, x10
	str x9, [x28, #104]
	ldr x9, [x28, #29992]
	ldr x10, [x28, #112]
	eor x9, x9, x10
	str x9, [x28, #112]
	ldr x9, [x28, #30000]
	ldr x10, [x28, #120]
	eor x9, x9, x10
	str x9, [x28, #120]
	ldr x9, [x28, #30008]
	ldr x10, [x28, #128]
	eor x9, x9, x10
	str x9, [x28, #128]
	add x2, x19, #1536
	str x30, [x2, #128]
	add x0, x19, #0
	add x1, x28, #0
	bl {vg_keccak_f1600_x3_sha3}
	ldr x30, [x19, #1664]
	ldr x6, [x19, #0]
	ldr x7, [x19, #8]
	str x6, [x20, #0]
	str x7, [x21, #0]
	ldr x6, [x19, #16]
	ldr x7, [x19, #24]
	str x6, [x20, #8]
	str x7, [x21, #8]
	ldr x6, [x19, #32]
	ldr x7, [x19, #40]
	str x6, [x20, #16]
	str x7, [x21, #16]
	ldr x6, [x19, #48]
	ldr x7, [x19, #56]
	str x6, [x20, #24]
	str x7, [x21, #24]
	ldr x6, [x19, #64]
	ldr x7, [x19, #72]
	str x6, [x20, #32]
	str x7, [x21, #32]
	ldr x6, [x19, #80]
	ldr x7, [x19, #88]
	str x6, [x20, #40]
	str x7, [x21, #40]
	ldr x6, [x19, #96]
	ldr x7, [x19, #104]
	str x6, [x20, #48]
	str x7, [x21, #48]
	ldr x6, [x19, #112]
	ldr x7, [x19, #120]
	str x6, [x20, #56]
	str x7, [x21, #56]
	ldr x6, [x19, #128]
	ldr x7, [x19, #136]
	str x6, [x20, #64]
	str x7, [x21, #64]
	ldr x6, [x19, #144]
	ldr x7, [x19, #152]
	str x6, [x20, #72]
	str x7, [x21, #72]
	ldr x6, [x19, #160]
	ldr x7, [x19, #168]
	str x6, [x20, #80]
	str x7, [x21, #80]
	ldr x6, [x19, #176]
	ldr x7, [x19, #184]
	str x6, [x20, #88]
	str x7, [x21, #88]
	ldr x6, [x19, #192]
	ldr x7, [x19, #200]
	str x6, [x20, #96]
	str x7, [x21, #96]
	ldr x6, [x19, #208]
	ldr x7, [x19, #216]
	str x6, [x20, #104]
	str x7, [x21, #104]
	ldr x6, [x19, #224]
	ldr x7, [x19, #232]
	str x6, [x20, #112]
	str x7, [x21, #112]
	ldr x6, [x19, #240]
	ldr x7, [x19, #248]
	str x6, [x20, #120]
	str x7, [x21, #120]
	ldr x6, [x19, #256]
	ldr x7, [x19, #264]
	str x6, [x20, #128]
	str x7, [x21, #128]
	ldr x6, [x19, #272]
	ldr x7, [x19, #280]
	str x6, [x20, #136]
	str x7, [x21, #136]
	ldr x6, [x19, #288]
	ldr x7, [x19, #296]
	str x6, [x20, #144]
	str x7, [x21, #144]
	ldr x6, [x19, #304]
	ldr x7, [x19, #312]
	str x6, [x20, #152]
	str x7, [x21, #152]
	ldr x6, [x19, #320]
	ldr x7, [x19, #328]
	str x6, [x20, #160]
	str x7, [x21, #160]
	add x20, x20, #168
	add x21, x21, #168
	movz x9, #256, lsl #0
	movk x9, #513, lsl #16
	movk x9, #1027, lsl #32
	movk x9, #1284, lsl #48
	dup v16.2d, x9
	movz x9, #1798, lsl #0
	movk x9, #2055, lsl #16
	movk x9, #2569, lsl #32
	movk x9, #2826, lsl #48
	mov v16.d[1], x9
	movz x9, #4095, lsl #0
	movk x9, #0, lsl #16
	movk x9, #4095, lsl #32
	movk x9, #0, lsl #48
	dup v17.2d, x9
	movz x9, #4095, lsl #0
	movk x9, #0, lsl #16
	movk x9, #4095, lsl #32
	movk x9, #0, lsl #48
	mov v17.d[1], x9
	movz x9, #257, lsl #0
	movk x9, #258, lsl #16
	movk x9, #260, lsl #32
	movk x9, #264, lsl #48
	dup v20.2d, x9
	movz x9, #272, lsl #0
	movk x9, #288, lsl #16
	movk x9, #320, lsl #32
	movk x9, #384, lsl #48
	mov v20.d[1], x9
	movz x9, #3329, lsl #0
	dup v19.8h, w9
	movi v21.2d, #0
	movz x9, #0, lsl #0
	str x9, [x19, #1408]
	adrp x16, {VG_MLKEM_REJ_SHUFFLE}
	add x16, x16, {VG_MLKEM_REJ_SHUFFLE}
	movz x21, #8344, lsl #0
	add x21, x28, x21
	movz x23, #9368, lsl #0
	add x23, x28, x23
	add x20, x19, #400
	add x1, x19, #1680
	movz x22, #1, lsl #0
2128:
	add x2, x20, #0
	add x3, x21, #0
	movz x4, #256, lsl #0
	movz x5, #168, lsl #0
	movz x9, #3329, lsl #0
	movz x10, #15, lsl #0
2129:
	sub x6, x4, #8
	lsr x6, x6, #63
	cbz x6, 2130f
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2132f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2134f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2135f
2134:
2135:
	b 2133f
2132:
2133:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2136f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2138f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2139f
2138:
2139:
	b 2137f
2136:
2137:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2140f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2142f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2143f
2142:
2143:
	b 2141f
2140:
2141:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2144f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2146f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2147f
2146:
2147:
	b 2145f
2144:
2145:
	cbz x4, 2148f
	b 2149f
2148:
	movz x5, #0, lsl #0
2149:
	b 2131f
2130:
	ldr q0, [x2, #0]
	tbl v0.16b, {v0.16b}, v16.16b
	ushr v1.8h, v0.8h, #4
	bif v0.16b, v1.16b, v17.16b
	cmhi v1.8h, v19.8h, v0.8h
	and v1.16b, v1.16b, v20.16b
	addv h1, v1.8h
	umov w6, v1.s[0]
	movz x7, #255, lsl #0
	and x7, x6, x7
	lsl x7, x7, #4
	add x7, x16, x7
	ldr q2, [x7, #0]
	tbl v0.16b, {v0.16b}, v2.16b
	str q0, [x3, #0]
	lsr x6, x6, #8
	movz x7, #15, lsl #0
	and x6, x6, x7
	sub x4, x4, x6
	lsl x6, x6, #1
	add x3, x3, x6
	add x2, x2, #12
	sub x5, x5, #4
2131:
	cbnz x5, 2129b
	cbz x4, 2150f
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	b 2151f
2150:
2151:
	sub x0, x4, #1
	lsr x0, x0, #63
	str x3, [x1, #0]
	str x4, [x1, #8]
	and x22, x22, x0
	add x20, x20, #504
	add x21, x23, #0
	add x1, x1, #16
	sub x6, x1, x19
	sub x6, x6, #1712
	cbnz x6, 2128b
	add x6, x22, #0
	cbz x6, 2152f
	b 2153f
2152:
	movz x30, #1, lsl #0
2154:
	add x20, x19, #400
	add x21, x19, #904
	add x1, x19, #768
	add x1, x1, #768
	str x30, [x1, #128]
	add x0, x19, #0
	bl {vg_keccak_f1600_x2_sha3}
	ldr x30, [x1, #128]
	ldr x6, [x19, #0]
	ldr x7, [x19, #8]
	str x6, [x20, #0]
	str x7, [x21, #0]
	ldr x6, [x19, #16]
	ldr x7, [x19, #24]
	str x6, [x20, #8]
	str x7, [x21, #8]
	ldr x6, [x19, #32]
	ldr x7, [x19, #40]
	str x6, [x20, #16]
	str x7, [x21, #16]
	ldr x6, [x19, #48]
	ldr x7, [x19, #56]
	str x6, [x20, #24]
	str x7, [x21, #24]
	ldr x6, [x19, #64]
	ldr x7, [x19, #72]
	str x6, [x20, #32]
	str x7, [x21, #32]
	ldr x6, [x19, #80]
	ldr x7, [x19, #88]
	str x6, [x20, #40]
	str x7, [x21, #40]
	ldr x6, [x19, #96]
	ldr x7, [x19, #104]
	str x6, [x20, #48]
	str x7, [x21, #48]
	ldr x6, [x19, #112]
	ldr x7, [x19, #120]
	str x6, [x20, #56]
	str x7, [x21, #56]
	ldr x6, [x19, #128]
	ldr x7, [x19, #136]
	str x6, [x20, #64]
	str x7, [x21, #64]
	ldr x6, [x19, #144]
	ldr x7, [x19, #152]
	str x6, [x20, #72]
	str x7, [x21, #72]
	ldr x6, [x19, #160]
	ldr x7, [x19, #168]
	str x6, [x20, #80]
	str x7, [x21, #80]
	ldr x6, [x19, #176]
	ldr x7, [x19, #184]
	str x6, [x20, #88]
	str x7, [x21, #88]
	ldr x6, [x19, #192]
	ldr x7, [x19, #200]
	str x6, [x20, #96]
	str x7, [x21, #96]
	ldr x6, [x19, #208]
	ldr x7, [x19, #216]
	str x6, [x20, #104]
	str x7, [x21, #104]
	ldr x6, [x19, #224]
	ldr x7, [x19, #232]
	str x6, [x20, #112]
	str x7, [x21, #112]
	ldr x6, [x19, #240]
	ldr x7, [x19, #248]
	str x6, [x20, #120]
	str x7, [x21, #120]
	ldr x6, [x19, #256]
	ldr x7, [x19, #264]
	str x6, [x20, #128]
	str x7, [x21, #128]
	ldr x6, [x19, #272]
	ldr x7, [x19, #280]
	str x6, [x20, #136]
	str x7, [x21, #136]
	ldr x6, [x19, #288]
	ldr x7, [x19, #296]
	str x6, [x20, #144]
	str x7, [x21, #144]
	ldr x6, [x19, #304]
	ldr x7, [x19, #312]
	str x6, [x20, #152]
	str x7, [x21, #152]
	ldr x6, [x19, #320]
	ldr x7, [x19, #328]
	str x6, [x20, #160]
	str x7, [x21, #160]
	movz x9, #256, lsl #0
	movk x9, #513, lsl #16
	movk x9, #1027, lsl #32
	movk x9, #1284, lsl #48
	dup v16.2d, x9
	movz x9, #1798, lsl #0
	movk x9, #2055, lsl #16
	movk x9, #2569, lsl #32
	movk x9, #2826, lsl #48
	mov v16.d[1], x9
	movz x9, #4095, lsl #0
	movk x9, #0, lsl #16
	movk x9, #4095, lsl #32
	movk x9, #0, lsl #48
	dup v17.2d, x9
	movz x9, #4095, lsl #0
	movk x9, #0, lsl #16
	movk x9, #4095, lsl #32
	movk x9, #0, lsl #48
	mov v17.d[1], x9
	movz x9, #257, lsl #0
	movk x9, #258, lsl #16
	movk x9, #260, lsl #32
	movk x9, #264, lsl #48
	dup v20.2d, x9
	movz x9, #272, lsl #0
	movk x9, #288, lsl #16
	movk x9, #320, lsl #32
	movk x9, #384, lsl #48
	mov v20.d[1], x9
	movz x9, #3329, lsl #0
	dup v19.8h, w9
	movi v21.2d, #0
	movz x9, #0, lsl #0
	str x9, [x19, #1408]
	adrp x16, {VG_MLKEM_REJ_SHUFFLE}
	add x16, x16, {VG_MLKEM_REJ_SHUFFLE}
	add x20, x19, #400
	add x1, x19, #1680
	movz x22, #1, lsl #0
	movz x23, #2, lsl #0
2155:
	ldr x3, [x1, #0]
	ldr x4, [x1, #8]
	cbz x4, 2156f
	add x2, x20, #0
	movz x5, #56, lsl #0
	movz x9, #3329, lsl #0
	movz x10, #15, lsl #0
2158:
	sub x6, x4, #8
	lsr x6, x6, #63
	cbz x6, 2159f
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2161f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2163f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2164f
2163:
2164:
	b 2162f
2161:
2162:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2165f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2167f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2168f
2167:
2168:
	b 2166f
2165:
2166:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2169f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2171f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2172f
2171:
2172:
	b 2170f
2169:
2170:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2173f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2175f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2176f
2175:
2176:
	b 2174f
2173:
2174:
	cbz x4, 2177f
	b 2178f
2177:
	movz x5, #0, lsl #0
2178:
	b 2160f
2159:
	ldr q0, [x2, #0]
	tbl v0.16b, {v0.16b}, v16.16b
	ushr v1.8h, v0.8h, #4
	bif v0.16b, v1.16b, v17.16b
	cmhi v1.8h, v19.8h, v0.8h
	and v1.16b, v1.16b, v20.16b
	addv h1, v1.8h
	umov w6, v1.s[0]
	movz x7, #255, lsl #0
	and x7, x6, x7
	lsl x7, x7, #4
	add x7, x16, x7
	ldr q2, [x7, #0]
	tbl v0.16b, {v0.16b}, v2.16b
	str q0, [x3, #0]
	lsr x6, x6, #8
	movz x7, #15, lsl #0
	and x6, x6, x7
	sub x4, x4, x6
	lsl x6, x6, #1
	add x3, x3, x6
	add x2, x2, #12
	sub x5, x5, #4
2160:
	cbnz x5, 2158b
	cbz x4, 2179f
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	b 2180f
2179:
2180:
	sub x0, x4, #1
	lsr x0, x0, #63
	str x3, [x1, #0]
	str x4, [x1, #8]
	b 2157f
2156:
	movz x0, #1, lsl #0
2157:
	and x22, x22, x0
	add x20, x20, #504
	add x1, x1, #16
	sub x23, x23, #1
	cbnz x23, 2155b
	add x6, x22, #0
	sub x7, x6, x30
	lsr x7, x7, #63
	movz x30, #0, lsl #0
	cbnz x7, 2154b
	and x24, x24, x6
	ldr x3, [x19, #1680]
	ldr x4, [x19, #1688]
	cbz x4, 2181f
2183:
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	add x3, x3, #2
	sub x4, x4, #1
	cbnz x4, 2183b
	b 2182f
2181:
2182:
	ldr x3, [x19, #1696]
	ldr x4, [x19, #1704]
	cbz x4, 2184f
2186:
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	add x3, x3, #2
	sub x4, x4, #1
	cbnz x4, 2186b
	b 2185f
2184:
2185:
2153:
	ldr x30, [x19, #1840]
	ldr x23, [x19, #1832]
	ldr x22, [x19, #1824]
	ldr x21, [x19, #1816]
	ldr x20, [x19, #1808]
	ldr x19, [x19, #1800]
	add x2, x28, #1176
	str x19, [x2, #1800]
	str x20, [x2, #1808]
	str x21, [x2, #1816]
	str x22, [x2, #1824]
	str x23, [x2, #1832]
	str x30, [x2, #1840]
	add x19, x2, #0
	movi v0.2d, #0
	str q0, [x19, #0]
	str q0, [x19, #16]
	str q0, [x19, #32]
	str q0, [x19, #48]
	str q0, [x19, #64]
	str q0, [x19, #80]
	str q0, [x19, #96]
	str q0, [x19, #112]
	str q0, [x19, #128]
	str q0, [x19, #144]
	str q0, [x19, #160]
	str q0, [x19, #176]
	str q0, [x19, #192]
	str q0, [x19, #208]
	str q0, [x19, #224]
	str q0, [x19, #240]
	str q0, [x19, #256]
	str q0, [x19, #272]
	str q0, [x19, #288]
	str q0, [x19, #304]
	str q0, [x19, #320]
	str q0, [x19, #336]
	str q0, [x19, #352]
	str q0, [x19, #368]
	str q0, [x19, #384]
	ldr x6, [x28, #840]
	dup v0.2d, x6
	str q0, [x19, #0]
	ldr x6, [x28, #848]
	dup v0.2d, x6
	str q0, [x19, #16]
	ldr x6, [x28, #856]
	dup v0.2d, x6
	str q0, [x19, #32]
	ldr x6, [x28, #864]
	dup v0.2d, x6
	str q0, [x19, #48]
	movz x6, #258, lsl #0
	movk x6, #31, lsl #16
	movz x7, #259, lsl #0
	movk x7, #31, lsl #16
	dup v0.2d, x6
	mov v0.d[1], x7
	str q0, [x19, #64]
	movz x6, #32768, lsl #48
	dup v0.2d, x6
	str q0, [x19, #320]
	add x20, x19, #400
	add x21, x19, #904
	movz x22, #3, lsl #0
	ldr x9, [x28, #30016]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	ldr x9, [x28, #30024]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	ldr x9, [x28, #30032]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	ldr x9, [x28, #30040]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	ldr x9, [x28, #30048]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	ldr x9, [x28, #30056]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	ldr x9, [x28, #30064]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	ldr x9, [x28, #30072]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldr x9, [x28, #30080]
	ldr x10, [x28, #64]
	eor x9, x9, x10
	str x9, [x28, #64]
	ldr x9, [x28, #30088]
	ldr x10, [x28, #72]
	eor x9, x9, x10
	str x9, [x28, #72]
	ldr x9, [x28, #30096]
	ldr x10, [x28, #80]
	eor x9, x9, x10
	str x9, [x28, #80]
	ldr x9, [x28, #30104]
	ldr x10, [x28, #88]
	eor x9, x9, x10
	str x9, [x28, #88]
	ldr x9, [x28, #30112]
	ldr x10, [x28, #96]
	eor x9, x9, x10
	str x9, [x28, #96]
	ldr x9, [x28, #30120]
	ldr x10, [x28, #104]
	eor x9, x9, x10
	str x9, [x28, #104]
	ldr x9, [x28, #30128]
	ldr x10, [x28, #112]
	eor x9, x9, x10
	str x9, [x28, #112]
	ldr x9, [x28, #30136]
	ldr x10, [x28, #120]
	eor x9, x9, x10
	str x9, [x28, #120]
	ldr x9, [x28, #30144]
	ldr x10, [x28, #128]
	eor x9, x9, x10
	str x9, [x28, #128]
	add x2, x19, #1536
	str x30, [x2, #128]
	add x0, x19, #0
	add x1, x28, #0
	bl {vg_keccak_f1600_x3_sha3}
	ldr x30, [x19, #1664]
	ldr x6, [x19, #0]
	ldr x7, [x19, #8]
	str x6, [x20, #0]
	str x7, [x21, #0]
	ldr x6, [x19, #16]
	ldr x7, [x19, #24]
	str x6, [x20, #8]
	str x7, [x21, #8]
	ldr x6, [x19, #32]
	ldr x7, [x19, #40]
	str x6, [x20, #16]
	str x7, [x21, #16]
	ldr x6, [x19, #48]
	ldr x7, [x19, #56]
	str x6, [x20, #24]
	str x7, [x21, #24]
	ldr x6, [x19, #64]
	ldr x7, [x19, #72]
	str x6, [x20, #32]
	str x7, [x21, #32]
	ldr x6, [x19, #80]
	ldr x7, [x19, #88]
	str x6, [x20, #40]
	str x7, [x21, #40]
	ldr x6, [x19, #96]
	ldr x7, [x19, #104]
	str x6, [x20, #48]
	str x7, [x21, #48]
	ldr x6, [x19, #112]
	ldr x7, [x19, #120]
	str x6, [x20, #56]
	str x7, [x21, #56]
	ldr x6, [x19, #128]
	ldr x7, [x19, #136]
	str x6, [x20, #64]
	str x7, [x21, #64]
	ldr x6, [x19, #144]
	ldr x7, [x19, #152]
	str x6, [x20, #72]
	str x7, [x21, #72]
	ldr x6, [x19, #160]
	ldr x7, [x19, #168]
	str x6, [x20, #80]
	str x7, [x21, #80]
	ldr x6, [x19, #176]
	ldr x7, [x19, #184]
	str x6, [x20, #88]
	str x7, [x21, #88]
	ldr x6, [x19, #192]
	ldr x7, [x19, #200]
	str x6, [x20, #96]
	str x7, [x21, #96]
	ldr x6, [x19, #208]
	ldr x7, [x19, #216]
	str x6, [x20, #104]
	str x7, [x21, #104]
	ldr x6, [x19, #224]
	ldr x7, [x19, #232]
	str x6, [x20, #112]
	str x7, [x21, #112]
	ldr x6, [x19, #240]
	ldr x7, [x19, #248]
	str x6, [x20, #120]
	str x7, [x21, #120]
	ldr x6, [x19, #256]
	ldr x7, [x19, #264]
	str x6, [x20, #128]
	str x7, [x21, #128]
	ldr x6, [x19, #272]
	ldr x7, [x19, #280]
	str x6, [x20, #136]
	str x7, [x21, #136]
	ldr x6, [x19, #288]
	ldr x7, [x19, #296]
	str x6, [x20, #144]
	str x7, [x21, #144]
	ldr x6, [x19, #304]
	ldr x7, [x19, #312]
	str x6, [x20, #152]
	str x7, [x21, #152]
	ldr x6, [x19, #320]
	ldr x7, [x19, #328]
	str x6, [x20, #160]
	str x7, [x21, #160]
	add x20, x20, #168
	add x21, x21, #168
	ldr x9, [x28, #30152]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	ldr x9, [x28, #30160]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	ldr x9, [x28, #30168]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	ldr x9, [x28, #30176]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	ldr x9, [x28, #30184]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	ldr x9, [x28, #30192]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	ldr x9, [x28, #30200]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	ldr x9, [x28, #30208]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldr x9, [x28, #30216]
	ldr x10, [x28, #64]
	eor x9, x9, x10
	str x9, [x28, #64]
	ldr x9, [x28, #30224]
	ldr x10, [x28, #72]
	eor x9, x9, x10
	str x9, [x28, #72]
	ldr x9, [x28, #30232]
	ldr x10, [x28, #80]
	eor x9, x9, x10
	str x9, [x28, #80]
	ldr x9, [x28, #30240]
	ldr x10, [x28, #88]
	eor x9, x9, x10
	str x9, [x28, #88]
	ldr x9, [x28, #30248]
	ldr x10, [x28, #96]
	eor x9, x9, x10
	str x9, [x28, #96]
	ldr x9, [x28, #30256]
	ldr x10, [x28, #104]
	eor x9, x9, x10
	str x9, [x28, #104]
	ldr x9, [x28, #30264]
	ldr x10, [x28, #112]
	eor x9, x9, x10
	str x9, [x28, #112]
	ldr x9, [x28, #30272]
	ldr x10, [x28, #120]
	eor x9, x9, x10
	str x9, [x28, #120]
	ldr x9, [x28, #30280]
	ldr x10, [x28, #128]
	eor x9, x9, x10
	str x9, [x28, #128]
	add x2, x19, #1536
	str x30, [x2, #128]
	add x0, x19, #0
	add x1, x28, #0
	bl {vg_keccak_f1600_x3_sha3}
	ldr x30, [x19, #1664]
	ldr x6, [x19, #0]
	ldr x7, [x19, #8]
	str x6, [x20, #0]
	str x7, [x21, #0]
	ldr x6, [x19, #16]
	ldr x7, [x19, #24]
	str x6, [x20, #8]
	str x7, [x21, #8]
	ldr x6, [x19, #32]
	ldr x7, [x19, #40]
	str x6, [x20, #16]
	str x7, [x21, #16]
	ldr x6, [x19, #48]
	ldr x7, [x19, #56]
	str x6, [x20, #24]
	str x7, [x21, #24]
	ldr x6, [x19, #64]
	ldr x7, [x19, #72]
	str x6, [x20, #32]
	str x7, [x21, #32]
	ldr x6, [x19, #80]
	ldr x7, [x19, #88]
	str x6, [x20, #40]
	str x7, [x21, #40]
	ldr x6, [x19, #96]
	ldr x7, [x19, #104]
	str x6, [x20, #48]
	str x7, [x21, #48]
	ldr x6, [x19, #112]
	ldr x7, [x19, #120]
	str x6, [x20, #56]
	str x7, [x21, #56]
	ldr x6, [x19, #128]
	ldr x7, [x19, #136]
	str x6, [x20, #64]
	str x7, [x21, #64]
	ldr x6, [x19, #144]
	ldr x7, [x19, #152]
	str x6, [x20, #72]
	str x7, [x21, #72]
	ldr x6, [x19, #160]
	ldr x7, [x19, #168]
	str x6, [x20, #80]
	str x7, [x21, #80]
	ldr x6, [x19, #176]
	ldr x7, [x19, #184]
	str x6, [x20, #88]
	str x7, [x21, #88]
	ldr x6, [x19, #192]
	ldr x7, [x19, #200]
	str x6, [x20, #96]
	str x7, [x21, #96]
	ldr x6, [x19, #208]
	ldr x7, [x19, #216]
	str x6, [x20, #104]
	str x7, [x21, #104]
	ldr x6, [x19, #224]
	ldr x7, [x19, #232]
	str x6, [x20, #112]
	str x7, [x21, #112]
	ldr x6, [x19, #240]
	ldr x7, [x19, #248]
	str x6, [x20, #120]
	str x7, [x21, #120]
	ldr x6, [x19, #256]
	ldr x7, [x19, #264]
	str x6, [x20, #128]
	str x7, [x21, #128]
	ldr x6, [x19, #272]
	ldr x7, [x19, #280]
	str x6, [x20, #136]
	str x7, [x21, #136]
	ldr x6, [x19, #288]
	ldr x7, [x19, #296]
	str x6, [x20, #144]
	str x7, [x21, #144]
	ldr x6, [x19, #304]
	ldr x7, [x19, #312]
	str x6, [x20, #152]
	str x7, [x21, #152]
	ldr x6, [x19, #320]
	ldr x7, [x19, #328]
	str x6, [x20, #160]
	str x7, [x21, #160]
	add x20, x20, #168
	add x21, x21, #168
	ldr x9, [x28, #30288]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	ldr x9, [x28, #30296]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	ldr x9, [x28, #30304]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	ldr x9, [x28, #30312]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	ldr x9, [x28, #30320]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	ldr x9, [x28, #30328]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	ldr x9, [x28, #30336]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	ldr x9, [x28, #30344]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldr x9, [x28, #30352]
	ldr x10, [x28, #64]
	eor x9, x9, x10
	str x9, [x28, #64]
	ldr x9, [x28, #30360]
	ldr x10, [x28, #72]
	eor x9, x9, x10
	str x9, [x28, #72]
	ldr x9, [x28, #30368]
	ldr x10, [x28, #80]
	eor x9, x9, x10
	str x9, [x28, #80]
	ldr x9, [x28, #30376]
	ldr x10, [x28, #88]
	eor x9, x9, x10
	str x9, [x28, #88]
	ldr x9, [x28, #30384]
	ldr x10, [x28, #96]
	eor x9, x9, x10
	str x9, [x28, #96]
	ldrb w9, [x28, #104]
	movz x10, #31, lsl #0
	eor x9, x9, x10
	strb w9, [x28, #104]
	ldrb w9, [x28, #135]
	movz x10, #128, lsl #0
	eor x9, x9, x10
	strb w9, [x28, #135]
	add x2, x19, #1536
	str x30, [x2, #128]
	add x0, x19, #0
	add x1, x28, #0
	bl {vg_keccak_f1600_x3_sha3}
	ldr x30, [x19, #1664]
	ldr x6, [x19, #0]
	ldr x7, [x19, #8]
	str x6, [x20, #0]
	str x7, [x21, #0]
	ldr x6, [x19, #16]
	ldr x7, [x19, #24]
	str x6, [x20, #8]
	str x7, [x21, #8]
	ldr x6, [x19, #32]
	ldr x7, [x19, #40]
	str x6, [x20, #16]
	str x7, [x21, #16]
	ldr x6, [x19, #48]
	ldr x7, [x19, #56]
	str x6, [x20, #24]
	str x7, [x21, #24]
	ldr x6, [x19, #64]
	ldr x7, [x19, #72]
	str x6, [x20, #32]
	str x7, [x21, #32]
	ldr x6, [x19, #80]
	ldr x7, [x19, #88]
	str x6, [x20, #40]
	str x7, [x21, #40]
	ldr x6, [x19, #96]
	ldr x7, [x19, #104]
	str x6, [x20, #48]
	str x7, [x21, #48]
	ldr x6, [x19, #112]
	ldr x7, [x19, #120]
	str x6, [x20, #56]
	str x7, [x21, #56]
	ldr x6, [x19, #128]
	ldr x7, [x19, #136]
	str x6, [x20, #64]
	str x7, [x21, #64]
	ldr x6, [x19, #144]
	ldr x7, [x19, #152]
	str x6, [x20, #72]
	str x7, [x21, #72]
	ldr x6, [x19, #160]
	ldr x7, [x19, #168]
	str x6, [x20, #80]
	str x7, [x21, #80]
	ldr x6, [x19, #176]
	ldr x7, [x19, #184]
	str x6, [x20, #88]
	str x7, [x21, #88]
	ldr x6, [x19, #192]
	ldr x7, [x19, #200]
	str x6, [x20, #96]
	str x7, [x21, #96]
	ldr x6, [x19, #208]
	ldr x7, [x19, #216]
	str x6, [x20, #104]
	str x7, [x21, #104]
	ldr x6, [x19, #224]
	ldr x7, [x19, #232]
	str x6, [x20, #112]
	str x7, [x21, #112]
	ldr x6, [x19, #240]
	ldr x7, [x19, #248]
	str x6, [x20, #120]
	str x7, [x21, #120]
	ldr x6, [x19, #256]
	ldr x7, [x19, #264]
	str x6, [x20, #128]
	str x7, [x21, #128]
	ldr x6, [x19, #272]
	ldr x7, [x19, #280]
	str x6, [x20, #136]
	str x7, [x21, #136]
	ldr x6, [x19, #288]
	ldr x7, [x19, #296]
	str x6, [x20, #144]
	str x7, [x21, #144]
	ldr x6, [x19, #304]
	ldr x7, [x19, #312]
	str x6, [x20, #152]
	str x7, [x21, #152]
	ldr x6, [x19, #320]
	ldr x7, [x19, #328]
	str x6, [x20, #160]
	str x7, [x21, #160]
	add x20, x20, #168
	add x21, x21, #168
	movz x9, #256, lsl #0
	movk x9, #513, lsl #16
	movk x9, #1027, lsl #32
	movk x9, #1284, lsl #48
	dup v16.2d, x9
	movz x9, #1798, lsl #0
	movk x9, #2055, lsl #16
	movk x9, #2569, lsl #32
	movk x9, #2826, lsl #48
	mov v16.d[1], x9
	movz x9, #4095, lsl #0
	movk x9, #0, lsl #16
	movk x9, #4095, lsl #32
	movk x9, #0, lsl #48
	dup v17.2d, x9
	movz x9, #4095, lsl #0
	movk x9, #0, lsl #16
	movk x9, #4095, lsl #32
	movk x9, #0, lsl #48
	mov v17.d[1], x9
	movz x9, #257, lsl #0
	movk x9, #258, lsl #16
	movk x9, #260, lsl #32
	movk x9, #264, lsl #48
	dup v20.2d, x9
	movz x9, #272, lsl #0
	movk x9, #288, lsl #16
	movk x9, #320, lsl #32
	movk x9, #384, lsl #48
	mov v20.d[1], x9
	movz x9, #3329, lsl #0
	dup v19.8h, w9
	movi v21.2d, #0
	movz x9, #0, lsl #0
	str x9, [x19, #1408]
	adrp x16, {VG_MLKEM_REJ_SHUFFLE}
	add x16, x16, {VG_MLKEM_REJ_SHUFFLE}
	movz x21, #10392, lsl #0
	add x21, x28, x21
	movz x23, #11416, lsl #0
	add x23, x28, x23
	add x20, x19, #400
	add x1, x19, #1680
	movz x22, #1, lsl #0
2187:
	add x2, x20, #0
	add x3, x21, #0
	movz x4, #256, lsl #0
	movz x5, #168, lsl #0
	movz x9, #3329, lsl #0
	movz x10, #15, lsl #0
2188:
	sub x6, x4, #8
	lsr x6, x6, #63
	cbz x6, 2189f
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2191f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2193f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2194f
2193:
2194:
	b 2192f
2191:
2192:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2195f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2197f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2198f
2197:
2198:
	b 2196f
2195:
2196:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2199f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2201f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2202f
2201:
2202:
	b 2200f
2199:
2200:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2203f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2205f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2206f
2205:
2206:
	b 2204f
2203:
2204:
	cbz x4, 2207f
	b 2208f
2207:
	movz x5, #0, lsl #0
2208:
	b 2190f
2189:
	ldr q0, [x2, #0]
	tbl v0.16b, {v0.16b}, v16.16b
	ushr v1.8h, v0.8h, #4
	bif v0.16b, v1.16b, v17.16b
	cmhi v1.8h, v19.8h, v0.8h
	and v1.16b, v1.16b, v20.16b
	addv h1, v1.8h
	umov w6, v1.s[0]
	movz x7, #255, lsl #0
	and x7, x6, x7
	lsl x7, x7, #4
	add x7, x16, x7
	ldr q2, [x7, #0]
	tbl v0.16b, {v0.16b}, v2.16b
	str q0, [x3, #0]
	lsr x6, x6, #8
	movz x7, #15, lsl #0
	and x6, x6, x7
	sub x4, x4, x6
	lsl x6, x6, #1
	add x3, x3, x6
	add x2, x2, #12
	sub x5, x5, #4
2190:
	cbnz x5, 2188b
	cbz x4, 2209f
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	b 2210f
2209:
2210:
	sub x0, x4, #1
	lsr x0, x0, #63
	str x3, [x1, #0]
	str x4, [x1, #8]
	and x22, x22, x0
	add x20, x20, #504
	add x21, x23, #0
	add x1, x1, #16
	sub x6, x1, x19
	sub x6, x6, #1712
	cbnz x6, 2187b
	add x6, x22, #0
	cbz x6, 2211f
	b 2212f
2211:
	movz x30, #1, lsl #0
2213:
	add x20, x19, #400
	add x21, x19, #904
	add x1, x19, #768
	add x1, x1, #768
	str x30, [x1, #128]
	add x0, x19, #0
	bl {vg_keccak_f1600_x2_sha3}
	ldr x30, [x1, #128]
	ldr x6, [x19, #0]
	ldr x7, [x19, #8]
	str x6, [x20, #0]
	str x7, [x21, #0]
	ldr x6, [x19, #16]
	ldr x7, [x19, #24]
	str x6, [x20, #8]
	str x7, [x21, #8]
	ldr x6, [x19, #32]
	ldr x7, [x19, #40]
	str x6, [x20, #16]
	str x7, [x21, #16]
	ldr x6, [x19, #48]
	ldr x7, [x19, #56]
	str x6, [x20, #24]
	str x7, [x21, #24]
	ldr x6, [x19, #64]
	ldr x7, [x19, #72]
	str x6, [x20, #32]
	str x7, [x21, #32]
	ldr x6, [x19, #80]
	ldr x7, [x19, #88]
	str x6, [x20, #40]
	str x7, [x21, #40]
	ldr x6, [x19, #96]
	ldr x7, [x19, #104]
	str x6, [x20, #48]
	str x7, [x21, #48]
	ldr x6, [x19, #112]
	ldr x7, [x19, #120]
	str x6, [x20, #56]
	str x7, [x21, #56]
	ldr x6, [x19, #128]
	ldr x7, [x19, #136]
	str x6, [x20, #64]
	str x7, [x21, #64]
	ldr x6, [x19, #144]
	ldr x7, [x19, #152]
	str x6, [x20, #72]
	str x7, [x21, #72]
	ldr x6, [x19, #160]
	ldr x7, [x19, #168]
	str x6, [x20, #80]
	str x7, [x21, #80]
	ldr x6, [x19, #176]
	ldr x7, [x19, #184]
	str x6, [x20, #88]
	str x7, [x21, #88]
	ldr x6, [x19, #192]
	ldr x7, [x19, #200]
	str x6, [x20, #96]
	str x7, [x21, #96]
	ldr x6, [x19, #208]
	ldr x7, [x19, #216]
	str x6, [x20, #104]
	str x7, [x21, #104]
	ldr x6, [x19, #224]
	ldr x7, [x19, #232]
	str x6, [x20, #112]
	str x7, [x21, #112]
	ldr x6, [x19, #240]
	ldr x7, [x19, #248]
	str x6, [x20, #120]
	str x7, [x21, #120]
	ldr x6, [x19, #256]
	ldr x7, [x19, #264]
	str x6, [x20, #128]
	str x7, [x21, #128]
	ldr x6, [x19, #272]
	ldr x7, [x19, #280]
	str x6, [x20, #136]
	str x7, [x21, #136]
	ldr x6, [x19, #288]
	ldr x7, [x19, #296]
	str x6, [x20, #144]
	str x7, [x21, #144]
	ldr x6, [x19, #304]
	ldr x7, [x19, #312]
	str x6, [x20, #152]
	str x7, [x21, #152]
	ldr x6, [x19, #320]
	ldr x7, [x19, #328]
	str x6, [x20, #160]
	str x7, [x21, #160]
	movz x9, #256, lsl #0
	movk x9, #513, lsl #16
	movk x9, #1027, lsl #32
	movk x9, #1284, lsl #48
	dup v16.2d, x9
	movz x9, #1798, lsl #0
	movk x9, #2055, lsl #16
	movk x9, #2569, lsl #32
	movk x9, #2826, lsl #48
	mov v16.d[1], x9
	movz x9, #4095, lsl #0
	movk x9, #0, lsl #16
	movk x9, #4095, lsl #32
	movk x9, #0, lsl #48
	dup v17.2d, x9
	movz x9, #4095, lsl #0
	movk x9, #0, lsl #16
	movk x9, #4095, lsl #32
	movk x9, #0, lsl #48
	mov v17.d[1], x9
	movz x9, #257, lsl #0
	movk x9, #258, lsl #16
	movk x9, #260, lsl #32
	movk x9, #264, lsl #48
	dup v20.2d, x9
	movz x9, #272, lsl #0
	movk x9, #288, lsl #16
	movk x9, #320, lsl #32
	movk x9, #384, lsl #48
	mov v20.d[1], x9
	movz x9, #3329, lsl #0
	dup v19.8h, w9
	movi v21.2d, #0
	movz x9, #0, lsl #0
	str x9, [x19, #1408]
	adrp x16, {VG_MLKEM_REJ_SHUFFLE}
	add x16, x16, {VG_MLKEM_REJ_SHUFFLE}
	add x20, x19, #400
	add x1, x19, #1680
	movz x22, #1, lsl #0
	movz x23, #2, lsl #0
2214:
	ldr x3, [x1, #0]
	ldr x4, [x1, #8]
	cbz x4, 2215f
	add x2, x20, #0
	movz x5, #56, lsl #0
	movz x9, #3329, lsl #0
	movz x10, #15, lsl #0
2217:
	sub x6, x4, #8
	lsr x6, x6, #63
	cbz x6, 2218f
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2220f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2222f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2223f
2222:
2223:
	b 2221f
2220:
2221:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2224f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2226f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2227f
2226:
2227:
	b 2225f
2224:
2225:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2228f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2230f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2231f
2230:
2231:
	b 2229f
2228:
2229:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2232f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2234f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2235f
2234:
2235:
	b 2233f
2232:
2233:
	cbz x4, 2236f
	b 2237f
2236:
	movz x5, #0, lsl #0
2237:
	b 2219f
2218:
	ldr q0, [x2, #0]
	tbl v0.16b, {v0.16b}, v16.16b
	ushr v1.8h, v0.8h, #4
	bif v0.16b, v1.16b, v17.16b
	cmhi v1.8h, v19.8h, v0.8h
	and v1.16b, v1.16b, v20.16b
	addv h1, v1.8h
	umov w6, v1.s[0]
	movz x7, #255, lsl #0
	and x7, x6, x7
	lsl x7, x7, #4
	add x7, x16, x7
	ldr q2, [x7, #0]
	tbl v0.16b, {v0.16b}, v2.16b
	str q0, [x3, #0]
	lsr x6, x6, #8
	movz x7, #15, lsl #0
	and x6, x6, x7
	sub x4, x4, x6
	lsl x6, x6, #1
	add x3, x3, x6
	add x2, x2, #12
	sub x5, x5, #4
2219:
	cbnz x5, 2217b
	cbz x4, 2238f
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	b 2239f
2238:
2239:
	sub x0, x4, #1
	lsr x0, x0, #63
	str x3, [x1, #0]
	str x4, [x1, #8]
	b 2216f
2215:
	movz x0, #1, lsl #0
2216:
	and x22, x22, x0
	add x20, x20, #504
	add x1, x1, #16
	sub x23, x23, #1
	cbnz x23, 2214b
	add x6, x22, #0
	sub x7, x6, x30
	lsr x7, x7, #63
	movz x30, #0, lsl #0
	cbnz x7, 2213b
	and x24, x24, x6
	ldr x3, [x19, #1680]
	ldr x4, [x19, #1688]
	cbz x4, 2240f
2242:
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	add x3, x3, #2
	sub x4, x4, #1
	cbnz x4, 2242b
	b 2241f
2240:
2241:
	ldr x3, [x19, #1696]
	ldr x4, [x19, #1704]
	cbz x4, 2243f
2245:
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	add x3, x3, #2
	sub x4, x4, #1
	cbnz x4, 2245b
	b 2244f
2243:
2244:
2212:
	ldr x30, [x19, #1840]
	ldr x23, [x19, #1832]
	ldr x22, [x19, #1824]
	ldr x21, [x19, #1816]
	ldr x20, [x19, #1808]
	ldr x19, [x19, #1800]
	ldr x9, [x28, #0]
	str x9, [x28, #1016]
	ldr x9, [x28, #8]
	str x9, [x28, #1024]
	ldr x9, [x28, #16]
	str x9, [x28, #1032]
	ldr x9, [x28, #24]
	str x9, [x28, #1040]
	bl {vg_mlkem1024_pair_prf_840_1176_4248_944_25752_8_0_3}
	bl {vg_mlkem1024_pair_prf_840_1176_4248_944_25752_10_3_3}
	bl {vg_mlkem1024_pair_prf_840_1176_4248_944_25752_12_6_3}
	add x2, x28, #1176
	str x19, [x2, #1800]
	str x20, [x2, #1808]
	str x21, [x2, #1816]
	str x22, [x2, #1824]
	str x23, [x2, #1832]
	str x30, [x2, #1840]
	add x19, x2, #0
	movi v0.2d, #0
	str q0, [x19, #0]
	str q0, [x19, #16]
	str q0, [x19, #32]
	str q0, [x19, #48]
	str q0, [x19, #64]
	str q0, [x19, #80]
	str q0, [x19, #96]
	str q0, [x19, #112]
	str q0, [x19, #128]
	str q0, [x19, #144]
	str q0, [x19, #160]
	str q0, [x19, #176]
	str q0, [x19, #192]
	str q0, [x19, #208]
	str q0, [x19, #224]
	str q0, [x19, #240]
	str q0, [x19, #256]
	str q0, [x19, #272]
	str q0, [x19, #288]
	str q0, [x19, #304]
	str q0, [x19, #320]
	str q0, [x19, #336]
	str q0, [x19, #352]
	str q0, [x19, #368]
	str q0, [x19, #384]
	ldr x6, [x28, #840]
	dup v0.2d, x6
	str q0, [x19, #0]
	ldr x6, [x28, #848]
	dup v0.2d, x6
	str q0, [x19, #16]
	ldr x6, [x28, #856]
	dup v0.2d, x6
	str q0, [x19, #32]
	ldr x6, [x28, #864]
	dup v0.2d, x6
	str q0, [x19, #48]
	movz x6, #770, lsl #0
	movk x6, #31, lsl #16
	movz x7, #771, lsl #0
	movk x7, #31, lsl #16
	dup v0.2d, x6
	mov v0.d[1], x7
	str q0, [x19, #64]
	movz x6, #32768, lsl #48
	dup v0.2d, x6
	str q0, [x19, #320]
	add x20, x19, #400
	add x21, x19, #904
	movz x22, #3, lsl #0
2246:
	add x1, x19, #768
	add x1, x1, #768
	str x30, [x1, #128]
	add x0, x19, #0
	bl {vg_keccak_f1600_x2_sha3}
	ldr x30, [x1, #128]
	ldr x6, [x19, #0]
	ldr x7, [x19, #8]
	str x6, [x20, #0]
	str x7, [x21, #0]
	ldr x6, [x19, #16]
	ldr x7, [x19, #24]
	str x6, [x20, #8]
	str x7, [x21, #8]
	ldr x6, [x19, #32]
	ldr x7, [x19, #40]
	str x6, [x20, #16]
	str x7, [x21, #16]
	ldr x6, [x19, #48]
	ldr x7, [x19, #56]
	str x6, [x20, #24]
	str x7, [x21, #24]
	ldr x6, [x19, #64]
	ldr x7, [x19, #72]
	str x6, [x20, #32]
	str x7, [x21, #32]
	ldr x6, [x19, #80]
	ldr x7, [x19, #88]
	str x6, [x20, #40]
	str x7, [x21, #40]
	ldr x6, [x19, #96]
	ldr x7, [x19, #104]
	str x6, [x20, #48]
	str x7, [x21, #48]
	ldr x6, [x19, #112]
	ldr x7, [x19, #120]
	str x6, [x20, #56]
	str x7, [x21, #56]
	ldr x6, [x19, #128]
	ldr x7, [x19, #136]
	str x6, [x20, #64]
	str x7, [x21, #64]
	ldr x6, [x19, #144]
	ldr x7, [x19, #152]
	str x6, [x20, #72]
	str x7, [x21, #72]
	ldr x6, [x19, #160]
	ldr x7, [x19, #168]
	str x6, [x20, #80]
	str x7, [x21, #80]
	ldr x6, [x19, #176]
	ldr x7, [x19, #184]
	str x6, [x20, #88]
	str x7, [x21, #88]
	ldr x6, [x19, #192]
	ldr x7, [x19, #200]
	str x6, [x20, #96]
	str x7, [x21, #96]
	ldr x6, [x19, #208]
	ldr x7, [x19, #216]
	str x6, [x20, #104]
	str x7, [x21, #104]
	ldr x6, [x19, #224]
	ldr x7, [x19, #232]
	str x6, [x20, #112]
	str x7, [x21, #112]
	ldr x6, [x19, #240]
	ldr x7, [x19, #248]
	str x6, [x20, #120]
	str x7, [x21, #120]
	ldr x6, [x19, #256]
	ldr x7, [x19, #264]
	str x6, [x20, #128]
	str x7, [x21, #128]
	ldr x6, [x19, #272]
	ldr x7, [x19, #280]
	str x6, [x20, #136]
	str x7, [x21, #136]
	ldr x6, [x19, #288]
	ldr x7, [x19, #296]
	str x6, [x20, #144]
	str x7, [x21, #144]
	ldr x6, [x19, #304]
	ldr x7, [x19, #312]
	str x6, [x20, #152]
	str x7, [x21, #152]
	ldr x6, [x19, #320]
	ldr x7, [x19, #328]
	str x6, [x20, #160]
	str x7, [x21, #160]
	add x20, x20, #168
	add x21, x21, #168
	sub x22, x22, #1
	cbnz x22, 2246b
	movz x9, #256, lsl #0
	movk x9, #513, lsl #16
	movk x9, #1027, lsl #32
	movk x9, #1284, lsl #48
	dup v16.2d, x9
	movz x9, #1798, lsl #0
	movk x9, #2055, lsl #16
	movk x9, #2569, lsl #32
	movk x9, #2826, lsl #48
	mov v16.d[1], x9
	movz x9, #4095, lsl #0
	movk x9, #0, lsl #16
	movk x9, #4095, lsl #32
	movk x9, #0, lsl #48
	dup v17.2d, x9
	movz x9, #4095, lsl #0
	movk x9, #0, lsl #16
	movk x9, #4095, lsl #32
	movk x9, #0, lsl #48
	mov v17.d[1], x9
	movz x9, #257, lsl #0
	movk x9, #258, lsl #16
	movk x9, #260, lsl #32
	movk x9, #264, lsl #48
	dup v20.2d, x9
	movz x9, #272, lsl #0
	movk x9, #288, lsl #16
	movk x9, #320, lsl #32
	movk x9, #384, lsl #48
	mov v20.d[1], x9
	movz x9, #3329, lsl #0
	dup v19.8h, w9
	movi v21.2d, #0
	movz x9, #0, lsl #0
	str x9, [x19, #1408]
	adrp x16, {VG_MLKEM_REJ_SHUFFLE}
	add x16, x16, {VG_MLKEM_REJ_SHUFFLE}
	movz x21, #18584, lsl #0
	add x21, x28, x21
	movz x23, #19608, lsl #0
	add x23, x28, x23
	add x20, x19, #400
	add x1, x19, #1680
	movz x22, #1, lsl #0
2247:
	add x2, x20, #0
	add x3, x21, #0
	movz x4, #256, lsl #0
	movz x5, #168, lsl #0
	movz x9, #3329, lsl #0
	movz x10, #15, lsl #0
2248:
	sub x6, x4, #8
	lsr x6, x6, #63
	cbz x6, 2249f
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2251f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2253f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2254f
2253:
2254:
	b 2252f
2251:
2252:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2255f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2257f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2258f
2257:
2258:
	b 2256f
2255:
2256:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2259f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2261f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2262f
2261:
2262:
	b 2260f
2259:
2260:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2263f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2265f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2266f
2265:
2266:
	b 2264f
2263:
2264:
	cbz x4, 2267f
	b 2268f
2267:
	movz x5, #0, lsl #0
2268:
	b 2250f
2249:
	ldr q0, [x2, #0]
	tbl v0.16b, {v0.16b}, v16.16b
	ushr v1.8h, v0.8h, #4
	bif v0.16b, v1.16b, v17.16b
	cmhi v1.8h, v19.8h, v0.8h
	and v1.16b, v1.16b, v20.16b
	addv h1, v1.8h
	umov w6, v1.s[0]
	movz x7, #255, lsl #0
	and x7, x6, x7
	lsl x7, x7, #4
	add x7, x16, x7
	ldr q2, [x7, #0]
	tbl v0.16b, {v0.16b}, v2.16b
	str q0, [x3, #0]
	lsr x6, x6, #8
	movz x7, #15, lsl #0
	and x6, x6, x7
	sub x4, x4, x6
	lsl x6, x6, #1
	add x3, x3, x6
	add x2, x2, #12
	sub x5, x5, #4
2250:
	cbnz x5, 2248b
	cbz x4, 2269f
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	b 2270f
2269:
2270:
	sub x0, x4, #1
	lsr x0, x0, #63
	str x3, [x1, #0]
	str x4, [x1, #8]
	and x22, x22, x0
	add x20, x20, #504
	add x21, x23, #0
	add x1, x1, #16
	sub x6, x1, x19
	sub x6, x6, #1712
	cbnz x6, 2247b
	add x6, x22, #0
	cbz x6, 2271f
	b 2272f
2271:
	movz x30, #1, lsl #0
2273:
	add x20, x19, #400
	add x21, x19, #904
	add x1, x19, #768
	add x1, x1, #768
	str x30, [x1, #128]
	add x0, x19, #0
	bl {vg_keccak_f1600_x2_sha3}
	ldr x30, [x1, #128]
	ldr x6, [x19, #0]
	ldr x7, [x19, #8]
	str x6, [x20, #0]
	str x7, [x21, #0]
	ldr x6, [x19, #16]
	ldr x7, [x19, #24]
	str x6, [x20, #8]
	str x7, [x21, #8]
	ldr x6, [x19, #32]
	ldr x7, [x19, #40]
	str x6, [x20, #16]
	str x7, [x21, #16]
	ldr x6, [x19, #48]
	ldr x7, [x19, #56]
	str x6, [x20, #24]
	str x7, [x21, #24]
	ldr x6, [x19, #64]
	ldr x7, [x19, #72]
	str x6, [x20, #32]
	str x7, [x21, #32]
	ldr x6, [x19, #80]
	ldr x7, [x19, #88]
	str x6, [x20, #40]
	str x7, [x21, #40]
	ldr x6, [x19, #96]
	ldr x7, [x19, #104]
	str x6, [x20, #48]
	str x7, [x21, #48]
	ldr x6, [x19, #112]
	ldr x7, [x19, #120]
	str x6, [x20, #56]
	str x7, [x21, #56]
	ldr x6, [x19, #128]
	ldr x7, [x19, #136]
	str x6, [x20, #64]
	str x7, [x21, #64]
	ldr x6, [x19, #144]
	ldr x7, [x19, #152]
	str x6, [x20, #72]
	str x7, [x21, #72]
	ldr x6, [x19, #160]
	ldr x7, [x19, #168]
	str x6, [x20, #80]
	str x7, [x21, #80]
	ldr x6, [x19, #176]
	ldr x7, [x19, #184]
	str x6, [x20, #88]
	str x7, [x21, #88]
	ldr x6, [x19, #192]
	ldr x7, [x19, #200]
	str x6, [x20, #96]
	str x7, [x21, #96]
	ldr x6, [x19, #208]
	ldr x7, [x19, #216]
	str x6, [x20, #104]
	str x7, [x21, #104]
	ldr x6, [x19, #224]
	ldr x7, [x19, #232]
	str x6, [x20, #112]
	str x7, [x21, #112]
	ldr x6, [x19, #240]
	ldr x7, [x19, #248]
	str x6, [x20, #120]
	str x7, [x21, #120]
	ldr x6, [x19, #256]
	ldr x7, [x19, #264]
	str x6, [x20, #128]
	str x7, [x21, #128]
	ldr x6, [x19, #272]
	ldr x7, [x19, #280]
	str x6, [x20, #136]
	str x7, [x21, #136]
	ldr x6, [x19, #288]
	ldr x7, [x19, #296]
	str x6, [x20, #144]
	str x7, [x21, #144]
	ldr x6, [x19, #304]
	ldr x7, [x19, #312]
	str x6, [x20, #152]
	str x7, [x21, #152]
	ldr x6, [x19, #320]
	ldr x7, [x19, #328]
	str x6, [x20, #160]
	str x7, [x21, #160]
	movz x9, #256, lsl #0
	movk x9, #513, lsl #16
	movk x9, #1027, lsl #32
	movk x9, #1284, lsl #48
	dup v16.2d, x9
	movz x9, #1798, lsl #0
	movk x9, #2055, lsl #16
	movk x9, #2569, lsl #32
	movk x9, #2826, lsl #48
	mov v16.d[1], x9
	movz x9, #4095, lsl #0
	movk x9, #0, lsl #16
	movk x9, #4095, lsl #32
	movk x9, #0, lsl #48
	dup v17.2d, x9
	movz x9, #4095, lsl #0
	movk x9, #0, lsl #16
	movk x9, #4095, lsl #32
	movk x9, #0, lsl #48
	mov v17.d[1], x9
	movz x9, #257, lsl #0
	movk x9, #258, lsl #16
	movk x9, #260, lsl #32
	movk x9, #264, lsl #48
	dup v20.2d, x9
	movz x9, #272, lsl #0
	movk x9, #288, lsl #16
	movk x9, #320, lsl #32
	movk x9, #384, lsl #48
	mov v20.d[1], x9
	movz x9, #3329, lsl #0
	dup v19.8h, w9
	movi v21.2d, #0
	movz x9, #0, lsl #0
	str x9, [x19, #1408]
	adrp x16, {VG_MLKEM_REJ_SHUFFLE}
	add x16, x16, {VG_MLKEM_REJ_SHUFFLE}
	add x20, x19, #400
	add x1, x19, #1680
	movz x22, #1, lsl #0
	movz x23, #2, lsl #0
2274:
	ldr x3, [x1, #0]
	ldr x4, [x1, #8]
	cbz x4, 2275f
	add x2, x20, #0
	movz x5, #56, lsl #0
	movz x9, #3329, lsl #0
	movz x10, #15, lsl #0
2277:
	sub x6, x4, #8
	lsr x6, x6, #63
	cbz x6, 2278f
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2280f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2282f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2283f
2282:
2283:
	b 2281f
2280:
2281:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2284f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2286f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2287f
2286:
2287:
	b 2285f
2284:
2285:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2288f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2290f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2291f
2290:
2291:
	b 2289f
2288:
2289:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2292f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2294f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2295f
2294:
2295:
	b 2293f
2292:
2293:
	cbz x4, 2296f
	b 2297f
2296:
	movz x5, #0, lsl #0
2297:
	b 2279f
2278:
	ldr q0, [x2, #0]
	tbl v0.16b, {v0.16b}, v16.16b
	ushr v1.8h, v0.8h, #4
	bif v0.16b, v1.16b, v17.16b
	cmhi v1.8h, v19.8h, v0.8h
	and v1.16b, v1.16b, v20.16b
	addv h1, v1.8h
	umov w6, v1.s[0]
	movz x7, #255, lsl #0
	and x7, x6, x7
	lsl x7, x7, #4
	add x7, x16, x7
	ldr q2, [x7, #0]
	tbl v0.16b, {v0.16b}, v2.16b
	str q0, [x3, #0]
	lsr x6, x6, #8
	movz x7, #15, lsl #0
	and x6, x6, x7
	sub x4, x4, x6
	lsl x6, x6, #1
	add x3, x3, x6
	add x2, x2, #12
	sub x5, x5, #4
2279:
	cbnz x5, 2277b
	cbz x4, 2298f
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	b 2299f
2298:
2299:
	sub x0, x4, #1
	lsr x0, x0, #63
	str x3, [x1, #0]
	str x4, [x1, #8]
	b 2276f
2275:
	movz x0, #1, lsl #0
2276:
	and x22, x22, x0
	add x20, x20, #504
	add x1, x1, #16
	sub x23, x23, #1
	cbnz x23, 2274b
	add x6, x22, #0
	sub x7, x6, x30
	lsr x7, x7, #63
	movz x30, #0, lsl #0
	cbnz x7, 2273b
	and x24, x24, x6
	ldr x3, [x19, #1680]
	ldr x4, [x19, #1688]
	cbz x4, 2300f
2302:
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	add x3, x3, #2
	sub x4, x4, #1
	cbnz x4, 2302b
	b 2301f
2300:
2301:
	ldr x3, [x19, #1696]
	ldr x4, [x19, #1704]
	cbz x4, 2303f
2305:
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	add x3, x3, #2
	sub x4, x4, #1
	cbnz x4, 2305b
	b 2304f
2303:
2304:
2272:
	ldr x30, [x19, #1840]
	ldr x23, [x19, #1832]
	ldr x22, [x19, #1824]
	ldr x21, [x19, #1816]
	ldr x20, [x19, #1808]
	ldr x19, [x19, #1800]
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #20632, lsl #0
	add x1, x28, x1
	bl {vg_mlkem16_cbd2}
	movz x0, #20632, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem16_ntt}
	movz x0, #25920, lsl #0
	add x0, x28, x0
	movz x1, #21656, lsl #0
	add x1, x28, x1
	bl {vg_mlkem16_cbd2}
	movz x0, #21656, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem16_ntt}
	movz x0, #26088, lsl #0
	add x0, x28, x0
	movz x1, #22680, lsl #0
	add x1, x28, x1
	bl {vg_mlkem16_cbd2}
	movz x0, #22680, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem16_ntt}
	movz x0, #26256, lsl #0
	add x0, x28, x0
	movz x1, #23704, lsl #0
	add x1, x28, x1
	bl {vg_mlkem16_cbd2}
	movz x0, #23704, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem16_ntt}
	movz x0, #26424, lsl #0
	add x0, x28, x0
	movz x1, #45056, lsl #0
	add x1, x28, x1
	bl {vg_mlkem16_cbd2}
	movz x0, #26592, lsl #0
	add x0, x28, x0
	movz x1, #46080, lsl #0
	add x1, x28, x1
	bl {vg_mlkem16_cbd2}
	movz x0, #26760, lsl #0
	add x0, x28, x0
	movz x1, #47104, lsl #0
	add x1, x28, x1
	bl {vg_mlkem16_cbd2}
	movz x0, #26928, lsl #0
	add x0, x28, x0
	movz x1, #48128, lsl #0
	add x1, x28, x1
	bl {vg_mlkem16_cbd2}
	movz x0, #27096, lsl #0
	add x0, x28, x0
	movz x1, #24728, lsl #0
	add x1, x28, x1
	bl {vg_mlkem16_cbd2}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x9, #3329, lsl #0
	movz x10, #55259, lsl #0
	movk x10, #9, lsl #16
	movk x10, #0, lsl #32
	movk x10, #0, lsl #48
	dup v16.4s, w9
	dup v17.4s, w10
	adrp x3, {VG_MLKEM_GAMMA}
	add x3, x3, {VG_MLKEM_GAMMA}
	movz x11, #16, lsl #0
	movz x12, #0, lsl #0
2306:
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movz x1, #4248, lsl #0
	add x1, x28, x1
	movz x2, #20632, lsl #0
	add x2, x28, x2
	add x1, x1, x12
	add x2, x2, x12
	ldr q0, [x1, #0]
	ldr q1, [x1, #16]
	ldr q4, [x2, #0]
	ldr q5, [x2, #16]
	uzp1 v6.8h, v0.8h, v1.8h
	uzp2 v7.8h, v0.8h, v1.8h
	uzp1 v19.8h, v4.8h, v5.8h
	uzp2 v20.8h, v4.8h, v5.8h
	umlal v21.4s, v6.4h, v19.4h
	umlal2 v25.4s, v6.8h, v19.8h
	umlal v22.4s, v7.4h, v20.4h
	umlal2 v26.4s, v7.8h, v20.8h
	umlal v23.4s, v6.4h, v20.4h
	umlal2 v27.4s, v6.8h, v20.8h
	umlal v23.4s, v7.4h, v19.4h
	umlal2 v27.4s, v7.8h, v19.8h
	movz x1, #8344, lsl #0
	add x1, x28, x1
	movz x2, #21656, lsl #0
	add x2, x28, x2
	add x1, x1, x12
	add x2, x2, x12
	ldr q0, [x1, #0]
	ldr q1, [x1, #16]
	ldr q4, [x2, #0]
	ldr q5, [x2, #16]
	uzp1 v6.8h, v0.8h, v1.8h
	uzp2 v7.8h, v0.8h, v1.8h
	uzp1 v19.8h, v4.8h, v5.8h
	uzp2 v20.8h, v4.8h, v5.8h
	umlal v21.4s, v6.4h, v19.4h
	umlal2 v25.4s, v6.8h, v19.8h
	umlal v22.4s, v7.4h, v20.4h
	umlal2 v26.4s, v7.8h, v20.8h
	umlal v23.4s, v6.4h, v20.4h
	umlal2 v27.4s, v6.8h, v20.8h
	umlal v23.4s, v7.4h, v19.4h
	umlal2 v27.4s, v7.8h, v19.8h
	movz x1, #12440, lsl #0
	add x1, x28, x1
	movz x2, #22680, lsl #0
	add x2, x28, x2
	add x1, x1, x12
	add x2, x2, x12
	ldr q0, [x1, #0]
	ldr q1, [x1, #16]
	ldr q4, [x2, #0]
	ldr q5, [x2, #16]
	uzp1 v6.8h, v0.8h, v1.8h
	uzp2 v7.8h, v0.8h, v1.8h
	uzp1 v19.8h, v4.8h, v5.8h
	uzp2 v20.8h, v4.8h, v5.8h
	umlal v21.4s, v6.4h, v19.4h
	umlal2 v25.4s, v6.8h, v19.8h
	umlal v22.4s, v7.4h, v20.4h
	umlal2 v26.4s, v7.8h, v20.8h
	umlal v23.4s, v6.4h, v20.4h
	umlal2 v27.4s, v6.8h, v20.8h
	umlal v23.4s, v7.4h, v19.4h
	umlal2 v27.4s, v7.8h, v19.8h
	movz x1, #16536, lsl #0
	add x1, x28, x1
	movz x2, #23704, lsl #0
	add x2, x28, x2
	add x1, x1, x12
	add x2, x2, x12
	ldr q0, [x1, #0]
	ldr q1, [x1, #16]
	ldr q4, [x2, #0]
	ldr q5, [x2, #16]
	uzp1 v6.8h, v0.8h, v1.8h
	uzp2 v7.8h, v0.8h, v1.8h
	uzp1 v19.8h, v4.8h, v5.8h
	uzp2 v20.8h, v4.8h, v5.8h
	umlal v21.4s, v6.4h, v19.4h
	umlal2 v25.4s, v6.8h, v19.8h
	umlal v22.4s, v7.4h, v20.4h
	umlal2 v26.4s, v7.8h, v20.8h
	umlal v23.4s, v6.4h, v20.4h
	umlal2 v27.4s, v6.8h, v20.8h
	umlal v23.4s, v7.4h, v19.4h
	umlal2 v27.4s, v7.8h, v19.8h
	ldr q18, [x3, #0]
	ldr q28, [x3, #16]
	sqdmulh v24.4s, v22.4s, v17.4s
	mls v22.4s, v24.4s, v16.4s
	mla v21.4s, v22.4s, v18.4s
	sqdmulh v24.4s, v21.4s, v17.4s
	mls v21.4s, v24.4s, v16.4s
	sub v24.4s, v21.4s, v16.4s
	umin v21.4s, v21.4s, v24.4s
	sqdmulh v24.4s, v23.4s, v17.4s
	mls v23.4s, v24.4s, v16.4s
	sub v24.4s, v23.4s, v16.4s
	umin v23.4s, v23.4s, v24.4s
	sqdmulh v24.4s, v26.4s, v17.4s
	mls v26.4s, v24.4s, v16.4s
	mla v25.4s, v26.4s, v28.4s
	sqdmulh v24.4s, v25.4s, v17.4s
	mls v25.4s, v24.4s, v16.4s
	sub v24.4s, v25.4s, v16.4s
	umin v25.4s, v25.4s, v24.4s
	sqdmulh v24.4s, v27.4s, v17.4s
	mls v27.4s, v24.4s, v16.4s
	sub v24.4s, v27.4s, v16.4s
	umin v27.4s, v27.4s, v24.4s
	uzp1 v0.8h, v21.8h, v25.8h
	uzp1 v1.8h, v23.8h, v27.8h
	zip1 v2.8h, v0.8h, v1.8h
	zip2 v3.8h, v0.8h, v1.8h
	str q2, [x0, #0]
	str q3, [x0, #16]
	add x0, x0, #32
	add x3, x3, #32
	add x12, x12, #32
	sub x11, x11, #1
	cbnz x11, 2306b
	movz x0, #25752, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem16_inv_ntt}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #45056, lsl #0
	add x1, x28, x1
	movz x9, #3329, lsl #0
	dup v16.8h, w9
	movz x11, #32, lsl #0
2307:
	ldr q0, [x0, #0]
	ldr q1, [x1, #0]
	add v2.8h, v0.8h, v1.8h
	cmhs v3.8h, v2.8h, v16.8h
	and v3.16b, v3.16b, v16.16b
	sub v2.8h, v2.8h, v3.8h
	str q2, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x11, x11, #1
	cbnz x11, 2307b
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #26776, lsl #0
	add x1, x28, x1
	movz x10, #32, lsl #0
	movi v29.2d, #0
2308:
	ldr q0, [x0, #0]
	zip1 v1.8h, v0.8h, v29.8h
	zip2 v2.8h, v0.8h, v29.8h
	str q1, [x1, #0]
	str q2, [x1, #16]
	add x0, x0, #16
	add x1, x1, #32
	sub x10, x10, #1
	cbnz x10, 2308b
	movz x0, #26776, lsl #0
	add x0, x28, x0
	movz x1, #11, lsl #0
	movz x2, #28824, lsl #0
	add x2, x28, x2
	movz x3, #352, lsl #0
	bl {vg_mlkem1024_compress_encode}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x9, #3329, lsl #0
	movz x10, #55259, lsl #0
	movk x10, #9, lsl #16
	movk x10, #0, lsl #32
	movk x10, #0, lsl #48
	dup v16.4s, w9
	dup v17.4s, w10
	adrp x3, {VG_MLKEM_GAMMA}
	add x3, x3, {VG_MLKEM_GAMMA}
	movz x11, #16, lsl #0
	movz x12, #0, lsl #0
2309:
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movz x1, #5272, lsl #0
	add x1, x28, x1
	movz x2, #20632, lsl #0
	add x2, x28, x2
	add x1, x1, x12
	add x2, x2, x12
	ldr q0, [x1, #0]
	ldr q1, [x1, #16]
	ldr q4, [x2, #0]
	ldr q5, [x2, #16]
	uzp1 v6.8h, v0.8h, v1.8h
	uzp2 v7.8h, v0.8h, v1.8h
	uzp1 v19.8h, v4.8h, v5.8h
	uzp2 v20.8h, v4.8h, v5.8h
	umlal v21.4s, v6.4h, v19.4h
	umlal2 v25.4s, v6.8h, v19.8h
	umlal v22.4s, v7.4h, v20.4h
	umlal2 v26.4s, v7.8h, v20.8h
	umlal v23.4s, v6.4h, v20.4h
	umlal2 v27.4s, v6.8h, v20.8h
	umlal v23.4s, v7.4h, v19.4h
	umlal2 v27.4s, v7.8h, v19.8h
	movz x1, #9368, lsl #0
	add x1, x28, x1
	movz x2, #21656, lsl #0
	add x2, x28, x2
	add x1, x1, x12
	add x2, x2, x12
	ldr q0, [x1, #0]
	ldr q1, [x1, #16]
	ldr q4, [x2, #0]
	ldr q5, [x2, #16]
	uzp1 v6.8h, v0.8h, v1.8h
	uzp2 v7.8h, v0.8h, v1.8h
	uzp1 v19.8h, v4.8h, v5.8h
	uzp2 v20.8h, v4.8h, v5.8h
	umlal v21.4s, v6.4h, v19.4h
	umlal2 v25.4s, v6.8h, v19.8h
	umlal v22.4s, v7.4h, v20.4h
	umlal2 v26.4s, v7.8h, v20.8h
	umlal v23.4s, v6.4h, v20.4h
	umlal2 v27.4s, v6.8h, v20.8h
	umlal v23.4s, v7.4h, v19.4h
	umlal2 v27.4s, v7.8h, v19.8h
	movz x1, #13464, lsl #0
	add x1, x28, x1
	movz x2, #22680, lsl #0
	add x2, x28, x2
	add x1, x1, x12
	add x2, x2, x12
	ldr q0, [x1, #0]
	ldr q1, [x1, #16]
	ldr q4, [x2, #0]
	ldr q5, [x2, #16]
	uzp1 v6.8h, v0.8h, v1.8h
	uzp2 v7.8h, v0.8h, v1.8h
	uzp1 v19.8h, v4.8h, v5.8h
	uzp2 v20.8h, v4.8h, v5.8h
	umlal v21.4s, v6.4h, v19.4h
	umlal2 v25.4s, v6.8h, v19.8h
	umlal v22.4s, v7.4h, v20.4h
	umlal2 v26.4s, v7.8h, v20.8h
	umlal v23.4s, v6.4h, v20.4h
	umlal2 v27.4s, v6.8h, v20.8h
	umlal v23.4s, v7.4h, v19.4h
	umlal2 v27.4s, v7.8h, v19.8h
	movz x1, #17560, lsl #0
	add x1, x28, x1
	movz x2, #23704, lsl #0
	add x2, x28, x2
	add x1, x1, x12
	add x2, x2, x12
	ldr q0, [x1, #0]
	ldr q1, [x1, #16]
	ldr q4, [x2, #0]
	ldr q5, [x2, #16]
	uzp1 v6.8h, v0.8h, v1.8h
	uzp2 v7.8h, v0.8h, v1.8h
	uzp1 v19.8h, v4.8h, v5.8h
	uzp2 v20.8h, v4.8h, v5.8h
	umlal v21.4s, v6.4h, v19.4h
	umlal2 v25.4s, v6.8h, v19.8h
	umlal v22.4s, v7.4h, v20.4h
	umlal2 v26.4s, v7.8h, v20.8h
	umlal v23.4s, v6.4h, v20.4h
	umlal2 v27.4s, v6.8h, v20.8h
	umlal v23.4s, v7.4h, v19.4h
	umlal2 v27.4s, v7.8h, v19.8h
	ldr q18, [x3, #0]
	ldr q28, [x3, #16]
	sqdmulh v24.4s, v22.4s, v17.4s
	mls v22.4s, v24.4s, v16.4s
	mla v21.4s, v22.4s, v18.4s
	sqdmulh v24.4s, v21.4s, v17.4s
	mls v21.4s, v24.4s, v16.4s
	sub v24.4s, v21.4s, v16.4s
	umin v21.4s, v21.4s, v24.4s
	sqdmulh v24.4s, v23.4s, v17.4s
	mls v23.4s, v24.4s, v16.4s
	sub v24.4s, v23.4s, v16.4s
	umin v23.4s, v23.4s, v24.4s
	sqdmulh v24.4s, v26.4s, v17.4s
	mls v26.4s, v24.4s, v16.4s
	mla v25.4s, v26.4s, v28.4s
	sqdmulh v24.4s, v25.4s, v17.4s
	mls v25.4s, v24.4s, v16.4s
	sub v24.4s, v25.4s, v16.4s
	umin v25.4s, v25.4s, v24.4s
	sqdmulh v24.4s, v27.4s, v17.4s
	mls v27.4s, v24.4s, v16.4s
	sub v24.4s, v27.4s, v16.4s
	umin v27.4s, v27.4s, v24.4s
	uzp1 v0.8h, v21.8h, v25.8h
	uzp1 v1.8h, v23.8h, v27.8h
	zip1 v2.8h, v0.8h, v1.8h
	zip2 v3.8h, v0.8h, v1.8h
	str q2, [x0, #0]
	str q3, [x0, #16]
	add x0, x0, #32
	add x3, x3, #32
	add x12, x12, #32
	sub x11, x11, #1
	cbnz x11, 2309b
	movz x0, #25752, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem16_inv_ntt}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #46080, lsl #0
	add x1, x28, x1
	movz x9, #3329, lsl #0
	dup v16.8h, w9
	movz x11, #32, lsl #0
2310:
	ldr q0, [x0, #0]
	ldr q1, [x1, #0]
	add v2.8h, v0.8h, v1.8h
	cmhs v3.8h, v2.8h, v16.8h
	and v3.16b, v3.16b, v16.16b
	sub v2.8h, v2.8h, v3.8h
	str q2, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x11, x11, #1
	cbnz x11, 2310b
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #26776, lsl #0
	add x1, x28, x1
	movz x10, #32, lsl #0
	movi v29.2d, #0
2311:
	ldr q0, [x0, #0]
	zip1 v1.8h, v0.8h, v29.8h
	zip2 v2.8h, v0.8h, v29.8h
	str q1, [x1, #0]
	str q2, [x1, #16]
	add x0, x0, #16
	add x1, x1, #32
	sub x10, x10, #1
	cbnz x10, 2311b
	movz x0, #26776, lsl #0
	add x0, x28, x0
	movz x1, #11, lsl #0
	movz x2, #29176, lsl #0
	add x2, x28, x2
	movz x3, #352, lsl #0
	bl {vg_mlkem1024_compress_encode}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x9, #3329, lsl #0
	movz x10, #55259, lsl #0
	movk x10, #9, lsl #16
	movk x10, #0, lsl #32
	movk x10, #0, lsl #48
	dup v16.4s, w9
	dup v17.4s, w10
	adrp x3, {VG_MLKEM_GAMMA}
	add x3, x3, {VG_MLKEM_GAMMA}
	movz x11, #16, lsl #0
	movz x12, #0, lsl #0
2312:
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movz x1, #6296, lsl #0
	add x1, x28, x1
	movz x2, #20632, lsl #0
	add x2, x28, x2
	add x1, x1, x12
	add x2, x2, x12
	ldr q0, [x1, #0]
	ldr q1, [x1, #16]
	ldr q4, [x2, #0]
	ldr q5, [x2, #16]
	uzp1 v6.8h, v0.8h, v1.8h
	uzp2 v7.8h, v0.8h, v1.8h
	uzp1 v19.8h, v4.8h, v5.8h
	uzp2 v20.8h, v4.8h, v5.8h
	umlal v21.4s, v6.4h, v19.4h
	umlal2 v25.4s, v6.8h, v19.8h
	umlal v22.4s, v7.4h, v20.4h
	umlal2 v26.4s, v7.8h, v20.8h
	umlal v23.4s, v6.4h, v20.4h
	umlal2 v27.4s, v6.8h, v20.8h
	umlal v23.4s, v7.4h, v19.4h
	umlal2 v27.4s, v7.8h, v19.8h
	movz x1, #10392, lsl #0
	add x1, x28, x1
	movz x2, #21656, lsl #0
	add x2, x28, x2
	add x1, x1, x12
	add x2, x2, x12
	ldr q0, [x1, #0]
	ldr q1, [x1, #16]
	ldr q4, [x2, #0]
	ldr q5, [x2, #16]
	uzp1 v6.8h, v0.8h, v1.8h
	uzp2 v7.8h, v0.8h, v1.8h
	uzp1 v19.8h, v4.8h, v5.8h
	uzp2 v20.8h, v4.8h, v5.8h
	umlal v21.4s, v6.4h, v19.4h
	umlal2 v25.4s, v6.8h, v19.8h
	umlal v22.4s, v7.4h, v20.4h
	umlal2 v26.4s, v7.8h, v20.8h
	umlal v23.4s, v6.4h, v20.4h
	umlal2 v27.4s, v6.8h, v20.8h
	umlal v23.4s, v7.4h, v19.4h
	umlal2 v27.4s, v7.8h, v19.8h
	movz x1, #14488, lsl #0
	add x1, x28, x1
	movz x2, #22680, lsl #0
	add x2, x28, x2
	add x1, x1, x12
	add x2, x2, x12
	ldr q0, [x1, #0]
	ldr q1, [x1, #16]
	ldr q4, [x2, #0]
	ldr q5, [x2, #16]
	uzp1 v6.8h, v0.8h, v1.8h
	uzp2 v7.8h, v0.8h, v1.8h
	uzp1 v19.8h, v4.8h, v5.8h
	uzp2 v20.8h, v4.8h, v5.8h
	umlal v21.4s, v6.4h, v19.4h
	umlal2 v25.4s, v6.8h, v19.8h
	umlal v22.4s, v7.4h, v20.4h
	umlal2 v26.4s, v7.8h, v20.8h
	umlal v23.4s, v6.4h, v20.4h
	umlal2 v27.4s, v6.8h, v20.8h
	umlal v23.4s, v7.4h, v19.4h
	umlal2 v27.4s, v7.8h, v19.8h
	movz x1, #18584, lsl #0
	add x1, x28, x1
	movz x2, #23704, lsl #0
	add x2, x28, x2
	add x1, x1, x12
	add x2, x2, x12
	ldr q0, [x1, #0]
	ldr q1, [x1, #16]
	ldr q4, [x2, #0]
	ldr q5, [x2, #16]
	uzp1 v6.8h, v0.8h, v1.8h
	uzp2 v7.8h, v0.8h, v1.8h
	uzp1 v19.8h, v4.8h, v5.8h
	uzp2 v20.8h, v4.8h, v5.8h
	umlal v21.4s, v6.4h, v19.4h
	umlal2 v25.4s, v6.8h, v19.8h
	umlal v22.4s, v7.4h, v20.4h
	umlal2 v26.4s, v7.8h, v20.8h
	umlal v23.4s, v6.4h, v20.4h
	umlal2 v27.4s, v6.8h, v20.8h
	umlal v23.4s, v7.4h, v19.4h
	umlal2 v27.4s, v7.8h, v19.8h
	ldr q18, [x3, #0]
	ldr q28, [x3, #16]
	sqdmulh v24.4s, v22.4s, v17.4s
	mls v22.4s, v24.4s, v16.4s
	mla v21.4s, v22.4s, v18.4s
	sqdmulh v24.4s, v21.4s, v17.4s
	mls v21.4s, v24.4s, v16.4s
	sub v24.4s, v21.4s, v16.4s
	umin v21.4s, v21.4s, v24.4s
	sqdmulh v24.4s, v23.4s, v17.4s
	mls v23.4s, v24.4s, v16.4s
	sub v24.4s, v23.4s, v16.4s
	umin v23.4s, v23.4s, v24.4s
	sqdmulh v24.4s, v26.4s, v17.4s
	mls v26.4s, v24.4s, v16.4s
	mla v25.4s, v26.4s, v28.4s
	sqdmulh v24.4s, v25.4s, v17.4s
	mls v25.4s, v24.4s, v16.4s
	sub v24.4s, v25.4s, v16.4s
	umin v25.4s, v25.4s, v24.4s
	sqdmulh v24.4s, v27.4s, v17.4s
	mls v27.4s, v24.4s, v16.4s
	sub v24.4s, v27.4s, v16.4s
	umin v27.4s, v27.4s, v24.4s
	uzp1 v0.8h, v21.8h, v25.8h
	uzp1 v1.8h, v23.8h, v27.8h
	zip1 v2.8h, v0.8h, v1.8h
	zip2 v3.8h, v0.8h, v1.8h
	str q2, [x0, #0]
	str q3, [x0, #16]
	add x0, x0, #32
	add x3, x3, #32
	add x12, x12, #32
	sub x11, x11, #1
	cbnz x11, 2312b
	movz x0, #25752, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem16_inv_ntt}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #47104, lsl #0
	add x1, x28, x1
	movz x9, #3329, lsl #0
	dup v16.8h, w9
	movz x11, #32, lsl #0
2313:
	ldr q0, [x0, #0]
	ldr q1, [x1, #0]
	add v2.8h, v0.8h, v1.8h
	cmhs v3.8h, v2.8h, v16.8h
	and v3.16b, v3.16b, v16.16b
	sub v2.8h, v2.8h, v3.8h
	str q2, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x11, x11, #1
	cbnz x11, 2313b
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #26776, lsl #0
	add x1, x28, x1
	movz x10, #32, lsl #0
	movi v29.2d, #0
2314:
	ldr q0, [x0, #0]
	zip1 v1.8h, v0.8h, v29.8h
	zip2 v2.8h, v0.8h, v29.8h
	str q1, [x1, #0]
	str q2, [x1, #16]
	add x0, x0, #16
	add x1, x1, #32
	sub x10, x10, #1
	cbnz x10, 2314b
	movz x0, #26776, lsl #0
	add x0, x28, x0
	movz x1, #11, lsl #0
	movz x2, #29528, lsl #0
	add x2, x28, x2
	movz x3, #352, lsl #0
	bl {vg_mlkem1024_compress_encode}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x9, #3329, lsl #0
	movz x10, #55259, lsl #0
	movk x10, #9, lsl #16
	movk x10, #0, lsl #32
	movk x10, #0, lsl #48
	dup v16.4s, w9
	dup v17.4s, w10
	adrp x3, {VG_MLKEM_GAMMA}
	add x3, x3, {VG_MLKEM_GAMMA}
	movz x11, #16, lsl #0
	movz x12, #0, lsl #0
2315:
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movz x1, #7320, lsl #0
	add x1, x28, x1
	movz x2, #20632, lsl #0
	add x2, x28, x2
	add x1, x1, x12
	add x2, x2, x12
	ldr q0, [x1, #0]
	ldr q1, [x1, #16]
	ldr q4, [x2, #0]
	ldr q5, [x2, #16]
	uzp1 v6.8h, v0.8h, v1.8h
	uzp2 v7.8h, v0.8h, v1.8h
	uzp1 v19.8h, v4.8h, v5.8h
	uzp2 v20.8h, v4.8h, v5.8h
	umlal v21.4s, v6.4h, v19.4h
	umlal2 v25.4s, v6.8h, v19.8h
	umlal v22.4s, v7.4h, v20.4h
	umlal2 v26.4s, v7.8h, v20.8h
	umlal v23.4s, v6.4h, v20.4h
	umlal2 v27.4s, v6.8h, v20.8h
	umlal v23.4s, v7.4h, v19.4h
	umlal2 v27.4s, v7.8h, v19.8h
	movz x1, #11416, lsl #0
	add x1, x28, x1
	movz x2, #21656, lsl #0
	add x2, x28, x2
	add x1, x1, x12
	add x2, x2, x12
	ldr q0, [x1, #0]
	ldr q1, [x1, #16]
	ldr q4, [x2, #0]
	ldr q5, [x2, #16]
	uzp1 v6.8h, v0.8h, v1.8h
	uzp2 v7.8h, v0.8h, v1.8h
	uzp1 v19.8h, v4.8h, v5.8h
	uzp2 v20.8h, v4.8h, v5.8h
	umlal v21.4s, v6.4h, v19.4h
	umlal2 v25.4s, v6.8h, v19.8h
	umlal v22.4s, v7.4h, v20.4h
	umlal2 v26.4s, v7.8h, v20.8h
	umlal v23.4s, v6.4h, v20.4h
	umlal2 v27.4s, v6.8h, v20.8h
	umlal v23.4s, v7.4h, v19.4h
	umlal2 v27.4s, v7.8h, v19.8h
	movz x1, #15512, lsl #0
	add x1, x28, x1
	movz x2, #22680, lsl #0
	add x2, x28, x2
	add x1, x1, x12
	add x2, x2, x12
	ldr q0, [x1, #0]
	ldr q1, [x1, #16]
	ldr q4, [x2, #0]
	ldr q5, [x2, #16]
	uzp1 v6.8h, v0.8h, v1.8h
	uzp2 v7.8h, v0.8h, v1.8h
	uzp1 v19.8h, v4.8h, v5.8h
	uzp2 v20.8h, v4.8h, v5.8h
	umlal v21.4s, v6.4h, v19.4h
	umlal2 v25.4s, v6.8h, v19.8h
	umlal v22.4s, v7.4h, v20.4h
	umlal2 v26.4s, v7.8h, v20.8h
	umlal v23.4s, v6.4h, v20.4h
	umlal2 v27.4s, v6.8h, v20.8h
	umlal v23.4s, v7.4h, v19.4h
	umlal2 v27.4s, v7.8h, v19.8h
	movz x1, #19608, lsl #0
	add x1, x28, x1
	movz x2, #23704, lsl #0
	add x2, x28, x2
	add x1, x1, x12
	add x2, x2, x12
	ldr q0, [x1, #0]
	ldr q1, [x1, #16]
	ldr q4, [x2, #0]
	ldr q5, [x2, #16]
	uzp1 v6.8h, v0.8h, v1.8h
	uzp2 v7.8h, v0.8h, v1.8h
	uzp1 v19.8h, v4.8h, v5.8h
	uzp2 v20.8h, v4.8h, v5.8h
	umlal v21.4s, v6.4h, v19.4h
	umlal2 v25.4s, v6.8h, v19.8h
	umlal v22.4s, v7.4h, v20.4h
	umlal2 v26.4s, v7.8h, v20.8h
	umlal v23.4s, v6.4h, v20.4h
	umlal2 v27.4s, v6.8h, v20.8h
	umlal v23.4s, v7.4h, v19.4h
	umlal2 v27.4s, v7.8h, v19.8h
	ldr q18, [x3, #0]
	ldr q28, [x3, #16]
	sqdmulh v24.4s, v22.4s, v17.4s
	mls v22.4s, v24.4s, v16.4s
	mla v21.4s, v22.4s, v18.4s
	sqdmulh v24.4s, v21.4s, v17.4s
	mls v21.4s, v24.4s, v16.4s
	sub v24.4s, v21.4s, v16.4s
	umin v21.4s, v21.4s, v24.4s
	sqdmulh v24.4s, v23.4s, v17.4s
	mls v23.4s, v24.4s, v16.4s
	sub v24.4s, v23.4s, v16.4s
	umin v23.4s, v23.4s, v24.4s
	sqdmulh v24.4s, v26.4s, v17.4s
	mls v26.4s, v24.4s, v16.4s
	mla v25.4s, v26.4s, v28.4s
	sqdmulh v24.4s, v25.4s, v17.4s
	mls v25.4s, v24.4s, v16.4s
	sub v24.4s, v25.4s, v16.4s
	umin v25.4s, v25.4s, v24.4s
	sqdmulh v24.4s, v27.4s, v17.4s
	mls v27.4s, v24.4s, v16.4s
	sub v24.4s, v27.4s, v16.4s
	umin v27.4s, v27.4s, v24.4s
	uzp1 v0.8h, v21.8h, v25.8h
	uzp1 v1.8h, v23.8h, v27.8h
	zip1 v2.8h, v0.8h, v1.8h
	zip2 v3.8h, v0.8h, v1.8h
	str q2, [x0, #0]
	str q3, [x0, #16]
	add x0, x0, #32
	add x3, x3, #32
	add x12, x12, #32
	sub x11, x11, #1
	cbnz x11, 2315b
	movz x0, #25752, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem16_inv_ntt}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #48128, lsl #0
	add x1, x28, x1
	movz x9, #3329, lsl #0
	dup v16.8h, w9
	movz x11, #32, lsl #0
2316:
	ldr q0, [x0, #0]
	ldr q1, [x1, #0]
	add v2.8h, v0.8h, v1.8h
	cmhs v3.8h, v2.8h, v16.8h
	and v3.16b, v3.16b, v16.16b
	sub v2.8h, v2.8h, v3.8h
	str q2, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x11, x11, #1
	cbnz x11, 2316b
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #26776, lsl #0
	add x1, x28, x1
	movz x10, #32, lsl #0
	movi v29.2d, #0
2317:
	ldr q0, [x0, #0]
	zip1 v1.8h, v0.8h, v29.8h
	zip2 v2.8h, v0.8h, v29.8h
	str q1, [x1, #0]
	str q2, [x1, #16]
	add x0, x0, #16
	add x1, x1, #32
	sub x10, x10, #1
	cbnz x10, 2317b
	movz x0, #26776, lsl #0
	add x0, x28, x0
	movz x1, #11, lsl #0
	movz x2, #29880, lsl #0
	add x2, x28, x2
	movz x3, #352, lsl #0
	bl {vg_mlkem1024_compress_encode}
	add x0, x25, #1536
	movz x1, #4248, lsl #0
	add x1, x28, x1
	movz x9, #256, lsl #0
	movk x9, #65282, lsl #16
	movk x9, #1027, lsl #32
	movk x9, #65285, lsl #48
	dup v16.2d, x9
	movz x9, #1798, lsl #0
	movk x9, #65288, lsl #16
	movk x9, #2569, lsl #32
	movk x9, #65291, lsl #48
	mov v16.d[1], x9
	movz x9, #4095, lsl #0
	dup v17.4s, w9
	movz x9, #3329, lsl #0
	dup v18.4s, w9
	movz x11, #32, lsl #0
2318:
	ldr x9, [x0, #0]
	ldr w10, [x0, #8]
	dup v0.2d, x9
	mov v0.d[1], x10
	tbl v1.16b, {v0.16b}, v16.16b
	and v2.16b, v1.16b, v17.16b
	ushr v3.4s, v1.4s, #12
	sub v4.4s, v2.4s, v18.4s
	umin v2.4s, v2.4s, v4.4s
	sub v4.4s, v3.4s, v18.4s
	umin v3.4s, v3.4s, v4.4s
	zip1 v0.4s, v2.4s, v3.4s
	zip2 v1.4s, v2.4s, v3.4s
	uzp1 v0.8h, v0.8h, v1.8h
	str q0, [x1, #0]
	add x0, x0, #12
	add x1, x1, #16
	sub x11, x11, #1
	cbnz x11, 2318b
	add x0, x25, #1920
	movz x1, #5272, lsl #0
	add x1, x28, x1
	movz x9, #256, lsl #0
	movk x9, #65282, lsl #16
	movk x9, #1027, lsl #32
	movk x9, #65285, lsl #48
	dup v16.2d, x9
	movz x9, #1798, lsl #0
	movk x9, #65288, lsl #16
	movk x9, #2569, lsl #32
	movk x9, #65291, lsl #48
	mov v16.d[1], x9
	movz x9, #4095, lsl #0
	dup v17.4s, w9
	movz x9, #3329, lsl #0
	dup v18.4s, w9
	movz x11, #32, lsl #0
2319:
	ldr x9, [x0, #0]
	ldr w10, [x0, #8]
	dup v0.2d, x9
	mov v0.d[1], x10
	tbl v1.16b, {v0.16b}, v16.16b
	and v2.16b, v1.16b, v17.16b
	ushr v3.4s, v1.4s, #12
	sub v4.4s, v2.4s, v18.4s
	umin v2.4s, v2.4s, v4.4s
	sub v4.4s, v3.4s, v18.4s
	umin v3.4s, v3.4s, v4.4s
	zip1 v0.4s, v2.4s, v3.4s
	zip2 v1.4s, v2.4s, v3.4s
	uzp1 v0.8h, v0.8h, v1.8h
	str q0, [x1, #0]
	add x0, x0, #12
	add x1, x1, #16
	sub x11, x11, #1
	cbnz x11, 2319b
	add x0, x25, #2304
	movz x1, #6296, lsl #0
	add x1, x28, x1
	movz x9, #256, lsl #0
	movk x9, #65282, lsl #16
	movk x9, #1027, lsl #32
	movk x9, #65285, lsl #48
	dup v16.2d, x9
	movz x9, #1798, lsl #0
	movk x9, #65288, lsl #16
	movk x9, #2569, lsl #32
	movk x9, #65291, lsl #48
	mov v16.d[1], x9
	movz x9, #4095, lsl #0
	dup v17.4s, w9
	movz x9, #3329, lsl #0
	dup v18.4s, w9
	movz x11, #32, lsl #0
2320:
	ldr x9, [x0, #0]
	ldr w10, [x0, #8]
	dup v0.2d, x9
	mov v0.d[1], x10
	tbl v1.16b, {v0.16b}, v16.16b
	and v2.16b, v1.16b, v17.16b
	ushr v3.4s, v1.4s, #12
	sub v4.4s, v2.4s, v18.4s
	umin v2.4s, v2.4s, v4.4s
	sub v4.4s, v3.4s, v18.4s
	umin v3.4s, v3.4s, v4.4s
	zip1 v0.4s, v2.4s, v3.4s
	zip2 v1.4s, v2.4s, v3.4s
	uzp1 v0.8h, v0.8h, v1.8h
	str q0, [x1, #0]
	add x0, x0, #12
	add x1, x1, #16
	sub x11, x11, #1
	cbnz x11, 2320b
	add x0, x25, #2688
	movz x1, #7320, lsl #0
	add x1, x28, x1
	movz x9, #256, lsl #0
	movk x9, #65282, lsl #16
	movk x9, #1027, lsl #32
	movk x9, #65285, lsl #48
	dup v16.2d, x9
	movz x9, #1798, lsl #0
	movk x9, #65288, lsl #16
	movk x9, #2569, lsl #32
	movk x9, #65291, lsl #48
	mov v16.d[1], x9
	movz x9, #4095, lsl #0
	dup v17.4s, w9
	movz x9, #3329, lsl #0
	dup v18.4s, w9
	movz x11, #32, lsl #0
2321:
	ldr x9, [x0, #0]
	ldr w10, [x0, #8]
	dup v0.2d, x9
	mov v0.d[1], x10
	tbl v1.16b, {v0.16b}, v16.16b
	and v2.16b, v1.16b, v17.16b
	ushr v3.4s, v1.4s, #12
	sub v4.4s, v2.4s, v18.4s
	umin v2.4s, v2.4s, v4.4s
	sub v4.4s, v3.4s, v18.4s
	umin v3.4s, v3.4s, v4.4s
	zip1 v0.4s, v2.4s, v3.4s
	zip2 v1.4s, v2.4s, v3.4s
	uzp1 v0.8h, v0.8h, v1.8h
	str q0, [x1, #0]
	add x0, x0, #12
	add x1, x1, #16
	sub x11, x11, #1
	cbnz x11, 2321b
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x9, #3329, lsl #0
	movz x10, #55259, lsl #0
	movk x10, #9, lsl #16
	movk x10, #0, lsl #32
	movk x10, #0, lsl #48
	dup v16.4s, w9
	dup v17.4s, w10
	adrp x3, {VG_MLKEM_GAMMA}
	add x3, x3, {VG_MLKEM_GAMMA}
	movz x11, #16, lsl #0
	movz x12, #0, lsl #0
2322:
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movz x1, #4248, lsl #0
	add x1, x28, x1
	movz x2, #20632, lsl #0
	add x2, x28, x2
	add x1, x1, x12
	add x2, x2, x12
	ldr q0, [x1, #0]
	ldr q1, [x1, #16]
	ldr q4, [x2, #0]
	ldr q5, [x2, #16]
	uzp1 v6.8h, v0.8h, v1.8h
	uzp2 v7.8h, v0.8h, v1.8h
	uzp1 v19.8h, v4.8h, v5.8h
	uzp2 v20.8h, v4.8h, v5.8h
	umlal v21.4s, v6.4h, v19.4h
	umlal2 v25.4s, v6.8h, v19.8h
	umlal v22.4s, v7.4h, v20.4h
	umlal2 v26.4s, v7.8h, v20.8h
	umlal v23.4s, v6.4h, v20.4h
	umlal2 v27.4s, v6.8h, v20.8h
	umlal v23.4s, v7.4h, v19.4h
	umlal2 v27.4s, v7.8h, v19.8h
	movz x1, #5272, lsl #0
	add x1, x28, x1
	movz x2, #21656, lsl #0
	add x2, x28, x2
	add x1, x1, x12
	add x2, x2, x12
	ldr q0, [x1, #0]
	ldr q1, [x1, #16]
	ldr q4, [x2, #0]
	ldr q5, [x2, #16]
	uzp1 v6.8h, v0.8h, v1.8h
	uzp2 v7.8h, v0.8h, v1.8h
	uzp1 v19.8h, v4.8h, v5.8h
	uzp2 v20.8h, v4.8h, v5.8h
	umlal v21.4s, v6.4h, v19.4h
	umlal2 v25.4s, v6.8h, v19.8h
	umlal v22.4s, v7.4h, v20.4h
	umlal2 v26.4s, v7.8h, v20.8h
	umlal v23.4s, v6.4h, v20.4h
	umlal2 v27.4s, v6.8h, v20.8h
	umlal v23.4s, v7.4h, v19.4h
	umlal2 v27.4s, v7.8h, v19.8h
	movz x1, #6296, lsl #0
	add x1, x28, x1
	movz x2, #22680, lsl #0
	add x2, x28, x2
	add x1, x1, x12
	add x2, x2, x12
	ldr q0, [x1, #0]
	ldr q1, [x1, #16]
	ldr q4, [x2, #0]
	ldr q5, [x2, #16]
	uzp1 v6.8h, v0.8h, v1.8h
	uzp2 v7.8h, v0.8h, v1.8h
	uzp1 v19.8h, v4.8h, v5.8h
	uzp2 v20.8h, v4.8h, v5.8h
	umlal v21.4s, v6.4h, v19.4h
	umlal2 v25.4s, v6.8h, v19.8h
	umlal v22.4s, v7.4h, v20.4h
	umlal2 v26.4s, v7.8h, v20.8h
	umlal v23.4s, v6.4h, v20.4h
	umlal2 v27.4s, v6.8h, v20.8h
	umlal v23.4s, v7.4h, v19.4h
	umlal2 v27.4s, v7.8h, v19.8h
	movz x1, #7320, lsl #0
	add x1, x28, x1
	movz x2, #23704, lsl #0
	add x2, x28, x2
	add x1, x1, x12
	add x2, x2, x12
	ldr q0, [x1, #0]
	ldr q1, [x1, #16]
	ldr q4, [x2, #0]
	ldr q5, [x2, #16]
	uzp1 v6.8h, v0.8h, v1.8h
	uzp2 v7.8h, v0.8h, v1.8h
	uzp1 v19.8h, v4.8h, v5.8h
	uzp2 v20.8h, v4.8h, v5.8h
	umlal v21.4s, v6.4h, v19.4h
	umlal2 v25.4s, v6.8h, v19.8h
	umlal v22.4s, v7.4h, v20.4h
	umlal2 v26.4s, v7.8h, v20.8h
	umlal v23.4s, v6.4h, v20.4h
	umlal2 v27.4s, v6.8h, v20.8h
	umlal v23.4s, v7.4h, v19.4h
	umlal2 v27.4s, v7.8h, v19.8h
	ldr q18, [x3, #0]
	ldr q28, [x3, #16]
	sqdmulh v24.4s, v22.4s, v17.4s
	mls v22.4s, v24.4s, v16.4s
	mla v21.4s, v22.4s, v18.4s
	sqdmulh v24.4s, v21.4s, v17.4s
	mls v21.4s, v24.4s, v16.4s
	sub v24.4s, v21.4s, v16.4s
	umin v21.4s, v21.4s, v24.4s
	sqdmulh v24.4s, v23.4s, v17.4s
	mls v23.4s, v24.4s, v16.4s
	sub v24.4s, v23.4s, v16.4s
	umin v23.4s, v23.4s, v24.4s
	sqdmulh v24.4s, v26.4s, v17.4s
	mls v26.4s, v24.4s, v16.4s
	mla v25.4s, v26.4s, v28.4s
	sqdmulh v24.4s, v25.4s, v17.4s
	mls v25.4s, v24.4s, v16.4s
	sub v24.4s, v25.4s, v16.4s
	umin v25.4s, v25.4s, v24.4s
	sqdmulh v24.4s, v27.4s, v17.4s
	mls v27.4s, v24.4s, v16.4s
	sub v24.4s, v27.4s, v16.4s
	umin v27.4s, v27.4s, v24.4s
	uzp1 v0.8h, v21.8h, v25.8h
	uzp1 v1.8h, v23.8h, v27.8h
	zip1 v2.8h, v0.8h, v1.8h
	zip2 v3.8h, v0.8h, v1.8h
	str q2, [x0, #0]
	str q3, [x0, #16]
	add x0, x0, #32
	add x3, x3, #32
	add x12, x12, #32
	sub x11, x11, #1
	cbnz x11, 2322b
	movz x0, #25752, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem16_inv_ntt}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #24728, lsl #0
	add x1, x28, x1
	movz x9, #3329, lsl #0
	dup v16.8h, w9
	movz x11, #32, lsl #0
2323:
	ldr q0, [x0, #0]
	ldr q1, [x1, #0]
	add v2.8h, v0.8h, v1.8h
	cmhs v3.8h, v2.8h, v16.8h
	and v3.16b, v3.16b, v16.16b
	sub v2.8h, v2.8h, v3.8h
	str q2, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x11, x11, #1
	cbnz x11, 2323b
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #26776, lsl #0
	add x1, x28, x1
	movz x10, #32, lsl #0
	movi v29.2d, #0
2324:
	ldr q0, [x0, #0]
	zip1 v1.8h, v0.8h, v29.8h
	zip2 v2.8h, v0.8h, v29.8h
	str q1, [x1, #0]
	str q2, [x1, #16]
	add x0, x0, #16
	add x1, x1, #32
	sub x10, x10, #1
	cbnz x10, 2324b
	add x0, x28, #912
	movz x1, #32, lsl #0
	movz x2, #1, lsl #0
	movz x3, #24728, lsl #0
	add x3, x28, x3
	bl {vg_mlkem_decode_decompress}
	movz x0, #26776, lsl #0
	add x0, x28, x0
	movz x1, #24728, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	movz x0, #26776, lsl #0
	add x0, x28, x0
	movz x1, #5, lsl #0
	movz x2, #30232, lsl #0
	add x2, x28, x2
	movz x3, #160, lsl #0
	bl {vg_mlkem1024_compress_encode}
	add x0, x26, #0
	movz x1, #28824, lsl #0
	add x1, x28, x1
	movz x2, #196, lsl #0
	movz x10, #0, lsl #0
2325:
	ldr x9, [x0, #0]
	ldr x11, [x1, #0]
	eor x9, x9, x11
	orr x10, x10, x9
	add x0, x0, #8
	add x1, x1, #8
	sub x2, x2, #1
	cbnz x2, 2325b
	movz x11, #0, lsl #0
	sub x11, x11, x10
	orr x10, x10, x11
	lsr x10, x10, #63
	sub x10, x10, #1
	ldr x12, [x28, #984]
	ldr x13, [x28, #1016]
	eor x12, x12, x13
	and x12, x12, x10
	eor x12, x12, x13
	str x12, [x27, #0]
	ldr x12, [x28, #992]
	ldr x13, [x28, #1024]
	eor x12, x12, x13
	and x12, x12, x10
	eor x12, x12, x13
	str x12, [x27, #8]
	ldr x12, [x28, #1000]
	ldr x13, [x28, #1032]
	eor x12, x12, x13
	and x12, x12, x10
	eor x12, x12, x13
	str x12, [x27, #16]
	ldr x12, [x28, #1008]
	ldr x13, [x28, #1040]
	eor x12, x12, x13
	and x12, x12, x10
	eor x12, x12, x13
	str x12, [x27, #24]
	add x0, x24, #0
	ldr x24, [x28, #30392]
	ldr x30, [x28, #30400]
	ldr x25, [x28, #30408]
	ldr x26, [x28, #30416]
	ldr x27, [x28, #30424]
	ldr x28, [x28, #30432]
	ret
	.p2align 6
