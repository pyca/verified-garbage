// The functions of `src/internal/vg_mlkem768_decaps_body_x2_sha3_keccak_sha3.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem768_decaps_body_x2_sha3_keccak_sha3:
	str x24, [x3, #21720]
	str x30, [x3, #21728]
	str x25, [x3, #21736]
	str x26, [x3, #21744]
	str x27, [x3, #21752]
	str x28, [x3, #21760]
	add x25, x0, #0
	add x26, x1, #0
	add x27, x2, #0
	add x28, x3, #0
	movz x24, #1, lsl #0
	add x0, x26, #0
	movz x1, #320, lsl #0
	movz x2, #10, lsl #0
	movz x3, #18584, lsl #0
	add x3, x28, x3
	bl {vg_mlkem_decode_decompress}
	movz x0, #18584, lsl #0
	add x0, x28, x0
	movz x1, #13464, lsl #0
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
	movz x0, #13464, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem16_ntt}
	add x0, x26, #320
	movz x1, #320, lsl #0
	movz x2, #10, lsl #0
	movz x3, #18584, lsl #0
	add x3, x28, x3
	bl {vg_mlkem_decode_decompress}
	movz x0, #18584, lsl #0
	add x0, x28, x0
	movz x1, #14488, lsl #0
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
	movz x0, #14488, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem16_ntt}
	add x0, x26, #640
	movz x1, #320, lsl #0
	movz x2, #10, lsl #0
	movz x3, #18584, lsl #0
	add x3, x28, x3
	bl {vg_mlkem_decode_decompress}
	movz x0, #18584, lsl #0
	add x0, x28, x0
	movz x1, #15512, lsl #0
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
	movz x0, #15512, lsl #0
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
23:
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
	cbnz x11, 23b
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
	movz x0, #17560, lsl #0
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
26:
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movz x1, #4248, lsl #0
	add x1, x28, x1
	movz x2, #13464, lsl #0
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
	movz x2, #14488, lsl #0
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
	movz x2, #15512, lsl #0
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
	cbnz x11, 26b
	movz x0, #17560, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem16_inv_ntt}
	movz x0, #17560, lsl #0
	add x0, x28, x0
	movz x1, #18584, lsl #0
	add x1, x28, x1
	movz x10, #32, lsl #0
	movi v29.2d, #0
27:
	ldr q0, [x0, #0]
	zip1 v1.8h, v0.8h, v29.8h
	zip2 v2.8h, v0.8h, v29.8h
	str q1, [x1, #0]
	str q2, [x1, #16]
	add x0, x0, #16
	add x1, x1, #32
	sub x10, x10, #1
	cbnz x10, 27b
	add x0, x26, #960
	movz x1, #128, lsl #0
	movz x2, #4, lsl #0
	movz x3, #16536, lsl #0
	add x3, x28, x3
	bl {vg_mlkem_decode_decompress}
	movz x0, #16536, lsl #0
	add x0, x28, x0
	movz x1, #18584, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_sub}
	movz x0, #16536, lsl #0
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
	add x2, x25, #2336
	ldr x9, [x2, #0]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	add x2, x25, #2344
	ldr x9, [x2, #0]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	add x2, x25, #2352
	ldr x9, [x2, #0]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	add x2, x25, #2360
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
	bl {vg_keccak_f1600_sha3}
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
	ldr x9, [x25, #2304]
	str x9, [x28, #840]
	ldr x9, [x25, #2312]
	str x9, [x28, #848]
	ldr x9, [x25, #2320]
	str x9, [x28, #856]
	ldr x9, [x25, #2328]
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
	ldr x9, [x25, #2368]
	str x9, [x28, #20600]
	ldr x9, [x25, #2376]
	str x9, [x28, #20608]
	ldr x9, [x25, #2384]
	str x9, [x28, #20616]
	ldr x9, [x25, #2392]
	str x9, [x28, #20624]
	ldr x9, [x26, #0]
	str x9, [x28, #20632]
	ldr x9, [x26, #8]
	str x9, [x28, #20640]
	ldr x9, [x26, #16]
	str x9, [x28, #20648]
	ldr x9, [x26, #24]
	str x9, [x28, #20656]
	ldr x9, [x26, #32]
	str x9, [x28, #20664]
	ldr x9, [x26, #40]
	str x9, [x28, #20672]
	ldr x9, [x26, #48]
	str x9, [x28, #20680]
	ldr x9, [x26, #56]
	str x9, [x28, #20688]
	ldr x9, [x26, #64]
	str x9, [x28, #20696]
	ldr x9, [x26, #72]
	str x9, [x28, #20704]
	ldr x9, [x26, #80]
	str x9, [x28, #20712]
	ldr x9, [x26, #88]
	str x9, [x28, #20720]
	ldr x9, [x26, #96]
	str x9, [x28, #20728]
	ldr x9, [x26, #104]
	str x9, [x28, #20736]
	ldr x9, [x26, #112]
	str x9, [x28, #20744]
	ldr x9, [x26, #120]
	str x9, [x28, #20752]
	ldr x9, [x26, #128]
	str x9, [x28, #20760]
	ldr x9, [x26, #136]
	str x9, [x28, #20768]
	ldr x9, [x26, #144]
	str x9, [x28, #20776]
	ldr x9, [x26, #152]
	str x9, [x28, #20784]
	ldr x9, [x26, #160]
	str x9, [x28, #20792]
	ldr x9, [x26, #168]
	str x9, [x28, #20800]
	ldr x9, [x26, #176]
	str x9, [x28, #20808]
	ldr x9, [x26, #184]
	str x9, [x28, #20816]
	ldr x9, [x26, #192]
	str x9, [x28, #20824]
	ldr x9, [x26, #200]
	str x9, [x28, #20832]
	ldr x9, [x26, #208]
	str x9, [x28, #20840]
	ldr x9, [x26, #216]
	str x9, [x28, #20848]
	ldr x9, [x26, #224]
	str x9, [x28, #20856]
	ldr x9, [x26, #232]
	str x9, [x28, #20864]
	ldr x9, [x26, #240]
	str x9, [x28, #20872]
	ldr x9, [x26, #248]
	str x9, [x28, #20880]
	ldr x9, [x26, #256]
	str x9, [x28, #20888]
	ldr x9, [x26, #264]
	str x9, [x28, #20896]
	ldr x9, [x26, #272]
	str x9, [x28, #20904]
	ldr x9, [x26, #280]
	str x9, [x28, #20912]
	ldr x9, [x26, #288]
	str x9, [x28, #20920]
	ldr x9, [x26, #296]
	str x9, [x28, #20928]
	ldr x9, [x26, #304]
	str x9, [x28, #20936]
	ldr x9, [x26, #312]
	str x9, [x28, #20944]
	ldr x9, [x26, #320]
	str x9, [x28, #20952]
	ldr x9, [x26, #328]
	str x9, [x28, #20960]
	ldr x9, [x26, #336]
	str x9, [x28, #20968]
	ldr x9, [x26, #344]
	str x9, [x28, #20976]
	ldr x9, [x26, #352]
	str x9, [x28, #20984]
	ldr x9, [x26, #360]
	str x9, [x28, #20992]
	ldr x9, [x26, #368]
	str x9, [x28, #21000]
	ldr x9, [x26, #376]
	str x9, [x28, #21008]
	ldr x9, [x26, #384]
	str x9, [x28, #21016]
	ldr x9, [x26, #392]
	str x9, [x28, #21024]
	ldr x9, [x26, #400]
	str x9, [x28, #21032]
	ldr x9, [x26, #408]
	str x9, [x28, #21040]
	ldr x9, [x26, #416]
	str x9, [x28, #21048]
	ldr x9, [x26, #424]
	str x9, [x28, #21056]
	ldr x9, [x26, #432]
	str x9, [x28, #21064]
	ldr x9, [x26, #440]
	str x9, [x28, #21072]
	ldr x9, [x26, #448]
	str x9, [x28, #21080]
	ldr x9, [x26, #456]
	str x9, [x28, #21088]
	ldr x9, [x26, #464]
	str x9, [x28, #21096]
	ldr x9, [x26, #472]
	str x9, [x28, #21104]
	ldr x9, [x26, #480]
	str x9, [x28, #21112]
	ldr x9, [x26, #488]
	str x9, [x28, #21120]
	ldr x9, [x26, #496]
	str x9, [x28, #21128]
	ldr x9, [x26, #504]
	str x9, [x28, #21136]
	ldr x9, [x26, #512]
	str x9, [x28, #21144]
	ldr x9, [x26, #520]
	str x9, [x28, #21152]
	ldr x9, [x26, #528]
	str x9, [x28, #21160]
	ldr x9, [x26, #536]
	str x9, [x28, #21168]
	ldr x9, [x26, #544]
	str x9, [x28, #21176]
	ldr x9, [x26, #552]
	str x9, [x28, #21184]
	ldr x9, [x26, #560]
	str x9, [x28, #21192]
	ldr x9, [x26, #568]
	str x9, [x28, #21200]
	ldr x9, [x26, #576]
	str x9, [x28, #21208]
	ldr x9, [x26, #584]
	str x9, [x28, #21216]
	ldr x9, [x26, #592]
	str x9, [x28, #21224]
	ldr x9, [x26, #600]
	str x9, [x28, #21232]
	ldr x9, [x26, #608]
	str x9, [x28, #21240]
	ldr x9, [x26, #616]
	str x9, [x28, #21248]
	ldr x9, [x26, #624]
	str x9, [x28, #21256]
	ldr x9, [x26, #632]
	str x9, [x28, #21264]
	ldr x9, [x26, #640]
	str x9, [x28, #21272]
	ldr x9, [x26, #648]
	str x9, [x28, #21280]
	ldr x9, [x26, #656]
	str x9, [x28, #21288]
	ldr x9, [x26, #664]
	str x9, [x28, #21296]
	ldr x9, [x26, #672]
	str x9, [x28, #21304]
	ldr x9, [x26, #680]
	str x9, [x28, #21312]
	ldr x9, [x26, #688]
	str x9, [x28, #21320]
	ldr x9, [x26, #696]
	str x9, [x28, #21328]
	ldr x9, [x26, #704]
	str x9, [x28, #21336]
	ldr x9, [x26, #712]
	str x9, [x28, #21344]
	ldr x9, [x26, #720]
	str x9, [x28, #21352]
	ldr x9, [x26, #728]
	str x9, [x28, #21360]
	ldr x9, [x26, #736]
	str x9, [x28, #21368]
	ldr x9, [x26, #744]
	str x9, [x28, #21376]
	ldr x9, [x26, #752]
	str x9, [x28, #21384]
	ldr x9, [x26, #760]
	str x9, [x28, #21392]
	ldr x9, [x26, #768]
	str x9, [x28, #21400]
	ldr x9, [x26, #776]
	str x9, [x28, #21408]
	ldr x9, [x26, #784]
	str x9, [x28, #21416]
	ldr x9, [x26, #792]
	str x9, [x28, #21424]
	ldr x9, [x26, #800]
	str x9, [x28, #21432]
	ldr x9, [x26, #808]
	str x9, [x28, #21440]
	ldr x9, [x26, #816]
	str x9, [x28, #21448]
	ldr x9, [x26, #824]
	str x9, [x28, #21456]
	ldr x9, [x26, #832]
	str x9, [x28, #21464]
	ldr x9, [x26, #840]
	str x9, [x28, #21472]
	ldr x9, [x26, #848]
	str x9, [x28, #21480]
	ldr x9, [x26, #856]
	str x9, [x28, #21488]
	ldr x9, [x26, #864]
	str x9, [x28, #21496]
	ldr x9, [x26, #872]
	str x9, [x28, #21504]
	ldr x9, [x26, #880]
	str x9, [x28, #21512]
	ldr x9, [x26, #888]
	str x9, [x28, #21520]
	ldr x9, [x26, #896]
	str x9, [x28, #21528]
	ldr x9, [x26, #904]
	str x9, [x28, #21536]
	ldr x9, [x26, #912]
	str x9, [x28, #21544]
	ldr x9, [x26, #920]
	str x9, [x28, #21552]
	ldr x9, [x26, #928]
	str x9, [x28, #21560]
	ldr x9, [x26, #936]
	str x9, [x28, #21568]
	ldr x9, [x26, #944]
	str x9, [x28, #21576]
	ldr x9, [x26, #952]
	str x9, [x28, #21584]
	ldr x9, [x26, #960]
	str x9, [x28, #21592]
	ldr x9, [x26, #968]
	str x9, [x28, #21600]
	ldr x9, [x26, #976]
	str x9, [x28, #21608]
	ldr x9, [x26, #984]
	str x9, [x28, #21616]
	ldr x9, [x26, #992]
	str x9, [x28, #21624]
	ldr x9, [x26, #1000]
	str x9, [x28, #21632]
	ldr x9, [x26, #1008]
	str x9, [x28, #21640]
	ldr x9, [x26, #1016]
	str x9, [x28, #21648]
	ldr x9, [x26, #1024]
	str x9, [x28, #21656]
	ldr x9, [x26, #1032]
	str x9, [x28, #21664]
	ldr x9, [x26, #1040]
	str x9, [x28, #21672]
	ldr x9, [x26, #1048]
	str x9, [x28, #21680]
	ldr x9, [x26, #1056]
	str x9, [x28, #21688]
	ldr x9, [x26, #1064]
	str x9, [x28, #21696]
	ldr x9, [x26, #1072]
	str x9, [x28, #21704]
	ldr x9, [x26, #1080]
	str x9, [x28, #21712]
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
	ldr x9, [x28, #20600]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	ldr x9, [x28, #20608]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	ldr x9, [x28, #20616]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	ldr x9, [x28, #20624]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	ldr x9, [x28, #20632]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	ldr x9, [x28, #20640]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	ldr x9, [x28, #20648]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	ldr x9, [x28, #20656]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldr x9, [x28, #20664]
	ldr x10, [x28, #64]
	eor x9, x9, x10
	str x9, [x28, #64]
	ldr x9, [x28, #20672]
	ldr x10, [x28, #72]
	eor x9, x9, x10
	str x9, [x28, #72]
	ldr x9, [x28, #20680]
	ldr x10, [x28, #80]
	eor x9, x9, x10
	str x9, [x28, #80]
	ldr x9, [x28, #20688]
	ldr x10, [x28, #88]
	eor x9, x9, x10
	str x9, [x28, #88]
	ldr x9, [x28, #20696]
	ldr x10, [x28, #96]
	eor x9, x9, x10
	str x9, [x28, #96]
	ldr x9, [x28, #20704]
	ldr x10, [x28, #104]
	eor x9, x9, x10
	str x9, [x28, #104]
	ldr x9, [x28, #20712]
	ldr x10, [x28, #112]
	eor x9, x9, x10
	str x9, [x28, #112]
	ldr x9, [x28, #20720]
	ldr x10, [x28, #120]
	eor x9, x9, x10
	str x9, [x28, #120]
	ldr x9, [x28, #20728]
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
	ldr x9, [x28, #20736]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	ldr x9, [x28, #20744]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	ldr x9, [x28, #20752]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	ldr x9, [x28, #20760]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	ldr x9, [x28, #20768]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	ldr x9, [x28, #20776]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	ldr x9, [x28, #20784]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	ldr x9, [x28, #20792]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldr x9, [x28, #20800]
	ldr x10, [x28, #64]
	eor x9, x9, x10
	str x9, [x28, #64]
	ldr x9, [x28, #20808]
	ldr x10, [x28, #72]
	eor x9, x9, x10
	str x9, [x28, #72]
	ldr x9, [x28, #20816]
	ldr x10, [x28, #80]
	eor x9, x9, x10
	str x9, [x28, #80]
	ldr x9, [x28, #20824]
	ldr x10, [x28, #88]
	eor x9, x9, x10
	str x9, [x28, #88]
	ldr x9, [x28, #20832]
	ldr x10, [x28, #96]
	eor x9, x9, x10
	str x9, [x28, #96]
	ldr x9, [x28, #20840]
	ldr x10, [x28, #104]
	eor x9, x9, x10
	str x9, [x28, #104]
	ldr x9, [x28, #20848]
	ldr x10, [x28, #112]
	eor x9, x9, x10
	str x9, [x28, #112]
	ldr x9, [x28, #20856]
	ldr x10, [x28, #120]
	eor x9, x9, x10
	str x9, [x28, #120]
	ldr x9, [x28, #20864]
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
	ldr x9, [x28, #20872]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	ldr x9, [x28, #20880]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	ldr x9, [x28, #20888]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	ldr x9, [x28, #20896]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	ldr x9, [x28, #20904]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	ldr x9, [x28, #20912]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	ldr x9, [x28, #20920]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	ldr x9, [x28, #20928]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldr x9, [x28, #20936]
	ldr x10, [x28, #64]
	eor x9, x9, x10
	str x9, [x28, #64]
	ldr x9, [x28, #20944]
	ldr x10, [x28, #72]
	eor x9, x9, x10
	str x9, [x28, #72]
	ldr x9, [x28, #20952]
	ldr x10, [x28, #80]
	eor x9, x9, x10
	str x9, [x28, #80]
	ldr x9, [x28, #20960]
	ldr x10, [x28, #88]
	eor x9, x9, x10
	str x9, [x28, #88]
	ldr x9, [x28, #20968]
	ldr x10, [x28, #96]
	eor x9, x9, x10
	str x9, [x28, #96]
	ldr x9, [x28, #20976]
	ldr x10, [x28, #104]
	eor x9, x9, x10
	str x9, [x28, #104]
	ldr x9, [x28, #20984]
	ldr x10, [x28, #112]
	eor x9, x9, x10
	str x9, [x28, #112]
	ldr x9, [x28, #20992]
	ldr x10, [x28, #120]
	eor x9, x9, x10
	str x9, [x28, #120]
	ldr x9, [x28, #21000]
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
28:
	add x2, x20, #0
	add x3, x21, #0
	movz x4, #256, lsl #0
	movz x5, #168, lsl #0
	movz x9, #3329, lsl #0
	movz x10, #15, lsl #0
29:
	sub x6, x4, #8
	lsr x6, x6, #63
	cbz x6, 210f
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
	cbz x4, 212f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 214f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 215f
214:
215:
	b 213f
212:
213:
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
	cbz x4, 216f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 218f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 219f
218:
219:
	b 217f
216:
217:
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
	cbz x4, 220f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 222f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 223f
222:
223:
	b 221f
220:
221:
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
	cbz x4, 224f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 226f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 227f
226:
227:
	b 225f
224:
225:
	cbz x4, 228f
	b 229f
228:
	movz x5, #0, lsl #0
229:
	b 211f
210:
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
211:
	cbnz x5, 29b
	cbz x4, 230f
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	b 231f
230:
231:
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
	cbnz x6, 28b
	add x6, x22, #0
	cbz x6, 232f
	b 233f
232:
	movz x30, #1, lsl #0
234:
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
235:
	ldr x3, [x1, #0]
	ldr x4, [x1, #8]
	cbz x4, 236f
	add x2, x20, #0
	movz x5, #56, lsl #0
	movz x9, #3329, lsl #0
	movz x10, #15, lsl #0
238:
	sub x6, x4, #8
	lsr x6, x6, #63
	cbz x6, 239f
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
	cbz x4, 241f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 243f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 244f
243:
244:
	b 242f
241:
242:
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
	cbz x4, 245f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 247f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 248f
247:
248:
	b 246f
245:
246:
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
	cbz x4, 249f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 251f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 252f
251:
252:
	b 250f
249:
250:
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
	cbz x4, 253f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 255f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 256f
255:
256:
	b 254f
253:
254:
	cbz x4, 257f
	b 258f
257:
	movz x5, #0, lsl #0
258:
	b 240f
239:
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
240:
	cbnz x5, 238b
	cbz x4, 259f
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	b 260f
259:
260:
	sub x0, x4, #1
	lsr x0, x0, #63
	str x3, [x1, #0]
	str x4, [x1, #8]
	b 237f
236:
	movz x0, #1, lsl #0
237:
	and x22, x22, x0
	add x20, x20, #504
	add x1, x1, #16
	sub x23, x23, #1
	cbnz x23, 235b
	add x6, x22, #0
	sub x7, x6, x30
	lsr x7, x7, #63
	movz x30, #0, lsl #0
	cbnz x7, 234b
	and x24, x24, x6
	ldr x3, [x19, #1680]
	ldr x4, [x19, #1688]
	cbz x4, 261f
263:
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	add x3, x3, #2
	sub x4, x4, #1
	cbnz x4, 263b
	b 262f
261:
262:
	ldr x3, [x19, #1696]
	ldr x4, [x19, #1704]
	cbz x4, 264f
266:
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	add x3, x3, #2
	sub x4, x4, #1
	cbnz x4, 266b
	b 265f
264:
265:
233:
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
	movz x7, #256, lsl #0
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
	ldr x9, [x28, #21008]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	ldr x9, [x28, #21016]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	ldr x9, [x28, #21024]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	ldr x9, [x28, #21032]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	ldr x9, [x28, #21040]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	ldr x9, [x28, #21048]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	ldr x9, [x28, #21056]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	ldr x9, [x28, #21064]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldr x9, [x28, #21072]
	ldr x10, [x28, #64]
	eor x9, x9, x10
	str x9, [x28, #64]
	ldr x9, [x28, #21080]
	ldr x10, [x28, #72]
	eor x9, x9, x10
	str x9, [x28, #72]
	ldr x9, [x28, #21088]
	ldr x10, [x28, #80]
	eor x9, x9, x10
	str x9, [x28, #80]
	ldr x9, [x28, #21096]
	ldr x10, [x28, #88]
	eor x9, x9, x10
	str x9, [x28, #88]
	ldr x9, [x28, #21104]
	ldr x10, [x28, #96]
	eor x9, x9, x10
	str x9, [x28, #96]
	ldr x9, [x28, #21112]
	ldr x10, [x28, #104]
	eor x9, x9, x10
	str x9, [x28, #104]
	ldr x9, [x28, #21120]
	ldr x10, [x28, #112]
	eor x9, x9, x10
	str x9, [x28, #112]
	ldr x9, [x28, #21128]
	ldr x10, [x28, #120]
	eor x9, x9, x10
	str x9, [x28, #120]
	ldr x9, [x28, #21136]
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
	ldr x9, [x28, #21144]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	ldr x9, [x28, #21152]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	ldr x9, [x28, #21160]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	ldr x9, [x28, #21168]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	ldr x9, [x28, #21176]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	ldr x9, [x28, #21184]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	ldr x9, [x28, #21192]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	ldr x9, [x28, #21200]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldr x9, [x28, #21208]
	ldr x10, [x28, #64]
	eor x9, x9, x10
	str x9, [x28, #64]
	ldr x9, [x28, #21216]
	ldr x10, [x28, #72]
	eor x9, x9, x10
	str x9, [x28, #72]
	ldr x9, [x28, #21224]
	ldr x10, [x28, #80]
	eor x9, x9, x10
	str x9, [x28, #80]
	ldr x9, [x28, #21232]
	ldr x10, [x28, #88]
	eor x9, x9, x10
	str x9, [x28, #88]
	ldr x9, [x28, #21240]
	ldr x10, [x28, #96]
	eor x9, x9, x10
	str x9, [x28, #96]
	ldr x9, [x28, #21248]
	ldr x10, [x28, #104]
	eor x9, x9, x10
	str x9, [x28, #104]
	ldr x9, [x28, #21256]
	ldr x10, [x28, #112]
	eor x9, x9, x10
	str x9, [x28, #112]
	ldr x9, [x28, #21264]
	ldr x10, [x28, #120]
	eor x9, x9, x10
	str x9, [x28, #120]
	ldr x9, [x28, #21272]
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
	ldr x9, [x28, #21280]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	ldr x9, [x28, #21288]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	ldr x9, [x28, #21296]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	ldr x9, [x28, #21304]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	ldr x9, [x28, #21312]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	ldr x9, [x28, #21320]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	ldr x9, [x28, #21328]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	ldr x9, [x28, #21336]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldr x9, [x28, #21344]
	ldr x10, [x28, #64]
	eor x9, x9, x10
	str x9, [x28, #64]
	ldr x9, [x28, #21352]
	ldr x10, [x28, #72]
	eor x9, x9, x10
	str x9, [x28, #72]
	ldr x9, [x28, #21360]
	ldr x10, [x28, #80]
	eor x9, x9, x10
	str x9, [x28, #80]
	ldr x9, [x28, #21368]
	ldr x10, [x28, #88]
	eor x9, x9, x10
	str x9, [x28, #88]
	ldr x9, [x28, #21376]
	ldr x10, [x28, #96]
	eor x9, x9, x10
	str x9, [x28, #96]
	ldr x9, [x28, #21384]
	ldr x10, [x28, #104]
	eor x9, x9, x10
	str x9, [x28, #104]
	ldr x9, [x28, #21392]
	ldr x10, [x28, #112]
	eor x9, x9, x10
	str x9, [x28, #112]
	ldr x9, [x28, #21400]
	ldr x10, [x28, #120]
	eor x9, x9, x10
	str x9, [x28, #120]
	ldr x9, [x28, #21408]
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
267:
	add x2, x20, #0
	add x3, x21, #0
	movz x4, #256, lsl #0
	movz x5, #168, lsl #0
	movz x9, #3329, lsl #0
	movz x10, #15, lsl #0
268:
	sub x6, x4, #8
	lsr x6, x6, #63
	cbz x6, 269f
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
	cbz x4, 271f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 273f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 274f
273:
274:
	b 272f
271:
272:
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
	cbz x4, 275f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 277f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 278f
277:
278:
	b 276f
275:
276:
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
	cbz x4, 279f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 281f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 282f
281:
282:
	b 280f
279:
280:
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
	cbz x4, 283f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 285f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 286f
285:
286:
	b 284f
283:
284:
	cbz x4, 287f
	b 288f
287:
	movz x5, #0, lsl #0
288:
	b 270f
269:
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
270:
	cbnz x5, 268b
	cbz x4, 289f
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	b 290f
289:
290:
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
	cbnz x6, 267b
	add x6, x22, #0
	cbz x6, 291f
	b 292f
291:
	movz x30, #1, lsl #0
293:
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
294:
	ldr x3, [x1, #0]
	ldr x4, [x1, #8]
	cbz x4, 295f
	add x2, x20, #0
	movz x5, #56, lsl #0
	movz x9, #3329, lsl #0
	movz x10, #15, lsl #0
297:
	sub x6, x4, #8
	lsr x6, x6, #63
	cbz x6, 298f
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
	cbz x4, 2100f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2102f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2103f
2102:
2103:
	b 2101f
2100:
2101:
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
	cbz x4, 2104f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2106f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2107f
2106:
2107:
	b 2105f
2104:
2105:
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
	cbz x4, 2108f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2110f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2111f
2110:
2111:
	b 2109f
2108:
2109:
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
	cbz x4, 2112f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2114f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2115f
2114:
2115:
	b 2113f
2112:
2113:
	cbz x4, 2116f
	b 2117f
2116:
	movz x5, #0, lsl #0
2117:
	b 299f
298:
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
299:
	cbnz x5, 297b
	cbz x4, 2118f
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	b 2119f
2118:
2119:
	sub x0, x4, #1
	lsr x0, x0, #63
	str x3, [x1, #0]
	str x4, [x1, #8]
	b 296f
295:
	movz x0, #1, lsl #0
296:
	and x22, x22, x0
	add x20, x20, #504
	add x1, x1, #16
	sub x23, x23, #1
	cbnz x23, 294b
	add x6, x22, #0
	sub x7, x6, x30
	lsr x7, x7, #63
	movz x30, #0, lsl #0
	cbnz x7, 293b
	and x24, x24, x6
	ldr x3, [x19, #1680]
	ldr x4, [x19, #1688]
	cbz x4, 2120f
2122:
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	add x3, x3, #2
	sub x4, x4, #1
	cbnz x4, 2122b
	b 2121f
2120:
2121:
	ldr x3, [x19, #1696]
	ldr x4, [x19, #1704]
	cbz x4, 2123f
2125:
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	add x3, x3, #2
	sub x4, x4, #1
	cbnz x4, 2125b
	b 2124f
2123:
2124:
292:
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
	movz x6, #257, lsl #0
	movk x6, #31, lsl #16
	movz x7, #258, lsl #0
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
	ldr x9, [x28, #21416]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	ldr x9, [x28, #21424]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	ldr x9, [x28, #21432]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	ldr x9, [x28, #21440]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	ldr x9, [x28, #21448]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	ldr x9, [x28, #21456]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	ldr x9, [x28, #21464]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	ldr x9, [x28, #21472]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldr x9, [x28, #21480]
	ldr x10, [x28, #64]
	eor x9, x9, x10
	str x9, [x28, #64]
	ldr x9, [x28, #21488]
	ldr x10, [x28, #72]
	eor x9, x9, x10
	str x9, [x28, #72]
	ldr x9, [x28, #21496]
	ldr x10, [x28, #80]
	eor x9, x9, x10
	str x9, [x28, #80]
	ldr x9, [x28, #21504]
	ldr x10, [x28, #88]
	eor x9, x9, x10
	str x9, [x28, #88]
	ldr x9, [x28, #21512]
	ldr x10, [x28, #96]
	eor x9, x9, x10
	str x9, [x28, #96]
	ldr x9, [x28, #21520]
	ldr x10, [x28, #104]
	eor x9, x9, x10
	str x9, [x28, #104]
	ldr x9, [x28, #21528]
	ldr x10, [x28, #112]
	eor x9, x9, x10
	str x9, [x28, #112]
	ldr x9, [x28, #21536]
	ldr x10, [x28, #120]
	eor x9, x9, x10
	str x9, [x28, #120]
	ldr x9, [x28, #21544]
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
	ldr x9, [x28, #21552]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	ldr x9, [x28, #21560]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	ldr x9, [x28, #21568]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	ldr x9, [x28, #21576]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	ldr x9, [x28, #21584]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	ldr x9, [x28, #21592]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	ldr x9, [x28, #21600]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	ldr x9, [x28, #21608]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldr x9, [x28, #21616]
	ldr x10, [x28, #64]
	eor x9, x9, x10
	str x9, [x28, #64]
	ldr x9, [x28, #21624]
	ldr x10, [x28, #72]
	eor x9, x9, x10
	str x9, [x28, #72]
	ldr x9, [x28, #21632]
	ldr x10, [x28, #80]
	eor x9, x9, x10
	str x9, [x28, #80]
	ldr x9, [x28, #21640]
	ldr x10, [x28, #88]
	eor x9, x9, x10
	str x9, [x28, #88]
	ldr x9, [x28, #21648]
	ldr x10, [x28, #96]
	eor x9, x9, x10
	str x9, [x28, #96]
	ldr x9, [x28, #21656]
	ldr x10, [x28, #104]
	eor x9, x9, x10
	str x9, [x28, #104]
	ldr x9, [x28, #21664]
	ldr x10, [x28, #112]
	eor x9, x9, x10
	str x9, [x28, #112]
	ldr x9, [x28, #21672]
	ldr x10, [x28, #120]
	eor x9, x9, x10
	str x9, [x28, #120]
	ldr x9, [x28, #21680]
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
	ldr x9, [x28, #21688]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	ldr x9, [x28, #21696]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	ldr x9, [x28, #21704]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	ldr x9, [x28, #21712]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	ldrb w9, [x28, #32]
	movz x10, #31, lsl #0
	eor x9, x9, x10
	strb w9, [x28, #32]
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
	movz x21, #8344, lsl #0
	add x21, x28, x21
	movz x23, #9368, lsl #0
	add x23, x28, x23
	add x20, x19, #400
	add x1, x19, #1680
	movz x22, #1, lsl #0
2126:
	add x2, x20, #0
	add x3, x21, #0
	movz x4, #256, lsl #0
	movz x5, #168, lsl #0
	movz x9, #3329, lsl #0
	movz x10, #15, lsl #0
2127:
	sub x6, x4, #8
	lsr x6, x6, #63
	cbz x6, 2128f
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
	cbz x4, 2130f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2132f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2133f
2132:
2133:
	b 2131f
2130:
2131:
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
	cbz x4, 2134f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2136f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2137f
2136:
2137:
	b 2135f
2134:
2135:
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
	cbz x4, 2138f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2140f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2141f
2140:
2141:
	b 2139f
2138:
2139:
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
	cbz x4, 2142f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2144f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2145f
2144:
2145:
	b 2143f
2142:
2143:
	cbz x4, 2146f
	b 2147f
2146:
	movz x5, #0, lsl #0
2147:
	b 2129f
2128:
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
2129:
	cbnz x5, 2127b
	cbz x4, 2148f
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	b 2149f
2148:
2149:
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
	cbnz x6, 2126b
	add x6, x22, #0
	cbz x6, 2150f
	b 2151f
2150:
	movz x30, #1, lsl #0
2152:
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
2153:
	ldr x3, [x1, #0]
	ldr x4, [x1, #8]
	cbz x4, 2154f
	add x2, x20, #0
	movz x5, #56, lsl #0
	movz x9, #3329, lsl #0
	movz x10, #15, lsl #0
2156:
	sub x6, x4, #8
	lsr x6, x6, #63
	cbz x6, 2157f
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
	cbz x4, 2159f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2161f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2162f
2161:
2162:
	b 2160f
2159:
2160:
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
	cbz x4, 2163f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2165f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2166f
2165:
2166:
	b 2164f
2163:
2164:
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
	cbz x4, 2167f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2169f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2170f
2169:
2170:
	b 2168f
2167:
2168:
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
	cbz x4, 2171f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2173f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2174f
2173:
2174:
	b 2172f
2171:
2172:
	cbz x4, 2175f
	b 2176f
2175:
	movz x5, #0, lsl #0
2176:
	b 2158f
2157:
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
2158:
	cbnz x5, 2156b
	cbz x4, 2177f
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	b 2178f
2177:
2178:
	sub x0, x4, #1
	lsr x0, x0, #63
	str x3, [x1, #0]
	str x4, [x1, #8]
	b 2155f
2154:
	movz x0, #1, lsl #0
2155:
	and x22, x22, x0
	add x20, x20, #504
	add x1, x1, #16
	sub x23, x23, #1
	cbnz x23, 2153b
	add x6, x22, #0
	sub x7, x6, x30
	lsr x7, x7, #63
	movz x30, #0, lsl #0
	cbnz x7, 2152b
	and x24, x24, x6
	ldr x3, [x19, #1680]
	ldr x4, [x19, #1688]
	cbz x4, 2179f
2181:
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	add x3, x3, #2
	sub x4, x4, #1
	cbnz x4, 2181b
	b 2180f
2179:
2180:
	ldr x3, [x19, #1696]
	ldr x4, [x19, #1704]
	cbz x4, 2182f
2184:
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	add x3, x3, #2
	sub x4, x4, #1
	cbnz x4, 2184b
	b 2183f
2182:
2183:
2151:
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
	bl {vg_mlkem768_pair_prf_840_1176_4248_944_17560_6_0_3}
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
	movz x6, #514, lsl #0
	movk x6, #31, lsl #16
	movz x7, #514, lsl #0
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
	movz x21, #18064, lsl #0
	add x21, x28, x21
	ldr x9, [x28, #944]
	str x9, [x19, #8]
	ldr x9, [x28, #952]
	str x9, [x19, #24]
	ldr x9, [x28, #960]
	str x9, [x19, #40]
	ldr x9, [x28, #968]
	str x9, [x19, #56]
	movz x9, #7939, lsl #0
	str x9, [x19, #72]
	movz x9, #0, lsl #0
	str x9, [x19, #88]
	movz x9, #0, lsl #0
	str x9, [x19, #104]
	movz x9, #0, lsl #0
	str x9, [x19, #120]
	movz x9, #0, lsl #0
	str x9, [x19, #136]
	movz x9, #0, lsl #0
	str x9, [x19, #152]
	movz x9, #0, lsl #0
	str x9, [x19, #168]
	movz x9, #0, lsl #0
	str x9, [x19, #184]
	movz x9, #0, lsl #0
	str x9, [x19, #200]
	movz x9, #0, lsl #0
	str x9, [x19, #216]
	movz x9, #0, lsl #0
	str x9, [x19, #232]
	movz x9, #0, lsl #0
	str x9, [x19, #248]
	movz x9, #32768, lsl #48
	str x9, [x19, #264]
	movz x9, #0, lsl #0
	str x9, [x19, #280]
	movz x9, #0, lsl #0
	str x9, [x19, #296]
	movz x9, #0, lsl #0
	str x9, [x19, #312]
	movz x9, #0, lsl #0
	str x9, [x19, #328]
	movz x9, #0, lsl #0
	str x9, [x19, #344]
	movz x9, #0, lsl #0
	str x9, [x19, #360]
	movz x9, #0, lsl #0
	str x9, [x19, #376]
	movz x9, #0, lsl #0
	str x9, [x19, #392]
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
	ldr x9, [x28, #944]
	str x9, [x19, #8]
	ldr x9, [x28, #952]
	str x9, [x19, #24]
	ldr x9, [x28, #960]
	str x9, [x19, #40]
	ldr x9, [x28, #968]
	str x9, [x19, #56]
	movz x9, #7940, lsl #0
	str x9, [x19, #72]
	movz x9, #0, lsl #0
	str x9, [x19, #88]
	movz x9, #0, lsl #0
	str x9, [x19, #104]
	movz x9, #0, lsl #0
	str x9, [x19, #120]
	movz x9, #0, lsl #0
	str x9, [x19, #136]
	movz x9, #0, lsl #0
	str x9, [x19, #152]
	movz x9, #0, lsl #0
	str x9, [x19, #168]
	movz x9, #0, lsl #0
	str x9, [x19, #184]
	movz x9, #0, lsl #0
	str x9, [x19, #200]
	movz x9, #0, lsl #0
	str x9, [x19, #216]
	movz x9, #0, lsl #0
	str x9, [x19, #232]
	movz x9, #0, lsl #0
	str x9, [x19, #248]
	movz x9, #32768, lsl #48
	str x9, [x19, #264]
	movz x9, #0, lsl #0
	str x9, [x19, #280]
	movz x9, #0, lsl #0
	str x9, [x19, #296]
	movz x9, #0, lsl #0
	str x9, [x19, #312]
	movz x9, #0, lsl #0
	str x9, [x19, #328]
	movz x9, #0, lsl #0
	str x9, [x19, #344]
	movz x9, #0, lsl #0
	str x9, [x19, #360]
	movz x9, #0, lsl #0
	str x9, [x19, #376]
	movz x9, #0, lsl #0
	str x9, [x19, #392]
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
	ldr x9, [x28, #944]
	str x9, [x19, #8]
	ldr x9, [x28, #952]
	str x9, [x19, #24]
	ldr x9, [x28, #960]
	str x9, [x19, #40]
	ldr x9, [x28, #968]
	str x9, [x19, #56]
	movz x9, #7941, lsl #0
	str x9, [x19, #72]
	movz x9, #0, lsl #0
	str x9, [x19, #88]
	movz x9, #0, lsl #0
	str x9, [x19, #104]
	movz x9, #0, lsl #0
	str x9, [x19, #120]
	movz x9, #0, lsl #0
	str x9, [x19, #136]
	movz x9, #0, lsl #0
	str x9, [x19, #152]
	movz x9, #0, lsl #0
	str x9, [x19, #168]
	movz x9, #0, lsl #0
	str x9, [x19, #184]
	movz x9, #0, lsl #0
	str x9, [x19, #200]
	movz x9, #0, lsl #0
	str x9, [x19, #216]
	movz x9, #0, lsl #0
	str x9, [x19, #232]
	movz x9, #0, lsl #0
	str x9, [x19, #248]
	movz x9, #32768, lsl #48
	str x9, [x19, #264]
	movz x9, #0, lsl #0
	str x9, [x19, #280]
	movz x9, #0, lsl #0
	str x9, [x19, #296]
	movz x9, #0, lsl #0
	str x9, [x19, #312]
	movz x9, #0, lsl #0
	str x9, [x19, #328]
	movz x9, #0, lsl #0
	str x9, [x19, #344]
	movz x9, #0, lsl #0
	str x9, [x19, #360]
	movz x9, #0, lsl #0
	str x9, [x19, #376]
	movz x9, #0, lsl #0
	str x9, [x19, #392]
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
	movz x3, #12440, lsl #0
	add x3, x28, x3
	add x2, x19, #400
	movz x4, #256, lsl #0
	movz x5, #168, lsl #0
	movz x9, #3329, lsl #0
	movz x10, #15, lsl #0
2185:
	sub x6, x4, #8
	lsr x6, x6, #63
	cbz x6, 2186f
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
	cbz x4, 2188f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2190f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2191f
2190:
2191:
	b 2189f
2188:
2189:
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
	cbz x4, 2192f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2194f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2195f
2194:
2195:
	b 2193f
2192:
2193:
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
	cbz x4, 2196f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2198f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2199f
2198:
2199:
	b 2197f
2196:
2197:
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
	cbz x4, 2200f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2202f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2203f
2202:
2203:
	b 2201f
2200:
2201:
	cbz x4, 2204f
	b 2205f
2204:
	movz x5, #0, lsl #0
2205:
	b 2187f
2186:
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
2187:
	cbnz x5, 2185b
	cbz x4, 2206f
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	b 2207f
2206:
2207:
	sub x0, x4, #1
	lsr x0, x0, #63
	add x22, x0, #0
	cbz x22, 2208f
	b 2209f
2208:
	str x22, [x19, #1848]
	str x23, [x19, #1856]
	add x2, x28, #1176
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
	movz x6, #514, lsl #0
	movk x6, #31, lsl #16
	movz x7, #514, lsl #0
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
	movz x22, #5, lsl #0
2210:
	add x1, x19, #768
	add x1, x1, #768
	str x30, [x1, #128]
	add x0, x19, #0
	bl {vg_keccak_f1600_x2_sha3}
	ldr x30, [x1, #128]
	ldr x6, [x19, #0]
	str x6, [x20, #0]
	ldr x6, [x19, #16]
	str x6, [x20, #8]
	ldr x6, [x19, #32]
	str x6, [x20, #16]
	ldr x6, [x19, #48]
	str x6, [x20, #24]
	ldr x6, [x19, #64]
	str x6, [x20, #32]
	ldr x6, [x19, #80]
	str x6, [x20, #40]
	ldr x6, [x19, #96]
	str x6, [x20, #48]
	ldr x6, [x19, #112]
	str x6, [x20, #56]
	ldr x6, [x19, #128]
	str x6, [x20, #64]
	ldr x6, [x19, #144]
	str x6, [x20, #72]
	ldr x6, [x19, #160]
	str x6, [x20, #80]
	ldr x6, [x19, #176]
	str x6, [x20, #88]
	ldr x6, [x19, #192]
	str x6, [x20, #96]
	ldr x6, [x19, #208]
	str x6, [x20, #104]
	ldr x6, [x19, #224]
	str x6, [x20, #112]
	ldr x6, [x19, #240]
	str x6, [x20, #120]
	ldr x6, [x19, #256]
	str x6, [x20, #128]
	ldr x6, [x19, #272]
	str x6, [x20, #136]
	ldr x6, [x19, #288]
	str x6, [x20, #144]
	ldr x6, [x19, #304]
	str x6, [x20, #152]
	ldr x6, [x19, #320]
	str x6, [x20, #160]
	add x20, x20, #168
	sub x22, x22, #1
	cbnz x22, 2210b
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
	movz x9, #0, lsl #0
	str x9, [x19, #1240]
	movz x3, #12440, lsl #0
	add x3, x28, x3
	add x2, x19, #400
	movz x4, #256, lsl #0
	movz x5, #280, lsl #0
	movz x9, #3329, lsl #0
	movz x10, #15, lsl #0
2211:
	sub x6, x4, #8
	lsr x6, x6, #63
	cbz x6, 2212f
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
	cbz x4, 2214f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2216f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2217f
2216:
2217:
	b 2215f
2214:
2215:
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
	cbz x4, 2218f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2220f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2221f
2220:
2221:
	b 2219f
2218:
2219:
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
	cbz x4, 2222f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2224f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2225f
2224:
2225:
	b 2223f
2222:
2223:
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
	cbz x4, 2226f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2228f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2229f
2228:
2229:
	b 2227f
2226:
2227:
	cbz x4, 2230f
	b 2231f
2230:
	movz x5, #0, lsl #0
2231:
	b 2213f
2212:
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
2213:
	cbnz x5, 2211b
	cbz x4, 2232f
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	b 2233f
2232:
2233:
	sub x0, x4, #1
	lsr x0, x0, #63
	and x24, x24, x0
	cbz x4, 2234f
2236:
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	add x3, x3, #2
	sub x4, x4, #1
	cbnz x4, 2236b
	b 2235f
2234:
2235:
	ldr x22, [x19, #1848]
	ldr x23, [x19, #1856]
2209:
	ldr x30, [x19, #1840]
	ldr x23, [x19, #1832]
	ldr x22, [x19, #1824]
	ldr x21, [x19, #1816]
	ldr x20, [x19, #1808]
	ldr x19, [x19, #1800]
	movz x0, #17560, lsl #0
	add x0, x28, x0
	movz x1, #13464, lsl #0
	add x1, x28, x1
	bl {vg_mlkem16_cbd2}
	movz x0, #13464, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem16_ntt}
	movz x0, #17728, lsl #0
	add x0, x28, x0
	movz x1, #14488, lsl #0
	add x1, x28, x1
	bl {vg_mlkem16_cbd2}
	movz x0, #14488, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem16_ntt}
	movz x0, #17896, lsl #0
	add x0, x28, x0
	movz x1, #15512, lsl #0
	add x1, x28, x1
	bl {vg_mlkem16_cbd2}
	movz x0, #15512, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem16_ntt}
	movz x0, #18064, lsl #0
	add x0, x28, x0
	movz x1, #29696, lsl #0
	add x1, x28, x1
	bl {vg_mlkem16_cbd2}
	movz x0, #18232, lsl #0
	add x0, x28, x0
	movz x1, #30720, lsl #0
	add x1, x28, x1
	bl {vg_mlkem16_cbd2}
	movz x0, #18400, lsl #0
	add x0, x28, x0
	movz x1, #31744, lsl #0
	add x1, x28, x1
	bl {vg_mlkem16_cbd2}
	movz x0, #17560, lsl #0
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
2237:
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movz x1, #4248, lsl #0
	add x1, x28, x1
	movz x2, #13464, lsl #0
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
	movz x2, #14488, lsl #0
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
	movz x2, #15512, lsl #0
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
	cbnz x11, 2237b
	movz x0, #17560, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem16_inv_ntt}
	movz x0, #17560, lsl #0
	add x0, x28, x0
	movz x1, #29696, lsl #0
	add x1, x28, x1
	movz x9, #3329, lsl #0
	dup v16.8h, w9
	movz x11, #32, lsl #0
2238:
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
	cbnz x11, 2238b
	movz x0, #17560, lsl #0
	add x0, x28, x0
	movz x1, #18584, lsl #0
	add x1, x28, x1
	movz x10, #32, lsl #0
	movi v29.2d, #0
2239:
	ldr q0, [x0, #0]
	zip1 v1.8h, v0.8h, v29.8h
	zip2 v2.8h, v0.8h, v29.8h
	str q1, [x1, #0]
	str q2, [x1, #16]
	add x0, x0, #16
	add x1, x1, #32
	sub x10, x10, #1
	cbnz x10, 2239b
	movz x0, #18584, lsl #0
	add x0, x28, x0
	movz x1, #10, lsl #0
	movz x2, #20632, lsl #0
	add x2, x28, x2
	movz x3, #320, lsl #0
	bl {vg_mlkem_compress_encode}
	movz x0, #17560, lsl #0
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
2240:
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movz x1, #5272, lsl #0
	add x1, x28, x1
	movz x2, #13464, lsl #0
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
	movz x2, #14488, lsl #0
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
	movz x2, #15512, lsl #0
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
	cbnz x11, 2240b
	movz x0, #17560, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem16_inv_ntt}
	movz x0, #17560, lsl #0
	add x0, x28, x0
	movz x1, #30720, lsl #0
	add x1, x28, x1
	movz x9, #3329, lsl #0
	dup v16.8h, w9
	movz x11, #32, lsl #0
2241:
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
	cbnz x11, 2241b
	movz x0, #17560, lsl #0
	add x0, x28, x0
	movz x1, #18584, lsl #0
	add x1, x28, x1
	movz x10, #32, lsl #0
	movi v29.2d, #0
2242:
	ldr q0, [x0, #0]
	zip1 v1.8h, v0.8h, v29.8h
	zip2 v2.8h, v0.8h, v29.8h
	str q1, [x1, #0]
	str q2, [x1, #16]
	add x0, x0, #16
	add x1, x1, #32
	sub x10, x10, #1
	cbnz x10, 2242b
	movz x0, #18584, lsl #0
	add x0, x28, x0
	movz x1, #10, lsl #0
	movz x2, #20952, lsl #0
	add x2, x28, x2
	movz x3, #320, lsl #0
	bl {vg_mlkem_compress_encode}
	movz x0, #17560, lsl #0
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
2243:
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movz x1, #6296, lsl #0
	add x1, x28, x1
	movz x2, #13464, lsl #0
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
	movz x2, #14488, lsl #0
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
	movz x2, #15512, lsl #0
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
	cbnz x11, 2243b
	movz x0, #17560, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem16_inv_ntt}
	movz x0, #17560, lsl #0
	add x0, x28, x0
	movz x1, #31744, lsl #0
	add x1, x28, x1
	movz x9, #3329, lsl #0
	dup v16.8h, w9
	movz x11, #32, lsl #0
2244:
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
	cbnz x11, 2244b
	movz x0, #17560, lsl #0
	add x0, x28, x0
	movz x1, #18584, lsl #0
	add x1, x28, x1
	movz x10, #32, lsl #0
	movi v29.2d, #0
2245:
	ldr q0, [x0, #0]
	zip1 v1.8h, v0.8h, v29.8h
	zip2 v2.8h, v0.8h, v29.8h
	str q1, [x1, #0]
	str q2, [x1, #16]
	add x0, x0, #16
	add x1, x1, #32
	sub x10, x10, #1
	cbnz x10, 2245b
	movz x0, #18584, lsl #0
	add x0, x28, x0
	movz x1, #10, lsl #0
	movz x2, #21272, lsl #0
	add x2, x28, x2
	movz x3, #320, lsl #0
	bl {vg_mlkem_compress_encode}
	add x0, x25, #1152
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
2246:
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
	cbnz x11, 2246b
	add x0, x25, #1536
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
2247:
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
	cbnz x11, 2247b
	add x0, x25, #1920
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
2248:
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
	cbnz x11, 2248b
	movz x0, #17560, lsl #0
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
2249:
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movz x1, #4248, lsl #0
	add x1, x28, x1
	movz x2, #13464, lsl #0
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
	movz x2, #14488, lsl #0
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
	movz x2, #15512, lsl #0
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
	cbnz x11, 2249b
	movz x0, #17560, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem16_inv_ntt}
	movz x9, #6, lsl #0
	strb w9, [x28, #976]
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
	add x2, x28, #944
	ldr x9, [x2, #0]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	add x2, x28, #952
	ldr x9, [x2, #0]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	add x2, x28, #960
	ldr x9, [x2, #0]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	add x2, x28, #968
	ldr x9, [x2, #0]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	add x2, x28, #976
	ldrb w9, [x2, #0]
	ldrb w10, [x28, #32]
	eor x9, x9, x10
	strb w9, [x28, #32]
	ldrb w9, [x28, #33]
	movz x10, #31, lsl #0
	eor x9, x9, x10
	strb w9, [x28, #33]
	ldrb w9, [x28, #135]
	movz x10, #128, lsl #0
	eor x9, x9, x10
	strb w9, [x28, #135]
	add x0, x28, #0
	add x1, x28, #200
	bl {vg_keccak_f1600_sha3}
	ldr x9, [x28, #0]
	add x2, x28, #1048
	str x9, [x2, #0]
	ldr x9, [x28, #8]
	add x2, x28, #1056
	str x9, [x2, #0]
	ldr x9, [x28, #16]
	add x2, x28, #1064
	str x9, [x2, #0]
	ldr x9, [x28, #24]
	add x2, x28, #1072
	str x9, [x2, #0]
	ldr x9, [x28, #32]
	add x2, x28, #1080
	str x9, [x2, #0]
	ldr x9, [x28, #40]
	add x2, x28, #1088
	str x9, [x2, #0]
	ldr x9, [x28, #48]
	add x2, x28, #1096
	str x9, [x2, #0]
	ldr x9, [x28, #56]
	add x2, x28, #1104
	str x9, [x2, #0]
	ldr x9, [x28, #64]
	add x2, x28, #1112
	str x9, [x2, #0]
	ldr x9, [x28, #72]
	add x2, x28, #1120
	str x9, [x2, #0]
	ldr x9, [x28, #80]
	add x2, x28, #1128
	str x9, [x2, #0]
	ldr x9, [x28, #88]
	add x2, x28, #1136
	str x9, [x2, #0]
	ldr x9, [x28, #96]
	add x2, x28, #1144
	str x9, [x2, #0]
	ldr x9, [x28, #104]
	add x2, x28, #1152
	str x9, [x2, #0]
	ldr x9, [x28, #112]
	add x2, x28, #1160
	str x9, [x2, #0]
	ldr x9, [x28, #120]
	add x2, x28, #1168
	str x9, [x2, #0]
	ldr x30, [x28, #800]
	add x0, x28, #1048
	movz x1, #16536, lsl #0
	add x1, x28, x1
	bl {vg_mlkem16_cbd2}
	movz x0, #17560, lsl #0
	add x0, x28, x0
	movz x1, #16536, lsl #0
	add x1, x28, x1
	movz x9, #3329, lsl #0
	dup v16.8h, w9
	movz x11, #32, lsl #0
2250:
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
	cbnz x11, 2250b
	movz x0, #17560, lsl #0
	add x0, x28, x0
	movz x1, #18584, lsl #0
	add x1, x28, x1
	movz x10, #32, lsl #0
	movi v29.2d, #0
2251:
	ldr q0, [x0, #0]
	zip1 v1.8h, v0.8h, v29.8h
	zip2 v2.8h, v0.8h, v29.8h
	str q1, [x1, #0]
	str q2, [x1, #16]
	add x0, x0, #16
	add x1, x1, #32
	sub x10, x10, #1
	cbnz x10, 2251b
	add x0, x28, #912
	movz x1, #32, lsl #0
	movz x2, #1, lsl #0
	movz x3, #16536, lsl #0
	add x3, x28, x3
	bl {vg_mlkem_decode_decompress}
	movz x0, #18584, lsl #0
	add x0, x28, x0
	movz x1, #16536, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	movz x0, #18584, lsl #0
	add x0, x28, x0
	movz x1, #4, lsl #0
	movz x2, #21592, lsl #0
	add x2, x28, x2
	movz x3, #128, lsl #0
	bl {vg_mlkem_compress_encode}
	add x0, x26, #0
	movz x1, #20632, lsl #0
	add x1, x28, x1
	movz x2, #136, lsl #0
	movz x10, #0, lsl #0
2252:
	ldr x9, [x0, #0]
	ldr x11, [x1, #0]
	eor x9, x9, x11
	orr x10, x10, x9
	add x0, x0, #8
	add x1, x1, #8
	sub x2, x2, #1
	cbnz x2, 2252b
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
	ldr x24, [x28, #21720]
	ldr x30, [x28, #21728]
	ldr x25, [x28, #21736]
	ldr x26, [x28, #21744]
	ldr x27, [x28, #21752]
	ldr x28, [x28, #21760]
	ret
	.p2align 6
