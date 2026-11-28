// The functions of `src/slhdsa_shake_192s.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_slhdsa_shake_192s_keygen_sha3:
	str x19, [x3, #1536]
	str x20, [x3, #1544]
	str x21, [x3, #1552]
	str x22, [x3, #1560]
	str x23, [x3, #1568]
	str x24, [x3, #1576]
	str x25, [x3, #1584]
	str x30, [x3, #1592]
	add x19, x3, #0
	add x20, x1, #0
	add x21, x2, #0
	ldr q16, [x0, #0]
	str q16, [x19, #1664]
	ldr x14, [x0, #16]
	str x14, [x19, #1680]
	ldr x14, [x0, #24]
	str x14, [x19, #1696]
	ldr x14, [x0, #32]
	str x14, [x19, #1704]
	ldr x14, [x0, #40]
	str x14, [x19, #1712]
	ldr q16, [x0, #48]
	str q16, [x19, #1728]
	ldr x14, [x0, #64]
	str x14, [x19, #1744]
	ldr q16, [x19, #1728]
	str q16, [x19, #3136]
	ldr x14, [x19, #1744]
	str x14, [x19, #3152]
	ldr q16, [x19, #1728]
	str q16, [x19, #3648]
	ldr x14, [x19, #1744]
	str x14, [x19, #3664]
	ldr q16, [x19, #1728]
	str q16, [x19, #3264]
	ldr x14, [x19, #1744]
	str x14, [x19, #3280]
	ldr q16, [x19, #1728]
	str q16, [x19, #5856]
	ldr x14, [x19, #1744]
	str x14, [x19, #5872]
	ldr q16, [x19, #1728]
	str q16, [x19, #3392]
	ldr x14, [x19, #1744]
	str x14, [x19, #3408]
	ldr q16, [x19, #1728]
	str q16, [x19, #8064]
	ldr x14, [x19, #1744]
	str x14, [x19, #8080]
	ldr q16, [x19, #1728]
	str q16, [x19, #3520]
	ldr x14, [x19, #1744]
	str x14, [x19, #3536]
	ldr q16, [x19, #1728]
	str q16, [x19, #10272]
	ldr x14, [x19, #1744]
	str x14, [x19, #10288]
	movz x10, #6, lsl #0
	movz x11, #0, lsl #0
	rev x12, x11
	rev w13, w10
	movz x14, #0, lsl #0
	str w13, [x19, #3160]
	str w14, [x19, #3164]
	str x12, [x19, #3168]
	str w13, [x19, #3672]
	str w14, [x19, #3676]
	str x12, [x19, #3680]
	str w13, [x19, #3288]
	str w14, [x19, #3292]
	str x12, [x19, #3296]
	str w13, [x19, #5880]
	str w14, [x19, #5884]
	str x12, [x19, #5888]
	str w13, [x19, #3416]
	str w14, [x19, #3420]
	str x12, [x19, #3424]
	str w13, [x19, #8088]
	str w14, [x19, #8092]
	str x12, [x19, #8096]
	str w13, [x19, #3544]
	str w14, [x19, #3548]
	str x12, [x19, #3552]
	str w13, [x19, #10296]
	str w14, [x19, #10300]
	str x12, [x19, #10304]
	add x0, x19, #0
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movz x2, #30144, lsl #0
	add x2, x19, x2
	bl {vg_slhdsa_shake_xmss_192s_sha3}
	ldr q16, [x19, #1984]
	str q16, [x19, #1760]
	ldr x14, [x19, #2000]
	str x14, [x19, #1776]
	ldr q16, [x19, #1664]
	str q16, [x20, #0]
	ldr x14, [x19, #1680]
	str x14, [x20, #16]
	ldr x14, [x19, #1696]
	str x14, [x20, #24]
	ldr x14, [x19, #1704]
	str x14, [x20, #32]
	ldr x14, [x19, #1712]
	str x14, [x20, #40]
	ldr q16, [x19, #1728]
	str q16, [x20, #48]
	ldr x14, [x19, #1744]
	str x14, [x20, #64]
	ldr x14, [x19, #1760]
	str x14, [x20, #72]
	ldr x14, [x19, #1768]
	str x14, [x20, #80]
	ldr x14, [x19, #1776]
	str x14, [x20, #88]
	ldr q16, [x19, #1728]
	str q16, [x21, #0]
	ldr x14, [x19, #1744]
	str x14, [x21, #16]
	ldr x14, [x19, #1760]
	str x14, [x21, #24]
	ldr x14, [x19, #1768]
	str x14, [x21, #32]
	ldr x14, [x19, #1776]
	str x14, [x21, #40]
	ldr x20, [x19, #1544]
	ldr x21, [x19, #1552]
	ldr x22, [x19, #1560]
	ldr x23, [x19, #1568]
	ldr x24, [x19, #1576]
	ldr x25, [x19, #1584]
	ldr x30, [x19, #1592]
	ldr x19, [x19, #1536]
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	mov v8.d[1], x1
	mov v9.d[1], x1
	mov v10.d[1], x1
	mov v11.d[1], x1
	mov v12.d[1], x1
	mov v13.d[1], x1
	mov v14.d[1], x1
	mov v15.d[1], x1
	movz x0, #0, lsl #0
	ret
	.p2align 6

vg_slhdsa_shake_192s_sign_sha3:
	lsr x9, x4, #8
	cbnz x9, 20f
	str x19, [x7, #1536]
	str x20, [x7, #1544]
	str x21, [x7, #1552]
	str x22, [x7, #1560]
	str x23, [x7, #1568]
	str x24, [x7, #1576]
	str x25, [x7, #1584]
	str x30, [x7, #1592]
	add x19, x7, #0
	add x20, x1, #0
	add x21, x2, #0
	add x22, x3, #0
	add x23, x4, #0
	add x24, x5, #0
	add x25, x6, #0
	movz x9, #0, lsl #0
	strb w9, [x19, #1632]
	strb w23, [x19, #1633]
	ldr q16, [x0, #0]
	str q16, [x19, #1664]
	ldr x14, [x0, #16]
	str x14, [x19, #1680]
	ldr x14, [x0, #24]
	str x14, [x19, #1696]
	ldr x14, [x0, #32]
	str x14, [x19, #1704]
	ldr x14, [x0, #40]
	str x14, [x19, #1712]
	ldr q16, [x0, #48]
	str q16, [x19, #1728]
	ldr x14, [x0, #64]
	str x14, [x19, #1744]
	ldr x14, [x0, #72]
	str x14, [x19, #1760]
	ldr x14, [x0, #80]
	str x14, [x19, #1768]
	ldr x14, [x0, #88]
	str x14, [x19, #1776]
	add x9, x19, #2368
	movi v16.2d, #0
	str q16, [x9, #0]
	str q16, [x9, #16]
	str q16, [x9, #32]
	str q16, [x9, #48]
	str q16, [x9, #64]
	str q16, [x9, #80]
	str q16, [x9, #96]
	str q16, [x9, #112]
	str q16, [x9, #128]
	str q16, [x9, #144]
	str q16, [x9, #160]
	str q16, [x9, #176]
	movz x14, #0, lsl #0
	str x14, [x9, #192]
	movz x2, #0, lsl #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	add x3, x19, #1696
	movz x4, #24, lsl #0
	add x5, x19, #2568
	bl {vg_keccak_absorb_scratch_sha3}
	movz x2, #24, lsl #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	add x3, x24, #0
	movz x4, #24, lsl #0
	add x5, x19, #2568
	bl {vg_keccak_absorb_scratch_sha3}
	movz x2, #48, lsl #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	add x3, x19, #1632
	movz x4, #2, lsl #0
	add x5, x19, #2568
	bl {vg_keccak_absorb_scratch_sha3}
	add x2, x0, #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	add x3, x22, #0
	add x4, x23, #0
	add x5, x19, #2568
	bl {vg_keccak_absorb_scratch_sha3}
	add x2, x0, #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	add x3, x20, #0
	add x4, x21, #0
	add x5, x19, #2568
	bl {vg_keccak_absorb_scratch_sha3}
	add x2, x0, #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	movz x3, #31, lsl #0
	add x4, x19, #2568
	bl {vg_keccak_pad_scratch_sha3}
	movz x2, #0, lsl #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	add x3, x25, #0
	movz x4, #24, lsl #0
	add x5, x19, #2568
	bl {vg_keccak_squeeze_scratch_sha3}
	add x9, x19, #2368
	movi v16.2d, #0
	str q16, [x9, #0]
	str q16, [x9, #16]
	str q16, [x9, #32]
	str q16, [x9, #48]
	str q16, [x9, #64]
	str q16, [x9, #80]
	str q16, [x9, #96]
	str q16, [x9, #112]
	str q16, [x9, #128]
	str q16, [x9, #144]
	str q16, [x9, #160]
	str q16, [x9, #176]
	movz x14, #0, lsl #0
	str x14, [x9, #192]
	movz x2, #0, lsl #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	add x3, x25, #0
	movz x4, #24, lsl #0
	add x5, x19, #2568
	bl {vg_keccak_absorb_scratch_sha3}
	movz x2, #24, lsl #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	add x3, x19, #1728
	movz x4, #24, lsl #0
	add x5, x19, #2568
	bl {vg_keccak_absorb_scratch_sha3}
	movz x2, #48, lsl #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	add x3, x19, #1760
	movz x4, #24, lsl #0
	add x5, x19, #2568
	bl {vg_keccak_absorb_scratch_sha3}
	movz x2, #72, lsl #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	add x3, x19, #1632
	movz x4, #2, lsl #0
	add x5, x19, #2568
	bl {vg_keccak_absorb_scratch_sha3}
	add x2, x0, #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	add x3, x22, #0
	add x4, x23, #0
	add x5, x19, #2568
	bl {vg_keccak_absorb_scratch_sha3}
	add x2, x0, #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	add x3, x20, #0
	add x4, x21, #0
	add x5, x19, #2568
	bl {vg_keccak_absorb_scratch_sha3}
	add x2, x0, #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	movz x3, #31, lsl #0
	add x4, x19, #2568
	bl {vg_keccak_pad_scratch_sha3}
	movz x2, #0, lsl #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	add x3, x19, #1792
	movz x4, #39, lsl #0
	add x5, x19, #2568
	bl {vg_keccak_squeeze_scratch_sha3}
	ldr q16, [x19, #1728]
	str q16, [x19, #3136]
	ldr x14, [x19, #1744]
	str x14, [x19, #3152]
	ldr q16, [x19, #1728]
	str q16, [x19, #3648]
	ldr x14, [x19, #1744]
	str x14, [x19, #3664]
	ldr q16, [x19, #1728]
	str q16, [x19, #3264]
	ldr x14, [x19, #1744]
	str x14, [x19, #3280]
	ldr q16, [x19, #1728]
	str q16, [x19, #5856]
	ldr x14, [x19, #1744]
	str x14, [x19, #5872]
	ldr q16, [x19, #1728]
	str q16, [x19, #3392]
	ldr x14, [x19, #1744]
	str x14, [x19, #3408]
	ldr q16, [x19, #1728]
	str q16, [x19, #8064]
	ldr x14, [x19, #1744]
	str x14, [x19, #8080]
	ldr q16, [x19, #1728]
	str q16, [x19, #3520]
	ldr x14, [x19, #1744]
	str x14, [x19, #3536]
	ldr q16, [x19, #1728]
	str q16, [x19, #10272]
	ldr x14, [x19, #1744]
	str x14, [x19, #10288]
	add x9, x19, #1822
	ldr x10, [x9, #0]
	rev x10, x10
	lsr x10, x10, #8
	lsl x10, x10, #10
	lsr x10, x10, #10
	add x22, x10, #0
	add x9, x19, #1829
	ldr x10, [x9, #0]
	rev x10, x10
	lsr x10, x10, #48
	movz x11, #511, lsl #0
	and x23, x10, x11
	movz x10, #0, lsl #0
	rev x12, x22
	rev w13, w10
	movz x14, #0, lsl #0
	str w13, [x19, #3160]
	str w14, [x19, #3164]
	str x12, [x19, #3168]
	str w13, [x19, #3672]
	str w14, [x19, #3676]
	str x12, [x19, #3680]
	str w13, [x19, #3288]
	str w14, [x19, #3292]
	str x12, [x19, #3296]
	str w13, [x19, #5880]
	str w14, [x19, #5884]
	str x12, [x19, #5888]
	str w13, [x19, #3416]
	str w14, [x19, #3420]
	str x12, [x19, #3424]
	str w13, [x19, #8088]
	str w14, [x19, #8092]
	str x12, [x19, #8096]
	str w13, [x19, #3544]
	str w14, [x19, #3548]
	str x12, [x19, #3552]
	str w13, [x19, #10296]
	str w14, [x19, #10300]
	str x12, [x19, #10304]
	add x0, x19, #0
	add x1, x25, #24
	add x2, x23, #0
	bl {vg_slhdsa_shake_fors_192s_sha3}
	movz x21, #0, lsl #0
	movz x20, #6144, lsl #0
	add x20, x25, x20
22:
	rev x12, x22
	rev w13, w21
	movz x14, #0, lsl #0
	str w13, [x19, #3160]
	str w14, [x19, #3164]
	str x12, [x19, #3168]
	str w13, [x19, #3672]
	str w14, [x19, #3676]
	str x12, [x19, #3680]
	str w13, [x19, #3288]
	str w14, [x19, #3292]
	str x12, [x19, #3296]
	str w13, [x19, #5880]
	str w14, [x19, #5884]
	str x12, [x19, #5888]
	str w13, [x19, #3416]
	str w14, [x19, #3420]
	str x12, [x19, #3424]
	str w13, [x19, #8088]
	str w14, [x19, #8092]
	str x12, [x19, #8096]
	str w13, [x19, #3544]
	str w14, [x19, #3548]
	str x12, [x19, #3552]
	str w13, [x19, #10296]
	str w14, [x19, #10300]
	str x12, [x19, #10304]
	add x0, x19, #0
	add x1, x23, #0
	add x2, x20, #0
	bl {vg_slhdsa_shake_xmss_192s_sha3}
	add x20, x20, #1440
	movz x11, #511, lsl #0
	and x23, x22, x11
	lsr x22, x22, #9
	add x21, x21, #1
	sub x9, x21, #7
	cbnz x9, 22b
	ldr x20, [x19, #1544]
	ldr x21, [x19, #1552]
	ldr x22, [x19, #1560]
	ldr x23, [x19, #1568]
	ldr x24, [x19, #1576]
	ldr x25, [x19, #1584]
	ldr x30, [x19, #1592]
	ldr x19, [x19, #1536]
	movz x0, #1, lsl #0
	b 21f
20:
	movz x0, #2, lsl #0
21:
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	mov v8.d[1], x1
	mov v9.d[1], x1
	mov v10.d[1], x1
	mov v11.d[1], x1
	mov v12.d[1], x1
	mov v13.d[1], x1
	mov v14.d[1], x1
	mov v15.d[1], x1
	add w0, w0, #0
	sub sp, sp, #16
	movi v31.2d, #0
	add x9, sp, #0
	str q31, [x9, #0]
	add sp, sp, #16
	ret
	.p2align 6

vg_slhdsa_shake_192s_verify_sha3:
	lsr x9, x4, #8
	movz x10, #16224, lsl #0
	sub x10, x6, x10
	orr x9, x9, x10
	cbnz x9, 20f
	str x19, [x7, #1536]
	str x20, [x7, #1544]
	str x21, [x7, #1552]
	str x22, [x7, #1560]
	str x23, [x7, #1568]
	str x24, [x7, #1576]
	str x25, [x7, #1584]
	str x30, [x7, #1592]
	add x19, x7, #0
	add x20, x1, #0
	add x21, x2, #0
	add x22, x3, #0
	add x23, x4, #0
	add x24, x5, #0
	movz x9, #0, lsl #0
	strb w9, [x19, #1632]
	strb w23, [x19, #1633]
	ldr q16, [x0, #0]
	str q16, [x19, #1728]
	ldr x14, [x0, #16]
	str x14, [x19, #1744]
	ldr x14, [x0, #24]
	str x14, [x19, #1760]
	ldr x14, [x0, #32]
	str x14, [x19, #1768]
	ldr x14, [x0, #40]
	str x14, [x19, #1776]
	add x9, x19, #2368
	movi v16.2d, #0
	str q16, [x9, #0]
	str q16, [x9, #16]
	str q16, [x9, #32]
	str q16, [x9, #48]
	str q16, [x9, #64]
	str q16, [x9, #80]
	str q16, [x9, #96]
	str q16, [x9, #112]
	str q16, [x9, #128]
	str q16, [x9, #144]
	str q16, [x9, #160]
	str q16, [x9, #176]
	movz x14, #0, lsl #0
	str x14, [x9, #192]
	movz x2, #0, lsl #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	add x3, x24, #0
	movz x4, #24, lsl #0
	add x5, x19, #2568
	bl {vg_keccak_absorb_scratch_sha3}
	movz x2, #24, lsl #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	add x3, x19, #1728
	movz x4, #24, lsl #0
	add x5, x19, #2568
	bl {vg_keccak_absorb_scratch_sha3}
	movz x2, #48, lsl #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	add x3, x19, #1760
	movz x4, #24, lsl #0
	add x5, x19, #2568
	bl {vg_keccak_absorb_scratch_sha3}
	movz x2, #72, lsl #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	add x3, x19, #1632
	movz x4, #2, lsl #0
	add x5, x19, #2568
	bl {vg_keccak_absorb_scratch_sha3}
	add x2, x0, #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	add x3, x22, #0
	add x4, x23, #0
	add x5, x19, #2568
	bl {vg_keccak_absorb_scratch_sha3}
	add x2, x0, #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	add x3, x20, #0
	add x4, x21, #0
	add x5, x19, #2568
	bl {vg_keccak_absorb_scratch_sha3}
	add x2, x0, #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	movz x3, #31, lsl #0
	add x4, x19, #2568
	bl {vg_keccak_pad_scratch_sha3}
	movz x2, #0, lsl #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	add x3, x19, #1792
	movz x4, #39, lsl #0
	add x5, x19, #2568
	bl {vg_keccak_squeeze_scratch_sha3}
	ldr q16, [x19, #1728]
	str q16, [x19, #3136]
	ldr x14, [x19, #1744]
	str x14, [x19, #3152]
	ldr q16, [x19, #1728]
	str q16, [x19, #3648]
	ldr x14, [x19, #1744]
	str x14, [x19, #3664]
	ldr q16, [x19, #1728]
	str q16, [x19, #3264]
	ldr x14, [x19, #1744]
	str x14, [x19, #3280]
	ldr q16, [x19, #1728]
	str q16, [x19, #5856]
	ldr x14, [x19, #1744]
	str x14, [x19, #5872]
	ldr q16, [x19, #1728]
	str q16, [x19, #3392]
	ldr x14, [x19, #1744]
	str x14, [x19, #3408]
	ldr q16, [x19, #1728]
	str q16, [x19, #8064]
	ldr x14, [x19, #1744]
	str x14, [x19, #8080]
	ldr q16, [x19, #1728]
	str q16, [x19, #3520]
	ldr x14, [x19, #1744]
	str x14, [x19, #3536]
	ldr q16, [x19, #1728]
	str q16, [x19, #10272]
	ldr x14, [x19, #1744]
	str x14, [x19, #10288]
	add x9, x19, #1822
	ldr x10, [x9, #0]
	rev x10, x10
	lsr x10, x10, #8
	lsl x10, x10, #10
	lsr x10, x10, #10
	add x22, x10, #0
	add x9, x19, #1829
	ldr x10, [x9, #0]
	rev x10, x10
	lsr x10, x10, #48
	movz x11, #511, lsl #0
	and x23, x10, x11
	movz x10, #0, lsl #0
	rev x12, x22
	rev w13, w10
	movz x14, #0, lsl #0
	str w13, [x19, #3160]
	str w14, [x19, #3164]
	str x12, [x19, #3168]
	str w13, [x19, #3672]
	str w14, [x19, #3676]
	str x12, [x19, #3680]
	str w13, [x19, #3288]
	str w14, [x19, #3292]
	str x12, [x19, #3296]
	str w13, [x19, #5880]
	str w14, [x19, #5884]
	str x12, [x19, #5888]
	str w13, [x19, #3416]
	str w14, [x19, #3420]
	str x12, [x19, #3424]
	str w13, [x19, #8088]
	str w14, [x19, #8092]
	str x12, [x19, #8096]
	str w13, [x19, #3544]
	str w14, [x19, #3548]
	str x12, [x19, #3552]
	str w13, [x19, #10296]
	str w14, [x19, #10300]
	str x12, [x19, #10304]
	add x0, x19, #0
	add x1, x24, #24
	add x2, x23, #0
	bl {vg_slhdsa_shake_forspk_192s_sha3}
	movz x21, #0, lsl #0
	movz x20, #6144, lsl #0
	add x20, x24, x20
22:
	rev x12, x22
	rev w13, w21
	movz x14, #0, lsl #0
	str w13, [x19, #3160]
	str w14, [x19, #3164]
	str x12, [x19, #3168]
	str w13, [x19, #3672]
	str w14, [x19, #3676]
	str x12, [x19, #3680]
	str w13, [x19, #3288]
	str w14, [x19, #3292]
	str x12, [x19, #3296]
	str w13, [x19, #5880]
	str w14, [x19, #5884]
	str x12, [x19, #5888]
	str w13, [x19, #3416]
	str w14, [x19, #3420]
	str x12, [x19, #3424]
	str w13, [x19, #8088]
	str w14, [x19, #8092]
	str x12, [x19, #8096]
	str w13, [x19, #3544]
	str w14, [x19, #3548]
	str x12, [x19, #3552]
	str w13, [x19, #10296]
	str w14, [x19, #10300]
	str x12, [x19, #10304]
	add x0, x19, #0
	add x1, x23, #0
	add x2, x20, #0
	bl {vg_slhdsa_shake_xmsspk_192s_sha3}
	add x20, x20, #1440
	movz x11, #511, lsl #0
	and x23, x22, x11
	lsr x22, x22, #9
	add x21, x21, #1
	sub x9, x21, #7
	cbnz x9, 22b
	movz x9, #0, lsl #0
	ldr x10, [x19, #1984]
	ldr x11, [x19, #1760]
	eor x10, x10, x11
	orr x9, x9, x10
	ldr x10, [x19, #1992]
	ldr x11, [x19, #1768]
	eor x10, x10, x11
	orr x9, x9, x10
	ldr x10, [x19, #2000]
	ldr x11, [x19, #1776]
	eor x10, x10, x11
	orr x9, x9, x10
	movz x10, #0, lsl #0
	sub x10, x10, x9
	orr x10, x10, x9
	lsr x10, x10, #63
	movz x11, #1, lsl #0
	sub x9, x11, x10
	ldr x20, [x19, #1544]
	ldr x21, [x19, #1552]
	ldr x22, [x19, #1560]
	ldr x23, [x19, #1568]
	ldr x24, [x19, #1576]
	ldr x25, [x19, #1584]
	ldr x30, [x19, #1592]
	ldr x19, [x19, #1536]
	add x0, x9, #0
	b 21f
20:
	movz x0, #0, lsl #0
21:
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	mov v8.d[1], x1
	mov v9.d[1], x1
	mov v10.d[1], x1
	mov v11.d[1], x1
	mov v12.d[1], x1
	mov v13.d[1], x1
	mov v14.d[1], x1
	mov v15.d[1], x1
	add w0, w0, #0
	sub sp, sp, #16
	movi v31.2d, #0
	add x9, sp, #0
	str q31, [x9, #0]
	add sp, sp, #16
	ret
	.p2align 6

vg_slhdsa_shake_192s_keygen:
	str x19, [x3, #1536]
	str x20, [x3, #1544]
	str x21, [x3, #1552]
	str x22, [x3, #1560]
	str x23, [x3, #1568]
	str x24, [x3, #1576]
	str x25, [x3, #1584]
	str x30, [x3, #1592]
	add x19, x3, #0
	add x20, x1, #0
	add x21, x2, #0
	ldr q16, [x0, #0]
	str q16, [x19, #1664]
	ldr x14, [x0, #16]
	str x14, [x19, #1680]
	ldr x14, [x0, #24]
	str x14, [x19, #1696]
	ldr x14, [x0, #32]
	str x14, [x19, #1704]
	ldr x14, [x0, #40]
	str x14, [x19, #1712]
	ldr q16, [x0, #48]
	str q16, [x19, #1728]
	ldr x14, [x0, #64]
	str x14, [x19, #1744]
	ldr q16, [x19, #1728]
	str q16, [x19, #3136]
	ldr x14, [x19, #1744]
	str x14, [x19, #3152]
	ldr q16, [x19, #1728]
	str q16, [x19, #3648]
	ldr x14, [x19, #1744]
	str x14, [x19, #3664]
	ldr q16, [x19, #1728]
	str q16, [x19, #3264]
	ldr x14, [x19, #1744]
	str x14, [x19, #3280]
	ldr q16, [x19, #1728]
	str q16, [x19, #5856]
	ldr x14, [x19, #1744]
	str x14, [x19, #5872]
	ldr q16, [x19, #1728]
	str q16, [x19, #3392]
	ldr x14, [x19, #1744]
	str x14, [x19, #3408]
	ldr q16, [x19, #1728]
	str q16, [x19, #8064]
	ldr x14, [x19, #1744]
	str x14, [x19, #8080]
	ldr q16, [x19, #1728]
	str q16, [x19, #3520]
	ldr x14, [x19, #1744]
	str x14, [x19, #3536]
	ldr q16, [x19, #1728]
	str q16, [x19, #10272]
	ldr x14, [x19, #1744]
	str x14, [x19, #10288]
	movz x10, #6, lsl #0
	movz x11, #0, lsl #0
	rev x12, x11
	rev w13, w10
	movz x14, #0, lsl #0
	str w13, [x19, #3160]
	str w14, [x19, #3164]
	str x12, [x19, #3168]
	str w13, [x19, #3672]
	str w14, [x19, #3676]
	str x12, [x19, #3680]
	str w13, [x19, #3288]
	str w14, [x19, #3292]
	str x12, [x19, #3296]
	str w13, [x19, #5880]
	str w14, [x19, #5884]
	str x12, [x19, #5888]
	str w13, [x19, #3416]
	str w14, [x19, #3420]
	str x12, [x19, #3424]
	str w13, [x19, #8088]
	str w14, [x19, #8092]
	str x12, [x19, #8096]
	str w13, [x19, #3544]
	str w14, [x19, #3548]
	str x12, [x19, #3552]
	str w13, [x19, #10296]
	str w14, [x19, #10300]
	str x12, [x19, #10304]
	add x0, x19, #0
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movz x2, #30144, lsl #0
	add x2, x19, x2
	bl {vg_slhdsa_shake_xmss_192s}
	ldr q16, [x19, #1984]
	str q16, [x19, #1760]
	ldr x14, [x19, #2000]
	str x14, [x19, #1776]
	ldr q16, [x19, #1664]
	str q16, [x20, #0]
	ldr x14, [x19, #1680]
	str x14, [x20, #16]
	ldr x14, [x19, #1696]
	str x14, [x20, #24]
	ldr x14, [x19, #1704]
	str x14, [x20, #32]
	ldr x14, [x19, #1712]
	str x14, [x20, #40]
	ldr q16, [x19, #1728]
	str q16, [x20, #48]
	ldr x14, [x19, #1744]
	str x14, [x20, #64]
	ldr x14, [x19, #1760]
	str x14, [x20, #72]
	ldr x14, [x19, #1768]
	str x14, [x20, #80]
	ldr x14, [x19, #1776]
	str x14, [x20, #88]
	ldr q16, [x19, #1728]
	str q16, [x21, #0]
	ldr x14, [x19, #1744]
	str x14, [x21, #16]
	ldr x14, [x19, #1760]
	str x14, [x21, #24]
	ldr x14, [x19, #1768]
	str x14, [x21, #32]
	ldr x14, [x19, #1776]
	str x14, [x21, #40]
	ldr x20, [x19, #1544]
	ldr x21, [x19, #1552]
	ldr x22, [x19, #1560]
	ldr x23, [x19, #1568]
	ldr x24, [x19, #1576]
	ldr x25, [x19, #1584]
	ldr x30, [x19, #1592]
	ldr x19, [x19, #1536]
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	mov v8.d[1], x1
	mov v9.d[1], x1
	mov v10.d[1], x1
	mov v11.d[1], x1
	mov v12.d[1], x1
	mov v13.d[1], x1
	mov v14.d[1], x1
	mov v15.d[1], x1
	movz x0, #0, lsl #0
	ret
	.p2align 6

vg_slhdsa_shake_192s_sign:
	lsr x9, x4, #8
	cbnz x9, 20f
	str x19, [x7, #1536]
	str x20, [x7, #1544]
	str x21, [x7, #1552]
	str x22, [x7, #1560]
	str x23, [x7, #1568]
	str x24, [x7, #1576]
	str x25, [x7, #1584]
	str x30, [x7, #1592]
	add x19, x7, #0
	add x20, x1, #0
	add x21, x2, #0
	add x22, x3, #0
	add x23, x4, #0
	add x24, x5, #0
	add x25, x6, #0
	movz x9, #0, lsl #0
	strb w9, [x19, #1632]
	strb w23, [x19, #1633]
	ldr q16, [x0, #0]
	str q16, [x19, #1664]
	ldr x14, [x0, #16]
	str x14, [x19, #1680]
	ldr x14, [x0, #24]
	str x14, [x19, #1696]
	ldr x14, [x0, #32]
	str x14, [x19, #1704]
	ldr x14, [x0, #40]
	str x14, [x19, #1712]
	ldr q16, [x0, #48]
	str q16, [x19, #1728]
	ldr x14, [x0, #64]
	str x14, [x19, #1744]
	ldr x14, [x0, #72]
	str x14, [x19, #1760]
	ldr x14, [x0, #80]
	str x14, [x19, #1768]
	ldr x14, [x0, #88]
	str x14, [x19, #1776]
	add x9, x19, #2368
	movi v16.2d, #0
	str q16, [x9, #0]
	str q16, [x9, #16]
	str q16, [x9, #32]
	str q16, [x9, #48]
	str q16, [x9, #64]
	str q16, [x9, #80]
	str q16, [x9, #96]
	str q16, [x9, #112]
	str q16, [x9, #128]
	str q16, [x9, #144]
	str q16, [x9, #160]
	str q16, [x9, #176]
	movz x14, #0, lsl #0
	str x14, [x9, #192]
	movz x2, #0, lsl #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	add x3, x19, #1696
	movz x4, #24, lsl #0
	add x5, x19, #2568
	bl {vg_keccak_absorb_scratch}
	movz x2, #24, lsl #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	add x3, x24, #0
	movz x4, #24, lsl #0
	add x5, x19, #2568
	bl {vg_keccak_absorb_scratch}
	movz x2, #48, lsl #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	add x3, x19, #1632
	movz x4, #2, lsl #0
	add x5, x19, #2568
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	add x3, x22, #0
	add x4, x23, #0
	add x5, x19, #2568
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	add x3, x20, #0
	add x4, x21, #0
	add x5, x19, #2568
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	movz x3, #31, lsl #0
	add x4, x19, #2568
	bl {vg_keccak_pad_scratch}
	movz x2, #0, lsl #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	add x3, x25, #0
	movz x4, #24, lsl #0
	add x5, x19, #2568
	bl {vg_keccak_squeeze_scratch}
	add x9, x19, #2368
	movi v16.2d, #0
	str q16, [x9, #0]
	str q16, [x9, #16]
	str q16, [x9, #32]
	str q16, [x9, #48]
	str q16, [x9, #64]
	str q16, [x9, #80]
	str q16, [x9, #96]
	str q16, [x9, #112]
	str q16, [x9, #128]
	str q16, [x9, #144]
	str q16, [x9, #160]
	str q16, [x9, #176]
	movz x14, #0, lsl #0
	str x14, [x9, #192]
	movz x2, #0, lsl #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	add x3, x25, #0
	movz x4, #24, lsl #0
	add x5, x19, #2568
	bl {vg_keccak_absorb_scratch}
	movz x2, #24, lsl #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	add x3, x19, #1728
	movz x4, #24, lsl #0
	add x5, x19, #2568
	bl {vg_keccak_absorb_scratch}
	movz x2, #48, lsl #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	add x3, x19, #1760
	movz x4, #24, lsl #0
	add x5, x19, #2568
	bl {vg_keccak_absorb_scratch}
	movz x2, #72, lsl #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	add x3, x19, #1632
	movz x4, #2, lsl #0
	add x5, x19, #2568
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	add x3, x22, #0
	add x4, x23, #0
	add x5, x19, #2568
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	add x3, x20, #0
	add x4, x21, #0
	add x5, x19, #2568
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	movz x3, #31, lsl #0
	add x4, x19, #2568
	bl {vg_keccak_pad_scratch}
	movz x2, #0, lsl #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	add x3, x19, #1792
	movz x4, #39, lsl #0
	add x5, x19, #2568
	bl {vg_keccak_squeeze_scratch}
	ldr q16, [x19, #1728]
	str q16, [x19, #3136]
	ldr x14, [x19, #1744]
	str x14, [x19, #3152]
	ldr q16, [x19, #1728]
	str q16, [x19, #3648]
	ldr x14, [x19, #1744]
	str x14, [x19, #3664]
	ldr q16, [x19, #1728]
	str q16, [x19, #3264]
	ldr x14, [x19, #1744]
	str x14, [x19, #3280]
	ldr q16, [x19, #1728]
	str q16, [x19, #5856]
	ldr x14, [x19, #1744]
	str x14, [x19, #5872]
	ldr q16, [x19, #1728]
	str q16, [x19, #3392]
	ldr x14, [x19, #1744]
	str x14, [x19, #3408]
	ldr q16, [x19, #1728]
	str q16, [x19, #8064]
	ldr x14, [x19, #1744]
	str x14, [x19, #8080]
	ldr q16, [x19, #1728]
	str q16, [x19, #3520]
	ldr x14, [x19, #1744]
	str x14, [x19, #3536]
	ldr q16, [x19, #1728]
	str q16, [x19, #10272]
	ldr x14, [x19, #1744]
	str x14, [x19, #10288]
	add x9, x19, #1822
	ldr x10, [x9, #0]
	rev x10, x10
	lsr x10, x10, #8
	lsl x10, x10, #10
	lsr x10, x10, #10
	add x22, x10, #0
	add x9, x19, #1829
	ldr x10, [x9, #0]
	rev x10, x10
	lsr x10, x10, #48
	movz x11, #511, lsl #0
	and x23, x10, x11
	movz x10, #0, lsl #0
	rev x12, x22
	rev w13, w10
	movz x14, #0, lsl #0
	str w13, [x19, #3160]
	str w14, [x19, #3164]
	str x12, [x19, #3168]
	str w13, [x19, #3672]
	str w14, [x19, #3676]
	str x12, [x19, #3680]
	str w13, [x19, #3288]
	str w14, [x19, #3292]
	str x12, [x19, #3296]
	str w13, [x19, #5880]
	str w14, [x19, #5884]
	str x12, [x19, #5888]
	str w13, [x19, #3416]
	str w14, [x19, #3420]
	str x12, [x19, #3424]
	str w13, [x19, #8088]
	str w14, [x19, #8092]
	str x12, [x19, #8096]
	str w13, [x19, #3544]
	str w14, [x19, #3548]
	str x12, [x19, #3552]
	str w13, [x19, #10296]
	str w14, [x19, #10300]
	str x12, [x19, #10304]
	add x0, x19, #0
	add x1, x25, #24
	add x2, x23, #0
	bl {vg_slhdsa_shake_fors_192s}
	movz x21, #0, lsl #0
	movz x20, #6144, lsl #0
	add x20, x25, x20
22:
	rev x12, x22
	rev w13, w21
	movz x14, #0, lsl #0
	str w13, [x19, #3160]
	str w14, [x19, #3164]
	str x12, [x19, #3168]
	str w13, [x19, #3672]
	str w14, [x19, #3676]
	str x12, [x19, #3680]
	str w13, [x19, #3288]
	str w14, [x19, #3292]
	str x12, [x19, #3296]
	str w13, [x19, #5880]
	str w14, [x19, #5884]
	str x12, [x19, #5888]
	str w13, [x19, #3416]
	str w14, [x19, #3420]
	str x12, [x19, #3424]
	str w13, [x19, #8088]
	str w14, [x19, #8092]
	str x12, [x19, #8096]
	str w13, [x19, #3544]
	str w14, [x19, #3548]
	str x12, [x19, #3552]
	str w13, [x19, #10296]
	str w14, [x19, #10300]
	str x12, [x19, #10304]
	add x0, x19, #0
	add x1, x23, #0
	add x2, x20, #0
	bl {vg_slhdsa_shake_xmss_192s}
	add x20, x20, #1440
	movz x11, #511, lsl #0
	and x23, x22, x11
	lsr x22, x22, #9
	add x21, x21, #1
	sub x9, x21, #7
	cbnz x9, 22b
	ldr x20, [x19, #1544]
	ldr x21, [x19, #1552]
	ldr x22, [x19, #1560]
	ldr x23, [x19, #1568]
	ldr x24, [x19, #1576]
	ldr x25, [x19, #1584]
	ldr x30, [x19, #1592]
	ldr x19, [x19, #1536]
	movz x0, #1, lsl #0
	b 21f
20:
	movz x0, #2, lsl #0
21:
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	mov v8.d[1], x1
	mov v9.d[1], x1
	mov v10.d[1], x1
	mov v11.d[1], x1
	mov v12.d[1], x1
	mov v13.d[1], x1
	mov v14.d[1], x1
	mov v15.d[1], x1
	add w0, w0, #0
	sub sp, sp, #16
	movi v31.2d, #0
	add x9, sp, #0
	str q31, [x9, #0]
	add sp, sp, #16
	ret
	.p2align 6

vg_slhdsa_shake_192s_verify:
	lsr x9, x4, #8
	movz x10, #16224, lsl #0
	sub x10, x6, x10
	orr x9, x9, x10
	cbnz x9, 20f
	str x19, [x7, #1536]
	str x20, [x7, #1544]
	str x21, [x7, #1552]
	str x22, [x7, #1560]
	str x23, [x7, #1568]
	str x24, [x7, #1576]
	str x25, [x7, #1584]
	str x30, [x7, #1592]
	add x19, x7, #0
	add x20, x1, #0
	add x21, x2, #0
	add x22, x3, #0
	add x23, x4, #0
	add x24, x5, #0
	movz x9, #0, lsl #0
	strb w9, [x19, #1632]
	strb w23, [x19, #1633]
	ldr q16, [x0, #0]
	str q16, [x19, #1728]
	ldr x14, [x0, #16]
	str x14, [x19, #1744]
	ldr x14, [x0, #24]
	str x14, [x19, #1760]
	ldr x14, [x0, #32]
	str x14, [x19, #1768]
	ldr x14, [x0, #40]
	str x14, [x19, #1776]
	add x9, x19, #2368
	movi v16.2d, #0
	str q16, [x9, #0]
	str q16, [x9, #16]
	str q16, [x9, #32]
	str q16, [x9, #48]
	str q16, [x9, #64]
	str q16, [x9, #80]
	str q16, [x9, #96]
	str q16, [x9, #112]
	str q16, [x9, #128]
	str q16, [x9, #144]
	str q16, [x9, #160]
	str q16, [x9, #176]
	movz x14, #0, lsl #0
	str x14, [x9, #192]
	movz x2, #0, lsl #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	add x3, x24, #0
	movz x4, #24, lsl #0
	add x5, x19, #2568
	bl {vg_keccak_absorb_scratch}
	movz x2, #24, lsl #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	add x3, x19, #1728
	movz x4, #24, lsl #0
	add x5, x19, #2568
	bl {vg_keccak_absorb_scratch}
	movz x2, #48, lsl #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	add x3, x19, #1760
	movz x4, #24, lsl #0
	add x5, x19, #2568
	bl {vg_keccak_absorb_scratch}
	movz x2, #72, lsl #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	add x3, x19, #1632
	movz x4, #2, lsl #0
	add x5, x19, #2568
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	add x3, x22, #0
	add x4, x23, #0
	add x5, x19, #2568
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	add x3, x20, #0
	add x4, x21, #0
	add x5, x19, #2568
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	movz x3, #31, lsl #0
	add x4, x19, #2568
	bl {vg_keccak_pad_scratch}
	movz x2, #0, lsl #0
	add x0, x19, #2368
	movz x1, #136, lsl #0
	add x3, x19, #1792
	movz x4, #39, lsl #0
	add x5, x19, #2568
	bl {vg_keccak_squeeze_scratch}
	ldr q16, [x19, #1728]
	str q16, [x19, #3136]
	ldr x14, [x19, #1744]
	str x14, [x19, #3152]
	ldr q16, [x19, #1728]
	str q16, [x19, #3648]
	ldr x14, [x19, #1744]
	str x14, [x19, #3664]
	ldr q16, [x19, #1728]
	str q16, [x19, #3264]
	ldr x14, [x19, #1744]
	str x14, [x19, #3280]
	ldr q16, [x19, #1728]
	str q16, [x19, #5856]
	ldr x14, [x19, #1744]
	str x14, [x19, #5872]
	ldr q16, [x19, #1728]
	str q16, [x19, #3392]
	ldr x14, [x19, #1744]
	str x14, [x19, #3408]
	ldr q16, [x19, #1728]
	str q16, [x19, #8064]
	ldr x14, [x19, #1744]
	str x14, [x19, #8080]
	ldr q16, [x19, #1728]
	str q16, [x19, #3520]
	ldr x14, [x19, #1744]
	str x14, [x19, #3536]
	ldr q16, [x19, #1728]
	str q16, [x19, #10272]
	ldr x14, [x19, #1744]
	str x14, [x19, #10288]
	add x9, x19, #1822
	ldr x10, [x9, #0]
	rev x10, x10
	lsr x10, x10, #8
	lsl x10, x10, #10
	lsr x10, x10, #10
	add x22, x10, #0
	add x9, x19, #1829
	ldr x10, [x9, #0]
	rev x10, x10
	lsr x10, x10, #48
	movz x11, #511, lsl #0
	and x23, x10, x11
	movz x10, #0, lsl #0
	rev x12, x22
	rev w13, w10
	movz x14, #0, lsl #0
	str w13, [x19, #3160]
	str w14, [x19, #3164]
	str x12, [x19, #3168]
	str w13, [x19, #3672]
	str w14, [x19, #3676]
	str x12, [x19, #3680]
	str w13, [x19, #3288]
	str w14, [x19, #3292]
	str x12, [x19, #3296]
	str w13, [x19, #5880]
	str w14, [x19, #5884]
	str x12, [x19, #5888]
	str w13, [x19, #3416]
	str w14, [x19, #3420]
	str x12, [x19, #3424]
	str w13, [x19, #8088]
	str w14, [x19, #8092]
	str x12, [x19, #8096]
	str w13, [x19, #3544]
	str w14, [x19, #3548]
	str x12, [x19, #3552]
	str w13, [x19, #10296]
	str w14, [x19, #10300]
	str x12, [x19, #10304]
	add x0, x19, #0
	add x1, x24, #24
	add x2, x23, #0
	bl {vg_slhdsa_shake_forspk_192s}
	movz x21, #0, lsl #0
	movz x20, #6144, lsl #0
	add x20, x24, x20
22:
	rev x12, x22
	rev w13, w21
	movz x14, #0, lsl #0
	str w13, [x19, #3160]
	str w14, [x19, #3164]
	str x12, [x19, #3168]
	str w13, [x19, #3672]
	str w14, [x19, #3676]
	str x12, [x19, #3680]
	str w13, [x19, #3288]
	str w14, [x19, #3292]
	str x12, [x19, #3296]
	str w13, [x19, #5880]
	str w14, [x19, #5884]
	str x12, [x19, #5888]
	str w13, [x19, #3416]
	str w14, [x19, #3420]
	str x12, [x19, #3424]
	str w13, [x19, #8088]
	str w14, [x19, #8092]
	str x12, [x19, #8096]
	str w13, [x19, #3544]
	str w14, [x19, #3548]
	str x12, [x19, #3552]
	str w13, [x19, #10296]
	str w14, [x19, #10300]
	str x12, [x19, #10304]
	add x0, x19, #0
	add x1, x23, #0
	add x2, x20, #0
	bl {vg_slhdsa_shake_xmsspk_192s}
	add x20, x20, #1440
	movz x11, #511, lsl #0
	and x23, x22, x11
	lsr x22, x22, #9
	add x21, x21, #1
	sub x9, x21, #7
	cbnz x9, 22b
	movz x9, #0, lsl #0
	ldr x10, [x19, #1984]
	ldr x11, [x19, #1760]
	eor x10, x10, x11
	orr x9, x9, x10
	ldr x10, [x19, #1992]
	ldr x11, [x19, #1768]
	eor x10, x10, x11
	orr x9, x9, x10
	ldr x10, [x19, #2000]
	ldr x11, [x19, #1776]
	eor x10, x10, x11
	orr x9, x9, x10
	movz x10, #0, lsl #0
	sub x10, x10, x9
	orr x10, x10, x9
	lsr x10, x10, #63
	movz x11, #1, lsl #0
	sub x9, x11, x10
	ldr x20, [x19, #1544]
	ldr x21, [x19, #1552]
	ldr x22, [x19, #1560]
	ldr x23, [x19, #1568]
	ldr x24, [x19, #1576]
	ldr x25, [x19, #1584]
	ldr x30, [x19, #1592]
	ldr x19, [x19, #1536]
	add x0, x9, #0
	b 21f
20:
	movz x0, #0, lsl #0
21:
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	mov v8.d[1], x1
	mov v9.d[1], x1
	mov v10.d[1], x1
	mov v11.d[1], x1
	mov v12.d[1], x1
	mov v13.d[1], x1
	mov v14.d[1], x1
	mov v15.d[1], x1
	add w0, w0, #0
	sub sp, sp, #16
	movi v31.2d, #0
	add x9, sp, #0
	str q31, [x9, #0]
	add sp, sp, #16
	ret
	.p2align 6
