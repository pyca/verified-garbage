// The functions of `src/ecdsa_p521_sha512.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p521_sha512_sign:
	str x30, [sp, #-16]!
	sub sp, sp, #368
	add x15, sp, #0
	str x0, [x15, #208]
	str x1, [x15, #200]
	str x2, [x15, #192]
	str x3, [x15, #184]
	ldr x1, [sp, #192]
	add x15, sp, #0
	movz x11, #0, lsl #0
	str x11, [x15, #288]
	ldr x11, [x1, #0]
	str x11, [x15, #224]
	ldr x11, [x1, #8]
	str x11, [x15, #232]
	ldr x11, [x1, #16]
	str x11, [x15, #240]
	ldr x11, [x1, #24]
	str x11, [x15, #248]
	ldr x11, [x1, #32]
	str x11, [x15, #256]
	ldr x11, [x1, #40]
	str x11, [x15, #264]
	ldr x11, [x1, #48]
	str x11, [x15, #272]
	ldr x11, [x1, #56]
	str x11, [x15, #280]
	ldr x0, [sp, #184]
	add x6, sp, #224
	add x17, x6, #58
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2560]
	add x17, x6, #50
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2568]
	add x17, x6, #42
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2576]
	add x17, x6, #34
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2584]
	add x17, x6, #26
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2592]
	add x17, x6, #18
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2600]
	add x17, x6, #10
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2608]
	add x17, x6, #2
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2616]
	ldr x5, [x6, #0]
	rev x5, x5
	lsr x5, x5, #48
	str x5, [x0, #2624]
	ldr x1, [x0, #2560]
	ldr x2, [x0, #2568]
	extr x1, x2, x1, #9
	str x1, [x0, #2560]
	ldr x1, [x0, #2568]
	ldr x2, [x0, #2576]
	extr x1, x2, x1, #9
	str x1, [x0, #2568]
	ldr x1, [x0, #2576]
	ldr x2, [x0, #2584]
	extr x1, x2, x1, #9
	str x1, [x0, #2576]
	ldr x1, [x0, #2584]
	ldr x2, [x0, #2592]
	extr x1, x2, x1, #9
	str x1, [x0, #2584]
	ldr x1, [x0, #2592]
	ldr x2, [x0, #2600]
	extr x1, x2, x1, #9
	str x1, [x0, #2592]
	ldr x1, [x0, #2600]
	ldr x2, [x0, #2608]
	extr x1, x2, x1, #9
	str x1, [x0, #2600]
	ldr x1, [x0, #2608]
	ldr x2, [x0, #2616]
	extr x1, x2, x1, #9
	str x1, [x0, #2608]
	ldr x1, [x0, #2616]
	ldr x2, [x0, #2624]
	extr x1, x2, x1, #9
	str x1, [x0, #2616]
	ldr x1, [x0, #2624]
	lsr x1, x1, #9
	str x1, [x0, #2624]
	movz x3, #0, lsl #0
	sub x3, x3, #1
	ldr x1, [x0, #2560]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #58
	str x1, [x17, #0]
	ldr x1, [x0, #2568]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #50
	str x1, [x17, #0]
	ldr x1, [x0, #2576]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #42
	str x1, [x17, #0]
	ldr x1, [x0, #2584]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #34
	str x1, [x17, #0]
	ldr x1, [x0, #2592]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #26
	str x1, [x17, #0]
	ldr x1, [x0, #2600]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #18
	str x1, [x17, #0]
	ldr x1, [x0, #2608]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #10
	str x1, [x17, #0]
	ldr x1, [x0, #2616]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #2
	str x1, [x17, #0]
	ldr x1, [x0, #2624]
	and x1, x1, x3
	lsr x2, x1, #8
	strb w2, [x6, #0]
	strb w1, [x6, #1]
	movz x9, #257, lsl #0
	movk x9, #257, lsl #16
	movk x9, #257, lsl #32
	movk x9, #257, lsl #48
	movz x10, #0, lsl #0
	add x15, sp, #0
	str x9, [x15, #64]
	str x10, [x15, #0]
	str x9, [x15, #72]
	str x10, [x15, #8]
	str x9, [x15, #80]
	str x10, [x15, #16]
	str x9, [x15, #88]
	str x10, [x15, #24]
	str x9, [x15, #96]
	str x10, [x15, #32]
	str x9, [x15, #104]
	str x10, [x15, #40]
	str x9, [x15, #112]
	str x10, [x15, #48]
	str x9, [x15, #120]
	str x10, [x15, #56]
	ldr x9, [sp, #184]
	ldr x10, [sp, #200]
	add x15, sp, #0
	ldr x8, [sp, #192]
	ldr x11, [x15, #64]
	str x11, [x9, #2256]
	ldr x11, [x15, #72]
	str x11, [x9, #2264]
	ldr x11, [x15, #80]
	str x11, [x9, #2272]
	ldr x11, [x15, #88]
	str x11, [x9, #2280]
	ldr x11, [x15, #96]
	str x11, [x9, #2288]
	ldr x11, [x15, #104]
	str x11, [x9, #2296]
	ldr x11, [x15, #112]
	str x11, [x9, #2304]
	ldr x11, [x15, #120]
	str x11, [x9, #2312]
	movz x11, #0, lsl #0
	strb w11, [x9, #2320]
	add x12, x9, #2321
	ldr x11, [x10, #0]
	str x11, [x12, #0]
	ldr x11, [x10, #8]
	str x11, [x12, #8]
	ldr x11, [x10, #16]
	str x11, [x12, #16]
	ldr x11, [x10, #24]
	str x11, [x12, #24]
	ldr x11, [x10, #32]
	str x11, [x12, #32]
	ldr x11, [x10, #40]
	str x11, [x12, #40]
	ldr x11, [x10, #48]
	str x11, [x12, #48]
	ldr x11, [x10, #56]
	str x11, [x12, #56]
	add x13, x10, #58
	add x14, x12, #58
	ldr x11, [x13, #0]
	str x11, [x14, #0]
	add x13, x9, #2387
	movz x11, #0, lsl #0
	str x11, [x13, #0]
	add x14, x9, #2389
	ldr x11, [x8, #0]
	str x11, [x14, #0]
	ldr x11, [x8, #8]
	str x11, [x14, #8]
	ldr x11, [x8, #16]
	str x11, [x14, #16]
	ldr x11, [x8, #24]
	str x11, [x14, #24]
	ldr x11, [x8, #32]
	str x11, [x14, #32]
	ldr x11, [x8, #40]
	str x11, [x14, #40]
	ldr x11, [x8, #48]
	str x11, [x14, #48]
	ldr x11, [x8, #56]
	str x11, [x14, #56]
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #64, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha512_init_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #128, lsl #0
	ldr x2, [sp, #184]
	add x2, x2, #2256
	movz x3, #197, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha512_update_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #325, lsl #0
	add x3, sp, #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha512_finalize_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #64, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha512_init_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #128, lsl #0
	add x2, sp, #64
	movz x3, #64, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha512_update_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #192, lsl #0
	add x3, sp, #64
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha512_finalize_scratch}
	ldr x9, [sp, #184]
	ldr x10, [sp, #200]
	add x15, sp, #0
	ldr x8, [sp, #192]
	ldr x11, [x15, #64]
	str x11, [x9, #2256]
	ldr x11, [x15, #72]
	str x11, [x9, #2264]
	ldr x11, [x15, #80]
	str x11, [x9, #2272]
	ldr x11, [x15, #88]
	str x11, [x9, #2280]
	ldr x11, [x15, #96]
	str x11, [x9, #2288]
	ldr x11, [x15, #104]
	str x11, [x9, #2296]
	ldr x11, [x15, #112]
	str x11, [x9, #2304]
	ldr x11, [x15, #120]
	str x11, [x9, #2312]
	movz x11, #1, lsl #0
	strb w11, [x9, #2320]
	add x12, x9, #2321
	ldr x11, [x10, #0]
	str x11, [x12, #0]
	ldr x11, [x10, #8]
	str x11, [x12, #8]
	ldr x11, [x10, #16]
	str x11, [x12, #16]
	ldr x11, [x10, #24]
	str x11, [x12, #24]
	ldr x11, [x10, #32]
	str x11, [x12, #32]
	ldr x11, [x10, #40]
	str x11, [x12, #40]
	ldr x11, [x10, #48]
	str x11, [x12, #48]
	ldr x11, [x10, #56]
	str x11, [x12, #56]
	add x13, x10, #58
	add x14, x12, #58
	ldr x11, [x13, #0]
	str x11, [x14, #0]
	add x13, x9, #2387
	movz x11, #0, lsl #0
	str x11, [x13, #0]
	add x14, x9, #2389
	ldr x11, [x8, #0]
	str x11, [x14, #0]
	ldr x11, [x8, #8]
	str x11, [x14, #8]
	ldr x11, [x8, #16]
	str x11, [x14, #16]
	ldr x11, [x8, #24]
	str x11, [x14, #24]
	ldr x11, [x8, #32]
	str x11, [x14, #32]
	ldr x11, [x8, #40]
	str x11, [x14, #40]
	ldr x11, [x8, #48]
	str x11, [x14, #48]
	ldr x11, [x8, #56]
	str x11, [x14, #56]
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #64, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha512_init_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #128, lsl #0
	ldr x2, [sp, #184]
	add x2, x2, #2256
	movz x3, #197, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha512_update_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #325, lsl #0
	add x3, sp, #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha512_finalize_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #64, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha512_init_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #128, lsl #0
	add x2, sp, #64
	movz x3, #64, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha512_update_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #192, lsl #0
	add x3, sp, #64
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha512_finalize_scratch}
	movz x9, #8, lsl #0
	add x15, sp, #0
	str x9, [x15, #176]
20:
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #64, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha512_init_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #128, lsl #0
	add x2, sp, #64
	movz x3, #64, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha512_update_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #192, lsl #0
	add x3, sp, #64
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha512_finalize_scratch}
	add x15, sp, #0
	ldr x11, [x15, #64]
	str x11, [x15, #296]
	ldr x11, [x15, #72]
	str x11, [x15, #304]
	ldr x11, [x15, #80]
	str x11, [x15, #312]
	ldr x11, [x15, #88]
	str x11, [x15, #320]
	ldr x11, [x15, #96]
	str x11, [x15, #328]
	ldr x11, [x15, #104]
	str x11, [x15, #336]
	ldr x11, [x15, #112]
	str x11, [x15, #344]
	ldr x11, [x15, #120]
	str x11, [x15, #352]
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #64, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha512_init_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #128, lsl #0
	add x2, sp, #64
	movz x3, #64, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha512_update_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #192, lsl #0
	add x3, sp, #64
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha512_finalize_scratch}
	add x15, sp, #0
	ldr x11, [x15, #64]
	str x11, [x15, #360]
	ldr x0, [sp, #184]
	add x6, sp, #296
	add x17, x6, #58
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2560]
	add x17, x6, #50
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2568]
	add x17, x6, #42
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2576]
	add x17, x6, #34
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2584]
	add x17, x6, #26
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2592]
	add x17, x6, #18
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2600]
	add x17, x6, #10
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2608]
	add x17, x6, #2
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2616]
	ldr x5, [x6, #0]
	rev x5, x5
	lsr x5, x5, #48
	str x5, [x0, #2624]
	ldr x1, [x0, #2560]
	ldr x2, [x0, #2568]
	extr x1, x2, x1, #7
	str x1, [x0, #2560]
	ldr x1, [x0, #2568]
	ldr x2, [x0, #2576]
	extr x1, x2, x1, #7
	str x1, [x0, #2568]
	ldr x1, [x0, #2576]
	ldr x2, [x0, #2584]
	extr x1, x2, x1, #7
	str x1, [x0, #2576]
	ldr x1, [x0, #2584]
	ldr x2, [x0, #2592]
	extr x1, x2, x1, #7
	str x1, [x0, #2584]
	ldr x1, [x0, #2592]
	ldr x2, [x0, #2600]
	extr x1, x2, x1, #7
	str x1, [x0, #2592]
	ldr x1, [x0, #2600]
	ldr x2, [x0, #2608]
	extr x1, x2, x1, #7
	str x1, [x0, #2600]
	ldr x1, [x0, #2608]
	ldr x2, [x0, #2616]
	extr x1, x2, x1, #7
	str x1, [x0, #2608]
	ldr x1, [x0, #2616]
	ldr x2, [x0, #2624]
	extr x1, x2, x1, #7
	str x1, [x0, #2616]
	ldr x1, [x0, #2624]
	lsr x1, x1, #7
	str x1, [x0, #2624]
	movz x3, #0, lsl #0
	sub x3, x3, #1
	ldr x1, [x0, #2560]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #58
	str x1, [x17, #0]
	ldr x1, [x0, #2568]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #50
	str x1, [x17, #0]
	ldr x1, [x0, #2576]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #42
	str x1, [x17, #0]
	ldr x1, [x0, #2584]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #34
	str x1, [x17, #0]
	ldr x1, [x0, #2592]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #26
	str x1, [x17, #0]
	ldr x1, [x0, #2600]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #18
	str x1, [x17, #0]
	ldr x1, [x0, #2608]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #10
	str x1, [x17, #0]
	ldr x1, [x0, #2616]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #2
	str x1, [x17, #0]
	ldr x1, [x0, #2624]
	and x1, x1, x3
	lsr x2, x1, #8
	strb w2, [x6, #0]
	strb w1, [x6, #1]
	ldr x0, [sp, #208]
	ldr x1, [sp, #200]
	add x2, sp, #224
	add x3, sp, #296
	ldr x4, [sp, #184]
	bl {vg_ecdsa_p521_sign}
	ldr x9, [sp, #176]
	sub x9, x9, #1
	add x15, sp, #0
	str x9, [x15, #176]
	movz x7, #0, lsl #0
	movz x10, #1, lsl #0
	subs w16, w0, w10
	sbc x11, x7, x7
	and x12, x11, x9
	cbnz x12, 21f
	movz x12, #0, lsl #0
	b 22f
21:
	ldr x9, [sp, #184]
	ldr x10, [sp, #200]
	add x15, sp, #0
	ldr x11, [x15, #64]
	str x11, [x9, #2256]
	ldr x11, [x15, #72]
	str x11, [x9, #2264]
	ldr x11, [x15, #80]
	str x11, [x9, #2272]
	ldr x11, [x15, #88]
	str x11, [x9, #2280]
	ldr x11, [x15, #96]
	str x11, [x9, #2288]
	ldr x11, [x15, #104]
	str x11, [x9, #2296]
	ldr x11, [x15, #112]
	str x11, [x9, #2304]
	ldr x11, [x15, #120]
	str x11, [x9, #2312]
	movz x11, #0, lsl #0
	strb w11, [x9, #2320]
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #64, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha512_init_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #128, lsl #0
	ldr x2, [sp, #184]
	add x2, x2, #2256
	movz x3, #65, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha512_update_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #193, lsl #0
	add x3, sp, #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha512_finalize_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #64, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha512_init_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #128, lsl #0
	add x2, sp, #64
	movz x3, #64, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha512_update_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #192, lsl #0
	add x3, sp, #64
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha512_finalize_scratch}
	movz x12, #1, lsl #0
22:
	cbnz x12, 20b
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #0]
	str x14, [x15, #8]
	str x14, [x15, #16]
	str x14, [x15, #24]
	str x14, [x15, #32]
	str x14, [x15, #40]
	str x14, [x15, #48]
	str x14, [x15, #56]
	str x14, [x15, #64]
	str x14, [x15, #72]
	str x14, [x15, #80]
	str x14, [x15, #88]
	str x14, [x15, #96]
	str x14, [x15, #104]
	str x14, [x15, #112]
	str x14, [x15, #120]
	str x14, [x15, #128]
	str x14, [x15, #136]
	str x14, [x15, #144]
	str x14, [x15, #152]
	str x14, [x15, #160]
	str x14, [x15, #168]
	str x14, [x15, #224]
	str x14, [x15, #232]
	str x14, [x15, #240]
	str x14, [x15, #248]
	str x14, [x15, #256]
	str x14, [x15, #264]
	str x14, [x15, #272]
	str x14, [x15, #280]
	str x14, [x15, #288]
	str x14, [x15, #296]
	str x14, [x15, #304]
	str x14, [x15, #312]
	str x14, [x15, #320]
	str x14, [x15, #328]
	str x14, [x15, #336]
	str x14, [x15, #344]
	str x14, [x15, #352]
	str x14, [x15, #360]
	add sp, sp, #368
	ldr x30, [sp], #16
	ret
	.p2align 6

vg_ecdsa_p521_sha512_sign_sha3:
	.arch_extension sha3
	str x30, [sp, #-16]!
	sub sp, sp, #368
	add x15, sp, #0
	str x0, [x15, #208]
	str x1, [x15, #200]
	str x2, [x15, #192]
	str x3, [x15, #184]
	ldr x1, [sp, #192]
	add x15, sp, #0
	movz x11, #0, lsl #0
	str x11, [x15, #288]
	ldr x11, [x1, #0]
	str x11, [x15, #224]
	ldr x11, [x1, #8]
	str x11, [x15, #232]
	ldr x11, [x1, #16]
	str x11, [x15, #240]
	ldr x11, [x1, #24]
	str x11, [x15, #248]
	ldr x11, [x1, #32]
	str x11, [x15, #256]
	ldr x11, [x1, #40]
	str x11, [x15, #264]
	ldr x11, [x1, #48]
	str x11, [x15, #272]
	ldr x11, [x1, #56]
	str x11, [x15, #280]
	ldr x0, [sp, #184]
	add x6, sp, #224
	add x17, x6, #58
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2560]
	add x17, x6, #50
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2568]
	add x17, x6, #42
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2576]
	add x17, x6, #34
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2584]
	add x17, x6, #26
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2592]
	add x17, x6, #18
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2600]
	add x17, x6, #10
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2608]
	add x17, x6, #2
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2616]
	ldr x5, [x6, #0]
	rev x5, x5
	lsr x5, x5, #48
	str x5, [x0, #2624]
	ldr x1, [x0, #2560]
	ldr x2, [x0, #2568]
	extr x1, x2, x1, #9
	str x1, [x0, #2560]
	ldr x1, [x0, #2568]
	ldr x2, [x0, #2576]
	extr x1, x2, x1, #9
	str x1, [x0, #2568]
	ldr x1, [x0, #2576]
	ldr x2, [x0, #2584]
	extr x1, x2, x1, #9
	str x1, [x0, #2576]
	ldr x1, [x0, #2584]
	ldr x2, [x0, #2592]
	extr x1, x2, x1, #9
	str x1, [x0, #2584]
	ldr x1, [x0, #2592]
	ldr x2, [x0, #2600]
	extr x1, x2, x1, #9
	str x1, [x0, #2592]
	ldr x1, [x0, #2600]
	ldr x2, [x0, #2608]
	extr x1, x2, x1, #9
	str x1, [x0, #2600]
	ldr x1, [x0, #2608]
	ldr x2, [x0, #2616]
	extr x1, x2, x1, #9
	str x1, [x0, #2608]
	ldr x1, [x0, #2616]
	ldr x2, [x0, #2624]
	extr x1, x2, x1, #9
	str x1, [x0, #2616]
	ldr x1, [x0, #2624]
	lsr x1, x1, #9
	str x1, [x0, #2624]
	movz x3, #0, lsl #0
	sub x3, x3, #1
	ldr x1, [x0, #2560]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #58
	str x1, [x17, #0]
	ldr x1, [x0, #2568]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #50
	str x1, [x17, #0]
	ldr x1, [x0, #2576]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #42
	str x1, [x17, #0]
	ldr x1, [x0, #2584]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #34
	str x1, [x17, #0]
	ldr x1, [x0, #2592]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #26
	str x1, [x17, #0]
	ldr x1, [x0, #2600]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #18
	str x1, [x17, #0]
	ldr x1, [x0, #2608]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #10
	str x1, [x17, #0]
	ldr x1, [x0, #2616]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #2
	str x1, [x17, #0]
	ldr x1, [x0, #2624]
	and x1, x1, x3
	lsr x2, x1, #8
	strb w2, [x6, #0]
	strb w1, [x6, #1]
	movz x9, #257, lsl #0
	movk x9, #257, lsl #16
	movk x9, #257, lsl #32
	movk x9, #257, lsl #48
	movz x10, #0, lsl #0
	add x15, sp, #0
	str x9, [x15, #64]
	str x10, [x15, #0]
	str x9, [x15, #72]
	str x10, [x15, #8]
	str x9, [x15, #80]
	str x10, [x15, #16]
	str x9, [x15, #88]
	str x10, [x15, #24]
	str x9, [x15, #96]
	str x10, [x15, #32]
	str x9, [x15, #104]
	str x10, [x15, #40]
	str x9, [x15, #112]
	str x10, [x15, #48]
	str x9, [x15, #120]
	str x10, [x15, #56]
	ldr x9, [sp, #184]
	ldr x10, [sp, #200]
	add x15, sp, #0
	ldr x8, [sp, #192]
	ldr x11, [x15, #64]
	str x11, [x9, #2256]
	ldr x11, [x15, #72]
	str x11, [x9, #2264]
	ldr x11, [x15, #80]
	str x11, [x9, #2272]
	ldr x11, [x15, #88]
	str x11, [x9, #2280]
	ldr x11, [x15, #96]
	str x11, [x9, #2288]
	ldr x11, [x15, #104]
	str x11, [x9, #2296]
	ldr x11, [x15, #112]
	str x11, [x9, #2304]
	ldr x11, [x15, #120]
	str x11, [x9, #2312]
	movz x11, #0, lsl #0
	strb w11, [x9, #2320]
	add x12, x9, #2321
	ldr x11, [x10, #0]
	str x11, [x12, #0]
	ldr x11, [x10, #8]
	str x11, [x12, #8]
	ldr x11, [x10, #16]
	str x11, [x12, #16]
	ldr x11, [x10, #24]
	str x11, [x12, #24]
	ldr x11, [x10, #32]
	str x11, [x12, #32]
	ldr x11, [x10, #40]
	str x11, [x12, #40]
	ldr x11, [x10, #48]
	str x11, [x12, #48]
	ldr x11, [x10, #56]
	str x11, [x12, #56]
	add x13, x10, #58
	add x14, x12, #58
	ldr x11, [x13, #0]
	str x11, [x14, #0]
	add x13, x9, #2387
	movz x11, #0, lsl #0
	str x11, [x13, #0]
	add x14, x9, #2389
	ldr x11, [x8, #0]
	str x11, [x14, #0]
	ldr x11, [x8, #8]
	str x11, [x14, #8]
	ldr x11, [x8, #16]
	str x11, [x14, #16]
	ldr x11, [x8, #24]
	str x11, [x14, #24]
	ldr x11, [x8, #32]
	str x11, [x14, #32]
	ldr x11, [x8, #40]
	str x11, [x14, #40]
	ldr x11, [x8, #48]
	str x11, [x14, #48]
	ldr x11, [x8, #56]
	str x11, [x14, #56]
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #64, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha512_init_scratch_sha3}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #128, lsl #0
	ldr x2, [sp, #184]
	add x2, x2, #2256
	movz x3, #197, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha512_update_scratch_sha3}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #325, lsl #0
	add x3, sp, #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha512_finalize_scratch_sha3}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #64, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha512_init_scratch_sha3}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #128, lsl #0
	add x2, sp, #64
	movz x3, #64, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha512_update_scratch_sha3}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #192, lsl #0
	add x3, sp, #64
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha512_finalize_scratch_sha3}
	ldr x9, [sp, #184]
	ldr x10, [sp, #200]
	add x15, sp, #0
	ldr x8, [sp, #192]
	ldr x11, [x15, #64]
	str x11, [x9, #2256]
	ldr x11, [x15, #72]
	str x11, [x9, #2264]
	ldr x11, [x15, #80]
	str x11, [x9, #2272]
	ldr x11, [x15, #88]
	str x11, [x9, #2280]
	ldr x11, [x15, #96]
	str x11, [x9, #2288]
	ldr x11, [x15, #104]
	str x11, [x9, #2296]
	ldr x11, [x15, #112]
	str x11, [x9, #2304]
	ldr x11, [x15, #120]
	str x11, [x9, #2312]
	movz x11, #1, lsl #0
	strb w11, [x9, #2320]
	add x12, x9, #2321
	ldr x11, [x10, #0]
	str x11, [x12, #0]
	ldr x11, [x10, #8]
	str x11, [x12, #8]
	ldr x11, [x10, #16]
	str x11, [x12, #16]
	ldr x11, [x10, #24]
	str x11, [x12, #24]
	ldr x11, [x10, #32]
	str x11, [x12, #32]
	ldr x11, [x10, #40]
	str x11, [x12, #40]
	ldr x11, [x10, #48]
	str x11, [x12, #48]
	ldr x11, [x10, #56]
	str x11, [x12, #56]
	add x13, x10, #58
	add x14, x12, #58
	ldr x11, [x13, #0]
	str x11, [x14, #0]
	add x13, x9, #2387
	movz x11, #0, lsl #0
	str x11, [x13, #0]
	add x14, x9, #2389
	ldr x11, [x8, #0]
	str x11, [x14, #0]
	ldr x11, [x8, #8]
	str x11, [x14, #8]
	ldr x11, [x8, #16]
	str x11, [x14, #16]
	ldr x11, [x8, #24]
	str x11, [x14, #24]
	ldr x11, [x8, #32]
	str x11, [x14, #32]
	ldr x11, [x8, #40]
	str x11, [x14, #40]
	ldr x11, [x8, #48]
	str x11, [x14, #48]
	ldr x11, [x8, #56]
	str x11, [x14, #56]
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #64, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha512_init_scratch_sha3}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #128, lsl #0
	ldr x2, [sp, #184]
	add x2, x2, #2256
	movz x3, #197, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha512_update_scratch_sha3}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #325, lsl #0
	add x3, sp, #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha512_finalize_scratch_sha3}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #64, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha512_init_scratch_sha3}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #128, lsl #0
	add x2, sp, #64
	movz x3, #64, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha512_update_scratch_sha3}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #192, lsl #0
	add x3, sp, #64
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha512_finalize_scratch_sha3}
	movz x9, #8, lsl #0
	add x15, sp, #0
	str x9, [x15, #176]
20:
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #64, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha512_init_scratch_sha3}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #128, lsl #0
	add x2, sp, #64
	movz x3, #64, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha512_update_scratch_sha3}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #192, lsl #0
	add x3, sp, #64
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha512_finalize_scratch_sha3}
	add x15, sp, #0
	ldr x11, [x15, #64]
	str x11, [x15, #296]
	ldr x11, [x15, #72]
	str x11, [x15, #304]
	ldr x11, [x15, #80]
	str x11, [x15, #312]
	ldr x11, [x15, #88]
	str x11, [x15, #320]
	ldr x11, [x15, #96]
	str x11, [x15, #328]
	ldr x11, [x15, #104]
	str x11, [x15, #336]
	ldr x11, [x15, #112]
	str x11, [x15, #344]
	ldr x11, [x15, #120]
	str x11, [x15, #352]
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #64, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha512_init_scratch_sha3}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #128, lsl #0
	add x2, sp, #64
	movz x3, #64, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha512_update_scratch_sha3}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #192, lsl #0
	add x3, sp, #64
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha512_finalize_scratch_sha3}
	add x15, sp, #0
	ldr x11, [x15, #64]
	str x11, [x15, #360]
	ldr x0, [sp, #184]
	add x6, sp, #296
	add x17, x6, #58
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2560]
	add x17, x6, #50
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2568]
	add x17, x6, #42
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2576]
	add x17, x6, #34
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2584]
	add x17, x6, #26
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2592]
	add x17, x6, #18
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2600]
	add x17, x6, #10
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2608]
	add x17, x6, #2
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2616]
	ldr x5, [x6, #0]
	rev x5, x5
	lsr x5, x5, #48
	str x5, [x0, #2624]
	ldr x1, [x0, #2560]
	ldr x2, [x0, #2568]
	extr x1, x2, x1, #7
	str x1, [x0, #2560]
	ldr x1, [x0, #2568]
	ldr x2, [x0, #2576]
	extr x1, x2, x1, #7
	str x1, [x0, #2568]
	ldr x1, [x0, #2576]
	ldr x2, [x0, #2584]
	extr x1, x2, x1, #7
	str x1, [x0, #2576]
	ldr x1, [x0, #2584]
	ldr x2, [x0, #2592]
	extr x1, x2, x1, #7
	str x1, [x0, #2584]
	ldr x1, [x0, #2592]
	ldr x2, [x0, #2600]
	extr x1, x2, x1, #7
	str x1, [x0, #2592]
	ldr x1, [x0, #2600]
	ldr x2, [x0, #2608]
	extr x1, x2, x1, #7
	str x1, [x0, #2600]
	ldr x1, [x0, #2608]
	ldr x2, [x0, #2616]
	extr x1, x2, x1, #7
	str x1, [x0, #2608]
	ldr x1, [x0, #2616]
	ldr x2, [x0, #2624]
	extr x1, x2, x1, #7
	str x1, [x0, #2616]
	ldr x1, [x0, #2624]
	lsr x1, x1, #7
	str x1, [x0, #2624]
	movz x3, #0, lsl #0
	sub x3, x3, #1
	ldr x1, [x0, #2560]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #58
	str x1, [x17, #0]
	ldr x1, [x0, #2568]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #50
	str x1, [x17, #0]
	ldr x1, [x0, #2576]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #42
	str x1, [x17, #0]
	ldr x1, [x0, #2584]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #34
	str x1, [x17, #0]
	ldr x1, [x0, #2592]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #26
	str x1, [x17, #0]
	ldr x1, [x0, #2600]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #18
	str x1, [x17, #0]
	ldr x1, [x0, #2608]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #10
	str x1, [x17, #0]
	ldr x1, [x0, #2616]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #2
	str x1, [x17, #0]
	ldr x1, [x0, #2624]
	and x1, x1, x3
	lsr x2, x1, #8
	strb w2, [x6, #0]
	strb w1, [x6, #1]
	ldr x0, [sp, #208]
	ldr x1, [sp, #200]
	add x2, sp, #224
	add x3, sp, #296
	ldr x4, [sp, #184]
	bl {vg_ecdsa_p521_sign}
	ldr x9, [sp, #176]
	sub x9, x9, #1
	add x15, sp, #0
	str x9, [x15, #176]
	movz x7, #0, lsl #0
	movz x10, #1, lsl #0
	subs w16, w0, w10
	sbc x11, x7, x7
	and x12, x11, x9
	cbnz x12, 21f
	movz x12, #0, lsl #0
	b 22f
21:
	ldr x9, [sp, #184]
	ldr x10, [sp, #200]
	add x15, sp, #0
	ldr x11, [x15, #64]
	str x11, [x9, #2256]
	ldr x11, [x15, #72]
	str x11, [x9, #2264]
	ldr x11, [x15, #80]
	str x11, [x9, #2272]
	ldr x11, [x15, #88]
	str x11, [x9, #2280]
	ldr x11, [x15, #96]
	str x11, [x9, #2288]
	ldr x11, [x15, #104]
	str x11, [x9, #2296]
	ldr x11, [x15, #112]
	str x11, [x9, #2304]
	ldr x11, [x15, #120]
	str x11, [x9, #2312]
	movz x11, #0, lsl #0
	strb w11, [x9, #2320]
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #64, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha512_init_scratch_sha3}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #128, lsl #0
	ldr x2, [sp, #184]
	add x2, x2, #2256
	movz x3, #65, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha512_update_scratch_sha3}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #193, lsl #0
	add x3, sp, #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha512_finalize_scratch_sha3}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	add x2, sp, #0
	movz x3, #64, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha512_init_scratch_sha3}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #128, lsl #0
	add x2, sp, #64
	movz x3, #64, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_sha512_update_scratch_sha3}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #192
	movz x2, #192, lsl #0
	add x3, sp, #64
	ldr x4, [sp, #184]
	add x4, x4, #384
	bl {vg_hmac_sha512_finalize_scratch_sha3}
	movz x12, #1, lsl #0
22:
	cbnz x12, 20b
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #0]
	str x14, [x15, #8]
	str x14, [x15, #16]
	str x14, [x15, #24]
	str x14, [x15, #32]
	str x14, [x15, #40]
	str x14, [x15, #48]
	str x14, [x15, #56]
	str x14, [x15, #64]
	str x14, [x15, #72]
	str x14, [x15, #80]
	str x14, [x15, #88]
	str x14, [x15, #96]
	str x14, [x15, #104]
	str x14, [x15, #112]
	str x14, [x15, #120]
	str x14, [x15, #128]
	str x14, [x15, #136]
	str x14, [x15, #144]
	str x14, [x15, #152]
	str x14, [x15, #160]
	str x14, [x15, #168]
	str x14, [x15, #224]
	str x14, [x15, #232]
	str x14, [x15, #240]
	str x14, [x15, #248]
	str x14, [x15, #256]
	str x14, [x15, #264]
	str x14, [x15, #272]
	str x14, [x15, #280]
	str x14, [x15, #288]
	str x14, [x15, #296]
	str x14, [x15, #304]
	str x14, [x15, #312]
	str x14, [x15, #320]
	str x14, [x15, #328]
	str x14, [x15, #336]
	str x14, [x15, #344]
	str x14, [x15, #352]
	str x14, [x15, #360]
	add sp, sp, #368
	ldr x30, [sp], #16
	ret
	.arch_extension nosha3
	.p2align 6
