// The functions of `src/seed.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_seed_expand_key:
	sub sp, sp, #976
	add x2, sp, #0
	add x5, x2, #0
	str x19, [x5, #896]
	str x20, [x5, #904]
	str x21, [x5, #912]
	str x22, [x5, #920]
	str x23, [x5, #928]
	str x24, [x5, #936]
	str x25, [x5, #944]
	str x26, [x5, #952]
	str x27, [x5, #960]
	str x28, [x5, #968]
	ldr w14, [x0, #0]
	rev w14, w14
	lsl x14, x14, #32
	ldr w3, [x0, #4]
	rev w3, w3
	orr x3, x3, x14
	ldr w14, [x0, #8]
	rev w14, w14
	lsl x14, x14, #32
	ldr w4, [x0, #12]
	rev w4, w4
	orr x4, x4, x14
	lsr x14, x3, #32
	lsr x15, x4, #32
	add w14, w14, w15
	movz w16, #31161, lsl #0
	movk w16, #40503, lsl #16
	sub w14, w14, w16
	str w14, [x5, #384]
	sub w14, w3, w4
	add w14, w14, w16
	str w14, [x5, #388]
	ror x3, x3, #8
	lsr x14, x3, #32
	lsr x15, x4, #32
	add w14, w14, w15
	movz w16, #62323, lsl #0
	movk w16, #15470, lsl #16
	sub w14, w14, w16
	str w14, [x5, #392]
	sub w14, w3, w4
	add w14, w14, w16
	str w14, [x5, #396]
	ror x4, x4, #56
	lsr x14, x3, #32
	lsr x15, x4, #32
	add w14, w14, w15
	movz w16, #59110, lsl #0
	movk w16, #30941, lsl #16
	sub w14, w14, w16
	str w14, [x5, #400]
	sub w14, w3, w4
	add w14, w14, w16
	str w14, [x5, #404]
	ror x3, x3, #8
	lsr x14, x3, #32
	lsr x15, x4, #32
	add w14, w14, w15
	movz w16, #52684, lsl #0
	movk w16, #61883, lsl #16
	sub w14, w14, w16
	str w14, [x5, #408]
	sub w14, w3, w4
	add w14, w14, w16
	str w14, [x5, #412]
	ror x4, x4, #56
	lsr x14, x3, #32
	lsr x15, x4, #32
	add w14, w14, w15
	movz w16, #39833, lsl #0
	movk w16, #58231, lsl #16
	sub w14, w14, w16
	str w14, [x5, #416]
	sub w14, w3, w4
	add w14, w14, w16
	str w14, [x5, #420]
	ror x3, x3, #8
	lsr x14, x3, #32
	lsr x15, x4, #32
	add w14, w14, w15
	movz w16, #14131, lsl #0
	movk w16, #50927, lsl #16
	sub w14, w14, w16
	str w14, [x5, #424]
	sub w14, w3, w4
	add w14, w14, w16
	str w14, [x5, #428]
	ror x4, x4, #56
	lsr x14, x3, #32
	lsr x15, x4, #32
	add w14, w14, w15
	movz w16, #28263, lsl #0
	movk w16, #36318, lsl #16
	sub w14, w14, w16
	str w14, [x5, #432]
	sub w14, w3, w4
	add w14, w14, w16
	str w14, [x5, #436]
	ror x3, x3, #8
	lsr x14, x3, #32
	lsr x15, x4, #32
	add w14, w14, w15
	movz w16, #56527, lsl #0
	movk w16, #7100, lsl #16
	sub w14, w14, w16
	str w14, [x5, #440]
	sub w14, w3, w4
	add w14, w14, w16
	str w14, [x5, #444]
	ror x4, x4, #56
	lsr x14, x3, #32
	lsr x15, x4, #32
	add w14, w14, w15
	movz w16, #47518, lsl #0
	movk w16, #14201, lsl #16
	sub w14, w14, w16
	str w14, [x5, #448]
	sub w14, w3, w4
	add w14, w14, w16
	str w14, [x5, #452]
	ror x3, x3, #8
	lsr x14, x3, #32
	lsr x15, x4, #32
	add w14, w14, w15
	movz w16, #29500, lsl #0
	movk w16, #28403, lsl #16
	sub w14, w14, w16
	str w14, [x5, #456]
	sub w14, w3, w4
	add w14, w14, w16
	str w14, [x5, #460]
	ror x4, x4, #56
	lsr x14, x3, #32
	lsr x15, x4, #32
	add w14, w14, w15
	movz w16, #59000, lsl #0
	movk w16, #56806, lsl #16
	sub w14, w14, w16
	str w14, [x5, #464]
	sub w14, w3, w4
	add w14, w14, w16
	str w14, [x5, #468]
	ror x3, x3, #8
	lsr x14, x3, #32
	lsr x15, x4, #32
	add w14, w14, w15
	movz w16, #52465, lsl #0
	movk w16, #48077, lsl #16
	sub w14, w14, w16
	str w14, [x5, #472]
	sub w14, w3, w4
	add w14, w14, w16
	str w14, [x5, #476]
	ror x4, x4, #56
	lsr x14, x3, #32
	lsr x15, x4, #32
	add w14, w14, w15
	movz w16, #39395, lsl #0
	movk w16, #30619, lsl #16
	sub w14, w14, w16
	str w14, [x5, #480]
	sub w14, w3, w4
	add w14, w14, w16
	str w14, [x5, #484]
	ror x3, x3, #8
	lsr x14, x3, #32
	lsr x15, x4, #32
	add w14, w14, w15
	movz w16, #13254, lsl #0
	movk w16, #61239, lsl #16
	sub w14, w14, w16
	str w14, [x5, #488]
	sub w14, w3, w4
	add w14, w14, w16
	str w14, [x5, #492]
	ror x4, x4, #56
	lsr x14, x3, #32
	lsr x15, x4, #32
	add w14, w14, w15
	movz w16, #26509, lsl #0
	movk w16, #56942, lsl #16
	sub w14, w14, w16
	str w14, [x5, #496]
	sub w14, w3, w4
	add w14, w14, w16
	str w14, [x5, #500]
	ror x3, x3, #8
	lsr x14, x3, #32
	lsr x15, x4, #32
	add w14, w14, w15
	movz w16, #53019, lsl #0
	movk w16, #48348, lsl #16
	sub w14, w14, w16
	str w14, [x5, #504]
	sub w14, w3, w4
	add w14, w14, w16
	str w14, [x5, #508]
	ror x4, x4, #56
	movz x3, #2, lsl #0
20:
	ldr x6, [x5, #384]
	ldr x7, [x5, #392]
	ldr x8, [x5, #400]
	ldr x9, [x5, #408]
	ldr x10, [x5, #416]
	ldr x11, [x5, #424]
	ldr x12, [x5, #432]
	ldr x13, [x5, #440]
	movz x17, #21845, lsl #0
	movk x17, #21845, lsl #16
	movk x17, #21845, lsl #32
	movk x17, #21845, lsl #48
	movz x19, #13107, lsl #0
	movk x19, #13107, lsl #16
	movk x19, #13107, lsl #32
	movk x19, #13107, lsl #48
	movz x20, #3855, lsl #0
	movk x20, #3855, lsl #16
	movk x20, #3855, lsl #32
	movk x20, #3855, lsl #48
	lsr x21, x6, #1
	eor x21, x21, x7
	and x21, x21, x17
	eor x7, x7, x21
	ror x21, x21, #63
	eor x6, x6, x21
	lsr x21, x8, #1
	eor x21, x21, x9
	and x21, x21, x17
	eor x9, x9, x21
	ror x21, x21, #63
	eor x8, x8, x21
	lsr x21, x10, #1
	eor x21, x21, x11
	and x21, x21, x17
	eor x11, x11, x21
	ror x21, x21, #63
	eor x10, x10, x21
	lsr x21, x12, #1
	eor x21, x21, x13
	and x21, x21, x17
	eor x13, x13, x21
	ror x21, x21, #63
	eor x12, x12, x21
	lsr x21, x6, #2
	eor x21, x21, x8
	and x21, x21, x19
	eor x8, x8, x21
	ror x21, x21, #62
	eor x6, x6, x21
	lsr x21, x7, #2
	eor x21, x21, x9
	and x21, x21, x19
	eor x9, x9, x21
	ror x21, x21, #62
	eor x7, x7, x21
	lsr x21, x10, #2
	eor x21, x21, x12
	and x21, x21, x19
	eor x12, x12, x21
	ror x21, x21, #62
	eor x10, x10, x21
	lsr x21, x11, #2
	eor x21, x21, x13
	and x21, x21, x19
	eor x13, x13, x21
	ror x21, x21, #62
	eor x11, x11, x21
	lsr x21, x6, #4
	eor x21, x21, x10
	and x21, x21, x20
	eor x10, x10, x21
	ror x21, x21, #60
	eor x6, x6, x21
	lsr x21, x7, #4
	eor x21, x21, x11
	and x21, x21, x20
	eor x11, x11, x21
	ror x21, x21, #60
	eor x7, x7, x21
	lsr x21, x8, #4
	eor x21, x21, x12
	and x21, x21, x20
	eor x12, x12, x21
	ror x21, x21, #60
	eor x8, x8, x21
	lsr x21, x9, #4
	eor x21, x21, x13
	and x21, x21, x20
	eor x13, x13, x21
	ror x21, x21, #60
	eor x9, x9, x21
	add x14, x6, #0
	add x15, x7, #0
	add x16, x8, #0
	add x17, x9, #0
	add x19, x10, #0
	add x20, x11, #0
	add x23, x12, #0
	add x24, x13, #0
	add x6, x14, #0
	eor x6, x6, x15
	eor x6, x6, x17
	add x7, x16, #0
	eor x7, x7, x17
	eor x7, x7, x23
	eor x7, x7, x24
	add x8, x19, #0
	eor x8, x8, x20
	eor x8, x8, x24
	add x9, x15, #0
	eor x9, x9, x16
	eor x9, x9, x17
	eor x9, x9, x20
	add x10, x15, #0
	eor x10, x10, x16
	eor x10, x10, x19
	add x11, x17, #0
	eor x11, x11, x19
	add x12, x16, #0
	eor x12, x12, x17
	eor x12, x12, x19
	eor x12, x12, x20
	add x13, x19, #0
	eor x13, x13, x20
	eor x13, x13, x23
	movz x28, #0, lsl #0
	sub x28, x28, #1
	eor x14, x10, x8
	eor x15, x13, x7
	eor x16, x13, x10
	eor x17, x13, x8
	eor x11, x12, x11
	eor x19, x11, x6
	eor x10, x19, x10
	eor x20, x15, x14
	eor x21, x19, x13
	eor x7, x19, x7
	eor x22, x7, x17
	eor x9, x9, x20
	eor x8, x9, x8
	eor x9, x9, x12
	eor x12, x8, x6
	eor x23, x8, x11
	eor x24, x9, x16
	eor x25, x6, x24
	eor x26, x23, x24
	eor x27, x23, x17
	eor x11, x11, x24
	str x27, [x5, #0]
	eor x27, x15, x11
	eor x13, x13, x11
	str x13, [x5, #8]
	and x13, x20, x8
	str x20, [x5, #16]
	and x20, x22, x12
	eor x20, x20, x13
	str x22, [x5, #24]
	and x22, x10, x6
	eor x22, x22, x13
	and x13, x15, x11
	str x15, [x5, #32]
	and x15, x7, x19
	eor x15, x15, x13
	str x7, [x5, #40]
	and x7, x21, x25
	eor x7, x7, x13
	and x13, x16, x24
	str x16, [x5, #48]
	and x16, x14, x26
	eor x16, x16, x13
	str x14, [x5, #56]
	and x14, x17, x23
	eor x14, x14, x13
	eor x20, x20, x16
	eor x22, x22, x14
	eor x15, x15, x16
	eor x7, x7, x14
	eor x20, x20, x9
	ldr x9, [x5, #0]
	eor x22, x22, x9
	eor x15, x15, x27
	ldr x27, [x5, #8]
	eor x7, x7, x27
	eor x27, x20, x22
	and x20, x20, x15
	eor x9, x7, x20
	and x14, x27, x9
	eor x14, x14, x22
	eor x16, x15, x7
	eor x22, x22, x20
	and x22, x22, x16
	eor x22, x22, x7
	eor x15, x15, x22
	eor x16, x9, x22
	and x7, x7, x16
	eor x15, x7, x15
	eor x9, x9, x7
	and x9, x14, x9
	eor x27, x27, x9
	eor x9, x27, x15
	eor x7, x14, x22
	eor x16, x14, x27
	eor x20, x22, x15
	eor x13, x7, x9
	and x8, x20, x8
	and x12, x15, x12
	and x6, x22, x6
	and x11, x16, x11
	and x19, x27, x19
	and x25, x14, x25
	and x24, x7, x24
	and x26, x13, x26
	and x23, x9, x23
	str x12, [x5, #8]
	ldr x12, [x5, #16]
	and x20, x20, x12
	ldr x12, [x5, #24]
	and x15, x15, x12
	and x22, x22, x10
	ldr x10, [x5, #32]
	and x16, x16, x10
	ldr x10, [x5, #40]
	and x27, x27, x10
	and x14, x14, x21
	ldr x21, [x5, #48]
	and x7, x7, x21
	ldr x21, [x5, #56]
	and x13, x13, x21
	and x9, x9, x17
	eor x7, x7, x13
	eor x22, x15, x22
	eor x27, x25, x27
	eor x20, x20, x15
	eor x15, x6, x16
	eor x6, x6, x25
	eor x23, x26, x23
	eor x8, x8, x11
	eor x24, x24, x26
	eor x13, x13, x9
	eor x16, x16, x27
	eor x15, x15, x8
	eor x9, x19, x7
	eor x11, x11, x24
	eor x7, x7, x15
	eor x14, x14, x15
	eor x23, x23, x9
	eor x20, x20, x9
	eor x19, x19, x11
	eor x14, x14, x23
	ldr x9, [x5, #8]
	eor x9, x9, x20
	eor x11, x11, x20
	eor x16, x16, x23
	eor x16, x16, x28
	eor x27, x27, x7
	eor x27, x27, x28
	eor x7, x19, x14
	eor x10, x8, x9
	eor x9, x6, x9
	eor x8, x22, x14
	eor x12, x19, x10
	eor x12, x12, x28
	eor x13, x13, x7
	eor x13, x13, x28
	str x13, [x5, #8]
	add x13, x11, #0
	ldr x11, [x5, #8]
	add x7, x16, #0
	add x6, x27, #0
	add x14, x6, #0
	add x15, x7, #0
	add x16, x8, #0
	add x17, x9, #0
	add x19, x10, #0
	add x20, x11, #0
	add x23, x12, #0
	add x24, x13, #0
	movz x25, #255, lsl #0
	movk x25, #255, lsl #16
	movk x25, #255, lsl #32
	movk x25, #255, lsl #48
	movz x26, #65280, lsl #0
	movk x26, #65280, lsl #16
	movk x26, #65280, lsl #32
	movk x26, #65280, lsl #48
	and x6, x15, x26
	and x21, x16, x25
	eor x6, x6, x21
	and x21, x17, x26
	eor x6, x6, x21
	and x21, x19, x25
	eor x6, x6, x21
	and x21, x20, x25
	eor x6, x6, x21
	and x21, x23, x25
	eor x6, x6, x21
	and x7, x15, x26
	and x21, x16, x25
	eor x7, x7, x21
	eor x7, x7, x19
	and x21, x20, x26
	eor x7, x7, x21
	eor x7, x7, x23
	eor x7, x7, x24
	add x8, x14, #0
	and x21, x15, x25
	eor x8, x8, x21
	and x21, x16, x26
	eor x8, x8, x21
	and x21, x17, x26
	eor x8, x8, x21
	eor x8, x8, x19
	eor x8, x8, x23
	add x9, x14, #0
	and x21, x15, x26
	eor x9, x9, x21
	and x21, x16, x25
	eor x9, x9, x21
	and x21, x17, x26
	eor x9, x9, x21
	eor x9, x9, x19
	eor x9, x9, x20
	eor x9, x9, x23
	and x21, x24, x25
	eor x9, x9, x21
	and x10, x14, x25
	and x21, x16, x25
	eor x10, x10, x21
	eor x10, x10, x17
	and x21, x19, x25
	eor x10, x10, x21
	eor x10, x10, x23
	and x21, x24, x26
	eor x10, x10, x21
	and x11, x14, x25
	and x21, x15, x25
	eor x11, x11, x21
	eor x11, x11, x17
	and x21, x19, x26
	eor x11, x11, x21
	eor x11, x11, x20
	eor x11, x11, x23
	and x12, x14, x25
	and x21, x15, x26
	eor x12, x12, x21
	and x21, x16, x26
	eor x12, x12, x21
	and x21, x17, x26
	eor x12, x12, x21
	and x21, x19, x25
	eor x12, x12, x21
	and x21, x20, x25
	eor x12, x12, x21
	eor x12, x12, x23
	and x13, x15, x25
	eor x13, x13, x17
	and x21, x23, x25
	eor x13, x13, x21
	and x21, x24, x25
	eor x13, x13, x21
	movz x17, #21845, lsl #0
	movk x17, #21845, lsl #16
	movk x17, #21845, lsl #32
	movk x17, #21845, lsl #48
	movz x19, #13107, lsl #0
	movk x19, #13107, lsl #16
	movk x19, #13107, lsl #32
	movk x19, #13107, lsl #48
	movz x20, #3855, lsl #0
	movk x20, #3855, lsl #16
	movk x20, #3855, lsl #32
	movk x20, #3855, lsl #48
	lsr x21, x6, #1
	eor x21, x21, x7
	and x21, x21, x17
	eor x7, x7, x21
	ror x21, x21, #63
	eor x6, x6, x21
	lsr x21, x8, #1
	eor x21, x21, x9
	and x21, x21, x17
	eor x9, x9, x21
	ror x21, x21, #63
	eor x8, x8, x21
	lsr x21, x10, #1
	eor x21, x21, x11
	and x21, x21, x17
	eor x11, x11, x21
	ror x21, x21, #63
	eor x10, x10, x21
	lsr x21, x12, #1
	eor x21, x21, x13
	and x21, x21, x17
	eor x13, x13, x21
	ror x21, x21, #63
	eor x12, x12, x21
	lsr x21, x6, #2
	eor x21, x21, x8
	and x21, x21, x19
	eor x8, x8, x21
	ror x21, x21, #62
	eor x6, x6, x21
	lsr x21, x7, #2
	eor x21, x21, x9
	and x21, x21, x19
	eor x9, x9, x21
	ror x21, x21, #62
	eor x7, x7, x21
	lsr x21, x10, #2
	eor x21, x21, x12
	and x21, x21, x19
	eor x12, x12, x21
	ror x21, x21, #62
	eor x10, x10, x21
	lsr x21, x11, #2
	eor x21, x21, x13
	and x21, x21, x19
	eor x13, x13, x21
	ror x21, x21, #62
	eor x11, x11, x21
	lsr x21, x6, #4
	eor x21, x21, x10
	and x21, x21, x20
	eor x10, x10, x21
	ror x21, x21, #60
	eor x6, x6, x21
	lsr x21, x7, #4
	eor x21, x21, x11
	and x21, x21, x20
	eor x11, x11, x21
	ror x21, x21, #60
	eor x7, x7, x21
	lsr x21, x8, #4
	eor x21, x21, x12
	and x21, x21, x20
	eor x12, x12, x21
	ror x21, x21, #60
	eor x8, x8, x21
	lsr x21, x9, #4
	eor x21, x21, x13
	and x21, x21, x20
	eor x13, x13, x21
	ror x21, x21, #60
	eor x9, x9, x21
	movz x14, #53244, lsl #0
	movk x14, #53244, lsl #16
	movk x14, #53244, lsl #32
	movk x14, #53244, lsl #48
	movz x15, #16371, lsl #0
	movk x15, #243, lsl #16
	movk x15, #16371, lsl #32
	movk x15, #243, lsl #48
	movz x19, #0, lsl #0
	movk x19, #16128, lsl #16
	movk x19, #16128, lsl #48
	movz x16, #64719, lsl #0
	movk x16, #64719, lsl #32
	movz x23, #0, lsl #0
	movk x23, #64719, lsl #16
	movk x23, #64719, lsl #48
	movz x17, #63, lsl #0
	movk x17, #63, lsl #32
	movz x24, #62208, lsl #0
	movk x24, #62271, lsl #16
	movk x24, #62208, lsl #32
	movk x24, #62271, lsl #48
	movz x25, #59179, lsl #0
	movk x25, #59179, lsl #16
	movk x25, #59179, lsl #32
	movk x25, #59179, lsl #48
	and x22, x6, x14
	ror x21, x6, #8
	and x21, x21, x15
	eor x22, x22, x21
	ror x21, x6, #40
	and x21, x21, x19
	eor x22, x22, x21
	ror x21, x6, #16
	and x21, x21, x16
	eor x22, x22, x21
	ror x21, x6, #48
	and x21, x21, x23
	eor x22, x22, x21
	ror x21, x6, #24
	and x21, x21, x17
	eor x22, x22, x21
	ror x21, x6, #56
	and x21, x21, x24
	eor x22, x22, x21
	eor x22, x22, x25
	str x22, [x5, #384]
	and x22, x7, x14
	ror x21, x7, #8
	and x21, x21, x15
	eor x22, x22, x21
	ror x21, x7, #40
	and x21, x21, x19
	eor x22, x22, x21
	ror x21, x7, #16
	and x21, x21, x16
	eor x22, x22, x21
	ror x21, x7, #48
	and x21, x21, x23
	eor x22, x22, x21
	ror x21, x7, #24
	and x21, x21, x17
	eor x22, x22, x21
	ror x21, x7, #56
	and x21, x21, x24
	eor x22, x22, x21
	eor x22, x22, x25
	str x22, [x5, #392]
	and x22, x8, x14
	ror x21, x8, #8
	and x21, x21, x15
	eor x22, x22, x21
	ror x21, x8, #40
	and x21, x21, x19
	eor x22, x22, x21
	ror x21, x8, #16
	and x21, x21, x16
	eor x22, x22, x21
	ror x21, x8, #48
	and x21, x21, x23
	eor x22, x22, x21
	ror x21, x8, #24
	and x21, x21, x17
	eor x22, x22, x21
	ror x21, x8, #56
	and x21, x21, x24
	eor x22, x22, x21
	eor x22, x22, x25
	str x22, [x5, #400]
	and x22, x9, x14
	ror x21, x9, #8
	and x21, x21, x15
	eor x22, x22, x21
	ror x21, x9, #40
	and x21, x21, x19
	eor x22, x22, x21
	ror x21, x9, #16
	and x21, x21, x16
	eor x22, x22, x21
	ror x21, x9, #48
	and x21, x21, x23
	eor x22, x22, x21
	ror x21, x9, #24
	and x21, x21, x17
	eor x22, x22, x21
	ror x21, x9, #56
	and x21, x21, x24
	eor x22, x22, x21
	eor x22, x22, x25
	str x22, [x5, #408]
	and x22, x10, x14
	ror x21, x10, #8
	and x21, x21, x15
	eor x22, x22, x21
	ror x21, x10, #40
	and x21, x21, x19
	eor x22, x22, x21
	ror x21, x10, #16
	and x21, x21, x16
	eor x22, x22, x21
	ror x21, x10, #48
	and x21, x21, x23
	eor x22, x22, x21
	ror x21, x10, #24
	and x21, x21, x17
	eor x22, x22, x21
	ror x21, x10, #56
	and x21, x21, x24
	eor x22, x22, x21
	eor x22, x22, x25
	str x22, [x5, #416]
	and x22, x11, x14
	ror x21, x11, #8
	and x21, x21, x15
	eor x22, x22, x21
	ror x21, x11, #40
	and x21, x21, x19
	eor x22, x22, x21
	ror x21, x11, #16
	and x21, x21, x16
	eor x22, x22, x21
	ror x21, x11, #48
	and x21, x21, x23
	eor x22, x22, x21
	ror x21, x11, #24
	and x21, x21, x17
	eor x22, x22, x21
	ror x21, x11, #56
	and x21, x21, x24
	eor x22, x22, x21
	eor x22, x22, x25
	str x22, [x5, #424]
	and x22, x12, x14
	ror x21, x12, #8
	and x21, x21, x15
	eor x22, x22, x21
	ror x21, x12, #40
	and x21, x21, x19
	eor x22, x22, x21
	ror x21, x12, #16
	and x21, x21, x16
	eor x22, x22, x21
	ror x21, x12, #48
	and x21, x21, x23
	eor x22, x22, x21
	ror x21, x12, #24
	and x21, x21, x17
	eor x22, x22, x21
	ror x21, x12, #56
	and x21, x21, x24
	eor x22, x22, x21
	eor x22, x22, x25
	str x22, [x5, #432]
	and x22, x13, x14
	ror x21, x13, #8
	and x21, x21, x15
	eor x22, x22, x21
	ror x21, x13, #40
	and x21, x21, x19
	eor x22, x22, x21
	ror x21, x13, #16
	and x21, x21, x16
	eor x22, x22, x21
	ror x21, x13, #48
	and x21, x21, x23
	eor x22, x22, x21
	ror x21, x13, #24
	and x21, x21, x17
	eor x22, x22, x21
	ror x21, x13, #56
	and x21, x21, x24
	eor x22, x22, x21
	eor x22, x22, x25
	str x22, [x5, #440]
	ldr w14, [x5, #384]
	str w14, [x1, #0]
	ldr w14, [x5, #388]
	str w14, [x1, #4]
	ldr w14, [x5, #392]
	str w14, [x1, #8]
	ldr w14, [x5, #396]
	str w14, [x1, #12]
	ldr w14, [x5, #400]
	str w14, [x1, #16]
	ldr w14, [x5, #404]
	str w14, [x1, #20]
	ldr w14, [x5, #408]
	str w14, [x1, #24]
	ldr w14, [x5, #412]
	str w14, [x1, #28]
	ldr w14, [x5, #416]
	str w14, [x1, #32]
	ldr w14, [x5, #420]
	str w14, [x1, #36]
	ldr w14, [x5, #424]
	str w14, [x1, #40]
	ldr w14, [x5, #428]
	str w14, [x1, #44]
	ldr w14, [x5, #432]
	str w14, [x1, #48]
	ldr w14, [x5, #436]
	str w14, [x1, #52]
	ldr w14, [x5, #440]
	str w14, [x1, #56]
	ldr w14, [x5, #444]
	str w14, [x1, #60]
	add x1, x1, #64
	sub x3, x3, #1
	cbnz x3, 21f
	b 22f
21:
	ldr w14, [x5, #448]
	str w14, [x5, #384]
	ldr w14, [x5, #452]
	str w14, [x5, #388]
	ldr w14, [x5, #456]
	str w14, [x5, #392]
	ldr w14, [x5, #460]
	str w14, [x5, #396]
	ldr w14, [x5, #464]
	str w14, [x5, #400]
	ldr w14, [x5, #468]
	str w14, [x5, #404]
	ldr w14, [x5, #472]
	str w14, [x5, #408]
	ldr w14, [x5, #476]
	str w14, [x5, #412]
	ldr w14, [x5, #480]
	str w14, [x5, #416]
	ldr w14, [x5, #484]
	str w14, [x5, #420]
	ldr w14, [x5, #488]
	str w14, [x5, #424]
	ldr w14, [x5, #492]
	str w14, [x5, #428]
	ldr w14, [x5, #496]
	str w14, [x5, #432]
	ldr w14, [x5, #500]
	str w14, [x5, #436]
	ldr w14, [x5, #504]
	str w14, [x5, #440]
	ldr w14, [x5, #508]
	str w14, [x5, #444]
22:
	cbnz x3, 20b
	ldr x19, [x5, #896]
	ldr x20, [x5, #904]
	ldr x21, [x5, #912]
	ldr x22, [x5, #920]
	ldr x23, [x5, #928]
	ldr x24, [x5, #936]
	ldr x25, [x5, #944]
	ldr x26, [x5, #952]
	ldr x27, [x5, #960]
	ldr x28, [x5, #968]
	movz x17, #0, lsl #0
	add x16, sp, #0
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	stp x17, x17, [x16, #192]
	stp x17, x17, [x16, #208]
	stp x17, x17, [x16, #224]
	stp x17, x17, [x16, #240]
	stp x17, x17, [x16, #256]
	stp x17, x17, [x16, #272]
	stp x17, x17, [x16, #288]
	stp x17, x17, [x16, #304]
	stp x17, x17, [x16, #320]
	stp x17, x17, [x16, #336]
	stp x17, x17, [x16, #352]
	stp x17, x17, [x16, #368]
	stp x17, x17, [x16, #384]
	stp x17, x17, [x16, #400]
	stp x17, x17, [x16, #416]
	stp x17, x17, [x16, #432]
	stp x17, x17, [x16, #448]
	stp x17, x17, [x16, #464]
	stp x17, x17, [x16, #480]
	stp x17, x17, [x16, #496]
	add x16, sp, #512
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	stp x17, x17, [x16, #192]
	stp x17, x17, [x16, #208]
	stp x17, x17, [x16, #224]
	stp x17, x17, [x16, #240]
	stp x17, x17, [x16, #256]
	stp x17, x17, [x16, #272]
	stp x17, x17, [x16, #288]
	stp x17, x17, [x16, #304]
	stp x17, x17, [x16, #320]
	stp x17, x17, [x16, #336]
	stp x17, x17, [x16, #352]
	stp x17, x17, [x16, #368]
	stp x17, x17, [x16, #384]
	stp x17, x17, [x16, #400]
	stp x17, x17, [x16, #416]
	stp x17, x17, [x16, #432]
	stp x17, x17, [x16, #448]
	add sp, sp, #976
	movz x4, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	ret
	.p2align 6

vg_seed_ecb_encrypt:
	sub sp, sp, #1456
	add x3, sp, #0
	add x13, x2, #1
	lsr x13, x13, #3
	cbz x13, 20f
	str x30, [sp, #-16]!
	bl {vg_seed_encrypt_blocks}
	ldr x30, [sp], #16
	b 21f
20:
	add x5, x3, #0
	str x19, [x5, #1360]
	str x20, [x5, #1368]
	str x21, [x5, #1376]
	str x22, [x5, #1384]
	str x23, [x5, #1392]
	str x24, [x5, #1400]
	str x25, [x5, #1408]
	str x26, [x5, #1416]
	str x27, [x5, #1424]
	str x28, [x5, #1432]
	add x23, x1, #0
	add x24, x2, #0
	ldr x6, [x0, #0]
	str x6, [x5, #1232]
	ldr x6, [x0, #8]
	str x6, [x5, #1240]
	ldr x6, [x0, #16]
	str x6, [x5, #1248]
	ldr x6, [x0, #24]
	str x6, [x5, #1256]
	ldr x6, [x0, #32]
	str x6, [x5, #1264]
	ldr x6, [x0, #40]
	str x6, [x5, #1272]
	ldr x6, [x0, #48]
	str x6, [x5, #1280]
	ldr x6, [x0, #56]
	str x6, [x5, #1288]
	ldr x6, [x0, #64]
	str x6, [x5, #1296]
	ldr x6, [x0, #72]
	str x6, [x5, #1304]
	ldr x6, [x0, #80]
	str x6, [x5, #1312]
	ldr x6, [x0, #88]
	str x6, [x5, #1320]
	ldr x6, [x0, #96]
	str x6, [x5, #1328]
	ldr x6, [x0, #104]
	str x6, [x5, #1336]
	ldr x6, [x0, #112]
	str x6, [x5, #1344]
	ldr x6, [x0, #120]
	str x6, [x5, #1352]
	cbz x24, 22f
24:
	lsr x13, x24, #0
	cbnz x13, 25f
	add x16, x24, #0
	b 26f
25:
	movz x16, #1, lsl #0
26:
	add x14, x5, #0
	add x14, x14, #976
	add x15, x23, #0
	add x17, x16, #0
27:
	ldr x8, [x15, #0]
	str x8, [x14, #0]
	ldr x8, [x15, #8]
	str x8, [x14, #8]
	add x14, x14, #16
	add x15, x15, #16
	sub x17, x17, #1
	cbnz x17, 27b
	movz x6, #34217, lsl #0
	movk x6, #54230, lsl #16
	movk x6, #7508, lsl #32
	movk x6, #9644, lsl #48
	movz x7, #17245, lsl #0
	movk x7, #7704, lsl #16
	movk x7, #64593, lsl #32
	movk x7, #25546, lsl #48
	mov v16.d[0], x6
	mov v16.d[1], x7
	movz x6, #17448, lsl #0
	movk x6, #40224, lsl #16
	movk x6, #58080, lsl #32
	movk x6, #6088, lsl #48
	movz x7, #36773, lsl #0
	movk x7, #31491, lsl #16
	movk x7, #5051, lsl #32
	movk x7, #61138, lsl #48
	mov v17.d[0], x6
	mov v17.d[1], x7
	movz x6, #35952, lsl #0
	movk x6, #43071, lsl #16
	movk x6, #56626, lsl #32
	movk x6, #29942, lsl #48
	movz x7, #38380, lsl #0
	movk x7, #22283, lsl #16
	movk x7, #23388, lsl #32
	movk x7, #445, lsl #48
	mov v18.d[0], x6
	mov v18.d[1], x7
	movz x6, #7204, lsl #0
	movk x6, #39027, lsl #16
	movk x6, #52240, lsl #32
	movk x6, #55794, lsl #48
	movz x7, #59180, lsl #0
	movk x7, #33650, lsl #16
	movk x7, #53659, lsl #32
	movk x7, #51590, lsl #48
	mov v19.d[0], x6
	mov v19.d[1], x7
	movz x6, #20576, lsl #0
	movk x6, #60323, lsl #16
	movk x6, #46605, lsl #32
	movk x6, #20382, lsl #48
	movz x7, #23223, lsl #0
	movk x7, #30918, lsl #16
	movk x7, #4774, lsl #32
	movk x7, #54703, lsl #48
	mov v20.d[0], x6
	mov v20.d[1], x7
	movz x6, #50017, lsl #0
	movk x6, #16820, lsl #16
	movk x6, #32082, lsl #32
	movk x6, #2189, lsl #48
	movz x7, #39199, lsl #0
	movk x7, #6400, lsl #16
	movk x7, #21252, lsl #32
	movk x7, #57847, lsl #48
	mov v21.d[0], x6
	mov v21.d[1], x7
	movz x6, #30461, lsl #0
	movk x6, #10031, lsl #16
	movk x6, #35760, lsl #32
	movk x6, #43790, lsl #48
	movz x7, #28322, lsl #0
	movk x7, #19859, lsl #16
	movk x7, #31849, lsl #32
	movk x7, #2569, lsl #48
	mov v22.d[0], x6
	mov v22.d[1], x7
	movz x6, #61375, lsl #0
	movk x6, #50675, lsl #16
	movk x6, #5255, lsl #32
	movk x6, #25854, lsl #48
	movz x7, #11998, lsl #0
	movk x7, #6731, lsl #16
	movk x7, #8454, lsl #32
	movk x7, #26219, lsl #48
	mov v23.d[0], x6
	mov v23.d[1], x7
	movz x6, #62722, lsl #0
	movk x6, #35474, lsl #16
	movk x6, #45836, lsl #32
	movk x6, #53374, lsl #48
	movz x7, #18298, lsl #0
	movk x7, #58774, lsl #16
	movk x7, #32806, lsl #32
	movk x7, #57261, lsl #48
	mov v24.d[0], x6
	mov v24.d[1], x7
	movz x6, #12449, lsl #0
	movk x6, #44599, lsl #16
	movk x6, #5430, lsl #32
	movk x6, #14370, lsl #48
	movz x7, #42996, lsl #0
	movk x7, #19525, lsl #16
	movk x7, #59777, lsl #32
	movk x7, #38788, lsl #48
	mov v25.d[0], x6
	mov v25.d[1], x7
	movz x6, #52021, lsl #0
	movk x6, #15566, lsl #16
	movk x6, #4465, lsl #32
	movk x6, #35271, lsl #48
	movz x7, #64373, lsl #0
	movk x7, #63706, lsl #16
	movk x7, #22932, lsl #32
	movk x7, #50306, lsl #48
	mov v26.d[0], x6
	mov v26.d[1], x7
	movz x6, #18943, lsl #0
	movk x6, #26425, lsl #16
	movk x6, #53184, lsl #32
	movk x6, #47319, lsl #48
	movz x7, #36367, lsl #0
	movk x7, #9026, lsl #16
	movk x7, #27793, lsl #32
	movk x7, #42203, lsl #48
	mov v27.d[0], x6
	mov v27.d[1], x7
	movz x6, #61748, lsl #0
	movk x6, #49736, lsl #16
	movk x6, #15727, lsl #32
	movk x6, #16429, lsl #48
	movz x7, #16062, lsl #0
	movk x7, #49596, lsl #16
	movk x7, #47786, lsl #32
	movk x7, #21838, lsl #48
	mov v28.d[0], x6
	mov v28.d[1], x7
	movz x6, #56379, lsl #0
	movk x6, #32616, lsl #16
	movk x6, #55452, lsl #32
	movk x6, #22090, lsl #48
	movz x7, #41079, lsl #0
	movk x7, #18157, lsl #16
	movk x7, #11189, lsl #32
	movk x7, #64101, lsl #48
	mov v29.d[0], x6
	mov v29.d[1], x7
	movz x6, #47587, lsl #0
	movk x6, #40881, lsl #16
	movk x6, #63838, lsl #32
	movk x6, #45798, lsl #48
	movz x7, #59953, lsl #0
	movk x7, #24429, lsl #16
	movk x7, #61668, lsl #32
	movk x7, #35021, lsl #48
	mov v30.d[0], x6
	mov v30.d[1], x7
	movz x6, #14870, lsl #0
	movk x6, #54360, lsl #16
	movk x6, #10594, lsl #32
	movk x6, #13063, lsl #48
	movz x7, #7144, lsl #0
	movk x7, #30981, lsl #16
	movk x7, #27280, lsl #32
	movk x7, #39466, lsl #48
	mov v31.d[0], x6
	mov v31.d[1], x7
	movz x6, #38920, lsl #0
	movk x6, #4481, lsl #16
	movk x6, #33555, lsl #32
	movk x6, #2714, lsl #48
	movz x7, #26872, lsl #0
	movk x7, #57713, lsl #16
	movk x7, #29667, lsl #32
	movk x7, #64106, lsl #48
	mov v4.d[0], x6
	mov v4.d[1], x7
	movz x6, #44288, lsl #0
	movk x6, #38459, lsl #16
	movk x6, #56433, lsl #32
	movk x6, #59210, lsl #48
	movz x7, #50795, lsl #0
	movk x7, #64848, lsl #16
	movk x7, #46874, lsl #32
	movk x7, #35873, lsl #48
	mov v5.d[0], x6
	mov v5.d[1], x7
	movz w15, #64, lsl #0
	dup v6.16b, w15
	movz w15, #128, lsl #0
	dup v7.16b, w15
	movz w14, #192, lsl #0
	movz w15, #15, lsl #0
	movz x16, #65280, lsl #0
	movk x16, #65280, lsl #16
	movk x16, #0, lsl #32
	movk x16, #0, lsl #48
	movz x17, #53244, lsl #0
	movk x17, #53244, lsl #16
	movk x17, #0, lsl #32
	movk x17, #0, lsl #48
	movz x4, #62271, lsl #0
	movk x4, #62271, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	ldr w0, [x5, #976]
	rev w0, w0
	ldr w1, [x5, #980]
	rev w1, w1
	ldr w2, [x5, #984]
	rev w2, w2
	ldr w3, [x5, #988]
	rev w3, w3
	ldr w8, [x5, #1232]
	eor w8, w8, w2
	ldr w10, [x5, #1236]
	eor w10, w10, w3
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w1, w1, w10
	add w10, w10, w8
	eor w0, w0, w10
	ldr w8, [x5, #1240]
	eor w8, w8, w0
	ldr w10, [x5, #1244]
	eor w10, w10, w1
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w3, w3, w10
	add w10, w10, w8
	eor w2, w2, w10
	ldr w8, [x5, #1248]
	eor w8, w8, w2
	ldr w10, [x5, #1252]
	eor w10, w10, w3
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w1, w1, w10
	add w10, w10, w8
	eor w0, w0, w10
	ldr w8, [x5, #1256]
	eor w8, w8, w0
	ldr w10, [x5, #1260]
	eor w10, w10, w1
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w3, w3, w10
	add w10, w10, w8
	eor w2, w2, w10
	ldr w8, [x5, #1264]
	eor w8, w8, w2
	ldr w10, [x5, #1268]
	eor w10, w10, w3
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w1, w1, w10
	add w10, w10, w8
	eor w0, w0, w10
	ldr w8, [x5, #1272]
	eor w8, w8, w0
	ldr w10, [x5, #1276]
	eor w10, w10, w1
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w3, w3, w10
	add w10, w10, w8
	eor w2, w2, w10
	ldr w8, [x5, #1280]
	eor w8, w8, w2
	ldr w10, [x5, #1284]
	eor w10, w10, w3
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w1, w1, w10
	add w10, w10, w8
	eor w0, w0, w10
	ldr w8, [x5, #1288]
	eor w8, w8, w0
	ldr w10, [x5, #1292]
	eor w10, w10, w1
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w3, w3, w10
	add w10, w10, w8
	eor w2, w2, w10
	ldr w8, [x5, #1296]
	eor w8, w8, w2
	ldr w10, [x5, #1300]
	eor w10, w10, w3
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w1, w1, w10
	add w10, w10, w8
	eor w0, w0, w10
	ldr w8, [x5, #1304]
	eor w8, w8, w0
	ldr w10, [x5, #1308]
	eor w10, w10, w1
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w3, w3, w10
	add w10, w10, w8
	eor w2, w2, w10
	ldr w8, [x5, #1312]
	eor w8, w8, w2
	ldr w10, [x5, #1316]
	eor w10, w10, w3
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w1, w1, w10
	add w10, w10, w8
	eor w0, w0, w10
	ldr w8, [x5, #1320]
	eor w8, w8, w0
	ldr w10, [x5, #1324]
	eor w10, w10, w1
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w3, w3, w10
	add w10, w10, w8
	eor w2, w2, w10
	ldr w8, [x5, #1328]
	eor w8, w8, w2
	ldr w10, [x5, #1332]
	eor w10, w10, w3
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w1, w1, w10
	add w10, w10, w8
	eor w0, w0, w10
	ldr w8, [x5, #1336]
	eor w8, w8, w0
	ldr w10, [x5, #1340]
	eor w10, w10, w1
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w3, w3, w10
	add w10, w10, w8
	eor w2, w2, w10
	ldr w8, [x5, #1344]
	eor w8, w8, w2
	ldr w10, [x5, #1348]
	eor w10, w10, w3
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w1, w1, w10
	add w10, w10, w8
	eor w0, w0, w10
	ldr w8, [x5, #1352]
	eor w8, w8, w0
	ldr w10, [x5, #1356]
	eor w10, w10, w1
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w3, w3, w10
	add w10, w10, w8
	eor w2, w2, w10
	rev w2, w2
	str w2, [x5, #976]
	rev w3, w3
	str w3, [x5, #980]
	rev w0, w0
	str w0, [x5, #984]
	rev w1, w1
	str w1, [x5, #988]
	lsr x13, x24, #0
	cbnz x13, 28f
	add x16, x24, #0
	b 29f
28:
	movz x16, #1, lsl #0
29:
	add x15, x5, #0
	add x15, x15, #976
	add x14, x23, #0
	add x17, x16, #0
210:
	ldr x8, [x15, #0]
	str x8, [x14, #0]
	ldr x8, [x15, #8]
	str x8, [x14, #8]
	add x14, x14, #16
	add x15, x15, #16
	sub x17, x17, #1
	cbnz x17, 210b
	add x23, x14, #0
	sub x24, x24, x16
	cbnz x24, 24b
	b 23f
22:
23:
	ldr x19, [x5, #1360]
	ldr x20, [x5, #1368]
	ldr x21, [x5, #1376]
	ldr x22, [x5, #1384]
	ldr x23, [x5, #1392]
	ldr x24, [x5, #1400]
	ldr x25, [x5, #1408]
	ldr x26, [x5, #1416]
	ldr x27, [x5, #1424]
	ldr x28, [x5, #1432]
21:
	movz x17, #0, lsl #0
	add x16, sp, #0
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	stp x17, x17, [x16, #192]
	stp x17, x17, [x16, #208]
	stp x17, x17, [x16, #224]
	stp x17, x17, [x16, #240]
	stp x17, x17, [x16, #256]
	stp x17, x17, [x16, #272]
	stp x17, x17, [x16, #288]
	stp x17, x17, [x16, #304]
	stp x17, x17, [x16, #320]
	stp x17, x17, [x16, #336]
	stp x17, x17, [x16, #352]
	stp x17, x17, [x16, #368]
	stp x17, x17, [x16, #384]
	stp x17, x17, [x16, #400]
	stp x17, x17, [x16, #416]
	stp x17, x17, [x16, #432]
	stp x17, x17, [x16, #448]
	stp x17, x17, [x16, #464]
	stp x17, x17, [x16, #480]
	stp x17, x17, [x16, #496]
	add x16, sp, #512
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	stp x17, x17, [x16, #192]
	stp x17, x17, [x16, #208]
	stp x17, x17, [x16, #224]
	stp x17, x17, [x16, #240]
	stp x17, x17, [x16, #256]
	stp x17, x17, [x16, #272]
	stp x17, x17, [x16, #288]
	stp x17, x17, [x16, #304]
	stp x17, x17, [x16, #320]
	stp x17, x17, [x16, #336]
	stp x17, x17, [x16, #352]
	stp x17, x17, [x16, #368]
	stp x17, x17, [x16, #384]
	stp x17, x17, [x16, #400]
	stp x17, x17, [x16, #416]
	stp x17, x17, [x16, #432]
	stp x17, x17, [x16, #448]
	stp x17, x17, [x16, #464]
	stp x17, x17, [x16, #480]
	stp x17, x17, [x16, #496]
	add x16, sp, #1024
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	stp x17, x17, [x16, #192]
	stp x17, x17, [x16, #208]
	stp x17, x17, [x16, #224]
	stp x17, x17, [x16, #240]
	stp x17, x17, [x16, #256]
	stp x17, x17, [x16, #272]
	stp x17, x17, [x16, #288]
	stp x17, x17, [x16, #304]
	stp x17, x17, [x16, #320]
	stp x17, x17, [x16, #336]
	stp x17, x17, [x16, #352]
	stp x17, x17, [x16, #368]
	stp x17, x17, [x16, #384]
	stp x17, x17, [x16, #400]
	stp x17, x17, [x16, #416]
	add sp, sp, #1456
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v3.2d, #0
	movz x0, #0, lsl #0
	sub sp, sp, #1472
	movi v31.2d, #0
	add x9, sp, #0
	str q31, [x9, #0]
	add sp, sp, #1472
	ret
	.p2align 6

vg_seed_ecb_decrypt:
	sub sp, sp, #1456
	add x3, sp, #0
	add x13, x2, #1
	lsr x13, x13, #3
	cbz x13, 20f
	str x30, [sp, #-16]!
	bl {vg_seed_decrypt_blocks}
	ldr x30, [sp], #16
	b 21f
20:
	add x5, x3, #0
	str x19, [x5, #1360]
	str x20, [x5, #1368]
	str x21, [x5, #1376]
	str x22, [x5, #1384]
	str x23, [x5, #1392]
	str x24, [x5, #1400]
	str x25, [x5, #1408]
	str x26, [x5, #1416]
	str x27, [x5, #1424]
	str x28, [x5, #1432]
	add x23, x1, #0
	add x24, x2, #0
	ldr x6, [x0, #0]
	str x6, [x5, #1232]
	ldr x6, [x0, #8]
	str x6, [x5, #1240]
	ldr x6, [x0, #16]
	str x6, [x5, #1248]
	ldr x6, [x0, #24]
	str x6, [x5, #1256]
	ldr x6, [x0, #32]
	str x6, [x5, #1264]
	ldr x6, [x0, #40]
	str x6, [x5, #1272]
	ldr x6, [x0, #48]
	str x6, [x5, #1280]
	ldr x6, [x0, #56]
	str x6, [x5, #1288]
	ldr x6, [x0, #64]
	str x6, [x5, #1296]
	ldr x6, [x0, #72]
	str x6, [x5, #1304]
	ldr x6, [x0, #80]
	str x6, [x5, #1312]
	ldr x6, [x0, #88]
	str x6, [x5, #1320]
	ldr x6, [x0, #96]
	str x6, [x5, #1328]
	ldr x6, [x0, #104]
	str x6, [x5, #1336]
	ldr x6, [x0, #112]
	str x6, [x5, #1344]
	ldr x6, [x0, #120]
	str x6, [x5, #1352]
	cbz x24, 22f
24:
	lsr x13, x24, #0
	cbnz x13, 25f
	add x16, x24, #0
	b 26f
25:
	movz x16, #1, lsl #0
26:
	add x14, x5, #0
	add x14, x14, #976
	add x15, x23, #0
	add x17, x16, #0
27:
	ldr x8, [x15, #0]
	str x8, [x14, #0]
	ldr x8, [x15, #8]
	str x8, [x14, #8]
	add x14, x14, #16
	add x15, x15, #16
	sub x17, x17, #1
	cbnz x17, 27b
	movz x6, #34217, lsl #0
	movk x6, #54230, lsl #16
	movk x6, #7508, lsl #32
	movk x6, #9644, lsl #48
	movz x7, #17245, lsl #0
	movk x7, #7704, lsl #16
	movk x7, #64593, lsl #32
	movk x7, #25546, lsl #48
	mov v16.d[0], x6
	mov v16.d[1], x7
	movz x6, #17448, lsl #0
	movk x6, #40224, lsl #16
	movk x6, #58080, lsl #32
	movk x6, #6088, lsl #48
	movz x7, #36773, lsl #0
	movk x7, #31491, lsl #16
	movk x7, #5051, lsl #32
	movk x7, #61138, lsl #48
	mov v17.d[0], x6
	mov v17.d[1], x7
	movz x6, #35952, lsl #0
	movk x6, #43071, lsl #16
	movk x6, #56626, lsl #32
	movk x6, #29942, lsl #48
	movz x7, #38380, lsl #0
	movk x7, #22283, lsl #16
	movk x7, #23388, lsl #32
	movk x7, #445, lsl #48
	mov v18.d[0], x6
	mov v18.d[1], x7
	movz x6, #7204, lsl #0
	movk x6, #39027, lsl #16
	movk x6, #52240, lsl #32
	movk x6, #55794, lsl #48
	movz x7, #59180, lsl #0
	movk x7, #33650, lsl #16
	movk x7, #53659, lsl #32
	movk x7, #51590, lsl #48
	mov v19.d[0], x6
	mov v19.d[1], x7
	movz x6, #20576, lsl #0
	movk x6, #60323, lsl #16
	movk x6, #46605, lsl #32
	movk x6, #20382, lsl #48
	movz x7, #23223, lsl #0
	movk x7, #30918, lsl #16
	movk x7, #4774, lsl #32
	movk x7, #54703, lsl #48
	mov v20.d[0], x6
	mov v20.d[1], x7
	movz x6, #50017, lsl #0
	movk x6, #16820, lsl #16
	movk x6, #32082, lsl #32
	movk x6, #2189, lsl #48
	movz x7, #39199, lsl #0
	movk x7, #6400, lsl #16
	movk x7, #21252, lsl #32
	movk x7, #57847, lsl #48
	mov v21.d[0], x6
	mov v21.d[1], x7
	movz x6, #30461, lsl #0
	movk x6, #10031, lsl #16
	movk x6, #35760, lsl #32
	movk x6, #43790, lsl #48
	movz x7, #28322, lsl #0
	movk x7, #19859, lsl #16
	movk x7, #31849, lsl #32
	movk x7, #2569, lsl #48
	mov v22.d[0], x6
	mov v22.d[1], x7
	movz x6, #61375, lsl #0
	movk x6, #50675, lsl #16
	movk x6, #5255, lsl #32
	movk x6, #25854, lsl #48
	movz x7, #11998, lsl #0
	movk x7, #6731, lsl #16
	movk x7, #8454, lsl #32
	movk x7, #26219, lsl #48
	mov v23.d[0], x6
	mov v23.d[1], x7
	movz x6, #62722, lsl #0
	movk x6, #35474, lsl #16
	movk x6, #45836, lsl #32
	movk x6, #53374, lsl #48
	movz x7, #18298, lsl #0
	movk x7, #58774, lsl #16
	movk x7, #32806, lsl #32
	movk x7, #57261, lsl #48
	mov v24.d[0], x6
	mov v24.d[1], x7
	movz x6, #12449, lsl #0
	movk x6, #44599, lsl #16
	movk x6, #5430, lsl #32
	movk x6, #14370, lsl #48
	movz x7, #42996, lsl #0
	movk x7, #19525, lsl #16
	movk x7, #59777, lsl #32
	movk x7, #38788, lsl #48
	mov v25.d[0], x6
	mov v25.d[1], x7
	movz x6, #52021, lsl #0
	movk x6, #15566, lsl #16
	movk x6, #4465, lsl #32
	movk x6, #35271, lsl #48
	movz x7, #64373, lsl #0
	movk x7, #63706, lsl #16
	movk x7, #22932, lsl #32
	movk x7, #50306, lsl #48
	mov v26.d[0], x6
	mov v26.d[1], x7
	movz x6, #18943, lsl #0
	movk x6, #26425, lsl #16
	movk x6, #53184, lsl #32
	movk x6, #47319, lsl #48
	movz x7, #36367, lsl #0
	movk x7, #9026, lsl #16
	movk x7, #27793, lsl #32
	movk x7, #42203, lsl #48
	mov v27.d[0], x6
	mov v27.d[1], x7
	movz x6, #61748, lsl #0
	movk x6, #49736, lsl #16
	movk x6, #15727, lsl #32
	movk x6, #16429, lsl #48
	movz x7, #16062, lsl #0
	movk x7, #49596, lsl #16
	movk x7, #47786, lsl #32
	movk x7, #21838, lsl #48
	mov v28.d[0], x6
	mov v28.d[1], x7
	movz x6, #56379, lsl #0
	movk x6, #32616, lsl #16
	movk x6, #55452, lsl #32
	movk x6, #22090, lsl #48
	movz x7, #41079, lsl #0
	movk x7, #18157, lsl #16
	movk x7, #11189, lsl #32
	movk x7, #64101, lsl #48
	mov v29.d[0], x6
	mov v29.d[1], x7
	movz x6, #47587, lsl #0
	movk x6, #40881, lsl #16
	movk x6, #63838, lsl #32
	movk x6, #45798, lsl #48
	movz x7, #59953, lsl #0
	movk x7, #24429, lsl #16
	movk x7, #61668, lsl #32
	movk x7, #35021, lsl #48
	mov v30.d[0], x6
	mov v30.d[1], x7
	movz x6, #14870, lsl #0
	movk x6, #54360, lsl #16
	movk x6, #10594, lsl #32
	movk x6, #13063, lsl #48
	movz x7, #7144, lsl #0
	movk x7, #30981, lsl #16
	movk x7, #27280, lsl #32
	movk x7, #39466, lsl #48
	mov v31.d[0], x6
	mov v31.d[1], x7
	movz x6, #38920, lsl #0
	movk x6, #4481, lsl #16
	movk x6, #33555, lsl #32
	movk x6, #2714, lsl #48
	movz x7, #26872, lsl #0
	movk x7, #57713, lsl #16
	movk x7, #29667, lsl #32
	movk x7, #64106, lsl #48
	mov v4.d[0], x6
	mov v4.d[1], x7
	movz x6, #44288, lsl #0
	movk x6, #38459, lsl #16
	movk x6, #56433, lsl #32
	movk x6, #59210, lsl #48
	movz x7, #50795, lsl #0
	movk x7, #64848, lsl #16
	movk x7, #46874, lsl #32
	movk x7, #35873, lsl #48
	mov v5.d[0], x6
	mov v5.d[1], x7
	movz w15, #64, lsl #0
	dup v6.16b, w15
	movz w15, #128, lsl #0
	dup v7.16b, w15
	movz w14, #192, lsl #0
	movz w15, #15, lsl #0
	movz x16, #65280, lsl #0
	movk x16, #65280, lsl #16
	movk x16, #0, lsl #32
	movk x16, #0, lsl #48
	movz x17, #53244, lsl #0
	movk x17, #53244, lsl #16
	movk x17, #0, lsl #32
	movk x17, #0, lsl #48
	movz x4, #62271, lsl #0
	movk x4, #62271, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	ldr w0, [x5, #976]
	rev w0, w0
	ldr w1, [x5, #980]
	rev w1, w1
	ldr w2, [x5, #984]
	rev w2, w2
	ldr w3, [x5, #988]
	rev w3, w3
	ldr w8, [x5, #1352]
	eor w8, w8, w2
	ldr w10, [x5, #1356]
	eor w10, w10, w3
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w1, w1, w10
	add w10, w10, w8
	eor w0, w0, w10
	ldr w8, [x5, #1344]
	eor w8, w8, w0
	ldr w10, [x5, #1348]
	eor w10, w10, w1
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w3, w3, w10
	add w10, w10, w8
	eor w2, w2, w10
	ldr w8, [x5, #1336]
	eor w8, w8, w2
	ldr w10, [x5, #1340]
	eor w10, w10, w3
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w1, w1, w10
	add w10, w10, w8
	eor w0, w0, w10
	ldr w8, [x5, #1328]
	eor w8, w8, w0
	ldr w10, [x5, #1332]
	eor w10, w10, w1
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w3, w3, w10
	add w10, w10, w8
	eor w2, w2, w10
	ldr w8, [x5, #1320]
	eor w8, w8, w2
	ldr w10, [x5, #1324]
	eor w10, w10, w3
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w1, w1, w10
	add w10, w10, w8
	eor w0, w0, w10
	ldr w8, [x5, #1312]
	eor w8, w8, w0
	ldr w10, [x5, #1316]
	eor w10, w10, w1
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w3, w3, w10
	add w10, w10, w8
	eor w2, w2, w10
	ldr w8, [x5, #1304]
	eor w8, w8, w2
	ldr w10, [x5, #1308]
	eor w10, w10, w3
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w1, w1, w10
	add w10, w10, w8
	eor w0, w0, w10
	ldr w8, [x5, #1296]
	eor w8, w8, w0
	ldr w10, [x5, #1300]
	eor w10, w10, w1
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w3, w3, w10
	add w10, w10, w8
	eor w2, w2, w10
	ldr w8, [x5, #1288]
	eor w8, w8, w2
	ldr w10, [x5, #1292]
	eor w10, w10, w3
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w1, w1, w10
	add w10, w10, w8
	eor w0, w0, w10
	ldr w8, [x5, #1280]
	eor w8, w8, w0
	ldr w10, [x5, #1284]
	eor w10, w10, w1
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w3, w3, w10
	add w10, w10, w8
	eor w2, w2, w10
	ldr w8, [x5, #1272]
	eor w8, w8, w2
	ldr w10, [x5, #1276]
	eor w10, w10, w3
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w1, w1, w10
	add w10, w10, w8
	eor w0, w0, w10
	ldr w8, [x5, #1264]
	eor w8, w8, w0
	ldr w10, [x5, #1268]
	eor w10, w10, w1
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w3, w3, w10
	add w10, w10, w8
	eor w2, w2, w10
	ldr w8, [x5, #1256]
	eor w8, w8, w2
	ldr w10, [x5, #1260]
	eor w10, w10, w3
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w1, w1, w10
	add w10, w10, w8
	eor w0, w0, w10
	ldr w8, [x5, #1248]
	eor w8, w8, w0
	ldr w10, [x5, #1252]
	eor w10, w10, w1
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w3, w3, w10
	add w10, w10, w8
	eor w2, w2, w10
	ldr w8, [x5, #1240]
	eor w8, w8, w2
	ldr w10, [x5, #1244]
	eor w10, w10, w3
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w1, w1, w10
	add w10, w10, w8
	eor w0, w0, w10
	ldr w8, [x5, #1232]
	eor w8, w8, w0
	ldr w10, [x5, #1236]
	eor w10, w10, w1
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w3, w3, w10
	add w10, w10, w8
	eor w2, w2, w10
	rev w2, w2
	str w2, [x5, #976]
	rev w3, w3
	str w3, [x5, #980]
	rev w0, w0
	str w0, [x5, #984]
	rev w1, w1
	str w1, [x5, #988]
	lsr x13, x24, #0
	cbnz x13, 28f
	add x16, x24, #0
	b 29f
28:
	movz x16, #1, lsl #0
29:
	add x15, x5, #0
	add x15, x15, #976
	add x14, x23, #0
	add x17, x16, #0
210:
	ldr x8, [x15, #0]
	str x8, [x14, #0]
	ldr x8, [x15, #8]
	str x8, [x14, #8]
	add x14, x14, #16
	add x15, x15, #16
	sub x17, x17, #1
	cbnz x17, 210b
	add x23, x14, #0
	sub x24, x24, x16
	cbnz x24, 24b
	b 23f
22:
23:
	ldr x19, [x5, #1360]
	ldr x20, [x5, #1368]
	ldr x21, [x5, #1376]
	ldr x22, [x5, #1384]
	ldr x23, [x5, #1392]
	ldr x24, [x5, #1400]
	ldr x25, [x5, #1408]
	ldr x26, [x5, #1416]
	ldr x27, [x5, #1424]
	ldr x28, [x5, #1432]
21:
	movz x17, #0, lsl #0
	add x16, sp, #0
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	stp x17, x17, [x16, #192]
	stp x17, x17, [x16, #208]
	stp x17, x17, [x16, #224]
	stp x17, x17, [x16, #240]
	stp x17, x17, [x16, #256]
	stp x17, x17, [x16, #272]
	stp x17, x17, [x16, #288]
	stp x17, x17, [x16, #304]
	stp x17, x17, [x16, #320]
	stp x17, x17, [x16, #336]
	stp x17, x17, [x16, #352]
	stp x17, x17, [x16, #368]
	stp x17, x17, [x16, #384]
	stp x17, x17, [x16, #400]
	stp x17, x17, [x16, #416]
	stp x17, x17, [x16, #432]
	stp x17, x17, [x16, #448]
	stp x17, x17, [x16, #464]
	stp x17, x17, [x16, #480]
	stp x17, x17, [x16, #496]
	add x16, sp, #512
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	stp x17, x17, [x16, #192]
	stp x17, x17, [x16, #208]
	stp x17, x17, [x16, #224]
	stp x17, x17, [x16, #240]
	stp x17, x17, [x16, #256]
	stp x17, x17, [x16, #272]
	stp x17, x17, [x16, #288]
	stp x17, x17, [x16, #304]
	stp x17, x17, [x16, #320]
	stp x17, x17, [x16, #336]
	stp x17, x17, [x16, #352]
	stp x17, x17, [x16, #368]
	stp x17, x17, [x16, #384]
	stp x17, x17, [x16, #400]
	stp x17, x17, [x16, #416]
	stp x17, x17, [x16, #432]
	stp x17, x17, [x16, #448]
	stp x17, x17, [x16, #464]
	stp x17, x17, [x16, #480]
	stp x17, x17, [x16, #496]
	add x16, sp, #1024
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	stp x17, x17, [x16, #192]
	stp x17, x17, [x16, #208]
	stp x17, x17, [x16, #224]
	stp x17, x17, [x16, #240]
	stp x17, x17, [x16, #256]
	stp x17, x17, [x16, #272]
	stp x17, x17, [x16, #288]
	stp x17, x17, [x16, #304]
	stp x17, x17, [x16, #320]
	stp x17, x17, [x16, #336]
	stp x17, x17, [x16, #352]
	stp x17, x17, [x16, #368]
	stp x17, x17, [x16, #384]
	stp x17, x17, [x16, #400]
	stp x17, x17, [x16, #416]
	add sp, sp, #1456
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v3.2d, #0
	movz x0, #0, lsl #0
	sub sp, sp, #1472
	movi v31.2d, #0
	add x9, sp, #0
	str q31, [x9, #0]
	add sp, sp, #1472
	ret
	.p2align 6
