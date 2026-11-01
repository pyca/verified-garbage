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
	ret
	.p2align 6

vg_seed_ecb_encrypt:
	sub sp, sp, #1088
	add x3, sp, #0
	str x30, [sp, #-16]!
	bl {vg_seed_encrypt_blocks}
	ldr x30, [sp], #16
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
	add sp, sp, #1088
	ret
	.p2align 6

vg_seed_ecb_decrypt:
	sub sp, sp, #1088
	add x3, sp, #0
	str x30, [sp, #-16]!
	bl {vg_seed_decrypt_blocks}
	ldr x30, [sp], #16
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
	add sp, sp, #1088
	ret
	.p2align 6
