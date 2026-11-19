// The functions of `src/internal/vg_chacha20_poly1305_seal_core.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chacha20_poly1305_seal_core:
	sub sp, sp, #1280
	add x7, sp, #0
	sub x9, x5, #1
	sub x10, x5, #64
	orr x9, x9, x10
	orr x9, x9, x5
	lsr x9, x9, #9
	cbz x9, 20f
	str x22, [x7, #584]
	str x23, [x7, #592]
	str x24, [x7, #600]
	str x25, [x7, #608]
	str x30, [x7, #616]
	str x6, [x7, #624]
	str x21, [x7, #576]
	add x21, x7, #0
	add x24, x2, #0
	add x25, x3, #0
	add x22, x4, #0
	add x23, x5, #0
	movz w9, #30821, lsl #0
	movk w9, #24944, lsl #16
	str w9, [x21, #64]
	movz w9, #25710, lsl #0
	movk w9, #13088, lsl #16
	str w9, [x21, #68]
	movz w9, #11570, lsl #0
	movk w9, #31074, lsl #16
	str w9, [x21, #72]
	movz w9, #25972, lsl #0
	movk w9, #27424, lsl #16
	str w9, [x21, #76]
	ldr w9, [x0, #0]
	str w9, [x21, #80]
	ldr w9, [x0, #4]
	str w9, [x21, #84]
	ldr w9, [x0, #8]
	str w9, [x21, #88]
	ldr w9, [x0, #12]
	str w9, [x21, #92]
	ldr w9, [x0, #16]
	str w9, [x21, #96]
	ldr w9, [x0, #20]
	str w9, [x21, #100]
	ldr w9, [x0, #24]
	str w9, [x21, #104]
	ldr w9, [x0, #28]
	str w9, [x21, #108]
	movz w9, #0, lsl #0
	str w9, [x21, #112]
	ldr w9, [x1, #0]
	str w9, [x21, #116]
	ldr w9, [x1, #4]
	str w9, [x21, #120]
	ldr w9, [x1, #8]
	str w9, [x21, #124]
	add x0, x21, #64
	add x1, x21, #128
	bl {vg_chacha20_block}
	add x0, x21, #448
	add x1, x21, #128
	bl {vg_poly1305_init}
	add x0, x21, #448
	add x1, x24, #0
	lsr x2, x25, #4
	bl {vg_poly1305_blocks}
	lsl x10, x25, #60
	lsr x10, x10, #60
	cbz x10, 22f
	sub x9, x25, x10
	add x1, x24, x9
	movz x11, #0, lsl #0
	str x11, [x21, #16]
	str x11, [x21, #24]
	add x9, x21, #16
24:
	ldrb w11, [x1, #0]
	strb w11, [x9, #0]
	add x1, x1, #1
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 24b
	add x0, x21, #448
	add x1, x21, #16
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 23f
22:
23:
	str x25, [x21, #0]
	str x23, [x21, #8]
	movz w9, #1, lsl #0
	str w9, [x21, #112]
	add x0, x21, #64
	add x1, x22, #0
	add x2, x23, #0
	add x3, x21, #128
	add x4, x1, #0
	bl {vg_chacha20_xor}
	add x0, x21, #448
	add x1, x22, #0
	lsr x2, x23, #4
	bl {vg_poly1305_blocks}
	lsl x10, x23, #60
	lsr x10, x10, #60
	cbz x10, 25f
	sub x9, x23, x10
	add x1, x22, x9
	movz x11, #0, lsl #0
	str x11, [x21, #16]
	str x11, [x21, #24]
	add x9, x21, #16
27:
	ldrb w11, [x1, #0]
	strb w11, [x9, #0]
	add x1, x1, #1
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 27b
	add x0, x21, #448
	add x1, x21, #16
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 26f
25:
26:
	add x0, x21, #448
	add x1, x21, #0
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 21f
20:
	add x9, x5, #63
	lsr x9, x9, #9
	cbz x9, 28f
	str x22, [x7, #584]
	str x23, [x7, #592]
	str x24, [x7, #600]
	str x25, [x7, #608]
	str x30, [x7, #616]
	str x6, [x7, #624]
	str x21, [x7, #576]
	add x21, x7, #0
	add x24, x2, #0
	add x25, x3, #0
	add x22, x4, #0
	add x23, x5, #0
	movz w9, #30821, lsl #0
	movk w9, #24944, lsl #16
	str w9, [x21, #64]
	movz w9, #25710, lsl #0
	movk w9, #13088, lsl #16
	str w9, [x21, #68]
	movz w9, #11570, lsl #0
	movk w9, #31074, lsl #16
	str w9, [x21, #72]
	movz w9, #25972, lsl #0
	movk w9, #27424, lsl #16
	str w9, [x21, #76]
	ldr w9, [x0, #0]
	str w9, [x21, #80]
	ldr w9, [x0, #4]
	str w9, [x21, #84]
	ldr w9, [x0, #8]
	str w9, [x21, #88]
	ldr w9, [x0, #12]
	str w9, [x21, #92]
	ldr w9, [x0, #16]
	str w9, [x21, #96]
	ldr w9, [x0, #20]
	str w9, [x21, #100]
	ldr w9, [x0, #24]
	str w9, [x21, #104]
	ldr w9, [x0, #28]
	str w9, [x21, #108]
	movz w9, #0, lsl #0
	str w9, [x21, #112]
	ldr w9, [x1, #0]
	str w9, [x21, #116]
	ldr w9, [x1, #4]
	str w9, [x21, #120]
	ldr w9, [x1, #8]
	str w9, [x21, #124]
	add x0, x21, #64
	add x1, x21, #128
	bl {vg_chacha20_block}
	add x0, x21, #448
	add x1, x21, #128
	bl {vg_poly1305_init}
	add x0, x21, #448
	add x1, x24, #0
	lsr x2, x25, #4
	bl {vg_poly1305_blocks}
	lsl x10, x25, #60
	lsr x10, x10, #60
	cbz x10, 210f
	sub x9, x25, x10
	add x1, x24, x9
	movz x11, #0, lsl #0
	str x11, [x21, #16]
	str x11, [x21, #24]
	add x9, x21, #16
212:
	ldrb w11, [x1, #0]
	strb w11, [x9, #0]
	add x1, x1, #1
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 212b
	add x0, x21, #448
	add x1, x21, #16
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 211f
210:
211:
	str x25, [x21, #0]
	str x23, [x21, #8]
	eor v0.16b, v0.16b, v0.16b
	str q0, [x21, #768]
	str q0, [x21, #784]
	str q0, [x21, #800]
	str q0, [x21, #816]
	str q0, [x21, #832]
	str q0, [x21, #848]
	str q0, [x21, #864]
	str q0, [x21, #880]
	str q0, [x21, #896]
	str q0, [x21, #912]
	str q0, [x21, #928]
	str q0, [x21, #944]
	str q0, [x21, #960]
	str q0, [x21, #976]
	str q0, [x21, #992]
	str q0, [x21, #1008]
	str q0, [x21, #1024]
	str q0, [x21, #1040]
	str q0, [x21, #1056]
	str q0, [x21, #1072]
	str q0, [x21, #1088]
	str q0, [x21, #1104]
	str q0, [x21, #1120]
	str q0, [x21, #1136]
	str q0, [x21, #1152]
	str q0, [x21, #1168]
	str q0, [x21, #1184]
	str q0, [x21, #1200]
	str q0, [x21, #1216]
	str q0, [x21, #1232]
	str q0, [x21, #1248]
	str q0, [x21, #1264]
	movz w9, #1, lsl #0
	str w9, [x21, #112]
	add x0, x21, #64
	add x1, x21, #768
	movz x2, #512, lsl #0
	add x3, x21, #128
	add x4, x1, #0
	bl {vg_chacha20_xor}
	add x9, x22, #0
	add x15, x9, #0
	add x10, x21, #768
	lsr x11, x23, #4
	cbz x11, 213f
215:
	ldr q0, [x9, #0]
	ldr q1, [x10, #0]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x15, #0]
	add x9, x9, #16
	add x10, x10, #16
	add x15, x15, #16
	sub x11, x11, #1
	cbnz x11, 215b
	b 214f
213:
214:
	lsl x11, x23, #60
	lsr x11, x11, #60
	cbz x11, 216f
218:
	ldrb w12, [x9, #0]
	ldrb w13, [x10, #0]
	eor w12, w12, w13
	strb w12, [x15, #0]
	add x9, x9, #1
	add x10, x10, #1
	add x15, x15, #1
	sub x11, x11, #1
	cbnz x11, 218b
	b 217f
216:
217:
	eor v0.16b, v0.16b, v0.16b
	str q0, [x21, #768]
	str q0, [x21, #784]
	str q0, [x21, #800]
	str q0, [x21, #816]
	str q0, [x21, #832]
	str q0, [x21, #848]
	str q0, [x21, #864]
	str q0, [x21, #880]
	str q0, [x21, #896]
	str q0, [x21, #912]
	str q0, [x21, #928]
	str q0, [x21, #944]
	str q0, [x21, #960]
	str q0, [x21, #976]
	str q0, [x21, #992]
	str q0, [x21, #1008]
	str q0, [x21, #1024]
	str q0, [x21, #1040]
	str q0, [x21, #1056]
	str q0, [x21, #1072]
	str q0, [x21, #1088]
	str q0, [x21, #1104]
	str q0, [x21, #1120]
	str q0, [x21, #1136]
	str q0, [x21, #1152]
	str q0, [x21, #1168]
	str q0, [x21, #1184]
	str q0, [x21, #1200]
	str q0, [x21, #1216]
	str q0, [x21, #1232]
	str q0, [x21, #1248]
	str q0, [x21, #1264]
	add x0, x21, #448
	add x1, x22, #0
	lsr x2, x23, #4
	bl {vg_poly1305_blocks}
	lsl x10, x23, #60
	lsr x10, x10, #60
	cbz x10, 219f
	sub x9, x23, x10
	add x1, x22, x9
	movz x11, #0, lsl #0
	str x11, [x21, #16]
	str x11, [x21, #24]
	add x9, x21, #16
221:
	ldrb w11, [x1, #0]
	strb w11, [x9, #0]
	add x1, x1, #1
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 221b
	add x0, x21, #448
	add x1, x21, #16
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 220f
219:
220:
	add x0, x21, #448
	add x1, x21, #0
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 29f
28:
	str x22, [x7, #584]
	str x23, [x7, #592]
	str x24, [x7, #600]
	str x25, [x7, #608]
	str x30, [x7, #616]
	str x6, [x7, #624]
	str x21, [x7, #576]
	add x21, x7, #0
	add x24, x2, #0
	add x25, x3, #0
	add x22, x4, #0
	add x23, x5, #0
	movz w9, #30821, lsl #0
	movk w9, #24944, lsl #16
	str w9, [x21, #0]
	movz w9, #25710, lsl #0
	movk w9, #13088, lsl #16
	str w9, [x21, #4]
	movz w9, #11570, lsl #0
	movk w9, #31074, lsl #16
	str w9, [x21, #8]
	movz w9, #25972, lsl #0
	movk w9, #27424, lsl #16
	str w9, [x21, #12]
	ldr w9, [x0, #0]
	str w9, [x21, #16]
	ldr w9, [x0, #4]
	str w9, [x21, #20]
	ldr w9, [x0, #8]
	str w9, [x21, #24]
	ldr w9, [x0, #12]
	str w9, [x21, #28]
	ldr w9, [x0, #16]
	str w9, [x21, #32]
	ldr w9, [x0, #20]
	str w9, [x21, #36]
	ldr w9, [x0, #24]
	str w9, [x21, #40]
	ldr w9, [x0, #28]
	str w9, [x21, #44]
	movz w9, #0, lsl #0
	str w9, [x21, #48]
	ldr w9, [x1, #0]
	str w9, [x21, #52]
	ldr w9, [x1, #4]
	str w9, [x21, #56]
	ldr w9, [x1, #8]
	str w9, [x21, #60]
	eor v0.16b, v0.16b, v0.16b
	str q0, [x21, #64]
	str q0, [x21, #80]
	str q0, [x21, #96]
	str q0, [x21, #112]
	str q0, [x21, #128]
	str q0, [x21, #144]
	str q0, [x21, #160]
	str q0, [x21, #176]
	str q0, [x21, #192]
	str q0, [x21, #208]
	str q0, [x21, #224]
	str q0, [x21, #240]
	str q0, [x21, #256]
	str q0, [x21, #272]
	str q0, [x21, #288]
	str q0, [x21, #304]
	str q0, [x21, #320]
	str q0, [x21, #336]
	str q0, [x21, #352]
	str q0, [x21, #368]
	str x19, [x21, #632]
	str x20, [x21, #640]
	str x26, [x21, #648]
	add x0, x21, #0
	add x1, x21, #64
	add x3, x21, #384
	add x20, x3, #0
	add x19, x2, #0
	add x26, x1, #0
	ldr w4, [x0, #0]
	dup v0.4s, w4
	ldr w4, [x0, #4]
	dup v1.4s, w4
	ldr w4, [x0, #8]
	dup v2.4s, w4
	ldr w4, [x0, #12]
	dup v3.4s, w4
	ldr w4, [x0, #16]
	dup v4.4s, w4
	ldr w4, [x0, #20]
	dup v5.4s, w4
	ldr w4, [x0, #24]
	dup v6.4s, w4
	ldr w4, [x0, #28]
	dup v7.4s, w4
	ldr w4, [x0, #32]
	dup v16.4s, w4
	ldr w4, [x0, #36]
	dup v17.4s, w4
	ldr w4, [x0, #40]
	dup v18.4s, w4
	ldr w4, [x0, #44]
	dup v19.4s, w4
	ldr w4, [x0, #48]
	dup v20.4s, w4
	add w4, w4, #1
	mov v20.s[1], w4
	add w4, w4, #1
	mov v20.s[2], w4
	add w4, w4, #1
	mov v20.s[3], w4
	ldr w4, [x0, #52]
	dup v21.4s, w4
	ldr w4, [x0, #56]
	dup v22.4s, w4
	ldr w4, [x0, #60]
	dup v23.4s, w4
	movz x4, #3, lsl #0
	movk x4, #513, lsl #16
	movk x4, #1031, lsl #32
	movk x4, #1541, lsl #48
	dup v30.2d, x4
	movz x4, #2059, lsl #0
	movk x4, #2569, lsl #16
	movk x4, #3087, lsl #32
	movk x4, #3597, lsl #48
	mov v30.d[1], x4
	ldr w4, [x0, #48]
	add w4, w4, #4
	str w4, [x0, #48]
	ldr w2, [x0, #0]
	ldr w3, [x0, #4]
	ldr w4, [x0, #8]
	ldr w5, [x0, #12]
	ldr w6, [x0, #16]
	ldr w7, [x0, #20]
	ldr w8, [x0, #24]
	ldr w9, [x0, #28]
	ldr w10, [x0, #32]
	ldr w11, [x0, #36]
	ldr w12, [x0, #40]
	ldr w13, [x0, #44]
	ldr w14, [x0, #48]
	ldr w15, [x0, #52]
	ldr w16, [x0, #56]
	ldr w17, [x0, #60]
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	eor v31.16b, v20.16b, v0.16b
	rev32 v20.8h, v31.8h
	eor w14, w14, w2
	ror w14, w14, #16
	eor v31.16b, v21.16b, v1.16b
	rev32 v21.8h, v31.8h
	eor w15, w15, w3
	ror w15, w15, #16
	eor v31.16b, v22.16b, v2.16b
	rev32 v22.8h, v31.8h
	eor w16, w16, w4
	ror w16, w16, #16
	eor v31.16b, v23.16b, v3.16b
	rev32 v23.8h, v31.8h
	eor w17, w17, w5
	ror w17, w17, #16
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	eor v31.16b, v4.16b, v16.16b
	ushr v4.4s, v31.4s, #20
	sli v4.4s, v31.4s, #12
	eor w6, w6, w10
	ror w6, w6, #20
	eor v31.16b, v5.16b, v17.16b
	ushr v5.4s, v31.4s, #20
	sli v5.4s, v31.4s, #12
	eor w7, w7, w11
	ror w7, w7, #20
	eor v31.16b, v6.16b, v18.16b
	ushr v6.4s, v31.4s, #20
	sli v6.4s, v31.4s, #12
	eor w8, w8, w12
	ror w8, w8, #20
	eor v31.16b, v7.16b, v19.16b
	ushr v7.4s, v31.4s, #20
	sli v7.4s, v31.4s, #12
	eor w9, w9, w13
	ror w9, w9, #20
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	eor v31.16b, v20.16b, v0.16b
	tbl v20.16b, {v31.16b}, v30.16b
	eor w14, w14, w2
	ror w14, w14, #24
	eor v31.16b, v21.16b, v1.16b
	tbl v21.16b, {v31.16b}, v30.16b
	eor w15, w15, w3
	ror w15, w15, #24
	eor v31.16b, v22.16b, v2.16b
	tbl v22.16b, {v31.16b}, v30.16b
	eor w16, w16, w4
	ror w16, w16, #24
	eor v31.16b, v23.16b, v3.16b
	tbl v23.16b, {v31.16b}, v30.16b
	eor w17, w17, w5
	ror w17, w17, #24
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	eor v31.16b, v4.16b, v16.16b
	ushr v4.4s, v31.4s, #25
	sli v4.4s, v31.4s, #7
	eor w6, w6, w10
	ror w6, w6, #25
	eor v31.16b, v5.16b, v17.16b
	ushr v5.4s, v31.4s, #25
	sli v5.4s, v31.4s, #7
	eor w7, w7, w11
	ror w7, w7, #25
	eor v31.16b, v6.16b, v18.16b
	ushr v6.4s, v31.4s, #25
	sli v6.4s, v31.4s, #7
	eor w8, w8, w12
	ror w8, w8, #25
	eor v31.16b, v7.16b, v19.16b
	ushr v7.4s, v31.4s, #25
	sli v7.4s, v31.4s, #7
	eor w9, w9, w13
	ror w9, w9, #25
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	eor v31.16b, v23.16b, v0.16b
	rev32 v23.8h, v31.8h
	eor w17, w17, w2
	ror w17, w17, #16
	eor v31.16b, v20.16b, v1.16b
	rev32 v20.8h, v31.8h
	eor w14, w14, w3
	ror w14, w14, #16
	eor v31.16b, v21.16b, v2.16b
	rev32 v21.8h, v31.8h
	eor w15, w15, w4
	ror w15, w15, #16
	eor v31.16b, v22.16b, v3.16b
	rev32 v22.8h, v31.8h
	eor w16, w16, w5
	ror w16, w16, #16
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	eor v31.16b, v5.16b, v18.16b
	ushr v5.4s, v31.4s, #20
	sli v5.4s, v31.4s, #12
	eor w7, w7, w12
	ror w7, w7, #20
	eor v31.16b, v6.16b, v19.16b
	ushr v6.4s, v31.4s, #20
	sli v6.4s, v31.4s, #12
	eor w8, w8, w13
	ror w8, w8, #20
	eor v31.16b, v7.16b, v16.16b
	ushr v7.4s, v31.4s, #20
	sli v7.4s, v31.4s, #12
	eor w9, w9, w10
	ror w9, w9, #20
	eor v31.16b, v4.16b, v17.16b
	ushr v4.4s, v31.4s, #20
	sli v4.4s, v31.4s, #12
	eor w6, w6, w11
	ror w6, w6, #20
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	eor v31.16b, v23.16b, v0.16b
	tbl v23.16b, {v31.16b}, v30.16b
	eor w17, w17, w2
	ror w17, w17, #24
	eor v31.16b, v20.16b, v1.16b
	tbl v20.16b, {v31.16b}, v30.16b
	eor w14, w14, w3
	ror w14, w14, #24
	eor v31.16b, v21.16b, v2.16b
	tbl v21.16b, {v31.16b}, v30.16b
	eor w15, w15, w4
	ror w15, w15, #24
	eor v31.16b, v22.16b, v3.16b
	tbl v22.16b, {v31.16b}, v30.16b
	eor w16, w16, w5
	ror w16, w16, #24
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	eor v31.16b, v5.16b, v18.16b
	ushr v5.4s, v31.4s, #25
	sli v5.4s, v31.4s, #7
	eor w7, w7, w12
	ror w7, w7, #25
	eor v31.16b, v6.16b, v19.16b
	ushr v6.4s, v31.4s, #25
	sli v6.4s, v31.4s, #7
	eor w8, w8, w13
	ror w8, w8, #25
	eor v31.16b, v7.16b, v16.16b
	ushr v7.4s, v31.4s, #25
	sli v7.4s, v31.4s, #7
	eor w9, w9, w10
	ror w9, w9, #25
	eor v31.16b, v4.16b, v17.16b
	ushr v4.4s, v31.4s, #25
	sli v4.4s, v31.4s, #7
	eor w6, w6, w11
	ror w6, w6, #25
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	eor v31.16b, v20.16b, v0.16b
	rev32 v20.8h, v31.8h
	eor w14, w14, w2
	ror w14, w14, #16
	eor v31.16b, v21.16b, v1.16b
	rev32 v21.8h, v31.8h
	eor w15, w15, w3
	ror w15, w15, #16
	eor v31.16b, v22.16b, v2.16b
	rev32 v22.8h, v31.8h
	eor w16, w16, w4
	ror w16, w16, #16
	eor v31.16b, v23.16b, v3.16b
	rev32 v23.8h, v31.8h
	eor w17, w17, w5
	ror w17, w17, #16
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	eor v31.16b, v4.16b, v16.16b
	ushr v4.4s, v31.4s, #20
	sli v4.4s, v31.4s, #12
	eor w6, w6, w10
	ror w6, w6, #20
	eor v31.16b, v5.16b, v17.16b
	ushr v5.4s, v31.4s, #20
	sli v5.4s, v31.4s, #12
	eor w7, w7, w11
	ror w7, w7, #20
	eor v31.16b, v6.16b, v18.16b
	ushr v6.4s, v31.4s, #20
	sli v6.4s, v31.4s, #12
	eor w8, w8, w12
	ror w8, w8, #20
	eor v31.16b, v7.16b, v19.16b
	ushr v7.4s, v31.4s, #20
	sli v7.4s, v31.4s, #12
	eor w9, w9, w13
	ror w9, w9, #20
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	eor v31.16b, v20.16b, v0.16b
	tbl v20.16b, {v31.16b}, v30.16b
	eor w14, w14, w2
	ror w14, w14, #24
	eor v31.16b, v21.16b, v1.16b
	tbl v21.16b, {v31.16b}, v30.16b
	eor w15, w15, w3
	ror w15, w15, #24
	eor v31.16b, v22.16b, v2.16b
	tbl v22.16b, {v31.16b}, v30.16b
	eor w16, w16, w4
	ror w16, w16, #24
	eor v31.16b, v23.16b, v3.16b
	tbl v23.16b, {v31.16b}, v30.16b
	eor w17, w17, w5
	ror w17, w17, #24
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	eor v31.16b, v4.16b, v16.16b
	ushr v4.4s, v31.4s, #25
	sli v4.4s, v31.4s, #7
	eor w6, w6, w10
	ror w6, w6, #25
	eor v31.16b, v5.16b, v17.16b
	ushr v5.4s, v31.4s, #25
	sli v5.4s, v31.4s, #7
	eor w7, w7, w11
	ror w7, w7, #25
	eor v31.16b, v6.16b, v18.16b
	ushr v6.4s, v31.4s, #25
	sli v6.4s, v31.4s, #7
	eor w8, w8, w12
	ror w8, w8, #25
	eor v31.16b, v7.16b, v19.16b
	ushr v7.4s, v31.4s, #25
	sli v7.4s, v31.4s, #7
	eor w9, w9, w13
	ror w9, w9, #25
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	eor v31.16b, v23.16b, v0.16b
	rev32 v23.8h, v31.8h
	eor w17, w17, w2
	ror w17, w17, #16
	eor v31.16b, v20.16b, v1.16b
	rev32 v20.8h, v31.8h
	eor w14, w14, w3
	ror w14, w14, #16
	eor v31.16b, v21.16b, v2.16b
	rev32 v21.8h, v31.8h
	eor w15, w15, w4
	ror w15, w15, #16
	eor v31.16b, v22.16b, v3.16b
	rev32 v22.8h, v31.8h
	eor w16, w16, w5
	ror w16, w16, #16
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	eor v31.16b, v5.16b, v18.16b
	ushr v5.4s, v31.4s, #20
	sli v5.4s, v31.4s, #12
	eor w7, w7, w12
	ror w7, w7, #20
	eor v31.16b, v6.16b, v19.16b
	ushr v6.4s, v31.4s, #20
	sli v6.4s, v31.4s, #12
	eor w8, w8, w13
	ror w8, w8, #20
	eor v31.16b, v7.16b, v16.16b
	ushr v7.4s, v31.4s, #20
	sli v7.4s, v31.4s, #12
	eor w9, w9, w10
	ror w9, w9, #20
	eor v31.16b, v4.16b, v17.16b
	ushr v4.4s, v31.4s, #20
	sli v4.4s, v31.4s, #12
	eor w6, w6, w11
	ror w6, w6, #20
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	eor v31.16b, v23.16b, v0.16b
	tbl v23.16b, {v31.16b}, v30.16b
	eor w17, w17, w2
	ror w17, w17, #24
	eor v31.16b, v20.16b, v1.16b
	tbl v20.16b, {v31.16b}, v30.16b
	eor w14, w14, w3
	ror w14, w14, #24
	eor v31.16b, v21.16b, v2.16b
	tbl v21.16b, {v31.16b}, v30.16b
	eor w15, w15, w4
	ror w15, w15, #24
	eor v31.16b, v22.16b, v3.16b
	tbl v22.16b, {v31.16b}, v30.16b
	eor w16, w16, w5
	ror w16, w16, #24
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	eor v31.16b, v5.16b, v18.16b
	ushr v5.4s, v31.4s, #25
	sli v5.4s, v31.4s, #7
	eor w7, w7, w12
	ror w7, w7, #25
	eor v31.16b, v6.16b, v19.16b
	ushr v6.4s, v31.4s, #25
	sli v6.4s, v31.4s, #7
	eor w8, w8, w13
	ror w8, w8, #25
	eor v31.16b, v7.16b, v16.16b
	ushr v7.4s, v31.4s, #25
	sli v7.4s, v31.4s, #7
	eor w9, w9, w10
	ror w9, w9, #25
	eor v31.16b, v4.16b, v17.16b
	ushr v4.4s, v31.4s, #25
	sli v4.4s, v31.4s, #7
	eor w6, w6, w11
	ror w6, w6, #25
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	eor v31.16b, v20.16b, v0.16b
	rev32 v20.8h, v31.8h
	eor w14, w14, w2
	ror w14, w14, #16
	eor v31.16b, v21.16b, v1.16b
	rev32 v21.8h, v31.8h
	eor w15, w15, w3
	ror w15, w15, #16
	eor v31.16b, v22.16b, v2.16b
	rev32 v22.8h, v31.8h
	eor w16, w16, w4
	ror w16, w16, #16
	eor v31.16b, v23.16b, v3.16b
	rev32 v23.8h, v31.8h
	eor w17, w17, w5
	ror w17, w17, #16
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	eor v31.16b, v4.16b, v16.16b
	ushr v4.4s, v31.4s, #20
	sli v4.4s, v31.4s, #12
	eor w6, w6, w10
	ror w6, w6, #20
	eor v31.16b, v5.16b, v17.16b
	ushr v5.4s, v31.4s, #20
	sli v5.4s, v31.4s, #12
	eor w7, w7, w11
	ror w7, w7, #20
	eor v31.16b, v6.16b, v18.16b
	ushr v6.4s, v31.4s, #20
	sli v6.4s, v31.4s, #12
	eor w8, w8, w12
	ror w8, w8, #20
	eor v31.16b, v7.16b, v19.16b
	ushr v7.4s, v31.4s, #20
	sli v7.4s, v31.4s, #12
	eor w9, w9, w13
	ror w9, w9, #20
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	eor v31.16b, v20.16b, v0.16b
	tbl v20.16b, {v31.16b}, v30.16b
	eor w14, w14, w2
	ror w14, w14, #24
	eor v31.16b, v21.16b, v1.16b
	tbl v21.16b, {v31.16b}, v30.16b
	eor w15, w15, w3
	ror w15, w15, #24
	eor v31.16b, v22.16b, v2.16b
	tbl v22.16b, {v31.16b}, v30.16b
	eor w16, w16, w4
	ror w16, w16, #24
	eor v31.16b, v23.16b, v3.16b
	tbl v23.16b, {v31.16b}, v30.16b
	eor w17, w17, w5
	ror w17, w17, #24
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	eor v31.16b, v4.16b, v16.16b
	ushr v4.4s, v31.4s, #25
	sli v4.4s, v31.4s, #7
	eor w6, w6, w10
	ror w6, w6, #25
	eor v31.16b, v5.16b, v17.16b
	ushr v5.4s, v31.4s, #25
	sli v5.4s, v31.4s, #7
	eor w7, w7, w11
	ror w7, w7, #25
	eor v31.16b, v6.16b, v18.16b
	ushr v6.4s, v31.4s, #25
	sli v6.4s, v31.4s, #7
	eor w8, w8, w12
	ror w8, w8, #25
	eor v31.16b, v7.16b, v19.16b
	ushr v7.4s, v31.4s, #25
	sli v7.4s, v31.4s, #7
	eor w9, w9, w13
	ror w9, w9, #25
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	eor v31.16b, v23.16b, v0.16b
	rev32 v23.8h, v31.8h
	eor w17, w17, w2
	ror w17, w17, #16
	eor v31.16b, v20.16b, v1.16b
	rev32 v20.8h, v31.8h
	eor w14, w14, w3
	ror w14, w14, #16
	eor v31.16b, v21.16b, v2.16b
	rev32 v21.8h, v31.8h
	eor w15, w15, w4
	ror w15, w15, #16
	eor v31.16b, v22.16b, v3.16b
	rev32 v22.8h, v31.8h
	eor w16, w16, w5
	ror w16, w16, #16
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	eor v31.16b, v5.16b, v18.16b
	ushr v5.4s, v31.4s, #20
	sli v5.4s, v31.4s, #12
	eor w7, w7, w12
	ror w7, w7, #20
	eor v31.16b, v6.16b, v19.16b
	ushr v6.4s, v31.4s, #20
	sli v6.4s, v31.4s, #12
	eor w8, w8, w13
	ror w8, w8, #20
	eor v31.16b, v7.16b, v16.16b
	ushr v7.4s, v31.4s, #20
	sli v7.4s, v31.4s, #12
	eor w9, w9, w10
	ror w9, w9, #20
	eor v31.16b, v4.16b, v17.16b
	ushr v4.4s, v31.4s, #20
	sli v4.4s, v31.4s, #12
	eor w6, w6, w11
	ror w6, w6, #20
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	eor v31.16b, v23.16b, v0.16b
	tbl v23.16b, {v31.16b}, v30.16b
	eor w17, w17, w2
	ror w17, w17, #24
	eor v31.16b, v20.16b, v1.16b
	tbl v20.16b, {v31.16b}, v30.16b
	eor w14, w14, w3
	ror w14, w14, #24
	eor v31.16b, v21.16b, v2.16b
	tbl v21.16b, {v31.16b}, v30.16b
	eor w15, w15, w4
	ror w15, w15, #24
	eor v31.16b, v22.16b, v3.16b
	tbl v22.16b, {v31.16b}, v30.16b
	eor w16, w16, w5
	ror w16, w16, #24
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	eor v31.16b, v5.16b, v18.16b
	ushr v5.4s, v31.4s, #25
	sli v5.4s, v31.4s, #7
	eor w7, w7, w12
	ror w7, w7, #25
	eor v31.16b, v6.16b, v19.16b
	ushr v6.4s, v31.4s, #25
	sli v6.4s, v31.4s, #7
	eor w8, w8, w13
	ror w8, w8, #25
	eor v31.16b, v7.16b, v16.16b
	ushr v7.4s, v31.4s, #25
	sli v7.4s, v31.4s, #7
	eor w9, w9, w10
	ror w9, w9, #25
	eor v31.16b, v4.16b, v17.16b
	ushr v4.4s, v31.4s, #25
	sli v4.4s, v31.4s, #7
	eor w6, w6, w11
	ror w6, w6, #25
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	eor v31.16b, v20.16b, v0.16b
	rev32 v20.8h, v31.8h
	eor w14, w14, w2
	ror w14, w14, #16
	eor v31.16b, v21.16b, v1.16b
	rev32 v21.8h, v31.8h
	eor w15, w15, w3
	ror w15, w15, #16
	eor v31.16b, v22.16b, v2.16b
	rev32 v22.8h, v31.8h
	eor w16, w16, w4
	ror w16, w16, #16
	eor v31.16b, v23.16b, v3.16b
	rev32 v23.8h, v31.8h
	eor w17, w17, w5
	ror w17, w17, #16
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	eor v31.16b, v4.16b, v16.16b
	ushr v4.4s, v31.4s, #20
	sli v4.4s, v31.4s, #12
	eor w6, w6, w10
	ror w6, w6, #20
	eor v31.16b, v5.16b, v17.16b
	ushr v5.4s, v31.4s, #20
	sli v5.4s, v31.4s, #12
	eor w7, w7, w11
	ror w7, w7, #20
	eor v31.16b, v6.16b, v18.16b
	ushr v6.4s, v31.4s, #20
	sli v6.4s, v31.4s, #12
	eor w8, w8, w12
	ror w8, w8, #20
	eor v31.16b, v7.16b, v19.16b
	ushr v7.4s, v31.4s, #20
	sli v7.4s, v31.4s, #12
	eor w9, w9, w13
	ror w9, w9, #20
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	eor v31.16b, v20.16b, v0.16b
	tbl v20.16b, {v31.16b}, v30.16b
	eor w14, w14, w2
	ror w14, w14, #24
	eor v31.16b, v21.16b, v1.16b
	tbl v21.16b, {v31.16b}, v30.16b
	eor w15, w15, w3
	ror w15, w15, #24
	eor v31.16b, v22.16b, v2.16b
	tbl v22.16b, {v31.16b}, v30.16b
	eor w16, w16, w4
	ror w16, w16, #24
	eor v31.16b, v23.16b, v3.16b
	tbl v23.16b, {v31.16b}, v30.16b
	eor w17, w17, w5
	ror w17, w17, #24
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	eor v31.16b, v4.16b, v16.16b
	ushr v4.4s, v31.4s, #25
	sli v4.4s, v31.4s, #7
	eor w6, w6, w10
	ror w6, w6, #25
	eor v31.16b, v5.16b, v17.16b
	ushr v5.4s, v31.4s, #25
	sli v5.4s, v31.4s, #7
	eor w7, w7, w11
	ror w7, w7, #25
	eor v31.16b, v6.16b, v18.16b
	ushr v6.4s, v31.4s, #25
	sli v6.4s, v31.4s, #7
	eor w8, w8, w12
	ror w8, w8, #25
	eor v31.16b, v7.16b, v19.16b
	ushr v7.4s, v31.4s, #25
	sli v7.4s, v31.4s, #7
	eor w9, w9, w13
	ror w9, w9, #25
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	eor v31.16b, v23.16b, v0.16b
	rev32 v23.8h, v31.8h
	eor w17, w17, w2
	ror w17, w17, #16
	eor v31.16b, v20.16b, v1.16b
	rev32 v20.8h, v31.8h
	eor w14, w14, w3
	ror w14, w14, #16
	eor v31.16b, v21.16b, v2.16b
	rev32 v21.8h, v31.8h
	eor w15, w15, w4
	ror w15, w15, #16
	eor v31.16b, v22.16b, v3.16b
	rev32 v22.8h, v31.8h
	eor w16, w16, w5
	ror w16, w16, #16
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	eor v31.16b, v5.16b, v18.16b
	ushr v5.4s, v31.4s, #20
	sli v5.4s, v31.4s, #12
	eor w7, w7, w12
	ror w7, w7, #20
	eor v31.16b, v6.16b, v19.16b
	ushr v6.4s, v31.4s, #20
	sli v6.4s, v31.4s, #12
	eor w8, w8, w13
	ror w8, w8, #20
	eor v31.16b, v7.16b, v16.16b
	ushr v7.4s, v31.4s, #20
	sli v7.4s, v31.4s, #12
	eor w9, w9, w10
	ror w9, w9, #20
	eor v31.16b, v4.16b, v17.16b
	ushr v4.4s, v31.4s, #20
	sli v4.4s, v31.4s, #12
	eor w6, w6, w11
	ror w6, w6, #20
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	eor v31.16b, v23.16b, v0.16b
	tbl v23.16b, {v31.16b}, v30.16b
	eor w17, w17, w2
	ror w17, w17, #24
	eor v31.16b, v20.16b, v1.16b
	tbl v20.16b, {v31.16b}, v30.16b
	eor w14, w14, w3
	ror w14, w14, #24
	eor v31.16b, v21.16b, v2.16b
	tbl v21.16b, {v31.16b}, v30.16b
	eor w15, w15, w4
	ror w15, w15, #24
	eor v31.16b, v22.16b, v3.16b
	tbl v22.16b, {v31.16b}, v30.16b
	eor w16, w16, w5
	ror w16, w16, #24
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	eor v31.16b, v5.16b, v18.16b
	ushr v5.4s, v31.4s, #25
	sli v5.4s, v31.4s, #7
	eor w7, w7, w12
	ror w7, w7, #25
	eor v31.16b, v6.16b, v19.16b
	ushr v6.4s, v31.4s, #25
	sli v6.4s, v31.4s, #7
	eor w8, w8, w13
	ror w8, w8, #25
	eor v31.16b, v7.16b, v16.16b
	ushr v7.4s, v31.4s, #25
	sli v7.4s, v31.4s, #7
	eor w9, w9, w10
	ror w9, w9, #25
	eor v31.16b, v4.16b, v17.16b
	ushr v4.4s, v31.4s, #25
	sli v4.4s, v31.4s, #7
	eor w6, w6, w11
	ror w6, w6, #25
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	eor v31.16b, v20.16b, v0.16b
	rev32 v20.8h, v31.8h
	eor w14, w14, w2
	ror w14, w14, #16
	eor v31.16b, v21.16b, v1.16b
	rev32 v21.8h, v31.8h
	eor w15, w15, w3
	ror w15, w15, #16
	eor v31.16b, v22.16b, v2.16b
	rev32 v22.8h, v31.8h
	eor w16, w16, w4
	ror w16, w16, #16
	eor v31.16b, v23.16b, v3.16b
	rev32 v23.8h, v31.8h
	eor w17, w17, w5
	ror w17, w17, #16
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	eor v31.16b, v4.16b, v16.16b
	ushr v4.4s, v31.4s, #20
	sli v4.4s, v31.4s, #12
	eor w6, w6, w10
	ror w6, w6, #20
	eor v31.16b, v5.16b, v17.16b
	ushr v5.4s, v31.4s, #20
	sli v5.4s, v31.4s, #12
	eor w7, w7, w11
	ror w7, w7, #20
	eor v31.16b, v6.16b, v18.16b
	ushr v6.4s, v31.4s, #20
	sli v6.4s, v31.4s, #12
	eor w8, w8, w12
	ror w8, w8, #20
	eor v31.16b, v7.16b, v19.16b
	ushr v7.4s, v31.4s, #20
	sli v7.4s, v31.4s, #12
	eor w9, w9, w13
	ror w9, w9, #20
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	eor v31.16b, v20.16b, v0.16b
	tbl v20.16b, {v31.16b}, v30.16b
	eor w14, w14, w2
	ror w14, w14, #24
	eor v31.16b, v21.16b, v1.16b
	tbl v21.16b, {v31.16b}, v30.16b
	eor w15, w15, w3
	ror w15, w15, #24
	eor v31.16b, v22.16b, v2.16b
	tbl v22.16b, {v31.16b}, v30.16b
	eor w16, w16, w4
	ror w16, w16, #24
	eor v31.16b, v23.16b, v3.16b
	tbl v23.16b, {v31.16b}, v30.16b
	eor w17, w17, w5
	ror w17, w17, #24
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	eor v31.16b, v4.16b, v16.16b
	ushr v4.4s, v31.4s, #25
	sli v4.4s, v31.4s, #7
	eor w6, w6, w10
	ror w6, w6, #25
	eor v31.16b, v5.16b, v17.16b
	ushr v5.4s, v31.4s, #25
	sli v5.4s, v31.4s, #7
	eor w7, w7, w11
	ror w7, w7, #25
	eor v31.16b, v6.16b, v18.16b
	ushr v6.4s, v31.4s, #25
	sli v6.4s, v31.4s, #7
	eor w8, w8, w12
	ror w8, w8, #25
	eor v31.16b, v7.16b, v19.16b
	ushr v7.4s, v31.4s, #25
	sli v7.4s, v31.4s, #7
	eor w9, w9, w13
	ror w9, w9, #25
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	eor v31.16b, v23.16b, v0.16b
	rev32 v23.8h, v31.8h
	eor w17, w17, w2
	ror w17, w17, #16
	eor v31.16b, v20.16b, v1.16b
	rev32 v20.8h, v31.8h
	eor w14, w14, w3
	ror w14, w14, #16
	eor v31.16b, v21.16b, v2.16b
	rev32 v21.8h, v31.8h
	eor w15, w15, w4
	ror w15, w15, #16
	eor v31.16b, v22.16b, v3.16b
	rev32 v22.8h, v31.8h
	eor w16, w16, w5
	ror w16, w16, #16
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	eor v31.16b, v5.16b, v18.16b
	ushr v5.4s, v31.4s, #20
	sli v5.4s, v31.4s, #12
	eor w7, w7, w12
	ror w7, w7, #20
	eor v31.16b, v6.16b, v19.16b
	ushr v6.4s, v31.4s, #20
	sli v6.4s, v31.4s, #12
	eor w8, w8, w13
	ror w8, w8, #20
	eor v31.16b, v7.16b, v16.16b
	ushr v7.4s, v31.4s, #20
	sli v7.4s, v31.4s, #12
	eor w9, w9, w10
	ror w9, w9, #20
	eor v31.16b, v4.16b, v17.16b
	ushr v4.4s, v31.4s, #20
	sli v4.4s, v31.4s, #12
	eor w6, w6, w11
	ror w6, w6, #20
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	eor v31.16b, v23.16b, v0.16b
	tbl v23.16b, {v31.16b}, v30.16b
	eor w17, w17, w2
	ror w17, w17, #24
	eor v31.16b, v20.16b, v1.16b
	tbl v20.16b, {v31.16b}, v30.16b
	eor w14, w14, w3
	ror w14, w14, #24
	eor v31.16b, v21.16b, v2.16b
	tbl v21.16b, {v31.16b}, v30.16b
	eor w15, w15, w4
	ror w15, w15, #24
	eor v31.16b, v22.16b, v3.16b
	tbl v22.16b, {v31.16b}, v30.16b
	eor w16, w16, w5
	ror w16, w16, #24
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	eor v31.16b, v5.16b, v18.16b
	ushr v5.4s, v31.4s, #25
	sli v5.4s, v31.4s, #7
	eor w7, w7, w12
	ror w7, w7, #25
	eor v31.16b, v6.16b, v19.16b
	ushr v6.4s, v31.4s, #25
	sli v6.4s, v31.4s, #7
	eor w8, w8, w13
	ror w8, w8, #25
	eor v31.16b, v7.16b, v16.16b
	ushr v7.4s, v31.4s, #25
	sli v7.4s, v31.4s, #7
	eor w9, w9, w10
	ror w9, w9, #25
	eor v31.16b, v4.16b, v17.16b
	ushr v4.4s, v31.4s, #25
	sli v4.4s, v31.4s, #7
	eor w6, w6, w11
	ror w6, w6, #25
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	eor v31.16b, v20.16b, v0.16b
	rev32 v20.8h, v31.8h
	eor w14, w14, w2
	ror w14, w14, #16
	eor v31.16b, v21.16b, v1.16b
	rev32 v21.8h, v31.8h
	eor w15, w15, w3
	ror w15, w15, #16
	eor v31.16b, v22.16b, v2.16b
	rev32 v22.8h, v31.8h
	eor w16, w16, w4
	ror w16, w16, #16
	eor v31.16b, v23.16b, v3.16b
	rev32 v23.8h, v31.8h
	eor w17, w17, w5
	ror w17, w17, #16
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	eor v31.16b, v4.16b, v16.16b
	ushr v4.4s, v31.4s, #20
	sli v4.4s, v31.4s, #12
	eor w6, w6, w10
	ror w6, w6, #20
	eor v31.16b, v5.16b, v17.16b
	ushr v5.4s, v31.4s, #20
	sli v5.4s, v31.4s, #12
	eor w7, w7, w11
	ror w7, w7, #20
	eor v31.16b, v6.16b, v18.16b
	ushr v6.4s, v31.4s, #20
	sli v6.4s, v31.4s, #12
	eor w8, w8, w12
	ror w8, w8, #20
	eor v31.16b, v7.16b, v19.16b
	ushr v7.4s, v31.4s, #20
	sli v7.4s, v31.4s, #12
	eor w9, w9, w13
	ror w9, w9, #20
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	eor v31.16b, v20.16b, v0.16b
	tbl v20.16b, {v31.16b}, v30.16b
	eor w14, w14, w2
	ror w14, w14, #24
	eor v31.16b, v21.16b, v1.16b
	tbl v21.16b, {v31.16b}, v30.16b
	eor w15, w15, w3
	ror w15, w15, #24
	eor v31.16b, v22.16b, v2.16b
	tbl v22.16b, {v31.16b}, v30.16b
	eor w16, w16, w4
	ror w16, w16, #24
	eor v31.16b, v23.16b, v3.16b
	tbl v23.16b, {v31.16b}, v30.16b
	eor w17, w17, w5
	ror w17, w17, #24
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	eor v31.16b, v4.16b, v16.16b
	ushr v4.4s, v31.4s, #25
	sli v4.4s, v31.4s, #7
	eor w6, w6, w10
	ror w6, w6, #25
	eor v31.16b, v5.16b, v17.16b
	ushr v5.4s, v31.4s, #25
	sli v5.4s, v31.4s, #7
	eor w7, w7, w11
	ror w7, w7, #25
	eor v31.16b, v6.16b, v18.16b
	ushr v6.4s, v31.4s, #25
	sli v6.4s, v31.4s, #7
	eor w8, w8, w12
	ror w8, w8, #25
	eor v31.16b, v7.16b, v19.16b
	ushr v7.4s, v31.4s, #25
	sli v7.4s, v31.4s, #7
	eor w9, w9, w13
	ror w9, w9, #25
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	eor v31.16b, v23.16b, v0.16b
	rev32 v23.8h, v31.8h
	eor w17, w17, w2
	ror w17, w17, #16
	eor v31.16b, v20.16b, v1.16b
	rev32 v20.8h, v31.8h
	eor w14, w14, w3
	ror w14, w14, #16
	eor v31.16b, v21.16b, v2.16b
	rev32 v21.8h, v31.8h
	eor w15, w15, w4
	ror w15, w15, #16
	eor v31.16b, v22.16b, v3.16b
	rev32 v22.8h, v31.8h
	eor w16, w16, w5
	ror w16, w16, #16
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	eor v31.16b, v5.16b, v18.16b
	ushr v5.4s, v31.4s, #20
	sli v5.4s, v31.4s, #12
	eor w7, w7, w12
	ror w7, w7, #20
	eor v31.16b, v6.16b, v19.16b
	ushr v6.4s, v31.4s, #20
	sli v6.4s, v31.4s, #12
	eor w8, w8, w13
	ror w8, w8, #20
	eor v31.16b, v7.16b, v16.16b
	ushr v7.4s, v31.4s, #20
	sli v7.4s, v31.4s, #12
	eor w9, w9, w10
	ror w9, w9, #20
	eor v31.16b, v4.16b, v17.16b
	ushr v4.4s, v31.4s, #20
	sli v4.4s, v31.4s, #12
	eor w6, w6, w11
	ror w6, w6, #20
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	eor v31.16b, v23.16b, v0.16b
	tbl v23.16b, {v31.16b}, v30.16b
	eor w17, w17, w2
	ror w17, w17, #24
	eor v31.16b, v20.16b, v1.16b
	tbl v20.16b, {v31.16b}, v30.16b
	eor w14, w14, w3
	ror w14, w14, #24
	eor v31.16b, v21.16b, v2.16b
	tbl v21.16b, {v31.16b}, v30.16b
	eor w15, w15, w4
	ror w15, w15, #24
	eor v31.16b, v22.16b, v3.16b
	tbl v22.16b, {v31.16b}, v30.16b
	eor w16, w16, w5
	ror w16, w16, #24
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	eor v31.16b, v5.16b, v18.16b
	ushr v5.4s, v31.4s, #25
	sli v5.4s, v31.4s, #7
	eor w7, w7, w12
	ror w7, w7, #25
	eor v31.16b, v6.16b, v19.16b
	ushr v6.4s, v31.4s, #25
	sli v6.4s, v31.4s, #7
	eor w8, w8, w13
	ror w8, w8, #25
	eor v31.16b, v7.16b, v16.16b
	ushr v7.4s, v31.4s, #25
	sli v7.4s, v31.4s, #7
	eor w9, w9, w10
	ror w9, w9, #25
	eor v31.16b, v4.16b, v17.16b
	ushr v4.4s, v31.4s, #25
	sli v4.4s, v31.4s, #7
	eor w6, w6, w11
	ror w6, w6, #25
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	eor v31.16b, v20.16b, v0.16b
	rev32 v20.8h, v31.8h
	eor w14, w14, w2
	ror w14, w14, #16
	eor v31.16b, v21.16b, v1.16b
	rev32 v21.8h, v31.8h
	eor w15, w15, w3
	ror w15, w15, #16
	eor v31.16b, v22.16b, v2.16b
	rev32 v22.8h, v31.8h
	eor w16, w16, w4
	ror w16, w16, #16
	eor v31.16b, v23.16b, v3.16b
	rev32 v23.8h, v31.8h
	eor w17, w17, w5
	ror w17, w17, #16
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	eor v31.16b, v4.16b, v16.16b
	ushr v4.4s, v31.4s, #20
	sli v4.4s, v31.4s, #12
	eor w6, w6, w10
	ror w6, w6, #20
	eor v31.16b, v5.16b, v17.16b
	ushr v5.4s, v31.4s, #20
	sli v5.4s, v31.4s, #12
	eor w7, w7, w11
	ror w7, w7, #20
	eor v31.16b, v6.16b, v18.16b
	ushr v6.4s, v31.4s, #20
	sli v6.4s, v31.4s, #12
	eor w8, w8, w12
	ror w8, w8, #20
	eor v31.16b, v7.16b, v19.16b
	ushr v7.4s, v31.4s, #20
	sli v7.4s, v31.4s, #12
	eor w9, w9, w13
	ror w9, w9, #20
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	eor v31.16b, v20.16b, v0.16b
	tbl v20.16b, {v31.16b}, v30.16b
	eor w14, w14, w2
	ror w14, w14, #24
	eor v31.16b, v21.16b, v1.16b
	tbl v21.16b, {v31.16b}, v30.16b
	eor w15, w15, w3
	ror w15, w15, #24
	eor v31.16b, v22.16b, v2.16b
	tbl v22.16b, {v31.16b}, v30.16b
	eor w16, w16, w4
	ror w16, w16, #24
	eor v31.16b, v23.16b, v3.16b
	tbl v23.16b, {v31.16b}, v30.16b
	eor w17, w17, w5
	ror w17, w17, #24
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	eor v31.16b, v4.16b, v16.16b
	ushr v4.4s, v31.4s, #25
	sli v4.4s, v31.4s, #7
	eor w6, w6, w10
	ror w6, w6, #25
	eor v31.16b, v5.16b, v17.16b
	ushr v5.4s, v31.4s, #25
	sli v5.4s, v31.4s, #7
	eor w7, w7, w11
	ror w7, w7, #25
	eor v31.16b, v6.16b, v18.16b
	ushr v6.4s, v31.4s, #25
	sli v6.4s, v31.4s, #7
	eor w8, w8, w12
	ror w8, w8, #25
	eor v31.16b, v7.16b, v19.16b
	ushr v7.4s, v31.4s, #25
	sli v7.4s, v31.4s, #7
	eor w9, w9, w13
	ror w9, w9, #25
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	eor v31.16b, v23.16b, v0.16b
	rev32 v23.8h, v31.8h
	eor w17, w17, w2
	ror w17, w17, #16
	eor v31.16b, v20.16b, v1.16b
	rev32 v20.8h, v31.8h
	eor w14, w14, w3
	ror w14, w14, #16
	eor v31.16b, v21.16b, v2.16b
	rev32 v21.8h, v31.8h
	eor w15, w15, w4
	ror w15, w15, #16
	eor v31.16b, v22.16b, v3.16b
	rev32 v22.8h, v31.8h
	eor w16, w16, w5
	ror w16, w16, #16
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	eor v31.16b, v5.16b, v18.16b
	ushr v5.4s, v31.4s, #20
	sli v5.4s, v31.4s, #12
	eor w7, w7, w12
	ror w7, w7, #20
	eor v31.16b, v6.16b, v19.16b
	ushr v6.4s, v31.4s, #20
	sli v6.4s, v31.4s, #12
	eor w8, w8, w13
	ror w8, w8, #20
	eor v31.16b, v7.16b, v16.16b
	ushr v7.4s, v31.4s, #20
	sli v7.4s, v31.4s, #12
	eor w9, w9, w10
	ror w9, w9, #20
	eor v31.16b, v4.16b, v17.16b
	ushr v4.4s, v31.4s, #20
	sli v4.4s, v31.4s, #12
	eor w6, w6, w11
	ror w6, w6, #20
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	eor v31.16b, v23.16b, v0.16b
	tbl v23.16b, {v31.16b}, v30.16b
	eor w17, w17, w2
	ror w17, w17, #24
	eor v31.16b, v20.16b, v1.16b
	tbl v20.16b, {v31.16b}, v30.16b
	eor w14, w14, w3
	ror w14, w14, #24
	eor v31.16b, v21.16b, v2.16b
	tbl v21.16b, {v31.16b}, v30.16b
	eor w15, w15, w4
	ror w15, w15, #24
	eor v31.16b, v22.16b, v3.16b
	tbl v22.16b, {v31.16b}, v30.16b
	eor w16, w16, w5
	ror w16, w16, #24
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	eor v31.16b, v5.16b, v18.16b
	ushr v5.4s, v31.4s, #25
	sli v5.4s, v31.4s, #7
	eor w7, w7, w12
	ror w7, w7, #25
	eor v31.16b, v6.16b, v19.16b
	ushr v6.4s, v31.4s, #25
	sli v6.4s, v31.4s, #7
	eor w8, w8, w13
	ror w8, w8, #25
	eor v31.16b, v7.16b, v16.16b
	ushr v7.4s, v31.4s, #25
	sli v7.4s, v31.4s, #7
	eor w9, w9, w10
	ror w9, w9, #25
	eor v31.16b, v4.16b, v17.16b
	ushr v4.4s, v31.4s, #25
	sli v4.4s, v31.4s, #7
	eor w6, w6, w11
	ror w6, w6, #25
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	eor v31.16b, v20.16b, v0.16b
	rev32 v20.8h, v31.8h
	eor w14, w14, w2
	ror w14, w14, #16
	eor v31.16b, v21.16b, v1.16b
	rev32 v21.8h, v31.8h
	eor w15, w15, w3
	ror w15, w15, #16
	eor v31.16b, v22.16b, v2.16b
	rev32 v22.8h, v31.8h
	eor w16, w16, w4
	ror w16, w16, #16
	eor v31.16b, v23.16b, v3.16b
	rev32 v23.8h, v31.8h
	eor w17, w17, w5
	ror w17, w17, #16
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	eor v31.16b, v4.16b, v16.16b
	ushr v4.4s, v31.4s, #20
	sli v4.4s, v31.4s, #12
	eor w6, w6, w10
	ror w6, w6, #20
	eor v31.16b, v5.16b, v17.16b
	ushr v5.4s, v31.4s, #20
	sli v5.4s, v31.4s, #12
	eor w7, w7, w11
	ror w7, w7, #20
	eor v31.16b, v6.16b, v18.16b
	ushr v6.4s, v31.4s, #20
	sli v6.4s, v31.4s, #12
	eor w8, w8, w12
	ror w8, w8, #20
	eor v31.16b, v7.16b, v19.16b
	ushr v7.4s, v31.4s, #20
	sli v7.4s, v31.4s, #12
	eor w9, w9, w13
	ror w9, w9, #20
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	eor v31.16b, v20.16b, v0.16b
	tbl v20.16b, {v31.16b}, v30.16b
	eor w14, w14, w2
	ror w14, w14, #24
	eor v31.16b, v21.16b, v1.16b
	tbl v21.16b, {v31.16b}, v30.16b
	eor w15, w15, w3
	ror w15, w15, #24
	eor v31.16b, v22.16b, v2.16b
	tbl v22.16b, {v31.16b}, v30.16b
	eor w16, w16, w4
	ror w16, w16, #24
	eor v31.16b, v23.16b, v3.16b
	tbl v23.16b, {v31.16b}, v30.16b
	eor w17, w17, w5
	ror w17, w17, #24
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	eor v31.16b, v4.16b, v16.16b
	ushr v4.4s, v31.4s, #25
	sli v4.4s, v31.4s, #7
	eor w6, w6, w10
	ror w6, w6, #25
	eor v31.16b, v5.16b, v17.16b
	ushr v5.4s, v31.4s, #25
	sli v5.4s, v31.4s, #7
	eor w7, w7, w11
	ror w7, w7, #25
	eor v31.16b, v6.16b, v18.16b
	ushr v6.4s, v31.4s, #25
	sli v6.4s, v31.4s, #7
	eor w8, w8, w12
	ror w8, w8, #25
	eor v31.16b, v7.16b, v19.16b
	ushr v7.4s, v31.4s, #25
	sli v7.4s, v31.4s, #7
	eor w9, w9, w13
	ror w9, w9, #25
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	eor v31.16b, v23.16b, v0.16b
	rev32 v23.8h, v31.8h
	eor w17, w17, w2
	ror w17, w17, #16
	eor v31.16b, v20.16b, v1.16b
	rev32 v20.8h, v31.8h
	eor w14, w14, w3
	ror w14, w14, #16
	eor v31.16b, v21.16b, v2.16b
	rev32 v21.8h, v31.8h
	eor w15, w15, w4
	ror w15, w15, #16
	eor v31.16b, v22.16b, v3.16b
	rev32 v22.8h, v31.8h
	eor w16, w16, w5
	ror w16, w16, #16
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	eor v31.16b, v5.16b, v18.16b
	ushr v5.4s, v31.4s, #20
	sli v5.4s, v31.4s, #12
	eor w7, w7, w12
	ror w7, w7, #20
	eor v31.16b, v6.16b, v19.16b
	ushr v6.4s, v31.4s, #20
	sli v6.4s, v31.4s, #12
	eor w8, w8, w13
	ror w8, w8, #20
	eor v31.16b, v7.16b, v16.16b
	ushr v7.4s, v31.4s, #20
	sli v7.4s, v31.4s, #12
	eor w9, w9, w10
	ror w9, w9, #20
	eor v31.16b, v4.16b, v17.16b
	ushr v4.4s, v31.4s, #20
	sli v4.4s, v31.4s, #12
	eor w6, w6, w11
	ror w6, w6, #20
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	eor v31.16b, v23.16b, v0.16b
	tbl v23.16b, {v31.16b}, v30.16b
	eor w17, w17, w2
	ror w17, w17, #24
	eor v31.16b, v20.16b, v1.16b
	tbl v20.16b, {v31.16b}, v30.16b
	eor w14, w14, w3
	ror w14, w14, #24
	eor v31.16b, v21.16b, v2.16b
	tbl v21.16b, {v31.16b}, v30.16b
	eor w15, w15, w4
	ror w15, w15, #24
	eor v31.16b, v22.16b, v3.16b
	tbl v22.16b, {v31.16b}, v30.16b
	eor w16, w16, w5
	ror w16, w16, #24
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	eor v31.16b, v5.16b, v18.16b
	ushr v5.4s, v31.4s, #25
	sli v5.4s, v31.4s, #7
	eor w7, w7, w12
	ror w7, w7, #25
	eor v31.16b, v6.16b, v19.16b
	ushr v6.4s, v31.4s, #25
	sli v6.4s, v31.4s, #7
	eor w8, w8, w13
	ror w8, w8, #25
	eor v31.16b, v7.16b, v16.16b
	ushr v7.4s, v31.4s, #25
	sli v7.4s, v31.4s, #7
	eor w9, w9, w10
	ror w9, w9, #25
	eor v31.16b, v4.16b, v17.16b
	ushr v4.4s, v31.4s, #25
	sli v4.4s, v31.4s, #7
	eor w6, w6, w11
	ror w6, w6, #25
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	eor v31.16b, v20.16b, v0.16b
	rev32 v20.8h, v31.8h
	eor w14, w14, w2
	ror w14, w14, #16
	eor v31.16b, v21.16b, v1.16b
	rev32 v21.8h, v31.8h
	eor w15, w15, w3
	ror w15, w15, #16
	eor v31.16b, v22.16b, v2.16b
	rev32 v22.8h, v31.8h
	eor w16, w16, w4
	ror w16, w16, #16
	eor v31.16b, v23.16b, v3.16b
	rev32 v23.8h, v31.8h
	eor w17, w17, w5
	ror w17, w17, #16
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	eor v31.16b, v4.16b, v16.16b
	ushr v4.4s, v31.4s, #20
	sli v4.4s, v31.4s, #12
	eor w6, w6, w10
	ror w6, w6, #20
	eor v31.16b, v5.16b, v17.16b
	ushr v5.4s, v31.4s, #20
	sli v5.4s, v31.4s, #12
	eor w7, w7, w11
	ror w7, w7, #20
	eor v31.16b, v6.16b, v18.16b
	ushr v6.4s, v31.4s, #20
	sli v6.4s, v31.4s, #12
	eor w8, w8, w12
	ror w8, w8, #20
	eor v31.16b, v7.16b, v19.16b
	ushr v7.4s, v31.4s, #20
	sli v7.4s, v31.4s, #12
	eor w9, w9, w13
	ror w9, w9, #20
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	eor v31.16b, v20.16b, v0.16b
	tbl v20.16b, {v31.16b}, v30.16b
	eor w14, w14, w2
	ror w14, w14, #24
	eor v31.16b, v21.16b, v1.16b
	tbl v21.16b, {v31.16b}, v30.16b
	eor w15, w15, w3
	ror w15, w15, #24
	eor v31.16b, v22.16b, v2.16b
	tbl v22.16b, {v31.16b}, v30.16b
	eor w16, w16, w4
	ror w16, w16, #24
	eor v31.16b, v23.16b, v3.16b
	tbl v23.16b, {v31.16b}, v30.16b
	eor w17, w17, w5
	ror w17, w17, #24
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	eor v31.16b, v4.16b, v16.16b
	ushr v4.4s, v31.4s, #25
	sli v4.4s, v31.4s, #7
	eor w6, w6, w10
	ror w6, w6, #25
	eor v31.16b, v5.16b, v17.16b
	ushr v5.4s, v31.4s, #25
	sli v5.4s, v31.4s, #7
	eor w7, w7, w11
	ror w7, w7, #25
	eor v31.16b, v6.16b, v18.16b
	ushr v6.4s, v31.4s, #25
	sli v6.4s, v31.4s, #7
	eor w8, w8, w12
	ror w8, w8, #25
	eor v31.16b, v7.16b, v19.16b
	ushr v7.4s, v31.4s, #25
	sli v7.4s, v31.4s, #7
	eor w9, w9, w13
	ror w9, w9, #25
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	eor v31.16b, v23.16b, v0.16b
	rev32 v23.8h, v31.8h
	eor w17, w17, w2
	ror w17, w17, #16
	eor v31.16b, v20.16b, v1.16b
	rev32 v20.8h, v31.8h
	eor w14, w14, w3
	ror w14, w14, #16
	eor v31.16b, v21.16b, v2.16b
	rev32 v21.8h, v31.8h
	eor w15, w15, w4
	ror w15, w15, #16
	eor v31.16b, v22.16b, v3.16b
	rev32 v22.8h, v31.8h
	eor w16, w16, w5
	ror w16, w16, #16
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	eor v31.16b, v5.16b, v18.16b
	ushr v5.4s, v31.4s, #20
	sli v5.4s, v31.4s, #12
	eor w7, w7, w12
	ror w7, w7, #20
	eor v31.16b, v6.16b, v19.16b
	ushr v6.4s, v31.4s, #20
	sli v6.4s, v31.4s, #12
	eor w8, w8, w13
	ror w8, w8, #20
	eor v31.16b, v7.16b, v16.16b
	ushr v7.4s, v31.4s, #20
	sli v7.4s, v31.4s, #12
	eor w9, w9, w10
	ror w9, w9, #20
	eor v31.16b, v4.16b, v17.16b
	ushr v4.4s, v31.4s, #20
	sli v4.4s, v31.4s, #12
	eor w6, w6, w11
	ror w6, w6, #20
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	eor v31.16b, v23.16b, v0.16b
	tbl v23.16b, {v31.16b}, v30.16b
	eor w17, w17, w2
	ror w17, w17, #24
	eor v31.16b, v20.16b, v1.16b
	tbl v20.16b, {v31.16b}, v30.16b
	eor w14, w14, w3
	ror w14, w14, #24
	eor v31.16b, v21.16b, v2.16b
	tbl v21.16b, {v31.16b}, v30.16b
	eor w15, w15, w4
	ror w15, w15, #24
	eor v31.16b, v22.16b, v3.16b
	tbl v22.16b, {v31.16b}, v30.16b
	eor w16, w16, w5
	ror w16, w16, #24
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	eor v31.16b, v5.16b, v18.16b
	ushr v5.4s, v31.4s, #25
	sli v5.4s, v31.4s, #7
	eor w7, w7, w12
	ror w7, w7, #25
	eor v31.16b, v6.16b, v19.16b
	ushr v6.4s, v31.4s, #25
	sli v6.4s, v31.4s, #7
	eor w8, w8, w13
	ror w8, w8, #25
	eor v31.16b, v7.16b, v16.16b
	ushr v7.4s, v31.4s, #25
	sli v7.4s, v31.4s, #7
	eor w9, w9, w10
	ror w9, w9, #25
	eor v31.16b, v4.16b, v17.16b
	ushr v4.4s, v31.4s, #25
	sli v4.4s, v31.4s, #7
	eor w6, w6, w11
	ror w6, w6, #25
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	eor v31.16b, v20.16b, v0.16b
	rev32 v20.8h, v31.8h
	eor w14, w14, w2
	ror w14, w14, #16
	eor v31.16b, v21.16b, v1.16b
	rev32 v21.8h, v31.8h
	eor w15, w15, w3
	ror w15, w15, #16
	eor v31.16b, v22.16b, v2.16b
	rev32 v22.8h, v31.8h
	eor w16, w16, w4
	ror w16, w16, #16
	eor v31.16b, v23.16b, v3.16b
	rev32 v23.8h, v31.8h
	eor w17, w17, w5
	ror w17, w17, #16
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	eor v31.16b, v4.16b, v16.16b
	ushr v4.4s, v31.4s, #20
	sli v4.4s, v31.4s, #12
	eor w6, w6, w10
	ror w6, w6, #20
	eor v31.16b, v5.16b, v17.16b
	ushr v5.4s, v31.4s, #20
	sli v5.4s, v31.4s, #12
	eor w7, w7, w11
	ror w7, w7, #20
	eor v31.16b, v6.16b, v18.16b
	ushr v6.4s, v31.4s, #20
	sli v6.4s, v31.4s, #12
	eor w8, w8, w12
	ror w8, w8, #20
	eor v31.16b, v7.16b, v19.16b
	ushr v7.4s, v31.4s, #20
	sli v7.4s, v31.4s, #12
	eor w9, w9, w13
	ror w9, w9, #20
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	eor v31.16b, v20.16b, v0.16b
	tbl v20.16b, {v31.16b}, v30.16b
	eor w14, w14, w2
	ror w14, w14, #24
	eor v31.16b, v21.16b, v1.16b
	tbl v21.16b, {v31.16b}, v30.16b
	eor w15, w15, w3
	ror w15, w15, #24
	eor v31.16b, v22.16b, v2.16b
	tbl v22.16b, {v31.16b}, v30.16b
	eor w16, w16, w4
	ror w16, w16, #24
	eor v31.16b, v23.16b, v3.16b
	tbl v23.16b, {v31.16b}, v30.16b
	eor w17, w17, w5
	ror w17, w17, #24
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	eor v31.16b, v4.16b, v16.16b
	ushr v4.4s, v31.4s, #25
	sli v4.4s, v31.4s, #7
	eor w6, w6, w10
	ror w6, w6, #25
	eor v31.16b, v5.16b, v17.16b
	ushr v5.4s, v31.4s, #25
	sli v5.4s, v31.4s, #7
	eor w7, w7, w11
	ror w7, w7, #25
	eor v31.16b, v6.16b, v18.16b
	ushr v6.4s, v31.4s, #25
	sli v6.4s, v31.4s, #7
	eor w8, w8, w12
	ror w8, w8, #25
	eor v31.16b, v7.16b, v19.16b
	ushr v7.4s, v31.4s, #25
	sli v7.4s, v31.4s, #7
	eor w9, w9, w13
	ror w9, w9, #25
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	eor v31.16b, v23.16b, v0.16b
	rev32 v23.8h, v31.8h
	eor w17, w17, w2
	ror w17, w17, #16
	eor v31.16b, v20.16b, v1.16b
	rev32 v20.8h, v31.8h
	eor w14, w14, w3
	ror w14, w14, #16
	eor v31.16b, v21.16b, v2.16b
	rev32 v21.8h, v31.8h
	eor w15, w15, w4
	ror w15, w15, #16
	eor v31.16b, v22.16b, v3.16b
	rev32 v22.8h, v31.8h
	eor w16, w16, w5
	ror w16, w16, #16
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	eor v31.16b, v5.16b, v18.16b
	ushr v5.4s, v31.4s, #20
	sli v5.4s, v31.4s, #12
	eor w7, w7, w12
	ror w7, w7, #20
	eor v31.16b, v6.16b, v19.16b
	ushr v6.4s, v31.4s, #20
	sli v6.4s, v31.4s, #12
	eor w8, w8, w13
	ror w8, w8, #20
	eor v31.16b, v7.16b, v16.16b
	ushr v7.4s, v31.4s, #20
	sli v7.4s, v31.4s, #12
	eor w9, w9, w10
	ror w9, w9, #20
	eor v31.16b, v4.16b, v17.16b
	ushr v4.4s, v31.4s, #20
	sli v4.4s, v31.4s, #12
	eor w6, w6, w11
	ror w6, w6, #20
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	eor v31.16b, v23.16b, v0.16b
	tbl v23.16b, {v31.16b}, v30.16b
	eor w17, w17, w2
	ror w17, w17, #24
	eor v31.16b, v20.16b, v1.16b
	tbl v20.16b, {v31.16b}, v30.16b
	eor w14, w14, w3
	ror w14, w14, #24
	eor v31.16b, v21.16b, v2.16b
	tbl v21.16b, {v31.16b}, v30.16b
	eor w15, w15, w4
	ror w15, w15, #24
	eor v31.16b, v22.16b, v3.16b
	tbl v22.16b, {v31.16b}, v30.16b
	eor w16, w16, w5
	ror w16, w16, #24
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	eor v31.16b, v5.16b, v18.16b
	ushr v5.4s, v31.4s, #25
	sli v5.4s, v31.4s, #7
	eor w7, w7, w12
	ror w7, w7, #25
	eor v31.16b, v6.16b, v19.16b
	ushr v6.4s, v31.4s, #25
	sli v6.4s, v31.4s, #7
	eor w8, w8, w13
	ror w8, w8, #25
	eor v31.16b, v7.16b, v16.16b
	ushr v7.4s, v31.4s, #25
	sli v7.4s, v31.4s, #7
	eor w9, w9, w10
	ror w9, w9, #25
	eor v31.16b, v4.16b, v17.16b
	ushr v4.4s, v31.4s, #25
	sli v4.4s, v31.4s, #7
	eor w6, w6, w11
	ror w6, w6, #25
	add x1, x20, #0
	str w2, [x1, #0]
	ldr w2, [x0, #4]
	add w3, w3, w2
	str w3, [x1, #4]
	ldr w2, [x0, #8]
	add w4, w4, w2
	str w4, [x1, #8]
	ldr w2, [x0, #12]
	add w5, w5, w2
	str w5, [x1, #12]
	ldr w2, [x0, #16]
	add w6, w6, w2
	str w6, [x1, #16]
	ldr w2, [x0, #20]
	add w7, w7, w2
	str w7, [x1, #20]
	ldr w2, [x0, #24]
	add w8, w8, w2
	str w8, [x1, #24]
	ldr w2, [x0, #28]
	add w9, w9, w2
	str w9, [x1, #28]
	ldr w2, [x0, #32]
	add w10, w10, w2
	str w10, [x1, #32]
	ldr w2, [x0, #36]
	add w11, w11, w2
	str w11, [x1, #36]
	ldr w2, [x0, #40]
	add w12, w12, w2
	str w12, [x1, #40]
	ldr w2, [x0, #44]
	add w13, w13, w2
	str w13, [x1, #44]
	ldr w2, [x0, #48]
	add w14, w14, w2
	str w14, [x1, #48]
	ldr w2, [x0, #52]
	add w15, w15, w2
	str w15, [x1, #52]
	ldr w2, [x0, #56]
	add w16, w16, w2
	str w16, [x1, #56]
	ldr w2, [x0, #60]
	add w17, w17, w2
	str w17, [x1, #60]
	ldr w2, [x0, #0]
	ldr w3, [x1, #0]
	add w2, w3, w2
	str w2, [x1, #0]
	add x1, x26, #0
	add x2, x19, #0
	add x3, x20, #0
	ldr w4, [x0, #48]
	sub w4, w4, #4
	str w4, [x0, #48]
	ldr w4, [x0, #0]
	dup v31.4s, w4
	add v0.4s, v0.4s, v31.4s
	ldr w4, [x0, #4]
	dup v31.4s, w4
	add v1.4s, v1.4s, v31.4s
	ldr w4, [x0, #8]
	dup v31.4s, w4
	add v2.4s, v2.4s, v31.4s
	ldr w4, [x0, #12]
	dup v31.4s, w4
	add v3.4s, v3.4s, v31.4s
	ldr w4, [x0, #16]
	dup v31.4s, w4
	add v4.4s, v4.4s, v31.4s
	ldr w4, [x0, #20]
	dup v31.4s, w4
	add v5.4s, v5.4s, v31.4s
	ldr w4, [x0, #24]
	dup v31.4s, w4
	add v6.4s, v6.4s, v31.4s
	ldr w4, [x0, #28]
	dup v31.4s, w4
	add v7.4s, v7.4s, v31.4s
	ldr w4, [x0, #32]
	dup v31.4s, w4
	add v16.4s, v16.4s, v31.4s
	ldr w4, [x0, #36]
	dup v31.4s, w4
	add v17.4s, v17.4s, v31.4s
	ldr w4, [x0, #40]
	dup v31.4s, w4
	add v18.4s, v18.4s, v31.4s
	ldr w4, [x0, #44]
	dup v31.4s, w4
	add v19.4s, v19.4s, v31.4s
	ldr w4, [x0, #48]
	dup v31.4s, w4
	add w4, w4, #1
	mov v31.s[1], w4
	add w4, w4, #1
	mov v31.s[2], w4
	add w4, w4, #1
	mov v31.s[3], w4
	add v20.4s, v20.4s, v31.4s
	ldr w4, [x0, #52]
	dup v31.4s, w4
	add v21.4s, v21.4s, v31.4s
	ldr w4, [x0, #56]
	dup v31.4s, w4
	add v22.4s, v22.4s, v31.4s
	ldr w4, [x0, #60]
	dup v31.4s, w4
	add v23.4s, v23.4s, v31.4s
	zip1 v24.4s, v0.4s, v1.4s
	zip2 v25.4s, v0.4s, v1.4s
	zip1 v26.4s, v2.4s, v3.4s
	zip2 v27.4s, v2.4s, v3.4s
	zip1 v0.2d, v24.2d, v26.2d
	zip2 v1.2d, v24.2d, v26.2d
	zip1 v2.2d, v25.2d, v27.2d
	zip2 v3.2d, v25.2d, v27.2d
	ldr q31, [x1, #0]
	eor v31.16b, v31.16b, v0.16b
	str q31, [x1, #0]
	ldr q31, [x1, #64]
	eor v31.16b, v31.16b, v1.16b
	str q31, [x1, #64]
	ldr q31, [x1, #128]
	eor v31.16b, v31.16b, v2.16b
	str q31, [x1, #128]
	ldr q31, [x1, #192]
	eor v31.16b, v31.16b, v3.16b
	str q31, [x1, #192]
	zip1 v24.4s, v4.4s, v5.4s
	zip2 v25.4s, v4.4s, v5.4s
	zip1 v26.4s, v6.4s, v7.4s
	zip2 v27.4s, v6.4s, v7.4s
	zip1 v4.2d, v24.2d, v26.2d
	zip2 v5.2d, v24.2d, v26.2d
	zip1 v6.2d, v25.2d, v27.2d
	zip2 v7.2d, v25.2d, v27.2d
	ldr q31, [x1, #16]
	eor v31.16b, v31.16b, v4.16b
	str q31, [x1, #16]
	ldr q31, [x1, #80]
	eor v31.16b, v31.16b, v5.16b
	str q31, [x1, #80]
	ldr q31, [x1, #144]
	eor v31.16b, v31.16b, v6.16b
	str q31, [x1, #144]
	ldr q31, [x1, #208]
	eor v31.16b, v31.16b, v7.16b
	str q31, [x1, #208]
	zip1 v24.4s, v16.4s, v17.4s
	zip2 v25.4s, v16.4s, v17.4s
	zip1 v26.4s, v18.4s, v19.4s
	zip2 v27.4s, v18.4s, v19.4s
	zip1 v16.2d, v24.2d, v26.2d
	zip2 v17.2d, v24.2d, v26.2d
	zip1 v18.2d, v25.2d, v27.2d
	zip2 v19.2d, v25.2d, v27.2d
	ldr q31, [x1, #32]
	eor v31.16b, v31.16b, v16.16b
	str q31, [x1, #32]
	ldr q31, [x1, #96]
	eor v31.16b, v31.16b, v17.16b
	str q31, [x1, #96]
	ldr q31, [x1, #160]
	eor v31.16b, v31.16b, v18.16b
	str q31, [x1, #160]
	ldr q31, [x1, #224]
	eor v31.16b, v31.16b, v19.16b
	str q31, [x1, #224]
	zip1 v24.4s, v20.4s, v21.4s
	zip2 v25.4s, v20.4s, v21.4s
	zip1 v26.4s, v22.4s, v23.4s
	zip2 v27.4s, v22.4s, v23.4s
	zip1 v20.2d, v24.2d, v26.2d
	zip2 v21.2d, v24.2d, v26.2d
	zip1 v22.2d, v25.2d, v27.2d
	zip2 v23.2d, v25.2d, v27.2d
	ldr q31, [x1, #48]
	eor v31.16b, v31.16b, v20.16b
	str q31, [x1, #48]
	ldr q31, [x1, #112]
	eor v31.16b, v31.16b, v21.16b
	str q31, [x1, #112]
	ldr q31, [x1, #176]
	eor v31.16b, v31.16b, v22.16b
	str q31, [x1, #176]
	ldr q31, [x1, #240]
	eor v31.16b, v31.16b, v23.16b
	str q31, [x1, #240]
	add x1, x1, #256
	ldr q0, [x3, #0]
	ldr q31, [x1, #0]
	eor v31.16b, v31.16b, v0.16b
	str q31, [x1, #0]
	ldr q4, [x3, #16]
	ldr q31, [x1, #16]
	eor v31.16b, v31.16b, v4.16b
	str q31, [x1, #16]
	ldr q16, [x3, #32]
	ldr q31, [x1, #32]
	eor v31.16b, v31.16b, v16.16b
	str q31, [x1, #32]
	ldr q20, [x3, #48]
	ldr q31, [x1, #48]
	eor v31.16b, v31.16b, v20.16b
	str q31, [x1, #48]
	sub x1, x1, #256
	ldr x19, [x21, #632]
	ldr x20, [x21, #640]
	ldr x26, [x21, #648]
	add x0, x21, #448
	add x1, x21, #64
	bl {vg_poly1305_init}
	sub x9, x23, #1
	lsr x9, x9, #8
	cbz x9, 222f
	ldr w9, [x21, #0]
	str w9, [x21, #64]
	ldr w9, [x21, #4]
	str w9, [x21, #68]
	ldr w9, [x21, #8]
	str w9, [x21, #72]
	ldr w9, [x21, #12]
	str w9, [x21, #76]
	ldr w9, [x21, #16]
	str w9, [x21, #80]
	ldr w9, [x21, #20]
	str w9, [x21, #84]
	ldr w9, [x21, #24]
	str w9, [x21, #88]
	ldr w9, [x21, #28]
	str w9, [x21, #92]
	ldr w9, [x21, #32]
	str w9, [x21, #96]
	ldr w9, [x21, #36]
	str w9, [x21, #100]
	ldr w9, [x21, #40]
	str w9, [x21, #104]
	ldr w9, [x21, #44]
	str w9, [x21, #108]
	movz w9, #5, lsl #0
	str w9, [x21, #112]
	ldr w9, [x21, #52]
	str w9, [x21, #116]
	ldr w9, [x21, #56]
	str w9, [x21, #120]
	ldr w9, [x21, #60]
	str w9, [x21, #124]
	add x14, x23, #0
	movz x23, #256, lsl #0
	add x9, x22, #0
	add x15, x9, #0
	add x10, x21, #128
	lsr x11, x23, #4
	cbz x11, 224f
226:
	ldr q0, [x9, #0]
	ldr q1, [x10, #0]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x15, #0]
	add x9, x9, #16
	add x10, x10, #16
	add x15, x15, #16
	sub x11, x11, #1
	cbnz x11, 226b
	b 225f
224:
225:
	lsl x11, x23, #60
	lsr x11, x11, #60
	cbz x11, 227f
229:
	ldrb w12, [x9, #0]
	ldrb w13, [x10, #0]
	eor w12, w12, w13
	strb w12, [x15, #0]
	add x9, x9, #1
	add x10, x10, #1
	add x15, x15, #1
	sub x11, x11, #1
	cbnz x11, 229b
	b 228f
227:
228:
	add x23, x14, #0
	add x0, x21, #64
	add x1, x22, #256
	sub x2, x23, #256
	add x3, x21, #128
	add x4, x1, #0
	bl {vg_chacha20_xor}
	add x0, x21, #448
	add x1, x24, #0
	lsr x2, x25, #4
	bl {vg_poly1305_blocks}
	lsl x10, x25, #60
	lsr x10, x10, #60
	cbz x10, 230f
	sub x9, x25, x10
	add x1, x24, x9
	movz x11, #0, lsl #0
	str x11, [x21, #16]
	str x11, [x21, #24]
	add x9, x21, #16
232:
	ldrb w11, [x1, #0]
	strb w11, [x9, #0]
	add x1, x1, #1
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 232b
	add x0, x21, #448
	add x1, x21, #16
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 231f
230:
231:
	str x25, [x21, #0]
	str x23, [x21, #8]
	add x0, x21, #448
	add x1, x22, #0
	lsr x2, x23, #4
	bl {vg_poly1305_blocks}
	lsl x10, x23, #60
	lsr x10, x10, #60
	cbz x10, 233f
	sub x9, x23, x10
	add x1, x22, x9
	movz x11, #0, lsl #0
	str x11, [x21, #16]
	str x11, [x21, #24]
	add x9, x21, #16
235:
	ldrb w11, [x1, #0]
	strb w11, [x9, #0]
	add x1, x1, #1
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 235b
	add x0, x21, #448
	add x1, x21, #16
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 234f
233:
234:
	add x0, x21, #448
	add x1, x21, #0
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 223f
222:
	str x25, [x21, #0]
	str x23, [x21, #8]
	add x9, x22, #0
	add x15, x9, #0
	add x10, x21, #128
	lsr x11, x23, #4
	cbz x11, 236f
238:
	ldr q0, [x9, #0]
	ldr q1, [x10, #0]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x15, #0]
	add x9, x9, #16
	add x10, x10, #16
	add x15, x15, #16
	sub x11, x11, #1
	cbnz x11, 238b
	b 237f
236:
237:
	lsl x11, x23, #60
	lsr x11, x11, #60
	cbz x11, 239f
241:
	ldrb w12, [x9, #0]
	ldrb w13, [x10, #0]
	eor w12, w12, w13
	strb w12, [x15, #0]
	add x9, x9, #1
	add x10, x10, #1
	add x15, x15, #1
	sub x11, x11, #1
	cbnz x11, 241b
	b 240f
239:
240:
	add x0, x21, #448
	movz x16, #65535, lsl #0
	movk x16, #4095, lsl #16
	movk x16, #65532, lsl #32
	movk x16, #4095, lsl #48
	ldr x7, [x0, #24]
	and x7, x7, x16
	movz x16, #65532, lsl #0
	movk x16, #4095, lsl #16
	movk x16, #65532, lsl #32
	movk x16, #4095, lsl #48
	ldr x8, [x0, #32]
	and x8, x8, x16
	lsr x17, x8, #2
	add x17, x17, x8
	ldr x4, [x0, #0]
	ldr x5, [x0, #8]
	ldr x6, [x0, #16]
	add x1, x24, #0
	lsr x2, x25, #4
	cbz x2, 242f
244:
	ldr x13, [x1, #0]
	ldr x14, [x1, #8]
	movz x15, #1, lsl #0
	adds x4, x4, x13
	adcs x5, x5, x14
	adc x6, x6, x15
	mul x9, x4, x7
	umulh x10, x4, x7
	mul x13, x5, x17
	umulh x14, x5, x17
	adds x9, x9, x13
	adc x10, x10, x14
	mul x11, x4, x8
	umulh x12, x4, x8
	mul x13, x5, x7
	umulh x14, x5, x7
	adds x11, x11, x13
	adc x12, x12, x14
	mul x13, x6, x17
	movz x14, #0, lsl #0
	adds x11, x11, x13
	adc x12, x12, x14
	mul x13, x6, x7
	adds x11, x11, x10
	adc x12, x12, x13
	add x4, x9, #0
	add x5, x11, #0
	movz x14, #3, lsl #0
	bic x13, x12, x14, ror #0
	and x6, x12, x14
	lsr x12, x12, #2
	add x13, x13, x12
	movz x14, #0, lsl #0
	adds x4, x4, x13
	adcs x5, x5, x14
	adc x6, x6, x14
	add x1, x1, #16
	sub x2, x2, #1
	cbnz x2, 244b
	b 243f
242:
243:
	lsl x10, x25, #60
	lsr x10, x10, #60
	cbz x10, 245f
	movz x11, #0, lsl #0
	str x11, [x21, #16]
	str x11, [x21, #24]
	add x9, x21, #16
247:
	ldrb w11, [x1, #0]
	strb w11, [x9, #0]
	add x1, x1, #1
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 247b
	add x1, x21, #16
	ldr x13, [x1, #0]
	ldr x14, [x1, #8]
	movz x15, #1, lsl #0
	adds x4, x4, x13
	adcs x5, x5, x14
	adc x6, x6, x15
	mul x9, x4, x7
	umulh x10, x4, x7
	mul x13, x5, x17
	umulh x14, x5, x17
	adds x9, x9, x13
	adc x10, x10, x14
	mul x11, x4, x8
	umulh x12, x4, x8
	mul x13, x5, x7
	umulh x14, x5, x7
	adds x11, x11, x13
	adc x12, x12, x14
	mul x13, x6, x17
	movz x14, #0, lsl #0
	adds x11, x11, x13
	adc x12, x12, x14
	mul x13, x6, x7
	adds x11, x11, x10
	adc x12, x12, x13
	add x4, x9, #0
	add x5, x11, #0
	movz x14, #3, lsl #0
	bic x13, x12, x14, ror #0
	and x6, x12, x14
	lsr x12, x12, #2
	add x13, x13, x12
	movz x14, #0, lsl #0
	adds x4, x4, x13
	adcs x5, x5, x14
	adc x6, x6, x14
	b 246f
245:
246:
	add x1, x22, #0
	lsr x2, x23, #4
	cbz x2, 248f
250:
	ldr x13, [x1, #0]
	ldr x14, [x1, #8]
	movz x15, #1, lsl #0
	adds x4, x4, x13
	adcs x5, x5, x14
	adc x6, x6, x15
	mul x9, x4, x7
	umulh x10, x4, x7
	mul x13, x5, x17
	umulh x14, x5, x17
	adds x9, x9, x13
	adc x10, x10, x14
	mul x11, x4, x8
	umulh x12, x4, x8
	mul x13, x5, x7
	umulh x14, x5, x7
	adds x11, x11, x13
	adc x12, x12, x14
	mul x13, x6, x17
	movz x14, #0, lsl #0
	adds x11, x11, x13
	adc x12, x12, x14
	mul x13, x6, x7
	adds x11, x11, x10
	adc x12, x12, x13
	add x4, x9, #0
	add x5, x11, #0
	movz x14, #3, lsl #0
	bic x13, x12, x14, ror #0
	and x6, x12, x14
	lsr x12, x12, #2
	add x13, x13, x12
	movz x14, #0, lsl #0
	adds x4, x4, x13
	adcs x5, x5, x14
	adc x6, x6, x14
	add x1, x1, #16
	sub x2, x2, #1
	cbnz x2, 250b
	b 249f
248:
249:
	lsl x10, x23, #60
	lsr x10, x10, #60
	cbz x10, 251f
	movz x11, #0, lsl #0
	str x11, [x21, #16]
	str x11, [x21, #24]
	add x9, x21, #16
253:
	ldrb w11, [x1, #0]
	strb w11, [x9, #0]
	add x1, x1, #1
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 253b
	add x1, x21, #16
	ldr x13, [x1, #0]
	ldr x14, [x1, #8]
	movz x15, #1, lsl #0
	adds x4, x4, x13
	adcs x5, x5, x14
	adc x6, x6, x15
	mul x9, x4, x7
	umulh x10, x4, x7
	mul x13, x5, x17
	umulh x14, x5, x17
	adds x9, x9, x13
	adc x10, x10, x14
	mul x11, x4, x8
	umulh x12, x4, x8
	mul x13, x5, x7
	umulh x14, x5, x7
	adds x11, x11, x13
	adc x12, x12, x14
	mul x13, x6, x17
	movz x14, #0, lsl #0
	adds x11, x11, x13
	adc x12, x12, x14
	mul x13, x6, x7
	adds x11, x11, x10
	adc x12, x12, x13
	add x4, x9, #0
	add x5, x11, #0
	movz x14, #3, lsl #0
	bic x13, x12, x14, ror #0
	and x6, x12, x14
	lsr x12, x12, #2
	add x13, x13, x12
	movz x14, #0, lsl #0
	adds x4, x4, x13
	adcs x5, x5, x14
	adc x6, x6, x14
	b 252f
251:
252:
	add x1, x21, #0
	ldr x13, [x1, #0]
	ldr x14, [x1, #8]
	movz x15, #1, lsl #0
	adds x4, x4, x13
	adcs x5, x5, x14
	adc x6, x6, x15
	mul x9, x4, x7
	umulh x10, x4, x7
	mul x13, x5, x17
	umulh x14, x5, x17
	adds x9, x9, x13
	adc x10, x10, x14
	mul x11, x4, x8
	umulh x12, x4, x8
	mul x13, x5, x7
	umulh x14, x5, x7
	adds x11, x11, x13
	adc x12, x12, x14
	mul x13, x6, x17
	movz x14, #0, lsl #0
	adds x11, x11, x13
	adc x12, x12, x14
	mul x13, x6, x7
	adds x11, x11, x10
	adc x12, x12, x13
	add x4, x9, #0
	add x5, x11, #0
	movz x14, #3, lsl #0
	bic x13, x12, x14, ror #0
	and x6, x12, x14
	lsr x12, x12, #2
	add x13, x13, x12
	movz x14, #0, lsl #0
	adds x4, x4, x13
	adcs x5, x5, x14
	adc x6, x6, x14
	movz x13, #5, lsl #0
	movz x14, #0, lsl #0
	adds x9, x4, x13
	adcs x10, x5, x14
	adc x11, x6, x14
	lsr x12, x11, #2
	movz x14, #0, lsl #0
	sub x12, x14, x12
	movz x14, #3, lsl #0
	and x11, x11, x14
	eor x13, x9, x4
	and x13, x13, x12
	eor x4, x4, x13
	eor x13, x10, x5
	and x13, x13, x12
	eor x5, x5, x13
	eor x13, x11, x6
	and x13, x13, x12
	eor x6, x6, x13
	str x4, [x0, #0]
	str x5, [x0, #8]
	str x6, [x0, #16]
223:
29:
21:
	ldr x2, [x21, #624]
	add x0, x21, #448
	movz x1, #0, lsl #0
	add x3, x21, #632
	bl {vg_poly1305_finalize_scratch}
	ldr x22, [x21, #584]
	ldr x23, [x21, #592]
	ldr x24, [x21, #600]
	ldr x25, [x21, #608]
	ldr x30, [x21, #616]
	ldr x6, [x21, #624]
	ldr x21, [x21, #576]
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
	add sp, sp, #1280
	ret
	.p2align 6
