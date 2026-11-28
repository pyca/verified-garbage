// The functions of `src/chacha20poly1305.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chacha20_poly1305_seal_sve2:
	sub sp, sp, #1280
	add x7, sp, #0
	sub x9, x5, #1
	sub x10, x5, #1
	orr x9, x9, x10
	orr x9, x9, x5
	lsr x9, x9, #9
	cbz x9, 20f
	movz x10, #0, lsl #0
	movz x10, #0, lsl #0
	movz x10, #0, lsl #0
	movz x10, #0, lsl #0
	sub x9, x5, #705
	lsr x9, x9, #63
	sub x10, x5, #513
	lsr x10, x10, #63
	sub x10, x10, x9
	add x10, x10, #1
	lsl x9, x5, #55
	lsr x9, x9, #55
	sub x9, x9, #257
	lsr x9, x9, #9
	cbz x9, 22f
	cbz x10, 24f
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
	cbz x10, 26f
	sub x9, x25, x10
	add x1, x24, x9
	movz x11, #0, lsl #0
	str x11, [x21, #16]
	str x11, [x21, #24]
	add x9, x21, #16
28:
	ldrb w11, [x1, #0]
	strb w11, [x9, #0]
	add x1, x1, #1
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 28b
	add x0, x21, #448
	add x1, x21, #16
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 27f
26:
27:
	str x25, [x21, #0]
	str x23, [x21, #8]
	movz w9, #1, lsl #0
	str w9, [x21, #112]
	bl {vg_chachapoly_stitched_seal_sve2}
	add x4, x1, #0
	bl {vg_chacha20_xor_sve2}
	add x0, x21, #448
	add x1, x22, #0
	lsr x2, x23, #4
	bl {vg_poly1305_blocks}
	lsl x10, x23, #60
	lsr x10, x10, #60
	cbz x10, 29f
	sub x9, x23, x10
	add x1, x22, x9
	movz x11, #0, lsl #0
	str x11, [x21, #16]
	str x11, [x21, #24]
	add x9, x21, #16
211:
	ldrb w11, [x1, #0]
	strb w11, [x9, #0]
	add x1, x1, #1
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 211b
	add x0, x21, #448
	add x1, x21, #16
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 210f
29:
210:
	add x0, x21, #448
	add x1, x21, #0
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
25:
	b 23f
22:
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
	bl {vg_chachapoly_short5_sve2}
	ldr x19, [x21, #632]
	ldr x20, [x21, #640]
	ldr x26, [x21, #648]
	add x0, x21, #448
	add x1, x21, #64
	bl {vg_poly1305_init}
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
	add x0, x21, #448
	add x1, x24, #0
	lsr x2, x25, #4
	bl {vg_poly1305_blocks}
	lsl x10, x25, #60
	lsr x10, x10, #60
	cbz x10, 237f
	sub x9, x25, x10
	add x1, x24, x9
	movz x11, #0, lsl #0
	str x11, [x21, #16]
	str x11, [x21, #24]
	add x9, x21, #16
239:
	ldrb w11, [x1, #0]
	strb w11, [x9, #0]
	add x1, x1, #1
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 239b
	add x0, x21, #448
	add x1, x21, #16
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 238f
237:
238:
	str x25, [x21, #0]
	str x23, [x21, #8]
	add x14, x23, #0
	movz x23, #256, lsl #0
	add x9, x22, #0
	add x15, x9, #0
	add x10, x21, #128
	lsr x11, x23, #4
	cbz x11, 240f
242:
	ldr q0, [x9, #0]
	ldr q1, [x10, #0]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x15, #0]
	add x9, x9, #16
	add x10, x10, #16
	add x15, x15, #16
	sub x11, x11, #1
	cbnz x11, 242b
	b 241f
240:
241:
	lsl x11, x23, #60
	lsr x11, x11, #60
	cbz x11, 243f
245:
	ldrb w12, [x9, #0]
	ldrb w13, [x10, #0]
	eor w12, w12, w13
	strb w12, [x15, #0]
	add x9, x9, #1
	add x10, x10, #1
	add x15, x15, #1
	sub x11, x11, #1
	cbnz x11, 245b
	b 244f
243:
244:
	add x23, x14, #0
	add x0, x21, #448
	add x1, x22, #0
	movz x2, #16, lsl #0
	bl {vg_poly1305_blocks}
	add x22, x22, #256
	sub x23, x23, #256
	bl {vg_chachapoly_stitched_seal_sve2}
	add x4, x1, #0
	bl {vg_chacha20_xor_sve2}
	add x0, x21, #448
	add x1, x22, #0
	lsr x2, x23, #4
	bl {vg_poly1305_blocks}
	lsl x10, x23, #60
	lsr x10, x10, #60
	cbz x10, 246f
	sub x9, x23, x10
	add x1, x22, x9
	movz x11, #0, lsl #0
	str x11, [x21, #16]
	str x11, [x21, #24]
	add x9, x21, #16
248:
	ldrb w11, [x1, #0]
	strb w11, [x9, #0]
	add x1, x1, #1
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 248b
	add x0, x21, #448
	add x1, x21, #16
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 247f
246:
247:
	add x0, x21, #448
	add x1, x21, #0
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
23:
	b 21f
20:
	add x9, x5, #191
	lsr x9, x9, #9
	cbz x9, 249f
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
	cbz x10, 251f
	sub x9, x25, x10
	add x1, x24, x9
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
	add x0, x21, #448
	add x1, x21, #16
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 252f
251:
252:
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
	bl {vg_chacha20_xor_sve2}
	add x9, x22, #0
	add x15, x9, #0
	add x10, x21, #768
	lsr x11, x23, #4
	cbz x11, 254f
256:
	ldr q0, [x9, #0]
	ldr q1, [x10, #0]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x15, #0]
	add x9, x9, #16
	add x10, x10, #16
	add x15, x15, #16
	sub x11, x11, #1
	cbnz x11, 256b
	b 255f
254:
255:
	lsl x11, x23, #60
	lsr x11, x11, #60
	cbz x11, 257f
259:
	ldrb w12, [x9, #0]
	ldrb w13, [x10, #0]
	eor w12, w12, w13
	strb w12, [x15, #0]
	add x9, x9, #1
	add x10, x10, #1
	add x15, x15, #1
	sub x11, x11, #1
	cbnz x11, 259b
	b 258f
257:
258:
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
	cbz x10, 260f
	sub x9, x23, x10
	add x1, x22, x9
	movz x11, #0, lsl #0
	str x11, [x21, #16]
	str x11, [x21, #24]
	add x9, x21, #16
262:
	ldrb w11, [x1, #0]
	strb w11, [x9, #0]
	add x1, x1, #1
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 262b
	add x0, x21, #448
	add x1, x21, #16
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 261f
260:
261:
	add x0, x21, #448
	add x1, x21, #0
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 250f
249:
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
	bl {vg_chachapoly_short5_sve2}
	ldr x19, [x21, #632]
	ldr x20, [x21, #640]
	ldr x26, [x21, #648]
	add x0, x21, #448
	add x1, x21, #64
	bl {vg_poly1305_init}
	sub x9, x23, #1
	lsr x9, x9, #8
	cbz x9, 263f
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
	cbz x11, 265f
267:
	ldr q0, [x9, #0]
	ldr q1, [x10, #0]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x15, #0]
	add x9, x9, #16
	add x10, x10, #16
	add x15, x15, #16
	sub x11, x11, #1
	cbnz x11, 267b
	b 266f
265:
266:
	lsl x11, x23, #60
	lsr x11, x11, #60
	cbz x11, 268f
270:
	ldrb w12, [x9, #0]
	ldrb w13, [x10, #0]
	eor w12, w12, w13
	strb w12, [x15, #0]
	add x9, x9, #1
	add x10, x10, #1
	add x15, x15, #1
	sub x11, x11, #1
	cbnz x11, 270b
	b 269f
268:
269:
	add x23, x14, #0
	add x0, x21, #64
	add x1, x22, #256
	sub x2, x23, #256
	add x3, x21, #128
	add x4, x1, #0
	bl {vg_chacha20_xor_sve2}
	add x0, x21, #448
	add x1, x24, #0
	lsr x2, x25, #4
	bl {vg_poly1305_blocks}
	lsl x10, x25, #60
	lsr x10, x10, #60
	cbz x10, 271f
	sub x9, x25, x10
	add x1, x24, x9
	movz x11, #0, lsl #0
	str x11, [x21, #16]
	str x11, [x21, #24]
	add x9, x21, #16
273:
	ldrb w11, [x1, #0]
	strb w11, [x9, #0]
	add x1, x1, #1
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 273b
	add x0, x21, #448
	add x1, x21, #16
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 272f
271:
272:
	str x25, [x21, #0]
	str x23, [x21, #8]
	add x0, x21, #448
	add x1, x22, #0
	lsr x2, x23, #4
	bl {vg_poly1305_blocks}
	lsl x10, x23, #60
	lsr x10, x10, #60
	cbz x10, 274f
	sub x9, x23, x10
	add x1, x22, x9
	movz x11, #0, lsl #0
	str x11, [x21, #16]
	str x11, [x21, #24]
	add x9, x21, #16
276:
	ldrb w11, [x1, #0]
	strb w11, [x9, #0]
	add x1, x1, #1
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 276b
	add x0, x21, #448
	add x1, x21, #16
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 275f
274:
275:
	add x0, x21, #448
	add x1, x21, #0
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 264f
263:
	str x25, [x21, #0]
	str x23, [x21, #8]
	add x9, x22, #0
	add x15, x9, #0
	add x10, x21, #128
	lsr x11, x23, #4
	cbz x11, 277f
279:
	ldr q0, [x9, #0]
	ldr q1, [x10, #0]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x15, #0]
	add x9, x9, #16
	add x10, x10, #16
	add x15, x15, #16
	sub x11, x11, #1
	cbnz x11, 279b
	b 278f
277:
278:
	lsl x11, x23, #60
	lsr x11, x11, #60
	cbz x11, 280f
282:
	ldrb w12, [x9, #0]
	ldrb w13, [x10, #0]
	eor w12, w12, w13
	strb w12, [x15, #0]
	add x9, x9, #1
	add x10, x10, #1
	add x15, x15, #1
	sub x11, x11, #1
	cbnz x11, 282b
	b 281f
280:
281:
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
	cbz x2, 283f
285:
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
	cbnz x2, 285b
	b 284f
283:
284:
	lsl x10, x25, #60
	lsr x10, x10, #60
	cbz x10, 286f
	movz x11, #0, lsl #0
	str x11, [x21, #16]
	str x11, [x21, #24]
	add x9, x21, #16
288:
	ldrb w11, [x1, #0]
	strb w11, [x9, #0]
	add x1, x1, #1
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 288b
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
	b 287f
286:
287:
	add x1, x22, #0
	lsr x2, x23, #4
	cbz x2, 289f
291:
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
	cbnz x2, 291b
	b 290f
289:
290:
	lsl x10, x23, #60
	lsr x10, x10, #60
	cbz x10, 292f
	movz x11, #0, lsl #0
	str x11, [x21, #16]
	str x11, [x21, #24]
	add x9, x21, #16
294:
	ldrb w11, [x1, #0]
	strb w11, [x9, #0]
	add x1, x1, #1
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 294b
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
	b 293f
292:
293:
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
264:
250:
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
	mov v15.d[1], x1
	movz x0, #0, lsl #0
	sub sp, sp, #1280
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #20, lsl #0
295:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 295b
	add sp, sp, #1280
	ret
24:
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
	ldr w9, [x21, #64]
	str w9, [x21, #640]
	ldr w9, [x21, #68]
	str w9, [x21, #644]
	ldr w9, [x21, #72]
	str w9, [x21, #648]
	ldr w9, [x21, #76]
	str w9, [x21, #652]
	ldr w9, [x21, #80]
	str w9, [x21, #656]
	ldr w9, [x21, #84]
	str w9, [x21, #660]
	ldr w9, [x21, #88]
	str w9, [x21, #664]
	ldr w9, [x21, #92]
	str w9, [x21, #668]
	ldr w9, [x21, #96]
	str w9, [x21, #672]
	ldr w9, [x21, #100]
	str w9, [x21, #676]
	ldr w9, [x21, #104]
	str w9, [x21, #680]
	ldr w9, [x21, #108]
	str w9, [x21, #684]
	ldr w9, [x21, #112]
	str w9, [x21, #688]
	ldr w9, [x21, #116]
	str w9, [x21, #692]
	ldr w9, [x21, #120]
	str w9, [x21, #696]
	ldr w9, [x21, #124]
	str w9, [x21, #700]
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
	add x0, x21, #640
	add x1, x21, #768
	movz x2, #512, lsl #0
	add x3, x21, #128
	add x4, x1, #0
	bl {vg_chacha20_xor_sve2}
	add x0, x21, #448
	add x1, x21, #768
	bl {vg_poly1305_init}
	add x0, x21, #448
	add x1, x24, #0
	lsr x2, x25, #4
	bl {vg_poly1305_blocks}
	lsl x10, x25, #60
	lsr x10, x10, #60
	cbz x10, 212f
	sub x9, x25, x10
	add x1, x24, x9
	movz x11, #0, lsl #0
	str x11, [x21, #16]
	str x11, [x21, #24]
	add x9, x21, #16
214:
	ldrb w11, [x1, #0]
	strb w11, [x9, #0]
	add x1, x1, #1
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 214b
	add x0, x21, #448
	add x1, x21, #16
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 213f
212:
213:
	str x25, [x21, #0]
	str x23, [x21, #8]
	add x14, x23, #0
	movz x23, #448, lsl #0
	add x9, x22, #0
	add x15, x9, #0
	add x10, x21, #832
	lsr x11, x23, #4
	cbz x11, 215f
217:
	ldr q0, [x9, #0]
	ldr q1, [x10, #0]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x15, #0]
	add x9, x9, #16
	add x10, x10, #16
	add x15, x15, #16
	sub x11, x11, #1
	cbnz x11, 217b
	b 216f
215:
216:
	lsl x11, x23, #60
	lsr x11, x11, #60
	cbz x11, 218f
220:
	ldrb w12, [x9, #0]
	ldrb w13, [x10, #0]
	eor w12, w12, w13
	strb w12, [x15, #0]
	add x9, x9, #1
	add x10, x10, #1
	add x15, x15, #1
	sub x11, x11, #1
	cbnz x11, 220b
	b 219f
218:
219:
	add x23, x14, #0
	movz w9, #8, lsl #0
	str w9, [x21, #112]
	add x0, x21, #64
	add x3, x21, #128
	add x2, x23, #0
	movz x23, #448, lsl #0
	add x8, x20, #0
	add x20, x22, #0
	add x7, x22, #0
	lsr x6, x23, #4
	str x27, [x21, #32]
	str x28, [x21, #40]
	movz x24, #65535, lsl #0
	movk x24, #4095, lsl #16
	movk x24, #65532, lsl #32
	movk x24, #4095, lsl #48
	ldr x25, [x21, #472]
	and x25, x25, x24
	str x25, [x21, #288]
	movz x24, #65532, lsl #0
	movk x24, #4095, lsl #16
	movk x24, #65532, lsl #32
	movk x24, #4095, lsl #48
	ldr x25, [x21, #480]
	and x25, x25, x24
	str x25, [x21, #296]
	ldr x22, [x21, #456]
	ldr x23, [x21, #464]
	ldr x21, [x21, #448]
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
	movz x4, #10, lsl #0
221:
	add v0.4s, v0.4s, v4.4s
	add v1.4s, v1.4s, v5.4s
	add v2.4s, v2.4s, v6.4s
	add v3.4s, v3.4s, v7.4s
	xar z20.s, z20.s, z0.s, #16
	xar z21.s, z21.s, z1.s, #16
	xar z22.s, z22.s, z2.s, #16
	xar z23.s, z23.s, z3.s, #16
	add v16.4s, v16.4s, v20.4s
	add v17.4s, v17.4s, v21.4s
	add v18.4s, v18.4s, v22.4s
	add v19.4s, v19.4s, v23.4s
	xar z4.s, z4.s, z16.s, #20
	xar z5.s, z5.s, z17.s, #20
	xar z6.s, z6.s, z18.s, #20
	xar z7.s, z7.s, z19.s, #20
	add v0.4s, v0.4s, v4.4s
	add v1.4s, v1.4s, v5.4s
	add v2.4s, v2.4s, v6.4s
	add v3.4s, v3.4s, v7.4s
	xar z20.s, z20.s, z0.s, #24
	xar z21.s, z21.s, z1.s, #24
	xar z22.s, z22.s, z2.s, #24
	xar z23.s, z23.s, z3.s, #24
	add v16.4s, v16.4s, v20.4s
	add v17.4s, v17.4s, v21.4s
	add v18.4s, v18.4s, v22.4s
	add v19.4s, v19.4s, v23.4s
	xar z4.s, z4.s, z16.s, #25
	xar z5.s, z5.s, z17.s, #25
	xar z6.s, z6.s, z18.s, #25
	xar z7.s, z7.s, z19.s, #25
	add v0.4s, v0.4s, v5.4s
	add v1.4s, v1.4s, v6.4s
	add v2.4s, v2.4s, v7.4s
	add v3.4s, v3.4s, v4.4s
	xar z23.s, z23.s, z0.s, #16
	xar z20.s, z20.s, z1.s, #16
	xar z21.s, z21.s, z2.s, #16
	xar z22.s, z22.s, z3.s, #16
	add v18.4s, v18.4s, v23.4s
	add v19.4s, v19.4s, v20.4s
	add v16.4s, v16.4s, v21.4s
	add v17.4s, v17.4s, v22.4s
	xar z5.s, z5.s, z18.s, #20
	xar z6.s, z6.s, z19.s, #20
	xar z7.s, z7.s, z16.s, #20
	xar z4.s, z4.s, z17.s, #20
	add v0.4s, v0.4s, v5.4s
	add v1.4s, v1.4s, v6.4s
	add v2.4s, v2.4s, v7.4s
	add v3.4s, v3.4s, v4.4s
	xar z23.s, z23.s, z0.s, #24
	xar z20.s, z20.s, z1.s, #24
	xar z21.s, z21.s, z2.s, #24
	xar z22.s, z22.s, z3.s, #24
	add v18.4s, v18.4s, v23.4s
	add v19.4s, v19.4s, v20.4s
	add v16.4s, v16.4s, v21.4s
	add v17.4s, v17.4s, v22.4s
	xar z5.s, z5.s, z18.s, #25
	xar z6.s, z6.s, z19.s, #25
	xar z7.s, z7.s, z16.s, #25
	xar z4.s, z4.s, z17.s, #25
	cbz x6, 222f
	ldr x25, [x20, #0]
	ldr x27, [x20, #8]
	movz x28, #1, lsl #0
	adds x21, x21, x25
	adcs x22, x22, x27
	adc x23, x23, x28
	ldr x24, [x0, #224]
	mul x25, x21, x24
	umulh x27, x21, x24
	mul x28, x22, x24
	umulh x30, x22, x24
	adds x27, x27, x28
	mul x28, x23, x24
	adc x28, x28, x30
	ldr x24, [x0, #232]
	mul x30, x21, x24
	umulh x21, x21, x24
	adds x27, x27, x30
	mul x30, x22, x24
	umulh x22, x22, x24
	adcs x30, x30, x21
	mul x23, x23, x24
	adc x23, x23, x22
	adds x28, x28, x30
	movz x22, #0, lsl #0
	adc x30, x23, x22
	movz x21, #3, lsl #0
	and x23, x28, x21
	sub x21, x28, x23
	extr x28, x30, x28, #2
	adds x21, x21, x25
	lsr x25, x30, #2
	adc x22, x30, x25
	adds x21, x21, x28
	adcs x22, x22, x27
	movz x25, #0, lsl #0
	adc x23, x23, x25
	add x20, x20, #16
	sub x6, x6, #1
	b 223f
222:
223:
	cbz x6, 224f
	ldr x25, [x20, #0]
	ldr x27, [x20, #8]
	movz x28, #1, lsl #0
	adds x21, x21, x25
	adcs x22, x22, x27
	adc x23, x23, x28
	ldr x24, [x0, #224]
	mul x25, x21, x24
	umulh x27, x21, x24
	mul x28, x22, x24
	umulh x30, x22, x24
	adds x27, x27, x28
	mul x28, x23, x24
	adc x28, x28, x30
	ldr x24, [x0, #232]
	mul x30, x21, x24
	umulh x21, x21, x24
	adds x27, x27, x30
	mul x30, x22, x24
	umulh x22, x22, x24
	adcs x30, x30, x21
	mul x23, x23, x24
	adc x23, x23, x22
	adds x28, x28, x30
	movz x22, #0, lsl #0
	adc x30, x23, x22
	movz x21, #3, lsl #0
	and x23, x28, x21
	sub x21, x28, x23
	extr x28, x30, x28, #2
	adds x21, x21, x25
	lsr x25, x30, #2
	adc x22, x30, x25
	adds x21, x21, x28
	adcs x22, x22, x27
	movz x25, #0, lsl #0
	adc x23, x23, x25
	add x20, x20, #16
	sub x6, x6, #1
	b 225f
224:
225:
	cbz x6, 226f
	ldr x25, [x20, #0]
	ldr x27, [x20, #8]
	movz x28, #1, lsl #0
	adds x21, x21, x25
	adcs x22, x22, x27
	adc x23, x23, x28
	ldr x24, [x0, #224]
	mul x25, x21, x24
	umulh x27, x21, x24
	mul x28, x22, x24
	umulh x30, x22, x24
	adds x27, x27, x28
	mul x28, x23, x24
	adc x28, x28, x30
	ldr x24, [x0, #232]
	mul x30, x21, x24
	umulh x21, x21, x24
	adds x27, x27, x30
	mul x30, x22, x24
	umulh x22, x22, x24
	adcs x30, x30, x21
	mul x23, x23, x24
	adc x23, x23, x22
	adds x28, x28, x30
	movz x22, #0, lsl #0
	adc x30, x23, x22
	movz x21, #3, lsl #0
	and x23, x28, x21
	sub x21, x28, x23
	extr x28, x30, x28, #2
	adds x21, x21, x25
	lsr x25, x30, #2
	adc x22, x30, x25
	adds x21, x21, x28
	adcs x22, x22, x27
	movz x25, #0, lsl #0
	adc x23, x23, x25
	add x20, x20, #16
	sub x6, x6, #1
	b 227f
226:
227:
	sub x4, x4, #1
	cbnz x4, 221b
	eor v28.16b, v28.16b, v28.16b
	str q28, [x3, #0]
	str q28, [x3, #16]
	str q28, [x3, #32]
	str q28, [x3, #48]
	str q28, [x3, #64]
	str q28, [x3, #80]
	str q28, [x3, #96]
	str q28, [x3, #112]
	str q28, [x3, #128]
	str q28, [x3, #144]
	str q28, [x3, #160]
	str q28, [x3, #176]
	str q28, [x3, #192]
	str q28, [x3, #208]
	str q28, [x3, #224]
	str q28, [x3, #240]
	add x1, x3, #0
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
	add x4, x21, #0
	add x5, x22, #0
	add x6, x23, #0
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
	sub x21, x0, #64
	str x4, [x21, #448]
	str x5, [x21, #456]
	str x6, [x21, #464]
	ldr x27, [x21, #32]
	ldr x28, [x21, #40]
	add x22, x1, #0
	add x23, x2, #0
	add x22, x20, #0
	add x23, x7, x2
	sub x23, x23, x20
	add x20, x8, #0
	add x24, x7, #0
	add x25, x2, #0
	add x9, x22, #0
	add x15, x9, #0
	add x10, x21, #128
	lsr x11, x23, #4
	cbz x11, 228f
230:
	ldr q0, [x9, #0]
	ldr q1, [x10, #0]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x15, #0]
	add x9, x9, #16
	add x10, x10, #16
	add x15, x15, #16
	sub x11, x11, #1
	cbnz x11, 230b
	b 229f
228:
229:
	lsl x11, x23, #60
	lsr x11, x11, #60
	cbz x11, 231f
233:
	ldrb w12, [x9, #0]
	ldrb w13, [x10, #0]
	eor w12, w12, w13
	strb w12, [x15, #0]
	add x9, x9, #1
	add x10, x10, #1
	add x15, x15, #1
	sub x11, x11, #1
	cbnz x11, 233b
	b 232f
231:
232:
	add x0, x21, #448
	add x1, x22, #0
	lsr x2, x23, #4
	bl {vg_poly1305_blocks}
	lsl x10, x23, #60
	lsr x10, x10, #60
	cbz x10, 234f
	sub x9, x23, x10
	add x1, x22, x9
	movz x11, #0, lsl #0
	str x11, [x21, #16]
	str x11, [x21, #24]
	add x9, x21, #16
236:
	ldrb w11, [x1, #0]
	strb w11, [x9, #0]
	add x1, x1, #1
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 236b
	add x0, x21, #448
	add x1, x21, #16
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 235f
234:
235:
	add x0, x21, #448
	add x1, x21, #0
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
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
	b 25b
	.p2align 6

vg_chacha20_poly1305_open_sve2:
	sub sp, sp, #1312
	add x7, sp, #0
	add x8, x4, #0
	mov v15.d[1], x30
	bl {vg_chacha20_poly1305_open_core_sve2}
	umov x30, v15.d[1]
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
	add sp, sp, #1312
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
	mov v15.d[1], x1
	add w0, w0, #0
	sub sp, sp, #1312
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #20, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	str q31, [x9, #0]
	str q31, [x9, #16]
	add sp, sp, #1312
	ret
	.p2align 6

vg_chacha20_poly1305_open_to_sve2:
	sub sp, sp, #1328
	add x16, sp, #0
	ldr x17, [sp, #1328]
	str x17, [x16, #0]
	add x17, sp, #16
	str x17, [x16, #8]
	add x8, x6, #0
	ldr x6, [sp, #0]
	ldr x7, [sp, #8]
	mov v15.d[1], x30
	bl {vg_chacha20_poly1305_open_core_sve2}
	umov x30, v15.d[1]
	movz x17, #0, lsl #0
	add x16, sp, #16
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
	add x16, sp, #528
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
	add sp, sp, #1328
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
	mov v15.d[1], x1
	add w0, w0, #0
	sub sp, sp, #1328
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #20, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	add sp, sp, #1328
	ret
	.p2align 6

vg_chacha20_poly1305_seal_gather_sve2:
	sub sp, sp, #16
	add x16, sp, #0
	str x30, [x16, #8]
	ldr x10, [sp, #16]
	add x8, x6, #0
	add x9, x7, #0
	add x11, x6, #0
	add x6, x4, #0
	add x7, x5, #0
	cbz x7, 20f
22:
	ldr x12, [x6, #0]
	ldr x13, [x6, #8]
	add x6, x6, #16
	lsr x14, x13, #4
	cbz x14, 23f
25:
	ldr q0, [x12, #0]
	str q0, [x11, #0]
	add x12, x12, #16
	add x11, x11, #16
	sub x14, x14, #1
	cbnz x14, 25b
	b 24f
23:
24:
	movz x15, #15, lsl #0
	and x13, x13, x15
	cbz x13, 26f
	lsr x14, x13, #3
	cbz x14, 28f
210:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 210b
	b 29f
28:
29:
	lsr x14, x13, #2
	cbz x14, 211f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 212f
211:
212:
	cbz x13, 213f
215:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 215b
	b 214f
213:
214:
	b 27f
26:
27:
	sub x7, x7, #1
	cbnz x7, 22b
	b 21f
20:
21:
	add x4, x8, #0
	add x5, x9, #0
	add x6, x10, #0
	bl {vg_chacha20_poly1305_seal_sve2}
	ldr x30, [sp, #8]
	add sp, sp, #16
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
	mov v15.d[1], x1
	movz x0, #0, lsl #0
	sub sp, sp, #1296
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #20, lsl #0
216:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 216b
	str q31, [x9, #0]
	add sp, sp, #1296
	ret
	.p2align 6

vg_chacha20_poly1305_seal_neon:
	sub sp, sp, #1280
	add x7, sp, #0
	sub x9, x5, #1
	sub x10, x5, #64
	orr x9, x9, x10
	orr x9, x9, x5
	lsr x9, x9, #9
	cbz x9, 20f
	movz x10, #0, lsl #0
	movz x10, #0, lsl #0
	movz x10, #0, lsl #0
	movz x10, #0, lsl #0
	sub x9, x5, #705
	lsr x9, x9, #63
	sub x10, x5, #513
	lsr x10, x10, #63
	sub x10, x10, x9
	add x10, x10, #1
	lsl x9, x5, #55
	lsr x9, x9, #55
	sub x9, x9, #321
	lsr x9, x9, #9
	cbz x9, 22f
	cbz x10, 24f
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
	cbz x10, 26f
	sub x9, x25, x10
	add x1, x24, x9
	movz x11, #0, lsl #0
	str x11, [x21, #16]
	str x11, [x21, #24]
	add x9, x21, #16
28:
	ldrb w11, [x1, #0]
	strb w11, [x9, #0]
	add x1, x1, #1
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 28b
	add x0, x21, #448
	add x1, x21, #16
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 27f
26:
27:
	str x25, [x21, #0]
	str x23, [x21, #8]
	movz w9, #1, lsl #0
	str w9, [x21, #112]
	bl {vg_chachapoly_stitched_seal}
	add x4, x1, #0
	bl {vg_chacha20_xor_neon}
	add x0, x21, #448
	add x1, x22, #0
	lsr x2, x23, #4
	bl {vg_poly1305_blocks}
	lsl x10, x23, #60
	lsr x10, x10, #60
	cbz x10, 29f
	sub x9, x23, x10
	add x1, x22, x9
	movz x11, #0, lsl #0
	str x11, [x21, #16]
	str x11, [x21, #24]
	add x9, x21, #16
211:
	ldrb w11, [x1, #0]
	strb w11, [x9, #0]
	add x1, x1, #1
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 211b
	add x0, x21, #448
	add x1, x21, #16
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 210f
29:
210:
	add x0, x21, #448
	add x1, x21, #0
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
25:
	b 23f
22:
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
	bl {vg_chachapoly_short5}
	ldr x19, [x21, #632]
	ldr x20, [x21, #640]
	ldr x26, [x21, #648]
	add x0, x21, #448
	add x1, x21, #64
	bl {vg_poly1305_init}
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
	add x0, x21, #448
	add x1, x24, #0
	lsr x2, x25, #4
	bl {vg_poly1305_blocks}
	lsl x10, x25, #60
	lsr x10, x10, #60
	cbz x10, 237f
	sub x9, x25, x10
	add x1, x24, x9
	movz x11, #0, lsl #0
	str x11, [x21, #16]
	str x11, [x21, #24]
	add x9, x21, #16
239:
	ldrb w11, [x1, #0]
	strb w11, [x9, #0]
	add x1, x1, #1
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 239b
	add x0, x21, #448
	add x1, x21, #16
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 238f
237:
238:
	str x25, [x21, #0]
	str x23, [x21, #8]
	add x14, x23, #0
	movz x23, #256, lsl #0
	add x9, x22, #0
	add x15, x9, #0
	add x10, x21, #128
	lsr x11, x23, #4
	cbz x11, 240f
242:
	ldr q0, [x9, #0]
	ldr q1, [x10, #0]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x15, #0]
	add x9, x9, #16
	add x10, x10, #16
	add x15, x15, #16
	sub x11, x11, #1
	cbnz x11, 242b
	b 241f
240:
241:
	lsl x11, x23, #60
	lsr x11, x11, #60
	cbz x11, 243f
245:
	ldrb w12, [x9, #0]
	ldrb w13, [x10, #0]
	eor w12, w12, w13
	strb w12, [x15, #0]
	add x9, x9, #1
	add x10, x10, #1
	add x15, x15, #1
	sub x11, x11, #1
	cbnz x11, 245b
	b 244f
243:
244:
	add x23, x14, #0
	add x0, x21, #448
	add x1, x22, #0
	movz x2, #16, lsl #0
	bl {vg_poly1305_blocks}
	add x22, x22, #256
	sub x23, x23, #256
	bl {vg_chachapoly_stitched_seal}
	add x4, x1, #0
	bl {vg_chacha20_xor_neon}
	add x0, x21, #448
	add x1, x22, #0
	lsr x2, x23, #4
	bl {vg_poly1305_blocks}
	lsl x10, x23, #60
	lsr x10, x10, #60
	cbz x10, 246f
	sub x9, x23, x10
	add x1, x22, x9
	movz x11, #0, lsl #0
	str x11, [x21, #16]
	str x11, [x21, #24]
	add x9, x21, #16
248:
	ldrb w11, [x1, #0]
	strb w11, [x9, #0]
	add x1, x1, #1
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 248b
	add x0, x21, #448
	add x1, x21, #16
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 247f
246:
247:
	add x0, x21, #448
	add x1, x21, #0
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
23:
	b 21f
20:
	add x9, x5, #63
	lsr x9, x9, #9
	cbz x9, 249f
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
	cbz x10, 251f
	sub x9, x25, x10
	add x1, x24, x9
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
	add x0, x21, #448
	add x1, x21, #16
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 252f
251:
252:
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
	bl {vg_chacha20_xor_neon}
	add x9, x22, #0
	add x15, x9, #0
	add x10, x21, #768
	lsr x11, x23, #4
	cbz x11, 254f
256:
	ldr q0, [x9, #0]
	ldr q1, [x10, #0]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x15, #0]
	add x9, x9, #16
	add x10, x10, #16
	add x15, x15, #16
	sub x11, x11, #1
	cbnz x11, 256b
	b 255f
254:
255:
	lsl x11, x23, #60
	lsr x11, x11, #60
	cbz x11, 257f
259:
	ldrb w12, [x9, #0]
	ldrb w13, [x10, #0]
	eor w12, w12, w13
	strb w12, [x15, #0]
	add x9, x9, #1
	add x10, x10, #1
	add x15, x15, #1
	sub x11, x11, #1
	cbnz x11, 259b
	b 258f
257:
258:
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
	cbz x10, 260f
	sub x9, x23, x10
	add x1, x22, x9
	movz x11, #0, lsl #0
	str x11, [x21, #16]
	str x11, [x21, #24]
	add x9, x21, #16
262:
	ldrb w11, [x1, #0]
	strb w11, [x9, #0]
	add x1, x1, #1
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 262b
	add x0, x21, #448
	add x1, x21, #16
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 261f
260:
261:
	add x0, x21, #448
	add x1, x21, #0
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 250f
249:
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
	bl {vg_chachapoly_short5}
	ldr x19, [x21, #632]
	ldr x20, [x21, #640]
	ldr x26, [x21, #648]
	add x0, x21, #448
	add x1, x21, #64
	bl {vg_poly1305_init}
	sub x9, x23, #1
	lsr x9, x9, #8
	cbz x9, 263f
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
	cbz x11, 265f
267:
	ldr q0, [x9, #0]
	ldr q1, [x10, #0]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x15, #0]
	add x9, x9, #16
	add x10, x10, #16
	add x15, x15, #16
	sub x11, x11, #1
	cbnz x11, 267b
	b 266f
265:
266:
	lsl x11, x23, #60
	lsr x11, x11, #60
	cbz x11, 268f
270:
	ldrb w12, [x9, #0]
	ldrb w13, [x10, #0]
	eor w12, w12, w13
	strb w12, [x15, #0]
	add x9, x9, #1
	add x10, x10, #1
	add x15, x15, #1
	sub x11, x11, #1
	cbnz x11, 270b
	b 269f
268:
269:
	add x23, x14, #0
	add x0, x21, #64
	add x1, x22, #256
	sub x2, x23, #256
	add x3, x21, #128
	add x4, x1, #0
	bl {vg_chacha20_xor_neon}
	add x0, x21, #448
	add x1, x24, #0
	lsr x2, x25, #4
	bl {vg_poly1305_blocks}
	lsl x10, x25, #60
	lsr x10, x10, #60
	cbz x10, 271f
	sub x9, x25, x10
	add x1, x24, x9
	movz x11, #0, lsl #0
	str x11, [x21, #16]
	str x11, [x21, #24]
	add x9, x21, #16
273:
	ldrb w11, [x1, #0]
	strb w11, [x9, #0]
	add x1, x1, #1
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 273b
	add x0, x21, #448
	add x1, x21, #16
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 272f
271:
272:
	str x25, [x21, #0]
	str x23, [x21, #8]
	add x0, x21, #448
	add x1, x22, #0
	lsr x2, x23, #4
	bl {vg_poly1305_blocks}
	lsl x10, x23, #60
	lsr x10, x10, #60
	cbz x10, 274f
	sub x9, x23, x10
	add x1, x22, x9
	movz x11, #0, lsl #0
	str x11, [x21, #16]
	str x11, [x21, #24]
	add x9, x21, #16
276:
	ldrb w11, [x1, #0]
	strb w11, [x9, #0]
	add x1, x1, #1
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 276b
	add x0, x21, #448
	add x1, x21, #16
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 275f
274:
275:
	add x0, x21, #448
	add x1, x21, #0
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 264f
263:
	str x25, [x21, #0]
	str x23, [x21, #8]
	add x9, x22, #0
	add x15, x9, #0
	add x10, x21, #128
	lsr x11, x23, #4
	cbz x11, 277f
279:
	ldr q0, [x9, #0]
	ldr q1, [x10, #0]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x15, #0]
	add x9, x9, #16
	add x10, x10, #16
	add x15, x15, #16
	sub x11, x11, #1
	cbnz x11, 279b
	b 278f
277:
278:
	lsl x11, x23, #60
	lsr x11, x11, #60
	cbz x11, 280f
282:
	ldrb w12, [x9, #0]
	ldrb w13, [x10, #0]
	eor w12, w12, w13
	strb w12, [x15, #0]
	add x9, x9, #1
	add x10, x10, #1
	add x15, x15, #1
	sub x11, x11, #1
	cbnz x11, 282b
	b 281f
280:
281:
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
	cbz x2, 283f
285:
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
	cbnz x2, 285b
	b 284f
283:
284:
	lsl x10, x25, #60
	lsr x10, x10, #60
	cbz x10, 286f
	movz x11, #0, lsl #0
	str x11, [x21, #16]
	str x11, [x21, #24]
	add x9, x21, #16
288:
	ldrb w11, [x1, #0]
	strb w11, [x9, #0]
	add x1, x1, #1
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 288b
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
	b 287f
286:
287:
	add x1, x22, #0
	lsr x2, x23, #4
	cbz x2, 289f
291:
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
	cbnz x2, 291b
	b 290f
289:
290:
	lsl x10, x23, #60
	lsr x10, x10, #60
	cbz x10, 292f
	movz x11, #0, lsl #0
	str x11, [x21, #16]
	str x11, [x21, #24]
	add x9, x21, #16
294:
	ldrb w11, [x1, #0]
	strb w11, [x9, #0]
	add x1, x1, #1
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 294b
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
	b 293f
292:
293:
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
264:
250:
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
	mov v15.d[1], x1
	movz x0, #0, lsl #0
	sub sp, sp, #1280
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #20, lsl #0
295:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 295b
	add sp, sp, #1280
	ret
24:
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
	ldr w9, [x21, #64]
	str w9, [x21, #640]
	ldr w9, [x21, #68]
	str w9, [x21, #644]
	ldr w9, [x21, #72]
	str w9, [x21, #648]
	ldr w9, [x21, #76]
	str w9, [x21, #652]
	ldr w9, [x21, #80]
	str w9, [x21, #656]
	ldr w9, [x21, #84]
	str w9, [x21, #660]
	ldr w9, [x21, #88]
	str w9, [x21, #664]
	ldr w9, [x21, #92]
	str w9, [x21, #668]
	ldr w9, [x21, #96]
	str w9, [x21, #672]
	ldr w9, [x21, #100]
	str w9, [x21, #676]
	ldr w9, [x21, #104]
	str w9, [x21, #680]
	ldr w9, [x21, #108]
	str w9, [x21, #684]
	ldr w9, [x21, #112]
	str w9, [x21, #688]
	ldr w9, [x21, #116]
	str w9, [x21, #692]
	ldr w9, [x21, #120]
	str w9, [x21, #696]
	ldr w9, [x21, #124]
	str w9, [x21, #700]
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
	add x0, x21, #640
	add x1, x21, #768
	movz x2, #512, lsl #0
	add x3, x21, #128
	add x4, x1, #0
	bl {vg_chacha20_xor_neon}
	add x0, x21, #448
	add x1, x21, #768
	bl {vg_poly1305_init}
	add x0, x21, #448
	add x1, x24, #0
	lsr x2, x25, #4
	bl {vg_poly1305_blocks}
	lsl x10, x25, #60
	lsr x10, x10, #60
	cbz x10, 212f
	sub x9, x25, x10
	add x1, x24, x9
	movz x11, #0, lsl #0
	str x11, [x21, #16]
	str x11, [x21, #24]
	add x9, x21, #16
214:
	ldrb w11, [x1, #0]
	strb w11, [x9, #0]
	add x1, x1, #1
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 214b
	add x0, x21, #448
	add x1, x21, #16
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 213f
212:
213:
	str x25, [x21, #0]
	str x23, [x21, #8]
	add x14, x23, #0
	movz x23, #448, lsl #0
	add x9, x22, #0
	add x15, x9, #0
	add x10, x21, #832
	lsr x11, x23, #4
	cbz x11, 215f
217:
	ldr q0, [x9, #0]
	ldr q1, [x10, #0]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x15, #0]
	add x9, x9, #16
	add x10, x10, #16
	add x15, x15, #16
	sub x11, x11, #1
	cbnz x11, 217b
	b 216f
215:
216:
	lsl x11, x23, #60
	lsr x11, x11, #60
	cbz x11, 218f
220:
	ldrb w12, [x9, #0]
	ldrb w13, [x10, #0]
	eor w12, w12, w13
	strb w12, [x15, #0]
	add x9, x9, #1
	add x10, x10, #1
	add x15, x15, #1
	sub x11, x11, #1
	cbnz x11, 220b
	b 219f
218:
219:
	add x23, x14, #0
	movz w9, #8, lsl #0
	str w9, [x21, #112]
	add x0, x21, #64
	add x3, x21, #128
	add x2, x23, #0
	movz x23, #448, lsl #0
	add x8, x20, #0
	add x20, x22, #0
	add x7, x22, #0
	lsr x6, x23, #4
	str x27, [x21, #32]
	str x28, [x21, #40]
	movz x24, #65535, lsl #0
	movk x24, #4095, lsl #16
	movk x24, #65532, lsl #32
	movk x24, #4095, lsl #48
	ldr x25, [x21, #472]
	and x25, x25, x24
	str x25, [x21, #288]
	movz x24, #65532, lsl #0
	movk x24, #4095, lsl #16
	movk x24, #65532, lsl #32
	movk x24, #4095, lsl #48
	ldr x25, [x21, #480]
	and x25, x25, x24
	str x25, [x21, #296]
	ldr x22, [x21, #456]
	ldr x23, [x21, #464]
	ldr x21, [x21, #448]
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
	movz x4, #10, lsl #0
221:
	add v0.4s, v0.4s, v4.4s
	add v1.4s, v1.4s, v5.4s
	add v2.4s, v2.4s, v6.4s
	add v3.4s, v3.4s, v7.4s
	eor v31.16b, v20.16b, v0.16b
	rev32 v20.8h, v31.8h
	eor v31.16b, v21.16b, v1.16b
	rev32 v21.8h, v31.8h
	eor v31.16b, v22.16b, v2.16b
	rev32 v22.8h, v31.8h
	eor v31.16b, v23.16b, v3.16b
	rev32 v23.8h, v31.8h
	add v16.4s, v16.4s, v20.4s
	add v17.4s, v17.4s, v21.4s
	add v18.4s, v18.4s, v22.4s
	add v19.4s, v19.4s, v23.4s
	eor v31.16b, v4.16b, v16.16b
	ushr v4.4s, v31.4s, #20
	sli v4.4s, v31.4s, #12
	eor v31.16b, v5.16b, v17.16b
	ushr v5.4s, v31.4s, #20
	sli v5.4s, v31.4s, #12
	eor v31.16b, v6.16b, v18.16b
	ushr v6.4s, v31.4s, #20
	sli v6.4s, v31.4s, #12
	eor v31.16b, v7.16b, v19.16b
	ushr v7.4s, v31.4s, #20
	sli v7.4s, v31.4s, #12
	add v0.4s, v0.4s, v4.4s
	add v1.4s, v1.4s, v5.4s
	add v2.4s, v2.4s, v6.4s
	add v3.4s, v3.4s, v7.4s
	eor v31.16b, v20.16b, v0.16b
	tbl v20.16b, {v31.16b}, v30.16b
	eor v31.16b, v21.16b, v1.16b
	tbl v21.16b, {v31.16b}, v30.16b
	eor v31.16b, v22.16b, v2.16b
	tbl v22.16b, {v31.16b}, v30.16b
	eor v31.16b, v23.16b, v3.16b
	tbl v23.16b, {v31.16b}, v30.16b
	add v16.4s, v16.4s, v20.4s
	add v17.4s, v17.4s, v21.4s
	add v18.4s, v18.4s, v22.4s
	add v19.4s, v19.4s, v23.4s
	eor v31.16b, v4.16b, v16.16b
	ushr v4.4s, v31.4s, #25
	sli v4.4s, v31.4s, #7
	eor v31.16b, v5.16b, v17.16b
	ushr v5.4s, v31.4s, #25
	sli v5.4s, v31.4s, #7
	eor v31.16b, v6.16b, v18.16b
	ushr v6.4s, v31.4s, #25
	sli v6.4s, v31.4s, #7
	eor v31.16b, v7.16b, v19.16b
	ushr v7.4s, v31.4s, #25
	sli v7.4s, v31.4s, #7
	add v0.4s, v0.4s, v5.4s
	add v1.4s, v1.4s, v6.4s
	add v2.4s, v2.4s, v7.4s
	add v3.4s, v3.4s, v4.4s
	eor v31.16b, v23.16b, v0.16b
	rev32 v23.8h, v31.8h
	eor v31.16b, v20.16b, v1.16b
	rev32 v20.8h, v31.8h
	eor v31.16b, v21.16b, v2.16b
	rev32 v21.8h, v31.8h
	eor v31.16b, v22.16b, v3.16b
	rev32 v22.8h, v31.8h
	add v18.4s, v18.4s, v23.4s
	add v19.4s, v19.4s, v20.4s
	add v16.4s, v16.4s, v21.4s
	add v17.4s, v17.4s, v22.4s
	eor v31.16b, v5.16b, v18.16b
	ushr v5.4s, v31.4s, #20
	sli v5.4s, v31.4s, #12
	eor v31.16b, v6.16b, v19.16b
	ushr v6.4s, v31.4s, #20
	sli v6.4s, v31.4s, #12
	eor v31.16b, v7.16b, v16.16b
	ushr v7.4s, v31.4s, #20
	sli v7.4s, v31.4s, #12
	eor v31.16b, v4.16b, v17.16b
	ushr v4.4s, v31.4s, #20
	sli v4.4s, v31.4s, #12
	add v0.4s, v0.4s, v5.4s
	add v1.4s, v1.4s, v6.4s
	add v2.4s, v2.4s, v7.4s
	add v3.4s, v3.4s, v4.4s
	eor v31.16b, v23.16b, v0.16b
	tbl v23.16b, {v31.16b}, v30.16b
	eor v31.16b, v20.16b, v1.16b
	tbl v20.16b, {v31.16b}, v30.16b
	eor v31.16b, v21.16b, v2.16b
	tbl v21.16b, {v31.16b}, v30.16b
	eor v31.16b, v22.16b, v3.16b
	tbl v22.16b, {v31.16b}, v30.16b
	add v18.4s, v18.4s, v23.4s
	add v19.4s, v19.4s, v20.4s
	add v16.4s, v16.4s, v21.4s
	add v17.4s, v17.4s, v22.4s
	eor v31.16b, v5.16b, v18.16b
	ushr v5.4s, v31.4s, #25
	sli v5.4s, v31.4s, #7
	eor v31.16b, v6.16b, v19.16b
	ushr v6.4s, v31.4s, #25
	sli v6.4s, v31.4s, #7
	eor v31.16b, v7.16b, v16.16b
	ushr v7.4s, v31.4s, #25
	sli v7.4s, v31.4s, #7
	eor v31.16b, v4.16b, v17.16b
	ushr v4.4s, v31.4s, #25
	sli v4.4s, v31.4s, #7
	cbz x6, 222f
	ldr x25, [x20, #0]
	ldr x27, [x20, #8]
	movz x28, #1, lsl #0
	adds x21, x21, x25
	adcs x22, x22, x27
	adc x23, x23, x28
	ldr x24, [x0, #224]
	mul x25, x21, x24
	umulh x27, x21, x24
	mul x28, x22, x24
	umulh x30, x22, x24
	adds x27, x27, x28
	mul x28, x23, x24
	adc x28, x28, x30
	ldr x24, [x0, #232]
	mul x30, x21, x24
	umulh x21, x21, x24
	adds x27, x27, x30
	mul x30, x22, x24
	umulh x22, x22, x24
	adcs x30, x30, x21
	mul x23, x23, x24
	adc x23, x23, x22
	adds x28, x28, x30
	movz x22, #0, lsl #0
	adc x30, x23, x22
	movz x21, #3, lsl #0
	and x23, x28, x21
	sub x21, x28, x23
	extr x28, x30, x28, #2
	adds x21, x21, x25
	lsr x25, x30, #2
	adc x22, x30, x25
	adds x21, x21, x28
	adcs x22, x22, x27
	movz x25, #0, lsl #0
	adc x23, x23, x25
	add x20, x20, #16
	sub x6, x6, #1
	b 223f
222:
223:
	cbz x6, 224f
	ldr x25, [x20, #0]
	ldr x27, [x20, #8]
	movz x28, #1, lsl #0
	adds x21, x21, x25
	adcs x22, x22, x27
	adc x23, x23, x28
	ldr x24, [x0, #224]
	mul x25, x21, x24
	umulh x27, x21, x24
	mul x28, x22, x24
	umulh x30, x22, x24
	adds x27, x27, x28
	mul x28, x23, x24
	adc x28, x28, x30
	ldr x24, [x0, #232]
	mul x30, x21, x24
	umulh x21, x21, x24
	adds x27, x27, x30
	mul x30, x22, x24
	umulh x22, x22, x24
	adcs x30, x30, x21
	mul x23, x23, x24
	adc x23, x23, x22
	adds x28, x28, x30
	movz x22, #0, lsl #0
	adc x30, x23, x22
	movz x21, #3, lsl #0
	and x23, x28, x21
	sub x21, x28, x23
	extr x28, x30, x28, #2
	adds x21, x21, x25
	lsr x25, x30, #2
	adc x22, x30, x25
	adds x21, x21, x28
	adcs x22, x22, x27
	movz x25, #0, lsl #0
	adc x23, x23, x25
	add x20, x20, #16
	sub x6, x6, #1
	b 225f
224:
225:
	cbz x6, 226f
	ldr x25, [x20, #0]
	ldr x27, [x20, #8]
	movz x28, #1, lsl #0
	adds x21, x21, x25
	adcs x22, x22, x27
	adc x23, x23, x28
	ldr x24, [x0, #224]
	mul x25, x21, x24
	umulh x27, x21, x24
	mul x28, x22, x24
	umulh x30, x22, x24
	adds x27, x27, x28
	mul x28, x23, x24
	adc x28, x28, x30
	ldr x24, [x0, #232]
	mul x30, x21, x24
	umulh x21, x21, x24
	adds x27, x27, x30
	mul x30, x22, x24
	umulh x22, x22, x24
	adcs x30, x30, x21
	mul x23, x23, x24
	adc x23, x23, x22
	adds x28, x28, x30
	movz x22, #0, lsl #0
	adc x30, x23, x22
	movz x21, #3, lsl #0
	and x23, x28, x21
	sub x21, x28, x23
	extr x28, x30, x28, #2
	adds x21, x21, x25
	lsr x25, x30, #2
	adc x22, x30, x25
	adds x21, x21, x28
	adcs x22, x22, x27
	movz x25, #0, lsl #0
	adc x23, x23, x25
	add x20, x20, #16
	sub x6, x6, #1
	b 227f
226:
227:
	sub x4, x4, #1
	cbnz x4, 221b
	eor v28.16b, v28.16b, v28.16b
	str q28, [x3, #0]
	str q28, [x3, #16]
	str q28, [x3, #32]
	str q28, [x3, #48]
	str q28, [x3, #64]
	str q28, [x3, #80]
	str q28, [x3, #96]
	str q28, [x3, #112]
	str q28, [x3, #128]
	str q28, [x3, #144]
	str q28, [x3, #160]
	str q28, [x3, #176]
	str q28, [x3, #192]
	str q28, [x3, #208]
	str q28, [x3, #224]
	str q28, [x3, #240]
	add x1, x3, #0
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
	add x4, x21, #0
	add x5, x22, #0
	add x6, x23, #0
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
	sub x21, x0, #64
	str x4, [x21, #448]
	str x5, [x21, #456]
	str x6, [x21, #464]
	ldr x27, [x21, #32]
	ldr x28, [x21, #40]
	add x22, x1, #0
	add x23, x2, #0
	add x22, x20, #0
	add x23, x7, x2
	sub x23, x23, x20
	add x20, x8, #0
	add x24, x7, #0
	add x25, x2, #0
	add x9, x22, #0
	add x15, x9, #0
	add x10, x21, #128
	lsr x11, x23, #4
	cbz x11, 228f
230:
	ldr q0, [x9, #0]
	ldr q1, [x10, #0]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x15, #0]
	add x9, x9, #16
	add x10, x10, #16
	add x15, x15, #16
	sub x11, x11, #1
	cbnz x11, 230b
	b 229f
228:
229:
	lsl x11, x23, #60
	lsr x11, x11, #60
	cbz x11, 231f
233:
	ldrb w12, [x9, #0]
	ldrb w13, [x10, #0]
	eor w12, w12, w13
	strb w12, [x15, #0]
	add x9, x9, #1
	add x10, x10, #1
	add x15, x15, #1
	sub x11, x11, #1
	cbnz x11, 233b
	b 232f
231:
232:
	add x0, x21, #448
	add x1, x22, #0
	lsr x2, x23, #4
	bl {vg_poly1305_blocks}
	lsl x10, x23, #60
	lsr x10, x10, #60
	cbz x10, 234f
	sub x9, x23, x10
	add x1, x22, x9
	movz x11, #0, lsl #0
	str x11, [x21, #16]
	str x11, [x21, #24]
	add x9, x21, #16
236:
	ldrb w11, [x1, #0]
	strb w11, [x9, #0]
	add x1, x1, #1
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 236b
	add x0, x21, #448
	add x1, x21, #16
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 235f
234:
235:
	add x0, x21, #448
	add x1, x21, #0
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
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
	b 25b
	.p2align 6

vg_chacha20_poly1305_open_neon:
	sub sp, sp, #1312
	add x7, sp, #0
	add x8, x4, #0
	mov v15.d[1], x30
	bl {vg_chacha20_poly1305_open_core_neon}
	umov x30, v15.d[1]
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
	add sp, sp, #1312
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
	mov v15.d[1], x1
	add w0, w0, #0
	sub sp, sp, #1312
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #20, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	str q31, [x9, #0]
	str q31, [x9, #16]
	add sp, sp, #1312
	ret
	.p2align 6

vg_chacha20_poly1305_open_to_neon:
	sub sp, sp, #1328
	add x16, sp, #0
	ldr x17, [sp, #1328]
	str x17, [x16, #0]
	add x17, sp, #16
	str x17, [x16, #8]
	add x8, x6, #0
	ldr x6, [sp, #0]
	ldr x7, [sp, #8]
	mov v15.d[1], x30
	bl {vg_chacha20_poly1305_open_core_neon}
	umov x30, v15.d[1]
	movz x17, #0, lsl #0
	add x16, sp, #16
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
	add x16, sp, #528
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
	add sp, sp, #1328
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
	mov v15.d[1], x1
	add w0, w0, #0
	sub sp, sp, #1328
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #20, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	add sp, sp, #1328
	ret
	.p2align 6

vg_chacha20_poly1305_seal_gather_neon:
	sub sp, sp, #16
	add x16, sp, #0
	str x30, [x16, #8]
	ldr x10, [sp, #16]
	add x8, x6, #0
	add x9, x7, #0
	add x11, x6, #0
	add x6, x4, #0
	add x7, x5, #0
	cbz x7, 20f
22:
	ldr x12, [x6, #0]
	ldr x13, [x6, #8]
	add x6, x6, #16
	lsr x14, x13, #4
	cbz x14, 23f
25:
	ldr q0, [x12, #0]
	str q0, [x11, #0]
	add x12, x12, #16
	add x11, x11, #16
	sub x14, x14, #1
	cbnz x14, 25b
	b 24f
23:
24:
	movz x15, #15, lsl #0
	and x13, x13, x15
	cbz x13, 26f
	lsr x14, x13, #3
	cbz x14, 28f
210:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 210b
	b 29f
28:
29:
	lsr x14, x13, #2
	cbz x14, 211f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 212f
211:
212:
	cbz x13, 213f
215:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 215b
	b 214f
213:
214:
	b 27f
26:
27:
	sub x7, x7, #1
	cbnz x7, 22b
	b 21f
20:
21:
	add x4, x8, #0
	add x5, x9, #0
	add x6, x10, #0
	bl {vg_chacha20_poly1305_seal_neon}
	ldr x30, [sp, #8]
	add sp, sp, #16
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
	mov v15.d[1], x1
	movz x0, #0, lsl #0
	sub sp, sp, #1296
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #20, lsl #0
216:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 216b
	str q31, [x9, #0]
	add sp, sp, #1296
	ret
	.p2align 6

vg_chacha20_poly1305_seal:
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
	bl {vg_chachapoly_short5}
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
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	movz x0, #0, lsl #0
	sub sp, sp, #1280
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #20, lsl #0
254:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 254b
	add sp, sp, #1280
	ret
	.p2align 6

vg_chacha20_poly1305_open:
	sub sp, sp, #1312
	add x7, sp, #0
	add x8, x4, #0
	mov v15.d[1], x30
	bl {vg_chacha20_poly1305_open_core}
	umov x30, v15.d[1]
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
	add sp, sp, #1312
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
	mov v15.d[1], x1
	add w0, w0, #0
	sub sp, sp, #1312
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #20, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	str q31, [x9, #0]
	str q31, [x9, #16]
	add sp, sp, #1312
	ret
	.p2align 6

vg_chacha20_poly1305_open_to:
	sub sp, sp, #1328
	add x16, sp, #0
	ldr x17, [sp, #1328]
	str x17, [x16, #0]
	add x17, sp, #16
	str x17, [x16, #8]
	add x8, x6, #0
	ldr x6, [sp, #0]
	ldr x7, [sp, #8]
	mov v15.d[1], x30
	bl {vg_chacha20_poly1305_open_core}
	umov x30, v15.d[1]
	movz x17, #0, lsl #0
	add x16, sp, #16
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
	add x16, sp, #528
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
	add sp, sp, #1328
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
	mov v15.d[1], x1
	add w0, w0, #0
	sub sp, sp, #1328
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #20, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	add sp, sp, #1328
	ret
	.p2align 6

vg_chacha20_poly1305_seal_gather:
	sub sp, sp, #16
	add x16, sp, #0
	str x30, [x16, #8]
	ldr x10, [sp, #16]
	add x8, x6, #0
	add x9, x7, #0
	add x11, x6, #0
	add x6, x4, #0
	add x7, x5, #0
	cbz x7, 20f
22:
	ldr x12, [x6, #0]
	ldr x13, [x6, #8]
	add x6, x6, #16
	lsr x14, x13, #4
	cbz x14, 23f
25:
	ldr q0, [x12, #0]
	str q0, [x11, #0]
	add x12, x12, #16
	add x11, x11, #16
	sub x14, x14, #1
	cbnz x14, 25b
	b 24f
23:
24:
	movz x15, #15, lsl #0
	and x13, x13, x15
	cbz x13, 26f
	lsr x14, x13, #3
	cbz x14, 28f
210:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 210b
	b 29f
28:
29:
	lsr x14, x13, #2
	cbz x14, 211f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 212f
211:
212:
	cbz x13, 213f
215:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 215b
	b 214f
213:
214:
	b 27f
26:
27:
	sub x7, x7, #1
	cbnz x7, 22b
	b 21f
20:
21:
	add x4, x8, #0
	add x5, x9, #0
	add x6, x10, #0
	bl {vg_chacha20_poly1305_seal}
	ldr x30, [sp, #8]
	add sp, sp, #16
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
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	movz x0, #0, lsl #0
	sub sp, sp, #1296
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #20, lsl #0
216:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 216b
	str q31, [x9, #0]
	add sp, sp, #1296
	ret
	.p2align 6
