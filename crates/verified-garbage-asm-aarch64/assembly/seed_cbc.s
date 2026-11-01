// The functions of `src/seed_cbc.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_seed_cbc_encrypt_chained:
	sub sp, sp, #1456
	add x4, sp, #0
	add x5, x4, #0
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
	add x25, x1, #0
	cbz x3, 20f
	ldr x6, [x2, #0]
	ldr x7, [x1, #0]
	eor x6, x6, x7
	str x6, [x2, #0]
	ldr x6, [x2, #8]
	ldr x7, [x1, #8]
	eor x6, x6, x7
	str x6, [x2, #8]
	b 21f
20:
21:
	add x23, x2, #0
	add x24, x3, #0
	dup v31.2d, x25
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
	umov x25, v31.d[0]
	cbz x24, 22f
24:
	ldr x6, [x23, #0]
	str x6, [x5, #976]
	ldr x6, [x23, #8]
	str x6, [x5, #984]
	dup v31.2d, x25
	dup v28.2d, x30
	dup v27.2d, x5
	dup v29.2d, x23
	dup v30.2d, x24
	add x0, x5, #1232
	add x1, x5, #976
	movz x2, #16, lsl #0
	add x3, x5, #0
	bl {vg_seed_encrypt_blocks}
	umov x5, v27.d[0]
	umov x30, v28.d[0]
	umov x23, v29.d[0]
	umov x24, v30.d[0]
	umov x25, v31.d[0]
	ldr x6, [x5, #976]
	str x6, [x23, #0]
	ldr x6, [x5, #984]
	str x6, [x23, #8]
	sub x24, x24, #1
	cbz x24, 25f
	ldr x6, [x23, #16]
	ldr x7, [x5, #976]
	eor x6, x6, x7
	str x6, [x23, #16]
	ldr x6, [x23, #24]
	ldr x7, [x5, #984]
	eor x6, x6, x7
	str x6, [x23, #24]
	b 26f
25:
26:
	add x23, x23, #16
	cbnz x24, 24b
	ldr x6, [x5, #976]
	str x6, [x25, #0]
	ldr x6, [x5, #984]
	str x6, [x25, #8]
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
	ret
	.p2align 6

vg_seed_cbc_decrypt_chained:
	sub sp, sp, #1456
	add x4, sp, #0
	add x5, x4, #0
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
	ldr x6, [x1, #0]
	str x6, [x5, #1440]
	ldr x6, [x1, #8]
	str x6, [x5, #1448]
	cbz x3, 20f
	sub x7, x3, #1
	lsl x7, x7, #4
	add x7, x7, x2
	ldr x6, [x7, #0]
	str x6, [x1, #0]
	ldr x6, [x7, #8]
	str x6, [x1, #8]
	b 21f
20:
21:
	add x23, x2, #0
	add x24, x3, #0
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
	lsr x13, x24, #4
	cbnz x13, 25f
	add x16, x24, #0
	b 26f
25:
	movz x16, #16, lsl #0
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
	dup v28.2d, x30
	dup v27.2d, x5
	dup v29.2d, x23
	dup v30.2d, x24
	add x0, x5, #1232
	add x1, x5, #976
	movz x2, #16, lsl #0
	add x3, x5, #0
	bl {vg_seed_decrypt_blocks}
	umov x5, v27.d[0]
	umov x30, v28.d[0]
	umov x23, v29.d[0]
	umov x24, v30.d[0]
	lsr x13, x24, #4
	cbnz x13, 28f
	add x16, x24, #0
	b 29f
28:
	movz x16, #16, lsl #0
29:
	add x14, x5, #0
	add x14, x14, #976
	add x15, x23, #0
	add x17, x16, #0
210:
	ldr x8, [x14, #0]
	ldr x9, [x5, #1440]
	eor x8, x8, x9
	str x8, [x14, #0]
	ldr x8, [x14, #8]
	ldr x9, [x5, #1448]
	eor x8, x8, x9
	str x8, [x14, #8]
	ldr x8, [x15, #0]
	str x8, [x5, #1440]
	ldr x8, [x15, #8]
	str x8, [x5, #1448]
	ldr x8, [x14, #0]
	str x8, [x15, #0]
	ldr x8, [x14, #8]
	str x8, [x15, #8]
	add x14, x14, #16
	add x15, x15, #16
	sub x17, x17, #1
	cbnz x17, 210b
	add x23, x15, #0
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
	ret
	.p2align 6
