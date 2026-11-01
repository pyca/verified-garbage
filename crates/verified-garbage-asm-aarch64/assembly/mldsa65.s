// The functions of `src/mldsa65.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa65_keygen:
	str x24, [x3, #840]
	str x25, [x3, #848]
	str x26, [x3, #856]
	str x27, [x3, #864]
	str x28, [x3, #872]
	str x30, [x3, #880]
	add x25, x0, #0
	add x26, x1, #0
	add x27, x2, #0
	add x28, x3, #0
	movz x24, #1, lsl #0
	movz x9, #6, lsl #0
	strb w9, [x28, #896]
	movz x9, #5, lsl #0
	strb w9, [x28, #897]
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
	movz x2, #0, lsl #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x5, x28, #200
	add x3, x25, #0
	movz x4, #32, lsl #0
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x5, x28, #200
	add x3, x28, #896
	movz x4, #2, lsl #0
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x4, x28, #200
	movz x3, #31, lsl #0
	bl {vg_keccak_pad_scratch}
	movz x2, #0, lsl #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x5, x28, #200
	add x3, x28, #1024
	movz x4, #128, lsl #0
	bl {vg_keccak_squeeze_scratch}
	ldr x9, [x28, #1024]
	str x9, [x28, #1152]
	ldr x9, [x28, #1032]
	str x9, [x28, #1160]
	ldr x9, [x28, #1040]
	str x9, [x28, #1168]
	ldr x9, [x28, #1048]
	str x9, [x28, #1176]
	ldr x9, [x28, #1056]
	str x9, [x28, #1216]
	ldr x9, [x28, #1064]
	str x9, [x28, #1224]
	ldr x9, [x28, #1072]
	str x9, [x28, #1232]
	ldr x9, [x28, #1080]
	str x9, [x28, #1240]
	ldr x9, [x28, #1088]
	str x9, [x28, #1248]
	ldr x9, [x28, #1096]
	str x9, [x28, #1256]
	ldr x9, [x28, #1104]
	str x9, [x28, #1264]
	ldr x9, [x28, #1112]
	str x9, [x28, #1272]
	movz x9, #0, lsl #0
	strb w9, [x28, #1281]
	add x10, x28, #1408
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #0, lsl #0
	strb w9, [x28, #1440]
	movz x9, #0, lsl #0
	strb w9, [x28, #1441]
	add x10, x28, #1442
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #1, lsl #0
	strb w9, [x28, #1474]
	movz x9, #0, lsl #0
	strb w9, [x28, #1475]
	add x10, x28, #1476
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #2, lsl #0
	strb w9, [x28, #1508]
	movz x9, #0, lsl #0
	strb w9, [x28, #1509]
	add x10, x28, #1510
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #3, lsl #0
	strb w9, [x28, #1542]
	movz x9, #0, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #4096, lsl #0
	add x1, x28, x1
	movz x2, #49152, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	movz x1, #4096, lsl #0
	add x1, x28, x1
	movz x2, #1024, lsl #0
20:
	ldr w9, [x1, #0]
	and w9, w9, w8
	str w9, [x1, #0]
	add x1, x1, #4
	sub x2, x2, #1
	cbnz x2, 20b
	add x10, x28, #1408
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #4, lsl #0
	strb w9, [x28, #1440]
	movz x9, #0, lsl #0
	strb w9, [x28, #1441]
	add x10, x28, #1442
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #0, lsl #0
	strb w9, [x28, #1474]
	movz x9, #1, lsl #0
	strb w9, [x28, #1475]
	add x10, x28, #1476
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #1, lsl #0
	strb w9, [x28, #1508]
	movz x9, #1, lsl #0
	strb w9, [x28, #1509]
	add x10, x28, #1510
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #2, lsl #0
	strb w9, [x28, #1542]
	movz x9, #1, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #8192, lsl #0
	add x1, x28, x1
	movz x2, #49152, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	movz x1, #8192, lsl #0
	add x1, x28, x1
	movz x2, #1024, lsl #0
21:
	ldr w9, [x1, #0]
	and w9, w9, w8
	str w9, [x1, #0]
	add x1, x1, #4
	sub x2, x2, #1
	cbnz x2, 21b
	add x10, x28, #1408
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #3, lsl #0
	strb w9, [x28, #1440]
	movz x9, #1, lsl #0
	strb w9, [x28, #1441]
	add x10, x28, #1442
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #4, lsl #0
	strb w9, [x28, #1474]
	movz x9, #1, lsl #0
	strb w9, [x28, #1475]
	add x10, x28, #1476
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #0, lsl #0
	strb w9, [x28, #1508]
	movz x9, #2, lsl #0
	strb w9, [x28, #1509]
	add x10, x28, #1510
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #1, lsl #0
	strb w9, [x28, #1542]
	movz x9, #2, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #12288, lsl #0
	add x1, x28, x1
	movz x2, #49152, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	movz x1, #12288, lsl #0
	add x1, x28, x1
	movz x2, #1024, lsl #0
22:
	ldr w9, [x1, #0]
	and w9, w9, w8
	str w9, [x1, #0]
	add x1, x1, #4
	sub x2, x2, #1
	cbnz x2, 22b
	add x10, x28, #1408
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #2, lsl #0
	strb w9, [x28, #1440]
	movz x9, #2, lsl #0
	strb w9, [x28, #1441]
	add x10, x28, #1442
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #3, lsl #0
	strb w9, [x28, #1474]
	movz x9, #2, lsl #0
	strb w9, [x28, #1475]
	add x10, x28, #1476
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #4, lsl #0
	strb w9, [x28, #1508]
	movz x9, #2, lsl #0
	strb w9, [x28, #1509]
	add x10, x28, #1510
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #0, lsl #0
	strb w9, [x28, #1542]
	movz x9, #3, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #16384, lsl #0
	add x1, x28, x1
	movz x2, #49152, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	movz x1, #16384, lsl #0
	add x1, x28, x1
	movz x2, #1024, lsl #0
23:
	ldr w9, [x1, #0]
	and w9, w9, w8
	str w9, [x1, #0]
	add x1, x1, #4
	sub x2, x2, #1
	cbnz x2, 23b
	add x10, x28, #1408
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #1, lsl #0
	strb w9, [x28, #1440]
	movz x9, #3, lsl #0
	strb w9, [x28, #1441]
	add x10, x28, #1442
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #2, lsl #0
	strb w9, [x28, #1474]
	movz x9, #3, lsl #0
	strb w9, [x28, #1475]
	add x10, x28, #1476
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #3, lsl #0
	strb w9, [x28, #1508]
	movz x9, #3, lsl #0
	strb w9, [x28, #1509]
	add x10, x28, #1510
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #4, lsl #0
	strb w9, [x28, #1542]
	movz x9, #3, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #20480, lsl #0
	add x1, x28, x1
	movz x2, #49152, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	movz x1, #20480, lsl #0
	add x1, x28, x1
	movz x2, #1024, lsl #0
24:
	ldr w9, [x1, #0]
	and w9, w9, w8
	str w9, [x1, #0]
	add x1, x1, #4
	sub x2, x2, #1
	cbnz x2, 24b
	add x10, x28, #1408
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #0, lsl #0
	strb w9, [x28, #1440]
	movz x9, #4, lsl #0
	strb w9, [x28, #1441]
	add x10, x28, #1442
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #1, lsl #0
	strb w9, [x28, #1474]
	movz x9, #4, lsl #0
	strb w9, [x28, #1475]
	add x10, x28, #1476
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #2, lsl #0
	strb w9, [x28, #1508]
	movz x9, #4, lsl #0
	strb w9, [x28, #1509]
	add x10, x28, #1510
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #3, lsl #0
	strb w9, [x28, #1542]
	movz x9, #4, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #24576, lsl #0
	add x1, x28, x1
	movz x2, #49152, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	movz x1, #24576, lsl #0
	add x1, x28, x1
	movz x2, #1024, lsl #0
25:
	ldr w9, [x1, #0]
	and w9, w9, w8
	str w9, [x1, #0]
	add x1, x1, #4
	sub x2, x2, #1
	cbnz x2, 25b
	add x10, x28, #1408
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #4, lsl #0
	strb w9, [x28, #1440]
	movz x9, #4, lsl #0
	strb w9, [x28, #1441]
	add x10, x28, #1442
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #0, lsl #0
	strb w9, [x28, #1474]
	movz x9, #5, lsl #0
	strb w9, [x28, #1475]
	add x10, x28, #1476
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #1, lsl #0
	strb w9, [x28, #1508]
	movz x9, #5, lsl #0
	strb w9, [x28, #1509]
	add x10, x28, #1510
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #2, lsl #0
	strb w9, [x28, #1542]
	movz x9, #5, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #28672, lsl #0
	add x1, x28, x1
	movz x2, #49152, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	movz x1, #28672, lsl #0
	add x1, x28, x1
	movz x2, #1024, lsl #0
26:
	ldr w9, [x1, #0]
	and w9, w9, w8
	str w9, [x1, #0]
	add x1, x1, #4
	sub x2, x2, #1
	cbnz x2, 26b
	movz x9, #3, lsl #0
	strb w9, [x28, #1184]
	movz x9, #5, lsl #0
	strb w9, [x28, #1185]
	add x0, x28, #1152
	movz x1, #32768, lsl #0
	add x1, x28, x1
	add x2, x28, #2048
	str x25, [x2, #2016]
	str x26, [x2, #2024]
	str x27, [x2, #2032]
	str x30, [x2, #2040]
	add x25, x2, #0
	add x26, x1, #0
	movz x27, #0, lsl #0
	add x3, x0, #0
	movz x4, #34, lsl #0
	movz x9, #0, lsl #0
	str x9, [x25, #0]
	str x9, [x25, #8]
	str x9, [x25, #16]
	str x9, [x25, #24]
	str x9, [x25, #32]
	str x9, [x25, #40]
	str x9, [x25, #48]
	str x9, [x25, #56]
	str x9, [x25, #64]
	str x9, [x25, #72]
	str x9, [x25, #80]
	str x9, [x25, #88]
	str x9, [x25, #96]
	str x9, [x25, #104]
	str x9, [x25, #112]
	str x9, [x25, #120]
	str x9, [x25, #128]
	str x9, [x25, #136]
	str x9, [x25, #144]
	str x9, [x25, #152]
	str x9, [x25, #160]
	str x9, [x25, #168]
	str x9, [x25, #176]
	str x9, [x25, #184]
	str x9, [x25, #192]
	add x0, x25, #0
	movz x1, #168, lsl #0
	movz x2, #0, lsl #0
	add x5, x25, #200
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	add x0, x25, #0
	movz x1, #168, lsl #0
	movz x3, #31, lsl #0
	add x4, x25, #200
	bl {vg_keccak_pad_scratch}
	add x0, x25, #0
	movz x1, #168, lsl #0
	movz x2, #0, lsl #0
	add x3, x25, #840
	movz x4, #1008, lsl #0
	add x5, x25, #200
	bl {vg_keccak_squeeze_scratch}
	movz x9, #0, lsl #0
	add x3, x26, #0
	movz x4, #256, lsl #0
27:
	str w9, [x3, #0]
	add x3, x3, #4
	sub x4, x4, #1
	cbnz x4, 27b
	add x2, x25, #840
	add x3, x26, #0
	movz x4, #256, lsl #0
	movz x5, #336, lsl #0
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
	movz x10, #127, lsl #0
28:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x8, x8, x10
	lsl x8, x8, #16
	lsl x7, x7, #8
	add x11, x6, x7
	add x11, x11, x8
	cbz x4, 29f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	b 210f
29:
210:
	cbnz x5, 28b
	sub x0, x4, #1
	lsr x0, x0, #63
	ldr x30, [x25, #2040]
	ldr x26, [x25, #2024]
	ldr x27, [x25, #2032]
	ldr x25, [x25, #2016]
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	movz x1, #32768, lsl #0
	add x1, x28, x1
	movz x2, #256, lsl #0
211:
	ldr w9, [x1, #0]
	and w9, w9, w8
	str w9, [x1, #0]
	add x1, x1, #4
	sub x2, x2, #1
	cbnz x2, 211b
	movz x9, #4, lsl #0
	strb w9, [x28, #1184]
	movz x9, #5, lsl #0
	strb w9, [x28, #1185]
	add x0, x28, #1152
	movz x1, #33792, lsl #0
	add x1, x28, x1
	add x2, x28, #2048
	str x25, [x2, #2016]
	str x26, [x2, #2024]
	str x27, [x2, #2032]
	str x30, [x2, #2040]
	add x25, x2, #0
	add x26, x1, #0
	movz x27, #0, lsl #0
	add x3, x0, #0
	movz x4, #34, lsl #0
	movz x9, #0, lsl #0
	str x9, [x25, #0]
	str x9, [x25, #8]
	str x9, [x25, #16]
	str x9, [x25, #24]
	str x9, [x25, #32]
	str x9, [x25, #40]
	str x9, [x25, #48]
	str x9, [x25, #56]
	str x9, [x25, #64]
	str x9, [x25, #72]
	str x9, [x25, #80]
	str x9, [x25, #88]
	str x9, [x25, #96]
	str x9, [x25, #104]
	str x9, [x25, #112]
	str x9, [x25, #120]
	str x9, [x25, #128]
	str x9, [x25, #136]
	str x9, [x25, #144]
	str x9, [x25, #152]
	str x9, [x25, #160]
	str x9, [x25, #168]
	str x9, [x25, #176]
	str x9, [x25, #184]
	str x9, [x25, #192]
	add x0, x25, #0
	movz x1, #168, lsl #0
	movz x2, #0, lsl #0
	add x5, x25, #200
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	add x0, x25, #0
	movz x1, #168, lsl #0
	movz x3, #31, lsl #0
	add x4, x25, #200
	bl {vg_keccak_pad_scratch}
	add x0, x25, #0
	movz x1, #168, lsl #0
	movz x2, #0, lsl #0
	add x3, x25, #840
	movz x4, #1008, lsl #0
	add x5, x25, #200
	bl {vg_keccak_squeeze_scratch}
	movz x9, #0, lsl #0
	add x3, x26, #0
	movz x4, #256, lsl #0
212:
	str w9, [x3, #0]
	add x3, x3, #4
	sub x4, x4, #1
	cbnz x4, 212b
	add x2, x25, #840
	add x3, x26, #0
	movz x4, #256, lsl #0
	movz x5, #336, lsl #0
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
	movz x10, #127, lsl #0
213:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x8, x8, x10
	lsl x8, x8, #16
	lsl x7, x7, #8
	add x11, x6, x7
	add x11, x11, x8
	cbz x4, 214f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	b 215f
214:
215:
	cbnz x5, 213b
	sub x0, x4, #1
	lsr x0, x0, #63
	ldr x30, [x25, #2040]
	ldr x26, [x25, #2024]
	ldr x27, [x25, #2032]
	ldr x25, [x25, #2016]
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	movz x1, #33792, lsl #0
	add x1, x28, x1
	movz x2, #256, lsl #0
216:
	ldr w9, [x1, #0]
	and w9, w9, w8
	str w9, [x1, #0]
	add x1, x1, #4
	sub x2, x2, #1
	cbnz x2, 216b
	add x10, x28, #1408
	ldr x9, [x28, #1216]
	str x9, [x10, #0]
	ldr x9, [x28, #1224]
	str x9, [x10, #8]
	ldr x9, [x28, #1232]
	str x9, [x10, #16]
	ldr x9, [x28, #1240]
	str x9, [x10, #24]
	ldr x9, [x28, #1248]
	str x9, [x10, #32]
	ldr x9, [x28, #1256]
	str x9, [x10, #40]
	ldr x9, [x28, #1264]
	str x9, [x10, #48]
	ldr x9, [x28, #1272]
	str x9, [x10, #56]
	movz x9, #0, lsl #0
	strb w9, [x28, #1472]
	movz x9, #0, lsl #0
	strb w9, [x28, #1473]
	add x10, x28, #1474
	ldr x9, [x28, #1216]
	str x9, [x10, #0]
	ldr x9, [x28, #1224]
	str x9, [x10, #8]
	ldr x9, [x28, #1232]
	str x9, [x10, #16]
	ldr x9, [x28, #1240]
	str x9, [x10, #24]
	ldr x9, [x28, #1248]
	str x9, [x10, #32]
	ldr x9, [x28, #1256]
	str x9, [x10, #40]
	ldr x9, [x28, #1264]
	str x9, [x10, #48]
	ldr x9, [x28, #1272]
	str x9, [x10, #56]
	movz x9, #1, lsl #0
	strb w9, [x28, #1538]
	movz x9, #0, lsl #0
	strb w9, [x28, #1539]
	add x10, x28, #1540
	ldr x9, [x28, #1216]
	str x9, [x10, #0]
	ldr x9, [x28, #1224]
	str x9, [x10, #8]
	ldr x9, [x28, #1232]
	str x9, [x10, #16]
	ldr x9, [x28, #1240]
	str x9, [x10, #24]
	ldr x9, [x28, #1248]
	str x9, [x10, #32]
	ldr x9, [x28, #1256]
	str x9, [x10, #40]
	ldr x9, [x28, #1264]
	str x9, [x10, #48]
	ldr x9, [x28, #1272]
	str x9, [x10, #56]
	movz x9, #2, lsl #0
	strb w9, [x28, #1604]
	movz x9, #0, lsl #0
	strb w9, [x28, #1605]
	add x10, x28, #1606
	ldr x9, [x28, #1216]
	str x9, [x10, #0]
	ldr x9, [x28, #1224]
	str x9, [x10, #8]
	ldr x9, [x28, #1232]
	str x9, [x10, #16]
	ldr x9, [x28, #1240]
	str x9, [x10, #24]
	ldr x9, [x28, #1248]
	str x9, [x10, #32]
	ldr x9, [x28, #1256]
	str x9, [x10, #40]
	ldr x9, [x28, #1264]
	str x9, [x10, #48]
	ldr x9, [x28, #1272]
	str x9, [x10, #56]
	movz x9, #3, lsl #0
	strb w9, [x28, #1670]
	movz x9, #0, lsl #0
	strb w9, [x28, #1671]
	add x0, x28, #1408
	movz x1, #34816, lsl #0
	add x1, x28, x1
	movz x2, #49152, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_rej_bounded_poly4_eta4}
	and w24, w24, w0
	add x10, x28, #1408
	ldr x9, [x28, #1216]
	str x9, [x10, #0]
	ldr x9, [x28, #1224]
	str x9, [x10, #8]
	ldr x9, [x28, #1232]
	str x9, [x10, #16]
	ldr x9, [x28, #1240]
	str x9, [x10, #24]
	ldr x9, [x28, #1248]
	str x9, [x10, #32]
	ldr x9, [x28, #1256]
	str x9, [x10, #40]
	ldr x9, [x28, #1264]
	str x9, [x10, #48]
	ldr x9, [x28, #1272]
	str x9, [x10, #56]
	movz x9, #4, lsl #0
	strb w9, [x28, #1472]
	movz x9, #0, lsl #0
	strb w9, [x28, #1473]
	add x10, x28, #1474
	ldr x9, [x28, #1216]
	str x9, [x10, #0]
	ldr x9, [x28, #1224]
	str x9, [x10, #8]
	ldr x9, [x28, #1232]
	str x9, [x10, #16]
	ldr x9, [x28, #1240]
	str x9, [x10, #24]
	ldr x9, [x28, #1248]
	str x9, [x10, #32]
	ldr x9, [x28, #1256]
	str x9, [x10, #40]
	ldr x9, [x28, #1264]
	str x9, [x10, #48]
	ldr x9, [x28, #1272]
	str x9, [x10, #56]
	movz x9, #5, lsl #0
	strb w9, [x28, #1538]
	movz x9, #0, lsl #0
	strb w9, [x28, #1539]
	add x10, x28, #1540
	ldr x9, [x28, #1216]
	str x9, [x10, #0]
	ldr x9, [x28, #1224]
	str x9, [x10, #8]
	ldr x9, [x28, #1232]
	str x9, [x10, #16]
	ldr x9, [x28, #1240]
	str x9, [x10, #24]
	ldr x9, [x28, #1248]
	str x9, [x10, #32]
	ldr x9, [x28, #1256]
	str x9, [x10, #40]
	ldr x9, [x28, #1264]
	str x9, [x10, #48]
	ldr x9, [x28, #1272]
	str x9, [x10, #56]
	movz x9, #6, lsl #0
	strb w9, [x28, #1604]
	movz x9, #0, lsl #0
	strb w9, [x28, #1605]
	add x10, x28, #1606
	ldr x9, [x28, #1216]
	str x9, [x10, #0]
	ldr x9, [x28, #1224]
	str x9, [x10, #8]
	ldr x9, [x28, #1232]
	str x9, [x10, #16]
	ldr x9, [x28, #1240]
	str x9, [x10, #24]
	ldr x9, [x28, #1248]
	str x9, [x10, #32]
	ldr x9, [x28, #1256]
	str x9, [x10, #40]
	ldr x9, [x28, #1264]
	str x9, [x10, #48]
	ldr x9, [x28, #1272]
	str x9, [x10, #56]
	movz x9, #7, lsl #0
	strb w9, [x28, #1670]
	movz x9, #0, lsl #0
	strb w9, [x28, #1671]
	add x0, x28, #1408
	movz x1, #38912, lsl #0
	add x1, x28, x1
	movz x2, #49152, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_rej_bounded_poly4_eta4}
	and w24, w24, w0
	add x10, x28, #1408
	ldr x9, [x28, #1216]
	str x9, [x10, #0]
	ldr x9, [x28, #1224]
	str x9, [x10, #8]
	ldr x9, [x28, #1232]
	str x9, [x10, #16]
	ldr x9, [x28, #1240]
	str x9, [x10, #24]
	ldr x9, [x28, #1248]
	str x9, [x10, #32]
	ldr x9, [x28, #1256]
	str x9, [x10, #40]
	ldr x9, [x28, #1264]
	str x9, [x10, #48]
	ldr x9, [x28, #1272]
	str x9, [x10, #56]
	movz x9, #8, lsl #0
	strb w9, [x28, #1472]
	movz x9, #0, lsl #0
	strb w9, [x28, #1473]
	add x10, x28, #1474
	ldr x9, [x28, #1216]
	str x9, [x10, #0]
	ldr x9, [x28, #1224]
	str x9, [x10, #8]
	ldr x9, [x28, #1232]
	str x9, [x10, #16]
	ldr x9, [x28, #1240]
	str x9, [x10, #24]
	ldr x9, [x28, #1248]
	str x9, [x10, #32]
	ldr x9, [x28, #1256]
	str x9, [x10, #40]
	ldr x9, [x28, #1264]
	str x9, [x10, #48]
	ldr x9, [x28, #1272]
	str x9, [x10, #56]
	movz x9, #9, lsl #0
	strb w9, [x28, #1538]
	movz x9, #0, lsl #0
	strb w9, [x28, #1539]
	add x10, x28, #1540
	ldr x9, [x28, #1216]
	str x9, [x10, #0]
	ldr x9, [x28, #1224]
	str x9, [x10, #8]
	ldr x9, [x28, #1232]
	str x9, [x10, #16]
	ldr x9, [x28, #1240]
	str x9, [x10, #24]
	ldr x9, [x28, #1248]
	str x9, [x10, #32]
	ldr x9, [x28, #1256]
	str x9, [x10, #40]
	ldr x9, [x28, #1264]
	str x9, [x10, #48]
	ldr x9, [x28, #1272]
	str x9, [x10, #56]
	movz x9, #10, lsl #0
	strb w9, [x28, #1604]
	movz x9, #0, lsl #0
	strb w9, [x28, #1605]
	add x10, x28, #1606
	ldr x9, [x28, #1216]
	str x9, [x10, #0]
	ldr x9, [x28, #1224]
	str x9, [x10, #8]
	ldr x9, [x28, #1232]
	str x9, [x10, #16]
	ldr x9, [x28, #1240]
	str x9, [x10, #24]
	ldr x9, [x28, #1248]
	str x9, [x10, #32]
	ldr x9, [x28, #1256]
	str x9, [x10, #40]
	ldr x9, [x28, #1264]
	str x9, [x10, #48]
	ldr x9, [x28, #1272]
	str x9, [x10, #56]
	movz x9, #8, lsl #0
	strb w9, [x28, #1670]
	movz x9, #0, lsl #0
	strb w9, [x28, #1671]
	add x0, x28, #1408
	movz x1, #43008, lsl #0
	add x1, x28, x1
	movz x2, #49152, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_rej_bounded_poly4_eta4}
	and w24, w24, w0
	ldr x9, [x28, #1024]
	str x9, [x26, #0]
	ldr x9, [x28, #1032]
	str x9, [x26, #8]
	ldr x9, [x28, #1040]
	str x9, [x26, #16]
	ldr x9, [x28, #1048]
	str x9, [x26, #24]
	ldr x9, [x28, #1024]
	str x9, [x27, #0]
	ldr x9, [x28, #1032]
	str x9, [x27, #8]
	ldr x9, [x28, #1040]
	str x9, [x27, #16]
	ldr x9, [x28, #1048]
	str x9, [x27, #24]
	ldr x9, [x28, #1120]
	str x9, [x27, #32]
	ldr x9, [x28, #1128]
	str x9, [x27, #40]
	ldr x9, [x28, #1136]
	str x9, [x27, #48]
	ldr x9, [x28, #1144]
	str x9, [x27, #56]
	movz x0, #34816, lsl #0
	add x0, x28, x0
	movz x1, #4, lsl #0
	movz x2, #4, lsl #0
	add x3, x27, #128
	movz x4, #128, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #35840, lsl #0
	add x0, x28, x0
	movz x1, #4, lsl #0
	movz x2, #4, lsl #0
	add x3, x27, #256
	movz x4, #128, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #36864, lsl #0
	add x0, x28, x0
	movz x1, #4, lsl #0
	movz x2, #4, lsl #0
	add x3, x27, #384
	movz x4, #128, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #37888, lsl #0
	add x0, x28, x0
	movz x1, #4, lsl #0
	movz x2, #4, lsl #0
	add x3, x27, #512
	movz x4, #128, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #38912, lsl #0
	add x0, x28, x0
	movz x1, #4, lsl #0
	movz x2, #4, lsl #0
	add x3, x27, #640
	movz x4, #128, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #39936, lsl #0
	add x0, x28, x0
	movz x1, #4, lsl #0
	movz x2, #4, lsl #0
	add x3, x27, #768
	movz x4, #128, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #40960, lsl #0
	add x0, x28, x0
	movz x1, #4, lsl #0
	movz x2, #4, lsl #0
	add x3, x27, #896
	movz x4, #128, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #41984, lsl #0
	add x0, x28, x0
	movz x1, #4, lsl #0
	movz x2, #4, lsl #0
	add x3, x27, #1024
	movz x4, #128, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #43008, lsl #0
	add x0, x28, x0
	movz x1, #4, lsl #0
	movz x2, #4, lsl #0
	add x3, x27, #1152
	movz x4, #128, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #44032, lsl #0
	add x0, x28, x0
	movz x1, #4, lsl #0
	movz x2, #4, lsl #0
	add x3, x27, #1280
	movz x4, #128, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #45056, lsl #0
	add x0, x28, x0
	movz x1, #4, lsl #0
	movz x2, #4, lsl #0
	add x3, x27, #1408
	movz x4, #128, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #34816, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_ntt}
	movz x0, #35840, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_ntt}
	movz x0, #36864, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_ntt}
	movz x0, #37888, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_ntt}
	movz x0, #38912, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_ntt}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #4096, lsl #0
	add x1, x28, x1
	movz x2, #34816, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_ntt}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #5120, lsl #0
	add x1, x28, x1
	movz x2, #35840, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #6144, lsl #0
	add x1, x28, x1
	movz x2, #36864, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #7168, lsl #0
	add x1, x28, x1
	movz x2, #37888, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #8192, lsl #0
	add x1, x28, x1
	movz x2, #38912, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_inv_ntt}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #39936, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_add}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #47104, lsl #0
	add x1, x28, x1
	movz x2, #48128, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_power2round}
	movz x0, #47104, lsl #0
	add x0, x28, x0
	movz x1, #1023, lsl #0
	add x2, x26, #32
	movz x3, #320, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #48128, lsl #0
	add x0, x28, x0
	movz x1, #4095, lsl #0
	movz x2, #4096, lsl #0
	add x3, x27, #1536
	movz x4, #416, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #9216, lsl #0
	add x1, x28, x1
	movz x2, #34816, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_ntt}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #10240, lsl #0
	add x1, x28, x1
	movz x2, #35840, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #11264, lsl #0
	add x1, x28, x1
	movz x2, #36864, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #12288, lsl #0
	add x1, x28, x1
	movz x2, #37888, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #13312, lsl #0
	add x1, x28, x1
	movz x2, #38912, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_inv_ntt}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #40960, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_add}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #47104, lsl #0
	add x1, x28, x1
	movz x2, #48128, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_power2round}
	movz x0, #47104, lsl #0
	add x0, x28, x0
	movz x1, #1023, lsl #0
	add x2, x26, #352
	movz x3, #320, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #48128, lsl #0
	add x0, x28, x0
	movz x1, #4095, lsl #0
	movz x2, #4096, lsl #0
	add x3, x27, #1952
	movz x4, #416, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #14336, lsl #0
	add x1, x28, x1
	movz x2, #34816, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_ntt}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #15360, lsl #0
	add x1, x28, x1
	movz x2, #35840, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #16384, lsl #0
	add x1, x28, x1
	movz x2, #36864, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #17408, lsl #0
	add x1, x28, x1
	movz x2, #37888, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #18432, lsl #0
	add x1, x28, x1
	movz x2, #38912, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_inv_ntt}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #41984, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_add}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #47104, lsl #0
	add x1, x28, x1
	movz x2, #48128, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_power2round}
	movz x0, #47104, lsl #0
	add x0, x28, x0
	movz x1, #1023, lsl #0
	add x2, x26, #672
	movz x3, #320, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #48128, lsl #0
	add x0, x28, x0
	movz x1, #4095, lsl #0
	movz x2, #4096, lsl #0
	add x3, x27, #2368
	movz x4, #416, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #19456, lsl #0
	add x1, x28, x1
	movz x2, #34816, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_ntt}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #20480, lsl #0
	add x1, x28, x1
	movz x2, #35840, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #21504, lsl #0
	add x1, x28, x1
	movz x2, #36864, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #22528, lsl #0
	add x1, x28, x1
	movz x2, #37888, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #23552, lsl #0
	add x1, x28, x1
	movz x2, #38912, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_inv_ntt}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #43008, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_add}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #47104, lsl #0
	add x1, x28, x1
	movz x2, #48128, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_power2round}
	movz x0, #47104, lsl #0
	add x0, x28, x0
	movz x1, #1023, lsl #0
	add x2, x26, #992
	movz x3, #320, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #48128, lsl #0
	add x0, x28, x0
	movz x1, #4095, lsl #0
	movz x2, #4096, lsl #0
	add x3, x27, #2784
	movz x4, #416, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #24576, lsl #0
	add x1, x28, x1
	movz x2, #34816, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_ntt}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #25600, lsl #0
	add x1, x28, x1
	movz x2, #35840, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #26624, lsl #0
	add x1, x28, x1
	movz x2, #36864, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #27648, lsl #0
	add x1, x28, x1
	movz x2, #37888, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #28672, lsl #0
	add x1, x28, x1
	movz x2, #38912, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_inv_ntt}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #44032, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_add}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #47104, lsl #0
	add x1, x28, x1
	movz x2, #48128, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_power2round}
	movz x0, #47104, lsl #0
	add x0, x28, x0
	movz x1, #1023, lsl #0
	add x2, x26, #1312
	movz x3, #320, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #48128, lsl #0
	add x0, x28, x0
	movz x1, #4095, lsl #0
	movz x2, #4096, lsl #0
	add x3, x27, #3200
	movz x4, #416, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #29696, lsl #0
	add x1, x28, x1
	movz x2, #34816, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_ntt}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #30720, lsl #0
	add x1, x28, x1
	movz x2, #35840, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #31744, lsl #0
	add x1, x28, x1
	movz x2, #36864, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #32768, lsl #0
	add x1, x28, x1
	movz x2, #37888, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #33792, lsl #0
	add x1, x28, x1
	movz x2, #38912, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_inv_ntt}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #45056, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_add}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #47104, lsl #0
	add x1, x28, x1
	movz x2, #48128, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_power2round}
	movz x0, #47104, lsl #0
	add x0, x28, x0
	movz x1, #1023, lsl #0
	add x2, x26, #1632
	movz x3, #320, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #48128, lsl #0
	add x0, x28, x0
	movz x1, #4095, lsl #0
	movz x2, #4096, lsl #0
	add x3, x27, #3616
	movz x4, #416, lsl #0
	bl {vg_mldsa_bit_pack}
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
	movz x2, #0, lsl #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x5, x28, #200
	add x3, x26, #0
	movz x4, #1952, lsl #0
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x4, x28, #200
	movz x3, #31, lsl #0
	bl {vg_keccak_pad_scratch}
	movz x2, #0, lsl #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x5, x28, #200
	add x3, x27, #64
	movz x4, #64, lsl #0
	bl {vg_keccak_squeeze_scratch}
	add x0, x24, #0
	ldr x30, [x28, #880]
	ldr x24, [x28, #840]
	ldr x25, [x28, #848]
	ldr x26, [x28, #856]
	ldr x27, [x28, #864]
	ldr x28, [x28, #872]
	ret
	.p2align 6

vg_mldsa65_sign:
	str x23, [x4, #840]
	str x24, [x4, #848]
	str x25, [x4, #856]
	str x26, [x4, #864]
	str x27, [x4, #872]
	str x30, [x4, #880]
	str x28, [x4, #888]
	add x28, x4, #0
	add x25, x0, #0
	add x26, x1, #0
	add x27, x2, #0
	add x23, x3, #0
	movz x24, #1, lsl #0
	ldr x9, [x25, #0]
	str x9, [x28, #920]
	ldr x9, [x25, #8]
	str x9, [x28, #928]
	ldr x9, [x25, #16]
	str x9, [x28, #936]
	ldr x9, [x25, #24]
	str x9, [x28, #944]
	add x10, x28, #1408
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #0, lsl #0
	strb w9, [x28, #1440]
	movz x9, #0, lsl #0
	strb w9, [x28, #1441]
	add x10, x28, #1442
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #1, lsl #0
	strb w9, [x28, #1474]
	movz x9, #0, lsl #0
	strb w9, [x28, #1475]
	add x10, x28, #1476
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #2, lsl #0
	strb w9, [x28, #1508]
	movz x9, #0, lsl #0
	strb w9, [x28, #1509]
	add x10, x28, #1510
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #3, lsl #0
	strb w9, [x28, #1542]
	movz x9, #0, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #50176, lsl #0
	add x1, x28, x1
	movz x2, #15360, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4}
	and w24, w24, w0
	add x10, x28, #1408
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #4, lsl #0
	strb w9, [x28, #1440]
	movz x9, #0, lsl #0
	strb w9, [x28, #1441]
	add x10, x28, #1442
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #0, lsl #0
	strb w9, [x28, #1474]
	movz x9, #1, lsl #0
	strb w9, [x28, #1475]
	add x10, x28, #1476
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #1, lsl #0
	strb w9, [x28, #1508]
	movz x9, #1, lsl #0
	strb w9, [x28, #1509]
	add x10, x28, #1510
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #2, lsl #0
	strb w9, [x28, #1542]
	movz x9, #1, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #54272, lsl #0
	add x1, x28, x1
	movz x2, #15360, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4}
	and w24, w24, w0
	add x10, x28, #1408
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #3, lsl #0
	strb w9, [x28, #1440]
	movz x9, #1, lsl #0
	strb w9, [x28, #1441]
	add x10, x28, #1442
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #4, lsl #0
	strb w9, [x28, #1474]
	movz x9, #1, lsl #0
	strb w9, [x28, #1475]
	add x10, x28, #1476
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #0, lsl #0
	strb w9, [x28, #1508]
	movz x9, #2, lsl #0
	strb w9, [x28, #1509]
	add x10, x28, #1510
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #1, lsl #0
	strb w9, [x28, #1542]
	movz x9, #2, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #58368, lsl #0
	add x1, x28, x1
	movz x2, #15360, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4}
	and w24, w24, w0
	add x10, x28, #1408
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #2, lsl #0
	strb w9, [x28, #1440]
	movz x9, #2, lsl #0
	strb w9, [x28, #1441]
	add x10, x28, #1442
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #3, lsl #0
	strb w9, [x28, #1474]
	movz x9, #2, lsl #0
	strb w9, [x28, #1475]
	add x10, x28, #1476
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #4, lsl #0
	strb w9, [x28, #1508]
	movz x9, #2, lsl #0
	strb w9, [x28, #1509]
	add x10, x28, #1510
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #0, lsl #0
	strb w9, [x28, #1542]
	movz x9, #3, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #62464, lsl #0
	add x1, x28, x1
	movz x2, #15360, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4}
	and w24, w24, w0
	add x10, x28, #1408
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #1, lsl #0
	strb w9, [x28, #1440]
	movz x9, #3, lsl #0
	strb w9, [x28, #1441]
	add x10, x28, #1442
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #2, lsl #0
	strb w9, [x28, #1474]
	movz x9, #3, lsl #0
	strb w9, [x28, #1475]
	add x10, x28, #1476
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #3, lsl #0
	strb w9, [x28, #1508]
	movz x9, #3, lsl #0
	strb w9, [x28, #1509]
	add x10, x28, #1510
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #4, lsl #0
	strb w9, [x28, #1542]
	movz x9, #3, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #1024, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	movz x2, #15360, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4}
	and w24, w24, w0
	add x10, x28, #1408
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #0, lsl #0
	strb w9, [x28, #1440]
	movz x9, #4, lsl #0
	strb w9, [x28, #1441]
	add x10, x28, #1442
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #1, lsl #0
	strb w9, [x28, #1474]
	movz x9, #4, lsl #0
	strb w9, [x28, #1475]
	add x10, x28, #1476
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #2, lsl #0
	strb w9, [x28, #1508]
	movz x9, #4, lsl #0
	strb w9, [x28, #1509]
	add x10, x28, #1510
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #3, lsl #0
	strb w9, [x28, #1542]
	movz x9, #4, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #5120, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	movz x2, #15360, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4}
	and w24, w24, w0
	add x10, x28, #1408
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #4, lsl #0
	strb w9, [x28, #1440]
	movz x9, #4, lsl #0
	strb w9, [x28, #1441]
	add x10, x28, #1442
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #0, lsl #0
	strb w9, [x28, #1474]
	movz x9, #5, lsl #0
	strb w9, [x28, #1475]
	add x10, x28, #1476
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #1, lsl #0
	strb w9, [x28, #1508]
	movz x9, #5, lsl #0
	strb w9, [x28, #1509]
	add x10, x28, #1510
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #2, lsl #0
	strb w9, [x28, #1542]
	movz x9, #5, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #9216, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	movz x2, #15360, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4}
	and w24, w24, w0
	movz x9, #3, lsl #0
	strb w9, [x28, #952]
	movz x9, #5, lsl #0
	strb w9, [x28, #953]
	add x0, x28, #920
	movz x1, #13312, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	add x2, x28, #3072
	str x25, [x2, #2016]
	str x26, [x2, #2024]
	str x27, [x2, #2032]
	str x30, [x2, #2040]
	add x25, x2, #0
	add x26, x1, #0
	movz x27, #0, lsl #0
	add x3, x0, #0
	movz x4, #34, lsl #0
	movz x9, #0, lsl #0
	str x9, [x25, #0]
	str x9, [x25, #8]
	str x9, [x25, #16]
	str x9, [x25, #24]
	str x9, [x25, #32]
	str x9, [x25, #40]
	str x9, [x25, #48]
	str x9, [x25, #56]
	str x9, [x25, #64]
	str x9, [x25, #72]
	str x9, [x25, #80]
	str x9, [x25, #88]
	str x9, [x25, #96]
	str x9, [x25, #104]
	str x9, [x25, #112]
	str x9, [x25, #120]
	str x9, [x25, #128]
	str x9, [x25, #136]
	str x9, [x25, #144]
	str x9, [x25, #152]
	str x9, [x25, #160]
	str x9, [x25, #168]
	str x9, [x25, #176]
	str x9, [x25, #184]
	str x9, [x25, #192]
	add x0, x25, #0
	movz x1, #168, lsl #0
	movz x2, #0, lsl #0
	add x5, x25, #200
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	add x0, x25, #0
	movz x1, #168, lsl #0
	movz x3, #31, lsl #0
	add x4, x25, #200
	bl {vg_keccak_pad_scratch}
	add x0, x25, #0
	movz x1, #168, lsl #0
	movz x2, #0, lsl #0
	add x3, x25, #840
	movz x4, #1008, lsl #0
	add x5, x25, #200
	bl {vg_keccak_squeeze_scratch}
	movz x9, #0, lsl #0
	add x3, x26, #0
	movz x4, #256, lsl #0
20:
	str w9, [x3, #0]
	add x3, x3, #4
	sub x4, x4, #1
	cbnz x4, 20b
	add x2, x25, #840
	add x3, x26, #0
	movz x4, #256, lsl #0
	movz x5, #336, lsl #0
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
	movz x10, #127, lsl #0
21:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x8, x8, x10
	lsl x8, x8, #16
	lsl x7, x7, #8
	add x11, x6, x7
	add x11, x11, x8
	cbz x4, 22f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	b 23f
22:
23:
	cbnz x5, 21b
	sub x0, x4, #1
	lsr x0, x0, #63
	ldr x30, [x25, #2040]
	ldr x26, [x25, #2024]
	ldr x27, [x25, #2032]
	ldr x25, [x25, #2016]
	and w24, w24, w0
	movz x9, #4, lsl #0
	strb w9, [x28, #952]
	movz x9, #5, lsl #0
	strb w9, [x28, #953]
	add x0, x28, #920
	movz x1, #14336, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	add x2, x28, #3072
	str x25, [x2, #2016]
	str x26, [x2, #2024]
	str x27, [x2, #2032]
	str x30, [x2, #2040]
	add x25, x2, #0
	add x26, x1, #0
	movz x27, #0, lsl #0
	add x3, x0, #0
	movz x4, #34, lsl #0
	movz x9, #0, lsl #0
	str x9, [x25, #0]
	str x9, [x25, #8]
	str x9, [x25, #16]
	str x9, [x25, #24]
	str x9, [x25, #32]
	str x9, [x25, #40]
	str x9, [x25, #48]
	str x9, [x25, #56]
	str x9, [x25, #64]
	str x9, [x25, #72]
	str x9, [x25, #80]
	str x9, [x25, #88]
	str x9, [x25, #96]
	str x9, [x25, #104]
	str x9, [x25, #112]
	str x9, [x25, #120]
	str x9, [x25, #128]
	str x9, [x25, #136]
	str x9, [x25, #144]
	str x9, [x25, #152]
	str x9, [x25, #160]
	str x9, [x25, #168]
	str x9, [x25, #176]
	str x9, [x25, #184]
	str x9, [x25, #192]
	add x0, x25, #0
	movz x1, #168, lsl #0
	movz x2, #0, lsl #0
	add x5, x25, #200
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	add x0, x25, #0
	movz x1, #168, lsl #0
	movz x3, #31, lsl #0
	add x4, x25, #200
	bl {vg_keccak_pad_scratch}
	add x0, x25, #0
	movz x1, #168, lsl #0
	movz x2, #0, lsl #0
	add x3, x25, #840
	movz x4, #1008, lsl #0
	add x5, x25, #200
	bl {vg_keccak_squeeze_scratch}
	movz x9, #0, lsl #0
	add x3, x26, #0
	movz x4, #256, lsl #0
24:
	str w9, [x3, #0]
	add x3, x3, #4
	sub x4, x4, #1
	cbnz x4, 24b
	add x2, x25, #840
	add x3, x26, #0
	movz x4, #256, lsl #0
	movz x5, #336, lsl #0
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
	movz x10, #127, lsl #0
25:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x8, x8, x10
	lsl x8, x8, #16
	lsl x7, x7, #8
	add x11, x6, x7
	add x11, x11, x8
	cbz x4, 26f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	b 27f
26:
27:
	cbnz x5, 25b
	sub x0, x4, #1
	lsr x0, x0, #63
	ldr x30, [x25, #2040]
	ldr x26, [x25, #2024]
	ldr x27, [x25, #2032]
	ldr x25, [x25, #2016]
	and w24, w24, w0
	cbnz w24, 28f
	b 29f
28:
	add x0, x25, #128
	movz x1, #128, lsl #0
	movz x2, #4, lsl #0
	movz x3, #4, lsl #0
	movz x4, #32768, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #32768, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #256
	movz x1, #128, lsl #0
	movz x2, #4, lsl #0
	movz x3, #4, lsl #0
	movz x4, #33792, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #33792, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #384
	movz x1, #128, lsl #0
	movz x2, #4, lsl #0
	movz x3, #4, lsl #0
	movz x4, #34816, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #34816, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #512
	movz x1, #128, lsl #0
	movz x2, #4, lsl #0
	movz x3, #4, lsl #0
	movz x4, #35840, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #35840, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #640
	movz x1, #128, lsl #0
	movz x2, #4, lsl #0
	movz x3, #4, lsl #0
	movz x4, #36864, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #36864, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #768
	movz x1, #128, lsl #0
	movz x2, #4, lsl #0
	movz x3, #4, lsl #0
	movz x4, #37888, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #37888, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #896
	movz x1, #128, lsl #0
	movz x2, #4, lsl #0
	movz x3, #4, lsl #0
	movz x4, #38912, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #38912, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #1024
	movz x1, #128, lsl #0
	movz x2, #4, lsl #0
	movz x3, #4, lsl #0
	movz x4, #39936, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #39936, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #1152
	movz x1, #128, lsl #0
	movz x2, #4, lsl #0
	movz x3, #4, lsl #0
	movz x4, #40960, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #40960, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #1280
	movz x1, #128, lsl #0
	movz x2, #4, lsl #0
	movz x3, #4, lsl #0
	movz x4, #41984, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #41984, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #1408
	movz x1, #128, lsl #0
	movz x2, #4, lsl #0
	movz x3, #4, lsl #0
	movz x4, #43008, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #43008, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #1536
	movz x1, #416, lsl #0
	movz x2, #4095, lsl #0
	movz x3, #4096, lsl #0
	movz x4, #44032, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #44032, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #1952
	movz x1, #416, lsl #0
	movz x2, #4095, lsl #0
	movz x3, #4096, lsl #0
	movz x4, #45056, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #45056, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #2368
	movz x1, #416, lsl #0
	movz x2, #4095, lsl #0
	movz x3, #4096, lsl #0
	movz x4, #46080, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #2784
	movz x1, #416, lsl #0
	movz x2, #4095, lsl #0
	movz x3, #4096, lsl #0
	movz x4, #47104, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #47104, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #3200
	movz x1, #416, lsl #0
	movz x2, #4095, lsl #0
	movz x3, #4096, lsl #0
	movz x4, #48128, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #48128, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #3616
	movz x1, #416, lsl #0
	movz x2, #4095, lsl #0
	movz x3, #4096, lsl #0
	movz x4, #49152, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #49152, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
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
	movz x2, #0, lsl #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x5, x28, #200
	add x3, x25, #32
	movz x4, #32, lsl #0
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x5, x28, #200
	add x3, x27, #0
	movz x4, #32, lsl #0
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x5, x28, #200
	add x3, x26, #0
	movz x4, #64, lsl #0
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x4, x28, #200
	movz x3, #31, lsl #0
	bl {vg_keccak_pad_scratch}
	movz x2, #0, lsl #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x5, x28, #200
	add x3, x28, #960
	movz x4, #64, lsl #0
	bl {vg_keccak_squeeze_scratch}
	movz x9, #0, lsl #0
	str x9, [x28, #904]
	movz x9, #814, lsl #0
	str x9, [x28, #896]
210:
	ldr x9, [x28, #904]
	add x9, x9, #0
	strb w9, [x28, #1024]
	lsr x9, x9, #8
	strb w9, [x28, #1025]
	add x0, x28, #960
	movz x1, #0, lsl #0
	movk x1, #8, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	movz x2, #16384, lsl #0
	add x2, x28, x2
	add x3, x28, #3072
	str x25, [x3, #2016]
	str x26, [x3, #2024]
	str x27, [x3, #2032]
	str x30, [x3, #2040]
	add x25, x3, #0
	add x26, x2, #0
	add w27, w1, #0
	add x3, x0, #0
	movz x4, #66, lsl #0
	movz x9, #0, lsl #0
	str x9, [x25, #0]
	str x9, [x25, #8]
	str x9, [x25, #16]
	str x9, [x25, #24]
	str x9, [x25, #32]
	str x9, [x25, #40]
	str x9, [x25, #48]
	str x9, [x25, #56]
	str x9, [x25, #64]
	str x9, [x25, #72]
	str x9, [x25, #80]
	str x9, [x25, #88]
	str x9, [x25, #96]
	str x9, [x25, #104]
	str x9, [x25, #112]
	str x9, [x25, #120]
	str x9, [x25, #128]
	str x9, [x25, #136]
	str x9, [x25, #144]
	str x9, [x25, #152]
	str x9, [x25, #160]
	str x9, [x25, #168]
	str x9, [x25, #176]
	str x9, [x25, #184]
	str x9, [x25, #192]
	add x0, x25, #0
	movz x1, #136, lsl #0
	movz x2, #0, lsl #0
	add x5, x25, #200
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	add x0, x25, #0
	movz x1, #136, lsl #0
	movz x3, #31, lsl #0
	add x4, x25, #200
	bl {vg_keccak_pad_scratch}
	add x0, x25, #0
	movz x1, #136, lsl #0
	movz x2, #0, lsl #0
	add x3, x25, #840
	movz x4, #640, lsl #0
	add x5, x25, #200
	bl {vg_keccak_squeeze_scratch}
	lsr x9, x27, #18
	cbz x9, 211f
	add x2, x25, #840
	add x3, x26, #0
	movz x5, #64, lsl #0
	movz x8, #15, lsl #16
	movk x8, #65535, lsl #0
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
213:
	ldr x6, [x2, #0]
	ldrb w7, [x2, #8]
	ldrb w11, [x2, #9]
	and x12, x6, x8
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #0]
	lsr x12, x6, #20
	and x12, x12, x8
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #4]
	lsr x12, x6, #40
	and x12, x12, x8
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #8]
	lsr x12, x6, #60
	lsl x13, x7, #4
	add x12, x12, x13
	lsl x13, x11, #12
	add x12, x12, x13
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #12]
	add x2, x2, #10
	add x3, x3, #16
	sub x5, x5, #1
	cbnz x5, 213b
	b 212f
211:
	add x2, x25, #840
	add x3, x26, #0
	movz x5, #64, lsl #0
	movz x8, #3, lsl #16
	movk x8, #65535, lsl #0
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
214:
	ldr x6, [x2, #0]
	ldrb w7, [x2, #8]
	and x12, x6, x8
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #0]
	lsr x12, x6, #18
	and x12, x12, x8
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #4]
	lsr x12, x6, #36
	and x12, x12, x8
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #8]
	lsr x12, x6, #54
	lsl x13, x7, #10
	add x12, x12, x13
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #12]
	add x2, x2, #9
	add x3, x3, #16
	sub x5, x5, #1
	cbnz x5, 214b
212:
	ldr x30, [x25, #2040]
	ldr x26, [x25, #2024]
	ldr x27, [x25, #2032]
	ldr x25, [x25, #2016]
	movz x0, #21504, lsl #0
	add x0, x28, x0
	movz x1, #16384, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_ntt_positive_from}
	ldr x9, [x28, #904]
	add x9, x9, #1
	strb w9, [x28, #1024]
	lsr x9, x9, #8
	strb w9, [x28, #1025]
	add x0, x28, #960
	movz x1, #0, lsl #0
	movk x1, #8, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	movz x2, #17408, lsl #0
	add x2, x28, x2
	add x3, x28, #3072
	str x25, [x3, #2016]
	str x26, [x3, #2024]
	str x27, [x3, #2032]
	str x30, [x3, #2040]
	add x25, x3, #0
	add x26, x2, #0
	add w27, w1, #0
	add x3, x0, #0
	movz x4, #66, lsl #0
	movz x9, #0, lsl #0
	str x9, [x25, #0]
	str x9, [x25, #8]
	str x9, [x25, #16]
	str x9, [x25, #24]
	str x9, [x25, #32]
	str x9, [x25, #40]
	str x9, [x25, #48]
	str x9, [x25, #56]
	str x9, [x25, #64]
	str x9, [x25, #72]
	str x9, [x25, #80]
	str x9, [x25, #88]
	str x9, [x25, #96]
	str x9, [x25, #104]
	str x9, [x25, #112]
	str x9, [x25, #120]
	str x9, [x25, #128]
	str x9, [x25, #136]
	str x9, [x25, #144]
	str x9, [x25, #152]
	str x9, [x25, #160]
	str x9, [x25, #168]
	str x9, [x25, #176]
	str x9, [x25, #184]
	str x9, [x25, #192]
	add x0, x25, #0
	movz x1, #136, lsl #0
	movz x2, #0, lsl #0
	add x5, x25, #200
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	add x0, x25, #0
	movz x1, #136, lsl #0
	movz x3, #31, lsl #0
	add x4, x25, #200
	bl {vg_keccak_pad_scratch}
	add x0, x25, #0
	movz x1, #136, lsl #0
	movz x2, #0, lsl #0
	add x3, x25, #840
	movz x4, #640, lsl #0
	add x5, x25, #200
	bl {vg_keccak_squeeze_scratch}
	lsr x9, x27, #18
	cbz x9, 215f
	add x2, x25, #840
	add x3, x26, #0
	movz x5, #64, lsl #0
	movz x8, #15, lsl #16
	movk x8, #65535, lsl #0
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
217:
	ldr x6, [x2, #0]
	ldrb w7, [x2, #8]
	ldrb w11, [x2, #9]
	and x12, x6, x8
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #0]
	lsr x12, x6, #20
	and x12, x12, x8
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #4]
	lsr x12, x6, #40
	and x12, x12, x8
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #8]
	lsr x12, x6, #60
	lsl x13, x7, #4
	add x12, x12, x13
	lsl x13, x11, #12
	add x12, x12, x13
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #12]
	add x2, x2, #10
	add x3, x3, #16
	sub x5, x5, #1
	cbnz x5, 217b
	b 216f
215:
	add x2, x25, #840
	add x3, x26, #0
	movz x5, #64, lsl #0
	movz x8, #3, lsl #16
	movk x8, #65535, lsl #0
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
218:
	ldr x6, [x2, #0]
	ldrb w7, [x2, #8]
	and x12, x6, x8
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #0]
	lsr x12, x6, #18
	and x12, x12, x8
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #4]
	lsr x12, x6, #36
	and x12, x12, x8
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #8]
	lsr x12, x6, #54
	lsl x13, x7, #10
	add x12, x12, x13
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #12]
	add x2, x2, #9
	add x3, x3, #16
	sub x5, x5, #1
	cbnz x5, 218b
216:
	ldr x30, [x25, #2040]
	ldr x26, [x25, #2024]
	ldr x27, [x25, #2032]
	ldr x25, [x25, #2016]
	movz x0, #22528, lsl #0
	add x0, x28, x0
	movz x1, #17408, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_ntt_positive_from}
	ldr x9, [x28, #904]
	add x9, x9, #2
	strb w9, [x28, #1024]
	lsr x9, x9, #8
	strb w9, [x28, #1025]
	add x0, x28, #960
	movz x1, #0, lsl #0
	movk x1, #8, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	movz x2, #18432, lsl #0
	add x2, x28, x2
	add x3, x28, #3072
	str x25, [x3, #2016]
	str x26, [x3, #2024]
	str x27, [x3, #2032]
	str x30, [x3, #2040]
	add x25, x3, #0
	add x26, x2, #0
	add w27, w1, #0
	add x3, x0, #0
	movz x4, #66, lsl #0
	movz x9, #0, lsl #0
	str x9, [x25, #0]
	str x9, [x25, #8]
	str x9, [x25, #16]
	str x9, [x25, #24]
	str x9, [x25, #32]
	str x9, [x25, #40]
	str x9, [x25, #48]
	str x9, [x25, #56]
	str x9, [x25, #64]
	str x9, [x25, #72]
	str x9, [x25, #80]
	str x9, [x25, #88]
	str x9, [x25, #96]
	str x9, [x25, #104]
	str x9, [x25, #112]
	str x9, [x25, #120]
	str x9, [x25, #128]
	str x9, [x25, #136]
	str x9, [x25, #144]
	str x9, [x25, #152]
	str x9, [x25, #160]
	str x9, [x25, #168]
	str x9, [x25, #176]
	str x9, [x25, #184]
	str x9, [x25, #192]
	add x0, x25, #0
	movz x1, #136, lsl #0
	movz x2, #0, lsl #0
	add x5, x25, #200
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	add x0, x25, #0
	movz x1, #136, lsl #0
	movz x3, #31, lsl #0
	add x4, x25, #200
	bl {vg_keccak_pad_scratch}
	add x0, x25, #0
	movz x1, #136, lsl #0
	movz x2, #0, lsl #0
	add x3, x25, #840
	movz x4, #640, lsl #0
	add x5, x25, #200
	bl {vg_keccak_squeeze_scratch}
	lsr x9, x27, #18
	cbz x9, 219f
	add x2, x25, #840
	add x3, x26, #0
	movz x5, #64, lsl #0
	movz x8, #15, lsl #16
	movk x8, #65535, lsl #0
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
221:
	ldr x6, [x2, #0]
	ldrb w7, [x2, #8]
	ldrb w11, [x2, #9]
	and x12, x6, x8
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #0]
	lsr x12, x6, #20
	and x12, x12, x8
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #4]
	lsr x12, x6, #40
	and x12, x12, x8
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #8]
	lsr x12, x6, #60
	lsl x13, x7, #4
	add x12, x12, x13
	lsl x13, x11, #12
	add x12, x12, x13
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #12]
	add x2, x2, #10
	add x3, x3, #16
	sub x5, x5, #1
	cbnz x5, 221b
	b 220f
219:
	add x2, x25, #840
	add x3, x26, #0
	movz x5, #64, lsl #0
	movz x8, #3, lsl #16
	movk x8, #65535, lsl #0
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
222:
	ldr x6, [x2, #0]
	ldrb w7, [x2, #8]
	and x12, x6, x8
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #0]
	lsr x12, x6, #18
	and x12, x12, x8
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #4]
	lsr x12, x6, #36
	and x12, x12, x8
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #8]
	lsr x12, x6, #54
	lsl x13, x7, #10
	add x12, x12, x13
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #12]
	add x2, x2, #9
	add x3, x3, #16
	sub x5, x5, #1
	cbnz x5, 222b
220:
	ldr x30, [x25, #2040]
	ldr x26, [x25, #2024]
	ldr x27, [x25, #2032]
	ldr x25, [x25, #2016]
	movz x0, #23552, lsl #0
	add x0, x28, x0
	movz x1, #18432, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_ntt_positive_from}
	ldr x9, [x28, #904]
	add x9, x9, #3
	strb w9, [x28, #1024]
	lsr x9, x9, #8
	strb w9, [x28, #1025]
	add x0, x28, #960
	movz x1, #0, lsl #0
	movk x1, #8, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	movz x2, #19456, lsl #0
	add x2, x28, x2
	add x3, x28, #3072
	str x25, [x3, #2016]
	str x26, [x3, #2024]
	str x27, [x3, #2032]
	str x30, [x3, #2040]
	add x25, x3, #0
	add x26, x2, #0
	add w27, w1, #0
	add x3, x0, #0
	movz x4, #66, lsl #0
	movz x9, #0, lsl #0
	str x9, [x25, #0]
	str x9, [x25, #8]
	str x9, [x25, #16]
	str x9, [x25, #24]
	str x9, [x25, #32]
	str x9, [x25, #40]
	str x9, [x25, #48]
	str x9, [x25, #56]
	str x9, [x25, #64]
	str x9, [x25, #72]
	str x9, [x25, #80]
	str x9, [x25, #88]
	str x9, [x25, #96]
	str x9, [x25, #104]
	str x9, [x25, #112]
	str x9, [x25, #120]
	str x9, [x25, #128]
	str x9, [x25, #136]
	str x9, [x25, #144]
	str x9, [x25, #152]
	str x9, [x25, #160]
	str x9, [x25, #168]
	str x9, [x25, #176]
	str x9, [x25, #184]
	str x9, [x25, #192]
	add x0, x25, #0
	movz x1, #136, lsl #0
	movz x2, #0, lsl #0
	add x5, x25, #200
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	add x0, x25, #0
	movz x1, #136, lsl #0
	movz x3, #31, lsl #0
	add x4, x25, #200
	bl {vg_keccak_pad_scratch}
	add x0, x25, #0
	movz x1, #136, lsl #0
	movz x2, #0, lsl #0
	add x3, x25, #840
	movz x4, #640, lsl #0
	add x5, x25, #200
	bl {vg_keccak_squeeze_scratch}
	lsr x9, x27, #18
	cbz x9, 223f
	add x2, x25, #840
	add x3, x26, #0
	movz x5, #64, lsl #0
	movz x8, #15, lsl #16
	movk x8, #65535, lsl #0
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
225:
	ldr x6, [x2, #0]
	ldrb w7, [x2, #8]
	ldrb w11, [x2, #9]
	and x12, x6, x8
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #0]
	lsr x12, x6, #20
	and x12, x12, x8
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #4]
	lsr x12, x6, #40
	and x12, x12, x8
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #8]
	lsr x12, x6, #60
	lsl x13, x7, #4
	add x12, x12, x13
	lsl x13, x11, #12
	add x12, x12, x13
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #12]
	add x2, x2, #10
	add x3, x3, #16
	sub x5, x5, #1
	cbnz x5, 225b
	b 224f
223:
	add x2, x25, #840
	add x3, x26, #0
	movz x5, #64, lsl #0
	movz x8, #3, lsl #16
	movk x8, #65535, lsl #0
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
226:
	ldr x6, [x2, #0]
	ldrb w7, [x2, #8]
	and x12, x6, x8
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #0]
	lsr x12, x6, #18
	and x12, x12, x8
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #4]
	lsr x12, x6, #36
	and x12, x12, x8
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #8]
	lsr x12, x6, #54
	lsl x13, x7, #10
	add x12, x12, x13
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #12]
	add x2, x2, #9
	add x3, x3, #16
	sub x5, x5, #1
	cbnz x5, 226b
224:
	ldr x30, [x25, #2040]
	ldr x26, [x25, #2024]
	ldr x27, [x25, #2032]
	ldr x25, [x25, #2016]
	movz x0, #24576, lsl #0
	add x0, x28, x0
	movz x1, #19456, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_ntt_positive_from}
	ldr x9, [x28, #904]
	add x9, x9, #4
	strb w9, [x28, #1024]
	lsr x9, x9, #8
	strb w9, [x28, #1025]
	add x0, x28, #960
	movz x1, #0, lsl #0
	movk x1, #8, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	movz x2, #20480, lsl #0
	add x2, x28, x2
	add x3, x28, #3072
	str x25, [x3, #2016]
	str x26, [x3, #2024]
	str x27, [x3, #2032]
	str x30, [x3, #2040]
	add x25, x3, #0
	add x26, x2, #0
	add w27, w1, #0
	add x3, x0, #0
	movz x4, #66, lsl #0
	movz x9, #0, lsl #0
	str x9, [x25, #0]
	str x9, [x25, #8]
	str x9, [x25, #16]
	str x9, [x25, #24]
	str x9, [x25, #32]
	str x9, [x25, #40]
	str x9, [x25, #48]
	str x9, [x25, #56]
	str x9, [x25, #64]
	str x9, [x25, #72]
	str x9, [x25, #80]
	str x9, [x25, #88]
	str x9, [x25, #96]
	str x9, [x25, #104]
	str x9, [x25, #112]
	str x9, [x25, #120]
	str x9, [x25, #128]
	str x9, [x25, #136]
	str x9, [x25, #144]
	str x9, [x25, #152]
	str x9, [x25, #160]
	str x9, [x25, #168]
	str x9, [x25, #176]
	str x9, [x25, #184]
	str x9, [x25, #192]
	add x0, x25, #0
	movz x1, #136, lsl #0
	movz x2, #0, lsl #0
	add x5, x25, #200
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	add x0, x25, #0
	movz x1, #136, lsl #0
	movz x3, #31, lsl #0
	add x4, x25, #200
	bl {vg_keccak_pad_scratch}
	add x0, x25, #0
	movz x1, #136, lsl #0
	movz x2, #0, lsl #0
	add x3, x25, #840
	movz x4, #640, lsl #0
	add x5, x25, #200
	bl {vg_keccak_squeeze_scratch}
	lsr x9, x27, #18
	cbz x9, 227f
	add x2, x25, #840
	add x3, x26, #0
	movz x5, #64, lsl #0
	movz x8, #15, lsl #16
	movk x8, #65535, lsl #0
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
229:
	ldr x6, [x2, #0]
	ldrb w7, [x2, #8]
	ldrb w11, [x2, #9]
	and x12, x6, x8
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #0]
	lsr x12, x6, #20
	and x12, x12, x8
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #4]
	lsr x12, x6, #40
	and x12, x12, x8
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #8]
	lsr x12, x6, #60
	lsl x13, x7, #4
	add x12, x12, x13
	lsl x13, x11, #12
	add x12, x12, x13
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #12]
	add x2, x2, #10
	add x3, x3, #16
	sub x5, x5, #1
	cbnz x5, 229b
	b 228f
227:
	add x2, x25, #840
	add x3, x26, #0
	movz x5, #64, lsl #0
	movz x8, #3, lsl #16
	movk x8, #65535, lsl #0
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
230:
	ldr x6, [x2, #0]
	ldrb w7, [x2, #8]
	and x12, x6, x8
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #0]
	lsr x12, x6, #18
	and x12, x12, x8
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #4]
	lsr x12, x6, #36
	and x12, x12, x8
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #8]
	lsr x12, x6, #54
	lsl x13, x7, #10
	add x12, x12, x13
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #12]
	add x2, x2, #9
	add x3, x3, #16
	sub x5, x5, #1
	cbnz x5, 230b
228:
	ldr x30, [x25, #2040]
	ldr x26, [x25, #2024]
	ldr x27, [x25, #2032]
	ldr x25, [x25, #2016]
	movz x0, #25600, lsl #0
	add x0, x28, x0
	movz x1, #20480, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_ntt_positive_from}
	movz x0, #26624, lsl #0
	add x0, x28, x0
	movz x1, #50176, lsl #0
	add x1, x28, x1
	movz x2, #21504, lsl #0
	add x2, x28, x2
	add x3, x28, #3072
	bl {vg_mldsa_dot_inverse5}
	movz x0, #27648, lsl #0
	add x0, x28, x0
	movz x1, #55296, lsl #0
	add x1, x28, x1
	movz x2, #21504, lsl #0
	add x2, x28, x2
	add x3, x28, #3072
	bl {vg_mldsa_dot_inverse5}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	movz x1, #60416, lsl #0
	add x1, x28, x1
	movz x2, #21504, lsl #0
	add x2, x28, x2
	add x3, x28, #3072
	bl {vg_mldsa_dot_inverse5}
	movz x0, #29696, lsl #0
	add x0, x28, x0
	movz x1, #0, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	movz x2, #21504, lsl #0
	add x2, x28, x2
	add x3, x28, #3072
	bl {vg_mldsa_dot_inverse5}
	movz x0, #30720, lsl #0
	add x0, x28, x0
	movz x1, #5120, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	movz x2, #21504, lsl #0
	add x2, x28, x2
	add x3, x28, #3072
	bl {vg_mldsa_dot_inverse5}
	movz x0, #31744, lsl #0
	add x0, x28, x0
	movz x1, #10240, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	movz x2, #21504, lsl #0
	add x2, x28, x2
	add x3, x28, #3072
	bl {vg_mldsa_dot_inverse5}
	movz x0, #26624, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_high_pack4}
	movz x0, #27648, lsl #0
	add x0, x28, x0
	add x1, x28, #2176
	bl {vg_mldsa_high_pack4}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	add x1, x28, #2304
	bl {vg_mldsa_high_pack4}
	movz x0, #29696, lsl #0
	add x0, x28, x0
	add x1, x28, #2432
	bl {vg_mldsa_high_pack4}
	movz x0, #30720, lsl #0
	add x0, x28, x0
	add x1, x28, #2560
	bl {vg_mldsa_high_pack4}
	movz x0, #31744, lsl #0
	add x0, x28, x0
	add x1, x28, #2688
	bl {vg_mldsa_high_pack4}
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
	movz x2, #0, lsl #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x5, x28, #200
	add x3, x26, #0
	movz x4, #64, lsl #0
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x5, x28, #200
	add x3, x28, #2048
	movz x4, #768, lsl #0
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x4, x28, #200
	movz x3, #31, lsl #0
	bl {vg_keccak_pad_scratch}
	movz x2, #0, lsl #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x5, x28, #200
	add x3, x28, #1040
	movz x4, #48, lsl #0
	bl {vg_keccak_squeeze_scratch}
	add x0, x28, #1040
	movz x1, #48, lsl #0
	movz x2, #49, lsl #0
	movz x3, #5120, lsl #0
	add x3, x28, x3
	add x4, x28, #3072
	bl {vg_mldsa_sample_in_ball}
	cbnz w0, 231f
	movz x24, #0, lsl #0
	movz x9, #1, lsl #0
	str x9, [x28, #896]
	b 232f
231:
	movz x0, #5120, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	movz x24, #1, lsl #0
	movz x9, #0, lsl #0
	str x9, [x28, #912]
	movz x0, #5120, lsl #0
	add x0, x28, x0
	movz x1, #32768, lsl #0
	add x1, x28, x1
	movz x2, #16384, lsl #0
	add x2, x28, x2
	movz x3, #6144, lsl #0
	add x3, x28, x3
	movz x4, #6144, lsl #0
	add x4, x28, x4
	movz x5, #0, lsl #0
	movk x5, #8, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #65340, lsl #0
	movk x6, #7, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	bl {vg_mldsa_fused_pair_z}
	and w24, w24, w0
	cbnz w24, 233f
	b 234f
233:
	movz x0, #5120, lsl #0
	add x0, x28, x0
	movz x1, #34816, lsl #0
	add x1, x28, x1
	movz x2, #18432, lsl #0
	add x2, x28, x2
	movz x3, #6144, lsl #0
	add x3, x28, x3
	movz x4, #6144, lsl #0
	add x4, x28, x4
	movz x5, #0, lsl #0
	movk x5, #8, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #65340, lsl #0
	movk x6, #7, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	bl {vg_mldsa_fused_pair_z}
	and w24, w24, w0
	cbnz w24, 235f
	b 236f
235:
	movz x0, #6144, lsl #0
	add x0, x28, x0
	movz x1, #5120, lsl #0
	add x1, x28, x1
	movz x2, #36864, lsl #0
	add x2, x28, x2
	add x3, x28, #3072
	bl {vg_mldsa_multiply_inverse_raw}
	movz x0, #20480, lsl #0
	add x0, x28, x0
	movz x1, #6144, lsl #0
	add x1, x28, x1
	movz x2, #65340, lsl #0
	movk x2, #7, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	bl {vg_mldsa_signed_add_norm}
	and w24, w24, w0
236:
234:
	cbnz w24, 237f
	ldr x9, [x28, #904]
	add x9, x9, #5
	str x9, [x28, #904]
	b 238f
237:
	movz x0, #5120, lsl #0
	add x0, x28, x0
	movz x1, #37888, lsl #0
	add x1, x28, x1
	movz x2, #26624, lsl #0
	add x2, x28, x2
	movz x3, #10240, lsl #0
	add x3, x28, x3
	movz x4, #6144, lsl #0
	add x4, x28, x4
	movz x5, #65280, lsl #0
	movk x5, #3, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #65084, lsl #0
	movk x6, #3, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	bl {vg_mldsa_fused_pair_r0}
	and w24, w24, w0
	cbnz w24, 239f
	b 240f
239:
	movz x0, #5120, lsl #0
	add x0, x28, x0
	movz x1, #39936, lsl #0
	add x1, x28, x1
	movz x2, #28672, lsl #0
	add x2, x28, x2
	movz x3, #12288, lsl #0
	add x3, x28, x3
	movz x4, #6144, lsl #0
	add x4, x28, x4
	movz x5, #65280, lsl #0
	movk x5, #3, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #65084, lsl #0
	movk x6, #3, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	bl {vg_mldsa_fused_pair_r0}
	and w24, w24, w0
	cbnz w24, 241f
	b 242f
241:
	movz x0, #5120, lsl #0
	add x0, x28, x0
	movz x1, #41984, lsl #0
	add x1, x28, x1
	movz x2, #30720, lsl #0
	add x2, x28, x2
	movz x3, #14336, lsl #0
	add x3, x28, x3
	movz x4, #6144, lsl #0
	add x4, x28, x4
	movz x5, #65280, lsl #0
	movk x5, #3, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #65084, lsl #0
	movk x6, #3, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	bl {vg_mldsa_fused_pair_r0}
	and w24, w24, w0
	cbnz w24, 243f
	b 244f
243:
244:
242:
240:
	cbnz w24, 245f
	ldr x9, [x28, #904]
	add x9, x9, #5
	str x9, [x28, #904]
	b 246f
245:
	movz x0, #5120, lsl #0
	add x0, x28, x0
	movz x1, #44032, lsl #0
	add x1, x28, x1
	movz x2, #10240, lsl #0
	add x2, x28, x2
	movz x3, #26624, lsl #0
	add x3, x28, x3
	movz x4, #6144, lsl #0
	add x4, x28, x4
	movz x5, #65280, lsl #0
	movk x5, #3, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #65280, lsl #0
	movk x6, #3, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	bl {vg_mldsa_fused_pair_h}
	ldr x9, [x28, #912]
	add w9, w9, w0
	str x9, [x28, #912]
	lsr x0, x0, #32
	and w24, w24, w0
	movz x0, #5120, lsl #0
	add x0, x28, x0
	movz x1, #46080, lsl #0
	add x1, x28, x1
	movz x2, #12288, lsl #0
	add x2, x28, x2
	movz x3, #28672, lsl #0
	add x3, x28, x3
	movz x4, #6144, lsl #0
	add x4, x28, x4
	movz x5, #65280, lsl #0
	movk x5, #3, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #65280, lsl #0
	movk x6, #3, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	bl {vg_mldsa_fused_pair_h}
	ldr x9, [x28, #912]
	add w9, w9, w0
	str x9, [x28, #912]
	lsr x0, x0, #32
	and w24, w24, w0
	movz x0, #5120, lsl #0
	add x0, x28, x0
	movz x1, #48128, lsl #0
	add x1, x28, x1
	movz x2, #14336, lsl #0
	add x2, x28, x2
	movz x3, #30720, lsl #0
	add x3, x28, x3
	movz x4, #6144, lsl #0
	add x4, x28, x4
	movz x5, #65280, lsl #0
	movk x5, #3, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #65280, lsl #0
	movk x6, #3, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	bl {vg_mldsa_fused_pair_h}
	ldr x9, [x28, #912]
	add w9, w9, w0
	str x9, [x28, #912]
	lsr x0, x0, #32
	and w24, w24, w0
	ldr x9, [x28, #912]
	sub x9, x9, #56
	lsr x9, x9, #63
	and w24, w24, w9
	cbnz w24, 247f
	ldr x9, [x28, #904]
	add x9, x9, #5
	str x9, [x28, #904]
	b 248f
247:
	movz x9, #1, lsl #0
	str x9, [x28, #896]
248:
246:
238:
232:
	ldr x9, [x28, #896]
	sub x9, x9, #1
	str x9, [x28, #896]
	cbnz x9, 210b
	cbnz w24, 249f
	b 250f
249:
	movz x0, #16384, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_canonicalize_signed}
	movz x0, #17408, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_canonicalize_signed}
	movz x0, #18432, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_canonicalize_signed}
	movz x0, #19456, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_canonicalize_signed}
	movz x0, #20480, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_canonicalize_signed}
	add x0, x23, #0
	add x1, x28, #1040
	movz x2, #48, lsl #0
251:
	ldrb w9, [x1, #0]
	strb w9, [x0, #0]
	add x0, x0, #1
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 251b
	movz x0, #16384, lsl #0
	add x0, x28, x0
	movz x1, #65535, lsl #0
	movk x1, #7, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	movz x2, #0, lsl #0
	movk x2, #8, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x3, x23, #48
	movz x4, #640, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #17408, lsl #0
	add x0, x28, x0
	movz x1, #65535, lsl #0
	movk x1, #7, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	movz x2, #0, lsl #0
	movk x2, #8, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x3, x23, #688
	movz x4, #640, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #18432, lsl #0
	add x0, x28, x0
	movz x1, #65535, lsl #0
	movk x1, #7, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	movz x2, #0, lsl #0
	movk x2, #8, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x3, x23, #1328
	movz x4, #640, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #19456, lsl #0
	add x0, x28, x0
	movz x1, #65535, lsl #0
	movk x1, #7, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	movz x2, #0, lsl #0
	movk x2, #8, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x3, x23, #1968
	movz x4, #640, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #20480, lsl #0
	add x0, x28, x0
	movz x1, #65535, lsl #0
	movk x1, #7, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	movz x2, #0, lsl #0
	movk x2, #8, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x3, x23, #2608
	movz x4, #640, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #10240, lsl #0
	add x0, x28, x0
	movz x1, #1536, lsl #0
	movz x2, #55, lsl #0
	add x3, x23, #3248
	movz x4, #61, lsl #0
	bl {vg_mldsa_hint_bit_pack}
250:
29:
	add x0, x24, #0
	ldr x23, [x28, #840]
	ldr x24, [x28, #848]
	ldr x25, [x28, #856]
	ldr x26, [x28, #864]
	ldr x27, [x28, #872]
	ldr x30, [x28, #880]
	ldr x28, [x28, #888]
	ret
	.p2align 6

vg_mldsa65_sign_message:
	lsr x9, x4, #8
	cbnz x9, 20f
	movz x9, #37888, lsl #0
	movk x9, #1, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	add x9, x7, x9
	str x28, [x9, #904]
	str x30, [x9, #912]
	add x28, x9, #0
	str x0, [x28, #920]
	str x1, [x28, #928]
	str x2, [x28, #936]
	str x3, [x28, #944]
	str x4, [x28, #952]
	str x5, [x28, #960]
	str x6, [x28, #968]
	str x7, [x28, #976]
	movz x9, #0, lsl #0
	strb w9, [x28, #984]
	strb w4, [x28, #985]
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
	movz x2, #0, lsl #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	ldr x3, [x28, #920]
	add x3, x3, #64
	movz x4, #64, lsl #0
	add x5, x28, #200
	bl {vg_keccak_absorb_scratch}
	movz x2, #64, lsl #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x3, x28, #984
	movz x4, #2, lsl #0
	add x5, x28, #200
	bl {vg_keccak_absorb_scratch}
	movz x2, #66, lsl #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	ldr x3, [x28, #944]
	ldr x4, [x28, #952]
	add x5, x28, #200
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	ldr x3, [x28, #928]
	ldr x4, [x28, #936]
	add x5, x28, #200
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	movz x3, #31, lsl #0
	add x4, x28, #200
	bl {vg_keccak_pad_scratch}
	add x0, x28, #0
	movz x1, #136, lsl #0
	movz x2, #0, lsl #0
	add x3, x28, #840
	movz x4, #64, lsl #0
	add x5, x28, #200
	bl {vg_keccak_squeeze_scratch}
	ldr x0, [x28, #920]
	add x1, x28, #840
	ldr x2, [x28, #960]
	ldr x3, [x28, #968]
	ldr x4, [x28, #976]
	bl {vg_mldsa65_sign}
	ldr x30, [x28, #912]
	ldr x28, [x28, #904]
	b 21f
20:
	movz x0, #2, lsl #0
21:
	ret
	.p2align 6

vg_mldsa65_verify:
	str x24, [x3, #840]
	str x25, [x3, #848]
	str x26, [x3, #856]
	str x27, [x3, #864]
	str x28, [x3, #872]
	str x30, [x3, #880]
	add x25, x0, #0
	add x26, x1, #0
	add x27, x2, #0
	add x28, x3, #0
	movz x24, #1, lsl #0
	add x0, x27, #3248
	movz x1, #61, lsl #0
	movz x2, #55, lsl #0
	movz x3, #35840, lsl #0
	add x3, x28, x3
	movz x4, #1536, lsl #0
	bl {vg_mldsa_hint_bit_unpack}
	and w24, w24, w0
	cbnz x24, 20f
	b 21f
20:
	add x0, x27, #48
	movz x1, #640, lsl #0
	movz x2, #65535, lsl #0
	movk x2, #7, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	movz x3, #0, lsl #0
	movk x3, #8, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	movz x4, #41984, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #41984, lsl #0
	add x0, x28, x0
	movz x1, #65340, lsl #0
	movk x1, #7, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	bl {vg_mldsa_norm_lt}
	and w24, w24, w0
	add x0, x27, #688
	movz x1, #640, lsl #0
	movz x2, #65535, lsl #0
	movk x2, #7, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	movz x3, #0, lsl #0
	movk x3, #8, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	movz x4, #43008, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #43008, lsl #0
	add x0, x28, x0
	movz x1, #65340, lsl #0
	movk x1, #7, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	bl {vg_mldsa_norm_lt}
	and w24, w24, w0
	add x0, x27, #1328
	movz x1, #640, lsl #0
	movz x2, #65535, lsl #0
	movk x2, #7, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	movz x3, #0, lsl #0
	movk x3, #8, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	movz x4, #44032, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #44032, lsl #0
	add x0, x28, x0
	movz x1, #65340, lsl #0
	movk x1, #7, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	bl {vg_mldsa_norm_lt}
	and w24, w24, w0
	add x0, x27, #1968
	movz x1, #640, lsl #0
	movz x2, #65535, lsl #0
	movk x2, #7, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	movz x3, #0, lsl #0
	movk x3, #8, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	movz x4, #45056, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #45056, lsl #0
	add x0, x28, x0
	movz x1, #65340, lsl #0
	movk x1, #7, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	bl {vg_mldsa_norm_lt}
	and w24, w24, w0
	add x0, x27, #2608
	movz x1, #640, lsl #0
	movz x2, #65535, lsl #0
	movk x2, #7, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	movz x3, #0, lsl #0
	movk x3, #8, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	movz x4, #46080, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #65340, lsl #0
	movk x1, #7, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	bl {vg_mldsa_norm_lt}
	and w24, w24, w0
	cbnz x24, 22f
	b 23f
22:
	ldr x9, [x25, #0]
	str x9, [x28, #1152]
	ldr x9, [x25, #8]
	str x9, [x28, #1160]
	ldr x9, [x25, #16]
	str x9, [x28, #1168]
	ldr x9, [x25, #24]
	str x9, [x28, #1176]
	add x10, x28, #1408
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #0, lsl #0
	strb w9, [x28, #1440]
	movz x9, #0, lsl #0
	strb w9, [x28, #1441]
	add x10, x28, #1442
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #1, lsl #0
	strb w9, [x28, #1474]
	movz x9, #0, lsl #0
	strb w9, [x28, #1475]
	add x10, x28, #1476
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #2, lsl #0
	strb w9, [x28, #1508]
	movz x9, #0, lsl #0
	strb w9, [x28, #1509]
	add x10, x28, #1510
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #3, lsl #0
	strb w9, [x28, #1542]
	movz x9, #0, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #4096, lsl #0
	add x1, x28, x1
	movz x2, #49152, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	movz x1, #4096, lsl #0
	add x1, x28, x1
	movz x2, #1024, lsl #0
24:
	ldr w9, [x1, #0]
	and w9, w9, w8
	str w9, [x1, #0]
	add x1, x1, #4
	sub x2, x2, #1
	cbnz x2, 24b
	add x10, x28, #1408
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #4, lsl #0
	strb w9, [x28, #1440]
	movz x9, #0, lsl #0
	strb w9, [x28, #1441]
	add x10, x28, #1442
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #0, lsl #0
	strb w9, [x28, #1474]
	movz x9, #1, lsl #0
	strb w9, [x28, #1475]
	add x10, x28, #1476
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #1, lsl #0
	strb w9, [x28, #1508]
	movz x9, #1, lsl #0
	strb w9, [x28, #1509]
	add x10, x28, #1510
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #2, lsl #0
	strb w9, [x28, #1542]
	movz x9, #1, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #8192, lsl #0
	add x1, x28, x1
	movz x2, #49152, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	movz x1, #8192, lsl #0
	add x1, x28, x1
	movz x2, #1024, lsl #0
25:
	ldr w9, [x1, #0]
	and w9, w9, w8
	str w9, [x1, #0]
	add x1, x1, #4
	sub x2, x2, #1
	cbnz x2, 25b
	add x10, x28, #1408
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #3, lsl #0
	strb w9, [x28, #1440]
	movz x9, #1, lsl #0
	strb w9, [x28, #1441]
	add x10, x28, #1442
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #4, lsl #0
	strb w9, [x28, #1474]
	movz x9, #1, lsl #0
	strb w9, [x28, #1475]
	add x10, x28, #1476
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #0, lsl #0
	strb w9, [x28, #1508]
	movz x9, #2, lsl #0
	strb w9, [x28, #1509]
	add x10, x28, #1510
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #1, lsl #0
	strb w9, [x28, #1542]
	movz x9, #2, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #12288, lsl #0
	add x1, x28, x1
	movz x2, #49152, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	movz x1, #12288, lsl #0
	add x1, x28, x1
	movz x2, #1024, lsl #0
26:
	ldr w9, [x1, #0]
	and w9, w9, w8
	str w9, [x1, #0]
	add x1, x1, #4
	sub x2, x2, #1
	cbnz x2, 26b
	add x10, x28, #1408
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #2, lsl #0
	strb w9, [x28, #1440]
	movz x9, #2, lsl #0
	strb w9, [x28, #1441]
	add x10, x28, #1442
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #3, lsl #0
	strb w9, [x28, #1474]
	movz x9, #2, lsl #0
	strb w9, [x28, #1475]
	add x10, x28, #1476
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #4, lsl #0
	strb w9, [x28, #1508]
	movz x9, #2, lsl #0
	strb w9, [x28, #1509]
	add x10, x28, #1510
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #0, lsl #0
	strb w9, [x28, #1542]
	movz x9, #3, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #16384, lsl #0
	add x1, x28, x1
	movz x2, #49152, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	movz x1, #16384, lsl #0
	add x1, x28, x1
	movz x2, #1024, lsl #0
27:
	ldr w9, [x1, #0]
	and w9, w9, w8
	str w9, [x1, #0]
	add x1, x1, #4
	sub x2, x2, #1
	cbnz x2, 27b
	add x10, x28, #1408
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #1, lsl #0
	strb w9, [x28, #1440]
	movz x9, #3, lsl #0
	strb w9, [x28, #1441]
	add x10, x28, #1442
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #2, lsl #0
	strb w9, [x28, #1474]
	movz x9, #3, lsl #0
	strb w9, [x28, #1475]
	add x10, x28, #1476
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #3, lsl #0
	strb w9, [x28, #1508]
	movz x9, #3, lsl #0
	strb w9, [x28, #1509]
	add x10, x28, #1510
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #4, lsl #0
	strb w9, [x28, #1542]
	movz x9, #3, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #20480, lsl #0
	add x1, x28, x1
	movz x2, #49152, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	movz x1, #20480, lsl #0
	add x1, x28, x1
	movz x2, #1024, lsl #0
28:
	ldr w9, [x1, #0]
	and w9, w9, w8
	str w9, [x1, #0]
	add x1, x1, #4
	sub x2, x2, #1
	cbnz x2, 28b
	add x10, x28, #1408
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #0, lsl #0
	strb w9, [x28, #1440]
	movz x9, #4, lsl #0
	strb w9, [x28, #1441]
	add x10, x28, #1442
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #1, lsl #0
	strb w9, [x28, #1474]
	movz x9, #4, lsl #0
	strb w9, [x28, #1475]
	add x10, x28, #1476
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #2, lsl #0
	strb w9, [x28, #1508]
	movz x9, #4, lsl #0
	strb w9, [x28, #1509]
	add x10, x28, #1510
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #3, lsl #0
	strb w9, [x28, #1542]
	movz x9, #4, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #24576, lsl #0
	add x1, x28, x1
	movz x2, #49152, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	movz x1, #24576, lsl #0
	add x1, x28, x1
	movz x2, #1024, lsl #0
29:
	ldr w9, [x1, #0]
	and w9, w9, w8
	str w9, [x1, #0]
	add x1, x1, #4
	sub x2, x2, #1
	cbnz x2, 29b
	add x10, x28, #1408
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #4, lsl #0
	strb w9, [x28, #1440]
	movz x9, #4, lsl #0
	strb w9, [x28, #1441]
	add x10, x28, #1442
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #0, lsl #0
	strb w9, [x28, #1474]
	movz x9, #5, lsl #0
	strb w9, [x28, #1475]
	add x10, x28, #1476
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #1, lsl #0
	strb w9, [x28, #1508]
	movz x9, #5, lsl #0
	strb w9, [x28, #1509]
	add x10, x28, #1510
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #2, lsl #0
	strb w9, [x28, #1542]
	movz x9, #5, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #28672, lsl #0
	add x1, x28, x1
	movz x2, #49152, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	movz x1, #28672, lsl #0
	add x1, x28, x1
	movz x2, #1024, lsl #0
210:
	ldr w9, [x1, #0]
	and w9, w9, w8
	str w9, [x1, #0]
	add x1, x1, #4
	sub x2, x2, #1
	cbnz x2, 210b
	movz x9, #3, lsl #0
	strb w9, [x28, #1184]
	movz x9, #5, lsl #0
	strb w9, [x28, #1185]
	add x0, x28, #1152
	movz x1, #32768, lsl #0
	add x1, x28, x1
	add x2, x28, #2048
	str x25, [x2, #2016]
	str x26, [x2, #2024]
	str x27, [x2, #2032]
	str x30, [x2, #2040]
	add x25, x2, #0
	add x26, x1, #0
	movz x27, #0, lsl #0
	add x3, x0, #0
	movz x4, #34, lsl #0
	movz x9, #0, lsl #0
	str x9, [x25, #0]
	str x9, [x25, #8]
	str x9, [x25, #16]
	str x9, [x25, #24]
	str x9, [x25, #32]
	str x9, [x25, #40]
	str x9, [x25, #48]
	str x9, [x25, #56]
	str x9, [x25, #64]
	str x9, [x25, #72]
	str x9, [x25, #80]
	str x9, [x25, #88]
	str x9, [x25, #96]
	str x9, [x25, #104]
	str x9, [x25, #112]
	str x9, [x25, #120]
	str x9, [x25, #128]
	str x9, [x25, #136]
	str x9, [x25, #144]
	str x9, [x25, #152]
	str x9, [x25, #160]
	str x9, [x25, #168]
	str x9, [x25, #176]
	str x9, [x25, #184]
	str x9, [x25, #192]
	add x0, x25, #0
	movz x1, #168, lsl #0
	movz x2, #0, lsl #0
	add x5, x25, #200
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	add x0, x25, #0
	movz x1, #168, lsl #0
	movz x3, #31, lsl #0
	add x4, x25, #200
	bl {vg_keccak_pad_scratch}
	add x0, x25, #0
	movz x1, #168, lsl #0
	movz x2, #0, lsl #0
	add x3, x25, #840
	movz x4, #1008, lsl #0
	add x5, x25, #200
	bl {vg_keccak_squeeze_scratch}
	movz x9, #0, lsl #0
	add x3, x26, #0
	movz x4, #256, lsl #0
211:
	str w9, [x3, #0]
	add x3, x3, #4
	sub x4, x4, #1
	cbnz x4, 211b
	add x2, x25, #840
	add x3, x26, #0
	movz x4, #256, lsl #0
	movz x5, #336, lsl #0
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
	movz x10, #127, lsl #0
212:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x8, x8, x10
	lsl x8, x8, #16
	lsl x7, x7, #8
	add x11, x6, x7
	add x11, x11, x8
	cbz x4, 213f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	b 214f
213:
214:
	cbnz x5, 212b
	sub x0, x4, #1
	lsr x0, x0, #63
	ldr x30, [x25, #2040]
	ldr x26, [x25, #2024]
	ldr x27, [x25, #2032]
	ldr x25, [x25, #2016]
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	movz x1, #32768, lsl #0
	add x1, x28, x1
	movz x2, #256, lsl #0
215:
	ldr w9, [x1, #0]
	and w9, w9, w8
	str w9, [x1, #0]
	add x1, x1, #4
	sub x2, x2, #1
	cbnz x2, 215b
	movz x9, #4, lsl #0
	strb w9, [x28, #1184]
	movz x9, #5, lsl #0
	strb w9, [x28, #1185]
	add x0, x28, #1152
	movz x1, #33792, lsl #0
	add x1, x28, x1
	add x2, x28, #2048
	str x25, [x2, #2016]
	str x26, [x2, #2024]
	str x27, [x2, #2032]
	str x30, [x2, #2040]
	add x25, x2, #0
	add x26, x1, #0
	movz x27, #0, lsl #0
	add x3, x0, #0
	movz x4, #34, lsl #0
	movz x9, #0, lsl #0
	str x9, [x25, #0]
	str x9, [x25, #8]
	str x9, [x25, #16]
	str x9, [x25, #24]
	str x9, [x25, #32]
	str x9, [x25, #40]
	str x9, [x25, #48]
	str x9, [x25, #56]
	str x9, [x25, #64]
	str x9, [x25, #72]
	str x9, [x25, #80]
	str x9, [x25, #88]
	str x9, [x25, #96]
	str x9, [x25, #104]
	str x9, [x25, #112]
	str x9, [x25, #120]
	str x9, [x25, #128]
	str x9, [x25, #136]
	str x9, [x25, #144]
	str x9, [x25, #152]
	str x9, [x25, #160]
	str x9, [x25, #168]
	str x9, [x25, #176]
	str x9, [x25, #184]
	str x9, [x25, #192]
	add x0, x25, #0
	movz x1, #168, lsl #0
	movz x2, #0, lsl #0
	add x5, x25, #200
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	add x0, x25, #0
	movz x1, #168, lsl #0
	movz x3, #31, lsl #0
	add x4, x25, #200
	bl {vg_keccak_pad_scratch}
	add x0, x25, #0
	movz x1, #168, lsl #0
	movz x2, #0, lsl #0
	add x3, x25, #840
	movz x4, #1008, lsl #0
	add x5, x25, #200
	bl {vg_keccak_squeeze_scratch}
	movz x9, #0, lsl #0
	add x3, x26, #0
	movz x4, #256, lsl #0
216:
	str w9, [x3, #0]
	add x3, x3, #4
	sub x4, x4, #1
	cbnz x4, 216b
	add x2, x25, #840
	add x3, x26, #0
	movz x4, #256, lsl #0
	movz x5, #336, lsl #0
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
	movz x10, #127, lsl #0
217:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x8, x8, x10
	lsl x8, x8, #16
	lsl x7, x7, #8
	add x11, x6, x7
	add x11, x11, x8
	cbz x4, 218f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	b 219f
218:
219:
	cbnz x5, 217b
	sub x0, x4, #1
	lsr x0, x0, #63
	ldr x30, [x25, #2040]
	ldr x26, [x25, #2024]
	ldr x27, [x25, #2032]
	ldr x25, [x25, #2016]
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	movz x1, #33792, lsl #0
	add x1, x28, x1
	movz x2, #256, lsl #0
220:
	ldr w9, [x1, #0]
	and w9, w9, w8
	str w9, [x1, #0]
	add x1, x1, #4
	sub x2, x2, #1
	cbnz x2, 220b
	add x0, x27, #0
	movz x1, #48, lsl #0
	movz x2, #49, lsl #0
	movz x3, #47104, lsl #0
	add x3, x28, x3
	add x4, x28, #2048
	bl {vg_mldsa_sample_in_ball}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	movz x1, #47104, lsl #0
	add x1, x28, x1
	movz x2, #256, lsl #0
221:
	ldr w9, [x1, #0]
	and w9, w9, w8
	str w9, [x1, #0]
	add x1, x1, #4
	sub x2, x2, #1
	cbnz x2, 221b
	movz x0, #41984, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_ntt}
	movz x0, #43008, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_ntt}
	movz x0, #44032, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_ntt}
	movz x0, #45056, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_ntt}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_ntt}
	movz x0, #47104, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_ntt}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #4096, lsl #0
	add x1, x28, x1
	movz x2, #41984, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_ntt}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #5120, lsl #0
	add x1, x28, x1
	movz x2, #43008, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #6144, lsl #0
	add x1, x28, x1
	movz x2, #44032, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #7168, lsl #0
	add x1, x28, x1
	movz x2, #45056, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #8192, lsl #0
	add x1, x28, x1
	movz x2, #46080, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	add x0, x25, #32
	movz x1, #48128, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_unpack_t1}
	movz x0, #48128, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_ntt}
	movz x0, #49152, lsl #0
	add x0, x28, x0
	movz x1, #47104, lsl #0
	add x1, x28, x1
	movz x2, #48128, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_ntt}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #49152, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_sub}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_inv_ntt}
	movz x0, #35840, lsl #0
	add x0, x28, x0
	movz x1, #50176, lsl #0
	add x1, x28, x1
	movz x2, #65280, lsl #0
	movk x2, #3, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	movz x3, #51200, lsl #0
	add x3, x28, x3
	bl {vg_mldsa_use_hint}
	movz x0, #51200, lsl #0
	add x0, x28, x0
	movz x1, #15, lsl #0
	movz x2, #34816, lsl #0
	add x2, x28, x2
	movz x3, #128, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #9216, lsl #0
	add x1, x28, x1
	movz x2, #41984, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_ntt}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #10240, lsl #0
	add x1, x28, x1
	movz x2, #43008, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #11264, lsl #0
	add x1, x28, x1
	movz x2, #44032, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #12288, lsl #0
	add x1, x28, x1
	movz x2, #45056, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #13312, lsl #0
	add x1, x28, x1
	movz x2, #46080, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	add x0, x25, #352
	movz x1, #48128, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_unpack_t1}
	movz x0, #48128, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_ntt}
	movz x0, #49152, lsl #0
	add x0, x28, x0
	movz x1, #47104, lsl #0
	add x1, x28, x1
	movz x2, #48128, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_ntt}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #49152, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_sub}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_inv_ntt}
	movz x0, #36864, lsl #0
	add x0, x28, x0
	movz x1, #50176, lsl #0
	add x1, x28, x1
	movz x2, #65280, lsl #0
	movk x2, #3, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	movz x3, #51200, lsl #0
	add x3, x28, x3
	bl {vg_mldsa_use_hint}
	movz x0, #51200, lsl #0
	add x0, x28, x0
	movz x1, #15, lsl #0
	movz x2, #34944, lsl #0
	add x2, x28, x2
	movz x3, #128, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #14336, lsl #0
	add x1, x28, x1
	movz x2, #41984, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_ntt}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #15360, lsl #0
	add x1, x28, x1
	movz x2, #43008, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #16384, lsl #0
	add x1, x28, x1
	movz x2, #44032, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #17408, lsl #0
	add x1, x28, x1
	movz x2, #45056, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #18432, lsl #0
	add x1, x28, x1
	movz x2, #46080, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	add x0, x25, #672
	movz x1, #48128, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_unpack_t1}
	movz x0, #48128, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_ntt}
	movz x0, #49152, lsl #0
	add x0, x28, x0
	movz x1, #47104, lsl #0
	add x1, x28, x1
	movz x2, #48128, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_ntt}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #49152, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_sub}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_inv_ntt}
	movz x0, #37888, lsl #0
	add x0, x28, x0
	movz x1, #50176, lsl #0
	add x1, x28, x1
	movz x2, #65280, lsl #0
	movk x2, #3, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	movz x3, #51200, lsl #0
	add x3, x28, x3
	bl {vg_mldsa_use_hint}
	movz x0, #51200, lsl #0
	add x0, x28, x0
	movz x1, #15, lsl #0
	movz x2, #35072, lsl #0
	add x2, x28, x2
	movz x3, #128, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #19456, lsl #0
	add x1, x28, x1
	movz x2, #41984, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_ntt}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #20480, lsl #0
	add x1, x28, x1
	movz x2, #43008, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #21504, lsl #0
	add x1, x28, x1
	movz x2, #44032, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #22528, lsl #0
	add x1, x28, x1
	movz x2, #45056, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #23552, lsl #0
	add x1, x28, x1
	movz x2, #46080, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	add x0, x25, #992
	movz x1, #48128, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_unpack_t1}
	movz x0, #48128, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_ntt}
	movz x0, #49152, lsl #0
	add x0, x28, x0
	movz x1, #47104, lsl #0
	add x1, x28, x1
	movz x2, #48128, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_ntt}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #49152, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_sub}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_inv_ntt}
	movz x0, #38912, lsl #0
	add x0, x28, x0
	movz x1, #50176, lsl #0
	add x1, x28, x1
	movz x2, #65280, lsl #0
	movk x2, #3, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	movz x3, #51200, lsl #0
	add x3, x28, x3
	bl {vg_mldsa_use_hint}
	movz x0, #51200, lsl #0
	add x0, x28, x0
	movz x1, #15, lsl #0
	movz x2, #35200, lsl #0
	add x2, x28, x2
	movz x3, #128, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #24576, lsl #0
	add x1, x28, x1
	movz x2, #41984, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_ntt}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #25600, lsl #0
	add x1, x28, x1
	movz x2, #43008, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #26624, lsl #0
	add x1, x28, x1
	movz x2, #44032, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #27648, lsl #0
	add x1, x28, x1
	movz x2, #45056, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #28672, lsl #0
	add x1, x28, x1
	movz x2, #46080, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	add x0, x25, #1312
	movz x1, #48128, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_unpack_t1}
	movz x0, #48128, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_ntt}
	movz x0, #49152, lsl #0
	add x0, x28, x0
	movz x1, #47104, lsl #0
	add x1, x28, x1
	movz x2, #48128, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_ntt}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #49152, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_sub}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_inv_ntt}
	movz x0, #39936, lsl #0
	add x0, x28, x0
	movz x1, #50176, lsl #0
	add x1, x28, x1
	movz x2, #65280, lsl #0
	movk x2, #3, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	movz x3, #51200, lsl #0
	add x3, x28, x3
	bl {vg_mldsa_use_hint}
	movz x0, #51200, lsl #0
	add x0, x28, x0
	movz x1, #15, lsl #0
	movz x2, #35328, lsl #0
	add x2, x28, x2
	movz x3, #128, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #29696, lsl #0
	add x1, x28, x1
	movz x2, #41984, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_ntt}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #30720, lsl #0
	add x1, x28, x1
	movz x2, #43008, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #31744, lsl #0
	add x1, x28, x1
	movz x2, #44032, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #32768, lsl #0
	add x1, x28, x1
	movz x2, #45056, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #33792, lsl #0
	add x1, x28, x1
	movz x2, #46080, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	add x0, x25, #1632
	movz x1, #48128, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_unpack_t1}
	movz x0, #48128, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_ntt}
	movz x0, #49152, lsl #0
	add x0, x28, x0
	movz x1, #47104, lsl #0
	add x1, x28, x1
	movz x2, #48128, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_ntt}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #49152, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_sub}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_inv_ntt}
	movz x0, #40960, lsl #0
	add x0, x28, x0
	movz x1, #50176, lsl #0
	add x1, x28, x1
	movz x2, #65280, lsl #0
	movk x2, #3, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	movz x3, #51200, lsl #0
	add x3, x28, x3
	bl {vg_mldsa_use_hint}
	movz x0, #51200, lsl #0
	add x0, x28, x0
	movz x1, #15, lsl #0
	movz x2, #35456, lsl #0
	add x2, x28, x2
	movz x3, #128, lsl #0
	bl {vg_mldsa_simple_bit_pack}
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
	movz x2, #0, lsl #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x5, x28, #200
	add x3, x26, #0
	movz x4, #64, lsl #0
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x5, x28, #200
	movz x3, #34816, lsl #0
	add x3, x28, x3
	movz x4, #768, lsl #0
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x4, x28, #200
	movz x3, #31, lsl #0
	bl {vg_keccak_pad_scratch}
	movz x2, #0, lsl #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x5, x28, #200
	add x3, x28, #1024
	movz x4, #48, lsl #0
	bl {vg_keccak_squeeze_scratch}
	add x0, x28, #1024
	add x1, x27, #0
	movz x2, #48, lsl #0
	movz x10, #0, lsl #0
222:
	ldrb w9, [x0, #0]
	ldrb w11, [x1, #0]
	eor x9, x9, x11
	orr x10, x10, x9
	add x0, x0, #1
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 222b
	sub x10, x10, #1
	lsr x10, x10, #63
	and w24, w24, w10
23:
21:
	add x0, x24, #0
	ldr x30, [x28, #880]
	ldr x24, [x28, #840]
	ldr x25, [x28, #848]
	ldr x26, [x28, #856]
	ldr x27, [x28, #864]
	ldr x28, [x28, #872]
	ret
	.p2align 6

vg_mldsa65_verify_message_cached:
	lsr x9, x4, #8
	cbnz x9, 20f
	movz x9, #37888, lsl #0
	movk x9, #1, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	add x9, x6, x9
	str x28, [x9, #904]
	str x30, [x9, #912]
	add x28, x9, #0
	str x0, [x28, #920]
	str x1, [x28, #928]
	str x2, [x28, #936]
	str x3, [x28, #944]
	str x4, [x28, #952]
	str x7, [x28, #960]
	str x5, [x28, #968]
	str x6, [x28, #976]
	movz x9, #0, lsl #0
	strb w9, [x28, #984]
	strb w4, [x28, #985]
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
	movz x2, #0, lsl #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	ldr x3, [x28, #960]
	movz x4, #64, lsl #0
	add x5, x28, #200
	bl {vg_keccak_absorb_scratch}
	movz x2, #64, lsl #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x3, x28, #984
	movz x4, #2, lsl #0
	add x5, x28, #200
	bl {vg_keccak_absorb_scratch}
	movz x2, #66, lsl #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	ldr x3, [x28, #944]
	ldr x4, [x28, #952]
	add x5, x28, #200
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	ldr x3, [x28, #928]
	ldr x4, [x28, #936]
	add x5, x28, #200
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	movz x3, #31, lsl #0
	add x4, x28, #200
	bl {vg_keccak_pad_scratch}
	add x0, x28, #0
	movz x1, #136, lsl #0
	movz x2, #0, lsl #0
	add x3, x28, #840
	movz x4, #64, lsl #0
	add x5, x28, #200
	bl {vg_keccak_squeeze_scratch}
	ldr x0, [x28, #920]
	add x1, x28, #840
	ldr x2, [x28, #968]
	ldr x3, [x28, #976]
	bl {vg_mldsa65_verify}
	ldr x30, [x28, #912]
	ldr x28, [x28, #904]
	b 21f
20:
	movz x0, #2, lsl #0
21:
	ret
	.p2align 6

vg_mldsa65_keygen_sha3:
	.arch_extension sha3
	str x24, [x3, #840]
	str x25, [x3, #848]
	str x26, [x3, #856]
	str x27, [x3, #864]
	str x28, [x3, #872]
	str x30, [x3, #880]
	add x25, x0, #0
	add x26, x1, #0
	add x27, x2, #0
	add x28, x3, #0
	movz x24, #1, lsl #0
	movz x9, #6, lsl #0
	strb w9, [x28, #896]
	movz x9, #5, lsl #0
	strb w9, [x28, #897]
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
	movz x2, #0, lsl #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x5, x28, #200
	add x3, x25, #0
	movz x4, #32, lsl #0
	bl {vg_keccak_absorb_scratch_sha3}
	add x2, x0, #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x5, x28, #200
	add x3, x28, #896
	movz x4, #2, lsl #0
	bl {vg_keccak_absorb_scratch_sha3}
	add x2, x0, #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x4, x28, #200
	movz x3, #31, lsl #0
	bl {vg_keccak_pad_scratch_sha3}
	movz x2, #0, lsl #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x5, x28, #200
	add x3, x28, #1024
	movz x4, #128, lsl #0
	bl {vg_keccak_squeeze_scratch_sha3}
	ldr x9, [x28, #1024]
	str x9, [x28, #1152]
	ldr x9, [x28, #1032]
	str x9, [x28, #1160]
	ldr x9, [x28, #1040]
	str x9, [x28, #1168]
	ldr x9, [x28, #1048]
	str x9, [x28, #1176]
	ldr x9, [x28, #1056]
	str x9, [x28, #1216]
	ldr x9, [x28, #1064]
	str x9, [x28, #1224]
	ldr x9, [x28, #1072]
	str x9, [x28, #1232]
	ldr x9, [x28, #1080]
	str x9, [x28, #1240]
	ldr x9, [x28, #1088]
	str x9, [x28, #1248]
	ldr x9, [x28, #1096]
	str x9, [x28, #1256]
	ldr x9, [x28, #1104]
	str x9, [x28, #1264]
	ldr x9, [x28, #1112]
	str x9, [x28, #1272]
	movz x9, #0, lsl #0
	strb w9, [x28, #1281]
	add x10, x28, #1408
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	add x10, x28, #1442
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	add x10, x28, #1476
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	add x10, x28, #1510
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #0, lsl #0
	strb w9, [x28, #1440]
	movz x9, #0, lsl #0
	strb w9, [x28, #1441]
	movz x9, #1, lsl #0
	strb w9, [x28, #1474]
	movz x9, #0, lsl #0
	strb w9, [x28, #1475]
	movz x9, #2, lsl #0
	strb w9, [x28, #1508]
	movz x9, #0, lsl #0
	strb w9, [x28, #1509]
	movz x9, #3, lsl #0
	strb w9, [x28, #1542]
	movz x9, #0, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #4096, lsl #0
	add x1, x28, x1
	movz x2, #49152, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4_sha3}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	dup v0.4s, w8
	movz x1, #4096, lsl #0
	add x1, x28, x1
	movz x2, #64, lsl #0
20:
	ldr q1, [x1, #0]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #0]
	ldr q1, [x1, #16]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #16]
	ldr q1, [x1, #32]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #32]
	ldr q1, [x1, #48]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #48]
	add x1, x1, #64
	sub x2, x2, #1
	cbnz x2, 20b
	movz x9, #4, lsl #0
	strb w9, [x28, #1440]
	movz x9, #0, lsl #0
	strb w9, [x28, #1441]
	movz x9, #0, lsl #0
	strb w9, [x28, #1474]
	movz x9, #1, lsl #0
	strb w9, [x28, #1475]
	movz x9, #1, lsl #0
	strb w9, [x28, #1508]
	movz x9, #1, lsl #0
	strb w9, [x28, #1509]
	movz x9, #2, lsl #0
	strb w9, [x28, #1542]
	movz x9, #1, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #8192, lsl #0
	add x1, x28, x1
	movz x2, #49152, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4_sha3}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	dup v0.4s, w8
	movz x1, #8192, lsl #0
	add x1, x28, x1
	movz x2, #64, lsl #0
21:
	ldr q1, [x1, #0]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #0]
	ldr q1, [x1, #16]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #16]
	ldr q1, [x1, #32]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #32]
	ldr q1, [x1, #48]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #48]
	add x1, x1, #64
	sub x2, x2, #1
	cbnz x2, 21b
	movz x9, #3, lsl #0
	strb w9, [x28, #1440]
	movz x9, #1, lsl #0
	strb w9, [x28, #1441]
	movz x9, #4, lsl #0
	strb w9, [x28, #1474]
	movz x9, #1, lsl #0
	strb w9, [x28, #1475]
	movz x9, #0, lsl #0
	strb w9, [x28, #1508]
	movz x9, #2, lsl #0
	strb w9, [x28, #1509]
	movz x9, #1, lsl #0
	strb w9, [x28, #1542]
	movz x9, #2, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #12288, lsl #0
	add x1, x28, x1
	movz x2, #49152, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4_sha3}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	dup v0.4s, w8
	movz x1, #12288, lsl #0
	add x1, x28, x1
	movz x2, #64, lsl #0
22:
	ldr q1, [x1, #0]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #0]
	ldr q1, [x1, #16]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #16]
	ldr q1, [x1, #32]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #32]
	ldr q1, [x1, #48]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #48]
	add x1, x1, #64
	sub x2, x2, #1
	cbnz x2, 22b
	movz x9, #2, lsl #0
	strb w9, [x28, #1440]
	movz x9, #2, lsl #0
	strb w9, [x28, #1441]
	movz x9, #3, lsl #0
	strb w9, [x28, #1474]
	movz x9, #2, lsl #0
	strb w9, [x28, #1475]
	movz x9, #4, lsl #0
	strb w9, [x28, #1508]
	movz x9, #2, lsl #0
	strb w9, [x28, #1509]
	movz x9, #0, lsl #0
	strb w9, [x28, #1542]
	movz x9, #3, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #16384, lsl #0
	add x1, x28, x1
	movz x2, #49152, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4_sha3}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	dup v0.4s, w8
	movz x1, #16384, lsl #0
	add x1, x28, x1
	movz x2, #64, lsl #0
23:
	ldr q1, [x1, #0]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #0]
	ldr q1, [x1, #16]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #16]
	ldr q1, [x1, #32]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #32]
	ldr q1, [x1, #48]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #48]
	add x1, x1, #64
	sub x2, x2, #1
	cbnz x2, 23b
	movz x9, #1, lsl #0
	strb w9, [x28, #1440]
	movz x9, #3, lsl #0
	strb w9, [x28, #1441]
	movz x9, #2, lsl #0
	strb w9, [x28, #1474]
	movz x9, #3, lsl #0
	strb w9, [x28, #1475]
	movz x9, #3, lsl #0
	strb w9, [x28, #1508]
	movz x9, #3, lsl #0
	strb w9, [x28, #1509]
	movz x9, #4, lsl #0
	strb w9, [x28, #1542]
	movz x9, #3, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #20480, lsl #0
	add x1, x28, x1
	movz x2, #49152, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4_sha3}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	dup v0.4s, w8
	movz x1, #20480, lsl #0
	add x1, x28, x1
	movz x2, #64, lsl #0
24:
	ldr q1, [x1, #0]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #0]
	ldr q1, [x1, #16]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #16]
	ldr q1, [x1, #32]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #32]
	ldr q1, [x1, #48]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #48]
	add x1, x1, #64
	sub x2, x2, #1
	cbnz x2, 24b
	movz x9, #0, lsl #0
	strb w9, [x28, #1440]
	movz x9, #4, lsl #0
	strb w9, [x28, #1441]
	movz x9, #1, lsl #0
	strb w9, [x28, #1474]
	movz x9, #4, lsl #0
	strb w9, [x28, #1475]
	movz x9, #2, lsl #0
	strb w9, [x28, #1508]
	movz x9, #4, lsl #0
	strb w9, [x28, #1509]
	movz x9, #3, lsl #0
	strb w9, [x28, #1542]
	movz x9, #4, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #24576, lsl #0
	add x1, x28, x1
	movz x2, #49152, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4_sha3}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	dup v0.4s, w8
	movz x1, #24576, lsl #0
	add x1, x28, x1
	movz x2, #64, lsl #0
25:
	ldr q1, [x1, #0]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #0]
	ldr q1, [x1, #16]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #16]
	ldr q1, [x1, #32]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #32]
	ldr q1, [x1, #48]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #48]
	add x1, x1, #64
	sub x2, x2, #1
	cbnz x2, 25b
	movz x9, #4, lsl #0
	strb w9, [x28, #1440]
	movz x9, #4, lsl #0
	strb w9, [x28, #1441]
	movz x9, #0, lsl #0
	strb w9, [x28, #1474]
	movz x9, #5, lsl #0
	strb w9, [x28, #1475]
	movz x9, #1, lsl #0
	strb w9, [x28, #1508]
	movz x9, #5, lsl #0
	strb w9, [x28, #1509]
	movz x9, #2, lsl #0
	strb w9, [x28, #1542]
	movz x9, #5, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #28672, lsl #0
	add x1, x28, x1
	movz x2, #49152, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4_sha3}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	dup v0.4s, w8
	movz x1, #28672, lsl #0
	add x1, x28, x1
	movz x2, #64, lsl #0
26:
	ldr q1, [x1, #0]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #0]
	ldr q1, [x1, #16]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #16]
	ldr q1, [x1, #32]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #32]
	ldr q1, [x1, #48]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #48]
	add x1, x1, #64
	sub x2, x2, #1
	cbnz x2, 26b
	movz x9, #3, lsl #0
	strb w9, [x28, #1440]
	movz x9, #5, lsl #0
	strb w9, [x28, #1441]
	movz x9, #4, lsl #0
	strb w9, [x28, #1474]
	movz x9, #5, lsl #0
	strb w9, [x28, #1475]
	add x0, x28, #1408
	movz x1, #32768, lsl #0
	add x1, x28, x1
	movz x2, #49152, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly2_sha3}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	dup v0.4s, w8
	movz x1, #32768, lsl #0
	add x1, x28, x1
	movz x2, #32, lsl #0
27:
	ldr q1, [x1, #0]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #0]
	ldr q1, [x1, #16]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #16]
	ldr q1, [x1, #32]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #32]
	ldr q1, [x1, #48]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #48]
	add x1, x1, #64
	sub x2, x2, #1
	cbnz x2, 27b
	add x10, x28, #1408
	ldr x9, [x28, #1216]
	str x9, [x10, #0]
	ldr x9, [x28, #1224]
	str x9, [x10, #8]
	ldr x9, [x28, #1232]
	str x9, [x10, #16]
	ldr x9, [x28, #1240]
	str x9, [x10, #24]
	ldr x9, [x28, #1248]
	str x9, [x10, #32]
	ldr x9, [x28, #1256]
	str x9, [x10, #40]
	ldr x9, [x28, #1264]
	str x9, [x10, #48]
	ldr x9, [x28, #1272]
	str x9, [x10, #56]
	movz x9, #0, lsl #0
	strb w9, [x28, #1472]
	movz x9, #0, lsl #0
	strb w9, [x28, #1473]
	add x10, x28, #1474
	ldr x9, [x28, #1216]
	str x9, [x10, #0]
	ldr x9, [x28, #1224]
	str x9, [x10, #8]
	ldr x9, [x28, #1232]
	str x9, [x10, #16]
	ldr x9, [x28, #1240]
	str x9, [x10, #24]
	ldr x9, [x28, #1248]
	str x9, [x10, #32]
	ldr x9, [x28, #1256]
	str x9, [x10, #40]
	ldr x9, [x28, #1264]
	str x9, [x10, #48]
	ldr x9, [x28, #1272]
	str x9, [x10, #56]
	movz x9, #1, lsl #0
	strb w9, [x28, #1538]
	movz x9, #0, lsl #0
	strb w9, [x28, #1539]
	add x10, x28, #1540
	ldr x9, [x28, #1216]
	str x9, [x10, #0]
	ldr x9, [x28, #1224]
	str x9, [x10, #8]
	ldr x9, [x28, #1232]
	str x9, [x10, #16]
	ldr x9, [x28, #1240]
	str x9, [x10, #24]
	ldr x9, [x28, #1248]
	str x9, [x10, #32]
	ldr x9, [x28, #1256]
	str x9, [x10, #40]
	ldr x9, [x28, #1264]
	str x9, [x10, #48]
	ldr x9, [x28, #1272]
	str x9, [x10, #56]
	movz x9, #2, lsl #0
	strb w9, [x28, #1604]
	movz x9, #0, lsl #0
	strb w9, [x28, #1605]
	add x10, x28, #1606
	ldr x9, [x28, #1216]
	str x9, [x10, #0]
	ldr x9, [x28, #1224]
	str x9, [x10, #8]
	ldr x9, [x28, #1232]
	str x9, [x10, #16]
	ldr x9, [x28, #1240]
	str x9, [x10, #24]
	ldr x9, [x28, #1248]
	str x9, [x10, #32]
	ldr x9, [x28, #1256]
	str x9, [x10, #40]
	ldr x9, [x28, #1264]
	str x9, [x10, #48]
	ldr x9, [x28, #1272]
	str x9, [x10, #56]
	movz x9, #3, lsl #0
	strb w9, [x28, #1670]
	movz x9, #0, lsl #0
	strb w9, [x28, #1671]
	add x0, x28, #1408
	movz x1, #34816, lsl #0
	add x1, x28, x1
	movz x2, #49152, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_rej_bounded_poly4_eta4_sha3}
	and w24, w24, w0
	add x10, x28, #1408
	ldr x9, [x28, #1216]
	str x9, [x10, #0]
	ldr x9, [x28, #1224]
	str x9, [x10, #8]
	ldr x9, [x28, #1232]
	str x9, [x10, #16]
	ldr x9, [x28, #1240]
	str x9, [x10, #24]
	ldr x9, [x28, #1248]
	str x9, [x10, #32]
	ldr x9, [x28, #1256]
	str x9, [x10, #40]
	ldr x9, [x28, #1264]
	str x9, [x10, #48]
	ldr x9, [x28, #1272]
	str x9, [x10, #56]
	movz x9, #4, lsl #0
	strb w9, [x28, #1472]
	movz x9, #0, lsl #0
	strb w9, [x28, #1473]
	add x10, x28, #1474
	ldr x9, [x28, #1216]
	str x9, [x10, #0]
	ldr x9, [x28, #1224]
	str x9, [x10, #8]
	ldr x9, [x28, #1232]
	str x9, [x10, #16]
	ldr x9, [x28, #1240]
	str x9, [x10, #24]
	ldr x9, [x28, #1248]
	str x9, [x10, #32]
	ldr x9, [x28, #1256]
	str x9, [x10, #40]
	ldr x9, [x28, #1264]
	str x9, [x10, #48]
	ldr x9, [x28, #1272]
	str x9, [x10, #56]
	movz x9, #5, lsl #0
	strb w9, [x28, #1538]
	movz x9, #0, lsl #0
	strb w9, [x28, #1539]
	add x10, x28, #1540
	ldr x9, [x28, #1216]
	str x9, [x10, #0]
	ldr x9, [x28, #1224]
	str x9, [x10, #8]
	ldr x9, [x28, #1232]
	str x9, [x10, #16]
	ldr x9, [x28, #1240]
	str x9, [x10, #24]
	ldr x9, [x28, #1248]
	str x9, [x10, #32]
	ldr x9, [x28, #1256]
	str x9, [x10, #40]
	ldr x9, [x28, #1264]
	str x9, [x10, #48]
	ldr x9, [x28, #1272]
	str x9, [x10, #56]
	movz x9, #6, lsl #0
	strb w9, [x28, #1604]
	movz x9, #0, lsl #0
	strb w9, [x28, #1605]
	add x10, x28, #1606
	ldr x9, [x28, #1216]
	str x9, [x10, #0]
	ldr x9, [x28, #1224]
	str x9, [x10, #8]
	ldr x9, [x28, #1232]
	str x9, [x10, #16]
	ldr x9, [x28, #1240]
	str x9, [x10, #24]
	ldr x9, [x28, #1248]
	str x9, [x10, #32]
	ldr x9, [x28, #1256]
	str x9, [x10, #40]
	ldr x9, [x28, #1264]
	str x9, [x10, #48]
	ldr x9, [x28, #1272]
	str x9, [x10, #56]
	movz x9, #7, lsl #0
	strb w9, [x28, #1670]
	movz x9, #0, lsl #0
	strb w9, [x28, #1671]
	add x0, x28, #1408
	movz x1, #38912, lsl #0
	add x1, x28, x1
	movz x2, #49152, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_rej_bounded_poly4_eta4_sha3}
	and w24, w24, w0
	add x10, x28, #1408
	ldr x9, [x28, #1216]
	str x9, [x10, #0]
	ldr x9, [x28, #1224]
	str x9, [x10, #8]
	ldr x9, [x28, #1232]
	str x9, [x10, #16]
	ldr x9, [x28, #1240]
	str x9, [x10, #24]
	ldr x9, [x28, #1248]
	str x9, [x10, #32]
	ldr x9, [x28, #1256]
	str x9, [x10, #40]
	ldr x9, [x28, #1264]
	str x9, [x10, #48]
	ldr x9, [x28, #1272]
	str x9, [x10, #56]
	movz x9, #8, lsl #0
	strb w9, [x28, #1472]
	movz x9, #0, lsl #0
	strb w9, [x28, #1473]
	add x10, x28, #1474
	ldr x9, [x28, #1216]
	str x9, [x10, #0]
	ldr x9, [x28, #1224]
	str x9, [x10, #8]
	ldr x9, [x28, #1232]
	str x9, [x10, #16]
	ldr x9, [x28, #1240]
	str x9, [x10, #24]
	ldr x9, [x28, #1248]
	str x9, [x10, #32]
	ldr x9, [x28, #1256]
	str x9, [x10, #40]
	ldr x9, [x28, #1264]
	str x9, [x10, #48]
	ldr x9, [x28, #1272]
	str x9, [x10, #56]
	movz x9, #9, lsl #0
	strb w9, [x28, #1538]
	movz x9, #0, lsl #0
	strb w9, [x28, #1539]
	add x10, x28, #1540
	ldr x9, [x28, #1216]
	str x9, [x10, #0]
	ldr x9, [x28, #1224]
	str x9, [x10, #8]
	ldr x9, [x28, #1232]
	str x9, [x10, #16]
	ldr x9, [x28, #1240]
	str x9, [x10, #24]
	ldr x9, [x28, #1248]
	str x9, [x10, #32]
	ldr x9, [x28, #1256]
	str x9, [x10, #40]
	ldr x9, [x28, #1264]
	str x9, [x10, #48]
	ldr x9, [x28, #1272]
	str x9, [x10, #56]
	movz x9, #10, lsl #0
	strb w9, [x28, #1604]
	movz x9, #0, lsl #0
	strb w9, [x28, #1605]
	add x10, x28, #1606
	ldr x9, [x28, #1216]
	str x9, [x10, #0]
	ldr x9, [x28, #1224]
	str x9, [x10, #8]
	ldr x9, [x28, #1232]
	str x9, [x10, #16]
	ldr x9, [x28, #1240]
	str x9, [x10, #24]
	ldr x9, [x28, #1248]
	str x9, [x10, #32]
	ldr x9, [x28, #1256]
	str x9, [x10, #40]
	ldr x9, [x28, #1264]
	str x9, [x10, #48]
	ldr x9, [x28, #1272]
	str x9, [x10, #56]
	movz x9, #8, lsl #0
	strb w9, [x28, #1670]
	movz x9, #0, lsl #0
	strb w9, [x28, #1671]
	add x0, x28, #1408
	movz x1, #43008, lsl #0
	add x1, x28, x1
	movz x2, #49152, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_rej_bounded_poly4_eta4_sha3}
	and w24, w24, w0
	ldr x9, [x28, #1024]
	str x9, [x26, #0]
	ldr x9, [x28, #1032]
	str x9, [x26, #8]
	ldr x9, [x28, #1040]
	str x9, [x26, #16]
	ldr x9, [x28, #1048]
	str x9, [x26, #24]
	ldr x9, [x28, #1024]
	str x9, [x27, #0]
	ldr x9, [x28, #1032]
	str x9, [x27, #8]
	ldr x9, [x28, #1040]
	str x9, [x27, #16]
	ldr x9, [x28, #1048]
	str x9, [x27, #24]
	ldr x9, [x28, #1120]
	str x9, [x27, #32]
	ldr x9, [x28, #1128]
	str x9, [x27, #40]
	ldr x9, [x28, #1136]
	str x9, [x27, #48]
	ldr x9, [x28, #1144]
	str x9, [x27, #56]
	movz x0, #34816, lsl #0
	add x0, x28, x0
	movz x1, #4, lsl #0
	movz x2, #4, lsl #0
	add x3, x27, #128
	movz x4, #128, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #35840, lsl #0
	add x0, x28, x0
	movz x1, #4, lsl #0
	movz x2, #4, lsl #0
	add x3, x27, #256
	movz x4, #128, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #36864, lsl #0
	add x0, x28, x0
	movz x1, #4, lsl #0
	movz x2, #4, lsl #0
	add x3, x27, #384
	movz x4, #128, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #37888, lsl #0
	add x0, x28, x0
	movz x1, #4, lsl #0
	movz x2, #4, lsl #0
	add x3, x27, #512
	movz x4, #128, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #38912, lsl #0
	add x0, x28, x0
	movz x1, #4, lsl #0
	movz x2, #4, lsl #0
	add x3, x27, #640
	movz x4, #128, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #39936, lsl #0
	add x0, x28, x0
	movz x1, #4, lsl #0
	movz x2, #4, lsl #0
	add x3, x27, #768
	movz x4, #128, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #40960, lsl #0
	add x0, x28, x0
	movz x1, #4, lsl #0
	movz x2, #4, lsl #0
	add x3, x27, #896
	movz x4, #128, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #41984, lsl #0
	add x0, x28, x0
	movz x1, #4, lsl #0
	movz x2, #4, lsl #0
	add x3, x27, #1024
	movz x4, #128, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #43008, lsl #0
	add x0, x28, x0
	movz x1, #4, lsl #0
	movz x2, #4, lsl #0
	add x3, x27, #1152
	movz x4, #128, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #44032, lsl #0
	add x0, x28, x0
	movz x1, #4, lsl #0
	movz x2, #4, lsl #0
	add x3, x27, #1280
	movz x4, #128, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #45056, lsl #0
	add x0, x28, x0
	movz x1, #4, lsl #0
	movz x2, #4, lsl #0
	add x3, x27, #1408
	movz x4, #128, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #34816, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	movz x0, #35840, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	movz x0, #36864, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	movz x0, #37888, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	movz x0, #38912, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #4096, lsl #0
	add x1, x28, x1
	movz x2, #34816, lsl #0
	add x2, x28, x2
	add x3, x28, #2048
	bl {vg_mldsa_dot_inverse5}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #39936, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_add}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #47104, lsl #0
	add x1, x28, x1
	movz x2, #48128, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_power2round}
	movz x0, #47104, lsl #0
	add x0, x28, x0
	movz x1, #1023, lsl #0
	add x2, x26, #32
	movz x3, #320, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #48128, lsl #0
	add x0, x28, x0
	movz x1, #4095, lsl #0
	movz x2, #4096, lsl #0
	add x3, x27, #1536
	movz x4, #416, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #9216, lsl #0
	add x1, x28, x1
	movz x2, #34816, lsl #0
	add x2, x28, x2
	add x3, x28, #2048
	bl {vg_mldsa_dot_inverse5}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #40960, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_add}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #47104, lsl #0
	add x1, x28, x1
	movz x2, #48128, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_power2round}
	movz x0, #47104, lsl #0
	add x0, x28, x0
	movz x1, #1023, lsl #0
	add x2, x26, #352
	movz x3, #320, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #48128, lsl #0
	add x0, x28, x0
	movz x1, #4095, lsl #0
	movz x2, #4096, lsl #0
	add x3, x27, #1952
	movz x4, #416, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #14336, lsl #0
	add x1, x28, x1
	movz x2, #34816, lsl #0
	add x2, x28, x2
	add x3, x28, #2048
	bl {vg_mldsa_dot_inverse5}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #41984, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_add}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #47104, lsl #0
	add x1, x28, x1
	movz x2, #48128, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_power2round}
	movz x0, #47104, lsl #0
	add x0, x28, x0
	movz x1, #1023, lsl #0
	add x2, x26, #672
	movz x3, #320, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #48128, lsl #0
	add x0, x28, x0
	movz x1, #4095, lsl #0
	movz x2, #4096, lsl #0
	add x3, x27, #2368
	movz x4, #416, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #19456, lsl #0
	add x1, x28, x1
	movz x2, #34816, lsl #0
	add x2, x28, x2
	add x3, x28, #2048
	bl {vg_mldsa_dot_inverse5}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #43008, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_add}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #47104, lsl #0
	add x1, x28, x1
	movz x2, #48128, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_power2round}
	movz x0, #47104, lsl #0
	add x0, x28, x0
	movz x1, #1023, lsl #0
	add x2, x26, #992
	movz x3, #320, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #48128, lsl #0
	add x0, x28, x0
	movz x1, #4095, lsl #0
	movz x2, #4096, lsl #0
	add x3, x27, #2784
	movz x4, #416, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #24576, lsl #0
	add x1, x28, x1
	movz x2, #34816, lsl #0
	add x2, x28, x2
	add x3, x28, #2048
	bl {vg_mldsa_dot_inverse5}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #44032, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_add}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #47104, lsl #0
	add x1, x28, x1
	movz x2, #48128, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_power2round}
	movz x0, #47104, lsl #0
	add x0, x28, x0
	movz x1, #1023, lsl #0
	add x2, x26, #1312
	movz x3, #320, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #48128, lsl #0
	add x0, x28, x0
	movz x1, #4095, lsl #0
	movz x2, #4096, lsl #0
	add x3, x27, #3200
	movz x4, #416, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #29696, lsl #0
	add x1, x28, x1
	movz x2, #34816, lsl #0
	add x2, x28, x2
	add x3, x28, #2048
	bl {vg_mldsa_dot_inverse5}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #45056, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_add}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #47104, lsl #0
	add x1, x28, x1
	movz x2, #48128, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_power2round}
	movz x0, #47104, lsl #0
	add x0, x28, x0
	movz x1, #1023, lsl #0
	add x2, x26, #1632
	movz x3, #320, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #48128, lsl #0
	add x0, x28, x0
	movz x1, #4095, lsl #0
	movz x2, #4096, lsl #0
	add x3, x27, #3616
	movz x4, #416, lsl #0
	bl {vg_mldsa_bit_pack}
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
	movz x2, #0, lsl #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x5, x28, #200
	add x3, x26, #0
	movz x4, #1952, lsl #0
	bl {vg_keccak_absorb_scratch_sha3}
	add x2, x0, #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x4, x28, #200
	movz x3, #31, lsl #0
	bl {vg_keccak_pad_scratch_sha3}
	movz x2, #0, lsl #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x5, x28, #200
	add x3, x27, #64
	movz x4, #64, lsl #0
	bl {vg_keccak_squeeze_scratch_sha3}
	add x0, x24, #0
	ldr x30, [x28, #880]
	ldr x24, [x28, #840]
	ldr x25, [x28, #848]
	ldr x26, [x28, #856]
	ldr x27, [x28, #864]
	ldr x28, [x28, #872]
	ret
	.arch_extension nosha3
	.p2align 6

vg_mldsa65_sign_sha3:
	.arch_extension sha3
	str x23, [x4, #840]
	str x24, [x4, #848]
	str x25, [x4, #856]
	str x26, [x4, #864]
	str x27, [x4, #872]
	str x30, [x4, #880]
	str x28, [x4, #888]
	add x28, x4, #0
	add x25, x0, #0
	add x26, x1, #0
	add x27, x2, #0
	add x23, x3, #0
	movz x24, #1, lsl #0
	ldr x9, [x25, #0]
	str x9, [x28, #920]
	ldr x9, [x25, #8]
	str x9, [x28, #928]
	ldr x9, [x25, #16]
	str x9, [x28, #936]
	ldr x9, [x25, #24]
	str x9, [x28, #944]
	add x10, x28, #1408
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #0, lsl #0
	strb w9, [x28, #1440]
	movz x9, #0, lsl #0
	strb w9, [x28, #1441]
	add x10, x28, #1442
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #1, lsl #0
	strb w9, [x28, #1474]
	movz x9, #0, lsl #0
	strb w9, [x28, #1475]
	add x10, x28, #1476
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #2, lsl #0
	strb w9, [x28, #1508]
	movz x9, #0, lsl #0
	strb w9, [x28, #1509]
	add x10, x28, #1510
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #3, lsl #0
	strb w9, [x28, #1542]
	movz x9, #0, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #50176, lsl #0
	add x1, x28, x1
	movz x2, #15360, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4_sha3}
	and w24, w24, w0
	add x10, x28, #1408
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #4, lsl #0
	strb w9, [x28, #1440]
	movz x9, #0, lsl #0
	strb w9, [x28, #1441]
	add x10, x28, #1442
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #0, lsl #0
	strb w9, [x28, #1474]
	movz x9, #1, lsl #0
	strb w9, [x28, #1475]
	add x10, x28, #1476
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #1, lsl #0
	strb w9, [x28, #1508]
	movz x9, #1, lsl #0
	strb w9, [x28, #1509]
	add x10, x28, #1510
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #2, lsl #0
	strb w9, [x28, #1542]
	movz x9, #1, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #54272, lsl #0
	add x1, x28, x1
	movz x2, #15360, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4_sha3}
	and w24, w24, w0
	add x10, x28, #1408
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #3, lsl #0
	strb w9, [x28, #1440]
	movz x9, #1, lsl #0
	strb w9, [x28, #1441]
	add x10, x28, #1442
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #4, lsl #0
	strb w9, [x28, #1474]
	movz x9, #1, lsl #0
	strb w9, [x28, #1475]
	add x10, x28, #1476
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #0, lsl #0
	strb w9, [x28, #1508]
	movz x9, #2, lsl #0
	strb w9, [x28, #1509]
	add x10, x28, #1510
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #1, lsl #0
	strb w9, [x28, #1542]
	movz x9, #2, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #58368, lsl #0
	add x1, x28, x1
	movz x2, #15360, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4_sha3}
	and w24, w24, w0
	add x10, x28, #1408
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #2, lsl #0
	strb w9, [x28, #1440]
	movz x9, #2, lsl #0
	strb w9, [x28, #1441]
	add x10, x28, #1442
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #3, lsl #0
	strb w9, [x28, #1474]
	movz x9, #2, lsl #0
	strb w9, [x28, #1475]
	add x10, x28, #1476
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #4, lsl #0
	strb w9, [x28, #1508]
	movz x9, #2, lsl #0
	strb w9, [x28, #1509]
	add x10, x28, #1510
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #0, lsl #0
	strb w9, [x28, #1542]
	movz x9, #3, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #62464, lsl #0
	add x1, x28, x1
	movz x2, #15360, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4_sha3}
	and w24, w24, w0
	add x10, x28, #1408
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #1, lsl #0
	strb w9, [x28, #1440]
	movz x9, #3, lsl #0
	strb w9, [x28, #1441]
	add x10, x28, #1442
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #2, lsl #0
	strb w9, [x28, #1474]
	movz x9, #3, lsl #0
	strb w9, [x28, #1475]
	add x10, x28, #1476
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #3, lsl #0
	strb w9, [x28, #1508]
	movz x9, #3, lsl #0
	strb w9, [x28, #1509]
	add x10, x28, #1510
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #4, lsl #0
	strb w9, [x28, #1542]
	movz x9, #3, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #1024, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	movz x2, #15360, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4_sha3}
	and w24, w24, w0
	add x10, x28, #1408
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #0, lsl #0
	strb w9, [x28, #1440]
	movz x9, #4, lsl #0
	strb w9, [x28, #1441]
	add x10, x28, #1442
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #1, lsl #0
	strb w9, [x28, #1474]
	movz x9, #4, lsl #0
	strb w9, [x28, #1475]
	add x10, x28, #1476
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #2, lsl #0
	strb w9, [x28, #1508]
	movz x9, #4, lsl #0
	strb w9, [x28, #1509]
	add x10, x28, #1510
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #3, lsl #0
	strb w9, [x28, #1542]
	movz x9, #4, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #5120, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	movz x2, #15360, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4_sha3}
	and w24, w24, w0
	add x10, x28, #1408
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #4, lsl #0
	strb w9, [x28, #1440]
	movz x9, #4, lsl #0
	strb w9, [x28, #1441]
	add x10, x28, #1442
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #0, lsl #0
	strb w9, [x28, #1474]
	movz x9, #5, lsl #0
	strb w9, [x28, #1475]
	add x10, x28, #1476
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #1, lsl #0
	strb w9, [x28, #1508]
	movz x9, #5, lsl #0
	strb w9, [x28, #1509]
	add x10, x28, #1510
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #2, lsl #0
	strb w9, [x28, #1542]
	movz x9, #5, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #9216, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	movz x2, #15360, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4_sha3}
	and w24, w24, w0
	add x10, x28, #1408
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #3, lsl #0
	strb w9, [x28, #1440]
	movz x9, #5, lsl #0
	strb w9, [x28, #1441]
	add x10, x28, #1442
	ldr x9, [x28, #920]
	str x9, [x10, #0]
	ldr x9, [x28, #928]
	str x9, [x10, #8]
	ldr x9, [x28, #936]
	str x9, [x10, #16]
	ldr x9, [x28, #944]
	str x9, [x10, #24]
	movz x9, #4, lsl #0
	strb w9, [x28, #1474]
	movz x9, #5, lsl #0
	strb w9, [x28, #1475]
	add x0, x28, #1408
	movz x1, #13312, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	movz x2, #15360, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly2_sha3}
	and w24, w24, w0
	cbnz w24, 20f
	b 21f
20:
	add x0, x25, #128
	movz x1, #128, lsl #0
	movz x2, #4, lsl #0
	movz x3, #4, lsl #0
	movz x4, #32768, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #32768, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #256
	movz x1, #128, lsl #0
	movz x2, #4, lsl #0
	movz x3, #4, lsl #0
	movz x4, #33792, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #33792, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #384
	movz x1, #128, lsl #0
	movz x2, #4, lsl #0
	movz x3, #4, lsl #0
	movz x4, #34816, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #34816, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #512
	movz x1, #128, lsl #0
	movz x2, #4, lsl #0
	movz x3, #4, lsl #0
	movz x4, #35840, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #35840, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #640
	movz x1, #128, lsl #0
	movz x2, #4, lsl #0
	movz x3, #4, lsl #0
	movz x4, #36864, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #36864, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #768
	movz x1, #128, lsl #0
	movz x2, #4, lsl #0
	movz x3, #4, lsl #0
	movz x4, #37888, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #37888, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #896
	movz x1, #128, lsl #0
	movz x2, #4, lsl #0
	movz x3, #4, lsl #0
	movz x4, #38912, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #38912, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #1024
	movz x1, #128, lsl #0
	movz x2, #4, lsl #0
	movz x3, #4, lsl #0
	movz x4, #39936, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #39936, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #1152
	movz x1, #128, lsl #0
	movz x2, #4, lsl #0
	movz x3, #4, lsl #0
	movz x4, #40960, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #40960, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #1280
	movz x1, #128, lsl #0
	movz x2, #4, lsl #0
	movz x3, #4, lsl #0
	movz x4, #41984, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #41984, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #1408
	movz x1, #128, lsl #0
	movz x2, #4, lsl #0
	movz x3, #4, lsl #0
	movz x4, #43008, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #43008, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #1536
	movz x1, #416, lsl #0
	movz x2, #4095, lsl #0
	movz x3, #4096, lsl #0
	movz x4, #44032, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #44032, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #1952
	movz x1, #416, lsl #0
	movz x2, #4095, lsl #0
	movz x3, #4096, lsl #0
	movz x4, #45056, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #45056, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #2368
	movz x1, #416, lsl #0
	movz x2, #4095, lsl #0
	movz x3, #4096, lsl #0
	movz x4, #46080, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #2784
	movz x1, #416, lsl #0
	movz x2, #4095, lsl #0
	movz x3, #4096, lsl #0
	movz x4, #47104, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #47104, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #3200
	movz x1, #416, lsl #0
	movz x2, #4095, lsl #0
	movz x3, #4096, lsl #0
	movz x4, #48128, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #48128, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #3616
	movz x1, #416, lsl #0
	movz x2, #4095, lsl #0
	movz x3, #4096, lsl #0
	movz x4, #49152, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #49152, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
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
	movz x2, #0, lsl #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x5, x28, #200
	add x3, x25, #32
	movz x4, #32, lsl #0
	bl {vg_keccak_absorb_scratch_sha3}
	add x2, x0, #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x5, x28, #200
	add x3, x27, #0
	movz x4, #32, lsl #0
	bl {vg_keccak_absorb_scratch_sha3}
	add x2, x0, #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x5, x28, #200
	add x3, x26, #0
	movz x4, #64, lsl #0
	bl {vg_keccak_absorb_scratch_sha3}
	add x2, x0, #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x4, x28, #200
	movz x3, #31, lsl #0
	bl {vg_keccak_pad_scratch_sha3}
	movz x2, #0, lsl #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x5, x28, #200
	add x3, x28, #960
	movz x4, #64, lsl #0
	bl {vg_keccak_squeeze_scratch_sha3}
	movz x9, #0, lsl #0
	str x9, [x28, #904]
	movz x9, #814, lsl #0
	str x9, [x28, #896]
22:
	add x10, x28, #1632
	ldr x9, [x28, #960]
	str x9, [x10, #0]
	ldr x9, [x28, #968]
	str x9, [x10, #8]
	ldr x9, [x28, #976]
	str x9, [x10, #16]
	ldr x9, [x28, #984]
	str x9, [x10, #24]
	add x10, x28, #1664
	ldr x9, [x28, #992]
	str x9, [x10, #0]
	ldr x9, [x28, #1000]
	str x9, [x10, #8]
	ldr x9, [x28, #1008]
	str x9, [x10, #16]
	ldr x9, [x28, #1016]
	str x9, [x10, #24]
	ldr x9, [x28, #904]
	add x9, x9, #0
	strb w9, [x28, #1696]
	lsr x9, x9, #8
	strb w9, [x28, #1697]
	add x10, x28, #1698
	ldr x9, [x28, #960]
	str x9, [x10, #0]
	ldr x9, [x28, #968]
	str x9, [x10, #8]
	ldr x9, [x28, #976]
	str x9, [x10, #16]
	ldr x9, [x28, #984]
	str x9, [x10, #24]
	add x10, x28, #1730
	ldr x9, [x28, #992]
	str x9, [x10, #0]
	ldr x9, [x28, #1000]
	str x9, [x10, #8]
	ldr x9, [x28, #1008]
	str x9, [x10, #16]
	ldr x9, [x28, #1016]
	str x9, [x10, #24]
	ldr x9, [x28, #904]
	add x9, x9, #1
	strb w9, [x28, #1762]
	lsr x9, x9, #8
	strb w9, [x28, #1763]
	add x0, x28, #1632
	movz x1, #0, lsl #0
	movk x1, #8, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	movz x2, #16384, lsl #0
	add x2, x28, x2
	movz x3, #17408, lsl #0
	add x3, x28, x3
	movz x4, #15360, lsl #0
	movk x4, #1, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	add x4, x28, x4
	bl {vg_mldsa_expand_mask_pair_sha3}
	movz x0, #21504, lsl #0
	add x0, x28, x0
	movz x1, #16384, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_ntt_positive_from}
	movz x0, #22528, lsl #0
	add x0, x28, x0
	movz x1, #17408, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_ntt_positive_from}
	add x10, x28, #1632
	ldr x9, [x28, #960]
	str x9, [x10, #0]
	ldr x9, [x28, #968]
	str x9, [x10, #8]
	ldr x9, [x28, #976]
	str x9, [x10, #16]
	ldr x9, [x28, #984]
	str x9, [x10, #24]
	add x10, x28, #1664
	ldr x9, [x28, #992]
	str x9, [x10, #0]
	ldr x9, [x28, #1000]
	str x9, [x10, #8]
	ldr x9, [x28, #1008]
	str x9, [x10, #16]
	ldr x9, [x28, #1016]
	str x9, [x10, #24]
	ldr x9, [x28, #904]
	add x9, x9, #2
	strb w9, [x28, #1696]
	lsr x9, x9, #8
	strb w9, [x28, #1697]
	add x10, x28, #1698
	ldr x9, [x28, #960]
	str x9, [x10, #0]
	ldr x9, [x28, #968]
	str x9, [x10, #8]
	ldr x9, [x28, #976]
	str x9, [x10, #16]
	ldr x9, [x28, #984]
	str x9, [x10, #24]
	add x10, x28, #1730
	ldr x9, [x28, #992]
	str x9, [x10, #0]
	ldr x9, [x28, #1000]
	str x9, [x10, #8]
	ldr x9, [x28, #1008]
	str x9, [x10, #16]
	ldr x9, [x28, #1016]
	str x9, [x10, #24]
	ldr x9, [x28, #904]
	add x9, x9, #3
	strb w9, [x28, #1762]
	lsr x9, x9, #8
	strb w9, [x28, #1763]
	add x0, x28, #1632
	movz x1, #0, lsl #0
	movk x1, #8, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	movz x2, #18432, lsl #0
	add x2, x28, x2
	movz x3, #19456, lsl #0
	add x3, x28, x3
	movz x4, #15360, lsl #0
	movk x4, #1, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	add x4, x28, x4
	bl {vg_mldsa_expand_mask_pair_sha3}
	movz x0, #23552, lsl #0
	add x0, x28, x0
	movz x1, #18432, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_ntt_positive_from}
	movz x0, #24576, lsl #0
	add x0, x28, x0
	movz x1, #19456, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_ntt_positive_from}
	ldr x9, [x28, #904]
	cbnz x9, 23f
	ldr x9, [x28, #904]
	add x9, x9, #4
	strb w9, [x28, #1024]
	lsr x9, x9, #8
	strb w9, [x28, #1025]
	add x0, x28, #960
	movz x1, #0, lsl #0
	movk x1, #8, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	movz x2, #20480, lsl #0
	add x2, x28, x2
	add x3, x28, #3072
	bl {vg_mldsa_expand_mask_poly_sha3}
	b 24f
23:
	movz x0, #20480, lsl #0
	add x0, x28, x0
	movz x1, #9216, lsl #0
	add x1, x28, x1
	movz x2, #128, lsl #0
25:
	ldr x9, [x1, #0]
	str x9, [x0, #0]
	add x0, x0, #8
	add x1, x1, #8
	sub x2, x2, #1
	cbnz x2, 25b
24:
	movz x0, #25600, lsl #0
	add x0, x28, x0
	movz x1, #20480, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_ntt_positive_from}
	movz x0, #26624, lsl #0
	add x0, x28, x0
	movz x1, #50176, lsl #0
	add x1, x28, x1
	movz x2, #21504, lsl #0
	add x2, x28, x2
	add x3, x28, #3072
	bl {vg_mldsa_dot_inverse5}
	movz x0, #27648, lsl #0
	add x0, x28, x0
	movz x1, #55296, lsl #0
	add x1, x28, x1
	movz x2, #21504, lsl #0
	add x2, x28, x2
	add x3, x28, #3072
	bl {vg_mldsa_dot_inverse5}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	movz x1, #60416, lsl #0
	add x1, x28, x1
	movz x2, #21504, lsl #0
	add x2, x28, x2
	add x3, x28, #3072
	bl {vg_mldsa_dot_inverse5}
	movz x0, #29696, lsl #0
	add x0, x28, x0
	movz x1, #0, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	movz x2, #21504, lsl #0
	add x2, x28, x2
	add x3, x28, #3072
	bl {vg_mldsa_dot_inverse5}
	movz x0, #30720, lsl #0
	add x0, x28, x0
	movz x1, #5120, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	movz x2, #21504, lsl #0
	add x2, x28, x2
	add x3, x28, #3072
	bl {vg_mldsa_dot_inverse5}
	movz x0, #31744, lsl #0
	add x0, x28, x0
	movz x1, #10240, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	movz x2, #21504, lsl #0
	add x2, x28, x2
	add x3, x28, #3072
	bl {vg_mldsa_dot_inverse5}
	movz x0, #26624, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_high_pack4}
	movz x0, #27648, lsl #0
	add x0, x28, x0
	add x1, x28, #2176
	bl {vg_mldsa_high_pack4}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	add x1, x28, #2304
	bl {vg_mldsa_high_pack4}
	movz x0, #29696, lsl #0
	add x0, x28, x0
	add x1, x28, #2432
	bl {vg_mldsa_high_pack4}
	movz x0, #30720, lsl #0
	add x0, x28, x0
	add x1, x28, #2560
	bl {vg_mldsa_high_pack4}
	movz x0, #31744, lsl #0
	add x0, x28, x0
	add x1, x28, #2688
	bl {vg_mldsa_high_pack4}
	ldr x9, [x28, #904]
	add x9, x9, #9
	add x0, x26, #0
	add x1, x28, #2048
	add x2, x28, #1040
	movz x3, #6144, lsl #0
	add x3, x28, x3
	add x4, x28, #960
	add x5, x9, #0
	movz x6, #9216, lsl #0
	add x6, x28, x6
	bl {vg_mldsa_commit_tail65}
	add x0, x28, #1040
	movz x1, #48, lsl #0
	movz x2, #49, lsl #0
	movz x3, #5120, lsl #0
	add x3, x28, x3
	add x4, x28, #3072
	bl {vg_mldsa_sample_in_ball_sha3}
	cbnz w0, 26f
	movz x24, #0, lsl #0
	movz x9, #1, lsl #0
	str x9, [x28, #896]
	b 27f
26:
	movz x0, #5120, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	movz x24, #1, lsl #0
	movz x9, #0, lsl #0
	str x9, [x28, #912]
	movz x0, #5120, lsl #0
	add x0, x28, x0
	movz x1, #32768, lsl #0
	add x1, x28, x1
	movz x2, #16384, lsl #0
	add x2, x28, x2
	movz x3, #6144, lsl #0
	add x3, x28, x3
	movz x4, #6144, lsl #0
	add x4, x28, x4
	movz x5, #0, lsl #0
	movk x5, #8, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #65340, lsl #0
	movk x6, #7, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	bl {vg_mldsa_fused_pair_z}
	and w24, w24, w0
	cbnz w24, 28f
	b 29f
28:
	movz x0, #5120, lsl #0
	add x0, x28, x0
	movz x1, #34816, lsl #0
	add x1, x28, x1
	movz x2, #18432, lsl #0
	add x2, x28, x2
	movz x3, #6144, lsl #0
	add x3, x28, x3
	movz x4, #6144, lsl #0
	add x4, x28, x4
	movz x5, #0, lsl #0
	movk x5, #8, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #65340, lsl #0
	movk x6, #7, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	bl {vg_mldsa_fused_pair_z}
	and w24, w24, w0
	cbnz w24, 210f
	b 211f
210:
	movz x0, #6144, lsl #0
	add x0, x28, x0
	movz x1, #5120, lsl #0
	add x1, x28, x1
	movz x2, #36864, lsl #0
	add x2, x28, x2
	add x3, x28, #3072
	bl {vg_mldsa_multiply_inverse_raw}
	movz x0, #20480, lsl #0
	add x0, x28, x0
	movz x1, #6144, lsl #0
	add x1, x28, x1
	movz x2, #65340, lsl #0
	movk x2, #7, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	bl {vg_mldsa_signed_add_norm}
	and w24, w24, w0
211:
29:
	cbnz w24, 212f
	ldr x9, [x28, #904]
	add x9, x9, #5
	str x9, [x28, #904]
	b 213f
212:
	movz x0, #5120, lsl #0
	add x0, x28, x0
	movz x1, #37888, lsl #0
	add x1, x28, x1
	movz x2, #26624, lsl #0
	add x2, x28, x2
	movz x3, #10240, lsl #0
	add x3, x28, x3
	movz x4, #6144, lsl #0
	add x4, x28, x4
	movz x5, #65280, lsl #0
	movk x5, #3, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #65084, lsl #0
	movk x6, #3, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	bl {vg_mldsa_fused_pair_r0}
	and w24, w24, w0
	cbnz w24, 214f
	b 215f
214:
	movz x0, #5120, lsl #0
	add x0, x28, x0
	movz x1, #39936, lsl #0
	add x1, x28, x1
	movz x2, #28672, lsl #0
	add x2, x28, x2
	movz x3, #12288, lsl #0
	add x3, x28, x3
	movz x4, #6144, lsl #0
	add x4, x28, x4
	movz x5, #65280, lsl #0
	movk x5, #3, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #65084, lsl #0
	movk x6, #3, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	bl {vg_mldsa_fused_pair_r0}
	and w24, w24, w0
	cbnz w24, 216f
	b 217f
216:
	movz x0, #5120, lsl #0
	add x0, x28, x0
	movz x1, #41984, lsl #0
	add x1, x28, x1
	movz x2, #30720, lsl #0
	add x2, x28, x2
	movz x3, #14336, lsl #0
	add x3, x28, x3
	movz x4, #6144, lsl #0
	add x4, x28, x4
	movz x5, #65280, lsl #0
	movk x5, #3, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #65084, lsl #0
	movk x6, #3, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	bl {vg_mldsa_fused_pair_r0}
	and w24, w24, w0
	cbnz w24, 218f
	b 219f
218:
219:
217:
215:
	cbnz w24, 220f
	ldr x9, [x28, #904]
	add x9, x9, #5
	str x9, [x28, #904]
	b 221f
220:
	movz x0, #5120, lsl #0
	add x0, x28, x0
	movz x1, #44032, lsl #0
	add x1, x28, x1
	movz x2, #10240, lsl #0
	add x2, x28, x2
	movz x3, #26624, lsl #0
	add x3, x28, x3
	movz x4, #6144, lsl #0
	add x4, x28, x4
	movz x5, #65280, lsl #0
	movk x5, #3, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #65280, lsl #0
	movk x6, #3, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	bl {vg_mldsa_fused_pair_h}
	ldr x9, [x28, #912]
	add w9, w9, w0
	str x9, [x28, #912]
	lsr x0, x0, #32
	and w24, w24, w0
	movz x0, #5120, lsl #0
	add x0, x28, x0
	movz x1, #46080, lsl #0
	add x1, x28, x1
	movz x2, #12288, lsl #0
	add x2, x28, x2
	movz x3, #28672, lsl #0
	add x3, x28, x3
	movz x4, #6144, lsl #0
	add x4, x28, x4
	movz x5, #65280, lsl #0
	movk x5, #3, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #65280, lsl #0
	movk x6, #3, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	bl {vg_mldsa_fused_pair_h}
	ldr x9, [x28, #912]
	add w9, w9, w0
	str x9, [x28, #912]
	lsr x0, x0, #32
	and w24, w24, w0
	movz x0, #5120, lsl #0
	add x0, x28, x0
	movz x1, #48128, lsl #0
	add x1, x28, x1
	movz x2, #14336, lsl #0
	add x2, x28, x2
	movz x3, #30720, lsl #0
	add x3, x28, x3
	movz x4, #6144, lsl #0
	add x4, x28, x4
	movz x5, #65280, lsl #0
	movk x5, #3, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #65280, lsl #0
	movk x6, #3, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	bl {vg_mldsa_fused_pair_h}
	ldr x9, [x28, #912]
	add w9, w9, w0
	str x9, [x28, #912]
	lsr x0, x0, #32
	and w24, w24, w0
	ldr x9, [x28, #912]
	sub x9, x9, #56
	lsr x9, x9, #63
	and w24, w24, w9
	cbnz w24, 222f
	ldr x9, [x28, #904]
	add x9, x9, #5
	str x9, [x28, #904]
	b 223f
222:
	movz x9, #1, lsl #0
	str x9, [x28, #896]
223:
221:
213:
27:
	ldr x9, [x28, #896]
	sub x9, x9, #1
	str x9, [x28, #896]
	cbnz x9, 22b
	cbnz w24, 224f
	b 225f
224:
	movz x0, #16384, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_canonicalize_signed}
	movz x0, #17408, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_canonicalize_signed}
	movz x0, #18432, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_canonicalize_signed}
	movz x0, #19456, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_canonicalize_signed}
	movz x0, #20480, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_canonicalize_signed}
	add x0, x23, #0
	add x1, x28, #1040
	movz x2, #48, lsl #0
226:
	ldrb w9, [x1, #0]
	strb w9, [x0, #0]
	add x0, x0, #1
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 226b
	movz x0, #16384, lsl #0
	add x0, x28, x0
	movz x1, #65535, lsl #0
	movk x1, #7, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	movz x2, #0, lsl #0
	movk x2, #8, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x3, x23, #48
	movz x4, #640, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #17408, lsl #0
	add x0, x28, x0
	movz x1, #65535, lsl #0
	movk x1, #7, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	movz x2, #0, lsl #0
	movk x2, #8, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x3, x23, #688
	movz x4, #640, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #18432, lsl #0
	add x0, x28, x0
	movz x1, #65535, lsl #0
	movk x1, #7, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	movz x2, #0, lsl #0
	movk x2, #8, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x3, x23, #1328
	movz x4, #640, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #19456, lsl #0
	add x0, x28, x0
	movz x1, #65535, lsl #0
	movk x1, #7, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	movz x2, #0, lsl #0
	movk x2, #8, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x3, x23, #1968
	movz x4, #640, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #20480, lsl #0
	add x0, x28, x0
	movz x1, #65535, lsl #0
	movk x1, #7, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	movz x2, #0, lsl #0
	movk x2, #8, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x3, x23, #2608
	movz x4, #640, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #10240, lsl #0
	add x0, x28, x0
	movz x1, #1536, lsl #0
	movz x2, #55, lsl #0
	add x3, x23, #3248
	movz x4, #61, lsl #0
	bl {vg_mldsa_hint_bit_pack}
225:
21:
	add x0, x24, #0
	ldr x23, [x28, #840]
	ldr x24, [x28, #848]
	ldr x25, [x28, #856]
	ldr x26, [x28, #864]
	ldr x27, [x28, #872]
	ldr x30, [x28, #880]
	ldr x28, [x28, #888]
	ret
	.arch_extension nosha3
	.p2align 6

vg_mldsa65_sign_message_sha3:
	.arch_extension sha3
	lsr x9, x4, #8
	cbnz x9, 20f
	movz x9, #37888, lsl #0
	movk x9, #1, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	add x9, x7, x9
	str x28, [x9, #904]
	str x30, [x9, #912]
	add x28, x9, #0
	str x0, [x28, #920]
	str x1, [x28, #928]
	str x2, [x28, #936]
	str x3, [x28, #944]
	str x4, [x28, #952]
	str x5, [x28, #960]
	str x6, [x28, #968]
	str x7, [x28, #976]
	movz x9, #0, lsl #0
	strb w9, [x28, #984]
	strb w4, [x28, #985]
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
	movz x2, #0, lsl #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	ldr x3, [x28, #920]
	add x3, x3, #64
	movz x4, #64, lsl #0
	add x5, x28, #200
	bl {vg_keccak_absorb_scratch_sha3}
	movz x2, #64, lsl #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x3, x28, #984
	movz x4, #2, lsl #0
	add x5, x28, #200
	bl {vg_keccak_absorb_scratch_sha3}
	movz x2, #66, lsl #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	ldr x3, [x28, #944]
	ldr x4, [x28, #952]
	add x5, x28, #200
	bl {vg_keccak_absorb_scratch_sha3}
	add x2, x0, #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	ldr x3, [x28, #928]
	ldr x4, [x28, #936]
	add x5, x28, #200
	bl {vg_keccak_absorb_scratch_sha3}
	add x2, x0, #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	movz x3, #31, lsl #0
	add x4, x28, #200
	bl {vg_keccak_pad_scratch_sha3}
	add x0, x28, #0
	movz x1, #136, lsl #0
	movz x2, #0, lsl #0
	add x3, x28, #840
	movz x4, #64, lsl #0
	add x5, x28, #200
	bl {vg_keccak_squeeze_scratch_sha3}
	ldr x0, [x28, #920]
	add x1, x28, #840
	ldr x2, [x28, #960]
	ldr x3, [x28, #968]
	ldr x4, [x28, #976]
	bl {vg_mldsa65_sign_sha3}
	ldr x30, [x28, #912]
	ldr x28, [x28, #904]
	b 21f
20:
	movz x0, #2, lsl #0
21:
	ret
	.arch_extension nosha3
	.p2align 6

vg_mldsa65_verify_sha3:
	.arch_extension sha3
	str x24, [x3, #840]
	str x25, [x3, #848]
	str x26, [x3, #856]
	str x27, [x3, #864]
	str x28, [x3, #872]
	str x30, [x3, #880]
	add x25, x0, #0
	add x26, x1, #0
	add x27, x2, #0
	add x28, x3, #0
	movz x24, #1, lsl #0
	add x0, x27, #3248
	movz x1, #61, lsl #0
	movz x2, #55, lsl #0
	movz x3, #35840, lsl #0
	add x3, x28, x3
	movz x4, #1536, lsl #0
	bl {vg_mldsa_hint_bit_unpack}
	and w24, w24, w0
	cbnz x24, 20f
	b 21f
20:
	add x0, x27, #48
	movz x1, #640, lsl #0
	movz x2, #65535, lsl #0
	movk x2, #7, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	movz x3, #0, lsl #0
	movk x3, #8, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	movz x4, #41984, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #41984, lsl #0
	add x0, x28, x0
	movz x1, #65340, lsl #0
	movk x1, #7, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	bl {vg_mldsa_norm_lt}
	and w24, w24, w0
	add x0, x27, #688
	movz x1, #640, lsl #0
	movz x2, #65535, lsl #0
	movk x2, #7, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	movz x3, #0, lsl #0
	movk x3, #8, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	movz x4, #43008, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #43008, lsl #0
	add x0, x28, x0
	movz x1, #65340, lsl #0
	movk x1, #7, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	bl {vg_mldsa_norm_lt}
	and w24, w24, w0
	add x0, x27, #1328
	movz x1, #640, lsl #0
	movz x2, #65535, lsl #0
	movk x2, #7, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	movz x3, #0, lsl #0
	movk x3, #8, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	movz x4, #44032, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #44032, lsl #0
	add x0, x28, x0
	movz x1, #65340, lsl #0
	movk x1, #7, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	bl {vg_mldsa_norm_lt}
	and w24, w24, w0
	add x0, x27, #1968
	movz x1, #640, lsl #0
	movz x2, #65535, lsl #0
	movk x2, #7, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	movz x3, #0, lsl #0
	movk x3, #8, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	movz x4, #45056, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #45056, lsl #0
	add x0, x28, x0
	movz x1, #65340, lsl #0
	movk x1, #7, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	bl {vg_mldsa_norm_lt}
	and w24, w24, w0
	add x0, x27, #2608
	movz x1, #640, lsl #0
	movz x2, #65535, lsl #0
	movk x2, #7, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	movz x3, #0, lsl #0
	movk x3, #8, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	movz x4, #46080, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #65340, lsl #0
	movk x1, #7, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	bl {vg_mldsa_norm_lt}
	and w24, w24, w0
	cbnz x24, 22f
	b 23f
22:
	ldr x9, [x25, #0]
	str x9, [x28, #1152]
	ldr x9, [x25, #8]
	str x9, [x28, #1160]
	ldr x9, [x25, #16]
	str x9, [x28, #1168]
	ldr x9, [x25, #24]
	str x9, [x28, #1176]
	add x10, x28, #1408
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #0, lsl #0
	strb w9, [x28, #1440]
	movz x9, #0, lsl #0
	strb w9, [x28, #1441]
	add x10, x28, #1442
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #1, lsl #0
	strb w9, [x28, #1474]
	movz x9, #0, lsl #0
	strb w9, [x28, #1475]
	add x10, x28, #1476
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #2, lsl #0
	strb w9, [x28, #1508]
	movz x9, #0, lsl #0
	strb w9, [x28, #1509]
	add x10, x28, #1510
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #3, lsl #0
	strb w9, [x28, #1542]
	movz x9, #0, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #4096, lsl #0
	add x1, x28, x1
	movz x2, #49152, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4_sha3}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	dup v0.4s, w8
	movz x1, #4096, lsl #0
	add x1, x28, x1
	movz x2, #64, lsl #0
24:
	ldr q1, [x1, #0]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #0]
	ldr q1, [x1, #16]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #16]
	ldr q1, [x1, #32]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #32]
	ldr q1, [x1, #48]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #48]
	add x1, x1, #64
	sub x2, x2, #1
	cbnz x2, 24b
	add x10, x28, #1408
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #4, lsl #0
	strb w9, [x28, #1440]
	movz x9, #0, lsl #0
	strb w9, [x28, #1441]
	add x10, x28, #1442
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #0, lsl #0
	strb w9, [x28, #1474]
	movz x9, #1, lsl #0
	strb w9, [x28, #1475]
	add x10, x28, #1476
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #1, lsl #0
	strb w9, [x28, #1508]
	movz x9, #1, lsl #0
	strb w9, [x28, #1509]
	add x10, x28, #1510
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #2, lsl #0
	strb w9, [x28, #1542]
	movz x9, #1, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #8192, lsl #0
	add x1, x28, x1
	movz x2, #49152, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4_sha3}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	dup v0.4s, w8
	movz x1, #8192, lsl #0
	add x1, x28, x1
	movz x2, #64, lsl #0
25:
	ldr q1, [x1, #0]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #0]
	ldr q1, [x1, #16]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #16]
	ldr q1, [x1, #32]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #32]
	ldr q1, [x1, #48]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #48]
	add x1, x1, #64
	sub x2, x2, #1
	cbnz x2, 25b
	add x10, x28, #1408
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #3, lsl #0
	strb w9, [x28, #1440]
	movz x9, #1, lsl #0
	strb w9, [x28, #1441]
	add x10, x28, #1442
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #4, lsl #0
	strb w9, [x28, #1474]
	movz x9, #1, lsl #0
	strb w9, [x28, #1475]
	add x10, x28, #1476
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #0, lsl #0
	strb w9, [x28, #1508]
	movz x9, #2, lsl #0
	strb w9, [x28, #1509]
	add x10, x28, #1510
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #1, lsl #0
	strb w9, [x28, #1542]
	movz x9, #2, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #12288, lsl #0
	add x1, x28, x1
	movz x2, #49152, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4_sha3}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	dup v0.4s, w8
	movz x1, #12288, lsl #0
	add x1, x28, x1
	movz x2, #64, lsl #0
26:
	ldr q1, [x1, #0]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #0]
	ldr q1, [x1, #16]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #16]
	ldr q1, [x1, #32]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #32]
	ldr q1, [x1, #48]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #48]
	add x1, x1, #64
	sub x2, x2, #1
	cbnz x2, 26b
	add x10, x28, #1408
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #2, lsl #0
	strb w9, [x28, #1440]
	movz x9, #2, lsl #0
	strb w9, [x28, #1441]
	add x10, x28, #1442
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #3, lsl #0
	strb w9, [x28, #1474]
	movz x9, #2, lsl #0
	strb w9, [x28, #1475]
	add x10, x28, #1476
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #4, lsl #0
	strb w9, [x28, #1508]
	movz x9, #2, lsl #0
	strb w9, [x28, #1509]
	add x10, x28, #1510
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #0, lsl #0
	strb w9, [x28, #1542]
	movz x9, #3, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #16384, lsl #0
	add x1, x28, x1
	movz x2, #49152, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4_sha3}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	dup v0.4s, w8
	movz x1, #16384, lsl #0
	add x1, x28, x1
	movz x2, #64, lsl #0
27:
	ldr q1, [x1, #0]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #0]
	ldr q1, [x1, #16]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #16]
	ldr q1, [x1, #32]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #32]
	ldr q1, [x1, #48]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #48]
	add x1, x1, #64
	sub x2, x2, #1
	cbnz x2, 27b
	add x10, x28, #1408
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #1, lsl #0
	strb w9, [x28, #1440]
	movz x9, #3, lsl #0
	strb w9, [x28, #1441]
	add x10, x28, #1442
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #2, lsl #0
	strb w9, [x28, #1474]
	movz x9, #3, lsl #0
	strb w9, [x28, #1475]
	add x10, x28, #1476
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #3, lsl #0
	strb w9, [x28, #1508]
	movz x9, #3, lsl #0
	strb w9, [x28, #1509]
	add x10, x28, #1510
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #4, lsl #0
	strb w9, [x28, #1542]
	movz x9, #3, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #20480, lsl #0
	add x1, x28, x1
	movz x2, #49152, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4_sha3}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	dup v0.4s, w8
	movz x1, #20480, lsl #0
	add x1, x28, x1
	movz x2, #64, lsl #0
28:
	ldr q1, [x1, #0]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #0]
	ldr q1, [x1, #16]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #16]
	ldr q1, [x1, #32]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #32]
	ldr q1, [x1, #48]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #48]
	add x1, x1, #64
	sub x2, x2, #1
	cbnz x2, 28b
	add x10, x28, #1408
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #0, lsl #0
	strb w9, [x28, #1440]
	movz x9, #4, lsl #0
	strb w9, [x28, #1441]
	add x10, x28, #1442
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #1, lsl #0
	strb w9, [x28, #1474]
	movz x9, #4, lsl #0
	strb w9, [x28, #1475]
	add x10, x28, #1476
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #2, lsl #0
	strb w9, [x28, #1508]
	movz x9, #4, lsl #0
	strb w9, [x28, #1509]
	add x10, x28, #1510
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #3, lsl #0
	strb w9, [x28, #1542]
	movz x9, #4, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #24576, lsl #0
	add x1, x28, x1
	movz x2, #49152, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4_sha3}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	dup v0.4s, w8
	movz x1, #24576, lsl #0
	add x1, x28, x1
	movz x2, #64, lsl #0
29:
	ldr q1, [x1, #0]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #0]
	ldr q1, [x1, #16]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #16]
	ldr q1, [x1, #32]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #32]
	ldr q1, [x1, #48]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #48]
	add x1, x1, #64
	sub x2, x2, #1
	cbnz x2, 29b
	add x10, x28, #1408
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #4, lsl #0
	strb w9, [x28, #1440]
	movz x9, #4, lsl #0
	strb w9, [x28, #1441]
	add x10, x28, #1442
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #0, lsl #0
	strb w9, [x28, #1474]
	movz x9, #5, lsl #0
	strb w9, [x28, #1475]
	add x10, x28, #1476
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #1, lsl #0
	strb w9, [x28, #1508]
	movz x9, #5, lsl #0
	strb w9, [x28, #1509]
	add x10, x28, #1510
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #2, lsl #0
	strb w9, [x28, #1542]
	movz x9, #5, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #28672, lsl #0
	add x1, x28, x1
	movz x2, #49152, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4_sha3}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	dup v0.4s, w8
	movz x1, #28672, lsl #0
	add x1, x28, x1
	movz x2, #64, lsl #0
210:
	ldr q1, [x1, #0]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #0]
	ldr q1, [x1, #16]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #16]
	ldr q1, [x1, #32]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #32]
	ldr q1, [x1, #48]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #48]
	add x1, x1, #64
	sub x2, x2, #1
	cbnz x2, 210b
	add x10, x28, #1408
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #3, lsl #0
	strb w9, [x28, #1440]
	movz x9, #5, lsl #0
	strb w9, [x28, #1441]
	add x10, x28, #1442
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #4, lsl #0
	strb w9, [x28, #1474]
	movz x9, #5, lsl #0
	strb w9, [x28, #1475]
	add x0, x28, #1408
	movz x1, #32768, lsl #0
	add x1, x28, x1
	movz x2, #49152, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly2_sha3}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	dup v0.4s, w8
	movz x1, #32768, lsl #0
	add x1, x28, x1
	movz x2, #32, lsl #0
211:
	ldr q1, [x1, #0]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #0]
	ldr q1, [x1, #16]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #16]
	ldr q1, [x1, #32]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #32]
	ldr q1, [x1, #48]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #48]
	add x1, x1, #64
	sub x2, x2, #1
	cbnz x2, 211b
	add x0, x27, #0
	movz x1, #48, lsl #0
	movz x2, #49, lsl #0
	movz x3, #47104, lsl #0
	add x3, x28, x3
	add x4, x28, #2048
	bl {vg_mldsa_sample_in_ball_sha3}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	dup v0.4s, w8
	movz x1, #47104, lsl #0
	add x1, x28, x1
	movz x2, #16, lsl #0
212:
	ldr q1, [x1, #0]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #0]
	ldr q1, [x1, #16]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #16]
	ldr q1, [x1, #32]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #32]
	ldr q1, [x1, #48]
	and v1.16b, v1.16b, v0.16b
	str q1, [x1, #48]
	add x1, x1, #64
	sub x2, x2, #1
	cbnz x2, 212b
	movz x0, #41984, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	movz x0, #43008, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	movz x0, #44032, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	movz x0, #45056, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	movz x0, #47104, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #4096, lsl #0
	add x1, x28, x1
	movz x2, #41984, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_montgomery_dot5}
	add x0, x25, #32
	movz x1, #48128, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_unpack_t1}
	movz x0, #48128, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	movz x0, #49152, lsl #0
	add x0, x28, x0
	movz x1, #47104, lsl #0
	add x1, x28, x1
	movz x2, #48128, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_montgomery_product}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #49152, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_sub}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_montgomery_inv_ntt}
	movz x0, #34816, lsl #0
	add x0, x28, x0
	movz x1, #35840, lsl #0
	add x1, x28, x1
	movz x2, #50176, lsl #0
	add x2, x28, x2
	movz x3, #65280, lsl #0
	movk x3, #3, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	bl {vg_mldsa_usehint_pack4}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #9216, lsl #0
	add x1, x28, x1
	movz x2, #41984, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_montgomery_dot5}
	add x0, x25, #352
	movz x1, #48128, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_unpack_t1}
	movz x0, #48128, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	movz x0, #49152, lsl #0
	add x0, x28, x0
	movz x1, #47104, lsl #0
	add x1, x28, x1
	movz x2, #48128, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_montgomery_product}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #49152, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_sub}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_montgomery_inv_ntt}
	movz x0, #34944, lsl #0
	add x0, x28, x0
	movz x1, #36864, lsl #0
	add x1, x28, x1
	movz x2, #50176, lsl #0
	add x2, x28, x2
	movz x3, #65280, lsl #0
	movk x3, #3, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	bl {vg_mldsa_usehint_pack4}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #14336, lsl #0
	add x1, x28, x1
	movz x2, #41984, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_montgomery_dot5}
	add x0, x25, #672
	movz x1, #48128, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_unpack_t1}
	movz x0, #48128, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	movz x0, #49152, lsl #0
	add x0, x28, x0
	movz x1, #47104, lsl #0
	add x1, x28, x1
	movz x2, #48128, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_montgomery_product}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #49152, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_sub}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_montgomery_inv_ntt}
	movz x0, #35072, lsl #0
	add x0, x28, x0
	movz x1, #37888, lsl #0
	add x1, x28, x1
	movz x2, #50176, lsl #0
	add x2, x28, x2
	movz x3, #65280, lsl #0
	movk x3, #3, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	bl {vg_mldsa_usehint_pack4}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #19456, lsl #0
	add x1, x28, x1
	movz x2, #41984, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_montgomery_dot5}
	add x0, x25, #992
	movz x1, #48128, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_unpack_t1}
	movz x0, #48128, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	movz x0, #49152, lsl #0
	add x0, x28, x0
	movz x1, #47104, lsl #0
	add x1, x28, x1
	movz x2, #48128, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_montgomery_product}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #49152, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_sub}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_montgomery_inv_ntt}
	movz x0, #35200, lsl #0
	add x0, x28, x0
	movz x1, #38912, lsl #0
	add x1, x28, x1
	movz x2, #50176, lsl #0
	add x2, x28, x2
	movz x3, #65280, lsl #0
	movk x3, #3, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	bl {vg_mldsa_usehint_pack4}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #24576, lsl #0
	add x1, x28, x1
	movz x2, #41984, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_montgomery_dot5}
	add x0, x25, #1312
	movz x1, #48128, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_unpack_t1}
	movz x0, #48128, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	movz x0, #49152, lsl #0
	add x0, x28, x0
	movz x1, #47104, lsl #0
	add x1, x28, x1
	movz x2, #48128, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_montgomery_product}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #49152, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_sub}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_montgomery_inv_ntt}
	movz x0, #35328, lsl #0
	add x0, x28, x0
	movz x1, #39936, lsl #0
	add x1, x28, x1
	movz x2, #50176, lsl #0
	add x2, x28, x2
	movz x3, #65280, lsl #0
	movk x3, #3, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	bl {vg_mldsa_usehint_pack4}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #29696, lsl #0
	add x1, x28, x1
	movz x2, #41984, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_montgomery_dot5}
	add x0, x25, #1632
	movz x1, #48128, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_unpack_t1}
	movz x0, #48128, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	movz x0, #49152, lsl #0
	add x0, x28, x0
	movz x1, #47104, lsl #0
	add x1, x28, x1
	movz x2, #48128, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_montgomery_product}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	movz x1, #49152, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_sub}
	movz x0, #50176, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_montgomery_inv_ntt}
	movz x0, #35456, lsl #0
	add x0, x28, x0
	movz x1, #40960, lsl #0
	add x1, x28, x1
	movz x2, #50176, lsl #0
	add x2, x28, x2
	movz x3, #65280, lsl #0
	movk x3, #3, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	bl {vg_mldsa_usehint_pack4}
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
	movz x2, #0, lsl #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x5, x28, #200
	add x3, x26, #0
	movz x4, #64, lsl #0
	bl {vg_keccak_absorb_scratch_sha3}
	add x2, x0, #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x5, x28, #200
	movz x3, #34816, lsl #0
	add x3, x28, x3
	movz x4, #768, lsl #0
	bl {vg_keccak_absorb_scratch_sha3}
	add x2, x0, #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x4, x28, #200
	movz x3, #31, lsl #0
	bl {vg_keccak_pad_scratch_sha3}
	movz x2, #0, lsl #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x5, x28, #200
	add x3, x28, #1024
	movz x4, #48, lsl #0
	bl {vg_keccak_squeeze_scratch_sha3}
	add x0, x28, #1024
	add x1, x27, #0
	movz x2, #48, lsl #0
	movz x10, #0, lsl #0
213:
	ldrb w9, [x0, #0]
	ldrb w11, [x1, #0]
	eor x9, x9, x11
	orr x10, x10, x9
	add x0, x0, #1
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 213b
	sub x10, x10, #1
	lsr x10, x10, #63
	and w24, w24, w10
23:
21:
	add x0, x24, #0
	ldr x30, [x28, #880]
	ldr x24, [x28, #840]
	ldr x25, [x28, #848]
	ldr x26, [x28, #856]
	ldr x27, [x28, #864]
	ldr x28, [x28, #872]
	ret
	.arch_extension nosha3
	.p2align 6

vg_mldsa65_verify_message_cached_sha3:
	.arch_extension sha3
	lsr x9, x4, #8
	cbnz x9, 20f
	movz x9, #37888, lsl #0
	movk x9, #1, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	add x9, x6, x9
	str x28, [x9, #904]
	str x30, [x9, #912]
	add x28, x9, #0
	str x0, [x28, #920]
	str x1, [x28, #928]
	str x2, [x28, #936]
	str x3, [x28, #944]
	str x4, [x28, #952]
	str x7, [x28, #960]
	str x5, [x28, #968]
	str x6, [x28, #976]
	movz x9, #0, lsl #0
	strb w9, [x28, #984]
	strb w4, [x28, #985]
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
	movz x2, #0, lsl #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	ldr x3, [x28, #960]
	movz x4, #64, lsl #0
	add x5, x28, #200
	bl {vg_keccak_absorb_scratch_sha3}
	movz x2, #64, lsl #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x3, x28, #984
	movz x4, #2, lsl #0
	add x5, x28, #200
	bl {vg_keccak_absorb_scratch_sha3}
	movz x2, #66, lsl #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	ldr x3, [x28, #944]
	ldr x4, [x28, #952]
	add x5, x28, #200
	bl {vg_keccak_absorb_scratch_sha3}
	add x2, x0, #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	ldr x3, [x28, #928]
	ldr x4, [x28, #936]
	add x5, x28, #200
	bl {vg_keccak_absorb_scratch_sha3}
	add x2, x0, #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	movz x3, #31, lsl #0
	add x4, x28, #200
	bl {vg_keccak_pad_scratch_sha3}
	add x0, x28, #0
	movz x1, #136, lsl #0
	movz x2, #0, lsl #0
	add x3, x28, #840
	movz x4, #64, lsl #0
	add x5, x28, #200
	bl {vg_keccak_squeeze_scratch_sha3}
	ldr x0, [x28, #920]
	add x1, x28, #840
	ldr x2, [x28, #968]
	ldr x3, [x28, #976]
	bl {vg_mldsa65_verify_sha3}
	ldr x30, [x28, #912]
	ldr x28, [x28, #904]
	b 21f
20:
	movz x0, #2, lsl #0
21:
	ret
	.arch_extension nosha3
	.p2align 6
