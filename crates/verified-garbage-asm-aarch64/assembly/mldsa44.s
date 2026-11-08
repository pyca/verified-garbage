// The functions of `src/mldsa44.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa44_keygen_sha3:
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
	movz x9, #4, lsl #0
	strb w9, [x28, #896]
	movz x9, #4, lsl #0
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
	movz x2, #31744, lsl #0
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
	movz x9, #0, lsl #0
	strb w9, [x28, #1440]
	movz x9, #1, lsl #0
	strb w9, [x28, #1441]
	movz x9, #1, lsl #0
	strb w9, [x28, #1474]
	movz x9, #1, lsl #0
	strb w9, [x28, #1475]
	movz x9, #2, lsl #0
	strb w9, [x28, #1508]
	movz x9, #1, lsl #0
	strb w9, [x28, #1509]
	movz x9, #3, lsl #0
	strb w9, [x28, #1542]
	movz x9, #1, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #8192, lsl #0
	add x1, x28, x1
	movz x2, #31744, lsl #0
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
	movz x9, #0, lsl #0
	strb w9, [x28, #1440]
	movz x9, #2, lsl #0
	strb w9, [x28, #1441]
	movz x9, #1, lsl #0
	strb w9, [x28, #1474]
	movz x9, #2, lsl #0
	strb w9, [x28, #1475]
	movz x9, #2, lsl #0
	strb w9, [x28, #1508]
	movz x9, #2, lsl #0
	strb w9, [x28, #1509]
	movz x9, #3, lsl #0
	strb w9, [x28, #1542]
	movz x9, #2, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #12288, lsl #0
	add x1, x28, x1
	movz x2, #31744, lsl #0
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
	movz x9, #0, lsl #0
	strb w9, [x28, #1440]
	movz x9, #3, lsl #0
	strb w9, [x28, #1441]
	movz x9, #1, lsl #0
	strb w9, [x28, #1474]
	movz x9, #3, lsl #0
	strb w9, [x28, #1475]
	movz x9, #2, lsl #0
	strb w9, [x28, #1508]
	movz x9, #3, lsl #0
	strb w9, [x28, #1509]
	movz x9, #3, lsl #0
	strb w9, [x28, #1542]
	movz x9, #3, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #16384, lsl #0
	add x1, x28, x1
	movz x2, #31744, lsl #0
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
	movz x1, #20480, lsl #0
	add x1, x28, x1
	movz x2, #31744, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_rej_bounded_poly4_eta2_sha3}
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
	movz x1, #24576, lsl #0
	add x1, x28, x1
	movz x2, #31744, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_rej_bounded_poly4_eta2_sha3}
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
	movz x0, #20480, lsl #0
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #128
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #21504, lsl #0
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #224
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #22528, lsl #0
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #320
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #23552, lsl #0
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #416
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #24576, lsl #0
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #512
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #25600, lsl #0
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #608
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #26624, lsl #0
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #704
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #27648, lsl #0
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #800
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #20480, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	movz x0, #21504, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	movz x0, #22528, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	movz x0, #23552, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	movz x1, #4096, lsl #0
	add x1, x28, x1
	movz x2, #20480, lsl #0
	add x2, x28, x2
	add x3, x28, #2048
	bl {vg_mldsa_dot_inverse4}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	movz x1, #24576, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_add}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	movz x1, #29696, lsl #0
	add x1, x28, x1
	movz x2, #30720, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_power2round}
	movz x0, #29696, lsl #0
	add x0, x28, x0
	movz x1, #1023, lsl #0
	add x2, x26, #32
	movz x3, #320, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #30720, lsl #0
	add x0, x28, x0
	movz x1, #4095, lsl #0
	movz x2, #4096, lsl #0
	add x3, x27, #896
	movz x4, #416, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	movz x1, #8192, lsl #0
	add x1, x28, x1
	movz x2, #20480, lsl #0
	add x2, x28, x2
	add x3, x28, #2048
	bl {vg_mldsa_dot_inverse4}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	movz x1, #25600, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_add}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	movz x1, #29696, lsl #0
	add x1, x28, x1
	movz x2, #30720, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_power2round}
	movz x0, #29696, lsl #0
	add x0, x28, x0
	movz x1, #1023, lsl #0
	add x2, x26, #352
	movz x3, #320, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #30720, lsl #0
	add x0, x28, x0
	movz x1, #4095, lsl #0
	movz x2, #4096, lsl #0
	add x3, x27, #1312
	movz x4, #416, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	movz x1, #12288, lsl #0
	add x1, x28, x1
	movz x2, #20480, lsl #0
	add x2, x28, x2
	add x3, x28, #2048
	bl {vg_mldsa_dot_inverse4}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	movz x1, #26624, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_add}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	movz x1, #29696, lsl #0
	add x1, x28, x1
	movz x2, #30720, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_power2round}
	movz x0, #29696, lsl #0
	add x0, x28, x0
	movz x1, #1023, lsl #0
	add x2, x26, #672
	movz x3, #320, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #30720, lsl #0
	add x0, x28, x0
	movz x1, #4095, lsl #0
	movz x2, #4096, lsl #0
	add x3, x27, #1728
	movz x4, #416, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	movz x1, #16384, lsl #0
	add x1, x28, x1
	movz x2, #20480, lsl #0
	add x2, x28, x2
	add x3, x28, #2048
	bl {vg_mldsa_dot_inverse4}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	movz x1, #27648, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_add}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	movz x1, #29696, lsl #0
	add x1, x28, x1
	movz x2, #30720, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_power2round}
	movz x0, #29696, lsl #0
	add x0, x28, x0
	movz x1, #1023, lsl #0
	add x2, x26, #992
	movz x3, #320, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #30720, lsl #0
	add x0, x28, x0
	movz x1, #4095, lsl #0
	movz x2, #4096, lsl #0
	add x3, x27, #2144
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
	movz x4, #1312, lsl #0
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
	.p2align 6

vg_mldsa44_keygen:
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
	movz x9, #4, lsl #0
	strb w9, [x28, #896]
	movz x9, #4, lsl #0
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
	movz x2, #31744, lsl #0
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
	movz x9, #0, lsl #0
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
	movz x9, #1, lsl #0
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
	movz x9, #2, lsl #0
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
	movz x9, #3, lsl #0
	strb w9, [x28, #1542]
	movz x9, #1, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #8192, lsl #0
	add x1, x28, x1
	movz x2, #31744, lsl #0
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
	movz x9, #0, lsl #0
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
	movz x9, #1, lsl #0
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
	movz x9, #2, lsl #0
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
	movz x9, #3, lsl #0
	strb w9, [x28, #1542]
	movz x9, #2, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #12288, lsl #0
	add x1, x28, x1
	movz x2, #31744, lsl #0
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
	movz x9, #0, lsl #0
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
	movz x9, #1, lsl #0
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
	movz x9, #2, lsl #0
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
	movz x9, #3, lsl #0
	strb w9, [x28, #1542]
	movz x9, #3, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #16384, lsl #0
	add x1, x28, x1
	movz x2, #31744, lsl #0
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
	movz x1, #20480, lsl #0
	add x1, x28, x1
	movz x2, #31744, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_rej_bounded_poly4_eta2}
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
	movz x1, #24576, lsl #0
	add x1, x28, x1
	movz x2, #31744, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_rej_bounded_poly4_eta2}
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
	movz x0, #20480, lsl #0
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #128
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #21504, lsl #0
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #224
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #22528, lsl #0
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #320
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #23552, lsl #0
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #416
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #24576, lsl #0
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #512
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #25600, lsl #0
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #608
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #26624, lsl #0
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #704
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #27648, lsl #0
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #800
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #20480, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_ntt}
	movz x0, #21504, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_ntt}
	movz x0, #22528, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_ntt}
	movz x0, #23552, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_ntt}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	movz x1, #4096, lsl #0
	add x1, x28, x1
	movz x2, #20480, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_ntt}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	movz x1, #5120, lsl #0
	add x1, x28, x1
	movz x2, #21504, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	movz x1, #6144, lsl #0
	add x1, x28, x1
	movz x2, #22528, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	movz x1, #7168, lsl #0
	add x1, x28, x1
	movz x2, #23552, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_inv_ntt}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	movz x1, #24576, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_add}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	movz x1, #29696, lsl #0
	add x1, x28, x1
	movz x2, #30720, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_power2round}
	movz x0, #29696, lsl #0
	add x0, x28, x0
	movz x1, #1023, lsl #0
	add x2, x26, #32
	movz x3, #320, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #30720, lsl #0
	add x0, x28, x0
	movz x1, #4095, lsl #0
	movz x2, #4096, lsl #0
	add x3, x27, #896
	movz x4, #416, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	movz x1, #8192, lsl #0
	add x1, x28, x1
	movz x2, #20480, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_ntt}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	movz x1, #9216, lsl #0
	add x1, x28, x1
	movz x2, #21504, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	movz x1, #10240, lsl #0
	add x1, x28, x1
	movz x2, #22528, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	movz x1, #11264, lsl #0
	add x1, x28, x1
	movz x2, #23552, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_inv_ntt}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	movz x1, #25600, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_add}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	movz x1, #29696, lsl #0
	add x1, x28, x1
	movz x2, #30720, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_power2round}
	movz x0, #29696, lsl #0
	add x0, x28, x0
	movz x1, #1023, lsl #0
	add x2, x26, #352
	movz x3, #320, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #30720, lsl #0
	add x0, x28, x0
	movz x1, #4095, lsl #0
	movz x2, #4096, lsl #0
	add x3, x27, #1312
	movz x4, #416, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	movz x1, #12288, lsl #0
	add x1, x28, x1
	movz x2, #20480, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_ntt}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	movz x1, #13312, lsl #0
	add x1, x28, x1
	movz x2, #21504, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	movz x1, #14336, lsl #0
	add x1, x28, x1
	movz x2, #22528, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	movz x1, #15360, lsl #0
	add x1, x28, x1
	movz x2, #23552, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_inv_ntt}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	movz x1, #26624, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_add}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	movz x1, #29696, lsl #0
	add x1, x28, x1
	movz x2, #30720, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_power2round}
	movz x0, #29696, lsl #0
	add x0, x28, x0
	movz x1, #1023, lsl #0
	add x2, x26, #672
	movz x3, #320, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #30720, lsl #0
	add x0, x28, x0
	movz x1, #4095, lsl #0
	movz x2, #4096, lsl #0
	add x3, x27, #1728
	movz x4, #416, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	movz x1, #16384, lsl #0
	add x1, x28, x1
	movz x2, #20480, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_ntt}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	movz x1, #17408, lsl #0
	add x1, x28, x1
	movz x2, #21504, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	movz x1, #18432, lsl #0
	add x1, x28, x1
	movz x2, #22528, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	movz x1, #19456, lsl #0
	add x1, x28, x1
	movz x2, #23552, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_inv_ntt}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	movz x1, #27648, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_add}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	movz x1, #29696, lsl #0
	add x1, x28, x1
	movz x2, #30720, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_power2round}
	movz x0, #29696, lsl #0
	add x0, x28, x0
	movz x1, #1023, lsl #0
	add x2, x26, #992
	movz x3, #320, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #30720, lsl #0
	add x0, x28, x0
	movz x1, #4095, lsl #0
	movz x2, #4096, lsl #0
	add x3, x27, #2144
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
	movz x4, #1312, lsl #0
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

vg_mldsa44_pk_tr_sha3:
	add x3, x2, #0
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
	movz x4, #1312, lsl #0
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
	add x3, x26, #0
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
	.p2align 6

vg_mldsa44_pk_tr:
	add x3, x2, #0
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
	movz x4, #1312, lsl #0
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
	add x3, x26, #0
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

vg_mldsa44_prepare_verifying_key:
	str x25, [sp, #-16]!
	str x26, [sp, #-16]!
	str x28, [sp, #-16]!
	str x30, [sp, #-16]!
	add x25, x0, #0
	add x26, x1, #0
	add x28, x2, #0
	add x0, x26, #0
	add x1, x25, #0
	movz x2, #82, lsl #0
20:
	ldr q0, [x1, #0]
	str q0, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x2, x2, #1
	cbnz x2, 20b
	add x0, x25, #32
	add x1, x26, #1312
	bl {vg_mldsa_unpack_t1}
	add x0, x26, #1312
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	add x0, x25, #352
	add x1, x26, #2336
	bl {vg_mldsa_unpack_t1}
	add x0, x26, #2336
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	add x0, x25, #672
	add x1, x26, #3360
	bl {vg_mldsa_unpack_t1}
	add x0, x26, #3360
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	add x0, x25, #992
	movz x1, #4384, lsl #0
	add x1, x26, x1
	bl {vg_mldsa_unpack_t1}
	movz x0, #4384, lsl #0
	add x0, x26, x0
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	ldr x30, [sp], #16
	ldr x28, [sp], #16
	ldr x26, [sp], #16
	ldr x25, [sp], #16
	ret
	.p2align 6

vg_mldsa44_prepare_signing_key:
	str x25, [sp, #-16]!
	str x26, [sp, #-16]!
	str x28, [sp, #-16]!
	str x30, [sp, #-16]!
	add x25, x0, #0
	add x26, x1, #0
	add x28, x2, #0
	add x0, x26, #0
	add x1, x25, #0
	movz x2, #160, lsl #0
20:
	ldr q0, [x1, #0]
	str q0, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x2, x2, #1
	cbnz x2, 20b
	add x0, x25, #128
	movz x1, #96, lsl #0
	movz x2, #2, lsl #0
	movz x3, #2, lsl #0
	add x4, x26, #2560
	bl {vg_mldsa_bit_unpack}
	add x0, x26, #2560
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	add x0, x25, #224
	movz x1, #96, lsl #0
	movz x2, #2, lsl #0
	movz x3, #2, lsl #0
	add x4, x26, #3584
	bl {vg_mldsa_bit_unpack}
	add x0, x26, #3584
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	add x0, x25, #320
	movz x1, #96, lsl #0
	movz x2, #2, lsl #0
	movz x3, #2, lsl #0
	movz x4, #4608, lsl #0
	add x4, x26, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #4608, lsl #0
	add x0, x26, x0
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	add x0, x25, #416
	movz x1, #96, lsl #0
	movz x2, #2, lsl #0
	movz x3, #2, lsl #0
	movz x4, #5632, lsl #0
	add x4, x26, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #5632, lsl #0
	add x0, x26, x0
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	add x0, x25, #512
	movz x1, #96, lsl #0
	movz x2, #2, lsl #0
	movz x3, #2, lsl #0
	movz x4, #6656, lsl #0
	add x4, x26, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #6656, lsl #0
	add x0, x26, x0
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	add x0, x25, #608
	movz x1, #96, lsl #0
	movz x2, #2, lsl #0
	movz x3, #2, lsl #0
	movz x4, #7680, lsl #0
	add x4, x26, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #7680, lsl #0
	add x0, x26, x0
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	add x0, x25, #704
	movz x1, #96, lsl #0
	movz x2, #2, lsl #0
	movz x3, #2, lsl #0
	movz x4, #8704, lsl #0
	add x4, x26, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #8704, lsl #0
	add x0, x26, x0
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	add x0, x25, #800
	movz x1, #96, lsl #0
	movz x2, #2, lsl #0
	movz x3, #2, lsl #0
	movz x4, #9728, lsl #0
	add x4, x26, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #9728, lsl #0
	add x0, x26, x0
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	add x0, x25, #896
	movz x1, #416, lsl #0
	movz x2, #4095, lsl #0
	movz x3, #4096, lsl #0
	movz x4, #10752, lsl #0
	add x4, x26, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #10752, lsl #0
	add x0, x26, x0
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	add x0, x25, #1312
	movz x1, #416, lsl #0
	movz x2, #4095, lsl #0
	movz x3, #4096, lsl #0
	movz x4, #11776, lsl #0
	add x4, x26, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #11776, lsl #0
	add x0, x26, x0
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	add x0, x25, #1728
	movz x1, #416, lsl #0
	movz x2, #4095, lsl #0
	movz x3, #4096, lsl #0
	movz x4, #12800, lsl #0
	add x4, x26, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #12800, lsl #0
	add x0, x26, x0
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	add x0, x25, #2144
	movz x1, #416, lsl #0
	movz x2, #4095, lsl #0
	movz x3, #4096, lsl #0
	movz x4, #13824, lsl #0
	add x4, x26, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #13824, lsl #0
	add x0, x26, x0
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	ldr x30, [sp], #16
	ldr x28, [sp], #16
	ldr x26, [sp], #16
	ldr x25, [sp], #16
	ret
	.p2align 6

vg_mldsa44_sign_sha3:
	str x30, [sp, #-16]!
	add x5, x0, #0
	movz x6, #0, lsl #0
	bl {vg_mldsa44_sign_with_cache_sha3}
	ldr x30, [sp], #16
	ret
	.p2align 6

vg_mldsa44_sign:
	str x30, [sp, #-16]!
	add x5, x0, #0
	movz x6, #0, lsl #0
	bl {vg_mldsa44_sign_with_cache}
	ldr x30, [sp], #16
	ret
	.p2align 6

vg_mldsa44_sign_message_sha3:
	lsr x9, x4, #8
	cbnz x9, 20f
	movz x9, #12288, lsl #0
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
	bl {vg_mldsa44_sign_sha3}
	ldr x30, [x28, #912]
	ldr x28, [x28, #904]
	b 21f
20:
	movz x0, #2, lsl #0
21:
	ret
	.p2align 6

vg_mldsa44_sign_message_prepared_sha3:
	lsr x9, x4, #8
	cbnz x9, 20f
	movz x9, #12288, lsl #0
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
	bl {vg_mldsa44_sign_prepared_sha3}
	ldr x30, [x28, #912]
	ldr x28, [x28, #904]
	b 21f
20:
	movz x0, #2, lsl #0
21:
	ret
	.p2align 6

vg_mldsa44_sign_message:
	lsr x9, x4, #8
	cbnz x9, 20f
	movz x9, #12288, lsl #0
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
	bl {vg_mldsa44_sign}
	ldr x30, [x28, #912]
	ldr x28, [x28, #904]
	b 21f
20:
	movz x0, #2, lsl #0
21:
	ret
	.p2align 6

vg_mldsa44_sign_message_prepared:
	lsr x9, x4, #8
	cbnz x9, 20f
	movz x9, #12288, lsl #0
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
	bl {vg_mldsa44_sign_prepared}
	ldr x30, [x28, #912]
	ldr x28, [x28, #904]
	b 21f
20:
	movz x0, #2, lsl #0
21:
	ret
	.p2align 6

vg_mldsa44_verify_sha3:
	str x30, [sp, #-16]!
	add x4, x0, #0
	movz x5, #0, lsl #0
	bl {vg_mldsa44_verify_with_cache_sha3}
	ldr x30, [sp], #16
	ret
	.p2align 6

vg_mldsa44_verify:
	str x30, [sp, #-16]!
	add x4, x0, #0
	movz x5, #0, lsl #0
	bl {vg_mldsa44_verify_with_cache}
	ldr x30, [sp], #16
	ret
	.p2align 6

vg_mldsa44_verify_message_cached_sha3:
	lsr x9, x4, #8
	cbnz x9, 20f
	movz x9, #12288, lsl #0
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
	bl {vg_mldsa44_verify_sha3}
	ldr x30, [x28, #912]
	ldr x28, [x28, #904]
	b 21f
20:
	movz x0, #2, lsl #0
21:
	ret
	.p2align 6

vg_mldsa44_verify_message_prepared_sha3:
	lsr x9, x4, #8
	cbnz x9, 20f
	movz x9, #12288, lsl #0
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
	bl {vg_mldsa44_verify_prepared_sha3}
	ldr x30, [x28, #912]
	ldr x28, [x28, #904]
	b 21f
20:
	movz x0, #2, lsl #0
21:
	ret
	.p2align 6

vg_mldsa44_verify_message_cached:
	lsr x9, x4, #8
	cbnz x9, 20f
	movz x9, #12288, lsl #0
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
	bl {vg_mldsa44_verify}
	ldr x30, [x28, #912]
	ldr x28, [x28, #904]
	b 21f
20:
	movz x0, #2, lsl #0
21:
	ret
	.p2align 6

vg_mldsa44_verify_message_prepared:
	lsr x9, x4, #8
	cbnz x9, 20f
	movz x9, #12288, lsl #0
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
	bl {vg_mldsa44_verify_prepared}
	ldr x30, [x28, #912]
	ldr x28, [x28, #904]
	b 21f
20:
	movz x0, #2, lsl #0
21:
	ret
	.p2align 6
