// The functions of `src/mldsa87.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa87_keygen_sha3:
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
	movz x9, #8, lsl #0
	strb w9, [x28, #896]
	movz x9, #7, lsl #0
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
	movz x2, #14336, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
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
	movz x9, #5, lsl #0
	strb w9, [x28, #1474]
	movz x9, #0, lsl #0
	strb w9, [x28, #1475]
	movz x9, #6, lsl #0
	strb w9, [x28, #1508]
	movz x9, #0, lsl #0
	strb w9, [x28, #1509]
	movz x9, #0, lsl #0
	strb w9, [x28, #1542]
	movz x9, #1, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #8192, lsl #0
	add x1, x28, x1
	movz x2, #14336, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
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
	movz x9, #1, lsl #0
	strb w9, [x28, #1440]
	movz x9, #1, lsl #0
	strb w9, [x28, #1441]
	movz x9, #2, lsl #0
	strb w9, [x28, #1474]
	movz x9, #1, lsl #0
	strb w9, [x28, #1475]
	movz x9, #3, lsl #0
	strb w9, [x28, #1508]
	movz x9, #1, lsl #0
	strb w9, [x28, #1509]
	movz x9, #4, lsl #0
	strb w9, [x28, #1542]
	movz x9, #1, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #12288, lsl #0
	add x1, x28, x1
	movz x2, #14336, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
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
	movz x9, #5, lsl #0
	strb w9, [x28, #1440]
	movz x9, #1, lsl #0
	strb w9, [x28, #1441]
	movz x9, #6, lsl #0
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
	movz x1, #16384, lsl #0
	add x1, x28, x1
	movz x2, #14336, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
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
	movz x9, #5, lsl #0
	strb w9, [x28, #1542]
	movz x9, #2, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #20480, lsl #0
	add x1, x28, x1
	movz x2, #14336, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
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
	movz x9, #6, lsl #0
	strb w9, [x28, #1440]
	movz x9, #2, lsl #0
	strb w9, [x28, #1441]
	movz x9, #0, lsl #0
	strb w9, [x28, #1474]
	movz x9, #3, lsl #0
	strb w9, [x28, #1475]
	movz x9, #1, lsl #0
	strb w9, [x28, #1508]
	movz x9, #3, lsl #0
	strb w9, [x28, #1509]
	movz x9, #2, lsl #0
	strb w9, [x28, #1542]
	movz x9, #3, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #24576, lsl #0
	add x1, x28, x1
	movz x2, #14336, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
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
	movz x9, #3, lsl #0
	strb w9, [x28, #1440]
	movz x9, #3, lsl #0
	strb w9, [x28, #1441]
	movz x9, #4, lsl #0
	strb w9, [x28, #1474]
	movz x9, #3, lsl #0
	strb w9, [x28, #1475]
	movz x9, #5, lsl #0
	strb w9, [x28, #1508]
	movz x9, #3, lsl #0
	strb w9, [x28, #1509]
	movz x9, #6, lsl #0
	strb w9, [x28, #1542]
	movz x9, #3, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #28672, lsl #0
	add x1, x28, x1
	movz x2, #14336, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
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
	movz x1, #32768, lsl #0
	add x1, x28, x1
	movz x2, #14336, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4_sha3}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	dup v0.4s, w8
	movz x1, #32768, lsl #0
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
	movz x9, #4, lsl #0
	strb w9, [x28, #1440]
	movz x9, #4, lsl #0
	strb w9, [x28, #1441]
	movz x9, #5, lsl #0
	strb w9, [x28, #1474]
	movz x9, #4, lsl #0
	strb w9, [x28, #1475]
	movz x9, #6, lsl #0
	strb w9, [x28, #1508]
	movz x9, #4, lsl #0
	strb w9, [x28, #1509]
	movz x9, #0, lsl #0
	strb w9, [x28, #1542]
	movz x9, #5, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #36864, lsl #0
	add x1, x28, x1
	movz x2, #14336, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4_sha3}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	dup v0.4s, w8
	movz x1, #36864, lsl #0
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
	movz x9, #1, lsl #0
	strb w9, [x28, #1440]
	movz x9, #5, lsl #0
	strb w9, [x28, #1441]
	movz x9, #2, lsl #0
	strb w9, [x28, #1474]
	movz x9, #5, lsl #0
	strb w9, [x28, #1475]
	movz x9, #3, lsl #0
	strb w9, [x28, #1508]
	movz x9, #5, lsl #0
	strb w9, [x28, #1509]
	movz x9, #4, lsl #0
	strb w9, [x28, #1542]
	movz x9, #5, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #40960, lsl #0
	add x1, x28, x1
	movz x2, #14336, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4_sha3}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	dup v0.4s, w8
	movz x1, #40960, lsl #0
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
	movz x9, #5, lsl #0
	strb w9, [x28, #1440]
	movz x9, #5, lsl #0
	strb w9, [x28, #1441]
	movz x9, #6, lsl #0
	strb w9, [x28, #1474]
	movz x9, #5, lsl #0
	strb w9, [x28, #1475]
	movz x9, #0, lsl #0
	strb w9, [x28, #1508]
	movz x9, #6, lsl #0
	strb w9, [x28, #1509]
	movz x9, #1, lsl #0
	strb w9, [x28, #1542]
	movz x9, #6, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #45056, lsl #0
	add x1, x28, x1
	movz x2, #14336, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4_sha3}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	dup v0.4s, w8
	movz x1, #45056, lsl #0
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
	movz x9, #2, lsl #0
	strb w9, [x28, #1440]
	movz x9, #6, lsl #0
	strb w9, [x28, #1441]
	movz x9, #3, lsl #0
	strb w9, [x28, #1474]
	movz x9, #6, lsl #0
	strb w9, [x28, #1475]
	movz x9, #4, lsl #0
	strb w9, [x28, #1508]
	movz x9, #6, lsl #0
	strb w9, [x28, #1509]
	movz x9, #5, lsl #0
	strb w9, [x28, #1542]
	movz x9, #6, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #49152, lsl #0
	add x1, x28, x1
	movz x2, #14336, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4_sha3}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	dup v0.4s, w8
	movz x1, #49152, lsl #0
	add x1, x28, x1
	movz x2, #64, lsl #0
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
	movz x9, #6, lsl #0
	strb w9, [x28, #1440]
	movz x9, #6, lsl #0
	strb w9, [x28, #1441]
	movz x9, #0, lsl #0
	strb w9, [x28, #1474]
	movz x9, #7, lsl #0
	strb w9, [x28, #1475]
	movz x9, #1, lsl #0
	strb w9, [x28, #1508]
	movz x9, #7, lsl #0
	strb w9, [x28, #1509]
	movz x9, #2, lsl #0
	strb w9, [x28, #1542]
	movz x9, #7, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #53248, lsl #0
	add x1, x28, x1
	movz x2, #14336, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4_sha3}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	dup v0.4s, w8
	movz x1, #53248, lsl #0
	add x1, x28, x1
	movz x2, #64, lsl #0
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
	movz x9, #3, lsl #0
	strb w9, [x28, #1440]
	movz x9, #7, lsl #0
	strb w9, [x28, #1441]
	movz x9, #4, lsl #0
	strb w9, [x28, #1474]
	movz x9, #7, lsl #0
	strb w9, [x28, #1475]
	movz x9, #5, lsl #0
	strb w9, [x28, #1508]
	movz x9, #7, lsl #0
	strb w9, [x28, #1509]
	movz x9, #6, lsl #0
	strb w9, [x28, #1542]
	movz x9, #7, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #57344, lsl #0
	add x1, x28, x1
	movz x2, #14336, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4_sha3}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	dup v0.4s, w8
	movz x1, #57344, lsl #0
	add x1, x28, x1
	movz x2, #64, lsl #0
213:
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
	cbnz x2, 213b
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
	movz x1, #61440, lsl #0
	add x1, x28, x1
	movz x2, #14336, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
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
	movz x1, #0, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	movz x2, #14336, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
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
	movz x9, #11, lsl #0
	strb w9, [x28, #1670]
	movz x9, #0, lsl #0
	strb w9, [x28, #1671]
	add x0, x28, #1408
	movz x1, #4096, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	movz x2, #14336, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
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
	movz x9, #12, lsl #0
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
	movz x9, #13, lsl #0
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
	movz x9, #14, lsl #0
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
	movz x9, #12, lsl #0
	strb w9, [x28, #1670]
	movz x9, #0, lsl #0
	strb w9, [x28, #1671]
	add x0, x28, #1408
	movz x1, #8192, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	movz x2, #14336, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
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
	movz x0, #61440, lsl #0
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #128
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #62464, lsl #0
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #224
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #63488, lsl #0
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #320
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #64512, lsl #0
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #416
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #0, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #512
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #1024, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #608
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #2048, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #704
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #3072, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #800
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #4096, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #896
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #5120, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #992
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #6144, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #1088
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #7168, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #1184
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #8192, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #1280
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #9216, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #1376
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #10240, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #1472
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #61440, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	movz x0, #62464, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	movz x0, #63488, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	movz x0, #64512, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	movz x0, #0, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	movz x0, #1024, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	movz x0, #2048, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #4096, lsl #0
	add x1, x28, x1
	movz x2, #61440, lsl #0
	add x2, x28, x2
	add x3, x28, #2048
	bl {vg_mldsa_dot_inverse7}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #3072, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	bl {vg_mldsa_add}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #12288, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	movz x2, #13312, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_power2round}
	movz x0, #12288, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #1023, lsl #0
	add x2, x26, #32
	movz x3, #320, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #13312, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #4095, lsl #0
	movz x2, #4096, lsl #0
	add x3, x27, #1568
	movz x4, #416, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #11264, lsl #0
	add x1, x28, x1
	movz x2, #61440, lsl #0
	add x2, x28, x2
	add x3, x28, #2048
	bl {vg_mldsa_dot_inverse7}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #4096, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	bl {vg_mldsa_add}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #12288, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	movz x2, #13312, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_power2round}
	movz x0, #12288, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #1023, lsl #0
	add x2, x26, #352
	movz x3, #320, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #13312, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #4095, lsl #0
	movz x2, #4096, lsl #0
	add x3, x27, #1984
	movz x4, #416, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #18432, lsl #0
	add x1, x28, x1
	movz x2, #61440, lsl #0
	add x2, x28, x2
	add x3, x28, #2048
	bl {vg_mldsa_dot_inverse7}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #5120, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	bl {vg_mldsa_add}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #12288, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	movz x2, #13312, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_power2round}
	movz x0, #12288, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #1023, lsl #0
	add x2, x26, #672
	movz x3, #320, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #13312, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #4095, lsl #0
	movz x2, #4096, lsl #0
	add x3, x27, #2400
	movz x4, #416, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #25600, lsl #0
	add x1, x28, x1
	movz x2, #61440, lsl #0
	add x2, x28, x2
	add x3, x28, #2048
	bl {vg_mldsa_dot_inverse7}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #6144, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	bl {vg_mldsa_add}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #12288, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	movz x2, #13312, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_power2round}
	movz x0, #12288, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #1023, lsl #0
	add x2, x26, #992
	movz x3, #320, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #13312, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #4095, lsl #0
	movz x2, #4096, lsl #0
	add x3, x27, #2816
	movz x4, #416, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #32768, lsl #0
	add x1, x28, x1
	movz x2, #61440, lsl #0
	add x2, x28, x2
	add x3, x28, #2048
	bl {vg_mldsa_dot_inverse7}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #7168, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	bl {vg_mldsa_add}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #12288, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	movz x2, #13312, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_power2round}
	movz x0, #12288, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #1023, lsl #0
	add x2, x26, #1312
	movz x3, #320, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #13312, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #4095, lsl #0
	movz x2, #4096, lsl #0
	add x3, x27, #3232
	movz x4, #416, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #39936, lsl #0
	add x1, x28, x1
	movz x2, #61440, lsl #0
	add x2, x28, x2
	add x3, x28, #2048
	bl {vg_mldsa_dot_inverse7}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #8192, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	bl {vg_mldsa_add}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #12288, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	movz x2, #13312, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_power2round}
	movz x0, #12288, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #1023, lsl #0
	add x2, x26, #1632
	movz x3, #320, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #13312, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #4095, lsl #0
	movz x2, #4096, lsl #0
	add x3, x27, #3648
	movz x4, #416, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #47104, lsl #0
	add x1, x28, x1
	movz x2, #61440, lsl #0
	add x2, x28, x2
	add x3, x28, #2048
	bl {vg_mldsa_dot_inverse7}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #9216, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	bl {vg_mldsa_add}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #12288, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	movz x2, #13312, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_power2round}
	movz x0, #12288, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #1023, lsl #0
	add x2, x26, #1952
	movz x3, #320, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #13312, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #4095, lsl #0
	movz x2, #4096, lsl #0
	add x3, x27, #4064
	movz x4, #416, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #54272, lsl #0
	add x1, x28, x1
	movz x2, #61440, lsl #0
	add x2, x28, x2
	add x3, x28, #2048
	bl {vg_mldsa_dot_inverse7}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #10240, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	bl {vg_mldsa_add}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #12288, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	movz x2, #13312, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_power2round}
	movz x0, #12288, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #1023, lsl #0
	add x2, x26, #2272
	movz x3, #320, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #13312, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #4095, lsl #0
	movz x2, #4096, lsl #0
	movz x3, #4480, lsl #0
	add x3, x27, x3
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
	movz x4, #2592, lsl #0
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

vg_mldsa87_keygen:
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
	movz x9, #8, lsl #0
	strb w9, [x28, #896]
	movz x9, #7, lsl #0
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
	movz x2, #14336, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
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
	movz x9, #5, lsl #0
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
	movz x9, #6, lsl #0
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
	movz x9, #0, lsl #0
	strb w9, [x28, #1542]
	movz x9, #1, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #8192, lsl #0
	add x1, x28, x1
	movz x2, #14336, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
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
	movz x9, #1, lsl #0
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
	movz x9, #2, lsl #0
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
	movz x9, #3, lsl #0
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
	movz x9, #4, lsl #0
	strb w9, [x28, #1542]
	movz x9, #1, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #12288, lsl #0
	add x1, x28, x1
	movz x2, #14336, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
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
	movz x9, #5, lsl #0
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
	movz x9, #6, lsl #0
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
	movz x1, #16384, lsl #0
	add x1, x28, x1
	movz x2, #14336, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
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
	movz x9, #5, lsl #0
	strb w9, [x28, #1542]
	movz x9, #2, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #20480, lsl #0
	add x1, x28, x1
	movz x2, #14336, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
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
	movz x9, #6, lsl #0
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
	movz x9, #0, lsl #0
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
	movz x9, #1, lsl #0
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
	movz x9, #2, lsl #0
	strb w9, [x28, #1542]
	movz x9, #3, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #24576, lsl #0
	add x1, x28, x1
	movz x2, #14336, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
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
	movz x9, #3, lsl #0
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
	movz x9, #4, lsl #0
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
	movz x9, #5, lsl #0
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
	movz x9, #6, lsl #0
	strb w9, [x28, #1542]
	movz x9, #3, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #28672, lsl #0
	add x1, x28, x1
	movz x2, #14336, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
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
	movz x1, #32768, lsl #0
	add x1, x28, x1
	movz x2, #14336, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	movz x1, #32768, lsl #0
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
	movz x9, #5, lsl #0
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
	movz x9, #6, lsl #0
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
	movz x9, #0, lsl #0
	strb w9, [x28, #1542]
	movz x9, #5, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #36864, lsl #0
	add x1, x28, x1
	movz x2, #14336, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	movz x1, #36864, lsl #0
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
	movz x9, #1, lsl #0
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
	movz x9, #2, lsl #0
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
	movz x9, #3, lsl #0
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
	movz x9, #4, lsl #0
	strb w9, [x28, #1542]
	movz x9, #5, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #40960, lsl #0
	add x1, x28, x1
	movz x2, #14336, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	movz x1, #40960, lsl #0
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
	movz x9, #5, lsl #0
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
	movz x9, #6, lsl #0
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
	movz x9, #0, lsl #0
	strb w9, [x28, #1508]
	movz x9, #6, lsl #0
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
	movz x9, #6, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #45056, lsl #0
	add x1, x28, x1
	movz x2, #14336, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	movz x1, #45056, lsl #0
	add x1, x28, x1
	movz x2, #1024, lsl #0
210:
	ldr w9, [x1, #0]
	and w9, w9, w8
	str w9, [x1, #0]
	add x1, x1, #4
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
	movz x9, #2, lsl #0
	strb w9, [x28, #1440]
	movz x9, #6, lsl #0
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
	movz x9, #6, lsl #0
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
	movz x9, #6, lsl #0
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
	movz x9, #5, lsl #0
	strb w9, [x28, #1542]
	movz x9, #6, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #49152, lsl #0
	add x1, x28, x1
	movz x2, #14336, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	movz x1, #49152, lsl #0
	add x1, x28, x1
	movz x2, #1024, lsl #0
211:
	ldr w9, [x1, #0]
	and w9, w9, w8
	str w9, [x1, #0]
	add x1, x1, #4
	sub x2, x2, #1
	cbnz x2, 211b
	add x10, x28, #1408
	ldr x9, [x28, #1152]
	str x9, [x10, #0]
	ldr x9, [x28, #1160]
	str x9, [x10, #8]
	ldr x9, [x28, #1168]
	str x9, [x10, #16]
	ldr x9, [x28, #1176]
	str x9, [x10, #24]
	movz x9, #6, lsl #0
	strb w9, [x28, #1440]
	movz x9, #6, lsl #0
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
	movz x9, #7, lsl #0
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
	movz x9, #7, lsl #0
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
	movz x9, #7, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #53248, lsl #0
	add x1, x28, x1
	movz x2, #14336, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	movz x1, #53248, lsl #0
	add x1, x28, x1
	movz x2, #1024, lsl #0
212:
	ldr w9, [x1, #0]
	and w9, w9, w8
	str w9, [x1, #0]
	add x1, x1, #4
	sub x2, x2, #1
	cbnz x2, 212b
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
	movz x9, #7, lsl #0
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
	movz x9, #7, lsl #0
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
	movz x9, #5, lsl #0
	strb w9, [x28, #1508]
	movz x9, #7, lsl #0
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
	movz x9, #6, lsl #0
	strb w9, [x28, #1542]
	movz x9, #7, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #57344, lsl #0
	add x1, x28, x1
	movz x2, #14336, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	movz x1, #57344, lsl #0
	add x1, x28, x1
	movz x2, #1024, lsl #0
213:
	ldr w9, [x1, #0]
	and w9, w9, w8
	str w9, [x1, #0]
	add x1, x1, #4
	sub x2, x2, #1
	cbnz x2, 213b
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
	movz x1, #61440, lsl #0
	add x1, x28, x1
	movz x2, #14336, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
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
	movz x1, #0, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	movz x2, #14336, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
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
	movz x9, #11, lsl #0
	strb w9, [x28, #1670]
	movz x9, #0, lsl #0
	strb w9, [x28, #1671]
	add x0, x28, #1408
	movz x1, #4096, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	movz x2, #14336, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
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
	movz x9, #12, lsl #0
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
	movz x9, #13, lsl #0
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
	movz x9, #14, lsl #0
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
	movz x9, #12, lsl #0
	strb w9, [x28, #1670]
	movz x9, #0, lsl #0
	strb w9, [x28, #1671]
	add x0, x28, #1408
	movz x1, #8192, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	movz x2, #14336, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
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
	movz x0, #61440, lsl #0
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #128
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #62464, lsl #0
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #224
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #63488, lsl #0
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #320
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #64512, lsl #0
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #416
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #0, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #512
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #1024, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #608
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #2048, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #704
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #3072, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #800
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #4096, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #896
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #5120, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #992
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #6144, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #1088
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #7168, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #1184
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #8192, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #1280
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #9216, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #1376
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #10240, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #2, lsl #0
	movz x2, #2, lsl #0
	add x3, x27, #1472
	movz x4, #96, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #61440, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_ntt}
	movz x0, #62464, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_ntt}
	movz x0, #63488, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_ntt}
	movz x0, #64512, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_ntt}
	movz x0, #0, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_ntt}
	movz x0, #1024, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_ntt}
	movz x0, #2048, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #4096, lsl #0
	add x1, x28, x1
	movz x2, #61440, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #5120, lsl #0
	add x1, x28, x1
	movz x2, #62464, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #6144, lsl #0
	add x1, x28, x1
	movz x2, #63488, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #7168, lsl #0
	add x1, x28, x1
	movz x2, #64512, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #8192, lsl #0
	add x1, x28, x1
	movz x2, #0, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #9216, lsl #0
	add x1, x28, x1
	movz x2, #1024, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #10240, lsl #0
	add x1, x28, x1
	movz x2, #2048, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_inv_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #3072, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	bl {vg_mldsa_add}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #12288, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	movz x2, #13312, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_power2round}
	movz x0, #12288, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #1023, lsl #0
	add x2, x26, #32
	movz x3, #320, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #13312, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #4095, lsl #0
	movz x2, #4096, lsl #0
	add x3, x27, #1568
	movz x4, #416, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #11264, lsl #0
	add x1, x28, x1
	movz x2, #61440, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #12288, lsl #0
	add x1, x28, x1
	movz x2, #62464, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #13312, lsl #0
	add x1, x28, x1
	movz x2, #63488, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #14336, lsl #0
	add x1, x28, x1
	movz x2, #64512, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #15360, lsl #0
	add x1, x28, x1
	movz x2, #0, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #16384, lsl #0
	add x1, x28, x1
	movz x2, #1024, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #17408, lsl #0
	add x1, x28, x1
	movz x2, #2048, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_inv_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #4096, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	bl {vg_mldsa_add}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #12288, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	movz x2, #13312, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_power2round}
	movz x0, #12288, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #1023, lsl #0
	add x2, x26, #352
	movz x3, #320, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #13312, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #4095, lsl #0
	movz x2, #4096, lsl #0
	add x3, x27, #1984
	movz x4, #416, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #18432, lsl #0
	add x1, x28, x1
	movz x2, #61440, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #19456, lsl #0
	add x1, x28, x1
	movz x2, #62464, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #20480, lsl #0
	add x1, x28, x1
	movz x2, #63488, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #21504, lsl #0
	add x1, x28, x1
	movz x2, #64512, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #22528, lsl #0
	add x1, x28, x1
	movz x2, #0, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #23552, lsl #0
	add x1, x28, x1
	movz x2, #1024, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #24576, lsl #0
	add x1, x28, x1
	movz x2, #2048, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_inv_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #5120, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	bl {vg_mldsa_add}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #12288, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	movz x2, #13312, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_power2round}
	movz x0, #12288, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #1023, lsl #0
	add x2, x26, #672
	movz x3, #320, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #13312, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #4095, lsl #0
	movz x2, #4096, lsl #0
	add x3, x27, #2400
	movz x4, #416, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #25600, lsl #0
	add x1, x28, x1
	movz x2, #61440, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #26624, lsl #0
	add x1, x28, x1
	movz x2, #62464, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #27648, lsl #0
	add x1, x28, x1
	movz x2, #63488, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #28672, lsl #0
	add x1, x28, x1
	movz x2, #64512, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #29696, lsl #0
	add x1, x28, x1
	movz x2, #0, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #30720, lsl #0
	add x1, x28, x1
	movz x2, #1024, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #31744, lsl #0
	add x1, x28, x1
	movz x2, #2048, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_inv_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #6144, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	bl {vg_mldsa_add}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #12288, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	movz x2, #13312, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_power2round}
	movz x0, #12288, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #1023, lsl #0
	add x2, x26, #992
	movz x3, #320, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #13312, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #4095, lsl #0
	movz x2, #4096, lsl #0
	add x3, x27, #2816
	movz x4, #416, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #32768, lsl #0
	add x1, x28, x1
	movz x2, #61440, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #33792, lsl #0
	add x1, x28, x1
	movz x2, #62464, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #34816, lsl #0
	add x1, x28, x1
	movz x2, #63488, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #35840, lsl #0
	add x1, x28, x1
	movz x2, #64512, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #36864, lsl #0
	add x1, x28, x1
	movz x2, #0, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #37888, lsl #0
	add x1, x28, x1
	movz x2, #1024, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #38912, lsl #0
	add x1, x28, x1
	movz x2, #2048, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_inv_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #7168, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	bl {vg_mldsa_add}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #12288, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	movz x2, #13312, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_power2round}
	movz x0, #12288, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #1023, lsl #0
	add x2, x26, #1312
	movz x3, #320, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #13312, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #4095, lsl #0
	movz x2, #4096, lsl #0
	add x3, x27, #3232
	movz x4, #416, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #39936, lsl #0
	add x1, x28, x1
	movz x2, #61440, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #40960, lsl #0
	add x1, x28, x1
	movz x2, #62464, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #41984, lsl #0
	add x1, x28, x1
	movz x2, #63488, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #43008, lsl #0
	add x1, x28, x1
	movz x2, #64512, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #44032, lsl #0
	add x1, x28, x1
	movz x2, #0, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #45056, lsl #0
	add x1, x28, x1
	movz x2, #1024, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #46080, lsl #0
	add x1, x28, x1
	movz x2, #2048, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_inv_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #8192, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	bl {vg_mldsa_add}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #12288, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	movz x2, #13312, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_power2round}
	movz x0, #12288, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #1023, lsl #0
	add x2, x26, #1632
	movz x3, #320, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #13312, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #4095, lsl #0
	movz x2, #4096, lsl #0
	add x3, x27, #3648
	movz x4, #416, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #47104, lsl #0
	add x1, x28, x1
	movz x2, #61440, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #48128, lsl #0
	add x1, x28, x1
	movz x2, #62464, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #49152, lsl #0
	add x1, x28, x1
	movz x2, #63488, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #50176, lsl #0
	add x1, x28, x1
	movz x2, #64512, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #51200, lsl #0
	add x1, x28, x1
	movz x2, #0, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #52224, lsl #0
	add x1, x28, x1
	movz x2, #1024, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #53248, lsl #0
	add x1, x28, x1
	movz x2, #2048, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_inv_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #9216, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	bl {vg_mldsa_add}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #12288, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	movz x2, #13312, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_power2round}
	movz x0, #12288, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #1023, lsl #0
	add x2, x26, #1952
	movz x3, #320, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #13312, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #4095, lsl #0
	movz x2, #4096, lsl #0
	add x3, x27, #4064
	movz x4, #416, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #54272, lsl #0
	add x1, x28, x1
	movz x2, #61440, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #55296, lsl #0
	add x1, x28, x1
	movz x2, #62464, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #56320, lsl #0
	add x1, x28, x1
	movz x2, #63488, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #57344, lsl #0
	add x1, x28, x1
	movz x2, #64512, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #58368, lsl #0
	add x1, x28, x1
	movz x2, #0, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #59392, lsl #0
	add x1, x28, x1
	movz x2, #1024, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #60416, lsl #0
	add x1, x28, x1
	movz x2, #2048, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_inv_ntt}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #10240, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	bl {vg_mldsa_add}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #12288, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	movz x2, #13312, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_power2round}
	movz x0, #12288, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #1023, lsl #0
	add x2, x26, #2272
	movz x3, #320, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #13312, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #4095, lsl #0
	movz x2, #4096, lsl #0
	movz x3, #4480, lsl #0
	add x3, x27, x3
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
	movz x4, #2592, lsl #0
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

vg_mldsa87_pk_tr_sha3:
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
	movz x4, #2592, lsl #0
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

vg_mldsa87_pk_tr:
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
	movz x4, #2592, lsl #0
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

vg_mldsa87_prepare_verifying_key:
	str x25, [sp, #-16]!
	str x26, [sp, #-16]!
	str x28, [sp, #-16]!
	str x30, [sp, #-16]!
	add x25, x0, #0
	add x26, x1, #0
	add x28, x2, #0
	add x0, x26, #0
	add x1, x25, #0
	movz x2, #162, lsl #0
20:
	ldr q0, [x1, #0]
	str q0, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x2, x2, #1
	cbnz x2, 20b
	add x0, x25, #32
	add x1, x26, #2592
	bl {vg_mldsa_unpack_t1}
	add x0, x26, #2592
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	add x0, x25, #352
	add x1, x26, #3616
	bl {vg_mldsa_unpack_t1}
	add x0, x26, #3616
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	add x0, x25, #672
	movz x1, #4640, lsl #0
	add x1, x26, x1
	bl {vg_mldsa_unpack_t1}
	movz x0, #4640, lsl #0
	add x0, x26, x0
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	add x0, x25, #992
	movz x1, #5664, lsl #0
	add x1, x26, x1
	bl {vg_mldsa_unpack_t1}
	movz x0, #5664, lsl #0
	add x0, x26, x0
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	add x0, x25, #1312
	movz x1, #6688, lsl #0
	add x1, x26, x1
	bl {vg_mldsa_unpack_t1}
	movz x0, #6688, lsl #0
	add x0, x26, x0
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	add x0, x25, #1632
	movz x1, #7712, lsl #0
	add x1, x26, x1
	bl {vg_mldsa_unpack_t1}
	movz x0, #7712, lsl #0
	add x0, x26, x0
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	add x0, x25, #1952
	movz x1, #8736, lsl #0
	add x1, x26, x1
	bl {vg_mldsa_unpack_t1}
	movz x0, #8736, lsl #0
	add x0, x26, x0
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	add x0, x25, #2272
	movz x1, #9760, lsl #0
	add x1, x26, x1
	bl {vg_mldsa_unpack_t1}
	movz x0, #9760, lsl #0
	add x0, x26, x0
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	ldr x30, [sp], #16
	ldr x28, [sp], #16
	ldr x26, [sp], #16
	ldr x25, [sp], #16
	ret
	.p2align 6

vg_mldsa87_prepare_signing_key:
	str x25, [sp, #-16]!
	str x26, [sp, #-16]!
	str x28, [sp, #-16]!
	str x30, [sp, #-16]!
	add x25, x0, #0
	add x26, x1, #0
	add x28, x2, #0
	add x0, x26, #0
	add x1, x25, #0
	movz x2, #306, lsl #0
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
	movz x4, #4896, lsl #0
	add x4, x26, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #4896, lsl #0
	add x0, x26, x0
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	add x0, x25, #224
	movz x1, #96, lsl #0
	movz x2, #2, lsl #0
	movz x3, #2, lsl #0
	movz x4, #5920, lsl #0
	add x4, x26, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #5920, lsl #0
	add x0, x26, x0
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	add x0, x25, #320
	movz x1, #96, lsl #0
	movz x2, #2, lsl #0
	movz x3, #2, lsl #0
	movz x4, #6944, lsl #0
	add x4, x26, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #6944, lsl #0
	add x0, x26, x0
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	add x0, x25, #416
	movz x1, #96, lsl #0
	movz x2, #2, lsl #0
	movz x3, #2, lsl #0
	movz x4, #7968, lsl #0
	add x4, x26, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #7968, lsl #0
	add x0, x26, x0
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	add x0, x25, #512
	movz x1, #96, lsl #0
	movz x2, #2, lsl #0
	movz x3, #2, lsl #0
	movz x4, #8992, lsl #0
	add x4, x26, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #8992, lsl #0
	add x0, x26, x0
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	add x0, x25, #608
	movz x1, #96, lsl #0
	movz x2, #2, lsl #0
	movz x3, #2, lsl #0
	movz x4, #10016, lsl #0
	add x4, x26, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #10016, lsl #0
	add x0, x26, x0
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	add x0, x25, #704
	movz x1, #96, lsl #0
	movz x2, #2, lsl #0
	movz x3, #2, lsl #0
	movz x4, #11040, lsl #0
	add x4, x26, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #11040, lsl #0
	add x0, x26, x0
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	add x0, x25, #800
	movz x1, #96, lsl #0
	movz x2, #2, lsl #0
	movz x3, #2, lsl #0
	movz x4, #12064, lsl #0
	add x4, x26, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #12064, lsl #0
	add x0, x26, x0
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	add x0, x25, #896
	movz x1, #96, lsl #0
	movz x2, #2, lsl #0
	movz x3, #2, lsl #0
	movz x4, #13088, lsl #0
	add x4, x26, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #13088, lsl #0
	add x0, x26, x0
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	add x0, x25, #992
	movz x1, #96, lsl #0
	movz x2, #2, lsl #0
	movz x3, #2, lsl #0
	movz x4, #14112, lsl #0
	add x4, x26, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #14112, lsl #0
	add x0, x26, x0
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	add x0, x25, #1088
	movz x1, #96, lsl #0
	movz x2, #2, lsl #0
	movz x3, #2, lsl #0
	movz x4, #15136, lsl #0
	add x4, x26, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #15136, lsl #0
	add x0, x26, x0
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	add x0, x25, #1184
	movz x1, #96, lsl #0
	movz x2, #2, lsl #0
	movz x3, #2, lsl #0
	movz x4, #16160, lsl #0
	add x4, x26, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #16160, lsl #0
	add x0, x26, x0
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	add x0, x25, #1280
	movz x1, #96, lsl #0
	movz x2, #2, lsl #0
	movz x3, #2, lsl #0
	movz x4, #17184, lsl #0
	add x4, x26, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #17184, lsl #0
	add x0, x26, x0
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	add x0, x25, #1376
	movz x1, #96, lsl #0
	movz x2, #2, lsl #0
	movz x3, #2, lsl #0
	movz x4, #18208, lsl #0
	add x4, x26, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #18208, lsl #0
	add x0, x26, x0
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	add x0, x25, #1472
	movz x1, #96, lsl #0
	movz x2, #2, lsl #0
	movz x3, #2, lsl #0
	movz x4, #19232, lsl #0
	add x4, x26, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #19232, lsl #0
	add x0, x26, x0
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	add x0, x25, #1568
	movz x1, #416, lsl #0
	movz x2, #4095, lsl #0
	movz x3, #4096, lsl #0
	movz x4, #20256, lsl #0
	add x4, x26, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #20256, lsl #0
	add x0, x26, x0
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	add x0, x25, #1984
	movz x1, #416, lsl #0
	movz x2, #4095, lsl #0
	movz x3, #4096, lsl #0
	movz x4, #21280, lsl #0
	add x4, x26, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #21280, lsl #0
	add x0, x26, x0
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	add x0, x25, #2400
	movz x1, #416, lsl #0
	movz x2, #4095, lsl #0
	movz x3, #4096, lsl #0
	movz x4, #22304, lsl #0
	add x4, x26, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #22304, lsl #0
	add x0, x26, x0
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	add x0, x25, #2816
	movz x1, #416, lsl #0
	movz x2, #4095, lsl #0
	movz x3, #4096, lsl #0
	movz x4, #23328, lsl #0
	add x4, x26, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #23328, lsl #0
	add x0, x26, x0
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	add x0, x25, #3232
	movz x1, #416, lsl #0
	movz x2, #4095, lsl #0
	movz x3, #4096, lsl #0
	movz x4, #24352, lsl #0
	add x4, x26, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #24352, lsl #0
	add x0, x26, x0
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	add x0, x25, #3648
	movz x1, #416, lsl #0
	movz x2, #4095, lsl #0
	movz x3, #4096, lsl #0
	movz x4, #25376, lsl #0
	add x4, x26, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #25376, lsl #0
	add x0, x26, x0
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	add x0, x25, #4064
	movz x1, #416, lsl #0
	movz x2, #4095, lsl #0
	movz x3, #4096, lsl #0
	movz x4, #26400, lsl #0
	add x4, x26, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #26400, lsl #0
	add x0, x26, x0
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	movz x0, #4480, lsl #0
	add x0, x25, x0
	movz x1, #416, lsl #0
	movz x2, #4095, lsl #0
	movz x3, #4096, lsl #0
	movz x4, #27424, lsl #0
	add x4, x26, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #27424, lsl #0
	add x0, x26, x0
	add x1, x28, #0
	bl {vg_mldsa_ntt}
	ldr x30, [sp], #16
	ldr x28, [sp], #16
	ldr x26, [sp], #16
	ldr x25, [sp], #16
	ret
	.p2align 6

vg_mldsa87_sign_sha3:
	str x30, [sp, #-16]!
	add x5, x0, #0
	movz x6, #0, lsl #0
	bl {vg_mldsa87_sign_with_cache_sha3}
	ldr x30, [sp], #16
	ret
	.p2align 6

vg_mldsa87_sign:
	str x30, [sp, #-16]!
	add x5, x0, #0
	movz x6, #0, lsl #0
	bl {vg_mldsa87_sign_with_cache}
	ldr x30, [sp], #16
	ret
	.p2align 6

vg_mldsa87_sign_message_sha3:
	lsr x9, x4, #8
	cbnz x9, 20f
	movz x9, #13312, lsl #0
	movk x9, #2, lsl #16
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
	bl {vg_mldsa87_sign_sha3}
	ldr x30, [x28, #912]
	ldr x28, [x28, #904]
	b 21f
20:
	movz x0, #2, lsl #0
21:
	ret
	.p2align 6

vg_mldsa87_sign_message_prepared_sha3:
	lsr x9, x4, #8
	cbnz x9, 20f
	movz x9, #13312, lsl #0
	movk x9, #2, lsl #16
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
	bl {vg_mldsa87_sign_prepared_sha3}
	ldr x30, [x28, #912]
	ldr x28, [x28, #904]
	b 21f
20:
	movz x0, #2, lsl #0
21:
	ret
	.p2align 6

vg_mldsa87_sign_message:
	lsr x9, x4, #8
	cbnz x9, 20f
	movz x9, #13312, lsl #0
	movk x9, #2, lsl #16
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
	bl {vg_mldsa87_sign}
	ldr x30, [x28, #912]
	ldr x28, [x28, #904]
	b 21f
20:
	movz x0, #2, lsl #0
21:
	ret
	.p2align 6

vg_mldsa87_sign_message_prepared:
	lsr x9, x4, #8
	cbnz x9, 20f
	movz x9, #13312, lsl #0
	movk x9, #2, lsl #16
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
	bl {vg_mldsa87_sign_prepared}
	ldr x30, [x28, #912]
	ldr x28, [x28, #904]
	b 21f
20:
	movz x0, #2, lsl #0
21:
	ret
	.p2align 6

vg_mldsa87_verify_sha3:
	str x30, [sp, #-16]!
	add x4, x0, #0
	movz x5, #0, lsl #0
	bl {vg_mldsa87_verify_with_cache_sha3}
	ldr x30, [sp], #16
	ret
	.p2align 6

vg_mldsa87_verify:
	str x30, [sp, #-16]!
	add x4, x0, #0
	movz x5, #0, lsl #0
	bl {vg_mldsa87_verify_with_cache}
	ldr x30, [sp], #16
	ret
	.p2align 6

vg_mldsa87_verify_message_cached_sha3:
	lsr x9, x4, #8
	cbnz x9, 20f
	movz x9, #13312, lsl #0
	movk x9, #2, lsl #16
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
	bl {vg_mldsa87_verify_sha3}
	ldr x30, [x28, #912]
	ldr x28, [x28, #904]
	b 21f
20:
	movz x0, #2, lsl #0
21:
	ret
	.p2align 6

vg_mldsa87_verify_message_prepared_sha3:
	lsr x9, x4, #8
	cbnz x9, 20f
	movz x9, #13312, lsl #0
	movk x9, #2, lsl #16
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
	bl {vg_mldsa87_verify_prepared_sha3}
	ldr x30, [x28, #912]
	ldr x28, [x28, #904]
	b 21f
20:
	movz x0, #2, lsl #0
21:
	ret
	.p2align 6

vg_mldsa87_verify_message_cached:
	lsr x9, x4, #8
	cbnz x9, 20f
	movz x9, #13312, lsl #0
	movk x9, #2, lsl #16
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
	bl {vg_mldsa87_verify}
	ldr x30, [x28, #912]
	ldr x28, [x28, #904]
	b 21f
20:
	movz x0, #2, lsl #0
21:
	ret
	.p2align 6

vg_mldsa87_verify_message_prepared:
	lsr x9, x4, #8
	cbnz x9, 20f
	movz x9, #13312, lsl #0
	movk x9, #2, lsl #16
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
	bl {vg_mldsa87_verify_prepared}
	ldr x30, [x28, #912]
	ldr x28, [x28, #904]
	b 21f
20:
	movz x0, #2, lsl #0
21:
	ret
	.p2align 6
