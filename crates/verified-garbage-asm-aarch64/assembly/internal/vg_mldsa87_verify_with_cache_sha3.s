// The functions of `src/internal/vg_mldsa87_verify_with_cache_sha3.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa87_verify_with_cache_sha3:
	str x21, [sp, #-16]!
	str x22, [sp, #-16]!
	add x21, x4, #0
	add x22, x5, #0
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
	movz x0, #4544, lsl #0
	add x0, x27, x0
	movz x1, #83, lsl #0
	movz x2, #75, lsl #0
	movz x3, #62464, lsl #0
	add x3, x28, x3
	movz x4, #2048, lsl #0
	bl {vg_mldsa_hint_bit_unpack}
	and w24, w24, w0
	cbnz x24, 20f
	b 21f
20:
	add x0, x27, #64
	movz x1, #640, lsl #0
	movz x2, #65535, lsl #0
	movk x2, #7, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	movz x3, #0, lsl #0
	movk x3, #8, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	movz x4, #5120, lsl #0
	movk x4, #1, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #5120, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #65416, lsl #0
	movk x1, #7, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	bl {vg_mldsa_norm_lt}
	and w24, w24, w0
	add x0, x27, #704
	movz x1, #640, lsl #0
	movz x2, #65535, lsl #0
	movk x2, #7, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	movz x3, #0, lsl #0
	movk x3, #8, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	movz x4, #6144, lsl #0
	movk x4, #1, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #6144, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #65416, lsl #0
	movk x1, #7, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	bl {vg_mldsa_norm_lt}
	and w24, w24, w0
	add x0, x27, #1344
	movz x1, #640, lsl #0
	movz x2, #65535, lsl #0
	movk x2, #7, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	movz x3, #0, lsl #0
	movk x3, #8, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	movz x4, #7168, lsl #0
	movk x4, #1, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #7168, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #65416, lsl #0
	movk x1, #7, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	bl {vg_mldsa_norm_lt}
	and w24, w24, w0
	add x0, x27, #1984
	movz x1, #640, lsl #0
	movz x2, #65535, lsl #0
	movk x2, #7, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	movz x3, #0, lsl #0
	movk x3, #8, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	movz x4, #8192, lsl #0
	movk x4, #1, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #8192, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #65416, lsl #0
	movk x1, #7, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	bl {vg_mldsa_norm_lt}
	and w24, w24, w0
	add x0, x27, #2624
	movz x1, #640, lsl #0
	movz x2, #65535, lsl #0
	movk x2, #7, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	movz x3, #0, lsl #0
	movk x3, #8, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	movz x4, #9216, lsl #0
	movk x4, #1, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #9216, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #65416, lsl #0
	movk x1, #7, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	bl {vg_mldsa_norm_lt}
	and w24, w24, w0
	add x0, x27, #3264
	movz x1, #640, lsl #0
	movz x2, #65535, lsl #0
	movk x2, #7, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	movz x3, #0, lsl #0
	movk x3, #8, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	movz x4, #10240, lsl #0
	movk x4, #1, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #10240, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #65416, lsl #0
	movk x1, #7, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	bl {vg_mldsa_norm_lt}
	and w24, w24, w0
	add x0, x27, #3904
	movz x1, #640, lsl #0
	movz x2, #65535, lsl #0
	movk x2, #7, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	movz x3, #0, lsl #0
	movk x3, #8, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	movz x4, #11264, lsl #0
	movk x4, #1, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #11264, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #65416, lsl #0
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
	bl {vg_mldsa_rej_ntt_poly4_sha3}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	dup v0.4s, w8
	movz x1, #32768, lsl #0
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
	bl {vg_mldsa_rej_ntt_poly4_sha3}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	dup v0.4s, w8
	movz x1, #36864, lsl #0
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
	bl {vg_mldsa_rej_ntt_poly4_sha3}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	dup v0.4s, w8
	movz x1, #40960, lsl #0
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
	bl {vg_mldsa_rej_ntt_poly4_sha3}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	dup v0.4s, w8
	movz x1, #45056, lsl #0
	add x1, x28, x1
	movz x2, #64, lsl #0
214:
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
	cbnz x2, 214b
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
	bl {vg_mldsa_rej_ntt_poly4_sha3}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	dup v0.4s, w8
	movz x1, #49152, lsl #0
	add x1, x28, x1
	movz x2, #64, lsl #0
215:
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
	cbnz x2, 215b
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
	bl {vg_mldsa_rej_ntt_poly4_sha3}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	dup v0.4s, w8
	movz x1, #53248, lsl #0
	add x1, x28, x1
	movz x2, #64, lsl #0
216:
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
	cbnz x2, 216b
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
	bl {vg_mldsa_rej_ntt_poly4_sha3}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	dup v0.4s, w8
	movz x1, #57344, lsl #0
	add x1, x28, x1
	movz x2, #64, lsl #0
217:
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
	cbnz x2, 217b
	add x0, x27, #0
	movz x1, #64, lsl #0
	movz x2, #60, lsl #0
	movz x3, #12288, lsl #0
	movk x3, #1, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	add x3, x28, x3
	add x4, x28, #2048
	bl {vg_mldsa_sample_in_ball_sha3}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	dup v0.4s, w8
	movz x1, #12288, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	movz x2, #16, lsl #0
218:
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
	cbnz x2, 218b
	movz x0, #5120, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	movz x0, #6144, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	movz x0, #7168, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	movz x0, #8192, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	movz x0, #9216, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	movz x0, #10240, lsl #0
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
	bl {vg_mldsa_ntt_positive}
	movz x0, #12288, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	movz x0, #15360, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #4096, lsl #0
	add x1, x28, x1
	movz x2, #5120, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_montgomery_dot7}
	cbnz x22, 219f
	add x0, x25, #32
	movz x1, #13312, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	bl {vg_mldsa_unpack_t1}
	movz x0, #13312, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	b 220f
219:
	movz x0, #13312, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	add x1, x21, #0
	movz x2, #64, lsl #0
221:
	ldr q0, [x1, #0]
	str q0, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x2, x2, #1
	cbnz x2, 221b
220:
	movz x0, #14336, lsl #0
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
	bl {vg_mldsa_montgomery_product}
	movz x0, #15360, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #14336, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	bl {vg_mldsa_sub}
	movz x0, #15360, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	bl {vg_mldsa_montgomery_inv_ntt}
	movz x0, #61440, lsl #0
	add x0, x28, x0
	movz x1, #62464, lsl #0
	add x1, x28, x1
	movz x2, #15360, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	movz x3, #65280, lsl #0
	movk x3, #3, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	bl {vg_mldsa_usehint_pack4}
	movz x0, #15360, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #11264, lsl #0
	add x1, x28, x1
	movz x2, #5120, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_montgomery_dot7}
	cbnz x22, 222f
	add x0, x25, #352
	movz x1, #13312, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	bl {vg_mldsa_unpack_t1}
	movz x0, #13312, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	b 223f
222:
	movz x0, #13312, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	add x1, x21, #1024
	movz x2, #64, lsl #0
224:
	ldr q0, [x1, #0]
	str q0, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x2, x2, #1
	cbnz x2, 224b
223:
	movz x0, #14336, lsl #0
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
	bl {vg_mldsa_montgomery_product}
	movz x0, #15360, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #14336, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	bl {vg_mldsa_sub}
	movz x0, #15360, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	bl {vg_mldsa_montgomery_inv_ntt}
	movz x0, #61568, lsl #0
	add x0, x28, x0
	movz x1, #63488, lsl #0
	add x1, x28, x1
	movz x2, #15360, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	movz x3, #65280, lsl #0
	movk x3, #3, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	bl {vg_mldsa_usehint_pack4}
	movz x0, #15360, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #18432, lsl #0
	add x1, x28, x1
	movz x2, #5120, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_montgomery_dot7}
	cbnz x22, 225f
	add x0, x25, #672
	movz x1, #13312, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	bl {vg_mldsa_unpack_t1}
	movz x0, #13312, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	b 226f
225:
	movz x0, #13312, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	add x1, x21, #2048
	movz x2, #64, lsl #0
227:
	ldr q0, [x1, #0]
	str q0, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x2, x2, #1
	cbnz x2, 227b
226:
	movz x0, #14336, lsl #0
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
	bl {vg_mldsa_montgomery_product}
	movz x0, #15360, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #14336, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	bl {vg_mldsa_sub}
	movz x0, #15360, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	bl {vg_mldsa_montgomery_inv_ntt}
	movz x0, #61696, lsl #0
	add x0, x28, x0
	movz x1, #64512, lsl #0
	add x1, x28, x1
	movz x2, #15360, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	movz x3, #65280, lsl #0
	movk x3, #3, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	bl {vg_mldsa_usehint_pack4}
	movz x0, #15360, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #25600, lsl #0
	add x1, x28, x1
	movz x2, #5120, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_montgomery_dot7}
	cbnz x22, 228f
	add x0, x25, #992
	movz x1, #13312, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	bl {vg_mldsa_unpack_t1}
	movz x0, #13312, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	b 229f
228:
	movz x0, #13312, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	add x1, x21, #3072
	movz x2, #64, lsl #0
230:
	ldr q0, [x1, #0]
	str q0, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x2, x2, #1
	cbnz x2, 230b
229:
	movz x0, #14336, lsl #0
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
	bl {vg_mldsa_montgomery_product}
	movz x0, #15360, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #14336, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	bl {vg_mldsa_sub}
	movz x0, #15360, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	bl {vg_mldsa_montgomery_inv_ntt}
	movz x0, #61824, lsl #0
	add x0, x28, x0
	movz x1, #0, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	movz x2, #15360, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	movz x3, #65280, lsl #0
	movk x3, #3, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	bl {vg_mldsa_usehint_pack4}
	movz x0, #15360, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #32768, lsl #0
	add x1, x28, x1
	movz x2, #5120, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_montgomery_dot7}
	cbnz x22, 231f
	add x0, x25, #1312
	movz x1, #13312, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	bl {vg_mldsa_unpack_t1}
	movz x0, #13312, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	b 232f
231:
	movz x0, #13312, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #4096, lsl #0
	add x1, x21, x1
	movz x2, #64, lsl #0
233:
	ldr q0, [x1, #0]
	str q0, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x2, x2, #1
	cbnz x2, 233b
232:
	movz x0, #14336, lsl #0
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
	bl {vg_mldsa_montgomery_product}
	movz x0, #15360, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #14336, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	bl {vg_mldsa_sub}
	movz x0, #15360, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	bl {vg_mldsa_montgomery_inv_ntt}
	movz x0, #61952, lsl #0
	add x0, x28, x0
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
	movz x3, #65280, lsl #0
	movk x3, #3, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	bl {vg_mldsa_usehint_pack4}
	movz x0, #15360, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #39936, lsl #0
	add x1, x28, x1
	movz x2, #5120, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_montgomery_dot7}
	cbnz x22, 234f
	add x0, x25, #1632
	movz x1, #13312, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	bl {vg_mldsa_unpack_t1}
	movz x0, #13312, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	b 235f
234:
	movz x0, #13312, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #5120, lsl #0
	add x1, x21, x1
	movz x2, #64, lsl #0
236:
	ldr q0, [x1, #0]
	str q0, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x2, x2, #1
	cbnz x2, 236b
235:
	movz x0, #14336, lsl #0
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
	bl {vg_mldsa_montgomery_product}
	movz x0, #15360, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #14336, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	bl {vg_mldsa_sub}
	movz x0, #15360, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	bl {vg_mldsa_montgomery_inv_ntt}
	movz x0, #62080, lsl #0
	add x0, x28, x0
	movz x1, #2048, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	movz x2, #15360, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	movz x3, #65280, lsl #0
	movk x3, #3, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	bl {vg_mldsa_usehint_pack4}
	movz x0, #15360, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #47104, lsl #0
	add x1, x28, x1
	movz x2, #5120, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_montgomery_dot7}
	cbnz x22, 237f
	add x0, x25, #1952
	movz x1, #13312, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	bl {vg_mldsa_unpack_t1}
	movz x0, #13312, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	b 238f
237:
	movz x0, #13312, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #6144, lsl #0
	add x1, x21, x1
	movz x2, #64, lsl #0
239:
	ldr q0, [x1, #0]
	str q0, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x2, x2, #1
	cbnz x2, 239b
238:
	movz x0, #14336, lsl #0
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
	bl {vg_mldsa_montgomery_product}
	movz x0, #15360, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #14336, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	bl {vg_mldsa_sub}
	movz x0, #15360, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	bl {vg_mldsa_montgomery_inv_ntt}
	movz x0, #62208, lsl #0
	add x0, x28, x0
	movz x1, #3072, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	movz x2, #15360, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	movz x3, #65280, lsl #0
	movk x3, #3, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	bl {vg_mldsa_usehint_pack4}
	movz x0, #15360, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #54272, lsl #0
	add x1, x28, x1
	movz x2, #5120, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x2, x28, x2
	bl {vg_mldsa_montgomery_dot7}
	cbnz x22, 240f
	add x0, x25, #2272
	movz x1, #13312, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	bl {vg_mldsa_unpack_t1}
	movz x0, #13312, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	b 241f
240:
	movz x0, #13312, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #7168, lsl #0
	add x1, x21, x1
	movz x2, #64, lsl #0
242:
	ldr q0, [x1, #0]
	str q0, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x2, x2, #1
	cbnz x2, 242b
241:
	movz x0, #14336, lsl #0
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
	bl {vg_mldsa_montgomery_product}
	movz x0, #15360, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	movz x1, #14336, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	bl {vg_mldsa_sub}
	movz x0, #15360, lsl #0
	movk x0, #1, lsl #16
	movk x0, #0, lsl #32
	movk x0, #0, lsl #48
	add x0, x28, x0
	bl {vg_mldsa_montgomery_inv_ntt}
	movz x0, #62336, lsl #0
	add x0, x28, x0
	movz x1, #4096, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	add x1, x28, x1
	movz x2, #15360, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
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
	movz x3, #61440, lsl #0
	add x3, x28, x3
	movz x4, #1024, lsl #0
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
	movz x4, #64, lsl #0
	bl {vg_keccak_squeeze_scratch_sha3}
	add x0, x28, #1024
	add x1, x27, #0
	movz x2, #64, lsl #0
	movz x10, #0, lsl #0
243:
	ldrb w9, [x0, #0]
	ldrb w11, [x1, #0]
	eor x9, x9, x11
	orr x10, x10, x9
	add x0, x0, #1
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 243b
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
	ldr x22, [sp], #16
	ldr x21, [sp], #16
	ret
	.p2align 6
