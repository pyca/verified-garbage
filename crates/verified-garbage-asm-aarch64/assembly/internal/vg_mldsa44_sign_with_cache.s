// The functions of `src/internal/vg_mldsa44_sign_with_cache.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa44_sign_with_cache:
	str x21, [sp, #-16]!
	str x22, [sp, #-16]!
	add x21, x5, #0
	add x22, x6, #0
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
	movz x1, #38912, lsl #0
	add x1, x28, x1
	movz x2, #55296, lsl #0
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
	movz x9, #1, lsl #0
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
	movz x9, #2, lsl #0
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
	movz x9, #3, lsl #0
	strb w9, [x28, #1542]
	movz x9, #1, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #43008, lsl #0
	add x1, x28, x1
	movz x2, #55296, lsl #0
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
	movz x9, #1, lsl #0
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
	movz x9, #2, lsl #0
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
	movz x9, #3, lsl #0
	strb w9, [x28, #1542]
	movz x9, #2, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #47104, lsl #0
	add x1, x28, x1
	movz x2, #55296, lsl #0
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
	movz x9, #1, lsl #0
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
	movz x9, #2, lsl #0
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
	movz x9, #3, lsl #0
	strb w9, [x28, #1542]
	movz x9, #3, lsl #0
	strb w9, [x28, #1543]
	add x0, x28, #1408
	movz x1, #51200, lsl #0
	add x1, x28, x1
	movz x2, #55296, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_rej_ntt_poly4}
	and w24, w24, w0
	cbnz w24, 20f
	b 21f
20:
	cbnz x22, 22f
	add x0, x25, #128
	movz x1, #96, lsl #0
	movz x2, #2, lsl #0
	movz x3, #2, lsl #0
	movz x4, #26624, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #26624, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #224
	movz x1, #96, lsl #0
	movz x2, #2, lsl #0
	movz x3, #2, lsl #0
	movz x4, #27648, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #27648, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #320
	movz x1, #96, lsl #0
	movz x2, #2, lsl #0
	movz x3, #2, lsl #0
	movz x4, #28672, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #416
	movz x1, #96, lsl #0
	movz x2, #2, lsl #0
	movz x3, #2, lsl #0
	movz x4, #29696, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #29696, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #512
	movz x1, #96, lsl #0
	movz x2, #2, lsl #0
	movz x3, #2, lsl #0
	movz x4, #30720, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #30720, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #608
	movz x1, #96, lsl #0
	movz x2, #2, lsl #0
	movz x3, #2, lsl #0
	movz x4, #31744, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #31744, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #704
	movz x1, #96, lsl #0
	movz x2, #2, lsl #0
	movz x3, #2, lsl #0
	movz x4, #32768, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #32768, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #800
	movz x1, #96, lsl #0
	movz x2, #2, lsl #0
	movz x3, #2, lsl #0
	movz x4, #33792, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #33792, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #896
	movz x1, #416, lsl #0
	movz x2, #4095, lsl #0
	movz x3, #4096, lsl #0
	movz x4, #34816, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #34816, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #1312
	movz x1, #416, lsl #0
	movz x2, #4095, lsl #0
	movz x3, #4096, lsl #0
	movz x4, #35840, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #35840, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #1728
	movz x1, #416, lsl #0
	movz x2, #4095, lsl #0
	movz x3, #4096, lsl #0
	movz x4, #36864, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #36864, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	add x0, x25, #2144
	movz x1, #416, lsl #0
	movz x2, #4095, lsl #0
	movz x3, #4096, lsl #0
	movz x4, #37888, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #37888, lsl #0
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
	b 23f
22:
	movz x0, #26624, lsl #0
	add x0, x28, x0
	add x1, x21, #0
	movz x2, #64, lsl #0
24:
	ldr q0, [x1, #0]
	str q0, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x2, x2, #1
	cbnz x2, 24b
	movz x0, #27648, lsl #0
	add x0, x28, x0
	add x1, x21, #1024
	movz x2, #64, lsl #0
25:
	ldr q0, [x1, #0]
	str q0, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x2, x2, #1
	cbnz x2, 25b
	movz x0, #28672, lsl #0
	add x0, x28, x0
	add x1, x21, #2048
	movz x2, #64, lsl #0
26:
	ldr q0, [x1, #0]
	str q0, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x2, x2, #1
	cbnz x2, 26b
	movz x0, #29696, lsl #0
	add x0, x28, x0
	add x1, x21, #3072
	movz x2, #64, lsl #0
27:
	ldr q0, [x1, #0]
	str q0, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x2, x2, #1
	cbnz x2, 27b
	movz x0, #30720, lsl #0
	add x0, x28, x0
	movz x1, #4096, lsl #0
	add x1, x21, x1
	movz x2, #64, lsl #0
28:
	ldr q0, [x1, #0]
	str q0, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x2, x2, #1
	cbnz x2, 28b
	movz x0, #31744, lsl #0
	add x0, x28, x0
	movz x1, #5120, lsl #0
	add x1, x21, x1
	movz x2, #64, lsl #0
29:
	ldr q0, [x1, #0]
	str q0, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x2, x2, #1
	cbnz x2, 29b
	movz x0, #32768, lsl #0
	add x0, x28, x0
	movz x1, #6144, lsl #0
	add x1, x21, x1
	movz x2, #64, lsl #0
210:
	ldr q0, [x1, #0]
	str q0, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x2, x2, #1
	cbnz x2, 210b
	movz x0, #33792, lsl #0
	add x0, x28, x0
	movz x1, #7168, lsl #0
	add x1, x21, x1
	movz x2, #64, lsl #0
211:
	ldr q0, [x1, #0]
	str q0, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x2, x2, #1
	cbnz x2, 211b
	movz x0, #34816, lsl #0
	add x0, x28, x0
	movz x1, #8192, lsl #0
	add x1, x21, x1
	movz x2, #64, lsl #0
212:
	ldr q0, [x1, #0]
	str q0, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x2, x2, #1
	cbnz x2, 212b
	movz x0, #35840, lsl #0
	add x0, x28, x0
	movz x1, #9216, lsl #0
	add x1, x21, x1
	movz x2, #64, lsl #0
213:
	ldr q0, [x1, #0]
	str q0, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x2, x2, #1
	cbnz x2, 213b
	movz x0, #36864, lsl #0
	add x0, x28, x0
	movz x1, #10240, lsl #0
	add x1, x21, x1
	movz x2, #64, lsl #0
214:
	ldr q0, [x1, #0]
	str q0, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x2, x2, #1
	cbnz x2, 214b
	movz x0, #37888, lsl #0
	add x0, x28, x0
	movz x1, #11264, lsl #0
	add x1, x21, x1
	movz x2, #64, lsl #0
215:
	ldr q0, [x1, #0]
	str q0, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x2, x2, #1
	cbnz x2, 215b
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
23:
	movz x9, #0, lsl #0
	str x9, [x28, #904]
	movz x9, #814, lsl #0
	str x9, [x28, #896]
216:
	ldr x9, [x28, #904]
	add x9, x9, #0
	strb w9, [x28, #1024]
	lsr x9, x9, #8
	strb w9, [x28, #1025]
	add x0, x28, #960
	movz x1, #0, lsl #0
	movk x1, #2, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	movz x2, #14336, lsl #0
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
	cbz x9, 217f
	add x2, x25, #840
	add x3, x26, #0
	movz x5, #64, lsl #0
	movz x8, #15, lsl #16
	movk x8, #65535, lsl #0
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
219:
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
	cbnz x5, 219b
	b 218f
217:
	add x2, x25, #840
	add x3, x26, #0
	movz x5, #64, lsl #0
	movz x8, #3, lsl #16
	movk x8, #65535, lsl #0
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
220:
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
	cbnz x5, 220b
218:
	ldr x30, [x25, #2040]
	ldr x26, [x25, #2024]
	ldr x27, [x25, #2032]
	ldr x25, [x25, #2016]
	movz x0, #18432, lsl #0
	add x0, x28, x0
	movz x1, #14336, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_ntt_positive_from}
	ldr x9, [x28, #904]
	add x9, x9, #1
	strb w9, [x28, #1024]
	lsr x9, x9, #8
	strb w9, [x28, #1025]
	add x0, x28, #960
	movz x1, #0, lsl #0
	movk x1, #2, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	movz x2, #15360, lsl #0
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
	cbz x9, 221f
	add x2, x25, #840
	add x3, x26, #0
	movz x5, #64, lsl #0
	movz x8, #15, lsl #16
	movk x8, #65535, lsl #0
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
223:
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
	cbnz x5, 223b
	b 222f
221:
	add x2, x25, #840
	add x3, x26, #0
	movz x5, #64, lsl #0
	movz x8, #3, lsl #16
	movk x8, #65535, lsl #0
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
224:
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
	cbnz x5, 224b
222:
	ldr x30, [x25, #2040]
	ldr x26, [x25, #2024]
	ldr x27, [x25, #2032]
	ldr x25, [x25, #2016]
	movz x0, #19456, lsl #0
	add x0, x28, x0
	movz x1, #15360, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_ntt_positive_from}
	ldr x9, [x28, #904]
	add x9, x9, #2
	strb w9, [x28, #1024]
	lsr x9, x9, #8
	strb w9, [x28, #1025]
	add x0, x28, #960
	movz x1, #0, lsl #0
	movk x1, #2, lsl #16
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
	cbz x9, 225f
	add x2, x25, #840
	add x3, x26, #0
	movz x5, #64, lsl #0
	movz x8, #15, lsl #16
	movk x8, #65535, lsl #0
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
227:
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
	cbnz x5, 227b
	b 226f
225:
	add x2, x25, #840
	add x3, x26, #0
	movz x5, #64, lsl #0
	movz x8, #3, lsl #16
	movk x8, #65535, lsl #0
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
228:
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
	cbnz x5, 228b
226:
	ldr x30, [x25, #2040]
	ldr x26, [x25, #2024]
	ldr x27, [x25, #2032]
	ldr x25, [x25, #2016]
	movz x0, #20480, lsl #0
	add x0, x28, x0
	movz x1, #16384, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_ntt_positive_from}
	ldr x9, [x28, #904]
	add x9, x9, #3
	strb w9, [x28, #1024]
	lsr x9, x9, #8
	strb w9, [x28, #1025]
	add x0, x28, #960
	movz x1, #0, lsl #0
	movk x1, #2, lsl #16
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
	cbz x9, 229f
	add x2, x25, #840
	add x3, x26, #0
	movz x5, #64, lsl #0
	movz x8, #15, lsl #16
	movk x8, #65535, lsl #0
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
231:
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
	cbnz x5, 231b
	b 230f
229:
	add x2, x25, #840
	add x3, x26, #0
	movz x5, #64, lsl #0
	movz x8, #3, lsl #16
	movk x8, #65535, lsl #0
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
232:
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
	cbnz x5, 232b
230:
	ldr x30, [x25, #2040]
	ldr x26, [x25, #2024]
	ldr x27, [x25, #2032]
	ldr x25, [x25, #2016]
	movz x0, #21504, lsl #0
	add x0, x28, x0
	movz x1, #17408, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_ntt_positive_from}
	movz x0, #22528, lsl #0
	add x0, x28, x0
	movz x1, #38912, lsl #0
	add x1, x28, x1
	movz x2, #18432, lsl #0
	add x2, x28, x2
	add x3, x28, #3072
	bl {vg_mldsa_dot_inverse4}
	movz x0, #23552, lsl #0
	add x0, x28, x0
	movz x1, #43008, lsl #0
	add x1, x28, x1
	movz x2, #18432, lsl #0
	add x2, x28, x2
	add x3, x28, #3072
	bl {vg_mldsa_dot_inverse4}
	movz x0, #24576, lsl #0
	add x0, x28, x0
	movz x1, #47104, lsl #0
	add x1, x28, x1
	movz x2, #18432, lsl #0
	add x2, x28, x2
	add x3, x28, #3072
	bl {vg_mldsa_dot_inverse4}
	movz x0, #25600, lsl #0
	add x0, x28, x0
	movz x1, #51200, lsl #0
	add x1, x28, x1
	movz x2, #18432, lsl #0
	add x2, x28, x2
	add x3, x28, #3072
	bl {vg_mldsa_dot_inverse4}
	movz x0, #22528, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_high_pack6}
	movz x0, #23552, lsl #0
	add x0, x28, x0
	add x1, x28, #2240
	bl {vg_mldsa_high_pack6}
	movz x0, #24576, lsl #0
	add x0, x28, x0
	add x1, x28, #2432
	bl {vg_mldsa_high_pack6}
	movz x0, #25600, lsl #0
	add x0, x28, x0
	add x1, x28, #2624
	bl {vg_mldsa_high_pack6}
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
	movz x4, #32, lsl #0
	bl {vg_keccak_squeeze_scratch}
	add x0, x28, #1040
	movz x1, #32, lsl #0
	movz x2, #39, lsl #0
	movz x3, #5120, lsl #0
	add x3, x28, x3
	add x4, x28, #3072
	bl {vg_mldsa_sample_in_ball}
	cbnz w0, 233f
	movz x24, #0, lsl #0
	movz x9, #1, lsl #0
	str x9, [x28, #896]
	b 234f
233:
	movz x0, #5120, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_ntt_positive}
	movz x24, #1, lsl #0
	movz x9, #0, lsl #0
	str x9, [x28, #912]
	movz x0, #5120, lsl #0
	add x0, x28, x0
	movz x1, #26624, lsl #0
	add x1, x28, x1
	movz x2, #14336, lsl #0
	add x2, x28, x2
	movz x3, #6144, lsl #0
	add x3, x28, x3
	movz x4, #6144, lsl #0
	add x4, x28, x4
	movz x5, #0, lsl #0
	movk x5, #2, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #65458, lsl #0
	movk x6, #1, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	bl {vg_mldsa_fused_pair_z}
	and w24, w24, w0
	cbnz w24, 235f
	b 236f
235:
	movz x0, #5120, lsl #0
	add x0, x28, x0
	movz x1, #28672, lsl #0
	add x1, x28, x1
	movz x2, #16384, lsl #0
	add x2, x28, x2
	movz x3, #6144, lsl #0
	add x3, x28, x3
	movz x4, #6144, lsl #0
	add x4, x28, x4
	movz x5, #0, lsl #0
	movk x5, #2, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #65458, lsl #0
	movk x6, #1, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	bl {vg_mldsa_fused_pair_z}
	and w24, w24, w0
	cbnz w24, 237f
	b 238f
237:
238:
236:
	cbnz w24, 239f
	ldr x9, [x28, #904]
	add x9, x9, #4
	str x9, [x28, #904]
	b 240f
239:
	movz x0, #5120, lsl #0
	add x0, x28, x0
	movz x1, #30720, lsl #0
	add x1, x28, x1
	movz x2, #22528, lsl #0
	add x2, x28, x2
	movz x3, #10240, lsl #0
	add x3, x28, x3
	movz x4, #6144, lsl #0
	add x4, x28, x4
	movz x5, #29696, lsl #0
	movk x5, #1, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #29618, lsl #0
	movk x6, #1, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	bl {vg_mldsa_fused_pair_r0}
	and w24, w24, w0
	cbnz w24, 241f
	b 242f
241:
	movz x0, #5120, lsl #0
	add x0, x28, x0
	movz x1, #32768, lsl #0
	add x1, x28, x1
	movz x2, #24576, lsl #0
	add x2, x28, x2
	movz x3, #12288, lsl #0
	add x3, x28, x3
	movz x4, #6144, lsl #0
	add x4, x28, x4
	movz x5, #29696, lsl #0
	movk x5, #1, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #29618, lsl #0
	movk x6, #1, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	bl {vg_mldsa_fused_pair_r0}
	and w24, w24, w0
	cbnz w24, 243f
	b 244f
243:
244:
242:
	cbnz w24, 245f
	ldr x9, [x28, #904]
	add x9, x9, #4
	str x9, [x28, #904]
	b 246f
245:
	movz x0, #5120, lsl #0
	add x0, x28, x0
	movz x1, #34816, lsl #0
	add x1, x28, x1
	movz x2, #10240, lsl #0
	add x2, x28, x2
	movz x3, #22528, lsl #0
	add x3, x28, x3
	movz x4, #6144, lsl #0
	add x4, x28, x4
	movz x5, #29696, lsl #0
	movk x5, #1, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #29696, lsl #0
	movk x6, #1, lsl #16
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
	movz x1, #36864, lsl #0
	add x1, x28, x1
	movz x2, #12288, lsl #0
	add x2, x28, x2
	movz x3, #24576, lsl #0
	add x3, x28, x3
	movz x4, #6144, lsl #0
	add x4, x28, x4
	movz x5, #29696, lsl #0
	movk x5, #1, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #29696, lsl #0
	movk x6, #1, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	bl {vg_mldsa_fused_pair_h}
	ldr x9, [x28, #912]
	add w9, w9, w0
	str x9, [x28, #912]
	lsr x0, x0, #32
	and w24, w24, w0
	ldr x9, [x28, #912]
	sub x9, x9, #81
	lsr x9, x9, #63
	and w24, w24, w9
	cbnz w24, 247f
	ldr x9, [x28, #904]
	add x9, x9, #4
	str x9, [x28, #904]
	b 248f
247:
	movz x9, #1, lsl #0
	str x9, [x28, #896]
248:
246:
240:
234:
	ldr x9, [x28, #896]
	sub x9, x9, #1
	str x9, [x28, #896]
	cbnz x9, 216b
	cbnz w24, 249f
	b 250f
249:
	movz x0, #14336, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_canonicalize_signed}
	movz x0, #15360, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_canonicalize_signed}
	movz x0, #16384, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_canonicalize_signed}
	movz x0, #17408, lsl #0
	add x0, x28, x0
	bl {vg_mldsa_canonicalize_signed}
	add x0, x23, #0
	add x1, x28, #1040
	movz x2, #32, lsl #0
251:
	ldrb w9, [x1, #0]
	strb w9, [x0, #0]
	add x0, x0, #1
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 251b
	movz x0, #14336, lsl #0
	add x0, x28, x0
	movz x1, #65535, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	movz x2, #0, lsl #0
	movk x2, #2, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x3, x23, #32
	movz x4, #576, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #15360, lsl #0
	add x0, x28, x0
	movz x1, #65535, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	movz x2, #0, lsl #0
	movk x2, #2, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x3, x23, #608
	movz x4, #576, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #16384, lsl #0
	add x0, x28, x0
	movz x1, #65535, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	movz x2, #0, lsl #0
	movk x2, #2, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x3, x23, #1184
	movz x4, #576, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #17408, lsl #0
	add x0, x28, x0
	movz x1, #65535, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	movz x2, #0, lsl #0
	movk x2, #2, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	add x3, x23, #1760
	movz x4, #576, lsl #0
	bl {vg_mldsa_bit_pack}
	movz x0, #10240, lsl #0
	add x0, x28, x0
	movz x1, #1024, lsl #0
	movz x2, #80, lsl #0
	add x3, x23, #2336
	movz x4, #84, lsl #0
	bl {vg_mldsa_hint_bit_pack}
250:
21:
	add x0, x24, #0
	ldr x23, [x28, #840]
	ldr x24, [x28, #848]
	ldr x25, [x28, #856]
	ldr x26, [x28, #864]
	ldr x27, [x28, #872]
	ldr x30, [x28, #880]
	ldr x28, [x28, #888]
	ldr x22, [sp], #16
	ldr x21, [sp], #16
	ret
	.p2align 6
