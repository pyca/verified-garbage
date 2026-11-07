// The functions of `src/internal/vg_mldsa44_verify_with_cache.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa44_verify_with_cache:
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
	add x0, x27, #2336
	movz x1, #84, lsl #0
	movz x2, #80, lsl #0
	movz x3, #21504, lsl #0
	add x3, x28, x3
	movz x4, #1024, lsl #0
	bl {vg_mldsa_hint_bit_unpack}
	and w24, w24, w0
	cbnz x24, 20f
	b 21f
20:
	add x0, x27, #32
	movz x1, #576, lsl #0
	movz x2, #65535, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	movz x3, #0, lsl #0
	movk x3, #2, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	movz x4, #25600, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #25600, lsl #0
	add x0, x28, x0
	movz x1, #65458, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	bl {vg_mldsa_norm_lt}
	and w24, w24, w0
	add x0, x27, #608
	movz x1, #576, lsl #0
	movz x2, #65535, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	movz x3, #0, lsl #0
	movk x3, #2, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	movz x4, #26624, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #26624, lsl #0
	add x0, x28, x0
	movz x1, #65458, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	bl {vg_mldsa_norm_lt}
	and w24, w24, w0
	add x0, x27, #1184
	movz x1, #576, lsl #0
	movz x2, #65535, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	movz x3, #0, lsl #0
	movk x3, #2, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	movz x4, #27648, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #27648, lsl #0
	add x0, x28, x0
	movz x1, #65458, lsl #0
	movk x1, #1, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	bl {vg_mldsa_norm_lt}
	and w24, w24, w0
	add x0, x27, #1760
	movz x1, #576, lsl #0
	movz x2, #65535, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	movz x3, #0, lsl #0
	movk x3, #2, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	movz x4, #28672, lsl #0
	add x4, x28, x4
	bl {vg_mldsa_bit_unpack}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	movz x1, #65458, lsl #0
	movk x1, #1, lsl #16
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
	movz x2, #31744, lsl #0
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
27:
	ldr w9, [x1, #0]
	and w9, w9, w8
	str w9, [x1, #0]
	add x1, x1, #4
	sub x2, x2, #1
	cbnz x2, 27b
	add x0, x27, #0
	movz x1, #32, lsl #0
	movz x2, #39, lsl #0
	movz x3, #29696, lsl #0
	add x3, x28, x3
	add x4, x28, #2048
	bl {vg_mldsa_sample_in_ball}
	and w24, w24, w0
	movz x8, #0, lsl #0
	sub w8, w8, w0
	movz x1, #29696, lsl #0
	add x1, x28, x1
	movz x2, #256, lsl #0
28:
	ldr w9, [x1, #0]
	and w9, w9, w8
	str w9, [x1, #0]
	add x1, x1, #4
	sub x2, x2, #1
	cbnz x2, 28b
	movz x0, #25600, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_ntt}
	movz x0, #26624, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_ntt}
	movz x0, #27648, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_ntt}
	movz x0, #28672, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_ntt}
	movz x0, #29696, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_ntt}
	movz x0, #32768, lsl #0
	add x0, x28, x0
	movz x1, #4096, lsl #0
	add x1, x28, x1
	movz x2, #25600, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_ntt}
	movz x0, #32768, lsl #0
	add x0, x28, x0
	movz x1, #5120, lsl #0
	add x1, x28, x1
	movz x2, #26624, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #32768, lsl #0
	add x0, x28, x0
	movz x1, #6144, lsl #0
	add x1, x28, x1
	movz x2, #27648, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #32768, lsl #0
	add x0, x28, x0
	movz x1, #7168, lsl #0
	add x1, x28, x1
	movz x2, #28672, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	cbnz x22, 29f
	add x0, x25, #32
	movz x1, #30720, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_unpack_t1}
	movz x0, #30720, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_ntt}
	b 210f
29:
	movz x0, #30720, lsl #0
	add x0, x28, x0
	add x1, x21, #0
	movz x2, #64, lsl #0
211:
	ldr q0, [x1, #0]
	str q0, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x2, x2, #1
	cbnz x2, 211b
210:
	movz x0, #31744, lsl #0
	add x0, x28, x0
	movz x1, #29696, lsl #0
	add x1, x28, x1
	movz x2, #30720, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_ntt}
	movz x0, #32768, lsl #0
	add x0, x28, x0
	movz x1, #31744, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_sub}
	movz x0, #32768, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_inv_ntt}
	movz x0, #21504, lsl #0
	add x0, x28, x0
	movz x1, #32768, lsl #0
	add x1, x28, x1
	movz x2, #29696, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	movz x3, #33792, lsl #0
	add x3, x28, x3
	bl {vg_mldsa_use_hint}
	movz x0, #33792, lsl #0
	add x0, x28, x0
	movz x1, #43, lsl #0
	movz x2, #20480, lsl #0
	add x2, x28, x2
	movz x3, #192, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #32768, lsl #0
	add x0, x28, x0
	movz x1, #8192, lsl #0
	add x1, x28, x1
	movz x2, #25600, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_ntt}
	movz x0, #32768, lsl #0
	add x0, x28, x0
	movz x1, #9216, lsl #0
	add x1, x28, x1
	movz x2, #26624, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #32768, lsl #0
	add x0, x28, x0
	movz x1, #10240, lsl #0
	add x1, x28, x1
	movz x2, #27648, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #32768, lsl #0
	add x0, x28, x0
	movz x1, #11264, lsl #0
	add x1, x28, x1
	movz x2, #28672, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	cbnz x22, 212f
	add x0, x25, #352
	movz x1, #30720, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_unpack_t1}
	movz x0, #30720, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_ntt}
	b 213f
212:
	movz x0, #30720, lsl #0
	add x0, x28, x0
	add x1, x21, #1024
	movz x2, #64, lsl #0
214:
	ldr q0, [x1, #0]
	str q0, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x2, x2, #1
	cbnz x2, 214b
213:
	movz x0, #31744, lsl #0
	add x0, x28, x0
	movz x1, #29696, lsl #0
	add x1, x28, x1
	movz x2, #30720, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_ntt}
	movz x0, #32768, lsl #0
	add x0, x28, x0
	movz x1, #31744, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_sub}
	movz x0, #32768, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_inv_ntt}
	movz x0, #22528, lsl #0
	add x0, x28, x0
	movz x1, #32768, lsl #0
	add x1, x28, x1
	movz x2, #29696, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	movz x3, #33792, lsl #0
	add x3, x28, x3
	bl {vg_mldsa_use_hint}
	movz x0, #33792, lsl #0
	add x0, x28, x0
	movz x1, #43, lsl #0
	movz x2, #20672, lsl #0
	add x2, x28, x2
	movz x3, #192, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #32768, lsl #0
	add x0, x28, x0
	movz x1, #12288, lsl #0
	add x1, x28, x1
	movz x2, #25600, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_ntt}
	movz x0, #32768, lsl #0
	add x0, x28, x0
	movz x1, #13312, lsl #0
	add x1, x28, x1
	movz x2, #26624, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #32768, lsl #0
	add x0, x28, x0
	movz x1, #14336, lsl #0
	add x1, x28, x1
	movz x2, #27648, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #32768, lsl #0
	add x0, x28, x0
	movz x1, #15360, lsl #0
	add x1, x28, x1
	movz x2, #28672, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	cbnz x22, 215f
	add x0, x25, #672
	movz x1, #30720, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_unpack_t1}
	movz x0, #30720, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_ntt}
	b 216f
215:
	movz x0, #30720, lsl #0
	add x0, x28, x0
	add x1, x21, #2048
	movz x2, #64, lsl #0
217:
	ldr q0, [x1, #0]
	str q0, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x2, x2, #1
	cbnz x2, 217b
216:
	movz x0, #31744, lsl #0
	add x0, x28, x0
	movz x1, #29696, lsl #0
	add x1, x28, x1
	movz x2, #30720, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_ntt}
	movz x0, #32768, lsl #0
	add x0, x28, x0
	movz x1, #31744, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_sub}
	movz x0, #32768, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_inv_ntt}
	movz x0, #23552, lsl #0
	add x0, x28, x0
	movz x1, #32768, lsl #0
	add x1, x28, x1
	movz x2, #29696, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	movz x3, #33792, lsl #0
	add x3, x28, x3
	bl {vg_mldsa_use_hint}
	movz x0, #33792, lsl #0
	add x0, x28, x0
	movz x1, #43, lsl #0
	movz x2, #20864, lsl #0
	add x2, x28, x2
	movz x3, #192, lsl #0
	bl {vg_mldsa_simple_bit_pack}
	movz x0, #32768, lsl #0
	add x0, x28, x0
	movz x1, #16384, lsl #0
	add x1, x28, x1
	movz x2, #25600, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_ntt}
	movz x0, #32768, lsl #0
	add x0, x28, x0
	movz x1, #17408, lsl #0
	add x1, x28, x1
	movz x2, #26624, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #32768, lsl #0
	add x0, x28, x0
	movz x1, #18432, lsl #0
	add x1, x28, x1
	movz x2, #27648, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	movz x0, #32768, lsl #0
	add x0, x28, x0
	movz x1, #19456, lsl #0
	add x1, x28, x1
	movz x2, #28672, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_add_ntt}
	cbnz x22, 218f
	add x0, x25, #992
	movz x1, #30720, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_unpack_t1}
	movz x0, #30720, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_ntt}
	b 219f
218:
	movz x0, #30720, lsl #0
	add x0, x28, x0
	add x1, x21, #3072
	movz x2, #64, lsl #0
220:
	ldr q0, [x1, #0]
	str q0, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x2, x2, #1
	cbnz x2, 220b
219:
	movz x0, #31744, lsl #0
	add x0, x28, x0
	movz x1, #29696, lsl #0
	add x1, x28, x1
	movz x2, #30720, lsl #0
	add x2, x28, x2
	bl {vg_mldsa_multiply_ntt}
	movz x0, #32768, lsl #0
	add x0, x28, x0
	movz x1, #31744, lsl #0
	add x1, x28, x1
	bl {vg_mldsa_sub}
	movz x0, #32768, lsl #0
	add x0, x28, x0
	add x1, x28, #2048
	bl {vg_mldsa_inv_ntt}
	movz x0, #24576, lsl #0
	add x0, x28, x0
	movz x1, #32768, lsl #0
	add x1, x28, x1
	movz x2, #29696, lsl #0
	movk x2, #1, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	movz x3, #33792, lsl #0
	add x3, x28, x3
	bl {vg_mldsa_use_hint}
	movz x0, #33792, lsl #0
	add x0, x28, x0
	movz x1, #43, lsl #0
	movz x2, #21056, lsl #0
	add x2, x28, x2
	movz x3, #192, lsl #0
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
	movz x3, #20480, lsl #0
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
	movz x4, #32, lsl #0
	bl {vg_keccak_squeeze_scratch}
	add x0, x28, #1024
	add x1, x27, #0
	movz x2, #32, lsl #0
	movz x10, #0, lsl #0
221:
	ldrb w9, [x0, #0]
	ldrb w11, [x1, #0]
	eor x9, x9, x11
	orr x10, x10, x9
	add x0, x0, #1
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 221b
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
