// The functions of `src/internal/vg_mldsa65_sign_with_cache_sha3.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa65_sign_with_cache_sha3:
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
	cbnz x22, 22f
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
	b 23f
22:
	movz x0, #32768, lsl #0
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
	movz x0, #33792, lsl #0
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
	movz x0, #34816, lsl #0
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
	movz x0, #35840, lsl #0
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
	movz x0, #36864, lsl #0
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
	movz x0, #37888, lsl #0
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
	movz x0, #38912, lsl #0
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
	movz x0, #39936, lsl #0
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
	movz x0, #40960, lsl #0
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
	movz x0, #41984, lsl #0
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
	movz x0, #43008, lsl #0
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
	movz x0, #44032, lsl #0
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
	movz x0, #45056, lsl #0
	add x0, x28, x0
	movz x1, #12288, lsl #0
	add x1, x21, x1
	movz x2, #64, lsl #0
216:
	ldr q0, [x1, #0]
	str q0, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x2, x2, #1
	cbnz x2, 216b
	movz x0, #46080, lsl #0
	add x0, x28, x0
	movz x1, #13312, lsl #0
	add x1, x21, x1
	movz x2, #64, lsl #0
217:
	ldr q0, [x1, #0]
	str q0, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x2, x2, #1
	cbnz x2, 217b
	movz x0, #47104, lsl #0
	add x0, x28, x0
	movz x1, #14336, lsl #0
	add x1, x21, x1
	movz x2, #64, lsl #0
218:
	ldr q0, [x1, #0]
	str q0, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x2, x2, #1
	cbnz x2, 218b
	movz x0, #48128, lsl #0
	add x0, x28, x0
	movz x1, #15360, lsl #0
	add x1, x21, x1
	movz x2, #64, lsl #0
219:
	ldr q0, [x1, #0]
	str q0, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x2, x2, #1
	cbnz x2, 219b
	movz x0, #49152, lsl #0
	add x0, x28, x0
	movz x1, #16384, lsl #0
	add x1, x21, x1
	movz x2, #64, lsl #0
220:
	ldr q0, [x1, #0]
	str q0, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x2, x2, #1
	cbnz x2, 220b
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
23:
	movz x9, #0, lsl #0
	str x9, [x28, #904]
	movz x9, #814, lsl #0
	str x9, [x28, #896]
221:
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
	cbnz x9, 222f
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
	b 223f
222:
	movz x0, #20480, lsl #0
	add x0, x28, x0
	movz x1, #9216, lsl #0
	add x1, x28, x1
	movz x2, #128, lsl #0
224:
	ldr x9, [x1, #0]
	str x9, [x0, #0]
	add x0, x0, #8
	add x1, x1, #8
	sub x2, x2, #1
	cbnz x2, 224b
223:
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
	cbnz w0, 225f
	movz x24, #0, lsl #0
	movz x9, #1, lsl #0
	str x9, [x28, #896]
	b 226f
225:
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
	cbnz w24, 227f
	b 228f
227:
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
	cbnz w24, 229f
	b 230f
229:
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
230:
228:
	cbnz w24, 231f
	ldr x9, [x28, #904]
	add x9, x9, #5
	str x9, [x28, #904]
	b 232f
231:
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
	cbnz w24, 233f
	b 234f
233:
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
	cbnz w24, 235f
	b 236f
235:
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
	cbnz w24, 237f
	b 238f
237:
238:
236:
234:
	cbnz w24, 239f
	ldr x9, [x28, #904]
	add x9, x9, #5
	str x9, [x28, #904]
	b 240f
239:
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
	cbnz w24, 241f
	ldr x9, [x28, #904]
	add x9, x9, #5
	str x9, [x28, #904]
	b 242f
241:
	movz x9, #1, lsl #0
	str x9, [x28, #896]
242:
240:
232:
226:
	ldr x9, [x28, #896]
	sub x9, x9, #1
	str x9, [x28, #896]
	cbnz x9, 221b
	cbnz w24, 243f
	b 244f
243:
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
245:
	ldrb w9, [x1, #0]
	strb w9, [x0, #0]
	add x0, x0, #1
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 245b
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
244:
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
