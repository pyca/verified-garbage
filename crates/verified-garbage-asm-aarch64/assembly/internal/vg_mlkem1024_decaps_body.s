// The functions of `src/internal/vg_mlkem1024_decaps_body.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem1024_decaps_body:
	str x24, [x3, #30392]
	str x30, [x3, #30400]
	str x25, [x3, #30408]
	str x26, [x3, #30416]
	str x27, [x3, #30424]
	str x28, [x3, #30432]
	add x25, x0, #0
	add x26, x1, #0
	add x27, x2, #0
	add x28, x3, #0
	movz x24, #1, lsl #0
	add x0, x26, #0
	movz x1, #352, lsl #0
	movz x2, #11, lsl #0
	movz x3, #20632, lsl #0
	add x3, x28, x3
	bl {vg_mlkem1024_decode_decompress}
	movz x0, #20632, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem_ntt}
	add x0, x26, #352
	movz x1, #352, lsl #0
	movz x2, #11, lsl #0
	movz x3, #21656, lsl #0
	add x3, x28, x3
	bl {vg_mlkem1024_decode_decompress}
	movz x0, #21656, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem_ntt}
	add x0, x26, #704
	movz x1, #352, lsl #0
	movz x2, #11, lsl #0
	movz x3, #22680, lsl #0
	add x3, x28, x3
	bl {vg_mlkem1024_decode_decompress}
	movz x0, #22680, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem_ntt}
	add x0, x26, #1056
	movz x1, #352, lsl #0
	movz x2, #11, lsl #0
	movz x3, #23704, lsl #0
	add x3, x28, x3
	bl {vg_mlkem1024_decode_decompress}
	movz x0, #23704, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem_ntt}
	add x0, x25, #0
	movz x1, #27800, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_decode12}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #27800, lsl #0
	add x1, x28, x1
	movz x2, #20632, lsl #0
	add x2, x28, x2
	add x3, x28, #3224
	bl {vg_mlkem_multiply_ntts}
	add x0, x25, #384
	movz x1, #27800, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_decode12}
	movz x0, #26776, lsl #0
	add x0, x28, x0
	movz x1, #27800, lsl #0
	add x1, x28, x1
	movz x2, #21656, lsl #0
	add x2, x28, x2
	add x3, x28, #3224
	bl {vg_mlkem_multiply_ntts}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #26776, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	add x0, x25, #768
	movz x1, #27800, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_decode12}
	movz x0, #26776, lsl #0
	add x0, x28, x0
	movz x1, #27800, lsl #0
	add x1, x28, x1
	movz x2, #22680, lsl #0
	add x2, x28, x2
	add x3, x28, #3224
	bl {vg_mlkem_multiply_ntts}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #26776, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	add x0, x25, #1152
	movz x1, #27800, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_decode12}
	movz x0, #26776, lsl #0
	add x0, x28, x0
	movz x1, #27800, lsl #0
	add x1, x28, x1
	movz x2, #23704, lsl #0
	add x2, x28, x2
	add x3, x28, #3224
	bl {vg_mlkem_multiply_ntts}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #26776, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem_inv_ntt}
	add x0, x26, #1408
	movz x1, #160, lsl #0
	movz x2, #5, lsl #0
	movz x3, #24728, lsl #0
	add x3, x28, x3
	bl {vg_mlkem1024_decode_decompress}
	movz x0, #24728, lsl #0
	add x0, x28, x0
	movz x1, #25752, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_sub}
	movz x0, #24728, lsl #0
	add x0, x28, x0
	movz x1, #1, lsl #0
	add x2, x28, #912
	movz x3, #32, lsl #0
	bl {vg_mlkem_compress_encode}
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
	movz x1, #72, lsl #0
	add x5, x28, #200
	add x3, x28, #912
	movz x4, #32, lsl #0
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	add x0, x28, #0
	movz x1, #72, lsl #0
	add x5, x28, #200
	add x3, x25, #3104
	movz x4, #32, lsl #0
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	add x0, x28, #0
	movz x1, #72, lsl #0
	add x4, x28, #200
	movz x3, #6, lsl #0
	bl {vg_keccak_pad_scratch}
	movz x2, #0, lsl #0
	add x0, x28, #0
	movz x1, #72, lsl #0
	add x5, x28, #200
	add x3, x28, #984
	movz x4, #32, lsl #0
	bl {vg_keccak_squeeze_scratch}
	add x2, x0, #0
	add x0, x28, #0
	movz x1, #72, lsl #0
	add x5, x28, #200
	add x3, x28, #944
	movz x4, #32, lsl #0
	bl {vg_keccak_squeeze_scratch}
	ldr x9, [x25, #3072]
	str x9, [x28, #840]
	ldr x9, [x25, #3080]
	str x9, [x28, #848]
	ldr x9, [x25, #3088]
	str x9, [x28, #856]
	ldr x9, [x25, #3096]
	str x9, [x28, #864]
	movz x9, #0, lsl #0
	strb w9, [x28, #872]
	movz x9, #0, lsl #0
	strb w9, [x28, #873]
	add x0, x28, #840
	movz x1, #4248, lsl #0
	add x1, x28, x1
	add x2, x28, #1176
	bl {vg_mlkem_sample_ntt}
	and x24, x24, x0
	movz x9, #1, lsl #0
	strb w9, [x28, #872]
	movz x9, #0, lsl #0
	strb w9, [x28, #873]
	add x0, x28, #840
	movz x1, #5272, lsl #0
	add x1, x28, x1
	add x2, x28, #1176
	bl {vg_mlkem_sample_ntt}
	and x24, x24, x0
	movz x9, #2, lsl #0
	strb w9, [x28, #872]
	movz x9, #0, lsl #0
	strb w9, [x28, #873]
	add x0, x28, #840
	movz x1, #6296, lsl #0
	add x1, x28, x1
	add x2, x28, #1176
	bl {vg_mlkem_sample_ntt}
	and x24, x24, x0
	movz x9, #3, lsl #0
	strb w9, [x28, #872]
	movz x9, #0, lsl #0
	strb w9, [x28, #873]
	add x0, x28, #840
	movz x1, #7320, lsl #0
	add x1, x28, x1
	add x2, x28, #1176
	bl {vg_mlkem_sample_ntt}
	and x24, x24, x0
	movz x9, #0, lsl #0
	strb w9, [x28, #872]
	movz x9, #1, lsl #0
	strb w9, [x28, #873]
	add x0, x28, #840
	movz x1, #8344, lsl #0
	add x1, x28, x1
	add x2, x28, #1176
	bl {vg_mlkem_sample_ntt}
	and x24, x24, x0
	movz x9, #1, lsl #0
	strb w9, [x28, #872]
	movz x9, #1, lsl #0
	strb w9, [x28, #873]
	add x0, x28, #840
	movz x1, #9368, lsl #0
	add x1, x28, x1
	add x2, x28, #1176
	bl {vg_mlkem_sample_ntt}
	and x24, x24, x0
	movz x9, #2, lsl #0
	strb w9, [x28, #872]
	movz x9, #1, lsl #0
	strb w9, [x28, #873]
	add x0, x28, #840
	movz x1, #10392, lsl #0
	add x1, x28, x1
	add x2, x28, #1176
	bl {vg_mlkem_sample_ntt}
	and x24, x24, x0
	movz x9, #3, lsl #0
	strb w9, [x28, #872]
	movz x9, #1, lsl #0
	strb w9, [x28, #873]
	add x0, x28, #840
	movz x1, #11416, lsl #0
	add x1, x28, x1
	add x2, x28, #1176
	bl {vg_mlkem_sample_ntt}
	and x24, x24, x0
	movz x9, #0, lsl #0
	strb w9, [x28, #872]
	movz x9, #2, lsl #0
	strb w9, [x28, #873]
	add x0, x28, #840
	movz x1, #12440, lsl #0
	add x1, x28, x1
	add x2, x28, #1176
	bl {vg_mlkem_sample_ntt}
	and x24, x24, x0
	movz x9, #1, lsl #0
	strb w9, [x28, #872]
	movz x9, #2, lsl #0
	strb w9, [x28, #873]
	add x0, x28, #840
	movz x1, #13464, lsl #0
	add x1, x28, x1
	add x2, x28, #1176
	bl {vg_mlkem_sample_ntt}
	and x24, x24, x0
	movz x9, #2, lsl #0
	strb w9, [x28, #872]
	movz x9, #2, lsl #0
	strb w9, [x28, #873]
	add x0, x28, #840
	movz x1, #14488, lsl #0
	add x1, x28, x1
	add x2, x28, #1176
	bl {vg_mlkem_sample_ntt}
	and x24, x24, x0
	movz x9, #3, lsl #0
	strb w9, [x28, #872]
	movz x9, #2, lsl #0
	strb w9, [x28, #873]
	add x0, x28, #840
	movz x1, #15512, lsl #0
	add x1, x28, x1
	add x2, x28, #1176
	bl {vg_mlkem_sample_ntt}
	and x24, x24, x0
	movz x9, #0, lsl #0
	strb w9, [x28, #872]
	movz x9, #3, lsl #0
	strb w9, [x28, #873]
	add x0, x28, #840
	movz x1, #16536, lsl #0
	add x1, x28, x1
	add x2, x28, #1176
	bl {vg_mlkem_sample_ntt}
	and x24, x24, x0
	movz x9, #1, lsl #0
	strb w9, [x28, #872]
	movz x9, #3, lsl #0
	strb w9, [x28, #873]
	add x0, x28, #840
	movz x1, #17560, lsl #0
	add x1, x28, x1
	add x2, x28, #1176
	bl {vg_mlkem_sample_ntt}
	and x24, x24, x0
	movz x9, #2, lsl #0
	strb w9, [x28, #872]
	movz x9, #3, lsl #0
	strb w9, [x28, #873]
	add x0, x28, #840
	movz x1, #18584, lsl #0
	add x1, x28, x1
	add x2, x28, #1176
	bl {vg_mlkem_sample_ntt}
	and x24, x24, x0
	movz x9, #3, lsl #0
	strb w9, [x28, #872]
	movz x9, #3, lsl #0
	strb w9, [x28, #873]
	add x0, x28, #840
	movz x1, #19608, lsl #0
	add x1, x28, x1
	add x2, x28, #1176
	bl {vg_mlkem_sample_ntt}
	and x24, x24, x0
	movz x9, #0, lsl #0
	strb w9, [x28, #976]
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
	add x3, x28, #944
	movz x4, #33, lsl #0
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
	add x3, x28, #1048
	movz x4, #128, lsl #0
	bl {vg_keccak_squeeze_scratch}
	add x0, x28, #1048
	movz x1, #20632, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_cbd2}
	movz x0, #20632, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem_ntt}
	movz x9, #1, lsl #0
	strb w9, [x28, #976]
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
	add x3, x28, #944
	movz x4, #33, lsl #0
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
	add x3, x28, #1048
	movz x4, #128, lsl #0
	bl {vg_keccak_squeeze_scratch}
	add x0, x28, #1048
	movz x1, #21656, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_cbd2}
	movz x0, #21656, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem_ntt}
	movz x9, #2, lsl #0
	strb w9, [x28, #976]
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
	add x3, x28, #944
	movz x4, #33, lsl #0
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
	add x3, x28, #1048
	movz x4, #128, lsl #0
	bl {vg_keccak_squeeze_scratch}
	add x0, x28, #1048
	movz x1, #22680, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_cbd2}
	movz x0, #22680, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem_ntt}
	movz x9, #3, lsl #0
	strb w9, [x28, #976]
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
	add x3, x28, #944
	movz x4, #33, lsl #0
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
	add x3, x28, #1048
	movz x4, #128, lsl #0
	bl {vg_keccak_squeeze_scratch}
	add x0, x28, #1048
	movz x1, #23704, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_cbd2}
	movz x0, #23704, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem_ntt}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #4248, lsl #0
	add x1, x28, x1
	movz x2, #20632, lsl #0
	add x2, x28, x2
	add x3, x28, #3224
	bl {vg_mlkem_multiply_ntts}
	movz x0, #26776, lsl #0
	add x0, x28, x0
	movz x1, #8344, lsl #0
	add x1, x28, x1
	movz x2, #21656, lsl #0
	add x2, x28, x2
	add x3, x28, #3224
	bl {vg_mlkem_multiply_ntts}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #26776, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	movz x0, #26776, lsl #0
	add x0, x28, x0
	movz x1, #12440, lsl #0
	add x1, x28, x1
	movz x2, #22680, lsl #0
	add x2, x28, x2
	add x3, x28, #3224
	bl {vg_mlkem_multiply_ntts}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #26776, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	movz x0, #26776, lsl #0
	add x0, x28, x0
	movz x1, #16536, lsl #0
	add x1, x28, x1
	movz x2, #23704, lsl #0
	add x2, x28, x2
	add x3, x28, #3224
	bl {vg_mlkem_multiply_ntts}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #26776, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem_inv_ntt}
	movz x9, #4, lsl #0
	strb w9, [x28, #976]
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
	add x3, x28, #944
	movz x4, #33, lsl #0
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
	add x3, x28, #1048
	movz x4, #128, lsl #0
	bl {vg_keccak_squeeze_scratch}
	add x0, x28, #1048
	movz x1, #24728, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_cbd2}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #24728, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #11, lsl #0
	movz x2, #28824, lsl #0
	add x2, x28, x2
	movz x3, #352, lsl #0
	bl {vg_mlkem1024_compress_encode}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #5272, lsl #0
	add x1, x28, x1
	movz x2, #20632, lsl #0
	add x2, x28, x2
	add x3, x28, #3224
	bl {vg_mlkem_multiply_ntts}
	movz x0, #26776, lsl #0
	add x0, x28, x0
	movz x1, #9368, lsl #0
	add x1, x28, x1
	movz x2, #21656, lsl #0
	add x2, x28, x2
	add x3, x28, #3224
	bl {vg_mlkem_multiply_ntts}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #26776, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	movz x0, #26776, lsl #0
	add x0, x28, x0
	movz x1, #13464, lsl #0
	add x1, x28, x1
	movz x2, #22680, lsl #0
	add x2, x28, x2
	add x3, x28, #3224
	bl {vg_mlkem_multiply_ntts}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #26776, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	movz x0, #26776, lsl #0
	add x0, x28, x0
	movz x1, #17560, lsl #0
	add x1, x28, x1
	movz x2, #23704, lsl #0
	add x2, x28, x2
	add x3, x28, #3224
	bl {vg_mlkem_multiply_ntts}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #26776, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem_inv_ntt}
	movz x9, #5, lsl #0
	strb w9, [x28, #976]
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
	add x3, x28, #944
	movz x4, #33, lsl #0
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
	add x3, x28, #1048
	movz x4, #128, lsl #0
	bl {vg_keccak_squeeze_scratch}
	add x0, x28, #1048
	movz x1, #24728, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_cbd2}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #24728, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #11, lsl #0
	movz x2, #29176, lsl #0
	add x2, x28, x2
	movz x3, #352, lsl #0
	bl {vg_mlkem1024_compress_encode}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #6296, lsl #0
	add x1, x28, x1
	movz x2, #20632, lsl #0
	add x2, x28, x2
	add x3, x28, #3224
	bl {vg_mlkem_multiply_ntts}
	movz x0, #26776, lsl #0
	add x0, x28, x0
	movz x1, #10392, lsl #0
	add x1, x28, x1
	movz x2, #21656, lsl #0
	add x2, x28, x2
	add x3, x28, #3224
	bl {vg_mlkem_multiply_ntts}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #26776, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	movz x0, #26776, lsl #0
	add x0, x28, x0
	movz x1, #14488, lsl #0
	add x1, x28, x1
	movz x2, #22680, lsl #0
	add x2, x28, x2
	add x3, x28, #3224
	bl {vg_mlkem_multiply_ntts}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #26776, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	movz x0, #26776, lsl #0
	add x0, x28, x0
	movz x1, #18584, lsl #0
	add x1, x28, x1
	movz x2, #23704, lsl #0
	add x2, x28, x2
	add x3, x28, #3224
	bl {vg_mlkem_multiply_ntts}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #26776, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem_inv_ntt}
	movz x9, #6, lsl #0
	strb w9, [x28, #976]
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
	add x3, x28, #944
	movz x4, #33, lsl #0
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
	add x3, x28, #1048
	movz x4, #128, lsl #0
	bl {vg_keccak_squeeze_scratch}
	add x0, x28, #1048
	movz x1, #24728, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_cbd2}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #24728, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #11, lsl #0
	movz x2, #29528, lsl #0
	add x2, x28, x2
	movz x3, #352, lsl #0
	bl {vg_mlkem1024_compress_encode}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #7320, lsl #0
	add x1, x28, x1
	movz x2, #20632, lsl #0
	add x2, x28, x2
	add x3, x28, #3224
	bl {vg_mlkem_multiply_ntts}
	movz x0, #26776, lsl #0
	add x0, x28, x0
	movz x1, #11416, lsl #0
	add x1, x28, x1
	movz x2, #21656, lsl #0
	add x2, x28, x2
	add x3, x28, #3224
	bl {vg_mlkem_multiply_ntts}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #26776, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	movz x0, #26776, lsl #0
	add x0, x28, x0
	movz x1, #15512, lsl #0
	add x1, x28, x1
	movz x2, #22680, lsl #0
	add x2, x28, x2
	add x3, x28, #3224
	bl {vg_mlkem_multiply_ntts}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #26776, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	movz x0, #26776, lsl #0
	add x0, x28, x0
	movz x1, #19608, lsl #0
	add x1, x28, x1
	movz x2, #23704, lsl #0
	add x2, x28, x2
	add x3, x28, #3224
	bl {vg_mlkem_multiply_ntts}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #26776, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem_inv_ntt}
	movz x9, #7, lsl #0
	strb w9, [x28, #976]
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
	add x3, x28, #944
	movz x4, #33, lsl #0
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
	add x3, x28, #1048
	movz x4, #128, lsl #0
	bl {vg_keccak_squeeze_scratch}
	add x0, x28, #1048
	movz x1, #24728, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_cbd2}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #24728, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #11, lsl #0
	movz x2, #29880, lsl #0
	add x2, x28, x2
	movz x3, #352, lsl #0
	bl {vg_mlkem1024_compress_encode}
	add x0, x25, #1536
	movz x1, #27800, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_decode12}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #27800, lsl #0
	add x1, x28, x1
	movz x2, #20632, lsl #0
	add x2, x28, x2
	add x3, x28, #3224
	bl {vg_mlkem_multiply_ntts}
	add x0, x25, #1920
	movz x1, #27800, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_decode12}
	movz x0, #26776, lsl #0
	add x0, x28, x0
	movz x1, #27800, lsl #0
	add x1, x28, x1
	movz x2, #21656, lsl #0
	add x2, x28, x2
	add x3, x28, #3224
	bl {vg_mlkem_multiply_ntts}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #26776, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	add x0, x25, #2304
	movz x1, #27800, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_decode12}
	movz x0, #26776, lsl #0
	add x0, x28, x0
	movz x1, #27800, lsl #0
	add x1, x28, x1
	movz x2, #22680, lsl #0
	add x2, x28, x2
	add x3, x28, #3224
	bl {vg_mlkem_multiply_ntts}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #26776, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	add x0, x25, #2688
	movz x1, #27800, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_decode12}
	movz x0, #26776, lsl #0
	add x0, x28, x0
	movz x1, #27800, lsl #0
	add x1, x28, x1
	movz x2, #23704, lsl #0
	add x2, x28, x2
	add x3, x28, #3224
	bl {vg_mlkem_multiply_ntts}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #26776, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem_inv_ntt}
	movz x9, #8, lsl #0
	strb w9, [x28, #976]
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
	add x3, x28, #944
	movz x4, #33, lsl #0
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
	add x3, x28, #1048
	movz x4, #128, lsl #0
	bl {vg_keccak_squeeze_scratch}
	add x0, x28, #1048
	movz x1, #24728, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_cbd2}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #24728, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	add x0, x28, #912
	movz x1, #32, lsl #0
	movz x2, #1, lsl #0
	movz x3, #24728, lsl #0
	add x3, x28, x3
	bl {vg_mlkem_decode_decompress}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #24728, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	movz x0, #25752, lsl #0
	add x0, x28, x0
	movz x1, #5, lsl #0
	movz x2, #30232, lsl #0
	add x2, x28, x2
	movz x3, #160, lsl #0
	bl {vg_mlkem1024_compress_encode}
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
	add x3, x25, #3136
	movz x4, #32, lsl #0
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x5, x28, #200
	add x3, x26, #0
	movz x4, #1568, lsl #0
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
	add x3, x28, #1016
	movz x4, #32, lsl #0
	bl {vg_keccak_squeeze_scratch}
	add x0, x26, #0
	movz x1, #28824, lsl #0
	add x1, x28, x1
	movz x2, #196, lsl #0
	movz x10, #0, lsl #0
20:
	ldr x9, [x0, #0]
	ldr x11, [x1, #0]
	eor x9, x9, x11
	orr x10, x10, x9
	add x0, x0, #8
	add x1, x1, #8
	sub x2, x2, #1
	cbnz x2, 20b
	movz x11, #0, lsl #0
	sub x11, x11, x10
	orr x10, x10, x11
	lsr x10, x10, #63
	sub x10, x10, #1
	ldr x12, [x28, #984]
	ldr x13, [x28, #1016]
	eor x12, x12, x13
	and x12, x12, x10
	eor x12, x12, x13
	str x12, [x27, #0]
	ldr x12, [x28, #992]
	ldr x13, [x28, #1024]
	eor x12, x12, x13
	and x12, x12, x10
	eor x12, x12, x13
	str x12, [x27, #8]
	ldr x12, [x28, #1000]
	ldr x13, [x28, #1032]
	eor x12, x12, x13
	and x12, x12, x10
	eor x12, x12, x13
	str x12, [x27, #16]
	ldr x12, [x28, #1008]
	ldr x13, [x28, #1040]
	eor x12, x12, x13
	and x12, x12, x10
	eor x12, x12, x13
	str x12, [x27, #24]
	add x0, x24, #0
	ldr x24, [x28, #30392]
	ldr x30, [x28, #30400]
	ldr x25, [x28, #30408]
	ldr x26, [x28, #30416]
	ldr x27, [x28, #30424]
	ldr x28, [x28, #30432]
	ret
	.p2align 6
