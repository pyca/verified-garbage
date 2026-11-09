// The functions of `src/internal/vg_mlkem1024_keygen_body.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem1024_keygen_body:
	str x24, [x3, #27680]
	str x25, [x3, #27688]
	str x26, [x3, #27696]
	str x27, [x3, #27704]
	str x28, [x3, #27712]
	str x30, [x3, #27720]
	add x25, x0, #0
	add x26, x1, #0
	add x27, x2, #0
	add x28, x3, #0
	movz x24, #1, lsl #0
	movz x9, #4, lsl #0
	strb w9, [x28, #920]
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
	add x3, x25, #0
	movz x4, #32, lsl #0
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	add x0, x28, #0
	movz x1, #72, lsl #0
	add x5, x28, #200
	add x3, x28, #920
	movz x4, #1, lsl #0
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
	add x3, x28, #840
	movz x4, #32, lsl #0
	bl {vg_keccak_squeeze_scratch}
	add x2, x0, #0
	add x0, x28, #0
	movz x1, #72, lsl #0
	add x5, x28, #200
	add x3, x28, #880
	movz x4, #32, lsl #0
	bl {vg_keccak_squeeze_scratch}
	movz x9, #0, lsl #0
	strb w9, [x28, #872]
	movz x9, #0, lsl #0
	strb w9, [x28, #873]
	add x0, x28, #840
	movz x1, #4128, lsl #0
	add x1, x28, x1
	add x2, x28, #1056
	bl {vg_mlkem_sample_ntt}
	and x24, x24, x0
	movz x9, #1, lsl #0
	strb w9, [x28, #872]
	movz x9, #0, lsl #0
	strb w9, [x28, #873]
	add x0, x28, #840
	movz x1, #5152, lsl #0
	add x1, x28, x1
	add x2, x28, #1056
	bl {vg_mlkem_sample_ntt}
	and x24, x24, x0
	movz x9, #2, lsl #0
	strb w9, [x28, #872]
	movz x9, #0, lsl #0
	strb w9, [x28, #873]
	add x0, x28, #840
	movz x1, #6176, lsl #0
	add x1, x28, x1
	add x2, x28, #1056
	bl {vg_mlkem_sample_ntt}
	and x24, x24, x0
	movz x9, #3, lsl #0
	strb w9, [x28, #872]
	movz x9, #0, lsl #0
	strb w9, [x28, #873]
	add x0, x28, #840
	movz x1, #7200, lsl #0
	add x1, x28, x1
	add x2, x28, #1056
	bl {vg_mlkem_sample_ntt}
	and x24, x24, x0
	movz x9, #0, lsl #0
	strb w9, [x28, #872]
	movz x9, #1, lsl #0
	strb w9, [x28, #873]
	add x0, x28, #840
	movz x1, #8224, lsl #0
	add x1, x28, x1
	add x2, x28, #1056
	bl {vg_mlkem_sample_ntt}
	and x24, x24, x0
	movz x9, #1, lsl #0
	strb w9, [x28, #872]
	movz x9, #1, lsl #0
	strb w9, [x28, #873]
	add x0, x28, #840
	movz x1, #9248, lsl #0
	add x1, x28, x1
	add x2, x28, #1056
	bl {vg_mlkem_sample_ntt}
	and x24, x24, x0
	movz x9, #2, lsl #0
	strb w9, [x28, #872]
	movz x9, #1, lsl #0
	strb w9, [x28, #873]
	add x0, x28, #840
	movz x1, #10272, lsl #0
	add x1, x28, x1
	add x2, x28, #1056
	bl {vg_mlkem_sample_ntt}
	and x24, x24, x0
	movz x9, #3, lsl #0
	strb w9, [x28, #872]
	movz x9, #1, lsl #0
	strb w9, [x28, #873]
	add x0, x28, #840
	movz x1, #11296, lsl #0
	add x1, x28, x1
	add x2, x28, #1056
	bl {vg_mlkem_sample_ntt}
	and x24, x24, x0
	movz x9, #0, lsl #0
	strb w9, [x28, #872]
	movz x9, #2, lsl #0
	strb w9, [x28, #873]
	add x0, x28, #840
	movz x1, #12320, lsl #0
	add x1, x28, x1
	add x2, x28, #1056
	bl {vg_mlkem_sample_ntt}
	and x24, x24, x0
	movz x9, #1, lsl #0
	strb w9, [x28, #872]
	movz x9, #2, lsl #0
	strb w9, [x28, #873]
	add x0, x28, #840
	movz x1, #13344, lsl #0
	add x1, x28, x1
	add x2, x28, #1056
	bl {vg_mlkem_sample_ntt}
	and x24, x24, x0
	movz x9, #2, lsl #0
	strb w9, [x28, #872]
	movz x9, #2, lsl #0
	strb w9, [x28, #873]
	add x0, x28, #840
	movz x1, #14368, lsl #0
	add x1, x28, x1
	add x2, x28, #1056
	bl {vg_mlkem_sample_ntt}
	and x24, x24, x0
	movz x9, #3, lsl #0
	strb w9, [x28, #872]
	movz x9, #2, lsl #0
	strb w9, [x28, #873]
	add x0, x28, #840
	movz x1, #15392, lsl #0
	add x1, x28, x1
	add x2, x28, #1056
	bl {vg_mlkem_sample_ntt}
	and x24, x24, x0
	movz x9, #0, lsl #0
	strb w9, [x28, #872]
	movz x9, #3, lsl #0
	strb w9, [x28, #873]
	add x0, x28, #840
	movz x1, #16416, lsl #0
	add x1, x28, x1
	add x2, x28, #1056
	bl {vg_mlkem_sample_ntt}
	and x24, x24, x0
	movz x9, #1, lsl #0
	strb w9, [x28, #872]
	movz x9, #3, lsl #0
	strb w9, [x28, #873]
	add x0, x28, #840
	movz x1, #17440, lsl #0
	add x1, x28, x1
	add x2, x28, #1056
	bl {vg_mlkem_sample_ntt}
	and x24, x24, x0
	movz x9, #2, lsl #0
	strb w9, [x28, #872]
	movz x9, #3, lsl #0
	strb w9, [x28, #873]
	add x0, x28, #840
	movz x1, #18464, lsl #0
	add x1, x28, x1
	add x2, x28, #1056
	bl {vg_mlkem_sample_ntt}
	and x24, x24, x0
	movz x9, #3, lsl #0
	strb w9, [x28, #872]
	movz x9, #3, lsl #0
	strb w9, [x28, #873]
	add x0, x28, #840
	movz x1, #19488, lsl #0
	add x1, x28, x1
	add x2, x28, #1056
	bl {vg_mlkem_sample_ntt}
	and x24, x24, x0
	movz x9, #0, lsl #0
	strb w9, [x28, #912]
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
	add x3, x28, #880
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
	add x3, x28, #928
	movz x4, #128, lsl #0
	bl {vg_keccak_squeeze_scratch}
	add x0, x28, #928
	movz x1, #20512, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_cbd2}
	movz x0, #20512, lsl #0
	add x0, x28, x0
	add x1, x28, #3104
	bl {vg_mlkem_ntt}
	movz x0, #20512, lsl #0
	add x0, x28, x0
	add x1, x27, #0
	bl {vg_mlkem_encode12}
	movz x9, #1, lsl #0
	strb w9, [x28, #912]
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
	add x3, x28, #880
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
	add x3, x28, #928
	movz x4, #128, lsl #0
	bl {vg_keccak_squeeze_scratch}
	add x0, x28, #928
	movz x1, #21536, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_cbd2}
	movz x0, #21536, lsl #0
	add x0, x28, x0
	add x1, x28, #3104
	bl {vg_mlkem_ntt}
	movz x0, #21536, lsl #0
	add x0, x28, x0
	add x1, x27, #384
	bl {vg_mlkem_encode12}
	movz x9, #2, lsl #0
	strb w9, [x28, #912]
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
	add x3, x28, #880
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
	add x3, x28, #928
	movz x4, #128, lsl #0
	bl {vg_keccak_squeeze_scratch}
	add x0, x28, #928
	movz x1, #22560, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_cbd2}
	movz x0, #22560, lsl #0
	add x0, x28, x0
	add x1, x28, #3104
	bl {vg_mlkem_ntt}
	movz x0, #22560, lsl #0
	add x0, x28, x0
	add x1, x27, #768
	bl {vg_mlkem_encode12}
	movz x9, #3, lsl #0
	strb w9, [x28, #912]
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
	add x3, x28, #880
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
	add x3, x28, #928
	movz x4, #128, lsl #0
	bl {vg_keccak_squeeze_scratch}
	add x0, x28, #928
	movz x1, #23584, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_cbd2}
	movz x0, #23584, lsl #0
	add x0, x28, x0
	add x1, x28, #3104
	bl {vg_mlkem_ntt}
	movz x0, #23584, lsl #0
	add x0, x28, x0
	add x1, x27, #1152
	bl {vg_mlkem_encode12}
	movz x9, #4, lsl #0
	strb w9, [x28, #912]
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
	add x3, x28, #880
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
	add x3, x28, #928
	movz x4, #128, lsl #0
	bl {vg_keccak_squeeze_scratch}
	add x0, x28, #928
	movz x1, #24608, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_cbd2}
	movz x0, #24608, lsl #0
	add x0, x28, x0
	add x1, x28, #3104
	bl {vg_mlkem_ntt}
	movz x0, #25632, lsl #0
	add x0, x28, x0
	movz x1, #4128, lsl #0
	add x1, x28, x1
	movz x2, #20512, lsl #0
	add x2, x28, x2
	add x3, x28, #3104
	bl {vg_mlkem_multiply_ntts}
	movz x0, #26656, lsl #0
	add x0, x28, x0
	movz x1, #5152, lsl #0
	add x1, x28, x1
	movz x2, #21536, lsl #0
	add x2, x28, x2
	add x3, x28, #3104
	bl {vg_mlkem_multiply_ntts}
	movz x0, #25632, lsl #0
	add x0, x28, x0
	movz x1, #26656, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	movz x0, #26656, lsl #0
	add x0, x28, x0
	movz x1, #6176, lsl #0
	add x1, x28, x1
	movz x2, #22560, lsl #0
	add x2, x28, x2
	add x3, x28, #3104
	bl {vg_mlkem_multiply_ntts}
	movz x0, #25632, lsl #0
	add x0, x28, x0
	movz x1, #26656, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	movz x0, #26656, lsl #0
	add x0, x28, x0
	movz x1, #7200, lsl #0
	add x1, x28, x1
	movz x2, #23584, lsl #0
	add x2, x28, x2
	add x3, x28, #3104
	bl {vg_mlkem_multiply_ntts}
	movz x0, #25632, lsl #0
	add x0, x28, x0
	movz x1, #26656, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	movz x0, #25632, lsl #0
	add x0, x28, x0
	movz x1, #24608, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	movz x0, #25632, lsl #0
	add x0, x28, x0
	add x1, x26, #0
	bl {vg_mlkem_encode12}
	movz x0, #25632, lsl #0
	add x0, x28, x0
	add x1, x27, #1536
	bl {vg_mlkem_encode12}
	movz x9, #5, lsl #0
	strb w9, [x28, #912]
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
	add x3, x28, #880
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
	add x3, x28, #928
	movz x4, #128, lsl #0
	bl {vg_keccak_squeeze_scratch}
	add x0, x28, #928
	movz x1, #24608, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_cbd2}
	movz x0, #24608, lsl #0
	add x0, x28, x0
	add x1, x28, #3104
	bl {vg_mlkem_ntt}
	movz x0, #25632, lsl #0
	add x0, x28, x0
	movz x1, #8224, lsl #0
	add x1, x28, x1
	movz x2, #20512, lsl #0
	add x2, x28, x2
	add x3, x28, #3104
	bl {vg_mlkem_multiply_ntts}
	movz x0, #26656, lsl #0
	add x0, x28, x0
	movz x1, #9248, lsl #0
	add x1, x28, x1
	movz x2, #21536, lsl #0
	add x2, x28, x2
	add x3, x28, #3104
	bl {vg_mlkem_multiply_ntts}
	movz x0, #25632, lsl #0
	add x0, x28, x0
	movz x1, #26656, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	movz x0, #26656, lsl #0
	add x0, x28, x0
	movz x1, #10272, lsl #0
	add x1, x28, x1
	movz x2, #22560, lsl #0
	add x2, x28, x2
	add x3, x28, #3104
	bl {vg_mlkem_multiply_ntts}
	movz x0, #25632, lsl #0
	add x0, x28, x0
	movz x1, #26656, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	movz x0, #26656, lsl #0
	add x0, x28, x0
	movz x1, #11296, lsl #0
	add x1, x28, x1
	movz x2, #23584, lsl #0
	add x2, x28, x2
	add x3, x28, #3104
	bl {vg_mlkem_multiply_ntts}
	movz x0, #25632, lsl #0
	add x0, x28, x0
	movz x1, #26656, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	movz x0, #25632, lsl #0
	add x0, x28, x0
	movz x1, #24608, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	movz x0, #25632, lsl #0
	add x0, x28, x0
	add x1, x26, #384
	bl {vg_mlkem_encode12}
	movz x0, #25632, lsl #0
	add x0, x28, x0
	add x1, x27, #1920
	bl {vg_mlkem_encode12}
	movz x9, #6, lsl #0
	strb w9, [x28, #912]
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
	add x3, x28, #880
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
	add x3, x28, #928
	movz x4, #128, lsl #0
	bl {vg_keccak_squeeze_scratch}
	add x0, x28, #928
	movz x1, #24608, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_cbd2}
	movz x0, #24608, lsl #0
	add x0, x28, x0
	add x1, x28, #3104
	bl {vg_mlkem_ntt}
	movz x0, #25632, lsl #0
	add x0, x28, x0
	movz x1, #12320, lsl #0
	add x1, x28, x1
	movz x2, #20512, lsl #0
	add x2, x28, x2
	add x3, x28, #3104
	bl {vg_mlkem_multiply_ntts}
	movz x0, #26656, lsl #0
	add x0, x28, x0
	movz x1, #13344, lsl #0
	add x1, x28, x1
	movz x2, #21536, lsl #0
	add x2, x28, x2
	add x3, x28, #3104
	bl {vg_mlkem_multiply_ntts}
	movz x0, #25632, lsl #0
	add x0, x28, x0
	movz x1, #26656, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	movz x0, #26656, lsl #0
	add x0, x28, x0
	movz x1, #14368, lsl #0
	add x1, x28, x1
	movz x2, #22560, lsl #0
	add x2, x28, x2
	add x3, x28, #3104
	bl {vg_mlkem_multiply_ntts}
	movz x0, #25632, lsl #0
	add x0, x28, x0
	movz x1, #26656, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	movz x0, #26656, lsl #0
	add x0, x28, x0
	movz x1, #15392, lsl #0
	add x1, x28, x1
	movz x2, #23584, lsl #0
	add x2, x28, x2
	add x3, x28, #3104
	bl {vg_mlkem_multiply_ntts}
	movz x0, #25632, lsl #0
	add x0, x28, x0
	movz x1, #26656, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	movz x0, #25632, lsl #0
	add x0, x28, x0
	movz x1, #24608, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	movz x0, #25632, lsl #0
	add x0, x28, x0
	add x1, x26, #768
	bl {vg_mlkem_encode12}
	movz x0, #25632, lsl #0
	add x0, x28, x0
	add x1, x27, #2304
	bl {vg_mlkem_encode12}
	movz x9, #7, lsl #0
	strb w9, [x28, #912]
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
	add x3, x28, #880
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
	add x3, x28, #928
	movz x4, #128, lsl #0
	bl {vg_keccak_squeeze_scratch}
	add x0, x28, #928
	movz x1, #24608, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_cbd2}
	movz x0, #24608, lsl #0
	add x0, x28, x0
	add x1, x28, #3104
	bl {vg_mlkem_ntt}
	movz x0, #25632, lsl #0
	add x0, x28, x0
	movz x1, #16416, lsl #0
	add x1, x28, x1
	movz x2, #20512, lsl #0
	add x2, x28, x2
	add x3, x28, #3104
	bl {vg_mlkem_multiply_ntts}
	movz x0, #26656, lsl #0
	add x0, x28, x0
	movz x1, #17440, lsl #0
	add x1, x28, x1
	movz x2, #21536, lsl #0
	add x2, x28, x2
	add x3, x28, #3104
	bl {vg_mlkem_multiply_ntts}
	movz x0, #25632, lsl #0
	add x0, x28, x0
	movz x1, #26656, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	movz x0, #26656, lsl #0
	add x0, x28, x0
	movz x1, #18464, lsl #0
	add x1, x28, x1
	movz x2, #22560, lsl #0
	add x2, x28, x2
	add x3, x28, #3104
	bl {vg_mlkem_multiply_ntts}
	movz x0, #25632, lsl #0
	add x0, x28, x0
	movz x1, #26656, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	movz x0, #26656, lsl #0
	add x0, x28, x0
	movz x1, #19488, lsl #0
	add x1, x28, x1
	movz x2, #23584, lsl #0
	add x2, x28, x2
	add x3, x28, #3104
	bl {vg_mlkem_multiply_ntts}
	movz x0, #25632, lsl #0
	add x0, x28, x0
	movz x1, #26656, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	movz x0, #25632, lsl #0
	add x0, x28, x0
	movz x1, #24608, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	movz x0, #25632, lsl #0
	add x0, x28, x0
	add x1, x26, #1152
	bl {vg_mlkem_encode12}
	movz x0, #25632, lsl #0
	add x0, x28, x0
	add x1, x27, #2688
	bl {vg_mlkem_encode12}
	ldr x9, [x28, #840]
	str x9, [x26, #1536]
	ldr x9, [x28, #848]
	str x9, [x26, #1544]
	ldr x9, [x28, #856]
	str x9, [x26, #1552]
	ldr x9, [x28, #864]
	str x9, [x26, #1560]
	ldr x9, [x28, #840]
	str x9, [x27, #3072]
	ldr x9, [x28, #848]
	str x9, [x27, #3080]
	ldr x9, [x28, #856]
	str x9, [x27, #3088]
	ldr x9, [x28, #864]
	str x9, [x27, #3096]
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
	movz x4, #1568, lsl #0
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x4, x28, #200
	movz x3, #6, lsl #0
	bl {vg_keccak_pad_scratch}
	movz x2, #0, lsl #0
	add x0, x28, #0
	movz x1, #136, lsl #0
	add x5, x28, #200
	add x3, x27, #3104
	movz x4, #32, lsl #0
	bl {vg_keccak_squeeze_scratch}
	ldr x9, [x25, #32]
	str x9, [x27, #3136]
	ldr x9, [x25, #40]
	str x9, [x27, #3144]
	ldr x9, [x25, #48]
	str x9, [x27, #3152]
	ldr x9, [x25, #56]
	str x9, [x27, #3160]
	add x0, x24, #0
	ldr x30, [x28, #27720]
	ldr x24, [x28, #27680]
	ldr x25, [x28, #27688]
	ldr x26, [x28, #27696]
	ldr x27, [x28, #27704]
	ldr x28, [x28, #27712]
	ret
	.p2align 6
