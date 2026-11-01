// The functions of `src/internal/vg_salsa20_8.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_salsa20_8:
	ldr r2, [r0, #0]
	str r2, [r1, #0]
	ldr r2, [r0, #4]
	str r2, [r1, #4]
	ldr r2, [r0, #8]
	str r2, [r1, #8]
	ldr r2, [r0, #12]
	str r2, [r1, #12]
	ldr r2, [r0, #16]
	str r2, [r1, #16]
	ldr r2, [r0, #20]
	str r2, [r1, #20]
	ldr r2, [r0, #24]
	str r2, [r1, #24]
	ldr r2, [r0, #28]
	str r2, [r1, #28]
	ldr r2, [r0, #32]
	str r2, [r1, #32]
	ldr r2, [r0, #36]
	str r2, [r1, #36]
	ldr r2, [r0, #40]
	str r2, [r1, #40]
	ldr r2, [r0, #44]
	str r2, [r1, #44]
	ldr r2, [r0, #48]
	str r2, [r1, #48]
	ldr r2, [r0, #52]
	str r2, [r1, #52]
	ldr r2, [r0, #56]
	str r2, [r1, #56]
	ldr r2, [r0, #60]
	str r2, [r1, #60]
	ldr r2, [r1, #0]
	ldr r3, [r1, #48]
	add r2, r2, r3
	ldr r3, [r1, #16]
	eor r3, r3, r2, ror #25
	str r3, [r1, #16]
	ldr r2, [r1, #16]
	ldr r3, [r1, #0]
	add r2, r2, r3
	ldr r3, [r1, #32]
	eor r3, r3, r2, ror #23
	str r3, [r1, #32]
	ldr r2, [r1, #32]
	ldr r3, [r1, #16]
	add r2, r2, r3
	ldr r3, [r1, #48]
	eor r3, r3, r2, ror #19
	str r3, [r1, #48]
	ldr r2, [r1, #48]
	ldr r3, [r1, #32]
	add r2, r2, r3
	ldr r3, [r1, #0]
	eor r3, r3, r2, ror #14
	str r3, [r1, #0]
	ldr r2, [r1, #20]
	ldr r3, [r1, #4]
	add r2, r2, r3
	ldr r3, [r1, #36]
	eor r3, r3, r2, ror #25
	str r3, [r1, #36]
	ldr r2, [r1, #36]
	ldr r3, [r1, #20]
	add r2, r2, r3
	ldr r3, [r1, #52]
	eor r3, r3, r2, ror #23
	str r3, [r1, #52]
	ldr r2, [r1, #52]
	ldr r3, [r1, #36]
	add r2, r2, r3
	ldr r3, [r1, #4]
	eor r3, r3, r2, ror #19
	str r3, [r1, #4]
	ldr r2, [r1, #4]
	ldr r3, [r1, #52]
	add r2, r2, r3
	ldr r3, [r1, #20]
	eor r3, r3, r2, ror #14
	str r3, [r1, #20]
	ldr r2, [r1, #40]
	ldr r3, [r1, #24]
	add r2, r2, r3
	ldr r3, [r1, #56]
	eor r3, r3, r2, ror #25
	str r3, [r1, #56]
	ldr r2, [r1, #56]
	ldr r3, [r1, #40]
	add r2, r2, r3
	ldr r3, [r1, #8]
	eor r3, r3, r2, ror #23
	str r3, [r1, #8]
	ldr r2, [r1, #8]
	ldr r3, [r1, #56]
	add r2, r2, r3
	ldr r3, [r1, #24]
	eor r3, r3, r2, ror #19
	str r3, [r1, #24]
	ldr r2, [r1, #24]
	ldr r3, [r1, #8]
	add r2, r2, r3
	ldr r3, [r1, #40]
	eor r3, r3, r2, ror #14
	str r3, [r1, #40]
	ldr r2, [r1, #60]
	ldr r3, [r1, #44]
	add r2, r2, r3
	ldr r3, [r1, #12]
	eor r3, r3, r2, ror #25
	str r3, [r1, #12]
	ldr r2, [r1, #12]
	ldr r3, [r1, #60]
	add r2, r2, r3
	ldr r3, [r1, #28]
	eor r3, r3, r2, ror #23
	str r3, [r1, #28]
	ldr r2, [r1, #28]
	ldr r3, [r1, #12]
	add r2, r2, r3
	ldr r3, [r1, #44]
	eor r3, r3, r2, ror #19
	str r3, [r1, #44]
	ldr r2, [r1, #44]
	ldr r3, [r1, #28]
	add r2, r2, r3
	ldr r3, [r1, #60]
	eor r3, r3, r2, ror #14
	str r3, [r1, #60]
	ldr r2, [r1, #0]
	ldr r3, [r1, #12]
	add r2, r2, r3
	ldr r3, [r1, #4]
	eor r3, r3, r2, ror #25
	str r3, [r1, #4]
	ldr r2, [r1, #4]
	ldr r3, [r1, #0]
	add r2, r2, r3
	ldr r3, [r1, #8]
	eor r3, r3, r2, ror #23
	str r3, [r1, #8]
	ldr r2, [r1, #8]
	ldr r3, [r1, #4]
	add r2, r2, r3
	ldr r3, [r1, #12]
	eor r3, r3, r2, ror #19
	str r3, [r1, #12]
	ldr r2, [r1, #12]
	ldr r3, [r1, #8]
	add r2, r2, r3
	ldr r3, [r1, #0]
	eor r3, r3, r2, ror #14
	str r3, [r1, #0]
	ldr r2, [r1, #20]
	ldr r3, [r1, #16]
	add r2, r2, r3
	ldr r3, [r1, #24]
	eor r3, r3, r2, ror #25
	str r3, [r1, #24]
	ldr r2, [r1, #24]
	ldr r3, [r1, #20]
	add r2, r2, r3
	ldr r3, [r1, #28]
	eor r3, r3, r2, ror #23
	str r3, [r1, #28]
	ldr r2, [r1, #28]
	ldr r3, [r1, #24]
	add r2, r2, r3
	ldr r3, [r1, #16]
	eor r3, r3, r2, ror #19
	str r3, [r1, #16]
	ldr r2, [r1, #16]
	ldr r3, [r1, #28]
	add r2, r2, r3
	ldr r3, [r1, #20]
	eor r3, r3, r2, ror #14
	str r3, [r1, #20]
	ldr r2, [r1, #40]
	ldr r3, [r1, #36]
	add r2, r2, r3
	ldr r3, [r1, #44]
	eor r3, r3, r2, ror #25
	str r3, [r1, #44]
	ldr r2, [r1, #44]
	ldr r3, [r1, #40]
	add r2, r2, r3
	ldr r3, [r1, #32]
	eor r3, r3, r2, ror #23
	str r3, [r1, #32]
	ldr r2, [r1, #32]
	ldr r3, [r1, #44]
	add r2, r2, r3
	ldr r3, [r1, #36]
	eor r3, r3, r2, ror #19
	str r3, [r1, #36]
	ldr r2, [r1, #36]
	ldr r3, [r1, #32]
	add r2, r2, r3
	ldr r3, [r1, #40]
	eor r3, r3, r2, ror #14
	str r3, [r1, #40]
	ldr r2, [r1, #60]
	ldr r3, [r1, #56]
	add r2, r2, r3
	ldr r3, [r1, #48]
	eor r3, r3, r2, ror #25
	str r3, [r1, #48]
	ldr r2, [r1, #48]
	ldr r3, [r1, #60]
	add r2, r2, r3
	ldr r3, [r1, #52]
	eor r3, r3, r2, ror #23
	str r3, [r1, #52]
	ldr r2, [r1, #52]
	ldr r3, [r1, #48]
	add r2, r2, r3
	ldr r3, [r1, #56]
	eor r3, r3, r2, ror #19
	str r3, [r1, #56]
	ldr r2, [r1, #56]
	ldr r3, [r1, #52]
	add r2, r2, r3
	ldr r3, [r1, #60]
	eor r3, r3, r2, ror #14
	str r3, [r1, #60]
	ldr r2, [r1, #0]
	ldr r3, [r1, #48]
	add r2, r2, r3
	ldr r3, [r1, #16]
	eor r3, r3, r2, ror #25
	str r3, [r1, #16]
	ldr r2, [r1, #16]
	ldr r3, [r1, #0]
	add r2, r2, r3
	ldr r3, [r1, #32]
	eor r3, r3, r2, ror #23
	str r3, [r1, #32]
	ldr r2, [r1, #32]
	ldr r3, [r1, #16]
	add r2, r2, r3
	ldr r3, [r1, #48]
	eor r3, r3, r2, ror #19
	str r3, [r1, #48]
	ldr r2, [r1, #48]
	ldr r3, [r1, #32]
	add r2, r2, r3
	ldr r3, [r1, #0]
	eor r3, r3, r2, ror #14
	str r3, [r1, #0]
	ldr r2, [r1, #20]
	ldr r3, [r1, #4]
	add r2, r2, r3
	ldr r3, [r1, #36]
	eor r3, r3, r2, ror #25
	str r3, [r1, #36]
	ldr r2, [r1, #36]
	ldr r3, [r1, #20]
	add r2, r2, r3
	ldr r3, [r1, #52]
	eor r3, r3, r2, ror #23
	str r3, [r1, #52]
	ldr r2, [r1, #52]
	ldr r3, [r1, #36]
	add r2, r2, r3
	ldr r3, [r1, #4]
	eor r3, r3, r2, ror #19
	str r3, [r1, #4]
	ldr r2, [r1, #4]
	ldr r3, [r1, #52]
	add r2, r2, r3
	ldr r3, [r1, #20]
	eor r3, r3, r2, ror #14
	str r3, [r1, #20]
	ldr r2, [r1, #40]
	ldr r3, [r1, #24]
	add r2, r2, r3
	ldr r3, [r1, #56]
	eor r3, r3, r2, ror #25
	str r3, [r1, #56]
	ldr r2, [r1, #56]
	ldr r3, [r1, #40]
	add r2, r2, r3
	ldr r3, [r1, #8]
	eor r3, r3, r2, ror #23
	str r3, [r1, #8]
	ldr r2, [r1, #8]
	ldr r3, [r1, #56]
	add r2, r2, r3
	ldr r3, [r1, #24]
	eor r3, r3, r2, ror #19
	str r3, [r1, #24]
	ldr r2, [r1, #24]
	ldr r3, [r1, #8]
	add r2, r2, r3
	ldr r3, [r1, #40]
	eor r3, r3, r2, ror #14
	str r3, [r1, #40]
	ldr r2, [r1, #60]
	ldr r3, [r1, #44]
	add r2, r2, r3
	ldr r3, [r1, #12]
	eor r3, r3, r2, ror #25
	str r3, [r1, #12]
	ldr r2, [r1, #12]
	ldr r3, [r1, #60]
	add r2, r2, r3
	ldr r3, [r1, #28]
	eor r3, r3, r2, ror #23
	str r3, [r1, #28]
	ldr r2, [r1, #28]
	ldr r3, [r1, #12]
	add r2, r2, r3
	ldr r3, [r1, #44]
	eor r3, r3, r2, ror #19
	str r3, [r1, #44]
	ldr r2, [r1, #44]
	ldr r3, [r1, #28]
	add r2, r2, r3
	ldr r3, [r1, #60]
	eor r3, r3, r2, ror #14
	str r3, [r1, #60]
	ldr r2, [r1, #0]
	ldr r3, [r1, #12]
	add r2, r2, r3
	ldr r3, [r1, #4]
	eor r3, r3, r2, ror #25
	str r3, [r1, #4]
	ldr r2, [r1, #4]
	ldr r3, [r1, #0]
	add r2, r2, r3
	ldr r3, [r1, #8]
	eor r3, r3, r2, ror #23
	str r3, [r1, #8]
	ldr r2, [r1, #8]
	ldr r3, [r1, #4]
	add r2, r2, r3
	ldr r3, [r1, #12]
	eor r3, r3, r2, ror #19
	str r3, [r1, #12]
	ldr r2, [r1, #12]
	ldr r3, [r1, #8]
	add r2, r2, r3
	ldr r3, [r1, #0]
	eor r3, r3, r2, ror #14
	str r3, [r1, #0]
	ldr r2, [r1, #20]
	ldr r3, [r1, #16]
	add r2, r2, r3
	ldr r3, [r1, #24]
	eor r3, r3, r2, ror #25
	str r3, [r1, #24]
	ldr r2, [r1, #24]
	ldr r3, [r1, #20]
	add r2, r2, r3
	ldr r3, [r1, #28]
	eor r3, r3, r2, ror #23
	str r3, [r1, #28]
	ldr r2, [r1, #28]
	ldr r3, [r1, #24]
	add r2, r2, r3
	ldr r3, [r1, #16]
	eor r3, r3, r2, ror #19
	str r3, [r1, #16]
	ldr r2, [r1, #16]
	ldr r3, [r1, #28]
	add r2, r2, r3
	ldr r3, [r1, #20]
	eor r3, r3, r2, ror #14
	str r3, [r1, #20]
	ldr r2, [r1, #40]
	ldr r3, [r1, #36]
	add r2, r2, r3
	ldr r3, [r1, #44]
	eor r3, r3, r2, ror #25
	str r3, [r1, #44]
	ldr r2, [r1, #44]
	ldr r3, [r1, #40]
	add r2, r2, r3
	ldr r3, [r1, #32]
	eor r3, r3, r2, ror #23
	str r3, [r1, #32]
	ldr r2, [r1, #32]
	ldr r3, [r1, #44]
	add r2, r2, r3
	ldr r3, [r1, #36]
	eor r3, r3, r2, ror #19
	str r3, [r1, #36]
	ldr r2, [r1, #36]
	ldr r3, [r1, #32]
	add r2, r2, r3
	ldr r3, [r1, #40]
	eor r3, r3, r2, ror #14
	str r3, [r1, #40]
	ldr r2, [r1, #60]
	ldr r3, [r1, #56]
	add r2, r2, r3
	ldr r3, [r1, #48]
	eor r3, r3, r2, ror #25
	str r3, [r1, #48]
	ldr r2, [r1, #48]
	ldr r3, [r1, #60]
	add r2, r2, r3
	ldr r3, [r1, #52]
	eor r3, r3, r2, ror #23
	str r3, [r1, #52]
	ldr r2, [r1, #52]
	ldr r3, [r1, #48]
	add r2, r2, r3
	ldr r3, [r1, #56]
	eor r3, r3, r2, ror #19
	str r3, [r1, #56]
	ldr r2, [r1, #56]
	ldr r3, [r1, #52]
	add r2, r2, r3
	ldr r3, [r1, #60]
	eor r3, r3, r2, ror #14
	str r3, [r1, #60]
	ldr r2, [r1, #0]
	ldr r3, [r1, #48]
	add r2, r2, r3
	ldr r3, [r1, #16]
	eor r3, r3, r2, ror #25
	str r3, [r1, #16]
	ldr r2, [r1, #16]
	ldr r3, [r1, #0]
	add r2, r2, r3
	ldr r3, [r1, #32]
	eor r3, r3, r2, ror #23
	str r3, [r1, #32]
	ldr r2, [r1, #32]
	ldr r3, [r1, #16]
	add r2, r2, r3
	ldr r3, [r1, #48]
	eor r3, r3, r2, ror #19
	str r3, [r1, #48]
	ldr r2, [r1, #48]
	ldr r3, [r1, #32]
	add r2, r2, r3
	ldr r3, [r1, #0]
	eor r3, r3, r2, ror #14
	str r3, [r1, #0]
	ldr r2, [r1, #20]
	ldr r3, [r1, #4]
	add r2, r2, r3
	ldr r3, [r1, #36]
	eor r3, r3, r2, ror #25
	str r3, [r1, #36]
	ldr r2, [r1, #36]
	ldr r3, [r1, #20]
	add r2, r2, r3
	ldr r3, [r1, #52]
	eor r3, r3, r2, ror #23
	str r3, [r1, #52]
	ldr r2, [r1, #52]
	ldr r3, [r1, #36]
	add r2, r2, r3
	ldr r3, [r1, #4]
	eor r3, r3, r2, ror #19
	str r3, [r1, #4]
	ldr r2, [r1, #4]
	ldr r3, [r1, #52]
	add r2, r2, r3
	ldr r3, [r1, #20]
	eor r3, r3, r2, ror #14
	str r3, [r1, #20]
	ldr r2, [r1, #40]
	ldr r3, [r1, #24]
	add r2, r2, r3
	ldr r3, [r1, #56]
	eor r3, r3, r2, ror #25
	str r3, [r1, #56]
	ldr r2, [r1, #56]
	ldr r3, [r1, #40]
	add r2, r2, r3
	ldr r3, [r1, #8]
	eor r3, r3, r2, ror #23
	str r3, [r1, #8]
	ldr r2, [r1, #8]
	ldr r3, [r1, #56]
	add r2, r2, r3
	ldr r3, [r1, #24]
	eor r3, r3, r2, ror #19
	str r3, [r1, #24]
	ldr r2, [r1, #24]
	ldr r3, [r1, #8]
	add r2, r2, r3
	ldr r3, [r1, #40]
	eor r3, r3, r2, ror #14
	str r3, [r1, #40]
	ldr r2, [r1, #60]
	ldr r3, [r1, #44]
	add r2, r2, r3
	ldr r3, [r1, #12]
	eor r3, r3, r2, ror #25
	str r3, [r1, #12]
	ldr r2, [r1, #12]
	ldr r3, [r1, #60]
	add r2, r2, r3
	ldr r3, [r1, #28]
	eor r3, r3, r2, ror #23
	str r3, [r1, #28]
	ldr r2, [r1, #28]
	ldr r3, [r1, #12]
	add r2, r2, r3
	ldr r3, [r1, #44]
	eor r3, r3, r2, ror #19
	str r3, [r1, #44]
	ldr r2, [r1, #44]
	ldr r3, [r1, #28]
	add r2, r2, r3
	ldr r3, [r1, #60]
	eor r3, r3, r2, ror #14
	str r3, [r1, #60]
	ldr r2, [r1, #0]
	ldr r3, [r1, #12]
	add r2, r2, r3
	ldr r3, [r1, #4]
	eor r3, r3, r2, ror #25
	str r3, [r1, #4]
	ldr r2, [r1, #4]
	ldr r3, [r1, #0]
	add r2, r2, r3
	ldr r3, [r1, #8]
	eor r3, r3, r2, ror #23
	str r3, [r1, #8]
	ldr r2, [r1, #8]
	ldr r3, [r1, #4]
	add r2, r2, r3
	ldr r3, [r1, #12]
	eor r3, r3, r2, ror #19
	str r3, [r1, #12]
	ldr r2, [r1, #12]
	ldr r3, [r1, #8]
	add r2, r2, r3
	ldr r3, [r1, #0]
	eor r3, r3, r2, ror #14
	str r3, [r1, #0]
	ldr r2, [r1, #20]
	ldr r3, [r1, #16]
	add r2, r2, r3
	ldr r3, [r1, #24]
	eor r3, r3, r2, ror #25
	str r3, [r1, #24]
	ldr r2, [r1, #24]
	ldr r3, [r1, #20]
	add r2, r2, r3
	ldr r3, [r1, #28]
	eor r3, r3, r2, ror #23
	str r3, [r1, #28]
	ldr r2, [r1, #28]
	ldr r3, [r1, #24]
	add r2, r2, r3
	ldr r3, [r1, #16]
	eor r3, r3, r2, ror #19
	str r3, [r1, #16]
	ldr r2, [r1, #16]
	ldr r3, [r1, #28]
	add r2, r2, r3
	ldr r3, [r1, #20]
	eor r3, r3, r2, ror #14
	str r3, [r1, #20]
	ldr r2, [r1, #40]
	ldr r3, [r1, #36]
	add r2, r2, r3
	ldr r3, [r1, #44]
	eor r3, r3, r2, ror #25
	str r3, [r1, #44]
	ldr r2, [r1, #44]
	ldr r3, [r1, #40]
	add r2, r2, r3
	ldr r3, [r1, #32]
	eor r3, r3, r2, ror #23
	str r3, [r1, #32]
	ldr r2, [r1, #32]
	ldr r3, [r1, #44]
	add r2, r2, r3
	ldr r3, [r1, #36]
	eor r3, r3, r2, ror #19
	str r3, [r1, #36]
	ldr r2, [r1, #36]
	ldr r3, [r1, #32]
	add r2, r2, r3
	ldr r3, [r1, #40]
	eor r3, r3, r2, ror #14
	str r3, [r1, #40]
	ldr r2, [r1, #60]
	ldr r3, [r1, #56]
	add r2, r2, r3
	ldr r3, [r1, #48]
	eor r3, r3, r2, ror #25
	str r3, [r1, #48]
	ldr r2, [r1, #48]
	ldr r3, [r1, #60]
	add r2, r2, r3
	ldr r3, [r1, #52]
	eor r3, r3, r2, ror #23
	str r3, [r1, #52]
	ldr r2, [r1, #52]
	ldr r3, [r1, #48]
	add r2, r2, r3
	ldr r3, [r1, #56]
	eor r3, r3, r2, ror #19
	str r3, [r1, #56]
	ldr r2, [r1, #56]
	ldr r3, [r1, #52]
	add r2, r2, r3
	ldr r3, [r1, #60]
	eor r3, r3, r2, ror #14
	str r3, [r1, #60]
	ldr r2, [r1, #0]
	ldr r3, [r1, #48]
	add r2, r2, r3
	ldr r3, [r1, #16]
	eor r3, r3, r2, ror #25
	str r3, [r1, #16]
	ldr r2, [r1, #16]
	ldr r3, [r1, #0]
	add r2, r2, r3
	ldr r3, [r1, #32]
	eor r3, r3, r2, ror #23
	str r3, [r1, #32]
	ldr r2, [r1, #32]
	ldr r3, [r1, #16]
	add r2, r2, r3
	ldr r3, [r1, #48]
	eor r3, r3, r2, ror #19
	str r3, [r1, #48]
	ldr r2, [r1, #48]
	ldr r3, [r1, #32]
	add r2, r2, r3
	ldr r3, [r1, #0]
	eor r3, r3, r2, ror #14
	str r3, [r1, #0]
	ldr r2, [r1, #20]
	ldr r3, [r1, #4]
	add r2, r2, r3
	ldr r3, [r1, #36]
	eor r3, r3, r2, ror #25
	str r3, [r1, #36]
	ldr r2, [r1, #36]
	ldr r3, [r1, #20]
	add r2, r2, r3
	ldr r3, [r1, #52]
	eor r3, r3, r2, ror #23
	str r3, [r1, #52]
	ldr r2, [r1, #52]
	ldr r3, [r1, #36]
	add r2, r2, r3
	ldr r3, [r1, #4]
	eor r3, r3, r2, ror #19
	str r3, [r1, #4]
	ldr r2, [r1, #4]
	ldr r3, [r1, #52]
	add r2, r2, r3
	ldr r3, [r1, #20]
	eor r3, r3, r2, ror #14
	str r3, [r1, #20]
	ldr r2, [r1, #40]
	ldr r3, [r1, #24]
	add r2, r2, r3
	ldr r3, [r1, #56]
	eor r3, r3, r2, ror #25
	str r3, [r1, #56]
	ldr r2, [r1, #56]
	ldr r3, [r1, #40]
	add r2, r2, r3
	ldr r3, [r1, #8]
	eor r3, r3, r2, ror #23
	str r3, [r1, #8]
	ldr r2, [r1, #8]
	ldr r3, [r1, #56]
	add r2, r2, r3
	ldr r3, [r1, #24]
	eor r3, r3, r2, ror #19
	str r3, [r1, #24]
	ldr r2, [r1, #24]
	ldr r3, [r1, #8]
	add r2, r2, r3
	ldr r3, [r1, #40]
	eor r3, r3, r2, ror #14
	str r3, [r1, #40]
	ldr r2, [r1, #60]
	ldr r3, [r1, #44]
	add r2, r2, r3
	ldr r3, [r1, #12]
	eor r3, r3, r2, ror #25
	str r3, [r1, #12]
	ldr r2, [r1, #12]
	ldr r3, [r1, #60]
	add r2, r2, r3
	ldr r3, [r1, #28]
	eor r3, r3, r2, ror #23
	str r3, [r1, #28]
	ldr r2, [r1, #28]
	ldr r3, [r1, #12]
	add r2, r2, r3
	ldr r3, [r1, #44]
	eor r3, r3, r2, ror #19
	str r3, [r1, #44]
	ldr r2, [r1, #44]
	ldr r3, [r1, #28]
	add r2, r2, r3
	ldr r3, [r1, #60]
	eor r3, r3, r2, ror #14
	str r3, [r1, #60]
	ldr r2, [r1, #0]
	ldr r3, [r1, #12]
	add r2, r2, r3
	ldr r3, [r1, #4]
	eor r3, r3, r2, ror #25
	str r3, [r1, #4]
	ldr r2, [r1, #4]
	ldr r3, [r1, #0]
	add r2, r2, r3
	ldr r3, [r1, #8]
	eor r3, r3, r2, ror #23
	str r3, [r1, #8]
	ldr r2, [r1, #8]
	ldr r3, [r1, #4]
	add r2, r2, r3
	ldr r3, [r1, #12]
	eor r3, r3, r2, ror #19
	str r3, [r1, #12]
	ldr r2, [r1, #12]
	ldr r3, [r1, #8]
	add r2, r2, r3
	ldr r3, [r1, #0]
	eor r3, r3, r2, ror #14
	str r3, [r1, #0]
	ldr r2, [r1, #20]
	ldr r3, [r1, #16]
	add r2, r2, r3
	ldr r3, [r1, #24]
	eor r3, r3, r2, ror #25
	str r3, [r1, #24]
	ldr r2, [r1, #24]
	ldr r3, [r1, #20]
	add r2, r2, r3
	ldr r3, [r1, #28]
	eor r3, r3, r2, ror #23
	str r3, [r1, #28]
	ldr r2, [r1, #28]
	ldr r3, [r1, #24]
	add r2, r2, r3
	ldr r3, [r1, #16]
	eor r3, r3, r2, ror #19
	str r3, [r1, #16]
	ldr r2, [r1, #16]
	ldr r3, [r1, #28]
	add r2, r2, r3
	ldr r3, [r1, #20]
	eor r3, r3, r2, ror #14
	str r3, [r1, #20]
	ldr r2, [r1, #40]
	ldr r3, [r1, #36]
	add r2, r2, r3
	ldr r3, [r1, #44]
	eor r3, r3, r2, ror #25
	str r3, [r1, #44]
	ldr r2, [r1, #44]
	ldr r3, [r1, #40]
	add r2, r2, r3
	ldr r3, [r1, #32]
	eor r3, r3, r2, ror #23
	str r3, [r1, #32]
	ldr r2, [r1, #32]
	ldr r3, [r1, #44]
	add r2, r2, r3
	ldr r3, [r1, #36]
	eor r3, r3, r2, ror #19
	str r3, [r1, #36]
	ldr r2, [r1, #36]
	ldr r3, [r1, #32]
	add r2, r2, r3
	ldr r3, [r1, #40]
	eor r3, r3, r2, ror #14
	str r3, [r1, #40]
	ldr r2, [r1, #60]
	ldr r3, [r1, #56]
	add r2, r2, r3
	ldr r3, [r1, #48]
	eor r3, r3, r2, ror #25
	str r3, [r1, #48]
	ldr r2, [r1, #48]
	ldr r3, [r1, #60]
	add r2, r2, r3
	ldr r3, [r1, #52]
	eor r3, r3, r2, ror #23
	str r3, [r1, #52]
	ldr r2, [r1, #52]
	ldr r3, [r1, #48]
	add r2, r2, r3
	ldr r3, [r1, #56]
	eor r3, r3, r2, ror #19
	str r3, [r1, #56]
	ldr r2, [r1, #56]
	ldr r3, [r1, #52]
	add r2, r2, r3
	ldr r3, [r1, #60]
	eor r3, r3, r2, ror #14
	str r3, [r1, #60]
	ldr r2, [r1, #0]
	ldr r3, [r0, #0]
	add r2, r2, r3
	str r2, [r0, #0]
	ldr r2, [r1, #4]
	ldr r3, [r0, #4]
	add r2, r2, r3
	str r2, [r0, #4]
	ldr r2, [r1, #8]
	ldr r3, [r0, #8]
	add r2, r2, r3
	str r2, [r0, #8]
	ldr r2, [r1, #12]
	ldr r3, [r0, #12]
	add r2, r2, r3
	str r2, [r0, #12]
	ldr r2, [r1, #16]
	ldr r3, [r0, #16]
	add r2, r2, r3
	str r2, [r0, #16]
	ldr r2, [r1, #20]
	ldr r3, [r0, #20]
	add r2, r2, r3
	str r2, [r0, #20]
	ldr r2, [r1, #24]
	ldr r3, [r0, #24]
	add r2, r2, r3
	str r2, [r0, #24]
	ldr r2, [r1, #28]
	ldr r3, [r0, #28]
	add r2, r2, r3
	str r2, [r0, #28]
	ldr r2, [r1, #32]
	ldr r3, [r0, #32]
	add r2, r2, r3
	str r2, [r0, #32]
	ldr r2, [r1, #36]
	ldr r3, [r0, #36]
	add r2, r2, r3
	str r2, [r0, #36]
	ldr r2, [r1, #40]
	ldr r3, [r0, #40]
	add r2, r2, r3
	str r2, [r0, #40]
	ldr r2, [r1, #44]
	ldr r3, [r0, #44]
	add r2, r2, r3
	str r2, [r0, #44]
	ldr r2, [r1, #48]
	ldr r3, [r0, #48]
	add r2, r2, r3
	str r2, [r0, #48]
	ldr r2, [r1, #52]
	ldr r3, [r0, #52]
	add r2, r2, r3
	str r2, [r0, #52]
	ldr r2, [r1, #56]
	ldr r3, [r0, #56]
	add r2, r2, r3
	str r2, [r0, #56]
	ldr r2, [r1, #60]
	ldr r3, [r0, #60]
	add r2, r2, r3
	str r2, [r0, #60]
	bx lr
