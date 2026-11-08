// The functions of `src/internal/vg_gf25519_r32_pow250.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_gf25519_r32_pow250:
	addi %r6, %r3, 0
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 128(%r6)
	ld %r5, 128(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 136(%r6)
	ld %r5, 128(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 128(%r6)
	ld %r5, 136(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 144(%r6)
	ld %r5, 128(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 136(%r6)
	ld %r5, 136(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 128(%r6)
	ld %r5, 144(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 152(%r6)
	ld %r5, 128(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 144(%r6)
	ld %r5, 136(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 136(%r6)
	ld %r5, 144(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 128(%r6)
	ld %r5, 152(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 152(%r6)
	ld %r5, 136(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 144(%r6)
	ld %r5, 144(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 136(%r6)
	ld %r5, 152(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 152(%r6)
	ld %r5, 144(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 144(%r6)
	ld %r5, 152(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 152(%r6)
	ld %r5, 152(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 512(%r6)
	std %r9, 520(%r6)
	std %r10, 528(%r6)
	std %r11, 536(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 512(%r6)
	ld %r5, 512(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 520(%r6)
	ld %r5, 512(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 512(%r6)
	ld %r5, 520(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 528(%r6)
	ld %r5, 512(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 520(%r6)
	ld %r5, 520(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 512(%r6)
	ld %r5, 528(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 536(%r6)
	ld %r5, 512(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 528(%r6)
	ld %r5, 520(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 520(%r6)
	ld %r5, 528(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 512(%r6)
	ld %r5, 536(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 536(%r6)
	ld %r5, 520(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 528(%r6)
	ld %r5, 528(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 520(%r6)
	ld %r5, 536(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 536(%r6)
	ld %r5, 528(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 528(%r6)
	ld %r5, 536(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 536(%r6)
	ld %r5, 536(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 544(%r6)
	std %r9, 552(%r6)
	std %r10, 560(%r6)
	std %r11, 568(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 544(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 552(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 544(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 560(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 552(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 544(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 568(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 560(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 552(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 544(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 568(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 560(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 552(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 568(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 560(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 568(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 544(%r6)
	std %r9, 552(%r6)
	std %r10, 560(%r6)
	std %r11, 568(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 128(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 136(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 128(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 144(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 136(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 128(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 152(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 144(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 136(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 128(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 152(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 144(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 136(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 152(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 144(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 152(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 544(%r6)
	std %r9, 552(%r6)
	std %r10, 560(%r6)
	std %r11, 568(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 512(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 520(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 512(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 528(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 520(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 512(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 536(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 528(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 520(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 512(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 536(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 528(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 520(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 536(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 528(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 536(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 512(%r6)
	std %r9, 520(%r6)
	std %r10, 528(%r6)
	std %r11, 536(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 512(%r6)
	ld %r5, 512(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 520(%r6)
	ld %r5, 512(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 512(%r6)
	ld %r5, 520(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 528(%r6)
	ld %r5, 512(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 520(%r6)
	ld %r5, 520(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 512(%r6)
	ld %r5, 528(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 536(%r6)
	ld %r5, 512(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 528(%r6)
	ld %r5, 520(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 520(%r6)
	ld %r5, 528(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 512(%r6)
	ld %r5, 536(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 536(%r6)
	ld %r5, 520(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 528(%r6)
	ld %r5, 528(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 520(%r6)
	ld %r5, 536(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 536(%r6)
	ld %r5, 528(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 528(%r6)
	ld %r5, 536(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 536(%r6)
	ld %r5, 536(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 576(%r6)
	std %r9, 584(%r6)
	std %r10, 592(%r6)
	std %r11, 600(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 544(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 552(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 544(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 560(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 552(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 544(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 568(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 560(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 552(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 544(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 568(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 560(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 552(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 568(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 560(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 568(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 544(%r6)
	std %r9, 552(%r6)
	std %r10, 560(%r6)
	std %r11, 568(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 544(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 552(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 544(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 560(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 552(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 544(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 568(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 560(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 552(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 544(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 568(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 560(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 552(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 568(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 560(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 568(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 576(%r6)
	std %r9, 584(%r6)
	std %r10, 592(%r6)
	std %r11, 600(%r6)
	li %r12, 4
20:
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 576(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 584(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 576(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 592(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 584(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 576(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 600(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 592(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 584(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 576(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 600(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 592(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 584(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 600(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 592(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 600(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 576(%r6)
	std %r9, 584(%r6)
	std %r10, 592(%r6)
	std %r11, 600(%r6)
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 20b
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 576(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 584(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 576(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 592(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 584(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 576(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 600(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 592(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 584(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 576(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 600(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 592(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 584(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 600(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 592(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 600(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 544(%r6)
	std %r9, 552(%r6)
	std %r10, 560(%r6)
	std %r11, 568(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 544(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 552(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 544(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 560(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 552(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 544(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 568(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 560(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 552(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 544(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 568(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 560(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 552(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 568(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 560(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 568(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 576(%r6)
	std %r9, 584(%r6)
	std %r10, 592(%r6)
	std %r11, 600(%r6)
	li %r12, 9
21:
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 576(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 584(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 576(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 592(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 584(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 576(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 600(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 592(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 584(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 576(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 600(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 592(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 584(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 600(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 592(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 600(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 576(%r6)
	std %r9, 584(%r6)
	std %r10, 592(%r6)
	std %r11, 600(%r6)
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 21b
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 576(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 584(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 576(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 592(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 584(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 576(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 600(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 592(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 584(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 576(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 600(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 592(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 584(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 600(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 592(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 600(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 576(%r6)
	std %r9, 584(%r6)
	std %r10, 592(%r6)
	std %r11, 600(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 576(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 584(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 576(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 592(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 584(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 576(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 600(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 592(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 584(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 576(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 600(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 592(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 584(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 600(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 592(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 600(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 608(%r6)
	std %r9, 616(%r6)
	std %r10, 624(%r6)
	std %r11, 632(%r6)
	li %r12, 19
22:
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 608(%r6)
	ld %r5, 608(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 616(%r6)
	ld %r5, 608(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 608(%r6)
	ld %r5, 616(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 624(%r6)
	ld %r5, 608(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 616(%r6)
	ld %r5, 616(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 608(%r6)
	ld %r5, 624(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 632(%r6)
	ld %r5, 608(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 624(%r6)
	ld %r5, 616(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 616(%r6)
	ld %r5, 624(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 608(%r6)
	ld %r5, 632(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 632(%r6)
	ld %r5, 616(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 624(%r6)
	ld %r5, 624(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 616(%r6)
	ld %r5, 632(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 632(%r6)
	ld %r5, 624(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 624(%r6)
	ld %r5, 632(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 632(%r6)
	ld %r5, 632(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 608(%r6)
	std %r9, 616(%r6)
	std %r10, 624(%r6)
	std %r11, 632(%r6)
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 22b
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 608(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 616(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 608(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 624(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 616(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 608(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 632(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 624(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 616(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 608(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 632(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 624(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 616(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 632(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 624(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 632(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 576(%r6)
	std %r9, 584(%r6)
	std %r10, 592(%r6)
	std %r11, 600(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 576(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 584(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 576(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 592(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 584(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 576(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 600(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 592(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 584(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 576(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 600(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 592(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 584(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 600(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 592(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 600(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 576(%r6)
	std %r9, 584(%r6)
	std %r10, 592(%r6)
	std %r11, 600(%r6)
	li %r12, 9
23:
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 576(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 584(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 576(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 592(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 584(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 576(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 600(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 592(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 584(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 576(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 600(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 592(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 584(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 600(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 592(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 600(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 576(%r6)
	std %r9, 584(%r6)
	std %r10, 592(%r6)
	std %r11, 600(%r6)
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 23b
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 576(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 584(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 576(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 592(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 584(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 576(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 600(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 592(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 584(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 576(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 600(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 592(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 584(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 600(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 592(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 600(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 544(%r6)
	std %r9, 552(%r6)
	std %r10, 560(%r6)
	std %r11, 568(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 544(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 552(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 544(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 560(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 552(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 544(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 568(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 560(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 552(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 544(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 568(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 560(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 552(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 568(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 560(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 568(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 576(%r6)
	std %r9, 584(%r6)
	std %r10, 592(%r6)
	std %r11, 600(%r6)
	li %r12, 49
24:
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 576(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 584(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 576(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 592(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 584(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 576(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 600(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 592(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 584(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 576(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 600(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 592(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 584(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 600(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 592(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 600(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 576(%r6)
	std %r9, 584(%r6)
	std %r10, 592(%r6)
	std %r11, 600(%r6)
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 24b
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 576(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 584(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 576(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 592(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 584(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 576(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 600(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 592(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 584(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 576(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 600(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 592(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 584(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 600(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 592(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 600(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 576(%r6)
	std %r9, 584(%r6)
	std %r10, 592(%r6)
	std %r11, 600(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 576(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 584(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 576(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 592(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 584(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 576(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 600(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 592(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 584(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 576(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 600(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 592(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 584(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 600(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 592(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 600(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 608(%r6)
	std %r9, 616(%r6)
	std %r10, 624(%r6)
	std %r11, 632(%r6)
	li %r12, 99
25:
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 608(%r6)
	ld %r5, 608(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 616(%r6)
	ld %r5, 608(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 608(%r6)
	ld %r5, 616(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 624(%r6)
	ld %r5, 608(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 616(%r6)
	ld %r5, 616(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 608(%r6)
	ld %r5, 624(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 632(%r6)
	ld %r5, 608(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 624(%r6)
	ld %r5, 616(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 616(%r6)
	ld %r5, 624(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 608(%r6)
	ld %r5, 632(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 632(%r6)
	ld %r5, 616(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 624(%r6)
	ld %r5, 624(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 616(%r6)
	ld %r5, 632(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 632(%r6)
	ld %r5, 624(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 624(%r6)
	ld %r5, 632(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 632(%r6)
	ld %r5, 632(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 608(%r6)
	std %r9, 616(%r6)
	std %r10, 624(%r6)
	std %r11, 632(%r6)
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 25b
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 608(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 616(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 608(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 624(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 616(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 608(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 632(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 624(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 616(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 608(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 632(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 624(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 616(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 632(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 624(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 632(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 576(%r6)
	std %r9, 584(%r6)
	std %r10, 592(%r6)
	std %r11, 600(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 576(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 584(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 576(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 592(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 584(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 576(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 600(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 592(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 584(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 576(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 600(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 592(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 584(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 600(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 592(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 600(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 576(%r6)
	std %r9, 584(%r6)
	std %r10, 592(%r6)
	std %r11, 600(%r6)
	li %r12, 49
26:
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 576(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 584(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 576(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 592(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 584(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 576(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 600(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 592(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 584(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 576(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 600(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 592(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 584(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 600(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 592(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 600(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 576(%r6)
	std %r9, 584(%r6)
	std %r10, 592(%r6)
	std %r11, 600(%r6)
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 26b
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 576(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 584(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 576(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 592(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 584(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 576(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 600(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 592(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 584(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 576(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 600(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 592(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 584(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 600(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 592(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 600(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 544(%r6)
	std %r9, 552(%r6)
	std %r10, 560(%r6)
	std %r11, 568(%r6)
	blr
