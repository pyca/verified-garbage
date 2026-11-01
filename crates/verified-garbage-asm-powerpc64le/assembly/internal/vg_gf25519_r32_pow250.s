// The functions of `src/internal/vg_gf25519_r32_pow250.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_gf25519_r32_pow250:
	addi %r6, %r3, 0
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
20:
	lwz %r4, 128(%r9)
	li %r8, 0
	lwz %r5, 128(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 132(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 136(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 140(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 144(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 148(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 152(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 156(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 20b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 516(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 520(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 524(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 528(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 532(%r6)
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 536(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
21:
	lwz %r4, 512(%r9)
	li %r8, 0
	lwz %r5, 512(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 516(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 520(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 524(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 528(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 532(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 536(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 540(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 21b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 560(%r6)
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
22:
	lwz %r4, 544(%r9)
	li %r8, 0
	lwz %r5, 544(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 548(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 552(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 556(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 560(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 564(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 568(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 572(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 22b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 560(%r6)
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
23:
	lwz %r4, 128(%r9)
	li %r8, 0
	lwz %r5, 544(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 548(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 552(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 556(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 560(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 564(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 568(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 572(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 23b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 560(%r6)
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
24:
	lwz %r4, 512(%r9)
	li %r8, 0
	lwz %r5, 544(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 548(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 552(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 556(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 560(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 564(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 568(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 572(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 24b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 516(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 520(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 524(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 528(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 532(%r6)
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 536(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
25:
	lwz %r4, 512(%r9)
	li %r8, 0
	lwz %r5, 512(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 516(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 520(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 524(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 528(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 532(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 536(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 540(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 25b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 580(%r6)
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 584(%r6)
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 588(%r6)
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 592(%r6)
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 596(%r6)
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 600(%r6)
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 604(%r6)
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
26:
	lwz %r4, 544(%r9)
	li %r8, 0
	lwz %r5, 576(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 580(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 584(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 588(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 592(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 596(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 600(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 604(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 26b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 560(%r6)
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
27:
	lwz %r4, 544(%r9)
	li %r8, 0
	lwz %r5, 544(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 548(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 552(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 556(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 560(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 564(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 568(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 572(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 27b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 580(%r6)
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 584(%r6)
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 588(%r6)
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 592(%r6)
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 596(%r6)
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 600(%r6)
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 604(%r6)
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	li %r12, 4
28:
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
29:
	lwz %r4, 576(%r9)
	li %r8, 0
	lwz %r5, 576(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 580(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 584(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 588(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 592(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 596(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 600(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 604(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 29b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 580(%r6)
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 584(%r6)
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 588(%r6)
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 592(%r6)
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 596(%r6)
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 600(%r6)
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 604(%r6)
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 28b
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
210:
	lwz %r4, 576(%r9)
	li %r8, 0
	lwz %r5, 544(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 548(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 552(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 556(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 560(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 564(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 568(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 572(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 210b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 560(%r6)
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
211:
	lwz %r4, 544(%r9)
	li %r8, 0
	lwz %r5, 544(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 548(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 552(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 556(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 560(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 564(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 568(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 572(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 211b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 580(%r6)
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 584(%r6)
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 588(%r6)
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 592(%r6)
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 596(%r6)
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 600(%r6)
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 604(%r6)
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	li %r12, 9
212:
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
213:
	lwz %r4, 576(%r9)
	li %r8, 0
	lwz %r5, 576(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 580(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 584(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 588(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 592(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 596(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 600(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 604(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 213b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 580(%r6)
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 584(%r6)
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 588(%r6)
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 592(%r6)
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 596(%r6)
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 600(%r6)
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 604(%r6)
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 212b
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
214:
	lwz %r4, 576(%r9)
	li %r8, 0
	lwz %r5, 544(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 548(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 552(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 556(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 560(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 564(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 568(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 572(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 214b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 580(%r6)
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 584(%r6)
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 588(%r6)
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 592(%r6)
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 596(%r6)
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 600(%r6)
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 604(%r6)
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
215:
	lwz %r4, 576(%r9)
	li %r8, 0
	lwz %r5, 576(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 580(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 584(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 588(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 592(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 596(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 600(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 604(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 215b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 608(%r6)
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 612(%r6)
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 616(%r6)
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 620(%r6)
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 624(%r6)
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 628(%r6)
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 632(%r6)
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 636(%r6)
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 608(%r6)
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	li %r12, 19
216:
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
217:
	lwz %r4, 608(%r9)
	li %r8, 0
	lwz %r5, 608(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 612(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 616(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 620(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 624(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 628(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 632(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 636(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 217b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 608(%r6)
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 612(%r6)
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 616(%r6)
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 620(%r6)
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 624(%r6)
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 628(%r6)
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 632(%r6)
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 636(%r6)
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 608(%r6)
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 216b
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
218:
	lwz %r4, 608(%r9)
	li %r8, 0
	lwz %r5, 576(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 580(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 584(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 588(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 592(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 596(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 600(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 604(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 218b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 580(%r6)
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 584(%r6)
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 588(%r6)
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 592(%r6)
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 596(%r6)
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 600(%r6)
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 604(%r6)
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
219:
	lwz %r4, 576(%r9)
	li %r8, 0
	lwz %r5, 576(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 580(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 584(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 588(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 592(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 596(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 600(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 604(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 219b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 580(%r6)
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 584(%r6)
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 588(%r6)
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 592(%r6)
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 596(%r6)
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 600(%r6)
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 604(%r6)
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	li %r12, 9
220:
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
221:
	lwz %r4, 576(%r9)
	li %r8, 0
	lwz %r5, 576(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 580(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 584(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 588(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 592(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 596(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 600(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 604(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 221b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 580(%r6)
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 584(%r6)
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 588(%r6)
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 592(%r6)
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 596(%r6)
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 600(%r6)
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 604(%r6)
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 220b
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
222:
	lwz %r4, 576(%r9)
	li %r8, 0
	lwz %r5, 544(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 548(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 552(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 556(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 560(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 564(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 568(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 572(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 222b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 560(%r6)
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
223:
	lwz %r4, 544(%r9)
	li %r8, 0
	lwz %r5, 544(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 548(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 552(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 556(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 560(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 564(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 568(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 572(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 223b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 580(%r6)
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 584(%r6)
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 588(%r6)
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 592(%r6)
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 596(%r6)
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 600(%r6)
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 604(%r6)
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	li %r12, 49
224:
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
225:
	lwz %r4, 576(%r9)
	li %r8, 0
	lwz %r5, 576(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 580(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 584(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 588(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 592(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 596(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 600(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 604(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 225b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 580(%r6)
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 584(%r6)
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 588(%r6)
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 592(%r6)
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 596(%r6)
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 600(%r6)
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 604(%r6)
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 224b
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
226:
	lwz %r4, 576(%r9)
	li %r8, 0
	lwz %r5, 544(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 548(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 552(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 556(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 560(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 564(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 568(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 572(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 226b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 580(%r6)
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 584(%r6)
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 588(%r6)
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 592(%r6)
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 596(%r6)
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 600(%r6)
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 604(%r6)
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
227:
	lwz %r4, 576(%r9)
	li %r8, 0
	lwz %r5, 576(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 580(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 584(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 588(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 592(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 596(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 600(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 604(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 227b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 608(%r6)
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 612(%r6)
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 616(%r6)
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 620(%r6)
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 624(%r6)
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 628(%r6)
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 632(%r6)
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 636(%r6)
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 608(%r6)
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	li %r12, 99
228:
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
229:
	lwz %r4, 608(%r9)
	li %r8, 0
	lwz %r5, 608(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 612(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 616(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 620(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 624(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 628(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 632(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 636(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 229b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 608(%r6)
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 612(%r6)
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 616(%r6)
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 620(%r6)
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 624(%r6)
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 628(%r6)
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 632(%r6)
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 636(%r6)
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 608(%r6)
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 228b
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
230:
	lwz %r4, 608(%r9)
	li %r8, 0
	lwz %r5, 576(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 580(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 584(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 588(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 592(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 596(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 600(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 604(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 230b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 580(%r6)
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 584(%r6)
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 588(%r6)
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 592(%r6)
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 596(%r6)
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 600(%r6)
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 604(%r6)
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
231:
	lwz %r4, 576(%r9)
	li %r8, 0
	lwz %r5, 576(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 580(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 584(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 588(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 592(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 596(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 600(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 604(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 231b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 580(%r6)
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 584(%r6)
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 588(%r6)
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 592(%r6)
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 596(%r6)
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 600(%r6)
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 604(%r6)
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	li %r12, 49
232:
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
233:
	lwz %r4, 576(%r9)
	li %r8, 0
	lwz %r5, 576(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 580(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 584(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 588(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 592(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 596(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 600(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 604(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 233b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 580(%r6)
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 584(%r6)
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 588(%r6)
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 592(%r6)
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 596(%r6)
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 600(%r6)
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 604(%r6)
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 232b
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
234:
	lwz %r4, 576(%r9)
	li %r8, 0
	lwz %r5, 544(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 548(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 552(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 556(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 560(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 564(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 568(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 572(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 234b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 560(%r6)
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	blr
