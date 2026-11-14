// The functions of `src/internal/vg_secp256k1_add_mod_p.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_secp256k1_add_mod_p:
	rlwinm %r4, %r4, 0, 0, 31
	rlwinm %r5, %r5, 0, 0, 31
	rlwinm %r6, %r6, 0, 0, 31
	add %r4, %r3, %r4
	add %r5, %r3, %r5
	add %r6, %r3, %r6
	ld %r11, 0(%r5)
	ld %r12, 0(%r6)
	addc %r7, %r11, %r12
	ld %r11, 8(%r5)
	ld %r12, 8(%r6)
	adde %r8, %r11, %r12
	ld %r11, 16(%r5)
	ld %r12, 16(%r6)
	adde %r9, %r11, %r12
	ld %r11, 24(%r5)
	ld %r12, 24(%r6)
	adde %r10, %r11, %r12
	li %r0, 0
	addze %r0, %r0
	lis %r12, -1
	ori %r12, %r12, 65534
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 65535
	ori %r12, %r12, 64559
	subfc %r7, %r12, %r7
	lis %r12, -1
	ori %r12, %r12, 65535
	subfe %r8, %r12, %r8
	lis %r12, -1
	ori %r12, %r12, 65535
	subfe %r9, %r12, %r9
	lis %r12, -1
	ori %r12, %r12, 65535
	subfe %r10, %r12, %r10
	addze %r11, %r0
	addi %r11, %r11, -1
	lis %r12, -1
	ori %r12, %r12, 65534
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 65535
	ori %r12, %r12, 64559
	and %r12, %r12, %r11
	addc %r7, %r7, %r12
	std %r7, 0(%r4)
	adde %r8, %r8, %r11
	std %r8, 8(%r4)
	adde %r9, %r9, %r11
	std %r9, 16(%r4)
	adde %r10, %r10, %r11
	std %r10, 24(%r4)
	blr
