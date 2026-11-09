// The functions of `src/internal/vg_p256_sub_mod_p.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p256_sub_mod_p:
	rlwinm %r4, %r4, 0, 0, 31
	rlwinm %r5, %r5, 0, 0, 31
	rlwinm %r6, %r6, 0, 0, 31
	add %r4, %r3, %r4
	add %r5, %r3, %r5
	add %r6, %r3, %r6
	ld %r11, 0(%r5)
	ld %r12, 0(%r6)
	subfc %r7, %r12, %r11
	ld %r11, 8(%r5)
	ld %r12, 8(%r6)
	subfe %r8, %r12, %r11
	ld %r11, 16(%r5)
	ld %r12, 16(%r6)
	subfe %r9, %r12, %r11
	ld %r11, 24(%r5)
	ld %r12, 24(%r6)
	subfe %r10, %r12, %r11
	subfe %r11, %r11, %r11
	addc %r7, %r7, %r11
	std %r7, 0(%r4)
	lis %r12, -1
	ori %r12, %r12, 65535
	rldicl %r12, %r12, 32, 32
	and %r12, %r12, %r11
	adde %r8, %r8, %r12
	std %r8, 8(%r4)
	li %r12, 0
	and %r12, %r12, %r11
	adde %r9, %r9, %r12
	std %r9, 16(%r4)
	lis %r12, -1
	ori %r12, %r12, 65535
	rldicr %r12, %r12, 32, 31
	ori %r12, %r12, 1
	and %r12, %r12, %r11
	adde %r10, %r10, %r12
	std %r10, 24(%r4)
	blr
