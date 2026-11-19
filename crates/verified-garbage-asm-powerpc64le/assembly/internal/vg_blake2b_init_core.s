// The functions of `src/internal/vg_blake2b_init_core.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blake2b_init_core:
	lis %r9, -17561
	ori %r9, %r9, 44677
	rldicr %r9, %r9, 32, 31
	oris %r9, %r9, 33994
	ori %r9, %r9, 42811
	std %r9, 8(%r3)
	lis %r9, 15470
	ori %r9, %r9, 62322
	rldicr %r9, %r9, 32, 31
	oris %r9, %r9, 65172
	ori %r9, %r9, 63531
	std %r9, 16(%r3)
	lis %r9, -23217
	ori %r9, %r9, 62778
	rldicr %r9, %r9, 32, 31
	oris %r9, %r9, 24349
	ori %r9, %r9, 14065
	std %r9, 24(%r3)
	lis %r9, 20750
	ori %r9, %r9, 21119
	rldicr %r9, %r9, 32, 31
	oris %r9, %r9, 44518
	ori %r9, %r9, 33489
	std %r9, 32(%r3)
	lis %r9, -25851
	ori %r9, %r9, 26764
	rldicr %r9, %r9, 32, 31
	oris %r9, %r9, 11070
	ori %r9, %r9, 27679
	std %r9, 40(%r3)
	lis %r9, 8067
	ori %r9, %r9, 55723
	rldicr %r9, %r9, 32, 31
	oris %r9, %r9, 64321
	ori %r9, %r9, 48491
	std %r9, 48(%r3)
	lis %r9, 23520
	ori %r9, %r9, 52505
	rldicr %r9, %r9, 32, 31
	oris %r9, %r9, 4990
	ori %r9, %r9, 8569
	std %r9, 56(%r3)
	lis %r9, 27145
	ori %r9, %r9, 58983
	rldicr %r9, %r9, 32, 31
	oris %r9, %r9, 62141
	ori %r9, %r9, 51464
	rldicr %r10, %r6, 8, 55
	xor %r9, %r9, %r10
	xor %r9, %r9, %r4
	std %r9, 0(%r3)
	cmpldi %cr0, %r6, 0
	beq %cr0, 20f
	li %r9, 0
	std %r9, 64(%r3)
	std %r9, 72(%r3)
	std %r9, 80(%r3)
	std %r9, 88(%r3)
	std %r9, 96(%r3)
	std %r9, 104(%r3)
	std %r9, 112(%r3)
	std %r9, 120(%r3)
	std %r9, 128(%r3)
	std %r9, 136(%r3)
	std %r9, 144(%r3)
	std %r9, 152(%r3)
	std %r9, 160(%r3)
	std %r9, 168(%r3)
	std %r9, 176(%r3)
	std %r9, 184(%r3)
	addi %r12, %r3, 64
22:
	lbz %r9, 0(%r5)
	stb %r9, 0(%r12)
	addi %r5, %r5, 1
	addi %r12, %r12, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 22b
	b 21f
20:
21:
	blr
