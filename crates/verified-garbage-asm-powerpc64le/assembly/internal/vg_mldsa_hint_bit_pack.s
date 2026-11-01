// The functions of `src/internal/vg_mldsa_hint_bit_pack.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_hint_bit_pack:
	rldicr %r5, %r5, 32, 31
	rldicl %r5, %r5, 32, 32
	subf %r4, %r5, %r7
	addi %r9, %r7, 0
	li %r0, 0
	addi %r10, %r6, 0
20:
	stb %r0, 0(%r10)
	addi %r10, %r10, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 20b
	addi %r9, %r4, 0
	add %r10, %r6, %r5
	li %r11, 0
21:
	li %r12, 0
22:
	lwz %r8, 0(%r3)
	cmplwi %cr0, %r8, 0
	beq %cr0, 23f
	add %r8, %r6, %r11
	stb %r12, 0(%r8)
	addi %r11, %r11, 1
	b 24f
23:
24:
	addi %r3, %r3, 4
	addi %r12, %r12, 1
	addi %r8, %r12, -256
	cmpldi %cr0, %r8, 0
	bne %cr0, 22b
	stb %r11, 0(%r10)
	addi %r10, %r10, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 21b
	blr
