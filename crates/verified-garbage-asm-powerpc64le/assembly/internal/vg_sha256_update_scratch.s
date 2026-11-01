// The functions of `src/internal/vg_sha256_update_scratch.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha256_update_scratch:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r26, 112(%r7)
	std %r27, 120(%r7)
	std %r28, 128(%r7)
	std %r29, 136(%r7)
	std %r30, 144(%r7)
	std %r31, 152(%r7)
	addi %r26, %r3, 0
	addi %r27, %r7, 0
	addi %r28, %r5, 0
	addi %r29, %r6, 0
	li %r8, 63
	and %r30, %r4, %r8
	cmpldi %cr0, %r29, 0
	beq %cr0, 20f
22:
	li %r9, 0
	cmpldi %cr0, %r30, 0
	beq %cr0, 23f
	li %r10, 64
	subf %r10, %r30, %r10
	rldicl %r8, %r29, 58, 6
	cmpldi %cr0, %r8, 0
	beq %cr0, 25f
	b 26f
25:
	add %r8, %r29, %r30
	rldicl %r8, %r8, 58, 6
	cmpldi %cr0, %r8, 0
	beq %cr0, 27f
	b 28f
27:
	addi %r10, %r29, 0
28:
26:
	subf %r29, %r10, %r29
29:
	lbz %r8, 0(%r28)
	add %r11, %r26, %r30
	stb %r8, 32(%r11)
	addi %r28, %r28, 1
	addi %r30, %r30, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 29b
	addi %r8, %r30, -64
	cmpldi %cr0, %r8, 0
	beq %cr0, 210f
	b 211f
210:
	addi %r4, %r26, 32
	li %r30, 0
	li %r9, 1
211:
	b 24f
23:
	rldicl %r8, %r29, 58, 6
	cmpldi %cr0, %r8, 0
	beq %cr0, 212f
	addi %r4, %r28, 0
	addi %r28, %r28, 64
	addi %r29, %r29, -64
	li %r9, 1
	b 213f
212:
	li %r10, 64
	subf %r10, %r30, %r10
	rldicl %r8, %r29, 58, 6
	cmpldi %cr0, %r8, 0
	beq %cr0, 214f
	b 215f
214:
	add %r8, %r29, %r30
	rldicl %r8, %r8, 58, 6
	cmpldi %cr0, %r8, 0
	beq %cr0, 216f
	b 217f
216:
	addi %r10, %r29, 0
217:
215:
	subf %r29, %r10, %r29
218:
	lbz %r8, 0(%r28)
	add %r11, %r26, %r30
	stb %r8, 32(%r11)
	addi %r28, %r28, 1
	addi %r30, %r30, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 218b
	addi %r8, %r30, -64
	cmpldi %cr0, %r8, 0
	beq %cr0, 219f
	b 220f
219:
	addi %r4, %r26, 32
	li %r30, 0
	li %r9, 1
220:
213:
24:
	cmpldi %cr0, %r9, 0
	beq %cr0, 221f
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha256_compress}
	b 222f
221:
222:
	cmpldi %cr0, %r29, 0
	bne %cr0, 22b
	b 21f
20:
21:
	ld %r26, 112(%r27)
	ld %r28, 128(%r27)
	ld %r29, 136(%r27)
	ld %r30, 144(%r27)
	ld %r31, 152(%r27)
	ld %r27, 120(%r27)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	blr
