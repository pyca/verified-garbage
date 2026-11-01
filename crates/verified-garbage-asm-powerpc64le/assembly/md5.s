// The functions of `src/md5.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_md5_init:
	lis %r8, 26437
	ori %r8, %r8, 8961
	stw %r8, 0(%r3)
	lis %r8, -4147
	ori %r8, %r8, 43913
	stw %r8, 4(%r3)
	lis %r8, -26438
	ori %r8, %r8, 56574
	stw %r8, 8(%r3)
	lis %r8, 4146
	ori %r8, %r8, 21622
	stw %r8, 12(%r3)
	blr

vg_md5_update:
	stdu %r1, -144(%r1)
	addi %r7, %r1, 32
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r26, 64(%r7)
	std %r27, 72(%r7)
	std %r28, 80(%r7)
	std %r29, 88(%r7)
	std %r30, 96(%r7)
	std %r31, 104(%r7)
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
	rldicl %r12, %r10, 61, 3
	cmpldi %cr0, %r12, 0
	beq %cr0, 29f
211:
	ld %r8, 0(%r28)
	add %r11, %r26, %r30
	std %r8, 16(%r11)
	addi %r28, %r28, 8
	addi %r30, %r30, 8
	addi %r10, %r10, -8
	rldicl %r12, %r10, 61, 3
	cmpldi %cr0, %r12, 0
	bne %cr0, 211b
	b 210f
29:
210:
	cmpldi %cr0, %r10, 0
	beq %cr0, 212f
214:
	lbz %r8, 0(%r28)
	add %r11, %r26, %r30
	stb %r8, 16(%r11)
	addi %r28, %r28, 1
	addi %r30, %r30, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 214b
	b 213f
212:
213:
	addi %r8, %r30, -64
	cmpldi %cr0, %r8, 0
	beq %cr0, 215f
	b 216f
215:
	addi %r4, %r26, 16
	li %r30, 0
	li %r9, 1
216:
	b 24f
23:
	rldicl %r8, %r29, 58, 6
	cmpldi %cr0, %r8, 0
	beq %cr0, 217f
	addi %r4, %r28, 0
	rldicl %r9, %r29, 58, 6
	rldicr %r8, %r9, 6, 57
	add %r28, %r28, %r8
	subf %r29, %r8, %r29
	b 218f
217:
	li %r10, 64
	subf %r10, %r30, %r10
	rldicl %r8, %r29, 58, 6
	cmpldi %cr0, %r8, 0
	beq %cr0, 219f
	b 220f
219:
	add %r8, %r29, %r30
	rldicl %r8, %r8, 58, 6
	cmpldi %cr0, %r8, 0
	beq %cr0, 221f
	b 222f
221:
	addi %r10, %r29, 0
222:
220:
	subf %r29, %r10, %r29
	rldicl %r12, %r10, 61, 3
	cmpldi %cr0, %r12, 0
	beq %cr0, 223f
225:
	ld %r8, 0(%r28)
	add %r11, %r26, %r30
	std %r8, 16(%r11)
	addi %r28, %r28, 8
	addi %r30, %r30, 8
	addi %r10, %r10, -8
	rldicl %r12, %r10, 61, 3
	cmpldi %cr0, %r12, 0
	bne %cr0, 225b
	b 224f
223:
224:
	cmpldi %cr0, %r10, 0
	beq %cr0, 226f
228:
	lbz %r8, 0(%r28)
	add %r11, %r26, %r30
	stb %r8, 16(%r11)
	addi %r28, %r28, 1
	addi %r30, %r30, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 228b
	b 227f
226:
227:
	addi %r8, %r30, -64
	cmpldi %cr0, %r8, 0
	beq %cr0, 229f
	b 230f
229:
	addi %r4, %r26, 16
	li %r30, 0
	li %r9, 1
230:
218:
24:
	cmpldi %cr0, %r9, 0
	beq %cr0, 231f
	addi %r3, %r26, 0
	addi %r5, %r9, 0
	addi %r6, %r27, 0
	bl {vg_md5_compress}
	b 232f
231:
232:
	cmpldi %cr0, %r29, 0
	bne %cr0, 22b
	b 21f
20:
21:
	ld %r26, 64(%r27)
	ld %r28, 80(%r27)
	ld %r29, 88(%r27)
	ld %r30, 96(%r27)
	ld %r31, 104(%r27)
	ld %r27, 72(%r27)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	addi %r1, %r1, 144
	blr

vg_md5_finalize:
	stdu %r1, -144(%r1)
	addi %r6, %r1, 32
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r26, 64(%r6)
	std %r27, 72(%r6)
	std %r28, 80(%r6)
	std %r29, 88(%r6)
	std %r30, 96(%r6)
	std %r31, 104(%r6)
	addi %r26, %r3, 0
	addi %r27, %r6, 0
	addi %r28, %r5, 0
	addi %r29, %r4, 0
	li %r8, 63
	and %r30, %r29, %r8
	li %r8, 128
	add %r11, %r26, %r30
	stb %r8, 16(%r11)
	addi %r30, %r30, 1
	addi %r31, %r30, 7
	rldicl %r31, %r31, 58, 6
20:
	li %r10, 64
	cmpldi %cr0, %r31, 0
	beq %cr0, 21f
	b 22f
21:
	li %r10, 56
22:
	li %r8, 0
	subf %r10, %r30, %r10
	rldicl %r12, %r10, 61, 3
	cmpldi %cr0, %r12, 0
	beq %cr0, 23f
25:
	add %r11, %r26, %r30
	std %r8, 16(%r11)
	addi %r30, %r30, 8
	addi %r10, %r10, -8
	rldicl %r12, %r10, 61, 3
	cmpldi %cr0, %r12, 0
	bne %cr0, 25b
	b 24f
23:
24:
	cmpldi %cr0, %r10, 0
	beq %cr0, 26f
28:
	add %r11, %r26, %r30
	stb %r8, 16(%r11)
	addi %r30, %r30, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 28b
	b 27f
26:
27:
	cmpldi %cr0, %r31, 0
	beq %cr0, 29f
	b 210f
29:
	add %r8, %r29, %r29
	add %r8, %r8, %r8
	add %r8, %r8, %r8
	std %r8, 72(%r26)
210:
	addi %r4, %r26, 16
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_md5_compress}
	li %r30, 0
	addi %r31, %r31, -1
	cmpldi %cr0, %r31, 0
	beq %cr0, 20b
	lwz %r8, 0(%r26)
	stw %r8, 0(%r28)
	lwz %r8, 4(%r26)
	stw %r8, 4(%r28)
	lwz %r8, 8(%r26)
	stw %r8, 8(%r28)
	lwz %r8, 12(%r26)
	stw %r8, 12(%r28)
	ld %r26, 64(%r27)
	ld %r28, 80(%r27)
	ld %r29, 88(%r27)
	ld %r30, 96(%r27)
	ld %r31, 104(%r27)
	ld %r27, 72(%r27)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	addi %r1, %r1, 144
	blr
