// The functions of `src/blake2b.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blake2b_init:
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

vg_blake2b_update:
	stdu %r1, -608(%r1)
	addi %r7, %r1, 32
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r26, 512(%r7)
	std %r27, 520(%r7)
	std %r28, 528(%r7)
	std %r29, 536(%r7)
	std %r30, 544(%r7)
	std %r31, 552(%r7)
	addi %r26, %r3, 0
	addi %r27, %r7, 0
	addi %r28, %r5, 0
	addi %r29, %r6, 0
	addi %r31, %r4, 0
	addi %r30, %r31, -1
	li %r9, 127
	and %r30, %r30, %r9
	addi %r30, %r30, 1
	cmpldi %cr0, %r31, 0
	beq %cr0, 20f
	b 21f
20:
	li %r30, 0
21:
	cmpldi %cr0, %r29, 0
	beq %cr0, 22f
	cmpldi %cr0, %r30, 0
	beq %cr0, 24f
	li %r11, 128
	subf %r11, %r30, %r11
	rldicl %r9, %r29, 57, 7
	cmpldi %cr0, %r9, 0
	beq %cr0, 26f
	b 27f
26:
	add %r9, %r29, %r30
	rldicl %r9, %r9, 57, 7
	cmpldi %cr0, %r9, 0
	beq %cr0, 28f
	b 29f
28:
	addi %r11, %r29, 0
29:
27:
	subf %r29, %r11, %r29
	add %r31, %r31, %r11
	cmpldi %cr0, %r11, 0
	beq %cr0, 210f
212:
	lbz %r9, 0(%r28)
	add %r12, %r26, %r30
	stb %r9, 64(%r12)
	addi %r28, %r28, 1
	addi %r30, %r30, 1
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 212b
	b 211f
210:
211:
	cmpldi %cr0, %r29, 0
	beq %cr0, 213f
	addi %r3, %r26, 0
	addi %r4, %r26, 64
	li %r5, 1
	addi %r6, %r31, 0
	li %r7, 0
	addi %r8, %r27, 0
	bl {vg_blake2b_compress}
	li %r30, 0
	b 214f
213:
214:
	b 25f
24:
25:
	cmpldi %cr0, %r29, 0
	beq %cr0, 215f
	addi %r9, %r29, -1
	rldicl %r10, %r9, 57, 7
	cmpldi %cr0, %r10, 0
	beq %cr0, 217f
	addi %r3, %r26, 0
	addi %r4, %r28, 0
	addi %r5, %r10, 0
	addi %r6, %r31, 128
	li %r7, 0
	addi %r8, %r27, 0
	bl {vg_blake2b_compress}
	addi %r9, %r29, -1
	li %r10, 127
	and %r9, %r9, %r10
	addi %r9, %r9, 1
	subf %r10, %r9, %r29
	add %r28, %r28, %r10
	add %r31, %r31, %r10
	addi %r29, %r9, 0
	b 218f
217:
218:
	addi %r11, %r29, 0
	add %r31, %r31, %r29
	li %r29, 0
219:
	lbz %r9, 0(%r28)
	add %r12, %r26, %r30
	stb %r9, 64(%r12)
	addi %r28, %r28, 1
	addi %r30, %r30, 1
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 219b
	b 216f
215:
216:
	b 23f
22:
23:
	ld %r26, 512(%r27)
	ld %r28, 528(%r27)
	ld %r29, 536(%r27)
	ld %r30, 544(%r27)
	ld %r31, 552(%r27)
	ld %r27, 520(%r27)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	addi %r1, %r1, 608
	blr

vg_blake2b_finalize:
	stdu %r1, -608(%r1)
	addi %r6, %r1, 32
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r26, 512(%r6)
	std %r27, 520(%r6)
	std %r28, 528(%r6)
	std %r29, 536(%r6)
	std %r30, 544(%r6)
	std %r31, 552(%r6)
	addi %r26, %r3, 0
	addi %r27, %r6, 0
	addi %r28, %r5, 0
	addi %r31, %r4, 0
	addi %r30, %r31, -1
	li %r9, 127
	and %r30, %r30, %r9
	addi %r30, %r30, 1
	cmpldi %cr0, %r31, 0
	beq %cr0, 20f
	b 21f
20:
	li %r30, 0
21:
	li %r9, 0
	li %r11, 128
	subf %r11, %r30, %r11
	cmpldi %cr0, %r11, 0
	beq %cr0, 22f
24:
	add %r12, %r26, %r30
	stb %r9, 64(%r12)
	addi %r30, %r30, 1
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 24b
	b 23f
22:
23:
	addi %r3, %r26, 0
	addi %r4, %r26, 64
	li %r5, 1
	addi %r6, %r31, 0
	li %r7, 1
	addi %r8, %r27, 0
	bl {vg_blake2b_compress}
	ld %r9, 0(%r26)
	std %r9, 0(%r28)
	ld %r9, 8(%r26)
	std %r9, 8(%r28)
	ld %r9, 16(%r26)
	std %r9, 16(%r28)
	ld %r9, 24(%r26)
	std %r9, 24(%r28)
	ld %r9, 32(%r26)
	std %r9, 32(%r28)
	ld %r9, 40(%r26)
	std %r9, 40(%r28)
	ld %r9, 48(%r26)
	std %r9, 48(%r28)
	ld %r9, 56(%r26)
	std %r9, 56(%r28)
	ld %r26, 512(%r27)
	ld %r28, 528(%r27)
	ld %r29, 536(%r27)
	ld %r30, 544(%r27)
	ld %r31, 552(%r27)
	ld %r27, 520(%r27)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	addi %r1, %r1, 608
	blr
