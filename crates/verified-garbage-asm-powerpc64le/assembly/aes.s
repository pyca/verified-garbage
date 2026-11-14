// The functions of `src/aes.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_expand_key:
	or %r7, %r4, %r4
20:
	ld %r8, 0(%r3)
	std %r8, 0(%r5)
	addi %r3, %r3, 8
	addi %r5, %r5, 8
	addi %r4, %r4, -8
	cmpldi %cr0, %r4, 0
	bne %cr0, 20b
	addi %r0, %r7, -24
	cmpldi %cr0, %r0, 0
	beq %cr0, 21f
	subf %r11, %r7, %r5
	li %r12, 0
	lxvd2x 33, %r11, %r12
	vsldoi %v1, %v1, %v1, 8
	addi %r10, %r11, 16
	lxvd2x 34, %r10, %r12
	vsldoi %v2, %v2, %v2, 8
	vxor %v4, %v4, %v4
	lis %r8, 768
	ori %r8, %r8, 258
	rldicr %r8, %r8, 32, 31
	oris %r8, %r8, 768
	ori %r8, %r8, 258
	mtvsrd 37, %r8
	mtvsrd 35, %r8
	vsldoi %v5, %v4, %v5, 8
	vsldoi %v5, %v5, %v3, 8
	lis %r8, 1
	ori %r8, %r8, 515
	rldicr %r8, %r8, 32, 31
	oris %r8, %r8, 1
	ori %r8, %r8, 515
	mtvsrd 38, %r8
	mtvsrd 35, %r8
	vsldoi %v6, %v4, %v6, 8
	vsldoi %v6, %v6, %v3, 8
	lis %r8, 4112
	ori %r8, %r8, 4103
	rldicr %r8, %r8, 32, 31
	oris %r8, %r8, 4112
	ori %r8, %r8, 4103
	mtvsrd 39, %r8
	mtvsrd 35, %r8
	vsldoi %v7, %v4, %v7, 8
	vsldoi %v7, %v7, %v3, 8
	li %r6, 1
	addi %r0, %r7, -16
	cmpldi %cr0, %r0, 0
	beq %cr0, 23f
	li %r4, 6
25:
	mtvsrd 40, %r6
	vperm %v8, %v8, %v4, %v7
	rldicl %r0, %r6, 57, 7
	li %r8, 0
	subf %r0, %r0, %r8
	li %r8, 27
	and %r0, %r0, %r8
	add %r6, %r6, %r6
	xor %r6, %r6, %r0
	li %r8, 255
	and %r6, %r6, %r8
	vperm %v0, %v2, %v2, %v5
	vsbox %v0, %v0
	vxor %v0, %v0, %v8
	vsldoi %v3, %v1, %v4, 4
	vxor %v1, %v1, %v3
	vsldoi %v3, %v1, %v4, 8
	vxor %v1, %v1, %v3
	vxor %v1, %v1, %v0
	vsldoi %v9, %v1, %v1, 8
	stxvd2x 41, %r5, %r12
	addi %r5, %r5, 16
	vperm %v0, %v1, %v1, %v6
	vsbox %v0, %v0
	vsldoi %v3, %v2, %v4, 4
	vxor %v2, %v2, %v3
	vsldoi %v3, %v2, %v4, 8
	vxor %v2, %v2, %v3
	vxor %v2, %v2, %v0
	vsldoi %v9, %v2, %v2, 8
	stxvd2x 41, %r5, %r12
	addi %r5, %r5, 16
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 25b
	mtvsrd 40, %r6
	vperm %v8, %v8, %v4, %v7
	rldicl %r0, %r6, 57, 7
	li %r8, 0
	subf %r0, %r0, %r8
	li %r8, 27
	and %r0, %r0, %r8
	add %r6, %r6, %r6
	xor %r6, %r6, %r0
	li %r8, 255
	and %r6, %r6, %r8
	vperm %v0, %v2, %v2, %v5
	vsbox %v0, %v0
	vxor %v0, %v0, %v8
	vsldoi %v3, %v1, %v4, 4
	vxor %v1, %v1, %v3
	vsldoi %v3, %v1, %v4, 8
	vxor %v1, %v1, %v3
	vxor %v1, %v1, %v0
	vsldoi %v9, %v1, %v1, 8
	stxvd2x 41, %r5, %r12
	addi %r5, %r5, 16
	b 24f
23:
	li %r4, 10
26:
	mtvsrd 40, %r6
	vperm %v8, %v8, %v4, %v7
	rldicl %r0, %r6, 57, 7
	li %r8, 0
	subf %r0, %r0, %r8
	li %r8, 27
	and %r0, %r0, %r8
	add %r6, %r6, %r6
	xor %r6, %r6, %r0
	li %r8, 255
	and %r6, %r6, %r8
	vperm %v0, %v1, %v1, %v5
	vsbox %v0, %v0
	vxor %v0, %v0, %v8
	vsldoi %v3, %v1, %v4, 4
	vxor %v1, %v1, %v3
	vsldoi %v3, %v1, %v4, 8
	vxor %v1, %v1, %v3
	vxor %v1, %v1, %v0
	vsldoi %v9, %v1, %v1, 8
	stxvd2x 41, %r5, %r12
	addi %r5, %r5, 16
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 26b
24:
	b 22f
21:
	subf %r10, %r7, %r5
	addi %r11, %r5, -4
	li %r12, 0
	rldicl %r4, %r7, 62, 2
	add %r8, %r4, %r4
	add %r4, %r4, %r8
	addi %r4, %r4, 28
	li %r6, 1
	lwz %r9, 0(%r11)
27:
	cmpldi %cr0, %r12, 0
	beq %cr0, 28f
	addi %r0, %r12, -16
	cmpldi %cr0, %r0, 0
	beq %cr0, 210f
	b 211f
210:
	addi %r0, %r7, -32
	cmpldi %cr0, %r0, 0
	beq %cr0, 212f
	b 213f
212:
	mtvsrd 32, %r9
	vsbox %v0, %v0
	mfvsrd %r9, 32
	rlwinm %r9, %r9, 0, 0, 31
213:
211:
	b 29f
28:
	mtvsrd 32, %r9
	vsbox %v0, %v0
	mfvsrd %r9, 32
	rlwinm %r9, %r9, 0, 0, 31
	rlwinm %r9, %r9, 24, 0, 31
	xor %r9, %r9, %r6
	rldicl %r0, %r6, 57, 7
	li %r8, 0
	subf %r0, %r0, %r8
	li %r8, 27
	and %r0, %r0, %r8
	add %r6, %r6, %r6
	xor %r6, %r6, %r0
	li %r8, 255
	and %r6, %r6, %r8
29:
	lwz %r8, 0(%r10)
	xor %r9, %r9, %r8
	stw %r9, 4(%r11)
	addi %r11, %r11, 4
	addi %r10, %r10, 4
	addi %r12, %r12, 4
	subf %r0, %r7, %r12
	cmpldi %cr0, %r0, 0
	beq %cr0, 214f
	b 215f
214:
	li %r12, 0
215:
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 27b
22:
	blr
