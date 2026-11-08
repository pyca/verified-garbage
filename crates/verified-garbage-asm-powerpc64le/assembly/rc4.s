// The functions of `src/rc4.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rc4_init:
	addi %r12, %r4, -1
	rldicl %r12, %r12, 56, 8
	cmpldi %cr0, %r12, 0
	bne %cr0, 20f
	or %r7, %r3, %r3
	or %r3, %r5, %r5
	li %r6, 0
22:
	add %r12, %r3, %r6
	stb %r6, 0(%r12)
	addi %r6, %r6, 1
	li %r12, 256
	subf %r12, %r12, %r6
	cmpldi %cr0, %r12, 0
	bne %cr0, 22b
	li %r6, 0
	li %r5, 0
	li %r9, 0
	li %r8, 0
23:
	add %r12, %r3, %r6
	lbz %r0, 0(%r12)
	add %r9, %r9, %r0
	add %r12, %r7, %r5
	lbz %r0, 0(%r12)
	add %r9, %r9, %r0
	rldicr %r9, %r9, 56, 7
	rldicl %r9, %r9, 8, 56
	li %r0, 7
	xor %r12, %r9, %r0
	rldicr %r12, %r12, 56, 7
	mtvsrd 32, %r12
	rldicr %r12, %r9, 58, 5
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	mtvsrd 33, %r12
	rldicr %r12, %r9, 57, 6
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	mtvsrd 34, %r12
	rldicr %r12, %r9, 56, 7
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	mtvsrd 35, %r12
	li %r12, 16
	or %r11, %r3, %r3
	lxvd2x 36, %r11, %r8
	lxvd2x 37, %r11, %r12
	vperm %v6, %v4, %v5, %v0
	addi %r11, %r11, 32
	lxvd2x 36, %r11, %r8
	lxvd2x 37, %r11, %r12
	vperm %v7, %v4, %v5, %v0
	addi %r11, %r11, 32
	lxvd2x 36, %r11, %r8
	lxvd2x 37, %r11, %r12
	vperm %v8, %v4, %v5, %v0
	addi %r11, %r11, 32
	lxvd2x 36, %r11, %r8
	lxvd2x 37, %r11, %r12
	vperm %v9, %v4, %v5, %v0
	addi %r11, %r11, 32
	lxvd2x 36, %r11, %r8
	lxvd2x 37, %r11, %r12
	vperm %v10, %v4, %v5, %v0
	addi %r11, %r11, 32
	lxvd2x 36, %r11, %r8
	lxvd2x 37, %r11, %r12
	vperm %v11, %v4, %v5, %v0
	addi %r11, %r11, 32
	lxvd2x 36, %r11, %r8
	lxvd2x 37, %r11, %r12
	vperm %v12, %v4, %v5, %v0
	addi %r11, %r11, 32
	lxvd2x 36, %r11, %r8
	lxvd2x 37, %r11, %r12
	vperm %v13, %v4, %v5, %v0
	addi %r11, %r11, 32
	vsel %v6, %v6, %v7, %v1
	vsel %v8, %v8, %v9, %v1
	vsel %v6, %v6, %v8, %v2
	vsel %v10, %v10, %v11, %v1
	vsel %v12, %v12, %v13, %v1
	vsel %v10, %v10, %v12, %v2
	vsel %v6, %v6, %v10, %v3
	mfvsrd %r10, 38
	rldicl %r10, %r10, 8, 56
	add %r12, %r3, %r6
	lbz %r0, 0(%r12)
	xor %r0, %r0, %r10
	vxor %v14, %v14, %v14
	rldicr %r0, %r0, 56, 7
	mtvsrd 47, %r0
	vperm %v15, %v15, %v15, %v14
	rldicr %r0, %r9, 60, 3
	rldicl %r0, %r0, 4, 60
	li %r12, 7
	xor %r0, %r0, %r12
	subf %r0, %r0, %r8
	rldicr %r0, %r0, 60, 3
	rldicl %r0, %r0, 4, 60
	li %r12, 255
	rldicr %r12, %r12, 56, 7
	mtvsrd 32, %r12
	vsldoi %v0, %v14, %v0, 8
	vsldoi %v0, %v0, %v14, 8
	rldicr %r12, %r0, 63, 0
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	mtvsrd 34, %r12
	vperm %v2, %v2, %v2, %v14
	vsldoi %v3, %v0, %v0, 1
	vsel %v0, %v0, %v3, %v2
	rldicr %r12, %r0, 62, 1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	mtvsrd 34, %r12
	vperm %v2, %v2, %v2, %v14
	vsldoi %v3, %v0, %v0, 2
	vsel %v0, %v0, %v3, %v2
	rldicr %r12, %r0, 61, 2
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	mtvsrd 34, %r12
	vperm %v2, %v2, %v2, %v14
	vsldoi %v3, %v0, %v0, 4
	vsel %v0, %v0, %v3, %v2
	rldicr %r12, %r0, 60, 3
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	mtvsrd 34, %r12
	vperm %v2, %v2, %v2, %v14
	vsldoi %v3, %v0, %v0, 8
	vsel %v0, %v0, %v3, %v2
	vand %v0, %v0, %v15
	rldicl %r0, %r9, 60, 4
	subf %r0, %r0, %r8
	rldicr %r0, %r0, 60, 3
	rldicl %r0, %r0, 4, 60
	li %r12, 255
	rldicr %r12, %r12, 56, 7
	mtvsrd 33, %r12
	vsldoi %v1, %v14, %v1, 8
	vsldoi %v1, %v1, %v14, 8
	rldicr %r12, %r0, 63, 0
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	mtvsrd 34, %r12
	vperm %v2, %v2, %v2, %v14
	vsldoi %v3, %v1, %v1, 1
	vsel %v1, %v1, %v3, %v2
	rldicr %r12, %r0, 62, 1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	mtvsrd 34, %r12
	vperm %v2, %v2, %v2, %v14
	vsldoi %v3, %v1, %v1, 2
	vsel %v1, %v1, %v3, %v2
	rldicr %r12, %r0, 61, 2
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	mtvsrd 34, %r12
	vperm %v2, %v2, %v2, %v14
	vsldoi %v3, %v1, %v1, 4
	vsel %v1, %v1, %v3, %v2
	rldicr %r12, %r0, 60, 3
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	mtvsrd 34, %r12
	vperm %v2, %v2, %v2, %v14
	vsldoi %v3, %v1, %v1, 8
	vsel %v1, %v1, %v3, %v2
	or %r11, %r3, %r3
	vperm %v4, %v1, %v1, %v14
	vsldoi %v1, %v1, %v1, 1
	vand %v4, %v0, %v4
	lxvd2x 37, %r11, %r8
	vxor %v5, %v5, %v4
	stxvd2x 37, %r11, %r8
	addi %r11, %r11, 16
	vperm %v4, %v1, %v1, %v14
	vsldoi %v1, %v1, %v1, 1
	vand %v4, %v0, %v4
	lxvd2x 37, %r11, %r8
	vxor %v5, %v5, %v4
	stxvd2x 37, %r11, %r8
	addi %r11, %r11, 16
	vperm %v4, %v1, %v1, %v14
	vsldoi %v1, %v1, %v1, 1
	vand %v4, %v0, %v4
	lxvd2x 37, %r11, %r8
	vxor %v5, %v5, %v4
	stxvd2x 37, %r11, %r8
	addi %r11, %r11, 16
	vperm %v4, %v1, %v1, %v14
	vsldoi %v1, %v1, %v1, 1
	vand %v4, %v0, %v4
	lxvd2x 37, %r11, %r8
	vxor %v5, %v5, %v4
	stxvd2x 37, %r11, %r8
	addi %r11, %r11, 16
	vperm %v4, %v1, %v1, %v14
	vsldoi %v1, %v1, %v1, 1
	vand %v4, %v0, %v4
	lxvd2x 37, %r11, %r8
	vxor %v5, %v5, %v4
	stxvd2x 37, %r11, %r8
	addi %r11, %r11, 16
	vperm %v4, %v1, %v1, %v14
	vsldoi %v1, %v1, %v1, 1
	vand %v4, %v0, %v4
	lxvd2x 37, %r11, %r8
	vxor %v5, %v5, %v4
	stxvd2x 37, %r11, %r8
	addi %r11, %r11, 16
	vperm %v4, %v1, %v1, %v14
	vsldoi %v1, %v1, %v1, 1
	vand %v4, %v0, %v4
	lxvd2x 37, %r11, %r8
	vxor %v5, %v5, %v4
	stxvd2x 37, %r11, %r8
	addi %r11, %r11, 16
	vperm %v4, %v1, %v1, %v14
	vsldoi %v1, %v1, %v1, 1
	vand %v4, %v0, %v4
	lxvd2x 37, %r11, %r8
	vxor %v5, %v5, %v4
	stxvd2x 37, %r11, %r8
	addi %r11, %r11, 16
	vperm %v4, %v1, %v1, %v14
	vsldoi %v1, %v1, %v1, 1
	vand %v4, %v0, %v4
	lxvd2x 37, %r11, %r8
	vxor %v5, %v5, %v4
	stxvd2x 37, %r11, %r8
	addi %r11, %r11, 16
	vperm %v4, %v1, %v1, %v14
	vsldoi %v1, %v1, %v1, 1
	vand %v4, %v0, %v4
	lxvd2x 37, %r11, %r8
	vxor %v5, %v5, %v4
	stxvd2x 37, %r11, %r8
	addi %r11, %r11, 16
	vperm %v4, %v1, %v1, %v14
	vsldoi %v1, %v1, %v1, 1
	vand %v4, %v0, %v4
	lxvd2x 37, %r11, %r8
	vxor %v5, %v5, %v4
	stxvd2x 37, %r11, %r8
	addi %r11, %r11, 16
	vperm %v4, %v1, %v1, %v14
	vsldoi %v1, %v1, %v1, 1
	vand %v4, %v0, %v4
	lxvd2x 37, %r11, %r8
	vxor %v5, %v5, %v4
	stxvd2x 37, %r11, %r8
	addi %r11, %r11, 16
	vperm %v4, %v1, %v1, %v14
	vsldoi %v1, %v1, %v1, 1
	vand %v4, %v0, %v4
	lxvd2x 37, %r11, %r8
	vxor %v5, %v5, %v4
	stxvd2x 37, %r11, %r8
	addi %r11, %r11, 16
	vperm %v4, %v1, %v1, %v14
	vsldoi %v1, %v1, %v1, 1
	vand %v4, %v0, %v4
	lxvd2x 37, %r11, %r8
	vxor %v5, %v5, %v4
	stxvd2x 37, %r11, %r8
	addi %r11, %r11, 16
	vperm %v4, %v1, %v1, %v14
	vsldoi %v1, %v1, %v1, 1
	vand %v4, %v0, %v4
	lxvd2x 37, %r11, %r8
	vxor %v5, %v5, %v4
	stxvd2x 37, %r11, %r8
	addi %r11, %r11, 16
	vperm %v4, %v1, %v1, %v14
	vsldoi %v1, %v1, %v1, 1
	vand %v4, %v0, %v4
	lxvd2x 37, %r11, %r8
	vxor %v5, %v5, %v4
	stxvd2x 37, %r11, %r8
	addi %r11, %r11, 16
	add %r12, %r3, %r6
	stb %r10, 0(%r12)
	addi %r5, %r5, 1
	subf %r12, %r4, %r5
	addi %r0, %r12, -1
	xor %r0, %r0, %r12
	rldicl %r12, %r0, 1, 63
	addi %r12, %r12, -1
	and %r5, %r5, %r12
	addi %r6, %r6, 1
	li %r12, 256
	subf %r12, %r12, %r6
	cmpldi %cr0, %r12, 0
	bne %cr0, 23b
	li %r12, 0
	stb %r12, 256(%r3)
	stb %r12, 257(%r3)
	li %r3, 0
	b 21f
20:
	li %r3, 1
21:
	blr

vg_rc4_apply:
	lbz %r6, 256(%r3)
	lbz %r7, 257(%r3)
	li %r8, 0
	cmpldi %cr0, %r5, 0
	beq %cr0, 20f
22:
	addi %r6, %r6, 1
	rldicr %r6, %r6, 56, 7
	rldicl %r6, %r6, 8, 56
	add %r12, %r3, %r6
	lbz %r0, 0(%r12)
	add %r7, %r7, %r0
	rldicr %r7, %r7, 56, 7
	rldicl %r7, %r7, 8, 56
	or %r9, %r7, %r7
	li %r0, 7
	xor %r12, %r9, %r0
	rldicr %r12, %r12, 56, 7
	mtvsrd 32, %r12
	rldicr %r12, %r9, 58, 5
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	mtvsrd 33, %r12
	rldicr %r12, %r9, 57, 6
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	mtvsrd 34, %r12
	rldicr %r12, %r9, 56, 7
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	mtvsrd 35, %r12
	li %r12, 16
	or %r11, %r3, %r3
	lxvd2x 36, %r11, %r8
	lxvd2x 37, %r11, %r12
	vperm %v6, %v4, %v5, %v0
	addi %r11, %r11, 32
	lxvd2x 36, %r11, %r8
	lxvd2x 37, %r11, %r12
	vperm %v7, %v4, %v5, %v0
	addi %r11, %r11, 32
	lxvd2x 36, %r11, %r8
	lxvd2x 37, %r11, %r12
	vperm %v8, %v4, %v5, %v0
	addi %r11, %r11, 32
	lxvd2x 36, %r11, %r8
	lxvd2x 37, %r11, %r12
	vperm %v9, %v4, %v5, %v0
	addi %r11, %r11, 32
	lxvd2x 36, %r11, %r8
	lxvd2x 37, %r11, %r12
	vperm %v10, %v4, %v5, %v0
	addi %r11, %r11, 32
	lxvd2x 36, %r11, %r8
	lxvd2x 37, %r11, %r12
	vperm %v11, %v4, %v5, %v0
	addi %r11, %r11, 32
	lxvd2x 36, %r11, %r8
	lxvd2x 37, %r11, %r12
	vperm %v12, %v4, %v5, %v0
	addi %r11, %r11, 32
	lxvd2x 36, %r11, %r8
	lxvd2x 37, %r11, %r12
	vperm %v13, %v4, %v5, %v0
	addi %r11, %r11, 32
	vsel %v6, %v6, %v7, %v1
	vsel %v8, %v8, %v9, %v1
	vsel %v6, %v6, %v8, %v2
	vsel %v10, %v10, %v11, %v1
	vsel %v12, %v12, %v13, %v1
	vsel %v10, %v10, %v12, %v2
	vsel %v6, %v6, %v10, %v3
	mfvsrd %r10, 38
	rldicl %r10, %r10, 8, 56
	add %r12, %r3, %r6
	lbz %r0, 0(%r12)
	xor %r0, %r0, %r10
	vxor %v14, %v14, %v14
	rldicr %r0, %r0, 56, 7
	mtvsrd 47, %r0
	vperm %v15, %v15, %v15, %v14
	rldicr %r0, %r9, 60, 3
	rldicl %r0, %r0, 4, 60
	li %r12, 7
	xor %r0, %r0, %r12
	subf %r0, %r0, %r8
	rldicr %r0, %r0, 60, 3
	rldicl %r0, %r0, 4, 60
	li %r12, 255
	rldicr %r12, %r12, 56, 7
	mtvsrd 32, %r12
	vsldoi %v0, %v14, %v0, 8
	vsldoi %v0, %v0, %v14, 8
	rldicr %r12, %r0, 63, 0
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	mtvsrd 34, %r12
	vperm %v2, %v2, %v2, %v14
	vsldoi %v3, %v0, %v0, 1
	vsel %v0, %v0, %v3, %v2
	rldicr %r12, %r0, 62, 1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	mtvsrd 34, %r12
	vperm %v2, %v2, %v2, %v14
	vsldoi %v3, %v0, %v0, 2
	vsel %v0, %v0, %v3, %v2
	rldicr %r12, %r0, 61, 2
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	mtvsrd 34, %r12
	vperm %v2, %v2, %v2, %v14
	vsldoi %v3, %v0, %v0, 4
	vsel %v0, %v0, %v3, %v2
	rldicr %r12, %r0, 60, 3
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	mtvsrd 34, %r12
	vperm %v2, %v2, %v2, %v14
	vsldoi %v3, %v0, %v0, 8
	vsel %v0, %v0, %v3, %v2
	vand %v0, %v0, %v15
	rldicl %r0, %r9, 60, 4
	subf %r0, %r0, %r8
	rldicr %r0, %r0, 60, 3
	rldicl %r0, %r0, 4, 60
	li %r12, 255
	rldicr %r12, %r12, 56, 7
	mtvsrd 33, %r12
	vsldoi %v1, %v14, %v1, 8
	vsldoi %v1, %v1, %v14, 8
	rldicr %r12, %r0, 63, 0
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	mtvsrd 34, %r12
	vperm %v2, %v2, %v2, %v14
	vsldoi %v3, %v1, %v1, 1
	vsel %v1, %v1, %v3, %v2
	rldicr %r12, %r0, 62, 1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	mtvsrd 34, %r12
	vperm %v2, %v2, %v2, %v14
	vsldoi %v3, %v1, %v1, 2
	vsel %v1, %v1, %v3, %v2
	rldicr %r12, %r0, 61, 2
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	mtvsrd 34, %r12
	vperm %v2, %v2, %v2, %v14
	vsldoi %v3, %v1, %v1, 4
	vsel %v1, %v1, %v3, %v2
	rldicr %r12, %r0, 60, 3
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	mtvsrd 34, %r12
	vperm %v2, %v2, %v2, %v14
	vsldoi %v3, %v1, %v1, 8
	vsel %v1, %v1, %v3, %v2
	or %r11, %r3, %r3
	vperm %v4, %v1, %v1, %v14
	vsldoi %v1, %v1, %v1, 1
	vand %v4, %v0, %v4
	lxvd2x 37, %r11, %r8
	vxor %v5, %v5, %v4
	stxvd2x 37, %r11, %r8
	addi %r11, %r11, 16
	vperm %v4, %v1, %v1, %v14
	vsldoi %v1, %v1, %v1, 1
	vand %v4, %v0, %v4
	lxvd2x 37, %r11, %r8
	vxor %v5, %v5, %v4
	stxvd2x 37, %r11, %r8
	addi %r11, %r11, 16
	vperm %v4, %v1, %v1, %v14
	vsldoi %v1, %v1, %v1, 1
	vand %v4, %v0, %v4
	lxvd2x 37, %r11, %r8
	vxor %v5, %v5, %v4
	stxvd2x 37, %r11, %r8
	addi %r11, %r11, 16
	vperm %v4, %v1, %v1, %v14
	vsldoi %v1, %v1, %v1, 1
	vand %v4, %v0, %v4
	lxvd2x 37, %r11, %r8
	vxor %v5, %v5, %v4
	stxvd2x 37, %r11, %r8
	addi %r11, %r11, 16
	vperm %v4, %v1, %v1, %v14
	vsldoi %v1, %v1, %v1, 1
	vand %v4, %v0, %v4
	lxvd2x 37, %r11, %r8
	vxor %v5, %v5, %v4
	stxvd2x 37, %r11, %r8
	addi %r11, %r11, 16
	vperm %v4, %v1, %v1, %v14
	vsldoi %v1, %v1, %v1, 1
	vand %v4, %v0, %v4
	lxvd2x 37, %r11, %r8
	vxor %v5, %v5, %v4
	stxvd2x 37, %r11, %r8
	addi %r11, %r11, 16
	vperm %v4, %v1, %v1, %v14
	vsldoi %v1, %v1, %v1, 1
	vand %v4, %v0, %v4
	lxvd2x 37, %r11, %r8
	vxor %v5, %v5, %v4
	stxvd2x 37, %r11, %r8
	addi %r11, %r11, 16
	vperm %v4, %v1, %v1, %v14
	vsldoi %v1, %v1, %v1, 1
	vand %v4, %v0, %v4
	lxvd2x 37, %r11, %r8
	vxor %v5, %v5, %v4
	stxvd2x 37, %r11, %r8
	addi %r11, %r11, 16
	vperm %v4, %v1, %v1, %v14
	vsldoi %v1, %v1, %v1, 1
	vand %v4, %v0, %v4
	lxvd2x 37, %r11, %r8
	vxor %v5, %v5, %v4
	stxvd2x 37, %r11, %r8
	addi %r11, %r11, 16
	vperm %v4, %v1, %v1, %v14
	vsldoi %v1, %v1, %v1, 1
	vand %v4, %v0, %v4
	lxvd2x 37, %r11, %r8
	vxor %v5, %v5, %v4
	stxvd2x 37, %r11, %r8
	addi %r11, %r11, 16
	vperm %v4, %v1, %v1, %v14
	vsldoi %v1, %v1, %v1, 1
	vand %v4, %v0, %v4
	lxvd2x 37, %r11, %r8
	vxor %v5, %v5, %v4
	stxvd2x 37, %r11, %r8
	addi %r11, %r11, 16
	vperm %v4, %v1, %v1, %v14
	vsldoi %v1, %v1, %v1, 1
	vand %v4, %v0, %v4
	lxvd2x 37, %r11, %r8
	vxor %v5, %v5, %v4
	stxvd2x 37, %r11, %r8
	addi %r11, %r11, 16
	vperm %v4, %v1, %v1, %v14
	vsldoi %v1, %v1, %v1, 1
	vand %v4, %v0, %v4
	lxvd2x 37, %r11, %r8
	vxor %v5, %v5, %v4
	stxvd2x 37, %r11, %r8
	addi %r11, %r11, 16
	vperm %v4, %v1, %v1, %v14
	vsldoi %v1, %v1, %v1, 1
	vand %v4, %v0, %v4
	lxvd2x 37, %r11, %r8
	vxor %v5, %v5, %v4
	stxvd2x 37, %r11, %r8
	addi %r11, %r11, 16
	vperm %v4, %v1, %v1, %v14
	vsldoi %v1, %v1, %v1, 1
	vand %v4, %v0, %v4
	lxvd2x 37, %r11, %r8
	vxor %v5, %v5, %v4
	stxvd2x 37, %r11, %r8
	addi %r11, %r11, 16
	vperm %v4, %v1, %v1, %v14
	vsldoi %v1, %v1, %v1, 1
	vand %v4, %v0, %v4
	lxvd2x 37, %r11, %r8
	vxor %v5, %v5, %v4
	stxvd2x 37, %r11, %r8
	addi %r11, %r11, 16
	add %r12, %r3, %r6
	lbz %r0, 0(%r12)
	stb %r10, 0(%r12)
	add %r9, %r10, %r0
	rldicr %r9, %r9, 56, 7
	rldicl %r9, %r9, 8, 56
	li %r0, 7
	xor %r12, %r9, %r0
	rldicr %r12, %r12, 56, 7
	mtvsrd 32, %r12
	rldicr %r12, %r9, 58, 5
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	mtvsrd 33, %r12
	rldicr %r12, %r9, 57, 6
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	mtvsrd 34, %r12
	rldicr %r12, %r9, 56, 7
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	mtvsrd 35, %r12
	li %r12, 16
	or %r11, %r3, %r3
	lxvd2x 36, %r11, %r8
	lxvd2x 37, %r11, %r12
	vperm %v6, %v4, %v5, %v0
	addi %r11, %r11, 32
	lxvd2x 36, %r11, %r8
	lxvd2x 37, %r11, %r12
	vperm %v7, %v4, %v5, %v0
	addi %r11, %r11, 32
	lxvd2x 36, %r11, %r8
	lxvd2x 37, %r11, %r12
	vperm %v8, %v4, %v5, %v0
	addi %r11, %r11, 32
	lxvd2x 36, %r11, %r8
	lxvd2x 37, %r11, %r12
	vperm %v9, %v4, %v5, %v0
	addi %r11, %r11, 32
	lxvd2x 36, %r11, %r8
	lxvd2x 37, %r11, %r12
	vperm %v10, %v4, %v5, %v0
	addi %r11, %r11, 32
	lxvd2x 36, %r11, %r8
	lxvd2x 37, %r11, %r12
	vperm %v11, %v4, %v5, %v0
	addi %r11, %r11, 32
	lxvd2x 36, %r11, %r8
	lxvd2x 37, %r11, %r12
	vperm %v12, %v4, %v5, %v0
	addi %r11, %r11, 32
	lxvd2x 36, %r11, %r8
	lxvd2x 37, %r11, %r12
	vperm %v13, %v4, %v5, %v0
	addi %r11, %r11, 32
	vsel %v6, %v6, %v7, %v1
	vsel %v8, %v8, %v9, %v1
	vsel %v6, %v6, %v8, %v2
	vsel %v10, %v10, %v11, %v1
	vsel %v12, %v12, %v13, %v1
	vsel %v10, %v10, %v12, %v2
	vsel %v6, %v6, %v10, %v3
	mfvsrd %r10, 38
	rldicl %r10, %r10, 8, 56
	lbz %r0, 0(%r4)
	xor %r0, %r0, %r10
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 22b
	stb %r6, 256(%r3)
	stb %r7, 257(%r3)
	b 21f
20:
21:
	blr
