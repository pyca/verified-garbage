// The functions of `src/internal/vg_camellia_serial_crypt.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_camellia_serial_crypt:
	mflr %r0
	bcl 20, 31, 2f
2:
	mflr %r10
	addis %r10, %r10, ({VG_CAMELLIA_PPC64LE_AFFINE}
	addi %r10, %r10, ({VG_CAMELLIA_PPC64LE_AFFINE}
	mtlr %r0
	li %r11, 0
	lxvd2x 40, %r10, %r11
	li %r11, 16
	lxvd2x 41, %r10, %r11
	li %r11, 32
	lxvd2x 42, %r10, %r11
	li %r11, 48
	lxvd2x 43, %r10, %r11
	li %r11, 64
	lxvd2x 44, %r10, %r11
	li %r11, 80
	lxvd2x 45, %r10, %r11
	li %r11, 96
	lxvd2x 46, %r10, %r11
	li %r11, 112
	lxvd2x 47, %r10, %r11
	li %r11, 128
	lxvd2x 48, %r10, %r11
	li %r11, 144
	lxvd2x 49, %r10, %r11
	li %r11, 160
	lxvd2x 50, %r10, %r11
	li %r11, 176
	lxvd2x 51, %r10, %r11
	li %r11, 192
	lxvd2x 39, %r10, %r11
	li %r11, 208
	lxvd2x 32, %r10, %r11
	mfvsrd %r12, 32
	li %r0, 3088
	ldbrx %r6, %r5, %r0
	li %r0, 3096
	ldbrx %r7, %r5, %r0
	li %r0, 0
	ldbrx %r4, %r3, %r0
	xor %r6, %r6, %r4
	li %r0, 8
	ldbrx %r4, %r3, %r0
	xor %r7, %r7, %r4
	li %r0, 16
	ldbrx %r4, %r3, %r0
	xor %r8, %r6, %r4
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v0, %v0, %v18
	vor %v1, %v1, %v18
	vperm %v0, %v8, %v9, %v0
	vperm %v1, %v10, %v11, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r8, 32
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v2, %v0, %v19
	vor %v3, %v1, %v19
	vperm %v2, %v12, %v13, %v2
	vperm %v3, %v14, %v15, %v3
	vxor %v2, %v2, %v3
	vperm %v0, %v16, %v16, %v0
	vperm %v1, %v17, %v17, %v1
	vxor %v0, %v0, %v1
	vsel %v0, %v2, %v0, %v7
	mfvsrd %r8, 32
	rldicl %r9, %r8, 32, 32
	rlwinm %r10, %r8, 0, 0, 31
	rlwinm %r11, %r9, 24, 0, 31
	xor %r11, %r9, %r11
	rlwinm %r4, %r9, 16, 0, 31
	xor %r11, %r11, %r4
	rlwinm %r4, %r10, 24, 0, 31
	rlwinm %r0, %r10, 16, 0, 31
	xor %r4, %r4, %r0
	rlwinm %r0, %r10, 8, 0, 31
	xor %r4, %r4, %r0
	xor %r11, %r11, %r4
	rlwinm %r0, %r9, 8, 0, 31
	xor %r10, %r9, %r0
	xor %r10, %r10, %r4
	rldicr %r11, %r11, 32, 31
	or %r8, %r11, %r10
	xor %r7, %r7, %r8
	li %r0, 24
	ldbrx %r4, %r3, %r0
	xor %r8, %r7, %r4
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v0, %v0, %v18
	vor %v1, %v1, %v18
	vperm %v0, %v8, %v9, %v0
	vperm %v1, %v10, %v11, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r8, 32
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v2, %v0, %v19
	vor %v3, %v1, %v19
	vperm %v2, %v12, %v13, %v2
	vperm %v3, %v14, %v15, %v3
	vxor %v2, %v2, %v3
	vperm %v0, %v16, %v16, %v0
	vperm %v1, %v17, %v17, %v1
	vxor %v0, %v0, %v1
	vsel %v0, %v2, %v0, %v7
	mfvsrd %r8, 32
	rldicl %r9, %r8, 32, 32
	rlwinm %r10, %r8, 0, 0, 31
	rlwinm %r11, %r9, 24, 0, 31
	xor %r11, %r9, %r11
	rlwinm %r4, %r9, 16, 0, 31
	xor %r11, %r11, %r4
	rlwinm %r4, %r10, 24, 0, 31
	rlwinm %r0, %r10, 16, 0, 31
	xor %r4, %r4, %r0
	rlwinm %r0, %r10, 8, 0, 31
	xor %r4, %r4, %r0
	xor %r11, %r11, %r4
	rlwinm %r0, %r9, 8, 0, 31
	xor %r10, %r9, %r0
	xor %r10, %r10, %r4
	rldicr %r11, %r11, 32, 31
	or %r8, %r11, %r10
	xor %r6, %r6, %r8
	li %r0, 32
	ldbrx %r4, %r3, %r0
	xor %r8, %r6, %r4
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v0, %v0, %v18
	vor %v1, %v1, %v18
	vperm %v0, %v8, %v9, %v0
	vperm %v1, %v10, %v11, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r8, 32
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v2, %v0, %v19
	vor %v3, %v1, %v19
	vperm %v2, %v12, %v13, %v2
	vperm %v3, %v14, %v15, %v3
	vxor %v2, %v2, %v3
	vperm %v0, %v16, %v16, %v0
	vperm %v1, %v17, %v17, %v1
	vxor %v0, %v0, %v1
	vsel %v0, %v2, %v0, %v7
	mfvsrd %r8, 32
	rldicl %r9, %r8, 32, 32
	rlwinm %r10, %r8, 0, 0, 31
	rlwinm %r11, %r9, 24, 0, 31
	xor %r11, %r9, %r11
	rlwinm %r4, %r9, 16, 0, 31
	xor %r11, %r11, %r4
	rlwinm %r4, %r10, 24, 0, 31
	rlwinm %r0, %r10, 16, 0, 31
	xor %r4, %r4, %r0
	rlwinm %r0, %r10, 8, 0, 31
	xor %r4, %r4, %r0
	xor %r11, %r11, %r4
	rlwinm %r0, %r9, 8, 0, 31
	xor %r10, %r9, %r0
	xor %r10, %r10, %r4
	rldicr %r11, %r11, 32, 31
	or %r8, %r11, %r10
	xor %r7, %r7, %r8
	li %r0, 40
	ldbrx %r4, %r3, %r0
	xor %r8, %r7, %r4
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v0, %v0, %v18
	vor %v1, %v1, %v18
	vperm %v0, %v8, %v9, %v0
	vperm %v1, %v10, %v11, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r8, 32
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v2, %v0, %v19
	vor %v3, %v1, %v19
	vperm %v2, %v12, %v13, %v2
	vperm %v3, %v14, %v15, %v3
	vxor %v2, %v2, %v3
	vperm %v0, %v16, %v16, %v0
	vperm %v1, %v17, %v17, %v1
	vxor %v0, %v0, %v1
	vsel %v0, %v2, %v0, %v7
	mfvsrd %r8, 32
	rldicl %r9, %r8, 32, 32
	rlwinm %r10, %r8, 0, 0, 31
	rlwinm %r11, %r9, 24, 0, 31
	xor %r11, %r9, %r11
	rlwinm %r4, %r9, 16, 0, 31
	xor %r11, %r11, %r4
	rlwinm %r4, %r10, 24, 0, 31
	rlwinm %r0, %r10, 16, 0, 31
	xor %r4, %r4, %r0
	rlwinm %r0, %r10, 8, 0, 31
	xor %r4, %r4, %r0
	xor %r11, %r11, %r4
	rlwinm %r0, %r9, 8, 0, 31
	xor %r10, %r9, %r0
	xor %r10, %r10, %r4
	rldicr %r11, %r11, 32, 31
	or %r8, %r11, %r10
	xor %r6, %r6, %r8
	li %r0, 48
	ldbrx %r4, %r3, %r0
	xor %r8, %r6, %r4
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v0, %v0, %v18
	vor %v1, %v1, %v18
	vperm %v0, %v8, %v9, %v0
	vperm %v1, %v10, %v11, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r8, 32
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v2, %v0, %v19
	vor %v3, %v1, %v19
	vperm %v2, %v12, %v13, %v2
	vperm %v3, %v14, %v15, %v3
	vxor %v2, %v2, %v3
	vperm %v0, %v16, %v16, %v0
	vperm %v1, %v17, %v17, %v1
	vxor %v0, %v0, %v1
	vsel %v0, %v2, %v0, %v7
	mfvsrd %r8, 32
	rldicl %r9, %r8, 32, 32
	rlwinm %r10, %r8, 0, 0, 31
	rlwinm %r11, %r9, 24, 0, 31
	xor %r11, %r9, %r11
	rlwinm %r4, %r9, 16, 0, 31
	xor %r11, %r11, %r4
	rlwinm %r4, %r10, 24, 0, 31
	rlwinm %r0, %r10, 16, 0, 31
	xor %r4, %r4, %r0
	rlwinm %r0, %r10, 8, 0, 31
	xor %r4, %r4, %r0
	xor %r11, %r11, %r4
	rlwinm %r0, %r9, 8, 0, 31
	xor %r10, %r9, %r0
	xor %r10, %r10, %r4
	rldicr %r11, %r11, 32, 31
	or %r8, %r11, %r10
	xor %r7, %r7, %r8
	li %r0, 56
	ldbrx %r4, %r3, %r0
	xor %r8, %r7, %r4
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v0, %v0, %v18
	vor %v1, %v1, %v18
	vperm %v0, %v8, %v9, %v0
	vperm %v1, %v10, %v11, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r8, 32
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v2, %v0, %v19
	vor %v3, %v1, %v19
	vperm %v2, %v12, %v13, %v2
	vperm %v3, %v14, %v15, %v3
	vxor %v2, %v2, %v3
	vperm %v0, %v16, %v16, %v0
	vperm %v1, %v17, %v17, %v1
	vxor %v0, %v0, %v1
	vsel %v0, %v2, %v0, %v7
	mfvsrd %r8, 32
	rldicl %r9, %r8, 32, 32
	rlwinm %r10, %r8, 0, 0, 31
	rlwinm %r11, %r9, 24, 0, 31
	xor %r11, %r9, %r11
	rlwinm %r4, %r9, 16, 0, 31
	xor %r11, %r11, %r4
	rlwinm %r4, %r10, 24, 0, 31
	rlwinm %r0, %r10, 16, 0, 31
	xor %r4, %r4, %r0
	rlwinm %r0, %r10, 8, 0, 31
	xor %r4, %r4, %r0
	xor %r11, %r11, %r4
	rlwinm %r0, %r9, 8, 0, 31
	xor %r10, %r9, %r0
	xor %r10, %r10, %r4
	rldicr %r11, %r11, 32, 31
	or %r8, %r11, %r10
	xor %r6, %r6, %r8
	li %r0, 64
	ldbrx %r4, %r3, %r0
	rldicl %r9, %r6, 32, 32
	rlwinm %r10, %r6, 0, 0, 31
	rldicl %r11, %r4, 32, 32
	rlwinm %r4, %r4, 0, 0, 31
	and %r0, %r9, %r11
	rlwinm %r0, %r0, 1, 0, 31
	xor %r10, %r10, %r0
	or %r0, %r10, %r4
	xor %r9, %r9, %r0
	rldicr %r9, %r9, 32, 31
	or %r6, %r9, %r10
	li %r0, 72
	ldbrx %r4, %r3, %r0
	rldicl %r9, %r7, 32, 32
	rlwinm %r10, %r7, 0, 0, 31
	rldicl %r11, %r4, 32, 32
	rlwinm %r4, %r4, 0, 0, 31
	or %r0, %r10, %r4
	xor %r9, %r9, %r0
	and %r0, %r9, %r11
	rlwinm %r0, %r0, 1, 0, 31
	xor %r10, %r10, %r0
	rldicr %r9, %r9, 32, 31
	or %r7, %r9, %r10
	li %r0, 80
	ldbrx %r4, %r3, %r0
	xor %r8, %r6, %r4
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v0, %v0, %v18
	vor %v1, %v1, %v18
	vperm %v0, %v8, %v9, %v0
	vperm %v1, %v10, %v11, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r8, 32
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v2, %v0, %v19
	vor %v3, %v1, %v19
	vperm %v2, %v12, %v13, %v2
	vperm %v3, %v14, %v15, %v3
	vxor %v2, %v2, %v3
	vperm %v0, %v16, %v16, %v0
	vperm %v1, %v17, %v17, %v1
	vxor %v0, %v0, %v1
	vsel %v0, %v2, %v0, %v7
	mfvsrd %r8, 32
	rldicl %r9, %r8, 32, 32
	rlwinm %r10, %r8, 0, 0, 31
	rlwinm %r11, %r9, 24, 0, 31
	xor %r11, %r9, %r11
	rlwinm %r4, %r9, 16, 0, 31
	xor %r11, %r11, %r4
	rlwinm %r4, %r10, 24, 0, 31
	rlwinm %r0, %r10, 16, 0, 31
	xor %r4, %r4, %r0
	rlwinm %r0, %r10, 8, 0, 31
	xor %r4, %r4, %r0
	xor %r11, %r11, %r4
	rlwinm %r0, %r9, 8, 0, 31
	xor %r10, %r9, %r0
	xor %r10, %r10, %r4
	rldicr %r11, %r11, 32, 31
	or %r8, %r11, %r10
	xor %r7, %r7, %r8
	li %r0, 88
	ldbrx %r4, %r3, %r0
	xor %r8, %r7, %r4
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v0, %v0, %v18
	vor %v1, %v1, %v18
	vperm %v0, %v8, %v9, %v0
	vperm %v1, %v10, %v11, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r8, 32
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v2, %v0, %v19
	vor %v3, %v1, %v19
	vperm %v2, %v12, %v13, %v2
	vperm %v3, %v14, %v15, %v3
	vxor %v2, %v2, %v3
	vperm %v0, %v16, %v16, %v0
	vperm %v1, %v17, %v17, %v1
	vxor %v0, %v0, %v1
	vsel %v0, %v2, %v0, %v7
	mfvsrd %r8, 32
	rldicl %r9, %r8, 32, 32
	rlwinm %r10, %r8, 0, 0, 31
	rlwinm %r11, %r9, 24, 0, 31
	xor %r11, %r9, %r11
	rlwinm %r4, %r9, 16, 0, 31
	xor %r11, %r11, %r4
	rlwinm %r4, %r10, 24, 0, 31
	rlwinm %r0, %r10, 16, 0, 31
	xor %r4, %r4, %r0
	rlwinm %r0, %r10, 8, 0, 31
	xor %r4, %r4, %r0
	xor %r11, %r11, %r4
	rlwinm %r0, %r9, 8, 0, 31
	xor %r10, %r9, %r0
	xor %r10, %r10, %r4
	rldicr %r11, %r11, 32, 31
	or %r8, %r11, %r10
	xor %r6, %r6, %r8
	li %r0, 96
	ldbrx %r4, %r3, %r0
	xor %r8, %r6, %r4
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v0, %v0, %v18
	vor %v1, %v1, %v18
	vperm %v0, %v8, %v9, %v0
	vperm %v1, %v10, %v11, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r8, 32
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v2, %v0, %v19
	vor %v3, %v1, %v19
	vperm %v2, %v12, %v13, %v2
	vperm %v3, %v14, %v15, %v3
	vxor %v2, %v2, %v3
	vperm %v0, %v16, %v16, %v0
	vperm %v1, %v17, %v17, %v1
	vxor %v0, %v0, %v1
	vsel %v0, %v2, %v0, %v7
	mfvsrd %r8, 32
	rldicl %r9, %r8, 32, 32
	rlwinm %r10, %r8, 0, 0, 31
	rlwinm %r11, %r9, 24, 0, 31
	xor %r11, %r9, %r11
	rlwinm %r4, %r9, 16, 0, 31
	xor %r11, %r11, %r4
	rlwinm %r4, %r10, 24, 0, 31
	rlwinm %r0, %r10, 16, 0, 31
	xor %r4, %r4, %r0
	rlwinm %r0, %r10, 8, 0, 31
	xor %r4, %r4, %r0
	xor %r11, %r11, %r4
	rlwinm %r0, %r9, 8, 0, 31
	xor %r10, %r9, %r0
	xor %r10, %r10, %r4
	rldicr %r11, %r11, 32, 31
	or %r8, %r11, %r10
	xor %r7, %r7, %r8
	li %r0, 104
	ldbrx %r4, %r3, %r0
	xor %r8, %r7, %r4
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v0, %v0, %v18
	vor %v1, %v1, %v18
	vperm %v0, %v8, %v9, %v0
	vperm %v1, %v10, %v11, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r8, 32
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v2, %v0, %v19
	vor %v3, %v1, %v19
	vperm %v2, %v12, %v13, %v2
	vperm %v3, %v14, %v15, %v3
	vxor %v2, %v2, %v3
	vperm %v0, %v16, %v16, %v0
	vperm %v1, %v17, %v17, %v1
	vxor %v0, %v0, %v1
	vsel %v0, %v2, %v0, %v7
	mfvsrd %r8, 32
	rldicl %r9, %r8, 32, 32
	rlwinm %r10, %r8, 0, 0, 31
	rlwinm %r11, %r9, 24, 0, 31
	xor %r11, %r9, %r11
	rlwinm %r4, %r9, 16, 0, 31
	xor %r11, %r11, %r4
	rlwinm %r4, %r10, 24, 0, 31
	rlwinm %r0, %r10, 16, 0, 31
	xor %r4, %r4, %r0
	rlwinm %r0, %r10, 8, 0, 31
	xor %r4, %r4, %r0
	xor %r11, %r11, %r4
	rlwinm %r0, %r9, 8, 0, 31
	xor %r10, %r9, %r0
	xor %r10, %r10, %r4
	rldicr %r11, %r11, 32, 31
	or %r8, %r11, %r10
	xor %r6, %r6, %r8
	li %r0, 112
	ldbrx %r4, %r3, %r0
	xor %r8, %r6, %r4
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v0, %v0, %v18
	vor %v1, %v1, %v18
	vperm %v0, %v8, %v9, %v0
	vperm %v1, %v10, %v11, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r8, 32
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v2, %v0, %v19
	vor %v3, %v1, %v19
	vperm %v2, %v12, %v13, %v2
	vperm %v3, %v14, %v15, %v3
	vxor %v2, %v2, %v3
	vperm %v0, %v16, %v16, %v0
	vperm %v1, %v17, %v17, %v1
	vxor %v0, %v0, %v1
	vsel %v0, %v2, %v0, %v7
	mfvsrd %r8, 32
	rldicl %r9, %r8, 32, 32
	rlwinm %r10, %r8, 0, 0, 31
	rlwinm %r11, %r9, 24, 0, 31
	xor %r11, %r9, %r11
	rlwinm %r4, %r9, 16, 0, 31
	xor %r11, %r11, %r4
	rlwinm %r4, %r10, 24, 0, 31
	rlwinm %r0, %r10, 16, 0, 31
	xor %r4, %r4, %r0
	rlwinm %r0, %r10, 8, 0, 31
	xor %r4, %r4, %r0
	xor %r11, %r11, %r4
	rlwinm %r0, %r9, 8, 0, 31
	xor %r10, %r9, %r0
	xor %r10, %r10, %r4
	rldicr %r11, %r11, 32, 31
	or %r8, %r11, %r10
	xor %r7, %r7, %r8
	li %r0, 120
	ldbrx %r4, %r3, %r0
	xor %r8, %r7, %r4
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v0, %v0, %v18
	vor %v1, %v1, %v18
	vperm %v0, %v8, %v9, %v0
	vperm %v1, %v10, %v11, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r8, 32
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v2, %v0, %v19
	vor %v3, %v1, %v19
	vperm %v2, %v12, %v13, %v2
	vperm %v3, %v14, %v15, %v3
	vxor %v2, %v2, %v3
	vperm %v0, %v16, %v16, %v0
	vperm %v1, %v17, %v17, %v1
	vxor %v0, %v0, %v1
	vsel %v0, %v2, %v0, %v7
	mfvsrd %r8, 32
	rldicl %r9, %r8, 32, 32
	rlwinm %r10, %r8, 0, 0, 31
	rlwinm %r11, %r9, 24, 0, 31
	xor %r11, %r9, %r11
	rlwinm %r4, %r9, 16, 0, 31
	xor %r11, %r11, %r4
	rlwinm %r4, %r10, 24, 0, 31
	rlwinm %r0, %r10, 16, 0, 31
	xor %r4, %r4, %r0
	rlwinm %r0, %r10, 8, 0, 31
	xor %r4, %r4, %r0
	xor %r11, %r11, %r4
	rlwinm %r0, %r9, 8, 0, 31
	xor %r10, %r9, %r0
	xor %r10, %r10, %r4
	rldicr %r11, %r11, 32, 31
	or %r8, %r11, %r10
	xor %r6, %r6, %r8
	li %r0, 128
	ldbrx %r4, %r3, %r0
	rldicl %r9, %r6, 32, 32
	rlwinm %r10, %r6, 0, 0, 31
	rldicl %r11, %r4, 32, 32
	rlwinm %r4, %r4, 0, 0, 31
	and %r0, %r9, %r11
	rlwinm %r0, %r0, 1, 0, 31
	xor %r10, %r10, %r0
	or %r0, %r10, %r4
	xor %r9, %r9, %r0
	rldicr %r9, %r9, 32, 31
	or %r6, %r9, %r10
	li %r0, 136
	ldbrx %r4, %r3, %r0
	rldicl %r9, %r7, 32, 32
	rlwinm %r10, %r7, 0, 0, 31
	rldicl %r11, %r4, 32, 32
	rlwinm %r4, %r4, 0, 0, 31
	or %r0, %r10, %r4
	xor %r9, %r9, %r0
	and %r0, %r9, %r11
	rlwinm %r0, %r0, 1, 0, 31
	xor %r10, %r10, %r0
	rldicr %r9, %r9, 32, 31
	or %r7, %r9, %r10
	li %r0, 144
	ldbrx %r4, %r3, %r0
	xor %r8, %r6, %r4
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v0, %v0, %v18
	vor %v1, %v1, %v18
	vperm %v0, %v8, %v9, %v0
	vperm %v1, %v10, %v11, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r8, 32
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v2, %v0, %v19
	vor %v3, %v1, %v19
	vperm %v2, %v12, %v13, %v2
	vperm %v3, %v14, %v15, %v3
	vxor %v2, %v2, %v3
	vperm %v0, %v16, %v16, %v0
	vperm %v1, %v17, %v17, %v1
	vxor %v0, %v0, %v1
	vsel %v0, %v2, %v0, %v7
	mfvsrd %r8, 32
	rldicl %r9, %r8, 32, 32
	rlwinm %r10, %r8, 0, 0, 31
	rlwinm %r11, %r9, 24, 0, 31
	xor %r11, %r9, %r11
	rlwinm %r4, %r9, 16, 0, 31
	xor %r11, %r11, %r4
	rlwinm %r4, %r10, 24, 0, 31
	rlwinm %r0, %r10, 16, 0, 31
	xor %r4, %r4, %r0
	rlwinm %r0, %r10, 8, 0, 31
	xor %r4, %r4, %r0
	xor %r11, %r11, %r4
	rlwinm %r0, %r9, 8, 0, 31
	xor %r10, %r9, %r0
	xor %r10, %r10, %r4
	rldicr %r11, %r11, 32, 31
	or %r8, %r11, %r10
	xor %r7, %r7, %r8
	li %r0, 152
	ldbrx %r4, %r3, %r0
	xor %r8, %r7, %r4
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v0, %v0, %v18
	vor %v1, %v1, %v18
	vperm %v0, %v8, %v9, %v0
	vperm %v1, %v10, %v11, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r8, 32
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v2, %v0, %v19
	vor %v3, %v1, %v19
	vperm %v2, %v12, %v13, %v2
	vperm %v3, %v14, %v15, %v3
	vxor %v2, %v2, %v3
	vperm %v0, %v16, %v16, %v0
	vperm %v1, %v17, %v17, %v1
	vxor %v0, %v0, %v1
	vsel %v0, %v2, %v0, %v7
	mfvsrd %r8, 32
	rldicl %r9, %r8, 32, 32
	rlwinm %r10, %r8, 0, 0, 31
	rlwinm %r11, %r9, 24, 0, 31
	xor %r11, %r9, %r11
	rlwinm %r4, %r9, 16, 0, 31
	xor %r11, %r11, %r4
	rlwinm %r4, %r10, 24, 0, 31
	rlwinm %r0, %r10, 16, 0, 31
	xor %r4, %r4, %r0
	rlwinm %r0, %r10, 8, 0, 31
	xor %r4, %r4, %r0
	xor %r11, %r11, %r4
	rlwinm %r0, %r9, 8, 0, 31
	xor %r10, %r9, %r0
	xor %r10, %r10, %r4
	rldicr %r11, %r11, 32, 31
	or %r8, %r11, %r10
	xor %r6, %r6, %r8
	li %r0, 160
	ldbrx %r4, %r3, %r0
	xor %r8, %r6, %r4
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v0, %v0, %v18
	vor %v1, %v1, %v18
	vperm %v0, %v8, %v9, %v0
	vperm %v1, %v10, %v11, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r8, 32
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v2, %v0, %v19
	vor %v3, %v1, %v19
	vperm %v2, %v12, %v13, %v2
	vperm %v3, %v14, %v15, %v3
	vxor %v2, %v2, %v3
	vperm %v0, %v16, %v16, %v0
	vperm %v1, %v17, %v17, %v1
	vxor %v0, %v0, %v1
	vsel %v0, %v2, %v0, %v7
	mfvsrd %r8, 32
	rldicl %r9, %r8, 32, 32
	rlwinm %r10, %r8, 0, 0, 31
	rlwinm %r11, %r9, 24, 0, 31
	xor %r11, %r9, %r11
	rlwinm %r4, %r9, 16, 0, 31
	xor %r11, %r11, %r4
	rlwinm %r4, %r10, 24, 0, 31
	rlwinm %r0, %r10, 16, 0, 31
	xor %r4, %r4, %r0
	rlwinm %r0, %r10, 8, 0, 31
	xor %r4, %r4, %r0
	xor %r11, %r11, %r4
	rlwinm %r0, %r9, 8, 0, 31
	xor %r10, %r9, %r0
	xor %r10, %r10, %r4
	rldicr %r11, %r11, 32, 31
	or %r8, %r11, %r10
	xor %r7, %r7, %r8
	li %r0, 168
	ldbrx %r4, %r3, %r0
	xor %r8, %r7, %r4
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v0, %v0, %v18
	vor %v1, %v1, %v18
	vperm %v0, %v8, %v9, %v0
	vperm %v1, %v10, %v11, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r8, 32
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v2, %v0, %v19
	vor %v3, %v1, %v19
	vperm %v2, %v12, %v13, %v2
	vperm %v3, %v14, %v15, %v3
	vxor %v2, %v2, %v3
	vperm %v0, %v16, %v16, %v0
	vperm %v1, %v17, %v17, %v1
	vxor %v0, %v0, %v1
	vsel %v0, %v2, %v0, %v7
	mfvsrd %r8, 32
	rldicl %r9, %r8, 32, 32
	rlwinm %r10, %r8, 0, 0, 31
	rlwinm %r11, %r9, 24, 0, 31
	xor %r11, %r9, %r11
	rlwinm %r4, %r9, 16, 0, 31
	xor %r11, %r11, %r4
	rlwinm %r4, %r10, 24, 0, 31
	rlwinm %r0, %r10, 16, 0, 31
	xor %r4, %r4, %r0
	rlwinm %r0, %r10, 8, 0, 31
	xor %r4, %r4, %r0
	xor %r11, %r11, %r4
	rlwinm %r0, %r9, 8, 0, 31
	xor %r10, %r9, %r0
	xor %r10, %r10, %r4
	rldicr %r11, %r11, 32, 31
	or %r8, %r11, %r10
	xor %r6, %r6, %r8
	li %r0, 176
	ldbrx %r4, %r3, %r0
	xor %r8, %r6, %r4
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v0, %v0, %v18
	vor %v1, %v1, %v18
	vperm %v0, %v8, %v9, %v0
	vperm %v1, %v10, %v11, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r8, 32
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v2, %v0, %v19
	vor %v3, %v1, %v19
	vperm %v2, %v12, %v13, %v2
	vperm %v3, %v14, %v15, %v3
	vxor %v2, %v2, %v3
	vperm %v0, %v16, %v16, %v0
	vperm %v1, %v17, %v17, %v1
	vxor %v0, %v0, %v1
	vsel %v0, %v2, %v0, %v7
	mfvsrd %r8, 32
	rldicl %r9, %r8, 32, 32
	rlwinm %r10, %r8, 0, 0, 31
	rlwinm %r11, %r9, 24, 0, 31
	xor %r11, %r9, %r11
	rlwinm %r4, %r9, 16, 0, 31
	xor %r11, %r11, %r4
	rlwinm %r4, %r10, 24, 0, 31
	rlwinm %r0, %r10, 16, 0, 31
	xor %r4, %r4, %r0
	rlwinm %r0, %r10, 8, 0, 31
	xor %r4, %r4, %r0
	xor %r11, %r11, %r4
	rlwinm %r0, %r9, 8, 0, 31
	xor %r10, %r9, %r0
	xor %r10, %r10, %r4
	rldicr %r11, %r11, 32, 31
	or %r8, %r11, %r10
	xor %r7, %r7, %r8
	li %r0, 184
	ldbrx %r4, %r3, %r0
	xor %r8, %r7, %r4
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v0, %v0, %v18
	vor %v1, %v1, %v18
	vperm %v0, %v8, %v9, %v0
	vperm %v1, %v10, %v11, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r8, 32
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v2, %v0, %v19
	vor %v3, %v1, %v19
	vperm %v2, %v12, %v13, %v2
	vperm %v3, %v14, %v15, %v3
	vxor %v2, %v2, %v3
	vperm %v0, %v16, %v16, %v0
	vperm %v1, %v17, %v17, %v1
	vxor %v0, %v0, %v1
	vsel %v0, %v2, %v0, %v7
	mfvsrd %r8, 32
	rldicl %r9, %r8, 32, 32
	rlwinm %r10, %r8, 0, 0, 31
	rlwinm %r11, %r9, 24, 0, 31
	xor %r11, %r9, %r11
	rlwinm %r4, %r9, 16, 0, 31
	xor %r11, %r11, %r4
	rlwinm %r4, %r10, 24, 0, 31
	rlwinm %r0, %r10, 16, 0, 31
	xor %r4, %r4, %r0
	rlwinm %r0, %r10, 8, 0, 31
	xor %r4, %r4, %r0
	xor %r11, %r11, %r4
	rlwinm %r0, %r9, 8, 0, 31
	xor %r10, %r9, %r0
	xor %r10, %r10, %r4
	rldicr %r11, %r11, 32, 31
	or %r8, %r11, %r10
	xor %r6, %r6, %r8
	addi %r9, %r28, -18
	cmpldi %cr0, %r9, 0
	beq %cr0, 20f
	li %r0, 192
	ldbrx %r4, %r3, %r0
	rldicl %r9, %r6, 32, 32
	rlwinm %r10, %r6, 0, 0, 31
	rldicl %r11, %r4, 32, 32
	rlwinm %r4, %r4, 0, 0, 31
	and %r0, %r9, %r11
	rlwinm %r0, %r0, 1, 0, 31
	xor %r10, %r10, %r0
	or %r0, %r10, %r4
	xor %r9, %r9, %r0
	rldicr %r9, %r9, 32, 31
	or %r6, %r9, %r10
	li %r0, 200
	ldbrx %r4, %r3, %r0
	rldicl %r9, %r7, 32, 32
	rlwinm %r10, %r7, 0, 0, 31
	rldicl %r11, %r4, 32, 32
	rlwinm %r4, %r4, 0, 0, 31
	or %r0, %r10, %r4
	xor %r9, %r9, %r0
	and %r0, %r9, %r11
	rlwinm %r0, %r0, 1, 0, 31
	xor %r10, %r10, %r0
	rldicr %r9, %r9, 32, 31
	or %r7, %r9, %r10
	li %r0, 208
	ldbrx %r4, %r3, %r0
	xor %r8, %r6, %r4
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v0, %v0, %v18
	vor %v1, %v1, %v18
	vperm %v0, %v8, %v9, %v0
	vperm %v1, %v10, %v11, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r8, 32
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v2, %v0, %v19
	vor %v3, %v1, %v19
	vperm %v2, %v12, %v13, %v2
	vperm %v3, %v14, %v15, %v3
	vxor %v2, %v2, %v3
	vperm %v0, %v16, %v16, %v0
	vperm %v1, %v17, %v17, %v1
	vxor %v0, %v0, %v1
	vsel %v0, %v2, %v0, %v7
	mfvsrd %r8, 32
	rldicl %r9, %r8, 32, 32
	rlwinm %r10, %r8, 0, 0, 31
	rlwinm %r11, %r9, 24, 0, 31
	xor %r11, %r9, %r11
	rlwinm %r4, %r9, 16, 0, 31
	xor %r11, %r11, %r4
	rlwinm %r4, %r10, 24, 0, 31
	rlwinm %r0, %r10, 16, 0, 31
	xor %r4, %r4, %r0
	rlwinm %r0, %r10, 8, 0, 31
	xor %r4, %r4, %r0
	xor %r11, %r11, %r4
	rlwinm %r0, %r9, 8, 0, 31
	xor %r10, %r9, %r0
	xor %r10, %r10, %r4
	rldicr %r11, %r11, 32, 31
	or %r8, %r11, %r10
	xor %r7, %r7, %r8
	li %r0, 216
	ldbrx %r4, %r3, %r0
	xor %r8, %r7, %r4
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v0, %v0, %v18
	vor %v1, %v1, %v18
	vperm %v0, %v8, %v9, %v0
	vperm %v1, %v10, %v11, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r8, 32
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v2, %v0, %v19
	vor %v3, %v1, %v19
	vperm %v2, %v12, %v13, %v2
	vperm %v3, %v14, %v15, %v3
	vxor %v2, %v2, %v3
	vperm %v0, %v16, %v16, %v0
	vperm %v1, %v17, %v17, %v1
	vxor %v0, %v0, %v1
	vsel %v0, %v2, %v0, %v7
	mfvsrd %r8, 32
	rldicl %r9, %r8, 32, 32
	rlwinm %r10, %r8, 0, 0, 31
	rlwinm %r11, %r9, 24, 0, 31
	xor %r11, %r9, %r11
	rlwinm %r4, %r9, 16, 0, 31
	xor %r11, %r11, %r4
	rlwinm %r4, %r10, 24, 0, 31
	rlwinm %r0, %r10, 16, 0, 31
	xor %r4, %r4, %r0
	rlwinm %r0, %r10, 8, 0, 31
	xor %r4, %r4, %r0
	xor %r11, %r11, %r4
	rlwinm %r0, %r9, 8, 0, 31
	xor %r10, %r9, %r0
	xor %r10, %r10, %r4
	rldicr %r11, %r11, 32, 31
	or %r8, %r11, %r10
	xor %r6, %r6, %r8
	li %r0, 224
	ldbrx %r4, %r3, %r0
	xor %r8, %r6, %r4
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v0, %v0, %v18
	vor %v1, %v1, %v18
	vperm %v0, %v8, %v9, %v0
	vperm %v1, %v10, %v11, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r8, 32
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v2, %v0, %v19
	vor %v3, %v1, %v19
	vperm %v2, %v12, %v13, %v2
	vperm %v3, %v14, %v15, %v3
	vxor %v2, %v2, %v3
	vperm %v0, %v16, %v16, %v0
	vperm %v1, %v17, %v17, %v1
	vxor %v0, %v0, %v1
	vsel %v0, %v2, %v0, %v7
	mfvsrd %r8, 32
	rldicl %r9, %r8, 32, 32
	rlwinm %r10, %r8, 0, 0, 31
	rlwinm %r11, %r9, 24, 0, 31
	xor %r11, %r9, %r11
	rlwinm %r4, %r9, 16, 0, 31
	xor %r11, %r11, %r4
	rlwinm %r4, %r10, 24, 0, 31
	rlwinm %r0, %r10, 16, 0, 31
	xor %r4, %r4, %r0
	rlwinm %r0, %r10, 8, 0, 31
	xor %r4, %r4, %r0
	xor %r11, %r11, %r4
	rlwinm %r0, %r9, 8, 0, 31
	xor %r10, %r9, %r0
	xor %r10, %r10, %r4
	rldicr %r11, %r11, 32, 31
	or %r8, %r11, %r10
	xor %r7, %r7, %r8
	li %r0, 232
	ldbrx %r4, %r3, %r0
	xor %r8, %r7, %r4
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v0, %v0, %v18
	vor %v1, %v1, %v18
	vperm %v0, %v8, %v9, %v0
	vperm %v1, %v10, %v11, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r8, 32
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v2, %v0, %v19
	vor %v3, %v1, %v19
	vperm %v2, %v12, %v13, %v2
	vperm %v3, %v14, %v15, %v3
	vxor %v2, %v2, %v3
	vperm %v0, %v16, %v16, %v0
	vperm %v1, %v17, %v17, %v1
	vxor %v0, %v0, %v1
	vsel %v0, %v2, %v0, %v7
	mfvsrd %r8, 32
	rldicl %r9, %r8, 32, 32
	rlwinm %r10, %r8, 0, 0, 31
	rlwinm %r11, %r9, 24, 0, 31
	xor %r11, %r9, %r11
	rlwinm %r4, %r9, 16, 0, 31
	xor %r11, %r11, %r4
	rlwinm %r4, %r10, 24, 0, 31
	rlwinm %r0, %r10, 16, 0, 31
	xor %r4, %r4, %r0
	rlwinm %r0, %r10, 8, 0, 31
	xor %r4, %r4, %r0
	xor %r11, %r11, %r4
	rlwinm %r0, %r9, 8, 0, 31
	xor %r10, %r9, %r0
	xor %r10, %r10, %r4
	rldicr %r11, %r11, 32, 31
	or %r8, %r11, %r10
	xor %r6, %r6, %r8
	li %r0, 240
	ldbrx %r4, %r3, %r0
	xor %r8, %r6, %r4
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v0, %v0, %v18
	vor %v1, %v1, %v18
	vperm %v0, %v8, %v9, %v0
	vperm %v1, %v10, %v11, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r8, 32
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v2, %v0, %v19
	vor %v3, %v1, %v19
	vperm %v2, %v12, %v13, %v2
	vperm %v3, %v14, %v15, %v3
	vxor %v2, %v2, %v3
	vperm %v0, %v16, %v16, %v0
	vperm %v1, %v17, %v17, %v1
	vxor %v0, %v0, %v1
	vsel %v0, %v2, %v0, %v7
	mfvsrd %r8, 32
	rldicl %r9, %r8, 32, 32
	rlwinm %r10, %r8, 0, 0, 31
	rlwinm %r11, %r9, 24, 0, 31
	xor %r11, %r9, %r11
	rlwinm %r4, %r9, 16, 0, 31
	xor %r11, %r11, %r4
	rlwinm %r4, %r10, 24, 0, 31
	rlwinm %r0, %r10, 16, 0, 31
	xor %r4, %r4, %r0
	rlwinm %r0, %r10, 8, 0, 31
	xor %r4, %r4, %r0
	xor %r11, %r11, %r4
	rlwinm %r0, %r9, 8, 0, 31
	xor %r10, %r9, %r0
	xor %r10, %r10, %r4
	rldicr %r11, %r11, 32, 31
	or %r8, %r11, %r10
	xor %r7, %r7, %r8
	li %r0, 248
	ldbrx %r4, %r3, %r0
	xor %r8, %r7, %r4
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v0, %v0, %v18
	vor %v1, %v1, %v18
	vperm %v0, %v8, %v9, %v0
	vperm %v1, %v10, %v11, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r8, 32
	and %r9, %r8, %r12
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r12
	mtvsrd 32, %r9
	mtvsrd 33, %r10
	vor %v2, %v0, %v19
	vor %v3, %v1, %v19
	vperm %v2, %v12, %v13, %v2
	vperm %v3, %v14, %v15, %v3
	vxor %v2, %v2, %v3
	vperm %v0, %v16, %v16, %v0
	vperm %v1, %v17, %v17, %v1
	vxor %v0, %v0, %v1
	vsel %v0, %v2, %v0, %v7
	mfvsrd %r8, 32
	rldicl %r9, %r8, 32, 32
	rlwinm %r10, %r8, 0, 0, 31
	rlwinm %r11, %r9, 24, 0, 31
	xor %r11, %r9, %r11
	rlwinm %r4, %r9, 16, 0, 31
	xor %r11, %r11, %r4
	rlwinm %r4, %r10, 24, 0, 31
	rlwinm %r0, %r10, 16, 0, 31
	xor %r4, %r4, %r0
	rlwinm %r0, %r10, 8, 0, 31
	xor %r4, %r4, %r0
	xor %r11, %r11, %r4
	rlwinm %r0, %r9, 8, 0, 31
	xor %r10, %r9, %r0
	xor %r10, %r10, %r4
	rldicr %r11, %r11, 32, 31
	or %r8, %r11, %r10
	xor %r6, %r6, %r8
	li %r0, 256
	ldbrx %r4, %r3, %r0
	xor %r7, %r7, %r4
	li %r0, 264
	ldbrx %r4, %r3, %r0
	xor %r6, %r6, %r4
	li %r0, 3088
	stdbrx %r7, %r5, %r0
	li %r0, 3096
	stdbrx %r6, %r5, %r0
	b 21f
20:
	li %r0, 192
	ldbrx %r4, %r3, %r0
	xor %r7, %r7, %r4
	li %r0, 200
	ldbrx %r4, %r3, %r0
	xor %r6, %r6, %r4
	li %r0, 3088
	stdbrx %r7, %r5, %r0
	li %r0, 3096
	stdbrx %r6, %r5, %r0
21:
	blr
