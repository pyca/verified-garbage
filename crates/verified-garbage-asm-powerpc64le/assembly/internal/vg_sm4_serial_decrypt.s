// The functions of `src/internal/vg_sm4_serial_decrypt.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_serial_decrypt:
	mflr %r0
	bcl 20, 31, 2f
2:
	mflr %r10
	addis %r10, %r10, ({VG_SM4_PPC64LE_AFFINE}
	addi %r10, %r10, ({VG_SM4_PPC64LE_AFFINE}
	mtlr %r0
	li %r11, 0
	lxvd2x 44, %r10, %r11
	li %r11, 16
	lxvd2x 45, %r10, %r11
	li %r11, 32
	lxvd2x 46, %r10, %r11
	li %r11, 48
	lxvd2x 47, %r10, %r11
	lis %r12, 3855
	ori %r12, %r12, 3855
	li %r0, 768
	lwbrx %r4, %r5, %r0
	li %r0, 772
	lwbrx %r6, %r5, %r0
	li %r0, 776
	lwbrx %r7, %r5, %r0
	li %r0, 780
	lwbrx %r8, %r5, %r0
	lwz %r9, 124(%r3)
	xor %r9, %r9, %r6
	xor %r9, %r9, %r7
	xor %r9, %r9, %r8
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v12, %v12, %v0
	vperm %v1, %v13, %v13, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r9, 32
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v14, %v14, %v0
	vperm %v1, %v15, %v15, %v1
	vxor %v0, %v0, %v1
	mfvsrd %r9, 32
	rlwinm %r10, %r9, 2, 0, 31
	xor %r11, %r9, %r10
	rlwinm %r10, %r9, 10, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 18, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 24, 0, 31
	xor %r11, %r11, %r10
	xor %r4, %r4, %r11
	lwz %r9, 120(%r3)
	xor %r9, %r9, %r7
	xor %r9, %r9, %r8
	xor %r9, %r9, %r4
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v12, %v12, %v0
	vperm %v1, %v13, %v13, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r9, 32
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v14, %v14, %v0
	vperm %v1, %v15, %v15, %v1
	vxor %v0, %v0, %v1
	mfvsrd %r9, 32
	rlwinm %r10, %r9, 2, 0, 31
	xor %r11, %r9, %r10
	rlwinm %r10, %r9, 10, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 18, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 24, 0, 31
	xor %r11, %r11, %r10
	xor %r6, %r6, %r11
	lwz %r9, 116(%r3)
	xor %r9, %r9, %r8
	xor %r9, %r9, %r4
	xor %r9, %r9, %r6
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v12, %v12, %v0
	vperm %v1, %v13, %v13, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r9, 32
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v14, %v14, %v0
	vperm %v1, %v15, %v15, %v1
	vxor %v0, %v0, %v1
	mfvsrd %r9, 32
	rlwinm %r10, %r9, 2, 0, 31
	xor %r11, %r9, %r10
	rlwinm %r10, %r9, 10, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 18, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 24, 0, 31
	xor %r11, %r11, %r10
	xor %r7, %r7, %r11
	lwz %r9, 112(%r3)
	xor %r9, %r9, %r4
	xor %r9, %r9, %r6
	xor %r9, %r9, %r7
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v12, %v12, %v0
	vperm %v1, %v13, %v13, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r9, 32
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v14, %v14, %v0
	vperm %v1, %v15, %v15, %v1
	vxor %v0, %v0, %v1
	mfvsrd %r9, 32
	rlwinm %r10, %r9, 2, 0, 31
	xor %r11, %r9, %r10
	rlwinm %r10, %r9, 10, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 18, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 24, 0, 31
	xor %r11, %r11, %r10
	xor %r8, %r8, %r11
	lwz %r9, 108(%r3)
	xor %r9, %r9, %r6
	xor %r9, %r9, %r7
	xor %r9, %r9, %r8
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v12, %v12, %v0
	vperm %v1, %v13, %v13, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r9, 32
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v14, %v14, %v0
	vperm %v1, %v15, %v15, %v1
	vxor %v0, %v0, %v1
	mfvsrd %r9, 32
	rlwinm %r10, %r9, 2, 0, 31
	xor %r11, %r9, %r10
	rlwinm %r10, %r9, 10, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 18, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 24, 0, 31
	xor %r11, %r11, %r10
	xor %r4, %r4, %r11
	lwz %r9, 104(%r3)
	xor %r9, %r9, %r7
	xor %r9, %r9, %r8
	xor %r9, %r9, %r4
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v12, %v12, %v0
	vperm %v1, %v13, %v13, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r9, 32
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v14, %v14, %v0
	vperm %v1, %v15, %v15, %v1
	vxor %v0, %v0, %v1
	mfvsrd %r9, 32
	rlwinm %r10, %r9, 2, 0, 31
	xor %r11, %r9, %r10
	rlwinm %r10, %r9, 10, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 18, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 24, 0, 31
	xor %r11, %r11, %r10
	xor %r6, %r6, %r11
	lwz %r9, 100(%r3)
	xor %r9, %r9, %r8
	xor %r9, %r9, %r4
	xor %r9, %r9, %r6
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v12, %v12, %v0
	vperm %v1, %v13, %v13, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r9, 32
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v14, %v14, %v0
	vperm %v1, %v15, %v15, %v1
	vxor %v0, %v0, %v1
	mfvsrd %r9, 32
	rlwinm %r10, %r9, 2, 0, 31
	xor %r11, %r9, %r10
	rlwinm %r10, %r9, 10, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 18, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 24, 0, 31
	xor %r11, %r11, %r10
	xor %r7, %r7, %r11
	lwz %r9, 96(%r3)
	xor %r9, %r9, %r4
	xor %r9, %r9, %r6
	xor %r9, %r9, %r7
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v12, %v12, %v0
	vperm %v1, %v13, %v13, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r9, 32
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v14, %v14, %v0
	vperm %v1, %v15, %v15, %v1
	vxor %v0, %v0, %v1
	mfvsrd %r9, 32
	rlwinm %r10, %r9, 2, 0, 31
	xor %r11, %r9, %r10
	rlwinm %r10, %r9, 10, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 18, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 24, 0, 31
	xor %r11, %r11, %r10
	xor %r8, %r8, %r11
	lwz %r9, 92(%r3)
	xor %r9, %r9, %r6
	xor %r9, %r9, %r7
	xor %r9, %r9, %r8
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v12, %v12, %v0
	vperm %v1, %v13, %v13, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r9, 32
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v14, %v14, %v0
	vperm %v1, %v15, %v15, %v1
	vxor %v0, %v0, %v1
	mfvsrd %r9, 32
	rlwinm %r10, %r9, 2, 0, 31
	xor %r11, %r9, %r10
	rlwinm %r10, %r9, 10, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 18, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 24, 0, 31
	xor %r11, %r11, %r10
	xor %r4, %r4, %r11
	lwz %r9, 88(%r3)
	xor %r9, %r9, %r7
	xor %r9, %r9, %r8
	xor %r9, %r9, %r4
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v12, %v12, %v0
	vperm %v1, %v13, %v13, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r9, 32
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v14, %v14, %v0
	vperm %v1, %v15, %v15, %v1
	vxor %v0, %v0, %v1
	mfvsrd %r9, 32
	rlwinm %r10, %r9, 2, 0, 31
	xor %r11, %r9, %r10
	rlwinm %r10, %r9, 10, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 18, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 24, 0, 31
	xor %r11, %r11, %r10
	xor %r6, %r6, %r11
	lwz %r9, 84(%r3)
	xor %r9, %r9, %r8
	xor %r9, %r9, %r4
	xor %r9, %r9, %r6
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v12, %v12, %v0
	vperm %v1, %v13, %v13, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r9, 32
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v14, %v14, %v0
	vperm %v1, %v15, %v15, %v1
	vxor %v0, %v0, %v1
	mfvsrd %r9, 32
	rlwinm %r10, %r9, 2, 0, 31
	xor %r11, %r9, %r10
	rlwinm %r10, %r9, 10, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 18, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 24, 0, 31
	xor %r11, %r11, %r10
	xor %r7, %r7, %r11
	lwz %r9, 80(%r3)
	xor %r9, %r9, %r4
	xor %r9, %r9, %r6
	xor %r9, %r9, %r7
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v12, %v12, %v0
	vperm %v1, %v13, %v13, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r9, 32
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v14, %v14, %v0
	vperm %v1, %v15, %v15, %v1
	vxor %v0, %v0, %v1
	mfvsrd %r9, 32
	rlwinm %r10, %r9, 2, 0, 31
	xor %r11, %r9, %r10
	rlwinm %r10, %r9, 10, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 18, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 24, 0, 31
	xor %r11, %r11, %r10
	xor %r8, %r8, %r11
	lwz %r9, 76(%r3)
	xor %r9, %r9, %r6
	xor %r9, %r9, %r7
	xor %r9, %r9, %r8
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v12, %v12, %v0
	vperm %v1, %v13, %v13, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r9, 32
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v14, %v14, %v0
	vperm %v1, %v15, %v15, %v1
	vxor %v0, %v0, %v1
	mfvsrd %r9, 32
	rlwinm %r10, %r9, 2, 0, 31
	xor %r11, %r9, %r10
	rlwinm %r10, %r9, 10, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 18, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 24, 0, 31
	xor %r11, %r11, %r10
	xor %r4, %r4, %r11
	lwz %r9, 72(%r3)
	xor %r9, %r9, %r7
	xor %r9, %r9, %r8
	xor %r9, %r9, %r4
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v12, %v12, %v0
	vperm %v1, %v13, %v13, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r9, 32
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v14, %v14, %v0
	vperm %v1, %v15, %v15, %v1
	vxor %v0, %v0, %v1
	mfvsrd %r9, 32
	rlwinm %r10, %r9, 2, 0, 31
	xor %r11, %r9, %r10
	rlwinm %r10, %r9, 10, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 18, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 24, 0, 31
	xor %r11, %r11, %r10
	xor %r6, %r6, %r11
	lwz %r9, 68(%r3)
	xor %r9, %r9, %r8
	xor %r9, %r9, %r4
	xor %r9, %r9, %r6
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v12, %v12, %v0
	vperm %v1, %v13, %v13, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r9, 32
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v14, %v14, %v0
	vperm %v1, %v15, %v15, %v1
	vxor %v0, %v0, %v1
	mfvsrd %r9, 32
	rlwinm %r10, %r9, 2, 0, 31
	xor %r11, %r9, %r10
	rlwinm %r10, %r9, 10, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 18, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 24, 0, 31
	xor %r11, %r11, %r10
	xor %r7, %r7, %r11
	lwz %r9, 64(%r3)
	xor %r9, %r9, %r4
	xor %r9, %r9, %r6
	xor %r9, %r9, %r7
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v12, %v12, %v0
	vperm %v1, %v13, %v13, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r9, 32
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v14, %v14, %v0
	vperm %v1, %v15, %v15, %v1
	vxor %v0, %v0, %v1
	mfvsrd %r9, 32
	rlwinm %r10, %r9, 2, 0, 31
	xor %r11, %r9, %r10
	rlwinm %r10, %r9, 10, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 18, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 24, 0, 31
	xor %r11, %r11, %r10
	xor %r8, %r8, %r11
	lwz %r9, 60(%r3)
	xor %r9, %r9, %r6
	xor %r9, %r9, %r7
	xor %r9, %r9, %r8
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v12, %v12, %v0
	vperm %v1, %v13, %v13, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r9, 32
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v14, %v14, %v0
	vperm %v1, %v15, %v15, %v1
	vxor %v0, %v0, %v1
	mfvsrd %r9, 32
	rlwinm %r10, %r9, 2, 0, 31
	xor %r11, %r9, %r10
	rlwinm %r10, %r9, 10, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 18, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 24, 0, 31
	xor %r11, %r11, %r10
	xor %r4, %r4, %r11
	lwz %r9, 56(%r3)
	xor %r9, %r9, %r7
	xor %r9, %r9, %r8
	xor %r9, %r9, %r4
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v12, %v12, %v0
	vperm %v1, %v13, %v13, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r9, 32
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v14, %v14, %v0
	vperm %v1, %v15, %v15, %v1
	vxor %v0, %v0, %v1
	mfvsrd %r9, 32
	rlwinm %r10, %r9, 2, 0, 31
	xor %r11, %r9, %r10
	rlwinm %r10, %r9, 10, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 18, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 24, 0, 31
	xor %r11, %r11, %r10
	xor %r6, %r6, %r11
	lwz %r9, 52(%r3)
	xor %r9, %r9, %r8
	xor %r9, %r9, %r4
	xor %r9, %r9, %r6
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v12, %v12, %v0
	vperm %v1, %v13, %v13, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r9, 32
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v14, %v14, %v0
	vperm %v1, %v15, %v15, %v1
	vxor %v0, %v0, %v1
	mfvsrd %r9, 32
	rlwinm %r10, %r9, 2, 0, 31
	xor %r11, %r9, %r10
	rlwinm %r10, %r9, 10, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 18, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 24, 0, 31
	xor %r11, %r11, %r10
	xor %r7, %r7, %r11
	lwz %r9, 48(%r3)
	xor %r9, %r9, %r4
	xor %r9, %r9, %r6
	xor %r9, %r9, %r7
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v12, %v12, %v0
	vperm %v1, %v13, %v13, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r9, 32
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v14, %v14, %v0
	vperm %v1, %v15, %v15, %v1
	vxor %v0, %v0, %v1
	mfvsrd %r9, 32
	rlwinm %r10, %r9, 2, 0, 31
	xor %r11, %r9, %r10
	rlwinm %r10, %r9, 10, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 18, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 24, 0, 31
	xor %r11, %r11, %r10
	xor %r8, %r8, %r11
	lwz %r9, 44(%r3)
	xor %r9, %r9, %r6
	xor %r9, %r9, %r7
	xor %r9, %r9, %r8
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v12, %v12, %v0
	vperm %v1, %v13, %v13, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r9, 32
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v14, %v14, %v0
	vperm %v1, %v15, %v15, %v1
	vxor %v0, %v0, %v1
	mfvsrd %r9, 32
	rlwinm %r10, %r9, 2, 0, 31
	xor %r11, %r9, %r10
	rlwinm %r10, %r9, 10, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 18, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 24, 0, 31
	xor %r11, %r11, %r10
	xor %r4, %r4, %r11
	lwz %r9, 40(%r3)
	xor %r9, %r9, %r7
	xor %r9, %r9, %r8
	xor %r9, %r9, %r4
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v12, %v12, %v0
	vperm %v1, %v13, %v13, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r9, 32
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v14, %v14, %v0
	vperm %v1, %v15, %v15, %v1
	vxor %v0, %v0, %v1
	mfvsrd %r9, 32
	rlwinm %r10, %r9, 2, 0, 31
	xor %r11, %r9, %r10
	rlwinm %r10, %r9, 10, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 18, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 24, 0, 31
	xor %r11, %r11, %r10
	xor %r6, %r6, %r11
	lwz %r9, 36(%r3)
	xor %r9, %r9, %r8
	xor %r9, %r9, %r4
	xor %r9, %r9, %r6
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v12, %v12, %v0
	vperm %v1, %v13, %v13, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r9, 32
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v14, %v14, %v0
	vperm %v1, %v15, %v15, %v1
	vxor %v0, %v0, %v1
	mfvsrd %r9, 32
	rlwinm %r10, %r9, 2, 0, 31
	xor %r11, %r9, %r10
	rlwinm %r10, %r9, 10, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 18, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 24, 0, 31
	xor %r11, %r11, %r10
	xor %r7, %r7, %r11
	lwz %r9, 32(%r3)
	xor %r9, %r9, %r4
	xor %r9, %r9, %r6
	xor %r9, %r9, %r7
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v12, %v12, %v0
	vperm %v1, %v13, %v13, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r9, 32
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v14, %v14, %v0
	vperm %v1, %v15, %v15, %v1
	vxor %v0, %v0, %v1
	mfvsrd %r9, 32
	rlwinm %r10, %r9, 2, 0, 31
	xor %r11, %r9, %r10
	rlwinm %r10, %r9, 10, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 18, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 24, 0, 31
	xor %r11, %r11, %r10
	xor %r8, %r8, %r11
	lwz %r9, 28(%r3)
	xor %r9, %r9, %r6
	xor %r9, %r9, %r7
	xor %r9, %r9, %r8
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v12, %v12, %v0
	vperm %v1, %v13, %v13, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r9, 32
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v14, %v14, %v0
	vperm %v1, %v15, %v15, %v1
	vxor %v0, %v0, %v1
	mfvsrd %r9, 32
	rlwinm %r10, %r9, 2, 0, 31
	xor %r11, %r9, %r10
	rlwinm %r10, %r9, 10, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 18, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 24, 0, 31
	xor %r11, %r11, %r10
	xor %r4, %r4, %r11
	lwz %r9, 24(%r3)
	xor %r9, %r9, %r7
	xor %r9, %r9, %r8
	xor %r9, %r9, %r4
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v12, %v12, %v0
	vperm %v1, %v13, %v13, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r9, 32
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v14, %v14, %v0
	vperm %v1, %v15, %v15, %v1
	vxor %v0, %v0, %v1
	mfvsrd %r9, 32
	rlwinm %r10, %r9, 2, 0, 31
	xor %r11, %r9, %r10
	rlwinm %r10, %r9, 10, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 18, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 24, 0, 31
	xor %r11, %r11, %r10
	xor %r6, %r6, %r11
	lwz %r9, 20(%r3)
	xor %r9, %r9, %r8
	xor %r9, %r9, %r4
	xor %r9, %r9, %r6
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v12, %v12, %v0
	vperm %v1, %v13, %v13, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r9, 32
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v14, %v14, %v0
	vperm %v1, %v15, %v15, %v1
	vxor %v0, %v0, %v1
	mfvsrd %r9, 32
	rlwinm %r10, %r9, 2, 0, 31
	xor %r11, %r9, %r10
	rlwinm %r10, %r9, 10, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 18, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 24, 0, 31
	xor %r11, %r11, %r10
	xor %r7, %r7, %r11
	lwz %r9, 16(%r3)
	xor %r9, %r9, %r4
	xor %r9, %r9, %r6
	xor %r9, %r9, %r7
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v12, %v12, %v0
	vperm %v1, %v13, %v13, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r9, 32
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v14, %v14, %v0
	vperm %v1, %v15, %v15, %v1
	vxor %v0, %v0, %v1
	mfvsrd %r9, 32
	rlwinm %r10, %r9, 2, 0, 31
	xor %r11, %r9, %r10
	rlwinm %r10, %r9, 10, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 18, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 24, 0, 31
	xor %r11, %r11, %r10
	xor %r8, %r8, %r11
	lwz %r9, 12(%r3)
	xor %r9, %r9, %r6
	xor %r9, %r9, %r7
	xor %r9, %r9, %r8
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v12, %v12, %v0
	vperm %v1, %v13, %v13, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r9, 32
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v14, %v14, %v0
	vperm %v1, %v15, %v15, %v1
	vxor %v0, %v0, %v1
	mfvsrd %r9, 32
	rlwinm %r10, %r9, 2, 0, 31
	xor %r11, %r9, %r10
	rlwinm %r10, %r9, 10, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 18, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 24, 0, 31
	xor %r11, %r11, %r10
	xor %r4, %r4, %r11
	lwz %r9, 8(%r3)
	xor %r9, %r9, %r7
	xor %r9, %r9, %r8
	xor %r9, %r9, %r4
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v12, %v12, %v0
	vperm %v1, %v13, %v13, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r9, 32
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v14, %v14, %v0
	vperm %v1, %v15, %v15, %v1
	vxor %v0, %v0, %v1
	mfvsrd %r9, 32
	rlwinm %r10, %r9, 2, 0, 31
	xor %r11, %r9, %r10
	rlwinm %r10, %r9, 10, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 18, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 24, 0, 31
	xor %r11, %r11, %r10
	xor %r6, %r6, %r11
	lwz %r9, 4(%r3)
	xor %r9, %r9, %r8
	xor %r9, %r9, %r4
	xor %r9, %r9, %r6
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v12, %v12, %v0
	vperm %v1, %v13, %v13, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r9, 32
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v14, %v14, %v0
	vperm %v1, %v15, %v15, %v1
	vxor %v0, %v0, %v1
	mfvsrd %r9, 32
	rlwinm %r10, %r9, 2, 0, 31
	xor %r11, %r9, %r10
	rlwinm %r10, %r9, 10, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 18, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 24, 0, 31
	xor %r11, %r11, %r10
	xor %r7, %r7, %r11
	lwz %r9, 0(%r3)
	xor %r9, %r9, %r4
	xor %r9, %r9, %r6
	xor %r9, %r9, %r7
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v12, %v12, %v0
	vperm %v1, %v13, %v13, %v1
	vxor %v0, %v0, %v1
	vsbox %v0, %v0
	mfvsrd %r9, 32
	and %r10, %r9, %r12
	rlwinm %r11, %r9, 28, 4, 31
	and %r11, %r11, %r12
	mtvsrd 32, %r10
	mtvsrd 33, %r11
	vperm %v0, %v14, %v14, %v0
	vperm %v1, %v15, %v15, %v1
	vxor %v0, %v0, %v1
	mfvsrd %r9, 32
	rlwinm %r10, %r9, 2, 0, 31
	xor %r11, %r9, %r10
	rlwinm %r10, %r9, 10, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 18, 0, 31
	xor %r11, %r11, %r10
	rlwinm %r10, %r9, 24, 0, 31
	xor %r11, %r11, %r10
	xor %r8, %r8, %r11
	li %r0, 768
	stwbrx %r8, %r5, %r0
	li %r0, 772
	stwbrx %r7, %r5, %r0
	li %r0, 776
	stwbrx %r6, %r5, %r0
	li %r0, 780
	stwbrx %r4, %r5, %r0
	blr
