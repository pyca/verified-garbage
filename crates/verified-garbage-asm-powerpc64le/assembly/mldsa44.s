// The functions of `src/mldsa44.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa44_keygen:
	mflr %r0
	std %r24, 840(%r6)
	std %r25, 848(%r6)
	std %r26, 856(%r6)
	std %r27, 864(%r6)
	std %r28, 872(%r6)
	std %r29, 880(%r6)
	std %r30, 888(%r6)
	std %r31, 896(%r6)
	std %r0, 904(%r6)
	addi %r30, %r3, 0
	addi %r29, %r4, 0
	addi %r28, %r5, 0
	addi %r31, %r6, 0
	li %r24, 1
	li %r0, 4
	stb %r0, 920(%r31)
	li %r0, 4
	stb %r0, 921(%r31)
	li %r0, 0
	std %r0, 0(%r31)
	std %r0, 8(%r31)
	std %r0, 16(%r31)
	std %r0, 24(%r31)
	std %r0, 32(%r31)
	std %r0, 40(%r31)
	std %r0, 48(%r31)
	std %r0, 56(%r31)
	std %r0, 64(%r31)
	std %r0, 72(%r31)
	std %r0, 80(%r31)
	std %r0, 88(%r31)
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	std %r0, 112(%r31)
	std %r0, 120(%r31)
	std %r0, 128(%r31)
	std %r0, 136(%r31)
	std %r0, 144(%r31)
	std %r0, 152(%r31)
	std %r0, 160(%r31)
	std %r0, 168(%r31)
	std %r0, 176(%r31)
	std %r0, 184(%r31)
	std %r0, 192(%r31)
	li %r5, 0
	addi %r3, %r31, 0
	li %r4, 136
	addi %r6, %r30, 0
	li %r7, 32
	addi %r8, %r31, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r31, 0
	li %r4, 136
	addi %r6, %r31, 920
	li %r7, 2
	addi %r8, %r31, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r31, 0
	li %r4, 136
	li %r6, 31
	addi %r7, %r31, 200
	bl {vg_keccak_pad_scratch}
	li %r5, 0
	addi %r3, %r31, 0
	li %r4, 136
	addi %r6, %r31, 1024
	li %r7, 128
	addi %r8, %r31, 200
	bl {vg_keccak_squeeze_scratch}
	addi %r3, %r31, 1024
	addi %r4, %r31, 1152
	li %r5, 32
20:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 20b
	addi %r3, %r31, 1056
	addi %r4, %r31, 1216
	li %r5, 64
21:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 21b
	li %r0, 0
	stb %r0, 1281(%r31)
	li %r0, 0
	stb %r0, 1184(%r31)
	li %r0, 0
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4096
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 2048
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 4096
	add %r4, %r31, %r4
	li %r5, 256
22:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 22b
	li %r0, 1
	stb %r0, 1184(%r31)
	li %r0, 0
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 5120
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 2048
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 5120
	add %r4, %r31, %r4
	li %r5, 256
23:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 23b
	li %r0, 2
	stb %r0, 1184(%r31)
	li %r0, 0
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 6144
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 2048
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 6144
	add %r4, %r31, %r4
	li %r5, 256
24:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 24b
	li %r0, 3
	stb %r0, 1184(%r31)
	li %r0, 0
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 7168
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 2048
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 7168
	add %r4, %r31, %r4
	li %r5, 256
25:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 25b
	li %r0, 0
	stb %r0, 1184(%r31)
	li %r0, 1
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 8192
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 2048
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 8192
	add %r4, %r31, %r4
	li %r5, 256
26:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 26b
	li %r0, 1
	stb %r0, 1184(%r31)
	li %r0, 1
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 9216
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 2048
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 9216
	add %r4, %r31, %r4
	li %r5, 256
27:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 27b
	li %r0, 2
	stb %r0, 1184(%r31)
	li %r0, 1
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 10240
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 2048
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 10240
	add %r4, %r31, %r4
	li %r5, 256
28:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 28b
	li %r0, 3
	stb %r0, 1184(%r31)
	li %r0, 1
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 11264
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 2048
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 11264
	add %r4, %r31, %r4
	li %r5, 256
29:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 29b
	li %r0, 0
	stb %r0, 1184(%r31)
	li %r0, 2
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 12288
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 2048
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 12288
	add %r4, %r31, %r4
	li %r5, 256
210:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 210b
	li %r0, 1
	stb %r0, 1184(%r31)
	li %r0, 2
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 13312
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 2048
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 13312
	add %r4, %r31, %r4
	li %r5, 256
211:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 211b
	li %r0, 2
	stb %r0, 1184(%r31)
	li %r0, 2
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 14336
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 2048
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 14336
	add %r4, %r31, %r4
	li %r5, 256
212:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 212b
	li %r0, 3
	stb %r0, 1184(%r31)
	li %r0, 2
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 15360
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 2048
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 15360
	add %r4, %r31, %r4
	li %r5, 256
213:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 213b
	li %r0, 0
	stb %r0, 1184(%r31)
	li %r0, 3
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 16384
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 2048
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 16384
	add %r4, %r31, %r4
	li %r5, 256
214:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 214b
	li %r0, 1
	stb %r0, 1184(%r31)
	li %r0, 3
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 17408
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 2048
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 17408
	add %r4, %r31, %r4
	li %r5, 256
215:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 215b
	li %r0, 2
	stb %r0, 1184(%r31)
	li %r0, 3
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 18432
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 2048
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 18432
	add %r4, %r31, %r4
	li %r5, 256
216:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 216b
	li %r0, 3
	stb %r0, 1184(%r31)
	li %r0, 3
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 19456
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 2048
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 19456
	add %r4, %r31, %r4
	li %r5, 256
217:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 217b
	li %r0, 0
	stb %r0, 1280(%r31)
	lis %r3, 0
	ori %r3, %r3, 1216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2
	lis %r5, 0
	ori %r5, %r5, 20480
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 2048
	add %r6, %r31, %r6
	bl {vg_mldsa_rej_bounded_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 20480
	add %r4, %r31, %r4
	li %r5, 256
218:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 218b
	li %r0, 1
	stb %r0, 1280(%r31)
	lis %r3, 0
	ori %r3, %r3, 1216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2
	lis %r5, 0
	ori %r5, %r5, 21504
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 2048
	add %r6, %r31, %r6
	bl {vg_mldsa_rej_bounded_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 21504
	add %r4, %r31, %r4
	li %r5, 256
219:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 219b
	li %r0, 2
	stb %r0, 1280(%r31)
	lis %r3, 0
	ori %r3, %r3, 1216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2
	lis %r5, 0
	ori %r5, %r5, 22528
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 2048
	add %r6, %r31, %r6
	bl {vg_mldsa_rej_bounded_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 22528
	add %r4, %r31, %r4
	li %r5, 256
220:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 220b
	li %r0, 3
	stb %r0, 1280(%r31)
	lis %r3, 0
	ori %r3, %r3, 1216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2
	lis %r5, 0
	ori %r5, %r5, 23552
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 2048
	add %r6, %r31, %r6
	bl {vg_mldsa_rej_bounded_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 23552
	add %r4, %r31, %r4
	li %r5, 256
221:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 221b
	li %r0, 4
	stb %r0, 1280(%r31)
	lis %r3, 0
	ori %r3, %r3, 1216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2
	lis %r5, 0
	ori %r5, %r5, 24576
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 2048
	add %r6, %r31, %r6
	bl {vg_mldsa_rej_bounded_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 24576
	add %r4, %r31, %r4
	li %r5, 256
222:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 222b
	li %r0, 5
	stb %r0, 1280(%r31)
	lis %r3, 0
	ori %r3, %r3, 1216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2
	lis %r5, 0
	ori %r5, %r5, 25600
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 2048
	add %r6, %r31, %r6
	bl {vg_mldsa_rej_bounded_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 25600
	add %r4, %r31, %r4
	li %r5, 256
223:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 223b
	li %r0, 6
	stb %r0, 1280(%r31)
	lis %r3, 0
	ori %r3, %r3, 1216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2
	lis %r5, 0
	ori %r5, %r5, 26624
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 2048
	add %r6, %r31, %r6
	bl {vg_mldsa_rej_bounded_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 26624
	add %r4, %r31, %r4
	li %r5, 256
224:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 224b
	li %r0, 7
	stb %r0, 1280(%r31)
	lis %r3, 0
	ori %r3, %r3, 1216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2
	lis %r5, 0
	ori %r5, %r5, 27648
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 2048
	add %r6, %r31, %r6
	bl {vg_mldsa_rej_bounded_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 27648
	add %r4, %r31, %r4
	li %r5, 256
225:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 225b
	addi %r3, %r31, 1024
	addi %r4, %r29, 0
	li %r5, 32
226:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 226b
	addi %r3, %r31, 1024
	addi %r4, %r28, 0
	li %r5, 32
227:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 227b
	addi %r3, %r31, 1120
	addi %r4, %r28, 32
	li %r5, 32
228:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 228b
	lis %r3, 0
	ori %r3, %r3, 20480
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2
	lis %r5, 0
	ori %r5, %r5, 2
	lis %r6, 0
	ori %r6, %r6, 128
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 96
	bl {vg_mldsa_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 21504
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2
	lis %r5, 0
	ori %r5, %r5, 2
	lis %r6, 0
	ori %r6, %r6, 224
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 96
	bl {vg_mldsa_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 22528
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2
	lis %r5, 0
	ori %r5, %r5, 2
	lis %r6, 0
	ori %r6, %r6, 320
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 96
	bl {vg_mldsa_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 23552
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2
	lis %r5, 0
	ori %r5, %r5, 2
	lis %r6, 0
	ori %r6, %r6, 416
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 96
	bl {vg_mldsa_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 24576
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2
	lis %r5, 0
	ori %r5, %r5, 2
	lis %r6, 0
	ori %r6, %r6, 512
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 96
	bl {vg_mldsa_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 25600
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2
	lis %r5, 0
	ori %r5, %r5, 2
	lis %r6, 0
	ori %r6, %r6, 608
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 96
	bl {vg_mldsa_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2
	lis %r5, 0
	ori %r5, %r5, 2
	lis %r6, 0
	ori %r6, %r6, 704
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 96
	bl {vg_mldsa_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 27648
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2
	lis %r5, 0
	ori %r5, %r5, 2
	lis %r6, 0
	ori %r6, %r6, 800
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 96
	bl {vg_mldsa_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 20480
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2048
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 21504
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2048
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 22528
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2048
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 23552
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2048
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 28672
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4096
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 20480
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 28672
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 5120
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 21504
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 28672
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 6144
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 22528
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 28672
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 7168
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 23552
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 28672
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2048
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 28672
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 24576
	add %r4, %r31, %r4
	bl {vg_mldsa_add}
	lis %r3, 0
	ori %r3, %r3, 28672
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 29696
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 30720
	add %r5, %r31, %r5
	bl {vg_mldsa_power2round}
	lis %r3, 0
	ori %r3, %r3, 29696
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 1023
	lis %r5, 0
	ori %r5, %r5, 32
	add %r5, %r29, %r5
	lis %r6, 0
	ori %r6, %r6, 320
	bl {vg_mldsa_simple_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 30720
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4095
	lis %r5, 0
	ori %r5, %r5, 4096
	lis %r6, 0
	ori %r6, %r6, 896
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 416
	bl {vg_mldsa_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 28672
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 8192
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 20480
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 28672
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 9216
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 21504
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 28672
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 10240
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 22528
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 28672
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 11264
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 23552
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 28672
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2048
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 28672
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 25600
	add %r4, %r31, %r4
	bl {vg_mldsa_add}
	lis %r3, 0
	ori %r3, %r3, 28672
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 29696
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 30720
	add %r5, %r31, %r5
	bl {vg_mldsa_power2round}
	lis %r3, 0
	ori %r3, %r3, 29696
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 1023
	lis %r5, 0
	ori %r5, %r5, 352
	add %r5, %r29, %r5
	lis %r6, 0
	ori %r6, %r6, 320
	bl {vg_mldsa_simple_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 30720
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4095
	lis %r5, 0
	ori %r5, %r5, 4096
	lis %r6, 0
	ori %r6, %r6, 1312
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 416
	bl {vg_mldsa_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 28672
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 12288
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 20480
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 28672
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 13312
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 21504
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 28672
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 14336
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 22528
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 28672
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 15360
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 23552
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 28672
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2048
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 28672
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 26624
	add %r4, %r31, %r4
	bl {vg_mldsa_add}
	lis %r3, 0
	ori %r3, %r3, 28672
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 29696
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 30720
	add %r5, %r31, %r5
	bl {vg_mldsa_power2round}
	lis %r3, 0
	ori %r3, %r3, 29696
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 1023
	lis %r5, 0
	ori %r5, %r5, 672
	add %r5, %r29, %r5
	lis %r6, 0
	ori %r6, %r6, 320
	bl {vg_mldsa_simple_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 30720
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4095
	lis %r5, 0
	ori %r5, %r5, 4096
	lis %r6, 0
	ori %r6, %r6, 1728
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 416
	bl {vg_mldsa_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 28672
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 16384
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 20480
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 28672
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 17408
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 21504
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 28672
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 18432
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 22528
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 28672
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 19456
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 23552
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 28672
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2048
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 28672
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 27648
	add %r4, %r31, %r4
	bl {vg_mldsa_add}
	lis %r3, 0
	ori %r3, %r3, 28672
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 29696
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 30720
	add %r5, %r31, %r5
	bl {vg_mldsa_power2round}
	lis %r3, 0
	ori %r3, %r3, 29696
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 1023
	lis %r5, 0
	ori %r5, %r5, 992
	add %r5, %r29, %r5
	lis %r6, 0
	ori %r6, %r6, 320
	bl {vg_mldsa_simple_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 30720
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4095
	lis %r5, 0
	ori %r5, %r5, 4096
	lis %r6, 0
	ori %r6, %r6, 2144
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 416
	bl {vg_mldsa_bit_pack}
	li %r0, 0
	std %r0, 0(%r31)
	std %r0, 8(%r31)
	std %r0, 16(%r31)
	std %r0, 24(%r31)
	std %r0, 32(%r31)
	std %r0, 40(%r31)
	std %r0, 48(%r31)
	std %r0, 56(%r31)
	std %r0, 64(%r31)
	std %r0, 72(%r31)
	std %r0, 80(%r31)
	std %r0, 88(%r31)
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	std %r0, 112(%r31)
	std %r0, 120(%r31)
	std %r0, 128(%r31)
	std %r0, 136(%r31)
	std %r0, 144(%r31)
	std %r0, 152(%r31)
	std %r0, 160(%r31)
	std %r0, 168(%r31)
	std %r0, 176(%r31)
	std %r0, 184(%r31)
	std %r0, 192(%r31)
	li %r5, 0
	addi %r3, %r31, 0
	li %r4, 136
	addi %r6, %r29, 0
	li %r7, 1312
	addi %r8, %r31, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r31, 0
	li %r4, 136
	li %r6, 31
	addi %r7, %r31, 200
	bl {vg_keccak_pad_scratch}
	li %r5, 0
	addi %r3, %r31, 0
	li %r4, 136
	addi %r6, %r28, 64
	li %r7, 64
	addi %r8, %r31, 200
	bl {vg_keccak_squeeze_scratch}
	addi %r3, %r24, 0
	ld %r0, 904(%r31)
	mtlr %r0
	ld %r24, 840(%r31)
	ld %r25, 848(%r31)
	ld %r26, 856(%r31)
	ld %r27, 864(%r31)
	ld %r28, 872(%r31)
	ld %r29, 880(%r31)
	ld %r30, 888(%r31)
	ld %r31, 896(%r31)
	blr

vg_mldsa44_pk_tr:
	addi %r6, %r5, 0
	mflr %r0
	std %r24, 840(%r6)
	std %r25, 848(%r6)
	std %r26, 856(%r6)
	std %r27, 864(%r6)
	std %r28, 872(%r6)
	std %r29, 880(%r6)
	std %r30, 888(%r6)
	std %r31, 896(%r6)
	std %r0, 904(%r6)
	addi %r30, %r3, 0
	addi %r29, %r3, 0
	addi %r28, %r4, 0
	addi %r31, %r6, 0
	li %r24, 1
	li %r0, 0
	std %r0, 0(%r31)
	std %r0, 8(%r31)
	std %r0, 16(%r31)
	std %r0, 24(%r31)
	std %r0, 32(%r31)
	std %r0, 40(%r31)
	std %r0, 48(%r31)
	std %r0, 56(%r31)
	std %r0, 64(%r31)
	std %r0, 72(%r31)
	std %r0, 80(%r31)
	std %r0, 88(%r31)
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	std %r0, 112(%r31)
	std %r0, 120(%r31)
	std %r0, 128(%r31)
	std %r0, 136(%r31)
	std %r0, 144(%r31)
	std %r0, 152(%r31)
	std %r0, 160(%r31)
	std %r0, 168(%r31)
	std %r0, 176(%r31)
	std %r0, 184(%r31)
	std %r0, 192(%r31)
	li %r5, 0
	addi %r3, %r31, 0
	li %r4, 136
	addi %r6, %r29, 0
	li %r7, 1312
	addi %r8, %r31, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r31, 0
	li %r4, 136
	li %r6, 31
	addi %r7, %r31, 200
	bl {vg_keccak_pad_scratch}
	li %r5, 0
	addi %r3, %r31, 0
	li %r4, 136
	addi %r6, %r28, 0
	li %r7, 64
	addi %r8, %r31, 200
	bl {vg_keccak_squeeze_scratch}
	addi %r3, %r24, 0
	ld %r0, 904(%r31)
	mtlr %r0
	ld %r24, 840(%r31)
	ld %r25, 848(%r31)
	ld %r26, 856(%r31)
	ld %r27, 864(%r31)
	ld %r28, 872(%r31)
	ld %r29, 880(%r31)
	ld %r30, 888(%r31)
	ld %r31, 896(%r31)
	blr

vg_mldsa44_prepare_verifying_key:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	stdu %r1, -48(%r1)
	std %r30, 32(%r1)
	stdu %r1, -48(%r1)
	std %r31, 32(%r1)
	addi %r30, %r4, 0
	addi %r31, %r5, 0
	addi %r9, %r4, 0
	li %r5, 164
20:
	ld %r0, 0(%r3)
	std %r0, 0(%r9)
	addi %r3, %r3, 8
	addi %r9, %r9, 8
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 20b
	lis %r3, 0
	ori %r3, %r3, 32
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 1312
	add %r4, %r30, %r4
	bl {vg_mldsa_unpack_t1}
	lis %r3, 0
	ori %r3, %r3, 1312
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 352
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 2336
	add %r4, %r30, %r4
	bl {vg_mldsa_unpack_t1}
	lis %r3, 0
	ori %r3, %r3, 2336
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 672
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 3360
	add %r4, %r30, %r4
	bl {vg_mldsa_unpack_t1}
	lis %r3, 0
	ori %r3, %r3, 3360
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 992
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 4384
	add %r4, %r30, %r4
	bl {vg_mldsa_unpack_t1}
	lis %r3, 0
	ori %r3, %r3, 4384
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	ld %r31, 32(%r1)
	addi %r1, %r1, 48
	ld %r30, 32(%r1)
	addi %r1, %r1, 48
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	blr

vg_mldsa44_prepare_signing_key:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	stdu %r1, -48(%r1)
	std %r30, 32(%r1)
	stdu %r1, -48(%r1)
	std %r31, 32(%r1)
	addi %r30, %r4, 0
	addi %r31, %r5, 0
	addi %r9, %r4, 0
	li %r5, 320
20:
	ld %r0, 0(%r3)
	std %r0, 0(%r9)
	addi %r3, %r3, 8
	addi %r9, %r9, 8
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 20b
	lis %r3, 0
	ori %r3, %r3, 128
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 96
	lis %r5, 0
	ori %r5, %r5, 2
	lis %r6, 0
	ori %r6, %r6, 2
	lis %r7, 0
	ori %r7, %r7, 2560
	add %r7, %r30, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 2560
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 224
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 96
	lis %r5, 0
	ori %r5, %r5, 2
	lis %r6, 0
	ori %r6, %r6, 2
	lis %r7, 0
	ori %r7, %r7, 3584
	add %r7, %r30, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 3584
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 320
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 96
	lis %r5, 0
	ori %r5, %r5, 2
	lis %r6, 0
	ori %r6, %r6, 2
	lis %r7, 0
	ori %r7, %r7, 4608
	add %r7, %r30, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 4608
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 416
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 96
	lis %r5, 0
	ori %r5, %r5, 2
	lis %r6, 0
	ori %r6, %r6, 2
	lis %r7, 0
	ori %r7, %r7, 5632
	add %r7, %r30, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 5632
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 512
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 96
	lis %r5, 0
	ori %r5, %r5, 2
	lis %r6, 0
	ori %r6, %r6, 2
	lis %r7, 0
	ori %r7, %r7, 6656
	add %r7, %r30, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 6656
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 608
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 96
	lis %r5, 0
	ori %r5, %r5, 2
	lis %r6, 0
	ori %r6, %r6, 2
	lis %r7, 0
	ori %r7, %r7, 7680
	add %r7, %r30, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 7680
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 704
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 96
	lis %r5, 0
	ori %r5, %r5, 2
	lis %r6, 0
	ori %r6, %r6, 2
	lis %r7, 0
	ori %r7, %r7, 8704
	add %r7, %r30, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 8704
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 800
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 96
	lis %r5, 0
	ori %r5, %r5, 2
	lis %r6, 0
	ori %r6, %r6, 2
	lis %r7, 0
	ori %r7, %r7, 9728
	add %r7, %r30, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 9728
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 896
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 416
	lis %r5, 0
	ori %r5, %r5, 4095
	lis %r6, 0
	ori %r6, %r6, 4096
	lis %r7, 0
	ori %r7, %r7, 10752
	add %r7, %r30, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 10752
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 1312
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 416
	lis %r5, 0
	ori %r5, %r5, 4095
	lis %r6, 0
	ori %r6, %r6, 4096
	lis %r7, 0
	ori %r7, %r7, 11776
	add %r7, %r30, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 11776
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 1728
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 416
	lis %r5, 0
	ori %r5, %r5, 4095
	lis %r6, 0
	ori %r6, %r6, 4096
	lis %r7, 0
	ori %r7, %r7, 12800
	add %r7, %r30, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 12800
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 2144
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 416
	lis %r5, 0
	ori %r5, %r5, 4095
	lis %r6, 0
	ori %r6, %r6, 4096
	lis %r7, 0
	ori %r7, %r7, 13824
	add %r7, %r30, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 13824
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	ld %r31, 32(%r1)
	addi %r1, %r1, 48
	ld %r30, 32(%r1)
	addi %r1, %r1, 48
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	blr

vg_mldsa44_sign:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	addi %r8, %r3, 0
	li %r9, 0
	bl {vg_mldsa44_sign_with_cache}
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	blr

vg_mldsa44_sign_message:
	rldicl %r11, %r7, 56, 8
	cmpldi %cr0, %r11, 0
	beq %cr0, 20f
	li %r3, 2
	b 21f
20:
	lis %r12, 1
	ori %r12, %r12, 12288
	add %r12, %r10, %r12
	mflr %r0
	std %r22, 904(%r12)
	std %r23, 912(%r12)
	std %r24, 920(%r12)
	std %r25, 928(%r12)
	std %r26, 936(%r12)
	std %r27, 944(%r12)
	std %r28, 952(%r12)
	std %r29, 960(%r12)
	std %r30, 968(%r12)
	std %r0, 976(%r12)
	addi %r22, %r3, 0
	addi %r23, %r4, 0
	addi %r24, %r5, 0
	addi %r25, %r6, 0
	addi %r26, %r7, 0
	addi %r27, %r8, 0
	addi %r28, %r9, 0
	addi %r29, %r10, 0
	addi %r30, %r12, 0
	li %r0, 0
	stb %r0, 984(%r30)
	stb %r26, 985(%r30)
	li %r0, 0
	std %r0, 0(%r30)
	std %r0, 8(%r30)
	std %r0, 16(%r30)
	std %r0, 24(%r30)
	std %r0, 32(%r30)
	std %r0, 40(%r30)
	std %r0, 48(%r30)
	std %r0, 56(%r30)
	std %r0, 64(%r30)
	std %r0, 72(%r30)
	std %r0, 80(%r30)
	std %r0, 88(%r30)
	std %r0, 96(%r30)
	std %r0, 104(%r30)
	std %r0, 112(%r30)
	std %r0, 120(%r30)
	std %r0, 128(%r30)
	std %r0, 136(%r30)
	std %r0, 144(%r30)
	std %r0, 152(%r30)
	std %r0, 160(%r30)
	std %r0, 168(%r30)
	std %r0, 176(%r30)
	std %r0, 184(%r30)
	std %r0, 192(%r30)
	li %r5, 0
	addi %r3, %r30, 0
	li %r4, 136
	addi %r6, %r22, 64
	li %r7, 64
	addi %r8, %r30, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r30, 0
	li %r4, 136
	addi %r6, %r30, 984
	li %r7, 2
	addi %r8, %r30, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r30, 0
	li %r4, 136
	addi %r6, %r25, 0
	addi %r7, %r26, 0
	addi %r8, %r30, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r30, 0
	li %r4, 136
	addi %r6, %r23, 0
	addi %r7, %r24, 0
	addi %r8, %r30, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r30, 0
	li %r4, 136
	li %r6, 31
	addi %r7, %r30, 200
	bl {vg_keccak_pad_scratch}
	addi %r3, %r30, 0
	li %r4, 136
	li %r5, 0
	addi %r6, %r30, 840
	li %r7, 64
	addi %r8, %r30, 200
	bl {vg_keccak_squeeze_scratch}
	addi %r3, %r22, 0
	addi %r4, %r30, 840
	addi %r5, %r27, 0
	addi %r6, %r28, 0
	addi %r7, %r29, 0
	bl {vg_mldsa44_sign}
	ld %r0, 976(%r30)
	ld %r22, 904(%r30)
	ld %r23, 912(%r30)
	ld %r24, 920(%r30)
	ld %r25, 928(%r30)
	ld %r26, 936(%r30)
	ld %r27, 944(%r30)
	ld %r28, 952(%r30)
	ld %r29, 960(%r30)
	ld %r30, 968(%r30)
	mtlr %r0
21:
	blr

vg_mldsa44_sign_message_prepared:
	rldicl %r11, %r7, 56, 8
	cmpldi %cr0, %r11, 0
	beq %cr0, 20f
	li %r3, 2
	b 21f
20:
	lis %r12, 1
	ori %r12, %r12, 12288
	add %r12, %r10, %r12
	mflr %r0
	std %r22, 904(%r12)
	std %r23, 912(%r12)
	std %r24, 920(%r12)
	std %r25, 928(%r12)
	std %r26, 936(%r12)
	std %r27, 944(%r12)
	std %r28, 952(%r12)
	std %r29, 960(%r12)
	std %r30, 968(%r12)
	std %r0, 976(%r12)
	addi %r22, %r3, 0
	addi %r23, %r4, 0
	addi %r24, %r5, 0
	addi %r25, %r6, 0
	addi %r26, %r7, 0
	addi %r27, %r8, 0
	addi %r28, %r9, 0
	addi %r29, %r10, 0
	addi %r30, %r12, 0
	li %r0, 0
	stb %r0, 984(%r30)
	stb %r26, 985(%r30)
	li %r0, 0
	std %r0, 0(%r30)
	std %r0, 8(%r30)
	std %r0, 16(%r30)
	std %r0, 24(%r30)
	std %r0, 32(%r30)
	std %r0, 40(%r30)
	std %r0, 48(%r30)
	std %r0, 56(%r30)
	std %r0, 64(%r30)
	std %r0, 72(%r30)
	std %r0, 80(%r30)
	std %r0, 88(%r30)
	std %r0, 96(%r30)
	std %r0, 104(%r30)
	std %r0, 112(%r30)
	std %r0, 120(%r30)
	std %r0, 128(%r30)
	std %r0, 136(%r30)
	std %r0, 144(%r30)
	std %r0, 152(%r30)
	std %r0, 160(%r30)
	std %r0, 168(%r30)
	std %r0, 176(%r30)
	std %r0, 184(%r30)
	std %r0, 192(%r30)
	li %r5, 0
	addi %r3, %r30, 0
	li %r4, 136
	addi %r6, %r22, 64
	li %r7, 64
	addi %r8, %r30, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r30, 0
	li %r4, 136
	addi %r6, %r30, 984
	li %r7, 2
	addi %r8, %r30, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r30, 0
	li %r4, 136
	addi %r6, %r25, 0
	addi %r7, %r26, 0
	addi %r8, %r30, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r30, 0
	li %r4, 136
	addi %r6, %r23, 0
	addi %r7, %r24, 0
	addi %r8, %r30, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r30, 0
	li %r4, 136
	li %r6, 31
	addi %r7, %r30, 200
	bl {vg_keccak_pad_scratch}
	addi %r3, %r30, 0
	li %r4, 136
	li %r5, 0
	addi %r6, %r30, 840
	li %r7, 64
	addi %r8, %r30, 200
	bl {vg_keccak_squeeze_scratch}
	addi %r3, %r22, 0
	addi %r4, %r30, 840
	addi %r5, %r27, 0
	addi %r6, %r28, 0
	addi %r7, %r29, 0
	bl {vg_mldsa44_sign_prepared}
	ld %r0, 976(%r30)
	ld %r22, 904(%r30)
	ld %r23, 912(%r30)
	ld %r24, 920(%r30)
	ld %r25, 928(%r30)
	ld %r26, 936(%r30)
	ld %r27, 944(%r30)
	ld %r28, 952(%r30)
	ld %r29, 960(%r30)
	ld %r30, 968(%r30)
	mtlr %r0
21:
	blr

vg_mldsa44_verify:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	addi %r7, %r3, 0
	li %r8, 0
	bl {vg_mldsa44_verify_with_cache}
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	blr

vg_mldsa44_verify_message_cached:
	rldicl %r11, %r7, 56, 8
	cmpldi %cr0, %r11, 0
	beq %cr0, 20f
	li %r3, 2
	b 21f
20:
	lis %r12, 1
	ori %r12, %r12, 12288
	add %r12, %r9, %r12
	mflr %r0
	std %r22, 904(%r12)
	std %r23, 912(%r12)
	std %r24, 920(%r12)
	std %r25, 928(%r12)
	std %r26, 936(%r12)
	std %r27, 944(%r12)
	std %r28, 952(%r12)
	std %r29, 960(%r12)
	std %r30, 968(%r12)
	std %r0, 976(%r12)
	addi %r22, %r3, 0
	addi %r23, %r4, 0
	addi %r24, %r5, 0
	addi %r25, %r6, 0
	addi %r26, %r7, 0
	addi %r27, %r8, 0
	addi %r28, %r10, 0
	addi %r29, %r9, 0
	addi %r30, %r12, 0
	li %r0, 0
	stb %r0, 984(%r30)
	stb %r26, 985(%r30)
	li %r0, 0
	std %r0, 0(%r30)
	std %r0, 8(%r30)
	std %r0, 16(%r30)
	std %r0, 24(%r30)
	std %r0, 32(%r30)
	std %r0, 40(%r30)
	std %r0, 48(%r30)
	std %r0, 56(%r30)
	std %r0, 64(%r30)
	std %r0, 72(%r30)
	std %r0, 80(%r30)
	std %r0, 88(%r30)
	std %r0, 96(%r30)
	std %r0, 104(%r30)
	std %r0, 112(%r30)
	std %r0, 120(%r30)
	std %r0, 128(%r30)
	std %r0, 136(%r30)
	std %r0, 144(%r30)
	std %r0, 152(%r30)
	std %r0, 160(%r30)
	std %r0, 168(%r30)
	std %r0, 176(%r30)
	std %r0, 184(%r30)
	std %r0, 192(%r30)
	li %r5, 0
	addi %r3, %r30, 0
	li %r4, 136
	addi %r6, %r28, 0
	li %r7, 64
	addi %r8, %r30, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r30, 0
	li %r4, 136
	addi %r6, %r30, 984
	li %r7, 2
	addi %r8, %r30, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r30, 0
	li %r4, 136
	addi %r6, %r25, 0
	addi %r7, %r26, 0
	addi %r8, %r30, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r30, 0
	li %r4, 136
	addi %r6, %r23, 0
	addi %r7, %r24, 0
	addi %r8, %r30, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r30, 0
	li %r4, 136
	li %r6, 31
	addi %r7, %r30, 200
	bl {vg_keccak_pad_scratch}
	addi %r3, %r30, 0
	li %r4, 136
	li %r5, 0
	addi %r6, %r30, 840
	li %r7, 64
	addi %r8, %r30, 200
	bl {vg_keccak_squeeze_scratch}
	addi %r3, %r22, 0
	addi %r4, %r30, 840
	addi %r5, %r27, 0
	addi %r6, %r29, 0
	bl {vg_mldsa44_verify}
	ld %r0, 976(%r30)
	ld %r22, 904(%r30)
	ld %r23, 912(%r30)
	ld %r24, 920(%r30)
	ld %r25, 928(%r30)
	ld %r26, 936(%r30)
	ld %r27, 944(%r30)
	ld %r28, 952(%r30)
	ld %r29, 960(%r30)
	ld %r30, 968(%r30)
	mtlr %r0
21:
	blr

vg_mldsa44_verify_message_prepared:
	rldicl %r11, %r7, 56, 8
	cmpldi %cr0, %r11, 0
	beq %cr0, 20f
	li %r3, 2
	b 21f
20:
	lis %r12, 1
	ori %r12, %r12, 12288
	add %r12, %r9, %r12
	mflr %r0
	std %r22, 904(%r12)
	std %r23, 912(%r12)
	std %r24, 920(%r12)
	std %r25, 928(%r12)
	std %r26, 936(%r12)
	std %r27, 944(%r12)
	std %r28, 952(%r12)
	std %r29, 960(%r12)
	std %r30, 968(%r12)
	std %r0, 976(%r12)
	addi %r22, %r3, 0
	addi %r23, %r4, 0
	addi %r24, %r5, 0
	addi %r25, %r6, 0
	addi %r26, %r7, 0
	addi %r27, %r8, 0
	addi %r28, %r10, 0
	addi %r29, %r9, 0
	addi %r30, %r12, 0
	li %r0, 0
	stb %r0, 984(%r30)
	stb %r26, 985(%r30)
	li %r0, 0
	std %r0, 0(%r30)
	std %r0, 8(%r30)
	std %r0, 16(%r30)
	std %r0, 24(%r30)
	std %r0, 32(%r30)
	std %r0, 40(%r30)
	std %r0, 48(%r30)
	std %r0, 56(%r30)
	std %r0, 64(%r30)
	std %r0, 72(%r30)
	std %r0, 80(%r30)
	std %r0, 88(%r30)
	std %r0, 96(%r30)
	std %r0, 104(%r30)
	std %r0, 112(%r30)
	std %r0, 120(%r30)
	std %r0, 128(%r30)
	std %r0, 136(%r30)
	std %r0, 144(%r30)
	std %r0, 152(%r30)
	std %r0, 160(%r30)
	std %r0, 168(%r30)
	std %r0, 176(%r30)
	std %r0, 184(%r30)
	std %r0, 192(%r30)
	li %r5, 0
	addi %r3, %r30, 0
	li %r4, 136
	addi %r6, %r28, 0
	li %r7, 64
	addi %r8, %r30, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r30, 0
	li %r4, 136
	addi %r6, %r30, 984
	li %r7, 2
	addi %r8, %r30, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r30, 0
	li %r4, 136
	addi %r6, %r25, 0
	addi %r7, %r26, 0
	addi %r8, %r30, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r30, 0
	li %r4, 136
	addi %r6, %r23, 0
	addi %r7, %r24, 0
	addi %r8, %r30, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r30, 0
	li %r4, 136
	li %r6, 31
	addi %r7, %r30, 200
	bl {vg_keccak_pad_scratch}
	addi %r3, %r30, 0
	li %r4, 136
	li %r5, 0
	addi %r6, %r30, 840
	li %r7, 64
	addi %r8, %r30, 200
	bl {vg_keccak_squeeze_scratch}
	addi %r3, %r22, 0
	addi %r4, %r30, 840
	addi %r5, %r27, 0
	addi %r6, %r29, 0
	bl {vg_mldsa44_verify_prepared}
	ld %r0, 976(%r30)
	ld %r22, 904(%r30)
	ld %r23, 912(%r30)
	ld %r24, 920(%r30)
	ld %r25, 928(%r30)
	ld %r26, 936(%r30)
	ld %r27, 944(%r30)
	ld %r28, 952(%r30)
	ld %r29, 960(%r30)
	ld %r30, 968(%r30)
	mtlr %r0
21:
	blr
