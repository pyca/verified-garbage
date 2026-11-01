// The functions of `src/mldsa65.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa65_keygen:
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
	li %r0, 6
	stb %r0, 920(%r31)
	li %r0, 5
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
	li %r0, 4
	stb %r0, 1184(%r31)
	li %r0, 0
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
	li %r0, 0
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
	li %r0, 1
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
	li %r0, 2
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
	li %r0, 3
	stb %r0, 1184(%r31)
	li %r0, 1
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
	li %r0, 4
	stb %r0, 1184(%r31)
	li %r0, 1
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
	li %r0, 0
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
	li %r0, 1
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
	li %r0, 2
	stb %r0, 1184(%r31)
	li %r0, 2
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
	li %r0, 3
	stb %r0, 1184(%r31)
	li %r0, 2
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
	li %r0, 4
	stb %r0, 1184(%r31)
	li %r0, 2
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
	li %r0, 0
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
	li %r0, 1
	stb %r0, 1184(%r31)
	li %r0, 3
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 20480
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
	li %r0, 2
	stb %r0, 1184(%r31)
	li %r0, 3
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 21504
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
	li %r0, 3
	stb %r0, 1184(%r31)
	li %r0, 3
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 22528
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
	li %r0, 4
	stb %r0, 1184(%r31)
	li %r0, 3
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 23552
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
	li %r0, 0
	stb %r0, 1184(%r31)
	li %r0, 4
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 24576
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
	li %r0, 1
	stb %r0, 1184(%r31)
	li %r0, 4
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 25600
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
	li %r0, 2
	stb %r0, 1184(%r31)
	li %r0, 4
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 26624
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
	li %r0, 3
	stb %r0, 1184(%r31)
	li %r0, 4
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 27648
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
	li %r0, 4
	stb %r0, 1184(%r31)
	li %r0, 4
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 28672
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
	ori %r4, %r4, 28672
	add %r4, %r31, %r4
	li %r5, 256
226:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 226b
	li %r0, 0
	stb %r0, 1184(%r31)
	li %r0, 5
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 29696
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
	ori %r4, %r4, 29696
	add %r4, %r31, %r4
	li %r5, 256
227:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 227b
	li %r0, 1
	stb %r0, 1184(%r31)
	li %r0, 5
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 30720
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
	ori %r4, %r4, 30720
	add %r4, %r31, %r4
	li %r5, 256
228:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 228b
	li %r0, 2
	stb %r0, 1184(%r31)
	li %r0, 5
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 31744
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
	ori %r4, %r4, 31744
	add %r4, %r31, %r4
	li %r5, 256
229:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 229b
	li %r0, 3
	stb %r0, 1184(%r31)
	li %r0, 5
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 32768
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
	ori %r4, %r4, 32768
	add %r4, %r31, %r4
	li %r5, 256
230:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 230b
	li %r0, 4
	stb %r0, 1184(%r31)
	li %r0, 5
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 33792
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
	ori %r4, %r4, 33792
	add %r4, %r31, %r4
	li %r5, 256
231:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 231b
	li %r0, 0
	stb %r0, 1280(%r31)
	lis %r3, 0
	ori %r3, %r3, 1216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4
	lis %r5, 0
	ori %r5, %r5, 34816
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
	ori %r4, %r4, 34816
	add %r4, %r31, %r4
	li %r5, 256
232:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 232b
	li %r0, 1
	stb %r0, 1280(%r31)
	lis %r3, 0
	ori %r3, %r3, 1216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4
	lis %r5, 0
	ori %r5, %r5, 35840
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
	ori %r4, %r4, 35840
	add %r4, %r31, %r4
	li %r5, 256
233:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 233b
	li %r0, 2
	stb %r0, 1280(%r31)
	lis %r3, 0
	ori %r3, %r3, 1216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4
	lis %r5, 0
	ori %r5, %r5, 36864
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
	ori %r4, %r4, 36864
	add %r4, %r31, %r4
	li %r5, 256
234:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 234b
	li %r0, 3
	stb %r0, 1280(%r31)
	lis %r3, 0
	ori %r3, %r3, 1216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4
	lis %r5, 0
	ori %r5, %r5, 37888
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
	ori %r4, %r4, 37888
	add %r4, %r31, %r4
	li %r5, 256
235:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 235b
	li %r0, 4
	stb %r0, 1280(%r31)
	lis %r3, 0
	ori %r3, %r3, 1216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4
	lis %r5, 0
	ori %r5, %r5, 38912
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
	ori %r4, %r4, 38912
	add %r4, %r31, %r4
	li %r5, 256
236:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 236b
	li %r0, 5
	stb %r0, 1280(%r31)
	lis %r3, 0
	ori %r3, %r3, 1216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4
	lis %r5, 0
	ori %r5, %r5, 39936
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
	ori %r4, %r4, 39936
	add %r4, %r31, %r4
	li %r5, 256
237:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 237b
	li %r0, 6
	stb %r0, 1280(%r31)
	lis %r3, 0
	ori %r3, %r3, 1216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4
	lis %r5, 0
	ori %r5, %r5, 40960
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
	ori %r4, %r4, 40960
	add %r4, %r31, %r4
	li %r5, 256
238:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 238b
	li %r0, 7
	stb %r0, 1280(%r31)
	lis %r3, 0
	ori %r3, %r3, 1216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4
	lis %r5, 0
	ori %r5, %r5, 41984
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
	ori %r4, %r4, 41984
	add %r4, %r31, %r4
	li %r5, 256
239:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 239b
	li %r0, 8
	stb %r0, 1280(%r31)
	lis %r3, 0
	ori %r3, %r3, 1216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4
	lis %r5, 0
	ori %r5, %r5, 43008
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
	ori %r4, %r4, 43008
	add %r4, %r31, %r4
	li %r5, 256
240:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 240b
	li %r0, 9
	stb %r0, 1280(%r31)
	lis %r3, 0
	ori %r3, %r3, 1216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4
	lis %r5, 0
	ori %r5, %r5, 44032
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
	ori %r4, %r4, 44032
	add %r4, %r31, %r4
	li %r5, 256
241:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 241b
	li %r0, 10
	stb %r0, 1280(%r31)
	lis %r3, 0
	ori %r3, %r3, 1216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4
	lis %r5, 0
	ori %r5, %r5, 45056
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
	ori %r4, %r4, 45056
	add %r4, %r31, %r4
	li %r5, 256
242:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 242b
	addi %r3, %r31, 1024
	addi %r4, %r29, 0
	li %r5, 32
243:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 243b
	addi %r3, %r31, 1024
	addi %r4, %r28, 0
	li %r5, 32
244:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 244b
	addi %r3, %r31, 1120
	addi %r4, %r28, 32
	li %r5, 32
245:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 245b
	lis %r3, 0
	ori %r3, %r3, 34816
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4
	lis %r5, 0
	ori %r5, %r5, 4
	lis %r6, 0
	ori %r6, %r6, 128
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 128
	bl {vg_mldsa_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 35840
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4
	lis %r5, 0
	ori %r5, %r5, 4
	lis %r6, 0
	ori %r6, %r6, 256
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 128
	bl {vg_mldsa_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 36864
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4
	lis %r5, 0
	ori %r5, %r5, 4
	lis %r6, 0
	ori %r6, %r6, 384
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 128
	bl {vg_mldsa_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 37888
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4
	lis %r5, 0
	ori %r5, %r5, 4
	lis %r6, 0
	ori %r6, %r6, 512
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 128
	bl {vg_mldsa_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 38912
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4
	lis %r5, 0
	ori %r5, %r5, 4
	lis %r6, 0
	ori %r6, %r6, 640
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 128
	bl {vg_mldsa_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 39936
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4
	lis %r5, 0
	ori %r5, %r5, 4
	lis %r6, 0
	ori %r6, %r6, 768
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 128
	bl {vg_mldsa_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 40960
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4
	lis %r5, 0
	ori %r5, %r5, 4
	lis %r6, 0
	ori %r6, %r6, 896
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 128
	bl {vg_mldsa_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 41984
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4
	lis %r5, 0
	ori %r5, %r5, 4
	lis %r6, 0
	ori %r6, %r6, 1024
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 128
	bl {vg_mldsa_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 43008
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4
	lis %r5, 0
	ori %r5, %r5, 4
	lis %r6, 0
	ori %r6, %r6, 1152
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 128
	bl {vg_mldsa_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 44032
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4
	lis %r5, 0
	ori %r5, %r5, 4
	lis %r6, 0
	ori %r6, %r6, 1280
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 128
	bl {vg_mldsa_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 45056
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4
	lis %r5, 0
	ori %r5, %r5, 4
	lis %r6, 0
	ori %r6, %r6, 1408
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 128
	bl {vg_mldsa_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 34816
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2048
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 35840
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2048
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 36864
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2048
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 37888
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2048
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 38912
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2048
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4096
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 34816
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 5120
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 35840
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 6144
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 36864
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 7168
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 37888
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 8192
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 38912
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2048
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 39936
	add %r4, %r31, %r4
	bl {vg_mldsa_add}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 47104
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 48128
	add %r5, %r31, %r5
	bl {vg_mldsa_power2round}
	lis %r3, 0
	ori %r3, %r3, 47104
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
	ori %r3, %r3, 48128
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4095
	lis %r5, 0
	ori %r5, %r5, 4096
	lis %r6, 0
	ori %r6, %r6, 1536
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 416
	bl {vg_mldsa_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 9216
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 34816
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 10240
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 35840
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 11264
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 36864
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 12288
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 37888
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 13312
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 38912
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2048
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 40960
	add %r4, %r31, %r4
	bl {vg_mldsa_add}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 47104
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 48128
	add %r5, %r31, %r5
	bl {vg_mldsa_power2round}
	lis %r3, 0
	ori %r3, %r3, 47104
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
	ori %r3, %r3, 48128
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4095
	lis %r5, 0
	ori %r5, %r5, 4096
	lis %r6, 0
	ori %r6, %r6, 1952
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 416
	bl {vg_mldsa_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 14336
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 34816
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 15360
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 35840
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 16384
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 36864
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 17408
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 37888
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 18432
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 38912
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2048
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 41984
	add %r4, %r31, %r4
	bl {vg_mldsa_add}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 47104
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 48128
	add %r5, %r31, %r5
	bl {vg_mldsa_power2round}
	lis %r3, 0
	ori %r3, %r3, 47104
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
	ori %r3, %r3, 48128
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4095
	lis %r5, 0
	ori %r5, %r5, 4096
	lis %r6, 0
	ori %r6, %r6, 2368
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 416
	bl {vg_mldsa_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 19456
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 34816
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 20480
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 35840
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 21504
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 36864
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 22528
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 37888
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 23552
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 38912
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2048
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 43008
	add %r4, %r31, %r4
	bl {vg_mldsa_add}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 47104
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 48128
	add %r5, %r31, %r5
	bl {vg_mldsa_power2round}
	lis %r3, 0
	ori %r3, %r3, 47104
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
	ori %r3, %r3, 48128
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4095
	lis %r5, 0
	ori %r5, %r5, 4096
	lis %r6, 0
	ori %r6, %r6, 2784
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 416
	bl {vg_mldsa_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 24576
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 34816
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 25600
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 35840
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 26624
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 36864
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 27648
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 37888
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 28672
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 38912
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2048
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 44032
	add %r4, %r31, %r4
	bl {vg_mldsa_add}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 47104
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 48128
	add %r5, %r31, %r5
	bl {vg_mldsa_power2round}
	lis %r3, 0
	ori %r3, %r3, 47104
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 1023
	lis %r5, 0
	ori %r5, %r5, 1312
	add %r5, %r29, %r5
	lis %r6, 0
	ori %r6, %r6, 320
	bl {vg_mldsa_simple_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 48128
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4095
	lis %r5, 0
	ori %r5, %r5, 4096
	lis %r6, 0
	ori %r6, %r6, 3200
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 416
	bl {vg_mldsa_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 29696
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 34816
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 30720
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 35840
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 31744
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 36864
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 32768
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 37888
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 33792
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 38912
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2048
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 45056
	add %r4, %r31, %r4
	bl {vg_mldsa_add}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 47104
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 48128
	add %r5, %r31, %r5
	bl {vg_mldsa_power2round}
	lis %r3, 0
	ori %r3, %r3, 47104
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 1023
	lis %r5, 0
	ori %r5, %r5, 1632
	add %r5, %r29, %r5
	lis %r6, 0
	ori %r6, %r6, 320
	bl {vg_mldsa_simple_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 48128
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4095
	lis %r5, 0
	ori %r5, %r5, 4096
	lis %r6, 0
	ori %r6, %r6, 3616
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
	li %r7, 1952
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

vg_mldsa65_sign:
	mflr %r0
	std %r24, 840(%r7)
	std %r25, 848(%r7)
	std %r26, 856(%r7)
	std %r27, 864(%r7)
	std %r28, 872(%r7)
	std %r29, 880(%r7)
	std %r30, 888(%r7)
	std %r31, 896(%r7)
	std %r0, 904(%r7)
	addi %r30, %r3, 0
	addi %r29, %r4, 0
	addi %r28, %r5, 0
	addi %r31, %r7, 0
	std %r6, 912(%r31)
	li %r24, 1
	addi %r3, %r30, 0
	addi %r4, %r31, 920
	li %r5, 32
20:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 20b
	li %r0, 0
	stb %r0, 952(%r31)
	li %r0, 0
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 50176
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 1
	stb %r0, 952(%r31)
	li %r0, 0
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 51200
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 2
	stb %r0, 952(%r31)
	li %r0, 0
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 52224
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 3
	stb %r0, 952(%r31)
	li %r0, 0
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 53248
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 4
	stb %r0, 952(%r31)
	li %r0, 0
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 54272
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 0
	stb %r0, 952(%r31)
	li %r0, 1
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 55296
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 1
	stb %r0, 952(%r31)
	li %r0, 1
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 56320
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 2
	stb %r0, 952(%r31)
	li %r0, 1
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 57344
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 3
	stb %r0, 952(%r31)
	li %r0, 1
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 58368
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 4
	stb %r0, 952(%r31)
	li %r0, 1
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 59392
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 0
	stb %r0, 952(%r31)
	li %r0, 2
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 60416
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 1
	stb %r0, 952(%r31)
	li %r0, 2
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 61440
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 2
	stb %r0, 952(%r31)
	li %r0, 2
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 62464
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 3
	stb %r0, 952(%r31)
	li %r0, 2
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 63488
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 4
	stb %r0, 952(%r31)
	li %r0, 2
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 64512
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 0
	stb %r0, 952(%r31)
	li %r0, 3
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 1
	stb %r0, 952(%r31)
	li %r0, 3
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 1024
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 2
	stb %r0, 952(%r31)
	li %r0, 3
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 2048
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 3
	stb %r0, 952(%r31)
	li %r0, 3
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 4
	stb %r0, 952(%r31)
	li %r0, 3
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 4096
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 0
	stb %r0, 952(%r31)
	li %r0, 4
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 5120
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 1
	stb %r0, 952(%r31)
	li %r0, 4
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 6144
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 2
	stb %r0, 952(%r31)
	li %r0, 4
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 7168
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 3
	stb %r0, 952(%r31)
	li %r0, 4
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 8192
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 4
	stb %r0, 952(%r31)
	li %r0, 4
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 9216
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 0
	stb %r0, 952(%r31)
	li %r0, 5
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 10240
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 1
	stb %r0, 952(%r31)
	li %r0, 5
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 11264
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 2
	stb %r0, 952(%r31)
	li %r0, 5
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 12288
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 3
	stb %r0, 952(%r31)
	li %r0, 5
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 13312
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 4
	stb %r0, 952(%r31)
	li %r0, 5
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 14336
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	cmpldi %cr0, %r24, 0
	bne %cr0, 21f
	b 22f
21:
	addi %r3, %r28, 0
	addi %r4, %r31, 2048
	li %r5, 32
23:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 23b
	addi %r3, %r29, 0
	addi %r4, %r31, 2080
	li %r5, 64
24:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 24b
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
	addi %r6, %r30, 32
	li %r7, 32
	addi %r8, %r31, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r31, 0
	li %r4, 136
	addi %r6, %r31, 2048
	li %r7, 96
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
	addi %r6, %r31, 960
	li %r7, 64
	addi %r8, %r31, 200
	bl {vg_keccak_squeeze_scratch}
	ld %r28, 912(%r31)
	lis %r3, 0
	ori %r3, %r3, 128
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 128
	lis %r5, 0
	ori %r5, %r5, 4
	lis %r6, 0
	ori %r6, %r6, 4
	lis %r7, 0
	ori %r7, %r7, 32768
	add %r7, %r31, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 32768
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 256
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 128
	lis %r5, 0
	ori %r5, %r5, 4
	lis %r6, 0
	ori %r6, %r6, 4
	lis %r7, 0
	ori %r7, %r7, 33792
	add %r7, %r31, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 33792
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 384
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 128
	lis %r5, 0
	ori %r5, %r5, 4
	lis %r6, 0
	ori %r6, %r6, 4
	lis %r7, 0
	ori %r7, %r7, 34816
	add %r7, %r31, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 34816
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 512
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 128
	lis %r5, 0
	ori %r5, %r5, 4
	lis %r6, 0
	ori %r6, %r6, 4
	lis %r7, 0
	ori %r7, %r7, 35840
	add %r7, %r31, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 35840
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 640
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 128
	lis %r5, 0
	ori %r5, %r5, 4
	lis %r6, 0
	ori %r6, %r6, 4
	lis %r7, 0
	ori %r7, %r7, 36864
	add %r7, %r31, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 36864
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 768
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 128
	lis %r5, 0
	ori %r5, %r5, 4
	lis %r6, 0
	ori %r6, %r6, 4
	lis %r7, 0
	ori %r7, %r7, 37888
	add %r7, %r31, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 37888
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 896
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 128
	lis %r5, 0
	ori %r5, %r5, 4
	lis %r6, 0
	ori %r6, %r6, 4
	lis %r7, 0
	ori %r7, %r7, 38912
	add %r7, %r31, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 38912
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 1024
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 128
	lis %r5, 0
	ori %r5, %r5, 4
	lis %r6, 0
	ori %r6, %r6, 4
	lis %r7, 0
	ori %r7, %r7, 39936
	add %r7, %r31, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 39936
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 128
	lis %r5, 0
	ori %r5, %r5, 4
	lis %r6, 0
	ori %r6, %r6, 4
	lis %r7, 0
	ori %r7, %r7, 40960
	add %r7, %r31, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 40960
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 1280
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 128
	lis %r5, 0
	ori %r5, %r5, 4
	lis %r6, 0
	ori %r6, %r6, 4
	lis %r7, 0
	ori %r7, %r7, 41984
	add %r7, %r31, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 41984
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 1408
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 128
	lis %r5, 0
	ori %r5, %r5, 4
	lis %r6, 0
	ori %r6, %r6, 4
	lis %r7, 0
	ori %r7, %r7, 43008
	add %r7, %r31, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 43008
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 1536
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 416
	lis %r5, 0
	ori %r5, %r5, 4095
	lis %r6, 0
	ori %r6, %r6, 4096
	lis %r7, 0
	ori %r7, %r7, 44032
	add %r7, %r31, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 44032
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 1952
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 416
	lis %r5, 0
	ori %r5, %r5, 4095
	lis %r6, 0
	ori %r6, %r6, 4096
	lis %r7, 0
	ori %r7, %r7, 45056
	add %r7, %r31, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 45056
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 2368
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 416
	lis %r5, 0
	ori %r5, %r5, 4095
	lis %r6, 0
	ori %r6, %r6, 4096
	lis %r7, 0
	ori %r7, %r7, 46080
	add %r7, %r31, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 46080
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 2784
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 416
	lis %r5, 0
	ori %r5, %r5, 4095
	lis %r6, 0
	ori %r6, %r6, 4096
	lis %r7, 0
	ori %r7, %r7, 47104
	add %r7, %r31, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 47104
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 3200
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 416
	lis %r5, 0
	ori %r5, %r5, 4095
	lis %r6, 0
	ori %r6, %r6, 4096
	lis %r7, 0
	ori %r7, %r7, 48128
	add %r7, %r31, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 48128
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 3616
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 416
	lis %r5, 0
	ori %r5, %r5, 4095
	lis %r6, 0
	ori %r6, %r6, 4096
	lis %r7, 0
	ori %r7, %r7, 49152
	add %r7, %r31, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 49152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	li %r27, 0
	li %r25, 814
25:
	addi %r3, %r27, 0
	stb %r3, 1024(%r31)
	rldicl %r3, %r3, 56, 8
	stb %r3, 1025(%r31)
	lis %r3, 0
	ori %r3, %r3, 960
	add %r3, %r31, %r3
	lis %r4, 8
	ori %r4, %r4, 0
	lis %r5, 0
	ori %r5, %r5, 16384
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 3072
	add %r6, %r31, %r6
	bl {vg_mldsa_expand_mask_poly}
	addi %r3, %r31, 16384
	addi %r4, %r31, 21504
	li %r5, 1024
26:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 26b
	lis %r3, 0
	ori %r3, %r3, 21504
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	addi %r3, %r27, 1
	stb %r3, 1024(%r31)
	rldicl %r3, %r3, 56, 8
	stb %r3, 1025(%r31)
	lis %r3, 0
	ori %r3, %r3, 960
	add %r3, %r31, %r3
	lis %r4, 8
	ori %r4, %r4, 0
	lis %r5, 0
	ori %r5, %r5, 17408
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 3072
	add %r6, %r31, %r6
	bl {vg_mldsa_expand_mask_poly}
	addi %r3, %r31, 17408
	addi %r4, %r31, 22528
	li %r5, 1024
27:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 27b
	lis %r3, 0
	ori %r3, %r3, 22528
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	addi %r3, %r27, 2
	stb %r3, 1024(%r31)
	rldicl %r3, %r3, 56, 8
	stb %r3, 1025(%r31)
	lis %r3, 0
	ori %r3, %r3, 960
	add %r3, %r31, %r3
	lis %r4, 8
	ori %r4, %r4, 0
	lis %r5, 0
	ori %r5, %r5, 18432
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 3072
	add %r6, %r31, %r6
	bl {vg_mldsa_expand_mask_poly}
	addi %r3, %r31, 18432
	addi %r4, %r31, 23552
	li %r5, 1024
28:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 28b
	lis %r3, 0
	ori %r3, %r3, 23552
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	addi %r3, %r27, 3
	stb %r3, 1024(%r31)
	rldicl %r3, %r3, 56, 8
	stb %r3, 1025(%r31)
	lis %r3, 0
	ori %r3, %r3, 960
	add %r3, %r31, %r3
	lis %r4, 8
	ori %r4, %r4, 0
	lis %r5, 0
	ori %r5, %r5, 19456
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 3072
	add %r6, %r31, %r6
	bl {vg_mldsa_expand_mask_poly}
	addi %r3, %r31, 19456
	addi %r4, %r31, 24576
	li %r5, 1024
29:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 29b
	lis %r3, 0
	ori %r3, %r3, 24576
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	addi %r3, %r27, 4
	stb %r3, 1024(%r31)
	rldicl %r3, %r3, 56, 8
	stb %r3, 1025(%r31)
	lis %r3, 0
	ori %r3, %r3, 960
	add %r3, %r31, %r3
	lis %r4, 8
	ori %r4, %r4, 0
	lis %r5, 0
	ori %r5, %r5, 20480
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 3072
	add %r6, %r31, %r6
	bl {vg_mldsa_expand_mask_poly}
	addi %r3, %r31, 20480
	addi %r4, %r31, 25600
	li %r5, 1024
210:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 210b
	lis %r3, 0
	ori %r3, %r3, 25600
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 50176
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 21504
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 51200
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 22528
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 52224
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 23552
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 53248
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 24576
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 54272
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 25600
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 27648
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 55296
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 21504
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 27648
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 56320
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 22528
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 27648
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 57344
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 23552
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 27648
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 58368
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 24576
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 27648
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 59392
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 25600
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 27648
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 28672
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 60416
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 21504
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 28672
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 61440
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 22528
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 28672
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 62464
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 23552
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 28672
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 63488
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 24576
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 28672
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 64512
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 25600
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 28672
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 29696
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 21504
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 29696
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 1024
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 22528
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 29696
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 2048
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 23552
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 29696
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 24576
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 29696
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 4096
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 25600
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 29696
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 30720
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 5120
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 21504
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 30720
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 6144
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 22528
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 30720
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 7168
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 23552
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 30720
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 8192
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 24576
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 30720
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 9216
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 25600
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 30720
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 31744
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 10240
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 21504
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 31744
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 11264
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 22528
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 31744
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 12288
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 23552
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 31744
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 13312
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 24576
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 31744
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 14336
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 25600
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 31744
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 3
	ori %r4, %r4, 65280
	lis %r5, 0
	ori %r5, %r5, 6144
	add %r5, %r31, %r5
	bl {vg_mldsa_high_bits}
	lis %r3, 0
	ori %r3, %r3, 6144
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 15
	lis %r5, 0
	ori %r5, %r5, 2048
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 128
	bl {vg_mldsa_simple_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 27648
	add %r3, %r31, %r3
	lis %r4, 3
	ori %r4, %r4, 65280
	lis %r5, 0
	ori %r5, %r5, 6144
	add %r5, %r31, %r5
	bl {vg_mldsa_high_bits}
	lis %r3, 0
	ori %r3, %r3, 6144
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 15
	lis %r5, 0
	ori %r5, %r5, 2176
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 128
	bl {vg_mldsa_simple_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 28672
	add %r3, %r31, %r3
	lis %r4, 3
	ori %r4, %r4, 65280
	lis %r5, 0
	ori %r5, %r5, 6144
	add %r5, %r31, %r5
	bl {vg_mldsa_high_bits}
	lis %r3, 0
	ori %r3, %r3, 6144
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 15
	lis %r5, 0
	ori %r5, %r5, 2304
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 128
	bl {vg_mldsa_simple_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 29696
	add %r3, %r31, %r3
	lis %r4, 3
	ori %r4, %r4, 65280
	lis %r5, 0
	ori %r5, %r5, 6144
	add %r5, %r31, %r5
	bl {vg_mldsa_high_bits}
	lis %r3, 0
	ori %r3, %r3, 6144
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 15
	lis %r5, 0
	ori %r5, %r5, 2432
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 128
	bl {vg_mldsa_simple_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 30720
	add %r3, %r31, %r3
	lis %r4, 3
	ori %r4, %r4, 65280
	lis %r5, 0
	ori %r5, %r5, 6144
	add %r5, %r31, %r5
	bl {vg_mldsa_high_bits}
	lis %r3, 0
	ori %r3, %r3, 6144
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 15
	lis %r5, 0
	ori %r5, %r5, 2560
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 128
	bl {vg_mldsa_simple_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 31744
	add %r3, %r31, %r3
	lis %r4, 3
	ori %r4, %r4, 65280
	lis %r5, 0
	ori %r5, %r5, 6144
	add %r5, %r31, %r5
	bl {vg_mldsa_high_bits}
	lis %r3, 0
	ori %r3, %r3, 6144
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 15
	lis %r5, 0
	ori %r5, %r5, 2688
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 128
	bl {vg_mldsa_simple_bit_pack}
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
	li %r7, 64
	addi %r8, %r31, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r31, 0
	li %r4, 136
	addi %r6, %r31, 2048
	li %r7, 768
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
	addi %r6, %r31, 1040
	li %r7, 48
	addi %r8, %r31, 200
	bl {vg_keccak_squeeze_scratch}
	lis %r3, 0
	ori %r3, %r3, 1040
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 48
	lis %r5, 0
	ori %r5, %r5, 49
	lis %r6, 0
	ori %r6, %r6, 5120
	add %r6, %r31, %r6
	lis %r7, 0
	ori %r7, %r7, 3072
	add %r7, %r31, %r7
	bl {vg_mldsa_sample_in_ball}
	cmplwi %cr0, %r3, 0
	bne %cr0, 211f
	li %r24, 0
	li %r25, 1
	b 212f
211:
	lis %r3, 0
	ori %r3, %r3, 5120
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	li %r24, 1
	li %r26, 0
	lis %r3, 0
	ori %r3, %r3, 6144
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 5120
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 32768
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 6144
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 16384
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 6144
	add %r4, %r31, %r4
	bl {vg_mldsa_add}
	lis %r3, 0
	ori %r3, %r3, 16384
	add %r3, %r31, %r3
	lis %r4, 7
	ori %r4, %r4, 65340
	bl {vg_mldsa_norm_lt}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	cmpldi %cr0, %r24, 0
	bne %cr0, 213f
	b 214f
213:
	lis %r3, 0
	ori %r3, %r3, 6144
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 5120
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 33792
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 6144
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 17408
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 6144
	add %r4, %r31, %r4
	bl {vg_mldsa_add}
	lis %r3, 0
	ori %r3, %r3, 17408
	add %r3, %r31, %r3
	lis %r4, 7
	ori %r4, %r4, 65340
	bl {vg_mldsa_norm_lt}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	cmpldi %cr0, %r24, 0
	bne %cr0, 215f
	b 216f
215:
	lis %r3, 0
	ori %r3, %r3, 6144
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 5120
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 34816
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 6144
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 18432
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 6144
	add %r4, %r31, %r4
	bl {vg_mldsa_add}
	lis %r3, 0
	ori %r3, %r3, 18432
	add %r3, %r31, %r3
	lis %r4, 7
	ori %r4, %r4, 65340
	bl {vg_mldsa_norm_lt}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	cmpldi %cr0, %r24, 0
	bne %cr0, 217f
	b 218f
217:
	lis %r3, 0
	ori %r3, %r3, 6144
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 5120
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 35840
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 6144
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 19456
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 6144
	add %r4, %r31, %r4
	bl {vg_mldsa_add}
	lis %r3, 0
	ori %r3, %r3, 19456
	add %r3, %r31, %r3
	lis %r4, 7
	ori %r4, %r4, 65340
	bl {vg_mldsa_norm_lt}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	cmpldi %cr0, %r24, 0
	bne %cr0, 219f
	b 220f
219:
	lis %r3, 0
	ori %r3, %r3, 6144
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 5120
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 36864
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 6144
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 20480
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 6144
	add %r4, %r31, %r4
	bl {vg_mldsa_add}
	lis %r3, 0
	ori %r3, %r3, 20480
	add %r3, %r31, %r3
	lis %r4, 7
	ori %r4, %r4, 65340
	bl {vg_mldsa_norm_lt}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	cmpldi %cr0, %r24, 0
	bne %cr0, 221f
	b 222f
221:
222:
220:
218:
216:
214:
	cmpldi %cr0, %r24, 0
	bne %cr0, 223f
	b 224f
223:
	lis %r3, 0
	ori %r3, %r3, 6144
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 5120
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 37888
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 6144
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 6144
	add %r4, %r31, %r4
	bl {vg_mldsa_sub}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 3
	ori %r4, %r4, 65280
	lis %r5, 0
	ori %r5, %r5, 7168
	add %r5, %r31, %r5
	bl {vg_mldsa_low_bits}
	lis %r3, 0
	ori %r3, %r3, 7168
	add %r3, %r31, %r3
	lis %r4, 3
	ori %r4, %r4, 65084
	bl {vg_mldsa_norm_lt}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	cmpldi %cr0, %r24, 0
	bne %cr0, 225f
	b 226f
225:
	lis %r3, 0
	ori %r3, %r3, 6144
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 5120
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 38912
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 6144
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 27648
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 6144
	add %r4, %r31, %r4
	bl {vg_mldsa_sub}
	lis %r3, 0
	ori %r3, %r3, 27648
	add %r3, %r31, %r3
	lis %r4, 3
	ori %r4, %r4, 65280
	lis %r5, 0
	ori %r5, %r5, 7168
	add %r5, %r31, %r5
	bl {vg_mldsa_low_bits}
	lis %r3, 0
	ori %r3, %r3, 7168
	add %r3, %r31, %r3
	lis %r4, 3
	ori %r4, %r4, 65084
	bl {vg_mldsa_norm_lt}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	cmpldi %cr0, %r24, 0
	bne %cr0, 227f
	b 228f
227:
	lis %r3, 0
	ori %r3, %r3, 6144
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 5120
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 39936
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 6144
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 28672
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 6144
	add %r4, %r31, %r4
	bl {vg_mldsa_sub}
	lis %r3, 0
	ori %r3, %r3, 28672
	add %r3, %r31, %r3
	lis %r4, 3
	ori %r4, %r4, 65280
	lis %r5, 0
	ori %r5, %r5, 7168
	add %r5, %r31, %r5
	bl {vg_mldsa_low_bits}
	lis %r3, 0
	ori %r3, %r3, 7168
	add %r3, %r31, %r3
	lis %r4, 3
	ori %r4, %r4, 65084
	bl {vg_mldsa_norm_lt}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	cmpldi %cr0, %r24, 0
	bne %cr0, 229f
	b 230f
229:
	lis %r3, 0
	ori %r3, %r3, 6144
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 5120
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 40960
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 6144
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 29696
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 6144
	add %r4, %r31, %r4
	bl {vg_mldsa_sub}
	lis %r3, 0
	ori %r3, %r3, 29696
	add %r3, %r31, %r3
	lis %r4, 3
	ori %r4, %r4, 65280
	lis %r5, 0
	ori %r5, %r5, 7168
	add %r5, %r31, %r5
	bl {vg_mldsa_low_bits}
	lis %r3, 0
	ori %r3, %r3, 7168
	add %r3, %r31, %r3
	lis %r4, 3
	ori %r4, %r4, 65084
	bl {vg_mldsa_norm_lt}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	cmpldi %cr0, %r24, 0
	bne %cr0, 231f
	b 232f
231:
	lis %r3, 0
	ori %r3, %r3, 6144
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 5120
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 41984
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 6144
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 30720
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 6144
	add %r4, %r31, %r4
	bl {vg_mldsa_sub}
	lis %r3, 0
	ori %r3, %r3, 30720
	add %r3, %r31, %r3
	lis %r4, 3
	ori %r4, %r4, 65280
	lis %r5, 0
	ori %r5, %r5, 7168
	add %r5, %r31, %r5
	bl {vg_mldsa_low_bits}
	lis %r3, 0
	ori %r3, %r3, 7168
	add %r3, %r31, %r3
	lis %r4, 3
	ori %r4, %r4, 65084
	bl {vg_mldsa_norm_lt}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	cmpldi %cr0, %r24, 0
	bne %cr0, 233f
	b 234f
233:
	lis %r3, 0
	ori %r3, %r3, 6144
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 5120
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 43008
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 6144
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 31744
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 6144
	add %r4, %r31, %r4
	bl {vg_mldsa_sub}
	lis %r3, 0
	ori %r3, %r3, 31744
	add %r3, %r31, %r3
	lis %r4, 3
	ori %r4, %r4, 65280
	lis %r5, 0
	ori %r5, %r5, 7168
	add %r5, %r31, %r5
	bl {vg_mldsa_low_bits}
	lis %r3, 0
	ori %r3, %r3, 7168
	add %r3, %r31, %r3
	lis %r4, 3
	ori %r4, %r4, 65084
	bl {vg_mldsa_norm_lt}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	cmpldi %cr0, %r24, 0
	bne %cr0, 235f
	b 236f
235:
236:
234:
232:
230:
228:
226:
	cmpldi %cr0, %r24, 0
	bne %cr0, 237f
	b 238f
237:
	lis %r3, 0
	ori %r3, %r3, 8192
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 5120
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 44032
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 8192
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 8192
	add %r3, %r31, %r3
	lis %r4, 3
	ori %r4, %r4, 65280
	bl {vg_mldsa_norm_lt}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	addi %r3, %r31, 8192
	addi %r4, %r31, 9216
	li %r5, 1024
239:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 239b
	lis %r3, 0
	ori %r3, %r3, 9216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 8192
	add %r4, %r31, %r4
	bl {vg_mldsa_sub}
	lis %r3, 0
	ori %r3, %r3, 9216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 8192
	add %r4, %r31, %r4
	bl {vg_mldsa_sub}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 8192
	add %r4, %r31, %r4
	bl {vg_mldsa_add}
	lis %r3, 0
	ori %r3, %r3, 9216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 26624
	add %r4, %r31, %r4
	lis %r5, 3
	ori %r5, %r5, 65280
	lis %r6, 0
	ori %r6, %r6, 10240
	add %r6, %r31, %r6
	bl {vg_mldsa_make_hint}
	rlwinm %r3, %r3, 0, 0, 31
	add %r26, %r26, %r3
	lis %r3, 0
	ori %r3, %r3, 8192
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 5120
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 45056
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 8192
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 8192
	add %r3, %r31, %r3
	lis %r4, 3
	ori %r4, %r4, 65280
	bl {vg_mldsa_norm_lt}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	addi %r3, %r31, 8192
	addi %r4, %r31, 9216
	li %r5, 1024
240:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 240b
	lis %r3, 0
	ori %r3, %r3, 9216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 8192
	add %r4, %r31, %r4
	bl {vg_mldsa_sub}
	lis %r3, 0
	ori %r3, %r3, 9216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 8192
	add %r4, %r31, %r4
	bl {vg_mldsa_sub}
	lis %r3, 0
	ori %r3, %r3, 27648
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 8192
	add %r4, %r31, %r4
	bl {vg_mldsa_add}
	lis %r3, 0
	ori %r3, %r3, 9216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 27648
	add %r4, %r31, %r4
	lis %r5, 3
	ori %r5, %r5, 65280
	lis %r6, 0
	ori %r6, %r6, 11264
	add %r6, %r31, %r6
	bl {vg_mldsa_make_hint}
	rlwinm %r3, %r3, 0, 0, 31
	add %r26, %r26, %r3
	lis %r3, 0
	ori %r3, %r3, 8192
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 5120
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 46080
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 8192
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 8192
	add %r3, %r31, %r3
	lis %r4, 3
	ori %r4, %r4, 65280
	bl {vg_mldsa_norm_lt}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	addi %r3, %r31, 8192
	addi %r4, %r31, 9216
	li %r5, 1024
241:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 241b
	lis %r3, 0
	ori %r3, %r3, 9216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 8192
	add %r4, %r31, %r4
	bl {vg_mldsa_sub}
	lis %r3, 0
	ori %r3, %r3, 9216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 8192
	add %r4, %r31, %r4
	bl {vg_mldsa_sub}
	lis %r3, 0
	ori %r3, %r3, 28672
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 8192
	add %r4, %r31, %r4
	bl {vg_mldsa_add}
	lis %r3, 0
	ori %r3, %r3, 9216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 28672
	add %r4, %r31, %r4
	lis %r5, 3
	ori %r5, %r5, 65280
	lis %r6, 0
	ori %r6, %r6, 12288
	add %r6, %r31, %r6
	bl {vg_mldsa_make_hint}
	rlwinm %r3, %r3, 0, 0, 31
	add %r26, %r26, %r3
	lis %r3, 0
	ori %r3, %r3, 8192
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 5120
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 47104
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 8192
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 8192
	add %r3, %r31, %r3
	lis %r4, 3
	ori %r4, %r4, 65280
	bl {vg_mldsa_norm_lt}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	addi %r3, %r31, 8192
	addi %r4, %r31, 9216
	li %r5, 1024
242:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 242b
	lis %r3, 0
	ori %r3, %r3, 9216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 8192
	add %r4, %r31, %r4
	bl {vg_mldsa_sub}
	lis %r3, 0
	ori %r3, %r3, 9216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 8192
	add %r4, %r31, %r4
	bl {vg_mldsa_sub}
	lis %r3, 0
	ori %r3, %r3, 29696
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 8192
	add %r4, %r31, %r4
	bl {vg_mldsa_add}
	lis %r3, 0
	ori %r3, %r3, 9216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 29696
	add %r4, %r31, %r4
	lis %r5, 3
	ori %r5, %r5, 65280
	lis %r6, 0
	ori %r6, %r6, 13312
	add %r6, %r31, %r6
	bl {vg_mldsa_make_hint}
	rlwinm %r3, %r3, 0, 0, 31
	add %r26, %r26, %r3
	lis %r3, 0
	ori %r3, %r3, 8192
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 5120
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 48128
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 8192
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 8192
	add %r3, %r31, %r3
	lis %r4, 3
	ori %r4, %r4, 65280
	bl {vg_mldsa_norm_lt}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	addi %r3, %r31, 8192
	addi %r4, %r31, 9216
	li %r5, 1024
243:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 243b
	lis %r3, 0
	ori %r3, %r3, 9216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 8192
	add %r4, %r31, %r4
	bl {vg_mldsa_sub}
	lis %r3, 0
	ori %r3, %r3, 9216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 8192
	add %r4, %r31, %r4
	bl {vg_mldsa_sub}
	lis %r3, 0
	ori %r3, %r3, 30720
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 8192
	add %r4, %r31, %r4
	bl {vg_mldsa_add}
	lis %r3, 0
	ori %r3, %r3, 9216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 30720
	add %r4, %r31, %r4
	lis %r5, 3
	ori %r5, %r5, 65280
	lis %r6, 0
	ori %r6, %r6, 14336
	add %r6, %r31, %r6
	bl {vg_mldsa_make_hint}
	rlwinm %r3, %r3, 0, 0, 31
	add %r26, %r26, %r3
	lis %r3, 0
	ori %r3, %r3, 8192
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 5120
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 49152
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 8192
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 8192
	add %r3, %r31, %r3
	lis %r4, 3
	ori %r4, %r4, 65280
	bl {vg_mldsa_norm_lt}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	addi %r3, %r31, 8192
	addi %r4, %r31, 9216
	li %r5, 1024
244:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 244b
	lis %r3, 0
	ori %r3, %r3, 9216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 8192
	add %r4, %r31, %r4
	bl {vg_mldsa_sub}
	lis %r3, 0
	ori %r3, %r3, 9216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 8192
	add %r4, %r31, %r4
	bl {vg_mldsa_sub}
	lis %r3, 0
	ori %r3, %r3, 31744
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 8192
	add %r4, %r31, %r4
	bl {vg_mldsa_add}
	lis %r3, 0
	ori %r3, %r3, 9216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 31744
	add %r4, %r31, %r4
	lis %r5, 3
	ori %r5, %r5, 65280
	lis %r6, 0
	ori %r6, %r6, 15360
	add %r6, %r31, %r6
	bl {vg_mldsa_make_hint}
	rlwinm %r3, %r3, 0, 0, 31
	add %r26, %r26, %r3
	addi %r3, %r26, -56
	rldicl %r3, %r3, 1, 63
	and %r24, %r24, %r3
238:
224:
	cmpldi %cr0, %r24, 0
	bne %cr0, 245f
	addi %r27, %r27, 5
	b 246f
245:
	li %r25, 1
246:
212:
	addi %r25, %r25, -1
	cmpldi %cr0, %r25, 0
	bne %cr0, 25b
	cmpldi %cr0, %r24, 0
	bne %cr0, 247f
	b 248f
247:
	addi %r3, %r31, 1040
	addi %r4, %r28, 0
	li %r5, 48
249:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 249b
	lis %r3, 0
	ori %r3, %r3, 16384
	add %r3, %r31, %r3
	lis %r4, 7
	ori %r4, %r4, 65535
	lis %r5, 8
	ori %r5, %r5, 0
	lis %r6, 0
	ori %r6, %r6, 48
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 640
	bl {vg_mldsa_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 17408
	add %r3, %r31, %r3
	lis %r4, 7
	ori %r4, %r4, 65535
	lis %r5, 8
	ori %r5, %r5, 0
	lis %r6, 0
	ori %r6, %r6, 688
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 640
	bl {vg_mldsa_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 18432
	add %r3, %r31, %r3
	lis %r4, 7
	ori %r4, %r4, 65535
	lis %r5, 8
	ori %r5, %r5, 0
	lis %r6, 0
	ori %r6, %r6, 1328
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 640
	bl {vg_mldsa_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 19456
	add %r3, %r31, %r3
	lis %r4, 7
	ori %r4, %r4, 65535
	lis %r5, 8
	ori %r5, %r5, 0
	lis %r6, 0
	ori %r6, %r6, 1968
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 640
	bl {vg_mldsa_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 20480
	add %r3, %r31, %r3
	lis %r4, 7
	ori %r4, %r4, 65535
	lis %r5, 8
	ori %r5, %r5, 0
	lis %r6, 0
	ori %r6, %r6, 2608
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 640
	bl {vg_mldsa_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 10240
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 1536
	lis %r5, 0
	ori %r5, %r5, 55
	lis %r6, 0
	ori %r6, %r6, 3248
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 61
	bl {vg_mldsa_hint_bit_pack}
248:
22:
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

vg_mldsa65_sign_message:
	rldicl %r11, %r7, 56, 8
	cmpldi %cr0, %r11, 0
	beq %cr0, 20f
	li %r3, 2
	b 21f
20:
	lis %r12, 1
	ori %r12, %r12, 37888
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
	bl {vg_mldsa65_sign}
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

vg_mldsa65_verify:
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
	lis %r3, 0
	ori %r3, %r3, 3248
	add %r3, %r28, %r3
	lis %r4, 0
	ori %r4, %r4, 61
	lis %r5, 0
	ori %r5, %r5, 55
	lis %r6, 0
	ori %r6, %r6, 8192
	add %r6, %r31, %r6
	lis %r7, 0
	ori %r7, %r7, 1536
	bl {vg_mldsa_hint_bit_unpack}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	cmpldi %cr0, %r24, 0
	bne %cr0, 20f
	b 21f
20:
	lis %r3, 0
	ori %r3, %r3, 48
	add %r3, %r28, %r3
	lis %r4, 0
	ori %r4, %r4, 640
	lis %r5, 7
	ori %r5, %r5, 65535
	lis %r6, 8
	ori %r6, %r6, 0
	lis %r7, 0
	ori %r7, %r7, 16384
	add %r7, %r31, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 16384
	add %r3, %r31, %r3
	lis %r4, 7
	ori %r4, %r4, 65340
	bl {vg_mldsa_norm_lt}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	lis %r3, 0
	ori %r3, %r3, 688
	add %r3, %r28, %r3
	lis %r4, 0
	ori %r4, %r4, 640
	lis %r5, 7
	ori %r5, %r5, 65535
	lis %r6, 8
	ori %r6, %r6, 0
	lis %r7, 0
	ori %r7, %r7, 17408
	add %r7, %r31, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 17408
	add %r3, %r31, %r3
	lis %r4, 7
	ori %r4, %r4, 65340
	bl {vg_mldsa_norm_lt}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	lis %r3, 0
	ori %r3, %r3, 1328
	add %r3, %r28, %r3
	lis %r4, 0
	ori %r4, %r4, 640
	lis %r5, 7
	ori %r5, %r5, 65535
	lis %r6, 8
	ori %r6, %r6, 0
	lis %r7, 0
	ori %r7, %r7, 18432
	add %r7, %r31, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 18432
	add %r3, %r31, %r3
	lis %r4, 7
	ori %r4, %r4, 65340
	bl {vg_mldsa_norm_lt}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	lis %r3, 0
	ori %r3, %r3, 1968
	add %r3, %r28, %r3
	lis %r4, 0
	ori %r4, %r4, 640
	lis %r5, 7
	ori %r5, %r5, 65535
	lis %r6, 8
	ori %r6, %r6, 0
	lis %r7, 0
	ori %r7, %r7, 19456
	add %r7, %r31, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 19456
	add %r3, %r31, %r3
	lis %r4, 7
	ori %r4, %r4, 65340
	bl {vg_mldsa_norm_lt}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	lis %r3, 0
	ori %r3, %r3, 2608
	add %r3, %r28, %r3
	lis %r4, 0
	ori %r4, %r4, 640
	lis %r5, 7
	ori %r5, %r5, 65535
	lis %r6, 8
	ori %r6, %r6, 0
	lis %r7, 0
	ori %r7, %r7, 20480
	add %r7, %r31, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 20480
	add %r3, %r31, %r3
	lis %r4, 7
	ori %r4, %r4, 65340
	bl {vg_mldsa_norm_lt}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	cmpldi %cr0, %r24, 0
	bne %cr0, 22f
	b 23f
22:
	addi %r3, %r30, 0
	addi %r4, %r31, 920
	li %r5, 32
24:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 24b
	li %r0, 0
	stb %r0, 952(%r31)
	li %r0, 0
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 28672
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 4096
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 28672
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
	li %r0, 1
	stb %r0, 952(%r31)
	li %r0, 0
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 29696
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 4096
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 29696
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
	li %r0, 2
	stb %r0, 952(%r31)
	li %r0, 0
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 30720
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 4096
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 30720
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
	li %r0, 3
	stb %r0, 952(%r31)
	li %r0, 0
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 31744
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 4096
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 31744
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
	li %r0, 4
	stb %r0, 952(%r31)
	li %r0, 0
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 32768
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 4096
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 32768
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
	stb %r0, 952(%r31)
	li %r0, 1
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 36864
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 4096
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 36864
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
	stb %r0, 952(%r31)
	li %r0, 1
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 37888
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 4096
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 37888
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
	stb %r0, 952(%r31)
	li %r0, 1
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 38912
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 4096
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 38912
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
	stb %r0, 952(%r31)
	li %r0, 1
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 39936
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 4096
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 39936
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
	li %r0, 4
	stb %r0, 952(%r31)
	li %r0, 1
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 40960
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 4096
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 40960
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
	li %r0, 0
	stb %r0, 952(%r31)
	li %r0, 2
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 45056
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 4096
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 45056
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
	li %r0, 1
	stb %r0, 952(%r31)
	li %r0, 2
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 46080
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 4096
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 46080
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
	li %r0, 2
	stb %r0, 952(%r31)
	li %r0, 2
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 47104
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 4096
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 47104
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
	li %r0, 3
	stb %r0, 952(%r31)
	li %r0, 2
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 48128
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 4096
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 48128
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
	li %r0, 4
	stb %r0, 952(%r31)
	li %r0, 2
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 49152
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 4096
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 49152
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
	li %r0, 0
	stb %r0, 952(%r31)
	li %r0, 3
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 53248
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 4096
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 53248
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
	li %r0, 1
	stb %r0, 952(%r31)
	li %r0, 3
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 54272
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 4096
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 54272
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
	li %r0, 2
	stb %r0, 952(%r31)
	li %r0, 3
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 55296
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 4096
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 55296
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
	li %r0, 3
	stb %r0, 952(%r31)
	li %r0, 3
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 56320
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 4096
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 56320
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
	li %r0, 4
	stb %r0, 952(%r31)
	li %r0, 3
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 57344
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 4096
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 57344
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
	li %r0, 0
	stb %r0, 952(%r31)
	li %r0, 4
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 61440
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 4096
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 61440
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
	li %r0, 1
	stb %r0, 952(%r31)
	li %r0, 4
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 62464
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 4096
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 62464
	add %r4, %r31, %r4
	li %r5, 256
226:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 226b
	li %r0, 2
	stb %r0, 952(%r31)
	li %r0, 4
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 63488
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 4096
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 63488
	add %r4, %r31, %r4
	li %r5, 256
227:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 227b
	li %r0, 3
	stb %r0, 952(%r31)
	li %r0, 4
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 64512
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 4096
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 64512
	add %r4, %r31, %r4
	li %r5, 256
228:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 228b
	li %r0, 4
	stb %r0, 952(%r31)
	li %r0, 4
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 4096
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 1
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	li %r5, 256
229:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 229b
	li %r0, 0
	stb %r0, 952(%r31)
	li %r0, 5
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 4096
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 4096
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 1
	ori %r4, %r4, 4096
	add %r4, %r31, %r4
	li %r5, 256
230:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 230b
	li %r0, 1
	stb %r0, 952(%r31)
	li %r0, 5
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 5120
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 4096
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 1
	ori %r4, %r4, 5120
	add %r4, %r31, %r4
	li %r5, 256
231:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 231b
	li %r0, 2
	stb %r0, 952(%r31)
	li %r0, 5
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 6144
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 4096
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 1
	ori %r4, %r4, 6144
	add %r4, %r31, %r4
	li %r5, 256
232:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 232b
	li %r0, 3
	stb %r0, 952(%r31)
	li %r0, 5
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 7168
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 4096
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 1
	ori %r4, %r4, 7168
	add %r4, %r31, %r4
	li %r5, 256
233:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 233b
	li %r0, 4
	stb %r0, 952(%r31)
	li %r0, 5
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 8192
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 4096
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 1
	ori %r4, %r4, 8192
	add %r4, %r31, %r4
	li %r5, 256
234:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 234b
	lis %r3, 0
	ori %r3, %r3, 0
	add %r3, %r28, %r3
	lis %r4, 0
	ori %r4, %r4, 48
	lis %r5, 0
	ori %r5, %r5, 49
	lis %r6, 0
	ori %r6, %r6, 23552
	add %r6, %r31, %r6
	lis %r7, 0
	ori %r7, %r7, 4096
	add %r7, %r31, %r7
	bl {vg_mldsa_sample_in_ball}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 0
	ori %r4, %r4, 23552
	add %r4, %r31, %r4
	li %r5, 256
235:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 235b
	lis %r3, 0
	ori %r3, %r3, 16384
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4096
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 17408
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4096
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 18432
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4096
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 19456
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4096
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 20480
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4096
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 23552
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4096
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 28672
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 16384
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 29696
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 17408
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 30720
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 18432
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 31744
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 19456
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 32768
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 20480
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 32
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 24576
	add %r4, %r31, %r4
	bl {vg_mldsa_unpack_t1}
	lis %r3, 0
	ori %r3, %r3, 24576
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4096
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 25600
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 23552
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 24576
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 25600
	add %r4, %r31, %r4
	bl {vg_mldsa_sub}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4096
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 8192
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 26624
	add %r4, %r31, %r4
	lis %r5, 3
	ori %r5, %r5, 65280
	lis %r6, 0
	ori %r6, %r6, 27648
	add %r6, %r31, %r6
	bl {vg_mldsa_use_hint}
	lis %r3, 0
	ori %r3, %r3, 27648
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 15
	lis %r5, 0
	ori %r5, %r5, 1024
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 128
	bl {vg_mldsa_simple_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 36864
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 16384
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 37888
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 17408
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 38912
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 18432
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 39936
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 19456
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 40960
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 20480
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 352
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 24576
	add %r4, %r31, %r4
	bl {vg_mldsa_unpack_t1}
	lis %r3, 0
	ori %r3, %r3, 24576
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4096
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 25600
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 23552
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 24576
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 25600
	add %r4, %r31, %r4
	bl {vg_mldsa_sub}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4096
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 9216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 26624
	add %r4, %r31, %r4
	lis %r5, 3
	ori %r5, %r5, 65280
	lis %r6, 0
	ori %r6, %r6, 27648
	add %r6, %r31, %r6
	bl {vg_mldsa_use_hint}
	lis %r3, 0
	ori %r3, %r3, 27648
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 15
	lis %r5, 0
	ori %r5, %r5, 1152
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 128
	bl {vg_mldsa_simple_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 45056
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 16384
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 46080
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 17408
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 47104
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 18432
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 48128
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 19456
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 49152
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 20480
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 672
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 24576
	add %r4, %r31, %r4
	bl {vg_mldsa_unpack_t1}
	lis %r3, 0
	ori %r3, %r3, 24576
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4096
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 25600
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 23552
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 24576
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 25600
	add %r4, %r31, %r4
	bl {vg_mldsa_sub}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4096
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 10240
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 26624
	add %r4, %r31, %r4
	lis %r5, 3
	ori %r5, %r5, 65280
	lis %r6, 0
	ori %r6, %r6, 27648
	add %r6, %r31, %r6
	bl {vg_mldsa_use_hint}
	lis %r3, 0
	ori %r3, %r3, 27648
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 15
	lis %r5, 0
	ori %r5, %r5, 1280
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 128
	bl {vg_mldsa_simple_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 53248
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 16384
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 54272
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 17408
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 55296
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 18432
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 56320
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 19456
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 57344
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 20480
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 992
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 24576
	add %r4, %r31, %r4
	bl {vg_mldsa_unpack_t1}
	lis %r3, 0
	ori %r3, %r3, 24576
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4096
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 25600
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 23552
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 24576
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 25600
	add %r4, %r31, %r4
	bl {vg_mldsa_sub}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4096
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 26624
	add %r4, %r31, %r4
	lis %r5, 3
	ori %r5, %r5, 65280
	lis %r6, 0
	ori %r6, %r6, 27648
	add %r6, %r31, %r6
	bl {vg_mldsa_use_hint}
	lis %r3, 0
	ori %r3, %r3, 27648
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 15
	lis %r5, 0
	ori %r5, %r5, 1408
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 128
	bl {vg_mldsa_simple_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 61440
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 16384
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 62464
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 17408
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 63488
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 18432
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 64512
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 19456
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 20480
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 1312
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 24576
	add %r4, %r31, %r4
	bl {vg_mldsa_unpack_t1}
	lis %r3, 0
	ori %r3, %r3, 24576
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4096
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 25600
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 23552
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 24576
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 25600
	add %r4, %r31, %r4
	bl {vg_mldsa_sub}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4096
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 12288
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 26624
	add %r4, %r31, %r4
	lis %r5, 3
	ori %r5, %r5, 65280
	lis %r6, 0
	ori %r6, %r6, 27648
	add %r6, %r31, %r6
	bl {vg_mldsa_use_hint}
	lis %r3, 0
	ori %r3, %r3, 27648
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 15
	lis %r5, 0
	ori %r5, %r5, 1536
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 128
	bl {vg_mldsa_simple_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 4096
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 16384
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 5120
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 17408
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 6144
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 18432
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 7168
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 19456
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 8192
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 20480
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 1632
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 24576
	add %r4, %r31, %r4
	bl {vg_mldsa_unpack_t1}
	lis %r3, 0
	ori %r3, %r3, 24576
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4096
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 25600
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 23552
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 24576
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 25600
	add %r4, %r31, %r4
	bl {vg_mldsa_sub}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4096
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 13312
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 26624
	add %r4, %r31, %r4
	lis %r5, 3
	ori %r5, %r5, 65280
	lis %r6, 0
	ori %r6, %r6, 27648
	add %r6, %r31, %r6
	bl {vg_mldsa_use_hint}
	lis %r3, 0
	ori %r3, %r3, 27648
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 15
	lis %r5, 0
	ori %r5, %r5, 1664
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 128
	bl {vg_mldsa_simple_bit_pack}
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
	li %r7, 64
	addi %r8, %r31, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r31, 0
	li %r4, 136
	addi %r6, %r31, 1024
	li %r7, 768
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
	addi %r6, %r31, 2048
	li %r7, 48
	addi %r8, %r31, 200
	bl {vg_keccak_squeeze_scratch}
	lis %r3, 0
	ori %r3, %r3, 2048
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 0
	add %r4, %r28, %r4
	lis %r26, 0
	ori %r26, %r26, 48
	li %r12, 0
236:
	lbz %r5, 0(%r3)
	lbz %r6, 0(%r4)
	xor %r5, %r5, %r6
	or %r12, %r12, %r5
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r26, %r26, -1
	cmpldi %cr0, %r26, 0
	bne %cr0, 236b
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	and %r24, %r24, %r12
23:
21:
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

vg_mldsa65_verify_message:
	rldicl %r11, %r7, 56, 8
	cmpldi %cr0, %r11, 0
	beq %cr0, 20f
	li %r3, 2
	b 21f
20:
	lis %r12, 1
	ori %r12, %r12, 37888
	add %r12, %r9, %r12
	mflr %r0
	std %r22, 904(%r12)
	std %r23, 912(%r12)
	std %r24, 920(%r12)
	std %r25, 928(%r12)
	std %r26, 936(%r12)
	std %r27, 944(%r12)
	std %r29, 952(%r12)
	std %r30, 960(%r12)
	std %r0, 968(%r12)
	addi %r22, %r3, 0
	addi %r23, %r4, 0
	addi %r24, %r5, 0
	addi %r25, %r6, 0
	addi %r26, %r7, 0
	addi %r27, %r8, 0
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
	addi %r6, %r22, 0
	li %r7, 1952
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
	addi %r6, %r30, 840
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
	bl {vg_mldsa65_verify}
	ld %r0, 968(%r30)
	ld %r22, 904(%r30)
	ld %r23, 912(%r30)
	ld %r24, 920(%r30)
	ld %r25, 928(%r30)
	ld %r26, 936(%r30)
	ld %r27, 944(%r30)
	ld %r29, 952(%r30)
	ld %r30, 960(%r30)
	mtlr %r0
21:
	blr
