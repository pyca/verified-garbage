// The functions of `src/mldsa87.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa87_keygen:
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
	li %r0, 8
	stb %r0, 920(%r31)
	li %r0, 7
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
	li %r0, 5
	stb %r0, 1184(%r31)
	li %r0, 0
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
	li %r0, 6
	stb %r0, 1184(%r31)
	li %r0, 0
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
	li %r0, 0
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
	li %r0, 1
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
	li %r0, 2
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
	li %r0, 3
	stb %r0, 1184(%r31)
	li %r0, 1
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
	li %r0, 4
	stb %r0, 1184(%r31)
	li %r0, 1
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
	li %r0, 5
	stb %r0, 1184(%r31)
	li %r0, 1
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
	li %r0, 6
	stb %r0, 1184(%r31)
	li %r0, 1
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
	li %r0, 0
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
	li %r0, 1
	stb %r0, 1184(%r31)
	li %r0, 2
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
	li %r0, 2
	stb %r0, 1184(%r31)
	li %r0, 2
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
	li %r0, 3
	stb %r0, 1184(%r31)
	li %r0, 2
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
	li %r0, 4
	stb %r0, 1184(%r31)
	li %r0, 2
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
	li %r0, 5
	stb %r0, 1184(%r31)
	li %r0, 2
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
	li %r0, 6
	stb %r0, 1184(%r31)
	li %r0, 2
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
	li %r0, 0
	stb %r0, 1184(%r31)
	li %r0, 3
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
	li %r0, 1
	stb %r0, 1184(%r31)
	li %r0, 3
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
	li %r0, 2
	stb %r0, 1184(%r31)
	li %r0, 3
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
	li %r0, 3
	stb %r0, 1184(%r31)
	li %r0, 3
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
	li %r0, 4
	stb %r0, 1184(%r31)
	li %r0, 3
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
	li %r0, 5
	stb %r0, 1184(%r31)
	li %r0, 3
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
	li %r0, 6
	stb %r0, 1184(%r31)
	li %r0, 3
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
	li %r0, 0
	stb %r0, 1184(%r31)
	li %r0, 4
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
	li %r0, 1
	stb %r0, 1184(%r31)
	li %r0, 4
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
	li %r0, 2
	stb %r0, 1184(%r31)
	li %r0, 4
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 34816
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
	li %r0, 3
	stb %r0, 1184(%r31)
	li %r0, 4
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 35840
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
	li %r0, 4
	stb %r0, 1184(%r31)
	li %r0, 4
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 36864
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
	li %r0, 5
	stb %r0, 1184(%r31)
	li %r0, 4
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 37888
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
	li %r0, 6
	stb %r0, 1184(%r31)
	li %r0, 4
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 38912
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
	li %r0, 0
	stb %r0, 1184(%r31)
	li %r0, 5
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 39936
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
	li %r0, 1
	stb %r0, 1184(%r31)
	li %r0, 5
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 40960
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
	li %r0, 2
	stb %r0, 1184(%r31)
	li %r0, 5
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 41984
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
	li %r0, 3
	stb %r0, 1184(%r31)
	li %r0, 5
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 43008
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
	li %r0, 4
	stb %r0, 1184(%r31)
	li %r0, 5
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 44032
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
	li %r0, 5
	stb %r0, 1184(%r31)
	li %r0, 5
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 45056
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
	li %r0, 6
	stb %r0, 1184(%r31)
	li %r0, 5
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 46080
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
	ori %r4, %r4, 46080
	add %r4, %r31, %r4
	li %r5, 256
243:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 243b
	li %r0, 0
	stb %r0, 1184(%r31)
	li %r0, 6
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 47104
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
	ori %r4, %r4, 47104
	add %r4, %r31, %r4
	li %r5, 256
244:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 244b
	li %r0, 1
	stb %r0, 1184(%r31)
	li %r0, 6
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 48128
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
	ori %r4, %r4, 48128
	add %r4, %r31, %r4
	li %r5, 256
245:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 245b
	li %r0, 2
	stb %r0, 1184(%r31)
	li %r0, 6
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 49152
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
	ori %r4, %r4, 49152
	add %r4, %r31, %r4
	li %r5, 256
246:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 246b
	li %r0, 3
	stb %r0, 1184(%r31)
	li %r0, 6
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 50176
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
	ori %r4, %r4, 50176
	add %r4, %r31, %r4
	li %r5, 256
247:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 247b
	li %r0, 4
	stb %r0, 1184(%r31)
	li %r0, 6
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 51200
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
	ori %r4, %r4, 51200
	add %r4, %r31, %r4
	li %r5, 256
248:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 248b
	li %r0, 5
	stb %r0, 1184(%r31)
	li %r0, 6
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 52224
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
	ori %r4, %r4, 52224
	add %r4, %r31, %r4
	li %r5, 256
249:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 249b
	li %r0, 6
	stb %r0, 1184(%r31)
	li %r0, 6
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 53248
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
	ori %r4, %r4, 53248
	add %r4, %r31, %r4
	li %r5, 256
250:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 250b
	li %r0, 0
	stb %r0, 1184(%r31)
	li %r0, 7
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 54272
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
	ori %r4, %r4, 54272
	add %r4, %r31, %r4
	li %r5, 256
251:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 251b
	li %r0, 1
	stb %r0, 1184(%r31)
	li %r0, 7
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 55296
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
	ori %r4, %r4, 55296
	add %r4, %r31, %r4
	li %r5, 256
252:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 252b
	li %r0, 2
	stb %r0, 1184(%r31)
	li %r0, 7
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 56320
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
	ori %r4, %r4, 56320
	add %r4, %r31, %r4
	li %r5, 256
253:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 253b
	li %r0, 3
	stb %r0, 1184(%r31)
	li %r0, 7
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 57344
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
	ori %r4, %r4, 57344
	add %r4, %r31, %r4
	li %r5, 256
254:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 254b
	li %r0, 4
	stb %r0, 1184(%r31)
	li %r0, 7
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 58368
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
	ori %r4, %r4, 58368
	add %r4, %r31, %r4
	li %r5, 256
255:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 255b
	li %r0, 5
	stb %r0, 1184(%r31)
	li %r0, 7
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 59392
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
	ori %r4, %r4, 59392
	add %r4, %r31, %r4
	li %r5, 256
256:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 256b
	li %r0, 6
	stb %r0, 1184(%r31)
	li %r0, 7
	stb %r0, 1185(%r31)
	lis %r3, 0
	ori %r3, %r3, 1152
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 60416
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
	ori %r4, %r4, 60416
	add %r4, %r31, %r4
	li %r5, 256
257:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 257b
	li %r0, 0
	stb %r0, 1280(%r31)
	lis %r3, 0
	ori %r3, %r3, 1216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2
	lis %r5, 0
	ori %r5, %r5, 61440
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
	ori %r4, %r4, 61440
	add %r4, %r31, %r4
	li %r5, 256
258:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 258b
	li %r0, 1
	stb %r0, 1280(%r31)
	lis %r3, 0
	ori %r3, %r3, 1216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2
	lis %r5, 0
	ori %r5, %r5, 62464
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
	ori %r4, %r4, 62464
	add %r4, %r31, %r4
	li %r5, 256
259:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 259b
	li %r0, 2
	stb %r0, 1280(%r31)
	lis %r3, 0
	ori %r3, %r3, 1216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2
	lis %r5, 0
	ori %r5, %r5, 63488
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
	ori %r4, %r4, 63488
	add %r4, %r31, %r4
	li %r5, 256
260:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 260b
	li %r0, 3
	stb %r0, 1280(%r31)
	lis %r3, 0
	ori %r3, %r3, 1216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2
	lis %r5, 0
	ori %r5, %r5, 64512
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
	ori %r4, %r4, 64512
	add %r4, %r31, %r4
	li %r5, 256
261:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 261b
	li %r0, 4
	stb %r0, 1280(%r31)
	lis %r3, 0
	ori %r3, %r3, 1216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2
	lis %r5, 1
	ori %r5, %r5, 0
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 2048
	add %r6, %r31, %r6
	bl {vg_mldsa_rej_bounded_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 1
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	li %r5, 256
262:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 262b
	li %r0, 5
	stb %r0, 1280(%r31)
	lis %r3, 0
	ori %r3, %r3, 1216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2
	lis %r5, 1
	ori %r5, %r5, 1024
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 2048
	add %r6, %r31, %r6
	bl {vg_mldsa_rej_bounded_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 1
	ori %r4, %r4, 1024
	add %r4, %r31, %r4
	li %r5, 256
263:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 263b
	li %r0, 6
	stb %r0, 1280(%r31)
	lis %r3, 0
	ori %r3, %r3, 1216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2
	lis %r5, 1
	ori %r5, %r5, 2048
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 2048
	add %r6, %r31, %r6
	bl {vg_mldsa_rej_bounded_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 1
	ori %r4, %r4, 2048
	add %r4, %r31, %r4
	li %r5, 256
264:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 264b
	li %r0, 7
	stb %r0, 1280(%r31)
	lis %r3, 0
	ori %r3, %r3, 1216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2
	lis %r5, 1
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 2048
	add %r6, %r31, %r6
	bl {vg_mldsa_rej_bounded_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 1
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	li %r5, 256
265:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 265b
	li %r0, 8
	stb %r0, 1280(%r31)
	lis %r3, 0
	ori %r3, %r3, 1216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2
	lis %r5, 1
	ori %r5, %r5, 4096
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 2048
	add %r6, %r31, %r6
	bl {vg_mldsa_rej_bounded_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 1
	ori %r4, %r4, 4096
	add %r4, %r31, %r4
	li %r5, 256
266:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 266b
	li %r0, 9
	stb %r0, 1280(%r31)
	lis %r3, 0
	ori %r3, %r3, 1216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2
	lis %r5, 1
	ori %r5, %r5, 5120
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 2048
	add %r6, %r31, %r6
	bl {vg_mldsa_rej_bounded_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 1
	ori %r4, %r4, 5120
	add %r4, %r31, %r4
	li %r5, 256
267:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 267b
	li %r0, 10
	stb %r0, 1280(%r31)
	lis %r3, 0
	ori %r3, %r3, 1216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2
	lis %r5, 1
	ori %r5, %r5, 6144
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 2048
	add %r6, %r31, %r6
	bl {vg_mldsa_rej_bounded_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 1
	ori %r4, %r4, 6144
	add %r4, %r31, %r4
	li %r5, 256
268:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 268b
	li %r0, 11
	stb %r0, 1280(%r31)
	lis %r3, 0
	ori %r3, %r3, 1216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2
	lis %r5, 1
	ori %r5, %r5, 7168
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 2048
	add %r6, %r31, %r6
	bl {vg_mldsa_rej_bounded_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 1
	ori %r4, %r4, 7168
	add %r4, %r31, %r4
	li %r5, 256
269:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 269b
	li %r0, 12
	stb %r0, 1280(%r31)
	lis %r3, 0
	ori %r3, %r3, 1216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2
	lis %r5, 1
	ori %r5, %r5, 8192
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 2048
	add %r6, %r31, %r6
	bl {vg_mldsa_rej_bounded_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 1
	ori %r4, %r4, 8192
	add %r4, %r31, %r4
	li %r5, 256
270:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 270b
	li %r0, 13
	stb %r0, 1280(%r31)
	lis %r3, 0
	ori %r3, %r3, 1216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2
	lis %r5, 1
	ori %r5, %r5, 9216
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 2048
	add %r6, %r31, %r6
	bl {vg_mldsa_rej_bounded_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 1
	ori %r4, %r4, 9216
	add %r4, %r31, %r4
	li %r5, 256
271:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 271b
	li %r0, 14
	stb %r0, 1280(%r31)
	lis %r3, 0
	ori %r3, %r3, 1216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2
	lis %r5, 1
	ori %r5, %r5, 10240
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 2048
	add %r6, %r31, %r6
	bl {vg_mldsa_rej_bounded_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 1
	ori %r4, %r4, 10240
	add %r4, %r31, %r4
	li %r5, 256
272:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 272b
	addi %r3, %r31, 1024
	addi %r4, %r29, 0
	li %r5, 32
273:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 273b
	addi %r3, %r31, 1024
	addi %r4, %r28, 0
	li %r5, 32
274:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 274b
	addi %r3, %r31, 1120
	addi %r4, %r28, 32
	li %r5, 32
275:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 275b
	lis %r3, 0
	ori %r3, %r3, 61440
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
	ori %r3, %r3, 62464
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
	ori %r3, %r3, 63488
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
	ori %r3, %r3, 64512
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
	lis %r3, 1
	ori %r3, %r3, 0
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
	lis %r3, 1
	ori %r3, %r3, 1024
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
	lis %r3, 1
	ori %r3, %r3, 2048
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
	lis %r3, 1
	ori %r3, %r3, 3072
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
	lis %r3, 1
	ori %r3, %r3, 4096
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2
	lis %r5, 0
	ori %r5, %r5, 2
	lis %r6, 0
	ori %r6, %r6, 896
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 96
	bl {vg_mldsa_bit_pack}
	lis %r3, 1
	ori %r3, %r3, 5120
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2
	lis %r5, 0
	ori %r5, %r5, 2
	lis %r6, 0
	ori %r6, %r6, 992
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 96
	bl {vg_mldsa_bit_pack}
	lis %r3, 1
	ori %r3, %r3, 6144
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2
	lis %r5, 0
	ori %r5, %r5, 2
	lis %r6, 0
	ori %r6, %r6, 1088
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 96
	bl {vg_mldsa_bit_pack}
	lis %r3, 1
	ori %r3, %r3, 7168
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2
	lis %r5, 0
	ori %r5, %r5, 2
	lis %r6, 0
	ori %r6, %r6, 1184
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 96
	bl {vg_mldsa_bit_pack}
	lis %r3, 1
	ori %r3, %r3, 8192
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2
	lis %r5, 0
	ori %r5, %r5, 2
	lis %r6, 0
	ori %r6, %r6, 1280
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 96
	bl {vg_mldsa_bit_pack}
	lis %r3, 1
	ori %r3, %r3, 9216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2
	lis %r5, 0
	ori %r5, %r5, 2
	lis %r6, 0
	ori %r6, %r6, 1376
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 96
	bl {vg_mldsa_bit_pack}
	lis %r3, 1
	ori %r3, %r3, 10240
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2
	lis %r5, 0
	ori %r5, %r5, 2
	lis %r6, 0
	ori %r6, %r6, 1472
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 96
	bl {vg_mldsa_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 61440
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2048
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 62464
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2048
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 63488
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2048
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 64512
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2048
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 1
	ori %r3, %r3, 0
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2048
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 1
	ori %r3, %r3, 1024
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2048
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 1
	ori %r3, %r3, 2048
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2048
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4096
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 61440
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 5120
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 62464
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 6144
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 63488
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 7168
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 64512
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 8192
	add %r4, %r31, %r4
	lis %r5, 1
	ori %r5, %r5, 0
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 9216
	add %r4, %r31, %r4
	lis %r5, 1
	ori %r5, %r5, 1024
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 10240
	add %r4, %r31, %r4
	lis %r5, 1
	ori %r5, %r5, 2048
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2048
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_add}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 12288
	add %r4, %r31, %r4
	lis %r5, 1
	ori %r5, %r5, 13312
	add %r5, %r31, %r5
	bl {vg_mldsa_power2round}
	lis %r3, 1
	ori %r3, %r3, 12288
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 1023
	lis %r5, 0
	ori %r5, %r5, 32
	add %r5, %r29, %r5
	lis %r6, 0
	ori %r6, %r6, 320
	bl {vg_mldsa_simple_bit_pack}
	lis %r3, 1
	ori %r3, %r3, 13312
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4095
	lis %r5, 0
	ori %r5, %r5, 4096
	lis %r6, 0
	ori %r6, %r6, 1568
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 416
	bl {vg_mldsa_bit_pack}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 11264
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 61440
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 12288
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 62464
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 13312
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 63488
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 14336
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 64512
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 15360
	add %r4, %r31, %r4
	lis %r5, 1
	ori %r5, %r5, 0
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 16384
	add %r4, %r31, %r4
	lis %r5, 1
	ori %r5, %r5, 1024
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 17408
	add %r4, %r31, %r4
	lis %r5, 1
	ori %r5, %r5, 2048
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2048
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 4096
	add %r4, %r31, %r4
	bl {vg_mldsa_add}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 12288
	add %r4, %r31, %r4
	lis %r5, 1
	ori %r5, %r5, 13312
	add %r5, %r31, %r5
	bl {vg_mldsa_power2round}
	lis %r3, 1
	ori %r3, %r3, 12288
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 1023
	lis %r5, 0
	ori %r5, %r5, 352
	add %r5, %r29, %r5
	lis %r6, 0
	ori %r6, %r6, 320
	bl {vg_mldsa_simple_bit_pack}
	lis %r3, 1
	ori %r3, %r3, 13312
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4095
	lis %r5, 0
	ori %r5, %r5, 4096
	lis %r6, 0
	ori %r6, %r6, 1984
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 416
	bl {vg_mldsa_bit_pack}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 18432
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 61440
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 19456
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 62464
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 20480
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 63488
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 21504
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 64512
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 22528
	add %r4, %r31, %r4
	lis %r5, 1
	ori %r5, %r5, 0
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 23552
	add %r4, %r31, %r4
	lis %r5, 1
	ori %r5, %r5, 1024
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 24576
	add %r4, %r31, %r4
	lis %r5, 1
	ori %r5, %r5, 2048
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2048
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 5120
	add %r4, %r31, %r4
	bl {vg_mldsa_add}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 12288
	add %r4, %r31, %r4
	lis %r5, 1
	ori %r5, %r5, 13312
	add %r5, %r31, %r5
	bl {vg_mldsa_power2round}
	lis %r3, 1
	ori %r3, %r3, 12288
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 1023
	lis %r5, 0
	ori %r5, %r5, 672
	add %r5, %r29, %r5
	lis %r6, 0
	ori %r6, %r6, 320
	bl {vg_mldsa_simple_bit_pack}
	lis %r3, 1
	ori %r3, %r3, 13312
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4095
	lis %r5, 0
	ori %r5, %r5, 4096
	lis %r6, 0
	ori %r6, %r6, 2400
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 416
	bl {vg_mldsa_bit_pack}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 25600
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 61440
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 26624
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 62464
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 27648
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 63488
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 28672
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 64512
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 29696
	add %r4, %r31, %r4
	lis %r5, 1
	ori %r5, %r5, 0
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 30720
	add %r4, %r31, %r4
	lis %r5, 1
	ori %r5, %r5, 1024
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 31744
	add %r4, %r31, %r4
	lis %r5, 1
	ori %r5, %r5, 2048
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2048
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 6144
	add %r4, %r31, %r4
	bl {vg_mldsa_add}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 12288
	add %r4, %r31, %r4
	lis %r5, 1
	ori %r5, %r5, 13312
	add %r5, %r31, %r5
	bl {vg_mldsa_power2round}
	lis %r3, 1
	ori %r3, %r3, 12288
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 1023
	lis %r5, 0
	ori %r5, %r5, 992
	add %r5, %r29, %r5
	lis %r6, 0
	ori %r6, %r6, 320
	bl {vg_mldsa_simple_bit_pack}
	lis %r3, 1
	ori %r3, %r3, 13312
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4095
	lis %r5, 0
	ori %r5, %r5, 4096
	lis %r6, 0
	ori %r6, %r6, 2816
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 416
	bl {vg_mldsa_bit_pack}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 32768
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 61440
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 33792
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 62464
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 34816
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 63488
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 35840
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 64512
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 36864
	add %r4, %r31, %r4
	lis %r5, 1
	ori %r5, %r5, 0
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 37888
	add %r4, %r31, %r4
	lis %r5, 1
	ori %r5, %r5, 1024
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 38912
	add %r4, %r31, %r4
	lis %r5, 1
	ori %r5, %r5, 2048
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2048
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 7168
	add %r4, %r31, %r4
	bl {vg_mldsa_add}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 12288
	add %r4, %r31, %r4
	lis %r5, 1
	ori %r5, %r5, 13312
	add %r5, %r31, %r5
	bl {vg_mldsa_power2round}
	lis %r3, 1
	ori %r3, %r3, 12288
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 1023
	lis %r5, 0
	ori %r5, %r5, 1312
	add %r5, %r29, %r5
	lis %r6, 0
	ori %r6, %r6, 320
	bl {vg_mldsa_simple_bit_pack}
	lis %r3, 1
	ori %r3, %r3, 13312
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4095
	lis %r5, 0
	ori %r5, %r5, 4096
	lis %r6, 0
	ori %r6, %r6, 3232
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 416
	bl {vg_mldsa_bit_pack}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 39936
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 61440
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 40960
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 62464
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 41984
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 63488
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 43008
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 64512
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 44032
	add %r4, %r31, %r4
	lis %r5, 1
	ori %r5, %r5, 0
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 45056
	add %r4, %r31, %r4
	lis %r5, 1
	ori %r5, %r5, 1024
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 46080
	add %r4, %r31, %r4
	lis %r5, 1
	ori %r5, %r5, 2048
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2048
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 8192
	add %r4, %r31, %r4
	bl {vg_mldsa_add}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 12288
	add %r4, %r31, %r4
	lis %r5, 1
	ori %r5, %r5, 13312
	add %r5, %r31, %r5
	bl {vg_mldsa_power2round}
	lis %r3, 1
	ori %r3, %r3, 12288
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 1023
	lis %r5, 0
	ori %r5, %r5, 1632
	add %r5, %r29, %r5
	lis %r6, 0
	ori %r6, %r6, 320
	bl {vg_mldsa_simple_bit_pack}
	lis %r3, 1
	ori %r3, %r3, 13312
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4095
	lis %r5, 0
	ori %r5, %r5, 4096
	lis %r6, 0
	ori %r6, %r6, 3648
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 416
	bl {vg_mldsa_bit_pack}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 47104
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 61440
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 48128
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 62464
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 49152
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 63488
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 50176
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 64512
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 51200
	add %r4, %r31, %r4
	lis %r5, 1
	ori %r5, %r5, 0
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 52224
	add %r4, %r31, %r4
	lis %r5, 1
	ori %r5, %r5, 1024
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 53248
	add %r4, %r31, %r4
	lis %r5, 1
	ori %r5, %r5, 2048
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2048
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 9216
	add %r4, %r31, %r4
	bl {vg_mldsa_add}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 12288
	add %r4, %r31, %r4
	lis %r5, 1
	ori %r5, %r5, 13312
	add %r5, %r31, %r5
	bl {vg_mldsa_power2round}
	lis %r3, 1
	ori %r3, %r3, 12288
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 1023
	lis %r5, 0
	ori %r5, %r5, 1952
	add %r5, %r29, %r5
	lis %r6, 0
	ori %r6, %r6, 320
	bl {vg_mldsa_simple_bit_pack}
	lis %r3, 1
	ori %r3, %r3, 13312
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4095
	lis %r5, 0
	ori %r5, %r5, 4096
	lis %r6, 0
	ori %r6, %r6, 4064
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 416
	bl {vg_mldsa_bit_pack}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 54272
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 61440
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 55296
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 62464
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 56320
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 63488
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 57344
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 64512
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 58368
	add %r4, %r31, %r4
	lis %r5, 1
	ori %r5, %r5, 0
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 59392
	add %r4, %r31, %r4
	lis %r5, 1
	ori %r5, %r5, 1024
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 60416
	add %r4, %r31, %r4
	lis %r5, 1
	ori %r5, %r5, 2048
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2048
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 10240
	add %r4, %r31, %r4
	bl {vg_mldsa_add}
	lis %r3, 1
	ori %r3, %r3, 11264
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 12288
	add %r4, %r31, %r4
	lis %r5, 1
	ori %r5, %r5, 13312
	add %r5, %r31, %r5
	bl {vg_mldsa_power2round}
	lis %r3, 1
	ori %r3, %r3, 12288
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 1023
	lis %r5, 0
	ori %r5, %r5, 2272
	add %r5, %r29, %r5
	lis %r6, 0
	ori %r6, %r6, 320
	bl {vg_mldsa_simple_bit_pack}
	lis %r3, 1
	ori %r3, %r3, 13312
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4095
	lis %r5, 0
	ori %r5, %r5, 4096
	lis %r6, 0
	ori %r6, %r6, 4480
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
	li %r7, 2592
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

vg_mldsa87_pk_tr:
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
	li %r7, 2592
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

vg_mldsa87_prepare_verifying_key:
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
	li %r5, 324
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
	ori %r4, %r4, 2592
	add %r4, %r30, %r4
	bl {vg_mldsa_unpack_t1}
	lis %r3, 0
	ori %r3, %r3, 2592
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 352
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 3616
	add %r4, %r30, %r4
	bl {vg_mldsa_unpack_t1}
	lis %r3, 0
	ori %r3, %r3, 3616
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 672
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 4640
	add %r4, %r30, %r4
	bl {vg_mldsa_unpack_t1}
	lis %r3, 0
	ori %r3, %r3, 4640
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 992
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 5664
	add %r4, %r30, %r4
	bl {vg_mldsa_unpack_t1}
	lis %r3, 0
	ori %r3, %r3, 5664
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 1312
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 6688
	add %r4, %r30, %r4
	bl {vg_mldsa_unpack_t1}
	lis %r3, 0
	ori %r3, %r3, 6688
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 1632
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 7712
	add %r4, %r30, %r4
	bl {vg_mldsa_unpack_t1}
	lis %r3, 0
	ori %r3, %r3, 7712
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 1952
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 8736
	add %r4, %r30, %r4
	bl {vg_mldsa_unpack_t1}
	lis %r3, 0
	ori %r3, %r3, 8736
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 2272
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 9760
	add %r4, %r30, %r4
	bl {vg_mldsa_unpack_t1}
	lis %r3, 0
	ori %r3, %r3, 9760
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

vg_mldsa87_prepare_signing_key:
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
	li %r5, 612
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
	ori %r7, %r7, 4896
	add %r7, %r30, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 4896
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
	ori %r7, %r7, 5920
	add %r7, %r30, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 5920
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
	ori %r7, %r7, 6944
	add %r7, %r30, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 6944
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
	ori %r7, %r7, 7968
	add %r7, %r30, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 7968
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
	ori %r7, %r7, 8992
	add %r7, %r30, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 8992
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
	ori %r7, %r7, 10016
	add %r7, %r30, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 10016
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
	ori %r7, %r7, 11040
	add %r7, %r30, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 11040
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
	ori %r7, %r7, 12064
	add %r7, %r30, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 12064
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 896
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 96
	lis %r5, 0
	ori %r5, %r5, 2
	lis %r6, 0
	ori %r6, %r6, 2
	lis %r7, 0
	ori %r7, %r7, 13088
	add %r7, %r30, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 13088
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 992
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 96
	lis %r5, 0
	ori %r5, %r5, 2
	lis %r6, 0
	ori %r6, %r6, 2
	lis %r7, 0
	ori %r7, %r7, 14112
	add %r7, %r30, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 14112
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 1088
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 96
	lis %r5, 0
	ori %r5, %r5, 2
	lis %r6, 0
	ori %r6, %r6, 2
	lis %r7, 0
	ori %r7, %r7, 15136
	add %r7, %r30, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 15136
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 1184
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 96
	lis %r5, 0
	ori %r5, %r5, 2
	lis %r6, 0
	ori %r6, %r6, 2
	lis %r7, 0
	ori %r7, %r7, 16160
	add %r7, %r30, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 16160
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 1280
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 96
	lis %r5, 0
	ori %r5, %r5, 2
	lis %r6, 0
	ori %r6, %r6, 2
	lis %r7, 0
	ori %r7, %r7, 17184
	add %r7, %r30, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 17184
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 1376
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 96
	lis %r5, 0
	ori %r5, %r5, 2
	lis %r6, 0
	ori %r6, %r6, 2
	lis %r7, 0
	ori %r7, %r7, 18208
	add %r7, %r30, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 18208
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 1472
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 96
	lis %r5, 0
	ori %r5, %r5, 2
	lis %r6, 0
	ori %r6, %r6, 2
	lis %r7, 0
	ori %r7, %r7, 19232
	add %r7, %r30, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 19232
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 1568
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 416
	lis %r5, 0
	ori %r5, %r5, 4095
	lis %r6, 0
	ori %r6, %r6, 4096
	lis %r7, 0
	ori %r7, %r7, 20256
	add %r7, %r30, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 20256
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 1984
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 416
	lis %r5, 0
	ori %r5, %r5, 4095
	lis %r6, 0
	ori %r6, %r6, 4096
	lis %r7, 0
	ori %r7, %r7, 21280
	add %r7, %r30, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 21280
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 2400
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 416
	lis %r5, 0
	ori %r5, %r5, 4095
	lis %r6, 0
	ori %r6, %r6, 4096
	lis %r7, 0
	ori %r7, %r7, 22304
	add %r7, %r30, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 22304
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 2816
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 416
	lis %r5, 0
	ori %r5, %r5, 4095
	lis %r6, 0
	ori %r6, %r6, 4096
	lis %r7, 0
	ori %r7, %r7, 23328
	add %r7, %r30, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 23328
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 3232
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 416
	lis %r5, 0
	ori %r5, %r5, 4095
	lis %r6, 0
	ori %r6, %r6, 4096
	lis %r7, 0
	ori %r7, %r7, 24352
	add %r7, %r30, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 24352
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 3648
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 416
	lis %r5, 0
	ori %r5, %r5, 4095
	lis %r6, 0
	ori %r6, %r6, 4096
	lis %r7, 0
	ori %r7, %r7, 25376
	add %r7, %r30, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 25376
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 4064
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 416
	lis %r5, 0
	ori %r5, %r5, 4095
	lis %r6, 0
	ori %r6, %r6, 4096
	lis %r7, 0
	ori %r7, %r7, 26400
	add %r7, %r30, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 26400
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 4480
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 416
	lis %r5, 0
	ori %r5, %r5, 4095
	lis %r6, 0
	ori %r6, %r6, 4096
	lis %r7, 0
	ori %r7, %r7, 27424
	add %r7, %r30, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 27424
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

vg_mldsa87_sign:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	addi %r8, %r3, 0
	li %r9, 0
	bl {vg_mldsa87_sign_with_cache}
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	blr

vg_mldsa87_sign_message:
	rldicl %r11, %r7, 56, 8
	cmpldi %cr0, %r11, 0
	beq %cr0, 20f
	li %r3, 2
	b 21f
20:
	lis %r12, 2
	ori %r12, %r12, 13312
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
	bl {vg_mldsa87_sign}
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

vg_mldsa87_sign_message_prepared:
	rldicl %r11, %r7, 56, 8
	cmpldi %cr0, %r11, 0
	beq %cr0, 20f
	li %r3, 2
	b 21f
20:
	lis %r12, 2
	ori %r12, %r12, 13312
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
	bl {vg_mldsa87_sign_prepared}
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

vg_mldsa87_verify:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	addi %r7, %r3, 0
	li %r8, 0
	bl {vg_mldsa87_verify_with_cache}
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	blr

vg_mldsa87_verify_message_cached:
	rldicl %r11, %r7, 56, 8
	cmpldi %cr0, %r11, 0
	beq %cr0, 20f
	li %r3, 2
	b 21f
20:
	lis %r12, 2
	ori %r12, %r12, 13312
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
	bl {vg_mldsa87_verify}
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

vg_mldsa87_verify_message_prepared:
	rldicl %r11, %r7, 56, 8
	cmpldi %cr0, %r11, 0
	beq %cr0, 20f
	li %r3, 2
	b 21f
20:
	lis %r12, 2
	ori %r12, %r12, 13312
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
	bl {vg_mldsa87_verify_prepared}
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
