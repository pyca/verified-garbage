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

vg_mldsa87_sign:
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
	ori %r4, %r4, 64512
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
	lis %r4, 1
	ori %r4, %r4, 0
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
	lis %r4, 1
	ori %r4, %r4, 1024
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
	lis %r4, 1
	ori %r4, %r4, 2048
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
	lis %r4, 1
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 5
	stb %r0, 952(%r31)
	li %r0, 0
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
	li %r0, 6
	stb %r0, 952(%r31)
	li %r0, 0
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
	li %r0, 0
	stb %r0, 952(%r31)
	li %r0, 1
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
	li %r0, 1
	stb %r0, 952(%r31)
	li %r0, 1
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
	li %r0, 2
	stb %r0, 952(%r31)
	li %r0, 1
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
	li %r0, 3
	stb %r0, 952(%r31)
	li %r0, 1
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
	li %r0, 4
	stb %r0, 952(%r31)
	li %r0, 1
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
	li %r0, 5
	stb %r0, 952(%r31)
	li %r0, 1
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
	li %r0, 6
	stb %r0, 952(%r31)
	li %r0, 1
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
	li %r0, 0
	stb %r0, 952(%r31)
	li %r0, 2
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
	li %r0, 1
	stb %r0, 952(%r31)
	li %r0, 2
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
	li %r0, 2
	stb %r0, 952(%r31)
	li %r0, 2
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 15360
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
	lis %r4, 1
	ori %r4, %r4, 16384
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
	lis %r4, 1
	ori %r4, %r4, 17408
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 5
	stb %r0, 952(%r31)
	li %r0, 2
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 18432
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 6
	stb %r0, 952(%r31)
	li %r0, 2
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 19456
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
	ori %r4, %r4, 20480
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
	ori %r4, %r4, 21504
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
	ori %r4, %r4, 22528
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
	ori %r4, %r4, 23552
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
	ori %r4, %r4, 24576
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 5
	stb %r0, 952(%r31)
	li %r0, 3
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 25600
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 6
	stb %r0, 952(%r31)
	li %r0, 3
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 26624
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
	ori %r4, %r4, 27648
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
	ori %r4, %r4, 28672
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
	ori %r4, %r4, 29696
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
	ori %r4, %r4, 30720
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
	ori %r4, %r4, 31744
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 5
	stb %r0, 952(%r31)
	li %r0, 4
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 32768
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 6
	stb %r0, 952(%r31)
	li %r0, 4
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 33792
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
	ori %r4, %r4, 34816
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
	ori %r4, %r4, 35840
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
	ori %r4, %r4, 36864
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
	ori %r4, %r4, 37888
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
	ori %r4, %r4, 38912
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 5
	stb %r0, 952(%r31)
	li %r0, 5
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 39936
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 6
	stb %r0, 952(%r31)
	li %r0, 5
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 40960
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 0
	stb %r0, 952(%r31)
	li %r0, 6
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 41984
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 1
	stb %r0, 952(%r31)
	li %r0, 6
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 43008
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 2
	stb %r0, 952(%r31)
	li %r0, 6
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 44032
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 3
	stb %r0, 952(%r31)
	li %r0, 6
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 45056
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 4
	stb %r0, 952(%r31)
	li %r0, 6
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 46080
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 5
	stb %r0, 952(%r31)
	li %r0, 6
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 47104
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 6
	stb %r0, 952(%r31)
	li %r0, 6
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 48128
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 0
	stb %r0, 952(%r31)
	li %r0, 7
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 49152
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 1
	stb %r0, 952(%r31)
	li %r0, 7
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 50176
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 2
	stb %r0, 952(%r31)
	li %r0, 7
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 51200
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 3
	stb %r0, 952(%r31)
	li %r0, 7
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 52224
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 4
	stb %r0, 952(%r31)
	li %r0, 7
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 53248
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 5
	stb %r0, 952(%r31)
	li %r0, 7
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 54272
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 3072
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r0, 6
	stb %r0, 952(%r31)
	li %r0, 7
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 55296
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
	ori %r4, %r4, 96
	lis %r5, 0
	ori %r5, %r5, 2
	lis %r6, 0
	ori %r6, %r6, 2
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
	ori %r3, %r3, 224
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 96
	lis %r5, 0
	ori %r5, %r5, 2
	lis %r6, 0
	ori %r6, %r6, 2
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
	ori %r3, %r3, 320
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 96
	lis %r5, 0
	ori %r5, %r5, 2
	lis %r6, 0
	ori %r6, %r6, 2
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
	ori %r3, %r3, 416
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 96
	lis %r5, 0
	ori %r5, %r5, 2
	lis %r6, 0
	ori %r6, %r6, 2
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
	ori %r3, %r3, 512
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 96
	lis %r5, 0
	ori %r5, %r5, 2
	lis %r6, 0
	ori %r6, %r6, 2
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
	ori %r3, %r3, 608
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 96
	lis %r5, 0
	ori %r5, %r5, 2
	lis %r6, 0
	ori %r6, %r6, 2
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
	ori %r3, %r3, 704
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 96
	lis %r5, 0
	ori %r5, %r5, 2
	lis %r6, 0
	ori %r6, %r6, 2
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
	ori %r3, %r3, 800
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 96
	lis %r5, 0
	ori %r5, %r5, 2
	lis %r6, 0
	ori %r6, %r6, 2
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
	ori %r3, %r3, 896
	add %r3, %r30, %r3
	lis %r4, 0
	ori %r4, %r4, 96
	lis %r5, 0
	ori %r5, %r5, 2
	lis %r6, 0
	ori %r6, %r6, 2
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
	ori %r7, %r7, 50176
	add %r7, %r31, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 50176
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
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
	ori %r7, %r7, 51200
	add %r7, %r31, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 51200
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
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
	ori %r7, %r7, 52224
	add %r7, %r31, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 52224
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
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
	ori %r7, %r7, 53248
	add %r7, %r31, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 53248
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
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
	ori %r7, %r7, 54272
	add %r7, %r31, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 54272
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
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
	ori %r7, %r7, 55296
	add %r7, %r31, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 55296
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
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
	ori %r7, %r7, 56320
	add %r7, %r31, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 56320
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
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
	ori %r7, %r7, 57344
	add %r7, %r31, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 57344
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
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
	ori %r7, %r7, 58368
	add %r7, %r31, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 58368
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
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
	ori %r7, %r7, 59392
	add %r7, %r31, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 59392
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
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
	ori %r7, %r7, 60416
	add %r7, %r31, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 60416
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
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
	ori %r7, %r7, 61440
	add %r7, %r31, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 61440
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
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
	ori %r7, %r7, 62464
	add %r7, %r31, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 62464
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
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
	ori %r7, %r7, 63488
	add %r7, %r31, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 63488
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
	ori %r5, %r5, 18432
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 3072
	add %r6, %r31, %r6
	bl {vg_mldsa_expand_mask_poly}
	addi %r3, %r31, 18432
	addi %r4, %r31, 25600
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
	ori %r3, %r3, 25600
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
	ori %r5, %r5, 19456
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 3072
	add %r6, %r31, %r6
	bl {vg_mldsa_expand_mask_poly}
	addi %r3, %r31, 19456
	addi %r4, %r31, 26624
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
	ori %r3, %r3, 26624
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
	ori %r5, %r5, 20480
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 3072
	add %r6, %r31, %r6
	bl {vg_mldsa_expand_mask_poly}
	addi %r3, %r31, 20480
	addi %r4, %r31, 27648
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
	ori %r3, %r3, 27648
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
	ori %r5, %r5, 21504
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 3072
	add %r6, %r31, %r6
	bl {vg_mldsa_expand_mask_poly}
	addi %r3, %r31, 21504
	addi %r4, %r31, 28672
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
	ori %r3, %r3, 28672
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
	ori %r5, %r5, 22528
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 3072
	add %r6, %r31, %r6
	bl {vg_mldsa_expand_mask_poly}
	addi %r3, %r31, 22528
	addi %r4, %r31, 29696
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
	ori %r3, %r3, 29696
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	addi %r3, %r27, 5
	stb %r3, 1024(%r31)
	rldicl %r3, %r3, 56, 8
	stb %r3, 1025(%r31)
	lis %r3, 0
	ori %r3, %r3, 960
	add %r3, %r31, %r3
	lis %r4, 8
	ori %r4, %r4, 0
	lis %r5, 0
	ori %r5, %r5, 23552
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 3072
	add %r6, %r31, %r6
	bl {vg_mldsa_expand_mask_poly}
	addi %r3, %r31, 23552
	addi %r4, %r31, 30720
	li %r5, 1024
211:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 211b
	lis %r3, 0
	ori %r3, %r3, 30720
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	addi %r3, %r27, 6
	stb %r3, 1024(%r31)
	rldicl %r3, %r3, 56, 8
	stb %r3, 1025(%r31)
	lis %r3, 0
	ori %r3, %r3, 960
	add %r3, %r31, %r3
	lis %r4, 8
	ori %r4, %r4, 0
	lis %r5, 0
	ori %r5, %r5, 24576
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 3072
	add %r6, %r31, %r6
	bl {vg_mldsa_expand_mask_poly}
	addi %r3, %r31, 24576
	addi %r4, %r31, 31744
	li %r5, 1024
212:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 212b
	lis %r3, 0
	ori %r3, %r3, 31744
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 32768
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 64512
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 25600
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 32768
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 0
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 26624
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 32768
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 1024
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 27648
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 32768
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 2048
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 28672
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 32768
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 29696
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 32768
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 4096
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 30720
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 32768
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 5120
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 31744
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 32768
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 33792
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 6144
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 25600
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 33792
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 7168
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 26624
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 33792
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 8192
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 27648
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 33792
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 9216
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 28672
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 33792
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 10240
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 29696
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 33792
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 11264
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 30720
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 33792
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 12288
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 31744
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 33792
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 34816
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 13312
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 25600
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 34816
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 14336
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 26624
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 34816
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 15360
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 27648
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 34816
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 16384
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 28672
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 34816
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 17408
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 29696
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 34816
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 18432
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 30720
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 34816
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 19456
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 31744
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 34816
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 35840
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 20480
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 25600
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 35840
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 21504
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 26624
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 35840
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 22528
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 27648
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 35840
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 23552
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 28672
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 35840
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 24576
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 29696
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 35840
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 25600
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 30720
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 35840
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 26624
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 31744
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 35840
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 36864
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 27648
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 25600
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 36864
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 28672
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 26624
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 36864
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 29696
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 27648
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 36864
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 30720
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 28672
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 36864
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 31744
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 29696
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 36864
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 32768
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 30720
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 36864
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 33792
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 31744
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 36864
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 37888
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 34816
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 25600
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 37888
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 35840
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 26624
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 37888
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 36864
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 27648
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 37888
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 37888
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 28672
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 37888
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 38912
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 29696
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 37888
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 39936
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 30720
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 37888
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 40960
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 31744
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 37888
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 38912
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 41984
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 25600
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 38912
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 43008
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 26624
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 38912
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 44032
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 27648
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 38912
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 45056
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 28672
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 38912
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 46080
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 29696
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 38912
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 47104
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 30720
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 38912
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 48128
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 31744
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 38912
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 39936
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 49152
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 25600
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 39936
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 50176
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 26624
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 39936
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 51200
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 27648
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 39936
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 52224
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 28672
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 39936
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 53248
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 29696
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 39936
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 54272
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 30720
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 39936
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 55296
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 31744
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 39936
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 3072
	add %r4, %r31, %r4
	bl {vg_mldsa_inv_ntt}
	lis %r3, 0
	ori %r3, %r3, 32768
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
	ori %r3, %r3, 33792
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
	ori %r3, %r3, 34816
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
	ori %r3, %r3, 35840
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
	ori %r3, %r3, 36864
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
	ori %r3, %r3, 37888
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
	lis %r3, 0
	ori %r3, %r3, 38912
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
	ori %r5, %r5, 2816
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 128
	bl {vg_mldsa_simple_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 39936
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
	ori %r5, %r5, 2944
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
	li %r7, 1024
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
	li %r7, 64
	addi %r8, %r31, 200
	bl {vg_keccak_squeeze_scratch}
	lis %r3, 0
	ori %r3, %r3, 1040
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 64
	lis %r5, 0
	ori %r5, %r5, 60
	lis %r6, 0
	ori %r6, %r6, 5120
	add %r6, %r31, %r6
	lis %r7, 0
	ori %r7, %r7, 3072
	add %r7, %r31, %r7
	bl {vg_mldsa_sample_in_ball}
	cmplwi %cr0, %r3, 0
	bne %cr0, 213f
	li %r24, 0
	li %r25, 1
	b 214f
213:
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
	ori %r4, %r4, 65416
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
	ori %r4, %r4, 65416
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
	ori %r4, %r4, 65416
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
	ori %r5, %r5, 44032
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
	ori %r3, %r3, 21504
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 6144
	add %r4, %r31, %r4
	bl {vg_mldsa_add}
	lis %r3, 0
	ori %r3, %r3, 21504
	add %r3, %r31, %r3
	lis %r4, 7
	ori %r4, %r4, 65416
	bl {vg_mldsa_norm_lt}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	cmpldi %cr0, %r24, 0
	bne %cr0, 221f
	b 222f
221:
	lis %r3, 0
	ori %r3, %r3, 6144
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 5120
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 45056
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
	ori %r3, %r3, 22528
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 6144
	add %r4, %r31, %r4
	bl {vg_mldsa_add}
	lis %r3, 0
	ori %r3, %r3, 22528
	add %r3, %r31, %r3
	lis %r4, 7
	ori %r4, %r4, 65416
	bl {vg_mldsa_norm_lt}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
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
	ori %r5, %r5, 46080
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
	ori %r3, %r3, 23552
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 6144
	add %r4, %r31, %r4
	bl {vg_mldsa_add}
	lis %r3, 0
	ori %r3, %r3, 23552
	add %r3, %r31, %r3
	lis %r4, 7
	ori %r4, %r4, 65416
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
	ori %r5, %r5, 47104
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
	ori %r3, %r3, 24576
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 6144
	add %r4, %r31, %r4
	bl {vg_mldsa_add}
	lis %r3, 0
	ori %r3, %r3, 24576
	add %r3, %r31, %r3
	lis %r4, 7
	ori %r4, %r4, 65416
	bl {vg_mldsa_norm_lt}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	cmpldi %cr0, %r24, 0
	bne %cr0, 227f
	b 228f
227:
228:
226:
224:
222:
220:
218:
216:
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
	ori %r5, %r5, 48128
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
	ori %r3, %r3, 32768
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 6144
	add %r4, %r31, %r4
	bl {vg_mldsa_sub}
	lis %r3, 0
	ori %r3, %r3, 32768
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
	ori %r4, %r4, 65160
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
	ori %r5, %r5, 49152
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
	ori %r3, %r3, 33792
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 6144
	add %r4, %r31, %r4
	bl {vg_mldsa_sub}
	lis %r3, 0
	ori %r3, %r3, 33792
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
	ori %r4, %r4, 65160
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
	ori %r5, %r5, 50176
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
	ori %r3, %r3, 34816
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 6144
	add %r4, %r31, %r4
	bl {vg_mldsa_sub}
	lis %r3, 0
	ori %r3, %r3, 34816
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
	ori %r4, %r4, 65160
	bl {vg_mldsa_norm_lt}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	cmpldi %cr0, %r24, 0
	bne %cr0, 235f
	b 236f
235:
	lis %r3, 0
	ori %r3, %r3, 6144
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 5120
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 51200
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
	ori %r3, %r3, 35840
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 6144
	add %r4, %r31, %r4
	bl {vg_mldsa_sub}
	lis %r3, 0
	ori %r3, %r3, 35840
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
	ori %r4, %r4, 65160
	bl {vg_mldsa_norm_lt}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	cmpldi %cr0, %r24, 0
	bne %cr0, 237f
	b 238f
237:
	lis %r3, 0
	ori %r3, %r3, 6144
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 5120
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 52224
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
	ori %r3, %r3, 36864
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 6144
	add %r4, %r31, %r4
	bl {vg_mldsa_sub}
	lis %r3, 0
	ori %r3, %r3, 36864
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
	ori %r4, %r4, 65160
	bl {vg_mldsa_norm_lt}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	cmpldi %cr0, %r24, 0
	bne %cr0, 239f
	b 240f
239:
	lis %r3, 0
	ori %r3, %r3, 6144
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 5120
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 53248
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
	ori %r3, %r3, 37888
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 6144
	add %r4, %r31, %r4
	bl {vg_mldsa_sub}
	lis %r3, 0
	ori %r3, %r3, 37888
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
	ori %r4, %r4, 65160
	bl {vg_mldsa_norm_lt}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	cmpldi %cr0, %r24, 0
	bne %cr0, 241f
	b 242f
241:
	lis %r3, 0
	ori %r3, %r3, 6144
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 5120
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 54272
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
	ori %r3, %r3, 38912
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 6144
	add %r4, %r31, %r4
	bl {vg_mldsa_sub}
	lis %r3, 0
	ori %r3, %r3, 38912
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
	ori %r4, %r4, 65160
	bl {vg_mldsa_norm_lt}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	cmpldi %cr0, %r24, 0
	bne %cr0, 243f
	b 244f
243:
	lis %r3, 0
	ori %r3, %r3, 6144
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 5120
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 55296
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
	ori %r3, %r3, 39936
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 6144
	add %r4, %r31, %r4
	bl {vg_mldsa_sub}
	lis %r3, 0
	ori %r3, %r3, 39936
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
	ori %r4, %r4, 65160
	bl {vg_mldsa_norm_lt}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	cmpldi %cr0, %r24, 0
	bne %cr0, 245f
	b 246f
245:
246:
244:
242:
240:
238:
236:
234:
232:
	cmpldi %cr0, %r24, 0
	bne %cr0, 247f
	b 248f
247:
	lis %r3, 0
	ori %r3, %r3, 8192
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 5120
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 56320
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
249:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 249b
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
	ori %r3, %r3, 32768
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 8192
	add %r4, %r31, %r4
	bl {vg_mldsa_add}
	lis %r3, 0
	ori %r3, %r3, 9216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 32768
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
	ori %r5, %r5, 57344
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
250:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 250b
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
	ori %r3, %r3, 33792
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 8192
	add %r4, %r31, %r4
	bl {vg_mldsa_add}
	lis %r3, 0
	ori %r3, %r3, 9216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 33792
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
	ori %r5, %r5, 58368
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
251:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 251b
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
	ori %r3, %r3, 34816
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 8192
	add %r4, %r31, %r4
	bl {vg_mldsa_add}
	lis %r3, 0
	ori %r3, %r3, 9216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 34816
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
	ori %r5, %r5, 59392
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
252:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 252b
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
	ori %r3, %r3, 35840
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 8192
	add %r4, %r31, %r4
	bl {vg_mldsa_add}
	lis %r3, 0
	ori %r3, %r3, 9216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 35840
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
	ori %r5, %r5, 60416
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
253:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 253b
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
	ori %r3, %r3, 36864
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 8192
	add %r4, %r31, %r4
	bl {vg_mldsa_add}
	lis %r3, 0
	ori %r3, %r3, 9216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 36864
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
	ori %r5, %r5, 61440
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
254:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 254b
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
	ori %r3, %r3, 37888
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 8192
	add %r4, %r31, %r4
	bl {vg_mldsa_add}
	lis %r3, 0
	ori %r3, %r3, 9216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 37888
	add %r4, %r31, %r4
	lis %r5, 3
	ori %r5, %r5, 65280
	lis %r6, 0
	ori %r6, %r6, 15360
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
	ori %r5, %r5, 62464
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
255:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 255b
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
	ori %r3, %r3, 38912
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 8192
	add %r4, %r31, %r4
	bl {vg_mldsa_add}
	lis %r3, 0
	ori %r3, %r3, 9216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 38912
	add %r4, %r31, %r4
	lis %r5, 3
	ori %r5, %r5, 65280
	lis %r6, 0
	ori %r6, %r6, 16384
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
	ori %r5, %r5, 63488
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
256:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 256b
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
	ori %r3, %r3, 39936
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 8192
	add %r4, %r31, %r4
	bl {vg_mldsa_add}
	lis %r3, 0
	ori %r3, %r3, 9216
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 39936
	add %r4, %r31, %r4
	lis %r5, 3
	ori %r5, %r5, 65280
	lis %r6, 0
	ori %r6, %r6, 17408
	add %r6, %r31, %r6
	bl {vg_mldsa_make_hint}
	rlwinm %r3, %r3, 0, 0, 31
	add %r26, %r26, %r3
	addi %r3, %r26, -76
	rldicl %r3, %r3, 1, 63
	and %r24, %r24, %r3
248:
230:
	cmpldi %cr0, %r24, 0
	bne %cr0, 257f
	addi %r27, %r27, 7
	b 258f
257:
	li %r25, 1
258:
214:
	addi %r25, %r25, -1
	cmpldi %cr0, %r25, 0
	bne %cr0, 25b
	cmpldi %cr0, %r24, 0
	bne %cr0, 259f
	b 260f
259:
	addi %r3, %r31, 1040
	addi %r4, %r28, 0
	li %r5, 64
261:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 261b
	lis %r3, 0
	ori %r3, %r3, 18432
	add %r3, %r31, %r3
	lis %r4, 7
	ori %r4, %r4, 65535
	lis %r5, 8
	ori %r5, %r5, 0
	lis %r6, 0
	ori %r6, %r6, 64
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
	ori %r6, %r6, 704
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
	ori %r6, %r6, 1344
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 640
	bl {vg_mldsa_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 21504
	add %r3, %r31, %r3
	lis %r4, 7
	ori %r4, %r4, 65535
	lis %r5, 8
	ori %r5, %r5, 0
	lis %r6, 0
	ori %r6, %r6, 1984
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 640
	bl {vg_mldsa_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 22528
	add %r3, %r31, %r3
	lis %r4, 7
	ori %r4, %r4, 65535
	lis %r5, 8
	ori %r5, %r5, 0
	lis %r6, 0
	ori %r6, %r6, 2624
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 640
	bl {vg_mldsa_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 23552
	add %r3, %r31, %r3
	lis %r4, 7
	ori %r4, %r4, 65535
	lis %r5, 8
	ori %r5, %r5, 0
	lis %r6, 0
	ori %r6, %r6, 3264
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 640
	bl {vg_mldsa_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 24576
	add %r3, %r31, %r3
	lis %r4, 7
	ori %r4, %r4, 65535
	lis %r5, 8
	ori %r5, %r5, 0
	lis %r6, 0
	ori %r6, %r6, 3904
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 640
	bl {vg_mldsa_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 10240
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 2048
	lis %r5, 0
	ori %r5, %r5, 75
	lis %r6, 0
	ori %r6, %r6, 4544
	add %r6, %r28, %r6
	lis %r7, 0
	ori %r7, %r7, 83
	bl {vg_mldsa_hint_bit_pack}
260:
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

vg_mldsa87_verify:
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
	ori %r3, %r3, 4544
	add %r3, %r28, %r3
	lis %r4, 0
	ori %r4, %r4, 83
	lis %r5, 0
	ori %r5, %r5, 75
	lis %r6, 0
	ori %r6, %r6, 8192
	add %r6, %r31, %r6
	lis %r7, 0
	ori %r7, %r7, 2048
	bl {vg_mldsa_hint_bit_unpack}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	cmpldi %cr0, %r24, 0
	bne %cr0, 20f
	b 21f
20:
	lis %r3, 0
	ori %r3, %r3, 64
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
	ori %r4, %r4, 65416
	bl {vg_mldsa_norm_lt}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	lis %r3, 0
	ori %r3, %r3, 704
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
	ori %r4, %r4, 65416
	bl {vg_mldsa_norm_lt}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	lis %r3, 0
	ori %r3, %r3, 1344
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
	ori %r4, %r4, 65416
	bl {vg_mldsa_norm_lt}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	lis %r3, 0
	ori %r3, %r3, 1984
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
	ori %r4, %r4, 65416
	bl {vg_mldsa_norm_lt}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	lis %r3, 0
	ori %r3, %r3, 2624
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
	ori %r4, %r4, 65416
	bl {vg_mldsa_norm_lt}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	lis %r3, 0
	ori %r3, %r3, 3264
	add %r3, %r28, %r3
	lis %r4, 0
	ori %r4, %r4, 640
	lis %r5, 7
	ori %r5, %r5, 65535
	lis %r6, 8
	ori %r6, %r6, 0
	lis %r7, 0
	ori %r7, %r7, 21504
	add %r7, %r31, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 21504
	add %r3, %r31, %r3
	lis %r4, 7
	ori %r4, %r4, 65416
	bl {vg_mldsa_norm_lt}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	lis %r3, 0
	ori %r3, %r3, 3904
	add %r3, %r28, %r3
	lis %r4, 0
	ori %r4, %r4, 640
	lis %r5, 7
	ori %r5, %r5, 65535
	lis %r6, 8
	ori %r6, %r6, 0
	lis %r7, 0
	ori %r7, %r7, 22528
	add %r7, %r31, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 22528
	add %r3, %r31, %r3
	lis %r4, 7
	ori %r4, %r4, 65416
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
	li %r0, 5
	stb %r0, 952(%r31)
	li %r0, 0
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 33792
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
	ori %r4, %r4, 33792
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
	li %r0, 6
	stb %r0, 952(%r31)
	li %r0, 0
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 34816
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
	ori %r4, %r4, 34816
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
212:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 212b
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
213:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 213b
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
214:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 214b
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
215:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 215b
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
216:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 216b
	li %r0, 5
	stb %r0, 952(%r31)
	li %r0, 1
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 41984
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
	ori %r4, %r4, 41984
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
	li %r0, 6
	stb %r0, 952(%r31)
	li %r0, 1
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 43008
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
	ori %r4, %r4, 43008
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
219:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 219b
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
220:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 220b
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
221:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 221b
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
222:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 222b
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
223:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 223b
	li %r0, 5
	stb %r0, 952(%r31)
	li %r0, 2
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 50176
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
	ori %r4, %r4, 50176
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
	li %r0, 6
	stb %r0, 952(%r31)
	li %r0, 2
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 51200
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
	ori %r4, %r4, 51200
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
226:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 226b
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
227:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 227b
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
228:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 228b
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
229:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 229b
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
230:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 230b
	li %r0, 5
	stb %r0, 952(%r31)
	li %r0, 3
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 58368
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
	ori %r4, %r4, 58368
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
	li %r0, 6
	stb %r0, 952(%r31)
	li %r0, 3
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 59392
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
	ori %r4, %r4, 59392
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
233:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 233b
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
234:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 234b
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
235:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 235b
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
236:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 236b
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
237:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 237b
	li %r0, 5
	stb %r0, 952(%r31)
	li %r0, 4
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 1024
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
	ori %r4, %r4, 1024
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
	li %r0, 6
	stb %r0, 952(%r31)
	li %r0, 4
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 2048
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
	ori %r4, %r4, 2048
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
240:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 240b
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
241:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 241b
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
242:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 242b
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
243:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 243b
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
244:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 244b
	li %r0, 5
	stb %r0, 952(%r31)
	li %r0, 5
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 9216
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
	ori %r4, %r4, 9216
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
	li %r0, 6
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
	ori %r5, %r5, 4096
	add %r5, %r31, %r5
	bl {vg_mldsa_rej_ntt_poly}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	li %r12, 0
	subf %r12, %r3, %r12
	lis %r4, 1
	ori %r4, %r4, 10240
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
	li %r0, 0
	stb %r0, 952(%r31)
	li %r0, 6
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 12288
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
	ori %r4, %r4, 12288
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
	li %r0, 1
	stb %r0, 952(%r31)
	li %r0, 6
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 13312
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
	ori %r4, %r4, 13312
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
	li %r0, 2
	stb %r0, 952(%r31)
	li %r0, 6
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 14336
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
	ori %r4, %r4, 14336
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
	li %r0, 3
	stb %r0, 952(%r31)
	li %r0, 6
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 15360
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
	ori %r4, %r4, 15360
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
	li %r0, 4
	stb %r0, 952(%r31)
	li %r0, 6
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 16384
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
	ori %r4, %r4, 16384
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
	li %r0, 5
	stb %r0, 952(%r31)
	li %r0, 6
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 17408
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
	ori %r4, %r4, 17408
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
	li %r0, 6
	stb %r0, 952(%r31)
	li %r0, 6
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 18432
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
	ori %r4, %r4, 18432
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
	li %r0, 0
	stb %r0, 952(%r31)
	li %r0, 7
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 20480
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
	ori %r4, %r4, 20480
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
	li %r0, 1
	stb %r0, 952(%r31)
	li %r0, 7
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 21504
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
	ori %r4, %r4, 21504
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
	li %r0, 2
	stb %r0, 952(%r31)
	li %r0, 7
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 22528
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
	ori %r4, %r4, 22528
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
	li %r0, 3
	stb %r0, 952(%r31)
	li %r0, 7
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 23552
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
	ori %r4, %r4, 23552
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
	li %r0, 4
	stb %r0, 952(%r31)
	li %r0, 7
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 24576
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
	ori %r4, %r4, 24576
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
	li %r0, 5
	stb %r0, 952(%r31)
	li %r0, 7
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 25600
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
	ori %r4, %r4, 25600
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
	li %r0, 6
	stb %r0, 952(%r31)
	li %r0, 7
	stb %r0, 953(%r31)
	lis %r3, 0
	ori %r3, %r3, 920
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 26624
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
	ori %r4, %r4, 26624
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
	lis %r3, 0
	ori %r3, %r3, 0
	add %r3, %r28, %r3
	lis %r4, 0
	ori %r4, %r4, 64
	lis %r5, 0
	ori %r5, %r5, 60
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
261:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 261b
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
	ori %r3, %r3, 21504
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 4096
	add %r4, %r31, %r4
	bl {vg_mldsa_ntt}
	lis %r3, 0
	ori %r3, %r3, 22528
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
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 33792
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 21504
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 34816
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 22528
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
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 41984
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 21504
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 43008
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 22528
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
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 50176
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 21504
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
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
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 58368
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 21504
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 59392
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 22528
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
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 1024
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 21504
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 2048
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 22528
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
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 9216
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 21504
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 10240
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 22528
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
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 12288
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 16384
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 13312
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 17408
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 14336
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 18432
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 15360
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 19456
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 16384
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 20480
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 17408
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 21504
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 18432
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 22528
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 1952
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
	ori %r3, %r3, 14336
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
	ori %r5, %r5, 1792
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 128
	bl {vg_mldsa_simple_bit_pack}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 20480
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 16384
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 21504
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 17408
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 22528
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 18432
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 23552
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 19456
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 24576
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 20480
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 25600
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 21504
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 26624
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 26624
	add %r4, %r31, %r4
	lis %r5, 0
	ori %r5, %r5, 22528
	add %r5, %r31, %r5
	bl {vg_mldsa_multiply_add_ntt}
	lis %r3, 0
	ori %r3, %r3, 2272
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
	ori %r3, %r3, 15360
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
	ori %r5, %r5, 1920
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
	li %r7, 1024
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
	li %r7, 64
	addi %r8, %r31, 200
	bl {vg_keccak_squeeze_scratch}
	lis %r3, 0
	ori %r3, %r3, 2048
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 0
	add %r4, %r28, %r4
	lis %r26, 0
	ori %r26, %r26, 64
	li %r12, 0
262:
	lbz %r5, 0(%r3)
	lbz %r6, 0(%r4)
	xor %r5, %r5, %r6
	or %r12, %r12, %r5
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r26, %r26, -1
	cmpldi %cr0, %r26, 0
	bne %cr0, 262b
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

vg_mldsa87_verify_message:
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
	li %r7, 2592
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
	bl {vg_mldsa87_verify}
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
