// The functions of `src/internal/vg_mldsa44_verify_with_cache.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa44_verify_with_cache:
	stdu %r1, -48(%r1)
	std %r14, 32(%r1)
	stdu %r1, -48(%r1)
	std %r15, 32(%r1)
	addi %r14, %r7, 0
	addi %r15, %r8, 0
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
	ori %r3, %r3, 2336
	add %r3, %r28, %r3
	lis %r4, 0
	ori %r4, %r4, 84
	lis %r5, 0
	ori %r5, %r5, 80
	lis %r6, 0
	ori %r6, %r6, 8192
	add %r6, %r31, %r6
	lis %r7, 0
	ori %r7, %r7, 1024
	bl {vg_mldsa_hint_bit_unpack}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	cmpldi %cr0, %r24, 0
	bne %cr0, 20f
	b 21f
20:
	lis %r3, 0
	ori %r3, %r3, 32
	add %r3, %r28, %r3
	lis %r4, 0
	ori %r4, %r4, 576
	lis %r5, 1
	ori %r5, %r5, 65535
	lis %r6, 2
	ori %r6, %r6, 0
	lis %r7, 0
	ori %r7, %r7, 16384
	add %r7, %r31, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 16384
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 65458
	bl {vg_mldsa_norm_lt}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	lis %r3, 0
	ori %r3, %r3, 608
	add %r3, %r28, %r3
	lis %r4, 0
	ori %r4, %r4, 576
	lis %r5, 1
	ori %r5, %r5, 65535
	lis %r6, 2
	ori %r6, %r6, 0
	lis %r7, 0
	ori %r7, %r7, 17408
	add %r7, %r31, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 17408
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 65458
	bl {vg_mldsa_norm_lt}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	lis %r3, 0
	ori %r3, %r3, 1184
	add %r3, %r28, %r3
	lis %r4, 0
	ori %r4, %r4, 576
	lis %r5, 1
	ori %r5, %r5, 65535
	lis %r6, 2
	ori %r6, %r6, 0
	lis %r7, 0
	ori %r7, %r7, 18432
	add %r7, %r31, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 18432
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 65458
	bl {vg_mldsa_norm_lt}
	rlwinm %r3, %r3, 0, 0, 31
	and %r24, %r24, %r3
	lis %r3, 0
	ori %r3, %r3, 1760
	add %r3, %r28, %r3
	lis %r4, 0
	ori %r4, %r4, 576
	lis %r5, 1
	ori %r5, %r5, 65535
	lis %r6, 2
	ori %r6, %r6, 0
	lis %r7, 0
	ori %r7, %r7, 19456
	add %r7, %r31, %r7
	bl {vg_mldsa_bit_unpack}
	lis %r3, 0
	ori %r3, %r3, 19456
	add %r3, %r31, %r3
	lis %r4, 1
	ori %r4, %r4, 65458
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
29:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 29b
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
210:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 210b
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
211:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 211b
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
212:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 212b
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
213:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 213b
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
214:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 214b
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
215:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 215b
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
216:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 216b
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
217:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 217b
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
218:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 218b
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
219:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 219b
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
220:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 220b
	lis %r3, 0
	ori %r3, %r3, 0
	add %r3, %r28, %r3
	lis %r4, 0
	ori %r4, %r4, 32
	lis %r5, 0
	ori %r5, %r5, 39
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
221:
	lwz %r6, 0(%r4)
	and %r6, %r6, %r12
	stw %r6, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 221b
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
	cmpldi %cr0, %r15, 0
	bne %cr0, 222f
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
	b 223f
222:
	lis %r3, 0
	ori %r3, %r3, 0
	add %r3, %r14, %r3
	lis %r9, 0
	ori %r9, %r9, 24576
	add %r9, %r31, %r9
	lis %r5, 0
	ori %r5, %r5, 128
224:
	ld %r0, 0(%r3)
	std %r0, 0(%r9)
	addi %r3, %r3, 8
	addi %r9, %r9, 8
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 224b
223:
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
	lis %r5, 1
	ori %r5, %r5, 29696
	lis %r6, 0
	ori %r6, %r6, 27648
	add %r6, %r31, %r6
	bl {vg_mldsa_use_hint}
	lis %r3, 0
	ori %r3, %r3, 27648
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 43
	lis %r5, 0
	ori %r5, %r5, 1024
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 192
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
	cmpldi %cr0, %r15, 0
	bne %cr0, 225f
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
	b 226f
225:
	lis %r3, 0
	ori %r3, %r3, 1024
	add %r3, %r14, %r3
	lis %r9, 0
	ori %r9, %r9, 24576
	add %r9, %r31, %r9
	lis %r5, 0
	ori %r5, %r5, 128
227:
	ld %r0, 0(%r3)
	std %r0, 0(%r9)
	addi %r3, %r3, 8
	addi %r9, %r9, 8
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 227b
226:
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
	lis %r5, 1
	ori %r5, %r5, 29696
	lis %r6, 0
	ori %r6, %r6, 27648
	add %r6, %r31, %r6
	bl {vg_mldsa_use_hint}
	lis %r3, 0
	ori %r3, %r3, 27648
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 43
	lis %r5, 0
	ori %r5, %r5, 1216
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 192
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
	cmpldi %cr0, %r15, 0
	bne %cr0, 228f
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
	b 229f
228:
	lis %r3, 0
	ori %r3, %r3, 2048
	add %r3, %r14, %r3
	lis %r9, 0
	ori %r9, %r9, 24576
	add %r9, %r31, %r9
	lis %r5, 0
	ori %r5, %r5, 128
230:
	ld %r0, 0(%r3)
	std %r0, 0(%r9)
	addi %r3, %r3, 8
	addi %r9, %r9, 8
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 230b
229:
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
	lis %r5, 1
	ori %r5, %r5, 29696
	lis %r6, 0
	ori %r6, %r6, 27648
	add %r6, %r31, %r6
	bl {vg_mldsa_use_hint}
	lis %r3, 0
	ori %r3, %r3, 27648
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 43
	lis %r5, 0
	ori %r5, %r5, 1408
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 192
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
	cmpldi %cr0, %r15, 0
	bne %cr0, 231f
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
	b 232f
231:
	lis %r3, 0
	ori %r3, %r3, 3072
	add %r3, %r14, %r3
	lis %r9, 0
	ori %r9, %r9, 24576
	add %r9, %r31, %r9
	lis %r5, 0
	ori %r5, %r5, 128
233:
	ld %r0, 0(%r3)
	std %r0, 0(%r9)
	addi %r3, %r3, 8
	addi %r9, %r9, 8
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 233b
232:
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
	lis %r5, 1
	ori %r5, %r5, 29696
	lis %r6, 0
	ori %r6, %r6, 27648
	add %r6, %r31, %r6
	bl {vg_mldsa_use_hint}
	lis %r3, 0
	ori %r3, %r3, 27648
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 43
	lis %r5, 0
	ori %r5, %r5, 1600
	add %r5, %r31, %r5
	lis %r6, 0
	ori %r6, %r6, 192
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
	li %r7, 32
	addi %r8, %r31, 200
	bl {vg_keccak_squeeze_scratch}
	lis %r3, 0
	ori %r3, %r3, 2048
	add %r3, %r31, %r3
	lis %r4, 0
	ori %r4, %r4, 0
	add %r4, %r28, %r4
	lis %r26, 0
	ori %r26, %r26, 32
	li %r12, 0
234:
	lbz %r5, 0(%r3)
	lbz %r6, 0(%r4)
	xor %r5, %r5, %r6
	or %r12, %r12, %r5
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r26, %r26, -1
	cmpldi %cr0, %r26, 0
	bne %cr0, 234b
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
	ld %r15, 32(%r1)
	addi %r1, %r1, 48
	ld %r14, 32(%r1)
	addi %r1, %r1, 48
	blr
