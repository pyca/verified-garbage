// The functions of `src/internal/vg_mldsa87_sign_with_cache.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa87_sign_with_cache:
	stdu %r1, -48(%r1)
	std %r14, 32(%r1)
	stdu %r1, -48(%r1)
	std %r15, 32(%r1)
	addi %r14, %r8, 0
	addi %r15, %r9, 0
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
	cmpldi %cr0, %r15, 0
	bne %cr0, 25f
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
	b 26f
25:
	lis %r3, 0
	ori %r3, %r3, 0
	add %r3, %r14, %r3
	lis %r9, 0
	ori %r9, %r9, 40960
	add %r9, %r31, %r9
	lis %r5, 0
	ori %r5, %r5, 128
27:
	ld %r0, 0(%r3)
	std %r0, 0(%r9)
	addi %r3, %r3, 8
	addi %r9, %r9, 8
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 27b
	lis %r3, 0
	ori %r3, %r3, 1024
	add %r3, %r14, %r3
	lis %r9, 0
	ori %r9, %r9, 41984
	add %r9, %r31, %r9
	lis %r5, 0
	ori %r5, %r5, 128
28:
	ld %r0, 0(%r3)
	std %r0, 0(%r9)
	addi %r3, %r3, 8
	addi %r9, %r9, 8
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 28b
	lis %r3, 0
	ori %r3, %r3, 2048
	add %r3, %r14, %r3
	lis %r9, 0
	ori %r9, %r9, 43008
	add %r9, %r31, %r9
	lis %r5, 0
	ori %r5, %r5, 128
29:
	ld %r0, 0(%r3)
	std %r0, 0(%r9)
	addi %r3, %r3, 8
	addi %r9, %r9, 8
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 29b
	lis %r3, 0
	ori %r3, %r3, 3072
	add %r3, %r14, %r3
	lis %r9, 0
	ori %r9, %r9, 44032
	add %r9, %r31, %r9
	lis %r5, 0
	ori %r5, %r5, 128
210:
	ld %r0, 0(%r3)
	std %r0, 0(%r9)
	addi %r3, %r3, 8
	addi %r9, %r9, 8
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 210b
	lis %r3, 0
	ori %r3, %r3, 4096
	add %r3, %r14, %r3
	lis %r9, 0
	ori %r9, %r9, 45056
	add %r9, %r31, %r9
	lis %r5, 0
	ori %r5, %r5, 128
211:
	ld %r0, 0(%r3)
	std %r0, 0(%r9)
	addi %r3, %r3, 8
	addi %r9, %r9, 8
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 211b
	lis %r3, 0
	ori %r3, %r3, 5120
	add %r3, %r14, %r3
	lis %r9, 0
	ori %r9, %r9, 46080
	add %r9, %r31, %r9
	lis %r5, 0
	ori %r5, %r5, 128
212:
	ld %r0, 0(%r3)
	std %r0, 0(%r9)
	addi %r3, %r3, 8
	addi %r9, %r9, 8
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 212b
	lis %r3, 0
	ori %r3, %r3, 6144
	add %r3, %r14, %r3
	lis %r9, 0
	ori %r9, %r9, 47104
	add %r9, %r31, %r9
	lis %r5, 0
	ori %r5, %r5, 128
213:
	ld %r0, 0(%r3)
	std %r0, 0(%r9)
	addi %r3, %r3, 8
	addi %r9, %r9, 8
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 213b
	lis %r3, 0
	ori %r3, %r3, 7168
	add %r3, %r14, %r3
	lis %r9, 0
	ori %r9, %r9, 48128
	add %r9, %r31, %r9
	lis %r5, 0
	ori %r5, %r5, 128
214:
	ld %r0, 0(%r3)
	std %r0, 0(%r9)
	addi %r3, %r3, 8
	addi %r9, %r9, 8
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 214b
	lis %r3, 0
	ori %r3, %r3, 8192
	add %r3, %r14, %r3
	lis %r9, 0
	ori %r9, %r9, 49152
	add %r9, %r31, %r9
	lis %r5, 0
	ori %r5, %r5, 128
215:
	ld %r0, 0(%r3)
	std %r0, 0(%r9)
	addi %r3, %r3, 8
	addi %r9, %r9, 8
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 215b
	lis %r3, 0
	ori %r3, %r3, 9216
	add %r3, %r14, %r3
	lis %r9, 0
	ori %r9, %r9, 50176
	add %r9, %r31, %r9
	lis %r5, 0
	ori %r5, %r5, 128
216:
	ld %r0, 0(%r3)
	std %r0, 0(%r9)
	addi %r3, %r3, 8
	addi %r9, %r9, 8
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 216b
	lis %r3, 0
	ori %r3, %r3, 10240
	add %r3, %r14, %r3
	lis %r9, 0
	ori %r9, %r9, 51200
	add %r9, %r31, %r9
	lis %r5, 0
	ori %r5, %r5, 128
217:
	ld %r0, 0(%r3)
	std %r0, 0(%r9)
	addi %r3, %r3, 8
	addi %r9, %r9, 8
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 217b
	lis %r3, 0
	ori %r3, %r3, 11264
	add %r3, %r14, %r3
	lis %r9, 0
	ori %r9, %r9, 52224
	add %r9, %r31, %r9
	lis %r5, 0
	ori %r5, %r5, 128
218:
	ld %r0, 0(%r3)
	std %r0, 0(%r9)
	addi %r3, %r3, 8
	addi %r9, %r9, 8
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 218b
	lis %r3, 0
	ori %r3, %r3, 12288
	add %r3, %r14, %r3
	lis %r9, 0
	ori %r9, %r9, 53248
	add %r9, %r31, %r9
	lis %r5, 0
	ori %r5, %r5, 128
219:
	ld %r0, 0(%r3)
	std %r0, 0(%r9)
	addi %r3, %r3, 8
	addi %r9, %r9, 8
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 219b
	lis %r3, 0
	ori %r3, %r3, 13312
	add %r3, %r14, %r3
	lis %r9, 0
	ori %r9, %r9, 54272
	add %r9, %r31, %r9
	lis %r5, 0
	ori %r5, %r5, 128
220:
	ld %r0, 0(%r3)
	std %r0, 0(%r9)
	addi %r3, %r3, 8
	addi %r9, %r9, 8
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 220b
	lis %r3, 0
	ori %r3, %r3, 14336
	add %r3, %r14, %r3
	lis %r9, 0
	ori %r9, %r9, 55296
	add %r9, %r31, %r9
	lis %r5, 0
	ori %r5, %r5, 128
221:
	ld %r0, 0(%r3)
	std %r0, 0(%r9)
	addi %r3, %r3, 8
	addi %r9, %r9, 8
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 221b
	lis %r3, 0
	ori %r3, %r3, 15360
	add %r3, %r14, %r3
	lis %r9, 0
	ori %r9, %r9, 56320
	add %r9, %r31, %r9
	lis %r5, 0
	ori %r5, %r5, 128
222:
	ld %r0, 0(%r3)
	std %r0, 0(%r9)
	addi %r3, %r3, 8
	addi %r9, %r9, 8
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 222b
	lis %r3, 0
	ori %r3, %r3, 16384
	add %r3, %r14, %r3
	lis %r9, 0
	ori %r9, %r9, 57344
	add %r9, %r31, %r9
	lis %r5, 0
	ori %r5, %r5, 128
223:
	ld %r0, 0(%r3)
	std %r0, 0(%r9)
	addi %r3, %r3, 8
	addi %r9, %r9, 8
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 223b
	lis %r3, 0
	ori %r3, %r3, 17408
	add %r3, %r14, %r3
	lis %r9, 0
	ori %r9, %r9, 58368
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
	lis %r3, 0
	ori %r3, %r3, 18432
	add %r3, %r14, %r3
	lis %r9, 0
	ori %r9, %r9, 59392
	add %r9, %r31, %r9
	lis %r5, 0
	ori %r5, %r5, 128
225:
	ld %r0, 0(%r3)
	std %r0, 0(%r9)
	addi %r3, %r3, 8
	addi %r9, %r9, 8
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 225b
	lis %r3, 0
	ori %r3, %r3, 19456
	add %r3, %r14, %r3
	lis %r9, 0
	ori %r9, %r9, 60416
	add %r9, %r31, %r9
	lis %r5, 0
	ori %r5, %r5, 128
226:
	ld %r0, 0(%r3)
	std %r0, 0(%r9)
	addi %r3, %r3, 8
	addi %r9, %r9, 8
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 226b
	lis %r3, 0
	ori %r3, %r3, 20480
	add %r3, %r14, %r3
	lis %r9, 0
	ori %r9, %r9, 61440
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
	lis %r3, 0
	ori %r3, %r3, 21504
	add %r3, %r14, %r3
	lis %r9, 0
	ori %r9, %r9, 62464
	add %r9, %r31, %r9
	lis %r5, 0
	ori %r5, %r5, 128
228:
	ld %r0, 0(%r3)
	std %r0, 0(%r9)
	addi %r3, %r3, 8
	addi %r9, %r9, 8
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 228b
	lis %r3, 0
	ori %r3, %r3, 22528
	add %r3, %r14, %r3
	lis %r9, 0
	ori %r9, %r9, 63488
	add %r9, %r31, %r9
	lis %r5, 0
	ori %r5, %r5, 128
229:
	ld %r0, 0(%r3)
	std %r0, 0(%r9)
	addi %r3, %r3, 8
	addi %r9, %r9, 8
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 229b
26:
	li %r27, 0
	li %r25, 814
230:
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
231:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 231b
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
232:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 232b
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
233:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 233b
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
234:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 234b
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
235:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 235b
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
236:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 236b
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
237:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 237b
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
	bne %cr0, 238f
	li %r24, 0
	li %r25, 1
	b 239f
238:
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
	bne %cr0, 240f
	b 241f
240:
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
	bne %cr0, 242f
	b 243f
242:
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
	bne %cr0, 244f
	b 245f
244:
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
	bne %cr0, 246f
	b 247f
246:
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
	bne %cr0, 248f
	b 249f
248:
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
	bne %cr0, 250f
	b 251f
250:
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
	bne %cr0, 252f
	b 253f
252:
253:
251:
249:
247:
245:
243:
241:
	cmpldi %cr0, %r24, 0
	bne %cr0, 254f
	b 255f
254:
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
	bne %cr0, 256f
	b 257f
256:
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
	bne %cr0, 258f
	b 259f
258:
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
	bne %cr0, 260f
	b 261f
260:
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
	bne %cr0, 262f
	b 263f
262:
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
	bne %cr0, 264f
	b 265f
264:
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
	bne %cr0, 266f
	b 267f
266:
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
	bne %cr0, 268f
	b 269f
268:
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
	bne %cr0, 270f
	b 271f
270:
271:
269:
267:
265:
263:
261:
259:
257:
	cmpldi %cr0, %r24, 0
	bne %cr0, 272f
	b 273f
272:
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
274:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 274b
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
275:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 275b
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
276:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 276b
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
277:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 277b
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
278:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 278b
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
279:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 279b
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
280:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 280b
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
281:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 281b
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
273:
255:
	cmpldi %cr0, %r24, 0
	bne %cr0, 282f
	addi %r27, %r27, 7
	b 283f
282:
	li %r25, 1
283:
239:
	addi %r25, %r25, -1
	cmpldi %cr0, %r25, 0
	bne %cr0, 230b
	cmpldi %cr0, %r24, 0
	bne %cr0, 284f
	b 285f
284:
	addi %r3, %r31, 1040
	addi %r4, %r28, 0
	li %r5, 64
286:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 286b
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
285:
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
	ld %r15, 32(%r1)
	addi %r1, %r1, 48
	ld %r14, 32(%r1)
	addi %r1, %r1, 48
	blr
	.p2align 6
