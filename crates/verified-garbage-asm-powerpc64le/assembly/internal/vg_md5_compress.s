// The functions of `src/internal/vg_md5_compress.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_md5_compress:
	cmpldi %cr0, %r5, 0
	beq %cr0, 20f
22:
	lwz %r6, 0(%r3)
	lwz %r7, 4(%r3)
	lwz %r8, 8(%r3)
	lwz %r9, 12(%r3)
	lis %r12, -1
	ori %r12, %r12, 65535
	lwz %r11, 0(%r4)
	add %r6, %r6, %r11
	lis %r11, -10390
	ori %r11, %r11, 42104
	add %r6, %r6, %r11
	xor %r10, %r8, %r9
	and %r10, %r10, %r7
	xor %r10, %r10, %r9
	add %r6, %r6, %r10
	rlwinm %r6, %r6, 7, 0, 31
	add %r6, %r6, %r7
	lwz %r11, 4(%r4)
	add %r9, %r9, %r11
	lis %r11, -5945
	ori %r11, %r11, 46934
	add %r9, %r9, %r11
	xor %r10, %r7, %r8
	and %r10, %r10, %r6
	xor %r10, %r10, %r8
	add %r9, %r9, %r10
	rlwinm %r9, %r9, 12, 0, 31
	add %r9, %r9, %r6
	lwz %r11, 8(%r4)
	add %r8, %r8, %r11
	lis %r11, 9248
	ori %r11, %r11, 28891
	add %r8, %r8, %r11
	xor %r10, %r6, %r7
	and %r10, %r10, %r9
	xor %r10, %r10, %r7
	add %r8, %r8, %r10
	rlwinm %r8, %r8, 17, 0, 31
	add %r8, %r8, %r9
	lwz %r11, 12(%r4)
	add %r7, %r7, %r11
	lis %r11, -15939
	ori %r11, %r11, 52974
	add %r7, %r7, %r11
	xor %r10, %r9, %r6
	and %r10, %r10, %r8
	xor %r10, %r10, %r6
	add %r7, %r7, %r10
	rlwinm %r7, %r7, 22, 0, 31
	add %r7, %r7, %r8
	lwz %r11, 16(%r4)
	add %r6, %r6, %r11
	lis %r11, -2692
	ori %r11, %r11, 4015
	add %r6, %r6, %r11
	xor %r10, %r8, %r9
	and %r10, %r10, %r7
	xor %r10, %r10, %r9
	add %r6, %r6, %r10
	rlwinm %r6, %r6, 7, 0, 31
	add %r6, %r6, %r7
	lwz %r11, 20(%r4)
	add %r9, %r9, %r11
	lis %r11, 18311
	ori %r11, %r11, 50730
	add %r9, %r9, %r11
	xor %r10, %r7, %r8
	and %r10, %r10, %r6
	xor %r10, %r10, %r8
	add %r9, %r9, %r10
	rlwinm %r9, %r9, 12, 0, 31
	add %r9, %r9, %r6
	lwz %r11, 24(%r4)
	add %r8, %r8, %r11
	lis %r11, -22480
	ori %r11, %r11, 17939
	add %r8, %r8, %r11
	xor %r10, %r6, %r7
	and %r10, %r10, %r9
	xor %r10, %r10, %r7
	add %r8, %r8, %r10
	rlwinm %r8, %r8, 17, 0, 31
	add %r8, %r8, %r9
	lwz %r11, 28(%r4)
	add %r7, %r7, %r11
	lis %r11, -698
	ori %r11, %r11, 38145
	add %r7, %r7, %r11
	xor %r10, %r9, %r6
	and %r10, %r10, %r8
	xor %r10, %r10, %r6
	add %r7, %r7, %r10
	rlwinm %r7, %r7, 22, 0, 31
	add %r7, %r7, %r8
	lwz %r11, 32(%r4)
	add %r6, %r6, %r11
	lis %r11, 27008
	ori %r11, %r11, 39128
	add %r6, %r6, %r11
	xor %r10, %r8, %r9
	and %r10, %r10, %r7
	xor %r10, %r10, %r9
	add %r6, %r6, %r10
	rlwinm %r6, %r6, 7, 0, 31
	add %r6, %r6, %r7
	lwz %r11, 36(%r4)
	add %r9, %r9, %r11
	lis %r11, -29884
	ori %r11, %r11, 63407
	add %r9, %r9, %r11
	xor %r10, %r7, %r8
	and %r10, %r10, %r6
	xor %r10, %r10, %r8
	add %r9, %r9, %r10
	rlwinm %r9, %r9, 12, 0, 31
	add %r9, %r9, %r6
	lwz %r11, 40(%r4)
	add %r8, %r8, %r11
	lis %r11, -1
	ori %r11, %r11, 23473
	add %r8, %r8, %r11
	xor %r10, %r6, %r7
	and %r10, %r10, %r9
	xor %r10, %r10, %r7
	add %r8, %r8, %r10
	rlwinm %r8, %r8, 17, 0, 31
	add %r8, %r8, %r9
	lwz %r11, 44(%r4)
	add %r7, %r7, %r11
	lis %r11, -30372
	ori %r11, %r11, 55230
	add %r7, %r7, %r11
	xor %r10, %r9, %r6
	and %r10, %r10, %r8
	xor %r10, %r10, %r6
	add %r7, %r7, %r10
	rlwinm %r7, %r7, 22, 0, 31
	add %r7, %r7, %r8
	lwz %r11, 48(%r4)
	add %r6, %r6, %r11
	lis %r11, 27536
	ori %r11, %r11, 4386
	add %r6, %r6, %r11
	xor %r10, %r8, %r9
	and %r10, %r10, %r7
	xor %r10, %r10, %r9
	add %r6, %r6, %r10
	rlwinm %r6, %r6, 7, 0, 31
	add %r6, %r6, %r7
	lwz %r11, 52(%r4)
	add %r9, %r9, %r11
	lis %r11, -616
	ori %r11, %r11, 29075
	add %r9, %r9, %r11
	xor %r10, %r7, %r8
	and %r10, %r10, %r6
	xor %r10, %r10, %r8
	add %r9, %r9, %r10
	rlwinm %r9, %r9, 12, 0, 31
	add %r9, %r9, %r6
	lwz %r11, 56(%r4)
	add %r8, %r8, %r11
	lis %r11, -22919
	ori %r11, %r11, 17294
	add %r8, %r8, %r11
	xor %r10, %r6, %r7
	and %r10, %r10, %r9
	xor %r10, %r10, %r7
	add %r8, %r8, %r10
	rlwinm %r8, %r8, 17, 0, 31
	add %r8, %r8, %r9
	lwz %r11, 60(%r4)
	add %r7, %r7, %r11
	lis %r11, 18868
	ori %r11, %r11, 2081
	add %r7, %r7, %r11
	xor %r10, %r9, %r6
	and %r10, %r10, %r8
	xor %r10, %r10, %r6
	add %r7, %r7, %r10
	rlwinm %r7, %r7, 22, 0, 31
	add %r7, %r7, %r8
	lwz %r11, 4(%r4)
	add %r6, %r6, %r11
	lis %r11, -2530
	ori %r11, %r11, 9570
	add %r6, %r6, %r11
	xor %r10, %r9, %r12
	and %r10, %r10, %r8
	add %r6, %r6, %r10
	and %r10, %r9, %r7
	add %r6, %r6, %r10
	rlwinm %r6, %r6, 5, 0, 31
	add %r6, %r6, %r7
	lwz %r11, 24(%r4)
	add %r9, %r9, %r11
	lis %r11, -16320
	ori %r11, %r11, 45888
	add %r9, %r9, %r11
	xor %r10, %r8, %r12
	and %r10, %r10, %r7
	add %r9, %r9, %r10
	and %r10, %r8, %r6
	add %r9, %r9, %r10
	rlwinm %r9, %r9, 9, 0, 31
	add %r9, %r9, %r6
	lwz %r11, 44(%r4)
	add %r8, %r8, %r11
	lis %r11, 9822
	ori %r11, %r11, 23121
	add %r8, %r8, %r11
	xor %r10, %r7, %r12
	and %r10, %r10, %r6
	add %r8, %r8, %r10
	and %r10, %r7, %r9
	add %r8, %r8, %r10
	rlwinm %r8, %r8, 14, 0, 31
	add %r8, %r8, %r9
	lwz %r11, 0(%r4)
	add %r7, %r7, %r11
	lis %r11, -5706
	ori %r11, %r11, 51114
	add %r7, %r7, %r11
	xor %r10, %r6, %r12
	and %r10, %r10, %r9
	add %r7, %r7, %r10
	and %r10, %r6, %r8
	add %r7, %r7, %r10
	rlwinm %r7, %r7, 20, 0, 31
	add %r7, %r7, %r8
	lwz %r11, 20(%r4)
	add %r6, %r6, %r11
	lis %r11, -10705
	ori %r11, %r11, 4189
	add %r6, %r6, %r11
	xor %r10, %r9, %r12
	and %r10, %r10, %r8
	add %r6, %r6, %r10
	and %r10, %r9, %r7
	add %r6, %r6, %r10
	rlwinm %r6, %r6, 5, 0, 31
	add %r6, %r6, %r7
	lwz %r11, 40(%r4)
	add %r9, %r9, %r11
	lis %r11, 580
	ori %r11, %r11, 5203
	add %r9, %r9, %r11
	xor %r10, %r8, %r12
	and %r10, %r10, %r7
	add %r9, %r9, %r10
	and %r10, %r8, %r6
	add %r9, %r9, %r10
	rlwinm %r9, %r9, 9, 0, 31
	add %r9, %r9, %r6
	lwz %r11, 60(%r4)
	add %r8, %r8, %r11
	lis %r11, -10079
	ori %r11, %r11, 59009
	add %r8, %r8, %r11
	xor %r10, %r7, %r12
	and %r10, %r10, %r6
	add %r8, %r8, %r10
	and %r10, %r7, %r9
	add %r8, %r8, %r10
	rlwinm %r8, %r8, 14, 0, 31
	add %r8, %r8, %r9
	lwz %r11, 16(%r4)
	add %r7, %r7, %r11
	lis %r11, -6189
	ori %r11, %r11, 64456
	add %r7, %r7, %r11
	xor %r10, %r6, %r12
	and %r10, %r10, %r9
	add %r7, %r7, %r10
	and %r10, %r6, %r8
	add %r7, %r7, %r10
	rlwinm %r7, %r7, 20, 0, 31
	add %r7, %r7, %r8
	lwz %r11, 36(%r4)
	add %r6, %r6, %r11
	lis %r11, 8673
	ori %r11, %r11, 52710
	add %r6, %r6, %r11
	xor %r10, %r9, %r12
	and %r10, %r10, %r8
	add %r6, %r6, %r10
	and %r10, %r9, %r7
	add %r6, %r6, %r10
	rlwinm %r6, %r6, 5, 0, 31
	add %r6, %r6, %r7
	lwz %r11, 56(%r4)
	add %r9, %r9, %r11
	lis %r11, -15561
	ori %r11, %r11, 2006
	add %r9, %r9, %r11
	xor %r10, %r8, %r12
	and %r10, %r10, %r7
	add %r9, %r9, %r10
	and %r10, %r8, %r6
	add %r9, %r9, %r10
	rlwinm %r9, %r9, 9, 0, 31
	add %r9, %r9, %r6
	lwz %r11, 12(%r4)
	add %r8, %r8, %r11
	lis %r11, -2859
	ori %r11, %r11, 3463
	add %r8, %r8, %r11
	xor %r10, %r7, %r12
	and %r10, %r10, %r6
	add %r8, %r8, %r10
	and %r10, %r7, %r9
	add %r8, %r8, %r10
	rlwinm %r8, %r8, 14, 0, 31
	add %r8, %r8, %r9
	lwz %r11, 32(%r4)
	add %r7, %r7, %r11
	lis %r11, 17754
	ori %r11, %r11, 5357
	add %r7, %r7, %r11
	xor %r10, %r6, %r12
	and %r10, %r10, %r9
	add %r7, %r7, %r10
	and %r10, %r6, %r8
	add %r7, %r7, %r10
	rlwinm %r7, %r7, 20, 0, 31
	add %r7, %r7, %r8
	lwz %r11, 52(%r4)
	add %r6, %r6, %r11
	lis %r11, -22045
	ori %r11, %r11, 59653
	add %r6, %r6, %r11
	xor %r10, %r9, %r12
	and %r10, %r10, %r8
	add %r6, %r6, %r10
	and %r10, %r9, %r7
	add %r6, %r6, %r10
	rlwinm %r6, %r6, 5, 0, 31
	add %r6, %r6, %r7
	lwz %r11, 8(%r4)
	add %r9, %r9, %r11
	lis %r11, -785
	ori %r11, %r11, 41976
	add %r9, %r9, %r11
	xor %r10, %r8, %r12
	and %r10, %r10, %r7
	add %r9, %r9, %r10
	and %r10, %r8, %r6
	add %r9, %r9, %r10
	rlwinm %r9, %r9, 9, 0, 31
	add %r9, %r9, %r6
	lwz %r11, 28(%r4)
	add %r8, %r8, %r11
	lis %r11, 26479
	ori %r11, %r11, 729
	add %r8, %r8, %r11
	xor %r10, %r7, %r12
	and %r10, %r10, %r6
	add %r8, %r8, %r10
	and %r10, %r7, %r9
	add %r8, %r8, %r10
	rlwinm %r8, %r8, 14, 0, 31
	add %r8, %r8, %r9
	lwz %r11, 48(%r4)
	add %r7, %r7, %r11
	lis %r11, -29398
	ori %r11, %r11, 19594
	add %r7, %r7, %r11
	xor %r10, %r6, %r12
	and %r10, %r10, %r9
	add %r7, %r7, %r10
	and %r10, %r6, %r8
	add %r7, %r7, %r10
	rlwinm %r7, %r7, 20, 0, 31
	add %r7, %r7, %r8
	lwz %r11, 20(%r4)
	add %r6, %r6, %r11
	lis %r11, -6
	ori %r11, %r11, 14658
	add %r6, %r6, %r11
	xor %r10, %r8, %r9
	xor %r10, %r10, %r7
	add %r6, %r6, %r10
	rlwinm %r6, %r6, 4, 0, 31
	add %r6, %r6, %r7
	lwz %r11, 32(%r4)
	add %r9, %r9, %r11
	lis %r11, -30863
	ori %r11, %r11, 63105
	add %r9, %r9, %r11
	xor %r10, %r7, %r8
	xor %r10, %r10, %r6
	add %r9, %r9, %r10
	rlwinm %r9, %r9, 11, 0, 31
	add %r9, %r9, %r6
	lwz %r11, 44(%r4)
	add %r8, %r8, %r11
	lis %r11, 28061
	ori %r11, %r11, 24866
	add %r8, %r8, %r11
	xor %r10, %r6, %r7
	xor %r10, %r10, %r9
	add %r8, %r8, %r10
	rlwinm %r8, %r8, 16, 0, 31
	add %r8, %r8, %r9
	lwz %r11, 56(%r4)
	add %r7, %r7, %r11
	lis %r11, -539
	ori %r11, %r11, 14348
	add %r7, %r7, %r11
	xor %r10, %r9, %r6
	xor %r10, %r10, %r8
	add %r7, %r7, %r10
	rlwinm %r7, %r7, 23, 0, 31
	add %r7, %r7, %r8
	lwz %r11, 4(%r4)
	add %r6, %r6, %r11
	lis %r11, -23362
	ori %r11, %r11, 59972
	add %r6, %r6, %r11
	xor %r10, %r8, %r9
	xor %r10, %r10, %r7
	add %r6, %r6, %r10
	rlwinm %r6, %r6, 4, 0, 31
	add %r6, %r6, %r7
	lwz %r11, 16(%r4)
	add %r9, %r9, %r11
	lis %r11, 19422
	ori %r11, %r11, 53161
	add %r9, %r9, %r11
	xor %r10, %r7, %r8
	xor %r10, %r10, %r6
	add %r9, %r9, %r10
	rlwinm %r9, %r9, 11, 0, 31
	add %r9, %r9, %r6
	lwz %r11, 28(%r4)
	add %r8, %r8, %r11
	lis %r11, -2373
	ori %r11, %r11, 19296
	add %r8, %r8, %r11
	xor %r10, %r6, %r7
	xor %r10, %r10, %r9
	add %r8, %r8, %r10
	rlwinm %r8, %r8, 16, 0, 31
	add %r8, %r8, %r9
	lwz %r11, 40(%r4)
	add %r7, %r7, %r11
	lis %r11, -16705
	ori %r11, %r11, 48240
	add %r7, %r7, %r11
	xor %r10, %r9, %r6
	xor %r10, %r10, %r8
	add %r7, %r7, %r10
	rlwinm %r7, %r7, 23, 0, 31
	add %r7, %r7, %r8
	lwz %r11, 52(%r4)
	add %r6, %r6, %r11
	lis %r11, 10395
	ori %r11, %r11, 32454
	add %r6, %r6, %r11
	xor %r10, %r8, %r9
	xor %r10, %r10, %r7
	add %r6, %r6, %r10
	rlwinm %r6, %r6, 4, 0, 31
	add %r6, %r6, %r7
	lwz %r11, 0(%r4)
	add %r9, %r9, %r11
	lis %r11, -5471
	ori %r11, %r11, 10234
	add %r9, %r9, %r11
	xor %r10, %r7, %r8
	xor %r10, %r10, %r6
	add %r9, %r9, %r10
	rlwinm %r9, %r9, 11, 0, 31
	add %r9, %r9, %r6
	lwz %r11, 12(%r4)
	add %r8, %r8, %r11
	lis %r11, -11025
	ori %r11, %r11, 12421
	add %r8, %r8, %r11
	xor %r10, %r6, %r7
	xor %r10, %r10, %r9
	add %r8, %r8, %r10
	rlwinm %r8, %r8, 16, 0, 31
	add %r8, %r8, %r9
	lwz %r11, 24(%r4)
	add %r7, %r7, %r11
	lis %r11, 1160
	ori %r11, %r11, 7429
	add %r7, %r7, %r11
	xor %r10, %r9, %r6
	xor %r10, %r10, %r8
	add %r7, %r7, %r10
	rlwinm %r7, %r7, 23, 0, 31
	add %r7, %r7, %r8
	lwz %r11, 36(%r4)
	add %r6, %r6, %r11
	lis %r11, -9772
	ori %r11, %r11, 53305
	add %r6, %r6, %r11
	xor %r10, %r8, %r9
	xor %r10, %r10, %r7
	add %r6, %r6, %r10
	rlwinm %r6, %r6, 4, 0, 31
	add %r6, %r6, %r7
	lwz %r11, 48(%r4)
	add %r9, %r9, %r11
	lis %r11, -6437
	ori %r11, %r11, 39397
	add %r9, %r9, %r11
	xor %r10, %r7, %r8
	xor %r10, %r10, %r6
	add %r9, %r9, %r10
	rlwinm %r9, %r9, 11, 0, 31
	add %r9, %r9, %r6
	lwz %r11, 60(%r4)
	add %r8, %r8, %r11
	lis %r11, 8098
	ori %r11, %r11, 31992
	add %r8, %r8, %r11
	xor %r10, %r6, %r7
	xor %r10, %r10, %r9
	add %r8, %r8, %r10
	rlwinm %r8, %r8, 16, 0, 31
	add %r8, %r8, %r9
	lwz %r11, 8(%r4)
	add %r7, %r7, %r11
	lis %r11, -15188
	ori %r11, %r11, 22117
	add %r7, %r7, %r11
	xor %r10, %r9, %r6
	xor %r10, %r10, %r8
	add %r7, %r7, %r10
	rlwinm %r7, %r7, 23, 0, 31
	add %r7, %r7, %r8
	lwz %r11, 0(%r4)
	add %r6, %r6, %r11
	lis %r11, -3031
	ori %r11, %r11, 8772
	add %r6, %r6, %r11
	xor %r10, %r9, %r12
	or %r10, %r10, %r7
	xor %r10, %r10, %r8
	add %r6, %r6, %r10
	rlwinm %r6, %r6, 6, 0, 31
	add %r6, %r6, %r7
	lwz %r11, 28(%r4)
	add %r9, %r9, %r11
	lis %r11, 17194
	ori %r11, %r11, 65431
	add %r9, %r9, %r11
	xor %r10, %r8, %r12
	or %r10, %r10, %r6
	xor %r10, %r10, %r7
	add %r9, %r9, %r10
	rlwinm %r9, %r9, 10, 0, 31
	add %r9, %r9, %r6
	lwz %r11, 56(%r4)
	add %r8, %r8, %r11
	lis %r11, -21612
	ori %r11, %r11, 9127
	add %r8, %r8, %r11
	xor %r10, %r7, %r12
	or %r10, %r10, %r9
	xor %r10, %r10, %r6
	add %r8, %r8, %r10
	rlwinm %r8, %r8, 15, 0, 31
	add %r8, %r8, %r9
	lwz %r11, 20(%r4)
	add %r7, %r7, %r11
	lis %r11, -877
	ori %r11, %r11, 41017
	add %r7, %r7, %r11
	xor %r10, %r6, %r12
	or %r10, %r10, %r8
	xor %r10, %r10, %r9
	add %r7, %r7, %r10
	rlwinm %r7, %r7, 21, 0, 31
	add %r7, %r7, %r8
	lwz %r11, 48(%r4)
	add %r6, %r6, %r11
	lis %r11, 25947
	ori %r11, %r11, 22979
	add %r6, %r6, %r11
	xor %r10, %r9, %r12
	or %r10, %r10, %r7
	xor %r10, %r10, %r8
	add %r6, %r6, %r10
	rlwinm %r6, %r6, 6, 0, 31
	add %r6, %r6, %r7
	lwz %r11, 12(%r4)
	add %r9, %r9, %r11
	lis %r11, -28916
	ori %r11, %r11, 52370
	add %r9, %r9, %r11
	xor %r10, %r8, %r12
	or %r10, %r10, %r6
	xor %r10, %r10, %r7
	add %r9, %r9, %r10
	rlwinm %r9, %r9, 10, 0, 31
	add %r9, %r9, %r6
	lwz %r11, 40(%r4)
	add %r8, %r8, %r11
	lis %r11, -17
	ori %r11, %r11, 62589
	add %r8, %r8, %r11
	xor %r10, %r7, %r12
	or %r10, %r10, %r9
	xor %r10, %r10, %r6
	add %r8, %r8, %r10
	rlwinm %r8, %r8, 15, 0, 31
	add %r8, %r8, %r9
	lwz %r11, 4(%r4)
	add %r7, %r7, %r11
	lis %r11, -31356
	ori %r11, %r11, 24017
	add %r7, %r7, %r11
	xor %r10, %r6, %r12
	or %r10, %r10, %r8
	xor %r10, %r10, %r9
	add %r7, %r7, %r10
	rlwinm %r7, %r7, 21, 0, 31
	add %r7, %r7, %r8
	lwz %r11, 32(%r4)
	add %r6, %r6, %r11
	lis %r11, 28584
	ori %r11, %r11, 32335
	add %r6, %r6, %r11
	xor %r10, %r9, %r12
	or %r10, %r10, %r7
	xor %r10, %r10, %r8
	add %r6, %r6, %r10
	rlwinm %r6, %r6, 6, 0, 31
	add %r6, %r6, %r7
	lwz %r11, 60(%r4)
	add %r9, %r9, %r11
	lis %r11, -468
	ori %r11, %r11, 59104
	add %r9, %r9, %r11
	xor %r10, %r8, %r12
	or %r10, %r10, %r6
	xor %r10, %r10, %r7
	add %r9, %r9, %r10
	rlwinm %r9, %r9, 10, 0, 31
	add %r9, %r9, %r6
	lwz %r11, 24(%r4)
	add %r8, %r8, %r11
	lis %r11, -23807
	ori %r11, %r11, 17172
	add %r8, %r8, %r11
	xor %r10, %r7, %r12
	or %r10, %r10, %r9
	xor %r10, %r10, %r6
	add %r8, %r8, %r10
	rlwinm %r8, %r8, 15, 0, 31
	add %r8, %r8, %r9
	lwz %r11, 52(%r4)
	add %r7, %r7, %r11
	lis %r11, 19976
	ori %r11, %r11, 4513
	add %r7, %r7, %r11
	xor %r10, %r6, %r12
	or %r10, %r10, %r8
	xor %r10, %r10, %r9
	add %r7, %r7, %r10
	rlwinm %r7, %r7, 21, 0, 31
	add %r7, %r7, %r8
	lwz %r11, 16(%r4)
	add %r6, %r6, %r11
	lis %r11, -2221
	ori %r11, %r11, 32386
	add %r6, %r6, %r11
	xor %r10, %r9, %r12
	or %r10, %r10, %r7
	xor %r10, %r10, %r8
	add %r6, %r6, %r10
	rlwinm %r6, %r6, 6, 0, 31
	add %r6, %r6, %r7
	lwz %r11, 44(%r4)
	add %r9, %r9, %r11
	lis %r11, -17094
	ori %r11, %r11, 62005
	add %r9, %r9, %r11
	xor %r10, %r8, %r12
	or %r10, %r10, %r6
	xor %r10, %r10, %r7
	add %r9, %r9, %r10
	rlwinm %r9, %r9, 10, 0, 31
	add %r9, %r9, %r6
	lwz %r11, 8(%r4)
	add %r8, %r8, %r11
	lis %r11, 10967
	ori %r11, %r11, 53947
	add %r8, %r8, %r11
	xor %r10, %r7, %r12
	or %r10, %r10, %r9
	xor %r10, %r10, %r6
	add %r8, %r8, %r10
	rlwinm %r8, %r8, 15, 0, 31
	add %r8, %r8, %r9
	lwz %r11, 36(%r4)
	add %r7, %r7, %r11
	lis %r11, -5242
	ori %r11, %r11, 54161
	add %r7, %r7, %r11
	xor %r10, %r6, %r12
	or %r10, %r10, %r8
	xor %r10, %r10, %r9
	add %r7, %r7, %r10
	rlwinm %r7, %r7, 21, 0, 31
	add %r7, %r7, %r8
	lwz %r10, 0(%r3)
	lwz %r11, 4(%r3)
	lwz %r12, 8(%r3)
	lwz %r0, 12(%r3)
	add %r6, %r6, %r10
	add %r7, %r7, %r11
	add %r8, %r8, %r12
	add %r9, %r9, %r0
	stw %r6, 0(%r3)
	stw %r7, 4(%r3)
	stw %r8, 8(%r3)
	stw %r9, 12(%r3)
	addi %r4, %r4, 64
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 22b
	b 21f
20:
21:
	blr
