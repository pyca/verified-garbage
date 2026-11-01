// The functions of `src/md5.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
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

vg_md5_init:
	lis %r8, 26437
	ori %r8, %r8, 8961
	stw %r8, 0(%r3)
	lis %r8, -4147
	ori %r8, %r8, 43913
	stw %r8, 4(%r3)
	lis %r8, -26438
	ori %r8, %r8, 56574
	stw %r8, 8(%r3)
	lis %r8, 4146
	ori %r8, %r8, 21622
	stw %r8, 12(%r3)
	blr

vg_md5_update:
	stdu %r1, -144(%r1)
	addi %r7, %r1, 32
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r26, 64(%r7)
	std %r27, 72(%r7)
	std %r28, 80(%r7)
	std %r29, 88(%r7)
	std %r30, 96(%r7)
	std %r31, 104(%r7)
	addi %r26, %r3, 0
	addi %r27, %r7, 0
	addi %r28, %r5, 0
	addi %r29, %r6, 0
	li %r8, 63
	and %r30, %r4, %r8
	cmpldi %cr0, %r29, 0
	beq %cr0, 20f
22:
	li %r9, 0
	cmpldi %cr0, %r30, 0
	beq %cr0, 23f
	li %r10, 64
	subf %r10, %r30, %r10
	rldicl %r8, %r29, 58, 6
	cmpldi %cr0, %r8, 0
	beq %cr0, 25f
	b 26f
25:
	add %r8, %r29, %r30
	rldicl %r8, %r8, 58, 6
	cmpldi %cr0, %r8, 0
	beq %cr0, 27f
	b 28f
27:
	addi %r10, %r29, 0
28:
26:
	subf %r29, %r10, %r29
	rldicl %r12, %r10, 61, 3
	cmpldi %cr0, %r12, 0
	beq %cr0, 29f
211:
	ld %r8, 0(%r28)
	add %r11, %r26, %r30
	std %r8, 16(%r11)
	addi %r28, %r28, 8
	addi %r30, %r30, 8
	addi %r10, %r10, -8
	rldicl %r12, %r10, 61, 3
	cmpldi %cr0, %r12, 0
	bne %cr0, 211b
	b 210f
29:
210:
	cmpldi %cr0, %r10, 0
	beq %cr0, 212f
214:
	lbz %r8, 0(%r28)
	add %r11, %r26, %r30
	stb %r8, 16(%r11)
	addi %r28, %r28, 1
	addi %r30, %r30, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 214b
	b 213f
212:
213:
	addi %r8, %r30, -64
	cmpldi %cr0, %r8, 0
	beq %cr0, 215f
	b 216f
215:
	addi %r4, %r26, 16
	li %r30, 0
	li %r9, 1
216:
	b 24f
23:
	rldicl %r8, %r29, 58, 6
	cmpldi %cr0, %r8, 0
	beq %cr0, 217f
	addi %r4, %r28, 0
	rldicl %r9, %r29, 58, 6
	rldicr %r8, %r9, 6, 57
	add %r28, %r28, %r8
	subf %r29, %r8, %r29
	b 218f
217:
	li %r10, 64
	subf %r10, %r30, %r10
	rldicl %r8, %r29, 58, 6
	cmpldi %cr0, %r8, 0
	beq %cr0, 219f
	b 220f
219:
	add %r8, %r29, %r30
	rldicl %r8, %r8, 58, 6
	cmpldi %cr0, %r8, 0
	beq %cr0, 221f
	b 222f
221:
	addi %r10, %r29, 0
222:
220:
	subf %r29, %r10, %r29
	rldicl %r12, %r10, 61, 3
	cmpldi %cr0, %r12, 0
	beq %cr0, 223f
225:
	ld %r8, 0(%r28)
	add %r11, %r26, %r30
	std %r8, 16(%r11)
	addi %r28, %r28, 8
	addi %r30, %r30, 8
	addi %r10, %r10, -8
	rldicl %r12, %r10, 61, 3
	cmpldi %cr0, %r12, 0
	bne %cr0, 225b
	b 224f
223:
224:
	cmpldi %cr0, %r10, 0
	beq %cr0, 226f
228:
	lbz %r8, 0(%r28)
	add %r11, %r26, %r30
	stb %r8, 16(%r11)
	addi %r28, %r28, 1
	addi %r30, %r30, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 228b
	b 227f
226:
227:
	addi %r8, %r30, -64
	cmpldi %cr0, %r8, 0
	beq %cr0, 229f
	b 230f
229:
	addi %r4, %r26, 16
	li %r30, 0
	li %r9, 1
230:
218:
24:
	cmpldi %cr0, %r9, 0
	beq %cr0, 231f
	addi %r3, %r26, 0
	addi %r5, %r9, 0
	addi %r6, %r27, 0
	bl {vg_md5_compress}
	b 232f
231:
232:
	cmpldi %cr0, %r29, 0
	bne %cr0, 22b
	b 21f
20:
21:
	ld %r26, 64(%r27)
	ld %r28, 80(%r27)
	ld %r29, 88(%r27)
	ld %r30, 96(%r27)
	ld %r31, 104(%r27)
	ld %r27, 72(%r27)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	addi %r1, %r1, 144
	blr

vg_md5_finalize:
	stdu %r1, -144(%r1)
	addi %r6, %r1, 32
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r26, 64(%r6)
	std %r27, 72(%r6)
	std %r28, 80(%r6)
	std %r29, 88(%r6)
	std %r30, 96(%r6)
	std %r31, 104(%r6)
	addi %r26, %r3, 0
	addi %r27, %r6, 0
	addi %r28, %r5, 0
	addi %r29, %r4, 0
	li %r8, 63
	and %r30, %r29, %r8
	li %r8, 128
	add %r11, %r26, %r30
	stb %r8, 16(%r11)
	addi %r30, %r30, 1
	addi %r31, %r30, 7
	rldicl %r31, %r31, 58, 6
20:
	li %r10, 64
	cmpldi %cr0, %r31, 0
	beq %cr0, 21f
	b 22f
21:
	li %r10, 56
22:
	li %r8, 0
	subf %r10, %r30, %r10
	rldicl %r12, %r10, 61, 3
	cmpldi %cr0, %r12, 0
	beq %cr0, 23f
25:
	add %r11, %r26, %r30
	std %r8, 16(%r11)
	addi %r30, %r30, 8
	addi %r10, %r10, -8
	rldicl %r12, %r10, 61, 3
	cmpldi %cr0, %r12, 0
	bne %cr0, 25b
	b 24f
23:
24:
	cmpldi %cr0, %r10, 0
	beq %cr0, 26f
28:
	add %r11, %r26, %r30
	stb %r8, 16(%r11)
	addi %r30, %r30, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 28b
	b 27f
26:
27:
	cmpldi %cr0, %r31, 0
	beq %cr0, 29f
	b 210f
29:
	add %r8, %r29, %r29
	add %r8, %r8, %r8
	add %r8, %r8, %r8
	std %r8, 72(%r26)
210:
	addi %r4, %r26, 16
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_md5_compress}
	li %r30, 0
	addi %r31, %r31, -1
	cmpldi %cr0, %r31, 0
	beq %cr0, 20b
	lwz %r8, 0(%r26)
	stw %r8, 0(%r28)
	lwz %r8, 4(%r26)
	stw %r8, 4(%r28)
	lwz %r8, 8(%r26)
	stw %r8, 8(%r28)
	lwz %r8, 12(%r26)
	stw %r8, 12(%r28)
	ld %r26, 64(%r27)
	ld %r28, 80(%r27)
	ld %r29, 88(%r27)
	ld %r30, 96(%r27)
	ld %r31, 104(%r27)
	ld %r27, 72(%r27)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	addi %r1, %r1, 144
	blr

vg_md5_update_scratch:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r26, 64(%r7)
	std %r27, 72(%r7)
	std %r28, 80(%r7)
	std %r29, 88(%r7)
	std %r30, 96(%r7)
	std %r31, 104(%r7)
	addi %r26, %r3, 0
	addi %r27, %r7, 0
	addi %r28, %r5, 0
	addi %r29, %r6, 0
	li %r8, 63
	and %r30, %r4, %r8
	cmpldi %cr0, %r29, 0
	beq %cr0, 20f
22:
	li %r9, 0
	cmpldi %cr0, %r30, 0
	beq %cr0, 23f
	li %r10, 64
	subf %r10, %r30, %r10
	rldicl %r8, %r29, 58, 6
	cmpldi %cr0, %r8, 0
	beq %cr0, 25f
	b 26f
25:
	add %r8, %r29, %r30
	rldicl %r8, %r8, 58, 6
	cmpldi %cr0, %r8, 0
	beq %cr0, 27f
	b 28f
27:
	addi %r10, %r29, 0
28:
26:
	subf %r29, %r10, %r29
	rldicl %r12, %r10, 61, 3
	cmpldi %cr0, %r12, 0
	beq %cr0, 29f
211:
	ld %r8, 0(%r28)
	add %r11, %r26, %r30
	std %r8, 16(%r11)
	addi %r28, %r28, 8
	addi %r30, %r30, 8
	addi %r10, %r10, -8
	rldicl %r12, %r10, 61, 3
	cmpldi %cr0, %r12, 0
	bne %cr0, 211b
	b 210f
29:
210:
	cmpldi %cr0, %r10, 0
	beq %cr0, 212f
214:
	lbz %r8, 0(%r28)
	add %r11, %r26, %r30
	stb %r8, 16(%r11)
	addi %r28, %r28, 1
	addi %r30, %r30, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 214b
	b 213f
212:
213:
	addi %r8, %r30, -64
	cmpldi %cr0, %r8, 0
	beq %cr0, 215f
	b 216f
215:
	addi %r4, %r26, 16
	li %r30, 0
	li %r9, 1
216:
	b 24f
23:
	rldicl %r8, %r29, 58, 6
	cmpldi %cr0, %r8, 0
	beq %cr0, 217f
	addi %r4, %r28, 0
	rldicl %r9, %r29, 58, 6
	rldicr %r8, %r9, 6, 57
	add %r28, %r28, %r8
	subf %r29, %r8, %r29
	b 218f
217:
	li %r10, 64
	subf %r10, %r30, %r10
	rldicl %r8, %r29, 58, 6
	cmpldi %cr0, %r8, 0
	beq %cr0, 219f
	b 220f
219:
	add %r8, %r29, %r30
	rldicl %r8, %r8, 58, 6
	cmpldi %cr0, %r8, 0
	beq %cr0, 221f
	b 222f
221:
	addi %r10, %r29, 0
222:
220:
	subf %r29, %r10, %r29
	rldicl %r12, %r10, 61, 3
	cmpldi %cr0, %r12, 0
	beq %cr0, 223f
225:
	ld %r8, 0(%r28)
	add %r11, %r26, %r30
	std %r8, 16(%r11)
	addi %r28, %r28, 8
	addi %r30, %r30, 8
	addi %r10, %r10, -8
	rldicl %r12, %r10, 61, 3
	cmpldi %cr0, %r12, 0
	bne %cr0, 225b
	b 224f
223:
224:
	cmpldi %cr0, %r10, 0
	beq %cr0, 226f
228:
	lbz %r8, 0(%r28)
	add %r11, %r26, %r30
	stb %r8, 16(%r11)
	addi %r28, %r28, 1
	addi %r30, %r30, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 228b
	b 227f
226:
227:
	addi %r8, %r30, -64
	cmpldi %cr0, %r8, 0
	beq %cr0, 229f
	b 230f
229:
	addi %r4, %r26, 16
	li %r30, 0
	li %r9, 1
230:
218:
24:
	cmpldi %cr0, %r9, 0
	beq %cr0, 231f
	addi %r3, %r26, 0
	addi %r5, %r9, 0
	addi %r6, %r27, 0
	bl {vg_md5_compress}
	b 232f
231:
232:
	cmpldi %cr0, %r29, 0
	bne %cr0, 22b
	b 21f
20:
21:
	ld %r26, 64(%r27)
	ld %r28, 80(%r27)
	ld %r29, 88(%r27)
	ld %r30, 96(%r27)
	ld %r31, 104(%r27)
	ld %r27, 72(%r27)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	blr

vg_md5_finalize_scratch:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r26, 64(%r6)
	std %r27, 72(%r6)
	std %r28, 80(%r6)
	std %r29, 88(%r6)
	std %r30, 96(%r6)
	std %r31, 104(%r6)
	addi %r26, %r3, 0
	addi %r27, %r6, 0
	addi %r28, %r5, 0
	addi %r29, %r4, 0
	li %r8, 63
	and %r30, %r29, %r8
	li %r8, 128
	add %r11, %r26, %r30
	stb %r8, 16(%r11)
	addi %r30, %r30, 1
	addi %r31, %r30, 7
	rldicl %r31, %r31, 58, 6
20:
	li %r10, 64
	cmpldi %cr0, %r31, 0
	beq %cr0, 21f
	b 22f
21:
	li %r10, 56
22:
	li %r8, 0
	subf %r10, %r30, %r10
	rldicl %r12, %r10, 61, 3
	cmpldi %cr0, %r12, 0
	beq %cr0, 23f
25:
	add %r11, %r26, %r30
	std %r8, 16(%r11)
	addi %r30, %r30, 8
	addi %r10, %r10, -8
	rldicl %r12, %r10, 61, 3
	cmpldi %cr0, %r12, 0
	bne %cr0, 25b
	b 24f
23:
24:
	cmpldi %cr0, %r10, 0
	beq %cr0, 26f
28:
	add %r11, %r26, %r30
	stb %r8, 16(%r11)
	addi %r30, %r30, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 28b
	b 27f
26:
27:
	cmpldi %cr0, %r31, 0
	beq %cr0, 29f
	b 210f
29:
	add %r8, %r29, %r29
	add %r8, %r8, %r8
	add %r8, %r8, %r8
	std %r8, 72(%r26)
210:
	addi %r4, %r26, 16
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_md5_compress}
	li %r30, 0
	addi %r31, %r31, -1
	cmpldi %cr0, %r31, 0
	beq %cr0, 20b
	lwz %r8, 0(%r26)
	stw %r8, 0(%r28)
	lwz %r8, 4(%r26)
	stw %r8, 4(%r28)
	lwz %r8, 8(%r26)
	stw %r8, 8(%r28)
	lwz %r8, 12(%r26)
	stw %r8, 12(%r28)
	ld %r26, 64(%r27)
	ld %r28, 80(%r27)
	ld %r29, 88(%r27)
	ld %r30, 96(%r27)
	ld %r31, 104(%r27)
	ld %r27, 72(%r27)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	blr
