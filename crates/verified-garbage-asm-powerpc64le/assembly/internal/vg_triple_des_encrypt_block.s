// The functions of `src/internal/vg_triple_des_encrypt_block.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_triple_des_encrypt_block:
	std %r14, 0(%r5)
	std %r15, 8(%r5)
	std %r16, 16(%r5)
	std %r17, 24(%r5)
	std %r18, 32(%r5)
	std %r19, 40(%r5)
	std %r20, 48(%r5)
	std %r21, 56(%r5)
	std %r22, 64(%r5)
	std %r23, 72(%r5)
	std %r24, 80(%r5)
	std %r25, 88(%r5)
	std %r26, 96(%r5)
	std %r27, 104(%r5)
	std %r28, 112(%r5)
	lis %r6, -29425
	ori %r6, %r6, 59815
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 18588
	ori %r6, %r6, 10365
	std %r6, 120(%r5)
	lis %r6, 32185
	ori %r6, %r6, 51146
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 62934
	ori %r6, %r6, 58201
	std %r6, 128(%r5)
	lis %r6, 10450
	ori %r6, %r6, 20541
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 34273
	ori %r6, %r6, 34786
	std %r6, 136(%r5)
	lis %r6, -6199
	ori %r6, %r6, 51141
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 40670
	ori %r6, %r6, 63405
	std %r6, 144(%r5)
	lis %r6, -8479
	ori %r6, %r6, 19147
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 9466
	ori %r6, %r6, 29720
	std %r6, 152(%r5)
	lis %r6, -27207
	ori %r6, %r6, 43717
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 31966
	ori %r6, %r6, 50085
	std %r6, 160(%r5)
	lis %r6, 17021
	ori %r6, %r6, 44294
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 45663
	ori %r6, %r6, 48449
	std %r6, 168(%r5)
	lis %r6, 23123
	ori %r6, %r6, 42803
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 22429
	ori %r6, %r6, 41785
	std %r6, 176(%r5)
	lis %r6, -7844
	ori %r6, %r6, 34192
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 40489
	ori %r6, %r6, 40899
	std %r6, 184(%r5)
	lis %r6, 27699
	ori %r6, %r6, 54835
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 47806
	ori %r6, %r6, 47065
	std %r6, 192(%r5)
	lis %r6, -24697
	ori %r6, %r6, 62435
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 31106
	ori %r6, %r6, 24735
	std %r6, 200(%r5)
	lis %r6, -397
	ori %r6, %r6, 22444
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 42974
	ori %r6, %r6, 58169
	std %r6, 208(%r5)
	lis %r6, 6070
	ori %r6, %r6, 16252
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 60358
	ori %r6, %r6, 57790
	std %r6, 216(%r5)
	lis %r6, 14647
	ori %r6, %r6, 47788
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 27711
	ori %r6, %r6, 45881
	std %r6, 224(%r5)
	lis %r6, 29736
	ori %r6, %r6, 1754
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 7224
	ori %r6, %r6, 56100
	std %r6, 232(%r5)
	lis %r6, -14747
	ori %r6, %r6, 32604
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 28317
	ori %r6, %r6, 16117
	std %r6, 240(%r5)
	lis %r6, -3165
	ori %r6, %r6, 45812
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 61808
	ori %r6, %r6, 22026
	std %r6, 248(%r5)
	lis %r6, 22234
	ori %r6, %r6, 62261
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 14278
	ori %r6, %r6, 27635
	std %r6, 256(%r5)
	lis %r6, -15074
	ori %r6, %r6, 11842
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 13837
	ori %r6, %r6, 63804
	std %r6, 264(%r5)
	lis %r6, -17186
	ori %r6, %r6, 54869
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 50924
	ori %r6, %r6, 24489
	std %r6, 272(%r5)
	lis %r6, 27028
	ori %r6, %r6, 7272
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 23107
	ori %r6, %r6, 50086
	std %r6, 280(%r5)
	lis %r6, 21878
	ori %r6, %r6, 51770
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 21854
	ori %r6, %r6, 51557
	std %r6, 288(%r5)
	lis %r6, -17205
	ori %r6, %r6, 51125
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 28580
	ori %r6, %r6, 7899
	std %r6, 296(%r5)
	lis %r6, 27486
	ori %r6, %r6, 64092
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 22234
	ori %r6, %r6, 59349
	std %r6, 304(%r5)
	lis %r6, 14905
	ori %r6, %r6, 27486
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 50974
	ori %r6, %r6, 2805
	std %r6, 312(%r5)
	lis %r6, 27701
	ori %r6, %r6, 55242
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 23934
	ori %r6, %r6, 56981
	std %r6, 320(%r5)
	lis %r6, 22112
	ori %r6, %r6, 37929
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 41175
	ori %r6, %r6, 42336
	std %r6, 328(%r5)
	lis %r6, 23747
	ori %r6, %r6, 65363
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 58332
	ori %r6, %r6, 59963
	std %r6, 336(%r5)
	lis %r6, -24502
	ori %r6, %r6, 53633
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 3509
	ori %r6, %r6, 15449
	std %r6, 344(%r5)
	lis %r6, 13213
	ori %r6, %r6, 52906
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 27702
	ori %r6, %r6, 23909
	std %r6, 352(%r5)
	lis %r6, 3061
	ori %r6, %r6, 30751
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 54123
	ori %r6, %r6, 17031
	std %r6, 360(%r5)
	lis %r6, -4145
	ori %r6, %r6, 47779
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 32691
	ori %r6, %r6, 56933
	std %r6, 368(%r5)
	lis %r6, 0
	ori %r6, %r6, 0
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 3
	ori %r6, %r6, 65535
	std %r6, 376(%r5)
	lis %r6, 0
	ori %r6, %r6, 1023
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 0
	ori %r6, %r6, 1023
	std %r6, 384(%r5)
	lis %r6, 63
	ori %r6, %r6, 63
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 63
	ori %r6, %r6, 63
	std %r6, 392(%r5)
	lis %r6, 0
	ori %r6, %r6, 0
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 255
	ori %r6, %r6, 65535
	std %r6, 400(%r5)
	lis %r6, 0
	ori %r6, %r6, 4095
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 0
	ori %r6, %r6, 4095
	std %r6, 408(%r5)
	lis %r6, 63
	ori %r6, %r6, 63
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 63
	ori %r6, %r6, 63
	std %r6, 416(%r5)
	lis %r6, 257
	ori %r6, %r6, 257
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 257
	ori %r6, %r6, 257
	std %r6, 424(%r5)
	lis %r6, 3855
	ori %r6, %r6, 3855
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 3855
	ori %r6, %r6, 3855
	std %r6, 432(%r5)
	lis %r6, 0
	ori %r6, %r6, 0
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 65535
	ori %r6, %r6, 65535
	std %r6, 440(%r5)
	lis %r6, 1026
	ori %r6, %r6, 2048
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 0
	ori %r6, %r6, 0
	std %r6, 448(%r5)
	lis %r6, 4
	ori %r6, %r6, 1
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 2048
	ori %r6, %r6, 0
	std %r6, 456(%r5)
	lis %r6, 0
	ori %r6, %r6, 512
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 4
	ori %r6, %r6, 0
	std %r6, 464(%r5)
	lis %r6, 0
	ori %r6, %r6, 0
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 1024
	ori %r6, %r6, 256
	std %r6, 472(%r5)
	lis %r6, 0
	ori %r6, %r6, 4
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 1
	ori %r6, %r6, 0
	std %r6, 480(%r5)
	lis %r6, 0
	ori %r6, %r6, 0
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 8
	ori %r6, %r6, 2052
	std %r6, 488(%r5)
	li %r6, 0
	ldbrx %r7, %r4, %r6
	li %r8, 0
	li %r10, 1
	rldicl %r9, %r7, 58, 6
	and %r9, %r9, %r10
	rldicl %r9, %r9, 63, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 50, 14
	and %r9, %r9, %r10
	rldicl %r9, %r9, 62, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 42, 22
	and %r9, %r9, %r10
	rldicl %r9, %r9, 61, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 34, 30
	and %r9, %r9, %r10
	rldicl %r9, %r9, 60, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 26, 38
	and %r9, %r9, %r10
	rldicl %r9, %r9, 59, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 18, 46
	and %r9, %r9, %r10
	rldicl %r9, %r9, 58, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 10, 54
	and %r9, %r9, %r10
	rldicl %r9, %r9, 57, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 2, 62
	and %r9, %r9, %r10
	rldicl %r9, %r9, 56, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 60, 4
	and %r9, %r9, %r10
	rldicl %r9, %r9, 55, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 52, 12
	and %r9, %r9, %r10
	rldicl %r9, %r9, 54, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 44, 20
	and %r9, %r9, %r10
	rldicl %r9, %r9, 53, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 36, 28
	and %r9, %r9, %r10
	rldicl %r9, %r9, 52, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 28, 36
	and %r9, %r9, %r10
	rldicl %r9, %r9, 51, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 20, 44
	and %r9, %r9, %r10
	rldicl %r9, %r9, 50, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 12, 52
	and %r9, %r9, %r10
	rldicl %r9, %r9, 49, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 4, 60
	and %r9, %r9, %r10
	rldicl %r9, %r9, 48, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 62, 2
	and %r9, %r9, %r10
	rldicl %r9, %r9, 47, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 54, 10
	and %r9, %r9, %r10
	rldicl %r9, %r9, 46, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 46, 18
	and %r9, %r9, %r10
	rldicl %r9, %r9, 45, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 38, 26
	and %r9, %r9, %r10
	rldicl %r9, %r9, 44, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 30, 34
	and %r9, %r9, %r10
	rldicl %r9, %r9, 43, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 22, 42
	and %r9, %r9, %r10
	rldicl %r9, %r9, 42, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 14, 50
	and %r9, %r9, %r10
	rldicl %r9, %r9, 41, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 6, 58
	and %r9, %r9, %r10
	rldicl %r9, %r9, 40, 0
	xor %r8, %r8, %r9
	or %r9, %r7, %r7
	and %r9, %r9, %r10
	rldicl %r9, %r9, 39, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 56, 8
	and %r9, %r9, %r10
	rldicl %r9, %r9, 38, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 48, 16
	and %r9, %r9, %r10
	rldicl %r9, %r9, 37, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 40, 24
	and %r9, %r9, %r10
	rldicl %r9, %r9, 36, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 32, 32
	and %r9, %r9, %r10
	rldicl %r9, %r9, 35, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 24, 40
	and %r9, %r9, %r10
	rldicl %r9, %r9, 34, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 16, 48
	and %r9, %r9, %r10
	rldicl %r9, %r9, 33, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 8, 56
	and %r9, %r9, %r10
	rldicl %r9, %r9, 32, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 57, 7
	and %r9, %r9, %r10
	rldicl %r9, %r9, 31, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 49, 15
	and %r9, %r9, %r10
	rldicl %r9, %r9, 30, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 41, 23
	and %r9, %r9, %r10
	rldicl %r9, %r9, 29, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 33, 31
	and %r9, %r9, %r10
	rldicl %r9, %r9, 28, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 25, 39
	and %r9, %r9, %r10
	rldicl %r9, %r9, 27, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 17, 47
	and %r9, %r9, %r10
	rldicl %r9, %r9, 26, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 9, 55
	and %r9, %r9, %r10
	rldicl %r9, %r9, 25, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 1, 63
	and %r9, %r9, %r10
	rldicl %r9, %r9, 24, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 59, 5
	and %r9, %r9, %r10
	rldicl %r9, %r9, 23, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 51, 13
	and %r9, %r9, %r10
	rldicl %r9, %r9, 22, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 43, 21
	and %r9, %r9, %r10
	rldicl %r9, %r9, 21, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 35, 29
	and %r9, %r9, %r10
	rldicl %r9, %r9, 20, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 27, 37
	and %r9, %r9, %r10
	rldicl %r9, %r9, 19, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 19, 45
	and %r9, %r9, %r10
	rldicl %r9, %r9, 18, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 11, 53
	and %r9, %r9, %r10
	rldicl %r9, %r9, 17, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 3, 61
	and %r9, %r9, %r10
	rldicl %r9, %r9, 16, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 61, 3
	and %r9, %r9, %r10
	rldicl %r9, %r9, 15, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 53, 11
	and %r9, %r9, %r10
	rldicl %r9, %r9, 14, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 45, 19
	and %r9, %r9, %r10
	rldicl %r9, %r9, 13, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 37, 27
	and %r9, %r9, %r10
	rldicl %r9, %r9, 12, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 29, 35
	and %r9, %r9, %r10
	rldicl %r9, %r9, 11, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 21, 43
	and %r9, %r9, %r10
	rldicl %r9, %r9, 10, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 13, 51
	and %r9, %r9, %r10
	rldicl %r9, %r9, 9, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 5, 59
	and %r9, %r9, %r10
	rldicl %r9, %r9, 8, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 63, 1
	and %r9, %r9, %r10
	rldicl %r9, %r9, 7, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 55, 9
	and %r9, %r9, %r10
	rldicl %r9, %r9, 6, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 47, 17
	and %r9, %r9, %r10
	rldicl %r9, %r9, 5, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 39, 25
	and %r9, %r9, %r10
	rldicl %r9, %r9, 4, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 31, 33
	and %r9, %r9, %r10
	rldicl %r9, %r9, 3, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 23, 41
	and %r9, %r9, %r10
	rldicl %r9, %r9, 2, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 15, 49
	and %r9, %r9, %r10
	rldicl %r9, %r9, 1, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 7, 57
	and %r9, %r9, %r10
	xor %r8, %r8, %r9
	rldicl %r14, %r8, 32, 32
	rlwinm %r15, %r8, 0, 0, 31
	li %r19, 3
20:
	addi %r20, %r19, -3
	cmpldi %cr0, %r20, 0
	beq %cr0, 21f
	addi %r20, %r19, -2
	cmpldi %cr0, %r20, 0
	beq %cr0, 23f
	addi %r17, %r3, 256
	li %r16, 16
	li %r18, 0
	addi %r18, %r18, 8
	b 24f
23:
	addi %r17, %r3, 248
	li %r16, 16
	li %r18, 0
	addi %r18, %r18, -8
24:
	b 22f
21:
	addi %r17, %r3, 0
	li %r16, 16
	li %r18, 0
	addi %r18, %r18, 8
22:
25:
	ld %r10, 0(%r17)
	ld %r6, 440(%r5)
	and %r6, %r15, %r6
	rldicl %r7, %r6, 1, 0
	rldicl %r8, %r6, 33, 0
	xor %r6, %r7, %r8
	ld %r7, 376(%r5)
	rldicl %r8, %r6, 48, 16
	and %r8, %r8, %r7
	and %r7, %r6, %r7
	rldicl %r8, %r8, 32, 0
	xor %r6, %r7, %r8
	ld %r7, 384(%r5)
	rldicl %r8, %r6, 56, 8
	and %r8, %r8, %r7
	and %r7, %r6, %r7
	rldicl %r8, %r8, 16, 0
	xor %r6, %r7, %r8
	ld %r7, 392(%r5)
	rldicl %r8, %r6, 60, 4
	and %r8, %r8, %r7
	and %r7, %r6, %r7
	rldicl %r8, %r8, 8, 0
	xor %r6, %r7, %r8
	ld %r7, 400(%r5)
	rldicl %r8, %r10, 40, 24
	and %r8, %r8, %r7
	and %r7, %r10, %r7
	rldicl %r8, %r8, 32, 0
	xor %r10, %r7, %r8
	ld %r7, 408(%r5)
	rldicl %r8, %r10, 52, 12
	and %r8, %r8, %r7
	and %r7, %r10, %r7
	rldicl %r8, %r8, 16, 0
	xor %r10, %r7, %r8
	ld %r7, 416(%r5)
	rldicl %r8, %r10, 58, 6
	and %r8, %r8, %r7
	and %r7, %r10, %r7
	rldicl %r8, %r8, 8, 0
	xor %r10, %r7, %r8
	xor %r6, %r6, %r10
	ld %r9, 424(%r5)
	and %r20, %r6, %r9
	rldicl %r7, %r20, 1, 0
	xor %r20, %r20, %r7
	rldicl %r7, %r20, 2, 0
	xor %r20, %r20, %r7
	rldicl %r7, %r20, 4, 0
	xor %r20, %r20, %r7
	rldicl %r21, %r6, 63, 1
	and %r21, %r21, %r9
	rldicl %r7, %r21, 1, 0
	xor %r21, %r21, %r7
	rldicl %r7, %r21, 2, 0
	xor %r21, %r21, %r7
	rldicl %r7, %r21, 4, 0
	xor %r21, %r21, %r7
	rldicl %r22, %r6, 62, 2
	and %r22, %r22, %r9
	rldicl %r7, %r22, 1, 0
	xor %r22, %r22, %r7
	rldicl %r7, %r22, 2, 0
	xor %r22, %r22, %r7
	rldicl %r7, %r22, 4, 0
	xor %r22, %r22, %r7
	rldicl %r23, %r6, 61, 3
	and %r23, %r23, %r9
	rldicl %r7, %r23, 1, 0
	xor %r23, %r23, %r7
	rldicl %r7, %r23, 2, 0
	xor %r23, %r23, %r7
	rldicl %r7, %r23, 4, 0
	xor %r23, %r23, %r7
	rldicl %r24, %r6, 60, 4
	and %r24, %r24, %r9
	rldicl %r7, %r24, 1, 0
	xor %r24, %r24, %r7
	rldicl %r7, %r24, 2, 0
	xor %r24, %r24, %r7
	rldicl %r7, %r24, 4, 0
	xor %r24, %r24, %r7
	rldicl %r25, %r6, 59, 5
	and %r25, %r25, %r9
	rldicl %r7, %r25, 1, 0
	xor %r25, %r25, %r7
	rldicl %r7, %r25, 2, 0
	xor %r25, %r25, %r7
	rldicl %r7, %r25, 4, 0
	xor %r25, %r25, %r7
	ld %r6, 120(%r5)
	ld %r7, 128(%r5)
	and %r7, %r7, %r20
	xor %r6, %r6, %r7
	ld %r7, 136(%r5)
	ld %r8, 144(%r5)
	and %r8, %r8, %r20
	xor %r7, %r7, %r8
	xor %r7, %r6, %r7
	and %r7, %r7, %r21
	xor %r6, %r6, %r7
	ld %r7, 152(%r5)
	ld %r8, 160(%r5)
	and %r8, %r8, %r20
	xor %r7, %r7, %r8
	ld %r8, 168(%r5)
	ld %r9, 176(%r5)
	and %r9, %r9, %r20
	xor %r8, %r8, %r9
	xor %r8, %r7, %r8
	and %r8, %r8, %r21
	xor %r7, %r7, %r8
	xor %r7, %r6, %r7
	and %r7, %r7, %r22
	xor %r6, %r6, %r7
	ld %r7, 184(%r5)
	ld %r8, 192(%r5)
	and %r8, %r8, %r20
	xor %r7, %r7, %r8
	ld %r8, 200(%r5)
	ld %r9, 208(%r5)
	and %r9, %r9, %r20
	xor %r8, %r8, %r9
	xor %r8, %r7, %r8
	and %r8, %r8, %r21
	xor %r7, %r7, %r8
	ld %r8, 216(%r5)
	ld %r9, 224(%r5)
	and %r9, %r9, %r20
	xor %r8, %r8, %r9
	ld %r9, 232(%r5)
	ld %r10, 240(%r5)
	and %r10, %r10, %r20
	xor %r9, %r9, %r10
	xor %r9, %r8, %r9
	and %r9, %r9, %r21
	xor %r8, %r8, %r9
	xor %r8, %r7, %r8
	and %r8, %r8, %r22
	xor %r7, %r7, %r8
	xor %r7, %r6, %r7
	and %r7, %r7, %r23
	xor %r6, %r6, %r7
	ld %r7, 248(%r5)
	ld %r8, 256(%r5)
	and %r8, %r8, %r20
	xor %r7, %r7, %r8
	ld %r8, 264(%r5)
	ld %r9, 272(%r5)
	and %r9, %r9, %r20
	xor %r8, %r8, %r9
	xor %r8, %r7, %r8
	and %r8, %r8, %r21
	xor %r7, %r7, %r8
	ld %r8, 280(%r5)
	ld %r9, 288(%r5)
	and %r9, %r9, %r20
	xor %r8, %r8, %r9
	ld %r9, 296(%r5)
	ld %r10, 304(%r5)
	and %r10, %r10, %r20
	xor %r9, %r9, %r10
	xor %r9, %r8, %r9
	and %r9, %r9, %r21
	xor %r8, %r8, %r9
	xor %r8, %r7, %r8
	and %r8, %r8, %r22
	xor %r7, %r7, %r8
	ld %r8, 312(%r5)
	ld %r9, 320(%r5)
	and %r9, %r9, %r20
	xor %r8, %r8, %r9
	ld %r9, 328(%r5)
	ld %r10, 336(%r5)
	and %r10, %r10, %r20
	xor %r9, %r9, %r10
	xor %r9, %r8, %r9
	and %r9, %r9, %r21
	xor %r8, %r8, %r9
	ld %r9, 344(%r5)
	ld %r10, 352(%r5)
	and %r10, %r10, %r20
	xor %r9, %r9, %r10
	ld %r10, 360(%r5)
	ld %r11, 368(%r5)
	and %r11, %r11, %r20
	xor %r10, %r10, %r11
	xor %r10, %r9, %r10
	and %r10, %r10, %r21
	xor %r9, %r9, %r10
	xor %r9, %r8, %r9
	and %r9, %r9, %r22
	xor %r8, %r8, %r9
	xor %r8, %r7, %r8
	and %r8, %r8, %r23
	xor %r7, %r7, %r8
	xor %r7, %r6, %r7
	and %r7, %r7, %r24
	xor %r6, %r6, %r7
	ld %r12, 432(%r5)
	xor %r12, %r25, %r12
	and %r6, %r6, %r12
	rldicl %r7, %r6, 60, 4
	xor %r6, %r6, %r7
	rldicl %r7, %r6, 6, 0
	rldicl %r7, %r7, 1, 63
	rldicl %r7, %r7, 1, 0
	xor %r14, %r14, %r7
	rldicl %r7, %r6, 13, 51
	li %r8, 33
	and %r7, %r7, %r8
	rldicl %r7, %r7, 4, 0
	xor %r14, %r14, %r7
	rldicl %r7, %r6, 4, 0
	rldicl %r7, %r7, 1, 63
	rldicl %r7, %r7, 15, 0
	xor %r14, %r14, %r7
	rldicl %r7, %r6, 23, 0
	rldicl %r7, %r7, 1, 63
	rldicl %r7, %r7, 2, 0
	xor %r14, %r14, %r7
	ld %r7, 448(%r5)
	and %r7, %r7, %r6
	rldicl %r7, %r7, 29, 35
	xor %r14, %r14, %r7
	rldicl %r7, %r6, 29, 35
	li %r8, 8193
	and %r7, %r7, %r8
	rldicl %r7, %r7, 6, 0
	xor %r14, %r14, %r7
	rldicl %r7, %r6, 21, 0
	rldicl %r7, %r7, 1, 63
	rldicl %r7, %r7, 16, 0
	xor %r14, %r14, %r7
	ld %r7, 456(%r5)
	and %r7, %r7, %r6
	rldicl %r7, %r7, 44, 20
	xor %r14, %r14, %r7
	ld %r7, 464(%r5)
	and %r7, %r7, %r6
	rldicl %r7, %r7, 49, 15
	xor %r14, %r14, %r7
	rldicl %r7, %r6, 30, 0
	rldicl %r7, %r7, 1, 63
	rldicl %r7, %r7, 22, 0
	xor %r14, %r14, %r7
	ld %r7, 472(%r5)
	and %r7, %r7, %r6
	rldicl %r7, %r7, 56, 8
	xor %r14, %r14, %r7
	ld %r7, 480(%r5)
	and %r7, %r7, %r6
	rldicl %r7, %r7, 61, 3
	xor %r14, %r14, %r7
	rldicl %r7, %r6, 54, 10
	li %r8, 16385
	and %r7, %r7, %r8
	rldicl %r7, %r7, 10, 0
	xor %r14, %r14, %r7
	rldicl %r7, %r6, 47, 17
	li %r8, 257
	and %r7, %r7, %r8
	rldicl %r7, %r7, 21, 0
	xor %r14, %r14, %r7
	rldicl %r7, %r6, 63, 0
	rldicl %r7, %r7, 1, 63
	rldicl %r7, %r7, 5, 0
	xor %r14, %r14, %r7
	ld %r7, 488(%r5)
	and %r7, %r7, %r6
	rldicl %r7, %r7, 9, 0
	xor %r14, %r14, %r7
	rldicl %r7, %r6, 63, 1
	li %r8, 257
	and %r7, %r7, %r8
	rldicl %r7, %r7, 17, 0
	xor %r14, %r14, %r7
	rldicl %r7, %r6, 60, 0
	rldicl %r7, %r7, 1, 63
	rldicl %r7, %r7, 27, 0
	xor %r14, %r14, %r7
	or %r6, %r14, %r14
	or %r14, %r15, %r15
	or %r15, %r6, %r6
	add %r17, %r17, %r18
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 25b
	or %r6, %r14, %r14
	or %r14, %r15, %r15
	or %r15, %r6, %r6
	addi %r19, %r19, -1
	cmpldi %cr0, %r19, 0
	bne %cr0, 20b
	rldicl %r6, %r14, 32, 0
	xor %r6, %r6, %r15
	li %r8, 0
	li %r10, 1
	rldicl %r9, %r6, 40, 24
	and %r9, %r9, %r10
	rldicl %r9, %r9, 63, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 8, 56
	and %r9, %r9, %r10
	rldicl %r9, %r9, 62, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 48, 16
	and %r9, %r9, %r10
	rldicl %r9, %r9, 61, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 16, 48
	and %r9, %r9, %r10
	rldicl %r9, %r9, 60, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 56, 8
	and %r9, %r9, %r10
	rldicl %r9, %r9, 59, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 24, 40
	and %r9, %r9, %r10
	rldicl %r9, %r9, 58, 0
	xor %r8, %r8, %r9
	or %r9, %r6, %r6
	and %r9, %r9, %r10
	rldicl %r9, %r9, 57, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 32, 32
	and %r9, %r9, %r10
	rldicl %r9, %r9, 56, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 39, 25
	and %r9, %r9, %r10
	rldicl %r9, %r9, 55, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 7, 57
	and %r9, %r9, %r10
	rldicl %r9, %r9, 54, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 47, 17
	and %r9, %r9, %r10
	rldicl %r9, %r9, 53, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 15, 49
	and %r9, %r9, %r10
	rldicl %r9, %r9, 52, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 55, 9
	and %r9, %r9, %r10
	rldicl %r9, %r9, 51, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 23, 41
	and %r9, %r9, %r10
	rldicl %r9, %r9, 50, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 63, 1
	and %r9, %r9, %r10
	rldicl %r9, %r9, 49, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 31, 33
	and %r9, %r9, %r10
	rldicl %r9, %r9, 48, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 38, 26
	and %r9, %r9, %r10
	rldicl %r9, %r9, 47, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 6, 58
	and %r9, %r9, %r10
	rldicl %r9, %r9, 46, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 46, 18
	and %r9, %r9, %r10
	rldicl %r9, %r9, 45, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 14, 50
	and %r9, %r9, %r10
	rldicl %r9, %r9, 44, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 54, 10
	and %r9, %r9, %r10
	rldicl %r9, %r9, 43, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 22, 42
	and %r9, %r9, %r10
	rldicl %r9, %r9, 42, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 62, 2
	and %r9, %r9, %r10
	rldicl %r9, %r9, 41, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 30, 34
	and %r9, %r9, %r10
	rldicl %r9, %r9, 40, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 37, 27
	and %r9, %r9, %r10
	rldicl %r9, %r9, 39, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 5, 59
	and %r9, %r9, %r10
	rldicl %r9, %r9, 38, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 45, 19
	and %r9, %r9, %r10
	rldicl %r9, %r9, 37, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 13, 51
	and %r9, %r9, %r10
	rldicl %r9, %r9, 36, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 53, 11
	and %r9, %r9, %r10
	rldicl %r9, %r9, 35, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 21, 43
	and %r9, %r9, %r10
	rldicl %r9, %r9, 34, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 61, 3
	and %r9, %r9, %r10
	rldicl %r9, %r9, 33, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 29, 35
	and %r9, %r9, %r10
	rldicl %r9, %r9, 32, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 36, 28
	and %r9, %r9, %r10
	rldicl %r9, %r9, 31, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 4, 60
	and %r9, %r9, %r10
	rldicl %r9, %r9, 30, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 44, 20
	and %r9, %r9, %r10
	rldicl %r9, %r9, 29, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 12, 52
	and %r9, %r9, %r10
	rldicl %r9, %r9, 28, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 52, 12
	and %r9, %r9, %r10
	rldicl %r9, %r9, 27, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 20, 44
	and %r9, %r9, %r10
	rldicl %r9, %r9, 26, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 60, 4
	and %r9, %r9, %r10
	rldicl %r9, %r9, 25, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 28, 36
	and %r9, %r9, %r10
	rldicl %r9, %r9, 24, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 35, 29
	and %r9, %r9, %r10
	rldicl %r9, %r9, 23, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 3, 61
	and %r9, %r9, %r10
	rldicl %r9, %r9, 22, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 43, 21
	and %r9, %r9, %r10
	rldicl %r9, %r9, 21, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 11, 53
	and %r9, %r9, %r10
	rldicl %r9, %r9, 20, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 51, 13
	and %r9, %r9, %r10
	rldicl %r9, %r9, 19, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 19, 45
	and %r9, %r9, %r10
	rldicl %r9, %r9, 18, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 59, 5
	and %r9, %r9, %r10
	rldicl %r9, %r9, 17, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 27, 37
	and %r9, %r9, %r10
	rldicl %r9, %r9, 16, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 34, 30
	and %r9, %r9, %r10
	rldicl %r9, %r9, 15, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 2, 62
	and %r9, %r9, %r10
	rldicl %r9, %r9, 14, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 42, 22
	and %r9, %r9, %r10
	rldicl %r9, %r9, 13, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 10, 54
	and %r9, %r9, %r10
	rldicl %r9, %r9, 12, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 50, 14
	and %r9, %r9, %r10
	rldicl %r9, %r9, 11, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 18, 46
	and %r9, %r9, %r10
	rldicl %r9, %r9, 10, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 58, 6
	and %r9, %r9, %r10
	rldicl %r9, %r9, 9, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 26, 38
	and %r9, %r9, %r10
	rldicl %r9, %r9, 8, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 33, 31
	and %r9, %r9, %r10
	rldicl %r9, %r9, 7, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 1, 63
	and %r9, %r9, %r10
	rldicl %r9, %r9, 6, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 41, 23
	and %r9, %r9, %r10
	rldicl %r9, %r9, 5, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 9, 55
	and %r9, %r9, %r10
	rldicl %r9, %r9, 4, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 49, 15
	and %r9, %r9, %r10
	rldicl %r9, %r9, 3, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 17, 47
	and %r9, %r9, %r10
	rldicl %r9, %r9, 2, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 57, 7
	and %r9, %r9, %r10
	rldicl %r9, %r9, 1, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 25, 39
	and %r9, %r9, %r10
	xor %r8, %r8, %r9
	li %r7, 0
	stdbrx %r8, %r4, %r7
	ld %r14, 0(%r5)
	ld %r15, 8(%r5)
	ld %r16, 16(%r5)
	ld %r17, 24(%r5)
	ld %r18, 32(%r5)
	ld %r19, 40(%r5)
	ld %r20, 48(%r5)
	ld %r21, 56(%r5)
	ld %r22, 64(%r5)
	ld %r23, 72(%r5)
	ld %r24, 80(%r5)
	ld %r25, 88(%r5)
	ld %r26, 96(%r5)
	ld %r27, 104(%r5)
	ld %r28, 112(%r5)
	blr
