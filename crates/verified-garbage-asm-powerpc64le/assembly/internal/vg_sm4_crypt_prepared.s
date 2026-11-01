// The functions of `src/internal/vg_sm4_crypt_prepared.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_crypt_prepared:
	or %r8, %r3, %r3
	std %r14, 3072(%r8)
	std %r15, 3080(%r8)
	std %r16, 3088(%r8)
	std %r17, 3096(%r8)
	std %r18, 3104(%r8)
	std %r19, 3112(%r8)
	std %r20, 3120(%r8)
	std %r21, 3128(%r8)
	std %r22, 3136(%r8)
	std %r23, 3144(%r8)
	std %r24, 3152(%r8)
	std %r25, 3160(%r8)
	std %r26, 3168(%r8)
	std %r27, 3176(%r8)
	std %r28, 3184(%r8)
	std %r29, 3192(%r8)
	std %r30, 3200(%r8)
	std %r31, 3208(%r8)
	addi %r11, %r8, 3072
	lis %r24, 0
	ori %r24, %r24, 0
	rldicr %r24, %r24, 32, 31
	oris %r24, %r24, 65535
	ori %r24, %r24, 0
	lis %r25, 0
	ori %r25, %r25, 65280
	rldicr %r25, %r25, 32, 31
	oris %r25, %r25, 0
	ori %r25, %r25, 65280
	lis %r26, 255
	ori %r26, %r26, 255
	rldicr %r26, %r26, 32, 31
	oris %r26, %r26, 255
	ori %r26, %r26, 255
	lis %r27, 21845
	ori %r27, %r27, 21845
	rldicr %r27, %r27, 32, 31
	oris %r27, %r27, 21845
	ori %r27, %r27, 21845
	lis %r28, 13107
	ori %r28, %r28, 13107
	rldicr %r28, %r28, 32, 31
	oris %r28, %r28, 13107
	ori %r28, %r28, 13107
	lis %r29, 3855
	ori %r29, %r29, 3855
	rldicr %r29, %r29, 32, 31
	oris %r29, %r29, 3855
	ori %r29, %r29, 3855
	ld %r14, 768(%r8)
	ld %r18, 896(%r8)
	ld %r15, 784(%r8)
	ld %r19, 912(%r8)
	ld %r16, 800(%r8)
	ld %r20, 928(%r8)
	ld %r17, 816(%r8)
	ld %r21, 944(%r8)
	rldicl %r22, %r14, 48, 16
	xor %r22, %r22, %r14
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 16, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 48, 16
	xor %r22, %r22, %r15
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 16, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 48, 16
	xor %r22, %r22, %r16
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 16, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 48, 16
	xor %r22, %r22, %r17
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 16, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 48, 16
	xor %r22, %r22, %r18
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 16, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 48, 16
	xor %r22, %r22, %r19
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 16, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 48, 16
	xor %r22, %r22, %r20
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 16, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 48, 16
	xor %r22, %r22, %r21
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 16, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r14
	and %r22, %r22, %r25
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r15
	and %r22, %r22, %r25
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r16
	and %r22, %r22, %r25
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r17
	and %r22, %r22, %r25
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r25
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r25
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r25
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r25
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r26
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r26
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r26
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r26
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	std %r14, 768(%r8)
	std %r18, 896(%r8)
	std %r15, 784(%r8)
	std %r19, 912(%r8)
	std %r16, 800(%r8)
	std %r20, 928(%r8)
	std %r17, 816(%r8)
	std %r21, 944(%r8)
	ld %r14, 832(%r8)
	ld %r18, 960(%r8)
	ld %r15, 848(%r8)
	ld %r19, 976(%r8)
	ld %r16, 864(%r8)
	ld %r20, 992(%r8)
	ld %r17, 880(%r8)
	ld %r21, 1008(%r8)
	rldicl %r22, %r14, 48, 16
	xor %r22, %r22, %r14
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 16, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 48, 16
	xor %r22, %r22, %r15
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 16, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 48, 16
	xor %r22, %r22, %r16
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 16, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 48, 16
	xor %r22, %r22, %r17
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 16, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 48, 16
	xor %r22, %r22, %r18
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 16, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 48, 16
	xor %r22, %r22, %r19
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 16, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 48, 16
	xor %r22, %r22, %r20
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 16, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 48, 16
	xor %r22, %r22, %r21
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 16, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r14
	and %r22, %r22, %r25
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r15
	and %r22, %r22, %r25
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r16
	and %r22, %r22, %r25
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r17
	and %r22, %r22, %r25
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r25
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r25
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r25
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r25
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r26
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r26
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r26
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r26
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	std %r14, 832(%r8)
	std %r18, 960(%r8)
	std %r15, 848(%r8)
	std %r19, 976(%r8)
	std %r16, 864(%r8)
	std %r20, 992(%r8)
	std %r17, 880(%r8)
	std %r21, 1008(%r8)
	ld %r14, 776(%r8)
	ld %r18, 904(%r8)
	ld %r15, 792(%r8)
	ld %r19, 920(%r8)
	ld %r16, 808(%r8)
	ld %r20, 936(%r8)
	ld %r17, 824(%r8)
	ld %r21, 952(%r8)
	rldicl %r22, %r14, 48, 16
	xor %r22, %r22, %r14
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 16, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 48, 16
	xor %r22, %r22, %r15
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 16, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 48, 16
	xor %r22, %r22, %r16
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 16, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 48, 16
	xor %r22, %r22, %r17
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 16, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 48, 16
	xor %r22, %r22, %r18
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 16, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 48, 16
	xor %r22, %r22, %r19
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 16, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 48, 16
	xor %r22, %r22, %r20
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 16, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 48, 16
	xor %r22, %r22, %r21
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 16, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r14
	and %r22, %r22, %r25
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r15
	and %r22, %r22, %r25
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r16
	and %r22, %r22, %r25
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r17
	and %r22, %r22, %r25
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r25
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r25
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r25
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r25
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r26
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r26
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r26
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r26
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	std %r14, 776(%r8)
	std %r18, 904(%r8)
	std %r15, 792(%r8)
	std %r19, 920(%r8)
	std %r16, 808(%r8)
	std %r20, 936(%r8)
	std %r17, 824(%r8)
	std %r21, 952(%r8)
	ld %r14, 840(%r8)
	ld %r18, 968(%r8)
	ld %r15, 856(%r8)
	ld %r19, 984(%r8)
	ld %r16, 872(%r8)
	ld %r20, 1000(%r8)
	ld %r17, 888(%r8)
	ld %r21, 1016(%r8)
	rldicl %r22, %r14, 48, 16
	xor %r22, %r22, %r14
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 16, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 48, 16
	xor %r22, %r22, %r15
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 16, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 48, 16
	xor %r22, %r22, %r16
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 16, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 48, 16
	xor %r22, %r22, %r17
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 16, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 48, 16
	xor %r22, %r22, %r18
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 16, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 48, 16
	xor %r22, %r22, %r19
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 16, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 48, 16
	xor %r22, %r22, %r20
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 16, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 48, 16
	xor %r22, %r22, %r21
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 16, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r14
	and %r22, %r22, %r25
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r15
	and %r22, %r22, %r25
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r16
	and %r22, %r22, %r25
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r17
	and %r22, %r22, %r25
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r25
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r25
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r25
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r25
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r26
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r26
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r26
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r26
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	std %r14, 840(%r8)
	std %r18, 968(%r8)
	std %r15, 856(%r8)
	std %r19, 984(%r8)
	std %r16, 872(%r8)
	std %r20, 1000(%r8)
	std %r17, 888(%r8)
	std %r21, 1016(%r8)
	ld %r14, 768(%r8)
	ld %r15, 784(%r8)
	ld %r16, 800(%r8)
	ld %r17, 816(%r8)
	ld %r18, 832(%r8)
	ld %r19, 848(%r8)
	ld %r20, 864(%r8)
	ld %r21, 880(%r8)
	rldicl %r22, %r14, 63, 1
	xor %r22, %r22, %r15
	and %r22, %r22, %r27
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r16, 63, 1
	xor %r22, %r22, %r17
	and %r22, %r22, %r27
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r18, 63, 1
	xor %r22, %r22, %r19
	and %r22, %r22, %r27
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r20, 63, 1
	xor %r22, %r22, %r21
	and %r22, %r22, %r27
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r14, 62, 2
	xor %r22, %r22, %r16
	and %r22, %r22, %r28
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 62, 2
	xor %r22, %r22, %r17
	and %r22, %r22, %r28
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r18, 62, 2
	xor %r22, %r22, %r20
	and %r22, %r22, %r28
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 62, 2
	xor %r22, %r22, %r21
	and %r22, %r22, %r28
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r14, 60, 4
	xor %r22, %r22, %r18
	and %r22, %r22, %r29
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 60, 4
	xor %r22, %r22, %r19
	and %r22, %r22, %r29
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 60, 4
	xor %r22, %r22, %r20
	and %r22, %r22, %r29
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 60, 4
	xor %r22, %r22, %r21
	and %r22, %r22, %r29
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 4, 0
	xor %r17, %r17, %r22
	std %r14, 512(%r8)
	std %r15, 520(%r8)
	std %r16, 528(%r8)
	std %r17, 536(%r8)
	std %r18, 544(%r8)
	std %r19, 552(%r8)
	std %r20, 560(%r8)
	std %r21, 568(%r8)
	ld %r14, 896(%r8)
	ld %r15, 912(%r8)
	ld %r16, 928(%r8)
	ld %r17, 944(%r8)
	ld %r18, 960(%r8)
	ld %r19, 976(%r8)
	ld %r20, 992(%r8)
	ld %r21, 1008(%r8)
	rldicl %r22, %r14, 63, 1
	xor %r22, %r22, %r15
	and %r22, %r22, %r27
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r16, 63, 1
	xor %r22, %r22, %r17
	and %r22, %r22, %r27
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r18, 63, 1
	xor %r22, %r22, %r19
	and %r22, %r22, %r27
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r20, 63, 1
	xor %r22, %r22, %r21
	and %r22, %r22, %r27
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r14, 62, 2
	xor %r22, %r22, %r16
	and %r22, %r22, %r28
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 62, 2
	xor %r22, %r22, %r17
	and %r22, %r22, %r28
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r18, 62, 2
	xor %r22, %r22, %r20
	and %r22, %r22, %r28
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 62, 2
	xor %r22, %r22, %r21
	and %r22, %r22, %r28
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r14, 60, 4
	xor %r22, %r22, %r18
	and %r22, %r22, %r29
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 60, 4
	xor %r22, %r22, %r19
	and %r22, %r22, %r29
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 60, 4
	xor %r22, %r22, %r20
	and %r22, %r22, %r29
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 60, 4
	xor %r22, %r22, %r21
	and %r22, %r22, %r29
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 4, 0
	xor %r17, %r17, %r22
	std %r14, 576(%r8)
	std %r15, 584(%r8)
	std %r16, 592(%r8)
	std %r17, 600(%r8)
	std %r18, 608(%r8)
	std %r19, 616(%r8)
	std %r20, 624(%r8)
	std %r21, 632(%r8)
	ld %r14, 776(%r8)
	ld %r15, 792(%r8)
	ld %r16, 808(%r8)
	ld %r17, 824(%r8)
	ld %r18, 840(%r8)
	ld %r19, 856(%r8)
	ld %r20, 872(%r8)
	ld %r21, 888(%r8)
	rldicl %r22, %r14, 63, 1
	xor %r22, %r22, %r15
	and %r22, %r22, %r27
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r16, 63, 1
	xor %r22, %r22, %r17
	and %r22, %r22, %r27
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r18, 63, 1
	xor %r22, %r22, %r19
	and %r22, %r22, %r27
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r20, 63, 1
	xor %r22, %r22, %r21
	and %r22, %r22, %r27
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r14, 62, 2
	xor %r22, %r22, %r16
	and %r22, %r22, %r28
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 62, 2
	xor %r22, %r22, %r17
	and %r22, %r22, %r28
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r18, 62, 2
	xor %r22, %r22, %r20
	and %r22, %r22, %r28
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 62, 2
	xor %r22, %r22, %r21
	and %r22, %r22, %r28
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r14, 60, 4
	xor %r22, %r22, %r18
	and %r22, %r22, %r29
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 60, 4
	xor %r22, %r22, %r19
	and %r22, %r22, %r29
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 60, 4
	xor %r22, %r22, %r20
	and %r22, %r22, %r29
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 60, 4
	xor %r22, %r22, %r21
	and %r22, %r22, %r29
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 4, 0
	xor %r17, %r17, %r22
	std %r14, 640(%r8)
	std %r15, 648(%r8)
	std %r16, 656(%r8)
	std %r17, 664(%r8)
	std %r18, 672(%r8)
	std %r19, 680(%r8)
	std %r20, 688(%r8)
	std %r21, 696(%r8)
	ld %r14, 904(%r8)
	ld %r15, 920(%r8)
	ld %r16, 936(%r8)
	ld %r17, 952(%r8)
	ld %r18, 968(%r8)
	ld %r19, 984(%r8)
	ld %r20, 1000(%r8)
	ld %r21, 1016(%r8)
	rldicl %r22, %r14, 63, 1
	xor %r22, %r22, %r15
	and %r22, %r22, %r27
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r16, 63, 1
	xor %r22, %r22, %r17
	and %r22, %r22, %r27
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r18, 63, 1
	xor %r22, %r22, %r19
	and %r22, %r22, %r27
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r20, 63, 1
	xor %r22, %r22, %r21
	and %r22, %r22, %r27
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r14, 62, 2
	xor %r22, %r22, %r16
	and %r22, %r22, %r28
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 62, 2
	xor %r22, %r22, %r17
	and %r22, %r22, %r28
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r18, 62, 2
	xor %r22, %r22, %r20
	and %r22, %r22, %r28
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 62, 2
	xor %r22, %r22, %r21
	and %r22, %r22, %r28
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r14, 60, 4
	xor %r22, %r22, %r18
	and %r22, %r22, %r29
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 60, 4
	xor %r22, %r22, %r19
	and %r22, %r22, %r29
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 60, 4
	xor %r22, %r22, %r20
	and %r22, %r22, %r29
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 60, 4
	xor %r22, %r22, %r21
	and %r22, %r22, %r29
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 4, 0
	xor %r17, %r17, %r22
	std %r14, 704(%r8)
	std %r15, 712(%r8)
	std %r16, 720(%r8)
	std %r17, 728(%r8)
	std %r18, 736(%r8)
	std %r19, 744(%r8)
	std %r20, 752(%r8)
	std %r21, 760(%r8)
	addi %r10, %r8, 1024
20:
	ld %r14, 576(%r8)
	ld %r22, 640(%r8)
	xor %r14, %r14, %r22
	ld %r22, 704(%r8)
	xor %r14, %r14, %r22
	ld %r22, 0(%r10)
	xor %r14, %r14, %r22
	ld %r15, 584(%r8)
	ld %r22, 648(%r8)
	xor %r15, %r15, %r22
	ld %r22, 712(%r8)
	xor %r15, %r15, %r22
	ld %r22, 8(%r10)
	xor %r15, %r15, %r22
	ld %r16, 592(%r8)
	ld %r22, 656(%r8)
	xor %r16, %r16, %r22
	ld %r22, 720(%r8)
	xor %r16, %r16, %r22
	ld %r22, 16(%r10)
	xor %r16, %r16, %r22
	ld %r17, 600(%r8)
	ld %r22, 664(%r8)
	xor %r17, %r17, %r22
	ld %r22, 728(%r8)
	xor %r17, %r17, %r22
	ld %r22, 24(%r10)
	xor %r17, %r17, %r22
	ld %r18, 608(%r8)
	ld %r22, 672(%r8)
	xor %r18, %r18, %r22
	ld %r22, 736(%r8)
	xor %r18, %r18, %r22
	ld %r22, 32(%r10)
	xor %r18, %r18, %r22
	ld %r19, 616(%r8)
	ld %r22, 680(%r8)
	xor %r19, %r19, %r22
	ld %r22, 744(%r8)
	xor %r19, %r19, %r22
	ld %r22, 40(%r10)
	xor %r19, %r19, %r22
	ld %r20, 624(%r8)
	ld %r22, 688(%r8)
	xor %r20, %r20, %r22
	ld %r22, 752(%r8)
	xor %r20, %r20, %r22
	ld %r22, 48(%r10)
	xor %r20, %r20, %r22
	ld %r21, 632(%r8)
	ld %r22, 696(%r8)
	xor %r21, %r21, %r22
	ld %r22, 760(%r8)
	xor %r21, %r21, %r22
	ld %r22, 56(%r10)
	xor %r21, %r21, %r22
	li %r31, 0
	addi %r31, %r31, -1
	xor %r22, %r18, %r16
	xor %r23, %r17, %r14
	xor %r24, %r15, %r23
	xor %r25, %r21, %r22
	xor %r26, %r19, %r24
	xor %r27, %r20, %r16
	xor %r18, %r21, %r18
	xor %r28, %r19, %r25
	xor %r29, %r20, %r28
	xor %r30, %r21, %r17
	xor %r0, %r20, %r18
	xor %r9, %r19, %r22
	xor %r28, %r15, %r28
	xor %r28, %r28, %r31
	std %r28, 0(%r8)
	xor %r28, %r23, %r25
	std %r29, 8(%r8)
	xor %r29, %r14, %r0
	xor %r0, %r26, %r0
	std %r0, 16(%r8)
	xor %r0, %r15, %r27
	xor %r20, %r20, %r28
	xor %r14, %r14, %r25
	xor %r14, %r14, %r31
	xor %r28, %r15, %r30
	xor %r17, %r17, %r9
	xor %r17, %r17, %r31
	xor %r18, %r24, %r18
	std %r25, 24(%r8)
	xor %r25, %r22, %r26
	std %r25, 32(%r8)
	xor %r25, %r26, %r27
	xor %r16, %r21, %r16
	xor %r16, %r16, %r31
	xor %r29, %r15, %r29
	xor %r29, %r29, %r31
	xor %r23, %r23, %r9
	xor %r19, %r19, %r30
	xor %r19, %r19, %r31
	ld %r30, 8(%r8)
	xor %r9, %r15, %r30
	xor %r22, %r22, %r24
	xor %r22, %r22, %r31
	xor %r21, %r21, %r24
	xor %r21, %r21, %r31
	ld %r24, 0(%r8)
	std %r31, 40(%r8)
	and %r31, %r9, %r24
	std %r9, 48(%r8)
	and %r9, %r26, %r17
	xor %r9, %r9, %r31
	std %r26, 56(%r8)
	and %r26, %r20, %r28
	xor %r26, %r26, %r31
	and %r31, %r15, %r23
	std %r15, 64(%r8)
	and %r15, %r27, %r19
	xor %r15, %r15, %r31
	std %r27, 72(%r8)
	and %r27, %r0, %r14
	xor %r27, %r27, %r31
	and %r31, %r18, %r22
	std %r18, 80(%r8)
	and %r18, %r30, %r21
	xor %r18, %r18, %r31
	ld %r30, 24(%r8)
	std %r0, 88(%r8)
	and %r0, %r25, %r30
	xor %r0, %r0, %r31
	xor %r9, %r9, %r18
	xor %r26, %r26, %r0
	xor %r15, %r15, %r18
	xor %r27, %r27, %r0
	xor %r9, %r9, %r16
	ld %r16, 16(%r8)
	xor %r26, %r26, %r16
	ld %r16, 32(%r8)
	xor %r15, %r15, %r16
	xor %r27, %r27, %r29
	xor %r29, %r9, %r26
	and %r9, %r9, %r15
	xor %r16, %r27, %r9
	and %r0, %r29, %r16
	xor %r0, %r0, %r26
	xor %r18, %r15, %r27
	xor %r26, %r26, %r9
	and %r26, %r26, %r18
	xor %r26, %r26, %r27
	xor %r15, %r15, %r26
	xor %r18, %r16, %r26
	and %r27, %r27, %r18
	xor %r15, %r27, %r15
	xor %r16, %r16, %r27
	and %r16, %r0, %r16
	xor %r29, %r29, %r16
	xor %r16, %r29, %r15
	xor %r27, %r0, %r26
	xor %r18, %r0, %r29
	xor %r9, %r26, %r15
	xor %r31, %r27, %r16
	and %r24, %r9, %r24
	and %r17, %r15, %r17
	and %r28, %r26, %r28
	and %r23, %r18, %r23
	and %r19, %r29, %r19
	and %r14, %r0, %r14
	and %r22, %r27, %r22
	and %r21, %r31, %r21
	and %r30, %r16, %r30
	std %r28, 24(%r8)
	ld %r28, 48(%r8)
	and %r9, %r9, %r28
	ld %r28, 56(%r8)
	and %r15, %r15, %r28
	and %r26, %r26, %r20
	ld %r20, 64(%r8)
	and %r18, %r18, %r20
	ld %r20, 72(%r8)
	and %r29, %r29, %r20
	ld %r20, 88(%r8)
	and %r0, %r0, %r20
	ld %r20, 80(%r8)
	and %r27, %r27, %r20
	ld %r20, 8(%r8)
	and %r31, %r31, %r20
	and %r16, %r16, %r25
	xor %r9, %r9, %r27
	xor %r22, %r22, %r15
	xor %r14, %r24, %r14
	xor %r25, %r29, %r22
	xor %r0, %r0, %r25
	xor %r30, %r17, %r30
	xor %r25, %r21, %r0
	xor %r16, %r16, %r9
	xor %r20, %r19, %r14
	xor %r28, %r25, %r16
	std %r19, 8(%r8)
	xor %r19, %r26, %r20
	std %r28, 80(%r8)
	xor %r28, %r31, %r30
	xor %r9, %r9, %r28
	xor %r14, %r23, %r14
	xor %r14, %r9, %r14
	xor %r26, %r26, %r16
	xor %r29, %r29, %r31
	xor %r18, %r18, %r27
	xor %r22, %r22, %r20
	xor %r30, %r30, %r19
	xor %r0, %r0, %r30
	ld %r30, 40(%r8)
	xor %r0, %r0, %r30
	xor %r15, %r15, %r14
	ld %r14, 24(%r8)
	xor %r14, %r14, %r25
	xor %r21, %r21, %r15
	xor %r21, %r21, %r30
	xor %r29, %r29, %r18
	xor %r29, %r29, %r30
	xor %r24, %r24, %r17
	ld %r17, 80(%r8)
	xor %r23, %r23, %r17
	xor %r17, %r17, %r24
	xor %r19, %r19, %r14
	xor %r20, %r19, %r30
	ld %r19, 8(%r8)
	xor %r16, %r19, %r23
	xor %r9, %r9, %r22
	xor %r18, %r9, %r30
	std %r21, 40(%r8)
	or %r21, %r29, %r29
	or %r19, %r17, %r17
	or %r17, %r26, %r26
	or %r15, %r0, %r0
	ld %r14, 40(%r8)
	rldicl %r30, %r20, 48, 0
	rldicl %r23, %r30, 48, 0
	xor %r22, %r30, %r23
	rldicl %r23, %r30, 32, 0
	xor %r22, %r22, %r23
	xor %r22, %r22, %r14
	rldicl %r23, %r14, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 512(%r8)
	xor %r22, %r22, %r23
	std %r22, 512(%r8)
	rldicl %r30, %r21, 48, 0
	rldicl %r23, %r30, 48, 0
	xor %r22, %r30, %r23
	rldicl %r23, %r30, 32, 0
	xor %r22, %r22, %r23
	xor %r22, %r22, %r15
	rldicl %r23, %r15, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 520(%r8)
	xor %r22, %r22, %r23
	std %r22, 520(%r8)
	rldicl %r23, %r14, 48, 0
	xor %r22, %r14, %r23
	rldicl %r23, %r14, 32, 0
	xor %r22, %r22, %r23
	xor %r22, %r22, %r16
	rldicl %r23, %r16, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 528(%r8)
	xor %r22, %r22, %r23
	std %r22, 528(%r8)
	rldicl %r23, %r15, 48, 0
	xor %r22, %r15, %r23
	rldicl %r23, %r15, 32, 0
	xor %r22, %r22, %r23
	xor %r22, %r22, %r17
	rldicl %r23, %r17, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 536(%r8)
	xor %r22, %r22, %r23
	std %r22, 536(%r8)
	rldicl %r23, %r16, 48, 0
	xor %r22, %r16, %r23
	rldicl %r23, %r16, 32, 0
	xor %r22, %r22, %r23
	xor %r22, %r22, %r18
	rldicl %r23, %r18, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 544(%r8)
	xor %r22, %r22, %r23
	std %r22, 544(%r8)
	rldicl %r23, %r17, 48, 0
	xor %r22, %r17, %r23
	rldicl %r23, %r17, 32, 0
	xor %r22, %r22, %r23
	xor %r22, %r22, %r19
	rldicl %r23, %r19, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 552(%r8)
	xor %r22, %r22, %r23
	std %r22, 552(%r8)
	rldicl %r23, %r18, 48, 0
	xor %r22, %r18, %r23
	rldicl %r23, %r18, 32, 0
	xor %r22, %r22, %r23
	xor %r22, %r22, %r20
	rldicl %r23, %r20, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 560(%r8)
	xor %r22, %r22, %r23
	std %r22, 560(%r8)
	rldicl %r23, %r19, 48, 0
	xor %r22, %r19, %r23
	rldicl %r23, %r19, 32, 0
	xor %r22, %r22, %r23
	xor %r22, %r22, %r21
	rldicl %r23, %r21, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 568(%r8)
	xor %r22, %r22, %r23
	std %r22, 568(%r8)
	ld %r14, 640(%r8)
	ld %r22, 704(%r8)
	xor %r14, %r14, %r22
	ld %r22, 512(%r8)
	xor %r14, %r14, %r22
	ld %r22, 64(%r10)
	xor %r14, %r14, %r22
	ld %r15, 648(%r8)
	ld %r22, 712(%r8)
	xor %r15, %r15, %r22
	ld %r22, 520(%r8)
	xor %r15, %r15, %r22
	ld %r22, 72(%r10)
	xor %r15, %r15, %r22
	ld %r16, 656(%r8)
	ld %r22, 720(%r8)
	xor %r16, %r16, %r22
	ld %r22, 528(%r8)
	xor %r16, %r16, %r22
	ld %r22, 80(%r10)
	xor %r16, %r16, %r22
	ld %r17, 664(%r8)
	ld %r22, 728(%r8)
	xor %r17, %r17, %r22
	ld %r22, 536(%r8)
	xor %r17, %r17, %r22
	ld %r22, 88(%r10)
	xor %r17, %r17, %r22
	ld %r18, 672(%r8)
	ld %r22, 736(%r8)
	xor %r18, %r18, %r22
	ld %r22, 544(%r8)
	xor %r18, %r18, %r22
	ld %r22, 96(%r10)
	xor %r18, %r18, %r22
	ld %r19, 680(%r8)
	ld %r22, 744(%r8)
	xor %r19, %r19, %r22
	ld %r22, 552(%r8)
	xor %r19, %r19, %r22
	ld %r22, 104(%r10)
	xor %r19, %r19, %r22
	ld %r20, 688(%r8)
	ld %r22, 752(%r8)
	xor %r20, %r20, %r22
	ld %r22, 560(%r8)
	xor %r20, %r20, %r22
	ld %r22, 112(%r10)
	xor %r20, %r20, %r22
	ld %r21, 696(%r8)
	ld %r22, 760(%r8)
	xor %r21, %r21, %r22
	ld %r22, 568(%r8)
	xor %r21, %r21, %r22
	ld %r22, 120(%r10)
	xor %r21, %r21, %r22
	li %r31, 0
	addi %r31, %r31, -1
	xor %r22, %r18, %r16
	xor %r23, %r17, %r14
	xor %r24, %r15, %r23
	xor %r25, %r21, %r22
	xor %r26, %r19, %r24
	xor %r27, %r20, %r16
	xor %r18, %r21, %r18
	xor %r28, %r19, %r25
	xor %r29, %r20, %r28
	xor %r30, %r21, %r17
	xor %r0, %r20, %r18
	xor %r9, %r19, %r22
	xor %r28, %r15, %r28
	xor %r28, %r28, %r31
	std %r28, 0(%r8)
	xor %r28, %r23, %r25
	std %r29, 8(%r8)
	xor %r29, %r14, %r0
	xor %r0, %r26, %r0
	std %r0, 16(%r8)
	xor %r0, %r15, %r27
	xor %r20, %r20, %r28
	xor %r14, %r14, %r25
	xor %r14, %r14, %r31
	xor %r28, %r15, %r30
	xor %r17, %r17, %r9
	xor %r17, %r17, %r31
	xor %r18, %r24, %r18
	std %r25, 24(%r8)
	xor %r25, %r22, %r26
	std %r25, 32(%r8)
	xor %r25, %r26, %r27
	xor %r16, %r21, %r16
	xor %r16, %r16, %r31
	xor %r29, %r15, %r29
	xor %r29, %r29, %r31
	xor %r23, %r23, %r9
	xor %r19, %r19, %r30
	xor %r19, %r19, %r31
	ld %r30, 8(%r8)
	xor %r9, %r15, %r30
	xor %r22, %r22, %r24
	xor %r22, %r22, %r31
	xor %r21, %r21, %r24
	xor %r21, %r21, %r31
	ld %r24, 0(%r8)
	std %r31, 40(%r8)
	and %r31, %r9, %r24
	std %r9, 48(%r8)
	and %r9, %r26, %r17
	xor %r9, %r9, %r31
	std %r26, 56(%r8)
	and %r26, %r20, %r28
	xor %r26, %r26, %r31
	and %r31, %r15, %r23
	std %r15, 64(%r8)
	and %r15, %r27, %r19
	xor %r15, %r15, %r31
	std %r27, 72(%r8)
	and %r27, %r0, %r14
	xor %r27, %r27, %r31
	and %r31, %r18, %r22
	std %r18, 80(%r8)
	and %r18, %r30, %r21
	xor %r18, %r18, %r31
	ld %r30, 24(%r8)
	std %r0, 88(%r8)
	and %r0, %r25, %r30
	xor %r0, %r0, %r31
	xor %r9, %r9, %r18
	xor %r26, %r26, %r0
	xor %r15, %r15, %r18
	xor %r27, %r27, %r0
	xor %r9, %r9, %r16
	ld %r16, 16(%r8)
	xor %r26, %r26, %r16
	ld %r16, 32(%r8)
	xor %r15, %r15, %r16
	xor %r27, %r27, %r29
	xor %r29, %r9, %r26
	and %r9, %r9, %r15
	xor %r16, %r27, %r9
	and %r0, %r29, %r16
	xor %r0, %r0, %r26
	xor %r18, %r15, %r27
	xor %r26, %r26, %r9
	and %r26, %r26, %r18
	xor %r26, %r26, %r27
	xor %r15, %r15, %r26
	xor %r18, %r16, %r26
	and %r27, %r27, %r18
	xor %r15, %r27, %r15
	xor %r16, %r16, %r27
	and %r16, %r0, %r16
	xor %r29, %r29, %r16
	xor %r16, %r29, %r15
	xor %r27, %r0, %r26
	xor %r18, %r0, %r29
	xor %r9, %r26, %r15
	xor %r31, %r27, %r16
	and %r24, %r9, %r24
	and %r17, %r15, %r17
	and %r28, %r26, %r28
	and %r23, %r18, %r23
	and %r19, %r29, %r19
	and %r14, %r0, %r14
	and %r22, %r27, %r22
	and %r21, %r31, %r21
	and %r30, %r16, %r30
	std %r28, 24(%r8)
	ld %r28, 48(%r8)
	and %r9, %r9, %r28
	ld %r28, 56(%r8)
	and %r15, %r15, %r28
	and %r26, %r26, %r20
	ld %r20, 64(%r8)
	and %r18, %r18, %r20
	ld %r20, 72(%r8)
	and %r29, %r29, %r20
	ld %r20, 88(%r8)
	and %r0, %r0, %r20
	ld %r20, 80(%r8)
	and %r27, %r27, %r20
	ld %r20, 8(%r8)
	and %r31, %r31, %r20
	and %r16, %r16, %r25
	xor %r9, %r9, %r27
	xor %r22, %r22, %r15
	xor %r14, %r24, %r14
	xor %r25, %r29, %r22
	xor %r0, %r0, %r25
	xor %r30, %r17, %r30
	xor %r25, %r21, %r0
	xor %r16, %r16, %r9
	xor %r20, %r19, %r14
	xor %r28, %r25, %r16
	std %r19, 8(%r8)
	xor %r19, %r26, %r20
	std %r28, 80(%r8)
	xor %r28, %r31, %r30
	xor %r9, %r9, %r28
	xor %r14, %r23, %r14
	xor %r14, %r9, %r14
	xor %r26, %r26, %r16
	xor %r29, %r29, %r31
	xor %r18, %r18, %r27
	xor %r22, %r22, %r20
	xor %r30, %r30, %r19
	xor %r0, %r0, %r30
	ld %r30, 40(%r8)
	xor %r0, %r0, %r30
	xor %r15, %r15, %r14
	ld %r14, 24(%r8)
	xor %r14, %r14, %r25
	xor %r21, %r21, %r15
	xor %r21, %r21, %r30
	xor %r29, %r29, %r18
	xor %r29, %r29, %r30
	xor %r24, %r24, %r17
	ld %r17, 80(%r8)
	xor %r23, %r23, %r17
	xor %r17, %r17, %r24
	xor %r19, %r19, %r14
	xor %r20, %r19, %r30
	ld %r19, 8(%r8)
	xor %r16, %r19, %r23
	xor %r9, %r9, %r22
	xor %r18, %r9, %r30
	std %r21, 40(%r8)
	or %r21, %r29, %r29
	or %r19, %r17, %r17
	or %r17, %r26, %r26
	or %r15, %r0, %r0
	ld %r14, 40(%r8)
	rldicl %r30, %r20, 48, 0
	rldicl %r23, %r30, 48, 0
	xor %r22, %r30, %r23
	rldicl %r23, %r30, 32, 0
	xor %r22, %r22, %r23
	xor %r22, %r22, %r14
	rldicl %r23, %r14, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 576(%r8)
	xor %r22, %r22, %r23
	std %r22, 576(%r8)
	rldicl %r30, %r21, 48, 0
	rldicl %r23, %r30, 48, 0
	xor %r22, %r30, %r23
	rldicl %r23, %r30, 32, 0
	xor %r22, %r22, %r23
	xor %r22, %r22, %r15
	rldicl %r23, %r15, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 584(%r8)
	xor %r22, %r22, %r23
	std %r22, 584(%r8)
	rldicl %r23, %r14, 48, 0
	xor %r22, %r14, %r23
	rldicl %r23, %r14, 32, 0
	xor %r22, %r22, %r23
	xor %r22, %r22, %r16
	rldicl %r23, %r16, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 592(%r8)
	xor %r22, %r22, %r23
	std %r22, 592(%r8)
	rldicl %r23, %r15, 48, 0
	xor %r22, %r15, %r23
	rldicl %r23, %r15, 32, 0
	xor %r22, %r22, %r23
	xor %r22, %r22, %r17
	rldicl %r23, %r17, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 600(%r8)
	xor %r22, %r22, %r23
	std %r22, 600(%r8)
	rldicl %r23, %r16, 48, 0
	xor %r22, %r16, %r23
	rldicl %r23, %r16, 32, 0
	xor %r22, %r22, %r23
	xor %r22, %r22, %r18
	rldicl %r23, %r18, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 608(%r8)
	xor %r22, %r22, %r23
	std %r22, 608(%r8)
	rldicl %r23, %r17, 48, 0
	xor %r22, %r17, %r23
	rldicl %r23, %r17, 32, 0
	xor %r22, %r22, %r23
	xor %r22, %r22, %r19
	rldicl %r23, %r19, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 616(%r8)
	xor %r22, %r22, %r23
	std %r22, 616(%r8)
	rldicl %r23, %r18, 48, 0
	xor %r22, %r18, %r23
	rldicl %r23, %r18, 32, 0
	xor %r22, %r22, %r23
	xor %r22, %r22, %r20
	rldicl %r23, %r20, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 624(%r8)
	xor %r22, %r22, %r23
	std %r22, 624(%r8)
	rldicl %r23, %r19, 48, 0
	xor %r22, %r19, %r23
	rldicl %r23, %r19, 32, 0
	xor %r22, %r22, %r23
	xor %r22, %r22, %r21
	rldicl %r23, %r21, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 632(%r8)
	xor %r22, %r22, %r23
	std %r22, 632(%r8)
	ld %r14, 704(%r8)
	ld %r22, 512(%r8)
	xor %r14, %r14, %r22
	ld %r22, 576(%r8)
	xor %r14, %r14, %r22
	ld %r22, 128(%r10)
	xor %r14, %r14, %r22
	ld %r15, 712(%r8)
	ld %r22, 520(%r8)
	xor %r15, %r15, %r22
	ld %r22, 584(%r8)
	xor %r15, %r15, %r22
	ld %r22, 136(%r10)
	xor %r15, %r15, %r22
	ld %r16, 720(%r8)
	ld %r22, 528(%r8)
	xor %r16, %r16, %r22
	ld %r22, 592(%r8)
	xor %r16, %r16, %r22
	ld %r22, 144(%r10)
	xor %r16, %r16, %r22
	ld %r17, 728(%r8)
	ld %r22, 536(%r8)
	xor %r17, %r17, %r22
	ld %r22, 600(%r8)
	xor %r17, %r17, %r22
	ld %r22, 152(%r10)
	xor %r17, %r17, %r22
	ld %r18, 736(%r8)
	ld %r22, 544(%r8)
	xor %r18, %r18, %r22
	ld %r22, 608(%r8)
	xor %r18, %r18, %r22
	ld %r22, 160(%r10)
	xor %r18, %r18, %r22
	ld %r19, 744(%r8)
	ld %r22, 552(%r8)
	xor %r19, %r19, %r22
	ld %r22, 616(%r8)
	xor %r19, %r19, %r22
	ld %r22, 168(%r10)
	xor %r19, %r19, %r22
	ld %r20, 752(%r8)
	ld %r22, 560(%r8)
	xor %r20, %r20, %r22
	ld %r22, 624(%r8)
	xor %r20, %r20, %r22
	ld %r22, 176(%r10)
	xor %r20, %r20, %r22
	ld %r21, 760(%r8)
	ld %r22, 568(%r8)
	xor %r21, %r21, %r22
	ld %r22, 632(%r8)
	xor %r21, %r21, %r22
	ld %r22, 184(%r10)
	xor %r21, %r21, %r22
	li %r31, 0
	addi %r31, %r31, -1
	xor %r22, %r18, %r16
	xor %r23, %r17, %r14
	xor %r24, %r15, %r23
	xor %r25, %r21, %r22
	xor %r26, %r19, %r24
	xor %r27, %r20, %r16
	xor %r18, %r21, %r18
	xor %r28, %r19, %r25
	xor %r29, %r20, %r28
	xor %r30, %r21, %r17
	xor %r0, %r20, %r18
	xor %r9, %r19, %r22
	xor %r28, %r15, %r28
	xor %r28, %r28, %r31
	std %r28, 0(%r8)
	xor %r28, %r23, %r25
	std %r29, 8(%r8)
	xor %r29, %r14, %r0
	xor %r0, %r26, %r0
	std %r0, 16(%r8)
	xor %r0, %r15, %r27
	xor %r20, %r20, %r28
	xor %r14, %r14, %r25
	xor %r14, %r14, %r31
	xor %r28, %r15, %r30
	xor %r17, %r17, %r9
	xor %r17, %r17, %r31
	xor %r18, %r24, %r18
	std %r25, 24(%r8)
	xor %r25, %r22, %r26
	std %r25, 32(%r8)
	xor %r25, %r26, %r27
	xor %r16, %r21, %r16
	xor %r16, %r16, %r31
	xor %r29, %r15, %r29
	xor %r29, %r29, %r31
	xor %r23, %r23, %r9
	xor %r19, %r19, %r30
	xor %r19, %r19, %r31
	ld %r30, 8(%r8)
	xor %r9, %r15, %r30
	xor %r22, %r22, %r24
	xor %r22, %r22, %r31
	xor %r21, %r21, %r24
	xor %r21, %r21, %r31
	ld %r24, 0(%r8)
	std %r31, 40(%r8)
	and %r31, %r9, %r24
	std %r9, 48(%r8)
	and %r9, %r26, %r17
	xor %r9, %r9, %r31
	std %r26, 56(%r8)
	and %r26, %r20, %r28
	xor %r26, %r26, %r31
	and %r31, %r15, %r23
	std %r15, 64(%r8)
	and %r15, %r27, %r19
	xor %r15, %r15, %r31
	std %r27, 72(%r8)
	and %r27, %r0, %r14
	xor %r27, %r27, %r31
	and %r31, %r18, %r22
	std %r18, 80(%r8)
	and %r18, %r30, %r21
	xor %r18, %r18, %r31
	ld %r30, 24(%r8)
	std %r0, 88(%r8)
	and %r0, %r25, %r30
	xor %r0, %r0, %r31
	xor %r9, %r9, %r18
	xor %r26, %r26, %r0
	xor %r15, %r15, %r18
	xor %r27, %r27, %r0
	xor %r9, %r9, %r16
	ld %r16, 16(%r8)
	xor %r26, %r26, %r16
	ld %r16, 32(%r8)
	xor %r15, %r15, %r16
	xor %r27, %r27, %r29
	xor %r29, %r9, %r26
	and %r9, %r9, %r15
	xor %r16, %r27, %r9
	and %r0, %r29, %r16
	xor %r0, %r0, %r26
	xor %r18, %r15, %r27
	xor %r26, %r26, %r9
	and %r26, %r26, %r18
	xor %r26, %r26, %r27
	xor %r15, %r15, %r26
	xor %r18, %r16, %r26
	and %r27, %r27, %r18
	xor %r15, %r27, %r15
	xor %r16, %r16, %r27
	and %r16, %r0, %r16
	xor %r29, %r29, %r16
	xor %r16, %r29, %r15
	xor %r27, %r0, %r26
	xor %r18, %r0, %r29
	xor %r9, %r26, %r15
	xor %r31, %r27, %r16
	and %r24, %r9, %r24
	and %r17, %r15, %r17
	and %r28, %r26, %r28
	and %r23, %r18, %r23
	and %r19, %r29, %r19
	and %r14, %r0, %r14
	and %r22, %r27, %r22
	and %r21, %r31, %r21
	and %r30, %r16, %r30
	std %r28, 24(%r8)
	ld %r28, 48(%r8)
	and %r9, %r9, %r28
	ld %r28, 56(%r8)
	and %r15, %r15, %r28
	and %r26, %r26, %r20
	ld %r20, 64(%r8)
	and %r18, %r18, %r20
	ld %r20, 72(%r8)
	and %r29, %r29, %r20
	ld %r20, 88(%r8)
	and %r0, %r0, %r20
	ld %r20, 80(%r8)
	and %r27, %r27, %r20
	ld %r20, 8(%r8)
	and %r31, %r31, %r20
	and %r16, %r16, %r25
	xor %r9, %r9, %r27
	xor %r22, %r22, %r15
	xor %r14, %r24, %r14
	xor %r25, %r29, %r22
	xor %r0, %r0, %r25
	xor %r30, %r17, %r30
	xor %r25, %r21, %r0
	xor %r16, %r16, %r9
	xor %r20, %r19, %r14
	xor %r28, %r25, %r16
	std %r19, 8(%r8)
	xor %r19, %r26, %r20
	std %r28, 80(%r8)
	xor %r28, %r31, %r30
	xor %r9, %r9, %r28
	xor %r14, %r23, %r14
	xor %r14, %r9, %r14
	xor %r26, %r26, %r16
	xor %r29, %r29, %r31
	xor %r18, %r18, %r27
	xor %r22, %r22, %r20
	xor %r30, %r30, %r19
	xor %r0, %r0, %r30
	ld %r30, 40(%r8)
	xor %r0, %r0, %r30
	xor %r15, %r15, %r14
	ld %r14, 24(%r8)
	xor %r14, %r14, %r25
	xor %r21, %r21, %r15
	xor %r21, %r21, %r30
	xor %r29, %r29, %r18
	xor %r29, %r29, %r30
	xor %r24, %r24, %r17
	ld %r17, 80(%r8)
	xor %r23, %r23, %r17
	xor %r17, %r17, %r24
	xor %r19, %r19, %r14
	xor %r20, %r19, %r30
	ld %r19, 8(%r8)
	xor %r16, %r19, %r23
	xor %r9, %r9, %r22
	xor %r18, %r9, %r30
	std %r21, 40(%r8)
	or %r21, %r29, %r29
	or %r19, %r17, %r17
	or %r17, %r26, %r26
	or %r15, %r0, %r0
	ld %r14, 40(%r8)
	rldicl %r30, %r20, 48, 0
	rldicl %r23, %r30, 48, 0
	xor %r22, %r30, %r23
	rldicl %r23, %r30, 32, 0
	xor %r22, %r22, %r23
	xor %r22, %r22, %r14
	rldicl %r23, %r14, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 640(%r8)
	xor %r22, %r22, %r23
	std %r22, 640(%r8)
	rldicl %r30, %r21, 48, 0
	rldicl %r23, %r30, 48, 0
	xor %r22, %r30, %r23
	rldicl %r23, %r30, 32, 0
	xor %r22, %r22, %r23
	xor %r22, %r22, %r15
	rldicl %r23, %r15, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 648(%r8)
	xor %r22, %r22, %r23
	std %r22, 648(%r8)
	rldicl %r23, %r14, 48, 0
	xor %r22, %r14, %r23
	rldicl %r23, %r14, 32, 0
	xor %r22, %r22, %r23
	xor %r22, %r22, %r16
	rldicl %r23, %r16, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 656(%r8)
	xor %r22, %r22, %r23
	std %r22, 656(%r8)
	rldicl %r23, %r15, 48, 0
	xor %r22, %r15, %r23
	rldicl %r23, %r15, 32, 0
	xor %r22, %r22, %r23
	xor %r22, %r22, %r17
	rldicl %r23, %r17, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 664(%r8)
	xor %r22, %r22, %r23
	std %r22, 664(%r8)
	rldicl %r23, %r16, 48, 0
	xor %r22, %r16, %r23
	rldicl %r23, %r16, 32, 0
	xor %r22, %r22, %r23
	xor %r22, %r22, %r18
	rldicl %r23, %r18, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 672(%r8)
	xor %r22, %r22, %r23
	std %r22, 672(%r8)
	rldicl %r23, %r17, 48, 0
	xor %r22, %r17, %r23
	rldicl %r23, %r17, 32, 0
	xor %r22, %r22, %r23
	xor %r22, %r22, %r19
	rldicl %r23, %r19, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 680(%r8)
	xor %r22, %r22, %r23
	std %r22, 680(%r8)
	rldicl %r23, %r18, 48, 0
	xor %r22, %r18, %r23
	rldicl %r23, %r18, 32, 0
	xor %r22, %r22, %r23
	xor %r22, %r22, %r20
	rldicl %r23, %r20, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 688(%r8)
	xor %r22, %r22, %r23
	std %r22, 688(%r8)
	rldicl %r23, %r19, 48, 0
	xor %r22, %r19, %r23
	rldicl %r23, %r19, 32, 0
	xor %r22, %r22, %r23
	xor %r22, %r22, %r21
	rldicl %r23, %r21, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 696(%r8)
	xor %r22, %r22, %r23
	std %r22, 696(%r8)
	ld %r14, 512(%r8)
	ld %r22, 576(%r8)
	xor %r14, %r14, %r22
	ld %r22, 640(%r8)
	xor %r14, %r14, %r22
	ld %r22, 192(%r10)
	xor %r14, %r14, %r22
	ld %r15, 520(%r8)
	ld %r22, 584(%r8)
	xor %r15, %r15, %r22
	ld %r22, 648(%r8)
	xor %r15, %r15, %r22
	ld %r22, 200(%r10)
	xor %r15, %r15, %r22
	ld %r16, 528(%r8)
	ld %r22, 592(%r8)
	xor %r16, %r16, %r22
	ld %r22, 656(%r8)
	xor %r16, %r16, %r22
	ld %r22, 208(%r10)
	xor %r16, %r16, %r22
	ld %r17, 536(%r8)
	ld %r22, 600(%r8)
	xor %r17, %r17, %r22
	ld %r22, 664(%r8)
	xor %r17, %r17, %r22
	ld %r22, 216(%r10)
	xor %r17, %r17, %r22
	ld %r18, 544(%r8)
	ld %r22, 608(%r8)
	xor %r18, %r18, %r22
	ld %r22, 672(%r8)
	xor %r18, %r18, %r22
	ld %r22, 224(%r10)
	xor %r18, %r18, %r22
	ld %r19, 552(%r8)
	ld %r22, 616(%r8)
	xor %r19, %r19, %r22
	ld %r22, 680(%r8)
	xor %r19, %r19, %r22
	ld %r22, 232(%r10)
	xor %r19, %r19, %r22
	ld %r20, 560(%r8)
	ld %r22, 624(%r8)
	xor %r20, %r20, %r22
	ld %r22, 688(%r8)
	xor %r20, %r20, %r22
	ld %r22, 240(%r10)
	xor %r20, %r20, %r22
	ld %r21, 568(%r8)
	ld %r22, 632(%r8)
	xor %r21, %r21, %r22
	ld %r22, 696(%r8)
	xor %r21, %r21, %r22
	ld %r22, 248(%r10)
	xor %r21, %r21, %r22
	li %r31, 0
	addi %r31, %r31, -1
	xor %r22, %r18, %r16
	xor %r23, %r17, %r14
	xor %r24, %r15, %r23
	xor %r25, %r21, %r22
	xor %r26, %r19, %r24
	xor %r27, %r20, %r16
	xor %r18, %r21, %r18
	xor %r28, %r19, %r25
	xor %r29, %r20, %r28
	xor %r30, %r21, %r17
	xor %r0, %r20, %r18
	xor %r9, %r19, %r22
	xor %r28, %r15, %r28
	xor %r28, %r28, %r31
	std %r28, 0(%r8)
	xor %r28, %r23, %r25
	std %r29, 8(%r8)
	xor %r29, %r14, %r0
	xor %r0, %r26, %r0
	std %r0, 16(%r8)
	xor %r0, %r15, %r27
	xor %r20, %r20, %r28
	xor %r14, %r14, %r25
	xor %r14, %r14, %r31
	xor %r28, %r15, %r30
	xor %r17, %r17, %r9
	xor %r17, %r17, %r31
	xor %r18, %r24, %r18
	std %r25, 24(%r8)
	xor %r25, %r22, %r26
	std %r25, 32(%r8)
	xor %r25, %r26, %r27
	xor %r16, %r21, %r16
	xor %r16, %r16, %r31
	xor %r29, %r15, %r29
	xor %r29, %r29, %r31
	xor %r23, %r23, %r9
	xor %r19, %r19, %r30
	xor %r19, %r19, %r31
	ld %r30, 8(%r8)
	xor %r9, %r15, %r30
	xor %r22, %r22, %r24
	xor %r22, %r22, %r31
	xor %r21, %r21, %r24
	xor %r21, %r21, %r31
	ld %r24, 0(%r8)
	std %r31, 40(%r8)
	and %r31, %r9, %r24
	std %r9, 48(%r8)
	and %r9, %r26, %r17
	xor %r9, %r9, %r31
	std %r26, 56(%r8)
	and %r26, %r20, %r28
	xor %r26, %r26, %r31
	and %r31, %r15, %r23
	std %r15, 64(%r8)
	and %r15, %r27, %r19
	xor %r15, %r15, %r31
	std %r27, 72(%r8)
	and %r27, %r0, %r14
	xor %r27, %r27, %r31
	and %r31, %r18, %r22
	std %r18, 80(%r8)
	and %r18, %r30, %r21
	xor %r18, %r18, %r31
	ld %r30, 24(%r8)
	std %r0, 88(%r8)
	and %r0, %r25, %r30
	xor %r0, %r0, %r31
	xor %r9, %r9, %r18
	xor %r26, %r26, %r0
	xor %r15, %r15, %r18
	xor %r27, %r27, %r0
	xor %r9, %r9, %r16
	ld %r16, 16(%r8)
	xor %r26, %r26, %r16
	ld %r16, 32(%r8)
	xor %r15, %r15, %r16
	xor %r27, %r27, %r29
	xor %r29, %r9, %r26
	and %r9, %r9, %r15
	xor %r16, %r27, %r9
	and %r0, %r29, %r16
	xor %r0, %r0, %r26
	xor %r18, %r15, %r27
	xor %r26, %r26, %r9
	and %r26, %r26, %r18
	xor %r26, %r26, %r27
	xor %r15, %r15, %r26
	xor %r18, %r16, %r26
	and %r27, %r27, %r18
	xor %r15, %r27, %r15
	xor %r16, %r16, %r27
	and %r16, %r0, %r16
	xor %r29, %r29, %r16
	xor %r16, %r29, %r15
	xor %r27, %r0, %r26
	xor %r18, %r0, %r29
	xor %r9, %r26, %r15
	xor %r31, %r27, %r16
	and %r24, %r9, %r24
	and %r17, %r15, %r17
	and %r28, %r26, %r28
	and %r23, %r18, %r23
	and %r19, %r29, %r19
	and %r14, %r0, %r14
	and %r22, %r27, %r22
	and %r21, %r31, %r21
	and %r30, %r16, %r30
	std %r28, 24(%r8)
	ld %r28, 48(%r8)
	and %r9, %r9, %r28
	ld %r28, 56(%r8)
	and %r15, %r15, %r28
	and %r26, %r26, %r20
	ld %r20, 64(%r8)
	and %r18, %r18, %r20
	ld %r20, 72(%r8)
	and %r29, %r29, %r20
	ld %r20, 88(%r8)
	and %r0, %r0, %r20
	ld %r20, 80(%r8)
	and %r27, %r27, %r20
	ld %r20, 8(%r8)
	and %r31, %r31, %r20
	and %r16, %r16, %r25
	xor %r9, %r9, %r27
	xor %r22, %r22, %r15
	xor %r14, %r24, %r14
	xor %r25, %r29, %r22
	xor %r0, %r0, %r25
	xor %r30, %r17, %r30
	xor %r25, %r21, %r0
	xor %r16, %r16, %r9
	xor %r20, %r19, %r14
	xor %r28, %r25, %r16
	std %r19, 8(%r8)
	xor %r19, %r26, %r20
	std %r28, 80(%r8)
	xor %r28, %r31, %r30
	xor %r9, %r9, %r28
	xor %r14, %r23, %r14
	xor %r14, %r9, %r14
	xor %r26, %r26, %r16
	xor %r29, %r29, %r31
	xor %r18, %r18, %r27
	xor %r22, %r22, %r20
	xor %r30, %r30, %r19
	xor %r0, %r0, %r30
	ld %r30, 40(%r8)
	xor %r0, %r0, %r30
	xor %r15, %r15, %r14
	ld %r14, 24(%r8)
	xor %r14, %r14, %r25
	xor %r21, %r21, %r15
	xor %r21, %r21, %r30
	xor %r29, %r29, %r18
	xor %r29, %r29, %r30
	xor %r24, %r24, %r17
	ld %r17, 80(%r8)
	xor %r23, %r23, %r17
	xor %r17, %r17, %r24
	xor %r19, %r19, %r14
	xor %r20, %r19, %r30
	ld %r19, 8(%r8)
	xor %r16, %r19, %r23
	xor %r9, %r9, %r22
	xor %r18, %r9, %r30
	std %r21, 40(%r8)
	or %r21, %r29, %r29
	or %r19, %r17, %r17
	or %r17, %r26, %r26
	or %r15, %r0, %r0
	ld %r14, 40(%r8)
	rldicl %r30, %r20, 48, 0
	rldicl %r23, %r30, 48, 0
	xor %r22, %r30, %r23
	rldicl %r23, %r30, 32, 0
	xor %r22, %r22, %r23
	xor %r22, %r22, %r14
	rldicl %r23, %r14, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 704(%r8)
	xor %r22, %r22, %r23
	std %r22, 704(%r8)
	rldicl %r30, %r21, 48, 0
	rldicl %r23, %r30, 48, 0
	xor %r22, %r30, %r23
	rldicl %r23, %r30, 32, 0
	xor %r22, %r22, %r23
	xor %r22, %r22, %r15
	rldicl %r23, %r15, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 712(%r8)
	xor %r22, %r22, %r23
	std %r22, 712(%r8)
	rldicl %r23, %r14, 48, 0
	xor %r22, %r14, %r23
	rldicl %r23, %r14, 32, 0
	xor %r22, %r22, %r23
	xor %r22, %r22, %r16
	rldicl %r23, %r16, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 720(%r8)
	xor %r22, %r22, %r23
	std %r22, 720(%r8)
	rldicl %r23, %r15, 48, 0
	xor %r22, %r15, %r23
	rldicl %r23, %r15, 32, 0
	xor %r22, %r22, %r23
	xor %r22, %r22, %r17
	rldicl %r23, %r17, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 728(%r8)
	xor %r22, %r22, %r23
	std %r22, 728(%r8)
	rldicl %r23, %r16, 48, 0
	xor %r22, %r16, %r23
	rldicl %r23, %r16, 32, 0
	xor %r22, %r22, %r23
	xor %r22, %r22, %r18
	rldicl %r23, %r18, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 736(%r8)
	xor %r22, %r22, %r23
	std %r22, 736(%r8)
	rldicl %r23, %r17, 48, 0
	xor %r22, %r17, %r23
	rldicl %r23, %r17, 32, 0
	xor %r22, %r22, %r23
	xor %r22, %r22, %r19
	rldicl %r23, %r19, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 744(%r8)
	xor %r22, %r22, %r23
	std %r22, 744(%r8)
	rldicl %r23, %r18, 48, 0
	xor %r22, %r18, %r23
	rldicl %r23, %r18, 32, 0
	xor %r22, %r22, %r23
	xor %r22, %r22, %r20
	rldicl %r23, %r20, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 752(%r8)
	xor %r22, %r22, %r23
	std %r22, 752(%r8)
	rldicl %r23, %r19, 48, 0
	xor %r22, %r19, %r23
	rldicl %r23, %r19, 32, 0
	xor %r22, %r22, %r23
	xor %r22, %r22, %r21
	rldicl %r23, %r21, 16, 0
	xor %r22, %r22, %r23
	ld %r23, 760(%r8)
	xor %r22, %r22, %r23
	std %r22, 760(%r8)
	addi %r10, %r10, 256
	subf %r22, %r11, %r10
	cmpldi %cr0, %r22, 0
	bne %cr0, 20b
	lis %r24, 0
	ori %r24, %r24, 0
	rldicr %r24, %r24, 32, 31
	oris %r24, %r24, 65535
	ori %r24, %r24, 0
	lis %r25, 0
	ori %r25, %r25, 65280
	rldicr %r25, %r25, 32, 31
	oris %r25, %r25, 0
	ori %r25, %r25, 65280
	lis %r26, 255
	ori %r26, %r26, 255
	rldicr %r26, %r26, 32, 31
	oris %r26, %r26, 255
	ori %r26, %r26, 255
	lis %r27, 21845
	ori %r27, %r27, 21845
	rldicr %r27, %r27, 32, 31
	oris %r27, %r27, 21845
	ori %r27, %r27, 21845
	lis %r28, 13107
	ori %r28, %r28, 13107
	rldicr %r28, %r28, 32, 31
	oris %r28, %r28, 13107
	ori %r28, %r28, 13107
	lis %r29, 3855
	ori %r29, %r29, 3855
	rldicr %r29, %r29, 32, 31
	oris %r29, %r29, 3855
	ori %r29, %r29, 3855
	ld %r14, 704(%r8)
	ld %r15, 712(%r8)
	ld %r16, 720(%r8)
	ld %r17, 728(%r8)
	ld %r18, 736(%r8)
	ld %r19, 744(%r8)
	ld %r20, 752(%r8)
	ld %r21, 760(%r8)
	rldicl %r22, %r14, 63, 1
	xor %r22, %r22, %r15
	and %r22, %r22, %r27
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r16, 63, 1
	xor %r22, %r22, %r17
	and %r22, %r22, %r27
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r18, 63, 1
	xor %r22, %r22, %r19
	and %r22, %r22, %r27
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r20, 63, 1
	xor %r22, %r22, %r21
	and %r22, %r22, %r27
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r14, 62, 2
	xor %r22, %r22, %r16
	and %r22, %r22, %r28
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 62, 2
	xor %r22, %r22, %r17
	and %r22, %r22, %r28
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r18, 62, 2
	xor %r22, %r22, %r20
	and %r22, %r22, %r28
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 62, 2
	xor %r22, %r22, %r21
	and %r22, %r22, %r28
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r14, 60, 4
	xor %r22, %r22, %r18
	and %r22, %r22, %r29
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 60, 4
	xor %r22, %r22, %r19
	and %r22, %r22, %r29
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 60, 4
	xor %r22, %r22, %r20
	and %r22, %r22, %r29
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 60, 4
	xor %r22, %r22, %r21
	and %r22, %r22, %r29
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 4, 0
	xor %r17, %r17, %r22
	std %r14, 768(%r8)
	std %r15, 784(%r8)
	std %r16, 800(%r8)
	std %r17, 816(%r8)
	std %r18, 832(%r8)
	std %r19, 848(%r8)
	std %r20, 864(%r8)
	std %r21, 880(%r8)
	ld %r14, 640(%r8)
	ld %r15, 648(%r8)
	ld %r16, 656(%r8)
	ld %r17, 664(%r8)
	ld %r18, 672(%r8)
	ld %r19, 680(%r8)
	ld %r20, 688(%r8)
	ld %r21, 696(%r8)
	rldicl %r22, %r14, 63, 1
	xor %r22, %r22, %r15
	and %r22, %r22, %r27
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r16, 63, 1
	xor %r22, %r22, %r17
	and %r22, %r22, %r27
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r18, 63, 1
	xor %r22, %r22, %r19
	and %r22, %r22, %r27
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r20, 63, 1
	xor %r22, %r22, %r21
	and %r22, %r22, %r27
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r14, 62, 2
	xor %r22, %r22, %r16
	and %r22, %r22, %r28
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 62, 2
	xor %r22, %r22, %r17
	and %r22, %r22, %r28
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r18, 62, 2
	xor %r22, %r22, %r20
	and %r22, %r22, %r28
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 62, 2
	xor %r22, %r22, %r21
	and %r22, %r22, %r28
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r14, 60, 4
	xor %r22, %r22, %r18
	and %r22, %r22, %r29
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 60, 4
	xor %r22, %r22, %r19
	and %r22, %r22, %r29
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 60, 4
	xor %r22, %r22, %r20
	and %r22, %r22, %r29
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 60, 4
	xor %r22, %r22, %r21
	and %r22, %r22, %r29
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 4, 0
	xor %r17, %r17, %r22
	std %r14, 896(%r8)
	std %r15, 912(%r8)
	std %r16, 928(%r8)
	std %r17, 944(%r8)
	std %r18, 960(%r8)
	std %r19, 976(%r8)
	std %r20, 992(%r8)
	std %r21, 1008(%r8)
	ld %r14, 576(%r8)
	ld %r15, 584(%r8)
	ld %r16, 592(%r8)
	ld %r17, 600(%r8)
	ld %r18, 608(%r8)
	ld %r19, 616(%r8)
	ld %r20, 624(%r8)
	ld %r21, 632(%r8)
	rldicl %r22, %r14, 63, 1
	xor %r22, %r22, %r15
	and %r22, %r22, %r27
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r16, 63, 1
	xor %r22, %r22, %r17
	and %r22, %r22, %r27
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r18, 63, 1
	xor %r22, %r22, %r19
	and %r22, %r22, %r27
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r20, 63, 1
	xor %r22, %r22, %r21
	and %r22, %r22, %r27
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r14, 62, 2
	xor %r22, %r22, %r16
	and %r22, %r22, %r28
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 62, 2
	xor %r22, %r22, %r17
	and %r22, %r22, %r28
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r18, 62, 2
	xor %r22, %r22, %r20
	and %r22, %r22, %r28
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 62, 2
	xor %r22, %r22, %r21
	and %r22, %r22, %r28
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r14, 60, 4
	xor %r22, %r22, %r18
	and %r22, %r22, %r29
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 60, 4
	xor %r22, %r22, %r19
	and %r22, %r22, %r29
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 60, 4
	xor %r22, %r22, %r20
	and %r22, %r22, %r29
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 60, 4
	xor %r22, %r22, %r21
	and %r22, %r22, %r29
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 4, 0
	xor %r17, %r17, %r22
	std %r14, 776(%r8)
	std %r15, 792(%r8)
	std %r16, 808(%r8)
	std %r17, 824(%r8)
	std %r18, 840(%r8)
	std %r19, 856(%r8)
	std %r20, 872(%r8)
	std %r21, 888(%r8)
	ld %r14, 512(%r8)
	ld %r15, 520(%r8)
	ld %r16, 528(%r8)
	ld %r17, 536(%r8)
	ld %r18, 544(%r8)
	ld %r19, 552(%r8)
	ld %r20, 560(%r8)
	ld %r21, 568(%r8)
	rldicl %r22, %r14, 63, 1
	xor %r22, %r22, %r15
	and %r22, %r22, %r27
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r16, 63, 1
	xor %r22, %r22, %r17
	and %r22, %r22, %r27
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r18, 63, 1
	xor %r22, %r22, %r19
	and %r22, %r22, %r27
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r20, 63, 1
	xor %r22, %r22, %r21
	and %r22, %r22, %r27
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r14, 62, 2
	xor %r22, %r22, %r16
	and %r22, %r22, %r28
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 62, 2
	xor %r22, %r22, %r17
	and %r22, %r22, %r28
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r18, 62, 2
	xor %r22, %r22, %r20
	and %r22, %r22, %r28
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 62, 2
	xor %r22, %r22, %r21
	and %r22, %r22, %r28
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r14, 60, 4
	xor %r22, %r22, %r18
	and %r22, %r22, %r29
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 60, 4
	xor %r22, %r22, %r19
	and %r22, %r22, %r29
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 60, 4
	xor %r22, %r22, %r20
	and %r22, %r22, %r29
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 60, 4
	xor %r22, %r22, %r21
	and %r22, %r22, %r29
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 4, 0
	xor %r17, %r17, %r22
	std %r14, 904(%r8)
	std %r15, 920(%r8)
	std %r16, 936(%r8)
	std %r17, 952(%r8)
	std %r18, 968(%r8)
	std %r19, 984(%r8)
	std %r20, 1000(%r8)
	std %r21, 1016(%r8)
	ld %r14, 768(%r8)
	ld %r18, 896(%r8)
	ld %r15, 784(%r8)
	ld %r19, 912(%r8)
	ld %r16, 800(%r8)
	ld %r20, 928(%r8)
	ld %r17, 816(%r8)
	ld %r21, 944(%r8)
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r26
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r26
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r26
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r26
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r14
	and %r22, %r22, %r25
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r15
	and %r22, %r22, %r25
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r16
	and %r22, %r22, %r25
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r17
	and %r22, %r22, %r25
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r25
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r25
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r25
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r25
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 48, 16
	xor %r22, %r22, %r14
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 16, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 48, 16
	xor %r22, %r22, %r15
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 16, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 48, 16
	xor %r22, %r22, %r16
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 16, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 48, 16
	xor %r22, %r22, %r17
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 16, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 48, 16
	xor %r22, %r22, %r18
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 16, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 48, 16
	xor %r22, %r22, %r19
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 16, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 48, 16
	xor %r22, %r22, %r20
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 16, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 48, 16
	xor %r22, %r22, %r21
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 16, 0
	xor %r21, %r21, %r22
	std %r14, 768(%r8)
	std %r18, 896(%r8)
	std %r15, 784(%r8)
	std %r19, 912(%r8)
	std %r16, 800(%r8)
	std %r20, 928(%r8)
	std %r17, 816(%r8)
	std %r21, 944(%r8)
	ld %r14, 832(%r8)
	ld %r18, 960(%r8)
	ld %r15, 848(%r8)
	ld %r19, 976(%r8)
	ld %r16, 864(%r8)
	ld %r20, 992(%r8)
	ld %r17, 880(%r8)
	ld %r21, 1008(%r8)
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r26
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r26
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r26
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r26
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r14
	and %r22, %r22, %r25
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r15
	and %r22, %r22, %r25
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r16
	and %r22, %r22, %r25
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r17
	and %r22, %r22, %r25
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r25
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r25
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r25
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r25
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 48, 16
	xor %r22, %r22, %r14
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 16, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 48, 16
	xor %r22, %r22, %r15
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 16, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 48, 16
	xor %r22, %r22, %r16
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 16, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 48, 16
	xor %r22, %r22, %r17
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 16, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 48, 16
	xor %r22, %r22, %r18
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 16, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 48, 16
	xor %r22, %r22, %r19
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 16, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 48, 16
	xor %r22, %r22, %r20
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 16, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 48, 16
	xor %r22, %r22, %r21
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 16, 0
	xor %r21, %r21, %r22
	std %r14, 832(%r8)
	std %r18, 960(%r8)
	std %r15, 848(%r8)
	std %r19, 976(%r8)
	std %r16, 864(%r8)
	std %r20, 992(%r8)
	std %r17, 880(%r8)
	std %r21, 1008(%r8)
	ld %r14, 776(%r8)
	ld %r18, 904(%r8)
	ld %r15, 792(%r8)
	ld %r19, 920(%r8)
	ld %r16, 808(%r8)
	ld %r20, 936(%r8)
	ld %r17, 824(%r8)
	ld %r21, 952(%r8)
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r26
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r26
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r26
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r26
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r14
	and %r22, %r22, %r25
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r15
	and %r22, %r22, %r25
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r16
	and %r22, %r22, %r25
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r17
	and %r22, %r22, %r25
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r25
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r25
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r25
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r25
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 48, 16
	xor %r22, %r22, %r14
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 16, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 48, 16
	xor %r22, %r22, %r15
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 16, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 48, 16
	xor %r22, %r22, %r16
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 16, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 48, 16
	xor %r22, %r22, %r17
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 16, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 48, 16
	xor %r22, %r22, %r18
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 16, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 48, 16
	xor %r22, %r22, %r19
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 16, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 48, 16
	xor %r22, %r22, %r20
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 16, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 48, 16
	xor %r22, %r22, %r21
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 16, 0
	xor %r21, %r21, %r22
	std %r14, 776(%r8)
	std %r18, 904(%r8)
	std %r15, 792(%r8)
	std %r19, 920(%r8)
	std %r16, 808(%r8)
	std %r20, 936(%r8)
	std %r17, 824(%r8)
	std %r21, 952(%r8)
	ld %r14, 840(%r8)
	ld %r18, 968(%r8)
	ld %r15, 856(%r8)
	ld %r19, 984(%r8)
	ld %r16, 872(%r8)
	ld %r20, 1000(%r8)
	ld %r17, 888(%r8)
	ld %r21, 1016(%r8)
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r26
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r26
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r26
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r26
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r14
	and %r22, %r22, %r25
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r15
	and %r22, %r22, %r25
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r16
	and %r22, %r22, %r25
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r17
	and %r22, %r22, %r25
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r25
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r25
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r25
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r25
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 48, 16
	xor %r22, %r22, %r14
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 16, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 48, 16
	xor %r22, %r22, %r15
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 16, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 48, 16
	xor %r22, %r22, %r16
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 16, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 48, 16
	xor %r22, %r22, %r17
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 16, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 48, 16
	xor %r22, %r22, %r18
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 16, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 48, 16
	xor %r22, %r22, %r19
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 16, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 48, 16
	xor %r22, %r22, %r20
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 16, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 48, 16
	xor %r22, %r22, %r21
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 16, 0
	xor %r21, %r21, %r22
	std %r14, 840(%r8)
	std %r18, 968(%r8)
	std %r15, 856(%r8)
	std %r19, 984(%r8)
	std %r16, 872(%r8)
	std %r20, 1000(%r8)
	std %r17, 888(%r8)
	std %r21, 1016(%r8)
	ld %r14, 3072(%r8)
	ld %r15, 3080(%r8)
	ld %r16, 3088(%r8)
	ld %r17, 3096(%r8)
	ld %r18, 3104(%r8)
	ld %r19, 3112(%r8)
	ld %r20, 3120(%r8)
	ld %r21, 3128(%r8)
	ld %r22, 3136(%r8)
	ld %r23, 3144(%r8)
	ld %r24, 3152(%r8)
	ld %r25, 3160(%r8)
	ld %r26, 3168(%r8)
	ld %r27, 3176(%r8)
	ld %r28, 3184(%r8)
	ld %r29, 3192(%r8)
	ld %r30, 3200(%r8)
	ld %r31, 3208(%r8)
	blr
