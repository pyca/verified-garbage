// The functions of `src/internal/vg_p384_mul.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p384_mul:
	std %r31, 2224(%r3)
	mflr %r0
	std %r0, 2232(%r3)
	li %r31, 48
20:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 1552(%r4)
	rldicr %r5, %r31, 3, 60
	add %r5, %r3, %r5
	li %r7, 1
	and %r6, %r4, %r7
	stb %r6, 4096(%r5)
	rldicl %r6, %r4, 63, 1
	and %r6, %r6, %r7
	stb %r6, 4097(%r5)
	rldicl %r6, %r4, 62, 2
	and %r6, %r6, %r7
	stb %r6, 4098(%r5)
	rldicl %r6, %r4, 61, 3
	and %r6, %r6, %r7
	stb %r6, 4099(%r5)
	rldicl %r6, %r4, 60, 4
	and %r6, %r6, %r7
	stb %r6, 4100(%r5)
	rldicl %r6, %r4, 59, 5
	and %r6, %r6, %r7
	stb %r6, 4101(%r5)
	rldicl %r6, %r4, 58, 6
	and %r6, %r6, %r7
	stb %r6, 4102(%r5)
	rldicl %r6, %r4, 57, 7
	and %r6, %r6, %r7
	stb %r6, 4103(%r5)
	cmpldi %cr0, %r31, 0
	bne %cr0, 20b
	ld %r4, 736(%r3)
	std %r4, 1456(%r3)
	ld %r4, 744(%r3)
	std %r4, 1464(%r3)
	ld %r4, 752(%r3)
	std %r4, 1472(%r3)
	ld %r4, 760(%r3)
	std %r4, 1480(%r3)
	ld %r4, 768(%r3)
	std %r4, 1488(%r3)
	ld %r4, 776(%r3)
	std %r4, 1496(%r3)
	ld %r4, 784(%r3)
	std %r4, 1504(%r3)
	ld %r4, 792(%r3)
	std %r4, 1512(%r3)
	ld %r4, 800(%r3)
	std %r4, 1520(%r3)
	ld %r4, 808(%r3)
	std %r4, 1528(%r3)
	ld %r4, 816(%r3)
	std %r4, 1536(%r3)
	ld %r4, 824(%r3)
	std %r4, 1544(%r3)
	ld %r4, 208(%r3)
	std %r4, 736(%r3)
	ld %r4, 216(%r3)
	std %r4, 744(%r3)
	ld %r4, 224(%r3)
	std %r4, 752(%r3)
	ld %r4, 232(%r3)
	std %r4, 760(%r3)
	ld %r4, 240(%r3)
	std %r4, 768(%r3)
	ld %r4, 248(%r3)
	std %r4, 776(%r3)
	ld %r4, 304(%r3)
	std %r4, 784(%r3)
	ld %r4, 312(%r3)
	std %r4, 792(%r3)
	ld %r4, 320(%r3)
	std %r4, 800(%r3)
	ld %r4, 328(%r3)
	std %r4, 808(%r3)
	ld %r4, 336(%r3)
	std %r4, 816(%r3)
	ld %r4, 344(%r3)
	std %r4, 824(%r3)
	ld %r4, 208(%r3)
	std %r4, 832(%r3)
	ld %r4, 216(%r3)
	std %r4, 840(%r3)
	ld %r4, 224(%r3)
	std %r4, 848(%r3)
	ld %r4, 232(%r3)
	std %r4, 856(%r3)
	ld %r4, 240(%r3)
	std %r4, 864(%r3)
	ld %r4, 248(%r3)
	std %r4, 872(%r3)
	ld %r4, 1456(%r3)
	std %r4, 3120(%r3)
	ld %r4, 1464(%r3)
	std %r4, 3128(%r3)
	ld %r4, 1472(%r3)
	std %r4, 3136(%r3)
	ld %r4, 1480(%r3)
	std %r4, 3144(%r3)
	ld %r4, 1488(%r3)
	std %r4, 3152(%r3)
	ld %r4, 1496(%r3)
	std %r4, 3160(%r3)
	ld %r4, 1504(%r3)
	std %r4, 3168(%r3)
	ld %r4, 1512(%r3)
	std %r4, 3176(%r3)
	ld %r4, 1520(%r3)
	std %r4, 3184(%r3)
	ld %r4, 1528(%r3)
	std %r4, 3192(%r3)
	ld %r4, 1536(%r3)
	std %r4, 3200(%r3)
	ld %r4, 1544(%r3)
	std %r4, 3208(%r3)
	ld %r4, 304(%r3)
	std %r4, 3216(%r3)
	ld %r4, 312(%r3)
	std %r4, 3224(%r3)
	ld %r4, 320(%r3)
	std %r4, 3232(%r3)
	ld %r4, 328(%r3)
	std %r4, 3240(%r3)
	ld %r4, 336(%r3)
	std %r4, 3248(%r3)
	ld %r4, 344(%r3)
	std %r4, 3256(%r3)
	ld %r4, 352(%r3)
	std %r4, 3264(%r3)
	ld %r4, 360(%r3)
	std %r4, 3272(%r3)
	ld %r4, 368(%r3)
	std %r4, 3280(%r3)
	ld %r4, 376(%r3)
	std %r4, 3288(%r3)
	ld %r4, 384(%r3)
	std %r4, 3296(%r3)
	ld %r4, 392(%r3)
	std %r4, 3304(%r3)
	ld %r4, 400(%r3)
	std %r4, 3312(%r3)
	ld %r4, 408(%r3)
	std %r4, 3320(%r3)
	ld %r4, 416(%r3)
	std %r4, 3328(%r3)
	ld %r4, 424(%r3)
	std %r4, 3336(%r3)
	ld %r4, 432(%r3)
	std %r4, 3344(%r3)
	ld %r4, 440(%r3)
	std %r4, 3352(%r3)
	li %r31, 384
21:
	addi %r31, %r31, -1
	ld %r4, 736(%r3)
	std %r4, 2976(%r3)
	ld %r4, 744(%r3)
	std %r4, 2984(%r3)
	ld %r4, 752(%r3)
	std %r4, 2992(%r3)
	ld %r4, 760(%r3)
	std %r4, 3000(%r3)
	ld %r4, 768(%r3)
	std %r4, 3008(%r3)
	ld %r4, 776(%r3)
	std %r4, 3016(%r3)
	ld %r4, 784(%r3)
	std %r4, 3024(%r3)
	ld %r4, 792(%r3)
	std %r4, 3032(%r3)
	ld %r4, 800(%r3)
	std %r4, 3040(%r3)
	ld %r4, 808(%r3)
	std %r4, 3048(%r3)
	ld %r4, 816(%r3)
	std %r4, 3056(%r3)
	ld %r4, 824(%r3)
	std %r4, 3064(%r3)
	ld %r4, 832(%r3)
	std %r4, 3072(%r3)
	ld %r4, 840(%r3)
	std %r4, 3080(%r3)
	ld %r4, 848(%r3)
	std %r4, 3088(%r3)
	ld %r4, 856(%r3)
	std %r4, 3096(%r3)
	ld %r4, 864(%r3)
	std %r4, 3104(%r3)
	ld %r4, 872(%r3)
	std %r4, 3112(%r3)
	bl {vg_p384_point_double}
	ld %r4, 2832(%r3)
	std %r4, 2976(%r3)
	ld %r4, 2840(%r3)
	std %r4, 2984(%r3)
	ld %r4, 2848(%r3)
	std %r4, 2992(%r3)
	ld %r4, 2856(%r3)
	std %r4, 3000(%r3)
	ld %r4, 2864(%r3)
	std %r4, 3008(%r3)
	ld %r4, 2872(%r3)
	std %r4, 3016(%r3)
	ld %r4, 2880(%r3)
	std %r4, 3024(%r3)
	ld %r4, 2888(%r3)
	std %r4, 3032(%r3)
	ld %r4, 2896(%r3)
	std %r4, 3040(%r3)
	ld %r4, 2904(%r3)
	std %r4, 3048(%r3)
	ld %r4, 2912(%r3)
	std %r4, 3056(%r3)
	ld %r4, 2920(%r3)
	std %r4, 3064(%r3)
	ld %r4, 2928(%r3)
	std %r4, 3072(%r3)
	ld %r4, 2936(%r3)
	std %r4, 3080(%r3)
	ld %r4, 2944(%r3)
	std %r4, 3088(%r3)
	ld %r4, 2952(%r3)
	std %r4, 3096(%r3)
	ld %r4, 2960(%r3)
	std %r4, 3104(%r3)
	ld %r4, 2968(%r3)
	std %r4, 3112(%r3)
	bl {vg_p384_point_add}
	add %r4, %r3, %r31
	lbz %r4, 4096(%r4)
	li %r5, 0
	subf %r10, %r4, %r5
	ld %r4, 2976(%r3)
	ld %r5, 2832(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 736(%r3)
	ld %r4, 2984(%r3)
	ld %r5, 2840(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 744(%r3)
	ld %r4, 2992(%r3)
	ld %r5, 2848(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 752(%r3)
	ld %r4, 3000(%r3)
	ld %r5, 2856(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 760(%r3)
	ld %r4, 3008(%r3)
	ld %r5, 2864(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 768(%r3)
	ld %r4, 3016(%r3)
	ld %r5, 2872(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 776(%r3)
	ld %r4, 3024(%r3)
	ld %r5, 2880(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 784(%r3)
	ld %r4, 3032(%r3)
	ld %r5, 2888(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 792(%r3)
	ld %r4, 3040(%r3)
	ld %r5, 2896(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 800(%r3)
	ld %r4, 3048(%r3)
	ld %r5, 2904(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 808(%r3)
	ld %r4, 3056(%r3)
	ld %r5, 2912(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 816(%r3)
	ld %r4, 3064(%r3)
	ld %r5, 2920(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 824(%r3)
	ld %r4, 3072(%r3)
	ld %r5, 2928(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 832(%r3)
	ld %r4, 3080(%r3)
	ld %r5, 2936(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 840(%r3)
	ld %r4, 3088(%r3)
	ld %r5, 2944(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 848(%r3)
	ld %r4, 3096(%r3)
	ld %r5, 2952(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 856(%r3)
	ld %r4, 3104(%r3)
	ld %r5, 2960(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 864(%r3)
	ld %r4, 3112(%r3)
	ld %r5, 2968(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 872(%r3)
	cmpldi %cr0, %r31, 0
	bne %cr0, 21b
	ld %r0, 2232(%r3)
	mtlr %r0
	ld %r31, 2224(%r3)
	blr
