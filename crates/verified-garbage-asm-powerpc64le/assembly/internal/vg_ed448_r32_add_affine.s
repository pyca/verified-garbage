// The functions of `src/internal/vg_ed448_r32_add_affine.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed448_r32_add_affine:
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
20:
	ld %r4, 112(%r9)
	li %r8, 0
	ld %r5, 112(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 120(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 128(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 136(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 144(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 152(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 160(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 20b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 392(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 396(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 400(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 404(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 408(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 412(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 416(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 420(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 424(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 428(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 432(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 436(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 440(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 444(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 392(%r6)
	add %r7, %r7, %r8
	stw %r7, 392(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 396(%r6)
	add %r7, %r7, %r8
	stw %r7, 396(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 400(%r6)
	add %r7, %r7, %r8
	stw %r7, 400(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 404(%r6)
	add %r7, %r7, %r8
	stw %r7, 404(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 408(%r6)
	add %r7, %r7, %r8
	stw %r7, 408(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 412(%r6)
	add %r7, %r7, %r8
	stw %r7, 412(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 416(%r6)
	add %r7, %r7, %r8
	stw %r7, 416(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 420(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 420(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 424(%r6)
	add %r7, %r7, %r8
	stw %r7, 424(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 428(%r6)
	add %r7, %r7, %r8
	stw %r7, 428(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 432(%r6)
	add %r7, %r7, %r8
	stw %r7, 432(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 436(%r6)
	add %r7, %r7, %r8
	stw %r7, 436(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 440(%r6)
	add %r7, %r7, %r8
	stw %r7, 440(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 444(%r6)
	add %r7, %r7, %r8
	stw %r7, 444(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 392(%r6)
	add %r7, %r7, %r8
	stw %r7, 392(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 396(%r6)
	add %r7, %r7, %r8
	stw %r7, 396(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 400(%r6)
	add %r7, %r7, %r8
	stw %r7, 400(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 404(%r6)
	add %r7, %r7, %r8
	stw %r7, 404(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 408(%r6)
	add %r7, %r7, %r8
	stw %r7, 408(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 412(%r6)
	add %r7, %r7, %r8
	stw %r7, 412(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 416(%r6)
	add %r7, %r7, %r8
	stw %r7, 416(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 420(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 420(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 424(%r6)
	add %r7, %r7, %r8
	stw %r7, 424(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 428(%r6)
	add %r7, %r7, %r8
	stw %r7, 428(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 432(%r6)
	add %r7, %r7, %r8
	stw %r7, 432(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 436(%r6)
	add %r7, %r7, %r8
	stw %r7, 436(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 440(%r6)
	add %r7, %r7, %r8
	stw %r7, 440(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 444(%r6)
	add %r7, %r7, %r8
	stw %r7, 444(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
21:
	ld %r4, 56(%r9)
	li %r8, 0
	ld %r5, 168(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 176(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 184(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 21b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 448(%r6)
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 452(%r6)
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 456(%r6)
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 460(%r6)
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 464(%r6)
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 468(%r6)
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 472(%r6)
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 476(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 480(%r6)
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 484(%r6)
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 488(%r6)
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 492(%r6)
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 496(%r6)
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 500(%r6)
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 448(%r6)
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 452(%r6)
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 456(%r6)
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 460(%r6)
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 464(%r6)
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 468(%r6)
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 472(%r6)
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 476(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 480(%r6)
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 484(%r6)
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 488(%r6)
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 492(%r6)
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 496(%r6)
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 500(%r6)
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
22:
	ld %r4, 0(%r9)
	li %r8, 0
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 256(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 264(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 272(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 22b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 504(%r6)
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 516(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 520(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 524(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 528(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 532(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 536(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 504(%r6)
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 516(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 520(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 524(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 528(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 532(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 536(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
23:
	ld %r4, 336(%r9)
	li %r8, 0
	ld %r5, 448(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 456(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 464(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 472(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 480(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 488(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 496(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 23b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 560(%r6)
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 580(%r6)
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 584(%r6)
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 588(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 592(%r6)
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 596(%r6)
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 600(%r6)
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 604(%r6)
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 608(%r6)
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 612(%r6)
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 560(%r6)
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 580(%r6)
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 584(%r6)
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 588(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 592(%r6)
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 596(%r6)
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 600(%r6)
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 604(%r6)
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 608(%r6)
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 612(%r6)
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
24:
	ld %r4, 560(%r9)
	li %r8, 0
	ld %r5, 504(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 512(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 520(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 528(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 536(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 24b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 560(%r6)
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 580(%r6)
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 584(%r6)
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 588(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 592(%r6)
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 596(%r6)
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 600(%r6)
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 604(%r6)
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 608(%r6)
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 612(%r6)
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 560(%r6)
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 580(%r6)
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 584(%r6)
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 588(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 592(%r6)
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 596(%r6)
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 600(%r6)
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 604(%r6)
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 608(%r6)
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 612(%r6)
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 34, 29
	lwz %r7, 392(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 560(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 396(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 564(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 400(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 568(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 404(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 572(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 408(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 576(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 412(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 580(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 416(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 584(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 640(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 420(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -8
	lwz %r5, 588(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 644(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 424(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 592(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 648(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 428(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 596(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 652(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 432(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 600(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 656(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 436(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 604(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 660(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 440(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 608(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 664(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 444(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 612(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 668(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 616(%r6)
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 620(%r6)
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 624(%r6)
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 628(%r6)
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 632(%r6)
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 636(%r6)
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 640(%r6)
	add %r7, %r7, %r8
	stw %r7, 640(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 644(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 644(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 648(%r6)
	add %r7, %r7, %r8
	stw %r7, 648(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 652(%r6)
	add %r7, %r7, %r8
	stw %r7, 652(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 656(%r6)
	add %r7, %r7, %r8
	stw %r7, 656(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 660(%r6)
	add %r7, %r7, %r8
	stw %r7, 660(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 664(%r6)
	add %r7, %r7, %r8
	stw %r7, 664(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 668(%r6)
	add %r7, %r7, %r8
	stw %r7, 668(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 616(%r6)
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 620(%r6)
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 624(%r6)
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 628(%r6)
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 632(%r6)
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 636(%r6)
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 640(%r6)
	add %r7, %r7, %r8
	stw %r7, 640(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 644(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 644(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 648(%r6)
	add %r7, %r7, %r8
	stw %r7, 648(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 652(%r6)
	add %r7, %r7, %r8
	stw %r7, 652(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 656(%r6)
	add %r7, %r7, %r8
	stw %r7, 656(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 660(%r6)
	add %r7, %r7, %r8
	stw %r7, 660(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 664(%r6)
	add %r7, %r7, %r8
	stw %r7, 664(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 668(%r6)
	add %r7, %r7, %r8
	stw %r7, 668(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 0
	lwz %r7, 392(%r6)
	lwz %r5, 560(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 672(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 396(%r6)
	lwz %r5, 564(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 676(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 400(%r6)
	lwz %r5, 568(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 680(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 404(%r6)
	lwz %r5, 572(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 684(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 408(%r6)
	lwz %r5, 576(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 688(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 412(%r6)
	lwz %r5, 580(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 692(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 416(%r6)
	lwz %r5, 584(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 696(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 420(%r6)
	lwz %r5, 588(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 700(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 424(%r6)
	lwz %r5, 592(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 704(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 428(%r6)
	lwz %r5, 596(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 708(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 432(%r6)
	lwz %r5, 600(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 712(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 436(%r6)
	lwz %r5, 604(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 716(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 440(%r6)
	lwz %r5, 608(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 720(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 444(%r6)
	lwz %r5, 612(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 724(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 672(%r6)
	add %r7, %r7, %r8
	stw %r7, 672(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 676(%r6)
	add %r7, %r7, %r8
	stw %r7, 676(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 680(%r6)
	add %r7, %r7, %r8
	stw %r7, 680(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 684(%r6)
	add %r7, %r7, %r8
	stw %r7, 684(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 688(%r6)
	add %r7, %r7, %r8
	stw %r7, 688(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 692(%r6)
	add %r7, %r7, %r8
	stw %r7, 692(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 696(%r6)
	add %r7, %r7, %r8
	stw %r7, 696(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 700(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 700(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 704(%r6)
	add %r7, %r7, %r8
	stw %r7, 704(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 708(%r6)
	add %r7, %r7, %r8
	stw %r7, 708(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 712(%r6)
	add %r7, %r7, %r8
	stw %r7, 712(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 716(%r6)
	add %r7, %r7, %r8
	stw %r7, 716(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 720(%r6)
	add %r7, %r7, %r8
	stw %r7, 720(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 724(%r6)
	add %r7, %r7, %r8
	stw %r7, 724(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 672(%r6)
	add %r7, %r7, %r8
	stw %r7, 672(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 676(%r6)
	add %r7, %r7, %r8
	stw %r7, 676(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 680(%r6)
	add %r7, %r7, %r8
	stw %r7, 680(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 684(%r6)
	add %r7, %r7, %r8
	stw %r7, 684(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 688(%r6)
	add %r7, %r7, %r8
	stw %r7, 688(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 692(%r6)
	add %r7, %r7, %r8
	stw %r7, 692(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 696(%r6)
	add %r7, %r7, %r8
	stw %r7, 696(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 700(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 700(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 704(%r6)
	add %r7, %r7, %r8
	stw %r7, 704(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 708(%r6)
	add %r7, %r7, %r8
	stw %r7, 708(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 712(%r6)
	add %r7, %r7, %r8
	stw %r7, 712(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 716(%r6)
	add %r7, %r7, %r8
	stw %r7, 716(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 720(%r6)
	add %r7, %r7, %r8
	stw %r7, 720(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 724(%r6)
	add %r7, %r7, %r8
	stw %r7, 724(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 0
	lwz %r7, 56(%r6)
	lwz %r5, 0(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 728(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	lwz %r5, 4(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 732(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 64(%r6)
	lwz %r5, 8(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 736(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 68(%r6)
	lwz %r5, 12(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 740(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 72(%r6)
	lwz %r5, 16(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 744(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 76(%r6)
	lwz %r5, 20(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 748(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 80(%r6)
	lwz %r5, 24(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 752(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 84(%r6)
	lwz %r5, 28(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 756(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 88(%r6)
	lwz %r5, 32(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 760(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 92(%r6)
	lwz %r5, 36(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 764(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 96(%r6)
	lwz %r5, 40(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 768(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 100(%r6)
	lwz %r5, 44(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 772(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 104(%r6)
	lwz %r5, 48(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 776(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 108(%r6)
	lwz %r5, 52(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 780(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 728(%r6)
	add %r7, %r7, %r8
	stw %r7, 728(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 732(%r6)
	add %r7, %r7, %r8
	stw %r7, 732(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 736(%r6)
	add %r7, %r7, %r8
	stw %r7, 736(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 740(%r6)
	add %r7, %r7, %r8
	stw %r7, 740(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 744(%r6)
	add %r7, %r7, %r8
	stw %r7, 744(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 748(%r6)
	add %r7, %r7, %r8
	stw %r7, 748(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 752(%r6)
	add %r7, %r7, %r8
	stw %r7, 752(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 756(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 756(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 760(%r6)
	add %r7, %r7, %r8
	stw %r7, 760(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 764(%r6)
	add %r7, %r7, %r8
	stw %r7, 764(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 768(%r6)
	add %r7, %r7, %r8
	stw %r7, 768(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 772(%r6)
	add %r7, %r7, %r8
	stw %r7, 772(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 776(%r6)
	add %r7, %r7, %r8
	stw %r7, 776(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 780(%r6)
	add %r7, %r7, %r8
	stw %r7, 780(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 728(%r6)
	add %r7, %r7, %r8
	stw %r7, 728(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 732(%r6)
	add %r7, %r7, %r8
	stw %r7, 732(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 736(%r6)
	add %r7, %r7, %r8
	stw %r7, 736(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 740(%r6)
	add %r7, %r7, %r8
	stw %r7, 740(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 744(%r6)
	add %r7, %r7, %r8
	stw %r7, 744(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 748(%r6)
	add %r7, %r7, %r8
	stw %r7, 748(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 752(%r6)
	add %r7, %r7, %r8
	stw %r7, 752(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 756(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 756(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 760(%r6)
	add %r7, %r7, %r8
	stw %r7, 760(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 764(%r6)
	add %r7, %r7, %r8
	stw %r7, 764(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 768(%r6)
	add %r7, %r7, %r8
	stw %r7, 768(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 772(%r6)
	add %r7, %r7, %r8
	stw %r7, 772(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 776(%r6)
	add %r7, %r7, %r8
	stw %r7, 776(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 780(%r6)
	add %r7, %r7, %r8
	stw %r7, 780(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 0
	lwz %r7, 168(%r6)
	lwz %r5, 224(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 784(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	lwz %r5, 228(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 788(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	lwz %r5, 232(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 792(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	lwz %r5, 236(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 796(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	lwz %r5, 240(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 800(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	lwz %r5, 244(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 804(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 192(%r6)
	lwz %r5, 248(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 808(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 196(%r6)
	lwz %r5, 252(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 812(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 200(%r6)
	lwz %r5, 256(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 816(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 204(%r6)
	lwz %r5, 260(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 820(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 208(%r6)
	lwz %r5, 264(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 824(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 212(%r6)
	lwz %r5, 268(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 828(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 216(%r6)
	lwz %r5, 272(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 832(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 220(%r6)
	lwz %r5, 276(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 836(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 784(%r6)
	add %r7, %r7, %r8
	stw %r7, 784(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 788(%r6)
	add %r7, %r7, %r8
	stw %r7, 788(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 792(%r6)
	add %r7, %r7, %r8
	stw %r7, 792(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 796(%r6)
	add %r7, %r7, %r8
	stw %r7, 796(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 800(%r6)
	add %r7, %r7, %r8
	stw %r7, 800(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 804(%r6)
	add %r7, %r7, %r8
	stw %r7, 804(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 808(%r6)
	add %r7, %r7, %r8
	stw %r7, 808(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 812(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 812(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 816(%r6)
	add %r7, %r7, %r8
	stw %r7, 816(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 820(%r6)
	add %r7, %r7, %r8
	stw %r7, 820(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 824(%r6)
	add %r7, %r7, %r8
	stw %r7, 824(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 828(%r6)
	add %r7, %r7, %r8
	stw %r7, 828(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 832(%r6)
	add %r7, %r7, %r8
	stw %r7, 832(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 836(%r6)
	add %r7, %r7, %r8
	stw %r7, 836(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 784(%r6)
	add %r7, %r7, %r8
	stw %r7, 784(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 788(%r6)
	add %r7, %r7, %r8
	stw %r7, 788(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 792(%r6)
	add %r7, %r7, %r8
	stw %r7, 792(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 796(%r6)
	add %r7, %r7, %r8
	stw %r7, 796(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 800(%r6)
	add %r7, %r7, %r8
	stw %r7, 800(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 804(%r6)
	add %r7, %r7, %r8
	stw %r7, 804(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 808(%r6)
	add %r7, %r7, %r8
	stw %r7, 808(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 812(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 812(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 816(%r6)
	add %r7, %r7, %r8
	stw %r7, 816(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 820(%r6)
	add %r7, %r7, %r8
	stw %r7, 820(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 824(%r6)
	add %r7, %r7, %r8
	stw %r7, 824(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 828(%r6)
	add %r7, %r7, %r8
	stw %r7, 828(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 832(%r6)
	add %r7, %r7, %r8
	stw %r7, 832(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 836(%r6)
	add %r7, %r7, %r8
	stw %r7, 836(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
25:
	ld %r4, 728(%r9)
	li %r8, 0
	ld %r5, 784(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 792(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 800(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 808(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 816(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 824(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 832(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 25b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 728(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 732(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 736(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 740(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 744(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 748(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 752(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 756(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 760(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 764(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 768(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 772(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 776(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 780(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 728(%r6)
	add %r7, %r7, %r8
	stw %r7, 728(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 732(%r6)
	add %r7, %r7, %r8
	stw %r7, 732(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 736(%r6)
	add %r7, %r7, %r8
	stw %r7, 736(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 740(%r6)
	add %r7, %r7, %r8
	stw %r7, 740(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 744(%r6)
	add %r7, %r7, %r8
	stw %r7, 744(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 748(%r6)
	add %r7, %r7, %r8
	stw %r7, 748(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 752(%r6)
	add %r7, %r7, %r8
	stw %r7, 752(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 756(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 756(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 760(%r6)
	add %r7, %r7, %r8
	stw %r7, 760(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 764(%r6)
	add %r7, %r7, %r8
	stw %r7, 764(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 768(%r6)
	add %r7, %r7, %r8
	stw %r7, 768(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 772(%r6)
	add %r7, %r7, %r8
	stw %r7, 772(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 776(%r6)
	add %r7, %r7, %r8
	stw %r7, 776(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 780(%r6)
	add %r7, %r7, %r8
	stw %r7, 780(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 728(%r6)
	add %r7, %r7, %r8
	stw %r7, 728(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 732(%r6)
	add %r7, %r7, %r8
	stw %r7, 732(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 736(%r6)
	add %r7, %r7, %r8
	stw %r7, 736(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 740(%r6)
	add %r7, %r7, %r8
	stw %r7, 740(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 744(%r6)
	add %r7, %r7, %r8
	stw %r7, 744(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 748(%r6)
	add %r7, %r7, %r8
	stw %r7, 748(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 752(%r6)
	add %r7, %r7, %r8
	stw %r7, 752(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 756(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 756(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 760(%r6)
	add %r7, %r7, %r8
	stw %r7, 760(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 764(%r6)
	add %r7, %r7, %r8
	stw %r7, 764(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 768(%r6)
	add %r7, %r7, %r8
	stw %r7, 768(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 772(%r6)
	add %r7, %r7, %r8
	stw %r7, 772(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 776(%r6)
	add %r7, %r7, %r8
	stw %r7, 776(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 780(%r6)
	add %r7, %r7, %r8
	stw %r7, 780(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
26:
	ld %r4, 112(%r9)
	li %r8, 0
	ld %r5, 616(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 624(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 632(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 640(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 648(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 656(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 664(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 26b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 784(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 788(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 792(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 796(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 800(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 804(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 808(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 812(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 816(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 820(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 824(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 828(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 832(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 836(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 784(%r6)
	add %r7, %r7, %r8
	stw %r7, 784(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 788(%r6)
	add %r7, %r7, %r8
	stw %r7, 788(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 792(%r6)
	add %r7, %r7, %r8
	stw %r7, 792(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 796(%r6)
	add %r7, %r7, %r8
	stw %r7, 796(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 800(%r6)
	add %r7, %r7, %r8
	stw %r7, 800(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 804(%r6)
	add %r7, %r7, %r8
	stw %r7, 804(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 808(%r6)
	add %r7, %r7, %r8
	stw %r7, 808(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 812(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 812(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 816(%r6)
	add %r7, %r7, %r8
	stw %r7, 816(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 820(%r6)
	add %r7, %r7, %r8
	stw %r7, 820(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 824(%r6)
	add %r7, %r7, %r8
	stw %r7, 824(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 828(%r6)
	add %r7, %r7, %r8
	stw %r7, 828(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 832(%r6)
	add %r7, %r7, %r8
	stw %r7, 832(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 836(%r6)
	add %r7, %r7, %r8
	stw %r7, 836(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 784(%r6)
	add %r7, %r7, %r8
	stw %r7, 784(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 788(%r6)
	add %r7, %r7, %r8
	stw %r7, 788(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 792(%r6)
	add %r7, %r7, %r8
	stw %r7, 792(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 796(%r6)
	add %r7, %r7, %r8
	stw %r7, 796(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 800(%r6)
	add %r7, %r7, %r8
	stw %r7, 800(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 804(%r6)
	add %r7, %r7, %r8
	stw %r7, 804(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 808(%r6)
	add %r7, %r7, %r8
	stw %r7, 808(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 812(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 812(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 816(%r6)
	add %r7, %r7, %r8
	stw %r7, 816(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 820(%r6)
	add %r7, %r7, %r8
	stw %r7, 820(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 824(%r6)
	add %r7, %r7, %r8
	stw %r7, 824(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 828(%r6)
	add %r7, %r7, %r8
	stw %r7, 828(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 832(%r6)
	add %r7, %r7, %r8
	stw %r7, 832(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 836(%r6)
	add %r7, %r7, %r8
	stw %r7, 836(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 34, 29
	lwz %r7, 728(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 448(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 728(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 732(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 452(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 732(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 736(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 456(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 736(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 740(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 460(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 740(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 744(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 464(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 744(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 748(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 468(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 748(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 752(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 472(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 752(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 756(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -8
	lwz %r5, 476(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 756(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 760(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 480(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 760(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 764(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 484(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 764(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 768(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 488(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 768(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 772(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 492(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 772(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 776(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 496(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 776(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 780(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 500(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 780(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 728(%r6)
	add %r7, %r7, %r8
	stw %r7, 728(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 732(%r6)
	add %r7, %r7, %r8
	stw %r7, 732(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 736(%r6)
	add %r7, %r7, %r8
	stw %r7, 736(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 740(%r6)
	add %r7, %r7, %r8
	stw %r7, 740(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 744(%r6)
	add %r7, %r7, %r8
	stw %r7, 744(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 748(%r6)
	add %r7, %r7, %r8
	stw %r7, 748(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 752(%r6)
	add %r7, %r7, %r8
	stw %r7, 752(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 756(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 756(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 760(%r6)
	add %r7, %r7, %r8
	stw %r7, 760(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 764(%r6)
	add %r7, %r7, %r8
	stw %r7, 764(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 768(%r6)
	add %r7, %r7, %r8
	stw %r7, 768(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 772(%r6)
	add %r7, %r7, %r8
	stw %r7, 772(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 776(%r6)
	add %r7, %r7, %r8
	stw %r7, 776(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 780(%r6)
	add %r7, %r7, %r8
	stw %r7, 780(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 728(%r6)
	add %r7, %r7, %r8
	stw %r7, 728(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 732(%r6)
	add %r7, %r7, %r8
	stw %r7, 732(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 736(%r6)
	add %r7, %r7, %r8
	stw %r7, 736(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 740(%r6)
	add %r7, %r7, %r8
	stw %r7, 740(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 744(%r6)
	add %r7, %r7, %r8
	stw %r7, 744(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 748(%r6)
	add %r7, %r7, %r8
	stw %r7, 748(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 752(%r6)
	add %r7, %r7, %r8
	stw %r7, 752(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 756(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 756(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 760(%r6)
	add %r7, %r7, %r8
	stw %r7, 760(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 764(%r6)
	add %r7, %r7, %r8
	stw %r7, 764(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 768(%r6)
	add %r7, %r7, %r8
	stw %r7, 768(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 772(%r6)
	add %r7, %r7, %r8
	stw %r7, 772(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 776(%r6)
	add %r7, %r7, %r8
	stw %r7, 776(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 780(%r6)
	add %r7, %r7, %r8
	stw %r7, 780(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 34, 29
	lwz %r7, 728(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 504(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 728(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 732(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 508(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 732(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 736(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 512(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 736(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 740(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 516(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 740(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 744(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 520(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 744(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 748(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 524(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 748(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 752(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 528(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 752(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 756(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -8
	lwz %r5, 532(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 756(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 760(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 536(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 760(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 764(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 540(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 764(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 768(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 544(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 768(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 772(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 548(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 772(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 776(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 552(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 776(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 780(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 556(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 780(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 728(%r6)
	add %r7, %r7, %r8
	stw %r7, 728(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 732(%r6)
	add %r7, %r7, %r8
	stw %r7, 732(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 736(%r6)
	add %r7, %r7, %r8
	stw %r7, 736(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 740(%r6)
	add %r7, %r7, %r8
	stw %r7, 740(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 744(%r6)
	add %r7, %r7, %r8
	stw %r7, 744(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 748(%r6)
	add %r7, %r7, %r8
	stw %r7, 748(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 752(%r6)
	add %r7, %r7, %r8
	stw %r7, 752(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 756(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 756(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 760(%r6)
	add %r7, %r7, %r8
	stw %r7, 760(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 764(%r6)
	add %r7, %r7, %r8
	stw %r7, 764(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 768(%r6)
	add %r7, %r7, %r8
	stw %r7, 768(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 772(%r6)
	add %r7, %r7, %r8
	stw %r7, 772(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 776(%r6)
	add %r7, %r7, %r8
	stw %r7, 776(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 780(%r6)
	add %r7, %r7, %r8
	stw %r7, 780(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 728(%r6)
	add %r7, %r7, %r8
	stw %r7, 728(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 732(%r6)
	add %r7, %r7, %r8
	stw %r7, 732(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 736(%r6)
	add %r7, %r7, %r8
	stw %r7, 736(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 740(%r6)
	add %r7, %r7, %r8
	stw %r7, 740(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 744(%r6)
	add %r7, %r7, %r8
	stw %r7, 744(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 748(%r6)
	add %r7, %r7, %r8
	stw %r7, 748(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 752(%r6)
	add %r7, %r7, %r8
	stw %r7, 752(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 756(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 756(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 760(%r6)
	add %r7, %r7, %r8
	stw %r7, 760(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 764(%r6)
	add %r7, %r7, %r8
	stw %r7, 764(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 768(%r6)
	add %r7, %r7, %r8
	stw %r7, 768(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 772(%r6)
	add %r7, %r7, %r8
	stw %r7, 772(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 776(%r6)
	add %r7, %r7, %r8
	stw %r7, 776(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 780(%r6)
	add %r7, %r7, %r8
	stw %r7, 780(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
27:
	ld %r4, 784(%r9)
	li %r8, 0
	ld %r5, 728(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 736(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 744(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 752(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 760(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 768(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 776(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 27b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 56(%r6)
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 64(%r6)
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 68(%r6)
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 72(%r6)
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 76(%r6)
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 80(%r6)
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 84(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 88(%r6)
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 92(%r6)
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 96(%r6)
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 100(%r6)
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 104(%r6)
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 108(%r6)
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 56(%r6)
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 64(%r6)
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 68(%r6)
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 72(%r6)
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 76(%r6)
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 80(%r6)
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 84(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 88(%r6)
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 92(%r6)
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 96(%r6)
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 100(%r6)
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 104(%r6)
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 108(%r6)
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
28:
	ld %r4, 112(%r9)
	li %r8, 0
	ld %r5, 672(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 680(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 688(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 696(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 704(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 712(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 720(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 28b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 784(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 788(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 792(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 796(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 800(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 804(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 808(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 812(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 816(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 820(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 824(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 828(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 832(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 836(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 784(%r6)
	add %r7, %r7, %r8
	stw %r7, 784(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 788(%r6)
	add %r7, %r7, %r8
	stw %r7, 788(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 792(%r6)
	add %r7, %r7, %r8
	stw %r7, 792(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 796(%r6)
	add %r7, %r7, %r8
	stw %r7, 796(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 800(%r6)
	add %r7, %r7, %r8
	stw %r7, 800(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 804(%r6)
	add %r7, %r7, %r8
	stw %r7, 804(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 808(%r6)
	add %r7, %r7, %r8
	stw %r7, 808(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 812(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 812(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 816(%r6)
	add %r7, %r7, %r8
	stw %r7, 816(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 820(%r6)
	add %r7, %r7, %r8
	stw %r7, 820(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 824(%r6)
	add %r7, %r7, %r8
	stw %r7, 824(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 828(%r6)
	add %r7, %r7, %r8
	stw %r7, 828(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 832(%r6)
	add %r7, %r7, %r8
	stw %r7, 832(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 836(%r6)
	add %r7, %r7, %r8
	stw %r7, 836(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 784(%r6)
	add %r7, %r7, %r8
	stw %r7, 784(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 788(%r6)
	add %r7, %r7, %r8
	stw %r7, 788(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 792(%r6)
	add %r7, %r7, %r8
	stw %r7, 792(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 796(%r6)
	add %r7, %r7, %r8
	stw %r7, 796(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 800(%r6)
	add %r7, %r7, %r8
	stw %r7, 800(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 804(%r6)
	add %r7, %r7, %r8
	stw %r7, 804(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 808(%r6)
	add %r7, %r7, %r8
	stw %r7, 808(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 812(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 812(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 816(%r6)
	add %r7, %r7, %r8
	stw %r7, 816(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 820(%r6)
	add %r7, %r7, %r8
	stw %r7, 820(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 824(%r6)
	add %r7, %r7, %r8
	stw %r7, 824(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 828(%r6)
	add %r7, %r7, %r8
	stw %r7, 828(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 832(%r6)
	add %r7, %r7, %r8
	stw %r7, 832(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 836(%r6)
	add %r7, %r7, %r8
	stw %r7, 836(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 34, 29
	lwz %r7, 504(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 448(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 728(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 452(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 732(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 512(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 456(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 736(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 516(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 460(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 740(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 520(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 464(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 744(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 524(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 468(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 748(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 528(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 472(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 752(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 532(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -8
	lwz %r5, 476(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 756(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 536(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 480(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 760(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 484(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 764(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 544(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 488(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 768(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 492(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 772(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 496(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 776(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 500(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 780(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 728(%r6)
	add %r7, %r7, %r8
	stw %r7, 728(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 732(%r6)
	add %r7, %r7, %r8
	stw %r7, 732(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 736(%r6)
	add %r7, %r7, %r8
	stw %r7, 736(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 740(%r6)
	add %r7, %r7, %r8
	stw %r7, 740(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 744(%r6)
	add %r7, %r7, %r8
	stw %r7, 744(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 748(%r6)
	add %r7, %r7, %r8
	stw %r7, 748(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 752(%r6)
	add %r7, %r7, %r8
	stw %r7, 752(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 756(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 756(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 760(%r6)
	add %r7, %r7, %r8
	stw %r7, 760(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 764(%r6)
	add %r7, %r7, %r8
	stw %r7, 764(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 768(%r6)
	add %r7, %r7, %r8
	stw %r7, 768(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 772(%r6)
	add %r7, %r7, %r8
	stw %r7, 772(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 776(%r6)
	add %r7, %r7, %r8
	stw %r7, 776(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 780(%r6)
	add %r7, %r7, %r8
	stw %r7, 780(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 728(%r6)
	add %r7, %r7, %r8
	stw %r7, 728(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 732(%r6)
	add %r7, %r7, %r8
	stw %r7, 732(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 736(%r6)
	add %r7, %r7, %r8
	stw %r7, 736(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 740(%r6)
	add %r7, %r7, %r8
	stw %r7, 740(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 744(%r6)
	add %r7, %r7, %r8
	stw %r7, 744(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 748(%r6)
	add %r7, %r7, %r8
	stw %r7, 748(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 752(%r6)
	add %r7, %r7, %r8
	stw %r7, 752(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 756(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 756(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 760(%r6)
	add %r7, %r7, %r8
	stw %r7, 760(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 764(%r6)
	add %r7, %r7, %r8
	stw %r7, 764(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 768(%r6)
	add %r7, %r7, %r8
	stw %r7, 768(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 772(%r6)
	add %r7, %r7, %r8
	stw %r7, 772(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 776(%r6)
	add %r7, %r7, %r8
	stw %r7, 776(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 780(%r6)
	add %r7, %r7, %r8
	stw %r7, 780(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
29:
	ld %r4, 784(%r9)
	li %r8, 0
	ld %r5, 728(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 736(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 744(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 752(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 760(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 768(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 776(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 29b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 0(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 4(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 8(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 12(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 16(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 20(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 24(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 28(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 32(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 36(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 40(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 44(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 48(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 52(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 0(%r6)
	add %r7, %r7, %r8
	stw %r7, 0(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	add %r7, %r7, %r8
	stw %r7, 4(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	add %r7, %r7, %r8
	stw %r7, 8(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	add %r7, %r7, %r8
	stw %r7, 12(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	add %r7, %r7, %r8
	stw %r7, 16(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	add %r7, %r7, %r8
	stw %r7, 20(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	add %r7, %r7, %r8
	stw %r7, 24(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 28(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	add %r7, %r7, %r8
	stw %r7, 32(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	add %r7, %r7, %r8
	stw %r7, 36(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	add %r7, %r7, %r8
	stw %r7, 40(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	add %r7, %r7, %r8
	stw %r7, 44(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	add %r7, %r7, %r8
	stw %r7, 48(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	add %r7, %r7, %r8
	stw %r7, 52(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 0(%r6)
	add %r7, %r7, %r8
	stw %r7, 0(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	add %r7, %r7, %r8
	stw %r7, 4(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	add %r7, %r7, %r8
	stw %r7, 8(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	add %r7, %r7, %r8
	stw %r7, 12(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	add %r7, %r7, %r8
	stw %r7, 16(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	add %r7, %r7, %r8
	stw %r7, 20(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	add %r7, %r7, %r8
	stw %r7, 24(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 28(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	add %r7, %r7, %r8
	stw %r7, 32(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	add %r7, %r7, %r8
	stw %r7, 36(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	add %r7, %r7, %r8
	stw %r7, 40(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	add %r7, %r7, %r8
	stw %r7, 44(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	add %r7, %r7, %r8
	stw %r7, 48(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	add %r7, %r7, %r8
	stw %r7, 52(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
210:
	ld %r4, 616(%r9)
	li %r8, 0
	ld %r5, 672(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 680(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 688(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 696(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 704(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 712(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 720(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 210b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 112(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 116(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 120(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 124(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 132(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 136(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 140(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 144(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 148(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 152(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 156(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 112(%r6)
	add %r7, %r7, %r8
	stw %r7, 112(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	add %r7, %r7, %r8
	stw %r7, 116(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	add %r7, %r7, %r8
	stw %r7, 120(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	add %r7, %r7, %r8
	stw %r7, 124(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 128(%r6)
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	add %r7, %r7, %r8
	stw %r7, 132(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	add %r7, %r7, %r8
	stw %r7, 136(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 140(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	add %r7, %r7, %r8
	stw %r7, 144(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	add %r7, %r7, %r8
	stw %r7, 148(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	add %r7, %r7, %r8
	stw %r7, 152(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	add %r7, %r7, %r8
	stw %r7, 156(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 160(%r6)
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 112(%r6)
	add %r7, %r7, %r8
	stw %r7, 112(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	add %r7, %r7, %r8
	stw %r7, 116(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	add %r7, %r7, %r8
	stw %r7, 120(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	add %r7, %r7, %r8
	stw %r7, 124(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 128(%r6)
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	add %r7, %r7, %r8
	stw %r7, 132(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	add %r7, %r7, %r8
	stw %r7, 136(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 140(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	add %r7, %r7, %r8
	stw %r7, 144(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	add %r7, %r7, %r8
	stw %r7, 148(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	add %r7, %r7, %r8
	stw %r7, 152(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	add %r7, %r7, %r8
	stw %r7, 156(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 160(%r6)
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	blr
