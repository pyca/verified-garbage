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
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 392(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 400(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 408(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 416(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 424(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 432(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 440(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 392(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 392(%r6)
	ld %r7, 400(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 400(%r6)
	ld %r7, 408(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 408(%r6)
	ld %r7, 416(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 416(%r6)
	ld %r7, 424(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 424(%r6)
	ld %r7, 432(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 432(%r6)
	ld %r7, 440(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 440(%r6)
	addze %r4, %r4
	ld %r7, 416(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 416(%r6)
	ld %r7, 424(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 424(%r6)
	ld %r7, 432(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 432(%r6)
	ld %r7, 440(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 440(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 392(%r6)
	addc %r7, %r7, %r4
	std %r7, 392(%r6)
	ld %r7, 400(%r6)
	adde %r7, %r7, %r8
	std %r7, 400(%r6)
	ld %r7, 408(%r6)
	adde %r7, %r7, %r8
	std %r7, 408(%r6)
	ld %r7, 416(%r6)
	adde %r7, %r7, %r5
	std %r7, 416(%r6)
	ld %r7, 424(%r6)
	adde %r7, %r7, %r8
	std %r7, 424(%r6)
	ld %r7, 432(%r6)
	adde %r7, %r7, %r8
	std %r7, 432(%r6)
	ld %r7, 440(%r6)
	adde %r7, %r7, %r8
	std %r7, 440(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 392(%r6)
	addc %r7, %r7, %r4
	std %r7, 392(%r6)
	ld %r7, 400(%r6)
	adde %r7, %r7, %r8
	std %r7, 400(%r6)
	ld %r7, 408(%r6)
	adde %r7, %r7, %r8
	std %r7, 408(%r6)
	ld %r7, 416(%r6)
	adde %r7, %r7, %r5
	std %r7, 416(%r6)
	ld %r7, 424(%r6)
	adde %r7, %r7, %r8
	std %r7, 424(%r6)
	ld %r7, 432(%r6)
	adde %r7, %r7, %r8
	std %r7, 432(%r6)
	ld %r7, 440(%r6)
	adde %r7, %r7, %r8
	std %r7, 440(%r6)
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
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 448(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 456(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 464(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 472(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 480(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 488(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 496(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 448(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 448(%r6)
	ld %r7, 456(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 456(%r6)
	ld %r7, 464(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 464(%r6)
	ld %r7, 472(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 472(%r6)
	ld %r7, 480(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 480(%r6)
	ld %r7, 488(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 488(%r6)
	ld %r7, 496(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 496(%r6)
	addze %r4, %r4
	ld %r7, 472(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 472(%r6)
	ld %r7, 480(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 480(%r6)
	ld %r7, 488(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 488(%r6)
	ld %r7, 496(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 496(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 448(%r6)
	addc %r7, %r7, %r4
	std %r7, 448(%r6)
	ld %r7, 456(%r6)
	adde %r7, %r7, %r8
	std %r7, 456(%r6)
	ld %r7, 464(%r6)
	adde %r7, %r7, %r8
	std %r7, 464(%r6)
	ld %r7, 472(%r6)
	adde %r7, %r7, %r5
	std %r7, 472(%r6)
	ld %r7, 480(%r6)
	adde %r7, %r7, %r8
	std %r7, 480(%r6)
	ld %r7, 488(%r6)
	adde %r7, %r7, %r8
	std %r7, 488(%r6)
	ld %r7, 496(%r6)
	adde %r7, %r7, %r8
	std %r7, 496(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 448(%r6)
	addc %r7, %r7, %r4
	std %r7, 448(%r6)
	ld %r7, 456(%r6)
	adde %r7, %r7, %r8
	std %r7, 456(%r6)
	ld %r7, 464(%r6)
	adde %r7, %r7, %r8
	std %r7, 464(%r6)
	ld %r7, 472(%r6)
	adde %r7, %r7, %r5
	std %r7, 472(%r6)
	ld %r7, 480(%r6)
	adde %r7, %r7, %r8
	std %r7, 480(%r6)
	ld %r7, 488(%r6)
	adde %r7, %r7, %r8
	std %r7, 488(%r6)
	ld %r7, 496(%r6)
	adde %r7, %r7, %r8
	std %r7, 496(%r6)
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
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 504(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 512(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 520(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 528(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 536(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 544(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 552(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 504(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 504(%r6)
	ld %r7, 512(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 512(%r6)
	ld %r7, 520(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 520(%r6)
	ld %r7, 528(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 528(%r6)
	ld %r7, 536(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 536(%r6)
	ld %r7, 544(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 544(%r6)
	ld %r7, 552(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 552(%r6)
	addze %r4, %r4
	ld %r7, 528(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 528(%r6)
	ld %r7, 536(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 536(%r6)
	ld %r7, 544(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 544(%r6)
	ld %r7, 552(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 552(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 504(%r6)
	addc %r7, %r7, %r4
	std %r7, 504(%r6)
	ld %r7, 512(%r6)
	adde %r7, %r7, %r8
	std %r7, 512(%r6)
	ld %r7, 520(%r6)
	adde %r7, %r7, %r8
	std %r7, 520(%r6)
	ld %r7, 528(%r6)
	adde %r7, %r7, %r5
	std %r7, 528(%r6)
	ld %r7, 536(%r6)
	adde %r7, %r7, %r8
	std %r7, 536(%r6)
	ld %r7, 544(%r6)
	adde %r7, %r7, %r8
	std %r7, 544(%r6)
	ld %r7, 552(%r6)
	adde %r7, %r7, %r8
	std %r7, 552(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 504(%r6)
	addc %r7, %r7, %r4
	std %r7, 504(%r6)
	ld %r7, 512(%r6)
	adde %r7, %r7, %r8
	std %r7, 512(%r6)
	ld %r7, 520(%r6)
	adde %r7, %r7, %r8
	std %r7, 520(%r6)
	ld %r7, 528(%r6)
	adde %r7, %r7, %r5
	std %r7, 528(%r6)
	ld %r7, 536(%r6)
	adde %r7, %r7, %r8
	std %r7, 536(%r6)
	ld %r7, 544(%r6)
	adde %r7, %r7, %r8
	std %r7, 544(%r6)
	ld %r7, 552(%r6)
	adde %r7, %r7, %r8
	std %r7, 552(%r6)
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
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 560(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 568(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 576(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 584(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 592(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 600(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 608(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 560(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 560(%r6)
	ld %r7, 568(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 568(%r6)
	ld %r7, 576(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 576(%r6)
	ld %r7, 584(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 584(%r6)
	ld %r7, 592(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 592(%r6)
	ld %r7, 600(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 600(%r6)
	ld %r7, 608(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 608(%r6)
	addze %r4, %r4
	ld %r7, 584(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 584(%r6)
	ld %r7, 592(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 592(%r6)
	ld %r7, 600(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 600(%r6)
	ld %r7, 608(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 608(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 560(%r6)
	addc %r7, %r7, %r4
	std %r7, 560(%r6)
	ld %r7, 568(%r6)
	adde %r7, %r7, %r8
	std %r7, 568(%r6)
	ld %r7, 576(%r6)
	adde %r7, %r7, %r8
	std %r7, 576(%r6)
	ld %r7, 584(%r6)
	adde %r7, %r7, %r5
	std %r7, 584(%r6)
	ld %r7, 592(%r6)
	adde %r7, %r7, %r8
	std %r7, 592(%r6)
	ld %r7, 600(%r6)
	adde %r7, %r7, %r8
	std %r7, 600(%r6)
	ld %r7, 608(%r6)
	adde %r7, %r7, %r8
	std %r7, 608(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 560(%r6)
	addc %r7, %r7, %r4
	std %r7, 560(%r6)
	ld %r7, 568(%r6)
	adde %r7, %r7, %r8
	std %r7, 568(%r6)
	ld %r7, 576(%r6)
	adde %r7, %r7, %r8
	std %r7, 576(%r6)
	ld %r7, 584(%r6)
	adde %r7, %r7, %r5
	std %r7, 584(%r6)
	ld %r7, 592(%r6)
	adde %r7, %r7, %r8
	std %r7, 592(%r6)
	ld %r7, 600(%r6)
	adde %r7, %r7, %r8
	std %r7, 600(%r6)
	ld %r7, 608(%r6)
	adde %r7, %r7, %r8
	std %r7, 608(%r6)
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
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 560(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 568(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 576(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 584(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 592(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 600(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 608(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 560(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 560(%r6)
	ld %r7, 568(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 568(%r6)
	ld %r7, 576(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 576(%r6)
	ld %r7, 584(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 584(%r6)
	ld %r7, 592(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 592(%r6)
	ld %r7, 600(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 600(%r6)
	ld %r7, 608(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 608(%r6)
	addze %r4, %r4
	ld %r7, 584(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 584(%r6)
	ld %r7, 592(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 592(%r6)
	ld %r7, 600(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 600(%r6)
	ld %r7, 608(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 608(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 560(%r6)
	addc %r7, %r7, %r4
	std %r7, 560(%r6)
	ld %r7, 568(%r6)
	adde %r7, %r7, %r8
	std %r7, 568(%r6)
	ld %r7, 576(%r6)
	adde %r7, %r7, %r8
	std %r7, 576(%r6)
	ld %r7, 584(%r6)
	adde %r7, %r7, %r5
	std %r7, 584(%r6)
	ld %r7, 592(%r6)
	adde %r7, %r7, %r8
	std %r7, 592(%r6)
	ld %r7, 600(%r6)
	adde %r7, %r7, %r8
	std %r7, 600(%r6)
	ld %r7, 608(%r6)
	adde %r7, %r7, %r8
	std %r7, 608(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 560(%r6)
	addc %r7, %r7, %r4
	std %r7, 560(%r6)
	ld %r7, 568(%r6)
	adde %r7, %r7, %r8
	std %r7, 568(%r6)
	ld %r7, 576(%r6)
	adde %r7, %r7, %r8
	std %r7, 576(%r6)
	ld %r7, 584(%r6)
	adde %r7, %r7, %r5
	std %r7, 584(%r6)
	ld %r7, 592(%r6)
	adde %r7, %r7, %r8
	std %r7, 592(%r6)
	ld %r7, 600(%r6)
	adde %r7, %r7, %r8
	std %r7, 600(%r6)
	ld %r7, 608(%r6)
	adde %r7, %r7, %r8
	std %r7, 608(%r6)
	ld %r7, 392(%r6)
	ld %r8, 560(%r6)
	subfc %r7, %r8, %r7
	std %r7, 616(%r6)
	ld %r7, 400(%r6)
	ld %r8, 568(%r6)
	subfe %r7, %r8, %r7
	std %r7, 624(%r6)
	ld %r7, 408(%r6)
	ld %r8, 576(%r6)
	subfe %r7, %r8, %r7
	std %r7, 632(%r6)
	ld %r7, 416(%r6)
	ld %r8, 584(%r6)
	subfe %r7, %r8, %r7
	std %r7, 640(%r6)
	ld %r7, 424(%r6)
	ld %r8, 592(%r6)
	subfe %r7, %r8, %r7
	std %r7, 648(%r6)
	ld %r7, 432(%r6)
	ld %r8, 600(%r6)
	subfe %r7, %r8, %r7
	std %r7, 656(%r6)
	ld %r7, 440(%r6)
	ld %r8, 608(%r6)
	subfe %r7, %r8, %r7
	std %r7, 664(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 616(%r6)
	subfc %r7, %r4, %r7
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	subfe %r7, %r8, %r7
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	subfe %r7, %r8, %r7
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	subfe %r7, %r5, %r7
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	subfe %r7, %r8, %r7
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	subfe %r7, %r8, %r7
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	subfe %r7, %r8, %r7
	std %r7, 664(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 616(%r6)
	subfc %r7, %r4, %r7
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	subfe %r7, %r8, %r7
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	subfe %r7, %r8, %r7
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	subfe %r7, %r5, %r7
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	subfe %r7, %r8, %r7
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	subfe %r7, %r8, %r7
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	subfe %r7, %r8, %r7
	std %r7, 664(%r6)
	ld %r7, 392(%r6)
	ld %r8, 560(%r6)
	addc %r7, %r7, %r8
	std %r7, 672(%r6)
	ld %r7, 400(%r6)
	ld %r8, 568(%r6)
	adde %r7, %r7, %r8
	std %r7, 680(%r6)
	ld %r7, 408(%r6)
	ld %r8, 576(%r6)
	adde %r7, %r7, %r8
	std %r7, 688(%r6)
	ld %r7, 416(%r6)
	ld %r8, 584(%r6)
	adde %r7, %r7, %r8
	std %r7, 696(%r6)
	ld %r7, 424(%r6)
	ld %r8, 592(%r6)
	adde %r7, %r7, %r8
	std %r7, 704(%r6)
	ld %r7, 432(%r6)
	ld %r8, 600(%r6)
	adde %r7, %r7, %r8
	std %r7, 712(%r6)
	ld %r7, 440(%r6)
	ld %r8, 608(%r6)
	adde %r7, %r7, %r8
	std %r7, 720(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 672(%r6)
	addc %r7, %r7, %r4
	std %r7, 672(%r6)
	ld %r7, 680(%r6)
	adde %r7, %r7, %r8
	std %r7, 680(%r6)
	ld %r7, 688(%r6)
	adde %r7, %r7, %r8
	std %r7, 688(%r6)
	ld %r7, 696(%r6)
	adde %r7, %r7, %r5
	std %r7, 696(%r6)
	ld %r7, 704(%r6)
	adde %r7, %r7, %r8
	std %r7, 704(%r6)
	ld %r7, 712(%r6)
	adde %r7, %r7, %r8
	std %r7, 712(%r6)
	ld %r7, 720(%r6)
	adde %r7, %r7, %r8
	std %r7, 720(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 672(%r6)
	addc %r7, %r7, %r4
	std %r7, 672(%r6)
	ld %r7, 680(%r6)
	adde %r7, %r7, %r8
	std %r7, 680(%r6)
	ld %r7, 688(%r6)
	adde %r7, %r7, %r8
	std %r7, 688(%r6)
	ld %r7, 696(%r6)
	adde %r7, %r7, %r5
	std %r7, 696(%r6)
	ld %r7, 704(%r6)
	adde %r7, %r7, %r8
	std %r7, 704(%r6)
	ld %r7, 712(%r6)
	adde %r7, %r7, %r8
	std %r7, 712(%r6)
	ld %r7, 720(%r6)
	adde %r7, %r7, %r8
	std %r7, 720(%r6)
	ld %r7, 56(%r6)
	ld %r8, 0(%r6)
	addc %r7, %r7, %r8
	std %r7, 728(%r6)
	ld %r7, 64(%r6)
	ld %r8, 8(%r6)
	adde %r7, %r7, %r8
	std %r7, 736(%r6)
	ld %r7, 72(%r6)
	ld %r8, 16(%r6)
	adde %r7, %r7, %r8
	std %r7, 744(%r6)
	ld %r7, 80(%r6)
	ld %r8, 24(%r6)
	adde %r7, %r7, %r8
	std %r7, 752(%r6)
	ld %r7, 88(%r6)
	ld %r8, 32(%r6)
	adde %r7, %r7, %r8
	std %r7, 760(%r6)
	ld %r7, 96(%r6)
	ld %r8, 40(%r6)
	adde %r7, %r7, %r8
	std %r7, 768(%r6)
	ld %r7, 104(%r6)
	ld %r8, 48(%r6)
	adde %r7, %r7, %r8
	std %r7, 776(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 728(%r6)
	addc %r7, %r7, %r4
	std %r7, 728(%r6)
	ld %r7, 736(%r6)
	adde %r7, %r7, %r8
	std %r7, 736(%r6)
	ld %r7, 744(%r6)
	adde %r7, %r7, %r8
	std %r7, 744(%r6)
	ld %r7, 752(%r6)
	adde %r7, %r7, %r5
	std %r7, 752(%r6)
	ld %r7, 760(%r6)
	adde %r7, %r7, %r8
	std %r7, 760(%r6)
	ld %r7, 768(%r6)
	adde %r7, %r7, %r8
	std %r7, 768(%r6)
	ld %r7, 776(%r6)
	adde %r7, %r7, %r8
	std %r7, 776(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 728(%r6)
	addc %r7, %r7, %r4
	std %r7, 728(%r6)
	ld %r7, 736(%r6)
	adde %r7, %r7, %r8
	std %r7, 736(%r6)
	ld %r7, 744(%r6)
	adde %r7, %r7, %r8
	std %r7, 744(%r6)
	ld %r7, 752(%r6)
	adde %r7, %r7, %r5
	std %r7, 752(%r6)
	ld %r7, 760(%r6)
	adde %r7, %r7, %r8
	std %r7, 760(%r6)
	ld %r7, 768(%r6)
	adde %r7, %r7, %r8
	std %r7, 768(%r6)
	ld %r7, 776(%r6)
	adde %r7, %r7, %r8
	std %r7, 776(%r6)
	ld %r7, 168(%r6)
	ld %r8, 224(%r6)
	addc %r7, %r7, %r8
	std %r7, 784(%r6)
	ld %r7, 176(%r6)
	ld %r8, 232(%r6)
	adde %r7, %r7, %r8
	std %r7, 792(%r6)
	ld %r7, 184(%r6)
	ld %r8, 240(%r6)
	adde %r7, %r7, %r8
	std %r7, 800(%r6)
	ld %r7, 192(%r6)
	ld %r8, 248(%r6)
	adde %r7, %r7, %r8
	std %r7, 808(%r6)
	ld %r7, 200(%r6)
	ld %r8, 256(%r6)
	adde %r7, %r7, %r8
	std %r7, 816(%r6)
	ld %r7, 208(%r6)
	ld %r8, 264(%r6)
	adde %r7, %r7, %r8
	std %r7, 824(%r6)
	ld %r7, 216(%r6)
	ld %r8, 272(%r6)
	adde %r7, %r7, %r8
	std %r7, 832(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 784(%r6)
	addc %r7, %r7, %r4
	std %r7, 784(%r6)
	ld %r7, 792(%r6)
	adde %r7, %r7, %r8
	std %r7, 792(%r6)
	ld %r7, 800(%r6)
	adde %r7, %r7, %r8
	std %r7, 800(%r6)
	ld %r7, 808(%r6)
	adde %r7, %r7, %r5
	std %r7, 808(%r6)
	ld %r7, 816(%r6)
	adde %r7, %r7, %r8
	std %r7, 816(%r6)
	ld %r7, 824(%r6)
	adde %r7, %r7, %r8
	std %r7, 824(%r6)
	ld %r7, 832(%r6)
	adde %r7, %r7, %r8
	std %r7, 832(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 784(%r6)
	addc %r7, %r7, %r4
	std %r7, 784(%r6)
	ld %r7, 792(%r6)
	adde %r7, %r7, %r8
	std %r7, 792(%r6)
	ld %r7, 800(%r6)
	adde %r7, %r7, %r8
	std %r7, 800(%r6)
	ld %r7, 808(%r6)
	adde %r7, %r7, %r5
	std %r7, 808(%r6)
	ld %r7, 816(%r6)
	adde %r7, %r7, %r8
	std %r7, 816(%r6)
	ld %r7, 824(%r6)
	adde %r7, %r7, %r8
	std %r7, 824(%r6)
	ld %r7, 832(%r6)
	adde %r7, %r7, %r8
	std %r7, 832(%r6)
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
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 728(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 736(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 744(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 752(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 760(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 768(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 776(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 728(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 728(%r6)
	ld %r7, 736(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 736(%r6)
	ld %r7, 744(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 744(%r6)
	ld %r7, 752(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 752(%r6)
	ld %r7, 760(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 760(%r6)
	ld %r7, 768(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 768(%r6)
	ld %r7, 776(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 776(%r6)
	addze %r4, %r4
	ld %r7, 752(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 752(%r6)
	ld %r7, 760(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 760(%r6)
	ld %r7, 768(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 768(%r6)
	ld %r7, 776(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 776(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 728(%r6)
	addc %r7, %r7, %r4
	std %r7, 728(%r6)
	ld %r7, 736(%r6)
	adde %r7, %r7, %r8
	std %r7, 736(%r6)
	ld %r7, 744(%r6)
	adde %r7, %r7, %r8
	std %r7, 744(%r6)
	ld %r7, 752(%r6)
	adde %r7, %r7, %r5
	std %r7, 752(%r6)
	ld %r7, 760(%r6)
	adde %r7, %r7, %r8
	std %r7, 760(%r6)
	ld %r7, 768(%r6)
	adde %r7, %r7, %r8
	std %r7, 768(%r6)
	ld %r7, 776(%r6)
	adde %r7, %r7, %r8
	std %r7, 776(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 728(%r6)
	addc %r7, %r7, %r4
	std %r7, 728(%r6)
	ld %r7, 736(%r6)
	adde %r7, %r7, %r8
	std %r7, 736(%r6)
	ld %r7, 744(%r6)
	adde %r7, %r7, %r8
	std %r7, 744(%r6)
	ld %r7, 752(%r6)
	adde %r7, %r7, %r5
	std %r7, 752(%r6)
	ld %r7, 760(%r6)
	adde %r7, %r7, %r8
	std %r7, 760(%r6)
	ld %r7, 768(%r6)
	adde %r7, %r7, %r8
	std %r7, 768(%r6)
	ld %r7, 776(%r6)
	adde %r7, %r7, %r8
	std %r7, 776(%r6)
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
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 784(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 792(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 800(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 808(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 816(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 824(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 832(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 784(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 784(%r6)
	ld %r7, 792(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 792(%r6)
	ld %r7, 800(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 800(%r6)
	ld %r7, 808(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 808(%r6)
	ld %r7, 816(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 816(%r6)
	ld %r7, 824(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 824(%r6)
	ld %r7, 832(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 832(%r6)
	addze %r4, %r4
	ld %r7, 808(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 808(%r6)
	ld %r7, 816(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 816(%r6)
	ld %r7, 824(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 824(%r6)
	ld %r7, 832(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 832(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 784(%r6)
	addc %r7, %r7, %r4
	std %r7, 784(%r6)
	ld %r7, 792(%r6)
	adde %r7, %r7, %r8
	std %r7, 792(%r6)
	ld %r7, 800(%r6)
	adde %r7, %r7, %r8
	std %r7, 800(%r6)
	ld %r7, 808(%r6)
	adde %r7, %r7, %r5
	std %r7, 808(%r6)
	ld %r7, 816(%r6)
	adde %r7, %r7, %r8
	std %r7, 816(%r6)
	ld %r7, 824(%r6)
	adde %r7, %r7, %r8
	std %r7, 824(%r6)
	ld %r7, 832(%r6)
	adde %r7, %r7, %r8
	std %r7, 832(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 784(%r6)
	addc %r7, %r7, %r4
	std %r7, 784(%r6)
	ld %r7, 792(%r6)
	adde %r7, %r7, %r8
	std %r7, 792(%r6)
	ld %r7, 800(%r6)
	adde %r7, %r7, %r8
	std %r7, 800(%r6)
	ld %r7, 808(%r6)
	adde %r7, %r7, %r5
	std %r7, 808(%r6)
	ld %r7, 816(%r6)
	adde %r7, %r7, %r8
	std %r7, 816(%r6)
	ld %r7, 824(%r6)
	adde %r7, %r7, %r8
	std %r7, 824(%r6)
	ld %r7, 832(%r6)
	adde %r7, %r7, %r8
	std %r7, 832(%r6)
	ld %r7, 728(%r6)
	ld %r8, 448(%r6)
	subfc %r7, %r8, %r7
	std %r7, 728(%r6)
	ld %r7, 736(%r6)
	ld %r8, 456(%r6)
	subfe %r7, %r8, %r7
	std %r7, 736(%r6)
	ld %r7, 744(%r6)
	ld %r8, 464(%r6)
	subfe %r7, %r8, %r7
	std %r7, 744(%r6)
	ld %r7, 752(%r6)
	ld %r8, 472(%r6)
	subfe %r7, %r8, %r7
	std %r7, 752(%r6)
	ld %r7, 760(%r6)
	ld %r8, 480(%r6)
	subfe %r7, %r8, %r7
	std %r7, 760(%r6)
	ld %r7, 768(%r6)
	ld %r8, 488(%r6)
	subfe %r7, %r8, %r7
	std %r7, 768(%r6)
	ld %r7, 776(%r6)
	ld %r8, 496(%r6)
	subfe %r7, %r8, %r7
	std %r7, 776(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 728(%r6)
	subfc %r7, %r4, %r7
	std %r7, 728(%r6)
	ld %r7, 736(%r6)
	subfe %r7, %r8, %r7
	std %r7, 736(%r6)
	ld %r7, 744(%r6)
	subfe %r7, %r8, %r7
	std %r7, 744(%r6)
	ld %r7, 752(%r6)
	subfe %r7, %r5, %r7
	std %r7, 752(%r6)
	ld %r7, 760(%r6)
	subfe %r7, %r8, %r7
	std %r7, 760(%r6)
	ld %r7, 768(%r6)
	subfe %r7, %r8, %r7
	std %r7, 768(%r6)
	ld %r7, 776(%r6)
	subfe %r7, %r8, %r7
	std %r7, 776(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 728(%r6)
	subfc %r7, %r4, %r7
	std %r7, 728(%r6)
	ld %r7, 736(%r6)
	subfe %r7, %r8, %r7
	std %r7, 736(%r6)
	ld %r7, 744(%r6)
	subfe %r7, %r8, %r7
	std %r7, 744(%r6)
	ld %r7, 752(%r6)
	subfe %r7, %r5, %r7
	std %r7, 752(%r6)
	ld %r7, 760(%r6)
	subfe %r7, %r8, %r7
	std %r7, 760(%r6)
	ld %r7, 768(%r6)
	subfe %r7, %r8, %r7
	std %r7, 768(%r6)
	ld %r7, 776(%r6)
	subfe %r7, %r8, %r7
	std %r7, 776(%r6)
	ld %r7, 728(%r6)
	ld %r8, 504(%r6)
	subfc %r7, %r8, %r7
	std %r7, 728(%r6)
	ld %r7, 736(%r6)
	ld %r8, 512(%r6)
	subfe %r7, %r8, %r7
	std %r7, 736(%r6)
	ld %r7, 744(%r6)
	ld %r8, 520(%r6)
	subfe %r7, %r8, %r7
	std %r7, 744(%r6)
	ld %r7, 752(%r6)
	ld %r8, 528(%r6)
	subfe %r7, %r8, %r7
	std %r7, 752(%r6)
	ld %r7, 760(%r6)
	ld %r8, 536(%r6)
	subfe %r7, %r8, %r7
	std %r7, 760(%r6)
	ld %r7, 768(%r6)
	ld %r8, 544(%r6)
	subfe %r7, %r8, %r7
	std %r7, 768(%r6)
	ld %r7, 776(%r6)
	ld %r8, 552(%r6)
	subfe %r7, %r8, %r7
	std %r7, 776(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 728(%r6)
	subfc %r7, %r4, %r7
	std %r7, 728(%r6)
	ld %r7, 736(%r6)
	subfe %r7, %r8, %r7
	std %r7, 736(%r6)
	ld %r7, 744(%r6)
	subfe %r7, %r8, %r7
	std %r7, 744(%r6)
	ld %r7, 752(%r6)
	subfe %r7, %r5, %r7
	std %r7, 752(%r6)
	ld %r7, 760(%r6)
	subfe %r7, %r8, %r7
	std %r7, 760(%r6)
	ld %r7, 768(%r6)
	subfe %r7, %r8, %r7
	std %r7, 768(%r6)
	ld %r7, 776(%r6)
	subfe %r7, %r8, %r7
	std %r7, 776(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 728(%r6)
	subfc %r7, %r4, %r7
	std %r7, 728(%r6)
	ld %r7, 736(%r6)
	subfe %r7, %r8, %r7
	std %r7, 736(%r6)
	ld %r7, 744(%r6)
	subfe %r7, %r8, %r7
	std %r7, 744(%r6)
	ld %r7, 752(%r6)
	subfe %r7, %r5, %r7
	std %r7, 752(%r6)
	ld %r7, 760(%r6)
	subfe %r7, %r8, %r7
	std %r7, 760(%r6)
	ld %r7, 768(%r6)
	subfe %r7, %r8, %r7
	std %r7, 768(%r6)
	ld %r7, 776(%r6)
	subfe %r7, %r8, %r7
	std %r7, 776(%r6)
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
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 56(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 64(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 72(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 80(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 88(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 96(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 104(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 56(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 56(%r6)
	ld %r7, 64(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 64(%r6)
	ld %r7, 72(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 72(%r6)
	ld %r7, 80(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 80(%r6)
	ld %r7, 88(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 88(%r6)
	ld %r7, 96(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 96(%r6)
	ld %r7, 104(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 104(%r6)
	addze %r4, %r4
	ld %r7, 80(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 80(%r6)
	ld %r7, 88(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 88(%r6)
	ld %r7, 96(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 96(%r6)
	ld %r7, 104(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 104(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 56(%r6)
	addc %r7, %r7, %r4
	std %r7, 56(%r6)
	ld %r7, 64(%r6)
	adde %r7, %r7, %r8
	std %r7, 64(%r6)
	ld %r7, 72(%r6)
	adde %r7, %r7, %r8
	std %r7, 72(%r6)
	ld %r7, 80(%r6)
	adde %r7, %r7, %r5
	std %r7, 80(%r6)
	ld %r7, 88(%r6)
	adde %r7, %r7, %r8
	std %r7, 88(%r6)
	ld %r7, 96(%r6)
	adde %r7, %r7, %r8
	std %r7, 96(%r6)
	ld %r7, 104(%r6)
	adde %r7, %r7, %r8
	std %r7, 104(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 56(%r6)
	addc %r7, %r7, %r4
	std %r7, 56(%r6)
	ld %r7, 64(%r6)
	adde %r7, %r7, %r8
	std %r7, 64(%r6)
	ld %r7, 72(%r6)
	adde %r7, %r7, %r8
	std %r7, 72(%r6)
	ld %r7, 80(%r6)
	adde %r7, %r7, %r5
	std %r7, 80(%r6)
	ld %r7, 88(%r6)
	adde %r7, %r7, %r8
	std %r7, 88(%r6)
	ld %r7, 96(%r6)
	adde %r7, %r7, %r8
	std %r7, 96(%r6)
	ld %r7, 104(%r6)
	adde %r7, %r7, %r8
	std %r7, 104(%r6)
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
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 784(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 792(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 800(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 808(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 816(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 824(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 832(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 784(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 784(%r6)
	ld %r7, 792(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 792(%r6)
	ld %r7, 800(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 800(%r6)
	ld %r7, 808(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 808(%r6)
	ld %r7, 816(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 816(%r6)
	ld %r7, 824(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 824(%r6)
	ld %r7, 832(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 832(%r6)
	addze %r4, %r4
	ld %r7, 808(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 808(%r6)
	ld %r7, 816(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 816(%r6)
	ld %r7, 824(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 824(%r6)
	ld %r7, 832(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 832(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 784(%r6)
	addc %r7, %r7, %r4
	std %r7, 784(%r6)
	ld %r7, 792(%r6)
	adde %r7, %r7, %r8
	std %r7, 792(%r6)
	ld %r7, 800(%r6)
	adde %r7, %r7, %r8
	std %r7, 800(%r6)
	ld %r7, 808(%r6)
	adde %r7, %r7, %r5
	std %r7, 808(%r6)
	ld %r7, 816(%r6)
	adde %r7, %r7, %r8
	std %r7, 816(%r6)
	ld %r7, 824(%r6)
	adde %r7, %r7, %r8
	std %r7, 824(%r6)
	ld %r7, 832(%r6)
	adde %r7, %r7, %r8
	std %r7, 832(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 784(%r6)
	addc %r7, %r7, %r4
	std %r7, 784(%r6)
	ld %r7, 792(%r6)
	adde %r7, %r7, %r8
	std %r7, 792(%r6)
	ld %r7, 800(%r6)
	adde %r7, %r7, %r8
	std %r7, 800(%r6)
	ld %r7, 808(%r6)
	adde %r7, %r7, %r5
	std %r7, 808(%r6)
	ld %r7, 816(%r6)
	adde %r7, %r7, %r8
	std %r7, 816(%r6)
	ld %r7, 824(%r6)
	adde %r7, %r7, %r8
	std %r7, 824(%r6)
	ld %r7, 832(%r6)
	adde %r7, %r7, %r8
	std %r7, 832(%r6)
	ld %r7, 504(%r6)
	ld %r8, 448(%r6)
	subfc %r7, %r8, %r7
	std %r7, 728(%r6)
	ld %r7, 512(%r6)
	ld %r8, 456(%r6)
	subfe %r7, %r8, %r7
	std %r7, 736(%r6)
	ld %r7, 520(%r6)
	ld %r8, 464(%r6)
	subfe %r7, %r8, %r7
	std %r7, 744(%r6)
	ld %r7, 528(%r6)
	ld %r8, 472(%r6)
	subfe %r7, %r8, %r7
	std %r7, 752(%r6)
	ld %r7, 536(%r6)
	ld %r8, 480(%r6)
	subfe %r7, %r8, %r7
	std %r7, 760(%r6)
	ld %r7, 544(%r6)
	ld %r8, 488(%r6)
	subfe %r7, %r8, %r7
	std %r7, 768(%r6)
	ld %r7, 552(%r6)
	ld %r8, 496(%r6)
	subfe %r7, %r8, %r7
	std %r7, 776(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 728(%r6)
	subfc %r7, %r4, %r7
	std %r7, 728(%r6)
	ld %r7, 736(%r6)
	subfe %r7, %r8, %r7
	std %r7, 736(%r6)
	ld %r7, 744(%r6)
	subfe %r7, %r8, %r7
	std %r7, 744(%r6)
	ld %r7, 752(%r6)
	subfe %r7, %r5, %r7
	std %r7, 752(%r6)
	ld %r7, 760(%r6)
	subfe %r7, %r8, %r7
	std %r7, 760(%r6)
	ld %r7, 768(%r6)
	subfe %r7, %r8, %r7
	std %r7, 768(%r6)
	ld %r7, 776(%r6)
	subfe %r7, %r8, %r7
	std %r7, 776(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 728(%r6)
	subfc %r7, %r4, %r7
	std %r7, 728(%r6)
	ld %r7, 736(%r6)
	subfe %r7, %r8, %r7
	std %r7, 736(%r6)
	ld %r7, 744(%r6)
	subfe %r7, %r8, %r7
	std %r7, 744(%r6)
	ld %r7, 752(%r6)
	subfe %r7, %r5, %r7
	std %r7, 752(%r6)
	ld %r7, 760(%r6)
	subfe %r7, %r8, %r7
	std %r7, 760(%r6)
	ld %r7, 768(%r6)
	subfe %r7, %r8, %r7
	std %r7, 768(%r6)
	ld %r7, 776(%r6)
	subfe %r7, %r8, %r7
	std %r7, 776(%r6)
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
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 0(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 8(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 16(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 24(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 32(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 40(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 48(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 0(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 0(%r6)
	ld %r7, 8(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 8(%r6)
	ld %r7, 16(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 16(%r6)
	ld %r7, 24(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 24(%r6)
	ld %r7, 32(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 32(%r6)
	ld %r7, 40(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 40(%r6)
	ld %r7, 48(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 48(%r6)
	addze %r4, %r4
	ld %r7, 24(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 24(%r6)
	ld %r7, 32(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 32(%r6)
	ld %r7, 40(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 40(%r6)
	ld %r7, 48(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 48(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 0(%r6)
	addc %r7, %r7, %r4
	std %r7, 0(%r6)
	ld %r7, 8(%r6)
	adde %r7, %r7, %r8
	std %r7, 8(%r6)
	ld %r7, 16(%r6)
	adde %r7, %r7, %r8
	std %r7, 16(%r6)
	ld %r7, 24(%r6)
	adde %r7, %r7, %r5
	std %r7, 24(%r6)
	ld %r7, 32(%r6)
	adde %r7, %r7, %r8
	std %r7, 32(%r6)
	ld %r7, 40(%r6)
	adde %r7, %r7, %r8
	std %r7, 40(%r6)
	ld %r7, 48(%r6)
	adde %r7, %r7, %r8
	std %r7, 48(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 0(%r6)
	addc %r7, %r7, %r4
	std %r7, 0(%r6)
	ld %r7, 8(%r6)
	adde %r7, %r7, %r8
	std %r7, 8(%r6)
	ld %r7, 16(%r6)
	adde %r7, %r7, %r8
	std %r7, 16(%r6)
	ld %r7, 24(%r6)
	adde %r7, %r7, %r5
	std %r7, 24(%r6)
	ld %r7, 32(%r6)
	adde %r7, %r7, %r8
	std %r7, 32(%r6)
	ld %r7, 40(%r6)
	adde %r7, %r7, %r8
	std %r7, 40(%r6)
	ld %r7, 48(%r6)
	adde %r7, %r7, %r8
	std %r7, 48(%r6)
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
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 112(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 120(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 128(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 136(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 144(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 152(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 160(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 112(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 112(%r6)
	ld %r7, 120(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 120(%r6)
	ld %r7, 128(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 128(%r6)
	ld %r7, 136(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 136(%r6)
	ld %r7, 144(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 144(%r6)
	ld %r7, 152(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 152(%r6)
	ld %r7, 160(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 160(%r6)
	addze %r4, %r4
	ld %r7, 136(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 136(%r6)
	ld %r7, 144(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 144(%r6)
	ld %r7, 152(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 152(%r6)
	ld %r7, 160(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 160(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 112(%r6)
	addc %r7, %r7, %r4
	std %r7, 112(%r6)
	ld %r7, 120(%r6)
	adde %r7, %r7, %r8
	std %r7, 120(%r6)
	ld %r7, 128(%r6)
	adde %r7, %r7, %r8
	std %r7, 128(%r6)
	ld %r7, 136(%r6)
	adde %r7, %r7, %r5
	std %r7, 136(%r6)
	ld %r7, 144(%r6)
	adde %r7, %r7, %r8
	std %r7, 144(%r6)
	ld %r7, 152(%r6)
	adde %r7, %r7, %r8
	std %r7, 152(%r6)
	ld %r7, 160(%r6)
	adde %r7, %r7, %r8
	std %r7, 160(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 112(%r6)
	addc %r7, %r7, %r4
	std %r7, 112(%r6)
	ld %r7, 120(%r6)
	adde %r7, %r7, %r8
	std %r7, 120(%r6)
	ld %r7, 128(%r6)
	adde %r7, %r7, %r8
	std %r7, 128(%r6)
	ld %r7, 136(%r6)
	adde %r7, %r7, %r5
	std %r7, 136(%r6)
	ld %r7, 144(%r6)
	adde %r7, %r7, %r8
	std %r7, 144(%r6)
	ld %r7, 152(%r6)
	adde %r7, %r7, %r8
	std %r7, 152(%r6)
	ld %r7, 160(%r6)
	adde %r7, %r7, %r8
	std %r7, 160(%r6)
	blr
