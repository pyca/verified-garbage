// The functions of `src/internal/vg_ed25519_r32_point_add.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed25519_r32_point_add:
	addi %r6, %r3, 0
	li %r10, 38
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 33, 30
	lwz %r7, 96(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -76
	lwz %r5, 64(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 320(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 100(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 68(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 324(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 104(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 72(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 328(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 108(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 76(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 332(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 112(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 80(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 336(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 84(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 340(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 88(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 344(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 92(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 348(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 320(%r6)
	add %r7, %r7, %r8
	stw %r7, 320(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 324(%r6)
	add %r7, %r7, %r8
	stw %r7, 324(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 328(%r6)
	add %r7, %r7, %r8
	stw %r7, 328(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 332(%r6)
	add %r7, %r7, %r8
	stw %r7, 332(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 336(%r6)
	add %r7, %r7, %r8
	stw %r7, 336(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 340(%r6)
	add %r7, %r7, %r8
	stw %r7, 340(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 344(%r6)
	add %r7, %r7, %r8
	stw %r7, 344(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 348(%r6)
	add %r7, %r7, %r8
	stw %r7, 348(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 320(%r6)
	add %r7, %r7, %r8
	stw %r7, 320(%r6)
	li %r10, 38
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 33, 30
	lwz %r7, 224(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -76
	lwz %r5, 192(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 352(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 228(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 196(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 356(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 232(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 200(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 360(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 236(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 204(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 364(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 240(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 208(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 368(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 244(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 212(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 372(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 248(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 216(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 376(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 252(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 220(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 380(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 352(%r6)
	add %r7, %r7, %r8
	stw %r7, 352(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 356(%r6)
	add %r7, %r7, %r8
	stw %r7, 356(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 360(%r6)
	add %r7, %r7, %r8
	stw %r7, 360(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 364(%r6)
	add %r7, %r7, %r8
	stw %r7, 364(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 368(%r6)
	add %r7, %r7, %r8
	stw %r7, 368(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 372(%r6)
	add %r7, %r7, %r8
	stw %r7, 372(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 376(%r6)
	add %r7, %r7, %r8
	stw %r7, 376(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 380(%r6)
	add %r7, %r7, %r8
	stw %r7, 380(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 352(%r6)
	add %r7, %r7, %r8
	stw %r7, 352(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 320(%r6)
	ld %r5, 352(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 328(%r6)
	ld %r5, 352(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 320(%r6)
	ld %r5, 360(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 336(%r6)
	ld %r5, 352(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 328(%r6)
	ld %r5, 360(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 320(%r6)
	ld %r5, 368(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 344(%r6)
	ld %r5, 352(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 336(%r6)
	ld %r5, 360(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 328(%r6)
	ld %r5, 368(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 320(%r6)
	ld %r5, 376(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 344(%r6)
	ld %r5, 360(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 336(%r6)
	ld %r5, 368(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 328(%r6)
	ld %r5, 376(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 344(%r6)
	ld %r5, 368(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 336(%r6)
	ld %r5, 376(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 344(%r6)
	ld %r5, 376(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 320(%r6)
	std %r9, 328(%r6)
	std %r10, 336(%r6)
	std %r11, 344(%r6)
	li %r10, 38
	li %r8, 0
	lwz %r7, 96(%r6)
	lwz %r5, 64(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 352(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 100(%r6)
	lwz %r5, 68(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 356(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 104(%r6)
	lwz %r5, 72(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 360(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 108(%r6)
	lwz %r5, 76(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 364(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 112(%r6)
	lwz %r5, 80(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 368(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	lwz %r5, 84(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 372(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	lwz %r5, 88(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 376(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	lwz %r5, 92(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 380(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 352(%r6)
	add %r7, %r7, %r8
	stw %r7, 352(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 356(%r6)
	add %r7, %r7, %r8
	stw %r7, 356(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 360(%r6)
	add %r7, %r7, %r8
	stw %r7, 360(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 364(%r6)
	add %r7, %r7, %r8
	stw %r7, 364(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 368(%r6)
	add %r7, %r7, %r8
	stw %r7, 368(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 372(%r6)
	add %r7, %r7, %r8
	stw %r7, 372(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 376(%r6)
	add %r7, %r7, %r8
	stw %r7, 376(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 380(%r6)
	add %r7, %r7, %r8
	stw %r7, 380(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 352(%r6)
	add %r7, %r7, %r8
	stw %r7, 352(%r6)
	li %r10, 38
	li %r8, 0
	lwz %r7, 224(%r6)
	lwz %r5, 192(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 384(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 228(%r6)
	lwz %r5, 196(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 388(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 232(%r6)
	lwz %r5, 200(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 392(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 236(%r6)
	lwz %r5, 204(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 396(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 240(%r6)
	lwz %r5, 208(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 400(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 244(%r6)
	lwz %r5, 212(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 404(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 248(%r6)
	lwz %r5, 216(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 408(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 252(%r6)
	lwz %r5, 220(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 412(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 384(%r6)
	add %r7, %r7, %r8
	stw %r7, 384(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 388(%r6)
	add %r7, %r7, %r8
	stw %r7, 388(%r6)
	rldicl %r8, %r7, 32, 32
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
	mulld %r8, %r8, %r10
	lwz %r7, 384(%r6)
	add %r7, %r7, %r8
	stw %r7, 384(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 352(%r6)
	ld %r5, 384(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 360(%r6)
	ld %r5, 384(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 352(%r6)
	ld %r5, 392(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 368(%r6)
	ld %r5, 384(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 360(%r6)
	ld %r5, 392(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 352(%r6)
	ld %r5, 400(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 376(%r6)
	ld %r5, 384(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 368(%r6)
	ld %r5, 392(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 360(%r6)
	ld %r5, 400(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 352(%r6)
	ld %r5, 408(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 376(%r6)
	ld %r5, 392(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 368(%r6)
	ld %r5, 400(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 360(%r6)
	ld %r5, 408(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 376(%r6)
	ld %r5, 400(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 368(%r6)
	ld %r5, 408(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 376(%r6)
	ld %r5, 408(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 352(%r6)
	std %r9, 360(%r6)
	std %r10, 368(%r6)
	std %r11, 376(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 160(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 168(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 160(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 176(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 168(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 160(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 184(%r6)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 176(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 168(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 160(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 184(%r6)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 176(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 168(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 184(%r6)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 176(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 184(%r6)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 384(%r6)
	std %r9, 392(%r6)
	std %r10, 400(%r6)
	std %r11, 408(%r6)
	li %r10, 38
	li %r8, 0
	lwz %r7, 384(%r6)
	lwz %r5, 384(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 384(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 388(%r6)
	lwz %r5, 388(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 388(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 392(%r6)
	lwz %r5, 392(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 392(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 396(%r6)
	lwz %r5, 396(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 396(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 400(%r6)
	lwz %r5, 400(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 400(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 404(%r6)
	lwz %r5, 404(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 404(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 408(%r6)
	lwz %r5, 408(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 408(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 412(%r6)
	lwz %r5, 412(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 412(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 384(%r6)
	add %r7, %r7, %r8
	stw %r7, 384(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 388(%r6)
	add %r7, %r7, %r8
	stw %r7, 388(%r6)
	rldicl %r8, %r7, 32, 32
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
	mulld %r8, %r8, %r10
	lwz %r7, 384(%r6)
	add %r7, %r7, %r8
	stw %r7, 384(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 384(%r6)
	ld %r5, 288(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 392(%r6)
	ld %r5, 288(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 384(%r6)
	ld %r5, 296(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 400(%r6)
	ld %r5, 288(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 392(%r6)
	ld %r5, 296(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 384(%r6)
	ld %r5, 304(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 408(%r6)
	ld %r5, 288(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 400(%r6)
	ld %r5, 296(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 392(%r6)
	ld %r5, 304(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 384(%r6)
	ld %r5, 312(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 408(%r6)
	ld %r5, 296(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 400(%r6)
	ld %r5, 304(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 392(%r6)
	ld %r5, 312(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 408(%r6)
	ld %r5, 304(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 400(%r6)
	ld %r5, 312(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 408(%r6)
	ld %r5, 312(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 384(%r6)
	std %r9, 392(%r6)
	std %r10, 400(%r6)
	std %r11, 408(%r6)
	li %r10, 38
	li %r8, 0
	lwz %r7, 128(%r6)
	lwz %r5, 128(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 416(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	lwz %r5, 132(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 420(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	lwz %r5, 136(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 424(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	lwz %r5, 140(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 428(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	lwz %r5, 144(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 432(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	lwz %r5, 148(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 436(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	lwz %r5, 152(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 440(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	lwz %r5, 156(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 444(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 416(%r6)
	add %r7, %r7, %r8
	stw %r7, 416(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 420(%r6)
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
	mulld %r8, %r8, %r10
	lwz %r7, 416(%r6)
	add %r7, %r7, %r8
	stw %r7, 416(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 416(%r6)
	ld %r5, 256(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 424(%r6)
	ld %r5, 256(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 416(%r6)
	ld %r5, 264(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 432(%r6)
	ld %r5, 256(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 424(%r6)
	ld %r5, 264(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 416(%r6)
	ld %r5, 272(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 440(%r6)
	ld %r5, 256(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 432(%r6)
	ld %r5, 264(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 424(%r6)
	ld %r5, 272(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 416(%r6)
	ld %r5, 280(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 440(%r6)
	ld %r5, 264(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 432(%r6)
	ld %r5, 272(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 424(%r6)
	ld %r5, 280(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 440(%r6)
	ld %r5, 272(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 432(%r6)
	ld %r5, 280(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 440(%r6)
	ld %r5, 280(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 416(%r6)
	std %r9, 424(%r6)
	std %r10, 432(%r6)
	std %r11, 440(%r6)
	li %r10, 38
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 33, 30
	lwz %r7, 352(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -76
	lwz %r5, 320(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 356(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 324(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 360(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 328(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 364(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 332(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 368(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 336(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 372(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 340(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 376(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 344(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 380(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 348(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
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
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 448(%r6)
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	li %r10, 38
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 33, 30
	lwz %r7, 416(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -76
	lwz %r5, 384(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 420(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 388(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 424(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 392(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 428(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 396(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 432(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 400(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 436(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 404(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 440(%r6)
	add %r7, %r7, %r4
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 408(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 444(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 412(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
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
	lwz %r7, 504(%r6)
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 480(%r6)
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	li %r10, 38
	li %r8, 0
	lwz %r7, 416(%r6)
	lwz %r5, 384(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 420(%r6)
	lwz %r5, 388(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 424(%r6)
	lwz %r5, 392(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 428(%r6)
	lwz %r5, 396(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 432(%r6)
	lwz %r5, 400(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 436(%r6)
	lwz %r5, 404(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 440(%r6)
	lwz %r5, 408(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 444(%r6)
	lwz %r5, 412(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
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
	mulld %r8, %r8, %r10
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	li %r10, 38
	li %r8, 0
	lwz %r7, 352(%r6)
	lwz %r5, 320(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 356(%r6)
	lwz %r5, 324(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 360(%r6)
	lwz %r5, 328(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 364(%r6)
	lwz %r5, 332(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 368(%r6)
	lwz %r5, 336(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 372(%r6)
	lwz %r5, 340(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 376(%r6)
	lwz %r5, 344(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 380(%r6)
	lwz %r5, 348(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
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
	mulld %r8, %r8, %r10
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 448(%r6)
	ld %r5, 480(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 456(%r6)
	ld %r5, 480(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 448(%r6)
	ld %r5, 488(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 464(%r6)
	ld %r5, 480(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 456(%r6)
	ld %r5, 488(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 448(%r6)
	ld %r5, 496(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 472(%r6)
	ld %r5, 480(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 464(%r6)
	ld %r5, 488(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 456(%r6)
	ld %r5, 496(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 448(%r6)
	ld %r5, 504(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 472(%r6)
	ld %r5, 488(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 464(%r6)
	ld %r5, 496(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 456(%r6)
	ld %r5, 504(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 472(%r6)
	ld %r5, 496(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 464(%r6)
	ld %r5, 504(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 472(%r6)
	ld %r5, 504(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 64(%r6)
	std %r9, 72(%r6)
	std %r10, 80(%r6)
	std %r11, 88(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 512(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 520(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 512(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 528(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 520(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 512(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 536(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 528(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 520(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 512(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 536(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 528(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 520(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 536(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 528(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 536(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 96(%r6)
	std %r9, 104(%r6)
	std %r10, 112(%r6)
	std %r11, 120(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 480(%r6)
	ld %r5, 512(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 488(%r6)
	ld %r5, 512(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 480(%r6)
	ld %r5, 520(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 496(%r6)
	ld %r5, 512(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 488(%r6)
	ld %r5, 520(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 480(%r6)
	ld %r5, 528(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 504(%r6)
	ld %r5, 512(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 496(%r6)
	ld %r5, 520(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 488(%r6)
	ld %r5, 528(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 480(%r6)
	ld %r5, 536(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 504(%r6)
	ld %r5, 520(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 496(%r6)
	ld %r5, 528(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 488(%r6)
	ld %r5, 536(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 504(%r6)
	ld %r5, 528(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 496(%r6)
	ld %r5, 536(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 504(%r6)
	ld %r5, 536(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 128(%r6)
	std %r9, 136(%r6)
	std %r10, 144(%r6)
	std %r11, 152(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 448(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 864(%r6)
	li %r8, 0
	ld %r4, 456(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 448(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 872(%r6)
	li %r9, 0
	ld %r4, 464(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 456(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 448(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 880(%r6)
	li %r10, 0
	ld %r4, 472(%r6)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 464(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 456(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 448(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 888(%r6)
	li %r8, 0
	ld %r4, 472(%r6)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 464(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 456(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 896(%r6)
	li %r9, 0
	ld %r4, 472(%r6)
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 464(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 904(%r6)
	li %r10, 0
	ld %r4, 472(%r6)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 912(%r6)
	li %r8, 0
	std %r9, 920(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 864(%r6)
	ld %r4, 896(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 872(%r6)
	ld %r4, 904(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 880(%r6)
	ld %r4, 912(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 888(%r6)
	ld %r4, 920(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 896(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 904(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 912(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 920(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 160(%r6)
	std %r9, 168(%r6)
	std %r10, 176(%r6)
	std %r11, 184(%r6)
	blr
