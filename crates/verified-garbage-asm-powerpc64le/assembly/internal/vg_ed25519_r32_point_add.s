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
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
20:
	lwz %r4, 320(%r9)
	li %r8, 0
	lwz %r5, 352(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 356(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 360(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 364(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 368(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 372(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 376(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 380(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 20b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 320(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 324(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 328(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 332(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 336(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 340(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 344(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
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
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
21:
	lwz %r4, 352(%r9)
	li %r8, 0
	lwz %r5, 384(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 388(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 392(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 396(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 400(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 404(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 408(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 412(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 21b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 352(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 356(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 360(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 364(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 368(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 372(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 376(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
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
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
22:
	lwz %r4, 160(%r9)
	li %r8, 0
	lwz %r5, 576(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 580(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 584(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 588(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 592(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 596(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 600(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 604(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 22b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 384(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 388(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 392(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 396(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 400(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 404(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 408(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
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
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
23:
	lwz %r4, 384(%r9)
	li %r8, 0
	lwz %r5, 288(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 292(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 296(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 300(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 304(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 308(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 312(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 316(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 23b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 384(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 388(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 392(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 396(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 400(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 404(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 408(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
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
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
24:
	lwz %r4, 416(%r9)
	li %r8, 0
	lwz %r5, 256(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 260(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 264(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 268(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 272(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 276(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 280(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 284(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 24b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 416(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 420(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 424(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 428(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 432(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 436(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 440(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
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
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
25:
	lwz %r4, 448(%r9)
	li %r8, 0
	lwz %r5, 480(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 484(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 488(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 492(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 496(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 500(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 504(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 508(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 25b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
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
	mulld %r8, %r8, %r10
	lwz %r7, 64(%r6)
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
26:
	lwz %r4, 512(%r9)
	li %r8, 0
	lwz %r5, 544(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 548(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 552(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 556(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 560(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 564(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 568(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 572(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 26b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 112(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 116(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 120(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 124(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
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
	mulld %r8, %r8, %r10
	lwz %r7, 96(%r6)
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
27:
	lwz %r4, 480(%r9)
	li %r8, 0
	lwz %r5, 512(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 516(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 520(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 524(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 528(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 532(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 536(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 540(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 27b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 132(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 136(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 140(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 144(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 148(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 152(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 156(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
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
	mulld %r8, %r8, %r10
	lwz %r7, 128(%r6)
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
28:
	lwz %r4, 448(%r9)
	li %r8, 0
	lwz %r5, 544(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 548(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 552(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 556(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 560(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 564(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 568(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 572(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 28b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 896(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 900(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 904(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 168(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 908(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 172(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 912(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 176(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 916(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 180(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 920(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 184(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 924(%r6)
	mulld %r5, %r5, %r10
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 188(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 160(%r6)
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 168(%r6)
	add %r7, %r7, %r8
	stw %r7, 168(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	add %r7, %r7, %r8
	stw %r7, 172(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	add %r7, %r7, %r8
	stw %r7, 176(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	add %r7, %r7, %r8
	stw %r7, 180(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	add %r7, %r7, %r8
	stw %r7, 184(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	add %r7, %r7, %r8
	stw %r7, 188(%r6)
	rldicl %r8, %r7, 32, 32
	mulld %r8, %r8, %r10
	lwz %r7, 160(%r6)
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	blr
