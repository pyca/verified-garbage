// The functions of `src/internal/vg_mlkem_decode_decompress.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_decode_decompress:
	rlwinm %r5, %r5, 0, 0, 31
	li %r9, 3329
	addi %r7, %r5, -1
	cmplwi %cr0, %r7, 0
	beq %cr0, 20f
	addi %r7, %r5, -4
	cmplwi %cr0, %r7, 0
	beq %cr0, 22f
	li %r11, 64
24:
	lbz %r8, 0(%r3)
	lbz %r7, 1(%r3)
	rldicr %r7, %r7, 8, 55
	add %r8, %r8, %r7
	lbz %r7, 2(%r3)
	rldicr %r7, %r7, 16, 47
	add %r8, %r8, %r7
	lbz %r7, 3(%r3)
	rldicr %r7, %r7, 24, 39
	add %r8, %r8, %r7
	lbz %r7, 4(%r3)
	rldicr %r7, %r7, 32, 31
	add %r8, %r8, %r7
	rldicr %r7, %r8, 54, 9
	rldicl %r7, %r7, 10, 54
	mulld %r7, %r7, %r9
	addi %r7, %r7, 512
	rldicl %r7, %r7, 54, 10
	stw %r7, 0(%r6)
	rldicr %r7, %r8, 44, 19
	rldicl %r7, %r7, 10, 54
	mulld %r7, %r7, %r9
	addi %r7, %r7, 512
	rldicl %r7, %r7, 54, 10
	stw %r7, 4(%r6)
	rldicr %r7, %r8, 34, 29
	rldicl %r7, %r7, 10, 54
	mulld %r7, %r7, %r9
	addi %r7, %r7, 512
	rldicl %r7, %r7, 54, 10
	stw %r7, 8(%r6)
	rldicr %r7, %r8, 24, 39
	rldicl %r7, %r7, 10, 54
	mulld %r7, %r7, %r9
	addi %r7, %r7, 512
	rldicl %r7, %r7, 54, 10
	stw %r7, 12(%r6)
	addi %r3, %r3, 5
	addi %r6, %r6, 16
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 24b
	b 23f
22:
	li %r11, 128
25:
	lbz %r8, 0(%r3)
	rldicr %r7, %r8, 60, 3
	rldicl %r7, %r7, 4, 60
	mulld %r7, %r7, %r9
	addi %r7, %r7, 8
	rldicl %r7, %r7, 60, 4
	stw %r7, 0(%r6)
	rldicl %r7, %r8, 60, 4
	mulld %r7, %r7, %r9
	addi %r7, %r7, 8
	rldicl %r7, %r7, 60, 4
	stw %r7, 4(%r6)
	addi %r3, %r3, 1
	addi %r6, %r6, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 25b
23:
	b 21f
20:
	li %r11, 32
26:
	lbz %r8, 0(%r3)
	rldicr %r7, %r8, 63, 0
	rldicl %r7, %r7, 1, 63
	mulld %r7, %r7, %r9
	addi %r7, %r7, 1
	rldicl %r7, %r7, 63, 1
	stw %r7, 0(%r6)
	rldicr %r7, %r8, 62, 1
	rldicl %r7, %r7, 1, 63
	mulld %r7, %r7, %r9
	addi %r7, %r7, 1
	rldicl %r7, %r7, 63, 1
	stw %r7, 4(%r6)
	rldicr %r7, %r8, 61, 2
	rldicl %r7, %r7, 1, 63
	mulld %r7, %r7, %r9
	addi %r7, %r7, 1
	rldicl %r7, %r7, 63, 1
	stw %r7, 8(%r6)
	rldicr %r7, %r8, 60, 3
	rldicl %r7, %r7, 1, 63
	mulld %r7, %r7, %r9
	addi %r7, %r7, 1
	rldicl %r7, %r7, 63, 1
	stw %r7, 12(%r6)
	rldicr %r7, %r8, 59, 4
	rldicl %r7, %r7, 1, 63
	mulld %r7, %r7, %r9
	addi %r7, %r7, 1
	rldicl %r7, %r7, 63, 1
	stw %r7, 16(%r6)
	rldicr %r7, %r8, 58, 5
	rldicl %r7, %r7, 1, 63
	mulld %r7, %r7, %r9
	addi %r7, %r7, 1
	rldicl %r7, %r7, 63, 1
	stw %r7, 20(%r6)
	rldicr %r7, %r8, 57, 6
	rldicl %r7, %r7, 1, 63
	mulld %r7, %r7, %r9
	addi %r7, %r7, 1
	rldicl %r7, %r7, 63, 1
	stw %r7, 24(%r6)
	rldicr %r7, %r8, 56, 7
	rldicl %r7, %r7, 1, 63
	mulld %r7, %r7, %r9
	addi %r7, %r7, 1
	rldicl %r7, %r7, 63, 1
	stw %r7, 28(%r6)
	addi %r3, %r3, 1
	addi %r6, %r6, 32
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 26b
21:
	blr
