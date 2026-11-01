// The functions of `src/rc4.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rc4_init:
	addi %r12, %r4, -1
	rldicl %r12, %r12, 56, 8
	cmpldi %cr0, %r12, 0
	bne %cr0, 20f
	or %r7, %r3, %r3
	or %r3, %r5, %r5
	li %r6, 0
22:
	add %r12, %r3, %r6
	stb %r6, 0(%r12)
	addi %r6, %r6, 1
	li %r12, 256
	subf %r12, %r12, %r6
	cmpldi %cr0, %r12, 0
	bne %cr0, 22b
	li %r6, 0
	li %r5, 0
	li %r9, 0
	li %r8, 0
23:
	add %r12, %r3, %r6
	lbz %r0, 0(%r12)
	add %r9, %r9, %r0
	add %r12, %r7, %r5
	lbz %r0, 0(%r12)
	add %r9, %r9, %r0
	rldicr %r9, %r9, 56, 7
	rldicl %r9, %r9, 8, 56
	li %r11, 0
	li %r12, 0
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 0(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 8
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 8(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 16
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 16(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 24
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 24(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 32
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 32(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 40
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 40(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 48
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 48(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 56
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 56(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 64
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 64(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 72
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 72(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 80
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 80(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 88
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 88(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 96
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 96(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 104
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 104(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 112
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 112(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 120
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 120(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 128
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 128(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 136
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 136(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 144
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 144(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 152
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 152(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 160
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 160(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 168
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 168(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 176
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 176(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 184
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 184(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 192
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 192(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 200
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 200(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 208
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 208(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 216
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 216(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 224
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 224(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 232
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 232(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 240
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 240(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 248
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 248(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r10, 0
	li %r12, 0
	xor %r12, %r12, %r9
	rldicr %r12, %r12, 61, 2
	rldicl %r12, %r12, 3, 61
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r0, %r11, %r12
	or %r10, %r10, %r0
	rldicl %r11, %r11, 56, 8
	li %r12, 1
	xor %r12, %r12, %r9
	rldicr %r12, %r12, 61, 2
	rldicl %r12, %r12, 3, 61
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r0, %r11, %r12
	or %r10, %r10, %r0
	rldicl %r11, %r11, 56, 8
	li %r12, 2
	xor %r12, %r12, %r9
	rldicr %r12, %r12, 61, 2
	rldicl %r12, %r12, 3, 61
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r0, %r11, %r12
	or %r10, %r10, %r0
	rldicl %r11, %r11, 56, 8
	li %r12, 3
	xor %r12, %r12, %r9
	rldicr %r12, %r12, 61, 2
	rldicl %r12, %r12, 3, 61
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r0, %r11, %r12
	or %r10, %r10, %r0
	rldicl %r11, %r11, 56, 8
	li %r12, 4
	xor %r12, %r12, %r9
	rldicr %r12, %r12, 61, 2
	rldicl %r12, %r12, 3, 61
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r0, %r11, %r12
	or %r10, %r10, %r0
	rldicl %r11, %r11, 56, 8
	li %r12, 5
	xor %r12, %r12, %r9
	rldicr %r12, %r12, 61, 2
	rldicl %r12, %r12, 3, 61
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r0, %r11, %r12
	or %r10, %r10, %r0
	rldicl %r11, %r11, 56, 8
	li %r12, 6
	xor %r12, %r12, %r9
	rldicr %r12, %r12, 61, 2
	rldicl %r12, %r12, 3, 61
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r0, %r11, %r12
	or %r10, %r10, %r0
	rldicl %r11, %r11, 56, 8
	li %r12, 7
	xor %r12, %r12, %r9
	rldicr %r12, %r12, 61, 2
	rldicl %r12, %r12, 3, 61
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r0, %r11, %r12
	or %r10, %r10, %r0
	rldicl %r11, %r11, 56, 8
	rldicr %r10, %r10, 56, 7
	rldicl %r10, %r10, 8, 56
	add %r12, %r3, %r6
	lbz %r0, 0(%r12)
	xor %r10, %r10, %r0
	li %r11, 0
	li %r12, 7
	xor %r12, %r12, %r9
	rldicr %r12, %r12, 61, 2
	rldicl %r12, %r12, 3, 61
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r0, %r10, %r12
	rldicl %r11, %r11, 8, 0
	or %r11, %r11, %r0
	li %r12, 6
	xor %r12, %r12, %r9
	rldicr %r12, %r12, 61, 2
	rldicl %r12, %r12, 3, 61
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r0, %r10, %r12
	rldicl %r11, %r11, 8, 0
	or %r11, %r11, %r0
	li %r12, 5
	xor %r12, %r12, %r9
	rldicr %r12, %r12, 61, 2
	rldicl %r12, %r12, 3, 61
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r0, %r10, %r12
	rldicl %r11, %r11, 8, 0
	or %r11, %r11, %r0
	li %r12, 4
	xor %r12, %r12, %r9
	rldicr %r12, %r12, 61, 2
	rldicl %r12, %r12, 3, 61
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r0, %r10, %r12
	rldicl %r11, %r11, 8, 0
	or %r11, %r11, %r0
	li %r12, 3
	xor %r12, %r12, %r9
	rldicr %r12, %r12, 61, 2
	rldicl %r12, %r12, 3, 61
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r0, %r10, %r12
	rldicl %r11, %r11, 8, 0
	or %r11, %r11, %r0
	li %r12, 2
	xor %r12, %r12, %r9
	rldicr %r12, %r12, 61, 2
	rldicl %r12, %r12, 3, 61
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r0, %r10, %r12
	rldicl %r11, %r11, 8, 0
	or %r11, %r11, %r0
	li %r12, 1
	xor %r12, %r12, %r9
	rldicr %r12, %r12, 61, 2
	rldicl %r12, %r12, 3, 61
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r0, %r10, %r12
	rldicl %r11, %r11, 8, 0
	or %r11, %r11, %r0
	li %r12, 0
	xor %r12, %r12, %r9
	rldicr %r12, %r12, 61, 2
	rldicl %r12, %r12, 3, 61
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r0, %r10, %r12
	rldicl %r11, %r11, 8, 0
	or %r11, %r11, %r0
	add %r12, %r3, %r6
	lbz %r0, 0(%r12)
	xor %r10, %r10, %r0
	li %r12, 0
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 0(%r3)
	xor %r0, %r0, %r12
	std %r0, 0(%r3)
	li %r12, 8
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 8(%r3)
	xor %r0, %r0, %r12
	std %r0, 8(%r3)
	li %r12, 16
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 16(%r3)
	xor %r0, %r0, %r12
	std %r0, 16(%r3)
	li %r12, 24
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 24(%r3)
	xor %r0, %r0, %r12
	std %r0, 24(%r3)
	li %r12, 32
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 32(%r3)
	xor %r0, %r0, %r12
	std %r0, 32(%r3)
	li %r12, 40
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 40(%r3)
	xor %r0, %r0, %r12
	std %r0, 40(%r3)
	li %r12, 48
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 48(%r3)
	xor %r0, %r0, %r12
	std %r0, 48(%r3)
	li %r12, 56
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 56(%r3)
	xor %r0, %r0, %r12
	std %r0, 56(%r3)
	li %r12, 64
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 64(%r3)
	xor %r0, %r0, %r12
	std %r0, 64(%r3)
	li %r12, 72
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 72(%r3)
	xor %r0, %r0, %r12
	std %r0, 72(%r3)
	li %r12, 80
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 80(%r3)
	xor %r0, %r0, %r12
	std %r0, 80(%r3)
	li %r12, 88
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 88(%r3)
	xor %r0, %r0, %r12
	std %r0, 88(%r3)
	li %r12, 96
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 96(%r3)
	xor %r0, %r0, %r12
	std %r0, 96(%r3)
	li %r12, 104
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 104(%r3)
	xor %r0, %r0, %r12
	std %r0, 104(%r3)
	li %r12, 112
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 112(%r3)
	xor %r0, %r0, %r12
	std %r0, 112(%r3)
	li %r12, 120
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 120(%r3)
	xor %r0, %r0, %r12
	std %r0, 120(%r3)
	li %r12, 128
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 128(%r3)
	xor %r0, %r0, %r12
	std %r0, 128(%r3)
	li %r12, 136
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 136(%r3)
	xor %r0, %r0, %r12
	std %r0, 136(%r3)
	li %r12, 144
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 144(%r3)
	xor %r0, %r0, %r12
	std %r0, 144(%r3)
	li %r12, 152
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 152(%r3)
	xor %r0, %r0, %r12
	std %r0, 152(%r3)
	li %r12, 160
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 160(%r3)
	xor %r0, %r0, %r12
	std %r0, 160(%r3)
	li %r12, 168
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 168(%r3)
	xor %r0, %r0, %r12
	std %r0, 168(%r3)
	li %r12, 176
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 176(%r3)
	xor %r0, %r0, %r12
	std %r0, 176(%r3)
	li %r12, 184
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 184(%r3)
	xor %r0, %r0, %r12
	std %r0, 184(%r3)
	li %r12, 192
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 192(%r3)
	xor %r0, %r0, %r12
	std %r0, 192(%r3)
	li %r12, 200
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 200(%r3)
	xor %r0, %r0, %r12
	std %r0, 200(%r3)
	li %r12, 208
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 208(%r3)
	xor %r0, %r0, %r12
	std %r0, 208(%r3)
	li %r12, 216
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 216(%r3)
	xor %r0, %r0, %r12
	std %r0, 216(%r3)
	li %r12, 224
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 224(%r3)
	xor %r0, %r0, %r12
	std %r0, 224(%r3)
	li %r12, 232
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 232(%r3)
	xor %r0, %r0, %r12
	std %r0, 232(%r3)
	li %r12, 240
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 240(%r3)
	xor %r0, %r0, %r12
	std %r0, 240(%r3)
	li %r12, 248
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 248(%r3)
	xor %r0, %r0, %r12
	std %r0, 248(%r3)
	add %r12, %r3, %r6
	stb %r10, 0(%r12)
	addi %r5, %r5, 1
	subf %r12, %r4, %r5
	addi %r0, %r12, -1
	xor %r0, %r0, %r12
	rldicl %r12, %r0, 1, 63
	addi %r12, %r12, -1
	and %r5, %r5, %r12
	addi %r6, %r6, 1
	li %r12, 256
	subf %r12, %r12, %r6
	cmpldi %cr0, %r12, 0
	bne %cr0, 23b
	li %r12, 0
	stb %r12, 256(%r3)
	stb %r12, 257(%r3)
	li %r3, 0
	b 21f
20:
	li %r3, 1
21:
	blr

vg_rc4_apply:
	lbz %r6, 256(%r3)
	lbz %r7, 257(%r3)
	li %r8, 0
	cmpldi %cr0, %r5, 0
	beq %cr0, 20f
22:
	addi %r6, %r6, 1
	rldicr %r6, %r6, 56, 7
	rldicl %r6, %r6, 8, 56
	add %r12, %r3, %r6
	lbz %r0, 0(%r12)
	add %r7, %r7, %r0
	rldicr %r7, %r7, 56, 7
	rldicl %r7, %r7, 8, 56
	or %r9, %r7, %r7
	li %r11, 0
	li %r12, 0
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 0(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 8
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 8(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 16
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 16(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 24
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 24(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 32
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 32(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 40
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 40(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 48
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 48(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 56
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 56(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 64
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 64(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 72
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 72(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 80
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 80(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 88
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 88(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 96
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 96(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 104
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 104(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 112
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 112(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 120
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 120(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 128
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 128(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 136
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 136(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 144
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 144(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 152
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 152(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 160
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 160(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 168
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 168(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 176
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 176(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 184
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 184(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 192
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 192(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 200
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 200(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 208
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 208(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 216
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 216(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 224
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 224(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 232
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 232(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 240
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 240(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 248
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 248(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r10, 0
	li %r12, 0
	xor %r12, %r12, %r9
	rldicr %r12, %r12, 61, 2
	rldicl %r12, %r12, 3, 61
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r0, %r11, %r12
	or %r10, %r10, %r0
	rldicl %r11, %r11, 56, 8
	li %r12, 1
	xor %r12, %r12, %r9
	rldicr %r12, %r12, 61, 2
	rldicl %r12, %r12, 3, 61
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r0, %r11, %r12
	or %r10, %r10, %r0
	rldicl %r11, %r11, 56, 8
	li %r12, 2
	xor %r12, %r12, %r9
	rldicr %r12, %r12, 61, 2
	rldicl %r12, %r12, 3, 61
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r0, %r11, %r12
	or %r10, %r10, %r0
	rldicl %r11, %r11, 56, 8
	li %r12, 3
	xor %r12, %r12, %r9
	rldicr %r12, %r12, 61, 2
	rldicl %r12, %r12, 3, 61
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r0, %r11, %r12
	or %r10, %r10, %r0
	rldicl %r11, %r11, 56, 8
	li %r12, 4
	xor %r12, %r12, %r9
	rldicr %r12, %r12, 61, 2
	rldicl %r12, %r12, 3, 61
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r0, %r11, %r12
	or %r10, %r10, %r0
	rldicl %r11, %r11, 56, 8
	li %r12, 5
	xor %r12, %r12, %r9
	rldicr %r12, %r12, 61, 2
	rldicl %r12, %r12, 3, 61
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r0, %r11, %r12
	or %r10, %r10, %r0
	rldicl %r11, %r11, 56, 8
	li %r12, 6
	xor %r12, %r12, %r9
	rldicr %r12, %r12, 61, 2
	rldicl %r12, %r12, 3, 61
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r0, %r11, %r12
	or %r10, %r10, %r0
	rldicl %r11, %r11, 56, 8
	li %r12, 7
	xor %r12, %r12, %r9
	rldicr %r12, %r12, 61, 2
	rldicl %r12, %r12, 3, 61
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r0, %r11, %r12
	or %r10, %r10, %r0
	rldicl %r11, %r11, 56, 8
	rldicr %r10, %r10, 56, 7
	rldicl %r10, %r10, 8, 56
	add %r12, %r3, %r6
	lbz %r0, 0(%r12)
	xor %r10, %r10, %r0
	li %r11, 0
	li %r12, 7
	xor %r12, %r12, %r9
	rldicr %r12, %r12, 61, 2
	rldicl %r12, %r12, 3, 61
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r0, %r10, %r12
	rldicl %r11, %r11, 8, 0
	or %r11, %r11, %r0
	li %r12, 6
	xor %r12, %r12, %r9
	rldicr %r12, %r12, 61, 2
	rldicl %r12, %r12, 3, 61
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r0, %r10, %r12
	rldicl %r11, %r11, 8, 0
	or %r11, %r11, %r0
	li %r12, 5
	xor %r12, %r12, %r9
	rldicr %r12, %r12, 61, 2
	rldicl %r12, %r12, 3, 61
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r0, %r10, %r12
	rldicl %r11, %r11, 8, 0
	or %r11, %r11, %r0
	li %r12, 4
	xor %r12, %r12, %r9
	rldicr %r12, %r12, 61, 2
	rldicl %r12, %r12, 3, 61
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r0, %r10, %r12
	rldicl %r11, %r11, 8, 0
	or %r11, %r11, %r0
	li %r12, 3
	xor %r12, %r12, %r9
	rldicr %r12, %r12, 61, 2
	rldicl %r12, %r12, 3, 61
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r0, %r10, %r12
	rldicl %r11, %r11, 8, 0
	or %r11, %r11, %r0
	li %r12, 2
	xor %r12, %r12, %r9
	rldicr %r12, %r12, 61, 2
	rldicl %r12, %r12, 3, 61
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r0, %r10, %r12
	rldicl %r11, %r11, 8, 0
	or %r11, %r11, %r0
	li %r12, 1
	xor %r12, %r12, %r9
	rldicr %r12, %r12, 61, 2
	rldicl %r12, %r12, 3, 61
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r0, %r10, %r12
	rldicl %r11, %r11, 8, 0
	or %r11, %r11, %r0
	li %r12, 0
	xor %r12, %r12, %r9
	rldicr %r12, %r12, 61, 2
	rldicl %r12, %r12, 3, 61
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r0, %r10, %r12
	rldicl %r11, %r11, 8, 0
	or %r11, %r11, %r0
	add %r12, %r3, %r6
	lbz %r0, 0(%r12)
	xor %r10, %r10, %r0
	li %r12, 0
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 0(%r3)
	xor %r0, %r0, %r12
	std %r0, 0(%r3)
	li %r12, 8
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 8(%r3)
	xor %r0, %r0, %r12
	std %r0, 8(%r3)
	li %r12, 16
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 16(%r3)
	xor %r0, %r0, %r12
	std %r0, 16(%r3)
	li %r12, 24
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 24(%r3)
	xor %r0, %r0, %r12
	std %r0, 24(%r3)
	li %r12, 32
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 32(%r3)
	xor %r0, %r0, %r12
	std %r0, 32(%r3)
	li %r12, 40
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 40(%r3)
	xor %r0, %r0, %r12
	std %r0, 40(%r3)
	li %r12, 48
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 48(%r3)
	xor %r0, %r0, %r12
	std %r0, 48(%r3)
	li %r12, 56
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 56(%r3)
	xor %r0, %r0, %r12
	std %r0, 56(%r3)
	li %r12, 64
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 64(%r3)
	xor %r0, %r0, %r12
	std %r0, 64(%r3)
	li %r12, 72
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 72(%r3)
	xor %r0, %r0, %r12
	std %r0, 72(%r3)
	li %r12, 80
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 80(%r3)
	xor %r0, %r0, %r12
	std %r0, 80(%r3)
	li %r12, 88
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 88(%r3)
	xor %r0, %r0, %r12
	std %r0, 88(%r3)
	li %r12, 96
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 96(%r3)
	xor %r0, %r0, %r12
	std %r0, 96(%r3)
	li %r12, 104
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 104(%r3)
	xor %r0, %r0, %r12
	std %r0, 104(%r3)
	li %r12, 112
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 112(%r3)
	xor %r0, %r0, %r12
	std %r0, 112(%r3)
	li %r12, 120
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 120(%r3)
	xor %r0, %r0, %r12
	std %r0, 120(%r3)
	li %r12, 128
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 128(%r3)
	xor %r0, %r0, %r12
	std %r0, 128(%r3)
	li %r12, 136
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 136(%r3)
	xor %r0, %r0, %r12
	std %r0, 136(%r3)
	li %r12, 144
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 144(%r3)
	xor %r0, %r0, %r12
	std %r0, 144(%r3)
	li %r12, 152
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 152(%r3)
	xor %r0, %r0, %r12
	std %r0, 152(%r3)
	li %r12, 160
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 160(%r3)
	xor %r0, %r0, %r12
	std %r0, 160(%r3)
	li %r12, 168
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 168(%r3)
	xor %r0, %r0, %r12
	std %r0, 168(%r3)
	li %r12, 176
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 176(%r3)
	xor %r0, %r0, %r12
	std %r0, 176(%r3)
	li %r12, 184
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 184(%r3)
	xor %r0, %r0, %r12
	std %r0, 184(%r3)
	li %r12, 192
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 192(%r3)
	xor %r0, %r0, %r12
	std %r0, 192(%r3)
	li %r12, 200
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 200(%r3)
	xor %r0, %r0, %r12
	std %r0, 200(%r3)
	li %r12, 208
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 208(%r3)
	xor %r0, %r0, %r12
	std %r0, 208(%r3)
	li %r12, 216
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 216(%r3)
	xor %r0, %r0, %r12
	std %r0, 216(%r3)
	li %r12, 224
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 224(%r3)
	xor %r0, %r0, %r12
	std %r0, 224(%r3)
	li %r12, 232
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 232(%r3)
	xor %r0, %r0, %r12
	std %r0, 232(%r3)
	li %r12, 240
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 240(%r3)
	xor %r0, %r0, %r12
	std %r0, 240(%r3)
	li %r12, 248
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r12, %r12, %r11
	ld %r0, 248(%r3)
	xor %r0, %r0, %r12
	std %r0, 248(%r3)
	add %r12, %r3, %r6
	lbz %r0, 0(%r12)
	stb %r10, 0(%r12)
	add %r9, %r10, %r0
	rldicr %r9, %r9, 56, 7
	rldicl %r9, %r9, 8, 56
	li %r11, 0
	li %r12, 0
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 0(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 8
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 8(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 16
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 16(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 24
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 24(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 32
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 32(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 40
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 40(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 48
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 48(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 56
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 56(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 64
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 64(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 72
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 72(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 80
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 80(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 88
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 88(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 96
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 96(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 104
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 104(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 112
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 112(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 120
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 120(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 128
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 128(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 136
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 136(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 144
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 144(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 152
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 152(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 160
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 160(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 168
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 168(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 176
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 176(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 184
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 184(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 192
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 192(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 200
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 200(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 208
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 208(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 216
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 216(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 224
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 224(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 232
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 232(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 240
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 240(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r12, 248
	xor %r12, %r12, %r9
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	ld %r0, 248(%r3)
	and %r0, %r0, %r12
	or %r11, %r11, %r0
	li %r10, 0
	li %r12, 0
	xor %r12, %r12, %r9
	rldicr %r12, %r12, 61, 2
	rldicl %r12, %r12, 3, 61
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r0, %r11, %r12
	or %r10, %r10, %r0
	rldicl %r11, %r11, 56, 8
	li %r12, 1
	xor %r12, %r12, %r9
	rldicr %r12, %r12, 61, 2
	rldicl %r12, %r12, 3, 61
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r0, %r11, %r12
	or %r10, %r10, %r0
	rldicl %r11, %r11, 56, 8
	li %r12, 2
	xor %r12, %r12, %r9
	rldicr %r12, %r12, 61, 2
	rldicl %r12, %r12, 3, 61
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r0, %r11, %r12
	or %r10, %r10, %r0
	rldicl %r11, %r11, 56, 8
	li %r12, 3
	xor %r12, %r12, %r9
	rldicr %r12, %r12, 61, 2
	rldicl %r12, %r12, 3, 61
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r0, %r11, %r12
	or %r10, %r10, %r0
	rldicl %r11, %r11, 56, 8
	li %r12, 4
	xor %r12, %r12, %r9
	rldicr %r12, %r12, 61, 2
	rldicl %r12, %r12, 3, 61
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r0, %r11, %r12
	or %r10, %r10, %r0
	rldicl %r11, %r11, 56, 8
	li %r12, 5
	xor %r12, %r12, %r9
	rldicr %r12, %r12, 61, 2
	rldicl %r12, %r12, 3, 61
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r0, %r11, %r12
	or %r10, %r10, %r0
	rldicl %r11, %r11, 56, 8
	li %r12, 6
	xor %r12, %r12, %r9
	rldicr %r12, %r12, 61, 2
	rldicl %r12, %r12, 3, 61
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r0, %r11, %r12
	or %r10, %r10, %r0
	rldicl %r11, %r11, 56, 8
	li %r12, 7
	xor %r12, %r12, %r9
	rldicr %r12, %r12, 61, 2
	rldicl %r12, %r12, 3, 61
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	subf %r12, %r12, %r8
	and %r0, %r11, %r12
	or %r10, %r10, %r0
	rldicl %r11, %r11, 56, 8
	rldicr %r10, %r10, 56, 7
	rldicl %r10, %r10, 8, 56
	lbz %r0, 0(%r4)
	xor %r0, %r0, %r10
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 22b
	stb %r6, 256(%r3)
	stb %r7, 257(%r3)
	b 21f
20:
21:
	blr
