// The functions of `src/idea.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_idea_expand_key:
	ld %r12, 0(%r3)
	rldicl %r12, %r12, 56, 0
	lis %r11, 255
	ori %r11, %r11, 255
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 255
	ori %r11, %r11, 255
	and %r10, %r12, %r11
	ld %r12, 0(%r3)
	rldicl %r12, %r12, 8, 0
	lis %r11, -256
	ori %r11, %r11, 65280
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 65280
	ori %r11, %r11, 65280
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	std %r10, 0(%r4)
	ld %r12, 8(%r3)
	rldicl %r12, %r12, 56, 0
	lis %r11, 255
	ori %r11, %r11, 255
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 255
	ori %r11, %r11, 255
	and %r10, %r12, %r11
	ld %r12, 8(%r3)
	rldicl %r12, %r12, 8, 0
	lis %r11, -256
	ori %r11, %r11, 65280
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 65280
	ori %r11, %r11, 65280
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	std %r10, 8(%r4)
	ld %r12, 0(%r3)
	rldicl %r12, %r12, 17, 0
	lis %r11, 0
	ori %r11, %r11, 0
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 1
	ori %r11, %r11, 1
	and %r10, %r12, %r11
	ld %r12, 0(%r3)
	rldicl %r12, %r12, 33, 0
	lis %r11, 0
	ori %r11, %r11, 0
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 510
	ori %r11, %r11, 510
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	ld %r12, 0(%r3)
	rldicl %r12, %r12, 49, 0
	lis %r11, 0
	ori %r11, %r11, 65024
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 65024
	ori %r11, %r11, 65024
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	ld %r12, 8(%r3)
	rldicl %r12, %r12, 17, 0
	lis %r11, 1
	ori %r11, %r11, 1
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 0
	ori %r11, %r11, 0
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	ld %r12, 8(%r3)
	rldicl %r12, %r12, 33, 0
	lis %r11, 510
	ori %r11, %r11, 510
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 0
	ori %r11, %r11, 0
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	ld %r12, 8(%r3)
	rldicl %r12, %r12, 49, 0
	lis %r11, -512
	ori %r11, %r11, 0
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 0
	ori %r11, %r11, 0
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	std %r10, 16(%r4)
	ld %r12, 8(%r3)
	rldicl %r12, %r12, 17, 0
	lis %r11, 0
	ori %r11, %r11, 0
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 1
	ori %r11, %r11, 1
	and %r10, %r12, %r11
	ld %r12, 8(%r3)
	rldicl %r12, %r12, 33, 0
	lis %r11, 0
	ori %r11, %r11, 0
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 510
	ori %r11, %r11, 510
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	ld %r12, 8(%r3)
	rldicl %r12, %r12, 49, 0
	lis %r11, 0
	ori %r11, %r11, 65024
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 65024
	ori %r11, %r11, 65024
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	ld %r12, 0(%r3)
	rldicl %r12, %r12, 17, 0
	lis %r11, 1
	ori %r11, %r11, 1
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 0
	ori %r11, %r11, 0
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	ld %r12, 0(%r3)
	rldicl %r12, %r12, 33, 0
	lis %r11, 510
	ori %r11, %r11, 510
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 0
	ori %r11, %r11, 0
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	ld %r12, 0(%r3)
	rldicl %r12, %r12, 49, 0
	lis %r11, -512
	ori %r11, %r11, 0
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 0
	ori %r11, %r11, 0
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	std %r10, 24(%r4)
	ld %r12, 8(%r3)
	rldicl %r12, %r12, 58, 0
	lis %r11, 3
	ori %r11, %r11, 3
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 3
	ori %r11, %r11, 3
	and %r10, %r12, %r11
	ld %r12, 0(%r3)
	rldicl %r12, %r12, 10, 0
	lis %r11, 0
	ori %r11, %r11, 0
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 0
	ori %r11, %r11, 1020
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	ld %r12, 0(%r3)
	rldicl %r12, %r12, 26, 0
	lis %r11, 0
	ori %r11, %r11, 0
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 0
	ori %r11, %r11, 64512
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	ld %r12, 8(%r3)
	rldicl %r12, %r12, 10, 0
	lis %r11, 1020
	ori %r11, %r11, 1020
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 1020
	ori %r11, %r11, 0
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	ld %r12, 8(%r3)
	rldicl %r12, %r12, 26, 0
	lis %r11, -1024
	ori %r11, %r11, 64512
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 64512
	ori %r11, %r11, 0
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	std %r10, 32(%r4)
	ld %r12, 0(%r3)
	rldicl %r12, %r12, 58, 0
	lis %r11, 3
	ori %r11, %r11, 3
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 3
	ori %r11, %r11, 3
	and %r10, %r12, %r11
	ld %r12, 8(%r3)
	rldicl %r12, %r12, 10, 0
	lis %r11, 0
	ori %r11, %r11, 0
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 0
	ori %r11, %r11, 1020
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	ld %r12, 8(%r3)
	rldicl %r12, %r12, 26, 0
	lis %r11, 0
	ori %r11, %r11, 0
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 0
	ori %r11, %r11, 64512
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	ld %r12, 0(%r3)
	rldicl %r12, %r12, 10, 0
	lis %r11, 1020
	ori %r11, %r11, 1020
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 1020
	ori %r11, %r11, 0
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	ld %r12, 0(%r3)
	rldicl %r12, %r12, 26, 0
	lis %r11, -1024
	ori %r11, %r11, 64512
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 64512
	ori %r11, %r11, 0
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	std %r10, 40(%r4)
	ld %r12, 8(%r3)
	rldicl %r12, %r12, 35, 0
	lis %r11, 0
	ori %r11, %r11, 7
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 7
	ori %r11, %r11, 7
	and %r10, %r12, %r11
	ld %r12, 8(%r3)
	rldicl %r12, %r12, 51, 0
	lis %r11, 0
	ori %r11, %r11, 2040
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 2040
	ori %r11, %r11, 2040
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	ld %r12, 8(%r3)
	rldicl %r12, %r12, 3, 0
	lis %r11, -2048
	ori %r11, %r11, 63488
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 63488
	ori %r11, %r11, 63488
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	ld %r12, 0(%r3)
	rldicl %r12, %r12, 35, 0
	lis %r11, 7
	ori %r11, %r11, 0
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 0
	ori %r11, %r11, 0
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	ld %r12, 0(%r3)
	rldicl %r12, %r12, 51, 0
	lis %r11, 2040
	ori %r11, %r11, 0
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 0
	ori %r11, %r11, 0
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	std %r10, 48(%r4)
	ld %r12, 0(%r3)
	rldicl %r12, %r12, 35, 0
	lis %r11, 0
	ori %r11, %r11, 7
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 7
	ori %r11, %r11, 7
	and %r10, %r12, %r11
	ld %r12, 0(%r3)
	rldicl %r12, %r12, 51, 0
	lis %r11, 0
	ori %r11, %r11, 2040
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 2040
	ori %r11, %r11, 2040
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	ld %r12, 0(%r3)
	rldicl %r12, %r12, 3, 0
	lis %r11, -2048
	ori %r11, %r11, 63488
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 63488
	ori %r11, %r11, 63488
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	ld %r12, 8(%r3)
	rldicl %r12, %r12, 35, 0
	lis %r11, 7
	ori %r11, %r11, 0
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 0
	ori %r11, %r11, 0
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	ld %r12, 8(%r3)
	rldicl %r12, %r12, 51, 0
	lis %r11, 2040
	ori %r11, %r11, 0
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 0
	ori %r11, %r11, 0
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	std %r10, 56(%r4)
	ld %r12, 8(%r3)
	rldicl %r12, %r12, 12, 0
	lis %r11, 0
	ori %r11, %r11, 0
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 0
	ori %r11, %r11, 15
	and %r10, %r12, %r11
	ld %r12, 8(%r3)
	rldicl %r12, %r12, 28, 0
	lis %r11, 0
	ori %r11, %r11, 0
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 4080
	ori %r11, %r11, 4080
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	ld %r12, 8(%r3)
	rldicl %r12, %r12, 44, 0
	lis %r11, 0
	ori %r11, %r11, 0
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 61440
	ori %r11, %r11, 61440
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	ld %r12, 0(%r3)
	rldicl %r12, %r12, 12, 0
	lis %r11, 15
	ori %r11, %r11, 15
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 15
	ori %r11, %r11, 0
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	ld %r12, 0(%r3)
	rldicl %r12, %r12, 28, 0
	lis %r11, 4080
	ori %r11, %r11, 4080
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 0
	ori %r11, %r11, 0
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	ld %r12, 0(%r3)
	rldicl %r12, %r12, 44, 0
	lis %r11, -4096
	ori %r11, %r11, 61440
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 0
	ori %r11, %r11, 0
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	std %r10, 64(%r4)
	ld %r12, 0(%r3)
	rldicl %r12, %r12, 12, 0
	lis %r11, 0
	ori %r11, %r11, 0
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 0
	ori %r11, %r11, 15
	and %r10, %r12, %r11
	ld %r12, 0(%r3)
	rldicl %r12, %r12, 28, 0
	lis %r11, 0
	ori %r11, %r11, 0
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 4080
	ori %r11, %r11, 4080
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	ld %r12, 0(%r3)
	rldicl %r12, %r12, 44, 0
	lis %r11, 0
	ori %r11, %r11, 0
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 61440
	ori %r11, %r11, 61440
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	ld %r12, 8(%r3)
	rldicl %r12, %r12, 12, 0
	lis %r11, 15
	ori %r11, %r11, 15
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 15
	ori %r11, %r11, 0
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	ld %r12, 8(%r3)
	rldicl %r12, %r12, 28, 0
	lis %r11, 4080
	ori %r11, %r11, 4080
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 0
	ori %r11, %r11, 0
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	ld %r12, 8(%r3)
	rldicl %r12, %r12, 44, 0
	lis %r11, -4096
	ori %r11, %r11, 61440
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 0
	ori %r11, %r11, 0
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	std %r10, 72(%r4)
	ld %r12, 0(%r3)
	rldicl %r12, %r12, 53, 0
	lis %r11, 31
	ori %r11, %r11, 31
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 31
	ori %r11, %r11, 31
	and %r10, %r12, %r11
	ld %r12, 0(%r3)
	rldicl %r12, %r12, 5, 0
	lis %r11, 8160
	ori %r11, %r11, 8160
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 8160
	ori %r11, %r11, 8160
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	ld %r12, 8(%r3)
	rldicl %r12, %r12, 21, 0
	lis %r11, 0
	ori %r11, %r11, 0
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 0
	ori %r11, %r11, 57344
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	ld %r12, 0(%r3)
	rldicl %r12, %r12, 21, 0
	lis %r11, -8192
	ori %r11, %r11, 57344
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 57344
	ori %r11, %r11, 0
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	std %r10, 80(%r4)
	ld %r12, 8(%r3)
	rldicl %r12, %r12, 53, 0
	lis %r11, 31
	ori %r11, %r11, 31
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 31
	ori %r11, %r11, 31
	and %r10, %r12, %r11
	ld %r12, 8(%r3)
	rldicl %r12, %r12, 5, 0
	lis %r11, 8160
	ori %r11, %r11, 8160
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 8160
	ori %r11, %r11, 8160
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	ld %r12, 0(%r3)
	rldicl %r12, %r12, 21, 0
	lis %r11, 0
	ori %r11, %r11, 0
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 0
	ori %r11, %r11, 57344
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	ld %r12, 8(%r3)
	rldicl %r12, %r12, 21, 0
	lis %r11, -8192
	ori %r11, %r11, 57344
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 57344
	ori %r11, %r11, 0
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	std %r10, 88(%r4)
	ld %r12, 0(%r3)
	rldicl %r12, %r12, 30, 0
	lis %r11, 0
	ori %r11, %r11, 0
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 63
	ori %r11, %r11, 63
	and %r10, %r12, %r11
	ld %r12, 0(%r3)
	rldicl %r12, %r12, 46, 0
	lis %r11, 0
	ori %r11, %r11, 16320
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 16320
	ori %r11, %r11, 16320
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	ld %r12, 0(%r3)
	rldicl %r12, %r12, 62, 0
	lis %r11, 0
	ori %r11, %r11, 49152
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 49152
	ori %r11, %r11, 49152
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	ld %r12, 8(%r3)
	rldicl %r12, %r12, 30, 0
	lis %r11, 63
	ori %r11, %r11, 63
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 0
	ori %r11, %r11, 0
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	ld %r12, 8(%r3)
	rldicl %r12, %r12, 46, 0
	lis %r11, 16320
	ori %r11, %r11, 0
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 0
	ori %r11, %r11, 0
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	ld %r12, 8(%r3)
	rldicl %r12, %r12, 62, 0
	lis %r11, -16384
	ori %r11, %r11, 0
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 0
	ori %r11, %r11, 0
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	std %r10, 96(%r4)
	blr

vg_idea_invert_key:
	li %r0, 0
	ori %r0, %r0, 65535
	lwz %r6, 96(%r3)
	or %r7, %r6, %r6
	li %r5, 15
20:
	or %r11, %r7, %r7
	or %r12, %r7, %r7
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r11, %r12, %r12
	or %r12, %r6, %r6
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r7, %r12, %r12
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 20b
	or %r12, %r7, %r7
	or %r8, %r12, %r12
	lwz %r9, 98(%r3)
	li %r12, 0
	subf %r12, %r9, %r12
	and %r12, %r12, %r0
	rldicr %r12, %r12, 16, 47
	or %r8, %r8, %r12
	lwz %r9, 100(%r3)
	li %r12, 0
	subf %r12, %r9, %r12
	and %r12, %r12, %r0
	rldicr %r12, %r12, 32, 31
	or %r8, %r8, %r12
	lwz %r6, 100(%r3)
	rldicl %r6, %r6, 48, 16
	or %r7, %r6, %r6
	li %r5, 15
21:
	or %r11, %r7, %r7
	or %r12, %r7, %r7
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r11, %r12, %r12
	or %r12, %r6, %r6
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r7, %r12, %r12
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 21b
	or %r12, %r7, %r7
	rldicr %r12, %r12, 48, 15
	or %r8, %r8, %r12
	std %r8, 0(%r4)
	lwz %r12, 92(%r3)
	and %r12, %r12, %r0
	or %r8, %r12, %r12
	lwz %r12, 94(%r3)
	and %r12, %r12, %r0
	rldicr %r12, %r12, 16, 47
	or %r8, %r8, %r12
	lwz %r6, 84(%r3)
	or %r7, %r6, %r6
	li %r5, 15
22:
	or %r11, %r7, %r7
	or %r12, %r7, %r7
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r11, %r12, %r12
	or %r12, %r6, %r6
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r7, %r12, %r12
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 22b
	or %r12, %r7, %r7
	rldicr %r12, %r12, 32, 31
	or %r8, %r8, %r12
	lwz %r9, 88(%r3)
	li %r12, 0
	subf %r12, %r9, %r12
	and %r12, %r12, %r0
	rldicr %r12, %r12, 48, 15
	or %r8, %r8, %r12
	std %r8, 8(%r4)
	lwz %r9, 86(%r3)
	li %r12, 0
	subf %r12, %r9, %r12
	and %r12, %r12, %r0
	or %r8, %r12, %r12
	lwz %r6, 90(%r3)
	or %r7, %r6, %r6
	li %r5, 15
23:
	or %r11, %r7, %r7
	or %r12, %r7, %r7
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r11, %r12, %r12
	or %r12, %r6, %r6
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r7, %r12, %r12
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 23b
	or %r12, %r7, %r7
	rldicr %r12, %r12, 16, 47
	or %r8, %r8, %r12
	lwz %r12, 80(%r3)
	and %r12, %r12, %r0
	rldicr %r12, %r12, 32, 31
	or %r8, %r8, %r12
	lwz %r12, 82(%r3)
	and %r12, %r12, %r0
	rldicr %r12, %r12, 48, 15
	or %r8, %r8, %r12
	std %r8, 16(%r4)
	lwz %r6, 72(%r3)
	or %r7, %r6, %r6
	li %r5, 15
24:
	or %r11, %r7, %r7
	or %r12, %r7, %r7
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r11, %r12, %r12
	or %r12, %r6, %r6
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r7, %r12, %r12
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 24b
	or %r12, %r7, %r7
	or %r8, %r12, %r12
	lwz %r9, 76(%r3)
	li %r12, 0
	subf %r12, %r9, %r12
	and %r12, %r12, %r0
	rldicr %r12, %r12, 16, 47
	or %r8, %r8, %r12
	lwz %r9, 74(%r3)
	li %r12, 0
	subf %r12, %r9, %r12
	and %r12, %r12, %r0
	rldicr %r12, %r12, 32, 31
	or %r8, %r8, %r12
	lwz %r6, 78(%r3)
	or %r7, %r6, %r6
	li %r5, 15
25:
	or %r11, %r7, %r7
	or %r12, %r7, %r7
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r11, %r12, %r12
	or %r12, %r6, %r6
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r7, %r12, %r12
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 25b
	or %r12, %r7, %r7
	rldicr %r12, %r12, 48, 15
	or %r8, %r8, %r12
	std %r8, 24(%r4)
	lwz %r12, 68(%r3)
	and %r12, %r12, %r0
	or %r8, %r12, %r12
	lwz %r12, 70(%r3)
	and %r12, %r12, %r0
	rldicr %r12, %r12, 16, 47
	or %r8, %r8, %r12
	lwz %r6, 60(%r3)
	or %r7, %r6, %r6
	li %r5, 15
26:
	or %r11, %r7, %r7
	or %r12, %r7, %r7
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r11, %r12, %r12
	or %r12, %r6, %r6
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r7, %r12, %r12
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 26b
	or %r12, %r7, %r7
	rldicr %r12, %r12, 32, 31
	or %r8, %r8, %r12
	lwz %r9, 64(%r3)
	li %r12, 0
	subf %r12, %r9, %r12
	and %r12, %r12, %r0
	rldicr %r12, %r12, 48, 15
	or %r8, %r8, %r12
	std %r8, 32(%r4)
	lwz %r9, 62(%r3)
	li %r12, 0
	subf %r12, %r9, %r12
	and %r12, %r12, %r0
	or %r8, %r12, %r12
	lwz %r6, 66(%r3)
	or %r7, %r6, %r6
	li %r5, 15
27:
	or %r11, %r7, %r7
	or %r12, %r7, %r7
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r11, %r12, %r12
	or %r12, %r6, %r6
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r7, %r12, %r12
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 27b
	or %r12, %r7, %r7
	rldicr %r12, %r12, 16, 47
	or %r8, %r8, %r12
	lwz %r12, 56(%r3)
	and %r12, %r12, %r0
	rldicr %r12, %r12, 32, 31
	or %r8, %r8, %r12
	lwz %r12, 58(%r3)
	and %r12, %r12, %r0
	rldicr %r12, %r12, 48, 15
	or %r8, %r8, %r12
	std %r8, 40(%r4)
	lwz %r6, 48(%r3)
	or %r7, %r6, %r6
	li %r5, 15
28:
	or %r11, %r7, %r7
	or %r12, %r7, %r7
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r11, %r12, %r12
	or %r12, %r6, %r6
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r7, %r12, %r12
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 28b
	or %r12, %r7, %r7
	or %r8, %r12, %r12
	lwz %r9, 52(%r3)
	li %r12, 0
	subf %r12, %r9, %r12
	and %r12, %r12, %r0
	rldicr %r12, %r12, 16, 47
	or %r8, %r8, %r12
	lwz %r9, 50(%r3)
	li %r12, 0
	subf %r12, %r9, %r12
	and %r12, %r12, %r0
	rldicr %r12, %r12, 32, 31
	or %r8, %r8, %r12
	lwz %r6, 54(%r3)
	or %r7, %r6, %r6
	li %r5, 15
29:
	or %r11, %r7, %r7
	or %r12, %r7, %r7
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r11, %r12, %r12
	or %r12, %r6, %r6
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r7, %r12, %r12
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 29b
	or %r12, %r7, %r7
	rldicr %r12, %r12, 48, 15
	or %r8, %r8, %r12
	std %r8, 48(%r4)
	lwz %r12, 44(%r3)
	and %r12, %r12, %r0
	or %r8, %r12, %r12
	lwz %r12, 46(%r3)
	and %r12, %r12, %r0
	rldicr %r12, %r12, 16, 47
	or %r8, %r8, %r12
	lwz %r6, 36(%r3)
	or %r7, %r6, %r6
	li %r5, 15
210:
	or %r11, %r7, %r7
	or %r12, %r7, %r7
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r11, %r12, %r12
	or %r12, %r6, %r6
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r7, %r12, %r12
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 210b
	or %r12, %r7, %r7
	rldicr %r12, %r12, 32, 31
	or %r8, %r8, %r12
	lwz %r9, 40(%r3)
	li %r12, 0
	subf %r12, %r9, %r12
	and %r12, %r12, %r0
	rldicr %r12, %r12, 48, 15
	or %r8, %r8, %r12
	std %r8, 56(%r4)
	lwz %r9, 38(%r3)
	li %r12, 0
	subf %r12, %r9, %r12
	and %r12, %r12, %r0
	or %r8, %r12, %r12
	lwz %r6, 42(%r3)
	or %r7, %r6, %r6
	li %r5, 15
211:
	or %r11, %r7, %r7
	or %r12, %r7, %r7
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r11, %r12, %r12
	or %r12, %r6, %r6
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r7, %r12, %r12
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 211b
	or %r12, %r7, %r7
	rldicr %r12, %r12, 16, 47
	or %r8, %r8, %r12
	lwz %r12, 32(%r3)
	and %r12, %r12, %r0
	rldicr %r12, %r12, 32, 31
	or %r8, %r8, %r12
	lwz %r12, 34(%r3)
	and %r12, %r12, %r0
	rldicr %r12, %r12, 48, 15
	or %r8, %r8, %r12
	std %r8, 64(%r4)
	lwz %r6, 24(%r3)
	or %r7, %r6, %r6
	li %r5, 15
212:
	or %r11, %r7, %r7
	or %r12, %r7, %r7
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r11, %r12, %r12
	or %r12, %r6, %r6
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r7, %r12, %r12
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 212b
	or %r12, %r7, %r7
	or %r8, %r12, %r12
	lwz %r9, 28(%r3)
	li %r12, 0
	subf %r12, %r9, %r12
	and %r12, %r12, %r0
	rldicr %r12, %r12, 16, 47
	or %r8, %r8, %r12
	lwz %r9, 26(%r3)
	li %r12, 0
	subf %r12, %r9, %r12
	and %r12, %r12, %r0
	rldicr %r12, %r12, 32, 31
	or %r8, %r8, %r12
	lwz %r6, 30(%r3)
	or %r7, %r6, %r6
	li %r5, 15
213:
	or %r11, %r7, %r7
	or %r12, %r7, %r7
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r11, %r12, %r12
	or %r12, %r6, %r6
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r7, %r12, %r12
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 213b
	or %r12, %r7, %r7
	rldicr %r12, %r12, 48, 15
	or %r8, %r8, %r12
	std %r8, 72(%r4)
	lwz %r12, 20(%r3)
	and %r12, %r12, %r0
	or %r8, %r12, %r12
	lwz %r12, 22(%r3)
	and %r12, %r12, %r0
	rldicr %r12, %r12, 16, 47
	or %r8, %r8, %r12
	lwz %r6, 12(%r3)
	or %r7, %r6, %r6
	li %r5, 15
214:
	or %r11, %r7, %r7
	or %r12, %r7, %r7
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r11, %r12, %r12
	or %r12, %r6, %r6
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r7, %r12, %r12
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 214b
	or %r12, %r7, %r7
	rldicr %r12, %r12, 32, 31
	or %r8, %r8, %r12
	lwz %r9, 16(%r3)
	li %r12, 0
	subf %r12, %r9, %r12
	and %r12, %r12, %r0
	rldicr %r12, %r12, 48, 15
	or %r8, %r8, %r12
	std %r8, 80(%r4)
	lwz %r9, 14(%r3)
	li %r12, 0
	subf %r12, %r9, %r12
	and %r12, %r12, %r0
	or %r8, %r12, %r12
	lwz %r6, 18(%r3)
	or %r7, %r6, %r6
	li %r5, 15
215:
	or %r11, %r7, %r7
	or %r12, %r7, %r7
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r11, %r12, %r12
	or %r12, %r6, %r6
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r7, %r12, %r12
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 215b
	or %r12, %r7, %r7
	rldicr %r12, %r12, 16, 47
	or %r8, %r8, %r12
	lwz %r12, 8(%r3)
	and %r12, %r12, %r0
	rldicr %r12, %r12, 32, 31
	or %r8, %r8, %r12
	lwz %r12, 10(%r3)
	and %r12, %r12, %r0
	rldicr %r12, %r12, 48, 15
	or %r8, %r8, %r12
	std %r8, 88(%r4)
	lwz %r6, 0(%r3)
	or %r7, %r6, %r6
	li %r5, 15
216:
	or %r11, %r7, %r7
	or %r12, %r7, %r7
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r11, %r12, %r12
	or %r12, %r6, %r6
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r7, %r12, %r12
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 216b
	or %r12, %r7, %r7
	or %r8, %r12, %r12
	lwz %r9, 2(%r3)
	li %r12, 0
	subf %r12, %r9, %r12
	and %r12, %r12, %r0
	rldicr %r12, %r12, 16, 47
	or %r8, %r8, %r12
	lwz %r9, 4(%r3)
	li %r12, 0
	subf %r12, %r9, %r12
	and %r12, %r12, %r0
	rldicr %r12, %r12, 32, 31
	or %r8, %r8, %r12
	lwz %r6, 6(%r3)
	or %r7, %r6, %r6
	li %r5, 15
217:
	or %r11, %r7, %r7
	or %r12, %r7, %r7
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r11, %r12, %r12
	or %r12, %r6, %r6
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r7, %r12, %r12
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 217b
	or %r12, %r7, %r7
	rldicr %r12, %r12, 48, 15
	or %r8, %r8, %r12
	std %r8, 96(%r4)
	blr

vg_idea_ecb:
	li %r0, 0
	ori %r0, %r0, 65535
	cmpldi %cr0, %r5, 0
	beq %cr0, 20f
22:
	lbz %r6, 0(%r4)
	rldicr %r6, %r6, 8, 55
	lbz %r11, 1(%r4)
	or %r6, %r6, %r11
	lbz %r7, 2(%r4)
	rldicr %r7, %r7, 8, 55
	lbz %r11, 3(%r4)
	or %r7, %r7, %r11
	lbz %r8, 4(%r4)
	rldicr %r8, %r8, 8, 55
	lbz %r11, 5(%r4)
	or %r8, %r8, %r11
	lbz %r9, 6(%r4)
	rldicr %r9, %r9, 8, 55
	lbz %r11, 7(%r4)
	or %r9, %r9, %r11
	or %r11, %r6, %r6
	lwz %r12, 0(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r6, %r12, %r12
	or %r11, %r9, %r9
	lwz %r12, 6(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r9, %r12, %r12
	lwz %r12, 2(%r3)
	add %r7, %r7, %r12
	and %r7, %r7, %r0
	lwz %r12, 4(%r3)
	add %r8, %r8, %r12
	and %r8, %r8, %r0
	xor %r11, %r6, %r8
	lwz %r12, 8(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r10, %r12, %r12
	xor %r11, %r7, %r9
	add %r11, %r11, %r10
	lwz %r12, 10(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	add %r10, %r10, %r12
	and %r10, %r10, %r0
	xor %r6, %r6, %r12
	xor %r8, %r8, %r12
	xor %r7, %r7, %r10
	xor %r9, %r9, %r10
	or %r11, %r7, %r7
	or %r7, %r8, %r8
	or %r8, %r11, %r11
	or %r11, %r6, %r6
	lwz %r12, 12(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r6, %r12, %r12
	or %r11, %r9, %r9
	lwz %r12, 18(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r9, %r12, %r12
	lwz %r12, 14(%r3)
	add %r7, %r7, %r12
	and %r7, %r7, %r0
	lwz %r12, 16(%r3)
	add %r8, %r8, %r12
	and %r8, %r8, %r0
	xor %r11, %r6, %r8
	lwz %r12, 20(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r10, %r12, %r12
	xor %r11, %r7, %r9
	add %r11, %r11, %r10
	lwz %r12, 22(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	add %r10, %r10, %r12
	and %r10, %r10, %r0
	xor %r6, %r6, %r12
	xor %r8, %r8, %r12
	xor %r7, %r7, %r10
	xor %r9, %r9, %r10
	or %r11, %r7, %r7
	or %r7, %r8, %r8
	or %r8, %r11, %r11
	or %r11, %r6, %r6
	lwz %r12, 24(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r6, %r12, %r12
	or %r11, %r9, %r9
	lwz %r12, 30(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r9, %r12, %r12
	lwz %r12, 26(%r3)
	add %r7, %r7, %r12
	and %r7, %r7, %r0
	lwz %r12, 28(%r3)
	add %r8, %r8, %r12
	and %r8, %r8, %r0
	xor %r11, %r6, %r8
	lwz %r12, 32(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r10, %r12, %r12
	xor %r11, %r7, %r9
	add %r11, %r11, %r10
	lwz %r12, 34(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	add %r10, %r10, %r12
	and %r10, %r10, %r0
	xor %r6, %r6, %r12
	xor %r8, %r8, %r12
	xor %r7, %r7, %r10
	xor %r9, %r9, %r10
	or %r11, %r7, %r7
	or %r7, %r8, %r8
	or %r8, %r11, %r11
	or %r11, %r6, %r6
	lwz %r12, 36(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r6, %r12, %r12
	or %r11, %r9, %r9
	lwz %r12, 42(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r9, %r12, %r12
	lwz %r12, 38(%r3)
	add %r7, %r7, %r12
	and %r7, %r7, %r0
	lwz %r12, 40(%r3)
	add %r8, %r8, %r12
	and %r8, %r8, %r0
	xor %r11, %r6, %r8
	lwz %r12, 44(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r10, %r12, %r12
	xor %r11, %r7, %r9
	add %r11, %r11, %r10
	lwz %r12, 46(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	add %r10, %r10, %r12
	and %r10, %r10, %r0
	xor %r6, %r6, %r12
	xor %r8, %r8, %r12
	xor %r7, %r7, %r10
	xor %r9, %r9, %r10
	or %r11, %r7, %r7
	or %r7, %r8, %r8
	or %r8, %r11, %r11
	or %r11, %r6, %r6
	lwz %r12, 48(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r6, %r12, %r12
	or %r11, %r9, %r9
	lwz %r12, 54(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r9, %r12, %r12
	lwz %r12, 50(%r3)
	add %r7, %r7, %r12
	and %r7, %r7, %r0
	lwz %r12, 52(%r3)
	add %r8, %r8, %r12
	and %r8, %r8, %r0
	xor %r11, %r6, %r8
	lwz %r12, 56(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r10, %r12, %r12
	xor %r11, %r7, %r9
	add %r11, %r11, %r10
	lwz %r12, 58(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	add %r10, %r10, %r12
	and %r10, %r10, %r0
	xor %r6, %r6, %r12
	xor %r8, %r8, %r12
	xor %r7, %r7, %r10
	xor %r9, %r9, %r10
	or %r11, %r7, %r7
	or %r7, %r8, %r8
	or %r8, %r11, %r11
	or %r11, %r6, %r6
	lwz %r12, 60(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r6, %r12, %r12
	or %r11, %r9, %r9
	lwz %r12, 66(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r9, %r12, %r12
	lwz %r12, 62(%r3)
	add %r7, %r7, %r12
	and %r7, %r7, %r0
	lwz %r12, 64(%r3)
	add %r8, %r8, %r12
	and %r8, %r8, %r0
	xor %r11, %r6, %r8
	lwz %r12, 68(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r10, %r12, %r12
	xor %r11, %r7, %r9
	add %r11, %r11, %r10
	lwz %r12, 70(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	add %r10, %r10, %r12
	and %r10, %r10, %r0
	xor %r6, %r6, %r12
	xor %r8, %r8, %r12
	xor %r7, %r7, %r10
	xor %r9, %r9, %r10
	or %r11, %r7, %r7
	or %r7, %r8, %r8
	or %r8, %r11, %r11
	or %r11, %r6, %r6
	lwz %r12, 72(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r6, %r12, %r12
	or %r11, %r9, %r9
	lwz %r12, 78(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r9, %r12, %r12
	lwz %r12, 74(%r3)
	add %r7, %r7, %r12
	and %r7, %r7, %r0
	lwz %r12, 76(%r3)
	add %r8, %r8, %r12
	and %r8, %r8, %r0
	xor %r11, %r6, %r8
	lwz %r12, 80(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r10, %r12, %r12
	xor %r11, %r7, %r9
	add %r11, %r11, %r10
	lwz %r12, 82(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	add %r10, %r10, %r12
	and %r10, %r10, %r0
	xor %r6, %r6, %r12
	xor %r8, %r8, %r12
	xor %r7, %r7, %r10
	xor %r9, %r9, %r10
	or %r11, %r7, %r7
	or %r7, %r8, %r8
	or %r8, %r11, %r11
	or %r11, %r6, %r6
	lwz %r12, 84(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r6, %r12, %r12
	or %r11, %r9, %r9
	lwz %r12, 90(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r9, %r12, %r12
	lwz %r12, 86(%r3)
	add %r7, %r7, %r12
	and %r7, %r7, %r0
	lwz %r12, 88(%r3)
	add %r8, %r8, %r12
	and %r8, %r8, %r0
	xor %r11, %r6, %r8
	lwz %r12, 92(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r10, %r12, %r12
	xor %r11, %r7, %r9
	add %r11, %r11, %r10
	lwz %r12, 94(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	add %r10, %r10, %r12
	and %r10, %r10, %r0
	xor %r6, %r6, %r12
	xor %r8, %r8, %r12
	xor %r7, %r7, %r10
	xor %r9, %r9, %r10
	or %r11, %r7, %r7
	or %r7, %r8, %r8
	or %r8, %r11, %r11
	or %r11, %r6, %r6
	lwz %r12, 96(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r6, %r12, %r12
	or %r11, %r9, %r9
	lwz %r12, 100(%r3)
	rldicl %r12, %r12, 48, 16
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r9, %r12, %r12
	lwz %r12, 98(%r3)
	add %r8, %r8, %r12
	and %r8, %r8, %r0
	lwz %r12, 100(%r3)
	add %r7, %r7, %r12
	and %r7, %r7, %r0
	stb %r6, 1(%r4)
	rldicl %r11, %r6, 56, 8
	stb %r11, 0(%r4)
	stb %r8, 3(%r4)
	rldicl %r11, %r8, 56, 8
	stb %r11, 2(%r4)
	stb %r7, 5(%r4)
	rldicl %r11, %r7, 56, 8
	stb %r11, 4(%r4)
	stb %r9, 7(%r4)
	rldicl %r11, %r9, 56, 8
	stb %r11, 6(%r4)
	addi %r4, %r4, 8
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 22b
	b 21f
20:
21:
	blr
