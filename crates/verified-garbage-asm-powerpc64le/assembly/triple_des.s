// The functions of `src/triple_des.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_triple_des_expand_key:
	li %r8, 0
	ldbrx %r8, %r3, %r8
	li %r9, 0
	li %r11, 1
	rldicl %r10, %r8, 57, 7
	and %r10, %r10, %r11
	rldicl %r10, %r10, 55, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 49, 15
	and %r10, %r10, %r11
	rldicl %r10, %r10, 54, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 41, 23
	and %r10, %r10, %r11
	rldicl %r10, %r10, 53, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 33, 31
	and %r10, %r10, %r11
	rldicl %r10, %r10, 52, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 25, 39
	and %r10, %r10, %r11
	rldicl %r10, %r10, 51, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 17, 47
	and %r10, %r10, %r11
	rldicl %r10, %r10, 50, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 9, 55
	and %r10, %r10, %r11
	rldicl %r10, %r10, 49, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 1, 63
	and %r10, %r10, %r11
	rldicl %r10, %r10, 48, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 58, 6
	and %r10, %r10, %r11
	rldicl %r10, %r10, 47, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 50, 14
	and %r10, %r10, %r11
	rldicl %r10, %r10, 46, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 42, 22
	and %r10, %r10, %r11
	rldicl %r10, %r10, 45, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 34, 30
	and %r10, %r10, %r11
	rldicl %r10, %r10, 44, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 26, 38
	and %r10, %r10, %r11
	rldicl %r10, %r10, 43, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 18, 46
	and %r10, %r10, %r11
	rldicl %r10, %r10, 42, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 10, 54
	and %r10, %r10, %r11
	rldicl %r10, %r10, 41, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 2, 62
	and %r10, %r10, %r11
	rldicl %r10, %r10, 40, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 59, 5
	and %r10, %r10, %r11
	rldicl %r10, %r10, 39, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 51, 13
	and %r10, %r10, %r11
	rldicl %r10, %r10, 38, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 43, 21
	and %r10, %r10, %r11
	rldicl %r10, %r10, 37, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 35, 29
	and %r10, %r10, %r11
	rldicl %r10, %r10, 36, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 27, 37
	and %r10, %r10, %r11
	rldicl %r10, %r10, 35, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 19, 45
	and %r10, %r10, %r11
	rldicl %r10, %r10, 34, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 11, 53
	and %r10, %r10, %r11
	rldicl %r10, %r10, 33, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 3, 61
	and %r10, %r10, %r11
	rldicl %r10, %r10, 32, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r11
	rldicl %r10, %r10, 31, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 52, 12
	and %r10, %r10, %r11
	rldicl %r10, %r10, 30, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 44, 20
	and %r10, %r10, %r11
	rldicl %r10, %r10, 29, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 36, 28
	and %r10, %r10, %r11
	rldicl %r10, %r10, 28, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 63, 1
	and %r10, %r10, %r11
	rldicl %r10, %r10, 27, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 55, 9
	and %r10, %r10, %r11
	rldicl %r10, %r10, 26, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 47, 17
	and %r10, %r10, %r11
	rldicl %r10, %r10, 25, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 39, 25
	and %r10, %r10, %r11
	rldicl %r10, %r10, 24, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 31, 33
	and %r10, %r10, %r11
	rldicl %r10, %r10, 23, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 23, 41
	and %r10, %r10, %r11
	rldicl %r10, %r10, 22, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 15, 49
	and %r10, %r10, %r11
	rldicl %r10, %r10, 21, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 7, 57
	and %r10, %r10, %r11
	rldicl %r10, %r10, 20, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 62, 2
	and %r10, %r10, %r11
	rldicl %r10, %r10, 19, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 54, 10
	and %r10, %r10, %r11
	rldicl %r10, %r10, 18, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 46, 18
	and %r10, %r10, %r11
	rldicl %r10, %r10, 17, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 38, 26
	and %r10, %r10, %r11
	rldicl %r10, %r10, 16, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 30, 34
	and %r10, %r10, %r11
	rldicl %r10, %r10, 15, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 22, 42
	and %r10, %r10, %r11
	rldicl %r10, %r10, 14, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 14, 50
	and %r10, %r10, %r11
	rldicl %r10, %r10, 13, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 6, 58
	and %r10, %r10, %r11
	rldicl %r10, %r10, 12, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 61, 3
	and %r10, %r10, %r11
	rldicl %r10, %r10, 11, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 53, 11
	and %r10, %r10, %r11
	rldicl %r10, %r10, 10, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 45, 19
	and %r10, %r10, %r11
	rldicl %r10, %r10, 9, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 37, 27
	and %r10, %r10, %r11
	rldicl %r10, %r10, 8, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 29, 35
	and %r10, %r10, %r11
	rldicl %r10, %r10, 7, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 21, 43
	and %r10, %r10, %r11
	rldicl %r10, %r10, 6, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 13, 51
	and %r10, %r10, %r11
	rldicl %r10, %r10, 5, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 5, 59
	and %r10, %r10, %r11
	rldicl %r10, %r10, 4, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 28, 36
	and %r10, %r10, %r11
	rldicl %r10, %r10, 3, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 20, 44
	and %r10, %r10, %r11
	rldicl %r10, %r10, 2, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 12, 52
	and %r10, %r10, %r11
	rldicl %r10, %r10, 1, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 4, 60
	and %r10, %r10, %r11
	xor %r9, %r9, %r10
	rldicl %r0, %r9, 36, 28
	or %r7, %r9, %r9
	rldicr %r7, %r7, 36, 27
	rldicl %r7, %r7, 28, 36
	li %r12, 0
	addi %r6, %r5, 0
20:
	rldicl %r8, %r12, 63, 1
	cmpldi %cr0, %r8, 0
	beq %cr0, 21f
	addi %r8, %r12, -8
	cmpldi %cr0, %r8, 0
	beq %cr0, 23f
	addi %r8, %r12, -15
	cmpldi %cr0, %r8, 0
	beq %cr0, 25f
	rldicl %r8, %r0, 38, 26
	rldicl %r0, %r0, 2, 0
	xor %r0, %r0, %r8
	rldicr %r0, %r0, 36, 27
	rldicl %r0, %r0, 28, 36
	rldicl %r8, %r7, 38, 26
	rldicl %r7, %r7, 2, 0
	xor %r7, %r7, %r8
	rldicr %r7, %r7, 36, 27
	rldicl %r7, %r7, 28, 36
	b 26f
25:
	rldicl %r8, %r0, 37, 27
	rldicl %r0, %r0, 1, 0
	xor %r0, %r0, %r8
	rldicr %r0, %r0, 36, 27
	rldicl %r0, %r0, 28, 36
	rldicl %r8, %r7, 37, 27
	rldicl %r7, %r7, 1, 0
	xor %r7, %r7, %r8
	rldicr %r7, %r7, 36, 27
	rldicl %r7, %r7, 28, 36
26:
	b 24f
23:
	rldicl %r8, %r0, 37, 27
	rldicl %r0, %r0, 1, 0
	xor %r0, %r0, %r8
	rldicr %r0, %r0, 36, 27
	rldicl %r0, %r0, 28, 36
	rldicl %r8, %r7, 37, 27
	rldicl %r7, %r7, 1, 0
	xor %r7, %r7, %r8
	rldicr %r7, %r7, 36, 27
	rldicl %r7, %r7, 28, 36
24:
	b 22f
21:
	rldicl %r8, %r0, 37, 27
	rldicl %r0, %r0, 1, 0
	xor %r0, %r0, %r8
	rldicr %r0, %r0, 36, 27
	rldicl %r0, %r0, 28, 36
	rldicl %r8, %r7, 37, 27
	rldicl %r7, %r7, 1, 0
	xor %r7, %r7, %r8
	rldicr %r7, %r7, 36, 27
	rldicl %r7, %r7, 28, 36
22:
	rldicr %r8, %r0, 28, 35
	xor %r8, %r8, %r7
	li %r9, 0
	li %r11, 1
	rldicl %r10, %r8, 22, 42
	and %r10, %r10, %r11
	rldicl %r10, %r10, 47, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 25, 39
	and %r10, %r10, %r11
	rldicl %r10, %r10, 46, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 19, 45
	and %r10, %r10, %r11
	rldicl %r10, %r10, 45, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 32, 32
	and %r10, %r10, %r11
	rldicl %r10, %r10, 44, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 9, 55
	and %r10, %r10, %r11
	rldicl %r10, %r10, 43, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 13, 51
	and %r10, %r10, %r11
	rldicl %r10, %r10, 42, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 11, 53
	and %r10, %r10, %r11
	rldicl %r10, %r10, 41, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 36, 28
	and %r10, %r10, %r11
	rldicl %r10, %r10, 40, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 23, 41
	and %r10, %r10, %r11
	rldicl %r10, %r10, 39, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 14, 50
	and %r10, %r10, %r11
	rldicl %r10, %r10, 38, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 29, 35
	and %r10, %r10, %r11
	rldicl %r10, %r10, 37, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 18, 46
	and %r10, %r10, %r11
	rldicl %r10, %r10, 36, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 31, 33
	and %r10, %r10, %r11
	rldicl %r10, %r10, 35, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 27, 37
	and %r10, %r10, %r11
	rldicl %r10, %r10, 34, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 20, 44
	and %r10, %r10, %r11
	rldicl %r10, %r10, 33, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 12, 52
	and %r10, %r10, %r11
	rldicl %r10, %r10, 32, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 34, 30
	and %r10, %r10, %r11
	rldicl %r10, %r10, 31, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 16, 48
	and %r10, %r10, %r11
	rldicl %r10, %r10, 30, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 24, 40
	and %r10, %r10, %r11
	rldicl %r10, %r10, 29, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 15, 49
	and %r10, %r10, %r11
	rldicl %r10, %r10, 28, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 35, 29
	and %r10, %r10, %r11
	rldicl %r10, %r10, 27, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 28, 36
	and %r10, %r10, %r11
	rldicl %r10, %r10, 26, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 21, 43
	and %r10, %r10, %r11
	rldicl %r10, %r10, 25, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 10, 54
	and %r10, %r10, %r11
	rldicl %r10, %r10, 24, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 49, 15
	and %r10, %r10, %r11
	rldicl %r10, %r10, 23, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r11
	rldicl %r10, %r10, 22, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 39, 25
	and %r10, %r10, %r11
	rldicl %r10, %r10, 21, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 45, 19
	and %r10, %r10, %r11
	rldicl %r10, %r10, 20, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 55, 9
	and %r10, %r10, %r11
	rldicl %r10, %r10, 19, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 63, 1
	and %r10, %r10, %r11
	rldicl %r10, %r10, 18, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 38, 26
	and %r10, %r10, %r11
	rldicl %r10, %r10, 17, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 48, 16
	and %r10, %r10, %r11
	rldicl %r10, %r10, 16, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 59, 5
	and %r10, %r10, %r11
	rldicl %r10, %r10, 15, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 53, 11
	and %r10, %r10, %r11
	rldicl %r10, %r10, 14, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 41, 23
	and %r10, %r10, %r11
	rldicl %r10, %r10, 13, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 56, 8
	and %r10, %r10, %r11
	rldicl %r10, %r10, 12, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 52, 12
	and %r10, %r10, %r11
	rldicl %r10, %r10, 11, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 57, 7
	and %r10, %r10, %r11
	rldicl %r10, %r10, 10, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 47, 17
	and %r10, %r10, %r11
	rldicl %r10, %r10, 9, 0
	xor %r9, %r9, %r10
	or %r10, %r8, %r8
	and %r10, %r10, %r11
	rldicl %r10, %r10, 8, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 42, 22
	and %r10, %r10, %r11
	rldicl %r10, %r10, 7, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 61, 3
	and %r10, %r10, %r11
	rldicl %r10, %r10, 6, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 54, 10
	and %r10, %r10, %r11
	rldicl %r10, %r10, 5, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 50, 14
	and %r10, %r10, %r11
	rldicl %r10, %r10, 4, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 58, 6
	and %r10, %r10, %r11
	rldicl %r10, %r10, 3, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 44, 20
	and %r10, %r10, %r11
	rldicl %r10, %r10, 2, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 37, 27
	and %r10, %r10, %r11
	rldicl %r10, %r10, 1, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 40, 24
	and %r10, %r10, %r11
	xor %r9, %r9, %r10
	std %r9, 0(%r6)
	addi %r6, %r6, 8
	addi %r12, %r12, 1
	addi %r8, %r12, -16
	cmpldi %cr0, %r8, 0
	bne %cr0, 20b
	li %r8, 8
	ldbrx %r8, %r3, %r8
	li %r9, 0
	li %r11, 1
	rldicl %r10, %r8, 57, 7
	and %r10, %r10, %r11
	rldicl %r10, %r10, 55, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 49, 15
	and %r10, %r10, %r11
	rldicl %r10, %r10, 54, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 41, 23
	and %r10, %r10, %r11
	rldicl %r10, %r10, 53, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 33, 31
	and %r10, %r10, %r11
	rldicl %r10, %r10, 52, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 25, 39
	and %r10, %r10, %r11
	rldicl %r10, %r10, 51, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 17, 47
	and %r10, %r10, %r11
	rldicl %r10, %r10, 50, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 9, 55
	and %r10, %r10, %r11
	rldicl %r10, %r10, 49, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 1, 63
	and %r10, %r10, %r11
	rldicl %r10, %r10, 48, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 58, 6
	and %r10, %r10, %r11
	rldicl %r10, %r10, 47, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 50, 14
	and %r10, %r10, %r11
	rldicl %r10, %r10, 46, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 42, 22
	and %r10, %r10, %r11
	rldicl %r10, %r10, 45, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 34, 30
	and %r10, %r10, %r11
	rldicl %r10, %r10, 44, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 26, 38
	and %r10, %r10, %r11
	rldicl %r10, %r10, 43, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 18, 46
	and %r10, %r10, %r11
	rldicl %r10, %r10, 42, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 10, 54
	and %r10, %r10, %r11
	rldicl %r10, %r10, 41, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 2, 62
	and %r10, %r10, %r11
	rldicl %r10, %r10, 40, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 59, 5
	and %r10, %r10, %r11
	rldicl %r10, %r10, 39, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 51, 13
	and %r10, %r10, %r11
	rldicl %r10, %r10, 38, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 43, 21
	and %r10, %r10, %r11
	rldicl %r10, %r10, 37, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 35, 29
	and %r10, %r10, %r11
	rldicl %r10, %r10, 36, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 27, 37
	and %r10, %r10, %r11
	rldicl %r10, %r10, 35, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 19, 45
	and %r10, %r10, %r11
	rldicl %r10, %r10, 34, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 11, 53
	and %r10, %r10, %r11
	rldicl %r10, %r10, 33, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 3, 61
	and %r10, %r10, %r11
	rldicl %r10, %r10, 32, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r11
	rldicl %r10, %r10, 31, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 52, 12
	and %r10, %r10, %r11
	rldicl %r10, %r10, 30, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 44, 20
	and %r10, %r10, %r11
	rldicl %r10, %r10, 29, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 36, 28
	and %r10, %r10, %r11
	rldicl %r10, %r10, 28, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 63, 1
	and %r10, %r10, %r11
	rldicl %r10, %r10, 27, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 55, 9
	and %r10, %r10, %r11
	rldicl %r10, %r10, 26, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 47, 17
	and %r10, %r10, %r11
	rldicl %r10, %r10, 25, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 39, 25
	and %r10, %r10, %r11
	rldicl %r10, %r10, 24, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 31, 33
	and %r10, %r10, %r11
	rldicl %r10, %r10, 23, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 23, 41
	and %r10, %r10, %r11
	rldicl %r10, %r10, 22, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 15, 49
	and %r10, %r10, %r11
	rldicl %r10, %r10, 21, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 7, 57
	and %r10, %r10, %r11
	rldicl %r10, %r10, 20, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 62, 2
	and %r10, %r10, %r11
	rldicl %r10, %r10, 19, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 54, 10
	and %r10, %r10, %r11
	rldicl %r10, %r10, 18, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 46, 18
	and %r10, %r10, %r11
	rldicl %r10, %r10, 17, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 38, 26
	and %r10, %r10, %r11
	rldicl %r10, %r10, 16, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 30, 34
	and %r10, %r10, %r11
	rldicl %r10, %r10, 15, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 22, 42
	and %r10, %r10, %r11
	rldicl %r10, %r10, 14, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 14, 50
	and %r10, %r10, %r11
	rldicl %r10, %r10, 13, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 6, 58
	and %r10, %r10, %r11
	rldicl %r10, %r10, 12, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 61, 3
	and %r10, %r10, %r11
	rldicl %r10, %r10, 11, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 53, 11
	and %r10, %r10, %r11
	rldicl %r10, %r10, 10, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 45, 19
	and %r10, %r10, %r11
	rldicl %r10, %r10, 9, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 37, 27
	and %r10, %r10, %r11
	rldicl %r10, %r10, 8, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 29, 35
	and %r10, %r10, %r11
	rldicl %r10, %r10, 7, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 21, 43
	and %r10, %r10, %r11
	rldicl %r10, %r10, 6, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 13, 51
	and %r10, %r10, %r11
	rldicl %r10, %r10, 5, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 5, 59
	and %r10, %r10, %r11
	rldicl %r10, %r10, 4, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 28, 36
	and %r10, %r10, %r11
	rldicl %r10, %r10, 3, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 20, 44
	and %r10, %r10, %r11
	rldicl %r10, %r10, 2, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 12, 52
	and %r10, %r10, %r11
	rldicl %r10, %r10, 1, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 4, 60
	and %r10, %r10, %r11
	xor %r9, %r9, %r10
	rldicl %r0, %r9, 36, 28
	or %r7, %r9, %r9
	rldicr %r7, %r7, 36, 27
	rldicl %r7, %r7, 28, 36
	li %r12, 0
	addi %r6, %r5, 128
27:
	rldicl %r8, %r12, 63, 1
	cmpldi %cr0, %r8, 0
	beq %cr0, 28f
	addi %r8, %r12, -8
	cmpldi %cr0, %r8, 0
	beq %cr0, 210f
	addi %r8, %r12, -15
	cmpldi %cr0, %r8, 0
	beq %cr0, 212f
	rldicl %r8, %r0, 38, 26
	rldicl %r0, %r0, 2, 0
	xor %r0, %r0, %r8
	rldicr %r0, %r0, 36, 27
	rldicl %r0, %r0, 28, 36
	rldicl %r8, %r7, 38, 26
	rldicl %r7, %r7, 2, 0
	xor %r7, %r7, %r8
	rldicr %r7, %r7, 36, 27
	rldicl %r7, %r7, 28, 36
	b 213f
212:
	rldicl %r8, %r0, 37, 27
	rldicl %r0, %r0, 1, 0
	xor %r0, %r0, %r8
	rldicr %r0, %r0, 36, 27
	rldicl %r0, %r0, 28, 36
	rldicl %r8, %r7, 37, 27
	rldicl %r7, %r7, 1, 0
	xor %r7, %r7, %r8
	rldicr %r7, %r7, 36, 27
	rldicl %r7, %r7, 28, 36
213:
	b 211f
210:
	rldicl %r8, %r0, 37, 27
	rldicl %r0, %r0, 1, 0
	xor %r0, %r0, %r8
	rldicr %r0, %r0, 36, 27
	rldicl %r0, %r0, 28, 36
	rldicl %r8, %r7, 37, 27
	rldicl %r7, %r7, 1, 0
	xor %r7, %r7, %r8
	rldicr %r7, %r7, 36, 27
	rldicl %r7, %r7, 28, 36
211:
	b 29f
28:
	rldicl %r8, %r0, 37, 27
	rldicl %r0, %r0, 1, 0
	xor %r0, %r0, %r8
	rldicr %r0, %r0, 36, 27
	rldicl %r0, %r0, 28, 36
	rldicl %r8, %r7, 37, 27
	rldicl %r7, %r7, 1, 0
	xor %r7, %r7, %r8
	rldicr %r7, %r7, 36, 27
	rldicl %r7, %r7, 28, 36
29:
	rldicr %r8, %r0, 28, 35
	xor %r8, %r8, %r7
	li %r9, 0
	li %r11, 1
	rldicl %r10, %r8, 22, 42
	and %r10, %r10, %r11
	rldicl %r10, %r10, 47, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 25, 39
	and %r10, %r10, %r11
	rldicl %r10, %r10, 46, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 19, 45
	and %r10, %r10, %r11
	rldicl %r10, %r10, 45, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 32, 32
	and %r10, %r10, %r11
	rldicl %r10, %r10, 44, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 9, 55
	and %r10, %r10, %r11
	rldicl %r10, %r10, 43, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 13, 51
	and %r10, %r10, %r11
	rldicl %r10, %r10, 42, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 11, 53
	and %r10, %r10, %r11
	rldicl %r10, %r10, 41, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 36, 28
	and %r10, %r10, %r11
	rldicl %r10, %r10, 40, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 23, 41
	and %r10, %r10, %r11
	rldicl %r10, %r10, 39, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 14, 50
	and %r10, %r10, %r11
	rldicl %r10, %r10, 38, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 29, 35
	and %r10, %r10, %r11
	rldicl %r10, %r10, 37, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 18, 46
	and %r10, %r10, %r11
	rldicl %r10, %r10, 36, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 31, 33
	and %r10, %r10, %r11
	rldicl %r10, %r10, 35, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 27, 37
	and %r10, %r10, %r11
	rldicl %r10, %r10, 34, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 20, 44
	and %r10, %r10, %r11
	rldicl %r10, %r10, 33, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 12, 52
	and %r10, %r10, %r11
	rldicl %r10, %r10, 32, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 34, 30
	and %r10, %r10, %r11
	rldicl %r10, %r10, 31, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 16, 48
	and %r10, %r10, %r11
	rldicl %r10, %r10, 30, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 24, 40
	and %r10, %r10, %r11
	rldicl %r10, %r10, 29, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 15, 49
	and %r10, %r10, %r11
	rldicl %r10, %r10, 28, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 35, 29
	and %r10, %r10, %r11
	rldicl %r10, %r10, 27, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 28, 36
	and %r10, %r10, %r11
	rldicl %r10, %r10, 26, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 21, 43
	and %r10, %r10, %r11
	rldicl %r10, %r10, 25, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 10, 54
	and %r10, %r10, %r11
	rldicl %r10, %r10, 24, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 49, 15
	and %r10, %r10, %r11
	rldicl %r10, %r10, 23, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r11
	rldicl %r10, %r10, 22, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 39, 25
	and %r10, %r10, %r11
	rldicl %r10, %r10, 21, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 45, 19
	and %r10, %r10, %r11
	rldicl %r10, %r10, 20, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 55, 9
	and %r10, %r10, %r11
	rldicl %r10, %r10, 19, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 63, 1
	and %r10, %r10, %r11
	rldicl %r10, %r10, 18, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 38, 26
	and %r10, %r10, %r11
	rldicl %r10, %r10, 17, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 48, 16
	and %r10, %r10, %r11
	rldicl %r10, %r10, 16, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 59, 5
	and %r10, %r10, %r11
	rldicl %r10, %r10, 15, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 53, 11
	and %r10, %r10, %r11
	rldicl %r10, %r10, 14, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 41, 23
	and %r10, %r10, %r11
	rldicl %r10, %r10, 13, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 56, 8
	and %r10, %r10, %r11
	rldicl %r10, %r10, 12, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 52, 12
	and %r10, %r10, %r11
	rldicl %r10, %r10, 11, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 57, 7
	and %r10, %r10, %r11
	rldicl %r10, %r10, 10, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 47, 17
	and %r10, %r10, %r11
	rldicl %r10, %r10, 9, 0
	xor %r9, %r9, %r10
	or %r10, %r8, %r8
	and %r10, %r10, %r11
	rldicl %r10, %r10, 8, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 42, 22
	and %r10, %r10, %r11
	rldicl %r10, %r10, 7, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 61, 3
	and %r10, %r10, %r11
	rldicl %r10, %r10, 6, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 54, 10
	and %r10, %r10, %r11
	rldicl %r10, %r10, 5, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 50, 14
	and %r10, %r10, %r11
	rldicl %r10, %r10, 4, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 58, 6
	and %r10, %r10, %r11
	rldicl %r10, %r10, 3, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 44, 20
	and %r10, %r10, %r11
	rldicl %r10, %r10, 2, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 37, 27
	and %r10, %r10, %r11
	rldicl %r10, %r10, 1, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 40, 24
	and %r10, %r10, %r11
	xor %r9, %r9, %r10
	std %r9, 0(%r6)
	addi %r6, %r6, 8
	addi %r12, %r12, 1
	addi %r8, %r12, -16
	cmpldi %cr0, %r8, 0
	bne %cr0, 27b
	addi %r8, %r4, -16
	cmpldi %cr0, %r8, 0
	beq %cr0, 214f
	li %r8, 16
	ldbrx %r8, %r3, %r8
	li %r9, 0
	li %r11, 1
	rldicl %r10, %r8, 57, 7
	and %r10, %r10, %r11
	rldicl %r10, %r10, 55, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 49, 15
	and %r10, %r10, %r11
	rldicl %r10, %r10, 54, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 41, 23
	and %r10, %r10, %r11
	rldicl %r10, %r10, 53, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 33, 31
	and %r10, %r10, %r11
	rldicl %r10, %r10, 52, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 25, 39
	and %r10, %r10, %r11
	rldicl %r10, %r10, 51, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 17, 47
	and %r10, %r10, %r11
	rldicl %r10, %r10, 50, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 9, 55
	and %r10, %r10, %r11
	rldicl %r10, %r10, 49, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 1, 63
	and %r10, %r10, %r11
	rldicl %r10, %r10, 48, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 58, 6
	and %r10, %r10, %r11
	rldicl %r10, %r10, 47, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 50, 14
	and %r10, %r10, %r11
	rldicl %r10, %r10, 46, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 42, 22
	and %r10, %r10, %r11
	rldicl %r10, %r10, 45, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 34, 30
	and %r10, %r10, %r11
	rldicl %r10, %r10, 44, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 26, 38
	and %r10, %r10, %r11
	rldicl %r10, %r10, 43, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 18, 46
	and %r10, %r10, %r11
	rldicl %r10, %r10, 42, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 10, 54
	and %r10, %r10, %r11
	rldicl %r10, %r10, 41, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 2, 62
	and %r10, %r10, %r11
	rldicl %r10, %r10, 40, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 59, 5
	and %r10, %r10, %r11
	rldicl %r10, %r10, 39, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 51, 13
	and %r10, %r10, %r11
	rldicl %r10, %r10, 38, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 43, 21
	and %r10, %r10, %r11
	rldicl %r10, %r10, 37, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 35, 29
	and %r10, %r10, %r11
	rldicl %r10, %r10, 36, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 27, 37
	and %r10, %r10, %r11
	rldicl %r10, %r10, 35, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 19, 45
	and %r10, %r10, %r11
	rldicl %r10, %r10, 34, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 11, 53
	and %r10, %r10, %r11
	rldicl %r10, %r10, 33, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 3, 61
	and %r10, %r10, %r11
	rldicl %r10, %r10, 32, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r11
	rldicl %r10, %r10, 31, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 52, 12
	and %r10, %r10, %r11
	rldicl %r10, %r10, 30, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 44, 20
	and %r10, %r10, %r11
	rldicl %r10, %r10, 29, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 36, 28
	and %r10, %r10, %r11
	rldicl %r10, %r10, 28, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 63, 1
	and %r10, %r10, %r11
	rldicl %r10, %r10, 27, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 55, 9
	and %r10, %r10, %r11
	rldicl %r10, %r10, 26, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 47, 17
	and %r10, %r10, %r11
	rldicl %r10, %r10, 25, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 39, 25
	and %r10, %r10, %r11
	rldicl %r10, %r10, 24, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 31, 33
	and %r10, %r10, %r11
	rldicl %r10, %r10, 23, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 23, 41
	and %r10, %r10, %r11
	rldicl %r10, %r10, 22, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 15, 49
	and %r10, %r10, %r11
	rldicl %r10, %r10, 21, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 7, 57
	and %r10, %r10, %r11
	rldicl %r10, %r10, 20, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 62, 2
	and %r10, %r10, %r11
	rldicl %r10, %r10, 19, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 54, 10
	and %r10, %r10, %r11
	rldicl %r10, %r10, 18, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 46, 18
	and %r10, %r10, %r11
	rldicl %r10, %r10, 17, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 38, 26
	and %r10, %r10, %r11
	rldicl %r10, %r10, 16, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 30, 34
	and %r10, %r10, %r11
	rldicl %r10, %r10, 15, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 22, 42
	and %r10, %r10, %r11
	rldicl %r10, %r10, 14, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 14, 50
	and %r10, %r10, %r11
	rldicl %r10, %r10, 13, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 6, 58
	and %r10, %r10, %r11
	rldicl %r10, %r10, 12, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 61, 3
	and %r10, %r10, %r11
	rldicl %r10, %r10, 11, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 53, 11
	and %r10, %r10, %r11
	rldicl %r10, %r10, 10, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 45, 19
	and %r10, %r10, %r11
	rldicl %r10, %r10, 9, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 37, 27
	and %r10, %r10, %r11
	rldicl %r10, %r10, 8, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 29, 35
	and %r10, %r10, %r11
	rldicl %r10, %r10, 7, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 21, 43
	and %r10, %r10, %r11
	rldicl %r10, %r10, 6, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 13, 51
	and %r10, %r10, %r11
	rldicl %r10, %r10, 5, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 5, 59
	and %r10, %r10, %r11
	rldicl %r10, %r10, 4, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 28, 36
	and %r10, %r10, %r11
	rldicl %r10, %r10, 3, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 20, 44
	and %r10, %r10, %r11
	rldicl %r10, %r10, 2, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 12, 52
	and %r10, %r10, %r11
	rldicl %r10, %r10, 1, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 4, 60
	and %r10, %r10, %r11
	xor %r9, %r9, %r10
	rldicl %r0, %r9, 36, 28
	or %r7, %r9, %r9
	rldicr %r7, %r7, 36, 27
	rldicl %r7, %r7, 28, 36
	li %r12, 0
	addi %r6, %r5, 256
216:
	rldicl %r8, %r12, 63, 1
	cmpldi %cr0, %r8, 0
	beq %cr0, 217f
	addi %r8, %r12, -8
	cmpldi %cr0, %r8, 0
	beq %cr0, 219f
	addi %r8, %r12, -15
	cmpldi %cr0, %r8, 0
	beq %cr0, 221f
	rldicl %r8, %r0, 38, 26
	rldicl %r0, %r0, 2, 0
	xor %r0, %r0, %r8
	rldicr %r0, %r0, 36, 27
	rldicl %r0, %r0, 28, 36
	rldicl %r8, %r7, 38, 26
	rldicl %r7, %r7, 2, 0
	xor %r7, %r7, %r8
	rldicr %r7, %r7, 36, 27
	rldicl %r7, %r7, 28, 36
	b 222f
221:
	rldicl %r8, %r0, 37, 27
	rldicl %r0, %r0, 1, 0
	xor %r0, %r0, %r8
	rldicr %r0, %r0, 36, 27
	rldicl %r0, %r0, 28, 36
	rldicl %r8, %r7, 37, 27
	rldicl %r7, %r7, 1, 0
	xor %r7, %r7, %r8
	rldicr %r7, %r7, 36, 27
	rldicl %r7, %r7, 28, 36
222:
	b 220f
219:
	rldicl %r8, %r0, 37, 27
	rldicl %r0, %r0, 1, 0
	xor %r0, %r0, %r8
	rldicr %r0, %r0, 36, 27
	rldicl %r0, %r0, 28, 36
	rldicl %r8, %r7, 37, 27
	rldicl %r7, %r7, 1, 0
	xor %r7, %r7, %r8
	rldicr %r7, %r7, 36, 27
	rldicl %r7, %r7, 28, 36
220:
	b 218f
217:
	rldicl %r8, %r0, 37, 27
	rldicl %r0, %r0, 1, 0
	xor %r0, %r0, %r8
	rldicr %r0, %r0, 36, 27
	rldicl %r0, %r0, 28, 36
	rldicl %r8, %r7, 37, 27
	rldicl %r7, %r7, 1, 0
	xor %r7, %r7, %r8
	rldicr %r7, %r7, 36, 27
	rldicl %r7, %r7, 28, 36
218:
	rldicr %r8, %r0, 28, 35
	xor %r8, %r8, %r7
	li %r9, 0
	li %r11, 1
	rldicl %r10, %r8, 22, 42
	and %r10, %r10, %r11
	rldicl %r10, %r10, 47, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 25, 39
	and %r10, %r10, %r11
	rldicl %r10, %r10, 46, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 19, 45
	and %r10, %r10, %r11
	rldicl %r10, %r10, 45, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 32, 32
	and %r10, %r10, %r11
	rldicl %r10, %r10, 44, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 9, 55
	and %r10, %r10, %r11
	rldicl %r10, %r10, 43, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 13, 51
	and %r10, %r10, %r11
	rldicl %r10, %r10, 42, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 11, 53
	and %r10, %r10, %r11
	rldicl %r10, %r10, 41, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 36, 28
	and %r10, %r10, %r11
	rldicl %r10, %r10, 40, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 23, 41
	and %r10, %r10, %r11
	rldicl %r10, %r10, 39, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 14, 50
	and %r10, %r10, %r11
	rldicl %r10, %r10, 38, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 29, 35
	and %r10, %r10, %r11
	rldicl %r10, %r10, 37, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 18, 46
	and %r10, %r10, %r11
	rldicl %r10, %r10, 36, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 31, 33
	and %r10, %r10, %r11
	rldicl %r10, %r10, 35, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 27, 37
	and %r10, %r10, %r11
	rldicl %r10, %r10, 34, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 20, 44
	and %r10, %r10, %r11
	rldicl %r10, %r10, 33, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 12, 52
	and %r10, %r10, %r11
	rldicl %r10, %r10, 32, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 34, 30
	and %r10, %r10, %r11
	rldicl %r10, %r10, 31, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 16, 48
	and %r10, %r10, %r11
	rldicl %r10, %r10, 30, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 24, 40
	and %r10, %r10, %r11
	rldicl %r10, %r10, 29, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 15, 49
	and %r10, %r10, %r11
	rldicl %r10, %r10, 28, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 35, 29
	and %r10, %r10, %r11
	rldicl %r10, %r10, 27, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 28, 36
	and %r10, %r10, %r11
	rldicl %r10, %r10, 26, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 21, 43
	and %r10, %r10, %r11
	rldicl %r10, %r10, 25, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 10, 54
	and %r10, %r10, %r11
	rldicl %r10, %r10, 24, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 49, 15
	and %r10, %r10, %r11
	rldicl %r10, %r10, 23, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 60, 4
	and %r10, %r10, %r11
	rldicl %r10, %r10, 22, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 39, 25
	and %r10, %r10, %r11
	rldicl %r10, %r10, 21, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 45, 19
	and %r10, %r10, %r11
	rldicl %r10, %r10, 20, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 55, 9
	and %r10, %r10, %r11
	rldicl %r10, %r10, 19, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 63, 1
	and %r10, %r10, %r11
	rldicl %r10, %r10, 18, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 38, 26
	and %r10, %r10, %r11
	rldicl %r10, %r10, 17, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 48, 16
	and %r10, %r10, %r11
	rldicl %r10, %r10, 16, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 59, 5
	and %r10, %r10, %r11
	rldicl %r10, %r10, 15, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 53, 11
	and %r10, %r10, %r11
	rldicl %r10, %r10, 14, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 41, 23
	and %r10, %r10, %r11
	rldicl %r10, %r10, 13, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 56, 8
	and %r10, %r10, %r11
	rldicl %r10, %r10, 12, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 52, 12
	and %r10, %r10, %r11
	rldicl %r10, %r10, 11, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 57, 7
	and %r10, %r10, %r11
	rldicl %r10, %r10, 10, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 47, 17
	and %r10, %r10, %r11
	rldicl %r10, %r10, 9, 0
	xor %r9, %r9, %r10
	or %r10, %r8, %r8
	and %r10, %r10, %r11
	rldicl %r10, %r10, 8, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 42, 22
	and %r10, %r10, %r11
	rldicl %r10, %r10, 7, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 61, 3
	and %r10, %r10, %r11
	rldicl %r10, %r10, 6, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 54, 10
	and %r10, %r10, %r11
	rldicl %r10, %r10, 5, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 50, 14
	and %r10, %r10, %r11
	rldicl %r10, %r10, 4, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 58, 6
	and %r10, %r10, %r11
	rldicl %r10, %r10, 3, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 44, 20
	and %r10, %r10, %r11
	rldicl %r10, %r10, 2, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 37, 27
	and %r10, %r10, %r11
	rldicl %r10, %r10, 1, 0
	xor %r9, %r9, %r10
	rldicl %r10, %r8, 40, 24
	and %r10, %r10, %r11
	xor %r9, %r9, %r10
	std %r9, 0(%r6)
	addi %r6, %r6, 8
	addi %r12, %r12, 1
	addi %r8, %r12, -16
	cmpldi %cr0, %r8, 0
	bne %cr0, 216b
	b 215f
214:
	ld %r8, 0(%r5)
	std %r8, 256(%r5)
	ld %r8, 8(%r5)
	std %r8, 264(%r5)
	ld %r8, 16(%r5)
	std %r8, 272(%r5)
	ld %r8, 24(%r5)
	std %r8, 280(%r5)
	ld %r8, 32(%r5)
	std %r8, 288(%r5)
	ld %r8, 40(%r5)
	std %r8, 296(%r5)
	ld %r8, 48(%r5)
	std %r8, 304(%r5)
	ld %r8, 56(%r5)
	std %r8, 312(%r5)
	ld %r8, 64(%r5)
	std %r8, 320(%r5)
	ld %r8, 72(%r5)
	std %r8, 328(%r5)
	ld %r8, 80(%r5)
	std %r8, 336(%r5)
	ld %r8, 88(%r5)
	std %r8, 344(%r5)
	ld %r8, 96(%r5)
	std %r8, 352(%r5)
	ld %r8, 104(%r5)
	std %r8, 360(%r5)
	ld %r8, 112(%r5)
	std %r8, 368(%r5)
	ld %r8, 120(%r5)
	std %r8, 376(%r5)
215:
	blr

vg_triple_des_ecb_encrypt:
	stdu %r1, -1056(%r1)
	addi %r6, %r1, 32
	mflr %r0
	std %r0, 512(%r6)
	std %r31, 520(%r6)
	or %r31, %r5, %r5
	or %r5, %r6, %r6
	cmpldi %cr0, %r31, 0
	beq %cr0, 20f
22:
	bl {vg_triple_des_encrypt_block}
	addi %r4, %r4, 8
	addi %r31, %r31, -1
	cmpldi %cr0, %r31, 0
	bne %cr0, 22b
	b 21f
20:
21:
	ld %r0, 512(%r5)
	mtlr %r0
	ld %r31, 520(%r5)
	addi %r12, %r1, 32
	li %r11, 0
	std %r11, 0(%r12)
	std %r11, 8(%r12)
	std %r11, 16(%r12)
	std %r11, 24(%r12)
	std %r11, 32(%r12)
	std %r11, 40(%r12)
	std %r11, 48(%r12)
	std %r11, 56(%r12)
	std %r11, 64(%r12)
	std %r11, 72(%r12)
	std %r11, 80(%r12)
	std %r11, 88(%r12)
	std %r11, 96(%r12)
	std %r11, 104(%r12)
	std %r11, 112(%r12)
	std %r11, 120(%r12)
	std %r11, 128(%r12)
	std %r11, 136(%r12)
	std %r11, 144(%r12)
	std %r11, 152(%r12)
	std %r11, 160(%r12)
	std %r11, 168(%r12)
	std %r11, 176(%r12)
	std %r11, 184(%r12)
	std %r11, 192(%r12)
	std %r11, 200(%r12)
	std %r11, 208(%r12)
	std %r11, 216(%r12)
	std %r11, 224(%r12)
	std %r11, 232(%r12)
	std %r11, 240(%r12)
	std %r11, 248(%r12)
	std %r11, 256(%r12)
	std %r11, 264(%r12)
	std %r11, 272(%r12)
	std %r11, 280(%r12)
	std %r11, 288(%r12)
	std %r11, 296(%r12)
	std %r11, 304(%r12)
	std %r11, 312(%r12)
	std %r11, 320(%r12)
	std %r11, 328(%r12)
	std %r11, 336(%r12)
	std %r11, 344(%r12)
	std %r11, 352(%r12)
	std %r11, 360(%r12)
	std %r11, 368(%r12)
	std %r11, 376(%r12)
	std %r11, 384(%r12)
	std %r11, 392(%r12)
	std %r11, 400(%r12)
	std %r11, 408(%r12)
	std %r11, 416(%r12)
	std %r11, 424(%r12)
	std %r11, 432(%r12)
	std %r11, 440(%r12)
	std %r11, 448(%r12)
	std %r11, 456(%r12)
	std %r11, 464(%r12)
	std %r11, 472(%r12)
	std %r11, 480(%r12)
	std %r11, 488(%r12)
	std %r11, 496(%r12)
	std %r11, 504(%r12)
	std %r11, 512(%r12)
	std %r11, 520(%r12)
	std %r11, 528(%r12)
	std %r11, 536(%r12)
	std %r11, 544(%r12)
	std %r11, 552(%r12)
	std %r11, 560(%r12)
	std %r11, 568(%r12)
	std %r11, 576(%r12)
	std %r11, 584(%r12)
	std %r11, 592(%r12)
	std %r11, 600(%r12)
	std %r11, 608(%r12)
	std %r11, 616(%r12)
	std %r11, 624(%r12)
	std %r11, 632(%r12)
	std %r11, 640(%r12)
	std %r11, 648(%r12)
	std %r11, 656(%r12)
	std %r11, 664(%r12)
	std %r11, 672(%r12)
	std %r11, 680(%r12)
	std %r11, 688(%r12)
	std %r11, 696(%r12)
	std %r11, 704(%r12)
	std %r11, 712(%r12)
	std %r11, 720(%r12)
	std %r11, 728(%r12)
	std %r11, 736(%r12)
	std %r11, 744(%r12)
	std %r11, 752(%r12)
	std %r11, 760(%r12)
	std %r11, 768(%r12)
	std %r11, 776(%r12)
	std %r11, 784(%r12)
	std %r11, 792(%r12)
	std %r11, 800(%r12)
	std %r11, 808(%r12)
	std %r11, 816(%r12)
	std %r11, 824(%r12)
	std %r11, 832(%r12)
	std %r11, 840(%r12)
	std %r11, 848(%r12)
	std %r11, 856(%r12)
	std %r11, 864(%r12)
	std %r11, 872(%r12)
	std %r11, 880(%r12)
	std %r11, 888(%r12)
	std %r11, 896(%r12)
	std %r11, 904(%r12)
	std %r11, 912(%r12)
	std %r11, 920(%r12)
	std %r11, 928(%r12)
	std %r11, 936(%r12)
	std %r11, 944(%r12)
	std %r11, 952(%r12)
	std %r11, 960(%r12)
	std %r11, 968(%r12)
	std %r11, 976(%r12)
	std %r11, 984(%r12)
	std %r11, 992(%r12)
	std %r11, 1000(%r12)
	std %r11, 1008(%r12)
	std %r11, 1016(%r12)
	addi %r1, %r1, 1056
	blr

vg_triple_des_ecb_decrypt:
	stdu %r1, -1056(%r1)
	addi %r6, %r1, 32
	mflr %r0
	std %r0, 512(%r6)
	std %r31, 520(%r6)
	or %r31, %r5, %r5
	or %r5, %r6, %r6
	cmpldi %cr0, %r31, 0
	beq %cr0, 20f
22:
	bl {vg_triple_des_decrypt_block}
	addi %r4, %r4, 8
	addi %r31, %r31, -1
	cmpldi %cr0, %r31, 0
	bne %cr0, 22b
	b 21f
20:
21:
	ld %r0, 512(%r5)
	mtlr %r0
	ld %r31, 520(%r5)
	addi %r12, %r1, 32
	li %r11, 0
	std %r11, 0(%r12)
	std %r11, 8(%r12)
	std %r11, 16(%r12)
	std %r11, 24(%r12)
	std %r11, 32(%r12)
	std %r11, 40(%r12)
	std %r11, 48(%r12)
	std %r11, 56(%r12)
	std %r11, 64(%r12)
	std %r11, 72(%r12)
	std %r11, 80(%r12)
	std %r11, 88(%r12)
	std %r11, 96(%r12)
	std %r11, 104(%r12)
	std %r11, 112(%r12)
	std %r11, 120(%r12)
	std %r11, 128(%r12)
	std %r11, 136(%r12)
	std %r11, 144(%r12)
	std %r11, 152(%r12)
	std %r11, 160(%r12)
	std %r11, 168(%r12)
	std %r11, 176(%r12)
	std %r11, 184(%r12)
	std %r11, 192(%r12)
	std %r11, 200(%r12)
	std %r11, 208(%r12)
	std %r11, 216(%r12)
	std %r11, 224(%r12)
	std %r11, 232(%r12)
	std %r11, 240(%r12)
	std %r11, 248(%r12)
	std %r11, 256(%r12)
	std %r11, 264(%r12)
	std %r11, 272(%r12)
	std %r11, 280(%r12)
	std %r11, 288(%r12)
	std %r11, 296(%r12)
	std %r11, 304(%r12)
	std %r11, 312(%r12)
	std %r11, 320(%r12)
	std %r11, 328(%r12)
	std %r11, 336(%r12)
	std %r11, 344(%r12)
	std %r11, 352(%r12)
	std %r11, 360(%r12)
	std %r11, 368(%r12)
	std %r11, 376(%r12)
	std %r11, 384(%r12)
	std %r11, 392(%r12)
	std %r11, 400(%r12)
	std %r11, 408(%r12)
	std %r11, 416(%r12)
	std %r11, 424(%r12)
	std %r11, 432(%r12)
	std %r11, 440(%r12)
	std %r11, 448(%r12)
	std %r11, 456(%r12)
	std %r11, 464(%r12)
	std %r11, 472(%r12)
	std %r11, 480(%r12)
	std %r11, 488(%r12)
	std %r11, 496(%r12)
	std %r11, 504(%r12)
	std %r11, 512(%r12)
	std %r11, 520(%r12)
	std %r11, 528(%r12)
	std %r11, 536(%r12)
	std %r11, 544(%r12)
	std %r11, 552(%r12)
	std %r11, 560(%r12)
	std %r11, 568(%r12)
	std %r11, 576(%r12)
	std %r11, 584(%r12)
	std %r11, 592(%r12)
	std %r11, 600(%r12)
	std %r11, 608(%r12)
	std %r11, 616(%r12)
	std %r11, 624(%r12)
	std %r11, 632(%r12)
	std %r11, 640(%r12)
	std %r11, 648(%r12)
	std %r11, 656(%r12)
	std %r11, 664(%r12)
	std %r11, 672(%r12)
	std %r11, 680(%r12)
	std %r11, 688(%r12)
	std %r11, 696(%r12)
	std %r11, 704(%r12)
	std %r11, 712(%r12)
	std %r11, 720(%r12)
	std %r11, 728(%r12)
	std %r11, 736(%r12)
	std %r11, 744(%r12)
	std %r11, 752(%r12)
	std %r11, 760(%r12)
	std %r11, 768(%r12)
	std %r11, 776(%r12)
	std %r11, 784(%r12)
	std %r11, 792(%r12)
	std %r11, 800(%r12)
	std %r11, 808(%r12)
	std %r11, 816(%r12)
	std %r11, 824(%r12)
	std %r11, 832(%r12)
	std %r11, 840(%r12)
	std %r11, 848(%r12)
	std %r11, 856(%r12)
	std %r11, 864(%r12)
	std %r11, 872(%r12)
	std %r11, 880(%r12)
	std %r11, 888(%r12)
	std %r11, 896(%r12)
	std %r11, 904(%r12)
	std %r11, 912(%r12)
	std %r11, 920(%r12)
	std %r11, 928(%r12)
	std %r11, 936(%r12)
	std %r11, 944(%r12)
	std %r11, 952(%r12)
	std %r11, 960(%r12)
	std %r11, 968(%r12)
	std %r11, 976(%r12)
	std %r11, 984(%r12)
	std %r11, 992(%r12)
	std %r11, 1000(%r12)
	std %r11, 1008(%r12)
	std %r11, 1016(%r12)
	addi %r1, %r1, 1056
	blr
