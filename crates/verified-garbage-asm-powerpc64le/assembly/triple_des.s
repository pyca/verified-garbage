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
	cmpldi %cr0, %r5, 0
	beq %cr0, 20f
	std %r2, 560(%r6)
	std %r14, 568(%r6)
	std %r15, 576(%r6)
	std %r16, 584(%r6)
	std %r17, 592(%r6)
	std %r18, 600(%r6)
	std %r19, 608(%r6)
	std %r20, 616(%r6)
	std %r21, 624(%r6)
	std %r22, 632(%r6)
	std %r23, 640(%r6)
	std %r24, 648(%r6)
	std %r25, 656(%r6)
	std %r26, 664(%r6)
	std %r27, 672(%r6)
	std %r28, 680(%r6)
	std %r29, 688(%r6)
	std %r30, 696(%r6)
	std %r31, 704(%r6)
	or %r10, %r6, %r6
	or %r7, %r3, %r3
	or %r8, %r5, %r5
	lis %r11, -1
	ori %r11, %r11, 65535
	lis %r12, 0
	ori %r12, %r12, 0
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 65535
	ori %r12, %r12, 65535
	std %r12, 512(%r10)
	lis %r12, 0
	ori %r12, %r12, 65535
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 0
	ori %r12, %r12, 65535
	std %r12, 520(%r10)
	lis %r12, 255
	ori %r12, %r12, 255
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 255
	ori %r12, %r12, 255
	std %r12, 528(%r10)
	lis %r12, 3855
	ori %r12, %r12, 3855
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 3855
	ori %r12, %r12, 3855
	std %r12, 536(%r10)
	lis %r12, 13107
	ori %r12, %r12, 13107
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 13107
	ori %r12, %r12, 13107
	std %r12, 544(%r10)
	lis %r12, 21845
	ori %r12, %r12, 21845
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 21845
	ori %r12, %r12, 21845
	std %r12, 552(%r10)
22:
	rldicl %r12, %r8, 58, 6
	cmpldi %cr0, %r12, 0
	beq %cr0, 23f
	li %r12, 64
	b 24f
23:
	or %r12, %r8, %r8
24:
	or %r3, %r4, %r4
	or %r9, %r10, %r10
	or %r5, %r12, %r12
25:
	ld %r0, 0(%r3)
	std %r0, 0(%r9)
	addi %r3, %r3, 8
	addi %r9, %r9, 8
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 25b
	addi %r25, %r10, 512
	ld %r21, 0(%r25)
	ld %r22, 8(%r25)
	ld %r23, 16(%r25)
	ld %r12, 0(%r10)
	ld %r14, 64(%r10)
	ld %r15, 128(%r10)
	ld %r16, 192(%r10)
	ld %r17, 256(%r10)
	ld %r18, 320(%r10)
	ld %r19, 384(%r10)
	ld %r20, 448(%r10)
	rldicl %r24, %r12, 32, 32
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 32, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 32, 32
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 32, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 32, 32
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 32, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 32, 32
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 32, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 48, 16
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 16, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 48, 16
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 16, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 48, 16
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 16, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 48, 16
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 16, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 56, 8
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 8, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 56, 8
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 8, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 56, 8
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 8, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 56, 8
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 8, 0
	xor %r19, %r19, %r24
	std %r12, 0(%r10)
	std %r14, 64(%r10)
	std %r15, 128(%r10)
	std %r16, 192(%r10)
	std %r17, 256(%r10)
	std %r18, 320(%r10)
	std %r19, 384(%r10)
	std %r20, 448(%r10)
	ld %r12, 8(%r10)
	ld %r14, 72(%r10)
	ld %r15, 136(%r10)
	ld %r16, 200(%r10)
	ld %r17, 264(%r10)
	ld %r18, 328(%r10)
	ld %r19, 392(%r10)
	ld %r20, 456(%r10)
	rldicl %r24, %r12, 32, 32
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 32, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 32, 32
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 32, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 32, 32
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 32, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 32, 32
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 32, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 48, 16
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 16, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 48, 16
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 16, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 48, 16
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 16, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 48, 16
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 16, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 56, 8
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 8, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 56, 8
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 8, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 56, 8
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 8, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 56, 8
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 8, 0
	xor %r19, %r19, %r24
	std %r12, 8(%r10)
	std %r14, 72(%r10)
	std %r15, 136(%r10)
	std %r16, 200(%r10)
	std %r17, 264(%r10)
	std %r18, 328(%r10)
	std %r19, 392(%r10)
	std %r20, 456(%r10)
	ld %r12, 16(%r10)
	ld %r14, 80(%r10)
	ld %r15, 144(%r10)
	ld %r16, 208(%r10)
	ld %r17, 272(%r10)
	ld %r18, 336(%r10)
	ld %r19, 400(%r10)
	ld %r20, 464(%r10)
	rldicl %r24, %r12, 32, 32
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 32, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 32, 32
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 32, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 32, 32
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 32, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 32, 32
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 32, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 48, 16
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 16, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 48, 16
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 16, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 48, 16
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 16, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 48, 16
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 16, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 56, 8
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 8, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 56, 8
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 8, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 56, 8
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 8, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 56, 8
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 8, 0
	xor %r19, %r19, %r24
	std %r12, 16(%r10)
	std %r14, 80(%r10)
	std %r15, 144(%r10)
	std %r16, 208(%r10)
	std %r17, 272(%r10)
	std %r18, 336(%r10)
	std %r19, 400(%r10)
	std %r20, 464(%r10)
	ld %r12, 24(%r10)
	ld %r14, 88(%r10)
	ld %r15, 152(%r10)
	ld %r16, 216(%r10)
	ld %r17, 280(%r10)
	ld %r18, 344(%r10)
	ld %r19, 408(%r10)
	ld %r20, 472(%r10)
	rldicl %r24, %r12, 32, 32
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 32, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 32, 32
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 32, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 32, 32
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 32, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 32, 32
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 32, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 48, 16
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 16, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 48, 16
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 16, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 48, 16
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 16, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 48, 16
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 16, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 56, 8
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 8, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 56, 8
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 8, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 56, 8
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 8, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 56, 8
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 8, 0
	xor %r19, %r19, %r24
	std %r12, 24(%r10)
	std %r14, 88(%r10)
	std %r15, 152(%r10)
	std %r16, 216(%r10)
	std %r17, 280(%r10)
	std %r18, 344(%r10)
	std %r19, 408(%r10)
	std %r20, 472(%r10)
	ld %r12, 32(%r10)
	ld %r14, 96(%r10)
	ld %r15, 160(%r10)
	ld %r16, 224(%r10)
	ld %r17, 288(%r10)
	ld %r18, 352(%r10)
	ld %r19, 416(%r10)
	ld %r20, 480(%r10)
	rldicl %r24, %r12, 32, 32
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 32, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 32, 32
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 32, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 32, 32
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 32, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 32, 32
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 32, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 48, 16
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 16, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 48, 16
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 16, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 48, 16
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 16, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 48, 16
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 16, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 56, 8
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 8, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 56, 8
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 8, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 56, 8
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 8, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 56, 8
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 8, 0
	xor %r19, %r19, %r24
	std %r12, 32(%r10)
	std %r14, 96(%r10)
	std %r15, 160(%r10)
	std %r16, 224(%r10)
	std %r17, 288(%r10)
	std %r18, 352(%r10)
	std %r19, 416(%r10)
	std %r20, 480(%r10)
	ld %r12, 40(%r10)
	ld %r14, 104(%r10)
	ld %r15, 168(%r10)
	ld %r16, 232(%r10)
	ld %r17, 296(%r10)
	ld %r18, 360(%r10)
	ld %r19, 424(%r10)
	ld %r20, 488(%r10)
	rldicl %r24, %r12, 32, 32
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 32, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 32, 32
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 32, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 32, 32
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 32, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 32, 32
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 32, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 48, 16
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 16, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 48, 16
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 16, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 48, 16
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 16, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 48, 16
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 16, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 56, 8
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 8, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 56, 8
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 8, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 56, 8
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 8, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 56, 8
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 8, 0
	xor %r19, %r19, %r24
	std %r12, 40(%r10)
	std %r14, 104(%r10)
	std %r15, 168(%r10)
	std %r16, 232(%r10)
	std %r17, 296(%r10)
	std %r18, 360(%r10)
	std %r19, 424(%r10)
	std %r20, 488(%r10)
	ld %r12, 48(%r10)
	ld %r14, 112(%r10)
	ld %r15, 176(%r10)
	ld %r16, 240(%r10)
	ld %r17, 304(%r10)
	ld %r18, 368(%r10)
	ld %r19, 432(%r10)
	ld %r20, 496(%r10)
	rldicl %r24, %r12, 32, 32
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 32, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 32, 32
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 32, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 32, 32
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 32, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 32, 32
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 32, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 48, 16
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 16, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 48, 16
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 16, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 48, 16
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 16, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 48, 16
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 16, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 56, 8
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 8, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 56, 8
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 8, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 56, 8
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 8, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 56, 8
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 8, 0
	xor %r19, %r19, %r24
	std %r12, 48(%r10)
	std %r14, 112(%r10)
	std %r15, 176(%r10)
	std %r16, 240(%r10)
	std %r17, 304(%r10)
	std %r18, 368(%r10)
	std %r19, 432(%r10)
	std %r20, 496(%r10)
	ld %r12, 56(%r10)
	ld %r14, 120(%r10)
	ld %r15, 184(%r10)
	ld %r16, 248(%r10)
	ld %r17, 312(%r10)
	ld %r18, 376(%r10)
	ld %r19, 440(%r10)
	ld %r20, 504(%r10)
	rldicl %r24, %r12, 32, 32
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 32, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 32, 32
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 32, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 32, 32
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 32, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 32, 32
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 32, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 48, 16
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 16, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 48, 16
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 16, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 48, 16
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 16, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 48, 16
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 16, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 56, 8
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 8, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 56, 8
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 8, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 56, 8
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 8, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 56, 8
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 8, 0
	xor %r19, %r19, %r24
	std %r12, 56(%r10)
	std %r14, 120(%r10)
	std %r15, 184(%r10)
	std %r16, 248(%r10)
	std %r17, 312(%r10)
	std %r18, 376(%r10)
	std %r19, 440(%r10)
	std %r20, 504(%r10)
	ld %r21, 24(%r25)
	ld %r22, 32(%r25)
	ld %r23, 40(%r25)
	ld %r12, 0(%r10)
	ld %r14, 8(%r10)
	ld %r15, 16(%r10)
	ld %r16, 24(%r10)
	ld %r17, 32(%r10)
	ld %r18, 40(%r10)
	ld %r19, 48(%r10)
	ld %r20, 56(%r10)
	rldicl %r24, %r12, 60, 4
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 4, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 60, 4
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 4, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 60, 4
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 4, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 60, 4
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 4, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 62, 2
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 2, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 62, 2
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 2, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 62, 2
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 2, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 62, 2
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 2, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 63, 1
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 1, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 63, 1
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 1, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 63, 1
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 1, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 63, 1
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 1, 0
	xor %r19, %r19, %r24
	std %r12, 0(%r10)
	std %r14, 8(%r10)
	std %r15, 16(%r10)
	std %r16, 24(%r10)
	std %r17, 32(%r10)
	std %r18, 40(%r10)
	std %r19, 48(%r10)
	std %r20, 56(%r10)
	ld %r12, 64(%r10)
	ld %r14, 72(%r10)
	ld %r15, 80(%r10)
	ld %r16, 88(%r10)
	ld %r17, 96(%r10)
	ld %r18, 104(%r10)
	ld %r19, 112(%r10)
	ld %r20, 120(%r10)
	rldicl %r24, %r12, 60, 4
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 4, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 60, 4
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 4, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 60, 4
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 4, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 60, 4
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 4, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 62, 2
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 2, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 62, 2
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 2, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 62, 2
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 2, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 62, 2
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 2, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 63, 1
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 1, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 63, 1
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 1, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 63, 1
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 1, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 63, 1
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 1, 0
	xor %r19, %r19, %r24
	std %r12, 64(%r10)
	std %r14, 72(%r10)
	std %r15, 80(%r10)
	std %r16, 88(%r10)
	std %r17, 96(%r10)
	std %r18, 104(%r10)
	std %r19, 112(%r10)
	std %r20, 120(%r10)
	ld %r12, 128(%r10)
	ld %r14, 136(%r10)
	ld %r15, 144(%r10)
	ld %r16, 152(%r10)
	ld %r17, 160(%r10)
	ld %r18, 168(%r10)
	ld %r19, 176(%r10)
	ld %r20, 184(%r10)
	rldicl %r24, %r12, 60, 4
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 4, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 60, 4
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 4, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 60, 4
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 4, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 60, 4
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 4, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 62, 2
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 2, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 62, 2
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 2, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 62, 2
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 2, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 62, 2
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 2, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 63, 1
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 1, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 63, 1
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 1, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 63, 1
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 1, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 63, 1
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 1, 0
	xor %r19, %r19, %r24
	std %r12, 128(%r10)
	std %r14, 136(%r10)
	std %r15, 144(%r10)
	std %r16, 152(%r10)
	std %r17, 160(%r10)
	std %r18, 168(%r10)
	std %r19, 176(%r10)
	std %r20, 184(%r10)
	ld %r12, 192(%r10)
	ld %r14, 200(%r10)
	ld %r15, 208(%r10)
	ld %r16, 216(%r10)
	ld %r17, 224(%r10)
	ld %r18, 232(%r10)
	ld %r19, 240(%r10)
	ld %r20, 248(%r10)
	rldicl %r24, %r12, 60, 4
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 4, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 60, 4
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 4, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 60, 4
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 4, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 60, 4
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 4, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 62, 2
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 2, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 62, 2
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 2, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 62, 2
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 2, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 62, 2
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 2, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 63, 1
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 1, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 63, 1
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 1, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 63, 1
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 1, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 63, 1
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 1, 0
	xor %r19, %r19, %r24
	std %r12, 192(%r10)
	std %r14, 200(%r10)
	std %r15, 208(%r10)
	std %r16, 216(%r10)
	std %r17, 224(%r10)
	std %r18, 232(%r10)
	std %r19, 240(%r10)
	std %r20, 248(%r10)
	ld %r12, 256(%r10)
	ld %r14, 264(%r10)
	ld %r15, 272(%r10)
	ld %r16, 280(%r10)
	ld %r17, 288(%r10)
	ld %r18, 296(%r10)
	ld %r19, 304(%r10)
	ld %r20, 312(%r10)
	rldicl %r24, %r12, 60, 4
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 4, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 60, 4
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 4, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 60, 4
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 4, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 60, 4
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 4, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 62, 2
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 2, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 62, 2
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 2, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 62, 2
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 2, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 62, 2
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 2, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 63, 1
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 1, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 63, 1
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 1, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 63, 1
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 1, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 63, 1
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 1, 0
	xor %r19, %r19, %r24
	std %r12, 256(%r10)
	std %r14, 264(%r10)
	std %r15, 272(%r10)
	std %r16, 280(%r10)
	std %r17, 288(%r10)
	std %r18, 296(%r10)
	std %r19, 304(%r10)
	std %r20, 312(%r10)
	ld %r12, 320(%r10)
	ld %r14, 328(%r10)
	ld %r15, 336(%r10)
	ld %r16, 344(%r10)
	ld %r17, 352(%r10)
	ld %r18, 360(%r10)
	ld %r19, 368(%r10)
	ld %r20, 376(%r10)
	rldicl %r24, %r12, 60, 4
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 4, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 60, 4
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 4, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 60, 4
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 4, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 60, 4
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 4, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 62, 2
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 2, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 62, 2
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 2, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 62, 2
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 2, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 62, 2
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 2, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 63, 1
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 1, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 63, 1
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 1, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 63, 1
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 1, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 63, 1
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 1, 0
	xor %r19, %r19, %r24
	std %r12, 320(%r10)
	std %r14, 328(%r10)
	std %r15, 336(%r10)
	std %r16, 344(%r10)
	std %r17, 352(%r10)
	std %r18, 360(%r10)
	std %r19, 368(%r10)
	std %r20, 376(%r10)
	ld %r12, 384(%r10)
	ld %r14, 392(%r10)
	ld %r15, 400(%r10)
	ld %r16, 408(%r10)
	ld %r17, 416(%r10)
	ld %r18, 424(%r10)
	ld %r19, 432(%r10)
	ld %r20, 440(%r10)
	rldicl %r24, %r12, 60, 4
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 4, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 60, 4
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 4, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 60, 4
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 4, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 60, 4
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 4, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 62, 2
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 2, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 62, 2
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 2, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 62, 2
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 2, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 62, 2
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 2, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 63, 1
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 1, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 63, 1
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 1, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 63, 1
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 1, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 63, 1
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 1, 0
	xor %r19, %r19, %r24
	std %r12, 384(%r10)
	std %r14, 392(%r10)
	std %r15, 400(%r10)
	std %r16, 408(%r10)
	std %r17, 416(%r10)
	std %r18, 424(%r10)
	std %r19, 432(%r10)
	std %r20, 440(%r10)
	ld %r12, 448(%r10)
	ld %r14, 456(%r10)
	ld %r15, 464(%r10)
	ld %r16, 472(%r10)
	ld %r17, 480(%r10)
	ld %r18, 488(%r10)
	ld %r19, 496(%r10)
	ld %r20, 504(%r10)
	rldicl %r24, %r12, 60, 4
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 4, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 60, 4
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 4, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 60, 4
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 4, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 60, 4
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 4, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 62, 2
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 2, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 62, 2
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 2, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 62, 2
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 2, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 62, 2
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 2, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 63, 1
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 1, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 63, 1
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 1, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 63, 1
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 1, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 63, 1
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 1, 0
	xor %r19, %r19, %r24
	std %r12, 448(%r10)
	std %r14, 456(%r10)
	std %r15, 464(%r10)
	std %r16, 472(%r10)
	std %r17, 480(%r10)
	std %r18, 488(%r10)
	std %r19, 496(%r10)
	std %r20, 504(%r10)
	addi %r3, %r7, 0
	li %r5, 8
26:
	ld %r9, 0(%r3)
	xor %r9, %r9, %r11
	addi %r3, %r3, 8
	rldicr %r12, %r9, 21, 42
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 248(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 20, 43
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 312(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 19, 44
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 376(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 18, 45
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 440(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 17, 46
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 504(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 16, 47
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 8(%r10)
	xor %r18, %r18, %r0
	or %r6, %r18, %r14
	xor %r6, %r6, %r14
	xor %r2, %r15, %r6
	or %r19, %r16, %r12
	xor %r20, %r18, %r16
	and %r21, %r19, %r20
	xor %r22, %r15, %r21
	or %r23, %r22, %r2
	xor %r23, %r23, %r2
	xor %r24, %r14, %r12
	xor %r25, %r16, %r24
	xor %r25, %r25, %r11
	and %r25, %r25, %r2
	or %r21, %r12, %r21
	xor %r25, %r25, %r21
	or %r21, %r25, %r23
	xor %r21, %r21, %r23
	or %r12, %r18, %r12
	or %r26, %r25, %r12
	xor %r22, %r22, %r11
	and %r22, %r22, %r14
	xor %r27, %r26, %r22
	or %r15, %r15, %r12
	xor %r15, %r15, %r12
	xor %r15, %r22, %r15
	xor %r20, %r20, %r11
	and %r20, %r20, %r24
	or %r15, %r15, %r20
	or %r16, %r16, %r6
	xor %r16, %r16, %r6
	xor %r6, %r2, %r26
	or %r6, %r6, %r16
	xor %r6, %r6, %r16
	xor %r16, %r6, %r11
	and %r25, %r19, %r25
	xor %r16, %r16, %r25
	or %r27, %r27, %r17
	xor %r27, %r27, %r17
	xor %r27, %r27, %r16
	xor %r6, %r24, %r6
	or %r22, %r22, %r6
	xor %r22, %r19, %r22
	xor %r18, %r18, %r22
	xor %r16, %r16, %r18
	or %r23, %r23, %r17
	xor %r23, %r23, %r16
	xor %r19, %r19, %r26
	or %r19, %r15, %r19
	xor %r19, %r18, %r19
	or %r24, %r24, %r16
	xor %r24, %r19, %r24
	or %r16, %r21, %r17
	xor %r16, %r16, %r24
	or %r14, %r14, %r2
	or %r14, %r14, %r19
	xor %r14, %r14, %r19
	and %r21, %r21, %r18
	xor %r14, %r14, %r21
	or %r14, %r14, %r17
	xor %r14, %r14, %r15
	ld %r0, 64(%r10)
	xor %r0, %r0, %r14
	std %r0, 64(%r10)
	ld %r0, 80(%r10)
	xor %r0, %r0, %r27
	std %r0, 80(%r10)
	ld %r0, 464(%r10)
	xor %r0, %r0, %r16
	std %r0, 464(%r10)
	ld %r0, 480(%r10)
	xor %r0, %r0, %r23
	std %r0, 480(%r10)
	rldicr %r12, %r9, 27, 36
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 488(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 26, 37
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 56(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 25, 38
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 120(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 24, 39
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 184(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 23, 40
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 248(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 22, 41
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 312(%r10)
	xor %r18, %r18, %r0
	xor %r6, %r17, %r14
	or %r2, %r18, %r12
	xor %r2, %r2, %r12
	xor %r2, %r2, %r11
	and %r2, %r2, %r14
	or %r19, %r17, %r2
	or %r20, %r6, %r12
	xor %r20, %r20, %r12
	and %r21, %r18, %r6
	xor %r14, %r14, %r21
	or %r21, %r14, %r20
	xor %r21, %r21, %r20
	and %r22, %r16, %r12
	xor %r2, %r2, %r20
	and %r2, %r19, %r2
	or %r20, %r2, %r22
	xor %r20, %r20, %r22
	and %r23, %r16, %r2
	xor %r18, %r18, %r11
	xor %r18, %r23, %r18
	xor %r12, %r12, %r6
	or %r24, %r12, %r22
	xor %r24, %r24, %r22
	xor %r25, %r18, %r24
	xor %r20, %r20, %r11
	and %r20, %r20, %r15
	xor %r20, %r20, %r25
	or %r17, %r17, %r24
	xor %r17, %r17, %r24
	xor %r14, %r14, %r17
	or %r18, %r18, %r14
	xor %r18, %r18, %r14
	xor %r16, %r16, %r12
	xor %r18, %r18, %r16
	or %r24, %r19, %r15
	xor %r24, %r24, %r15
	xor %r24, %r24, %r18
	xor %r23, %r23, %r17
	or %r16, %r16, %r23
	xor %r19, %r19, %r25
	or %r22, %r22, %r19
	xor %r23, %r16, %r22
	xor %r2, %r2, %r25
	xor %r18, %r18, %r2
	and %r22, %r22, %r18
	and %r6, %r6, %r16
	xor %r22, %r22, %r6
	or %r6, %r22, %r15
	xor %r6, %r6, %r23
	or %r22, %r22, %r14
	xor %r22, %r22, %r14
	or %r12, %r12, %r19
	xor %r22, %r22, %r12
	or %r21, %r21, %r15
	xor %r21, %r21, %r22
	ld %r0, 400(%r10)
	xor %r0, %r0, %r21
	std %r0, 400(%r10)
	ld %r0, 432(%r10)
	xor %r0, %r0, %r6
	std %r0, 432(%r10)
	ld %r0, 256(%r10)
	xor %r0, %r0, %r20
	std %r0, 256(%r10)
	ld %r0, 224(%r10)
	xor %r0, %r0, %r24
	std %r0, 224(%r10)
	rldicr %r12, %r9, 33, 30
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 232(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 32, 31
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 296(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 31, 32
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 360(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 30, 33
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 424(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 29, 34
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 488(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 28, 35
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 56(%r10)
	xor %r18, %r18, %r0
	or %r6, %r18, %r17
	xor %r6, %r6, %r17
	xor %r2, %r16, %r12
	or %r19, %r6, %r2
	xor %r20, %r15, %r12
	or %r21, %r20, %r18
	xor %r21, %r21, %r18
	xor %r22, %r19, %r21
	xor %r23, %r17, %r2
	or %r24, %r23, %r12
	xor %r24, %r24, %r12
	xor %r19, %r19, %r24
	or %r24, %r22, %r19
	xor %r24, %r24, %r19
	and %r25, %r12, %r22
	or %r25, %r15, %r25
	and %r25, %r18, %r25
	xor %r25, %r23, %r25
	or %r26, %r22, %r14
	xor %r26, %r26, %r14
	xor %r26, %r26, %r25
	and %r2, %r2, %r20
	xor %r20, %r18, %r15
	xor %r27, %r19, %r20
	or %r27, %r16, %r27
	or %r27, %r27, %r2
	xor %r27, %r27, %r2
	or %r21, %r21, %r20
	or %r20, %r25, %r21
	xor %r20, %r20, %r21
	and %r12, %r15, %r12
	or %r2, %r12, %r17
	xor %r2, %r2, %r17
	xor %r20, %r20, %r2
	and %r19, %r19, %r20
	or %r12, %r23, %r12
	or %r12, %r12, %r19
	xor %r12, %r12, %r19
	xor %r18, %r18, %r12
	and %r27, %r27, %r14
	xor %r27, %r27, %r18
	xor %r22, %r22, %r11
	or %r17, %r17, %r22
	or %r16, %r16, %r17
	xor %r23, %r23, %r16
	xor %r21, %r21, %r23
	xor %r24, %r24, %r11
	and %r24, %r24, %r14
	xor %r24, %r24, %r21
	and %r15, %r15, %r22
	xor %r25, %r25, %r15
	or %r23, %r23, %r25
	xor %r6, %r6, %r18
	xor %r23, %r23, %r6
	or %r20, %r20, %r14
	xor %r20, %r20, %r23
	ld %r0, 176(%r10)
	xor %r0, %r0, %r26
	std %r0, 176(%r10)
	ld %r0, 128(%r10)
	xor %r0, %r0, %r20
	std %r0, 128(%r10)
	ld %r0, 32(%r10)
	xor %r0, %r0, %r27
	std %r0, 32(%r10)
	ld %r0, 16(%r10)
	xor %r0, %r0, %r24
	std %r0, 16(%r10)
	rldicr %r12, %r9, 39, 24
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 472(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 38, 25
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 40(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 37, 26
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 104(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 36, 27
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 168(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 35, 28
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 232(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 34, 29
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 296(%r10)
	xor %r18, %r18, %r0
	xor %r18, %r18, %r16
	xor %r16, %r16, %r14
	or %r6, %r17, %r15
	xor %r6, %r14, %r6
	xor %r6, %r6, %r11
	and %r6, %r6, %r16
	or %r2, %r16, %r17
	xor %r2, %r2, %r17
	xor %r19, %r15, %r2
	or %r20, %r18, %r19
	or %r20, %r20, %r6
	xor %r20, %r20, %r6
	xor %r21, %r17, %r20
	and %r19, %r19, %r21
	or %r16, %r16, %r19
	xor %r16, %r16, %r19
	xor %r18, %r18, %r21
	xor %r16, %r16, %r11
	and %r16, %r16, %r18
	xor %r6, %r6, %r16
	xor %r17, %r17, %r15
	or %r14, %r14, %r2
	xor %r18, %r18, %r14
	or %r14, %r18, %r17
	xor %r14, %r14, %r17
	xor %r20, %r20, %r14
	or %r14, %r12, %r6
	xor %r14, %r14, %r6
	xor %r14, %r14, %r20
	xor %r20, %r20, %r11
	or %r2, %r6, %r12
	xor %r2, %r2, %r12
	xor %r2, %r2, %r20
	xor %r6, %r6, %r20
	or %r6, %r6, %r17
	xor %r6, %r6, %r17
	or %r19, %r19, %r6
	xor %r18, %r18, %r19
	or %r19, %r21, %r12
	xor %r19, %r19, %r18
	and %r12, %r12, %r21
	xor %r12, %r12, %r18
	ld %r0, 496(%r10)
	xor %r0, %r0, %r12
	std %r0, 496(%r10)
	ld %r0, 416(%r10)
	xor %r0, %r0, %r19
	std %r0, 416(%r10)
	ld %r0, 272(%r10)
	xor %r0, %r0, %r2
	std %r0, 272(%r10)
	ld %r0, 384(%r10)
	xor %r0, %r0, %r14
	std %r0, 384(%r10)
	rldicr %r12, %r9, 45, 18
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 216(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 44, 19
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 280(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 43, 20
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 344(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 42, 21
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 408(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 41, 22
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 472(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 40, 23
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 40(%r10)
	xor %r18, %r18, %r0
	or %r6, %r18, %r16
	or %r2, %r6, %r12
	xor %r2, %r2, %r12
	xor %r19, %r18, %r2
	xor %r20, %r16, %r19
	or %r21, %r15, %r20
	or %r2, %r2, %r15
	xor %r2, %r2, %r15
	xor %r16, %r16, %r2
	and %r2, %r14, %r16
	or %r20, %r18, %r20
	xor %r2, %r2, %r20
	xor %r2, %r15, %r2
	xor %r12, %r12, %r2
	or %r22, %r19, %r12
	and %r23, %r14, %r22
	xor %r24, %r19, %r23
	and %r25, %r15, %r20
	xor %r24, %r24, %r25
	or %r22, %r22, %r18
	xor %r22, %r22, %r18
	xor %r25, %r16, %r22
	xor %r14, %r14, %r21
	xor %r25, %r25, %r11
	and %r25, %r25, %r14
	xor %r25, %r25, %r11
	or %r25, %r25, %r17
	xor %r25, %r25, %r17
	xor %r25, %r25, %r2
	or %r2, %r16, %r23
	xor %r2, %r2, %r23
	xor %r22, %r22, %r14
	or %r22, %r24, %r22
	or %r22, %r22, %r2
	xor %r22, %r22, %r2
	or %r2, %r21, %r22
	xor %r2, %r2, %r22
	and %r12, %r12, %r22
	xor %r14, %r14, %r12
	and %r20, %r16, %r20
	or %r20, %r14, %r20
	xor %r23, %r23, %r20
	and %r23, %r23, %r17
	xor %r23, %r23, %r24
	xor %r18, %r18, %r6
	xor %r22, %r22, %r18
	and %r15, %r15, %r14
	xor %r22, %r22, %r15
	or %r2, %r2, %r17
	xor %r2, %r2, %r22
	xor %r16, %r21, %r16
	or %r16, %r16, %r22
	xor %r16, %r16, %r22
	xor %r19, %r19, %r14
	xor %r16, %r16, %r19
	and %r21, %r21, %r17
	xor %r21, %r21, %r16
	ld %r0, 368(%r10)
	xor %r0, %r0, %r23
	std %r0, 368(%r10)
	ld %r0, 448(%r10)
	xor %r0, %r0, %r25
	std %r0, 448(%r10)
	ld %r0, 160(%r10)
	xor %r0, %r0, %r21
	std %r0, 160(%r10)
	ld %r0, 48(%r10)
	xor %r0, %r0, %r2
	std %r0, 48(%r10)
	rldicr %r12, %r9, 51, 12
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 456(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 50, 13
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 24(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 49, 14
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 88(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 48, 15
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 152(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 47, 16
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 216(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 46, 17
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 280(%r10)
	xor %r18, %r18, %r0
	xor %r6, %r17, %r14
	or %r2, %r17, %r12
	and %r2, %r18, %r2
	xor %r6, %r6, %r2
	xor %r19, %r12, %r6
	or %r20, %r14, %r19
	xor %r20, %r20, %r19
	and %r19, %r18, %r19
	xor %r21, %r17, %r19
	xor %r22, %r18, %r16
	or %r23, %r21, %r22
	xor %r24, %r6, %r23
	and %r25, %r16, %r24
	or %r26, %r25, %r12
	xor %r26, %r26, %r12
	or %r21, %r20, %r21
	xor %r27, %r26, %r21
	and %r28, %r27, %r15
	xor %r28, %r28, %r24
	xor %r23, %r17, %r23
	or %r29, %r12, %r23
	xor %r29, %r29, %r23
	xor %r16, %r16, %r29
	or %r29, %r14, %r25
	xor %r29, %r29, %r25
	or %r29, %r16, %r29
	or %r17, %r17, %r22
	xor %r27, %r27, %r17
	or %r2, %r2, %r29
	xor %r27, %r27, %r2
	or %r24, %r18, %r24
	and %r21, %r21, %r24
	xor %r21, %r16, %r21
	xor %r26, %r26, %r11
	and %r26, %r26, %r21
	or %r20, %r20, %r15
	xor %r20, %r20, %r26
	xor %r6, %r6, %r21
	or %r14, %r14, %r6
	xor %r14, %r14, %r6
	xor %r17, %r17, %r11
	xor %r23, %r23, %r17
	xor %r14, %r14, %r23
	or %r14, %r14, %r15
	xor %r14, %r14, %r15
	xor %r14, %r14, %r27
	xor %r12, %r12, %r19
	xor %r18, %r18, %r16
	and %r12, %r12, %r18
	xor %r25, %r25, %r23
	xor %r12, %r12, %r25
	or %r29, %r29, %r15
	xor %r29, %r29, %r15
	xor %r29, %r29, %r12
	ld %r0, 336(%r10)
	xor %r0, %r0, %r28
	std %r0, 336(%r10)
	ld %r0, 352(%r10)
	xor %r0, %r0, %r20
	std %r0, 352(%r10)
	ld %r0, 192(%r10)
	xor %r0, %r0, %r14
	std %r0, 192(%r10)
	ld %r0, 304(%r10)
	xor %r0, %r0, %r29
	std %r0, 304(%r10)
	rldicr %r12, %r9, 57, 6
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 200(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 56, 7
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 264(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 55, 8
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 328(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 54, 9
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 392(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 53, 10
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 456(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 52, 11
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 24(%r10)
	xor %r18, %r18, %r0
	xor %r6, %r15, %r14
	xor %r2, %r16, %r6
	and %r19, %r12, %r2
	and %r20, %r15, %r6
	xor %r21, %r17, %r20
	and %r22, %r19, %r21
	and %r23, %r12, %r20
	xor %r24, %r16, %r23
	or %r25, %r21, %r24
	xor %r6, %r12, %r6
	xor %r26, %r25, %r6
	or %r27, %r18, %r22
	xor %r27, %r27, %r22
	xor %r27, %r27, %r26
	xor %r2, %r2, %r11
	and %r2, %r2, %r14
	or %r26, %r21, %r2
	xor %r24, %r19, %r24
	xor %r26, %r26, %r24
	xor %r19, %r19, %r6
	or %r15, %r15, %r19
	xor %r15, %r15, %r19
	or %r6, %r21, %r15
	xor %r6, %r6, %r15
	xor %r14, %r14, %r24
	xor %r6, %r6, %r14
	or %r19, %r19, %r23
	xor %r19, %r19, %r23
	or %r15, %r15, %r19
	xor %r25, %r17, %r25
	and %r25, %r6, %r25
	xor %r25, %r15, %r25
	and %r23, %r25, %r18
	xor %r23, %r23, %r6
	or %r21, %r21, %r16
	xor %r21, %r21, %r16
	or %r19, %r19, %r21
	or %r20, %r20, %r6
	and %r19, %r19, %r20
	xor %r25, %r25, %r19
	xor %r2, %r2, %r15
	and %r12, %r12, %r2
	or %r22, %r22, %r12
	xor %r19, %r19, %r22
	or %r12, %r19, %r18
	xor %r12, %r12, %r18
	xor %r12, %r12, %r26
	and %r17, %r17, %r22
	xor %r26, %r26, %r11
	xor %r17, %r17, %r26
	xor %r19, %r19, %r17
	or %r25, %r25, %r18
	xor %r25, %r25, %r19
	ld %r0, 112(%r10)
	xor %r0, %r0, %r27
	std %r0, 112(%r10)
	ld %r0, 144(%r10)
	xor %r0, %r0, %r23
	std %r0, 144(%r10)
	ld %r0, 288(%r10)
	xor %r0, %r0, %r25
	std %r0, 288(%r10)
	ld %r0, 0(%r10)
	xor %r0, %r0, %r12
	std %r0, 0(%r10)
	rldicr %r12, %r9, 63, 0
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 504(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 62, 1
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 8(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 61, 2
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 72(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 60, 3
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 136(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 59, 4
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 200(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 58, 5
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 264(%r10)
	xor %r18, %r18, %r0
	or %r6, %r16, %r17
	xor %r6, %r6, %r17
	or %r2, %r14, %r16
	xor %r2, %r2, %r16
	xor %r2, %r15, %r2
	and %r19, %r18, %r2
	or %r20, %r19, %r6
	xor %r20, %r20, %r6
	or %r21, %r17, %r2
	xor %r21, %r21, %r2
	or %r22, %r18, %r21
	or %r23, %r17, %r16
	xor %r23, %r23, %r16
	xor %r23, %r14, %r23
	and %r24, %r22, %r23
	or %r19, %r19, %r24
	xor %r2, %r2, %r11
	xor %r24, %r24, %r2
	or %r16, %r16, %r22
	xor %r16, %r16, %r22
	xor %r24, %r24, %r16
	xor %r6, %r6, %r24
	or %r16, %r20, %r12
	xor %r16, %r16, %r6
	xor %r6, %r18, %r6
	and %r22, %r14, %r6
	xor %r24, %r17, %r24
	xor %r22, %r22, %r24
	xor %r21, %r21, %r22
	xor %r22, %r19, %r22
	or %r17, %r17, %r22
	xor %r14, %r14, %r6
	xor %r17, %r17, %r14
	and %r19, %r19, %r12
	xor %r19, %r19, %r17
	xor %r23, %r23, %r21
	or %r24, %r15, %r24
	xor %r24, %r23, %r24
	xor %r18, %r18, %r24
	and %r18, %r18, %r12
	xor %r18, %r18, %r21
	or %r23, %r23, %r15
	xor %r23, %r23, %r15
	and %r17, %r17, %r23
	xor %r20, %r20, %r24
	xor %r17, %r17, %r20
	or %r17, %r17, %r12
	xor %r17, %r17, %r21
	ld %r0, 208(%r10)
	xor %r0, %r0, %r18
	std %r0, 208(%r10)
	ld %r0, 96(%r10)
	xor %r0, %r0, %r19
	std %r0, 96(%r10)
	ld %r0, 320(%r10)
	xor %r0, %r0, %r16
	std %r0, 320(%r10)
	ld %r0, 240(%r10)
	xor %r0, %r0, %r17
	std %r0, 240(%r10)
	ld %r9, 0(%r3)
	xor %r9, %r9, %r11
	addi %r3, %r3, 8
	rldicr %r12, %r9, 21, 42
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 240(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 20, 43
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 304(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 19, 44
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 368(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 18, 45
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 432(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 17, 46
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 496(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 16, 47
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 0(%r10)
	xor %r18, %r18, %r0
	or %r6, %r18, %r14
	xor %r6, %r6, %r14
	xor %r2, %r15, %r6
	or %r19, %r16, %r12
	xor %r20, %r18, %r16
	and %r21, %r19, %r20
	xor %r22, %r15, %r21
	or %r23, %r22, %r2
	xor %r23, %r23, %r2
	xor %r24, %r14, %r12
	xor %r25, %r16, %r24
	xor %r25, %r25, %r11
	and %r25, %r25, %r2
	or %r21, %r12, %r21
	xor %r25, %r25, %r21
	or %r21, %r25, %r23
	xor %r21, %r21, %r23
	or %r12, %r18, %r12
	or %r26, %r25, %r12
	xor %r22, %r22, %r11
	and %r22, %r22, %r14
	xor %r27, %r26, %r22
	or %r15, %r15, %r12
	xor %r15, %r15, %r12
	xor %r15, %r22, %r15
	xor %r20, %r20, %r11
	and %r20, %r20, %r24
	or %r15, %r15, %r20
	or %r16, %r16, %r6
	xor %r16, %r16, %r6
	xor %r6, %r2, %r26
	or %r6, %r6, %r16
	xor %r6, %r6, %r16
	xor %r16, %r6, %r11
	and %r25, %r19, %r25
	xor %r16, %r16, %r25
	or %r27, %r27, %r17
	xor %r27, %r27, %r17
	xor %r27, %r27, %r16
	xor %r6, %r24, %r6
	or %r22, %r22, %r6
	xor %r22, %r19, %r22
	xor %r18, %r18, %r22
	xor %r16, %r16, %r18
	or %r23, %r23, %r17
	xor %r23, %r23, %r16
	xor %r19, %r19, %r26
	or %r19, %r15, %r19
	xor %r19, %r18, %r19
	or %r24, %r24, %r16
	xor %r24, %r19, %r24
	or %r16, %r21, %r17
	xor %r16, %r16, %r24
	or %r14, %r14, %r2
	or %r14, %r14, %r19
	xor %r14, %r14, %r19
	and %r21, %r21, %r18
	xor %r14, %r14, %r21
	or %r14, %r14, %r17
	xor %r14, %r14, %r15
	ld %r0, 72(%r10)
	xor %r0, %r0, %r14
	std %r0, 72(%r10)
	ld %r0, 88(%r10)
	xor %r0, %r0, %r27
	std %r0, 88(%r10)
	ld %r0, 472(%r10)
	xor %r0, %r0, %r16
	std %r0, 472(%r10)
	ld %r0, 488(%r10)
	xor %r0, %r0, %r23
	std %r0, 488(%r10)
	rldicr %r12, %r9, 27, 36
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 480(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 26, 37
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 48(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 25, 38
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 112(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 24, 39
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 176(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 23, 40
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 240(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 22, 41
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 304(%r10)
	xor %r18, %r18, %r0
	xor %r6, %r17, %r14
	or %r2, %r18, %r12
	xor %r2, %r2, %r12
	xor %r2, %r2, %r11
	and %r2, %r2, %r14
	or %r19, %r17, %r2
	or %r20, %r6, %r12
	xor %r20, %r20, %r12
	and %r21, %r18, %r6
	xor %r14, %r14, %r21
	or %r21, %r14, %r20
	xor %r21, %r21, %r20
	and %r22, %r16, %r12
	xor %r2, %r2, %r20
	and %r2, %r19, %r2
	or %r20, %r2, %r22
	xor %r20, %r20, %r22
	and %r23, %r16, %r2
	xor %r18, %r18, %r11
	xor %r18, %r23, %r18
	xor %r12, %r12, %r6
	or %r24, %r12, %r22
	xor %r24, %r24, %r22
	xor %r25, %r18, %r24
	xor %r20, %r20, %r11
	and %r20, %r20, %r15
	xor %r20, %r20, %r25
	or %r17, %r17, %r24
	xor %r17, %r17, %r24
	xor %r14, %r14, %r17
	or %r18, %r18, %r14
	xor %r18, %r18, %r14
	xor %r16, %r16, %r12
	xor %r18, %r18, %r16
	or %r24, %r19, %r15
	xor %r24, %r24, %r15
	xor %r24, %r24, %r18
	xor %r23, %r23, %r17
	or %r16, %r16, %r23
	xor %r19, %r19, %r25
	or %r22, %r22, %r19
	xor %r23, %r16, %r22
	xor %r2, %r2, %r25
	xor %r18, %r18, %r2
	and %r22, %r22, %r18
	and %r6, %r6, %r16
	xor %r22, %r22, %r6
	or %r6, %r22, %r15
	xor %r6, %r6, %r23
	or %r22, %r22, %r14
	xor %r22, %r22, %r14
	or %r12, %r12, %r19
	xor %r22, %r22, %r12
	or %r21, %r21, %r15
	xor %r21, %r21, %r22
	ld %r0, 408(%r10)
	xor %r0, %r0, %r21
	std %r0, 408(%r10)
	ld %r0, 440(%r10)
	xor %r0, %r0, %r6
	std %r0, 440(%r10)
	ld %r0, 264(%r10)
	xor %r0, %r0, %r20
	std %r0, 264(%r10)
	ld %r0, 232(%r10)
	xor %r0, %r0, %r24
	std %r0, 232(%r10)
	rldicr %r12, %r9, 33, 30
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 224(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 32, 31
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 288(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 31, 32
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 352(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 30, 33
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 416(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 29, 34
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 480(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 28, 35
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 48(%r10)
	xor %r18, %r18, %r0
	or %r6, %r18, %r17
	xor %r6, %r6, %r17
	xor %r2, %r16, %r12
	or %r19, %r6, %r2
	xor %r20, %r15, %r12
	or %r21, %r20, %r18
	xor %r21, %r21, %r18
	xor %r22, %r19, %r21
	xor %r23, %r17, %r2
	or %r24, %r23, %r12
	xor %r24, %r24, %r12
	xor %r19, %r19, %r24
	or %r24, %r22, %r19
	xor %r24, %r24, %r19
	and %r25, %r12, %r22
	or %r25, %r15, %r25
	and %r25, %r18, %r25
	xor %r25, %r23, %r25
	or %r26, %r22, %r14
	xor %r26, %r26, %r14
	xor %r26, %r26, %r25
	and %r2, %r2, %r20
	xor %r20, %r18, %r15
	xor %r27, %r19, %r20
	or %r27, %r16, %r27
	or %r27, %r27, %r2
	xor %r27, %r27, %r2
	or %r21, %r21, %r20
	or %r20, %r25, %r21
	xor %r20, %r20, %r21
	and %r12, %r15, %r12
	or %r2, %r12, %r17
	xor %r2, %r2, %r17
	xor %r20, %r20, %r2
	and %r19, %r19, %r20
	or %r12, %r23, %r12
	or %r12, %r12, %r19
	xor %r12, %r12, %r19
	xor %r18, %r18, %r12
	and %r27, %r27, %r14
	xor %r27, %r27, %r18
	xor %r22, %r22, %r11
	or %r17, %r17, %r22
	or %r16, %r16, %r17
	xor %r23, %r23, %r16
	xor %r21, %r21, %r23
	xor %r24, %r24, %r11
	and %r24, %r24, %r14
	xor %r24, %r24, %r21
	and %r15, %r15, %r22
	xor %r25, %r25, %r15
	or %r23, %r23, %r25
	xor %r6, %r6, %r18
	xor %r23, %r23, %r6
	or %r20, %r20, %r14
	xor %r20, %r20, %r23
	ld %r0, 184(%r10)
	xor %r0, %r0, %r26
	std %r0, 184(%r10)
	ld %r0, 136(%r10)
	xor %r0, %r0, %r20
	std %r0, 136(%r10)
	ld %r0, 40(%r10)
	xor %r0, %r0, %r27
	std %r0, 40(%r10)
	ld %r0, 24(%r10)
	xor %r0, %r0, %r24
	std %r0, 24(%r10)
	rldicr %r12, %r9, 39, 24
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 464(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 38, 25
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 32(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 37, 26
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 96(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 36, 27
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 160(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 35, 28
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 224(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 34, 29
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 288(%r10)
	xor %r18, %r18, %r0
	xor %r18, %r18, %r16
	xor %r16, %r16, %r14
	or %r6, %r17, %r15
	xor %r6, %r14, %r6
	xor %r6, %r6, %r11
	and %r6, %r6, %r16
	or %r2, %r16, %r17
	xor %r2, %r2, %r17
	xor %r19, %r15, %r2
	or %r20, %r18, %r19
	or %r20, %r20, %r6
	xor %r20, %r20, %r6
	xor %r21, %r17, %r20
	and %r19, %r19, %r21
	or %r16, %r16, %r19
	xor %r16, %r16, %r19
	xor %r18, %r18, %r21
	xor %r16, %r16, %r11
	and %r16, %r16, %r18
	xor %r6, %r6, %r16
	xor %r17, %r17, %r15
	or %r14, %r14, %r2
	xor %r18, %r18, %r14
	or %r14, %r18, %r17
	xor %r14, %r14, %r17
	xor %r20, %r20, %r14
	or %r14, %r12, %r6
	xor %r14, %r14, %r6
	xor %r14, %r14, %r20
	xor %r20, %r20, %r11
	or %r2, %r6, %r12
	xor %r2, %r2, %r12
	xor %r2, %r2, %r20
	xor %r6, %r6, %r20
	or %r6, %r6, %r17
	xor %r6, %r6, %r17
	or %r19, %r19, %r6
	xor %r18, %r18, %r19
	or %r19, %r21, %r12
	xor %r19, %r19, %r18
	and %r12, %r12, %r21
	xor %r12, %r12, %r18
	ld %r0, 504(%r10)
	xor %r0, %r0, %r12
	std %r0, 504(%r10)
	ld %r0, 424(%r10)
	xor %r0, %r0, %r19
	std %r0, 424(%r10)
	ld %r0, 280(%r10)
	xor %r0, %r0, %r2
	std %r0, 280(%r10)
	ld %r0, 392(%r10)
	xor %r0, %r0, %r14
	std %r0, 392(%r10)
	rldicr %r12, %r9, 45, 18
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 208(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 44, 19
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 272(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 43, 20
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 336(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 42, 21
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 400(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 41, 22
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 464(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 40, 23
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 32(%r10)
	xor %r18, %r18, %r0
	or %r6, %r18, %r16
	or %r2, %r6, %r12
	xor %r2, %r2, %r12
	xor %r19, %r18, %r2
	xor %r20, %r16, %r19
	or %r21, %r15, %r20
	or %r2, %r2, %r15
	xor %r2, %r2, %r15
	xor %r16, %r16, %r2
	and %r2, %r14, %r16
	or %r20, %r18, %r20
	xor %r2, %r2, %r20
	xor %r2, %r15, %r2
	xor %r12, %r12, %r2
	or %r22, %r19, %r12
	and %r23, %r14, %r22
	xor %r24, %r19, %r23
	and %r25, %r15, %r20
	xor %r24, %r24, %r25
	or %r22, %r22, %r18
	xor %r22, %r22, %r18
	xor %r25, %r16, %r22
	xor %r14, %r14, %r21
	xor %r25, %r25, %r11
	and %r25, %r25, %r14
	xor %r25, %r25, %r11
	or %r25, %r25, %r17
	xor %r25, %r25, %r17
	xor %r25, %r25, %r2
	or %r2, %r16, %r23
	xor %r2, %r2, %r23
	xor %r22, %r22, %r14
	or %r22, %r24, %r22
	or %r22, %r22, %r2
	xor %r22, %r22, %r2
	or %r2, %r21, %r22
	xor %r2, %r2, %r22
	and %r12, %r12, %r22
	xor %r14, %r14, %r12
	and %r20, %r16, %r20
	or %r20, %r14, %r20
	xor %r23, %r23, %r20
	and %r23, %r23, %r17
	xor %r23, %r23, %r24
	xor %r18, %r18, %r6
	xor %r22, %r22, %r18
	and %r15, %r15, %r14
	xor %r22, %r22, %r15
	or %r2, %r2, %r17
	xor %r2, %r2, %r22
	xor %r16, %r21, %r16
	or %r16, %r16, %r22
	xor %r16, %r16, %r22
	xor %r19, %r19, %r14
	xor %r16, %r16, %r19
	and %r21, %r21, %r17
	xor %r21, %r21, %r16
	ld %r0, 376(%r10)
	xor %r0, %r0, %r23
	std %r0, 376(%r10)
	ld %r0, 456(%r10)
	xor %r0, %r0, %r25
	std %r0, 456(%r10)
	ld %r0, 168(%r10)
	xor %r0, %r0, %r21
	std %r0, 168(%r10)
	ld %r0, 56(%r10)
	xor %r0, %r0, %r2
	std %r0, 56(%r10)
	rldicr %r12, %r9, 51, 12
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 448(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 50, 13
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 16(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 49, 14
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 80(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 48, 15
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 144(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 47, 16
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 208(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 46, 17
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 272(%r10)
	xor %r18, %r18, %r0
	xor %r6, %r17, %r14
	or %r2, %r17, %r12
	and %r2, %r18, %r2
	xor %r6, %r6, %r2
	xor %r19, %r12, %r6
	or %r20, %r14, %r19
	xor %r20, %r20, %r19
	and %r19, %r18, %r19
	xor %r21, %r17, %r19
	xor %r22, %r18, %r16
	or %r23, %r21, %r22
	xor %r24, %r6, %r23
	and %r25, %r16, %r24
	or %r26, %r25, %r12
	xor %r26, %r26, %r12
	or %r21, %r20, %r21
	xor %r27, %r26, %r21
	and %r28, %r27, %r15
	xor %r28, %r28, %r24
	xor %r23, %r17, %r23
	or %r29, %r12, %r23
	xor %r29, %r29, %r23
	xor %r16, %r16, %r29
	or %r29, %r14, %r25
	xor %r29, %r29, %r25
	or %r29, %r16, %r29
	or %r17, %r17, %r22
	xor %r27, %r27, %r17
	or %r2, %r2, %r29
	xor %r27, %r27, %r2
	or %r24, %r18, %r24
	and %r21, %r21, %r24
	xor %r21, %r16, %r21
	xor %r26, %r26, %r11
	and %r26, %r26, %r21
	or %r20, %r20, %r15
	xor %r20, %r20, %r26
	xor %r6, %r6, %r21
	or %r14, %r14, %r6
	xor %r14, %r14, %r6
	xor %r17, %r17, %r11
	xor %r23, %r23, %r17
	xor %r14, %r14, %r23
	or %r14, %r14, %r15
	xor %r14, %r14, %r15
	xor %r14, %r14, %r27
	xor %r12, %r12, %r19
	xor %r18, %r18, %r16
	and %r12, %r12, %r18
	xor %r25, %r25, %r23
	xor %r12, %r12, %r25
	or %r29, %r29, %r15
	xor %r29, %r29, %r15
	xor %r29, %r29, %r12
	ld %r0, 344(%r10)
	xor %r0, %r0, %r28
	std %r0, 344(%r10)
	ld %r0, 360(%r10)
	xor %r0, %r0, %r20
	std %r0, 360(%r10)
	ld %r0, 200(%r10)
	xor %r0, %r0, %r14
	std %r0, 200(%r10)
	ld %r0, 312(%r10)
	xor %r0, %r0, %r29
	std %r0, 312(%r10)
	rldicr %r12, %r9, 57, 6
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 192(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 56, 7
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 256(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 55, 8
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 320(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 54, 9
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 384(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 53, 10
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 448(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 52, 11
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 16(%r10)
	xor %r18, %r18, %r0
	xor %r6, %r15, %r14
	xor %r2, %r16, %r6
	and %r19, %r12, %r2
	and %r20, %r15, %r6
	xor %r21, %r17, %r20
	and %r22, %r19, %r21
	and %r23, %r12, %r20
	xor %r24, %r16, %r23
	or %r25, %r21, %r24
	xor %r6, %r12, %r6
	xor %r26, %r25, %r6
	or %r27, %r18, %r22
	xor %r27, %r27, %r22
	xor %r27, %r27, %r26
	xor %r2, %r2, %r11
	and %r2, %r2, %r14
	or %r26, %r21, %r2
	xor %r24, %r19, %r24
	xor %r26, %r26, %r24
	xor %r19, %r19, %r6
	or %r15, %r15, %r19
	xor %r15, %r15, %r19
	or %r6, %r21, %r15
	xor %r6, %r6, %r15
	xor %r14, %r14, %r24
	xor %r6, %r6, %r14
	or %r19, %r19, %r23
	xor %r19, %r19, %r23
	or %r15, %r15, %r19
	xor %r25, %r17, %r25
	and %r25, %r6, %r25
	xor %r25, %r15, %r25
	and %r23, %r25, %r18
	xor %r23, %r23, %r6
	or %r21, %r21, %r16
	xor %r21, %r21, %r16
	or %r19, %r19, %r21
	or %r20, %r20, %r6
	and %r19, %r19, %r20
	xor %r25, %r25, %r19
	xor %r2, %r2, %r15
	and %r12, %r12, %r2
	or %r22, %r22, %r12
	xor %r19, %r19, %r22
	or %r12, %r19, %r18
	xor %r12, %r12, %r18
	xor %r12, %r12, %r26
	and %r17, %r17, %r22
	xor %r26, %r26, %r11
	xor %r17, %r17, %r26
	xor %r19, %r19, %r17
	or %r25, %r25, %r18
	xor %r25, %r25, %r19
	ld %r0, 120(%r10)
	xor %r0, %r0, %r27
	std %r0, 120(%r10)
	ld %r0, 152(%r10)
	xor %r0, %r0, %r23
	std %r0, 152(%r10)
	ld %r0, 296(%r10)
	xor %r0, %r0, %r25
	std %r0, 296(%r10)
	ld %r0, 8(%r10)
	xor %r0, %r0, %r12
	std %r0, 8(%r10)
	rldicr %r12, %r9, 63, 0
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 496(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 62, 1
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 0(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 61, 2
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 64(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 60, 3
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 128(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 59, 4
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 192(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 58, 5
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 256(%r10)
	xor %r18, %r18, %r0
	or %r6, %r16, %r17
	xor %r6, %r6, %r17
	or %r2, %r14, %r16
	xor %r2, %r2, %r16
	xor %r2, %r15, %r2
	and %r19, %r18, %r2
	or %r20, %r19, %r6
	xor %r20, %r20, %r6
	or %r21, %r17, %r2
	xor %r21, %r21, %r2
	or %r22, %r18, %r21
	or %r23, %r17, %r16
	xor %r23, %r23, %r16
	xor %r23, %r14, %r23
	and %r24, %r22, %r23
	or %r19, %r19, %r24
	xor %r2, %r2, %r11
	xor %r24, %r24, %r2
	or %r16, %r16, %r22
	xor %r16, %r16, %r22
	xor %r24, %r24, %r16
	xor %r6, %r6, %r24
	or %r16, %r20, %r12
	xor %r16, %r16, %r6
	xor %r6, %r18, %r6
	and %r22, %r14, %r6
	xor %r24, %r17, %r24
	xor %r22, %r22, %r24
	xor %r21, %r21, %r22
	xor %r22, %r19, %r22
	or %r17, %r17, %r22
	xor %r14, %r14, %r6
	xor %r17, %r17, %r14
	and %r19, %r19, %r12
	xor %r19, %r19, %r17
	xor %r23, %r23, %r21
	or %r24, %r15, %r24
	xor %r24, %r23, %r24
	xor %r18, %r18, %r24
	and %r18, %r18, %r12
	xor %r18, %r18, %r21
	or %r23, %r23, %r15
	xor %r23, %r23, %r15
	and %r17, %r17, %r23
	xor %r20, %r20, %r24
	xor %r17, %r17, %r20
	or %r17, %r17, %r12
	xor %r17, %r17, %r21
	ld %r0, 216(%r10)
	xor %r0, %r0, %r18
	std %r0, 216(%r10)
	ld %r0, 104(%r10)
	xor %r0, %r0, %r19
	std %r0, 104(%r10)
	ld %r0, 328(%r10)
	xor %r0, %r0, %r16
	std %r0, 328(%r10)
	ld %r0, 248(%r10)
	xor %r0, %r0, %r17
	std %r0, 248(%r10)
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 26b
	ld %r12, 0(%r10)
	ld %r14, 8(%r10)
	std %r14, 0(%r10)
	std %r12, 8(%r10)
	ld %r12, 64(%r10)
	ld %r14, 72(%r10)
	std %r14, 64(%r10)
	std %r12, 72(%r10)
	ld %r12, 128(%r10)
	ld %r14, 136(%r10)
	std %r14, 128(%r10)
	std %r12, 136(%r10)
	ld %r12, 192(%r10)
	ld %r14, 200(%r10)
	std %r14, 192(%r10)
	std %r12, 200(%r10)
	ld %r12, 256(%r10)
	ld %r14, 264(%r10)
	std %r14, 256(%r10)
	std %r12, 264(%r10)
	ld %r12, 320(%r10)
	ld %r14, 328(%r10)
	std %r14, 320(%r10)
	std %r12, 328(%r10)
	ld %r12, 384(%r10)
	ld %r14, 392(%r10)
	std %r14, 384(%r10)
	std %r12, 392(%r10)
	ld %r12, 448(%r10)
	ld %r14, 456(%r10)
	std %r14, 448(%r10)
	std %r12, 456(%r10)
	ld %r12, 16(%r10)
	ld %r14, 24(%r10)
	std %r14, 16(%r10)
	std %r12, 24(%r10)
	ld %r12, 80(%r10)
	ld %r14, 88(%r10)
	std %r14, 80(%r10)
	std %r12, 88(%r10)
	ld %r12, 144(%r10)
	ld %r14, 152(%r10)
	std %r14, 144(%r10)
	std %r12, 152(%r10)
	ld %r12, 208(%r10)
	ld %r14, 216(%r10)
	std %r14, 208(%r10)
	std %r12, 216(%r10)
	ld %r12, 272(%r10)
	ld %r14, 280(%r10)
	std %r14, 272(%r10)
	std %r12, 280(%r10)
	ld %r12, 336(%r10)
	ld %r14, 344(%r10)
	std %r14, 336(%r10)
	std %r12, 344(%r10)
	ld %r12, 400(%r10)
	ld %r14, 408(%r10)
	std %r14, 400(%r10)
	std %r12, 408(%r10)
	ld %r12, 464(%r10)
	ld %r14, 472(%r10)
	std %r14, 464(%r10)
	std %r12, 472(%r10)
	ld %r12, 32(%r10)
	ld %r14, 40(%r10)
	std %r14, 32(%r10)
	std %r12, 40(%r10)
	ld %r12, 96(%r10)
	ld %r14, 104(%r10)
	std %r14, 96(%r10)
	std %r12, 104(%r10)
	ld %r12, 160(%r10)
	ld %r14, 168(%r10)
	std %r14, 160(%r10)
	std %r12, 168(%r10)
	ld %r12, 224(%r10)
	ld %r14, 232(%r10)
	std %r14, 224(%r10)
	std %r12, 232(%r10)
	ld %r12, 288(%r10)
	ld %r14, 296(%r10)
	std %r14, 288(%r10)
	std %r12, 296(%r10)
	ld %r12, 352(%r10)
	ld %r14, 360(%r10)
	std %r14, 352(%r10)
	std %r12, 360(%r10)
	ld %r12, 416(%r10)
	ld %r14, 424(%r10)
	std %r14, 416(%r10)
	std %r12, 424(%r10)
	ld %r12, 480(%r10)
	ld %r14, 488(%r10)
	std %r14, 480(%r10)
	std %r12, 488(%r10)
	ld %r12, 48(%r10)
	ld %r14, 56(%r10)
	std %r14, 48(%r10)
	std %r12, 56(%r10)
	ld %r12, 112(%r10)
	ld %r14, 120(%r10)
	std %r14, 112(%r10)
	std %r12, 120(%r10)
	ld %r12, 176(%r10)
	ld %r14, 184(%r10)
	std %r14, 176(%r10)
	std %r12, 184(%r10)
	ld %r12, 240(%r10)
	ld %r14, 248(%r10)
	std %r14, 240(%r10)
	std %r12, 248(%r10)
	ld %r12, 304(%r10)
	ld %r14, 312(%r10)
	std %r14, 304(%r10)
	std %r12, 312(%r10)
	ld %r12, 368(%r10)
	ld %r14, 376(%r10)
	std %r14, 368(%r10)
	std %r12, 376(%r10)
	ld %r12, 432(%r10)
	ld %r14, 440(%r10)
	std %r14, 432(%r10)
	std %r12, 440(%r10)
	ld %r12, 496(%r10)
	ld %r14, 504(%r10)
	std %r14, 496(%r10)
	std %r12, 504(%r10)
	addi %r3, %r7, 248
	li %r5, 8
27:
	ld %r9, 0(%r3)
	xor %r9, %r9, %r11
	addi %r3, %r3, -8
	rldicr %r12, %r9, 21, 42
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 248(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 20, 43
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 312(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 19, 44
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 376(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 18, 45
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 440(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 17, 46
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 504(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 16, 47
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 8(%r10)
	xor %r18, %r18, %r0
	or %r6, %r18, %r14
	xor %r6, %r6, %r14
	xor %r2, %r15, %r6
	or %r19, %r16, %r12
	xor %r20, %r18, %r16
	and %r21, %r19, %r20
	xor %r22, %r15, %r21
	or %r23, %r22, %r2
	xor %r23, %r23, %r2
	xor %r24, %r14, %r12
	xor %r25, %r16, %r24
	xor %r25, %r25, %r11
	and %r25, %r25, %r2
	or %r21, %r12, %r21
	xor %r25, %r25, %r21
	or %r21, %r25, %r23
	xor %r21, %r21, %r23
	or %r12, %r18, %r12
	or %r26, %r25, %r12
	xor %r22, %r22, %r11
	and %r22, %r22, %r14
	xor %r27, %r26, %r22
	or %r15, %r15, %r12
	xor %r15, %r15, %r12
	xor %r15, %r22, %r15
	xor %r20, %r20, %r11
	and %r20, %r20, %r24
	or %r15, %r15, %r20
	or %r16, %r16, %r6
	xor %r16, %r16, %r6
	xor %r6, %r2, %r26
	or %r6, %r6, %r16
	xor %r6, %r6, %r16
	xor %r16, %r6, %r11
	and %r25, %r19, %r25
	xor %r16, %r16, %r25
	or %r27, %r27, %r17
	xor %r27, %r27, %r17
	xor %r27, %r27, %r16
	xor %r6, %r24, %r6
	or %r22, %r22, %r6
	xor %r22, %r19, %r22
	xor %r18, %r18, %r22
	xor %r16, %r16, %r18
	or %r23, %r23, %r17
	xor %r23, %r23, %r16
	xor %r19, %r19, %r26
	or %r19, %r15, %r19
	xor %r19, %r18, %r19
	or %r24, %r24, %r16
	xor %r24, %r19, %r24
	or %r16, %r21, %r17
	xor %r16, %r16, %r24
	or %r14, %r14, %r2
	or %r14, %r14, %r19
	xor %r14, %r14, %r19
	and %r21, %r21, %r18
	xor %r14, %r14, %r21
	or %r14, %r14, %r17
	xor %r14, %r14, %r15
	ld %r0, 64(%r10)
	xor %r0, %r0, %r14
	std %r0, 64(%r10)
	ld %r0, 80(%r10)
	xor %r0, %r0, %r27
	std %r0, 80(%r10)
	ld %r0, 464(%r10)
	xor %r0, %r0, %r16
	std %r0, 464(%r10)
	ld %r0, 480(%r10)
	xor %r0, %r0, %r23
	std %r0, 480(%r10)
	rldicr %r12, %r9, 27, 36
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 488(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 26, 37
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 56(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 25, 38
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 120(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 24, 39
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 184(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 23, 40
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 248(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 22, 41
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 312(%r10)
	xor %r18, %r18, %r0
	xor %r6, %r17, %r14
	or %r2, %r18, %r12
	xor %r2, %r2, %r12
	xor %r2, %r2, %r11
	and %r2, %r2, %r14
	or %r19, %r17, %r2
	or %r20, %r6, %r12
	xor %r20, %r20, %r12
	and %r21, %r18, %r6
	xor %r14, %r14, %r21
	or %r21, %r14, %r20
	xor %r21, %r21, %r20
	and %r22, %r16, %r12
	xor %r2, %r2, %r20
	and %r2, %r19, %r2
	or %r20, %r2, %r22
	xor %r20, %r20, %r22
	and %r23, %r16, %r2
	xor %r18, %r18, %r11
	xor %r18, %r23, %r18
	xor %r12, %r12, %r6
	or %r24, %r12, %r22
	xor %r24, %r24, %r22
	xor %r25, %r18, %r24
	xor %r20, %r20, %r11
	and %r20, %r20, %r15
	xor %r20, %r20, %r25
	or %r17, %r17, %r24
	xor %r17, %r17, %r24
	xor %r14, %r14, %r17
	or %r18, %r18, %r14
	xor %r18, %r18, %r14
	xor %r16, %r16, %r12
	xor %r18, %r18, %r16
	or %r24, %r19, %r15
	xor %r24, %r24, %r15
	xor %r24, %r24, %r18
	xor %r23, %r23, %r17
	or %r16, %r16, %r23
	xor %r19, %r19, %r25
	or %r22, %r22, %r19
	xor %r23, %r16, %r22
	xor %r2, %r2, %r25
	xor %r18, %r18, %r2
	and %r22, %r22, %r18
	and %r6, %r6, %r16
	xor %r22, %r22, %r6
	or %r6, %r22, %r15
	xor %r6, %r6, %r23
	or %r22, %r22, %r14
	xor %r22, %r22, %r14
	or %r12, %r12, %r19
	xor %r22, %r22, %r12
	or %r21, %r21, %r15
	xor %r21, %r21, %r22
	ld %r0, 400(%r10)
	xor %r0, %r0, %r21
	std %r0, 400(%r10)
	ld %r0, 432(%r10)
	xor %r0, %r0, %r6
	std %r0, 432(%r10)
	ld %r0, 256(%r10)
	xor %r0, %r0, %r20
	std %r0, 256(%r10)
	ld %r0, 224(%r10)
	xor %r0, %r0, %r24
	std %r0, 224(%r10)
	rldicr %r12, %r9, 33, 30
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 232(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 32, 31
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 296(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 31, 32
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 360(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 30, 33
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 424(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 29, 34
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 488(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 28, 35
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 56(%r10)
	xor %r18, %r18, %r0
	or %r6, %r18, %r17
	xor %r6, %r6, %r17
	xor %r2, %r16, %r12
	or %r19, %r6, %r2
	xor %r20, %r15, %r12
	or %r21, %r20, %r18
	xor %r21, %r21, %r18
	xor %r22, %r19, %r21
	xor %r23, %r17, %r2
	or %r24, %r23, %r12
	xor %r24, %r24, %r12
	xor %r19, %r19, %r24
	or %r24, %r22, %r19
	xor %r24, %r24, %r19
	and %r25, %r12, %r22
	or %r25, %r15, %r25
	and %r25, %r18, %r25
	xor %r25, %r23, %r25
	or %r26, %r22, %r14
	xor %r26, %r26, %r14
	xor %r26, %r26, %r25
	and %r2, %r2, %r20
	xor %r20, %r18, %r15
	xor %r27, %r19, %r20
	or %r27, %r16, %r27
	or %r27, %r27, %r2
	xor %r27, %r27, %r2
	or %r21, %r21, %r20
	or %r20, %r25, %r21
	xor %r20, %r20, %r21
	and %r12, %r15, %r12
	or %r2, %r12, %r17
	xor %r2, %r2, %r17
	xor %r20, %r20, %r2
	and %r19, %r19, %r20
	or %r12, %r23, %r12
	or %r12, %r12, %r19
	xor %r12, %r12, %r19
	xor %r18, %r18, %r12
	and %r27, %r27, %r14
	xor %r27, %r27, %r18
	xor %r22, %r22, %r11
	or %r17, %r17, %r22
	or %r16, %r16, %r17
	xor %r23, %r23, %r16
	xor %r21, %r21, %r23
	xor %r24, %r24, %r11
	and %r24, %r24, %r14
	xor %r24, %r24, %r21
	and %r15, %r15, %r22
	xor %r25, %r25, %r15
	or %r23, %r23, %r25
	xor %r6, %r6, %r18
	xor %r23, %r23, %r6
	or %r20, %r20, %r14
	xor %r20, %r20, %r23
	ld %r0, 176(%r10)
	xor %r0, %r0, %r26
	std %r0, 176(%r10)
	ld %r0, 128(%r10)
	xor %r0, %r0, %r20
	std %r0, 128(%r10)
	ld %r0, 32(%r10)
	xor %r0, %r0, %r27
	std %r0, 32(%r10)
	ld %r0, 16(%r10)
	xor %r0, %r0, %r24
	std %r0, 16(%r10)
	rldicr %r12, %r9, 39, 24
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 472(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 38, 25
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 40(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 37, 26
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 104(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 36, 27
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 168(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 35, 28
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 232(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 34, 29
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 296(%r10)
	xor %r18, %r18, %r0
	xor %r18, %r18, %r16
	xor %r16, %r16, %r14
	or %r6, %r17, %r15
	xor %r6, %r14, %r6
	xor %r6, %r6, %r11
	and %r6, %r6, %r16
	or %r2, %r16, %r17
	xor %r2, %r2, %r17
	xor %r19, %r15, %r2
	or %r20, %r18, %r19
	or %r20, %r20, %r6
	xor %r20, %r20, %r6
	xor %r21, %r17, %r20
	and %r19, %r19, %r21
	or %r16, %r16, %r19
	xor %r16, %r16, %r19
	xor %r18, %r18, %r21
	xor %r16, %r16, %r11
	and %r16, %r16, %r18
	xor %r6, %r6, %r16
	xor %r17, %r17, %r15
	or %r14, %r14, %r2
	xor %r18, %r18, %r14
	or %r14, %r18, %r17
	xor %r14, %r14, %r17
	xor %r20, %r20, %r14
	or %r14, %r12, %r6
	xor %r14, %r14, %r6
	xor %r14, %r14, %r20
	xor %r20, %r20, %r11
	or %r2, %r6, %r12
	xor %r2, %r2, %r12
	xor %r2, %r2, %r20
	xor %r6, %r6, %r20
	or %r6, %r6, %r17
	xor %r6, %r6, %r17
	or %r19, %r19, %r6
	xor %r18, %r18, %r19
	or %r19, %r21, %r12
	xor %r19, %r19, %r18
	and %r12, %r12, %r21
	xor %r12, %r12, %r18
	ld %r0, 496(%r10)
	xor %r0, %r0, %r12
	std %r0, 496(%r10)
	ld %r0, 416(%r10)
	xor %r0, %r0, %r19
	std %r0, 416(%r10)
	ld %r0, 272(%r10)
	xor %r0, %r0, %r2
	std %r0, 272(%r10)
	ld %r0, 384(%r10)
	xor %r0, %r0, %r14
	std %r0, 384(%r10)
	rldicr %r12, %r9, 45, 18
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 216(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 44, 19
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 280(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 43, 20
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 344(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 42, 21
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 408(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 41, 22
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 472(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 40, 23
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 40(%r10)
	xor %r18, %r18, %r0
	or %r6, %r18, %r16
	or %r2, %r6, %r12
	xor %r2, %r2, %r12
	xor %r19, %r18, %r2
	xor %r20, %r16, %r19
	or %r21, %r15, %r20
	or %r2, %r2, %r15
	xor %r2, %r2, %r15
	xor %r16, %r16, %r2
	and %r2, %r14, %r16
	or %r20, %r18, %r20
	xor %r2, %r2, %r20
	xor %r2, %r15, %r2
	xor %r12, %r12, %r2
	or %r22, %r19, %r12
	and %r23, %r14, %r22
	xor %r24, %r19, %r23
	and %r25, %r15, %r20
	xor %r24, %r24, %r25
	or %r22, %r22, %r18
	xor %r22, %r22, %r18
	xor %r25, %r16, %r22
	xor %r14, %r14, %r21
	xor %r25, %r25, %r11
	and %r25, %r25, %r14
	xor %r25, %r25, %r11
	or %r25, %r25, %r17
	xor %r25, %r25, %r17
	xor %r25, %r25, %r2
	or %r2, %r16, %r23
	xor %r2, %r2, %r23
	xor %r22, %r22, %r14
	or %r22, %r24, %r22
	or %r22, %r22, %r2
	xor %r22, %r22, %r2
	or %r2, %r21, %r22
	xor %r2, %r2, %r22
	and %r12, %r12, %r22
	xor %r14, %r14, %r12
	and %r20, %r16, %r20
	or %r20, %r14, %r20
	xor %r23, %r23, %r20
	and %r23, %r23, %r17
	xor %r23, %r23, %r24
	xor %r18, %r18, %r6
	xor %r22, %r22, %r18
	and %r15, %r15, %r14
	xor %r22, %r22, %r15
	or %r2, %r2, %r17
	xor %r2, %r2, %r22
	xor %r16, %r21, %r16
	or %r16, %r16, %r22
	xor %r16, %r16, %r22
	xor %r19, %r19, %r14
	xor %r16, %r16, %r19
	and %r21, %r21, %r17
	xor %r21, %r21, %r16
	ld %r0, 368(%r10)
	xor %r0, %r0, %r23
	std %r0, 368(%r10)
	ld %r0, 448(%r10)
	xor %r0, %r0, %r25
	std %r0, 448(%r10)
	ld %r0, 160(%r10)
	xor %r0, %r0, %r21
	std %r0, 160(%r10)
	ld %r0, 48(%r10)
	xor %r0, %r0, %r2
	std %r0, 48(%r10)
	rldicr %r12, %r9, 51, 12
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 456(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 50, 13
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 24(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 49, 14
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 88(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 48, 15
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 152(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 47, 16
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 216(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 46, 17
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 280(%r10)
	xor %r18, %r18, %r0
	xor %r6, %r17, %r14
	or %r2, %r17, %r12
	and %r2, %r18, %r2
	xor %r6, %r6, %r2
	xor %r19, %r12, %r6
	or %r20, %r14, %r19
	xor %r20, %r20, %r19
	and %r19, %r18, %r19
	xor %r21, %r17, %r19
	xor %r22, %r18, %r16
	or %r23, %r21, %r22
	xor %r24, %r6, %r23
	and %r25, %r16, %r24
	or %r26, %r25, %r12
	xor %r26, %r26, %r12
	or %r21, %r20, %r21
	xor %r27, %r26, %r21
	and %r28, %r27, %r15
	xor %r28, %r28, %r24
	xor %r23, %r17, %r23
	or %r29, %r12, %r23
	xor %r29, %r29, %r23
	xor %r16, %r16, %r29
	or %r29, %r14, %r25
	xor %r29, %r29, %r25
	or %r29, %r16, %r29
	or %r17, %r17, %r22
	xor %r27, %r27, %r17
	or %r2, %r2, %r29
	xor %r27, %r27, %r2
	or %r24, %r18, %r24
	and %r21, %r21, %r24
	xor %r21, %r16, %r21
	xor %r26, %r26, %r11
	and %r26, %r26, %r21
	or %r20, %r20, %r15
	xor %r20, %r20, %r26
	xor %r6, %r6, %r21
	or %r14, %r14, %r6
	xor %r14, %r14, %r6
	xor %r17, %r17, %r11
	xor %r23, %r23, %r17
	xor %r14, %r14, %r23
	or %r14, %r14, %r15
	xor %r14, %r14, %r15
	xor %r14, %r14, %r27
	xor %r12, %r12, %r19
	xor %r18, %r18, %r16
	and %r12, %r12, %r18
	xor %r25, %r25, %r23
	xor %r12, %r12, %r25
	or %r29, %r29, %r15
	xor %r29, %r29, %r15
	xor %r29, %r29, %r12
	ld %r0, 336(%r10)
	xor %r0, %r0, %r28
	std %r0, 336(%r10)
	ld %r0, 352(%r10)
	xor %r0, %r0, %r20
	std %r0, 352(%r10)
	ld %r0, 192(%r10)
	xor %r0, %r0, %r14
	std %r0, 192(%r10)
	ld %r0, 304(%r10)
	xor %r0, %r0, %r29
	std %r0, 304(%r10)
	rldicr %r12, %r9, 57, 6
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 200(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 56, 7
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 264(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 55, 8
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 328(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 54, 9
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 392(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 53, 10
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 456(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 52, 11
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 24(%r10)
	xor %r18, %r18, %r0
	xor %r6, %r15, %r14
	xor %r2, %r16, %r6
	and %r19, %r12, %r2
	and %r20, %r15, %r6
	xor %r21, %r17, %r20
	and %r22, %r19, %r21
	and %r23, %r12, %r20
	xor %r24, %r16, %r23
	or %r25, %r21, %r24
	xor %r6, %r12, %r6
	xor %r26, %r25, %r6
	or %r27, %r18, %r22
	xor %r27, %r27, %r22
	xor %r27, %r27, %r26
	xor %r2, %r2, %r11
	and %r2, %r2, %r14
	or %r26, %r21, %r2
	xor %r24, %r19, %r24
	xor %r26, %r26, %r24
	xor %r19, %r19, %r6
	or %r15, %r15, %r19
	xor %r15, %r15, %r19
	or %r6, %r21, %r15
	xor %r6, %r6, %r15
	xor %r14, %r14, %r24
	xor %r6, %r6, %r14
	or %r19, %r19, %r23
	xor %r19, %r19, %r23
	or %r15, %r15, %r19
	xor %r25, %r17, %r25
	and %r25, %r6, %r25
	xor %r25, %r15, %r25
	and %r23, %r25, %r18
	xor %r23, %r23, %r6
	or %r21, %r21, %r16
	xor %r21, %r21, %r16
	or %r19, %r19, %r21
	or %r20, %r20, %r6
	and %r19, %r19, %r20
	xor %r25, %r25, %r19
	xor %r2, %r2, %r15
	and %r12, %r12, %r2
	or %r22, %r22, %r12
	xor %r19, %r19, %r22
	or %r12, %r19, %r18
	xor %r12, %r12, %r18
	xor %r12, %r12, %r26
	and %r17, %r17, %r22
	xor %r26, %r26, %r11
	xor %r17, %r17, %r26
	xor %r19, %r19, %r17
	or %r25, %r25, %r18
	xor %r25, %r25, %r19
	ld %r0, 112(%r10)
	xor %r0, %r0, %r27
	std %r0, 112(%r10)
	ld %r0, 144(%r10)
	xor %r0, %r0, %r23
	std %r0, 144(%r10)
	ld %r0, 288(%r10)
	xor %r0, %r0, %r25
	std %r0, 288(%r10)
	ld %r0, 0(%r10)
	xor %r0, %r0, %r12
	std %r0, 0(%r10)
	rldicr %r12, %r9, 63, 0
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 504(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 62, 1
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 8(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 61, 2
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 72(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 60, 3
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 136(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 59, 4
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 200(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 58, 5
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 264(%r10)
	xor %r18, %r18, %r0
	or %r6, %r16, %r17
	xor %r6, %r6, %r17
	or %r2, %r14, %r16
	xor %r2, %r2, %r16
	xor %r2, %r15, %r2
	and %r19, %r18, %r2
	or %r20, %r19, %r6
	xor %r20, %r20, %r6
	or %r21, %r17, %r2
	xor %r21, %r21, %r2
	or %r22, %r18, %r21
	or %r23, %r17, %r16
	xor %r23, %r23, %r16
	xor %r23, %r14, %r23
	and %r24, %r22, %r23
	or %r19, %r19, %r24
	xor %r2, %r2, %r11
	xor %r24, %r24, %r2
	or %r16, %r16, %r22
	xor %r16, %r16, %r22
	xor %r24, %r24, %r16
	xor %r6, %r6, %r24
	or %r16, %r20, %r12
	xor %r16, %r16, %r6
	xor %r6, %r18, %r6
	and %r22, %r14, %r6
	xor %r24, %r17, %r24
	xor %r22, %r22, %r24
	xor %r21, %r21, %r22
	xor %r22, %r19, %r22
	or %r17, %r17, %r22
	xor %r14, %r14, %r6
	xor %r17, %r17, %r14
	and %r19, %r19, %r12
	xor %r19, %r19, %r17
	xor %r23, %r23, %r21
	or %r24, %r15, %r24
	xor %r24, %r23, %r24
	xor %r18, %r18, %r24
	and %r18, %r18, %r12
	xor %r18, %r18, %r21
	or %r23, %r23, %r15
	xor %r23, %r23, %r15
	and %r17, %r17, %r23
	xor %r20, %r20, %r24
	xor %r17, %r17, %r20
	or %r17, %r17, %r12
	xor %r17, %r17, %r21
	ld %r0, 208(%r10)
	xor %r0, %r0, %r18
	std %r0, 208(%r10)
	ld %r0, 96(%r10)
	xor %r0, %r0, %r19
	std %r0, 96(%r10)
	ld %r0, 320(%r10)
	xor %r0, %r0, %r16
	std %r0, 320(%r10)
	ld %r0, 240(%r10)
	xor %r0, %r0, %r17
	std %r0, 240(%r10)
	ld %r9, 0(%r3)
	xor %r9, %r9, %r11
	addi %r3, %r3, -8
	rldicr %r12, %r9, 21, 42
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 240(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 20, 43
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 304(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 19, 44
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 368(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 18, 45
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 432(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 17, 46
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 496(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 16, 47
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 0(%r10)
	xor %r18, %r18, %r0
	or %r6, %r18, %r14
	xor %r6, %r6, %r14
	xor %r2, %r15, %r6
	or %r19, %r16, %r12
	xor %r20, %r18, %r16
	and %r21, %r19, %r20
	xor %r22, %r15, %r21
	or %r23, %r22, %r2
	xor %r23, %r23, %r2
	xor %r24, %r14, %r12
	xor %r25, %r16, %r24
	xor %r25, %r25, %r11
	and %r25, %r25, %r2
	or %r21, %r12, %r21
	xor %r25, %r25, %r21
	or %r21, %r25, %r23
	xor %r21, %r21, %r23
	or %r12, %r18, %r12
	or %r26, %r25, %r12
	xor %r22, %r22, %r11
	and %r22, %r22, %r14
	xor %r27, %r26, %r22
	or %r15, %r15, %r12
	xor %r15, %r15, %r12
	xor %r15, %r22, %r15
	xor %r20, %r20, %r11
	and %r20, %r20, %r24
	or %r15, %r15, %r20
	or %r16, %r16, %r6
	xor %r16, %r16, %r6
	xor %r6, %r2, %r26
	or %r6, %r6, %r16
	xor %r6, %r6, %r16
	xor %r16, %r6, %r11
	and %r25, %r19, %r25
	xor %r16, %r16, %r25
	or %r27, %r27, %r17
	xor %r27, %r27, %r17
	xor %r27, %r27, %r16
	xor %r6, %r24, %r6
	or %r22, %r22, %r6
	xor %r22, %r19, %r22
	xor %r18, %r18, %r22
	xor %r16, %r16, %r18
	or %r23, %r23, %r17
	xor %r23, %r23, %r16
	xor %r19, %r19, %r26
	or %r19, %r15, %r19
	xor %r19, %r18, %r19
	or %r24, %r24, %r16
	xor %r24, %r19, %r24
	or %r16, %r21, %r17
	xor %r16, %r16, %r24
	or %r14, %r14, %r2
	or %r14, %r14, %r19
	xor %r14, %r14, %r19
	and %r21, %r21, %r18
	xor %r14, %r14, %r21
	or %r14, %r14, %r17
	xor %r14, %r14, %r15
	ld %r0, 72(%r10)
	xor %r0, %r0, %r14
	std %r0, 72(%r10)
	ld %r0, 88(%r10)
	xor %r0, %r0, %r27
	std %r0, 88(%r10)
	ld %r0, 472(%r10)
	xor %r0, %r0, %r16
	std %r0, 472(%r10)
	ld %r0, 488(%r10)
	xor %r0, %r0, %r23
	std %r0, 488(%r10)
	rldicr %r12, %r9, 27, 36
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 480(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 26, 37
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 48(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 25, 38
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 112(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 24, 39
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 176(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 23, 40
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 240(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 22, 41
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 304(%r10)
	xor %r18, %r18, %r0
	xor %r6, %r17, %r14
	or %r2, %r18, %r12
	xor %r2, %r2, %r12
	xor %r2, %r2, %r11
	and %r2, %r2, %r14
	or %r19, %r17, %r2
	or %r20, %r6, %r12
	xor %r20, %r20, %r12
	and %r21, %r18, %r6
	xor %r14, %r14, %r21
	or %r21, %r14, %r20
	xor %r21, %r21, %r20
	and %r22, %r16, %r12
	xor %r2, %r2, %r20
	and %r2, %r19, %r2
	or %r20, %r2, %r22
	xor %r20, %r20, %r22
	and %r23, %r16, %r2
	xor %r18, %r18, %r11
	xor %r18, %r23, %r18
	xor %r12, %r12, %r6
	or %r24, %r12, %r22
	xor %r24, %r24, %r22
	xor %r25, %r18, %r24
	xor %r20, %r20, %r11
	and %r20, %r20, %r15
	xor %r20, %r20, %r25
	or %r17, %r17, %r24
	xor %r17, %r17, %r24
	xor %r14, %r14, %r17
	or %r18, %r18, %r14
	xor %r18, %r18, %r14
	xor %r16, %r16, %r12
	xor %r18, %r18, %r16
	or %r24, %r19, %r15
	xor %r24, %r24, %r15
	xor %r24, %r24, %r18
	xor %r23, %r23, %r17
	or %r16, %r16, %r23
	xor %r19, %r19, %r25
	or %r22, %r22, %r19
	xor %r23, %r16, %r22
	xor %r2, %r2, %r25
	xor %r18, %r18, %r2
	and %r22, %r22, %r18
	and %r6, %r6, %r16
	xor %r22, %r22, %r6
	or %r6, %r22, %r15
	xor %r6, %r6, %r23
	or %r22, %r22, %r14
	xor %r22, %r22, %r14
	or %r12, %r12, %r19
	xor %r22, %r22, %r12
	or %r21, %r21, %r15
	xor %r21, %r21, %r22
	ld %r0, 408(%r10)
	xor %r0, %r0, %r21
	std %r0, 408(%r10)
	ld %r0, 440(%r10)
	xor %r0, %r0, %r6
	std %r0, 440(%r10)
	ld %r0, 264(%r10)
	xor %r0, %r0, %r20
	std %r0, 264(%r10)
	ld %r0, 232(%r10)
	xor %r0, %r0, %r24
	std %r0, 232(%r10)
	rldicr %r12, %r9, 33, 30
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 224(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 32, 31
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 288(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 31, 32
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 352(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 30, 33
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 416(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 29, 34
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 480(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 28, 35
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 48(%r10)
	xor %r18, %r18, %r0
	or %r6, %r18, %r17
	xor %r6, %r6, %r17
	xor %r2, %r16, %r12
	or %r19, %r6, %r2
	xor %r20, %r15, %r12
	or %r21, %r20, %r18
	xor %r21, %r21, %r18
	xor %r22, %r19, %r21
	xor %r23, %r17, %r2
	or %r24, %r23, %r12
	xor %r24, %r24, %r12
	xor %r19, %r19, %r24
	or %r24, %r22, %r19
	xor %r24, %r24, %r19
	and %r25, %r12, %r22
	or %r25, %r15, %r25
	and %r25, %r18, %r25
	xor %r25, %r23, %r25
	or %r26, %r22, %r14
	xor %r26, %r26, %r14
	xor %r26, %r26, %r25
	and %r2, %r2, %r20
	xor %r20, %r18, %r15
	xor %r27, %r19, %r20
	or %r27, %r16, %r27
	or %r27, %r27, %r2
	xor %r27, %r27, %r2
	or %r21, %r21, %r20
	or %r20, %r25, %r21
	xor %r20, %r20, %r21
	and %r12, %r15, %r12
	or %r2, %r12, %r17
	xor %r2, %r2, %r17
	xor %r20, %r20, %r2
	and %r19, %r19, %r20
	or %r12, %r23, %r12
	or %r12, %r12, %r19
	xor %r12, %r12, %r19
	xor %r18, %r18, %r12
	and %r27, %r27, %r14
	xor %r27, %r27, %r18
	xor %r22, %r22, %r11
	or %r17, %r17, %r22
	or %r16, %r16, %r17
	xor %r23, %r23, %r16
	xor %r21, %r21, %r23
	xor %r24, %r24, %r11
	and %r24, %r24, %r14
	xor %r24, %r24, %r21
	and %r15, %r15, %r22
	xor %r25, %r25, %r15
	or %r23, %r23, %r25
	xor %r6, %r6, %r18
	xor %r23, %r23, %r6
	or %r20, %r20, %r14
	xor %r20, %r20, %r23
	ld %r0, 184(%r10)
	xor %r0, %r0, %r26
	std %r0, 184(%r10)
	ld %r0, 136(%r10)
	xor %r0, %r0, %r20
	std %r0, 136(%r10)
	ld %r0, 40(%r10)
	xor %r0, %r0, %r27
	std %r0, 40(%r10)
	ld %r0, 24(%r10)
	xor %r0, %r0, %r24
	std %r0, 24(%r10)
	rldicr %r12, %r9, 39, 24
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 464(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 38, 25
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 32(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 37, 26
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 96(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 36, 27
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 160(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 35, 28
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 224(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 34, 29
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 288(%r10)
	xor %r18, %r18, %r0
	xor %r18, %r18, %r16
	xor %r16, %r16, %r14
	or %r6, %r17, %r15
	xor %r6, %r14, %r6
	xor %r6, %r6, %r11
	and %r6, %r6, %r16
	or %r2, %r16, %r17
	xor %r2, %r2, %r17
	xor %r19, %r15, %r2
	or %r20, %r18, %r19
	or %r20, %r20, %r6
	xor %r20, %r20, %r6
	xor %r21, %r17, %r20
	and %r19, %r19, %r21
	or %r16, %r16, %r19
	xor %r16, %r16, %r19
	xor %r18, %r18, %r21
	xor %r16, %r16, %r11
	and %r16, %r16, %r18
	xor %r6, %r6, %r16
	xor %r17, %r17, %r15
	or %r14, %r14, %r2
	xor %r18, %r18, %r14
	or %r14, %r18, %r17
	xor %r14, %r14, %r17
	xor %r20, %r20, %r14
	or %r14, %r12, %r6
	xor %r14, %r14, %r6
	xor %r14, %r14, %r20
	xor %r20, %r20, %r11
	or %r2, %r6, %r12
	xor %r2, %r2, %r12
	xor %r2, %r2, %r20
	xor %r6, %r6, %r20
	or %r6, %r6, %r17
	xor %r6, %r6, %r17
	or %r19, %r19, %r6
	xor %r18, %r18, %r19
	or %r19, %r21, %r12
	xor %r19, %r19, %r18
	and %r12, %r12, %r21
	xor %r12, %r12, %r18
	ld %r0, 504(%r10)
	xor %r0, %r0, %r12
	std %r0, 504(%r10)
	ld %r0, 424(%r10)
	xor %r0, %r0, %r19
	std %r0, 424(%r10)
	ld %r0, 280(%r10)
	xor %r0, %r0, %r2
	std %r0, 280(%r10)
	ld %r0, 392(%r10)
	xor %r0, %r0, %r14
	std %r0, 392(%r10)
	rldicr %r12, %r9, 45, 18
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 208(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 44, 19
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 272(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 43, 20
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 336(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 42, 21
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 400(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 41, 22
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 464(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 40, 23
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 32(%r10)
	xor %r18, %r18, %r0
	or %r6, %r18, %r16
	or %r2, %r6, %r12
	xor %r2, %r2, %r12
	xor %r19, %r18, %r2
	xor %r20, %r16, %r19
	or %r21, %r15, %r20
	or %r2, %r2, %r15
	xor %r2, %r2, %r15
	xor %r16, %r16, %r2
	and %r2, %r14, %r16
	or %r20, %r18, %r20
	xor %r2, %r2, %r20
	xor %r2, %r15, %r2
	xor %r12, %r12, %r2
	or %r22, %r19, %r12
	and %r23, %r14, %r22
	xor %r24, %r19, %r23
	and %r25, %r15, %r20
	xor %r24, %r24, %r25
	or %r22, %r22, %r18
	xor %r22, %r22, %r18
	xor %r25, %r16, %r22
	xor %r14, %r14, %r21
	xor %r25, %r25, %r11
	and %r25, %r25, %r14
	xor %r25, %r25, %r11
	or %r25, %r25, %r17
	xor %r25, %r25, %r17
	xor %r25, %r25, %r2
	or %r2, %r16, %r23
	xor %r2, %r2, %r23
	xor %r22, %r22, %r14
	or %r22, %r24, %r22
	or %r22, %r22, %r2
	xor %r22, %r22, %r2
	or %r2, %r21, %r22
	xor %r2, %r2, %r22
	and %r12, %r12, %r22
	xor %r14, %r14, %r12
	and %r20, %r16, %r20
	or %r20, %r14, %r20
	xor %r23, %r23, %r20
	and %r23, %r23, %r17
	xor %r23, %r23, %r24
	xor %r18, %r18, %r6
	xor %r22, %r22, %r18
	and %r15, %r15, %r14
	xor %r22, %r22, %r15
	or %r2, %r2, %r17
	xor %r2, %r2, %r22
	xor %r16, %r21, %r16
	or %r16, %r16, %r22
	xor %r16, %r16, %r22
	xor %r19, %r19, %r14
	xor %r16, %r16, %r19
	and %r21, %r21, %r17
	xor %r21, %r21, %r16
	ld %r0, 376(%r10)
	xor %r0, %r0, %r23
	std %r0, 376(%r10)
	ld %r0, 456(%r10)
	xor %r0, %r0, %r25
	std %r0, 456(%r10)
	ld %r0, 168(%r10)
	xor %r0, %r0, %r21
	std %r0, 168(%r10)
	ld %r0, 56(%r10)
	xor %r0, %r0, %r2
	std %r0, 56(%r10)
	rldicr %r12, %r9, 51, 12
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 448(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 50, 13
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 16(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 49, 14
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 80(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 48, 15
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 144(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 47, 16
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 208(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 46, 17
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 272(%r10)
	xor %r18, %r18, %r0
	xor %r6, %r17, %r14
	or %r2, %r17, %r12
	and %r2, %r18, %r2
	xor %r6, %r6, %r2
	xor %r19, %r12, %r6
	or %r20, %r14, %r19
	xor %r20, %r20, %r19
	and %r19, %r18, %r19
	xor %r21, %r17, %r19
	xor %r22, %r18, %r16
	or %r23, %r21, %r22
	xor %r24, %r6, %r23
	and %r25, %r16, %r24
	or %r26, %r25, %r12
	xor %r26, %r26, %r12
	or %r21, %r20, %r21
	xor %r27, %r26, %r21
	and %r28, %r27, %r15
	xor %r28, %r28, %r24
	xor %r23, %r17, %r23
	or %r29, %r12, %r23
	xor %r29, %r29, %r23
	xor %r16, %r16, %r29
	or %r29, %r14, %r25
	xor %r29, %r29, %r25
	or %r29, %r16, %r29
	or %r17, %r17, %r22
	xor %r27, %r27, %r17
	or %r2, %r2, %r29
	xor %r27, %r27, %r2
	or %r24, %r18, %r24
	and %r21, %r21, %r24
	xor %r21, %r16, %r21
	xor %r26, %r26, %r11
	and %r26, %r26, %r21
	or %r20, %r20, %r15
	xor %r20, %r20, %r26
	xor %r6, %r6, %r21
	or %r14, %r14, %r6
	xor %r14, %r14, %r6
	xor %r17, %r17, %r11
	xor %r23, %r23, %r17
	xor %r14, %r14, %r23
	or %r14, %r14, %r15
	xor %r14, %r14, %r15
	xor %r14, %r14, %r27
	xor %r12, %r12, %r19
	xor %r18, %r18, %r16
	and %r12, %r12, %r18
	xor %r25, %r25, %r23
	xor %r12, %r12, %r25
	or %r29, %r29, %r15
	xor %r29, %r29, %r15
	xor %r29, %r29, %r12
	ld %r0, 344(%r10)
	xor %r0, %r0, %r28
	std %r0, 344(%r10)
	ld %r0, 360(%r10)
	xor %r0, %r0, %r20
	std %r0, 360(%r10)
	ld %r0, 200(%r10)
	xor %r0, %r0, %r14
	std %r0, 200(%r10)
	ld %r0, 312(%r10)
	xor %r0, %r0, %r29
	std %r0, 312(%r10)
	rldicr %r12, %r9, 57, 6
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 192(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 56, 7
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 256(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 55, 8
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 320(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 54, 9
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 384(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 53, 10
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 448(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 52, 11
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 16(%r10)
	xor %r18, %r18, %r0
	xor %r6, %r15, %r14
	xor %r2, %r16, %r6
	and %r19, %r12, %r2
	and %r20, %r15, %r6
	xor %r21, %r17, %r20
	and %r22, %r19, %r21
	and %r23, %r12, %r20
	xor %r24, %r16, %r23
	or %r25, %r21, %r24
	xor %r6, %r12, %r6
	xor %r26, %r25, %r6
	or %r27, %r18, %r22
	xor %r27, %r27, %r22
	xor %r27, %r27, %r26
	xor %r2, %r2, %r11
	and %r2, %r2, %r14
	or %r26, %r21, %r2
	xor %r24, %r19, %r24
	xor %r26, %r26, %r24
	xor %r19, %r19, %r6
	or %r15, %r15, %r19
	xor %r15, %r15, %r19
	or %r6, %r21, %r15
	xor %r6, %r6, %r15
	xor %r14, %r14, %r24
	xor %r6, %r6, %r14
	or %r19, %r19, %r23
	xor %r19, %r19, %r23
	or %r15, %r15, %r19
	xor %r25, %r17, %r25
	and %r25, %r6, %r25
	xor %r25, %r15, %r25
	and %r23, %r25, %r18
	xor %r23, %r23, %r6
	or %r21, %r21, %r16
	xor %r21, %r21, %r16
	or %r19, %r19, %r21
	or %r20, %r20, %r6
	and %r19, %r19, %r20
	xor %r25, %r25, %r19
	xor %r2, %r2, %r15
	and %r12, %r12, %r2
	or %r22, %r22, %r12
	xor %r19, %r19, %r22
	or %r12, %r19, %r18
	xor %r12, %r12, %r18
	xor %r12, %r12, %r26
	and %r17, %r17, %r22
	xor %r26, %r26, %r11
	xor %r17, %r17, %r26
	xor %r19, %r19, %r17
	or %r25, %r25, %r18
	xor %r25, %r25, %r19
	ld %r0, 120(%r10)
	xor %r0, %r0, %r27
	std %r0, 120(%r10)
	ld %r0, 152(%r10)
	xor %r0, %r0, %r23
	std %r0, 152(%r10)
	ld %r0, 296(%r10)
	xor %r0, %r0, %r25
	std %r0, 296(%r10)
	ld %r0, 8(%r10)
	xor %r0, %r0, %r12
	std %r0, 8(%r10)
	rldicr %r12, %r9, 63, 0
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 496(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 62, 1
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 0(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 61, 2
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 64(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 60, 3
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 128(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 59, 4
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 192(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 58, 5
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 256(%r10)
	xor %r18, %r18, %r0
	or %r6, %r16, %r17
	xor %r6, %r6, %r17
	or %r2, %r14, %r16
	xor %r2, %r2, %r16
	xor %r2, %r15, %r2
	and %r19, %r18, %r2
	or %r20, %r19, %r6
	xor %r20, %r20, %r6
	or %r21, %r17, %r2
	xor %r21, %r21, %r2
	or %r22, %r18, %r21
	or %r23, %r17, %r16
	xor %r23, %r23, %r16
	xor %r23, %r14, %r23
	and %r24, %r22, %r23
	or %r19, %r19, %r24
	xor %r2, %r2, %r11
	xor %r24, %r24, %r2
	or %r16, %r16, %r22
	xor %r16, %r16, %r22
	xor %r24, %r24, %r16
	xor %r6, %r6, %r24
	or %r16, %r20, %r12
	xor %r16, %r16, %r6
	xor %r6, %r18, %r6
	and %r22, %r14, %r6
	xor %r24, %r17, %r24
	xor %r22, %r22, %r24
	xor %r21, %r21, %r22
	xor %r22, %r19, %r22
	or %r17, %r17, %r22
	xor %r14, %r14, %r6
	xor %r17, %r17, %r14
	and %r19, %r19, %r12
	xor %r19, %r19, %r17
	xor %r23, %r23, %r21
	or %r24, %r15, %r24
	xor %r24, %r23, %r24
	xor %r18, %r18, %r24
	and %r18, %r18, %r12
	xor %r18, %r18, %r21
	or %r23, %r23, %r15
	xor %r23, %r23, %r15
	and %r17, %r17, %r23
	xor %r20, %r20, %r24
	xor %r17, %r17, %r20
	or %r17, %r17, %r12
	xor %r17, %r17, %r21
	ld %r0, 216(%r10)
	xor %r0, %r0, %r18
	std %r0, 216(%r10)
	ld %r0, 104(%r10)
	xor %r0, %r0, %r19
	std %r0, 104(%r10)
	ld %r0, 328(%r10)
	xor %r0, %r0, %r16
	std %r0, 328(%r10)
	ld %r0, 248(%r10)
	xor %r0, %r0, %r17
	std %r0, 248(%r10)
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 27b
	ld %r12, 0(%r10)
	ld %r14, 8(%r10)
	std %r14, 0(%r10)
	std %r12, 8(%r10)
	ld %r12, 64(%r10)
	ld %r14, 72(%r10)
	std %r14, 64(%r10)
	std %r12, 72(%r10)
	ld %r12, 128(%r10)
	ld %r14, 136(%r10)
	std %r14, 128(%r10)
	std %r12, 136(%r10)
	ld %r12, 192(%r10)
	ld %r14, 200(%r10)
	std %r14, 192(%r10)
	std %r12, 200(%r10)
	ld %r12, 256(%r10)
	ld %r14, 264(%r10)
	std %r14, 256(%r10)
	std %r12, 264(%r10)
	ld %r12, 320(%r10)
	ld %r14, 328(%r10)
	std %r14, 320(%r10)
	std %r12, 328(%r10)
	ld %r12, 384(%r10)
	ld %r14, 392(%r10)
	std %r14, 384(%r10)
	std %r12, 392(%r10)
	ld %r12, 448(%r10)
	ld %r14, 456(%r10)
	std %r14, 448(%r10)
	std %r12, 456(%r10)
	ld %r12, 16(%r10)
	ld %r14, 24(%r10)
	std %r14, 16(%r10)
	std %r12, 24(%r10)
	ld %r12, 80(%r10)
	ld %r14, 88(%r10)
	std %r14, 80(%r10)
	std %r12, 88(%r10)
	ld %r12, 144(%r10)
	ld %r14, 152(%r10)
	std %r14, 144(%r10)
	std %r12, 152(%r10)
	ld %r12, 208(%r10)
	ld %r14, 216(%r10)
	std %r14, 208(%r10)
	std %r12, 216(%r10)
	ld %r12, 272(%r10)
	ld %r14, 280(%r10)
	std %r14, 272(%r10)
	std %r12, 280(%r10)
	ld %r12, 336(%r10)
	ld %r14, 344(%r10)
	std %r14, 336(%r10)
	std %r12, 344(%r10)
	ld %r12, 400(%r10)
	ld %r14, 408(%r10)
	std %r14, 400(%r10)
	std %r12, 408(%r10)
	ld %r12, 464(%r10)
	ld %r14, 472(%r10)
	std %r14, 464(%r10)
	std %r12, 472(%r10)
	ld %r12, 32(%r10)
	ld %r14, 40(%r10)
	std %r14, 32(%r10)
	std %r12, 40(%r10)
	ld %r12, 96(%r10)
	ld %r14, 104(%r10)
	std %r14, 96(%r10)
	std %r12, 104(%r10)
	ld %r12, 160(%r10)
	ld %r14, 168(%r10)
	std %r14, 160(%r10)
	std %r12, 168(%r10)
	ld %r12, 224(%r10)
	ld %r14, 232(%r10)
	std %r14, 224(%r10)
	std %r12, 232(%r10)
	ld %r12, 288(%r10)
	ld %r14, 296(%r10)
	std %r14, 288(%r10)
	std %r12, 296(%r10)
	ld %r12, 352(%r10)
	ld %r14, 360(%r10)
	std %r14, 352(%r10)
	std %r12, 360(%r10)
	ld %r12, 416(%r10)
	ld %r14, 424(%r10)
	std %r14, 416(%r10)
	std %r12, 424(%r10)
	ld %r12, 480(%r10)
	ld %r14, 488(%r10)
	std %r14, 480(%r10)
	std %r12, 488(%r10)
	ld %r12, 48(%r10)
	ld %r14, 56(%r10)
	std %r14, 48(%r10)
	std %r12, 56(%r10)
	ld %r12, 112(%r10)
	ld %r14, 120(%r10)
	std %r14, 112(%r10)
	std %r12, 120(%r10)
	ld %r12, 176(%r10)
	ld %r14, 184(%r10)
	std %r14, 176(%r10)
	std %r12, 184(%r10)
	ld %r12, 240(%r10)
	ld %r14, 248(%r10)
	std %r14, 240(%r10)
	std %r12, 248(%r10)
	ld %r12, 304(%r10)
	ld %r14, 312(%r10)
	std %r14, 304(%r10)
	std %r12, 312(%r10)
	ld %r12, 368(%r10)
	ld %r14, 376(%r10)
	std %r14, 368(%r10)
	std %r12, 376(%r10)
	ld %r12, 432(%r10)
	ld %r14, 440(%r10)
	std %r14, 432(%r10)
	std %r12, 440(%r10)
	ld %r12, 496(%r10)
	ld %r14, 504(%r10)
	std %r14, 496(%r10)
	std %r12, 504(%r10)
	addi %r3, %r7, 256
	li %r5, 8
28:
	ld %r9, 0(%r3)
	xor %r9, %r9, %r11
	addi %r3, %r3, 8
	rldicr %r12, %r9, 21, 42
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 248(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 20, 43
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 312(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 19, 44
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 376(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 18, 45
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 440(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 17, 46
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 504(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 16, 47
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 8(%r10)
	xor %r18, %r18, %r0
	or %r6, %r18, %r14
	xor %r6, %r6, %r14
	xor %r2, %r15, %r6
	or %r19, %r16, %r12
	xor %r20, %r18, %r16
	and %r21, %r19, %r20
	xor %r22, %r15, %r21
	or %r23, %r22, %r2
	xor %r23, %r23, %r2
	xor %r24, %r14, %r12
	xor %r25, %r16, %r24
	xor %r25, %r25, %r11
	and %r25, %r25, %r2
	or %r21, %r12, %r21
	xor %r25, %r25, %r21
	or %r21, %r25, %r23
	xor %r21, %r21, %r23
	or %r12, %r18, %r12
	or %r26, %r25, %r12
	xor %r22, %r22, %r11
	and %r22, %r22, %r14
	xor %r27, %r26, %r22
	or %r15, %r15, %r12
	xor %r15, %r15, %r12
	xor %r15, %r22, %r15
	xor %r20, %r20, %r11
	and %r20, %r20, %r24
	or %r15, %r15, %r20
	or %r16, %r16, %r6
	xor %r16, %r16, %r6
	xor %r6, %r2, %r26
	or %r6, %r6, %r16
	xor %r6, %r6, %r16
	xor %r16, %r6, %r11
	and %r25, %r19, %r25
	xor %r16, %r16, %r25
	or %r27, %r27, %r17
	xor %r27, %r27, %r17
	xor %r27, %r27, %r16
	xor %r6, %r24, %r6
	or %r22, %r22, %r6
	xor %r22, %r19, %r22
	xor %r18, %r18, %r22
	xor %r16, %r16, %r18
	or %r23, %r23, %r17
	xor %r23, %r23, %r16
	xor %r19, %r19, %r26
	or %r19, %r15, %r19
	xor %r19, %r18, %r19
	or %r24, %r24, %r16
	xor %r24, %r19, %r24
	or %r16, %r21, %r17
	xor %r16, %r16, %r24
	or %r14, %r14, %r2
	or %r14, %r14, %r19
	xor %r14, %r14, %r19
	and %r21, %r21, %r18
	xor %r14, %r14, %r21
	or %r14, %r14, %r17
	xor %r14, %r14, %r15
	ld %r0, 64(%r10)
	xor %r0, %r0, %r14
	std %r0, 64(%r10)
	ld %r0, 80(%r10)
	xor %r0, %r0, %r27
	std %r0, 80(%r10)
	ld %r0, 464(%r10)
	xor %r0, %r0, %r16
	std %r0, 464(%r10)
	ld %r0, 480(%r10)
	xor %r0, %r0, %r23
	std %r0, 480(%r10)
	rldicr %r12, %r9, 27, 36
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 488(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 26, 37
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 56(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 25, 38
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 120(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 24, 39
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 184(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 23, 40
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 248(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 22, 41
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 312(%r10)
	xor %r18, %r18, %r0
	xor %r6, %r17, %r14
	or %r2, %r18, %r12
	xor %r2, %r2, %r12
	xor %r2, %r2, %r11
	and %r2, %r2, %r14
	or %r19, %r17, %r2
	or %r20, %r6, %r12
	xor %r20, %r20, %r12
	and %r21, %r18, %r6
	xor %r14, %r14, %r21
	or %r21, %r14, %r20
	xor %r21, %r21, %r20
	and %r22, %r16, %r12
	xor %r2, %r2, %r20
	and %r2, %r19, %r2
	or %r20, %r2, %r22
	xor %r20, %r20, %r22
	and %r23, %r16, %r2
	xor %r18, %r18, %r11
	xor %r18, %r23, %r18
	xor %r12, %r12, %r6
	or %r24, %r12, %r22
	xor %r24, %r24, %r22
	xor %r25, %r18, %r24
	xor %r20, %r20, %r11
	and %r20, %r20, %r15
	xor %r20, %r20, %r25
	or %r17, %r17, %r24
	xor %r17, %r17, %r24
	xor %r14, %r14, %r17
	or %r18, %r18, %r14
	xor %r18, %r18, %r14
	xor %r16, %r16, %r12
	xor %r18, %r18, %r16
	or %r24, %r19, %r15
	xor %r24, %r24, %r15
	xor %r24, %r24, %r18
	xor %r23, %r23, %r17
	or %r16, %r16, %r23
	xor %r19, %r19, %r25
	or %r22, %r22, %r19
	xor %r23, %r16, %r22
	xor %r2, %r2, %r25
	xor %r18, %r18, %r2
	and %r22, %r22, %r18
	and %r6, %r6, %r16
	xor %r22, %r22, %r6
	or %r6, %r22, %r15
	xor %r6, %r6, %r23
	or %r22, %r22, %r14
	xor %r22, %r22, %r14
	or %r12, %r12, %r19
	xor %r22, %r22, %r12
	or %r21, %r21, %r15
	xor %r21, %r21, %r22
	ld %r0, 400(%r10)
	xor %r0, %r0, %r21
	std %r0, 400(%r10)
	ld %r0, 432(%r10)
	xor %r0, %r0, %r6
	std %r0, 432(%r10)
	ld %r0, 256(%r10)
	xor %r0, %r0, %r20
	std %r0, 256(%r10)
	ld %r0, 224(%r10)
	xor %r0, %r0, %r24
	std %r0, 224(%r10)
	rldicr %r12, %r9, 33, 30
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 232(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 32, 31
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 296(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 31, 32
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 360(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 30, 33
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 424(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 29, 34
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 488(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 28, 35
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 56(%r10)
	xor %r18, %r18, %r0
	or %r6, %r18, %r17
	xor %r6, %r6, %r17
	xor %r2, %r16, %r12
	or %r19, %r6, %r2
	xor %r20, %r15, %r12
	or %r21, %r20, %r18
	xor %r21, %r21, %r18
	xor %r22, %r19, %r21
	xor %r23, %r17, %r2
	or %r24, %r23, %r12
	xor %r24, %r24, %r12
	xor %r19, %r19, %r24
	or %r24, %r22, %r19
	xor %r24, %r24, %r19
	and %r25, %r12, %r22
	or %r25, %r15, %r25
	and %r25, %r18, %r25
	xor %r25, %r23, %r25
	or %r26, %r22, %r14
	xor %r26, %r26, %r14
	xor %r26, %r26, %r25
	and %r2, %r2, %r20
	xor %r20, %r18, %r15
	xor %r27, %r19, %r20
	or %r27, %r16, %r27
	or %r27, %r27, %r2
	xor %r27, %r27, %r2
	or %r21, %r21, %r20
	or %r20, %r25, %r21
	xor %r20, %r20, %r21
	and %r12, %r15, %r12
	or %r2, %r12, %r17
	xor %r2, %r2, %r17
	xor %r20, %r20, %r2
	and %r19, %r19, %r20
	or %r12, %r23, %r12
	or %r12, %r12, %r19
	xor %r12, %r12, %r19
	xor %r18, %r18, %r12
	and %r27, %r27, %r14
	xor %r27, %r27, %r18
	xor %r22, %r22, %r11
	or %r17, %r17, %r22
	or %r16, %r16, %r17
	xor %r23, %r23, %r16
	xor %r21, %r21, %r23
	xor %r24, %r24, %r11
	and %r24, %r24, %r14
	xor %r24, %r24, %r21
	and %r15, %r15, %r22
	xor %r25, %r25, %r15
	or %r23, %r23, %r25
	xor %r6, %r6, %r18
	xor %r23, %r23, %r6
	or %r20, %r20, %r14
	xor %r20, %r20, %r23
	ld %r0, 176(%r10)
	xor %r0, %r0, %r26
	std %r0, 176(%r10)
	ld %r0, 128(%r10)
	xor %r0, %r0, %r20
	std %r0, 128(%r10)
	ld %r0, 32(%r10)
	xor %r0, %r0, %r27
	std %r0, 32(%r10)
	ld %r0, 16(%r10)
	xor %r0, %r0, %r24
	std %r0, 16(%r10)
	rldicr %r12, %r9, 39, 24
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 472(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 38, 25
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 40(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 37, 26
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 104(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 36, 27
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 168(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 35, 28
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 232(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 34, 29
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 296(%r10)
	xor %r18, %r18, %r0
	xor %r18, %r18, %r16
	xor %r16, %r16, %r14
	or %r6, %r17, %r15
	xor %r6, %r14, %r6
	xor %r6, %r6, %r11
	and %r6, %r6, %r16
	or %r2, %r16, %r17
	xor %r2, %r2, %r17
	xor %r19, %r15, %r2
	or %r20, %r18, %r19
	or %r20, %r20, %r6
	xor %r20, %r20, %r6
	xor %r21, %r17, %r20
	and %r19, %r19, %r21
	or %r16, %r16, %r19
	xor %r16, %r16, %r19
	xor %r18, %r18, %r21
	xor %r16, %r16, %r11
	and %r16, %r16, %r18
	xor %r6, %r6, %r16
	xor %r17, %r17, %r15
	or %r14, %r14, %r2
	xor %r18, %r18, %r14
	or %r14, %r18, %r17
	xor %r14, %r14, %r17
	xor %r20, %r20, %r14
	or %r14, %r12, %r6
	xor %r14, %r14, %r6
	xor %r14, %r14, %r20
	xor %r20, %r20, %r11
	or %r2, %r6, %r12
	xor %r2, %r2, %r12
	xor %r2, %r2, %r20
	xor %r6, %r6, %r20
	or %r6, %r6, %r17
	xor %r6, %r6, %r17
	or %r19, %r19, %r6
	xor %r18, %r18, %r19
	or %r19, %r21, %r12
	xor %r19, %r19, %r18
	and %r12, %r12, %r21
	xor %r12, %r12, %r18
	ld %r0, 496(%r10)
	xor %r0, %r0, %r12
	std %r0, 496(%r10)
	ld %r0, 416(%r10)
	xor %r0, %r0, %r19
	std %r0, 416(%r10)
	ld %r0, 272(%r10)
	xor %r0, %r0, %r2
	std %r0, 272(%r10)
	ld %r0, 384(%r10)
	xor %r0, %r0, %r14
	std %r0, 384(%r10)
	rldicr %r12, %r9, 45, 18
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 216(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 44, 19
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 280(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 43, 20
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 344(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 42, 21
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 408(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 41, 22
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 472(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 40, 23
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 40(%r10)
	xor %r18, %r18, %r0
	or %r6, %r18, %r16
	or %r2, %r6, %r12
	xor %r2, %r2, %r12
	xor %r19, %r18, %r2
	xor %r20, %r16, %r19
	or %r21, %r15, %r20
	or %r2, %r2, %r15
	xor %r2, %r2, %r15
	xor %r16, %r16, %r2
	and %r2, %r14, %r16
	or %r20, %r18, %r20
	xor %r2, %r2, %r20
	xor %r2, %r15, %r2
	xor %r12, %r12, %r2
	or %r22, %r19, %r12
	and %r23, %r14, %r22
	xor %r24, %r19, %r23
	and %r25, %r15, %r20
	xor %r24, %r24, %r25
	or %r22, %r22, %r18
	xor %r22, %r22, %r18
	xor %r25, %r16, %r22
	xor %r14, %r14, %r21
	xor %r25, %r25, %r11
	and %r25, %r25, %r14
	xor %r25, %r25, %r11
	or %r25, %r25, %r17
	xor %r25, %r25, %r17
	xor %r25, %r25, %r2
	or %r2, %r16, %r23
	xor %r2, %r2, %r23
	xor %r22, %r22, %r14
	or %r22, %r24, %r22
	or %r22, %r22, %r2
	xor %r22, %r22, %r2
	or %r2, %r21, %r22
	xor %r2, %r2, %r22
	and %r12, %r12, %r22
	xor %r14, %r14, %r12
	and %r20, %r16, %r20
	or %r20, %r14, %r20
	xor %r23, %r23, %r20
	and %r23, %r23, %r17
	xor %r23, %r23, %r24
	xor %r18, %r18, %r6
	xor %r22, %r22, %r18
	and %r15, %r15, %r14
	xor %r22, %r22, %r15
	or %r2, %r2, %r17
	xor %r2, %r2, %r22
	xor %r16, %r21, %r16
	or %r16, %r16, %r22
	xor %r16, %r16, %r22
	xor %r19, %r19, %r14
	xor %r16, %r16, %r19
	and %r21, %r21, %r17
	xor %r21, %r21, %r16
	ld %r0, 368(%r10)
	xor %r0, %r0, %r23
	std %r0, 368(%r10)
	ld %r0, 448(%r10)
	xor %r0, %r0, %r25
	std %r0, 448(%r10)
	ld %r0, 160(%r10)
	xor %r0, %r0, %r21
	std %r0, 160(%r10)
	ld %r0, 48(%r10)
	xor %r0, %r0, %r2
	std %r0, 48(%r10)
	rldicr %r12, %r9, 51, 12
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 456(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 50, 13
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 24(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 49, 14
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 88(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 48, 15
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 152(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 47, 16
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 216(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 46, 17
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 280(%r10)
	xor %r18, %r18, %r0
	xor %r6, %r17, %r14
	or %r2, %r17, %r12
	and %r2, %r18, %r2
	xor %r6, %r6, %r2
	xor %r19, %r12, %r6
	or %r20, %r14, %r19
	xor %r20, %r20, %r19
	and %r19, %r18, %r19
	xor %r21, %r17, %r19
	xor %r22, %r18, %r16
	or %r23, %r21, %r22
	xor %r24, %r6, %r23
	and %r25, %r16, %r24
	or %r26, %r25, %r12
	xor %r26, %r26, %r12
	or %r21, %r20, %r21
	xor %r27, %r26, %r21
	and %r28, %r27, %r15
	xor %r28, %r28, %r24
	xor %r23, %r17, %r23
	or %r29, %r12, %r23
	xor %r29, %r29, %r23
	xor %r16, %r16, %r29
	or %r29, %r14, %r25
	xor %r29, %r29, %r25
	or %r29, %r16, %r29
	or %r17, %r17, %r22
	xor %r27, %r27, %r17
	or %r2, %r2, %r29
	xor %r27, %r27, %r2
	or %r24, %r18, %r24
	and %r21, %r21, %r24
	xor %r21, %r16, %r21
	xor %r26, %r26, %r11
	and %r26, %r26, %r21
	or %r20, %r20, %r15
	xor %r20, %r20, %r26
	xor %r6, %r6, %r21
	or %r14, %r14, %r6
	xor %r14, %r14, %r6
	xor %r17, %r17, %r11
	xor %r23, %r23, %r17
	xor %r14, %r14, %r23
	or %r14, %r14, %r15
	xor %r14, %r14, %r15
	xor %r14, %r14, %r27
	xor %r12, %r12, %r19
	xor %r18, %r18, %r16
	and %r12, %r12, %r18
	xor %r25, %r25, %r23
	xor %r12, %r12, %r25
	or %r29, %r29, %r15
	xor %r29, %r29, %r15
	xor %r29, %r29, %r12
	ld %r0, 336(%r10)
	xor %r0, %r0, %r28
	std %r0, 336(%r10)
	ld %r0, 352(%r10)
	xor %r0, %r0, %r20
	std %r0, 352(%r10)
	ld %r0, 192(%r10)
	xor %r0, %r0, %r14
	std %r0, 192(%r10)
	ld %r0, 304(%r10)
	xor %r0, %r0, %r29
	std %r0, 304(%r10)
	rldicr %r12, %r9, 57, 6
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 200(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 56, 7
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 264(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 55, 8
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 328(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 54, 9
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 392(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 53, 10
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 456(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 52, 11
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 24(%r10)
	xor %r18, %r18, %r0
	xor %r6, %r15, %r14
	xor %r2, %r16, %r6
	and %r19, %r12, %r2
	and %r20, %r15, %r6
	xor %r21, %r17, %r20
	and %r22, %r19, %r21
	and %r23, %r12, %r20
	xor %r24, %r16, %r23
	or %r25, %r21, %r24
	xor %r6, %r12, %r6
	xor %r26, %r25, %r6
	or %r27, %r18, %r22
	xor %r27, %r27, %r22
	xor %r27, %r27, %r26
	xor %r2, %r2, %r11
	and %r2, %r2, %r14
	or %r26, %r21, %r2
	xor %r24, %r19, %r24
	xor %r26, %r26, %r24
	xor %r19, %r19, %r6
	or %r15, %r15, %r19
	xor %r15, %r15, %r19
	or %r6, %r21, %r15
	xor %r6, %r6, %r15
	xor %r14, %r14, %r24
	xor %r6, %r6, %r14
	or %r19, %r19, %r23
	xor %r19, %r19, %r23
	or %r15, %r15, %r19
	xor %r25, %r17, %r25
	and %r25, %r6, %r25
	xor %r25, %r15, %r25
	and %r23, %r25, %r18
	xor %r23, %r23, %r6
	or %r21, %r21, %r16
	xor %r21, %r21, %r16
	or %r19, %r19, %r21
	or %r20, %r20, %r6
	and %r19, %r19, %r20
	xor %r25, %r25, %r19
	xor %r2, %r2, %r15
	and %r12, %r12, %r2
	or %r22, %r22, %r12
	xor %r19, %r19, %r22
	or %r12, %r19, %r18
	xor %r12, %r12, %r18
	xor %r12, %r12, %r26
	and %r17, %r17, %r22
	xor %r26, %r26, %r11
	xor %r17, %r17, %r26
	xor %r19, %r19, %r17
	or %r25, %r25, %r18
	xor %r25, %r25, %r19
	ld %r0, 112(%r10)
	xor %r0, %r0, %r27
	std %r0, 112(%r10)
	ld %r0, 144(%r10)
	xor %r0, %r0, %r23
	std %r0, 144(%r10)
	ld %r0, 288(%r10)
	xor %r0, %r0, %r25
	std %r0, 288(%r10)
	ld %r0, 0(%r10)
	xor %r0, %r0, %r12
	std %r0, 0(%r10)
	rldicr %r12, %r9, 63, 0
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 504(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 62, 1
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 8(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 61, 2
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 72(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 60, 3
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 136(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 59, 4
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 200(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 58, 5
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 264(%r10)
	xor %r18, %r18, %r0
	or %r6, %r16, %r17
	xor %r6, %r6, %r17
	or %r2, %r14, %r16
	xor %r2, %r2, %r16
	xor %r2, %r15, %r2
	and %r19, %r18, %r2
	or %r20, %r19, %r6
	xor %r20, %r20, %r6
	or %r21, %r17, %r2
	xor %r21, %r21, %r2
	or %r22, %r18, %r21
	or %r23, %r17, %r16
	xor %r23, %r23, %r16
	xor %r23, %r14, %r23
	and %r24, %r22, %r23
	or %r19, %r19, %r24
	xor %r2, %r2, %r11
	xor %r24, %r24, %r2
	or %r16, %r16, %r22
	xor %r16, %r16, %r22
	xor %r24, %r24, %r16
	xor %r6, %r6, %r24
	or %r16, %r20, %r12
	xor %r16, %r16, %r6
	xor %r6, %r18, %r6
	and %r22, %r14, %r6
	xor %r24, %r17, %r24
	xor %r22, %r22, %r24
	xor %r21, %r21, %r22
	xor %r22, %r19, %r22
	or %r17, %r17, %r22
	xor %r14, %r14, %r6
	xor %r17, %r17, %r14
	and %r19, %r19, %r12
	xor %r19, %r19, %r17
	xor %r23, %r23, %r21
	or %r24, %r15, %r24
	xor %r24, %r23, %r24
	xor %r18, %r18, %r24
	and %r18, %r18, %r12
	xor %r18, %r18, %r21
	or %r23, %r23, %r15
	xor %r23, %r23, %r15
	and %r17, %r17, %r23
	xor %r20, %r20, %r24
	xor %r17, %r17, %r20
	or %r17, %r17, %r12
	xor %r17, %r17, %r21
	ld %r0, 208(%r10)
	xor %r0, %r0, %r18
	std %r0, 208(%r10)
	ld %r0, 96(%r10)
	xor %r0, %r0, %r19
	std %r0, 96(%r10)
	ld %r0, 320(%r10)
	xor %r0, %r0, %r16
	std %r0, 320(%r10)
	ld %r0, 240(%r10)
	xor %r0, %r0, %r17
	std %r0, 240(%r10)
	ld %r9, 0(%r3)
	xor %r9, %r9, %r11
	addi %r3, %r3, 8
	rldicr %r12, %r9, 21, 42
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 240(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 20, 43
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 304(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 19, 44
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 368(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 18, 45
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 432(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 17, 46
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 496(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 16, 47
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 0(%r10)
	xor %r18, %r18, %r0
	or %r6, %r18, %r14
	xor %r6, %r6, %r14
	xor %r2, %r15, %r6
	or %r19, %r16, %r12
	xor %r20, %r18, %r16
	and %r21, %r19, %r20
	xor %r22, %r15, %r21
	or %r23, %r22, %r2
	xor %r23, %r23, %r2
	xor %r24, %r14, %r12
	xor %r25, %r16, %r24
	xor %r25, %r25, %r11
	and %r25, %r25, %r2
	or %r21, %r12, %r21
	xor %r25, %r25, %r21
	or %r21, %r25, %r23
	xor %r21, %r21, %r23
	or %r12, %r18, %r12
	or %r26, %r25, %r12
	xor %r22, %r22, %r11
	and %r22, %r22, %r14
	xor %r27, %r26, %r22
	or %r15, %r15, %r12
	xor %r15, %r15, %r12
	xor %r15, %r22, %r15
	xor %r20, %r20, %r11
	and %r20, %r20, %r24
	or %r15, %r15, %r20
	or %r16, %r16, %r6
	xor %r16, %r16, %r6
	xor %r6, %r2, %r26
	or %r6, %r6, %r16
	xor %r6, %r6, %r16
	xor %r16, %r6, %r11
	and %r25, %r19, %r25
	xor %r16, %r16, %r25
	or %r27, %r27, %r17
	xor %r27, %r27, %r17
	xor %r27, %r27, %r16
	xor %r6, %r24, %r6
	or %r22, %r22, %r6
	xor %r22, %r19, %r22
	xor %r18, %r18, %r22
	xor %r16, %r16, %r18
	or %r23, %r23, %r17
	xor %r23, %r23, %r16
	xor %r19, %r19, %r26
	or %r19, %r15, %r19
	xor %r19, %r18, %r19
	or %r24, %r24, %r16
	xor %r24, %r19, %r24
	or %r16, %r21, %r17
	xor %r16, %r16, %r24
	or %r14, %r14, %r2
	or %r14, %r14, %r19
	xor %r14, %r14, %r19
	and %r21, %r21, %r18
	xor %r14, %r14, %r21
	or %r14, %r14, %r17
	xor %r14, %r14, %r15
	ld %r0, 72(%r10)
	xor %r0, %r0, %r14
	std %r0, 72(%r10)
	ld %r0, 88(%r10)
	xor %r0, %r0, %r27
	std %r0, 88(%r10)
	ld %r0, 472(%r10)
	xor %r0, %r0, %r16
	std %r0, 472(%r10)
	ld %r0, 488(%r10)
	xor %r0, %r0, %r23
	std %r0, 488(%r10)
	rldicr %r12, %r9, 27, 36
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 480(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 26, 37
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 48(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 25, 38
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 112(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 24, 39
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 176(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 23, 40
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 240(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 22, 41
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 304(%r10)
	xor %r18, %r18, %r0
	xor %r6, %r17, %r14
	or %r2, %r18, %r12
	xor %r2, %r2, %r12
	xor %r2, %r2, %r11
	and %r2, %r2, %r14
	or %r19, %r17, %r2
	or %r20, %r6, %r12
	xor %r20, %r20, %r12
	and %r21, %r18, %r6
	xor %r14, %r14, %r21
	or %r21, %r14, %r20
	xor %r21, %r21, %r20
	and %r22, %r16, %r12
	xor %r2, %r2, %r20
	and %r2, %r19, %r2
	or %r20, %r2, %r22
	xor %r20, %r20, %r22
	and %r23, %r16, %r2
	xor %r18, %r18, %r11
	xor %r18, %r23, %r18
	xor %r12, %r12, %r6
	or %r24, %r12, %r22
	xor %r24, %r24, %r22
	xor %r25, %r18, %r24
	xor %r20, %r20, %r11
	and %r20, %r20, %r15
	xor %r20, %r20, %r25
	or %r17, %r17, %r24
	xor %r17, %r17, %r24
	xor %r14, %r14, %r17
	or %r18, %r18, %r14
	xor %r18, %r18, %r14
	xor %r16, %r16, %r12
	xor %r18, %r18, %r16
	or %r24, %r19, %r15
	xor %r24, %r24, %r15
	xor %r24, %r24, %r18
	xor %r23, %r23, %r17
	or %r16, %r16, %r23
	xor %r19, %r19, %r25
	or %r22, %r22, %r19
	xor %r23, %r16, %r22
	xor %r2, %r2, %r25
	xor %r18, %r18, %r2
	and %r22, %r22, %r18
	and %r6, %r6, %r16
	xor %r22, %r22, %r6
	or %r6, %r22, %r15
	xor %r6, %r6, %r23
	or %r22, %r22, %r14
	xor %r22, %r22, %r14
	or %r12, %r12, %r19
	xor %r22, %r22, %r12
	or %r21, %r21, %r15
	xor %r21, %r21, %r22
	ld %r0, 408(%r10)
	xor %r0, %r0, %r21
	std %r0, 408(%r10)
	ld %r0, 440(%r10)
	xor %r0, %r0, %r6
	std %r0, 440(%r10)
	ld %r0, 264(%r10)
	xor %r0, %r0, %r20
	std %r0, 264(%r10)
	ld %r0, 232(%r10)
	xor %r0, %r0, %r24
	std %r0, 232(%r10)
	rldicr %r12, %r9, 33, 30
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 224(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 32, 31
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 288(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 31, 32
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 352(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 30, 33
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 416(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 29, 34
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 480(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 28, 35
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 48(%r10)
	xor %r18, %r18, %r0
	or %r6, %r18, %r17
	xor %r6, %r6, %r17
	xor %r2, %r16, %r12
	or %r19, %r6, %r2
	xor %r20, %r15, %r12
	or %r21, %r20, %r18
	xor %r21, %r21, %r18
	xor %r22, %r19, %r21
	xor %r23, %r17, %r2
	or %r24, %r23, %r12
	xor %r24, %r24, %r12
	xor %r19, %r19, %r24
	or %r24, %r22, %r19
	xor %r24, %r24, %r19
	and %r25, %r12, %r22
	or %r25, %r15, %r25
	and %r25, %r18, %r25
	xor %r25, %r23, %r25
	or %r26, %r22, %r14
	xor %r26, %r26, %r14
	xor %r26, %r26, %r25
	and %r2, %r2, %r20
	xor %r20, %r18, %r15
	xor %r27, %r19, %r20
	or %r27, %r16, %r27
	or %r27, %r27, %r2
	xor %r27, %r27, %r2
	or %r21, %r21, %r20
	or %r20, %r25, %r21
	xor %r20, %r20, %r21
	and %r12, %r15, %r12
	or %r2, %r12, %r17
	xor %r2, %r2, %r17
	xor %r20, %r20, %r2
	and %r19, %r19, %r20
	or %r12, %r23, %r12
	or %r12, %r12, %r19
	xor %r12, %r12, %r19
	xor %r18, %r18, %r12
	and %r27, %r27, %r14
	xor %r27, %r27, %r18
	xor %r22, %r22, %r11
	or %r17, %r17, %r22
	or %r16, %r16, %r17
	xor %r23, %r23, %r16
	xor %r21, %r21, %r23
	xor %r24, %r24, %r11
	and %r24, %r24, %r14
	xor %r24, %r24, %r21
	and %r15, %r15, %r22
	xor %r25, %r25, %r15
	or %r23, %r23, %r25
	xor %r6, %r6, %r18
	xor %r23, %r23, %r6
	or %r20, %r20, %r14
	xor %r20, %r20, %r23
	ld %r0, 184(%r10)
	xor %r0, %r0, %r26
	std %r0, 184(%r10)
	ld %r0, 136(%r10)
	xor %r0, %r0, %r20
	std %r0, 136(%r10)
	ld %r0, 40(%r10)
	xor %r0, %r0, %r27
	std %r0, 40(%r10)
	ld %r0, 24(%r10)
	xor %r0, %r0, %r24
	std %r0, 24(%r10)
	rldicr %r12, %r9, 39, 24
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 464(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 38, 25
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 32(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 37, 26
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 96(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 36, 27
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 160(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 35, 28
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 224(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 34, 29
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 288(%r10)
	xor %r18, %r18, %r0
	xor %r18, %r18, %r16
	xor %r16, %r16, %r14
	or %r6, %r17, %r15
	xor %r6, %r14, %r6
	xor %r6, %r6, %r11
	and %r6, %r6, %r16
	or %r2, %r16, %r17
	xor %r2, %r2, %r17
	xor %r19, %r15, %r2
	or %r20, %r18, %r19
	or %r20, %r20, %r6
	xor %r20, %r20, %r6
	xor %r21, %r17, %r20
	and %r19, %r19, %r21
	or %r16, %r16, %r19
	xor %r16, %r16, %r19
	xor %r18, %r18, %r21
	xor %r16, %r16, %r11
	and %r16, %r16, %r18
	xor %r6, %r6, %r16
	xor %r17, %r17, %r15
	or %r14, %r14, %r2
	xor %r18, %r18, %r14
	or %r14, %r18, %r17
	xor %r14, %r14, %r17
	xor %r20, %r20, %r14
	or %r14, %r12, %r6
	xor %r14, %r14, %r6
	xor %r14, %r14, %r20
	xor %r20, %r20, %r11
	or %r2, %r6, %r12
	xor %r2, %r2, %r12
	xor %r2, %r2, %r20
	xor %r6, %r6, %r20
	or %r6, %r6, %r17
	xor %r6, %r6, %r17
	or %r19, %r19, %r6
	xor %r18, %r18, %r19
	or %r19, %r21, %r12
	xor %r19, %r19, %r18
	and %r12, %r12, %r21
	xor %r12, %r12, %r18
	ld %r0, 504(%r10)
	xor %r0, %r0, %r12
	std %r0, 504(%r10)
	ld %r0, 424(%r10)
	xor %r0, %r0, %r19
	std %r0, 424(%r10)
	ld %r0, 280(%r10)
	xor %r0, %r0, %r2
	std %r0, 280(%r10)
	ld %r0, 392(%r10)
	xor %r0, %r0, %r14
	std %r0, 392(%r10)
	rldicr %r12, %r9, 45, 18
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 208(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 44, 19
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 272(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 43, 20
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 336(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 42, 21
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 400(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 41, 22
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 464(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 40, 23
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 32(%r10)
	xor %r18, %r18, %r0
	or %r6, %r18, %r16
	or %r2, %r6, %r12
	xor %r2, %r2, %r12
	xor %r19, %r18, %r2
	xor %r20, %r16, %r19
	or %r21, %r15, %r20
	or %r2, %r2, %r15
	xor %r2, %r2, %r15
	xor %r16, %r16, %r2
	and %r2, %r14, %r16
	or %r20, %r18, %r20
	xor %r2, %r2, %r20
	xor %r2, %r15, %r2
	xor %r12, %r12, %r2
	or %r22, %r19, %r12
	and %r23, %r14, %r22
	xor %r24, %r19, %r23
	and %r25, %r15, %r20
	xor %r24, %r24, %r25
	or %r22, %r22, %r18
	xor %r22, %r22, %r18
	xor %r25, %r16, %r22
	xor %r14, %r14, %r21
	xor %r25, %r25, %r11
	and %r25, %r25, %r14
	xor %r25, %r25, %r11
	or %r25, %r25, %r17
	xor %r25, %r25, %r17
	xor %r25, %r25, %r2
	or %r2, %r16, %r23
	xor %r2, %r2, %r23
	xor %r22, %r22, %r14
	or %r22, %r24, %r22
	or %r22, %r22, %r2
	xor %r22, %r22, %r2
	or %r2, %r21, %r22
	xor %r2, %r2, %r22
	and %r12, %r12, %r22
	xor %r14, %r14, %r12
	and %r20, %r16, %r20
	or %r20, %r14, %r20
	xor %r23, %r23, %r20
	and %r23, %r23, %r17
	xor %r23, %r23, %r24
	xor %r18, %r18, %r6
	xor %r22, %r22, %r18
	and %r15, %r15, %r14
	xor %r22, %r22, %r15
	or %r2, %r2, %r17
	xor %r2, %r2, %r22
	xor %r16, %r21, %r16
	or %r16, %r16, %r22
	xor %r16, %r16, %r22
	xor %r19, %r19, %r14
	xor %r16, %r16, %r19
	and %r21, %r21, %r17
	xor %r21, %r21, %r16
	ld %r0, 376(%r10)
	xor %r0, %r0, %r23
	std %r0, 376(%r10)
	ld %r0, 456(%r10)
	xor %r0, %r0, %r25
	std %r0, 456(%r10)
	ld %r0, 168(%r10)
	xor %r0, %r0, %r21
	std %r0, 168(%r10)
	ld %r0, 56(%r10)
	xor %r0, %r0, %r2
	std %r0, 56(%r10)
	rldicr %r12, %r9, 51, 12
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 448(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 50, 13
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 16(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 49, 14
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 80(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 48, 15
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 144(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 47, 16
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 208(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 46, 17
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 272(%r10)
	xor %r18, %r18, %r0
	xor %r6, %r17, %r14
	or %r2, %r17, %r12
	and %r2, %r18, %r2
	xor %r6, %r6, %r2
	xor %r19, %r12, %r6
	or %r20, %r14, %r19
	xor %r20, %r20, %r19
	and %r19, %r18, %r19
	xor %r21, %r17, %r19
	xor %r22, %r18, %r16
	or %r23, %r21, %r22
	xor %r24, %r6, %r23
	and %r25, %r16, %r24
	or %r26, %r25, %r12
	xor %r26, %r26, %r12
	or %r21, %r20, %r21
	xor %r27, %r26, %r21
	and %r28, %r27, %r15
	xor %r28, %r28, %r24
	xor %r23, %r17, %r23
	or %r29, %r12, %r23
	xor %r29, %r29, %r23
	xor %r16, %r16, %r29
	or %r29, %r14, %r25
	xor %r29, %r29, %r25
	or %r29, %r16, %r29
	or %r17, %r17, %r22
	xor %r27, %r27, %r17
	or %r2, %r2, %r29
	xor %r27, %r27, %r2
	or %r24, %r18, %r24
	and %r21, %r21, %r24
	xor %r21, %r16, %r21
	xor %r26, %r26, %r11
	and %r26, %r26, %r21
	or %r20, %r20, %r15
	xor %r20, %r20, %r26
	xor %r6, %r6, %r21
	or %r14, %r14, %r6
	xor %r14, %r14, %r6
	xor %r17, %r17, %r11
	xor %r23, %r23, %r17
	xor %r14, %r14, %r23
	or %r14, %r14, %r15
	xor %r14, %r14, %r15
	xor %r14, %r14, %r27
	xor %r12, %r12, %r19
	xor %r18, %r18, %r16
	and %r12, %r12, %r18
	xor %r25, %r25, %r23
	xor %r12, %r12, %r25
	or %r29, %r29, %r15
	xor %r29, %r29, %r15
	xor %r29, %r29, %r12
	ld %r0, 344(%r10)
	xor %r0, %r0, %r28
	std %r0, 344(%r10)
	ld %r0, 360(%r10)
	xor %r0, %r0, %r20
	std %r0, 360(%r10)
	ld %r0, 200(%r10)
	xor %r0, %r0, %r14
	std %r0, 200(%r10)
	ld %r0, 312(%r10)
	xor %r0, %r0, %r29
	std %r0, 312(%r10)
	rldicr %r12, %r9, 57, 6
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 192(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 56, 7
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 256(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 55, 8
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 320(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 54, 9
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 384(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 53, 10
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 448(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 52, 11
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 16(%r10)
	xor %r18, %r18, %r0
	xor %r6, %r15, %r14
	xor %r2, %r16, %r6
	and %r19, %r12, %r2
	and %r20, %r15, %r6
	xor %r21, %r17, %r20
	and %r22, %r19, %r21
	and %r23, %r12, %r20
	xor %r24, %r16, %r23
	or %r25, %r21, %r24
	xor %r6, %r12, %r6
	xor %r26, %r25, %r6
	or %r27, %r18, %r22
	xor %r27, %r27, %r22
	xor %r27, %r27, %r26
	xor %r2, %r2, %r11
	and %r2, %r2, %r14
	or %r26, %r21, %r2
	xor %r24, %r19, %r24
	xor %r26, %r26, %r24
	xor %r19, %r19, %r6
	or %r15, %r15, %r19
	xor %r15, %r15, %r19
	or %r6, %r21, %r15
	xor %r6, %r6, %r15
	xor %r14, %r14, %r24
	xor %r6, %r6, %r14
	or %r19, %r19, %r23
	xor %r19, %r19, %r23
	or %r15, %r15, %r19
	xor %r25, %r17, %r25
	and %r25, %r6, %r25
	xor %r25, %r15, %r25
	and %r23, %r25, %r18
	xor %r23, %r23, %r6
	or %r21, %r21, %r16
	xor %r21, %r21, %r16
	or %r19, %r19, %r21
	or %r20, %r20, %r6
	and %r19, %r19, %r20
	xor %r25, %r25, %r19
	xor %r2, %r2, %r15
	and %r12, %r12, %r2
	or %r22, %r22, %r12
	xor %r19, %r19, %r22
	or %r12, %r19, %r18
	xor %r12, %r12, %r18
	xor %r12, %r12, %r26
	and %r17, %r17, %r22
	xor %r26, %r26, %r11
	xor %r17, %r17, %r26
	xor %r19, %r19, %r17
	or %r25, %r25, %r18
	xor %r25, %r25, %r19
	ld %r0, 120(%r10)
	xor %r0, %r0, %r27
	std %r0, 120(%r10)
	ld %r0, 152(%r10)
	xor %r0, %r0, %r23
	std %r0, 152(%r10)
	ld %r0, 296(%r10)
	xor %r0, %r0, %r25
	std %r0, 296(%r10)
	ld %r0, 8(%r10)
	xor %r0, %r0, %r12
	std %r0, 8(%r10)
	rldicr %r12, %r9, 63, 0
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 496(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 62, 1
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 0(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 61, 2
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 64(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 60, 3
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 128(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 59, 4
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 192(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 58, 5
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 256(%r10)
	xor %r18, %r18, %r0
	or %r6, %r16, %r17
	xor %r6, %r6, %r17
	or %r2, %r14, %r16
	xor %r2, %r2, %r16
	xor %r2, %r15, %r2
	and %r19, %r18, %r2
	or %r20, %r19, %r6
	xor %r20, %r20, %r6
	or %r21, %r17, %r2
	xor %r21, %r21, %r2
	or %r22, %r18, %r21
	or %r23, %r17, %r16
	xor %r23, %r23, %r16
	xor %r23, %r14, %r23
	and %r24, %r22, %r23
	or %r19, %r19, %r24
	xor %r2, %r2, %r11
	xor %r24, %r24, %r2
	or %r16, %r16, %r22
	xor %r16, %r16, %r22
	xor %r24, %r24, %r16
	xor %r6, %r6, %r24
	or %r16, %r20, %r12
	xor %r16, %r16, %r6
	xor %r6, %r18, %r6
	and %r22, %r14, %r6
	xor %r24, %r17, %r24
	xor %r22, %r22, %r24
	xor %r21, %r21, %r22
	xor %r22, %r19, %r22
	or %r17, %r17, %r22
	xor %r14, %r14, %r6
	xor %r17, %r17, %r14
	and %r19, %r19, %r12
	xor %r19, %r19, %r17
	xor %r23, %r23, %r21
	or %r24, %r15, %r24
	xor %r24, %r23, %r24
	xor %r18, %r18, %r24
	and %r18, %r18, %r12
	xor %r18, %r18, %r21
	or %r23, %r23, %r15
	xor %r23, %r23, %r15
	and %r17, %r17, %r23
	xor %r20, %r20, %r24
	xor %r17, %r17, %r20
	or %r17, %r17, %r12
	xor %r17, %r17, %r21
	ld %r0, 216(%r10)
	xor %r0, %r0, %r18
	std %r0, 216(%r10)
	ld %r0, 104(%r10)
	xor %r0, %r0, %r19
	std %r0, 104(%r10)
	ld %r0, 328(%r10)
	xor %r0, %r0, %r16
	std %r0, 328(%r10)
	ld %r0, 248(%r10)
	xor %r0, %r0, %r17
	std %r0, 248(%r10)
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 28b
	ld %r12, 0(%r10)
	ld %r14, 8(%r10)
	std %r14, 0(%r10)
	std %r12, 8(%r10)
	ld %r12, 64(%r10)
	ld %r14, 72(%r10)
	std %r14, 64(%r10)
	std %r12, 72(%r10)
	ld %r12, 128(%r10)
	ld %r14, 136(%r10)
	std %r14, 128(%r10)
	std %r12, 136(%r10)
	ld %r12, 192(%r10)
	ld %r14, 200(%r10)
	std %r14, 192(%r10)
	std %r12, 200(%r10)
	ld %r12, 256(%r10)
	ld %r14, 264(%r10)
	std %r14, 256(%r10)
	std %r12, 264(%r10)
	ld %r12, 320(%r10)
	ld %r14, 328(%r10)
	std %r14, 320(%r10)
	std %r12, 328(%r10)
	ld %r12, 384(%r10)
	ld %r14, 392(%r10)
	std %r14, 384(%r10)
	std %r12, 392(%r10)
	ld %r12, 448(%r10)
	ld %r14, 456(%r10)
	std %r14, 448(%r10)
	std %r12, 456(%r10)
	ld %r12, 16(%r10)
	ld %r14, 24(%r10)
	std %r14, 16(%r10)
	std %r12, 24(%r10)
	ld %r12, 80(%r10)
	ld %r14, 88(%r10)
	std %r14, 80(%r10)
	std %r12, 88(%r10)
	ld %r12, 144(%r10)
	ld %r14, 152(%r10)
	std %r14, 144(%r10)
	std %r12, 152(%r10)
	ld %r12, 208(%r10)
	ld %r14, 216(%r10)
	std %r14, 208(%r10)
	std %r12, 216(%r10)
	ld %r12, 272(%r10)
	ld %r14, 280(%r10)
	std %r14, 272(%r10)
	std %r12, 280(%r10)
	ld %r12, 336(%r10)
	ld %r14, 344(%r10)
	std %r14, 336(%r10)
	std %r12, 344(%r10)
	ld %r12, 400(%r10)
	ld %r14, 408(%r10)
	std %r14, 400(%r10)
	std %r12, 408(%r10)
	ld %r12, 464(%r10)
	ld %r14, 472(%r10)
	std %r14, 464(%r10)
	std %r12, 472(%r10)
	ld %r12, 32(%r10)
	ld %r14, 40(%r10)
	std %r14, 32(%r10)
	std %r12, 40(%r10)
	ld %r12, 96(%r10)
	ld %r14, 104(%r10)
	std %r14, 96(%r10)
	std %r12, 104(%r10)
	ld %r12, 160(%r10)
	ld %r14, 168(%r10)
	std %r14, 160(%r10)
	std %r12, 168(%r10)
	ld %r12, 224(%r10)
	ld %r14, 232(%r10)
	std %r14, 224(%r10)
	std %r12, 232(%r10)
	ld %r12, 288(%r10)
	ld %r14, 296(%r10)
	std %r14, 288(%r10)
	std %r12, 296(%r10)
	ld %r12, 352(%r10)
	ld %r14, 360(%r10)
	std %r14, 352(%r10)
	std %r12, 360(%r10)
	ld %r12, 416(%r10)
	ld %r14, 424(%r10)
	std %r14, 416(%r10)
	std %r12, 424(%r10)
	ld %r12, 480(%r10)
	ld %r14, 488(%r10)
	std %r14, 480(%r10)
	std %r12, 488(%r10)
	ld %r12, 48(%r10)
	ld %r14, 56(%r10)
	std %r14, 48(%r10)
	std %r12, 56(%r10)
	ld %r12, 112(%r10)
	ld %r14, 120(%r10)
	std %r14, 112(%r10)
	std %r12, 120(%r10)
	ld %r12, 176(%r10)
	ld %r14, 184(%r10)
	std %r14, 176(%r10)
	std %r12, 184(%r10)
	ld %r12, 240(%r10)
	ld %r14, 248(%r10)
	std %r14, 240(%r10)
	std %r12, 248(%r10)
	ld %r12, 304(%r10)
	ld %r14, 312(%r10)
	std %r14, 304(%r10)
	std %r12, 312(%r10)
	ld %r12, 368(%r10)
	ld %r14, 376(%r10)
	std %r14, 368(%r10)
	std %r12, 376(%r10)
	ld %r12, 432(%r10)
	ld %r14, 440(%r10)
	std %r14, 432(%r10)
	std %r12, 440(%r10)
	ld %r12, 496(%r10)
	ld %r14, 504(%r10)
	std %r14, 496(%r10)
	std %r12, 504(%r10)
	addi %r25, %r10, 512
	ld %r21, 0(%r25)
	ld %r22, 8(%r25)
	ld %r23, 16(%r25)
	ld %r12, 0(%r10)
	ld %r14, 64(%r10)
	ld %r15, 128(%r10)
	ld %r16, 192(%r10)
	ld %r17, 256(%r10)
	ld %r18, 320(%r10)
	ld %r19, 384(%r10)
	ld %r20, 448(%r10)
	rldicl %r24, %r12, 32, 32
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 32, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 32, 32
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 32, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 32, 32
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 32, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 32, 32
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 32, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 48, 16
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 16, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 48, 16
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 16, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 48, 16
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 16, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 48, 16
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 16, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 56, 8
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 8, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 56, 8
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 8, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 56, 8
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 8, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 56, 8
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 8, 0
	xor %r19, %r19, %r24
	std %r12, 0(%r10)
	std %r14, 64(%r10)
	std %r15, 128(%r10)
	std %r16, 192(%r10)
	std %r17, 256(%r10)
	std %r18, 320(%r10)
	std %r19, 384(%r10)
	std %r20, 448(%r10)
	ld %r12, 8(%r10)
	ld %r14, 72(%r10)
	ld %r15, 136(%r10)
	ld %r16, 200(%r10)
	ld %r17, 264(%r10)
	ld %r18, 328(%r10)
	ld %r19, 392(%r10)
	ld %r20, 456(%r10)
	rldicl %r24, %r12, 32, 32
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 32, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 32, 32
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 32, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 32, 32
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 32, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 32, 32
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 32, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 48, 16
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 16, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 48, 16
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 16, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 48, 16
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 16, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 48, 16
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 16, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 56, 8
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 8, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 56, 8
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 8, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 56, 8
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 8, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 56, 8
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 8, 0
	xor %r19, %r19, %r24
	std %r12, 8(%r10)
	std %r14, 72(%r10)
	std %r15, 136(%r10)
	std %r16, 200(%r10)
	std %r17, 264(%r10)
	std %r18, 328(%r10)
	std %r19, 392(%r10)
	std %r20, 456(%r10)
	ld %r12, 16(%r10)
	ld %r14, 80(%r10)
	ld %r15, 144(%r10)
	ld %r16, 208(%r10)
	ld %r17, 272(%r10)
	ld %r18, 336(%r10)
	ld %r19, 400(%r10)
	ld %r20, 464(%r10)
	rldicl %r24, %r12, 32, 32
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 32, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 32, 32
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 32, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 32, 32
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 32, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 32, 32
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 32, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 48, 16
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 16, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 48, 16
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 16, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 48, 16
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 16, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 48, 16
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 16, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 56, 8
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 8, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 56, 8
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 8, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 56, 8
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 8, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 56, 8
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 8, 0
	xor %r19, %r19, %r24
	std %r12, 16(%r10)
	std %r14, 80(%r10)
	std %r15, 144(%r10)
	std %r16, 208(%r10)
	std %r17, 272(%r10)
	std %r18, 336(%r10)
	std %r19, 400(%r10)
	std %r20, 464(%r10)
	ld %r12, 24(%r10)
	ld %r14, 88(%r10)
	ld %r15, 152(%r10)
	ld %r16, 216(%r10)
	ld %r17, 280(%r10)
	ld %r18, 344(%r10)
	ld %r19, 408(%r10)
	ld %r20, 472(%r10)
	rldicl %r24, %r12, 32, 32
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 32, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 32, 32
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 32, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 32, 32
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 32, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 32, 32
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 32, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 48, 16
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 16, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 48, 16
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 16, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 48, 16
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 16, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 48, 16
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 16, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 56, 8
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 8, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 56, 8
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 8, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 56, 8
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 8, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 56, 8
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 8, 0
	xor %r19, %r19, %r24
	std %r12, 24(%r10)
	std %r14, 88(%r10)
	std %r15, 152(%r10)
	std %r16, 216(%r10)
	std %r17, 280(%r10)
	std %r18, 344(%r10)
	std %r19, 408(%r10)
	std %r20, 472(%r10)
	ld %r12, 32(%r10)
	ld %r14, 96(%r10)
	ld %r15, 160(%r10)
	ld %r16, 224(%r10)
	ld %r17, 288(%r10)
	ld %r18, 352(%r10)
	ld %r19, 416(%r10)
	ld %r20, 480(%r10)
	rldicl %r24, %r12, 32, 32
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 32, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 32, 32
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 32, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 32, 32
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 32, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 32, 32
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 32, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 48, 16
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 16, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 48, 16
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 16, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 48, 16
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 16, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 48, 16
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 16, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 56, 8
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 8, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 56, 8
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 8, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 56, 8
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 8, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 56, 8
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 8, 0
	xor %r19, %r19, %r24
	std %r12, 32(%r10)
	std %r14, 96(%r10)
	std %r15, 160(%r10)
	std %r16, 224(%r10)
	std %r17, 288(%r10)
	std %r18, 352(%r10)
	std %r19, 416(%r10)
	std %r20, 480(%r10)
	ld %r12, 40(%r10)
	ld %r14, 104(%r10)
	ld %r15, 168(%r10)
	ld %r16, 232(%r10)
	ld %r17, 296(%r10)
	ld %r18, 360(%r10)
	ld %r19, 424(%r10)
	ld %r20, 488(%r10)
	rldicl %r24, %r12, 32, 32
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 32, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 32, 32
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 32, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 32, 32
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 32, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 32, 32
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 32, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 48, 16
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 16, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 48, 16
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 16, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 48, 16
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 16, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 48, 16
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 16, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 56, 8
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 8, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 56, 8
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 8, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 56, 8
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 8, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 56, 8
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 8, 0
	xor %r19, %r19, %r24
	std %r12, 40(%r10)
	std %r14, 104(%r10)
	std %r15, 168(%r10)
	std %r16, 232(%r10)
	std %r17, 296(%r10)
	std %r18, 360(%r10)
	std %r19, 424(%r10)
	std %r20, 488(%r10)
	ld %r12, 48(%r10)
	ld %r14, 112(%r10)
	ld %r15, 176(%r10)
	ld %r16, 240(%r10)
	ld %r17, 304(%r10)
	ld %r18, 368(%r10)
	ld %r19, 432(%r10)
	ld %r20, 496(%r10)
	rldicl %r24, %r12, 32, 32
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 32, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 32, 32
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 32, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 32, 32
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 32, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 32, 32
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 32, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 48, 16
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 16, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 48, 16
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 16, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 48, 16
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 16, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 48, 16
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 16, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 56, 8
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 8, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 56, 8
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 8, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 56, 8
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 8, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 56, 8
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 8, 0
	xor %r19, %r19, %r24
	std %r12, 48(%r10)
	std %r14, 112(%r10)
	std %r15, 176(%r10)
	std %r16, 240(%r10)
	std %r17, 304(%r10)
	std %r18, 368(%r10)
	std %r19, 432(%r10)
	std %r20, 496(%r10)
	ld %r12, 56(%r10)
	ld %r14, 120(%r10)
	ld %r15, 184(%r10)
	ld %r16, 248(%r10)
	ld %r17, 312(%r10)
	ld %r18, 376(%r10)
	ld %r19, 440(%r10)
	ld %r20, 504(%r10)
	rldicl %r24, %r12, 32, 32
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 32, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 32, 32
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 32, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 32, 32
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 32, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 32, 32
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 32, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 48, 16
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 16, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 48, 16
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 16, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 48, 16
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 16, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 48, 16
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 16, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 56, 8
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 8, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 56, 8
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 8, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 56, 8
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 8, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 56, 8
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 8, 0
	xor %r19, %r19, %r24
	std %r12, 56(%r10)
	std %r14, 120(%r10)
	std %r15, 184(%r10)
	std %r16, 248(%r10)
	std %r17, 312(%r10)
	std %r18, 376(%r10)
	std %r19, 440(%r10)
	std %r20, 504(%r10)
	ld %r21, 24(%r25)
	ld %r22, 32(%r25)
	ld %r23, 40(%r25)
	ld %r12, 0(%r10)
	ld %r14, 8(%r10)
	ld %r15, 16(%r10)
	ld %r16, 24(%r10)
	ld %r17, 32(%r10)
	ld %r18, 40(%r10)
	ld %r19, 48(%r10)
	ld %r20, 56(%r10)
	rldicl %r24, %r12, 60, 4
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 4, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 60, 4
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 4, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 60, 4
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 4, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 60, 4
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 4, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 62, 2
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 2, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 62, 2
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 2, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 62, 2
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 2, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 62, 2
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 2, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 63, 1
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 1, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 63, 1
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 1, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 63, 1
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 1, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 63, 1
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 1, 0
	xor %r19, %r19, %r24
	std %r12, 0(%r10)
	std %r14, 8(%r10)
	std %r15, 16(%r10)
	std %r16, 24(%r10)
	std %r17, 32(%r10)
	std %r18, 40(%r10)
	std %r19, 48(%r10)
	std %r20, 56(%r10)
	ld %r12, 64(%r10)
	ld %r14, 72(%r10)
	ld %r15, 80(%r10)
	ld %r16, 88(%r10)
	ld %r17, 96(%r10)
	ld %r18, 104(%r10)
	ld %r19, 112(%r10)
	ld %r20, 120(%r10)
	rldicl %r24, %r12, 60, 4
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 4, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 60, 4
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 4, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 60, 4
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 4, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 60, 4
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 4, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 62, 2
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 2, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 62, 2
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 2, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 62, 2
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 2, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 62, 2
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 2, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 63, 1
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 1, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 63, 1
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 1, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 63, 1
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 1, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 63, 1
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 1, 0
	xor %r19, %r19, %r24
	std %r12, 64(%r10)
	std %r14, 72(%r10)
	std %r15, 80(%r10)
	std %r16, 88(%r10)
	std %r17, 96(%r10)
	std %r18, 104(%r10)
	std %r19, 112(%r10)
	std %r20, 120(%r10)
	ld %r12, 128(%r10)
	ld %r14, 136(%r10)
	ld %r15, 144(%r10)
	ld %r16, 152(%r10)
	ld %r17, 160(%r10)
	ld %r18, 168(%r10)
	ld %r19, 176(%r10)
	ld %r20, 184(%r10)
	rldicl %r24, %r12, 60, 4
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 4, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 60, 4
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 4, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 60, 4
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 4, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 60, 4
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 4, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 62, 2
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 2, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 62, 2
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 2, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 62, 2
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 2, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 62, 2
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 2, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 63, 1
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 1, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 63, 1
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 1, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 63, 1
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 1, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 63, 1
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 1, 0
	xor %r19, %r19, %r24
	std %r12, 128(%r10)
	std %r14, 136(%r10)
	std %r15, 144(%r10)
	std %r16, 152(%r10)
	std %r17, 160(%r10)
	std %r18, 168(%r10)
	std %r19, 176(%r10)
	std %r20, 184(%r10)
	ld %r12, 192(%r10)
	ld %r14, 200(%r10)
	ld %r15, 208(%r10)
	ld %r16, 216(%r10)
	ld %r17, 224(%r10)
	ld %r18, 232(%r10)
	ld %r19, 240(%r10)
	ld %r20, 248(%r10)
	rldicl %r24, %r12, 60, 4
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 4, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 60, 4
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 4, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 60, 4
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 4, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 60, 4
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 4, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 62, 2
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 2, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 62, 2
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 2, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 62, 2
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 2, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 62, 2
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 2, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 63, 1
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 1, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 63, 1
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 1, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 63, 1
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 1, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 63, 1
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 1, 0
	xor %r19, %r19, %r24
	std %r12, 192(%r10)
	std %r14, 200(%r10)
	std %r15, 208(%r10)
	std %r16, 216(%r10)
	std %r17, 224(%r10)
	std %r18, 232(%r10)
	std %r19, 240(%r10)
	std %r20, 248(%r10)
	ld %r12, 256(%r10)
	ld %r14, 264(%r10)
	ld %r15, 272(%r10)
	ld %r16, 280(%r10)
	ld %r17, 288(%r10)
	ld %r18, 296(%r10)
	ld %r19, 304(%r10)
	ld %r20, 312(%r10)
	rldicl %r24, %r12, 60, 4
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 4, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 60, 4
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 4, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 60, 4
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 4, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 60, 4
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 4, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 62, 2
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 2, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 62, 2
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 2, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 62, 2
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 2, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 62, 2
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 2, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 63, 1
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 1, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 63, 1
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 1, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 63, 1
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 1, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 63, 1
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 1, 0
	xor %r19, %r19, %r24
	std %r12, 256(%r10)
	std %r14, 264(%r10)
	std %r15, 272(%r10)
	std %r16, 280(%r10)
	std %r17, 288(%r10)
	std %r18, 296(%r10)
	std %r19, 304(%r10)
	std %r20, 312(%r10)
	ld %r12, 320(%r10)
	ld %r14, 328(%r10)
	ld %r15, 336(%r10)
	ld %r16, 344(%r10)
	ld %r17, 352(%r10)
	ld %r18, 360(%r10)
	ld %r19, 368(%r10)
	ld %r20, 376(%r10)
	rldicl %r24, %r12, 60, 4
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 4, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 60, 4
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 4, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 60, 4
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 4, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 60, 4
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 4, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 62, 2
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 2, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 62, 2
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 2, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 62, 2
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 2, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 62, 2
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 2, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 63, 1
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 1, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 63, 1
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 1, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 63, 1
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 1, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 63, 1
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 1, 0
	xor %r19, %r19, %r24
	std %r12, 320(%r10)
	std %r14, 328(%r10)
	std %r15, 336(%r10)
	std %r16, 344(%r10)
	std %r17, 352(%r10)
	std %r18, 360(%r10)
	std %r19, 368(%r10)
	std %r20, 376(%r10)
	ld %r12, 384(%r10)
	ld %r14, 392(%r10)
	ld %r15, 400(%r10)
	ld %r16, 408(%r10)
	ld %r17, 416(%r10)
	ld %r18, 424(%r10)
	ld %r19, 432(%r10)
	ld %r20, 440(%r10)
	rldicl %r24, %r12, 60, 4
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 4, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 60, 4
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 4, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 60, 4
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 4, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 60, 4
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 4, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 62, 2
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 2, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 62, 2
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 2, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 62, 2
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 2, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 62, 2
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 2, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 63, 1
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 1, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 63, 1
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 1, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 63, 1
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 1, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 63, 1
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 1, 0
	xor %r19, %r19, %r24
	std %r12, 384(%r10)
	std %r14, 392(%r10)
	std %r15, 400(%r10)
	std %r16, 408(%r10)
	std %r17, 416(%r10)
	std %r18, 424(%r10)
	std %r19, 432(%r10)
	std %r20, 440(%r10)
	ld %r12, 448(%r10)
	ld %r14, 456(%r10)
	ld %r15, 464(%r10)
	ld %r16, 472(%r10)
	ld %r17, 480(%r10)
	ld %r18, 488(%r10)
	ld %r19, 496(%r10)
	ld %r20, 504(%r10)
	rldicl %r24, %r12, 60, 4
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 4, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 60, 4
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 4, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 60, 4
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 4, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 60, 4
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 4, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 62, 2
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 2, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 62, 2
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 2, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 62, 2
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 2, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 62, 2
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 2, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 63, 1
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 1, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 63, 1
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 1, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 63, 1
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 1, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 63, 1
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 1, 0
	xor %r19, %r19, %r24
	std %r12, 448(%r10)
	std %r14, 456(%r10)
	std %r15, 464(%r10)
	std %r16, 472(%r10)
	std %r17, 480(%r10)
	std %r18, 488(%r10)
	std %r19, 496(%r10)
	std %r20, 504(%r10)
	rldicl %r12, %r8, 58, 6
	cmpldi %cr0, %r12, 0
	beq %cr0, 29f
	li %r12, 64
	b 210f
29:
	or %r12, %r8, %r8
210:
	or %r3, %r10, %r10
	or %r9, %r4, %r4
	or %r5, %r12, %r12
211:
	ld %r0, 0(%r3)
	std %r0, 0(%r9)
	addi %r3, %r3, 8
	addi %r9, %r9, 8
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 211b
	or %r4, %r9, %r9
	subf %r8, %r12, %r8
	cmpldi %cr0, %r8, 0
	bne %cr0, 22b
	ld %r2, 560(%r10)
	ld %r14, 568(%r10)
	ld %r15, 576(%r10)
	ld %r16, 584(%r10)
	ld %r17, 592(%r10)
	ld %r18, 600(%r10)
	ld %r19, 608(%r10)
	ld %r20, 616(%r10)
	ld %r21, 624(%r10)
	ld %r22, 632(%r10)
	ld %r23, 640(%r10)
	ld %r24, 648(%r10)
	ld %r25, 656(%r10)
	ld %r26, 664(%r10)
	ld %r27, 672(%r10)
	ld %r28, 680(%r10)
	ld %r29, 688(%r10)
	ld %r30, 696(%r10)
	ld %r31, 704(%r10)
	b 21f
20:
21:
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
	cmpldi %cr0, %r5, 0
	beq %cr0, 20f
	std %r2, 560(%r6)
	std %r14, 568(%r6)
	std %r15, 576(%r6)
	std %r16, 584(%r6)
	std %r17, 592(%r6)
	std %r18, 600(%r6)
	std %r19, 608(%r6)
	std %r20, 616(%r6)
	std %r21, 624(%r6)
	std %r22, 632(%r6)
	std %r23, 640(%r6)
	std %r24, 648(%r6)
	std %r25, 656(%r6)
	std %r26, 664(%r6)
	std %r27, 672(%r6)
	std %r28, 680(%r6)
	std %r29, 688(%r6)
	std %r30, 696(%r6)
	std %r31, 704(%r6)
	or %r10, %r6, %r6
	or %r7, %r3, %r3
	or %r8, %r5, %r5
	lis %r11, -1
	ori %r11, %r11, 65535
	lis %r12, 0
	ori %r12, %r12, 0
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 65535
	ori %r12, %r12, 65535
	std %r12, 512(%r10)
	lis %r12, 0
	ori %r12, %r12, 65535
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 0
	ori %r12, %r12, 65535
	std %r12, 520(%r10)
	lis %r12, 255
	ori %r12, %r12, 255
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 255
	ori %r12, %r12, 255
	std %r12, 528(%r10)
	lis %r12, 3855
	ori %r12, %r12, 3855
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 3855
	ori %r12, %r12, 3855
	std %r12, 536(%r10)
	lis %r12, 13107
	ori %r12, %r12, 13107
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 13107
	ori %r12, %r12, 13107
	std %r12, 544(%r10)
	lis %r12, 21845
	ori %r12, %r12, 21845
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 21845
	ori %r12, %r12, 21845
	std %r12, 552(%r10)
22:
	rldicl %r12, %r8, 58, 6
	cmpldi %cr0, %r12, 0
	beq %cr0, 23f
	li %r12, 64
	b 24f
23:
	or %r12, %r8, %r8
24:
	or %r3, %r4, %r4
	or %r9, %r10, %r10
	or %r5, %r12, %r12
25:
	ld %r0, 0(%r3)
	std %r0, 0(%r9)
	addi %r3, %r3, 8
	addi %r9, %r9, 8
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 25b
	addi %r25, %r10, 512
	ld %r21, 0(%r25)
	ld %r22, 8(%r25)
	ld %r23, 16(%r25)
	ld %r12, 0(%r10)
	ld %r14, 64(%r10)
	ld %r15, 128(%r10)
	ld %r16, 192(%r10)
	ld %r17, 256(%r10)
	ld %r18, 320(%r10)
	ld %r19, 384(%r10)
	ld %r20, 448(%r10)
	rldicl %r24, %r12, 32, 32
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 32, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 32, 32
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 32, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 32, 32
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 32, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 32, 32
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 32, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 48, 16
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 16, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 48, 16
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 16, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 48, 16
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 16, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 48, 16
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 16, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 56, 8
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 8, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 56, 8
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 8, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 56, 8
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 8, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 56, 8
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 8, 0
	xor %r19, %r19, %r24
	std %r12, 0(%r10)
	std %r14, 64(%r10)
	std %r15, 128(%r10)
	std %r16, 192(%r10)
	std %r17, 256(%r10)
	std %r18, 320(%r10)
	std %r19, 384(%r10)
	std %r20, 448(%r10)
	ld %r12, 8(%r10)
	ld %r14, 72(%r10)
	ld %r15, 136(%r10)
	ld %r16, 200(%r10)
	ld %r17, 264(%r10)
	ld %r18, 328(%r10)
	ld %r19, 392(%r10)
	ld %r20, 456(%r10)
	rldicl %r24, %r12, 32, 32
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 32, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 32, 32
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 32, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 32, 32
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 32, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 32, 32
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 32, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 48, 16
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 16, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 48, 16
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 16, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 48, 16
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 16, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 48, 16
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 16, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 56, 8
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 8, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 56, 8
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 8, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 56, 8
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 8, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 56, 8
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 8, 0
	xor %r19, %r19, %r24
	std %r12, 8(%r10)
	std %r14, 72(%r10)
	std %r15, 136(%r10)
	std %r16, 200(%r10)
	std %r17, 264(%r10)
	std %r18, 328(%r10)
	std %r19, 392(%r10)
	std %r20, 456(%r10)
	ld %r12, 16(%r10)
	ld %r14, 80(%r10)
	ld %r15, 144(%r10)
	ld %r16, 208(%r10)
	ld %r17, 272(%r10)
	ld %r18, 336(%r10)
	ld %r19, 400(%r10)
	ld %r20, 464(%r10)
	rldicl %r24, %r12, 32, 32
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 32, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 32, 32
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 32, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 32, 32
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 32, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 32, 32
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 32, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 48, 16
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 16, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 48, 16
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 16, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 48, 16
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 16, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 48, 16
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 16, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 56, 8
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 8, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 56, 8
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 8, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 56, 8
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 8, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 56, 8
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 8, 0
	xor %r19, %r19, %r24
	std %r12, 16(%r10)
	std %r14, 80(%r10)
	std %r15, 144(%r10)
	std %r16, 208(%r10)
	std %r17, 272(%r10)
	std %r18, 336(%r10)
	std %r19, 400(%r10)
	std %r20, 464(%r10)
	ld %r12, 24(%r10)
	ld %r14, 88(%r10)
	ld %r15, 152(%r10)
	ld %r16, 216(%r10)
	ld %r17, 280(%r10)
	ld %r18, 344(%r10)
	ld %r19, 408(%r10)
	ld %r20, 472(%r10)
	rldicl %r24, %r12, 32, 32
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 32, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 32, 32
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 32, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 32, 32
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 32, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 32, 32
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 32, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 48, 16
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 16, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 48, 16
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 16, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 48, 16
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 16, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 48, 16
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 16, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 56, 8
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 8, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 56, 8
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 8, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 56, 8
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 8, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 56, 8
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 8, 0
	xor %r19, %r19, %r24
	std %r12, 24(%r10)
	std %r14, 88(%r10)
	std %r15, 152(%r10)
	std %r16, 216(%r10)
	std %r17, 280(%r10)
	std %r18, 344(%r10)
	std %r19, 408(%r10)
	std %r20, 472(%r10)
	ld %r12, 32(%r10)
	ld %r14, 96(%r10)
	ld %r15, 160(%r10)
	ld %r16, 224(%r10)
	ld %r17, 288(%r10)
	ld %r18, 352(%r10)
	ld %r19, 416(%r10)
	ld %r20, 480(%r10)
	rldicl %r24, %r12, 32, 32
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 32, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 32, 32
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 32, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 32, 32
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 32, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 32, 32
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 32, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 48, 16
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 16, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 48, 16
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 16, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 48, 16
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 16, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 48, 16
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 16, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 56, 8
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 8, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 56, 8
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 8, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 56, 8
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 8, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 56, 8
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 8, 0
	xor %r19, %r19, %r24
	std %r12, 32(%r10)
	std %r14, 96(%r10)
	std %r15, 160(%r10)
	std %r16, 224(%r10)
	std %r17, 288(%r10)
	std %r18, 352(%r10)
	std %r19, 416(%r10)
	std %r20, 480(%r10)
	ld %r12, 40(%r10)
	ld %r14, 104(%r10)
	ld %r15, 168(%r10)
	ld %r16, 232(%r10)
	ld %r17, 296(%r10)
	ld %r18, 360(%r10)
	ld %r19, 424(%r10)
	ld %r20, 488(%r10)
	rldicl %r24, %r12, 32, 32
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 32, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 32, 32
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 32, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 32, 32
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 32, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 32, 32
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 32, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 48, 16
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 16, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 48, 16
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 16, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 48, 16
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 16, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 48, 16
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 16, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 56, 8
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 8, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 56, 8
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 8, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 56, 8
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 8, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 56, 8
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 8, 0
	xor %r19, %r19, %r24
	std %r12, 40(%r10)
	std %r14, 104(%r10)
	std %r15, 168(%r10)
	std %r16, 232(%r10)
	std %r17, 296(%r10)
	std %r18, 360(%r10)
	std %r19, 424(%r10)
	std %r20, 488(%r10)
	ld %r12, 48(%r10)
	ld %r14, 112(%r10)
	ld %r15, 176(%r10)
	ld %r16, 240(%r10)
	ld %r17, 304(%r10)
	ld %r18, 368(%r10)
	ld %r19, 432(%r10)
	ld %r20, 496(%r10)
	rldicl %r24, %r12, 32, 32
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 32, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 32, 32
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 32, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 32, 32
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 32, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 32, 32
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 32, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 48, 16
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 16, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 48, 16
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 16, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 48, 16
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 16, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 48, 16
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 16, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 56, 8
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 8, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 56, 8
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 8, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 56, 8
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 8, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 56, 8
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 8, 0
	xor %r19, %r19, %r24
	std %r12, 48(%r10)
	std %r14, 112(%r10)
	std %r15, 176(%r10)
	std %r16, 240(%r10)
	std %r17, 304(%r10)
	std %r18, 368(%r10)
	std %r19, 432(%r10)
	std %r20, 496(%r10)
	ld %r12, 56(%r10)
	ld %r14, 120(%r10)
	ld %r15, 184(%r10)
	ld %r16, 248(%r10)
	ld %r17, 312(%r10)
	ld %r18, 376(%r10)
	ld %r19, 440(%r10)
	ld %r20, 504(%r10)
	rldicl %r24, %r12, 32, 32
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 32, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 32, 32
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 32, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 32, 32
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 32, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 32, 32
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 32, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 48, 16
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 16, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 48, 16
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 16, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 48, 16
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 16, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 48, 16
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 16, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 56, 8
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 8, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 56, 8
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 8, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 56, 8
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 8, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 56, 8
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 8, 0
	xor %r19, %r19, %r24
	std %r12, 56(%r10)
	std %r14, 120(%r10)
	std %r15, 184(%r10)
	std %r16, 248(%r10)
	std %r17, 312(%r10)
	std %r18, 376(%r10)
	std %r19, 440(%r10)
	std %r20, 504(%r10)
	ld %r21, 24(%r25)
	ld %r22, 32(%r25)
	ld %r23, 40(%r25)
	ld %r12, 0(%r10)
	ld %r14, 8(%r10)
	ld %r15, 16(%r10)
	ld %r16, 24(%r10)
	ld %r17, 32(%r10)
	ld %r18, 40(%r10)
	ld %r19, 48(%r10)
	ld %r20, 56(%r10)
	rldicl %r24, %r12, 60, 4
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 4, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 60, 4
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 4, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 60, 4
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 4, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 60, 4
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 4, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 62, 2
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 2, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 62, 2
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 2, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 62, 2
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 2, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 62, 2
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 2, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 63, 1
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 1, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 63, 1
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 1, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 63, 1
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 1, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 63, 1
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 1, 0
	xor %r19, %r19, %r24
	std %r12, 0(%r10)
	std %r14, 8(%r10)
	std %r15, 16(%r10)
	std %r16, 24(%r10)
	std %r17, 32(%r10)
	std %r18, 40(%r10)
	std %r19, 48(%r10)
	std %r20, 56(%r10)
	ld %r12, 64(%r10)
	ld %r14, 72(%r10)
	ld %r15, 80(%r10)
	ld %r16, 88(%r10)
	ld %r17, 96(%r10)
	ld %r18, 104(%r10)
	ld %r19, 112(%r10)
	ld %r20, 120(%r10)
	rldicl %r24, %r12, 60, 4
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 4, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 60, 4
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 4, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 60, 4
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 4, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 60, 4
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 4, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 62, 2
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 2, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 62, 2
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 2, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 62, 2
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 2, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 62, 2
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 2, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 63, 1
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 1, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 63, 1
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 1, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 63, 1
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 1, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 63, 1
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 1, 0
	xor %r19, %r19, %r24
	std %r12, 64(%r10)
	std %r14, 72(%r10)
	std %r15, 80(%r10)
	std %r16, 88(%r10)
	std %r17, 96(%r10)
	std %r18, 104(%r10)
	std %r19, 112(%r10)
	std %r20, 120(%r10)
	ld %r12, 128(%r10)
	ld %r14, 136(%r10)
	ld %r15, 144(%r10)
	ld %r16, 152(%r10)
	ld %r17, 160(%r10)
	ld %r18, 168(%r10)
	ld %r19, 176(%r10)
	ld %r20, 184(%r10)
	rldicl %r24, %r12, 60, 4
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 4, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 60, 4
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 4, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 60, 4
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 4, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 60, 4
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 4, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 62, 2
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 2, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 62, 2
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 2, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 62, 2
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 2, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 62, 2
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 2, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 63, 1
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 1, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 63, 1
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 1, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 63, 1
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 1, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 63, 1
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 1, 0
	xor %r19, %r19, %r24
	std %r12, 128(%r10)
	std %r14, 136(%r10)
	std %r15, 144(%r10)
	std %r16, 152(%r10)
	std %r17, 160(%r10)
	std %r18, 168(%r10)
	std %r19, 176(%r10)
	std %r20, 184(%r10)
	ld %r12, 192(%r10)
	ld %r14, 200(%r10)
	ld %r15, 208(%r10)
	ld %r16, 216(%r10)
	ld %r17, 224(%r10)
	ld %r18, 232(%r10)
	ld %r19, 240(%r10)
	ld %r20, 248(%r10)
	rldicl %r24, %r12, 60, 4
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 4, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 60, 4
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 4, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 60, 4
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 4, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 60, 4
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 4, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 62, 2
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 2, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 62, 2
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 2, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 62, 2
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 2, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 62, 2
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 2, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 63, 1
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 1, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 63, 1
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 1, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 63, 1
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 1, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 63, 1
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 1, 0
	xor %r19, %r19, %r24
	std %r12, 192(%r10)
	std %r14, 200(%r10)
	std %r15, 208(%r10)
	std %r16, 216(%r10)
	std %r17, 224(%r10)
	std %r18, 232(%r10)
	std %r19, 240(%r10)
	std %r20, 248(%r10)
	ld %r12, 256(%r10)
	ld %r14, 264(%r10)
	ld %r15, 272(%r10)
	ld %r16, 280(%r10)
	ld %r17, 288(%r10)
	ld %r18, 296(%r10)
	ld %r19, 304(%r10)
	ld %r20, 312(%r10)
	rldicl %r24, %r12, 60, 4
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 4, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 60, 4
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 4, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 60, 4
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 4, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 60, 4
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 4, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 62, 2
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 2, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 62, 2
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 2, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 62, 2
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 2, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 62, 2
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 2, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 63, 1
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 1, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 63, 1
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 1, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 63, 1
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 1, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 63, 1
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 1, 0
	xor %r19, %r19, %r24
	std %r12, 256(%r10)
	std %r14, 264(%r10)
	std %r15, 272(%r10)
	std %r16, 280(%r10)
	std %r17, 288(%r10)
	std %r18, 296(%r10)
	std %r19, 304(%r10)
	std %r20, 312(%r10)
	ld %r12, 320(%r10)
	ld %r14, 328(%r10)
	ld %r15, 336(%r10)
	ld %r16, 344(%r10)
	ld %r17, 352(%r10)
	ld %r18, 360(%r10)
	ld %r19, 368(%r10)
	ld %r20, 376(%r10)
	rldicl %r24, %r12, 60, 4
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 4, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 60, 4
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 4, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 60, 4
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 4, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 60, 4
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 4, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 62, 2
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 2, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 62, 2
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 2, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 62, 2
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 2, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 62, 2
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 2, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 63, 1
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 1, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 63, 1
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 1, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 63, 1
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 1, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 63, 1
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 1, 0
	xor %r19, %r19, %r24
	std %r12, 320(%r10)
	std %r14, 328(%r10)
	std %r15, 336(%r10)
	std %r16, 344(%r10)
	std %r17, 352(%r10)
	std %r18, 360(%r10)
	std %r19, 368(%r10)
	std %r20, 376(%r10)
	ld %r12, 384(%r10)
	ld %r14, 392(%r10)
	ld %r15, 400(%r10)
	ld %r16, 408(%r10)
	ld %r17, 416(%r10)
	ld %r18, 424(%r10)
	ld %r19, 432(%r10)
	ld %r20, 440(%r10)
	rldicl %r24, %r12, 60, 4
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 4, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 60, 4
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 4, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 60, 4
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 4, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 60, 4
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 4, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 62, 2
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 2, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 62, 2
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 2, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 62, 2
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 2, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 62, 2
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 2, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 63, 1
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 1, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 63, 1
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 1, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 63, 1
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 1, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 63, 1
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 1, 0
	xor %r19, %r19, %r24
	std %r12, 384(%r10)
	std %r14, 392(%r10)
	std %r15, 400(%r10)
	std %r16, 408(%r10)
	std %r17, 416(%r10)
	std %r18, 424(%r10)
	std %r19, 432(%r10)
	std %r20, 440(%r10)
	ld %r12, 448(%r10)
	ld %r14, 456(%r10)
	ld %r15, 464(%r10)
	ld %r16, 472(%r10)
	ld %r17, 480(%r10)
	ld %r18, 488(%r10)
	ld %r19, 496(%r10)
	ld %r20, 504(%r10)
	rldicl %r24, %r12, 60, 4
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 4, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 60, 4
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 4, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 60, 4
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 4, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 60, 4
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 4, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 62, 2
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 2, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 62, 2
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 2, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 62, 2
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 2, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 62, 2
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 2, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 63, 1
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 1, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 63, 1
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 1, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 63, 1
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 1, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 63, 1
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 1, 0
	xor %r19, %r19, %r24
	std %r12, 448(%r10)
	std %r14, 456(%r10)
	std %r15, 464(%r10)
	std %r16, 472(%r10)
	std %r17, 480(%r10)
	std %r18, 488(%r10)
	std %r19, 496(%r10)
	std %r20, 504(%r10)
	addi %r3, %r7, 376
	li %r5, 8
26:
	ld %r9, 0(%r3)
	xor %r9, %r9, %r11
	addi %r3, %r3, -8
	rldicr %r12, %r9, 21, 42
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 248(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 20, 43
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 312(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 19, 44
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 376(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 18, 45
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 440(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 17, 46
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 504(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 16, 47
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 8(%r10)
	xor %r18, %r18, %r0
	or %r6, %r18, %r14
	xor %r6, %r6, %r14
	xor %r2, %r15, %r6
	or %r19, %r16, %r12
	xor %r20, %r18, %r16
	and %r21, %r19, %r20
	xor %r22, %r15, %r21
	or %r23, %r22, %r2
	xor %r23, %r23, %r2
	xor %r24, %r14, %r12
	xor %r25, %r16, %r24
	xor %r25, %r25, %r11
	and %r25, %r25, %r2
	or %r21, %r12, %r21
	xor %r25, %r25, %r21
	or %r21, %r25, %r23
	xor %r21, %r21, %r23
	or %r12, %r18, %r12
	or %r26, %r25, %r12
	xor %r22, %r22, %r11
	and %r22, %r22, %r14
	xor %r27, %r26, %r22
	or %r15, %r15, %r12
	xor %r15, %r15, %r12
	xor %r15, %r22, %r15
	xor %r20, %r20, %r11
	and %r20, %r20, %r24
	or %r15, %r15, %r20
	or %r16, %r16, %r6
	xor %r16, %r16, %r6
	xor %r6, %r2, %r26
	or %r6, %r6, %r16
	xor %r6, %r6, %r16
	xor %r16, %r6, %r11
	and %r25, %r19, %r25
	xor %r16, %r16, %r25
	or %r27, %r27, %r17
	xor %r27, %r27, %r17
	xor %r27, %r27, %r16
	xor %r6, %r24, %r6
	or %r22, %r22, %r6
	xor %r22, %r19, %r22
	xor %r18, %r18, %r22
	xor %r16, %r16, %r18
	or %r23, %r23, %r17
	xor %r23, %r23, %r16
	xor %r19, %r19, %r26
	or %r19, %r15, %r19
	xor %r19, %r18, %r19
	or %r24, %r24, %r16
	xor %r24, %r19, %r24
	or %r16, %r21, %r17
	xor %r16, %r16, %r24
	or %r14, %r14, %r2
	or %r14, %r14, %r19
	xor %r14, %r14, %r19
	and %r21, %r21, %r18
	xor %r14, %r14, %r21
	or %r14, %r14, %r17
	xor %r14, %r14, %r15
	ld %r0, 64(%r10)
	xor %r0, %r0, %r14
	std %r0, 64(%r10)
	ld %r0, 80(%r10)
	xor %r0, %r0, %r27
	std %r0, 80(%r10)
	ld %r0, 464(%r10)
	xor %r0, %r0, %r16
	std %r0, 464(%r10)
	ld %r0, 480(%r10)
	xor %r0, %r0, %r23
	std %r0, 480(%r10)
	rldicr %r12, %r9, 27, 36
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 488(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 26, 37
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 56(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 25, 38
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 120(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 24, 39
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 184(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 23, 40
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 248(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 22, 41
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 312(%r10)
	xor %r18, %r18, %r0
	xor %r6, %r17, %r14
	or %r2, %r18, %r12
	xor %r2, %r2, %r12
	xor %r2, %r2, %r11
	and %r2, %r2, %r14
	or %r19, %r17, %r2
	or %r20, %r6, %r12
	xor %r20, %r20, %r12
	and %r21, %r18, %r6
	xor %r14, %r14, %r21
	or %r21, %r14, %r20
	xor %r21, %r21, %r20
	and %r22, %r16, %r12
	xor %r2, %r2, %r20
	and %r2, %r19, %r2
	or %r20, %r2, %r22
	xor %r20, %r20, %r22
	and %r23, %r16, %r2
	xor %r18, %r18, %r11
	xor %r18, %r23, %r18
	xor %r12, %r12, %r6
	or %r24, %r12, %r22
	xor %r24, %r24, %r22
	xor %r25, %r18, %r24
	xor %r20, %r20, %r11
	and %r20, %r20, %r15
	xor %r20, %r20, %r25
	or %r17, %r17, %r24
	xor %r17, %r17, %r24
	xor %r14, %r14, %r17
	or %r18, %r18, %r14
	xor %r18, %r18, %r14
	xor %r16, %r16, %r12
	xor %r18, %r18, %r16
	or %r24, %r19, %r15
	xor %r24, %r24, %r15
	xor %r24, %r24, %r18
	xor %r23, %r23, %r17
	or %r16, %r16, %r23
	xor %r19, %r19, %r25
	or %r22, %r22, %r19
	xor %r23, %r16, %r22
	xor %r2, %r2, %r25
	xor %r18, %r18, %r2
	and %r22, %r22, %r18
	and %r6, %r6, %r16
	xor %r22, %r22, %r6
	or %r6, %r22, %r15
	xor %r6, %r6, %r23
	or %r22, %r22, %r14
	xor %r22, %r22, %r14
	or %r12, %r12, %r19
	xor %r22, %r22, %r12
	or %r21, %r21, %r15
	xor %r21, %r21, %r22
	ld %r0, 400(%r10)
	xor %r0, %r0, %r21
	std %r0, 400(%r10)
	ld %r0, 432(%r10)
	xor %r0, %r0, %r6
	std %r0, 432(%r10)
	ld %r0, 256(%r10)
	xor %r0, %r0, %r20
	std %r0, 256(%r10)
	ld %r0, 224(%r10)
	xor %r0, %r0, %r24
	std %r0, 224(%r10)
	rldicr %r12, %r9, 33, 30
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 232(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 32, 31
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 296(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 31, 32
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 360(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 30, 33
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 424(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 29, 34
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 488(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 28, 35
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 56(%r10)
	xor %r18, %r18, %r0
	or %r6, %r18, %r17
	xor %r6, %r6, %r17
	xor %r2, %r16, %r12
	or %r19, %r6, %r2
	xor %r20, %r15, %r12
	or %r21, %r20, %r18
	xor %r21, %r21, %r18
	xor %r22, %r19, %r21
	xor %r23, %r17, %r2
	or %r24, %r23, %r12
	xor %r24, %r24, %r12
	xor %r19, %r19, %r24
	or %r24, %r22, %r19
	xor %r24, %r24, %r19
	and %r25, %r12, %r22
	or %r25, %r15, %r25
	and %r25, %r18, %r25
	xor %r25, %r23, %r25
	or %r26, %r22, %r14
	xor %r26, %r26, %r14
	xor %r26, %r26, %r25
	and %r2, %r2, %r20
	xor %r20, %r18, %r15
	xor %r27, %r19, %r20
	or %r27, %r16, %r27
	or %r27, %r27, %r2
	xor %r27, %r27, %r2
	or %r21, %r21, %r20
	or %r20, %r25, %r21
	xor %r20, %r20, %r21
	and %r12, %r15, %r12
	or %r2, %r12, %r17
	xor %r2, %r2, %r17
	xor %r20, %r20, %r2
	and %r19, %r19, %r20
	or %r12, %r23, %r12
	or %r12, %r12, %r19
	xor %r12, %r12, %r19
	xor %r18, %r18, %r12
	and %r27, %r27, %r14
	xor %r27, %r27, %r18
	xor %r22, %r22, %r11
	or %r17, %r17, %r22
	or %r16, %r16, %r17
	xor %r23, %r23, %r16
	xor %r21, %r21, %r23
	xor %r24, %r24, %r11
	and %r24, %r24, %r14
	xor %r24, %r24, %r21
	and %r15, %r15, %r22
	xor %r25, %r25, %r15
	or %r23, %r23, %r25
	xor %r6, %r6, %r18
	xor %r23, %r23, %r6
	or %r20, %r20, %r14
	xor %r20, %r20, %r23
	ld %r0, 176(%r10)
	xor %r0, %r0, %r26
	std %r0, 176(%r10)
	ld %r0, 128(%r10)
	xor %r0, %r0, %r20
	std %r0, 128(%r10)
	ld %r0, 32(%r10)
	xor %r0, %r0, %r27
	std %r0, 32(%r10)
	ld %r0, 16(%r10)
	xor %r0, %r0, %r24
	std %r0, 16(%r10)
	rldicr %r12, %r9, 39, 24
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 472(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 38, 25
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 40(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 37, 26
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 104(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 36, 27
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 168(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 35, 28
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 232(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 34, 29
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 296(%r10)
	xor %r18, %r18, %r0
	xor %r18, %r18, %r16
	xor %r16, %r16, %r14
	or %r6, %r17, %r15
	xor %r6, %r14, %r6
	xor %r6, %r6, %r11
	and %r6, %r6, %r16
	or %r2, %r16, %r17
	xor %r2, %r2, %r17
	xor %r19, %r15, %r2
	or %r20, %r18, %r19
	or %r20, %r20, %r6
	xor %r20, %r20, %r6
	xor %r21, %r17, %r20
	and %r19, %r19, %r21
	or %r16, %r16, %r19
	xor %r16, %r16, %r19
	xor %r18, %r18, %r21
	xor %r16, %r16, %r11
	and %r16, %r16, %r18
	xor %r6, %r6, %r16
	xor %r17, %r17, %r15
	or %r14, %r14, %r2
	xor %r18, %r18, %r14
	or %r14, %r18, %r17
	xor %r14, %r14, %r17
	xor %r20, %r20, %r14
	or %r14, %r12, %r6
	xor %r14, %r14, %r6
	xor %r14, %r14, %r20
	xor %r20, %r20, %r11
	or %r2, %r6, %r12
	xor %r2, %r2, %r12
	xor %r2, %r2, %r20
	xor %r6, %r6, %r20
	or %r6, %r6, %r17
	xor %r6, %r6, %r17
	or %r19, %r19, %r6
	xor %r18, %r18, %r19
	or %r19, %r21, %r12
	xor %r19, %r19, %r18
	and %r12, %r12, %r21
	xor %r12, %r12, %r18
	ld %r0, 496(%r10)
	xor %r0, %r0, %r12
	std %r0, 496(%r10)
	ld %r0, 416(%r10)
	xor %r0, %r0, %r19
	std %r0, 416(%r10)
	ld %r0, 272(%r10)
	xor %r0, %r0, %r2
	std %r0, 272(%r10)
	ld %r0, 384(%r10)
	xor %r0, %r0, %r14
	std %r0, 384(%r10)
	rldicr %r12, %r9, 45, 18
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 216(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 44, 19
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 280(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 43, 20
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 344(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 42, 21
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 408(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 41, 22
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 472(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 40, 23
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 40(%r10)
	xor %r18, %r18, %r0
	or %r6, %r18, %r16
	or %r2, %r6, %r12
	xor %r2, %r2, %r12
	xor %r19, %r18, %r2
	xor %r20, %r16, %r19
	or %r21, %r15, %r20
	or %r2, %r2, %r15
	xor %r2, %r2, %r15
	xor %r16, %r16, %r2
	and %r2, %r14, %r16
	or %r20, %r18, %r20
	xor %r2, %r2, %r20
	xor %r2, %r15, %r2
	xor %r12, %r12, %r2
	or %r22, %r19, %r12
	and %r23, %r14, %r22
	xor %r24, %r19, %r23
	and %r25, %r15, %r20
	xor %r24, %r24, %r25
	or %r22, %r22, %r18
	xor %r22, %r22, %r18
	xor %r25, %r16, %r22
	xor %r14, %r14, %r21
	xor %r25, %r25, %r11
	and %r25, %r25, %r14
	xor %r25, %r25, %r11
	or %r25, %r25, %r17
	xor %r25, %r25, %r17
	xor %r25, %r25, %r2
	or %r2, %r16, %r23
	xor %r2, %r2, %r23
	xor %r22, %r22, %r14
	or %r22, %r24, %r22
	or %r22, %r22, %r2
	xor %r22, %r22, %r2
	or %r2, %r21, %r22
	xor %r2, %r2, %r22
	and %r12, %r12, %r22
	xor %r14, %r14, %r12
	and %r20, %r16, %r20
	or %r20, %r14, %r20
	xor %r23, %r23, %r20
	and %r23, %r23, %r17
	xor %r23, %r23, %r24
	xor %r18, %r18, %r6
	xor %r22, %r22, %r18
	and %r15, %r15, %r14
	xor %r22, %r22, %r15
	or %r2, %r2, %r17
	xor %r2, %r2, %r22
	xor %r16, %r21, %r16
	or %r16, %r16, %r22
	xor %r16, %r16, %r22
	xor %r19, %r19, %r14
	xor %r16, %r16, %r19
	and %r21, %r21, %r17
	xor %r21, %r21, %r16
	ld %r0, 368(%r10)
	xor %r0, %r0, %r23
	std %r0, 368(%r10)
	ld %r0, 448(%r10)
	xor %r0, %r0, %r25
	std %r0, 448(%r10)
	ld %r0, 160(%r10)
	xor %r0, %r0, %r21
	std %r0, 160(%r10)
	ld %r0, 48(%r10)
	xor %r0, %r0, %r2
	std %r0, 48(%r10)
	rldicr %r12, %r9, 51, 12
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 456(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 50, 13
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 24(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 49, 14
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 88(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 48, 15
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 152(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 47, 16
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 216(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 46, 17
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 280(%r10)
	xor %r18, %r18, %r0
	xor %r6, %r17, %r14
	or %r2, %r17, %r12
	and %r2, %r18, %r2
	xor %r6, %r6, %r2
	xor %r19, %r12, %r6
	or %r20, %r14, %r19
	xor %r20, %r20, %r19
	and %r19, %r18, %r19
	xor %r21, %r17, %r19
	xor %r22, %r18, %r16
	or %r23, %r21, %r22
	xor %r24, %r6, %r23
	and %r25, %r16, %r24
	or %r26, %r25, %r12
	xor %r26, %r26, %r12
	or %r21, %r20, %r21
	xor %r27, %r26, %r21
	and %r28, %r27, %r15
	xor %r28, %r28, %r24
	xor %r23, %r17, %r23
	or %r29, %r12, %r23
	xor %r29, %r29, %r23
	xor %r16, %r16, %r29
	or %r29, %r14, %r25
	xor %r29, %r29, %r25
	or %r29, %r16, %r29
	or %r17, %r17, %r22
	xor %r27, %r27, %r17
	or %r2, %r2, %r29
	xor %r27, %r27, %r2
	or %r24, %r18, %r24
	and %r21, %r21, %r24
	xor %r21, %r16, %r21
	xor %r26, %r26, %r11
	and %r26, %r26, %r21
	or %r20, %r20, %r15
	xor %r20, %r20, %r26
	xor %r6, %r6, %r21
	or %r14, %r14, %r6
	xor %r14, %r14, %r6
	xor %r17, %r17, %r11
	xor %r23, %r23, %r17
	xor %r14, %r14, %r23
	or %r14, %r14, %r15
	xor %r14, %r14, %r15
	xor %r14, %r14, %r27
	xor %r12, %r12, %r19
	xor %r18, %r18, %r16
	and %r12, %r12, %r18
	xor %r25, %r25, %r23
	xor %r12, %r12, %r25
	or %r29, %r29, %r15
	xor %r29, %r29, %r15
	xor %r29, %r29, %r12
	ld %r0, 336(%r10)
	xor %r0, %r0, %r28
	std %r0, 336(%r10)
	ld %r0, 352(%r10)
	xor %r0, %r0, %r20
	std %r0, 352(%r10)
	ld %r0, 192(%r10)
	xor %r0, %r0, %r14
	std %r0, 192(%r10)
	ld %r0, 304(%r10)
	xor %r0, %r0, %r29
	std %r0, 304(%r10)
	rldicr %r12, %r9, 57, 6
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 200(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 56, 7
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 264(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 55, 8
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 328(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 54, 9
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 392(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 53, 10
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 456(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 52, 11
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 24(%r10)
	xor %r18, %r18, %r0
	xor %r6, %r15, %r14
	xor %r2, %r16, %r6
	and %r19, %r12, %r2
	and %r20, %r15, %r6
	xor %r21, %r17, %r20
	and %r22, %r19, %r21
	and %r23, %r12, %r20
	xor %r24, %r16, %r23
	or %r25, %r21, %r24
	xor %r6, %r12, %r6
	xor %r26, %r25, %r6
	or %r27, %r18, %r22
	xor %r27, %r27, %r22
	xor %r27, %r27, %r26
	xor %r2, %r2, %r11
	and %r2, %r2, %r14
	or %r26, %r21, %r2
	xor %r24, %r19, %r24
	xor %r26, %r26, %r24
	xor %r19, %r19, %r6
	or %r15, %r15, %r19
	xor %r15, %r15, %r19
	or %r6, %r21, %r15
	xor %r6, %r6, %r15
	xor %r14, %r14, %r24
	xor %r6, %r6, %r14
	or %r19, %r19, %r23
	xor %r19, %r19, %r23
	or %r15, %r15, %r19
	xor %r25, %r17, %r25
	and %r25, %r6, %r25
	xor %r25, %r15, %r25
	and %r23, %r25, %r18
	xor %r23, %r23, %r6
	or %r21, %r21, %r16
	xor %r21, %r21, %r16
	or %r19, %r19, %r21
	or %r20, %r20, %r6
	and %r19, %r19, %r20
	xor %r25, %r25, %r19
	xor %r2, %r2, %r15
	and %r12, %r12, %r2
	or %r22, %r22, %r12
	xor %r19, %r19, %r22
	or %r12, %r19, %r18
	xor %r12, %r12, %r18
	xor %r12, %r12, %r26
	and %r17, %r17, %r22
	xor %r26, %r26, %r11
	xor %r17, %r17, %r26
	xor %r19, %r19, %r17
	or %r25, %r25, %r18
	xor %r25, %r25, %r19
	ld %r0, 112(%r10)
	xor %r0, %r0, %r27
	std %r0, 112(%r10)
	ld %r0, 144(%r10)
	xor %r0, %r0, %r23
	std %r0, 144(%r10)
	ld %r0, 288(%r10)
	xor %r0, %r0, %r25
	std %r0, 288(%r10)
	ld %r0, 0(%r10)
	xor %r0, %r0, %r12
	std %r0, 0(%r10)
	rldicr %r12, %r9, 63, 0
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 504(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 62, 1
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 8(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 61, 2
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 72(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 60, 3
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 136(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 59, 4
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 200(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 58, 5
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 264(%r10)
	xor %r18, %r18, %r0
	or %r6, %r16, %r17
	xor %r6, %r6, %r17
	or %r2, %r14, %r16
	xor %r2, %r2, %r16
	xor %r2, %r15, %r2
	and %r19, %r18, %r2
	or %r20, %r19, %r6
	xor %r20, %r20, %r6
	or %r21, %r17, %r2
	xor %r21, %r21, %r2
	or %r22, %r18, %r21
	or %r23, %r17, %r16
	xor %r23, %r23, %r16
	xor %r23, %r14, %r23
	and %r24, %r22, %r23
	or %r19, %r19, %r24
	xor %r2, %r2, %r11
	xor %r24, %r24, %r2
	or %r16, %r16, %r22
	xor %r16, %r16, %r22
	xor %r24, %r24, %r16
	xor %r6, %r6, %r24
	or %r16, %r20, %r12
	xor %r16, %r16, %r6
	xor %r6, %r18, %r6
	and %r22, %r14, %r6
	xor %r24, %r17, %r24
	xor %r22, %r22, %r24
	xor %r21, %r21, %r22
	xor %r22, %r19, %r22
	or %r17, %r17, %r22
	xor %r14, %r14, %r6
	xor %r17, %r17, %r14
	and %r19, %r19, %r12
	xor %r19, %r19, %r17
	xor %r23, %r23, %r21
	or %r24, %r15, %r24
	xor %r24, %r23, %r24
	xor %r18, %r18, %r24
	and %r18, %r18, %r12
	xor %r18, %r18, %r21
	or %r23, %r23, %r15
	xor %r23, %r23, %r15
	and %r17, %r17, %r23
	xor %r20, %r20, %r24
	xor %r17, %r17, %r20
	or %r17, %r17, %r12
	xor %r17, %r17, %r21
	ld %r0, 208(%r10)
	xor %r0, %r0, %r18
	std %r0, 208(%r10)
	ld %r0, 96(%r10)
	xor %r0, %r0, %r19
	std %r0, 96(%r10)
	ld %r0, 320(%r10)
	xor %r0, %r0, %r16
	std %r0, 320(%r10)
	ld %r0, 240(%r10)
	xor %r0, %r0, %r17
	std %r0, 240(%r10)
	ld %r9, 0(%r3)
	xor %r9, %r9, %r11
	addi %r3, %r3, -8
	rldicr %r12, %r9, 21, 42
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 240(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 20, 43
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 304(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 19, 44
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 368(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 18, 45
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 432(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 17, 46
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 496(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 16, 47
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 0(%r10)
	xor %r18, %r18, %r0
	or %r6, %r18, %r14
	xor %r6, %r6, %r14
	xor %r2, %r15, %r6
	or %r19, %r16, %r12
	xor %r20, %r18, %r16
	and %r21, %r19, %r20
	xor %r22, %r15, %r21
	or %r23, %r22, %r2
	xor %r23, %r23, %r2
	xor %r24, %r14, %r12
	xor %r25, %r16, %r24
	xor %r25, %r25, %r11
	and %r25, %r25, %r2
	or %r21, %r12, %r21
	xor %r25, %r25, %r21
	or %r21, %r25, %r23
	xor %r21, %r21, %r23
	or %r12, %r18, %r12
	or %r26, %r25, %r12
	xor %r22, %r22, %r11
	and %r22, %r22, %r14
	xor %r27, %r26, %r22
	or %r15, %r15, %r12
	xor %r15, %r15, %r12
	xor %r15, %r22, %r15
	xor %r20, %r20, %r11
	and %r20, %r20, %r24
	or %r15, %r15, %r20
	or %r16, %r16, %r6
	xor %r16, %r16, %r6
	xor %r6, %r2, %r26
	or %r6, %r6, %r16
	xor %r6, %r6, %r16
	xor %r16, %r6, %r11
	and %r25, %r19, %r25
	xor %r16, %r16, %r25
	or %r27, %r27, %r17
	xor %r27, %r27, %r17
	xor %r27, %r27, %r16
	xor %r6, %r24, %r6
	or %r22, %r22, %r6
	xor %r22, %r19, %r22
	xor %r18, %r18, %r22
	xor %r16, %r16, %r18
	or %r23, %r23, %r17
	xor %r23, %r23, %r16
	xor %r19, %r19, %r26
	or %r19, %r15, %r19
	xor %r19, %r18, %r19
	or %r24, %r24, %r16
	xor %r24, %r19, %r24
	or %r16, %r21, %r17
	xor %r16, %r16, %r24
	or %r14, %r14, %r2
	or %r14, %r14, %r19
	xor %r14, %r14, %r19
	and %r21, %r21, %r18
	xor %r14, %r14, %r21
	or %r14, %r14, %r17
	xor %r14, %r14, %r15
	ld %r0, 72(%r10)
	xor %r0, %r0, %r14
	std %r0, 72(%r10)
	ld %r0, 88(%r10)
	xor %r0, %r0, %r27
	std %r0, 88(%r10)
	ld %r0, 472(%r10)
	xor %r0, %r0, %r16
	std %r0, 472(%r10)
	ld %r0, 488(%r10)
	xor %r0, %r0, %r23
	std %r0, 488(%r10)
	rldicr %r12, %r9, 27, 36
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 480(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 26, 37
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 48(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 25, 38
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 112(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 24, 39
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 176(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 23, 40
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 240(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 22, 41
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 304(%r10)
	xor %r18, %r18, %r0
	xor %r6, %r17, %r14
	or %r2, %r18, %r12
	xor %r2, %r2, %r12
	xor %r2, %r2, %r11
	and %r2, %r2, %r14
	or %r19, %r17, %r2
	or %r20, %r6, %r12
	xor %r20, %r20, %r12
	and %r21, %r18, %r6
	xor %r14, %r14, %r21
	or %r21, %r14, %r20
	xor %r21, %r21, %r20
	and %r22, %r16, %r12
	xor %r2, %r2, %r20
	and %r2, %r19, %r2
	or %r20, %r2, %r22
	xor %r20, %r20, %r22
	and %r23, %r16, %r2
	xor %r18, %r18, %r11
	xor %r18, %r23, %r18
	xor %r12, %r12, %r6
	or %r24, %r12, %r22
	xor %r24, %r24, %r22
	xor %r25, %r18, %r24
	xor %r20, %r20, %r11
	and %r20, %r20, %r15
	xor %r20, %r20, %r25
	or %r17, %r17, %r24
	xor %r17, %r17, %r24
	xor %r14, %r14, %r17
	or %r18, %r18, %r14
	xor %r18, %r18, %r14
	xor %r16, %r16, %r12
	xor %r18, %r18, %r16
	or %r24, %r19, %r15
	xor %r24, %r24, %r15
	xor %r24, %r24, %r18
	xor %r23, %r23, %r17
	or %r16, %r16, %r23
	xor %r19, %r19, %r25
	or %r22, %r22, %r19
	xor %r23, %r16, %r22
	xor %r2, %r2, %r25
	xor %r18, %r18, %r2
	and %r22, %r22, %r18
	and %r6, %r6, %r16
	xor %r22, %r22, %r6
	or %r6, %r22, %r15
	xor %r6, %r6, %r23
	or %r22, %r22, %r14
	xor %r22, %r22, %r14
	or %r12, %r12, %r19
	xor %r22, %r22, %r12
	or %r21, %r21, %r15
	xor %r21, %r21, %r22
	ld %r0, 408(%r10)
	xor %r0, %r0, %r21
	std %r0, 408(%r10)
	ld %r0, 440(%r10)
	xor %r0, %r0, %r6
	std %r0, 440(%r10)
	ld %r0, 264(%r10)
	xor %r0, %r0, %r20
	std %r0, 264(%r10)
	ld %r0, 232(%r10)
	xor %r0, %r0, %r24
	std %r0, 232(%r10)
	rldicr %r12, %r9, 33, 30
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 224(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 32, 31
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 288(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 31, 32
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 352(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 30, 33
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 416(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 29, 34
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 480(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 28, 35
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 48(%r10)
	xor %r18, %r18, %r0
	or %r6, %r18, %r17
	xor %r6, %r6, %r17
	xor %r2, %r16, %r12
	or %r19, %r6, %r2
	xor %r20, %r15, %r12
	or %r21, %r20, %r18
	xor %r21, %r21, %r18
	xor %r22, %r19, %r21
	xor %r23, %r17, %r2
	or %r24, %r23, %r12
	xor %r24, %r24, %r12
	xor %r19, %r19, %r24
	or %r24, %r22, %r19
	xor %r24, %r24, %r19
	and %r25, %r12, %r22
	or %r25, %r15, %r25
	and %r25, %r18, %r25
	xor %r25, %r23, %r25
	or %r26, %r22, %r14
	xor %r26, %r26, %r14
	xor %r26, %r26, %r25
	and %r2, %r2, %r20
	xor %r20, %r18, %r15
	xor %r27, %r19, %r20
	or %r27, %r16, %r27
	or %r27, %r27, %r2
	xor %r27, %r27, %r2
	or %r21, %r21, %r20
	or %r20, %r25, %r21
	xor %r20, %r20, %r21
	and %r12, %r15, %r12
	or %r2, %r12, %r17
	xor %r2, %r2, %r17
	xor %r20, %r20, %r2
	and %r19, %r19, %r20
	or %r12, %r23, %r12
	or %r12, %r12, %r19
	xor %r12, %r12, %r19
	xor %r18, %r18, %r12
	and %r27, %r27, %r14
	xor %r27, %r27, %r18
	xor %r22, %r22, %r11
	or %r17, %r17, %r22
	or %r16, %r16, %r17
	xor %r23, %r23, %r16
	xor %r21, %r21, %r23
	xor %r24, %r24, %r11
	and %r24, %r24, %r14
	xor %r24, %r24, %r21
	and %r15, %r15, %r22
	xor %r25, %r25, %r15
	or %r23, %r23, %r25
	xor %r6, %r6, %r18
	xor %r23, %r23, %r6
	or %r20, %r20, %r14
	xor %r20, %r20, %r23
	ld %r0, 184(%r10)
	xor %r0, %r0, %r26
	std %r0, 184(%r10)
	ld %r0, 136(%r10)
	xor %r0, %r0, %r20
	std %r0, 136(%r10)
	ld %r0, 40(%r10)
	xor %r0, %r0, %r27
	std %r0, 40(%r10)
	ld %r0, 24(%r10)
	xor %r0, %r0, %r24
	std %r0, 24(%r10)
	rldicr %r12, %r9, 39, 24
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 464(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 38, 25
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 32(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 37, 26
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 96(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 36, 27
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 160(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 35, 28
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 224(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 34, 29
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 288(%r10)
	xor %r18, %r18, %r0
	xor %r18, %r18, %r16
	xor %r16, %r16, %r14
	or %r6, %r17, %r15
	xor %r6, %r14, %r6
	xor %r6, %r6, %r11
	and %r6, %r6, %r16
	or %r2, %r16, %r17
	xor %r2, %r2, %r17
	xor %r19, %r15, %r2
	or %r20, %r18, %r19
	or %r20, %r20, %r6
	xor %r20, %r20, %r6
	xor %r21, %r17, %r20
	and %r19, %r19, %r21
	or %r16, %r16, %r19
	xor %r16, %r16, %r19
	xor %r18, %r18, %r21
	xor %r16, %r16, %r11
	and %r16, %r16, %r18
	xor %r6, %r6, %r16
	xor %r17, %r17, %r15
	or %r14, %r14, %r2
	xor %r18, %r18, %r14
	or %r14, %r18, %r17
	xor %r14, %r14, %r17
	xor %r20, %r20, %r14
	or %r14, %r12, %r6
	xor %r14, %r14, %r6
	xor %r14, %r14, %r20
	xor %r20, %r20, %r11
	or %r2, %r6, %r12
	xor %r2, %r2, %r12
	xor %r2, %r2, %r20
	xor %r6, %r6, %r20
	or %r6, %r6, %r17
	xor %r6, %r6, %r17
	or %r19, %r19, %r6
	xor %r18, %r18, %r19
	or %r19, %r21, %r12
	xor %r19, %r19, %r18
	and %r12, %r12, %r21
	xor %r12, %r12, %r18
	ld %r0, 504(%r10)
	xor %r0, %r0, %r12
	std %r0, 504(%r10)
	ld %r0, 424(%r10)
	xor %r0, %r0, %r19
	std %r0, 424(%r10)
	ld %r0, 280(%r10)
	xor %r0, %r0, %r2
	std %r0, 280(%r10)
	ld %r0, 392(%r10)
	xor %r0, %r0, %r14
	std %r0, 392(%r10)
	rldicr %r12, %r9, 45, 18
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 208(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 44, 19
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 272(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 43, 20
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 336(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 42, 21
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 400(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 41, 22
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 464(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 40, 23
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 32(%r10)
	xor %r18, %r18, %r0
	or %r6, %r18, %r16
	or %r2, %r6, %r12
	xor %r2, %r2, %r12
	xor %r19, %r18, %r2
	xor %r20, %r16, %r19
	or %r21, %r15, %r20
	or %r2, %r2, %r15
	xor %r2, %r2, %r15
	xor %r16, %r16, %r2
	and %r2, %r14, %r16
	or %r20, %r18, %r20
	xor %r2, %r2, %r20
	xor %r2, %r15, %r2
	xor %r12, %r12, %r2
	or %r22, %r19, %r12
	and %r23, %r14, %r22
	xor %r24, %r19, %r23
	and %r25, %r15, %r20
	xor %r24, %r24, %r25
	or %r22, %r22, %r18
	xor %r22, %r22, %r18
	xor %r25, %r16, %r22
	xor %r14, %r14, %r21
	xor %r25, %r25, %r11
	and %r25, %r25, %r14
	xor %r25, %r25, %r11
	or %r25, %r25, %r17
	xor %r25, %r25, %r17
	xor %r25, %r25, %r2
	or %r2, %r16, %r23
	xor %r2, %r2, %r23
	xor %r22, %r22, %r14
	or %r22, %r24, %r22
	or %r22, %r22, %r2
	xor %r22, %r22, %r2
	or %r2, %r21, %r22
	xor %r2, %r2, %r22
	and %r12, %r12, %r22
	xor %r14, %r14, %r12
	and %r20, %r16, %r20
	or %r20, %r14, %r20
	xor %r23, %r23, %r20
	and %r23, %r23, %r17
	xor %r23, %r23, %r24
	xor %r18, %r18, %r6
	xor %r22, %r22, %r18
	and %r15, %r15, %r14
	xor %r22, %r22, %r15
	or %r2, %r2, %r17
	xor %r2, %r2, %r22
	xor %r16, %r21, %r16
	or %r16, %r16, %r22
	xor %r16, %r16, %r22
	xor %r19, %r19, %r14
	xor %r16, %r16, %r19
	and %r21, %r21, %r17
	xor %r21, %r21, %r16
	ld %r0, 376(%r10)
	xor %r0, %r0, %r23
	std %r0, 376(%r10)
	ld %r0, 456(%r10)
	xor %r0, %r0, %r25
	std %r0, 456(%r10)
	ld %r0, 168(%r10)
	xor %r0, %r0, %r21
	std %r0, 168(%r10)
	ld %r0, 56(%r10)
	xor %r0, %r0, %r2
	std %r0, 56(%r10)
	rldicr %r12, %r9, 51, 12
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 448(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 50, 13
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 16(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 49, 14
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 80(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 48, 15
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 144(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 47, 16
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 208(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 46, 17
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 272(%r10)
	xor %r18, %r18, %r0
	xor %r6, %r17, %r14
	or %r2, %r17, %r12
	and %r2, %r18, %r2
	xor %r6, %r6, %r2
	xor %r19, %r12, %r6
	or %r20, %r14, %r19
	xor %r20, %r20, %r19
	and %r19, %r18, %r19
	xor %r21, %r17, %r19
	xor %r22, %r18, %r16
	or %r23, %r21, %r22
	xor %r24, %r6, %r23
	and %r25, %r16, %r24
	or %r26, %r25, %r12
	xor %r26, %r26, %r12
	or %r21, %r20, %r21
	xor %r27, %r26, %r21
	and %r28, %r27, %r15
	xor %r28, %r28, %r24
	xor %r23, %r17, %r23
	or %r29, %r12, %r23
	xor %r29, %r29, %r23
	xor %r16, %r16, %r29
	or %r29, %r14, %r25
	xor %r29, %r29, %r25
	or %r29, %r16, %r29
	or %r17, %r17, %r22
	xor %r27, %r27, %r17
	or %r2, %r2, %r29
	xor %r27, %r27, %r2
	or %r24, %r18, %r24
	and %r21, %r21, %r24
	xor %r21, %r16, %r21
	xor %r26, %r26, %r11
	and %r26, %r26, %r21
	or %r20, %r20, %r15
	xor %r20, %r20, %r26
	xor %r6, %r6, %r21
	or %r14, %r14, %r6
	xor %r14, %r14, %r6
	xor %r17, %r17, %r11
	xor %r23, %r23, %r17
	xor %r14, %r14, %r23
	or %r14, %r14, %r15
	xor %r14, %r14, %r15
	xor %r14, %r14, %r27
	xor %r12, %r12, %r19
	xor %r18, %r18, %r16
	and %r12, %r12, %r18
	xor %r25, %r25, %r23
	xor %r12, %r12, %r25
	or %r29, %r29, %r15
	xor %r29, %r29, %r15
	xor %r29, %r29, %r12
	ld %r0, 344(%r10)
	xor %r0, %r0, %r28
	std %r0, 344(%r10)
	ld %r0, 360(%r10)
	xor %r0, %r0, %r20
	std %r0, 360(%r10)
	ld %r0, 200(%r10)
	xor %r0, %r0, %r14
	std %r0, 200(%r10)
	ld %r0, 312(%r10)
	xor %r0, %r0, %r29
	std %r0, 312(%r10)
	rldicr %r12, %r9, 57, 6
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 192(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 56, 7
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 256(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 55, 8
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 320(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 54, 9
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 384(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 53, 10
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 448(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 52, 11
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 16(%r10)
	xor %r18, %r18, %r0
	xor %r6, %r15, %r14
	xor %r2, %r16, %r6
	and %r19, %r12, %r2
	and %r20, %r15, %r6
	xor %r21, %r17, %r20
	and %r22, %r19, %r21
	and %r23, %r12, %r20
	xor %r24, %r16, %r23
	or %r25, %r21, %r24
	xor %r6, %r12, %r6
	xor %r26, %r25, %r6
	or %r27, %r18, %r22
	xor %r27, %r27, %r22
	xor %r27, %r27, %r26
	xor %r2, %r2, %r11
	and %r2, %r2, %r14
	or %r26, %r21, %r2
	xor %r24, %r19, %r24
	xor %r26, %r26, %r24
	xor %r19, %r19, %r6
	or %r15, %r15, %r19
	xor %r15, %r15, %r19
	or %r6, %r21, %r15
	xor %r6, %r6, %r15
	xor %r14, %r14, %r24
	xor %r6, %r6, %r14
	or %r19, %r19, %r23
	xor %r19, %r19, %r23
	or %r15, %r15, %r19
	xor %r25, %r17, %r25
	and %r25, %r6, %r25
	xor %r25, %r15, %r25
	and %r23, %r25, %r18
	xor %r23, %r23, %r6
	or %r21, %r21, %r16
	xor %r21, %r21, %r16
	or %r19, %r19, %r21
	or %r20, %r20, %r6
	and %r19, %r19, %r20
	xor %r25, %r25, %r19
	xor %r2, %r2, %r15
	and %r12, %r12, %r2
	or %r22, %r22, %r12
	xor %r19, %r19, %r22
	or %r12, %r19, %r18
	xor %r12, %r12, %r18
	xor %r12, %r12, %r26
	and %r17, %r17, %r22
	xor %r26, %r26, %r11
	xor %r17, %r17, %r26
	xor %r19, %r19, %r17
	or %r25, %r25, %r18
	xor %r25, %r25, %r19
	ld %r0, 120(%r10)
	xor %r0, %r0, %r27
	std %r0, 120(%r10)
	ld %r0, 152(%r10)
	xor %r0, %r0, %r23
	std %r0, 152(%r10)
	ld %r0, 296(%r10)
	xor %r0, %r0, %r25
	std %r0, 296(%r10)
	ld %r0, 8(%r10)
	xor %r0, %r0, %r12
	std %r0, 8(%r10)
	rldicr %r12, %r9, 63, 0
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 496(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 62, 1
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 0(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 61, 2
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 64(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 60, 3
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 128(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 59, 4
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 192(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 58, 5
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 256(%r10)
	xor %r18, %r18, %r0
	or %r6, %r16, %r17
	xor %r6, %r6, %r17
	or %r2, %r14, %r16
	xor %r2, %r2, %r16
	xor %r2, %r15, %r2
	and %r19, %r18, %r2
	or %r20, %r19, %r6
	xor %r20, %r20, %r6
	or %r21, %r17, %r2
	xor %r21, %r21, %r2
	or %r22, %r18, %r21
	or %r23, %r17, %r16
	xor %r23, %r23, %r16
	xor %r23, %r14, %r23
	and %r24, %r22, %r23
	or %r19, %r19, %r24
	xor %r2, %r2, %r11
	xor %r24, %r24, %r2
	or %r16, %r16, %r22
	xor %r16, %r16, %r22
	xor %r24, %r24, %r16
	xor %r6, %r6, %r24
	or %r16, %r20, %r12
	xor %r16, %r16, %r6
	xor %r6, %r18, %r6
	and %r22, %r14, %r6
	xor %r24, %r17, %r24
	xor %r22, %r22, %r24
	xor %r21, %r21, %r22
	xor %r22, %r19, %r22
	or %r17, %r17, %r22
	xor %r14, %r14, %r6
	xor %r17, %r17, %r14
	and %r19, %r19, %r12
	xor %r19, %r19, %r17
	xor %r23, %r23, %r21
	or %r24, %r15, %r24
	xor %r24, %r23, %r24
	xor %r18, %r18, %r24
	and %r18, %r18, %r12
	xor %r18, %r18, %r21
	or %r23, %r23, %r15
	xor %r23, %r23, %r15
	and %r17, %r17, %r23
	xor %r20, %r20, %r24
	xor %r17, %r17, %r20
	or %r17, %r17, %r12
	xor %r17, %r17, %r21
	ld %r0, 216(%r10)
	xor %r0, %r0, %r18
	std %r0, 216(%r10)
	ld %r0, 104(%r10)
	xor %r0, %r0, %r19
	std %r0, 104(%r10)
	ld %r0, 328(%r10)
	xor %r0, %r0, %r16
	std %r0, 328(%r10)
	ld %r0, 248(%r10)
	xor %r0, %r0, %r17
	std %r0, 248(%r10)
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 26b
	ld %r12, 0(%r10)
	ld %r14, 8(%r10)
	std %r14, 0(%r10)
	std %r12, 8(%r10)
	ld %r12, 64(%r10)
	ld %r14, 72(%r10)
	std %r14, 64(%r10)
	std %r12, 72(%r10)
	ld %r12, 128(%r10)
	ld %r14, 136(%r10)
	std %r14, 128(%r10)
	std %r12, 136(%r10)
	ld %r12, 192(%r10)
	ld %r14, 200(%r10)
	std %r14, 192(%r10)
	std %r12, 200(%r10)
	ld %r12, 256(%r10)
	ld %r14, 264(%r10)
	std %r14, 256(%r10)
	std %r12, 264(%r10)
	ld %r12, 320(%r10)
	ld %r14, 328(%r10)
	std %r14, 320(%r10)
	std %r12, 328(%r10)
	ld %r12, 384(%r10)
	ld %r14, 392(%r10)
	std %r14, 384(%r10)
	std %r12, 392(%r10)
	ld %r12, 448(%r10)
	ld %r14, 456(%r10)
	std %r14, 448(%r10)
	std %r12, 456(%r10)
	ld %r12, 16(%r10)
	ld %r14, 24(%r10)
	std %r14, 16(%r10)
	std %r12, 24(%r10)
	ld %r12, 80(%r10)
	ld %r14, 88(%r10)
	std %r14, 80(%r10)
	std %r12, 88(%r10)
	ld %r12, 144(%r10)
	ld %r14, 152(%r10)
	std %r14, 144(%r10)
	std %r12, 152(%r10)
	ld %r12, 208(%r10)
	ld %r14, 216(%r10)
	std %r14, 208(%r10)
	std %r12, 216(%r10)
	ld %r12, 272(%r10)
	ld %r14, 280(%r10)
	std %r14, 272(%r10)
	std %r12, 280(%r10)
	ld %r12, 336(%r10)
	ld %r14, 344(%r10)
	std %r14, 336(%r10)
	std %r12, 344(%r10)
	ld %r12, 400(%r10)
	ld %r14, 408(%r10)
	std %r14, 400(%r10)
	std %r12, 408(%r10)
	ld %r12, 464(%r10)
	ld %r14, 472(%r10)
	std %r14, 464(%r10)
	std %r12, 472(%r10)
	ld %r12, 32(%r10)
	ld %r14, 40(%r10)
	std %r14, 32(%r10)
	std %r12, 40(%r10)
	ld %r12, 96(%r10)
	ld %r14, 104(%r10)
	std %r14, 96(%r10)
	std %r12, 104(%r10)
	ld %r12, 160(%r10)
	ld %r14, 168(%r10)
	std %r14, 160(%r10)
	std %r12, 168(%r10)
	ld %r12, 224(%r10)
	ld %r14, 232(%r10)
	std %r14, 224(%r10)
	std %r12, 232(%r10)
	ld %r12, 288(%r10)
	ld %r14, 296(%r10)
	std %r14, 288(%r10)
	std %r12, 296(%r10)
	ld %r12, 352(%r10)
	ld %r14, 360(%r10)
	std %r14, 352(%r10)
	std %r12, 360(%r10)
	ld %r12, 416(%r10)
	ld %r14, 424(%r10)
	std %r14, 416(%r10)
	std %r12, 424(%r10)
	ld %r12, 480(%r10)
	ld %r14, 488(%r10)
	std %r14, 480(%r10)
	std %r12, 488(%r10)
	ld %r12, 48(%r10)
	ld %r14, 56(%r10)
	std %r14, 48(%r10)
	std %r12, 56(%r10)
	ld %r12, 112(%r10)
	ld %r14, 120(%r10)
	std %r14, 112(%r10)
	std %r12, 120(%r10)
	ld %r12, 176(%r10)
	ld %r14, 184(%r10)
	std %r14, 176(%r10)
	std %r12, 184(%r10)
	ld %r12, 240(%r10)
	ld %r14, 248(%r10)
	std %r14, 240(%r10)
	std %r12, 248(%r10)
	ld %r12, 304(%r10)
	ld %r14, 312(%r10)
	std %r14, 304(%r10)
	std %r12, 312(%r10)
	ld %r12, 368(%r10)
	ld %r14, 376(%r10)
	std %r14, 368(%r10)
	std %r12, 376(%r10)
	ld %r12, 432(%r10)
	ld %r14, 440(%r10)
	std %r14, 432(%r10)
	std %r12, 440(%r10)
	ld %r12, 496(%r10)
	ld %r14, 504(%r10)
	std %r14, 496(%r10)
	std %r12, 504(%r10)
	addi %r3, %r7, 128
	li %r5, 8
27:
	ld %r9, 0(%r3)
	xor %r9, %r9, %r11
	addi %r3, %r3, 8
	rldicr %r12, %r9, 21, 42
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 248(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 20, 43
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 312(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 19, 44
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 376(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 18, 45
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 440(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 17, 46
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 504(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 16, 47
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 8(%r10)
	xor %r18, %r18, %r0
	or %r6, %r18, %r14
	xor %r6, %r6, %r14
	xor %r2, %r15, %r6
	or %r19, %r16, %r12
	xor %r20, %r18, %r16
	and %r21, %r19, %r20
	xor %r22, %r15, %r21
	or %r23, %r22, %r2
	xor %r23, %r23, %r2
	xor %r24, %r14, %r12
	xor %r25, %r16, %r24
	xor %r25, %r25, %r11
	and %r25, %r25, %r2
	or %r21, %r12, %r21
	xor %r25, %r25, %r21
	or %r21, %r25, %r23
	xor %r21, %r21, %r23
	or %r12, %r18, %r12
	or %r26, %r25, %r12
	xor %r22, %r22, %r11
	and %r22, %r22, %r14
	xor %r27, %r26, %r22
	or %r15, %r15, %r12
	xor %r15, %r15, %r12
	xor %r15, %r22, %r15
	xor %r20, %r20, %r11
	and %r20, %r20, %r24
	or %r15, %r15, %r20
	or %r16, %r16, %r6
	xor %r16, %r16, %r6
	xor %r6, %r2, %r26
	or %r6, %r6, %r16
	xor %r6, %r6, %r16
	xor %r16, %r6, %r11
	and %r25, %r19, %r25
	xor %r16, %r16, %r25
	or %r27, %r27, %r17
	xor %r27, %r27, %r17
	xor %r27, %r27, %r16
	xor %r6, %r24, %r6
	or %r22, %r22, %r6
	xor %r22, %r19, %r22
	xor %r18, %r18, %r22
	xor %r16, %r16, %r18
	or %r23, %r23, %r17
	xor %r23, %r23, %r16
	xor %r19, %r19, %r26
	or %r19, %r15, %r19
	xor %r19, %r18, %r19
	or %r24, %r24, %r16
	xor %r24, %r19, %r24
	or %r16, %r21, %r17
	xor %r16, %r16, %r24
	or %r14, %r14, %r2
	or %r14, %r14, %r19
	xor %r14, %r14, %r19
	and %r21, %r21, %r18
	xor %r14, %r14, %r21
	or %r14, %r14, %r17
	xor %r14, %r14, %r15
	ld %r0, 64(%r10)
	xor %r0, %r0, %r14
	std %r0, 64(%r10)
	ld %r0, 80(%r10)
	xor %r0, %r0, %r27
	std %r0, 80(%r10)
	ld %r0, 464(%r10)
	xor %r0, %r0, %r16
	std %r0, 464(%r10)
	ld %r0, 480(%r10)
	xor %r0, %r0, %r23
	std %r0, 480(%r10)
	rldicr %r12, %r9, 27, 36
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 488(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 26, 37
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 56(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 25, 38
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 120(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 24, 39
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 184(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 23, 40
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 248(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 22, 41
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 312(%r10)
	xor %r18, %r18, %r0
	xor %r6, %r17, %r14
	or %r2, %r18, %r12
	xor %r2, %r2, %r12
	xor %r2, %r2, %r11
	and %r2, %r2, %r14
	or %r19, %r17, %r2
	or %r20, %r6, %r12
	xor %r20, %r20, %r12
	and %r21, %r18, %r6
	xor %r14, %r14, %r21
	or %r21, %r14, %r20
	xor %r21, %r21, %r20
	and %r22, %r16, %r12
	xor %r2, %r2, %r20
	and %r2, %r19, %r2
	or %r20, %r2, %r22
	xor %r20, %r20, %r22
	and %r23, %r16, %r2
	xor %r18, %r18, %r11
	xor %r18, %r23, %r18
	xor %r12, %r12, %r6
	or %r24, %r12, %r22
	xor %r24, %r24, %r22
	xor %r25, %r18, %r24
	xor %r20, %r20, %r11
	and %r20, %r20, %r15
	xor %r20, %r20, %r25
	or %r17, %r17, %r24
	xor %r17, %r17, %r24
	xor %r14, %r14, %r17
	or %r18, %r18, %r14
	xor %r18, %r18, %r14
	xor %r16, %r16, %r12
	xor %r18, %r18, %r16
	or %r24, %r19, %r15
	xor %r24, %r24, %r15
	xor %r24, %r24, %r18
	xor %r23, %r23, %r17
	or %r16, %r16, %r23
	xor %r19, %r19, %r25
	or %r22, %r22, %r19
	xor %r23, %r16, %r22
	xor %r2, %r2, %r25
	xor %r18, %r18, %r2
	and %r22, %r22, %r18
	and %r6, %r6, %r16
	xor %r22, %r22, %r6
	or %r6, %r22, %r15
	xor %r6, %r6, %r23
	or %r22, %r22, %r14
	xor %r22, %r22, %r14
	or %r12, %r12, %r19
	xor %r22, %r22, %r12
	or %r21, %r21, %r15
	xor %r21, %r21, %r22
	ld %r0, 400(%r10)
	xor %r0, %r0, %r21
	std %r0, 400(%r10)
	ld %r0, 432(%r10)
	xor %r0, %r0, %r6
	std %r0, 432(%r10)
	ld %r0, 256(%r10)
	xor %r0, %r0, %r20
	std %r0, 256(%r10)
	ld %r0, 224(%r10)
	xor %r0, %r0, %r24
	std %r0, 224(%r10)
	rldicr %r12, %r9, 33, 30
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 232(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 32, 31
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 296(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 31, 32
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 360(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 30, 33
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 424(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 29, 34
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 488(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 28, 35
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 56(%r10)
	xor %r18, %r18, %r0
	or %r6, %r18, %r17
	xor %r6, %r6, %r17
	xor %r2, %r16, %r12
	or %r19, %r6, %r2
	xor %r20, %r15, %r12
	or %r21, %r20, %r18
	xor %r21, %r21, %r18
	xor %r22, %r19, %r21
	xor %r23, %r17, %r2
	or %r24, %r23, %r12
	xor %r24, %r24, %r12
	xor %r19, %r19, %r24
	or %r24, %r22, %r19
	xor %r24, %r24, %r19
	and %r25, %r12, %r22
	or %r25, %r15, %r25
	and %r25, %r18, %r25
	xor %r25, %r23, %r25
	or %r26, %r22, %r14
	xor %r26, %r26, %r14
	xor %r26, %r26, %r25
	and %r2, %r2, %r20
	xor %r20, %r18, %r15
	xor %r27, %r19, %r20
	or %r27, %r16, %r27
	or %r27, %r27, %r2
	xor %r27, %r27, %r2
	or %r21, %r21, %r20
	or %r20, %r25, %r21
	xor %r20, %r20, %r21
	and %r12, %r15, %r12
	or %r2, %r12, %r17
	xor %r2, %r2, %r17
	xor %r20, %r20, %r2
	and %r19, %r19, %r20
	or %r12, %r23, %r12
	or %r12, %r12, %r19
	xor %r12, %r12, %r19
	xor %r18, %r18, %r12
	and %r27, %r27, %r14
	xor %r27, %r27, %r18
	xor %r22, %r22, %r11
	or %r17, %r17, %r22
	or %r16, %r16, %r17
	xor %r23, %r23, %r16
	xor %r21, %r21, %r23
	xor %r24, %r24, %r11
	and %r24, %r24, %r14
	xor %r24, %r24, %r21
	and %r15, %r15, %r22
	xor %r25, %r25, %r15
	or %r23, %r23, %r25
	xor %r6, %r6, %r18
	xor %r23, %r23, %r6
	or %r20, %r20, %r14
	xor %r20, %r20, %r23
	ld %r0, 176(%r10)
	xor %r0, %r0, %r26
	std %r0, 176(%r10)
	ld %r0, 128(%r10)
	xor %r0, %r0, %r20
	std %r0, 128(%r10)
	ld %r0, 32(%r10)
	xor %r0, %r0, %r27
	std %r0, 32(%r10)
	ld %r0, 16(%r10)
	xor %r0, %r0, %r24
	std %r0, 16(%r10)
	rldicr %r12, %r9, 39, 24
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 472(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 38, 25
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 40(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 37, 26
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 104(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 36, 27
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 168(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 35, 28
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 232(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 34, 29
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 296(%r10)
	xor %r18, %r18, %r0
	xor %r18, %r18, %r16
	xor %r16, %r16, %r14
	or %r6, %r17, %r15
	xor %r6, %r14, %r6
	xor %r6, %r6, %r11
	and %r6, %r6, %r16
	or %r2, %r16, %r17
	xor %r2, %r2, %r17
	xor %r19, %r15, %r2
	or %r20, %r18, %r19
	or %r20, %r20, %r6
	xor %r20, %r20, %r6
	xor %r21, %r17, %r20
	and %r19, %r19, %r21
	or %r16, %r16, %r19
	xor %r16, %r16, %r19
	xor %r18, %r18, %r21
	xor %r16, %r16, %r11
	and %r16, %r16, %r18
	xor %r6, %r6, %r16
	xor %r17, %r17, %r15
	or %r14, %r14, %r2
	xor %r18, %r18, %r14
	or %r14, %r18, %r17
	xor %r14, %r14, %r17
	xor %r20, %r20, %r14
	or %r14, %r12, %r6
	xor %r14, %r14, %r6
	xor %r14, %r14, %r20
	xor %r20, %r20, %r11
	or %r2, %r6, %r12
	xor %r2, %r2, %r12
	xor %r2, %r2, %r20
	xor %r6, %r6, %r20
	or %r6, %r6, %r17
	xor %r6, %r6, %r17
	or %r19, %r19, %r6
	xor %r18, %r18, %r19
	or %r19, %r21, %r12
	xor %r19, %r19, %r18
	and %r12, %r12, %r21
	xor %r12, %r12, %r18
	ld %r0, 496(%r10)
	xor %r0, %r0, %r12
	std %r0, 496(%r10)
	ld %r0, 416(%r10)
	xor %r0, %r0, %r19
	std %r0, 416(%r10)
	ld %r0, 272(%r10)
	xor %r0, %r0, %r2
	std %r0, 272(%r10)
	ld %r0, 384(%r10)
	xor %r0, %r0, %r14
	std %r0, 384(%r10)
	rldicr %r12, %r9, 45, 18
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 216(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 44, 19
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 280(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 43, 20
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 344(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 42, 21
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 408(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 41, 22
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 472(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 40, 23
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 40(%r10)
	xor %r18, %r18, %r0
	or %r6, %r18, %r16
	or %r2, %r6, %r12
	xor %r2, %r2, %r12
	xor %r19, %r18, %r2
	xor %r20, %r16, %r19
	or %r21, %r15, %r20
	or %r2, %r2, %r15
	xor %r2, %r2, %r15
	xor %r16, %r16, %r2
	and %r2, %r14, %r16
	or %r20, %r18, %r20
	xor %r2, %r2, %r20
	xor %r2, %r15, %r2
	xor %r12, %r12, %r2
	or %r22, %r19, %r12
	and %r23, %r14, %r22
	xor %r24, %r19, %r23
	and %r25, %r15, %r20
	xor %r24, %r24, %r25
	or %r22, %r22, %r18
	xor %r22, %r22, %r18
	xor %r25, %r16, %r22
	xor %r14, %r14, %r21
	xor %r25, %r25, %r11
	and %r25, %r25, %r14
	xor %r25, %r25, %r11
	or %r25, %r25, %r17
	xor %r25, %r25, %r17
	xor %r25, %r25, %r2
	or %r2, %r16, %r23
	xor %r2, %r2, %r23
	xor %r22, %r22, %r14
	or %r22, %r24, %r22
	or %r22, %r22, %r2
	xor %r22, %r22, %r2
	or %r2, %r21, %r22
	xor %r2, %r2, %r22
	and %r12, %r12, %r22
	xor %r14, %r14, %r12
	and %r20, %r16, %r20
	or %r20, %r14, %r20
	xor %r23, %r23, %r20
	and %r23, %r23, %r17
	xor %r23, %r23, %r24
	xor %r18, %r18, %r6
	xor %r22, %r22, %r18
	and %r15, %r15, %r14
	xor %r22, %r22, %r15
	or %r2, %r2, %r17
	xor %r2, %r2, %r22
	xor %r16, %r21, %r16
	or %r16, %r16, %r22
	xor %r16, %r16, %r22
	xor %r19, %r19, %r14
	xor %r16, %r16, %r19
	and %r21, %r21, %r17
	xor %r21, %r21, %r16
	ld %r0, 368(%r10)
	xor %r0, %r0, %r23
	std %r0, 368(%r10)
	ld %r0, 448(%r10)
	xor %r0, %r0, %r25
	std %r0, 448(%r10)
	ld %r0, 160(%r10)
	xor %r0, %r0, %r21
	std %r0, 160(%r10)
	ld %r0, 48(%r10)
	xor %r0, %r0, %r2
	std %r0, 48(%r10)
	rldicr %r12, %r9, 51, 12
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 456(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 50, 13
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 24(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 49, 14
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 88(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 48, 15
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 152(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 47, 16
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 216(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 46, 17
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 280(%r10)
	xor %r18, %r18, %r0
	xor %r6, %r17, %r14
	or %r2, %r17, %r12
	and %r2, %r18, %r2
	xor %r6, %r6, %r2
	xor %r19, %r12, %r6
	or %r20, %r14, %r19
	xor %r20, %r20, %r19
	and %r19, %r18, %r19
	xor %r21, %r17, %r19
	xor %r22, %r18, %r16
	or %r23, %r21, %r22
	xor %r24, %r6, %r23
	and %r25, %r16, %r24
	or %r26, %r25, %r12
	xor %r26, %r26, %r12
	or %r21, %r20, %r21
	xor %r27, %r26, %r21
	and %r28, %r27, %r15
	xor %r28, %r28, %r24
	xor %r23, %r17, %r23
	or %r29, %r12, %r23
	xor %r29, %r29, %r23
	xor %r16, %r16, %r29
	or %r29, %r14, %r25
	xor %r29, %r29, %r25
	or %r29, %r16, %r29
	or %r17, %r17, %r22
	xor %r27, %r27, %r17
	or %r2, %r2, %r29
	xor %r27, %r27, %r2
	or %r24, %r18, %r24
	and %r21, %r21, %r24
	xor %r21, %r16, %r21
	xor %r26, %r26, %r11
	and %r26, %r26, %r21
	or %r20, %r20, %r15
	xor %r20, %r20, %r26
	xor %r6, %r6, %r21
	or %r14, %r14, %r6
	xor %r14, %r14, %r6
	xor %r17, %r17, %r11
	xor %r23, %r23, %r17
	xor %r14, %r14, %r23
	or %r14, %r14, %r15
	xor %r14, %r14, %r15
	xor %r14, %r14, %r27
	xor %r12, %r12, %r19
	xor %r18, %r18, %r16
	and %r12, %r12, %r18
	xor %r25, %r25, %r23
	xor %r12, %r12, %r25
	or %r29, %r29, %r15
	xor %r29, %r29, %r15
	xor %r29, %r29, %r12
	ld %r0, 336(%r10)
	xor %r0, %r0, %r28
	std %r0, 336(%r10)
	ld %r0, 352(%r10)
	xor %r0, %r0, %r20
	std %r0, 352(%r10)
	ld %r0, 192(%r10)
	xor %r0, %r0, %r14
	std %r0, 192(%r10)
	ld %r0, 304(%r10)
	xor %r0, %r0, %r29
	std %r0, 304(%r10)
	rldicr %r12, %r9, 57, 6
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 200(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 56, 7
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 264(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 55, 8
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 328(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 54, 9
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 392(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 53, 10
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 456(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 52, 11
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 24(%r10)
	xor %r18, %r18, %r0
	xor %r6, %r15, %r14
	xor %r2, %r16, %r6
	and %r19, %r12, %r2
	and %r20, %r15, %r6
	xor %r21, %r17, %r20
	and %r22, %r19, %r21
	and %r23, %r12, %r20
	xor %r24, %r16, %r23
	or %r25, %r21, %r24
	xor %r6, %r12, %r6
	xor %r26, %r25, %r6
	or %r27, %r18, %r22
	xor %r27, %r27, %r22
	xor %r27, %r27, %r26
	xor %r2, %r2, %r11
	and %r2, %r2, %r14
	or %r26, %r21, %r2
	xor %r24, %r19, %r24
	xor %r26, %r26, %r24
	xor %r19, %r19, %r6
	or %r15, %r15, %r19
	xor %r15, %r15, %r19
	or %r6, %r21, %r15
	xor %r6, %r6, %r15
	xor %r14, %r14, %r24
	xor %r6, %r6, %r14
	or %r19, %r19, %r23
	xor %r19, %r19, %r23
	or %r15, %r15, %r19
	xor %r25, %r17, %r25
	and %r25, %r6, %r25
	xor %r25, %r15, %r25
	and %r23, %r25, %r18
	xor %r23, %r23, %r6
	or %r21, %r21, %r16
	xor %r21, %r21, %r16
	or %r19, %r19, %r21
	or %r20, %r20, %r6
	and %r19, %r19, %r20
	xor %r25, %r25, %r19
	xor %r2, %r2, %r15
	and %r12, %r12, %r2
	or %r22, %r22, %r12
	xor %r19, %r19, %r22
	or %r12, %r19, %r18
	xor %r12, %r12, %r18
	xor %r12, %r12, %r26
	and %r17, %r17, %r22
	xor %r26, %r26, %r11
	xor %r17, %r17, %r26
	xor %r19, %r19, %r17
	or %r25, %r25, %r18
	xor %r25, %r25, %r19
	ld %r0, 112(%r10)
	xor %r0, %r0, %r27
	std %r0, 112(%r10)
	ld %r0, 144(%r10)
	xor %r0, %r0, %r23
	std %r0, 144(%r10)
	ld %r0, 288(%r10)
	xor %r0, %r0, %r25
	std %r0, 288(%r10)
	ld %r0, 0(%r10)
	xor %r0, %r0, %r12
	std %r0, 0(%r10)
	rldicr %r12, %r9, 63, 0
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 504(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 62, 1
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 8(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 61, 2
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 72(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 60, 3
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 136(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 59, 4
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 200(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 58, 5
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 264(%r10)
	xor %r18, %r18, %r0
	or %r6, %r16, %r17
	xor %r6, %r6, %r17
	or %r2, %r14, %r16
	xor %r2, %r2, %r16
	xor %r2, %r15, %r2
	and %r19, %r18, %r2
	or %r20, %r19, %r6
	xor %r20, %r20, %r6
	or %r21, %r17, %r2
	xor %r21, %r21, %r2
	or %r22, %r18, %r21
	or %r23, %r17, %r16
	xor %r23, %r23, %r16
	xor %r23, %r14, %r23
	and %r24, %r22, %r23
	or %r19, %r19, %r24
	xor %r2, %r2, %r11
	xor %r24, %r24, %r2
	or %r16, %r16, %r22
	xor %r16, %r16, %r22
	xor %r24, %r24, %r16
	xor %r6, %r6, %r24
	or %r16, %r20, %r12
	xor %r16, %r16, %r6
	xor %r6, %r18, %r6
	and %r22, %r14, %r6
	xor %r24, %r17, %r24
	xor %r22, %r22, %r24
	xor %r21, %r21, %r22
	xor %r22, %r19, %r22
	or %r17, %r17, %r22
	xor %r14, %r14, %r6
	xor %r17, %r17, %r14
	and %r19, %r19, %r12
	xor %r19, %r19, %r17
	xor %r23, %r23, %r21
	or %r24, %r15, %r24
	xor %r24, %r23, %r24
	xor %r18, %r18, %r24
	and %r18, %r18, %r12
	xor %r18, %r18, %r21
	or %r23, %r23, %r15
	xor %r23, %r23, %r15
	and %r17, %r17, %r23
	xor %r20, %r20, %r24
	xor %r17, %r17, %r20
	or %r17, %r17, %r12
	xor %r17, %r17, %r21
	ld %r0, 208(%r10)
	xor %r0, %r0, %r18
	std %r0, 208(%r10)
	ld %r0, 96(%r10)
	xor %r0, %r0, %r19
	std %r0, 96(%r10)
	ld %r0, 320(%r10)
	xor %r0, %r0, %r16
	std %r0, 320(%r10)
	ld %r0, 240(%r10)
	xor %r0, %r0, %r17
	std %r0, 240(%r10)
	ld %r9, 0(%r3)
	xor %r9, %r9, %r11
	addi %r3, %r3, 8
	rldicr %r12, %r9, 21, 42
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 240(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 20, 43
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 304(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 19, 44
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 368(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 18, 45
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 432(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 17, 46
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 496(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 16, 47
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 0(%r10)
	xor %r18, %r18, %r0
	or %r6, %r18, %r14
	xor %r6, %r6, %r14
	xor %r2, %r15, %r6
	or %r19, %r16, %r12
	xor %r20, %r18, %r16
	and %r21, %r19, %r20
	xor %r22, %r15, %r21
	or %r23, %r22, %r2
	xor %r23, %r23, %r2
	xor %r24, %r14, %r12
	xor %r25, %r16, %r24
	xor %r25, %r25, %r11
	and %r25, %r25, %r2
	or %r21, %r12, %r21
	xor %r25, %r25, %r21
	or %r21, %r25, %r23
	xor %r21, %r21, %r23
	or %r12, %r18, %r12
	or %r26, %r25, %r12
	xor %r22, %r22, %r11
	and %r22, %r22, %r14
	xor %r27, %r26, %r22
	or %r15, %r15, %r12
	xor %r15, %r15, %r12
	xor %r15, %r22, %r15
	xor %r20, %r20, %r11
	and %r20, %r20, %r24
	or %r15, %r15, %r20
	or %r16, %r16, %r6
	xor %r16, %r16, %r6
	xor %r6, %r2, %r26
	or %r6, %r6, %r16
	xor %r6, %r6, %r16
	xor %r16, %r6, %r11
	and %r25, %r19, %r25
	xor %r16, %r16, %r25
	or %r27, %r27, %r17
	xor %r27, %r27, %r17
	xor %r27, %r27, %r16
	xor %r6, %r24, %r6
	or %r22, %r22, %r6
	xor %r22, %r19, %r22
	xor %r18, %r18, %r22
	xor %r16, %r16, %r18
	or %r23, %r23, %r17
	xor %r23, %r23, %r16
	xor %r19, %r19, %r26
	or %r19, %r15, %r19
	xor %r19, %r18, %r19
	or %r24, %r24, %r16
	xor %r24, %r19, %r24
	or %r16, %r21, %r17
	xor %r16, %r16, %r24
	or %r14, %r14, %r2
	or %r14, %r14, %r19
	xor %r14, %r14, %r19
	and %r21, %r21, %r18
	xor %r14, %r14, %r21
	or %r14, %r14, %r17
	xor %r14, %r14, %r15
	ld %r0, 72(%r10)
	xor %r0, %r0, %r14
	std %r0, 72(%r10)
	ld %r0, 88(%r10)
	xor %r0, %r0, %r27
	std %r0, 88(%r10)
	ld %r0, 472(%r10)
	xor %r0, %r0, %r16
	std %r0, 472(%r10)
	ld %r0, 488(%r10)
	xor %r0, %r0, %r23
	std %r0, 488(%r10)
	rldicr %r12, %r9, 27, 36
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 480(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 26, 37
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 48(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 25, 38
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 112(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 24, 39
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 176(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 23, 40
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 240(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 22, 41
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 304(%r10)
	xor %r18, %r18, %r0
	xor %r6, %r17, %r14
	or %r2, %r18, %r12
	xor %r2, %r2, %r12
	xor %r2, %r2, %r11
	and %r2, %r2, %r14
	or %r19, %r17, %r2
	or %r20, %r6, %r12
	xor %r20, %r20, %r12
	and %r21, %r18, %r6
	xor %r14, %r14, %r21
	or %r21, %r14, %r20
	xor %r21, %r21, %r20
	and %r22, %r16, %r12
	xor %r2, %r2, %r20
	and %r2, %r19, %r2
	or %r20, %r2, %r22
	xor %r20, %r20, %r22
	and %r23, %r16, %r2
	xor %r18, %r18, %r11
	xor %r18, %r23, %r18
	xor %r12, %r12, %r6
	or %r24, %r12, %r22
	xor %r24, %r24, %r22
	xor %r25, %r18, %r24
	xor %r20, %r20, %r11
	and %r20, %r20, %r15
	xor %r20, %r20, %r25
	or %r17, %r17, %r24
	xor %r17, %r17, %r24
	xor %r14, %r14, %r17
	or %r18, %r18, %r14
	xor %r18, %r18, %r14
	xor %r16, %r16, %r12
	xor %r18, %r18, %r16
	or %r24, %r19, %r15
	xor %r24, %r24, %r15
	xor %r24, %r24, %r18
	xor %r23, %r23, %r17
	or %r16, %r16, %r23
	xor %r19, %r19, %r25
	or %r22, %r22, %r19
	xor %r23, %r16, %r22
	xor %r2, %r2, %r25
	xor %r18, %r18, %r2
	and %r22, %r22, %r18
	and %r6, %r6, %r16
	xor %r22, %r22, %r6
	or %r6, %r22, %r15
	xor %r6, %r6, %r23
	or %r22, %r22, %r14
	xor %r22, %r22, %r14
	or %r12, %r12, %r19
	xor %r22, %r22, %r12
	or %r21, %r21, %r15
	xor %r21, %r21, %r22
	ld %r0, 408(%r10)
	xor %r0, %r0, %r21
	std %r0, 408(%r10)
	ld %r0, 440(%r10)
	xor %r0, %r0, %r6
	std %r0, 440(%r10)
	ld %r0, 264(%r10)
	xor %r0, %r0, %r20
	std %r0, 264(%r10)
	ld %r0, 232(%r10)
	xor %r0, %r0, %r24
	std %r0, 232(%r10)
	rldicr %r12, %r9, 33, 30
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 224(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 32, 31
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 288(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 31, 32
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 352(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 30, 33
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 416(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 29, 34
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 480(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 28, 35
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 48(%r10)
	xor %r18, %r18, %r0
	or %r6, %r18, %r17
	xor %r6, %r6, %r17
	xor %r2, %r16, %r12
	or %r19, %r6, %r2
	xor %r20, %r15, %r12
	or %r21, %r20, %r18
	xor %r21, %r21, %r18
	xor %r22, %r19, %r21
	xor %r23, %r17, %r2
	or %r24, %r23, %r12
	xor %r24, %r24, %r12
	xor %r19, %r19, %r24
	or %r24, %r22, %r19
	xor %r24, %r24, %r19
	and %r25, %r12, %r22
	or %r25, %r15, %r25
	and %r25, %r18, %r25
	xor %r25, %r23, %r25
	or %r26, %r22, %r14
	xor %r26, %r26, %r14
	xor %r26, %r26, %r25
	and %r2, %r2, %r20
	xor %r20, %r18, %r15
	xor %r27, %r19, %r20
	or %r27, %r16, %r27
	or %r27, %r27, %r2
	xor %r27, %r27, %r2
	or %r21, %r21, %r20
	or %r20, %r25, %r21
	xor %r20, %r20, %r21
	and %r12, %r15, %r12
	or %r2, %r12, %r17
	xor %r2, %r2, %r17
	xor %r20, %r20, %r2
	and %r19, %r19, %r20
	or %r12, %r23, %r12
	or %r12, %r12, %r19
	xor %r12, %r12, %r19
	xor %r18, %r18, %r12
	and %r27, %r27, %r14
	xor %r27, %r27, %r18
	xor %r22, %r22, %r11
	or %r17, %r17, %r22
	or %r16, %r16, %r17
	xor %r23, %r23, %r16
	xor %r21, %r21, %r23
	xor %r24, %r24, %r11
	and %r24, %r24, %r14
	xor %r24, %r24, %r21
	and %r15, %r15, %r22
	xor %r25, %r25, %r15
	or %r23, %r23, %r25
	xor %r6, %r6, %r18
	xor %r23, %r23, %r6
	or %r20, %r20, %r14
	xor %r20, %r20, %r23
	ld %r0, 184(%r10)
	xor %r0, %r0, %r26
	std %r0, 184(%r10)
	ld %r0, 136(%r10)
	xor %r0, %r0, %r20
	std %r0, 136(%r10)
	ld %r0, 40(%r10)
	xor %r0, %r0, %r27
	std %r0, 40(%r10)
	ld %r0, 24(%r10)
	xor %r0, %r0, %r24
	std %r0, 24(%r10)
	rldicr %r12, %r9, 39, 24
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 464(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 38, 25
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 32(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 37, 26
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 96(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 36, 27
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 160(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 35, 28
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 224(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 34, 29
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 288(%r10)
	xor %r18, %r18, %r0
	xor %r18, %r18, %r16
	xor %r16, %r16, %r14
	or %r6, %r17, %r15
	xor %r6, %r14, %r6
	xor %r6, %r6, %r11
	and %r6, %r6, %r16
	or %r2, %r16, %r17
	xor %r2, %r2, %r17
	xor %r19, %r15, %r2
	or %r20, %r18, %r19
	or %r20, %r20, %r6
	xor %r20, %r20, %r6
	xor %r21, %r17, %r20
	and %r19, %r19, %r21
	or %r16, %r16, %r19
	xor %r16, %r16, %r19
	xor %r18, %r18, %r21
	xor %r16, %r16, %r11
	and %r16, %r16, %r18
	xor %r6, %r6, %r16
	xor %r17, %r17, %r15
	or %r14, %r14, %r2
	xor %r18, %r18, %r14
	or %r14, %r18, %r17
	xor %r14, %r14, %r17
	xor %r20, %r20, %r14
	or %r14, %r12, %r6
	xor %r14, %r14, %r6
	xor %r14, %r14, %r20
	xor %r20, %r20, %r11
	or %r2, %r6, %r12
	xor %r2, %r2, %r12
	xor %r2, %r2, %r20
	xor %r6, %r6, %r20
	or %r6, %r6, %r17
	xor %r6, %r6, %r17
	or %r19, %r19, %r6
	xor %r18, %r18, %r19
	or %r19, %r21, %r12
	xor %r19, %r19, %r18
	and %r12, %r12, %r21
	xor %r12, %r12, %r18
	ld %r0, 504(%r10)
	xor %r0, %r0, %r12
	std %r0, 504(%r10)
	ld %r0, 424(%r10)
	xor %r0, %r0, %r19
	std %r0, 424(%r10)
	ld %r0, 280(%r10)
	xor %r0, %r0, %r2
	std %r0, 280(%r10)
	ld %r0, 392(%r10)
	xor %r0, %r0, %r14
	std %r0, 392(%r10)
	rldicr %r12, %r9, 45, 18
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 208(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 44, 19
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 272(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 43, 20
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 336(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 42, 21
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 400(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 41, 22
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 464(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 40, 23
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 32(%r10)
	xor %r18, %r18, %r0
	or %r6, %r18, %r16
	or %r2, %r6, %r12
	xor %r2, %r2, %r12
	xor %r19, %r18, %r2
	xor %r20, %r16, %r19
	or %r21, %r15, %r20
	or %r2, %r2, %r15
	xor %r2, %r2, %r15
	xor %r16, %r16, %r2
	and %r2, %r14, %r16
	or %r20, %r18, %r20
	xor %r2, %r2, %r20
	xor %r2, %r15, %r2
	xor %r12, %r12, %r2
	or %r22, %r19, %r12
	and %r23, %r14, %r22
	xor %r24, %r19, %r23
	and %r25, %r15, %r20
	xor %r24, %r24, %r25
	or %r22, %r22, %r18
	xor %r22, %r22, %r18
	xor %r25, %r16, %r22
	xor %r14, %r14, %r21
	xor %r25, %r25, %r11
	and %r25, %r25, %r14
	xor %r25, %r25, %r11
	or %r25, %r25, %r17
	xor %r25, %r25, %r17
	xor %r25, %r25, %r2
	or %r2, %r16, %r23
	xor %r2, %r2, %r23
	xor %r22, %r22, %r14
	or %r22, %r24, %r22
	or %r22, %r22, %r2
	xor %r22, %r22, %r2
	or %r2, %r21, %r22
	xor %r2, %r2, %r22
	and %r12, %r12, %r22
	xor %r14, %r14, %r12
	and %r20, %r16, %r20
	or %r20, %r14, %r20
	xor %r23, %r23, %r20
	and %r23, %r23, %r17
	xor %r23, %r23, %r24
	xor %r18, %r18, %r6
	xor %r22, %r22, %r18
	and %r15, %r15, %r14
	xor %r22, %r22, %r15
	or %r2, %r2, %r17
	xor %r2, %r2, %r22
	xor %r16, %r21, %r16
	or %r16, %r16, %r22
	xor %r16, %r16, %r22
	xor %r19, %r19, %r14
	xor %r16, %r16, %r19
	and %r21, %r21, %r17
	xor %r21, %r21, %r16
	ld %r0, 376(%r10)
	xor %r0, %r0, %r23
	std %r0, 376(%r10)
	ld %r0, 456(%r10)
	xor %r0, %r0, %r25
	std %r0, 456(%r10)
	ld %r0, 168(%r10)
	xor %r0, %r0, %r21
	std %r0, 168(%r10)
	ld %r0, 56(%r10)
	xor %r0, %r0, %r2
	std %r0, 56(%r10)
	rldicr %r12, %r9, 51, 12
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 448(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 50, 13
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 16(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 49, 14
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 80(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 48, 15
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 144(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 47, 16
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 208(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 46, 17
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 272(%r10)
	xor %r18, %r18, %r0
	xor %r6, %r17, %r14
	or %r2, %r17, %r12
	and %r2, %r18, %r2
	xor %r6, %r6, %r2
	xor %r19, %r12, %r6
	or %r20, %r14, %r19
	xor %r20, %r20, %r19
	and %r19, %r18, %r19
	xor %r21, %r17, %r19
	xor %r22, %r18, %r16
	or %r23, %r21, %r22
	xor %r24, %r6, %r23
	and %r25, %r16, %r24
	or %r26, %r25, %r12
	xor %r26, %r26, %r12
	or %r21, %r20, %r21
	xor %r27, %r26, %r21
	and %r28, %r27, %r15
	xor %r28, %r28, %r24
	xor %r23, %r17, %r23
	or %r29, %r12, %r23
	xor %r29, %r29, %r23
	xor %r16, %r16, %r29
	or %r29, %r14, %r25
	xor %r29, %r29, %r25
	or %r29, %r16, %r29
	or %r17, %r17, %r22
	xor %r27, %r27, %r17
	or %r2, %r2, %r29
	xor %r27, %r27, %r2
	or %r24, %r18, %r24
	and %r21, %r21, %r24
	xor %r21, %r16, %r21
	xor %r26, %r26, %r11
	and %r26, %r26, %r21
	or %r20, %r20, %r15
	xor %r20, %r20, %r26
	xor %r6, %r6, %r21
	or %r14, %r14, %r6
	xor %r14, %r14, %r6
	xor %r17, %r17, %r11
	xor %r23, %r23, %r17
	xor %r14, %r14, %r23
	or %r14, %r14, %r15
	xor %r14, %r14, %r15
	xor %r14, %r14, %r27
	xor %r12, %r12, %r19
	xor %r18, %r18, %r16
	and %r12, %r12, %r18
	xor %r25, %r25, %r23
	xor %r12, %r12, %r25
	or %r29, %r29, %r15
	xor %r29, %r29, %r15
	xor %r29, %r29, %r12
	ld %r0, 344(%r10)
	xor %r0, %r0, %r28
	std %r0, 344(%r10)
	ld %r0, 360(%r10)
	xor %r0, %r0, %r20
	std %r0, 360(%r10)
	ld %r0, 200(%r10)
	xor %r0, %r0, %r14
	std %r0, 200(%r10)
	ld %r0, 312(%r10)
	xor %r0, %r0, %r29
	std %r0, 312(%r10)
	rldicr %r12, %r9, 57, 6
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 192(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 56, 7
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 256(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 55, 8
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 320(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 54, 9
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 384(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 53, 10
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 448(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 52, 11
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 16(%r10)
	xor %r18, %r18, %r0
	xor %r6, %r15, %r14
	xor %r2, %r16, %r6
	and %r19, %r12, %r2
	and %r20, %r15, %r6
	xor %r21, %r17, %r20
	and %r22, %r19, %r21
	and %r23, %r12, %r20
	xor %r24, %r16, %r23
	or %r25, %r21, %r24
	xor %r6, %r12, %r6
	xor %r26, %r25, %r6
	or %r27, %r18, %r22
	xor %r27, %r27, %r22
	xor %r27, %r27, %r26
	xor %r2, %r2, %r11
	and %r2, %r2, %r14
	or %r26, %r21, %r2
	xor %r24, %r19, %r24
	xor %r26, %r26, %r24
	xor %r19, %r19, %r6
	or %r15, %r15, %r19
	xor %r15, %r15, %r19
	or %r6, %r21, %r15
	xor %r6, %r6, %r15
	xor %r14, %r14, %r24
	xor %r6, %r6, %r14
	or %r19, %r19, %r23
	xor %r19, %r19, %r23
	or %r15, %r15, %r19
	xor %r25, %r17, %r25
	and %r25, %r6, %r25
	xor %r25, %r15, %r25
	and %r23, %r25, %r18
	xor %r23, %r23, %r6
	or %r21, %r21, %r16
	xor %r21, %r21, %r16
	or %r19, %r19, %r21
	or %r20, %r20, %r6
	and %r19, %r19, %r20
	xor %r25, %r25, %r19
	xor %r2, %r2, %r15
	and %r12, %r12, %r2
	or %r22, %r22, %r12
	xor %r19, %r19, %r22
	or %r12, %r19, %r18
	xor %r12, %r12, %r18
	xor %r12, %r12, %r26
	and %r17, %r17, %r22
	xor %r26, %r26, %r11
	xor %r17, %r17, %r26
	xor %r19, %r19, %r17
	or %r25, %r25, %r18
	xor %r25, %r25, %r19
	ld %r0, 120(%r10)
	xor %r0, %r0, %r27
	std %r0, 120(%r10)
	ld %r0, 152(%r10)
	xor %r0, %r0, %r23
	std %r0, 152(%r10)
	ld %r0, 296(%r10)
	xor %r0, %r0, %r25
	std %r0, 296(%r10)
	ld %r0, 8(%r10)
	xor %r0, %r0, %r12
	std %r0, 8(%r10)
	rldicr %r12, %r9, 63, 0
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 496(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 62, 1
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 0(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 61, 2
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 64(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 60, 3
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 128(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 59, 4
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 192(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 58, 5
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 256(%r10)
	xor %r18, %r18, %r0
	or %r6, %r16, %r17
	xor %r6, %r6, %r17
	or %r2, %r14, %r16
	xor %r2, %r2, %r16
	xor %r2, %r15, %r2
	and %r19, %r18, %r2
	or %r20, %r19, %r6
	xor %r20, %r20, %r6
	or %r21, %r17, %r2
	xor %r21, %r21, %r2
	or %r22, %r18, %r21
	or %r23, %r17, %r16
	xor %r23, %r23, %r16
	xor %r23, %r14, %r23
	and %r24, %r22, %r23
	or %r19, %r19, %r24
	xor %r2, %r2, %r11
	xor %r24, %r24, %r2
	or %r16, %r16, %r22
	xor %r16, %r16, %r22
	xor %r24, %r24, %r16
	xor %r6, %r6, %r24
	or %r16, %r20, %r12
	xor %r16, %r16, %r6
	xor %r6, %r18, %r6
	and %r22, %r14, %r6
	xor %r24, %r17, %r24
	xor %r22, %r22, %r24
	xor %r21, %r21, %r22
	xor %r22, %r19, %r22
	or %r17, %r17, %r22
	xor %r14, %r14, %r6
	xor %r17, %r17, %r14
	and %r19, %r19, %r12
	xor %r19, %r19, %r17
	xor %r23, %r23, %r21
	or %r24, %r15, %r24
	xor %r24, %r23, %r24
	xor %r18, %r18, %r24
	and %r18, %r18, %r12
	xor %r18, %r18, %r21
	or %r23, %r23, %r15
	xor %r23, %r23, %r15
	and %r17, %r17, %r23
	xor %r20, %r20, %r24
	xor %r17, %r17, %r20
	or %r17, %r17, %r12
	xor %r17, %r17, %r21
	ld %r0, 216(%r10)
	xor %r0, %r0, %r18
	std %r0, 216(%r10)
	ld %r0, 104(%r10)
	xor %r0, %r0, %r19
	std %r0, 104(%r10)
	ld %r0, 328(%r10)
	xor %r0, %r0, %r16
	std %r0, 328(%r10)
	ld %r0, 248(%r10)
	xor %r0, %r0, %r17
	std %r0, 248(%r10)
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 27b
	ld %r12, 0(%r10)
	ld %r14, 8(%r10)
	std %r14, 0(%r10)
	std %r12, 8(%r10)
	ld %r12, 64(%r10)
	ld %r14, 72(%r10)
	std %r14, 64(%r10)
	std %r12, 72(%r10)
	ld %r12, 128(%r10)
	ld %r14, 136(%r10)
	std %r14, 128(%r10)
	std %r12, 136(%r10)
	ld %r12, 192(%r10)
	ld %r14, 200(%r10)
	std %r14, 192(%r10)
	std %r12, 200(%r10)
	ld %r12, 256(%r10)
	ld %r14, 264(%r10)
	std %r14, 256(%r10)
	std %r12, 264(%r10)
	ld %r12, 320(%r10)
	ld %r14, 328(%r10)
	std %r14, 320(%r10)
	std %r12, 328(%r10)
	ld %r12, 384(%r10)
	ld %r14, 392(%r10)
	std %r14, 384(%r10)
	std %r12, 392(%r10)
	ld %r12, 448(%r10)
	ld %r14, 456(%r10)
	std %r14, 448(%r10)
	std %r12, 456(%r10)
	ld %r12, 16(%r10)
	ld %r14, 24(%r10)
	std %r14, 16(%r10)
	std %r12, 24(%r10)
	ld %r12, 80(%r10)
	ld %r14, 88(%r10)
	std %r14, 80(%r10)
	std %r12, 88(%r10)
	ld %r12, 144(%r10)
	ld %r14, 152(%r10)
	std %r14, 144(%r10)
	std %r12, 152(%r10)
	ld %r12, 208(%r10)
	ld %r14, 216(%r10)
	std %r14, 208(%r10)
	std %r12, 216(%r10)
	ld %r12, 272(%r10)
	ld %r14, 280(%r10)
	std %r14, 272(%r10)
	std %r12, 280(%r10)
	ld %r12, 336(%r10)
	ld %r14, 344(%r10)
	std %r14, 336(%r10)
	std %r12, 344(%r10)
	ld %r12, 400(%r10)
	ld %r14, 408(%r10)
	std %r14, 400(%r10)
	std %r12, 408(%r10)
	ld %r12, 464(%r10)
	ld %r14, 472(%r10)
	std %r14, 464(%r10)
	std %r12, 472(%r10)
	ld %r12, 32(%r10)
	ld %r14, 40(%r10)
	std %r14, 32(%r10)
	std %r12, 40(%r10)
	ld %r12, 96(%r10)
	ld %r14, 104(%r10)
	std %r14, 96(%r10)
	std %r12, 104(%r10)
	ld %r12, 160(%r10)
	ld %r14, 168(%r10)
	std %r14, 160(%r10)
	std %r12, 168(%r10)
	ld %r12, 224(%r10)
	ld %r14, 232(%r10)
	std %r14, 224(%r10)
	std %r12, 232(%r10)
	ld %r12, 288(%r10)
	ld %r14, 296(%r10)
	std %r14, 288(%r10)
	std %r12, 296(%r10)
	ld %r12, 352(%r10)
	ld %r14, 360(%r10)
	std %r14, 352(%r10)
	std %r12, 360(%r10)
	ld %r12, 416(%r10)
	ld %r14, 424(%r10)
	std %r14, 416(%r10)
	std %r12, 424(%r10)
	ld %r12, 480(%r10)
	ld %r14, 488(%r10)
	std %r14, 480(%r10)
	std %r12, 488(%r10)
	ld %r12, 48(%r10)
	ld %r14, 56(%r10)
	std %r14, 48(%r10)
	std %r12, 56(%r10)
	ld %r12, 112(%r10)
	ld %r14, 120(%r10)
	std %r14, 112(%r10)
	std %r12, 120(%r10)
	ld %r12, 176(%r10)
	ld %r14, 184(%r10)
	std %r14, 176(%r10)
	std %r12, 184(%r10)
	ld %r12, 240(%r10)
	ld %r14, 248(%r10)
	std %r14, 240(%r10)
	std %r12, 248(%r10)
	ld %r12, 304(%r10)
	ld %r14, 312(%r10)
	std %r14, 304(%r10)
	std %r12, 312(%r10)
	ld %r12, 368(%r10)
	ld %r14, 376(%r10)
	std %r14, 368(%r10)
	std %r12, 376(%r10)
	ld %r12, 432(%r10)
	ld %r14, 440(%r10)
	std %r14, 432(%r10)
	std %r12, 440(%r10)
	ld %r12, 496(%r10)
	ld %r14, 504(%r10)
	std %r14, 496(%r10)
	std %r12, 504(%r10)
	addi %r3, %r7, 120
	li %r5, 8
28:
	ld %r9, 0(%r3)
	xor %r9, %r9, %r11
	addi %r3, %r3, -8
	rldicr %r12, %r9, 21, 42
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 248(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 20, 43
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 312(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 19, 44
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 376(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 18, 45
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 440(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 17, 46
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 504(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 16, 47
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 8(%r10)
	xor %r18, %r18, %r0
	or %r6, %r18, %r14
	xor %r6, %r6, %r14
	xor %r2, %r15, %r6
	or %r19, %r16, %r12
	xor %r20, %r18, %r16
	and %r21, %r19, %r20
	xor %r22, %r15, %r21
	or %r23, %r22, %r2
	xor %r23, %r23, %r2
	xor %r24, %r14, %r12
	xor %r25, %r16, %r24
	xor %r25, %r25, %r11
	and %r25, %r25, %r2
	or %r21, %r12, %r21
	xor %r25, %r25, %r21
	or %r21, %r25, %r23
	xor %r21, %r21, %r23
	or %r12, %r18, %r12
	or %r26, %r25, %r12
	xor %r22, %r22, %r11
	and %r22, %r22, %r14
	xor %r27, %r26, %r22
	or %r15, %r15, %r12
	xor %r15, %r15, %r12
	xor %r15, %r22, %r15
	xor %r20, %r20, %r11
	and %r20, %r20, %r24
	or %r15, %r15, %r20
	or %r16, %r16, %r6
	xor %r16, %r16, %r6
	xor %r6, %r2, %r26
	or %r6, %r6, %r16
	xor %r6, %r6, %r16
	xor %r16, %r6, %r11
	and %r25, %r19, %r25
	xor %r16, %r16, %r25
	or %r27, %r27, %r17
	xor %r27, %r27, %r17
	xor %r27, %r27, %r16
	xor %r6, %r24, %r6
	or %r22, %r22, %r6
	xor %r22, %r19, %r22
	xor %r18, %r18, %r22
	xor %r16, %r16, %r18
	or %r23, %r23, %r17
	xor %r23, %r23, %r16
	xor %r19, %r19, %r26
	or %r19, %r15, %r19
	xor %r19, %r18, %r19
	or %r24, %r24, %r16
	xor %r24, %r19, %r24
	or %r16, %r21, %r17
	xor %r16, %r16, %r24
	or %r14, %r14, %r2
	or %r14, %r14, %r19
	xor %r14, %r14, %r19
	and %r21, %r21, %r18
	xor %r14, %r14, %r21
	or %r14, %r14, %r17
	xor %r14, %r14, %r15
	ld %r0, 64(%r10)
	xor %r0, %r0, %r14
	std %r0, 64(%r10)
	ld %r0, 80(%r10)
	xor %r0, %r0, %r27
	std %r0, 80(%r10)
	ld %r0, 464(%r10)
	xor %r0, %r0, %r16
	std %r0, 464(%r10)
	ld %r0, 480(%r10)
	xor %r0, %r0, %r23
	std %r0, 480(%r10)
	rldicr %r12, %r9, 27, 36
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 488(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 26, 37
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 56(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 25, 38
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 120(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 24, 39
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 184(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 23, 40
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 248(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 22, 41
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 312(%r10)
	xor %r18, %r18, %r0
	xor %r6, %r17, %r14
	or %r2, %r18, %r12
	xor %r2, %r2, %r12
	xor %r2, %r2, %r11
	and %r2, %r2, %r14
	or %r19, %r17, %r2
	or %r20, %r6, %r12
	xor %r20, %r20, %r12
	and %r21, %r18, %r6
	xor %r14, %r14, %r21
	or %r21, %r14, %r20
	xor %r21, %r21, %r20
	and %r22, %r16, %r12
	xor %r2, %r2, %r20
	and %r2, %r19, %r2
	or %r20, %r2, %r22
	xor %r20, %r20, %r22
	and %r23, %r16, %r2
	xor %r18, %r18, %r11
	xor %r18, %r23, %r18
	xor %r12, %r12, %r6
	or %r24, %r12, %r22
	xor %r24, %r24, %r22
	xor %r25, %r18, %r24
	xor %r20, %r20, %r11
	and %r20, %r20, %r15
	xor %r20, %r20, %r25
	or %r17, %r17, %r24
	xor %r17, %r17, %r24
	xor %r14, %r14, %r17
	or %r18, %r18, %r14
	xor %r18, %r18, %r14
	xor %r16, %r16, %r12
	xor %r18, %r18, %r16
	or %r24, %r19, %r15
	xor %r24, %r24, %r15
	xor %r24, %r24, %r18
	xor %r23, %r23, %r17
	or %r16, %r16, %r23
	xor %r19, %r19, %r25
	or %r22, %r22, %r19
	xor %r23, %r16, %r22
	xor %r2, %r2, %r25
	xor %r18, %r18, %r2
	and %r22, %r22, %r18
	and %r6, %r6, %r16
	xor %r22, %r22, %r6
	or %r6, %r22, %r15
	xor %r6, %r6, %r23
	or %r22, %r22, %r14
	xor %r22, %r22, %r14
	or %r12, %r12, %r19
	xor %r22, %r22, %r12
	or %r21, %r21, %r15
	xor %r21, %r21, %r22
	ld %r0, 400(%r10)
	xor %r0, %r0, %r21
	std %r0, 400(%r10)
	ld %r0, 432(%r10)
	xor %r0, %r0, %r6
	std %r0, 432(%r10)
	ld %r0, 256(%r10)
	xor %r0, %r0, %r20
	std %r0, 256(%r10)
	ld %r0, 224(%r10)
	xor %r0, %r0, %r24
	std %r0, 224(%r10)
	rldicr %r12, %r9, 33, 30
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 232(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 32, 31
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 296(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 31, 32
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 360(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 30, 33
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 424(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 29, 34
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 488(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 28, 35
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 56(%r10)
	xor %r18, %r18, %r0
	or %r6, %r18, %r17
	xor %r6, %r6, %r17
	xor %r2, %r16, %r12
	or %r19, %r6, %r2
	xor %r20, %r15, %r12
	or %r21, %r20, %r18
	xor %r21, %r21, %r18
	xor %r22, %r19, %r21
	xor %r23, %r17, %r2
	or %r24, %r23, %r12
	xor %r24, %r24, %r12
	xor %r19, %r19, %r24
	or %r24, %r22, %r19
	xor %r24, %r24, %r19
	and %r25, %r12, %r22
	or %r25, %r15, %r25
	and %r25, %r18, %r25
	xor %r25, %r23, %r25
	or %r26, %r22, %r14
	xor %r26, %r26, %r14
	xor %r26, %r26, %r25
	and %r2, %r2, %r20
	xor %r20, %r18, %r15
	xor %r27, %r19, %r20
	or %r27, %r16, %r27
	or %r27, %r27, %r2
	xor %r27, %r27, %r2
	or %r21, %r21, %r20
	or %r20, %r25, %r21
	xor %r20, %r20, %r21
	and %r12, %r15, %r12
	or %r2, %r12, %r17
	xor %r2, %r2, %r17
	xor %r20, %r20, %r2
	and %r19, %r19, %r20
	or %r12, %r23, %r12
	or %r12, %r12, %r19
	xor %r12, %r12, %r19
	xor %r18, %r18, %r12
	and %r27, %r27, %r14
	xor %r27, %r27, %r18
	xor %r22, %r22, %r11
	or %r17, %r17, %r22
	or %r16, %r16, %r17
	xor %r23, %r23, %r16
	xor %r21, %r21, %r23
	xor %r24, %r24, %r11
	and %r24, %r24, %r14
	xor %r24, %r24, %r21
	and %r15, %r15, %r22
	xor %r25, %r25, %r15
	or %r23, %r23, %r25
	xor %r6, %r6, %r18
	xor %r23, %r23, %r6
	or %r20, %r20, %r14
	xor %r20, %r20, %r23
	ld %r0, 176(%r10)
	xor %r0, %r0, %r26
	std %r0, 176(%r10)
	ld %r0, 128(%r10)
	xor %r0, %r0, %r20
	std %r0, 128(%r10)
	ld %r0, 32(%r10)
	xor %r0, %r0, %r27
	std %r0, 32(%r10)
	ld %r0, 16(%r10)
	xor %r0, %r0, %r24
	std %r0, 16(%r10)
	rldicr %r12, %r9, 39, 24
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 472(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 38, 25
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 40(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 37, 26
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 104(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 36, 27
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 168(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 35, 28
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 232(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 34, 29
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 296(%r10)
	xor %r18, %r18, %r0
	xor %r18, %r18, %r16
	xor %r16, %r16, %r14
	or %r6, %r17, %r15
	xor %r6, %r14, %r6
	xor %r6, %r6, %r11
	and %r6, %r6, %r16
	or %r2, %r16, %r17
	xor %r2, %r2, %r17
	xor %r19, %r15, %r2
	or %r20, %r18, %r19
	or %r20, %r20, %r6
	xor %r20, %r20, %r6
	xor %r21, %r17, %r20
	and %r19, %r19, %r21
	or %r16, %r16, %r19
	xor %r16, %r16, %r19
	xor %r18, %r18, %r21
	xor %r16, %r16, %r11
	and %r16, %r16, %r18
	xor %r6, %r6, %r16
	xor %r17, %r17, %r15
	or %r14, %r14, %r2
	xor %r18, %r18, %r14
	or %r14, %r18, %r17
	xor %r14, %r14, %r17
	xor %r20, %r20, %r14
	or %r14, %r12, %r6
	xor %r14, %r14, %r6
	xor %r14, %r14, %r20
	xor %r20, %r20, %r11
	or %r2, %r6, %r12
	xor %r2, %r2, %r12
	xor %r2, %r2, %r20
	xor %r6, %r6, %r20
	or %r6, %r6, %r17
	xor %r6, %r6, %r17
	or %r19, %r19, %r6
	xor %r18, %r18, %r19
	or %r19, %r21, %r12
	xor %r19, %r19, %r18
	and %r12, %r12, %r21
	xor %r12, %r12, %r18
	ld %r0, 496(%r10)
	xor %r0, %r0, %r12
	std %r0, 496(%r10)
	ld %r0, 416(%r10)
	xor %r0, %r0, %r19
	std %r0, 416(%r10)
	ld %r0, 272(%r10)
	xor %r0, %r0, %r2
	std %r0, 272(%r10)
	ld %r0, 384(%r10)
	xor %r0, %r0, %r14
	std %r0, 384(%r10)
	rldicr %r12, %r9, 45, 18
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 216(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 44, 19
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 280(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 43, 20
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 344(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 42, 21
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 408(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 41, 22
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 472(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 40, 23
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 40(%r10)
	xor %r18, %r18, %r0
	or %r6, %r18, %r16
	or %r2, %r6, %r12
	xor %r2, %r2, %r12
	xor %r19, %r18, %r2
	xor %r20, %r16, %r19
	or %r21, %r15, %r20
	or %r2, %r2, %r15
	xor %r2, %r2, %r15
	xor %r16, %r16, %r2
	and %r2, %r14, %r16
	or %r20, %r18, %r20
	xor %r2, %r2, %r20
	xor %r2, %r15, %r2
	xor %r12, %r12, %r2
	or %r22, %r19, %r12
	and %r23, %r14, %r22
	xor %r24, %r19, %r23
	and %r25, %r15, %r20
	xor %r24, %r24, %r25
	or %r22, %r22, %r18
	xor %r22, %r22, %r18
	xor %r25, %r16, %r22
	xor %r14, %r14, %r21
	xor %r25, %r25, %r11
	and %r25, %r25, %r14
	xor %r25, %r25, %r11
	or %r25, %r25, %r17
	xor %r25, %r25, %r17
	xor %r25, %r25, %r2
	or %r2, %r16, %r23
	xor %r2, %r2, %r23
	xor %r22, %r22, %r14
	or %r22, %r24, %r22
	or %r22, %r22, %r2
	xor %r22, %r22, %r2
	or %r2, %r21, %r22
	xor %r2, %r2, %r22
	and %r12, %r12, %r22
	xor %r14, %r14, %r12
	and %r20, %r16, %r20
	or %r20, %r14, %r20
	xor %r23, %r23, %r20
	and %r23, %r23, %r17
	xor %r23, %r23, %r24
	xor %r18, %r18, %r6
	xor %r22, %r22, %r18
	and %r15, %r15, %r14
	xor %r22, %r22, %r15
	or %r2, %r2, %r17
	xor %r2, %r2, %r22
	xor %r16, %r21, %r16
	or %r16, %r16, %r22
	xor %r16, %r16, %r22
	xor %r19, %r19, %r14
	xor %r16, %r16, %r19
	and %r21, %r21, %r17
	xor %r21, %r21, %r16
	ld %r0, 368(%r10)
	xor %r0, %r0, %r23
	std %r0, 368(%r10)
	ld %r0, 448(%r10)
	xor %r0, %r0, %r25
	std %r0, 448(%r10)
	ld %r0, 160(%r10)
	xor %r0, %r0, %r21
	std %r0, 160(%r10)
	ld %r0, 48(%r10)
	xor %r0, %r0, %r2
	std %r0, 48(%r10)
	rldicr %r12, %r9, 51, 12
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 456(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 50, 13
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 24(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 49, 14
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 88(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 48, 15
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 152(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 47, 16
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 216(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 46, 17
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 280(%r10)
	xor %r18, %r18, %r0
	xor %r6, %r17, %r14
	or %r2, %r17, %r12
	and %r2, %r18, %r2
	xor %r6, %r6, %r2
	xor %r19, %r12, %r6
	or %r20, %r14, %r19
	xor %r20, %r20, %r19
	and %r19, %r18, %r19
	xor %r21, %r17, %r19
	xor %r22, %r18, %r16
	or %r23, %r21, %r22
	xor %r24, %r6, %r23
	and %r25, %r16, %r24
	or %r26, %r25, %r12
	xor %r26, %r26, %r12
	or %r21, %r20, %r21
	xor %r27, %r26, %r21
	and %r28, %r27, %r15
	xor %r28, %r28, %r24
	xor %r23, %r17, %r23
	or %r29, %r12, %r23
	xor %r29, %r29, %r23
	xor %r16, %r16, %r29
	or %r29, %r14, %r25
	xor %r29, %r29, %r25
	or %r29, %r16, %r29
	or %r17, %r17, %r22
	xor %r27, %r27, %r17
	or %r2, %r2, %r29
	xor %r27, %r27, %r2
	or %r24, %r18, %r24
	and %r21, %r21, %r24
	xor %r21, %r16, %r21
	xor %r26, %r26, %r11
	and %r26, %r26, %r21
	or %r20, %r20, %r15
	xor %r20, %r20, %r26
	xor %r6, %r6, %r21
	or %r14, %r14, %r6
	xor %r14, %r14, %r6
	xor %r17, %r17, %r11
	xor %r23, %r23, %r17
	xor %r14, %r14, %r23
	or %r14, %r14, %r15
	xor %r14, %r14, %r15
	xor %r14, %r14, %r27
	xor %r12, %r12, %r19
	xor %r18, %r18, %r16
	and %r12, %r12, %r18
	xor %r25, %r25, %r23
	xor %r12, %r12, %r25
	or %r29, %r29, %r15
	xor %r29, %r29, %r15
	xor %r29, %r29, %r12
	ld %r0, 336(%r10)
	xor %r0, %r0, %r28
	std %r0, 336(%r10)
	ld %r0, 352(%r10)
	xor %r0, %r0, %r20
	std %r0, 352(%r10)
	ld %r0, 192(%r10)
	xor %r0, %r0, %r14
	std %r0, 192(%r10)
	ld %r0, 304(%r10)
	xor %r0, %r0, %r29
	std %r0, 304(%r10)
	rldicr %r12, %r9, 57, 6
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 200(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 56, 7
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 264(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 55, 8
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 328(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 54, 9
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 392(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 53, 10
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 456(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 52, 11
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 24(%r10)
	xor %r18, %r18, %r0
	xor %r6, %r15, %r14
	xor %r2, %r16, %r6
	and %r19, %r12, %r2
	and %r20, %r15, %r6
	xor %r21, %r17, %r20
	and %r22, %r19, %r21
	and %r23, %r12, %r20
	xor %r24, %r16, %r23
	or %r25, %r21, %r24
	xor %r6, %r12, %r6
	xor %r26, %r25, %r6
	or %r27, %r18, %r22
	xor %r27, %r27, %r22
	xor %r27, %r27, %r26
	xor %r2, %r2, %r11
	and %r2, %r2, %r14
	or %r26, %r21, %r2
	xor %r24, %r19, %r24
	xor %r26, %r26, %r24
	xor %r19, %r19, %r6
	or %r15, %r15, %r19
	xor %r15, %r15, %r19
	or %r6, %r21, %r15
	xor %r6, %r6, %r15
	xor %r14, %r14, %r24
	xor %r6, %r6, %r14
	or %r19, %r19, %r23
	xor %r19, %r19, %r23
	or %r15, %r15, %r19
	xor %r25, %r17, %r25
	and %r25, %r6, %r25
	xor %r25, %r15, %r25
	and %r23, %r25, %r18
	xor %r23, %r23, %r6
	or %r21, %r21, %r16
	xor %r21, %r21, %r16
	or %r19, %r19, %r21
	or %r20, %r20, %r6
	and %r19, %r19, %r20
	xor %r25, %r25, %r19
	xor %r2, %r2, %r15
	and %r12, %r12, %r2
	or %r22, %r22, %r12
	xor %r19, %r19, %r22
	or %r12, %r19, %r18
	xor %r12, %r12, %r18
	xor %r12, %r12, %r26
	and %r17, %r17, %r22
	xor %r26, %r26, %r11
	xor %r17, %r17, %r26
	xor %r19, %r19, %r17
	or %r25, %r25, %r18
	xor %r25, %r25, %r19
	ld %r0, 112(%r10)
	xor %r0, %r0, %r27
	std %r0, 112(%r10)
	ld %r0, 144(%r10)
	xor %r0, %r0, %r23
	std %r0, 144(%r10)
	ld %r0, 288(%r10)
	xor %r0, %r0, %r25
	std %r0, 288(%r10)
	ld %r0, 0(%r10)
	xor %r0, %r0, %r12
	std %r0, 0(%r10)
	rldicr %r12, %r9, 63, 0
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 504(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 62, 1
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 8(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 61, 2
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 72(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 60, 3
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 136(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 59, 4
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 200(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 58, 5
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 264(%r10)
	xor %r18, %r18, %r0
	or %r6, %r16, %r17
	xor %r6, %r6, %r17
	or %r2, %r14, %r16
	xor %r2, %r2, %r16
	xor %r2, %r15, %r2
	and %r19, %r18, %r2
	or %r20, %r19, %r6
	xor %r20, %r20, %r6
	or %r21, %r17, %r2
	xor %r21, %r21, %r2
	or %r22, %r18, %r21
	or %r23, %r17, %r16
	xor %r23, %r23, %r16
	xor %r23, %r14, %r23
	and %r24, %r22, %r23
	or %r19, %r19, %r24
	xor %r2, %r2, %r11
	xor %r24, %r24, %r2
	or %r16, %r16, %r22
	xor %r16, %r16, %r22
	xor %r24, %r24, %r16
	xor %r6, %r6, %r24
	or %r16, %r20, %r12
	xor %r16, %r16, %r6
	xor %r6, %r18, %r6
	and %r22, %r14, %r6
	xor %r24, %r17, %r24
	xor %r22, %r22, %r24
	xor %r21, %r21, %r22
	xor %r22, %r19, %r22
	or %r17, %r17, %r22
	xor %r14, %r14, %r6
	xor %r17, %r17, %r14
	and %r19, %r19, %r12
	xor %r19, %r19, %r17
	xor %r23, %r23, %r21
	or %r24, %r15, %r24
	xor %r24, %r23, %r24
	xor %r18, %r18, %r24
	and %r18, %r18, %r12
	xor %r18, %r18, %r21
	or %r23, %r23, %r15
	xor %r23, %r23, %r15
	and %r17, %r17, %r23
	xor %r20, %r20, %r24
	xor %r17, %r17, %r20
	or %r17, %r17, %r12
	xor %r17, %r17, %r21
	ld %r0, 208(%r10)
	xor %r0, %r0, %r18
	std %r0, 208(%r10)
	ld %r0, 96(%r10)
	xor %r0, %r0, %r19
	std %r0, 96(%r10)
	ld %r0, 320(%r10)
	xor %r0, %r0, %r16
	std %r0, 320(%r10)
	ld %r0, 240(%r10)
	xor %r0, %r0, %r17
	std %r0, 240(%r10)
	ld %r9, 0(%r3)
	xor %r9, %r9, %r11
	addi %r3, %r3, -8
	rldicr %r12, %r9, 21, 42
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 240(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 20, 43
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 304(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 19, 44
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 368(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 18, 45
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 432(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 17, 46
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 496(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 16, 47
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 0(%r10)
	xor %r18, %r18, %r0
	or %r6, %r18, %r14
	xor %r6, %r6, %r14
	xor %r2, %r15, %r6
	or %r19, %r16, %r12
	xor %r20, %r18, %r16
	and %r21, %r19, %r20
	xor %r22, %r15, %r21
	or %r23, %r22, %r2
	xor %r23, %r23, %r2
	xor %r24, %r14, %r12
	xor %r25, %r16, %r24
	xor %r25, %r25, %r11
	and %r25, %r25, %r2
	or %r21, %r12, %r21
	xor %r25, %r25, %r21
	or %r21, %r25, %r23
	xor %r21, %r21, %r23
	or %r12, %r18, %r12
	or %r26, %r25, %r12
	xor %r22, %r22, %r11
	and %r22, %r22, %r14
	xor %r27, %r26, %r22
	or %r15, %r15, %r12
	xor %r15, %r15, %r12
	xor %r15, %r22, %r15
	xor %r20, %r20, %r11
	and %r20, %r20, %r24
	or %r15, %r15, %r20
	or %r16, %r16, %r6
	xor %r16, %r16, %r6
	xor %r6, %r2, %r26
	or %r6, %r6, %r16
	xor %r6, %r6, %r16
	xor %r16, %r6, %r11
	and %r25, %r19, %r25
	xor %r16, %r16, %r25
	or %r27, %r27, %r17
	xor %r27, %r27, %r17
	xor %r27, %r27, %r16
	xor %r6, %r24, %r6
	or %r22, %r22, %r6
	xor %r22, %r19, %r22
	xor %r18, %r18, %r22
	xor %r16, %r16, %r18
	or %r23, %r23, %r17
	xor %r23, %r23, %r16
	xor %r19, %r19, %r26
	or %r19, %r15, %r19
	xor %r19, %r18, %r19
	or %r24, %r24, %r16
	xor %r24, %r19, %r24
	or %r16, %r21, %r17
	xor %r16, %r16, %r24
	or %r14, %r14, %r2
	or %r14, %r14, %r19
	xor %r14, %r14, %r19
	and %r21, %r21, %r18
	xor %r14, %r14, %r21
	or %r14, %r14, %r17
	xor %r14, %r14, %r15
	ld %r0, 72(%r10)
	xor %r0, %r0, %r14
	std %r0, 72(%r10)
	ld %r0, 88(%r10)
	xor %r0, %r0, %r27
	std %r0, 88(%r10)
	ld %r0, 472(%r10)
	xor %r0, %r0, %r16
	std %r0, 472(%r10)
	ld %r0, 488(%r10)
	xor %r0, %r0, %r23
	std %r0, 488(%r10)
	rldicr %r12, %r9, 27, 36
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 480(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 26, 37
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 48(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 25, 38
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 112(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 24, 39
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 176(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 23, 40
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 240(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 22, 41
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 304(%r10)
	xor %r18, %r18, %r0
	xor %r6, %r17, %r14
	or %r2, %r18, %r12
	xor %r2, %r2, %r12
	xor %r2, %r2, %r11
	and %r2, %r2, %r14
	or %r19, %r17, %r2
	or %r20, %r6, %r12
	xor %r20, %r20, %r12
	and %r21, %r18, %r6
	xor %r14, %r14, %r21
	or %r21, %r14, %r20
	xor %r21, %r21, %r20
	and %r22, %r16, %r12
	xor %r2, %r2, %r20
	and %r2, %r19, %r2
	or %r20, %r2, %r22
	xor %r20, %r20, %r22
	and %r23, %r16, %r2
	xor %r18, %r18, %r11
	xor %r18, %r23, %r18
	xor %r12, %r12, %r6
	or %r24, %r12, %r22
	xor %r24, %r24, %r22
	xor %r25, %r18, %r24
	xor %r20, %r20, %r11
	and %r20, %r20, %r15
	xor %r20, %r20, %r25
	or %r17, %r17, %r24
	xor %r17, %r17, %r24
	xor %r14, %r14, %r17
	or %r18, %r18, %r14
	xor %r18, %r18, %r14
	xor %r16, %r16, %r12
	xor %r18, %r18, %r16
	or %r24, %r19, %r15
	xor %r24, %r24, %r15
	xor %r24, %r24, %r18
	xor %r23, %r23, %r17
	or %r16, %r16, %r23
	xor %r19, %r19, %r25
	or %r22, %r22, %r19
	xor %r23, %r16, %r22
	xor %r2, %r2, %r25
	xor %r18, %r18, %r2
	and %r22, %r22, %r18
	and %r6, %r6, %r16
	xor %r22, %r22, %r6
	or %r6, %r22, %r15
	xor %r6, %r6, %r23
	or %r22, %r22, %r14
	xor %r22, %r22, %r14
	or %r12, %r12, %r19
	xor %r22, %r22, %r12
	or %r21, %r21, %r15
	xor %r21, %r21, %r22
	ld %r0, 408(%r10)
	xor %r0, %r0, %r21
	std %r0, 408(%r10)
	ld %r0, 440(%r10)
	xor %r0, %r0, %r6
	std %r0, 440(%r10)
	ld %r0, 264(%r10)
	xor %r0, %r0, %r20
	std %r0, 264(%r10)
	ld %r0, 232(%r10)
	xor %r0, %r0, %r24
	std %r0, 232(%r10)
	rldicr %r12, %r9, 33, 30
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 224(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 32, 31
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 288(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 31, 32
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 352(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 30, 33
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 416(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 29, 34
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 480(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 28, 35
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 48(%r10)
	xor %r18, %r18, %r0
	or %r6, %r18, %r17
	xor %r6, %r6, %r17
	xor %r2, %r16, %r12
	or %r19, %r6, %r2
	xor %r20, %r15, %r12
	or %r21, %r20, %r18
	xor %r21, %r21, %r18
	xor %r22, %r19, %r21
	xor %r23, %r17, %r2
	or %r24, %r23, %r12
	xor %r24, %r24, %r12
	xor %r19, %r19, %r24
	or %r24, %r22, %r19
	xor %r24, %r24, %r19
	and %r25, %r12, %r22
	or %r25, %r15, %r25
	and %r25, %r18, %r25
	xor %r25, %r23, %r25
	or %r26, %r22, %r14
	xor %r26, %r26, %r14
	xor %r26, %r26, %r25
	and %r2, %r2, %r20
	xor %r20, %r18, %r15
	xor %r27, %r19, %r20
	or %r27, %r16, %r27
	or %r27, %r27, %r2
	xor %r27, %r27, %r2
	or %r21, %r21, %r20
	or %r20, %r25, %r21
	xor %r20, %r20, %r21
	and %r12, %r15, %r12
	or %r2, %r12, %r17
	xor %r2, %r2, %r17
	xor %r20, %r20, %r2
	and %r19, %r19, %r20
	or %r12, %r23, %r12
	or %r12, %r12, %r19
	xor %r12, %r12, %r19
	xor %r18, %r18, %r12
	and %r27, %r27, %r14
	xor %r27, %r27, %r18
	xor %r22, %r22, %r11
	or %r17, %r17, %r22
	or %r16, %r16, %r17
	xor %r23, %r23, %r16
	xor %r21, %r21, %r23
	xor %r24, %r24, %r11
	and %r24, %r24, %r14
	xor %r24, %r24, %r21
	and %r15, %r15, %r22
	xor %r25, %r25, %r15
	or %r23, %r23, %r25
	xor %r6, %r6, %r18
	xor %r23, %r23, %r6
	or %r20, %r20, %r14
	xor %r20, %r20, %r23
	ld %r0, 184(%r10)
	xor %r0, %r0, %r26
	std %r0, 184(%r10)
	ld %r0, 136(%r10)
	xor %r0, %r0, %r20
	std %r0, 136(%r10)
	ld %r0, 40(%r10)
	xor %r0, %r0, %r27
	std %r0, 40(%r10)
	ld %r0, 24(%r10)
	xor %r0, %r0, %r24
	std %r0, 24(%r10)
	rldicr %r12, %r9, 39, 24
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 464(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 38, 25
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 32(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 37, 26
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 96(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 36, 27
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 160(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 35, 28
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 224(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 34, 29
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 288(%r10)
	xor %r18, %r18, %r0
	xor %r18, %r18, %r16
	xor %r16, %r16, %r14
	or %r6, %r17, %r15
	xor %r6, %r14, %r6
	xor %r6, %r6, %r11
	and %r6, %r6, %r16
	or %r2, %r16, %r17
	xor %r2, %r2, %r17
	xor %r19, %r15, %r2
	or %r20, %r18, %r19
	or %r20, %r20, %r6
	xor %r20, %r20, %r6
	xor %r21, %r17, %r20
	and %r19, %r19, %r21
	or %r16, %r16, %r19
	xor %r16, %r16, %r19
	xor %r18, %r18, %r21
	xor %r16, %r16, %r11
	and %r16, %r16, %r18
	xor %r6, %r6, %r16
	xor %r17, %r17, %r15
	or %r14, %r14, %r2
	xor %r18, %r18, %r14
	or %r14, %r18, %r17
	xor %r14, %r14, %r17
	xor %r20, %r20, %r14
	or %r14, %r12, %r6
	xor %r14, %r14, %r6
	xor %r14, %r14, %r20
	xor %r20, %r20, %r11
	or %r2, %r6, %r12
	xor %r2, %r2, %r12
	xor %r2, %r2, %r20
	xor %r6, %r6, %r20
	or %r6, %r6, %r17
	xor %r6, %r6, %r17
	or %r19, %r19, %r6
	xor %r18, %r18, %r19
	or %r19, %r21, %r12
	xor %r19, %r19, %r18
	and %r12, %r12, %r21
	xor %r12, %r12, %r18
	ld %r0, 504(%r10)
	xor %r0, %r0, %r12
	std %r0, 504(%r10)
	ld %r0, 424(%r10)
	xor %r0, %r0, %r19
	std %r0, 424(%r10)
	ld %r0, 280(%r10)
	xor %r0, %r0, %r2
	std %r0, 280(%r10)
	ld %r0, 392(%r10)
	xor %r0, %r0, %r14
	std %r0, 392(%r10)
	rldicr %r12, %r9, 45, 18
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 208(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 44, 19
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 272(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 43, 20
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 336(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 42, 21
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 400(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 41, 22
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 464(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 40, 23
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 32(%r10)
	xor %r18, %r18, %r0
	or %r6, %r18, %r16
	or %r2, %r6, %r12
	xor %r2, %r2, %r12
	xor %r19, %r18, %r2
	xor %r20, %r16, %r19
	or %r21, %r15, %r20
	or %r2, %r2, %r15
	xor %r2, %r2, %r15
	xor %r16, %r16, %r2
	and %r2, %r14, %r16
	or %r20, %r18, %r20
	xor %r2, %r2, %r20
	xor %r2, %r15, %r2
	xor %r12, %r12, %r2
	or %r22, %r19, %r12
	and %r23, %r14, %r22
	xor %r24, %r19, %r23
	and %r25, %r15, %r20
	xor %r24, %r24, %r25
	or %r22, %r22, %r18
	xor %r22, %r22, %r18
	xor %r25, %r16, %r22
	xor %r14, %r14, %r21
	xor %r25, %r25, %r11
	and %r25, %r25, %r14
	xor %r25, %r25, %r11
	or %r25, %r25, %r17
	xor %r25, %r25, %r17
	xor %r25, %r25, %r2
	or %r2, %r16, %r23
	xor %r2, %r2, %r23
	xor %r22, %r22, %r14
	or %r22, %r24, %r22
	or %r22, %r22, %r2
	xor %r22, %r22, %r2
	or %r2, %r21, %r22
	xor %r2, %r2, %r22
	and %r12, %r12, %r22
	xor %r14, %r14, %r12
	and %r20, %r16, %r20
	or %r20, %r14, %r20
	xor %r23, %r23, %r20
	and %r23, %r23, %r17
	xor %r23, %r23, %r24
	xor %r18, %r18, %r6
	xor %r22, %r22, %r18
	and %r15, %r15, %r14
	xor %r22, %r22, %r15
	or %r2, %r2, %r17
	xor %r2, %r2, %r22
	xor %r16, %r21, %r16
	or %r16, %r16, %r22
	xor %r16, %r16, %r22
	xor %r19, %r19, %r14
	xor %r16, %r16, %r19
	and %r21, %r21, %r17
	xor %r21, %r21, %r16
	ld %r0, 376(%r10)
	xor %r0, %r0, %r23
	std %r0, 376(%r10)
	ld %r0, 456(%r10)
	xor %r0, %r0, %r25
	std %r0, 456(%r10)
	ld %r0, 168(%r10)
	xor %r0, %r0, %r21
	std %r0, 168(%r10)
	ld %r0, 56(%r10)
	xor %r0, %r0, %r2
	std %r0, 56(%r10)
	rldicr %r12, %r9, 51, 12
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 448(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 50, 13
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 16(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 49, 14
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 80(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 48, 15
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 144(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 47, 16
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 208(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 46, 17
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 272(%r10)
	xor %r18, %r18, %r0
	xor %r6, %r17, %r14
	or %r2, %r17, %r12
	and %r2, %r18, %r2
	xor %r6, %r6, %r2
	xor %r19, %r12, %r6
	or %r20, %r14, %r19
	xor %r20, %r20, %r19
	and %r19, %r18, %r19
	xor %r21, %r17, %r19
	xor %r22, %r18, %r16
	or %r23, %r21, %r22
	xor %r24, %r6, %r23
	and %r25, %r16, %r24
	or %r26, %r25, %r12
	xor %r26, %r26, %r12
	or %r21, %r20, %r21
	xor %r27, %r26, %r21
	and %r28, %r27, %r15
	xor %r28, %r28, %r24
	xor %r23, %r17, %r23
	or %r29, %r12, %r23
	xor %r29, %r29, %r23
	xor %r16, %r16, %r29
	or %r29, %r14, %r25
	xor %r29, %r29, %r25
	or %r29, %r16, %r29
	or %r17, %r17, %r22
	xor %r27, %r27, %r17
	or %r2, %r2, %r29
	xor %r27, %r27, %r2
	or %r24, %r18, %r24
	and %r21, %r21, %r24
	xor %r21, %r16, %r21
	xor %r26, %r26, %r11
	and %r26, %r26, %r21
	or %r20, %r20, %r15
	xor %r20, %r20, %r26
	xor %r6, %r6, %r21
	or %r14, %r14, %r6
	xor %r14, %r14, %r6
	xor %r17, %r17, %r11
	xor %r23, %r23, %r17
	xor %r14, %r14, %r23
	or %r14, %r14, %r15
	xor %r14, %r14, %r15
	xor %r14, %r14, %r27
	xor %r12, %r12, %r19
	xor %r18, %r18, %r16
	and %r12, %r12, %r18
	xor %r25, %r25, %r23
	xor %r12, %r12, %r25
	or %r29, %r29, %r15
	xor %r29, %r29, %r15
	xor %r29, %r29, %r12
	ld %r0, 344(%r10)
	xor %r0, %r0, %r28
	std %r0, 344(%r10)
	ld %r0, 360(%r10)
	xor %r0, %r0, %r20
	std %r0, 360(%r10)
	ld %r0, 200(%r10)
	xor %r0, %r0, %r14
	std %r0, 200(%r10)
	ld %r0, 312(%r10)
	xor %r0, %r0, %r29
	std %r0, 312(%r10)
	rldicr %r12, %r9, 57, 6
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 192(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 56, 7
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 256(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 55, 8
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 320(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 54, 9
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 384(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 53, 10
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 448(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 52, 11
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 16(%r10)
	xor %r18, %r18, %r0
	xor %r6, %r15, %r14
	xor %r2, %r16, %r6
	and %r19, %r12, %r2
	and %r20, %r15, %r6
	xor %r21, %r17, %r20
	and %r22, %r19, %r21
	and %r23, %r12, %r20
	xor %r24, %r16, %r23
	or %r25, %r21, %r24
	xor %r6, %r12, %r6
	xor %r26, %r25, %r6
	or %r27, %r18, %r22
	xor %r27, %r27, %r22
	xor %r27, %r27, %r26
	xor %r2, %r2, %r11
	and %r2, %r2, %r14
	or %r26, %r21, %r2
	xor %r24, %r19, %r24
	xor %r26, %r26, %r24
	xor %r19, %r19, %r6
	or %r15, %r15, %r19
	xor %r15, %r15, %r19
	or %r6, %r21, %r15
	xor %r6, %r6, %r15
	xor %r14, %r14, %r24
	xor %r6, %r6, %r14
	or %r19, %r19, %r23
	xor %r19, %r19, %r23
	or %r15, %r15, %r19
	xor %r25, %r17, %r25
	and %r25, %r6, %r25
	xor %r25, %r15, %r25
	and %r23, %r25, %r18
	xor %r23, %r23, %r6
	or %r21, %r21, %r16
	xor %r21, %r21, %r16
	or %r19, %r19, %r21
	or %r20, %r20, %r6
	and %r19, %r19, %r20
	xor %r25, %r25, %r19
	xor %r2, %r2, %r15
	and %r12, %r12, %r2
	or %r22, %r22, %r12
	xor %r19, %r19, %r22
	or %r12, %r19, %r18
	xor %r12, %r12, %r18
	xor %r12, %r12, %r26
	and %r17, %r17, %r22
	xor %r26, %r26, %r11
	xor %r17, %r17, %r26
	xor %r19, %r19, %r17
	or %r25, %r25, %r18
	xor %r25, %r25, %r19
	ld %r0, 120(%r10)
	xor %r0, %r0, %r27
	std %r0, 120(%r10)
	ld %r0, 152(%r10)
	xor %r0, %r0, %r23
	std %r0, 152(%r10)
	ld %r0, 296(%r10)
	xor %r0, %r0, %r25
	std %r0, 296(%r10)
	ld %r0, 8(%r10)
	xor %r0, %r0, %r12
	std %r0, 8(%r10)
	rldicr %r12, %r9, 63, 0
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 496(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 62, 1
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 0(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 61, 2
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 64(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 60, 3
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 128(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 59, 4
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 192(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 58, 5
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 256(%r10)
	xor %r18, %r18, %r0
	or %r6, %r16, %r17
	xor %r6, %r6, %r17
	or %r2, %r14, %r16
	xor %r2, %r2, %r16
	xor %r2, %r15, %r2
	and %r19, %r18, %r2
	or %r20, %r19, %r6
	xor %r20, %r20, %r6
	or %r21, %r17, %r2
	xor %r21, %r21, %r2
	or %r22, %r18, %r21
	or %r23, %r17, %r16
	xor %r23, %r23, %r16
	xor %r23, %r14, %r23
	and %r24, %r22, %r23
	or %r19, %r19, %r24
	xor %r2, %r2, %r11
	xor %r24, %r24, %r2
	or %r16, %r16, %r22
	xor %r16, %r16, %r22
	xor %r24, %r24, %r16
	xor %r6, %r6, %r24
	or %r16, %r20, %r12
	xor %r16, %r16, %r6
	xor %r6, %r18, %r6
	and %r22, %r14, %r6
	xor %r24, %r17, %r24
	xor %r22, %r22, %r24
	xor %r21, %r21, %r22
	xor %r22, %r19, %r22
	or %r17, %r17, %r22
	xor %r14, %r14, %r6
	xor %r17, %r17, %r14
	and %r19, %r19, %r12
	xor %r19, %r19, %r17
	xor %r23, %r23, %r21
	or %r24, %r15, %r24
	xor %r24, %r23, %r24
	xor %r18, %r18, %r24
	and %r18, %r18, %r12
	xor %r18, %r18, %r21
	or %r23, %r23, %r15
	xor %r23, %r23, %r15
	and %r17, %r17, %r23
	xor %r20, %r20, %r24
	xor %r17, %r17, %r20
	or %r17, %r17, %r12
	xor %r17, %r17, %r21
	ld %r0, 216(%r10)
	xor %r0, %r0, %r18
	std %r0, 216(%r10)
	ld %r0, 104(%r10)
	xor %r0, %r0, %r19
	std %r0, 104(%r10)
	ld %r0, 328(%r10)
	xor %r0, %r0, %r16
	std %r0, 328(%r10)
	ld %r0, 248(%r10)
	xor %r0, %r0, %r17
	std %r0, 248(%r10)
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 28b
	ld %r12, 0(%r10)
	ld %r14, 8(%r10)
	std %r14, 0(%r10)
	std %r12, 8(%r10)
	ld %r12, 64(%r10)
	ld %r14, 72(%r10)
	std %r14, 64(%r10)
	std %r12, 72(%r10)
	ld %r12, 128(%r10)
	ld %r14, 136(%r10)
	std %r14, 128(%r10)
	std %r12, 136(%r10)
	ld %r12, 192(%r10)
	ld %r14, 200(%r10)
	std %r14, 192(%r10)
	std %r12, 200(%r10)
	ld %r12, 256(%r10)
	ld %r14, 264(%r10)
	std %r14, 256(%r10)
	std %r12, 264(%r10)
	ld %r12, 320(%r10)
	ld %r14, 328(%r10)
	std %r14, 320(%r10)
	std %r12, 328(%r10)
	ld %r12, 384(%r10)
	ld %r14, 392(%r10)
	std %r14, 384(%r10)
	std %r12, 392(%r10)
	ld %r12, 448(%r10)
	ld %r14, 456(%r10)
	std %r14, 448(%r10)
	std %r12, 456(%r10)
	ld %r12, 16(%r10)
	ld %r14, 24(%r10)
	std %r14, 16(%r10)
	std %r12, 24(%r10)
	ld %r12, 80(%r10)
	ld %r14, 88(%r10)
	std %r14, 80(%r10)
	std %r12, 88(%r10)
	ld %r12, 144(%r10)
	ld %r14, 152(%r10)
	std %r14, 144(%r10)
	std %r12, 152(%r10)
	ld %r12, 208(%r10)
	ld %r14, 216(%r10)
	std %r14, 208(%r10)
	std %r12, 216(%r10)
	ld %r12, 272(%r10)
	ld %r14, 280(%r10)
	std %r14, 272(%r10)
	std %r12, 280(%r10)
	ld %r12, 336(%r10)
	ld %r14, 344(%r10)
	std %r14, 336(%r10)
	std %r12, 344(%r10)
	ld %r12, 400(%r10)
	ld %r14, 408(%r10)
	std %r14, 400(%r10)
	std %r12, 408(%r10)
	ld %r12, 464(%r10)
	ld %r14, 472(%r10)
	std %r14, 464(%r10)
	std %r12, 472(%r10)
	ld %r12, 32(%r10)
	ld %r14, 40(%r10)
	std %r14, 32(%r10)
	std %r12, 40(%r10)
	ld %r12, 96(%r10)
	ld %r14, 104(%r10)
	std %r14, 96(%r10)
	std %r12, 104(%r10)
	ld %r12, 160(%r10)
	ld %r14, 168(%r10)
	std %r14, 160(%r10)
	std %r12, 168(%r10)
	ld %r12, 224(%r10)
	ld %r14, 232(%r10)
	std %r14, 224(%r10)
	std %r12, 232(%r10)
	ld %r12, 288(%r10)
	ld %r14, 296(%r10)
	std %r14, 288(%r10)
	std %r12, 296(%r10)
	ld %r12, 352(%r10)
	ld %r14, 360(%r10)
	std %r14, 352(%r10)
	std %r12, 360(%r10)
	ld %r12, 416(%r10)
	ld %r14, 424(%r10)
	std %r14, 416(%r10)
	std %r12, 424(%r10)
	ld %r12, 480(%r10)
	ld %r14, 488(%r10)
	std %r14, 480(%r10)
	std %r12, 488(%r10)
	ld %r12, 48(%r10)
	ld %r14, 56(%r10)
	std %r14, 48(%r10)
	std %r12, 56(%r10)
	ld %r12, 112(%r10)
	ld %r14, 120(%r10)
	std %r14, 112(%r10)
	std %r12, 120(%r10)
	ld %r12, 176(%r10)
	ld %r14, 184(%r10)
	std %r14, 176(%r10)
	std %r12, 184(%r10)
	ld %r12, 240(%r10)
	ld %r14, 248(%r10)
	std %r14, 240(%r10)
	std %r12, 248(%r10)
	ld %r12, 304(%r10)
	ld %r14, 312(%r10)
	std %r14, 304(%r10)
	std %r12, 312(%r10)
	ld %r12, 368(%r10)
	ld %r14, 376(%r10)
	std %r14, 368(%r10)
	std %r12, 376(%r10)
	ld %r12, 432(%r10)
	ld %r14, 440(%r10)
	std %r14, 432(%r10)
	std %r12, 440(%r10)
	ld %r12, 496(%r10)
	ld %r14, 504(%r10)
	std %r14, 496(%r10)
	std %r12, 504(%r10)
	addi %r25, %r10, 512
	ld %r21, 0(%r25)
	ld %r22, 8(%r25)
	ld %r23, 16(%r25)
	ld %r12, 0(%r10)
	ld %r14, 64(%r10)
	ld %r15, 128(%r10)
	ld %r16, 192(%r10)
	ld %r17, 256(%r10)
	ld %r18, 320(%r10)
	ld %r19, 384(%r10)
	ld %r20, 448(%r10)
	rldicl %r24, %r12, 32, 32
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 32, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 32, 32
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 32, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 32, 32
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 32, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 32, 32
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 32, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 48, 16
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 16, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 48, 16
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 16, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 48, 16
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 16, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 48, 16
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 16, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 56, 8
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 8, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 56, 8
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 8, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 56, 8
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 8, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 56, 8
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 8, 0
	xor %r19, %r19, %r24
	std %r12, 0(%r10)
	std %r14, 64(%r10)
	std %r15, 128(%r10)
	std %r16, 192(%r10)
	std %r17, 256(%r10)
	std %r18, 320(%r10)
	std %r19, 384(%r10)
	std %r20, 448(%r10)
	ld %r12, 8(%r10)
	ld %r14, 72(%r10)
	ld %r15, 136(%r10)
	ld %r16, 200(%r10)
	ld %r17, 264(%r10)
	ld %r18, 328(%r10)
	ld %r19, 392(%r10)
	ld %r20, 456(%r10)
	rldicl %r24, %r12, 32, 32
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 32, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 32, 32
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 32, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 32, 32
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 32, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 32, 32
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 32, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 48, 16
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 16, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 48, 16
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 16, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 48, 16
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 16, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 48, 16
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 16, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 56, 8
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 8, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 56, 8
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 8, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 56, 8
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 8, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 56, 8
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 8, 0
	xor %r19, %r19, %r24
	std %r12, 8(%r10)
	std %r14, 72(%r10)
	std %r15, 136(%r10)
	std %r16, 200(%r10)
	std %r17, 264(%r10)
	std %r18, 328(%r10)
	std %r19, 392(%r10)
	std %r20, 456(%r10)
	ld %r12, 16(%r10)
	ld %r14, 80(%r10)
	ld %r15, 144(%r10)
	ld %r16, 208(%r10)
	ld %r17, 272(%r10)
	ld %r18, 336(%r10)
	ld %r19, 400(%r10)
	ld %r20, 464(%r10)
	rldicl %r24, %r12, 32, 32
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 32, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 32, 32
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 32, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 32, 32
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 32, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 32, 32
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 32, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 48, 16
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 16, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 48, 16
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 16, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 48, 16
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 16, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 48, 16
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 16, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 56, 8
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 8, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 56, 8
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 8, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 56, 8
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 8, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 56, 8
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 8, 0
	xor %r19, %r19, %r24
	std %r12, 16(%r10)
	std %r14, 80(%r10)
	std %r15, 144(%r10)
	std %r16, 208(%r10)
	std %r17, 272(%r10)
	std %r18, 336(%r10)
	std %r19, 400(%r10)
	std %r20, 464(%r10)
	ld %r12, 24(%r10)
	ld %r14, 88(%r10)
	ld %r15, 152(%r10)
	ld %r16, 216(%r10)
	ld %r17, 280(%r10)
	ld %r18, 344(%r10)
	ld %r19, 408(%r10)
	ld %r20, 472(%r10)
	rldicl %r24, %r12, 32, 32
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 32, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 32, 32
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 32, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 32, 32
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 32, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 32, 32
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 32, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 48, 16
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 16, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 48, 16
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 16, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 48, 16
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 16, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 48, 16
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 16, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 56, 8
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 8, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 56, 8
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 8, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 56, 8
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 8, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 56, 8
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 8, 0
	xor %r19, %r19, %r24
	std %r12, 24(%r10)
	std %r14, 88(%r10)
	std %r15, 152(%r10)
	std %r16, 216(%r10)
	std %r17, 280(%r10)
	std %r18, 344(%r10)
	std %r19, 408(%r10)
	std %r20, 472(%r10)
	ld %r12, 32(%r10)
	ld %r14, 96(%r10)
	ld %r15, 160(%r10)
	ld %r16, 224(%r10)
	ld %r17, 288(%r10)
	ld %r18, 352(%r10)
	ld %r19, 416(%r10)
	ld %r20, 480(%r10)
	rldicl %r24, %r12, 32, 32
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 32, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 32, 32
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 32, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 32, 32
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 32, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 32, 32
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 32, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 48, 16
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 16, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 48, 16
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 16, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 48, 16
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 16, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 48, 16
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 16, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 56, 8
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 8, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 56, 8
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 8, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 56, 8
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 8, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 56, 8
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 8, 0
	xor %r19, %r19, %r24
	std %r12, 32(%r10)
	std %r14, 96(%r10)
	std %r15, 160(%r10)
	std %r16, 224(%r10)
	std %r17, 288(%r10)
	std %r18, 352(%r10)
	std %r19, 416(%r10)
	std %r20, 480(%r10)
	ld %r12, 40(%r10)
	ld %r14, 104(%r10)
	ld %r15, 168(%r10)
	ld %r16, 232(%r10)
	ld %r17, 296(%r10)
	ld %r18, 360(%r10)
	ld %r19, 424(%r10)
	ld %r20, 488(%r10)
	rldicl %r24, %r12, 32, 32
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 32, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 32, 32
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 32, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 32, 32
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 32, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 32, 32
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 32, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 48, 16
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 16, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 48, 16
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 16, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 48, 16
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 16, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 48, 16
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 16, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 56, 8
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 8, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 56, 8
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 8, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 56, 8
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 8, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 56, 8
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 8, 0
	xor %r19, %r19, %r24
	std %r12, 40(%r10)
	std %r14, 104(%r10)
	std %r15, 168(%r10)
	std %r16, 232(%r10)
	std %r17, 296(%r10)
	std %r18, 360(%r10)
	std %r19, 424(%r10)
	std %r20, 488(%r10)
	ld %r12, 48(%r10)
	ld %r14, 112(%r10)
	ld %r15, 176(%r10)
	ld %r16, 240(%r10)
	ld %r17, 304(%r10)
	ld %r18, 368(%r10)
	ld %r19, 432(%r10)
	ld %r20, 496(%r10)
	rldicl %r24, %r12, 32, 32
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 32, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 32, 32
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 32, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 32, 32
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 32, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 32, 32
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 32, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 48, 16
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 16, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 48, 16
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 16, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 48, 16
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 16, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 48, 16
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 16, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 56, 8
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 8, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 56, 8
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 8, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 56, 8
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 8, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 56, 8
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 8, 0
	xor %r19, %r19, %r24
	std %r12, 48(%r10)
	std %r14, 112(%r10)
	std %r15, 176(%r10)
	std %r16, 240(%r10)
	std %r17, 304(%r10)
	std %r18, 368(%r10)
	std %r19, 432(%r10)
	std %r20, 496(%r10)
	ld %r12, 56(%r10)
	ld %r14, 120(%r10)
	ld %r15, 184(%r10)
	ld %r16, 248(%r10)
	ld %r17, 312(%r10)
	ld %r18, 376(%r10)
	ld %r19, 440(%r10)
	ld %r20, 504(%r10)
	rldicl %r24, %r12, 32, 32
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 32, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 32, 32
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 32, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 32, 32
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 32, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 32, 32
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 32, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 48, 16
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 16, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 48, 16
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 16, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 48, 16
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 16, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 48, 16
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 16, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 56, 8
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 8, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 56, 8
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 8, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 56, 8
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 8, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 56, 8
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 8, 0
	xor %r19, %r19, %r24
	std %r12, 56(%r10)
	std %r14, 120(%r10)
	std %r15, 184(%r10)
	std %r16, 248(%r10)
	std %r17, 312(%r10)
	std %r18, 376(%r10)
	std %r19, 440(%r10)
	std %r20, 504(%r10)
	ld %r21, 24(%r25)
	ld %r22, 32(%r25)
	ld %r23, 40(%r25)
	ld %r12, 0(%r10)
	ld %r14, 8(%r10)
	ld %r15, 16(%r10)
	ld %r16, 24(%r10)
	ld %r17, 32(%r10)
	ld %r18, 40(%r10)
	ld %r19, 48(%r10)
	ld %r20, 56(%r10)
	rldicl %r24, %r12, 60, 4
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 4, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 60, 4
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 4, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 60, 4
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 4, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 60, 4
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 4, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 62, 2
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 2, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 62, 2
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 2, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 62, 2
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 2, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 62, 2
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 2, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 63, 1
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 1, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 63, 1
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 1, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 63, 1
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 1, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 63, 1
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 1, 0
	xor %r19, %r19, %r24
	std %r12, 0(%r10)
	std %r14, 8(%r10)
	std %r15, 16(%r10)
	std %r16, 24(%r10)
	std %r17, 32(%r10)
	std %r18, 40(%r10)
	std %r19, 48(%r10)
	std %r20, 56(%r10)
	ld %r12, 64(%r10)
	ld %r14, 72(%r10)
	ld %r15, 80(%r10)
	ld %r16, 88(%r10)
	ld %r17, 96(%r10)
	ld %r18, 104(%r10)
	ld %r19, 112(%r10)
	ld %r20, 120(%r10)
	rldicl %r24, %r12, 60, 4
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 4, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 60, 4
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 4, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 60, 4
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 4, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 60, 4
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 4, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 62, 2
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 2, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 62, 2
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 2, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 62, 2
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 2, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 62, 2
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 2, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 63, 1
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 1, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 63, 1
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 1, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 63, 1
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 1, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 63, 1
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 1, 0
	xor %r19, %r19, %r24
	std %r12, 64(%r10)
	std %r14, 72(%r10)
	std %r15, 80(%r10)
	std %r16, 88(%r10)
	std %r17, 96(%r10)
	std %r18, 104(%r10)
	std %r19, 112(%r10)
	std %r20, 120(%r10)
	ld %r12, 128(%r10)
	ld %r14, 136(%r10)
	ld %r15, 144(%r10)
	ld %r16, 152(%r10)
	ld %r17, 160(%r10)
	ld %r18, 168(%r10)
	ld %r19, 176(%r10)
	ld %r20, 184(%r10)
	rldicl %r24, %r12, 60, 4
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 4, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 60, 4
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 4, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 60, 4
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 4, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 60, 4
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 4, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 62, 2
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 2, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 62, 2
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 2, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 62, 2
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 2, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 62, 2
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 2, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 63, 1
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 1, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 63, 1
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 1, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 63, 1
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 1, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 63, 1
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 1, 0
	xor %r19, %r19, %r24
	std %r12, 128(%r10)
	std %r14, 136(%r10)
	std %r15, 144(%r10)
	std %r16, 152(%r10)
	std %r17, 160(%r10)
	std %r18, 168(%r10)
	std %r19, 176(%r10)
	std %r20, 184(%r10)
	ld %r12, 192(%r10)
	ld %r14, 200(%r10)
	ld %r15, 208(%r10)
	ld %r16, 216(%r10)
	ld %r17, 224(%r10)
	ld %r18, 232(%r10)
	ld %r19, 240(%r10)
	ld %r20, 248(%r10)
	rldicl %r24, %r12, 60, 4
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 4, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 60, 4
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 4, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 60, 4
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 4, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 60, 4
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 4, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 62, 2
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 2, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 62, 2
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 2, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 62, 2
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 2, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 62, 2
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 2, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 63, 1
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 1, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 63, 1
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 1, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 63, 1
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 1, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 63, 1
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 1, 0
	xor %r19, %r19, %r24
	std %r12, 192(%r10)
	std %r14, 200(%r10)
	std %r15, 208(%r10)
	std %r16, 216(%r10)
	std %r17, 224(%r10)
	std %r18, 232(%r10)
	std %r19, 240(%r10)
	std %r20, 248(%r10)
	ld %r12, 256(%r10)
	ld %r14, 264(%r10)
	ld %r15, 272(%r10)
	ld %r16, 280(%r10)
	ld %r17, 288(%r10)
	ld %r18, 296(%r10)
	ld %r19, 304(%r10)
	ld %r20, 312(%r10)
	rldicl %r24, %r12, 60, 4
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 4, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 60, 4
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 4, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 60, 4
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 4, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 60, 4
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 4, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 62, 2
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 2, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 62, 2
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 2, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 62, 2
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 2, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 62, 2
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 2, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 63, 1
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 1, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 63, 1
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 1, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 63, 1
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 1, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 63, 1
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 1, 0
	xor %r19, %r19, %r24
	std %r12, 256(%r10)
	std %r14, 264(%r10)
	std %r15, 272(%r10)
	std %r16, 280(%r10)
	std %r17, 288(%r10)
	std %r18, 296(%r10)
	std %r19, 304(%r10)
	std %r20, 312(%r10)
	ld %r12, 320(%r10)
	ld %r14, 328(%r10)
	ld %r15, 336(%r10)
	ld %r16, 344(%r10)
	ld %r17, 352(%r10)
	ld %r18, 360(%r10)
	ld %r19, 368(%r10)
	ld %r20, 376(%r10)
	rldicl %r24, %r12, 60, 4
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 4, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 60, 4
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 4, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 60, 4
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 4, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 60, 4
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 4, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 62, 2
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 2, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 62, 2
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 2, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 62, 2
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 2, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 62, 2
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 2, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 63, 1
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 1, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 63, 1
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 1, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 63, 1
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 1, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 63, 1
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 1, 0
	xor %r19, %r19, %r24
	std %r12, 320(%r10)
	std %r14, 328(%r10)
	std %r15, 336(%r10)
	std %r16, 344(%r10)
	std %r17, 352(%r10)
	std %r18, 360(%r10)
	std %r19, 368(%r10)
	std %r20, 376(%r10)
	ld %r12, 384(%r10)
	ld %r14, 392(%r10)
	ld %r15, 400(%r10)
	ld %r16, 408(%r10)
	ld %r17, 416(%r10)
	ld %r18, 424(%r10)
	ld %r19, 432(%r10)
	ld %r20, 440(%r10)
	rldicl %r24, %r12, 60, 4
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 4, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 60, 4
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 4, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 60, 4
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 4, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 60, 4
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 4, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 62, 2
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 2, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 62, 2
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 2, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 62, 2
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 2, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 62, 2
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 2, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 63, 1
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 1, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 63, 1
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 1, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 63, 1
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 1, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 63, 1
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 1, 0
	xor %r19, %r19, %r24
	std %r12, 384(%r10)
	std %r14, 392(%r10)
	std %r15, 400(%r10)
	std %r16, 408(%r10)
	std %r17, 416(%r10)
	std %r18, 424(%r10)
	std %r19, 432(%r10)
	std %r20, 440(%r10)
	ld %r12, 448(%r10)
	ld %r14, 456(%r10)
	ld %r15, 464(%r10)
	ld %r16, 472(%r10)
	ld %r17, 480(%r10)
	ld %r18, 488(%r10)
	ld %r19, 496(%r10)
	ld %r20, 504(%r10)
	rldicl %r24, %r12, 60, 4
	xor %r24, %r24, %r17
	and %r24, %r24, %r21
	xor %r17, %r17, %r24
	rldicl %r24, %r24, 4, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 60, 4
	xor %r24, %r24, %r18
	and %r24, %r24, %r21
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 4, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r15, 60, 4
	xor %r24, %r24, %r19
	and %r24, %r24, %r21
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 4, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r16, 60, 4
	xor %r24, %r24, %r20
	and %r24, %r24, %r21
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 4, 0
	xor %r16, %r16, %r24
	rldicl %r24, %r12, 62, 2
	xor %r24, %r24, %r15
	and %r24, %r24, %r22
	xor %r15, %r15, %r24
	rldicl %r24, %r24, 2, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r14, 62, 2
	xor %r24, %r24, %r16
	and %r24, %r24, %r22
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 2, 0
	xor %r14, %r14, %r24
	rldicl %r24, %r17, 62, 2
	xor %r24, %r24, %r19
	and %r24, %r24, %r22
	xor %r19, %r19, %r24
	rldicl %r24, %r24, 2, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r18, 62, 2
	xor %r24, %r24, %r20
	and %r24, %r24, %r22
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 2, 0
	xor %r18, %r18, %r24
	rldicl %r24, %r12, 63, 1
	xor %r24, %r24, %r14
	and %r24, %r24, %r23
	xor %r14, %r14, %r24
	rldicl %r24, %r24, 1, 0
	xor %r12, %r12, %r24
	rldicl %r24, %r15, 63, 1
	xor %r24, %r24, %r16
	and %r24, %r24, %r23
	xor %r16, %r16, %r24
	rldicl %r24, %r24, 1, 0
	xor %r15, %r15, %r24
	rldicl %r24, %r17, 63, 1
	xor %r24, %r24, %r18
	and %r24, %r24, %r23
	xor %r18, %r18, %r24
	rldicl %r24, %r24, 1, 0
	xor %r17, %r17, %r24
	rldicl %r24, %r19, 63, 1
	xor %r24, %r24, %r20
	and %r24, %r24, %r23
	xor %r20, %r20, %r24
	rldicl %r24, %r24, 1, 0
	xor %r19, %r19, %r24
	std %r12, 448(%r10)
	std %r14, 456(%r10)
	std %r15, 464(%r10)
	std %r16, 472(%r10)
	std %r17, 480(%r10)
	std %r18, 488(%r10)
	std %r19, 496(%r10)
	std %r20, 504(%r10)
	rldicl %r12, %r8, 58, 6
	cmpldi %cr0, %r12, 0
	beq %cr0, 29f
	li %r12, 64
	b 210f
29:
	or %r12, %r8, %r8
210:
	or %r3, %r10, %r10
	or %r9, %r4, %r4
	or %r5, %r12, %r12
211:
	ld %r0, 0(%r3)
	std %r0, 0(%r9)
	addi %r3, %r3, 8
	addi %r9, %r9, 8
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 211b
	or %r4, %r9, %r9
	subf %r8, %r12, %r8
	cmpldi %cr0, %r8, 0
	bne %cr0, 22b
	ld %r2, 560(%r10)
	ld %r14, 568(%r10)
	ld %r15, 576(%r10)
	ld %r16, 584(%r10)
	ld %r17, 592(%r10)
	ld %r18, 600(%r10)
	ld %r19, 608(%r10)
	ld %r20, 616(%r10)
	ld %r21, 624(%r10)
	ld %r22, 632(%r10)
	ld %r23, 640(%r10)
	ld %r24, 648(%r10)
	ld %r25, 656(%r10)
	ld %r26, 664(%r10)
	ld %r27, 672(%r10)
	ld %r28, 680(%r10)
	ld %r29, 688(%r10)
	ld %r30, 696(%r10)
	ld %r31, 704(%r10)
	b 21f
20:
21:
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
