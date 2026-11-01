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

vg_triple_des_encrypt_block:
	std %r14, 0(%r5)
	std %r15, 8(%r5)
	std %r16, 16(%r5)
	std %r17, 24(%r5)
	std %r18, 32(%r5)
	std %r19, 40(%r5)
	std %r20, 48(%r5)
	std %r21, 56(%r5)
	std %r22, 64(%r5)
	std %r23, 72(%r5)
	std %r24, 80(%r5)
	std %r25, 88(%r5)
	std %r26, 96(%r5)
	std %r27, 104(%r5)
	std %r28, 112(%r5)
	li %r6, 0
	ldbrx %r7, %r4, %r6
	li %r8, 0
	li %r10, 1
	rldicl %r9, %r7, 58, 6
	and %r9, %r9, %r10
	rldicl %r9, %r9, 63, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 50, 14
	and %r9, %r9, %r10
	rldicl %r9, %r9, 62, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 42, 22
	and %r9, %r9, %r10
	rldicl %r9, %r9, 61, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 34, 30
	and %r9, %r9, %r10
	rldicl %r9, %r9, 60, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 26, 38
	and %r9, %r9, %r10
	rldicl %r9, %r9, 59, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 18, 46
	and %r9, %r9, %r10
	rldicl %r9, %r9, 58, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 10, 54
	and %r9, %r9, %r10
	rldicl %r9, %r9, 57, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 2, 62
	and %r9, %r9, %r10
	rldicl %r9, %r9, 56, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 60, 4
	and %r9, %r9, %r10
	rldicl %r9, %r9, 55, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 52, 12
	and %r9, %r9, %r10
	rldicl %r9, %r9, 54, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 44, 20
	and %r9, %r9, %r10
	rldicl %r9, %r9, 53, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 36, 28
	and %r9, %r9, %r10
	rldicl %r9, %r9, 52, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 28, 36
	and %r9, %r9, %r10
	rldicl %r9, %r9, 51, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 20, 44
	and %r9, %r9, %r10
	rldicl %r9, %r9, 50, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 12, 52
	and %r9, %r9, %r10
	rldicl %r9, %r9, 49, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 4, 60
	and %r9, %r9, %r10
	rldicl %r9, %r9, 48, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 62, 2
	and %r9, %r9, %r10
	rldicl %r9, %r9, 47, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 54, 10
	and %r9, %r9, %r10
	rldicl %r9, %r9, 46, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 46, 18
	and %r9, %r9, %r10
	rldicl %r9, %r9, 45, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 38, 26
	and %r9, %r9, %r10
	rldicl %r9, %r9, 44, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 30, 34
	and %r9, %r9, %r10
	rldicl %r9, %r9, 43, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 22, 42
	and %r9, %r9, %r10
	rldicl %r9, %r9, 42, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 14, 50
	and %r9, %r9, %r10
	rldicl %r9, %r9, 41, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 6, 58
	and %r9, %r9, %r10
	rldicl %r9, %r9, 40, 0
	xor %r8, %r8, %r9
	or %r9, %r7, %r7
	and %r9, %r9, %r10
	rldicl %r9, %r9, 39, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 56, 8
	and %r9, %r9, %r10
	rldicl %r9, %r9, 38, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 48, 16
	and %r9, %r9, %r10
	rldicl %r9, %r9, 37, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 40, 24
	and %r9, %r9, %r10
	rldicl %r9, %r9, 36, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 32, 32
	and %r9, %r9, %r10
	rldicl %r9, %r9, 35, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 24, 40
	and %r9, %r9, %r10
	rldicl %r9, %r9, 34, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 16, 48
	and %r9, %r9, %r10
	rldicl %r9, %r9, 33, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 8, 56
	and %r9, %r9, %r10
	rldicl %r9, %r9, 32, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 57, 7
	and %r9, %r9, %r10
	rldicl %r9, %r9, 31, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 49, 15
	and %r9, %r9, %r10
	rldicl %r9, %r9, 30, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 41, 23
	and %r9, %r9, %r10
	rldicl %r9, %r9, 29, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 33, 31
	and %r9, %r9, %r10
	rldicl %r9, %r9, 28, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 25, 39
	and %r9, %r9, %r10
	rldicl %r9, %r9, 27, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 17, 47
	and %r9, %r9, %r10
	rldicl %r9, %r9, 26, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 9, 55
	and %r9, %r9, %r10
	rldicl %r9, %r9, 25, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 1, 63
	and %r9, %r9, %r10
	rldicl %r9, %r9, 24, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 59, 5
	and %r9, %r9, %r10
	rldicl %r9, %r9, 23, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 51, 13
	and %r9, %r9, %r10
	rldicl %r9, %r9, 22, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 43, 21
	and %r9, %r9, %r10
	rldicl %r9, %r9, 21, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 35, 29
	and %r9, %r9, %r10
	rldicl %r9, %r9, 20, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 27, 37
	and %r9, %r9, %r10
	rldicl %r9, %r9, 19, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 19, 45
	and %r9, %r9, %r10
	rldicl %r9, %r9, 18, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 11, 53
	and %r9, %r9, %r10
	rldicl %r9, %r9, 17, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 3, 61
	and %r9, %r9, %r10
	rldicl %r9, %r9, 16, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 61, 3
	and %r9, %r9, %r10
	rldicl %r9, %r9, 15, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 53, 11
	and %r9, %r9, %r10
	rldicl %r9, %r9, 14, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 45, 19
	and %r9, %r9, %r10
	rldicl %r9, %r9, 13, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 37, 27
	and %r9, %r9, %r10
	rldicl %r9, %r9, 12, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 29, 35
	and %r9, %r9, %r10
	rldicl %r9, %r9, 11, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 21, 43
	and %r9, %r9, %r10
	rldicl %r9, %r9, 10, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 13, 51
	and %r9, %r9, %r10
	rldicl %r9, %r9, 9, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 5, 59
	and %r9, %r9, %r10
	rldicl %r9, %r9, 8, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 63, 1
	and %r9, %r9, %r10
	rldicl %r9, %r9, 7, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 55, 9
	and %r9, %r9, %r10
	rldicl %r9, %r9, 6, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 47, 17
	and %r9, %r9, %r10
	rldicl %r9, %r9, 5, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 39, 25
	and %r9, %r9, %r10
	rldicl %r9, %r9, 4, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 31, 33
	and %r9, %r9, %r10
	rldicl %r9, %r9, 3, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 23, 41
	and %r9, %r9, %r10
	rldicl %r9, %r9, 2, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 15, 49
	and %r9, %r9, %r10
	rldicl %r9, %r9, 1, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 7, 57
	and %r9, %r9, %r10
	xor %r8, %r8, %r9
	rldicl %r14, %r8, 32, 32
	rlwinm %r15, %r8, 0, 0, 31
	li %r19, 3
20:
	addi %r20, %r19, -3
	cmpldi %cr0, %r20, 0
	beq %cr0, 21f
	addi %r20, %r19, -2
	cmpldi %cr0, %r20, 0
	beq %cr0, 23f
	addi %r17, %r3, 256
	li %r16, 16
	li %r18, 0
	addi %r18, %r18, 8
	b 24f
23:
	addi %r17, %r3, 248
	li %r16, 16
	li %r18, 0
	addi %r18, %r18, -8
24:
	b 22f
21:
	addi %r17, %r3, 0
	li %r16, 16
	li %r18, 0
	addi %r18, %r18, 8
22:
25:
	ld %r20, 0(%r17)
	li %r22, 1
	rldicl %r6, %r15, 37, 27
	rldicl %r21, %r20, 22, 42
	xor %r6, %r6, %r21
	and %r6, %r6, %r22
	rldicl %r7, %r15, 36, 28
	rldicl %r21, %r20, 21, 43
	xor %r7, %r7, %r21
	and %r7, %r7, %r22
	rldicl %r8, %r15, 35, 29
	rldicl %r21, %r20, 20, 44
	xor %r8, %r8, %r21
	and %r8, %r8, %r22
	rldicl %r9, %r15, 34, 30
	rldicl %r21, %r20, 19, 45
	xor %r9, %r9, %r21
	and %r9, %r9, %r22
	rldicl %r10, %r15, 33, 31
	rldicl %r21, %r20, 18, 46
	xor %r10, %r10, %r21
	and %r10, %r10, %r22
	or %r11, %r15, %r15
	rldicl %r21, %r20, 17, 47
	xor %r11, %r11, %r21
	and %r11, %r11, %r22
	li %r12, 0
	addi %r12, %r12, -1
	xor %r20, %r6, %r6
	xor %r21, %r6, %r20
	xor %r21, %r21, %r12
	and %r22, %r10, %r21
	xor %r23, %r6, %r10
	and %r24, %r7, %r23
	xor %r24, %r22, %r24
	xor %r25, %r21, %r22
	and %r26, %r7, %r25
	xor %r26, %r6, %r26
	and %r26, %r11, %r26
	xor %r24, %r24, %r26
	and %r26, %r10, %r6
	xor %r27, %r26, %r20
	xor %r27, %r27, %r12
	and %r28, %r7, %r27
	xor %r0, %r26, %r28
	std %r23, 120(%r5)
	xor %r23, %r10, %r20
	xor %r23, %r23, %r12
	std %r6, 128(%r5)
	xor %r6, %r23, %r28
	std %r28, 136(%r5)
	and %r28, %r11, %r6
	xor %r0, %r0, %r28
	and %r0, %r9, %r0
	xor %r24, %r24, %r0
	and %r10, %r7, %r10
	xor %r0, %r27, %r10
	and %r28, %r7, %r23
	std %r10, 144(%r5)
	xor %r10, %r21, %r28
	and %r10, %r11, %r10
	xor %r0, %r0, %r10
	and %r10, %r7, %r21
	std %r23, 152(%r5)
	xor %r23, %r25, %r10
	and %r23, %r11, %r23
	and %r23, %r9, %r23
	xor %r0, %r0, %r23
	and %r0, %r8, %r0
	xor %r24, %r24, %r0
	xor %r21, %r21, %r26
	xor %r26, %r21, %r28
	xor %r0, %r22, %r20
	xor %r0, %r0, %r12
	and %r21, %r7, %r21
	xor %r21, %r0, %r21
	and %r23, %r11, %r21
	xor %r26, %r26, %r23
	xor %r23, %r25, %r20
	xor %r23, %r23, %r12
	xor %r28, %r23, %r28
	std %r24, 160(%r5)
	and %r24, %r7, %r22
	xor %r22, %r22, %r24
	and %r22, %r11, %r22
	xor %r24, %r28, %r22
	and %r24, %r9, %r24
	xor %r26, %r26, %r24
	xor %r21, %r21, %r22
	ld %r22, 128(%r5)
	and %r24, %r7, %r22
	std %r6, 168(%r5)
	xor %r6, %r0, %r24
	and %r6, %r11, %r6
	std %r12, 176(%r5)
	xor %r12, %r25, %r6
	and %r12, %r9, %r12
	xor %r21, %r21, %r12
	and %r21, %r8, %r21
	xor %r26, %r26, %r21
	xor %r21, %r25, %r24
	and %r12, %r11, %r28
	xor %r21, %r21, %r12
	xor %r27, %r27, %r10
	and %r23, %r7, %r23
	xor %r0, %r0, %r23
	and %r0, %r11, %r0
	xor %r27, %r27, %r0
	and %r27, %r9, %r27
	xor %r21, %r21, %r27
	ld %r27, 136(%r5)
	and %r0, %r11, %r27
	xor %r28, %r28, %r0
	xor %r22, %r22, %r24
	xor %r22, %r22, %r6
	and %r22, %r9, %r22
	xor %r28, %r28, %r22
	and %r28, %r8, %r28
	xor %r21, %r21, %r28
	ld %r28, 120(%r5)
	xor %r28, %r28, %r20
	ld %r22, 176(%r5)
	xor %r28, %r28, %r22
	xor %r28, %r28, %r7
	xor %r27, %r27, %r20
	xor %r27, %r27, %r22
	and %r27, %r11, %r27
	xor %r27, %r28, %r27
	ld %r6, 168(%r5)
	xor %r6, %r6, %r20
	xor %r6, %r6, %r22
	and %r6, %r11, %r6
	ld %r22, 152(%r5)
	xor %r22, %r22, %r6
	and %r22, %r9, %r22
	xor %r27, %r27, %r22
	ld %r22, 144(%r5)
	xor %r22, %r25, %r22
	and %r22, %r11, %r22
	xor %r24, %r24, %r22
	xor %r25, %r25, %r7
	and %r11, %r11, %r25
	xor %r28, %r28, %r11
	and %r9, %r9, %r28
	xor %r24, %r24, %r9
	and %r8, %r8, %r24
	xor %r9, %r27, %r8
	ld %r6, 160(%r5)
	or %r7, %r26, %r26
	or %r8, %r21, %r21
	li %r20, 1
	and %r6, %r6, %r20
	rldicl %r6, %r6, 1, 0
	xor %r14, %r14, %r6
	and %r7, %r7, %r20
	rldicl %r7, %r7, 9, 0
	xor %r14, %r14, %r7
	and %r8, %r8, %r20
	rldicl %r8, %r8, 15, 0
	xor %r14, %r14, %r8
	and %r9, %r9, %r20
	rldicl %r9, %r9, 23, 0
	xor %r14, %r14, %r9
	ld %r20, 0(%r17)
	li %r22, 1
	rldicl %r6, %r15, 41, 23
	rldicl %r21, %r20, 28, 36
	xor %r6, %r6, %r21
	and %r6, %r6, %r22
	rldicl %r7, %r15, 40, 24
	rldicl %r21, %r20, 27, 37
	xor %r7, %r7, %r21
	and %r7, %r7, %r22
	rldicl %r8, %r15, 39, 25
	rldicl %r21, %r20, 26, 38
	xor %r8, %r8, %r21
	and %r8, %r8, %r22
	rldicl %r9, %r15, 38, 26
	rldicl %r21, %r20, 25, 39
	xor %r9, %r9, %r21
	and %r9, %r9, %r22
	rldicl %r10, %r15, 37, 27
	rldicl %r21, %r20, 24, 40
	xor %r10, %r10, %r21
	and %r10, %r10, %r22
	rldicl %r11, %r15, 36, 28
	rldicl %r21, %r20, 23, 41
	xor %r11, %r11, %r21
	and %r11, %r11, %r22
	li %r12, 0
	addi %r12, %r12, -1
	xor %r20, %r6, %r6
	xor %r21, %r6, %r6
	xor %r21, %r21, %r12
	xor %r22, %r11, %r20
	xor %r22, %r22, %r12
	and %r23, %r7, %r11
	xor %r24, %r11, %r23
	and %r25, %r6, %r24
	xor %r25, %r22, %r25
	xor %r26, %r23, %r20
	xor %r26, %r26, %r12
	and %r27, %r6, %r26
	xor %r28, %r24, %r27
	and %r28, %r10, %r28
	xor %r25, %r25, %r28
	and %r0, %r7, %r22
	std %r27, 120(%r5)
	xor %r27, %r22, %r0
	xor %r24, %r24, %r20
	xor %r24, %r24, %r12
	std %r22, 128(%r5)
	and %r22, %r6, %r24
	std %r26, 136(%r5)
	xor %r26, %r27, %r22
	std %r22, 144(%r5)
	xor %r22, %r27, %r20
	xor %r22, %r22, %r12
	std %r27, 152(%r5)
	and %r27, %r6, %r22
	xor %r27, %r7, %r27
	and %r27, %r10, %r27
	xor %r26, %r26, %r27
	and %r26, %r9, %r26
	xor %r25, %r25, %r26
	and %r26, %r6, %r0
	xor %r26, %r21, %r26
	xor %r27, %r11, %r7
	std %r0, 160(%r5)
	and %r0, %r6, %r27
	std %r21, 168(%r5)
	xor %r21, %r7, %r0
	and %r21, %r10, %r21
	xor %r26, %r26, %r21
	and %r26, %r8, %r26
	xor %r25, %r25, %r26
	xor %r27, %r27, %r20
	xor %r27, %r27, %r12
	and %r23, %r6, %r23
	xor %r26, %r27, %r23
	xor %r24, %r24, %r0
	and %r24, %r10, %r24
	xor %r26, %r26, %r24
	xor %r22, %r22, %r28
	and %r22, %r9, %r22
	xor %r26, %r26, %r22
	ld %r22, 152(%r5)
	and %r28, %r6, %r22
	xor %r28, %r11, %r28
	and %r28, %r10, %r28
	ld %r24, 136(%r5)
	xor %r28, %r24, %r28
	ld %r0, 128(%r5)
	and %r21, %r6, %r0
	xor %r22, %r22, %r21
	and %r11, %r10, %r11
	xor %r22, %r22, %r11
	and %r22, %r9, %r22
	xor %r28, %r28, %r22
	and %r28, %r8, %r28
	xor %r26, %r26, %r28
	xor %r28, %r27, %r6
	xor %r28, %r28, %r10
	xor %r22, %r24, %r23
	and %r22, %r10, %r22
	xor %r22, %r6, %r22
	and %r22, %r9, %r22
	xor %r28, %r28, %r22
	and %r6, %r6, %r7
	ld %r7, 168(%r5)
	xor %r7, %r7, %r6
	ld %r22, 120(%r5)
	xor %r24, %r24, %r22
	and %r24, %r10, %r24
	xor %r7, %r7, %r24
	and %r6, %r9, %r6
	xor %r7, %r7, %r6
	and %r7, %r8, %r7
	xor %r28, %r28, %r7
	xor %r27, %r27, %r22
	ld %r22, 144(%r5)
	and %r22, %r10, %r22
	xor %r27, %r27, %r22
	xor %r22, %r23, %r20
	xor %r22, %r22, %r12
	xor %r0, %r0, %r21
	and %r0, %r10, %r0
	xor %r22, %r22, %r0
	and %r9, %r9, %r22
	xor %r27, %r27, %r9
	ld %r9, 160(%r5)
	xor %r9, %r9, %r23
	xor %r20, %r9, %r20
	xor %r20, %r20, %r12
	and %r10, %r10, %r20
	xor %r9, %r9, %r10
	and %r8, %r8, %r9
	xor %r9, %r27, %r8
	or %r6, %r25, %r25
	or %r7, %r26, %r26
	or %r8, %r28, %r28
	li %r20, 1
	and %r6, %r6, %r20
	rldicl %r6, %r6, 14, 0
	xor %r14, %r14, %r6
	and %r7, %r7, %r20
	rldicl %r7, %r7, 30, 0
	xor %r14, %r14, %r7
	and %r8, %r8, %r20
	rldicl %r8, %r8, 4, 0
	xor %r14, %r14, %r8
	and %r9, %r9, %r20
	rldicl %r9, %r9, 19, 0
	xor %r14, %r14, %r9
	ld %r20, 0(%r17)
	li %r22, 1
	rldicl %r6, %r15, 45, 19
	rldicl %r21, %r20, 34, 30
	xor %r6, %r6, %r21
	and %r6, %r6, %r22
	rldicl %r7, %r15, 44, 20
	rldicl %r21, %r20, 33, 31
	xor %r7, %r7, %r21
	and %r7, %r7, %r22
	rldicl %r8, %r15, 43, 21
	rldicl %r21, %r20, 32, 32
	xor %r8, %r8, %r21
	and %r8, %r8, %r22
	rldicl %r9, %r15, 42, 22
	rldicl %r21, %r20, 31, 33
	xor %r9, %r9, %r21
	and %r9, %r9, %r22
	rldicl %r10, %r15, 41, 23
	rldicl %r21, %r20, 30, 34
	xor %r10, %r10, %r21
	and %r10, %r10, %r22
	rldicl %r11, %r15, 40, 24
	rldicl %r21, %r20, 29, 35
	xor %r11, %r11, %r21
	and %r11, %r11, %r22
	li %r12, 0
	addi %r12, %r12, -1
	xor %r20, %r6, %r6
	xor %r21, %r6, %r6
	xor %r21, %r21, %r12
	xor %r22, %r11, %r20
	xor %r22, %r22, %r12
	and %r23, %r10, %r22
	xor %r24, %r11, %r23
	and %r25, %r10, %r11
	xor %r26, %r22, %r25
	and %r27, %r6, %r26
	xor %r28, %r24, %r27
	xor %r0, %r26, %r20
	xor %r0, %r0, %r12
	and %r25, %r6, %r25
	std %r24, 120(%r5)
	xor %r24, %r0, %r25
	std %r0, 128(%r5)
	and %r0, %r7, %r24
	xor %r0, %r28, %r0
	std %r28, 136(%r5)
	and %r28, %r7, %r26
	xor %r24, %r24, %r28
	and %r24, %r9, %r24
	xor %r0, %r0, %r24
	and %r11, %r6, %r11
	xor %r21, %r21, %r11
	and %r24, %r7, %r22
	xor %r21, %r21, %r24
	and %r25, %r9, %r25
	xor %r21, %r21, %r25
	and %r21, %r8, %r21
	xor %r0, %r0, %r21
	xor %r21, %r22, %r10
	xor %r27, %r21, %r27
	xor %r25, %r23, %r20
	xor %r25, %r25, %r12
	and %r24, %r6, %r23
	xor %r24, %r25, %r24
	and %r28, %r7, %r24
	std %r0, 144(%r5)
	xor %r0, %r27, %r28
	std %r26, 152(%r5)
	xor %r26, %r10, %r20
	xor %r26, %r26, %r12
	std %r21, 160(%r5)
	and %r21, %r6, %r26
	xor %r10, %r10, %r21
	std %r26, 168(%r5)
	and %r26, %r6, %r22
	xor %r22, %r22, %r26
	and %r22, %r7, %r22
	xor %r10, %r10, %r22
	and %r10, %r9, %r10
	xor %r0, %r0, %r10
	ld %r10, 136(%r5)
	xor %r10, %r10, %r20
	xor %r10, %r10, %r12
	xor %r27, %r27, %r20
	xor %r27, %r27, %r12
	and %r27, %r7, %r27
	xor %r10, %r10, %r27
	ld %r27, 120(%r5)
	xor %r22, %r27, %r20
	xor %r22, %r22, %r12
	and %r27, %r6, %r22
	std %r22, 136(%r5)
	xor %r22, %r25, %r27
	std %r27, 176(%r5)
	xor %r27, %r26, %r20
	xor %r27, %r27, %r12
	and %r27, %r7, %r27
	xor %r22, %r22, %r27
	and %r22, %r9, %r22
	xor %r10, %r10, %r22
	and %r10, %r8, %r10
	xor %r0, %r0, %r10
	and %r10, %r6, %r25
	ld %r22, 128(%r5)
	xor %r22, %r22, %r10
	xor %r10, %r24, %r20
	xor %r10, %r10, %r12
	and %r10, %r7, %r10
	xor %r22, %r22, %r10
	xor %r24, %r24, %r28
	and %r24, %r9, %r24
	xor %r22, %r22, %r24
	xor %r21, %r23, %r21
	xor %r21, %r21, %r27
	and %r27, %r7, %r11
	xor %r23, %r23, %r27
	and %r23, %r9, %r23
	xor %r21, %r21, %r23
	and %r21, %r8, %r21
	xor %r22, %r22, %r21
	xor %r25, %r25, %r11
	xor %r25, %r25, %r7
	ld %r11, 160(%r5)
	xor %r11, %r11, %r20
	xor %r11, %r11, %r12
	and %r6, %r6, %r11
	ld %r11, 168(%r5)
	xor %r11, %r11, %r6
	and %r11, %r7, %r11
	ld %r6, 152(%r5)
	xor %r6, %r6, %r11
	and %r6, %r9, %r6
	xor %r25, %r25, %r6
	ld %r6, 120(%r5)
	xor %r6, %r6, %r26
	ld %r11, 136(%r5)
	ld %r12, 176(%r5)
	xor %r12, %r11, %r12
	and %r12, %r7, %r12
	xor %r6, %r6, %r12
	and %r7, %r7, %r26
	xor %r11, %r11, %r7
	and %r9, %r9, %r11
	xor %r6, %r6, %r9
	and %r8, %r8, %r6
	xor %r9, %r25, %r8
	ld %r6, 144(%r5)
	or %r7, %r0, %r0
	or %r8, %r22, %r22
	li %r20, 1
	and %r6, %r6, %r20
	rldicl %r6, %r6, 26, 0
	xor %r14, %r14, %r6
	and %r7, %r7, %r20
	rldicl %r7, %r7, 2, 0
	xor %r14, %r14, %r7
	and %r8, %r8, %r20
	rldicl %r8, %r8, 16, 0
	xor %r14, %r14, %r8
	and %r9, %r9, %r20
	rldicl %r9, %r9, 8, 0
	xor %r14, %r14, %r9
	ld %r20, 0(%r17)
	li %r22, 1
	rldicl %r6, %r15, 49, 15
	rldicl %r21, %r20, 40, 24
	xor %r6, %r6, %r21
	and %r6, %r6, %r22
	rldicl %r7, %r15, 48, 16
	rldicl %r21, %r20, 39, 25
	xor %r7, %r7, %r21
	and %r7, %r7, %r22
	rldicl %r8, %r15, 47, 17
	rldicl %r21, %r20, 38, 26
	xor %r8, %r8, %r21
	and %r8, %r8, %r22
	rldicl %r9, %r15, 46, 18
	rldicl %r21, %r20, 37, 27
	xor %r9, %r9, %r21
	and %r9, %r9, %r22
	rldicl %r10, %r15, 45, 19
	rldicl %r21, %r20, 36, 28
	xor %r10, %r10, %r21
	and %r10, %r10, %r22
	rldicl %r11, %r15, 44, 20
	rldicl %r21, %r20, 35, 29
	xor %r11, %r11, %r21
	and %r11, %r11, %r22
	li %r12, 0
	addi %r12, %r12, -1
	xor %r20, %r6, %r6
	xor %r21, %r6, %r6
	xor %r21, %r21, %r12
	xor %r22, %r9, %r20
	xor %r22, %r22, %r12
	and %r23, %r7, %r9
	xor %r24, %r22, %r23
	and %r25, %r11, %r24
	xor %r26, %r22, %r25
	xor %r27, %r9, %r7
	xor %r28, %r27, %r20
	xor %r28, %r28, %r12
	and %r0, %r11, %r28
	std %r25, 120(%r5)
	xor %r25, %r27, %r0
	and %r25, %r10, %r25
	xor %r26, %r26, %r25
	xor %r25, %r7, %r20
	xor %r25, %r25, %r12
	std %r9, 128(%r5)
	xor %r9, %r7, %r0
	std %r0, 136(%r5)
	and %r0, %r10, %r9
	std %r6, 144(%r5)
	xor %r6, %r25, %r0
	and %r6, %r8, %r6
	xor %r26, %r26, %r6
	xor %r6, %r24, %r20
	xor %r6, %r6, %r12
	and %r6, %r11, %r6
	xor %r6, %r28, %r6
	and %r6, %r10, %r6
	xor %r9, %r9, %r6
	xor %r23, %r23, %r20
	xor %r23, %r23, %r12
	and %r6, %r7, %r22
	xor %r21, %r21, %r6
	std %r0, 152(%r5)
	and %r0, %r11, %r21
	xor %r23, %r23, %r0
	and %r27, %r10, %r27
	xor %r23, %r23, %r27
	and %r23, %r8, %r23
	xor %r9, %r9, %r23
	ld %r23, 144(%r5)
	std %r27, 160(%r5)
	and %r27, %r23, %r9
	xor %r26, %r26, %r27
	and %r27, %r11, %r6
	xor %r28, %r28, %r27
	std %r26, 168(%r5)
	xor %r26, %r0, %r20
	xor %r26, %r26, %r12
	and %r26, %r10, %r26
	xor %r26, %r28, %r26
	std %r11, 176(%r5)
	xor %r11, %r6, %r0
	std %r6, 184(%r5)
	ld %r6, 128(%r5)
	std %r25, 192(%r5)
	ld %r25, 136(%r5)
	xor %r25, %r6, %r25
	and %r25, %r10, %r25
	xor %r11, %r11, %r25
	and %r11, %r8, %r11
	xor %r26, %r26, %r11
	xor %r9, %r9, %r20
	xor %r9, %r9, %r12
	and %r9, %r23, %r9
	xor %r26, %r26, %r9
	xor %r24, %r24, %r0
	and %r22, %r10, %r22
	xor %r24, %r24, %r22
	xor %r7, %r7, %r25
	and %r7, %r8, %r7
	xor %r24, %r24, %r7
	xor %r28, %r28, %r20
	xor %r28, %r28, %r12
	xor %r21, %r21, %r27
	and %r21, %r10, %r21
	xor %r28, %r28, %r21
	ld %r21, 192(%r5)
	ld %r7, 120(%r5)
	xor %r21, %r21, %r7
	ld %r25, 160(%r5)
	xor %r21, %r21, %r25
	and %r21, %r8, %r21
	xor %r28, %r28, %r21
	and %r21, %r23, %r28
	xor %r24, %r24, %r21
	ld %r21, 184(%r5)
	ld %r25, 176(%r5)
	xor %r25, %r21, %r25
	xor %r6, %r6, %r21
	xor %r6, %r6, %r27
	and %r10, %r10, %r6
	xor %r25, %r25, %r10
	xor %r7, %r7, %r20
	xor %r7, %r7, %r12
	ld %r10, 152(%r5)
	xor %r7, %r7, %r10
	and %r8, %r8, %r7
	xor %r25, %r25, %r8
	xor %r28, %r28, %r20
	xor %r28, %r28, %r12
	and %r23, %r23, %r28
	xor %r9, %r25, %r23
	ld %r6, 168(%r5)
	or %r7, %r26, %r26
	or %r8, %r24, %r24
	li %r20, 1
	and %r6, %r6, %r20
	rldicl %r6, %r6, 31, 0
	xor %r14, %r14, %r6
	and %r7, %r7, %r20
	rldicl %r7, %r7, 22, 0
	xor %r14, %r14, %r7
	and %r8, %r8, %r20
	rldicl %r8, %r8, 12, 0
	xor %r14, %r14, %r8
	and %r9, %r9, %r20
	rldicl %r9, %r9, 6, 0
	xor %r14, %r14, %r9
	ld %r20, 0(%r17)
	li %r22, 1
	rldicl %r6, %r15, 53, 11
	rldicl %r21, %r20, 46, 18
	xor %r6, %r6, %r21
	and %r6, %r6, %r22
	rldicl %r7, %r15, 52, 12
	rldicl %r21, %r20, 45, 19
	xor %r7, %r7, %r21
	and %r7, %r7, %r22
	rldicl %r8, %r15, 51, 13
	rldicl %r21, %r20, 44, 20
	xor %r8, %r8, %r21
	and %r8, %r8, %r22
	rldicl %r9, %r15, 50, 14
	rldicl %r21, %r20, 43, 21
	xor %r9, %r9, %r21
	and %r9, %r9, %r22
	rldicl %r10, %r15, 49, 15
	rldicl %r21, %r20, 42, 22
	xor %r10, %r10, %r21
	and %r10, %r10, %r22
	rldicl %r11, %r15, 48, 16
	rldicl %r21, %r20, 41, 23
	xor %r11, %r11, %r21
	and %r11, %r11, %r22
	li %r12, 0
	addi %r12, %r12, -1
	xor %r20, %r6, %r6
	xor %r21, %r6, %r6
	xor %r21, %r21, %r12
	xor %r22, %r9, %r20
	xor %r22, %r22, %r12
	and %r23, %r22, %r11
	xor %r24, %r21, %r23
	xor %r6, %r6, %r20
	xor %r6, %r6, %r12
	and %r25, %r6, %r24
	xor %r26, %r11, %r25
	xor %r27, %r11, %r20
	xor %r27, %r27, %r12
	and %r28, %r22, %r27
	xor %r0, %r27, %r28
	xor %r10, %r10, %r20
	xor %r10, %r10, %r12
	std %r25, 120(%r5)
	and %r25, %r10, %r0
	xor %r25, %r26, %r25
	std %r26, 128(%r5)
	xor %r26, %r27, %r23
	std %r21, 136(%r5)
	and %r21, %r10, %r26
	xor %r21, %r9, %r21
	xor %r8, %r8, %r20
	xor %r8, %r8, %r12
	and %r21, %r8, %r21
	xor %r25, %r25, %r21
	and %r21, %r6, %r27
	xor %r21, %r22, %r21
	std %r9, 144(%r5)
	xor %r9, %r11, %r22
	and %r23, %r6, %r23
	xor %r23, %r9, %r23
	and %r23, %r10, %r23
	xor %r21, %r21, %r23
	xor %r23, %r0, %r20
	xor %r23, %r23, %r12
	and %r23, %r6, %r23
	std %r22, 152(%r5)
	xor %r22, %r27, %r6
	and %r22, %r10, %r22
	xor %r23, %r23, %r22
	and %r23, %r8, %r23
	xor %r21, %r21, %r23
	xor %r7, %r7, %r20
	xor %r7, %r7, %r12
	and %r21, %r7, %r21
	xor %r25, %r25, %r21
	and %r21, %r6, %r0
	xor %r23, %r24, %r21
	xor %r23, %r23, %r10
	xor %r22, %r28, %r20
	xor %r22, %r22, %r12
	std %r25, 160(%r5)
	and %r25, %r6, %r22
	std %r24, 168(%r5)
	ld %r24, 136(%r5)
	xor %r24, %r24, %r25
	and %r28, %r6, %r28
	std %r12, 136(%r5)
	and %r12, %r10, %r28
	xor %r24, %r24, %r12
	and %r24, %r8, %r24
	xor %r23, %r23, %r24
	xor %r28, %r26, %r28
	and %r28, %r10, %r28
	ld %r24, 144(%r5)
	xor %r28, %r24, %r28
	and %r11, %r6, %r11
	xor %r27, %r27, %r11
	and %r12, %r10, %r27
	xor %r12, %r25, %r12
	and %r12, %r8, %r12
	xor %r28, %r28, %r12
	and %r28, %r7, %r28
	xor %r23, %r23, %r28
	xor %r28, %r0, %r6
	xor %r28, %r28, %r10
	xor %r22, %r22, %r21
	xor %r21, %r9, %r25
	and %r21, %r10, %r21
	xor %r22, %r22, %r21
	and %r22, %r8, %r22
	xor %r28, %r28, %r22
	xor %r22, %r9, %r20
	ld %r21, 136(%r5)
	xor %r22, %r22, %r21
	and %r12, %r6, %r22
	xor %r0, %r0, %r12
	and %r0, %r8, %r0
	std %r23, 176(%r5)
	ld %r23, 168(%r5)
	xor %r23, %r23, %r0
	and %r23, %r7, %r23
	xor %r28, %r28, %r23
	ld %r23, 152(%r5)
	xor %r23, %r23, %r25
	ld %r25, 128(%r5)
	and %r25, %r10, %r25
	xor %r23, %r23, %r25
	xor %r25, %r26, %r6
	and %r25, %r10, %r25
	xor %r27, %r27, %r25
	and %r27, %r8, %r27
	xor %r23, %r23, %r27
	ld %r27, 120(%r5)
	xor %r22, %r22, %r27
	and %r6, %r6, %r24
	xor %r9, %r9, %r6
	and %r9, %r10, %r9
	xor %r22, %r22, %r9
	xor %r26, %r26, %r20
	xor %r26, %r26, %r21
	xor %r26, %r26, %r12
	xor %r11, %r11, %r20
	xor %r11, %r11, %r21
	and %r10, %r10, %r11
	xor %r26, %r26, %r10
	and %r8, %r8, %r26
	xor %r22, %r22, %r8
	and %r7, %r7, %r22
	xor %r9, %r23, %r7
	ld %r6, 160(%r5)
	ld %r7, 176(%r5)
	or %r8, %r28, %r28
	li %r20, 1
	and %r6, %r6, %r20
	rldicl %r6, %r6, 29, 0
	xor %r14, %r14, %r6
	and %r7, %r7, %r20
	rldicl %r7, %r7, 7, 0
	xor %r14, %r14, %r7
	and %r8, %r8, %r20
	rldicl %r8, %r8, 18, 0
	xor %r14, %r14, %r8
	and %r9, %r9, %r20
	rldicl %r9, %r9, 24, 0
	xor %r14, %r14, %r9
	ld %r20, 0(%r17)
	li %r22, 1
	rldicl %r6, %r15, 57, 7
	rldicl %r21, %r20, 52, 12
	xor %r6, %r6, %r21
	and %r6, %r6, %r22
	rldicl %r7, %r15, 56, 8
	rldicl %r21, %r20, 51, 13
	xor %r7, %r7, %r21
	and %r7, %r7, %r22
	rldicl %r8, %r15, 55, 9
	rldicl %r21, %r20, 50, 14
	xor %r8, %r8, %r21
	and %r8, %r8, %r22
	rldicl %r9, %r15, 54, 10
	rldicl %r21, %r20, 49, 15
	xor %r9, %r9, %r21
	and %r9, %r9, %r22
	rldicl %r10, %r15, 53, 11
	rldicl %r21, %r20, 48, 16
	xor %r10, %r10, %r21
	and %r10, %r10, %r22
	rldicl %r11, %r15, 52, 12
	rldicl %r21, %r20, 47, 17
	xor %r11, %r11, %r21
	and %r11, %r11, %r22
	li %r12, 0
	addi %r12, %r12, -1
	xor %r20, %r6, %r6
	xor %r21, %r6, %r6
	xor %r21, %r21, %r12
	xor %r22, %r10, %r20
	xor %r22, %r22, %r12
	and %r23, %r9, %r22
	xor %r24, %r23, %r7
	xor %r25, %r10, %r23
	and %r26, %r7, %r9
	xor %r27, %r25, %r26
	and %r27, %r8, %r27
	xor %r24, %r24, %r27
	xor %r27, %r26, %r20
	xor %r27, %r27, %r12
	xor %r28, %r9, %r20
	xor %r28, %r28, %r12
	and %r0, %r7, %r28
	std %r26, 120(%r5)
	xor %r26, %r9, %r0
	std %r28, 128(%r5)
	and %r28, %r8, %r26
	xor %r27, %r27, %r28
	and %r27, %r11, %r27
	xor %r24, %r24, %r27
	xor %r27, %r22, %r9
	std %r26, 136(%r5)
	and %r26, %r7, %r27
	std %r28, 144(%r5)
	xor %r28, %r23, %r26
	and %r28, %r8, %r28
	and %r9, %r9, %r10
	std %r0, 152(%r5)
	xor %r0, %r22, %r9
	std %r22, 160(%r5)
	xor %r22, %r27, %r20
	xor %r22, %r22, %r12
	xor %r22, %r22, %r26
	and %r22, %r8, %r22
	xor %r22, %r0, %r22
	and %r22, %r11, %r22
	xor %r28, %r28, %r22
	and %r28, %r6, %r28
	xor %r24, %r24, %r28
	and %r28, %r7, %r23
	xor %r22, %r9, %r28
	and %r10, %r7, %r10
	xor %r21, %r21, %r10
	std %r24, 168(%r5)
	and %r24, %r8, %r21
	xor %r22, %r22, %r24
	ld %r24, 152(%r5)
	xor %r25, %r25, %r24
	and %r10, %r8, %r10
	xor %r25, %r25, %r10
	and %r25, %r11, %r25
	xor %r22, %r22, %r25
	and %r25, %r8, %r7
	xor %r21, %r21, %r25
	ld %r25, 128(%r5)
	xor %r25, %r25, %r28
	std %r0, 128(%r5)
	ld %r0, 160(%r5)
	std %r28, 176(%r5)
	and %r28, %r7, %r0
	std %r10, 184(%r5)
	and %r10, %r8, %r28
	xor %r25, %r25, %r10
	and %r25, %r11, %r25
	xor %r21, %r21, %r25
	and %r21, %r6, %r21
	xor %r22, %r22, %r21
	xor %r27, %r27, %r24
	ld %r21, 120(%r5)
	xor %r0, %r0, %r21
	and %r0, %r8, %r0
	xor %r27, %r27, %r0
	xor %r0, %r23, %r20
	xor %r0, %r0, %r12
	and %r21, %r7, %r9
	xor %r21, %r0, %r21
	and %r26, %r8, %r26
	xor %r21, %r21, %r26
	and %r21, %r11, %r21
	xor %r27, %r27, %r21
	ld %r21, 184(%r5)
	xor %r21, %r21, %r20
	xor %r21, %r21, %r12
	ld %r12, 176(%r5)
	xor %r23, %r23, %r12
	xor %r9, %r9, %r7
	and %r9, %r8, %r9
	xor %r23, %r23, %r9
	and %r23, %r11, %r23
	xor %r21, %r21, %r23
	and %r21, %r6, %r21
	xor %r27, %r27, %r21
	ld %r21, 128(%r5)
	xor %r23, %r21, %r7
	ld %r9, 144(%r5)
	xor %r23, %r23, %r9
	ld %r9, 136(%r5)
	and %r12, %r11, %r9
	xor %r23, %r23, %r12
	xor %r24, %r0, %r24
	and %r24, %r8, %r24
	xor %r9, %r9, %r24
	and %r7, %r7, %r0
	xor %r0, %r0, %r7
	xor %r21, %r21, %r28
	and %r8, %r8, %r21
	xor %r0, %r0, %r8
	and %r11, %r11, %r0
	xor %r9, %r9, %r11
	and %r6, %r6, %r9
	xor %r9, %r23, %r6
	ld %r6, 168(%r5)
	or %r7, %r22, %r22
	or %r8, %r27, %r27
	li %r20, 1
	and %r6, %r6, %r20
	rldicl %r6, %r6, 13, 0
	xor %r14, %r14, %r6
	and %r7, %r7, %r20
	rldicl %r7, %r7, 21, 0
	xor %r14, %r14, %r7
	and %r8, %r8, %r20
	rldicl %r8, %r8, 3, 0
	xor %r14, %r14, %r8
	and %r9, %r9, %r20
	rldicl %r9, %r9, 28, 0
	xor %r14, %r14, %r9
	ld %r20, 0(%r17)
	li %r22, 1
	rldicl %r6, %r15, 61, 3
	rldicl %r21, %r20, 58, 6
	xor %r6, %r6, %r21
	and %r6, %r6, %r22
	rldicl %r7, %r15, 60, 4
	rldicl %r21, %r20, 57, 7
	xor %r7, %r7, %r21
	and %r7, %r7, %r22
	rldicl %r8, %r15, 59, 5
	rldicl %r21, %r20, 56, 8
	xor %r8, %r8, %r21
	and %r8, %r8, %r22
	rldicl %r9, %r15, 58, 6
	rldicl %r21, %r20, 55, 9
	xor %r9, %r9, %r21
	and %r9, %r9, %r22
	rldicl %r10, %r15, 57, 7
	rldicl %r21, %r20, 54, 10
	xor %r10, %r10, %r21
	and %r10, %r10, %r22
	rldicl %r11, %r15, 56, 8
	rldicl %r21, %r20, 53, 11
	xor %r11, %r11, %r21
	and %r11, %r11, %r22
	li %r12, 0
	addi %r12, %r12, -1
	xor %r20, %r6, %r6
	xor %r21, %r6, %r6
	xor %r21, %r21, %r12
	xor %r22, %r11, %r6
	and %r23, %r6, %r11
	and %r24, %r8, %r23
	xor %r25, %r22, %r24
	xor %r26, %r23, %r20
	xor %r26, %r26, %r12
	and %r27, %r8, %r26
	xor %r28, %r21, %r27
	and %r0, %r9, %r28
	xor %r25, %r25, %r0
	xor %r0, %r11, %r20
	xor %r0, %r0, %r12
	std %r24, 120(%r5)
	and %r24, %r6, %r0
	std %r0, 128(%r5)
	and %r0, %r8, %r24
	std %r24, 136(%r5)
	xor %r24, %r21, %r0
	std %r21, 144(%r5)
	and %r21, %r9, %r26
	xor %r24, %r24, %r21
	and %r24, %r10, %r24
	xor %r25, %r25, %r24
	and %r24, %r9, %r27
	xor %r28, %r28, %r24
	and %r24, %r8, %r6
	xor %r24, %r23, %r24
	and %r24, %r10, %r24
	xor %r28, %r28, %r24
	and %r28, %r7, %r28
	xor %r25, %r25, %r28
	xor %r28, %r23, %r8
	xor %r24, %r22, %r20
	xor %r24, %r24, %r12
	std %r25, 152(%r5)
	xor %r25, %r24, %r0
	and %r25, %r9, %r25
	xor %r28, %r28, %r25
	and %r25, %r8, %r11
	std %r21, 160(%r5)
	ld %r21, 144(%r5)
	std %r22, 168(%r5)
	xor %r22, %r21, %r25
	xor %r23, %r11, %r23
	xor %r21, %r23, %r0
	and %r21, %r9, %r21
	xor %r22, %r22, %r21
	and %r22, %r10, %r22
	xor %r28, %r28, %r22
	ld %r22, 128(%r5)
	std %r0, 176(%r5)
	ld %r0, 136(%r5)
	std %r25, 184(%r5)
	xor %r25, %r22, %r0
	xor %r6, %r6, %r20
	xor %r6, %r6, %r12
	and %r6, %r8, %r6
	xor %r6, %r25, %r6
	xor %r6, %r6, %r21
	and %r21, %r8, %r24
	std %r25, 192(%r5)
	and %r25, %r9, %r23
	xor %r21, %r21, %r25
	and %r21, %r10, %r21
	xor %r6, %r6, %r21
	and %r6, %r7, %r6
	xor %r28, %r28, %r6
	xor %r23, %r23, %r20
	xor %r23, %r23, %r12
	and %r22, %r8, %r22
	xor %r12, %r23, %r22
	and %r20, %r9, %r11
	xor %r12, %r12, %r20
	xor %r24, %r24, %r27
	ld %r27, 184(%r5)
	xor %r26, %r26, %r27
	and %r26, %r9, %r26
	xor %r24, %r24, %r26
	and %r24, %r10, %r24
	xor %r12, %r12, %r24
	ld %r24, 168(%r5)
	and %r24, %r8, %r24
	and %r24, %r9, %r24
	ld %r26, 144(%r5)
	xor %r26, %r26, %r24
	ld %r24, 176(%r5)
	and %r24, %r10, %r24
	xor %r26, %r26, %r24
	and %r26, %r7, %r26
	xor %r12, %r12, %r26
	xor %r0, %r0, %r27
	ld %r26, 160(%r5)
	xor %r0, %r0, %r26
	xor %r22, %r11, %r22
	ld %r26, 192(%r5)
	and %r8, %r8, %r26
	xor %r26, %r26, %r8
	and %r26, %r9, %r26
	xor %r22, %r22, %r26
	and %r22, %r10, %r22
	xor %r0, %r0, %r22
	ld %r22, 120(%r5)
	xor %r23, %r23, %r22
	xor %r11, %r11, %r8
	and %r9, %r9, %r11
	xor %r23, %r23, %r9
	xor %r27, %r27, %r20
	and %r10, %r10, %r27
	xor %r23, %r23, %r10
	and %r7, %r7, %r23
	xor %r9, %r0, %r7
	ld %r6, 152(%r5)
	or %r7, %r28, %r28
	or %r8, %r12, %r12
	li %r20, 1
	and %r6, %r6, %r20
	rldicl %r6, %r6, 25, 0
	xor %r14, %r14, %r6
	and %r7, %r7, %r20
	rldicl %r7, %r7, 10, 0
	xor %r14, %r14, %r7
	and %r8, %r8, %r20
	rldicl %r8, %r8, 20, 0
	xor %r14, %r14, %r8
	and %r9, %r9, %r20
	xor %r14, %r14, %r9
	ld %r20, 0(%r17)
	li %r22, 1
	rldicl %r6, %r15, 33, 31
	or %r21, %r20, %r20
	xor %r6, %r6, %r21
	and %r6, %r6, %r22
	or %r7, %r15, %r15
	rldicl %r21, %r20, 63, 1
	xor %r7, %r7, %r21
	and %r7, %r7, %r22
	rldicl %r8, %r15, 63, 1
	rldicl %r21, %r20, 62, 2
	xor %r8, %r8, %r21
	and %r8, %r8, %r22
	rldicl %r9, %r15, 62, 2
	rldicl %r21, %r20, 61, 3
	xor %r9, %r9, %r21
	and %r9, %r9, %r22
	rldicl %r10, %r15, 61, 3
	rldicl %r21, %r20, 60, 4
	xor %r10, %r10, %r21
	and %r10, %r10, %r22
	rldicl %r11, %r15, 60, 4
	rldicl %r21, %r20, 59, 5
	xor %r11, %r11, %r21
	and %r11, %r11, %r22
	li %r12, 0
	addi %r12, %r12, -1
	xor %r20, %r6, %r6
	xor %r21, %r6, %r6
	xor %r21, %r21, %r12
	xor %r22, %r6, %r20
	xor %r22, %r22, %r12
	xor %r23, %r11, %r22
	xor %r9, %r9, %r20
	xor %r9, %r9, %r12
	xor %r24, %r23, %r9
	xor %r7, %r7, %r20
	xor %r7, %r7, %r12
	xor %r24, %r24, %r7
	and %r25, %r9, %r6
	and %r26, %r22, %r11
	and %r27, %r9, %r26
	xor %r28, %r22, %r27
	and %r28, %r7, %r28
	xor %r28, %r25, %r28
	xor %r10, %r10, %r20
	xor %r10, %r10, %r12
	and %r28, %r10, %r28
	xor %r24, %r24, %r28
	xor %r28, %r11, %r20
	xor %r28, %r28, %r12
	and %r0, %r22, %r28
	std %r6, 120(%r5)
	xor %r6, %r21, %r0
	std %r23, 128(%r5)
	xor %r23, %r6, %r25
	and %r23, %r7, %r23
	xor %r22, %r22, %r23
	xor %r23, %r11, %r26
	std %r6, 136(%r5)
	and %r6, %r9, %r23
	xor %r21, %r21, %r6
	std %r25, 144(%r5)
	and %r25, %r7, %r28
	xor %r21, %r21, %r25
	and %r21, %r10, %r21
	xor %r22, %r22, %r21
	xor %r8, %r8, %r20
	xor %r8, %r8, %r12
	and %r22, %r8, %r22
	xor %r24, %r24, %r22
	xor %r22, %r26, %r20
	xor %r22, %r22, %r12
	xor %r21, %r22, %r6
	xor %r23, %r23, %r20
	xor %r23, %r23, %r12
	std %r24, 152(%r5)
	and %r24, %r9, %r23
	xor %r28, %r28, %r24
	and %r28, %r7, %r28
	xor %r21, %r21, %r28
	xor %r28, %r27, %r20
	xor %r28, %r28, %r12
	std %r23, 160(%r5)
	and %r23, %r7, %r27
	xor %r23, %r28, %r23
	and %r23, %r10, %r23
	xor %r21, %r21, %r23
	xor %r23, %r11, %r0
	std %r6, 168(%r5)
	ld %r6, 144(%r5)
	xor %r6, %r23, %r6
	std %r28, 144(%r5)
	ld %r28, 128(%r5)
	and %r28, %r7, %r28
	std %r26, 128(%r5)
	xor %r26, %r6, %r28
	xor %r6, %r6, %r20
	xor %r6, %r6, %r12
	xor %r23, %r23, %r20
	xor %r23, %r23, %r12
	and %r23, %r7, %r23
	xor %r6, %r6, %r23
	and %r6, %r10, %r6
	xor %r26, %r26, %r6
	and %r26, %r8, %r26
	xor %r21, %r21, %r26
	xor %r26, %r0, %r27
	and %r6, %r9, %r22
	xor %r11, %r11, %r6
	and %r6, %r7, %r11
	xor %r26, %r26, %r6
	xor %r24, %r22, %r24
	and %r24, %r10, %r24
	xor %r26, %r26, %r24
	xor %r22, %r22, %r25
	ld %r24, 128(%r5)
	xor %r27, %r24, %r27
	xor %r27, %r27, %r25
	and %r27, %r10, %r27
	xor %r22, %r22, %r27
	and %r22, %r8, %r22
	xor %r26, %r26, %r22
	ld %r22, 144(%r5)
	and %r22, %r7, %r22
	xor %r11, %r11, %r22
	and %r9, %r9, %r0
	xor %r24, %r24, %r9
	ld %r9, 120(%r5)
	ld %r0, 168(%r5)
	xor %r9, %r9, %r0
	and %r9, %r7, %r9
	xor %r9, %r24, %r9
	and %r9, %r10, %r9
	xor %r11, %r11, %r9
	ld %r9, 136(%r5)
	xor %r9, %r9, %r28
	xor %r24, %r24, %r20
	xor %r24, %r24, %r12
	ld %r12, 160(%r5)
	and %r7, %r7, %r12
	xor %r24, %r24, %r7
	and %r10, %r10, %r24
	xor %r9, %r9, %r10
	and %r8, %r8, %r9
	xor %r9, %r11, %r8
	ld %r6, 152(%r5)
	or %r7, %r21, %r21
	or %r8, %r26, %r26
	li %r20, 1
	and %r6, %r6, %r20
	rldicl %r6, %r6, 11, 0
	xor %r14, %r14, %r6
	and %r7, %r7, %r20
	rldicl %r7, %r7, 17, 0
	xor %r14, %r14, %r7
	and %r8, %r8, %r20
	rldicl %r8, %r8, 5, 0
	xor %r14, %r14, %r8
	and %r9, %r9, %r20
	rldicl %r9, %r9, 27, 0
	xor %r14, %r14, %r9
	or %r6, %r14, %r14
	or %r14, %r15, %r15
	or %r15, %r6, %r6
	add %r17, %r17, %r18
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 25b
	or %r6, %r14, %r14
	or %r14, %r15, %r15
	or %r15, %r6, %r6
	addi %r19, %r19, -1
	cmpldi %cr0, %r19, 0
	bne %cr0, 20b
	rldicl %r6, %r14, 32, 0
	xor %r6, %r6, %r15
	li %r8, 0
	li %r10, 1
	rldicl %r9, %r6, 40, 24
	and %r9, %r9, %r10
	rldicl %r9, %r9, 63, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 8, 56
	and %r9, %r9, %r10
	rldicl %r9, %r9, 62, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 48, 16
	and %r9, %r9, %r10
	rldicl %r9, %r9, 61, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 16, 48
	and %r9, %r9, %r10
	rldicl %r9, %r9, 60, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 56, 8
	and %r9, %r9, %r10
	rldicl %r9, %r9, 59, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 24, 40
	and %r9, %r9, %r10
	rldicl %r9, %r9, 58, 0
	xor %r8, %r8, %r9
	or %r9, %r6, %r6
	and %r9, %r9, %r10
	rldicl %r9, %r9, 57, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 32, 32
	and %r9, %r9, %r10
	rldicl %r9, %r9, 56, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 39, 25
	and %r9, %r9, %r10
	rldicl %r9, %r9, 55, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 7, 57
	and %r9, %r9, %r10
	rldicl %r9, %r9, 54, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 47, 17
	and %r9, %r9, %r10
	rldicl %r9, %r9, 53, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 15, 49
	and %r9, %r9, %r10
	rldicl %r9, %r9, 52, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 55, 9
	and %r9, %r9, %r10
	rldicl %r9, %r9, 51, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 23, 41
	and %r9, %r9, %r10
	rldicl %r9, %r9, 50, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 63, 1
	and %r9, %r9, %r10
	rldicl %r9, %r9, 49, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 31, 33
	and %r9, %r9, %r10
	rldicl %r9, %r9, 48, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 38, 26
	and %r9, %r9, %r10
	rldicl %r9, %r9, 47, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 6, 58
	and %r9, %r9, %r10
	rldicl %r9, %r9, 46, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 46, 18
	and %r9, %r9, %r10
	rldicl %r9, %r9, 45, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 14, 50
	and %r9, %r9, %r10
	rldicl %r9, %r9, 44, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 54, 10
	and %r9, %r9, %r10
	rldicl %r9, %r9, 43, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 22, 42
	and %r9, %r9, %r10
	rldicl %r9, %r9, 42, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 62, 2
	and %r9, %r9, %r10
	rldicl %r9, %r9, 41, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 30, 34
	and %r9, %r9, %r10
	rldicl %r9, %r9, 40, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 37, 27
	and %r9, %r9, %r10
	rldicl %r9, %r9, 39, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 5, 59
	and %r9, %r9, %r10
	rldicl %r9, %r9, 38, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 45, 19
	and %r9, %r9, %r10
	rldicl %r9, %r9, 37, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 13, 51
	and %r9, %r9, %r10
	rldicl %r9, %r9, 36, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 53, 11
	and %r9, %r9, %r10
	rldicl %r9, %r9, 35, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 21, 43
	and %r9, %r9, %r10
	rldicl %r9, %r9, 34, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 61, 3
	and %r9, %r9, %r10
	rldicl %r9, %r9, 33, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 29, 35
	and %r9, %r9, %r10
	rldicl %r9, %r9, 32, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 36, 28
	and %r9, %r9, %r10
	rldicl %r9, %r9, 31, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 4, 60
	and %r9, %r9, %r10
	rldicl %r9, %r9, 30, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 44, 20
	and %r9, %r9, %r10
	rldicl %r9, %r9, 29, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 12, 52
	and %r9, %r9, %r10
	rldicl %r9, %r9, 28, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 52, 12
	and %r9, %r9, %r10
	rldicl %r9, %r9, 27, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 20, 44
	and %r9, %r9, %r10
	rldicl %r9, %r9, 26, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 60, 4
	and %r9, %r9, %r10
	rldicl %r9, %r9, 25, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 28, 36
	and %r9, %r9, %r10
	rldicl %r9, %r9, 24, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 35, 29
	and %r9, %r9, %r10
	rldicl %r9, %r9, 23, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 3, 61
	and %r9, %r9, %r10
	rldicl %r9, %r9, 22, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 43, 21
	and %r9, %r9, %r10
	rldicl %r9, %r9, 21, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 11, 53
	and %r9, %r9, %r10
	rldicl %r9, %r9, 20, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 51, 13
	and %r9, %r9, %r10
	rldicl %r9, %r9, 19, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 19, 45
	and %r9, %r9, %r10
	rldicl %r9, %r9, 18, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 59, 5
	and %r9, %r9, %r10
	rldicl %r9, %r9, 17, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 27, 37
	and %r9, %r9, %r10
	rldicl %r9, %r9, 16, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 34, 30
	and %r9, %r9, %r10
	rldicl %r9, %r9, 15, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 2, 62
	and %r9, %r9, %r10
	rldicl %r9, %r9, 14, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 42, 22
	and %r9, %r9, %r10
	rldicl %r9, %r9, 13, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 10, 54
	and %r9, %r9, %r10
	rldicl %r9, %r9, 12, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 50, 14
	and %r9, %r9, %r10
	rldicl %r9, %r9, 11, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 18, 46
	and %r9, %r9, %r10
	rldicl %r9, %r9, 10, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 58, 6
	and %r9, %r9, %r10
	rldicl %r9, %r9, 9, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 26, 38
	and %r9, %r9, %r10
	rldicl %r9, %r9, 8, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 33, 31
	and %r9, %r9, %r10
	rldicl %r9, %r9, 7, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 1, 63
	and %r9, %r9, %r10
	rldicl %r9, %r9, 6, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 41, 23
	and %r9, %r9, %r10
	rldicl %r9, %r9, 5, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 9, 55
	and %r9, %r9, %r10
	rldicl %r9, %r9, 4, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 49, 15
	and %r9, %r9, %r10
	rldicl %r9, %r9, 3, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 17, 47
	and %r9, %r9, %r10
	rldicl %r9, %r9, 2, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 57, 7
	and %r9, %r9, %r10
	rldicl %r9, %r9, 1, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 25, 39
	and %r9, %r9, %r10
	xor %r8, %r8, %r9
	li %r7, 0
	stdbrx %r8, %r4, %r7
	ld %r14, 0(%r5)
	ld %r15, 8(%r5)
	ld %r16, 16(%r5)
	ld %r17, 24(%r5)
	ld %r18, 32(%r5)
	ld %r19, 40(%r5)
	ld %r20, 48(%r5)
	ld %r21, 56(%r5)
	ld %r22, 64(%r5)
	ld %r23, 72(%r5)
	ld %r24, 80(%r5)
	ld %r25, 88(%r5)
	ld %r26, 96(%r5)
	ld %r27, 104(%r5)
	ld %r28, 112(%r5)
	blr

vg_triple_des_decrypt_block:
	std %r14, 0(%r5)
	std %r15, 8(%r5)
	std %r16, 16(%r5)
	std %r17, 24(%r5)
	std %r18, 32(%r5)
	std %r19, 40(%r5)
	std %r20, 48(%r5)
	std %r21, 56(%r5)
	std %r22, 64(%r5)
	std %r23, 72(%r5)
	std %r24, 80(%r5)
	std %r25, 88(%r5)
	std %r26, 96(%r5)
	std %r27, 104(%r5)
	std %r28, 112(%r5)
	li %r6, 0
	ldbrx %r7, %r4, %r6
	li %r8, 0
	li %r10, 1
	rldicl %r9, %r7, 58, 6
	and %r9, %r9, %r10
	rldicl %r9, %r9, 63, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 50, 14
	and %r9, %r9, %r10
	rldicl %r9, %r9, 62, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 42, 22
	and %r9, %r9, %r10
	rldicl %r9, %r9, 61, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 34, 30
	and %r9, %r9, %r10
	rldicl %r9, %r9, 60, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 26, 38
	and %r9, %r9, %r10
	rldicl %r9, %r9, 59, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 18, 46
	and %r9, %r9, %r10
	rldicl %r9, %r9, 58, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 10, 54
	and %r9, %r9, %r10
	rldicl %r9, %r9, 57, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 2, 62
	and %r9, %r9, %r10
	rldicl %r9, %r9, 56, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 60, 4
	and %r9, %r9, %r10
	rldicl %r9, %r9, 55, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 52, 12
	and %r9, %r9, %r10
	rldicl %r9, %r9, 54, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 44, 20
	and %r9, %r9, %r10
	rldicl %r9, %r9, 53, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 36, 28
	and %r9, %r9, %r10
	rldicl %r9, %r9, 52, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 28, 36
	and %r9, %r9, %r10
	rldicl %r9, %r9, 51, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 20, 44
	and %r9, %r9, %r10
	rldicl %r9, %r9, 50, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 12, 52
	and %r9, %r9, %r10
	rldicl %r9, %r9, 49, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 4, 60
	and %r9, %r9, %r10
	rldicl %r9, %r9, 48, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 62, 2
	and %r9, %r9, %r10
	rldicl %r9, %r9, 47, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 54, 10
	and %r9, %r9, %r10
	rldicl %r9, %r9, 46, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 46, 18
	and %r9, %r9, %r10
	rldicl %r9, %r9, 45, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 38, 26
	and %r9, %r9, %r10
	rldicl %r9, %r9, 44, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 30, 34
	and %r9, %r9, %r10
	rldicl %r9, %r9, 43, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 22, 42
	and %r9, %r9, %r10
	rldicl %r9, %r9, 42, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 14, 50
	and %r9, %r9, %r10
	rldicl %r9, %r9, 41, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 6, 58
	and %r9, %r9, %r10
	rldicl %r9, %r9, 40, 0
	xor %r8, %r8, %r9
	or %r9, %r7, %r7
	and %r9, %r9, %r10
	rldicl %r9, %r9, 39, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 56, 8
	and %r9, %r9, %r10
	rldicl %r9, %r9, 38, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 48, 16
	and %r9, %r9, %r10
	rldicl %r9, %r9, 37, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 40, 24
	and %r9, %r9, %r10
	rldicl %r9, %r9, 36, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 32, 32
	and %r9, %r9, %r10
	rldicl %r9, %r9, 35, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 24, 40
	and %r9, %r9, %r10
	rldicl %r9, %r9, 34, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 16, 48
	and %r9, %r9, %r10
	rldicl %r9, %r9, 33, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 8, 56
	and %r9, %r9, %r10
	rldicl %r9, %r9, 32, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 57, 7
	and %r9, %r9, %r10
	rldicl %r9, %r9, 31, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 49, 15
	and %r9, %r9, %r10
	rldicl %r9, %r9, 30, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 41, 23
	and %r9, %r9, %r10
	rldicl %r9, %r9, 29, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 33, 31
	and %r9, %r9, %r10
	rldicl %r9, %r9, 28, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 25, 39
	and %r9, %r9, %r10
	rldicl %r9, %r9, 27, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 17, 47
	and %r9, %r9, %r10
	rldicl %r9, %r9, 26, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 9, 55
	and %r9, %r9, %r10
	rldicl %r9, %r9, 25, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 1, 63
	and %r9, %r9, %r10
	rldicl %r9, %r9, 24, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 59, 5
	and %r9, %r9, %r10
	rldicl %r9, %r9, 23, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 51, 13
	and %r9, %r9, %r10
	rldicl %r9, %r9, 22, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 43, 21
	and %r9, %r9, %r10
	rldicl %r9, %r9, 21, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 35, 29
	and %r9, %r9, %r10
	rldicl %r9, %r9, 20, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 27, 37
	and %r9, %r9, %r10
	rldicl %r9, %r9, 19, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 19, 45
	and %r9, %r9, %r10
	rldicl %r9, %r9, 18, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 11, 53
	and %r9, %r9, %r10
	rldicl %r9, %r9, 17, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 3, 61
	and %r9, %r9, %r10
	rldicl %r9, %r9, 16, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 61, 3
	and %r9, %r9, %r10
	rldicl %r9, %r9, 15, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 53, 11
	and %r9, %r9, %r10
	rldicl %r9, %r9, 14, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 45, 19
	and %r9, %r9, %r10
	rldicl %r9, %r9, 13, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 37, 27
	and %r9, %r9, %r10
	rldicl %r9, %r9, 12, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 29, 35
	and %r9, %r9, %r10
	rldicl %r9, %r9, 11, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 21, 43
	and %r9, %r9, %r10
	rldicl %r9, %r9, 10, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 13, 51
	and %r9, %r9, %r10
	rldicl %r9, %r9, 9, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 5, 59
	and %r9, %r9, %r10
	rldicl %r9, %r9, 8, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 63, 1
	and %r9, %r9, %r10
	rldicl %r9, %r9, 7, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 55, 9
	and %r9, %r9, %r10
	rldicl %r9, %r9, 6, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 47, 17
	and %r9, %r9, %r10
	rldicl %r9, %r9, 5, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 39, 25
	and %r9, %r9, %r10
	rldicl %r9, %r9, 4, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 31, 33
	and %r9, %r9, %r10
	rldicl %r9, %r9, 3, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 23, 41
	and %r9, %r9, %r10
	rldicl %r9, %r9, 2, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 15, 49
	and %r9, %r9, %r10
	rldicl %r9, %r9, 1, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r7, 7, 57
	and %r9, %r9, %r10
	xor %r8, %r8, %r9
	rldicl %r14, %r8, 32, 32
	rlwinm %r15, %r8, 0, 0, 31
	li %r19, 3
20:
	addi %r20, %r19, -3
	cmpldi %cr0, %r20, 0
	beq %cr0, 21f
	addi %r20, %r19, -2
	cmpldi %cr0, %r20, 0
	beq %cr0, 23f
	addi %r17, %r3, 120
	li %r16, 16
	li %r18, 0
	addi %r18, %r18, -8
	b 24f
23:
	addi %r17, %r3, 128
	li %r16, 16
	li %r18, 0
	addi %r18, %r18, 8
24:
	b 22f
21:
	addi %r17, %r3, 376
	li %r16, 16
	li %r18, 0
	addi %r18, %r18, -8
22:
25:
	ld %r20, 0(%r17)
	li %r22, 1
	rldicl %r6, %r15, 37, 27
	rldicl %r21, %r20, 22, 42
	xor %r6, %r6, %r21
	and %r6, %r6, %r22
	rldicl %r7, %r15, 36, 28
	rldicl %r21, %r20, 21, 43
	xor %r7, %r7, %r21
	and %r7, %r7, %r22
	rldicl %r8, %r15, 35, 29
	rldicl %r21, %r20, 20, 44
	xor %r8, %r8, %r21
	and %r8, %r8, %r22
	rldicl %r9, %r15, 34, 30
	rldicl %r21, %r20, 19, 45
	xor %r9, %r9, %r21
	and %r9, %r9, %r22
	rldicl %r10, %r15, 33, 31
	rldicl %r21, %r20, 18, 46
	xor %r10, %r10, %r21
	and %r10, %r10, %r22
	or %r11, %r15, %r15
	rldicl %r21, %r20, 17, 47
	xor %r11, %r11, %r21
	and %r11, %r11, %r22
	li %r12, 0
	addi %r12, %r12, -1
	xor %r20, %r6, %r6
	xor %r21, %r6, %r20
	xor %r21, %r21, %r12
	and %r22, %r10, %r21
	xor %r23, %r6, %r10
	and %r24, %r7, %r23
	xor %r24, %r22, %r24
	xor %r25, %r21, %r22
	and %r26, %r7, %r25
	xor %r26, %r6, %r26
	and %r26, %r11, %r26
	xor %r24, %r24, %r26
	and %r26, %r10, %r6
	xor %r27, %r26, %r20
	xor %r27, %r27, %r12
	and %r28, %r7, %r27
	xor %r0, %r26, %r28
	std %r23, 120(%r5)
	xor %r23, %r10, %r20
	xor %r23, %r23, %r12
	std %r6, 128(%r5)
	xor %r6, %r23, %r28
	std %r28, 136(%r5)
	and %r28, %r11, %r6
	xor %r0, %r0, %r28
	and %r0, %r9, %r0
	xor %r24, %r24, %r0
	and %r10, %r7, %r10
	xor %r0, %r27, %r10
	and %r28, %r7, %r23
	std %r10, 144(%r5)
	xor %r10, %r21, %r28
	and %r10, %r11, %r10
	xor %r0, %r0, %r10
	and %r10, %r7, %r21
	std %r23, 152(%r5)
	xor %r23, %r25, %r10
	and %r23, %r11, %r23
	and %r23, %r9, %r23
	xor %r0, %r0, %r23
	and %r0, %r8, %r0
	xor %r24, %r24, %r0
	xor %r21, %r21, %r26
	xor %r26, %r21, %r28
	xor %r0, %r22, %r20
	xor %r0, %r0, %r12
	and %r21, %r7, %r21
	xor %r21, %r0, %r21
	and %r23, %r11, %r21
	xor %r26, %r26, %r23
	xor %r23, %r25, %r20
	xor %r23, %r23, %r12
	xor %r28, %r23, %r28
	std %r24, 160(%r5)
	and %r24, %r7, %r22
	xor %r22, %r22, %r24
	and %r22, %r11, %r22
	xor %r24, %r28, %r22
	and %r24, %r9, %r24
	xor %r26, %r26, %r24
	xor %r21, %r21, %r22
	ld %r22, 128(%r5)
	and %r24, %r7, %r22
	std %r6, 168(%r5)
	xor %r6, %r0, %r24
	and %r6, %r11, %r6
	std %r12, 176(%r5)
	xor %r12, %r25, %r6
	and %r12, %r9, %r12
	xor %r21, %r21, %r12
	and %r21, %r8, %r21
	xor %r26, %r26, %r21
	xor %r21, %r25, %r24
	and %r12, %r11, %r28
	xor %r21, %r21, %r12
	xor %r27, %r27, %r10
	and %r23, %r7, %r23
	xor %r0, %r0, %r23
	and %r0, %r11, %r0
	xor %r27, %r27, %r0
	and %r27, %r9, %r27
	xor %r21, %r21, %r27
	ld %r27, 136(%r5)
	and %r0, %r11, %r27
	xor %r28, %r28, %r0
	xor %r22, %r22, %r24
	xor %r22, %r22, %r6
	and %r22, %r9, %r22
	xor %r28, %r28, %r22
	and %r28, %r8, %r28
	xor %r21, %r21, %r28
	ld %r28, 120(%r5)
	xor %r28, %r28, %r20
	ld %r22, 176(%r5)
	xor %r28, %r28, %r22
	xor %r28, %r28, %r7
	xor %r27, %r27, %r20
	xor %r27, %r27, %r22
	and %r27, %r11, %r27
	xor %r27, %r28, %r27
	ld %r6, 168(%r5)
	xor %r6, %r6, %r20
	xor %r6, %r6, %r22
	and %r6, %r11, %r6
	ld %r22, 152(%r5)
	xor %r22, %r22, %r6
	and %r22, %r9, %r22
	xor %r27, %r27, %r22
	ld %r22, 144(%r5)
	xor %r22, %r25, %r22
	and %r22, %r11, %r22
	xor %r24, %r24, %r22
	xor %r25, %r25, %r7
	and %r11, %r11, %r25
	xor %r28, %r28, %r11
	and %r9, %r9, %r28
	xor %r24, %r24, %r9
	and %r8, %r8, %r24
	xor %r9, %r27, %r8
	ld %r6, 160(%r5)
	or %r7, %r26, %r26
	or %r8, %r21, %r21
	li %r20, 1
	and %r6, %r6, %r20
	rldicl %r6, %r6, 1, 0
	xor %r14, %r14, %r6
	and %r7, %r7, %r20
	rldicl %r7, %r7, 9, 0
	xor %r14, %r14, %r7
	and %r8, %r8, %r20
	rldicl %r8, %r8, 15, 0
	xor %r14, %r14, %r8
	and %r9, %r9, %r20
	rldicl %r9, %r9, 23, 0
	xor %r14, %r14, %r9
	ld %r20, 0(%r17)
	li %r22, 1
	rldicl %r6, %r15, 41, 23
	rldicl %r21, %r20, 28, 36
	xor %r6, %r6, %r21
	and %r6, %r6, %r22
	rldicl %r7, %r15, 40, 24
	rldicl %r21, %r20, 27, 37
	xor %r7, %r7, %r21
	and %r7, %r7, %r22
	rldicl %r8, %r15, 39, 25
	rldicl %r21, %r20, 26, 38
	xor %r8, %r8, %r21
	and %r8, %r8, %r22
	rldicl %r9, %r15, 38, 26
	rldicl %r21, %r20, 25, 39
	xor %r9, %r9, %r21
	and %r9, %r9, %r22
	rldicl %r10, %r15, 37, 27
	rldicl %r21, %r20, 24, 40
	xor %r10, %r10, %r21
	and %r10, %r10, %r22
	rldicl %r11, %r15, 36, 28
	rldicl %r21, %r20, 23, 41
	xor %r11, %r11, %r21
	and %r11, %r11, %r22
	li %r12, 0
	addi %r12, %r12, -1
	xor %r20, %r6, %r6
	xor %r21, %r6, %r6
	xor %r21, %r21, %r12
	xor %r22, %r11, %r20
	xor %r22, %r22, %r12
	and %r23, %r7, %r11
	xor %r24, %r11, %r23
	and %r25, %r6, %r24
	xor %r25, %r22, %r25
	xor %r26, %r23, %r20
	xor %r26, %r26, %r12
	and %r27, %r6, %r26
	xor %r28, %r24, %r27
	and %r28, %r10, %r28
	xor %r25, %r25, %r28
	and %r0, %r7, %r22
	std %r27, 120(%r5)
	xor %r27, %r22, %r0
	xor %r24, %r24, %r20
	xor %r24, %r24, %r12
	std %r22, 128(%r5)
	and %r22, %r6, %r24
	std %r26, 136(%r5)
	xor %r26, %r27, %r22
	std %r22, 144(%r5)
	xor %r22, %r27, %r20
	xor %r22, %r22, %r12
	std %r27, 152(%r5)
	and %r27, %r6, %r22
	xor %r27, %r7, %r27
	and %r27, %r10, %r27
	xor %r26, %r26, %r27
	and %r26, %r9, %r26
	xor %r25, %r25, %r26
	and %r26, %r6, %r0
	xor %r26, %r21, %r26
	xor %r27, %r11, %r7
	std %r0, 160(%r5)
	and %r0, %r6, %r27
	std %r21, 168(%r5)
	xor %r21, %r7, %r0
	and %r21, %r10, %r21
	xor %r26, %r26, %r21
	and %r26, %r8, %r26
	xor %r25, %r25, %r26
	xor %r27, %r27, %r20
	xor %r27, %r27, %r12
	and %r23, %r6, %r23
	xor %r26, %r27, %r23
	xor %r24, %r24, %r0
	and %r24, %r10, %r24
	xor %r26, %r26, %r24
	xor %r22, %r22, %r28
	and %r22, %r9, %r22
	xor %r26, %r26, %r22
	ld %r22, 152(%r5)
	and %r28, %r6, %r22
	xor %r28, %r11, %r28
	and %r28, %r10, %r28
	ld %r24, 136(%r5)
	xor %r28, %r24, %r28
	ld %r0, 128(%r5)
	and %r21, %r6, %r0
	xor %r22, %r22, %r21
	and %r11, %r10, %r11
	xor %r22, %r22, %r11
	and %r22, %r9, %r22
	xor %r28, %r28, %r22
	and %r28, %r8, %r28
	xor %r26, %r26, %r28
	xor %r28, %r27, %r6
	xor %r28, %r28, %r10
	xor %r22, %r24, %r23
	and %r22, %r10, %r22
	xor %r22, %r6, %r22
	and %r22, %r9, %r22
	xor %r28, %r28, %r22
	and %r6, %r6, %r7
	ld %r7, 168(%r5)
	xor %r7, %r7, %r6
	ld %r22, 120(%r5)
	xor %r24, %r24, %r22
	and %r24, %r10, %r24
	xor %r7, %r7, %r24
	and %r6, %r9, %r6
	xor %r7, %r7, %r6
	and %r7, %r8, %r7
	xor %r28, %r28, %r7
	xor %r27, %r27, %r22
	ld %r22, 144(%r5)
	and %r22, %r10, %r22
	xor %r27, %r27, %r22
	xor %r22, %r23, %r20
	xor %r22, %r22, %r12
	xor %r0, %r0, %r21
	and %r0, %r10, %r0
	xor %r22, %r22, %r0
	and %r9, %r9, %r22
	xor %r27, %r27, %r9
	ld %r9, 160(%r5)
	xor %r9, %r9, %r23
	xor %r20, %r9, %r20
	xor %r20, %r20, %r12
	and %r10, %r10, %r20
	xor %r9, %r9, %r10
	and %r8, %r8, %r9
	xor %r9, %r27, %r8
	or %r6, %r25, %r25
	or %r7, %r26, %r26
	or %r8, %r28, %r28
	li %r20, 1
	and %r6, %r6, %r20
	rldicl %r6, %r6, 14, 0
	xor %r14, %r14, %r6
	and %r7, %r7, %r20
	rldicl %r7, %r7, 30, 0
	xor %r14, %r14, %r7
	and %r8, %r8, %r20
	rldicl %r8, %r8, 4, 0
	xor %r14, %r14, %r8
	and %r9, %r9, %r20
	rldicl %r9, %r9, 19, 0
	xor %r14, %r14, %r9
	ld %r20, 0(%r17)
	li %r22, 1
	rldicl %r6, %r15, 45, 19
	rldicl %r21, %r20, 34, 30
	xor %r6, %r6, %r21
	and %r6, %r6, %r22
	rldicl %r7, %r15, 44, 20
	rldicl %r21, %r20, 33, 31
	xor %r7, %r7, %r21
	and %r7, %r7, %r22
	rldicl %r8, %r15, 43, 21
	rldicl %r21, %r20, 32, 32
	xor %r8, %r8, %r21
	and %r8, %r8, %r22
	rldicl %r9, %r15, 42, 22
	rldicl %r21, %r20, 31, 33
	xor %r9, %r9, %r21
	and %r9, %r9, %r22
	rldicl %r10, %r15, 41, 23
	rldicl %r21, %r20, 30, 34
	xor %r10, %r10, %r21
	and %r10, %r10, %r22
	rldicl %r11, %r15, 40, 24
	rldicl %r21, %r20, 29, 35
	xor %r11, %r11, %r21
	and %r11, %r11, %r22
	li %r12, 0
	addi %r12, %r12, -1
	xor %r20, %r6, %r6
	xor %r21, %r6, %r6
	xor %r21, %r21, %r12
	xor %r22, %r11, %r20
	xor %r22, %r22, %r12
	and %r23, %r10, %r22
	xor %r24, %r11, %r23
	and %r25, %r10, %r11
	xor %r26, %r22, %r25
	and %r27, %r6, %r26
	xor %r28, %r24, %r27
	xor %r0, %r26, %r20
	xor %r0, %r0, %r12
	and %r25, %r6, %r25
	std %r24, 120(%r5)
	xor %r24, %r0, %r25
	std %r0, 128(%r5)
	and %r0, %r7, %r24
	xor %r0, %r28, %r0
	std %r28, 136(%r5)
	and %r28, %r7, %r26
	xor %r24, %r24, %r28
	and %r24, %r9, %r24
	xor %r0, %r0, %r24
	and %r11, %r6, %r11
	xor %r21, %r21, %r11
	and %r24, %r7, %r22
	xor %r21, %r21, %r24
	and %r25, %r9, %r25
	xor %r21, %r21, %r25
	and %r21, %r8, %r21
	xor %r0, %r0, %r21
	xor %r21, %r22, %r10
	xor %r27, %r21, %r27
	xor %r25, %r23, %r20
	xor %r25, %r25, %r12
	and %r24, %r6, %r23
	xor %r24, %r25, %r24
	and %r28, %r7, %r24
	std %r0, 144(%r5)
	xor %r0, %r27, %r28
	std %r26, 152(%r5)
	xor %r26, %r10, %r20
	xor %r26, %r26, %r12
	std %r21, 160(%r5)
	and %r21, %r6, %r26
	xor %r10, %r10, %r21
	std %r26, 168(%r5)
	and %r26, %r6, %r22
	xor %r22, %r22, %r26
	and %r22, %r7, %r22
	xor %r10, %r10, %r22
	and %r10, %r9, %r10
	xor %r0, %r0, %r10
	ld %r10, 136(%r5)
	xor %r10, %r10, %r20
	xor %r10, %r10, %r12
	xor %r27, %r27, %r20
	xor %r27, %r27, %r12
	and %r27, %r7, %r27
	xor %r10, %r10, %r27
	ld %r27, 120(%r5)
	xor %r22, %r27, %r20
	xor %r22, %r22, %r12
	and %r27, %r6, %r22
	std %r22, 136(%r5)
	xor %r22, %r25, %r27
	std %r27, 176(%r5)
	xor %r27, %r26, %r20
	xor %r27, %r27, %r12
	and %r27, %r7, %r27
	xor %r22, %r22, %r27
	and %r22, %r9, %r22
	xor %r10, %r10, %r22
	and %r10, %r8, %r10
	xor %r0, %r0, %r10
	and %r10, %r6, %r25
	ld %r22, 128(%r5)
	xor %r22, %r22, %r10
	xor %r10, %r24, %r20
	xor %r10, %r10, %r12
	and %r10, %r7, %r10
	xor %r22, %r22, %r10
	xor %r24, %r24, %r28
	and %r24, %r9, %r24
	xor %r22, %r22, %r24
	xor %r21, %r23, %r21
	xor %r21, %r21, %r27
	and %r27, %r7, %r11
	xor %r23, %r23, %r27
	and %r23, %r9, %r23
	xor %r21, %r21, %r23
	and %r21, %r8, %r21
	xor %r22, %r22, %r21
	xor %r25, %r25, %r11
	xor %r25, %r25, %r7
	ld %r11, 160(%r5)
	xor %r11, %r11, %r20
	xor %r11, %r11, %r12
	and %r6, %r6, %r11
	ld %r11, 168(%r5)
	xor %r11, %r11, %r6
	and %r11, %r7, %r11
	ld %r6, 152(%r5)
	xor %r6, %r6, %r11
	and %r6, %r9, %r6
	xor %r25, %r25, %r6
	ld %r6, 120(%r5)
	xor %r6, %r6, %r26
	ld %r11, 136(%r5)
	ld %r12, 176(%r5)
	xor %r12, %r11, %r12
	and %r12, %r7, %r12
	xor %r6, %r6, %r12
	and %r7, %r7, %r26
	xor %r11, %r11, %r7
	and %r9, %r9, %r11
	xor %r6, %r6, %r9
	and %r8, %r8, %r6
	xor %r9, %r25, %r8
	ld %r6, 144(%r5)
	or %r7, %r0, %r0
	or %r8, %r22, %r22
	li %r20, 1
	and %r6, %r6, %r20
	rldicl %r6, %r6, 26, 0
	xor %r14, %r14, %r6
	and %r7, %r7, %r20
	rldicl %r7, %r7, 2, 0
	xor %r14, %r14, %r7
	and %r8, %r8, %r20
	rldicl %r8, %r8, 16, 0
	xor %r14, %r14, %r8
	and %r9, %r9, %r20
	rldicl %r9, %r9, 8, 0
	xor %r14, %r14, %r9
	ld %r20, 0(%r17)
	li %r22, 1
	rldicl %r6, %r15, 49, 15
	rldicl %r21, %r20, 40, 24
	xor %r6, %r6, %r21
	and %r6, %r6, %r22
	rldicl %r7, %r15, 48, 16
	rldicl %r21, %r20, 39, 25
	xor %r7, %r7, %r21
	and %r7, %r7, %r22
	rldicl %r8, %r15, 47, 17
	rldicl %r21, %r20, 38, 26
	xor %r8, %r8, %r21
	and %r8, %r8, %r22
	rldicl %r9, %r15, 46, 18
	rldicl %r21, %r20, 37, 27
	xor %r9, %r9, %r21
	and %r9, %r9, %r22
	rldicl %r10, %r15, 45, 19
	rldicl %r21, %r20, 36, 28
	xor %r10, %r10, %r21
	and %r10, %r10, %r22
	rldicl %r11, %r15, 44, 20
	rldicl %r21, %r20, 35, 29
	xor %r11, %r11, %r21
	and %r11, %r11, %r22
	li %r12, 0
	addi %r12, %r12, -1
	xor %r20, %r6, %r6
	xor %r21, %r6, %r6
	xor %r21, %r21, %r12
	xor %r22, %r9, %r20
	xor %r22, %r22, %r12
	and %r23, %r7, %r9
	xor %r24, %r22, %r23
	and %r25, %r11, %r24
	xor %r26, %r22, %r25
	xor %r27, %r9, %r7
	xor %r28, %r27, %r20
	xor %r28, %r28, %r12
	and %r0, %r11, %r28
	std %r25, 120(%r5)
	xor %r25, %r27, %r0
	and %r25, %r10, %r25
	xor %r26, %r26, %r25
	xor %r25, %r7, %r20
	xor %r25, %r25, %r12
	std %r9, 128(%r5)
	xor %r9, %r7, %r0
	std %r0, 136(%r5)
	and %r0, %r10, %r9
	std %r6, 144(%r5)
	xor %r6, %r25, %r0
	and %r6, %r8, %r6
	xor %r26, %r26, %r6
	xor %r6, %r24, %r20
	xor %r6, %r6, %r12
	and %r6, %r11, %r6
	xor %r6, %r28, %r6
	and %r6, %r10, %r6
	xor %r9, %r9, %r6
	xor %r23, %r23, %r20
	xor %r23, %r23, %r12
	and %r6, %r7, %r22
	xor %r21, %r21, %r6
	std %r0, 152(%r5)
	and %r0, %r11, %r21
	xor %r23, %r23, %r0
	and %r27, %r10, %r27
	xor %r23, %r23, %r27
	and %r23, %r8, %r23
	xor %r9, %r9, %r23
	ld %r23, 144(%r5)
	std %r27, 160(%r5)
	and %r27, %r23, %r9
	xor %r26, %r26, %r27
	and %r27, %r11, %r6
	xor %r28, %r28, %r27
	std %r26, 168(%r5)
	xor %r26, %r0, %r20
	xor %r26, %r26, %r12
	and %r26, %r10, %r26
	xor %r26, %r28, %r26
	std %r11, 176(%r5)
	xor %r11, %r6, %r0
	std %r6, 184(%r5)
	ld %r6, 128(%r5)
	std %r25, 192(%r5)
	ld %r25, 136(%r5)
	xor %r25, %r6, %r25
	and %r25, %r10, %r25
	xor %r11, %r11, %r25
	and %r11, %r8, %r11
	xor %r26, %r26, %r11
	xor %r9, %r9, %r20
	xor %r9, %r9, %r12
	and %r9, %r23, %r9
	xor %r26, %r26, %r9
	xor %r24, %r24, %r0
	and %r22, %r10, %r22
	xor %r24, %r24, %r22
	xor %r7, %r7, %r25
	and %r7, %r8, %r7
	xor %r24, %r24, %r7
	xor %r28, %r28, %r20
	xor %r28, %r28, %r12
	xor %r21, %r21, %r27
	and %r21, %r10, %r21
	xor %r28, %r28, %r21
	ld %r21, 192(%r5)
	ld %r7, 120(%r5)
	xor %r21, %r21, %r7
	ld %r25, 160(%r5)
	xor %r21, %r21, %r25
	and %r21, %r8, %r21
	xor %r28, %r28, %r21
	and %r21, %r23, %r28
	xor %r24, %r24, %r21
	ld %r21, 184(%r5)
	ld %r25, 176(%r5)
	xor %r25, %r21, %r25
	xor %r6, %r6, %r21
	xor %r6, %r6, %r27
	and %r10, %r10, %r6
	xor %r25, %r25, %r10
	xor %r7, %r7, %r20
	xor %r7, %r7, %r12
	ld %r10, 152(%r5)
	xor %r7, %r7, %r10
	and %r8, %r8, %r7
	xor %r25, %r25, %r8
	xor %r28, %r28, %r20
	xor %r28, %r28, %r12
	and %r23, %r23, %r28
	xor %r9, %r25, %r23
	ld %r6, 168(%r5)
	or %r7, %r26, %r26
	or %r8, %r24, %r24
	li %r20, 1
	and %r6, %r6, %r20
	rldicl %r6, %r6, 31, 0
	xor %r14, %r14, %r6
	and %r7, %r7, %r20
	rldicl %r7, %r7, 22, 0
	xor %r14, %r14, %r7
	and %r8, %r8, %r20
	rldicl %r8, %r8, 12, 0
	xor %r14, %r14, %r8
	and %r9, %r9, %r20
	rldicl %r9, %r9, 6, 0
	xor %r14, %r14, %r9
	ld %r20, 0(%r17)
	li %r22, 1
	rldicl %r6, %r15, 53, 11
	rldicl %r21, %r20, 46, 18
	xor %r6, %r6, %r21
	and %r6, %r6, %r22
	rldicl %r7, %r15, 52, 12
	rldicl %r21, %r20, 45, 19
	xor %r7, %r7, %r21
	and %r7, %r7, %r22
	rldicl %r8, %r15, 51, 13
	rldicl %r21, %r20, 44, 20
	xor %r8, %r8, %r21
	and %r8, %r8, %r22
	rldicl %r9, %r15, 50, 14
	rldicl %r21, %r20, 43, 21
	xor %r9, %r9, %r21
	and %r9, %r9, %r22
	rldicl %r10, %r15, 49, 15
	rldicl %r21, %r20, 42, 22
	xor %r10, %r10, %r21
	and %r10, %r10, %r22
	rldicl %r11, %r15, 48, 16
	rldicl %r21, %r20, 41, 23
	xor %r11, %r11, %r21
	and %r11, %r11, %r22
	li %r12, 0
	addi %r12, %r12, -1
	xor %r20, %r6, %r6
	xor %r21, %r6, %r6
	xor %r21, %r21, %r12
	xor %r22, %r9, %r20
	xor %r22, %r22, %r12
	and %r23, %r22, %r11
	xor %r24, %r21, %r23
	xor %r6, %r6, %r20
	xor %r6, %r6, %r12
	and %r25, %r6, %r24
	xor %r26, %r11, %r25
	xor %r27, %r11, %r20
	xor %r27, %r27, %r12
	and %r28, %r22, %r27
	xor %r0, %r27, %r28
	xor %r10, %r10, %r20
	xor %r10, %r10, %r12
	std %r25, 120(%r5)
	and %r25, %r10, %r0
	xor %r25, %r26, %r25
	std %r26, 128(%r5)
	xor %r26, %r27, %r23
	std %r21, 136(%r5)
	and %r21, %r10, %r26
	xor %r21, %r9, %r21
	xor %r8, %r8, %r20
	xor %r8, %r8, %r12
	and %r21, %r8, %r21
	xor %r25, %r25, %r21
	and %r21, %r6, %r27
	xor %r21, %r22, %r21
	std %r9, 144(%r5)
	xor %r9, %r11, %r22
	and %r23, %r6, %r23
	xor %r23, %r9, %r23
	and %r23, %r10, %r23
	xor %r21, %r21, %r23
	xor %r23, %r0, %r20
	xor %r23, %r23, %r12
	and %r23, %r6, %r23
	std %r22, 152(%r5)
	xor %r22, %r27, %r6
	and %r22, %r10, %r22
	xor %r23, %r23, %r22
	and %r23, %r8, %r23
	xor %r21, %r21, %r23
	xor %r7, %r7, %r20
	xor %r7, %r7, %r12
	and %r21, %r7, %r21
	xor %r25, %r25, %r21
	and %r21, %r6, %r0
	xor %r23, %r24, %r21
	xor %r23, %r23, %r10
	xor %r22, %r28, %r20
	xor %r22, %r22, %r12
	std %r25, 160(%r5)
	and %r25, %r6, %r22
	std %r24, 168(%r5)
	ld %r24, 136(%r5)
	xor %r24, %r24, %r25
	and %r28, %r6, %r28
	std %r12, 136(%r5)
	and %r12, %r10, %r28
	xor %r24, %r24, %r12
	and %r24, %r8, %r24
	xor %r23, %r23, %r24
	xor %r28, %r26, %r28
	and %r28, %r10, %r28
	ld %r24, 144(%r5)
	xor %r28, %r24, %r28
	and %r11, %r6, %r11
	xor %r27, %r27, %r11
	and %r12, %r10, %r27
	xor %r12, %r25, %r12
	and %r12, %r8, %r12
	xor %r28, %r28, %r12
	and %r28, %r7, %r28
	xor %r23, %r23, %r28
	xor %r28, %r0, %r6
	xor %r28, %r28, %r10
	xor %r22, %r22, %r21
	xor %r21, %r9, %r25
	and %r21, %r10, %r21
	xor %r22, %r22, %r21
	and %r22, %r8, %r22
	xor %r28, %r28, %r22
	xor %r22, %r9, %r20
	ld %r21, 136(%r5)
	xor %r22, %r22, %r21
	and %r12, %r6, %r22
	xor %r0, %r0, %r12
	and %r0, %r8, %r0
	std %r23, 176(%r5)
	ld %r23, 168(%r5)
	xor %r23, %r23, %r0
	and %r23, %r7, %r23
	xor %r28, %r28, %r23
	ld %r23, 152(%r5)
	xor %r23, %r23, %r25
	ld %r25, 128(%r5)
	and %r25, %r10, %r25
	xor %r23, %r23, %r25
	xor %r25, %r26, %r6
	and %r25, %r10, %r25
	xor %r27, %r27, %r25
	and %r27, %r8, %r27
	xor %r23, %r23, %r27
	ld %r27, 120(%r5)
	xor %r22, %r22, %r27
	and %r6, %r6, %r24
	xor %r9, %r9, %r6
	and %r9, %r10, %r9
	xor %r22, %r22, %r9
	xor %r26, %r26, %r20
	xor %r26, %r26, %r21
	xor %r26, %r26, %r12
	xor %r11, %r11, %r20
	xor %r11, %r11, %r21
	and %r10, %r10, %r11
	xor %r26, %r26, %r10
	and %r8, %r8, %r26
	xor %r22, %r22, %r8
	and %r7, %r7, %r22
	xor %r9, %r23, %r7
	ld %r6, 160(%r5)
	ld %r7, 176(%r5)
	or %r8, %r28, %r28
	li %r20, 1
	and %r6, %r6, %r20
	rldicl %r6, %r6, 29, 0
	xor %r14, %r14, %r6
	and %r7, %r7, %r20
	rldicl %r7, %r7, 7, 0
	xor %r14, %r14, %r7
	and %r8, %r8, %r20
	rldicl %r8, %r8, 18, 0
	xor %r14, %r14, %r8
	and %r9, %r9, %r20
	rldicl %r9, %r9, 24, 0
	xor %r14, %r14, %r9
	ld %r20, 0(%r17)
	li %r22, 1
	rldicl %r6, %r15, 57, 7
	rldicl %r21, %r20, 52, 12
	xor %r6, %r6, %r21
	and %r6, %r6, %r22
	rldicl %r7, %r15, 56, 8
	rldicl %r21, %r20, 51, 13
	xor %r7, %r7, %r21
	and %r7, %r7, %r22
	rldicl %r8, %r15, 55, 9
	rldicl %r21, %r20, 50, 14
	xor %r8, %r8, %r21
	and %r8, %r8, %r22
	rldicl %r9, %r15, 54, 10
	rldicl %r21, %r20, 49, 15
	xor %r9, %r9, %r21
	and %r9, %r9, %r22
	rldicl %r10, %r15, 53, 11
	rldicl %r21, %r20, 48, 16
	xor %r10, %r10, %r21
	and %r10, %r10, %r22
	rldicl %r11, %r15, 52, 12
	rldicl %r21, %r20, 47, 17
	xor %r11, %r11, %r21
	and %r11, %r11, %r22
	li %r12, 0
	addi %r12, %r12, -1
	xor %r20, %r6, %r6
	xor %r21, %r6, %r6
	xor %r21, %r21, %r12
	xor %r22, %r10, %r20
	xor %r22, %r22, %r12
	and %r23, %r9, %r22
	xor %r24, %r23, %r7
	xor %r25, %r10, %r23
	and %r26, %r7, %r9
	xor %r27, %r25, %r26
	and %r27, %r8, %r27
	xor %r24, %r24, %r27
	xor %r27, %r26, %r20
	xor %r27, %r27, %r12
	xor %r28, %r9, %r20
	xor %r28, %r28, %r12
	and %r0, %r7, %r28
	std %r26, 120(%r5)
	xor %r26, %r9, %r0
	std %r28, 128(%r5)
	and %r28, %r8, %r26
	xor %r27, %r27, %r28
	and %r27, %r11, %r27
	xor %r24, %r24, %r27
	xor %r27, %r22, %r9
	std %r26, 136(%r5)
	and %r26, %r7, %r27
	std %r28, 144(%r5)
	xor %r28, %r23, %r26
	and %r28, %r8, %r28
	and %r9, %r9, %r10
	std %r0, 152(%r5)
	xor %r0, %r22, %r9
	std %r22, 160(%r5)
	xor %r22, %r27, %r20
	xor %r22, %r22, %r12
	xor %r22, %r22, %r26
	and %r22, %r8, %r22
	xor %r22, %r0, %r22
	and %r22, %r11, %r22
	xor %r28, %r28, %r22
	and %r28, %r6, %r28
	xor %r24, %r24, %r28
	and %r28, %r7, %r23
	xor %r22, %r9, %r28
	and %r10, %r7, %r10
	xor %r21, %r21, %r10
	std %r24, 168(%r5)
	and %r24, %r8, %r21
	xor %r22, %r22, %r24
	ld %r24, 152(%r5)
	xor %r25, %r25, %r24
	and %r10, %r8, %r10
	xor %r25, %r25, %r10
	and %r25, %r11, %r25
	xor %r22, %r22, %r25
	and %r25, %r8, %r7
	xor %r21, %r21, %r25
	ld %r25, 128(%r5)
	xor %r25, %r25, %r28
	std %r0, 128(%r5)
	ld %r0, 160(%r5)
	std %r28, 176(%r5)
	and %r28, %r7, %r0
	std %r10, 184(%r5)
	and %r10, %r8, %r28
	xor %r25, %r25, %r10
	and %r25, %r11, %r25
	xor %r21, %r21, %r25
	and %r21, %r6, %r21
	xor %r22, %r22, %r21
	xor %r27, %r27, %r24
	ld %r21, 120(%r5)
	xor %r0, %r0, %r21
	and %r0, %r8, %r0
	xor %r27, %r27, %r0
	xor %r0, %r23, %r20
	xor %r0, %r0, %r12
	and %r21, %r7, %r9
	xor %r21, %r0, %r21
	and %r26, %r8, %r26
	xor %r21, %r21, %r26
	and %r21, %r11, %r21
	xor %r27, %r27, %r21
	ld %r21, 184(%r5)
	xor %r21, %r21, %r20
	xor %r21, %r21, %r12
	ld %r12, 176(%r5)
	xor %r23, %r23, %r12
	xor %r9, %r9, %r7
	and %r9, %r8, %r9
	xor %r23, %r23, %r9
	and %r23, %r11, %r23
	xor %r21, %r21, %r23
	and %r21, %r6, %r21
	xor %r27, %r27, %r21
	ld %r21, 128(%r5)
	xor %r23, %r21, %r7
	ld %r9, 144(%r5)
	xor %r23, %r23, %r9
	ld %r9, 136(%r5)
	and %r12, %r11, %r9
	xor %r23, %r23, %r12
	xor %r24, %r0, %r24
	and %r24, %r8, %r24
	xor %r9, %r9, %r24
	and %r7, %r7, %r0
	xor %r0, %r0, %r7
	xor %r21, %r21, %r28
	and %r8, %r8, %r21
	xor %r0, %r0, %r8
	and %r11, %r11, %r0
	xor %r9, %r9, %r11
	and %r6, %r6, %r9
	xor %r9, %r23, %r6
	ld %r6, 168(%r5)
	or %r7, %r22, %r22
	or %r8, %r27, %r27
	li %r20, 1
	and %r6, %r6, %r20
	rldicl %r6, %r6, 13, 0
	xor %r14, %r14, %r6
	and %r7, %r7, %r20
	rldicl %r7, %r7, 21, 0
	xor %r14, %r14, %r7
	and %r8, %r8, %r20
	rldicl %r8, %r8, 3, 0
	xor %r14, %r14, %r8
	and %r9, %r9, %r20
	rldicl %r9, %r9, 28, 0
	xor %r14, %r14, %r9
	ld %r20, 0(%r17)
	li %r22, 1
	rldicl %r6, %r15, 61, 3
	rldicl %r21, %r20, 58, 6
	xor %r6, %r6, %r21
	and %r6, %r6, %r22
	rldicl %r7, %r15, 60, 4
	rldicl %r21, %r20, 57, 7
	xor %r7, %r7, %r21
	and %r7, %r7, %r22
	rldicl %r8, %r15, 59, 5
	rldicl %r21, %r20, 56, 8
	xor %r8, %r8, %r21
	and %r8, %r8, %r22
	rldicl %r9, %r15, 58, 6
	rldicl %r21, %r20, 55, 9
	xor %r9, %r9, %r21
	and %r9, %r9, %r22
	rldicl %r10, %r15, 57, 7
	rldicl %r21, %r20, 54, 10
	xor %r10, %r10, %r21
	and %r10, %r10, %r22
	rldicl %r11, %r15, 56, 8
	rldicl %r21, %r20, 53, 11
	xor %r11, %r11, %r21
	and %r11, %r11, %r22
	li %r12, 0
	addi %r12, %r12, -1
	xor %r20, %r6, %r6
	xor %r21, %r6, %r6
	xor %r21, %r21, %r12
	xor %r22, %r11, %r6
	and %r23, %r6, %r11
	and %r24, %r8, %r23
	xor %r25, %r22, %r24
	xor %r26, %r23, %r20
	xor %r26, %r26, %r12
	and %r27, %r8, %r26
	xor %r28, %r21, %r27
	and %r0, %r9, %r28
	xor %r25, %r25, %r0
	xor %r0, %r11, %r20
	xor %r0, %r0, %r12
	std %r24, 120(%r5)
	and %r24, %r6, %r0
	std %r0, 128(%r5)
	and %r0, %r8, %r24
	std %r24, 136(%r5)
	xor %r24, %r21, %r0
	std %r21, 144(%r5)
	and %r21, %r9, %r26
	xor %r24, %r24, %r21
	and %r24, %r10, %r24
	xor %r25, %r25, %r24
	and %r24, %r9, %r27
	xor %r28, %r28, %r24
	and %r24, %r8, %r6
	xor %r24, %r23, %r24
	and %r24, %r10, %r24
	xor %r28, %r28, %r24
	and %r28, %r7, %r28
	xor %r25, %r25, %r28
	xor %r28, %r23, %r8
	xor %r24, %r22, %r20
	xor %r24, %r24, %r12
	std %r25, 152(%r5)
	xor %r25, %r24, %r0
	and %r25, %r9, %r25
	xor %r28, %r28, %r25
	and %r25, %r8, %r11
	std %r21, 160(%r5)
	ld %r21, 144(%r5)
	std %r22, 168(%r5)
	xor %r22, %r21, %r25
	xor %r23, %r11, %r23
	xor %r21, %r23, %r0
	and %r21, %r9, %r21
	xor %r22, %r22, %r21
	and %r22, %r10, %r22
	xor %r28, %r28, %r22
	ld %r22, 128(%r5)
	std %r0, 176(%r5)
	ld %r0, 136(%r5)
	std %r25, 184(%r5)
	xor %r25, %r22, %r0
	xor %r6, %r6, %r20
	xor %r6, %r6, %r12
	and %r6, %r8, %r6
	xor %r6, %r25, %r6
	xor %r6, %r6, %r21
	and %r21, %r8, %r24
	std %r25, 192(%r5)
	and %r25, %r9, %r23
	xor %r21, %r21, %r25
	and %r21, %r10, %r21
	xor %r6, %r6, %r21
	and %r6, %r7, %r6
	xor %r28, %r28, %r6
	xor %r23, %r23, %r20
	xor %r23, %r23, %r12
	and %r22, %r8, %r22
	xor %r12, %r23, %r22
	and %r20, %r9, %r11
	xor %r12, %r12, %r20
	xor %r24, %r24, %r27
	ld %r27, 184(%r5)
	xor %r26, %r26, %r27
	and %r26, %r9, %r26
	xor %r24, %r24, %r26
	and %r24, %r10, %r24
	xor %r12, %r12, %r24
	ld %r24, 168(%r5)
	and %r24, %r8, %r24
	and %r24, %r9, %r24
	ld %r26, 144(%r5)
	xor %r26, %r26, %r24
	ld %r24, 176(%r5)
	and %r24, %r10, %r24
	xor %r26, %r26, %r24
	and %r26, %r7, %r26
	xor %r12, %r12, %r26
	xor %r0, %r0, %r27
	ld %r26, 160(%r5)
	xor %r0, %r0, %r26
	xor %r22, %r11, %r22
	ld %r26, 192(%r5)
	and %r8, %r8, %r26
	xor %r26, %r26, %r8
	and %r26, %r9, %r26
	xor %r22, %r22, %r26
	and %r22, %r10, %r22
	xor %r0, %r0, %r22
	ld %r22, 120(%r5)
	xor %r23, %r23, %r22
	xor %r11, %r11, %r8
	and %r9, %r9, %r11
	xor %r23, %r23, %r9
	xor %r27, %r27, %r20
	and %r10, %r10, %r27
	xor %r23, %r23, %r10
	and %r7, %r7, %r23
	xor %r9, %r0, %r7
	ld %r6, 152(%r5)
	or %r7, %r28, %r28
	or %r8, %r12, %r12
	li %r20, 1
	and %r6, %r6, %r20
	rldicl %r6, %r6, 25, 0
	xor %r14, %r14, %r6
	and %r7, %r7, %r20
	rldicl %r7, %r7, 10, 0
	xor %r14, %r14, %r7
	and %r8, %r8, %r20
	rldicl %r8, %r8, 20, 0
	xor %r14, %r14, %r8
	and %r9, %r9, %r20
	xor %r14, %r14, %r9
	ld %r20, 0(%r17)
	li %r22, 1
	rldicl %r6, %r15, 33, 31
	or %r21, %r20, %r20
	xor %r6, %r6, %r21
	and %r6, %r6, %r22
	or %r7, %r15, %r15
	rldicl %r21, %r20, 63, 1
	xor %r7, %r7, %r21
	and %r7, %r7, %r22
	rldicl %r8, %r15, 63, 1
	rldicl %r21, %r20, 62, 2
	xor %r8, %r8, %r21
	and %r8, %r8, %r22
	rldicl %r9, %r15, 62, 2
	rldicl %r21, %r20, 61, 3
	xor %r9, %r9, %r21
	and %r9, %r9, %r22
	rldicl %r10, %r15, 61, 3
	rldicl %r21, %r20, 60, 4
	xor %r10, %r10, %r21
	and %r10, %r10, %r22
	rldicl %r11, %r15, 60, 4
	rldicl %r21, %r20, 59, 5
	xor %r11, %r11, %r21
	and %r11, %r11, %r22
	li %r12, 0
	addi %r12, %r12, -1
	xor %r20, %r6, %r6
	xor %r21, %r6, %r6
	xor %r21, %r21, %r12
	xor %r22, %r6, %r20
	xor %r22, %r22, %r12
	xor %r23, %r11, %r22
	xor %r9, %r9, %r20
	xor %r9, %r9, %r12
	xor %r24, %r23, %r9
	xor %r7, %r7, %r20
	xor %r7, %r7, %r12
	xor %r24, %r24, %r7
	and %r25, %r9, %r6
	and %r26, %r22, %r11
	and %r27, %r9, %r26
	xor %r28, %r22, %r27
	and %r28, %r7, %r28
	xor %r28, %r25, %r28
	xor %r10, %r10, %r20
	xor %r10, %r10, %r12
	and %r28, %r10, %r28
	xor %r24, %r24, %r28
	xor %r28, %r11, %r20
	xor %r28, %r28, %r12
	and %r0, %r22, %r28
	std %r6, 120(%r5)
	xor %r6, %r21, %r0
	std %r23, 128(%r5)
	xor %r23, %r6, %r25
	and %r23, %r7, %r23
	xor %r22, %r22, %r23
	xor %r23, %r11, %r26
	std %r6, 136(%r5)
	and %r6, %r9, %r23
	xor %r21, %r21, %r6
	std %r25, 144(%r5)
	and %r25, %r7, %r28
	xor %r21, %r21, %r25
	and %r21, %r10, %r21
	xor %r22, %r22, %r21
	xor %r8, %r8, %r20
	xor %r8, %r8, %r12
	and %r22, %r8, %r22
	xor %r24, %r24, %r22
	xor %r22, %r26, %r20
	xor %r22, %r22, %r12
	xor %r21, %r22, %r6
	xor %r23, %r23, %r20
	xor %r23, %r23, %r12
	std %r24, 152(%r5)
	and %r24, %r9, %r23
	xor %r28, %r28, %r24
	and %r28, %r7, %r28
	xor %r21, %r21, %r28
	xor %r28, %r27, %r20
	xor %r28, %r28, %r12
	std %r23, 160(%r5)
	and %r23, %r7, %r27
	xor %r23, %r28, %r23
	and %r23, %r10, %r23
	xor %r21, %r21, %r23
	xor %r23, %r11, %r0
	std %r6, 168(%r5)
	ld %r6, 144(%r5)
	xor %r6, %r23, %r6
	std %r28, 144(%r5)
	ld %r28, 128(%r5)
	and %r28, %r7, %r28
	std %r26, 128(%r5)
	xor %r26, %r6, %r28
	xor %r6, %r6, %r20
	xor %r6, %r6, %r12
	xor %r23, %r23, %r20
	xor %r23, %r23, %r12
	and %r23, %r7, %r23
	xor %r6, %r6, %r23
	and %r6, %r10, %r6
	xor %r26, %r26, %r6
	and %r26, %r8, %r26
	xor %r21, %r21, %r26
	xor %r26, %r0, %r27
	and %r6, %r9, %r22
	xor %r11, %r11, %r6
	and %r6, %r7, %r11
	xor %r26, %r26, %r6
	xor %r24, %r22, %r24
	and %r24, %r10, %r24
	xor %r26, %r26, %r24
	xor %r22, %r22, %r25
	ld %r24, 128(%r5)
	xor %r27, %r24, %r27
	xor %r27, %r27, %r25
	and %r27, %r10, %r27
	xor %r22, %r22, %r27
	and %r22, %r8, %r22
	xor %r26, %r26, %r22
	ld %r22, 144(%r5)
	and %r22, %r7, %r22
	xor %r11, %r11, %r22
	and %r9, %r9, %r0
	xor %r24, %r24, %r9
	ld %r9, 120(%r5)
	ld %r0, 168(%r5)
	xor %r9, %r9, %r0
	and %r9, %r7, %r9
	xor %r9, %r24, %r9
	and %r9, %r10, %r9
	xor %r11, %r11, %r9
	ld %r9, 136(%r5)
	xor %r9, %r9, %r28
	xor %r24, %r24, %r20
	xor %r24, %r24, %r12
	ld %r12, 160(%r5)
	and %r7, %r7, %r12
	xor %r24, %r24, %r7
	and %r10, %r10, %r24
	xor %r9, %r9, %r10
	and %r8, %r8, %r9
	xor %r9, %r11, %r8
	ld %r6, 152(%r5)
	or %r7, %r21, %r21
	or %r8, %r26, %r26
	li %r20, 1
	and %r6, %r6, %r20
	rldicl %r6, %r6, 11, 0
	xor %r14, %r14, %r6
	and %r7, %r7, %r20
	rldicl %r7, %r7, 17, 0
	xor %r14, %r14, %r7
	and %r8, %r8, %r20
	rldicl %r8, %r8, 5, 0
	xor %r14, %r14, %r8
	and %r9, %r9, %r20
	rldicl %r9, %r9, 27, 0
	xor %r14, %r14, %r9
	or %r6, %r14, %r14
	or %r14, %r15, %r15
	or %r15, %r6, %r6
	add %r17, %r17, %r18
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 25b
	or %r6, %r14, %r14
	or %r14, %r15, %r15
	or %r15, %r6, %r6
	addi %r19, %r19, -1
	cmpldi %cr0, %r19, 0
	bne %cr0, 20b
	rldicl %r6, %r14, 32, 0
	xor %r6, %r6, %r15
	li %r8, 0
	li %r10, 1
	rldicl %r9, %r6, 40, 24
	and %r9, %r9, %r10
	rldicl %r9, %r9, 63, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 8, 56
	and %r9, %r9, %r10
	rldicl %r9, %r9, 62, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 48, 16
	and %r9, %r9, %r10
	rldicl %r9, %r9, 61, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 16, 48
	and %r9, %r9, %r10
	rldicl %r9, %r9, 60, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 56, 8
	and %r9, %r9, %r10
	rldicl %r9, %r9, 59, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 24, 40
	and %r9, %r9, %r10
	rldicl %r9, %r9, 58, 0
	xor %r8, %r8, %r9
	or %r9, %r6, %r6
	and %r9, %r9, %r10
	rldicl %r9, %r9, 57, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 32, 32
	and %r9, %r9, %r10
	rldicl %r9, %r9, 56, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 39, 25
	and %r9, %r9, %r10
	rldicl %r9, %r9, 55, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 7, 57
	and %r9, %r9, %r10
	rldicl %r9, %r9, 54, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 47, 17
	and %r9, %r9, %r10
	rldicl %r9, %r9, 53, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 15, 49
	and %r9, %r9, %r10
	rldicl %r9, %r9, 52, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 55, 9
	and %r9, %r9, %r10
	rldicl %r9, %r9, 51, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 23, 41
	and %r9, %r9, %r10
	rldicl %r9, %r9, 50, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 63, 1
	and %r9, %r9, %r10
	rldicl %r9, %r9, 49, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 31, 33
	and %r9, %r9, %r10
	rldicl %r9, %r9, 48, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 38, 26
	and %r9, %r9, %r10
	rldicl %r9, %r9, 47, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 6, 58
	and %r9, %r9, %r10
	rldicl %r9, %r9, 46, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 46, 18
	and %r9, %r9, %r10
	rldicl %r9, %r9, 45, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 14, 50
	and %r9, %r9, %r10
	rldicl %r9, %r9, 44, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 54, 10
	and %r9, %r9, %r10
	rldicl %r9, %r9, 43, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 22, 42
	and %r9, %r9, %r10
	rldicl %r9, %r9, 42, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 62, 2
	and %r9, %r9, %r10
	rldicl %r9, %r9, 41, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 30, 34
	and %r9, %r9, %r10
	rldicl %r9, %r9, 40, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 37, 27
	and %r9, %r9, %r10
	rldicl %r9, %r9, 39, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 5, 59
	and %r9, %r9, %r10
	rldicl %r9, %r9, 38, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 45, 19
	and %r9, %r9, %r10
	rldicl %r9, %r9, 37, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 13, 51
	and %r9, %r9, %r10
	rldicl %r9, %r9, 36, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 53, 11
	and %r9, %r9, %r10
	rldicl %r9, %r9, 35, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 21, 43
	and %r9, %r9, %r10
	rldicl %r9, %r9, 34, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 61, 3
	and %r9, %r9, %r10
	rldicl %r9, %r9, 33, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 29, 35
	and %r9, %r9, %r10
	rldicl %r9, %r9, 32, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 36, 28
	and %r9, %r9, %r10
	rldicl %r9, %r9, 31, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 4, 60
	and %r9, %r9, %r10
	rldicl %r9, %r9, 30, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 44, 20
	and %r9, %r9, %r10
	rldicl %r9, %r9, 29, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 12, 52
	and %r9, %r9, %r10
	rldicl %r9, %r9, 28, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 52, 12
	and %r9, %r9, %r10
	rldicl %r9, %r9, 27, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 20, 44
	and %r9, %r9, %r10
	rldicl %r9, %r9, 26, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 60, 4
	and %r9, %r9, %r10
	rldicl %r9, %r9, 25, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 28, 36
	and %r9, %r9, %r10
	rldicl %r9, %r9, 24, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 35, 29
	and %r9, %r9, %r10
	rldicl %r9, %r9, 23, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 3, 61
	and %r9, %r9, %r10
	rldicl %r9, %r9, 22, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 43, 21
	and %r9, %r9, %r10
	rldicl %r9, %r9, 21, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 11, 53
	and %r9, %r9, %r10
	rldicl %r9, %r9, 20, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 51, 13
	and %r9, %r9, %r10
	rldicl %r9, %r9, 19, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 19, 45
	and %r9, %r9, %r10
	rldicl %r9, %r9, 18, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 59, 5
	and %r9, %r9, %r10
	rldicl %r9, %r9, 17, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 27, 37
	and %r9, %r9, %r10
	rldicl %r9, %r9, 16, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 34, 30
	and %r9, %r9, %r10
	rldicl %r9, %r9, 15, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 2, 62
	and %r9, %r9, %r10
	rldicl %r9, %r9, 14, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 42, 22
	and %r9, %r9, %r10
	rldicl %r9, %r9, 13, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 10, 54
	and %r9, %r9, %r10
	rldicl %r9, %r9, 12, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 50, 14
	and %r9, %r9, %r10
	rldicl %r9, %r9, 11, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 18, 46
	and %r9, %r9, %r10
	rldicl %r9, %r9, 10, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 58, 6
	and %r9, %r9, %r10
	rldicl %r9, %r9, 9, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 26, 38
	and %r9, %r9, %r10
	rldicl %r9, %r9, 8, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 33, 31
	and %r9, %r9, %r10
	rldicl %r9, %r9, 7, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 1, 63
	and %r9, %r9, %r10
	rldicl %r9, %r9, 6, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 41, 23
	and %r9, %r9, %r10
	rldicl %r9, %r9, 5, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 9, 55
	and %r9, %r9, %r10
	rldicl %r9, %r9, 4, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 49, 15
	and %r9, %r9, %r10
	rldicl %r9, %r9, 3, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 17, 47
	and %r9, %r9, %r10
	rldicl %r9, %r9, 2, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 57, 7
	and %r9, %r9, %r10
	rldicl %r9, %r9, 1, 0
	xor %r8, %r8, %r9
	rldicl %r9, %r6, 25, 39
	and %r9, %r9, %r10
	xor %r8, %r8, %r9
	li %r7, 0
	stdbrx %r8, %r4, %r7
	ld %r14, 0(%r5)
	ld %r15, 8(%r5)
	ld %r16, 16(%r5)
	ld %r17, 24(%r5)
	ld %r18, 32(%r5)
	ld %r19, 40(%r5)
	ld %r20, 48(%r5)
	ld %r21, 56(%r5)
	ld %r22, 64(%r5)
	ld %r23, 72(%r5)
	ld %r24, 80(%r5)
	ld %r25, 88(%r5)
	ld %r26, 96(%r5)
	ld %r27, 104(%r5)
	ld %r28, 112(%r5)
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
