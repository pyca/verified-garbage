// The functions of `src/triple_des.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_triple_des_expand_key:
	.option push
	.option arch, +m, +c
	lbu t0, 0(a0)
	slli t0, t0, 8
	lbu t1, 1(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 2(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 3(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 4(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 5(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 6(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 7(a0)
	or t0, t0, t1
	andi t2, t0, 0
	srli t3, t0, 7
	andi t3, t3, 1
	slli t3, t3, 55
	xor t2, t2, t3
	srli t3, t0, 15
	andi t3, t3, 1
	slli t3, t3, 54
	xor t2, t2, t3
	srli t3, t0, 23
	andi t3, t3, 1
	slli t3, t3, 53
	xor t2, t2, t3
	srli t3, t0, 31
	andi t3, t3, 1
	slli t3, t3, 52
	xor t2, t2, t3
	srli t3, t0, 39
	andi t3, t3, 1
	slli t3, t3, 51
	xor t2, t2, t3
	srli t3, t0, 47
	andi t3, t3, 1
	slli t3, t3, 50
	xor t2, t2, t3
	srli t3, t0, 55
	andi t3, t3, 1
	slli t3, t3, 49
	xor t2, t2, t3
	srli t3, t0, 63
	andi t3, t3, 1
	slli t3, t3, 48
	xor t2, t2, t3
	srli t3, t0, 6
	andi t3, t3, 1
	slli t3, t3, 47
	xor t2, t2, t3
	srli t3, t0, 14
	andi t3, t3, 1
	slli t3, t3, 46
	xor t2, t2, t3
	srli t3, t0, 22
	andi t3, t3, 1
	slli t3, t3, 45
	xor t2, t2, t3
	srli t3, t0, 30
	andi t3, t3, 1
	slli t3, t3, 44
	xor t2, t2, t3
	srli t3, t0, 38
	andi t3, t3, 1
	slli t3, t3, 43
	xor t2, t2, t3
	srli t3, t0, 46
	andi t3, t3, 1
	slli t3, t3, 42
	xor t2, t2, t3
	srli t3, t0, 54
	andi t3, t3, 1
	slli t3, t3, 41
	xor t2, t2, t3
	srli t3, t0, 62
	andi t3, t3, 1
	slli t3, t3, 40
	xor t2, t2, t3
	srli t3, t0, 5
	andi t3, t3, 1
	slli t3, t3, 39
	xor t2, t2, t3
	srli t3, t0, 13
	andi t3, t3, 1
	slli t3, t3, 38
	xor t2, t2, t3
	srli t3, t0, 21
	andi t3, t3, 1
	slli t3, t3, 37
	xor t2, t2, t3
	srli t3, t0, 29
	andi t3, t3, 1
	slli t3, t3, 36
	xor t2, t2, t3
	srli t3, t0, 37
	andi t3, t3, 1
	slli t3, t3, 35
	xor t2, t2, t3
	srli t3, t0, 45
	andi t3, t3, 1
	slli t3, t3, 34
	xor t2, t2, t3
	srli t3, t0, 53
	andi t3, t3, 1
	slli t3, t3, 33
	xor t2, t2, t3
	srli t3, t0, 61
	andi t3, t3, 1
	slli t3, t3, 32
	xor t2, t2, t3
	srli t3, t0, 4
	andi t3, t3, 1
	slli t3, t3, 31
	xor t2, t2, t3
	srli t3, t0, 12
	andi t3, t3, 1
	slli t3, t3, 30
	xor t2, t2, t3
	srli t3, t0, 20
	andi t3, t3, 1
	slli t3, t3, 29
	xor t2, t2, t3
	srli t3, t0, 28
	andi t3, t3, 1
	slli t3, t3, 28
	xor t2, t2, t3
	srli t3, t0, 1
	andi t3, t3, 1
	slli t3, t3, 27
	xor t2, t2, t3
	srli t3, t0, 9
	andi t3, t3, 1
	slli t3, t3, 26
	xor t2, t2, t3
	srli t3, t0, 17
	andi t3, t3, 1
	slli t3, t3, 25
	xor t2, t2, t3
	srli t3, t0, 25
	andi t3, t3, 1
	slli t3, t3, 24
	xor t2, t2, t3
	srli t3, t0, 33
	andi t3, t3, 1
	slli t3, t3, 23
	xor t2, t2, t3
	srli t3, t0, 41
	andi t3, t3, 1
	slli t3, t3, 22
	xor t2, t2, t3
	srli t3, t0, 49
	andi t3, t3, 1
	slli t3, t3, 21
	xor t2, t2, t3
	srli t3, t0, 57
	andi t3, t3, 1
	slli t3, t3, 20
	xor t2, t2, t3
	srli t3, t0, 2
	andi t3, t3, 1
	slli t3, t3, 19
	xor t2, t2, t3
	srli t3, t0, 10
	andi t3, t3, 1
	slli t3, t3, 18
	xor t2, t2, t3
	srli t3, t0, 18
	andi t3, t3, 1
	slli t3, t3, 17
	xor t2, t2, t3
	srli t3, t0, 26
	andi t3, t3, 1
	slli t3, t3, 16
	xor t2, t2, t3
	srli t3, t0, 34
	andi t3, t3, 1
	slli t3, t3, 15
	xor t2, t2, t3
	srli t3, t0, 42
	andi t3, t3, 1
	slli t3, t3, 14
	xor t2, t2, t3
	srli t3, t0, 50
	andi t3, t3, 1
	slli t3, t3, 13
	xor t2, t2, t3
	srli t3, t0, 58
	andi t3, t3, 1
	slli t3, t3, 12
	xor t2, t2, t3
	srli t3, t0, 3
	andi t3, t3, 1
	slli t3, t3, 11
	xor t2, t2, t3
	srli t3, t0, 11
	andi t3, t3, 1
	slli t3, t3, 10
	xor t2, t2, t3
	srli t3, t0, 19
	andi t3, t3, 1
	slli t3, t3, 9
	xor t2, t2, t3
	srli t3, t0, 27
	andi t3, t3, 1
	slli t3, t3, 8
	xor t2, t2, t3
	srli t3, t0, 35
	andi t3, t3, 1
	slli t3, t3, 7
	xor t2, t2, t3
	srli t3, t0, 43
	andi t3, t3, 1
	slli t3, t3, 6
	xor t2, t2, t3
	srli t3, t0, 51
	andi t3, t3, 1
	slli t3, t3, 5
	xor t2, t2, t3
	srli t3, t0, 59
	andi t3, t3, 1
	slli t3, t3, 4
	xor t2, t2, t3
	srli t3, t0, 36
	andi t3, t3, 1
	slli t3, t3, 3
	xor t2, t2, t3
	srli t3, t0, 44
	andi t3, t3, 1
	slli t3, t3, 2
	xor t2, t2, t3
	srli t3, t0, 52
	andi t3, t3, 1
	slli t3, t3, 1
	xor t2, t2, t3
	srli t3, t0, 60
	andi t3, t3, 1
	xor t2, t2, t3
	srli a3, t2, 28
	addi a4, t2, 0
	slli a4, a4, 36
	srli a4, a4, 36
	addi a6, zero, 0
	addi a5, a2, 0
20:
	srli t0, a6, 1
	beqz t0, 21f
	addi t0, a6, -8
	beqz t0, 23f
	addi t0, a6, -15
	beqz t0, 25f
	srli t0, a3, 26
	slli a3, a3, 2
	xor a3, a3, t0
	slli a3, a3, 36
	srli a3, a3, 36
	srli t0, a4, 26
	slli a4, a4, 2
	xor a4, a4, t0
	slli a4, a4, 36
	srli a4, a4, 36
	j 26f
25:
	srli t0, a3, 27
	slli a3, a3, 1
	xor a3, a3, t0
	slli a3, a3, 36
	srli a3, a3, 36
	srli t0, a4, 27
	slli a4, a4, 1
	xor a4, a4, t0
	slli a4, a4, 36
	srli a4, a4, 36
26:
	j 24f
23:
	srli t0, a3, 27
	slli a3, a3, 1
	xor a3, a3, t0
	slli a3, a3, 36
	srli a3, a3, 36
	srli t0, a4, 27
	slli a4, a4, 1
	xor a4, a4, t0
	slli a4, a4, 36
	srli a4, a4, 36
24:
	j 22f
21:
	srli t0, a3, 27
	slli a3, a3, 1
	xor a3, a3, t0
	slli a3, a3, 36
	srli a3, a3, 36
	srli t0, a4, 27
	slli a4, a4, 1
	xor a4, a4, t0
	slli a4, a4, 36
	srli a4, a4, 36
22:
	slli t0, a3, 28
	xor t0, t0, a4
	andi t2, t0, 0
	srli t3, t0, 42
	andi t3, t3, 1
	slli t3, t3, 47
	xor t2, t2, t3
	srli t3, t0, 39
	andi t3, t3, 1
	slli t3, t3, 46
	xor t2, t2, t3
	srli t3, t0, 45
	andi t3, t3, 1
	slli t3, t3, 45
	xor t2, t2, t3
	srli t3, t0, 32
	andi t3, t3, 1
	slli t3, t3, 44
	xor t2, t2, t3
	srli t3, t0, 55
	andi t3, t3, 1
	slli t3, t3, 43
	xor t2, t2, t3
	srli t3, t0, 51
	andi t3, t3, 1
	slli t3, t3, 42
	xor t2, t2, t3
	srli t3, t0, 53
	andi t3, t3, 1
	slli t3, t3, 41
	xor t2, t2, t3
	srli t3, t0, 28
	andi t3, t3, 1
	slli t3, t3, 40
	xor t2, t2, t3
	srli t3, t0, 41
	andi t3, t3, 1
	slli t3, t3, 39
	xor t2, t2, t3
	srli t3, t0, 50
	andi t3, t3, 1
	slli t3, t3, 38
	xor t2, t2, t3
	srli t3, t0, 35
	andi t3, t3, 1
	slli t3, t3, 37
	xor t2, t2, t3
	srli t3, t0, 46
	andi t3, t3, 1
	slli t3, t3, 36
	xor t2, t2, t3
	srli t3, t0, 33
	andi t3, t3, 1
	slli t3, t3, 35
	xor t2, t2, t3
	srli t3, t0, 37
	andi t3, t3, 1
	slli t3, t3, 34
	xor t2, t2, t3
	srli t3, t0, 44
	andi t3, t3, 1
	slli t3, t3, 33
	xor t2, t2, t3
	srli t3, t0, 52
	andi t3, t3, 1
	slli t3, t3, 32
	xor t2, t2, t3
	srli t3, t0, 30
	andi t3, t3, 1
	slli t3, t3, 31
	xor t2, t2, t3
	srli t3, t0, 48
	andi t3, t3, 1
	slli t3, t3, 30
	xor t2, t2, t3
	srli t3, t0, 40
	andi t3, t3, 1
	slli t3, t3, 29
	xor t2, t2, t3
	srli t3, t0, 49
	andi t3, t3, 1
	slli t3, t3, 28
	xor t2, t2, t3
	srli t3, t0, 29
	andi t3, t3, 1
	slli t3, t3, 27
	xor t2, t2, t3
	srli t3, t0, 36
	andi t3, t3, 1
	slli t3, t3, 26
	xor t2, t2, t3
	srli t3, t0, 43
	andi t3, t3, 1
	slli t3, t3, 25
	xor t2, t2, t3
	srli t3, t0, 54
	andi t3, t3, 1
	slli t3, t3, 24
	xor t2, t2, t3
	srli t3, t0, 15
	andi t3, t3, 1
	slli t3, t3, 23
	xor t2, t2, t3
	srli t3, t0, 4
	andi t3, t3, 1
	slli t3, t3, 22
	xor t2, t2, t3
	srli t3, t0, 25
	andi t3, t3, 1
	slli t3, t3, 21
	xor t2, t2, t3
	srli t3, t0, 19
	andi t3, t3, 1
	slli t3, t3, 20
	xor t2, t2, t3
	srli t3, t0, 9
	andi t3, t3, 1
	slli t3, t3, 19
	xor t2, t2, t3
	srli t3, t0, 1
	andi t3, t3, 1
	slli t3, t3, 18
	xor t2, t2, t3
	srli t3, t0, 26
	andi t3, t3, 1
	slli t3, t3, 17
	xor t2, t2, t3
	srli t3, t0, 16
	andi t3, t3, 1
	slli t3, t3, 16
	xor t2, t2, t3
	srli t3, t0, 5
	andi t3, t3, 1
	slli t3, t3, 15
	xor t2, t2, t3
	srli t3, t0, 11
	andi t3, t3, 1
	slli t3, t3, 14
	xor t2, t2, t3
	srli t3, t0, 23
	andi t3, t3, 1
	slli t3, t3, 13
	xor t2, t2, t3
	srli t3, t0, 8
	andi t3, t3, 1
	slli t3, t3, 12
	xor t2, t2, t3
	srli t3, t0, 12
	andi t3, t3, 1
	slli t3, t3, 11
	xor t2, t2, t3
	srli t3, t0, 7
	andi t3, t3, 1
	slli t3, t3, 10
	xor t2, t2, t3
	srli t3, t0, 17
	andi t3, t3, 1
	slli t3, t3, 9
	xor t2, t2, t3
	addi t3, t0, 0
	andi t3, t3, 1
	slli t3, t3, 8
	xor t2, t2, t3
	srli t3, t0, 22
	andi t3, t3, 1
	slli t3, t3, 7
	xor t2, t2, t3
	srli t3, t0, 3
	andi t3, t3, 1
	slli t3, t3, 6
	xor t2, t2, t3
	srli t3, t0, 10
	andi t3, t3, 1
	slli t3, t3, 5
	xor t2, t2, t3
	srli t3, t0, 14
	andi t3, t3, 1
	slli t3, t3, 4
	xor t2, t2, t3
	srli t3, t0, 6
	andi t3, t3, 1
	slli t3, t3, 3
	xor t2, t2, t3
	srli t3, t0, 20
	andi t3, t3, 1
	slli t3, t3, 2
	xor t2, t2, t3
	srli t3, t0, 27
	andi t3, t3, 1
	slli t3, t3, 1
	xor t2, t2, t3
	srli t3, t0, 24
	andi t3, t3, 1
	xor t2, t2, t3
	sb t2, 0(a5)
	srli t1, t2, 8
	sb t1, 1(a5)
	srli t1, t2, 16
	sb t1, 2(a5)
	srli t1, t2, 24
	sb t1, 3(a5)
	srli t1, t2, 32
	sb t1, 4(a5)
	srli t4, t1, 8
	sb t4, 5(a5)
	srli t4, t1, 16
	sb t4, 6(a5)
	srli t4, t1, 24
	sb t4, 7(a5)
	addi a5, a5, 8
	addi a6, a6, 1
	addi t0, a6, -16
	bnez t0, 20b
	lbu t0, 8(a0)
	slli t0, t0, 8
	lbu t1, 9(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 10(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 11(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 12(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 13(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 14(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 15(a0)
	or t0, t0, t1
	andi t2, t0, 0
	srli t3, t0, 7
	andi t3, t3, 1
	slli t3, t3, 55
	xor t2, t2, t3
	srli t3, t0, 15
	andi t3, t3, 1
	slli t3, t3, 54
	xor t2, t2, t3
	srli t3, t0, 23
	andi t3, t3, 1
	slli t3, t3, 53
	xor t2, t2, t3
	srli t3, t0, 31
	andi t3, t3, 1
	slli t3, t3, 52
	xor t2, t2, t3
	srli t3, t0, 39
	andi t3, t3, 1
	slli t3, t3, 51
	xor t2, t2, t3
	srli t3, t0, 47
	andi t3, t3, 1
	slli t3, t3, 50
	xor t2, t2, t3
	srli t3, t0, 55
	andi t3, t3, 1
	slli t3, t3, 49
	xor t2, t2, t3
	srli t3, t0, 63
	andi t3, t3, 1
	slli t3, t3, 48
	xor t2, t2, t3
	srli t3, t0, 6
	andi t3, t3, 1
	slli t3, t3, 47
	xor t2, t2, t3
	srli t3, t0, 14
	andi t3, t3, 1
	slli t3, t3, 46
	xor t2, t2, t3
	srli t3, t0, 22
	andi t3, t3, 1
	slli t3, t3, 45
	xor t2, t2, t3
	srli t3, t0, 30
	andi t3, t3, 1
	slli t3, t3, 44
	xor t2, t2, t3
	srli t3, t0, 38
	andi t3, t3, 1
	slli t3, t3, 43
	xor t2, t2, t3
	srli t3, t0, 46
	andi t3, t3, 1
	slli t3, t3, 42
	xor t2, t2, t3
	srli t3, t0, 54
	andi t3, t3, 1
	slli t3, t3, 41
	xor t2, t2, t3
	srli t3, t0, 62
	andi t3, t3, 1
	slli t3, t3, 40
	xor t2, t2, t3
	srli t3, t0, 5
	andi t3, t3, 1
	slli t3, t3, 39
	xor t2, t2, t3
	srli t3, t0, 13
	andi t3, t3, 1
	slli t3, t3, 38
	xor t2, t2, t3
	srli t3, t0, 21
	andi t3, t3, 1
	slli t3, t3, 37
	xor t2, t2, t3
	srli t3, t0, 29
	andi t3, t3, 1
	slli t3, t3, 36
	xor t2, t2, t3
	srli t3, t0, 37
	andi t3, t3, 1
	slli t3, t3, 35
	xor t2, t2, t3
	srli t3, t0, 45
	andi t3, t3, 1
	slli t3, t3, 34
	xor t2, t2, t3
	srli t3, t0, 53
	andi t3, t3, 1
	slli t3, t3, 33
	xor t2, t2, t3
	srli t3, t0, 61
	andi t3, t3, 1
	slli t3, t3, 32
	xor t2, t2, t3
	srli t3, t0, 4
	andi t3, t3, 1
	slli t3, t3, 31
	xor t2, t2, t3
	srli t3, t0, 12
	andi t3, t3, 1
	slli t3, t3, 30
	xor t2, t2, t3
	srli t3, t0, 20
	andi t3, t3, 1
	slli t3, t3, 29
	xor t2, t2, t3
	srli t3, t0, 28
	andi t3, t3, 1
	slli t3, t3, 28
	xor t2, t2, t3
	srli t3, t0, 1
	andi t3, t3, 1
	slli t3, t3, 27
	xor t2, t2, t3
	srli t3, t0, 9
	andi t3, t3, 1
	slli t3, t3, 26
	xor t2, t2, t3
	srli t3, t0, 17
	andi t3, t3, 1
	slli t3, t3, 25
	xor t2, t2, t3
	srli t3, t0, 25
	andi t3, t3, 1
	slli t3, t3, 24
	xor t2, t2, t3
	srli t3, t0, 33
	andi t3, t3, 1
	slli t3, t3, 23
	xor t2, t2, t3
	srli t3, t0, 41
	andi t3, t3, 1
	slli t3, t3, 22
	xor t2, t2, t3
	srli t3, t0, 49
	andi t3, t3, 1
	slli t3, t3, 21
	xor t2, t2, t3
	srli t3, t0, 57
	andi t3, t3, 1
	slli t3, t3, 20
	xor t2, t2, t3
	srli t3, t0, 2
	andi t3, t3, 1
	slli t3, t3, 19
	xor t2, t2, t3
	srli t3, t0, 10
	andi t3, t3, 1
	slli t3, t3, 18
	xor t2, t2, t3
	srli t3, t0, 18
	andi t3, t3, 1
	slli t3, t3, 17
	xor t2, t2, t3
	srli t3, t0, 26
	andi t3, t3, 1
	slli t3, t3, 16
	xor t2, t2, t3
	srli t3, t0, 34
	andi t3, t3, 1
	slli t3, t3, 15
	xor t2, t2, t3
	srli t3, t0, 42
	andi t3, t3, 1
	slli t3, t3, 14
	xor t2, t2, t3
	srli t3, t0, 50
	andi t3, t3, 1
	slli t3, t3, 13
	xor t2, t2, t3
	srli t3, t0, 58
	andi t3, t3, 1
	slli t3, t3, 12
	xor t2, t2, t3
	srli t3, t0, 3
	andi t3, t3, 1
	slli t3, t3, 11
	xor t2, t2, t3
	srli t3, t0, 11
	andi t3, t3, 1
	slli t3, t3, 10
	xor t2, t2, t3
	srli t3, t0, 19
	andi t3, t3, 1
	slli t3, t3, 9
	xor t2, t2, t3
	srli t3, t0, 27
	andi t3, t3, 1
	slli t3, t3, 8
	xor t2, t2, t3
	srli t3, t0, 35
	andi t3, t3, 1
	slli t3, t3, 7
	xor t2, t2, t3
	srli t3, t0, 43
	andi t3, t3, 1
	slli t3, t3, 6
	xor t2, t2, t3
	srli t3, t0, 51
	andi t3, t3, 1
	slli t3, t3, 5
	xor t2, t2, t3
	srli t3, t0, 59
	andi t3, t3, 1
	slli t3, t3, 4
	xor t2, t2, t3
	srli t3, t0, 36
	andi t3, t3, 1
	slli t3, t3, 3
	xor t2, t2, t3
	srli t3, t0, 44
	andi t3, t3, 1
	slli t3, t3, 2
	xor t2, t2, t3
	srli t3, t0, 52
	andi t3, t3, 1
	slli t3, t3, 1
	xor t2, t2, t3
	srli t3, t0, 60
	andi t3, t3, 1
	xor t2, t2, t3
	srli a3, t2, 28
	addi a4, t2, 0
	slli a4, a4, 36
	srli a4, a4, 36
	addi a6, zero, 0
	addi a5, a2, 128
27:
	srli t0, a6, 1
	beqz t0, 28f
	addi t0, a6, -8
	beqz t0, 210f
	addi t0, a6, -15
	beqz t0, 212f
	srli t0, a3, 26
	slli a3, a3, 2
	xor a3, a3, t0
	slli a3, a3, 36
	srli a3, a3, 36
	srli t0, a4, 26
	slli a4, a4, 2
	xor a4, a4, t0
	slli a4, a4, 36
	srli a4, a4, 36
	j 213f
212:
	srli t0, a3, 27
	slli a3, a3, 1
	xor a3, a3, t0
	slli a3, a3, 36
	srli a3, a3, 36
	srli t0, a4, 27
	slli a4, a4, 1
	xor a4, a4, t0
	slli a4, a4, 36
	srli a4, a4, 36
213:
	j 211f
210:
	srli t0, a3, 27
	slli a3, a3, 1
	xor a3, a3, t0
	slli a3, a3, 36
	srli a3, a3, 36
	srli t0, a4, 27
	slli a4, a4, 1
	xor a4, a4, t0
	slli a4, a4, 36
	srli a4, a4, 36
211:
	j 29f
28:
	srli t0, a3, 27
	slli a3, a3, 1
	xor a3, a3, t0
	slli a3, a3, 36
	srli a3, a3, 36
	srli t0, a4, 27
	slli a4, a4, 1
	xor a4, a4, t0
	slli a4, a4, 36
	srli a4, a4, 36
29:
	slli t0, a3, 28
	xor t0, t0, a4
	andi t2, t0, 0
	srli t3, t0, 42
	andi t3, t3, 1
	slli t3, t3, 47
	xor t2, t2, t3
	srli t3, t0, 39
	andi t3, t3, 1
	slli t3, t3, 46
	xor t2, t2, t3
	srli t3, t0, 45
	andi t3, t3, 1
	slli t3, t3, 45
	xor t2, t2, t3
	srli t3, t0, 32
	andi t3, t3, 1
	slli t3, t3, 44
	xor t2, t2, t3
	srli t3, t0, 55
	andi t3, t3, 1
	slli t3, t3, 43
	xor t2, t2, t3
	srli t3, t0, 51
	andi t3, t3, 1
	slli t3, t3, 42
	xor t2, t2, t3
	srli t3, t0, 53
	andi t3, t3, 1
	slli t3, t3, 41
	xor t2, t2, t3
	srli t3, t0, 28
	andi t3, t3, 1
	slli t3, t3, 40
	xor t2, t2, t3
	srli t3, t0, 41
	andi t3, t3, 1
	slli t3, t3, 39
	xor t2, t2, t3
	srli t3, t0, 50
	andi t3, t3, 1
	slli t3, t3, 38
	xor t2, t2, t3
	srli t3, t0, 35
	andi t3, t3, 1
	slli t3, t3, 37
	xor t2, t2, t3
	srli t3, t0, 46
	andi t3, t3, 1
	slli t3, t3, 36
	xor t2, t2, t3
	srli t3, t0, 33
	andi t3, t3, 1
	slli t3, t3, 35
	xor t2, t2, t3
	srli t3, t0, 37
	andi t3, t3, 1
	slli t3, t3, 34
	xor t2, t2, t3
	srli t3, t0, 44
	andi t3, t3, 1
	slli t3, t3, 33
	xor t2, t2, t3
	srli t3, t0, 52
	andi t3, t3, 1
	slli t3, t3, 32
	xor t2, t2, t3
	srli t3, t0, 30
	andi t3, t3, 1
	slli t3, t3, 31
	xor t2, t2, t3
	srli t3, t0, 48
	andi t3, t3, 1
	slli t3, t3, 30
	xor t2, t2, t3
	srli t3, t0, 40
	andi t3, t3, 1
	slli t3, t3, 29
	xor t2, t2, t3
	srli t3, t0, 49
	andi t3, t3, 1
	slli t3, t3, 28
	xor t2, t2, t3
	srli t3, t0, 29
	andi t3, t3, 1
	slli t3, t3, 27
	xor t2, t2, t3
	srli t3, t0, 36
	andi t3, t3, 1
	slli t3, t3, 26
	xor t2, t2, t3
	srli t3, t0, 43
	andi t3, t3, 1
	slli t3, t3, 25
	xor t2, t2, t3
	srli t3, t0, 54
	andi t3, t3, 1
	slli t3, t3, 24
	xor t2, t2, t3
	srli t3, t0, 15
	andi t3, t3, 1
	slli t3, t3, 23
	xor t2, t2, t3
	srli t3, t0, 4
	andi t3, t3, 1
	slli t3, t3, 22
	xor t2, t2, t3
	srli t3, t0, 25
	andi t3, t3, 1
	slli t3, t3, 21
	xor t2, t2, t3
	srli t3, t0, 19
	andi t3, t3, 1
	slli t3, t3, 20
	xor t2, t2, t3
	srli t3, t0, 9
	andi t3, t3, 1
	slli t3, t3, 19
	xor t2, t2, t3
	srli t3, t0, 1
	andi t3, t3, 1
	slli t3, t3, 18
	xor t2, t2, t3
	srli t3, t0, 26
	andi t3, t3, 1
	slli t3, t3, 17
	xor t2, t2, t3
	srli t3, t0, 16
	andi t3, t3, 1
	slli t3, t3, 16
	xor t2, t2, t3
	srli t3, t0, 5
	andi t3, t3, 1
	slli t3, t3, 15
	xor t2, t2, t3
	srli t3, t0, 11
	andi t3, t3, 1
	slli t3, t3, 14
	xor t2, t2, t3
	srli t3, t0, 23
	andi t3, t3, 1
	slli t3, t3, 13
	xor t2, t2, t3
	srli t3, t0, 8
	andi t3, t3, 1
	slli t3, t3, 12
	xor t2, t2, t3
	srli t3, t0, 12
	andi t3, t3, 1
	slli t3, t3, 11
	xor t2, t2, t3
	srli t3, t0, 7
	andi t3, t3, 1
	slli t3, t3, 10
	xor t2, t2, t3
	srli t3, t0, 17
	andi t3, t3, 1
	slli t3, t3, 9
	xor t2, t2, t3
	addi t3, t0, 0
	andi t3, t3, 1
	slli t3, t3, 8
	xor t2, t2, t3
	srli t3, t0, 22
	andi t3, t3, 1
	slli t3, t3, 7
	xor t2, t2, t3
	srli t3, t0, 3
	andi t3, t3, 1
	slli t3, t3, 6
	xor t2, t2, t3
	srli t3, t0, 10
	andi t3, t3, 1
	slli t3, t3, 5
	xor t2, t2, t3
	srli t3, t0, 14
	andi t3, t3, 1
	slli t3, t3, 4
	xor t2, t2, t3
	srli t3, t0, 6
	andi t3, t3, 1
	slli t3, t3, 3
	xor t2, t2, t3
	srli t3, t0, 20
	andi t3, t3, 1
	slli t3, t3, 2
	xor t2, t2, t3
	srli t3, t0, 27
	andi t3, t3, 1
	slli t3, t3, 1
	xor t2, t2, t3
	srli t3, t0, 24
	andi t3, t3, 1
	xor t2, t2, t3
	sb t2, 0(a5)
	srli t1, t2, 8
	sb t1, 1(a5)
	srli t1, t2, 16
	sb t1, 2(a5)
	srli t1, t2, 24
	sb t1, 3(a5)
	srli t1, t2, 32
	sb t1, 4(a5)
	srli t4, t1, 8
	sb t4, 5(a5)
	srli t4, t1, 16
	sb t4, 6(a5)
	srli t4, t1, 24
	sb t4, 7(a5)
	addi a5, a5, 8
	addi a6, a6, 1
	addi t0, a6, -16
	bnez t0, 27b
	addi t0, a1, -16
	beqz t0, 214f
	lbu t0, 16(a0)
	slli t0, t0, 8
	lbu t1, 17(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 18(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 19(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 20(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 21(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 22(a0)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 23(a0)
	or t0, t0, t1
	andi t2, t0, 0
	srli t3, t0, 7
	andi t3, t3, 1
	slli t3, t3, 55
	xor t2, t2, t3
	srli t3, t0, 15
	andi t3, t3, 1
	slli t3, t3, 54
	xor t2, t2, t3
	srli t3, t0, 23
	andi t3, t3, 1
	slli t3, t3, 53
	xor t2, t2, t3
	srli t3, t0, 31
	andi t3, t3, 1
	slli t3, t3, 52
	xor t2, t2, t3
	srli t3, t0, 39
	andi t3, t3, 1
	slli t3, t3, 51
	xor t2, t2, t3
	srli t3, t0, 47
	andi t3, t3, 1
	slli t3, t3, 50
	xor t2, t2, t3
	srli t3, t0, 55
	andi t3, t3, 1
	slli t3, t3, 49
	xor t2, t2, t3
	srli t3, t0, 63
	andi t3, t3, 1
	slli t3, t3, 48
	xor t2, t2, t3
	srli t3, t0, 6
	andi t3, t3, 1
	slli t3, t3, 47
	xor t2, t2, t3
	srli t3, t0, 14
	andi t3, t3, 1
	slli t3, t3, 46
	xor t2, t2, t3
	srli t3, t0, 22
	andi t3, t3, 1
	slli t3, t3, 45
	xor t2, t2, t3
	srli t3, t0, 30
	andi t3, t3, 1
	slli t3, t3, 44
	xor t2, t2, t3
	srli t3, t0, 38
	andi t3, t3, 1
	slli t3, t3, 43
	xor t2, t2, t3
	srli t3, t0, 46
	andi t3, t3, 1
	slli t3, t3, 42
	xor t2, t2, t3
	srli t3, t0, 54
	andi t3, t3, 1
	slli t3, t3, 41
	xor t2, t2, t3
	srli t3, t0, 62
	andi t3, t3, 1
	slli t3, t3, 40
	xor t2, t2, t3
	srli t3, t0, 5
	andi t3, t3, 1
	slli t3, t3, 39
	xor t2, t2, t3
	srli t3, t0, 13
	andi t3, t3, 1
	slli t3, t3, 38
	xor t2, t2, t3
	srli t3, t0, 21
	andi t3, t3, 1
	slli t3, t3, 37
	xor t2, t2, t3
	srli t3, t0, 29
	andi t3, t3, 1
	slli t3, t3, 36
	xor t2, t2, t3
	srli t3, t0, 37
	andi t3, t3, 1
	slli t3, t3, 35
	xor t2, t2, t3
	srli t3, t0, 45
	andi t3, t3, 1
	slli t3, t3, 34
	xor t2, t2, t3
	srli t3, t0, 53
	andi t3, t3, 1
	slli t3, t3, 33
	xor t2, t2, t3
	srli t3, t0, 61
	andi t3, t3, 1
	slli t3, t3, 32
	xor t2, t2, t3
	srli t3, t0, 4
	andi t3, t3, 1
	slli t3, t3, 31
	xor t2, t2, t3
	srli t3, t0, 12
	andi t3, t3, 1
	slli t3, t3, 30
	xor t2, t2, t3
	srli t3, t0, 20
	andi t3, t3, 1
	slli t3, t3, 29
	xor t2, t2, t3
	srli t3, t0, 28
	andi t3, t3, 1
	slli t3, t3, 28
	xor t2, t2, t3
	srli t3, t0, 1
	andi t3, t3, 1
	slli t3, t3, 27
	xor t2, t2, t3
	srli t3, t0, 9
	andi t3, t3, 1
	slli t3, t3, 26
	xor t2, t2, t3
	srli t3, t0, 17
	andi t3, t3, 1
	slli t3, t3, 25
	xor t2, t2, t3
	srli t3, t0, 25
	andi t3, t3, 1
	slli t3, t3, 24
	xor t2, t2, t3
	srli t3, t0, 33
	andi t3, t3, 1
	slli t3, t3, 23
	xor t2, t2, t3
	srli t3, t0, 41
	andi t3, t3, 1
	slli t3, t3, 22
	xor t2, t2, t3
	srli t3, t0, 49
	andi t3, t3, 1
	slli t3, t3, 21
	xor t2, t2, t3
	srli t3, t0, 57
	andi t3, t3, 1
	slli t3, t3, 20
	xor t2, t2, t3
	srli t3, t0, 2
	andi t3, t3, 1
	slli t3, t3, 19
	xor t2, t2, t3
	srli t3, t0, 10
	andi t3, t3, 1
	slli t3, t3, 18
	xor t2, t2, t3
	srli t3, t0, 18
	andi t3, t3, 1
	slli t3, t3, 17
	xor t2, t2, t3
	srli t3, t0, 26
	andi t3, t3, 1
	slli t3, t3, 16
	xor t2, t2, t3
	srli t3, t0, 34
	andi t3, t3, 1
	slli t3, t3, 15
	xor t2, t2, t3
	srli t3, t0, 42
	andi t3, t3, 1
	slli t3, t3, 14
	xor t2, t2, t3
	srli t3, t0, 50
	andi t3, t3, 1
	slli t3, t3, 13
	xor t2, t2, t3
	srli t3, t0, 58
	andi t3, t3, 1
	slli t3, t3, 12
	xor t2, t2, t3
	srli t3, t0, 3
	andi t3, t3, 1
	slli t3, t3, 11
	xor t2, t2, t3
	srli t3, t0, 11
	andi t3, t3, 1
	slli t3, t3, 10
	xor t2, t2, t3
	srli t3, t0, 19
	andi t3, t3, 1
	slli t3, t3, 9
	xor t2, t2, t3
	srli t3, t0, 27
	andi t3, t3, 1
	slli t3, t3, 8
	xor t2, t2, t3
	srli t3, t0, 35
	andi t3, t3, 1
	slli t3, t3, 7
	xor t2, t2, t3
	srli t3, t0, 43
	andi t3, t3, 1
	slli t3, t3, 6
	xor t2, t2, t3
	srli t3, t0, 51
	andi t3, t3, 1
	slli t3, t3, 5
	xor t2, t2, t3
	srli t3, t0, 59
	andi t3, t3, 1
	slli t3, t3, 4
	xor t2, t2, t3
	srli t3, t0, 36
	andi t3, t3, 1
	slli t3, t3, 3
	xor t2, t2, t3
	srli t3, t0, 44
	andi t3, t3, 1
	slli t3, t3, 2
	xor t2, t2, t3
	srli t3, t0, 52
	andi t3, t3, 1
	slli t3, t3, 1
	xor t2, t2, t3
	srli t3, t0, 60
	andi t3, t3, 1
	xor t2, t2, t3
	srli a3, t2, 28
	addi a4, t2, 0
	slli a4, a4, 36
	srli a4, a4, 36
	addi a6, zero, 0
	addi a5, a2, 256
216:
	srli t0, a6, 1
	beqz t0, 217f
	addi t0, a6, -8
	beqz t0, 219f
	addi t0, a6, -15
	beqz t0, 221f
	srli t0, a3, 26
	slli a3, a3, 2
	xor a3, a3, t0
	slli a3, a3, 36
	srli a3, a3, 36
	srli t0, a4, 26
	slli a4, a4, 2
	xor a4, a4, t0
	slli a4, a4, 36
	srli a4, a4, 36
	j 222f
221:
	srli t0, a3, 27
	slli a3, a3, 1
	xor a3, a3, t0
	slli a3, a3, 36
	srli a3, a3, 36
	srli t0, a4, 27
	slli a4, a4, 1
	xor a4, a4, t0
	slli a4, a4, 36
	srli a4, a4, 36
222:
	j 220f
219:
	srli t0, a3, 27
	slli a3, a3, 1
	xor a3, a3, t0
	slli a3, a3, 36
	srli a3, a3, 36
	srli t0, a4, 27
	slli a4, a4, 1
	xor a4, a4, t0
	slli a4, a4, 36
	srli a4, a4, 36
220:
	j 218f
217:
	srli t0, a3, 27
	slli a3, a3, 1
	xor a3, a3, t0
	slli a3, a3, 36
	srli a3, a3, 36
	srli t0, a4, 27
	slli a4, a4, 1
	xor a4, a4, t0
	slli a4, a4, 36
	srli a4, a4, 36
218:
	slli t0, a3, 28
	xor t0, t0, a4
	andi t2, t0, 0
	srli t3, t0, 42
	andi t3, t3, 1
	slli t3, t3, 47
	xor t2, t2, t3
	srli t3, t0, 39
	andi t3, t3, 1
	slli t3, t3, 46
	xor t2, t2, t3
	srli t3, t0, 45
	andi t3, t3, 1
	slli t3, t3, 45
	xor t2, t2, t3
	srli t3, t0, 32
	andi t3, t3, 1
	slli t3, t3, 44
	xor t2, t2, t3
	srli t3, t0, 55
	andi t3, t3, 1
	slli t3, t3, 43
	xor t2, t2, t3
	srli t3, t0, 51
	andi t3, t3, 1
	slli t3, t3, 42
	xor t2, t2, t3
	srli t3, t0, 53
	andi t3, t3, 1
	slli t3, t3, 41
	xor t2, t2, t3
	srli t3, t0, 28
	andi t3, t3, 1
	slli t3, t3, 40
	xor t2, t2, t3
	srli t3, t0, 41
	andi t3, t3, 1
	slli t3, t3, 39
	xor t2, t2, t3
	srli t3, t0, 50
	andi t3, t3, 1
	slli t3, t3, 38
	xor t2, t2, t3
	srli t3, t0, 35
	andi t3, t3, 1
	slli t3, t3, 37
	xor t2, t2, t3
	srli t3, t0, 46
	andi t3, t3, 1
	slli t3, t3, 36
	xor t2, t2, t3
	srli t3, t0, 33
	andi t3, t3, 1
	slli t3, t3, 35
	xor t2, t2, t3
	srli t3, t0, 37
	andi t3, t3, 1
	slli t3, t3, 34
	xor t2, t2, t3
	srli t3, t0, 44
	andi t3, t3, 1
	slli t3, t3, 33
	xor t2, t2, t3
	srli t3, t0, 52
	andi t3, t3, 1
	slli t3, t3, 32
	xor t2, t2, t3
	srli t3, t0, 30
	andi t3, t3, 1
	slli t3, t3, 31
	xor t2, t2, t3
	srli t3, t0, 48
	andi t3, t3, 1
	slli t3, t3, 30
	xor t2, t2, t3
	srli t3, t0, 40
	andi t3, t3, 1
	slli t3, t3, 29
	xor t2, t2, t3
	srli t3, t0, 49
	andi t3, t3, 1
	slli t3, t3, 28
	xor t2, t2, t3
	srli t3, t0, 29
	andi t3, t3, 1
	slli t3, t3, 27
	xor t2, t2, t3
	srli t3, t0, 36
	andi t3, t3, 1
	slli t3, t3, 26
	xor t2, t2, t3
	srli t3, t0, 43
	andi t3, t3, 1
	slli t3, t3, 25
	xor t2, t2, t3
	srli t3, t0, 54
	andi t3, t3, 1
	slli t3, t3, 24
	xor t2, t2, t3
	srli t3, t0, 15
	andi t3, t3, 1
	slli t3, t3, 23
	xor t2, t2, t3
	srli t3, t0, 4
	andi t3, t3, 1
	slli t3, t3, 22
	xor t2, t2, t3
	srli t3, t0, 25
	andi t3, t3, 1
	slli t3, t3, 21
	xor t2, t2, t3
	srli t3, t0, 19
	andi t3, t3, 1
	slli t3, t3, 20
	xor t2, t2, t3
	srli t3, t0, 9
	andi t3, t3, 1
	slli t3, t3, 19
	xor t2, t2, t3
	srli t3, t0, 1
	andi t3, t3, 1
	slli t3, t3, 18
	xor t2, t2, t3
	srli t3, t0, 26
	andi t3, t3, 1
	slli t3, t3, 17
	xor t2, t2, t3
	srli t3, t0, 16
	andi t3, t3, 1
	slli t3, t3, 16
	xor t2, t2, t3
	srli t3, t0, 5
	andi t3, t3, 1
	slli t3, t3, 15
	xor t2, t2, t3
	srli t3, t0, 11
	andi t3, t3, 1
	slli t3, t3, 14
	xor t2, t2, t3
	srli t3, t0, 23
	andi t3, t3, 1
	slli t3, t3, 13
	xor t2, t2, t3
	srli t3, t0, 8
	andi t3, t3, 1
	slli t3, t3, 12
	xor t2, t2, t3
	srli t3, t0, 12
	andi t3, t3, 1
	slli t3, t3, 11
	xor t2, t2, t3
	srli t3, t0, 7
	andi t3, t3, 1
	slli t3, t3, 10
	xor t2, t2, t3
	srli t3, t0, 17
	andi t3, t3, 1
	slli t3, t3, 9
	xor t2, t2, t3
	addi t3, t0, 0
	andi t3, t3, 1
	slli t3, t3, 8
	xor t2, t2, t3
	srli t3, t0, 22
	andi t3, t3, 1
	slli t3, t3, 7
	xor t2, t2, t3
	srli t3, t0, 3
	andi t3, t3, 1
	slli t3, t3, 6
	xor t2, t2, t3
	srli t3, t0, 10
	andi t3, t3, 1
	slli t3, t3, 5
	xor t2, t2, t3
	srli t3, t0, 14
	andi t3, t3, 1
	slli t3, t3, 4
	xor t2, t2, t3
	srli t3, t0, 6
	andi t3, t3, 1
	slli t3, t3, 3
	xor t2, t2, t3
	srli t3, t0, 20
	andi t3, t3, 1
	slli t3, t3, 2
	xor t2, t2, t3
	srli t3, t0, 27
	andi t3, t3, 1
	slli t3, t3, 1
	xor t2, t2, t3
	srli t3, t0, 24
	andi t3, t3, 1
	xor t2, t2, t3
	sb t2, 0(a5)
	srli t1, t2, 8
	sb t1, 1(a5)
	srli t1, t2, 16
	sb t1, 2(a5)
	srli t1, t2, 24
	sb t1, 3(a5)
	srli t1, t2, 32
	sb t1, 4(a5)
	srli t4, t1, 8
	sb t4, 5(a5)
	srli t4, t1, 16
	sb t4, 6(a5)
	srli t4, t1, 24
	sb t4, 7(a5)
	addi a5, a5, 8
	addi a6, a6, 1
	addi t0, a6, -16
	bnez t0, 216b
	j 215f
214:
	addi t0, a2, 0
	addi t1, a2, 256
	addi t2, zero, 128
223:
	lbu t3, 0(t0)
	sb t3, 0(t1)
	addi t0, t0, 1
	addi t1, t1, 1
	addi t2, t2, -1
	bnez t2, 223b
215:
	addi t0, zero, 0
	addi a0, zero, 0
	addi a1, zero, 0
	addi a2, zero, 0
	addi a3, zero, 0
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	addi a7, zero, 0
	addi t0, zero, 0
	addi t1, zero, 0
	addi t2, zero, 0
	addi t3, zero, 0
	addi t4, zero, 0
	addi t5, zero, 0
	addi t6, zero, 0
	ret
	.option pop

vg_triple_des_ecb_encrypt:
	.option push
	.option arch, +m, +c
	beqz a2, 20f
	addi sp, sp, -1056
	addi t0, sp, 0
	sd s1, 944(t0)
	sd s2, 952(t0)
	sd s3, 960(t0)
	sd s4, 968(t0)
	sd s5, 976(t0)
	sd s6, 984(t0)
	sd s7, 992(t0)
	sd s8, 1000(t0)
	sd s9, 1008(t0)
	sd s10, 1016(t0)
	sd s11, 1024(t0)
	sd ra, 1032(t0)
	sd s0, 1040(t0)
	addi s0, t0, 0
	addi t3, s0, 512
	addi t2, a0, 0
	addi t4, zero, 384
22:
	lbu t1, 0(t2)
	sb t1, 0(t3)
	addi t2, t2, 1
	addi t3, t3, 1
	addi t4, t4, -1
	bnez t4, 22b
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 896(s0)
	lui t0, 16
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 904(s0)
	lui t0, 4080
	addiw t0, t0, 255
	slli t0, t0, 32
	lui t1, 4080
	addiw t1, t1, 255
	add t0, t0, t1
	sd t0, 912(s0)
	lui t0, 61681
	addiw t0, t0, -241
	slli t0, t0, 32
	lui t1, 61681
	addiw t1, t1, -241
	add t0, t0, t1
	sd t0, 920(s0)
	lui t0, 209715
	addiw t0, t0, 819
	slli t0, t0, 32
	lui t1, 209715
	addiw t1, t1, 819
	add t0, t0, t1
	sd t0, 928(s0)
	lui t0, 349525
	addiw t0, t0, 1365
	slli t0, t0, 32
	lui t1, 349525
	addiw t1, t1, 1365
	add t0, t0, t1
	sd t0, 936(s0)
23:
	srli t0, a2, 6
	beqz t0, 24f
	addi s5, zero, 512
	j 25f
24:
	slli s5, a2, 3
25:
	addi t2, a1, 0
	addi t3, s0, 0
	addi t4, s5, 0
26:
	lbu t1, 0(t2)
	sb t1, 0(t3)
	addi t2, t2, 1
	addi t3, t3, 1
	addi t4, t4, -1
	bnez t4, 26b
	call {vg_triple_des_transpose}
	addi a3, s0, 512
	call {vg_triple_des_pass_encrypt}
	addi a3, s0, 760
	call {vg_triple_des_pass_decrypt}
	addi a3, s0, 768
	call {vg_triple_des_pass_encrypt}
	call {vg_triple_des_transpose}
	srli t0, a2, 6
	beqz t0, 27f
	addi s5, zero, 512
	j 28f
27:
	slli s5, a2, 3
28:
	addi t2, s0, 0
	addi t3, a1, 0
	addi t4, s5, 0
29:
	lbu t1, 0(t2)
	sb t1, 0(t3)
	addi t2, t2, 1
	addi t3, t3, 1
	addi t4, t4, -1
	bnez t4, 29b
	add a1, a1, s5
	srli t0, s5, 3
	sub a2, a2, t0
	bnez a2, 23b
	addi t1, zero, 0
	addi t0, s0, 0
	addi t4, zero, 118
210:
	sd t1, 0(t0)
	addi t0, t0, 8
	addi t4, t4, -1
	bnez t4, 210b
	ld s1, 944(s0)
	ld s2, 952(s0)
	ld s3, 960(s0)
	ld s4, 968(s0)
	ld s5, 976(s0)
	ld s6, 984(s0)
	ld s7, 992(s0)
	ld s8, 1000(s0)
	ld s9, 1008(s0)
	ld s10, 1016(s0)
	ld s11, 1024(s0)
	ld ra, 1032(s0)
	ld s0, 1040(s0)
	addi sp, sp, 1056
	j 21f
20:
21:
	addi t0, zero, 0
	addi sp, sp, -1056
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	sd t0, 80(t1)
	sd t0, 88(t1)
	sd t0, 96(t1)
	sd t0, 104(t1)
	sd t0, 112(t1)
	sd t0, 120(t1)
	sd t0, 128(t1)
	sd t0, 136(t1)
	sd t0, 144(t1)
	sd t0, 152(t1)
	sd t0, 160(t1)
	sd t0, 168(t1)
	sd t0, 176(t1)
	sd t0, 184(t1)
	sd t0, 192(t1)
	sd t0, 200(t1)
	sd t0, 208(t1)
	sd t0, 216(t1)
	sd t0, 224(t1)
	sd t0, 232(t1)
	sd t0, 240(t1)
	sd t0, 248(t1)
	sd t0, 256(t1)
	sd t0, 264(t1)
	sd t0, 272(t1)
	sd t0, 280(t1)
	sd t0, 288(t1)
	sd t0, 296(t1)
	sd t0, 304(t1)
	sd t0, 312(t1)
	sd t0, 320(t1)
	sd t0, 328(t1)
	sd t0, 336(t1)
	sd t0, 344(t1)
	sd t0, 352(t1)
	sd t0, 360(t1)
	sd t0, 368(t1)
	sd t0, 376(t1)
	sd t0, 384(t1)
	sd t0, 392(t1)
	sd t0, 400(t1)
	sd t0, 408(t1)
	sd t0, 416(t1)
	sd t0, 424(t1)
	sd t0, 432(t1)
	sd t0, 440(t1)
	sd t0, 448(t1)
	sd t0, 456(t1)
	sd t0, 464(t1)
	sd t0, 472(t1)
	sd t0, 480(t1)
	sd t0, 488(t1)
	sd t0, 496(t1)
	sd t0, 504(t1)
	sd t0, 512(t1)
	sd t0, 520(t1)
	sd t0, 528(t1)
	sd t0, 536(t1)
	sd t0, 544(t1)
	sd t0, 552(t1)
	sd t0, 560(t1)
	sd t0, 568(t1)
	sd t0, 576(t1)
	sd t0, 584(t1)
	sd t0, 592(t1)
	sd t0, 600(t1)
	sd t0, 608(t1)
	sd t0, 616(t1)
	sd t0, 624(t1)
	sd t0, 632(t1)
	sd t0, 640(t1)
	sd t0, 648(t1)
	sd t0, 656(t1)
	sd t0, 664(t1)
	sd t0, 672(t1)
	sd t0, 680(t1)
	sd t0, 688(t1)
	sd t0, 696(t1)
	sd t0, 704(t1)
	sd t0, 712(t1)
	sd t0, 720(t1)
	sd t0, 728(t1)
	sd t0, 736(t1)
	sd t0, 744(t1)
	sd t0, 752(t1)
	sd t0, 760(t1)
	sd t0, 768(t1)
	sd t0, 776(t1)
	sd t0, 784(t1)
	sd t0, 792(t1)
	sd t0, 800(t1)
	sd t0, 808(t1)
	sd t0, 816(t1)
	sd t0, 824(t1)
	sd t0, 832(t1)
	sd t0, 840(t1)
	sd t0, 848(t1)
	sd t0, 856(t1)
	sd t0, 864(t1)
	sd t0, 872(t1)
	sd t0, 880(t1)
	sd t0, 888(t1)
	sd t0, 896(t1)
	sd t0, 904(t1)
	sd t0, 912(t1)
	sd t0, 920(t1)
	sd t0, 928(t1)
	sd t0, 936(t1)
	sd t0, 944(t1)
	sd t0, 952(t1)
	sd t0, 960(t1)
	sd t0, 968(t1)
	sd t0, 976(t1)
	sd t0, 984(t1)
	sd t0, 992(t1)
	sd t0, 1000(t1)
	sd t0, 1008(t1)
	sd t0, 1016(t1)
	sd t0, 1024(t1)
	sd t0, 1032(t1)
	sd t0, 1040(t1)
	sd t0, 1048(t1)
	addi sp, sp, 1056
	addi a0, zero, 0
	addi a1, zero, 0
	addi a2, zero, 0
	addi a3, zero, 0
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	addi a7, zero, 0
	addi t0, zero, 0
	addi t1, zero, 0
	addi t2, zero, 0
	addi t3, zero, 0
	addi t4, zero, 0
	addi t5, zero, 0
	addi t6, zero, 0
	ret
	.option pop

vg_triple_des_ecb_decrypt:
	.option push
	.option arch, +m, +c
	beqz a2, 20f
	addi sp, sp, -1056
	addi t0, sp, 0
	sd s1, 944(t0)
	sd s2, 952(t0)
	sd s3, 960(t0)
	sd s4, 968(t0)
	sd s5, 976(t0)
	sd s6, 984(t0)
	sd s7, 992(t0)
	sd s8, 1000(t0)
	sd s9, 1008(t0)
	sd s10, 1016(t0)
	sd s11, 1024(t0)
	sd ra, 1032(t0)
	sd s0, 1040(t0)
	addi s0, t0, 0
	addi t3, s0, 512
	addi t2, a0, 0
	addi t4, zero, 384
22:
	lbu t1, 0(t2)
	sb t1, 0(t3)
	addi t2, t2, 1
	addi t3, t3, 1
	addi t4, t4, -1
	bnez t4, 22b
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 896(s0)
	lui t0, 16
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 904(s0)
	lui t0, 4080
	addiw t0, t0, 255
	slli t0, t0, 32
	lui t1, 4080
	addiw t1, t1, 255
	add t0, t0, t1
	sd t0, 912(s0)
	lui t0, 61681
	addiw t0, t0, -241
	slli t0, t0, 32
	lui t1, 61681
	addiw t1, t1, -241
	add t0, t0, t1
	sd t0, 920(s0)
	lui t0, 209715
	addiw t0, t0, 819
	slli t0, t0, 32
	lui t1, 209715
	addiw t1, t1, 819
	add t0, t0, t1
	sd t0, 928(s0)
	lui t0, 349525
	addiw t0, t0, 1365
	slli t0, t0, 32
	lui t1, 349525
	addiw t1, t1, 1365
	add t0, t0, t1
	sd t0, 936(s0)
23:
	srli t0, a2, 6
	beqz t0, 24f
	addi s5, zero, 512
	j 25f
24:
	slli s5, a2, 3
25:
	addi t2, a1, 0
	addi t3, s0, 0
	addi t4, s5, 0
26:
	lbu t1, 0(t2)
	sb t1, 0(t3)
	addi t2, t2, 1
	addi t3, t3, 1
	addi t4, t4, -1
	bnez t4, 26b
	call {vg_triple_des_transpose}
	addi a3, s0, 888
	call {vg_triple_des_pass_decrypt}
	addi a3, s0, 640
	call {vg_triple_des_pass_encrypt}
	addi a3, s0, 632
	call {vg_triple_des_pass_decrypt}
	call {vg_triple_des_transpose}
	srli t0, a2, 6
	beqz t0, 27f
	addi s5, zero, 512
	j 28f
27:
	slli s5, a2, 3
28:
	addi t2, s0, 0
	addi t3, a1, 0
	addi t4, s5, 0
29:
	lbu t1, 0(t2)
	sb t1, 0(t3)
	addi t2, t2, 1
	addi t3, t3, 1
	addi t4, t4, -1
	bnez t4, 29b
	add a1, a1, s5
	srli t0, s5, 3
	sub a2, a2, t0
	bnez a2, 23b
	addi t1, zero, 0
	addi t0, s0, 0
	addi t4, zero, 118
210:
	sd t1, 0(t0)
	addi t0, t0, 8
	addi t4, t4, -1
	bnez t4, 210b
	ld s1, 944(s0)
	ld s2, 952(s0)
	ld s3, 960(s0)
	ld s4, 968(s0)
	ld s5, 976(s0)
	ld s6, 984(s0)
	ld s7, 992(s0)
	ld s8, 1000(s0)
	ld s9, 1008(s0)
	ld s10, 1016(s0)
	ld s11, 1024(s0)
	ld ra, 1032(s0)
	ld s0, 1040(s0)
	addi sp, sp, 1056
	j 21f
20:
21:
	addi t0, zero, 0
	addi sp, sp, -1056
	addi t1, sp, 0
	sd t0, 0(t1)
	sd t0, 8(t1)
	sd t0, 16(t1)
	sd t0, 24(t1)
	sd t0, 32(t1)
	sd t0, 40(t1)
	sd t0, 48(t1)
	sd t0, 56(t1)
	sd t0, 64(t1)
	sd t0, 72(t1)
	sd t0, 80(t1)
	sd t0, 88(t1)
	sd t0, 96(t1)
	sd t0, 104(t1)
	sd t0, 112(t1)
	sd t0, 120(t1)
	sd t0, 128(t1)
	sd t0, 136(t1)
	sd t0, 144(t1)
	sd t0, 152(t1)
	sd t0, 160(t1)
	sd t0, 168(t1)
	sd t0, 176(t1)
	sd t0, 184(t1)
	sd t0, 192(t1)
	sd t0, 200(t1)
	sd t0, 208(t1)
	sd t0, 216(t1)
	sd t0, 224(t1)
	sd t0, 232(t1)
	sd t0, 240(t1)
	sd t0, 248(t1)
	sd t0, 256(t1)
	sd t0, 264(t1)
	sd t0, 272(t1)
	sd t0, 280(t1)
	sd t0, 288(t1)
	sd t0, 296(t1)
	sd t0, 304(t1)
	sd t0, 312(t1)
	sd t0, 320(t1)
	sd t0, 328(t1)
	sd t0, 336(t1)
	sd t0, 344(t1)
	sd t0, 352(t1)
	sd t0, 360(t1)
	sd t0, 368(t1)
	sd t0, 376(t1)
	sd t0, 384(t1)
	sd t0, 392(t1)
	sd t0, 400(t1)
	sd t0, 408(t1)
	sd t0, 416(t1)
	sd t0, 424(t1)
	sd t0, 432(t1)
	sd t0, 440(t1)
	sd t0, 448(t1)
	sd t0, 456(t1)
	sd t0, 464(t1)
	sd t0, 472(t1)
	sd t0, 480(t1)
	sd t0, 488(t1)
	sd t0, 496(t1)
	sd t0, 504(t1)
	sd t0, 512(t1)
	sd t0, 520(t1)
	sd t0, 528(t1)
	sd t0, 536(t1)
	sd t0, 544(t1)
	sd t0, 552(t1)
	sd t0, 560(t1)
	sd t0, 568(t1)
	sd t0, 576(t1)
	sd t0, 584(t1)
	sd t0, 592(t1)
	sd t0, 600(t1)
	sd t0, 608(t1)
	sd t0, 616(t1)
	sd t0, 624(t1)
	sd t0, 632(t1)
	sd t0, 640(t1)
	sd t0, 648(t1)
	sd t0, 656(t1)
	sd t0, 664(t1)
	sd t0, 672(t1)
	sd t0, 680(t1)
	sd t0, 688(t1)
	sd t0, 696(t1)
	sd t0, 704(t1)
	sd t0, 712(t1)
	sd t0, 720(t1)
	sd t0, 728(t1)
	sd t0, 736(t1)
	sd t0, 744(t1)
	sd t0, 752(t1)
	sd t0, 760(t1)
	sd t0, 768(t1)
	sd t0, 776(t1)
	sd t0, 784(t1)
	sd t0, 792(t1)
	sd t0, 800(t1)
	sd t0, 808(t1)
	sd t0, 816(t1)
	sd t0, 824(t1)
	sd t0, 832(t1)
	sd t0, 840(t1)
	sd t0, 848(t1)
	sd t0, 856(t1)
	sd t0, 864(t1)
	sd t0, 872(t1)
	sd t0, 880(t1)
	sd t0, 888(t1)
	sd t0, 896(t1)
	sd t0, 904(t1)
	sd t0, 912(t1)
	sd t0, 920(t1)
	sd t0, 928(t1)
	sd t0, 936(t1)
	sd t0, 944(t1)
	sd t0, 952(t1)
	sd t0, 960(t1)
	sd t0, 968(t1)
	sd t0, 976(t1)
	sd t0, 984(t1)
	sd t0, 992(t1)
	sd t0, 1000(t1)
	sd t0, 1008(t1)
	sd t0, 1016(t1)
	sd t0, 1024(t1)
	sd t0, 1032(t1)
	sd t0, 1040(t1)
	sd t0, 1048(t1)
	addi sp, sp, 1056
	addi a0, zero, 0
	addi a1, zero, 0
	addi a2, zero, 0
	addi a3, zero, 0
	addi a4, zero, 0
	addi a5, zero, 0
	addi a6, zero, 0
	addi a7, zero, 0
	addi t0, zero, 0
	addi t1, zero, 0
	addi t2, zero, 0
	addi t3, zero, 0
	addi t4, zero, 0
	addi t5, zero, 0
	addi t6, zero, 0
	ret
	.option pop
