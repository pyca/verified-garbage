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
	ret
	.option pop

vg_triple_des_ecb_encrypt:
	.option push
	.option arch, +m, +c
	beqz a2, 20f
	addi sp, sp, -944
	addi t0, sp, 0
	sd s1, 0(t0)
	sd s2, 8(t0)
	sd s3, 16(t0)
	sd s4, 24(t0)
	addi s4, t0, 0
	addi s1, a1, 0
	addi s2, a1, 0
	addi s3, a3, 0
	addi s3, a2, 0
	addi t0, s4, 560
	addi t2, a0, 0
	addi t4, zero, 384
22:
	lbu t1, 0(t2)
	sb t1, 0(t0)
	addi t2, t2, 1
	addi t0, t0, 1
	addi t4, t4, -1
	bnez t4, 22b
23:
	sd s5, 56(s4)
	sd s6, 64(s4)
	sd s7, 72(s4)
	sd s8, 80(s4)
	sd s9, 88(s4)
	sd s10, 96(s4)
	lui t0, 577791
	addiw t0, t0, -1625
	slli t0, t0, 32
	lui t1, 297411
	addiw t1, t1, -1923
	add t0, t0, t1
	sd t0, 120(s4)
	lui t0, 514972
	addiw t0, t0, 1995
	slli t0, t0, 32
	lui t1, 1006958
	addiw t1, t1, 857
	add t0, t0, t1
	sd t0, 128(s4)
	lui t0, 167205
	addiw t0, t0, 62
	slli t0, t0, 32
	lui t1, 548376
	addiw t1, t1, 2018
	add t0, t0, t1
	sd t0, 136(s4)
	lui t0, 949404
	addiw t0, t0, 1990
	slli t0, t0, 32
	lui t1, 650735
	addiw t1, t1, 1965
	add t0, t0, t1
	sd t0, 144(s4)
	lui t0, 912917
	addiw t0, t0, -1333
	slli t0, t0, 32
	lui t1, 151463
	addiw t1, t1, 1048
	add t0, t0, t1
	sd t0, 152(s4)
	lui t0, 613275
	addiw t0, t0, -1339
	slli t0, t0, 32
	lui t1, 511468
	addiw t1, t1, 933
	add t0, t0, t1
	sd t0, 160(s4)
	lui t0, 272347
	addiw t0, t0, -761
	slli t0, t0, 32
	lui t1, 730620
	addiw t1, t1, -703
	add t0, t0, t1
	sd t0, 168(s4)
	lui t0, 369978
	addiw t0, t0, 1843
	slli t0, t0, 32
	lui t1, 358874
	addiw t1, t1, 825
	add t0, t0, t1
	sd t0, 176(s4)
	lui t0, 923080
	addiw t0, t0, 1425
	slli t0, t0, 32
	lui t1, 647834
	addiw t1, t1, -61
	add t0, t0, t1
	sd t0, 184(s4)
	lui t0, 443197
	addiw t0, t0, 1588
	slli t0, t0, 32
	lui t1, 764907
	addiw t1, t1, 2009
	add t0, t0, t1
	sd t0, 192(s4)
	lui t0, 653439
	addiw t0, t0, 995
	slli t0, t0, 32
	lui t1, 497702
	addiw t1, t1, 159
	add t0, t0, t1
	sd t0, 200(s4)
	lui t0, 1042229
	addiw t0, t0, 1965
	slli t0, t0, 32
	lui t1, 687598
	addiw t1, t1, 825
	add t0, t0, t1
	sd t0, 208(s4)
	lui t0, 97124
	addiw t0, t0, -131
	slli t0, t0, 32
	lui t1, 965742
	addiw t1, t1, 446
	add t0, t0, t1
	sd t0, 216(s4)
	lui t0, 234364
	addiw t0, t0, -1364
	slli t0, t0, 32
	lui t1, 443387
	addiw t1, t1, 825
	add t0, t0, t1
	sd t0, 224(s4)
	lui t0, 475776
	addiw t0, t0, 1754
	slli t0, t0, 32
	lui t1, 115598
	addiw t1, t1, -1244
	add t0, t0, t1
	sd t0, 232(s4)
	lui t0, 812632
	addiw t0, t0, -164
	slli t0, t0, 32
	lui t1, 453076
	addiw t1, t1, -267
	add t0, t0, t1
	sd t0, 240(s4)
	lui t0, 997947
	addiw t0, t0, 757
	slli t0, t0, 32
	lui t1, 988933
	addiw t1, t1, 1546
	add t0, t0, t1
	sd t0, 248(s4)
	lui t0, 355759
	addiw t0, t0, 821
	slli t0, t0, 32
	lui t1, 228455
	addiw t1, t1, -1037
	add t0, t0, t1
	sd t0, 256(s4)
	lui t0, 807395
	addiw t0, t0, -446
	slli t0, t0, 32
	lui t1, 221408
	addiw t1, t1, -1732
	add t0, t0, t1
	sd t0, 264(s4)
	lui t0, 773613
	addiw t0, t0, 1622
	slli t0, t0, 32
	lui t1, 814790
	addiw t1, t1, -87
	add t0, t0, t1
	sd t0, 272(s4)
	lui t0, 432450
	addiw t0, t0, -920
	slli t0, t0, 32
	lui t1, 369724
	addiw t1, t1, 934
	add t0, t0, t1
	sd t0, 280(s4)
	lui t0, 350061
	addiw t0, t0, -1478
	slli t0, t0, 32
	lui t1, 349677
	addiw t1, t1, -1691
	add t0, t0, t1
	sd t0, 288(s4)
	lui t0, 773308
	addiw t0, t0, 1973
	slli t0, t0, 32
	lui t1, 457282
	addiw t1, t1, -293
	add t0, t0, t1
	sd t0, 296(s4)
	lui t0, 439792
	addiw t0, t0, -1444
	slli t0, t0, 32
	lui t1, 355758
	addiw t1, t1, 2005
	add t0, t0, t1
	sd t0, 304(s4)
	lui t0, 238487
	addiw t0, t0, -1185
	slli t0, t0, 32
	lui t1, 815585
	addiw t1, t1, -1291
	add t0, t0, t1
	sd t0, 312(s4)
	lui t0, 443229
	addiw t0, t0, 1994
	slli t0, t0, 32
	lui t1, 382958
	addiw t1, t1, -363
	add t0, t0, t1
	sd t0, 320(s4)
	lui t0, 353801
	addiw t0, t0, 1066
	slli t0, t0, 32
	lui t1, 658810
	addiw t1, t1, 1376
	add t0, t0, t1
	sd t0, 328(s4)
	lui t0, 379968
	addiw t0, t0, -172
	slli t0, t0, 32
	lui t1, 933327
	addiw t1, t1, -1477
	add t0, t0, t1
	sd t0, 336(s4)
	lui t0, 656557
	addiw t0, t0, 385
	slli t0, t0, 32
	lui t1, 56148
	addiw t1, t1, -935
	add t0, t0, t1
	sd t0, 344(s4)
	lui t0, 211421
	addiw t0, t0, -342
	slli t0, t0, 32
	lui t1, 443238
	addiw t1, t1, -667
	add t0, t0, t1
	sd t0, 352(s4)
	lui t0, 48984
	addiw t0, t0, -2016
	slli t0, t0, 32
	lui t1, 865972
	addiw t1, t1, 647
	add t0, t0, t1
	sd t0, 360(s4)
	lui t0, 982268
	addiw t0, t0, -1373
	slli t0, t0, 32
	lui t1, 523070
	addiw t1, t1, -411
	add t0, t0, t1
	sd t0, 368(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 64
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 376(s4)
	lui t0, 0
	addiw t0, t0, 4
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 384(s4)
	lui t0, 0
	addiw t0, t0, 1023
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 1023
	add t0, t0, t1
	sd t0, 392(s4)
	lui t0, 64
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 64
	addiw t1, t1, -256
	add t0, t0, t1
	sd t0, 400(s4)
	lui t0, 1008
	addiw t0, t0, 63
	slli t0, t0, 32
	lui t1, 1008
	addiw t1, t1, 63
	add t0, t0, t1
	sd t0, 408(s4)
	lui t0, 16128
	addiw t0, t0, 1008
	slli t0, t0, 32
	lui t1, 16128
	addiw t1, t1, 1008
	add t0, t0, t1
	sd t0, 416(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 4096
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 424(s4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1044480
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 432(s4)
	lui t0, 1
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 1
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 440(s4)
	lui t0, 4095
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 4095
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 448(s4)
	lui t0, 1008
	addiw t0, t0, 63
	slli t0, t0, 32
	lui t1, 1008
	addiw t1, t1, 63
	add t0, t0, t1
	sd t0, 456(s4)
	lui t0, 64513
	addiw t0, t0, -64
	slli t0, t0, 32
	lui t1, 64513
	addiw t1, t1, -64
	add t0, t0, t1
	sd t0, 464(s4)
	lui t0, 4112
	addiw t0, t0, 257
	slli t0, t0, 32
	lui t1, 4112
	addiw t1, t1, 257
	add t0, t0, t1
	sd t0, 472(s4)
	lui t0, 61681
	addiw t0, t0, -241
	slli t0, t0, 32
	lui t1, 61681
	addiw t1, t1, -241
	add t0, t0, t1
	sd t0, 480(s4)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 488(s4)
	lui t0, 16417
	addiw t0, t0, -2048
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 496(s4)
	lui t0, 16
	addiw t0, t0, 8
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 504(s4)
	lui t0, 64
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 32768
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 512(s4)
	lui t0, 0
	addiw t0, t0, 512
	slli t0, t0, 32
	lui t1, 64
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 520(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 16384
	addiw t1, t1, 256
	add t0, t0, t1
	sd t0, 528(s4)
	lui t0, 0
	addiw t0, t0, 4
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 536(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 4096
	addiw t1, t1, 1024
	add t0, t0, t1
	sd t0, 544(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 129
	addiw t1, t1, -2044
	add t0, t0, t1
	sd t0, 552(s4)
	lbu t0, 0(s2)
	slli t0, t0, 8
	lbu t1, 1(s2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 2(s2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 3(s2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 4(s2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 5(s2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 6(s2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 7(s2)
	or t0, t0, t1
	andi t2, t0, 0
	srli t3, t0, 6
	andi t3, t3, 1
	slli t3, t3, 63
	xor t2, t2, t3
	srli t3, t0, 14
	andi t3, t3, 1
	slli t3, t3, 62
	xor t2, t2, t3
	srli t3, t0, 22
	andi t3, t3, 1
	slli t3, t3, 61
	xor t2, t2, t3
	srli t3, t0, 30
	andi t3, t3, 1
	slli t3, t3, 60
	xor t2, t2, t3
	srli t3, t0, 38
	andi t3, t3, 1
	slli t3, t3, 59
	xor t2, t2, t3
	srli t3, t0, 46
	andi t3, t3, 1
	slli t3, t3, 58
	xor t2, t2, t3
	srli t3, t0, 54
	andi t3, t3, 1
	slli t3, t3, 57
	xor t2, t2, t3
	srli t3, t0, 62
	andi t3, t3, 1
	slli t3, t3, 56
	xor t2, t2, t3
	srli t3, t0, 4
	andi t3, t3, 1
	slli t3, t3, 55
	xor t2, t2, t3
	srli t3, t0, 12
	andi t3, t3, 1
	slli t3, t3, 54
	xor t2, t2, t3
	srli t3, t0, 20
	andi t3, t3, 1
	slli t3, t3, 53
	xor t2, t2, t3
	srli t3, t0, 28
	andi t3, t3, 1
	slli t3, t3, 52
	xor t2, t2, t3
	srli t3, t0, 36
	andi t3, t3, 1
	slli t3, t3, 51
	xor t2, t2, t3
	srli t3, t0, 44
	andi t3, t3, 1
	slli t3, t3, 50
	xor t2, t2, t3
	srli t3, t0, 52
	andi t3, t3, 1
	slli t3, t3, 49
	xor t2, t2, t3
	srli t3, t0, 60
	andi t3, t3, 1
	slli t3, t3, 48
	xor t2, t2, t3
	srli t3, t0, 2
	andi t3, t3, 1
	slli t3, t3, 47
	xor t2, t2, t3
	srli t3, t0, 10
	andi t3, t3, 1
	slli t3, t3, 46
	xor t2, t2, t3
	srli t3, t0, 18
	andi t3, t3, 1
	slli t3, t3, 45
	xor t2, t2, t3
	srli t3, t0, 26
	andi t3, t3, 1
	slli t3, t3, 44
	xor t2, t2, t3
	srli t3, t0, 34
	andi t3, t3, 1
	slli t3, t3, 43
	xor t2, t2, t3
	srli t3, t0, 42
	andi t3, t3, 1
	slli t3, t3, 42
	xor t2, t2, t3
	srli t3, t0, 50
	andi t3, t3, 1
	slli t3, t3, 41
	xor t2, t2, t3
	srli t3, t0, 58
	andi t3, t3, 1
	slli t3, t3, 40
	xor t2, t2, t3
	addi t3, t0, 0
	andi t3, t3, 1
	slli t3, t3, 39
	xor t2, t2, t3
	srli t3, t0, 8
	andi t3, t3, 1
	slli t3, t3, 38
	xor t2, t2, t3
	srli t3, t0, 16
	andi t3, t3, 1
	slli t3, t3, 37
	xor t2, t2, t3
	srli t3, t0, 24
	andi t3, t3, 1
	slli t3, t3, 36
	xor t2, t2, t3
	srli t3, t0, 32
	andi t3, t3, 1
	slli t3, t3, 35
	xor t2, t2, t3
	srli t3, t0, 40
	andi t3, t3, 1
	slli t3, t3, 34
	xor t2, t2, t3
	srli t3, t0, 48
	andi t3, t3, 1
	slli t3, t3, 33
	xor t2, t2, t3
	srli t3, t0, 56
	andi t3, t3, 1
	slli t3, t3, 32
	xor t2, t2, t3
	srli t3, t0, 7
	andi t3, t3, 1
	slli t3, t3, 31
	xor t2, t2, t3
	srli t3, t0, 15
	andi t3, t3, 1
	slli t3, t3, 30
	xor t2, t2, t3
	srli t3, t0, 23
	andi t3, t3, 1
	slli t3, t3, 29
	xor t2, t2, t3
	srli t3, t0, 31
	andi t3, t3, 1
	slli t3, t3, 28
	xor t2, t2, t3
	srli t3, t0, 39
	andi t3, t3, 1
	slli t3, t3, 27
	xor t2, t2, t3
	srli t3, t0, 47
	andi t3, t3, 1
	slli t3, t3, 26
	xor t2, t2, t3
	srli t3, t0, 55
	andi t3, t3, 1
	slli t3, t3, 25
	xor t2, t2, t3
	srli t3, t0, 63
	andi t3, t3, 1
	slli t3, t3, 24
	xor t2, t2, t3
	srli t3, t0, 5
	andi t3, t3, 1
	slli t3, t3, 23
	xor t2, t2, t3
	srli t3, t0, 13
	andi t3, t3, 1
	slli t3, t3, 22
	xor t2, t2, t3
	srli t3, t0, 21
	andi t3, t3, 1
	slli t3, t3, 21
	xor t2, t2, t3
	srli t3, t0, 29
	andi t3, t3, 1
	slli t3, t3, 20
	xor t2, t2, t3
	srli t3, t0, 37
	andi t3, t3, 1
	slli t3, t3, 19
	xor t2, t2, t3
	srli t3, t0, 45
	andi t3, t3, 1
	slli t3, t3, 18
	xor t2, t2, t3
	srli t3, t0, 53
	andi t3, t3, 1
	slli t3, t3, 17
	xor t2, t2, t3
	srli t3, t0, 61
	andi t3, t3, 1
	slli t3, t3, 16
	xor t2, t2, t3
	srli t3, t0, 3
	andi t3, t3, 1
	slli t3, t3, 15
	xor t2, t2, t3
	srli t3, t0, 11
	andi t3, t3, 1
	slli t3, t3, 14
	xor t2, t2, t3
	srli t3, t0, 19
	andi t3, t3, 1
	slli t3, t3, 13
	xor t2, t2, t3
	srli t3, t0, 27
	andi t3, t3, 1
	slli t3, t3, 12
	xor t2, t2, t3
	srli t3, t0, 35
	andi t3, t3, 1
	slli t3, t3, 11
	xor t2, t2, t3
	srli t3, t0, 43
	andi t3, t3, 1
	slli t3, t3, 10
	xor t2, t2, t3
	srli t3, t0, 51
	andi t3, t3, 1
	slli t3, t3, 9
	xor t2, t2, t3
	srli t3, t0, 59
	andi t3, t3, 1
	slli t3, t3, 8
	xor t2, t2, t3
	srli t3, t0, 1
	andi t3, t3, 1
	slli t3, t3, 7
	xor t2, t2, t3
	srli t3, t0, 9
	andi t3, t3, 1
	slli t3, t3, 6
	xor t2, t2, t3
	srli t3, t0, 17
	andi t3, t3, 1
	slli t3, t3, 5
	xor t2, t2, t3
	srli t3, t0, 25
	andi t3, t3, 1
	slli t3, t3, 4
	xor t2, t2, t3
	srli t3, t0, 33
	andi t3, t3, 1
	slli t3, t3, 3
	xor t2, t2, t3
	srli t3, t0, 41
	andi t3, t3, 1
	slli t3, t3, 2
	xor t2, t2, t3
	srli t3, t0, 49
	andi t3, t3, 1
	slli t3, t3, 1
	xor t2, t2, t3
	srli t3, t0, 57
	andi t3, t3, 1
	xor t2, t2, t3
	srli a1, t2, 32
	slli a2, t2, 32
	srli a2, a2, 32
	addi a6, zero, 3
24:
	addi t6, a6, -3
	beqz t6, 25f
	addi t6, a6, -2
	beqz t6, 27f
	addi a3, s4, 816
	addi a4, zero, 16
	addi a5, zero, 8
	j 28f
27:
	addi a3, s4, 808
	addi a4, zero, 16
	addi a5, zero, -8
28:
	j 26f
25:
	addi a3, s4, 560
	addi a4, zero, 16
	addi a5, zero, 8
26:
29:
	ld t4, 0(a3)
	ld t0, 488(s4)
	and t0, a2, t0
	slli t1, t0, 1
	srli t2, t0, 31
	xor t1, t1, t2
	slli t2, t0, 33
	xor t0, t1, t2
	ld t1, 376(s4)
	and t1, t0, t1
	ld t2, 384(s4)
	and t2, t0, t2
	slli t2, t2, 16
	xor t0, t1, t2
	ld t1, 392(s4)
	and t1, t0, t1
	ld t2, 400(s4)
	and t2, t0, t2
	slli t2, t2, 8
	xor t0, t1, t2
	ld t1, 408(s4)
	and t1, t0, t1
	ld t2, 416(s4)
	and t2, t0, t2
	slli t2, t2, 4
	xor t0, t1, t2
	ld t1, 424(s4)
	and t1, t4, t1
	ld t2, 432(s4)
	and t2, t4, t2
	slli t2, t2, 8
	xor t4, t1, t2
	ld t1, 440(s4)
	and t1, t4, t1
	ld t2, 448(s4)
	and t2, t4, t2
	slli t2, t2, 4
	xor t4, t1, t2
	ld t1, 456(s4)
	and t1, t4, t1
	ld t2, 464(s4)
	and t2, t4, t2
	slli t2, t2, 2
	xor t4, t1, t2
	xor t0, t0, t4
	ld t3, 472(s4)
	and s5, t0, t3
	slli t1, s5, 1
	xor s5, s5, t1
	slli t1, s5, 2
	xor s5, s5, t1
	slli t1, s5, 4
	xor s5, s5, t1
	srli s6, t0, 1
	and s6, s6, t3
	slli t1, s6, 1
	xor s6, s6, t1
	slli t1, s6, 2
	xor s6, s6, t1
	slli t1, s6, 4
	xor s6, s6, t1
	srli s7, t0, 2
	and s7, s7, t3
	slli t1, s7, 1
	xor s7, s7, t1
	slli t1, s7, 2
	xor s7, s7, t1
	slli t1, s7, 4
	xor s7, s7, t1
	srli s8, t0, 3
	and s8, s8, t3
	slli t1, s8, 1
	xor s8, s8, t1
	slli t1, s8, 2
	xor s8, s8, t1
	slli t1, s8, 4
	xor s8, s8, t1
	srli s9, t0, 4
	and s9, s9, t3
	slli t1, s9, 1
	xor s9, s9, t1
	slli t1, s9, 2
	xor s9, s9, t1
	slli t1, s9, 4
	xor s9, s9, t1
	srli s10, t0, 5
	and s10, s10, t3
	slli t1, s10, 1
	xor s10, s10, t1
	slli t1, s10, 2
	xor s10, s10, t1
	slli t1, s10, 4
	xor s10, s10, t1
	ld t0, 120(s4)
	ld t1, 128(s4)
	and t1, t1, s5
	xor t0, t0, t1
	ld t1, 136(s4)
	ld t2, 144(s4)
	and t2, t2, s5
	xor t1, t1, t2
	xor t1, t0, t1
	and t1, t1, s6
	xor t0, t0, t1
	ld t1, 152(s4)
	ld t2, 160(s4)
	and t2, t2, s5
	xor t1, t1, t2
	ld t2, 168(s4)
	ld t3, 176(s4)
	and t3, t3, s5
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s6
	xor t1, t1, t2
	xor t1, t0, t1
	and t1, t1, s7
	xor t0, t0, t1
	ld t1, 184(s4)
	ld t2, 192(s4)
	and t2, t2, s5
	xor t1, t1, t2
	ld t2, 200(s4)
	ld t3, 208(s4)
	and t3, t3, s5
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s6
	xor t1, t1, t2
	ld t2, 216(s4)
	ld t3, 224(s4)
	and t3, t3, s5
	xor t2, t2, t3
	ld t3, 232(s4)
	ld t4, 240(s4)
	and t4, t4, s5
	xor t3, t3, t4
	xor t3, t2, t3
	and t3, t3, s6
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s7
	xor t1, t1, t2
	xor t1, t0, t1
	and t1, t1, s8
	xor t0, t0, t1
	ld t1, 248(s4)
	ld t2, 256(s4)
	and t2, t2, s5
	xor t1, t1, t2
	ld t2, 264(s4)
	ld t3, 272(s4)
	and t3, t3, s5
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s6
	xor t1, t1, t2
	ld t2, 280(s4)
	ld t3, 288(s4)
	and t3, t3, s5
	xor t2, t2, t3
	ld t3, 296(s4)
	ld t4, 304(s4)
	and t4, t4, s5
	xor t3, t3, t4
	xor t3, t2, t3
	and t3, t3, s6
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s7
	xor t1, t1, t2
	ld t2, 312(s4)
	ld t3, 320(s4)
	and t3, t3, s5
	xor t2, t2, t3
	ld t3, 328(s4)
	ld t4, 336(s4)
	and t4, t4, s5
	xor t3, t3, t4
	xor t3, t2, t3
	and t3, t3, s6
	xor t2, t2, t3
	ld t3, 344(s4)
	ld t4, 352(s4)
	and t4, t4, s5
	xor t3, t3, t4
	ld t4, 360(s4)
	ld t5, 368(s4)
	and t5, t5, s5
	xor t4, t4, t5
	xor t4, t3, t4
	and t4, t4, s6
	xor t3, t3, t4
	xor t3, t2, t3
	and t3, t3, s7
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s8
	xor t1, t1, t2
	xor t1, t0, t1
	and t1, t1, s9
	xor t0, t0, t1
	ld t6, 480(s4)
	xor t6, s10, t6
	and t0, t0, t6
	srli t1, t0, 4
	xor t0, t0, t1
	srli t1, t0, 57
	andi t1, t1, 1
	slli t1, t1, 1
	xor a1, a1, t1
	srli t1, t0, 51
	andi t1, t1, 33
	slli t1, t1, 4
	xor a1, a1, t1
	srli t1, t0, 59
	andi t1, t1, 1
	slli t1, t1, 15
	xor a1, a1, t1
	srli t1, t0, 40
	andi t1, t1, 1
	slli t1, t1, 2
	xor a1, a1, t1
	ld t1, 496(s4)
	and t1, t1, t0
	srli t1, t1, 35
	xor a1, a1, t1
	ld t1, 504(s4)
	and t1, t1, t0
	srli t1, t1, 29
	xor a1, a1, t1
	srli t1, t0, 42
	andi t1, t1, 1
	slli t1, t1, 16
	xor a1, a1, t1
	ld t1, 512(s4)
	and t1, t1, t0
	srli t1, t1, 20
	xor a1, a1, t1
	ld t1, 520(s4)
	and t1, t1, t0
	srli t1, t1, 15
	xor a1, a1, t1
	srli t1, t0, 33
	andi t1, t1, 1
	slli t1, t1, 22
	xor a1, a1, t1
	ld t1, 528(s4)
	and t1, t1, t0
	srli t1, t1, 8
	xor a1, a1, t1
	ld t1, 536(s4)
	and t1, t1, t0
	srli t1, t1, 3
	xor a1, a1, t1
	ld t1, 544(s4)
	and t1, t1, t0
	xor a1, a1, t1
	srli t1, t0, 17
	andi t1, t1, 257
	slli t1, t1, 21
	xor a1, a1, t1
	andi t1, t0, 1
	slli t1, t1, 5
	xor a1, a1, t1
	ld t1, 552(s4)
	and t1, t1, t0
	slli t1, t1, 9
	xor a1, a1, t1
	srli t1, t0, 1
	andi t1, t1, 257
	slli t1, t1, 17
	xor a1, a1, t1
	srli t1, t0, 3
	andi t1, t1, 1
	slli t1, t1, 27
	xor a1, a1, t1
	addi t0, a1, 0
	addi a1, a2, 0
	addi a2, t0, 0
	add a3, a3, a5
	addi a4, a4, -1
	bnez a4, 29b
	addi t0, a1, 0
	addi a1, a2, 0
	addi a2, t0, 0
	addi a6, a6, -1
	bnez a6, 24b
	slli t0, a1, 32
	xor t0, t0, a2
	andi t2, t0, 0
	srli t3, t0, 24
	andi t3, t3, 1
	slli t3, t3, 63
	xor t2, t2, t3
	srli t3, t0, 56
	andi t3, t3, 1
	slli t3, t3, 62
	xor t2, t2, t3
	srli t3, t0, 16
	andi t3, t3, 1
	slli t3, t3, 61
	xor t2, t2, t3
	srli t3, t0, 48
	andi t3, t3, 1
	slli t3, t3, 60
	xor t2, t2, t3
	srli t3, t0, 8
	andi t3, t3, 1
	slli t3, t3, 59
	xor t2, t2, t3
	srli t3, t0, 40
	andi t3, t3, 1
	slli t3, t3, 58
	xor t2, t2, t3
	addi t3, t0, 0
	andi t3, t3, 1
	slli t3, t3, 57
	xor t2, t2, t3
	srli t3, t0, 32
	andi t3, t3, 1
	slli t3, t3, 56
	xor t2, t2, t3
	srli t3, t0, 25
	andi t3, t3, 1
	slli t3, t3, 55
	xor t2, t2, t3
	srli t3, t0, 57
	andi t3, t3, 1
	slli t3, t3, 54
	xor t2, t2, t3
	srli t3, t0, 17
	andi t3, t3, 1
	slli t3, t3, 53
	xor t2, t2, t3
	srli t3, t0, 49
	andi t3, t3, 1
	slli t3, t3, 52
	xor t2, t2, t3
	srli t3, t0, 9
	andi t3, t3, 1
	slli t3, t3, 51
	xor t2, t2, t3
	srli t3, t0, 41
	andi t3, t3, 1
	slli t3, t3, 50
	xor t2, t2, t3
	srli t3, t0, 1
	andi t3, t3, 1
	slli t3, t3, 49
	xor t2, t2, t3
	srli t3, t0, 33
	andi t3, t3, 1
	slli t3, t3, 48
	xor t2, t2, t3
	srli t3, t0, 26
	andi t3, t3, 1
	slli t3, t3, 47
	xor t2, t2, t3
	srli t3, t0, 58
	andi t3, t3, 1
	slli t3, t3, 46
	xor t2, t2, t3
	srli t3, t0, 18
	andi t3, t3, 1
	slli t3, t3, 45
	xor t2, t2, t3
	srli t3, t0, 50
	andi t3, t3, 1
	slli t3, t3, 44
	xor t2, t2, t3
	srli t3, t0, 10
	andi t3, t3, 1
	slli t3, t3, 43
	xor t2, t2, t3
	srli t3, t0, 42
	andi t3, t3, 1
	slli t3, t3, 42
	xor t2, t2, t3
	srli t3, t0, 2
	andi t3, t3, 1
	slli t3, t3, 41
	xor t2, t2, t3
	srli t3, t0, 34
	andi t3, t3, 1
	slli t3, t3, 40
	xor t2, t2, t3
	srli t3, t0, 27
	andi t3, t3, 1
	slli t3, t3, 39
	xor t2, t2, t3
	srli t3, t0, 59
	andi t3, t3, 1
	slli t3, t3, 38
	xor t2, t2, t3
	srli t3, t0, 19
	andi t3, t3, 1
	slli t3, t3, 37
	xor t2, t2, t3
	srli t3, t0, 51
	andi t3, t3, 1
	slli t3, t3, 36
	xor t2, t2, t3
	srli t3, t0, 11
	andi t3, t3, 1
	slli t3, t3, 35
	xor t2, t2, t3
	srli t3, t0, 43
	andi t3, t3, 1
	slli t3, t3, 34
	xor t2, t2, t3
	srli t3, t0, 3
	andi t3, t3, 1
	slli t3, t3, 33
	xor t2, t2, t3
	srli t3, t0, 35
	andi t3, t3, 1
	slli t3, t3, 32
	xor t2, t2, t3
	srli t3, t0, 28
	andi t3, t3, 1
	slli t3, t3, 31
	xor t2, t2, t3
	srli t3, t0, 60
	andi t3, t3, 1
	slli t3, t3, 30
	xor t2, t2, t3
	srli t3, t0, 20
	andi t3, t3, 1
	slli t3, t3, 29
	xor t2, t2, t3
	srli t3, t0, 52
	andi t3, t3, 1
	slli t3, t3, 28
	xor t2, t2, t3
	srli t3, t0, 12
	andi t3, t3, 1
	slli t3, t3, 27
	xor t2, t2, t3
	srli t3, t0, 44
	andi t3, t3, 1
	slli t3, t3, 26
	xor t2, t2, t3
	srli t3, t0, 4
	andi t3, t3, 1
	slli t3, t3, 25
	xor t2, t2, t3
	srli t3, t0, 36
	andi t3, t3, 1
	slli t3, t3, 24
	xor t2, t2, t3
	srli t3, t0, 29
	andi t3, t3, 1
	slli t3, t3, 23
	xor t2, t2, t3
	srli t3, t0, 61
	andi t3, t3, 1
	slli t3, t3, 22
	xor t2, t2, t3
	srli t3, t0, 21
	andi t3, t3, 1
	slli t3, t3, 21
	xor t2, t2, t3
	srli t3, t0, 53
	andi t3, t3, 1
	slli t3, t3, 20
	xor t2, t2, t3
	srli t3, t0, 13
	andi t3, t3, 1
	slli t3, t3, 19
	xor t2, t2, t3
	srli t3, t0, 45
	andi t3, t3, 1
	slli t3, t3, 18
	xor t2, t2, t3
	srli t3, t0, 5
	andi t3, t3, 1
	slli t3, t3, 17
	xor t2, t2, t3
	srli t3, t0, 37
	andi t3, t3, 1
	slli t3, t3, 16
	xor t2, t2, t3
	srli t3, t0, 30
	andi t3, t3, 1
	slli t3, t3, 15
	xor t2, t2, t3
	srli t3, t0, 62
	andi t3, t3, 1
	slli t3, t3, 14
	xor t2, t2, t3
	srli t3, t0, 22
	andi t3, t3, 1
	slli t3, t3, 13
	xor t2, t2, t3
	srli t3, t0, 54
	andi t3, t3, 1
	slli t3, t3, 12
	xor t2, t2, t3
	srli t3, t0, 14
	andi t3, t3, 1
	slli t3, t3, 11
	xor t2, t2, t3
	srli t3, t0, 46
	andi t3, t3, 1
	slli t3, t3, 10
	xor t2, t2, t3
	srli t3, t0, 6
	andi t3, t3, 1
	slli t3, t3, 9
	xor t2, t2, t3
	srli t3, t0, 38
	andi t3, t3, 1
	slli t3, t3, 8
	xor t2, t2, t3
	srli t3, t0, 31
	andi t3, t3, 1
	slli t3, t3, 7
	xor t2, t2, t3
	srli t3, t0, 63
	andi t3, t3, 1
	slli t3, t3, 6
	xor t2, t2, t3
	srli t3, t0, 23
	andi t3, t3, 1
	slli t3, t3, 5
	xor t2, t2, t3
	srli t3, t0, 55
	andi t3, t3, 1
	slli t3, t3, 4
	xor t2, t2, t3
	srli t3, t0, 15
	andi t3, t3, 1
	slli t3, t3, 3
	xor t2, t2, t3
	srli t3, t0, 47
	andi t3, t3, 1
	slli t3, t3, 2
	xor t2, t2, t3
	srli t3, t0, 7
	andi t3, t3, 1
	slli t3, t3, 1
	xor t2, t2, t3
	srli t3, t0, 39
	andi t3, t3, 1
	xor t2, t2, t3
	srli t1, t2, 56
	sb t1, 0(s2)
	srli t1, t2, 48
	sb t1, 1(s2)
	srli t1, t2, 40
	sb t1, 2(s2)
	srli t1, t2, 32
	sb t1, 3(s2)
	srli t1, t2, 24
	sb t1, 4(s2)
	srli t1, t2, 16
	sb t1, 5(s2)
	srli t1, t2, 8
	sb t1, 6(s2)
	srli t1, t2, 0
	sb t1, 7(s2)
	ld s5, 56(s4)
	ld s6, 64(s4)
	ld s7, 72(s4)
	ld s8, 80(s4)
	ld s9, 88(s4)
	ld s10, 96(s4)
	addi s2, s2, 8
	addi s3, s3, -1
	bnez s3, 23b
	addi t3, s4, 0
	ld s1, 0(t3)
	ld s2, 8(t3)
	ld s3, 16(t3)
	ld s4, 24(t3)
	addi t0, zero, 0
	addi t1, t3, 0
	addi t2, zero, 118
210:
	sd t0, 0(t1)
	addi t1, t1, 8
	addi t2, t2, -1
	bnez t2, 210b
	addi sp, sp, 944
	j 21f
20:
21:
	ret
	.option pop

vg_triple_des_ecb_decrypt:
	.option push
	.option arch, +m, +c
	beqz a2, 20f
	addi sp, sp, -944
	addi t0, sp, 0
	sd s1, 0(t0)
	sd s2, 8(t0)
	sd s3, 16(t0)
	sd s4, 24(t0)
	addi s4, t0, 0
	addi s1, a1, 0
	addi s2, a1, 0
	addi s3, a3, 0
	addi s3, a2, 0
	addi t0, s4, 560
	addi t2, a0, 0
	addi t4, zero, 384
22:
	lbu t1, 0(t2)
	sb t1, 0(t0)
	addi t2, t2, 1
	addi t0, t0, 1
	addi t4, t4, -1
	bnez t4, 22b
23:
	sd s5, 56(s4)
	sd s6, 64(s4)
	sd s7, 72(s4)
	sd s8, 80(s4)
	sd s9, 88(s4)
	sd s10, 96(s4)
	lui t0, 577791
	addiw t0, t0, -1625
	slli t0, t0, 32
	lui t1, 297411
	addiw t1, t1, -1923
	add t0, t0, t1
	sd t0, 120(s4)
	lui t0, 514972
	addiw t0, t0, 1995
	slli t0, t0, 32
	lui t1, 1006958
	addiw t1, t1, 857
	add t0, t0, t1
	sd t0, 128(s4)
	lui t0, 167205
	addiw t0, t0, 62
	slli t0, t0, 32
	lui t1, 548376
	addiw t1, t1, 2018
	add t0, t0, t1
	sd t0, 136(s4)
	lui t0, 949404
	addiw t0, t0, 1990
	slli t0, t0, 32
	lui t1, 650735
	addiw t1, t1, 1965
	add t0, t0, t1
	sd t0, 144(s4)
	lui t0, 912917
	addiw t0, t0, -1333
	slli t0, t0, 32
	lui t1, 151463
	addiw t1, t1, 1048
	add t0, t0, t1
	sd t0, 152(s4)
	lui t0, 613275
	addiw t0, t0, -1339
	slli t0, t0, 32
	lui t1, 511468
	addiw t1, t1, 933
	add t0, t0, t1
	sd t0, 160(s4)
	lui t0, 272347
	addiw t0, t0, -761
	slli t0, t0, 32
	lui t1, 730620
	addiw t1, t1, -703
	add t0, t0, t1
	sd t0, 168(s4)
	lui t0, 369978
	addiw t0, t0, 1843
	slli t0, t0, 32
	lui t1, 358874
	addiw t1, t1, 825
	add t0, t0, t1
	sd t0, 176(s4)
	lui t0, 923080
	addiw t0, t0, 1425
	slli t0, t0, 32
	lui t1, 647834
	addiw t1, t1, -61
	add t0, t0, t1
	sd t0, 184(s4)
	lui t0, 443197
	addiw t0, t0, 1588
	slli t0, t0, 32
	lui t1, 764907
	addiw t1, t1, 2009
	add t0, t0, t1
	sd t0, 192(s4)
	lui t0, 653439
	addiw t0, t0, 995
	slli t0, t0, 32
	lui t1, 497702
	addiw t1, t1, 159
	add t0, t0, t1
	sd t0, 200(s4)
	lui t0, 1042229
	addiw t0, t0, 1965
	slli t0, t0, 32
	lui t1, 687598
	addiw t1, t1, 825
	add t0, t0, t1
	sd t0, 208(s4)
	lui t0, 97124
	addiw t0, t0, -131
	slli t0, t0, 32
	lui t1, 965742
	addiw t1, t1, 446
	add t0, t0, t1
	sd t0, 216(s4)
	lui t0, 234364
	addiw t0, t0, -1364
	slli t0, t0, 32
	lui t1, 443387
	addiw t1, t1, 825
	add t0, t0, t1
	sd t0, 224(s4)
	lui t0, 475776
	addiw t0, t0, 1754
	slli t0, t0, 32
	lui t1, 115598
	addiw t1, t1, -1244
	add t0, t0, t1
	sd t0, 232(s4)
	lui t0, 812632
	addiw t0, t0, -164
	slli t0, t0, 32
	lui t1, 453076
	addiw t1, t1, -267
	add t0, t0, t1
	sd t0, 240(s4)
	lui t0, 997947
	addiw t0, t0, 757
	slli t0, t0, 32
	lui t1, 988933
	addiw t1, t1, 1546
	add t0, t0, t1
	sd t0, 248(s4)
	lui t0, 355759
	addiw t0, t0, 821
	slli t0, t0, 32
	lui t1, 228455
	addiw t1, t1, -1037
	add t0, t0, t1
	sd t0, 256(s4)
	lui t0, 807395
	addiw t0, t0, -446
	slli t0, t0, 32
	lui t1, 221408
	addiw t1, t1, -1732
	add t0, t0, t1
	sd t0, 264(s4)
	lui t0, 773613
	addiw t0, t0, 1622
	slli t0, t0, 32
	lui t1, 814790
	addiw t1, t1, -87
	add t0, t0, t1
	sd t0, 272(s4)
	lui t0, 432450
	addiw t0, t0, -920
	slli t0, t0, 32
	lui t1, 369724
	addiw t1, t1, 934
	add t0, t0, t1
	sd t0, 280(s4)
	lui t0, 350061
	addiw t0, t0, -1478
	slli t0, t0, 32
	lui t1, 349677
	addiw t1, t1, -1691
	add t0, t0, t1
	sd t0, 288(s4)
	lui t0, 773308
	addiw t0, t0, 1973
	slli t0, t0, 32
	lui t1, 457282
	addiw t1, t1, -293
	add t0, t0, t1
	sd t0, 296(s4)
	lui t0, 439792
	addiw t0, t0, -1444
	slli t0, t0, 32
	lui t1, 355758
	addiw t1, t1, 2005
	add t0, t0, t1
	sd t0, 304(s4)
	lui t0, 238487
	addiw t0, t0, -1185
	slli t0, t0, 32
	lui t1, 815585
	addiw t1, t1, -1291
	add t0, t0, t1
	sd t0, 312(s4)
	lui t0, 443229
	addiw t0, t0, 1994
	slli t0, t0, 32
	lui t1, 382958
	addiw t1, t1, -363
	add t0, t0, t1
	sd t0, 320(s4)
	lui t0, 353801
	addiw t0, t0, 1066
	slli t0, t0, 32
	lui t1, 658810
	addiw t1, t1, 1376
	add t0, t0, t1
	sd t0, 328(s4)
	lui t0, 379968
	addiw t0, t0, -172
	slli t0, t0, 32
	lui t1, 933327
	addiw t1, t1, -1477
	add t0, t0, t1
	sd t0, 336(s4)
	lui t0, 656557
	addiw t0, t0, 385
	slli t0, t0, 32
	lui t1, 56148
	addiw t1, t1, -935
	add t0, t0, t1
	sd t0, 344(s4)
	lui t0, 211421
	addiw t0, t0, -342
	slli t0, t0, 32
	lui t1, 443238
	addiw t1, t1, -667
	add t0, t0, t1
	sd t0, 352(s4)
	lui t0, 48984
	addiw t0, t0, -2016
	slli t0, t0, 32
	lui t1, 865972
	addiw t1, t1, 647
	add t0, t0, t1
	sd t0, 360(s4)
	lui t0, 982268
	addiw t0, t0, -1373
	slli t0, t0, 32
	lui t1, 523070
	addiw t1, t1, -411
	add t0, t0, t1
	sd t0, 368(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 64
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 376(s4)
	lui t0, 0
	addiw t0, t0, 4
	slli t0, t0, 32
	lui t1, 1048560
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 384(s4)
	lui t0, 0
	addiw t0, t0, 1023
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 1023
	add t0, t0, t1
	sd t0, 392(s4)
	lui t0, 64
	addiw t0, t0, -256
	slli t0, t0, 32
	lui t1, 64
	addiw t1, t1, -256
	add t0, t0, t1
	sd t0, 400(s4)
	lui t0, 1008
	addiw t0, t0, 63
	slli t0, t0, 32
	lui t1, 1008
	addiw t1, t1, 63
	add t0, t0, t1
	sd t0, 408(s4)
	lui t0, 16128
	addiw t0, t0, 1008
	slli t0, t0, 32
	lui t1, 16128
	addiw t1, t1, 1008
	add t0, t0, t1
	sd t0, 416(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 4096
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 424(s4)
	lui t0, 16
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 1044480
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 432(s4)
	lui t0, 1
	addiw t0, t0, -1
	slli t0, t0, 32
	lui t1, 1
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 440(s4)
	lui t0, 4095
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 4095
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 448(s4)
	lui t0, 1008
	addiw t0, t0, 63
	slli t0, t0, 32
	lui t1, 1008
	addiw t1, t1, 63
	add t0, t0, t1
	sd t0, 456(s4)
	lui t0, 64513
	addiw t0, t0, -64
	slli t0, t0, 32
	lui t1, 64513
	addiw t1, t1, -64
	add t0, t0, t1
	sd t0, 464(s4)
	lui t0, 4112
	addiw t0, t0, 257
	slli t0, t0, 32
	lui t1, 4112
	addiw t1, t1, 257
	add t0, t0, t1
	sd t0, 472(s4)
	lui t0, 61681
	addiw t0, t0, -241
	slli t0, t0, 32
	lui t1, 61681
	addiw t1, t1, -241
	add t0, t0, t1
	sd t0, 480(s4)
	lui t0, 0
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, -1
	add t0, t0, t1
	sd t0, 488(s4)
	lui t0, 16417
	addiw t0, t0, -2048
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 496(s4)
	lui t0, 16
	addiw t0, t0, 8
	slli t0, t0, 32
	lui t1, 0
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 504(s4)
	lui t0, 64
	addiw t0, t0, 1
	slli t0, t0, 32
	lui t1, 32768
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 512(s4)
	lui t0, 0
	addiw t0, t0, 512
	slli t0, t0, 32
	lui t1, 64
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 520(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 16384
	addiw t1, t1, 256
	add t0, t0, t1
	sd t0, 528(s4)
	lui t0, 0
	addiw t0, t0, 4
	slli t0, t0, 32
	lui t1, 16
	addiw t1, t1, 0
	add t0, t0, t1
	sd t0, 536(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 4096
	addiw t1, t1, 1024
	add t0, t0, t1
	sd t0, 544(s4)
	lui t0, 0
	addiw t0, t0, 0
	slli t0, t0, 32
	lui t1, 129
	addiw t1, t1, -2044
	add t0, t0, t1
	sd t0, 552(s4)
	lbu t0, 0(s2)
	slli t0, t0, 8
	lbu t1, 1(s2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 2(s2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 3(s2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 4(s2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 5(s2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 6(s2)
	or t0, t0, t1
	slli t0, t0, 8
	lbu t1, 7(s2)
	or t0, t0, t1
	andi t2, t0, 0
	srli t3, t0, 6
	andi t3, t3, 1
	slli t3, t3, 63
	xor t2, t2, t3
	srli t3, t0, 14
	andi t3, t3, 1
	slli t3, t3, 62
	xor t2, t2, t3
	srli t3, t0, 22
	andi t3, t3, 1
	slli t3, t3, 61
	xor t2, t2, t3
	srli t3, t0, 30
	andi t3, t3, 1
	slli t3, t3, 60
	xor t2, t2, t3
	srli t3, t0, 38
	andi t3, t3, 1
	slli t3, t3, 59
	xor t2, t2, t3
	srli t3, t0, 46
	andi t3, t3, 1
	slli t3, t3, 58
	xor t2, t2, t3
	srli t3, t0, 54
	andi t3, t3, 1
	slli t3, t3, 57
	xor t2, t2, t3
	srli t3, t0, 62
	andi t3, t3, 1
	slli t3, t3, 56
	xor t2, t2, t3
	srli t3, t0, 4
	andi t3, t3, 1
	slli t3, t3, 55
	xor t2, t2, t3
	srli t3, t0, 12
	andi t3, t3, 1
	slli t3, t3, 54
	xor t2, t2, t3
	srli t3, t0, 20
	andi t3, t3, 1
	slli t3, t3, 53
	xor t2, t2, t3
	srli t3, t0, 28
	andi t3, t3, 1
	slli t3, t3, 52
	xor t2, t2, t3
	srli t3, t0, 36
	andi t3, t3, 1
	slli t3, t3, 51
	xor t2, t2, t3
	srli t3, t0, 44
	andi t3, t3, 1
	slli t3, t3, 50
	xor t2, t2, t3
	srli t3, t0, 52
	andi t3, t3, 1
	slli t3, t3, 49
	xor t2, t2, t3
	srli t3, t0, 60
	andi t3, t3, 1
	slli t3, t3, 48
	xor t2, t2, t3
	srli t3, t0, 2
	andi t3, t3, 1
	slli t3, t3, 47
	xor t2, t2, t3
	srli t3, t0, 10
	andi t3, t3, 1
	slli t3, t3, 46
	xor t2, t2, t3
	srli t3, t0, 18
	andi t3, t3, 1
	slli t3, t3, 45
	xor t2, t2, t3
	srli t3, t0, 26
	andi t3, t3, 1
	slli t3, t3, 44
	xor t2, t2, t3
	srli t3, t0, 34
	andi t3, t3, 1
	slli t3, t3, 43
	xor t2, t2, t3
	srli t3, t0, 42
	andi t3, t3, 1
	slli t3, t3, 42
	xor t2, t2, t3
	srli t3, t0, 50
	andi t3, t3, 1
	slli t3, t3, 41
	xor t2, t2, t3
	srli t3, t0, 58
	andi t3, t3, 1
	slli t3, t3, 40
	xor t2, t2, t3
	addi t3, t0, 0
	andi t3, t3, 1
	slli t3, t3, 39
	xor t2, t2, t3
	srli t3, t0, 8
	andi t3, t3, 1
	slli t3, t3, 38
	xor t2, t2, t3
	srli t3, t0, 16
	andi t3, t3, 1
	slli t3, t3, 37
	xor t2, t2, t3
	srli t3, t0, 24
	andi t3, t3, 1
	slli t3, t3, 36
	xor t2, t2, t3
	srli t3, t0, 32
	andi t3, t3, 1
	slli t3, t3, 35
	xor t2, t2, t3
	srli t3, t0, 40
	andi t3, t3, 1
	slli t3, t3, 34
	xor t2, t2, t3
	srli t3, t0, 48
	andi t3, t3, 1
	slli t3, t3, 33
	xor t2, t2, t3
	srli t3, t0, 56
	andi t3, t3, 1
	slli t3, t3, 32
	xor t2, t2, t3
	srli t3, t0, 7
	andi t3, t3, 1
	slli t3, t3, 31
	xor t2, t2, t3
	srli t3, t0, 15
	andi t3, t3, 1
	slli t3, t3, 30
	xor t2, t2, t3
	srli t3, t0, 23
	andi t3, t3, 1
	slli t3, t3, 29
	xor t2, t2, t3
	srli t3, t0, 31
	andi t3, t3, 1
	slli t3, t3, 28
	xor t2, t2, t3
	srli t3, t0, 39
	andi t3, t3, 1
	slli t3, t3, 27
	xor t2, t2, t3
	srli t3, t0, 47
	andi t3, t3, 1
	slli t3, t3, 26
	xor t2, t2, t3
	srli t3, t0, 55
	andi t3, t3, 1
	slli t3, t3, 25
	xor t2, t2, t3
	srli t3, t0, 63
	andi t3, t3, 1
	slli t3, t3, 24
	xor t2, t2, t3
	srli t3, t0, 5
	andi t3, t3, 1
	slli t3, t3, 23
	xor t2, t2, t3
	srli t3, t0, 13
	andi t3, t3, 1
	slli t3, t3, 22
	xor t2, t2, t3
	srli t3, t0, 21
	andi t3, t3, 1
	slli t3, t3, 21
	xor t2, t2, t3
	srli t3, t0, 29
	andi t3, t3, 1
	slli t3, t3, 20
	xor t2, t2, t3
	srli t3, t0, 37
	andi t3, t3, 1
	slli t3, t3, 19
	xor t2, t2, t3
	srli t3, t0, 45
	andi t3, t3, 1
	slli t3, t3, 18
	xor t2, t2, t3
	srli t3, t0, 53
	andi t3, t3, 1
	slli t3, t3, 17
	xor t2, t2, t3
	srli t3, t0, 61
	andi t3, t3, 1
	slli t3, t3, 16
	xor t2, t2, t3
	srli t3, t0, 3
	andi t3, t3, 1
	slli t3, t3, 15
	xor t2, t2, t3
	srli t3, t0, 11
	andi t3, t3, 1
	slli t3, t3, 14
	xor t2, t2, t3
	srli t3, t0, 19
	andi t3, t3, 1
	slli t3, t3, 13
	xor t2, t2, t3
	srli t3, t0, 27
	andi t3, t3, 1
	slli t3, t3, 12
	xor t2, t2, t3
	srli t3, t0, 35
	andi t3, t3, 1
	slli t3, t3, 11
	xor t2, t2, t3
	srli t3, t0, 43
	andi t3, t3, 1
	slli t3, t3, 10
	xor t2, t2, t3
	srli t3, t0, 51
	andi t3, t3, 1
	slli t3, t3, 9
	xor t2, t2, t3
	srli t3, t0, 59
	andi t3, t3, 1
	slli t3, t3, 8
	xor t2, t2, t3
	srli t3, t0, 1
	andi t3, t3, 1
	slli t3, t3, 7
	xor t2, t2, t3
	srli t3, t0, 9
	andi t3, t3, 1
	slli t3, t3, 6
	xor t2, t2, t3
	srli t3, t0, 17
	andi t3, t3, 1
	slli t3, t3, 5
	xor t2, t2, t3
	srli t3, t0, 25
	andi t3, t3, 1
	slli t3, t3, 4
	xor t2, t2, t3
	srli t3, t0, 33
	andi t3, t3, 1
	slli t3, t3, 3
	xor t2, t2, t3
	srli t3, t0, 41
	andi t3, t3, 1
	slli t3, t3, 2
	xor t2, t2, t3
	srli t3, t0, 49
	andi t3, t3, 1
	slli t3, t3, 1
	xor t2, t2, t3
	srli t3, t0, 57
	andi t3, t3, 1
	xor t2, t2, t3
	srli a1, t2, 32
	slli a2, t2, 32
	srli a2, a2, 32
	addi a6, zero, 3
24:
	addi t6, a6, -3
	beqz t6, 25f
	addi t6, a6, -2
	beqz t6, 27f
	addi a3, s4, 680
	addi a4, zero, 16
	addi a5, zero, -8
	j 28f
27:
	addi a3, s4, 688
	addi a4, zero, 16
	addi a5, zero, 8
28:
	j 26f
25:
	addi a3, s4, 936
	addi a4, zero, 16
	addi a5, zero, -8
26:
29:
	ld t4, 0(a3)
	ld t0, 488(s4)
	and t0, a2, t0
	slli t1, t0, 1
	srli t2, t0, 31
	xor t1, t1, t2
	slli t2, t0, 33
	xor t0, t1, t2
	ld t1, 376(s4)
	and t1, t0, t1
	ld t2, 384(s4)
	and t2, t0, t2
	slli t2, t2, 16
	xor t0, t1, t2
	ld t1, 392(s4)
	and t1, t0, t1
	ld t2, 400(s4)
	and t2, t0, t2
	slli t2, t2, 8
	xor t0, t1, t2
	ld t1, 408(s4)
	and t1, t0, t1
	ld t2, 416(s4)
	and t2, t0, t2
	slli t2, t2, 4
	xor t0, t1, t2
	ld t1, 424(s4)
	and t1, t4, t1
	ld t2, 432(s4)
	and t2, t4, t2
	slli t2, t2, 8
	xor t4, t1, t2
	ld t1, 440(s4)
	and t1, t4, t1
	ld t2, 448(s4)
	and t2, t4, t2
	slli t2, t2, 4
	xor t4, t1, t2
	ld t1, 456(s4)
	and t1, t4, t1
	ld t2, 464(s4)
	and t2, t4, t2
	slli t2, t2, 2
	xor t4, t1, t2
	xor t0, t0, t4
	ld t3, 472(s4)
	and s5, t0, t3
	slli t1, s5, 1
	xor s5, s5, t1
	slli t1, s5, 2
	xor s5, s5, t1
	slli t1, s5, 4
	xor s5, s5, t1
	srli s6, t0, 1
	and s6, s6, t3
	slli t1, s6, 1
	xor s6, s6, t1
	slli t1, s6, 2
	xor s6, s6, t1
	slli t1, s6, 4
	xor s6, s6, t1
	srli s7, t0, 2
	and s7, s7, t3
	slli t1, s7, 1
	xor s7, s7, t1
	slli t1, s7, 2
	xor s7, s7, t1
	slli t1, s7, 4
	xor s7, s7, t1
	srli s8, t0, 3
	and s8, s8, t3
	slli t1, s8, 1
	xor s8, s8, t1
	slli t1, s8, 2
	xor s8, s8, t1
	slli t1, s8, 4
	xor s8, s8, t1
	srli s9, t0, 4
	and s9, s9, t3
	slli t1, s9, 1
	xor s9, s9, t1
	slli t1, s9, 2
	xor s9, s9, t1
	slli t1, s9, 4
	xor s9, s9, t1
	srli s10, t0, 5
	and s10, s10, t3
	slli t1, s10, 1
	xor s10, s10, t1
	slli t1, s10, 2
	xor s10, s10, t1
	slli t1, s10, 4
	xor s10, s10, t1
	ld t0, 120(s4)
	ld t1, 128(s4)
	and t1, t1, s5
	xor t0, t0, t1
	ld t1, 136(s4)
	ld t2, 144(s4)
	and t2, t2, s5
	xor t1, t1, t2
	xor t1, t0, t1
	and t1, t1, s6
	xor t0, t0, t1
	ld t1, 152(s4)
	ld t2, 160(s4)
	and t2, t2, s5
	xor t1, t1, t2
	ld t2, 168(s4)
	ld t3, 176(s4)
	and t3, t3, s5
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s6
	xor t1, t1, t2
	xor t1, t0, t1
	and t1, t1, s7
	xor t0, t0, t1
	ld t1, 184(s4)
	ld t2, 192(s4)
	and t2, t2, s5
	xor t1, t1, t2
	ld t2, 200(s4)
	ld t3, 208(s4)
	and t3, t3, s5
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s6
	xor t1, t1, t2
	ld t2, 216(s4)
	ld t3, 224(s4)
	and t3, t3, s5
	xor t2, t2, t3
	ld t3, 232(s4)
	ld t4, 240(s4)
	and t4, t4, s5
	xor t3, t3, t4
	xor t3, t2, t3
	and t3, t3, s6
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s7
	xor t1, t1, t2
	xor t1, t0, t1
	and t1, t1, s8
	xor t0, t0, t1
	ld t1, 248(s4)
	ld t2, 256(s4)
	and t2, t2, s5
	xor t1, t1, t2
	ld t2, 264(s4)
	ld t3, 272(s4)
	and t3, t3, s5
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s6
	xor t1, t1, t2
	ld t2, 280(s4)
	ld t3, 288(s4)
	and t3, t3, s5
	xor t2, t2, t3
	ld t3, 296(s4)
	ld t4, 304(s4)
	and t4, t4, s5
	xor t3, t3, t4
	xor t3, t2, t3
	and t3, t3, s6
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s7
	xor t1, t1, t2
	ld t2, 312(s4)
	ld t3, 320(s4)
	and t3, t3, s5
	xor t2, t2, t3
	ld t3, 328(s4)
	ld t4, 336(s4)
	and t4, t4, s5
	xor t3, t3, t4
	xor t3, t2, t3
	and t3, t3, s6
	xor t2, t2, t3
	ld t3, 344(s4)
	ld t4, 352(s4)
	and t4, t4, s5
	xor t3, t3, t4
	ld t4, 360(s4)
	ld t5, 368(s4)
	and t5, t5, s5
	xor t4, t4, t5
	xor t4, t3, t4
	and t4, t4, s6
	xor t3, t3, t4
	xor t3, t2, t3
	and t3, t3, s7
	xor t2, t2, t3
	xor t2, t1, t2
	and t2, t2, s8
	xor t1, t1, t2
	xor t1, t0, t1
	and t1, t1, s9
	xor t0, t0, t1
	ld t6, 480(s4)
	xor t6, s10, t6
	and t0, t0, t6
	srli t1, t0, 4
	xor t0, t0, t1
	srli t1, t0, 57
	andi t1, t1, 1
	slli t1, t1, 1
	xor a1, a1, t1
	srli t1, t0, 51
	andi t1, t1, 33
	slli t1, t1, 4
	xor a1, a1, t1
	srli t1, t0, 59
	andi t1, t1, 1
	slli t1, t1, 15
	xor a1, a1, t1
	srli t1, t0, 40
	andi t1, t1, 1
	slli t1, t1, 2
	xor a1, a1, t1
	ld t1, 496(s4)
	and t1, t1, t0
	srli t1, t1, 35
	xor a1, a1, t1
	ld t1, 504(s4)
	and t1, t1, t0
	srli t1, t1, 29
	xor a1, a1, t1
	srli t1, t0, 42
	andi t1, t1, 1
	slli t1, t1, 16
	xor a1, a1, t1
	ld t1, 512(s4)
	and t1, t1, t0
	srli t1, t1, 20
	xor a1, a1, t1
	ld t1, 520(s4)
	and t1, t1, t0
	srli t1, t1, 15
	xor a1, a1, t1
	srli t1, t0, 33
	andi t1, t1, 1
	slli t1, t1, 22
	xor a1, a1, t1
	ld t1, 528(s4)
	and t1, t1, t0
	srli t1, t1, 8
	xor a1, a1, t1
	ld t1, 536(s4)
	and t1, t1, t0
	srli t1, t1, 3
	xor a1, a1, t1
	ld t1, 544(s4)
	and t1, t1, t0
	xor a1, a1, t1
	srli t1, t0, 17
	andi t1, t1, 257
	slli t1, t1, 21
	xor a1, a1, t1
	andi t1, t0, 1
	slli t1, t1, 5
	xor a1, a1, t1
	ld t1, 552(s4)
	and t1, t1, t0
	slli t1, t1, 9
	xor a1, a1, t1
	srli t1, t0, 1
	andi t1, t1, 257
	slli t1, t1, 17
	xor a1, a1, t1
	srli t1, t0, 3
	andi t1, t1, 1
	slli t1, t1, 27
	xor a1, a1, t1
	addi t0, a1, 0
	addi a1, a2, 0
	addi a2, t0, 0
	add a3, a3, a5
	addi a4, a4, -1
	bnez a4, 29b
	addi t0, a1, 0
	addi a1, a2, 0
	addi a2, t0, 0
	addi a6, a6, -1
	bnez a6, 24b
	slli t0, a1, 32
	xor t0, t0, a2
	andi t2, t0, 0
	srli t3, t0, 24
	andi t3, t3, 1
	slli t3, t3, 63
	xor t2, t2, t3
	srli t3, t0, 56
	andi t3, t3, 1
	slli t3, t3, 62
	xor t2, t2, t3
	srli t3, t0, 16
	andi t3, t3, 1
	slli t3, t3, 61
	xor t2, t2, t3
	srli t3, t0, 48
	andi t3, t3, 1
	slli t3, t3, 60
	xor t2, t2, t3
	srli t3, t0, 8
	andi t3, t3, 1
	slli t3, t3, 59
	xor t2, t2, t3
	srli t3, t0, 40
	andi t3, t3, 1
	slli t3, t3, 58
	xor t2, t2, t3
	addi t3, t0, 0
	andi t3, t3, 1
	slli t3, t3, 57
	xor t2, t2, t3
	srli t3, t0, 32
	andi t3, t3, 1
	slli t3, t3, 56
	xor t2, t2, t3
	srli t3, t0, 25
	andi t3, t3, 1
	slli t3, t3, 55
	xor t2, t2, t3
	srli t3, t0, 57
	andi t3, t3, 1
	slli t3, t3, 54
	xor t2, t2, t3
	srli t3, t0, 17
	andi t3, t3, 1
	slli t3, t3, 53
	xor t2, t2, t3
	srli t3, t0, 49
	andi t3, t3, 1
	slli t3, t3, 52
	xor t2, t2, t3
	srli t3, t0, 9
	andi t3, t3, 1
	slli t3, t3, 51
	xor t2, t2, t3
	srli t3, t0, 41
	andi t3, t3, 1
	slli t3, t3, 50
	xor t2, t2, t3
	srli t3, t0, 1
	andi t3, t3, 1
	slli t3, t3, 49
	xor t2, t2, t3
	srli t3, t0, 33
	andi t3, t3, 1
	slli t3, t3, 48
	xor t2, t2, t3
	srli t3, t0, 26
	andi t3, t3, 1
	slli t3, t3, 47
	xor t2, t2, t3
	srli t3, t0, 58
	andi t3, t3, 1
	slli t3, t3, 46
	xor t2, t2, t3
	srli t3, t0, 18
	andi t3, t3, 1
	slli t3, t3, 45
	xor t2, t2, t3
	srli t3, t0, 50
	andi t3, t3, 1
	slli t3, t3, 44
	xor t2, t2, t3
	srli t3, t0, 10
	andi t3, t3, 1
	slli t3, t3, 43
	xor t2, t2, t3
	srli t3, t0, 42
	andi t3, t3, 1
	slli t3, t3, 42
	xor t2, t2, t3
	srli t3, t0, 2
	andi t3, t3, 1
	slli t3, t3, 41
	xor t2, t2, t3
	srli t3, t0, 34
	andi t3, t3, 1
	slli t3, t3, 40
	xor t2, t2, t3
	srli t3, t0, 27
	andi t3, t3, 1
	slli t3, t3, 39
	xor t2, t2, t3
	srli t3, t0, 59
	andi t3, t3, 1
	slli t3, t3, 38
	xor t2, t2, t3
	srli t3, t0, 19
	andi t3, t3, 1
	slli t3, t3, 37
	xor t2, t2, t3
	srli t3, t0, 51
	andi t3, t3, 1
	slli t3, t3, 36
	xor t2, t2, t3
	srli t3, t0, 11
	andi t3, t3, 1
	slli t3, t3, 35
	xor t2, t2, t3
	srli t3, t0, 43
	andi t3, t3, 1
	slli t3, t3, 34
	xor t2, t2, t3
	srli t3, t0, 3
	andi t3, t3, 1
	slli t3, t3, 33
	xor t2, t2, t3
	srli t3, t0, 35
	andi t3, t3, 1
	slli t3, t3, 32
	xor t2, t2, t3
	srli t3, t0, 28
	andi t3, t3, 1
	slli t3, t3, 31
	xor t2, t2, t3
	srli t3, t0, 60
	andi t3, t3, 1
	slli t3, t3, 30
	xor t2, t2, t3
	srli t3, t0, 20
	andi t3, t3, 1
	slli t3, t3, 29
	xor t2, t2, t3
	srli t3, t0, 52
	andi t3, t3, 1
	slli t3, t3, 28
	xor t2, t2, t3
	srli t3, t0, 12
	andi t3, t3, 1
	slli t3, t3, 27
	xor t2, t2, t3
	srli t3, t0, 44
	andi t3, t3, 1
	slli t3, t3, 26
	xor t2, t2, t3
	srli t3, t0, 4
	andi t3, t3, 1
	slli t3, t3, 25
	xor t2, t2, t3
	srli t3, t0, 36
	andi t3, t3, 1
	slli t3, t3, 24
	xor t2, t2, t3
	srli t3, t0, 29
	andi t3, t3, 1
	slli t3, t3, 23
	xor t2, t2, t3
	srli t3, t0, 61
	andi t3, t3, 1
	slli t3, t3, 22
	xor t2, t2, t3
	srli t3, t0, 21
	andi t3, t3, 1
	slli t3, t3, 21
	xor t2, t2, t3
	srli t3, t0, 53
	andi t3, t3, 1
	slli t3, t3, 20
	xor t2, t2, t3
	srli t3, t0, 13
	andi t3, t3, 1
	slli t3, t3, 19
	xor t2, t2, t3
	srli t3, t0, 45
	andi t3, t3, 1
	slli t3, t3, 18
	xor t2, t2, t3
	srli t3, t0, 5
	andi t3, t3, 1
	slli t3, t3, 17
	xor t2, t2, t3
	srli t3, t0, 37
	andi t3, t3, 1
	slli t3, t3, 16
	xor t2, t2, t3
	srli t3, t0, 30
	andi t3, t3, 1
	slli t3, t3, 15
	xor t2, t2, t3
	srli t3, t0, 62
	andi t3, t3, 1
	slli t3, t3, 14
	xor t2, t2, t3
	srli t3, t0, 22
	andi t3, t3, 1
	slli t3, t3, 13
	xor t2, t2, t3
	srli t3, t0, 54
	andi t3, t3, 1
	slli t3, t3, 12
	xor t2, t2, t3
	srli t3, t0, 14
	andi t3, t3, 1
	slli t3, t3, 11
	xor t2, t2, t3
	srli t3, t0, 46
	andi t3, t3, 1
	slli t3, t3, 10
	xor t2, t2, t3
	srli t3, t0, 6
	andi t3, t3, 1
	slli t3, t3, 9
	xor t2, t2, t3
	srli t3, t0, 38
	andi t3, t3, 1
	slli t3, t3, 8
	xor t2, t2, t3
	srli t3, t0, 31
	andi t3, t3, 1
	slli t3, t3, 7
	xor t2, t2, t3
	srli t3, t0, 63
	andi t3, t3, 1
	slli t3, t3, 6
	xor t2, t2, t3
	srli t3, t0, 23
	andi t3, t3, 1
	slli t3, t3, 5
	xor t2, t2, t3
	srli t3, t0, 55
	andi t3, t3, 1
	slli t3, t3, 4
	xor t2, t2, t3
	srli t3, t0, 15
	andi t3, t3, 1
	slli t3, t3, 3
	xor t2, t2, t3
	srli t3, t0, 47
	andi t3, t3, 1
	slli t3, t3, 2
	xor t2, t2, t3
	srli t3, t0, 7
	andi t3, t3, 1
	slli t3, t3, 1
	xor t2, t2, t3
	srli t3, t0, 39
	andi t3, t3, 1
	xor t2, t2, t3
	srli t1, t2, 56
	sb t1, 0(s2)
	srli t1, t2, 48
	sb t1, 1(s2)
	srli t1, t2, 40
	sb t1, 2(s2)
	srli t1, t2, 32
	sb t1, 3(s2)
	srli t1, t2, 24
	sb t1, 4(s2)
	srli t1, t2, 16
	sb t1, 5(s2)
	srli t1, t2, 8
	sb t1, 6(s2)
	srli t1, t2, 0
	sb t1, 7(s2)
	ld s5, 56(s4)
	ld s6, 64(s4)
	ld s7, 72(s4)
	ld s8, 80(s4)
	ld s9, 88(s4)
	ld s10, 96(s4)
	addi s2, s2, 8
	addi s3, s3, -1
	bnez s3, 23b
	addi t3, s4, 0
	ld s1, 0(t3)
	ld s2, 8(t3)
	ld s3, 16(t3)
	ld s4, 24(t3)
	addi t0, zero, 0
	addi t1, t3, 0
	addi t2, zero, 118
210:
	sd t0, 0(t1)
	addi t1, t1, 8
	addi t2, t2, -1
	bnez t2, 210b
	addi sp, sp, 944
	j 21f
20:
21:
	ret
	.option pop
