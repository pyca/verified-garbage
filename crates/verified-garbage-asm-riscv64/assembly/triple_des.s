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
	addi a0, s0, 896
	ld s1, 0(a0)
	ld s2, 8(a0)
	ld s3, 16(a0)
	ld t0, 0(s0)
	ld t1, 64(s0)
	ld t2, 128(s0)
	ld t3, 192(s0)
	ld t4, 256(s0)
	ld t5, 320(s0)
	ld t6, 384(s0)
	ld a7, 448(s0)
	srli s4, t0, 32
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 32
	xor t0, t0, s4
	srli s4, t1, 32
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 32
	xor t1, t1, s4
	srli s4, t2, 32
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 32
	xor t2, t2, s4
	srli s4, t3, 32
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 32
	xor t3, t3, s4
	srli s4, t0, 16
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 16
	xor t0, t0, s4
	srli s4, t1, 16
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 16
	xor t1, t1, s4
	srli s4, t4, 16
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 16
	xor t4, t4, s4
	srli s4, t5, 16
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 16
	xor t5, t5, s4
	srli s4, t0, 8
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 8
	xor t0, t0, s4
	srli s4, t2, 8
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 8
	xor t2, t2, s4
	srli s4, t4, 8
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 8
	xor t4, t4, s4
	srli s4, t6, 8
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 8
	xor t6, t6, s4
	sd t0, 0(s0)
	sd t1, 64(s0)
	sd t2, 128(s0)
	sd t3, 192(s0)
	sd t4, 256(s0)
	sd t5, 320(s0)
	sd t6, 384(s0)
	sd a7, 448(s0)
	ld t0, 8(s0)
	ld t1, 72(s0)
	ld t2, 136(s0)
	ld t3, 200(s0)
	ld t4, 264(s0)
	ld t5, 328(s0)
	ld t6, 392(s0)
	ld a7, 456(s0)
	srli s4, t0, 32
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 32
	xor t0, t0, s4
	srli s4, t1, 32
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 32
	xor t1, t1, s4
	srli s4, t2, 32
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 32
	xor t2, t2, s4
	srli s4, t3, 32
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 32
	xor t3, t3, s4
	srli s4, t0, 16
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 16
	xor t0, t0, s4
	srli s4, t1, 16
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 16
	xor t1, t1, s4
	srli s4, t4, 16
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 16
	xor t4, t4, s4
	srli s4, t5, 16
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 16
	xor t5, t5, s4
	srli s4, t0, 8
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 8
	xor t0, t0, s4
	srli s4, t2, 8
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 8
	xor t2, t2, s4
	srli s4, t4, 8
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 8
	xor t4, t4, s4
	srli s4, t6, 8
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 8
	xor t6, t6, s4
	sd t0, 8(s0)
	sd t1, 72(s0)
	sd t2, 136(s0)
	sd t3, 200(s0)
	sd t4, 264(s0)
	sd t5, 328(s0)
	sd t6, 392(s0)
	sd a7, 456(s0)
	ld t0, 16(s0)
	ld t1, 80(s0)
	ld t2, 144(s0)
	ld t3, 208(s0)
	ld t4, 272(s0)
	ld t5, 336(s0)
	ld t6, 400(s0)
	ld a7, 464(s0)
	srli s4, t0, 32
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 32
	xor t0, t0, s4
	srli s4, t1, 32
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 32
	xor t1, t1, s4
	srli s4, t2, 32
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 32
	xor t2, t2, s4
	srli s4, t3, 32
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 32
	xor t3, t3, s4
	srli s4, t0, 16
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 16
	xor t0, t0, s4
	srli s4, t1, 16
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 16
	xor t1, t1, s4
	srli s4, t4, 16
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 16
	xor t4, t4, s4
	srli s4, t5, 16
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 16
	xor t5, t5, s4
	srli s4, t0, 8
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 8
	xor t0, t0, s4
	srli s4, t2, 8
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 8
	xor t2, t2, s4
	srli s4, t4, 8
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 8
	xor t4, t4, s4
	srli s4, t6, 8
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 8
	xor t6, t6, s4
	sd t0, 16(s0)
	sd t1, 80(s0)
	sd t2, 144(s0)
	sd t3, 208(s0)
	sd t4, 272(s0)
	sd t5, 336(s0)
	sd t6, 400(s0)
	sd a7, 464(s0)
	ld t0, 24(s0)
	ld t1, 88(s0)
	ld t2, 152(s0)
	ld t3, 216(s0)
	ld t4, 280(s0)
	ld t5, 344(s0)
	ld t6, 408(s0)
	ld a7, 472(s0)
	srli s4, t0, 32
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 32
	xor t0, t0, s4
	srli s4, t1, 32
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 32
	xor t1, t1, s4
	srli s4, t2, 32
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 32
	xor t2, t2, s4
	srli s4, t3, 32
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 32
	xor t3, t3, s4
	srli s4, t0, 16
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 16
	xor t0, t0, s4
	srli s4, t1, 16
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 16
	xor t1, t1, s4
	srli s4, t4, 16
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 16
	xor t4, t4, s4
	srli s4, t5, 16
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 16
	xor t5, t5, s4
	srli s4, t0, 8
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 8
	xor t0, t0, s4
	srli s4, t2, 8
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 8
	xor t2, t2, s4
	srli s4, t4, 8
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 8
	xor t4, t4, s4
	srli s4, t6, 8
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 8
	xor t6, t6, s4
	sd t0, 24(s0)
	sd t1, 88(s0)
	sd t2, 152(s0)
	sd t3, 216(s0)
	sd t4, 280(s0)
	sd t5, 344(s0)
	sd t6, 408(s0)
	sd a7, 472(s0)
	ld t0, 32(s0)
	ld t1, 96(s0)
	ld t2, 160(s0)
	ld t3, 224(s0)
	ld t4, 288(s0)
	ld t5, 352(s0)
	ld t6, 416(s0)
	ld a7, 480(s0)
	srli s4, t0, 32
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 32
	xor t0, t0, s4
	srli s4, t1, 32
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 32
	xor t1, t1, s4
	srli s4, t2, 32
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 32
	xor t2, t2, s4
	srli s4, t3, 32
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 32
	xor t3, t3, s4
	srli s4, t0, 16
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 16
	xor t0, t0, s4
	srli s4, t1, 16
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 16
	xor t1, t1, s4
	srli s4, t4, 16
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 16
	xor t4, t4, s4
	srli s4, t5, 16
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 16
	xor t5, t5, s4
	srli s4, t0, 8
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 8
	xor t0, t0, s4
	srli s4, t2, 8
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 8
	xor t2, t2, s4
	srli s4, t4, 8
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 8
	xor t4, t4, s4
	srli s4, t6, 8
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 8
	xor t6, t6, s4
	sd t0, 32(s0)
	sd t1, 96(s0)
	sd t2, 160(s0)
	sd t3, 224(s0)
	sd t4, 288(s0)
	sd t5, 352(s0)
	sd t6, 416(s0)
	sd a7, 480(s0)
	ld t0, 40(s0)
	ld t1, 104(s0)
	ld t2, 168(s0)
	ld t3, 232(s0)
	ld t4, 296(s0)
	ld t5, 360(s0)
	ld t6, 424(s0)
	ld a7, 488(s0)
	srli s4, t0, 32
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 32
	xor t0, t0, s4
	srli s4, t1, 32
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 32
	xor t1, t1, s4
	srli s4, t2, 32
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 32
	xor t2, t2, s4
	srli s4, t3, 32
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 32
	xor t3, t3, s4
	srli s4, t0, 16
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 16
	xor t0, t0, s4
	srli s4, t1, 16
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 16
	xor t1, t1, s4
	srli s4, t4, 16
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 16
	xor t4, t4, s4
	srli s4, t5, 16
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 16
	xor t5, t5, s4
	srli s4, t0, 8
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 8
	xor t0, t0, s4
	srli s4, t2, 8
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 8
	xor t2, t2, s4
	srli s4, t4, 8
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 8
	xor t4, t4, s4
	srli s4, t6, 8
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 8
	xor t6, t6, s4
	sd t0, 40(s0)
	sd t1, 104(s0)
	sd t2, 168(s0)
	sd t3, 232(s0)
	sd t4, 296(s0)
	sd t5, 360(s0)
	sd t6, 424(s0)
	sd a7, 488(s0)
	ld t0, 48(s0)
	ld t1, 112(s0)
	ld t2, 176(s0)
	ld t3, 240(s0)
	ld t4, 304(s0)
	ld t5, 368(s0)
	ld t6, 432(s0)
	ld a7, 496(s0)
	srli s4, t0, 32
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 32
	xor t0, t0, s4
	srli s4, t1, 32
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 32
	xor t1, t1, s4
	srli s4, t2, 32
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 32
	xor t2, t2, s4
	srli s4, t3, 32
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 32
	xor t3, t3, s4
	srli s4, t0, 16
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 16
	xor t0, t0, s4
	srli s4, t1, 16
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 16
	xor t1, t1, s4
	srli s4, t4, 16
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 16
	xor t4, t4, s4
	srli s4, t5, 16
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 16
	xor t5, t5, s4
	srli s4, t0, 8
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 8
	xor t0, t0, s4
	srli s4, t2, 8
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 8
	xor t2, t2, s4
	srli s4, t4, 8
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 8
	xor t4, t4, s4
	srli s4, t6, 8
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 8
	xor t6, t6, s4
	sd t0, 48(s0)
	sd t1, 112(s0)
	sd t2, 176(s0)
	sd t3, 240(s0)
	sd t4, 304(s0)
	sd t5, 368(s0)
	sd t6, 432(s0)
	sd a7, 496(s0)
	ld t0, 56(s0)
	ld t1, 120(s0)
	ld t2, 184(s0)
	ld t3, 248(s0)
	ld t4, 312(s0)
	ld t5, 376(s0)
	ld t6, 440(s0)
	ld a7, 504(s0)
	srli s4, t0, 32
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 32
	xor t0, t0, s4
	srli s4, t1, 32
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 32
	xor t1, t1, s4
	srli s4, t2, 32
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 32
	xor t2, t2, s4
	srli s4, t3, 32
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 32
	xor t3, t3, s4
	srli s4, t0, 16
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 16
	xor t0, t0, s4
	srli s4, t1, 16
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 16
	xor t1, t1, s4
	srli s4, t4, 16
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 16
	xor t4, t4, s4
	srli s4, t5, 16
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 16
	xor t5, t5, s4
	srli s4, t0, 8
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 8
	xor t0, t0, s4
	srli s4, t2, 8
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 8
	xor t2, t2, s4
	srli s4, t4, 8
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 8
	xor t4, t4, s4
	srli s4, t6, 8
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 8
	xor t6, t6, s4
	sd t0, 56(s0)
	sd t1, 120(s0)
	sd t2, 184(s0)
	sd t3, 248(s0)
	sd t4, 312(s0)
	sd t5, 376(s0)
	sd t6, 440(s0)
	sd a7, 504(s0)
	ld s1, 24(a0)
	ld s2, 32(a0)
	ld s3, 40(a0)
	ld t0, 0(s0)
	ld t1, 8(s0)
	ld t2, 16(s0)
	ld t3, 24(s0)
	ld t4, 32(s0)
	ld t5, 40(s0)
	ld t6, 48(s0)
	ld a7, 56(s0)
	srli s4, t0, 4
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 4
	xor t0, t0, s4
	srli s4, t1, 4
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 4
	xor t1, t1, s4
	srli s4, t2, 4
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 4
	xor t2, t2, s4
	srli s4, t3, 4
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 4
	xor t3, t3, s4
	srli s4, t0, 2
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 2
	xor t0, t0, s4
	srli s4, t1, 2
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 2
	xor t1, t1, s4
	srli s4, t4, 2
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 2
	xor t4, t4, s4
	srli s4, t5, 2
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 2
	xor t5, t5, s4
	srli s4, t0, 1
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 1
	xor t0, t0, s4
	srli s4, t2, 1
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 1
	xor t2, t2, s4
	srli s4, t4, 1
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 1
	xor t4, t4, s4
	srli s4, t6, 1
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 1
	xor t6, t6, s4
	sd t0, 0(s0)
	sd t1, 8(s0)
	sd t2, 16(s0)
	sd t3, 24(s0)
	sd t4, 32(s0)
	sd t5, 40(s0)
	sd t6, 48(s0)
	sd a7, 56(s0)
	ld t0, 64(s0)
	ld t1, 72(s0)
	ld t2, 80(s0)
	ld t3, 88(s0)
	ld t4, 96(s0)
	ld t5, 104(s0)
	ld t6, 112(s0)
	ld a7, 120(s0)
	srli s4, t0, 4
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 4
	xor t0, t0, s4
	srli s4, t1, 4
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 4
	xor t1, t1, s4
	srli s4, t2, 4
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 4
	xor t2, t2, s4
	srli s4, t3, 4
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 4
	xor t3, t3, s4
	srli s4, t0, 2
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 2
	xor t0, t0, s4
	srli s4, t1, 2
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 2
	xor t1, t1, s4
	srli s4, t4, 2
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 2
	xor t4, t4, s4
	srli s4, t5, 2
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 2
	xor t5, t5, s4
	srli s4, t0, 1
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 1
	xor t0, t0, s4
	srli s4, t2, 1
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 1
	xor t2, t2, s4
	srli s4, t4, 1
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 1
	xor t4, t4, s4
	srli s4, t6, 1
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 1
	xor t6, t6, s4
	sd t0, 64(s0)
	sd t1, 72(s0)
	sd t2, 80(s0)
	sd t3, 88(s0)
	sd t4, 96(s0)
	sd t5, 104(s0)
	sd t6, 112(s0)
	sd a7, 120(s0)
	ld t0, 128(s0)
	ld t1, 136(s0)
	ld t2, 144(s0)
	ld t3, 152(s0)
	ld t4, 160(s0)
	ld t5, 168(s0)
	ld t6, 176(s0)
	ld a7, 184(s0)
	srli s4, t0, 4
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 4
	xor t0, t0, s4
	srli s4, t1, 4
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 4
	xor t1, t1, s4
	srli s4, t2, 4
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 4
	xor t2, t2, s4
	srli s4, t3, 4
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 4
	xor t3, t3, s4
	srli s4, t0, 2
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 2
	xor t0, t0, s4
	srli s4, t1, 2
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 2
	xor t1, t1, s4
	srli s4, t4, 2
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 2
	xor t4, t4, s4
	srli s4, t5, 2
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 2
	xor t5, t5, s4
	srli s4, t0, 1
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 1
	xor t0, t0, s4
	srli s4, t2, 1
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 1
	xor t2, t2, s4
	srli s4, t4, 1
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 1
	xor t4, t4, s4
	srli s4, t6, 1
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 1
	xor t6, t6, s4
	sd t0, 128(s0)
	sd t1, 136(s0)
	sd t2, 144(s0)
	sd t3, 152(s0)
	sd t4, 160(s0)
	sd t5, 168(s0)
	sd t6, 176(s0)
	sd a7, 184(s0)
	ld t0, 192(s0)
	ld t1, 200(s0)
	ld t2, 208(s0)
	ld t3, 216(s0)
	ld t4, 224(s0)
	ld t5, 232(s0)
	ld t6, 240(s0)
	ld a7, 248(s0)
	srli s4, t0, 4
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 4
	xor t0, t0, s4
	srli s4, t1, 4
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 4
	xor t1, t1, s4
	srli s4, t2, 4
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 4
	xor t2, t2, s4
	srli s4, t3, 4
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 4
	xor t3, t3, s4
	srli s4, t0, 2
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 2
	xor t0, t0, s4
	srli s4, t1, 2
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 2
	xor t1, t1, s4
	srli s4, t4, 2
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 2
	xor t4, t4, s4
	srli s4, t5, 2
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 2
	xor t5, t5, s4
	srli s4, t0, 1
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 1
	xor t0, t0, s4
	srli s4, t2, 1
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 1
	xor t2, t2, s4
	srli s4, t4, 1
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 1
	xor t4, t4, s4
	srli s4, t6, 1
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 1
	xor t6, t6, s4
	sd t0, 192(s0)
	sd t1, 200(s0)
	sd t2, 208(s0)
	sd t3, 216(s0)
	sd t4, 224(s0)
	sd t5, 232(s0)
	sd t6, 240(s0)
	sd a7, 248(s0)
	ld t0, 256(s0)
	ld t1, 264(s0)
	ld t2, 272(s0)
	ld t3, 280(s0)
	ld t4, 288(s0)
	ld t5, 296(s0)
	ld t6, 304(s0)
	ld a7, 312(s0)
	srli s4, t0, 4
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 4
	xor t0, t0, s4
	srli s4, t1, 4
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 4
	xor t1, t1, s4
	srli s4, t2, 4
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 4
	xor t2, t2, s4
	srli s4, t3, 4
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 4
	xor t3, t3, s4
	srli s4, t0, 2
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 2
	xor t0, t0, s4
	srli s4, t1, 2
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 2
	xor t1, t1, s4
	srli s4, t4, 2
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 2
	xor t4, t4, s4
	srli s4, t5, 2
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 2
	xor t5, t5, s4
	srli s4, t0, 1
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 1
	xor t0, t0, s4
	srli s4, t2, 1
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 1
	xor t2, t2, s4
	srli s4, t4, 1
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 1
	xor t4, t4, s4
	srli s4, t6, 1
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 1
	xor t6, t6, s4
	sd t0, 256(s0)
	sd t1, 264(s0)
	sd t2, 272(s0)
	sd t3, 280(s0)
	sd t4, 288(s0)
	sd t5, 296(s0)
	sd t6, 304(s0)
	sd a7, 312(s0)
	ld t0, 320(s0)
	ld t1, 328(s0)
	ld t2, 336(s0)
	ld t3, 344(s0)
	ld t4, 352(s0)
	ld t5, 360(s0)
	ld t6, 368(s0)
	ld a7, 376(s0)
	srli s4, t0, 4
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 4
	xor t0, t0, s4
	srli s4, t1, 4
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 4
	xor t1, t1, s4
	srli s4, t2, 4
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 4
	xor t2, t2, s4
	srli s4, t3, 4
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 4
	xor t3, t3, s4
	srli s4, t0, 2
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 2
	xor t0, t0, s4
	srli s4, t1, 2
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 2
	xor t1, t1, s4
	srli s4, t4, 2
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 2
	xor t4, t4, s4
	srli s4, t5, 2
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 2
	xor t5, t5, s4
	srli s4, t0, 1
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 1
	xor t0, t0, s4
	srli s4, t2, 1
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 1
	xor t2, t2, s4
	srli s4, t4, 1
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 1
	xor t4, t4, s4
	srli s4, t6, 1
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 1
	xor t6, t6, s4
	sd t0, 320(s0)
	sd t1, 328(s0)
	sd t2, 336(s0)
	sd t3, 344(s0)
	sd t4, 352(s0)
	sd t5, 360(s0)
	sd t6, 368(s0)
	sd a7, 376(s0)
	ld t0, 384(s0)
	ld t1, 392(s0)
	ld t2, 400(s0)
	ld t3, 408(s0)
	ld t4, 416(s0)
	ld t5, 424(s0)
	ld t6, 432(s0)
	ld a7, 440(s0)
	srli s4, t0, 4
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 4
	xor t0, t0, s4
	srli s4, t1, 4
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 4
	xor t1, t1, s4
	srli s4, t2, 4
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 4
	xor t2, t2, s4
	srli s4, t3, 4
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 4
	xor t3, t3, s4
	srli s4, t0, 2
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 2
	xor t0, t0, s4
	srli s4, t1, 2
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 2
	xor t1, t1, s4
	srli s4, t4, 2
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 2
	xor t4, t4, s4
	srli s4, t5, 2
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 2
	xor t5, t5, s4
	srli s4, t0, 1
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 1
	xor t0, t0, s4
	srli s4, t2, 1
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 1
	xor t2, t2, s4
	srli s4, t4, 1
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 1
	xor t4, t4, s4
	srli s4, t6, 1
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 1
	xor t6, t6, s4
	sd t0, 384(s0)
	sd t1, 392(s0)
	sd t2, 400(s0)
	sd t3, 408(s0)
	sd t4, 416(s0)
	sd t5, 424(s0)
	sd t6, 432(s0)
	sd a7, 440(s0)
	ld t0, 448(s0)
	ld t1, 456(s0)
	ld t2, 464(s0)
	ld t3, 472(s0)
	ld t4, 480(s0)
	ld t5, 488(s0)
	ld t6, 496(s0)
	ld a7, 504(s0)
	srli s4, t0, 4
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 4
	xor t0, t0, s4
	srli s4, t1, 4
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 4
	xor t1, t1, s4
	srli s4, t2, 4
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 4
	xor t2, t2, s4
	srli s4, t3, 4
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 4
	xor t3, t3, s4
	srli s4, t0, 2
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 2
	xor t0, t0, s4
	srli s4, t1, 2
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 2
	xor t1, t1, s4
	srli s4, t4, 2
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 2
	xor t4, t4, s4
	srli s4, t5, 2
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 2
	xor t5, t5, s4
	srli s4, t0, 1
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 1
	xor t0, t0, s4
	srli s4, t2, 1
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 1
	xor t2, t2, s4
	srli s4, t4, 1
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 1
	xor t4, t4, s4
	srli s4, t6, 1
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 1
	xor t6, t6, s4
	sd t0, 448(s0)
	sd t1, 456(s0)
	sd t2, 464(s0)
	sd t3, 472(s0)
	sd t4, 480(s0)
	sd t5, 488(s0)
	sd t6, 496(s0)
	sd a7, 504(s0)
	addi a3, s0, 512
	addi a4, zero, 8
27:
	ld a5, 0(a3)
	addi a3, a3, 8
	slli t0, a5, 21
	srai t0, t0, 63
	ld a6, 248(s0)
	xor t0, t0, a6
	slli t1, a5, 20
	srai t1, t1, 63
	ld a6, 312(s0)
	xor t1, t1, a6
	slli t2, a5, 19
	srai t2, t2, 63
	ld a6, 376(s0)
	xor t2, t2, a6
	slli t3, a5, 18
	srai t3, t3, 63
	ld a6, 440(s0)
	xor t3, t3, a6
	slli t4, a5, 17
	srai t4, t4, 63
	ld a6, 504(s0)
	xor t4, t4, a6
	slli t5, a5, 16
	srai t5, t5, 63
	ld a6, 8(s0)
	xor t5, t5, a6
	or t6, t5, t1
	xor t6, t6, t1
	xor a0, t2, t6
	or a7, t3, t0
	xor s1, t5, t3
	and s2, a7, s1
	xor s3, t2, s2
	or s4, s3, a0
	xor s4, s4, a0
	xor s5, t1, t0
	xor s6, t3, s5
	xori s6, s6, -1
	and s6, s6, a0
	or s2, t0, s2
	xor s6, s6, s2
	or s2, s6, s4
	xor s2, s2, s4
	or t0, t5, t0
	or s7, s6, t0
	xori s3, s3, -1
	and s3, s3, t1
	xor s8, s7, s3
	or t2, t2, t0
	xor t2, t2, t0
	xor t2, s3, t2
	xori s1, s1, -1
	and s1, s1, s5
	or t2, t2, s1
	or t3, t3, t6
	xor t3, t3, t6
	xor t6, a0, s7
	or t6, t6, t3
	xor t6, t6, t3
	xori t3, t6, -1
	and s6, a7, s6
	xor t3, t3, s6
	or s8, s8, t4
	xor s8, s8, t4
	xor s8, s8, t3
	xor t6, s5, t6
	or s3, s3, t6
	xor s3, a7, s3
	xor t5, t5, s3
	xor t3, t3, t5
	or s4, s4, t4
	xor s4, s4, t3
	xor a7, a7, s7
	or a7, t2, a7
	xor a7, t5, a7
	or s5, s5, t3
	xor s5, a7, s5
	or t3, s2, t4
	xor t3, t3, s5
	or t1, t1, a0
	or t1, t1, a7
	xor t1, t1, a7
	and s2, s2, t5
	xor t1, t1, s2
	or t1, t1, t4
	xor t1, t1, t2
	ld a6, 64(s0)
	xor a6, a6, t1
	sd a6, 64(s0)
	ld a6, 80(s0)
	xor a6, a6, s8
	sd a6, 80(s0)
	ld a6, 464(s0)
	xor a6, a6, t3
	sd a6, 464(s0)
	ld a6, 480(s0)
	xor a6, a6, s4
	sd a6, 480(s0)
	slli t0, a5, 27
	srai t0, t0, 63
	ld a6, 488(s0)
	xor t0, t0, a6
	slli t1, a5, 26
	srai t1, t1, 63
	ld a6, 56(s0)
	xor t1, t1, a6
	slli t2, a5, 25
	srai t2, t2, 63
	ld a6, 120(s0)
	xor t2, t2, a6
	slli t3, a5, 24
	srai t3, t3, 63
	ld a6, 184(s0)
	xor t3, t3, a6
	slli t4, a5, 23
	srai t4, t4, 63
	ld a6, 248(s0)
	xor t4, t4, a6
	slli t5, a5, 22
	srai t5, t5, 63
	ld a6, 312(s0)
	xor t5, t5, a6
	xor t6, t4, t1
	or a0, t5, t0
	xor a0, a0, t0
	xori a0, a0, -1
	and a0, a0, t1
	or a7, t4, a0
	or s1, t6, t0
	xor s1, s1, t0
	and s2, t5, t6
	xor t1, t1, s2
	or s2, t1, s1
	xor s2, s2, s1
	and s3, t3, t0
	xor a0, a0, s1
	and a0, a7, a0
	or s1, a0, s3
	xor s1, s1, s3
	and s4, t3, a0
	xori t5, t5, -1
	xor t5, s4, t5
	xor t0, t0, t6
	or s5, t0, s3
	xor s5, s5, s3
	xor s6, t5, s5
	xori s1, s1, -1
	and s1, s1, t2
	xor s1, s1, s6
	or t4, t4, s5
	xor t4, t4, s5
	xor t1, t1, t4
	or t5, t5, t1
	xor t5, t5, t1
	xor t3, t3, t0
	xor t5, t5, t3
	or s5, a7, t2
	xor s5, s5, t2
	xor s5, s5, t5
	xor s4, s4, t4
	or t3, t3, s4
	xor a7, a7, s6
	or s3, s3, a7
	xor s4, t3, s3
	xor a0, a0, s6
	xor t5, t5, a0
	and s3, s3, t5
	and t6, t6, t3
	xor s3, s3, t6
	or t6, s3, t2
	xor t6, t6, s4
	or s3, s3, t1
	xor s3, s3, t1
	or t0, t0, a7
	xor s3, s3, t0
	or s2, s2, t2
	xor s2, s2, s3
	ld a6, 400(s0)
	xor a6, a6, s2
	sd a6, 400(s0)
	ld a6, 432(s0)
	xor a6, a6, t6
	sd a6, 432(s0)
	ld a6, 256(s0)
	xor a6, a6, s1
	sd a6, 256(s0)
	ld a6, 224(s0)
	xor a6, a6, s5
	sd a6, 224(s0)
	slli t0, a5, 33
	srai t0, t0, 63
	ld a6, 232(s0)
	xor t0, t0, a6
	slli t1, a5, 32
	srai t1, t1, 63
	ld a6, 296(s0)
	xor t1, t1, a6
	slli t2, a5, 31
	srai t2, t2, 63
	ld a6, 360(s0)
	xor t2, t2, a6
	slli t3, a5, 30
	srai t3, t3, 63
	ld a6, 424(s0)
	xor t3, t3, a6
	slli t4, a5, 29
	srai t4, t4, 63
	ld a6, 488(s0)
	xor t4, t4, a6
	slli t5, a5, 28
	srai t5, t5, 63
	ld a6, 56(s0)
	xor t5, t5, a6
	or t6, t5, t4
	xor t6, t6, t4
	xor a0, t3, t0
	or a7, t6, a0
	xor s1, t2, t0
	or s2, s1, t5
	xor s2, s2, t5
	xor s3, a7, s2
	xor s4, t4, a0
	or s5, s4, t0
	xor s5, s5, t0
	xor a7, a7, s5
	or s5, s3, a7
	xor s5, s5, a7
	and s6, t0, s3
	or s6, t2, s6
	and s6, t5, s6
	xor s6, s4, s6
	or s7, s3, t1
	xor s7, s7, t1
	xor s7, s7, s6
	and a0, a0, s1
	xor s1, t5, t2
	xor s8, a7, s1
	or s8, t3, s8
	or s8, s8, a0
	xor s8, s8, a0
	or s2, s2, s1
	or s1, s6, s2
	xor s1, s1, s2
	and t0, t2, t0
	or a0, t0, t4
	xor a0, a0, t4
	xor s1, s1, a0
	and a7, a7, s1
	or t0, s4, t0
	or t0, t0, a7
	xor t0, t0, a7
	xor t5, t5, t0
	and s8, s8, t1
	xor s8, s8, t5
	xori s3, s3, -1
	or t4, t4, s3
	or t3, t3, t4
	xor s4, s4, t3
	xor s2, s2, s4
	xori s5, s5, -1
	and s5, s5, t1
	xor s5, s5, s2
	and t2, t2, s3
	xor s6, s6, t2
	or s4, s4, s6
	xor t6, t6, t5
	xor s4, s4, t6
	or s1, s1, t1
	xor s1, s1, s4
	ld a6, 176(s0)
	xor a6, a6, s7
	sd a6, 176(s0)
	ld a6, 128(s0)
	xor a6, a6, s1
	sd a6, 128(s0)
	ld a6, 32(s0)
	xor a6, a6, s8
	sd a6, 32(s0)
	ld a6, 16(s0)
	xor a6, a6, s5
	sd a6, 16(s0)
	slli t0, a5, 39
	srai t0, t0, 63
	ld a6, 472(s0)
	xor t0, t0, a6
	slli t1, a5, 38
	srai t1, t1, 63
	ld a6, 40(s0)
	xor t1, t1, a6
	slli t2, a5, 37
	srai t2, t2, 63
	ld a6, 104(s0)
	xor t2, t2, a6
	slli t3, a5, 36
	srai t3, t3, 63
	ld a6, 168(s0)
	xor t3, t3, a6
	slli t4, a5, 35
	srai t4, t4, 63
	ld a6, 232(s0)
	xor t4, t4, a6
	slli t5, a5, 34
	srai t5, t5, 63
	ld a6, 296(s0)
	xor t5, t5, a6
	xor t5, t5, t3
	xor t3, t3, t1
	or t6, t4, t2
	xor t6, t1, t6
	xori t6, t6, -1
	and t6, t6, t3
	or a0, t3, t4
	xor a0, a0, t4
	xor a7, t2, a0
	or s1, t5, a7
	or s1, s1, t6
	xor s1, s1, t6
	xor s2, t4, s1
	and a7, a7, s2
	or t3, t3, a7
	xor t3, t3, a7
	xor t5, t5, s2
	xori t3, t3, -1
	and t3, t3, t5
	xor t6, t6, t3
	xor t4, t4, t2
	or t1, t1, a0
	xor t5, t5, t1
	or t1, t5, t4
	xor t1, t1, t4
	xor s1, s1, t1
	or t1, t0, t6
	xor t1, t1, t6
	xor t1, t1, s1
	xori s1, s1, -1
	or a0, t6, t0
	xor a0, a0, t0
	xor a0, a0, s1
	xor t6, t6, s1
	or t6, t6, t4
	xor t6, t6, t4
	or a7, a7, t6
	xor t5, t5, a7
	or a7, s2, t0
	xor a7, a7, t5
	and t0, t0, s2
	xor t0, t0, t5
	ld a6, 496(s0)
	xor a6, a6, t0
	sd a6, 496(s0)
	ld a6, 416(s0)
	xor a6, a6, a7
	sd a6, 416(s0)
	ld a6, 272(s0)
	xor a6, a6, a0
	sd a6, 272(s0)
	ld a6, 384(s0)
	xor a6, a6, t1
	sd a6, 384(s0)
	slli t0, a5, 45
	srai t0, t0, 63
	ld a6, 216(s0)
	xor t0, t0, a6
	slli t1, a5, 44
	srai t1, t1, 63
	ld a6, 280(s0)
	xor t1, t1, a6
	slli t2, a5, 43
	srai t2, t2, 63
	ld a6, 344(s0)
	xor t2, t2, a6
	slli t3, a5, 42
	srai t3, t3, 63
	ld a6, 408(s0)
	xor t3, t3, a6
	slli t4, a5, 41
	srai t4, t4, 63
	ld a6, 472(s0)
	xor t4, t4, a6
	slli t5, a5, 40
	srai t5, t5, 63
	ld a6, 40(s0)
	xor t5, t5, a6
	or t6, t5, t3
	or a0, t6, t0
	xor a0, a0, t0
	xor a7, t5, a0
	xor s1, t3, a7
	or s2, t2, s1
	or a0, a0, t2
	xor a0, a0, t2
	xor t3, t3, a0
	and a0, t1, t3
	or s1, t5, s1
	xor a0, a0, s1
	xor a0, t2, a0
	xor t0, t0, a0
	or s3, a7, t0
	and s4, t1, s3
	xor s5, a7, s4
	and s6, t2, s1
	xor s5, s5, s6
	or s3, s3, t5
	xor s3, s3, t5
	xor s6, t3, s3
	xor t1, t1, s2
	xori s6, s6, -1
	and s6, s6, t1
	xori s6, s6, -1
	or s6, s6, t4
	xor s6, s6, t4
	xor s6, s6, a0
	or a0, t3, s4
	xor a0, a0, s4
	xor s3, s3, t1
	or s3, s5, s3
	or s3, s3, a0
	xor s3, s3, a0
	or a0, s2, s3
	xor a0, a0, s3
	and t0, t0, s3
	xor t1, t1, t0
	and s1, t3, s1
	or s1, t1, s1
	xor s4, s4, s1
	and s4, s4, t4
	xor s4, s4, s5
	xor t5, t5, t6
	xor s3, s3, t5
	and t2, t2, t1
	xor s3, s3, t2
	or a0, a0, t4
	xor a0, a0, s3
	xor t3, s2, t3
	or t3, t3, s3
	xor t3, t3, s3
	xor a7, a7, t1
	xor t3, t3, a7
	and s2, s2, t4
	xor s2, s2, t3
	ld a6, 368(s0)
	xor a6, a6, s4
	sd a6, 368(s0)
	ld a6, 448(s0)
	xor a6, a6, s6
	sd a6, 448(s0)
	ld a6, 160(s0)
	xor a6, a6, s2
	sd a6, 160(s0)
	ld a6, 48(s0)
	xor a6, a6, a0
	sd a6, 48(s0)
	slli t0, a5, 51
	srai t0, t0, 63
	ld a6, 456(s0)
	xor t0, t0, a6
	slli t1, a5, 50
	srai t1, t1, 63
	ld a6, 24(s0)
	xor t1, t1, a6
	slli t2, a5, 49
	srai t2, t2, 63
	ld a6, 88(s0)
	xor t2, t2, a6
	slli t3, a5, 48
	srai t3, t3, 63
	ld a6, 152(s0)
	xor t3, t3, a6
	slli t4, a5, 47
	srai t4, t4, 63
	ld a6, 216(s0)
	xor t4, t4, a6
	slli t5, a5, 46
	srai t5, t5, 63
	ld a6, 280(s0)
	xor t5, t5, a6
	xor t6, t4, t1
	or a0, t4, t0
	and a0, t5, a0
	xor t6, t6, a0
	xor a7, t0, t6
	or s1, t1, a7
	xor s1, s1, a7
	and a7, t5, a7
	xor s2, t4, a7
	xor s3, t5, t3
	or s4, s2, s3
	xor s5, t6, s4
	and s6, t3, s5
	or s7, s6, t0
	xor s7, s7, t0
	or s2, s1, s2
	xor s8, s7, s2
	and s9, s8, t2
	xor s9, s9, s5
	xor s4, t4, s4
	or s10, t0, s4
	xor s10, s10, s4
	xor t3, t3, s10
	or s10, t1, s6
	xor s10, s10, s6
	or s10, t3, s10
	or t4, t4, s3
	xor s8, s8, t4
	or a0, a0, s10
	xor s8, s8, a0
	or s5, t5, s5
	and s2, s2, s5
	xor s2, t3, s2
	xori s7, s7, -1
	and s7, s7, s2
	or s1, s1, t2
	xor s1, s1, s7
	xor t6, t6, s2
	or t1, t1, t6
	xor t1, t1, t6
	xori t4, t4, -1
	xor s4, s4, t4
	xor t1, t1, s4
	or t1, t1, t2
	xor t1, t1, t2
	xor t1, t1, s8
	xor t0, t0, a7
	xor t5, t5, t3
	and t0, t0, t5
	xor s6, s6, s4
	xor t0, t0, s6
	or s10, s10, t2
	xor s10, s10, t2
	xor s10, s10, t0
	ld a6, 336(s0)
	xor a6, a6, s9
	sd a6, 336(s0)
	ld a6, 352(s0)
	xor a6, a6, s1
	sd a6, 352(s0)
	ld a6, 192(s0)
	xor a6, a6, t1
	sd a6, 192(s0)
	ld a6, 304(s0)
	xor a6, a6, s10
	sd a6, 304(s0)
	slli t0, a5, 57
	srai t0, t0, 63
	ld a6, 200(s0)
	xor t0, t0, a6
	slli t1, a5, 56
	srai t1, t1, 63
	ld a6, 264(s0)
	xor t1, t1, a6
	slli t2, a5, 55
	srai t2, t2, 63
	ld a6, 328(s0)
	xor t2, t2, a6
	slli t3, a5, 54
	srai t3, t3, 63
	ld a6, 392(s0)
	xor t3, t3, a6
	slli t4, a5, 53
	srai t4, t4, 63
	ld a6, 456(s0)
	xor t4, t4, a6
	slli t5, a5, 52
	srai t5, t5, 63
	ld a6, 24(s0)
	xor t5, t5, a6
	xor t6, t2, t1
	xor a0, t3, t6
	and a7, t0, a0
	and s1, t2, t6
	xor s2, t4, s1
	and s3, a7, s2
	and s4, t0, s1
	xor s5, t3, s4
	or s6, s2, s5
	xor t6, t0, t6
	xor s7, s6, t6
	or s8, t5, s3
	xor s8, s8, s3
	xor s8, s8, s7
	xori a0, a0, -1
	and a0, a0, t1
	or s7, s2, a0
	xor s5, a7, s5
	xor s7, s7, s5
	xor a7, a7, t6
	or t2, t2, a7
	xor t2, t2, a7
	or t6, s2, t2
	xor t6, t6, t2
	xor t1, t1, s5
	xor t6, t6, t1
	or a7, a7, s4
	xor a7, a7, s4
	or t2, t2, a7
	xor s6, t4, s6
	and s6, t6, s6
	xor s6, t2, s6
	and s4, s6, t5
	xor s4, s4, t6
	or s2, s2, t3
	xor s2, s2, t3
	or a7, a7, s2
	or s1, s1, t6
	and a7, a7, s1
	xor s6, s6, a7
	xor a0, a0, t2
	and t0, t0, a0
	or s3, s3, t0
	xor a7, a7, s3
	or t0, a7, t5
	xor t0, t0, t5
	xor t0, t0, s7
	and t4, t4, s3
	xori s7, s7, -1
	xor t4, t4, s7
	xor a7, a7, t4
	or s6, s6, t5
	xor s6, s6, a7
	ld a6, 112(s0)
	xor a6, a6, s8
	sd a6, 112(s0)
	ld a6, 144(s0)
	xor a6, a6, s4
	sd a6, 144(s0)
	ld a6, 288(s0)
	xor a6, a6, s6
	sd a6, 288(s0)
	ld a6, 0(s0)
	xor a6, a6, t0
	sd a6, 0(s0)
	slli t0, a5, 63
	srai t0, t0, 63
	ld a6, 504(s0)
	xor t0, t0, a6
	slli t1, a5, 62
	srai t1, t1, 63
	ld a6, 8(s0)
	xor t1, t1, a6
	slli t2, a5, 61
	srai t2, t2, 63
	ld a6, 72(s0)
	xor t2, t2, a6
	slli t3, a5, 60
	srai t3, t3, 63
	ld a6, 136(s0)
	xor t3, t3, a6
	slli t4, a5, 59
	srai t4, t4, 63
	ld a6, 200(s0)
	xor t4, t4, a6
	slli t5, a5, 58
	srai t5, t5, 63
	ld a6, 264(s0)
	xor t5, t5, a6
	or t6, t3, t4
	xor t6, t6, t4
	or a0, t1, t3
	xor a0, a0, t3
	xor a0, t2, a0
	and a7, t5, a0
	or s1, a7, t6
	xor s1, s1, t6
	or s2, t4, a0
	xor s2, s2, a0
	or s3, t5, s2
	or s4, t4, t3
	xor s4, s4, t3
	xor s4, t1, s4
	and s5, s3, s4
	or a7, a7, s5
	xori a0, a0, -1
	xor s5, s5, a0
	or t3, t3, s3
	xor t3, t3, s3
	xor s5, s5, t3
	xor t6, t6, s5
	or t3, s1, t0
	xor t3, t3, t6
	xor t6, t5, t6
	and s3, t1, t6
	xor s5, t4, s5
	xor s3, s3, s5
	xor s2, s2, s3
	xor s3, a7, s3
	or t4, t4, s3
	xor t1, t1, t6
	xor t4, t4, t1
	and a7, a7, t0
	xor a7, a7, t4
	xor s4, s4, s2
	or s5, t2, s5
	xor s5, s4, s5
	xor t5, t5, s5
	and t5, t5, t0
	xor t5, t5, s2
	or s4, s4, t2
	xor s4, s4, t2
	and t4, t4, s4
	xor s1, s1, s5
	xor t4, t4, s1
	or t4, t4, t0
	xor t4, t4, s2
	ld a6, 208(s0)
	xor a6, a6, t5
	sd a6, 208(s0)
	ld a6, 96(s0)
	xor a6, a6, a7
	sd a6, 96(s0)
	ld a6, 320(s0)
	xor a6, a6, t3
	sd a6, 320(s0)
	ld a6, 240(s0)
	xor a6, a6, t4
	sd a6, 240(s0)
	ld a5, 0(a3)
	addi a3, a3, 8
	slli t0, a5, 21
	srai t0, t0, 63
	ld a6, 240(s0)
	xor t0, t0, a6
	slli t1, a5, 20
	srai t1, t1, 63
	ld a6, 304(s0)
	xor t1, t1, a6
	slli t2, a5, 19
	srai t2, t2, 63
	ld a6, 368(s0)
	xor t2, t2, a6
	slli t3, a5, 18
	srai t3, t3, 63
	ld a6, 432(s0)
	xor t3, t3, a6
	slli t4, a5, 17
	srai t4, t4, 63
	ld a6, 496(s0)
	xor t4, t4, a6
	slli t5, a5, 16
	srai t5, t5, 63
	ld a6, 0(s0)
	xor t5, t5, a6
	or t6, t5, t1
	xor t6, t6, t1
	xor a0, t2, t6
	or a7, t3, t0
	xor s1, t5, t3
	and s2, a7, s1
	xor s3, t2, s2
	or s4, s3, a0
	xor s4, s4, a0
	xor s5, t1, t0
	xor s6, t3, s5
	xori s6, s6, -1
	and s6, s6, a0
	or s2, t0, s2
	xor s6, s6, s2
	or s2, s6, s4
	xor s2, s2, s4
	or t0, t5, t0
	or s7, s6, t0
	xori s3, s3, -1
	and s3, s3, t1
	xor s8, s7, s3
	or t2, t2, t0
	xor t2, t2, t0
	xor t2, s3, t2
	xori s1, s1, -1
	and s1, s1, s5
	or t2, t2, s1
	or t3, t3, t6
	xor t3, t3, t6
	xor t6, a0, s7
	or t6, t6, t3
	xor t6, t6, t3
	xori t3, t6, -1
	and s6, a7, s6
	xor t3, t3, s6
	or s8, s8, t4
	xor s8, s8, t4
	xor s8, s8, t3
	xor t6, s5, t6
	or s3, s3, t6
	xor s3, a7, s3
	xor t5, t5, s3
	xor t3, t3, t5
	or s4, s4, t4
	xor s4, s4, t3
	xor a7, a7, s7
	or a7, t2, a7
	xor a7, t5, a7
	or s5, s5, t3
	xor s5, a7, s5
	or t3, s2, t4
	xor t3, t3, s5
	or t1, t1, a0
	or t1, t1, a7
	xor t1, t1, a7
	and s2, s2, t5
	xor t1, t1, s2
	or t1, t1, t4
	xor t1, t1, t2
	ld a6, 72(s0)
	xor a6, a6, t1
	sd a6, 72(s0)
	ld a6, 88(s0)
	xor a6, a6, s8
	sd a6, 88(s0)
	ld a6, 472(s0)
	xor a6, a6, t3
	sd a6, 472(s0)
	ld a6, 488(s0)
	xor a6, a6, s4
	sd a6, 488(s0)
	slli t0, a5, 27
	srai t0, t0, 63
	ld a6, 480(s0)
	xor t0, t0, a6
	slli t1, a5, 26
	srai t1, t1, 63
	ld a6, 48(s0)
	xor t1, t1, a6
	slli t2, a5, 25
	srai t2, t2, 63
	ld a6, 112(s0)
	xor t2, t2, a6
	slli t3, a5, 24
	srai t3, t3, 63
	ld a6, 176(s0)
	xor t3, t3, a6
	slli t4, a5, 23
	srai t4, t4, 63
	ld a6, 240(s0)
	xor t4, t4, a6
	slli t5, a5, 22
	srai t5, t5, 63
	ld a6, 304(s0)
	xor t5, t5, a6
	xor t6, t4, t1
	or a0, t5, t0
	xor a0, a0, t0
	xori a0, a0, -1
	and a0, a0, t1
	or a7, t4, a0
	or s1, t6, t0
	xor s1, s1, t0
	and s2, t5, t6
	xor t1, t1, s2
	or s2, t1, s1
	xor s2, s2, s1
	and s3, t3, t0
	xor a0, a0, s1
	and a0, a7, a0
	or s1, a0, s3
	xor s1, s1, s3
	and s4, t3, a0
	xori t5, t5, -1
	xor t5, s4, t5
	xor t0, t0, t6
	or s5, t0, s3
	xor s5, s5, s3
	xor s6, t5, s5
	xori s1, s1, -1
	and s1, s1, t2
	xor s1, s1, s6
	or t4, t4, s5
	xor t4, t4, s5
	xor t1, t1, t4
	or t5, t5, t1
	xor t5, t5, t1
	xor t3, t3, t0
	xor t5, t5, t3
	or s5, a7, t2
	xor s5, s5, t2
	xor s5, s5, t5
	xor s4, s4, t4
	or t3, t3, s4
	xor a7, a7, s6
	or s3, s3, a7
	xor s4, t3, s3
	xor a0, a0, s6
	xor t5, t5, a0
	and s3, s3, t5
	and t6, t6, t3
	xor s3, s3, t6
	or t6, s3, t2
	xor t6, t6, s4
	or s3, s3, t1
	xor s3, s3, t1
	or t0, t0, a7
	xor s3, s3, t0
	or s2, s2, t2
	xor s2, s2, s3
	ld a6, 408(s0)
	xor a6, a6, s2
	sd a6, 408(s0)
	ld a6, 440(s0)
	xor a6, a6, t6
	sd a6, 440(s0)
	ld a6, 264(s0)
	xor a6, a6, s1
	sd a6, 264(s0)
	ld a6, 232(s0)
	xor a6, a6, s5
	sd a6, 232(s0)
	slli t0, a5, 33
	srai t0, t0, 63
	ld a6, 224(s0)
	xor t0, t0, a6
	slli t1, a5, 32
	srai t1, t1, 63
	ld a6, 288(s0)
	xor t1, t1, a6
	slli t2, a5, 31
	srai t2, t2, 63
	ld a6, 352(s0)
	xor t2, t2, a6
	slli t3, a5, 30
	srai t3, t3, 63
	ld a6, 416(s0)
	xor t3, t3, a6
	slli t4, a5, 29
	srai t4, t4, 63
	ld a6, 480(s0)
	xor t4, t4, a6
	slli t5, a5, 28
	srai t5, t5, 63
	ld a6, 48(s0)
	xor t5, t5, a6
	or t6, t5, t4
	xor t6, t6, t4
	xor a0, t3, t0
	or a7, t6, a0
	xor s1, t2, t0
	or s2, s1, t5
	xor s2, s2, t5
	xor s3, a7, s2
	xor s4, t4, a0
	or s5, s4, t0
	xor s5, s5, t0
	xor a7, a7, s5
	or s5, s3, a7
	xor s5, s5, a7
	and s6, t0, s3
	or s6, t2, s6
	and s6, t5, s6
	xor s6, s4, s6
	or s7, s3, t1
	xor s7, s7, t1
	xor s7, s7, s6
	and a0, a0, s1
	xor s1, t5, t2
	xor s8, a7, s1
	or s8, t3, s8
	or s8, s8, a0
	xor s8, s8, a0
	or s2, s2, s1
	or s1, s6, s2
	xor s1, s1, s2
	and t0, t2, t0
	or a0, t0, t4
	xor a0, a0, t4
	xor s1, s1, a0
	and a7, a7, s1
	or t0, s4, t0
	or t0, t0, a7
	xor t0, t0, a7
	xor t5, t5, t0
	and s8, s8, t1
	xor s8, s8, t5
	xori s3, s3, -1
	or t4, t4, s3
	or t3, t3, t4
	xor s4, s4, t3
	xor s2, s2, s4
	xori s5, s5, -1
	and s5, s5, t1
	xor s5, s5, s2
	and t2, t2, s3
	xor s6, s6, t2
	or s4, s4, s6
	xor t6, t6, t5
	xor s4, s4, t6
	or s1, s1, t1
	xor s1, s1, s4
	ld a6, 184(s0)
	xor a6, a6, s7
	sd a6, 184(s0)
	ld a6, 136(s0)
	xor a6, a6, s1
	sd a6, 136(s0)
	ld a6, 40(s0)
	xor a6, a6, s8
	sd a6, 40(s0)
	ld a6, 24(s0)
	xor a6, a6, s5
	sd a6, 24(s0)
	slli t0, a5, 39
	srai t0, t0, 63
	ld a6, 464(s0)
	xor t0, t0, a6
	slli t1, a5, 38
	srai t1, t1, 63
	ld a6, 32(s0)
	xor t1, t1, a6
	slli t2, a5, 37
	srai t2, t2, 63
	ld a6, 96(s0)
	xor t2, t2, a6
	slli t3, a5, 36
	srai t3, t3, 63
	ld a6, 160(s0)
	xor t3, t3, a6
	slli t4, a5, 35
	srai t4, t4, 63
	ld a6, 224(s0)
	xor t4, t4, a6
	slli t5, a5, 34
	srai t5, t5, 63
	ld a6, 288(s0)
	xor t5, t5, a6
	xor t5, t5, t3
	xor t3, t3, t1
	or t6, t4, t2
	xor t6, t1, t6
	xori t6, t6, -1
	and t6, t6, t3
	or a0, t3, t4
	xor a0, a0, t4
	xor a7, t2, a0
	or s1, t5, a7
	or s1, s1, t6
	xor s1, s1, t6
	xor s2, t4, s1
	and a7, a7, s2
	or t3, t3, a7
	xor t3, t3, a7
	xor t5, t5, s2
	xori t3, t3, -1
	and t3, t3, t5
	xor t6, t6, t3
	xor t4, t4, t2
	or t1, t1, a0
	xor t5, t5, t1
	or t1, t5, t4
	xor t1, t1, t4
	xor s1, s1, t1
	or t1, t0, t6
	xor t1, t1, t6
	xor t1, t1, s1
	xori s1, s1, -1
	or a0, t6, t0
	xor a0, a0, t0
	xor a0, a0, s1
	xor t6, t6, s1
	or t6, t6, t4
	xor t6, t6, t4
	or a7, a7, t6
	xor t5, t5, a7
	or a7, s2, t0
	xor a7, a7, t5
	and t0, t0, s2
	xor t0, t0, t5
	ld a6, 504(s0)
	xor a6, a6, t0
	sd a6, 504(s0)
	ld a6, 424(s0)
	xor a6, a6, a7
	sd a6, 424(s0)
	ld a6, 280(s0)
	xor a6, a6, a0
	sd a6, 280(s0)
	ld a6, 392(s0)
	xor a6, a6, t1
	sd a6, 392(s0)
	slli t0, a5, 45
	srai t0, t0, 63
	ld a6, 208(s0)
	xor t0, t0, a6
	slli t1, a5, 44
	srai t1, t1, 63
	ld a6, 272(s0)
	xor t1, t1, a6
	slli t2, a5, 43
	srai t2, t2, 63
	ld a6, 336(s0)
	xor t2, t2, a6
	slli t3, a5, 42
	srai t3, t3, 63
	ld a6, 400(s0)
	xor t3, t3, a6
	slli t4, a5, 41
	srai t4, t4, 63
	ld a6, 464(s0)
	xor t4, t4, a6
	slli t5, a5, 40
	srai t5, t5, 63
	ld a6, 32(s0)
	xor t5, t5, a6
	or t6, t5, t3
	or a0, t6, t0
	xor a0, a0, t0
	xor a7, t5, a0
	xor s1, t3, a7
	or s2, t2, s1
	or a0, a0, t2
	xor a0, a0, t2
	xor t3, t3, a0
	and a0, t1, t3
	or s1, t5, s1
	xor a0, a0, s1
	xor a0, t2, a0
	xor t0, t0, a0
	or s3, a7, t0
	and s4, t1, s3
	xor s5, a7, s4
	and s6, t2, s1
	xor s5, s5, s6
	or s3, s3, t5
	xor s3, s3, t5
	xor s6, t3, s3
	xor t1, t1, s2
	xori s6, s6, -1
	and s6, s6, t1
	xori s6, s6, -1
	or s6, s6, t4
	xor s6, s6, t4
	xor s6, s6, a0
	or a0, t3, s4
	xor a0, a0, s4
	xor s3, s3, t1
	or s3, s5, s3
	or s3, s3, a0
	xor s3, s3, a0
	or a0, s2, s3
	xor a0, a0, s3
	and t0, t0, s3
	xor t1, t1, t0
	and s1, t3, s1
	or s1, t1, s1
	xor s4, s4, s1
	and s4, s4, t4
	xor s4, s4, s5
	xor t5, t5, t6
	xor s3, s3, t5
	and t2, t2, t1
	xor s3, s3, t2
	or a0, a0, t4
	xor a0, a0, s3
	xor t3, s2, t3
	or t3, t3, s3
	xor t3, t3, s3
	xor a7, a7, t1
	xor t3, t3, a7
	and s2, s2, t4
	xor s2, s2, t3
	ld a6, 376(s0)
	xor a6, a6, s4
	sd a6, 376(s0)
	ld a6, 456(s0)
	xor a6, a6, s6
	sd a6, 456(s0)
	ld a6, 168(s0)
	xor a6, a6, s2
	sd a6, 168(s0)
	ld a6, 56(s0)
	xor a6, a6, a0
	sd a6, 56(s0)
	slli t0, a5, 51
	srai t0, t0, 63
	ld a6, 448(s0)
	xor t0, t0, a6
	slli t1, a5, 50
	srai t1, t1, 63
	ld a6, 16(s0)
	xor t1, t1, a6
	slli t2, a5, 49
	srai t2, t2, 63
	ld a6, 80(s0)
	xor t2, t2, a6
	slli t3, a5, 48
	srai t3, t3, 63
	ld a6, 144(s0)
	xor t3, t3, a6
	slli t4, a5, 47
	srai t4, t4, 63
	ld a6, 208(s0)
	xor t4, t4, a6
	slli t5, a5, 46
	srai t5, t5, 63
	ld a6, 272(s0)
	xor t5, t5, a6
	xor t6, t4, t1
	or a0, t4, t0
	and a0, t5, a0
	xor t6, t6, a0
	xor a7, t0, t6
	or s1, t1, a7
	xor s1, s1, a7
	and a7, t5, a7
	xor s2, t4, a7
	xor s3, t5, t3
	or s4, s2, s3
	xor s5, t6, s4
	and s6, t3, s5
	or s7, s6, t0
	xor s7, s7, t0
	or s2, s1, s2
	xor s8, s7, s2
	and s9, s8, t2
	xor s9, s9, s5
	xor s4, t4, s4
	or s10, t0, s4
	xor s10, s10, s4
	xor t3, t3, s10
	or s10, t1, s6
	xor s10, s10, s6
	or s10, t3, s10
	or t4, t4, s3
	xor s8, s8, t4
	or a0, a0, s10
	xor s8, s8, a0
	or s5, t5, s5
	and s2, s2, s5
	xor s2, t3, s2
	xori s7, s7, -1
	and s7, s7, s2
	or s1, s1, t2
	xor s1, s1, s7
	xor t6, t6, s2
	or t1, t1, t6
	xor t1, t1, t6
	xori t4, t4, -1
	xor s4, s4, t4
	xor t1, t1, s4
	or t1, t1, t2
	xor t1, t1, t2
	xor t1, t1, s8
	xor t0, t0, a7
	xor t5, t5, t3
	and t0, t0, t5
	xor s6, s6, s4
	xor t0, t0, s6
	or s10, s10, t2
	xor s10, s10, t2
	xor s10, s10, t0
	ld a6, 344(s0)
	xor a6, a6, s9
	sd a6, 344(s0)
	ld a6, 360(s0)
	xor a6, a6, s1
	sd a6, 360(s0)
	ld a6, 200(s0)
	xor a6, a6, t1
	sd a6, 200(s0)
	ld a6, 312(s0)
	xor a6, a6, s10
	sd a6, 312(s0)
	slli t0, a5, 57
	srai t0, t0, 63
	ld a6, 192(s0)
	xor t0, t0, a6
	slli t1, a5, 56
	srai t1, t1, 63
	ld a6, 256(s0)
	xor t1, t1, a6
	slli t2, a5, 55
	srai t2, t2, 63
	ld a6, 320(s0)
	xor t2, t2, a6
	slli t3, a5, 54
	srai t3, t3, 63
	ld a6, 384(s0)
	xor t3, t3, a6
	slli t4, a5, 53
	srai t4, t4, 63
	ld a6, 448(s0)
	xor t4, t4, a6
	slli t5, a5, 52
	srai t5, t5, 63
	ld a6, 16(s0)
	xor t5, t5, a6
	xor t6, t2, t1
	xor a0, t3, t6
	and a7, t0, a0
	and s1, t2, t6
	xor s2, t4, s1
	and s3, a7, s2
	and s4, t0, s1
	xor s5, t3, s4
	or s6, s2, s5
	xor t6, t0, t6
	xor s7, s6, t6
	or s8, t5, s3
	xor s8, s8, s3
	xor s8, s8, s7
	xori a0, a0, -1
	and a0, a0, t1
	or s7, s2, a0
	xor s5, a7, s5
	xor s7, s7, s5
	xor a7, a7, t6
	or t2, t2, a7
	xor t2, t2, a7
	or t6, s2, t2
	xor t6, t6, t2
	xor t1, t1, s5
	xor t6, t6, t1
	or a7, a7, s4
	xor a7, a7, s4
	or t2, t2, a7
	xor s6, t4, s6
	and s6, t6, s6
	xor s6, t2, s6
	and s4, s6, t5
	xor s4, s4, t6
	or s2, s2, t3
	xor s2, s2, t3
	or a7, a7, s2
	or s1, s1, t6
	and a7, a7, s1
	xor s6, s6, a7
	xor a0, a0, t2
	and t0, t0, a0
	or s3, s3, t0
	xor a7, a7, s3
	or t0, a7, t5
	xor t0, t0, t5
	xor t0, t0, s7
	and t4, t4, s3
	xori s7, s7, -1
	xor t4, t4, s7
	xor a7, a7, t4
	or s6, s6, t5
	xor s6, s6, a7
	ld a6, 120(s0)
	xor a6, a6, s8
	sd a6, 120(s0)
	ld a6, 152(s0)
	xor a6, a6, s4
	sd a6, 152(s0)
	ld a6, 296(s0)
	xor a6, a6, s6
	sd a6, 296(s0)
	ld a6, 8(s0)
	xor a6, a6, t0
	sd a6, 8(s0)
	slli t0, a5, 63
	srai t0, t0, 63
	ld a6, 496(s0)
	xor t0, t0, a6
	slli t1, a5, 62
	srai t1, t1, 63
	ld a6, 0(s0)
	xor t1, t1, a6
	slli t2, a5, 61
	srai t2, t2, 63
	ld a6, 64(s0)
	xor t2, t2, a6
	slli t3, a5, 60
	srai t3, t3, 63
	ld a6, 128(s0)
	xor t3, t3, a6
	slli t4, a5, 59
	srai t4, t4, 63
	ld a6, 192(s0)
	xor t4, t4, a6
	slli t5, a5, 58
	srai t5, t5, 63
	ld a6, 256(s0)
	xor t5, t5, a6
	or t6, t3, t4
	xor t6, t6, t4
	or a0, t1, t3
	xor a0, a0, t3
	xor a0, t2, a0
	and a7, t5, a0
	or s1, a7, t6
	xor s1, s1, t6
	or s2, t4, a0
	xor s2, s2, a0
	or s3, t5, s2
	or s4, t4, t3
	xor s4, s4, t3
	xor s4, t1, s4
	and s5, s3, s4
	or a7, a7, s5
	xori a0, a0, -1
	xor s5, s5, a0
	or t3, t3, s3
	xor t3, t3, s3
	xor s5, s5, t3
	xor t6, t6, s5
	or t3, s1, t0
	xor t3, t3, t6
	xor t6, t5, t6
	and s3, t1, t6
	xor s5, t4, s5
	xor s3, s3, s5
	xor s2, s2, s3
	xor s3, a7, s3
	or t4, t4, s3
	xor t1, t1, t6
	xor t4, t4, t1
	and a7, a7, t0
	xor a7, a7, t4
	xor s4, s4, s2
	or s5, t2, s5
	xor s5, s4, s5
	xor t5, t5, s5
	and t5, t5, t0
	xor t5, t5, s2
	or s4, s4, t2
	xor s4, s4, t2
	and t4, t4, s4
	xor s1, s1, s5
	xor t4, t4, s1
	or t4, t4, t0
	xor t4, t4, s2
	ld a6, 216(s0)
	xor a6, a6, t5
	sd a6, 216(s0)
	ld a6, 104(s0)
	xor a6, a6, a7
	sd a6, 104(s0)
	ld a6, 328(s0)
	xor a6, a6, t3
	sd a6, 328(s0)
	ld a6, 248(s0)
	xor a6, a6, t4
	sd a6, 248(s0)
	addi a4, a4, -1
	bnez a4, 27b
	ld t0, 0(s0)
	ld t1, 8(s0)
	sd t1, 0(s0)
	sd t0, 8(s0)
	ld t0, 64(s0)
	ld t1, 72(s0)
	sd t1, 64(s0)
	sd t0, 72(s0)
	ld t0, 128(s0)
	ld t1, 136(s0)
	sd t1, 128(s0)
	sd t0, 136(s0)
	ld t0, 192(s0)
	ld t1, 200(s0)
	sd t1, 192(s0)
	sd t0, 200(s0)
	ld t0, 256(s0)
	ld t1, 264(s0)
	sd t1, 256(s0)
	sd t0, 264(s0)
	ld t0, 320(s0)
	ld t1, 328(s0)
	sd t1, 320(s0)
	sd t0, 328(s0)
	ld t0, 384(s0)
	ld t1, 392(s0)
	sd t1, 384(s0)
	sd t0, 392(s0)
	ld t0, 448(s0)
	ld t1, 456(s0)
	sd t1, 448(s0)
	sd t0, 456(s0)
	ld t0, 16(s0)
	ld t1, 24(s0)
	sd t1, 16(s0)
	sd t0, 24(s0)
	ld t0, 80(s0)
	ld t1, 88(s0)
	sd t1, 80(s0)
	sd t0, 88(s0)
	ld t0, 144(s0)
	ld t1, 152(s0)
	sd t1, 144(s0)
	sd t0, 152(s0)
	ld t0, 208(s0)
	ld t1, 216(s0)
	sd t1, 208(s0)
	sd t0, 216(s0)
	ld t0, 272(s0)
	ld t1, 280(s0)
	sd t1, 272(s0)
	sd t0, 280(s0)
	ld t0, 336(s0)
	ld t1, 344(s0)
	sd t1, 336(s0)
	sd t0, 344(s0)
	ld t0, 400(s0)
	ld t1, 408(s0)
	sd t1, 400(s0)
	sd t0, 408(s0)
	ld t0, 464(s0)
	ld t1, 472(s0)
	sd t1, 464(s0)
	sd t0, 472(s0)
	ld t0, 32(s0)
	ld t1, 40(s0)
	sd t1, 32(s0)
	sd t0, 40(s0)
	ld t0, 96(s0)
	ld t1, 104(s0)
	sd t1, 96(s0)
	sd t0, 104(s0)
	ld t0, 160(s0)
	ld t1, 168(s0)
	sd t1, 160(s0)
	sd t0, 168(s0)
	ld t0, 224(s0)
	ld t1, 232(s0)
	sd t1, 224(s0)
	sd t0, 232(s0)
	ld t0, 288(s0)
	ld t1, 296(s0)
	sd t1, 288(s0)
	sd t0, 296(s0)
	ld t0, 352(s0)
	ld t1, 360(s0)
	sd t1, 352(s0)
	sd t0, 360(s0)
	ld t0, 416(s0)
	ld t1, 424(s0)
	sd t1, 416(s0)
	sd t0, 424(s0)
	ld t0, 480(s0)
	ld t1, 488(s0)
	sd t1, 480(s0)
	sd t0, 488(s0)
	ld t0, 48(s0)
	ld t1, 56(s0)
	sd t1, 48(s0)
	sd t0, 56(s0)
	ld t0, 112(s0)
	ld t1, 120(s0)
	sd t1, 112(s0)
	sd t0, 120(s0)
	ld t0, 176(s0)
	ld t1, 184(s0)
	sd t1, 176(s0)
	sd t0, 184(s0)
	ld t0, 240(s0)
	ld t1, 248(s0)
	sd t1, 240(s0)
	sd t0, 248(s0)
	ld t0, 304(s0)
	ld t1, 312(s0)
	sd t1, 304(s0)
	sd t0, 312(s0)
	ld t0, 368(s0)
	ld t1, 376(s0)
	sd t1, 368(s0)
	sd t0, 376(s0)
	ld t0, 432(s0)
	ld t1, 440(s0)
	sd t1, 432(s0)
	sd t0, 440(s0)
	ld t0, 496(s0)
	ld t1, 504(s0)
	sd t1, 496(s0)
	sd t0, 504(s0)
	addi a3, s0, 760
	addi a4, zero, 8
28:
	ld a5, 0(a3)
	addi a3, a3, -8
	slli t0, a5, 21
	srai t0, t0, 63
	ld a6, 248(s0)
	xor t0, t0, a6
	slli t1, a5, 20
	srai t1, t1, 63
	ld a6, 312(s0)
	xor t1, t1, a6
	slli t2, a5, 19
	srai t2, t2, 63
	ld a6, 376(s0)
	xor t2, t2, a6
	slli t3, a5, 18
	srai t3, t3, 63
	ld a6, 440(s0)
	xor t3, t3, a6
	slli t4, a5, 17
	srai t4, t4, 63
	ld a6, 504(s0)
	xor t4, t4, a6
	slli t5, a5, 16
	srai t5, t5, 63
	ld a6, 8(s0)
	xor t5, t5, a6
	or t6, t5, t1
	xor t6, t6, t1
	xor a0, t2, t6
	or a7, t3, t0
	xor s1, t5, t3
	and s2, a7, s1
	xor s3, t2, s2
	or s4, s3, a0
	xor s4, s4, a0
	xor s5, t1, t0
	xor s6, t3, s5
	xori s6, s6, -1
	and s6, s6, a0
	or s2, t0, s2
	xor s6, s6, s2
	or s2, s6, s4
	xor s2, s2, s4
	or t0, t5, t0
	or s7, s6, t0
	xori s3, s3, -1
	and s3, s3, t1
	xor s8, s7, s3
	or t2, t2, t0
	xor t2, t2, t0
	xor t2, s3, t2
	xori s1, s1, -1
	and s1, s1, s5
	or t2, t2, s1
	or t3, t3, t6
	xor t3, t3, t6
	xor t6, a0, s7
	or t6, t6, t3
	xor t6, t6, t3
	xori t3, t6, -1
	and s6, a7, s6
	xor t3, t3, s6
	or s8, s8, t4
	xor s8, s8, t4
	xor s8, s8, t3
	xor t6, s5, t6
	or s3, s3, t6
	xor s3, a7, s3
	xor t5, t5, s3
	xor t3, t3, t5
	or s4, s4, t4
	xor s4, s4, t3
	xor a7, a7, s7
	or a7, t2, a7
	xor a7, t5, a7
	or s5, s5, t3
	xor s5, a7, s5
	or t3, s2, t4
	xor t3, t3, s5
	or t1, t1, a0
	or t1, t1, a7
	xor t1, t1, a7
	and s2, s2, t5
	xor t1, t1, s2
	or t1, t1, t4
	xor t1, t1, t2
	ld a6, 64(s0)
	xor a6, a6, t1
	sd a6, 64(s0)
	ld a6, 80(s0)
	xor a6, a6, s8
	sd a6, 80(s0)
	ld a6, 464(s0)
	xor a6, a6, t3
	sd a6, 464(s0)
	ld a6, 480(s0)
	xor a6, a6, s4
	sd a6, 480(s0)
	slli t0, a5, 27
	srai t0, t0, 63
	ld a6, 488(s0)
	xor t0, t0, a6
	slli t1, a5, 26
	srai t1, t1, 63
	ld a6, 56(s0)
	xor t1, t1, a6
	slli t2, a5, 25
	srai t2, t2, 63
	ld a6, 120(s0)
	xor t2, t2, a6
	slli t3, a5, 24
	srai t3, t3, 63
	ld a6, 184(s0)
	xor t3, t3, a6
	slli t4, a5, 23
	srai t4, t4, 63
	ld a6, 248(s0)
	xor t4, t4, a6
	slli t5, a5, 22
	srai t5, t5, 63
	ld a6, 312(s0)
	xor t5, t5, a6
	xor t6, t4, t1
	or a0, t5, t0
	xor a0, a0, t0
	xori a0, a0, -1
	and a0, a0, t1
	or a7, t4, a0
	or s1, t6, t0
	xor s1, s1, t0
	and s2, t5, t6
	xor t1, t1, s2
	or s2, t1, s1
	xor s2, s2, s1
	and s3, t3, t0
	xor a0, a0, s1
	and a0, a7, a0
	or s1, a0, s3
	xor s1, s1, s3
	and s4, t3, a0
	xori t5, t5, -1
	xor t5, s4, t5
	xor t0, t0, t6
	or s5, t0, s3
	xor s5, s5, s3
	xor s6, t5, s5
	xori s1, s1, -1
	and s1, s1, t2
	xor s1, s1, s6
	or t4, t4, s5
	xor t4, t4, s5
	xor t1, t1, t4
	or t5, t5, t1
	xor t5, t5, t1
	xor t3, t3, t0
	xor t5, t5, t3
	or s5, a7, t2
	xor s5, s5, t2
	xor s5, s5, t5
	xor s4, s4, t4
	or t3, t3, s4
	xor a7, a7, s6
	or s3, s3, a7
	xor s4, t3, s3
	xor a0, a0, s6
	xor t5, t5, a0
	and s3, s3, t5
	and t6, t6, t3
	xor s3, s3, t6
	or t6, s3, t2
	xor t6, t6, s4
	or s3, s3, t1
	xor s3, s3, t1
	or t0, t0, a7
	xor s3, s3, t0
	or s2, s2, t2
	xor s2, s2, s3
	ld a6, 400(s0)
	xor a6, a6, s2
	sd a6, 400(s0)
	ld a6, 432(s0)
	xor a6, a6, t6
	sd a6, 432(s0)
	ld a6, 256(s0)
	xor a6, a6, s1
	sd a6, 256(s0)
	ld a6, 224(s0)
	xor a6, a6, s5
	sd a6, 224(s0)
	slli t0, a5, 33
	srai t0, t0, 63
	ld a6, 232(s0)
	xor t0, t0, a6
	slli t1, a5, 32
	srai t1, t1, 63
	ld a6, 296(s0)
	xor t1, t1, a6
	slli t2, a5, 31
	srai t2, t2, 63
	ld a6, 360(s0)
	xor t2, t2, a6
	slli t3, a5, 30
	srai t3, t3, 63
	ld a6, 424(s0)
	xor t3, t3, a6
	slli t4, a5, 29
	srai t4, t4, 63
	ld a6, 488(s0)
	xor t4, t4, a6
	slli t5, a5, 28
	srai t5, t5, 63
	ld a6, 56(s0)
	xor t5, t5, a6
	or t6, t5, t4
	xor t6, t6, t4
	xor a0, t3, t0
	or a7, t6, a0
	xor s1, t2, t0
	or s2, s1, t5
	xor s2, s2, t5
	xor s3, a7, s2
	xor s4, t4, a0
	or s5, s4, t0
	xor s5, s5, t0
	xor a7, a7, s5
	or s5, s3, a7
	xor s5, s5, a7
	and s6, t0, s3
	or s6, t2, s6
	and s6, t5, s6
	xor s6, s4, s6
	or s7, s3, t1
	xor s7, s7, t1
	xor s7, s7, s6
	and a0, a0, s1
	xor s1, t5, t2
	xor s8, a7, s1
	or s8, t3, s8
	or s8, s8, a0
	xor s8, s8, a0
	or s2, s2, s1
	or s1, s6, s2
	xor s1, s1, s2
	and t0, t2, t0
	or a0, t0, t4
	xor a0, a0, t4
	xor s1, s1, a0
	and a7, a7, s1
	or t0, s4, t0
	or t0, t0, a7
	xor t0, t0, a7
	xor t5, t5, t0
	and s8, s8, t1
	xor s8, s8, t5
	xori s3, s3, -1
	or t4, t4, s3
	or t3, t3, t4
	xor s4, s4, t3
	xor s2, s2, s4
	xori s5, s5, -1
	and s5, s5, t1
	xor s5, s5, s2
	and t2, t2, s3
	xor s6, s6, t2
	or s4, s4, s6
	xor t6, t6, t5
	xor s4, s4, t6
	or s1, s1, t1
	xor s1, s1, s4
	ld a6, 176(s0)
	xor a6, a6, s7
	sd a6, 176(s0)
	ld a6, 128(s0)
	xor a6, a6, s1
	sd a6, 128(s0)
	ld a6, 32(s0)
	xor a6, a6, s8
	sd a6, 32(s0)
	ld a6, 16(s0)
	xor a6, a6, s5
	sd a6, 16(s0)
	slli t0, a5, 39
	srai t0, t0, 63
	ld a6, 472(s0)
	xor t0, t0, a6
	slli t1, a5, 38
	srai t1, t1, 63
	ld a6, 40(s0)
	xor t1, t1, a6
	slli t2, a5, 37
	srai t2, t2, 63
	ld a6, 104(s0)
	xor t2, t2, a6
	slli t3, a5, 36
	srai t3, t3, 63
	ld a6, 168(s0)
	xor t3, t3, a6
	slli t4, a5, 35
	srai t4, t4, 63
	ld a6, 232(s0)
	xor t4, t4, a6
	slli t5, a5, 34
	srai t5, t5, 63
	ld a6, 296(s0)
	xor t5, t5, a6
	xor t5, t5, t3
	xor t3, t3, t1
	or t6, t4, t2
	xor t6, t1, t6
	xori t6, t6, -1
	and t6, t6, t3
	or a0, t3, t4
	xor a0, a0, t4
	xor a7, t2, a0
	or s1, t5, a7
	or s1, s1, t6
	xor s1, s1, t6
	xor s2, t4, s1
	and a7, a7, s2
	or t3, t3, a7
	xor t3, t3, a7
	xor t5, t5, s2
	xori t3, t3, -1
	and t3, t3, t5
	xor t6, t6, t3
	xor t4, t4, t2
	or t1, t1, a0
	xor t5, t5, t1
	or t1, t5, t4
	xor t1, t1, t4
	xor s1, s1, t1
	or t1, t0, t6
	xor t1, t1, t6
	xor t1, t1, s1
	xori s1, s1, -1
	or a0, t6, t0
	xor a0, a0, t0
	xor a0, a0, s1
	xor t6, t6, s1
	or t6, t6, t4
	xor t6, t6, t4
	or a7, a7, t6
	xor t5, t5, a7
	or a7, s2, t0
	xor a7, a7, t5
	and t0, t0, s2
	xor t0, t0, t5
	ld a6, 496(s0)
	xor a6, a6, t0
	sd a6, 496(s0)
	ld a6, 416(s0)
	xor a6, a6, a7
	sd a6, 416(s0)
	ld a6, 272(s0)
	xor a6, a6, a0
	sd a6, 272(s0)
	ld a6, 384(s0)
	xor a6, a6, t1
	sd a6, 384(s0)
	slli t0, a5, 45
	srai t0, t0, 63
	ld a6, 216(s0)
	xor t0, t0, a6
	slli t1, a5, 44
	srai t1, t1, 63
	ld a6, 280(s0)
	xor t1, t1, a6
	slli t2, a5, 43
	srai t2, t2, 63
	ld a6, 344(s0)
	xor t2, t2, a6
	slli t3, a5, 42
	srai t3, t3, 63
	ld a6, 408(s0)
	xor t3, t3, a6
	slli t4, a5, 41
	srai t4, t4, 63
	ld a6, 472(s0)
	xor t4, t4, a6
	slli t5, a5, 40
	srai t5, t5, 63
	ld a6, 40(s0)
	xor t5, t5, a6
	or t6, t5, t3
	or a0, t6, t0
	xor a0, a0, t0
	xor a7, t5, a0
	xor s1, t3, a7
	or s2, t2, s1
	or a0, a0, t2
	xor a0, a0, t2
	xor t3, t3, a0
	and a0, t1, t3
	or s1, t5, s1
	xor a0, a0, s1
	xor a0, t2, a0
	xor t0, t0, a0
	or s3, a7, t0
	and s4, t1, s3
	xor s5, a7, s4
	and s6, t2, s1
	xor s5, s5, s6
	or s3, s3, t5
	xor s3, s3, t5
	xor s6, t3, s3
	xor t1, t1, s2
	xori s6, s6, -1
	and s6, s6, t1
	xori s6, s6, -1
	or s6, s6, t4
	xor s6, s6, t4
	xor s6, s6, a0
	or a0, t3, s4
	xor a0, a0, s4
	xor s3, s3, t1
	or s3, s5, s3
	or s3, s3, a0
	xor s3, s3, a0
	or a0, s2, s3
	xor a0, a0, s3
	and t0, t0, s3
	xor t1, t1, t0
	and s1, t3, s1
	or s1, t1, s1
	xor s4, s4, s1
	and s4, s4, t4
	xor s4, s4, s5
	xor t5, t5, t6
	xor s3, s3, t5
	and t2, t2, t1
	xor s3, s3, t2
	or a0, a0, t4
	xor a0, a0, s3
	xor t3, s2, t3
	or t3, t3, s3
	xor t3, t3, s3
	xor a7, a7, t1
	xor t3, t3, a7
	and s2, s2, t4
	xor s2, s2, t3
	ld a6, 368(s0)
	xor a6, a6, s4
	sd a6, 368(s0)
	ld a6, 448(s0)
	xor a6, a6, s6
	sd a6, 448(s0)
	ld a6, 160(s0)
	xor a6, a6, s2
	sd a6, 160(s0)
	ld a6, 48(s0)
	xor a6, a6, a0
	sd a6, 48(s0)
	slli t0, a5, 51
	srai t0, t0, 63
	ld a6, 456(s0)
	xor t0, t0, a6
	slli t1, a5, 50
	srai t1, t1, 63
	ld a6, 24(s0)
	xor t1, t1, a6
	slli t2, a5, 49
	srai t2, t2, 63
	ld a6, 88(s0)
	xor t2, t2, a6
	slli t3, a5, 48
	srai t3, t3, 63
	ld a6, 152(s0)
	xor t3, t3, a6
	slli t4, a5, 47
	srai t4, t4, 63
	ld a6, 216(s0)
	xor t4, t4, a6
	slli t5, a5, 46
	srai t5, t5, 63
	ld a6, 280(s0)
	xor t5, t5, a6
	xor t6, t4, t1
	or a0, t4, t0
	and a0, t5, a0
	xor t6, t6, a0
	xor a7, t0, t6
	or s1, t1, a7
	xor s1, s1, a7
	and a7, t5, a7
	xor s2, t4, a7
	xor s3, t5, t3
	or s4, s2, s3
	xor s5, t6, s4
	and s6, t3, s5
	or s7, s6, t0
	xor s7, s7, t0
	or s2, s1, s2
	xor s8, s7, s2
	and s9, s8, t2
	xor s9, s9, s5
	xor s4, t4, s4
	or s10, t0, s4
	xor s10, s10, s4
	xor t3, t3, s10
	or s10, t1, s6
	xor s10, s10, s6
	or s10, t3, s10
	or t4, t4, s3
	xor s8, s8, t4
	or a0, a0, s10
	xor s8, s8, a0
	or s5, t5, s5
	and s2, s2, s5
	xor s2, t3, s2
	xori s7, s7, -1
	and s7, s7, s2
	or s1, s1, t2
	xor s1, s1, s7
	xor t6, t6, s2
	or t1, t1, t6
	xor t1, t1, t6
	xori t4, t4, -1
	xor s4, s4, t4
	xor t1, t1, s4
	or t1, t1, t2
	xor t1, t1, t2
	xor t1, t1, s8
	xor t0, t0, a7
	xor t5, t5, t3
	and t0, t0, t5
	xor s6, s6, s4
	xor t0, t0, s6
	or s10, s10, t2
	xor s10, s10, t2
	xor s10, s10, t0
	ld a6, 336(s0)
	xor a6, a6, s9
	sd a6, 336(s0)
	ld a6, 352(s0)
	xor a6, a6, s1
	sd a6, 352(s0)
	ld a6, 192(s0)
	xor a6, a6, t1
	sd a6, 192(s0)
	ld a6, 304(s0)
	xor a6, a6, s10
	sd a6, 304(s0)
	slli t0, a5, 57
	srai t0, t0, 63
	ld a6, 200(s0)
	xor t0, t0, a6
	slli t1, a5, 56
	srai t1, t1, 63
	ld a6, 264(s0)
	xor t1, t1, a6
	slli t2, a5, 55
	srai t2, t2, 63
	ld a6, 328(s0)
	xor t2, t2, a6
	slli t3, a5, 54
	srai t3, t3, 63
	ld a6, 392(s0)
	xor t3, t3, a6
	slli t4, a5, 53
	srai t4, t4, 63
	ld a6, 456(s0)
	xor t4, t4, a6
	slli t5, a5, 52
	srai t5, t5, 63
	ld a6, 24(s0)
	xor t5, t5, a6
	xor t6, t2, t1
	xor a0, t3, t6
	and a7, t0, a0
	and s1, t2, t6
	xor s2, t4, s1
	and s3, a7, s2
	and s4, t0, s1
	xor s5, t3, s4
	or s6, s2, s5
	xor t6, t0, t6
	xor s7, s6, t6
	or s8, t5, s3
	xor s8, s8, s3
	xor s8, s8, s7
	xori a0, a0, -1
	and a0, a0, t1
	or s7, s2, a0
	xor s5, a7, s5
	xor s7, s7, s5
	xor a7, a7, t6
	or t2, t2, a7
	xor t2, t2, a7
	or t6, s2, t2
	xor t6, t6, t2
	xor t1, t1, s5
	xor t6, t6, t1
	or a7, a7, s4
	xor a7, a7, s4
	or t2, t2, a7
	xor s6, t4, s6
	and s6, t6, s6
	xor s6, t2, s6
	and s4, s6, t5
	xor s4, s4, t6
	or s2, s2, t3
	xor s2, s2, t3
	or a7, a7, s2
	or s1, s1, t6
	and a7, a7, s1
	xor s6, s6, a7
	xor a0, a0, t2
	and t0, t0, a0
	or s3, s3, t0
	xor a7, a7, s3
	or t0, a7, t5
	xor t0, t0, t5
	xor t0, t0, s7
	and t4, t4, s3
	xori s7, s7, -1
	xor t4, t4, s7
	xor a7, a7, t4
	or s6, s6, t5
	xor s6, s6, a7
	ld a6, 112(s0)
	xor a6, a6, s8
	sd a6, 112(s0)
	ld a6, 144(s0)
	xor a6, a6, s4
	sd a6, 144(s0)
	ld a6, 288(s0)
	xor a6, a6, s6
	sd a6, 288(s0)
	ld a6, 0(s0)
	xor a6, a6, t0
	sd a6, 0(s0)
	slli t0, a5, 63
	srai t0, t0, 63
	ld a6, 504(s0)
	xor t0, t0, a6
	slli t1, a5, 62
	srai t1, t1, 63
	ld a6, 8(s0)
	xor t1, t1, a6
	slli t2, a5, 61
	srai t2, t2, 63
	ld a6, 72(s0)
	xor t2, t2, a6
	slli t3, a5, 60
	srai t3, t3, 63
	ld a6, 136(s0)
	xor t3, t3, a6
	slli t4, a5, 59
	srai t4, t4, 63
	ld a6, 200(s0)
	xor t4, t4, a6
	slli t5, a5, 58
	srai t5, t5, 63
	ld a6, 264(s0)
	xor t5, t5, a6
	or t6, t3, t4
	xor t6, t6, t4
	or a0, t1, t3
	xor a0, a0, t3
	xor a0, t2, a0
	and a7, t5, a0
	or s1, a7, t6
	xor s1, s1, t6
	or s2, t4, a0
	xor s2, s2, a0
	or s3, t5, s2
	or s4, t4, t3
	xor s4, s4, t3
	xor s4, t1, s4
	and s5, s3, s4
	or a7, a7, s5
	xori a0, a0, -1
	xor s5, s5, a0
	or t3, t3, s3
	xor t3, t3, s3
	xor s5, s5, t3
	xor t6, t6, s5
	or t3, s1, t0
	xor t3, t3, t6
	xor t6, t5, t6
	and s3, t1, t6
	xor s5, t4, s5
	xor s3, s3, s5
	xor s2, s2, s3
	xor s3, a7, s3
	or t4, t4, s3
	xor t1, t1, t6
	xor t4, t4, t1
	and a7, a7, t0
	xor a7, a7, t4
	xor s4, s4, s2
	or s5, t2, s5
	xor s5, s4, s5
	xor t5, t5, s5
	and t5, t5, t0
	xor t5, t5, s2
	or s4, s4, t2
	xor s4, s4, t2
	and t4, t4, s4
	xor s1, s1, s5
	xor t4, t4, s1
	or t4, t4, t0
	xor t4, t4, s2
	ld a6, 208(s0)
	xor a6, a6, t5
	sd a6, 208(s0)
	ld a6, 96(s0)
	xor a6, a6, a7
	sd a6, 96(s0)
	ld a6, 320(s0)
	xor a6, a6, t3
	sd a6, 320(s0)
	ld a6, 240(s0)
	xor a6, a6, t4
	sd a6, 240(s0)
	ld a5, 0(a3)
	addi a3, a3, -8
	slli t0, a5, 21
	srai t0, t0, 63
	ld a6, 240(s0)
	xor t0, t0, a6
	slli t1, a5, 20
	srai t1, t1, 63
	ld a6, 304(s0)
	xor t1, t1, a6
	slli t2, a5, 19
	srai t2, t2, 63
	ld a6, 368(s0)
	xor t2, t2, a6
	slli t3, a5, 18
	srai t3, t3, 63
	ld a6, 432(s0)
	xor t3, t3, a6
	slli t4, a5, 17
	srai t4, t4, 63
	ld a6, 496(s0)
	xor t4, t4, a6
	slli t5, a5, 16
	srai t5, t5, 63
	ld a6, 0(s0)
	xor t5, t5, a6
	or t6, t5, t1
	xor t6, t6, t1
	xor a0, t2, t6
	or a7, t3, t0
	xor s1, t5, t3
	and s2, a7, s1
	xor s3, t2, s2
	or s4, s3, a0
	xor s4, s4, a0
	xor s5, t1, t0
	xor s6, t3, s5
	xori s6, s6, -1
	and s6, s6, a0
	or s2, t0, s2
	xor s6, s6, s2
	or s2, s6, s4
	xor s2, s2, s4
	or t0, t5, t0
	or s7, s6, t0
	xori s3, s3, -1
	and s3, s3, t1
	xor s8, s7, s3
	or t2, t2, t0
	xor t2, t2, t0
	xor t2, s3, t2
	xori s1, s1, -1
	and s1, s1, s5
	or t2, t2, s1
	or t3, t3, t6
	xor t3, t3, t6
	xor t6, a0, s7
	or t6, t6, t3
	xor t6, t6, t3
	xori t3, t6, -1
	and s6, a7, s6
	xor t3, t3, s6
	or s8, s8, t4
	xor s8, s8, t4
	xor s8, s8, t3
	xor t6, s5, t6
	or s3, s3, t6
	xor s3, a7, s3
	xor t5, t5, s3
	xor t3, t3, t5
	or s4, s4, t4
	xor s4, s4, t3
	xor a7, a7, s7
	or a7, t2, a7
	xor a7, t5, a7
	or s5, s5, t3
	xor s5, a7, s5
	or t3, s2, t4
	xor t3, t3, s5
	or t1, t1, a0
	or t1, t1, a7
	xor t1, t1, a7
	and s2, s2, t5
	xor t1, t1, s2
	or t1, t1, t4
	xor t1, t1, t2
	ld a6, 72(s0)
	xor a6, a6, t1
	sd a6, 72(s0)
	ld a6, 88(s0)
	xor a6, a6, s8
	sd a6, 88(s0)
	ld a6, 472(s0)
	xor a6, a6, t3
	sd a6, 472(s0)
	ld a6, 488(s0)
	xor a6, a6, s4
	sd a6, 488(s0)
	slli t0, a5, 27
	srai t0, t0, 63
	ld a6, 480(s0)
	xor t0, t0, a6
	slli t1, a5, 26
	srai t1, t1, 63
	ld a6, 48(s0)
	xor t1, t1, a6
	slli t2, a5, 25
	srai t2, t2, 63
	ld a6, 112(s0)
	xor t2, t2, a6
	slli t3, a5, 24
	srai t3, t3, 63
	ld a6, 176(s0)
	xor t3, t3, a6
	slli t4, a5, 23
	srai t4, t4, 63
	ld a6, 240(s0)
	xor t4, t4, a6
	slli t5, a5, 22
	srai t5, t5, 63
	ld a6, 304(s0)
	xor t5, t5, a6
	xor t6, t4, t1
	or a0, t5, t0
	xor a0, a0, t0
	xori a0, a0, -1
	and a0, a0, t1
	or a7, t4, a0
	or s1, t6, t0
	xor s1, s1, t0
	and s2, t5, t6
	xor t1, t1, s2
	or s2, t1, s1
	xor s2, s2, s1
	and s3, t3, t0
	xor a0, a0, s1
	and a0, a7, a0
	or s1, a0, s3
	xor s1, s1, s3
	and s4, t3, a0
	xori t5, t5, -1
	xor t5, s4, t5
	xor t0, t0, t6
	or s5, t0, s3
	xor s5, s5, s3
	xor s6, t5, s5
	xori s1, s1, -1
	and s1, s1, t2
	xor s1, s1, s6
	or t4, t4, s5
	xor t4, t4, s5
	xor t1, t1, t4
	or t5, t5, t1
	xor t5, t5, t1
	xor t3, t3, t0
	xor t5, t5, t3
	or s5, a7, t2
	xor s5, s5, t2
	xor s5, s5, t5
	xor s4, s4, t4
	or t3, t3, s4
	xor a7, a7, s6
	or s3, s3, a7
	xor s4, t3, s3
	xor a0, a0, s6
	xor t5, t5, a0
	and s3, s3, t5
	and t6, t6, t3
	xor s3, s3, t6
	or t6, s3, t2
	xor t6, t6, s4
	or s3, s3, t1
	xor s3, s3, t1
	or t0, t0, a7
	xor s3, s3, t0
	or s2, s2, t2
	xor s2, s2, s3
	ld a6, 408(s0)
	xor a6, a6, s2
	sd a6, 408(s0)
	ld a6, 440(s0)
	xor a6, a6, t6
	sd a6, 440(s0)
	ld a6, 264(s0)
	xor a6, a6, s1
	sd a6, 264(s0)
	ld a6, 232(s0)
	xor a6, a6, s5
	sd a6, 232(s0)
	slli t0, a5, 33
	srai t0, t0, 63
	ld a6, 224(s0)
	xor t0, t0, a6
	slli t1, a5, 32
	srai t1, t1, 63
	ld a6, 288(s0)
	xor t1, t1, a6
	slli t2, a5, 31
	srai t2, t2, 63
	ld a6, 352(s0)
	xor t2, t2, a6
	slli t3, a5, 30
	srai t3, t3, 63
	ld a6, 416(s0)
	xor t3, t3, a6
	slli t4, a5, 29
	srai t4, t4, 63
	ld a6, 480(s0)
	xor t4, t4, a6
	slli t5, a5, 28
	srai t5, t5, 63
	ld a6, 48(s0)
	xor t5, t5, a6
	or t6, t5, t4
	xor t6, t6, t4
	xor a0, t3, t0
	or a7, t6, a0
	xor s1, t2, t0
	or s2, s1, t5
	xor s2, s2, t5
	xor s3, a7, s2
	xor s4, t4, a0
	or s5, s4, t0
	xor s5, s5, t0
	xor a7, a7, s5
	or s5, s3, a7
	xor s5, s5, a7
	and s6, t0, s3
	or s6, t2, s6
	and s6, t5, s6
	xor s6, s4, s6
	or s7, s3, t1
	xor s7, s7, t1
	xor s7, s7, s6
	and a0, a0, s1
	xor s1, t5, t2
	xor s8, a7, s1
	or s8, t3, s8
	or s8, s8, a0
	xor s8, s8, a0
	or s2, s2, s1
	or s1, s6, s2
	xor s1, s1, s2
	and t0, t2, t0
	or a0, t0, t4
	xor a0, a0, t4
	xor s1, s1, a0
	and a7, a7, s1
	or t0, s4, t0
	or t0, t0, a7
	xor t0, t0, a7
	xor t5, t5, t0
	and s8, s8, t1
	xor s8, s8, t5
	xori s3, s3, -1
	or t4, t4, s3
	or t3, t3, t4
	xor s4, s4, t3
	xor s2, s2, s4
	xori s5, s5, -1
	and s5, s5, t1
	xor s5, s5, s2
	and t2, t2, s3
	xor s6, s6, t2
	or s4, s4, s6
	xor t6, t6, t5
	xor s4, s4, t6
	or s1, s1, t1
	xor s1, s1, s4
	ld a6, 184(s0)
	xor a6, a6, s7
	sd a6, 184(s0)
	ld a6, 136(s0)
	xor a6, a6, s1
	sd a6, 136(s0)
	ld a6, 40(s0)
	xor a6, a6, s8
	sd a6, 40(s0)
	ld a6, 24(s0)
	xor a6, a6, s5
	sd a6, 24(s0)
	slli t0, a5, 39
	srai t0, t0, 63
	ld a6, 464(s0)
	xor t0, t0, a6
	slli t1, a5, 38
	srai t1, t1, 63
	ld a6, 32(s0)
	xor t1, t1, a6
	slli t2, a5, 37
	srai t2, t2, 63
	ld a6, 96(s0)
	xor t2, t2, a6
	slli t3, a5, 36
	srai t3, t3, 63
	ld a6, 160(s0)
	xor t3, t3, a6
	slli t4, a5, 35
	srai t4, t4, 63
	ld a6, 224(s0)
	xor t4, t4, a6
	slli t5, a5, 34
	srai t5, t5, 63
	ld a6, 288(s0)
	xor t5, t5, a6
	xor t5, t5, t3
	xor t3, t3, t1
	or t6, t4, t2
	xor t6, t1, t6
	xori t6, t6, -1
	and t6, t6, t3
	or a0, t3, t4
	xor a0, a0, t4
	xor a7, t2, a0
	or s1, t5, a7
	or s1, s1, t6
	xor s1, s1, t6
	xor s2, t4, s1
	and a7, a7, s2
	or t3, t3, a7
	xor t3, t3, a7
	xor t5, t5, s2
	xori t3, t3, -1
	and t3, t3, t5
	xor t6, t6, t3
	xor t4, t4, t2
	or t1, t1, a0
	xor t5, t5, t1
	or t1, t5, t4
	xor t1, t1, t4
	xor s1, s1, t1
	or t1, t0, t6
	xor t1, t1, t6
	xor t1, t1, s1
	xori s1, s1, -1
	or a0, t6, t0
	xor a0, a0, t0
	xor a0, a0, s1
	xor t6, t6, s1
	or t6, t6, t4
	xor t6, t6, t4
	or a7, a7, t6
	xor t5, t5, a7
	or a7, s2, t0
	xor a7, a7, t5
	and t0, t0, s2
	xor t0, t0, t5
	ld a6, 504(s0)
	xor a6, a6, t0
	sd a6, 504(s0)
	ld a6, 424(s0)
	xor a6, a6, a7
	sd a6, 424(s0)
	ld a6, 280(s0)
	xor a6, a6, a0
	sd a6, 280(s0)
	ld a6, 392(s0)
	xor a6, a6, t1
	sd a6, 392(s0)
	slli t0, a5, 45
	srai t0, t0, 63
	ld a6, 208(s0)
	xor t0, t0, a6
	slli t1, a5, 44
	srai t1, t1, 63
	ld a6, 272(s0)
	xor t1, t1, a6
	slli t2, a5, 43
	srai t2, t2, 63
	ld a6, 336(s0)
	xor t2, t2, a6
	slli t3, a5, 42
	srai t3, t3, 63
	ld a6, 400(s0)
	xor t3, t3, a6
	slli t4, a5, 41
	srai t4, t4, 63
	ld a6, 464(s0)
	xor t4, t4, a6
	slli t5, a5, 40
	srai t5, t5, 63
	ld a6, 32(s0)
	xor t5, t5, a6
	or t6, t5, t3
	or a0, t6, t0
	xor a0, a0, t0
	xor a7, t5, a0
	xor s1, t3, a7
	or s2, t2, s1
	or a0, a0, t2
	xor a0, a0, t2
	xor t3, t3, a0
	and a0, t1, t3
	or s1, t5, s1
	xor a0, a0, s1
	xor a0, t2, a0
	xor t0, t0, a0
	or s3, a7, t0
	and s4, t1, s3
	xor s5, a7, s4
	and s6, t2, s1
	xor s5, s5, s6
	or s3, s3, t5
	xor s3, s3, t5
	xor s6, t3, s3
	xor t1, t1, s2
	xori s6, s6, -1
	and s6, s6, t1
	xori s6, s6, -1
	or s6, s6, t4
	xor s6, s6, t4
	xor s6, s6, a0
	or a0, t3, s4
	xor a0, a0, s4
	xor s3, s3, t1
	or s3, s5, s3
	or s3, s3, a0
	xor s3, s3, a0
	or a0, s2, s3
	xor a0, a0, s3
	and t0, t0, s3
	xor t1, t1, t0
	and s1, t3, s1
	or s1, t1, s1
	xor s4, s4, s1
	and s4, s4, t4
	xor s4, s4, s5
	xor t5, t5, t6
	xor s3, s3, t5
	and t2, t2, t1
	xor s3, s3, t2
	or a0, a0, t4
	xor a0, a0, s3
	xor t3, s2, t3
	or t3, t3, s3
	xor t3, t3, s3
	xor a7, a7, t1
	xor t3, t3, a7
	and s2, s2, t4
	xor s2, s2, t3
	ld a6, 376(s0)
	xor a6, a6, s4
	sd a6, 376(s0)
	ld a6, 456(s0)
	xor a6, a6, s6
	sd a6, 456(s0)
	ld a6, 168(s0)
	xor a6, a6, s2
	sd a6, 168(s0)
	ld a6, 56(s0)
	xor a6, a6, a0
	sd a6, 56(s0)
	slli t0, a5, 51
	srai t0, t0, 63
	ld a6, 448(s0)
	xor t0, t0, a6
	slli t1, a5, 50
	srai t1, t1, 63
	ld a6, 16(s0)
	xor t1, t1, a6
	slli t2, a5, 49
	srai t2, t2, 63
	ld a6, 80(s0)
	xor t2, t2, a6
	slli t3, a5, 48
	srai t3, t3, 63
	ld a6, 144(s0)
	xor t3, t3, a6
	slli t4, a5, 47
	srai t4, t4, 63
	ld a6, 208(s0)
	xor t4, t4, a6
	slli t5, a5, 46
	srai t5, t5, 63
	ld a6, 272(s0)
	xor t5, t5, a6
	xor t6, t4, t1
	or a0, t4, t0
	and a0, t5, a0
	xor t6, t6, a0
	xor a7, t0, t6
	or s1, t1, a7
	xor s1, s1, a7
	and a7, t5, a7
	xor s2, t4, a7
	xor s3, t5, t3
	or s4, s2, s3
	xor s5, t6, s4
	and s6, t3, s5
	or s7, s6, t0
	xor s7, s7, t0
	or s2, s1, s2
	xor s8, s7, s2
	and s9, s8, t2
	xor s9, s9, s5
	xor s4, t4, s4
	or s10, t0, s4
	xor s10, s10, s4
	xor t3, t3, s10
	or s10, t1, s6
	xor s10, s10, s6
	or s10, t3, s10
	or t4, t4, s3
	xor s8, s8, t4
	or a0, a0, s10
	xor s8, s8, a0
	or s5, t5, s5
	and s2, s2, s5
	xor s2, t3, s2
	xori s7, s7, -1
	and s7, s7, s2
	or s1, s1, t2
	xor s1, s1, s7
	xor t6, t6, s2
	or t1, t1, t6
	xor t1, t1, t6
	xori t4, t4, -1
	xor s4, s4, t4
	xor t1, t1, s4
	or t1, t1, t2
	xor t1, t1, t2
	xor t1, t1, s8
	xor t0, t0, a7
	xor t5, t5, t3
	and t0, t0, t5
	xor s6, s6, s4
	xor t0, t0, s6
	or s10, s10, t2
	xor s10, s10, t2
	xor s10, s10, t0
	ld a6, 344(s0)
	xor a6, a6, s9
	sd a6, 344(s0)
	ld a6, 360(s0)
	xor a6, a6, s1
	sd a6, 360(s0)
	ld a6, 200(s0)
	xor a6, a6, t1
	sd a6, 200(s0)
	ld a6, 312(s0)
	xor a6, a6, s10
	sd a6, 312(s0)
	slli t0, a5, 57
	srai t0, t0, 63
	ld a6, 192(s0)
	xor t0, t0, a6
	slli t1, a5, 56
	srai t1, t1, 63
	ld a6, 256(s0)
	xor t1, t1, a6
	slli t2, a5, 55
	srai t2, t2, 63
	ld a6, 320(s0)
	xor t2, t2, a6
	slli t3, a5, 54
	srai t3, t3, 63
	ld a6, 384(s0)
	xor t3, t3, a6
	slli t4, a5, 53
	srai t4, t4, 63
	ld a6, 448(s0)
	xor t4, t4, a6
	slli t5, a5, 52
	srai t5, t5, 63
	ld a6, 16(s0)
	xor t5, t5, a6
	xor t6, t2, t1
	xor a0, t3, t6
	and a7, t0, a0
	and s1, t2, t6
	xor s2, t4, s1
	and s3, a7, s2
	and s4, t0, s1
	xor s5, t3, s4
	or s6, s2, s5
	xor t6, t0, t6
	xor s7, s6, t6
	or s8, t5, s3
	xor s8, s8, s3
	xor s8, s8, s7
	xori a0, a0, -1
	and a0, a0, t1
	or s7, s2, a0
	xor s5, a7, s5
	xor s7, s7, s5
	xor a7, a7, t6
	or t2, t2, a7
	xor t2, t2, a7
	or t6, s2, t2
	xor t6, t6, t2
	xor t1, t1, s5
	xor t6, t6, t1
	or a7, a7, s4
	xor a7, a7, s4
	or t2, t2, a7
	xor s6, t4, s6
	and s6, t6, s6
	xor s6, t2, s6
	and s4, s6, t5
	xor s4, s4, t6
	or s2, s2, t3
	xor s2, s2, t3
	or a7, a7, s2
	or s1, s1, t6
	and a7, a7, s1
	xor s6, s6, a7
	xor a0, a0, t2
	and t0, t0, a0
	or s3, s3, t0
	xor a7, a7, s3
	or t0, a7, t5
	xor t0, t0, t5
	xor t0, t0, s7
	and t4, t4, s3
	xori s7, s7, -1
	xor t4, t4, s7
	xor a7, a7, t4
	or s6, s6, t5
	xor s6, s6, a7
	ld a6, 120(s0)
	xor a6, a6, s8
	sd a6, 120(s0)
	ld a6, 152(s0)
	xor a6, a6, s4
	sd a6, 152(s0)
	ld a6, 296(s0)
	xor a6, a6, s6
	sd a6, 296(s0)
	ld a6, 8(s0)
	xor a6, a6, t0
	sd a6, 8(s0)
	slli t0, a5, 63
	srai t0, t0, 63
	ld a6, 496(s0)
	xor t0, t0, a6
	slli t1, a5, 62
	srai t1, t1, 63
	ld a6, 0(s0)
	xor t1, t1, a6
	slli t2, a5, 61
	srai t2, t2, 63
	ld a6, 64(s0)
	xor t2, t2, a6
	slli t3, a5, 60
	srai t3, t3, 63
	ld a6, 128(s0)
	xor t3, t3, a6
	slli t4, a5, 59
	srai t4, t4, 63
	ld a6, 192(s0)
	xor t4, t4, a6
	slli t5, a5, 58
	srai t5, t5, 63
	ld a6, 256(s0)
	xor t5, t5, a6
	or t6, t3, t4
	xor t6, t6, t4
	or a0, t1, t3
	xor a0, a0, t3
	xor a0, t2, a0
	and a7, t5, a0
	or s1, a7, t6
	xor s1, s1, t6
	or s2, t4, a0
	xor s2, s2, a0
	or s3, t5, s2
	or s4, t4, t3
	xor s4, s4, t3
	xor s4, t1, s4
	and s5, s3, s4
	or a7, a7, s5
	xori a0, a0, -1
	xor s5, s5, a0
	or t3, t3, s3
	xor t3, t3, s3
	xor s5, s5, t3
	xor t6, t6, s5
	or t3, s1, t0
	xor t3, t3, t6
	xor t6, t5, t6
	and s3, t1, t6
	xor s5, t4, s5
	xor s3, s3, s5
	xor s2, s2, s3
	xor s3, a7, s3
	or t4, t4, s3
	xor t1, t1, t6
	xor t4, t4, t1
	and a7, a7, t0
	xor a7, a7, t4
	xor s4, s4, s2
	or s5, t2, s5
	xor s5, s4, s5
	xor t5, t5, s5
	and t5, t5, t0
	xor t5, t5, s2
	or s4, s4, t2
	xor s4, s4, t2
	and t4, t4, s4
	xor s1, s1, s5
	xor t4, t4, s1
	or t4, t4, t0
	xor t4, t4, s2
	ld a6, 216(s0)
	xor a6, a6, t5
	sd a6, 216(s0)
	ld a6, 104(s0)
	xor a6, a6, a7
	sd a6, 104(s0)
	ld a6, 328(s0)
	xor a6, a6, t3
	sd a6, 328(s0)
	ld a6, 248(s0)
	xor a6, a6, t4
	sd a6, 248(s0)
	addi a4, a4, -1
	bnez a4, 28b
	ld t0, 0(s0)
	ld t1, 8(s0)
	sd t1, 0(s0)
	sd t0, 8(s0)
	ld t0, 64(s0)
	ld t1, 72(s0)
	sd t1, 64(s0)
	sd t0, 72(s0)
	ld t0, 128(s0)
	ld t1, 136(s0)
	sd t1, 128(s0)
	sd t0, 136(s0)
	ld t0, 192(s0)
	ld t1, 200(s0)
	sd t1, 192(s0)
	sd t0, 200(s0)
	ld t0, 256(s0)
	ld t1, 264(s0)
	sd t1, 256(s0)
	sd t0, 264(s0)
	ld t0, 320(s0)
	ld t1, 328(s0)
	sd t1, 320(s0)
	sd t0, 328(s0)
	ld t0, 384(s0)
	ld t1, 392(s0)
	sd t1, 384(s0)
	sd t0, 392(s0)
	ld t0, 448(s0)
	ld t1, 456(s0)
	sd t1, 448(s0)
	sd t0, 456(s0)
	ld t0, 16(s0)
	ld t1, 24(s0)
	sd t1, 16(s0)
	sd t0, 24(s0)
	ld t0, 80(s0)
	ld t1, 88(s0)
	sd t1, 80(s0)
	sd t0, 88(s0)
	ld t0, 144(s0)
	ld t1, 152(s0)
	sd t1, 144(s0)
	sd t0, 152(s0)
	ld t0, 208(s0)
	ld t1, 216(s0)
	sd t1, 208(s0)
	sd t0, 216(s0)
	ld t0, 272(s0)
	ld t1, 280(s0)
	sd t1, 272(s0)
	sd t0, 280(s0)
	ld t0, 336(s0)
	ld t1, 344(s0)
	sd t1, 336(s0)
	sd t0, 344(s0)
	ld t0, 400(s0)
	ld t1, 408(s0)
	sd t1, 400(s0)
	sd t0, 408(s0)
	ld t0, 464(s0)
	ld t1, 472(s0)
	sd t1, 464(s0)
	sd t0, 472(s0)
	ld t0, 32(s0)
	ld t1, 40(s0)
	sd t1, 32(s0)
	sd t0, 40(s0)
	ld t0, 96(s0)
	ld t1, 104(s0)
	sd t1, 96(s0)
	sd t0, 104(s0)
	ld t0, 160(s0)
	ld t1, 168(s0)
	sd t1, 160(s0)
	sd t0, 168(s0)
	ld t0, 224(s0)
	ld t1, 232(s0)
	sd t1, 224(s0)
	sd t0, 232(s0)
	ld t0, 288(s0)
	ld t1, 296(s0)
	sd t1, 288(s0)
	sd t0, 296(s0)
	ld t0, 352(s0)
	ld t1, 360(s0)
	sd t1, 352(s0)
	sd t0, 360(s0)
	ld t0, 416(s0)
	ld t1, 424(s0)
	sd t1, 416(s0)
	sd t0, 424(s0)
	ld t0, 480(s0)
	ld t1, 488(s0)
	sd t1, 480(s0)
	sd t0, 488(s0)
	ld t0, 48(s0)
	ld t1, 56(s0)
	sd t1, 48(s0)
	sd t0, 56(s0)
	ld t0, 112(s0)
	ld t1, 120(s0)
	sd t1, 112(s0)
	sd t0, 120(s0)
	ld t0, 176(s0)
	ld t1, 184(s0)
	sd t1, 176(s0)
	sd t0, 184(s0)
	ld t0, 240(s0)
	ld t1, 248(s0)
	sd t1, 240(s0)
	sd t0, 248(s0)
	ld t0, 304(s0)
	ld t1, 312(s0)
	sd t1, 304(s0)
	sd t0, 312(s0)
	ld t0, 368(s0)
	ld t1, 376(s0)
	sd t1, 368(s0)
	sd t0, 376(s0)
	ld t0, 432(s0)
	ld t1, 440(s0)
	sd t1, 432(s0)
	sd t0, 440(s0)
	ld t0, 496(s0)
	ld t1, 504(s0)
	sd t1, 496(s0)
	sd t0, 504(s0)
	addi a3, s0, 768
	addi a4, zero, 8
29:
	ld a5, 0(a3)
	addi a3, a3, 8
	slli t0, a5, 21
	srai t0, t0, 63
	ld a6, 248(s0)
	xor t0, t0, a6
	slli t1, a5, 20
	srai t1, t1, 63
	ld a6, 312(s0)
	xor t1, t1, a6
	slli t2, a5, 19
	srai t2, t2, 63
	ld a6, 376(s0)
	xor t2, t2, a6
	slli t3, a5, 18
	srai t3, t3, 63
	ld a6, 440(s0)
	xor t3, t3, a6
	slli t4, a5, 17
	srai t4, t4, 63
	ld a6, 504(s0)
	xor t4, t4, a6
	slli t5, a5, 16
	srai t5, t5, 63
	ld a6, 8(s0)
	xor t5, t5, a6
	or t6, t5, t1
	xor t6, t6, t1
	xor a0, t2, t6
	or a7, t3, t0
	xor s1, t5, t3
	and s2, a7, s1
	xor s3, t2, s2
	or s4, s3, a0
	xor s4, s4, a0
	xor s5, t1, t0
	xor s6, t3, s5
	xori s6, s6, -1
	and s6, s6, a0
	or s2, t0, s2
	xor s6, s6, s2
	or s2, s6, s4
	xor s2, s2, s4
	or t0, t5, t0
	or s7, s6, t0
	xori s3, s3, -1
	and s3, s3, t1
	xor s8, s7, s3
	or t2, t2, t0
	xor t2, t2, t0
	xor t2, s3, t2
	xori s1, s1, -1
	and s1, s1, s5
	or t2, t2, s1
	or t3, t3, t6
	xor t3, t3, t6
	xor t6, a0, s7
	or t6, t6, t3
	xor t6, t6, t3
	xori t3, t6, -1
	and s6, a7, s6
	xor t3, t3, s6
	or s8, s8, t4
	xor s8, s8, t4
	xor s8, s8, t3
	xor t6, s5, t6
	or s3, s3, t6
	xor s3, a7, s3
	xor t5, t5, s3
	xor t3, t3, t5
	or s4, s4, t4
	xor s4, s4, t3
	xor a7, a7, s7
	or a7, t2, a7
	xor a7, t5, a7
	or s5, s5, t3
	xor s5, a7, s5
	or t3, s2, t4
	xor t3, t3, s5
	or t1, t1, a0
	or t1, t1, a7
	xor t1, t1, a7
	and s2, s2, t5
	xor t1, t1, s2
	or t1, t1, t4
	xor t1, t1, t2
	ld a6, 64(s0)
	xor a6, a6, t1
	sd a6, 64(s0)
	ld a6, 80(s0)
	xor a6, a6, s8
	sd a6, 80(s0)
	ld a6, 464(s0)
	xor a6, a6, t3
	sd a6, 464(s0)
	ld a6, 480(s0)
	xor a6, a6, s4
	sd a6, 480(s0)
	slli t0, a5, 27
	srai t0, t0, 63
	ld a6, 488(s0)
	xor t0, t0, a6
	slli t1, a5, 26
	srai t1, t1, 63
	ld a6, 56(s0)
	xor t1, t1, a6
	slli t2, a5, 25
	srai t2, t2, 63
	ld a6, 120(s0)
	xor t2, t2, a6
	slli t3, a5, 24
	srai t3, t3, 63
	ld a6, 184(s0)
	xor t3, t3, a6
	slli t4, a5, 23
	srai t4, t4, 63
	ld a6, 248(s0)
	xor t4, t4, a6
	slli t5, a5, 22
	srai t5, t5, 63
	ld a6, 312(s0)
	xor t5, t5, a6
	xor t6, t4, t1
	or a0, t5, t0
	xor a0, a0, t0
	xori a0, a0, -1
	and a0, a0, t1
	or a7, t4, a0
	or s1, t6, t0
	xor s1, s1, t0
	and s2, t5, t6
	xor t1, t1, s2
	or s2, t1, s1
	xor s2, s2, s1
	and s3, t3, t0
	xor a0, a0, s1
	and a0, a7, a0
	or s1, a0, s3
	xor s1, s1, s3
	and s4, t3, a0
	xori t5, t5, -1
	xor t5, s4, t5
	xor t0, t0, t6
	or s5, t0, s3
	xor s5, s5, s3
	xor s6, t5, s5
	xori s1, s1, -1
	and s1, s1, t2
	xor s1, s1, s6
	or t4, t4, s5
	xor t4, t4, s5
	xor t1, t1, t4
	or t5, t5, t1
	xor t5, t5, t1
	xor t3, t3, t0
	xor t5, t5, t3
	or s5, a7, t2
	xor s5, s5, t2
	xor s5, s5, t5
	xor s4, s4, t4
	or t3, t3, s4
	xor a7, a7, s6
	or s3, s3, a7
	xor s4, t3, s3
	xor a0, a0, s6
	xor t5, t5, a0
	and s3, s3, t5
	and t6, t6, t3
	xor s3, s3, t6
	or t6, s3, t2
	xor t6, t6, s4
	or s3, s3, t1
	xor s3, s3, t1
	or t0, t0, a7
	xor s3, s3, t0
	or s2, s2, t2
	xor s2, s2, s3
	ld a6, 400(s0)
	xor a6, a6, s2
	sd a6, 400(s0)
	ld a6, 432(s0)
	xor a6, a6, t6
	sd a6, 432(s0)
	ld a6, 256(s0)
	xor a6, a6, s1
	sd a6, 256(s0)
	ld a6, 224(s0)
	xor a6, a6, s5
	sd a6, 224(s0)
	slli t0, a5, 33
	srai t0, t0, 63
	ld a6, 232(s0)
	xor t0, t0, a6
	slli t1, a5, 32
	srai t1, t1, 63
	ld a6, 296(s0)
	xor t1, t1, a6
	slli t2, a5, 31
	srai t2, t2, 63
	ld a6, 360(s0)
	xor t2, t2, a6
	slli t3, a5, 30
	srai t3, t3, 63
	ld a6, 424(s0)
	xor t3, t3, a6
	slli t4, a5, 29
	srai t4, t4, 63
	ld a6, 488(s0)
	xor t4, t4, a6
	slli t5, a5, 28
	srai t5, t5, 63
	ld a6, 56(s0)
	xor t5, t5, a6
	or t6, t5, t4
	xor t6, t6, t4
	xor a0, t3, t0
	or a7, t6, a0
	xor s1, t2, t0
	or s2, s1, t5
	xor s2, s2, t5
	xor s3, a7, s2
	xor s4, t4, a0
	or s5, s4, t0
	xor s5, s5, t0
	xor a7, a7, s5
	or s5, s3, a7
	xor s5, s5, a7
	and s6, t0, s3
	or s6, t2, s6
	and s6, t5, s6
	xor s6, s4, s6
	or s7, s3, t1
	xor s7, s7, t1
	xor s7, s7, s6
	and a0, a0, s1
	xor s1, t5, t2
	xor s8, a7, s1
	or s8, t3, s8
	or s8, s8, a0
	xor s8, s8, a0
	or s2, s2, s1
	or s1, s6, s2
	xor s1, s1, s2
	and t0, t2, t0
	or a0, t0, t4
	xor a0, a0, t4
	xor s1, s1, a0
	and a7, a7, s1
	or t0, s4, t0
	or t0, t0, a7
	xor t0, t0, a7
	xor t5, t5, t0
	and s8, s8, t1
	xor s8, s8, t5
	xori s3, s3, -1
	or t4, t4, s3
	or t3, t3, t4
	xor s4, s4, t3
	xor s2, s2, s4
	xori s5, s5, -1
	and s5, s5, t1
	xor s5, s5, s2
	and t2, t2, s3
	xor s6, s6, t2
	or s4, s4, s6
	xor t6, t6, t5
	xor s4, s4, t6
	or s1, s1, t1
	xor s1, s1, s4
	ld a6, 176(s0)
	xor a6, a6, s7
	sd a6, 176(s0)
	ld a6, 128(s0)
	xor a6, a6, s1
	sd a6, 128(s0)
	ld a6, 32(s0)
	xor a6, a6, s8
	sd a6, 32(s0)
	ld a6, 16(s0)
	xor a6, a6, s5
	sd a6, 16(s0)
	slli t0, a5, 39
	srai t0, t0, 63
	ld a6, 472(s0)
	xor t0, t0, a6
	slli t1, a5, 38
	srai t1, t1, 63
	ld a6, 40(s0)
	xor t1, t1, a6
	slli t2, a5, 37
	srai t2, t2, 63
	ld a6, 104(s0)
	xor t2, t2, a6
	slli t3, a5, 36
	srai t3, t3, 63
	ld a6, 168(s0)
	xor t3, t3, a6
	slli t4, a5, 35
	srai t4, t4, 63
	ld a6, 232(s0)
	xor t4, t4, a6
	slli t5, a5, 34
	srai t5, t5, 63
	ld a6, 296(s0)
	xor t5, t5, a6
	xor t5, t5, t3
	xor t3, t3, t1
	or t6, t4, t2
	xor t6, t1, t6
	xori t6, t6, -1
	and t6, t6, t3
	or a0, t3, t4
	xor a0, a0, t4
	xor a7, t2, a0
	or s1, t5, a7
	or s1, s1, t6
	xor s1, s1, t6
	xor s2, t4, s1
	and a7, a7, s2
	or t3, t3, a7
	xor t3, t3, a7
	xor t5, t5, s2
	xori t3, t3, -1
	and t3, t3, t5
	xor t6, t6, t3
	xor t4, t4, t2
	or t1, t1, a0
	xor t5, t5, t1
	or t1, t5, t4
	xor t1, t1, t4
	xor s1, s1, t1
	or t1, t0, t6
	xor t1, t1, t6
	xor t1, t1, s1
	xori s1, s1, -1
	or a0, t6, t0
	xor a0, a0, t0
	xor a0, a0, s1
	xor t6, t6, s1
	or t6, t6, t4
	xor t6, t6, t4
	or a7, a7, t6
	xor t5, t5, a7
	or a7, s2, t0
	xor a7, a7, t5
	and t0, t0, s2
	xor t0, t0, t5
	ld a6, 496(s0)
	xor a6, a6, t0
	sd a6, 496(s0)
	ld a6, 416(s0)
	xor a6, a6, a7
	sd a6, 416(s0)
	ld a6, 272(s0)
	xor a6, a6, a0
	sd a6, 272(s0)
	ld a6, 384(s0)
	xor a6, a6, t1
	sd a6, 384(s0)
	slli t0, a5, 45
	srai t0, t0, 63
	ld a6, 216(s0)
	xor t0, t0, a6
	slli t1, a5, 44
	srai t1, t1, 63
	ld a6, 280(s0)
	xor t1, t1, a6
	slli t2, a5, 43
	srai t2, t2, 63
	ld a6, 344(s0)
	xor t2, t2, a6
	slli t3, a5, 42
	srai t3, t3, 63
	ld a6, 408(s0)
	xor t3, t3, a6
	slli t4, a5, 41
	srai t4, t4, 63
	ld a6, 472(s0)
	xor t4, t4, a6
	slli t5, a5, 40
	srai t5, t5, 63
	ld a6, 40(s0)
	xor t5, t5, a6
	or t6, t5, t3
	or a0, t6, t0
	xor a0, a0, t0
	xor a7, t5, a0
	xor s1, t3, a7
	or s2, t2, s1
	or a0, a0, t2
	xor a0, a0, t2
	xor t3, t3, a0
	and a0, t1, t3
	or s1, t5, s1
	xor a0, a0, s1
	xor a0, t2, a0
	xor t0, t0, a0
	or s3, a7, t0
	and s4, t1, s3
	xor s5, a7, s4
	and s6, t2, s1
	xor s5, s5, s6
	or s3, s3, t5
	xor s3, s3, t5
	xor s6, t3, s3
	xor t1, t1, s2
	xori s6, s6, -1
	and s6, s6, t1
	xori s6, s6, -1
	or s6, s6, t4
	xor s6, s6, t4
	xor s6, s6, a0
	or a0, t3, s4
	xor a0, a0, s4
	xor s3, s3, t1
	or s3, s5, s3
	or s3, s3, a0
	xor s3, s3, a0
	or a0, s2, s3
	xor a0, a0, s3
	and t0, t0, s3
	xor t1, t1, t0
	and s1, t3, s1
	or s1, t1, s1
	xor s4, s4, s1
	and s4, s4, t4
	xor s4, s4, s5
	xor t5, t5, t6
	xor s3, s3, t5
	and t2, t2, t1
	xor s3, s3, t2
	or a0, a0, t4
	xor a0, a0, s3
	xor t3, s2, t3
	or t3, t3, s3
	xor t3, t3, s3
	xor a7, a7, t1
	xor t3, t3, a7
	and s2, s2, t4
	xor s2, s2, t3
	ld a6, 368(s0)
	xor a6, a6, s4
	sd a6, 368(s0)
	ld a6, 448(s0)
	xor a6, a6, s6
	sd a6, 448(s0)
	ld a6, 160(s0)
	xor a6, a6, s2
	sd a6, 160(s0)
	ld a6, 48(s0)
	xor a6, a6, a0
	sd a6, 48(s0)
	slli t0, a5, 51
	srai t0, t0, 63
	ld a6, 456(s0)
	xor t0, t0, a6
	slli t1, a5, 50
	srai t1, t1, 63
	ld a6, 24(s0)
	xor t1, t1, a6
	slli t2, a5, 49
	srai t2, t2, 63
	ld a6, 88(s0)
	xor t2, t2, a6
	slli t3, a5, 48
	srai t3, t3, 63
	ld a6, 152(s0)
	xor t3, t3, a6
	slli t4, a5, 47
	srai t4, t4, 63
	ld a6, 216(s0)
	xor t4, t4, a6
	slli t5, a5, 46
	srai t5, t5, 63
	ld a6, 280(s0)
	xor t5, t5, a6
	xor t6, t4, t1
	or a0, t4, t0
	and a0, t5, a0
	xor t6, t6, a0
	xor a7, t0, t6
	or s1, t1, a7
	xor s1, s1, a7
	and a7, t5, a7
	xor s2, t4, a7
	xor s3, t5, t3
	or s4, s2, s3
	xor s5, t6, s4
	and s6, t3, s5
	or s7, s6, t0
	xor s7, s7, t0
	or s2, s1, s2
	xor s8, s7, s2
	and s9, s8, t2
	xor s9, s9, s5
	xor s4, t4, s4
	or s10, t0, s4
	xor s10, s10, s4
	xor t3, t3, s10
	or s10, t1, s6
	xor s10, s10, s6
	or s10, t3, s10
	or t4, t4, s3
	xor s8, s8, t4
	or a0, a0, s10
	xor s8, s8, a0
	or s5, t5, s5
	and s2, s2, s5
	xor s2, t3, s2
	xori s7, s7, -1
	and s7, s7, s2
	or s1, s1, t2
	xor s1, s1, s7
	xor t6, t6, s2
	or t1, t1, t6
	xor t1, t1, t6
	xori t4, t4, -1
	xor s4, s4, t4
	xor t1, t1, s4
	or t1, t1, t2
	xor t1, t1, t2
	xor t1, t1, s8
	xor t0, t0, a7
	xor t5, t5, t3
	and t0, t0, t5
	xor s6, s6, s4
	xor t0, t0, s6
	or s10, s10, t2
	xor s10, s10, t2
	xor s10, s10, t0
	ld a6, 336(s0)
	xor a6, a6, s9
	sd a6, 336(s0)
	ld a6, 352(s0)
	xor a6, a6, s1
	sd a6, 352(s0)
	ld a6, 192(s0)
	xor a6, a6, t1
	sd a6, 192(s0)
	ld a6, 304(s0)
	xor a6, a6, s10
	sd a6, 304(s0)
	slli t0, a5, 57
	srai t0, t0, 63
	ld a6, 200(s0)
	xor t0, t0, a6
	slli t1, a5, 56
	srai t1, t1, 63
	ld a6, 264(s0)
	xor t1, t1, a6
	slli t2, a5, 55
	srai t2, t2, 63
	ld a6, 328(s0)
	xor t2, t2, a6
	slli t3, a5, 54
	srai t3, t3, 63
	ld a6, 392(s0)
	xor t3, t3, a6
	slli t4, a5, 53
	srai t4, t4, 63
	ld a6, 456(s0)
	xor t4, t4, a6
	slli t5, a5, 52
	srai t5, t5, 63
	ld a6, 24(s0)
	xor t5, t5, a6
	xor t6, t2, t1
	xor a0, t3, t6
	and a7, t0, a0
	and s1, t2, t6
	xor s2, t4, s1
	and s3, a7, s2
	and s4, t0, s1
	xor s5, t3, s4
	or s6, s2, s5
	xor t6, t0, t6
	xor s7, s6, t6
	or s8, t5, s3
	xor s8, s8, s3
	xor s8, s8, s7
	xori a0, a0, -1
	and a0, a0, t1
	or s7, s2, a0
	xor s5, a7, s5
	xor s7, s7, s5
	xor a7, a7, t6
	or t2, t2, a7
	xor t2, t2, a7
	or t6, s2, t2
	xor t6, t6, t2
	xor t1, t1, s5
	xor t6, t6, t1
	or a7, a7, s4
	xor a7, a7, s4
	or t2, t2, a7
	xor s6, t4, s6
	and s6, t6, s6
	xor s6, t2, s6
	and s4, s6, t5
	xor s4, s4, t6
	or s2, s2, t3
	xor s2, s2, t3
	or a7, a7, s2
	or s1, s1, t6
	and a7, a7, s1
	xor s6, s6, a7
	xor a0, a0, t2
	and t0, t0, a0
	or s3, s3, t0
	xor a7, a7, s3
	or t0, a7, t5
	xor t0, t0, t5
	xor t0, t0, s7
	and t4, t4, s3
	xori s7, s7, -1
	xor t4, t4, s7
	xor a7, a7, t4
	or s6, s6, t5
	xor s6, s6, a7
	ld a6, 112(s0)
	xor a6, a6, s8
	sd a6, 112(s0)
	ld a6, 144(s0)
	xor a6, a6, s4
	sd a6, 144(s0)
	ld a6, 288(s0)
	xor a6, a6, s6
	sd a6, 288(s0)
	ld a6, 0(s0)
	xor a6, a6, t0
	sd a6, 0(s0)
	slli t0, a5, 63
	srai t0, t0, 63
	ld a6, 504(s0)
	xor t0, t0, a6
	slli t1, a5, 62
	srai t1, t1, 63
	ld a6, 8(s0)
	xor t1, t1, a6
	slli t2, a5, 61
	srai t2, t2, 63
	ld a6, 72(s0)
	xor t2, t2, a6
	slli t3, a5, 60
	srai t3, t3, 63
	ld a6, 136(s0)
	xor t3, t3, a6
	slli t4, a5, 59
	srai t4, t4, 63
	ld a6, 200(s0)
	xor t4, t4, a6
	slli t5, a5, 58
	srai t5, t5, 63
	ld a6, 264(s0)
	xor t5, t5, a6
	or t6, t3, t4
	xor t6, t6, t4
	or a0, t1, t3
	xor a0, a0, t3
	xor a0, t2, a0
	and a7, t5, a0
	or s1, a7, t6
	xor s1, s1, t6
	or s2, t4, a0
	xor s2, s2, a0
	or s3, t5, s2
	or s4, t4, t3
	xor s4, s4, t3
	xor s4, t1, s4
	and s5, s3, s4
	or a7, a7, s5
	xori a0, a0, -1
	xor s5, s5, a0
	or t3, t3, s3
	xor t3, t3, s3
	xor s5, s5, t3
	xor t6, t6, s5
	or t3, s1, t0
	xor t3, t3, t6
	xor t6, t5, t6
	and s3, t1, t6
	xor s5, t4, s5
	xor s3, s3, s5
	xor s2, s2, s3
	xor s3, a7, s3
	or t4, t4, s3
	xor t1, t1, t6
	xor t4, t4, t1
	and a7, a7, t0
	xor a7, a7, t4
	xor s4, s4, s2
	or s5, t2, s5
	xor s5, s4, s5
	xor t5, t5, s5
	and t5, t5, t0
	xor t5, t5, s2
	or s4, s4, t2
	xor s4, s4, t2
	and t4, t4, s4
	xor s1, s1, s5
	xor t4, t4, s1
	or t4, t4, t0
	xor t4, t4, s2
	ld a6, 208(s0)
	xor a6, a6, t5
	sd a6, 208(s0)
	ld a6, 96(s0)
	xor a6, a6, a7
	sd a6, 96(s0)
	ld a6, 320(s0)
	xor a6, a6, t3
	sd a6, 320(s0)
	ld a6, 240(s0)
	xor a6, a6, t4
	sd a6, 240(s0)
	ld a5, 0(a3)
	addi a3, a3, 8
	slli t0, a5, 21
	srai t0, t0, 63
	ld a6, 240(s0)
	xor t0, t0, a6
	slli t1, a5, 20
	srai t1, t1, 63
	ld a6, 304(s0)
	xor t1, t1, a6
	slli t2, a5, 19
	srai t2, t2, 63
	ld a6, 368(s0)
	xor t2, t2, a6
	slli t3, a5, 18
	srai t3, t3, 63
	ld a6, 432(s0)
	xor t3, t3, a6
	slli t4, a5, 17
	srai t4, t4, 63
	ld a6, 496(s0)
	xor t4, t4, a6
	slli t5, a5, 16
	srai t5, t5, 63
	ld a6, 0(s0)
	xor t5, t5, a6
	or t6, t5, t1
	xor t6, t6, t1
	xor a0, t2, t6
	or a7, t3, t0
	xor s1, t5, t3
	and s2, a7, s1
	xor s3, t2, s2
	or s4, s3, a0
	xor s4, s4, a0
	xor s5, t1, t0
	xor s6, t3, s5
	xori s6, s6, -1
	and s6, s6, a0
	or s2, t0, s2
	xor s6, s6, s2
	or s2, s6, s4
	xor s2, s2, s4
	or t0, t5, t0
	or s7, s6, t0
	xori s3, s3, -1
	and s3, s3, t1
	xor s8, s7, s3
	or t2, t2, t0
	xor t2, t2, t0
	xor t2, s3, t2
	xori s1, s1, -1
	and s1, s1, s5
	or t2, t2, s1
	or t3, t3, t6
	xor t3, t3, t6
	xor t6, a0, s7
	or t6, t6, t3
	xor t6, t6, t3
	xori t3, t6, -1
	and s6, a7, s6
	xor t3, t3, s6
	or s8, s8, t4
	xor s8, s8, t4
	xor s8, s8, t3
	xor t6, s5, t6
	or s3, s3, t6
	xor s3, a7, s3
	xor t5, t5, s3
	xor t3, t3, t5
	or s4, s4, t4
	xor s4, s4, t3
	xor a7, a7, s7
	or a7, t2, a7
	xor a7, t5, a7
	or s5, s5, t3
	xor s5, a7, s5
	or t3, s2, t4
	xor t3, t3, s5
	or t1, t1, a0
	or t1, t1, a7
	xor t1, t1, a7
	and s2, s2, t5
	xor t1, t1, s2
	or t1, t1, t4
	xor t1, t1, t2
	ld a6, 72(s0)
	xor a6, a6, t1
	sd a6, 72(s0)
	ld a6, 88(s0)
	xor a6, a6, s8
	sd a6, 88(s0)
	ld a6, 472(s0)
	xor a6, a6, t3
	sd a6, 472(s0)
	ld a6, 488(s0)
	xor a6, a6, s4
	sd a6, 488(s0)
	slli t0, a5, 27
	srai t0, t0, 63
	ld a6, 480(s0)
	xor t0, t0, a6
	slli t1, a5, 26
	srai t1, t1, 63
	ld a6, 48(s0)
	xor t1, t1, a6
	slli t2, a5, 25
	srai t2, t2, 63
	ld a6, 112(s0)
	xor t2, t2, a6
	slli t3, a5, 24
	srai t3, t3, 63
	ld a6, 176(s0)
	xor t3, t3, a6
	slli t4, a5, 23
	srai t4, t4, 63
	ld a6, 240(s0)
	xor t4, t4, a6
	slli t5, a5, 22
	srai t5, t5, 63
	ld a6, 304(s0)
	xor t5, t5, a6
	xor t6, t4, t1
	or a0, t5, t0
	xor a0, a0, t0
	xori a0, a0, -1
	and a0, a0, t1
	or a7, t4, a0
	or s1, t6, t0
	xor s1, s1, t0
	and s2, t5, t6
	xor t1, t1, s2
	or s2, t1, s1
	xor s2, s2, s1
	and s3, t3, t0
	xor a0, a0, s1
	and a0, a7, a0
	or s1, a0, s3
	xor s1, s1, s3
	and s4, t3, a0
	xori t5, t5, -1
	xor t5, s4, t5
	xor t0, t0, t6
	or s5, t0, s3
	xor s5, s5, s3
	xor s6, t5, s5
	xori s1, s1, -1
	and s1, s1, t2
	xor s1, s1, s6
	or t4, t4, s5
	xor t4, t4, s5
	xor t1, t1, t4
	or t5, t5, t1
	xor t5, t5, t1
	xor t3, t3, t0
	xor t5, t5, t3
	or s5, a7, t2
	xor s5, s5, t2
	xor s5, s5, t5
	xor s4, s4, t4
	or t3, t3, s4
	xor a7, a7, s6
	or s3, s3, a7
	xor s4, t3, s3
	xor a0, a0, s6
	xor t5, t5, a0
	and s3, s3, t5
	and t6, t6, t3
	xor s3, s3, t6
	or t6, s3, t2
	xor t6, t6, s4
	or s3, s3, t1
	xor s3, s3, t1
	or t0, t0, a7
	xor s3, s3, t0
	or s2, s2, t2
	xor s2, s2, s3
	ld a6, 408(s0)
	xor a6, a6, s2
	sd a6, 408(s0)
	ld a6, 440(s0)
	xor a6, a6, t6
	sd a6, 440(s0)
	ld a6, 264(s0)
	xor a6, a6, s1
	sd a6, 264(s0)
	ld a6, 232(s0)
	xor a6, a6, s5
	sd a6, 232(s0)
	slli t0, a5, 33
	srai t0, t0, 63
	ld a6, 224(s0)
	xor t0, t0, a6
	slli t1, a5, 32
	srai t1, t1, 63
	ld a6, 288(s0)
	xor t1, t1, a6
	slli t2, a5, 31
	srai t2, t2, 63
	ld a6, 352(s0)
	xor t2, t2, a6
	slli t3, a5, 30
	srai t3, t3, 63
	ld a6, 416(s0)
	xor t3, t3, a6
	slli t4, a5, 29
	srai t4, t4, 63
	ld a6, 480(s0)
	xor t4, t4, a6
	slli t5, a5, 28
	srai t5, t5, 63
	ld a6, 48(s0)
	xor t5, t5, a6
	or t6, t5, t4
	xor t6, t6, t4
	xor a0, t3, t0
	or a7, t6, a0
	xor s1, t2, t0
	or s2, s1, t5
	xor s2, s2, t5
	xor s3, a7, s2
	xor s4, t4, a0
	or s5, s4, t0
	xor s5, s5, t0
	xor a7, a7, s5
	or s5, s3, a7
	xor s5, s5, a7
	and s6, t0, s3
	or s6, t2, s6
	and s6, t5, s6
	xor s6, s4, s6
	or s7, s3, t1
	xor s7, s7, t1
	xor s7, s7, s6
	and a0, a0, s1
	xor s1, t5, t2
	xor s8, a7, s1
	or s8, t3, s8
	or s8, s8, a0
	xor s8, s8, a0
	or s2, s2, s1
	or s1, s6, s2
	xor s1, s1, s2
	and t0, t2, t0
	or a0, t0, t4
	xor a0, a0, t4
	xor s1, s1, a0
	and a7, a7, s1
	or t0, s4, t0
	or t0, t0, a7
	xor t0, t0, a7
	xor t5, t5, t0
	and s8, s8, t1
	xor s8, s8, t5
	xori s3, s3, -1
	or t4, t4, s3
	or t3, t3, t4
	xor s4, s4, t3
	xor s2, s2, s4
	xori s5, s5, -1
	and s5, s5, t1
	xor s5, s5, s2
	and t2, t2, s3
	xor s6, s6, t2
	or s4, s4, s6
	xor t6, t6, t5
	xor s4, s4, t6
	or s1, s1, t1
	xor s1, s1, s4
	ld a6, 184(s0)
	xor a6, a6, s7
	sd a6, 184(s0)
	ld a6, 136(s0)
	xor a6, a6, s1
	sd a6, 136(s0)
	ld a6, 40(s0)
	xor a6, a6, s8
	sd a6, 40(s0)
	ld a6, 24(s0)
	xor a6, a6, s5
	sd a6, 24(s0)
	slli t0, a5, 39
	srai t0, t0, 63
	ld a6, 464(s0)
	xor t0, t0, a6
	slli t1, a5, 38
	srai t1, t1, 63
	ld a6, 32(s0)
	xor t1, t1, a6
	slli t2, a5, 37
	srai t2, t2, 63
	ld a6, 96(s0)
	xor t2, t2, a6
	slli t3, a5, 36
	srai t3, t3, 63
	ld a6, 160(s0)
	xor t3, t3, a6
	slli t4, a5, 35
	srai t4, t4, 63
	ld a6, 224(s0)
	xor t4, t4, a6
	slli t5, a5, 34
	srai t5, t5, 63
	ld a6, 288(s0)
	xor t5, t5, a6
	xor t5, t5, t3
	xor t3, t3, t1
	or t6, t4, t2
	xor t6, t1, t6
	xori t6, t6, -1
	and t6, t6, t3
	or a0, t3, t4
	xor a0, a0, t4
	xor a7, t2, a0
	or s1, t5, a7
	or s1, s1, t6
	xor s1, s1, t6
	xor s2, t4, s1
	and a7, a7, s2
	or t3, t3, a7
	xor t3, t3, a7
	xor t5, t5, s2
	xori t3, t3, -1
	and t3, t3, t5
	xor t6, t6, t3
	xor t4, t4, t2
	or t1, t1, a0
	xor t5, t5, t1
	or t1, t5, t4
	xor t1, t1, t4
	xor s1, s1, t1
	or t1, t0, t6
	xor t1, t1, t6
	xor t1, t1, s1
	xori s1, s1, -1
	or a0, t6, t0
	xor a0, a0, t0
	xor a0, a0, s1
	xor t6, t6, s1
	or t6, t6, t4
	xor t6, t6, t4
	or a7, a7, t6
	xor t5, t5, a7
	or a7, s2, t0
	xor a7, a7, t5
	and t0, t0, s2
	xor t0, t0, t5
	ld a6, 504(s0)
	xor a6, a6, t0
	sd a6, 504(s0)
	ld a6, 424(s0)
	xor a6, a6, a7
	sd a6, 424(s0)
	ld a6, 280(s0)
	xor a6, a6, a0
	sd a6, 280(s0)
	ld a6, 392(s0)
	xor a6, a6, t1
	sd a6, 392(s0)
	slli t0, a5, 45
	srai t0, t0, 63
	ld a6, 208(s0)
	xor t0, t0, a6
	slli t1, a5, 44
	srai t1, t1, 63
	ld a6, 272(s0)
	xor t1, t1, a6
	slli t2, a5, 43
	srai t2, t2, 63
	ld a6, 336(s0)
	xor t2, t2, a6
	slli t3, a5, 42
	srai t3, t3, 63
	ld a6, 400(s0)
	xor t3, t3, a6
	slli t4, a5, 41
	srai t4, t4, 63
	ld a6, 464(s0)
	xor t4, t4, a6
	slli t5, a5, 40
	srai t5, t5, 63
	ld a6, 32(s0)
	xor t5, t5, a6
	or t6, t5, t3
	or a0, t6, t0
	xor a0, a0, t0
	xor a7, t5, a0
	xor s1, t3, a7
	or s2, t2, s1
	or a0, a0, t2
	xor a0, a0, t2
	xor t3, t3, a0
	and a0, t1, t3
	or s1, t5, s1
	xor a0, a0, s1
	xor a0, t2, a0
	xor t0, t0, a0
	or s3, a7, t0
	and s4, t1, s3
	xor s5, a7, s4
	and s6, t2, s1
	xor s5, s5, s6
	or s3, s3, t5
	xor s3, s3, t5
	xor s6, t3, s3
	xor t1, t1, s2
	xori s6, s6, -1
	and s6, s6, t1
	xori s6, s6, -1
	or s6, s6, t4
	xor s6, s6, t4
	xor s6, s6, a0
	or a0, t3, s4
	xor a0, a0, s4
	xor s3, s3, t1
	or s3, s5, s3
	or s3, s3, a0
	xor s3, s3, a0
	or a0, s2, s3
	xor a0, a0, s3
	and t0, t0, s3
	xor t1, t1, t0
	and s1, t3, s1
	or s1, t1, s1
	xor s4, s4, s1
	and s4, s4, t4
	xor s4, s4, s5
	xor t5, t5, t6
	xor s3, s3, t5
	and t2, t2, t1
	xor s3, s3, t2
	or a0, a0, t4
	xor a0, a0, s3
	xor t3, s2, t3
	or t3, t3, s3
	xor t3, t3, s3
	xor a7, a7, t1
	xor t3, t3, a7
	and s2, s2, t4
	xor s2, s2, t3
	ld a6, 376(s0)
	xor a6, a6, s4
	sd a6, 376(s0)
	ld a6, 456(s0)
	xor a6, a6, s6
	sd a6, 456(s0)
	ld a6, 168(s0)
	xor a6, a6, s2
	sd a6, 168(s0)
	ld a6, 56(s0)
	xor a6, a6, a0
	sd a6, 56(s0)
	slli t0, a5, 51
	srai t0, t0, 63
	ld a6, 448(s0)
	xor t0, t0, a6
	slli t1, a5, 50
	srai t1, t1, 63
	ld a6, 16(s0)
	xor t1, t1, a6
	slli t2, a5, 49
	srai t2, t2, 63
	ld a6, 80(s0)
	xor t2, t2, a6
	slli t3, a5, 48
	srai t3, t3, 63
	ld a6, 144(s0)
	xor t3, t3, a6
	slli t4, a5, 47
	srai t4, t4, 63
	ld a6, 208(s0)
	xor t4, t4, a6
	slli t5, a5, 46
	srai t5, t5, 63
	ld a6, 272(s0)
	xor t5, t5, a6
	xor t6, t4, t1
	or a0, t4, t0
	and a0, t5, a0
	xor t6, t6, a0
	xor a7, t0, t6
	or s1, t1, a7
	xor s1, s1, a7
	and a7, t5, a7
	xor s2, t4, a7
	xor s3, t5, t3
	or s4, s2, s3
	xor s5, t6, s4
	and s6, t3, s5
	or s7, s6, t0
	xor s7, s7, t0
	or s2, s1, s2
	xor s8, s7, s2
	and s9, s8, t2
	xor s9, s9, s5
	xor s4, t4, s4
	or s10, t0, s4
	xor s10, s10, s4
	xor t3, t3, s10
	or s10, t1, s6
	xor s10, s10, s6
	or s10, t3, s10
	or t4, t4, s3
	xor s8, s8, t4
	or a0, a0, s10
	xor s8, s8, a0
	or s5, t5, s5
	and s2, s2, s5
	xor s2, t3, s2
	xori s7, s7, -1
	and s7, s7, s2
	or s1, s1, t2
	xor s1, s1, s7
	xor t6, t6, s2
	or t1, t1, t6
	xor t1, t1, t6
	xori t4, t4, -1
	xor s4, s4, t4
	xor t1, t1, s4
	or t1, t1, t2
	xor t1, t1, t2
	xor t1, t1, s8
	xor t0, t0, a7
	xor t5, t5, t3
	and t0, t0, t5
	xor s6, s6, s4
	xor t0, t0, s6
	or s10, s10, t2
	xor s10, s10, t2
	xor s10, s10, t0
	ld a6, 344(s0)
	xor a6, a6, s9
	sd a6, 344(s0)
	ld a6, 360(s0)
	xor a6, a6, s1
	sd a6, 360(s0)
	ld a6, 200(s0)
	xor a6, a6, t1
	sd a6, 200(s0)
	ld a6, 312(s0)
	xor a6, a6, s10
	sd a6, 312(s0)
	slli t0, a5, 57
	srai t0, t0, 63
	ld a6, 192(s0)
	xor t0, t0, a6
	slli t1, a5, 56
	srai t1, t1, 63
	ld a6, 256(s0)
	xor t1, t1, a6
	slli t2, a5, 55
	srai t2, t2, 63
	ld a6, 320(s0)
	xor t2, t2, a6
	slli t3, a5, 54
	srai t3, t3, 63
	ld a6, 384(s0)
	xor t3, t3, a6
	slli t4, a5, 53
	srai t4, t4, 63
	ld a6, 448(s0)
	xor t4, t4, a6
	slli t5, a5, 52
	srai t5, t5, 63
	ld a6, 16(s0)
	xor t5, t5, a6
	xor t6, t2, t1
	xor a0, t3, t6
	and a7, t0, a0
	and s1, t2, t6
	xor s2, t4, s1
	and s3, a7, s2
	and s4, t0, s1
	xor s5, t3, s4
	or s6, s2, s5
	xor t6, t0, t6
	xor s7, s6, t6
	or s8, t5, s3
	xor s8, s8, s3
	xor s8, s8, s7
	xori a0, a0, -1
	and a0, a0, t1
	or s7, s2, a0
	xor s5, a7, s5
	xor s7, s7, s5
	xor a7, a7, t6
	or t2, t2, a7
	xor t2, t2, a7
	or t6, s2, t2
	xor t6, t6, t2
	xor t1, t1, s5
	xor t6, t6, t1
	or a7, a7, s4
	xor a7, a7, s4
	or t2, t2, a7
	xor s6, t4, s6
	and s6, t6, s6
	xor s6, t2, s6
	and s4, s6, t5
	xor s4, s4, t6
	or s2, s2, t3
	xor s2, s2, t3
	or a7, a7, s2
	or s1, s1, t6
	and a7, a7, s1
	xor s6, s6, a7
	xor a0, a0, t2
	and t0, t0, a0
	or s3, s3, t0
	xor a7, a7, s3
	or t0, a7, t5
	xor t0, t0, t5
	xor t0, t0, s7
	and t4, t4, s3
	xori s7, s7, -1
	xor t4, t4, s7
	xor a7, a7, t4
	or s6, s6, t5
	xor s6, s6, a7
	ld a6, 120(s0)
	xor a6, a6, s8
	sd a6, 120(s0)
	ld a6, 152(s0)
	xor a6, a6, s4
	sd a6, 152(s0)
	ld a6, 296(s0)
	xor a6, a6, s6
	sd a6, 296(s0)
	ld a6, 8(s0)
	xor a6, a6, t0
	sd a6, 8(s0)
	slli t0, a5, 63
	srai t0, t0, 63
	ld a6, 496(s0)
	xor t0, t0, a6
	slli t1, a5, 62
	srai t1, t1, 63
	ld a6, 0(s0)
	xor t1, t1, a6
	slli t2, a5, 61
	srai t2, t2, 63
	ld a6, 64(s0)
	xor t2, t2, a6
	slli t3, a5, 60
	srai t3, t3, 63
	ld a6, 128(s0)
	xor t3, t3, a6
	slli t4, a5, 59
	srai t4, t4, 63
	ld a6, 192(s0)
	xor t4, t4, a6
	slli t5, a5, 58
	srai t5, t5, 63
	ld a6, 256(s0)
	xor t5, t5, a6
	or t6, t3, t4
	xor t6, t6, t4
	or a0, t1, t3
	xor a0, a0, t3
	xor a0, t2, a0
	and a7, t5, a0
	or s1, a7, t6
	xor s1, s1, t6
	or s2, t4, a0
	xor s2, s2, a0
	or s3, t5, s2
	or s4, t4, t3
	xor s4, s4, t3
	xor s4, t1, s4
	and s5, s3, s4
	or a7, a7, s5
	xori a0, a0, -1
	xor s5, s5, a0
	or t3, t3, s3
	xor t3, t3, s3
	xor s5, s5, t3
	xor t6, t6, s5
	or t3, s1, t0
	xor t3, t3, t6
	xor t6, t5, t6
	and s3, t1, t6
	xor s5, t4, s5
	xor s3, s3, s5
	xor s2, s2, s3
	xor s3, a7, s3
	or t4, t4, s3
	xor t1, t1, t6
	xor t4, t4, t1
	and a7, a7, t0
	xor a7, a7, t4
	xor s4, s4, s2
	or s5, t2, s5
	xor s5, s4, s5
	xor t5, t5, s5
	and t5, t5, t0
	xor t5, t5, s2
	or s4, s4, t2
	xor s4, s4, t2
	and t4, t4, s4
	xor s1, s1, s5
	xor t4, t4, s1
	or t4, t4, t0
	xor t4, t4, s2
	ld a6, 216(s0)
	xor a6, a6, t5
	sd a6, 216(s0)
	ld a6, 104(s0)
	xor a6, a6, a7
	sd a6, 104(s0)
	ld a6, 328(s0)
	xor a6, a6, t3
	sd a6, 328(s0)
	ld a6, 248(s0)
	xor a6, a6, t4
	sd a6, 248(s0)
	addi a4, a4, -1
	bnez a4, 29b
	ld t0, 0(s0)
	ld t1, 8(s0)
	sd t1, 0(s0)
	sd t0, 8(s0)
	ld t0, 64(s0)
	ld t1, 72(s0)
	sd t1, 64(s0)
	sd t0, 72(s0)
	ld t0, 128(s0)
	ld t1, 136(s0)
	sd t1, 128(s0)
	sd t0, 136(s0)
	ld t0, 192(s0)
	ld t1, 200(s0)
	sd t1, 192(s0)
	sd t0, 200(s0)
	ld t0, 256(s0)
	ld t1, 264(s0)
	sd t1, 256(s0)
	sd t0, 264(s0)
	ld t0, 320(s0)
	ld t1, 328(s0)
	sd t1, 320(s0)
	sd t0, 328(s0)
	ld t0, 384(s0)
	ld t1, 392(s0)
	sd t1, 384(s0)
	sd t0, 392(s0)
	ld t0, 448(s0)
	ld t1, 456(s0)
	sd t1, 448(s0)
	sd t0, 456(s0)
	ld t0, 16(s0)
	ld t1, 24(s0)
	sd t1, 16(s0)
	sd t0, 24(s0)
	ld t0, 80(s0)
	ld t1, 88(s0)
	sd t1, 80(s0)
	sd t0, 88(s0)
	ld t0, 144(s0)
	ld t1, 152(s0)
	sd t1, 144(s0)
	sd t0, 152(s0)
	ld t0, 208(s0)
	ld t1, 216(s0)
	sd t1, 208(s0)
	sd t0, 216(s0)
	ld t0, 272(s0)
	ld t1, 280(s0)
	sd t1, 272(s0)
	sd t0, 280(s0)
	ld t0, 336(s0)
	ld t1, 344(s0)
	sd t1, 336(s0)
	sd t0, 344(s0)
	ld t0, 400(s0)
	ld t1, 408(s0)
	sd t1, 400(s0)
	sd t0, 408(s0)
	ld t0, 464(s0)
	ld t1, 472(s0)
	sd t1, 464(s0)
	sd t0, 472(s0)
	ld t0, 32(s0)
	ld t1, 40(s0)
	sd t1, 32(s0)
	sd t0, 40(s0)
	ld t0, 96(s0)
	ld t1, 104(s0)
	sd t1, 96(s0)
	sd t0, 104(s0)
	ld t0, 160(s0)
	ld t1, 168(s0)
	sd t1, 160(s0)
	sd t0, 168(s0)
	ld t0, 224(s0)
	ld t1, 232(s0)
	sd t1, 224(s0)
	sd t0, 232(s0)
	ld t0, 288(s0)
	ld t1, 296(s0)
	sd t1, 288(s0)
	sd t0, 296(s0)
	ld t0, 352(s0)
	ld t1, 360(s0)
	sd t1, 352(s0)
	sd t0, 360(s0)
	ld t0, 416(s0)
	ld t1, 424(s0)
	sd t1, 416(s0)
	sd t0, 424(s0)
	ld t0, 480(s0)
	ld t1, 488(s0)
	sd t1, 480(s0)
	sd t0, 488(s0)
	ld t0, 48(s0)
	ld t1, 56(s0)
	sd t1, 48(s0)
	sd t0, 56(s0)
	ld t0, 112(s0)
	ld t1, 120(s0)
	sd t1, 112(s0)
	sd t0, 120(s0)
	ld t0, 176(s0)
	ld t1, 184(s0)
	sd t1, 176(s0)
	sd t0, 184(s0)
	ld t0, 240(s0)
	ld t1, 248(s0)
	sd t1, 240(s0)
	sd t0, 248(s0)
	ld t0, 304(s0)
	ld t1, 312(s0)
	sd t1, 304(s0)
	sd t0, 312(s0)
	ld t0, 368(s0)
	ld t1, 376(s0)
	sd t1, 368(s0)
	sd t0, 376(s0)
	ld t0, 432(s0)
	ld t1, 440(s0)
	sd t1, 432(s0)
	sd t0, 440(s0)
	ld t0, 496(s0)
	ld t1, 504(s0)
	sd t1, 496(s0)
	sd t0, 504(s0)
	addi a0, s0, 896
	ld s1, 0(a0)
	ld s2, 8(a0)
	ld s3, 16(a0)
	ld t0, 0(s0)
	ld t1, 64(s0)
	ld t2, 128(s0)
	ld t3, 192(s0)
	ld t4, 256(s0)
	ld t5, 320(s0)
	ld t6, 384(s0)
	ld a7, 448(s0)
	srli s4, t0, 32
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 32
	xor t0, t0, s4
	srli s4, t1, 32
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 32
	xor t1, t1, s4
	srli s4, t2, 32
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 32
	xor t2, t2, s4
	srli s4, t3, 32
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 32
	xor t3, t3, s4
	srli s4, t0, 16
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 16
	xor t0, t0, s4
	srli s4, t1, 16
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 16
	xor t1, t1, s4
	srli s4, t4, 16
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 16
	xor t4, t4, s4
	srli s4, t5, 16
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 16
	xor t5, t5, s4
	srli s4, t0, 8
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 8
	xor t0, t0, s4
	srli s4, t2, 8
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 8
	xor t2, t2, s4
	srli s4, t4, 8
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 8
	xor t4, t4, s4
	srli s4, t6, 8
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 8
	xor t6, t6, s4
	sd t0, 0(s0)
	sd t1, 64(s0)
	sd t2, 128(s0)
	sd t3, 192(s0)
	sd t4, 256(s0)
	sd t5, 320(s0)
	sd t6, 384(s0)
	sd a7, 448(s0)
	ld t0, 8(s0)
	ld t1, 72(s0)
	ld t2, 136(s0)
	ld t3, 200(s0)
	ld t4, 264(s0)
	ld t5, 328(s0)
	ld t6, 392(s0)
	ld a7, 456(s0)
	srli s4, t0, 32
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 32
	xor t0, t0, s4
	srli s4, t1, 32
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 32
	xor t1, t1, s4
	srli s4, t2, 32
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 32
	xor t2, t2, s4
	srli s4, t3, 32
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 32
	xor t3, t3, s4
	srli s4, t0, 16
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 16
	xor t0, t0, s4
	srli s4, t1, 16
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 16
	xor t1, t1, s4
	srli s4, t4, 16
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 16
	xor t4, t4, s4
	srli s4, t5, 16
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 16
	xor t5, t5, s4
	srli s4, t0, 8
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 8
	xor t0, t0, s4
	srli s4, t2, 8
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 8
	xor t2, t2, s4
	srli s4, t4, 8
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 8
	xor t4, t4, s4
	srli s4, t6, 8
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 8
	xor t6, t6, s4
	sd t0, 8(s0)
	sd t1, 72(s0)
	sd t2, 136(s0)
	sd t3, 200(s0)
	sd t4, 264(s0)
	sd t5, 328(s0)
	sd t6, 392(s0)
	sd a7, 456(s0)
	ld t0, 16(s0)
	ld t1, 80(s0)
	ld t2, 144(s0)
	ld t3, 208(s0)
	ld t4, 272(s0)
	ld t5, 336(s0)
	ld t6, 400(s0)
	ld a7, 464(s0)
	srli s4, t0, 32
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 32
	xor t0, t0, s4
	srli s4, t1, 32
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 32
	xor t1, t1, s4
	srli s4, t2, 32
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 32
	xor t2, t2, s4
	srli s4, t3, 32
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 32
	xor t3, t3, s4
	srli s4, t0, 16
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 16
	xor t0, t0, s4
	srli s4, t1, 16
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 16
	xor t1, t1, s4
	srli s4, t4, 16
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 16
	xor t4, t4, s4
	srli s4, t5, 16
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 16
	xor t5, t5, s4
	srli s4, t0, 8
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 8
	xor t0, t0, s4
	srli s4, t2, 8
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 8
	xor t2, t2, s4
	srli s4, t4, 8
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 8
	xor t4, t4, s4
	srli s4, t6, 8
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 8
	xor t6, t6, s4
	sd t0, 16(s0)
	sd t1, 80(s0)
	sd t2, 144(s0)
	sd t3, 208(s0)
	sd t4, 272(s0)
	sd t5, 336(s0)
	sd t6, 400(s0)
	sd a7, 464(s0)
	ld t0, 24(s0)
	ld t1, 88(s0)
	ld t2, 152(s0)
	ld t3, 216(s0)
	ld t4, 280(s0)
	ld t5, 344(s0)
	ld t6, 408(s0)
	ld a7, 472(s0)
	srli s4, t0, 32
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 32
	xor t0, t0, s4
	srli s4, t1, 32
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 32
	xor t1, t1, s4
	srli s4, t2, 32
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 32
	xor t2, t2, s4
	srli s4, t3, 32
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 32
	xor t3, t3, s4
	srli s4, t0, 16
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 16
	xor t0, t0, s4
	srli s4, t1, 16
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 16
	xor t1, t1, s4
	srli s4, t4, 16
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 16
	xor t4, t4, s4
	srli s4, t5, 16
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 16
	xor t5, t5, s4
	srli s4, t0, 8
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 8
	xor t0, t0, s4
	srli s4, t2, 8
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 8
	xor t2, t2, s4
	srli s4, t4, 8
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 8
	xor t4, t4, s4
	srli s4, t6, 8
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 8
	xor t6, t6, s4
	sd t0, 24(s0)
	sd t1, 88(s0)
	sd t2, 152(s0)
	sd t3, 216(s0)
	sd t4, 280(s0)
	sd t5, 344(s0)
	sd t6, 408(s0)
	sd a7, 472(s0)
	ld t0, 32(s0)
	ld t1, 96(s0)
	ld t2, 160(s0)
	ld t3, 224(s0)
	ld t4, 288(s0)
	ld t5, 352(s0)
	ld t6, 416(s0)
	ld a7, 480(s0)
	srli s4, t0, 32
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 32
	xor t0, t0, s4
	srli s4, t1, 32
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 32
	xor t1, t1, s4
	srli s4, t2, 32
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 32
	xor t2, t2, s4
	srli s4, t3, 32
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 32
	xor t3, t3, s4
	srli s4, t0, 16
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 16
	xor t0, t0, s4
	srli s4, t1, 16
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 16
	xor t1, t1, s4
	srli s4, t4, 16
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 16
	xor t4, t4, s4
	srli s4, t5, 16
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 16
	xor t5, t5, s4
	srli s4, t0, 8
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 8
	xor t0, t0, s4
	srli s4, t2, 8
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 8
	xor t2, t2, s4
	srli s4, t4, 8
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 8
	xor t4, t4, s4
	srli s4, t6, 8
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 8
	xor t6, t6, s4
	sd t0, 32(s0)
	sd t1, 96(s0)
	sd t2, 160(s0)
	sd t3, 224(s0)
	sd t4, 288(s0)
	sd t5, 352(s0)
	sd t6, 416(s0)
	sd a7, 480(s0)
	ld t0, 40(s0)
	ld t1, 104(s0)
	ld t2, 168(s0)
	ld t3, 232(s0)
	ld t4, 296(s0)
	ld t5, 360(s0)
	ld t6, 424(s0)
	ld a7, 488(s0)
	srli s4, t0, 32
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 32
	xor t0, t0, s4
	srli s4, t1, 32
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 32
	xor t1, t1, s4
	srli s4, t2, 32
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 32
	xor t2, t2, s4
	srli s4, t3, 32
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 32
	xor t3, t3, s4
	srli s4, t0, 16
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 16
	xor t0, t0, s4
	srli s4, t1, 16
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 16
	xor t1, t1, s4
	srli s4, t4, 16
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 16
	xor t4, t4, s4
	srli s4, t5, 16
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 16
	xor t5, t5, s4
	srli s4, t0, 8
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 8
	xor t0, t0, s4
	srli s4, t2, 8
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 8
	xor t2, t2, s4
	srli s4, t4, 8
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 8
	xor t4, t4, s4
	srli s4, t6, 8
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 8
	xor t6, t6, s4
	sd t0, 40(s0)
	sd t1, 104(s0)
	sd t2, 168(s0)
	sd t3, 232(s0)
	sd t4, 296(s0)
	sd t5, 360(s0)
	sd t6, 424(s0)
	sd a7, 488(s0)
	ld t0, 48(s0)
	ld t1, 112(s0)
	ld t2, 176(s0)
	ld t3, 240(s0)
	ld t4, 304(s0)
	ld t5, 368(s0)
	ld t6, 432(s0)
	ld a7, 496(s0)
	srli s4, t0, 32
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 32
	xor t0, t0, s4
	srli s4, t1, 32
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 32
	xor t1, t1, s4
	srli s4, t2, 32
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 32
	xor t2, t2, s4
	srli s4, t3, 32
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 32
	xor t3, t3, s4
	srli s4, t0, 16
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 16
	xor t0, t0, s4
	srli s4, t1, 16
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 16
	xor t1, t1, s4
	srli s4, t4, 16
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 16
	xor t4, t4, s4
	srli s4, t5, 16
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 16
	xor t5, t5, s4
	srli s4, t0, 8
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 8
	xor t0, t0, s4
	srli s4, t2, 8
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 8
	xor t2, t2, s4
	srli s4, t4, 8
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 8
	xor t4, t4, s4
	srli s4, t6, 8
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 8
	xor t6, t6, s4
	sd t0, 48(s0)
	sd t1, 112(s0)
	sd t2, 176(s0)
	sd t3, 240(s0)
	sd t4, 304(s0)
	sd t5, 368(s0)
	sd t6, 432(s0)
	sd a7, 496(s0)
	ld t0, 56(s0)
	ld t1, 120(s0)
	ld t2, 184(s0)
	ld t3, 248(s0)
	ld t4, 312(s0)
	ld t5, 376(s0)
	ld t6, 440(s0)
	ld a7, 504(s0)
	srli s4, t0, 32
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 32
	xor t0, t0, s4
	srli s4, t1, 32
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 32
	xor t1, t1, s4
	srli s4, t2, 32
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 32
	xor t2, t2, s4
	srli s4, t3, 32
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 32
	xor t3, t3, s4
	srli s4, t0, 16
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 16
	xor t0, t0, s4
	srli s4, t1, 16
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 16
	xor t1, t1, s4
	srli s4, t4, 16
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 16
	xor t4, t4, s4
	srli s4, t5, 16
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 16
	xor t5, t5, s4
	srli s4, t0, 8
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 8
	xor t0, t0, s4
	srli s4, t2, 8
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 8
	xor t2, t2, s4
	srli s4, t4, 8
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 8
	xor t4, t4, s4
	srli s4, t6, 8
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 8
	xor t6, t6, s4
	sd t0, 56(s0)
	sd t1, 120(s0)
	sd t2, 184(s0)
	sd t3, 248(s0)
	sd t4, 312(s0)
	sd t5, 376(s0)
	sd t6, 440(s0)
	sd a7, 504(s0)
	ld s1, 24(a0)
	ld s2, 32(a0)
	ld s3, 40(a0)
	ld t0, 0(s0)
	ld t1, 8(s0)
	ld t2, 16(s0)
	ld t3, 24(s0)
	ld t4, 32(s0)
	ld t5, 40(s0)
	ld t6, 48(s0)
	ld a7, 56(s0)
	srli s4, t0, 4
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 4
	xor t0, t0, s4
	srli s4, t1, 4
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 4
	xor t1, t1, s4
	srli s4, t2, 4
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 4
	xor t2, t2, s4
	srli s4, t3, 4
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 4
	xor t3, t3, s4
	srli s4, t0, 2
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 2
	xor t0, t0, s4
	srli s4, t1, 2
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 2
	xor t1, t1, s4
	srli s4, t4, 2
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 2
	xor t4, t4, s4
	srli s4, t5, 2
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 2
	xor t5, t5, s4
	srli s4, t0, 1
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 1
	xor t0, t0, s4
	srli s4, t2, 1
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 1
	xor t2, t2, s4
	srli s4, t4, 1
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 1
	xor t4, t4, s4
	srli s4, t6, 1
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 1
	xor t6, t6, s4
	sd t0, 0(s0)
	sd t1, 8(s0)
	sd t2, 16(s0)
	sd t3, 24(s0)
	sd t4, 32(s0)
	sd t5, 40(s0)
	sd t6, 48(s0)
	sd a7, 56(s0)
	ld t0, 64(s0)
	ld t1, 72(s0)
	ld t2, 80(s0)
	ld t3, 88(s0)
	ld t4, 96(s0)
	ld t5, 104(s0)
	ld t6, 112(s0)
	ld a7, 120(s0)
	srli s4, t0, 4
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 4
	xor t0, t0, s4
	srli s4, t1, 4
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 4
	xor t1, t1, s4
	srli s4, t2, 4
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 4
	xor t2, t2, s4
	srli s4, t3, 4
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 4
	xor t3, t3, s4
	srli s4, t0, 2
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 2
	xor t0, t0, s4
	srli s4, t1, 2
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 2
	xor t1, t1, s4
	srli s4, t4, 2
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 2
	xor t4, t4, s4
	srli s4, t5, 2
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 2
	xor t5, t5, s4
	srli s4, t0, 1
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 1
	xor t0, t0, s4
	srli s4, t2, 1
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 1
	xor t2, t2, s4
	srli s4, t4, 1
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 1
	xor t4, t4, s4
	srli s4, t6, 1
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 1
	xor t6, t6, s4
	sd t0, 64(s0)
	sd t1, 72(s0)
	sd t2, 80(s0)
	sd t3, 88(s0)
	sd t4, 96(s0)
	sd t5, 104(s0)
	sd t6, 112(s0)
	sd a7, 120(s0)
	ld t0, 128(s0)
	ld t1, 136(s0)
	ld t2, 144(s0)
	ld t3, 152(s0)
	ld t4, 160(s0)
	ld t5, 168(s0)
	ld t6, 176(s0)
	ld a7, 184(s0)
	srli s4, t0, 4
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 4
	xor t0, t0, s4
	srli s4, t1, 4
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 4
	xor t1, t1, s4
	srli s4, t2, 4
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 4
	xor t2, t2, s4
	srli s4, t3, 4
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 4
	xor t3, t3, s4
	srli s4, t0, 2
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 2
	xor t0, t0, s4
	srli s4, t1, 2
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 2
	xor t1, t1, s4
	srli s4, t4, 2
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 2
	xor t4, t4, s4
	srli s4, t5, 2
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 2
	xor t5, t5, s4
	srli s4, t0, 1
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 1
	xor t0, t0, s4
	srli s4, t2, 1
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 1
	xor t2, t2, s4
	srli s4, t4, 1
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 1
	xor t4, t4, s4
	srli s4, t6, 1
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 1
	xor t6, t6, s4
	sd t0, 128(s0)
	sd t1, 136(s0)
	sd t2, 144(s0)
	sd t3, 152(s0)
	sd t4, 160(s0)
	sd t5, 168(s0)
	sd t6, 176(s0)
	sd a7, 184(s0)
	ld t0, 192(s0)
	ld t1, 200(s0)
	ld t2, 208(s0)
	ld t3, 216(s0)
	ld t4, 224(s0)
	ld t5, 232(s0)
	ld t6, 240(s0)
	ld a7, 248(s0)
	srli s4, t0, 4
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 4
	xor t0, t0, s4
	srli s4, t1, 4
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 4
	xor t1, t1, s4
	srli s4, t2, 4
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 4
	xor t2, t2, s4
	srli s4, t3, 4
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 4
	xor t3, t3, s4
	srli s4, t0, 2
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 2
	xor t0, t0, s4
	srli s4, t1, 2
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 2
	xor t1, t1, s4
	srli s4, t4, 2
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 2
	xor t4, t4, s4
	srli s4, t5, 2
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 2
	xor t5, t5, s4
	srli s4, t0, 1
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 1
	xor t0, t0, s4
	srli s4, t2, 1
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 1
	xor t2, t2, s4
	srli s4, t4, 1
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 1
	xor t4, t4, s4
	srli s4, t6, 1
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 1
	xor t6, t6, s4
	sd t0, 192(s0)
	sd t1, 200(s0)
	sd t2, 208(s0)
	sd t3, 216(s0)
	sd t4, 224(s0)
	sd t5, 232(s0)
	sd t6, 240(s0)
	sd a7, 248(s0)
	ld t0, 256(s0)
	ld t1, 264(s0)
	ld t2, 272(s0)
	ld t3, 280(s0)
	ld t4, 288(s0)
	ld t5, 296(s0)
	ld t6, 304(s0)
	ld a7, 312(s0)
	srli s4, t0, 4
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 4
	xor t0, t0, s4
	srli s4, t1, 4
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 4
	xor t1, t1, s4
	srli s4, t2, 4
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 4
	xor t2, t2, s4
	srli s4, t3, 4
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 4
	xor t3, t3, s4
	srli s4, t0, 2
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 2
	xor t0, t0, s4
	srli s4, t1, 2
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 2
	xor t1, t1, s4
	srli s4, t4, 2
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 2
	xor t4, t4, s4
	srli s4, t5, 2
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 2
	xor t5, t5, s4
	srli s4, t0, 1
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 1
	xor t0, t0, s4
	srli s4, t2, 1
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 1
	xor t2, t2, s4
	srli s4, t4, 1
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 1
	xor t4, t4, s4
	srli s4, t6, 1
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 1
	xor t6, t6, s4
	sd t0, 256(s0)
	sd t1, 264(s0)
	sd t2, 272(s0)
	sd t3, 280(s0)
	sd t4, 288(s0)
	sd t5, 296(s0)
	sd t6, 304(s0)
	sd a7, 312(s0)
	ld t0, 320(s0)
	ld t1, 328(s0)
	ld t2, 336(s0)
	ld t3, 344(s0)
	ld t4, 352(s0)
	ld t5, 360(s0)
	ld t6, 368(s0)
	ld a7, 376(s0)
	srli s4, t0, 4
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 4
	xor t0, t0, s4
	srli s4, t1, 4
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 4
	xor t1, t1, s4
	srli s4, t2, 4
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 4
	xor t2, t2, s4
	srli s4, t3, 4
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 4
	xor t3, t3, s4
	srli s4, t0, 2
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 2
	xor t0, t0, s4
	srli s4, t1, 2
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 2
	xor t1, t1, s4
	srli s4, t4, 2
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 2
	xor t4, t4, s4
	srli s4, t5, 2
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 2
	xor t5, t5, s4
	srli s4, t0, 1
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 1
	xor t0, t0, s4
	srli s4, t2, 1
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 1
	xor t2, t2, s4
	srli s4, t4, 1
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 1
	xor t4, t4, s4
	srli s4, t6, 1
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 1
	xor t6, t6, s4
	sd t0, 320(s0)
	sd t1, 328(s0)
	sd t2, 336(s0)
	sd t3, 344(s0)
	sd t4, 352(s0)
	sd t5, 360(s0)
	sd t6, 368(s0)
	sd a7, 376(s0)
	ld t0, 384(s0)
	ld t1, 392(s0)
	ld t2, 400(s0)
	ld t3, 408(s0)
	ld t4, 416(s0)
	ld t5, 424(s0)
	ld t6, 432(s0)
	ld a7, 440(s0)
	srli s4, t0, 4
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 4
	xor t0, t0, s4
	srli s4, t1, 4
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 4
	xor t1, t1, s4
	srli s4, t2, 4
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 4
	xor t2, t2, s4
	srli s4, t3, 4
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 4
	xor t3, t3, s4
	srli s4, t0, 2
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 2
	xor t0, t0, s4
	srli s4, t1, 2
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 2
	xor t1, t1, s4
	srli s4, t4, 2
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 2
	xor t4, t4, s4
	srli s4, t5, 2
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 2
	xor t5, t5, s4
	srli s4, t0, 1
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 1
	xor t0, t0, s4
	srli s4, t2, 1
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 1
	xor t2, t2, s4
	srli s4, t4, 1
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 1
	xor t4, t4, s4
	srli s4, t6, 1
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 1
	xor t6, t6, s4
	sd t0, 384(s0)
	sd t1, 392(s0)
	sd t2, 400(s0)
	sd t3, 408(s0)
	sd t4, 416(s0)
	sd t5, 424(s0)
	sd t6, 432(s0)
	sd a7, 440(s0)
	ld t0, 448(s0)
	ld t1, 456(s0)
	ld t2, 464(s0)
	ld t3, 472(s0)
	ld t4, 480(s0)
	ld t5, 488(s0)
	ld t6, 496(s0)
	ld a7, 504(s0)
	srli s4, t0, 4
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 4
	xor t0, t0, s4
	srli s4, t1, 4
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 4
	xor t1, t1, s4
	srli s4, t2, 4
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 4
	xor t2, t2, s4
	srli s4, t3, 4
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 4
	xor t3, t3, s4
	srli s4, t0, 2
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 2
	xor t0, t0, s4
	srli s4, t1, 2
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 2
	xor t1, t1, s4
	srli s4, t4, 2
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 2
	xor t4, t4, s4
	srli s4, t5, 2
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 2
	xor t5, t5, s4
	srli s4, t0, 1
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 1
	xor t0, t0, s4
	srli s4, t2, 1
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 1
	xor t2, t2, s4
	srli s4, t4, 1
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 1
	xor t4, t4, s4
	srli s4, t6, 1
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 1
	xor t6, t6, s4
	sd t0, 448(s0)
	sd t1, 456(s0)
	sd t2, 464(s0)
	sd t3, 472(s0)
	sd t4, 480(s0)
	sd t5, 488(s0)
	sd t6, 496(s0)
	sd a7, 504(s0)
	srli t0, a2, 6
	beqz t0, 210f
	addi s5, zero, 512
	j 211f
210:
	slli s5, a2, 3
211:
	addi t2, s0, 0
	addi t3, a1, 0
	addi t4, s5, 0
212:
	lbu t1, 0(t2)
	sb t1, 0(t3)
	addi t2, t2, 1
	addi t3, t3, 1
	addi t4, t4, -1
	bnez t4, 212b
	add a1, a1, s5
	srli t0, s5, 3
	sub a2, a2, t0
	bnez a2, 23b
	addi t1, zero, 0
	addi t0, s0, 0
	addi t4, zero, 118
213:
	sd t1, 0(t0)
	addi t0, t0, 8
	addi t4, t4, -1
	bnez t4, 213b
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
	addi a0, s0, 896
	ld s1, 0(a0)
	ld s2, 8(a0)
	ld s3, 16(a0)
	ld t0, 0(s0)
	ld t1, 64(s0)
	ld t2, 128(s0)
	ld t3, 192(s0)
	ld t4, 256(s0)
	ld t5, 320(s0)
	ld t6, 384(s0)
	ld a7, 448(s0)
	srli s4, t0, 32
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 32
	xor t0, t0, s4
	srli s4, t1, 32
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 32
	xor t1, t1, s4
	srli s4, t2, 32
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 32
	xor t2, t2, s4
	srli s4, t3, 32
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 32
	xor t3, t3, s4
	srli s4, t0, 16
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 16
	xor t0, t0, s4
	srli s4, t1, 16
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 16
	xor t1, t1, s4
	srli s4, t4, 16
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 16
	xor t4, t4, s4
	srli s4, t5, 16
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 16
	xor t5, t5, s4
	srli s4, t0, 8
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 8
	xor t0, t0, s4
	srli s4, t2, 8
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 8
	xor t2, t2, s4
	srli s4, t4, 8
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 8
	xor t4, t4, s4
	srli s4, t6, 8
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 8
	xor t6, t6, s4
	sd t0, 0(s0)
	sd t1, 64(s0)
	sd t2, 128(s0)
	sd t3, 192(s0)
	sd t4, 256(s0)
	sd t5, 320(s0)
	sd t6, 384(s0)
	sd a7, 448(s0)
	ld t0, 8(s0)
	ld t1, 72(s0)
	ld t2, 136(s0)
	ld t3, 200(s0)
	ld t4, 264(s0)
	ld t5, 328(s0)
	ld t6, 392(s0)
	ld a7, 456(s0)
	srli s4, t0, 32
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 32
	xor t0, t0, s4
	srli s4, t1, 32
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 32
	xor t1, t1, s4
	srli s4, t2, 32
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 32
	xor t2, t2, s4
	srli s4, t3, 32
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 32
	xor t3, t3, s4
	srli s4, t0, 16
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 16
	xor t0, t0, s4
	srli s4, t1, 16
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 16
	xor t1, t1, s4
	srli s4, t4, 16
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 16
	xor t4, t4, s4
	srli s4, t5, 16
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 16
	xor t5, t5, s4
	srli s4, t0, 8
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 8
	xor t0, t0, s4
	srli s4, t2, 8
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 8
	xor t2, t2, s4
	srli s4, t4, 8
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 8
	xor t4, t4, s4
	srli s4, t6, 8
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 8
	xor t6, t6, s4
	sd t0, 8(s0)
	sd t1, 72(s0)
	sd t2, 136(s0)
	sd t3, 200(s0)
	sd t4, 264(s0)
	sd t5, 328(s0)
	sd t6, 392(s0)
	sd a7, 456(s0)
	ld t0, 16(s0)
	ld t1, 80(s0)
	ld t2, 144(s0)
	ld t3, 208(s0)
	ld t4, 272(s0)
	ld t5, 336(s0)
	ld t6, 400(s0)
	ld a7, 464(s0)
	srli s4, t0, 32
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 32
	xor t0, t0, s4
	srli s4, t1, 32
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 32
	xor t1, t1, s4
	srli s4, t2, 32
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 32
	xor t2, t2, s4
	srli s4, t3, 32
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 32
	xor t3, t3, s4
	srli s4, t0, 16
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 16
	xor t0, t0, s4
	srli s4, t1, 16
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 16
	xor t1, t1, s4
	srli s4, t4, 16
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 16
	xor t4, t4, s4
	srli s4, t5, 16
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 16
	xor t5, t5, s4
	srli s4, t0, 8
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 8
	xor t0, t0, s4
	srli s4, t2, 8
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 8
	xor t2, t2, s4
	srli s4, t4, 8
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 8
	xor t4, t4, s4
	srli s4, t6, 8
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 8
	xor t6, t6, s4
	sd t0, 16(s0)
	sd t1, 80(s0)
	sd t2, 144(s0)
	sd t3, 208(s0)
	sd t4, 272(s0)
	sd t5, 336(s0)
	sd t6, 400(s0)
	sd a7, 464(s0)
	ld t0, 24(s0)
	ld t1, 88(s0)
	ld t2, 152(s0)
	ld t3, 216(s0)
	ld t4, 280(s0)
	ld t5, 344(s0)
	ld t6, 408(s0)
	ld a7, 472(s0)
	srli s4, t0, 32
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 32
	xor t0, t0, s4
	srli s4, t1, 32
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 32
	xor t1, t1, s4
	srli s4, t2, 32
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 32
	xor t2, t2, s4
	srli s4, t3, 32
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 32
	xor t3, t3, s4
	srli s4, t0, 16
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 16
	xor t0, t0, s4
	srli s4, t1, 16
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 16
	xor t1, t1, s4
	srli s4, t4, 16
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 16
	xor t4, t4, s4
	srli s4, t5, 16
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 16
	xor t5, t5, s4
	srli s4, t0, 8
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 8
	xor t0, t0, s4
	srli s4, t2, 8
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 8
	xor t2, t2, s4
	srli s4, t4, 8
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 8
	xor t4, t4, s4
	srli s4, t6, 8
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 8
	xor t6, t6, s4
	sd t0, 24(s0)
	sd t1, 88(s0)
	sd t2, 152(s0)
	sd t3, 216(s0)
	sd t4, 280(s0)
	sd t5, 344(s0)
	sd t6, 408(s0)
	sd a7, 472(s0)
	ld t0, 32(s0)
	ld t1, 96(s0)
	ld t2, 160(s0)
	ld t3, 224(s0)
	ld t4, 288(s0)
	ld t5, 352(s0)
	ld t6, 416(s0)
	ld a7, 480(s0)
	srli s4, t0, 32
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 32
	xor t0, t0, s4
	srli s4, t1, 32
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 32
	xor t1, t1, s4
	srli s4, t2, 32
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 32
	xor t2, t2, s4
	srli s4, t3, 32
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 32
	xor t3, t3, s4
	srli s4, t0, 16
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 16
	xor t0, t0, s4
	srli s4, t1, 16
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 16
	xor t1, t1, s4
	srli s4, t4, 16
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 16
	xor t4, t4, s4
	srli s4, t5, 16
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 16
	xor t5, t5, s4
	srli s4, t0, 8
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 8
	xor t0, t0, s4
	srli s4, t2, 8
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 8
	xor t2, t2, s4
	srli s4, t4, 8
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 8
	xor t4, t4, s4
	srli s4, t6, 8
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 8
	xor t6, t6, s4
	sd t0, 32(s0)
	sd t1, 96(s0)
	sd t2, 160(s0)
	sd t3, 224(s0)
	sd t4, 288(s0)
	sd t5, 352(s0)
	sd t6, 416(s0)
	sd a7, 480(s0)
	ld t0, 40(s0)
	ld t1, 104(s0)
	ld t2, 168(s0)
	ld t3, 232(s0)
	ld t4, 296(s0)
	ld t5, 360(s0)
	ld t6, 424(s0)
	ld a7, 488(s0)
	srli s4, t0, 32
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 32
	xor t0, t0, s4
	srli s4, t1, 32
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 32
	xor t1, t1, s4
	srli s4, t2, 32
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 32
	xor t2, t2, s4
	srli s4, t3, 32
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 32
	xor t3, t3, s4
	srli s4, t0, 16
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 16
	xor t0, t0, s4
	srli s4, t1, 16
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 16
	xor t1, t1, s4
	srli s4, t4, 16
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 16
	xor t4, t4, s4
	srli s4, t5, 16
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 16
	xor t5, t5, s4
	srli s4, t0, 8
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 8
	xor t0, t0, s4
	srli s4, t2, 8
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 8
	xor t2, t2, s4
	srli s4, t4, 8
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 8
	xor t4, t4, s4
	srli s4, t6, 8
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 8
	xor t6, t6, s4
	sd t0, 40(s0)
	sd t1, 104(s0)
	sd t2, 168(s0)
	sd t3, 232(s0)
	sd t4, 296(s0)
	sd t5, 360(s0)
	sd t6, 424(s0)
	sd a7, 488(s0)
	ld t0, 48(s0)
	ld t1, 112(s0)
	ld t2, 176(s0)
	ld t3, 240(s0)
	ld t4, 304(s0)
	ld t5, 368(s0)
	ld t6, 432(s0)
	ld a7, 496(s0)
	srli s4, t0, 32
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 32
	xor t0, t0, s4
	srli s4, t1, 32
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 32
	xor t1, t1, s4
	srli s4, t2, 32
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 32
	xor t2, t2, s4
	srli s4, t3, 32
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 32
	xor t3, t3, s4
	srli s4, t0, 16
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 16
	xor t0, t0, s4
	srli s4, t1, 16
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 16
	xor t1, t1, s4
	srli s4, t4, 16
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 16
	xor t4, t4, s4
	srli s4, t5, 16
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 16
	xor t5, t5, s4
	srli s4, t0, 8
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 8
	xor t0, t0, s4
	srli s4, t2, 8
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 8
	xor t2, t2, s4
	srli s4, t4, 8
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 8
	xor t4, t4, s4
	srli s4, t6, 8
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 8
	xor t6, t6, s4
	sd t0, 48(s0)
	sd t1, 112(s0)
	sd t2, 176(s0)
	sd t3, 240(s0)
	sd t4, 304(s0)
	sd t5, 368(s0)
	sd t6, 432(s0)
	sd a7, 496(s0)
	ld t0, 56(s0)
	ld t1, 120(s0)
	ld t2, 184(s0)
	ld t3, 248(s0)
	ld t4, 312(s0)
	ld t5, 376(s0)
	ld t6, 440(s0)
	ld a7, 504(s0)
	srli s4, t0, 32
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 32
	xor t0, t0, s4
	srli s4, t1, 32
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 32
	xor t1, t1, s4
	srli s4, t2, 32
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 32
	xor t2, t2, s4
	srli s4, t3, 32
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 32
	xor t3, t3, s4
	srli s4, t0, 16
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 16
	xor t0, t0, s4
	srli s4, t1, 16
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 16
	xor t1, t1, s4
	srli s4, t4, 16
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 16
	xor t4, t4, s4
	srli s4, t5, 16
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 16
	xor t5, t5, s4
	srli s4, t0, 8
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 8
	xor t0, t0, s4
	srli s4, t2, 8
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 8
	xor t2, t2, s4
	srli s4, t4, 8
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 8
	xor t4, t4, s4
	srli s4, t6, 8
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 8
	xor t6, t6, s4
	sd t0, 56(s0)
	sd t1, 120(s0)
	sd t2, 184(s0)
	sd t3, 248(s0)
	sd t4, 312(s0)
	sd t5, 376(s0)
	sd t6, 440(s0)
	sd a7, 504(s0)
	ld s1, 24(a0)
	ld s2, 32(a0)
	ld s3, 40(a0)
	ld t0, 0(s0)
	ld t1, 8(s0)
	ld t2, 16(s0)
	ld t3, 24(s0)
	ld t4, 32(s0)
	ld t5, 40(s0)
	ld t6, 48(s0)
	ld a7, 56(s0)
	srli s4, t0, 4
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 4
	xor t0, t0, s4
	srli s4, t1, 4
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 4
	xor t1, t1, s4
	srli s4, t2, 4
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 4
	xor t2, t2, s4
	srli s4, t3, 4
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 4
	xor t3, t3, s4
	srli s4, t0, 2
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 2
	xor t0, t0, s4
	srli s4, t1, 2
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 2
	xor t1, t1, s4
	srli s4, t4, 2
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 2
	xor t4, t4, s4
	srli s4, t5, 2
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 2
	xor t5, t5, s4
	srli s4, t0, 1
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 1
	xor t0, t0, s4
	srli s4, t2, 1
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 1
	xor t2, t2, s4
	srli s4, t4, 1
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 1
	xor t4, t4, s4
	srli s4, t6, 1
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 1
	xor t6, t6, s4
	sd t0, 0(s0)
	sd t1, 8(s0)
	sd t2, 16(s0)
	sd t3, 24(s0)
	sd t4, 32(s0)
	sd t5, 40(s0)
	sd t6, 48(s0)
	sd a7, 56(s0)
	ld t0, 64(s0)
	ld t1, 72(s0)
	ld t2, 80(s0)
	ld t3, 88(s0)
	ld t4, 96(s0)
	ld t5, 104(s0)
	ld t6, 112(s0)
	ld a7, 120(s0)
	srli s4, t0, 4
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 4
	xor t0, t0, s4
	srli s4, t1, 4
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 4
	xor t1, t1, s4
	srli s4, t2, 4
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 4
	xor t2, t2, s4
	srli s4, t3, 4
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 4
	xor t3, t3, s4
	srli s4, t0, 2
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 2
	xor t0, t0, s4
	srli s4, t1, 2
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 2
	xor t1, t1, s4
	srli s4, t4, 2
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 2
	xor t4, t4, s4
	srli s4, t5, 2
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 2
	xor t5, t5, s4
	srli s4, t0, 1
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 1
	xor t0, t0, s4
	srli s4, t2, 1
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 1
	xor t2, t2, s4
	srli s4, t4, 1
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 1
	xor t4, t4, s4
	srli s4, t6, 1
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 1
	xor t6, t6, s4
	sd t0, 64(s0)
	sd t1, 72(s0)
	sd t2, 80(s0)
	sd t3, 88(s0)
	sd t4, 96(s0)
	sd t5, 104(s0)
	sd t6, 112(s0)
	sd a7, 120(s0)
	ld t0, 128(s0)
	ld t1, 136(s0)
	ld t2, 144(s0)
	ld t3, 152(s0)
	ld t4, 160(s0)
	ld t5, 168(s0)
	ld t6, 176(s0)
	ld a7, 184(s0)
	srli s4, t0, 4
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 4
	xor t0, t0, s4
	srli s4, t1, 4
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 4
	xor t1, t1, s4
	srli s4, t2, 4
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 4
	xor t2, t2, s4
	srli s4, t3, 4
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 4
	xor t3, t3, s4
	srli s4, t0, 2
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 2
	xor t0, t0, s4
	srli s4, t1, 2
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 2
	xor t1, t1, s4
	srli s4, t4, 2
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 2
	xor t4, t4, s4
	srli s4, t5, 2
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 2
	xor t5, t5, s4
	srli s4, t0, 1
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 1
	xor t0, t0, s4
	srli s4, t2, 1
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 1
	xor t2, t2, s4
	srli s4, t4, 1
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 1
	xor t4, t4, s4
	srli s4, t6, 1
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 1
	xor t6, t6, s4
	sd t0, 128(s0)
	sd t1, 136(s0)
	sd t2, 144(s0)
	sd t3, 152(s0)
	sd t4, 160(s0)
	sd t5, 168(s0)
	sd t6, 176(s0)
	sd a7, 184(s0)
	ld t0, 192(s0)
	ld t1, 200(s0)
	ld t2, 208(s0)
	ld t3, 216(s0)
	ld t4, 224(s0)
	ld t5, 232(s0)
	ld t6, 240(s0)
	ld a7, 248(s0)
	srli s4, t0, 4
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 4
	xor t0, t0, s4
	srli s4, t1, 4
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 4
	xor t1, t1, s4
	srli s4, t2, 4
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 4
	xor t2, t2, s4
	srli s4, t3, 4
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 4
	xor t3, t3, s4
	srli s4, t0, 2
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 2
	xor t0, t0, s4
	srli s4, t1, 2
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 2
	xor t1, t1, s4
	srli s4, t4, 2
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 2
	xor t4, t4, s4
	srli s4, t5, 2
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 2
	xor t5, t5, s4
	srli s4, t0, 1
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 1
	xor t0, t0, s4
	srli s4, t2, 1
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 1
	xor t2, t2, s4
	srli s4, t4, 1
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 1
	xor t4, t4, s4
	srli s4, t6, 1
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 1
	xor t6, t6, s4
	sd t0, 192(s0)
	sd t1, 200(s0)
	sd t2, 208(s0)
	sd t3, 216(s0)
	sd t4, 224(s0)
	sd t5, 232(s0)
	sd t6, 240(s0)
	sd a7, 248(s0)
	ld t0, 256(s0)
	ld t1, 264(s0)
	ld t2, 272(s0)
	ld t3, 280(s0)
	ld t4, 288(s0)
	ld t5, 296(s0)
	ld t6, 304(s0)
	ld a7, 312(s0)
	srli s4, t0, 4
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 4
	xor t0, t0, s4
	srli s4, t1, 4
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 4
	xor t1, t1, s4
	srli s4, t2, 4
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 4
	xor t2, t2, s4
	srli s4, t3, 4
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 4
	xor t3, t3, s4
	srli s4, t0, 2
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 2
	xor t0, t0, s4
	srli s4, t1, 2
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 2
	xor t1, t1, s4
	srli s4, t4, 2
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 2
	xor t4, t4, s4
	srli s4, t5, 2
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 2
	xor t5, t5, s4
	srli s4, t0, 1
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 1
	xor t0, t0, s4
	srli s4, t2, 1
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 1
	xor t2, t2, s4
	srli s4, t4, 1
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 1
	xor t4, t4, s4
	srli s4, t6, 1
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 1
	xor t6, t6, s4
	sd t0, 256(s0)
	sd t1, 264(s0)
	sd t2, 272(s0)
	sd t3, 280(s0)
	sd t4, 288(s0)
	sd t5, 296(s0)
	sd t6, 304(s0)
	sd a7, 312(s0)
	ld t0, 320(s0)
	ld t1, 328(s0)
	ld t2, 336(s0)
	ld t3, 344(s0)
	ld t4, 352(s0)
	ld t5, 360(s0)
	ld t6, 368(s0)
	ld a7, 376(s0)
	srli s4, t0, 4
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 4
	xor t0, t0, s4
	srli s4, t1, 4
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 4
	xor t1, t1, s4
	srli s4, t2, 4
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 4
	xor t2, t2, s4
	srli s4, t3, 4
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 4
	xor t3, t3, s4
	srli s4, t0, 2
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 2
	xor t0, t0, s4
	srli s4, t1, 2
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 2
	xor t1, t1, s4
	srli s4, t4, 2
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 2
	xor t4, t4, s4
	srli s4, t5, 2
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 2
	xor t5, t5, s4
	srli s4, t0, 1
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 1
	xor t0, t0, s4
	srli s4, t2, 1
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 1
	xor t2, t2, s4
	srli s4, t4, 1
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 1
	xor t4, t4, s4
	srli s4, t6, 1
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 1
	xor t6, t6, s4
	sd t0, 320(s0)
	sd t1, 328(s0)
	sd t2, 336(s0)
	sd t3, 344(s0)
	sd t4, 352(s0)
	sd t5, 360(s0)
	sd t6, 368(s0)
	sd a7, 376(s0)
	ld t0, 384(s0)
	ld t1, 392(s0)
	ld t2, 400(s0)
	ld t3, 408(s0)
	ld t4, 416(s0)
	ld t5, 424(s0)
	ld t6, 432(s0)
	ld a7, 440(s0)
	srli s4, t0, 4
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 4
	xor t0, t0, s4
	srli s4, t1, 4
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 4
	xor t1, t1, s4
	srli s4, t2, 4
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 4
	xor t2, t2, s4
	srli s4, t3, 4
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 4
	xor t3, t3, s4
	srli s4, t0, 2
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 2
	xor t0, t0, s4
	srli s4, t1, 2
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 2
	xor t1, t1, s4
	srli s4, t4, 2
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 2
	xor t4, t4, s4
	srli s4, t5, 2
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 2
	xor t5, t5, s4
	srli s4, t0, 1
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 1
	xor t0, t0, s4
	srli s4, t2, 1
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 1
	xor t2, t2, s4
	srli s4, t4, 1
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 1
	xor t4, t4, s4
	srli s4, t6, 1
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 1
	xor t6, t6, s4
	sd t0, 384(s0)
	sd t1, 392(s0)
	sd t2, 400(s0)
	sd t3, 408(s0)
	sd t4, 416(s0)
	sd t5, 424(s0)
	sd t6, 432(s0)
	sd a7, 440(s0)
	ld t0, 448(s0)
	ld t1, 456(s0)
	ld t2, 464(s0)
	ld t3, 472(s0)
	ld t4, 480(s0)
	ld t5, 488(s0)
	ld t6, 496(s0)
	ld a7, 504(s0)
	srli s4, t0, 4
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 4
	xor t0, t0, s4
	srli s4, t1, 4
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 4
	xor t1, t1, s4
	srli s4, t2, 4
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 4
	xor t2, t2, s4
	srli s4, t3, 4
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 4
	xor t3, t3, s4
	srli s4, t0, 2
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 2
	xor t0, t0, s4
	srli s4, t1, 2
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 2
	xor t1, t1, s4
	srli s4, t4, 2
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 2
	xor t4, t4, s4
	srli s4, t5, 2
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 2
	xor t5, t5, s4
	srli s4, t0, 1
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 1
	xor t0, t0, s4
	srli s4, t2, 1
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 1
	xor t2, t2, s4
	srli s4, t4, 1
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 1
	xor t4, t4, s4
	srli s4, t6, 1
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 1
	xor t6, t6, s4
	sd t0, 448(s0)
	sd t1, 456(s0)
	sd t2, 464(s0)
	sd t3, 472(s0)
	sd t4, 480(s0)
	sd t5, 488(s0)
	sd t6, 496(s0)
	sd a7, 504(s0)
	addi a3, s0, 888
	addi a4, zero, 8
27:
	ld a5, 0(a3)
	addi a3, a3, -8
	slli t0, a5, 21
	srai t0, t0, 63
	ld a6, 248(s0)
	xor t0, t0, a6
	slli t1, a5, 20
	srai t1, t1, 63
	ld a6, 312(s0)
	xor t1, t1, a6
	slli t2, a5, 19
	srai t2, t2, 63
	ld a6, 376(s0)
	xor t2, t2, a6
	slli t3, a5, 18
	srai t3, t3, 63
	ld a6, 440(s0)
	xor t3, t3, a6
	slli t4, a5, 17
	srai t4, t4, 63
	ld a6, 504(s0)
	xor t4, t4, a6
	slli t5, a5, 16
	srai t5, t5, 63
	ld a6, 8(s0)
	xor t5, t5, a6
	or t6, t5, t1
	xor t6, t6, t1
	xor a0, t2, t6
	or a7, t3, t0
	xor s1, t5, t3
	and s2, a7, s1
	xor s3, t2, s2
	or s4, s3, a0
	xor s4, s4, a0
	xor s5, t1, t0
	xor s6, t3, s5
	xori s6, s6, -1
	and s6, s6, a0
	or s2, t0, s2
	xor s6, s6, s2
	or s2, s6, s4
	xor s2, s2, s4
	or t0, t5, t0
	or s7, s6, t0
	xori s3, s3, -1
	and s3, s3, t1
	xor s8, s7, s3
	or t2, t2, t0
	xor t2, t2, t0
	xor t2, s3, t2
	xori s1, s1, -1
	and s1, s1, s5
	or t2, t2, s1
	or t3, t3, t6
	xor t3, t3, t6
	xor t6, a0, s7
	or t6, t6, t3
	xor t6, t6, t3
	xori t3, t6, -1
	and s6, a7, s6
	xor t3, t3, s6
	or s8, s8, t4
	xor s8, s8, t4
	xor s8, s8, t3
	xor t6, s5, t6
	or s3, s3, t6
	xor s3, a7, s3
	xor t5, t5, s3
	xor t3, t3, t5
	or s4, s4, t4
	xor s4, s4, t3
	xor a7, a7, s7
	or a7, t2, a7
	xor a7, t5, a7
	or s5, s5, t3
	xor s5, a7, s5
	or t3, s2, t4
	xor t3, t3, s5
	or t1, t1, a0
	or t1, t1, a7
	xor t1, t1, a7
	and s2, s2, t5
	xor t1, t1, s2
	or t1, t1, t4
	xor t1, t1, t2
	ld a6, 64(s0)
	xor a6, a6, t1
	sd a6, 64(s0)
	ld a6, 80(s0)
	xor a6, a6, s8
	sd a6, 80(s0)
	ld a6, 464(s0)
	xor a6, a6, t3
	sd a6, 464(s0)
	ld a6, 480(s0)
	xor a6, a6, s4
	sd a6, 480(s0)
	slli t0, a5, 27
	srai t0, t0, 63
	ld a6, 488(s0)
	xor t0, t0, a6
	slli t1, a5, 26
	srai t1, t1, 63
	ld a6, 56(s0)
	xor t1, t1, a6
	slli t2, a5, 25
	srai t2, t2, 63
	ld a6, 120(s0)
	xor t2, t2, a6
	slli t3, a5, 24
	srai t3, t3, 63
	ld a6, 184(s0)
	xor t3, t3, a6
	slli t4, a5, 23
	srai t4, t4, 63
	ld a6, 248(s0)
	xor t4, t4, a6
	slli t5, a5, 22
	srai t5, t5, 63
	ld a6, 312(s0)
	xor t5, t5, a6
	xor t6, t4, t1
	or a0, t5, t0
	xor a0, a0, t0
	xori a0, a0, -1
	and a0, a0, t1
	or a7, t4, a0
	or s1, t6, t0
	xor s1, s1, t0
	and s2, t5, t6
	xor t1, t1, s2
	or s2, t1, s1
	xor s2, s2, s1
	and s3, t3, t0
	xor a0, a0, s1
	and a0, a7, a0
	or s1, a0, s3
	xor s1, s1, s3
	and s4, t3, a0
	xori t5, t5, -1
	xor t5, s4, t5
	xor t0, t0, t6
	or s5, t0, s3
	xor s5, s5, s3
	xor s6, t5, s5
	xori s1, s1, -1
	and s1, s1, t2
	xor s1, s1, s6
	or t4, t4, s5
	xor t4, t4, s5
	xor t1, t1, t4
	or t5, t5, t1
	xor t5, t5, t1
	xor t3, t3, t0
	xor t5, t5, t3
	or s5, a7, t2
	xor s5, s5, t2
	xor s5, s5, t5
	xor s4, s4, t4
	or t3, t3, s4
	xor a7, a7, s6
	or s3, s3, a7
	xor s4, t3, s3
	xor a0, a0, s6
	xor t5, t5, a0
	and s3, s3, t5
	and t6, t6, t3
	xor s3, s3, t6
	or t6, s3, t2
	xor t6, t6, s4
	or s3, s3, t1
	xor s3, s3, t1
	or t0, t0, a7
	xor s3, s3, t0
	or s2, s2, t2
	xor s2, s2, s3
	ld a6, 400(s0)
	xor a6, a6, s2
	sd a6, 400(s0)
	ld a6, 432(s0)
	xor a6, a6, t6
	sd a6, 432(s0)
	ld a6, 256(s0)
	xor a6, a6, s1
	sd a6, 256(s0)
	ld a6, 224(s0)
	xor a6, a6, s5
	sd a6, 224(s0)
	slli t0, a5, 33
	srai t0, t0, 63
	ld a6, 232(s0)
	xor t0, t0, a6
	slli t1, a5, 32
	srai t1, t1, 63
	ld a6, 296(s0)
	xor t1, t1, a6
	slli t2, a5, 31
	srai t2, t2, 63
	ld a6, 360(s0)
	xor t2, t2, a6
	slli t3, a5, 30
	srai t3, t3, 63
	ld a6, 424(s0)
	xor t3, t3, a6
	slli t4, a5, 29
	srai t4, t4, 63
	ld a6, 488(s0)
	xor t4, t4, a6
	slli t5, a5, 28
	srai t5, t5, 63
	ld a6, 56(s0)
	xor t5, t5, a6
	or t6, t5, t4
	xor t6, t6, t4
	xor a0, t3, t0
	or a7, t6, a0
	xor s1, t2, t0
	or s2, s1, t5
	xor s2, s2, t5
	xor s3, a7, s2
	xor s4, t4, a0
	or s5, s4, t0
	xor s5, s5, t0
	xor a7, a7, s5
	or s5, s3, a7
	xor s5, s5, a7
	and s6, t0, s3
	or s6, t2, s6
	and s6, t5, s6
	xor s6, s4, s6
	or s7, s3, t1
	xor s7, s7, t1
	xor s7, s7, s6
	and a0, a0, s1
	xor s1, t5, t2
	xor s8, a7, s1
	or s8, t3, s8
	or s8, s8, a0
	xor s8, s8, a0
	or s2, s2, s1
	or s1, s6, s2
	xor s1, s1, s2
	and t0, t2, t0
	or a0, t0, t4
	xor a0, a0, t4
	xor s1, s1, a0
	and a7, a7, s1
	or t0, s4, t0
	or t0, t0, a7
	xor t0, t0, a7
	xor t5, t5, t0
	and s8, s8, t1
	xor s8, s8, t5
	xori s3, s3, -1
	or t4, t4, s3
	or t3, t3, t4
	xor s4, s4, t3
	xor s2, s2, s4
	xori s5, s5, -1
	and s5, s5, t1
	xor s5, s5, s2
	and t2, t2, s3
	xor s6, s6, t2
	or s4, s4, s6
	xor t6, t6, t5
	xor s4, s4, t6
	or s1, s1, t1
	xor s1, s1, s4
	ld a6, 176(s0)
	xor a6, a6, s7
	sd a6, 176(s0)
	ld a6, 128(s0)
	xor a6, a6, s1
	sd a6, 128(s0)
	ld a6, 32(s0)
	xor a6, a6, s8
	sd a6, 32(s0)
	ld a6, 16(s0)
	xor a6, a6, s5
	sd a6, 16(s0)
	slli t0, a5, 39
	srai t0, t0, 63
	ld a6, 472(s0)
	xor t0, t0, a6
	slli t1, a5, 38
	srai t1, t1, 63
	ld a6, 40(s0)
	xor t1, t1, a6
	slli t2, a5, 37
	srai t2, t2, 63
	ld a6, 104(s0)
	xor t2, t2, a6
	slli t3, a5, 36
	srai t3, t3, 63
	ld a6, 168(s0)
	xor t3, t3, a6
	slli t4, a5, 35
	srai t4, t4, 63
	ld a6, 232(s0)
	xor t4, t4, a6
	slli t5, a5, 34
	srai t5, t5, 63
	ld a6, 296(s0)
	xor t5, t5, a6
	xor t5, t5, t3
	xor t3, t3, t1
	or t6, t4, t2
	xor t6, t1, t6
	xori t6, t6, -1
	and t6, t6, t3
	or a0, t3, t4
	xor a0, a0, t4
	xor a7, t2, a0
	or s1, t5, a7
	or s1, s1, t6
	xor s1, s1, t6
	xor s2, t4, s1
	and a7, a7, s2
	or t3, t3, a7
	xor t3, t3, a7
	xor t5, t5, s2
	xori t3, t3, -1
	and t3, t3, t5
	xor t6, t6, t3
	xor t4, t4, t2
	or t1, t1, a0
	xor t5, t5, t1
	or t1, t5, t4
	xor t1, t1, t4
	xor s1, s1, t1
	or t1, t0, t6
	xor t1, t1, t6
	xor t1, t1, s1
	xori s1, s1, -1
	or a0, t6, t0
	xor a0, a0, t0
	xor a0, a0, s1
	xor t6, t6, s1
	or t6, t6, t4
	xor t6, t6, t4
	or a7, a7, t6
	xor t5, t5, a7
	or a7, s2, t0
	xor a7, a7, t5
	and t0, t0, s2
	xor t0, t0, t5
	ld a6, 496(s0)
	xor a6, a6, t0
	sd a6, 496(s0)
	ld a6, 416(s0)
	xor a6, a6, a7
	sd a6, 416(s0)
	ld a6, 272(s0)
	xor a6, a6, a0
	sd a6, 272(s0)
	ld a6, 384(s0)
	xor a6, a6, t1
	sd a6, 384(s0)
	slli t0, a5, 45
	srai t0, t0, 63
	ld a6, 216(s0)
	xor t0, t0, a6
	slli t1, a5, 44
	srai t1, t1, 63
	ld a6, 280(s0)
	xor t1, t1, a6
	slli t2, a5, 43
	srai t2, t2, 63
	ld a6, 344(s0)
	xor t2, t2, a6
	slli t3, a5, 42
	srai t3, t3, 63
	ld a6, 408(s0)
	xor t3, t3, a6
	slli t4, a5, 41
	srai t4, t4, 63
	ld a6, 472(s0)
	xor t4, t4, a6
	slli t5, a5, 40
	srai t5, t5, 63
	ld a6, 40(s0)
	xor t5, t5, a6
	or t6, t5, t3
	or a0, t6, t0
	xor a0, a0, t0
	xor a7, t5, a0
	xor s1, t3, a7
	or s2, t2, s1
	or a0, a0, t2
	xor a0, a0, t2
	xor t3, t3, a0
	and a0, t1, t3
	or s1, t5, s1
	xor a0, a0, s1
	xor a0, t2, a0
	xor t0, t0, a0
	or s3, a7, t0
	and s4, t1, s3
	xor s5, a7, s4
	and s6, t2, s1
	xor s5, s5, s6
	or s3, s3, t5
	xor s3, s3, t5
	xor s6, t3, s3
	xor t1, t1, s2
	xori s6, s6, -1
	and s6, s6, t1
	xori s6, s6, -1
	or s6, s6, t4
	xor s6, s6, t4
	xor s6, s6, a0
	or a0, t3, s4
	xor a0, a0, s4
	xor s3, s3, t1
	or s3, s5, s3
	or s3, s3, a0
	xor s3, s3, a0
	or a0, s2, s3
	xor a0, a0, s3
	and t0, t0, s3
	xor t1, t1, t0
	and s1, t3, s1
	or s1, t1, s1
	xor s4, s4, s1
	and s4, s4, t4
	xor s4, s4, s5
	xor t5, t5, t6
	xor s3, s3, t5
	and t2, t2, t1
	xor s3, s3, t2
	or a0, a0, t4
	xor a0, a0, s3
	xor t3, s2, t3
	or t3, t3, s3
	xor t3, t3, s3
	xor a7, a7, t1
	xor t3, t3, a7
	and s2, s2, t4
	xor s2, s2, t3
	ld a6, 368(s0)
	xor a6, a6, s4
	sd a6, 368(s0)
	ld a6, 448(s0)
	xor a6, a6, s6
	sd a6, 448(s0)
	ld a6, 160(s0)
	xor a6, a6, s2
	sd a6, 160(s0)
	ld a6, 48(s0)
	xor a6, a6, a0
	sd a6, 48(s0)
	slli t0, a5, 51
	srai t0, t0, 63
	ld a6, 456(s0)
	xor t0, t0, a6
	slli t1, a5, 50
	srai t1, t1, 63
	ld a6, 24(s0)
	xor t1, t1, a6
	slli t2, a5, 49
	srai t2, t2, 63
	ld a6, 88(s0)
	xor t2, t2, a6
	slli t3, a5, 48
	srai t3, t3, 63
	ld a6, 152(s0)
	xor t3, t3, a6
	slli t4, a5, 47
	srai t4, t4, 63
	ld a6, 216(s0)
	xor t4, t4, a6
	slli t5, a5, 46
	srai t5, t5, 63
	ld a6, 280(s0)
	xor t5, t5, a6
	xor t6, t4, t1
	or a0, t4, t0
	and a0, t5, a0
	xor t6, t6, a0
	xor a7, t0, t6
	or s1, t1, a7
	xor s1, s1, a7
	and a7, t5, a7
	xor s2, t4, a7
	xor s3, t5, t3
	or s4, s2, s3
	xor s5, t6, s4
	and s6, t3, s5
	or s7, s6, t0
	xor s7, s7, t0
	or s2, s1, s2
	xor s8, s7, s2
	and s9, s8, t2
	xor s9, s9, s5
	xor s4, t4, s4
	or s10, t0, s4
	xor s10, s10, s4
	xor t3, t3, s10
	or s10, t1, s6
	xor s10, s10, s6
	or s10, t3, s10
	or t4, t4, s3
	xor s8, s8, t4
	or a0, a0, s10
	xor s8, s8, a0
	or s5, t5, s5
	and s2, s2, s5
	xor s2, t3, s2
	xori s7, s7, -1
	and s7, s7, s2
	or s1, s1, t2
	xor s1, s1, s7
	xor t6, t6, s2
	or t1, t1, t6
	xor t1, t1, t6
	xori t4, t4, -1
	xor s4, s4, t4
	xor t1, t1, s4
	or t1, t1, t2
	xor t1, t1, t2
	xor t1, t1, s8
	xor t0, t0, a7
	xor t5, t5, t3
	and t0, t0, t5
	xor s6, s6, s4
	xor t0, t0, s6
	or s10, s10, t2
	xor s10, s10, t2
	xor s10, s10, t0
	ld a6, 336(s0)
	xor a6, a6, s9
	sd a6, 336(s0)
	ld a6, 352(s0)
	xor a6, a6, s1
	sd a6, 352(s0)
	ld a6, 192(s0)
	xor a6, a6, t1
	sd a6, 192(s0)
	ld a6, 304(s0)
	xor a6, a6, s10
	sd a6, 304(s0)
	slli t0, a5, 57
	srai t0, t0, 63
	ld a6, 200(s0)
	xor t0, t0, a6
	slli t1, a5, 56
	srai t1, t1, 63
	ld a6, 264(s0)
	xor t1, t1, a6
	slli t2, a5, 55
	srai t2, t2, 63
	ld a6, 328(s0)
	xor t2, t2, a6
	slli t3, a5, 54
	srai t3, t3, 63
	ld a6, 392(s0)
	xor t3, t3, a6
	slli t4, a5, 53
	srai t4, t4, 63
	ld a6, 456(s0)
	xor t4, t4, a6
	slli t5, a5, 52
	srai t5, t5, 63
	ld a6, 24(s0)
	xor t5, t5, a6
	xor t6, t2, t1
	xor a0, t3, t6
	and a7, t0, a0
	and s1, t2, t6
	xor s2, t4, s1
	and s3, a7, s2
	and s4, t0, s1
	xor s5, t3, s4
	or s6, s2, s5
	xor t6, t0, t6
	xor s7, s6, t6
	or s8, t5, s3
	xor s8, s8, s3
	xor s8, s8, s7
	xori a0, a0, -1
	and a0, a0, t1
	or s7, s2, a0
	xor s5, a7, s5
	xor s7, s7, s5
	xor a7, a7, t6
	or t2, t2, a7
	xor t2, t2, a7
	or t6, s2, t2
	xor t6, t6, t2
	xor t1, t1, s5
	xor t6, t6, t1
	or a7, a7, s4
	xor a7, a7, s4
	or t2, t2, a7
	xor s6, t4, s6
	and s6, t6, s6
	xor s6, t2, s6
	and s4, s6, t5
	xor s4, s4, t6
	or s2, s2, t3
	xor s2, s2, t3
	or a7, a7, s2
	or s1, s1, t6
	and a7, a7, s1
	xor s6, s6, a7
	xor a0, a0, t2
	and t0, t0, a0
	or s3, s3, t0
	xor a7, a7, s3
	or t0, a7, t5
	xor t0, t0, t5
	xor t0, t0, s7
	and t4, t4, s3
	xori s7, s7, -1
	xor t4, t4, s7
	xor a7, a7, t4
	or s6, s6, t5
	xor s6, s6, a7
	ld a6, 112(s0)
	xor a6, a6, s8
	sd a6, 112(s0)
	ld a6, 144(s0)
	xor a6, a6, s4
	sd a6, 144(s0)
	ld a6, 288(s0)
	xor a6, a6, s6
	sd a6, 288(s0)
	ld a6, 0(s0)
	xor a6, a6, t0
	sd a6, 0(s0)
	slli t0, a5, 63
	srai t0, t0, 63
	ld a6, 504(s0)
	xor t0, t0, a6
	slli t1, a5, 62
	srai t1, t1, 63
	ld a6, 8(s0)
	xor t1, t1, a6
	slli t2, a5, 61
	srai t2, t2, 63
	ld a6, 72(s0)
	xor t2, t2, a6
	slli t3, a5, 60
	srai t3, t3, 63
	ld a6, 136(s0)
	xor t3, t3, a6
	slli t4, a5, 59
	srai t4, t4, 63
	ld a6, 200(s0)
	xor t4, t4, a6
	slli t5, a5, 58
	srai t5, t5, 63
	ld a6, 264(s0)
	xor t5, t5, a6
	or t6, t3, t4
	xor t6, t6, t4
	or a0, t1, t3
	xor a0, a0, t3
	xor a0, t2, a0
	and a7, t5, a0
	or s1, a7, t6
	xor s1, s1, t6
	or s2, t4, a0
	xor s2, s2, a0
	or s3, t5, s2
	or s4, t4, t3
	xor s4, s4, t3
	xor s4, t1, s4
	and s5, s3, s4
	or a7, a7, s5
	xori a0, a0, -1
	xor s5, s5, a0
	or t3, t3, s3
	xor t3, t3, s3
	xor s5, s5, t3
	xor t6, t6, s5
	or t3, s1, t0
	xor t3, t3, t6
	xor t6, t5, t6
	and s3, t1, t6
	xor s5, t4, s5
	xor s3, s3, s5
	xor s2, s2, s3
	xor s3, a7, s3
	or t4, t4, s3
	xor t1, t1, t6
	xor t4, t4, t1
	and a7, a7, t0
	xor a7, a7, t4
	xor s4, s4, s2
	or s5, t2, s5
	xor s5, s4, s5
	xor t5, t5, s5
	and t5, t5, t0
	xor t5, t5, s2
	or s4, s4, t2
	xor s4, s4, t2
	and t4, t4, s4
	xor s1, s1, s5
	xor t4, t4, s1
	or t4, t4, t0
	xor t4, t4, s2
	ld a6, 208(s0)
	xor a6, a6, t5
	sd a6, 208(s0)
	ld a6, 96(s0)
	xor a6, a6, a7
	sd a6, 96(s0)
	ld a6, 320(s0)
	xor a6, a6, t3
	sd a6, 320(s0)
	ld a6, 240(s0)
	xor a6, a6, t4
	sd a6, 240(s0)
	ld a5, 0(a3)
	addi a3, a3, -8
	slli t0, a5, 21
	srai t0, t0, 63
	ld a6, 240(s0)
	xor t0, t0, a6
	slli t1, a5, 20
	srai t1, t1, 63
	ld a6, 304(s0)
	xor t1, t1, a6
	slli t2, a5, 19
	srai t2, t2, 63
	ld a6, 368(s0)
	xor t2, t2, a6
	slli t3, a5, 18
	srai t3, t3, 63
	ld a6, 432(s0)
	xor t3, t3, a6
	slli t4, a5, 17
	srai t4, t4, 63
	ld a6, 496(s0)
	xor t4, t4, a6
	slli t5, a5, 16
	srai t5, t5, 63
	ld a6, 0(s0)
	xor t5, t5, a6
	or t6, t5, t1
	xor t6, t6, t1
	xor a0, t2, t6
	or a7, t3, t0
	xor s1, t5, t3
	and s2, a7, s1
	xor s3, t2, s2
	or s4, s3, a0
	xor s4, s4, a0
	xor s5, t1, t0
	xor s6, t3, s5
	xori s6, s6, -1
	and s6, s6, a0
	or s2, t0, s2
	xor s6, s6, s2
	or s2, s6, s4
	xor s2, s2, s4
	or t0, t5, t0
	or s7, s6, t0
	xori s3, s3, -1
	and s3, s3, t1
	xor s8, s7, s3
	or t2, t2, t0
	xor t2, t2, t0
	xor t2, s3, t2
	xori s1, s1, -1
	and s1, s1, s5
	or t2, t2, s1
	or t3, t3, t6
	xor t3, t3, t6
	xor t6, a0, s7
	or t6, t6, t3
	xor t6, t6, t3
	xori t3, t6, -1
	and s6, a7, s6
	xor t3, t3, s6
	or s8, s8, t4
	xor s8, s8, t4
	xor s8, s8, t3
	xor t6, s5, t6
	or s3, s3, t6
	xor s3, a7, s3
	xor t5, t5, s3
	xor t3, t3, t5
	or s4, s4, t4
	xor s4, s4, t3
	xor a7, a7, s7
	or a7, t2, a7
	xor a7, t5, a7
	or s5, s5, t3
	xor s5, a7, s5
	or t3, s2, t4
	xor t3, t3, s5
	or t1, t1, a0
	or t1, t1, a7
	xor t1, t1, a7
	and s2, s2, t5
	xor t1, t1, s2
	or t1, t1, t4
	xor t1, t1, t2
	ld a6, 72(s0)
	xor a6, a6, t1
	sd a6, 72(s0)
	ld a6, 88(s0)
	xor a6, a6, s8
	sd a6, 88(s0)
	ld a6, 472(s0)
	xor a6, a6, t3
	sd a6, 472(s0)
	ld a6, 488(s0)
	xor a6, a6, s4
	sd a6, 488(s0)
	slli t0, a5, 27
	srai t0, t0, 63
	ld a6, 480(s0)
	xor t0, t0, a6
	slli t1, a5, 26
	srai t1, t1, 63
	ld a6, 48(s0)
	xor t1, t1, a6
	slli t2, a5, 25
	srai t2, t2, 63
	ld a6, 112(s0)
	xor t2, t2, a6
	slli t3, a5, 24
	srai t3, t3, 63
	ld a6, 176(s0)
	xor t3, t3, a6
	slli t4, a5, 23
	srai t4, t4, 63
	ld a6, 240(s0)
	xor t4, t4, a6
	slli t5, a5, 22
	srai t5, t5, 63
	ld a6, 304(s0)
	xor t5, t5, a6
	xor t6, t4, t1
	or a0, t5, t0
	xor a0, a0, t0
	xori a0, a0, -1
	and a0, a0, t1
	or a7, t4, a0
	or s1, t6, t0
	xor s1, s1, t0
	and s2, t5, t6
	xor t1, t1, s2
	or s2, t1, s1
	xor s2, s2, s1
	and s3, t3, t0
	xor a0, a0, s1
	and a0, a7, a0
	or s1, a0, s3
	xor s1, s1, s3
	and s4, t3, a0
	xori t5, t5, -1
	xor t5, s4, t5
	xor t0, t0, t6
	or s5, t0, s3
	xor s5, s5, s3
	xor s6, t5, s5
	xori s1, s1, -1
	and s1, s1, t2
	xor s1, s1, s6
	or t4, t4, s5
	xor t4, t4, s5
	xor t1, t1, t4
	or t5, t5, t1
	xor t5, t5, t1
	xor t3, t3, t0
	xor t5, t5, t3
	or s5, a7, t2
	xor s5, s5, t2
	xor s5, s5, t5
	xor s4, s4, t4
	or t3, t3, s4
	xor a7, a7, s6
	or s3, s3, a7
	xor s4, t3, s3
	xor a0, a0, s6
	xor t5, t5, a0
	and s3, s3, t5
	and t6, t6, t3
	xor s3, s3, t6
	or t6, s3, t2
	xor t6, t6, s4
	or s3, s3, t1
	xor s3, s3, t1
	or t0, t0, a7
	xor s3, s3, t0
	or s2, s2, t2
	xor s2, s2, s3
	ld a6, 408(s0)
	xor a6, a6, s2
	sd a6, 408(s0)
	ld a6, 440(s0)
	xor a6, a6, t6
	sd a6, 440(s0)
	ld a6, 264(s0)
	xor a6, a6, s1
	sd a6, 264(s0)
	ld a6, 232(s0)
	xor a6, a6, s5
	sd a6, 232(s0)
	slli t0, a5, 33
	srai t0, t0, 63
	ld a6, 224(s0)
	xor t0, t0, a6
	slli t1, a5, 32
	srai t1, t1, 63
	ld a6, 288(s0)
	xor t1, t1, a6
	slli t2, a5, 31
	srai t2, t2, 63
	ld a6, 352(s0)
	xor t2, t2, a6
	slli t3, a5, 30
	srai t3, t3, 63
	ld a6, 416(s0)
	xor t3, t3, a6
	slli t4, a5, 29
	srai t4, t4, 63
	ld a6, 480(s0)
	xor t4, t4, a6
	slli t5, a5, 28
	srai t5, t5, 63
	ld a6, 48(s0)
	xor t5, t5, a6
	or t6, t5, t4
	xor t6, t6, t4
	xor a0, t3, t0
	or a7, t6, a0
	xor s1, t2, t0
	or s2, s1, t5
	xor s2, s2, t5
	xor s3, a7, s2
	xor s4, t4, a0
	or s5, s4, t0
	xor s5, s5, t0
	xor a7, a7, s5
	or s5, s3, a7
	xor s5, s5, a7
	and s6, t0, s3
	or s6, t2, s6
	and s6, t5, s6
	xor s6, s4, s6
	or s7, s3, t1
	xor s7, s7, t1
	xor s7, s7, s6
	and a0, a0, s1
	xor s1, t5, t2
	xor s8, a7, s1
	or s8, t3, s8
	or s8, s8, a0
	xor s8, s8, a0
	or s2, s2, s1
	or s1, s6, s2
	xor s1, s1, s2
	and t0, t2, t0
	or a0, t0, t4
	xor a0, a0, t4
	xor s1, s1, a0
	and a7, a7, s1
	or t0, s4, t0
	or t0, t0, a7
	xor t0, t0, a7
	xor t5, t5, t0
	and s8, s8, t1
	xor s8, s8, t5
	xori s3, s3, -1
	or t4, t4, s3
	or t3, t3, t4
	xor s4, s4, t3
	xor s2, s2, s4
	xori s5, s5, -1
	and s5, s5, t1
	xor s5, s5, s2
	and t2, t2, s3
	xor s6, s6, t2
	or s4, s4, s6
	xor t6, t6, t5
	xor s4, s4, t6
	or s1, s1, t1
	xor s1, s1, s4
	ld a6, 184(s0)
	xor a6, a6, s7
	sd a6, 184(s0)
	ld a6, 136(s0)
	xor a6, a6, s1
	sd a6, 136(s0)
	ld a6, 40(s0)
	xor a6, a6, s8
	sd a6, 40(s0)
	ld a6, 24(s0)
	xor a6, a6, s5
	sd a6, 24(s0)
	slli t0, a5, 39
	srai t0, t0, 63
	ld a6, 464(s0)
	xor t0, t0, a6
	slli t1, a5, 38
	srai t1, t1, 63
	ld a6, 32(s0)
	xor t1, t1, a6
	slli t2, a5, 37
	srai t2, t2, 63
	ld a6, 96(s0)
	xor t2, t2, a6
	slli t3, a5, 36
	srai t3, t3, 63
	ld a6, 160(s0)
	xor t3, t3, a6
	slli t4, a5, 35
	srai t4, t4, 63
	ld a6, 224(s0)
	xor t4, t4, a6
	slli t5, a5, 34
	srai t5, t5, 63
	ld a6, 288(s0)
	xor t5, t5, a6
	xor t5, t5, t3
	xor t3, t3, t1
	or t6, t4, t2
	xor t6, t1, t6
	xori t6, t6, -1
	and t6, t6, t3
	or a0, t3, t4
	xor a0, a0, t4
	xor a7, t2, a0
	or s1, t5, a7
	or s1, s1, t6
	xor s1, s1, t6
	xor s2, t4, s1
	and a7, a7, s2
	or t3, t3, a7
	xor t3, t3, a7
	xor t5, t5, s2
	xori t3, t3, -1
	and t3, t3, t5
	xor t6, t6, t3
	xor t4, t4, t2
	or t1, t1, a0
	xor t5, t5, t1
	or t1, t5, t4
	xor t1, t1, t4
	xor s1, s1, t1
	or t1, t0, t6
	xor t1, t1, t6
	xor t1, t1, s1
	xori s1, s1, -1
	or a0, t6, t0
	xor a0, a0, t0
	xor a0, a0, s1
	xor t6, t6, s1
	or t6, t6, t4
	xor t6, t6, t4
	or a7, a7, t6
	xor t5, t5, a7
	or a7, s2, t0
	xor a7, a7, t5
	and t0, t0, s2
	xor t0, t0, t5
	ld a6, 504(s0)
	xor a6, a6, t0
	sd a6, 504(s0)
	ld a6, 424(s0)
	xor a6, a6, a7
	sd a6, 424(s0)
	ld a6, 280(s0)
	xor a6, a6, a0
	sd a6, 280(s0)
	ld a6, 392(s0)
	xor a6, a6, t1
	sd a6, 392(s0)
	slli t0, a5, 45
	srai t0, t0, 63
	ld a6, 208(s0)
	xor t0, t0, a6
	slli t1, a5, 44
	srai t1, t1, 63
	ld a6, 272(s0)
	xor t1, t1, a6
	slli t2, a5, 43
	srai t2, t2, 63
	ld a6, 336(s0)
	xor t2, t2, a6
	slli t3, a5, 42
	srai t3, t3, 63
	ld a6, 400(s0)
	xor t3, t3, a6
	slli t4, a5, 41
	srai t4, t4, 63
	ld a6, 464(s0)
	xor t4, t4, a6
	slli t5, a5, 40
	srai t5, t5, 63
	ld a6, 32(s0)
	xor t5, t5, a6
	or t6, t5, t3
	or a0, t6, t0
	xor a0, a0, t0
	xor a7, t5, a0
	xor s1, t3, a7
	or s2, t2, s1
	or a0, a0, t2
	xor a0, a0, t2
	xor t3, t3, a0
	and a0, t1, t3
	or s1, t5, s1
	xor a0, a0, s1
	xor a0, t2, a0
	xor t0, t0, a0
	or s3, a7, t0
	and s4, t1, s3
	xor s5, a7, s4
	and s6, t2, s1
	xor s5, s5, s6
	or s3, s3, t5
	xor s3, s3, t5
	xor s6, t3, s3
	xor t1, t1, s2
	xori s6, s6, -1
	and s6, s6, t1
	xori s6, s6, -1
	or s6, s6, t4
	xor s6, s6, t4
	xor s6, s6, a0
	or a0, t3, s4
	xor a0, a0, s4
	xor s3, s3, t1
	or s3, s5, s3
	or s3, s3, a0
	xor s3, s3, a0
	or a0, s2, s3
	xor a0, a0, s3
	and t0, t0, s3
	xor t1, t1, t0
	and s1, t3, s1
	or s1, t1, s1
	xor s4, s4, s1
	and s4, s4, t4
	xor s4, s4, s5
	xor t5, t5, t6
	xor s3, s3, t5
	and t2, t2, t1
	xor s3, s3, t2
	or a0, a0, t4
	xor a0, a0, s3
	xor t3, s2, t3
	or t3, t3, s3
	xor t3, t3, s3
	xor a7, a7, t1
	xor t3, t3, a7
	and s2, s2, t4
	xor s2, s2, t3
	ld a6, 376(s0)
	xor a6, a6, s4
	sd a6, 376(s0)
	ld a6, 456(s0)
	xor a6, a6, s6
	sd a6, 456(s0)
	ld a6, 168(s0)
	xor a6, a6, s2
	sd a6, 168(s0)
	ld a6, 56(s0)
	xor a6, a6, a0
	sd a6, 56(s0)
	slli t0, a5, 51
	srai t0, t0, 63
	ld a6, 448(s0)
	xor t0, t0, a6
	slli t1, a5, 50
	srai t1, t1, 63
	ld a6, 16(s0)
	xor t1, t1, a6
	slli t2, a5, 49
	srai t2, t2, 63
	ld a6, 80(s0)
	xor t2, t2, a6
	slli t3, a5, 48
	srai t3, t3, 63
	ld a6, 144(s0)
	xor t3, t3, a6
	slli t4, a5, 47
	srai t4, t4, 63
	ld a6, 208(s0)
	xor t4, t4, a6
	slli t5, a5, 46
	srai t5, t5, 63
	ld a6, 272(s0)
	xor t5, t5, a6
	xor t6, t4, t1
	or a0, t4, t0
	and a0, t5, a0
	xor t6, t6, a0
	xor a7, t0, t6
	or s1, t1, a7
	xor s1, s1, a7
	and a7, t5, a7
	xor s2, t4, a7
	xor s3, t5, t3
	or s4, s2, s3
	xor s5, t6, s4
	and s6, t3, s5
	or s7, s6, t0
	xor s7, s7, t0
	or s2, s1, s2
	xor s8, s7, s2
	and s9, s8, t2
	xor s9, s9, s5
	xor s4, t4, s4
	or s10, t0, s4
	xor s10, s10, s4
	xor t3, t3, s10
	or s10, t1, s6
	xor s10, s10, s6
	or s10, t3, s10
	or t4, t4, s3
	xor s8, s8, t4
	or a0, a0, s10
	xor s8, s8, a0
	or s5, t5, s5
	and s2, s2, s5
	xor s2, t3, s2
	xori s7, s7, -1
	and s7, s7, s2
	or s1, s1, t2
	xor s1, s1, s7
	xor t6, t6, s2
	or t1, t1, t6
	xor t1, t1, t6
	xori t4, t4, -1
	xor s4, s4, t4
	xor t1, t1, s4
	or t1, t1, t2
	xor t1, t1, t2
	xor t1, t1, s8
	xor t0, t0, a7
	xor t5, t5, t3
	and t0, t0, t5
	xor s6, s6, s4
	xor t0, t0, s6
	or s10, s10, t2
	xor s10, s10, t2
	xor s10, s10, t0
	ld a6, 344(s0)
	xor a6, a6, s9
	sd a6, 344(s0)
	ld a6, 360(s0)
	xor a6, a6, s1
	sd a6, 360(s0)
	ld a6, 200(s0)
	xor a6, a6, t1
	sd a6, 200(s0)
	ld a6, 312(s0)
	xor a6, a6, s10
	sd a6, 312(s0)
	slli t0, a5, 57
	srai t0, t0, 63
	ld a6, 192(s0)
	xor t0, t0, a6
	slli t1, a5, 56
	srai t1, t1, 63
	ld a6, 256(s0)
	xor t1, t1, a6
	slli t2, a5, 55
	srai t2, t2, 63
	ld a6, 320(s0)
	xor t2, t2, a6
	slli t3, a5, 54
	srai t3, t3, 63
	ld a6, 384(s0)
	xor t3, t3, a6
	slli t4, a5, 53
	srai t4, t4, 63
	ld a6, 448(s0)
	xor t4, t4, a6
	slli t5, a5, 52
	srai t5, t5, 63
	ld a6, 16(s0)
	xor t5, t5, a6
	xor t6, t2, t1
	xor a0, t3, t6
	and a7, t0, a0
	and s1, t2, t6
	xor s2, t4, s1
	and s3, a7, s2
	and s4, t0, s1
	xor s5, t3, s4
	or s6, s2, s5
	xor t6, t0, t6
	xor s7, s6, t6
	or s8, t5, s3
	xor s8, s8, s3
	xor s8, s8, s7
	xori a0, a0, -1
	and a0, a0, t1
	or s7, s2, a0
	xor s5, a7, s5
	xor s7, s7, s5
	xor a7, a7, t6
	or t2, t2, a7
	xor t2, t2, a7
	or t6, s2, t2
	xor t6, t6, t2
	xor t1, t1, s5
	xor t6, t6, t1
	or a7, a7, s4
	xor a7, a7, s4
	or t2, t2, a7
	xor s6, t4, s6
	and s6, t6, s6
	xor s6, t2, s6
	and s4, s6, t5
	xor s4, s4, t6
	or s2, s2, t3
	xor s2, s2, t3
	or a7, a7, s2
	or s1, s1, t6
	and a7, a7, s1
	xor s6, s6, a7
	xor a0, a0, t2
	and t0, t0, a0
	or s3, s3, t0
	xor a7, a7, s3
	or t0, a7, t5
	xor t0, t0, t5
	xor t0, t0, s7
	and t4, t4, s3
	xori s7, s7, -1
	xor t4, t4, s7
	xor a7, a7, t4
	or s6, s6, t5
	xor s6, s6, a7
	ld a6, 120(s0)
	xor a6, a6, s8
	sd a6, 120(s0)
	ld a6, 152(s0)
	xor a6, a6, s4
	sd a6, 152(s0)
	ld a6, 296(s0)
	xor a6, a6, s6
	sd a6, 296(s0)
	ld a6, 8(s0)
	xor a6, a6, t0
	sd a6, 8(s0)
	slli t0, a5, 63
	srai t0, t0, 63
	ld a6, 496(s0)
	xor t0, t0, a6
	slli t1, a5, 62
	srai t1, t1, 63
	ld a6, 0(s0)
	xor t1, t1, a6
	slli t2, a5, 61
	srai t2, t2, 63
	ld a6, 64(s0)
	xor t2, t2, a6
	slli t3, a5, 60
	srai t3, t3, 63
	ld a6, 128(s0)
	xor t3, t3, a6
	slli t4, a5, 59
	srai t4, t4, 63
	ld a6, 192(s0)
	xor t4, t4, a6
	slli t5, a5, 58
	srai t5, t5, 63
	ld a6, 256(s0)
	xor t5, t5, a6
	or t6, t3, t4
	xor t6, t6, t4
	or a0, t1, t3
	xor a0, a0, t3
	xor a0, t2, a0
	and a7, t5, a0
	or s1, a7, t6
	xor s1, s1, t6
	or s2, t4, a0
	xor s2, s2, a0
	or s3, t5, s2
	or s4, t4, t3
	xor s4, s4, t3
	xor s4, t1, s4
	and s5, s3, s4
	or a7, a7, s5
	xori a0, a0, -1
	xor s5, s5, a0
	or t3, t3, s3
	xor t3, t3, s3
	xor s5, s5, t3
	xor t6, t6, s5
	or t3, s1, t0
	xor t3, t3, t6
	xor t6, t5, t6
	and s3, t1, t6
	xor s5, t4, s5
	xor s3, s3, s5
	xor s2, s2, s3
	xor s3, a7, s3
	or t4, t4, s3
	xor t1, t1, t6
	xor t4, t4, t1
	and a7, a7, t0
	xor a7, a7, t4
	xor s4, s4, s2
	or s5, t2, s5
	xor s5, s4, s5
	xor t5, t5, s5
	and t5, t5, t0
	xor t5, t5, s2
	or s4, s4, t2
	xor s4, s4, t2
	and t4, t4, s4
	xor s1, s1, s5
	xor t4, t4, s1
	or t4, t4, t0
	xor t4, t4, s2
	ld a6, 216(s0)
	xor a6, a6, t5
	sd a6, 216(s0)
	ld a6, 104(s0)
	xor a6, a6, a7
	sd a6, 104(s0)
	ld a6, 328(s0)
	xor a6, a6, t3
	sd a6, 328(s0)
	ld a6, 248(s0)
	xor a6, a6, t4
	sd a6, 248(s0)
	addi a4, a4, -1
	bnez a4, 27b
	ld t0, 0(s0)
	ld t1, 8(s0)
	sd t1, 0(s0)
	sd t0, 8(s0)
	ld t0, 64(s0)
	ld t1, 72(s0)
	sd t1, 64(s0)
	sd t0, 72(s0)
	ld t0, 128(s0)
	ld t1, 136(s0)
	sd t1, 128(s0)
	sd t0, 136(s0)
	ld t0, 192(s0)
	ld t1, 200(s0)
	sd t1, 192(s0)
	sd t0, 200(s0)
	ld t0, 256(s0)
	ld t1, 264(s0)
	sd t1, 256(s0)
	sd t0, 264(s0)
	ld t0, 320(s0)
	ld t1, 328(s0)
	sd t1, 320(s0)
	sd t0, 328(s0)
	ld t0, 384(s0)
	ld t1, 392(s0)
	sd t1, 384(s0)
	sd t0, 392(s0)
	ld t0, 448(s0)
	ld t1, 456(s0)
	sd t1, 448(s0)
	sd t0, 456(s0)
	ld t0, 16(s0)
	ld t1, 24(s0)
	sd t1, 16(s0)
	sd t0, 24(s0)
	ld t0, 80(s0)
	ld t1, 88(s0)
	sd t1, 80(s0)
	sd t0, 88(s0)
	ld t0, 144(s0)
	ld t1, 152(s0)
	sd t1, 144(s0)
	sd t0, 152(s0)
	ld t0, 208(s0)
	ld t1, 216(s0)
	sd t1, 208(s0)
	sd t0, 216(s0)
	ld t0, 272(s0)
	ld t1, 280(s0)
	sd t1, 272(s0)
	sd t0, 280(s0)
	ld t0, 336(s0)
	ld t1, 344(s0)
	sd t1, 336(s0)
	sd t0, 344(s0)
	ld t0, 400(s0)
	ld t1, 408(s0)
	sd t1, 400(s0)
	sd t0, 408(s0)
	ld t0, 464(s0)
	ld t1, 472(s0)
	sd t1, 464(s0)
	sd t0, 472(s0)
	ld t0, 32(s0)
	ld t1, 40(s0)
	sd t1, 32(s0)
	sd t0, 40(s0)
	ld t0, 96(s0)
	ld t1, 104(s0)
	sd t1, 96(s0)
	sd t0, 104(s0)
	ld t0, 160(s0)
	ld t1, 168(s0)
	sd t1, 160(s0)
	sd t0, 168(s0)
	ld t0, 224(s0)
	ld t1, 232(s0)
	sd t1, 224(s0)
	sd t0, 232(s0)
	ld t0, 288(s0)
	ld t1, 296(s0)
	sd t1, 288(s0)
	sd t0, 296(s0)
	ld t0, 352(s0)
	ld t1, 360(s0)
	sd t1, 352(s0)
	sd t0, 360(s0)
	ld t0, 416(s0)
	ld t1, 424(s0)
	sd t1, 416(s0)
	sd t0, 424(s0)
	ld t0, 480(s0)
	ld t1, 488(s0)
	sd t1, 480(s0)
	sd t0, 488(s0)
	ld t0, 48(s0)
	ld t1, 56(s0)
	sd t1, 48(s0)
	sd t0, 56(s0)
	ld t0, 112(s0)
	ld t1, 120(s0)
	sd t1, 112(s0)
	sd t0, 120(s0)
	ld t0, 176(s0)
	ld t1, 184(s0)
	sd t1, 176(s0)
	sd t0, 184(s0)
	ld t0, 240(s0)
	ld t1, 248(s0)
	sd t1, 240(s0)
	sd t0, 248(s0)
	ld t0, 304(s0)
	ld t1, 312(s0)
	sd t1, 304(s0)
	sd t0, 312(s0)
	ld t0, 368(s0)
	ld t1, 376(s0)
	sd t1, 368(s0)
	sd t0, 376(s0)
	ld t0, 432(s0)
	ld t1, 440(s0)
	sd t1, 432(s0)
	sd t0, 440(s0)
	ld t0, 496(s0)
	ld t1, 504(s0)
	sd t1, 496(s0)
	sd t0, 504(s0)
	addi a3, s0, 640
	addi a4, zero, 8
28:
	ld a5, 0(a3)
	addi a3, a3, 8
	slli t0, a5, 21
	srai t0, t0, 63
	ld a6, 248(s0)
	xor t0, t0, a6
	slli t1, a5, 20
	srai t1, t1, 63
	ld a6, 312(s0)
	xor t1, t1, a6
	slli t2, a5, 19
	srai t2, t2, 63
	ld a6, 376(s0)
	xor t2, t2, a6
	slli t3, a5, 18
	srai t3, t3, 63
	ld a6, 440(s0)
	xor t3, t3, a6
	slli t4, a5, 17
	srai t4, t4, 63
	ld a6, 504(s0)
	xor t4, t4, a6
	slli t5, a5, 16
	srai t5, t5, 63
	ld a6, 8(s0)
	xor t5, t5, a6
	or t6, t5, t1
	xor t6, t6, t1
	xor a0, t2, t6
	or a7, t3, t0
	xor s1, t5, t3
	and s2, a7, s1
	xor s3, t2, s2
	or s4, s3, a0
	xor s4, s4, a0
	xor s5, t1, t0
	xor s6, t3, s5
	xori s6, s6, -1
	and s6, s6, a0
	or s2, t0, s2
	xor s6, s6, s2
	or s2, s6, s4
	xor s2, s2, s4
	or t0, t5, t0
	or s7, s6, t0
	xori s3, s3, -1
	and s3, s3, t1
	xor s8, s7, s3
	or t2, t2, t0
	xor t2, t2, t0
	xor t2, s3, t2
	xori s1, s1, -1
	and s1, s1, s5
	or t2, t2, s1
	or t3, t3, t6
	xor t3, t3, t6
	xor t6, a0, s7
	or t6, t6, t3
	xor t6, t6, t3
	xori t3, t6, -1
	and s6, a7, s6
	xor t3, t3, s6
	or s8, s8, t4
	xor s8, s8, t4
	xor s8, s8, t3
	xor t6, s5, t6
	or s3, s3, t6
	xor s3, a7, s3
	xor t5, t5, s3
	xor t3, t3, t5
	or s4, s4, t4
	xor s4, s4, t3
	xor a7, a7, s7
	or a7, t2, a7
	xor a7, t5, a7
	or s5, s5, t3
	xor s5, a7, s5
	or t3, s2, t4
	xor t3, t3, s5
	or t1, t1, a0
	or t1, t1, a7
	xor t1, t1, a7
	and s2, s2, t5
	xor t1, t1, s2
	or t1, t1, t4
	xor t1, t1, t2
	ld a6, 64(s0)
	xor a6, a6, t1
	sd a6, 64(s0)
	ld a6, 80(s0)
	xor a6, a6, s8
	sd a6, 80(s0)
	ld a6, 464(s0)
	xor a6, a6, t3
	sd a6, 464(s0)
	ld a6, 480(s0)
	xor a6, a6, s4
	sd a6, 480(s0)
	slli t0, a5, 27
	srai t0, t0, 63
	ld a6, 488(s0)
	xor t0, t0, a6
	slli t1, a5, 26
	srai t1, t1, 63
	ld a6, 56(s0)
	xor t1, t1, a6
	slli t2, a5, 25
	srai t2, t2, 63
	ld a6, 120(s0)
	xor t2, t2, a6
	slli t3, a5, 24
	srai t3, t3, 63
	ld a6, 184(s0)
	xor t3, t3, a6
	slli t4, a5, 23
	srai t4, t4, 63
	ld a6, 248(s0)
	xor t4, t4, a6
	slli t5, a5, 22
	srai t5, t5, 63
	ld a6, 312(s0)
	xor t5, t5, a6
	xor t6, t4, t1
	or a0, t5, t0
	xor a0, a0, t0
	xori a0, a0, -1
	and a0, a0, t1
	or a7, t4, a0
	or s1, t6, t0
	xor s1, s1, t0
	and s2, t5, t6
	xor t1, t1, s2
	or s2, t1, s1
	xor s2, s2, s1
	and s3, t3, t0
	xor a0, a0, s1
	and a0, a7, a0
	or s1, a0, s3
	xor s1, s1, s3
	and s4, t3, a0
	xori t5, t5, -1
	xor t5, s4, t5
	xor t0, t0, t6
	or s5, t0, s3
	xor s5, s5, s3
	xor s6, t5, s5
	xori s1, s1, -1
	and s1, s1, t2
	xor s1, s1, s6
	or t4, t4, s5
	xor t4, t4, s5
	xor t1, t1, t4
	or t5, t5, t1
	xor t5, t5, t1
	xor t3, t3, t0
	xor t5, t5, t3
	or s5, a7, t2
	xor s5, s5, t2
	xor s5, s5, t5
	xor s4, s4, t4
	or t3, t3, s4
	xor a7, a7, s6
	or s3, s3, a7
	xor s4, t3, s3
	xor a0, a0, s6
	xor t5, t5, a0
	and s3, s3, t5
	and t6, t6, t3
	xor s3, s3, t6
	or t6, s3, t2
	xor t6, t6, s4
	or s3, s3, t1
	xor s3, s3, t1
	or t0, t0, a7
	xor s3, s3, t0
	or s2, s2, t2
	xor s2, s2, s3
	ld a6, 400(s0)
	xor a6, a6, s2
	sd a6, 400(s0)
	ld a6, 432(s0)
	xor a6, a6, t6
	sd a6, 432(s0)
	ld a6, 256(s0)
	xor a6, a6, s1
	sd a6, 256(s0)
	ld a6, 224(s0)
	xor a6, a6, s5
	sd a6, 224(s0)
	slli t0, a5, 33
	srai t0, t0, 63
	ld a6, 232(s0)
	xor t0, t0, a6
	slli t1, a5, 32
	srai t1, t1, 63
	ld a6, 296(s0)
	xor t1, t1, a6
	slli t2, a5, 31
	srai t2, t2, 63
	ld a6, 360(s0)
	xor t2, t2, a6
	slli t3, a5, 30
	srai t3, t3, 63
	ld a6, 424(s0)
	xor t3, t3, a6
	slli t4, a5, 29
	srai t4, t4, 63
	ld a6, 488(s0)
	xor t4, t4, a6
	slli t5, a5, 28
	srai t5, t5, 63
	ld a6, 56(s0)
	xor t5, t5, a6
	or t6, t5, t4
	xor t6, t6, t4
	xor a0, t3, t0
	or a7, t6, a0
	xor s1, t2, t0
	or s2, s1, t5
	xor s2, s2, t5
	xor s3, a7, s2
	xor s4, t4, a0
	or s5, s4, t0
	xor s5, s5, t0
	xor a7, a7, s5
	or s5, s3, a7
	xor s5, s5, a7
	and s6, t0, s3
	or s6, t2, s6
	and s6, t5, s6
	xor s6, s4, s6
	or s7, s3, t1
	xor s7, s7, t1
	xor s7, s7, s6
	and a0, a0, s1
	xor s1, t5, t2
	xor s8, a7, s1
	or s8, t3, s8
	or s8, s8, a0
	xor s8, s8, a0
	or s2, s2, s1
	or s1, s6, s2
	xor s1, s1, s2
	and t0, t2, t0
	or a0, t0, t4
	xor a0, a0, t4
	xor s1, s1, a0
	and a7, a7, s1
	or t0, s4, t0
	or t0, t0, a7
	xor t0, t0, a7
	xor t5, t5, t0
	and s8, s8, t1
	xor s8, s8, t5
	xori s3, s3, -1
	or t4, t4, s3
	or t3, t3, t4
	xor s4, s4, t3
	xor s2, s2, s4
	xori s5, s5, -1
	and s5, s5, t1
	xor s5, s5, s2
	and t2, t2, s3
	xor s6, s6, t2
	or s4, s4, s6
	xor t6, t6, t5
	xor s4, s4, t6
	or s1, s1, t1
	xor s1, s1, s4
	ld a6, 176(s0)
	xor a6, a6, s7
	sd a6, 176(s0)
	ld a6, 128(s0)
	xor a6, a6, s1
	sd a6, 128(s0)
	ld a6, 32(s0)
	xor a6, a6, s8
	sd a6, 32(s0)
	ld a6, 16(s0)
	xor a6, a6, s5
	sd a6, 16(s0)
	slli t0, a5, 39
	srai t0, t0, 63
	ld a6, 472(s0)
	xor t0, t0, a6
	slli t1, a5, 38
	srai t1, t1, 63
	ld a6, 40(s0)
	xor t1, t1, a6
	slli t2, a5, 37
	srai t2, t2, 63
	ld a6, 104(s0)
	xor t2, t2, a6
	slli t3, a5, 36
	srai t3, t3, 63
	ld a6, 168(s0)
	xor t3, t3, a6
	slli t4, a5, 35
	srai t4, t4, 63
	ld a6, 232(s0)
	xor t4, t4, a6
	slli t5, a5, 34
	srai t5, t5, 63
	ld a6, 296(s0)
	xor t5, t5, a6
	xor t5, t5, t3
	xor t3, t3, t1
	or t6, t4, t2
	xor t6, t1, t6
	xori t6, t6, -1
	and t6, t6, t3
	or a0, t3, t4
	xor a0, a0, t4
	xor a7, t2, a0
	or s1, t5, a7
	or s1, s1, t6
	xor s1, s1, t6
	xor s2, t4, s1
	and a7, a7, s2
	or t3, t3, a7
	xor t3, t3, a7
	xor t5, t5, s2
	xori t3, t3, -1
	and t3, t3, t5
	xor t6, t6, t3
	xor t4, t4, t2
	or t1, t1, a0
	xor t5, t5, t1
	or t1, t5, t4
	xor t1, t1, t4
	xor s1, s1, t1
	or t1, t0, t6
	xor t1, t1, t6
	xor t1, t1, s1
	xori s1, s1, -1
	or a0, t6, t0
	xor a0, a0, t0
	xor a0, a0, s1
	xor t6, t6, s1
	or t6, t6, t4
	xor t6, t6, t4
	or a7, a7, t6
	xor t5, t5, a7
	or a7, s2, t0
	xor a7, a7, t5
	and t0, t0, s2
	xor t0, t0, t5
	ld a6, 496(s0)
	xor a6, a6, t0
	sd a6, 496(s0)
	ld a6, 416(s0)
	xor a6, a6, a7
	sd a6, 416(s0)
	ld a6, 272(s0)
	xor a6, a6, a0
	sd a6, 272(s0)
	ld a6, 384(s0)
	xor a6, a6, t1
	sd a6, 384(s0)
	slli t0, a5, 45
	srai t0, t0, 63
	ld a6, 216(s0)
	xor t0, t0, a6
	slli t1, a5, 44
	srai t1, t1, 63
	ld a6, 280(s0)
	xor t1, t1, a6
	slli t2, a5, 43
	srai t2, t2, 63
	ld a6, 344(s0)
	xor t2, t2, a6
	slli t3, a5, 42
	srai t3, t3, 63
	ld a6, 408(s0)
	xor t3, t3, a6
	slli t4, a5, 41
	srai t4, t4, 63
	ld a6, 472(s0)
	xor t4, t4, a6
	slli t5, a5, 40
	srai t5, t5, 63
	ld a6, 40(s0)
	xor t5, t5, a6
	or t6, t5, t3
	or a0, t6, t0
	xor a0, a0, t0
	xor a7, t5, a0
	xor s1, t3, a7
	or s2, t2, s1
	or a0, a0, t2
	xor a0, a0, t2
	xor t3, t3, a0
	and a0, t1, t3
	or s1, t5, s1
	xor a0, a0, s1
	xor a0, t2, a0
	xor t0, t0, a0
	or s3, a7, t0
	and s4, t1, s3
	xor s5, a7, s4
	and s6, t2, s1
	xor s5, s5, s6
	or s3, s3, t5
	xor s3, s3, t5
	xor s6, t3, s3
	xor t1, t1, s2
	xori s6, s6, -1
	and s6, s6, t1
	xori s6, s6, -1
	or s6, s6, t4
	xor s6, s6, t4
	xor s6, s6, a0
	or a0, t3, s4
	xor a0, a0, s4
	xor s3, s3, t1
	or s3, s5, s3
	or s3, s3, a0
	xor s3, s3, a0
	or a0, s2, s3
	xor a0, a0, s3
	and t0, t0, s3
	xor t1, t1, t0
	and s1, t3, s1
	or s1, t1, s1
	xor s4, s4, s1
	and s4, s4, t4
	xor s4, s4, s5
	xor t5, t5, t6
	xor s3, s3, t5
	and t2, t2, t1
	xor s3, s3, t2
	or a0, a0, t4
	xor a0, a0, s3
	xor t3, s2, t3
	or t3, t3, s3
	xor t3, t3, s3
	xor a7, a7, t1
	xor t3, t3, a7
	and s2, s2, t4
	xor s2, s2, t3
	ld a6, 368(s0)
	xor a6, a6, s4
	sd a6, 368(s0)
	ld a6, 448(s0)
	xor a6, a6, s6
	sd a6, 448(s0)
	ld a6, 160(s0)
	xor a6, a6, s2
	sd a6, 160(s0)
	ld a6, 48(s0)
	xor a6, a6, a0
	sd a6, 48(s0)
	slli t0, a5, 51
	srai t0, t0, 63
	ld a6, 456(s0)
	xor t0, t0, a6
	slli t1, a5, 50
	srai t1, t1, 63
	ld a6, 24(s0)
	xor t1, t1, a6
	slli t2, a5, 49
	srai t2, t2, 63
	ld a6, 88(s0)
	xor t2, t2, a6
	slli t3, a5, 48
	srai t3, t3, 63
	ld a6, 152(s0)
	xor t3, t3, a6
	slli t4, a5, 47
	srai t4, t4, 63
	ld a6, 216(s0)
	xor t4, t4, a6
	slli t5, a5, 46
	srai t5, t5, 63
	ld a6, 280(s0)
	xor t5, t5, a6
	xor t6, t4, t1
	or a0, t4, t0
	and a0, t5, a0
	xor t6, t6, a0
	xor a7, t0, t6
	or s1, t1, a7
	xor s1, s1, a7
	and a7, t5, a7
	xor s2, t4, a7
	xor s3, t5, t3
	or s4, s2, s3
	xor s5, t6, s4
	and s6, t3, s5
	or s7, s6, t0
	xor s7, s7, t0
	or s2, s1, s2
	xor s8, s7, s2
	and s9, s8, t2
	xor s9, s9, s5
	xor s4, t4, s4
	or s10, t0, s4
	xor s10, s10, s4
	xor t3, t3, s10
	or s10, t1, s6
	xor s10, s10, s6
	or s10, t3, s10
	or t4, t4, s3
	xor s8, s8, t4
	or a0, a0, s10
	xor s8, s8, a0
	or s5, t5, s5
	and s2, s2, s5
	xor s2, t3, s2
	xori s7, s7, -1
	and s7, s7, s2
	or s1, s1, t2
	xor s1, s1, s7
	xor t6, t6, s2
	or t1, t1, t6
	xor t1, t1, t6
	xori t4, t4, -1
	xor s4, s4, t4
	xor t1, t1, s4
	or t1, t1, t2
	xor t1, t1, t2
	xor t1, t1, s8
	xor t0, t0, a7
	xor t5, t5, t3
	and t0, t0, t5
	xor s6, s6, s4
	xor t0, t0, s6
	or s10, s10, t2
	xor s10, s10, t2
	xor s10, s10, t0
	ld a6, 336(s0)
	xor a6, a6, s9
	sd a6, 336(s0)
	ld a6, 352(s0)
	xor a6, a6, s1
	sd a6, 352(s0)
	ld a6, 192(s0)
	xor a6, a6, t1
	sd a6, 192(s0)
	ld a6, 304(s0)
	xor a6, a6, s10
	sd a6, 304(s0)
	slli t0, a5, 57
	srai t0, t0, 63
	ld a6, 200(s0)
	xor t0, t0, a6
	slli t1, a5, 56
	srai t1, t1, 63
	ld a6, 264(s0)
	xor t1, t1, a6
	slli t2, a5, 55
	srai t2, t2, 63
	ld a6, 328(s0)
	xor t2, t2, a6
	slli t3, a5, 54
	srai t3, t3, 63
	ld a6, 392(s0)
	xor t3, t3, a6
	slli t4, a5, 53
	srai t4, t4, 63
	ld a6, 456(s0)
	xor t4, t4, a6
	slli t5, a5, 52
	srai t5, t5, 63
	ld a6, 24(s0)
	xor t5, t5, a6
	xor t6, t2, t1
	xor a0, t3, t6
	and a7, t0, a0
	and s1, t2, t6
	xor s2, t4, s1
	and s3, a7, s2
	and s4, t0, s1
	xor s5, t3, s4
	or s6, s2, s5
	xor t6, t0, t6
	xor s7, s6, t6
	or s8, t5, s3
	xor s8, s8, s3
	xor s8, s8, s7
	xori a0, a0, -1
	and a0, a0, t1
	or s7, s2, a0
	xor s5, a7, s5
	xor s7, s7, s5
	xor a7, a7, t6
	or t2, t2, a7
	xor t2, t2, a7
	or t6, s2, t2
	xor t6, t6, t2
	xor t1, t1, s5
	xor t6, t6, t1
	or a7, a7, s4
	xor a7, a7, s4
	or t2, t2, a7
	xor s6, t4, s6
	and s6, t6, s6
	xor s6, t2, s6
	and s4, s6, t5
	xor s4, s4, t6
	or s2, s2, t3
	xor s2, s2, t3
	or a7, a7, s2
	or s1, s1, t6
	and a7, a7, s1
	xor s6, s6, a7
	xor a0, a0, t2
	and t0, t0, a0
	or s3, s3, t0
	xor a7, a7, s3
	or t0, a7, t5
	xor t0, t0, t5
	xor t0, t0, s7
	and t4, t4, s3
	xori s7, s7, -1
	xor t4, t4, s7
	xor a7, a7, t4
	or s6, s6, t5
	xor s6, s6, a7
	ld a6, 112(s0)
	xor a6, a6, s8
	sd a6, 112(s0)
	ld a6, 144(s0)
	xor a6, a6, s4
	sd a6, 144(s0)
	ld a6, 288(s0)
	xor a6, a6, s6
	sd a6, 288(s0)
	ld a6, 0(s0)
	xor a6, a6, t0
	sd a6, 0(s0)
	slli t0, a5, 63
	srai t0, t0, 63
	ld a6, 504(s0)
	xor t0, t0, a6
	slli t1, a5, 62
	srai t1, t1, 63
	ld a6, 8(s0)
	xor t1, t1, a6
	slli t2, a5, 61
	srai t2, t2, 63
	ld a6, 72(s0)
	xor t2, t2, a6
	slli t3, a5, 60
	srai t3, t3, 63
	ld a6, 136(s0)
	xor t3, t3, a6
	slli t4, a5, 59
	srai t4, t4, 63
	ld a6, 200(s0)
	xor t4, t4, a6
	slli t5, a5, 58
	srai t5, t5, 63
	ld a6, 264(s0)
	xor t5, t5, a6
	or t6, t3, t4
	xor t6, t6, t4
	or a0, t1, t3
	xor a0, a0, t3
	xor a0, t2, a0
	and a7, t5, a0
	or s1, a7, t6
	xor s1, s1, t6
	or s2, t4, a0
	xor s2, s2, a0
	or s3, t5, s2
	or s4, t4, t3
	xor s4, s4, t3
	xor s4, t1, s4
	and s5, s3, s4
	or a7, a7, s5
	xori a0, a0, -1
	xor s5, s5, a0
	or t3, t3, s3
	xor t3, t3, s3
	xor s5, s5, t3
	xor t6, t6, s5
	or t3, s1, t0
	xor t3, t3, t6
	xor t6, t5, t6
	and s3, t1, t6
	xor s5, t4, s5
	xor s3, s3, s5
	xor s2, s2, s3
	xor s3, a7, s3
	or t4, t4, s3
	xor t1, t1, t6
	xor t4, t4, t1
	and a7, a7, t0
	xor a7, a7, t4
	xor s4, s4, s2
	or s5, t2, s5
	xor s5, s4, s5
	xor t5, t5, s5
	and t5, t5, t0
	xor t5, t5, s2
	or s4, s4, t2
	xor s4, s4, t2
	and t4, t4, s4
	xor s1, s1, s5
	xor t4, t4, s1
	or t4, t4, t0
	xor t4, t4, s2
	ld a6, 208(s0)
	xor a6, a6, t5
	sd a6, 208(s0)
	ld a6, 96(s0)
	xor a6, a6, a7
	sd a6, 96(s0)
	ld a6, 320(s0)
	xor a6, a6, t3
	sd a6, 320(s0)
	ld a6, 240(s0)
	xor a6, a6, t4
	sd a6, 240(s0)
	ld a5, 0(a3)
	addi a3, a3, 8
	slli t0, a5, 21
	srai t0, t0, 63
	ld a6, 240(s0)
	xor t0, t0, a6
	slli t1, a5, 20
	srai t1, t1, 63
	ld a6, 304(s0)
	xor t1, t1, a6
	slli t2, a5, 19
	srai t2, t2, 63
	ld a6, 368(s0)
	xor t2, t2, a6
	slli t3, a5, 18
	srai t3, t3, 63
	ld a6, 432(s0)
	xor t3, t3, a6
	slli t4, a5, 17
	srai t4, t4, 63
	ld a6, 496(s0)
	xor t4, t4, a6
	slli t5, a5, 16
	srai t5, t5, 63
	ld a6, 0(s0)
	xor t5, t5, a6
	or t6, t5, t1
	xor t6, t6, t1
	xor a0, t2, t6
	or a7, t3, t0
	xor s1, t5, t3
	and s2, a7, s1
	xor s3, t2, s2
	or s4, s3, a0
	xor s4, s4, a0
	xor s5, t1, t0
	xor s6, t3, s5
	xori s6, s6, -1
	and s6, s6, a0
	or s2, t0, s2
	xor s6, s6, s2
	or s2, s6, s4
	xor s2, s2, s4
	or t0, t5, t0
	or s7, s6, t0
	xori s3, s3, -1
	and s3, s3, t1
	xor s8, s7, s3
	or t2, t2, t0
	xor t2, t2, t0
	xor t2, s3, t2
	xori s1, s1, -1
	and s1, s1, s5
	or t2, t2, s1
	or t3, t3, t6
	xor t3, t3, t6
	xor t6, a0, s7
	or t6, t6, t3
	xor t6, t6, t3
	xori t3, t6, -1
	and s6, a7, s6
	xor t3, t3, s6
	or s8, s8, t4
	xor s8, s8, t4
	xor s8, s8, t3
	xor t6, s5, t6
	or s3, s3, t6
	xor s3, a7, s3
	xor t5, t5, s3
	xor t3, t3, t5
	or s4, s4, t4
	xor s4, s4, t3
	xor a7, a7, s7
	or a7, t2, a7
	xor a7, t5, a7
	or s5, s5, t3
	xor s5, a7, s5
	or t3, s2, t4
	xor t3, t3, s5
	or t1, t1, a0
	or t1, t1, a7
	xor t1, t1, a7
	and s2, s2, t5
	xor t1, t1, s2
	or t1, t1, t4
	xor t1, t1, t2
	ld a6, 72(s0)
	xor a6, a6, t1
	sd a6, 72(s0)
	ld a6, 88(s0)
	xor a6, a6, s8
	sd a6, 88(s0)
	ld a6, 472(s0)
	xor a6, a6, t3
	sd a6, 472(s0)
	ld a6, 488(s0)
	xor a6, a6, s4
	sd a6, 488(s0)
	slli t0, a5, 27
	srai t0, t0, 63
	ld a6, 480(s0)
	xor t0, t0, a6
	slli t1, a5, 26
	srai t1, t1, 63
	ld a6, 48(s0)
	xor t1, t1, a6
	slli t2, a5, 25
	srai t2, t2, 63
	ld a6, 112(s0)
	xor t2, t2, a6
	slli t3, a5, 24
	srai t3, t3, 63
	ld a6, 176(s0)
	xor t3, t3, a6
	slli t4, a5, 23
	srai t4, t4, 63
	ld a6, 240(s0)
	xor t4, t4, a6
	slli t5, a5, 22
	srai t5, t5, 63
	ld a6, 304(s0)
	xor t5, t5, a6
	xor t6, t4, t1
	or a0, t5, t0
	xor a0, a0, t0
	xori a0, a0, -1
	and a0, a0, t1
	or a7, t4, a0
	or s1, t6, t0
	xor s1, s1, t0
	and s2, t5, t6
	xor t1, t1, s2
	or s2, t1, s1
	xor s2, s2, s1
	and s3, t3, t0
	xor a0, a0, s1
	and a0, a7, a0
	or s1, a0, s3
	xor s1, s1, s3
	and s4, t3, a0
	xori t5, t5, -1
	xor t5, s4, t5
	xor t0, t0, t6
	or s5, t0, s3
	xor s5, s5, s3
	xor s6, t5, s5
	xori s1, s1, -1
	and s1, s1, t2
	xor s1, s1, s6
	or t4, t4, s5
	xor t4, t4, s5
	xor t1, t1, t4
	or t5, t5, t1
	xor t5, t5, t1
	xor t3, t3, t0
	xor t5, t5, t3
	or s5, a7, t2
	xor s5, s5, t2
	xor s5, s5, t5
	xor s4, s4, t4
	or t3, t3, s4
	xor a7, a7, s6
	or s3, s3, a7
	xor s4, t3, s3
	xor a0, a0, s6
	xor t5, t5, a0
	and s3, s3, t5
	and t6, t6, t3
	xor s3, s3, t6
	or t6, s3, t2
	xor t6, t6, s4
	or s3, s3, t1
	xor s3, s3, t1
	or t0, t0, a7
	xor s3, s3, t0
	or s2, s2, t2
	xor s2, s2, s3
	ld a6, 408(s0)
	xor a6, a6, s2
	sd a6, 408(s0)
	ld a6, 440(s0)
	xor a6, a6, t6
	sd a6, 440(s0)
	ld a6, 264(s0)
	xor a6, a6, s1
	sd a6, 264(s0)
	ld a6, 232(s0)
	xor a6, a6, s5
	sd a6, 232(s0)
	slli t0, a5, 33
	srai t0, t0, 63
	ld a6, 224(s0)
	xor t0, t0, a6
	slli t1, a5, 32
	srai t1, t1, 63
	ld a6, 288(s0)
	xor t1, t1, a6
	slli t2, a5, 31
	srai t2, t2, 63
	ld a6, 352(s0)
	xor t2, t2, a6
	slli t3, a5, 30
	srai t3, t3, 63
	ld a6, 416(s0)
	xor t3, t3, a6
	slli t4, a5, 29
	srai t4, t4, 63
	ld a6, 480(s0)
	xor t4, t4, a6
	slli t5, a5, 28
	srai t5, t5, 63
	ld a6, 48(s0)
	xor t5, t5, a6
	or t6, t5, t4
	xor t6, t6, t4
	xor a0, t3, t0
	or a7, t6, a0
	xor s1, t2, t0
	or s2, s1, t5
	xor s2, s2, t5
	xor s3, a7, s2
	xor s4, t4, a0
	or s5, s4, t0
	xor s5, s5, t0
	xor a7, a7, s5
	or s5, s3, a7
	xor s5, s5, a7
	and s6, t0, s3
	or s6, t2, s6
	and s6, t5, s6
	xor s6, s4, s6
	or s7, s3, t1
	xor s7, s7, t1
	xor s7, s7, s6
	and a0, a0, s1
	xor s1, t5, t2
	xor s8, a7, s1
	or s8, t3, s8
	or s8, s8, a0
	xor s8, s8, a0
	or s2, s2, s1
	or s1, s6, s2
	xor s1, s1, s2
	and t0, t2, t0
	or a0, t0, t4
	xor a0, a0, t4
	xor s1, s1, a0
	and a7, a7, s1
	or t0, s4, t0
	or t0, t0, a7
	xor t0, t0, a7
	xor t5, t5, t0
	and s8, s8, t1
	xor s8, s8, t5
	xori s3, s3, -1
	or t4, t4, s3
	or t3, t3, t4
	xor s4, s4, t3
	xor s2, s2, s4
	xori s5, s5, -1
	and s5, s5, t1
	xor s5, s5, s2
	and t2, t2, s3
	xor s6, s6, t2
	or s4, s4, s6
	xor t6, t6, t5
	xor s4, s4, t6
	or s1, s1, t1
	xor s1, s1, s4
	ld a6, 184(s0)
	xor a6, a6, s7
	sd a6, 184(s0)
	ld a6, 136(s0)
	xor a6, a6, s1
	sd a6, 136(s0)
	ld a6, 40(s0)
	xor a6, a6, s8
	sd a6, 40(s0)
	ld a6, 24(s0)
	xor a6, a6, s5
	sd a6, 24(s0)
	slli t0, a5, 39
	srai t0, t0, 63
	ld a6, 464(s0)
	xor t0, t0, a6
	slli t1, a5, 38
	srai t1, t1, 63
	ld a6, 32(s0)
	xor t1, t1, a6
	slli t2, a5, 37
	srai t2, t2, 63
	ld a6, 96(s0)
	xor t2, t2, a6
	slli t3, a5, 36
	srai t3, t3, 63
	ld a6, 160(s0)
	xor t3, t3, a6
	slli t4, a5, 35
	srai t4, t4, 63
	ld a6, 224(s0)
	xor t4, t4, a6
	slli t5, a5, 34
	srai t5, t5, 63
	ld a6, 288(s0)
	xor t5, t5, a6
	xor t5, t5, t3
	xor t3, t3, t1
	or t6, t4, t2
	xor t6, t1, t6
	xori t6, t6, -1
	and t6, t6, t3
	or a0, t3, t4
	xor a0, a0, t4
	xor a7, t2, a0
	or s1, t5, a7
	or s1, s1, t6
	xor s1, s1, t6
	xor s2, t4, s1
	and a7, a7, s2
	or t3, t3, a7
	xor t3, t3, a7
	xor t5, t5, s2
	xori t3, t3, -1
	and t3, t3, t5
	xor t6, t6, t3
	xor t4, t4, t2
	or t1, t1, a0
	xor t5, t5, t1
	or t1, t5, t4
	xor t1, t1, t4
	xor s1, s1, t1
	or t1, t0, t6
	xor t1, t1, t6
	xor t1, t1, s1
	xori s1, s1, -1
	or a0, t6, t0
	xor a0, a0, t0
	xor a0, a0, s1
	xor t6, t6, s1
	or t6, t6, t4
	xor t6, t6, t4
	or a7, a7, t6
	xor t5, t5, a7
	or a7, s2, t0
	xor a7, a7, t5
	and t0, t0, s2
	xor t0, t0, t5
	ld a6, 504(s0)
	xor a6, a6, t0
	sd a6, 504(s0)
	ld a6, 424(s0)
	xor a6, a6, a7
	sd a6, 424(s0)
	ld a6, 280(s0)
	xor a6, a6, a0
	sd a6, 280(s0)
	ld a6, 392(s0)
	xor a6, a6, t1
	sd a6, 392(s0)
	slli t0, a5, 45
	srai t0, t0, 63
	ld a6, 208(s0)
	xor t0, t0, a6
	slli t1, a5, 44
	srai t1, t1, 63
	ld a6, 272(s0)
	xor t1, t1, a6
	slli t2, a5, 43
	srai t2, t2, 63
	ld a6, 336(s0)
	xor t2, t2, a6
	slli t3, a5, 42
	srai t3, t3, 63
	ld a6, 400(s0)
	xor t3, t3, a6
	slli t4, a5, 41
	srai t4, t4, 63
	ld a6, 464(s0)
	xor t4, t4, a6
	slli t5, a5, 40
	srai t5, t5, 63
	ld a6, 32(s0)
	xor t5, t5, a6
	or t6, t5, t3
	or a0, t6, t0
	xor a0, a0, t0
	xor a7, t5, a0
	xor s1, t3, a7
	or s2, t2, s1
	or a0, a0, t2
	xor a0, a0, t2
	xor t3, t3, a0
	and a0, t1, t3
	or s1, t5, s1
	xor a0, a0, s1
	xor a0, t2, a0
	xor t0, t0, a0
	or s3, a7, t0
	and s4, t1, s3
	xor s5, a7, s4
	and s6, t2, s1
	xor s5, s5, s6
	or s3, s3, t5
	xor s3, s3, t5
	xor s6, t3, s3
	xor t1, t1, s2
	xori s6, s6, -1
	and s6, s6, t1
	xori s6, s6, -1
	or s6, s6, t4
	xor s6, s6, t4
	xor s6, s6, a0
	or a0, t3, s4
	xor a0, a0, s4
	xor s3, s3, t1
	or s3, s5, s3
	or s3, s3, a0
	xor s3, s3, a0
	or a0, s2, s3
	xor a0, a0, s3
	and t0, t0, s3
	xor t1, t1, t0
	and s1, t3, s1
	or s1, t1, s1
	xor s4, s4, s1
	and s4, s4, t4
	xor s4, s4, s5
	xor t5, t5, t6
	xor s3, s3, t5
	and t2, t2, t1
	xor s3, s3, t2
	or a0, a0, t4
	xor a0, a0, s3
	xor t3, s2, t3
	or t3, t3, s3
	xor t3, t3, s3
	xor a7, a7, t1
	xor t3, t3, a7
	and s2, s2, t4
	xor s2, s2, t3
	ld a6, 376(s0)
	xor a6, a6, s4
	sd a6, 376(s0)
	ld a6, 456(s0)
	xor a6, a6, s6
	sd a6, 456(s0)
	ld a6, 168(s0)
	xor a6, a6, s2
	sd a6, 168(s0)
	ld a6, 56(s0)
	xor a6, a6, a0
	sd a6, 56(s0)
	slli t0, a5, 51
	srai t0, t0, 63
	ld a6, 448(s0)
	xor t0, t0, a6
	slli t1, a5, 50
	srai t1, t1, 63
	ld a6, 16(s0)
	xor t1, t1, a6
	slli t2, a5, 49
	srai t2, t2, 63
	ld a6, 80(s0)
	xor t2, t2, a6
	slli t3, a5, 48
	srai t3, t3, 63
	ld a6, 144(s0)
	xor t3, t3, a6
	slli t4, a5, 47
	srai t4, t4, 63
	ld a6, 208(s0)
	xor t4, t4, a6
	slli t5, a5, 46
	srai t5, t5, 63
	ld a6, 272(s0)
	xor t5, t5, a6
	xor t6, t4, t1
	or a0, t4, t0
	and a0, t5, a0
	xor t6, t6, a0
	xor a7, t0, t6
	or s1, t1, a7
	xor s1, s1, a7
	and a7, t5, a7
	xor s2, t4, a7
	xor s3, t5, t3
	or s4, s2, s3
	xor s5, t6, s4
	and s6, t3, s5
	or s7, s6, t0
	xor s7, s7, t0
	or s2, s1, s2
	xor s8, s7, s2
	and s9, s8, t2
	xor s9, s9, s5
	xor s4, t4, s4
	or s10, t0, s4
	xor s10, s10, s4
	xor t3, t3, s10
	or s10, t1, s6
	xor s10, s10, s6
	or s10, t3, s10
	or t4, t4, s3
	xor s8, s8, t4
	or a0, a0, s10
	xor s8, s8, a0
	or s5, t5, s5
	and s2, s2, s5
	xor s2, t3, s2
	xori s7, s7, -1
	and s7, s7, s2
	or s1, s1, t2
	xor s1, s1, s7
	xor t6, t6, s2
	or t1, t1, t6
	xor t1, t1, t6
	xori t4, t4, -1
	xor s4, s4, t4
	xor t1, t1, s4
	or t1, t1, t2
	xor t1, t1, t2
	xor t1, t1, s8
	xor t0, t0, a7
	xor t5, t5, t3
	and t0, t0, t5
	xor s6, s6, s4
	xor t0, t0, s6
	or s10, s10, t2
	xor s10, s10, t2
	xor s10, s10, t0
	ld a6, 344(s0)
	xor a6, a6, s9
	sd a6, 344(s0)
	ld a6, 360(s0)
	xor a6, a6, s1
	sd a6, 360(s0)
	ld a6, 200(s0)
	xor a6, a6, t1
	sd a6, 200(s0)
	ld a6, 312(s0)
	xor a6, a6, s10
	sd a6, 312(s0)
	slli t0, a5, 57
	srai t0, t0, 63
	ld a6, 192(s0)
	xor t0, t0, a6
	slli t1, a5, 56
	srai t1, t1, 63
	ld a6, 256(s0)
	xor t1, t1, a6
	slli t2, a5, 55
	srai t2, t2, 63
	ld a6, 320(s0)
	xor t2, t2, a6
	slli t3, a5, 54
	srai t3, t3, 63
	ld a6, 384(s0)
	xor t3, t3, a6
	slli t4, a5, 53
	srai t4, t4, 63
	ld a6, 448(s0)
	xor t4, t4, a6
	slli t5, a5, 52
	srai t5, t5, 63
	ld a6, 16(s0)
	xor t5, t5, a6
	xor t6, t2, t1
	xor a0, t3, t6
	and a7, t0, a0
	and s1, t2, t6
	xor s2, t4, s1
	and s3, a7, s2
	and s4, t0, s1
	xor s5, t3, s4
	or s6, s2, s5
	xor t6, t0, t6
	xor s7, s6, t6
	or s8, t5, s3
	xor s8, s8, s3
	xor s8, s8, s7
	xori a0, a0, -1
	and a0, a0, t1
	or s7, s2, a0
	xor s5, a7, s5
	xor s7, s7, s5
	xor a7, a7, t6
	or t2, t2, a7
	xor t2, t2, a7
	or t6, s2, t2
	xor t6, t6, t2
	xor t1, t1, s5
	xor t6, t6, t1
	or a7, a7, s4
	xor a7, a7, s4
	or t2, t2, a7
	xor s6, t4, s6
	and s6, t6, s6
	xor s6, t2, s6
	and s4, s6, t5
	xor s4, s4, t6
	or s2, s2, t3
	xor s2, s2, t3
	or a7, a7, s2
	or s1, s1, t6
	and a7, a7, s1
	xor s6, s6, a7
	xor a0, a0, t2
	and t0, t0, a0
	or s3, s3, t0
	xor a7, a7, s3
	or t0, a7, t5
	xor t0, t0, t5
	xor t0, t0, s7
	and t4, t4, s3
	xori s7, s7, -1
	xor t4, t4, s7
	xor a7, a7, t4
	or s6, s6, t5
	xor s6, s6, a7
	ld a6, 120(s0)
	xor a6, a6, s8
	sd a6, 120(s0)
	ld a6, 152(s0)
	xor a6, a6, s4
	sd a6, 152(s0)
	ld a6, 296(s0)
	xor a6, a6, s6
	sd a6, 296(s0)
	ld a6, 8(s0)
	xor a6, a6, t0
	sd a6, 8(s0)
	slli t0, a5, 63
	srai t0, t0, 63
	ld a6, 496(s0)
	xor t0, t0, a6
	slli t1, a5, 62
	srai t1, t1, 63
	ld a6, 0(s0)
	xor t1, t1, a6
	slli t2, a5, 61
	srai t2, t2, 63
	ld a6, 64(s0)
	xor t2, t2, a6
	slli t3, a5, 60
	srai t3, t3, 63
	ld a6, 128(s0)
	xor t3, t3, a6
	slli t4, a5, 59
	srai t4, t4, 63
	ld a6, 192(s0)
	xor t4, t4, a6
	slli t5, a5, 58
	srai t5, t5, 63
	ld a6, 256(s0)
	xor t5, t5, a6
	or t6, t3, t4
	xor t6, t6, t4
	or a0, t1, t3
	xor a0, a0, t3
	xor a0, t2, a0
	and a7, t5, a0
	or s1, a7, t6
	xor s1, s1, t6
	or s2, t4, a0
	xor s2, s2, a0
	or s3, t5, s2
	or s4, t4, t3
	xor s4, s4, t3
	xor s4, t1, s4
	and s5, s3, s4
	or a7, a7, s5
	xori a0, a0, -1
	xor s5, s5, a0
	or t3, t3, s3
	xor t3, t3, s3
	xor s5, s5, t3
	xor t6, t6, s5
	or t3, s1, t0
	xor t3, t3, t6
	xor t6, t5, t6
	and s3, t1, t6
	xor s5, t4, s5
	xor s3, s3, s5
	xor s2, s2, s3
	xor s3, a7, s3
	or t4, t4, s3
	xor t1, t1, t6
	xor t4, t4, t1
	and a7, a7, t0
	xor a7, a7, t4
	xor s4, s4, s2
	or s5, t2, s5
	xor s5, s4, s5
	xor t5, t5, s5
	and t5, t5, t0
	xor t5, t5, s2
	or s4, s4, t2
	xor s4, s4, t2
	and t4, t4, s4
	xor s1, s1, s5
	xor t4, t4, s1
	or t4, t4, t0
	xor t4, t4, s2
	ld a6, 216(s0)
	xor a6, a6, t5
	sd a6, 216(s0)
	ld a6, 104(s0)
	xor a6, a6, a7
	sd a6, 104(s0)
	ld a6, 328(s0)
	xor a6, a6, t3
	sd a6, 328(s0)
	ld a6, 248(s0)
	xor a6, a6, t4
	sd a6, 248(s0)
	addi a4, a4, -1
	bnez a4, 28b
	ld t0, 0(s0)
	ld t1, 8(s0)
	sd t1, 0(s0)
	sd t0, 8(s0)
	ld t0, 64(s0)
	ld t1, 72(s0)
	sd t1, 64(s0)
	sd t0, 72(s0)
	ld t0, 128(s0)
	ld t1, 136(s0)
	sd t1, 128(s0)
	sd t0, 136(s0)
	ld t0, 192(s0)
	ld t1, 200(s0)
	sd t1, 192(s0)
	sd t0, 200(s0)
	ld t0, 256(s0)
	ld t1, 264(s0)
	sd t1, 256(s0)
	sd t0, 264(s0)
	ld t0, 320(s0)
	ld t1, 328(s0)
	sd t1, 320(s0)
	sd t0, 328(s0)
	ld t0, 384(s0)
	ld t1, 392(s0)
	sd t1, 384(s0)
	sd t0, 392(s0)
	ld t0, 448(s0)
	ld t1, 456(s0)
	sd t1, 448(s0)
	sd t0, 456(s0)
	ld t0, 16(s0)
	ld t1, 24(s0)
	sd t1, 16(s0)
	sd t0, 24(s0)
	ld t0, 80(s0)
	ld t1, 88(s0)
	sd t1, 80(s0)
	sd t0, 88(s0)
	ld t0, 144(s0)
	ld t1, 152(s0)
	sd t1, 144(s0)
	sd t0, 152(s0)
	ld t0, 208(s0)
	ld t1, 216(s0)
	sd t1, 208(s0)
	sd t0, 216(s0)
	ld t0, 272(s0)
	ld t1, 280(s0)
	sd t1, 272(s0)
	sd t0, 280(s0)
	ld t0, 336(s0)
	ld t1, 344(s0)
	sd t1, 336(s0)
	sd t0, 344(s0)
	ld t0, 400(s0)
	ld t1, 408(s0)
	sd t1, 400(s0)
	sd t0, 408(s0)
	ld t0, 464(s0)
	ld t1, 472(s0)
	sd t1, 464(s0)
	sd t0, 472(s0)
	ld t0, 32(s0)
	ld t1, 40(s0)
	sd t1, 32(s0)
	sd t0, 40(s0)
	ld t0, 96(s0)
	ld t1, 104(s0)
	sd t1, 96(s0)
	sd t0, 104(s0)
	ld t0, 160(s0)
	ld t1, 168(s0)
	sd t1, 160(s0)
	sd t0, 168(s0)
	ld t0, 224(s0)
	ld t1, 232(s0)
	sd t1, 224(s0)
	sd t0, 232(s0)
	ld t0, 288(s0)
	ld t1, 296(s0)
	sd t1, 288(s0)
	sd t0, 296(s0)
	ld t0, 352(s0)
	ld t1, 360(s0)
	sd t1, 352(s0)
	sd t0, 360(s0)
	ld t0, 416(s0)
	ld t1, 424(s0)
	sd t1, 416(s0)
	sd t0, 424(s0)
	ld t0, 480(s0)
	ld t1, 488(s0)
	sd t1, 480(s0)
	sd t0, 488(s0)
	ld t0, 48(s0)
	ld t1, 56(s0)
	sd t1, 48(s0)
	sd t0, 56(s0)
	ld t0, 112(s0)
	ld t1, 120(s0)
	sd t1, 112(s0)
	sd t0, 120(s0)
	ld t0, 176(s0)
	ld t1, 184(s0)
	sd t1, 176(s0)
	sd t0, 184(s0)
	ld t0, 240(s0)
	ld t1, 248(s0)
	sd t1, 240(s0)
	sd t0, 248(s0)
	ld t0, 304(s0)
	ld t1, 312(s0)
	sd t1, 304(s0)
	sd t0, 312(s0)
	ld t0, 368(s0)
	ld t1, 376(s0)
	sd t1, 368(s0)
	sd t0, 376(s0)
	ld t0, 432(s0)
	ld t1, 440(s0)
	sd t1, 432(s0)
	sd t0, 440(s0)
	ld t0, 496(s0)
	ld t1, 504(s0)
	sd t1, 496(s0)
	sd t0, 504(s0)
	addi a3, s0, 632
	addi a4, zero, 8
29:
	ld a5, 0(a3)
	addi a3, a3, -8
	slli t0, a5, 21
	srai t0, t0, 63
	ld a6, 248(s0)
	xor t0, t0, a6
	slli t1, a5, 20
	srai t1, t1, 63
	ld a6, 312(s0)
	xor t1, t1, a6
	slli t2, a5, 19
	srai t2, t2, 63
	ld a6, 376(s0)
	xor t2, t2, a6
	slli t3, a5, 18
	srai t3, t3, 63
	ld a6, 440(s0)
	xor t3, t3, a6
	slli t4, a5, 17
	srai t4, t4, 63
	ld a6, 504(s0)
	xor t4, t4, a6
	slli t5, a5, 16
	srai t5, t5, 63
	ld a6, 8(s0)
	xor t5, t5, a6
	or t6, t5, t1
	xor t6, t6, t1
	xor a0, t2, t6
	or a7, t3, t0
	xor s1, t5, t3
	and s2, a7, s1
	xor s3, t2, s2
	or s4, s3, a0
	xor s4, s4, a0
	xor s5, t1, t0
	xor s6, t3, s5
	xori s6, s6, -1
	and s6, s6, a0
	or s2, t0, s2
	xor s6, s6, s2
	or s2, s6, s4
	xor s2, s2, s4
	or t0, t5, t0
	or s7, s6, t0
	xori s3, s3, -1
	and s3, s3, t1
	xor s8, s7, s3
	or t2, t2, t0
	xor t2, t2, t0
	xor t2, s3, t2
	xori s1, s1, -1
	and s1, s1, s5
	or t2, t2, s1
	or t3, t3, t6
	xor t3, t3, t6
	xor t6, a0, s7
	or t6, t6, t3
	xor t6, t6, t3
	xori t3, t6, -1
	and s6, a7, s6
	xor t3, t3, s6
	or s8, s8, t4
	xor s8, s8, t4
	xor s8, s8, t3
	xor t6, s5, t6
	or s3, s3, t6
	xor s3, a7, s3
	xor t5, t5, s3
	xor t3, t3, t5
	or s4, s4, t4
	xor s4, s4, t3
	xor a7, a7, s7
	or a7, t2, a7
	xor a7, t5, a7
	or s5, s5, t3
	xor s5, a7, s5
	or t3, s2, t4
	xor t3, t3, s5
	or t1, t1, a0
	or t1, t1, a7
	xor t1, t1, a7
	and s2, s2, t5
	xor t1, t1, s2
	or t1, t1, t4
	xor t1, t1, t2
	ld a6, 64(s0)
	xor a6, a6, t1
	sd a6, 64(s0)
	ld a6, 80(s0)
	xor a6, a6, s8
	sd a6, 80(s0)
	ld a6, 464(s0)
	xor a6, a6, t3
	sd a6, 464(s0)
	ld a6, 480(s0)
	xor a6, a6, s4
	sd a6, 480(s0)
	slli t0, a5, 27
	srai t0, t0, 63
	ld a6, 488(s0)
	xor t0, t0, a6
	slli t1, a5, 26
	srai t1, t1, 63
	ld a6, 56(s0)
	xor t1, t1, a6
	slli t2, a5, 25
	srai t2, t2, 63
	ld a6, 120(s0)
	xor t2, t2, a6
	slli t3, a5, 24
	srai t3, t3, 63
	ld a6, 184(s0)
	xor t3, t3, a6
	slli t4, a5, 23
	srai t4, t4, 63
	ld a6, 248(s0)
	xor t4, t4, a6
	slli t5, a5, 22
	srai t5, t5, 63
	ld a6, 312(s0)
	xor t5, t5, a6
	xor t6, t4, t1
	or a0, t5, t0
	xor a0, a0, t0
	xori a0, a0, -1
	and a0, a0, t1
	or a7, t4, a0
	or s1, t6, t0
	xor s1, s1, t0
	and s2, t5, t6
	xor t1, t1, s2
	or s2, t1, s1
	xor s2, s2, s1
	and s3, t3, t0
	xor a0, a0, s1
	and a0, a7, a0
	or s1, a0, s3
	xor s1, s1, s3
	and s4, t3, a0
	xori t5, t5, -1
	xor t5, s4, t5
	xor t0, t0, t6
	or s5, t0, s3
	xor s5, s5, s3
	xor s6, t5, s5
	xori s1, s1, -1
	and s1, s1, t2
	xor s1, s1, s6
	or t4, t4, s5
	xor t4, t4, s5
	xor t1, t1, t4
	or t5, t5, t1
	xor t5, t5, t1
	xor t3, t3, t0
	xor t5, t5, t3
	or s5, a7, t2
	xor s5, s5, t2
	xor s5, s5, t5
	xor s4, s4, t4
	or t3, t3, s4
	xor a7, a7, s6
	or s3, s3, a7
	xor s4, t3, s3
	xor a0, a0, s6
	xor t5, t5, a0
	and s3, s3, t5
	and t6, t6, t3
	xor s3, s3, t6
	or t6, s3, t2
	xor t6, t6, s4
	or s3, s3, t1
	xor s3, s3, t1
	or t0, t0, a7
	xor s3, s3, t0
	or s2, s2, t2
	xor s2, s2, s3
	ld a6, 400(s0)
	xor a6, a6, s2
	sd a6, 400(s0)
	ld a6, 432(s0)
	xor a6, a6, t6
	sd a6, 432(s0)
	ld a6, 256(s0)
	xor a6, a6, s1
	sd a6, 256(s0)
	ld a6, 224(s0)
	xor a6, a6, s5
	sd a6, 224(s0)
	slli t0, a5, 33
	srai t0, t0, 63
	ld a6, 232(s0)
	xor t0, t0, a6
	slli t1, a5, 32
	srai t1, t1, 63
	ld a6, 296(s0)
	xor t1, t1, a6
	slli t2, a5, 31
	srai t2, t2, 63
	ld a6, 360(s0)
	xor t2, t2, a6
	slli t3, a5, 30
	srai t3, t3, 63
	ld a6, 424(s0)
	xor t3, t3, a6
	slli t4, a5, 29
	srai t4, t4, 63
	ld a6, 488(s0)
	xor t4, t4, a6
	slli t5, a5, 28
	srai t5, t5, 63
	ld a6, 56(s0)
	xor t5, t5, a6
	or t6, t5, t4
	xor t6, t6, t4
	xor a0, t3, t0
	or a7, t6, a0
	xor s1, t2, t0
	or s2, s1, t5
	xor s2, s2, t5
	xor s3, a7, s2
	xor s4, t4, a0
	or s5, s4, t0
	xor s5, s5, t0
	xor a7, a7, s5
	or s5, s3, a7
	xor s5, s5, a7
	and s6, t0, s3
	or s6, t2, s6
	and s6, t5, s6
	xor s6, s4, s6
	or s7, s3, t1
	xor s7, s7, t1
	xor s7, s7, s6
	and a0, a0, s1
	xor s1, t5, t2
	xor s8, a7, s1
	or s8, t3, s8
	or s8, s8, a0
	xor s8, s8, a0
	or s2, s2, s1
	or s1, s6, s2
	xor s1, s1, s2
	and t0, t2, t0
	or a0, t0, t4
	xor a0, a0, t4
	xor s1, s1, a0
	and a7, a7, s1
	or t0, s4, t0
	or t0, t0, a7
	xor t0, t0, a7
	xor t5, t5, t0
	and s8, s8, t1
	xor s8, s8, t5
	xori s3, s3, -1
	or t4, t4, s3
	or t3, t3, t4
	xor s4, s4, t3
	xor s2, s2, s4
	xori s5, s5, -1
	and s5, s5, t1
	xor s5, s5, s2
	and t2, t2, s3
	xor s6, s6, t2
	or s4, s4, s6
	xor t6, t6, t5
	xor s4, s4, t6
	or s1, s1, t1
	xor s1, s1, s4
	ld a6, 176(s0)
	xor a6, a6, s7
	sd a6, 176(s0)
	ld a6, 128(s0)
	xor a6, a6, s1
	sd a6, 128(s0)
	ld a6, 32(s0)
	xor a6, a6, s8
	sd a6, 32(s0)
	ld a6, 16(s0)
	xor a6, a6, s5
	sd a6, 16(s0)
	slli t0, a5, 39
	srai t0, t0, 63
	ld a6, 472(s0)
	xor t0, t0, a6
	slli t1, a5, 38
	srai t1, t1, 63
	ld a6, 40(s0)
	xor t1, t1, a6
	slli t2, a5, 37
	srai t2, t2, 63
	ld a6, 104(s0)
	xor t2, t2, a6
	slli t3, a5, 36
	srai t3, t3, 63
	ld a6, 168(s0)
	xor t3, t3, a6
	slli t4, a5, 35
	srai t4, t4, 63
	ld a6, 232(s0)
	xor t4, t4, a6
	slli t5, a5, 34
	srai t5, t5, 63
	ld a6, 296(s0)
	xor t5, t5, a6
	xor t5, t5, t3
	xor t3, t3, t1
	or t6, t4, t2
	xor t6, t1, t6
	xori t6, t6, -1
	and t6, t6, t3
	or a0, t3, t4
	xor a0, a0, t4
	xor a7, t2, a0
	or s1, t5, a7
	or s1, s1, t6
	xor s1, s1, t6
	xor s2, t4, s1
	and a7, a7, s2
	or t3, t3, a7
	xor t3, t3, a7
	xor t5, t5, s2
	xori t3, t3, -1
	and t3, t3, t5
	xor t6, t6, t3
	xor t4, t4, t2
	or t1, t1, a0
	xor t5, t5, t1
	or t1, t5, t4
	xor t1, t1, t4
	xor s1, s1, t1
	or t1, t0, t6
	xor t1, t1, t6
	xor t1, t1, s1
	xori s1, s1, -1
	or a0, t6, t0
	xor a0, a0, t0
	xor a0, a0, s1
	xor t6, t6, s1
	or t6, t6, t4
	xor t6, t6, t4
	or a7, a7, t6
	xor t5, t5, a7
	or a7, s2, t0
	xor a7, a7, t5
	and t0, t0, s2
	xor t0, t0, t5
	ld a6, 496(s0)
	xor a6, a6, t0
	sd a6, 496(s0)
	ld a6, 416(s0)
	xor a6, a6, a7
	sd a6, 416(s0)
	ld a6, 272(s0)
	xor a6, a6, a0
	sd a6, 272(s0)
	ld a6, 384(s0)
	xor a6, a6, t1
	sd a6, 384(s0)
	slli t0, a5, 45
	srai t0, t0, 63
	ld a6, 216(s0)
	xor t0, t0, a6
	slli t1, a5, 44
	srai t1, t1, 63
	ld a6, 280(s0)
	xor t1, t1, a6
	slli t2, a5, 43
	srai t2, t2, 63
	ld a6, 344(s0)
	xor t2, t2, a6
	slli t3, a5, 42
	srai t3, t3, 63
	ld a6, 408(s0)
	xor t3, t3, a6
	slli t4, a5, 41
	srai t4, t4, 63
	ld a6, 472(s0)
	xor t4, t4, a6
	slli t5, a5, 40
	srai t5, t5, 63
	ld a6, 40(s0)
	xor t5, t5, a6
	or t6, t5, t3
	or a0, t6, t0
	xor a0, a0, t0
	xor a7, t5, a0
	xor s1, t3, a7
	or s2, t2, s1
	or a0, a0, t2
	xor a0, a0, t2
	xor t3, t3, a0
	and a0, t1, t3
	or s1, t5, s1
	xor a0, a0, s1
	xor a0, t2, a0
	xor t0, t0, a0
	or s3, a7, t0
	and s4, t1, s3
	xor s5, a7, s4
	and s6, t2, s1
	xor s5, s5, s6
	or s3, s3, t5
	xor s3, s3, t5
	xor s6, t3, s3
	xor t1, t1, s2
	xori s6, s6, -1
	and s6, s6, t1
	xori s6, s6, -1
	or s6, s6, t4
	xor s6, s6, t4
	xor s6, s6, a0
	or a0, t3, s4
	xor a0, a0, s4
	xor s3, s3, t1
	or s3, s5, s3
	or s3, s3, a0
	xor s3, s3, a0
	or a0, s2, s3
	xor a0, a0, s3
	and t0, t0, s3
	xor t1, t1, t0
	and s1, t3, s1
	or s1, t1, s1
	xor s4, s4, s1
	and s4, s4, t4
	xor s4, s4, s5
	xor t5, t5, t6
	xor s3, s3, t5
	and t2, t2, t1
	xor s3, s3, t2
	or a0, a0, t4
	xor a0, a0, s3
	xor t3, s2, t3
	or t3, t3, s3
	xor t3, t3, s3
	xor a7, a7, t1
	xor t3, t3, a7
	and s2, s2, t4
	xor s2, s2, t3
	ld a6, 368(s0)
	xor a6, a6, s4
	sd a6, 368(s0)
	ld a6, 448(s0)
	xor a6, a6, s6
	sd a6, 448(s0)
	ld a6, 160(s0)
	xor a6, a6, s2
	sd a6, 160(s0)
	ld a6, 48(s0)
	xor a6, a6, a0
	sd a6, 48(s0)
	slli t0, a5, 51
	srai t0, t0, 63
	ld a6, 456(s0)
	xor t0, t0, a6
	slli t1, a5, 50
	srai t1, t1, 63
	ld a6, 24(s0)
	xor t1, t1, a6
	slli t2, a5, 49
	srai t2, t2, 63
	ld a6, 88(s0)
	xor t2, t2, a6
	slli t3, a5, 48
	srai t3, t3, 63
	ld a6, 152(s0)
	xor t3, t3, a6
	slli t4, a5, 47
	srai t4, t4, 63
	ld a6, 216(s0)
	xor t4, t4, a6
	slli t5, a5, 46
	srai t5, t5, 63
	ld a6, 280(s0)
	xor t5, t5, a6
	xor t6, t4, t1
	or a0, t4, t0
	and a0, t5, a0
	xor t6, t6, a0
	xor a7, t0, t6
	or s1, t1, a7
	xor s1, s1, a7
	and a7, t5, a7
	xor s2, t4, a7
	xor s3, t5, t3
	or s4, s2, s3
	xor s5, t6, s4
	and s6, t3, s5
	or s7, s6, t0
	xor s7, s7, t0
	or s2, s1, s2
	xor s8, s7, s2
	and s9, s8, t2
	xor s9, s9, s5
	xor s4, t4, s4
	or s10, t0, s4
	xor s10, s10, s4
	xor t3, t3, s10
	or s10, t1, s6
	xor s10, s10, s6
	or s10, t3, s10
	or t4, t4, s3
	xor s8, s8, t4
	or a0, a0, s10
	xor s8, s8, a0
	or s5, t5, s5
	and s2, s2, s5
	xor s2, t3, s2
	xori s7, s7, -1
	and s7, s7, s2
	or s1, s1, t2
	xor s1, s1, s7
	xor t6, t6, s2
	or t1, t1, t6
	xor t1, t1, t6
	xori t4, t4, -1
	xor s4, s4, t4
	xor t1, t1, s4
	or t1, t1, t2
	xor t1, t1, t2
	xor t1, t1, s8
	xor t0, t0, a7
	xor t5, t5, t3
	and t0, t0, t5
	xor s6, s6, s4
	xor t0, t0, s6
	or s10, s10, t2
	xor s10, s10, t2
	xor s10, s10, t0
	ld a6, 336(s0)
	xor a6, a6, s9
	sd a6, 336(s0)
	ld a6, 352(s0)
	xor a6, a6, s1
	sd a6, 352(s0)
	ld a6, 192(s0)
	xor a6, a6, t1
	sd a6, 192(s0)
	ld a6, 304(s0)
	xor a6, a6, s10
	sd a6, 304(s0)
	slli t0, a5, 57
	srai t0, t0, 63
	ld a6, 200(s0)
	xor t0, t0, a6
	slli t1, a5, 56
	srai t1, t1, 63
	ld a6, 264(s0)
	xor t1, t1, a6
	slli t2, a5, 55
	srai t2, t2, 63
	ld a6, 328(s0)
	xor t2, t2, a6
	slli t3, a5, 54
	srai t3, t3, 63
	ld a6, 392(s0)
	xor t3, t3, a6
	slli t4, a5, 53
	srai t4, t4, 63
	ld a6, 456(s0)
	xor t4, t4, a6
	slli t5, a5, 52
	srai t5, t5, 63
	ld a6, 24(s0)
	xor t5, t5, a6
	xor t6, t2, t1
	xor a0, t3, t6
	and a7, t0, a0
	and s1, t2, t6
	xor s2, t4, s1
	and s3, a7, s2
	and s4, t0, s1
	xor s5, t3, s4
	or s6, s2, s5
	xor t6, t0, t6
	xor s7, s6, t6
	or s8, t5, s3
	xor s8, s8, s3
	xor s8, s8, s7
	xori a0, a0, -1
	and a0, a0, t1
	or s7, s2, a0
	xor s5, a7, s5
	xor s7, s7, s5
	xor a7, a7, t6
	or t2, t2, a7
	xor t2, t2, a7
	or t6, s2, t2
	xor t6, t6, t2
	xor t1, t1, s5
	xor t6, t6, t1
	or a7, a7, s4
	xor a7, a7, s4
	or t2, t2, a7
	xor s6, t4, s6
	and s6, t6, s6
	xor s6, t2, s6
	and s4, s6, t5
	xor s4, s4, t6
	or s2, s2, t3
	xor s2, s2, t3
	or a7, a7, s2
	or s1, s1, t6
	and a7, a7, s1
	xor s6, s6, a7
	xor a0, a0, t2
	and t0, t0, a0
	or s3, s3, t0
	xor a7, a7, s3
	or t0, a7, t5
	xor t0, t0, t5
	xor t0, t0, s7
	and t4, t4, s3
	xori s7, s7, -1
	xor t4, t4, s7
	xor a7, a7, t4
	or s6, s6, t5
	xor s6, s6, a7
	ld a6, 112(s0)
	xor a6, a6, s8
	sd a6, 112(s0)
	ld a6, 144(s0)
	xor a6, a6, s4
	sd a6, 144(s0)
	ld a6, 288(s0)
	xor a6, a6, s6
	sd a6, 288(s0)
	ld a6, 0(s0)
	xor a6, a6, t0
	sd a6, 0(s0)
	slli t0, a5, 63
	srai t0, t0, 63
	ld a6, 504(s0)
	xor t0, t0, a6
	slli t1, a5, 62
	srai t1, t1, 63
	ld a6, 8(s0)
	xor t1, t1, a6
	slli t2, a5, 61
	srai t2, t2, 63
	ld a6, 72(s0)
	xor t2, t2, a6
	slli t3, a5, 60
	srai t3, t3, 63
	ld a6, 136(s0)
	xor t3, t3, a6
	slli t4, a5, 59
	srai t4, t4, 63
	ld a6, 200(s0)
	xor t4, t4, a6
	slli t5, a5, 58
	srai t5, t5, 63
	ld a6, 264(s0)
	xor t5, t5, a6
	or t6, t3, t4
	xor t6, t6, t4
	or a0, t1, t3
	xor a0, a0, t3
	xor a0, t2, a0
	and a7, t5, a0
	or s1, a7, t6
	xor s1, s1, t6
	or s2, t4, a0
	xor s2, s2, a0
	or s3, t5, s2
	or s4, t4, t3
	xor s4, s4, t3
	xor s4, t1, s4
	and s5, s3, s4
	or a7, a7, s5
	xori a0, a0, -1
	xor s5, s5, a0
	or t3, t3, s3
	xor t3, t3, s3
	xor s5, s5, t3
	xor t6, t6, s5
	or t3, s1, t0
	xor t3, t3, t6
	xor t6, t5, t6
	and s3, t1, t6
	xor s5, t4, s5
	xor s3, s3, s5
	xor s2, s2, s3
	xor s3, a7, s3
	or t4, t4, s3
	xor t1, t1, t6
	xor t4, t4, t1
	and a7, a7, t0
	xor a7, a7, t4
	xor s4, s4, s2
	or s5, t2, s5
	xor s5, s4, s5
	xor t5, t5, s5
	and t5, t5, t0
	xor t5, t5, s2
	or s4, s4, t2
	xor s4, s4, t2
	and t4, t4, s4
	xor s1, s1, s5
	xor t4, t4, s1
	or t4, t4, t0
	xor t4, t4, s2
	ld a6, 208(s0)
	xor a6, a6, t5
	sd a6, 208(s0)
	ld a6, 96(s0)
	xor a6, a6, a7
	sd a6, 96(s0)
	ld a6, 320(s0)
	xor a6, a6, t3
	sd a6, 320(s0)
	ld a6, 240(s0)
	xor a6, a6, t4
	sd a6, 240(s0)
	ld a5, 0(a3)
	addi a3, a3, -8
	slli t0, a5, 21
	srai t0, t0, 63
	ld a6, 240(s0)
	xor t0, t0, a6
	slli t1, a5, 20
	srai t1, t1, 63
	ld a6, 304(s0)
	xor t1, t1, a6
	slli t2, a5, 19
	srai t2, t2, 63
	ld a6, 368(s0)
	xor t2, t2, a6
	slli t3, a5, 18
	srai t3, t3, 63
	ld a6, 432(s0)
	xor t3, t3, a6
	slli t4, a5, 17
	srai t4, t4, 63
	ld a6, 496(s0)
	xor t4, t4, a6
	slli t5, a5, 16
	srai t5, t5, 63
	ld a6, 0(s0)
	xor t5, t5, a6
	or t6, t5, t1
	xor t6, t6, t1
	xor a0, t2, t6
	or a7, t3, t0
	xor s1, t5, t3
	and s2, a7, s1
	xor s3, t2, s2
	or s4, s3, a0
	xor s4, s4, a0
	xor s5, t1, t0
	xor s6, t3, s5
	xori s6, s6, -1
	and s6, s6, a0
	or s2, t0, s2
	xor s6, s6, s2
	or s2, s6, s4
	xor s2, s2, s4
	or t0, t5, t0
	or s7, s6, t0
	xori s3, s3, -1
	and s3, s3, t1
	xor s8, s7, s3
	or t2, t2, t0
	xor t2, t2, t0
	xor t2, s3, t2
	xori s1, s1, -1
	and s1, s1, s5
	or t2, t2, s1
	or t3, t3, t6
	xor t3, t3, t6
	xor t6, a0, s7
	or t6, t6, t3
	xor t6, t6, t3
	xori t3, t6, -1
	and s6, a7, s6
	xor t3, t3, s6
	or s8, s8, t4
	xor s8, s8, t4
	xor s8, s8, t3
	xor t6, s5, t6
	or s3, s3, t6
	xor s3, a7, s3
	xor t5, t5, s3
	xor t3, t3, t5
	or s4, s4, t4
	xor s4, s4, t3
	xor a7, a7, s7
	or a7, t2, a7
	xor a7, t5, a7
	or s5, s5, t3
	xor s5, a7, s5
	or t3, s2, t4
	xor t3, t3, s5
	or t1, t1, a0
	or t1, t1, a7
	xor t1, t1, a7
	and s2, s2, t5
	xor t1, t1, s2
	or t1, t1, t4
	xor t1, t1, t2
	ld a6, 72(s0)
	xor a6, a6, t1
	sd a6, 72(s0)
	ld a6, 88(s0)
	xor a6, a6, s8
	sd a6, 88(s0)
	ld a6, 472(s0)
	xor a6, a6, t3
	sd a6, 472(s0)
	ld a6, 488(s0)
	xor a6, a6, s4
	sd a6, 488(s0)
	slli t0, a5, 27
	srai t0, t0, 63
	ld a6, 480(s0)
	xor t0, t0, a6
	slli t1, a5, 26
	srai t1, t1, 63
	ld a6, 48(s0)
	xor t1, t1, a6
	slli t2, a5, 25
	srai t2, t2, 63
	ld a6, 112(s0)
	xor t2, t2, a6
	slli t3, a5, 24
	srai t3, t3, 63
	ld a6, 176(s0)
	xor t3, t3, a6
	slli t4, a5, 23
	srai t4, t4, 63
	ld a6, 240(s0)
	xor t4, t4, a6
	slli t5, a5, 22
	srai t5, t5, 63
	ld a6, 304(s0)
	xor t5, t5, a6
	xor t6, t4, t1
	or a0, t5, t0
	xor a0, a0, t0
	xori a0, a0, -1
	and a0, a0, t1
	or a7, t4, a0
	or s1, t6, t0
	xor s1, s1, t0
	and s2, t5, t6
	xor t1, t1, s2
	or s2, t1, s1
	xor s2, s2, s1
	and s3, t3, t0
	xor a0, a0, s1
	and a0, a7, a0
	or s1, a0, s3
	xor s1, s1, s3
	and s4, t3, a0
	xori t5, t5, -1
	xor t5, s4, t5
	xor t0, t0, t6
	or s5, t0, s3
	xor s5, s5, s3
	xor s6, t5, s5
	xori s1, s1, -1
	and s1, s1, t2
	xor s1, s1, s6
	or t4, t4, s5
	xor t4, t4, s5
	xor t1, t1, t4
	or t5, t5, t1
	xor t5, t5, t1
	xor t3, t3, t0
	xor t5, t5, t3
	or s5, a7, t2
	xor s5, s5, t2
	xor s5, s5, t5
	xor s4, s4, t4
	or t3, t3, s4
	xor a7, a7, s6
	or s3, s3, a7
	xor s4, t3, s3
	xor a0, a0, s6
	xor t5, t5, a0
	and s3, s3, t5
	and t6, t6, t3
	xor s3, s3, t6
	or t6, s3, t2
	xor t6, t6, s4
	or s3, s3, t1
	xor s3, s3, t1
	or t0, t0, a7
	xor s3, s3, t0
	or s2, s2, t2
	xor s2, s2, s3
	ld a6, 408(s0)
	xor a6, a6, s2
	sd a6, 408(s0)
	ld a6, 440(s0)
	xor a6, a6, t6
	sd a6, 440(s0)
	ld a6, 264(s0)
	xor a6, a6, s1
	sd a6, 264(s0)
	ld a6, 232(s0)
	xor a6, a6, s5
	sd a6, 232(s0)
	slli t0, a5, 33
	srai t0, t0, 63
	ld a6, 224(s0)
	xor t0, t0, a6
	slli t1, a5, 32
	srai t1, t1, 63
	ld a6, 288(s0)
	xor t1, t1, a6
	slli t2, a5, 31
	srai t2, t2, 63
	ld a6, 352(s0)
	xor t2, t2, a6
	slli t3, a5, 30
	srai t3, t3, 63
	ld a6, 416(s0)
	xor t3, t3, a6
	slli t4, a5, 29
	srai t4, t4, 63
	ld a6, 480(s0)
	xor t4, t4, a6
	slli t5, a5, 28
	srai t5, t5, 63
	ld a6, 48(s0)
	xor t5, t5, a6
	or t6, t5, t4
	xor t6, t6, t4
	xor a0, t3, t0
	or a7, t6, a0
	xor s1, t2, t0
	or s2, s1, t5
	xor s2, s2, t5
	xor s3, a7, s2
	xor s4, t4, a0
	or s5, s4, t0
	xor s5, s5, t0
	xor a7, a7, s5
	or s5, s3, a7
	xor s5, s5, a7
	and s6, t0, s3
	or s6, t2, s6
	and s6, t5, s6
	xor s6, s4, s6
	or s7, s3, t1
	xor s7, s7, t1
	xor s7, s7, s6
	and a0, a0, s1
	xor s1, t5, t2
	xor s8, a7, s1
	or s8, t3, s8
	or s8, s8, a0
	xor s8, s8, a0
	or s2, s2, s1
	or s1, s6, s2
	xor s1, s1, s2
	and t0, t2, t0
	or a0, t0, t4
	xor a0, a0, t4
	xor s1, s1, a0
	and a7, a7, s1
	or t0, s4, t0
	or t0, t0, a7
	xor t0, t0, a7
	xor t5, t5, t0
	and s8, s8, t1
	xor s8, s8, t5
	xori s3, s3, -1
	or t4, t4, s3
	or t3, t3, t4
	xor s4, s4, t3
	xor s2, s2, s4
	xori s5, s5, -1
	and s5, s5, t1
	xor s5, s5, s2
	and t2, t2, s3
	xor s6, s6, t2
	or s4, s4, s6
	xor t6, t6, t5
	xor s4, s4, t6
	or s1, s1, t1
	xor s1, s1, s4
	ld a6, 184(s0)
	xor a6, a6, s7
	sd a6, 184(s0)
	ld a6, 136(s0)
	xor a6, a6, s1
	sd a6, 136(s0)
	ld a6, 40(s0)
	xor a6, a6, s8
	sd a6, 40(s0)
	ld a6, 24(s0)
	xor a6, a6, s5
	sd a6, 24(s0)
	slli t0, a5, 39
	srai t0, t0, 63
	ld a6, 464(s0)
	xor t0, t0, a6
	slli t1, a5, 38
	srai t1, t1, 63
	ld a6, 32(s0)
	xor t1, t1, a6
	slli t2, a5, 37
	srai t2, t2, 63
	ld a6, 96(s0)
	xor t2, t2, a6
	slli t3, a5, 36
	srai t3, t3, 63
	ld a6, 160(s0)
	xor t3, t3, a6
	slli t4, a5, 35
	srai t4, t4, 63
	ld a6, 224(s0)
	xor t4, t4, a6
	slli t5, a5, 34
	srai t5, t5, 63
	ld a6, 288(s0)
	xor t5, t5, a6
	xor t5, t5, t3
	xor t3, t3, t1
	or t6, t4, t2
	xor t6, t1, t6
	xori t6, t6, -1
	and t6, t6, t3
	or a0, t3, t4
	xor a0, a0, t4
	xor a7, t2, a0
	or s1, t5, a7
	or s1, s1, t6
	xor s1, s1, t6
	xor s2, t4, s1
	and a7, a7, s2
	or t3, t3, a7
	xor t3, t3, a7
	xor t5, t5, s2
	xori t3, t3, -1
	and t3, t3, t5
	xor t6, t6, t3
	xor t4, t4, t2
	or t1, t1, a0
	xor t5, t5, t1
	or t1, t5, t4
	xor t1, t1, t4
	xor s1, s1, t1
	or t1, t0, t6
	xor t1, t1, t6
	xor t1, t1, s1
	xori s1, s1, -1
	or a0, t6, t0
	xor a0, a0, t0
	xor a0, a0, s1
	xor t6, t6, s1
	or t6, t6, t4
	xor t6, t6, t4
	or a7, a7, t6
	xor t5, t5, a7
	or a7, s2, t0
	xor a7, a7, t5
	and t0, t0, s2
	xor t0, t0, t5
	ld a6, 504(s0)
	xor a6, a6, t0
	sd a6, 504(s0)
	ld a6, 424(s0)
	xor a6, a6, a7
	sd a6, 424(s0)
	ld a6, 280(s0)
	xor a6, a6, a0
	sd a6, 280(s0)
	ld a6, 392(s0)
	xor a6, a6, t1
	sd a6, 392(s0)
	slli t0, a5, 45
	srai t0, t0, 63
	ld a6, 208(s0)
	xor t0, t0, a6
	slli t1, a5, 44
	srai t1, t1, 63
	ld a6, 272(s0)
	xor t1, t1, a6
	slli t2, a5, 43
	srai t2, t2, 63
	ld a6, 336(s0)
	xor t2, t2, a6
	slli t3, a5, 42
	srai t3, t3, 63
	ld a6, 400(s0)
	xor t3, t3, a6
	slli t4, a5, 41
	srai t4, t4, 63
	ld a6, 464(s0)
	xor t4, t4, a6
	slli t5, a5, 40
	srai t5, t5, 63
	ld a6, 32(s0)
	xor t5, t5, a6
	or t6, t5, t3
	or a0, t6, t0
	xor a0, a0, t0
	xor a7, t5, a0
	xor s1, t3, a7
	or s2, t2, s1
	or a0, a0, t2
	xor a0, a0, t2
	xor t3, t3, a0
	and a0, t1, t3
	or s1, t5, s1
	xor a0, a0, s1
	xor a0, t2, a0
	xor t0, t0, a0
	or s3, a7, t0
	and s4, t1, s3
	xor s5, a7, s4
	and s6, t2, s1
	xor s5, s5, s6
	or s3, s3, t5
	xor s3, s3, t5
	xor s6, t3, s3
	xor t1, t1, s2
	xori s6, s6, -1
	and s6, s6, t1
	xori s6, s6, -1
	or s6, s6, t4
	xor s6, s6, t4
	xor s6, s6, a0
	or a0, t3, s4
	xor a0, a0, s4
	xor s3, s3, t1
	or s3, s5, s3
	or s3, s3, a0
	xor s3, s3, a0
	or a0, s2, s3
	xor a0, a0, s3
	and t0, t0, s3
	xor t1, t1, t0
	and s1, t3, s1
	or s1, t1, s1
	xor s4, s4, s1
	and s4, s4, t4
	xor s4, s4, s5
	xor t5, t5, t6
	xor s3, s3, t5
	and t2, t2, t1
	xor s3, s3, t2
	or a0, a0, t4
	xor a0, a0, s3
	xor t3, s2, t3
	or t3, t3, s3
	xor t3, t3, s3
	xor a7, a7, t1
	xor t3, t3, a7
	and s2, s2, t4
	xor s2, s2, t3
	ld a6, 376(s0)
	xor a6, a6, s4
	sd a6, 376(s0)
	ld a6, 456(s0)
	xor a6, a6, s6
	sd a6, 456(s0)
	ld a6, 168(s0)
	xor a6, a6, s2
	sd a6, 168(s0)
	ld a6, 56(s0)
	xor a6, a6, a0
	sd a6, 56(s0)
	slli t0, a5, 51
	srai t0, t0, 63
	ld a6, 448(s0)
	xor t0, t0, a6
	slli t1, a5, 50
	srai t1, t1, 63
	ld a6, 16(s0)
	xor t1, t1, a6
	slli t2, a5, 49
	srai t2, t2, 63
	ld a6, 80(s0)
	xor t2, t2, a6
	slli t3, a5, 48
	srai t3, t3, 63
	ld a6, 144(s0)
	xor t3, t3, a6
	slli t4, a5, 47
	srai t4, t4, 63
	ld a6, 208(s0)
	xor t4, t4, a6
	slli t5, a5, 46
	srai t5, t5, 63
	ld a6, 272(s0)
	xor t5, t5, a6
	xor t6, t4, t1
	or a0, t4, t0
	and a0, t5, a0
	xor t6, t6, a0
	xor a7, t0, t6
	or s1, t1, a7
	xor s1, s1, a7
	and a7, t5, a7
	xor s2, t4, a7
	xor s3, t5, t3
	or s4, s2, s3
	xor s5, t6, s4
	and s6, t3, s5
	or s7, s6, t0
	xor s7, s7, t0
	or s2, s1, s2
	xor s8, s7, s2
	and s9, s8, t2
	xor s9, s9, s5
	xor s4, t4, s4
	or s10, t0, s4
	xor s10, s10, s4
	xor t3, t3, s10
	or s10, t1, s6
	xor s10, s10, s6
	or s10, t3, s10
	or t4, t4, s3
	xor s8, s8, t4
	or a0, a0, s10
	xor s8, s8, a0
	or s5, t5, s5
	and s2, s2, s5
	xor s2, t3, s2
	xori s7, s7, -1
	and s7, s7, s2
	or s1, s1, t2
	xor s1, s1, s7
	xor t6, t6, s2
	or t1, t1, t6
	xor t1, t1, t6
	xori t4, t4, -1
	xor s4, s4, t4
	xor t1, t1, s4
	or t1, t1, t2
	xor t1, t1, t2
	xor t1, t1, s8
	xor t0, t0, a7
	xor t5, t5, t3
	and t0, t0, t5
	xor s6, s6, s4
	xor t0, t0, s6
	or s10, s10, t2
	xor s10, s10, t2
	xor s10, s10, t0
	ld a6, 344(s0)
	xor a6, a6, s9
	sd a6, 344(s0)
	ld a6, 360(s0)
	xor a6, a6, s1
	sd a6, 360(s0)
	ld a6, 200(s0)
	xor a6, a6, t1
	sd a6, 200(s0)
	ld a6, 312(s0)
	xor a6, a6, s10
	sd a6, 312(s0)
	slli t0, a5, 57
	srai t0, t0, 63
	ld a6, 192(s0)
	xor t0, t0, a6
	slli t1, a5, 56
	srai t1, t1, 63
	ld a6, 256(s0)
	xor t1, t1, a6
	slli t2, a5, 55
	srai t2, t2, 63
	ld a6, 320(s0)
	xor t2, t2, a6
	slli t3, a5, 54
	srai t3, t3, 63
	ld a6, 384(s0)
	xor t3, t3, a6
	slli t4, a5, 53
	srai t4, t4, 63
	ld a6, 448(s0)
	xor t4, t4, a6
	slli t5, a5, 52
	srai t5, t5, 63
	ld a6, 16(s0)
	xor t5, t5, a6
	xor t6, t2, t1
	xor a0, t3, t6
	and a7, t0, a0
	and s1, t2, t6
	xor s2, t4, s1
	and s3, a7, s2
	and s4, t0, s1
	xor s5, t3, s4
	or s6, s2, s5
	xor t6, t0, t6
	xor s7, s6, t6
	or s8, t5, s3
	xor s8, s8, s3
	xor s8, s8, s7
	xori a0, a0, -1
	and a0, a0, t1
	or s7, s2, a0
	xor s5, a7, s5
	xor s7, s7, s5
	xor a7, a7, t6
	or t2, t2, a7
	xor t2, t2, a7
	or t6, s2, t2
	xor t6, t6, t2
	xor t1, t1, s5
	xor t6, t6, t1
	or a7, a7, s4
	xor a7, a7, s4
	or t2, t2, a7
	xor s6, t4, s6
	and s6, t6, s6
	xor s6, t2, s6
	and s4, s6, t5
	xor s4, s4, t6
	or s2, s2, t3
	xor s2, s2, t3
	or a7, a7, s2
	or s1, s1, t6
	and a7, a7, s1
	xor s6, s6, a7
	xor a0, a0, t2
	and t0, t0, a0
	or s3, s3, t0
	xor a7, a7, s3
	or t0, a7, t5
	xor t0, t0, t5
	xor t0, t0, s7
	and t4, t4, s3
	xori s7, s7, -1
	xor t4, t4, s7
	xor a7, a7, t4
	or s6, s6, t5
	xor s6, s6, a7
	ld a6, 120(s0)
	xor a6, a6, s8
	sd a6, 120(s0)
	ld a6, 152(s0)
	xor a6, a6, s4
	sd a6, 152(s0)
	ld a6, 296(s0)
	xor a6, a6, s6
	sd a6, 296(s0)
	ld a6, 8(s0)
	xor a6, a6, t0
	sd a6, 8(s0)
	slli t0, a5, 63
	srai t0, t0, 63
	ld a6, 496(s0)
	xor t0, t0, a6
	slli t1, a5, 62
	srai t1, t1, 63
	ld a6, 0(s0)
	xor t1, t1, a6
	slli t2, a5, 61
	srai t2, t2, 63
	ld a6, 64(s0)
	xor t2, t2, a6
	slli t3, a5, 60
	srai t3, t3, 63
	ld a6, 128(s0)
	xor t3, t3, a6
	slli t4, a5, 59
	srai t4, t4, 63
	ld a6, 192(s0)
	xor t4, t4, a6
	slli t5, a5, 58
	srai t5, t5, 63
	ld a6, 256(s0)
	xor t5, t5, a6
	or t6, t3, t4
	xor t6, t6, t4
	or a0, t1, t3
	xor a0, a0, t3
	xor a0, t2, a0
	and a7, t5, a0
	or s1, a7, t6
	xor s1, s1, t6
	or s2, t4, a0
	xor s2, s2, a0
	or s3, t5, s2
	or s4, t4, t3
	xor s4, s4, t3
	xor s4, t1, s4
	and s5, s3, s4
	or a7, a7, s5
	xori a0, a0, -1
	xor s5, s5, a0
	or t3, t3, s3
	xor t3, t3, s3
	xor s5, s5, t3
	xor t6, t6, s5
	or t3, s1, t0
	xor t3, t3, t6
	xor t6, t5, t6
	and s3, t1, t6
	xor s5, t4, s5
	xor s3, s3, s5
	xor s2, s2, s3
	xor s3, a7, s3
	or t4, t4, s3
	xor t1, t1, t6
	xor t4, t4, t1
	and a7, a7, t0
	xor a7, a7, t4
	xor s4, s4, s2
	or s5, t2, s5
	xor s5, s4, s5
	xor t5, t5, s5
	and t5, t5, t0
	xor t5, t5, s2
	or s4, s4, t2
	xor s4, s4, t2
	and t4, t4, s4
	xor s1, s1, s5
	xor t4, t4, s1
	or t4, t4, t0
	xor t4, t4, s2
	ld a6, 216(s0)
	xor a6, a6, t5
	sd a6, 216(s0)
	ld a6, 104(s0)
	xor a6, a6, a7
	sd a6, 104(s0)
	ld a6, 328(s0)
	xor a6, a6, t3
	sd a6, 328(s0)
	ld a6, 248(s0)
	xor a6, a6, t4
	sd a6, 248(s0)
	addi a4, a4, -1
	bnez a4, 29b
	ld t0, 0(s0)
	ld t1, 8(s0)
	sd t1, 0(s0)
	sd t0, 8(s0)
	ld t0, 64(s0)
	ld t1, 72(s0)
	sd t1, 64(s0)
	sd t0, 72(s0)
	ld t0, 128(s0)
	ld t1, 136(s0)
	sd t1, 128(s0)
	sd t0, 136(s0)
	ld t0, 192(s0)
	ld t1, 200(s0)
	sd t1, 192(s0)
	sd t0, 200(s0)
	ld t0, 256(s0)
	ld t1, 264(s0)
	sd t1, 256(s0)
	sd t0, 264(s0)
	ld t0, 320(s0)
	ld t1, 328(s0)
	sd t1, 320(s0)
	sd t0, 328(s0)
	ld t0, 384(s0)
	ld t1, 392(s0)
	sd t1, 384(s0)
	sd t0, 392(s0)
	ld t0, 448(s0)
	ld t1, 456(s0)
	sd t1, 448(s0)
	sd t0, 456(s0)
	ld t0, 16(s0)
	ld t1, 24(s0)
	sd t1, 16(s0)
	sd t0, 24(s0)
	ld t0, 80(s0)
	ld t1, 88(s0)
	sd t1, 80(s0)
	sd t0, 88(s0)
	ld t0, 144(s0)
	ld t1, 152(s0)
	sd t1, 144(s0)
	sd t0, 152(s0)
	ld t0, 208(s0)
	ld t1, 216(s0)
	sd t1, 208(s0)
	sd t0, 216(s0)
	ld t0, 272(s0)
	ld t1, 280(s0)
	sd t1, 272(s0)
	sd t0, 280(s0)
	ld t0, 336(s0)
	ld t1, 344(s0)
	sd t1, 336(s0)
	sd t0, 344(s0)
	ld t0, 400(s0)
	ld t1, 408(s0)
	sd t1, 400(s0)
	sd t0, 408(s0)
	ld t0, 464(s0)
	ld t1, 472(s0)
	sd t1, 464(s0)
	sd t0, 472(s0)
	ld t0, 32(s0)
	ld t1, 40(s0)
	sd t1, 32(s0)
	sd t0, 40(s0)
	ld t0, 96(s0)
	ld t1, 104(s0)
	sd t1, 96(s0)
	sd t0, 104(s0)
	ld t0, 160(s0)
	ld t1, 168(s0)
	sd t1, 160(s0)
	sd t0, 168(s0)
	ld t0, 224(s0)
	ld t1, 232(s0)
	sd t1, 224(s0)
	sd t0, 232(s0)
	ld t0, 288(s0)
	ld t1, 296(s0)
	sd t1, 288(s0)
	sd t0, 296(s0)
	ld t0, 352(s0)
	ld t1, 360(s0)
	sd t1, 352(s0)
	sd t0, 360(s0)
	ld t0, 416(s0)
	ld t1, 424(s0)
	sd t1, 416(s0)
	sd t0, 424(s0)
	ld t0, 480(s0)
	ld t1, 488(s0)
	sd t1, 480(s0)
	sd t0, 488(s0)
	ld t0, 48(s0)
	ld t1, 56(s0)
	sd t1, 48(s0)
	sd t0, 56(s0)
	ld t0, 112(s0)
	ld t1, 120(s0)
	sd t1, 112(s0)
	sd t0, 120(s0)
	ld t0, 176(s0)
	ld t1, 184(s0)
	sd t1, 176(s0)
	sd t0, 184(s0)
	ld t0, 240(s0)
	ld t1, 248(s0)
	sd t1, 240(s0)
	sd t0, 248(s0)
	ld t0, 304(s0)
	ld t1, 312(s0)
	sd t1, 304(s0)
	sd t0, 312(s0)
	ld t0, 368(s0)
	ld t1, 376(s0)
	sd t1, 368(s0)
	sd t0, 376(s0)
	ld t0, 432(s0)
	ld t1, 440(s0)
	sd t1, 432(s0)
	sd t0, 440(s0)
	ld t0, 496(s0)
	ld t1, 504(s0)
	sd t1, 496(s0)
	sd t0, 504(s0)
	addi a0, s0, 896
	ld s1, 0(a0)
	ld s2, 8(a0)
	ld s3, 16(a0)
	ld t0, 0(s0)
	ld t1, 64(s0)
	ld t2, 128(s0)
	ld t3, 192(s0)
	ld t4, 256(s0)
	ld t5, 320(s0)
	ld t6, 384(s0)
	ld a7, 448(s0)
	srli s4, t0, 32
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 32
	xor t0, t0, s4
	srli s4, t1, 32
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 32
	xor t1, t1, s4
	srli s4, t2, 32
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 32
	xor t2, t2, s4
	srli s4, t3, 32
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 32
	xor t3, t3, s4
	srli s4, t0, 16
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 16
	xor t0, t0, s4
	srli s4, t1, 16
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 16
	xor t1, t1, s4
	srli s4, t4, 16
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 16
	xor t4, t4, s4
	srli s4, t5, 16
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 16
	xor t5, t5, s4
	srli s4, t0, 8
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 8
	xor t0, t0, s4
	srli s4, t2, 8
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 8
	xor t2, t2, s4
	srli s4, t4, 8
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 8
	xor t4, t4, s4
	srli s4, t6, 8
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 8
	xor t6, t6, s4
	sd t0, 0(s0)
	sd t1, 64(s0)
	sd t2, 128(s0)
	sd t3, 192(s0)
	sd t4, 256(s0)
	sd t5, 320(s0)
	sd t6, 384(s0)
	sd a7, 448(s0)
	ld t0, 8(s0)
	ld t1, 72(s0)
	ld t2, 136(s0)
	ld t3, 200(s0)
	ld t4, 264(s0)
	ld t5, 328(s0)
	ld t6, 392(s0)
	ld a7, 456(s0)
	srli s4, t0, 32
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 32
	xor t0, t0, s4
	srli s4, t1, 32
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 32
	xor t1, t1, s4
	srli s4, t2, 32
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 32
	xor t2, t2, s4
	srli s4, t3, 32
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 32
	xor t3, t3, s4
	srli s4, t0, 16
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 16
	xor t0, t0, s4
	srli s4, t1, 16
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 16
	xor t1, t1, s4
	srli s4, t4, 16
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 16
	xor t4, t4, s4
	srli s4, t5, 16
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 16
	xor t5, t5, s4
	srli s4, t0, 8
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 8
	xor t0, t0, s4
	srli s4, t2, 8
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 8
	xor t2, t2, s4
	srli s4, t4, 8
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 8
	xor t4, t4, s4
	srli s4, t6, 8
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 8
	xor t6, t6, s4
	sd t0, 8(s0)
	sd t1, 72(s0)
	sd t2, 136(s0)
	sd t3, 200(s0)
	sd t4, 264(s0)
	sd t5, 328(s0)
	sd t6, 392(s0)
	sd a7, 456(s0)
	ld t0, 16(s0)
	ld t1, 80(s0)
	ld t2, 144(s0)
	ld t3, 208(s0)
	ld t4, 272(s0)
	ld t5, 336(s0)
	ld t6, 400(s0)
	ld a7, 464(s0)
	srli s4, t0, 32
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 32
	xor t0, t0, s4
	srli s4, t1, 32
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 32
	xor t1, t1, s4
	srli s4, t2, 32
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 32
	xor t2, t2, s4
	srli s4, t3, 32
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 32
	xor t3, t3, s4
	srli s4, t0, 16
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 16
	xor t0, t0, s4
	srli s4, t1, 16
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 16
	xor t1, t1, s4
	srli s4, t4, 16
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 16
	xor t4, t4, s4
	srli s4, t5, 16
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 16
	xor t5, t5, s4
	srli s4, t0, 8
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 8
	xor t0, t0, s4
	srli s4, t2, 8
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 8
	xor t2, t2, s4
	srli s4, t4, 8
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 8
	xor t4, t4, s4
	srli s4, t6, 8
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 8
	xor t6, t6, s4
	sd t0, 16(s0)
	sd t1, 80(s0)
	sd t2, 144(s0)
	sd t3, 208(s0)
	sd t4, 272(s0)
	sd t5, 336(s0)
	sd t6, 400(s0)
	sd a7, 464(s0)
	ld t0, 24(s0)
	ld t1, 88(s0)
	ld t2, 152(s0)
	ld t3, 216(s0)
	ld t4, 280(s0)
	ld t5, 344(s0)
	ld t6, 408(s0)
	ld a7, 472(s0)
	srli s4, t0, 32
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 32
	xor t0, t0, s4
	srli s4, t1, 32
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 32
	xor t1, t1, s4
	srli s4, t2, 32
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 32
	xor t2, t2, s4
	srli s4, t3, 32
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 32
	xor t3, t3, s4
	srli s4, t0, 16
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 16
	xor t0, t0, s4
	srli s4, t1, 16
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 16
	xor t1, t1, s4
	srli s4, t4, 16
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 16
	xor t4, t4, s4
	srli s4, t5, 16
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 16
	xor t5, t5, s4
	srli s4, t0, 8
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 8
	xor t0, t0, s4
	srli s4, t2, 8
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 8
	xor t2, t2, s4
	srli s4, t4, 8
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 8
	xor t4, t4, s4
	srli s4, t6, 8
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 8
	xor t6, t6, s4
	sd t0, 24(s0)
	sd t1, 88(s0)
	sd t2, 152(s0)
	sd t3, 216(s0)
	sd t4, 280(s0)
	sd t5, 344(s0)
	sd t6, 408(s0)
	sd a7, 472(s0)
	ld t0, 32(s0)
	ld t1, 96(s0)
	ld t2, 160(s0)
	ld t3, 224(s0)
	ld t4, 288(s0)
	ld t5, 352(s0)
	ld t6, 416(s0)
	ld a7, 480(s0)
	srli s4, t0, 32
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 32
	xor t0, t0, s4
	srli s4, t1, 32
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 32
	xor t1, t1, s4
	srli s4, t2, 32
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 32
	xor t2, t2, s4
	srli s4, t3, 32
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 32
	xor t3, t3, s4
	srli s4, t0, 16
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 16
	xor t0, t0, s4
	srli s4, t1, 16
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 16
	xor t1, t1, s4
	srli s4, t4, 16
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 16
	xor t4, t4, s4
	srli s4, t5, 16
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 16
	xor t5, t5, s4
	srli s4, t0, 8
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 8
	xor t0, t0, s4
	srli s4, t2, 8
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 8
	xor t2, t2, s4
	srli s4, t4, 8
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 8
	xor t4, t4, s4
	srli s4, t6, 8
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 8
	xor t6, t6, s4
	sd t0, 32(s0)
	sd t1, 96(s0)
	sd t2, 160(s0)
	sd t3, 224(s0)
	sd t4, 288(s0)
	sd t5, 352(s0)
	sd t6, 416(s0)
	sd a7, 480(s0)
	ld t0, 40(s0)
	ld t1, 104(s0)
	ld t2, 168(s0)
	ld t3, 232(s0)
	ld t4, 296(s0)
	ld t5, 360(s0)
	ld t6, 424(s0)
	ld a7, 488(s0)
	srli s4, t0, 32
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 32
	xor t0, t0, s4
	srli s4, t1, 32
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 32
	xor t1, t1, s4
	srli s4, t2, 32
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 32
	xor t2, t2, s4
	srli s4, t3, 32
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 32
	xor t3, t3, s4
	srli s4, t0, 16
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 16
	xor t0, t0, s4
	srli s4, t1, 16
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 16
	xor t1, t1, s4
	srli s4, t4, 16
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 16
	xor t4, t4, s4
	srli s4, t5, 16
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 16
	xor t5, t5, s4
	srli s4, t0, 8
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 8
	xor t0, t0, s4
	srli s4, t2, 8
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 8
	xor t2, t2, s4
	srli s4, t4, 8
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 8
	xor t4, t4, s4
	srli s4, t6, 8
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 8
	xor t6, t6, s4
	sd t0, 40(s0)
	sd t1, 104(s0)
	sd t2, 168(s0)
	sd t3, 232(s0)
	sd t4, 296(s0)
	sd t5, 360(s0)
	sd t6, 424(s0)
	sd a7, 488(s0)
	ld t0, 48(s0)
	ld t1, 112(s0)
	ld t2, 176(s0)
	ld t3, 240(s0)
	ld t4, 304(s0)
	ld t5, 368(s0)
	ld t6, 432(s0)
	ld a7, 496(s0)
	srli s4, t0, 32
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 32
	xor t0, t0, s4
	srli s4, t1, 32
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 32
	xor t1, t1, s4
	srli s4, t2, 32
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 32
	xor t2, t2, s4
	srli s4, t3, 32
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 32
	xor t3, t3, s4
	srli s4, t0, 16
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 16
	xor t0, t0, s4
	srli s4, t1, 16
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 16
	xor t1, t1, s4
	srli s4, t4, 16
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 16
	xor t4, t4, s4
	srli s4, t5, 16
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 16
	xor t5, t5, s4
	srli s4, t0, 8
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 8
	xor t0, t0, s4
	srli s4, t2, 8
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 8
	xor t2, t2, s4
	srli s4, t4, 8
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 8
	xor t4, t4, s4
	srli s4, t6, 8
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 8
	xor t6, t6, s4
	sd t0, 48(s0)
	sd t1, 112(s0)
	sd t2, 176(s0)
	sd t3, 240(s0)
	sd t4, 304(s0)
	sd t5, 368(s0)
	sd t6, 432(s0)
	sd a7, 496(s0)
	ld t0, 56(s0)
	ld t1, 120(s0)
	ld t2, 184(s0)
	ld t3, 248(s0)
	ld t4, 312(s0)
	ld t5, 376(s0)
	ld t6, 440(s0)
	ld a7, 504(s0)
	srli s4, t0, 32
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 32
	xor t0, t0, s4
	srli s4, t1, 32
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 32
	xor t1, t1, s4
	srli s4, t2, 32
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 32
	xor t2, t2, s4
	srli s4, t3, 32
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 32
	xor t3, t3, s4
	srli s4, t0, 16
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 16
	xor t0, t0, s4
	srli s4, t1, 16
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 16
	xor t1, t1, s4
	srli s4, t4, 16
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 16
	xor t4, t4, s4
	srli s4, t5, 16
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 16
	xor t5, t5, s4
	srli s4, t0, 8
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 8
	xor t0, t0, s4
	srli s4, t2, 8
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 8
	xor t2, t2, s4
	srli s4, t4, 8
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 8
	xor t4, t4, s4
	srli s4, t6, 8
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 8
	xor t6, t6, s4
	sd t0, 56(s0)
	sd t1, 120(s0)
	sd t2, 184(s0)
	sd t3, 248(s0)
	sd t4, 312(s0)
	sd t5, 376(s0)
	sd t6, 440(s0)
	sd a7, 504(s0)
	ld s1, 24(a0)
	ld s2, 32(a0)
	ld s3, 40(a0)
	ld t0, 0(s0)
	ld t1, 8(s0)
	ld t2, 16(s0)
	ld t3, 24(s0)
	ld t4, 32(s0)
	ld t5, 40(s0)
	ld t6, 48(s0)
	ld a7, 56(s0)
	srli s4, t0, 4
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 4
	xor t0, t0, s4
	srli s4, t1, 4
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 4
	xor t1, t1, s4
	srli s4, t2, 4
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 4
	xor t2, t2, s4
	srli s4, t3, 4
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 4
	xor t3, t3, s4
	srli s4, t0, 2
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 2
	xor t0, t0, s4
	srli s4, t1, 2
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 2
	xor t1, t1, s4
	srli s4, t4, 2
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 2
	xor t4, t4, s4
	srli s4, t5, 2
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 2
	xor t5, t5, s4
	srli s4, t0, 1
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 1
	xor t0, t0, s4
	srli s4, t2, 1
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 1
	xor t2, t2, s4
	srli s4, t4, 1
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 1
	xor t4, t4, s4
	srli s4, t6, 1
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 1
	xor t6, t6, s4
	sd t0, 0(s0)
	sd t1, 8(s0)
	sd t2, 16(s0)
	sd t3, 24(s0)
	sd t4, 32(s0)
	sd t5, 40(s0)
	sd t6, 48(s0)
	sd a7, 56(s0)
	ld t0, 64(s0)
	ld t1, 72(s0)
	ld t2, 80(s0)
	ld t3, 88(s0)
	ld t4, 96(s0)
	ld t5, 104(s0)
	ld t6, 112(s0)
	ld a7, 120(s0)
	srli s4, t0, 4
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 4
	xor t0, t0, s4
	srli s4, t1, 4
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 4
	xor t1, t1, s4
	srli s4, t2, 4
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 4
	xor t2, t2, s4
	srli s4, t3, 4
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 4
	xor t3, t3, s4
	srli s4, t0, 2
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 2
	xor t0, t0, s4
	srli s4, t1, 2
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 2
	xor t1, t1, s4
	srli s4, t4, 2
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 2
	xor t4, t4, s4
	srli s4, t5, 2
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 2
	xor t5, t5, s4
	srli s4, t0, 1
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 1
	xor t0, t0, s4
	srli s4, t2, 1
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 1
	xor t2, t2, s4
	srli s4, t4, 1
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 1
	xor t4, t4, s4
	srli s4, t6, 1
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 1
	xor t6, t6, s4
	sd t0, 64(s0)
	sd t1, 72(s0)
	sd t2, 80(s0)
	sd t3, 88(s0)
	sd t4, 96(s0)
	sd t5, 104(s0)
	sd t6, 112(s0)
	sd a7, 120(s0)
	ld t0, 128(s0)
	ld t1, 136(s0)
	ld t2, 144(s0)
	ld t3, 152(s0)
	ld t4, 160(s0)
	ld t5, 168(s0)
	ld t6, 176(s0)
	ld a7, 184(s0)
	srli s4, t0, 4
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 4
	xor t0, t0, s4
	srli s4, t1, 4
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 4
	xor t1, t1, s4
	srli s4, t2, 4
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 4
	xor t2, t2, s4
	srli s4, t3, 4
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 4
	xor t3, t3, s4
	srli s4, t0, 2
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 2
	xor t0, t0, s4
	srli s4, t1, 2
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 2
	xor t1, t1, s4
	srli s4, t4, 2
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 2
	xor t4, t4, s4
	srli s4, t5, 2
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 2
	xor t5, t5, s4
	srli s4, t0, 1
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 1
	xor t0, t0, s4
	srli s4, t2, 1
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 1
	xor t2, t2, s4
	srli s4, t4, 1
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 1
	xor t4, t4, s4
	srli s4, t6, 1
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 1
	xor t6, t6, s4
	sd t0, 128(s0)
	sd t1, 136(s0)
	sd t2, 144(s0)
	sd t3, 152(s0)
	sd t4, 160(s0)
	sd t5, 168(s0)
	sd t6, 176(s0)
	sd a7, 184(s0)
	ld t0, 192(s0)
	ld t1, 200(s0)
	ld t2, 208(s0)
	ld t3, 216(s0)
	ld t4, 224(s0)
	ld t5, 232(s0)
	ld t6, 240(s0)
	ld a7, 248(s0)
	srli s4, t0, 4
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 4
	xor t0, t0, s4
	srli s4, t1, 4
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 4
	xor t1, t1, s4
	srli s4, t2, 4
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 4
	xor t2, t2, s4
	srli s4, t3, 4
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 4
	xor t3, t3, s4
	srli s4, t0, 2
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 2
	xor t0, t0, s4
	srli s4, t1, 2
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 2
	xor t1, t1, s4
	srli s4, t4, 2
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 2
	xor t4, t4, s4
	srli s4, t5, 2
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 2
	xor t5, t5, s4
	srli s4, t0, 1
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 1
	xor t0, t0, s4
	srli s4, t2, 1
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 1
	xor t2, t2, s4
	srli s4, t4, 1
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 1
	xor t4, t4, s4
	srli s4, t6, 1
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 1
	xor t6, t6, s4
	sd t0, 192(s0)
	sd t1, 200(s0)
	sd t2, 208(s0)
	sd t3, 216(s0)
	sd t4, 224(s0)
	sd t5, 232(s0)
	sd t6, 240(s0)
	sd a7, 248(s0)
	ld t0, 256(s0)
	ld t1, 264(s0)
	ld t2, 272(s0)
	ld t3, 280(s0)
	ld t4, 288(s0)
	ld t5, 296(s0)
	ld t6, 304(s0)
	ld a7, 312(s0)
	srli s4, t0, 4
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 4
	xor t0, t0, s4
	srli s4, t1, 4
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 4
	xor t1, t1, s4
	srli s4, t2, 4
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 4
	xor t2, t2, s4
	srli s4, t3, 4
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 4
	xor t3, t3, s4
	srli s4, t0, 2
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 2
	xor t0, t0, s4
	srli s4, t1, 2
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 2
	xor t1, t1, s4
	srli s4, t4, 2
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 2
	xor t4, t4, s4
	srli s4, t5, 2
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 2
	xor t5, t5, s4
	srli s4, t0, 1
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 1
	xor t0, t0, s4
	srli s4, t2, 1
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 1
	xor t2, t2, s4
	srli s4, t4, 1
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 1
	xor t4, t4, s4
	srli s4, t6, 1
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 1
	xor t6, t6, s4
	sd t0, 256(s0)
	sd t1, 264(s0)
	sd t2, 272(s0)
	sd t3, 280(s0)
	sd t4, 288(s0)
	sd t5, 296(s0)
	sd t6, 304(s0)
	sd a7, 312(s0)
	ld t0, 320(s0)
	ld t1, 328(s0)
	ld t2, 336(s0)
	ld t3, 344(s0)
	ld t4, 352(s0)
	ld t5, 360(s0)
	ld t6, 368(s0)
	ld a7, 376(s0)
	srli s4, t0, 4
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 4
	xor t0, t0, s4
	srli s4, t1, 4
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 4
	xor t1, t1, s4
	srli s4, t2, 4
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 4
	xor t2, t2, s4
	srli s4, t3, 4
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 4
	xor t3, t3, s4
	srli s4, t0, 2
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 2
	xor t0, t0, s4
	srli s4, t1, 2
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 2
	xor t1, t1, s4
	srli s4, t4, 2
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 2
	xor t4, t4, s4
	srli s4, t5, 2
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 2
	xor t5, t5, s4
	srli s4, t0, 1
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 1
	xor t0, t0, s4
	srli s4, t2, 1
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 1
	xor t2, t2, s4
	srli s4, t4, 1
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 1
	xor t4, t4, s4
	srli s4, t6, 1
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 1
	xor t6, t6, s4
	sd t0, 320(s0)
	sd t1, 328(s0)
	sd t2, 336(s0)
	sd t3, 344(s0)
	sd t4, 352(s0)
	sd t5, 360(s0)
	sd t6, 368(s0)
	sd a7, 376(s0)
	ld t0, 384(s0)
	ld t1, 392(s0)
	ld t2, 400(s0)
	ld t3, 408(s0)
	ld t4, 416(s0)
	ld t5, 424(s0)
	ld t6, 432(s0)
	ld a7, 440(s0)
	srli s4, t0, 4
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 4
	xor t0, t0, s4
	srli s4, t1, 4
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 4
	xor t1, t1, s4
	srli s4, t2, 4
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 4
	xor t2, t2, s4
	srli s4, t3, 4
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 4
	xor t3, t3, s4
	srli s4, t0, 2
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 2
	xor t0, t0, s4
	srli s4, t1, 2
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 2
	xor t1, t1, s4
	srli s4, t4, 2
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 2
	xor t4, t4, s4
	srli s4, t5, 2
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 2
	xor t5, t5, s4
	srli s4, t0, 1
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 1
	xor t0, t0, s4
	srli s4, t2, 1
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 1
	xor t2, t2, s4
	srli s4, t4, 1
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 1
	xor t4, t4, s4
	srli s4, t6, 1
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 1
	xor t6, t6, s4
	sd t0, 384(s0)
	sd t1, 392(s0)
	sd t2, 400(s0)
	sd t3, 408(s0)
	sd t4, 416(s0)
	sd t5, 424(s0)
	sd t6, 432(s0)
	sd a7, 440(s0)
	ld t0, 448(s0)
	ld t1, 456(s0)
	ld t2, 464(s0)
	ld t3, 472(s0)
	ld t4, 480(s0)
	ld t5, 488(s0)
	ld t6, 496(s0)
	ld a7, 504(s0)
	srli s4, t0, 4
	xor s4, s4, t4
	and s4, s4, s1
	xor t4, t4, s4
	slli s4, s4, 4
	xor t0, t0, s4
	srli s4, t1, 4
	xor s4, s4, t5
	and s4, s4, s1
	xor t5, t5, s4
	slli s4, s4, 4
	xor t1, t1, s4
	srli s4, t2, 4
	xor s4, s4, t6
	and s4, s4, s1
	xor t6, t6, s4
	slli s4, s4, 4
	xor t2, t2, s4
	srli s4, t3, 4
	xor s4, s4, a7
	and s4, s4, s1
	xor a7, a7, s4
	slli s4, s4, 4
	xor t3, t3, s4
	srli s4, t0, 2
	xor s4, s4, t2
	and s4, s4, s2
	xor t2, t2, s4
	slli s4, s4, 2
	xor t0, t0, s4
	srli s4, t1, 2
	xor s4, s4, t3
	and s4, s4, s2
	xor t3, t3, s4
	slli s4, s4, 2
	xor t1, t1, s4
	srli s4, t4, 2
	xor s4, s4, t6
	and s4, s4, s2
	xor t6, t6, s4
	slli s4, s4, 2
	xor t4, t4, s4
	srli s4, t5, 2
	xor s4, s4, a7
	and s4, s4, s2
	xor a7, a7, s4
	slli s4, s4, 2
	xor t5, t5, s4
	srli s4, t0, 1
	xor s4, s4, t1
	and s4, s4, s3
	xor t1, t1, s4
	slli s4, s4, 1
	xor t0, t0, s4
	srli s4, t2, 1
	xor s4, s4, t3
	and s4, s4, s3
	xor t3, t3, s4
	slli s4, s4, 1
	xor t2, t2, s4
	srli s4, t4, 1
	xor s4, s4, t5
	and s4, s4, s3
	xor t5, t5, s4
	slli s4, s4, 1
	xor t4, t4, s4
	srli s4, t6, 1
	xor s4, s4, a7
	and s4, s4, s3
	xor a7, a7, s4
	slli s4, s4, 1
	xor t6, t6, s4
	sd t0, 448(s0)
	sd t1, 456(s0)
	sd t2, 464(s0)
	sd t3, 472(s0)
	sd t4, 480(s0)
	sd t5, 488(s0)
	sd t6, 496(s0)
	sd a7, 504(s0)
	srli t0, a2, 6
	beqz t0, 210f
	addi s5, zero, 512
	j 211f
210:
	slli s5, a2, 3
211:
	addi t2, s0, 0
	addi t3, a1, 0
	addi t4, s5, 0
212:
	lbu t1, 0(t2)
	sb t1, 0(t3)
	addi t2, t2, 1
	addi t3, t3, 1
	addi t4, t4, -1
	bnez t4, 212b
	add a1, a1, s5
	srli t0, s5, 3
	sub a2, a2, t0
	bnez a2, 23b
	addi t1, zero, 0
	addi t0, s0, 0
	addi t4, zero, 118
213:
	sd t1, 0(t0)
	addi t0, t0, 8
	addi t4, t4, -1
	bnez t4, 213b
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
	ret
	.option pop
