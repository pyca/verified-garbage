// The functions of `src/triple_des.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_triple_des_expand_key:
	lea rsp, [rsp-520]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx], rbx
	mov QWORD PTR [rcx+8], rbp
	mov QWORD PTR [rcx+16], r12
	mov QWORD PTR [rcx+24], r13
	mov QWORD PTR [rcx+32], r14
	mov QWORD PTR [rcx+40], r15
	mov rax, QWORD PTR [rdi]
	bswap rax
	mov rbx, 0
	mov rbp, rax
	and rbp, 268435456
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 1
	and rbp, 16909312
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 33
	and rbp, 16
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 35
	and rbp, 2048
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 37
	and rbp, 262144
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 10
	and rbp, 8454656
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 42
	and rbp, 8
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 44
	and rbp, 1024
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 46
	and rbp, 131072
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 47
	and rbp, 16777216
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 19
	and rbp, 4227328
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 51
	and rbp, 4
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 53
	and rbp, 512
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 54
	and rbp, 65536
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 56
	and rbp, 8388608
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 28
	and rbp, 2113664
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 60
	and rbp, 2
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 61
	and rbp, 256
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 63
	and rbp, 32768
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 33
	and rbp, 8
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 1
	and rbp, 4194304
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 37
	and rbp, 1056832
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 4
	and rbp, 1
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 38
	and rbp, 134217728
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 6
	and rbp, 128
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 8
	and rbp, 16384
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 42
	and rbp, 4
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 10
	and rbp, 2097152
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 46
	and rbp, 1073745952
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 47
	and rbp, 67633152
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 15
	and rbp, 64
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 17
	and rbp, 8192
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 51
	and rbp, 2
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 19
	and rbp, 1048576
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 55
	and rbp, 536870928
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 56
	and rbp, 33818624
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 24
	and rbp, 32
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 26
	and rbp, 4096
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 60
	and rbp, 1
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 28
	and rbp, 524288
	ror rbp, 33
	xor rbx, rbp
	mov r12, rbx
	shr r12, 28
	mov r13, rbx
	and r13, 268435455
	mov r14, 0
	mov r15, rdx
	add r15, 0
20:
	cmp r14, 2
	jb 21f
	cmp r14, 8
	je 23f
	cmp r14, 15
	je 25f
	mov rax, r12
	shr rax, 26
	ror r12, 62
	xor r12, rax
	and r12, 268435455
	mov rax, r13
	shr rax, 26
	ror r13, 62
	xor r13, rax
	and r13, 268435455
	jmp 26f
25:
	mov rax, r12
	shr rax, 27
	ror r12, 63
	xor r12, rax
	and r12, 268435455
	mov rax, r13
	shr rax, 27
	ror r13, 63
	xor r13, rax
	and r13, 268435455
26:
	jmp 24f
23:
	mov rax, r12
	shr rax, 27
	ror r12, 63
	xor r12, rax
	and r12, 268435455
	mov rax, r13
	shr rax, 27
	ror r13, 63
	xor r13, rax
	and r13, 268435455
24:
	jmp 22f
21:
	mov rax, r12
	shr rax, 27
	ror r12, 63
	xor r12, rax
	and r12, 268435455
	mov rax, r13
	shr rax, 27
	ror r13, 63
	xor r13, rax
	and r13, 268435455
22:
	mov rax, r12
	ror rax, 36
	xor rax, r13
	mov rbx, 0
	mov rbp, rax
	and rbp, 65536
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 31
	and rbp, 16384
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 1
	and rbp, 2048
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 2
	and rbp, 134217728
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 33
	and rbp, 256
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 3
	and rbp, 8
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 34
	and rbp, 8
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 4
	and rbp, 2097152
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 5
	and rbp, 32
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 8
	and rbp, 512
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 9
	and rbp, 131072
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 40
	and rbp, 2048
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 10
	and rbp, 67117072
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 41
	and rbp, 32
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 11
	and rbp, 536870912
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 42
	and rbp, 4
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 43
	and rbp, 5248
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 15
	and rbp, 128
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 18
	and rbp, 1107296260
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 51
	and rbp, 2
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 21
	and rbp, 268435456
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 24
	and rbp, 1
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 26
	and rbp, 2
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 30
	and rbp, 16777216
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 46
	and rbp, 4194304
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 47
	and rbp, 262144
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 19
	and rbp, 8704
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 54
	and rbp, 557056
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 56
	and rbp, 8388864
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 24
	and rbp, 32768
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 26
	and rbp, 65536
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 60
	and rbp, 4096
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 61
	and rbp, 17472
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 29
	and rbp, 80
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 63
	and rbp, 1048576
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 30
	and rbp, 1
	ror rbp, 33
	xor rbx, rbp
	mov QWORD PTR [r15], rbx
	add r15, 8
	add r14, 1
	cmp r14, 16
	jne 20b
	mov rax, QWORD PTR [rdi+8]
	bswap rax
	mov rbx, 0
	mov rbp, rax
	and rbp, 268435456
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 1
	and rbp, 16909312
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 33
	and rbp, 16
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 35
	and rbp, 2048
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 37
	and rbp, 262144
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 10
	and rbp, 8454656
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 42
	and rbp, 8
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 44
	and rbp, 1024
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 46
	and rbp, 131072
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 47
	and rbp, 16777216
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 19
	and rbp, 4227328
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 51
	and rbp, 4
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 53
	and rbp, 512
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 54
	and rbp, 65536
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 56
	and rbp, 8388608
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 28
	and rbp, 2113664
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 60
	and rbp, 2
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 61
	and rbp, 256
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 63
	and rbp, 32768
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 33
	and rbp, 8
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 1
	and rbp, 4194304
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 37
	and rbp, 1056832
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 4
	and rbp, 1
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 38
	and rbp, 134217728
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 6
	and rbp, 128
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 8
	and rbp, 16384
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 42
	and rbp, 4
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 10
	and rbp, 2097152
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 46
	and rbp, 1073745952
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 47
	and rbp, 67633152
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 15
	and rbp, 64
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 17
	and rbp, 8192
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 51
	and rbp, 2
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 19
	and rbp, 1048576
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 55
	and rbp, 536870928
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 56
	and rbp, 33818624
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 24
	and rbp, 32
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 26
	and rbp, 4096
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 60
	and rbp, 1
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 28
	and rbp, 524288
	ror rbp, 33
	xor rbx, rbp
	mov r12, rbx
	shr r12, 28
	mov r13, rbx
	and r13, 268435455
	mov r14, 0
	mov r15, rdx
	add r15, 128
27:
	cmp r14, 2
	jb 28f
	cmp r14, 8
	je 210f
	cmp r14, 15
	je 212f
	mov rax, r12
	shr rax, 26
	ror r12, 62
	xor r12, rax
	and r12, 268435455
	mov rax, r13
	shr rax, 26
	ror r13, 62
	xor r13, rax
	and r13, 268435455
	jmp 213f
212:
	mov rax, r12
	shr rax, 27
	ror r12, 63
	xor r12, rax
	and r12, 268435455
	mov rax, r13
	shr rax, 27
	ror r13, 63
	xor r13, rax
	and r13, 268435455
213:
	jmp 211f
210:
	mov rax, r12
	shr rax, 27
	ror r12, 63
	xor r12, rax
	and r12, 268435455
	mov rax, r13
	shr rax, 27
	ror r13, 63
	xor r13, rax
	and r13, 268435455
211:
	jmp 29f
28:
	mov rax, r12
	shr rax, 27
	ror r12, 63
	xor r12, rax
	and r12, 268435455
	mov rax, r13
	shr rax, 27
	ror r13, 63
	xor r13, rax
	and r13, 268435455
29:
	mov rax, r12
	ror rax, 36
	xor rax, r13
	mov rbx, 0
	mov rbp, rax
	and rbp, 65536
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 31
	and rbp, 16384
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 1
	and rbp, 2048
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 2
	and rbp, 134217728
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 33
	and rbp, 256
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 3
	and rbp, 8
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 34
	and rbp, 8
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 4
	and rbp, 2097152
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 5
	and rbp, 32
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 8
	and rbp, 512
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 9
	and rbp, 131072
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 40
	and rbp, 2048
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 10
	and rbp, 67117072
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 41
	and rbp, 32
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 11
	and rbp, 536870912
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 42
	and rbp, 4
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 43
	and rbp, 5248
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 15
	and rbp, 128
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 18
	and rbp, 1107296260
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 51
	and rbp, 2
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 21
	and rbp, 268435456
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 24
	and rbp, 1
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 26
	and rbp, 2
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 30
	and rbp, 16777216
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 46
	and rbp, 4194304
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 47
	and rbp, 262144
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 19
	and rbp, 8704
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 54
	and rbp, 557056
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 56
	and rbp, 8388864
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 24
	and rbp, 32768
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 26
	and rbp, 65536
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 60
	and rbp, 4096
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 61
	and rbp, 17472
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 29
	and rbp, 80
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 63
	and rbp, 1048576
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 30
	and rbp, 1
	ror rbp, 33
	xor rbx, rbp
	mov QWORD PTR [r15], rbx
	add r15, 8
	add r14, 1
	cmp r14, 16
	jne 27b
	cmp rsi, 16
	je 214f
	mov rax, QWORD PTR [rdi+16]
	bswap rax
	mov rbx, 0
	mov rbp, rax
	and rbp, 268435456
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 1
	and rbp, 16909312
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 33
	and rbp, 16
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 35
	and rbp, 2048
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 37
	and rbp, 262144
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 10
	and rbp, 8454656
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 42
	and rbp, 8
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 44
	and rbp, 1024
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 46
	and rbp, 131072
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 47
	and rbp, 16777216
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 19
	and rbp, 4227328
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 51
	and rbp, 4
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 53
	and rbp, 512
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 54
	and rbp, 65536
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 56
	and rbp, 8388608
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 28
	and rbp, 2113664
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 60
	and rbp, 2
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 61
	and rbp, 256
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 63
	and rbp, 32768
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 33
	and rbp, 8
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 1
	and rbp, 4194304
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 37
	and rbp, 1056832
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 4
	and rbp, 1
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 38
	and rbp, 134217728
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 6
	and rbp, 128
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 8
	and rbp, 16384
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 42
	and rbp, 4
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 10
	and rbp, 2097152
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 46
	and rbp, 1073745952
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 47
	and rbp, 67633152
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 15
	and rbp, 64
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 17
	and rbp, 8192
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 51
	and rbp, 2
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 19
	and rbp, 1048576
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 55
	and rbp, 536870928
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 56
	and rbp, 33818624
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 24
	and rbp, 32
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 26
	and rbp, 4096
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 60
	and rbp, 1
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 28
	and rbp, 524288
	ror rbp, 33
	xor rbx, rbp
	mov r12, rbx
	shr r12, 28
	mov r13, rbx
	and r13, 268435455
	mov r14, 0
	mov r15, rdx
	add r15, 256
216:
	cmp r14, 2
	jb 217f
	cmp r14, 8
	je 219f
	cmp r14, 15
	je 221f
	mov rax, r12
	shr rax, 26
	ror r12, 62
	xor r12, rax
	and r12, 268435455
	mov rax, r13
	shr rax, 26
	ror r13, 62
	xor r13, rax
	and r13, 268435455
	jmp 222f
221:
	mov rax, r12
	shr rax, 27
	ror r12, 63
	xor r12, rax
	and r12, 268435455
	mov rax, r13
	shr rax, 27
	ror r13, 63
	xor r13, rax
	and r13, 268435455
222:
	jmp 220f
219:
	mov rax, r12
	shr rax, 27
	ror r12, 63
	xor r12, rax
	and r12, 268435455
	mov rax, r13
	shr rax, 27
	ror r13, 63
	xor r13, rax
	and r13, 268435455
220:
	jmp 218f
217:
	mov rax, r12
	shr rax, 27
	ror r12, 63
	xor r12, rax
	and r12, 268435455
	mov rax, r13
	shr rax, 27
	ror r13, 63
	xor r13, rax
	and r13, 268435455
218:
	mov rax, r12
	ror rax, 36
	xor rax, r13
	mov rbx, 0
	mov rbp, rax
	and rbp, 65536
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 31
	and rbp, 16384
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 1
	and rbp, 2048
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 2
	and rbp, 134217728
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 33
	and rbp, 256
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 3
	and rbp, 8
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 34
	and rbp, 8
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 4
	and rbp, 2097152
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 5
	and rbp, 32
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 8
	and rbp, 512
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 9
	and rbp, 131072
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 40
	and rbp, 2048
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 10
	and rbp, 67117072
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 41
	and rbp, 32
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 11
	and rbp, 536870912
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 42
	and rbp, 4
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 43
	and rbp, 5248
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 15
	and rbp, 128
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 18
	and rbp, 1107296260
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 51
	and rbp, 2
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 21
	and rbp, 268435456
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 24
	and rbp, 1
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 26
	and rbp, 2
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 30
	and rbp, 16777216
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 46
	and rbp, 4194304
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 47
	and rbp, 262144
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 19
	and rbp, 8704
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 54
	and rbp, 557056
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 56
	and rbp, 8388864
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 24
	and rbp, 32768
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 26
	and rbp, 65536
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 60
	and rbp, 4096
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 61
	and rbp, 17472
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 29
	and rbp, 80
	ror rbp, 33
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 63
	and rbp, 1048576
	xor rbx, rbp
	mov rbp, rax
	ror rbp, 30
	and rbp, 1
	ror rbp, 33
	xor rbx, rbp
	mov QWORD PTR [r15], rbx
	add r15, 8
	add r14, 1
	cmp r14, 16
	jne 216b
	jmp 215f
214:
	mov rax, QWORD PTR [rdx]
	mov QWORD PTR [rdx+256], rax
	mov rax, QWORD PTR [rdx+8]
	mov QWORD PTR [rdx+264], rax
	mov rax, QWORD PTR [rdx+16]
	mov QWORD PTR [rdx+272], rax
	mov rax, QWORD PTR [rdx+24]
	mov QWORD PTR [rdx+280], rax
	mov rax, QWORD PTR [rdx+32]
	mov QWORD PTR [rdx+288], rax
	mov rax, QWORD PTR [rdx+40]
	mov QWORD PTR [rdx+296], rax
	mov rax, QWORD PTR [rdx+48]
	mov QWORD PTR [rdx+304], rax
	mov rax, QWORD PTR [rdx+56]
	mov QWORD PTR [rdx+312], rax
	mov rax, QWORD PTR [rdx+64]
	mov QWORD PTR [rdx+320], rax
	mov rax, QWORD PTR [rdx+72]
	mov QWORD PTR [rdx+328], rax
	mov rax, QWORD PTR [rdx+80]
	mov QWORD PTR [rdx+336], rax
	mov rax, QWORD PTR [rdx+88]
	mov QWORD PTR [rdx+344], rax
	mov rax, QWORD PTR [rdx+96]
	mov QWORD PTR [rdx+352], rax
	mov rax, QWORD PTR [rdx+104]
	mov QWORD PTR [rdx+360], rax
	mov rax, QWORD PTR [rdx+112]
	mov QWORD PTR [rdx+368], rax
	mov rax, QWORD PTR [rdx+120]
	mov QWORD PTR [rdx+376], rax
215:
	mov rbx, QWORD PTR [rcx]
	mov rbp, QWORD PTR [rcx+8]
	mov r12, QWORD PTR [rcx+16]
	mov r13, QWORD PTR [rcx+24]
	mov r14, QWORD PTR [rcx+32]
	mov r15, QWORD PTR [rcx+40]
	mov r11d, 0
	mov QWORD PTR [rsp+8], r11
	mov QWORD PTR [rsp+16], r11
	mov QWORD PTR [rsp+24], r11
	mov QWORD PTR [rsp+32], r11
	mov QWORD PTR [rsp+40], r11
	mov QWORD PTR [rsp+48], r11
	mov QWORD PTR [rsp+56], r11
	mov QWORD PTR [rsp+64], r11
	mov QWORD PTR [rsp+72], r11
	mov QWORD PTR [rsp+80], r11
	mov QWORD PTR [rsp+88], r11
	mov QWORD PTR [rsp+96], r11
	mov QWORD PTR [rsp+104], r11
	mov QWORD PTR [rsp+112], r11
	mov QWORD PTR [rsp+120], r11
	mov QWORD PTR [rsp+128], r11
	mov QWORD PTR [rsp+136], r11
	mov QWORD PTR [rsp+144], r11
	mov QWORD PTR [rsp+152], r11
	mov QWORD PTR [rsp+160], r11
	mov QWORD PTR [rsp+168], r11
	mov QWORD PTR [rsp+176], r11
	mov QWORD PTR [rsp+184], r11
	mov QWORD PTR [rsp+192], r11
	mov QWORD PTR [rsp+200], r11
	mov QWORD PTR [rsp+208], r11
	mov QWORD PTR [rsp+216], r11
	mov QWORD PTR [rsp+224], r11
	mov QWORD PTR [rsp+232], r11
	mov QWORD PTR [rsp+240], r11
	mov QWORD PTR [rsp+248], r11
	mov QWORD PTR [rsp+256], r11
	mov QWORD PTR [rsp+264], r11
	mov QWORD PTR [rsp+272], r11
	mov QWORD PTR [rsp+280], r11
	mov QWORD PTR [rsp+288], r11
	mov QWORD PTR [rsp+296], r11
	mov QWORD PTR [rsp+304], r11
	mov QWORD PTR [rsp+312], r11
	mov QWORD PTR [rsp+320], r11
	mov QWORD PTR [rsp+328], r11
	mov QWORD PTR [rsp+336], r11
	mov QWORD PTR [rsp+344], r11
	mov QWORD PTR [rsp+352], r11
	mov QWORD PTR [rsp+360], r11
	mov QWORD PTR [rsp+368], r11
	mov QWORD PTR [rsp+376], r11
	mov QWORD PTR [rsp+384], r11
	mov QWORD PTR [rsp+392], r11
	mov QWORD PTR [rsp+400], r11
	mov QWORD PTR [rsp+408], r11
	mov QWORD PTR [rsp+416], r11
	mov QWORD PTR [rsp+424], r11
	mov QWORD PTR [rsp+432], r11
	mov QWORD PTR [rsp+440], r11
	mov QWORD PTR [rsp+448], r11
	mov QWORD PTR [rsp+456], r11
	mov QWORD PTR [rsp+464], r11
	mov QWORD PTR [rsp+472], r11
	mov QWORD PTR [rsp+480], r11
	mov QWORD PTR [rsp+488], r11
	mov QWORD PTR [rsp+496], r11
	mov QWORD PTR [rsp+504], r11
	mov QWORD PTR [rsp+512], r11
	lea rsp, [rsp+520]
	ret
	.p2align 6

vg_triple_des_ecb_encrypt:
	lea rsp, [rsp-1032]
	mov rcx, rsp
	add rcx, 8
	call {vg_triple_des_ecb_encrypt_core}
	mov r11d, 0
	mov QWORD PTR [rsp+8], r11
	mov QWORD PTR [rsp+16], r11
	mov QWORD PTR [rsp+24], r11
	mov QWORD PTR [rsp+32], r11
	mov QWORD PTR [rsp+40], r11
	mov QWORD PTR [rsp+48], r11
	mov QWORD PTR [rsp+56], r11
	mov QWORD PTR [rsp+64], r11
	mov QWORD PTR [rsp+72], r11
	mov QWORD PTR [rsp+80], r11
	mov QWORD PTR [rsp+88], r11
	mov QWORD PTR [rsp+96], r11
	mov QWORD PTR [rsp+104], r11
	mov QWORD PTR [rsp+112], r11
	mov QWORD PTR [rsp+120], r11
	mov QWORD PTR [rsp+128], r11
	mov QWORD PTR [rsp+136], r11
	mov QWORD PTR [rsp+144], r11
	mov QWORD PTR [rsp+152], r11
	mov QWORD PTR [rsp+160], r11
	mov QWORD PTR [rsp+168], r11
	mov QWORD PTR [rsp+176], r11
	mov QWORD PTR [rsp+184], r11
	mov QWORD PTR [rsp+192], r11
	mov QWORD PTR [rsp+200], r11
	mov QWORD PTR [rsp+208], r11
	mov QWORD PTR [rsp+216], r11
	mov QWORD PTR [rsp+224], r11
	mov QWORD PTR [rsp+232], r11
	mov QWORD PTR [rsp+240], r11
	mov QWORD PTR [rsp+248], r11
	mov QWORD PTR [rsp+256], r11
	mov QWORD PTR [rsp+264], r11
	mov QWORD PTR [rsp+272], r11
	mov QWORD PTR [rsp+280], r11
	mov QWORD PTR [rsp+288], r11
	mov QWORD PTR [rsp+296], r11
	mov QWORD PTR [rsp+304], r11
	mov QWORD PTR [rsp+312], r11
	mov QWORD PTR [rsp+320], r11
	mov QWORD PTR [rsp+328], r11
	mov QWORD PTR [rsp+336], r11
	mov QWORD PTR [rsp+344], r11
	mov QWORD PTR [rsp+352], r11
	mov QWORD PTR [rsp+360], r11
	mov QWORD PTR [rsp+368], r11
	mov QWORD PTR [rsp+376], r11
	mov QWORD PTR [rsp+384], r11
	mov QWORD PTR [rsp+392], r11
	mov QWORD PTR [rsp+400], r11
	mov QWORD PTR [rsp+408], r11
	mov QWORD PTR [rsp+416], r11
	mov QWORD PTR [rsp+424], r11
	mov QWORD PTR [rsp+432], r11
	mov QWORD PTR [rsp+440], r11
	mov QWORD PTR [rsp+448], r11
	mov QWORD PTR [rsp+456], r11
	mov QWORD PTR [rsp+464], r11
	mov QWORD PTR [rsp+472], r11
	mov QWORD PTR [rsp+480], r11
	mov QWORD PTR [rsp+488], r11
	mov QWORD PTR [rsp+496], r11
	mov QWORD PTR [rsp+504], r11
	mov QWORD PTR [rsp+512], r11
	mov QWORD PTR [rsp+520], r11
	mov QWORD PTR [rsp+528], r11
	mov QWORD PTR [rsp+536], r11
	mov QWORD PTR [rsp+544], r11
	mov QWORD PTR [rsp+552], r11
	mov QWORD PTR [rsp+560], r11
	mov QWORD PTR [rsp+568], r11
	mov QWORD PTR [rsp+576], r11
	mov QWORD PTR [rsp+584], r11
	mov QWORD PTR [rsp+592], r11
	mov QWORD PTR [rsp+600], r11
	mov QWORD PTR [rsp+608], r11
	mov QWORD PTR [rsp+616], r11
	mov QWORD PTR [rsp+624], r11
	mov QWORD PTR [rsp+632], r11
	mov QWORD PTR [rsp+640], r11
	mov QWORD PTR [rsp+648], r11
	mov QWORD PTR [rsp+656], r11
	mov QWORD PTR [rsp+664], r11
	mov QWORD PTR [rsp+672], r11
	mov QWORD PTR [rsp+680], r11
	mov QWORD PTR [rsp+688], r11
	mov QWORD PTR [rsp+696], r11
	mov QWORD PTR [rsp+704], r11
	mov QWORD PTR [rsp+712], r11
	mov QWORD PTR [rsp+720], r11
	mov QWORD PTR [rsp+728], r11
	mov QWORD PTR [rsp+736], r11
	mov QWORD PTR [rsp+744], r11
	mov QWORD PTR [rsp+752], r11
	mov QWORD PTR [rsp+760], r11
	mov QWORD PTR [rsp+768], r11
	mov QWORD PTR [rsp+776], r11
	mov QWORD PTR [rsp+784], r11
	mov QWORD PTR [rsp+792], r11
	mov QWORD PTR [rsp+800], r11
	mov QWORD PTR [rsp+808], r11
	mov QWORD PTR [rsp+816], r11
	mov QWORD PTR [rsp+824], r11
	mov QWORD PTR [rsp+832], r11
	mov QWORD PTR [rsp+840], r11
	mov QWORD PTR [rsp+848], r11
	mov QWORD PTR [rsp+856], r11
	mov QWORD PTR [rsp+864], r11
	mov QWORD PTR [rsp+872], r11
	mov QWORD PTR [rsp+880], r11
	mov QWORD PTR [rsp+888], r11
	mov QWORD PTR [rsp+896], r11
	mov QWORD PTR [rsp+904], r11
	mov QWORD PTR [rsp+912], r11
	mov QWORD PTR [rsp+920], r11
	mov QWORD PTR [rsp+928], r11
	mov QWORD PTR [rsp+936], r11
	mov QWORD PTR [rsp+944], r11
	mov QWORD PTR [rsp+952], r11
	mov QWORD PTR [rsp+960], r11
	mov QWORD PTR [rsp+968], r11
	mov QWORD PTR [rsp+976], r11
	mov QWORD PTR [rsp+984], r11
	mov QWORD PTR [rsp+992], r11
	mov QWORD PTR [rsp+1000], r11
	mov QWORD PTR [rsp+1008], r11
	mov QWORD PTR [rsp+1016], r11
	mov QWORD PTR [rsp+1024], r11
	lea rsp, [rsp+1032]
	ret
	.p2align 6

vg_triple_des_ecb_decrypt:
	lea rsp, [rsp-1032]
	mov rcx, rsp
	add rcx, 8
	call {vg_triple_des_ecb_decrypt_core}
	mov r11d, 0
	mov QWORD PTR [rsp+8], r11
	mov QWORD PTR [rsp+16], r11
	mov QWORD PTR [rsp+24], r11
	mov QWORD PTR [rsp+32], r11
	mov QWORD PTR [rsp+40], r11
	mov QWORD PTR [rsp+48], r11
	mov QWORD PTR [rsp+56], r11
	mov QWORD PTR [rsp+64], r11
	mov QWORD PTR [rsp+72], r11
	mov QWORD PTR [rsp+80], r11
	mov QWORD PTR [rsp+88], r11
	mov QWORD PTR [rsp+96], r11
	mov QWORD PTR [rsp+104], r11
	mov QWORD PTR [rsp+112], r11
	mov QWORD PTR [rsp+120], r11
	mov QWORD PTR [rsp+128], r11
	mov QWORD PTR [rsp+136], r11
	mov QWORD PTR [rsp+144], r11
	mov QWORD PTR [rsp+152], r11
	mov QWORD PTR [rsp+160], r11
	mov QWORD PTR [rsp+168], r11
	mov QWORD PTR [rsp+176], r11
	mov QWORD PTR [rsp+184], r11
	mov QWORD PTR [rsp+192], r11
	mov QWORD PTR [rsp+200], r11
	mov QWORD PTR [rsp+208], r11
	mov QWORD PTR [rsp+216], r11
	mov QWORD PTR [rsp+224], r11
	mov QWORD PTR [rsp+232], r11
	mov QWORD PTR [rsp+240], r11
	mov QWORD PTR [rsp+248], r11
	mov QWORD PTR [rsp+256], r11
	mov QWORD PTR [rsp+264], r11
	mov QWORD PTR [rsp+272], r11
	mov QWORD PTR [rsp+280], r11
	mov QWORD PTR [rsp+288], r11
	mov QWORD PTR [rsp+296], r11
	mov QWORD PTR [rsp+304], r11
	mov QWORD PTR [rsp+312], r11
	mov QWORD PTR [rsp+320], r11
	mov QWORD PTR [rsp+328], r11
	mov QWORD PTR [rsp+336], r11
	mov QWORD PTR [rsp+344], r11
	mov QWORD PTR [rsp+352], r11
	mov QWORD PTR [rsp+360], r11
	mov QWORD PTR [rsp+368], r11
	mov QWORD PTR [rsp+376], r11
	mov QWORD PTR [rsp+384], r11
	mov QWORD PTR [rsp+392], r11
	mov QWORD PTR [rsp+400], r11
	mov QWORD PTR [rsp+408], r11
	mov QWORD PTR [rsp+416], r11
	mov QWORD PTR [rsp+424], r11
	mov QWORD PTR [rsp+432], r11
	mov QWORD PTR [rsp+440], r11
	mov QWORD PTR [rsp+448], r11
	mov QWORD PTR [rsp+456], r11
	mov QWORD PTR [rsp+464], r11
	mov QWORD PTR [rsp+472], r11
	mov QWORD PTR [rsp+480], r11
	mov QWORD PTR [rsp+488], r11
	mov QWORD PTR [rsp+496], r11
	mov QWORD PTR [rsp+504], r11
	mov QWORD PTR [rsp+512], r11
	mov QWORD PTR [rsp+520], r11
	mov QWORD PTR [rsp+528], r11
	mov QWORD PTR [rsp+536], r11
	mov QWORD PTR [rsp+544], r11
	mov QWORD PTR [rsp+552], r11
	mov QWORD PTR [rsp+560], r11
	mov QWORD PTR [rsp+568], r11
	mov QWORD PTR [rsp+576], r11
	mov QWORD PTR [rsp+584], r11
	mov QWORD PTR [rsp+592], r11
	mov QWORD PTR [rsp+600], r11
	mov QWORD PTR [rsp+608], r11
	mov QWORD PTR [rsp+616], r11
	mov QWORD PTR [rsp+624], r11
	mov QWORD PTR [rsp+632], r11
	mov QWORD PTR [rsp+640], r11
	mov QWORD PTR [rsp+648], r11
	mov QWORD PTR [rsp+656], r11
	mov QWORD PTR [rsp+664], r11
	mov QWORD PTR [rsp+672], r11
	mov QWORD PTR [rsp+680], r11
	mov QWORD PTR [rsp+688], r11
	mov QWORD PTR [rsp+696], r11
	mov QWORD PTR [rsp+704], r11
	mov QWORD PTR [rsp+712], r11
	mov QWORD PTR [rsp+720], r11
	mov QWORD PTR [rsp+728], r11
	mov QWORD PTR [rsp+736], r11
	mov QWORD PTR [rsp+744], r11
	mov QWORD PTR [rsp+752], r11
	mov QWORD PTR [rsp+760], r11
	mov QWORD PTR [rsp+768], r11
	mov QWORD PTR [rsp+776], r11
	mov QWORD PTR [rsp+784], r11
	mov QWORD PTR [rsp+792], r11
	mov QWORD PTR [rsp+800], r11
	mov QWORD PTR [rsp+808], r11
	mov QWORD PTR [rsp+816], r11
	mov QWORD PTR [rsp+824], r11
	mov QWORD PTR [rsp+832], r11
	mov QWORD PTR [rsp+840], r11
	mov QWORD PTR [rsp+848], r11
	mov QWORD PTR [rsp+856], r11
	mov QWORD PTR [rsp+864], r11
	mov QWORD PTR [rsp+872], r11
	mov QWORD PTR [rsp+880], r11
	mov QWORD PTR [rsp+888], r11
	mov QWORD PTR [rsp+896], r11
	mov QWORD PTR [rsp+904], r11
	mov QWORD PTR [rsp+912], r11
	mov QWORD PTR [rsp+920], r11
	mov QWORD PTR [rsp+928], r11
	mov QWORD PTR [rsp+936], r11
	mov QWORD PTR [rsp+944], r11
	mov QWORD PTR [rsp+952], r11
	mov QWORD PTR [rsp+960], r11
	mov QWORD PTR [rsp+968], r11
	mov QWORD PTR [rsp+976], r11
	mov QWORD PTR [rsp+984], r11
	mov QWORD PTR [rsp+992], r11
	mov QWORD PTR [rsp+1000], r11
	mov QWORD PTR [rsp+1008], r11
	mov QWORD PTR [rsp+1016], r11
	mov QWORD PTR [rsp+1024], r11
	lea rsp, [rsp+1032]
	ret
	.p2align 6

vg_triple_des_ecb_encrypt_avx2:
	lea rsp, [rsp-1032]
	mov rcx, rsp
	add rcx, 8
	cmp rdx, 256
	jb 20f
	mov QWORD PTR [rcx+1016], rbx
	mov QWORD PTR [rcx+1008], r12
	mov QWORD PTR [rcx+1000], r13
22:
	mov r11, 8
23:
	movabs rbx, 4294967295
	vmovq xmm13, rbx
	vpbroadcastq ymm13, xmm13
	movabs rbx, 281470681808895
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	movabs rbx, 71777214294589695
	vmovq xmm15, rbx
	vpbroadcastq ymm15, xmm15
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vmovdqu ymm1, YMMWORD PTR [rsi+256]
	vmovdqu ymm2, YMMWORD PTR [rsi+512]
	vmovdqu ymm3, YMMWORD PTR [rsi+768]
	vmovdqu ymm4, YMMWORD PTR [rsi+1024]
	vmovdqu ymm5, YMMWORD PTR [rsi+1280]
	vmovdqu ymm6, YMMWORD PTR [rsi+1536]
	vmovdqu ymm7, YMMWORD PTR [rsi+1792]
	vpsrlq ymm8, ymm0, 32
	vpxor ymm8, ymm8, ymm4
	vpand ymm8, ymm8, ymm13
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm8, ymm8, 32
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm1, 32
	vpxor ymm8, ymm8, ymm5
	vpand ymm8, ymm8, ymm13
	vpxor ymm5, ymm5, ymm8
	vpsllq ymm8, ymm8, 32
	vpxor ymm1, ymm1, ymm8
	vpsrlq ymm8, ymm2, 32
	vpxor ymm8, ymm8, ymm6
	vpand ymm8, ymm8, ymm13
	vpxor ymm6, ymm6, ymm8
	vpsllq ymm8, ymm8, 32
	vpxor ymm2, ymm2, ymm8
	vpsrlq ymm8, ymm3, 32
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm13
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 32
	vpxor ymm3, ymm3, ymm8
	vpsrlq ymm8, ymm0, 16
	vpxor ymm8, ymm8, ymm2
	vpand ymm8, ymm8, ymm14
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm8, ymm8, 16
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm1, 16
	vpxor ymm8, ymm8, ymm3
	vpand ymm8, ymm8, ymm14
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm8, ymm8, 16
	vpxor ymm1, ymm1, ymm8
	vpsrlq ymm8, ymm4, 16
	vpxor ymm8, ymm8, ymm6
	vpand ymm8, ymm8, ymm14
	vpxor ymm6, ymm6, ymm8
	vpsllq ymm8, ymm8, 16
	vpxor ymm4, ymm4, ymm8
	vpsrlq ymm8, ymm5, 16
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm14
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 16
	vpxor ymm5, ymm5, ymm8
	vpsrlq ymm8, ymm0, 8
	vpxor ymm8, ymm8, ymm1
	vpand ymm8, ymm8, ymm15
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm8, ymm8, 8
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm2, 8
	vpxor ymm8, ymm8, ymm3
	vpand ymm8, ymm8, ymm15
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm8, ymm8, 8
	vpxor ymm2, ymm2, ymm8
	vpsrlq ymm8, ymm4, 8
	vpxor ymm8, ymm8, ymm5
	vpand ymm8, ymm8, ymm15
	vpxor ymm5, ymm5, ymm8
	vpsllq ymm8, ymm8, 8
	vpxor ymm4, ymm4, ymm8
	vpsrlq ymm8, ymm6, 8
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm15
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 8
	vpxor ymm6, ymm6, ymm8
	vmovdqu YMMWORD PTR [rsi], ymm0
	vmovdqu YMMWORD PTR [rsi+256], ymm1
	vmovdqu YMMWORD PTR [rsi+512], ymm2
	vmovdqu YMMWORD PTR [rsi+768], ymm3
	vmovdqu YMMWORD PTR [rsi+1024], ymm4
	vmovdqu YMMWORD PTR [rsi+1280], ymm5
	vmovdqu YMMWORD PTR [rsi+1536], ymm6
	vmovdqu YMMWORD PTR [rsi+1792], ymm7
	add rsi, 32
	sub r11, 1
	jne 23b
	sub rsi, 256
	mov r11, 8
24:
	movabs rbx, 1085102592571150095
	vmovq xmm13, rbx
	vpbroadcastq ymm13, xmm13
	movabs rbx, 3689348814741910323
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	movabs rbx, 6148914691236517205
	vmovq xmm15, rbx
	vpbroadcastq ymm15, xmm15
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vmovdqu ymm2, YMMWORD PTR [rsi+64]
	vmovdqu ymm3, YMMWORD PTR [rsi+96]
	vmovdqu ymm4, YMMWORD PTR [rsi+128]
	vmovdqu ymm5, YMMWORD PTR [rsi+160]
	vmovdqu ymm6, YMMWORD PTR [rsi+192]
	vmovdqu ymm7, YMMWORD PTR [rsi+224]
	vpsrlq ymm8, ymm0, 4
	vpxor ymm8, ymm8, ymm4
	vpand ymm8, ymm8, ymm13
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm8, ymm8, 4
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm1, 4
	vpxor ymm8, ymm8, ymm5
	vpand ymm8, ymm8, ymm13
	vpxor ymm5, ymm5, ymm8
	vpsllq ymm8, ymm8, 4
	vpxor ymm1, ymm1, ymm8
	vpsrlq ymm8, ymm2, 4
	vpxor ymm8, ymm8, ymm6
	vpand ymm8, ymm8, ymm13
	vpxor ymm6, ymm6, ymm8
	vpsllq ymm8, ymm8, 4
	vpxor ymm2, ymm2, ymm8
	vpsrlq ymm8, ymm3, 4
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm13
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 4
	vpxor ymm3, ymm3, ymm8
	vpsrlq ymm8, ymm0, 2
	vpxor ymm8, ymm8, ymm2
	vpand ymm8, ymm8, ymm14
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm8, ymm8, 2
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm1, 2
	vpxor ymm8, ymm8, ymm3
	vpand ymm8, ymm8, ymm14
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm8, ymm8, 2
	vpxor ymm1, ymm1, ymm8
	vpsrlq ymm8, ymm4, 2
	vpxor ymm8, ymm8, ymm6
	vpand ymm8, ymm8, ymm14
	vpxor ymm6, ymm6, ymm8
	vpsllq ymm8, ymm8, 2
	vpxor ymm4, ymm4, ymm8
	vpsrlq ymm8, ymm5, 2
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm14
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 2
	vpxor ymm5, ymm5, ymm8
	vpsrlq ymm8, ymm0, 1
	vpxor ymm8, ymm8, ymm1
	vpand ymm8, ymm8, ymm15
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm8, ymm8, 1
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm2, 1
	vpxor ymm8, ymm8, ymm3
	vpand ymm8, ymm8, ymm15
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm8, ymm8, 1
	vpxor ymm2, ymm2, ymm8
	vpsrlq ymm8, ymm4, 1
	vpxor ymm8, ymm8, ymm5
	vpand ymm8, ymm8, ymm15
	vpxor ymm5, ymm5, ymm8
	vpsllq ymm8, ymm8, 1
	vpxor ymm4, ymm4, ymm8
	vpsrlq ymm8, ymm6, 1
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm15
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 1
	vpxor ymm6, ymm6, ymm8
	vmovdqu YMMWORD PTR [rsi], ymm0
	vmovdqu YMMWORD PTR [rsi+32], ymm1
	vmovdqu YMMWORD PTR [rsi+64], ymm2
	vmovdqu YMMWORD PTR [rsi+96], ymm3
	vmovdqu YMMWORD PTR [rsi+128], ymm4
	vmovdqu YMMWORD PTR [rsi+160], ymm5
	vmovdqu YMMWORD PTR [rsi+192], ymm6
	vmovdqu YMMWORD PTR [rsi+224], ymm7
	add rsi, 256
	sub r11, 1
	jne 24b
	sub rsi, 2048
	movabs rbx, -1
	vmovq xmm15, rbx
	vpbroadcastq ymm15, xmm15
	mov r11, 3
25:
	cmp r11, 3
	je 26f
	cmp r11, 2
	je 28f
	mov r8, rdi
	add r8, 256
	mov r9, 8
	jmp 29f
28:
	mov r8, rdi
	add r8, 248
	mov r9, -8
29:
	jmp 27f
26:
	mov r8, rdi
	add r8, 0
	mov r9, 8
27:
	mov r10, 16
	mov r12, rsi
	add r12, 32
	mov r13, rsi
210:
	mov rax, QWORD PTR [r8]
	add r8, r9
	ror rax, 48
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm5, YMMWORD PTR [r12]
	vpxor ymm5, ymm5, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm4, YMMWORD PTR [r12+1984]
	vpxor ymm4, ymm4, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm3, YMMWORD PTR [r12+1728]
	vpxor ymm3, ymm3, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm2, YMMWORD PTR [r12+1472]
	vpxor ymm2, ymm2, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm1, YMMWORD PTR [r12+1216]
	vpxor ymm1, ymm1, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm0, YMMWORD PTR [r12+960]
	vpxor ymm0, ymm0, ymm14
	vpandn ymm6, ymm1, ymm5
	vpxor ymm7, ymm2, ymm6
	vpor ymm8, ymm3, ymm0
	vpxor ymm9, ymm5, ymm3
	vpand ymm10, ymm8, ymm9
	vpxor ymm11, ymm2, ymm10
	vpandn ymm12, ymm7, ymm11
	vpxor ymm13, ymm1, ymm0
	vpxor ymm14, ymm3, ymm13
	vpandn ymm14, ymm14, ymm7
	vpor ymm10, ymm0, ymm10
	vpxor ymm10, ymm14, ymm10
	vpandn ymm14, ymm12, ymm10
	vpor ymm0, ymm5, ymm0
	vmovdqu YMMWORD PTR [rcx], ymm14
	vpor ymm14, ymm10, ymm0
	vpandn ymm11, ymm11, ymm1
	vmovdqu YMMWORD PTR [rcx+32], ymm1
	vpxor ymm1, ymm14, ymm11
	vpandn ymm0, ymm0, ymm2
	vpxor ymm0, ymm11, ymm0
	vpandn ymm9, ymm9, ymm13
	vpor ymm9, ymm0, ymm9
	vpandn ymm6, ymm6, ymm3
	vpxor ymm3, ymm7, ymm14
	vpandn ymm6, ymm6, ymm3
	vpxor ymm3, ymm6, ymm15
	vpand ymm10, ymm8, ymm10
	vpxor ymm10, ymm3, ymm10
	vpandn ymm1, ymm4, ymm1
	vpxor ymm1, ymm1, ymm10
	vpxor ymm6, ymm13, ymm6
	vpor ymm6, ymm11, ymm6
	vpxor ymm6, ymm8, ymm6
	vpxor ymm6, ymm5, ymm6
	vpxor ymm10, ymm10, ymm6
	vpor ymm12, ymm12, ymm4
	vpxor ymm12, ymm12, ymm10
	vpxor ymm14, ymm8, ymm14
	vpor ymm14, ymm9, ymm14
	vpxor ymm14, ymm6, ymm14
	vpor ymm10, ymm13, ymm10
	vpxor ymm10, ymm14, ymm10
	vmovdqu ymm13, YMMWORD PTR [rcx]
	vpor ymm8, ymm13, ymm4
	vpxor ymm10, ymm8, ymm10
	vmovdqu ymm8, YMMWORD PTR [rcx+32]
	vpor ymm7, ymm8, ymm7
	vpandn ymm14, ymm14, ymm7
	vpand ymm6, ymm13, ymm6
	vpxor ymm6, ymm14, ymm6
	vpor ymm4, ymm6, ymm4
	vpxor ymm9, ymm4, ymm9
	vmovdqa ymm0, ymm9
	vmovdqa ymm2, ymm10
	vmovdqa ymm3, ymm12
	vmovdqu ymm14, YMMWORD PTR [r13+256]
	vpxor ymm0, ymm0, ymm14
	vmovdqu YMMWORD PTR [r13+256], ymm0
	vmovdqu ymm14, YMMWORD PTR [r13+320]
	vpxor ymm1, ymm1, ymm14
	vmovdqu YMMWORD PTR [r13+320], ymm1
	vmovdqu ymm14, YMMWORD PTR [r13+1856]
	vpxor ymm2, ymm2, ymm14
	vmovdqu YMMWORD PTR [r13+1856], ymm2
	vmovdqu ymm14, YMMWORD PTR [r13+1920]
	vpxor ymm3, ymm3, ymm14
	vmovdqu YMMWORD PTR [r13+1920], ymm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm5, YMMWORD PTR [r12+1216]
	vpxor ymm5, ymm5, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm4, YMMWORD PTR [r12+960]
	vpxor ymm4, ymm4, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm3, YMMWORD PTR [r12+704]
	vpxor ymm3, ymm3, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm2, YMMWORD PTR [r12+448]
	vpxor ymm2, ymm2, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm1, YMMWORD PTR [r12+192]
	vpxor ymm1, ymm1, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm0, YMMWORD PTR [r12+1920]
	vpxor ymm0, ymm0, ymm14
	vpxor ymm6, ymm4, ymm1
	vpandn ymm7, ymm0, ymm5
	vpandn ymm7, ymm7, ymm1
	vpor ymm8, ymm4, ymm7
	vpandn ymm9, ymm0, ymm6
	vpand ymm10, ymm5, ymm6
	vpxor ymm10, ymm1, ymm10
	vpandn ymm1, ymm9, ymm10
	vpand ymm11, ymm3, ymm0
	vpxor ymm9, ymm7, ymm9
	vpand ymm9, ymm8, ymm9
	vpandn ymm7, ymm11, ymm9
	vpand ymm12, ymm3, ymm9
	vpxor ymm5, ymm5, ymm15
	vpxor ymm5, ymm12, ymm5
	vpxor ymm0, ymm0, ymm6
	vpandn ymm13, ymm11, ymm0
	vpxor ymm14, ymm5, ymm13
	vpandn ymm7, ymm7, ymm2
	vpxor ymm7, ymm7, ymm14
	vpandn ymm13, ymm13, ymm4
	vpxor ymm10, ymm10, ymm13
	vpandn ymm5, ymm10, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm5, ymm5, ymm3
	vpandn ymm4, ymm2, ymm8
	vpxor ymm4, ymm4, ymm5
	vpxor ymm13, ymm12, ymm13
	vpor ymm13, ymm3, ymm13
	vpxor ymm8, ymm8, ymm14
	vpor ymm11, ymm11, ymm8
	vpxor ymm3, ymm13, ymm11
	vpxor ymm14, ymm9, ymm14
	vpxor ymm14, ymm5, ymm14
	vpand ymm14, ymm11, ymm14
	vpand ymm13, ymm6, ymm13
	vpxor ymm13, ymm14, ymm13
	vpor ymm14, ymm13, ymm2
	vpxor ymm3, ymm14, ymm3
	vpandn ymm10, ymm10, ymm13
	vpor ymm8, ymm0, ymm8
	vpxor ymm8, ymm10, ymm8
	vpor ymm2, ymm1, ymm2
	vpxor ymm8, ymm2, ymm8
	vmovdqa ymm0, ymm8
	vmovdqa ymm1, ymm3
	vmovdqa ymm2, ymm7
	vmovdqa ymm3, ymm4
	vmovdqu ymm14, YMMWORD PTR [r13+1600]
	vpxor ymm0, ymm0, ymm14
	vmovdqu YMMWORD PTR [r13+1600], ymm0
	vmovdqu ymm14, YMMWORD PTR [r13+1728]
	vpxor ymm1, ymm1, ymm14
	vmovdqu YMMWORD PTR [r13+1728], ymm1
	vmovdqu ymm14, YMMWORD PTR [r13+1024]
	vpxor ymm2, ymm2, ymm14
	vmovdqu YMMWORD PTR [r13+1024], ymm2
	vmovdqu ymm14, YMMWORD PTR [r13+896]
	vpxor ymm3, ymm3, ymm14
	vmovdqu YMMWORD PTR [r13+896], ymm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm5, YMMWORD PTR [r12+192]
	vpxor ymm5, ymm5, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm4, YMMWORD PTR [r12+1920]
	vpxor ymm4, ymm4, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm3, YMMWORD PTR [r12+1664]
	vpxor ymm3, ymm3, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm2, YMMWORD PTR [r12+1408]
	vpxor ymm2, ymm2, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm1, YMMWORD PTR [r12+1152]
	vpxor ymm1, ymm1, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm0, YMMWORD PTR [r12+896]
	vpxor ymm0, ymm0, ymm14
	vpandn ymm6, ymm4, ymm5
	vpxor ymm7, ymm3, ymm0
	vpor ymm8, ymm6, ymm7
	vpxor ymm9, ymm2, ymm0
	vpandn ymm10, ymm5, ymm9
	vpxor ymm11, ymm8, ymm10
	vpxor ymm12, ymm4, ymm7
	vpandn ymm13, ymm0, ymm12
	vpxor ymm13, ymm8, ymm13
	vpandn ymm8, ymm13, ymm11
	vpand ymm14, ymm0, ymm11
	vpor ymm14, ymm2, ymm14
	vpand ymm14, ymm5, ymm14
	vpxor ymm14, ymm12, ymm14
	vmovdqu YMMWORD PTR [rcx], ymm6
	vpandn ymm6, ymm1, ymm11
	vpxor ymm6, ymm6, ymm14
	vpand ymm9, ymm7, ymm9
	vpxor ymm7, ymm5, ymm2
	vmovdqu YMMWORD PTR [rcx+32], ymm6
	vpxor ymm6, ymm13, ymm7
	vpor ymm6, ymm3, ymm6
	vpandn ymm9, ymm9, ymm6
	vpor ymm7, ymm10, ymm7
	vpandn ymm10, ymm7, ymm14
	vpand ymm0, ymm2, ymm0
	vpandn ymm6, ymm4, ymm0
	vpxor ymm6, ymm10, ymm6
	vpand ymm13, ymm13, ymm6
	vpor ymm0, ymm12, ymm0
	vpandn ymm13, ymm13, ymm0
	vpxor ymm13, ymm5, ymm13
	vpand ymm9, ymm9, ymm1
	vpxor ymm9, ymm9, ymm13
	vpxor ymm11, ymm11, ymm15
	vpor ymm4, ymm4, ymm11
	vpor ymm4, ymm3, ymm4
	vpxor ymm4, ymm12, ymm4
	vpxor ymm7, ymm7, ymm4
	vpandn ymm8, ymm8, ymm1
	vpxor ymm7, ymm8, ymm7
	vpand ymm11, ymm2, ymm11
	vpxor ymm11, ymm14, ymm11
	vpor ymm11, ymm4, ymm11
	vmovdqu ymm4, YMMWORD PTR [rcx]
	vpxor ymm13, ymm4, ymm13
	vpxor ymm13, ymm11, ymm13
	vpor ymm1, ymm6, ymm1
	vpxor ymm13, ymm1, ymm13
	vmovdqu ymm0, YMMWORD PTR [rcx+32]
	vmovdqa ymm1, ymm13
	vmovdqa ymm2, ymm9
	vmovdqa ymm3, ymm7
	vmovdqu ymm14, YMMWORD PTR [r13+704]
	vpxor ymm0, ymm0, ymm14
	vmovdqu YMMWORD PTR [r13+704], ymm0
	vmovdqu ymm14, YMMWORD PTR [r13+512]
	vpxor ymm1, ymm1, ymm14
	vmovdqu YMMWORD PTR [r13+512], ymm1
	vmovdqu ymm14, YMMWORD PTR [r13+128]
	vpxor ymm2, ymm2, ymm14
	vmovdqu YMMWORD PTR [r13+128], ymm2
	vmovdqu ymm14, YMMWORD PTR [r13+64]
	vpxor ymm3, ymm3, ymm14
	vmovdqu YMMWORD PTR [r13+64], ymm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm5, YMMWORD PTR [r12+1152]
	vpxor ymm5, ymm5, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm4, YMMWORD PTR [r12+896]
	vpxor ymm4, ymm4, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm3, YMMWORD PTR [r12+640]
	vpxor ymm3, ymm3, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm2, YMMWORD PTR [r12+384]
	vpxor ymm2, ymm2, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm1, YMMWORD PTR [r12+128]
	vpxor ymm1, ymm1, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm0, YMMWORD PTR [r12+1856]
	vpxor ymm0, ymm0, ymm14
	vpxor ymm5, ymm5, ymm3
	vpxor ymm3, ymm3, ymm1
	vpor ymm6, ymm4, ymm2
	vpxor ymm6, ymm1, ymm6
	vpandn ymm6, ymm6, ymm3
	vpandn ymm7, ymm4, ymm3
	vpxor ymm8, ymm2, ymm7
	vpor ymm9, ymm5, ymm8
	vpandn ymm9, ymm6, ymm9
	vpxor ymm10, ymm4, ymm9
	vpand ymm8, ymm8, ymm10
	vpandn ymm3, ymm8, ymm3
	vpxor ymm5, ymm5, ymm10
	vpandn ymm3, ymm3, ymm5
	vpxor ymm3, ymm6, ymm3
	vpxor ymm2, ymm4, ymm2
	vpor ymm7, ymm1, ymm7
	vpxor ymm7, ymm5, ymm7
	vpandn ymm5, ymm2, ymm7
	vpxor ymm5, ymm9, ymm5
	vpandn ymm9, ymm3, ymm0
	vpxor ymm9, ymm9, ymm5
	vpxor ymm5, ymm5, ymm15
	vpandn ymm1, ymm0, ymm3
	vpxor ymm1, ymm1, ymm5
	vpxor ymm5, ymm3, ymm5
	vpandn ymm2, ymm2, ymm5
	vpor ymm2, ymm8, ymm2
	vpxor ymm2, ymm7, ymm2
	vpor ymm7, ymm10, ymm0
	vpxor ymm7, ymm7, ymm2
	vpand ymm10, ymm0, ymm10
	vpxor ymm2, ymm10, ymm2
	vmovdqa ymm0, ymm2
	vmovdqu YMMWORD PTR [rcx], ymm1
	vmovdqa ymm1, ymm7
	vmovdqu ymm2, YMMWORD PTR [rcx]
	vmovdqa ymm3, ymm9
	vmovdqu ymm14, YMMWORD PTR [r13+1984]
	vpxor ymm0, ymm0, ymm14
	vmovdqu YMMWORD PTR [r13+1984], ymm0
	vmovdqu ymm14, YMMWORD PTR [r13+1664]
	vpxor ymm1, ymm1, ymm14
	vmovdqu YMMWORD PTR [r13+1664], ymm1
	vmovdqu ymm14, YMMWORD PTR [r13+1088]
	vpxor ymm2, ymm2, ymm14
	vmovdqu YMMWORD PTR [r13+1088], ymm2
	vmovdqu ymm14, YMMWORD PTR [r13+1536]
	vpxor ymm3, ymm3, ymm14
	vmovdqu YMMWORD PTR [r13+1536], ymm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm5, YMMWORD PTR [r12+128]
	vpxor ymm5, ymm5, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm4, YMMWORD PTR [r12+1856]
	vpxor ymm4, ymm4, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm3, YMMWORD PTR [r12+1600]
	vpxor ymm3, ymm3, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm2, YMMWORD PTR [r12+1344]
	vpxor ymm2, ymm2, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm1, YMMWORD PTR [r12+1088]
	vpxor ymm1, ymm1, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm0, YMMWORD PTR [r12+832]
	vpxor ymm0, ymm0, ymm14
	vpor ymm6, ymm5, ymm3
	vpandn ymm7, ymm0, ymm6
	vpxor ymm8, ymm5, ymm7
	vpxor ymm9, ymm3, ymm8
	vpor ymm10, ymm2, ymm9
	vpandn ymm7, ymm2, ymm7
	vpxor ymm7, ymm3, ymm7
	vpand ymm3, ymm1, ymm7
	vpor ymm9, ymm5, ymm9
	vpxor ymm3, ymm3, ymm9
	vpxor ymm3, ymm2, ymm3
	vpxor ymm0, ymm0, ymm3
	vpor ymm11, ymm8, ymm0
	vpand ymm12, ymm1, ymm11
	vpxor ymm13, ymm8, ymm12
	vpand ymm14, ymm2, ymm9
	vpxor ymm14, ymm13, ymm14
	vpandn ymm11, ymm5, ymm11
	vpxor ymm13, ymm7, ymm11
	vpxor ymm1, ymm1, ymm10
	vpandn ymm13, ymm13, ymm1
	vpxor ymm13, ymm13, ymm15
	vpandn ymm13, ymm4, ymm13
	vpxor ymm3, ymm13, ymm3
	vpandn ymm13, ymm12, ymm7
	vpxor ymm11, ymm11, ymm1
	vpor ymm11, ymm14, ymm11
	vpandn ymm13, ymm13, ymm11
	vpandn ymm11, ymm13, ymm10
	vpand ymm0, ymm0, ymm13
	vpxor ymm0, ymm1, ymm0
	vpand ymm9, ymm7, ymm9
	vpor ymm9, ymm0, ymm9
	vpxor ymm9, ymm12, ymm9
	vpand ymm9, ymm9, ymm4
	vpxor ymm14, ymm9, ymm14
	vpxor ymm6, ymm5, ymm6
	vpxor ymm6, ymm13, ymm6
	vpand ymm2, ymm2, ymm0
	vpxor ymm2, ymm6, ymm2
	vpor ymm11, ymm11, ymm4
	vpxor ymm11, ymm11, ymm2
	vpxor ymm7, ymm10, ymm7
	vpandn ymm2, ymm2, ymm7
	vpxor ymm0, ymm8, ymm0
	vpxor ymm0, ymm2, ymm0
	vpand ymm4, ymm10, ymm4
	vpxor ymm0, ymm4, ymm0
	vmovdqu YMMWORD PTR [rcx], ymm0
	vmovdqa ymm0, ymm14
	vmovdqa ymm1, ymm3
	vmovdqu ymm2, YMMWORD PTR [rcx]
	vmovdqa ymm3, ymm11
	vmovdqu ymm14, YMMWORD PTR [r13+1472]
	vpxor ymm0, ymm0, ymm14
	vmovdqu YMMWORD PTR [r13+1472], ymm0
	vmovdqu ymm14, YMMWORD PTR [r13+1792]
	vpxor ymm1, ymm1, ymm14
	vmovdqu YMMWORD PTR [r13+1792], ymm1
	vmovdqu ymm14, YMMWORD PTR [r13+640]
	vpxor ymm2, ymm2, ymm14
	vmovdqu YMMWORD PTR [r13+640], ymm2
	vmovdqu ymm14, YMMWORD PTR [r13+192]
	vpxor ymm3, ymm3, ymm14
	vmovdqu YMMWORD PTR [r13+192], ymm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm5, YMMWORD PTR [r12+1088]
	vpxor ymm5, ymm5, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm4, YMMWORD PTR [r12+832]
	vpxor ymm4, ymm4, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm3, YMMWORD PTR [r12+576]
	vpxor ymm3, ymm3, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm2, YMMWORD PTR [r12+320]
	vpxor ymm2, ymm2, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm1, YMMWORD PTR [r12+64]
	vpxor ymm1, ymm1, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm0, YMMWORD PTR [r12+1792]
	vpxor ymm0, ymm0, ymm14
	vpxor ymm6, ymm4, ymm1
	vpor ymm7, ymm4, ymm0
	vpand ymm7, ymm5, ymm7
	vpxor ymm6, ymm6, ymm7
	vpxor ymm8, ymm0, ymm6
	vpandn ymm9, ymm8, ymm1
	vpand ymm8, ymm5, ymm8
	vpxor ymm10, ymm4, ymm8
	vpxor ymm11, ymm5, ymm3
	vpor ymm12, ymm10, ymm11
	vpxor ymm13, ymm6, ymm12
	vpand ymm14, ymm3, ymm13
	vmovdqu YMMWORD PTR [rcx], ymm8
	vpandn ymm8, ymm0, ymm14
	vpor ymm10, ymm9, ymm10
	vmovdqu YMMWORD PTR [rcx+32], ymm6
	vpxor ymm6, ymm8, ymm10
	vmovdqu YMMWORD PTR [rcx+64], ymm9
	vpand ymm9, ymm6, ymm2
	vpxor ymm9, ymm9, ymm13
	vpxor ymm12, ymm4, ymm12
	vmovdqu YMMWORD PTR [rcx+96], ymm9
	vpandn ymm9, ymm12, ymm0
	vpxor ymm9, ymm3, ymm9
	vpandn ymm3, ymm14, ymm1
	vpor ymm3, ymm9, ymm3
	vpor ymm11, ymm4, ymm11
	vpxor ymm6, ymm6, ymm11
	vpor ymm7, ymm7, ymm3
	vpxor ymm7, ymm6, ymm7
	vpor ymm13, ymm5, ymm13
	vpand ymm13, ymm10, ymm13
	vpxor ymm13, ymm9, ymm13
	vpandn ymm8, ymm8, ymm13
	vmovdqu ymm10, YMMWORD PTR [rcx+64]
	vpor ymm10, ymm10, ymm2
	vpxor ymm8, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rcx+32]
	vpxor ymm13, ymm10, ymm13
	vpandn ymm13, ymm13, ymm1
	vpxor ymm11, ymm11, ymm15
	vpxor ymm11, ymm12, ymm11
	vpxor ymm13, ymm13, ymm11
	vpandn ymm13, ymm2, ymm13
	vpxor ymm7, ymm13, ymm7
	vmovdqu ymm13, YMMWORD PTR [rcx]
	vpxor ymm13, ymm0, ymm13
	vpxor ymm9, ymm5, ymm9
	vpand ymm9, ymm13, ymm9
	vpxor ymm11, ymm14, ymm11
	vpxor ymm11, ymm9, ymm11
	vpandn ymm2, ymm2, ymm3
	vpxor ymm11, ymm2, ymm11
	vmovdqu ymm0, YMMWORD PTR [rcx+96]
	vmovdqa ymm1, ymm8
	vmovdqa ymm2, ymm7
	vmovdqa ymm3, ymm11
	vmovdqu ymm14, YMMWORD PTR [r13+1344]
	vpxor ymm0, ymm0, ymm14
	vmovdqu YMMWORD PTR [r13+1344], ymm0
	vmovdqu ymm14, YMMWORD PTR [r13+1408]
	vpxor ymm1, ymm1, ymm14
	vmovdqu YMMWORD PTR [r13+1408], ymm1
	vmovdqu ymm14, YMMWORD PTR [r13+768]
	vpxor ymm2, ymm2, ymm14
	vmovdqu YMMWORD PTR [r13+768], ymm2
	vmovdqu ymm14, YMMWORD PTR [r13+1216]
	vpxor ymm3, ymm3, ymm14
	vmovdqu YMMWORD PTR [r13+1216], ymm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm5, YMMWORD PTR [r12+64]
	vpxor ymm5, ymm5, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm4, YMMWORD PTR [r12+1792]
	vpxor ymm4, ymm4, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm3, YMMWORD PTR [r12+1536]
	vpxor ymm3, ymm3, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm2, YMMWORD PTR [r12+1280]
	vpxor ymm2, ymm2, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm1, YMMWORD PTR [r12+1024]
	vpxor ymm1, ymm1, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm0, YMMWORD PTR [r12+768]
	vpxor ymm0, ymm0, ymm14
	vpxor ymm6, ymm2, ymm1
	vpxor ymm7, ymm3, ymm6
	vpand ymm8, ymm0, ymm7
	vpand ymm9, ymm2, ymm6
	vpxor ymm10, ymm4, ymm9
	vpand ymm11, ymm8, ymm10
	vpand ymm12, ymm0, ymm9
	vpxor ymm13, ymm3, ymm12
	vpor ymm14, ymm10, ymm13
	vpxor ymm6, ymm0, ymm6
	vmovdqu YMMWORD PTR [rcx], ymm0
	vpxor ymm0, ymm14, ymm6
	vmovdqu YMMWORD PTR [rcx+32], ymm9
	vpandn ymm9, ymm11, ymm5
	vpxor ymm0, ymm9, ymm0
	vpandn ymm7, ymm7, ymm1
	vpor ymm9, ymm10, ymm7
	vpxor ymm13, ymm8, ymm13
	vpxor ymm9, ymm9, ymm13
	vpxor ymm6, ymm8, ymm6
	vpandn ymm2, ymm6, ymm2
	vpandn ymm8, ymm2, ymm10
	vpxor ymm13, ymm1, ymm13
	vpxor ymm13, ymm8, ymm13
	vpandn ymm12, ymm12, ymm6
	vpor ymm2, ymm2, ymm12
	vpxor ymm14, ymm4, ymm14
	vpand ymm14, ymm13, ymm14
	vpxor ymm14, ymm2, ymm14
	vpand ymm6, ymm14, ymm5
	vpxor ymm6, ymm6, ymm13
	vpandn ymm3, ymm3, ymm10
	vpor ymm3, ymm12, ymm3
	vmovdqu ymm12, YMMWORD PTR [rcx+32]
	vpor ymm13, ymm12, ymm13
	vpand ymm13, ymm3, ymm13
	vpxor ymm14, ymm14, ymm13
	vpxor ymm2, ymm7, ymm2
	vmovdqu ymm7, YMMWORD PTR [rcx]
	vpand ymm2, ymm7, ymm2
	vpor ymm2, ymm11, ymm2
	vpxor ymm13, ymm13, ymm2
	vpandn ymm11, ymm5, ymm13
	vpxor ymm11, ymm11, ymm9
	vpand ymm2, ymm4, ymm2
	vpxor ymm9, ymm9, ymm15
	vpxor ymm9, ymm2, ymm9
	vpxor ymm9, ymm13, ymm9
	vpor ymm5, ymm14, ymm5
	vpxor ymm9, ymm5, ymm9
	vmovdqa ymm1, ymm6
	vmovdqa ymm2, ymm9
	vmovdqa ymm3, ymm11
	vmovdqu ymm14, YMMWORD PTR [r13+448]
	vpxor ymm0, ymm0, ymm14
	vmovdqu YMMWORD PTR [r13+448], ymm0
	vmovdqu ymm14, YMMWORD PTR [r13+576]
	vpxor ymm1, ymm1, ymm14
	vmovdqu YMMWORD PTR [r13+576], ymm1
	vmovdqu ymm14, YMMWORD PTR [r13+1152]
	vpxor ymm2, ymm2, ymm14
	vmovdqu YMMWORD PTR [r13+1152], ymm2
	vmovdqu ymm14, YMMWORD PTR [r13]
	vpxor ymm3, ymm3, ymm14
	vmovdqu YMMWORD PTR [r13], ymm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm5, YMMWORD PTR [r12+1024]
	vpxor ymm5, ymm5, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm4, YMMWORD PTR [r12+768]
	vpxor ymm4, ymm4, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm3, YMMWORD PTR [r12+512]
	vpxor ymm3, ymm3, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm2, YMMWORD PTR [r12+256]
	vpxor ymm2, ymm2, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm1, YMMWORD PTR [r12]
	vpxor ymm1, ymm1, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm0, YMMWORD PTR [r12+1984]
	vpxor ymm0, ymm0, ymm14
	vpandn ymm6, ymm4, ymm3
	vpandn ymm7, ymm3, ymm1
	vpxor ymm7, ymm2, ymm7
	vpand ymm8, ymm5, ymm7
	vpandn ymm9, ymm6, ymm8
	vpandn ymm10, ymm7, ymm4
	vpor ymm11, ymm5, ymm10
	vpandn ymm12, ymm3, ymm4
	vpxor ymm12, ymm1, ymm12
	vpand ymm13, ymm11, ymm12
	vpor ymm8, ymm8, ymm13
	vpxor ymm7, ymm7, ymm15
	vpxor ymm7, ymm13, ymm7
	vpandn ymm11, ymm11, ymm3
	vpxor ymm11, ymm7, ymm11
	vpxor ymm6, ymm6, ymm11
	vpor ymm7, ymm9, ymm0
	vpxor ymm7, ymm7, ymm6
	vpxor ymm6, ymm5, ymm6
	vpand ymm3, ymm1, ymm6
	vpxor ymm11, ymm4, ymm11
	vpxor ymm3, ymm3, ymm11
	vpxor ymm10, ymm10, ymm3
	vpxor ymm3, ymm8, ymm3
	vpor ymm3, ymm4, ymm3
	vpxor ymm6, ymm1, ymm6
	vpxor ymm6, ymm3, ymm6
	vpand ymm8, ymm8, ymm0
	vpxor ymm8, ymm8, ymm6
	vpxor ymm12, ymm12, ymm10
	vpor ymm11, ymm2, ymm11
	vpxor ymm11, ymm12, ymm11
	vpxor ymm5, ymm5, ymm11
	vpand ymm5, ymm5, ymm0
	vpxor ymm5, ymm5, ymm10
	vpandn ymm2, ymm2, ymm12
	vpand ymm2, ymm6, ymm2
	vpxor ymm11, ymm9, ymm11
	vpxor ymm11, ymm2, ymm11
	vpor ymm0, ymm11, ymm0
	vpxor ymm10, ymm0, ymm10
	vmovdqa ymm0, ymm5
	vmovdqa ymm1, ymm8
	vmovdqa ymm2, ymm7
	vmovdqa ymm3, ymm10
	vmovdqu ymm14, YMMWORD PTR [r13+832]
	vpxor ymm0, ymm0, ymm14
	vmovdqu YMMWORD PTR [r13+832], ymm0
	vmovdqu ymm14, YMMWORD PTR [r13+384]
	vpxor ymm1, ymm1, ymm14
	vmovdqu YMMWORD PTR [r13+384], ymm1
	vmovdqu ymm14, YMMWORD PTR [r13+1280]
	vpxor ymm2, ymm2, ymm14
	vmovdqu YMMWORD PTR [r13+1280], ymm2
	vmovdqu ymm14, YMMWORD PTR [r13+960]
	vpxor ymm3, ymm3, ymm14
	vmovdqu YMMWORD PTR [r13+960], ymm3
	mov rbx, r12
	mov r12, r13
	mov r13, rbx
	sub r10, 1
	jne 210b
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vmovdqu YMMWORD PTR [rsi], ymm1
	vmovdqu YMMWORD PTR [rsi+32], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+256]
	vmovdqu ymm1, YMMWORD PTR [rsi+288]
	vmovdqu YMMWORD PTR [rsi+256], ymm1
	vmovdqu YMMWORD PTR [rsi+288], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+512]
	vmovdqu ymm1, YMMWORD PTR [rsi+544]
	vmovdqu YMMWORD PTR [rsi+512], ymm1
	vmovdqu YMMWORD PTR [rsi+544], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+768]
	vmovdqu ymm1, YMMWORD PTR [rsi+800]
	vmovdqu YMMWORD PTR [rsi+768], ymm1
	vmovdqu YMMWORD PTR [rsi+800], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1024]
	vmovdqu ymm1, YMMWORD PTR [rsi+1056]
	vmovdqu YMMWORD PTR [rsi+1024], ymm1
	vmovdqu YMMWORD PTR [rsi+1056], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1280]
	vmovdqu ymm1, YMMWORD PTR [rsi+1312]
	vmovdqu YMMWORD PTR [rsi+1280], ymm1
	vmovdqu YMMWORD PTR [rsi+1312], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1536]
	vmovdqu ymm1, YMMWORD PTR [rsi+1568]
	vmovdqu YMMWORD PTR [rsi+1536], ymm1
	vmovdqu YMMWORD PTR [rsi+1568], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1792]
	vmovdqu ymm1, YMMWORD PTR [rsi+1824]
	vmovdqu YMMWORD PTR [rsi+1792], ymm1
	vmovdqu YMMWORD PTR [rsi+1824], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+64]
	vmovdqu ymm1, YMMWORD PTR [rsi+96]
	vmovdqu YMMWORD PTR [rsi+64], ymm1
	vmovdqu YMMWORD PTR [rsi+96], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+320]
	vmovdqu ymm1, YMMWORD PTR [rsi+352]
	vmovdqu YMMWORD PTR [rsi+320], ymm1
	vmovdqu YMMWORD PTR [rsi+352], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+576]
	vmovdqu ymm1, YMMWORD PTR [rsi+608]
	vmovdqu YMMWORD PTR [rsi+576], ymm1
	vmovdqu YMMWORD PTR [rsi+608], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+832]
	vmovdqu ymm1, YMMWORD PTR [rsi+864]
	vmovdqu YMMWORD PTR [rsi+832], ymm1
	vmovdqu YMMWORD PTR [rsi+864], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1088]
	vmovdqu ymm1, YMMWORD PTR [rsi+1120]
	vmovdqu YMMWORD PTR [rsi+1088], ymm1
	vmovdqu YMMWORD PTR [rsi+1120], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1344]
	vmovdqu ymm1, YMMWORD PTR [rsi+1376]
	vmovdqu YMMWORD PTR [rsi+1344], ymm1
	vmovdqu YMMWORD PTR [rsi+1376], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1600]
	vmovdqu ymm1, YMMWORD PTR [rsi+1632]
	vmovdqu YMMWORD PTR [rsi+1600], ymm1
	vmovdqu YMMWORD PTR [rsi+1632], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1856]
	vmovdqu ymm1, YMMWORD PTR [rsi+1888]
	vmovdqu YMMWORD PTR [rsi+1856], ymm1
	vmovdqu YMMWORD PTR [rsi+1888], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+128]
	vmovdqu ymm1, YMMWORD PTR [rsi+160]
	vmovdqu YMMWORD PTR [rsi+128], ymm1
	vmovdqu YMMWORD PTR [rsi+160], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+384]
	vmovdqu ymm1, YMMWORD PTR [rsi+416]
	vmovdqu YMMWORD PTR [rsi+384], ymm1
	vmovdqu YMMWORD PTR [rsi+416], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+640]
	vmovdqu ymm1, YMMWORD PTR [rsi+672]
	vmovdqu YMMWORD PTR [rsi+640], ymm1
	vmovdqu YMMWORD PTR [rsi+672], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+896]
	vmovdqu ymm1, YMMWORD PTR [rsi+928]
	vmovdqu YMMWORD PTR [rsi+896], ymm1
	vmovdqu YMMWORD PTR [rsi+928], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1152]
	vmovdqu ymm1, YMMWORD PTR [rsi+1184]
	vmovdqu YMMWORD PTR [rsi+1152], ymm1
	vmovdqu YMMWORD PTR [rsi+1184], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1408]
	vmovdqu ymm1, YMMWORD PTR [rsi+1440]
	vmovdqu YMMWORD PTR [rsi+1408], ymm1
	vmovdqu YMMWORD PTR [rsi+1440], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1664]
	vmovdqu ymm1, YMMWORD PTR [rsi+1696]
	vmovdqu YMMWORD PTR [rsi+1664], ymm1
	vmovdqu YMMWORD PTR [rsi+1696], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1920]
	vmovdqu ymm1, YMMWORD PTR [rsi+1952]
	vmovdqu YMMWORD PTR [rsi+1920], ymm1
	vmovdqu YMMWORD PTR [rsi+1952], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+192]
	vmovdqu ymm1, YMMWORD PTR [rsi+224]
	vmovdqu YMMWORD PTR [rsi+192], ymm1
	vmovdqu YMMWORD PTR [rsi+224], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+448]
	vmovdqu ymm1, YMMWORD PTR [rsi+480]
	vmovdqu YMMWORD PTR [rsi+448], ymm1
	vmovdqu YMMWORD PTR [rsi+480], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+704]
	vmovdqu ymm1, YMMWORD PTR [rsi+736]
	vmovdqu YMMWORD PTR [rsi+704], ymm1
	vmovdqu YMMWORD PTR [rsi+736], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+960]
	vmovdqu ymm1, YMMWORD PTR [rsi+992]
	vmovdqu YMMWORD PTR [rsi+960], ymm1
	vmovdqu YMMWORD PTR [rsi+992], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1216]
	vmovdqu ymm1, YMMWORD PTR [rsi+1248]
	vmovdqu YMMWORD PTR [rsi+1216], ymm1
	vmovdqu YMMWORD PTR [rsi+1248], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1472]
	vmovdqu ymm1, YMMWORD PTR [rsi+1504]
	vmovdqu YMMWORD PTR [rsi+1472], ymm1
	vmovdqu YMMWORD PTR [rsi+1504], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1728]
	vmovdqu ymm1, YMMWORD PTR [rsi+1760]
	vmovdqu YMMWORD PTR [rsi+1728], ymm1
	vmovdqu YMMWORD PTR [rsi+1760], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1984]
	vmovdqu ymm1, YMMWORD PTR [rsi+2016]
	vmovdqu YMMWORD PTR [rsi+1984], ymm1
	vmovdqu YMMWORD PTR [rsi+2016], ymm0
	sub r11, 1
	jne 25b
	mov r11, 8
211:
	movabs rbx, 4294967295
	vmovq xmm13, rbx
	vpbroadcastq ymm13, xmm13
	movabs rbx, 281470681808895
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	movabs rbx, 71777214294589695
	vmovq xmm15, rbx
	vpbroadcastq ymm15, xmm15
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vmovdqu ymm1, YMMWORD PTR [rsi+256]
	vmovdqu ymm2, YMMWORD PTR [rsi+512]
	vmovdqu ymm3, YMMWORD PTR [rsi+768]
	vmovdqu ymm4, YMMWORD PTR [rsi+1024]
	vmovdqu ymm5, YMMWORD PTR [rsi+1280]
	vmovdqu ymm6, YMMWORD PTR [rsi+1536]
	vmovdqu ymm7, YMMWORD PTR [rsi+1792]
	vpsrlq ymm8, ymm0, 32
	vpxor ymm8, ymm8, ymm4
	vpand ymm8, ymm8, ymm13
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm8, ymm8, 32
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm1, 32
	vpxor ymm8, ymm8, ymm5
	vpand ymm8, ymm8, ymm13
	vpxor ymm5, ymm5, ymm8
	vpsllq ymm8, ymm8, 32
	vpxor ymm1, ymm1, ymm8
	vpsrlq ymm8, ymm2, 32
	vpxor ymm8, ymm8, ymm6
	vpand ymm8, ymm8, ymm13
	vpxor ymm6, ymm6, ymm8
	vpsllq ymm8, ymm8, 32
	vpxor ymm2, ymm2, ymm8
	vpsrlq ymm8, ymm3, 32
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm13
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 32
	vpxor ymm3, ymm3, ymm8
	vpsrlq ymm8, ymm0, 16
	vpxor ymm8, ymm8, ymm2
	vpand ymm8, ymm8, ymm14
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm8, ymm8, 16
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm1, 16
	vpxor ymm8, ymm8, ymm3
	vpand ymm8, ymm8, ymm14
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm8, ymm8, 16
	vpxor ymm1, ymm1, ymm8
	vpsrlq ymm8, ymm4, 16
	vpxor ymm8, ymm8, ymm6
	vpand ymm8, ymm8, ymm14
	vpxor ymm6, ymm6, ymm8
	vpsllq ymm8, ymm8, 16
	vpxor ymm4, ymm4, ymm8
	vpsrlq ymm8, ymm5, 16
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm14
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 16
	vpxor ymm5, ymm5, ymm8
	vpsrlq ymm8, ymm0, 8
	vpxor ymm8, ymm8, ymm1
	vpand ymm8, ymm8, ymm15
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm8, ymm8, 8
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm2, 8
	vpxor ymm8, ymm8, ymm3
	vpand ymm8, ymm8, ymm15
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm8, ymm8, 8
	vpxor ymm2, ymm2, ymm8
	vpsrlq ymm8, ymm4, 8
	vpxor ymm8, ymm8, ymm5
	vpand ymm8, ymm8, ymm15
	vpxor ymm5, ymm5, ymm8
	vpsllq ymm8, ymm8, 8
	vpxor ymm4, ymm4, ymm8
	vpsrlq ymm8, ymm6, 8
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm15
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 8
	vpxor ymm6, ymm6, ymm8
	vmovdqu YMMWORD PTR [rsi], ymm0
	vmovdqu YMMWORD PTR [rsi+256], ymm1
	vmovdqu YMMWORD PTR [rsi+512], ymm2
	vmovdqu YMMWORD PTR [rsi+768], ymm3
	vmovdqu YMMWORD PTR [rsi+1024], ymm4
	vmovdqu YMMWORD PTR [rsi+1280], ymm5
	vmovdqu YMMWORD PTR [rsi+1536], ymm6
	vmovdqu YMMWORD PTR [rsi+1792], ymm7
	add rsi, 32
	sub r11, 1
	jne 211b
	sub rsi, 256
	mov r11, 8
212:
	movabs rbx, 1085102592571150095
	vmovq xmm13, rbx
	vpbroadcastq ymm13, xmm13
	movabs rbx, 3689348814741910323
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	movabs rbx, 6148914691236517205
	vmovq xmm15, rbx
	vpbroadcastq ymm15, xmm15
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vmovdqu ymm2, YMMWORD PTR [rsi+64]
	vmovdqu ymm3, YMMWORD PTR [rsi+96]
	vmovdqu ymm4, YMMWORD PTR [rsi+128]
	vmovdqu ymm5, YMMWORD PTR [rsi+160]
	vmovdqu ymm6, YMMWORD PTR [rsi+192]
	vmovdqu ymm7, YMMWORD PTR [rsi+224]
	vpsrlq ymm8, ymm0, 4
	vpxor ymm8, ymm8, ymm4
	vpand ymm8, ymm8, ymm13
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm8, ymm8, 4
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm1, 4
	vpxor ymm8, ymm8, ymm5
	vpand ymm8, ymm8, ymm13
	vpxor ymm5, ymm5, ymm8
	vpsllq ymm8, ymm8, 4
	vpxor ymm1, ymm1, ymm8
	vpsrlq ymm8, ymm2, 4
	vpxor ymm8, ymm8, ymm6
	vpand ymm8, ymm8, ymm13
	vpxor ymm6, ymm6, ymm8
	vpsllq ymm8, ymm8, 4
	vpxor ymm2, ymm2, ymm8
	vpsrlq ymm8, ymm3, 4
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm13
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 4
	vpxor ymm3, ymm3, ymm8
	vpsrlq ymm8, ymm0, 2
	vpxor ymm8, ymm8, ymm2
	vpand ymm8, ymm8, ymm14
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm8, ymm8, 2
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm1, 2
	vpxor ymm8, ymm8, ymm3
	vpand ymm8, ymm8, ymm14
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm8, ymm8, 2
	vpxor ymm1, ymm1, ymm8
	vpsrlq ymm8, ymm4, 2
	vpxor ymm8, ymm8, ymm6
	vpand ymm8, ymm8, ymm14
	vpxor ymm6, ymm6, ymm8
	vpsllq ymm8, ymm8, 2
	vpxor ymm4, ymm4, ymm8
	vpsrlq ymm8, ymm5, 2
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm14
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 2
	vpxor ymm5, ymm5, ymm8
	vpsrlq ymm8, ymm0, 1
	vpxor ymm8, ymm8, ymm1
	vpand ymm8, ymm8, ymm15
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm8, ymm8, 1
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm2, 1
	vpxor ymm8, ymm8, ymm3
	vpand ymm8, ymm8, ymm15
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm8, ymm8, 1
	vpxor ymm2, ymm2, ymm8
	vpsrlq ymm8, ymm4, 1
	vpxor ymm8, ymm8, ymm5
	vpand ymm8, ymm8, ymm15
	vpxor ymm5, ymm5, ymm8
	vpsllq ymm8, ymm8, 1
	vpxor ymm4, ymm4, ymm8
	vpsrlq ymm8, ymm6, 1
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm15
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 1
	vpxor ymm6, ymm6, ymm8
	vmovdqu YMMWORD PTR [rsi], ymm0
	vmovdqu YMMWORD PTR [rsi+32], ymm1
	vmovdqu YMMWORD PTR [rsi+64], ymm2
	vmovdqu YMMWORD PTR [rsi+96], ymm3
	vmovdqu YMMWORD PTR [rsi+128], ymm4
	vmovdqu YMMWORD PTR [rsi+160], ymm5
	vmovdqu YMMWORD PTR [rsi+192], ymm6
	vmovdqu YMMWORD PTR [rsi+224], ymm7
	add rsi, 256
	sub r11, 1
	jne 212b
	sub rsi, 2048
	add rsi, 2048
	sub rdx, 256
	cmp rdx, 256
	jae 22b
	mov rbx, QWORD PTR [rcx+1016]
	mov r12, QWORD PTR [rcx+1008]
	mov r13, QWORD PTR [rcx+1000]
	vzeroupper
	jmp 21f
20:
21:
	call {vg_triple_des_ecb_encrypt_core}
	mov r11d, 0
	mov QWORD PTR [rsp+8], r11
	mov QWORD PTR [rsp+16], r11
	mov QWORD PTR [rsp+24], r11
	mov QWORD PTR [rsp+32], r11
	mov QWORD PTR [rsp+40], r11
	mov QWORD PTR [rsp+48], r11
	mov QWORD PTR [rsp+56], r11
	mov QWORD PTR [rsp+64], r11
	mov QWORD PTR [rsp+72], r11
	mov QWORD PTR [rsp+80], r11
	mov QWORD PTR [rsp+88], r11
	mov QWORD PTR [rsp+96], r11
	mov QWORD PTR [rsp+104], r11
	mov QWORD PTR [rsp+112], r11
	mov QWORD PTR [rsp+120], r11
	mov QWORD PTR [rsp+128], r11
	mov QWORD PTR [rsp+136], r11
	mov QWORD PTR [rsp+144], r11
	mov QWORD PTR [rsp+152], r11
	mov QWORD PTR [rsp+160], r11
	mov QWORD PTR [rsp+168], r11
	mov QWORD PTR [rsp+176], r11
	mov QWORD PTR [rsp+184], r11
	mov QWORD PTR [rsp+192], r11
	mov QWORD PTR [rsp+200], r11
	mov QWORD PTR [rsp+208], r11
	mov QWORD PTR [rsp+216], r11
	mov QWORD PTR [rsp+224], r11
	mov QWORD PTR [rsp+232], r11
	mov QWORD PTR [rsp+240], r11
	mov QWORD PTR [rsp+248], r11
	mov QWORD PTR [rsp+256], r11
	mov QWORD PTR [rsp+264], r11
	mov QWORD PTR [rsp+272], r11
	mov QWORD PTR [rsp+280], r11
	mov QWORD PTR [rsp+288], r11
	mov QWORD PTR [rsp+296], r11
	mov QWORD PTR [rsp+304], r11
	mov QWORD PTR [rsp+312], r11
	mov QWORD PTR [rsp+320], r11
	mov QWORD PTR [rsp+328], r11
	mov QWORD PTR [rsp+336], r11
	mov QWORD PTR [rsp+344], r11
	mov QWORD PTR [rsp+352], r11
	mov QWORD PTR [rsp+360], r11
	mov QWORD PTR [rsp+368], r11
	mov QWORD PTR [rsp+376], r11
	mov QWORD PTR [rsp+384], r11
	mov QWORD PTR [rsp+392], r11
	mov QWORD PTR [rsp+400], r11
	mov QWORD PTR [rsp+408], r11
	mov QWORD PTR [rsp+416], r11
	mov QWORD PTR [rsp+424], r11
	mov QWORD PTR [rsp+432], r11
	mov QWORD PTR [rsp+440], r11
	mov QWORD PTR [rsp+448], r11
	mov QWORD PTR [rsp+456], r11
	mov QWORD PTR [rsp+464], r11
	mov QWORD PTR [rsp+472], r11
	mov QWORD PTR [rsp+480], r11
	mov QWORD PTR [rsp+488], r11
	mov QWORD PTR [rsp+496], r11
	mov QWORD PTR [rsp+504], r11
	mov QWORD PTR [rsp+512], r11
	mov QWORD PTR [rsp+520], r11
	mov QWORD PTR [rsp+528], r11
	mov QWORD PTR [rsp+536], r11
	mov QWORD PTR [rsp+544], r11
	mov QWORD PTR [rsp+552], r11
	mov QWORD PTR [rsp+560], r11
	mov QWORD PTR [rsp+568], r11
	mov QWORD PTR [rsp+576], r11
	mov QWORD PTR [rsp+584], r11
	mov QWORD PTR [rsp+592], r11
	mov QWORD PTR [rsp+600], r11
	mov QWORD PTR [rsp+608], r11
	mov QWORD PTR [rsp+616], r11
	mov QWORD PTR [rsp+624], r11
	mov QWORD PTR [rsp+632], r11
	mov QWORD PTR [rsp+640], r11
	mov QWORD PTR [rsp+648], r11
	mov QWORD PTR [rsp+656], r11
	mov QWORD PTR [rsp+664], r11
	mov QWORD PTR [rsp+672], r11
	mov QWORD PTR [rsp+680], r11
	mov QWORD PTR [rsp+688], r11
	mov QWORD PTR [rsp+696], r11
	mov QWORD PTR [rsp+704], r11
	mov QWORD PTR [rsp+712], r11
	mov QWORD PTR [rsp+720], r11
	mov QWORD PTR [rsp+728], r11
	mov QWORD PTR [rsp+736], r11
	mov QWORD PTR [rsp+744], r11
	mov QWORD PTR [rsp+752], r11
	mov QWORD PTR [rsp+760], r11
	mov QWORD PTR [rsp+768], r11
	mov QWORD PTR [rsp+776], r11
	mov QWORD PTR [rsp+784], r11
	mov QWORD PTR [rsp+792], r11
	mov QWORD PTR [rsp+800], r11
	mov QWORD PTR [rsp+808], r11
	mov QWORD PTR [rsp+816], r11
	mov QWORD PTR [rsp+824], r11
	mov QWORD PTR [rsp+832], r11
	mov QWORD PTR [rsp+840], r11
	mov QWORD PTR [rsp+848], r11
	mov QWORD PTR [rsp+856], r11
	mov QWORD PTR [rsp+864], r11
	mov QWORD PTR [rsp+872], r11
	mov QWORD PTR [rsp+880], r11
	mov QWORD PTR [rsp+888], r11
	mov QWORD PTR [rsp+896], r11
	mov QWORD PTR [rsp+904], r11
	mov QWORD PTR [rsp+912], r11
	mov QWORD PTR [rsp+920], r11
	mov QWORD PTR [rsp+928], r11
	mov QWORD PTR [rsp+936], r11
	mov QWORD PTR [rsp+944], r11
	mov QWORD PTR [rsp+952], r11
	mov QWORD PTR [rsp+960], r11
	mov QWORD PTR [rsp+968], r11
	mov QWORD PTR [rsp+976], r11
	mov QWORD PTR [rsp+984], r11
	mov QWORD PTR [rsp+992], r11
	mov QWORD PTR [rsp+1000], r11
	mov QWORD PTR [rsp+1008], r11
	mov QWORD PTR [rsp+1016], r11
	mov QWORD PTR [rsp+1024], r11
	lea rsp, [rsp+1032]
	ret
	.p2align 6

vg_triple_des_ecb_decrypt_avx2:
	lea rsp, [rsp-1032]
	mov rcx, rsp
	add rcx, 8
	cmp rdx, 256
	jb 20f
	mov QWORD PTR [rcx+1016], rbx
	mov QWORD PTR [rcx+1008], r12
	mov QWORD PTR [rcx+1000], r13
22:
	mov r11, 8
23:
	movabs rbx, 4294967295
	vmovq xmm13, rbx
	vpbroadcastq ymm13, xmm13
	movabs rbx, 281470681808895
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	movabs rbx, 71777214294589695
	vmovq xmm15, rbx
	vpbroadcastq ymm15, xmm15
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vmovdqu ymm1, YMMWORD PTR [rsi+256]
	vmovdqu ymm2, YMMWORD PTR [rsi+512]
	vmovdqu ymm3, YMMWORD PTR [rsi+768]
	vmovdqu ymm4, YMMWORD PTR [rsi+1024]
	vmovdqu ymm5, YMMWORD PTR [rsi+1280]
	vmovdqu ymm6, YMMWORD PTR [rsi+1536]
	vmovdqu ymm7, YMMWORD PTR [rsi+1792]
	vpsrlq ymm8, ymm0, 32
	vpxor ymm8, ymm8, ymm4
	vpand ymm8, ymm8, ymm13
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm8, ymm8, 32
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm1, 32
	vpxor ymm8, ymm8, ymm5
	vpand ymm8, ymm8, ymm13
	vpxor ymm5, ymm5, ymm8
	vpsllq ymm8, ymm8, 32
	vpxor ymm1, ymm1, ymm8
	vpsrlq ymm8, ymm2, 32
	vpxor ymm8, ymm8, ymm6
	vpand ymm8, ymm8, ymm13
	vpxor ymm6, ymm6, ymm8
	vpsllq ymm8, ymm8, 32
	vpxor ymm2, ymm2, ymm8
	vpsrlq ymm8, ymm3, 32
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm13
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 32
	vpxor ymm3, ymm3, ymm8
	vpsrlq ymm8, ymm0, 16
	vpxor ymm8, ymm8, ymm2
	vpand ymm8, ymm8, ymm14
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm8, ymm8, 16
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm1, 16
	vpxor ymm8, ymm8, ymm3
	vpand ymm8, ymm8, ymm14
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm8, ymm8, 16
	vpxor ymm1, ymm1, ymm8
	vpsrlq ymm8, ymm4, 16
	vpxor ymm8, ymm8, ymm6
	vpand ymm8, ymm8, ymm14
	vpxor ymm6, ymm6, ymm8
	vpsllq ymm8, ymm8, 16
	vpxor ymm4, ymm4, ymm8
	vpsrlq ymm8, ymm5, 16
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm14
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 16
	vpxor ymm5, ymm5, ymm8
	vpsrlq ymm8, ymm0, 8
	vpxor ymm8, ymm8, ymm1
	vpand ymm8, ymm8, ymm15
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm8, ymm8, 8
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm2, 8
	vpxor ymm8, ymm8, ymm3
	vpand ymm8, ymm8, ymm15
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm8, ymm8, 8
	vpxor ymm2, ymm2, ymm8
	vpsrlq ymm8, ymm4, 8
	vpxor ymm8, ymm8, ymm5
	vpand ymm8, ymm8, ymm15
	vpxor ymm5, ymm5, ymm8
	vpsllq ymm8, ymm8, 8
	vpxor ymm4, ymm4, ymm8
	vpsrlq ymm8, ymm6, 8
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm15
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 8
	vpxor ymm6, ymm6, ymm8
	vmovdqu YMMWORD PTR [rsi], ymm0
	vmovdqu YMMWORD PTR [rsi+256], ymm1
	vmovdqu YMMWORD PTR [rsi+512], ymm2
	vmovdqu YMMWORD PTR [rsi+768], ymm3
	vmovdqu YMMWORD PTR [rsi+1024], ymm4
	vmovdqu YMMWORD PTR [rsi+1280], ymm5
	vmovdqu YMMWORD PTR [rsi+1536], ymm6
	vmovdqu YMMWORD PTR [rsi+1792], ymm7
	add rsi, 32
	sub r11, 1
	jne 23b
	sub rsi, 256
	mov r11, 8
24:
	movabs rbx, 1085102592571150095
	vmovq xmm13, rbx
	vpbroadcastq ymm13, xmm13
	movabs rbx, 3689348814741910323
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	movabs rbx, 6148914691236517205
	vmovq xmm15, rbx
	vpbroadcastq ymm15, xmm15
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vmovdqu ymm2, YMMWORD PTR [rsi+64]
	vmovdqu ymm3, YMMWORD PTR [rsi+96]
	vmovdqu ymm4, YMMWORD PTR [rsi+128]
	vmovdqu ymm5, YMMWORD PTR [rsi+160]
	vmovdqu ymm6, YMMWORD PTR [rsi+192]
	vmovdqu ymm7, YMMWORD PTR [rsi+224]
	vpsrlq ymm8, ymm0, 4
	vpxor ymm8, ymm8, ymm4
	vpand ymm8, ymm8, ymm13
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm8, ymm8, 4
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm1, 4
	vpxor ymm8, ymm8, ymm5
	vpand ymm8, ymm8, ymm13
	vpxor ymm5, ymm5, ymm8
	vpsllq ymm8, ymm8, 4
	vpxor ymm1, ymm1, ymm8
	vpsrlq ymm8, ymm2, 4
	vpxor ymm8, ymm8, ymm6
	vpand ymm8, ymm8, ymm13
	vpxor ymm6, ymm6, ymm8
	vpsllq ymm8, ymm8, 4
	vpxor ymm2, ymm2, ymm8
	vpsrlq ymm8, ymm3, 4
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm13
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 4
	vpxor ymm3, ymm3, ymm8
	vpsrlq ymm8, ymm0, 2
	vpxor ymm8, ymm8, ymm2
	vpand ymm8, ymm8, ymm14
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm8, ymm8, 2
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm1, 2
	vpxor ymm8, ymm8, ymm3
	vpand ymm8, ymm8, ymm14
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm8, ymm8, 2
	vpxor ymm1, ymm1, ymm8
	vpsrlq ymm8, ymm4, 2
	vpxor ymm8, ymm8, ymm6
	vpand ymm8, ymm8, ymm14
	vpxor ymm6, ymm6, ymm8
	vpsllq ymm8, ymm8, 2
	vpxor ymm4, ymm4, ymm8
	vpsrlq ymm8, ymm5, 2
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm14
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 2
	vpxor ymm5, ymm5, ymm8
	vpsrlq ymm8, ymm0, 1
	vpxor ymm8, ymm8, ymm1
	vpand ymm8, ymm8, ymm15
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm8, ymm8, 1
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm2, 1
	vpxor ymm8, ymm8, ymm3
	vpand ymm8, ymm8, ymm15
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm8, ymm8, 1
	vpxor ymm2, ymm2, ymm8
	vpsrlq ymm8, ymm4, 1
	vpxor ymm8, ymm8, ymm5
	vpand ymm8, ymm8, ymm15
	vpxor ymm5, ymm5, ymm8
	vpsllq ymm8, ymm8, 1
	vpxor ymm4, ymm4, ymm8
	vpsrlq ymm8, ymm6, 1
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm15
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 1
	vpxor ymm6, ymm6, ymm8
	vmovdqu YMMWORD PTR [rsi], ymm0
	vmovdqu YMMWORD PTR [rsi+32], ymm1
	vmovdqu YMMWORD PTR [rsi+64], ymm2
	vmovdqu YMMWORD PTR [rsi+96], ymm3
	vmovdqu YMMWORD PTR [rsi+128], ymm4
	vmovdqu YMMWORD PTR [rsi+160], ymm5
	vmovdqu YMMWORD PTR [rsi+192], ymm6
	vmovdqu YMMWORD PTR [rsi+224], ymm7
	add rsi, 256
	sub r11, 1
	jne 24b
	sub rsi, 2048
	movabs rbx, -1
	vmovq xmm15, rbx
	vpbroadcastq ymm15, xmm15
	mov r11, 3
25:
	cmp r11, 3
	je 26f
	cmp r11, 2
	je 28f
	mov r8, rdi
	add r8, 120
	mov r9, -8
	jmp 29f
28:
	mov r8, rdi
	add r8, 128
	mov r9, 8
29:
	jmp 27f
26:
	mov r8, rdi
	add r8, 376
	mov r9, -8
27:
	mov r10, 16
	mov r12, rsi
	add r12, 32
	mov r13, rsi
210:
	mov rax, QWORD PTR [r8]
	add r8, r9
	ror rax, 48
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm5, YMMWORD PTR [r12]
	vpxor ymm5, ymm5, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm4, YMMWORD PTR [r12+1984]
	vpxor ymm4, ymm4, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm3, YMMWORD PTR [r12+1728]
	vpxor ymm3, ymm3, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm2, YMMWORD PTR [r12+1472]
	vpxor ymm2, ymm2, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm1, YMMWORD PTR [r12+1216]
	vpxor ymm1, ymm1, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm0, YMMWORD PTR [r12+960]
	vpxor ymm0, ymm0, ymm14
	vpandn ymm6, ymm1, ymm5
	vpxor ymm7, ymm2, ymm6
	vpor ymm8, ymm3, ymm0
	vpxor ymm9, ymm5, ymm3
	vpand ymm10, ymm8, ymm9
	vpxor ymm11, ymm2, ymm10
	vpandn ymm12, ymm7, ymm11
	vpxor ymm13, ymm1, ymm0
	vpxor ymm14, ymm3, ymm13
	vpandn ymm14, ymm14, ymm7
	vpor ymm10, ymm0, ymm10
	vpxor ymm10, ymm14, ymm10
	vpandn ymm14, ymm12, ymm10
	vpor ymm0, ymm5, ymm0
	vmovdqu YMMWORD PTR [rcx], ymm14
	vpor ymm14, ymm10, ymm0
	vpandn ymm11, ymm11, ymm1
	vmovdqu YMMWORD PTR [rcx+32], ymm1
	vpxor ymm1, ymm14, ymm11
	vpandn ymm0, ymm0, ymm2
	vpxor ymm0, ymm11, ymm0
	vpandn ymm9, ymm9, ymm13
	vpor ymm9, ymm0, ymm9
	vpandn ymm6, ymm6, ymm3
	vpxor ymm3, ymm7, ymm14
	vpandn ymm6, ymm6, ymm3
	vpxor ymm3, ymm6, ymm15
	vpand ymm10, ymm8, ymm10
	vpxor ymm10, ymm3, ymm10
	vpandn ymm1, ymm4, ymm1
	vpxor ymm1, ymm1, ymm10
	vpxor ymm6, ymm13, ymm6
	vpor ymm6, ymm11, ymm6
	vpxor ymm6, ymm8, ymm6
	vpxor ymm6, ymm5, ymm6
	vpxor ymm10, ymm10, ymm6
	vpor ymm12, ymm12, ymm4
	vpxor ymm12, ymm12, ymm10
	vpxor ymm14, ymm8, ymm14
	vpor ymm14, ymm9, ymm14
	vpxor ymm14, ymm6, ymm14
	vpor ymm10, ymm13, ymm10
	vpxor ymm10, ymm14, ymm10
	vmovdqu ymm13, YMMWORD PTR [rcx]
	vpor ymm8, ymm13, ymm4
	vpxor ymm10, ymm8, ymm10
	vmovdqu ymm8, YMMWORD PTR [rcx+32]
	vpor ymm7, ymm8, ymm7
	vpandn ymm14, ymm14, ymm7
	vpand ymm6, ymm13, ymm6
	vpxor ymm6, ymm14, ymm6
	vpor ymm4, ymm6, ymm4
	vpxor ymm9, ymm4, ymm9
	vmovdqa ymm0, ymm9
	vmovdqa ymm2, ymm10
	vmovdqa ymm3, ymm12
	vmovdqu ymm14, YMMWORD PTR [r13+256]
	vpxor ymm0, ymm0, ymm14
	vmovdqu YMMWORD PTR [r13+256], ymm0
	vmovdqu ymm14, YMMWORD PTR [r13+320]
	vpxor ymm1, ymm1, ymm14
	vmovdqu YMMWORD PTR [r13+320], ymm1
	vmovdqu ymm14, YMMWORD PTR [r13+1856]
	vpxor ymm2, ymm2, ymm14
	vmovdqu YMMWORD PTR [r13+1856], ymm2
	vmovdqu ymm14, YMMWORD PTR [r13+1920]
	vpxor ymm3, ymm3, ymm14
	vmovdqu YMMWORD PTR [r13+1920], ymm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm5, YMMWORD PTR [r12+1216]
	vpxor ymm5, ymm5, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm4, YMMWORD PTR [r12+960]
	vpxor ymm4, ymm4, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm3, YMMWORD PTR [r12+704]
	vpxor ymm3, ymm3, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm2, YMMWORD PTR [r12+448]
	vpxor ymm2, ymm2, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm1, YMMWORD PTR [r12+192]
	vpxor ymm1, ymm1, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm0, YMMWORD PTR [r12+1920]
	vpxor ymm0, ymm0, ymm14
	vpxor ymm6, ymm4, ymm1
	vpandn ymm7, ymm0, ymm5
	vpandn ymm7, ymm7, ymm1
	vpor ymm8, ymm4, ymm7
	vpandn ymm9, ymm0, ymm6
	vpand ymm10, ymm5, ymm6
	vpxor ymm10, ymm1, ymm10
	vpandn ymm1, ymm9, ymm10
	vpand ymm11, ymm3, ymm0
	vpxor ymm9, ymm7, ymm9
	vpand ymm9, ymm8, ymm9
	vpandn ymm7, ymm11, ymm9
	vpand ymm12, ymm3, ymm9
	vpxor ymm5, ymm5, ymm15
	vpxor ymm5, ymm12, ymm5
	vpxor ymm0, ymm0, ymm6
	vpandn ymm13, ymm11, ymm0
	vpxor ymm14, ymm5, ymm13
	vpandn ymm7, ymm7, ymm2
	vpxor ymm7, ymm7, ymm14
	vpandn ymm13, ymm13, ymm4
	vpxor ymm10, ymm10, ymm13
	vpandn ymm5, ymm10, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm5, ymm5, ymm3
	vpandn ymm4, ymm2, ymm8
	vpxor ymm4, ymm4, ymm5
	vpxor ymm13, ymm12, ymm13
	vpor ymm13, ymm3, ymm13
	vpxor ymm8, ymm8, ymm14
	vpor ymm11, ymm11, ymm8
	vpxor ymm3, ymm13, ymm11
	vpxor ymm14, ymm9, ymm14
	vpxor ymm14, ymm5, ymm14
	vpand ymm14, ymm11, ymm14
	vpand ymm13, ymm6, ymm13
	vpxor ymm13, ymm14, ymm13
	vpor ymm14, ymm13, ymm2
	vpxor ymm3, ymm14, ymm3
	vpandn ymm10, ymm10, ymm13
	vpor ymm8, ymm0, ymm8
	vpxor ymm8, ymm10, ymm8
	vpor ymm2, ymm1, ymm2
	vpxor ymm8, ymm2, ymm8
	vmovdqa ymm0, ymm8
	vmovdqa ymm1, ymm3
	vmovdqa ymm2, ymm7
	vmovdqa ymm3, ymm4
	vmovdqu ymm14, YMMWORD PTR [r13+1600]
	vpxor ymm0, ymm0, ymm14
	vmovdqu YMMWORD PTR [r13+1600], ymm0
	vmovdqu ymm14, YMMWORD PTR [r13+1728]
	vpxor ymm1, ymm1, ymm14
	vmovdqu YMMWORD PTR [r13+1728], ymm1
	vmovdqu ymm14, YMMWORD PTR [r13+1024]
	vpxor ymm2, ymm2, ymm14
	vmovdqu YMMWORD PTR [r13+1024], ymm2
	vmovdqu ymm14, YMMWORD PTR [r13+896]
	vpxor ymm3, ymm3, ymm14
	vmovdqu YMMWORD PTR [r13+896], ymm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm5, YMMWORD PTR [r12+192]
	vpxor ymm5, ymm5, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm4, YMMWORD PTR [r12+1920]
	vpxor ymm4, ymm4, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm3, YMMWORD PTR [r12+1664]
	vpxor ymm3, ymm3, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm2, YMMWORD PTR [r12+1408]
	vpxor ymm2, ymm2, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm1, YMMWORD PTR [r12+1152]
	vpxor ymm1, ymm1, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm0, YMMWORD PTR [r12+896]
	vpxor ymm0, ymm0, ymm14
	vpandn ymm6, ymm4, ymm5
	vpxor ymm7, ymm3, ymm0
	vpor ymm8, ymm6, ymm7
	vpxor ymm9, ymm2, ymm0
	vpandn ymm10, ymm5, ymm9
	vpxor ymm11, ymm8, ymm10
	vpxor ymm12, ymm4, ymm7
	vpandn ymm13, ymm0, ymm12
	vpxor ymm13, ymm8, ymm13
	vpandn ymm8, ymm13, ymm11
	vpand ymm14, ymm0, ymm11
	vpor ymm14, ymm2, ymm14
	vpand ymm14, ymm5, ymm14
	vpxor ymm14, ymm12, ymm14
	vmovdqu YMMWORD PTR [rcx], ymm6
	vpandn ymm6, ymm1, ymm11
	vpxor ymm6, ymm6, ymm14
	vpand ymm9, ymm7, ymm9
	vpxor ymm7, ymm5, ymm2
	vmovdqu YMMWORD PTR [rcx+32], ymm6
	vpxor ymm6, ymm13, ymm7
	vpor ymm6, ymm3, ymm6
	vpandn ymm9, ymm9, ymm6
	vpor ymm7, ymm10, ymm7
	vpandn ymm10, ymm7, ymm14
	vpand ymm0, ymm2, ymm0
	vpandn ymm6, ymm4, ymm0
	vpxor ymm6, ymm10, ymm6
	vpand ymm13, ymm13, ymm6
	vpor ymm0, ymm12, ymm0
	vpandn ymm13, ymm13, ymm0
	vpxor ymm13, ymm5, ymm13
	vpand ymm9, ymm9, ymm1
	vpxor ymm9, ymm9, ymm13
	vpxor ymm11, ymm11, ymm15
	vpor ymm4, ymm4, ymm11
	vpor ymm4, ymm3, ymm4
	vpxor ymm4, ymm12, ymm4
	vpxor ymm7, ymm7, ymm4
	vpandn ymm8, ymm8, ymm1
	vpxor ymm7, ymm8, ymm7
	vpand ymm11, ymm2, ymm11
	vpxor ymm11, ymm14, ymm11
	vpor ymm11, ymm4, ymm11
	vmovdqu ymm4, YMMWORD PTR [rcx]
	vpxor ymm13, ymm4, ymm13
	vpxor ymm13, ymm11, ymm13
	vpor ymm1, ymm6, ymm1
	vpxor ymm13, ymm1, ymm13
	vmovdqu ymm0, YMMWORD PTR [rcx+32]
	vmovdqa ymm1, ymm13
	vmovdqa ymm2, ymm9
	vmovdqa ymm3, ymm7
	vmovdqu ymm14, YMMWORD PTR [r13+704]
	vpxor ymm0, ymm0, ymm14
	vmovdqu YMMWORD PTR [r13+704], ymm0
	vmovdqu ymm14, YMMWORD PTR [r13+512]
	vpxor ymm1, ymm1, ymm14
	vmovdqu YMMWORD PTR [r13+512], ymm1
	vmovdqu ymm14, YMMWORD PTR [r13+128]
	vpxor ymm2, ymm2, ymm14
	vmovdqu YMMWORD PTR [r13+128], ymm2
	vmovdqu ymm14, YMMWORD PTR [r13+64]
	vpxor ymm3, ymm3, ymm14
	vmovdqu YMMWORD PTR [r13+64], ymm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm5, YMMWORD PTR [r12+1152]
	vpxor ymm5, ymm5, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm4, YMMWORD PTR [r12+896]
	vpxor ymm4, ymm4, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm3, YMMWORD PTR [r12+640]
	vpxor ymm3, ymm3, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm2, YMMWORD PTR [r12+384]
	vpxor ymm2, ymm2, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm1, YMMWORD PTR [r12+128]
	vpxor ymm1, ymm1, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm0, YMMWORD PTR [r12+1856]
	vpxor ymm0, ymm0, ymm14
	vpxor ymm5, ymm5, ymm3
	vpxor ymm3, ymm3, ymm1
	vpor ymm6, ymm4, ymm2
	vpxor ymm6, ymm1, ymm6
	vpandn ymm6, ymm6, ymm3
	vpandn ymm7, ymm4, ymm3
	vpxor ymm8, ymm2, ymm7
	vpor ymm9, ymm5, ymm8
	vpandn ymm9, ymm6, ymm9
	vpxor ymm10, ymm4, ymm9
	vpand ymm8, ymm8, ymm10
	vpandn ymm3, ymm8, ymm3
	vpxor ymm5, ymm5, ymm10
	vpandn ymm3, ymm3, ymm5
	vpxor ymm3, ymm6, ymm3
	vpxor ymm2, ymm4, ymm2
	vpor ymm7, ymm1, ymm7
	vpxor ymm7, ymm5, ymm7
	vpandn ymm5, ymm2, ymm7
	vpxor ymm5, ymm9, ymm5
	vpandn ymm9, ymm3, ymm0
	vpxor ymm9, ymm9, ymm5
	vpxor ymm5, ymm5, ymm15
	vpandn ymm1, ymm0, ymm3
	vpxor ymm1, ymm1, ymm5
	vpxor ymm5, ymm3, ymm5
	vpandn ymm2, ymm2, ymm5
	vpor ymm2, ymm8, ymm2
	vpxor ymm2, ymm7, ymm2
	vpor ymm7, ymm10, ymm0
	vpxor ymm7, ymm7, ymm2
	vpand ymm10, ymm0, ymm10
	vpxor ymm2, ymm10, ymm2
	vmovdqa ymm0, ymm2
	vmovdqu YMMWORD PTR [rcx], ymm1
	vmovdqa ymm1, ymm7
	vmovdqu ymm2, YMMWORD PTR [rcx]
	vmovdqa ymm3, ymm9
	vmovdqu ymm14, YMMWORD PTR [r13+1984]
	vpxor ymm0, ymm0, ymm14
	vmovdqu YMMWORD PTR [r13+1984], ymm0
	vmovdqu ymm14, YMMWORD PTR [r13+1664]
	vpxor ymm1, ymm1, ymm14
	vmovdqu YMMWORD PTR [r13+1664], ymm1
	vmovdqu ymm14, YMMWORD PTR [r13+1088]
	vpxor ymm2, ymm2, ymm14
	vmovdqu YMMWORD PTR [r13+1088], ymm2
	vmovdqu ymm14, YMMWORD PTR [r13+1536]
	vpxor ymm3, ymm3, ymm14
	vmovdqu YMMWORD PTR [r13+1536], ymm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm5, YMMWORD PTR [r12+128]
	vpxor ymm5, ymm5, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm4, YMMWORD PTR [r12+1856]
	vpxor ymm4, ymm4, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm3, YMMWORD PTR [r12+1600]
	vpxor ymm3, ymm3, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm2, YMMWORD PTR [r12+1344]
	vpxor ymm2, ymm2, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm1, YMMWORD PTR [r12+1088]
	vpxor ymm1, ymm1, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm0, YMMWORD PTR [r12+832]
	vpxor ymm0, ymm0, ymm14
	vpor ymm6, ymm5, ymm3
	vpandn ymm7, ymm0, ymm6
	vpxor ymm8, ymm5, ymm7
	vpxor ymm9, ymm3, ymm8
	vpor ymm10, ymm2, ymm9
	vpandn ymm7, ymm2, ymm7
	vpxor ymm7, ymm3, ymm7
	vpand ymm3, ymm1, ymm7
	vpor ymm9, ymm5, ymm9
	vpxor ymm3, ymm3, ymm9
	vpxor ymm3, ymm2, ymm3
	vpxor ymm0, ymm0, ymm3
	vpor ymm11, ymm8, ymm0
	vpand ymm12, ymm1, ymm11
	vpxor ymm13, ymm8, ymm12
	vpand ymm14, ymm2, ymm9
	vpxor ymm14, ymm13, ymm14
	vpandn ymm11, ymm5, ymm11
	vpxor ymm13, ymm7, ymm11
	vpxor ymm1, ymm1, ymm10
	vpandn ymm13, ymm13, ymm1
	vpxor ymm13, ymm13, ymm15
	vpandn ymm13, ymm4, ymm13
	vpxor ymm3, ymm13, ymm3
	vpandn ymm13, ymm12, ymm7
	vpxor ymm11, ymm11, ymm1
	vpor ymm11, ymm14, ymm11
	vpandn ymm13, ymm13, ymm11
	vpandn ymm11, ymm13, ymm10
	vpand ymm0, ymm0, ymm13
	vpxor ymm0, ymm1, ymm0
	vpand ymm9, ymm7, ymm9
	vpor ymm9, ymm0, ymm9
	vpxor ymm9, ymm12, ymm9
	vpand ymm9, ymm9, ymm4
	vpxor ymm14, ymm9, ymm14
	vpxor ymm6, ymm5, ymm6
	vpxor ymm6, ymm13, ymm6
	vpand ymm2, ymm2, ymm0
	vpxor ymm2, ymm6, ymm2
	vpor ymm11, ymm11, ymm4
	vpxor ymm11, ymm11, ymm2
	vpxor ymm7, ymm10, ymm7
	vpandn ymm2, ymm2, ymm7
	vpxor ymm0, ymm8, ymm0
	vpxor ymm0, ymm2, ymm0
	vpand ymm4, ymm10, ymm4
	vpxor ymm0, ymm4, ymm0
	vmovdqu YMMWORD PTR [rcx], ymm0
	vmovdqa ymm0, ymm14
	vmovdqa ymm1, ymm3
	vmovdqu ymm2, YMMWORD PTR [rcx]
	vmovdqa ymm3, ymm11
	vmovdqu ymm14, YMMWORD PTR [r13+1472]
	vpxor ymm0, ymm0, ymm14
	vmovdqu YMMWORD PTR [r13+1472], ymm0
	vmovdqu ymm14, YMMWORD PTR [r13+1792]
	vpxor ymm1, ymm1, ymm14
	vmovdqu YMMWORD PTR [r13+1792], ymm1
	vmovdqu ymm14, YMMWORD PTR [r13+640]
	vpxor ymm2, ymm2, ymm14
	vmovdqu YMMWORD PTR [r13+640], ymm2
	vmovdqu ymm14, YMMWORD PTR [r13+192]
	vpxor ymm3, ymm3, ymm14
	vmovdqu YMMWORD PTR [r13+192], ymm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm5, YMMWORD PTR [r12+1088]
	vpxor ymm5, ymm5, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm4, YMMWORD PTR [r12+832]
	vpxor ymm4, ymm4, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm3, YMMWORD PTR [r12+576]
	vpxor ymm3, ymm3, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm2, YMMWORD PTR [r12+320]
	vpxor ymm2, ymm2, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm1, YMMWORD PTR [r12+64]
	vpxor ymm1, ymm1, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm0, YMMWORD PTR [r12+1792]
	vpxor ymm0, ymm0, ymm14
	vpxor ymm6, ymm4, ymm1
	vpor ymm7, ymm4, ymm0
	vpand ymm7, ymm5, ymm7
	vpxor ymm6, ymm6, ymm7
	vpxor ymm8, ymm0, ymm6
	vpandn ymm9, ymm8, ymm1
	vpand ymm8, ymm5, ymm8
	vpxor ymm10, ymm4, ymm8
	vpxor ymm11, ymm5, ymm3
	vpor ymm12, ymm10, ymm11
	vpxor ymm13, ymm6, ymm12
	vpand ymm14, ymm3, ymm13
	vmovdqu YMMWORD PTR [rcx], ymm8
	vpandn ymm8, ymm0, ymm14
	vpor ymm10, ymm9, ymm10
	vmovdqu YMMWORD PTR [rcx+32], ymm6
	vpxor ymm6, ymm8, ymm10
	vmovdqu YMMWORD PTR [rcx+64], ymm9
	vpand ymm9, ymm6, ymm2
	vpxor ymm9, ymm9, ymm13
	vpxor ymm12, ymm4, ymm12
	vmovdqu YMMWORD PTR [rcx+96], ymm9
	vpandn ymm9, ymm12, ymm0
	vpxor ymm9, ymm3, ymm9
	vpandn ymm3, ymm14, ymm1
	vpor ymm3, ymm9, ymm3
	vpor ymm11, ymm4, ymm11
	vpxor ymm6, ymm6, ymm11
	vpor ymm7, ymm7, ymm3
	vpxor ymm7, ymm6, ymm7
	vpor ymm13, ymm5, ymm13
	vpand ymm13, ymm10, ymm13
	vpxor ymm13, ymm9, ymm13
	vpandn ymm8, ymm8, ymm13
	vmovdqu ymm10, YMMWORD PTR [rcx+64]
	vpor ymm10, ymm10, ymm2
	vpxor ymm8, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rcx+32]
	vpxor ymm13, ymm10, ymm13
	vpandn ymm13, ymm13, ymm1
	vpxor ymm11, ymm11, ymm15
	vpxor ymm11, ymm12, ymm11
	vpxor ymm13, ymm13, ymm11
	vpandn ymm13, ymm2, ymm13
	vpxor ymm7, ymm13, ymm7
	vmovdqu ymm13, YMMWORD PTR [rcx]
	vpxor ymm13, ymm0, ymm13
	vpxor ymm9, ymm5, ymm9
	vpand ymm9, ymm13, ymm9
	vpxor ymm11, ymm14, ymm11
	vpxor ymm11, ymm9, ymm11
	vpandn ymm2, ymm2, ymm3
	vpxor ymm11, ymm2, ymm11
	vmovdqu ymm0, YMMWORD PTR [rcx+96]
	vmovdqa ymm1, ymm8
	vmovdqa ymm2, ymm7
	vmovdqa ymm3, ymm11
	vmovdqu ymm14, YMMWORD PTR [r13+1344]
	vpxor ymm0, ymm0, ymm14
	vmovdqu YMMWORD PTR [r13+1344], ymm0
	vmovdqu ymm14, YMMWORD PTR [r13+1408]
	vpxor ymm1, ymm1, ymm14
	vmovdqu YMMWORD PTR [r13+1408], ymm1
	vmovdqu ymm14, YMMWORD PTR [r13+768]
	vpxor ymm2, ymm2, ymm14
	vmovdqu YMMWORD PTR [r13+768], ymm2
	vmovdqu ymm14, YMMWORD PTR [r13+1216]
	vpxor ymm3, ymm3, ymm14
	vmovdqu YMMWORD PTR [r13+1216], ymm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm5, YMMWORD PTR [r12+64]
	vpxor ymm5, ymm5, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm4, YMMWORD PTR [r12+1792]
	vpxor ymm4, ymm4, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm3, YMMWORD PTR [r12+1536]
	vpxor ymm3, ymm3, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm2, YMMWORD PTR [r12+1280]
	vpxor ymm2, ymm2, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm1, YMMWORD PTR [r12+1024]
	vpxor ymm1, ymm1, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm0, YMMWORD PTR [r12+768]
	vpxor ymm0, ymm0, ymm14
	vpxor ymm6, ymm2, ymm1
	vpxor ymm7, ymm3, ymm6
	vpand ymm8, ymm0, ymm7
	vpand ymm9, ymm2, ymm6
	vpxor ymm10, ymm4, ymm9
	vpand ymm11, ymm8, ymm10
	vpand ymm12, ymm0, ymm9
	vpxor ymm13, ymm3, ymm12
	vpor ymm14, ymm10, ymm13
	vpxor ymm6, ymm0, ymm6
	vmovdqu YMMWORD PTR [rcx], ymm0
	vpxor ymm0, ymm14, ymm6
	vmovdqu YMMWORD PTR [rcx+32], ymm9
	vpandn ymm9, ymm11, ymm5
	vpxor ymm0, ymm9, ymm0
	vpandn ymm7, ymm7, ymm1
	vpor ymm9, ymm10, ymm7
	vpxor ymm13, ymm8, ymm13
	vpxor ymm9, ymm9, ymm13
	vpxor ymm6, ymm8, ymm6
	vpandn ymm2, ymm6, ymm2
	vpandn ymm8, ymm2, ymm10
	vpxor ymm13, ymm1, ymm13
	vpxor ymm13, ymm8, ymm13
	vpandn ymm12, ymm12, ymm6
	vpor ymm2, ymm2, ymm12
	vpxor ymm14, ymm4, ymm14
	vpand ymm14, ymm13, ymm14
	vpxor ymm14, ymm2, ymm14
	vpand ymm6, ymm14, ymm5
	vpxor ymm6, ymm6, ymm13
	vpandn ymm3, ymm3, ymm10
	vpor ymm3, ymm12, ymm3
	vmovdqu ymm12, YMMWORD PTR [rcx+32]
	vpor ymm13, ymm12, ymm13
	vpand ymm13, ymm3, ymm13
	vpxor ymm14, ymm14, ymm13
	vpxor ymm2, ymm7, ymm2
	vmovdqu ymm7, YMMWORD PTR [rcx]
	vpand ymm2, ymm7, ymm2
	vpor ymm2, ymm11, ymm2
	vpxor ymm13, ymm13, ymm2
	vpandn ymm11, ymm5, ymm13
	vpxor ymm11, ymm11, ymm9
	vpand ymm2, ymm4, ymm2
	vpxor ymm9, ymm9, ymm15
	vpxor ymm9, ymm2, ymm9
	vpxor ymm9, ymm13, ymm9
	vpor ymm5, ymm14, ymm5
	vpxor ymm9, ymm5, ymm9
	vmovdqa ymm1, ymm6
	vmovdqa ymm2, ymm9
	vmovdqa ymm3, ymm11
	vmovdqu ymm14, YMMWORD PTR [r13+448]
	vpxor ymm0, ymm0, ymm14
	vmovdqu YMMWORD PTR [r13+448], ymm0
	vmovdqu ymm14, YMMWORD PTR [r13+576]
	vpxor ymm1, ymm1, ymm14
	vmovdqu YMMWORD PTR [r13+576], ymm1
	vmovdqu ymm14, YMMWORD PTR [r13+1152]
	vpxor ymm2, ymm2, ymm14
	vmovdqu YMMWORD PTR [r13+1152], ymm2
	vmovdqu ymm14, YMMWORD PTR [r13]
	vpxor ymm3, ymm3, ymm14
	vmovdqu YMMWORD PTR [r13], ymm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm5, YMMWORD PTR [r12+1024]
	vpxor ymm5, ymm5, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm4, YMMWORD PTR [r12+768]
	vpxor ymm4, ymm4, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm3, YMMWORD PTR [r12+512]
	vpxor ymm3, ymm3, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm2, YMMWORD PTR [r12+256]
	vpxor ymm2, ymm2, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm1, YMMWORD PTR [r12]
	vpxor ymm1, ymm1, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm0, YMMWORD PTR [r12+1984]
	vpxor ymm0, ymm0, ymm14
	vpandn ymm6, ymm4, ymm3
	vpandn ymm7, ymm3, ymm1
	vpxor ymm7, ymm2, ymm7
	vpand ymm8, ymm5, ymm7
	vpandn ymm9, ymm6, ymm8
	vpandn ymm10, ymm7, ymm4
	vpor ymm11, ymm5, ymm10
	vpandn ymm12, ymm3, ymm4
	vpxor ymm12, ymm1, ymm12
	vpand ymm13, ymm11, ymm12
	vpor ymm8, ymm8, ymm13
	vpxor ymm7, ymm7, ymm15
	vpxor ymm7, ymm13, ymm7
	vpandn ymm11, ymm11, ymm3
	vpxor ymm11, ymm7, ymm11
	vpxor ymm6, ymm6, ymm11
	vpor ymm7, ymm9, ymm0
	vpxor ymm7, ymm7, ymm6
	vpxor ymm6, ymm5, ymm6
	vpand ymm3, ymm1, ymm6
	vpxor ymm11, ymm4, ymm11
	vpxor ymm3, ymm3, ymm11
	vpxor ymm10, ymm10, ymm3
	vpxor ymm3, ymm8, ymm3
	vpor ymm3, ymm4, ymm3
	vpxor ymm6, ymm1, ymm6
	vpxor ymm6, ymm3, ymm6
	vpand ymm8, ymm8, ymm0
	vpxor ymm8, ymm8, ymm6
	vpxor ymm12, ymm12, ymm10
	vpor ymm11, ymm2, ymm11
	vpxor ymm11, ymm12, ymm11
	vpxor ymm5, ymm5, ymm11
	vpand ymm5, ymm5, ymm0
	vpxor ymm5, ymm5, ymm10
	vpandn ymm2, ymm2, ymm12
	vpand ymm2, ymm6, ymm2
	vpxor ymm11, ymm9, ymm11
	vpxor ymm11, ymm2, ymm11
	vpor ymm0, ymm11, ymm0
	vpxor ymm10, ymm0, ymm10
	vmovdqa ymm0, ymm5
	vmovdqa ymm1, ymm8
	vmovdqa ymm2, ymm7
	vmovdqa ymm3, ymm10
	vmovdqu ymm14, YMMWORD PTR [r13+832]
	vpxor ymm0, ymm0, ymm14
	vmovdqu YMMWORD PTR [r13+832], ymm0
	vmovdqu ymm14, YMMWORD PTR [r13+384]
	vpxor ymm1, ymm1, ymm14
	vmovdqu YMMWORD PTR [r13+384], ymm1
	vmovdqu ymm14, YMMWORD PTR [r13+1280]
	vpxor ymm2, ymm2, ymm14
	vmovdqu YMMWORD PTR [r13+1280], ymm2
	vmovdqu ymm14, YMMWORD PTR [r13+960]
	vpxor ymm3, ymm3, ymm14
	vmovdqu YMMWORD PTR [r13+960], ymm3
	mov rbx, r12
	mov r12, r13
	mov r13, rbx
	sub r10, 1
	jne 210b
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vmovdqu YMMWORD PTR [rsi], ymm1
	vmovdqu YMMWORD PTR [rsi+32], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+256]
	vmovdqu ymm1, YMMWORD PTR [rsi+288]
	vmovdqu YMMWORD PTR [rsi+256], ymm1
	vmovdqu YMMWORD PTR [rsi+288], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+512]
	vmovdqu ymm1, YMMWORD PTR [rsi+544]
	vmovdqu YMMWORD PTR [rsi+512], ymm1
	vmovdqu YMMWORD PTR [rsi+544], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+768]
	vmovdqu ymm1, YMMWORD PTR [rsi+800]
	vmovdqu YMMWORD PTR [rsi+768], ymm1
	vmovdqu YMMWORD PTR [rsi+800], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1024]
	vmovdqu ymm1, YMMWORD PTR [rsi+1056]
	vmovdqu YMMWORD PTR [rsi+1024], ymm1
	vmovdqu YMMWORD PTR [rsi+1056], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1280]
	vmovdqu ymm1, YMMWORD PTR [rsi+1312]
	vmovdqu YMMWORD PTR [rsi+1280], ymm1
	vmovdqu YMMWORD PTR [rsi+1312], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1536]
	vmovdqu ymm1, YMMWORD PTR [rsi+1568]
	vmovdqu YMMWORD PTR [rsi+1536], ymm1
	vmovdqu YMMWORD PTR [rsi+1568], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1792]
	vmovdqu ymm1, YMMWORD PTR [rsi+1824]
	vmovdqu YMMWORD PTR [rsi+1792], ymm1
	vmovdqu YMMWORD PTR [rsi+1824], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+64]
	vmovdqu ymm1, YMMWORD PTR [rsi+96]
	vmovdqu YMMWORD PTR [rsi+64], ymm1
	vmovdqu YMMWORD PTR [rsi+96], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+320]
	vmovdqu ymm1, YMMWORD PTR [rsi+352]
	vmovdqu YMMWORD PTR [rsi+320], ymm1
	vmovdqu YMMWORD PTR [rsi+352], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+576]
	vmovdqu ymm1, YMMWORD PTR [rsi+608]
	vmovdqu YMMWORD PTR [rsi+576], ymm1
	vmovdqu YMMWORD PTR [rsi+608], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+832]
	vmovdqu ymm1, YMMWORD PTR [rsi+864]
	vmovdqu YMMWORD PTR [rsi+832], ymm1
	vmovdqu YMMWORD PTR [rsi+864], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1088]
	vmovdqu ymm1, YMMWORD PTR [rsi+1120]
	vmovdqu YMMWORD PTR [rsi+1088], ymm1
	vmovdqu YMMWORD PTR [rsi+1120], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1344]
	vmovdqu ymm1, YMMWORD PTR [rsi+1376]
	vmovdqu YMMWORD PTR [rsi+1344], ymm1
	vmovdqu YMMWORD PTR [rsi+1376], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1600]
	vmovdqu ymm1, YMMWORD PTR [rsi+1632]
	vmovdqu YMMWORD PTR [rsi+1600], ymm1
	vmovdqu YMMWORD PTR [rsi+1632], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1856]
	vmovdqu ymm1, YMMWORD PTR [rsi+1888]
	vmovdqu YMMWORD PTR [rsi+1856], ymm1
	vmovdqu YMMWORD PTR [rsi+1888], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+128]
	vmovdqu ymm1, YMMWORD PTR [rsi+160]
	vmovdqu YMMWORD PTR [rsi+128], ymm1
	vmovdqu YMMWORD PTR [rsi+160], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+384]
	vmovdqu ymm1, YMMWORD PTR [rsi+416]
	vmovdqu YMMWORD PTR [rsi+384], ymm1
	vmovdqu YMMWORD PTR [rsi+416], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+640]
	vmovdqu ymm1, YMMWORD PTR [rsi+672]
	vmovdqu YMMWORD PTR [rsi+640], ymm1
	vmovdqu YMMWORD PTR [rsi+672], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+896]
	vmovdqu ymm1, YMMWORD PTR [rsi+928]
	vmovdqu YMMWORD PTR [rsi+896], ymm1
	vmovdqu YMMWORD PTR [rsi+928], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1152]
	vmovdqu ymm1, YMMWORD PTR [rsi+1184]
	vmovdqu YMMWORD PTR [rsi+1152], ymm1
	vmovdqu YMMWORD PTR [rsi+1184], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1408]
	vmovdqu ymm1, YMMWORD PTR [rsi+1440]
	vmovdqu YMMWORD PTR [rsi+1408], ymm1
	vmovdqu YMMWORD PTR [rsi+1440], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1664]
	vmovdqu ymm1, YMMWORD PTR [rsi+1696]
	vmovdqu YMMWORD PTR [rsi+1664], ymm1
	vmovdqu YMMWORD PTR [rsi+1696], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1920]
	vmovdqu ymm1, YMMWORD PTR [rsi+1952]
	vmovdqu YMMWORD PTR [rsi+1920], ymm1
	vmovdqu YMMWORD PTR [rsi+1952], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+192]
	vmovdqu ymm1, YMMWORD PTR [rsi+224]
	vmovdqu YMMWORD PTR [rsi+192], ymm1
	vmovdqu YMMWORD PTR [rsi+224], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+448]
	vmovdqu ymm1, YMMWORD PTR [rsi+480]
	vmovdqu YMMWORD PTR [rsi+448], ymm1
	vmovdqu YMMWORD PTR [rsi+480], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+704]
	vmovdqu ymm1, YMMWORD PTR [rsi+736]
	vmovdqu YMMWORD PTR [rsi+704], ymm1
	vmovdqu YMMWORD PTR [rsi+736], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+960]
	vmovdqu ymm1, YMMWORD PTR [rsi+992]
	vmovdqu YMMWORD PTR [rsi+960], ymm1
	vmovdqu YMMWORD PTR [rsi+992], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1216]
	vmovdqu ymm1, YMMWORD PTR [rsi+1248]
	vmovdqu YMMWORD PTR [rsi+1216], ymm1
	vmovdqu YMMWORD PTR [rsi+1248], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1472]
	vmovdqu ymm1, YMMWORD PTR [rsi+1504]
	vmovdqu YMMWORD PTR [rsi+1472], ymm1
	vmovdqu YMMWORD PTR [rsi+1504], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1728]
	vmovdqu ymm1, YMMWORD PTR [rsi+1760]
	vmovdqu YMMWORD PTR [rsi+1728], ymm1
	vmovdqu YMMWORD PTR [rsi+1760], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1984]
	vmovdqu ymm1, YMMWORD PTR [rsi+2016]
	vmovdqu YMMWORD PTR [rsi+1984], ymm1
	vmovdqu YMMWORD PTR [rsi+2016], ymm0
	sub r11, 1
	jne 25b
	mov r11, 8
211:
	movabs rbx, 4294967295
	vmovq xmm13, rbx
	vpbroadcastq ymm13, xmm13
	movabs rbx, 281470681808895
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	movabs rbx, 71777214294589695
	vmovq xmm15, rbx
	vpbroadcastq ymm15, xmm15
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vmovdqu ymm1, YMMWORD PTR [rsi+256]
	vmovdqu ymm2, YMMWORD PTR [rsi+512]
	vmovdqu ymm3, YMMWORD PTR [rsi+768]
	vmovdqu ymm4, YMMWORD PTR [rsi+1024]
	vmovdqu ymm5, YMMWORD PTR [rsi+1280]
	vmovdqu ymm6, YMMWORD PTR [rsi+1536]
	vmovdqu ymm7, YMMWORD PTR [rsi+1792]
	vpsrlq ymm8, ymm0, 32
	vpxor ymm8, ymm8, ymm4
	vpand ymm8, ymm8, ymm13
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm8, ymm8, 32
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm1, 32
	vpxor ymm8, ymm8, ymm5
	vpand ymm8, ymm8, ymm13
	vpxor ymm5, ymm5, ymm8
	vpsllq ymm8, ymm8, 32
	vpxor ymm1, ymm1, ymm8
	vpsrlq ymm8, ymm2, 32
	vpxor ymm8, ymm8, ymm6
	vpand ymm8, ymm8, ymm13
	vpxor ymm6, ymm6, ymm8
	vpsllq ymm8, ymm8, 32
	vpxor ymm2, ymm2, ymm8
	vpsrlq ymm8, ymm3, 32
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm13
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 32
	vpxor ymm3, ymm3, ymm8
	vpsrlq ymm8, ymm0, 16
	vpxor ymm8, ymm8, ymm2
	vpand ymm8, ymm8, ymm14
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm8, ymm8, 16
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm1, 16
	vpxor ymm8, ymm8, ymm3
	vpand ymm8, ymm8, ymm14
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm8, ymm8, 16
	vpxor ymm1, ymm1, ymm8
	vpsrlq ymm8, ymm4, 16
	vpxor ymm8, ymm8, ymm6
	vpand ymm8, ymm8, ymm14
	vpxor ymm6, ymm6, ymm8
	vpsllq ymm8, ymm8, 16
	vpxor ymm4, ymm4, ymm8
	vpsrlq ymm8, ymm5, 16
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm14
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 16
	vpxor ymm5, ymm5, ymm8
	vpsrlq ymm8, ymm0, 8
	vpxor ymm8, ymm8, ymm1
	vpand ymm8, ymm8, ymm15
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm8, ymm8, 8
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm2, 8
	vpxor ymm8, ymm8, ymm3
	vpand ymm8, ymm8, ymm15
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm8, ymm8, 8
	vpxor ymm2, ymm2, ymm8
	vpsrlq ymm8, ymm4, 8
	vpxor ymm8, ymm8, ymm5
	vpand ymm8, ymm8, ymm15
	vpxor ymm5, ymm5, ymm8
	vpsllq ymm8, ymm8, 8
	vpxor ymm4, ymm4, ymm8
	vpsrlq ymm8, ymm6, 8
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm15
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 8
	vpxor ymm6, ymm6, ymm8
	vmovdqu YMMWORD PTR [rsi], ymm0
	vmovdqu YMMWORD PTR [rsi+256], ymm1
	vmovdqu YMMWORD PTR [rsi+512], ymm2
	vmovdqu YMMWORD PTR [rsi+768], ymm3
	vmovdqu YMMWORD PTR [rsi+1024], ymm4
	vmovdqu YMMWORD PTR [rsi+1280], ymm5
	vmovdqu YMMWORD PTR [rsi+1536], ymm6
	vmovdqu YMMWORD PTR [rsi+1792], ymm7
	add rsi, 32
	sub r11, 1
	jne 211b
	sub rsi, 256
	mov r11, 8
212:
	movabs rbx, 1085102592571150095
	vmovq xmm13, rbx
	vpbroadcastq ymm13, xmm13
	movabs rbx, 3689348814741910323
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	movabs rbx, 6148914691236517205
	vmovq xmm15, rbx
	vpbroadcastq ymm15, xmm15
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vmovdqu ymm2, YMMWORD PTR [rsi+64]
	vmovdqu ymm3, YMMWORD PTR [rsi+96]
	vmovdqu ymm4, YMMWORD PTR [rsi+128]
	vmovdqu ymm5, YMMWORD PTR [rsi+160]
	vmovdqu ymm6, YMMWORD PTR [rsi+192]
	vmovdqu ymm7, YMMWORD PTR [rsi+224]
	vpsrlq ymm8, ymm0, 4
	vpxor ymm8, ymm8, ymm4
	vpand ymm8, ymm8, ymm13
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm8, ymm8, 4
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm1, 4
	vpxor ymm8, ymm8, ymm5
	vpand ymm8, ymm8, ymm13
	vpxor ymm5, ymm5, ymm8
	vpsllq ymm8, ymm8, 4
	vpxor ymm1, ymm1, ymm8
	vpsrlq ymm8, ymm2, 4
	vpxor ymm8, ymm8, ymm6
	vpand ymm8, ymm8, ymm13
	vpxor ymm6, ymm6, ymm8
	vpsllq ymm8, ymm8, 4
	vpxor ymm2, ymm2, ymm8
	vpsrlq ymm8, ymm3, 4
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm13
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 4
	vpxor ymm3, ymm3, ymm8
	vpsrlq ymm8, ymm0, 2
	vpxor ymm8, ymm8, ymm2
	vpand ymm8, ymm8, ymm14
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm8, ymm8, 2
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm1, 2
	vpxor ymm8, ymm8, ymm3
	vpand ymm8, ymm8, ymm14
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm8, ymm8, 2
	vpxor ymm1, ymm1, ymm8
	vpsrlq ymm8, ymm4, 2
	vpxor ymm8, ymm8, ymm6
	vpand ymm8, ymm8, ymm14
	vpxor ymm6, ymm6, ymm8
	vpsllq ymm8, ymm8, 2
	vpxor ymm4, ymm4, ymm8
	vpsrlq ymm8, ymm5, 2
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm14
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 2
	vpxor ymm5, ymm5, ymm8
	vpsrlq ymm8, ymm0, 1
	vpxor ymm8, ymm8, ymm1
	vpand ymm8, ymm8, ymm15
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm8, ymm8, 1
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm2, 1
	vpxor ymm8, ymm8, ymm3
	vpand ymm8, ymm8, ymm15
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm8, ymm8, 1
	vpxor ymm2, ymm2, ymm8
	vpsrlq ymm8, ymm4, 1
	vpxor ymm8, ymm8, ymm5
	vpand ymm8, ymm8, ymm15
	vpxor ymm5, ymm5, ymm8
	vpsllq ymm8, ymm8, 1
	vpxor ymm4, ymm4, ymm8
	vpsrlq ymm8, ymm6, 1
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm15
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 1
	vpxor ymm6, ymm6, ymm8
	vmovdqu YMMWORD PTR [rsi], ymm0
	vmovdqu YMMWORD PTR [rsi+32], ymm1
	vmovdqu YMMWORD PTR [rsi+64], ymm2
	vmovdqu YMMWORD PTR [rsi+96], ymm3
	vmovdqu YMMWORD PTR [rsi+128], ymm4
	vmovdqu YMMWORD PTR [rsi+160], ymm5
	vmovdqu YMMWORD PTR [rsi+192], ymm6
	vmovdqu YMMWORD PTR [rsi+224], ymm7
	add rsi, 256
	sub r11, 1
	jne 212b
	sub rsi, 2048
	add rsi, 2048
	sub rdx, 256
	cmp rdx, 256
	jae 22b
	mov rbx, QWORD PTR [rcx+1016]
	mov r12, QWORD PTR [rcx+1008]
	mov r13, QWORD PTR [rcx+1000]
	vzeroupper
	jmp 21f
20:
21:
	call {vg_triple_des_ecb_decrypt_core}
	mov r11d, 0
	mov QWORD PTR [rsp+8], r11
	mov QWORD PTR [rsp+16], r11
	mov QWORD PTR [rsp+24], r11
	mov QWORD PTR [rsp+32], r11
	mov QWORD PTR [rsp+40], r11
	mov QWORD PTR [rsp+48], r11
	mov QWORD PTR [rsp+56], r11
	mov QWORD PTR [rsp+64], r11
	mov QWORD PTR [rsp+72], r11
	mov QWORD PTR [rsp+80], r11
	mov QWORD PTR [rsp+88], r11
	mov QWORD PTR [rsp+96], r11
	mov QWORD PTR [rsp+104], r11
	mov QWORD PTR [rsp+112], r11
	mov QWORD PTR [rsp+120], r11
	mov QWORD PTR [rsp+128], r11
	mov QWORD PTR [rsp+136], r11
	mov QWORD PTR [rsp+144], r11
	mov QWORD PTR [rsp+152], r11
	mov QWORD PTR [rsp+160], r11
	mov QWORD PTR [rsp+168], r11
	mov QWORD PTR [rsp+176], r11
	mov QWORD PTR [rsp+184], r11
	mov QWORD PTR [rsp+192], r11
	mov QWORD PTR [rsp+200], r11
	mov QWORD PTR [rsp+208], r11
	mov QWORD PTR [rsp+216], r11
	mov QWORD PTR [rsp+224], r11
	mov QWORD PTR [rsp+232], r11
	mov QWORD PTR [rsp+240], r11
	mov QWORD PTR [rsp+248], r11
	mov QWORD PTR [rsp+256], r11
	mov QWORD PTR [rsp+264], r11
	mov QWORD PTR [rsp+272], r11
	mov QWORD PTR [rsp+280], r11
	mov QWORD PTR [rsp+288], r11
	mov QWORD PTR [rsp+296], r11
	mov QWORD PTR [rsp+304], r11
	mov QWORD PTR [rsp+312], r11
	mov QWORD PTR [rsp+320], r11
	mov QWORD PTR [rsp+328], r11
	mov QWORD PTR [rsp+336], r11
	mov QWORD PTR [rsp+344], r11
	mov QWORD PTR [rsp+352], r11
	mov QWORD PTR [rsp+360], r11
	mov QWORD PTR [rsp+368], r11
	mov QWORD PTR [rsp+376], r11
	mov QWORD PTR [rsp+384], r11
	mov QWORD PTR [rsp+392], r11
	mov QWORD PTR [rsp+400], r11
	mov QWORD PTR [rsp+408], r11
	mov QWORD PTR [rsp+416], r11
	mov QWORD PTR [rsp+424], r11
	mov QWORD PTR [rsp+432], r11
	mov QWORD PTR [rsp+440], r11
	mov QWORD PTR [rsp+448], r11
	mov QWORD PTR [rsp+456], r11
	mov QWORD PTR [rsp+464], r11
	mov QWORD PTR [rsp+472], r11
	mov QWORD PTR [rsp+480], r11
	mov QWORD PTR [rsp+488], r11
	mov QWORD PTR [rsp+496], r11
	mov QWORD PTR [rsp+504], r11
	mov QWORD PTR [rsp+512], r11
	mov QWORD PTR [rsp+520], r11
	mov QWORD PTR [rsp+528], r11
	mov QWORD PTR [rsp+536], r11
	mov QWORD PTR [rsp+544], r11
	mov QWORD PTR [rsp+552], r11
	mov QWORD PTR [rsp+560], r11
	mov QWORD PTR [rsp+568], r11
	mov QWORD PTR [rsp+576], r11
	mov QWORD PTR [rsp+584], r11
	mov QWORD PTR [rsp+592], r11
	mov QWORD PTR [rsp+600], r11
	mov QWORD PTR [rsp+608], r11
	mov QWORD PTR [rsp+616], r11
	mov QWORD PTR [rsp+624], r11
	mov QWORD PTR [rsp+632], r11
	mov QWORD PTR [rsp+640], r11
	mov QWORD PTR [rsp+648], r11
	mov QWORD PTR [rsp+656], r11
	mov QWORD PTR [rsp+664], r11
	mov QWORD PTR [rsp+672], r11
	mov QWORD PTR [rsp+680], r11
	mov QWORD PTR [rsp+688], r11
	mov QWORD PTR [rsp+696], r11
	mov QWORD PTR [rsp+704], r11
	mov QWORD PTR [rsp+712], r11
	mov QWORD PTR [rsp+720], r11
	mov QWORD PTR [rsp+728], r11
	mov QWORD PTR [rsp+736], r11
	mov QWORD PTR [rsp+744], r11
	mov QWORD PTR [rsp+752], r11
	mov QWORD PTR [rsp+760], r11
	mov QWORD PTR [rsp+768], r11
	mov QWORD PTR [rsp+776], r11
	mov QWORD PTR [rsp+784], r11
	mov QWORD PTR [rsp+792], r11
	mov QWORD PTR [rsp+800], r11
	mov QWORD PTR [rsp+808], r11
	mov QWORD PTR [rsp+816], r11
	mov QWORD PTR [rsp+824], r11
	mov QWORD PTR [rsp+832], r11
	mov QWORD PTR [rsp+840], r11
	mov QWORD PTR [rsp+848], r11
	mov QWORD PTR [rsp+856], r11
	mov QWORD PTR [rsp+864], r11
	mov QWORD PTR [rsp+872], r11
	mov QWORD PTR [rsp+880], r11
	mov QWORD PTR [rsp+888], r11
	mov QWORD PTR [rsp+896], r11
	mov QWORD PTR [rsp+904], r11
	mov QWORD PTR [rsp+912], r11
	mov QWORD PTR [rsp+920], r11
	mov QWORD PTR [rsp+928], r11
	mov QWORD PTR [rsp+936], r11
	mov QWORD PTR [rsp+944], r11
	mov QWORD PTR [rsp+952], r11
	mov QWORD PTR [rsp+960], r11
	mov QWORD PTR [rsp+968], r11
	mov QWORD PTR [rsp+976], r11
	mov QWORD PTR [rsp+984], r11
	mov QWORD PTR [rsp+992], r11
	mov QWORD PTR [rsp+1000], r11
	mov QWORD PTR [rsp+1008], r11
	mov QWORD PTR [rsp+1016], r11
	mov QWORD PTR [rsp+1024], r11
	lea rsp, [rsp+1032]
	ret
	.p2align 6

vg_triple_des_ecb_encrypt_avx512:
	lea rsp, [rsp-1032]
	mov rcx, rsp
	add rcx, 8
	cmp rdx, 512
	jb 20f
	mov QWORD PTR [rcx+1016], rbx
	mov QWORD PTR [rcx+1008], r12
	mov QWORD PTR [rcx+1000], r13
22:
	mov r11, 8
23:
	movabs rbx, 4294967295
	vmovq xmm13, rbx
	vpbroadcastq zmm13, xmm13
	movabs rbx, 281470681808895
	vmovq xmm14, rbx
	vpbroadcastq zmm14, xmm14
	movabs rbx, 71777214294589695
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm0, ZMMWORD PTR [rsi]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+512]
	vmovdqu32 zmm2, ZMMWORD PTR [rsi+1024]
	vmovdqu32 zmm3, ZMMWORD PTR [rsi+1536]
	vmovdqu32 zmm4, ZMMWORD PTR [rsi+2048]
	vmovdqu32 zmm5, ZMMWORD PTR [rsi+2560]
	vmovdqu32 zmm6, ZMMWORD PTR [rsi+3072]
	vmovdqu32 zmm7, ZMMWORD PTR [rsi+3584]
	vpsrlq zmm8, zmm0, 32
	vpxord zmm8, zmm8, zmm4
	vpandq zmm8, zmm8, zmm13
	vpxord zmm4, zmm4, zmm8
	vpsllq zmm8, zmm8, 32
	vpxord zmm0, zmm0, zmm8
	vpsrlq zmm8, zmm1, 32
	vpxord zmm8, zmm8, zmm5
	vpandq zmm8, zmm8, zmm13
	vpxord zmm5, zmm5, zmm8
	vpsllq zmm8, zmm8, 32
	vpxord zmm1, zmm1, zmm8
	vpsrlq zmm8, zmm2, 32
	vpxord zmm8, zmm8, zmm6
	vpandq zmm8, zmm8, zmm13
	vpxord zmm6, zmm6, zmm8
	vpsllq zmm8, zmm8, 32
	vpxord zmm2, zmm2, zmm8
	vpsrlq zmm8, zmm3, 32
	vpxord zmm8, zmm8, zmm7
	vpandq zmm8, zmm8, zmm13
	vpxord zmm7, zmm7, zmm8
	vpsllq zmm8, zmm8, 32
	vpxord zmm3, zmm3, zmm8
	vpsrlq zmm8, zmm0, 16
	vpxord zmm8, zmm8, zmm2
	vpandq zmm8, zmm8, zmm14
	vpxord zmm2, zmm2, zmm8
	vpsllq zmm8, zmm8, 16
	vpxord zmm0, zmm0, zmm8
	vpsrlq zmm8, zmm1, 16
	vpxord zmm8, zmm8, zmm3
	vpandq zmm8, zmm8, zmm14
	vpxord zmm3, zmm3, zmm8
	vpsllq zmm8, zmm8, 16
	vpxord zmm1, zmm1, zmm8
	vpsrlq zmm8, zmm4, 16
	vpxord zmm8, zmm8, zmm6
	vpandq zmm8, zmm8, zmm14
	vpxord zmm6, zmm6, zmm8
	vpsllq zmm8, zmm8, 16
	vpxord zmm4, zmm4, zmm8
	vpsrlq zmm8, zmm5, 16
	vpxord zmm8, zmm8, zmm7
	vpandq zmm8, zmm8, zmm14
	vpxord zmm7, zmm7, zmm8
	vpsllq zmm8, zmm8, 16
	vpxord zmm5, zmm5, zmm8
	vpsrlq zmm8, zmm0, 8
	vpxord zmm8, zmm8, zmm1
	vpandq zmm8, zmm8, zmm15
	vpxord zmm1, zmm1, zmm8
	vpsllq zmm8, zmm8, 8
	vpxord zmm0, zmm0, zmm8
	vpsrlq zmm8, zmm2, 8
	vpxord zmm8, zmm8, zmm3
	vpandq zmm8, zmm8, zmm15
	vpxord zmm3, zmm3, zmm8
	vpsllq zmm8, zmm8, 8
	vpxord zmm2, zmm2, zmm8
	vpsrlq zmm8, zmm4, 8
	vpxord zmm8, zmm8, zmm5
	vpandq zmm8, zmm8, zmm15
	vpxord zmm5, zmm5, zmm8
	vpsllq zmm8, zmm8, 8
	vpxord zmm4, zmm4, zmm8
	vpsrlq zmm8, zmm6, 8
	vpxord zmm8, zmm8, zmm7
	vpandq zmm8, zmm8, zmm15
	vpxord zmm7, zmm7, zmm8
	vpsllq zmm8, zmm8, 8
	vpxord zmm6, zmm6, zmm8
	vmovdqu32 ZMMWORD PTR [rsi], zmm0
	vmovdqu32 ZMMWORD PTR [rsi+512], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+1024], zmm2
	vmovdqu32 ZMMWORD PTR [rsi+1536], zmm3
	vmovdqu32 ZMMWORD PTR [rsi+2048], zmm4
	vmovdqu32 ZMMWORD PTR [rsi+2560], zmm5
	vmovdqu32 ZMMWORD PTR [rsi+3072], zmm6
	vmovdqu32 ZMMWORD PTR [rsi+3584], zmm7
	add rsi, 64
	sub r11, 1
	jne 23b
	sub rsi, 512
	mov r11, 8
24:
	movabs rbx, 1085102592571150095
	vmovq xmm13, rbx
	vpbroadcastq zmm13, xmm13
	movabs rbx, 3689348814741910323
	vmovq xmm14, rbx
	vpbroadcastq zmm14, xmm14
	movabs rbx, 6148914691236517205
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm0, ZMMWORD PTR [rsi]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+64]
	vmovdqu32 zmm2, ZMMWORD PTR [rsi+128]
	vmovdqu32 zmm3, ZMMWORD PTR [rsi+192]
	vmovdqu32 zmm4, ZMMWORD PTR [rsi+256]
	vmovdqu32 zmm5, ZMMWORD PTR [rsi+320]
	vmovdqu32 zmm6, ZMMWORD PTR [rsi+384]
	vmovdqu32 zmm7, ZMMWORD PTR [rsi+448]
	vpsrlq zmm8, zmm0, 4
	vpxord zmm8, zmm8, zmm4
	vpandq zmm8, zmm8, zmm13
	vpxord zmm4, zmm4, zmm8
	vpsllq zmm8, zmm8, 4
	vpxord zmm0, zmm0, zmm8
	vpsrlq zmm8, zmm1, 4
	vpxord zmm8, zmm8, zmm5
	vpandq zmm8, zmm8, zmm13
	vpxord zmm5, zmm5, zmm8
	vpsllq zmm8, zmm8, 4
	vpxord zmm1, zmm1, zmm8
	vpsrlq zmm8, zmm2, 4
	vpxord zmm8, zmm8, zmm6
	vpandq zmm8, zmm8, zmm13
	vpxord zmm6, zmm6, zmm8
	vpsllq zmm8, zmm8, 4
	vpxord zmm2, zmm2, zmm8
	vpsrlq zmm8, zmm3, 4
	vpxord zmm8, zmm8, zmm7
	vpandq zmm8, zmm8, zmm13
	vpxord zmm7, zmm7, zmm8
	vpsllq zmm8, zmm8, 4
	vpxord zmm3, zmm3, zmm8
	vpsrlq zmm8, zmm0, 2
	vpxord zmm8, zmm8, zmm2
	vpandq zmm8, zmm8, zmm14
	vpxord zmm2, zmm2, zmm8
	vpsllq zmm8, zmm8, 2
	vpxord zmm0, zmm0, zmm8
	vpsrlq zmm8, zmm1, 2
	vpxord zmm8, zmm8, zmm3
	vpandq zmm8, zmm8, zmm14
	vpxord zmm3, zmm3, zmm8
	vpsllq zmm8, zmm8, 2
	vpxord zmm1, zmm1, zmm8
	vpsrlq zmm8, zmm4, 2
	vpxord zmm8, zmm8, zmm6
	vpandq zmm8, zmm8, zmm14
	vpxord zmm6, zmm6, zmm8
	vpsllq zmm8, zmm8, 2
	vpxord zmm4, zmm4, zmm8
	vpsrlq zmm8, zmm5, 2
	vpxord zmm8, zmm8, zmm7
	vpandq zmm8, zmm8, zmm14
	vpxord zmm7, zmm7, zmm8
	vpsllq zmm8, zmm8, 2
	vpxord zmm5, zmm5, zmm8
	vpsrlq zmm8, zmm0, 1
	vpxord zmm8, zmm8, zmm1
	vpandq zmm8, zmm8, zmm15
	vpxord zmm1, zmm1, zmm8
	vpsllq zmm8, zmm8, 1
	vpxord zmm0, zmm0, zmm8
	vpsrlq zmm8, zmm2, 1
	vpxord zmm8, zmm8, zmm3
	vpandq zmm8, zmm8, zmm15
	vpxord zmm3, zmm3, zmm8
	vpsllq zmm8, zmm8, 1
	vpxord zmm2, zmm2, zmm8
	vpsrlq zmm8, zmm4, 1
	vpxord zmm8, zmm8, zmm5
	vpandq zmm8, zmm8, zmm15
	vpxord zmm5, zmm5, zmm8
	vpsllq zmm8, zmm8, 1
	vpxord zmm4, zmm4, zmm8
	vpsrlq zmm8, zmm6, 1
	vpxord zmm8, zmm8, zmm7
	vpandq zmm8, zmm8, zmm15
	vpxord zmm7, zmm7, zmm8
	vpsllq zmm8, zmm8, 1
	vpxord zmm6, zmm6, zmm8
	vmovdqu32 ZMMWORD PTR [rsi], zmm0
	vmovdqu32 ZMMWORD PTR [rsi+64], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+128], zmm2
	vmovdqu32 ZMMWORD PTR [rsi+192], zmm3
	vmovdqu32 ZMMWORD PTR [rsi+256], zmm4
	vmovdqu32 ZMMWORD PTR [rsi+320], zmm5
	vmovdqu32 ZMMWORD PTR [rsi+384], zmm6
	vmovdqu32 ZMMWORD PTR [rsi+448], zmm7
	add rsi, 512
	sub r11, 1
	jne 24b
	sub rsi, 4096
	mov r11, 3
25:
	cmp r11, 3
	je 26f
	cmp r11, 2
	je 28f
	mov r8, rdi
	add r8, 256
	mov r9, 8
	jmp 29f
28:
	mov r8, rdi
	add r8, 248
	mov r9, -8
29:
	jmp 27f
26:
	mov r8, rdi
	add r8, 0
	mov r9, 8
27:
	mov r10, 16
	mov r12, rsi
	add r12, 64
	mov r13, rsi
210:
	mov rax, QWORD PTR [r8]
	add r8, r9
	ror rax, 48
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm5, ZMMWORD PTR [r12]
	vpxord zmm5, zmm5, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm4, ZMMWORD PTR [r12+3968]
	vpxord zmm4, zmm4, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm3, ZMMWORD PTR [r12+3456]
	vpxord zmm3, zmm3, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm2, ZMMWORD PTR [r12+2944]
	vpxord zmm2, zmm2, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm1, ZMMWORD PTR [r12+2432]
	vpxord zmm1, zmm1, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm0, ZMMWORD PTR [r12+1920]
	vpxord zmm0, zmm0, zmm15
	vpandnq zmm6, zmm1, zmm5
	vpxord zmm7, zmm2, zmm6
	vporq zmm8, zmm3, zmm0
	vpxord zmm9, zmm5, zmm3
	vpandq zmm10, zmm8, zmm9
	vpxord zmm11, zmm2, zmm10
	vpandnq zmm12, zmm7, zmm11
	vpxord zmm13, zmm1, zmm0
	vmovdqa64 zmm14, zmm7
	vpternlogd zmm14, zmm3, zmm13, 144
	vpternlogd zmm14, zmm0, zmm10, 30
	vpandnq zmm10, zmm12, zmm14
	vporq zmm0, zmm5, zmm0
	vporq zmm15, zmm14, zmm0
	vpandnq zmm11, zmm11, zmm1
	vpternlogd zmm2, zmm11, zmm0, 156
	vpternlogd zmm2, zmm13, zmm9, 244
	vpandnq zmm6, zmm6, zmm3
	vpternlogd zmm6, zmm7, zmm15, 6
	vpternlogd zmm14, zmm6, zmm8, 147
	vmovdqa64 zmm3, zmm4
	vpternlogd zmm3, zmm15, zmm11, 6
	vpxord zmm3, zmm3, zmm14
	vpternlogd zmm11, zmm13, zmm6, 246
	vpternlogd zmm5, zmm8, zmm11, 150
	vpxord zmm14, zmm14, zmm5
	vpternlogd zmm12, zmm14, zmm4, 54
	vpternlogd zmm8, zmm2, zmm15, 222
	vpxord zmm8, zmm5, zmm8
	vpternlogd zmm13, zmm8, zmm14, 54
	vpternlogd zmm13, zmm10, zmm4, 30
	vpternlogd zmm8, zmm1, zmm7, 14
	vpternlogd zmm8, zmm10, zmm5, 120
	vpternlogd zmm2, zmm8, zmm4, 30
	vmovdqa64 zmm0, zmm2
	vmovdqa64 zmm1, zmm3
	vmovdqa64 zmm2, zmm13
	vmovdqa64 zmm3, zmm12
	vmovdqu32 zmm15, ZMMWORD PTR [r13+512]
	vpxord zmm0, zmm0, zmm15
	vmovdqu32 ZMMWORD PTR [r13+512], zmm0
	vmovdqu32 zmm15, ZMMWORD PTR [r13+640]
	vpxord zmm1, zmm1, zmm15
	vmovdqu32 ZMMWORD PTR [r13+640], zmm1
	vmovdqu32 zmm15, ZMMWORD PTR [r13+3712]
	vpxord zmm2, zmm2, zmm15
	vmovdqu32 ZMMWORD PTR [r13+3712], zmm2
	vmovdqu32 zmm15, ZMMWORD PTR [r13+3840]
	vpxord zmm3, zmm3, zmm15
	vmovdqu32 ZMMWORD PTR [r13+3840], zmm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm5, ZMMWORD PTR [r12+2432]
	vpxord zmm5, zmm5, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm4, ZMMWORD PTR [r12+1920]
	vpxord zmm4, zmm4, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm3, ZMMWORD PTR [r12+1408]
	vpxord zmm3, zmm3, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm2, ZMMWORD PTR [r12+896]
	vpxord zmm2, zmm2, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm1, ZMMWORD PTR [r12+384]
	vpxord zmm1, zmm1, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm0, ZMMWORD PTR [r12+3840]
	vpxord zmm0, zmm0, zmm15
	vpxord zmm6, zmm4, zmm1
	vmovdqa64 zmm7, zmm1
	vpternlogd zmm7, zmm5, zmm0, 176
	vporq zmm8, zmm4, zmm7
	vpandnq zmm9, zmm0, zmm6
	vpternlogd zmm1, zmm5, zmm6, 120
	vpandq zmm10, zmm3, zmm0
	vpternlogd zmm7, zmm8, zmm9, 72
	vpandq zmm11, zmm3, zmm7
	vpternlogd zmm5, zmm11, zmm11, 195
	vpxord zmm0, zmm0, zmm6
	vpandnq zmm12, zmm10, zmm0
	vpxord zmm13, zmm5, zmm12
	vmovdqa64 zmm14, zmm2
	vpternlogd zmm14, zmm7, zmm10, 176
	vpxord zmm14, zmm14, zmm13
	vpandnq zmm12, zmm12, zmm4
	vpxord zmm4, zmm1, zmm12
	vpxord zmm3, zmm3, zmm0
	vpternlogd zmm5, zmm3, zmm4, 156
	vmovdqa64 zmm15, zmm5
	vpternlogd zmm15, zmm8, zmm2, 180
	vpternlogd zmm3, zmm11, zmm12, 246
	vpxord zmm8, zmm8, zmm13
	vporq zmm10, zmm10, zmm8
	vpxord zmm12, zmm3, zmm10
	vpternlogd zmm5, zmm7, zmm13, 150
	vpandq zmm3, zmm6, zmm3
	vpternlogd zmm3, zmm10, zmm5, 120
	vpternlogd zmm12, zmm3, zmm2, 30
	vporq zmm8, zmm0, zmm8
	vpternlogd zmm8, zmm3, zmm4, 180
	vpternlogd zmm2, zmm1, zmm9, 244
	vpxord zmm8, zmm2, zmm8
	vmovdqa64 zmm0, zmm8
	vmovdqa64 zmm1, zmm12
	vmovdqa64 zmm2, zmm14
	vmovdqa64 zmm3, zmm15
	vmovdqu32 zmm15, ZMMWORD PTR [r13+3200]
	vpxord zmm0, zmm0, zmm15
	vmovdqu32 ZMMWORD PTR [r13+3200], zmm0
	vmovdqu32 zmm15, ZMMWORD PTR [r13+3456]
	vpxord zmm1, zmm1, zmm15
	vmovdqu32 ZMMWORD PTR [r13+3456], zmm1
	vmovdqu32 zmm15, ZMMWORD PTR [r13+2048]
	vpxord zmm2, zmm2, zmm15
	vmovdqu32 ZMMWORD PTR [r13+2048], zmm2
	vmovdqu32 zmm15, ZMMWORD PTR [r13+1792]
	vpxord zmm3, zmm3, zmm15
	vmovdqu32 ZMMWORD PTR [r13+1792], zmm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm5, ZMMWORD PTR [r12+384]
	vpxord zmm5, zmm5, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm4, ZMMWORD PTR [r12+3840]
	vpxord zmm4, zmm4, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm3, ZMMWORD PTR [r12+3328]
	vpxord zmm3, zmm3, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm2, ZMMWORD PTR [r12+2816]
	vpxord zmm2, zmm2, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm1, ZMMWORD PTR [r12+2304]
	vpxord zmm1, zmm1, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm0, ZMMWORD PTR [r12+1792]
	vpxord zmm0, zmm0, zmm15
	vpandnq zmm6, zmm4, zmm5
	vpxord zmm7, zmm3, zmm0
	vporq zmm8, zmm6, zmm7
	vpxord zmm9, zmm2, zmm0
	vpandnq zmm10, zmm5, zmm9
	vpxord zmm11, zmm8, zmm10
	vpxord zmm12, zmm4, zmm7
	vpternlogd zmm8, zmm12, zmm0, 180
	vmovdqa64 zmm13, zmm2
	vpternlogd zmm13, zmm0, zmm11, 248
	vpternlogd zmm13, zmm12, zmm5, 108
	vmovdqa64 zmm14, zmm13
	vpternlogd zmm14, zmm11, zmm1, 180
	vpxord zmm15, zmm5, zmm2
	vmovdqu32 ZMMWORD PTR [rcx], zmm14
	vmovdqa64 zmm14, zmm3
	vpternlogd zmm14, zmm8, zmm15, 246
	vpternlogd zmm14, zmm7, zmm9, 112
	vporq zmm15, zmm10, zmm15
	vpandq zmm0, zmm2, zmm0
	vpandnq zmm10, zmm4, zmm0
	vpternlogd zmm10, zmm13, zmm15, 180
	vpandq zmm9, zmm8, zmm10
	vpternlogd zmm9, zmm12, zmm0, 14
	vpxord zmm9, zmm5, zmm9
	vpternlogd zmm14, zmm9, zmm1, 108
	vmovdqa64 zmm5, zmm11
	vpternlogd zmm5, zmm11, zmm11, 15
	vpternlogd zmm3, zmm4, zmm5, 254
	vpxord zmm3, zmm12, zmm3
	vpternlogd zmm11, zmm1, zmm8, 140
	vpternlogd zmm11, zmm15, zmm3, 150
	vpternlogd zmm13, zmm2, zmm5, 120
	vpxord zmm9, zmm6, zmm9
	vpternlogd zmm9, zmm3, zmm13, 30
	vpternlogd zmm9, zmm10, zmm1, 30
	vmovdqu32 zmm0, ZMMWORD PTR [rcx]
	vmovdqa64 zmm1, zmm9
	vmovdqa64 zmm2, zmm14
	vmovdqa64 zmm3, zmm11
	vmovdqu32 zmm15, ZMMWORD PTR [r13+1408]
	vpxord zmm0, zmm0, zmm15
	vmovdqu32 ZMMWORD PTR [r13+1408], zmm0
	vmovdqu32 zmm15, ZMMWORD PTR [r13+1024]
	vpxord zmm1, zmm1, zmm15
	vmovdqu32 ZMMWORD PTR [r13+1024], zmm1
	vmovdqu32 zmm15, ZMMWORD PTR [r13+256]
	vpxord zmm2, zmm2, zmm15
	vmovdqu32 ZMMWORD PTR [r13+256], zmm2
	vmovdqu32 zmm15, ZMMWORD PTR [r13+128]
	vpxord zmm3, zmm3, zmm15
	vmovdqu32 ZMMWORD PTR [r13+128], zmm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm5, ZMMWORD PTR [r12+2304]
	vpxord zmm5, zmm5, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm4, ZMMWORD PTR [r12+1792]
	vpxord zmm4, zmm4, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm3, ZMMWORD PTR [r12+1280]
	vpxord zmm3, zmm3, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm2, ZMMWORD PTR [r12+768]
	vpxord zmm2, zmm2, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm1, ZMMWORD PTR [r12+256]
	vpxord zmm1, zmm1, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm0, ZMMWORD PTR [r12+3712]
	vpxord zmm0, zmm0, zmm15
	vpxord zmm5, zmm5, zmm3
	vpxord zmm3, zmm3, zmm1
	vmovdqa64 zmm6, zmm1
	vpternlogd zmm6, zmm4, zmm2, 30
	vpandnq zmm6, zmm6, zmm3
	vpandnq zmm7, zmm4, zmm3
	vpxord zmm8, zmm2, zmm7
	vmovdqa64 zmm9, zmm6
	vpternlogd zmm9, zmm5, zmm8, 14
	vpxord zmm10, zmm4, zmm9
	vpandq zmm8, zmm8, zmm10
	vpxord zmm5, zmm5, zmm10
	vpternlogd zmm3, zmm5, zmm8, 140
	vpxord zmm3, zmm6, zmm3
	vpxord zmm2, zmm4, zmm2
	vpternlogd zmm5, zmm1, zmm7, 30
	vpternlogd zmm9, zmm5, zmm2, 180
	vmovdqa64 zmm7, zmm9
	vpternlogd zmm7, zmm0, zmm3, 180
	vpternlogd zmm9, zmm9, zmm9, 15
	vmovdqa64 zmm1, zmm9
	vpternlogd zmm1, zmm3, zmm0, 180
	vpternlogd zmm2, zmm3, zmm9, 6
	vpternlogd zmm5, zmm8, zmm2, 30
	vmovdqa64 zmm2, zmm5
	vpternlogd zmm2, zmm10, zmm0, 30
	vpternlogd zmm5, zmm0, zmm10, 120
	vmovdqa64 zmm0, zmm5
	vmovdqu32 ZMMWORD PTR [rcx], zmm1
	vmovdqa64 zmm1, zmm2
	vmovdqu32 zmm2, ZMMWORD PTR [rcx]
	vmovdqa64 zmm3, zmm7
	vmovdqu32 zmm15, ZMMWORD PTR [r13+3968]
	vpxord zmm0, zmm0, zmm15
	vmovdqu32 ZMMWORD PTR [r13+3968], zmm0
	vmovdqu32 zmm15, ZMMWORD PTR [r13+3328]
	vpxord zmm1, zmm1, zmm15
	vmovdqu32 ZMMWORD PTR [r13+3328], zmm1
	vmovdqu32 zmm15, ZMMWORD PTR [r13+2176]
	vpxord zmm2, zmm2, zmm15
	vmovdqu32 ZMMWORD PTR [r13+2176], zmm2
	vmovdqu32 zmm15, ZMMWORD PTR [r13+3072]
	vpxord zmm3, zmm3, zmm15
	vmovdqu32 ZMMWORD PTR [r13+3072], zmm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm5, ZMMWORD PTR [r12+256]
	vpxord zmm5, zmm5, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm4, ZMMWORD PTR [r12+3712]
	vpxord zmm4, zmm4, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm3, ZMMWORD PTR [r12+3200]
	vpxord zmm3, zmm3, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm2, ZMMWORD PTR [r12+2688]
	vpxord zmm2, zmm2, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm1, ZMMWORD PTR [r12+2176]
	vpxord zmm1, zmm1, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm0, ZMMWORD PTR [r12+1664]
	vpxord zmm0, zmm0, zmm15
	vporq zmm6, zmm5, zmm3
	vpandnq zmm7, zmm0, zmm6
	vpxord zmm8, zmm5, zmm7
	vpxord zmm9, zmm3, zmm8
	vporq zmm10, zmm2, zmm9
	vpternlogd zmm3, zmm7, zmm2, 180
	vporq zmm9, zmm5, zmm9
	vmovdqa64 zmm7, zmm9
	vpternlogd zmm7, zmm1, zmm3, 120
	vpxord zmm7, zmm2, zmm7
	vpxord zmm0, zmm0, zmm7
	vporq zmm11, zmm8, zmm0
	vpandq zmm12, zmm1, zmm11
	vpandq zmm13, zmm2, zmm9
	vpternlogd zmm13, zmm8, zmm12, 150
	vpandnq zmm11, zmm5, zmm11
	vpxord zmm1, zmm1, zmm10
	vmovdqa64 zmm14, zmm1
	vpternlogd zmm14, zmm3, zmm11, 111
	vpternlogd zmm7, zmm14, zmm4, 180
	vpternlogd zmm11, zmm13, zmm1, 222
	vpternlogd zmm11, zmm3, zmm12, 176
	vpternlogd zmm1, zmm0, zmm11, 120
	vpternlogd zmm9, zmm1, zmm3, 236
	vpternlogd zmm12, zmm4, zmm9, 72
	vpxord zmm13, zmm12, zmm13
	vpternlogd zmm5, zmm11, zmm6, 150
	vpternlogd zmm5, zmm2, zmm1, 120
	vpternlogd zmm11, zmm4, zmm10, 206
	vpxord zmm11, zmm11, zmm5
	vpternlogd zmm5, zmm10, zmm3, 6
	vpternlogd zmm5, zmm8, zmm1, 150
	vpternlogd zmm5, zmm10, zmm4, 120
	vmovdqa64 zmm0, zmm13
	vmovdqa64 zmm1, zmm7
	vmovdqa64 zmm2, zmm5
	vmovdqa64 zmm3, zmm11
	vmovdqu32 zmm15, ZMMWORD PTR [r13+2944]
	vpxord zmm0, zmm0, zmm15
	vmovdqu32 ZMMWORD PTR [r13+2944], zmm0
	vmovdqu32 zmm15, ZMMWORD PTR [r13+3584]
	vpxord zmm1, zmm1, zmm15
	vmovdqu32 ZMMWORD PTR [r13+3584], zmm1
	vmovdqu32 zmm15, ZMMWORD PTR [r13+1280]
	vpxord zmm2, zmm2, zmm15
	vmovdqu32 ZMMWORD PTR [r13+1280], zmm2
	vmovdqu32 zmm15, ZMMWORD PTR [r13+384]
	vpxord zmm3, zmm3, zmm15
	vmovdqu32 ZMMWORD PTR [r13+384], zmm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm5, ZMMWORD PTR [r12+2176]
	vpxord zmm5, zmm5, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm4, ZMMWORD PTR [r12+1664]
	vpxord zmm4, zmm4, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm3, ZMMWORD PTR [r12+1152]
	vpxord zmm3, zmm3, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm2, ZMMWORD PTR [r12+640]
	vpxord zmm2, zmm2, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm1, ZMMWORD PTR [r12+128]
	vpxord zmm1, zmm1, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm0, ZMMWORD PTR [r12+3584]
	vpxord zmm0, zmm0, zmm15
	vmovdqa64 zmm6, zmm5
	vpternlogd zmm6, zmm4, zmm0, 224
	vmovdqa64 zmm7, zmm6
	vpternlogd zmm7, zmm4, zmm1, 150
	vpxord zmm8, zmm0, zmm7
	vpandnq zmm9, zmm8, zmm1
	vpandq zmm8, zmm5, zmm8
	vpxord zmm10, zmm4, zmm8
	vpxord zmm11, zmm5, zmm3
	vporq zmm12, zmm10, zmm11
	vpxord zmm13, zmm7, zmm12
	vpandq zmm14, zmm3, zmm13
	vpandnq zmm15, zmm0, zmm14
	vporq zmm10, zmm9, zmm10
	vmovdqu32 ZMMWORD PTR [rcx], zmm8
	vpxord zmm8, zmm15, zmm10
	vmovdqu32 ZMMWORD PTR [rcx+64], zmm7
	vmovdqa64 zmm7, zmm13
	vpternlogd zmm7, zmm8, zmm2, 120
	vpxord zmm12, zmm4, zmm12
	vpternlogd zmm3, zmm0, zmm12, 180
	vmovdqu32 ZMMWORD PTR [rcx+128], zmm7
	vmovdqa64 zmm7, zmm3
	vpternlogd zmm7, zmm1, zmm14, 244
	vporq zmm11, zmm4, zmm11
	vporq zmm6, zmm6, zmm7
	vpternlogd zmm6, zmm8, zmm11, 150
	vpternlogd zmm10, zmm5, zmm13, 224
	vpxord zmm10, zmm3, zmm10
	vpandnq zmm15, zmm15, zmm10
	vpternlogd zmm15, zmm9, zmm2, 30
	vmovdqu32 zmm9, ZMMWORD PTR [rcx+64]
	vpternlogd zmm1, zmm9, zmm10, 144
	vpternlogd zmm12, zmm11, zmm11, 195
	vpternlogd zmm1, zmm2, zmm12, 18
	vpxord zmm6, zmm1, zmm6
	vpxord zmm3, zmm5, zmm3
	vmovdqu32 zmm5, ZMMWORD PTR [rcx]
	vpternlogd zmm3, zmm0, zmm5, 96
	vpternlogd zmm3, zmm14, zmm12, 150
	vpternlogd zmm3, zmm7, zmm2, 180
	vmovdqu32 zmm0, ZMMWORD PTR [rcx+128]
	vmovdqa64 zmm1, zmm15
	vmovdqa64 zmm2, zmm6
	vmovdqu32 zmm15, ZMMWORD PTR [r13+2688]
	vpxord zmm0, zmm0, zmm15
	vmovdqu32 ZMMWORD PTR [r13+2688], zmm0
	vmovdqu32 zmm15, ZMMWORD PTR [r13+2816]
	vpxord zmm1, zmm1, zmm15
	vmovdqu32 ZMMWORD PTR [r13+2816], zmm1
	vmovdqu32 zmm15, ZMMWORD PTR [r13+1536]
	vpxord zmm2, zmm2, zmm15
	vmovdqu32 ZMMWORD PTR [r13+1536], zmm2
	vmovdqu32 zmm15, ZMMWORD PTR [r13+2432]
	vpxord zmm3, zmm3, zmm15
	vmovdqu32 ZMMWORD PTR [r13+2432], zmm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm5, ZMMWORD PTR [r12+128]
	vpxord zmm5, zmm5, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm4, ZMMWORD PTR [r12+3584]
	vpxord zmm4, zmm4, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm3, ZMMWORD PTR [r12+3072]
	vpxord zmm3, zmm3, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm2, ZMMWORD PTR [r12+2560]
	vpxord zmm2, zmm2, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm1, ZMMWORD PTR [r12+2048]
	vpxord zmm1, zmm1, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm0, ZMMWORD PTR [r12+1536]
	vpxord zmm0, zmm0, zmm15
	vpxord zmm6, zmm2, zmm1
	vpxord zmm7, zmm3, zmm6
	vpandq zmm8, zmm0, zmm7
	vpandq zmm9, zmm2, zmm6
	vpxord zmm10, zmm4, zmm9
	vpandq zmm11, zmm8, zmm10
	vpandq zmm12, zmm0, zmm9
	vpxord zmm13, zmm3, zmm12
	vporq zmm14, zmm10, zmm13
	vpxord zmm6, zmm0, zmm6
	vpxord zmm15, zmm14, zmm6
	vpternlogd zmm15, zmm5, zmm11, 180
	vpandnq zmm7, zmm7, zmm1
	vpxord zmm13, zmm8, zmm13
	vmovdqu32 ZMMWORD PTR [rcx], zmm15
	vmovdqa64 zmm15, zmm13
	vpternlogd zmm15, zmm10, zmm7, 30
	vpxord zmm6, zmm8, zmm6
	vpandnq zmm2, zmm6, zmm2
	vpxord zmm13, zmm1, zmm13
	vpternlogd zmm13, zmm10, zmm2, 180
	vpandnq zmm12, zmm12, zmm6
	vporq zmm2, zmm2, zmm12
	vpternlogd zmm14, zmm13, zmm4, 72
	vpxord zmm14, zmm2, zmm14
	vmovdqa64 zmm6, zmm13
	vpternlogd zmm6, zmm14, zmm5, 120
	vpternlogd zmm12, zmm10, zmm3, 244
	vpternlogd zmm12, zmm9, zmm13, 224
	vpternlogd zmm0, zmm7, zmm2, 96
	vporq zmm0, zmm11, zmm0
	vpxord zmm11, zmm12, zmm0
	vmovdqa64 zmm2, zmm15
	vpternlogd zmm2, zmm11, zmm5, 180
	vpternlogd zmm15, zmm4, zmm0, 135
	vpternlogd zmm5, zmm14, zmm12, 246
	vpternlogd zmm5, zmm11, zmm15, 150
	vmovdqu32 zmm0, ZMMWORD PTR [rcx]
	vmovdqa64 zmm1, zmm6
	vmovdqu32 ZMMWORD PTR [rcx+64], zmm2
	vmovdqa64 zmm2, zmm5
	vmovdqu32 zmm3, ZMMWORD PTR [rcx+64]
	vmovdqu32 zmm15, ZMMWORD PTR [r13+896]
	vpxord zmm0, zmm0, zmm15
	vmovdqu32 ZMMWORD PTR [r13+896], zmm0
	vmovdqu32 zmm15, ZMMWORD PTR [r13+1152]
	vpxord zmm1, zmm1, zmm15
	vmovdqu32 ZMMWORD PTR [r13+1152], zmm1
	vmovdqu32 zmm15, ZMMWORD PTR [r13+2304]
	vpxord zmm2, zmm2, zmm15
	vmovdqu32 ZMMWORD PTR [r13+2304], zmm2
	vmovdqu32 zmm15, ZMMWORD PTR [r13]
	vpxord zmm3, zmm3, zmm15
	vmovdqu32 ZMMWORD PTR [r13], zmm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm5, ZMMWORD PTR [r12+2048]
	vpxord zmm5, zmm5, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm4, ZMMWORD PTR [r12+1536]
	vpxord zmm4, zmm4, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm3, ZMMWORD PTR [r12+1024]
	vpxord zmm3, zmm3, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm2, ZMMWORD PTR [r12+512]
	vpxord zmm2, zmm2, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm1, ZMMWORD PTR [r12]
	vpxord zmm1, zmm1, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm0, ZMMWORD PTR [r12+3968]
	vpxord zmm0, zmm0, zmm15
	vpandnq zmm6, zmm4, zmm3
	vmovdqa64 zmm7, zmm2
	vpternlogd zmm7, zmm1, zmm3, 180
	vpandq zmm8, zmm5, zmm7
	vpandnq zmm9, zmm6, zmm8
	vpandnq zmm10, zmm7, zmm4
	vporq zmm11, zmm5, zmm10
	vmovdqa64 zmm12, zmm1
	vpternlogd zmm12, zmm4, zmm3, 180
	vpandq zmm13, zmm11, zmm12
	vporq zmm8, zmm8, zmm13
	vpandnq zmm11, zmm11, zmm3
	vpternlogd zmm11, zmm13, zmm7, 105
	vpxord zmm6, zmm6, zmm11
	vmovdqa64 zmm7, zmm6
	vpternlogd zmm7, zmm9, zmm0, 30
	vpxord zmm6, zmm5, zmm6
	vpxord zmm11, zmm4, zmm11
	vmovdqa64 zmm13, zmm11
	vpternlogd zmm13, zmm1, zmm6, 120
	vpxord zmm10, zmm10, zmm13
	vpternlogd zmm4, zmm8, zmm13, 246
	vpternlogd zmm4, zmm1, zmm6, 150
	vpternlogd zmm8, zmm4, zmm0, 108
	vpxord zmm12, zmm12, zmm10
	vpternlogd zmm11, zmm12, zmm2, 54
	vpternlogd zmm5, zmm0, zmm11, 72
	vpxord zmm5, zmm5, zmm10
	vpternlogd zmm4, zmm12, zmm2, 64
	vpternlogd zmm4, zmm9, zmm11, 150
	vpternlogd zmm10, zmm4, zmm0, 30
	vmovdqa64 zmm0, zmm5
	vmovdqa64 zmm1, zmm8
	vmovdqa64 zmm2, zmm7
	vmovdqa64 zmm3, zmm10
	vmovdqu32 zmm15, ZMMWORD PTR [r13+1664]
	vpxord zmm0, zmm0, zmm15
	vmovdqu32 ZMMWORD PTR [r13+1664], zmm0
	vmovdqu32 zmm15, ZMMWORD PTR [r13+768]
	vpxord zmm1, zmm1, zmm15
	vmovdqu32 ZMMWORD PTR [r13+768], zmm1
	vmovdqu32 zmm15, ZMMWORD PTR [r13+2560]
	vpxord zmm2, zmm2, zmm15
	vmovdqu32 ZMMWORD PTR [r13+2560], zmm2
	vmovdqu32 zmm15, ZMMWORD PTR [r13+1920]
	vpxord zmm3, zmm3, zmm15
	vmovdqu32 ZMMWORD PTR [r13+1920], zmm3
	mov rbx, r12
	mov r12, r13
	mov r13, rbx
	sub r10, 1
	jne 210b
	vmovdqu32 zmm0, ZMMWORD PTR [rsi]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+64]
	vmovdqu32 ZMMWORD PTR [rsi], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+64], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+512]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+576]
	vmovdqu32 ZMMWORD PTR [rsi+512], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+576], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+1024]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+1088]
	vmovdqu32 ZMMWORD PTR [rsi+1024], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+1088], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+1536]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+1600]
	vmovdqu32 ZMMWORD PTR [rsi+1536], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+1600], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+2048]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+2112]
	vmovdqu32 ZMMWORD PTR [rsi+2048], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+2112], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+2560]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+2624]
	vmovdqu32 ZMMWORD PTR [rsi+2560], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+2624], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+3072]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+3136]
	vmovdqu32 ZMMWORD PTR [rsi+3072], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+3136], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+3584]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+3648]
	vmovdqu32 ZMMWORD PTR [rsi+3584], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+3648], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+128]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+192]
	vmovdqu32 ZMMWORD PTR [rsi+128], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+192], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+640]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+704]
	vmovdqu32 ZMMWORD PTR [rsi+640], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+704], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+1152]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+1216]
	vmovdqu32 ZMMWORD PTR [rsi+1152], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+1216], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+1664]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+1728]
	vmovdqu32 ZMMWORD PTR [rsi+1664], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+1728], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+2176]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+2240]
	vmovdqu32 ZMMWORD PTR [rsi+2176], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+2240], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+2688]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+2752]
	vmovdqu32 ZMMWORD PTR [rsi+2688], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+2752], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+3200]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+3264]
	vmovdqu32 ZMMWORD PTR [rsi+3200], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+3264], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+3712]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+3776]
	vmovdqu32 ZMMWORD PTR [rsi+3712], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+3776], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+256]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+320]
	vmovdqu32 ZMMWORD PTR [rsi+256], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+320], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+768]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+832]
	vmovdqu32 ZMMWORD PTR [rsi+768], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+832], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+1280]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+1344]
	vmovdqu32 ZMMWORD PTR [rsi+1280], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+1344], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+1792]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+1856]
	vmovdqu32 ZMMWORD PTR [rsi+1792], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+1856], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+2304]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+2368]
	vmovdqu32 ZMMWORD PTR [rsi+2304], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+2368], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+2816]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+2880]
	vmovdqu32 ZMMWORD PTR [rsi+2816], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+2880], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+3328]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+3392]
	vmovdqu32 ZMMWORD PTR [rsi+3328], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+3392], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+3840]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+3904]
	vmovdqu32 ZMMWORD PTR [rsi+3840], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+3904], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+384]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+448]
	vmovdqu32 ZMMWORD PTR [rsi+384], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+448], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+896]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+960]
	vmovdqu32 ZMMWORD PTR [rsi+896], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+960], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+1408]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+1472]
	vmovdqu32 ZMMWORD PTR [rsi+1408], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+1472], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+1920]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+1984]
	vmovdqu32 ZMMWORD PTR [rsi+1920], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+1984], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+2432]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+2496]
	vmovdqu32 ZMMWORD PTR [rsi+2432], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+2496], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+2944]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+3008]
	vmovdqu32 ZMMWORD PTR [rsi+2944], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+3008], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+3456]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+3520]
	vmovdqu32 ZMMWORD PTR [rsi+3456], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+3520], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+3968]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+4032]
	vmovdqu32 ZMMWORD PTR [rsi+3968], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+4032], zmm0
	sub r11, 1
	jne 25b
	mov r11, 8
211:
	movabs rbx, 4294967295
	vmovq xmm13, rbx
	vpbroadcastq zmm13, xmm13
	movabs rbx, 281470681808895
	vmovq xmm14, rbx
	vpbroadcastq zmm14, xmm14
	movabs rbx, 71777214294589695
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm0, ZMMWORD PTR [rsi]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+512]
	vmovdqu32 zmm2, ZMMWORD PTR [rsi+1024]
	vmovdqu32 zmm3, ZMMWORD PTR [rsi+1536]
	vmovdqu32 zmm4, ZMMWORD PTR [rsi+2048]
	vmovdqu32 zmm5, ZMMWORD PTR [rsi+2560]
	vmovdqu32 zmm6, ZMMWORD PTR [rsi+3072]
	vmovdqu32 zmm7, ZMMWORD PTR [rsi+3584]
	vpsrlq zmm8, zmm0, 32
	vpxord zmm8, zmm8, zmm4
	vpandq zmm8, zmm8, zmm13
	vpxord zmm4, zmm4, zmm8
	vpsllq zmm8, zmm8, 32
	vpxord zmm0, zmm0, zmm8
	vpsrlq zmm8, zmm1, 32
	vpxord zmm8, zmm8, zmm5
	vpandq zmm8, zmm8, zmm13
	vpxord zmm5, zmm5, zmm8
	vpsllq zmm8, zmm8, 32
	vpxord zmm1, zmm1, zmm8
	vpsrlq zmm8, zmm2, 32
	vpxord zmm8, zmm8, zmm6
	vpandq zmm8, zmm8, zmm13
	vpxord zmm6, zmm6, zmm8
	vpsllq zmm8, zmm8, 32
	vpxord zmm2, zmm2, zmm8
	vpsrlq zmm8, zmm3, 32
	vpxord zmm8, zmm8, zmm7
	vpandq zmm8, zmm8, zmm13
	vpxord zmm7, zmm7, zmm8
	vpsllq zmm8, zmm8, 32
	vpxord zmm3, zmm3, zmm8
	vpsrlq zmm8, zmm0, 16
	vpxord zmm8, zmm8, zmm2
	vpandq zmm8, zmm8, zmm14
	vpxord zmm2, zmm2, zmm8
	vpsllq zmm8, zmm8, 16
	vpxord zmm0, zmm0, zmm8
	vpsrlq zmm8, zmm1, 16
	vpxord zmm8, zmm8, zmm3
	vpandq zmm8, zmm8, zmm14
	vpxord zmm3, zmm3, zmm8
	vpsllq zmm8, zmm8, 16
	vpxord zmm1, zmm1, zmm8
	vpsrlq zmm8, zmm4, 16
	vpxord zmm8, zmm8, zmm6
	vpandq zmm8, zmm8, zmm14
	vpxord zmm6, zmm6, zmm8
	vpsllq zmm8, zmm8, 16
	vpxord zmm4, zmm4, zmm8
	vpsrlq zmm8, zmm5, 16
	vpxord zmm8, zmm8, zmm7
	vpandq zmm8, zmm8, zmm14
	vpxord zmm7, zmm7, zmm8
	vpsllq zmm8, zmm8, 16
	vpxord zmm5, zmm5, zmm8
	vpsrlq zmm8, zmm0, 8
	vpxord zmm8, zmm8, zmm1
	vpandq zmm8, zmm8, zmm15
	vpxord zmm1, zmm1, zmm8
	vpsllq zmm8, zmm8, 8
	vpxord zmm0, zmm0, zmm8
	vpsrlq zmm8, zmm2, 8
	vpxord zmm8, zmm8, zmm3
	vpandq zmm8, zmm8, zmm15
	vpxord zmm3, zmm3, zmm8
	vpsllq zmm8, zmm8, 8
	vpxord zmm2, zmm2, zmm8
	vpsrlq zmm8, zmm4, 8
	vpxord zmm8, zmm8, zmm5
	vpandq zmm8, zmm8, zmm15
	vpxord zmm5, zmm5, zmm8
	vpsllq zmm8, zmm8, 8
	vpxord zmm4, zmm4, zmm8
	vpsrlq zmm8, zmm6, 8
	vpxord zmm8, zmm8, zmm7
	vpandq zmm8, zmm8, zmm15
	vpxord zmm7, zmm7, zmm8
	vpsllq zmm8, zmm8, 8
	vpxord zmm6, zmm6, zmm8
	vmovdqu32 ZMMWORD PTR [rsi], zmm0
	vmovdqu32 ZMMWORD PTR [rsi+512], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+1024], zmm2
	vmovdqu32 ZMMWORD PTR [rsi+1536], zmm3
	vmovdqu32 ZMMWORD PTR [rsi+2048], zmm4
	vmovdqu32 ZMMWORD PTR [rsi+2560], zmm5
	vmovdqu32 ZMMWORD PTR [rsi+3072], zmm6
	vmovdqu32 ZMMWORD PTR [rsi+3584], zmm7
	add rsi, 64
	sub r11, 1
	jne 211b
	sub rsi, 512
	mov r11, 8
212:
	movabs rbx, 1085102592571150095
	vmovq xmm13, rbx
	vpbroadcastq zmm13, xmm13
	movabs rbx, 3689348814741910323
	vmovq xmm14, rbx
	vpbroadcastq zmm14, xmm14
	movabs rbx, 6148914691236517205
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm0, ZMMWORD PTR [rsi]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+64]
	vmovdqu32 zmm2, ZMMWORD PTR [rsi+128]
	vmovdqu32 zmm3, ZMMWORD PTR [rsi+192]
	vmovdqu32 zmm4, ZMMWORD PTR [rsi+256]
	vmovdqu32 zmm5, ZMMWORD PTR [rsi+320]
	vmovdqu32 zmm6, ZMMWORD PTR [rsi+384]
	vmovdqu32 zmm7, ZMMWORD PTR [rsi+448]
	vpsrlq zmm8, zmm0, 4
	vpxord zmm8, zmm8, zmm4
	vpandq zmm8, zmm8, zmm13
	vpxord zmm4, zmm4, zmm8
	vpsllq zmm8, zmm8, 4
	vpxord zmm0, zmm0, zmm8
	vpsrlq zmm8, zmm1, 4
	vpxord zmm8, zmm8, zmm5
	vpandq zmm8, zmm8, zmm13
	vpxord zmm5, zmm5, zmm8
	vpsllq zmm8, zmm8, 4
	vpxord zmm1, zmm1, zmm8
	vpsrlq zmm8, zmm2, 4
	vpxord zmm8, zmm8, zmm6
	vpandq zmm8, zmm8, zmm13
	vpxord zmm6, zmm6, zmm8
	vpsllq zmm8, zmm8, 4
	vpxord zmm2, zmm2, zmm8
	vpsrlq zmm8, zmm3, 4
	vpxord zmm8, zmm8, zmm7
	vpandq zmm8, zmm8, zmm13
	vpxord zmm7, zmm7, zmm8
	vpsllq zmm8, zmm8, 4
	vpxord zmm3, zmm3, zmm8
	vpsrlq zmm8, zmm0, 2
	vpxord zmm8, zmm8, zmm2
	vpandq zmm8, zmm8, zmm14
	vpxord zmm2, zmm2, zmm8
	vpsllq zmm8, zmm8, 2
	vpxord zmm0, zmm0, zmm8
	vpsrlq zmm8, zmm1, 2
	vpxord zmm8, zmm8, zmm3
	vpandq zmm8, zmm8, zmm14
	vpxord zmm3, zmm3, zmm8
	vpsllq zmm8, zmm8, 2
	vpxord zmm1, zmm1, zmm8
	vpsrlq zmm8, zmm4, 2
	vpxord zmm8, zmm8, zmm6
	vpandq zmm8, zmm8, zmm14
	vpxord zmm6, zmm6, zmm8
	vpsllq zmm8, zmm8, 2
	vpxord zmm4, zmm4, zmm8
	vpsrlq zmm8, zmm5, 2
	vpxord zmm8, zmm8, zmm7
	vpandq zmm8, zmm8, zmm14
	vpxord zmm7, zmm7, zmm8
	vpsllq zmm8, zmm8, 2
	vpxord zmm5, zmm5, zmm8
	vpsrlq zmm8, zmm0, 1
	vpxord zmm8, zmm8, zmm1
	vpandq zmm8, zmm8, zmm15
	vpxord zmm1, zmm1, zmm8
	vpsllq zmm8, zmm8, 1
	vpxord zmm0, zmm0, zmm8
	vpsrlq zmm8, zmm2, 1
	vpxord zmm8, zmm8, zmm3
	vpandq zmm8, zmm8, zmm15
	vpxord zmm3, zmm3, zmm8
	vpsllq zmm8, zmm8, 1
	vpxord zmm2, zmm2, zmm8
	vpsrlq zmm8, zmm4, 1
	vpxord zmm8, zmm8, zmm5
	vpandq zmm8, zmm8, zmm15
	vpxord zmm5, zmm5, zmm8
	vpsllq zmm8, zmm8, 1
	vpxord zmm4, zmm4, zmm8
	vpsrlq zmm8, zmm6, 1
	vpxord zmm8, zmm8, zmm7
	vpandq zmm8, zmm8, zmm15
	vpxord zmm7, zmm7, zmm8
	vpsllq zmm8, zmm8, 1
	vpxord zmm6, zmm6, zmm8
	vmovdqu32 ZMMWORD PTR [rsi], zmm0
	vmovdqu32 ZMMWORD PTR [rsi+64], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+128], zmm2
	vmovdqu32 ZMMWORD PTR [rsi+192], zmm3
	vmovdqu32 ZMMWORD PTR [rsi+256], zmm4
	vmovdqu32 ZMMWORD PTR [rsi+320], zmm5
	vmovdqu32 ZMMWORD PTR [rsi+384], zmm6
	vmovdqu32 ZMMWORD PTR [rsi+448], zmm7
	add rsi, 512
	sub r11, 1
	jne 212b
	sub rsi, 4096
	add rsi, 4096
	sub rdx, 512
	cmp rdx, 512
	jae 22b
	mov rbx, QWORD PTR [rcx+1016]
	mov r12, QWORD PTR [rcx+1008]
	mov r13, QWORD PTR [rcx+1000]
	vzeroupper
	jmp 21f
20:
21:
	cmp rdx, 256
	jb 213f
	mov QWORD PTR [rcx+1016], rbx
	mov QWORD PTR [rcx+1008], r12
	mov QWORD PTR [rcx+1000], r13
215:
	mov r11, 8
216:
	movabs rbx, 4294967295
	vmovq xmm13, rbx
	vpbroadcastq ymm13, xmm13
	movabs rbx, 281470681808895
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	movabs rbx, 71777214294589695
	vmovq xmm15, rbx
	vpbroadcastq ymm15, xmm15
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vmovdqu ymm1, YMMWORD PTR [rsi+256]
	vmovdqu ymm2, YMMWORD PTR [rsi+512]
	vmovdqu ymm3, YMMWORD PTR [rsi+768]
	vmovdqu ymm4, YMMWORD PTR [rsi+1024]
	vmovdqu ymm5, YMMWORD PTR [rsi+1280]
	vmovdqu ymm6, YMMWORD PTR [rsi+1536]
	vmovdqu ymm7, YMMWORD PTR [rsi+1792]
	vpsrlq ymm8, ymm0, 32
	vpxor ymm8, ymm8, ymm4
	vpand ymm8, ymm8, ymm13
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm8, ymm8, 32
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm1, 32
	vpxor ymm8, ymm8, ymm5
	vpand ymm8, ymm8, ymm13
	vpxor ymm5, ymm5, ymm8
	vpsllq ymm8, ymm8, 32
	vpxor ymm1, ymm1, ymm8
	vpsrlq ymm8, ymm2, 32
	vpxor ymm8, ymm8, ymm6
	vpand ymm8, ymm8, ymm13
	vpxor ymm6, ymm6, ymm8
	vpsllq ymm8, ymm8, 32
	vpxor ymm2, ymm2, ymm8
	vpsrlq ymm8, ymm3, 32
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm13
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 32
	vpxor ymm3, ymm3, ymm8
	vpsrlq ymm8, ymm0, 16
	vpxor ymm8, ymm8, ymm2
	vpand ymm8, ymm8, ymm14
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm8, ymm8, 16
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm1, 16
	vpxor ymm8, ymm8, ymm3
	vpand ymm8, ymm8, ymm14
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm8, ymm8, 16
	vpxor ymm1, ymm1, ymm8
	vpsrlq ymm8, ymm4, 16
	vpxor ymm8, ymm8, ymm6
	vpand ymm8, ymm8, ymm14
	vpxor ymm6, ymm6, ymm8
	vpsllq ymm8, ymm8, 16
	vpxor ymm4, ymm4, ymm8
	vpsrlq ymm8, ymm5, 16
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm14
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 16
	vpxor ymm5, ymm5, ymm8
	vpsrlq ymm8, ymm0, 8
	vpxor ymm8, ymm8, ymm1
	vpand ymm8, ymm8, ymm15
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm8, ymm8, 8
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm2, 8
	vpxor ymm8, ymm8, ymm3
	vpand ymm8, ymm8, ymm15
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm8, ymm8, 8
	vpxor ymm2, ymm2, ymm8
	vpsrlq ymm8, ymm4, 8
	vpxor ymm8, ymm8, ymm5
	vpand ymm8, ymm8, ymm15
	vpxor ymm5, ymm5, ymm8
	vpsllq ymm8, ymm8, 8
	vpxor ymm4, ymm4, ymm8
	vpsrlq ymm8, ymm6, 8
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm15
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 8
	vpxor ymm6, ymm6, ymm8
	vmovdqu YMMWORD PTR [rsi], ymm0
	vmovdqu YMMWORD PTR [rsi+256], ymm1
	vmovdqu YMMWORD PTR [rsi+512], ymm2
	vmovdqu YMMWORD PTR [rsi+768], ymm3
	vmovdqu YMMWORD PTR [rsi+1024], ymm4
	vmovdqu YMMWORD PTR [rsi+1280], ymm5
	vmovdqu YMMWORD PTR [rsi+1536], ymm6
	vmovdqu YMMWORD PTR [rsi+1792], ymm7
	add rsi, 32
	sub r11, 1
	jne 216b
	sub rsi, 256
	mov r11, 8
217:
	movabs rbx, 1085102592571150095
	vmovq xmm13, rbx
	vpbroadcastq ymm13, xmm13
	movabs rbx, 3689348814741910323
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	movabs rbx, 6148914691236517205
	vmovq xmm15, rbx
	vpbroadcastq ymm15, xmm15
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vmovdqu ymm2, YMMWORD PTR [rsi+64]
	vmovdqu ymm3, YMMWORD PTR [rsi+96]
	vmovdqu ymm4, YMMWORD PTR [rsi+128]
	vmovdqu ymm5, YMMWORD PTR [rsi+160]
	vmovdqu ymm6, YMMWORD PTR [rsi+192]
	vmovdqu ymm7, YMMWORD PTR [rsi+224]
	vpsrlq ymm8, ymm0, 4
	vpxor ymm8, ymm8, ymm4
	vpand ymm8, ymm8, ymm13
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm8, ymm8, 4
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm1, 4
	vpxor ymm8, ymm8, ymm5
	vpand ymm8, ymm8, ymm13
	vpxor ymm5, ymm5, ymm8
	vpsllq ymm8, ymm8, 4
	vpxor ymm1, ymm1, ymm8
	vpsrlq ymm8, ymm2, 4
	vpxor ymm8, ymm8, ymm6
	vpand ymm8, ymm8, ymm13
	vpxor ymm6, ymm6, ymm8
	vpsllq ymm8, ymm8, 4
	vpxor ymm2, ymm2, ymm8
	vpsrlq ymm8, ymm3, 4
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm13
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 4
	vpxor ymm3, ymm3, ymm8
	vpsrlq ymm8, ymm0, 2
	vpxor ymm8, ymm8, ymm2
	vpand ymm8, ymm8, ymm14
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm8, ymm8, 2
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm1, 2
	vpxor ymm8, ymm8, ymm3
	vpand ymm8, ymm8, ymm14
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm8, ymm8, 2
	vpxor ymm1, ymm1, ymm8
	vpsrlq ymm8, ymm4, 2
	vpxor ymm8, ymm8, ymm6
	vpand ymm8, ymm8, ymm14
	vpxor ymm6, ymm6, ymm8
	vpsllq ymm8, ymm8, 2
	vpxor ymm4, ymm4, ymm8
	vpsrlq ymm8, ymm5, 2
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm14
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 2
	vpxor ymm5, ymm5, ymm8
	vpsrlq ymm8, ymm0, 1
	vpxor ymm8, ymm8, ymm1
	vpand ymm8, ymm8, ymm15
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm8, ymm8, 1
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm2, 1
	vpxor ymm8, ymm8, ymm3
	vpand ymm8, ymm8, ymm15
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm8, ymm8, 1
	vpxor ymm2, ymm2, ymm8
	vpsrlq ymm8, ymm4, 1
	vpxor ymm8, ymm8, ymm5
	vpand ymm8, ymm8, ymm15
	vpxor ymm5, ymm5, ymm8
	vpsllq ymm8, ymm8, 1
	vpxor ymm4, ymm4, ymm8
	vpsrlq ymm8, ymm6, 1
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm15
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 1
	vpxor ymm6, ymm6, ymm8
	vmovdqu YMMWORD PTR [rsi], ymm0
	vmovdqu YMMWORD PTR [rsi+32], ymm1
	vmovdqu YMMWORD PTR [rsi+64], ymm2
	vmovdqu YMMWORD PTR [rsi+96], ymm3
	vmovdqu YMMWORD PTR [rsi+128], ymm4
	vmovdqu YMMWORD PTR [rsi+160], ymm5
	vmovdqu YMMWORD PTR [rsi+192], ymm6
	vmovdqu YMMWORD PTR [rsi+224], ymm7
	add rsi, 256
	sub r11, 1
	jne 217b
	sub rsi, 2048
	movabs rbx, -1
	vmovq xmm15, rbx
	vpbroadcastq ymm15, xmm15
	mov r11, 3
218:
	cmp r11, 3
	je 219f
	cmp r11, 2
	je 221f
	mov r8, rdi
	add r8, 256
	mov r9, 8
	jmp 222f
221:
	mov r8, rdi
	add r8, 248
	mov r9, -8
222:
	jmp 220f
219:
	mov r8, rdi
	add r8, 0
	mov r9, 8
220:
	mov r10, 16
	mov r12, rsi
	add r12, 32
	mov r13, rsi
223:
	mov rax, QWORD PTR [r8]
	add r8, r9
	ror rax, 48
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm5, YMMWORD PTR [r12]
	vpxor ymm5, ymm5, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm4, YMMWORD PTR [r12+1984]
	vpxor ymm4, ymm4, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm3, YMMWORD PTR [r12+1728]
	vpxor ymm3, ymm3, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm2, YMMWORD PTR [r12+1472]
	vpxor ymm2, ymm2, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm1, YMMWORD PTR [r12+1216]
	vpxor ymm1, ymm1, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm0, YMMWORD PTR [r12+960]
	vpxor ymm0, ymm0, ymm14
	vpandn ymm6, ymm1, ymm5
	vpxor ymm7, ymm2, ymm6
	vpor ymm8, ymm3, ymm0
	vpxor ymm9, ymm5, ymm3
	vpand ymm10, ymm8, ymm9
	vpxor ymm11, ymm2, ymm10
	vpandn ymm12, ymm7, ymm11
	vpxor ymm13, ymm1, ymm0
	vpxor ymm14, ymm3, ymm13
	vpandn ymm14, ymm14, ymm7
	vpor ymm10, ymm0, ymm10
	vpxor ymm10, ymm14, ymm10
	vpandn ymm14, ymm12, ymm10
	vpor ymm0, ymm5, ymm0
	vmovdqu YMMWORD PTR [rcx], ymm14
	vpor ymm14, ymm10, ymm0
	vpandn ymm11, ymm11, ymm1
	vmovdqu YMMWORD PTR [rcx+32], ymm1
	vpxor ymm1, ymm14, ymm11
	vpandn ymm0, ymm0, ymm2
	vpxor ymm0, ymm11, ymm0
	vpandn ymm9, ymm9, ymm13
	vpor ymm9, ymm0, ymm9
	vpandn ymm6, ymm6, ymm3
	vpxor ymm3, ymm7, ymm14
	vpandn ymm6, ymm6, ymm3
	vpxor ymm3, ymm6, ymm15
	vpand ymm10, ymm8, ymm10
	vpxor ymm10, ymm3, ymm10
	vpandn ymm1, ymm4, ymm1
	vpxor ymm1, ymm1, ymm10
	vpxor ymm6, ymm13, ymm6
	vpor ymm6, ymm11, ymm6
	vpxor ymm6, ymm8, ymm6
	vpxor ymm6, ymm5, ymm6
	vpxor ymm10, ymm10, ymm6
	vpor ymm12, ymm12, ymm4
	vpxor ymm12, ymm12, ymm10
	vpxor ymm14, ymm8, ymm14
	vpor ymm14, ymm9, ymm14
	vpxor ymm14, ymm6, ymm14
	vpor ymm10, ymm13, ymm10
	vpxor ymm10, ymm14, ymm10
	vmovdqu ymm13, YMMWORD PTR [rcx]
	vpor ymm8, ymm13, ymm4
	vpxor ymm10, ymm8, ymm10
	vmovdqu ymm8, YMMWORD PTR [rcx+32]
	vpor ymm7, ymm8, ymm7
	vpandn ymm14, ymm14, ymm7
	vpand ymm6, ymm13, ymm6
	vpxor ymm6, ymm14, ymm6
	vpor ymm4, ymm6, ymm4
	vpxor ymm9, ymm4, ymm9
	vmovdqa ymm0, ymm9
	vmovdqa ymm2, ymm10
	vmovdqa ymm3, ymm12
	vmovdqu ymm14, YMMWORD PTR [r13+256]
	vpxor ymm0, ymm0, ymm14
	vmovdqu YMMWORD PTR [r13+256], ymm0
	vmovdqu ymm14, YMMWORD PTR [r13+320]
	vpxor ymm1, ymm1, ymm14
	vmovdqu YMMWORD PTR [r13+320], ymm1
	vmovdqu ymm14, YMMWORD PTR [r13+1856]
	vpxor ymm2, ymm2, ymm14
	vmovdqu YMMWORD PTR [r13+1856], ymm2
	vmovdqu ymm14, YMMWORD PTR [r13+1920]
	vpxor ymm3, ymm3, ymm14
	vmovdqu YMMWORD PTR [r13+1920], ymm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm5, YMMWORD PTR [r12+1216]
	vpxor ymm5, ymm5, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm4, YMMWORD PTR [r12+960]
	vpxor ymm4, ymm4, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm3, YMMWORD PTR [r12+704]
	vpxor ymm3, ymm3, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm2, YMMWORD PTR [r12+448]
	vpxor ymm2, ymm2, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm1, YMMWORD PTR [r12+192]
	vpxor ymm1, ymm1, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm0, YMMWORD PTR [r12+1920]
	vpxor ymm0, ymm0, ymm14
	vpxor ymm6, ymm4, ymm1
	vpandn ymm7, ymm0, ymm5
	vpandn ymm7, ymm7, ymm1
	vpor ymm8, ymm4, ymm7
	vpandn ymm9, ymm0, ymm6
	vpand ymm10, ymm5, ymm6
	vpxor ymm10, ymm1, ymm10
	vpandn ymm1, ymm9, ymm10
	vpand ymm11, ymm3, ymm0
	vpxor ymm9, ymm7, ymm9
	vpand ymm9, ymm8, ymm9
	vpandn ymm7, ymm11, ymm9
	vpand ymm12, ymm3, ymm9
	vpxor ymm5, ymm5, ymm15
	vpxor ymm5, ymm12, ymm5
	vpxor ymm0, ymm0, ymm6
	vpandn ymm13, ymm11, ymm0
	vpxor ymm14, ymm5, ymm13
	vpandn ymm7, ymm7, ymm2
	vpxor ymm7, ymm7, ymm14
	vpandn ymm13, ymm13, ymm4
	vpxor ymm10, ymm10, ymm13
	vpandn ymm5, ymm10, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm5, ymm5, ymm3
	vpandn ymm4, ymm2, ymm8
	vpxor ymm4, ymm4, ymm5
	vpxor ymm13, ymm12, ymm13
	vpor ymm13, ymm3, ymm13
	vpxor ymm8, ymm8, ymm14
	vpor ymm11, ymm11, ymm8
	vpxor ymm3, ymm13, ymm11
	vpxor ymm14, ymm9, ymm14
	vpxor ymm14, ymm5, ymm14
	vpand ymm14, ymm11, ymm14
	vpand ymm13, ymm6, ymm13
	vpxor ymm13, ymm14, ymm13
	vpor ymm14, ymm13, ymm2
	vpxor ymm3, ymm14, ymm3
	vpandn ymm10, ymm10, ymm13
	vpor ymm8, ymm0, ymm8
	vpxor ymm8, ymm10, ymm8
	vpor ymm2, ymm1, ymm2
	vpxor ymm8, ymm2, ymm8
	vmovdqa ymm0, ymm8
	vmovdqa ymm1, ymm3
	vmovdqa ymm2, ymm7
	vmovdqa ymm3, ymm4
	vmovdqu ymm14, YMMWORD PTR [r13+1600]
	vpxor ymm0, ymm0, ymm14
	vmovdqu YMMWORD PTR [r13+1600], ymm0
	vmovdqu ymm14, YMMWORD PTR [r13+1728]
	vpxor ymm1, ymm1, ymm14
	vmovdqu YMMWORD PTR [r13+1728], ymm1
	vmovdqu ymm14, YMMWORD PTR [r13+1024]
	vpxor ymm2, ymm2, ymm14
	vmovdqu YMMWORD PTR [r13+1024], ymm2
	vmovdqu ymm14, YMMWORD PTR [r13+896]
	vpxor ymm3, ymm3, ymm14
	vmovdqu YMMWORD PTR [r13+896], ymm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm5, YMMWORD PTR [r12+192]
	vpxor ymm5, ymm5, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm4, YMMWORD PTR [r12+1920]
	vpxor ymm4, ymm4, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm3, YMMWORD PTR [r12+1664]
	vpxor ymm3, ymm3, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm2, YMMWORD PTR [r12+1408]
	vpxor ymm2, ymm2, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm1, YMMWORD PTR [r12+1152]
	vpxor ymm1, ymm1, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm0, YMMWORD PTR [r12+896]
	vpxor ymm0, ymm0, ymm14
	vpandn ymm6, ymm4, ymm5
	vpxor ymm7, ymm3, ymm0
	vpor ymm8, ymm6, ymm7
	vpxor ymm9, ymm2, ymm0
	vpandn ymm10, ymm5, ymm9
	vpxor ymm11, ymm8, ymm10
	vpxor ymm12, ymm4, ymm7
	vpandn ymm13, ymm0, ymm12
	vpxor ymm13, ymm8, ymm13
	vpandn ymm8, ymm13, ymm11
	vpand ymm14, ymm0, ymm11
	vpor ymm14, ymm2, ymm14
	vpand ymm14, ymm5, ymm14
	vpxor ymm14, ymm12, ymm14
	vmovdqu YMMWORD PTR [rcx], ymm6
	vpandn ymm6, ymm1, ymm11
	vpxor ymm6, ymm6, ymm14
	vpand ymm9, ymm7, ymm9
	vpxor ymm7, ymm5, ymm2
	vmovdqu YMMWORD PTR [rcx+32], ymm6
	vpxor ymm6, ymm13, ymm7
	vpor ymm6, ymm3, ymm6
	vpandn ymm9, ymm9, ymm6
	vpor ymm7, ymm10, ymm7
	vpandn ymm10, ymm7, ymm14
	vpand ymm0, ymm2, ymm0
	vpandn ymm6, ymm4, ymm0
	vpxor ymm6, ymm10, ymm6
	vpand ymm13, ymm13, ymm6
	vpor ymm0, ymm12, ymm0
	vpandn ymm13, ymm13, ymm0
	vpxor ymm13, ymm5, ymm13
	vpand ymm9, ymm9, ymm1
	vpxor ymm9, ymm9, ymm13
	vpxor ymm11, ymm11, ymm15
	vpor ymm4, ymm4, ymm11
	vpor ymm4, ymm3, ymm4
	vpxor ymm4, ymm12, ymm4
	vpxor ymm7, ymm7, ymm4
	vpandn ymm8, ymm8, ymm1
	vpxor ymm7, ymm8, ymm7
	vpand ymm11, ymm2, ymm11
	vpxor ymm11, ymm14, ymm11
	vpor ymm11, ymm4, ymm11
	vmovdqu ymm4, YMMWORD PTR [rcx]
	vpxor ymm13, ymm4, ymm13
	vpxor ymm13, ymm11, ymm13
	vpor ymm1, ymm6, ymm1
	vpxor ymm13, ymm1, ymm13
	vmovdqu ymm0, YMMWORD PTR [rcx+32]
	vmovdqa ymm1, ymm13
	vmovdqa ymm2, ymm9
	vmovdqa ymm3, ymm7
	vmovdqu ymm14, YMMWORD PTR [r13+704]
	vpxor ymm0, ymm0, ymm14
	vmovdqu YMMWORD PTR [r13+704], ymm0
	vmovdqu ymm14, YMMWORD PTR [r13+512]
	vpxor ymm1, ymm1, ymm14
	vmovdqu YMMWORD PTR [r13+512], ymm1
	vmovdqu ymm14, YMMWORD PTR [r13+128]
	vpxor ymm2, ymm2, ymm14
	vmovdqu YMMWORD PTR [r13+128], ymm2
	vmovdqu ymm14, YMMWORD PTR [r13+64]
	vpxor ymm3, ymm3, ymm14
	vmovdqu YMMWORD PTR [r13+64], ymm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm5, YMMWORD PTR [r12+1152]
	vpxor ymm5, ymm5, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm4, YMMWORD PTR [r12+896]
	vpxor ymm4, ymm4, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm3, YMMWORD PTR [r12+640]
	vpxor ymm3, ymm3, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm2, YMMWORD PTR [r12+384]
	vpxor ymm2, ymm2, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm1, YMMWORD PTR [r12+128]
	vpxor ymm1, ymm1, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm0, YMMWORD PTR [r12+1856]
	vpxor ymm0, ymm0, ymm14
	vpxor ymm5, ymm5, ymm3
	vpxor ymm3, ymm3, ymm1
	vpor ymm6, ymm4, ymm2
	vpxor ymm6, ymm1, ymm6
	vpandn ymm6, ymm6, ymm3
	vpandn ymm7, ymm4, ymm3
	vpxor ymm8, ymm2, ymm7
	vpor ymm9, ymm5, ymm8
	vpandn ymm9, ymm6, ymm9
	vpxor ymm10, ymm4, ymm9
	vpand ymm8, ymm8, ymm10
	vpandn ymm3, ymm8, ymm3
	vpxor ymm5, ymm5, ymm10
	vpandn ymm3, ymm3, ymm5
	vpxor ymm3, ymm6, ymm3
	vpxor ymm2, ymm4, ymm2
	vpor ymm7, ymm1, ymm7
	vpxor ymm7, ymm5, ymm7
	vpandn ymm5, ymm2, ymm7
	vpxor ymm5, ymm9, ymm5
	vpandn ymm9, ymm3, ymm0
	vpxor ymm9, ymm9, ymm5
	vpxor ymm5, ymm5, ymm15
	vpandn ymm1, ymm0, ymm3
	vpxor ymm1, ymm1, ymm5
	vpxor ymm5, ymm3, ymm5
	vpandn ymm2, ymm2, ymm5
	vpor ymm2, ymm8, ymm2
	vpxor ymm2, ymm7, ymm2
	vpor ymm7, ymm10, ymm0
	vpxor ymm7, ymm7, ymm2
	vpand ymm10, ymm0, ymm10
	vpxor ymm2, ymm10, ymm2
	vmovdqa ymm0, ymm2
	vmovdqu YMMWORD PTR [rcx], ymm1
	vmovdqa ymm1, ymm7
	vmovdqu ymm2, YMMWORD PTR [rcx]
	vmovdqa ymm3, ymm9
	vmovdqu ymm14, YMMWORD PTR [r13+1984]
	vpxor ymm0, ymm0, ymm14
	vmovdqu YMMWORD PTR [r13+1984], ymm0
	vmovdqu ymm14, YMMWORD PTR [r13+1664]
	vpxor ymm1, ymm1, ymm14
	vmovdqu YMMWORD PTR [r13+1664], ymm1
	vmovdqu ymm14, YMMWORD PTR [r13+1088]
	vpxor ymm2, ymm2, ymm14
	vmovdqu YMMWORD PTR [r13+1088], ymm2
	vmovdqu ymm14, YMMWORD PTR [r13+1536]
	vpxor ymm3, ymm3, ymm14
	vmovdqu YMMWORD PTR [r13+1536], ymm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm5, YMMWORD PTR [r12+128]
	vpxor ymm5, ymm5, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm4, YMMWORD PTR [r12+1856]
	vpxor ymm4, ymm4, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm3, YMMWORD PTR [r12+1600]
	vpxor ymm3, ymm3, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm2, YMMWORD PTR [r12+1344]
	vpxor ymm2, ymm2, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm1, YMMWORD PTR [r12+1088]
	vpxor ymm1, ymm1, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm0, YMMWORD PTR [r12+832]
	vpxor ymm0, ymm0, ymm14
	vpor ymm6, ymm5, ymm3
	vpandn ymm7, ymm0, ymm6
	vpxor ymm8, ymm5, ymm7
	vpxor ymm9, ymm3, ymm8
	vpor ymm10, ymm2, ymm9
	vpandn ymm7, ymm2, ymm7
	vpxor ymm7, ymm3, ymm7
	vpand ymm3, ymm1, ymm7
	vpor ymm9, ymm5, ymm9
	vpxor ymm3, ymm3, ymm9
	vpxor ymm3, ymm2, ymm3
	vpxor ymm0, ymm0, ymm3
	vpor ymm11, ymm8, ymm0
	vpand ymm12, ymm1, ymm11
	vpxor ymm13, ymm8, ymm12
	vpand ymm14, ymm2, ymm9
	vpxor ymm14, ymm13, ymm14
	vpandn ymm11, ymm5, ymm11
	vpxor ymm13, ymm7, ymm11
	vpxor ymm1, ymm1, ymm10
	vpandn ymm13, ymm13, ymm1
	vpxor ymm13, ymm13, ymm15
	vpandn ymm13, ymm4, ymm13
	vpxor ymm3, ymm13, ymm3
	vpandn ymm13, ymm12, ymm7
	vpxor ymm11, ymm11, ymm1
	vpor ymm11, ymm14, ymm11
	vpandn ymm13, ymm13, ymm11
	vpandn ymm11, ymm13, ymm10
	vpand ymm0, ymm0, ymm13
	vpxor ymm0, ymm1, ymm0
	vpand ymm9, ymm7, ymm9
	vpor ymm9, ymm0, ymm9
	vpxor ymm9, ymm12, ymm9
	vpand ymm9, ymm9, ymm4
	vpxor ymm14, ymm9, ymm14
	vpxor ymm6, ymm5, ymm6
	vpxor ymm6, ymm13, ymm6
	vpand ymm2, ymm2, ymm0
	vpxor ymm2, ymm6, ymm2
	vpor ymm11, ymm11, ymm4
	vpxor ymm11, ymm11, ymm2
	vpxor ymm7, ymm10, ymm7
	vpandn ymm2, ymm2, ymm7
	vpxor ymm0, ymm8, ymm0
	vpxor ymm0, ymm2, ymm0
	vpand ymm4, ymm10, ymm4
	vpxor ymm0, ymm4, ymm0
	vmovdqu YMMWORD PTR [rcx], ymm0
	vmovdqa ymm0, ymm14
	vmovdqa ymm1, ymm3
	vmovdqu ymm2, YMMWORD PTR [rcx]
	vmovdqa ymm3, ymm11
	vmovdqu ymm14, YMMWORD PTR [r13+1472]
	vpxor ymm0, ymm0, ymm14
	vmovdqu YMMWORD PTR [r13+1472], ymm0
	vmovdqu ymm14, YMMWORD PTR [r13+1792]
	vpxor ymm1, ymm1, ymm14
	vmovdqu YMMWORD PTR [r13+1792], ymm1
	vmovdqu ymm14, YMMWORD PTR [r13+640]
	vpxor ymm2, ymm2, ymm14
	vmovdqu YMMWORD PTR [r13+640], ymm2
	vmovdqu ymm14, YMMWORD PTR [r13+192]
	vpxor ymm3, ymm3, ymm14
	vmovdqu YMMWORD PTR [r13+192], ymm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm5, YMMWORD PTR [r12+1088]
	vpxor ymm5, ymm5, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm4, YMMWORD PTR [r12+832]
	vpxor ymm4, ymm4, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm3, YMMWORD PTR [r12+576]
	vpxor ymm3, ymm3, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm2, YMMWORD PTR [r12+320]
	vpxor ymm2, ymm2, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm1, YMMWORD PTR [r12+64]
	vpxor ymm1, ymm1, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm0, YMMWORD PTR [r12+1792]
	vpxor ymm0, ymm0, ymm14
	vpxor ymm6, ymm4, ymm1
	vpor ymm7, ymm4, ymm0
	vpand ymm7, ymm5, ymm7
	vpxor ymm6, ymm6, ymm7
	vpxor ymm8, ymm0, ymm6
	vpandn ymm9, ymm8, ymm1
	vpand ymm8, ymm5, ymm8
	vpxor ymm10, ymm4, ymm8
	vpxor ymm11, ymm5, ymm3
	vpor ymm12, ymm10, ymm11
	vpxor ymm13, ymm6, ymm12
	vpand ymm14, ymm3, ymm13
	vmovdqu YMMWORD PTR [rcx], ymm8
	vpandn ymm8, ymm0, ymm14
	vpor ymm10, ymm9, ymm10
	vmovdqu YMMWORD PTR [rcx+32], ymm6
	vpxor ymm6, ymm8, ymm10
	vmovdqu YMMWORD PTR [rcx+64], ymm9
	vpand ymm9, ymm6, ymm2
	vpxor ymm9, ymm9, ymm13
	vpxor ymm12, ymm4, ymm12
	vmovdqu YMMWORD PTR [rcx+96], ymm9
	vpandn ymm9, ymm12, ymm0
	vpxor ymm9, ymm3, ymm9
	vpandn ymm3, ymm14, ymm1
	vpor ymm3, ymm9, ymm3
	vpor ymm11, ymm4, ymm11
	vpxor ymm6, ymm6, ymm11
	vpor ymm7, ymm7, ymm3
	vpxor ymm7, ymm6, ymm7
	vpor ymm13, ymm5, ymm13
	vpand ymm13, ymm10, ymm13
	vpxor ymm13, ymm9, ymm13
	vpandn ymm8, ymm8, ymm13
	vmovdqu ymm10, YMMWORD PTR [rcx+64]
	vpor ymm10, ymm10, ymm2
	vpxor ymm8, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rcx+32]
	vpxor ymm13, ymm10, ymm13
	vpandn ymm13, ymm13, ymm1
	vpxor ymm11, ymm11, ymm15
	vpxor ymm11, ymm12, ymm11
	vpxor ymm13, ymm13, ymm11
	vpandn ymm13, ymm2, ymm13
	vpxor ymm7, ymm13, ymm7
	vmovdqu ymm13, YMMWORD PTR [rcx]
	vpxor ymm13, ymm0, ymm13
	vpxor ymm9, ymm5, ymm9
	vpand ymm9, ymm13, ymm9
	vpxor ymm11, ymm14, ymm11
	vpxor ymm11, ymm9, ymm11
	vpandn ymm2, ymm2, ymm3
	vpxor ymm11, ymm2, ymm11
	vmovdqu ymm0, YMMWORD PTR [rcx+96]
	vmovdqa ymm1, ymm8
	vmovdqa ymm2, ymm7
	vmovdqa ymm3, ymm11
	vmovdqu ymm14, YMMWORD PTR [r13+1344]
	vpxor ymm0, ymm0, ymm14
	vmovdqu YMMWORD PTR [r13+1344], ymm0
	vmovdqu ymm14, YMMWORD PTR [r13+1408]
	vpxor ymm1, ymm1, ymm14
	vmovdqu YMMWORD PTR [r13+1408], ymm1
	vmovdqu ymm14, YMMWORD PTR [r13+768]
	vpxor ymm2, ymm2, ymm14
	vmovdqu YMMWORD PTR [r13+768], ymm2
	vmovdqu ymm14, YMMWORD PTR [r13+1216]
	vpxor ymm3, ymm3, ymm14
	vmovdqu YMMWORD PTR [r13+1216], ymm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm5, YMMWORD PTR [r12+64]
	vpxor ymm5, ymm5, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm4, YMMWORD PTR [r12+1792]
	vpxor ymm4, ymm4, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm3, YMMWORD PTR [r12+1536]
	vpxor ymm3, ymm3, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm2, YMMWORD PTR [r12+1280]
	vpxor ymm2, ymm2, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm1, YMMWORD PTR [r12+1024]
	vpxor ymm1, ymm1, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm0, YMMWORD PTR [r12+768]
	vpxor ymm0, ymm0, ymm14
	vpxor ymm6, ymm2, ymm1
	vpxor ymm7, ymm3, ymm6
	vpand ymm8, ymm0, ymm7
	vpand ymm9, ymm2, ymm6
	vpxor ymm10, ymm4, ymm9
	vpand ymm11, ymm8, ymm10
	vpand ymm12, ymm0, ymm9
	vpxor ymm13, ymm3, ymm12
	vpor ymm14, ymm10, ymm13
	vpxor ymm6, ymm0, ymm6
	vmovdqu YMMWORD PTR [rcx], ymm0
	vpxor ymm0, ymm14, ymm6
	vmovdqu YMMWORD PTR [rcx+32], ymm9
	vpandn ymm9, ymm11, ymm5
	vpxor ymm0, ymm9, ymm0
	vpandn ymm7, ymm7, ymm1
	vpor ymm9, ymm10, ymm7
	vpxor ymm13, ymm8, ymm13
	vpxor ymm9, ymm9, ymm13
	vpxor ymm6, ymm8, ymm6
	vpandn ymm2, ymm6, ymm2
	vpandn ymm8, ymm2, ymm10
	vpxor ymm13, ymm1, ymm13
	vpxor ymm13, ymm8, ymm13
	vpandn ymm12, ymm12, ymm6
	vpor ymm2, ymm2, ymm12
	vpxor ymm14, ymm4, ymm14
	vpand ymm14, ymm13, ymm14
	vpxor ymm14, ymm2, ymm14
	vpand ymm6, ymm14, ymm5
	vpxor ymm6, ymm6, ymm13
	vpandn ymm3, ymm3, ymm10
	vpor ymm3, ymm12, ymm3
	vmovdqu ymm12, YMMWORD PTR [rcx+32]
	vpor ymm13, ymm12, ymm13
	vpand ymm13, ymm3, ymm13
	vpxor ymm14, ymm14, ymm13
	vpxor ymm2, ymm7, ymm2
	vmovdqu ymm7, YMMWORD PTR [rcx]
	vpand ymm2, ymm7, ymm2
	vpor ymm2, ymm11, ymm2
	vpxor ymm13, ymm13, ymm2
	vpandn ymm11, ymm5, ymm13
	vpxor ymm11, ymm11, ymm9
	vpand ymm2, ymm4, ymm2
	vpxor ymm9, ymm9, ymm15
	vpxor ymm9, ymm2, ymm9
	vpxor ymm9, ymm13, ymm9
	vpor ymm5, ymm14, ymm5
	vpxor ymm9, ymm5, ymm9
	vmovdqa ymm1, ymm6
	vmovdqa ymm2, ymm9
	vmovdqa ymm3, ymm11
	vmovdqu ymm14, YMMWORD PTR [r13+448]
	vpxor ymm0, ymm0, ymm14
	vmovdqu YMMWORD PTR [r13+448], ymm0
	vmovdqu ymm14, YMMWORD PTR [r13+576]
	vpxor ymm1, ymm1, ymm14
	vmovdqu YMMWORD PTR [r13+576], ymm1
	vmovdqu ymm14, YMMWORD PTR [r13+1152]
	vpxor ymm2, ymm2, ymm14
	vmovdqu YMMWORD PTR [r13+1152], ymm2
	vmovdqu ymm14, YMMWORD PTR [r13]
	vpxor ymm3, ymm3, ymm14
	vmovdqu YMMWORD PTR [r13], ymm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm5, YMMWORD PTR [r12+1024]
	vpxor ymm5, ymm5, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm4, YMMWORD PTR [r12+768]
	vpxor ymm4, ymm4, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm3, YMMWORD PTR [r12+512]
	vpxor ymm3, ymm3, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm2, YMMWORD PTR [r12+256]
	vpxor ymm2, ymm2, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm1, YMMWORD PTR [r12]
	vpxor ymm1, ymm1, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm0, YMMWORD PTR [r12+1984]
	vpxor ymm0, ymm0, ymm14
	vpandn ymm6, ymm4, ymm3
	vpandn ymm7, ymm3, ymm1
	vpxor ymm7, ymm2, ymm7
	vpand ymm8, ymm5, ymm7
	vpandn ymm9, ymm6, ymm8
	vpandn ymm10, ymm7, ymm4
	vpor ymm11, ymm5, ymm10
	vpandn ymm12, ymm3, ymm4
	vpxor ymm12, ymm1, ymm12
	vpand ymm13, ymm11, ymm12
	vpor ymm8, ymm8, ymm13
	vpxor ymm7, ymm7, ymm15
	vpxor ymm7, ymm13, ymm7
	vpandn ymm11, ymm11, ymm3
	vpxor ymm11, ymm7, ymm11
	vpxor ymm6, ymm6, ymm11
	vpor ymm7, ymm9, ymm0
	vpxor ymm7, ymm7, ymm6
	vpxor ymm6, ymm5, ymm6
	vpand ymm3, ymm1, ymm6
	vpxor ymm11, ymm4, ymm11
	vpxor ymm3, ymm3, ymm11
	vpxor ymm10, ymm10, ymm3
	vpxor ymm3, ymm8, ymm3
	vpor ymm3, ymm4, ymm3
	vpxor ymm6, ymm1, ymm6
	vpxor ymm6, ymm3, ymm6
	vpand ymm8, ymm8, ymm0
	vpxor ymm8, ymm8, ymm6
	vpxor ymm12, ymm12, ymm10
	vpor ymm11, ymm2, ymm11
	vpxor ymm11, ymm12, ymm11
	vpxor ymm5, ymm5, ymm11
	vpand ymm5, ymm5, ymm0
	vpxor ymm5, ymm5, ymm10
	vpandn ymm2, ymm2, ymm12
	vpand ymm2, ymm6, ymm2
	vpxor ymm11, ymm9, ymm11
	vpxor ymm11, ymm2, ymm11
	vpor ymm0, ymm11, ymm0
	vpxor ymm10, ymm0, ymm10
	vmovdqa ymm0, ymm5
	vmovdqa ymm1, ymm8
	vmovdqa ymm2, ymm7
	vmovdqa ymm3, ymm10
	vmovdqu ymm14, YMMWORD PTR [r13+832]
	vpxor ymm0, ymm0, ymm14
	vmovdqu YMMWORD PTR [r13+832], ymm0
	vmovdqu ymm14, YMMWORD PTR [r13+384]
	vpxor ymm1, ymm1, ymm14
	vmovdqu YMMWORD PTR [r13+384], ymm1
	vmovdqu ymm14, YMMWORD PTR [r13+1280]
	vpxor ymm2, ymm2, ymm14
	vmovdqu YMMWORD PTR [r13+1280], ymm2
	vmovdqu ymm14, YMMWORD PTR [r13+960]
	vpxor ymm3, ymm3, ymm14
	vmovdqu YMMWORD PTR [r13+960], ymm3
	mov rbx, r12
	mov r12, r13
	mov r13, rbx
	sub r10, 1
	jne 223b
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vmovdqu YMMWORD PTR [rsi], ymm1
	vmovdqu YMMWORD PTR [rsi+32], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+256]
	vmovdqu ymm1, YMMWORD PTR [rsi+288]
	vmovdqu YMMWORD PTR [rsi+256], ymm1
	vmovdqu YMMWORD PTR [rsi+288], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+512]
	vmovdqu ymm1, YMMWORD PTR [rsi+544]
	vmovdqu YMMWORD PTR [rsi+512], ymm1
	vmovdqu YMMWORD PTR [rsi+544], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+768]
	vmovdqu ymm1, YMMWORD PTR [rsi+800]
	vmovdqu YMMWORD PTR [rsi+768], ymm1
	vmovdqu YMMWORD PTR [rsi+800], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1024]
	vmovdqu ymm1, YMMWORD PTR [rsi+1056]
	vmovdqu YMMWORD PTR [rsi+1024], ymm1
	vmovdqu YMMWORD PTR [rsi+1056], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1280]
	vmovdqu ymm1, YMMWORD PTR [rsi+1312]
	vmovdqu YMMWORD PTR [rsi+1280], ymm1
	vmovdqu YMMWORD PTR [rsi+1312], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1536]
	vmovdqu ymm1, YMMWORD PTR [rsi+1568]
	vmovdqu YMMWORD PTR [rsi+1536], ymm1
	vmovdqu YMMWORD PTR [rsi+1568], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1792]
	vmovdqu ymm1, YMMWORD PTR [rsi+1824]
	vmovdqu YMMWORD PTR [rsi+1792], ymm1
	vmovdqu YMMWORD PTR [rsi+1824], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+64]
	vmovdqu ymm1, YMMWORD PTR [rsi+96]
	vmovdqu YMMWORD PTR [rsi+64], ymm1
	vmovdqu YMMWORD PTR [rsi+96], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+320]
	vmovdqu ymm1, YMMWORD PTR [rsi+352]
	vmovdqu YMMWORD PTR [rsi+320], ymm1
	vmovdqu YMMWORD PTR [rsi+352], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+576]
	vmovdqu ymm1, YMMWORD PTR [rsi+608]
	vmovdqu YMMWORD PTR [rsi+576], ymm1
	vmovdqu YMMWORD PTR [rsi+608], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+832]
	vmovdqu ymm1, YMMWORD PTR [rsi+864]
	vmovdqu YMMWORD PTR [rsi+832], ymm1
	vmovdqu YMMWORD PTR [rsi+864], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1088]
	vmovdqu ymm1, YMMWORD PTR [rsi+1120]
	vmovdqu YMMWORD PTR [rsi+1088], ymm1
	vmovdqu YMMWORD PTR [rsi+1120], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1344]
	vmovdqu ymm1, YMMWORD PTR [rsi+1376]
	vmovdqu YMMWORD PTR [rsi+1344], ymm1
	vmovdqu YMMWORD PTR [rsi+1376], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1600]
	vmovdqu ymm1, YMMWORD PTR [rsi+1632]
	vmovdqu YMMWORD PTR [rsi+1600], ymm1
	vmovdqu YMMWORD PTR [rsi+1632], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1856]
	vmovdqu ymm1, YMMWORD PTR [rsi+1888]
	vmovdqu YMMWORD PTR [rsi+1856], ymm1
	vmovdqu YMMWORD PTR [rsi+1888], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+128]
	vmovdqu ymm1, YMMWORD PTR [rsi+160]
	vmovdqu YMMWORD PTR [rsi+128], ymm1
	vmovdqu YMMWORD PTR [rsi+160], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+384]
	vmovdqu ymm1, YMMWORD PTR [rsi+416]
	vmovdqu YMMWORD PTR [rsi+384], ymm1
	vmovdqu YMMWORD PTR [rsi+416], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+640]
	vmovdqu ymm1, YMMWORD PTR [rsi+672]
	vmovdqu YMMWORD PTR [rsi+640], ymm1
	vmovdqu YMMWORD PTR [rsi+672], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+896]
	vmovdqu ymm1, YMMWORD PTR [rsi+928]
	vmovdqu YMMWORD PTR [rsi+896], ymm1
	vmovdqu YMMWORD PTR [rsi+928], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1152]
	vmovdqu ymm1, YMMWORD PTR [rsi+1184]
	vmovdqu YMMWORD PTR [rsi+1152], ymm1
	vmovdqu YMMWORD PTR [rsi+1184], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1408]
	vmovdqu ymm1, YMMWORD PTR [rsi+1440]
	vmovdqu YMMWORD PTR [rsi+1408], ymm1
	vmovdqu YMMWORD PTR [rsi+1440], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1664]
	vmovdqu ymm1, YMMWORD PTR [rsi+1696]
	vmovdqu YMMWORD PTR [rsi+1664], ymm1
	vmovdqu YMMWORD PTR [rsi+1696], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1920]
	vmovdqu ymm1, YMMWORD PTR [rsi+1952]
	vmovdqu YMMWORD PTR [rsi+1920], ymm1
	vmovdqu YMMWORD PTR [rsi+1952], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+192]
	vmovdqu ymm1, YMMWORD PTR [rsi+224]
	vmovdqu YMMWORD PTR [rsi+192], ymm1
	vmovdqu YMMWORD PTR [rsi+224], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+448]
	vmovdqu ymm1, YMMWORD PTR [rsi+480]
	vmovdqu YMMWORD PTR [rsi+448], ymm1
	vmovdqu YMMWORD PTR [rsi+480], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+704]
	vmovdqu ymm1, YMMWORD PTR [rsi+736]
	vmovdqu YMMWORD PTR [rsi+704], ymm1
	vmovdqu YMMWORD PTR [rsi+736], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+960]
	vmovdqu ymm1, YMMWORD PTR [rsi+992]
	vmovdqu YMMWORD PTR [rsi+960], ymm1
	vmovdqu YMMWORD PTR [rsi+992], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1216]
	vmovdqu ymm1, YMMWORD PTR [rsi+1248]
	vmovdqu YMMWORD PTR [rsi+1216], ymm1
	vmovdqu YMMWORD PTR [rsi+1248], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1472]
	vmovdqu ymm1, YMMWORD PTR [rsi+1504]
	vmovdqu YMMWORD PTR [rsi+1472], ymm1
	vmovdqu YMMWORD PTR [rsi+1504], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1728]
	vmovdqu ymm1, YMMWORD PTR [rsi+1760]
	vmovdqu YMMWORD PTR [rsi+1728], ymm1
	vmovdqu YMMWORD PTR [rsi+1760], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1984]
	vmovdqu ymm1, YMMWORD PTR [rsi+2016]
	vmovdqu YMMWORD PTR [rsi+1984], ymm1
	vmovdqu YMMWORD PTR [rsi+2016], ymm0
	sub r11, 1
	jne 218b
	mov r11, 8
224:
	movabs rbx, 4294967295
	vmovq xmm13, rbx
	vpbroadcastq ymm13, xmm13
	movabs rbx, 281470681808895
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	movabs rbx, 71777214294589695
	vmovq xmm15, rbx
	vpbroadcastq ymm15, xmm15
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vmovdqu ymm1, YMMWORD PTR [rsi+256]
	vmovdqu ymm2, YMMWORD PTR [rsi+512]
	vmovdqu ymm3, YMMWORD PTR [rsi+768]
	vmovdqu ymm4, YMMWORD PTR [rsi+1024]
	vmovdqu ymm5, YMMWORD PTR [rsi+1280]
	vmovdqu ymm6, YMMWORD PTR [rsi+1536]
	vmovdqu ymm7, YMMWORD PTR [rsi+1792]
	vpsrlq ymm8, ymm0, 32
	vpxor ymm8, ymm8, ymm4
	vpand ymm8, ymm8, ymm13
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm8, ymm8, 32
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm1, 32
	vpxor ymm8, ymm8, ymm5
	vpand ymm8, ymm8, ymm13
	vpxor ymm5, ymm5, ymm8
	vpsllq ymm8, ymm8, 32
	vpxor ymm1, ymm1, ymm8
	vpsrlq ymm8, ymm2, 32
	vpxor ymm8, ymm8, ymm6
	vpand ymm8, ymm8, ymm13
	vpxor ymm6, ymm6, ymm8
	vpsllq ymm8, ymm8, 32
	vpxor ymm2, ymm2, ymm8
	vpsrlq ymm8, ymm3, 32
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm13
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 32
	vpxor ymm3, ymm3, ymm8
	vpsrlq ymm8, ymm0, 16
	vpxor ymm8, ymm8, ymm2
	vpand ymm8, ymm8, ymm14
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm8, ymm8, 16
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm1, 16
	vpxor ymm8, ymm8, ymm3
	vpand ymm8, ymm8, ymm14
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm8, ymm8, 16
	vpxor ymm1, ymm1, ymm8
	vpsrlq ymm8, ymm4, 16
	vpxor ymm8, ymm8, ymm6
	vpand ymm8, ymm8, ymm14
	vpxor ymm6, ymm6, ymm8
	vpsllq ymm8, ymm8, 16
	vpxor ymm4, ymm4, ymm8
	vpsrlq ymm8, ymm5, 16
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm14
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 16
	vpxor ymm5, ymm5, ymm8
	vpsrlq ymm8, ymm0, 8
	vpxor ymm8, ymm8, ymm1
	vpand ymm8, ymm8, ymm15
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm8, ymm8, 8
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm2, 8
	vpxor ymm8, ymm8, ymm3
	vpand ymm8, ymm8, ymm15
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm8, ymm8, 8
	vpxor ymm2, ymm2, ymm8
	vpsrlq ymm8, ymm4, 8
	vpxor ymm8, ymm8, ymm5
	vpand ymm8, ymm8, ymm15
	vpxor ymm5, ymm5, ymm8
	vpsllq ymm8, ymm8, 8
	vpxor ymm4, ymm4, ymm8
	vpsrlq ymm8, ymm6, 8
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm15
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 8
	vpxor ymm6, ymm6, ymm8
	vmovdqu YMMWORD PTR [rsi], ymm0
	vmovdqu YMMWORD PTR [rsi+256], ymm1
	vmovdqu YMMWORD PTR [rsi+512], ymm2
	vmovdqu YMMWORD PTR [rsi+768], ymm3
	vmovdqu YMMWORD PTR [rsi+1024], ymm4
	vmovdqu YMMWORD PTR [rsi+1280], ymm5
	vmovdqu YMMWORD PTR [rsi+1536], ymm6
	vmovdqu YMMWORD PTR [rsi+1792], ymm7
	add rsi, 32
	sub r11, 1
	jne 224b
	sub rsi, 256
	mov r11, 8
225:
	movabs rbx, 1085102592571150095
	vmovq xmm13, rbx
	vpbroadcastq ymm13, xmm13
	movabs rbx, 3689348814741910323
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	movabs rbx, 6148914691236517205
	vmovq xmm15, rbx
	vpbroadcastq ymm15, xmm15
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vmovdqu ymm2, YMMWORD PTR [rsi+64]
	vmovdqu ymm3, YMMWORD PTR [rsi+96]
	vmovdqu ymm4, YMMWORD PTR [rsi+128]
	vmovdqu ymm5, YMMWORD PTR [rsi+160]
	vmovdqu ymm6, YMMWORD PTR [rsi+192]
	vmovdqu ymm7, YMMWORD PTR [rsi+224]
	vpsrlq ymm8, ymm0, 4
	vpxor ymm8, ymm8, ymm4
	vpand ymm8, ymm8, ymm13
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm8, ymm8, 4
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm1, 4
	vpxor ymm8, ymm8, ymm5
	vpand ymm8, ymm8, ymm13
	vpxor ymm5, ymm5, ymm8
	vpsllq ymm8, ymm8, 4
	vpxor ymm1, ymm1, ymm8
	vpsrlq ymm8, ymm2, 4
	vpxor ymm8, ymm8, ymm6
	vpand ymm8, ymm8, ymm13
	vpxor ymm6, ymm6, ymm8
	vpsllq ymm8, ymm8, 4
	vpxor ymm2, ymm2, ymm8
	vpsrlq ymm8, ymm3, 4
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm13
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 4
	vpxor ymm3, ymm3, ymm8
	vpsrlq ymm8, ymm0, 2
	vpxor ymm8, ymm8, ymm2
	vpand ymm8, ymm8, ymm14
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm8, ymm8, 2
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm1, 2
	vpxor ymm8, ymm8, ymm3
	vpand ymm8, ymm8, ymm14
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm8, ymm8, 2
	vpxor ymm1, ymm1, ymm8
	vpsrlq ymm8, ymm4, 2
	vpxor ymm8, ymm8, ymm6
	vpand ymm8, ymm8, ymm14
	vpxor ymm6, ymm6, ymm8
	vpsllq ymm8, ymm8, 2
	vpxor ymm4, ymm4, ymm8
	vpsrlq ymm8, ymm5, 2
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm14
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 2
	vpxor ymm5, ymm5, ymm8
	vpsrlq ymm8, ymm0, 1
	vpxor ymm8, ymm8, ymm1
	vpand ymm8, ymm8, ymm15
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm8, ymm8, 1
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm2, 1
	vpxor ymm8, ymm8, ymm3
	vpand ymm8, ymm8, ymm15
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm8, ymm8, 1
	vpxor ymm2, ymm2, ymm8
	vpsrlq ymm8, ymm4, 1
	vpxor ymm8, ymm8, ymm5
	vpand ymm8, ymm8, ymm15
	vpxor ymm5, ymm5, ymm8
	vpsllq ymm8, ymm8, 1
	vpxor ymm4, ymm4, ymm8
	vpsrlq ymm8, ymm6, 1
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm15
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 1
	vpxor ymm6, ymm6, ymm8
	vmovdqu YMMWORD PTR [rsi], ymm0
	vmovdqu YMMWORD PTR [rsi+32], ymm1
	vmovdqu YMMWORD PTR [rsi+64], ymm2
	vmovdqu YMMWORD PTR [rsi+96], ymm3
	vmovdqu YMMWORD PTR [rsi+128], ymm4
	vmovdqu YMMWORD PTR [rsi+160], ymm5
	vmovdqu YMMWORD PTR [rsi+192], ymm6
	vmovdqu YMMWORD PTR [rsi+224], ymm7
	add rsi, 256
	sub r11, 1
	jne 225b
	sub rsi, 2048
	add rsi, 2048
	sub rdx, 256
	cmp rdx, 256
	jae 215b
	mov rbx, QWORD PTR [rcx+1016]
	mov r12, QWORD PTR [rcx+1008]
	mov r13, QWORD PTR [rcx+1000]
	vzeroupper
	jmp 214f
213:
214:
	call {vg_triple_des_ecb_encrypt_core}
	mov r11d, 0
	mov QWORD PTR [rsp+8], r11
	mov QWORD PTR [rsp+16], r11
	mov QWORD PTR [rsp+24], r11
	mov QWORD PTR [rsp+32], r11
	mov QWORD PTR [rsp+40], r11
	mov QWORD PTR [rsp+48], r11
	mov QWORD PTR [rsp+56], r11
	mov QWORD PTR [rsp+64], r11
	mov QWORD PTR [rsp+72], r11
	mov QWORD PTR [rsp+80], r11
	mov QWORD PTR [rsp+88], r11
	mov QWORD PTR [rsp+96], r11
	mov QWORD PTR [rsp+104], r11
	mov QWORD PTR [rsp+112], r11
	mov QWORD PTR [rsp+120], r11
	mov QWORD PTR [rsp+128], r11
	mov QWORD PTR [rsp+136], r11
	mov QWORD PTR [rsp+144], r11
	mov QWORD PTR [rsp+152], r11
	mov QWORD PTR [rsp+160], r11
	mov QWORD PTR [rsp+168], r11
	mov QWORD PTR [rsp+176], r11
	mov QWORD PTR [rsp+184], r11
	mov QWORD PTR [rsp+192], r11
	mov QWORD PTR [rsp+200], r11
	mov QWORD PTR [rsp+208], r11
	mov QWORD PTR [rsp+216], r11
	mov QWORD PTR [rsp+224], r11
	mov QWORD PTR [rsp+232], r11
	mov QWORD PTR [rsp+240], r11
	mov QWORD PTR [rsp+248], r11
	mov QWORD PTR [rsp+256], r11
	mov QWORD PTR [rsp+264], r11
	mov QWORD PTR [rsp+272], r11
	mov QWORD PTR [rsp+280], r11
	mov QWORD PTR [rsp+288], r11
	mov QWORD PTR [rsp+296], r11
	mov QWORD PTR [rsp+304], r11
	mov QWORD PTR [rsp+312], r11
	mov QWORD PTR [rsp+320], r11
	mov QWORD PTR [rsp+328], r11
	mov QWORD PTR [rsp+336], r11
	mov QWORD PTR [rsp+344], r11
	mov QWORD PTR [rsp+352], r11
	mov QWORD PTR [rsp+360], r11
	mov QWORD PTR [rsp+368], r11
	mov QWORD PTR [rsp+376], r11
	mov QWORD PTR [rsp+384], r11
	mov QWORD PTR [rsp+392], r11
	mov QWORD PTR [rsp+400], r11
	mov QWORD PTR [rsp+408], r11
	mov QWORD PTR [rsp+416], r11
	mov QWORD PTR [rsp+424], r11
	mov QWORD PTR [rsp+432], r11
	mov QWORD PTR [rsp+440], r11
	mov QWORD PTR [rsp+448], r11
	mov QWORD PTR [rsp+456], r11
	mov QWORD PTR [rsp+464], r11
	mov QWORD PTR [rsp+472], r11
	mov QWORD PTR [rsp+480], r11
	mov QWORD PTR [rsp+488], r11
	mov QWORD PTR [rsp+496], r11
	mov QWORD PTR [rsp+504], r11
	mov QWORD PTR [rsp+512], r11
	mov QWORD PTR [rsp+520], r11
	mov QWORD PTR [rsp+528], r11
	mov QWORD PTR [rsp+536], r11
	mov QWORD PTR [rsp+544], r11
	mov QWORD PTR [rsp+552], r11
	mov QWORD PTR [rsp+560], r11
	mov QWORD PTR [rsp+568], r11
	mov QWORD PTR [rsp+576], r11
	mov QWORD PTR [rsp+584], r11
	mov QWORD PTR [rsp+592], r11
	mov QWORD PTR [rsp+600], r11
	mov QWORD PTR [rsp+608], r11
	mov QWORD PTR [rsp+616], r11
	mov QWORD PTR [rsp+624], r11
	mov QWORD PTR [rsp+632], r11
	mov QWORD PTR [rsp+640], r11
	mov QWORD PTR [rsp+648], r11
	mov QWORD PTR [rsp+656], r11
	mov QWORD PTR [rsp+664], r11
	mov QWORD PTR [rsp+672], r11
	mov QWORD PTR [rsp+680], r11
	mov QWORD PTR [rsp+688], r11
	mov QWORD PTR [rsp+696], r11
	mov QWORD PTR [rsp+704], r11
	mov QWORD PTR [rsp+712], r11
	mov QWORD PTR [rsp+720], r11
	mov QWORD PTR [rsp+728], r11
	mov QWORD PTR [rsp+736], r11
	mov QWORD PTR [rsp+744], r11
	mov QWORD PTR [rsp+752], r11
	mov QWORD PTR [rsp+760], r11
	mov QWORD PTR [rsp+768], r11
	mov QWORD PTR [rsp+776], r11
	mov QWORD PTR [rsp+784], r11
	mov QWORD PTR [rsp+792], r11
	mov QWORD PTR [rsp+800], r11
	mov QWORD PTR [rsp+808], r11
	mov QWORD PTR [rsp+816], r11
	mov QWORD PTR [rsp+824], r11
	mov QWORD PTR [rsp+832], r11
	mov QWORD PTR [rsp+840], r11
	mov QWORD PTR [rsp+848], r11
	mov QWORD PTR [rsp+856], r11
	mov QWORD PTR [rsp+864], r11
	mov QWORD PTR [rsp+872], r11
	mov QWORD PTR [rsp+880], r11
	mov QWORD PTR [rsp+888], r11
	mov QWORD PTR [rsp+896], r11
	mov QWORD PTR [rsp+904], r11
	mov QWORD PTR [rsp+912], r11
	mov QWORD PTR [rsp+920], r11
	mov QWORD PTR [rsp+928], r11
	mov QWORD PTR [rsp+936], r11
	mov QWORD PTR [rsp+944], r11
	mov QWORD PTR [rsp+952], r11
	mov QWORD PTR [rsp+960], r11
	mov QWORD PTR [rsp+968], r11
	mov QWORD PTR [rsp+976], r11
	mov QWORD PTR [rsp+984], r11
	mov QWORD PTR [rsp+992], r11
	mov QWORD PTR [rsp+1000], r11
	mov QWORD PTR [rsp+1008], r11
	mov QWORD PTR [rsp+1016], r11
	mov QWORD PTR [rsp+1024], r11
	lea rsp, [rsp+1032]
	ret
	.p2align 6

vg_triple_des_ecb_decrypt_avx512:
	lea rsp, [rsp-1032]
	mov rcx, rsp
	add rcx, 8
	cmp rdx, 512
	jb 20f
	mov QWORD PTR [rcx+1016], rbx
	mov QWORD PTR [rcx+1008], r12
	mov QWORD PTR [rcx+1000], r13
22:
	mov r11, 8
23:
	movabs rbx, 4294967295
	vmovq xmm13, rbx
	vpbroadcastq zmm13, xmm13
	movabs rbx, 281470681808895
	vmovq xmm14, rbx
	vpbroadcastq zmm14, xmm14
	movabs rbx, 71777214294589695
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm0, ZMMWORD PTR [rsi]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+512]
	vmovdqu32 zmm2, ZMMWORD PTR [rsi+1024]
	vmovdqu32 zmm3, ZMMWORD PTR [rsi+1536]
	vmovdqu32 zmm4, ZMMWORD PTR [rsi+2048]
	vmovdqu32 zmm5, ZMMWORD PTR [rsi+2560]
	vmovdqu32 zmm6, ZMMWORD PTR [rsi+3072]
	vmovdqu32 zmm7, ZMMWORD PTR [rsi+3584]
	vpsrlq zmm8, zmm0, 32
	vpxord zmm8, zmm8, zmm4
	vpandq zmm8, zmm8, zmm13
	vpxord zmm4, zmm4, zmm8
	vpsllq zmm8, zmm8, 32
	vpxord zmm0, zmm0, zmm8
	vpsrlq zmm8, zmm1, 32
	vpxord zmm8, zmm8, zmm5
	vpandq zmm8, zmm8, zmm13
	vpxord zmm5, zmm5, zmm8
	vpsllq zmm8, zmm8, 32
	vpxord zmm1, zmm1, zmm8
	vpsrlq zmm8, zmm2, 32
	vpxord zmm8, zmm8, zmm6
	vpandq zmm8, zmm8, zmm13
	vpxord zmm6, zmm6, zmm8
	vpsllq zmm8, zmm8, 32
	vpxord zmm2, zmm2, zmm8
	vpsrlq zmm8, zmm3, 32
	vpxord zmm8, zmm8, zmm7
	vpandq zmm8, zmm8, zmm13
	vpxord zmm7, zmm7, zmm8
	vpsllq zmm8, zmm8, 32
	vpxord zmm3, zmm3, zmm8
	vpsrlq zmm8, zmm0, 16
	vpxord zmm8, zmm8, zmm2
	vpandq zmm8, zmm8, zmm14
	vpxord zmm2, zmm2, zmm8
	vpsllq zmm8, zmm8, 16
	vpxord zmm0, zmm0, zmm8
	vpsrlq zmm8, zmm1, 16
	vpxord zmm8, zmm8, zmm3
	vpandq zmm8, zmm8, zmm14
	vpxord zmm3, zmm3, zmm8
	vpsllq zmm8, zmm8, 16
	vpxord zmm1, zmm1, zmm8
	vpsrlq zmm8, zmm4, 16
	vpxord zmm8, zmm8, zmm6
	vpandq zmm8, zmm8, zmm14
	vpxord zmm6, zmm6, zmm8
	vpsllq zmm8, zmm8, 16
	vpxord zmm4, zmm4, zmm8
	vpsrlq zmm8, zmm5, 16
	vpxord zmm8, zmm8, zmm7
	vpandq zmm8, zmm8, zmm14
	vpxord zmm7, zmm7, zmm8
	vpsllq zmm8, zmm8, 16
	vpxord zmm5, zmm5, zmm8
	vpsrlq zmm8, zmm0, 8
	vpxord zmm8, zmm8, zmm1
	vpandq zmm8, zmm8, zmm15
	vpxord zmm1, zmm1, zmm8
	vpsllq zmm8, zmm8, 8
	vpxord zmm0, zmm0, zmm8
	vpsrlq zmm8, zmm2, 8
	vpxord zmm8, zmm8, zmm3
	vpandq zmm8, zmm8, zmm15
	vpxord zmm3, zmm3, zmm8
	vpsllq zmm8, zmm8, 8
	vpxord zmm2, zmm2, zmm8
	vpsrlq zmm8, zmm4, 8
	vpxord zmm8, zmm8, zmm5
	vpandq zmm8, zmm8, zmm15
	vpxord zmm5, zmm5, zmm8
	vpsllq zmm8, zmm8, 8
	vpxord zmm4, zmm4, zmm8
	vpsrlq zmm8, zmm6, 8
	vpxord zmm8, zmm8, zmm7
	vpandq zmm8, zmm8, zmm15
	vpxord zmm7, zmm7, zmm8
	vpsllq zmm8, zmm8, 8
	vpxord zmm6, zmm6, zmm8
	vmovdqu32 ZMMWORD PTR [rsi], zmm0
	vmovdqu32 ZMMWORD PTR [rsi+512], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+1024], zmm2
	vmovdqu32 ZMMWORD PTR [rsi+1536], zmm3
	vmovdqu32 ZMMWORD PTR [rsi+2048], zmm4
	vmovdqu32 ZMMWORD PTR [rsi+2560], zmm5
	vmovdqu32 ZMMWORD PTR [rsi+3072], zmm6
	vmovdqu32 ZMMWORD PTR [rsi+3584], zmm7
	add rsi, 64
	sub r11, 1
	jne 23b
	sub rsi, 512
	mov r11, 8
24:
	movabs rbx, 1085102592571150095
	vmovq xmm13, rbx
	vpbroadcastq zmm13, xmm13
	movabs rbx, 3689348814741910323
	vmovq xmm14, rbx
	vpbroadcastq zmm14, xmm14
	movabs rbx, 6148914691236517205
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm0, ZMMWORD PTR [rsi]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+64]
	vmovdqu32 zmm2, ZMMWORD PTR [rsi+128]
	vmovdqu32 zmm3, ZMMWORD PTR [rsi+192]
	vmovdqu32 zmm4, ZMMWORD PTR [rsi+256]
	vmovdqu32 zmm5, ZMMWORD PTR [rsi+320]
	vmovdqu32 zmm6, ZMMWORD PTR [rsi+384]
	vmovdqu32 zmm7, ZMMWORD PTR [rsi+448]
	vpsrlq zmm8, zmm0, 4
	vpxord zmm8, zmm8, zmm4
	vpandq zmm8, zmm8, zmm13
	vpxord zmm4, zmm4, zmm8
	vpsllq zmm8, zmm8, 4
	vpxord zmm0, zmm0, zmm8
	vpsrlq zmm8, zmm1, 4
	vpxord zmm8, zmm8, zmm5
	vpandq zmm8, zmm8, zmm13
	vpxord zmm5, zmm5, zmm8
	vpsllq zmm8, zmm8, 4
	vpxord zmm1, zmm1, zmm8
	vpsrlq zmm8, zmm2, 4
	vpxord zmm8, zmm8, zmm6
	vpandq zmm8, zmm8, zmm13
	vpxord zmm6, zmm6, zmm8
	vpsllq zmm8, zmm8, 4
	vpxord zmm2, zmm2, zmm8
	vpsrlq zmm8, zmm3, 4
	vpxord zmm8, zmm8, zmm7
	vpandq zmm8, zmm8, zmm13
	vpxord zmm7, zmm7, zmm8
	vpsllq zmm8, zmm8, 4
	vpxord zmm3, zmm3, zmm8
	vpsrlq zmm8, zmm0, 2
	vpxord zmm8, zmm8, zmm2
	vpandq zmm8, zmm8, zmm14
	vpxord zmm2, zmm2, zmm8
	vpsllq zmm8, zmm8, 2
	vpxord zmm0, zmm0, zmm8
	vpsrlq zmm8, zmm1, 2
	vpxord zmm8, zmm8, zmm3
	vpandq zmm8, zmm8, zmm14
	vpxord zmm3, zmm3, zmm8
	vpsllq zmm8, zmm8, 2
	vpxord zmm1, zmm1, zmm8
	vpsrlq zmm8, zmm4, 2
	vpxord zmm8, zmm8, zmm6
	vpandq zmm8, zmm8, zmm14
	vpxord zmm6, zmm6, zmm8
	vpsllq zmm8, zmm8, 2
	vpxord zmm4, zmm4, zmm8
	vpsrlq zmm8, zmm5, 2
	vpxord zmm8, zmm8, zmm7
	vpandq zmm8, zmm8, zmm14
	vpxord zmm7, zmm7, zmm8
	vpsllq zmm8, zmm8, 2
	vpxord zmm5, zmm5, zmm8
	vpsrlq zmm8, zmm0, 1
	vpxord zmm8, zmm8, zmm1
	vpandq zmm8, zmm8, zmm15
	vpxord zmm1, zmm1, zmm8
	vpsllq zmm8, zmm8, 1
	vpxord zmm0, zmm0, zmm8
	vpsrlq zmm8, zmm2, 1
	vpxord zmm8, zmm8, zmm3
	vpandq zmm8, zmm8, zmm15
	vpxord zmm3, zmm3, zmm8
	vpsllq zmm8, zmm8, 1
	vpxord zmm2, zmm2, zmm8
	vpsrlq zmm8, zmm4, 1
	vpxord zmm8, zmm8, zmm5
	vpandq zmm8, zmm8, zmm15
	vpxord zmm5, zmm5, zmm8
	vpsllq zmm8, zmm8, 1
	vpxord zmm4, zmm4, zmm8
	vpsrlq zmm8, zmm6, 1
	vpxord zmm8, zmm8, zmm7
	vpandq zmm8, zmm8, zmm15
	vpxord zmm7, zmm7, zmm8
	vpsllq zmm8, zmm8, 1
	vpxord zmm6, zmm6, zmm8
	vmovdqu32 ZMMWORD PTR [rsi], zmm0
	vmovdqu32 ZMMWORD PTR [rsi+64], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+128], zmm2
	vmovdqu32 ZMMWORD PTR [rsi+192], zmm3
	vmovdqu32 ZMMWORD PTR [rsi+256], zmm4
	vmovdqu32 ZMMWORD PTR [rsi+320], zmm5
	vmovdqu32 ZMMWORD PTR [rsi+384], zmm6
	vmovdqu32 ZMMWORD PTR [rsi+448], zmm7
	add rsi, 512
	sub r11, 1
	jne 24b
	sub rsi, 4096
	mov r11, 3
25:
	cmp r11, 3
	je 26f
	cmp r11, 2
	je 28f
	mov r8, rdi
	add r8, 120
	mov r9, -8
	jmp 29f
28:
	mov r8, rdi
	add r8, 128
	mov r9, 8
29:
	jmp 27f
26:
	mov r8, rdi
	add r8, 376
	mov r9, -8
27:
	mov r10, 16
	mov r12, rsi
	add r12, 64
	mov r13, rsi
210:
	mov rax, QWORD PTR [r8]
	add r8, r9
	ror rax, 48
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm5, ZMMWORD PTR [r12]
	vpxord zmm5, zmm5, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm4, ZMMWORD PTR [r12+3968]
	vpxord zmm4, zmm4, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm3, ZMMWORD PTR [r12+3456]
	vpxord zmm3, zmm3, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm2, ZMMWORD PTR [r12+2944]
	vpxord zmm2, zmm2, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm1, ZMMWORD PTR [r12+2432]
	vpxord zmm1, zmm1, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm0, ZMMWORD PTR [r12+1920]
	vpxord zmm0, zmm0, zmm15
	vpandnq zmm6, zmm1, zmm5
	vpxord zmm7, zmm2, zmm6
	vporq zmm8, zmm3, zmm0
	vpxord zmm9, zmm5, zmm3
	vpandq zmm10, zmm8, zmm9
	vpxord zmm11, zmm2, zmm10
	vpandnq zmm12, zmm7, zmm11
	vpxord zmm13, zmm1, zmm0
	vmovdqa64 zmm14, zmm7
	vpternlogd zmm14, zmm3, zmm13, 144
	vpternlogd zmm14, zmm0, zmm10, 30
	vpandnq zmm10, zmm12, zmm14
	vporq zmm0, zmm5, zmm0
	vporq zmm15, zmm14, zmm0
	vpandnq zmm11, zmm11, zmm1
	vpternlogd zmm2, zmm11, zmm0, 156
	vpternlogd zmm2, zmm13, zmm9, 244
	vpandnq zmm6, zmm6, zmm3
	vpternlogd zmm6, zmm7, zmm15, 6
	vpternlogd zmm14, zmm6, zmm8, 147
	vmovdqa64 zmm3, zmm4
	vpternlogd zmm3, zmm15, zmm11, 6
	vpxord zmm3, zmm3, zmm14
	vpternlogd zmm11, zmm13, zmm6, 246
	vpternlogd zmm5, zmm8, zmm11, 150
	vpxord zmm14, zmm14, zmm5
	vpternlogd zmm12, zmm14, zmm4, 54
	vpternlogd zmm8, zmm2, zmm15, 222
	vpxord zmm8, zmm5, zmm8
	vpternlogd zmm13, zmm8, zmm14, 54
	vpternlogd zmm13, zmm10, zmm4, 30
	vpternlogd zmm8, zmm1, zmm7, 14
	vpternlogd zmm8, zmm10, zmm5, 120
	vpternlogd zmm2, zmm8, zmm4, 30
	vmovdqa64 zmm0, zmm2
	vmovdqa64 zmm1, zmm3
	vmovdqa64 zmm2, zmm13
	vmovdqa64 zmm3, zmm12
	vmovdqu32 zmm15, ZMMWORD PTR [r13+512]
	vpxord zmm0, zmm0, zmm15
	vmovdqu32 ZMMWORD PTR [r13+512], zmm0
	vmovdqu32 zmm15, ZMMWORD PTR [r13+640]
	vpxord zmm1, zmm1, zmm15
	vmovdqu32 ZMMWORD PTR [r13+640], zmm1
	vmovdqu32 zmm15, ZMMWORD PTR [r13+3712]
	vpxord zmm2, zmm2, zmm15
	vmovdqu32 ZMMWORD PTR [r13+3712], zmm2
	vmovdqu32 zmm15, ZMMWORD PTR [r13+3840]
	vpxord zmm3, zmm3, zmm15
	vmovdqu32 ZMMWORD PTR [r13+3840], zmm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm5, ZMMWORD PTR [r12+2432]
	vpxord zmm5, zmm5, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm4, ZMMWORD PTR [r12+1920]
	vpxord zmm4, zmm4, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm3, ZMMWORD PTR [r12+1408]
	vpxord zmm3, zmm3, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm2, ZMMWORD PTR [r12+896]
	vpxord zmm2, zmm2, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm1, ZMMWORD PTR [r12+384]
	vpxord zmm1, zmm1, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm0, ZMMWORD PTR [r12+3840]
	vpxord zmm0, zmm0, zmm15
	vpxord zmm6, zmm4, zmm1
	vmovdqa64 zmm7, zmm1
	vpternlogd zmm7, zmm5, zmm0, 176
	vporq zmm8, zmm4, zmm7
	vpandnq zmm9, zmm0, zmm6
	vpternlogd zmm1, zmm5, zmm6, 120
	vpandq zmm10, zmm3, zmm0
	vpternlogd zmm7, zmm8, zmm9, 72
	vpandq zmm11, zmm3, zmm7
	vpternlogd zmm5, zmm11, zmm11, 195
	vpxord zmm0, zmm0, zmm6
	vpandnq zmm12, zmm10, zmm0
	vpxord zmm13, zmm5, zmm12
	vmovdqa64 zmm14, zmm2
	vpternlogd zmm14, zmm7, zmm10, 176
	vpxord zmm14, zmm14, zmm13
	vpandnq zmm12, zmm12, zmm4
	vpxord zmm4, zmm1, zmm12
	vpxord zmm3, zmm3, zmm0
	vpternlogd zmm5, zmm3, zmm4, 156
	vmovdqa64 zmm15, zmm5
	vpternlogd zmm15, zmm8, zmm2, 180
	vpternlogd zmm3, zmm11, zmm12, 246
	vpxord zmm8, zmm8, zmm13
	vporq zmm10, zmm10, zmm8
	vpxord zmm12, zmm3, zmm10
	vpternlogd zmm5, zmm7, zmm13, 150
	vpandq zmm3, zmm6, zmm3
	vpternlogd zmm3, zmm10, zmm5, 120
	vpternlogd zmm12, zmm3, zmm2, 30
	vporq zmm8, zmm0, zmm8
	vpternlogd zmm8, zmm3, zmm4, 180
	vpternlogd zmm2, zmm1, zmm9, 244
	vpxord zmm8, zmm2, zmm8
	vmovdqa64 zmm0, zmm8
	vmovdqa64 zmm1, zmm12
	vmovdqa64 zmm2, zmm14
	vmovdqa64 zmm3, zmm15
	vmovdqu32 zmm15, ZMMWORD PTR [r13+3200]
	vpxord zmm0, zmm0, zmm15
	vmovdqu32 ZMMWORD PTR [r13+3200], zmm0
	vmovdqu32 zmm15, ZMMWORD PTR [r13+3456]
	vpxord zmm1, zmm1, zmm15
	vmovdqu32 ZMMWORD PTR [r13+3456], zmm1
	vmovdqu32 zmm15, ZMMWORD PTR [r13+2048]
	vpxord zmm2, zmm2, zmm15
	vmovdqu32 ZMMWORD PTR [r13+2048], zmm2
	vmovdqu32 zmm15, ZMMWORD PTR [r13+1792]
	vpxord zmm3, zmm3, zmm15
	vmovdqu32 ZMMWORD PTR [r13+1792], zmm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm5, ZMMWORD PTR [r12+384]
	vpxord zmm5, zmm5, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm4, ZMMWORD PTR [r12+3840]
	vpxord zmm4, zmm4, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm3, ZMMWORD PTR [r12+3328]
	vpxord zmm3, zmm3, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm2, ZMMWORD PTR [r12+2816]
	vpxord zmm2, zmm2, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm1, ZMMWORD PTR [r12+2304]
	vpxord zmm1, zmm1, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm0, ZMMWORD PTR [r12+1792]
	vpxord zmm0, zmm0, zmm15
	vpandnq zmm6, zmm4, zmm5
	vpxord zmm7, zmm3, zmm0
	vporq zmm8, zmm6, zmm7
	vpxord zmm9, zmm2, zmm0
	vpandnq zmm10, zmm5, zmm9
	vpxord zmm11, zmm8, zmm10
	vpxord zmm12, zmm4, zmm7
	vpternlogd zmm8, zmm12, zmm0, 180
	vmovdqa64 zmm13, zmm2
	vpternlogd zmm13, zmm0, zmm11, 248
	vpternlogd zmm13, zmm12, zmm5, 108
	vmovdqa64 zmm14, zmm13
	vpternlogd zmm14, zmm11, zmm1, 180
	vpxord zmm15, zmm5, zmm2
	vmovdqu32 ZMMWORD PTR [rcx], zmm14
	vmovdqa64 zmm14, zmm3
	vpternlogd zmm14, zmm8, zmm15, 246
	vpternlogd zmm14, zmm7, zmm9, 112
	vporq zmm15, zmm10, zmm15
	vpandq zmm0, zmm2, zmm0
	vpandnq zmm10, zmm4, zmm0
	vpternlogd zmm10, zmm13, zmm15, 180
	vpandq zmm9, zmm8, zmm10
	vpternlogd zmm9, zmm12, zmm0, 14
	vpxord zmm9, zmm5, zmm9
	vpternlogd zmm14, zmm9, zmm1, 108
	vmovdqa64 zmm5, zmm11
	vpternlogd zmm5, zmm11, zmm11, 15
	vpternlogd zmm3, zmm4, zmm5, 254
	vpxord zmm3, zmm12, zmm3
	vpternlogd zmm11, zmm1, zmm8, 140
	vpternlogd zmm11, zmm15, zmm3, 150
	vpternlogd zmm13, zmm2, zmm5, 120
	vpxord zmm9, zmm6, zmm9
	vpternlogd zmm9, zmm3, zmm13, 30
	vpternlogd zmm9, zmm10, zmm1, 30
	vmovdqu32 zmm0, ZMMWORD PTR [rcx]
	vmovdqa64 zmm1, zmm9
	vmovdqa64 zmm2, zmm14
	vmovdqa64 zmm3, zmm11
	vmovdqu32 zmm15, ZMMWORD PTR [r13+1408]
	vpxord zmm0, zmm0, zmm15
	vmovdqu32 ZMMWORD PTR [r13+1408], zmm0
	vmovdqu32 zmm15, ZMMWORD PTR [r13+1024]
	vpxord zmm1, zmm1, zmm15
	vmovdqu32 ZMMWORD PTR [r13+1024], zmm1
	vmovdqu32 zmm15, ZMMWORD PTR [r13+256]
	vpxord zmm2, zmm2, zmm15
	vmovdqu32 ZMMWORD PTR [r13+256], zmm2
	vmovdqu32 zmm15, ZMMWORD PTR [r13+128]
	vpxord zmm3, zmm3, zmm15
	vmovdqu32 ZMMWORD PTR [r13+128], zmm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm5, ZMMWORD PTR [r12+2304]
	vpxord zmm5, zmm5, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm4, ZMMWORD PTR [r12+1792]
	vpxord zmm4, zmm4, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm3, ZMMWORD PTR [r12+1280]
	vpxord zmm3, zmm3, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm2, ZMMWORD PTR [r12+768]
	vpxord zmm2, zmm2, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm1, ZMMWORD PTR [r12+256]
	vpxord zmm1, zmm1, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm0, ZMMWORD PTR [r12+3712]
	vpxord zmm0, zmm0, zmm15
	vpxord zmm5, zmm5, zmm3
	vpxord zmm3, zmm3, zmm1
	vmovdqa64 zmm6, zmm1
	vpternlogd zmm6, zmm4, zmm2, 30
	vpandnq zmm6, zmm6, zmm3
	vpandnq zmm7, zmm4, zmm3
	vpxord zmm8, zmm2, zmm7
	vmovdqa64 zmm9, zmm6
	vpternlogd zmm9, zmm5, zmm8, 14
	vpxord zmm10, zmm4, zmm9
	vpandq zmm8, zmm8, zmm10
	vpxord zmm5, zmm5, zmm10
	vpternlogd zmm3, zmm5, zmm8, 140
	vpxord zmm3, zmm6, zmm3
	vpxord zmm2, zmm4, zmm2
	vpternlogd zmm5, zmm1, zmm7, 30
	vpternlogd zmm9, zmm5, zmm2, 180
	vmovdqa64 zmm7, zmm9
	vpternlogd zmm7, zmm0, zmm3, 180
	vpternlogd zmm9, zmm9, zmm9, 15
	vmovdqa64 zmm1, zmm9
	vpternlogd zmm1, zmm3, zmm0, 180
	vpternlogd zmm2, zmm3, zmm9, 6
	vpternlogd zmm5, zmm8, zmm2, 30
	vmovdqa64 zmm2, zmm5
	vpternlogd zmm2, zmm10, zmm0, 30
	vpternlogd zmm5, zmm0, zmm10, 120
	vmovdqa64 zmm0, zmm5
	vmovdqu32 ZMMWORD PTR [rcx], zmm1
	vmovdqa64 zmm1, zmm2
	vmovdqu32 zmm2, ZMMWORD PTR [rcx]
	vmovdqa64 zmm3, zmm7
	vmovdqu32 zmm15, ZMMWORD PTR [r13+3968]
	vpxord zmm0, zmm0, zmm15
	vmovdqu32 ZMMWORD PTR [r13+3968], zmm0
	vmovdqu32 zmm15, ZMMWORD PTR [r13+3328]
	vpxord zmm1, zmm1, zmm15
	vmovdqu32 ZMMWORD PTR [r13+3328], zmm1
	vmovdqu32 zmm15, ZMMWORD PTR [r13+2176]
	vpxord zmm2, zmm2, zmm15
	vmovdqu32 ZMMWORD PTR [r13+2176], zmm2
	vmovdqu32 zmm15, ZMMWORD PTR [r13+3072]
	vpxord zmm3, zmm3, zmm15
	vmovdqu32 ZMMWORD PTR [r13+3072], zmm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm5, ZMMWORD PTR [r12+256]
	vpxord zmm5, zmm5, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm4, ZMMWORD PTR [r12+3712]
	vpxord zmm4, zmm4, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm3, ZMMWORD PTR [r12+3200]
	vpxord zmm3, zmm3, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm2, ZMMWORD PTR [r12+2688]
	vpxord zmm2, zmm2, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm1, ZMMWORD PTR [r12+2176]
	vpxord zmm1, zmm1, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm0, ZMMWORD PTR [r12+1664]
	vpxord zmm0, zmm0, zmm15
	vporq zmm6, zmm5, zmm3
	vpandnq zmm7, zmm0, zmm6
	vpxord zmm8, zmm5, zmm7
	vpxord zmm9, zmm3, zmm8
	vporq zmm10, zmm2, zmm9
	vpternlogd zmm3, zmm7, zmm2, 180
	vporq zmm9, zmm5, zmm9
	vmovdqa64 zmm7, zmm9
	vpternlogd zmm7, zmm1, zmm3, 120
	vpxord zmm7, zmm2, zmm7
	vpxord zmm0, zmm0, zmm7
	vporq zmm11, zmm8, zmm0
	vpandq zmm12, zmm1, zmm11
	vpandq zmm13, zmm2, zmm9
	vpternlogd zmm13, zmm8, zmm12, 150
	vpandnq zmm11, zmm5, zmm11
	vpxord zmm1, zmm1, zmm10
	vmovdqa64 zmm14, zmm1
	vpternlogd zmm14, zmm3, zmm11, 111
	vpternlogd zmm7, zmm14, zmm4, 180
	vpternlogd zmm11, zmm13, zmm1, 222
	vpternlogd zmm11, zmm3, zmm12, 176
	vpternlogd zmm1, zmm0, zmm11, 120
	vpternlogd zmm9, zmm1, zmm3, 236
	vpternlogd zmm12, zmm4, zmm9, 72
	vpxord zmm13, zmm12, zmm13
	vpternlogd zmm5, zmm11, zmm6, 150
	vpternlogd zmm5, zmm2, zmm1, 120
	vpternlogd zmm11, zmm4, zmm10, 206
	vpxord zmm11, zmm11, zmm5
	vpternlogd zmm5, zmm10, zmm3, 6
	vpternlogd zmm5, zmm8, zmm1, 150
	vpternlogd zmm5, zmm10, zmm4, 120
	vmovdqa64 zmm0, zmm13
	vmovdqa64 zmm1, zmm7
	vmovdqa64 zmm2, zmm5
	vmovdqa64 zmm3, zmm11
	vmovdqu32 zmm15, ZMMWORD PTR [r13+2944]
	vpxord zmm0, zmm0, zmm15
	vmovdqu32 ZMMWORD PTR [r13+2944], zmm0
	vmovdqu32 zmm15, ZMMWORD PTR [r13+3584]
	vpxord zmm1, zmm1, zmm15
	vmovdqu32 ZMMWORD PTR [r13+3584], zmm1
	vmovdqu32 zmm15, ZMMWORD PTR [r13+1280]
	vpxord zmm2, zmm2, zmm15
	vmovdqu32 ZMMWORD PTR [r13+1280], zmm2
	vmovdqu32 zmm15, ZMMWORD PTR [r13+384]
	vpxord zmm3, zmm3, zmm15
	vmovdqu32 ZMMWORD PTR [r13+384], zmm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm5, ZMMWORD PTR [r12+2176]
	vpxord zmm5, zmm5, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm4, ZMMWORD PTR [r12+1664]
	vpxord zmm4, zmm4, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm3, ZMMWORD PTR [r12+1152]
	vpxord zmm3, zmm3, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm2, ZMMWORD PTR [r12+640]
	vpxord zmm2, zmm2, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm1, ZMMWORD PTR [r12+128]
	vpxord zmm1, zmm1, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm0, ZMMWORD PTR [r12+3584]
	vpxord zmm0, zmm0, zmm15
	vmovdqa64 zmm6, zmm5
	vpternlogd zmm6, zmm4, zmm0, 224
	vmovdqa64 zmm7, zmm6
	vpternlogd zmm7, zmm4, zmm1, 150
	vpxord zmm8, zmm0, zmm7
	vpandnq zmm9, zmm8, zmm1
	vpandq zmm8, zmm5, zmm8
	vpxord zmm10, zmm4, zmm8
	vpxord zmm11, zmm5, zmm3
	vporq zmm12, zmm10, zmm11
	vpxord zmm13, zmm7, zmm12
	vpandq zmm14, zmm3, zmm13
	vpandnq zmm15, zmm0, zmm14
	vporq zmm10, zmm9, zmm10
	vmovdqu32 ZMMWORD PTR [rcx], zmm8
	vpxord zmm8, zmm15, zmm10
	vmovdqu32 ZMMWORD PTR [rcx+64], zmm7
	vmovdqa64 zmm7, zmm13
	vpternlogd zmm7, zmm8, zmm2, 120
	vpxord zmm12, zmm4, zmm12
	vpternlogd zmm3, zmm0, zmm12, 180
	vmovdqu32 ZMMWORD PTR [rcx+128], zmm7
	vmovdqa64 zmm7, zmm3
	vpternlogd zmm7, zmm1, zmm14, 244
	vporq zmm11, zmm4, zmm11
	vporq zmm6, zmm6, zmm7
	vpternlogd zmm6, zmm8, zmm11, 150
	vpternlogd zmm10, zmm5, zmm13, 224
	vpxord zmm10, zmm3, zmm10
	vpandnq zmm15, zmm15, zmm10
	vpternlogd zmm15, zmm9, zmm2, 30
	vmovdqu32 zmm9, ZMMWORD PTR [rcx+64]
	vpternlogd zmm1, zmm9, zmm10, 144
	vpternlogd zmm12, zmm11, zmm11, 195
	vpternlogd zmm1, zmm2, zmm12, 18
	vpxord zmm6, zmm1, zmm6
	vpxord zmm3, zmm5, zmm3
	vmovdqu32 zmm5, ZMMWORD PTR [rcx]
	vpternlogd zmm3, zmm0, zmm5, 96
	vpternlogd zmm3, zmm14, zmm12, 150
	vpternlogd zmm3, zmm7, zmm2, 180
	vmovdqu32 zmm0, ZMMWORD PTR [rcx+128]
	vmovdqa64 zmm1, zmm15
	vmovdqa64 zmm2, zmm6
	vmovdqu32 zmm15, ZMMWORD PTR [r13+2688]
	vpxord zmm0, zmm0, zmm15
	vmovdqu32 ZMMWORD PTR [r13+2688], zmm0
	vmovdqu32 zmm15, ZMMWORD PTR [r13+2816]
	vpxord zmm1, zmm1, zmm15
	vmovdqu32 ZMMWORD PTR [r13+2816], zmm1
	vmovdqu32 zmm15, ZMMWORD PTR [r13+1536]
	vpxord zmm2, zmm2, zmm15
	vmovdqu32 ZMMWORD PTR [r13+1536], zmm2
	vmovdqu32 zmm15, ZMMWORD PTR [r13+2432]
	vpxord zmm3, zmm3, zmm15
	vmovdqu32 ZMMWORD PTR [r13+2432], zmm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm5, ZMMWORD PTR [r12+128]
	vpxord zmm5, zmm5, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm4, ZMMWORD PTR [r12+3584]
	vpxord zmm4, zmm4, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm3, ZMMWORD PTR [r12+3072]
	vpxord zmm3, zmm3, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm2, ZMMWORD PTR [r12+2560]
	vpxord zmm2, zmm2, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm1, ZMMWORD PTR [r12+2048]
	vpxord zmm1, zmm1, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm0, ZMMWORD PTR [r12+1536]
	vpxord zmm0, zmm0, zmm15
	vpxord zmm6, zmm2, zmm1
	vpxord zmm7, zmm3, zmm6
	vpandq zmm8, zmm0, zmm7
	vpandq zmm9, zmm2, zmm6
	vpxord zmm10, zmm4, zmm9
	vpandq zmm11, zmm8, zmm10
	vpandq zmm12, zmm0, zmm9
	vpxord zmm13, zmm3, zmm12
	vporq zmm14, zmm10, zmm13
	vpxord zmm6, zmm0, zmm6
	vpxord zmm15, zmm14, zmm6
	vpternlogd zmm15, zmm5, zmm11, 180
	vpandnq zmm7, zmm7, zmm1
	vpxord zmm13, zmm8, zmm13
	vmovdqu32 ZMMWORD PTR [rcx], zmm15
	vmovdqa64 zmm15, zmm13
	vpternlogd zmm15, zmm10, zmm7, 30
	vpxord zmm6, zmm8, zmm6
	vpandnq zmm2, zmm6, zmm2
	vpxord zmm13, zmm1, zmm13
	vpternlogd zmm13, zmm10, zmm2, 180
	vpandnq zmm12, zmm12, zmm6
	vporq zmm2, zmm2, zmm12
	vpternlogd zmm14, zmm13, zmm4, 72
	vpxord zmm14, zmm2, zmm14
	vmovdqa64 zmm6, zmm13
	vpternlogd zmm6, zmm14, zmm5, 120
	vpternlogd zmm12, zmm10, zmm3, 244
	vpternlogd zmm12, zmm9, zmm13, 224
	vpternlogd zmm0, zmm7, zmm2, 96
	vporq zmm0, zmm11, zmm0
	vpxord zmm11, zmm12, zmm0
	vmovdqa64 zmm2, zmm15
	vpternlogd zmm2, zmm11, zmm5, 180
	vpternlogd zmm15, zmm4, zmm0, 135
	vpternlogd zmm5, zmm14, zmm12, 246
	vpternlogd zmm5, zmm11, zmm15, 150
	vmovdqu32 zmm0, ZMMWORD PTR [rcx]
	vmovdqa64 zmm1, zmm6
	vmovdqu32 ZMMWORD PTR [rcx+64], zmm2
	vmovdqa64 zmm2, zmm5
	vmovdqu32 zmm3, ZMMWORD PTR [rcx+64]
	vmovdqu32 zmm15, ZMMWORD PTR [r13+896]
	vpxord zmm0, zmm0, zmm15
	vmovdqu32 ZMMWORD PTR [r13+896], zmm0
	vmovdqu32 zmm15, ZMMWORD PTR [r13+1152]
	vpxord zmm1, zmm1, zmm15
	vmovdqu32 ZMMWORD PTR [r13+1152], zmm1
	vmovdqu32 zmm15, ZMMWORD PTR [r13+2304]
	vpxord zmm2, zmm2, zmm15
	vmovdqu32 ZMMWORD PTR [r13+2304], zmm2
	vmovdqu32 zmm15, ZMMWORD PTR [r13]
	vpxord zmm3, zmm3, zmm15
	vmovdqu32 ZMMWORD PTR [r13], zmm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm5, ZMMWORD PTR [r12+2048]
	vpxord zmm5, zmm5, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm4, ZMMWORD PTR [r12+1536]
	vpxord zmm4, zmm4, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm3, ZMMWORD PTR [r12+1024]
	vpxord zmm3, zmm3, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm2, ZMMWORD PTR [r12+512]
	vpxord zmm2, zmm2, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm1, ZMMWORD PTR [r12]
	vpxord zmm1, zmm1, zmm15
	add rax, rax
	sbb rbx, rbx
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm0, ZMMWORD PTR [r12+3968]
	vpxord zmm0, zmm0, zmm15
	vpandnq zmm6, zmm4, zmm3
	vmovdqa64 zmm7, zmm2
	vpternlogd zmm7, zmm1, zmm3, 180
	vpandq zmm8, zmm5, zmm7
	vpandnq zmm9, zmm6, zmm8
	vpandnq zmm10, zmm7, zmm4
	vporq zmm11, zmm5, zmm10
	vmovdqa64 zmm12, zmm1
	vpternlogd zmm12, zmm4, zmm3, 180
	vpandq zmm13, zmm11, zmm12
	vporq zmm8, zmm8, zmm13
	vpandnq zmm11, zmm11, zmm3
	vpternlogd zmm11, zmm13, zmm7, 105
	vpxord zmm6, zmm6, zmm11
	vmovdqa64 zmm7, zmm6
	vpternlogd zmm7, zmm9, zmm0, 30
	vpxord zmm6, zmm5, zmm6
	vpxord zmm11, zmm4, zmm11
	vmovdqa64 zmm13, zmm11
	vpternlogd zmm13, zmm1, zmm6, 120
	vpxord zmm10, zmm10, zmm13
	vpternlogd zmm4, zmm8, zmm13, 246
	vpternlogd zmm4, zmm1, zmm6, 150
	vpternlogd zmm8, zmm4, zmm0, 108
	vpxord zmm12, zmm12, zmm10
	vpternlogd zmm11, zmm12, zmm2, 54
	vpternlogd zmm5, zmm0, zmm11, 72
	vpxord zmm5, zmm5, zmm10
	vpternlogd zmm4, zmm12, zmm2, 64
	vpternlogd zmm4, zmm9, zmm11, 150
	vpternlogd zmm10, zmm4, zmm0, 30
	vmovdqa64 zmm0, zmm5
	vmovdqa64 zmm1, zmm8
	vmovdqa64 zmm2, zmm7
	vmovdqa64 zmm3, zmm10
	vmovdqu32 zmm15, ZMMWORD PTR [r13+1664]
	vpxord zmm0, zmm0, zmm15
	vmovdqu32 ZMMWORD PTR [r13+1664], zmm0
	vmovdqu32 zmm15, ZMMWORD PTR [r13+768]
	vpxord zmm1, zmm1, zmm15
	vmovdqu32 ZMMWORD PTR [r13+768], zmm1
	vmovdqu32 zmm15, ZMMWORD PTR [r13+2560]
	vpxord zmm2, zmm2, zmm15
	vmovdqu32 ZMMWORD PTR [r13+2560], zmm2
	vmovdqu32 zmm15, ZMMWORD PTR [r13+1920]
	vpxord zmm3, zmm3, zmm15
	vmovdqu32 ZMMWORD PTR [r13+1920], zmm3
	mov rbx, r12
	mov r12, r13
	mov r13, rbx
	sub r10, 1
	jne 210b
	vmovdqu32 zmm0, ZMMWORD PTR [rsi]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+64]
	vmovdqu32 ZMMWORD PTR [rsi], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+64], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+512]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+576]
	vmovdqu32 ZMMWORD PTR [rsi+512], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+576], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+1024]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+1088]
	vmovdqu32 ZMMWORD PTR [rsi+1024], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+1088], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+1536]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+1600]
	vmovdqu32 ZMMWORD PTR [rsi+1536], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+1600], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+2048]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+2112]
	vmovdqu32 ZMMWORD PTR [rsi+2048], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+2112], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+2560]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+2624]
	vmovdqu32 ZMMWORD PTR [rsi+2560], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+2624], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+3072]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+3136]
	vmovdqu32 ZMMWORD PTR [rsi+3072], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+3136], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+3584]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+3648]
	vmovdqu32 ZMMWORD PTR [rsi+3584], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+3648], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+128]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+192]
	vmovdqu32 ZMMWORD PTR [rsi+128], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+192], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+640]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+704]
	vmovdqu32 ZMMWORD PTR [rsi+640], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+704], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+1152]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+1216]
	vmovdqu32 ZMMWORD PTR [rsi+1152], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+1216], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+1664]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+1728]
	vmovdqu32 ZMMWORD PTR [rsi+1664], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+1728], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+2176]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+2240]
	vmovdqu32 ZMMWORD PTR [rsi+2176], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+2240], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+2688]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+2752]
	vmovdqu32 ZMMWORD PTR [rsi+2688], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+2752], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+3200]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+3264]
	vmovdqu32 ZMMWORD PTR [rsi+3200], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+3264], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+3712]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+3776]
	vmovdqu32 ZMMWORD PTR [rsi+3712], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+3776], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+256]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+320]
	vmovdqu32 ZMMWORD PTR [rsi+256], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+320], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+768]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+832]
	vmovdqu32 ZMMWORD PTR [rsi+768], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+832], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+1280]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+1344]
	vmovdqu32 ZMMWORD PTR [rsi+1280], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+1344], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+1792]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+1856]
	vmovdqu32 ZMMWORD PTR [rsi+1792], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+1856], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+2304]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+2368]
	vmovdqu32 ZMMWORD PTR [rsi+2304], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+2368], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+2816]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+2880]
	vmovdqu32 ZMMWORD PTR [rsi+2816], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+2880], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+3328]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+3392]
	vmovdqu32 ZMMWORD PTR [rsi+3328], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+3392], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+3840]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+3904]
	vmovdqu32 ZMMWORD PTR [rsi+3840], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+3904], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+384]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+448]
	vmovdqu32 ZMMWORD PTR [rsi+384], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+448], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+896]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+960]
	vmovdqu32 ZMMWORD PTR [rsi+896], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+960], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+1408]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+1472]
	vmovdqu32 ZMMWORD PTR [rsi+1408], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+1472], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+1920]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+1984]
	vmovdqu32 ZMMWORD PTR [rsi+1920], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+1984], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+2432]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+2496]
	vmovdqu32 ZMMWORD PTR [rsi+2432], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+2496], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+2944]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+3008]
	vmovdqu32 ZMMWORD PTR [rsi+2944], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+3008], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+3456]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+3520]
	vmovdqu32 ZMMWORD PTR [rsi+3456], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+3520], zmm0
	vmovdqu32 zmm0, ZMMWORD PTR [rsi+3968]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+4032]
	vmovdqu32 ZMMWORD PTR [rsi+3968], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+4032], zmm0
	sub r11, 1
	jne 25b
	mov r11, 8
211:
	movabs rbx, 4294967295
	vmovq xmm13, rbx
	vpbroadcastq zmm13, xmm13
	movabs rbx, 281470681808895
	vmovq xmm14, rbx
	vpbroadcastq zmm14, xmm14
	movabs rbx, 71777214294589695
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm0, ZMMWORD PTR [rsi]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+512]
	vmovdqu32 zmm2, ZMMWORD PTR [rsi+1024]
	vmovdqu32 zmm3, ZMMWORD PTR [rsi+1536]
	vmovdqu32 zmm4, ZMMWORD PTR [rsi+2048]
	vmovdqu32 zmm5, ZMMWORD PTR [rsi+2560]
	vmovdqu32 zmm6, ZMMWORD PTR [rsi+3072]
	vmovdqu32 zmm7, ZMMWORD PTR [rsi+3584]
	vpsrlq zmm8, zmm0, 32
	vpxord zmm8, zmm8, zmm4
	vpandq zmm8, zmm8, zmm13
	vpxord zmm4, zmm4, zmm8
	vpsllq zmm8, zmm8, 32
	vpxord zmm0, zmm0, zmm8
	vpsrlq zmm8, zmm1, 32
	vpxord zmm8, zmm8, zmm5
	vpandq zmm8, zmm8, zmm13
	vpxord zmm5, zmm5, zmm8
	vpsllq zmm8, zmm8, 32
	vpxord zmm1, zmm1, zmm8
	vpsrlq zmm8, zmm2, 32
	vpxord zmm8, zmm8, zmm6
	vpandq zmm8, zmm8, zmm13
	vpxord zmm6, zmm6, zmm8
	vpsllq zmm8, zmm8, 32
	vpxord zmm2, zmm2, zmm8
	vpsrlq zmm8, zmm3, 32
	vpxord zmm8, zmm8, zmm7
	vpandq zmm8, zmm8, zmm13
	vpxord zmm7, zmm7, zmm8
	vpsllq zmm8, zmm8, 32
	vpxord zmm3, zmm3, zmm8
	vpsrlq zmm8, zmm0, 16
	vpxord zmm8, zmm8, zmm2
	vpandq zmm8, zmm8, zmm14
	vpxord zmm2, zmm2, zmm8
	vpsllq zmm8, zmm8, 16
	vpxord zmm0, zmm0, zmm8
	vpsrlq zmm8, zmm1, 16
	vpxord zmm8, zmm8, zmm3
	vpandq zmm8, zmm8, zmm14
	vpxord zmm3, zmm3, zmm8
	vpsllq zmm8, zmm8, 16
	vpxord zmm1, zmm1, zmm8
	vpsrlq zmm8, zmm4, 16
	vpxord zmm8, zmm8, zmm6
	vpandq zmm8, zmm8, zmm14
	vpxord zmm6, zmm6, zmm8
	vpsllq zmm8, zmm8, 16
	vpxord zmm4, zmm4, zmm8
	vpsrlq zmm8, zmm5, 16
	vpxord zmm8, zmm8, zmm7
	vpandq zmm8, zmm8, zmm14
	vpxord zmm7, zmm7, zmm8
	vpsllq zmm8, zmm8, 16
	vpxord zmm5, zmm5, zmm8
	vpsrlq zmm8, zmm0, 8
	vpxord zmm8, zmm8, zmm1
	vpandq zmm8, zmm8, zmm15
	vpxord zmm1, zmm1, zmm8
	vpsllq zmm8, zmm8, 8
	vpxord zmm0, zmm0, zmm8
	vpsrlq zmm8, zmm2, 8
	vpxord zmm8, zmm8, zmm3
	vpandq zmm8, zmm8, zmm15
	vpxord zmm3, zmm3, zmm8
	vpsllq zmm8, zmm8, 8
	vpxord zmm2, zmm2, zmm8
	vpsrlq zmm8, zmm4, 8
	vpxord zmm8, zmm8, zmm5
	vpandq zmm8, zmm8, zmm15
	vpxord zmm5, zmm5, zmm8
	vpsllq zmm8, zmm8, 8
	vpxord zmm4, zmm4, zmm8
	vpsrlq zmm8, zmm6, 8
	vpxord zmm8, zmm8, zmm7
	vpandq zmm8, zmm8, zmm15
	vpxord zmm7, zmm7, zmm8
	vpsllq zmm8, zmm8, 8
	vpxord zmm6, zmm6, zmm8
	vmovdqu32 ZMMWORD PTR [rsi], zmm0
	vmovdqu32 ZMMWORD PTR [rsi+512], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+1024], zmm2
	vmovdqu32 ZMMWORD PTR [rsi+1536], zmm3
	vmovdqu32 ZMMWORD PTR [rsi+2048], zmm4
	vmovdqu32 ZMMWORD PTR [rsi+2560], zmm5
	vmovdqu32 ZMMWORD PTR [rsi+3072], zmm6
	vmovdqu32 ZMMWORD PTR [rsi+3584], zmm7
	add rsi, 64
	sub r11, 1
	jne 211b
	sub rsi, 512
	mov r11, 8
212:
	movabs rbx, 1085102592571150095
	vmovq xmm13, rbx
	vpbroadcastq zmm13, xmm13
	movabs rbx, 3689348814741910323
	vmovq xmm14, rbx
	vpbroadcastq zmm14, xmm14
	movabs rbx, 6148914691236517205
	vmovq xmm15, rbx
	vpbroadcastq zmm15, xmm15
	vmovdqu32 zmm0, ZMMWORD PTR [rsi]
	vmovdqu32 zmm1, ZMMWORD PTR [rsi+64]
	vmovdqu32 zmm2, ZMMWORD PTR [rsi+128]
	vmovdqu32 zmm3, ZMMWORD PTR [rsi+192]
	vmovdqu32 zmm4, ZMMWORD PTR [rsi+256]
	vmovdqu32 zmm5, ZMMWORD PTR [rsi+320]
	vmovdqu32 zmm6, ZMMWORD PTR [rsi+384]
	vmovdqu32 zmm7, ZMMWORD PTR [rsi+448]
	vpsrlq zmm8, zmm0, 4
	vpxord zmm8, zmm8, zmm4
	vpandq zmm8, zmm8, zmm13
	vpxord zmm4, zmm4, zmm8
	vpsllq zmm8, zmm8, 4
	vpxord zmm0, zmm0, zmm8
	vpsrlq zmm8, zmm1, 4
	vpxord zmm8, zmm8, zmm5
	vpandq zmm8, zmm8, zmm13
	vpxord zmm5, zmm5, zmm8
	vpsllq zmm8, zmm8, 4
	vpxord zmm1, zmm1, zmm8
	vpsrlq zmm8, zmm2, 4
	vpxord zmm8, zmm8, zmm6
	vpandq zmm8, zmm8, zmm13
	vpxord zmm6, zmm6, zmm8
	vpsllq zmm8, zmm8, 4
	vpxord zmm2, zmm2, zmm8
	vpsrlq zmm8, zmm3, 4
	vpxord zmm8, zmm8, zmm7
	vpandq zmm8, zmm8, zmm13
	vpxord zmm7, zmm7, zmm8
	vpsllq zmm8, zmm8, 4
	vpxord zmm3, zmm3, zmm8
	vpsrlq zmm8, zmm0, 2
	vpxord zmm8, zmm8, zmm2
	vpandq zmm8, zmm8, zmm14
	vpxord zmm2, zmm2, zmm8
	vpsllq zmm8, zmm8, 2
	vpxord zmm0, zmm0, zmm8
	vpsrlq zmm8, zmm1, 2
	vpxord zmm8, zmm8, zmm3
	vpandq zmm8, zmm8, zmm14
	vpxord zmm3, zmm3, zmm8
	vpsllq zmm8, zmm8, 2
	vpxord zmm1, zmm1, zmm8
	vpsrlq zmm8, zmm4, 2
	vpxord zmm8, zmm8, zmm6
	vpandq zmm8, zmm8, zmm14
	vpxord zmm6, zmm6, zmm8
	vpsllq zmm8, zmm8, 2
	vpxord zmm4, zmm4, zmm8
	vpsrlq zmm8, zmm5, 2
	vpxord zmm8, zmm8, zmm7
	vpandq zmm8, zmm8, zmm14
	vpxord zmm7, zmm7, zmm8
	vpsllq zmm8, zmm8, 2
	vpxord zmm5, zmm5, zmm8
	vpsrlq zmm8, zmm0, 1
	vpxord zmm8, zmm8, zmm1
	vpandq zmm8, zmm8, zmm15
	vpxord zmm1, zmm1, zmm8
	vpsllq zmm8, zmm8, 1
	vpxord zmm0, zmm0, zmm8
	vpsrlq zmm8, zmm2, 1
	vpxord zmm8, zmm8, zmm3
	vpandq zmm8, zmm8, zmm15
	vpxord zmm3, zmm3, zmm8
	vpsllq zmm8, zmm8, 1
	vpxord zmm2, zmm2, zmm8
	vpsrlq zmm8, zmm4, 1
	vpxord zmm8, zmm8, zmm5
	vpandq zmm8, zmm8, zmm15
	vpxord zmm5, zmm5, zmm8
	vpsllq zmm8, zmm8, 1
	vpxord zmm4, zmm4, zmm8
	vpsrlq zmm8, zmm6, 1
	vpxord zmm8, zmm8, zmm7
	vpandq zmm8, zmm8, zmm15
	vpxord zmm7, zmm7, zmm8
	vpsllq zmm8, zmm8, 1
	vpxord zmm6, zmm6, zmm8
	vmovdqu32 ZMMWORD PTR [rsi], zmm0
	vmovdqu32 ZMMWORD PTR [rsi+64], zmm1
	vmovdqu32 ZMMWORD PTR [rsi+128], zmm2
	vmovdqu32 ZMMWORD PTR [rsi+192], zmm3
	vmovdqu32 ZMMWORD PTR [rsi+256], zmm4
	vmovdqu32 ZMMWORD PTR [rsi+320], zmm5
	vmovdqu32 ZMMWORD PTR [rsi+384], zmm6
	vmovdqu32 ZMMWORD PTR [rsi+448], zmm7
	add rsi, 512
	sub r11, 1
	jne 212b
	sub rsi, 4096
	add rsi, 4096
	sub rdx, 512
	cmp rdx, 512
	jae 22b
	mov rbx, QWORD PTR [rcx+1016]
	mov r12, QWORD PTR [rcx+1008]
	mov r13, QWORD PTR [rcx+1000]
	vzeroupper
	jmp 21f
20:
21:
	cmp rdx, 256
	jb 213f
	mov QWORD PTR [rcx+1016], rbx
	mov QWORD PTR [rcx+1008], r12
	mov QWORD PTR [rcx+1000], r13
215:
	mov r11, 8
216:
	movabs rbx, 4294967295
	vmovq xmm13, rbx
	vpbroadcastq ymm13, xmm13
	movabs rbx, 281470681808895
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	movabs rbx, 71777214294589695
	vmovq xmm15, rbx
	vpbroadcastq ymm15, xmm15
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vmovdqu ymm1, YMMWORD PTR [rsi+256]
	vmovdqu ymm2, YMMWORD PTR [rsi+512]
	vmovdqu ymm3, YMMWORD PTR [rsi+768]
	vmovdqu ymm4, YMMWORD PTR [rsi+1024]
	vmovdqu ymm5, YMMWORD PTR [rsi+1280]
	vmovdqu ymm6, YMMWORD PTR [rsi+1536]
	vmovdqu ymm7, YMMWORD PTR [rsi+1792]
	vpsrlq ymm8, ymm0, 32
	vpxor ymm8, ymm8, ymm4
	vpand ymm8, ymm8, ymm13
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm8, ymm8, 32
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm1, 32
	vpxor ymm8, ymm8, ymm5
	vpand ymm8, ymm8, ymm13
	vpxor ymm5, ymm5, ymm8
	vpsllq ymm8, ymm8, 32
	vpxor ymm1, ymm1, ymm8
	vpsrlq ymm8, ymm2, 32
	vpxor ymm8, ymm8, ymm6
	vpand ymm8, ymm8, ymm13
	vpxor ymm6, ymm6, ymm8
	vpsllq ymm8, ymm8, 32
	vpxor ymm2, ymm2, ymm8
	vpsrlq ymm8, ymm3, 32
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm13
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 32
	vpxor ymm3, ymm3, ymm8
	vpsrlq ymm8, ymm0, 16
	vpxor ymm8, ymm8, ymm2
	vpand ymm8, ymm8, ymm14
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm8, ymm8, 16
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm1, 16
	vpxor ymm8, ymm8, ymm3
	vpand ymm8, ymm8, ymm14
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm8, ymm8, 16
	vpxor ymm1, ymm1, ymm8
	vpsrlq ymm8, ymm4, 16
	vpxor ymm8, ymm8, ymm6
	vpand ymm8, ymm8, ymm14
	vpxor ymm6, ymm6, ymm8
	vpsllq ymm8, ymm8, 16
	vpxor ymm4, ymm4, ymm8
	vpsrlq ymm8, ymm5, 16
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm14
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 16
	vpxor ymm5, ymm5, ymm8
	vpsrlq ymm8, ymm0, 8
	vpxor ymm8, ymm8, ymm1
	vpand ymm8, ymm8, ymm15
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm8, ymm8, 8
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm2, 8
	vpxor ymm8, ymm8, ymm3
	vpand ymm8, ymm8, ymm15
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm8, ymm8, 8
	vpxor ymm2, ymm2, ymm8
	vpsrlq ymm8, ymm4, 8
	vpxor ymm8, ymm8, ymm5
	vpand ymm8, ymm8, ymm15
	vpxor ymm5, ymm5, ymm8
	vpsllq ymm8, ymm8, 8
	vpxor ymm4, ymm4, ymm8
	vpsrlq ymm8, ymm6, 8
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm15
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 8
	vpxor ymm6, ymm6, ymm8
	vmovdqu YMMWORD PTR [rsi], ymm0
	vmovdqu YMMWORD PTR [rsi+256], ymm1
	vmovdqu YMMWORD PTR [rsi+512], ymm2
	vmovdqu YMMWORD PTR [rsi+768], ymm3
	vmovdqu YMMWORD PTR [rsi+1024], ymm4
	vmovdqu YMMWORD PTR [rsi+1280], ymm5
	vmovdqu YMMWORD PTR [rsi+1536], ymm6
	vmovdqu YMMWORD PTR [rsi+1792], ymm7
	add rsi, 32
	sub r11, 1
	jne 216b
	sub rsi, 256
	mov r11, 8
217:
	movabs rbx, 1085102592571150095
	vmovq xmm13, rbx
	vpbroadcastq ymm13, xmm13
	movabs rbx, 3689348814741910323
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	movabs rbx, 6148914691236517205
	vmovq xmm15, rbx
	vpbroadcastq ymm15, xmm15
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vmovdqu ymm2, YMMWORD PTR [rsi+64]
	vmovdqu ymm3, YMMWORD PTR [rsi+96]
	vmovdqu ymm4, YMMWORD PTR [rsi+128]
	vmovdqu ymm5, YMMWORD PTR [rsi+160]
	vmovdqu ymm6, YMMWORD PTR [rsi+192]
	vmovdqu ymm7, YMMWORD PTR [rsi+224]
	vpsrlq ymm8, ymm0, 4
	vpxor ymm8, ymm8, ymm4
	vpand ymm8, ymm8, ymm13
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm8, ymm8, 4
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm1, 4
	vpxor ymm8, ymm8, ymm5
	vpand ymm8, ymm8, ymm13
	vpxor ymm5, ymm5, ymm8
	vpsllq ymm8, ymm8, 4
	vpxor ymm1, ymm1, ymm8
	vpsrlq ymm8, ymm2, 4
	vpxor ymm8, ymm8, ymm6
	vpand ymm8, ymm8, ymm13
	vpxor ymm6, ymm6, ymm8
	vpsllq ymm8, ymm8, 4
	vpxor ymm2, ymm2, ymm8
	vpsrlq ymm8, ymm3, 4
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm13
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 4
	vpxor ymm3, ymm3, ymm8
	vpsrlq ymm8, ymm0, 2
	vpxor ymm8, ymm8, ymm2
	vpand ymm8, ymm8, ymm14
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm8, ymm8, 2
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm1, 2
	vpxor ymm8, ymm8, ymm3
	vpand ymm8, ymm8, ymm14
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm8, ymm8, 2
	vpxor ymm1, ymm1, ymm8
	vpsrlq ymm8, ymm4, 2
	vpxor ymm8, ymm8, ymm6
	vpand ymm8, ymm8, ymm14
	vpxor ymm6, ymm6, ymm8
	vpsllq ymm8, ymm8, 2
	vpxor ymm4, ymm4, ymm8
	vpsrlq ymm8, ymm5, 2
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm14
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 2
	vpxor ymm5, ymm5, ymm8
	vpsrlq ymm8, ymm0, 1
	vpxor ymm8, ymm8, ymm1
	vpand ymm8, ymm8, ymm15
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm8, ymm8, 1
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm2, 1
	vpxor ymm8, ymm8, ymm3
	vpand ymm8, ymm8, ymm15
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm8, ymm8, 1
	vpxor ymm2, ymm2, ymm8
	vpsrlq ymm8, ymm4, 1
	vpxor ymm8, ymm8, ymm5
	vpand ymm8, ymm8, ymm15
	vpxor ymm5, ymm5, ymm8
	vpsllq ymm8, ymm8, 1
	vpxor ymm4, ymm4, ymm8
	vpsrlq ymm8, ymm6, 1
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm15
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 1
	vpxor ymm6, ymm6, ymm8
	vmovdqu YMMWORD PTR [rsi], ymm0
	vmovdqu YMMWORD PTR [rsi+32], ymm1
	vmovdqu YMMWORD PTR [rsi+64], ymm2
	vmovdqu YMMWORD PTR [rsi+96], ymm3
	vmovdqu YMMWORD PTR [rsi+128], ymm4
	vmovdqu YMMWORD PTR [rsi+160], ymm5
	vmovdqu YMMWORD PTR [rsi+192], ymm6
	vmovdqu YMMWORD PTR [rsi+224], ymm7
	add rsi, 256
	sub r11, 1
	jne 217b
	sub rsi, 2048
	movabs rbx, -1
	vmovq xmm15, rbx
	vpbroadcastq ymm15, xmm15
	mov r11, 3
218:
	cmp r11, 3
	je 219f
	cmp r11, 2
	je 221f
	mov r8, rdi
	add r8, 120
	mov r9, -8
	jmp 222f
221:
	mov r8, rdi
	add r8, 128
	mov r9, 8
222:
	jmp 220f
219:
	mov r8, rdi
	add r8, 376
	mov r9, -8
220:
	mov r10, 16
	mov r12, rsi
	add r12, 32
	mov r13, rsi
223:
	mov rax, QWORD PTR [r8]
	add r8, r9
	ror rax, 48
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm5, YMMWORD PTR [r12]
	vpxor ymm5, ymm5, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm4, YMMWORD PTR [r12+1984]
	vpxor ymm4, ymm4, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm3, YMMWORD PTR [r12+1728]
	vpxor ymm3, ymm3, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm2, YMMWORD PTR [r12+1472]
	vpxor ymm2, ymm2, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm1, YMMWORD PTR [r12+1216]
	vpxor ymm1, ymm1, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm0, YMMWORD PTR [r12+960]
	vpxor ymm0, ymm0, ymm14
	vpandn ymm6, ymm1, ymm5
	vpxor ymm7, ymm2, ymm6
	vpor ymm8, ymm3, ymm0
	vpxor ymm9, ymm5, ymm3
	vpand ymm10, ymm8, ymm9
	vpxor ymm11, ymm2, ymm10
	vpandn ymm12, ymm7, ymm11
	vpxor ymm13, ymm1, ymm0
	vpxor ymm14, ymm3, ymm13
	vpandn ymm14, ymm14, ymm7
	vpor ymm10, ymm0, ymm10
	vpxor ymm10, ymm14, ymm10
	vpandn ymm14, ymm12, ymm10
	vpor ymm0, ymm5, ymm0
	vmovdqu YMMWORD PTR [rcx], ymm14
	vpor ymm14, ymm10, ymm0
	vpandn ymm11, ymm11, ymm1
	vmovdqu YMMWORD PTR [rcx+32], ymm1
	vpxor ymm1, ymm14, ymm11
	vpandn ymm0, ymm0, ymm2
	vpxor ymm0, ymm11, ymm0
	vpandn ymm9, ymm9, ymm13
	vpor ymm9, ymm0, ymm9
	vpandn ymm6, ymm6, ymm3
	vpxor ymm3, ymm7, ymm14
	vpandn ymm6, ymm6, ymm3
	vpxor ymm3, ymm6, ymm15
	vpand ymm10, ymm8, ymm10
	vpxor ymm10, ymm3, ymm10
	vpandn ymm1, ymm4, ymm1
	vpxor ymm1, ymm1, ymm10
	vpxor ymm6, ymm13, ymm6
	vpor ymm6, ymm11, ymm6
	vpxor ymm6, ymm8, ymm6
	vpxor ymm6, ymm5, ymm6
	vpxor ymm10, ymm10, ymm6
	vpor ymm12, ymm12, ymm4
	vpxor ymm12, ymm12, ymm10
	vpxor ymm14, ymm8, ymm14
	vpor ymm14, ymm9, ymm14
	vpxor ymm14, ymm6, ymm14
	vpor ymm10, ymm13, ymm10
	vpxor ymm10, ymm14, ymm10
	vmovdqu ymm13, YMMWORD PTR [rcx]
	vpor ymm8, ymm13, ymm4
	vpxor ymm10, ymm8, ymm10
	vmovdqu ymm8, YMMWORD PTR [rcx+32]
	vpor ymm7, ymm8, ymm7
	vpandn ymm14, ymm14, ymm7
	vpand ymm6, ymm13, ymm6
	vpxor ymm6, ymm14, ymm6
	vpor ymm4, ymm6, ymm4
	vpxor ymm9, ymm4, ymm9
	vmovdqa ymm0, ymm9
	vmovdqa ymm2, ymm10
	vmovdqa ymm3, ymm12
	vmovdqu ymm14, YMMWORD PTR [r13+256]
	vpxor ymm0, ymm0, ymm14
	vmovdqu YMMWORD PTR [r13+256], ymm0
	vmovdqu ymm14, YMMWORD PTR [r13+320]
	vpxor ymm1, ymm1, ymm14
	vmovdqu YMMWORD PTR [r13+320], ymm1
	vmovdqu ymm14, YMMWORD PTR [r13+1856]
	vpxor ymm2, ymm2, ymm14
	vmovdqu YMMWORD PTR [r13+1856], ymm2
	vmovdqu ymm14, YMMWORD PTR [r13+1920]
	vpxor ymm3, ymm3, ymm14
	vmovdqu YMMWORD PTR [r13+1920], ymm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm5, YMMWORD PTR [r12+1216]
	vpxor ymm5, ymm5, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm4, YMMWORD PTR [r12+960]
	vpxor ymm4, ymm4, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm3, YMMWORD PTR [r12+704]
	vpxor ymm3, ymm3, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm2, YMMWORD PTR [r12+448]
	vpxor ymm2, ymm2, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm1, YMMWORD PTR [r12+192]
	vpxor ymm1, ymm1, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm0, YMMWORD PTR [r12+1920]
	vpxor ymm0, ymm0, ymm14
	vpxor ymm6, ymm4, ymm1
	vpandn ymm7, ymm0, ymm5
	vpandn ymm7, ymm7, ymm1
	vpor ymm8, ymm4, ymm7
	vpandn ymm9, ymm0, ymm6
	vpand ymm10, ymm5, ymm6
	vpxor ymm10, ymm1, ymm10
	vpandn ymm1, ymm9, ymm10
	vpand ymm11, ymm3, ymm0
	vpxor ymm9, ymm7, ymm9
	vpand ymm9, ymm8, ymm9
	vpandn ymm7, ymm11, ymm9
	vpand ymm12, ymm3, ymm9
	vpxor ymm5, ymm5, ymm15
	vpxor ymm5, ymm12, ymm5
	vpxor ymm0, ymm0, ymm6
	vpandn ymm13, ymm11, ymm0
	vpxor ymm14, ymm5, ymm13
	vpandn ymm7, ymm7, ymm2
	vpxor ymm7, ymm7, ymm14
	vpandn ymm13, ymm13, ymm4
	vpxor ymm10, ymm10, ymm13
	vpandn ymm5, ymm10, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm5, ymm5, ymm3
	vpandn ymm4, ymm2, ymm8
	vpxor ymm4, ymm4, ymm5
	vpxor ymm13, ymm12, ymm13
	vpor ymm13, ymm3, ymm13
	vpxor ymm8, ymm8, ymm14
	vpor ymm11, ymm11, ymm8
	vpxor ymm3, ymm13, ymm11
	vpxor ymm14, ymm9, ymm14
	vpxor ymm14, ymm5, ymm14
	vpand ymm14, ymm11, ymm14
	vpand ymm13, ymm6, ymm13
	vpxor ymm13, ymm14, ymm13
	vpor ymm14, ymm13, ymm2
	vpxor ymm3, ymm14, ymm3
	vpandn ymm10, ymm10, ymm13
	vpor ymm8, ymm0, ymm8
	vpxor ymm8, ymm10, ymm8
	vpor ymm2, ymm1, ymm2
	vpxor ymm8, ymm2, ymm8
	vmovdqa ymm0, ymm8
	vmovdqa ymm1, ymm3
	vmovdqa ymm2, ymm7
	vmovdqa ymm3, ymm4
	vmovdqu ymm14, YMMWORD PTR [r13+1600]
	vpxor ymm0, ymm0, ymm14
	vmovdqu YMMWORD PTR [r13+1600], ymm0
	vmovdqu ymm14, YMMWORD PTR [r13+1728]
	vpxor ymm1, ymm1, ymm14
	vmovdqu YMMWORD PTR [r13+1728], ymm1
	vmovdqu ymm14, YMMWORD PTR [r13+1024]
	vpxor ymm2, ymm2, ymm14
	vmovdqu YMMWORD PTR [r13+1024], ymm2
	vmovdqu ymm14, YMMWORD PTR [r13+896]
	vpxor ymm3, ymm3, ymm14
	vmovdqu YMMWORD PTR [r13+896], ymm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm5, YMMWORD PTR [r12+192]
	vpxor ymm5, ymm5, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm4, YMMWORD PTR [r12+1920]
	vpxor ymm4, ymm4, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm3, YMMWORD PTR [r12+1664]
	vpxor ymm3, ymm3, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm2, YMMWORD PTR [r12+1408]
	vpxor ymm2, ymm2, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm1, YMMWORD PTR [r12+1152]
	vpxor ymm1, ymm1, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm0, YMMWORD PTR [r12+896]
	vpxor ymm0, ymm0, ymm14
	vpandn ymm6, ymm4, ymm5
	vpxor ymm7, ymm3, ymm0
	vpor ymm8, ymm6, ymm7
	vpxor ymm9, ymm2, ymm0
	vpandn ymm10, ymm5, ymm9
	vpxor ymm11, ymm8, ymm10
	vpxor ymm12, ymm4, ymm7
	vpandn ymm13, ymm0, ymm12
	vpxor ymm13, ymm8, ymm13
	vpandn ymm8, ymm13, ymm11
	vpand ymm14, ymm0, ymm11
	vpor ymm14, ymm2, ymm14
	vpand ymm14, ymm5, ymm14
	vpxor ymm14, ymm12, ymm14
	vmovdqu YMMWORD PTR [rcx], ymm6
	vpandn ymm6, ymm1, ymm11
	vpxor ymm6, ymm6, ymm14
	vpand ymm9, ymm7, ymm9
	vpxor ymm7, ymm5, ymm2
	vmovdqu YMMWORD PTR [rcx+32], ymm6
	vpxor ymm6, ymm13, ymm7
	vpor ymm6, ymm3, ymm6
	vpandn ymm9, ymm9, ymm6
	vpor ymm7, ymm10, ymm7
	vpandn ymm10, ymm7, ymm14
	vpand ymm0, ymm2, ymm0
	vpandn ymm6, ymm4, ymm0
	vpxor ymm6, ymm10, ymm6
	vpand ymm13, ymm13, ymm6
	vpor ymm0, ymm12, ymm0
	vpandn ymm13, ymm13, ymm0
	vpxor ymm13, ymm5, ymm13
	vpand ymm9, ymm9, ymm1
	vpxor ymm9, ymm9, ymm13
	vpxor ymm11, ymm11, ymm15
	vpor ymm4, ymm4, ymm11
	vpor ymm4, ymm3, ymm4
	vpxor ymm4, ymm12, ymm4
	vpxor ymm7, ymm7, ymm4
	vpandn ymm8, ymm8, ymm1
	vpxor ymm7, ymm8, ymm7
	vpand ymm11, ymm2, ymm11
	vpxor ymm11, ymm14, ymm11
	vpor ymm11, ymm4, ymm11
	vmovdqu ymm4, YMMWORD PTR [rcx]
	vpxor ymm13, ymm4, ymm13
	vpxor ymm13, ymm11, ymm13
	vpor ymm1, ymm6, ymm1
	vpxor ymm13, ymm1, ymm13
	vmovdqu ymm0, YMMWORD PTR [rcx+32]
	vmovdqa ymm1, ymm13
	vmovdqa ymm2, ymm9
	vmovdqa ymm3, ymm7
	vmovdqu ymm14, YMMWORD PTR [r13+704]
	vpxor ymm0, ymm0, ymm14
	vmovdqu YMMWORD PTR [r13+704], ymm0
	vmovdqu ymm14, YMMWORD PTR [r13+512]
	vpxor ymm1, ymm1, ymm14
	vmovdqu YMMWORD PTR [r13+512], ymm1
	vmovdqu ymm14, YMMWORD PTR [r13+128]
	vpxor ymm2, ymm2, ymm14
	vmovdqu YMMWORD PTR [r13+128], ymm2
	vmovdqu ymm14, YMMWORD PTR [r13+64]
	vpxor ymm3, ymm3, ymm14
	vmovdqu YMMWORD PTR [r13+64], ymm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm5, YMMWORD PTR [r12+1152]
	vpxor ymm5, ymm5, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm4, YMMWORD PTR [r12+896]
	vpxor ymm4, ymm4, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm3, YMMWORD PTR [r12+640]
	vpxor ymm3, ymm3, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm2, YMMWORD PTR [r12+384]
	vpxor ymm2, ymm2, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm1, YMMWORD PTR [r12+128]
	vpxor ymm1, ymm1, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm0, YMMWORD PTR [r12+1856]
	vpxor ymm0, ymm0, ymm14
	vpxor ymm5, ymm5, ymm3
	vpxor ymm3, ymm3, ymm1
	vpor ymm6, ymm4, ymm2
	vpxor ymm6, ymm1, ymm6
	vpandn ymm6, ymm6, ymm3
	vpandn ymm7, ymm4, ymm3
	vpxor ymm8, ymm2, ymm7
	vpor ymm9, ymm5, ymm8
	vpandn ymm9, ymm6, ymm9
	vpxor ymm10, ymm4, ymm9
	vpand ymm8, ymm8, ymm10
	vpandn ymm3, ymm8, ymm3
	vpxor ymm5, ymm5, ymm10
	vpandn ymm3, ymm3, ymm5
	vpxor ymm3, ymm6, ymm3
	vpxor ymm2, ymm4, ymm2
	vpor ymm7, ymm1, ymm7
	vpxor ymm7, ymm5, ymm7
	vpandn ymm5, ymm2, ymm7
	vpxor ymm5, ymm9, ymm5
	vpandn ymm9, ymm3, ymm0
	vpxor ymm9, ymm9, ymm5
	vpxor ymm5, ymm5, ymm15
	vpandn ymm1, ymm0, ymm3
	vpxor ymm1, ymm1, ymm5
	vpxor ymm5, ymm3, ymm5
	vpandn ymm2, ymm2, ymm5
	vpor ymm2, ymm8, ymm2
	vpxor ymm2, ymm7, ymm2
	vpor ymm7, ymm10, ymm0
	vpxor ymm7, ymm7, ymm2
	vpand ymm10, ymm0, ymm10
	vpxor ymm2, ymm10, ymm2
	vmovdqa ymm0, ymm2
	vmovdqu YMMWORD PTR [rcx], ymm1
	vmovdqa ymm1, ymm7
	vmovdqu ymm2, YMMWORD PTR [rcx]
	vmovdqa ymm3, ymm9
	vmovdqu ymm14, YMMWORD PTR [r13+1984]
	vpxor ymm0, ymm0, ymm14
	vmovdqu YMMWORD PTR [r13+1984], ymm0
	vmovdqu ymm14, YMMWORD PTR [r13+1664]
	vpxor ymm1, ymm1, ymm14
	vmovdqu YMMWORD PTR [r13+1664], ymm1
	vmovdqu ymm14, YMMWORD PTR [r13+1088]
	vpxor ymm2, ymm2, ymm14
	vmovdqu YMMWORD PTR [r13+1088], ymm2
	vmovdqu ymm14, YMMWORD PTR [r13+1536]
	vpxor ymm3, ymm3, ymm14
	vmovdqu YMMWORD PTR [r13+1536], ymm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm5, YMMWORD PTR [r12+128]
	vpxor ymm5, ymm5, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm4, YMMWORD PTR [r12+1856]
	vpxor ymm4, ymm4, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm3, YMMWORD PTR [r12+1600]
	vpxor ymm3, ymm3, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm2, YMMWORD PTR [r12+1344]
	vpxor ymm2, ymm2, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm1, YMMWORD PTR [r12+1088]
	vpxor ymm1, ymm1, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm0, YMMWORD PTR [r12+832]
	vpxor ymm0, ymm0, ymm14
	vpor ymm6, ymm5, ymm3
	vpandn ymm7, ymm0, ymm6
	vpxor ymm8, ymm5, ymm7
	vpxor ymm9, ymm3, ymm8
	vpor ymm10, ymm2, ymm9
	vpandn ymm7, ymm2, ymm7
	vpxor ymm7, ymm3, ymm7
	vpand ymm3, ymm1, ymm7
	vpor ymm9, ymm5, ymm9
	vpxor ymm3, ymm3, ymm9
	vpxor ymm3, ymm2, ymm3
	vpxor ymm0, ymm0, ymm3
	vpor ymm11, ymm8, ymm0
	vpand ymm12, ymm1, ymm11
	vpxor ymm13, ymm8, ymm12
	vpand ymm14, ymm2, ymm9
	vpxor ymm14, ymm13, ymm14
	vpandn ymm11, ymm5, ymm11
	vpxor ymm13, ymm7, ymm11
	vpxor ymm1, ymm1, ymm10
	vpandn ymm13, ymm13, ymm1
	vpxor ymm13, ymm13, ymm15
	vpandn ymm13, ymm4, ymm13
	vpxor ymm3, ymm13, ymm3
	vpandn ymm13, ymm12, ymm7
	vpxor ymm11, ymm11, ymm1
	vpor ymm11, ymm14, ymm11
	vpandn ymm13, ymm13, ymm11
	vpandn ymm11, ymm13, ymm10
	vpand ymm0, ymm0, ymm13
	vpxor ymm0, ymm1, ymm0
	vpand ymm9, ymm7, ymm9
	vpor ymm9, ymm0, ymm9
	vpxor ymm9, ymm12, ymm9
	vpand ymm9, ymm9, ymm4
	vpxor ymm14, ymm9, ymm14
	vpxor ymm6, ymm5, ymm6
	vpxor ymm6, ymm13, ymm6
	vpand ymm2, ymm2, ymm0
	vpxor ymm2, ymm6, ymm2
	vpor ymm11, ymm11, ymm4
	vpxor ymm11, ymm11, ymm2
	vpxor ymm7, ymm10, ymm7
	vpandn ymm2, ymm2, ymm7
	vpxor ymm0, ymm8, ymm0
	vpxor ymm0, ymm2, ymm0
	vpand ymm4, ymm10, ymm4
	vpxor ymm0, ymm4, ymm0
	vmovdqu YMMWORD PTR [rcx], ymm0
	vmovdqa ymm0, ymm14
	vmovdqa ymm1, ymm3
	vmovdqu ymm2, YMMWORD PTR [rcx]
	vmovdqa ymm3, ymm11
	vmovdqu ymm14, YMMWORD PTR [r13+1472]
	vpxor ymm0, ymm0, ymm14
	vmovdqu YMMWORD PTR [r13+1472], ymm0
	vmovdqu ymm14, YMMWORD PTR [r13+1792]
	vpxor ymm1, ymm1, ymm14
	vmovdqu YMMWORD PTR [r13+1792], ymm1
	vmovdqu ymm14, YMMWORD PTR [r13+640]
	vpxor ymm2, ymm2, ymm14
	vmovdqu YMMWORD PTR [r13+640], ymm2
	vmovdqu ymm14, YMMWORD PTR [r13+192]
	vpxor ymm3, ymm3, ymm14
	vmovdqu YMMWORD PTR [r13+192], ymm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm5, YMMWORD PTR [r12+1088]
	vpxor ymm5, ymm5, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm4, YMMWORD PTR [r12+832]
	vpxor ymm4, ymm4, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm3, YMMWORD PTR [r12+576]
	vpxor ymm3, ymm3, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm2, YMMWORD PTR [r12+320]
	vpxor ymm2, ymm2, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm1, YMMWORD PTR [r12+64]
	vpxor ymm1, ymm1, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm0, YMMWORD PTR [r12+1792]
	vpxor ymm0, ymm0, ymm14
	vpxor ymm6, ymm4, ymm1
	vpor ymm7, ymm4, ymm0
	vpand ymm7, ymm5, ymm7
	vpxor ymm6, ymm6, ymm7
	vpxor ymm8, ymm0, ymm6
	vpandn ymm9, ymm8, ymm1
	vpand ymm8, ymm5, ymm8
	vpxor ymm10, ymm4, ymm8
	vpxor ymm11, ymm5, ymm3
	vpor ymm12, ymm10, ymm11
	vpxor ymm13, ymm6, ymm12
	vpand ymm14, ymm3, ymm13
	vmovdqu YMMWORD PTR [rcx], ymm8
	vpandn ymm8, ymm0, ymm14
	vpor ymm10, ymm9, ymm10
	vmovdqu YMMWORD PTR [rcx+32], ymm6
	vpxor ymm6, ymm8, ymm10
	vmovdqu YMMWORD PTR [rcx+64], ymm9
	vpand ymm9, ymm6, ymm2
	vpxor ymm9, ymm9, ymm13
	vpxor ymm12, ymm4, ymm12
	vmovdqu YMMWORD PTR [rcx+96], ymm9
	vpandn ymm9, ymm12, ymm0
	vpxor ymm9, ymm3, ymm9
	vpandn ymm3, ymm14, ymm1
	vpor ymm3, ymm9, ymm3
	vpor ymm11, ymm4, ymm11
	vpxor ymm6, ymm6, ymm11
	vpor ymm7, ymm7, ymm3
	vpxor ymm7, ymm6, ymm7
	vpor ymm13, ymm5, ymm13
	vpand ymm13, ymm10, ymm13
	vpxor ymm13, ymm9, ymm13
	vpandn ymm8, ymm8, ymm13
	vmovdqu ymm10, YMMWORD PTR [rcx+64]
	vpor ymm10, ymm10, ymm2
	vpxor ymm8, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rcx+32]
	vpxor ymm13, ymm10, ymm13
	vpandn ymm13, ymm13, ymm1
	vpxor ymm11, ymm11, ymm15
	vpxor ymm11, ymm12, ymm11
	vpxor ymm13, ymm13, ymm11
	vpandn ymm13, ymm2, ymm13
	vpxor ymm7, ymm13, ymm7
	vmovdqu ymm13, YMMWORD PTR [rcx]
	vpxor ymm13, ymm0, ymm13
	vpxor ymm9, ymm5, ymm9
	vpand ymm9, ymm13, ymm9
	vpxor ymm11, ymm14, ymm11
	vpxor ymm11, ymm9, ymm11
	vpandn ymm2, ymm2, ymm3
	vpxor ymm11, ymm2, ymm11
	vmovdqu ymm0, YMMWORD PTR [rcx+96]
	vmovdqa ymm1, ymm8
	vmovdqa ymm2, ymm7
	vmovdqa ymm3, ymm11
	vmovdqu ymm14, YMMWORD PTR [r13+1344]
	vpxor ymm0, ymm0, ymm14
	vmovdqu YMMWORD PTR [r13+1344], ymm0
	vmovdqu ymm14, YMMWORD PTR [r13+1408]
	vpxor ymm1, ymm1, ymm14
	vmovdqu YMMWORD PTR [r13+1408], ymm1
	vmovdqu ymm14, YMMWORD PTR [r13+768]
	vpxor ymm2, ymm2, ymm14
	vmovdqu YMMWORD PTR [r13+768], ymm2
	vmovdqu ymm14, YMMWORD PTR [r13+1216]
	vpxor ymm3, ymm3, ymm14
	vmovdqu YMMWORD PTR [r13+1216], ymm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm5, YMMWORD PTR [r12+64]
	vpxor ymm5, ymm5, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm4, YMMWORD PTR [r12+1792]
	vpxor ymm4, ymm4, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm3, YMMWORD PTR [r12+1536]
	vpxor ymm3, ymm3, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm2, YMMWORD PTR [r12+1280]
	vpxor ymm2, ymm2, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm1, YMMWORD PTR [r12+1024]
	vpxor ymm1, ymm1, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm0, YMMWORD PTR [r12+768]
	vpxor ymm0, ymm0, ymm14
	vpxor ymm6, ymm2, ymm1
	vpxor ymm7, ymm3, ymm6
	vpand ymm8, ymm0, ymm7
	vpand ymm9, ymm2, ymm6
	vpxor ymm10, ymm4, ymm9
	vpand ymm11, ymm8, ymm10
	vpand ymm12, ymm0, ymm9
	vpxor ymm13, ymm3, ymm12
	vpor ymm14, ymm10, ymm13
	vpxor ymm6, ymm0, ymm6
	vmovdqu YMMWORD PTR [rcx], ymm0
	vpxor ymm0, ymm14, ymm6
	vmovdqu YMMWORD PTR [rcx+32], ymm9
	vpandn ymm9, ymm11, ymm5
	vpxor ymm0, ymm9, ymm0
	vpandn ymm7, ymm7, ymm1
	vpor ymm9, ymm10, ymm7
	vpxor ymm13, ymm8, ymm13
	vpxor ymm9, ymm9, ymm13
	vpxor ymm6, ymm8, ymm6
	vpandn ymm2, ymm6, ymm2
	vpandn ymm8, ymm2, ymm10
	vpxor ymm13, ymm1, ymm13
	vpxor ymm13, ymm8, ymm13
	vpandn ymm12, ymm12, ymm6
	vpor ymm2, ymm2, ymm12
	vpxor ymm14, ymm4, ymm14
	vpand ymm14, ymm13, ymm14
	vpxor ymm14, ymm2, ymm14
	vpand ymm6, ymm14, ymm5
	vpxor ymm6, ymm6, ymm13
	vpandn ymm3, ymm3, ymm10
	vpor ymm3, ymm12, ymm3
	vmovdqu ymm12, YMMWORD PTR [rcx+32]
	vpor ymm13, ymm12, ymm13
	vpand ymm13, ymm3, ymm13
	vpxor ymm14, ymm14, ymm13
	vpxor ymm2, ymm7, ymm2
	vmovdqu ymm7, YMMWORD PTR [rcx]
	vpand ymm2, ymm7, ymm2
	vpor ymm2, ymm11, ymm2
	vpxor ymm13, ymm13, ymm2
	vpandn ymm11, ymm5, ymm13
	vpxor ymm11, ymm11, ymm9
	vpand ymm2, ymm4, ymm2
	vpxor ymm9, ymm9, ymm15
	vpxor ymm9, ymm2, ymm9
	vpxor ymm9, ymm13, ymm9
	vpor ymm5, ymm14, ymm5
	vpxor ymm9, ymm5, ymm9
	vmovdqa ymm1, ymm6
	vmovdqa ymm2, ymm9
	vmovdqa ymm3, ymm11
	vmovdqu ymm14, YMMWORD PTR [r13+448]
	vpxor ymm0, ymm0, ymm14
	vmovdqu YMMWORD PTR [r13+448], ymm0
	vmovdqu ymm14, YMMWORD PTR [r13+576]
	vpxor ymm1, ymm1, ymm14
	vmovdqu YMMWORD PTR [r13+576], ymm1
	vmovdqu ymm14, YMMWORD PTR [r13+1152]
	vpxor ymm2, ymm2, ymm14
	vmovdqu YMMWORD PTR [r13+1152], ymm2
	vmovdqu ymm14, YMMWORD PTR [r13]
	vpxor ymm3, ymm3, ymm14
	vmovdqu YMMWORD PTR [r13], ymm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm5, YMMWORD PTR [r12+1024]
	vpxor ymm5, ymm5, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm4, YMMWORD PTR [r12+768]
	vpxor ymm4, ymm4, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm3, YMMWORD PTR [r12+512]
	vpxor ymm3, ymm3, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm2, YMMWORD PTR [r12+256]
	vpxor ymm2, ymm2, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm1, YMMWORD PTR [r12]
	vpxor ymm1, ymm1, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm0, YMMWORD PTR [r12+1984]
	vpxor ymm0, ymm0, ymm14
	vpandn ymm6, ymm4, ymm3
	vpandn ymm7, ymm3, ymm1
	vpxor ymm7, ymm2, ymm7
	vpand ymm8, ymm5, ymm7
	vpandn ymm9, ymm6, ymm8
	vpandn ymm10, ymm7, ymm4
	vpor ymm11, ymm5, ymm10
	vpandn ymm12, ymm3, ymm4
	vpxor ymm12, ymm1, ymm12
	vpand ymm13, ymm11, ymm12
	vpor ymm8, ymm8, ymm13
	vpxor ymm7, ymm7, ymm15
	vpxor ymm7, ymm13, ymm7
	vpandn ymm11, ymm11, ymm3
	vpxor ymm11, ymm7, ymm11
	vpxor ymm6, ymm6, ymm11
	vpor ymm7, ymm9, ymm0
	vpxor ymm7, ymm7, ymm6
	vpxor ymm6, ymm5, ymm6
	vpand ymm3, ymm1, ymm6
	vpxor ymm11, ymm4, ymm11
	vpxor ymm3, ymm3, ymm11
	vpxor ymm10, ymm10, ymm3
	vpxor ymm3, ymm8, ymm3
	vpor ymm3, ymm4, ymm3
	vpxor ymm6, ymm1, ymm6
	vpxor ymm6, ymm3, ymm6
	vpand ymm8, ymm8, ymm0
	vpxor ymm8, ymm8, ymm6
	vpxor ymm12, ymm12, ymm10
	vpor ymm11, ymm2, ymm11
	vpxor ymm11, ymm12, ymm11
	vpxor ymm5, ymm5, ymm11
	vpand ymm5, ymm5, ymm0
	vpxor ymm5, ymm5, ymm10
	vpandn ymm2, ymm2, ymm12
	vpand ymm2, ymm6, ymm2
	vpxor ymm11, ymm9, ymm11
	vpxor ymm11, ymm2, ymm11
	vpor ymm0, ymm11, ymm0
	vpxor ymm10, ymm0, ymm10
	vmovdqa ymm0, ymm5
	vmovdqa ymm1, ymm8
	vmovdqa ymm2, ymm7
	vmovdqa ymm3, ymm10
	vmovdqu ymm14, YMMWORD PTR [r13+832]
	vpxor ymm0, ymm0, ymm14
	vmovdqu YMMWORD PTR [r13+832], ymm0
	vmovdqu ymm14, YMMWORD PTR [r13+384]
	vpxor ymm1, ymm1, ymm14
	vmovdqu YMMWORD PTR [r13+384], ymm1
	vmovdqu ymm14, YMMWORD PTR [r13+1280]
	vpxor ymm2, ymm2, ymm14
	vmovdqu YMMWORD PTR [r13+1280], ymm2
	vmovdqu ymm14, YMMWORD PTR [r13+960]
	vpxor ymm3, ymm3, ymm14
	vmovdqu YMMWORD PTR [r13+960], ymm3
	mov rbx, r12
	mov r12, r13
	mov r13, rbx
	sub r10, 1
	jne 223b
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vmovdqu YMMWORD PTR [rsi], ymm1
	vmovdqu YMMWORD PTR [rsi+32], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+256]
	vmovdqu ymm1, YMMWORD PTR [rsi+288]
	vmovdqu YMMWORD PTR [rsi+256], ymm1
	vmovdqu YMMWORD PTR [rsi+288], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+512]
	vmovdqu ymm1, YMMWORD PTR [rsi+544]
	vmovdqu YMMWORD PTR [rsi+512], ymm1
	vmovdqu YMMWORD PTR [rsi+544], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+768]
	vmovdqu ymm1, YMMWORD PTR [rsi+800]
	vmovdqu YMMWORD PTR [rsi+768], ymm1
	vmovdqu YMMWORD PTR [rsi+800], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1024]
	vmovdqu ymm1, YMMWORD PTR [rsi+1056]
	vmovdqu YMMWORD PTR [rsi+1024], ymm1
	vmovdqu YMMWORD PTR [rsi+1056], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1280]
	vmovdqu ymm1, YMMWORD PTR [rsi+1312]
	vmovdqu YMMWORD PTR [rsi+1280], ymm1
	vmovdqu YMMWORD PTR [rsi+1312], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1536]
	vmovdqu ymm1, YMMWORD PTR [rsi+1568]
	vmovdqu YMMWORD PTR [rsi+1536], ymm1
	vmovdqu YMMWORD PTR [rsi+1568], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1792]
	vmovdqu ymm1, YMMWORD PTR [rsi+1824]
	vmovdqu YMMWORD PTR [rsi+1792], ymm1
	vmovdqu YMMWORD PTR [rsi+1824], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+64]
	vmovdqu ymm1, YMMWORD PTR [rsi+96]
	vmovdqu YMMWORD PTR [rsi+64], ymm1
	vmovdqu YMMWORD PTR [rsi+96], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+320]
	vmovdqu ymm1, YMMWORD PTR [rsi+352]
	vmovdqu YMMWORD PTR [rsi+320], ymm1
	vmovdqu YMMWORD PTR [rsi+352], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+576]
	vmovdqu ymm1, YMMWORD PTR [rsi+608]
	vmovdqu YMMWORD PTR [rsi+576], ymm1
	vmovdqu YMMWORD PTR [rsi+608], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+832]
	vmovdqu ymm1, YMMWORD PTR [rsi+864]
	vmovdqu YMMWORD PTR [rsi+832], ymm1
	vmovdqu YMMWORD PTR [rsi+864], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1088]
	vmovdqu ymm1, YMMWORD PTR [rsi+1120]
	vmovdqu YMMWORD PTR [rsi+1088], ymm1
	vmovdqu YMMWORD PTR [rsi+1120], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1344]
	vmovdqu ymm1, YMMWORD PTR [rsi+1376]
	vmovdqu YMMWORD PTR [rsi+1344], ymm1
	vmovdqu YMMWORD PTR [rsi+1376], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1600]
	vmovdqu ymm1, YMMWORD PTR [rsi+1632]
	vmovdqu YMMWORD PTR [rsi+1600], ymm1
	vmovdqu YMMWORD PTR [rsi+1632], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1856]
	vmovdqu ymm1, YMMWORD PTR [rsi+1888]
	vmovdqu YMMWORD PTR [rsi+1856], ymm1
	vmovdqu YMMWORD PTR [rsi+1888], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+128]
	vmovdqu ymm1, YMMWORD PTR [rsi+160]
	vmovdqu YMMWORD PTR [rsi+128], ymm1
	vmovdqu YMMWORD PTR [rsi+160], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+384]
	vmovdqu ymm1, YMMWORD PTR [rsi+416]
	vmovdqu YMMWORD PTR [rsi+384], ymm1
	vmovdqu YMMWORD PTR [rsi+416], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+640]
	vmovdqu ymm1, YMMWORD PTR [rsi+672]
	vmovdqu YMMWORD PTR [rsi+640], ymm1
	vmovdqu YMMWORD PTR [rsi+672], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+896]
	vmovdqu ymm1, YMMWORD PTR [rsi+928]
	vmovdqu YMMWORD PTR [rsi+896], ymm1
	vmovdqu YMMWORD PTR [rsi+928], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1152]
	vmovdqu ymm1, YMMWORD PTR [rsi+1184]
	vmovdqu YMMWORD PTR [rsi+1152], ymm1
	vmovdqu YMMWORD PTR [rsi+1184], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1408]
	vmovdqu ymm1, YMMWORD PTR [rsi+1440]
	vmovdqu YMMWORD PTR [rsi+1408], ymm1
	vmovdqu YMMWORD PTR [rsi+1440], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1664]
	vmovdqu ymm1, YMMWORD PTR [rsi+1696]
	vmovdqu YMMWORD PTR [rsi+1664], ymm1
	vmovdqu YMMWORD PTR [rsi+1696], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1920]
	vmovdqu ymm1, YMMWORD PTR [rsi+1952]
	vmovdqu YMMWORD PTR [rsi+1920], ymm1
	vmovdqu YMMWORD PTR [rsi+1952], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+192]
	vmovdqu ymm1, YMMWORD PTR [rsi+224]
	vmovdqu YMMWORD PTR [rsi+192], ymm1
	vmovdqu YMMWORD PTR [rsi+224], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+448]
	vmovdqu ymm1, YMMWORD PTR [rsi+480]
	vmovdqu YMMWORD PTR [rsi+448], ymm1
	vmovdqu YMMWORD PTR [rsi+480], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+704]
	vmovdqu ymm1, YMMWORD PTR [rsi+736]
	vmovdqu YMMWORD PTR [rsi+704], ymm1
	vmovdqu YMMWORD PTR [rsi+736], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+960]
	vmovdqu ymm1, YMMWORD PTR [rsi+992]
	vmovdqu YMMWORD PTR [rsi+960], ymm1
	vmovdqu YMMWORD PTR [rsi+992], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1216]
	vmovdqu ymm1, YMMWORD PTR [rsi+1248]
	vmovdqu YMMWORD PTR [rsi+1216], ymm1
	vmovdqu YMMWORD PTR [rsi+1248], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1472]
	vmovdqu ymm1, YMMWORD PTR [rsi+1504]
	vmovdqu YMMWORD PTR [rsi+1472], ymm1
	vmovdqu YMMWORD PTR [rsi+1504], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1728]
	vmovdqu ymm1, YMMWORD PTR [rsi+1760]
	vmovdqu YMMWORD PTR [rsi+1728], ymm1
	vmovdqu YMMWORD PTR [rsi+1760], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1984]
	vmovdqu ymm1, YMMWORD PTR [rsi+2016]
	vmovdqu YMMWORD PTR [rsi+1984], ymm1
	vmovdqu YMMWORD PTR [rsi+2016], ymm0
	sub r11, 1
	jne 218b
	mov r11, 8
224:
	movabs rbx, 4294967295
	vmovq xmm13, rbx
	vpbroadcastq ymm13, xmm13
	movabs rbx, 281470681808895
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	movabs rbx, 71777214294589695
	vmovq xmm15, rbx
	vpbroadcastq ymm15, xmm15
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vmovdqu ymm1, YMMWORD PTR [rsi+256]
	vmovdqu ymm2, YMMWORD PTR [rsi+512]
	vmovdqu ymm3, YMMWORD PTR [rsi+768]
	vmovdqu ymm4, YMMWORD PTR [rsi+1024]
	vmovdqu ymm5, YMMWORD PTR [rsi+1280]
	vmovdqu ymm6, YMMWORD PTR [rsi+1536]
	vmovdqu ymm7, YMMWORD PTR [rsi+1792]
	vpsrlq ymm8, ymm0, 32
	vpxor ymm8, ymm8, ymm4
	vpand ymm8, ymm8, ymm13
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm8, ymm8, 32
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm1, 32
	vpxor ymm8, ymm8, ymm5
	vpand ymm8, ymm8, ymm13
	vpxor ymm5, ymm5, ymm8
	vpsllq ymm8, ymm8, 32
	vpxor ymm1, ymm1, ymm8
	vpsrlq ymm8, ymm2, 32
	vpxor ymm8, ymm8, ymm6
	vpand ymm8, ymm8, ymm13
	vpxor ymm6, ymm6, ymm8
	vpsllq ymm8, ymm8, 32
	vpxor ymm2, ymm2, ymm8
	vpsrlq ymm8, ymm3, 32
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm13
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 32
	vpxor ymm3, ymm3, ymm8
	vpsrlq ymm8, ymm0, 16
	vpxor ymm8, ymm8, ymm2
	vpand ymm8, ymm8, ymm14
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm8, ymm8, 16
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm1, 16
	vpxor ymm8, ymm8, ymm3
	vpand ymm8, ymm8, ymm14
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm8, ymm8, 16
	vpxor ymm1, ymm1, ymm8
	vpsrlq ymm8, ymm4, 16
	vpxor ymm8, ymm8, ymm6
	vpand ymm8, ymm8, ymm14
	vpxor ymm6, ymm6, ymm8
	vpsllq ymm8, ymm8, 16
	vpxor ymm4, ymm4, ymm8
	vpsrlq ymm8, ymm5, 16
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm14
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 16
	vpxor ymm5, ymm5, ymm8
	vpsrlq ymm8, ymm0, 8
	vpxor ymm8, ymm8, ymm1
	vpand ymm8, ymm8, ymm15
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm8, ymm8, 8
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm2, 8
	vpxor ymm8, ymm8, ymm3
	vpand ymm8, ymm8, ymm15
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm8, ymm8, 8
	vpxor ymm2, ymm2, ymm8
	vpsrlq ymm8, ymm4, 8
	vpxor ymm8, ymm8, ymm5
	vpand ymm8, ymm8, ymm15
	vpxor ymm5, ymm5, ymm8
	vpsllq ymm8, ymm8, 8
	vpxor ymm4, ymm4, ymm8
	vpsrlq ymm8, ymm6, 8
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm15
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 8
	vpxor ymm6, ymm6, ymm8
	vmovdqu YMMWORD PTR [rsi], ymm0
	vmovdqu YMMWORD PTR [rsi+256], ymm1
	vmovdqu YMMWORD PTR [rsi+512], ymm2
	vmovdqu YMMWORD PTR [rsi+768], ymm3
	vmovdqu YMMWORD PTR [rsi+1024], ymm4
	vmovdqu YMMWORD PTR [rsi+1280], ymm5
	vmovdqu YMMWORD PTR [rsi+1536], ymm6
	vmovdqu YMMWORD PTR [rsi+1792], ymm7
	add rsi, 32
	sub r11, 1
	jne 224b
	sub rsi, 256
	mov r11, 8
225:
	movabs rbx, 1085102592571150095
	vmovq xmm13, rbx
	vpbroadcastq ymm13, xmm13
	movabs rbx, 3689348814741910323
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	movabs rbx, 6148914691236517205
	vmovq xmm15, rbx
	vpbroadcastq ymm15, xmm15
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vmovdqu ymm2, YMMWORD PTR [rsi+64]
	vmovdqu ymm3, YMMWORD PTR [rsi+96]
	vmovdqu ymm4, YMMWORD PTR [rsi+128]
	vmovdqu ymm5, YMMWORD PTR [rsi+160]
	vmovdqu ymm6, YMMWORD PTR [rsi+192]
	vmovdqu ymm7, YMMWORD PTR [rsi+224]
	vpsrlq ymm8, ymm0, 4
	vpxor ymm8, ymm8, ymm4
	vpand ymm8, ymm8, ymm13
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm8, ymm8, 4
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm1, 4
	vpxor ymm8, ymm8, ymm5
	vpand ymm8, ymm8, ymm13
	vpxor ymm5, ymm5, ymm8
	vpsllq ymm8, ymm8, 4
	vpxor ymm1, ymm1, ymm8
	vpsrlq ymm8, ymm2, 4
	vpxor ymm8, ymm8, ymm6
	vpand ymm8, ymm8, ymm13
	vpxor ymm6, ymm6, ymm8
	vpsllq ymm8, ymm8, 4
	vpxor ymm2, ymm2, ymm8
	vpsrlq ymm8, ymm3, 4
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm13
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 4
	vpxor ymm3, ymm3, ymm8
	vpsrlq ymm8, ymm0, 2
	vpxor ymm8, ymm8, ymm2
	vpand ymm8, ymm8, ymm14
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm8, ymm8, 2
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm1, 2
	vpxor ymm8, ymm8, ymm3
	vpand ymm8, ymm8, ymm14
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm8, ymm8, 2
	vpxor ymm1, ymm1, ymm8
	vpsrlq ymm8, ymm4, 2
	vpxor ymm8, ymm8, ymm6
	vpand ymm8, ymm8, ymm14
	vpxor ymm6, ymm6, ymm8
	vpsllq ymm8, ymm8, 2
	vpxor ymm4, ymm4, ymm8
	vpsrlq ymm8, ymm5, 2
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm14
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 2
	vpxor ymm5, ymm5, ymm8
	vpsrlq ymm8, ymm0, 1
	vpxor ymm8, ymm8, ymm1
	vpand ymm8, ymm8, ymm15
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm8, ymm8, 1
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm2, 1
	vpxor ymm8, ymm8, ymm3
	vpand ymm8, ymm8, ymm15
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm8, ymm8, 1
	vpxor ymm2, ymm2, ymm8
	vpsrlq ymm8, ymm4, 1
	vpxor ymm8, ymm8, ymm5
	vpand ymm8, ymm8, ymm15
	vpxor ymm5, ymm5, ymm8
	vpsllq ymm8, ymm8, 1
	vpxor ymm4, ymm4, ymm8
	vpsrlq ymm8, ymm6, 1
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm15
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 1
	vpxor ymm6, ymm6, ymm8
	vmovdqu YMMWORD PTR [rsi], ymm0
	vmovdqu YMMWORD PTR [rsi+32], ymm1
	vmovdqu YMMWORD PTR [rsi+64], ymm2
	vmovdqu YMMWORD PTR [rsi+96], ymm3
	vmovdqu YMMWORD PTR [rsi+128], ymm4
	vmovdqu YMMWORD PTR [rsi+160], ymm5
	vmovdqu YMMWORD PTR [rsi+192], ymm6
	vmovdqu YMMWORD PTR [rsi+224], ymm7
	add rsi, 256
	sub r11, 1
	jne 225b
	sub rsi, 2048
	add rsi, 2048
	sub rdx, 256
	cmp rdx, 256
	jae 215b
	mov rbx, QWORD PTR [rcx+1016]
	mov r12, QWORD PTR [rcx+1008]
	mov r13, QWORD PTR [rcx+1000]
	vzeroupper
	jmp 214f
213:
214:
	call {vg_triple_des_ecb_decrypt_core}
	mov r11d, 0
	mov QWORD PTR [rsp+8], r11
	mov QWORD PTR [rsp+16], r11
	mov QWORD PTR [rsp+24], r11
	mov QWORD PTR [rsp+32], r11
	mov QWORD PTR [rsp+40], r11
	mov QWORD PTR [rsp+48], r11
	mov QWORD PTR [rsp+56], r11
	mov QWORD PTR [rsp+64], r11
	mov QWORD PTR [rsp+72], r11
	mov QWORD PTR [rsp+80], r11
	mov QWORD PTR [rsp+88], r11
	mov QWORD PTR [rsp+96], r11
	mov QWORD PTR [rsp+104], r11
	mov QWORD PTR [rsp+112], r11
	mov QWORD PTR [rsp+120], r11
	mov QWORD PTR [rsp+128], r11
	mov QWORD PTR [rsp+136], r11
	mov QWORD PTR [rsp+144], r11
	mov QWORD PTR [rsp+152], r11
	mov QWORD PTR [rsp+160], r11
	mov QWORD PTR [rsp+168], r11
	mov QWORD PTR [rsp+176], r11
	mov QWORD PTR [rsp+184], r11
	mov QWORD PTR [rsp+192], r11
	mov QWORD PTR [rsp+200], r11
	mov QWORD PTR [rsp+208], r11
	mov QWORD PTR [rsp+216], r11
	mov QWORD PTR [rsp+224], r11
	mov QWORD PTR [rsp+232], r11
	mov QWORD PTR [rsp+240], r11
	mov QWORD PTR [rsp+248], r11
	mov QWORD PTR [rsp+256], r11
	mov QWORD PTR [rsp+264], r11
	mov QWORD PTR [rsp+272], r11
	mov QWORD PTR [rsp+280], r11
	mov QWORD PTR [rsp+288], r11
	mov QWORD PTR [rsp+296], r11
	mov QWORD PTR [rsp+304], r11
	mov QWORD PTR [rsp+312], r11
	mov QWORD PTR [rsp+320], r11
	mov QWORD PTR [rsp+328], r11
	mov QWORD PTR [rsp+336], r11
	mov QWORD PTR [rsp+344], r11
	mov QWORD PTR [rsp+352], r11
	mov QWORD PTR [rsp+360], r11
	mov QWORD PTR [rsp+368], r11
	mov QWORD PTR [rsp+376], r11
	mov QWORD PTR [rsp+384], r11
	mov QWORD PTR [rsp+392], r11
	mov QWORD PTR [rsp+400], r11
	mov QWORD PTR [rsp+408], r11
	mov QWORD PTR [rsp+416], r11
	mov QWORD PTR [rsp+424], r11
	mov QWORD PTR [rsp+432], r11
	mov QWORD PTR [rsp+440], r11
	mov QWORD PTR [rsp+448], r11
	mov QWORD PTR [rsp+456], r11
	mov QWORD PTR [rsp+464], r11
	mov QWORD PTR [rsp+472], r11
	mov QWORD PTR [rsp+480], r11
	mov QWORD PTR [rsp+488], r11
	mov QWORD PTR [rsp+496], r11
	mov QWORD PTR [rsp+504], r11
	mov QWORD PTR [rsp+512], r11
	mov QWORD PTR [rsp+520], r11
	mov QWORD PTR [rsp+528], r11
	mov QWORD PTR [rsp+536], r11
	mov QWORD PTR [rsp+544], r11
	mov QWORD PTR [rsp+552], r11
	mov QWORD PTR [rsp+560], r11
	mov QWORD PTR [rsp+568], r11
	mov QWORD PTR [rsp+576], r11
	mov QWORD PTR [rsp+584], r11
	mov QWORD PTR [rsp+592], r11
	mov QWORD PTR [rsp+600], r11
	mov QWORD PTR [rsp+608], r11
	mov QWORD PTR [rsp+616], r11
	mov QWORD PTR [rsp+624], r11
	mov QWORD PTR [rsp+632], r11
	mov QWORD PTR [rsp+640], r11
	mov QWORD PTR [rsp+648], r11
	mov QWORD PTR [rsp+656], r11
	mov QWORD PTR [rsp+664], r11
	mov QWORD PTR [rsp+672], r11
	mov QWORD PTR [rsp+680], r11
	mov QWORD PTR [rsp+688], r11
	mov QWORD PTR [rsp+696], r11
	mov QWORD PTR [rsp+704], r11
	mov QWORD PTR [rsp+712], r11
	mov QWORD PTR [rsp+720], r11
	mov QWORD PTR [rsp+728], r11
	mov QWORD PTR [rsp+736], r11
	mov QWORD PTR [rsp+744], r11
	mov QWORD PTR [rsp+752], r11
	mov QWORD PTR [rsp+760], r11
	mov QWORD PTR [rsp+768], r11
	mov QWORD PTR [rsp+776], r11
	mov QWORD PTR [rsp+784], r11
	mov QWORD PTR [rsp+792], r11
	mov QWORD PTR [rsp+800], r11
	mov QWORD PTR [rsp+808], r11
	mov QWORD PTR [rsp+816], r11
	mov QWORD PTR [rsp+824], r11
	mov QWORD PTR [rsp+832], r11
	mov QWORD PTR [rsp+840], r11
	mov QWORD PTR [rsp+848], r11
	mov QWORD PTR [rsp+856], r11
	mov QWORD PTR [rsp+864], r11
	mov QWORD PTR [rsp+872], r11
	mov QWORD PTR [rsp+880], r11
	mov QWORD PTR [rsp+888], r11
	mov QWORD PTR [rsp+896], r11
	mov QWORD PTR [rsp+904], r11
	mov QWORD PTR [rsp+912], r11
	mov QWORD PTR [rsp+920], r11
	mov QWORD PTR [rsp+928], r11
	mov QWORD PTR [rsp+936], r11
	mov QWORD PTR [rsp+944], r11
	mov QWORD PTR [rsp+952], r11
	mov QWORD PTR [rsp+960], r11
	mov QWORD PTR [rsp+968], r11
	mov QWORD PTR [rsp+976], r11
	mov QWORD PTR [rsp+984], r11
	mov QWORD PTR [rsp+992], r11
	mov QWORD PTR [rsp+1000], r11
	mov QWORD PTR [rsp+1008], r11
	mov QWORD PTR [rsp+1016], r11
	mov QWORD PTR [rsp+1024], r11
	lea rsp, [rsp+1032]
	ret
	.p2align 6
