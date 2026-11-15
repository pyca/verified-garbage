// The functions of `src/internal/vg_sm4_ctr32.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_ctr32:
	lea rsp, [rsp-3208]
	mov r8, rsp
	add r8, 8
	mov r9, r8
	mov QWORD PTR [r9+3136], rbx
	mov QWORD PTR [r9+3144], rbp
	mov QWORD PTR [r9+3152], r12
	mov QWORD PTR [r9+3160], r13
	mov QWORD PTR [r9+3168], r14
	mov QWORD PTR [r9+3176], r15
	mov rax, QWORD PTR [rsi]
	bswap rax
	mov rbx, QWORD PTR [rsi+8]
	bswap rbx
	mov QWORD PTR [r9+3184], rax
	mov QWORD PTR [r9+3192], rbx
	mov eax, ebx
	add eax, ecx
	shr rbx, 32
	shl rbx, 32
	add rbx, rax
	mov rax, QWORD PTR [r9+3184]
	bswap rax
	bswap rbx
	mov QWORD PTR [rsi+8], rbx
	mov QWORD PTR [rsi], rax
	mov rdx, rdx
	mov r8, rcx
	movabs r14, 71777214294589695
	mov QWORD PTR [r9+384], r14
	movabs r14, -71777214294589696
	mov QWORD PTR [r9+392], r14
	movabs r14, 281470681808895
	mov QWORD PTR [r9+400], r14
	mov rsi, r9
	add rsi, 1024
	movabs r15, 16
20:
	mov rax, QWORD PTR [rdi]
	movabs r14, 4294901760
	mov QWORD PTR [r9+8], r14
	movabs r14, 280375465148160
	mov QWORD PTR [r9+16], r14
	movabs r14, 71777214294589695
	mov QWORD PTR [r9+24], r14
	movabs r14, 6148914691236517205
	mov QWORD PTR [r9+32], r14
	movabs r14, 3689348814741910323
	mov QWORD PTR [r9+40], r14
	movabs r14, 1085102592571150095
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	shr r14, 16
	xor r14, rax
	and r14, QWORD PTR [r9+8]
	xor rax, r14
	ror r14, 48
	xor rax, r14
	mov r14, rax
	shr r14, 8
	xor r14, rax
	and r14, QWORD PTR [r9+16]
	xor rax, r14
	ror r14, 56
	xor rax, r14
	mov rbx, rax
	mov rcx, rax
	mov rbp, rax
	mov r10, rax
	mov r11, rax
	mov r12, rax
	mov r13, rax
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+32]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+32]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+32]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+32]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+40]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+40]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+40]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+40]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+48]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+48]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+48]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+48]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	and rax, QWORD PTR [r9+384]
	mov r14, rax
	ror r14, 56
	xor rax, r14
	ror rax, 32
	mov r14, rax
	shr r14, 16
	xor r14, rax
	and r14, QWORD PTR [r9+400]
	xor rax, r14
	ror r14, 48
	xor rax, r14
	and rbx, QWORD PTR [r9+384]
	mov r14, rbx
	ror r14, 56
	xor rbx, r14
	ror rbx, 32
	mov r14, rbx
	shr r14, 16
	xor r14, rbx
	and r14, QWORD PTR [r9+400]
	xor rbx, r14
	ror r14, 48
	xor rbx, r14
	and rcx, QWORD PTR [r9+384]
	mov r14, rcx
	ror r14, 56
	xor rcx, r14
	ror rcx, 32
	mov r14, rcx
	shr r14, 16
	xor r14, rcx
	and r14, QWORD PTR [r9+400]
	xor rcx, r14
	ror r14, 48
	xor rcx, r14
	and rbp, QWORD PTR [r9+384]
	mov r14, rbp
	ror r14, 56
	xor rbp, r14
	ror rbp, 32
	mov r14, rbp
	shr r14, 16
	xor r14, rbp
	and r14, QWORD PTR [r9+400]
	xor rbp, r14
	ror r14, 48
	xor rbp, r14
	and r10, QWORD PTR [r9+384]
	mov r14, r10
	ror r14, 56
	xor r10, r14
	ror r10, 32
	mov r14, r10
	shr r14, 16
	xor r14, r10
	and r14, QWORD PTR [r9+400]
	xor r10, r14
	ror r14, 48
	xor r10, r14
	and r11, QWORD PTR [r9+384]
	mov r14, r11
	ror r14, 56
	xor r11, r14
	ror r11, 32
	mov r14, r11
	shr r14, 16
	xor r14, r11
	and r14, QWORD PTR [r9+400]
	xor r11, r14
	ror r14, 48
	xor r11, r14
	and r12, QWORD PTR [r9+384]
	mov r14, r12
	ror r14, 56
	xor r12, r14
	ror r12, 32
	mov r14, r12
	shr r14, 16
	xor r14, r12
	and r14, QWORD PTR [r9+400]
	xor r12, r14
	ror r14, 48
	xor r12, r14
	and r13, QWORD PTR [r9+384]
	mov r14, r13
	ror r14, 56
	xor r13, r14
	ror r13, 32
	mov r14, r13
	shr r14, 16
	xor r14, r13
	and r14, QWORD PTR [r9+400]
	xor r13, r14
	ror r14, 48
	xor r13, r14
	mov QWORD PTR [rsi], rax
	mov QWORD PTR [rsi+8], rbx
	mov QWORD PTR [rsi+16], rcx
	mov QWORD PTR [rsi+24], rbp
	mov QWORD PTR [rsi+32], r10
	mov QWORD PTR [rsi+40], r11
	mov QWORD PTR [rsi+48], r12
	mov QWORD PTR [rsi+56], r13
	add rsi, 64
	mov rax, QWORD PTR [rdi]
	movabs r14, 4294901760
	mov QWORD PTR [r9+8], r14
	movabs r14, 280375465148160
	mov QWORD PTR [r9+16], r14
	movabs r14, 71777214294589695
	mov QWORD PTR [r9+24], r14
	movabs r14, 6148914691236517205
	mov QWORD PTR [r9+32], r14
	movabs r14, 3689348814741910323
	mov QWORD PTR [r9+40], r14
	movabs r14, 1085102592571150095
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	shr r14, 16
	xor r14, rax
	and r14, QWORD PTR [r9+8]
	xor rax, r14
	ror r14, 48
	xor rax, r14
	mov r14, rax
	shr r14, 8
	xor r14, rax
	and r14, QWORD PTR [r9+16]
	xor rax, r14
	ror r14, 56
	xor rax, r14
	mov rbx, rax
	mov rcx, rax
	mov rbp, rax
	mov r10, rax
	mov r11, rax
	mov r12, rax
	mov r13, rax
	mov r14, rax
	shr r14, 1
	xor r14, rbx
	and r14, QWORD PTR [r9+32]
	xor rbx, r14
	ror r14, 63
	xor rax, r14
	mov r14, rcx
	shr r14, 1
	xor r14, rbp
	and r14, QWORD PTR [r9+32]
	xor rbp, r14
	ror r14, 63
	xor rcx, r14
	mov r14, r10
	shr r14, 1
	xor r14, r11
	and r14, QWORD PTR [r9+32]
	xor r11, r14
	ror r14, 63
	xor r10, r14
	mov r14, r12
	shr r14, 1
	xor r14, r13
	and r14, QWORD PTR [r9+32]
	xor r13, r14
	ror r14, 63
	xor r12, r14
	mov r14, rax
	shr r14, 2
	xor r14, rcx
	and r14, QWORD PTR [r9+40]
	xor rcx, r14
	ror r14, 62
	xor rax, r14
	mov r14, rbx
	shr r14, 2
	xor r14, rbp
	and r14, QWORD PTR [r9+40]
	xor rbp, r14
	ror r14, 62
	xor rbx, r14
	mov r14, r10
	shr r14, 2
	xor r14, r12
	and r14, QWORD PTR [r9+40]
	xor r12, r14
	ror r14, 62
	xor r10, r14
	mov r14, r11
	shr r14, 2
	xor r14, r13
	and r14, QWORD PTR [r9+40]
	xor r13, r14
	ror r14, 62
	xor r11, r14
	mov r14, rax
	shr r14, 4
	xor r14, r10
	and r14, QWORD PTR [r9+48]
	xor r10, r14
	ror r14, 60
	xor rax, r14
	mov r14, rbx
	shr r14, 4
	xor r14, r11
	and r14, QWORD PTR [r9+48]
	xor r11, r14
	ror r14, 60
	xor rbx, r14
	mov r14, rcx
	shr r14, 4
	xor r14, r12
	and r14, QWORD PTR [r9+48]
	xor r12, r14
	ror r14, 60
	xor rcx, r14
	mov r14, rbp
	shr r14, 4
	xor r14, r13
	and r14, QWORD PTR [r9+48]
	xor r13, r14
	ror r14, 60
	xor rbp, r14
	and rax, QWORD PTR [r9+392]
	mov r14, rax
	ror r14, 8
	xor rax, r14
	ror rax, 32
	mov r14, rax
	shr r14, 16
	xor r14, rax
	and r14, QWORD PTR [r9+400]
	xor rax, r14
	ror r14, 48
	xor rax, r14
	and rbx, QWORD PTR [r9+392]
	mov r14, rbx
	ror r14, 8
	xor rbx, r14
	ror rbx, 32
	mov r14, rbx
	shr r14, 16
	xor r14, rbx
	and r14, QWORD PTR [r9+400]
	xor rbx, r14
	ror r14, 48
	xor rbx, r14
	and rcx, QWORD PTR [r9+392]
	mov r14, rcx
	ror r14, 8
	xor rcx, r14
	ror rcx, 32
	mov r14, rcx
	shr r14, 16
	xor r14, rcx
	and r14, QWORD PTR [r9+400]
	xor rcx, r14
	ror r14, 48
	xor rcx, r14
	and rbp, QWORD PTR [r9+392]
	mov r14, rbp
	ror r14, 8
	xor rbp, r14
	ror rbp, 32
	mov r14, rbp
	shr r14, 16
	xor r14, rbp
	and r14, QWORD PTR [r9+400]
	xor rbp, r14
	ror r14, 48
	xor rbp, r14
	and r10, QWORD PTR [r9+392]
	mov r14, r10
	ror r14, 8
	xor r10, r14
	ror r10, 32
	mov r14, r10
	shr r14, 16
	xor r14, r10
	and r14, QWORD PTR [r9+400]
	xor r10, r14
	ror r14, 48
	xor r10, r14
	and r11, QWORD PTR [r9+392]
	mov r14, r11
	ror r14, 8
	xor r11, r14
	ror r11, 32
	mov r14, r11
	shr r14, 16
	xor r14, r11
	and r14, QWORD PTR [r9+400]
	xor r11, r14
	ror r14, 48
	xor r11, r14
	and r12, QWORD PTR [r9+392]
	mov r14, r12
	ror r14, 8
	xor r12, r14
	ror r12, 32
	mov r14, r12
	shr r14, 16
	xor r14, r12
	and r14, QWORD PTR [r9+400]
	xor r12, r14
	ror r14, 48
	xor r12, r14
	and r13, QWORD PTR [r9+392]
	mov r14, r13
	ror r14, 8
	xor r13, r14
	ror r13, 32
	mov r14, r13
	shr r14, 16
	xor r14, r13
	and r14, QWORD PTR [r9+400]
	xor r13, r14
	ror r14, 48
	xor r13, r14
	mov QWORD PTR [rsi], rax
	mov QWORD PTR [rsi+8], rbx
	mov QWORD PTR [rsi+16], rcx
	mov QWORD PTR [rsi+24], rbp
	mov QWORD PTR [rsi+32], r10
	mov QWORD PTR [rsi+40], r11
	mov QWORD PTR [rsi+48], r12
	mov QWORD PTR [rsi+56], r13
	add rsi, 64
	add rdi, 8
	sub r15, 1
	jne 20b
	mov rdi, r9
	add rdi, 3072
	test r8, r8
	je 21f
23:
	mov rax, QWORD PTR [r9+3184]
	mov rbx, QWORD PTR [r9+3192]
	mov rcx, rax
	bswap rcx
	mov QWORD PTR [r9+768], rcx
	mov rcx, rbx
	bswap rcx
	mov QWORD PTR [r9+776], rcx
	mov ecx, ebx
	add ecx, 1
	shr rbx, 32
	shl rbx, 32
	add rbx, rcx
	mov rcx, rax
	bswap rcx
	mov QWORD PTR [r9+784], rcx
	mov rcx, rbx
	bswap rcx
	mov QWORD PTR [r9+792], rcx
	mov ecx, ebx
	add ecx, 1
	shr rbx, 32
	shl rbx, 32
	add rbx, rcx
	mov rcx, rax
	bswap rcx
	mov QWORD PTR [r9+800], rcx
	mov rcx, rbx
	bswap rcx
	mov QWORD PTR [r9+808], rcx
	mov ecx, ebx
	add ecx, 1
	shr rbx, 32
	shl rbx, 32
	add rbx, rcx
	mov rcx, rax
	bswap rcx
	mov QWORD PTR [r9+816], rcx
	mov rcx, rbx
	bswap rcx
	mov QWORD PTR [r9+824], rcx
	mov ecx, ebx
	add ecx, 1
	shr rbx, 32
	shl rbx, 32
	add rbx, rcx
	mov rcx, rax
	bswap rcx
	mov QWORD PTR [r9+832], rcx
	mov rcx, rbx
	bswap rcx
	mov QWORD PTR [r9+840], rcx
	mov ecx, ebx
	add ecx, 1
	shr rbx, 32
	shl rbx, 32
	add rbx, rcx
	mov rcx, rax
	bswap rcx
	mov QWORD PTR [r9+848], rcx
	mov rcx, rbx
	bswap rcx
	mov QWORD PTR [r9+856], rcx
	mov ecx, ebx
	add ecx, 1
	shr rbx, 32
	shl rbx, 32
	add rbx, rcx
	mov rcx, rax
	bswap rcx
	mov QWORD PTR [r9+864], rcx
	mov rcx, rbx
	bswap rcx
	mov QWORD PTR [r9+872], rcx
	mov ecx, ebx
	add ecx, 1
	shr rbx, 32
	shl rbx, 32
	add rbx, rcx
	mov rcx, rax
	bswap rcx
	mov QWORD PTR [r9+880], rcx
	mov rcx, rbx
	bswap rcx
	mov QWORD PTR [r9+888], rcx
	mov ecx, ebx
	add ecx, 1
	shr rbx, 32
	shl rbx, 32
	add rbx, rcx
	mov rcx, rax
	bswap rcx
	mov QWORD PTR [r9+896], rcx
	mov rcx, rbx
	bswap rcx
	mov QWORD PTR [r9+904], rcx
	mov ecx, ebx
	add ecx, 1
	shr rbx, 32
	shl rbx, 32
	add rbx, rcx
	mov rcx, rax
	bswap rcx
	mov QWORD PTR [r9+912], rcx
	mov rcx, rbx
	bswap rcx
	mov QWORD PTR [r9+920], rcx
	mov ecx, ebx
	add ecx, 1
	shr rbx, 32
	shl rbx, 32
	add rbx, rcx
	mov rcx, rax
	bswap rcx
	mov QWORD PTR [r9+928], rcx
	mov rcx, rbx
	bswap rcx
	mov QWORD PTR [r9+936], rcx
	mov ecx, ebx
	add ecx, 1
	shr rbx, 32
	shl rbx, 32
	add rbx, rcx
	mov rcx, rax
	bswap rcx
	mov QWORD PTR [r9+944], rcx
	mov rcx, rbx
	bswap rcx
	mov QWORD PTR [r9+952], rcx
	mov ecx, ebx
	add ecx, 1
	shr rbx, 32
	shl rbx, 32
	add rbx, rcx
	mov rcx, rax
	bswap rcx
	mov QWORD PTR [r9+960], rcx
	mov rcx, rbx
	bswap rcx
	mov QWORD PTR [r9+968], rcx
	mov ecx, ebx
	add ecx, 1
	shr rbx, 32
	shl rbx, 32
	add rbx, rcx
	mov rcx, rax
	bswap rcx
	mov QWORD PTR [r9+976], rcx
	mov rcx, rbx
	bswap rcx
	mov QWORD PTR [r9+984], rcx
	mov ecx, ebx
	add ecx, 1
	shr rbx, 32
	shl rbx, 32
	add rbx, rcx
	mov rcx, rax
	bswap rcx
	mov QWORD PTR [r9+992], rcx
	mov rcx, rbx
	bswap rcx
	mov QWORD PTR [r9+1000], rcx
	mov ecx, ebx
	add ecx, 1
	shr rbx, 32
	shl rbx, 32
	add rbx, rcx
	mov rcx, rax
	bswap rcx
	mov QWORD PTR [r9+1008], rcx
	mov rcx, rbx
	bswap rcx
	mov QWORD PTR [r9+1016], rcx
	mov ecx, ebx
	add ecx, 1
	shr rbx, 32
	shl rbx, 32
	add rbx, rcx
	mov QWORD PTR [r9+3184], rax
	mov QWORD PTR [r9+3192], rbx
	mov rdi, r9
	movabs rsi, 392
	call {vg_sm4_crypt_prepared}
	movabs rcx, 16
	cmp r8, 16
	jb 24f
	jmp 25f
24:
	mov rcx, r8
25:
	mov rax, r9
	add rax, 768
	mov rbx, rdx
	mov r10, rcx
26:
	mov rbp, QWORD PTR [rax]
	xor rbp, QWORD PTR [rbx]
	mov QWORD PTR [rbx], rbp
	mov rbp, QWORD PTR [rax+8]
	xor rbp, QWORD PTR [rbx+8]
	mov QWORD PTR [rbx+8], rbp
	add rax, 16
	add rbx, 16
	sub rcx, 1
	jne 26b
	mov rdx, rbx
	sub r8, r10
	jne 23b
	jmp 22f
21:
22:
	mov rbx, QWORD PTR [r9+3136]
	mov rbp, QWORD PTR [r9+3144]
	mov r12, QWORD PTR [r9+3152]
	mov r13, QWORD PTR [r9+3160]
	mov r14, QWORD PTR [r9+3168]
	mov r15, QWORD PTR [r9+3176]
	lea rsp, [rsp+3208]
	ret
	.p2align 6
