// The functions of `src/internal/vg_aes_decrypt_blocks.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_decrypt_blocks:
	mov r9, r8
	mov r8, rcx
	mov QWORD PTR [r9+384], rbx
	mov QWORD PTR [r9+392], rbp
	mov QWORD PTR [r9+400], r12
	mov QWORD PTR [r9+408], r13
	mov QWORD PTR [r9+416], r14
	mov QWORD PTR [r9+424], r15
	mov r15, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rdi, rsi
	mov rsi, r9
	add rsi, 1920
20:
	mov rax, QWORD PTR [rdi]
	mov r10, QWORD PTR [rdi+8]
	mov rbx, rax
	mov rcx, rax
	mov rbp, rax
	mov r11, r10
	mov r12, r10
	mov r13, r10
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
	mov r14, rbx
	shr r14, 16
	xor r14, rbx
	and r14, QWORD PTR [r9+8]
	xor rbx, r14
	ror r14, 48
	xor rbx, r14
	mov r14, rcx
	shr r14, 16
	xor r14, rcx
	and r14, QWORD PTR [r9+8]
	xor rcx, r14
	ror r14, 48
	xor rcx, r14
	mov r14, rbp
	shr r14, 16
	xor r14, rbp
	and r14, QWORD PTR [r9+8]
	xor rbp, r14
	ror r14, 48
	xor rbp, r14
	mov r14, r10
	shr r14, 16
	xor r14, r10
	and r14, QWORD PTR [r9+8]
	xor r10, r14
	ror r14, 48
	xor r10, r14
	mov r14, r11
	shr r14, 16
	xor r14, r11
	and r14, QWORD PTR [r9+8]
	xor r11, r14
	ror r14, 48
	xor r11, r14
	mov r14, r12
	shr r14, 16
	xor r14, r12
	and r14, QWORD PTR [r9+8]
	xor r12, r14
	ror r14, 48
	xor r12, r14
	mov r14, r13
	shr r14, 16
	xor r14, r13
	and r14, QWORD PTR [r9+8]
	xor r13, r14
	ror r14, 48
	xor r13, r14
	mov r14, rax
	shr r14, 8
	xor r14, rax
	and r14, QWORD PTR [r9+16]
	xor rax, r14
	ror r14, 56
	xor rax, r14
	mov r14, rbx
	shr r14, 8
	xor r14, rbx
	and r14, QWORD PTR [r9+16]
	xor rbx, r14
	ror r14, 56
	xor rbx, r14
	mov r14, rcx
	shr r14, 8
	xor r14, rcx
	and r14, QWORD PTR [r9+16]
	xor rcx, r14
	ror r14, 56
	xor rcx, r14
	mov r14, rbp
	shr r14, 8
	xor r14, rbp
	and r14, QWORD PTR [r9+16]
	xor rbp, r14
	ror r14, 56
	xor rbp, r14
	mov r14, r10
	shr r14, 8
	xor r14, r10
	and r14, QWORD PTR [r9+16]
	xor r10, r14
	ror r14, 56
	xor r10, r14
	mov r14, r11
	shr r14, 8
	xor r14, r11
	and r14, QWORD PTR [r9+16]
	xor r11, r14
	ror r14, 56
	xor r11, r14
	mov r14, r12
	shr r14, 8
	xor r14, r12
	and r14, QWORD PTR [r9+16]
	xor r12, r14
	ror r14, 56
	xor r12, r14
	mov r14, r13
	shr r14, 8
	xor r14, r13
	and r14, QWORD PTR [r9+16]
	xor r13, r14
	ror r14, 56
	xor r13, r14
	mov r14, rax
	shr r14, 8
	xor r14, r10
	and r14, QWORD PTR [r9+24]
	xor r10, r14
	ror r14, 56
	xor rax, r14
	mov r14, rbx
	shr r14, 8
	xor r14, r11
	and r14, QWORD PTR [r9+24]
	xor r11, r14
	ror r14, 56
	xor rbx, r14
	mov r14, rcx
	shr r14, 8
	xor r14, r12
	and r14, QWORD PTR [r9+24]
	xor r12, r14
	ror r14, 56
	xor rcx, r14
	mov r14, rbp
	shr r14, 8
	xor r14, r13
	and r14, QWORD PTR [r9+24]
	xor r13, r14
	ror r14, 56
	xor rbp, r14
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
	mov QWORD PTR [rsi], rax
	mov QWORD PTR [rsi+8], rbx
	mov QWORD PTR [rsi+16], rcx
	mov QWORD PTR [rsi+24], rbp
	mov QWORD PTR [rsi+32], r10
	mov QWORD PTR [rsi+40], r11
	mov QWORD PTR [rsi+48], r12
	mov QWORD PTR [rsi+56], r13
	sub rdi, 16
	sub rsi, 64
	sub r15, 1
	jae 20b
	mov rdi, rsi
	add rdi, 64
	test r8, r8
	je 21f
23:
	cmp r8, 4
	jae 24f
	mov rax, QWORD PTR [rdx]
	mov r10, QWORD PTR [rdx+8]
	cmp r8, 2
	jae 26f
	jmp 27f
26:
	mov rbx, QWORD PTR [rdx+16]
	mov r11, QWORD PTR [rdx+24]
	cmp r8, 3
	jae 28f
	jmp 29f
28:
	mov rcx, QWORD PTR [rdx+32]
	mov r12, QWORD PTR [rdx+40]
29:
27:
	jmp 25f
24:
	mov rax, QWORD PTR [rdx]
	mov r10, QWORD PTR [rdx+8]
	mov rbx, QWORD PTR [rdx+16]
	mov r11, QWORD PTR [rdx+24]
	mov rcx, QWORD PTR [rdx+32]
	mov r12, QWORD PTR [rdx+40]
	mov rbp, QWORD PTR [rdx+48]
	mov r13, QWORD PTR [rdx+56]
25:
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
	mov r14, rbx
	shr r14, 16
	xor r14, rbx
	and r14, QWORD PTR [r9+8]
	xor rbx, r14
	ror r14, 48
	xor rbx, r14
	mov r14, rcx
	shr r14, 16
	xor r14, rcx
	and r14, QWORD PTR [r9+8]
	xor rcx, r14
	ror r14, 48
	xor rcx, r14
	mov r14, rbp
	shr r14, 16
	xor r14, rbp
	and r14, QWORD PTR [r9+8]
	xor rbp, r14
	ror r14, 48
	xor rbp, r14
	mov r14, r10
	shr r14, 16
	xor r14, r10
	and r14, QWORD PTR [r9+8]
	xor r10, r14
	ror r14, 48
	xor r10, r14
	mov r14, r11
	shr r14, 16
	xor r14, r11
	and r14, QWORD PTR [r9+8]
	xor r11, r14
	ror r14, 48
	xor r11, r14
	mov r14, r12
	shr r14, 16
	xor r14, r12
	and r14, QWORD PTR [r9+8]
	xor r12, r14
	ror r14, 48
	xor r12, r14
	mov r14, r13
	shr r14, 16
	xor r14, r13
	and r14, QWORD PTR [r9+8]
	xor r13, r14
	ror r14, 48
	xor r13, r14
	mov r14, rax
	shr r14, 8
	xor r14, rax
	and r14, QWORD PTR [r9+16]
	xor rax, r14
	ror r14, 56
	xor rax, r14
	mov r14, rbx
	shr r14, 8
	xor r14, rbx
	and r14, QWORD PTR [r9+16]
	xor rbx, r14
	ror r14, 56
	xor rbx, r14
	mov r14, rcx
	shr r14, 8
	xor r14, rcx
	and r14, QWORD PTR [r9+16]
	xor rcx, r14
	ror r14, 56
	xor rcx, r14
	mov r14, rbp
	shr r14, 8
	xor r14, rbp
	and r14, QWORD PTR [r9+16]
	xor rbp, r14
	ror r14, 56
	xor rbp, r14
	mov r14, r10
	shr r14, 8
	xor r14, r10
	and r14, QWORD PTR [r9+16]
	xor r10, r14
	ror r14, 56
	xor r10, r14
	mov r14, r11
	shr r14, 8
	xor r14, r11
	and r14, QWORD PTR [r9+16]
	xor r11, r14
	ror r14, 56
	xor r11, r14
	mov r14, r12
	shr r14, 8
	xor r14, r12
	and r14, QWORD PTR [r9+16]
	xor r12, r14
	ror r14, 56
	xor r12, r14
	mov r14, r13
	shr r14, 8
	xor r14, r13
	and r14, QWORD PTR [r9+16]
	xor r13, r14
	ror r14, 56
	xor r13, r14
	mov r14, rax
	shr r14, 8
	xor r14, r10
	and r14, QWORD PTR [r9+24]
	xor r10, r14
	ror r14, 56
	xor rax, r14
	mov r14, rbx
	shr r14, 8
	xor r14, r11
	and r14, QWORD PTR [r9+24]
	xor r11, r14
	ror r14, 56
	xor rbx, r14
	mov r14, rcx
	shr r14, 8
	xor r14, r12
	and r14, QWORD PTR [r9+24]
	xor r12, r14
	ror r14, 56
	xor rcx, r14
	mov r14, rbp
	shr r14, 8
	xor r14, r13
	and r14, QWORD PTR [r9+24]
	xor r13, r14
	ror r14, 56
	xor rbp, r14
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
	mov rsi, r9
	add rsi, 1920
	xor rax, QWORD PTR [rsi]
	xor rbx, QWORD PTR [rsi+8]
	xor rcx, QWORD PTR [rsi+16]
	xor rbp, QWORD PTR [rsi+24]
	xor r10, QWORD PTR [rsi+32]
	xor r11, QWORD PTR [rsi+40]
	xor r12, QWORD PTR [rsi+48]
	xor r13, QWORD PTR [rsi+56]
210:
	sub rsi, 64
	movabs r14, 281470681808895
	mov QWORD PTR [r9+8], r14
	movabs r14, -4503595333451776
	mov QWORD PTR [r9+16], r14
	movabs r14, 4222124651642880
	mov QWORD PTR [r9+24], r14
	movabs r14, 4294967295
	mov QWORD PTR [r9+32], r14
	movabs r14, 71777214277877760
	mov QWORD PTR [r9+40], r14
	movabs r14, -71777218572845056
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	ror r14, 60
	and r14, QWORD PTR [r9+16]
	mov r15, rax
	ror r15, 12
	and r15, QWORD PTR [r9+24]
	and rax, QWORD PTR [r9+8]
	xor rax, r14
	xor rax, r15
	mov r14, rax
	ror r14, 8
	and r14, QWORD PTR [r9+40]
	mov r15, rax
	ror r15, 56
	and r15, QWORD PTR [r9+48]
	and rax, QWORD PTR [r9+32]
	xor rax, r14
	xor rax, r15
	mov r14, rbx
	ror r14, 60
	and r14, QWORD PTR [r9+16]
	mov r15, rbx
	ror r15, 12
	and r15, QWORD PTR [r9+24]
	and rbx, QWORD PTR [r9+8]
	xor rbx, r14
	xor rbx, r15
	mov r14, rbx
	ror r14, 8
	and r14, QWORD PTR [r9+40]
	mov r15, rbx
	ror r15, 56
	and r15, QWORD PTR [r9+48]
	and rbx, QWORD PTR [r9+32]
	xor rbx, r14
	xor rbx, r15
	mov r14, rcx
	ror r14, 60
	and r14, QWORD PTR [r9+16]
	mov r15, rcx
	ror r15, 12
	and r15, QWORD PTR [r9+24]
	and rcx, QWORD PTR [r9+8]
	xor rcx, r14
	xor rcx, r15
	mov r14, rcx
	ror r14, 8
	and r14, QWORD PTR [r9+40]
	mov r15, rcx
	ror r15, 56
	and r15, QWORD PTR [r9+48]
	and rcx, QWORD PTR [r9+32]
	xor rcx, r14
	xor rcx, r15
	mov r14, rbp
	ror r14, 60
	and r14, QWORD PTR [r9+16]
	mov r15, rbp
	ror r15, 12
	and r15, QWORD PTR [r9+24]
	and rbp, QWORD PTR [r9+8]
	xor rbp, r14
	xor rbp, r15
	mov r14, rbp
	ror r14, 8
	and r14, QWORD PTR [r9+40]
	mov r15, rbp
	ror r15, 56
	and r15, QWORD PTR [r9+48]
	and rbp, QWORD PTR [r9+32]
	xor rbp, r14
	xor rbp, r15
	mov r14, r10
	ror r14, 60
	and r14, QWORD PTR [r9+16]
	mov r15, r10
	ror r15, 12
	and r15, QWORD PTR [r9+24]
	and r10, QWORD PTR [r9+8]
	xor r10, r14
	xor r10, r15
	mov r14, r10
	ror r14, 8
	and r14, QWORD PTR [r9+40]
	mov r15, r10
	ror r15, 56
	and r15, QWORD PTR [r9+48]
	and r10, QWORD PTR [r9+32]
	xor r10, r14
	xor r10, r15
	mov r14, r11
	ror r14, 60
	and r14, QWORD PTR [r9+16]
	mov r15, r11
	ror r15, 12
	and r15, QWORD PTR [r9+24]
	and r11, QWORD PTR [r9+8]
	xor r11, r14
	xor r11, r15
	mov r14, r11
	ror r14, 8
	and r14, QWORD PTR [r9+40]
	mov r15, r11
	ror r15, 56
	and r15, QWORD PTR [r9+48]
	and r11, QWORD PTR [r9+32]
	xor r11, r14
	xor r11, r15
	mov r14, r12
	ror r14, 60
	and r14, QWORD PTR [r9+16]
	mov r15, r12
	ror r15, 12
	and r15, QWORD PTR [r9+24]
	and r12, QWORD PTR [r9+8]
	xor r12, r14
	xor r12, r15
	mov r14, r12
	ror r14, 8
	and r14, QWORD PTR [r9+40]
	mov r15, r12
	ror r15, 56
	and r15, QWORD PTR [r9+48]
	and r12, QWORD PTR [r9+32]
	xor r12, r14
	xor r12, r15
	mov r14, r13
	ror r14, 60
	and r14, QWORD PTR [r9+16]
	mov r15, r13
	ror r15, 12
	and r15, QWORD PTR [r9+24]
	and r13, QWORD PTR [r9+8]
	xor r13, r14
	xor r13, r15
	mov r14, r13
	ror r14, 8
	and r14, QWORD PTR [r9+40]
	mov r15, r13
	ror r15, 56
	and r15, QWORD PTR [r9+48]
	and r13, QWORD PTR [r9+32]
	xor r13, r14
	xor r13, r15
	movabs r14, -1
	mov QWORD PTR [r9], r14
	mov QWORD PTR [r9+160], rax
	mov QWORD PTR [r9+168], rbx
	mov QWORD PTR [r9+176], rcx
	mov QWORD PTR [r9+184], rbp
	mov QWORD PTR [r9+192], r10
	mov QWORD PTR [r9+200], r11
	mov QWORD PTR [r9+208], r12
	mov QWORD PTR [r9+216], r13
	mov rax, QWORD PTR [r9+176]
	xor rax, QWORD PTR [r9+200]
	xor rax, QWORD PTR [r9+216]
	xor rax, QWORD PTR [r9]
	mov rbx, QWORD PTR [r9+184]
	xor rbx, QWORD PTR [r9+208]
	xor rbx, QWORD PTR [r9+160]
	mov rcx, QWORD PTR [r9+192]
	xor rcx, QWORD PTR [r9+216]
	xor rcx, QWORD PTR [r9+168]
	xor rcx, QWORD PTR [r9]
	mov rbp, QWORD PTR [r9+200]
	xor rbp, QWORD PTR [r9+160]
	xor rbp, QWORD PTR [r9+176]
	mov r10, QWORD PTR [r9+208]
	xor r10, QWORD PTR [r9+168]
	xor r10, QWORD PTR [r9+184]
	mov r11, QWORD PTR [r9+216]
	xor r11, QWORD PTR [r9+176]
	xor r11, QWORD PTR [r9+192]
	mov r12, QWORD PTR [r9+160]
	xor r12, QWORD PTR [r9+184]
	xor r12, QWORD PTR [r9+200]
	mov r13, QWORD PTR [r9+168]
	xor r13, QWORD PTR [r9+192]
	xor r13, QWORD PTR [r9+208]
	movabs r14, -1
	mov QWORD PTR [r9], r14
	mov r14, r10
	xor r14, rcx
	mov r15, r13
	xor r15, rbx
	mov QWORD PTR [r9+8], rbp
	mov rbp, r13
	xor rbp, r10
	mov QWORD PTR [r9+16], rbp
	mov rbp, r13
	xor rbp, rcx
	xor r11, r12
	mov QWORD PTR [r9+24], r12
	mov r12, r11
	xor r12, rax
	xor r10, r12
	mov QWORD PTR [r9+32], r10
	mov r10, r15
	xor r10, r14
	mov QWORD PTR [r9+40], r14
	mov r14, r12
	xor r14, r13
	xor rbx, r12
	mov QWORD PTR [r9+48], r14
	mov r14, rbx
	xor r14, rbp
	mov QWORD PTR [r9+56], rbx
	mov rbx, QWORD PTR [r9+8]
	xor rbx, r10
	xor rcx, rbx
	xor rbx, QWORD PTR [r9+24]
	mov QWORD PTR [r9+24], r12
	mov r12, rcx
	xor r12, rax
	mov QWORD PTR [r9+8], r12
	mov r12, rcx
	xor r12, r11
	mov QWORD PTR [r9+64], r14
	mov r14, rbx
	xor r14, QWORD PTR [r9+16]
	mov QWORD PTR [r9+72], rbx
	mov rbx, rax
	xor rbx, r14
	mov QWORD PTR [r9+80], rbx
	mov rbx, r12
	xor rbx, r14
	mov QWORD PTR [r9+88], rbx
	mov rbx, r12
	xor rbx, rbp
	xor r11, r14
	mov QWORD PTR [r9+96], rbx
	mov rbx, r15
	xor rbx, r11
	xor r13, r11
	mov QWORD PTR [r9+104], r13
	mov r13, r10
	and r13, rcx
	mov QWORD PTR [r9+112], r10
	mov r10, QWORD PTR [r9+64]
	and r10, QWORD PTR [r9+8]
	xor r10, r13
	mov QWORD PTR [r9+120], rcx
	mov rcx, QWORD PTR [r9+32]
	and rcx, rax
	xor rcx, r13
	mov r13, r15
	and r13, r11
	mov QWORD PTR [r9+128], r15
	mov r15, QWORD PTR [r9+56]
	and r15, QWORD PTR [r9+24]
	xor r15, r13
	mov QWORD PTR [r9+136], r11
	mov r11, QWORD PTR [r9+48]
	and r11, QWORD PTR [r9+80]
	xor r11, r13
	mov r13, QWORD PTR [r9+16]
	and r13, r14
	mov QWORD PTR [r9+144], r14
	mov r14, QWORD PTR [r9+40]
	and r14, QWORD PTR [r9+88]
	xor r14, r13
	mov QWORD PTR [r9+152], rax
	mov rax, rbp
	and rax, r12
	xor rax, r13
	xor r10, r14
	xor rcx, rax
	xor r15, r14
	xor r11, rax
	xor r10, QWORD PTR [r9+72]
	xor rcx, QWORD PTR [r9+96]
	xor r15, rbx
	xor r11, QWORD PTR [r9+104]
	mov rbx, r10
	xor rbx, rcx
	and r10, r15
	mov rax, r11
	xor rax, r10
	mov r14, rbx
	and r14, rax
	xor r14, rcx
	mov r13, r15
	xor r13, r11
	xor rcx, r10
	and rcx, r13
	xor rcx, r11
	xor r15, rcx
	mov r13, rax
	xor r13, rcx
	and r11, r13
	xor r15, r11
	xor rax, r11
	and rax, r14
	xor rbx, rax
	mov rax, rbx
	xor rax, r15
	mov r11, r14
	xor r11, rcx
	mov r13, r14
	xor r13, rbx
	mov r10, rcx
	xor r10, r15
	mov QWORD PTR [r9+104], rbp
	mov rbp, r11
	xor rbp, rax
	mov QWORD PTR [r9+96], rax
	mov rax, r10
	and rax, QWORD PTR [r9+120]
	mov QWORD PTR [r9+120], rax
	mov rax, r15
	and rax, QWORD PTR [r9+8]
	mov QWORD PTR [r9+8], rax
	mov rax, rcx
	and rax, QWORD PTR [r9+152]
	mov QWORD PTR [r9+152], rax
	mov rax, r13
	and rax, QWORD PTR [r9+136]
	mov QWORD PTR [r9+136], rax
	mov rax, rbx
	and rax, QWORD PTR [r9+24]
	mov QWORD PTR [r9+24], rax
	mov rax, r14
	and rax, QWORD PTR [r9+80]
	mov QWORD PTR [r9+80], rax
	mov rax, r11
	and rax, QWORD PTR [r9+144]
	mov QWORD PTR [r9+144], rax
	mov rax, rbp
	and rax, QWORD PTR [r9+88]
	and r12, QWORD PTR [r9+96]
	and r10, QWORD PTR [r9+112]
	and r15, QWORD PTR [r9+64]
	and rcx, QWORD PTR [r9+32]
	and r13, QWORD PTR [r9+128]
	and rbx, QWORD PTR [r9+56]
	and r14, QWORD PTR [r9+48]
	and r11, QWORD PTR [r9+16]
	and rbp, QWORD PTR [r9+40]
	mov QWORD PTR [r9+40], r14
	mov r14, QWORD PTR [r9+96]
	and r14, QWORD PTR [r9+104]
	xor r11, rbp
	xor rcx, r15
	xor rbx, QWORD PTR [r9+80]
	xor r10, r15
	mov r15, QWORD PTR [r9+152]
	xor r15, r13
	mov QWORD PTR [r9+104], rcx
	mov rcx, QWORD PTR [r9+152]
	xor rcx, QWORD PTR [r9+80]
	xor r12, rax
	mov QWORD PTR [r9+80], rcx
	mov rcx, QWORD PTR [r9+120]
	xor rcx, QWORD PTR [r9+136]
	xor rax, QWORD PTR [r9+144]
	xor rbp, r14
	xor r13, rbx
	xor r15, rcx
	mov r14, QWORD PTR [r9+24]
	xor r14, r11
	xor rax, QWORD PTR [r9+136]
	xor r11, r15
	xor r15, QWORD PTR [r9+40]
	xor r12, r14
	xor r10, r14
	mov r14, QWORD PTR [r9+24]
	xor r14, rax
	xor r15, r12
	mov QWORD PTR [r9+24], rbp
	mov rbp, QWORD PTR [r9+8]
	xor rbp, r10
	xor rax, r10
	xor r13, r12
	xor r13, QWORD PTR [r9]
	xor rbx, r11
	xor rbx, QWORD PTR [r9]
	mov r11, r14
	xor r11, r15
	xor rcx, rbp
	xor rbp, QWORD PTR [r9+80]
	xor r15, QWORD PTR [r9+104]
	xor r14, rcx
	xor r14, QWORD PTR [r9]
	xor r11, QWORD PTR [r9+24]
	xor r11, QWORD PTR [r9]
	mov QWORD PTR [r9+24], r13
	mov r13, rax
	mov r12, r14
	mov r10, rcx
	mov rcx, r15
	mov QWORD PTR [r9+104], rbx
	mov rbx, QWORD PTR [r9+24]
	mov rax, QWORD PTR [r9+104]
	movabs r14, -1
	mov QWORD PTR [r9], r14
	mov QWORD PTR [r9+160], rax
	mov QWORD PTR [r9+168], rbx
	mov QWORD PTR [r9+176], rcx
	mov QWORD PTR [r9+184], rbp
	mov QWORD PTR [r9+192], r10
	mov QWORD PTR [r9+200], r11
	mov QWORD PTR [r9+208], r12
	mov QWORD PTR [r9+216], r13
	mov rax, QWORD PTR [r9+176]
	xor rax, QWORD PTR [r9+200]
	xor rax, QWORD PTR [r9+216]
	xor rax, QWORD PTR [r9]
	mov rbx, QWORD PTR [r9+184]
	xor rbx, QWORD PTR [r9+208]
	xor rbx, QWORD PTR [r9+160]
	mov rcx, QWORD PTR [r9+192]
	xor rcx, QWORD PTR [r9+216]
	xor rcx, QWORD PTR [r9+168]
	xor rcx, QWORD PTR [r9]
	mov rbp, QWORD PTR [r9+200]
	xor rbp, QWORD PTR [r9+160]
	xor rbp, QWORD PTR [r9+176]
	mov r10, QWORD PTR [r9+208]
	xor r10, QWORD PTR [r9+168]
	xor r10, QWORD PTR [r9+184]
	mov r11, QWORD PTR [r9+216]
	xor r11, QWORD PTR [r9+176]
	xor r11, QWORD PTR [r9+192]
	mov r12, QWORD PTR [r9+160]
	xor r12, QWORD PTR [r9+184]
	xor r12, QWORD PTR [r9+200]
	mov r13, QWORD PTR [r9+168]
	xor r13, QWORD PTR [r9+192]
	xor r13, QWORD PTR [r9+208]
	xor rax, QWORD PTR [rsi]
	xor rbx, QWORD PTR [rsi+8]
	xor rcx, QWORD PTR [rsi+16]
	xor rbp, QWORD PTR [rsi+24]
	xor r10, QWORD PTR [rsi+32]
	xor r11, QWORD PTR [rsi+40]
	xor r12, QWORD PTR [rsi+48]
	xor r13, QWORD PTR [rsi+56]
	mov r14, rax
	ror r14, 32
	xor r14, rax
	mov QWORD PTR [r9+160], r14
	mov r14, rbx
	ror r14, 32
	xor r14, rbx
	mov QWORD PTR [r9+168], r14
	mov r14, rcx
	ror r14, 32
	xor r14, rcx
	mov QWORD PTR [r9+176], r14
	mov r14, rbp
	ror r14, 32
	xor r14, rbp
	mov QWORD PTR [r9+184], r14
	mov r14, r10
	ror r14, 32
	xor r14, r10
	mov QWORD PTR [r9+192], r14
	mov r14, r11
	ror r14, 32
	xor r14, r11
	mov QWORD PTR [r9+200], r14
	mov r14, r12
	ror r14, 32
	xor r14, r12
	mov QWORD PTR [r9+208], r14
	mov r14, r13
	ror r14, 32
	xor r14, r13
	mov QWORD PTR [r9+216], r14
	xor rax, QWORD PTR [r9+208]
	xor rbx, QWORD PTR [r9+208]
	xor rbx, QWORD PTR [r9+216]
	xor rcx, QWORD PTR [r9+160]
	xor rcx, QWORD PTR [r9+216]
	xor rbp, QWORD PTR [r9+168]
	xor rbp, QWORD PTR [r9+208]
	xor r10, QWORD PTR [r9+176]
	xor r10, QWORD PTR [r9+208]
	xor r10, QWORD PTR [r9+216]
	xor r11, QWORD PTR [r9+184]
	xor r11, QWORD PTR [r9+216]
	xor r12, QWORD PTR [r9+192]
	xor r13, QWORD PTR [r9+200]
	mov r14, r13
	ror r14, 16
	xor r14, r13
	mov QWORD PTR [r9+56], r14
	mov r14, rax
	ror r14, 16
	xor rax, r14
	xor r14, QWORD PTR [r9+56]
	ror rax, 32
	xor r14, rax
	ror rax, 32
	mov r15, rbx
	ror r15, 16
	xor rbx, r15
	xor r15, rax
	xor r15, QWORD PTR [r9+56]
	ror rbx, 32
	xor r15, rbx
	ror rbx, 32
	mov rax, rcx
	ror rax, 16
	xor rcx, rax
	xor rax, rbx
	ror rcx, 32
	xor rax, rcx
	ror rcx, 32
	mov rbx, rbp
	ror rbx, 16
	xor rbp, rbx
	xor rbx, rcx
	xor rbx, QWORD PTR [r9+56]
	ror rbp, 32
	xor rbx, rbp
	ror rbp, 32
	mov rcx, r10
	ror rcx, 16
	xor r10, rcx
	xor rcx, rbp
	xor rcx, QWORD PTR [r9+56]
	ror r10, 32
	xor rcx, r10
	ror r10, 32
	mov rbp, r11
	ror rbp, 16
	xor r11, rbp
	xor rbp, r10
	ror r11, 32
	xor rbp, r11
	ror r11, 32
	mov r10, r12
	ror r10, 16
	xor r12, r10
	xor r10, r11
	ror r12, 32
	xor r10, r12
	ror r12, 32
	mov r11, r13
	ror r11, 16
	xor r13, r11
	xor r11, r12
	ror r13, 32
	xor r11, r13
	ror r13, 32
	mov r13, r11
	mov r12, r10
	mov r11, rbp
	mov r10, rcx
	mov rbp, rbx
	mov rcx, rax
	mov rbx, r15
	mov rax, r14
	mov r14, rdi
	add r14, 64
	cmp rsi, r14
	jne 210b
	sub rsi, 64
	movabs r14, 281470681808895
	mov QWORD PTR [r9+8], r14
	movabs r14, -4503595333451776
	mov QWORD PTR [r9+16], r14
	movabs r14, 4222124651642880
	mov QWORD PTR [r9+24], r14
	movabs r14, 4294967295
	mov QWORD PTR [r9+32], r14
	movabs r14, 71777214277877760
	mov QWORD PTR [r9+40], r14
	movabs r14, -71777218572845056
	mov QWORD PTR [r9+48], r14
	mov r14, rax
	ror r14, 60
	and r14, QWORD PTR [r9+16]
	mov r15, rax
	ror r15, 12
	and r15, QWORD PTR [r9+24]
	and rax, QWORD PTR [r9+8]
	xor rax, r14
	xor rax, r15
	mov r14, rax
	ror r14, 8
	and r14, QWORD PTR [r9+40]
	mov r15, rax
	ror r15, 56
	and r15, QWORD PTR [r9+48]
	and rax, QWORD PTR [r9+32]
	xor rax, r14
	xor rax, r15
	mov r14, rbx
	ror r14, 60
	and r14, QWORD PTR [r9+16]
	mov r15, rbx
	ror r15, 12
	and r15, QWORD PTR [r9+24]
	and rbx, QWORD PTR [r9+8]
	xor rbx, r14
	xor rbx, r15
	mov r14, rbx
	ror r14, 8
	and r14, QWORD PTR [r9+40]
	mov r15, rbx
	ror r15, 56
	and r15, QWORD PTR [r9+48]
	and rbx, QWORD PTR [r9+32]
	xor rbx, r14
	xor rbx, r15
	mov r14, rcx
	ror r14, 60
	and r14, QWORD PTR [r9+16]
	mov r15, rcx
	ror r15, 12
	and r15, QWORD PTR [r9+24]
	and rcx, QWORD PTR [r9+8]
	xor rcx, r14
	xor rcx, r15
	mov r14, rcx
	ror r14, 8
	and r14, QWORD PTR [r9+40]
	mov r15, rcx
	ror r15, 56
	and r15, QWORD PTR [r9+48]
	and rcx, QWORD PTR [r9+32]
	xor rcx, r14
	xor rcx, r15
	mov r14, rbp
	ror r14, 60
	and r14, QWORD PTR [r9+16]
	mov r15, rbp
	ror r15, 12
	and r15, QWORD PTR [r9+24]
	and rbp, QWORD PTR [r9+8]
	xor rbp, r14
	xor rbp, r15
	mov r14, rbp
	ror r14, 8
	and r14, QWORD PTR [r9+40]
	mov r15, rbp
	ror r15, 56
	and r15, QWORD PTR [r9+48]
	and rbp, QWORD PTR [r9+32]
	xor rbp, r14
	xor rbp, r15
	mov r14, r10
	ror r14, 60
	and r14, QWORD PTR [r9+16]
	mov r15, r10
	ror r15, 12
	and r15, QWORD PTR [r9+24]
	and r10, QWORD PTR [r9+8]
	xor r10, r14
	xor r10, r15
	mov r14, r10
	ror r14, 8
	and r14, QWORD PTR [r9+40]
	mov r15, r10
	ror r15, 56
	and r15, QWORD PTR [r9+48]
	and r10, QWORD PTR [r9+32]
	xor r10, r14
	xor r10, r15
	mov r14, r11
	ror r14, 60
	and r14, QWORD PTR [r9+16]
	mov r15, r11
	ror r15, 12
	and r15, QWORD PTR [r9+24]
	and r11, QWORD PTR [r9+8]
	xor r11, r14
	xor r11, r15
	mov r14, r11
	ror r14, 8
	and r14, QWORD PTR [r9+40]
	mov r15, r11
	ror r15, 56
	and r15, QWORD PTR [r9+48]
	and r11, QWORD PTR [r9+32]
	xor r11, r14
	xor r11, r15
	mov r14, r12
	ror r14, 60
	and r14, QWORD PTR [r9+16]
	mov r15, r12
	ror r15, 12
	and r15, QWORD PTR [r9+24]
	and r12, QWORD PTR [r9+8]
	xor r12, r14
	xor r12, r15
	mov r14, r12
	ror r14, 8
	and r14, QWORD PTR [r9+40]
	mov r15, r12
	ror r15, 56
	and r15, QWORD PTR [r9+48]
	and r12, QWORD PTR [r9+32]
	xor r12, r14
	xor r12, r15
	mov r14, r13
	ror r14, 60
	and r14, QWORD PTR [r9+16]
	mov r15, r13
	ror r15, 12
	and r15, QWORD PTR [r9+24]
	and r13, QWORD PTR [r9+8]
	xor r13, r14
	xor r13, r15
	mov r14, r13
	ror r14, 8
	and r14, QWORD PTR [r9+40]
	mov r15, r13
	ror r15, 56
	and r15, QWORD PTR [r9+48]
	and r13, QWORD PTR [r9+32]
	xor r13, r14
	xor r13, r15
	movabs r14, -1
	mov QWORD PTR [r9], r14
	mov QWORD PTR [r9+160], rax
	mov QWORD PTR [r9+168], rbx
	mov QWORD PTR [r9+176], rcx
	mov QWORD PTR [r9+184], rbp
	mov QWORD PTR [r9+192], r10
	mov QWORD PTR [r9+200], r11
	mov QWORD PTR [r9+208], r12
	mov QWORD PTR [r9+216], r13
	mov rax, QWORD PTR [r9+176]
	xor rax, QWORD PTR [r9+200]
	xor rax, QWORD PTR [r9+216]
	xor rax, QWORD PTR [r9]
	mov rbx, QWORD PTR [r9+184]
	xor rbx, QWORD PTR [r9+208]
	xor rbx, QWORD PTR [r9+160]
	mov rcx, QWORD PTR [r9+192]
	xor rcx, QWORD PTR [r9+216]
	xor rcx, QWORD PTR [r9+168]
	xor rcx, QWORD PTR [r9]
	mov rbp, QWORD PTR [r9+200]
	xor rbp, QWORD PTR [r9+160]
	xor rbp, QWORD PTR [r9+176]
	mov r10, QWORD PTR [r9+208]
	xor r10, QWORD PTR [r9+168]
	xor r10, QWORD PTR [r9+184]
	mov r11, QWORD PTR [r9+216]
	xor r11, QWORD PTR [r9+176]
	xor r11, QWORD PTR [r9+192]
	mov r12, QWORD PTR [r9+160]
	xor r12, QWORD PTR [r9+184]
	xor r12, QWORD PTR [r9+200]
	mov r13, QWORD PTR [r9+168]
	xor r13, QWORD PTR [r9+192]
	xor r13, QWORD PTR [r9+208]
	movabs r14, -1
	mov QWORD PTR [r9], r14
	mov r14, r10
	xor r14, rcx
	mov r15, r13
	xor r15, rbx
	mov QWORD PTR [r9+8], rbp
	mov rbp, r13
	xor rbp, r10
	mov QWORD PTR [r9+16], rbp
	mov rbp, r13
	xor rbp, rcx
	xor r11, r12
	mov QWORD PTR [r9+24], r12
	mov r12, r11
	xor r12, rax
	xor r10, r12
	mov QWORD PTR [r9+32], r10
	mov r10, r15
	xor r10, r14
	mov QWORD PTR [r9+40], r14
	mov r14, r12
	xor r14, r13
	xor rbx, r12
	mov QWORD PTR [r9+48], r14
	mov r14, rbx
	xor r14, rbp
	mov QWORD PTR [r9+56], rbx
	mov rbx, QWORD PTR [r9+8]
	xor rbx, r10
	xor rcx, rbx
	xor rbx, QWORD PTR [r9+24]
	mov QWORD PTR [r9+24], r12
	mov r12, rcx
	xor r12, rax
	mov QWORD PTR [r9+8], r12
	mov r12, rcx
	xor r12, r11
	mov QWORD PTR [r9+64], r14
	mov r14, rbx
	xor r14, QWORD PTR [r9+16]
	mov QWORD PTR [r9+72], rbx
	mov rbx, rax
	xor rbx, r14
	mov QWORD PTR [r9+80], rbx
	mov rbx, r12
	xor rbx, r14
	mov QWORD PTR [r9+88], rbx
	mov rbx, r12
	xor rbx, rbp
	xor r11, r14
	mov QWORD PTR [r9+96], rbx
	mov rbx, r15
	xor rbx, r11
	xor r13, r11
	mov QWORD PTR [r9+104], r13
	mov r13, r10
	and r13, rcx
	mov QWORD PTR [r9+112], r10
	mov r10, QWORD PTR [r9+64]
	and r10, QWORD PTR [r9+8]
	xor r10, r13
	mov QWORD PTR [r9+120], rcx
	mov rcx, QWORD PTR [r9+32]
	and rcx, rax
	xor rcx, r13
	mov r13, r15
	and r13, r11
	mov QWORD PTR [r9+128], r15
	mov r15, QWORD PTR [r9+56]
	and r15, QWORD PTR [r9+24]
	xor r15, r13
	mov QWORD PTR [r9+136], r11
	mov r11, QWORD PTR [r9+48]
	and r11, QWORD PTR [r9+80]
	xor r11, r13
	mov r13, QWORD PTR [r9+16]
	and r13, r14
	mov QWORD PTR [r9+144], r14
	mov r14, QWORD PTR [r9+40]
	and r14, QWORD PTR [r9+88]
	xor r14, r13
	mov QWORD PTR [r9+152], rax
	mov rax, rbp
	and rax, r12
	xor rax, r13
	xor r10, r14
	xor rcx, rax
	xor r15, r14
	xor r11, rax
	xor r10, QWORD PTR [r9+72]
	xor rcx, QWORD PTR [r9+96]
	xor r15, rbx
	xor r11, QWORD PTR [r9+104]
	mov rbx, r10
	xor rbx, rcx
	and r10, r15
	mov rax, r11
	xor rax, r10
	mov r14, rbx
	and r14, rax
	xor r14, rcx
	mov r13, r15
	xor r13, r11
	xor rcx, r10
	and rcx, r13
	xor rcx, r11
	xor r15, rcx
	mov r13, rax
	xor r13, rcx
	and r11, r13
	xor r15, r11
	xor rax, r11
	and rax, r14
	xor rbx, rax
	mov rax, rbx
	xor rax, r15
	mov r11, r14
	xor r11, rcx
	mov r13, r14
	xor r13, rbx
	mov r10, rcx
	xor r10, r15
	mov QWORD PTR [r9+104], rbp
	mov rbp, r11
	xor rbp, rax
	mov QWORD PTR [r9+96], rax
	mov rax, r10
	and rax, QWORD PTR [r9+120]
	mov QWORD PTR [r9+120], rax
	mov rax, r15
	and rax, QWORD PTR [r9+8]
	mov QWORD PTR [r9+8], rax
	mov rax, rcx
	and rax, QWORD PTR [r9+152]
	mov QWORD PTR [r9+152], rax
	mov rax, r13
	and rax, QWORD PTR [r9+136]
	mov QWORD PTR [r9+136], rax
	mov rax, rbx
	and rax, QWORD PTR [r9+24]
	mov QWORD PTR [r9+24], rax
	mov rax, r14
	and rax, QWORD PTR [r9+80]
	mov QWORD PTR [r9+80], rax
	mov rax, r11
	and rax, QWORD PTR [r9+144]
	mov QWORD PTR [r9+144], rax
	mov rax, rbp
	and rax, QWORD PTR [r9+88]
	and r12, QWORD PTR [r9+96]
	and r10, QWORD PTR [r9+112]
	and r15, QWORD PTR [r9+64]
	and rcx, QWORD PTR [r9+32]
	and r13, QWORD PTR [r9+128]
	and rbx, QWORD PTR [r9+56]
	and r14, QWORD PTR [r9+48]
	and r11, QWORD PTR [r9+16]
	and rbp, QWORD PTR [r9+40]
	mov QWORD PTR [r9+40], r14
	mov r14, QWORD PTR [r9+96]
	and r14, QWORD PTR [r9+104]
	xor r11, rbp
	xor rcx, r15
	xor rbx, QWORD PTR [r9+80]
	xor r10, r15
	mov r15, QWORD PTR [r9+152]
	xor r15, r13
	mov QWORD PTR [r9+104], rcx
	mov rcx, QWORD PTR [r9+152]
	xor rcx, QWORD PTR [r9+80]
	xor r12, rax
	mov QWORD PTR [r9+80], rcx
	mov rcx, QWORD PTR [r9+120]
	xor rcx, QWORD PTR [r9+136]
	xor rax, QWORD PTR [r9+144]
	xor rbp, r14
	xor r13, rbx
	xor r15, rcx
	mov r14, QWORD PTR [r9+24]
	xor r14, r11
	xor rax, QWORD PTR [r9+136]
	xor r11, r15
	xor r15, QWORD PTR [r9+40]
	xor r12, r14
	xor r10, r14
	mov r14, QWORD PTR [r9+24]
	xor r14, rax
	xor r15, r12
	mov QWORD PTR [r9+24], rbp
	mov rbp, QWORD PTR [r9+8]
	xor rbp, r10
	xor rax, r10
	xor r13, r12
	xor r13, QWORD PTR [r9]
	xor rbx, r11
	xor rbx, QWORD PTR [r9]
	mov r11, r14
	xor r11, r15
	xor rcx, rbp
	xor rbp, QWORD PTR [r9+80]
	xor r15, QWORD PTR [r9+104]
	xor r14, rcx
	xor r14, QWORD PTR [r9]
	xor r11, QWORD PTR [r9+24]
	xor r11, QWORD PTR [r9]
	mov QWORD PTR [r9+24], r13
	mov r13, rax
	mov r12, r14
	mov r10, rcx
	mov rcx, r15
	mov QWORD PTR [r9+104], rbx
	mov rbx, QWORD PTR [r9+24]
	mov rax, QWORD PTR [r9+104]
	movabs r14, -1
	mov QWORD PTR [r9], r14
	mov QWORD PTR [r9+160], rax
	mov QWORD PTR [r9+168], rbx
	mov QWORD PTR [r9+176], rcx
	mov QWORD PTR [r9+184], rbp
	mov QWORD PTR [r9+192], r10
	mov QWORD PTR [r9+200], r11
	mov QWORD PTR [r9+208], r12
	mov QWORD PTR [r9+216], r13
	mov rax, QWORD PTR [r9+176]
	xor rax, QWORD PTR [r9+200]
	xor rax, QWORD PTR [r9+216]
	xor rax, QWORD PTR [r9]
	mov rbx, QWORD PTR [r9+184]
	xor rbx, QWORD PTR [r9+208]
	xor rbx, QWORD PTR [r9+160]
	mov rcx, QWORD PTR [r9+192]
	xor rcx, QWORD PTR [r9+216]
	xor rcx, QWORD PTR [r9+168]
	xor rcx, QWORD PTR [r9]
	mov rbp, QWORD PTR [r9+200]
	xor rbp, QWORD PTR [r9+160]
	xor rbp, QWORD PTR [r9+176]
	mov r10, QWORD PTR [r9+208]
	xor r10, QWORD PTR [r9+168]
	xor r10, QWORD PTR [r9+184]
	mov r11, QWORD PTR [r9+216]
	xor r11, QWORD PTR [r9+176]
	xor r11, QWORD PTR [r9+192]
	mov r12, QWORD PTR [r9+160]
	xor r12, QWORD PTR [r9+184]
	xor r12, QWORD PTR [r9+200]
	mov r13, QWORD PTR [r9+168]
	xor r13, QWORD PTR [r9+192]
	xor r13, QWORD PTR [r9+208]
	xor rax, QWORD PTR [rsi]
	xor rbx, QWORD PTR [rsi+8]
	xor rcx, QWORD PTR [rsi+16]
	xor rbp, QWORD PTR [rsi+24]
	xor r10, QWORD PTR [rsi+32]
	xor r11, QWORD PTR [rsi+40]
	xor r12, QWORD PTR [rsi+48]
	xor r13, QWORD PTR [rsi+56]
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
	mov r14, rax
	shr r14, 8
	xor r14, r10
	and r14, QWORD PTR [r9+24]
	xor r10, r14
	ror r14, 56
	xor rax, r14
	mov r14, rbx
	shr r14, 8
	xor r14, r11
	and r14, QWORD PTR [r9+24]
	xor r11, r14
	ror r14, 56
	xor rbx, r14
	mov r14, rcx
	shr r14, 8
	xor r14, r12
	and r14, QWORD PTR [r9+24]
	xor r12, r14
	ror r14, 56
	xor rcx, r14
	mov r14, rbp
	shr r14, 8
	xor r14, r13
	and r14, QWORD PTR [r9+24]
	xor r13, r14
	ror r14, 56
	xor rbp, r14
	mov r14, rax
	shr r14, 8
	xor r14, rax
	and r14, QWORD PTR [r9+16]
	xor rax, r14
	ror r14, 56
	xor rax, r14
	mov r14, rbx
	shr r14, 8
	xor r14, rbx
	and r14, QWORD PTR [r9+16]
	xor rbx, r14
	ror r14, 56
	xor rbx, r14
	mov r14, rcx
	shr r14, 8
	xor r14, rcx
	and r14, QWORD PTR [r9+16]
	xor rcx, r14
	ror r14, 56
	xor rcx, r14
	mov r14, rbp
	shr r14, 8
	xor r14, rbp
	and r14, QWORD PTR [r9+16]
	xor rbp, r14
	ror r14, 56
	xor rbp, r14
	mov r14, r10
	shr r14, 8
	xor r14, r10
	and r14, QWORD PTR [r9+16]
	xor r10, r14
	ror r14, 56
	xor r10, r14
	mov r14, r11
	shr r14, 8
	xor r14, r11
	and r14, QWORD PTR [r9+16]
	xor r11, r14
	ror r14, 56
	xor r11, r14
	mov r14, r12
	shr r14, 8
	xor r14, r12
	and r14, QWORD PTR [r9+16]
	xor r12, r14
	ror r14, 56
	xor r12, r14
	mov r14, r13
	shr r14, 8
	xor r14, r13
	and r14, QWORD PTR [r9+16]
	xor r13, r14
	ror r14, 56
	xor r13, r14
	mov r14, rax
	shr r14, 16
	xor r14, rax
	and r14, QWORD PTR [r9+8]
	xor rax, r14
	ror r14, 48
	xor rax, r14
	mov r14, rbx
	shr r14, 16
	xor r14, rbx
	and r14, QWORD PTR [r9+8]
	xor rbx, r14
	ror r14, 48
	xor rbx, r14
	mov r14, rcx
	shr r14, 16
	xor r14, rcx
	and r14, QWORD PTR [r9+8]
	xor rcx, r14
	ror r14, 48
	xor rcx, r14
	mov r14, rbp
	shr r14, 16
	xor r14, rbp
	and r14, QWORD PTR [r9+8]
	xor rbp, r14
	ror r14, 48
	xor rbp, r14
	mov r14, r10
	shr r14, 16
	xor r14, r10
	and r14, QWORD PTR [r9+8]
	xor r10, r14
	ror r14, 48
	xor r10, r14
	mov r14, r11
	shr r14, 16
	xor r14, r11
	and r14, QWORD PTR [r9+8]
	xor r11, r14
	ror r14, 48
	xor r11, r14
	mov r14, r12
	shr r14, 16
	xor r14, r12
	and r14, QWORD PTR [r9+8]
	xor r12, r14
	ror r14, 48
	xor r12, r14
	mov r14, r13
	shr r14, 16
	xor r14, r13
	and r14, QWORD PTR [r9+8]
	xor r13, r14
	ror r14, 48
	xor r13, r14
	cmp r8, 4
	jae 211f
	mov QWORD PTR [rdx], rax
	mov QWORD PTR [rdx+8], r10
	cmp r8, 2
	jae 213f
	jmp 214f
213:
	mov QWORD PTR [rdx+16], rbx
	mov QWORD PTR [rdx+24], r11
	cmp r8, 3
	jae 215f
	jmp 216f
215:
	mov QWORD PTR [rdx+32], rcx
	mov QWORD PTR [rdx+40], r12
216:
214:
	sub r8, r8
	jmp 212f
211:
	mov QWORD PTR [rdx], rax
	mov QWORD PTR [rdx+8], r10
	mov QWORD PTR [rdx+16], rbx
	mov QWORD PTR [rdx+24], r11
	mov QWORD PTR [rdx+32], rcx
	mov QWORD PTR [rdx+40], r12
	mov QWORD PTR [rdx+48], rbp
	mov QWORD PTR [rdx+56], r13
	add rdx, 64
	sub r8, 4
212:
	jne 23b
	jmp 22f
21:
22:
	mov rbx, QWORD PTR [r9+384]
	mov rbp, QWORD PTR [r9+392]
	mov r12, QWORD PTR [r9+400]
	mov r13, QWORD PTR [r9+408]
	mov r14, QWORD PTR [r9+416]
	mov r15, QWORD PTR [r9+424]
	ret
	.p2align 6
