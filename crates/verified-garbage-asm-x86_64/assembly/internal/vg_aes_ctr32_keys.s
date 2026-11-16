// The functions of `src/internal/vg_aes_ctr32_keys.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ctr32_keys:
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
	add rsi, 1408
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
	mov rbx, QWORD PTR [r9+384]
	mov rbp, QWORD PTR [r9+392]
	mov r12, QWORD PTR [r9+400]
	mov r13, QWORD PTR [r9+408]
	mov r14, QWORD PTR [r9+416]
	mov r15, QWORD PTR [r9+424]
	ret
	.p2align 6
