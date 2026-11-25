// The functions of `src/internal/vg_aes_expand_key_scratch.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_expand_key_scratch:
	mov r9, rcx
	mov QWORD PTR [r9+384], rbx
	mov QWORD PTR [r9+392], rbp
	mov QWORD PTR [r9+400], r12
	mov QWORD PTR [r9+408], r13
	mov QWORD PTR [r9+416], r14
	mov QWORD PTR [r9+424], r15
	mov r8, rsi
20:
	mov eax, DWORD PTR [rdi]
	mov DWORD PTR [rdx], eax
	add rdi, 4
	add rdx, 4
	sub r8, 4
	jne 20b
	mov r10d, 1
	mov QWORD PTR [r9+432], r10
	mov r8d, 0
	mov rdi, rsi
	add rdi, rsi
	add rdi, rsi
	add rdi, 112
21:
	mov eax, DWORD PTR [rdx-4]
	test r8, r8
	je 22f
	mov r10, rsi
	add r10, r8
	cmp r10, 48
	je 24f
	jmp 25f
24:
	mov rbx, rax
	shr rbx, 1
	mov rcx, rax
	shr rcx, 2
	mov rbp, rax
	shr rbp, 3
	mov r10, rax
	shr r10, 4
	mov r11, rax
	shr r11, 5
	mov r12, rax
	shr r12, 6
	mov r13, rax
	shr r13, 7
	movabs r14, -1
	mov QWORD PTR [r9], r14
	xor rcx, r11
	mov r14, rcx
	xor r14, rbx
	mov r15, r14
	xor r15, r12
	xor rax, r14
	xor rbp, r15
	xor rbp, r13
	mov QWORD PTR [r9+8], r12
	mov r12, rbp
	xor r12, rcx
	mov QWORD PTR [r9+16], rcx
	mov rcx, r12
	xor rcx, rax
	xor r11, rcx
	mov QWORD PTR [r9+24], r14
	mov r14, rax
	xor r14, r13
	mov QWORD PTR [r9+32], rax
	mov rax, rcx
	xor rax, r10
	mov QWORD PTR [r9+40], r14
	mov r14, rcx
	xor r14, r15
	mov QWORD PTR [r9+48], r14
	mov r14, r11
	xor r14, r13
	mov QWORD PTR [r9+56], r13
	mov r13, rax
	xor r13, r14
	mov QWORD PTR [r9+64], r11
	mov r11, rax
	and r11, rcx
	mov QWORD PTR [r9+72], rcx
	mov rcx, r12
	xor rcx, r10
	xor r10, rbp
	xor rbp, rax
	mov QWORD PTR [r9+80], rax
	mov rax, r14
	and rax, r15
	mov QWORD PTR [r9+88], r15
	mov r15, rcx
	and r15, rbp
	xor rbx, rcx
	xor rax, r15
	mov QWORD PTR [r9+96], rbp
	mov rbp, r13
	and rbp, QWORD PTR [r9+48]
	xor r15, rbp
	mov rbp, QWORD PTR [r9+48]
	xor rbp, rbx
	mov QWORD PTR [r9+104], r13
	mov r13, rcx
	xor r13, QWORD PTR [r9+64]
	mov QWORD PTR [r9+112], rcx
	mov rcx, QWORD PTR [r9+40]
	and rcx, rbx
	mov QWORD PTR [r9+120], rbx
	mov rbx, r13
	and rbx, rbp
	xor rcx, r15
	xor r15, rbx
	mov rbx, QWORD PTR [r9+32]
	and rbx, r10
	mov QWORD PTR [r9+128], rbp
	mov rbp, QWORD PTR [r9+56]
	and rbp, QWORD PTR [r9+24]
	xor rcx, r11
	xor r15, rbx
	xor r11, rbp
	xor rbx, rax
	mov rbp, r14
	xor rbp, QWORD PTR [r9+8]
	xor rcx, QWORD PTR [r9+16]
	xor r11, rax
	mov rax, QWORD PTR [r9+64]
	and rax, QWORD PTR [r9+8]
	xor r11, rbp
	xor rbx, rax
	mov rax, QWORD PTR [r9+64]
	xor rax, QWORD PTR [r9+24]
	xor rbx, rax
	xor r15, r12
	mov r12, rcx
	xor r12, r15
	mov rax, r11
	and rax, rcx
	mov rbp, r15
	xor rbp, rax
	xor rax, rbx
	and rax, r12
	xor r11, rbx
	xor rax, r15
	xor rcx, rax
	mov r12, rax
	and r12, QWORD PTR [r9+56]
	mov QWORD PTR [r9+56], r12
	mov r12, rbp
	xor r12, rax
	and r15, r12
	xor rcx, r15
	and r14, rcx
	xor r15, rbp
	and rbp, r11
	xor rbx, rbp
	mov rbp, rcx
	and rbp, QWORD PTR [r9+88]
	and r15, rbx
	xor r15, r11
	mov r11, rbx
	xor r11, r15
	and r13, r11
	mov r12, rbx
	xor r12, rax
	and r10, r12
	and r11, QWORD PTR [r9+128]
	mov QWORD PTR [r9+128], r14
	mov r14, r15
	and r14, QWORD PTR [r9+104]
	mov QWORD PTR [r9+104], r14
	mov r14, r12
	and r14, QWORD PTR [r9+32]
	xor r14, r13
	mov QWORD PTR [r9+32], r14
	mov r14, r15
	and r14, QWORD PTR [r9+48]
	xor r15, rcx
	xor r12, r15
	xor r13, QWORD PTR [r9+56]
	xor rcx, rax
	and rax, QWORD PTR [r9+24]
	xor r11, r14
	xor r10, r11
	mov QWORD PTR [r9+24], r10
	mov r10, r12
	and r10, QWORD PTR [r9+96]
	xor r11, r10
	xor r11, rax
	xor rbp, rax
	mov rax, rcx
	and rax, QWORD PTR [r9+8]
	and rcx, QWORD PTR [r9+64]
	xor r11, rax
	and r12, QWORD PTR [r9+112]
	mov rax, rbx
	and rax, QWORD PTR [r9+120]
	xor r12, QWORD PTR [r9+104]
	xor r14, rax
	mov rax, r15
	and rax, QWORD PTR [r9+80]
	and rbx, QWORD PTR [r9+40]
	xor rax, r12
	xor r14, rbp
	xor r13, rax
	xor rax, rbx
	xor rax, QWORD PTR [r9]
	and r15, QWORD PTR [r9+72]
	xor r13, rcx
	xor r11, r15
	xor r12, QWORD PTR [r9+32]
	xor r12, r14
	xor r12, QWORD PTR [r9]
	xor r14, rax
	xor r10, rax
	xor r10, QWORD PTR [r9]
	xor rbp, r10
	xor r10, r13
	xor rbx, r12
	xor rbx, QWORD PTR [r9]
	xor rbx, QWORD PTR [r9+128]
	xor r10, QWORD PTR [r9+24]
	xor r10, QWORD PTR [r9]
	xor rbp, r15
	xor rbx, QWORD PTR [r9+104]
	xor rbx, QWORD PTR [r9+56]
	mov QWORD PTR [r9+56], rax
	mov rax, r12
	mov QWORD PTR [r9+104], rbx
	mov rbx, QWORD PTR [r9+56]
	mov rcx, r13
	mov QWORD PTR [r9+24], rbp
	mov rbp, r11
	mov QWORD PTR [r9+128], r10
	mov r10, QWORD PTR [r9+104]
	mov r11, r14
	mov r12, QWORD PTR [r9+128]
	mov r13, QWORD PTR [r9+24]
	and rax, 16843009
	and rbx, 16843009
	ror rbx, 63
	xor rax, rbx
	and rcx, 16843009
	ror rcx, 62
	xor rax, rcx
	and rbp, 16843009
	ror rbp, 61
	xor rax, rbp
	and r10, 16843009
	ror r10, 60
	xor rax, r10
	and r11, 16843009
	ror r11, 59
	xor rax, r11
	and r12, 16843009
	ror r12, 58
	xor rax, r12
	and r13, 16843009
	ror r13, 57
	xor rax, r13
25:
	jmp 23f
22:
	mov rbx, rax
	shr rbx, 1
	mov rcx, rax
	shr rcx, 2
	mov rbp, rax
	shr rbp, 3
	mov r10, rax
	shr r10, 4
	mov r11, rax
	shr r11, 5
	mov r12, rax
	shr r12, 6
	mov r13, rax
	shr r13, 7
	movabs r14, -1
	mov QWORD PTR [r9], r14
	xor rcx, r11
	mov r14, rcx
	xor r14, rbx
	mov r15, r14
	xor r15, r12
	xor rax, r14
	xor rbp, r15
	xor rbp, r13
	mov QWORD PTR [r9+8], r12
	mov r12, rbp
	xor r12, rcx
	mov QWORD PTR [r9+16], rcx
	mov rcx, r12
	xor rcx, rax
	xor r11, rcx
	mov QWORD PTR [r9+24], r14
	mov r14, rax
	xor r14, r13
	mov QWORD PTR [r9+32], rax
	mov rax, rcx
	xor rax, r10
	mov QWORD PTR [r9+40], r14
	mov r14, rcx
	xor r14, r15
	mov QWORD PTR [r9+48], r14
	mov r14, r11
	xor r14, r13
	mov QWORD PTR [r9+56], r13
	mov r13, rax
	xor r13, r14
	mov QWORD PTR [r9+64], r11
	mov r11, rax
	and r11, rcx
	mov QWORD PTR [r9+72], rcx
	mov rcx, r12
	xor rcx, r10
	xor r10, rbp
	xor rbp, rax
	mov QWORD PTR [r9+80], rax
	mov rax, r14
	and rax, r15
	mov QWORD PTR [r9+88], r15
	mov r15, rcx
	and r15, rbp
	xor rbx, rcx
	xor rax, r15
	mov QWORD PTR [r9+96], rbp
	mov rbp, r13
	and rbp, QWORD PTR [r9+48]
	xor r15, rbp
	mov rbp, QWORD PTR [r9+48]
	xor rbp, rbx
	mov QWORD PTR [r9+104], r13
	mov r13, rcx
	xor r13, QWORD PTR [r9+64]
	mov QWORD PTR [r9+112], rcx
	mov rcx, QWORD PTR [r9+40]
	and rcx, rbx
	mov QWORD PTR [r9+120], rbx
	mov rbx, r13
	and rbx, rbp
	xor rcx, r15
	xor r15, rbx
	mov rbx, QWORD PTR [r9+32]
	and rbx, r10
	mov QWORD PTR [r9+128], rbp
	mov rbp, QWORD PTR [r9+56]
	and rbp, QWORD PTR [r9+24]
	xor rcx, r11
	xor r15, rbx
	xor r11, rbp
	xor rbx, rax
	mov rbp, r14
	xor rbp, QWORD PTR [r9+8]
	xor rcx, QWORD PTR [r9+16]
	xor r11, rax
	mov rax, QWORD PTR [r9+64]
	and rax, QWORD PTR [r9+8]
	xor r11, rbp
	xor rbx, rax
	mov rax, QWORD PTR [r9+64]
	xor rax, QWORD PTR [r9+24]
	xor rbx, rax
	xor r15, r12
	mov r12, rcx
	xor r12, r15
	mov rax, r11
	and rax, rcx
	mov rbp, r15
	xor rbp, rax
	xor rax, rbx
	and rax, r12
	xor r11, rbx
	xor rax, r15
	xor rcx, rax
	mov r12, rax
	and r12, QWORD PTR [r9+56]
	mov QWORD PTR [r9+56], r12
	mov r12, rbp
	xor r12, rax
	and r15, r12
	xor rcx, r15
	and r14, rcx
	xor r15, rbp
	and rbp, r11
	xor rbx, rbp
	mov rbp, rcx
	and rbp, QWORD PTR [r9+88]
	and r15, rbx
	xor r15, r11
	mov r11, rbx
	xor r11, r15
	and r13, r11
	mov r12, rbx
	xor r12, rax
	and r10, r12
	and r11, QWORD PTR [r9+128]
	mov QWORD PTR [r9+128], r14
	mov r14, r15
	and r14, QWORD PTR [r9+104]
	mov QWORD PTR [r9+104], r14
	mov r14, r12
	and r14, QWORD PTR [r9+32]
	xor r14, r13
	mov QWORD PTR [r9+32], r14
	mov r14, r15
	and r14, QWORD PTR [r9+48]
	xor r15, rcx
	xor r12, r15
	xor r13, QWORD PTR [r9+56]
	xor rcx, rax
	and rax, QWORD PTR [r9+24]
	xor r11, r14
	xor r10, r11
	mov QWORD PTR [r9+24], r10
	mov r10, r12
	and r10, QWORD PTR [r9+96]
	xor r11, r10
	xor r11, rax
	xor rbp, rax
	mov rax, rcx
	and rax, QWORD PTR [r9+8]
	and rcx, QWORD PTR [r9+64]
	xor r11, rax
	and r12, QWORD PTR [r9+112]
	mov rax, rbx
	and rax, QWORD PTR [r9+120]
	xor r12, QWORD PTR [r9+104]
	xor r14, rax
	mov rax, r15
	and rax, QWORD PTR [r9+80]
	and rbx, QWORD PTR [r9+40]
	xor rax, r12
	xor r14, rbp
	xor r13, rax
	xor rax, rbx
	xor rax, QWORD PTR [r9]
	and r15, QWORD PTR [r9+72]
	xor r13, rcx
	xor r11, r15
	xor r12, QWORD PTR [r9+32]
	xor r12, r14
	xor r12, QWORD PTR [r9]
	xor r14, rax
	xor r10, rax
	xor r10, QWORD PTR [r9]
	xor rbp, r10
	xor r10, r13
	xor rbx, r12
	xor rbx, QWORD PTR [r9]
	xor rbx, QWORD PTR [r9+128]
	xor r10, QWORD PTR [r9+24]
	xor r10, QWORD PTR [r9]
	xor rbp, r15
	xor rbx, QWORD PTR [r9+104]
	xor rbx, QWORD PTR [r9+56]
	mov QWORD PTR [r9+56], rax
	mov rax, r12
	mov QWORD PTR [r9+104], rbx
	mov rbx, QWORD PTR [r9+56]
	mov rcx, r13
	mov QWORD PTR [r9+24], rbp
	mov rbp, r11
	mov QWORD PTR [r9+128], r10
	mov r10, QWORD PTR [r9+104]
	mov r11, r14
	mov r12, QWORD PTR [r9+128]
	mov r13, QWORD PTR [r9+24]
	and rax, 16843009
	and rbx, 16843009
	ror rbx, 63
	xor rax, rbx
	and rcx, 16843009
	ror rcx, 62
	xor rax, rcx
	and rbp, 16843009
	ror rbp, 61
	xor rax, rbp
	and r10, 16843009
	ror r10, 60
	xor rax, r10
	and r11, 16843009
	ror r11, 59
	xor rax, r11
	and r12, 16843009
	ror r12, 58
	xor rax, r12
	and r13, 16843009
	ror r13, 57
	xor rax, r13
	ror eax, 8
	mov r10, QWORD PTR [r9+432]
	xor rax, r10
	shl r10, 1
	mov r11, r10
	shr r11, 8
	mov r12d, 0
	sub r12, r11
	and r12, 283
	xor r10, r12
	mov QWORD PTR [r9+432], r10
23:
	mov r10, rdx
	sub r10, rsi
	xor eax, DWORD PTR [r10]
	mov DWORD PTR [rdx], eax
	add rdx, 4
	add r8, 4
	cmp r8, rsi
	je 26f
	jmp 27f
26:
	mov r8d, 0
27:
	sub rdi, 4
	jne 21b
	mov rbx, QWORD PTR [r9+384]
	mov rbp, QWORD PTR [r9+392]
	mov r12, QWORD PTR [r9+400]
	mov r13, QWORD PTR [r9+408]
	mov r14, QWORD PTR [r9+416]
	mov r15, QWORD PTR [r9+424]
	ret
	.p2align 6
