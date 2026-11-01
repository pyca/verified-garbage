// The functions of `src/internal/vg_mldsa_make_hint.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_make_hint:
	mov edx, edx
	cmp edx, 261888
	mov r10, rcx
	mov r9d, 0
	je 20f
	mov ecx, 256
22:
	mov eax, DWORD PTR [rsi+rcx*4-4]
	add rax, 127
	shr rax, 7
	mov r8d, 11275
	mul r8
	add rax, 8388608
	shr rax, 24
	sub rax, 44
	sbb r8, r8
	and r8, 44
	add rax, r8
	mov r11, rax
	mov eax, DWORD PTR [rsi+rcx*4-4]
	add eax, DWORD PTR [rdi+rcx*4-4]
	sub rax, 8380417
	sbb r8, r8
	and r8, 8380417
	add rax, r8
	add rax, 127
	shr rax, 7
	mov r8d, 11275
	mul r8
	add rax, 8388608
	shr rax, 24
	sub rax, 44
	sbb r8, r8
	and r8, 44
	add rax, r8
	xor rax, r11
	add rax, 63
	shr rax, 6
	mov DWORD PTR [r10+rcx*4-4], eax
	add r9, rax
	sub rcx, 1
	jne 22b
	jmp 21f
20:
	mov ecx, 256
23:
	mov eax, DWORD PTR [rsi+rcx*4-4]
	add rax, 127
	shr rax, 7
	mov r8d, 1025
	mul r8
	add rax, 2097152
	shr rax, 22
	sub rax, 16
	sbb r8, r8
	and r8, 16
	add rax, r8
	mov r11, rax
	mov eax, DWORD PTR [rsi+rcx*4-4]
	add eax, DWORD PTR [rdi+rcx*4-4]
	sub rax, 8380417
	sbb r8, r8
	and r8, 8380417
	add rax, r8
	add rax, 127
	shr rax, 7
	mov r8d, 1025
	mul r8
	add rax, 2097152
	shr rax, 22
	sub rax, 16
	sbb r8, r8
	and r8, 16
	add rax, r8
	xor rax, r11
	add rax, 63
	shr rax, 6
	mov DWORD PTR [r10+rcx*4-4], eax
	add r9, rax
	sub rcx, 1
	jne 23b
21:
	mov rax, r9
	ret
	.p2align 6
