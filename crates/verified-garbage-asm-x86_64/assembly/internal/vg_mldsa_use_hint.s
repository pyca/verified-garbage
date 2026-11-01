// The functions of `src/internal/vg_mldsa_use_hint.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_use_hint:
	mov edx, edx
	cmp edx, 261888
	mov r10, rcx
	je 20f
	mov ecx, 256
22:
	mov eax, DWORD PTR [rsi+rcx*4-4]
	mov r11, rax
	add rax, 127
	shr rax, 7
	mov r8d, 11275
	mul r8
	add rax, 8388608
	shr rax, 24
	mov r9, rax
	mov r8d, 190464
	mul r8
	sub rax, r11
	sbb rax, rax
	and rax, 2
	sub rax, 1
	mov r11d, DWORD PTR [rdi+rcx*4-4]
	mov r8d, 0
	sub r8, r11
	sbb r8, r8
	and rax, r8
	add rax, r9
	add rax, 44
	sub rax, 44
	sbb r8, r8
	and r8, 44
	add rax, r8
	sub rax, 44
	sbb r8, r8
	and r8, 44
	add rax, r8
	mov DWORD PTR [r10+rcx*4-4], eax
	sub rcx, 1
	jne 22b
	jmp 21f
20:
	mov ecx, 256
23:
	mov eax, DWORD PTR [rsi+rcx*4-4]
	mov r11, rax
	add rax, 127
	shr rax, 7
	mov r8d, 1025
	mul r8
	add rax, 2097152
	shr rax, 22
	mov r9, rax
	mov r8d, 523776
	mul r8
	sub rax, r11
	sbb rax, rax
	and rax, 2
	sub rax, 1
	mov r11d, DWORD PTR [rdi+rcx*4-4]
	mov r8d, 0
	sub r8, r11
	sbb r8, r8
	and rax, r8
	add rax, r9
	add rax, 16
	sub rax, 16
	sbb r8, r8
	and r8, 16
	add rax, r8
	sub rax, 16
	sbb r8, r8
	and r8, 16
	add rax, r8
	mov DWORD PTR [r10+rcx*4-4], eax
	sub rcx, 1
	jne 23b
21:
	ret
	.p2align 6
