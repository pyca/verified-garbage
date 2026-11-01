// The functions of `src/internal/vg_mldsa_bit_unpack.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_bit_unpack:
	mov ecx, ecx
	mov rsi, r8
	cmp ecx, 2
	je 20f
	cmp ecx, 4
	je 22f
	cmp ecx, 4096
	je 24f
	cmp ecx, 131072
	je 26f
	mov ecx, 128
28:
	mov eax, DWORD PTR [rdi]
	and eax, 1048575
	mov r11d, 524288
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi], r11d
	mov eax, DWORD PTR [rdi+1]
	shr eax, 12
	and eax, 1048575
	mov r11d, 524288
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi+4], r11d
	add rdi, 5
	add rsi, 8
	sub rcx, 1
	jne 28b
	jmp 27f
26:
	mov ecx, 64
29:
	mov eax, DWORD PTR [rdi]
	and eax, 262143
	mov r11d, 131072
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi], r11d
	mov eax, DWORD PTR [rdi+2]
	shr eax, 2
	and eax, 262143
	mov r11d, 131072
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi+4], r11d
	mov eax, DWORD PTR [rdi+4]
	shr eax, 4
	and eax, 262143
	mov r11d, 131072
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi+8], r11d
	mov eax, DWORD PTR [rdi+5]
	shr eax, 14
	and eax, 262143
	mov r11d, 131072
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi+12], r11d
	add rdi, 9
	add rsi, 16
	sub rcx, 1
	jne 29b
27:
	jmp 25f
24:
	mov ecx, 32
210:
	mov eax, DWORD PTR [rdi]
	and eax, 8191
	mov r11d, 4096
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi], r11d
	mov eax, DWORD PTR [rdi+1]
	shr eax, 5
	and eax, 8191
	mov r11d, 4096
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi+4], r11d
	mov eax, DWORD PTR [rdi+3]
	shr eax, 2
	and eax, 8191
	mov r11d, 4096
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi+8], r11d
	mov eax, DWORD PTR [rdi+4]
	shr eax, 7
	and eax, 8191
	mov r11d, 4096
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi+12], r11d
	mov eax, DWORD PTR [rdi+6]
	shr eax, 4
	and eax, 8191
	mov r11d, 4096
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi+16], r11d
	mov eax, DWORD PTR [rdi+8]
	shr eax, 1
	and eax, 8191
	mov r11d, 4096
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi+20], r11d
	mov eax, DWORD PTR [rdi+9]
	shr eax, 6
	and eax, 8191
	mov r11d, 4096
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi+24], r11d
	mov eax, DWORD PTR [rdi+9]
	shr eax, 19
	and eax, 8191
	mov r11d, 4096
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi+28], r11d
	add rdi, 13
	add rsi, 32
	sub rcx, 1
	jne 210b
25:
	jmp 23f
22:
	mov ecx, 64
211:
	movzx eax, WORD PTR [rdi]
	and eax, 15
	mov r11d, 4
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi], r11d
	movzx eax, WORD PTR [rdi]
	shr eax, 4
	and eax, 15
	mov r11d, 4
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi+4], r11d
	movzx eax, WORD PTR [rdi]
	shr eax, 8
	and eax, 15
	mov r11d, 4
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi+8], r11d
	movzx eax, WORD PTR [rdi]
	shr eax, 12
	and eax, 15
	mov r11d, 4
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi+12], r11d
	add rdi, 2
	add rsi, 16
	sub rcx, 1
	jne 211b
23:
	jmp 21f
20:
	mov ecx, 32
212:
	movzx eax, WORD PTR [rdi]
	and eax, 7
	mov r11d, 2
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi], r11d
	movzx eax, WORD PTR [rdi]
	shr eax, 3
	and eax, 7
	mov r11d, 2
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi+4], r11d
	movzx eax, WORD PTR [rdi]
	shr eax, 6
	and eax, 7
	mov r11d, 2
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi+8], r11d
	movzx eax, WORD PTR [rdi+1]
	shr eax, 1
	and eax, 7
	mov r11d, 2
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi+12], r11d
	movzx eax, WORD PTR [rdi+1]
	shr eax, 4
	and eax, 7
	mov r11d, 2
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi+16], r11d
	movzx eax, WORD PTR [rdi+1]
	shr eax, 7
	and eax, 7
	mov r11d, 2
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi+20], r11d
	movzx eax, WORD PTR [rdi+1]
	shr eax, 10
	and eax, 7
	mov r11d, 2
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi+24], r11d
	movzx eax, WORD PTR [rdi+1]
	shr eax, 13
	and eax, 7
	mov r11d, 2
	sub r11d, eax
	sbb eax, eax
	and eax, 8380417
	add r11d, eax
	mov DWORD PTR [rsi+28], r11d
	add rdi, 3
	add rsi, 32
	sub rcx, 1
	jne 212b
21:
	ret
	.p2align 6
