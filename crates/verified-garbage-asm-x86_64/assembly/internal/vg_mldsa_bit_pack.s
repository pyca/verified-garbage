// The functions of `src/internal/vg_mldsa_bit_pack.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_bit_pack:
	mov edx, edx
	mov r8, rcx
	cmp edx, 2
	je 20f
	cmp edx, 4
	je 22f
	cmp edx, 4096
	je 24f
	cmp edx, 131072
	je 26f
	mov ecx, 128
28:
	mov r10d, 0
	mov eax, 524288
	sub eax, DWORD PTR [rdi]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	add r10, rax
	mov BYTE PTR [r8], r10b
	shr r10, 8
	mov BYTE PTR [r8+1], r10b
	shr r10, 8
	mov eax, 524288
	sub eax, DWORD PTR [rdi+4]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	ror rax, 60
	add r10, rax
	mov BYTE PTR [r8+2], r10b
	shr r10, 8
	mov BYTE PTR [r8+3], r10b
	shr r10, 8
	mov BYTE PTR [r8+4], r10b
	shr r10, 8
	add rdi, 8
	add r8, 5
	sub rcx, 1
	jne 28b
	jmp 27f
26:
	mov ecx, 64
29:
	mov r10d, 0
	mov eax, 131072
	sub eax, DWORD PTR [rdi]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	add r10, rax
	mov BYTE PTR [r8], r10b
	shr r10, 8
	mov BYTE PTR [r8+1], r10b
	shr r10, 8
	mov eax, 131072
	sub eax, DWORD PTR [rdi+4]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	ror rax, 62
	add r10, rax
	mov BYTE PTR [r8+2], r10b
	shr r10, 8
	mov BYTE PTR [r8+3], r10b
	shr r10, 8
	mov eax, 131072
	sub eax, DWORD PTR [rdi+8]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	ror rax, 60
	add r10, rax
	mov BYTE PTR [r8+4], r10b
	shr r10, 8
	mov BYTE PTR [r8+5], r10b
	shr r10, 8
	mov eax, 131072
	sub eax, DWORD PTR [rdi+12]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	ror rax, 58
	add r10, rax
	mov BYTE PTR [r8+6], r10b
	shr r10, 8
	mov BYTE PTR [r8+7], r10b
	shr r10, 8
	mov BYTE PTR [r8+8], r10b
	shr r10, 8
	add rdi, 16
	add r8, 9
	sub rcx, 1
	jne 29b
27:
	jmp 25f
24:
	mov ecx, 32
210:
	mov r10d, 0
	mov eax, 4096
	sub eax, DWORD PTR [rdi]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	add r10, rax
	mov BYTE PTR [r8], r10b
	shr r10, 8
	mov eax, 4096
	sub eax, DWORD PTR [rdi+4]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	ror rax, 59
	add r10, rax
	mov BYTE PTR [r8+1], r10b
	shr r10, 8
	mov BYTE PTR [r8+2], r10b
	shr r10, 8
	mov eax, 4096
	sub eax, DWORD PTR [rdi+8]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	ror rax, 62
	add r10, rax
	mov BYTE PTR [r8+3], r10b
	shr r10, 8
	mov eax, 4096
	sub eax, DWORD PTR [rdi+12]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	ror rax, 57
	add r10, rax
	mov BYTE PTR [r8+4], r10b
	shr r10, 8
	mov BYTE PTR [r8+5], r10b
	shr r10, 8
	mov eax, 4096
	sub eax, DWORD PTR [rdi+16]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	ror rax, 60
	add r10, rax
	mov BYTE PTR [r8+6], r10b
	shr r10, 8
	mov BYTE PTR [r8+7], r10b
	shr r10, 8
	mov eax, 4096
	sub eax, DWORD PTR [rdi+20]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	ror rax, 63
	add r10, rax
	mov BYTE PTR [r8+8], r10b
	shr r10, 8
	mov eax, 4096
	sub eax, DWORD PTR [rdi+24]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	ror rax, 58
	add r10, rax
	mov BYTE PTR [r8+9], r10b
	shr r10, 8
	mov BYTE PTR [r8+10], r10b
	shr r10, 8
	mov eax, 4096
	sub eax, DWORD PTR [rdi+28]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	ror rax, 61
	add r10, rax
	mov BYTE PTR [r8+11], r10b
	shr r10, 8
	mov BYTE PTR [r8+12], r10b
	shr r10, 8
	add rdi, 32
	add r8, 13
	sub rcx, 1
	jne 210b
25:
	jmp 23f
22:
	mov ecx, 128
211:
	mov r10d, 0
	mov eax, 4
	sub eax, DWORD PTR [rdi]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	add r10, rax
	mov eax, 4
	sub eax, DWORD PTR [rdi+4]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	ror rax, 60
	add r10, rax
	mov BYTE PTR [r8], r10b
	shr r10, 8
	add rdi, 8
	add r8, 1
	sub rcx, 1
	jne 211b
23:
	jmp 21f
20:
	mov ecx, 32
212:
	mov r10d, 0
	mov eax, 2
	sub eax, DWORD PTR [rdi]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	add r10, rax
	mov eax, 2
	sub eax, DWORD PTR [rdi+4]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	ror rax, 61
	add r10, rax
	mov eax, 2
	sub eax, DWORD PTR [rdi+8]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	ror rax, 58
	add r10, rax
	mov BYTE PTR [r8], r10b
	shr r10, 8
	mov eax, 2
	sub eax, DWORD PTR [rdi+12]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	ror rax, 63
	add r10, rax
	mov eax, 2
	sub eax, DWORD PTR [rdi+16]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	ror rax, 60
	add r10, rax
	mov eax, 2
	sub eax, DWORD PTR [rdi+20]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	ror rax, 57
	add r10, rax
	mov BYTE PTR [r8+1], r10b
	shr r10, 8
	mov eax, 2
	sub eax, DWORD PTR [rdi+24]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	ror rax, 62
	add r10, rax
	mov eax, 2
	sub eax, DWORD PTR [rdi+28]
	sbb r11d, r11d
	and r11d, 8380417
	add eax, r11d
	ror rax, 59
	add r10, rax
	mov BYTE PTR [r8+2], r10b
	shr r10, 8
	add rdi, 32
	add r8, 3
	sub rcx, 1
	jne 212b
21:
	ret
	.p2align 6
