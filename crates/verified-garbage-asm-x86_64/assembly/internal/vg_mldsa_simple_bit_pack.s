// The functions of `src/internal/vg_mldsa_simple_bit_pack.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_simple_bit_pack:
	mov esi, esi
	mov r8, rdx
	cmp esi, 15
	je 20f
	cmp esi, 43
	je 22f
	mov ecx, 64
24:
	mov r10d, 0
	mov eax, DWORD PTR [rdi]
	add r10, rax
	mov BYTE PTR [r8], r10b
	shr r10, 8
	mov eax, DWORD PTR [rdi+4]
	ror rax, 62
	add r10, rax
	mov BYTE PTR [r8+1], r10b
	shr r10, 8
	mov eax, DWORD PTR [rdi+8]
	ror rax, 60
	add r10, rax
	mov BYTE PTR [r8+2], r10b
	shr r10, 8
	mov eax, DWORD PTR [rdi+12]
	ror rax, 58
	add r10, rax
	mov BYTE PTR [r8+3], r10b
	shr r10, 8
	mov BYTE PTR [r8+4], r10b
	shr r10, 8
	add rdi, 16
	add r8, 5
	sub rcx, 1
	jne 24b
	jmp 23f
22:
	mov ecx, 64
25:
	mov r10d, 0
	mov eax, DWORD PTR [rdi]
	add r10, rax
	mov eax, DWORD PTR [rdi+4]
	ror rax, 58
	add r10, rax
	mov BYTE PTR [r8], r10b
	shr r10, 8
	mov eax, DWORD PTR [rdi+8]
	ror rax, 60
	add r10, rax
	mov BYTE PTR [r8+1], r10b
	shr r10, 8
	mov eax, DWORD PTR [rdi+12]
	ror rax, 62
	add r10, rax
	mov BYTE PTR [r8+2], r10b
	shr r10, 8
	add rdi, 16
	add r8, 3
	sub rcx, 1
	jne 25b
23:
	jmp 21f
20:
	mov ecx, 128
26:
	mov r10d, 0
	mov eax, DWORD PTR [rdi]
	add r10, rax
	mov eax, DWORD PTR [rdi+4]
	ror rax, 60
	add r10, rax
	mov BYTE PTR [r8], r10b
	shr r10, 8
	add rdi, 8
	add r8, 1
	sub rcx, 1
	jne 26b
21:
	ret
	.p2align 6
