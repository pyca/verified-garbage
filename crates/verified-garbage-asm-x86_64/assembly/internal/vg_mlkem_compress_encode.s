// The functions of `src/internal/vg_mlkem_compress_encode.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_compress_encode:
	mov esi, esi
	mov r8, rdx
	cmp esi, 1
	je 20f
	cmp esi, 4
	je 22f
	mov r9, 161271
	mov ecx, 64
24:
	mov r10d, 0
	mov eax, DWORD PTR [rdi+12]
	mul r9
	add rax, 262080
	shr rax, 19
	and eax, 1023
	ror r10, 54
	add r10, rax
	mov eax, DWORD PTR [rdi+8]
	mul r9
	add rax, 262080
	shr rax, 19
	and eax, 1023
	ror r10, 54
	add r10, rax
	mov eax, DWORD PTR [rdi+4]
	mul r9
	add rax, 262080
	shr rax, 19
	and eax, 1023
	ror r10, 54
	add r10, rax
	mov eax, DWORD PTR [rdi]
	mul r9
	add rax, 262080
	shr rax, 19
	and eax, 1023
	ror r10, 54
	add r10, rax
	mov BYTE PTR [r8], r10b
	shr r10, 8
	mov BYTE PTR [r8+1], r10b
	shr r10, 8
	mov BYTE PTR [r8+2], r10b
	shr r10, 8
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
	mov r9, 2520
	mov ecx, 128
25:
	mov r10d, 0
	mov eax, DWORD PTR [rdi+4]
	mul r9
	add rax, 262080
	shr rax, 19
	and eax, 15
	ror r10, 60
	add r10, rax
	mov eax, DWORD PTR [rdi]
	mul r9
	add rax, 262080
	shr rax, 19
	and eax, 15
	ror r10, 60
	add r10, rax
	mov BYTE PTR [r8], r10b
	shr r10, 8
	add rdi, 8
	add r8, 1
	sub rcx, 1
	jne 25b
23:
	jmp 21f
20:
	mov r9, 315
	mov ecx, 32
26:
	mov r10d, 0
	mov eax, DWORD PTR [rdi+28]
	mul r9
	add rax, 262080
	shr rax, 19
	and eax, 1
	ror r10, 63
	add r10, rax
	mov eax, DWORD PTR [rdi+24]
	mul r9
	add rax, 262080
	shr rax, 19
	and eax, 1
	ror r10, 63
	add r10, rax
	mov eax, DWORD PTR [rdi+20]
	mul r9
	add rax, 262080
	shr rax, 19
	and eax, 1
	ror r10, 63
	add r10, rax
	mov eax, DWORD PTR [rdi+16]
	mul r9
	add rax, 262080
	shr rax, 19
	and eax, 1
	ror r10, 63
	add r10, rax
	mov eax, DWORD PTR [rdi+12]
	mul r9
	add rax, 262080
	shr rax, 19
	and eax, 1
	ror r10, 63
	add r10, rax
	mov eax, DWORD PTR [rdi+8]
	mul r9
	add rax, 262080
	shr rax, 19
	and eax, 1
	ror r10, 63
	add r10, rax
	mov eax, DWORD PTR [rdi+4]
	mul r9
	add rax, 262080
	shr rax, 19
	and eax, 1
	ror r10, 63
	add r10, rax
	mov eax, DWORD PTR [rdi]
	mul r9
	add rax, 262080
	shr rax, 19
	and eax, 1
	ror r10, 63
	add r10, rax
	mov BYTE PTR [r8], r10b
	shr r10, 8
	add rdi, 32
	add r8, 1
	sub rcx, 1
	jne 26b
21:
	ret
	.p2align 6
