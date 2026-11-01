// The functions of `src/internal/vg_mlkem1024_compress_encode.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem1024_compress_encode:
	mov esi, esi
	mov r8, rdx
	cmp esi, 5
	je 20f
	mov r9, 322542
	mov ecx, 32
22:
	mov r10d, 0
	mov eax, DWORD PTR [rdi+16]
	mul r9
	add rax, 261888
	shr rax, 19
	and eax, 2047
	ror r10, 53
	add r10, rax
	mov eax, DWORD PTR [rdi+12]
	mul r9
	add rax, 261888
	shr rax, 19
	and eax, 2047
	ror r10, 53
	add r10, rax
	mov eax, DWORD PTR [rdi+8]
	mul r9
	add rax, 261888
	shr rax, 19
	and eax, 2047
	ror r10, 53
	add r10, rax
	mov eax, DWORD PTR [rdi+4]
	mul r9
	add rax, 261888
	shr rax, 19
	and eax, 2047
	ror r10, 53
	add r10, rax
	mov eax, DWORD PTR [rdi]
	mul r9
	add rax, 261888
	shr rax, 19
	and eax, 2047
	ror r10, 53
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
	mov BYTE PTR [r8+5], r10b
	shr r10, 8
	mov r10d, 0
	mov eax, DWORD PTR [rdi+28]
	mul r9
	add rax, 261888
	shr rax, 19
	and eax, 2047
	ror r10, 53
	add r10, rax
	mov eax, DWORD PTR [rdi+24]
	mul r9
	add rax, 261888
	shr rax, 19
	and eax, 2047
	ror r10, 53
	add r10, rax
	mov eax, DWORD PTR [rdi+20]
	mul r9
	add rax, 261888
	shr rax, 19
	and eax, 2047
	ror r10, 53
	add r10, rax
	mov eax, DWORD PTR [rdi+16]
	mul r9
	add rax, 261888
	shr rax, 19
	and eax, 2047
	ror r10, 53
	add r10, rax
	shr r10, 4
	mov BYTE PTR [r8+6], r10b
	shr r10, 8
	mov BYTE PTR [r8+7], r10b
	shr r10, 8
	mov BYTE PTR [r8+8], r10b
	shr r10, 8
	mov BYTE PTR [r8+9], r10b
	shr r10, 8
	mov BYTE PTR [r8+10], r10b
	shr r10, 8
	add rdi, 32
	add r8, 11
	sub rcx, 1
	jne 22b
	jmp 21f
20:
	mov r9, 5040
	mov ecx, 32
23:
	mov r10d, 0
	mov eax, DWORD PTR [rdi+28]
	mul r9
	add rax, 261888
	shr rax, 19
	and eax, 31
	ror r10, 59
	add r10, rax
	mov eax, DWORD PTR [rdi+24]
	mul r9
	add rax, 261888
	shr rax, 19
	and eax, 31
	ror r10, 59
	add r10, rax
	mov eax, DWORD PTR [rdi+20]
	mul r9
	add rax, 261888
	shr rax, 19
	and eax, 31
	ror r10, 59
	add r10, rax
	mov eax, DWORD PTR [rdi+16]
	mul r9
	add rax, 261888
	shr rax, 19
	and eax, 31
	ror r10, 59
	add r10, rax
	mov eax, DWORD PTR [rdi+12]
	mul r9
	add rax, 261888
	shr rax, 19
	and eax, 31
	ror r10, 59
	add r10, rax
	mov eax, DWORD PTR [rdi+8]
	mul r9
	add rax, 261888
	shr rax, 19
	and eax, 31
	ror r10, 59
	add r10, rax
	mov eax, DWORD PTR [rdi+4]
	mul r9
	add rax, 261888
	shr rax, 19
	and eax, 31
	ror r10, 59
	add r10, rax
	mov eax, DWORD PTR [rdi]
	mul r9
	add rax, 261888
	shr rax, 19
	and eax, 31
	ror r10, 59
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
	add rdi, 32
	add r8, 5
	sub rcx, 1
	jne 23b
21:
	ret
	.p2align 6
