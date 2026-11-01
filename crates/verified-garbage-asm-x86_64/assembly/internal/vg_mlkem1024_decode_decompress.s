// The functions of `src/internal/vg_mlkem1024_decode_decompress.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem1024_decode_decompress:
	mov edx, edx
	mov rsi, rcx
	cmp edx, 5
	je 20f
	mov r9, 3329
	mov ecx, 32
22:
	mov r10d, 0
	movzx eax, BYTE PTR [rdi+5]
	ror r10, 56
	add r10, rax
	movzx eax, BYTE PTR [rdi+4]
	ror r10, 56
	add r10, rax
	movzx eax, BYTE PTR [rdi+3]
	ror r10, 56
	add r10, rax
	movzx eax, BYTE PTR [rdi+2]
	ror r10, 56
	add r10, rax
	movzx eax, BYTE PTR [rdi+1]
	ror r10, 56
	add r10, rax
	movzx eax, BYTE PTR [rdi]
	ror r10, 56
	add r10, rax
	mov rax, r10
	and eax, 2047
	mul r9
	add rax, 1024
	shr rax, 11
	mov DWORD PTR [rsi], eax
	shr r10, 11
	mov rax, r10
	and eax, 2047
	mul r9
	add rax, 1024
	shr rax, 11
	mov DWORD PTR [rsi+4], eax
	shr r10, 11
	mov rax, r10
	and eax, 2047
	mul r9
	add rax, 1024
	shr rax, 11
	mov DWORD PTR [rsi+8], eax
	shr r10, 11
	mov rax, r10
	and eax, 2047
	mul r9
	add rax, 1024
	shr rax, 11
	mov DWORD PTR [rsi+12], eax
	shr r10, 11
	mov r10d, 0
	movzx eax, BYTE PTR [rdi+10]
	ror r10, 56
	add r10, rax
	movzx eax, BYTE PTR [rdi+9]
	ror r10, 56
	add r10, rax
	movzx eax, BYTE PTR [rdi+8]
	ror r10, 56
	add r10, rax
	movzx eax, BYTE PTR [rdi+7]
	ror r10, 56
	add r10, rax
	movzx eax, BYTE PTR [rdi+6]
	ror r10, 56
	add r10, rax
	movzx eax, BYTE PTR [rdi+5]
	ror r10, 56
	add r10, rax
	shr r10, 4
	mov rax, r10
	and eax, 2047
	mul r9
	add rax, 1024
	shr rax, 11
	mov DWORD PTR [rsi+16], eax
	shr r10, 11
	mov rax, r10
	and eax, 2047
	mul r9
	add rax, 1024
	shr rax, 11
	mov DWORD PTR [rsi+20], eax
	shr r10, 11
	mov rax, r10
	and eax, 2047
	mul r9
	add rax, 1024
	shr rax, 11
	mov DWORD PTR [rsi+24], eax
	shr r10, 11
	mov rax, r10
	and eax, 2047
	mul r9
	add rax, 1024
	shr rax, 11
	mov DWORD PTR [rsi+28], eax
	shr r10, 11
	add rdi, 11
	add rsi, 32
	sub rcx, 1
	jne 22b
	jmp 21f
20:
	mov r9, 3329
	mov ecx, 32
23:
	mov r10d, 0
	movzx eax, BYTE PTR [rdi+4]
	ror r10, 56
	add r10, rax
	movzx eax, BYTE PTR [rdi+3]
	ror r10, 56
	add r10, rax
	movzx eax, BYTE PTR [rdi+2]
	ror r10, 56
	add r10, rax
	movzx eax, BYTE PTR [rdi+1]
	ror r10, 56
	add r10, rax
	movzx eax, BYTE PTR [rdi]
	ror r10, 56
	add r10, rax
	mov rax, r10
	and eax, 31
	mul r9
	add rax, 16
	shr rax, 5
	mov DWORD PTR [rsi], eax
	shr r10, 5
	mov rax, r10
	and eax, 31
	mul r9
	add rax, 16
	shr rax, 5
	mov DWORD PTR [rsi+4], eax
	shr r10, 5
	mov rax, r10
	and eax, 31
	mul r9
	add rax, 16
	shr rax, 5
	mov DWORD PTR [rsi+8], eax
	shr r10, 5
	mov rax, r10
	and eax, 31
	mul r9
	add rax, 16
	shr rax, 5
	mov DWORD PTR [rsi+12], eax
	shr r10, 5
	mov rax, r10
	and eax, 31
	mul r9
	add rax, 16
	shr rax, 5
	mov DWORD PTR [rsi+16], eax
	shr r10, 5
	mov rax, r10
	and eax, 31
	mul r9
	add rax, 16
	shr rax, 5
	mov DWORD PTR [rsi+20], eax
	shr r10, 5
	mov rax, r10
	and eax, 31
	mul r9
	add rax, 16
	shr rax, 5
	mov DWORD PTR [rsi+24], eax
	shr r10, 5
	mov rax, r10
	and eax, 31
	mul r9
	add rax, 16
	shr rax, 5
	mov DWORD PTR [rsi+28], eax
	shr r10, 5
	add rdi, 5
	add rsi, 32
	sub rcx, 1
	jne 23b
21:
	ret
	.p2align 6
