// The functions of `src/internal/vg_mlkem_decode_decompress.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_decode_decompress:
	mov edx, edx
	mov rsi, rcx
	cmp edx, 1
	je 20f
	cmp edx, 4
	je 22f
	mov r9, 3329
	mov ecx, 64
24:
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
	and eax, 1023
	mul r9
	add rax, 512
	shr rax, 10
	mov DWORD PTR [rsi], eax
	shr r10, 10
	mov rax, r10
	and eax, 1023
	mul r9
	add rax, 512
	shr rax, 10
	mov DWORD PTR [rsi+4], eax
	shr r10, 10
	mov rax, r10
	and eax, 1023
	mul r9
	add rax, 512
	shr rax, 10
	mov DWORD PTR [rsi+8], eax
	shr r10, 10
	mov rax, r10
	and eax, 1023
	mul r9
	add rax, 512
	shr rax, 10
	mov DWORD PTR [rsi+12], eax
	shr r10, 10
	add rdi, 5
	add rsi, 16
	sub rcx, 1
	jne 24b
	jmp 23f
22:
	mov r9, 3329
	mov ecx, 128
25:
	mov r10d, 0
	movzx eax, BYTE PTR [rdi]
	ror r10, 56
	add r10, rax
	mov rax, r10
	and eax, 15
	mul r9
	add rax, 8
	shr rax, 4
	mov DWORD PTR [rsi], eax
	shr r10, 4
	mov rax, r10
	and eax, 15
	mul r9
	add rax, 8
	shr rax, 4
	mov DWORD PTR [rsi+4], eax
	shr r10, 4
	add rdi, 1
	add rsi, 8
	sub rcx, 1
	jne 25b
23:
	jmp 21f
20:
	mov r9, 3329
	mov ecx, 32
26:
	mov r10d, 0
	movzx eax, BYTE PTR [rdi]
	ror r10, 56
	add r10, rax
	mov rax, r10
	and eax, 1
	mul r9
	add rax, 1
	shr rax, 1
	mov DWORD PTR [rsi], eax
	shr r10, 1
	mov rax, r10
	and eax, 1
	mul r9
	add rax, 1
	shr rax, 1
	mov DWORD PTR [rsi+4], eax
	shr r10, 1
	mov rax, r10
	and eax, 1
	mul r9
	add rax, 1
	shr rax, 1
	mov DWORD PTR [rsi+8], eax
	shr r10, 1
	mov rax, r10
	and eax, 1
	mul r9
	add rax, 1
	shr rax, 1
	mov DWORD PTR [rsi+12], eax
	shr r10, 1
	mov rax, r10
	and eax, 1
	mul r9
	add rax, 1
	shr rax, 1
	mov DWORD PTR [rsi+16], eax
	shr r10, 1
	mov rax, r10
	and eax, 1
	mul r9
	add rax, 1
	shr rax, 1
	mov DWORD PTR [rsi+20], eax
	shr r10, 1
	mov rax, r10
	and eax, 1
	mul r9
	add rax, 1
	shr rax, 1
	mov DWORD PTR [rsi+24], eax
	shr r10, 1
	mov rax, r10
	and eax, 1
	mul r9
	add rax, 1
	shr rax, 1
	mov DWORD PTR [rsi+28], eax
	shr r10, 1
	add rdi, 1
	add rsi, 32
	sub rcx, 1
	jne 26b
21:
	ret
	.p2align 6
