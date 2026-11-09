// The functions of `src/internal/vg_aes_xts_encrypt_to_aesni.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_xts_encrypt_to_aesni:
	mov QWORD PTR [r9], rdi
	mov QWORD PTR [r9+8], rsi
	mov QWORD PTR [r9+16], r8
	mov rsi, rcx
	mov rdi, r10
	mov rcx, r8
	shl rcx, 4
	cmp rcx, 32
	jb 20f
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu XMMWORD PTR [rdi], xmm0
	mov r10d, 0
	sub r10, rdi
	and r10, 15
	mov r8, rcx
	sub r8, 32
	cmp r8, r10
	jb 22f
24:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	add r10, 32
	cmp r8, r10
	jae 24b
	jmp 23f
22:
23:
	movdqu xmm0, XMMWORD PTR [rsi+rcx*1-32]
	movdqu xmm1, XMMWORD PTR [rsi+rcx*1-16]
	movdqu XMMWORD PTR [rdi+rcx*1-32], xmm0
	movdqu XMMWORD PTR [rdi+rcx*1-16], xmm1
	jmp 21f
20:
	cmp rcx, 16
	jb 25f
	movdqu xmm0, XMMWORD PTR [rsi]
	movdqu xmm1, XMMWORD PTR [rsi+rcx*1-16]
	movdqu XMMWORD PTR [rdi], xmm0
	movdqu XMMWORD PTR [rdi+rcx*1-16], xmm1
	jmp 26f
25:
	cmp rcx, 8
	jb 27f
	mov rax, QWORD PTR [rsi]
	mov r8, QWORD PTR [rsi+rcx*1-8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+rcx*1-8], r8
	jmp 28f
27:
	cmp rcx, 4
	jb 29f
	mov eax, DWORD PTR [rsi]
	mov r8d, DWORD PTR [rsi+rcx*1-4]
	mov DWORD PTR [rdi], eax
	mov DWORD PTR [rdi+rcx*1-4], r8d
	jmp 210f
29:
	mov r10d, 0
	cmp r10, rcx
	je 211f
213:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 213b
	jmp 212f
211:
212:
210:
28:
26:
21:
	mov rcx, rdi
	mov rdi, QWORD PTR [r9]
	mov rsi, QWORD PTR [r9+8]
	mov r8, QWORD PTR [r9+16]
	call {vg_aes_xts_encrypt_aesni}
	ret
	.p2align 6
