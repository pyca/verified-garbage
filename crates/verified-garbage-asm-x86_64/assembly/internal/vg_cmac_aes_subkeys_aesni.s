// The functions of `src/internal/vg_cmac_aes_subkeys_aesni.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cmac_aes_subkeys_aesni:
	mov QWORD PTR [rcx+2064], rbx
	mov QWORD PTR [rcx+2072], rbp
	mov rbx, rdx
	mov rbp, rcx
	mov eax, 0
	mov QWORD PTR [rcx+2048], rax
	mov QWORD PTR [rcx+2056], rax
	mov QWORD PTR [rdx], rax
	mov QWORD PTR [rdx+8], rax
	mov r9, rbp
	mov rdx, rbp
	add rdx, 2048
	mov rcx, rbx
	mov r8d, 1
	call {vg_aes_ctr32_aesni}
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov rdx, QWORD PTR [rbx+8]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	mov r8d, 0
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx], rax
	mov QWORD PTR [rbx+8], rdx
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov rdx, QWORD PTR [rbx+8]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	mov r8d, 0
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	bswap rdx
	mov QWORD PTR [rbx+16], rax
	mov QWORD PTR [rbx+24], rdx
	mov rbx, QWORD PTR [rbp+2064]
	mov rbp, QWORD PTR [rbp+2072]
	ret
	.p2align 6
