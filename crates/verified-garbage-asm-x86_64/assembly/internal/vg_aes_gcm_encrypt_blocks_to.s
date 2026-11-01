// The functions of `src/internal/vg_aes_gcm_encrypt_blocks_to.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_gcm_encrypt_blocks_to:
	mov r11, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [r11], rdi
	mov QWORD PTR [r11+8], rsi
	mov QWORD PTR [r11+16], rdx
	mov QWORD PTR [r11+24], rcx
	mov QWORD PTR [r11+32], r8
	mov QWORD PTR [r11+40], r9
	mov QWORD PTR [r11+48], r10
	mov r11, QWORD PTR [rsp+24]
	mov rcx, QWORD PTR [r11+40]
	test rcx, rcx
	je 20f
	mov rsi, QWORD PTR [r11+32]
	mov rdi, QWORD PTR [r11+48]
	mov r10d, 0
22:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	sub rcx, 1
	jne 22b
	mov r11, QWORD PTR [rsp+24]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, QWORD PTR [r11+16]
	mov rcx, QWORD PTR [r11+24]
	mov r8, QWORD PTR [r11+48]
	mov r9, QWORD PTR [r11+40]
	mov rax, r11
	push rax
	call {vg_aes_gcm_encrypt_blocks}
	pop rax
	jmp 21f
20:
21:
	ret
	.p2align 6
