// The functions of `src/internal/vg_aes_gcm_stream_encrypt_to_vaes_pclmul.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_gcm_stream_encrypt_to_vaes_pclmul:
	lea rsp, [rsp-2232]
	mov rax, QWORD PTR [rsp+2240]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2248]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2256]
	mov QWORD PTR [rsp+24], rax
	mov rax, rsp
	add rax, 40
	mov QWORD PTR [rsp+32], rax
	mov r11, QWORD PTR [rsp+32]
	mov rax, QWORD PTR [rsp+8]
	mov r10, QWORD PTR [rsp+16]
	mov QWORD PTR [r11], rdi
	mov QWORD PTR [r11+8], rsi
	mov QWORD PTR [r11+16], rdx
	mov QWORD PTR [r11+24], rcx
	mov QWORD PTR [r11+32], r8
	mov QWORD PTR [r11+40], r9
	mov QWORD PTR [r11+48], rax
	mov QWORD PTR [r11+56], r10
	mov eax, 0
	mov QWORD PTR [r11+64], rax
	mov eax, 0
	sub rax, r8
	and rax, 15
	mov rcx, QWORD PTR [r11+48]
	cmp rcx, rax
	cmovb rax, rcx
	test rax, rax
	je 20f
	mov rcx, r8
	add rcx, rax
	jb 22f
	mov QWORD PTR [r11+72], rax
	mov rcx, rax
	mov rsi, QWORD PTR [r11+40]
	mov rdi, QWORD PTR [r11+56]
	mov r10d, 0
24:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 24b
	mov r11, QWORD PTR [rsp+32]
	mov r10, QWORD PTR [r11+72]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, QWORD PTR [r11+16]
	mov rcx, QWORD PTR [r11+24]
	mov r8, QWORD PTR [r11+32]
	mov r9, QWORD PTR [r11+56]
	push r10
	call {vg_aes_gcm_stream_encrypt_vaes_pclmul}
	pop rax
	mov r11, QWORD PTR [rsp+32]
	mov rax, QWORD PTR [r11+72]
	mov QWORD PTR [r11+64], rax
	jmp 23f
22:
23:
	jmp 21f
20:
21:
	mov r11, QWORD PTR [rsp+32]
	mov rcx, QWORD PTR [r11+24]
	mov r8, QWORD PTR [r11+32]
	mov rax, QWORD PTR [r11+64]
	add r8, rax
	mov rax, r8
	test rax, rax
	je 25f
	jmp 26f
25:
	mov rax, rcx
26:
	and rax, 15
	jne 27f
	mov rax, QWORD PTR [r11+48]
	mov rcx, QWORD PTR [r11+64]
	sub rax, rcx
	shr rax, 4
	test rax, rax
	je 29f
	mov r9, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	mov rcx, r8
	add rcx, rax
	jb 211f
	mov rcx, QWORD PTR [r11+64]
	add rax, rcx
	mov QWORD PTR [r11+64], rax
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, QWORD PTR [r11+16]
	mov r8, QWORD PTR [r11+40]
	add r8, rcx
	mov r10, QWORD PTR [r11+56]
	add r10, rcx
	mov rcx, rdx
	add rcx, 16
	add rdx, 48
	mov rax, r11
	add rax, 80
	push rax
	push r9
	push r10
	call {vg_aes_gcm_encrypt_blocks_to_vaes_pclmul}
	pop rax
	pop rax
	pop rax
	jmp 212f
211:
212:
	jmp 210f
29:
210:
	jmp 28f
27:
28:
	mov r11, QWORD PTR [rsp+32]
	mov rcx, QWORD PTR [r11+48]
	mov rax, QWORD PTR [r11+64]
	sub rcx, rax
	test rcx, rcx
	je 213f
	mov rsi, QWORD PTR [r11+40]
	add rsi, rax
	mov rdi, QWORD PTR [r11+56]
	add rdi, rax
	mov r10d, 0
215:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 215b
	mov r11, QWORD PTR [rsp+32]
	mov rax, QWORD PTR [r11+64]
	mov r10, QWORD PTR [r11+48]
	sub r10, rax
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, QWORD PTR [r11+16]
	mov rcx, QWORD PTR [r11+24]
	mov r8, QWORD PTR [r11+32]
	add r8, rax
	mov r9, QWORD PTR [r11+56]
	add r9, rax
	push r10
	call {vg_aes_gcm_stream_encrypt_vaes_pclmul}
	pop rax
	jmp 214f
213:
214:
	lea rsp, [rsp+2232]
	ret
	.p2align 6
