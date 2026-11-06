// The functions of `src/internal/vg_rsa_pkcs1_encrypt_precomputed_adx.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pkcs1_encrypt_precomputed_adx:
	lea rsp, [rsp-1112]
	mov r10, QWORD PTR [rsp+1152]
	mov r11, QWORD PTR [rsp+1160]
	mov rsi, QWORD PTR [rsp+1136]
	mov rax, QWORD PTR [rsp+1144]
	mov QWORD PTR [rsp+32], rdi
	mov QWORD PTR [rsp+40], rdx
	mov QWORD PTR [rsp+48], rcx
	mov QWORD PTR [rsp+56], r8
	mov QWORD PTR [rsp+64], r9
	mov rdi, rsp
	add rdi, 80
	mov QWORD PTR [rsp], rdi
	mov QWORD PTR [rsp+8], rcx
	mov QWORD PTR [rsp+16], r10
	mov QWORD PTR [rsp+24], r11
	mov rcx, rax
	mov eax, 0
	mov BYTE PTR [rsp+80], al
	mov eax, 2
	mov BYTE PTR [rsp+81], al
	mov r10d, 0
	mov edx, 0
20:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rsp+r10*1+82], al
	cmp rax, 1
	sbb r11, r11
	or rdx, r11
	add r10, 1
	cmp r10, rcx
	jne 20b
	mov rsi, QWORD PTR [rsp+1120]
	mov r11, QWORD PTR [rsp+1128]
	mov eax, 0
	mov BYTE PTR [rsp+rcx*1+82], al
	mov QWORD PTR [rsp+72], rdx
	mov rdi, rsp
	add rdi, rcx
	add rdi, 83
	mov rcx, r11
	mov r10d, 0
	test rcx, rcx
	jne 21f
	jmp 22f
21:
23:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 23b
22:
	mov rdi, QWORD PTR [rsp+32]
	mov rsi, QWORD PTR [rsp+48]
	mov rdx, QWORD PTR [rsp+40]
	mov rcx, QWORD PTR [rsp+48]
	mov r8, QWORD PTR [rsp+56]
	mov r9, QWORD PTR [rsp+64]
	mov rdx, QWORD PTR [rsp+1168]
	mov rcx, QWORD PTR [rsp+1176]
	call {vg_rsa_public_precomputed_checked_adx}
	mov rdx, QWORD PTR [rsp+72]
	xor rdx, -1
	and rax, rdx
	mov r11, rax
	mov rdi, QWORD PTR [rsp+32]
	mov rcx, QWORD PTR [rsp+48]
	mov r10d, 0
24:
	movzx eax, BYTE PTR [rdi+r10*1]
	and rax, rdx
	mov BYTE PTR [rdi+r10*1], al
	mov eax, 0
	mov BYTE PTR [rsp+r10*1+80], al
	add r10, 1
	cmp r10, rcx
	jne 24b
	mov rax, r11
	lea rsp, [rsp+1112]
	ret
	.p2align 6
