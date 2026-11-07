// The functions of `src/internal/vg_rsa_prime_search.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_prime_search:
	lea rsp, [rsp-160]
	mov QWORD PTR [rsp+32], r12
	mov r12, rsp
	mov QWORD PTR [r12+40], rdi
	mov QWORD PTR [r12+48], rsi
	mov QWORD PTR [r12+56], rdx
	mov QWORD PTR [r12+64], rcx
	mov QWORD PTR [r12+72], r8
	mov QWORD PTR [r12+80], r9
	mov rax, QWORD PTR [rsp+168]
	mov QWORD PTR [r12+88], rax
	mov rax, QWORD PTR [rsp+176]
	mov QWORD PTR [r12+96], rax
	mov rax, QWORD PTR [rsp+184]
	mov QWORD PTR [r12+104], rax
	mov rax, QWORD PTR [rsp+192]
	mov QWORD PTR [r12+112], rax
	mov rax, QWORD PTR [rsp+200]
	mov QWORD PTR [r12+120], rax
	mov rax, QWORD PTR [rsp+208]
	mov QWORD PTR [r12+144], rax
	mov rcx, QWORD PTR [rax]
	mov QWORD PTR [r12], rcx
	mov QWORD PTR [r12+8], rsi
	mov rcx, rsi
	shl rcx, 15
	add rcx, rsi
	mov QWORD PTR [r12+16], rcx
	mov eax, 0
	mov QWORD PTR [r12+24], rax
	mov QWORD PTR [r12+128], rax
20:
	mov rax, QWORD PTR [r12]
	test rax, rax
	je 21f
	lea rsp, [rsp-40]
	mov rdi, QWORD PTR [r12+40]
	mov rsi, QWORD PTR [r12+48]
	mov rdx, QWORD PTR [r12+56]
	mov rcx, QWORD PTR [r12+64]
	mov r8, QWORD PTR [r12+72]
	mov r9, QWORD PTR [r12+80]
	mov rax, QWORD PTR [r12+88]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [r12+96]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [r12+104]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [r12+112]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [r12+120]
	mov QWORD PTR [rsp+32], rax
	call {vg_rsa_keygen_candidate}
	lea rsp, [rsp+40]
	mov eax, eax
	cmp rax, 1
	je 23f
	test rax, rax
	je 25f
	mov rdx, rax
	mov rcx, QWORD PTR [r12+56]
	mov rcx, QWORD PTR [rcx]
	test rcx, rcx
	je 27f
	mov rax, QWORD PTR [r12+96]
	add rax, rcx
	mov QWORD PTR [r12+96], rax
	mov rax, QWORD PTR [r12+104]
	sub rax, rcx
	mov QWORD PTR [r12+104], rax
	mov rax, QWORD PTR [r12+128]
	add rax, rcx
	mov QWORD PTR [r12+128], rax
	mov eax, 4
	mov QWORD PTR [r12+136], rax
	cmp rdx, 2
	je 29f
	mov rax, QWORD PTR [r12]
	sub rax, 1
	mov QWORD PTR [r12], rax
	jmp 210f
29:
210:
	jmp 28f
27:
	mov eax, 0
	mov QWORD PTR [r12], rax
	mov QWORD PTR [r12+24], rax
	mov eax, 3
	mov QWORD PTR [r12+136], rax
	mov rdi, r12
	mov rsi, QWORD PTR [rdi+40]
	mov rcx, QWORD PTR [rdi+48]
	mov eax, 0
211:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 211b
28:
	jmp 26f
25:
	mov rax, QWORD PTR [r12+104]
	cmp rax, QWORD PTR [r12+16]
	jae 212f
	mov rcx, QWORD PTR [r12+8]
	shl rcx, 4
	cmp rax, rcx
	cmovb rax, rcx
	shl rax, 1
	mov rcx, QWORD PTR [r12+16]
	cmp rax, rcx
	cmovae rax, rcx
	mov QWORD PTR [r12+24], rax
	mov eax, 0
	mov QWORD PTR [r12+136], rax
	jmp 213f
212:
	mov eax, 0
	mov QWORD PTR [r12], rax
	mov QWORD PTR [r12+24], rax
	mov eax, 3
	mov QWORD PTR [r12+136], rax
	mov rdi, r12
	mov rsi, QWORD PTR [rdi+40]
	mov rcx, QWORD PTR [rdi+48]
	mov eax, 0
214:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 214b
213:
26:
	jmp 24f
23:
	mov rcx, QWORD PTR [r12+56]
	mov rcx, QWORD PTR [rcx]
	mov rax, QWORD PTR [r12+128]
	add rax, rcx
	mov QWORD PTR [r12+128], rax
	mov eax, 0
	mov QWORD PTR [r12], rax
	mov QWORD PTR [r12+24], rax
	mov eax, 1
	mov QWORD PTR [r12+136], rax
24:
	jmp 22f
21:
	mov eax, 0
	mov QWORD PTR [r12], rax
	mov QWORD PTR [r12+24], rax
	mov eax, 3
	mov QWORD PTR [r12+136], rax
	mov rdi, r12
	mov rsi, QWORD PTR [rdi+40]
	mov rcx, QWORD PTR [rdi+48]
	mov eax, 0
215:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 215b
22:
	mov rax, QWORD PTR [r12+136]
	cmp rax, 4
	je 20b
	mov rax, QWORD PTR [r12+144]
	mov rcx, QWORD PTR [r12]
	mov rdx, QWORD PTR [r12+8]
	mov rsi, QWORD PTR [r12+16]
	mov rdi, QWORD PTR [r12+24]
	mov r8, QWORD PTR [r12+56]
	mov r9, QWORD PTR [r12+128]
	mov r10, QWORD PTR [r12+136]
	mov r11, QWORD PTR [r12+32]
	mov QWORD PTR [rax], rcx
	mov QWORD PTR [rax+8], rdx
	mov QWORD PTR [rax+16], rsi
	mov QWORD PTR [rax+24], rdi
	mov QWORD PTR [r8], r9
	mov rax, r10
	mov r12, r11
	lea rsp, [rsp+160]
	ret
	.p2align 6
