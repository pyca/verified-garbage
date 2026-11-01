// The functions of `src/pbkdf2_sha1.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_sha1_iterate:
	mov QWORD PTR [r8+112], rbx
	mov QWORD PTR [r8+120], rbp
	mov QWORD PTR [r8+128], r12
	mov QWORD PTR [r8+136], r13
	mov QWORD PTR [r8+144], r14
	mov QWORD PTR [r8+152], r15
	mov r15, r8
	mov r12, rdi
	mov r13, rcx
	mov r14d, edx
	mov rbx, r8
	add rbx, 160
	mov rbp, r8
	add rbp, 180
	mov eax, DWORD PTR [rsi]
	mov DWORD PTR [rbp], eax
	mov eax, DWORD PTR [rsi+4]
	mov DWORD PTR [rbp+4], eax
	mov eax, DWORD PTR [rsi+8]
	mov DWORD PTR [rbp+8], eax
	mov eax, DWORD PTR [rsi+12]
	mov DWORD PTR [rbp+12], eax
	mov eax, DWORD PTR [rsi+16]
	mov DWORD PTR [rbp+16], eax
	mov eax, 128
	mov DWORD PTR [rbp+20], eax
	mov eax, 0
	mov DWORD PTR [rbp+24], eax
	mov DWORD PTR [rbp+28], eax
	mov DWORD PTR [rbp+32], eax
	mov DWORD PTR [rbp+36], eax
	mov DWORD PTR [rbp+40], eax
	mov DWORD PTR [rbp+44], eax
	mov DWORD PTR [rbp+48], eax
	mov DWORD PTR [rbp+52], eax
	mov r12d, 84
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+76], rax
	mov r12, rdi
	test r14, r14
	je 20f
22:
	mov eax, DWORD PTR [r12]
	mov DWORD PTR [rbx], eax
	mov eax, DWORD PTR [r12+4]
	mov DWORD PTR [rbx+4], eax
	mov eax, DWORD PTR [r12+8]
	mov DWORD PTR [rbx+8], eax
	mov eax, DWORD PTR [r12+12]
	mov DWORD PTR [rbx+12], eax
	mov eax, DWORD PTR [r12+16]
	mov DWORD PTR [rbx+16], eax
	mov rsi, rbp
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha1_compress}
	mov rbx, rdi
	mov r15, rcx
	mov eax, DWORD PTR [rbx]
	bswap eax
	mov DWORD PTR [rbp], eax
	mov eax, DWORD PTR [rbx+4]
	bswap eax
	mov DWORD PTR [rbp+4], eax
	mov eax, DWORD PTR [rbx+8]
	bswap eax
	mov DWORD PTR [rbp+8], eax
	mov eax, DWORD PTR [rbx+12]
	bswap eax
	mov DWORD PTR [rbp+12], eax
	mov eax, DWORD PTR [rbx+16]
	bswap eax
	mov DWORD PTR [rbp+16], eax
	mov eax, DWORD PTR [r12+84]
	mov DWORD PTR [rbx], eax
	mov eax, DWORD PTR [r12+88]
	mov DWORD PTR [rbx+4], eax
	mov eax, DWORD PTR [r12+92]
	mov DWORD PTR [rbx+8], eax
	mov eax, DWORD PTR [r12+96]
	mov DWORD PTR [rbx+12], eax
	mov eax, DWORD PTR [r12+100]
	mov DWORD PTR [rbx+16], eax
	mov rsi, rbp
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha1_compress}
	mov rbx, rdi
	mov r15, rcx
	mov eax, DWORD PTR [rbx]
	bswap eax
	mov DWORD PTR [rbp], eax
	mov eax, DWORD PTR [rbx+4]
	bswap eax
	mov DWORD PTR [rbp+4], eax
	mov eax, DWORD PTR [rbx+8]
	bswap eax
	mov DWORD PTR [rbp+8], eax
	mov eax, DWORD PTR [rbx+12]
	bswap eax
	mov DWORD PTR [rbp+12], eax
	mov eax, DWORD PTR [rbx+16]
	bswap eax
	mov DWORD PTR [rbp+16], eax
	mov eax, DWORD PTR [rbp]
	xor eax, DWORD PTR [r13]
	mov DWORD PTR [r13], eax
	mov eax, DWORD PTR [rbp+4]
	xor eax, DWORD PTR [r13+4]
	mov DWORD PTR [r13+4], eax
	mov eax, DWORD PTR [rbp+8]
	xor eax, DWORD PTR [r13+8]
	mov DWORD PTR [r13+8], eax
	mov eax, DWORD PTR [rbp+12]
	xor eax, DWORD PTR [r13+12]
	mov DWORD PTR [r13+12], eax
	mov eax, DWORD PTR [rbp+16]
	xor eax, DWORD PTR [r13+16]
	mov DWORD PTR [r13+16], eax
	sub r14, 1
	jne 22b
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+112]
	mov rbp, QWORD PTR [r15+120]
	mov r12, QWORD PTR [r15+128]
	mov r13, QWORD PTR [r15+136]
	mov r14, QWORD PTR [r15+144]
	mov r15, QWORD PTR [r15+152]
	ret
	.p2align 6

vg_pbkdf2_hmac_sha1:
	lea rsp, [rsp-1144]
	mov rax, QWORD PTR [rsp+1152]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov r10, r8
	mov r8, QWORD PTR [rsp+16]
	mov QWORD PTR [r8+448], rbx
	mov QWORD PTR [r8+456], rbp
	mov QWORD PTR [r8+464], r12
	mov QWORD PTR [r8+472], r13
	mov QWORD PTR [r8+480], r14
	mov QWORD PTR [r8+488], r15
	mov r15, r8
	mov QWORD PTR [r15+496], r9
	mov eax, r10d
	sub rax, 1
	mov QWORD PTR [r15+504], rax
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rdx
	mov r13, rcx
	cmp rbp, 65
	jae 20f
	mov rdx, rbx
	mov rcx, rbp
	jmp 21f
20:
	mov rdi, r15
	add rdi, 764
	call {vg_sha1_init}
	mov rdi, r15
	add rdi, 764
	mov esi, 0
	mov rdx, rbx
	mov rcx, rbp
	mov r8, r15
	call {vg_sha1_update_scratch}
	mov rdi, r15
	add rdi, 764
	mov rsi, rbp
	mov rdx, r15
	add rdx, 888
	mov rcx, r15
	call {vg_sha1_finalize_scratch}
	mov rdx, r15
	add rdx, 888
	mov ecx, 20
21:
	mov rdi, r15
	add rdi, 512
	mov rsi, r15
	add rsi, 596
	mov r8, r15
	call {vg_hmac_sha1_init_scratch}
	mov r14d, 0
22:
	movzx eax, BYTE PTR [r15+r14*1+512]
	mov BYTE PTR [r15+r14*1+680], al
	add r14, 1
	cmp r14, 84
	jne 22b
	mov rdi, r15
	add rdi, 680
	mov esi, 64
	mov rdx, r12
	mov rcx, r13
	mov r8, r15
	call {vg_sha1_update_scratch}
	mov rbp, r13
	mov r13, QWORD PTR [r15+496]
	mov r12, QWORD PTR [rsp+8]
	mov ebx, 1
	test r12, r12
	je 23f
25:
	mov r14d, 0
26:
	movzx eax, BYTE PTR [r15+r14*1+680]
	mov BYTE PTR [r15+r14*1+764], al
	add r14, 1
	cmp r14, 84
	jne 26b
	mov eax, ebx
	bswap eax
	mov DWORD PTR [r15+908], eax
	mov rdi, r15
	add rdi, 764
	mov rsi, rbp
	add rsi, 64
	mov rdx, r15
	add rdx, 908
	mov ecx, 4
	mov r8, r15
	call {vg_sha1_update_scratch}
	mov rdi, r15
	add rdi, 764
	mov rsi, r15
	add rsi, 596
	mov rdx, rbp
	add rdx, 68
	mov rcx, r15
	add rcx, 848
	mov r8, r15
	call {vg_hmac_sha1_finalize_scratch}
	mov r14d, 0
27:
	movzx eax, BYTE PTR [r15+r14*1+848]
	mov BYTE PTR [r15+r14*1+868], al
	add r14, 1
	cmp r14, 20
	jne 27b
	mov rdi, r15
	add rdi, 512
	mov rsi, r15
	add rsi, 848
	mov rdx, QWORD PTR [r15+504]
	mov rcx, r15
	add rcx, 868
	mov r8, r15
	call {vg_pbkdf2_hmac_sha1_iterate}
	mov ecx, 20
	cmp r12, rcx
	jb 28f
	jmp 29f
28:
	mov rcx, r12
29:
	mov r14d, 0
210:
	movzx eax, BYTE PTR [r15+r14*1+868]
	mov BYTE PTR [r13+r14*1], al
	add r14, 1
	cmp r14, rcx
	jne 210b
	add r13, rcx
	add rbx, 1
	sub r12, rcx
	jne 25b
	jmp 24f
23:
24:
	mov rbx, QWORD PTR [r15+448]
	mov rbp, QWORD PTR [r15+456]
	mov r12, QWORD PTR [r15+464]
	mov r13, QWORD PTR [r15+472]
	mov r14, QWORD PTR [r15+480]
	mov r15, QWORD PTR [r15+488]
	lea rsp, [rsp+1144]
	ret
	.p2align 6

vg_pbkdf2_hmac_sha1_iterate_shani:
	mov QWORD PTR [r8+112], rbx
	mov QWORD PTR [r8+120], rbp
	mov QWORD PTR [r8+128], r12
	mov QWORD PTR [r8+136], r13
	mov QWORD PTR [r8+144], r14
	mov QWORD PTR [r8+152], r15
	mov r15, r8
	mov r12, rdi
	mov r13, rcx
	mov r14d, edx
	mov rbx, r8
	add rbx, 160
	mov rbp, r8
	add rbp, 180
	mov eax, DWORD PTR [rsi]
	mov DWORD PTR [rbp], eax
	mov eax, DWORD PTR [rsi+4]
	mov DWORD PTR [rbp+4], eax
	mov eax, DWORD PTR [rsi+8]
	mov DWORD PTR [rbp+8], eax
	mov eax, DWORD PTR [rsi+12]
	mov DWORD PTR [rbp+12], eax
	mov eax, DWORD PTR [rsi+16]
	mov DWORD PTR [rbp+16], eax
	mov eax, 128
	mov DWORD PTR [rbp+20], eax
	mov eax, 0
	mov DWORD PTR [rbp+24], eax
	mov DWORD PTR [rbp+28], eax
	mov DWORD PTR [rbp+32], eax
	mov DWORD PTR [rbp+36], eax
	mov DWORD PTR [rbp+40], eax
	mov DWORD PTR [rbp+44], eax
	mov DWORD PTR [rbp+48], eax
	mov DWORD PTR [rbp+52], eax
	mov r12d, 84
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+76], rax
	mov r12, rdi
	test r14, r14
	je 20f
22:
	mov eax, DWORD PTR [r12]
	mov DWORD PTR [rbx], eax
	mov eax, DWORD PTR [r12+4]
	mov DWORD PTR [rbx+4], eax
	mov eax, DWORD PTR [r12+8]
	mov DWORD PTR [rbx+8], eax
	mov eax, DWORD PTR [r12+12]
	mov DWORD PTR [rbx+12], eax
	mov eax, DWORD PTR [r12+16]
	mov DWORD PTR [rbx+16], eax
	mov rsi, rbp
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha1_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov eax, DWORD PTR [rbx]
	bswap eax
	mov DWORD PTR [rbp], eax
	mov eax, DWORD PTR [rbx+4]
	bswap eax
	mov DWORD PTR [rbp+4], eax
	mov eax, DWORD PTR [rbx+8]
	bswap eax
	mov DWORD PTR [rbp+8], eax
	mov eax, DWORD PTR [rbx+12]
	bswap eax
	mov DWORD PTR [rbp+12], eax
	mov eax, DWORD PTR [rbx+16]
	bswap eax
	mov DWORD PTR [rbp+16], eax
	mov eax, DWORD PTR [r12+84]
	mov DWORD PTR [rbx], eax
	mov eax, DWORD PTR [r12+88]
	mov DWORD PTR [rbx+4], eax
	mov eax, DWORD PTR [r12+92]
	mov DWORD PTR [rbx+8], eax
	mov eax, DWORD PTR [r12+96]
	mov DWORD PTR [rbx+12], eax
	mov eax, DWORD PTR [r12+100]
	mov DWORD PTR [rbx+16], eax
	mov rsi, rbp
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha1_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov eax, DWORD PTR [rbx]
	bswap eax
	mov DWORD PTR [rbp], eax
	mov eax, DWORD PTR [rbx+4]
	bswap eax
	mov DWORD PTR [rbp+4], eax
	mov eax, DWORD PTR [rbx+8]
	bswap eax
	mov DWORD PTR [rbp+8], eax
	mov eax, DWORD PTR [rbx+12]
	bswap eax
	mov DWORD PTR [rbp+12], eax
	mov eax, DWORD PTR [rbx+16]
	bswap eax
	mov DWORD PTR [rbp+16], eax
	mov eax, DWORD PTR [rbp]
	xor eax, DWORD PTR [r13]
	mov DWORD PTR [r13], eax
	mov eax, DWORD PTR [rbp+4]
	xor eax, DWORD PTR [r13+4]
	mov DWORD PTR [r13+4], eax
	mov eax, DWORD PTR [rbp+8]
	xor eax, DWORD PTR [r13+8]
	mov DWORD PTR [r13+8], eax
	mov eax, DWORD PTR [rbp+12]
	xor eax, DWORD PTR [r13+12]
	mov DWORD PTR [r13+12], eax
	mov eax, DWORD PTR [rbp+16]
	xor eax, DWORD PTR [r13+16]
	mov DWORD PTR [r13+16], eax
	sub r14, 1
	jne 22b
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+112]
	mov rbp, QWORD PTR [r15+120]
	mov r12, QWORD PTR [r15+128]
	mov r13, QWORD PTR [r15+136]
	mov r14, QWORD PTR [r15+144]
	mov r15, QWORD PTR [r15+152]
	ret
	.p2align 6

vg_pbkdf2_hmac_sha1_shani:
	lea rsp, [rsp-1144]
	mov rax, QWORD PTR [rsp+1152]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov r10, r8
	mov r8, QWORD PTR [rsp+16]
	mov QWORD PTR [r8+448], rbx
	mov QWORD PTR [r8+456], rbp
	mov QWORD PTR [r8+464], r12
	mov QWORD PTR [r8+472], r13
	mov QWORD PTR [r8+480], r14
	mov QWORD PTR [r8+488], r15
	mov r15, r8
	mov QWORD PTR [r15+496], r9
	mov eax, r10d
	sub rax, 1
	mov QWORD PTR [r15+504], rax
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rdx
	mov r13, rcx
	cmp rbp, 65
	jae 20f
	mov rdx, rbx
	mov rcx, rbp
	jmp 21f
20:
	mov rdi, r15
	add rdi, 764
	call {vg_sha1_init}
	mov rdi, r15
	add rdi, 764
	mov esi, 0
	mov rdx, rbx
	mov rcx, rbp
	mov r8, r15
	call {vg_sha1_update_scratch_shani}
	mov rdi, r15
	add rdi, 764
	mov rsi, rbp
	mov rdx, r15
	add rdx, 888
	mov rcx, r15
	call {vg_sha1_finalize_scratch_shani}
	mov rdx, r15
	add rdx, 888
	mov ecx, 20
21:
	mov rdi, r15
	add rdi, 512
	mov rsi, r15
	add rsi, 596
	mov r8, r15
	call {vg_hmac_sha1_init_scratch_shani}
	mov r14d, 0
22:
	movzx eax, BYTE PTR [r15+r14*1+512]
	mov BYTE PTR [r15+r14*1+680], al
	add r14, 1
	cmp r14, 84
	jne 22b
	mov rdi, r15
	add rdi, 680
	mov esi, 64
	mov rdx, r12
	mov rcx, r13
	mov r8, r15
	call {vg_sha1_update_scratch_shani}
	mov rbp, r13
	mov r13, QWORD PTR [r15+496]
	mov r12, QWORD PTR [rsp+8]
	mov ebx, 1
	test r12, r12
	je 23f
25:
	mov r14d, 0
26:
	movzx eax, BYTE PTR [r15+r14*1+680]
	mov BYTE PTR [r15+r14*1+764], al
	add r14, 1
	cmp r14, 84
	jne 26b
	mov eax, ebx
	bswap eax
	mov DWORD PTR [r15+908], eax
	mov rdi, r15
	add rdi, 764
	mov rsi, rbp
	add rsi, 64
	mov rdx, r15
	add rdx, 908
	mov ecx, 4
	mov r8, r15
	call {vg_sha1_update_scratch_shani}
	mov rdi, r15
	add rdi, 764
	mov rsi, r15
	add rsi, 596
	mov rdx, rbp
	add rdx, 68
	mov rcx, r15
	add rcx, 848
	mov r8, r15
	call {vg_hmac_sha1_finalize_scratch_shani}
	mov r14d, 0
27:
	movzx eax, BYTE PTR [r15+r14*1+848]
	mov BYTE PTR [r15+r14*1+868], al
	add r14, 1
	cmp r14, 20
	jne 27b
	mov rdi, r15
	add rdi, 512
	mov rsi, r15
	add rsi, 848
	mov rdx, QWORD PTR [r15+504]
	mov rcx, r15
	add rcx, 868
	mov r8, r15
	call {vg_pbkdf2_hmac_sha1_iterate_shani}
	mov ecx, 20
	cmp r12, rcx
	jb 28f
	jmp 29f
28:
	mov rcx, r12
29:
	mov r14d, 0
210:
	movzx eax, BYTE PTR [r15+r14*1+868]
	mov BYTE PTR [r13+r14*1], al
	add r14, 1
	cmp r14, rcx
	jne 210b
	add r13, rcx
	add rbx, 1
	sub r12, rcx
	jne 25b
	jmp 24f
23:
24:
	mov rbx, QWORD PTR [r15+448]
	mov rbp, QWORD PTR [r15+456]
	mov r12, QWORD PTR [r15+464]
	mov r13, QWORD PTR [r15+472]
	mov r14, QWORD PTR [r15+480]
	mov r15, QWORD PTR [r15+488]
	lea rsp, [rsp+1144]
	ret
	.p2align 6
