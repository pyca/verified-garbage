// The functions of `src/pbkdf2_sha224.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_sha224_iterate:
	mov QWORD PTR [r8+560], rbx
	mov QWORD PTR [r8+568], rbp
	mov QWORD PTR [r8+576], r12
	mov QWORD PTR [r8+584], r13
	mov QWORD PTR [r8+592], r14
	mov QWORD PTR [r8+600], r15
	mov r15, r8
	mov r12, rdi
	mov r13, rcx
	mov r14d, edx
	mov rbx, r8
	add rbx, 608
	mov rbp, r8
	add rbp, 640
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
	mov eax, DWORD PTR [rsi+20]
	mov DWORD PTR [rbp+20], eax
	mov eax, DWORD PTR [rsi+24]
	mov DWORD PTR [rbp+24], eax
	mov eax, 128
	mov DWORD PTR [rbp+28], eax
	mov eax, 0
	mov DWORD PTR [rbp+32], eax
	mov DWORD PTR [rbp+36], eax
	mov DWORD PTR [rbp+40], eax
	mov DWORD PTR [rbp+44], eax
	mov DWORD PTR [rbp+48], eax
	mov DWORD PTR [rbp+52], eax
	mov r12d, 92
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+88], rax
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
	mov eax, DWORD PTR [r12+20]
	mov DWORD PTR [rbx+20], eax
	mov eax, DWORD PTR [r12+24]
	mov DWORD PTR [rbx+24], eax
	mov eax, DWORD PTR [r12+28]
	mov DWORD PTR [rbx+28], eax
	mov rsi, rbp
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress}
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
	mov eax, DWORD PTR [rbx+20]
	bswap eax
	mov DWORD PTR [rbp+20], eax
	mov eax, DWORD PTR [rbx+24]
	bswap eax
	mov DWORD PTR [rbp+24], eax
	mov eax, DWORD PTR [rbx+28]
	bswap eax
	mov DWORD PTR [rbp+28], eax
	mov eax, 128
	mov DWORD PTR [rbp+28], eax
	mov eax, 0
	mov eax, DWORD PTR [r12+96]
	mov DWORD PTR [rbx], eax
	mov eax, DWORD PTR [r12+100]
	mov DWORD PTR [rbx+4], eax
	mov eax, DWORD PTR [r12+104]
	mov DWORD PTR [rbx+8], eax
	mov eax, DWORD PTR [r12+108]
	mov DWORD PTR [rbx+12], eax
	mov eax, DWORD PTR [r12+112]
	mov DWORD PTR [rbx+16], eax
	mov eax, DWORD PTR [r12+116]
	mov DWORD PTR [rbx+20], eax
	mov eax, DWORD PTR [r12+120]
	mov DWORD PTR [rbx+24], eax
	mov eax, DWORD PTR [r12+124]
	mov DWORD PTR [rbx+28], eax
	mov rsi, rbp
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress}
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
	mov eax, DWORD PTR [rbx+20]
	bswap eax
	mov DWORD PTR [rbp+20], eax
	mov eax, DWORD PTR [rbx+24]
	bswap eax
	mov DWORD PTR [rbp+24], eax
	mov eax, DWORD PTR [rbx+28]
	bswap eax
	mov DWORD PTR [rbp+28], eax
	mov eax, 128
	mov DWORD PTR [rbp+28], eax
	mov eax, 0
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
	mov eax, DWORD PTR [rbp+20]
	xor eax, DWORD PTR [r13+20]
	mov DWORD PTR [r13+20], eax
	mov eax, DWORD PTR [rbp+24]
	xor eax, DWORD PTR [r13+24]
	mov DWORD PTR [r13+24], eax
	sub r14, 1
	jne 22b
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+560]
	mov rbp, QWORD PTR [r15+568]
	mov r12, QWORD PTR [r15+576]
	mov r13, QWORD PTR [r15+584]
	mov r14, QWORD PTR [r15+592]
	mov r15, QWORD PTR [r15+600]
	ret
	.p2align 6

vg_pbkdf2_hmac_sha224:
	lea rsp, [rsp-1624]
	mov rax, QWORD PTR [rsp+1632]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov r10, r8
	mov r8, QWORD PTR [rsp+16]
	mov QWORD PTR [r8+832], rbx
	mov QWORD PTR [r8+840], rbp
	mov QWORD PTR [r8+848], r12
	mov QWORD PTR [r8+856], r13
	mov QWORD PTR [r8+864], r14
	mov QWORD PTR [r8+872], r15
	mov r15, r8
	mov QWORD PTR [r15+880], r9
	mov eax, r10d
	sub rax, 1
	mov QWORD PTR [r15+888], rax
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
	add rdi, 1184
	call {vg_sha224_init}
	mov rdi, r15
	add rdi, 1184
	mov esi, 0
	mov rdx, rbx
	mov rcx, rbp
	mov r8, r15
	call {vg_sha256_update_scratch}
	mov rdi, r15
	add rdi, 1184
	mov rsi, rbp
	mov rdx, r15
	add rdx, 1336
	mov rcx, r15
	call {vg_sha256_finalize_scratch}
	mov rdx, r15
	add rdx, 1336
	mov ecx, 28
21:
	mov rdi, r15
	add rdi, 896
	mov rsi, r15
	add rsi, 992
	mov r8, r15
	call {vg_hmac_sha224_init_scratch}
	mov r14d, 0
22:
	movzx eax, BYTE PTR [r15+r14*1+896]
	mov BYTE PTR [r15+r14*1+1088], al
	add r14, 1
	cmp r14, 96
	jne 22b
	mov rdi, r15
	add rdi, 1088
	mov esi, 64
	mov rdx, r12
	mov rcx, r13
	mov r8, r15
	call {vg_sha256_update_scratch}
	mov rbp, r13
	mov r13, QWORD PTR [r15+880]
	mov r12, QWORD PTR [rsp+8]
	mov ebx, 1
	test r12, r12
	je 23f
25:
	mov r14d, 0
26:
	movzx eax, BYTE PTR [r15+r14*1+1088]
	mov BYTE PTR [r15+r14*1+1184], al
	add r14, 1
	cmp r14, 96
	jne 26b
	mov eax, ebx
	bswap eax
	mov DWORD PTR [r15+1368], eax
	mov rdi, r15
	add rdi, 1184
	mov rsi, rbp
	add rsi, 64
	mov rdx, r15
	add rdx, 1368
	mov ecx, 4
	mov r8, r15
	call {vg_sha256_update_scratch}
	mov rdi, r15
	add rdi, 1184
	mov rsi, r15
	add rsi, 992
	mov rdx, rbp
	add rdx, 68
	mov rcx, r15
	add rcx, 1280
	mov r8, r15
	call {vg_hmac_sha224_finalize_scratch}
	mov r14d, 0
27:
	movzx eax, BYTE PTR [r15+r14*1+1280]
	mov BYTE PTR [r15+r14*1+1308], al
	add r14, 1
	cmp r14, 28
	jne 27b
	mov rdi, r15
	add rdi, 896
	mov rsi, r15
	add rsi, 1280
	mov rdx, QWORD PTR [r15+888]
	mov rcx, r15
	add rcx, 1308
	mov r8, r15
	call {vg_pbkdf2_hmac_sha224_iterate}
	mov ecx, 28
	cmp r12, rcx
	jb 28f
	jmp 29f
28:
	mov rcx, r12
29:
	mov r14d, 0
210:
	movzx eax, BYTE PTR [r15+r14*1+1308]
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
	mov rbx, QWORD PTR [r15+832]
	mov rbp, QWORD PTR [r15+840]
	mov r12, QWORD PTR [r15+848]
	mov r13, QWORD PTR [r15+856]
	mov r14, QWORD PTR [r15+864]
	mov r15, QWORD PTR [r15+872]
	lea rsp, [rsp+1624]
	ret
	.p2align 6

vg_pbkdf2_hmac_sha224_iterate_avx2:
	mov QWORD PTR [r8+560], rbx
	mov QWORD PTR [r8+568], rbp
	mov QWORD PTR [r8+576], r12
	mov QWORD PTR [r8+584], r13
	mov QWORD PTR [r8+592], r14
	mov QWORD PTR [r8+600], r15
	mov r15, r8
	mov r12, rdi
	mov r13, rcx
	mov r14d, edx
	mov rbx, r8
	add rbx, 608
	mov rbp, r8
	add rbp, 640
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
	mov eax, DWORD PTR [rsi+20]
	mov DWORD PTR [rbp+20], eax
	mov eax, DWORD PTR [rsi+24]
	mov DWORD PTR [rbp+24], eax
	mov eax, 128
	mov DWORD PTR [rbp+28], eax
	mov eax, 0
	mov DWORD PTR [rbp+32], eax
	mov DWORD PTR [rbp+36], eax
	mov DWORD PTR [rbp+40], eax
	mov DWORD PTR [rbp+44], eax
	mov DWORD PTR [rbp+48], eax
	mov DWORD PTR [rbp+52], eax
	mov r12d, 92
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+88], rax
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
	mov eax, DWORD PTR [r12+20]
	mov DWORD PTR [rbx+20], eax
	mov eax, DWORD PTR [r12+24]
	mov DWORD PTR [rbx+24], eax
	mov eax, DWORD PTR [r12+28]
	mov DWORD PTR [rbx+28], eax
	mov rsi, rbp
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress_avx2}
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
	mov eax, DWORD PTR [rbx+20]
	bswap eax
	mov DWORD PTR [rbp+20], eax
	mov eax, DWORD PTR [rbx+24]
	bswap eax
	mov DWORD PTR [rbp+24], eax
	mov eax, DWORD PTR [rbx+28]
	bswap eax
	mov DWORD PTR [rbp+28], eax
	mov eax, 128
	mov DWORD PTR [rbp+28], eax
	mov eax, 0
	mov eax, DWORD PTR [r12+96]
	mov DWORD PTR [rbx], eax
	mov eax, DWORD PTR [r12+100]
	mov DWORD PTR [rbx+4], eax
	mov eax, DWORD PTR [r12+104]
	mov DWORD PTR [rbx+8], eax
	mov eax, DWORD PTR [r12+108]
	mov DWORD PTR [rbx+12], eax
	mov eax, DWORD PTR [r12+112]
	mov DWORD PTR [rbx+16], eax
	mov eax, DWORD PTR [r12+116]
	mov DWORD PTR [rbx+20], eax
	mov eax, DWORD PTR [r12+120]
	mov DWORD PTR [rbx+24], eax
	mov eax, DWORD PTR [r12+124]
	mov DWORD PTR [rbx+28], eax
	mov rsi, rbp
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress_avx2}
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
	mov eax, DWORD PTR [rbx+20]
	bswap eax
	mov DWORD PTR [rbp+20], eax
	mov eax, DWORD PTR [rbx+24]
	bswap eax
	mov DWORD PTR [rbp+24], eax
	mov eax, DWORD PTR [rbx+28]
	bswap eax
	mov DWORD PTR [rbp+28], eax
	mov eax, 128
	mov DWORD PTR [rbp+28], eax
	mov eax, 0
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
	mov eax, DWORD PTR [rbp+20]
	xor eax, DWORD PTR [r13+20]
	mov DWORD PTR [r13+20], eax
	mov eax, DWORD PTR [rbp+24]
	xor eax, DWORD PTR [r13+24]
	mov DWORD PTR [r13+24], eax
	sub r14, 1
	jne 22b
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+560]
	mov rbp, QWORD PTR [r15+568]
	mov r12, QWORD PTR [r15+576]
	mov r13, QWORD PTR [r15+584]
	mov r14, QWORD PTR [r15+592]
	mov r15, QWORD PTR [r15+600]
	ret
	.p2align 6

vg_pbkdf2_hmac_sha224_avx2:
	lea rsp, [rsp-1624]
	mov rax, QWORD PTR [rsp+1632]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov r10, r8
	mov r8, QWORD PTR [rsp+16]
	mov QWORD PTR [r8+832], rbx
	mov QWORD PTR [r8+840], rbp
	mov QWORD PTR [r8+848], r12
	mov QWORD PTR [r8+856], r13
	mov QWORD PTR [r8+864], r14
	mov QWORD PTR [r8+872], r15
	mov r15, r8
	mov QWORD PTR [r15+880], r9
	mov eax, r10d
	sub rax, 1
	mov QWORD PTR [r15+888], rax
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
	add rdi, 1184
	call {vg_sha224_init}
	mov rdi, r15
	add rdi, 1184
	mov esi, 0
	mov rdx, rbx
	mov rcx, rbp
	mov r8, r15
	call {vg_sha256_update_scratch_avx2}
	mov rdi, r15
	add rdi, 1184
	mov rsi, rbp
	mov rdx, r15
	add rdx, 1336
	mov rcx, r15
	call {vg_sha256_finalize_scratch_avx2}
	mov rdx, r15
	add rdx, 1336
	mov ecx, 28
21:
	mov rdi, r15
	add rdi, 896
	mov rsi, r15
	add rsi, 992
	mov r8, r15
	call {vg_hmac_sha224_init_scratch_avx2}
	mov r14d, 0
22:
	movzx eax, BYTE PTR [r15+r14*1+896]
	mov BYTE PTR [r15+r14*1+1088], al
	add r14, 1
	cmp r14, 96
	jne 22b
	mov rdi, r15
	add rdi, 1088
	mov esi, 64
	mov rdx, r12
	mov rcx, r13
	mov r8, r15
	call {vg_sha256_update_scratch_avx2}
	mov rbp, r13
	mov r13, QWORD PTR [r15+880]
	mov r12, QWORD PTR [rsp+8]
	mov ebx, 1
	test r12, r12
	je 23f
25:
	mov r14d, 0
26:
	movzx eax, BYTE PTR [r15+r14*1+1088]
	mov BYTE PTR [r15+r14*1+1184], al
	add r14, 1
	cmp r14, 96
	jne 26b
	mov eax, ebx
	bswap eax
	mov DWORD PTR [r15+1368], eax
	mov rdi, r15
	add rdi, 1184
	mov rsi, rbp
	add rsi, 64
	mov rdx, r15
	add rdx, 1368
	mov ecx, 4
	mov r8, r15
	call {vg_sha256_update_scratch_avx2}
	mov rdi, r15
	add rdi, 1184
	mov rsi, r15
	add rsi, 992
	mov rdx, rbp
	add rdx, 68
	mov rcx, r15
	add rcx, 1280
	mov r8, r15
	call {vg_hmac_sha224_finalize_scratch_avx2}
	mov r14d, 0
27:
	movzx eax, BYTE PTR [r15+r14*1+1280]
	mov BYTE PTR [r15+r14*1+1308], al
	add r14, 1
	cmp r14, 28
	jne 27b
	mov rdi, r15
	add rdi, 896
	mov rsi, r15
	add rsi, 1280
	mov rdx, QWORD PTR [r15+888]
	mov rcx, r15
	add rcx, 1308
	mov r8, r15
	call {vg_pbkdf2_hmac_sha224_iterate_avx2}
	mov ecx, 28
	cmp r12, rcx
	jb 28f
	jmp 29f
28:
	mov rcx, r12
29:
	mov r14d, 0
210:
	movzx eax, BYTE PTR [r15+r14*1+1308]
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
	mov rbx, QWORD PTR [r15+832]
	mov rbp, QWORD PTR [r15+840]
	mov r12, QWORD PTR [r15+848]
	mov r13, QWORD PTR [r15+856]
	mov r14, QWORD PTR [r15+864]
	mov r15, QWORD PTR [r15+872]
	lea rsp, [rsp+1624]
	ret
	.p2align 6

vg_pbkdf2_hmac_sha224_iterate_shani:
	mov QWORD PTR [r8+560], rbx
	mov QWORD PTR [r8+568], rbp
	mov QWORD PTR [r8+576], r12
	mov QWORD PTR [r8+584], r13
	mov QWORD PTR [r8+592], r14
	mov QWORD PTR [r8+600], r15
	mov r15, r8
	mov r12, rdi
	mov r13, rcx
	mov r14d, edx
	mov rbx, r8
	add rbx, 608
	mov rbp, r8
	add rbp, 640
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
	mov eax, DWORD PTR [rsi+20]
	mov DWORD PTR [rbp+20], eax
	mov eax, DWORD PTR [rsi+24]
	mov DWORD PTR [rbp+24], eax
	mov eax, 128
	mov DWORD PTR [rbp+28], eax
	mov eax, 0
	mov DWORD PTR [rbp+32], eax
	mov DWORD PTR [rbp+36], eax
	mov DWORD PTR [rbp+40], eax
	mov DWORD PTR [rbp+44], eax
	mov DWORD PTR [rbp+48], eax
	mov DWORD PTR [rbp+52], eax
	mov r12d, 92
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [rbx+88], rax
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
	mov eax, DWORD PTR [r12+20]
	mov DWORD PTR [rbx+20], eax
	mov eax, DWORD PTR [r12+24]
	mov DWORD PTR [rbx+24], eax
	mov eax, DWORD PTR [r12+28]
	mov DWORD PTR [rbx+28], eax
	mov rsi, rbp
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress_shani}
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
	mov eax, DWORD PTR [rbx+20]
	bswap eax
	mov DWORD PTR [rbp+20], eax
	mov eax, DWORD PTR [rbx+24]
	bswap eax
	mov DWORD PTR [rbp+24], eax
	mov eax, DWORD PTR [rbx+28]
	bswap eax
	mov DWORD PTR [rbp+28], eax
	mov eax, 128
	mov DWORD PTR [rbp+28], eax
	mov eax, 0
	mov eax, DWORD PTR [r12+96]
	mov DWORD PTR [rbx], eax
	mov eax, DWORD PTR [r12+100]
	mov DWORD PTR [rbx+4], eax
	mov eax, DWORD PTR [r12+104]
	mov DWORD PTR [rbx+8], eax
	mov eax, DWORD PTR [r12+108]
	mov DWORD PTR [rbx+12], eax
	mov eax, DWORD PTR [r12+112]
	mov DWORD PTR [rbx+16], eax
	mov eax, DWORD PTR [r12+116]
	mov DWORD PTR [rbx+20], eax
	mov eax, DWORD PTR [r12+120]
	mov DWORD PTR [rbx+24], eax
	mov eax, DWORD PTR [r12+124]
	mov DWORD PTR [rbx+28], eax
	mov rsi, rbp
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha256_compress_shani}
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
	mov eax, DWORD PTR [rbx+20]
	bswap eax
	mov DWORD PTR [rbp+20], eax
	mov eax, DWORD PTR [rbx+24]
	bswap eax
	mov DWORD PTR [rbp+24], eax
	mov eax, DWORD PTR [rbx+28]
	bswap eax
	mov DWORD PTR [rbp+28], eax
	mov eax, 128
	mov DWORD PTR [rbp+28], eax
	mov eax, 0
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
	mov eax, DWORD PTR [rbp+20]
	xor eax, DWORD PTR [r13+20]
	mov DWORD PTR [r13+20], eax
	mov eax, DWORD PTR [rbp+24]
	xor eax, DWORD PTR [r13+24]
	mov DWORD PTR [r13+24], eax
	sub r14, 1
	jne 22b
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+560]
	mov rbp, QWORD PTR [r15+568]
	mov r12, QWORD PTR [r15+576]
	mov r13, QWORD PTR [r15+584]
	mov r14, QWORD PTR [r15+592]
	mov r15, QWORD PTR [r15+600]
	ret
	.p2align 6

vg_pbkdf2_hmac_sha224_shani:
	lea rsp, [rsp-1624]
	mov rax, QWORD PTR [rsp+1632]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov r10, r8
	mov r8, QWORD PTR [rsp+16]
	mov QWORD PTR [r8+832], rbx
	mov QWORD PTR [r8+840], rbp
	mov QWORD PTR [r8+848], r12
	mov QWORD PTR [r8+856], r13
	mov QWORD PTR [r8+864], r14
	mov QWORD PTR [r8+872], r15
	mov r15, r8
	mov QWORD PTR [r15+880], r9
	mov eax, r10d
	sub rax, 1
	mov QWORD PTR [r15+888], rax
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
	add rdi, 1184
	call {vg_sha224_init}
	mov rdi, r15
	add rdi, 1184
	mov esi, 0
	mov rdx, rbx
	mov rcx, rbp
	mov r8, r15
	call {vg_sha256_update_scratch_shani}
	mov rdi, r15
	add rdi, 1184
	mov rsi, rbp
	mov rdx, r15
	add rdx, 1336
	mov rcx, r15
	call {vg_sha256_finalize_scratch_shani}
	mov rdx, r15
	add rdx, 1336
	mov ecx, 28
21:
	mov rdi, r15
	add rdi, 896
	mov rsi, r15
	add rsi, 992
	mov r8, r15
	call {vg_hmac_sha224_init_scratch_shani}
	mov r14d, 0
22:
	movzx eax, BYTE PTR [r15+r14*1+896]
	mov BYTE PTR [r15+r14*1+1088], al
	add r14, 1
	cmp r14, 96
	jne 22b
	mov rdi, r15
	add rdi, 1088
	mov esi, 64
	mov rdx, r12
	mov rcx, r13
	mov r8, r15
	call {vg_sha256_update_scratch_shani}
	mov rbp, r13
	mov r13, QWORD PTR [r15+880]
	mov r12, QWORD PTR [rsp+8]
	mov ebx, 1
	test r12, r12
	je 23f
25:
	mov r14d, 0
26:
	movzx eax, BYTE PTR [r15+r14*1+1088]
	mov BYTE PTR [r15+r14*1+1184], al
	add r14, 1
	cmp r14, 96
	jne 26b
	mov eax, ebx
	bswap eax
	mov DWORD PTR [r15+1368], eax
	mov rdi, r15
	add rdi, 1184
	mov rsi, rbp
	add rsi, 64
	mov rdx, r15
	add rdx, 1368
	mov ecx, 4
	mov r8, r15
	call {vg_sha256_update_scratch_shani}
	mov rdi, r15
	add rdi, 1184
	mov rsi, r15
	add rsi, 992
	mov rdx, rbp
	add rdx, 68
	mov rcx, r15
	add rcx, 1280
	mov r8, r15
	call {vg_hmac_sha224_finalize_scratch_shani}
	mov r14d, 0
27:
	movzx eax, BYTE PTR [r15+r14*1+1280]
	mov BYTE PTR [r15+r14*1+1308], al
	add r14, 1
	cmp r14, 28
	jne 27b
	mov rdi, r15
	add rdi, 896
	mov rsi, r15
	add rsi, 1280
	mov rdx, QWORD PTR [r15+888]
	mov rcx, r15
	add rcx, 1308
	mov r8, r15
	call {vg_pbkdf2_hmac_sha224_iterate_shani}
	mov ecx, 28
	cmp r12, rcx
	jb 28f
	jmp 29f
28:
	mov rcx, r12
29:
	mov r14d, 0
210:
	movzx eax, BYTE PTR [r15+r14*1+1308]
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
	mov rbx, QWORD PTR [r15+832]
	mov rbp, QWORD PTR [r15+840]
	mov r12, QWORD PTR [r15+848]
	mov r13, QWORD PTR [r15+856]
	mov r14, QWORD PTR [r15+864]
	mov r15, QWORD PTR [r15+872]
	lea rsp, [rsp+1624]
	ret
	.p2align 6
