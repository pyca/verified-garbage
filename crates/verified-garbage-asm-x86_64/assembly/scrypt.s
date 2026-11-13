// The functions of `src/scrypt.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_scrypt_shani_sse2:
	push r9
	push r8
	push rsi
	push rdi
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+64]
	ror rax, 57
	mov r8, QWORD PTR [rsp+88]
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], r8
	mov r8d, 1
	call {vg_pbkdf2_hmac_sha256_scratch_shani}
	mov rax, QWORD PTR [rsp+48]
	mov QWORD PTR [rsp+16], rax
20:
	mov rdi, QWORD PTR [rsp+16]
	mov rsi, QWORD PTR [rsp+40]
	mov rdx, QWORD PTR [rsp+72]
	mov rcx, QWORD PTR [rsp+80]
	mov r8, QWORD PTR [rsp+88]
	mov r9, rsi
	add r9, 2
	call {vg_scrypt_romix_sse2}
	mov rcx, QWORD PTR [rsp+40]
	ror rcx, 57
	mov rax, QWORD PTR [rsp+16]
	add rax, rcx
	mov rdx, QWORD PTR [rsp+64]
	ror rdx, 57
	add rdx, QWORD PTR [rsp+48]
	mov QWORD PTR [rsp+16], rax
	cmp rax, rdx
	jne 20b
	mov rdi, QWORD PTR [rsp+24]
	mov rsi, QWORD PTR [rsp+32]
	mov rdx, QWORD PTR [rsp+48]
	mov rcx, QWORD PTR [rsp+64]
	ror rcx, 57
	mov r9, QWORD PTR [rsp+104]
	mov rax, QWORD PTR [rsp+112]
	mov r8, QWORD PTR [rsp+88]
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], r8
	mov r8d, 1
	call {vg_pbkdf2_hmac_sha256_scratch_shani}
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	pxor xmm12, xmm12
	pxor xmm13, xmm13
	pxor xmm14, xmm14
	pxor xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-88]
	mov QWORD PTR [rsp+80], r11
	movdqu XMMWORD PTR [rsp+64], xmm0
	movdqu XMMWORD PTR [rsp+48], xmm0
	movdqu XMMWORD PTR [rsp+32], xmm0
	movdqu XMMWORD PTR [rsp+16], xmm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+88]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	ret
	.p2align 6

vg_scrypt_avx2_sse2:
	push r9
	push r8
	push rsi
	push rdi
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+64]
	ror rax, 57
	mov r8, QWORD PTR [rsp+88]
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], r8
	mov r8d, 1
	call {vg_pbkdf2_hmac_sha256_scratch_avx2}
	mov rax, QWORD PTR [rsp+48]
	mov QWORD PTR [rsp+16], rax
20:
	mov rdi, QWORD PTR [rsp+16]
	mov rsi, QWORD PTR [rsp+40]
	mov rdx, QWORD PTR [rsp+72]
	mov rcx, QWORD PTR [rsp+80]
	mov r8, QWORD PTR [rsp+88]
	mov r9, rsi
	add r9, 2
	call {vg_scrypt_romix_sse2}
	mov rcx, QWORD PTR [rsp+40]
	ror rcx, 57
	mov rax, QWORD PTR [rsp+16]
	add rax, rcx
	mov rdx, QWORD PTR [rsp+64]
	ror rdx, 57
	add rdx, QWORD PTR [rsp+48]
	mov QWORD PTR [rsp+16], rax
	cmp rax, rdx
	jne 20b
	mov rdi, QWORD PTR [rsp+24]
	mov rsi, QWORD PTR [rsp+32]
	mov rdx, QWORD PTR [rsp+48]
	mov rcx, QWORD PTR [rsp+64]
	ror rcx, 57
	mov r9, QWORD PTR [rsp+104]
	mov rax, QWORD PTR [rsp+112]
	mov r8, QWORD PTR [rsp+88]
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], r8
	mov r8d, 1
	call {vg_pbkdf2_hmac_sha256_scratch_avx2}
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	vpxor xmm0, xmm0, xmm0
	vpxor xmm1, xmm1, xmm1
	vpxor xmm2, xmm2, xmm2
	vpxor xmm3, xmm3, xmm3
	vpxor xmm4, xmm4, xmm4
	vpxor xmm5, xmm5, xmm5
	vpxor xmm6, xmm6, xmm6
	vpxor xmm7, xmm7, xmm7
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	vpxor xmm11, xmm11, xmm11
	vpxor xmm12, xmm12, xmm12
	vpxor xmm13, xmm13, xmm13
	vpxor xmm14, xmm14, xmm14
	vpxor xmm15, xmm15, xmm15
	xor r11d, r11d
	mov r11d, 16
	test r11d, esp
	je 21f
	xor r11d, r11d
	lea rsp, [rsp-88]
	mov QWORD PTR [rsp+80], r11
	movdqu XMMWORD PTR [rsp+64], xmm0
	vmovdqu YMMWORD PTR [rsp+32], ymm0
	vmovdqu YMMWORD PTR [rsp], ymm0
	lea rsp, [rsp+88]
	jmp 22f
21:
	xor r11d, r11d
	lea rsp, [rsp-88]
	mov QWORD PTR [rsp+80], r11
	vmovdqu YMMWORD PTR [rsp+48], ymm0
	vmovdqu YMMWORD PTR [rsp+16], ymm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+88]
22:
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6

vg_scrypt_sse2:
	push r9
	push r8
	push rsi
	push rdi
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+64]
	ror rax, 57
	mov r8, QWORD PTR [rsp+88]
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], r8
	mov r8d, 1
	call {vg_pbkdf2_hmac_sha256_scratch}
	mov rax, QWORD PTR [rsp+48]
	mov QWORD PTR [rsp+16], rax
20:
	mov rdi, QWORD PTR [rsp+16]
	mov rsi, QWORD PTR [rsp+40]
	mov rdx, QWORD PTR [rsp+72]
	mov rcx, QWORD PTR [rsp+80]
	mov r8, QWORD PTR [rsp+88]
	mov r9, rsi
	add r9, 2
	call {vg_scrypt_romix_sse2}
	mov rcx, QWORD PTR [rsp+40]
	ror rcx, 57
	mov rax, QWORD PTR [rsp+16]
	add rax, rcx
	mov rdx, QWORD PTR [rsp+64]
	ror rdx, 57
	add rdx, QWORD PTR [rsp+48]
	mov QWORD PTR [rsp+16], rax
	cmp rax, rdx
	jne 20b
	mov rdi, QWORD PTR [rsp+24]
	mov rsi, QWORD PTR [rsp+32]
	mov rdx, QWORD PTR [rsp+48]
	mov rcx, QWORD PTR [rsp+64]
	ror rcx, 57
	mov r9, QWORD PTR [rsp+104]
	mov rax, QWORD PTR [rsp+112]
	mov r8, QWORD PTR [rsp+88]
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], r8
	mov r8d, 1
	call {vg_pbkdf2_hmac_sha256_scratch}
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	pxor xmm12, xmm12
	pxor xmm13, xmm13
	pxor xmm14, xmm14
	pxor xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-88]
	mov QWORD PTR [rsp+80], r11
	movdqu XMMWORD PTR [rsp+64], xmm0
	movdqu XMMWORD PTR [rsp+48], xmm0
	movdqu XMMWORD PTR [rsp+32], xmm0
	movdqu XMMWORD PTR [rsp+16], xmm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+88]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6

vg_scrypt_shani:
	push r9
	push r8
	push rsi
	push rdi
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+64]
	ror rax, 57
	mov r8, QWORD PTR [rsp+88]
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], r8
	mov r8d, 1
	call {vg_pbkdf2_hmac_sha256_scratch_shani}
	mov rax, QWORD PTR [rsp+48]
	mov QWORD PTR [rsp+16], rax
20:
	mov rdi, QWORD PTR [rsp+16]
	mov rsi, QWORD PTR [rsp+40]
	mov rdx, QWORD PTR [rsp+72]
	mov rcx, QWORD PTR [rsp+80]
	mov r8, QWORD PTR [rsp+88]
	mov r9, rsi
	add r9, 2
	call {vg_scrypt_romix}
	mov rcx, QWORD PTR [rsp+40]
	ror rcx, 57
	mov rax, QWORD PTR [rsp+16]
	add rax, rcx
	mov rdx, QWORD PTR [rsp+64]
	ror rdx, 57
	add rdx, QWORD PTR [rsp+48]
	mov QWORD PTR [rsp+16], rax
	cmp rax, rdx
	jne 20b
	mov rdi, QWORD PTR [rsp+24]
	mov rsi, QWORD PTR [rsp+32]
	mov rdx, QWORD PTR [rsp+48]
	mov rcx, QWORD PTR [rsp+64]
	ror rcx, 57
	mov r9, QWORD PTR [rsp+104]
	mov rax, QWORD PTR [rsp+112]
	mov r8, QWORD PTR [rsp+88]
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], r8
	mov r8d, 1
	call {vg_pbkdf2_hmac_sha256_scratch_shani}
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	pxor xmm12, xmm12
	pxor xmm13, xmm13
	pxor xmm14, xmm14
	pxor xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-88]
	mov QWORD PTR [rsp+80], r11
	movdqu XMMWORD PTR [rsp+64], xmm0
	movdqu XMMWORD PTR [rsp+48], xmm0
	movdqu XMMWORD PTR [rsp+32], xmm0
	movdqu XMMWORD PTR [rsp+16], xmm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+88]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6

vg_scrypt_avx2:
	push r9
	push r8
	push rsi
	push rdi
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+64]
	ror rax, 57
	mov r8, QWORD PTR [rsp+88]
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], r8
	mov r8d, 1
	call {vg_pbkdf2_hmac_sha256_scratch_avx2}
	mov rax, QWORD PTR [rsp+48]
	mov QWORD PTR [rsp+16], rax
20:
	mov rdi, QWORD PTR [rsp+16]
	mov rsi, QWORD PTR [rsp+40]
	mov rdx, QWORD PTR [rsp+72]
	mov rcx, QWORD PTR [rsp+80]
	mov r8, QWORD PTR [rsp+88]
	mov r9, rsi
	add r9, 2
	call {vg_scrypt_romix}
	mov rcx, QWORD PTR [rsp+40]
	ror rcx, 57
	mov rax, QWORD PTR [rsp+16]
	add rax, rcx
	mov rdx, QWORD PTR [rsp+64]
	ror rdx, 57
	add rdx, QWORD PTR [rsp+48]
	mov QWORD PTR [rsp+16], rax
	cmp rax, rdx
	jne 20b
	mov rdi, QWORD PTR [rsp+24]
	mov rsi, QWORD PTR [rsp+32]
	mov rdx, QWORD PTR [rsp+48]
	mov rcx, QWORD PTR [rsp+64]
	ror rcx, 57
	mov r9, QWORD PTR [rsp+104]
	mov rax, QWORD PTR [rsp+112]
	mov r8, QWORD PTR [rsp+88]
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], r8
	mov r8d, 1
	call {vg_pbkdf2_hmac_sha256_scratch_avx2}
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	vpxor xmm0, xmm0, xmm0
	vpxor xmm1, xmm1, xmm1
	vpxor xmm2, xmm2, xmm2
	vpxor xmm3, xmm3, xmm3
	vpxor xmm4, xmm4, xmm4
	vpxor xmm5, xmm5, xmm5
	vpxor xmm6, xmm6, xmm6
	vpxor xmm7, xmm7, xmm7
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	vpxor xmm11, xmm11, xmm11
	vpxor xmm12, xmm12, xmm12
	vpxor xmm13, xmm13, xmm13
	vpxor xmm14, xmm14, xmm14
	vpxor xmm15, xmm15, xmm15
	xor r11d, r11d
	mov r11d, 16
	test r11d, esp
	je 21f
	xor r11d, r11d
	lea rsp, [rsp-88]
	mov QWORD PTR [rsp+80], r11
	movdqu XMMWORD PTR [rsp+64], xmm0
	vmovdqu YMMWORD PTR [rsp+32], ymm0
	vmovdqu YMMWORD PTR [rsp], ymm0
	lea rsp, [rsp+88]
	jmp 22f
21:
	xor r11d, r11d
	lea rsp, [rsp-88]
	mov QWORD PTR [rsp+80], r11
	vmovdqu YMMWORD PTR [rsp+48], ymm0
	vmovdqu YMMWORD PTR [rsp+16], ymm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+88]
22:
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6

vg_scrypt:
	push r9
	push r8
	push rsi
	push rdi
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+64]
	ror rax, 57
	mov r8, QWORD PTR [rsp+88]
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], r8
	mov r8d, 1
	call {vg_pbkdf2_hmac_sha256_scratch}
	mov rax, QWORD PTR [rsp+48]
	mov QWORD PTR [rsp+16], rax
20:
	mov rdi, QWORD PTR [rsp+16]
	mov rsi, QWORD PTR [rsp+40]
	mov rdx, QWORD PTR [rsp+72]
	mov rcx, QWORD PTR [rsp+80]
	mov r8, QWORD PTR [rsp+88]
	mov r9, rsi
	add r9, 2
	call {vg_scrypt_romix}
	mov rcx, QWORD PTR [rsp+40]
	ror rcx, 57
	mov rax, QWORD PTR [rsp+16]
	add rax, rcx
	mov rdx, QWORD PTR [rsp+64]
	ror rdx, 57
	add rdx, QWORD PTR [rsp+48]
	mov QWORD PTR [rsp+16], rax
	cmp rax, rdx
	jne 20b
	mov rdi, QWORD PTR [rsp+24]
	mov rsi, QWORD PTR [rsp+32]
	mov rdx, QWORD PTR [rsp+48]
	mov rcx, QWORD PTR [rsp+64]
	ror rcx, 57
	mov r9, QWORD PTR [rsp+104]
	mov rax, QWORD PTR [rsp+112]
	mov r8, QWORD PTR [rsp+88]
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], r8
	mov r8d, 1
	call {vg_pbkdf2_hmac_sha256_scratch}
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	pxor xmm11, xmm11
	pxor xmm12, xmm12
	pxor xmm13, xmm13
	pxor xmm14, xmm14
	pxor xmm15, xmm15
	xor r11d, r11d
	lea rsp, [rsp-88]
	mov QWORD PTR [rsp+80], r11
	movdqu XMMWORD PTR [rsp+64], xmm0
	movdqu XMMWORD PTR [rsp+48], xmm0
	movdqu XMMWORD PTR [rsp+32], xmm0
	movdqu XMMWORD PTR [rsp+16], xmm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+88]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6
