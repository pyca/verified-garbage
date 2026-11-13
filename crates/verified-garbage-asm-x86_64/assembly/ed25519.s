// The functions of `src/ed25519.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed25519_verify_shani_ifma:
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rdi, QWORD PTR [rsp+128]
	call {vg_sha512_init_core}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+136]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+160]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+152]
	mov rcx, QWORD PTR [rsp+144]
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+128]
	mov rsi, QWORD PTR [rsp+144]
	add rsi, 64
	mov rdx, rsp
	add rdx, 64
	mov rcx, QWORD PTR [rsp+128]
	add rcx, 192
	call {vg_sha512_finalize_scratch_shani}
	mov rdi, rsp
	mov rsi, rsp
	add rsi, 64
	mov rdx, QWORD PTR [rsp+128]
	call {vg_ed25519_scalar_reduce}
	xor eax, eax
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], rax
	mov QWORD PTR [rsp+48], rax
	mov QWORD PTR [rsp+56], rax
	mov rdi, QWORD PTR [rsp+160]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, rsp
	mov rcx, QWORD PTR [rsp+128]
	call {vg_ed25519_verify_equation_ifma}
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	ret
	.p2align 6

vg_ed25519_sign_expanded_shani_ifma:
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push r9
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+232]
	mov rcx, QWORD PTR [rax]
	mov QWORD PTR [rsp+128], rcx
	mov rcx, QWORD PTR [rax+8]
	mov QWORD PTR [rsp+136], rcx
	mov rcx, QWORD PTR [rax+16]
	mov QWORD PTR [rsp+144], rcx
	mov rcx, QWORD PTR [rax+24]
	mov QWORD PTR [rsp+152], rcx
	mov rcx, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+160], rcx
	mov rcx, QWORD PTR [rax+40]
	mov QWORD PTR [rsp+168], rcx
	mov rcx, QWORD PTR [rax+48]
	mov QWORD PTR [rsp+176], rcx
	mov rcx, QWORD PTR [rax+56]
	mov QWORD PTR [rsp+184], rcx
	mov r8, QWORD PTR [rsp+128]
	mov r9, QWORD PTR [rsp+136]
	mov r10, QWORD PTR [rsp+144]
	mov r11, QWORD PTR [rsp+152]
	and r8, -8
	movabs rcx, 4611686018427387903
	and r11, rcx
	movabs rcx, 4611686018427387904
	or r11, rcx
	mov QWORD PTR [rsp], r8
	mov QWORD PTR [rsp+8], r9
	mov QWORD PTR [rsp+16], r10
	mov QWORD PTR [rsp+24], r11
	mov r8, QWORD PTR [rsp+160]
	mov r9, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+176]
	mov r11, QWORD PTR [rsp+184]
	mov QWORD PTR [rsp+32], r8
	mov QWORD PTR [rsp+40], r9
	mov QWORD PTR [rsp+48], r10
	mov QWORD PTR [rsp+56], r11
	mov rdi, QWORD PTR [rsp+200]
	call {vg_sha512_init_core}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 0
	mov rdx, rsp
	add rdx, 32
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+208]
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+200]
	mov rsi, QWORD PTR [rsp+208]
	add rsi, 32
	mov rdx, rsp
	add rdx, 128
	mov rcx, QWORD PTR [rsp+200]
	add rcx, 192
	call {vg_sha512_finalize_scratch_shani}
	mov rdi, rsp
	add rdi, 64
	mov rsi, rsp
	add rsi, 128
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_reduce}
	mov rdi, QWORD PTR [rsp+240]
	mov rsi, rsp
	add rsi, 64
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_base_ifma}
	mov rdi, QWORD PTR [rsp+200]
	call {vg_sha512_init_core}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+240]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+224]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+208]
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+200]
	mov rsi, QWORD PTR [rsp+208]
	add rsi, 64
	mov rdx, rsp
	add rdx, 128
	mov rcx, QWORD PTR [rsp+200]
	add rcx, 192
	call {vg_sha512_finalize_scratch_shani}
	mov rdi, rsp
	add rdi, 96
	mov rsi, rsp
	add rsi, 128
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_reduce}
	mov rdi, QWORD PTR [rsp+240]
	add rdi, 32
	mov rsi, rsp
	add rsi, 64
	mov rdx, rsp
	add rdx, 96
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_mul_add}
	xor eax, eax
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rax
	mov QWORD PTR [rsp+16], rax
	mov QWORD PTR [rsp+24], rax
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], rax
	mov QWORD PTR [rsp+48], rax
	mov QWORD PTR [rsp+56], rax
	mov QWORD PTR [rsp+64], rax
	mov QWORD PTR [rsp+72], rax
	mov QWORD PTR [rsp+80], rax
	mov QWORD PTR [rsp+88], rax
	mov QWORD PTR [rsp+96], rax
	mov QWORD PTR [rsp+104], rax
	mov QWORD PTR [rsp+112], rax
	mov QWORD PTR [rsp+120], rax
	mov QWORD PTR [rsp+128], rax
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rax
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
	mov QWORD PTR [rsp+168], rax
	mov QWORD PTR [rsp+176], rax
	mov QWORD PTR [rsp+184], rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
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
	vpxorq zmm16, zmm16, zmm16
	vpxorq zmm17, zmm17, zmm17
	vpxorq zmm18, zmm18, zmm18
	vpxorq zmm19, zmm19, zmm19
	vpxorq zmm20, zmm20, zmm20
	vpxorq zmm21, zmm21, zmm21
	vpxorq zmm22, zmm22, zmm22
	vpxorq zmm23, zmm23, zmm23
	vpxorq zmm24, zmm24, zmm24
	vpxorq zmm25, zmm25, zmm25
	vpxorq zmm26, zmm26, zmm26
	vpxorq zmm27, zmm27, zmm27
	vpxorq zmm28, zmm28, zmm28
	vpxorq zmm29, zmm29, zmm29
	vpxorq zmm30, zmm30, zmm30
	vpxorq zmm31, zmm31, zmm31
	xor r11d, r11d
	lea rsp, [rsp-16]
	stmxcsr DWORD PTR [rsp]
	mov r11d, DWORD PTR [rsp]
	and r11d, 65472
	mov DWORD PTR [rsp], r11d
	mov r11d, 8127
	mov DWORD PTR [rsp+4], r11d
	ldmxcsr DWORD PTR [rsp+4]
	lfence
	lfence
	ldmxcsr DWORD PTR [rsp]
	xor r11d, r11d
	lea rsp, [rsp+16]
	lea rsp, [rsp-264]
	vmovdqu YMMWORD PTR [rsp+232], ymm0
	vmovdqu YMMWORD PTR [rsp+200], ymm0
	vmovdqu YMMWORD PTR [rsp+168], ymm0
	vmovdqu YMMWORD PTR [rsp+136], ymm0
	vmovdqu YMMWORD PTR [rsp+104], ymm0
	vmovdqu YMMWORD PTR [rsp+72], ymm0
	vmovdqu YMMWORD PTR [rsp+40], ymm0
	vmovdqu YMMWORD PTR [rsp+8], ymm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+264]
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

vg_ed25519_key_pair_shani_ifma:
	push rdi
	push rsi
	push rcx
	mov rdi, rdx
	mov rdx, rsi
	mov esi, 32
	call {vg_sha512_digest_shani_core}
	mov rdi, QWORD PTR [rsp+16]
	mov rsi, QWORD PTR [rsp+8]
	mov rdx, QWORD PTR [rsp]
	call {vg_ed25519_public_key_expanded_ifma}
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
	vpxorq zmm16, zmm16, zmm16
	vpxorq zmm17, zmm17, zmm17
	vpxorq zmm18, zmm18, zmm18
	vpxorq zmm19, zmm19, zmm19
	vpxorq zmm20, zmm20, zmm20
	vpxorq zmm21, zmm21, zmm21
	vpxorq zmm22, zmm22, zmm22
	vpxorq zmm23, zmm23, zmm23
	vpxorq zmm24, zmm24, zmm24
	vpxorq zmm25, zmm25, zmm25
	vpxorq zmm26, zmm26, zmm26
	vpxorq zmm27, zmm27, zmm27
	vpxorq zmm28, zmm28, zmm28
	vpxorq zmm29, zmm29, zmm29
	vpxorq zmm30, zmm30, zmm30
	vpxorq zmm31, zmm31, zmm31
	xor r11d, r11d
	lea rsp, [rsp-16]
	stmxcsr DWORD PTR [rsp]
	mov r11d, DWORD PTR [rsp]
	and r11d, 65472
	mov DWORD PTR [rsp], r11d
	mov r11d, 8127
	mov DWORD PTR [rsp+4], r11d
	ldmxcsr DWORD PTR [rsp+4]
	lfence
	lfence
	ldmxcsr DWORD PTR [rsp]
	xor r11d, r11d
	lea rsp, [rsp+16]
	lea rsp, [rsp-1632]
	vmovdqu YMMWORD PTR [rsp+1600], ymm0
	vmovdqu YMMWORD PTR [rsp+1568], ymm0
	vmovdqu YMMWORD PTR [rsp+1536], ymm0
	vmovdqu YMMWORD PTR [rsp+1504], ymm0
	vmovdqu YMMWORD PTR [rsp+1472], ymm0
	vmovdqu YMMWORD PTR [rsp+1440], ymm0
	vmovdqu YMMWORD PTR [rsp+1408], ymm0
	vmovdqu YMMWORD PTR [rsp+1376], ymm0
	vmovdqu YMMWORD PTR [rsp+1344], ymm0
	vmovdqu YMMWORD PTR [rsp+1312], ymm0
	vmovdqu YMMWORD PTR [rsp+1280], ymm0
	vmovdqu YMMWORD PTR [rsp+1248], ymm0
	vmovdqu YMMWORD PTR [rsp+1216], ymm0
	vmovdqu YMMWORD PTR [rsp+1184], ymm0
	vmovdqu YMMWORD PTR [rsp+1152], ymm0
	vmovdqu YMMWORD PTR [rsp+1120], ymm0
	vmovdqu YMMWORD PTR [rsp+1088], ymm0
	vmovdqu YMMWORD PTR [rsp+1056], ymm0
	vmovdqu YMMWORD PTR [rsp+1024], ymm0
	vmovdqu YMMWORD PTR [rsp+992], ymm0
	vmovdqu YMMWORD PTR [rsp+960], ymm0
	vmovdqu YMMWORD PTR [rsp+928], ymm0
	vmovdqu YMMWORD PTR [rsp+896], ymm0
	vmovdqu YMMWORD PTR [rsp+864], ymm0
	vmovdqu YMMWORD PTR [rsp+832], ymm0
	vmovdqu YMMWORD PTR [rsp+800], ymm0
	vmovdqu YMMWORD PTR [rsp+768], ymm0
	vmovdqu YMMWORD PTR [rsp+736], ymm0
	vmovdqu YMMWORD PTR [rsp+704], ymm0
	vmovdqu YMMWORD PTR [rsp+672], ymm0
	vmovdqu YMMWORD PTR [rsp+640], ymm0
	vmovdqu YMMWORD PTR [rsp+608], ymm0
	vmovdqu YMMWORD PTR [rsp+576], ymm0
	vmovdqu YMMWORD PTR [rsp+544], ymm0
	vmovdqu YMMWORD PTR [rsp+512], ymm0
	vmovdqu YMMWORD PTR [rsp+480], ymm0
	vmovdqu YMMWORD PTR [rsp+448], ymm0
	vmovdqu YMMWORD PTR [rsp+416], ymm0
	vmovdqu YMMWORD PTR [rsp+384], ymm0
	vmovdqu YMMWORD PTR [rsp+352], ymm0
	vmovdqu YMMWORD PTR [rsp+320], ymm0
	vmovdqu YMMWORD PTR [rsp+288], ymm0
	vmovdqu YMMWORD PTR [rsp+256], ymm0
	vmovdqu YMMWORD PTR [rsp+224], ymm0
	vmovdqu YMMWORD PTR [rsp+192], ymm0
	vmovdqu YMMWORD PTR [rsp+160], ymm0
	vmovdqu YMMWORD PTR [rsp+128], ymm0
	vmovdqu YMMWORD PTR [rsp+96], ymm0
	vmovdqu YMMWORD PTR [rsp+64], ymm0
	vmovdqu YMMWORD PTR [rsp+32], ymm0
	vmovdqu YMMWORD PTR [rsp], ymm0
	lea rsp, [rsp+1632]
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

vg_ed25519_verify_shani_adx:
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rdi, QWORD PTR [rsp+128]
	call {vg_sha512_init_core}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+136]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+160]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+152]
	mov rcx, QWORD PTR [rsp+144]
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+128]
	mov rsi, QWORD PTR [rsp+144]
	add rsi, 64
	mov rdx, rsp
	add rdx, 64
	mov rcx, QWORD PTR [rsp+128]
	add rcx, 192
	call {vg_sha512_finalize_scratch_shani}
	mov rdi, rsp
	mov rsi, rsp
	add rsi, 64
	mov rdx, QWORD PTR [rsp+128]
	call {vg_ed25519_scalar_reduce}
	xor eax, eax
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], rax
	mov QWORD PTR [rsp+48], rax
	mov QWORD PTR [rsp+56], rax
	mov rdi, QWORD PTR [rsp+160]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, rsp
	mov rcx, QWORD PTR [rsp+128]
	call {vg_ed25519_verify_equation_adx}
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
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
	lea rsp, [rsp-184]
	vmovdqu YMMWORD PTR [rsp+152], ymm0
	vmovdqu YMMWORD PTR [rsp+120], ymm0
	vmovdqu YMMWORD PTR [rsp+88], ymm0
	vmovdqu YMMWORD PTR [rsp+56], ymm0
	vmovdqu YMMWORD PTR [rsp+24], ymm0
	movdqu XMMWORD PTR [rsp+8], xmm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+184]
	mov eax, eax
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

vg_ed25519_sign_expanded_shani_adx:
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push r9
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+232]
	mov rcx, QWORD PTR [rax]
	mov QWORD PTR [rsp+128], rcx
	mov rcx, QWORD PTR [rax+8]
	mov QWORD PTR [rsp+136], rcx
	mov rcx, QWORD PTR [rax+16]
	mov QWORD PTR [rsp+144], rcx
	mov rcx, QWORD PTR [rax+24]
	mov QWORD PTR [rsp+152], rcx
	mov rcx, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+160], rcx
	mov rcx, QWORD PTR [rax+40]
	mov QWORD PTR [rsp+168], rcx
	mov rcx, QWORD PTR [rax+48]
	mov QWORD PTR [rsp+176], rcx
	mov rcx, QWORD PTR [rax+56]
	mov QWORD PTR [rsp+184], rcx
	mov r8, QWORD PTR [rsp+128]
	mov r9, QWORD PTR [rsp+136]
	mov r10, QWORD PTR [rsp+144]
	mov r11, QWORD PTR [rsp+152]
	and r8, -8
	movabs rcx, 4611686018427387903
	and r11, rcx
	movabs rcx, 4611686018427387904
	or r11, rcx
	mov QWORD PTR [rsp], r8
	mov QWORD PTR [rsp+8], r9
	mov QWORD PTR [rsp+16], r10
	mov QWORD PTR [rsp+24], r11
	mov r8, QWORD PTR [rsp+160]
	mov r9, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+176]
	mov r11, QWORD PTR [rsp+184]
	mov QWORD PTR [rsp+32], r8
	mov QWORD PTR [rsp+40], r9
	mov QWORD PTR [rsp+48], r10
	mov QWORD PTR [rsp+56], r11
	mov rdi, QWORD PTR [rsp+200]
	call {vg_sha512_init_core}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 0
	mov rdx, rsp
	add rdx, 32
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+208]
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+200]
	mov rsi, QWORD PTR [rsp+208]
	add rsi, 32
	mov rdx, rsp
	add rdx, 128
	mov rcx, QWORD PTR [rsp+200]
	add rcx, 192
	call {vg_sha512_finalize_scratch_shani}
	mov rdi, rsp
	add rdi, 64
	mov rsi, rsp
	add rsi, 128
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_reduce}
	mov rdi, QWORD PTR [rsp+240]
	mov rsi, rsp
	add rsi, 64
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_base_adx}
	mov rdi, QWORD PTR [rsp+200]
	call {vg_sha512_init_core}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+240]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+224]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+208]
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+200]
	mov rsi, QWORD PTR [rsp+208]
	add rsi, 64
	mov rdx, rsp
	add rdx, 128
	mov rcx, QWORD PTR [rsp+200]
	add rcx, 192
	call {vg_sha512_finalize_scratch_shani}
	mov rdi, rsp
	add rdi, 96
	mov rsi, rsp
	add rsi, 128
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_reduce}
	mov rdi, QWORD PTR [rsp+240]
	add rdi, 32
	mov rsi, rsp
	add rsi, 64
	mov rdx, rsp
	add rdx, 96
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_mul_add}
	xor eax, eax
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rax
	mov QWORD PTR [rsp+16], rax
	mov QWORD PTR [rsp+24], rax
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], rax
	mov QWORD PTR [rsp+48], rax
	mov QWORD PTR [rsp+56], rax
	mov QWORD PTR [rsp+64], rax
	mov QWORD PTR [rsp+72], rax
	mov QWORD PTR [rsp+80], rax
	mov QWORD PTR [rsp+88], rax
	mov QWORD PTR [rsp+96], rax
	mov QWORD PTR [rsp+104], rax
	mov QWORD PTR [rsp+112], rax
	mov QWORD PTR [rsp+120], rax
	mov QWORD PTR [rsp+128], rax
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rax
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
	mov QWORD PTR [rsp+168], rax
	mov QWORD PTR [rsp+176], rax
	mov QWORD PTR [rsp+184], rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
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
	lea rsp, [rsp-264]
	vmovdqu YMMWORD PTR [rsp+232], ymm0
	vmovdqu YMMWORD PTR [rsp+200], ymm0
	vmovdqu YMMWORD PTR [rsp+168], ymm0
	vmovdqu YMMWORD PTR [rsp+136], ymm0
	vmovdqu YMMWORD PTR [rsp+104], ymm0
	vmovdqu YMMWORD PTR [rsp+72], ymm0
	vmovdqu YMMWORD PTR [rsp+40], ymm0
	vmovdqu YMMWORD PTR [rsp+8], ymm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+264]
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

vg_ed25519_key_pair_shani_adx:
	push rdi
	push rsi
	push rcx
	mov rdi, rdx
	mov rdx, rsi
	mov esi, 32
	call {vg_sha512_digest_shani_core}
	mov rdi, QWORD PTR [rsp+16]
	mov rsi, QWORD PTR [rsp+8]
	mov rdx, QWORD PTR [rsp]
	call {vg_ed25519_public_key_expanded_adx}
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
	lea rsp, [rsp-1632]
	vmovdqu YMMWORD PTR [rsp+1600], ymm0
	vmovdqu YMMWORD PTR [rsp+1568], ymm0
	vmovdqu YMMWORD PTR [rsp+1536], ymm0
	vmovdqu YMMWORD PTR [rsp+1504], ymm0
	vmovdqu YMMWORD PTR [rsp+1472], ymm0
	vmovdqu YMMWORD PTR [rsp+1440], ymm0
	vmovdqu YMMWORD PTR [rsp+1408], ymm0
	vmovdqu YMMWORD PTR [rsp+1376], ymm0
	vmovdqu YMMWORD PTR [rsp+1344], ymm0
	vmovdqu YMMWORD PTR [rsp+1312], ymm0
	vmovdqu YMMWORD PTR [rsp+1280], ymm0
	vmovdqu YMMWORD PTR [rsp+1248], ymm0
	vmovdqu YMMWORD PTR [rsp+1216], ymm0
	vmovdqu YMMWORD PTR [rsp+1184], ymm0
	vmovdqu YMMWORD PTR [rsp+1152], ymm0
	vmovdqu YMMWORD PTR [rsp+1120], ymm0
	vmovdqu YMMWORD PTR [rsp+1088], ymm0
	vmovdqu YMMWORD PTR [rsp+1056], ymm0
	vmovdqu YMMWORD PTR [rsp+1024], ymm0
	vmovdqu YMMWORD PTR [rsp+992], ymm0
	vmovdqu YMMWORD PTR [rsp+960], ymm0
	vmovdqu YMMWORD PTR [rsp+928], ymm0
	vmovdqu YMMWORD PTR [rsp+896], ymm0
	vmovdqu YMMWORD PTR [rsp+864], ymm0
	vmovdqu YMMWORD PTR [rsp+832], ymm0
	vmovdqu YMMWORD PTR [rsp+800], ymm0
	vmovdqu YMMWORD PTR [rsp+768], ymm0
	vmovdqu YMMWORD PTR [rsp+736], ymm0
	vmovdqu YMMWORD PTR [rsp+704], ymm0
	vmovdqu YMMWORD PTR [rsp+672], ymm0
	vmovdqu YMMWORD PTR [rsp+640], ymm0
	vmovdqu YMMWORD PTR [rsp+608], ymm0
	vmovdqu YMMWORD PTR [rsp+576], ymm0
	vmovdqu YMMWORD PTR [rsp+544], ymm0
	vmovdqu YMMWORD PTR [rsp+512], ymm0
	vmovdqu YMMWORD PTR [rsp+480], ymm0
	vmovdqu YMMWORD PTR [rsp+448], ymm0
	vmovdqu YMMWORD PTR [rsp+416], ymm0
	vmovdqu YMMWORD PTR [rsp+384], ymm0
	vmovdqu YMMWORD PTR [rsp+352], ymm0
	vmovdqu YMMWORD PTR [rsp+320], ymm0
	vmovdqu YMMWORD PTR [rsp+288], ymm0
	vmovdqu YMMWORD PTR [rsp+256], ymm0
	vmovdqu YMMWORD PTR [rsp+224], ymm0
	vmovdqu YMMWORD PTR [rsp+192], ymm0
	vmovdqu YMMWORD PTR [rsp+160], ymm0
	vmovdqu YMMWORD PTR [rsp+128], ymm0
	vmovdqu YMMWORD PTR [rsp+96], ymm0
	vmovdqu YMMWORD PTR [rsp+64], ymm0
	vmovdqu YMMWORD PTR [rsp+32], ymm0
	vmovdqu YMMWORD PTR [rsp], ymm0
	lea rsp, [rsp+1632]
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

vg_ed25519_verify_shani:
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rdi, QWORD PTR [rsp+128]
	call {vg_sha512_init_core}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+136]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+160]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+152]
	mov rcx, QWORD PTR [rsp+144]
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+128]
	mov rsi, QWORD PTR [rsp+144]
	add rsi, 64
	mov rdx, rsp
	add rdx, 64
	mov rcx, QWORD PTR [rsp+128]
	add rcx, 192
	call {vg_sha512_finalize_scratch_shani}
	mov rdi, rsp
	mov rsi, rsp
	add rsi, 64
	mov rdx, QWORD PTR [rsp+128]
	call {vg_ed25519_scalar_reduce}
	xor eax, eax
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], rax
	mov QWORD PTR [rsp+48], rax
	mov QWORD PTR [rsp+56], rax
	mov rdi, QWORD PTR [rsp+160]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, rsp
	mov rcx, QWORD PTR [rsp+128]
	call {vg_ed25519_verify_equation}
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
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
	lea rsp, [rsp-184]
	vmovdqu YMMWORD PTR [rsp+152], ymm0
	vmovdqu YMMWORD PTR [rsp+120], ymm0
	vmovdqu YMMWORD PTR [rsp+88], ymm0
	vmovdqu YMMWORD PTR [rsp+56], ymm0
	vmovdqu YMMWORD PTR [rsp+24], ymm0
	movdqu XMMWORD PTR [rsp+8], xmm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+184]
	mov eax, eax
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

vg_ed25519_sign_expanded_shani:
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push r9
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+232]
	mov rcx, QWORD PTR [rax]
	mov QWORD PTR [rsp+128], rcx
	mov rcx, QWORD PTR [rax+8]
	mov QWORD PTR [rsp+136], rcx
	mov rcx, QWORD PTR [rax+16]
	mov QWORD PTR [rsp+144], rcx
	mov rcx, QWORD PTR [rax+24]
	mov QWORD PTR [rsp+152], rcx
	mov rcx, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+160], rcx
	mov rcx, QWORD PTR [rax+40]
	mov QWORD PTR [rsp+168], rcx
	mov rcx, QWORD PTR [rax+48]
	mov QWORD PTR [rsp+176], rcx
	mov rcx, QWORD PTR [rax+56]
	mov QWORD PTR [rsp+184], rcx
	mov r8, QWORD PTR [rsp+128]
	mov r9, QWORD PTR [rsp+136]
	mov r10, QWORD PTR [rsp+144]
	mov r11, QWORD PTR [rsp+152]
	and r8, -8
	movabs rcx, 4611686018427387903
	and r11, rcx
	movabs rcx, 4611686018427387904
	or r11, rcx
	mov QWORD PTR [rsp], r8
	mov QWORD PTR [rsp+8], r9
	mov QWORD PTR [rsp+16], r10
	mov QWORD PTR [rsp+24], r11
	mov r8, QWORD PTR [rsp+160]
	mov r9, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+176]
	mov r11, QWORD PTR [rsp+184]
	mov QWORD PTR [rsp+32], r8
	mov QWORD PTR [rsp+40], r9
	mov QWORD PTR [rsp+48], r10
	mov QWORD PTR [rsp+56], r11
	mov rdi, QWORD PTR [rsp+200]
	call {vg_sha512_init_core}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 0
	mov rdx, rsp
	add rdx, 32
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+208]
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+200]
	mov rsi, QWORD PTR [rsp+208]
	add rsi, 32
	mov rdx, rsp
	add rdx, 128
	mov rcx, QWORD PTR [rsp+200]
	add rcx, 192
	call {vg_sha512_finalize_scratch_shani}
	mov rdi, rsp
	add rdi, 64
	mov rsi, rsp
	add rsi, 128
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_reduce}
	mov rdi, QWORD PTR [rsp+240]
	mov rsi, rsp
	add rsi, 64
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_base}
	mov rdi, QWORD PTR [rsp+200]
	call {vg_sha512_init_core}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+240]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+224]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+208]
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+200]
	mov rsi, QWORD PTR [rsp+208]
	add rsi, 64
	mov rdx, rsp
	add rdx, 128
	mov rcx, QWORD PTR [rsp+200]
	add rcx, 192
	call {vg_sha512_finalize_scratch_shani}
	mov rdi, rsp
	add rdi, 96
	mov rsi, rsp
	add rsi, 128
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_reduce}
	mov rdi, QWORD PTR [rsp+240]
	add rdi, 32
	mov rsi, rsp
	add rsi, 64
	mov rdx, rsp
	add rdx, 96
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_mul_add}
	xor eax, eax
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rax
	mov QWORD PTR [rsp+16], rax
	mov QWORD PTR [rsp+24], rax
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], rax
	mov QWORD PTR [rsp+48], rax
	mov QWORD PTR [rsp+56], rax
	mov QWORD PTR [rsp+64], rax
	mov QWORD PTR [rsp+72], rax
	mov QWORD PTR [rsp+80], rax
	mov QWORD PTR [rsp+88], rax
	mov QWORD PTR [rsp+96], rax
	mov QWORD PTR [rsp+104], rax
	mov QWORD PTR [rsp+112], rax
	mov QWORD PTR [rsp+120], rax
	mov QWORD PTR [rsp+128], rax
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rax
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
	mov QWORD PTR [rsp+168], rax
	mov QWORD PTR [rsp+176], rax
	mov QWORD PTR [rsp+184], rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
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
	lea rsp, [rsp-264]
	vmovdqu YMMWORD PTR [rsp+232], ymm0
	vmovdqu YMMWORD PTR [rsp+200], ymm0
	vmovdqu YMMWORD PTR [rsp+168], ymm0
	vmovdqu YMMWORD PTR [rsp+136], ymm0
	vmovdqu YMMWORD PTR [rsp+104], ymm0
	vmovdqu YMMWORD PTR [rsp+72], ymm0
	vmovdqu YMMWORD PTR [rsp+40], ymm0
	vmovdqu YMMWORD PTR [rsp+8], ymm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+264]
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

vg_ed25519_key_pair_shani:
	push rdi
	push rsi
	push rcx
	mov rdi, rdx
	mov rdx, rsi
	mov esi, 32
	call {vg_sha512_digest_shani_core}
	mov rdi, QWORD PTR [rsp+16]
	mov rsi, QWORD PTR [rsp+8]
	mov rdx, QWORD PTR [rsp]
	call {vg_ed25519_public_key_expanded}
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
	lea rsp, [rsp-1632]
	vmovdqu YMMWORD PTR [rsp+1600], ymm0
	vmovdqu YMMWORD PTR [rsp+1568], ymm0
	vmovdqu YMMWORD PTR [rsp+1536], ymm0
	vmovdqu YMMWORD PTR [rsp+1504], ymm0
	vmovdqu YMMWORD PTR [rsp+1472], ymm0
	vmovdqu YMMWORD PTR [rsp+1440], ymm0
	vmovdqu YMMWORD PTR [rsp+1408], ymm0
	vmovdqu YMMWORD PTR [rsp+1376], ymm0
	vmovdqu YMMWORD PTR [rsp+1344], ymm0
	vmovdqu YMMWORD PTR [rsp+1312], ymm0
	vmovdqu YMMWORD PTR [rsp+1280], ymm0
	vmovdqu YMMWORD PTR [rsp+1248], ymm0
	vmovdqu YMMWORD PTR [rsp+1216], ymm0
	vmovdqu YMMWORD PTR [rsp+1184], ymm0
	vmovdqu YMMWORD PTR [rsp+1152], ymm0
	vmovdqu YMMWORD PTR [rsp+1120], ymm0
	vmovdqu YMMWORD PTR [rsp+1088], ymm0
	vmovdqu YMMWORD PTR [rsp+1056], ymm0
	vmovdqu YMMWORD PTR [rsp+1024], ymm0
	vmovdqu YMMWORD PTR [rsp+992], ymm0
	vmovdqu YMMWORD PTR [rsp+960], ymm0
	vmovdqu YMMWORD PTR [rsp+928], ymm0
	vmovdqu YMMWORD PTR [rsp+896], ymm0
	vmovdqu YMMWORD PTR [rsp+864], ymm0
	vmovdqu YMMWORD PTR [rsp+832], ymm0
	vmovdqu YMMWORD PTR [rsp+800], ymm0
	vmovdqu YMMWORD PTR [rsp+768], ymm0
	vmovdqu YMMWORD PTR [rsp+736], ymm0
	vmovdqu YMMWORD PTR [rsp+704], ymm0
	vmovdqu YMMWORD PTR [rsp+672], ymm0
	vmovdqu YMMWORD PTR [rsp+640], ymm0
	vmovdqu YMMWORD PTR [rsp+608], ymm0
	vmovdqu YMMWORD PTR [rsp+576], ymm0
	vmovdqu YMMWORD PTR [rsp+544], ymm0
	vmovdqu YMMWORD PTR [rsp+512], ymm0
	vmovdqu YMMWORD PTR [rsp+480], ymm0
	vmovdqu YMMWORD PTR [rsp+448], ymm0
	vmovdqu YMMWORD PTR [rsp+416], ymm0
	vmovdqu YMMWORD PTR [rsp+384], ymm0
	vmovdqu YMMWORD PTR [rsp+352], ymm0
	vmovdqu YMMWORD PTR [rsp+320], ymm0
	vmovdqu YMMWORD PTR [rsp+288], ymm0
	vmovdqu YMMWORD PTR [rsp+256], ymm0
	vmovdqu YMMWORD PTR [rsp+224], ymm0
	vmovdqu YMMWORD PTR [rsp+192], ymm0
	vmovdqu YMMWORD PTR [rsp+160], ymm0
	vmovdqu YMMWORD PTR [rsp+128], ymm0
	vmovdqu YMMWORD PTR [rsp+96], ymm0
	vmovdqu YMMWORD PTR [rsp+64], ymm0
	vmovdqu YMMWORD PTR [rsp+32], ymm0
	vmovdqu YMMWORD PTR [rsp], ymm0
	lea rsp, [rsp+1632]
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

vg_ed25519_verify_avx2_ifma:
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rdi, QWORD PTR [rsp+128]
	call {vg_sha512_init_core}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+136]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+160]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+152]
	mov rcx, QWORD PTR [rsp+144]
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+128]
	mov rsi, QWORD PTR [rsp+144]
	add rsi, 64
	mov rdx, rsp
	add rdx, 64
	mov rcx, QWORD PTR [rsp+128]
	add rcx, 192
	call {vg_sha512_finalize_scratch_avx2}
	mov rdi, rsp
	mov rsi, rsp
	add rsi, 64
	mov rdx, QWORD PTR [rsp+128]
	call {vg_ed25519_scalar_reduce}
	xor eax, eax
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], rax
	mov QWORD PTR [rsp+48], rax
	mov QWORD PTR [rsp+56], rax
	mov rdi, QWORD PTR [rsp+160]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, rsp
	mov rcx, QWORD PTR [rsp+128]
	call {vg_ed25519_verify_equation_ifma}
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	ret
	.p2align 6

vg_ed25519_sign_expanded_avx2_ifma:
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push r9
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+232]
	mov rcx, QWORD PTR [rax]
	mov QWORD PTR [rsp+128], rcx
	mov rcx, QWORD PTR [rax+8]
	mov QWORD PTR [rsp+136], rcx
	mov rcx, QWORD PTR [rax+16]
	mov QWORD PTR [rsp+144], rcx
	mov rcx, QWORD PTR [rax+24]
	mov QWORD PTR [rsp+152], rcx
	mov rcx, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+160], rcx
	mov rcx, QWORD PTR [rax+40]
	mov QWORD PTR [rsp+168], rcx
	mov rcx, QWORD PTR [rax+48]
	mov QWORD PTR [rsp+176], rcx
	mov rcx, QWORD PTR [rax+56]
	mov QWORD PTR [rsp+184], rcx
	mov r8, QWORD PTR [rsp+128]
	mov r9, QWORD PTR [rsp+136]
	mov r10, QWORD PTR [rsp+144]
	mov r11, QWORD PTR [rsp+152]
	and r8, -8
	movabs rcx, 4611686018427387903
	and r11, rcx
	movabs rcx, 4611686018427387904
	or r11, rcx
	mov QWORD PTR [rsp], r8
	mov QWORD PTR [rsp+8], r9
	mov QWORD PTR [rsp+16], r10
	mov QWORD PTR [rsp+24], r11
	mov r8, QWORD PTR [rsp+160]
	mov r9, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+176]
	mov r11, QWORD PTR [rsp+184]
	mov QWORD PTR [rsp+32], r8
	mov QWORD PTR [rsp+40], r9
	mov QWORD PTR [rsp+48], r10
	mov QWORD PTR [rsp+56], r11
	mov rdi, QWORD PTR [rsp+200]
	call {vg_sha512_init_core}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 0
	mov rdx, rsp
	add rdx, 32
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+208]
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+200]
	mov rsi, QWORD PTR [rsp+208]
	add rsi, 32
	mov rdx, rsp
	add rdx, 128
	mov rcx, QWORD PTR [rsp+200]
	add rcx, 192
	call {vg_sha512_finalize_scratch_avx2}
	mov rdi, rsp
	add rdi, 64
	mov rsi, rsp
	add rsi, 128
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_reduce}
	mov rdi, QWORD PTR [rsp+240]
	mov rsi, rsp
	add rsi, 64
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_base_ifma}
	mov rdi, QWORD PTR [rsp+200]
	call {vg_sha512_init_core}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+240]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+224]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+208]
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+200]
	mov rsi, QWORD PTR [rsp+208]
	add rsi, 64
	mov rdx, rsp
	add rdx, 128
	mov rcx, QWORD PTR [rsp+200]
	add rcx, 192
	call {vg_sha512_finalize_scratch_avx2}
	mov rdi, rsp
	add rdi, 96
	mov rsi, rsp
	add rsi, 128
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_reduce}
	mov rdi, QWORD PTR [rsp+240]
	add rdi, 32
	mov rsi, rsp
	add rsi, 64
	mov rdx, rsp
	add rdx, 96
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_mul_add}
	xor eax, eax
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rax
	mov QWORD PTR [rsp+16], rax
	mov QWORD PTR [rsp+24], rax
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], rax
	mov QWORD PTR [rsp+48], rax
	mov QWORD PTR [rsp+56], rax
	mov QWORD PTR [rsp+64], rax
	mov QWORD PTR [rsp+72], rax
	mov QWORD PTR [rsp+80], rax
	mov QWORD PTR [rsp+88], rax
	mov QWORD PTR [rsp+96], rax
	mov QWORD PTR [rsp+104], rax
	mov QWORD PTR [rsp+112], rax
	mov QWORD PTR [rsp+120], rax
	mov QWORD PTR [rsp+128], rax
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rax
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
	mov QWORD PTR [rsp+168], rax
	mov QWORD PTR [rsp+176], rax
	mov QWORD PTR [rsp+184], rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
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
	vpxorq zmm16, zmm16, zmm16
	vpxorq zmm17, zmm17, zmm17
	vpxorq zmm18, zmm18, zmm18
	vpxorq zmm19, zmm19, zmm19
	vpxorq zmm20, zmm20, zmm20
	vpxorq zmm21, zmm21, zmm21
	vpxorq zmm22, zmm22, zmm22
	vpxorq zmm23, zmm23, zmm23
	vpxorq zmm24, zmm24, zmm24
	vpxorq zmm25, zmm25, zmm25
	vpxorq zmm26, zmm26, zmm26
	vpxorq zmm27, zmm27, zmm27
	vpxorq zmm28, zmm28, zmm28
	vpxorq zmm29, zmm29, zmm29
	vpxorq zmm30, zmm30, zmm30
	vpxorq zmm31, zmm31, zmm31
	xor r11d, r11d
	lea rsp, [rsp-16]
	stmxcsr DWORD PTR [rsp]
	mov r11d, DWORD PTR [rsp]
	and r11d, 65472
	mov DWORD PTR [rsp], r11d
	mov r11d, 8127
	mov DWORD PTR [rsp+4], r11d
	ldmxcsr DWORD PTR [rsp+4]
	lfence
	lfence
	ldmxcsr DWORD PTR [rsp]
	xor r11d, r11d
	lea rsp, [rsp+16]
	lea rsp, [rsp-264]
	vmovdqu YMMWORD PTR [rsp+232], ymm0
	vmovdqu YMMWORD PTR [rsp+200], ymm0
	vmovdqu YMMWORD PTR [rsp+168], ymm0
	vmovdqu YMMWORD PTR [rsp+136], ymm0
	vmovdqu YMMWORD PTR [rsp+104], ymm0
	vmovdqu YMMWORD PTR [rsp+72], ymm0
	vmovdqu YMMWORD PTR [rsp+40], ymm0
	vmovdqu YMMWORD PTR [rsp+8], ymm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+264]
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

vg_ed25519_key_pair_avx2_ifma:
	push rdi
	push rsi
	push rcx
	mov rdi, rdx
	mov rdx, rsi
	mov esi, 32
	call {vg_sha512_digest_avx2_core}
	mov rdi, QWORD PTR [rsp+16]
	mov rsi, QWORD PTR [rsp+8]
	mov rdx, QWORD PTR [rsp]
	call {vg_ed25519_public_key_expanded_ifma}
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
	vpxorq zmm16, zmm16, zmm16
	vpxorq zmm17, zmm17, zmm17
	vpxorq zmm18, zmm18, zmm18
	vpxorq zmm19, zmm19, zmm19
	vpxorq zmm20, zmm20, zmm20
	vpxorq zmm21, zmm21, zmm21
	vpxorq zmm22, zmm22, zmm22
	vpxorq zmm23, zmm23, zmm23
	vpxorq zmm24, zmm24, zmm24
	vpxorq zmm25, zmm25, zmm25
	vpxorq zmm26, zmm26, zmm26
	vpxorq zmm27, zmm27, zmm27
	vpxorq zmm28, zmm28, zmm28
	vpxorq zmm29, zmm29, zmm29
	vpxorq zmm30, zmm30, zmm30
	vpxorq zmm31, zmm31, zmm31
	xor r11d, r11d
	lea rsp, [rsp-16]
	stmxcsr DWORD PTR [rsp]
	mov r11d, DWORD PTR [rsp]
	and r11d, 65472
	mov DWORD PTR [rsp], r11d
	mov r11d, 8127
	mov DWORD PTR [rsp+4], r11d
	ldmxcsr DWORD PTR [rsp+4]
	lfence
	lfence
	ldmxcsr DWORD PTR [rsp]
	xor r11d, r11d
	lea rsp, [rsp+16]
	lea rsp, [rsp-1632]
	vmovdqu YMMWORD PTR [rsp+1600], ymm0
	vmovdqu YMMWORD PTR [rsp+1568], ymm0
	vmovdqu YMMWORD PTR [rsp+1536], ymm0
	vmovdqu YMMWORD PTR [rsp+1504], ymm0
	vmovdqu YMMWORD PTR [rsp+1472], ymm0
	vmovdqu YMMWORD PTR [rsp+1440], ymm0
	vmovdqu YMMWORD PTR [rsp+1408], ymm0
	vmovdqu YMMWORD PTR [rsp+1376], ymm0
	vmovdqu YMMWORD PTR [rsp+1344], ymm0
	vmovdqu YMMWORD PTR [rsp+1312], ymm0
	vmovdqu YMMWORD PTR [rsp+1280], ymm0
	vmovdqu YMMWORD PTR [rsp+1248], ymm0
	vmovdqu YMMWORD PTR [rsp+1216], ymm0
	vmovdqu YMMWORD PTR [rsp+1184], ymm0
	vmovdqu YMMWORD PTR [rsp+1152], ymm0
	vmovdqu YMMWORD PTR [rsp+1120], ymm0
	vmovdqu YMMWORD PTR [rsp+1088], ymm0
	vmovdqu YMMWORD PTR [rsp+1056], ymm0
	vmovdqu YMMWORD PTR [rsp+1024], ymm0
	vmovdqu YMMWORD PTR [rsp+992], ymm0
	vmovdqu YMMWORD PTR [rsp+960], ymm0
	vmovdqu YMMWORD PTR [rsp+928], ymm0
	vmovdqu YMMWORD PTR [rsp+896], ymm0
	vmovdqu YMMWORD PTR [rsp+864], ymm0
	vmovdqu YMMWORD PTR [rsp+832], ymm0
	vmovdqu YMMWORD PTR [rsp+800], ymm0
	vmovdqu YMMWORD PTR [rsp+768], ymm0
	vmovdqu YMMWORD PTR [rsp+736], ymm0
	vmovdqu YMMWORD PTR [rsp+704], ymm0
	vmovdqu YMMWORD PTR [rsp+672], ymm0
	vmovdqu YMMWORD PTR [rsp+640], ymm0
	vmovdqu YMMWORD PTR [rsp+608], ymm0
	vmovdqu YMMWORD PTR [rsp+576], ymm0
	vmovdqu YMMWORD PTR [rsp+544], ymm0
	vmovdqu YMMWORD PTR [rsp+512], ymm0
	vmovdqu YMMWORD PTR [rsp+480], ymm0
	vmovdqu YMMWORD PTR [rsp+448], ymm0
	vmovdqu YMMWORD PTR [rsp+416], ymm0
	vmovdqu YMMWORD PTR [rsp+384], ymm0
	vmovdqu YMMWORD PTR [rsp+352], ymm0
	vmovdqu YMMWORD PTR [rsp+320], ymm0
	vmovdqu YMMWORD PTR [rsp+288], ymm0
	vmovdqu YMMWORD PTR [rsp+256], ymm0
	vmovdqu YMMWORD PTR [rsp+224], ymm0
	vmovdqu YMMWORD PTR [rsp+192], ymm0
	vmovdqu YMMWORD PTR [rsp+160], ymm0
	vmovdqu YMMWORD PTR [rsp+128], ymm0
	vmovdqu YMMWORD PTR [rsp+96], ymm0
	vmovdqu YMMWORD PTR [rsp+64], ymm0
	vmovdqu YMMWORD PTR [rsp+32], ymm0
	vmovdqu YMMWORD PTR [rsp], ymm0
	lea rsp, [rsp+1632]
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

vg_ed25519_verify_avx2_adx:
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rdi, QWORD PTR [rsp+128]
	call {vg_sha512_init_core}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+136]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+160]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+152]
	mov rcx, QWORD PTR [rsp+144]
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+128]
	mov rsi, QWORD PTR [rsp+144]
	add rsi, 64
	mov rdx, rsp
	add rdx, 64
	mov rcx, QWORD PTR [rsp+128]
	add rcx, 192
	call {vg_sha512_finalize_scratch_avx2}
	mov rdi, rsp
	mov rsi, rsp
	add rsi, 64
	mov rdx, QWORD PTR [rsp+128]
	call {vg_ed25519_scalar_reduce}
	xor eax, eax
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], rax
	mov QWORD PTR [rsp+48], rax
	mov QWORD PTR [rsp+56], rax
	mov rdi, QWORD PTR [rsp+160]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, rsp
	mov rcx, QWORD PTR [rsp+128]
	call {vg_ed25519_verify_equation_adx}
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
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
	lea rsp, [rsp-184]
	vmovdqu YMMWORD PTR [rsp+152], ymm0
	vmovdqu YMMWORD PTR [rsp+120], ymm0
	vmovdqu YMMWORD PTR [rsp+88], ymm0
	vmovdqu YMMWORD PTR [rsp+56], ymm0
	vmovdqu YMMWORD PTR [rsp+24], ymm0
	movdqu XMMWORD PTR [rsp+8], xmm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+184]
	mov eax, eax
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

vg_ed25519_sign_expanded_avx2_adx:
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push r9
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+232]
	mov rcx, QWORD PTR [rax]
	mov QWORD PTR [rsp+128], rcx
	mov rcx, QWORD PTR [rax+8]
	mov QWORD PTR [rsp+136], rcx
	mov rcx, QWORD PTR [rax+16]
	mov QWORD PTR [rsp+144], rcx
	mov rcx, QWORD PTR [rax+24]
	mov QWORD PTR [rsp+152], rcx
	mov rcx, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+160], rcx
	mov rcx, QWORD PTR [rax+40]
	mov QWORD PTR [rsp+168], rcx
	mov rcx, QWORD PTR [rax+48]
	mov QWORD PTR [rsp+176], rcx
	mov rcx, QWORD PTR [rax+56]
	mov QWORD PTR [rsp+184], rcx
	mov r8, QWORD PTR [rsp+128]
	mov r9, QWORD PTR [rsp+136]
	mov r10, QWORD PTR [rsp+144]
	mov r11, QWORD PTR [rsp+152]
	and r8, -8
	movabs rcx, 4611686018427387903
	and r11, rcx
	movabs rcx, 4611686018427387904
	or r11, rcx
	mov QWORD PTR [rsp], r8
	mov QWORD PTR [rsp+8], r9
	mov QWORD PTR [rsp+16], r10
	mov QWORD PTR [rsp+24], r11
	mov r8, QWORD PTR [rsp+160]
	mov r9, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+176]
	mov r11, QWORD PTR [rsp+184]
	mov QWORD PTR [rsp+32], r8
	mov QWORD PTR [rsp+40], r9
	mov QWORD PTR [rsp+48], r10
	mov QWORD PTR [rsp+56], r11
	mov rdi, QWORD PTR [rsp+200]
	call {vg_sha512_init_core}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 0
	mov rdx, rsp
	add rdx, 32
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+208]
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+200]
	mov rsi, QWORD PTR [rsp+208]
	add rsi, 32
	mov rdx, rsp
	add rdx, 128
	mov rcx, QWORD PTR [rsp+200]
	add rcx, 192
	call {vg_sha512_finalize_scratch_avx2}
	mov rdi, rsp
	add rdi, 64
	mov rsi, rsp
	add rsi, 128
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_reduce}
	mov rdi, QWORD PTR [rsp+240]
	mov rsi, rsp
	add rsi, 64
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_base_adx}
	mov rdi, QWORD PTR [rsp+200]
	call {vg_sha512_init_core}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+240]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+224]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+208]
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+200]
	mov rsi, QWORD PTR [rsp+208]
	add rsi, 64
	mov rdx, rsp
	add rdx, 128
	mov rcx, QWORD PTR [rsp+200]
	add rcx, 192
	call {vg_sha512_finalize_scratch_avx2}
	mov rdi, rsp
	add rdi, 96
	mov rsi, rsp
	add rsi, 128
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_reduce}
	mov rdi, QWORD PTR [rsp+240]
	add rdi, 32
	mov rsi, rsp
	add rsi, 64
	mov rdx, rsp
	add rdx, 96
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_mul_add}
	xor eax, eax
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rax
	mov QWORD PTR [rsp+16], rax
	mov QWORD PTR [rsp+24], rax
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], rax
	mov QWORD PTR [rsp+48], rax
	mov QWORD PTR [rsp+56], rax
	mov QWORD PTR [rsp+64], rax
	mov QWORD PTR [rsp+72], rax
	mov QWORD PTR [rsp+80], rax
	mov QWORD PTR [rsp+88], rax
	mov QWORD PTR [rsp+96], rax
	mov QWORD PTR [rsp+104], rax
	mov QWORD PTR [rsp+112], rax
	mov QWORD PTR [rsp+120], rax
	mov QWORD PTR [rsp+128], rax
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rax
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
	mov QWORD PTR [rsp+168], rax
	mov QWORD PTR [rsp+176], rax
	mov QWORD PTR [rsp+184], rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
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
	lea rsp, [rsp-264]
	vmovdqu YMMWORD PTR [rsp+232], ymm0
	vmovdqu YMMWORD PTR [rsp+200], ymm0
	vmovdqu YMMWORD PTR [rsp+168], ymm0
	vmovdqu YMMWORD PTR [rsp+136], ymm0
	vmovdqu YMMWORD PTR [rsp+104], ymm0
	vmovdqu YMMWORD PTR [rsp+72], ymm0
	vmovdqu YMMWORD PTR [rsp+40], ymm0
	vmovdqu YMMWORD PTR [rsp+8], ymm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+264]
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

vg_ed25519_key_pair_avx2_adx:
	push rdi
	push rsi
	push rcx
	mov rdi, rdx
	mov rdx, rsi
	mov esi, 32
	call {vg_sha512_digest_avx2_core}
	mov rdi, QWORD PTR [rsp+16]
	mov rsi, QWORD PTR [rsp+8]
	mov rdx, QWORD PTR [rsp]
	call {vg_ed25519_public_key_expanded_adx}
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
	lea rsp, [rsp-1632]
	vmovdqu YMMWORD PTR [rsp+1600], ymm0
	vmovdqu YMMWORD PTR [rsp+1568], ymm0
	vmovdqu YMMWORD PTR [rsp+1536], ymm0
	vmovdqu YMMWORD PTR [rsp+1504], ymm0
	vmovdqu YMMWORD PTR [rsp+1472], ymm0
	vmovdqu YMMWORD PTR [rsp+1440], ymm0
	vmovdqu YMMWORD PTR [rsp+1408], ymm0
	vmovdqu YMMWORD PTR [rsp+1376], ymm0
	vmovdqu YMMWORD PTR [rsp+1344], ymm0
	vmovdqu YMMWORD PTR [rsp+1312], ymm0
	vmovdqu YMMWORD PTR [rsp+1280], ymm0
	vmovdqu YMMWORD PTR [rsp+1248], ymm0
	vmovdqu YMMWORD PTR [rsp+1216], ymm0
	vmovdqu YMMWORD PTR [rsp+1184], ymm0
	vmovdqu YMMWORD PTR [rsp+1152], ymm0
	vmovdqu YMMWORD PTR [rsp+1120], ymm0
	vmovdqu YMMWORD PTR [rsp+1088], ymm0
	vmovdqu YMMWORD PTR [rsp+1056], ymm0
	vmovdqu YMMWORD PTR [rsp+1024], ymm0
	vmovdqu YMMWORD PTR [rsp+992], ymm0
	vmovdqu YMMWORD PTR [rsp+960], ymm0
	vmovdqu YMMWORD PTR [rsp+928], ymm0
	vmovdqu YMMWORD PTR [rsp+896], ymm0
	vmovdqu YMMWORD PTR [rsp+864], ymm0
	vmovdqu YMMWORD PTR [rsp+832], ymm0
	vmovdqu YMMWORD PTR [rsp+800], ymm0
	vmovdqu YMMWORD PTR [rsp+768], ymm0
	vmovdqu YMMWORD PTR [rsp+736], ymm0
	vmovdqu YMMWORD PTR [rsp+704], ymm0
	vmovdqu YMMWORD PTR [rsp+672], ymm0
	vmovdqu YMMWORD PTR [rsp+640], ymm0
	vmovdqu YMMWORD PTR [rsp+608], ymm0
	vmovdqu YMMWORD PTR [rsp+576], ymm0
	vmovdqu YMMWORD PTR [rsp+544], ymm0
	vmovdqu YMMWORD PTR [rsp+512], ymm0
	vmovdqu YMMWORD PTR [rsp+480], ymm0
	vmovdqu YMMWORD PTR [rsp+448], ymm0
	vmovdqu YMMWORD PTR [rsp+416], ymm0
	vmovdqu YMMWORD PTR [rsp+384], ymm0
	vmovdqu YMMWORD PTR [rsp+352], ymm0
	vmovdqu YMMWORD PTR [rsp+320], ymm0
	vmovdqu YMMWORD PTR [rsp+288], ymm0
	vmovdqu YMMWORD PTR [rsp+256], ymm0
	vmovdqu YMMWORD PTR [rsp+224], ymm0
	vmovdqu YMMWORD PTR [rsp+192], ymm0
	vmovdqu YMMWORD PTR [rsp+160], ymm0
	vmovdqu YMMWORD PTR [rsp+128], ymm0
	vmovdqu YMMWORD PTR [rsp+96], ymm0
	vmovdqu YMMWORD PTR [rsp+64], ymm0
	vmovdqu YMMWORD PTR [rsp+32], ymm0
	vmovdqu YMMWORD PTR [rsp], ymm0
	lea rsp, [rsp+1632]
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

vg_ed25519_verify_avx2:
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rdi, QWORD PTR [rsp+128]
	call {vg_sha512_init_core}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+136]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+160]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+152]
	mov rcx, QWORD PTR [rsp+144]
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+128]
	mov rsi, QWORD PTR [rsp+144]
	add rsi, 64
	mov rdx, rsp
	add rdx, 64
	mov rcx, QWORD PTR [rsp+128]
	add rcx, 192
	call {vg_sha512_finalize_scratch_avx2}
	mov rdi, rsp
	mov rsi, rsp
	add rsi, 64
	mov rdx, QWORD PTR [rsp+128]
	call {vg_ed25519_scalar_reduce}
	xor eax, eax
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], rax
	mov QWORD PTR [rsp+48], rax
	mov QWORD PTR [rsp+56], rax
	mov rdi, QWORD PTR [rsp+160]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, rsp
	mov rcx, QWORD PTR [rsp+128]
	call {vg_ed25519_verify_equation}
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
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
	lea rsp, [rsp-184]
	vmovdqu YMMWORD PTR [rsp+152], ymm0
	vmovdqu YMMWORD PTR [rsp+120], ymm0
	vmovdqu YMMWORD PTR [rsp+88], ymm0
	vmovdqu YMMWORD PTR [rsp+56], ymm0
	vmovdqu YMMWORD PTR [rsp+24], ymm0
	movdqu XMMWORD PTR [rsp+8], xmm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+184]
	mov eax, eax
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

vg_ed25519_sign_expanded_avx2:
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push r9
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+232]
	mov rcx, QWORD PTR [rax]
	mov QWORD PTR [rsp+128], rcx
	mov rcx, QWORD PTR [rax+8]
	mov QWORD PTR [rsp+136], rcx
	mov rcx, QWORD PTR [rax+16]
	mov QWORD PTR [rsp+144], rcx
	mov rcx, QWORD PTR [rax+24]
	mov QWORD PTR [rsp+152], rcx
	mov rcx, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+160], rcx
	mov rcx, QWORD PTR [rax+40]
	mov QWORD PTR [rsp+168], rcx
	mov rcx, QWORD PTR [rax+48]
	mov QWORD PTR [rsp+176], rcx
	mov rcx, QWORD PTR [rax+56]
	mov QWORD PTR [rsp+184], rcx
	mov r8, QWORD PTR [rsp+128]
	mov r9, QWORD PTR [rsp+136]
	mov r10, QWORD PTR [rsp+144]
	mov r11, QWORD PTR [rsp+152]
	and r8, -8
	movabs rcx, 4611686018427387903
	and r11, rcx
	movabs rcx, 4611686018427387904
	or r11, rcx
	mov QWORD PTR [rsp], r8
	mov QWORD PTR [rsp+8], r9
	mov QWORD PTR [rsp+16], r10
	mov QWORD PTR [rsp+24], r11
	mov r8, QWORD PTR [rsp+160]
	mov r9, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+176]
	mov r11, QWORD PTR [rsp+184]
	mov QWORD PTR [rsp+32], r8
	mov QWORD PTR [rsp+40], r9
	mov QWORD PTR [rsp+48], r10
	mov QWORD PTR [rsp+56], r11
	mov rdi, QWORD PTR [rsp+200]
	call {vg_sha512_init_core}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 0
	mov rdx, rsp
	add rdx, 32
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+208]
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+200]
	mov rsi, QWORD PTR [rsp+208]
	add rsi, 32
	mov rdx, rsp
	add rdx, 128
	mov rcx, QWORD PTR [rsp+200]
	add rcx, 192
	call {vg_sha512_finalize_scratch_avx2}
	mov rdi, rsp
	add rdi, 64
	mov rsi, rsp
	add rsi, 128
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_reduce}
	mov rdi, QWORD PTR [rsp+240]
	mov rsi, rsp
	add rsi, 64
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_base}
	mov rdi, QWORD PTR [rsp+200]
	call {vg_sha512_init_core}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+240]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+224]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+208]
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+200]
	mov rsi, QWORD PTR [rsp+208]
	add rsi, 64
	mov rdx, rsp
	add rdx, 128
	mov rcx, QWORD PTR [rsp+200]
	add rcx, 192
	call {vg_sha512_finalize_scratch_avx2}
	mov rdi, rsp
	add rdi, 96
	mov rsi, rsp
	add rsi, 128
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_reduce}
	mov rdi, QWORD PTR [rsp+240]
	add rdi, 32
	mov rsi, rsp
	add rsi, 64
	mov rdx, rsp
	add rdx, 96
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_mul_add}
	xor eax, eax
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rax
	mov QWORD PTR [rsp+16], rax
	mov QWORD PTR [rsp+24], rax
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], rax
	mov QWORD PTR [rsp+48], rax
	mov QWORD PTR [rsp+56], rax
	mov QWORD PTR [rsp+64], rax
	mov QWORD PTR [rsp+72], rax
	mov QWORD PTR [rsp+80], rax
	mov QWORD PTR [rsp+88], rax
	mov QWORD PTR [rsp+96], rax
	mov QWORD PTR [rsp+104], rax
	mov QWORD PTR [rsp+112], rax
	mov QWORD PTR [rsp+120], rax
	mov QWORD PTR [rsp+128], rax
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rax
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
	mov QWORD PTR [rsp+168], rax
	mov QWORD PTR [rsp+176], rax
	mov QWORD PTR [rsp+184], rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
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
	lea rsp, [rsp-264]
	vmovdqu YMMWORD PTR [rsp+232], ymm0
	vmovdqu YMMWORD PTR [rsp+200], ymm0
	vmovdqu YMMWORD PTR [rsp+168], ymm0
	vmovdqu YMMWORD PTR [rsp+136], ymm0
	vmovdqu YMMWORD PTR [rsp+104], ymm0
	vmovdqu YMMWORD PTR [rsp+72], ymm0
	vmovdqu YMMWORD PTR [rsp+40], ymm0
	vmovdqu YMMWORD PTR [rsp+8], ymm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+264]
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

vg_ed25519_key_pair_avx2:
	push rdi
	push rsi
	push rcx
	mov rdi, rdx
	mov rdx, rsi
	mov esi, 32
	call {vg_sha512_digest_avx2_core}
	mov rdi, QWORD PTR [rsp+16]
	mov rsi, QWORD PTR [rsp+8]
	mov rdx, QWORD PTR [rsp]
	call {vg_ed25519_public_key_expanded}
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
	lea rsp, [rsp-1632]
	vmovdqu YMMWORD PTR [rsp+1600], ymm0
	vmovdqu YMMWORD PTR [rsp+1568], ymm0
	vmovdqu YMMWORD PTR [rsp+1536], ymm0
	vmovdqu YMMWORD PTR [rsp+1504], ymm0
	vmovdqu YMMWORD PTR [rsp+1472], ymm0
	vmovdqu YMMWORD PTR [rsp+1440], ymm0
	vmovdqu YMMWORD PTR [rsp+1408], ymm0
	vmovdqu YMMWORD PTR [rsp+1376], ymm0
	vmovdqu YMMWORD PTR [rsp+1344], ymm0
	vmovdqu YMMWORD PTR [rsp+1312], ymm0
	vmovdqu YMMWORD PTR [rsp+1280], ymm0
	vmovdqu YMMWORD PTR [rsp+1248], ymm0
	vmovdqu YMMWORD PTR [rsp+1216], ymm0
	vmovdqu YMMWORD PTR [rsp+1184], ymm0
	vmovdqu YMMWORD PTR [rsp+1152], ymm0
	vmovdqu YMMWORD PTR [rsp+1120], ymm0
	vmovdqu YMMWORD PTR [rsp+1088], ymm0
	vmovdqu YMMWORD PTR [rsp+1056], ymm0
	vmovdqu YMMWORD PTR [rsp+1024], ymm0
	vmovdqu YMMWORD PTR [rsp+992], ymm0
	vmovdqu YMMWORD PTR [rsp+960], ymm0
	vmovdqu YMMWORD PTR [rsp+928], ymm0
	vmovdqu YMMWORD PTR [rsp+896], ymm0
	vmovdqu YMMWORD PTR [rsp+864], ymm0
	vmovdqu YMMWORD PTR [rsp+832], ymm0
	vmovdqu YMMWORD PTR [rsp+800], ymm0
	vmovdqu YMMWORD PTR [rsp+768], ymm0
	vmovdqu YMMWORD PTR [rsp+736], ymm0
	vmovdqu YMMWORD PTR [rsp+704], ymm0
	vmovdqu YMMWORD PTR [rsp+672], ymm0
	vmovdqu YMMWORD PTR [rsp+640], ymm0
	vmovdqu YMMWORD PTR [rsp+608], ymm0
	vmovdqu YMMWORD PTR [rsp+576], ymm0
	vmovdqu YMMWORD PTR [rsp+544], ymm0
	vmovdqu YMMWORD PTR [rsp+512], ymm0
	vmovdqu YMMWORD PTR [rsp+480], ymm0
	vmovdqu YMMWORD PTR [rsp+448], ymm0
	vmovdqu YMMWORD PTR [rsp+416], ymm0
	vmovdqu YMMWORD PTR [rsp+384], ymm0
	vmovdqu YMMWORD PTR [rsp+352], ymm0
	vmovdqu YMMWORD PTR [rsp+320], ymm0
	vmovdqu YMMWORD PTR [rsp+288], ymm0
	vmovdqu YMMWORD PTR [rsp+256], ymm0
	vmovdqu YMMWORD PTR [rsp+224], ymm0
	vmovdqu YMMWORD PTR [rsp+192], ymm0
	vmovdqu YMMWORD PTR [rsp+160], ymm0
	vmovdqu YMMWORD PTR [rsp+128], ymm0
	vmovdqu YMMWORD PTR [rsp+96], ymm0
	vmovdqu YMMWORD PTR [rsp+64], ymm0
	vmovdqu YMMWORD PTR [rsp+32], ymm0
	vmovdqu YMMWORD PTR [rsp], ymm0
	lea rsp, [rsp+1632]
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

vg_ed25519_verify_ifma:
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rdi, QWORD PTR [rsp+128]
	call {vg_sha512_init_core}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+136]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+160]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+152]
	mov rcx, QWORD PTR [rsp+144]
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+128]
	mov rsi, QWORD PTR [rsp+144]
	add rsi, 64
	mov rdx, rsp
	add rdx, 64
	mov rcx, QWORD PTR [rsp+128]
	add rcx, 192
	call {vg_sha512_finalize_scratch}
	mov rdi, rsp
	mov rsi, rsp
	add rsi, 64
	mov rdx, QWORD PTR [rsp+128]
	call {vg_ed25519_scalar_reduce}
	xor eax, eax
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], rax
	mov QWORD PTR [rsp+48], rax
	mov QWORD PTR [rsp+56], rax
	mov rdi, QWORD PTR [rsp+160]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, rsp
	mov rcx, QWORD PTR [rsp+128]
	call {vg_ed25519_verify_equation_ifma}
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	ret
	.p2align 6

vg_ed25519_sign_expanded_ifma:
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push r9
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+232]
	mov rcx, QWORD PTR [rax]
	mov QWORD PTR [rsp+128], rcx
	mov rcx, QWORD PTR [rax+8]
	mov QWORD PTR [rsp+136], rcx
	mov rcx, QWORD PTR [rax+16]
	mov QWORD PTR [rsp+144], rcx
	mov rcx, QWORD PTR [rax+24]
	mov QWORD PTR [rsp+152], rcx
	mov rcx, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+160], rcx
	mov rcx, QWORD PTR [rax+40]
	mov QWORD PTR [rsp+168], rcx
	mov rcx, QWORD PTR [rax+48]
	mov QWORD PTR [rsp+176], rcx
	mov rcx, QWORD PTR [rax+56]
	mov QWORD PTR [rsp+184], rcx
	mov r8, QWORD PTR [rsp+128]
	mov r9, QWORD PTR [rsp+136]
	mov r10, QWORD PTR [rsp+144]
	mov r11, QWORD PTR [rsp+152]
	and r8, -8
	movabs rcx, 4611686018427387903
	and r11, rcx
	movabs rcx, 4611686018427387904
	or r11, rcx
	mov QWORD PTR [rsp], r8
	mov QWORD PTR [rsp+8], r9
	mov QWORD PTR [rsp+16], r10
	mov QWORD PTR [rsp+24], r11
	mov r8, QWORD PTR [rsp+160]
	mov r9, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+176]
	mov r11, QWORD PTR [rsp+184]
	mov QWORD PTR [rsp+32], r8
	mov QWORD PTR [rsp+40], r9
	mov QWORD PTR [rsp+48], r10
	mov QWORD PTR [rsp+56], r11
	mov rdi, QWORD PTR [rsp+200]
	call {vg_sha512_init_core}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 0
	mov rdx, rsp
	add rdx, 32
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+208]
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+200]
	mov rsi, QWORD PTR [rsp+208]
	add rsi, 32
	mov rdx, rsp
	add rdx, 128
	mov rcx, QWORD PTR [rsp+200]
	add rcx, 192
	call {vg_sha512_finalize_scratch}
	mov rdi, rsp
	add rdi, 64
	mov rsi, rsp
	add rsi, 128
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_reduce}
	mov rdi, QWORD PTR [rsp+240]
	mov rsi, rsp
	add rsi, 64
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_base_ifma}
	mov rdi, QWORD PTR [rsp+200]
	call {vg_sha512_init_core}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+240]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+224]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+208]
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+200]
	mov rsi, QWORD PTR [rsp+208]
	add rsi, 64
	mov rdx, rsp
	add rdx, 128
	mov rcx, QWORD PTR [rsp+200]
	add rcx, 192
	call {vg_sha512_finalize_scratch}
	mov rdi, rsp
	add rdi, 96
	mov rsi, rsp
	add rsi, 128
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_reduce}
	mov rdi, QWORD PTR [rsp+240]
	add rdi, 32
	mov rsi, rsp
	add rsi, 64
	mov rdx, rsp
	add rdx, 96
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_mul_add}
	xor eax, eax
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rax
	mov QWORD PTR [rsp+16], rax
	mov QWORD PTR [rsp+24], rax
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], rax
	mov QWORD PTR [rsp+48], rax
	mov QWORD PTR [rsp+56], rax
	mov QWORD PTR [rsp+64], rax
	mov QWORD PTR [rsp+72], rax
	mov QWORD PTR [rsp+80], rax
	mov QWORD PTR [rsp+88], rax
	mov QWORD PTR [rsp+96], rax
	mov QWORD PTR [rsp+104], rax
	mov QWORD PTR [rsp+112], rax
	mov QWORD PTR [rsp+120], rax
	mov QWORD PTR [rsp+128], rax
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rax
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
	mov QWORD PTR [rsp+168], rax
	mov QWORD PTR [rsp+176], rax
	mov QWORD PTR [rsp+184], rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
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
	vpxorq zmm16, zmm16, zmm16
	vpxorq zmm17, zmm17, zmm17
	vpxorq zmm18, zmm18, zmm18
	vpxorq zmm19, zmm19, zmm19
	vpxorq zmm20, zmm20, zmm20
	vpxorq zmm21, zmm21, zmm21
	vpxorq zmm22, zmm22, zmm22
	vpxorq zmm23, zmm23, zmm23
	vpxorq zmm24, zmm24, zmm24
	vpxorq zmm25, zmm25, zmm25
	vpxorq zmm26, zmm26, zmm26
	vpxorq zmm27, zmm27, zmm27
	vpxorq zmm28, zmm28, zmm28
	vpxorq zmm29, zmm29, zmm29
	vpxorq zmm30, zmm30, zmm30
	vpxorq zmm31, zmm31, zmm31
	xor r11d, r11d
	lea rsp, [rsp-16]
	stmxcsr DWORD PTR [rsp]
	mov r11d, DWORD PTR [rsp]
	and r11d, 65472
	mov DWORD PTR [rsp], r11d
	mov r11d, 8127
	mov DWORD PTR [rsp+4], r11d
	ldmxcsr DWORD PTR [rsp+4]
	lfence
	lfence
	ldmxcsr DWORD PTR [rsp]
	xor r11d, r11d
	lea rsp, [rsp+16]
	lea rsp, [rsp-264]
	vmovdqu YMMWORD PTR [rsp+232], ymm0
	vmovdqu YMMWORD PTR [rsp+200], ymm0
	vmovdqu YMMWORD PTR [rsp+168], ymm0
	vmovdqu YMMWORD PTR [rsp+136], ymm0
	vmovdqu YMMWORD PTR [rsp+104], ymm0
	vmovdqu YMMWORD PTR [rsp+72], ymm0
	vmovdqu YMMWORD PTR [rsp+40], ymm0
	vmovdqu YMMWORD PTR [rsp+8], ymm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+264]
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

vg_ed25519_key_pair_ifma:
	push rdi
	push rsi
	push rcx
	mov rdi, rdx
	mov rdx, rsi
	mov esi, 32
	call {vg_sha512_digest_core}
	mov rdi, QWORD PTR [rsp+16]
	mov rsi, QWORD PTR [rsp+8]
	mov rdx, QWORD PTR [rsp]
	call {vg_ed25519_public_key_expanded_ifma}
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
	vpxorq zmm16, zmm16, zmm16
	vpxorq zmm17, zmm17, zmm17
	vpxorq zmm18, zmm18, zmm18
	vpxorq zmm19, zmm19, zmm19
	vpxorq zmm20, zmm20, zmm20
	vpxorq zmm21, zmm21, zmm21
	vpxorq zmm22, zmm22, zmm22
	vpxorq zmm23, zmm23, zmm23
	vpxorq zmm24, zmm24, zmm24
	vpxorq zmm25, zmm25, zmm25
	vpxorq zmm26, zmm26, zmm26
	vpxorq zmm27, zmm27, zmm27
	vpxorq zmm28, zmm28, zmm28
	vpxorq zmm29, zmm29, zmm29
	vpxorq zmm30, zmm30, zmm30
	vpxorq zmm31, zmm31, zmm31
	xor r11d, r11d
	lea rsp, [rsp-16]
	stmxcsr DWORD PTR [rsp]
	mov r11d, DWORD PTR [rsp]
	and r11d, 65472
	mov DWORD PTR [rsp], r11d
	mov r11d, 8127
	mov DWORD PTR [rsp+4], r11d
	ldmxcsr DWORD PTR [rsp+4]
	lfence
	lfence
	ldmxcsr DWORD PTR [rsp]
	xor r11d, r11d
	lea rsp, [rsp+16]
	lea rsp, [rsp-1632]
	vmovdqu YMMWORD PTR [rsp+1600], ymm0
	vmovdqu YMMWORD PTR [rsp+1568], ymm0
	vmovdqu YMMWORD PTR [rsp+1536], ymm0
	vmovdqu YMMWORD PTR [rsp+1504], ymm0
	vmovdqu YMMWORD PTR [rsp+1472], ymm0
	vmovdqu YMMWORD PTR [rsp+1440], ymm0
	vmovdqu YMMWORD PTR [rsp+1408], ymm0
	vmovdqu YMMWORD PTR [rsp+1376], ymm0
	vmovdqu YMMWORD PTR [rsp+1344], ymm0
	vmovdqu YMMWORD PTR [rsp+1312], ymm0
	vmovdqu YMMWORD PTR [rsp+1280], ymm0
	vmovdqu YMMWORD PTR [rsp+1248], ymm0
	vmovdqu YMMWORD PTR [rsp+1216], ymm0
	vmovdqu YMMWORD PTR [rsp+1184], ymm0
	vmovdqu YMMWORD PTR [rsp+1152], ymm0
	vmovdqu YMMWORD PTR [rsp+1120], ymm0
	vmovdqu YMMWORD PTR [rsp+1088], ymm0
	vmovdqu YMMWORD PTR [rsp+1056], ymm0
	vmovdqu YMMWORD PTR [rsp+1024], ymm0
	vmovdqu YMMWORD PTR [rsp+992], ymm0
	vmovdqu YMMWORD PTR [rsp+960], ymm0
	vmovdqu YMMWORD PTR [rsp+928], ymm0
	vmovdqu YMMWORD PTR [rsp+896], ymm0
	vmovdqu YMMWORD PTR [rsp+864], ymm0
	vmovdqu YMMWORD PTR [rsp+832], ymm0
	vmovdqu YMMWORD PTR [rsp+800], ymm0
	vmovdqu YMMWORD PTR [rsp+768], ymm0
	vmovdqu YMMWORD PTR [rsp+736], ymm0
	vmovdqu YMMWORD PTR [rsp+704], ymm0
	vmovdqu YMMWORD PTR [rsp+672], ymm0
	vmovdqu YMMWORD PTR [rsp+640], ymm0
	vmovdqu YMMWORD PTR [rsp+608], ymm0
	vmovdqu YMMWORD PTR [rsp+576], ymm0
	vmovdqu YMMWORD PTR [rsp+544], ymm0
	vmovdqu YMMWORD PTR [rsp+512], ymm0
	vmovdqu YMMWORD PTR [rsp+480], ymm0
	vmovdqu YMMWORD PTR [rsp+448], ymm0
	vmovdqu YMMWORD PTR [rsp+416], ymm0
	vmovdqu YMMWORD PTR [rsp+384], ymm0
	vmovdqu YMMWORD PTR [rsp+352], ymm0
	vmovdqu YMMWORD PTR [rsp+320], ymm0
	vmovdqu YMMWORD PTR [rsp+288], ymm0
	vmovdqu YMMWORD PTR [rsp+256], ymm0
	vmovdqu YMMWORD PTR [rsp+224], ymm0
	vmovdqu YMMWORD PTR [rsp+192], ymm0
	vmovdqu YMMWORD PTR [rsp+160], ymm0
	vmovdqu YMMWORD PTR [rsp+128], ymm0
	vmovdqu YMMWORD PTR [rsp+96], ymm0
	vmovdqu YMMWORD PTR [rsp+64], ymm0
	vmovdqu YMMWORD PTR [rsp+32], ymm0
	vmovdqu YMMWORD PTR [rsp], ymm0
	lea rsp, [rsp+1632]
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

vg_ed25519_verify_adx:
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rdi, QWORD PTR [rsp+128]
	call {vg_sha512_init_core}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+136]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+160]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+152]
	mov rcx, QWORD PTR [rsp+144]
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+128]
	mov rsi, QWORD PTR [rsp+144]
	add rsi, 64
	mov rdx, rsp
	add rdx, 64
	mov rcx, QWORD PTR [rsp+128]
	add rcx, 192
	call {vg_sha512_finalize_scratch}
	mov rdi, rsp
	mov rsi, rsp
	add rsi, 64
	mov rdx, QWORD PTR [rsp+128]
	call {vg_ed25519_scalar_reduce}
	xor eax, eax
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], rax
	mov QWORD PTR [rsp+48], rax
	mov QWORD PTR [rsp+56], rax
	mov rdi, QWORD PTR [rsp+160]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, rsp
	mov rcx, QWORD PTR [rsp+128]
	call {vg_ed25519_verify_equation_adx}
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
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
	lea rsp, [rsp-184]
	movdqu XMMWORD PTR [rsp+168], xmm0
	movdqu XMMWORD PTR [rsp+152], xmm0
	movdqu XMMWORD PTR [rsp+136], xmm0
	movdqu XMMWORD PTR [rsp+120], xmm0
	movdqu XMMWORD PTR [rsp+104], xmm0
	movdqu XMMWORD PTR [rsp+88], xmm0
	movdqu XMMWORD PTR [rsp+72], xmm0
	movdqu XMMWORD PTR [rsp+56], xmm0
	movdqu XMMWORD PTR [rsp+40], xmm0
	movdqu XMMWORD PTR [rsp+24], xmm0
	movdqu XMMWORD PTR [rsp+8], xmm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+184]
	mov eax, eax
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

vg_ed25519_sign_expanded_adx:
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push r9
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+232]
	mov rcx, QWORD PTR [rax]
	mov QWORD PTR [rsp+128], rcx
	mov rcx, QWORD PTR [rax+8]
	mov QWORD PTR [rsp+136], rcx
	mov rcx, QWORD PTR [rax+16]
	mov QWORD PTR [rsp+144], rcx
	mov rcx, QWORD PTR [rax+24]
	mov QWORD PTR [rsp+152], rcx
	mov rcx, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+160], rcx
	mov rcx, QWORD PTR [rax+40]
	mov QWORD PTR [rsp+168], rcx
	mov rcx, QWORD PTR [rax+48]
	mov QWORD PTR [rsp+176], rcx
	mov rcx, QWORD PTR [rax+56]
	mov QWORD PTR [rsp+184], rcx
	mov r8, QWORD PTR [rsp+128]
	mov r9, QWORD PTR [rsp+136]
	mov r10, QWORD PTR [rsp+144]
	mov r11, QWORD PTR [rsp+152]
	and r8, -8
	movabs rcx, 4611686018427387903
	and r11, rcx
	movabs rcx, 4611686018427387904
	or r11, rcx
	mov QWORD PTR [rsp], r8
	mov QWORD PTR [rsp+8], r9
	mov QWORD PTR [rsp+16], r10
	mov QWORD PTR [rsp+24], r11
	mov r8, QWORD PTR [rsp+160]
	mov r9, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+176]
	mov r11, QWORD PTR [rsp+184]
	mov QWORD PTR [rsp+32], r8
	mov QWORD PTR [rsp+40], r9
	mov QWORD PTR [rsp+48], r10
	mov QWORD PTR [rsp+56], r11
	mov rdi, QWORD PTR [rsp+200]
	call {vg_sha512_init_core}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 0
	mov rdx, rsp
	add rdx, 32
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+208]
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+200]
	mov rsi, QWORD PTR [rsp+208]
	add rsi, 32
	mov rdx, rsp
	add rdx, 128
	mov rcx, QWORD PTR [rsp+200]
	add rcx, 192
	call {vg_sha512_finalize_scratch}
	mov rdi, rsp
	add rdi, 64
	mov rsi, rsp
	add rsi, 128
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_reduce}
	mov rdi, QWORD PTR [rsp+240]
	mov rsi, rsp
	add rsi, 64
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_base_adx}
	mov rdi, QWORD PTR [rsp+200]
	call {vg_sha512_init_core}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+240]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+224]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+208]
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+200]
	mov rsi, QWORD PTR [rsp+208]
	add rsi, 64
	mov rdx, rsp
	add rdx, 128
	mov rcx, QWORD PTR [rsp+200]
	add rcx, 192
	call {vg_sha512_finalize_scratch}
	mov rdi, rsp
	add rdi, 96
	mov rsi, rsp
	add rsi, 128
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_reduce}
	mov rdi, QWORD PTR [rsp+240]
	add rdi, 32
	mov rsi, rsp
	add rsi, 64
	mov rdx, rsp
	add rdx, 96
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_mul_add}
	xor eax, eax
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rax
	mov QWORD PTR [rsp+16], rax
	mov QWORD PTR [rsp+24], rax
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], rax
	mov QWORD PTR [rsp+48], rax
	mov QWORD PTR [rsp+56], rax
	mov QWORD PTR [rsp+64], rax
	mov QWORD PTR [rsp+72], rax
	mov QWORD PTR [rsp+80], rax
	mov QWORD PTR [rsp+88], rax
	mov QWORD PTR [rsp+96], rax
	mov QWORD PTR [rsp+104], rax
	mov QWORD PTR [rsp+112], rax
	mov QWORD PTR [rsp+120], rax
	mov QWORD PTR [rsp+128], rax
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rax
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
	mov QWORD PTR [rsp+168], rax
	mov QWORD PTR [rsp+176], rax
	mov QWORD PTR [rsp+184], rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
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
	lea rsp, [rsp-264]
	vmovdqu YMMWORD PTR [rsp+232], ymm0
	vmovdqu YMMWORD PTR [rsp+200], ymm0
	vmovdqu YMMWORD PTR [rsp+168], ymm0
	vmovdqu YMMWORD PTR [rsp+136], ymm0
	vmovdqu YMMWORD PTR [rsp+104], ymm0
	vmovdqu YMMWORD PTR [rsp+72], ymm0
	vmovdqu YMMWORD PTR [rsp+40], ymm0
	vmovdqu YMMWORD PTR [rsp+8], ymm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+264]
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

vg_ed25519_key_pair_adx:
	push rdi
	push rsi
	push rcx
	mov rdi, rdx
	mov rdx, rsi
	mov esi, 32
	call {vg_sha512_digest_core}
	mov rdi, QWORD PTR [rsp+16]
	mov rsi, QWORD PTR [rsp+8]
	mov rdx, QWORD PTR [rsp]
	call {vg_ed25519_public_key_expanded_adx}
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
	lea rsp, [rsp-1632]
	vmovdqu YMMWORD PTR [rsp+1600], ymm0
	vmovdqu YMMWORD PTR [rsp+1568], ymm0
	vmovdqu YMMWORD PTR [rsp+1536], ymm0
	vmovdqu YMMWORD PTR [rsp+1504], ymm0
	vmovdqu YMMWORD PTR [rsp+1472], ymm0
	vmovdqu YMMWORD PTR [rsp+1440], ymm0
	vmovdqu YMMWORD PTR [rsp+1408], ymm0
	vmovdqu YMMWORD PTR [rsp+1376], ymm0
	vmovdqu YMMWORD PTR [rsp+1344], ymm0
	vmovdqu YMMWORD PTR [rsp+1312], ymm0
	vmovdqu YMMWORD PTR [rsp+1280], ymm0
	vmovdqu YMMWORD PTR [rsp+1248], ymm0
	vmovdqu YMMWORD PTR [rsp+1216], ymm0
	vmovdqu YMMWORD PTR [rsp+1184], ymm0
	vmovdqu YMMWORD PTR [rsp+1152], ymm0
	vmovdqu YMMWORD PTR [rsp+1120], ymm0
	vmovdqu YMMWORD PTR [rsp+1088], ymm0
	vmovdqu YMMWORD PTR [rsp+1056], ymm0
	vmovdqu YMMWORD PTR [rsp+1024], ymm0
	vmovdqu YMMWORD PTR [rsp+992], ymm0
	vmovdqu YMMWORD PTR [rsp+960], ymm0
	vmovdqu YMMWORD PTR [rsp+928], ymm0
	vmovdqu YMMWORD PTR [rsp+896], ymm0
	vmovdqu YMMWORD PTR [rsp+864], ymm0
	vmovdqu YMMWORD PTR [rsp+832], ymm0
	vmovdqu YMMWORD PTR [rsp+800], ymm0
	vmovdqu YMMWORD PTR [rsp+768], ymm0
	vmovdqu YMMWORD PTR [rsp+736], ymm0
	vmovdqu YMMWORD PTR [rsp+704], ymm0
	vmovdqu YMMWORD PTR [rsp+672], ymm0
	vmovdqu YMMWORD PTR [rsp+640], ymm0
	vmovdqu YMMWORD PTR [rsp+608], ymm0
	vmovdqu YMMWORD PTR [rsp+576], ymm0
	vmovdqu YMMWORD PTR [rsp+544], ymm0
	vmovdqu YMMWORD PTR [rsp+512], ymm0
	vmovdqu YMMWORD PTR [rsp+480], ymm0
	vmovdqu YMMWORD PTR [rsp+448], ymm0
	vmovdqu YMMWORD PTR [rsp+416], ymm0
	vmovdqu YMMWORD PTR [rsp+384], ymm0
	vmovdqu YMMWORD PTR [rsp+352], ymm0
	vmovdqu YMMWORD PTR [rsp+320], ymm0
	vmovdqu YMMWORD PTR [rsp+288], ymm0
	vmovdqu YMMWORD PTR [rsp+256], ymm0
	vmovdqu YMMWORD PTR [rsp+224], ymm0
	vmovdqu YMMWORD PTR [rsp+192], ymm0
	vmovdqu YMMWORD PTR [rsp+160], ymm0
	vmovdqu YMMWORD PTR [rsp+128], ymm0
	vmovdqu YMMWORD PTR [rsp+96], ymm0
	vmovdqu YMMWORD PTR [rsp+64], ymm0
	vmovdqu YMMWORD PTR [rsp+32], ymm0
	vmovdqu YMMWORD PTR [rsp], ymm0
	lea rsp, [rsp+1632]
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

vg_ed25519_verify:
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rdi, QWORD PTR [rsp+128]
	call {vg_sha512_init_core}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+136]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+160]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+128]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+152]
	mov rcx, QWORD PTR [rsp+144]
	mov r8, QWORD PTR [rsp+128]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+128]
	mov rsi, QWORD PTR [rsp+144]
	add rsi, 64
	mov rdx, rsp
	add rdx, 64
	mov rcx, QWORD PTR [rsp+128]
	add rcx, 192
	call {vg_sha512_finalize_scratch}
	mov rdi, rsp
	mov rsi, rsp
	add rsi, 64
	mov rdx, QWORD PTR [rsp+128]
	call {vg_ed25519_scalar_reduce}
	xor eax, eax
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], rax
	mov QWORD PTR [rsp+48], rax
	mov QWORD PTR [rsp+56], rax
	mov rdi, QWORD PTR [rsp+160]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, rsp
	mov rcx, QWORD PTR [rsp+128]
	call {vg_ed25519_verify_equation}
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
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
	lea rsp, [rsp-184]
	movdqu XMMWORD PTR [rsp+168], xmm0
	movdqu XMMWORD PTR [rsp+152], xmm0
	movdqu XMMWORD PTR [rsp+136], xmm0
	movdqu XMMWORD PTR [rsp+120], xmm0
	movdqu XMMWORD PTR [rsp+104], xmm0
	movdqu XMMWORD PTR [rsp+88], xmm0
	movdqu XMMWORD PTR [rsp+72], xmm0
	movdqu XMMWORD PTR [rsp+56], xmm0
	movdqu XMMWORD PTR [rsp+40], xmm0
	movdqu XMMWORD PTR [rsp+24], xmm0
	movdqu XMMWORD PTR [rsp+8], xmm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+184]
	mov eax, eax
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

vg_ed25519_sign_expanded:
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push r9
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+232]
	mov rcx, QWORD PTR [rax]
	mov QWORD PTR [rsp+128], rcx
	mov rcx, QWORD PTR [rax+8]
	mov QWORD PTR [rsp+136], rcx
	mov rcx, QWORD PTR [rax+16]
	mov QWORD PTR [rsp+144], rcx
	mov rcx, QWORD PTR [rax+24]
	mov QWORD PTR [rsp+152], rcx
	mov rcx, QWORD PTR [rax+32]
	mov QWORD PTR [rsp+160], rcx
	mov rcx, QWORD PTR [rax+40]
	mov QWORD PTR [rsp+168], rcx
	mov rcx, QWORD PTR [rax+48]
	mov QWORD PTR [rsp+176], rcx
	mov rcx, QWORD PTR [rax+56]
	mov QWORD PTR [rsp+184], rcx
	mov r8, QWORD PTR [rsp+128]
	mov r9, QWORD PTR [rsp+136]
	mov r10, QWORD PTR [rsp+144]
	mov r11, QWORD PTR [rsp+152]
	and r8, -8
	movabs rcx, 4611686018427387903
	and r11, rcx
	movabs rcx, 4611686018427387904
	or r11, rcx
	mov QWORD PTR [rsp], r8
	mov QWORD PTR [rsp+8], r9
	mov QWORD PTR [rsp+16], r10
	mov QWORD PTR [rsp+24], r11
	mov r8, QWORD PTR [rsp+160]
	mov r9, QWORD PTR [rsp+168]
	mov r10, QWORD PTR [rsp+176]
	mov r11, QWORD PTR [rsp+184]
	mov QWORD PTR [rsp+32], r8
	mov QWORD PTR [rsp+40], r9
	mov QWORD PTR [rsp+48], r10
	mov QWORD PTR [rsp+56], r11
	mov rdi, QWORD PTR [rsp+200]
	call {vg_sha512_init_core}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 0
	mov rdx, rsp
	add rdx, 32
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+208]
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+200]
	mov rsi, QWORD PTR [rsp+208]
	add rsi, 32
	mov rdx, rsp
	add rdx, 128
	mov rcx, QWORD PTR [rsp+200]
	add rcx, 192
	call {vg_sha512_finalize_scratch}
	mov rdi, rsp
	add rdi, 64
	mov rsi, rsp
	add rsi, 128
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_reduce}
	mov rdi, QWORD PTR [rsp+240]
	mov rsi, rsp
	add rsi, 64
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_base}
	mov rdi, QWORD PTR [rsp+200]
	call {vg_sha512_init_core}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+240]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 32
	mov rdx, QWORD PTR [rsp+224]
	mov ecx, 32
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+200]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+216]
	mov rcx, QWORD PTR [rsp+208]
	mov r8, QWORD PTR [rsp+200]
	add r8, 192
	call {vg_sha512_update_scratch}
	mov rdi, QWORD PTR [rsp+200]
	mov rsi, QWORD PTR [rsp+208]
	add rsi, 64
	mov rdx, rsp
	add rdx, 128
	mov rcx, QWORD PTR [rsp+200]
	add rcx, 192
	call {vg_sha512_finalize_scratch}
	mov rdi, rsp
	add rdi, 96
	mov rsi, rsp
	add rsi, 128
	mov rdx, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_reduce}
	mov rdi, QWORD PTR [rsp+240]
	add rdi, 32
	mov rsi, rsp
	add rsi, 64
	mov rdx, rsp
	add rdx, 96
	mov rcx, rsp
	add rcx, 0
	mov r8, QWORD PTR [rsp+200]
	call {vg_ed25519_scalar_mul_add}
	xor eax, eax
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], rax
	mov QWORD PTR [rsp+16], rax
	mov QWORD PTR [rsp+24], rax
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], rax
	mov QWORD PTR [rsp+48], rax
	mov QWORD PTR [rsp+56], rax
	mov QWORD PTR [rsp+64], rax
	mov QWORD PTR [rsp+72], rax
	mov QWORD PTR [rsp+80], rax
	mov QWORD PTR [rsp+88], rax
	mov QWORD PTR [rsp+96], rax
	mov QWORD PTR [rsp+104], rax
	mov QWORD PTR [rsp+112], rax
	mov QWORD PTR [rsp+120], rax
	mov QWORD PTR [rsp+128], rax
	mov QWORD PTR [rsp+136], rax
	mov QWORD PTR [rsp+144], rax
	mov QWORD PTR [rsp+152], rax
	mov QWORD PTR [rsp+160], rax
	mov QWORD PTR [rsp+168], rax
	mov QWORD PTR [rsp+176], rax
	mov QWORD PTR [rsp+184], rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
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
	lea rsp, [rsp-264]
	movdqu XMMWORD PTR [rsp+248], xmm0
	movdqu XMMWORD PTR [rsp+232], xmm0
	movdqu XMMWORD PTR [rsp+216], xmm0
	movdqu XMMWORD PTR [rsp+200], xmm0
	movdqu XMMWORD PTR [rsp+184], xmm0
	movdqu XMMWORD PTR [rsp+168], xmm0
	movdqu XMMWORD PTR [rsp+152], xmm0
	movdqu XMMWORD PTR [rsp+136], xmm0
	movdqu XMMWORD PTR [rsp+120], xmm0
	movdqu XMMWORD PTR [rsp+104], xmm0
	movdqu XMMWORD PTR [rsp+88], xmm0
	movdqu XMMWORD PTR [rsp+72], xmm0
	movdqu XMMWORD PTR [rsp+56], xmm0
	movdqu XMMWORD PTR [rsp+40], xmm0
	movdqu XMMWORD PTR [rsp+24], xmm0
	movdqu XMMWORD PTR [rsp+8], xmm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+264]
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

vg_ed25519_key_pair:
	push rdi
	push rsi
	push rcx
	mov rdi, rdx
	mov rdx, rsi
	mov esi, 32
	call {vg_sha512_digest_core}
	mov rdi, QWORD PTR [rsp+16]
	mov rsi, QWORD PTR [rsp+8]
	mov rdx, QWORD PTR [rsp]
	call {vg_ed25519_public_key_expanded}
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
	lea rsp, [rsp-1632]
	movdqu XMMWORD PTR [rsp+1616], xmm0
	movdqu XMMWORD PTR [rsp+1600], xmm0
	movdqu XMMWORD PTR [rsp+1584], xmm0
	movdqu XMMWORD PTR [rsp+1568], xmm0
	movdqu XMMWORD PTR [rsp+1552], xmm0
	movdqu XMMWORD PTR [rsp+1536], xmm0
	movdqu XMMWORD PTR [rsp+1520], xmm0
	movdqu XMMWORD PTR [rsp+1504], xmm0
	movdqu XMMWORD PTR [rsp+1488], xmm0
	movdqu XMMWORD PTR [rsp+1472], xmm0
	movdqu XMMWORD PTR [rsp+1456], xmm0
	movdqu XMMWORD PTR [rsp+1440], xmm0
	movdqu XMMWORD PTR [rsp+1424], xmm0
	movdqu XMMWORD PTR [rsp+1408], xmm0
	movdqu XMMWORD PTR [rsp+1392], xmm0
	movdqu XMMWORD PTR [rsp+1376], xmm0
	movdqu XMMWORD PTR [rsp+1360], xmm0
	movdqu XMMWORD PTR [rsp+1344], xmm0
	movdqu XMMWORD PTR [rsp+1328], xmm0
	movdqu XMMWORD PTR [rsp+1312], xmm0
	movdqu XMMWORD PTR [rsp+1296], xmm0
	movdqu XMMWORD PTR [rsp+1280], xmm0
	movdqu XMMWORD PTR [rsp+1264], xmm0
	movdqu XMMWORD PTR [rsp+1248], xmm0
	movdqu XMMWORD PTR [rsp+1232], xmm0
	movdqu XMMWORD PTR [rsp+1216], xmm0
	movdqu XMMWORD PTR [rsp+1200], xmm0
	movdqu XMMWORD PTR [rsp+1184], xmm0
	movdqu XMMWORD PTR [rsp+1168], xmm0
	movdqu XMMWORD PTR [rsp+1152], xmm0
	movdqu XMMWORD PTR [rsp+1136], xmm0
	movdqu XMMWORD PTR [rsp+1120], xmm0
	movdqu XMMWORD PTR [rsp+1104], xmm0
	movdqu XMMWORD PTR [rsp+1088], xmm0
	movdqu XMMWORD PTR [rsp+1072], xmm0
	movdqu XMMWORD PTR [rsp+1056], xmm0
	movdqu XMMWORD PTR [rsp+1040], xmm0
	movdqu XMMWORD PTR [rsp+1024], xmm0
	movdqu XMMWORD PTR [rsp+1008], xmm0
	movdqu XMMWORD PTR [rsp+992], xmm0
	movdqu XMMWORD PTR [rsp+976], xmm0
	movdqu XMMWORD PTR [rsp+960], xmm0
	movdqu XMMWORD PTR [rsp+944], xmm0
	movdqu XMMWORD PTR [rsp+928], xmm0
	movdqu XMMWORD PTR [rsp+912], xmm0
	movdqu XMMWORD PTR [rsp+896], xmm0
	movdqu XMMWORD PTR [rsp+880], xmm0
	movdqu XMMWORD PTR [rsp+864], xmm0
	movdqu XMMWORD PTR [rsp+848], xmm0
	movdqu XMMWORD PTR [rsp+832], xmm0
	movdqu XMMWORD PTR [rsp+816], xmm0
	movdqu XMMWORD PTR [rsp+800], xmm0
	movdqu XMMWORD PTR [rsp+784], xmm0
	movdqu XMMWORD PTR [rsp+768], xmm0
	movdqu XMMWORD PTR [rsp+752], xmm0
	movdqu XMMWORD PTR [rsp+736], xmm0
	movdqu XMMWORD PTR [rsp+720], xmm0
	movdqu XMMWORD PTR [rsp+704], xmm0
	movdqu XMMWORD PTR [rsp+688], xmm0
	movdqu XMMWORD PTR [rsp+672], xmm0
	movdqu XMMWORD PTR [rsp+656], xmm0
	movdqu XMMWORD PTR [rsp+640], xmm0
	movdqu XMMWORD PTR [rsp+624], xmm0
	movdqu XMMWORD PTR [rsp+608], xmm0
	movdqu XMMWORD PTR [rsp+592], xmm0
	movdqu XMMWORD PTR [rsp+576], xmm0
	movdqu XMMWORD PTR [rsp+560], xmm0
	movdqu XMMWORD PTR [rsp+544], xmm0
	movdqu XMMWORD PTR [rsp+528], xmm0
	movdqu XMMWORD PTR [rsp+512], xmm0
	movdqu XMMWORD PTR [rsp+496], xmm0
	movdqu XMMWORD PTR [rsp+480], xmm0
	movdqu XMMWORD PTR [rsp+464], xmm0
	movdqu XMMWORD PTR [rsp+448], xmm0
	movdqu XMMWORD PTR [rsp+432], xmm0
	movdqu XMMWORD PTR [rsp+416], xmm0
	movdqu XMMWORD PTR [rsp+400], xmm0
	movdqu XMMWORD PTR [rsp+384], xmm0
	movdqu XMMWORD PTR [rsp+368], xmm0
	movdqu XMMWORD PTR [rsp+352], xmm0
	movdqu XMMWORD PTR [rsp+336], xmm0
	movdqu XMMWORD PTR [rsp+320], xmm0
	movdqu XMMWORD PTR [rsp+304], xmm0
	movdqu XMMWORD PTR [rsp+288], xmm0
	movdqu XMMWORD PTR [rsp+272], xmm0
	movdqu XMMWORD PTR [rsp+256], xmm0
	movdqu XMMWORD PTR [rsp+240], xmm0
	movdqu XMMWORD PTR [rsp+224], xmm0
	movdqu XMMWORD PTR [rsp+208], xmm0
	movdqu XMMWORD PTR [rsp+192], xmm0
	movdqu XMMWORD PTR [rsp+176], xmm0
	movdqu XMMWORD PTR [rsp+160], xmm0
	movdqu XMMWORD PTR [rsp+144], xmm0
	movdqu XMMWORD PTR [rsp+128], xmm0
	movdqu XMMWORD PTR [rsp+112], xmm0
	movdqu XMMWORD PTR [rsp+96], xmm0
	movdqu XMMWORD PTR [rsp+80], xmm0
	movdqu XMMWORD PTR [rsp+64], xmm0
	movdqu XMMWORD PTR [rsp+48], xmm0
	movdqu XMMWORD PTR [rsp+32], xmm0
	movdqu XMMWORD PTR [rsp+16], xmm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+1632]
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
