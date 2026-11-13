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
	je 20f
	xor r11d, r11d
	lea rsp, [rsp-184]
	mov QWORD PTR [rsp+176], r11
	movdqu XMMWORD PTR [rsp+160], xmm0
	vmovdqu YMMWORD PTR [rsp+128], ymm0
	vmovdqu YMMWORD PTR [rsp+96], ymm0
	vmovdqu YMMWORD PTR [rsp+64], ymm0
	vmovdqu YMMWORD PTR [rsp+32], ymm0
	vmovdqu YMMWORD PTR [rsp], ymm0
	lea rsp, [rsp+184]
	jmp 21f
20:
	xor r11d, r11d
	lea rsp, [rsp-184]
	mov QWORD PTR [rsp+176], r11
	vmovdqu YMMWORD PTR [rsp+144], ymm0
	vmovdqu YMMWORD PTR [rsp+112], ymm0
	vmovdqu YMMWORD PTR [rsp+80], ymm0
	vmovdqu YMMWORD PTR [rsp+48], ymm0
	vmovdqu YMMWORD PTR [rsp+16], ymm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+184]
21:
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
	xor r11d, r11d
	mov r11d, 16
	test r11d, esp
	je 20f
	xor r11d, r11d
	lea rsp, [rsp-264]
	mov QWORD PTR [rsp+256], r11
	movdqu XMMWORD PTR [rsp+240], xmm0
	vmovdqu YMMWORD PTR [rsp+208], ymm0
	vmovdqu YMMWORD PTR [rsp+176], ymm0
	vmovdqu YMMWORD PTR [rsp+144], ymm0
	vmovdqu YMMWORD PTR [rsp+112], ymm0
	vmovdqu YMMWORD PTR [rsp+80], ymm0
	vmovdqu YMMWORD PTR [rsp+48], ymm0
	vmovdqu YMMWORD PTR [rsp+16], ymm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+264]
	jmp 21f
20:
	xor r11d, r11d
	lea rsp, [rsp-264]
	mov QWORD PTR [rsp+256], r11
	vmovdqu YMMWORD PTR [rsp+224], ymm0
	vmovdqu YMMWORD PTR [rsp+192], ymm0
	vmovdqu YMMWORD PTR [rsp+160], ymm0
	vmovdqu YMMWORD PTR [rsp+128], ymm0
	vmovdqu YMMWORD PTR [rsp+96], ymm0
	vmovdqu YMMWORD PTR [rsp+64], ymm0
	vmovdqu YMMWORD PTR [rsp+32], ymm0
	vmovdqu YMMWORD PTR [rsp], ymm0
	lea rsp, [rsp+264]
21:
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
	xor r11d, r11d
	mov r11d, 16
	test r11d, esp
	je 20f
	xor r11d, r11d
	lea rsp, [rsp-1632]
	mov QWORD PTR [rsp+1624], r11
	movdqu XMMWORD PTR [rsp+1608], xmm0
	vmovdqu YMMWORD PTR [rsp+1576], ymm0
	vmovdqu YMMWORD PTR [rsp+1544], ymm0
	vmovdqu YMMWORD PTR [rsp+1512], ymm0
	vmovdqu YMMWORD PTR [rsp+1480], ymm0
	vmovdqu YMMWORD PTR [rsp+1448], ymm0
	vmovdqu YMMWORD PTR [rsp+1416], ymm0
	vmovdqu YMMWORD PTR [rsp+1384], ymm0
	vmovdqu YMMWORD PTR [rsp+1352], ymm0
	vmovdqu YMMWORD PTR [rsp+1320], ymm0
	vmovdqu YMMWORD PTR [rsp+1288], ymm0
	vmovdqu YMMWORD PTR [rsp+1256], ymm0
	vmovdqu YMMWORD PTR [rsp+1224], ymm0
	vmovdqu YMMWORD PTR [rsp+1192], ymm0
	vmovdqu YMMWORD PTR [rsp+1160], ymm0
	vmovdqu YMMWORD PTR [rsp+1128], ymm0
	vmovdqu YMMWORD PTR [rsp+1096], ymm0
	vmovdqu YMMWORD PTR [rsp+1064], ymm0
	vmovdqu YMMWORD PTR [rsp+1032], ymm0
	vmovdqu YMMWORD PTR [rsp+1000], ymm0
	vmovdqu YMMWORD PTR [rsp+968], ymm0
	vmovdqu YMMWORD PTR [rsp+936], ymm0
	vmovdqu YMMWORD PTR [rsp+904], ymm0
	vmovdqu YMMWORD PTR [rsp+872], ymm0
	vmovdqu YMMWORD PTR [rsp+840], ymm0
	vmovdqu YMMWORD PTR [rsp+808], ymm0
	vmovdqu YMMWORD PTR [rsp+776], ymm0
	vmovdqu YMMWORD PTR [rsp+744], ymm0
	vmovdqu YMMWORD PTR [rsp+712], ymm0
	vmovdqu YMMWORD PTR [rsp+680], ymm0
	vmovdqu YMMWORD PTR [rsp+648], ymm0
	vmovdqu YMMWORD PTR [rsp+616], ymm0
	vmovdqu YMMWORD PTR [rsp+584], ymm0
	vmovdqu YMMWORD PTR [rsp+552], ymm0
	vmovdqu YMMWORD PTR [rsp+520], ymm0
	vmovdqu YMMWORD PTR [rsp+488], ymm0
	vmovdqu YMMWORD PTR [rsp+456], ymm0
	vmovdqu YMMWORD PTR [rsp+424], ymm0
	vmovdqu YMMWORD PTR [rsp+392], ymm0
	vmovdqu YMMWORD PTR [rsp+360], ymm0
	vmovdqu YMMWORD PTR [rsp+328], ymm0
	vmovdqu YMMWORD PTR [rsp+296], ymm0
	vmovdqu YMMWORD PTR [rsp+264], ymm0
	vmovdqu YMMWORD PTR [rsp+232], ymm0
	vmovdqu YMMWORD PTR [rsp+200], ymm0
	vmovdqu YMMWORD PTR [rsp+168], ymm0
	vmovdqu YMMWORD PTR [rsp+136], ymm0
	vmovdqu YMMWORD PTR [rsp+104], ymm0
	vmovdqu YMMWORD PTR [rsp+72], ymm0
	vmovdqu YMMWORD PTR [rsp+40], ymm0
	vmovdqu YMMWORD PTR [rsp+8], ymm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+1632]
	jmp 21f
20:
	xor r11d, r11d
	lea rsp, [rsp-1632]
	mov QWORD PTR [rsp+1624], r11
	vmovdqu YMMWORD PTR [rsp+1592], ymm0
	vmovdqu YMMWORD PTR [rsp+1560], ymm0
	vmovdqu YMMWORD PTR [rsp+1528], ymm0
	vmovdqu YMMWORD PTR [rsp+1496], ymm0
	vmovdqu YMMWORD PTR [rsp+1464], ymm0
	vmovdqu YMMWORD PTR [rsp+1432], ymm0
	vmovdqu YMMWORD PTR [rsp+1400], ymm0
	vmovdqu YMMWORD PTR [rsp+1368], ymm0
	vmovdqu YMMWORD PTR [rsp+1336], ymm0
	vmovdqu YMMWORD PTR [rsp+1304], ymm0
	vmovdqu YMMWORD PTR [rsp+1272], ymm0
	vmovdqu YMMWORD PTR [rsp+1240], ymm0
	vmovdqu YMMWORD PTR [rsp+1208], ymm0
	vmovdqu YMMWORD PTR [rsp+1176], ymm0
	vmovdqu YMMWORD PTR [rsp+1144], ymm0
	vmovdqu YMMWORD PTR [rsp+1112], ymm0
	vmovdqu YMMWORD PTR [rsp+1080], ymm0
	vmovdqu YMMWORD PTR [rsp+1048], ymm0
	vmovdqu YMMWORD PTR [rsp+1016], ymm0
	vmovdqu YMMWORD PTR [rsp+984], ymm0
	vmovdqu YMMWORD PTR [rsp+952], ymm0
	vmovdqu YMMWORD PTR [rsp+920], ymm0
	vmovdqu YMMWORD PTR [rsp+888], ymm0
	vmovdqu YMMWORD PTR [rsp+856], ymm0
	vmovdqu YMMWORD PTR [rsp+824], ymm0
	vmovdqu YMMWORD PTR [rsp+792], ymm0
	vmovdqu YMMWORD PTR [rsp+760], ymm0
	vmovdqu YMMWORD PTR [rsp+728], ymm0
	vmovdqu YMMWORD PTR [rsp+696], ymm0
	vmovdqu YMMWORD PTR [rsp+664], ymm0
	vmovdqu YMMWORD PTR [rsp+632], ymm0
	vmovdqu YMMWORD PTR [rsp+600], ymm0
	vmovdqu YMMWORD PTR [rsp+568], ymm0
	vmovdqu YMMWORD PTR [rsp+536], ymm0
	vmovdqu YMMWORD PTR [rsp+504], ymm0
	vmovdqu YMMWORD PTR [rsp+472], ymm0
	vmovdqu YMMWORD PTR [rsp+440], ymm0
	vmovdqu YMMWORD PTR [rsp+408], ymm0
	vmovdqu YMMWORD PTR [rsp+376], ymm0
	vmovdqu YMMWORD PTR [rsp+344], ymm0
	vmovdqu YMMWORD PTR [rsp+312], ymm0
	vmovdqu YMMWORD PTR [rsp+280], ymm0
	vmovdqu YMMWORD PTR [rsp+248], ymm0
	vmovdqu YMMWORD PTR [rsp+216], ymm0
	vmovdqu YMMWORD PTR [rsp+184], ymm0
	vmovdqu YMMWORD PTR [rsp+152], ymm0
	vmovdqu YMMWORD PTR [rsp+120], ymm0
	vmovdqu YMMWORD PTR [rsp+88], ymm0
	vmovdqu YMMWORD PTR [rsp+56], ymm0
	vmovdqu YMMWORD PTR [rsp+24], ymm0
	movdqu XMMWORD PTR [rsp+8], xmm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+1632]
21:
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
	mov r11d, 16
	test r11d, esp
	je 20f
	xor r11d, r11d
	lea rsp, [rsp-184]
	mov QWORD PTR [rsp+176], r11
	movdqu XMMWORD PTR [rsp+160], xmm0
	vmovdqu YMMWORD PTR [rsp+128], ymm0
	vmovdqu YMMWORD PTR [rsp+96], ymm0
	vmovdqu YMMWORD PTR [rsp+64], ymm0
	vmovdqu YMMWORD PTR [rsp+32], ymm0
	vmovdqu YMMWORD PTR [rsp], ymm0
	lea rsp, [rsp+184]
	jmp 21f
20:
	xor r11d, r11d
	lea rsp, [rsp-184]
	mov QWORD PTR [rsp+176], r11
	vmovdqu YMMWORD PTR [rsp+144], ymm0
	vmovdqu YMMWORD PTR [rsp+112], ymm0
	vmovdqu YMMWORD PTR [rsp+80], ymm0
	vmovdqu YMMWORD PTR [rsp+48], ymm0
	vmovdqu YMMWORD PTR [rsp+16], ymm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+184]
21:
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
	mov r11d, 16
	test r11d, esp
	je 20f
	xor r11d, r11d
	lea rsp, [rsp-264]
	mov QWORD PTR [rsp+256], r11
	movdqu XMMWORD PTR [rsp+240], xmm0
	vmovdqu YMMWORD PTR [rsp+208], ymm0
	vmovdqu YMMWORD PTR [rsp+176], ymm0
	vmovdqu YMMWORD PTR [rsp+144], ymm0
	vmovdqu YMMWORD PTR [rsp+112], ymm0
	vmovdqu YMMWORD PTR [rsp+80], ymm0
	vmovdqu YMMWORD PTR [rsp+48], ymm0
	vmovdqu YMMWORD PTR [rsp+16], ymm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+264]
	jmp 21f
20:
	xor r11d, r11d
	lea rsp, [rsp-264]
	mov QWORD PTR [rsp+256], r11
	vmovdqu YMMWORD PTR [rsp+224], ymm0
	vmovdqu YMMWORD PTR [rsp+192], ymm0
	vmovdqu YMMWORD PTR [rsp+160], ymm0
	vmovdqu YMMWORD PTR [rsp+128], ymm0
	vmovdqu YMMWORD PTR [rsp+96], ymm0
	vmovdqu YMMWORD PTR [rsp+64], ymm0
	vmovdqu YMMWORD PTR [rsp+32], ymm0
	vmovdqu YMMWORD PTR [rsp], ymm0
	lea rsp, [rsp+264]
21:
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
	mov r11d, 16
	test r11d, esp
	je 20f
	xor r11d, r11d
	lea rsp, [rsp-1632]
	mov QWORD PTR [rsp+1624], r11
	movdqu XMMWORD PTR [rsp+1608], xmm0
	vmovdqu YMMWORD PTR [rsp+1576], ymm0
	vmovdqu YMMWORD PTR [rsp+1544], ymm0
	vmovdqu YMMWORD PTR [rsp+1512], ymm0
	vmovdqu YMMWORD PTR [rsp+1480], ymm0
	vmovdqu YMMWORD PTR [rsp+1448], ymm0
	vmovdqu YMMWORD PTR [rsp+1416], ymm0
	vmovdqu YMMWORD PTR [rsp+1384], ymm0
	vmovdqu YMMWORD PTR [rsp+1352], ymm0
	vmovdqu YMMWORD PTR [rsp+1320], ymm0
	vmovdqu YMMWORD PTR [rsp+1288], ymm0
	vmovdqu YMMWORD PTR [rsp+1256], ymm0
	vmovdqu YMMWORD PTR [rsp+1224], ymm0
	vmovdqu YMMWORD PTR [rsp+1192], ymm0
	vmovdqu YMMWORD PTR [rsp+1160], ymm0
	vmovdqu YMMWORD PTR [rsp+1128], ymm0
	vmovdqu YMMWORD PTR [rsp+1096], ymm0
	vmovdqu YMMWORD PTR [rsp+1064], ymm0
	vmovdqu YMMWORD PTR [rsp+1032], ymm0
	vmovdqu YMMWORD PTR [rsp+1000], ymm0
	vmovdqu YMMWORD PTR [rsp+968], ymm0
	vmovdqu YMMWORD PTR [rsp+936], ymm0
	vmovdqu YMMWORD PTR [rsp+904], ymm0
	vmovdqu YMMWORD PTR [rsp+872], ymm0
	vmovdqu YMMWORD PTR [rsp+840], ymm0
	vmovdqu YMMWORD PTR [rsp+808], ymm0
	vmovdqu YMMWORD PTR [rsp+776], ymm0
	vmovdqu YMMWORD PTR [rsp+744], ymm0
	vmovdqu YMMWORD PTR [rsp+712], ymm0
	vmovdqu YMMWORD PTR [rsp+680], ymm0
	vmovdqu YMMWORD PTR [rsp+648], ymm0
	vmovdqu YMMWORD PTR [rsp+616], ymm0
	vmovdqu YMMWORD PTR [rsp+584], ymm0
	vmovdqu YMMWORD PTR [rsp+552], ymm0
	vmovdqu YMMWORD PTR [rsp+520], ymm0
	vmovdqu YMMWORD PTR [rsp+488], ymm0
	vmovdqu YMMWORD PTR [rsp+456], ymm0
	vmovdqu YMMWORD PTR [rsp+424], ymm0
	vmovdqu YMMWORD PTR [rsp+392], ymm0
	vmovdqu YMMWORD PTR [rsp+360], ymm0
	vmovdqu YMMWORD PTR [rsp+328], ymm0
	vmovdqu YMMWORD PTR [rsp+296], ymm0
	vmovdqu YMMWORD PTR [rsp+264], ymm0
	vmovdqu YMMWORD PTR [rsp+232], ymm0
	vmovdqu YMMWORD PTR [rsp+200], ymm0
	vmovdqu YMMWORD PTR [rsp+168], ymm0
	vmovdqu YMMWORD PTR [rsp+136], ymm0
	vmovdqu YMMWORD PTR [rsp+104], ymm0
	vmovdqu YMMWORD PTR [rsp+72], ymm0
	vmovdqu YMMWORD PTR [rsp+40], ymm0
	vmovdqu YMMWORD PTR [rsp+8], ymm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+1632]
	jmp 21f
20:
	xor r11d, r11d
	lea rsp, [rsp-1632]
	mov QWORD PTR [rsp+1624], r11
	vmovdqu YMMWORD PTR [rsp+1592], ymm0
	vmovdqu YMMWORD PTR [rsp+1560], ymm0
	vmovdqu YMMWORD PTR [rsp+1528], ymm0
	vmovdqu YMMWORD PTR [rsp+1496], ymm0
	vmovdqu YMMWORD PTR [rsp+1464], ymm0
	vmovdqu YMMWORD PTR [rsp+1432], ymm0
	vmovdqu YMMWORD PTR [rsp+1400], ymm0
	vmovdqu YMMWORD PTR [rsp+1368], ymm0
	vmovdqu YMMWORD PTR [rsp+1336], ymm0
	vmovdqu YMMWORD PTR [rsp+1304], ymm0
	vmovdqu YMMWORD PTR [rsp+1272], ymm0
	vmovdqu YMMWORD PTR [rsp+1240], ymm0
	vmovdqu YMMWORD PTR [rsp+1208], ymm0
	vmovdqu YMMWORD PTR [rsp+1176], ymm0
	vmovdqu YMMWORD PTR [rsp+1144], ymm0
	vmovdqu YMMWORD PTR [rsp+1112], ymm0
	vmovdqu YMMWORD PTR [rsp+1080], ymm0
	vmovdqu YMMWORD PTR [rsp+1048], ymm0
	vmovdqu YMMWORD PTR [rsp+1016], ymm0
	vmovdqu YMMWORD PTR [rsp+984], ymm0
	vmovdqu YMMWORD PTR [rsp+952], ymm0
	vmovdqu YMMWORD PTR [rsp+920], ymm0
	vmovdqu YMMWORD PTR [rsp+888], ymm0
	vmovdqu YMMWORD PTR [rsp+856], ymm0
	vmovdqu YMMWORD PTR [rsp+824], ymm0
	vmovdqu YMMWORD PTR [rsp+792], ymm0
	vmovdqu YMMWORD PTR [rsp+760], ymm0
	vmovdqu YMMWORD PTR [rsp+728], ymm0
	vmovdqu YMMWORD PTR [rsp+696], ymm0
	vmovdqu YMMWORD PTR [rsp+664], ymm0
	vmovdqu YMMWORD PTR [rsp+632], ymm0
	vmovdqu YMMWORD PTR [rsp+600], ymm0
	vmovdqu YMMWORD PTR [rsp+568], ymm0
	vmovdqu YMMWORD PTR [rsp+536], ymm0
	vmovdqu YMMWORD PTR [rsp+504], ymm0
	vmovdqu YMMWORD PTR [rsp+472], ymm0
	vmovdqu YMMWORD PTR [rsp+440], ymm0
	vmovdqu YMMWORD PTR [rsp+408], ymm0
	vmovdqu YMMWORD PTR [rsp+376], ymm0
	vmovdqu YMMWORD PTR [rsp+344], ymm0
	vmovdqu YMMWORD PTR [rsp+312], ymm0
	vmovdqu YMMWORD PTR [rsp+280], ymm0
	vmovdqu YMMWORD PTR [rsp+248], ymm0
	vmovdqu YMMWORD PTR [rsp+216], ymm0
	vmovdqu YMMWORD PTR [rsp+184], ymm0
	vmovdqu YMMWORD PTR [rsp+152], ymm0
	vmovdqu YMMWORD PTR [rsp+120], ymm0
	vmovdqu YMMWORD PTR [rsp+88], ymm0
	vmovdqu YMMWORD PTR [rsp+56], ymm0
	vmovdqu YMMWORD PTR [rsp+24], ymm0
	movdqu XMMWORD PTR [rsp+8], xmm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+1632]
21:
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
	mov r11d, 16
	test r11d, esp
	je 20f
	xor r11d, r11d
	lea rsp, [rsp-184]
	mov QWORD PTR [rsp+176], r11
	movdqu XMMWORD PTR [rsp+160], xmm0
	vmovdqu YMMWORD PTR [rsp+128], ymm0
	vmovdqu YMMWORD PTR [rsp+96], ymm0
	vmovdqu YMMWORD PTR [rsp+64], ymm0
	vmovdqu YMMWORD PTR [rsp+32], ymm0
	vmovdqu YMMWORD PTR [rsp], ymm0
	lea rsp, [rsp+184]
	jmp 21f
20:
	xor r11d, r11d
	lea rsp, [rsp-184]
	mov QWORD PTR [rsp+176], r11
	vmovdqu YMMWORD PTR [rsp+144], ymm0
	vmovdqu YMMWORD PTR [rsp+112], ymm0
	vmovdqu YMMWORD PTR [rsp+80], ymm0
	vmovdqu YMMWORD PTR [rsp+48], ymm0
	vmovdqu YMMWORD PTR [rsp+16], ymm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+184]
21:
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
	mov r11d, 16
	test r11d, esp
	je 20f
	xor r11d, r11d
	lea rsp, [rsp-264]
	mov QWORD PTR [rsp+256], r11
	movdqu XMMWORD PTR [rsp+240], xmm0
	vmovdqu YMMWORD PTR [rsp+208], ymm0
	vmovdqu YMMWORD PTR [rsp+176], ymm0
	vmovdqu YMMWORD PTR [rsp+144], ymm0
	vmovdqu YMMWORD PTR [rsp+112], ymm0
	vmovdqu YMMWORD PTR [rsp+80], ymm0
	vmovdqu YMMWORD PTR [rsp+48], ymm0
	vmovdqu YMMWORD PTR [rsp+16], ymm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+264]
	jmp 21f
20:
	xor r11d, r11d
	lea rsp, [rsp-264]
	mov QWORD PTR [rsp+256], r11
	vmovdqu YMMWORD PTR [rsp+224], ymm0
	vmovdqu YMMWORD PTR [rsp+192], ymm0
	vmovdqu YMMWORD PTR [rsp+160], ymm0
	vmovdqu YMMWORD PTR [rsp+128], ymm0
	vmovdqu YMMWORD PTR [rsp+96], ymm0
	vmovdqu YMMWORD PTR [rsp+64], ymm0
	vmovdqu YMMWORD PTR [rsp+32], ymm0
	vmovdqu YMMWORD PTR [rsp], ymm0
	lea rsp, [rsp+264]
21:
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
	mov r11d, 16
	test r11d, esp
	je 20f
	xor r11d, r11d
	lea rsp, [rsp-1632]
	mov QWORD PTR [rsp+1624], r11
	movdqu XMMWORD PTR [rsp+1608], xmm0
	vmovdqu YMMWORD PTR [rsp+1576], ymm0
	vmovdqu YMMWORD PTR [rsp+1544], ymm0
	vmovdqu YMMWORD PTR [rsp+1512], ymm0
	vmovdqu YMMWORD PTR [rsp+1480], ymm0
	vmovdqu YMMWORD PTR [rsp+1448], ymm0
	vmovdqu YMMWORD PTR [rsp+1416], ymm0
	vmovdqu YMMWORD PTR [rsp+1384], ymm0
	vmovdqu YMMWORD PTR [rsp+1352], ymm0
	vmovdqu YMMWORD PTR [rsp+1320], ymm0
	vmovdqu YMMWORD PTR [rsp+1288], ymm0
	vmovdqu YMMWORD PTR [rsp+1256], ymm0
	vmovdqu YMMWORD PTR [rsp+1224], ymm0
	vmovdqu YMMWORD PTR [rsp+1192], ymm0
	vmovdqu YMMWORD PTR [rsp+1160], ymm0
	vmovdqu YMMWORD PTR [rsp+1128], ymm0
	vmovdqu YMMWORD PTR [rsp+1096], ymm0
	vmovdqu YMMWORD PTR [rsp+1064], ymm0
	vmovdqu YMMWORD PTR [rsp+1032], ymm0
	vmovdqu YMMWORD PTR [rsp+1000], ymm0
	vmovdqu YMMWORD PTR [rsp+968], ymm0
	vmovdqu YMMWORD PTR [rsp+936], ymm0
	vmovdqu YMMWORD PTR [rsp+904], ymm0
	vmovdqu YMMWORD PTR [rsp+872], ymm0
	vmovdqu YMMWORD PTR [rsp+840], ymm0
	vmovdqu YMMWORD PTR [rsp+808], ymm0
	vmovdqu YMMWORD PTR [rsp+776], ymm0
	vmovdqu YMMWORD PTR [rsp+744], ymm0
	vmovdqu YMMWORD PTR [rsp+712], ymm0
	vmovdqu YMMWORD PTR [rsp+680], ymm0
	vmovdqu YMMWORD PTR [rsp+648], ymm0
	vmovdqu YMMWORD PTR [rsp+616], ymm0
	vmovdqu YMMWORD PTR [rsp+584], ymm0
	vmovdqu YMMWORD PTR [rsp+552], ymm0
	vmovdqu YMMWORD PTR [rsp+520], ymm0
	vmovdqu YMMWORD PTR [rsp+488], ymm0
	vmovdqu YMMWORD PTR [rsp+456], ymm0
	vmovdqu YMMWORD PTR [rsp+424], ymm0
	vmovdqu YMMWORD PTR [rsp+392], ymm0
	vmovdqu YMMWORD PTR [rsp+360], ymm0
	vmovdqu YMMWORD PTR [rsp+328], ymm0
	vmovdqu YMMWORD PTR [rsp+296], ymm0
	vmovdqu YMMWORD PTR [rsp+264], ymm0
	vmovdqu YMMWORD PTR [rsp+232], ymm0
	vmovdqu YMMWORD PTR [rsp+200], ymm0
	vmovdqu YMMWORD PTR [rsp+168], ymm0
	vmovdqu YMMWORD PTR [rsp+136], ymm0
	vmovdqu YMMWORD PTR [rsp+104], ymm0
	vmovdqu YMMWORD PTR [rsp+72], ymm0
	vmovdqu YMMWORD PTR [rsp+40], ymm0
	vmovdqu YMMWORD PTR [rsp+8], ymm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+1632]
	jmp 21f
20:
	xor r11d, r11d
	lea rsp, [rsp-1632]
	mov QWORD PTR [rsp+1624], r11
	vmovdqu YMMWORD PTR [rsp+1592], ymm0
	vmovdqu YMMWORD PTR [rsp+1560], ymm0
	vmovdqu YMMWORD PTR [rsp+1528], ymm0
	vmovdqu YMMWORD PTR [rsp+1496], ymm0
	vmovdqu YMMWORD PTR [rsp+1464], ymm0
	vmovdqu YMMWORD PTR [rsp+1432], ymm0
	vmovdqu YMMWORD PTR [rsp+1400], ymm0
	vmovdqu YMMWORD PTR [rsp+1368], ymm0
	vmovdqu YMMWORD PTR [rsp+1336], ymm0
	vmovdqu YMMWORD PTR [rsp+1304], ymm0
	vmovdqu YMMWORD PTR [rsp+1272], ymm0
	vmovdqu YMMWORD PTR [rsp+1240], ymm0
	vmovdqu YMMWORD PTR [rsp+1208], ymm0
	vmovdqu YMMWORD PTR [rsp+1176], ymm0
	vmovdqu YMMWORD PTR [rsp+1144], ymm0
	vmovdqu YMMWORD PTR [rsp+1112], ymm0
	vmovdqu YMMWORD PTR [rsp+1080], ymm0
	vmovdqu YMMWORD PTR [rsp+1048], ymm0
	vmovdqu YMMWORD PTR [rsp+1016], ymm0
	vmovdqu YMMWORD PTR [rsp+984], ymm0
	vmovdqu YMMWORD PTR [rsp+952], ymm0
	vmovdqu YMMWORD PTR [rsp+920], ymm0
	vmovdqu YMMWORD PTR [rsp+888], ymm0
	vmovdqu YMMWORD PTR [rsp+856], ymm0
	vmovdqu YMMWORD PTR [rsp+824], ymm0
	vmovdqu YMMWORD PTR [rsp+792], ymm0
	vmovdqu YMMWORD PTR [rsp+760], ymm0
	vmovdqu YMMWORD PTR [rsp+728], ymm0
	vmovdqu YMMWORD PTR [rsp+696], ymm0
	vmovdqu YMMWORD PTR [rsp+664], ymm0
	vmovdqu YMMWORD PTR [rsp+632], ymm0
	vmovdqu YMMWORD PTR [rsp+600], ymm0
	vmovdqu YMMWORD PTR [rsp+568], ymm0
	vmovdqu YMMWORD PTR [rsp+536], ymm0
	vmovdqu YMMWORD PTR [rsp+504], ymm0
	vmovdqu YMMWORD PTR [rsp+472], ymm0
	vmovdqu YMMWORD PTR [rsp+440], ymm0
	vmovdqu YMMWORD PTR [rsp+408], ymm0
	vmovdqu YMMWORD PTR [rsp+376], ymm0
	vmovdqu YMMWORD PTR [rsp+344], ymm0
	vmovdqu YMMWORD PTR [rsp+312], ymm0
	vmovdqu YMMWORD PTR [rsp+280], ymm0
	vmovdqu YMMWORD PTR [rsp+248], ymm0
	vmovdqu YMMWORD PTR [rsp+216], ymm0
	vmovdqu YMMWORD PTR [rsp+184], ymm0
	vmovdqu YMMWORD PTR [rsp+152], ymm0
	vmovdqu YMMWORD PTR [rsp+120], ymm0
	vmovdqu YMMWORD PTR [rsp+88], ymm0
	vmovdqu YMMWORD PTR [rsp+56], ymm0
	vmovdqu YMMWORD PTR [rsp+24], ymm0
	movdqu XMMWORD PTR [rsp+8], xmm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+1632]
21:
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
	je 20f
	xor r11d, r11d
	lea rsp, [rsp-184]
	mov QWORD PTR [rsp+176], r11
	movdqu XMMWORD PTR [rsp+160], xmm0
	vmovdqu YMMWORD PTR [rsp+128], ymm0
	vmovdqu YMMWORD PTR [rsp+96], ymm0
	vmovdqu YMMWORD PTR [rsp+64], ymm0
	vmovdqu YMMWORD PTR [rsp+32], ymm0
	vmovdqu YMMWORD PTR [rsp], ymm0
	lea rsp, [rsp+184]
	jmp 21f
20:
	xor r11d, r11d
	lea rsp, [rsp-184]
	mov QWORD PTR [rsp+176], r11
	vmovdqu YMMWORD PTR [rsp+144], ymm0
	vmovdqu YMMWORD PTR [rsp+112], ymm0
	vmovdqu YMMWORD PTR [rsp+80], ymm0
	vmovdqu YMMWORD PTR [rsp+48], ymm0
	vmovdqu YMMWORD PTR [rsp+16], ymm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+184]
21:
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
	xor r11d, r11d
	mov r11d, 16
	test r11d, esp
	je 20f
	xor r11d, r11d
	lea rsp, [rsp-264]
	mov QWORD PTR [rsp+256], r11
	movdqu XMMWORD PTR [rsp+240], xmm0
	vmovdqu YMMWORD PTR [rsp+208], ymm0
	vmovdqu YMMWORD PTR [rsp+176], ymm0
	vmovdqu YMMWORD PTR [rsp+144], ymm0
	vmovdqu YMMWORD PTR [rsp+112], ymm0
	vmovdqu YMMWORD PTR [rsp+80], ymm0
	vmovdqu YMMWORD PTR [rsp+48], ymm0
	vmovdqu YMMWORD PTR [rsp+16], ymm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+264]
	jmp 21f
20:
	xor r11d, r11d
	lea rsp, [rsp-264]
	mov QWORD PTR [rsp+256], r11
	vmovdqu YMMWORD PTR [rsp+224], ymm0
	vmovdqu YMMWORD PTR [rsp+192], ymm0
	vmovdqu YMMWORD PTR [rsp+160], ymm0
	vmovdqu YMMWORD PTR [rsp+128], ymm0
	vmovdqu YMMWORD PTR [rsp+96], ymm0
	vmovdqu YMMWORD PTR [rsp+64], ymm0
	vmovdqu YMMWORD PTR [rsp+32], ymm0
	vmovdqu YMMWORD PTR [rsp], ymm0
	lea rsp, [rsp+264]
21:
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
	xor r11d, r11d
	mov r11d, 16
	test r11d, esp
	je 20f
	xor r11d, r11d
	lea rsp, [rsp-1632]
	mov QWORD PTR [rsp+1624], r11
	movdqu XMMWORD PTR [rsp+1608], xmm0
	vmovdqu YMMWORD PTR [rsp+1576], ymm0
	vmovdqu YMMWORD PTR [rsp+1544], ymm0
	vmovdqu YMMWORD PTR [rsp+1512], ymm0
	vmovdqu YMMWORD PTR [rsp+1480], ymm0
	vmovdqu YMMWORD PTR [rsp+1448], ymm0
	vmovdqu YMMWORD PTR [rsp+1416], ymm0
	vmovdqu YMMWORD PTR [rsp+1384], ymm0
	vmovdqu YMMWORD PTR [rsp+1352], ymm0
	vmovdqu YMMWORD PTR [rsp+1320], ymm0
	vmovdqu YMMWORD PTR [rsp+1288], ymm0
	vmovdqu YMMWORD PTR [rsp+1256], ymm0
	vmovdqu YMMWORD PTR [rsp+1224], ymm0
	vmovdqu YMMWORD PTR [rsp+1192], ymm0
	vmovdqu YMMWORD PTR [rsp+1160], ymm0
	vmovdqu YMMWORD PTR [rsp+1128], ymm0
	vmovdqu YMMWORD PTR [rsp+1096], ymm0
	vmovdqu YMMWORD PTR [rsp+1064], ymm0
	vmovdqu YMMWORD PTR [rsp+1032], ymm0
	vmovdqu YMMWORD PTR [rsp+1000], ymm0
	vmovdqu YMMWORD PTR [rsp+968], ymm0
	vmovdqu YMMWORD PTR [rsp+936], ymm0
	vmovdqu YMMWORD PTR [rsp+904], ymm0
	vmovdqu YMMWORD PTR [rsp+872], ymm0
	vmovdqu YMMWORD PTR [rsp+840], ymm0
	vmovdqu YMMWORD PTR [rsp+808], ymm0
	vmovdqu YMMWORD PTR [rsp+776], ymm0
	vmovdqu YMMWORD PTR [rsp+744], ymm0
	vmovdqu YMMWORD PTR [rsp+712], ymm0
	vmovdqu YMMWORD PTR [rsp+680], ymm0
	vmovdqu YMMWORD PTR [rsp+648], ymm0
	vmovdqu YMMWORD PTR [rsp+616], ymm0
	vmovdqu YMMWORD PTR [rsp+584], ymm0
	vmovdqu YMMWORD PTR [rsp+552], ymm0
	vmovdqu YMMWORD PTR [rsp+520], ymm0
	vmovdqu YMMWORD PTR [rsp+488], ymm0
	vmovdqu YMMWORD PTR [rsp+456], ymm0
	vmovdqu YMMWORD PTR [rsp+424], ymm0
	vmovdqu YMMWORD PTR [rsp+392], ymm0
	vmovdqu YMMWORD PTR [rsp+360], ymm0
	vmovdqu YMMWORD PTR [rsp+328], ymm0
	vmovdqu YMMWORD PTR [rsp+296], ymm0
	vmovdqu YMMWORD PTR [rsp+264], ymm0
	vmovdqu YMMWORD PTR [rsp+232], ymm0
	vmovdqu YMMWORD PTR [rsp+200], ymm0
	vmovdqu YMMWORD PTR [rsp+168], ymm0
	vmovdqu YMMWORD PTR [rsp+136], ymm0
	vmovdqu YMMWORD PTR [rsp+104], ymm0
	vmovdqu YMMWORD PTR [rsp+72], ymm0
	vmovdqu YMMWORD PTR [rsp+40], ymm0
	vmovdqu YMMWORD PTR [rsp+8], ymm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+1632]
	jmp 21f
20:
	xor r11d, r11d
	lea rsp, [rsp-1632]
	mov QWORD PTR [rsp+1624], r11
	vmovdqu YMMWORD PTR [rsp+1592], ymm0
	vmovdqu YMMWORD PTR [rsp+1560], ymm0
	vmovdqu YMMWORD PTR [rsp+1528], ymm0
	vmovdqu YMMWORD PTR [rsp+1496], ymm0
	vmovdqu YMMWORD PTR [rsp+1464], ymm0
	vmovdqu YMMWORD PTR [rsp+1432], ymm0
	vmovdqu YMMWORD PTR [rsp+1400], ymm0
	vmovdqu YMMWORD PTR [rsp+1368], ymm0
	vmovdqu YMMWORD PTR [rsp+1336], ymm0
	vmovdqu YMMWORD PTR [rsp+1304], ymm0
	vmovdqu YMMWORD PTR [rsp+1272], ymm0
	vmovdqu YMMWORD PTR [rsp+1240], ymm0
	vmovdqu YMMWORD PTR [rsp+1208], ymm0
	vmovdqu YMMWORD PTR [rsp+1176], ymm0
	vmovdqu YMMWORD PTR [rsp+1144], ymm0
	vmovdqu YMMWORD PTR [rsp+1112], ymm0
	vmovdqu YMMWORD PTR [rsp+1080], ymm0
	vmovdqu YMMWORD PTR [rsp+1048], ymm0
	vmovdqu YMMWORD PTR [rsp+1016], ymm0
	vmovdqu YMMWORD PTR [rsp+984], ymm0
	vmovdqu YMMWORD PTR [rsp+952], ymm0
	vmovdqu YMMWORD PTR [rsp+920], ymm0
	vmovdqu YMMWORD PTR [rsp+888], ymm0
	vmovdqu YMMWORD PTR [rsp+856], ymm0
	vmovdqu YMMWORD PTR [rsp+824], ymm0
	vmovdqu YMMWORD PTR [rsp+792], ymm0
	vmovdqu YMMWORD PTR [rsp+760], ymm0
	vmovdqu YMMWORD PTR [rsp+728], ymm0
	vmovdqu YMMWORD PTR [rsp+696], ymm0
	vmovdqu YMMWORD PTR [rsp+664], ymm0
	vmovdqu YMMWORD PTR [rsp+632], ymm0
	vmovdqu YMMWORD PTR [rsp+600], ymm0
	vmovdqu YMMWORD PTR [rsp+568], ymm0
	vmovdqu YMMWORD PTR [rsp+536], ymm0
	vmovdqu YMMWORD PTR [rsp+504], ymm0
	vmovdqu YMMWORD PTR [rsp+472], ymm0
	vmovdqu YMMWORD PTR [rsp+440], ymm0
	vmovdqu YMMWORD PTR [rsp+408], ymm0
	vmovdqu YMMWORD PTR [rsp+376], ymm0
	vmovdqu YMMWORD PTR [rsp+344], ymm0
	vmovdqu YMMWORD PTR [rsp+312], ymm0
	vmovdqu YMMWORD PTR [rsp+280], ymm0
	vmovdqu YMMWORD PTR [rsp+248], ymm0
	vmovdqu YMMWORD PTR [rsp+216], ymm0
	vmovdqu YMMWORD PTR [rsp+184], ymm0
	vmovdqu YMMWORD PTR [rsp+152], ymm0
	vmovdqu YMMWORD PTR [rsp+120], ymm0
	vmovdqu YMMWORD PTR [rsp+88], ymm0
	vmovdqu YMMWORD PTR [rsp+56], ymm0
	vmovdqu YMMWORD PTR [rsp+24], ymm0
	movdqu XMMWORD PTR [rsp+8], xmm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+1632]
21:
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
	mov r11d, 16
	test r11d, esp
	je 20f
	xor r11d, r11d
	lea rsp, [rsp-184]
	mov QWORD PTR [rsp+176], r11
	movdqu XMMWORD PTR [rsp+160], xmm0
	vmovdqu YMMWORD PTR [rsp+128], ymm0
	vmovdqu YMMWORD PTR [rsp+96], ymm0
	vmovdqu YMMWORD PTR [rsp+64], ymm0
	vmovdqu YMMWORD PTR [rsp+32], ymm0
	vmovdqu YMMWORD PTR [rsp], ymm0
	lea rsp, [rsp+184]
	jmp 21f
20:
	xor r11d, r11d
	lea rsp, [rsp-184]
	mov QWORD PTR [rsp+176], r11
	vmovdqu YMMWORD PTR [rsp+144], ymm0
	vmovdqu YMMWORD PTR [rsp+112], ymm0
	vmovdqu YMMWORD PTR [rsp+80], ymm0
	vmovdqu YMMWORD PTR [rsp+48], ymm0
	vmovdqu YMMWORD PTR [rsp+16], ymm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+184]
21:
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
	mov r11d, 16
	test r11d, esp
	je 20f
	xor r11d, r11d
	lea rsp, [rsp-264]
	mov QWORD PTR [rsp+256], r11
	movdqu XMMWORD PTR [rsp+240], xmm0
	vmovdqu YMMWORD PTR [rsp+208], ymm0
	vmovdqu YMMWORD PTR [rsp+176], ymm0
	vmovdqu YMMWORD PTR [rsp+144], ymm0
	vmovdqu YMMWORD PTR [rsp+112], ymm0
	vmovdqu YMMWORD PTR [rsp+80], ymm0
	vmovdqu YMMWORD PTR [rsp+48], ymm0
	vmovdqu YMMWORD PTR [rsp+16], ymm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+264]
	jmp 21f
20:
	xor r11d, r11d
	lea rsp, [rsp-264]
	mov QWORD PTR [rsp+256], r11
	vmovdqu YMMWORD PTR [rsp+224], ymm0
	vmovdqu YMMWORD PTR [rsp+192], ymm0
	vmovdqu YMMWORD PTR [rsp+160], ymm0
	vmovdqu YMMWORD PTR [rsp+128], ymm0
	vmovdqu YMMWORD PTR [rsp+96], ymm0
	vmovdqu YMMWORD PTR [rsp+64], ymm0
	vmovdqu YMMWORD PTR [rsp+32], ymm0
	vmovdqu YMMWORD PTR [rsp], ymm0
	lea rsp, [rsp+264]
21:
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
	mov r11d, 16
	test r11d, esp
	je 20f
	xor r11d, r11d
	lea rsp, [rsp-1632]
	mov QWORD PTR [rsp+1624], r11
	movdqu XMMWORD PTR [rsp+1608], xmm0
	vmovdqu YMMWORD PTR [rsp+1576], ymm0
	vmovdqu YMMWORD PTR [rsp+1544], ymm0
	vmovdqu YMMWORD PTR [rsp+1512], ymm0
	vmovdqu YMMWORD PTR [rsp+1480], ymm0
	vmovdqu YMMWORD PTR [rsp+1448], ymm0
	vmovdqu YMMWORD PTR [rsp+1416], ymm0
	vmovdqu YMMWORD PTR [rsp+1384], ymm0
	vmovdqu YMMWORD PTR [rsp+1352], ymm0
	vmovdqu YMMWORD PTR [rsp+1320], ymm0
	vmovdqu YMMWORD PTR [rsp+1288], ymm0
	vmovdqu YMMWORD PTR [rsp+1256], ymm0
	vmovdqu YMMWORD PTR [rsp+1224], ymm0
	vmovdqu YMMWORD PTR [rsp+1192], ymm0
	vmovdqu YMMWORD PTR [rsp+1160], ymm0
	vmovdqu YMMWORD PTR [rsp+1128], ymm0
	vmovdqu YMMWORD PTR [rsp+1096], ymm0
	vmovdqu YMMWORD PTR [rsp+1064], ymm0
	vmovdqu YMMWORD PTR [rsp+1032], ymm0
	vmovdqu YMMWORD PTR [rsp+1000], ymm0
	vmovdqu YMMWORD PTR [rsp+968], ymm0
	vmovdqu YMMWORD PTR [rsp+936], ymm0
	vmovdqu YMMWORD PTR [rsp+904], ymm0
	vmovdqu YMMWORD PTR [rsp+872], ymm0
	vmovdqu YMMWORD PTR [rsp+840], ymm0
	vmovdqu YMMWORD PTR [rsp+808], ymm0
	vmovdqu YMMWORD PTR [rsp+776], ymm0
	vmovdqu YMMWORD PTR [rsp+744], ymm0
	vmovdqu YMMWORD PTR [rsp+712], ymm0
	vmovdqu YMMWORD PTR [rsp+680], ymm0
	vmovdqu YMMWORD PTR [rsp+648], ymm0
	vmovdqu YMMWORD PTR [rsp+616], ymm0
	vmovdqu YMMWORD PTR [rsp+584], ymm0
	vmovdqu YMMWORD PTR [rsp+552], ymm0
	vmovdqu YMMWORD PTR [rsp+520], ymm0
	vmovdqu YMMWORD PTR [rsp+488], ymm0
	vmovdqu YMMWORD PTR [rsp+456], ymm0
	vmovdqu YMMWORD PTR [rsp+424], ymm0
	vmovdqu YMMWORD PTR [rsp+392], ymm0
	vmovdqu YMMWORD PTR [rsp+360], ymm0
	vmovdqu YMMWORD PTR [rsp+328], ymm0
	vmovdqu YMMWORD PTR [rsp+296], ymm0
	vmovdqu YMMWORD PTR [rsp+264], ymm0
	vmovdqu YMMWORD PTR [rsp+232], ymm0
	vmovdqu YMMWORD PTR [rsp+200], ymm0
	vmovdqu YMMWORD PTR [rsp+168], ymm0
	vmovdqu YMMWORD PTR [rsp+136], ymm0
	vmovdqu YMMWORD PTR [rsp+104], ymm0
	vmovdqu YMMWORD PTR [rsp+72], ymm0
	vmovdqu YMMWORD PTR [rsp+40], ymm0
	vmovdqu YMMWORD PTR [rsp+8], ymm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+1632]
	jmp 21f
20:
	xor r11d, r11d
	lea rsp, [rsp-1632]
	mov QWORD PTR [rsp+1624], r11
	vmovdqu YMMWORD PTR [rsp+1592], ymm0
	vmovdqu YMMWORD PTR [rsp+1560], ymm0
	vmovdqu YMMWORD PTR [rsp+1528], ymm0
	vmovdqu YMMWORD PTR [rsp+1496], ymm0
	vmovdqu YMMWORD PTR [rsp+1464], ymm0
	vmovdqu YMMWORD PTR [rsp+1432], ymm0
	vmovdqu YMMWORD PTR [rsp+1400], ymm0
	vmovdqu YMMWORD PTR [rsp+1368], ymm0
	vmovdqu YMMWORD PTR [rsp+1336], ymm0
	vmovdqu YMMWORD PTR [rsp+1304], ymm0
	vmovdqu YMMWORD PTR [rsp+1272], ymm0
	vmovdqu YMMWORD PTR [rsp+1240], ymm0
	vmovdqu YMMWORD PTR [rsp+1208], ymm0
	vmovdqu YMMWORD PTR [rsp+1176], ymm0
	vmovdqu YMMWORD PTR [rsp+1144], ymm0
	vmovdqu YMMWORD PTR [rsp+1112], ymm0
	vmovdqu YMMWORD PTR [rsp+1080], ymm0
	vmovdqu YMMWORD PTR [rsp+1048], ymm0
	vmovdqu YMMWORD PTR [rsp+1016], ymm0
	vmovdqu YMMWORD PTR [rsp+984], ymm0
	vmovdqu YMMWORD PTR [rsp+952], ymm0
	vmovdqu YMMWORD PTR [rsp+920], ymm0
	vmovdqu YMMWORD PTR [rsp+888], ymm0
	vmovdqu YMMWORD PTR [rsp+856], ymm0
	vmovdqu YMMWORD PTR [rsp+824], ymm0
	vmovdqu YMMWORD PTR [rsp+792], ymm0
	vmovdqu YMMWORD PTR [rsp+760], ymm0
	vmovdqu YMMWORD PTR [rsp+728], ymm0
	vmovdqu YMMWORD PTR [rsp+696], ymm0
	vmovdqu YMMWORD PTR [rsp+664], ymm0
	vmovdqu YMMWORD PTR [rsp+632], ymm0
	vmovdqu YMMWORD PTR [rsp+600], ymm0
	vmovdqu YMMWORD PTR [rsp+568], ymm0
	vmovdqu YMMWORD PTR [rsp+536], ymm0
	vmovdqu YMMWORD PTR [rsp+504], ymm0
	vmovdqu YMMWORD PTR [rsp+472], ymm0
	vmovdqu YMMWORD PTR [rsp+440], ymm0
	vmovdqu YMMWORD PTR [rsp+408], ymm0
	vmovdqu YMMWORD PTR [rsp+376], ymm0
	vmovdqu YMMWORD PTR [rsp+344], ymm0
	vmovdqu YMMWORD PTR [rsp+312], ymm0
	vmovdqu YMMWORD PTR [rsp+280], ymm0
	vmovdqu YMMWORD PTR [rsp+248], ymm0
	vmovdqu YMMWORD PTR [rsp+216], ymm0
	vmovdqu YMMWORD PTR [rsp+184], ymm0
	vmovdqu YMMWORD PTR [rsp+152], ymm0
	vmovdqu YMMWORD PTR [rsp+120], ymm0
	vmovdqu YMMWORD PTR [rsp+88], ymm0
	vmovdqu YMMWORD PTR [rsp+56], ymm0
	vmovdqu YMMWORD PTR [rsp+24], ymm0
	movdqu XMMWORD PTR [rsp+8], xmm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+1632]
21:
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
	mov r11d, 16
	test r11d, esp
	je 20f
	xor r11d, r11d
	lea rsp, [rsp-184]
	mov QWORD PTR [rsp+176], r11
	movdqu XMMWORD PTR [rsp+160], xmm0
	vmovdqu YMMWORD PTR [rsp+128], ymm0
	vmovdqu YMMWORD PTR [rsp+96], ymm0
	vmovdqu YMMWORD PTR [rsp+64], ymm0
	vmovdqu YMMWORD PTR [rsp+32], ymm0
	vmovdqu YMMWORD PTR [rsp], ymm0
	lea rsp, [rsp+184]
	jmp 21f
20:
	xor r11d, r11d
	lea rsp, [rsp-184]
	mov QWORD PTR [rsp+176], r11
	vmovdqu YMMWORD PTR [rsp+144], ymm0
	vmovdqu YMMWORD PTR [rsp+112], ymm0
	vmovdqu YMMWORD PTR [rsp+80], ymm0
	vmovdqu YMMWORD PTR [rsp+48], ymm0
	vmovdqu YMMWORD PTR [rsp+16], ymm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+184]
21:
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
	mov r11d, 16
	test r11d, esp
	je 20f
	xor r11d, r11d
	lea rsp, [rsp-264]
	mov QWORD PTR [rsp+256], r11
	movdqu XMMWORD PTR [rsp+240], xmm0
	vmovdqu YMMWORD PTR [rsp+208], ymm0
	vmovdqu YMMWORD PTR [rsp+176], ymm0
	vmovdqu YMMWORD PTR [rsp+144], ymm0
	vmovdqu YMMWORD PTR [rsp+112], ymm0
	vmovdqu YMMWORD PTR [rsp+80], ymm0
	vmovdqu YMMWORD PTR [rsp+48], ymm0
	vmovdqu YMMWORD PTR [rsp+16], ymm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+264]
	jmp 21f
20:
	xor r11d, r11d
	lea rsp, [rsp-264]
	mov QWORD PTR [rsp+256], r11
	vmovdqu YMMWORD PTR [rsp+224], ymm0
	vmovdqu YMMWORD PTR [rsp+192], ymm0
	vmovdqu YMMWORD PTR [rsp+160], ymm0
	vmovdqu YMMWORD PTR [rsp+128], ymm0
	vmovdqu YMMWORD PTR [rsp+96], ymm0
	vmovdqu YMMWORD PTR [rsp+64], ymm0
	vmovdqu YMMWORD PTR [rsp+32], ymm0
	vmovdqu YMMWORD PTR [rsp], ymm0
	lea rsp, [rsp+264]
21:
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
	mov r11d, 16
	test r11d, esp
	je 20f
	xor r11d, r11d
	lea rsp, [rsp-1632]
	mov QWORD PTR [rsp+1624], r11
	movdqu XMMWORD PTR [rsp+1608], xmm0
	vmovdqu YMMWORD PTR [rsp+1576], ymm0
	vmovdqu YMMWORD PTR [rsp+1544], ymm0
	vmovdqu YMMWORD PTR [rsp+1512], ymm0
	vmovdqu YMMWORD PTR [rsp+1480], ymm0
	vmovdqu YMMWORD PTR [rsp+1448], ymm0
	vmovdqu YMMWORD PTR [rsp+1416], ymm0
	vmovdqu YMMWORD PTR [rsp+1384], ymm0
	vmovdqu YMMWORD PTR [rsp+1352], ymm0
	vmovdqu YMMWORD PTR [rsp+1320], ymm0
	vmovdqu YMMWORD PTR [rsp+1288], ymm0
	vmovdqu YMMWORD PTR [rsp+1256], ymm0
	vmovdqu YMMWORD PTR [rsp+1224], ymm0
	vmovdqu YMMWORD PTR [rsp+1192], ymm0
	vmovdqu YMMWORD PTR [rsp+1160], ymm0
	vmovdqu YMMWORD PTR [rsp+1128], ymm0
	vmovdqu YMMWORD PTR [rsp+1096], ymm0
	vmovdqu YMMWORD PTR [rsp+1064], ymm0
	vmovdqu YMMWORD PTR [rsp+1032], ymm0
	vmovdqu YMMWORD PTR [rsp+1000], ymm0
	vmovdqu YMMWORD PTR [rsp+968], ymm0
	vmovdqu YMMWORD PTR [rsp+936], ymm0
	vmovdqu YMMWORD PTR [rsp+904], ymm0
	vmovdqu YMMWORD PTR [rsp+872], ymm0
	vmovdqu YMMWORD PTR [rsp+840], ymm0
	vmovdqu YMMWORD PTR [rsp+808], ymm0
	vmovdqu YMMWORD PTR [rsp+776], ymm0
	vmovdqu YMMWORD PTR [rsp+744], ymm0
	vmovdqu YMMWORD PTR [rsp+712], ymm0
	vmovdqu YMMWORD PTR [rsp+680], ymm0
	vmovdqu YMMWORD PTR [rsp+648], ymm0
	vmovdqu YMMWORD PTR [rsp+616], ymm0
	vmovdqu YMMWORD PTR [rsp+584], ymm0
	vmovdqu YMMWORD PTR [rsp+552], ymm0
	vmovdqu YMMWORD PTR [rsp+520], ymm0
	vmovdqu YMMWORD PTR [rsp+488], ymm0
	vmovdqu YMMWORD PTR [rsp+456], ymm0
	vmovdqu YMMWORD PTR [rsp+424], ymm0
	vmovdqu YMMWORD PTR [rsp+392], ymm0
	vmovdqu YMMWORD PTR [rsp+360], ymm0
	vmovdqu YMMWORD PTR [rsp+328], ymm0
	vmovdqu YMMWORD PTR [rsp+296], ymm0
	vmovdqu YMMWORD PTR [rsp+264], ymm0
	vmovdqu YMMWORD PTR [rsp+232], ymm0
	vmovdqu YMMWORD PTR [rsp+200], ymm0
	vmovdqu YMMWORD PTR [rsp+168], ymm0
	vmovdqu YMMWORD PTR [rsp+136], ymm0
	vmovdqu YMMWORD PTR [rsp+104], ymm0
	vmovdqu YMMWORD PTR [rsp+72], ymm0
	vmovdqu YMMWORD PTR [rsp+40], ymm0
	vmovdqu YMMWORD PTR [rsp+8], ymm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+1632]
	jmp 21f
20:
	xor r11d, r11d
	lea rsp, [rsp-1632]
	mov QWORD PTR [rsp+1624], r11
	vmovdqu YMMWORD PTR [rsp+1592], ymm0
	vmovdqu YMMWORD PTR [rsp+1560], ymm0
	vmovdqu YMMWORD PTR [rsp+1528], ymm0
	vmovdqu YMMWORD PTR [rsp+1496], ymm0
	vmovdqu YMMWORD PTR [rsp+1464], ymm0
	vmovdqu YMMWORD PTR [rsp+1432], ymm0
	vmovdqu YMMWORD PTR [rsp+1400], ymm0
	vmovdqu YMMWORD PTR [rsp+1368], ymm0
	vmovdqu YMMWORD PTR [rsp+1336], ymm0
	vmovdqu YMMWORD PTR [rsp+1304], ymm0
	vmovdqu YMMWORD PTR [rsp+1272], ymm0
	vmovdqu YMMWORD PTR [rsp+1240], ymm0
	vmovdqu YMMWORD PTR [rsp+1208], ymm0
	vmovdqu YMMWORD PTR [rsp+1176], ymm0
	vmovdqu YMMWORD PTR [rsp+1144], ymm0
	vmovdqu YMMWORD PTR [rsp+1112], ymm0
	vmovdqu YMMWORD PTR [rsp+1080], ymm0
	vmovdqu YMMWORD PTR [rsp+1048], ymm0
	vmovdqu YMMWORD PTR [rsp+1016], ymm0
	vmovdqu YMMWORD PTR [rsp+984], ymm0
	vmovdqu YMMWORD PTR [rsp+952], ymm0
	vmovdqu YMMWORD PTR [rsp+920], ymm0
	vmovdqu YMMWORD PTR [rsp+888], ymm0
	vmovdqu YMMWORD PTR [rsp+856], ymm0
	vmovdqu YMMWORD PTR [rsp+824], ymm0
	vmovdqu YMMWORD PTR [rsp+792], ymm0
	vmovdqu YMMWORD PTR [rsp+760], ymm0
	vmovdqu YMMWORD PTR [rsp+728], ymm0
	vmovdqu YMMWORD PTR [rsp+696], ymm0
	vmovdqu YMMWORD PTR [rsp+664], ymm0
	vmovdqu YMMWORD PTR [rsp+632], ymm0
	vmovdqu YMMWORD PTR [rsp+600], ymm0
	vmovdqu YMMWORD PTR [rsp+568], ymm0
	vmovdqu YMMWORD PTR [rsp+536], ymm0
	vmovdqu YMMWORD PTR [rsp+504], ymm0
	vmovdqu YMMWORD PTR [rsp+472], ymm0
	vmovdqu YMMWORD PTR [rsp+440], ymm0
	vmovdqu YMMWORD PTR [rsp+408], ymm0
	vmovdqu YMMWORD PTR [rsp+376], ymm0
	vmovdqu YMMWORD PTR [rsp+344], ymm0
	vmovdqu YMMWORD PTR [rsp+312], ymm0
	vmovdqu YMMWORD PTR [rsp+280], ymm0
	vmovdqu YMMWORD PTR [rsp+248], ymm0
	vmovdqu YMMWORD PTR [rsp+216], ymm0
	vmovdqu YMMWORD PTR [rsp+184], ymm0
	vmovdqu YMMWORD PTR [rsp+152], ymm0
	vmovdqu YMMWORD PTR [rsp+120], ymm0
	vmovdqu YMMWORD PTR [rsp+88], ymm0
	vmovdqu YMMWORD PTR [rsp+56], ymm0
	vmovdqu YMMWORD PTR [rsp+24], ymm0
	movdqu XMMWORD PTR [rsp+8], xmm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+1632]
21:
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
	je 20f
	xor r11d, r11d
	lea rsp, [rsp-184]
	mov QWORD PTR [rsp+176], r11
	movdqu XMMWORD PTR [rsp+160], xmm0
	vmovdqu YMMWORD PTR [rsp+128], ymm0
	vmovdqu YMMWORD PTR [rsp+96], ymm0
	vmovdqu YMMWORD PTR [rsp+64], ymm0
	vmovdqu YMMWORD PTR [rsp+32], ymm0
	vmovdqu YMMWORD PTR [rsp], ymm0
	lea rsp, [rsp+184]
	jmp 21f
20:
	xor r11d, r11d
	lea rsp, [rsp-184]
	mov QWORD PTR [rsp+176], r11
	vmovdqu YMMWORD PTR [rsp+144], ymm0
	vmovdqu YMMWORD PTR [rsp+112], ymm0
	vmovdqu YMMWORD PTR [rsp+80], ymm0
	vmovdqu YMMWORD PTR [rsp+48], ymm0
	vmovdqu YMMWORD PTR [rsp+16], ymm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+184]
21:
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
	xor r11d, r11d
	mov r11d, 16
	test r11d, esp
	je 20f
	xor r11d, r11d
	lea rsp, [rsp-264]
	mov QWORD PTR [rsp+256], r11
	movdqu XMMWORD PTR [rsp+240], xmm0
	vmovdqu YMMWORD PTR [rsp+208], ymm0
	vmovdqu YMMWORD PTR [rsp+176], ymm0
	vmovdqu YMMWORD PTR [rsp+144], ymm0
	vmovdqu YMMWORD PTR [rsp+112], ymm0
	vmovdqu YMMWORD PTR [rsp+80], ymm0
	vmovdqu YMMWORD PTR [rsp+48], ymm0
	vmovdqu YMMWORD PTR [rsp+16], ymm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+264]
	jmp 21f
20:
	xor r11d, r11d
	lea rsp, [rsp-264]
	mov QWORD PTR [rsp+256], r11
	vmovdqu YMMWORD PTR [rsp+224], ymm0
	vmovdqu YMMWORD PTR [rsp+192], ymm0
	vmovdqu YMMWORD PTR [rsp+160], ymm0
	vmovdqu YMMWORD PTR [rsp+128], ymm0
	vmovdqu YMMWORD PTR [rsp+96], ymm0
	vmovdqu YMMWORD PTR [rsp+64], ymm0
	vmovdqu YMMWORD PTR [rsp+32], ymm0
	vmovdqu YMMWORD PTR [rsp], ymm0
	lea rsp, [rsp+264]
21:
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
	xor r11d, r11d
	mov r11d, 16
	test r11d, esp
	je 20f
	xor r11d, r11d
	lea rsp, [rsp-1632]
	mov QWORD PTR [rsp+1624], r11
	movdqu XMMWORD PTR [rsp+1608], xmm0
	vmovdqu YMMWORD PTR [rsp+1576], ymm0
	vmovdqu YMMWORD PTR [rsp+1544], ymm0
	vmovdqu YMMWORD PTR [rsp+1512], ymm0
	vmovdqu YMMWORD PTR [rsp+1480], ymm0
	vmovdqu YMMWORD PTR [rsp+1448], ymm0
	vmovdqu YMMWORD PTR [rsp+1416], ymm0
	vmovdqu YMMWORD PTR [rsp+1384], ymm0
	vmovdqu YMMWORD PTR [rsp+1352], ymm0
	vmovdqu YMMWORD PTR [rsp+1320], ymm0
	vmovdqu YMMWORD PTR [rsp+1288], ymm0
	vmovdqu YMMWORD PTR [rsp+1256], ymm0
	vmovdqu YMMWORD PTR [rsp+1224], ymm0
	vmovdqu YMMWORD PTR [rsp+1192], ymm0
	vmovdqu YMMWORD PTR [rsp+1160], ymm0
	vmovdqu YMMWORD PTR [rsp+1128], ymm0
	vmovdqu YMMWORD PTR [rsp+1096], ymm0
	vmovdqu YMMWORD PTR [rsp+1064], ymm0
	vmovdqu YMMWORD PTR [rsp+1032], ymm0
	vmovdqu YMMWORD PTR [rsp+1000], ymm0
	vmovdqu YMMWORD PTR [rsp+968], ymm0
	vmovdqu YMMWORD PTR [rsp+936], ymm0
	vmovdqu YMMWORD PTR [rsp+904], ymm0
	vmovdqu YMMWORD PTR [rsp+872], ymm0
	vmovdqu YMMWORD PTR [rsp+840], ymm0
	vmovdqu YMMWORD PTR [rsp+808], ymm0
	vmovdqu YMMWORD PTR [rsp+776], ymm0
	vmovdqu YMMWORD PTR [rsp+744], ymm0
	vmovdqu YMMWORD PTR [rsp+712], ymm0
	vmovdqu YMMWORD PTR [rsp+680], ymm0
	vmovdqu YMMWORD PTR [rsp+648], ymm0
	vmovdqu YMMWORD PTR [rsp+616], ymm0
	vmovdqu YMMWORD PTR [rsp+584], ymm0
	vmovdqu YMMWORD PTR [rsp+552], ymm0
	vmovdqu YMMWORD PTR [rsp+520], ymm0
	vmovdqu YMMWORD PTR [rsp+488], ymm0
	vmovdqu YMMWORD PTR [rsp+456], ymm0
	vmovdqu YMMWORD PTR [rsp+424], ymm0
	vmovdqu YMMWORD PTR [rsp+392], ymm0
	vmovdqu YMMWORD PTR [rsp+360], ymm0
	vmovdqu YMMWORD PTR [rsp+328], ymm0
	vmovdqu YMMWORD PTR [rsp+296], ymm0
	vmovdqu YMMWORD PTR [rsp+264], ymm0
	vmovdqu YMMWORD PTR [rsp+232], ymm0
	vmovdqu YMMWORD PTR [rsp+200], ymm0
	vmovdqu YMMWORD PTR [rsp+168], ymm0
	vmovdqu YMMWORD PTR [rsp+136], ymm0
	vmovdqu YMMWORD PTR [rsp+104], ymm0
	vmovdqu YMMWORD PTR [rsp+72], ymm0
	vmovdqu YMMWORD PTR [rsp+40], ymm0
	vmovdqu YMMWORD PTR [rsp+8], ymm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+1632]
	jmp 21f
20:
	xor r11d, r11d
	lea rsp, [rsp-1632]
	mov QWORD PTR [rsp+1624], r11
	vmovdqu YMMWORD PTR [rsp+1592], ymm0
	vmovdqu YMMWORD PTR [rsp+1560], ymm0
	vmovdqu YMMWORD PTR [rsp+1528], ymm0
	vmovdqu YMMWORD PTR [rsp+1496], ymm0
	vmovdqu YMMWORD PTR [rsp+1464], ymm0
	vmovdqu YMMWORD PTR [rsp+1432], ymm0
	vmovdqu YMMWORD PTR [rsp+1400], ymm0
	vmovdqu YMMWORD PTR [rsp+1368], ymm0
	vmovdqu YMMWORD PTR [rsp+1336], ymm0
	vmovdqu YMMWORD PTR [rsp+1304], ymm0
	vmovdqu YMMWORD PTR [rsp+1272], ymm0
	vmovdqu YMMWORD PTR [rsp+1240], ymm0
	vmovdqu YMMWORD PTR [rsp+1208], ymm0
	vmovdqu YMMWORD PTR [rsp+1176], ymm0
	vmovdqu YMMWORD PTR [rsp+1144], ymm0
	vmovdqu YMMWORD PTR [rsp+1112], ymm0
	vmovdqu YMMWORD PTR [rsp+1080], ymm0
	vmovdqu YMMWORD PTR [rsp+1048], ymm0
	vmovdqu YMMWORD PTR [rsp+1016], ymm0
	vmovdqu YMMWORD PTR [rsp+984], ymm0
	vmovdqu YMMWORD PTR [rsp+952], ymm0
	vmovdqu YMMWORD PTR [rsp+920], ymm0
	vmovdqu YMMWORD PTR [rsp+888], ymm0
	vmovdqu YMMWORD PTR [rsp+856], ymm0
	vmovdqu YMMWORD PTR [rsp+824], ymm0
	vmovdqu YMMWORD PTR [rsp+792], ymm0
	vmovdqu YMMWORD PTR [rsp+760], ymm0
	vmovdqu YMMWORD PTR [rsp+728], ymm0
	vmovdqu YMMWORD PTR [rsp+696], ymm0
	vmovdqu YMMWORD PTR [rsp+664], ymm0
	vmovdqu YMMWORD PTR [rsp+632], ymm0
	vmovdqu YMMWORD PTR [rsp+600], ymm0
	vmovdqu YMMWORD PTR [rsp+568], ymm0
	vmovdqu YMMWORD PTR [rsp+536], ymm0
	vmovdqu YMMWORD PTR [rsp+504], ymm0
	vmovdqu YMMWORD PTR [rsp+472], ymm0
	vmovdqu YMMWORD PTR [rsp+440], ymm0
	vmovdqu YMMWORD PTR [rsp+408], ymm0
	vmovdqu YMMWORD PTR [rsp+376], ymm0
	vmovdqu YMMWORD PTR [rsp+344], ymm0
	vmovdqu YMMWORD PTR [rsp+312], ymm0
	vmovdqu YMMWORD PTR [rsp+280], ymm0
	vmovdqu YMMWORD PTR [rsp+248], ymm0
	vmovdqu YMMWORD PTR [rsp+216], ymm0
	vmovdqu YMMWORD PTR [rsp+184], ymm0
	vmovdqu YMMWORD PTR [rsp+152], ymm0
	vmovdqu YMMWORD PTR [rsp+120], ymm0
	vmovdqu YMMWORD PTR [rsp+88], ymm0
	vmovdqu YMMWORD PTR [rsp+56], ymm0
	vmovdqu YMMWORD PTR [rsp+24], ymm0
	movdqu XMMWORD PTR [rsp+8], xmm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+1632]
21:
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
	mov QWORD PTR [rsp+176], r11
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
	mov r11d, 16
	test r11d, esp
	je 20f
	xor r11d, r11d
	lea rsp, [rsp-264]
	mov QWORD PTR [rsp+256], r11
	movdqu XMMWORD PTR [rsp+240], xmm0
	vmovdqu YMMWORD PTR [rsp+208], ymm0
	vmovdqu YMMWORD PTR [rsp+176], ymm0
	vmovdqu YMMWORD PTR [rsp+144], ymm0
	vmovdqu YMMWORD PTR [rsp+112], ymm0
	vmovdqu YMMWORD PTR [rsp+80], ymm0
	vmovdqu YMMWORD PTR [rsp+48], ymm0
	vmovdqu YMMWORD PTR [rsp+16], ymm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+264]
	jmp 21f
20:
	xor r11d, r11d
	lea rsp, [rsp-264]
	mov QWORD PTR [rsp+256], r11
	vmovdqu YMMWORD PTR [rsp+224], ymm0
	vmovdqu YMMWORD PTR [rsp+192], ymm0
	vmovdqu YMMWORD PTR [rsp+160], ymm0
	vmovdqu YMMWORD PTR [rsp+128], ymm0
	vmovdqu YMMWORD PTR [rsp+96], ymm0
	vmovdqu YMMWORD PTR [rsp+64], ymm0
	vmovdqu YMMWORD PTR [rsp+32], ymm0
	vmovdqu YMMWORD PTR [rsp], ymm0
	lea rsp, [rsp+264]
21:
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
	mov r11d, 16
	test r11d, esp
	je 20f
	xor r11d, r11d
	lea rsp, [rsp-1632]
	mov QWORD PTR [rsp+1624], r11
	movdqu XMMWORD PTR [rsp+1608], xmm0
	vmovdqu YMMWORD PTR [rsp+1576], ymm0
	vmovdqu YMMWORD PTR [rsp+1544], ymm0
	vmovdqu YMMWORD PTR [rsp+1512], ymm0
	vmovdqu YMMWORD PTR [rsp+1480], ymm0
	vmovdqu YMMWORD PTR [rsp+1448], ymm0
	vmovdqu YMMWORD PTR [rsp+1416], ymm0
	vmovdqu YMMWORD PTR [rsp+1384], ymm0
	vmovdqu YMMWORD PTR [rsp+1352], ymm0
	vmovdqu YMMWORD PTR [rsp+1320], ymm0
	vmovdqu YMMWORD PTR [rsp+1288], ymm0
	vmovdqu YMMWORD PTR [rsp+1256], ymm0
	vmovdqu YMMWORD PTR [rsp+1224], ymm0
	vmovdqu YMMWORD PTR [rsp+1192], ymm0
	vmovdqu YMMWORD PTR [rsp+1160], ymm0
	vmovdqu YMMWORD PTR [rsp+1128], ymm0
	vmovdqu YMMWORD PTR [rsp+1096], ymm0
	vmovdqu YMMWORD PTR [rsp+1064], ymm0
	vmovdqu YMMWORD PTR [rsp+1032], ymm0
	vmovdqu YMMWORD PTR [rsp+1000], ymm0
	vmovdqu YMMWORD PTR [rsp+968], ymm0
	vmovdqu YMMWORD PTR [rsp+936], ymm0
	vmovdqu YMMWORD PTR [rsp+904], ymm0
	vmovdqu YMMWORD PTR [rsp+872], ymm0
	vmovdqu YMMWORD PTR [rsp+840], ymm0
	vmovdqu YMMWORD PTR [rsp+808], ymm0
	vmovdqu YMMWORD PTR [rsp+776], ymm0
	vmovdqu YMMWORD PTR [rsp+744], ymm0
	vmovdqu YMMWORD PTR [rsp+712], ymm0
	vmovdqu YMMWORD PTR [rsp+680], ymm0
	vmovdqu YMMWORD PTR [rsp+648], ymm0
	vmovdqu YMMWORD PTR [rsp+616], ymm0
	vmovdqu YMMWORD PTR [rsp+584], ymm0
	vmovdqu YMMWORD PTR [rsp+552], ymm0
	vmovdqu YMMWORD PTR [rsp+520], ymm0
	vmovdqu YMMWORD PTR [rsp+488], ymm0
	vmovdqu YMMWORD PTR [rsp+456], ymm0
	vmovdqu YMMWORD PTR [rsp+424], ymm0
	vmovdqu YMMWORD PTR [rsp+392], ymm0
	vmovdqu YMMWORD PTR [rsp+360], ymm0
	vmovdqu YMMWORD PTR [rsp+328], ymm0
	vmovdqu YMMWORD PTR [rsp+296], ymm0
	vmovdqu YMMWORD PTR [rsp+264], ymm0
	vmovdqu YMMWORD PTR [rsp+232], ymm0
	vmovdqu YMMWORD PTR [rsp+200], ymm0
	vmovdqu YMMWORD PTR [rsp+168], ymm0
	vmovdqu YMMWORD PTR [rsp+136], ymm0
	vmovdqu YMMWORD PTR [rsp+104], ymm0
	vmovdqu YMMWORD PTR [rsp+72], ymm0
	vmovdqu YMMWORD PTR [rsp+40], ymm0
	vmovdqu YMMWORD PTR [rsp+8], ymm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+1632]
	jmp 21f
20:
	xor r11d, r11d
	lea rsp, [rsp-1632]
	mov QWORD PTR [rsp+1624], r11
	vmovdqu YMMWORD PTR [rsp+1592], ymm0
	vmovdqu YMMWORD PTR [rsp+1560], ymm0
	vmovdqu YMMWORD PTR [rsp+1528], ymm0
	vmovdqu YMMWORD PTR [rsp+1496], ymm0
	vmovdqu YMMWORD PTR [rsp+1464], ymm0
	vmovdqu YMMWORD PTR [rsp+1432], ymm0
	vmovdqu YMMWORD PTR [rsp+1400], ymm0
	vmovdqu YMMWORD PTR [rsp+1368], ymm0
	vmovdqu YMMWORD PTR [rsp+1336], ymm0
	vmovdqu YMMWORD PTR [rsp+1304], ymm0
	vmovdqu YMMWORD PTR [rsp+1272], ymm0
	vmovdqu YMMWORD PTR [rsp+1240], ymm0
	vmovdqu YMMWORD PTR [rsp+1208], ymm0
	vmovdqu YMMWORD PTR [rsp+1176], ymm0
	vmovdqu YMMWORD PTR [rsp+1144], ymm0
	vmovdqu YMMWORD PTR [rsp+1112], ymm0
	vmovdqu YMMWORD PTR [rsp+1080], ymm0
	vmovdqu YMMWORD PTR [rsp+1048], ymm0
	vmovdqu YMMWORD PTR [rsp+1016], ymm0
	vmovdqu YMMWORD PTR [rsp+984], ymm0
	vmovdqu YMMWORD PTR [rsp+952], ymm0
	vmovdqu YMMWORD PTR [rsp+920], ymm0
	vmovdqu YMMWORD PTR [rsp+888], ymm0
	vmovdqu YMMWORD PTR [rsp+856], ymm0
	vmovdqu YMMWORD PTR [rsp+824], ymm0
	vmovdqu YMMWORD PTR [rsp+792], ymm0
	vmovdqu YMMWORD PTR [rsp+760], ymm0
	vmovdqu YMMWORD PTR [rsp+728], ymm0
	vmovdqu YMMWORD PTR [rsp+696], ymm0
	vmovdqu YMMWORD PTR [rsp+664], ymm0
	vmovdqu YMMWORD PTR [rsp+632], ymm0
	vmovdqu YMMWORD PTR [rsp+600], ymm0
	vmovdqu YMMWORD PTR [rsp+568], ymm0
	vmovdqu YMMWORD PTR [rsp+536], ymm0
	vmovdqu YMMWORD PTR [rsp+504], ymm0
	vmovdqu YMMWORD PTR [rsp+472], ymm0
	vmovdqu YMMWORD PTR [rsp+440], ymm0
	vmovdqu YMMWORD PTR [rsp+408], ymm0
	vmovdqu YMMWORD PTR [rsp+376], ymm0
	vmovdqu YMMWORD PTR [rsp+344], ymm0
	vmovdqu YMMWORD PTR [rsp+312], ymm0
	vmovdqu YMMWORD PTR [rsp+280], ymm0
	vmovdqu YMMWORD PTR [rsp+248], ymm0
	vmovdqu YMMWORD PTR [rsp+216], ymm0
	vmovdqu YMMWORD PTR [rsp+184], ymm0
	vmovdqu YMMWORD PTR [rsp+152], ymm0
	vmovdqu YMMWORD PTR [rsp+120], ymm0
	vmovdqu YMMWORD PTR [rsp+88], ymm0
	vmovdqu YMMWORD PTR [rsp+56], ymm0
	vmovdqu YMMWORD PTR [rsp+24], ymm0
	movdqu XMMWORD PTR [rsp+8], xmm0
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+1632]
21:
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
	mov QWORD PTR [rsp+176], r11
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
	mov QWORD PTR [rsp+256], r11
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
	mov QWORD PTR [rsp+1624], r11
	movdqu XMMWORD PTR [rsp+1608], xmm0
	movdqu XMMWORD PTR [rsp+1592], xmm0
	movdqu XMMWORD PTR [rsp+1576], xmm0
	movdqu XMMWORD PTR [rsp+1560], xmm0
	movdqu XMMWORD PTR [rsp+1544], xmm0
	movdqu XMMWORD PTR [rsp+1528], xmm0
	movdqu XMMWORD PTR [rsp+1512], xmm0
	movdqu XMMWORD PTR [rsp+1496], xmm0
	movdqu XMMWORD PTR [rsp+1480], xmm0
	movdqu XMMWORD PTR [rsp+1464], xmm0
	movdqu XMMWORD PTR [rsp+1448], xmm0
	movdqu XMMWORD PTR [rsp+1432], xmm0
	movdqu XMMWORD PTR [rsp+1416], xmm0
	movdqu XMMWORD PTR [rsp+1400], xmm0
	movdqu XMMWORD PTR [rsp+1384], xmm0
	movdqu XMMWORD PTR [rsp+1368], xmm0
	movdqu XMMWORD PTR [rsp+1352], xmm0
	movdqu XMMWORD PTR [rsp+1336], xmm0
	movdqu XMMWORD PTR [rsp+1320], xmm0
	movdqu XMMWORD PTR [rsp+1304], xmm0
	movdqu XMMWORD PTR [rsp+1288], xmm0
	movdqu XMMWORD PTR [rsp+1272], xmm0
	movdqu XMMWORD PTR [rsp+1256], xmm0
	movdqu XMMWORD PTR [rsp+1240], xmm0
	movdqu XMMWORD PTR [rsp+1224], xmm0
	movdqu XMMWORD PTR [rsp+1208], xmm0
	movdqu XMMWORD PTR [rsp+1192], xmm0
	movdqu XMMWORD PTR [rsp+1176], xmm0
	movdqu XMMWORD PTR [rsp+1160], xmm0
	movdqu XMMWORD PTR [rsp+1144], xmm0
	movdqu XMMWORD PTR [rsp+1128], xmm0
	movdqu XMMWORD PTR [rsp+1112], xmm0
	movdqu XMMWORD PTR [rsp+1096], xmm0
	movdqu XMMWORD PTR [rsp+1080], xmm0
	movdqu XMMWORD PTR [rsp+1064], xmm0
	movdqu XMMWORD PTR [rsp+1048], xmm0
	movdqu XMMWORD PTR [rsp+1032], xmm0
	movdqu XMMWORD PTR [rsp+1016], xmm0
	movdqu XMMWORD PTR [rsp+1000], xmm0
	movdqu XMMWORD PTR [rsp+984], xmm0
	movdqu XMMWORD PTR [rsp+968], xmm0
	movdqu XMMWORD PTR [rsp+952], xmm0
	movdqu XMMWORD PTR [rsp+936], xmm0
	movdqu XMMWORD PTR [rsp+920], xmm0
	movdqu XMMWORD PTR [rsp+904], xmm0
	movdqu XMMWORD PTR [rsp+888], xmm0
	movdqu XMMWORD PTR [rsp+872], xmm0
	movdqu XMMWORD PTR [rsp+856], xmm0
	movdqu XMMWORD PTR [rsp+840], xmm0
	movdqu XMMWORD PTR [rsp+824], xmm0
	movdqu XMMWORD PTR [rsp+808], xmm0
	movdqu XMMWORD PTR [rsp+792], xmm0
	movdqu XMMWORD PTR [rsp+776], xmm0
	movdqu XMMWORD PTR [rsp+760], xmm0
	movdqu XMMWORD PTR [rsp+744], xmm0
	movdqu XMMWORD PTR [rsp+728], xmm0
	movdqu XMMWORD PTR [rsp+712], xmm0
	movdqu XMMWORD PTR [rsp+696], xmm0
	movdqu XMMWORD PTR [rsp+680], xmm0
	movdqu XMMWORD PTR [rsp+664], xmm0
	movdqu XMMWORD PTR [rsp+648], xmm0
	movdqu XMMWORD PTR [rsp+632], xmm0
	movdqu XMMWORD PTR [rsp+616], xmm0
	movdqu XMMWORD PTR [rsp+600], xmm0
	movdqu XMMWORD PTR [rsp+584], xmm0
	movdqu XMMWORD PTR [rsp+568], xmm0
	movdqu XMMWORD PTR [rsp+552], xmm0
	movdqu XMMWORD PTR [rsp+536], xmm0
	movdqu XMMWORD PTR [rsp+520], xmm0
	movdqu XMMWORD PTR [rsp+504], xmm0
	movdqu XMMWORD PTR [rsp+488], xmm0
	movdqu XMMWORD PTR [rsp+472], xmm0
	movdqu XMMWORD PTR [rsp+456], xmm0
	movdqu XMMWORD PTR [rsp+440], xmm0
	movdqu XMMWORD PTR [rsp+424], xmm0
	movdqu XMMWORD PTR [rsp+408], xmm0
	movdqu XMMWORD PTR [rsp+392], xmm0
	movdqu XMMWORD PTR [rsp+376], xmm0
	movdqu XMMWORD PTR [rsp+360], xmm0
	movdqu XMMWORD PTR [rsp+344], xmm0
	movdqu XMMWORD PTR [rsp+328], xmm0
	movdqu XMMWORD PTR [rsp+312], xmm0
	movdqu XMMWORD PTR [rsp+296], xmm0
	movdqu XMMWORD PTR [rsp+280], xmm0
	movdqu XMMWORD PTR [rsp+264], xmm0
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
