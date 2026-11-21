// The functions of `src/rsa_keygen.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_generate_init:
	mov r9d, 0
	mov r10d, 0
	test rcx, rcx
	je 20f
22:
	movzx eax, BYTE PTR [rdx]
	shl r9, 8
	add r9, rax
	mov rax, r9
	shr rax, 32
	or r10, rax
	mov r9d, r9d
	add rdx, 1
	sub rcx, 1
	jne 22b
	jmp 21f
20:
21:
	mov eax, 1
	mov r8d, 2
	cmp rsi, 512
	cmovb rax, r8
	cmp rsi, 8193
	cmovae rax, r8
	mov r8d, 0
	test r10, r10
	cmovne rax, r8
	mov r11, r9
	and r11, 1
	cmove rax, r8
	cmp r9, 1
	cmove rax, r8
	mov rcx, rsi
	shr rcx, 7
	shl rcx, 3
	mov rdx, rcx
	shl rdx, 3
	mov r11, rdx
	shl rdx, 2
	add rdx, r11
	mov r11, rcx
	shl r11, 6
	cmp r9, 3
	cmove rdx, r11
	mov rsi, rcx
	shl rsi, 15
	add rsi, rcx
	mov r8, rcx
	shl r8, 5
	mov r10d, 4
	bswap r9
	mov r11d, 0
	cmp rax, 1
	cmovne rcx, r11
	cmovne rdx, r11
	cmovne rsi, r11
	cmovne r8, r11
	cmovne r10, r11
	cmovne r9, r11
	mov QWORD PTR [rdi], rdx
	mov QWORD PTR [rdi+8], rcx
	mov QWORD PTR [rdi+16], rsi
	mov QWORD PTR [rdi+24], r8
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r10
	mov QWORD PTR [rdi+48], r9
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

vg_rsa_generate_ifma:
	lea rsp, [rsp-160]
	mov QWORD PTR [rsp+72], r12
	mov r12, rsp
	mov QWORD PTR [r12], rdi
	mov QWORD PTR [r12+16], rdx
	mov QWORD PTR [r12+24], rcx
	mov QWORD PTR [r12+32], r8
	mov QWORD PTR [r12+40], r9
	mov rax, QWORD PTR [rsp+168]
	mov QWORD PTR [r12+48], rax
	mov rax, QWORD PTR [rsp+176]
	mov QWORD PTR [r12+56], rax
	mov rcx, QWORD PTR [rax+8]
	mov r9, QWORD PTR [rax+48]
	mov QWORD PTR [r12+8], rcx
	mov edx, 0
	mov QWORD PTR [r12+64], rdx
	mov rdx, rcx
	shl rdx, 3
	mov r11, rdx
	shl rdx, 2
	add rdx, r11
	mov r11, rcx
	shl r11, 6
	movabs r8, 216172782113783808
	cmp r9, r8
	cmove rdx, r11
	mov QWORD PTR [r12+88], rdx
	mov rax, QWORD PTR [r12]
	mov QWORD PTR [r12+96], rax
	mov rcx, QWORD PTR [r12+8]
	shl rcx, 2
	mov QWORD PTR [r12+104], rcx
	mov rdi, r12
	mov rsi, QWORD PTR [rdi+96]
	mov rcx, QWORD PTR [rdi+104]
	mov eax, 0
20:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 20b
	mov rax, QWORD PTR [r12+8]
	mov rcx, rax
	shl rcx, 2
	add rax, rcx
	mov rcx, QWORD PTR [r12]
	add rax, rcx
	mov QWORD PTR [r12+96], rax
	mov rcx, QWORD PTR [r12+8]
	shl rcx, 2
	mov QWORD PTR [r12+104], rcx
	mov rdi, r12
	mov rsi, QWORD PTR [rdi+96]
	mov rcx, QWORD PTR [rdi+104]
	mov eax, 0
21:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 21b
22:
	lea rsp, [rsp-48]
	mov rax, QWORD PTR [r12+56]
	mov r10, QWORD PTR [rax+32]
	mov rsi, QWORD PTR [r12+8]
	mov r9, rsi
	shl r9, 2
	add r9, QWORD PTR [r12]
	mov rdi, r9
	add rdi, rsi
	mov r11d, 0
	test r10, r10
	cmove rdi, r9
	cmove rsi, r11
	mov QWORD PTR [rsp], rsi
	mov rsi, QWORD PTR [r12+8]
	mov rdx, QWORD PTR [r12+24]
	add rdx, QWORD PTR [r12+64]
	mov QWORD PTR [rsp+8], rdx
	mov rdx, QWORD PTR [r12+32]
	sub rdx, QWORD PTR [r12+64]
	mov QWORD PTR [rsp+16], rdx
	mov rdx, QWORD PTR [r12+40]
	mov QWORD PTR [rsp+24], rdx
	mov rdx, QWORD PTR [r12+48]
	mov QWORD PTR [rsp+32], rdx
	mov QWORD PTR [rsp+40], rax
	mov rdx, QWORD PTR [r12+16]
	mov rcx, rax
	add rcx, 48
	mov r8d, 8
	call {vg_rsa_prime_search_ifma}
	lea rsp, [rsp+48]
	mov eax, eax
	mov rcx, QWORD PTR [r12+16]
	mov rcx, QWORD PTR [rcx]
	mov rdx, QWORD PTR [r12+64]
	add rdx, rcx
	mov QWORD PTR [r12+64], rdx
	test rax, rax
	je 23f
	cmp rax, 3
	je 25f
	test rcx, rcx
	je 27f
	mov rax, QWORD PTR [r12+56]
	mov rcx, QWORD PTR [rax+32]
	test rcx, rcx
	je 29f
	lea rsp, [rsp-96]
	mov r9, QWORD PTR [r12+8]
	mov rdi, QWORD PTR [r12]
	mov rsi, r9
	shl rsi, 1
	mov rdx, rdi
	add rdx, rsi
	mov rcx, rsi
	mov r8, rdx
	add r8, rsi
	mov rax, r8
	add rax, r9
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], r9
	add rax, r9
	mov QWORD PTR [rsp+16], rax
	mov QWORD PTR [rsp+24], r9
	add rax, r9
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], r9
	add rax, r9
	mov QWORD PTR [rsp+48], rax
	mov QWORD PTR [rsp+56], r9
	mov rax, QWORD PTR [r12+56]
	add rax, 48
	mov QWORD PTR [rsp+64], rax
	mov eax, 8
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [r12+40]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [r12+48]
	mov QWORD PTR [rsp+88], rax
	call {vg_rsa_keygen_key}
	lea rsp, [rsp+96]
	mov eax, eax
	cmp rax, 1
	je 211f
	cmp rax, 2
	je 213f
	mov rax, QWORD PTR [r12]
	mov QWORD PTR [r12+96], rax
	mov rcx, QWORD PTR [r12+8]
	mov rdx, rcx
	shl rcx, 3
	add rcx, rdx
	mov QWORD PTR [r12+104], rcx
	mov rdi, r12
	mov rsi, QWORD PTR [rdi+96]
	mov rcx, QWORD PTR [rdi+104]
	mov eax, 0
215:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 215b
	mov rax, QWORD PTR [r12+56]
	mov ecx, 0
	mov QWORD PTR [rax+32], rcx
	mov QWORD PTR [rax+40], rcx
	mov ecx, 2
	mov QWORD PTR [r12+80], rcx
	jmp 214f
213:
	mov rax, QWORD PTR [r12+56]
	mov rcx, QWORD PTR [r12+88]
	mov QWORD PTR [rax], rcx
	mov ecx, 0
	mov QWORD PTR [rax+32], rcx
	mov ecx, 4
	mov QWORD PTR [r12+80], rcx
214:
	jmp 212f
211:
	mov rax, QWORD PTR [r12+56]
	mov ecx, 0
	mov QWORD PTR [rax+32], rcx
	mov QWORD PTR [rax+40], rcx
	mov ecx, 1
	mov QWORD PTR [r12+80], rcx
212:
	jmp 210f
29:
	mov rax, QWORD PTR [r12+56]
	mov rcx, QWORD PTR [r12+88]
	mov QWORD PTR [rax], rcx
	mov ecx, 1
	mov QWORD PTR [rax+32], rcx
	mov ecx, 4
	mov QWORD PTR [r12+80], rcx
210:
	jmp 28f
27:
	mov rax, QWORD PTR [r12]
	mov QWORD PTR [r12+96], rax
	mov rcx, QWORD PTR [r12+8]
	mov rdx, rcx
	shl rcx, 3
	add rcx, rdx
	mov QWORD PTR [r12+104], rcx
	mov rdi, r12
	mov rsi, QWORD PTR [rdi+96]
	mov rcx, QWORD PTR [rdi+104]
	mov eax, 0
216:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 216b
	mov rax, QWORD PTR [r12+56]
	mov ecx, 0
	mov QWORD PTR [rax+32], rcx
	mov QWORD PTR [rax+40], rcx
	mov ecx, 3
	mov QWORD PTR [r12+80], rcx
28:
	jmp 26f
25:
	mov rax, QWORD PTR [r12+56]
	mov rcx, QWORD PTR [rax+40]
	cmp rcx, 2
	jb 217f
	sub rcx, 1
	mov QWORD PTR [rax+40], rcx
	mov rax, QWORD PTR [r12+56]
	mov rcx, QWORD PTR [r12+88]
	mov QWORD PTR [rax], rcx
	mov ecx, 0
	mov QWORD PTR [rax+32], rcx
	mov ecx, 4
	mov QWORD PTR [r12+80], rcx
	jmp 218f
217:
	mov rax, QWORD PTR [r12]
	mov QWORD PTR [r12+96], rax
	mov rcx, QWORD PTR [r12+8]
	mov rdx, rcx
	shl rcx, 3
	add rcx, rdx
	mov QWORD PTR [r12+104], rcx
	mov rdi, r12
	mov rsi, QWORD PTR [rdi+96]
	mov rcx, QWORD PTR [rdi+104]
	mov eax, 0
219:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 219b
	mov rax, QWORD PTR [r12+56]
	mov ecx, 0
	mov QWORD PTR [rax+32], rcx
	mov QWORD PTR [rax+40], rcx
	mov ecx, 3
	mov QWORD PTR [r12+80], rcx
218:
26:
	jmp 24f
23:
	mov QWORD PTR [r12+80], rax
24:
	mov rax, QWORD PTR [r12+80]
	cmp rax, 4
	je 22b
	mov rax, QWORD PTR [r12+16]
	mov rcx, QWORD PTR [r12+64]
	mov QWORD PTR [rax], rcx
	mov rax, QWORD PTR [r12+80]
	mov r12, QWORD PTR [r12+72]
	lea rsp, [rsp+160]
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
	lea rsp, [rsp-8]
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp-544]
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
	lea rsp, [rsp+544]
	lea rsp, [rsp+8]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	ret
	.p2align 6

vg_rsa_generate_adx:
	lea rsp, [rsp-160]
	mov QWORD PTR [rsp+72], r12
	mov r12, rsp
	mov QWORD PTR [r12], rdi
	mov QWORD PTR [r12+16], rdx
	mov QWORD PTR [r12+24], rcx
	mov QWORD PTR [r12+32], r8
	mov QWORD PTR [r12+40], r9
	mov rax, QWORD PTR [rsp+168]
	mov QWORD PTR [r12+48], rax
	mov rax, QWORD PTR [rsp+176]
	mov QWORD PTR [r12+56], rax
	mov rcx, QWORD PTR [rax+8]
	mov r9, QWORD PTR [rax+48]
	mov QWORD PTR [r12+8], rcx
	mov edx, 0
	mov QWORD PTR [r12+64], rdx
	mov rdx, rcx
	shl rdx, 3
	mov r11, rdx
	shl rdx, 2
	add rdx, r11
	mov r11, rcx
	shl r11, 6
	movabs r8, 216172782113783808
	cmp r9, r8
	cmove rdx, r11
	mov QWORD PTR [r12+88], rdx
	mov rax, QWORD PTR [r12]
	mov QWORD PTR [r12+96], rax
	mov rcx, QWORD PTR [r12+8]
	shl rcx, 2
	mov QWORD PTR [r12+104], rcx
	mov rdi, r12
	mov rsi, QWORD PTR [rdi+96]
	mov rcx, QWORD PTR [rdi+104]
	mov eax, 0
20:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 20b
	mov rax, QWORD PTR [r12+8]
	mov rcx, rax
	shl rcx, 2
	add rax, rcx
	mov rcx, QWORD PTR [r12]
	add rax, rcx
	mov QWORD PTR [r12+96], rax
	mov rcx, QWORD PTR [r12+8]
	shl rcx, 2
	mov QWORD PTR [r12+104], rcx
	mov rdi, r12
	mov rsi, QWORD PTR [rdi+96]
	mov rcx, QWORD PTR [rdi+104]
	mov eax, 0
21:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 21b
22:
	lea rsp, [rsp-48]
	mov rax, QWORD PTR [r12+56]
	mov r10, QWORD PTR [rax+32]
	mov rsi, QWORD PTR [r12+8]
	mov r9, rsi
	shl r9, 2
	add r9, QWORD PTR [r12]
	mov rdi, r9
	add rdi, rsi
	mov r11d, 0
	test r10, r10
	cmove rdi, r9
	cmove rsi, r11
	mov QWORD PTR [rsp], rsi
	mov rsi, QWORD PTR [r12+8]
	mov rdx, QWORD PTR [r12+24]
	add rdx, QWORD PTR [r12+64]
	mov QWORD PTR [rsp+8], rdx
	mov rdx, QWORD PTR [r12+32]
	sub rdx, QWORD PTR [r12+64]
	mov QWORD PTR [rsp+16], rdx
	mov rdx, QWORD PTR [r12+40]
	mov QWORD PTR [rsp+24], rdx
	mov rdx, QWORD PTR [r12+48]
	mov QWORD PTR [rsp+32], rdx
	mov QWORD PTR [rsp+40], rax
	mov rdx, QWORD PTR [r12+16]
	mov rcx, rax
	add rcx, 48
	mov r8d, 8
	call {vg_rsa_prime_search_adx}
	lea rsp, [rsp+48]
	mov eax, eax
	mov rcx, QWORD PTR [r12+16]
	mov rcx, QWORD PTR [rcx]
	mov rdx, QWORD PTR [r12+64]
	add rdx, rcx
	mov QWORD PTR [r12+64], rdx
	test rax, rax
	je 23f
	cmp rax, 3
	je 25f
	test rcx, rcx
	je 27f
	mov rax, QWORD PTR [r12+56]
	mov rcx, QWORD PTR [rax+32]
	test rcx, rcx
	je 29f
	lea rsp, [rsp-96]
	mov r9, QWORD PTR [r12+8]
	mov rdi, QWORD PTR [r12]
	mov rsi, r9
	shl rsi, 1
	mov rdx, rdi
	add rdx, rsi
	mov rcx, rsi
	mov r8, rdx
	add r8, rsi
	mov rax, r8
	add rax, r9
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], r9
	add rax, r9
	mov QWORD PTR [rsp+16], rax
	mov QWORD PTR [rsp+24], r9
	add rax, r9
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], r9
	add rax, r9
	mov QWORD PTR [rsp+48], rax
	mov QWORD PTR [rsp+56], r9
	mov rax, QWORD PTR [r12+56]
	add rax, 48
	mov QWORD PTR [rsp+64], rax
	mov eax, 8
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [r12+40]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [r12+48]
	mov QWORD PTR [rsp+88], rax
	call {vg_rsa_keygen_key}
	lea rsp, [rsp+96]
	mov eax, eax
	cmp rax, 1
	je 211f
	cmp rax, 2
	je 213f
	mov rax, QWORD PTR [r12]
	mov QWORD PTR [r12+96], rax
	mov rcx, QWORD PTR [r12+8]
	mov rdx, rcx
	shl rcx, 3
	add rcx, rdx
	mov QWORD PTR [r12+104], rcx
	mov rdi, r12
	mov rsi, QWORD PTR [rdi+96]
	mov rcx, QWORD PTR [rdi+104]
	mov eax, 0
215:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 215b
	mov rax, QWORD PTR [r12+56]
	mov ecx, 0
	mov QWORD PTR [rax+32], rcx
	mov QWORD PTR [rax+40], rcx
	mov ecx, 2
	mov QWORD PTR [r12+80], rcx
	jmp 214f
213:
	mov rax, QWORD PTR [r12+56]
	mov rcx, QWORD PTR [r12+88]
	mov QWORD PTR [rax], rcx
	mov ecx, 0
	mov QWORD PTR [rax+32], rcx
	mov ecx, 4
	mov QWORD PTR [r12+80], rcx
214:
	jmp 212f
211:
	mov rax, QWORD PTR [r12+56]
	mov ecx, 0
	mov QWORD PTR [rax+32], rcx
	mov QWORD PTR [rax+40], rcx
	mov ecx, 1
	mov QWORD PTR [r12+80], rcx
212:
	jmp 210f
29:
	mov rax, QWORD PTR [r12+56]
	mov rcx, QWORD PTR [r12+88]
	mov QWORD PTR [rax], rcx
	mov ecx, 1
	mov QWORD PTR [rax+32], rcx
	mov ecx, 4
	mov QWORD PTR [r12+80], rcx
210:
	jmp 28f
27:
	mov rax, QWORD PTR [r12]
	mov QWORD PTR [r12+96], rax
	mov rcx, QWORD PTR [r12+8]
	mov rdx, rcx
	shl rcx, 3
	add rcx, rdx
	mov QWORD PTR [r12+104], rcx
	mov rdi, r12
	mov rsi, QWORD PTR [rdi+96]
	mov rcx, QWORD PTR [rdi+104]
	mov eax, 0
216:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 216b
	mov rax, QWORD PTR [r12+56]
	mov ecx, 0
	mov QWORD PTR [rax+32], rcx
	mov QWORD PTR [rax+40], rcx
	mov ecx, 3
	mov QWORD PTR [r12+80], rcx
28:
	jmp 26f
25:
	mov rax, QWORD PTR [r12+56]
	mov rcx, QWORD PTR [rax+40]
	cmp rcx, 2
	jb 217f
	sub rcx, 1
	mov QWORD PTR [rax+40], rcx
	mov rax, QWORD PTR [r12+56]
	mov rcx, QWORD PTR [r12+88]
	mov QWORD PTR [rax], rcx
	mov ecx, 0
	mov QWORD PTR [rax+32], rcx
	mov ecx, 4
	mov QWORD PTR [r12+80], rcx
	jmp 218f
217:
	mov rax, QWORD PTR [r12]
	mov QWORD PTR [r12+96], rax
	mov rcx, QWORD PTR [r12+8]
	mov rdx, rcx
	shl rcx, 3
	add rcx, rdx
	mov QWORD PTR [r12+104], rcx
	mov rdi, r12
	mov rsi, QWORD PTR [rdi+96]
	mov rcx, QWORD PTR [rdi+104]
	mov eax, 0
219:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 219b
	mov rax, QWORD PTR [r12+56]
	mov ecx, 0
	mov QWORD PTR [rax+32], rcx
	mov QWORD PTR [rax+40], rcx
	mov ecx, 3
	mov QWORD PTR [r12+80], rcx
218:
26:
	jmp 24f
23:
	mov QWORD PTR [r12+80], rax
24:
	mov rax, QWORD PTR [r12+80]
	cmp rax, 4
	je 22b
	mov rax, QWORD PTR [r12+16]
	mov rcx, QWORD PTR [r12+64]
	mov QWORD PTR [rax], rcx
	mov rax, QWORD PTR [r12+80]
	mov r12, QWORD PTR [r12+72]
	lea rsp, [rsp+160]
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
	lea rsp, [rsp-8]
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp-544]
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
	lea rsp, [rsp+544]
	lea rsp, [rsp+8]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	ret
	.p2align 6

vg_rsa_generate:
	lea rsp, [rsp-160]
	mov QWORD PTR [rsp+72], r12
	mov r12, rsp
	mov QWORD PTR [r12], rdi
	mov QWORD PTR [r12+16], rdx
	mov QWORD PTR [r12+24], rcx
	mov QWORD PTR [r12+32], r8
	mov QWORD PTR [r12+40], r9
	mov rax, QWORD PTR [rsp+168]
	mov QWORD PTR [r12+48], rax
	mov rax, QWORD PTR [rsp+176]
	mov QWORD PTR [r12+56], rax
	mov rcx, QWORD PTR [rax+8]
	mov r9, QWORD PTR [rax+48]
	mov QWORD PTR [r12+8], rcx
	mov edx, 0
	mov QWORD PTR [r12+64], rdx
	mov rdx, rcx
	shl rdx, 3
	mov r11, rdx
	shl rdx, 2
	add rdx, r11
	mov r11, rcx
	shl r11, 6
	movabs r8, 216172782113783808
	cmp r9, r8
	cmove rdx, r11
	mov QWORD PTR [r12+88], rdx
	mov rax, QWORD PTR [r12]
	mov QWORD PTR [r12+96], rax
	mov rcx, QWORD PTR [r12+8]
	shl rcx, 2
	mov QWORD PTR [r12+104], rcx
	mov rdi, r12
	mov rsi, QWORD PTR [rdi+96]
	mov rcx, QWORD PTR [rdi+104]
	mov eax, 0
20:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 20b
	mov rax, QWORD PTR [r12+8]
	mov rcx, rax
	shl rcx, 2
	add rax, rcx
	mov rcx, QWORD PTR [r12]
	add rax, rcx
	mov QWORD PTR [r12+96], rax
	mov rcx, QWORD PTR [r12+8]
	shl rcx, 2
	mov QWORD PTR [r12+104], rcx
	mov rdi, r12
	mov rsi, QWORD PTR [rdi+96]
	mov rcx, QWORD PTR [rdi+104]
	mov eax, 0
21:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 21b
22:
	lea rsp, [rsp-48]
	mov rax, QWORD PTR [r12+56]
	mov r10, QWORD PTR [rax+32]
	mov rsi, QWORD PTR [r12+8]
	mov r9, rsi
	shl r9, 2
	add r9, QWORD PTR [r12]
	mov rdi, r9
	add rdi, rsi
	mov r11d, 0
	test r10, r10
	cmove rdi, r9
	cmove rsi, r11
	mov QWORD PTR [rsp], rsi
	mov rsi, QWORD PTR [r12+8]
	mov rdx, QWORD PTR [r12+24]
	add rdx, QWORD PTR [r12+64]
	mov QWORD PTR [rsp+8], rdx
	mov rdx, QWORD PTR [r12+32]
	sub rdx, QWORD PTR [r12+64]
	mov QWORD PTR [rsp+16], rdx
	mov rdx, QWORD PTR [r12+40]
	mov QWORD PTR [rsp+24], rdx
	mov rdx, QWORD PTR [r12+48]
	mov QWORD PTR [rsp+32], rdx
	mov QWORD PTR [rsp+40], rax
	mov rdx, QWORD PTR [r12+16]
	mov rcx, rax
	add rcx, 48
	mov r8d, 8
	call {vg_rsa_prime_search}
	lea rsp, [rsp+48]
	mov eax, eax
	mov rcx, QWORD PTR [r12+16]
	mov rcx, QWORD PTR [rcx]
	mov rdx, QWORD PTR [r12+64]
	add rdx, rcx
	mov QWORD PTR [r12+64], rdx
	test rax, rax
	je 23f
	cmp rax, 3
	je 25f
	test rcx, rcx
	je 27f
	mov rax, QWORD PTR [r12+56]
	mov rcx, QWORD PTR [rax+32]
	test rcx, rcx
	je 29f
	lea rsp, [rsp-96]
	mov r9, QWORD PTR [r12+8]
	mov rdi, QWORD PTR [r12]
	mov rsi, r9
	shl rsi, 1
	mov rdx, rdi
	add rdx, rsi
	mov rcx, rsi
	mov r8, rdx
	add r8, rsi
	mov rax, r8
	add rax, r9
	mov QWORD PTR [rsp], rax
	mov QWORD PTR [rsp+8], r9
	add rax, r9
	mov QWORD PTR [rsp+16], rax
	mov QWORD PTR [rsp+24], r9
	add rax, r9
	mov QWORD PTR [rsp+32], rax
	mov QWORD PTR [rsp+40], r9
	add rax, r9
	mov QWORD PTR [rsp+48], rax
	mov QWORD PTR [rsp+56], r9
	mov rax, QWORD PTR [r12+56]
	add rax, 48
	mov QWORD PTR [rsp+64], rax
	mov eax, 8
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [r12+40]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [r12+48]
	mov QWORD PTR [rsp+88], rax
	call {vg_rsa_keygen_key}
	lea rsp, [rsp+96]
	mov eax, eax
	cmp rax, 1
	je 211f
	cmp rax, 2
	je 213f
	mov rax, QWORD PTR [r12]
	mov QWORD PTR [r12+96], rax
	mov rcx, QWORD PTR [r12+8]
	mov rdx, rcx
	shl rcx, 3
	add rcx, rdx
	mov QWORD PTR [r12+104], rcx
	mov rdi, r12
	mov rsi, QWORD PTR [rdi+96]
	mov rcx, QWORD PTR [rdi+104]
	mov eax, 0
215:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 215b
	mov rax, QWORD PTR [r12+56]
	mov ecx, 0
	mov QWORD PTR [rax+32], rcx
	mov QWORD PTR [rax+40], rcx
	mov ecx, 2
	mov QWORD PTR [r12+80], rcx
	jmp 214f
213:
	mov rax, QWORD PTR [r12+56]
	mov rcx, QWORD PTR [r12+88]
	mov QWORD PTR [rax], rcx
	mov ecx, 0
	mov QWORD PTR [rax+32], rcx
	mov ecx, 4
	mov QWORD PTR [r12+80], rcx
214:
	jmp 212f
211:
	mov rax, QWORD PTR [r12+56]
	mov ecx, 0
	mov QWORD PTR [rax+32], rcx
	mov QWORD PTR [rax+40], rcx
	mov ecx, 1
	mov QWORD PTR [r12+80], rcx
212:
	jmp 210f
29:
	mov rax, QWORD PTR [r12+56]
	mov rcx, QWORD PTR [r12+88]
	mov QWORD PTR [rax], rcx
	mov ecx, 1
	mov QWORD PTR [rax+32], rcx
	mov ecx, 4
	mov QWORD PTR [r12+80], rcx
210:
	jmp 28f
27:
	mov rax, QWORD PTR [r12]
	mov QWORD PTR [r12+96], rax
	mov rcx, QWORD PTR [r12+8]
	mov rdx, rcx
	shl rcx, 3
	add rcx, rdx
	mov QWORD PTR [r12+104], rcx
	mov rdi, r12
	mov rsi, QWORD PTR [rdi+96]
	mov rcx, QWORD PTR [rdi+104]
	mov eax, 0
216:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 216b
	mov rax, QWORD PTR [r12+56]
	mov ecx, 0
	mov QWORD PTR [rax+32], rcx
	mov QWORD PTR [rax+40], rcx
	mov ecx, 3
	mov QWORD PTR [r12+80], rcx
28:
	jmp 26f
25:
	mov rax, QWORD PTR [r12+56]
	mov rcx, QWORD PTR [rax+40]
	cmp rcx, 2
	jb 217f
	sub rcx, 1
	mov QWORD PTR [rax+40], rcx
	mov rax, QWORD PTR [r12+56]
	mov rcx, QWORD PTR [r12+88]
	mov QWORD PTR [rax], rcx
	mov ecx, 0
	mov QWORD PTR [rax+32], rcx
	mov ecx, 4
	mov QWORD PTR [r12+80], rcx
	jmp 218f
217:
	mov rax, QWORD PTR [r12]
	mov QWORD PTR [r12+96], rax
	mov rcx, QWORD PTR [r12+8]
	mov rdx, rcx
	shl rcx, 3
	add rcx, rdx
	mov QWORD PTR [r12+104], rcx
	mov rdi, r12
	mov rsi, QWORD PTR [rdi+96]
	mov rcx, QWORD PTR [rdi+104]
	mov eax, 0
219:
	mov BYTE PTR [rsi], al
	add rsi, 1
	sub rcx, 1
	jne 219b
	mov rax, QWORD PTR [r12+56]
	mov ecx, 0
	mov QWORD PTR [rax+32], rcx
	mov QWORD PTR [rax+40], rcx
	mov ecx, 3
	mov QWORD PTR [r12+80], rcx
218:
26:
	jmp 24f
23:
	mov QWORD PTR [r12+80], rax
24:
	mov rax, QWORD PTR [r12+80]
	cmp rax, 4
	je 22b
	mov rax, QWORD PTR [r12+16]
	mov rcx, QWORD PTR [r12+64]
	mov QWORD PTR [rax], rcx
	mov rax, QWORD PTR [r12+80]
	mov r12, QWORD PTR [r12+72]
	lea rsp, [rsp+160]
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
	lea rsp, [rsp-8]
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp-544]
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
	lea rsp, [rsp+544]
	lea rsp, [rsp+8]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	ret
	.p2align 6
