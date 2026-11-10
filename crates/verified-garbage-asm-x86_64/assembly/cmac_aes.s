// The functions of `src/cmac_aes.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cmac_aes_absorb_aesni:
	lea rsp, [rsp-2312]
	mov r9, rsp
	add r9, 8
	mov QWORD PTR [r9+2176], rbx
	mov QWORD PTR [r9+2184], rbp
	mov QWORD PTR [r9+2192], r12
	mov QWORD PTR [r9+2200], r13
	mov QWORD PTR [r9+2208], r14
	mov QWORD PTR [r9+2216], r15
	mov rbx, rdi
	mov rbp, rsi
	mov r13, rcx
	mov r14, r8
	mov r15, r9
	test rdx, rdx
	je 20f
	mov rax, rdx
	sub rax, 1
	and rax, 15
	add rax, 1
	jmp 21f
20:
	mov eax, 0
21:
	mov ecx, 16
	sub rcx, rax
	cmp r14, rcx
	jb 22f
	jmp 23f
22:
	mov rcx, r14
23:
	mov rdx, rbx
	add rdx, 288
	add rdx, rax
	mov r10d, 0
	test rcx, rcx
	je 24f
26:
	movzx eax, BYTE PTR [r13+r10*1]
	mov BYTE PTR [rdx+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 26b
	jmp 25f
24:
25:
	add r13, rcx
	mov r8d, 0
	sub r14, rcx
	je 27f
	mov r8d, 1
	jmp 28f
27:
28:
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, rbx
	add rdx, 272
	mov rcx, rbx
	add rcx, 288
	mov r9, r15
	call {vg_cmac_aes_update_aesni}
	mov r12d, 0
	test r14, r14
	je 29f
	mov r12, r14
	sub r12, 1
	mov rax, r12
	and rax, 15
	sub r12, rax
	jmp 210f
29:
210:
	mov r8, r12
	shr r8, 4
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, rbx
	add rdx, 272
	mov rcx, r13
	mov r9, r15
	call {vg_cmac_aes_update_aesni}
	add r13, r12
	sub r14, r12
	mov rdx, rbx
	add rdx, 288
	mov rcx, r14
	mov r10d, 0
	test rcx, rcx
	je 211f
213:
	movzx eax, BYTE PTR [r13+r10*1]
	mov BYTE PTR [rdx+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 213b
	jmp 212f
211:
212:
	mov rbx, QWORD PTR [r15+2176]
	mov rbp, QWORD PTR [r15+2184]
	mov r12, QWORD PTR [r15+2192]
	mov r13, QWORD PTR [r15+2200]
	mov r14, QWORD PTR [r15+2208]
	mov r15, QWORD PTR [r15+2216]
	lea rsp, [rsp+2312]
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
	lea rsp, [rsp-2328]
	movdqu XMMWORD PTR [rsp+2312], xmm0
	movdqu XMMWORD PTR [rsp+2296], xmm0
	movdqu XMMWORD PTR [rsp+2280], xmm0
	movdqu XMMWORD PTR [rsp+2264], xmm0
	movdqu XMMWORD PTR [rsp+2248], xmm0
	movdqu XMMWORD PTR [rsp+2232], xmm0
	movdqu XMMWORD PTR [rsp+2216], xmm0
	movdqu XMMWORD PTR [rsp+2200], xmm0
	movdqu XMMWORD PTR [rsp+2184], xmm0
	movdqu XMMWORD PTR [rsp+2168], xmm0
	movdqu XMMWORD PTR [rsp+2152], xmm0
	movdqu XMMWORD PTR [rsp+2136], xmm0
	movdqu XMMWORD PTR [rsp+2120], xmm0
	movdqu XMMWORD PTR [rsp+2104], xmm0
	movdqu XMMWORD PTR [rsp+2088], xmm0
	movdqu XMMWORD PTR [rsp+2072], xmm0
	movdqu XMMWORD PTR [rsp+2056], xmm0
	movdqu XMMWORD PTR [rsp+2040], xmm0
	movdqu XMMWORD PTR [rsp+2024], xmm0
	movdqu XMMWORD PTR [rsp+2008], xmm0
	movdqu XMMWORD PTR [rsp+1992], xmm0
	movdqu XMMWORD PTR [rsp+1976], xmm0
	movdqu XMMWORD PTR [rsp+1960], xmm0
	movdqu XMMWORD PTR [rsp+1944], xmm0
	movdqu XMMWORD PTR [rsp+1928], xmm0
	movdqu XMMWORD PTR [rsp+1912], xmm0
	movdqu XMMWORD PTR [rsp+1896], xmm0
	movdqu XMMWORD PTR [rsp+1880], xmm0
	movdqu XMMWORD PTR [rsp+1864], xmm0
	movdqu XMMWORD PTR [rsp+1848], xmm0
	movdqu XMMWORD PTR [rsp+1832], xmm0
	movdqu XMMWORD PTR [rsp+1816], xmm0
	movdqu XMMWORD PTR [rsp+1800], xmm0
	movdqu XMMWORD PTR [rsp+1784], xmm0
	movdqu XMMWORD PTR [rsp+1768], xmm0
	movdqu XMMWORD PTR [rsp+1752], xmm0
	movdqu XMMWORD PTR [rsp+1736], xmm0
	movdqu XMMWORD PTR [rsp+1720], xmm0
	movdqu XMMWORD PTR [rsp+1704], xmm0
	movdqu XMMWORD PTR [rsp+1688], xmm0
	movdqu XMMWORD PTR [rsp+1672], xmm0
	movdqu XMMWORD PTR [rsp+1656], xmm0
	movdqu XMMWORD PTR [rsp+1640], xmm0
	movdqu XMMWORD PTR [rsp+1624], xmm0
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
	lea rsp, [rsp+2328]
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

vg_cmac_aes_absorb:
	lea rsp, [rsp-2312]
	mov r9, rsp
	add r9, 8
	mov QWORD PTR [r9+2176], rbx
	mov QWORD PTR [r9+2184], rbp
	mov QWORD PTR [r9+2192], r12
	mov QWORD PTR [r9+2200], r13
	mov QWORD PTR [r9+2208], r14
	mov QWORD PTR [r9+2216], r15
	mov rbx, rdi
	mov rbp, rsi
	mov r13, rcx
	mov r14, r8
	mov r15, r9
	test rdx, rdx
	je 20f
	mov rax, rdx
	sub rax, 1
	and rax, 15
	add rax, 1
	jmp 21f
20:
	mov eax, 0
21:
	mov ecx, 16
	sub rcx, rax
	cmp r14, rcx
	jb 22f
	jmp 23f
22:
	mov rcx, r14
23:
	mov rdx, rbx
	add rdx, 288
	add rdx, rax
	mov r10d, 0
	test rcx, rcx
	je 24f
26:
	movzx eax, BYTE PTR [r13+r10*1]
	mov BYTE PTR [rdx+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 26b
	jmp 25f
24:
25:
	add r13, rcx
	mov r8d, 0
	sub r14, rcx
	je 27f
	mov r8d, 1
	jmp 28f
27:
28:
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, rbx
	add rdx, 272
	mov rcx, rbx
	add rcx, 288
	mov r9, r15
	call {vg_cmac_aes_update}
	mov r12d, 0
	test r14, r14
	je 29f
	mov r12, r14
	sub r12, 1
	mov rax, r12
	and rax, 15
	sub r12, rax
	jmp 210f
29:
210:
	mov r8, r12
	shr r8, 4
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, rbx
	add rdx, 272
	mov rcx, r13
	mov r9, r15
	call {vg_cmac_aes_update}
	add r13, r12
	sub r14, r12
	mov rdx, rbx
	add rdx, 288
	mov rcx, r14
	mov r10d, 0
	test rcx, rcx
	je 211f
213:
	movzx eax, BYTE PTR [r13+r10*1]
	mov BYTE PTR [rdx+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 213b
	jmp 212f
211:
212:
	mov rbx, QWORD PTR [r15+2176]
	mov rbp, QWORD PTR [r15+2184]
	mov r12, QWORD PTR [r15+2192]
	mov r13, QWORD PTR [r15+2200]
	mov r14, QWORD PTR [r15+2208]
	mov r15, QWORD PTR [r15+2216]
	lea rsp, [rsp+2312]
	ret
	.p2align 6

vg_cmac_aes_init_vaes:
	lea rsp, [rsp-2312]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+2176], rbx
	mov QWORD PTR [rcx+2184], rbp
	mov QWORD PTR [rcx+2192], r12
	mov rbx, rdi
	mov rbp, rcx
	mov r12, rdx
	shr r12, 2
	add r12, 6
	mov rdi, rsi
	mov rsi, rdx
	mov rdx, rbx
	call {vg_aes_expand_key_scratch_aesni}
	mov rdi, rbx
	mov rsi, r12
	mov rdx, rbx
	add rdx, 240
	mov rcx, rbp
	call {vg_cmac_aes_subkeys_vaes}
	mov eax, 0
	mov QWORD PTR [rbx+272], rax
	mov QWORD PTR [rbx+280], rax
	mov rbx, QWORD PTR [rbp+2176]
	mov r12, QWORD PTR [rbp+2192]
	mov rbp, QWORD PTR [rbp+2184]
	lea rsp, [rsp+2312]
	ret
	.p2align 6

vg_cmac_aes_finish_vaes:
	lea rsp, [rsp-2312]
	mov r8, rsp
	add r8, 8
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rcx], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rcx+8], rax
	mov r9, r8
	mov r8, rdx
	mov rdx, rcx
	mov rcx, rdi
	add rcx, 288
	test r8, r8
	je 20f
	sub r8, 1
	and r8, 15
	add r8, 1
	jmp 21f
20:
21:
	call {vg_cmac_aes_finalize_vaes}
	lea rsp, [rsp+2312]
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
	lea rsp, [rsp-2328]
	movdqu XMMWORD PTR [rsp+2312], xmm0
	movdqu XMMWORD PTR [rsp+2296], xmm0
	movdqu XMMWORD PTR [rsp+2280], xmm0
	movdqu XMMWORD PTR [rsp+2264], xmm0
	movdqu XMMWORD PTR [rsp+2248], xmm0
	movdqu XMMWORD PTR [rsp+2232], xmm0
	movdqu XMMWORD PTR [rsp+2216], xmm0
	movdqu XMMWORD PTR [rsp+2200], xmm0
	movdqu XMMWORD PTR [rsp+2184], xmm0
	movdqu XMMWORD PTR [rsp+2168], xmm0
	movdqu XMMWORD PTR [rsp+2152], xmm0
	movdqu XMMWORD PTR [rsp+2136], xmm0
	movdqu XMMWORD PTR [rsp+2120], xmm0
	movdqu XMMWORD PTR [rsp+2104], xmm0
	movdqu XMMWORD PTR [rsp+2088], xmm0
	movdqu XMMWORD PTR [rsp+2072], xmm0
	movdqu XMMWORD PTR [rsp+2056], xmm0
	movdqu XMMWORD PTR [rsp+2040], xmm0
	movdqu XMMWORD PTR [rsp+2024], xmm0
	movdqu XMMWORD PTR [rsp+2008], xmm0
	movdqu XMMWORD PTR [rsp+1992], xmm0
	movdqu XMMWORD PTR [rsp+1976], xmm0
	movdqu XMMWORD PTR [rsp+1960], xmm0
	movdqu XMMWORD PTR [rsp+1944], xmm0
	movdqu XMMWORD PTR [rsp+1928], xmm0
	movdqu XMMWORD PTR [rsp+1912], xmm0
	movdqu XMMWORD PTR [rsp+1896], xmm0
	movdqu XMMWORD PTR [rsp+1880], xmm0
	movdqu XMMWORD PTR [rsp+1864], xmm0
	movdqu XMMWORD PTR [rsp+1848], xmm0
	movdqu XMMWORD PTR [rsp+1832], xmm0
	movdqu XMMWORD PTR [rsp+1816], xmm0
	movdqu XMMWORD PTR [rsp+1800], xmm0
	movdqu XMMWORD PTR [rsp+1784], xmm0
	movdqu XMMWORD PTR [rsp+1768], xmm0
	movdqu XMMWORD PTR [rsp+1752], xmm0
	movdqu XMMWORD PTR [rsp+1736], xmm0
	movdqu XMMWORD PTR [rsp+1720], xmm0
	movdqu XMMWORD PTR [rsp+1704], xmm0
	movdqu XMMWORD PTR [rsp+1688], xmm0
	movdqu XMMWORD PTR [rsp+1672], xmm0
	movdqu XMMWORD PTR [rsp+1656], xmm0
	movdqu XMMWORD PTR [rsp+1640], xmm0
	movdqu XMMWORD PTR [rsp+1624], xmm0
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
	lea rsp, [rsp+2328]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	ret
	.p2align 6

vg_cmac_aes_init_aesni:
	lea rsp, [rsp-2312]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+2176], rbx
	mov QWORD PTR [rcx+2184], rbp
	mov QWORD PTR [rcx+2192], r12
	mov rbx, rdi
	mov rbp, rcx
	mov r12, rdx
	shr r12, 2
	add r12, 6
	mov rdi, rsi
	mov rsi, rdx
	mov rdx, rbx
	call {vg_aes_expand_key_scratch_aesni}
	mov rdi, rbx
	mov rsi, r12
	mov rdx, rbx
	add rdx, 240
	mov rcx, rbp
	call {vg_cmac_aes_subkeys_aesni}
	mov eax, 0
	mov QWORD PTR [rbx+272], rax
	mov QWORD PTR [rbx+280], rax
	mov rbx, QWORD PTR [rbp+2176]
	mov r12, QWORD PTR [rbp+2192]
	mov rbp, QWORD PTR [rbp+2184]
	lea rsp, [rsp+2312]
	ret
	.p2align 6

vg_cmac_aes_finish_aesni:
	lea rsp, [rsp-2312]
	mov r8, rsp
	add r8, 8
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rcx], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rcx+8], rax
	mov r9, r8
	mov r8, rdx
	mov rdx, rcx
	mov rcx, rdi
	add rcx, 288
	test r8, r8
	je 20f
	sub r8, 1
	and r8, 15
	add r8, 1
	jmp 21f
20:
21:
	call {vg_cmac_aes_finalize_aesni}
	lea rsp, [rsp+2312]
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
	lea rsp, [rsp-2328]
	movdqu XMMWORD PTR [rsp+2312], xmm0
	movdqu XMMWORD PTR [rsp+2296], xmm0
	movdqu XMMWORD PTR [rsp+2280], xmm0
	movdqu XMMWORD PTR [rsp+2264], xmm0
	movdqu XMMWORD PTR [rsp+2248], xmm0
	movdqu XMMWORD PTR [rsp+2232], xmm0
	movdqu XMMWORD PTR [rsp+2216], xmm0
	movdqu XMMWORD PTR [rsp+2200], xmm0
	movdqu XMMWORD PTR [rsp+2184], xmm0
	movdqu XMMWORD PTR [rsp+2168], xmm0
	movdqu XMMWORD PTR [rsp+2152], xmm0
	movdqu XMMWORD PTR [rsp+2136], xmm0
	movdqu XMMWORD PTR [rsp+2120], xmm0
	movdqu XMMWORD PTR [rsp+2104], xmm0
	movdqu XMMWORD PTR [rsp+2088], xmm0
	movdqu XMMWORD PTR [rsp+2072], xmm0
	movdqu XMMWORD PTR [rsp+2056], xmm0
	movdqu XMMWORD PTR [rsp+2040], xmm0
	movdqu XMMWORD PTR [rsp+2024], xmm0
	movdqu XMMWORD PTR [rsp+2008], xmm0
	movdqu XMMWORD PTR [rsp+1992], xmm0
	movdqu XMMWORD PTR [rsp+1976], xmm0
	movdqu XMMWORD PTR [rsp+1960], xmm0
	movdqu XMMWORD PTR [rsp+1944], xmm0
	movdqu XMMWORD PTR [rsp+1928], xmm0
	movdqu XMMWORD PTR [rsp+1912], xmm0
	movdqu XMMWORD PTR [rsp+1896], xmm0
	movdqu XMMWORD PTR [rsp+1880], xmm0
	movdqu XMMWORD PTR [rsp+1864], xmm0
	movdqu XMMWORD PTR [rsp+1848], xmm0
	movdqu XMMWORD PTR [rsp+1832], xmm0
	movdqu XMMWORD PTR [rsp+1816], xmm0
	movdqu XMMWORD PTR [rsp+1800], xmm0
	movdqu XMMWORD PTR [rsp+1784], xmm0
	movdqu XMMWORD PTR [rsp+1768], xmm0
	movdqu XMMWORD PTR [rsp+1752], xmm0
	movdqu XMMWORD PTR [rsp+1736], xmm0
	movdqu XMMWORD PTR [rsp+1720], xmm0
	movdqu XMMWORD PTR [rsp+1704], xmm0
	movdqu XMMWORD PTR [rsp+1688], xmm0
	movdqu XMMWORD PTR [rsp+1672], xmm0
	movdqu XMMWORD PTR [rsp+1656], xmm0
	movdqu XMMWORD PTR [rsp+1640], xmm0
	movdqu XMMWORD PTR [rsp+1624], xmm0
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
	lea rsp, [rsp+2328]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	ret
	.p2align 6

vg_cmac_aes_init:
	lea rsp, [rsp-2312]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+2176], rbx
	mov QWORD PTR [rcx+2184], rbp
	mov QWORD PTR [rcx+2192], r12
	mov rbx, rdi
	mov rbp, rcx
	mov r12, rdx
	shr r12, 2
	add r12, 6
	mov rdi, rsi
	mov rsi, rdx
	mov rdx, rbx
	call {vg_aes_expand_key_scratch}
	mov rdi, rbx
	mov rsi, r12
	mov rdx, rbx
	add rdx, 240
	mov rcx, rbp
	call {vg_cmac_aes_subkeys}
	mov eax, 0
	mov QWORD PTR [rbx+272], rax
	mov QWORD PTR [rbx+280], rax
	mov rbx, QWORD PTR [rbp+2176]
	mov r12, QWORD PTR [rbp+2192]
	mov rbp, QWORD PTR [rbp+2184]
	lea rsp, [rsp+2312]
	ret
	.p2align 6

vg_cmac_aes_finish:
	lea rsp, [rsp-2312]
	mov r8, rsp
	add r8, 8
	mov rax, QWORD PTR [rdi+272]
	mov QWORD PTR [rcx], rax
	mov rax, QWORD PTR [rdi+280]
	mov QWORD PTR [rcx+8], rax
	mov r9, r8
	mov r8, rdx
	mov rdx, rcx
	mov rcx, rdi
	add rcx, 288
	test r8, r8
	je 20f
	sub r8, 1
	and r8, 15
	add r8, 1
	jmp 21f
20:
21:
	call {vg_cmac_aes_finalize}
	lea rsp, [rsp+2312]
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
	lea rsp, [rsp-2328]
	movdqu XMMWORD PTR [rsp+2312], xmm0
	movdqu XMMWORD PTR [rsp+2296], xmm0
	movdqu XMMWORD PTR [rsp+2280], xmm0
	movdqu XMMWORD PTR [rsp+2264], xmm0
	movdqu XMMWORD PTR [rsp+2248], xmm0
	movdqu XMMWORD PTR [rsp+2232], xmm0
	movdqu XMMWORD PTR [rsp+2216], xmm0
	movdqu XMMWORD PTR [rsp+2200], xmm0
	movdqu XMMWORD PTR [rsp+2184], xmm0
	movdqu XMMWORD PTR [rsp+2168], xmm0
	movdqu XMMWORD PTR [rsp+2152], xmm0
	movdqu XMMWORD PTR [rsp+2136], xmm0
	movdqu XMMWORD PTR [rsp+2120], xmm0
	movdqu XMMWORD PTR [rsp+2104], xmm0
	movdqu XMMWORD PTR [rsp+2088], xmm0
	movdqu XMMWORD PTR [rsp+2072], xmm0
	movdqu XMMWORD PTR [rsp+2056], xmm0
	movdqu XMMWORD PTR [rsp+2040], xmm0
	movdqu XMMWORD PTR [rsp+2024], xmm0
	movdqu XMMWORD PTR [rsp+2008], xmm0
	movdqu XMMWORD PTR [rsp+1992], xmm0
	movdqu XMMWORD PTR [rsp+1976], xmm0
	movdqu XMMWORD PTR [rsp+1960], xmm0
	movdqu XMMWORD PTR [rsp+1944], xmm0
	movdqu XMMWORD PTR [rsp+1928], xmm0
	movdqu XMMWORD PTR [rsp+1912], xmm0
	movdqu XMMWORD PTR [rsp+1896], xmm0
	movdqu XMMWORD PTR [rsp+1880], xmm0
	movdqu XMMWORD PTR [rsp+1864], xmm0
	movdqu XMMWORD PTR [rsp+1848], xmm0
	movdqu XMMWORD PTR [rsp+1832], xmm0
	movdqu XMMWORD PTR [rsp+1816], xmm0
	movdqu XMMWORD PTR [rsp+1800], xmm0
	movdqu XMMWORD PTR [rsp+1784], xmm0
	movdqu XMMWORD PTR [rsp+1768], xmm0
	movdqu XMMWORD PTR [rsp+1752], xmm0
	movdqu XMMWORD PTR [rsp+1736], xmm0
	movdqu XMMWORD PTR [rsp+1720], xmm0
	movdqu XMMWORD PTR [rsp+1704], xmm0
	movdqu XMMWORD PTR [rsp+1688], xmm0
	movdqu XMMWORD PTR [rsp+1672], xmm0
	movdqu XMMWORD PTR [rsp+1656], xmm0
	movdqu XMMWORD PTR [rsp+1640], xmm0
	movdqu XMMWORD PTR [rsp+1624], xmm0
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
	lea rsp, [rsp+2328]
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
