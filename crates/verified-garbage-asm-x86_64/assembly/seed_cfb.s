// The functions of `src/seed_cfb.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_seed_cfb128_encrypt:
	lea rsp, [rsp-1544]
	mov r8, rsp
	add r8, 8
	mov r9, r8
	mov QWORD PTR [r9+1472], rbx
	mov QWORD PTR [r9+1480], rbp
	mov QWORD PTR [r9+1488], r12
	mov QWORD PTR [r9+1496], r13
	mov QWORD PTR [r9+1504], r14
	mov QWORD PTR [r9+1512], r15
	movq xmm15, rsi
	mov r12, rdx
	mov r13, rcx
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [r9+1344], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [r9+1352], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [r9+1360], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [r9+1368], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [r9+1376], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [r9+1384], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [r9+1392], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [r9+1400], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [r9+1408], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [r9+1416], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [r9+1424], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [r9+1432], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [r9+1440], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [r9+1448], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [r9+1456], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [r9+1464], rax
	movq rax, xmm15
	mov rbp, QWORD PTR [rax]
	mov QWORD PTR [r9+1088], rbp
	mov rbp, QWORD PTR [rax+8]
	mov QWORD PTR [r9+1096], rbp
	test r13, r13
	je 20f
22:
	movq xmm12, r9
	movq xmm13, r12
	movq xmm14, r13
	mov rdi, r9
	add rdi, 1344
	mov rsi, r9
	add rsi, 1088
	movabs rdx, 16
	mov rcx, r9
	call {vg_seed_encrypt_blocks}
	movq r9, xmm12
	movq r12, xmm13
	movq r13, xmm14
	mov rax, QWORD PTR [r12]
	xor rax, QWORD PTR [r9+1088]
	mov QWORD PTR [r12], rax
	mov rax, QWORD PTR [r12+8]
	xor rax, QWORD PTR [r9+1096]
	mov QWORD PTR [r12+8], rax
	mov rax, QWORD PTR [r12]
	mov QWORD PTR [r9+1088], rax
	mov rax, QWORD PTR [r12+8]
	mov QWORD PTR [r9+1096], rax
	add r12, 16
	sub r13, 1
	jne 22b
	jmp 21f
20:
21:
	movq rax, xmm15
	mov rbp, QWORD PTR [r9+1088]
	mov QWORD PTR [rax], rbp
	mov rbp, QWORD PTR [r9+1096]
	mov QWORD PTR [rax+8], rbp
	mov rbx, QWORD PTR [r9+1472]
	mov rbp, QWORD PTR [r9+1480]
	mov r12, QWORD PTR [r9+1488]
	mov r13, QWORD PTR [r9+1496]
	mov r14, QWORD PTR [r9+1504]
	mov r15, QWORD PTR [r9+1512]
	pxor xmm0, xmm0
	mov r11d, 0
	movdqu XMMWORD PTR [rsp+8], xmm0
	movdqu XMMWORD PTR [rsp+24], xmm0
	movdqu XMMWORD PTR [rsp+40], xmm0
	movdqu XMMWORD PTR [rsp+56], xmm0
	movdqu XMMWORD PTR [rsp+72], xmm0
	movdqu XMMWORD PTR [rsp+88], xmm0
	movdqu XMMWORD PTR [rsp+104], xmm0
	movdqu XMMWORD PTR [rsp+120], xmm0
	movdqu XMMWORD PTR [rsp+136], xmm0
	movdqu XMMWORD PTR [rsp+152], xmm0
	movdqu XMMWORD PTR [rsp+168], xmm0
	movdqu XMMWORD PTR [rsp+184], xmm0
	movdqu XMMWORD PTR [rsp+200], xmm0
	movdqu XMMWORD PTR [rsp+216], xmm0
	movdqu XMMWORD PTR [rsp+232], xmm0
	movdqu XMMWORD PTR [rsp+248], xmm0
	movdqu XMMWORD PTR [rsp+264], xmm0
	movdqu XMMWORD PTR [rsp+280], xmm0
	movdqu XMMWORD PTR [rsp+296], xmm0
	movdqu XMMWORD PTR [rsp+312], xmm0
	movdqu XMMWORD PTR [rsp+328], xmm0
	movdqu XMMWORD PTR [rsp+344], xmm0
	movdqu XMMWORD PTR [rsp+360], xmm0
	movdqu XMMWORD PTR [rsp+376], xmm0
	movdqu XMMWORD PTR [rsp+392], xmm0
	movdqu XMMWORD PTR [rsp+408], xmm0
	movdqu XMMWORD PTR [rsp+424], xmm0
	movdqu XMMWORD PTR [rsp+440], xmm0
	movdqu XMMWORD PTR [rsp+456], xmm0
	movdqu XMMWORD PTR [rsp+472], xmm0
	movdqu XMMWORD PTR [rsp+488], xmm0
	movdqu XMMWORD PTR [rsp+504], xmm0
	movdqu XMMWORD PTR [rsp+520], xmm0
	movdqu XMMWORD PTR [rsp+536], xmm0
	movdqu XMMWORD PTR [rsp+552], xmm0
	movdqu XMMWORD PTR [rsp+568], xmm0
	movdqu XMMWORD PTR [rsp+584], xmm0
	movdqu XMMWORD PTR [rsp+600], xmm0
	movdqu XMMWORD PTR [rsp+616], xmm0
	movdqu XMMWORD PTR [rsp+632], xmm0
	movdqu XMMWORD PTR [rsp+648], xmm0
	movdqu XMMWORD PTR [rsp+664], xmm0
	movdqu XMMWORD PTR [rsp+680], xmm0
	movdqu XMMWORD PTR [rsp+696], xmm0
	movdqu XMMWORD PTR [rsp+712], xmm0
	movdqu XMMWORD PTR [rsp+728], xmm0
	movdqu XMMWORD PTR [rsp+744], xmm0
	movdqu XMMWORD PTR [rsp+760], xmm0
	movdqu XMMWORD PTR [rsp+776], xmm0
	movdqu XMMWORD PTR [rsp+792], xmm0
	movdqu XMMWORD PTR [rsp+808], xmm0
	movdqu XMMWORD PTR [rsp+824], xmm0
	movdqu XMMWORD PTR [rsp+840], xmm0
	movdqu XMMWORD PTR [rsp+856], xmm0
	movdqu XMMWORD PTR [rsp+872], xmm0
	movdqu XMMWORD PTR [rsp+888], xmm0
	movdqu XMMWORD PTR [rsp+904], xmm0
	movdqu XMMWORD PTR [rsp+920], xmm0
	movdqu XMMWORD PTR [rsp+936], xmm0
	movdqu XMMWORD PTR [rsp+952], xmm0
	movdqu XMMWORD PTR [rsp+968], xmm0
	movdqu XMMWORD PTR [rsp+984], xmm0
	movdqu XMMWORD PTR [rsp+1000], xmm0
	movdqu XMMWORD PTR [rsp+1016], xmm0
	movdqu XMMWORD PTR [rsp+1032], xmm0
	movdqu XMMWORD PTR [rsp+1048], xmm0
	movdqu XMMWORD PTR [rsp+1064], xmm0
	movdqu XMMWORD PTR [rsp+1080], xmm0
	movdqu XMMWORD PTR [rsp+1096], xmm0
	movdqu XMMWORD PTR [rsp+1112], xmm0
	movdqu XMMWORD PTR [rsp+1128], xmm0
	movdqu XMMWORD PTR [rsp+1144], xmm0
	movdqu XMMWORD PTR [rsp+1160], xmm0
	movdqu XMMWORD PTR [rsp+1176], xmm0
	movdqu XMMWORD PTR [rsp+1192], xmm0
	movdqu XMMWORD PTR [rsp+1208], xmm0
	movdqu XMMWORD PTR [rsp+1224], xmm0
	movdqu XMMWORD PTR [rsp+1240], xmm0
	movdqu XMMWORD PTR [rsp+1256], xmm0
	movdqu XMMWORD PTR [rsp+1272], xmm0
	movdqu XMMWORD PTR [rsp+1288], xmm0
	movdqu XMMWORD PTR [rsp+1304], xmm0
	movdqu XMMWORD PTR [rsp+1320], xmm0
	movdqu XMMWORD PTR [rsp+1336], xmm0
	movdqu XMMWORD PTR [rsp+1352], xmm0
	movdqu XMMWORD PTR [rsp+1368], xmm0
	movdqu XMMWORD PTR [rsp+1384], xmm0
	movdqu XMMWORD PTR [rsp+1400], xmm0
	movdqu XMMWORD PTR [rsp+1416], xmm0
	movdqu XMMWORD PTR [rsp+1432], xmm0
	movdqu XMMWORD PTR [rsp+1448], xmm0
	movdqu XMMWORD PTR [rsp+1464], xmm0
	movdqu XMMWORD PTR [rsp+1480], xmm0
	movdqu XMMWORD PTR [rsp+1496], xmm0
	movdqu XMMWORD PTR [rsp+1512], xmm0
	movdqu XMMWORD PTR [rsp+1528], xmm0
	lea rsp, [rsp+1544]
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
	lea rsp, [rsp-1544]
	movdqu XMMWORD PTR [rsp+8], xmm0
	lea rsp, [rsp+1544]
	lea rsp, [rsp+8]
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

vg_seed_cfb128_decrypt:
	lea rsp, [rsp-1544]
	mov r8, rsp
	add r8, 8
	mov r9, r8
	mov QWORD PTR [r9+1472], rbx
	mov QWORD PTR [r9+1480], rbp
	mov QWORD PTR [r9+1488], r12
	mov QWORD PTR [r9+1496], r13
	mov QWORD PTR [r9+1504], r14
	mov QWORD PTR [r9+1512], r15
	mov rax, QWORD PTR [rsi]
	mov QWORD PTR [r9+1520], rax
	mov rax, QWORD PTR [rsi+8]
	mov QWORD PTR [r9+1528], rax
	test rcx, rcx
	je 20f
	mov rax, rcx
	sub rax, 1
	shl rax, 4
	add rax, rdx
	mov rbx, QWORD PTR [rax]
	mov QWORD PTR [rsi], rbx
	mov rbx, QWORD PTR [rax+8]
	mov QWORD PTR [rsi+8], rbx
	jmp 21f
20:
21:
	mov r12, rdx
	mov r13, rcx
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [r9+1344], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [r9+1352], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [r9+1360], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [r9+1368], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [r9+1376], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [r9+1384], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [r9+1392], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [r9+1400], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [r9+1408], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [r9+1416], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [r9+1424], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [r9+1432], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [r9+1440], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [r9+1448], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [r9+1456], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [r9+1464], rax
	test r13, r13
	je 22f
24:
	movabs rcx, 16
	cmp r13, 16
	jb 25f
	jmp 26f
25:
	mov rcx, r13
26:
	mov rbp, QWORD PTR [r9+1520]
	mov QWORD PTR [r9+1088], rbp
	mov rbp, QWORD PTR [r9+1528]
	mov QWORD PTR [r9+1096], rbp
	mov rax, r9
	add rax, 1104
	mov rbx, r12
	sub rcx, 1
	je 27f
29:
	mov rbp, QWORD PTR [rbx]
	mov QWORD PTR [rax], rbp
	mov rbp, QWORD PTR [rbx+8]
	mov QWORD PTR [rax+8], rbp
	add rax, 16
	add rbx, 16
	sub rcx, 1
	jne 29b
	jmp 28f
27:
28:
	mov rbp, QWORD PTR [rbx]
	mov QWORD PTR [r9+1520], rbp
	mov rbp, QWORD PTR [rbx+8]
	mov QWORD PTR [r9+1528], rbp
	movq xmm12, r9
	movq xmm13, r12
	movq xmm14, r13
	mov rdi, r9
	add rdi, 1344
	mov rsi, r9
	add rsi, 1088
	movabs rdx, 16
	mov rcx, r9
	call {vg_seed_encrypt_blocks}
	movq r9, xmm12
	movq r12, xmm13
	movq r13, xmm14
	movabs rcx, 16
	cmp r13, 16
	jb 210f
	jmp 211f
210:
	mov rcx, r13
211:
	mov rax, r9
	add rax, 1088
	mov rbx, r12
	mov r10, rcx
212:
	mov rbp, QWORD PTR [rax]
	xor rbp, QWORD PTR [rbx]
	mov QWORD PTR [rbx], rbp
	mov rbp, QWORD PTR [rax+8]
	xor rbp, QWORD PTR [rbx+8]
	mov QWORD PTR [rbx+8], rbp
	add rax, 16
	add rbx, 16
	sub rcx, 1
	jne 212b
	mov r12, rbx
	sub r13, r10
	jne 24b
	jmp 23f
22:
23:
	mov rbx, QWORD PTR [r9+1472]
	mov rbp, QWORD PTR [r9+1480]
	mov r12, QWORD PTR [r9+1488]
	mov r13, QWORD PTR [r9+1496]
	mov r14, QWORD PTR [r9+1504]
	mov r15, QWORD PTR [r9+1512]
	pxor xmm0, xmm0
	mov r11d, 0
	movdqu XMMWORD PTR [rsp+8], xmm0
	movdqu XMMWORD PTR [rsp+24], xmm0
	movdqu XMMWORD PTR [rsp+40], xmm0
	movdqu XMMWORD PTR [rsp+56], xmm0
	movdqu XMMWORD PTR [rsp+72], xmm0
	movdqu XMMWORD PTR [rsp+88], xmm0
	movdqu XMMWORD PTR [rsp+104], xmm0
	movdqu XMMWORD PTR [rsp+120], xmm0
	movdqu XMMWORD PTR [rsp+136], xmm0
	movdqu XMMWORD PTR [rsp+152], xmm0
	movdqu XMMWORD PTR [rsp+168], xmm0
	movdqu XMMWORD PTR [rsp+184], xmm0
	movdqu XMMWORD PTR [rsp+200], xmm0
	movdqu XMMWORD PTR [rsp+216], xmm0
	movdqu XMMWORD PTR [rsp+232], xmm0
	movdqu XMMWORD PTR [rsp+248], xmm0
	movdqu XMMWORD PTR [rsp+264], xmm0
	movdqu XMMWORD PTR [rsp+280], xmm0
	movdqu XMMWORD PTR [rsp+296], xmm0
	movdqu XMMWORD PTR [rsp+312], xmm0
	movdqu XMMWORD PTR [rsp+328], xmm0
	movdqu XMMWORD PTR [rsp+344], xmm0
	movdqu XMMWORD PTR [rsp+360], xmm0
	movdqu XMMWORD PTR [rsp+376], xmm0
	movdqu XMMWORD PTR [rsp+392], xmm0
	movdqu XMMWORD PTR [rsp+408], xmm0
	movdqu XMMWORD PTR [rsp+424], xmm0
	movdqu XMMWORD PTR [rsp+440], xmm0
	movdqu XMMWORD PTR [rsp+456], xmm0
	movdqu XMMWORD PTR [rsp+472], xmm0
	movdqu XMMWORD PTR [rsp+488], xmm0
	movdqu XMMWORD PTR [rsp+504], xmm0
	movdqu XMMWORD PTR [rsp+520], xmm0
	movdqu XMMWORD PTR [rsp+536], xmm0
	movdqu XMMWORD PTR [rsp+552], xmm0
	movdqu XMMWORD PTR [rsp+568], xmm0
	movdqu XMMWORD PTR [rsp+584], xmm0
	movdqu XMMWORD PTR [rsp+600], xmm0
	movdqu XMMWORD PTR [rsp+616], xmm0
	movdqu XMMWORD PTR [rsp+632], xmm0
	movdqu XMMWORD PTR [rsp+648], xmm0
	movdqu XMMWORD PTR [rsp+664], xmm0
	movdqu XMMWORD PTR [rsp+680], xmm0
	movdqu XMMWORD PTR [rsp+696], xmm0
	movdqu XMMWORD PTR [rsp+712], xmm0
	movdqu XMMWORD PTR [rsp+728], xmm0
	movdqu XMMWORD PTR [rsp+744], xmm0
	movdqu XMMWORD PTR [rsp+760], xmm0
	movdqu XMMWORD PTR [rsp+776], xmm0
	movdqu XMMWORD PTR [rsp+792], xmm0
	movdqu XMMWORD PTR [rsp+808], xmm0
	movdqu XMMWORD PTR [rsp+824], xmm0
	movdqu XMMWORD PTR [rsp+840], xmm0
	movdqu XMMWORD PTR [rsp+856], xmm0
	movdqu XMMWORD PTR [rsp+872], xmm0
	movdqu XMMWORD PTR [rsp+888], xmm0
	movdqu XMMWORD PTR [rsp+904], xmm0
	movdqu XMMWORD PTR [rsp+920], xmm0
	movdqu XMMWORD PTR [rsp+936], xmm0
	movdqu XMMWORD PTR [rsp+952], xmm0
	movdqu XMMWORD PTR [rsp+968], xmm0
	movdqu XMMWORD PTR [rsp+984], xmm0
	movdqu XMMWORD PTR [rsp+1000], xmm0
	movdqu XMMWORD PTR [rsp+1016], xmm0
	movdqu XMMWORD PTR [rsp+1032], xmm0
	movdqu XMMWORD PTR [rsp+1048], xmm0
	movdqu XMMWORD PTR [rsp+1064], xmm0
	movdqu XMMWORD PTR [rsp+1080], xmm0
	movdqu XMMWORD PTR [rsp+1096], xmm0
	movdqu XMMWORD PTR [rsp+1112], xmm0
	movdqu XMMWORD PTR [rsp+1128], xmm0
	movdqu XMMWORD PTR [rsp+1144], xmm0
	movdqu XMMWORD PTR [rsp+1160], xmm0
	movdqu XMMWORD PTR [rsp+1176], xmm0
	movdqu XMMWORD PTR [rsp+1192], xmm0
	movdqu XMMWORD PTR [rsp+1208], xmm0
	movdqu XMMWORD PTR [rsp+1224], xmm0
	movdqu XMMWORD PTR [rsp+1240], xmm0
	movdqu XMMWORD PTR [rsp+1256], xmm0
	movdqu XMMWORD PTR [rsp+1272], xmm0
	movdqu XMMWORD PTR [rsp+1288], xmm0
	movdqu XMMWORD PTR [rsp+1304], xmm0
	movdqu XMMWORD PTR [rsp+1320], xmm0
	movdqu XMMWORD PTR [rsp+1336], xmm0
	movdqu XMMWORD PTR [rsp+1352], xmm0
	movdqu XMMWORD PTR [rsp+1368], xmm0
	movdqu XMMWORD PTR [rsp+1384], xmm0
	movdqu XMMWORD PTR [rsp+1400], xmm0
	movdqu XMMWORD PTR [rsp+1416], xmm0
	movdqu XMMWORD PTR [rsp+1432], xmm0
	movdqu XMMWORD PTR [rsp+1448], xmm0
	movdqu XMMWORD PTR [rsp+1464], xmm0
	movdqu XMMWORD PTR [rsp+1480], xmm0
	movdqu XMMWORD PTR [rsp+1496], xmm0
	movdqu XMMWORD PTR [rsp+1512], xmm0
	movdqu XMMWORD PTR [rsp+1528], xmm0
	lea rsp, [rsp+1544]
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
	lea rsp, [rsp-1544]
	movdqu XMMWORD PTR [rsp+8], xmm0
	lea rsp, [rsp+1544]
	lea rsp, [rsp+8]
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

vg_seed_cfb128_encrypt_final:
	lea rsp, [rsp-1544]
	mov r8, rsp
	add r8, 8
	mov r9, r8
	mov QWORD PTR [r9+1472], rbx
	mov QWORD PTR [r9+1480], rbp
	mov QWORD PTR [r9+1488], r12
	mov QWORD PTR [r9+1496], r13
	mov QWORD PTR [r9+1504], r14
	mov QWORD PTR [r9+1512], r15
	movq xmm15, rsi
	mov r12, rdx
	mov r13, rcx
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [r9+1344], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [r9+1352], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [r9+1360], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [r9+1368], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [r9+1376], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [r9+1384], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [r9+1392], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [r9+1400], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [r9+1408], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [r9+1416], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [r9+1424], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [r9+1432], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [r9+1440], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [r9+1448], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [r9+1456], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [r9+1464], rax
	movq rax, xmm15
	mov rbp, QWORD PTR [rax]
	mov QWORD PTR [r9+1088], rbp
	mov rbp, QWORD PTR [rax+8]
	mov QWORD PTR [r9+1096], rbp
	test r13, r13
	je 20f
22:
	movq xmm12, r9
	movq xmm13, r12
	movq xmm14, r13
	mov rdi, r9
	add rdi, 1344
	mov rsi, r9
	add rsi, 1088
	movabs rdx, 16
	mov rcx, r9
	call {vg_seed_encrypt_blocks}
	movq r9, xmm12
	movq r12, xmm13
	movq r13, xmm14
	cmp r13, 16
	jb 23f
	mov rax, QWORD PTR [r12]
	xor rax, QWORD PTR [r9+1088]
	mov QWORD PTR [r12], rax
	mov rax, QWORD PTR [r12+8]
	xor rax, QWORD PTR [r9+1096]
	mov QWORD PTR [r12+8], rax
	mov rax, QWORD PTR [r12]
	mov QWORD PTR [r9+1088], rax
	mov rax, QWORD PTR [r12+8]
	mov QWORD PTR [r9+1096], rax
	add r12, 16
	sub r13, 16
	jmp 24f
23:
	mov rax, r9
	add rax, 1088
25:
	movzx r10d, BYTE PTR [rax]
	movzx ecx, BYTE PTR [r12]
	xor rcx, r10
	mov BYTE PTR [r12], cl
	add rax, 1
	add r12, 1
	sub r13, 1
	jne 25b
24:
	jne 22b
	jmp 21f
20:
21:
	movq rax, xmm15
	mov rbp, QWORD PTR [r9+1088]
	mov QWORD PTR [rax], rbp
	mov rbp, QWORD PTR [r9+1096]
	mov QWORD PTR [rax+8], rbp
	mov rbx, QWORD PTR [r9+1472]
	mov rbp, QWORD PTR [r9+1480]
	mov r12, QWORD PTR [r9+1488]
	mov r13, QWORD PTR [r9+1496]
	mov r14, QWORD PTR [r9+1504]
	mov r15, QWORD PTR [r9+1512]
	pxor xmm0, xmm0
	mov r11d, 0
	movdqu XMMWORD PTR [rsp+8], xmm0
	movdqu XMMWORD PTR [rsp+24], xmm0
	movdqu XMMWORD PTR [rsp+40], xmm0
	movdqu XMMWORD PTR [rsp+56], xmm0
	movdqu XMMWORD PTR [rsp+72], xmm0
	movdqu XMMWORD PTR [rsp+88], xmm0
	movdqu XMMWORD PTR [rsp+104], xmm0
	movdqu XMMWORD PTR [rsp+120], xmm0
	movdqu XMMWORD PTR [rsp+136], xmm0
	movdqu XMMWORD PTR [rsp+152], xmm0
	movdqu XMMWORD PTR [rsp+168], xmm0
	movdqu XMMWORD PTR [rsp+184], xmm0
	movdqu XMMWORD PTR [rsp+200], xmm0
	movdqu XMMWORD PTR [rsp+216], xmm0
	movdqu XMMWORD PTR [rsp+232], xmm0
	movdqu XMMWORD PTR [rsp+248], xmm0
	movdqu XMMWORD PTR [rsp+264], xmm0
	movdqu XMMWORD PTR [rsp+280], xmm0
	movdqu XMMWORD PTR [rsp+296], xmm0
	movdqu XMMWORD PTR [rsp+312], xmm0
	movdqu XMMWORD PTR [rsp+328], xmm0
	movdqu XMMWORD PTR [rsp+344], xmm0
	movdqu XMMWORD PTR [rsp+360], xmm0
	movdqu XMMWORD PTR [rsp+376], xmm0
	movdqu XMMWORD PTR [rsp+392], xmm0
	movdqu XMMWORD PTR [rsp+408], xmm0
	movdqu XMMWORD PTR [rsp+424], xmm0
	movdqu XMMWORD PTR [rsp+440], xmm0
	movdqu XMMWORD PTR [rsp+456], xmm0
	movdqu XMMWORD PTR [rsp+472], xmm0
	movdqu XMMWORD PTR [rsp+488], xmm0
	movdqu XMMWORD PTR [rsp+504], xmm0
	movdqu XMMWORD PTR [rsp+520], xmm0
	movdqu XMMWORD PTR [rsp+536], xmm0
	movdqu XMMWORD PTR [rsp+552], xmm0
	movdqu XMMWORD PTR [rsp+568], xmm0
	movdqu XMMWORD PTR [rsp+584], xmm0
	movdqu XMMWORD PTR [rsp+600], xmm0
	movdqu XMMWORD PTR [rsp+616], xmm0
	movdqu XMMWORD PTR [rsp+632], xmm0
	movdqu XMMWORD PTR [rsp+648], xmm0
	movdqu XMMWORD PTR [rsp+664], xmm0
	movdqu XMMWORD PTR [rsp+680], xmm0
	movdqu XMMWORD PTR [rsp+696], xmm0
	movdqu XMMWORD PTR [rsp+712], xmm0
	movdqu XMMWORD PTR [rsp+728], xmm0
	movdqu XMMWORD PTR [rsp+744], xmm0
	movdqu XMMWORD PTR [rsp+760], xmm0
	movdqu XMMWORD PTR [rsp+776], xmm0
	movdqu XMMWORD PTR [rsp+792], xmm0
	movdqu XMMWORD PTR [rsp+808], xmm0
	movdqu XMMWORD PTR [rsp+824], xmm0
	movdqu XMMWORD PTR [rsp+840], xmm0
	movdqu XMMWORD PTR [rsp+856], xmm0
	movdqu XMMWORD PTR [rsp+872], xmm0
	movdqu XMMWORD PTR [rsp+888], xmm0
	movdqu XMMWORD PTR [rsp+904], xmm0
	movdqu XMMWORD PTR [rsp+920], xmm0
	movdqu XMMWORD PTR [rsp+936], xmm0
	movdqu XMMWORD PTR [rsp+952], xmm0
	movdqu XMMWORD PTR [rsp+968], xmm0
	movdqu XMMWORD PTR [rsp+984], xmm0
	movdqu XMMWORD PTR [rsp+1000], xmm0
	movdqu XMMWORD PTR [rsp+1016], xmm0
	movdqu XMMWORD PTR [rsp+1032], xmm0
	movdqu XMMWORD PTR [rsp+1048], xmm0
	movdqu XMMWORD PTR [rsp+1064], xmm0
	movdqu XMMWORD PTR [rsp+1080], xmm0
	movdqu XMMWORD PTR [rsp+1096], xmm0
	movdqu XMMWORD PTR [rsp+1112], xmm0
	movdqu XMMWORD PTR [rsp+1128], xmm0
	movdqu XMMWORD PTR [rsp+1144], xmm0
	movdqu XMMWORD PTR [rsp+1160], xmm0
	movdqu XMMWORD PTR [rsp+1176], xmm0
	movdqu XMMWORD PTR [rsp+1192], xmm0
	movdqu XMMWORD PTR [rsp+1208], xmm0
	movdqu XMMWORD PTR [rsp+1224], xmm0
	movdqu XMMWORD PTR [rsp+1240], xmm0
	movdqu XMMWORD PTR [rsp+1256], xmm0
	movdqu XMMWORD PTR [rsp+1272], xmm0
	movdqu XMMWORD PTR [rsp+1288], xmm0
	movdqu XMMWORD PTR [rsp+1304], xmm0
	movdqu XMMWORD PTR [rsp+1320], xmm0
	movdqu XMMWORD PTR [rsp+1336], xmm0
	movdqu XMMWORD PTR [rsp+1352], xmm0
	movdqu XMMWORD PTR [rsp+1368], xmm0
	movdqu XMMWORD PTR [rsp+1384], xmm0
	movdqu XMMWORD PTR [rsp+1400], xmm0
	movdqu XMMWORD PTR [rsp+1416], xmm0
	movdqu XMMWORD PTR [rsp+1432], xmm0
	movdqu XMMWORD PTR [rsp+1448], xmm0
	movdqu XMMWORD PTR [rsp+1464], xmm0
	movdqu XMMWORD PTR [rsp+1480], xmm0
	movdqu XMMWORD PTR [rsp+1496], xmm0
	movdqu XMMWORD PTR [rsp+1512], xmm0
	movdqu XMMWORD PTR [rsp+1528], xmm0
	lea rsp, [rsp+1544]
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
	lea rsp, [rsp-1544]
	movdqu XMMWORD PTR [rsp+8], xmm0
	lea rsp, [rsp+1544]
	lea rsp, [rsp+8]
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

vg_seed_cfb128_decrypt_final:
	lea rsp, [rsp-1544]
	mov r8, rsp
	add r8, 8
	mov r9, r8
	mov QWORD PTR [r9+1472], rbx
	mov QWORD PTR [r9+1480], rbp
	mov QWORD PTR [r9+1488], r12
	mov QWORD PTR [r9+1496], r13
	mov QWORD PTR [r9+1504], r14
	mov QWORD PTR [r9+1512], r15
	movq xmm15, rsi
	mov r12, rdx
	mov r13, rcx
	mov rax, QWORD PTR [rdi]
	mov QWORD PTR [r9+1344], rax
	mov rax, QWORD PTR [rdi+8]
	mov QWORD PTR [r9+1352], rax
	mov rax, QWORD PTR [rdi+16]
	mov QWORD PTR [r9+1360], rax
	mov rax, QWORD PTR [rdi+24]
	mov QWORD PTR [r9+1368], rax
	mov rax, QWORD PTR [rdi+32]
	mov QWORD PTR [r9+1376], rax
	mov rax, QWORD PTR [rdi+40]
	mov QWORD PTR [r9+1384], rax
	mov rax, QWORD PTR [rdi+48]
	mov QWORD PTR [r9+1392], rax
	mov rax, QWORD PTR [rdi+56]
	mov QWORD PTR [r9+1400], rax
	mov rax, QWORD PTR [rdi+64]
	mov QWORD PTR [r9+1408], rax
	mov rax, QWORD PTR [rdi+72]
	mov QWORD PTR [r9+1416], rax
	mov rax, QWORD PTR [rdi+80]
	mov QWORD PTR [r9+1424], rax
	mov rax, QWORD PTR [rdi+88]
	mov QWORD PTR [r9+1432], rax
	mov rax, QWORD PTR [rdi+96]
	mov QWORD PTR [r9+1440], rax
	mov rax, QWORD PTR [rdi+104]
	mov QWORD PTR [r9+1448], rax
	mov rax, QWORD PTR [rdi+112]
	mov QWORD PTR [r9+1456], rax
	mov rax, QWORD PTR [rdi+120]
	mov QWORD PTR [r9+1464], rax
	movq rax, xmm15
	mov rbp, QWORD PTR [rax]
	mov QWORD PTR [r9+1088], rbp
	mov rbp, QWORD PTR [rax+8]
	mov QWORD PTR [r9+1096], rbp
	test r13, r13
	je 20f
22:
	movq xmm12, r9
	movq xmm13, r12
	movq xmm14, r13
	mov rdi, r9
	add rdi, 1344
	mov rsi, r9
	add rsi, 1088
	movabs rdx, 16
	mov rcx, r9
	call {vg_seed_encrypt_blocks}
	movq r9, xmm12
	movq r12, xmm13
	movq r13, xmm14
	cmp r13, 16
	jb 23f
	mov rax, QWORD PTR [r12]
	xor rax, QWORD PTR [r9+1088]
	mov QWORD PTR [r12], rax
	mov rax, QWORD PTR [r12+8]
	xor rax, QWORD PTR [r9+1096]
	mov QWORD PTR [r12+8], rax
	mov rax, QWORD PTR [r9+1088]
	xor rax, QWORD PTR [r12]
	mov QWORD PTR [r9+1088], rax
	mov rax, QWORD PTR [r9+1096]
	xor rax, QWORD PTR [r12+8]
	mov QWORD PTR [r9+1096], rax
	add r12, 16
	sub r13, 16
	jmp 24f
23:
	mov rax, r9
	add rax, 1088
25:
	movzx r10d, BYTE PTR [rax]
	movzx ecx, BYTE PTR [r12]
	xor rcx, r10
	mov BYTE PTR [r12], cl
	add rax, 1
	add r12, 1
	sub r13, 1
	jne 25b
24:
	jne 22b
	jmp 21f
20:
21:
	movq rax, xmm15
	mov rbp, QWORD PTR [r9+1088]
	mov QWORD PTR [rax], rbp
	mov rbp, QWORD PTR [r9+1096]
	mov QWORD PTR [rax+8], rbp
	mov rbx, QWORD PTR [r9+1472]
	mov rbp, QWORD PTR [r9+1480]
	mov r12, QWORD PTR [r9+1488]
	mov r13, QWORD PTR [r9+1496]
	mov r14, QWORD PTR [r9+1504]
	mov r15, QWORD PTR [r9+1512]
	pxor xmm0, xmm0
	mov r11d, 0
	movdqu XMMWORD PTR [rsp+8], xmm0
	movdqu XMMWORD PTR [rsp+24], xmm0
	movdqu XMMWORD PTR [rsp+40], xmm0
	movdqu XMMWORD PTR [rsp+56], xmm0
	movdqu XMMWORD PTR [rsp+72], xmm0
	movdqu XMMWORD PTR [rsp+88], xmm0
	movdqu XMMWORD PTR [rsp+104], xmm0
	movdqu XMMWORD PTR [rsp+120], xmm0
	movdqu XMMWORD PTR [rsp+136], xmm0
	movdqu XMMWORD PTR [rsp+152], xmm0
	movdqu XMMWORD PTR [rsp+168], xmm0
	movdqu XMMWORD PTR [rsp+184], xmm0
	movdqu XMMWORD PTR [rsp+200], xmm0
	movdqu XMMWORD PTR [rsp+216], xmm0
	movdqu XMMWORD PTR [rsp+232], xmm0
	movdqu XMMWORD PTR [rsp+248], xmm0
	movdqu XMMWORD PTR [rsp+264], xmm0
	movdqu XMMWORD PTR [rsp+280], xmm0
	movdqu XMMWORD PTR [rsp+296], xmm0
	movdqu XMMWORD PTR [rsp+312], xmm0
	movdqu XMMWORD PTR [rsp+328], xmm0
	movdqu XMMWORD PTR [rsp+344], xmm0
	movdqu XMMWORD PTR [rsp+360], xmm0
	movdqu XMMWORD PTR [rsp+376], xmm0
	movdqu XMMWORD PTR [rsp+392], xmm0
	movdqu XMMWORD PTR [rsp+408], xmm0
	movdqu XMMWORD PTR [rsp+424], xmm0
	movdqu XMMWORD PTR [rsp+440], xmm0
	movdqu XMMWORD PTR [rsp+456], xmm0
	movdqu XMMWORD PTR [rsp+472], xmm0
	movdqu XMMWORD PTR [rsp+488], xmm0
	movdqu XMMWORD PTR [rsp+504], xmm0
	movdqu XMMWORD PTR [rsp+520], xmm0
	movdqu XMMWORD PTR [rsp+536], xmm0
	movdqu XMMWORD PTR [rsp+552], xmm0
	movdqu XMMWORD PTR [rsp+568], xmm0
	movdqu XMMWORD PTR [rsp+584], xmm0
	movdqu XMMWORD PTR [rsp+600], xmm0
	movdqu XMMWORD PTR [rsp+616], xmm0
	movdqu XMMWORD PTR [rsp+632], xmm0
	movdqu XMMWORD PTR [rsp+648], xmm0
	movdqu XMMWORD PTR [rsp+664], xmm0
	movdqu XMMWORD PTR [rsp+680], xmm0
	movdqu XMMWORD PTR [rsp+696], xmm0
	movdqu XMMWORD PTR [rsp+712], xmm0
	movdqu XMMWORD PTR [rsp+728], xmm0
	movdqu XMMWORD PTR [rsp+744], xmm0
	movdqu XMMWORD PTR [rsp+760], xmm0
	movdqu XMMWORD PTR [rsp+776], xmm0
	movdqu XMMWORD PTR [rsp+792], xmm0
	movdqu XMMWORD PTR [rsp+808], xmm0
	movdqu XMMWORD PTR [rsp+824], xmm0
	movdqu XMMWORD PTR [rsp+840], xmm0
	movdqu XMMWORD PTR [rsp+856], xmm0
	movdqu XMMWORD PTR [rsp+872], xmm0
	movdqu XMMWORD PTR [rsp+888], xmm0
	movdqu XMMWORD PTR [rsp+904], xmm0
	movdqu XMMWORD PTR [rsp+920], xmm0
	movdqu XMMWORD PTR [rsp+936], xmm0
	movdqu XMMWORD PTR [rsp+952], xmm0
	movdqu XMMWORD PTR [rsp+968], xmm0
	movdqu XMMWORD PTR [rsp+984], xmm0
	movdqu XMMWORD PTR [rsp+1000], xmm0
	movdqu XMMWORD PTR [rsp+1016], xmm0
	movdqu XMMWORD PTR [rsp+1032], xmm0
	movdqu XMMWORD PTR [rsp+1048], xmm0
	movdqu XMMWORD PTR [rsp+1064], xmm0
	movdqu XMMWORD PTR [rsp+1080], xmm0
	movdqu XMMWORD PTR [rsp+1096], xmm0
	movdqu XMMWORD PTR [rsp+1112], xmm0
	movdqu XMMWORD PTR [rsp+1128], xmm0
	movdqu XMMWORD PTR [rsp+1144], xmm0
	movdqu XMMWORD PTR [rsp+1160], xmm0
	movdqu XMMWORD PTR [rsp+1176], xmm0
	movdqu XMMWORD PTR [rsp+1192], xmm0
	movdqu XMMWORD PTR [rsp+1208], xmm0
	movdqu XMMWORD PTR [rsp+1224], xmm0
	movdqu XMMWORD PTR [rsp+1240], xmm0
	movdqu XMMWORD PTR [rsp+1256], xmm0
	movdqu XMMWORD PTR [rsp+1272], xmm0
	movdqu XMMWORD PTR [rsp+1288], xmm0
	movdqu XMMWORD PTR [rsp+1304], xmm0
	movdqu XMMWORD PTR [rsp+1320], xmm0
	movdqu XMMWORD PTR [rsp+1336], xmm0
	movdqu XMMWORD PTR [rsp+1352], xmm0
	movdqu XMMWORD PTR [rsp+1368], xmm0
	movdqu XMMWORD PTR [rsp+1384], xmm0
	movdqu XMMWORD PTR [rsp+1400], xmm0
	movdqu XMMWORD PTR [rsp+1416], xmm0
	movdqu XMMWORD PTR [rsp+1432], xmm0
	movdqu XMMWORD PTR [rsp+1448], xmm0
	movdqu XMMWORD PTR [rsp+1464], xmm0
	movdqu XMMWORD PTR [rsp+1480], xmm0
	movdqu XMMWORD PTR [rsp+1496], xmm0
	movdqu XMMWORD PTR [rsp+1512], xmm0
	movdqu XMMWORD PTR [rsp+1528], xmm0
	lea rsp, [rsp+1544]
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
	lea rsp, [rsp-1544]
	movdqu XMMWORD PTR [rsp+8], xmm0
	lea rsp, [rsp+1544]
	lea rsp, [rsp+8]
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
