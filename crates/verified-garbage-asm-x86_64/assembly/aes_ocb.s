// The functions of `src/aes_ocb.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ocb_init_vaes:
	lea rsp, [rsp-32]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx], rbx
	mov QWORD PTR [rcx+8], rbp
	mov QWORD PTR [rcx+16], r12
	mov rbx, rdx
	mov rbp, rsi
	shr rbp, 2
	add rbp, 6
	mov r12, rcx
	add rcx, 512
	call {vg_aes_expand_key_scratch_aesni}
	xor rax, rax
	mov QWORD PTR [rbx+240], rax
	mov QWORD PTR [rbx+248], rax
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, rbx
	add rdx, 240
	mov rcx, 1
	mov r8, r12
	add r8, 512
	call {vg_aes_encrypt_blocks_vaes}
	mov rbx, QWORD PTR [r12]
	mov rbp, QWORD PTR [r12+8]
	mov r12, QWORD PTR [r12+16]
	lea rsp, [rsp+32]
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
	lea rsp, [rsp-40]
	vmovdqu YMMWORD PTR [rsp+8], ymm0
	lea rsp, [rsp+40]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r10d, r10d
	ret
	.p2align 6

vg_aes_ocb_init_aesni:
	lea rsp, [rsp-32]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx], rbx
	mov QWORD PTR [rcx+8], rbp
	mov QWORD PTR [rcx+16], r12
	mov rbx, rdx
	mov rbp, rsi
	shr rbp, 2
	add rbp, 6
	mov r12, rcx
	add rcx, 512
	call {vg_aes_expand_key_scratch_aesni}
	xor rax, rax
	mov QWORD PTR [rbx+240], rax
	mov QWORD PTR [rbx+248], rax
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, rbx
	add rdx, 240
	mov rcx, 1
	mov r8, r12
	add r8, 512
	call {vg_aes_encrypt_blocks_aesni}
	mov rbx, QWORD PTR [r12]
	mov rbp, QWORD PTR [r12+8]
	mov r12, QWORD PTR [r12+16]
	lea rsp, [rsp+32]
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
	lea rsp, [rsp-40]
	movdqu XMMWORD PTR [rsp+24], xmm0
	movdqu XMMWORD PTR [rsp+8], xmm0
	lea rsp, [rsp+40]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r10d, r10d
	ret
	.p2align 6

vg_aes_ocb_init:
	lea rsp, [rsp-2568]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx], rbx
	mov QWORD PTR [rcx+8], rbp
	mov QWORD PTR [rcx+16], r12
	mov rbx, rdx
	mov rbp, rsi
	shr rbp, 2
	add rbp, 6
	mov r12, rcx
	add rcx, 512
	call {vg_aes_expand_key_scratch}
	xor rax, rax
	mov QWORD PTR [rbx+240], rax
	mov QWORD PTR [rbx+248], rax
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, rbx
	add rdx, 240
	mov rcx, 1
	mov r8, r12
	add r8, 512
	call {vg_aes_encrypt_blocks}
	mov rbx, QWORD PTR [r12]
	mov rbp, QWORD PTR [r12+8]
	mov r12, QWORD PTR [r12+16]
	lea rsp, [rsp+2568]
	pxor xmm0, xmm0
	xor r11d, r11d
	lea rsp, [rsp-2576]
	movdqu XMMWORD PTR [rsp+2560], xmm0
	movdqu XMMWORD PTR [rsp+2544], xmm0
	movdqu XMMWORD PTR [rsp+2528], xmm0
	movdqu XMMWORD PTR [rsp+2512], xmm0
	movdqu XMMWORD PTR [rsp+2496], xmm0
	movdqu XMMWORD PTR [rsp+2480], xmm0
	movdqu XMMWORD PTR [rsp+2464], xmm0
	movdqu XMMWORD PTR [rsp+2448], xmm0
	movdqu XMMWORD PTR [rsp+2432], xmm0
	movdqu XMMWORD PTR [rsp+2416], xmm0
	movdqu XMMWORD PTR [rsp+2400], xmm0
	movdqu XMMWORD PTR [rsp+2384], xmm0
	movdqu XMMWORD PTR [rsp+2368], xmm0
	movdqu XMMWORD PTR [rsp+2352], xmm0
	movdqu XMMWORD PTR [rsp+2336], xmm0
	movdqu XMMWORD PTR [rsp+2320], xmm0
	movdqu XMMWORD PTR [rsp+2304], xmm0
	movdqu XMMWORD PTR [rsp+2288], xmm0
	movdqu XMMWORD PTR [rsp+2272], xmm0
	movdqu XMMWORD PTR [rsp+2256], xmm0
	movdqu XMMWORD PTR [rsp+2240], xmm0
	movdqu XMMWORD PTR [rsp+2224], xmm0
	movdqu XMMWORD PTR [rsp+2208], xmm0
	movdqu XMMWORD PTR [rsp+2192], xmm0
	movdqu XMMWORD PTR [rsp+2176], xmm0
	movdqu XMMWORD PTR [rsp+2160], xmm0
	movdqu XMMWORD PTR [rsp+2144], xmm0
	movdqu XMMWORD PTR [rsp+2128], xmm0
	movdqu XMMWORD PTR [rsp+2112], xmm0
	movdqu XMMWORD PTR [rsp+2096], xmm0
	movdqu XMMWORD PTR [rsp+2080], xmm0
	movdqu XMMWORD PTR [rsp+2064], xmm0
	movdqu XMMWORD PTR [rsp+2048], xmm0
	movdqu XMMWORD PTR [rsp+2032], xmm0
	movdqu XMMWORD PTR [rsp+2016], xmm0
	movdqu XMMWORD PTR [rsp+2000], xmm0
	movdqu XMMWORD PTR [rsp+1984], xmm0
	movdqu XMMWORD PTR [rsp+1968], xmm0
	movdqu XMMWORD PTR [rsp+1952], xmm0
	movdqu XMMWORD PTR [rsp+1936], xmm0
	movdqu XMMWORD PTR [rsp+1920], xmm0
	movdqu XMMWORD PTR [rsp+1904], xmm0
	movdqu XMMWORD PTR [rsp+1888], xmm0
	movdqu XMMWORD PTR [rsp+1872], xmm0
	movdqu XMMWORD PTR [rsp+1856], xmm0
	movdqu XMMWORD PTR [rsp+1840], xmm0
	movdqu XMMWORD PTR [rsp+1824], xmm0
	movdqu XMMWORD PTR [rsp+1808], xmm0
	movdqu XMMWORD PTR [rsp+1792], xmm0
	movdqu XMMWORD PTR [rsp+1776], xmm0
	movdqu XMMWORD PTR [rsp+1760], xmm0
	movdqu XMMWORD PTR [rsp+1744], xmm0
	movdqu XMMWORD PTR [rsp+1728], xmm0
	movdqu XMMWORD PTR [rsp+1712], xmm0
	movdqu XMMWORD PTR [rsp+1696], xmm0
	movdqu XMMWORD PTR [rsp+1680], xmm0
	movdqu XMMWORD PTR [rsp+1664], xmm0
	movdqu XMMWORD PTR [rsp+1648], xmm0
	movdqu XMMWORD PTR [rsp+1632], xmm0
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
	lea rsp, [rsp+2576]
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

vg_aes_ocb_seal_aesni:
	lea rsp, [rsp-688]
	mov rax, QWORD PTR [rsp+696]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+704]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+712]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+720]
	mov QWORD PTR [rsp+32], rax
	mov rax, rsp
	add rax, 48
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+40]
	mov QWORD PTR [rax+160], rbx
	mov QWORD PTR [rax+168], rbp
	mov QWORD PTR [rax+176], r12
	mov QWORD PTR [rax+184], r13
	mov QWORD PTR [rax+192], r14
	mov QWORD PTR [rax+200], r15
	mov r15, rax
	mov r14, rdi
	mov QWORD PTR [r15+232], rsi
	mov QWORD PTR [r15+288], rdx
	mov QWORD PTR [r15+296], rcx
	mov QWORD PTR [r15+240], r8
	mov QWORD PTR [r15+248], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+208], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r15+216], rax
	mov rax, QWORD PTR [rsp+32]
	mov QWORD PTR [r15+224], rax
	mov rax, QWORD PTR [rsp+24]
	mov QWORD PTR [r15+304], rax
	mov rax, QWORD PTR [r14+240]
	bswap rax
	mov rdx, QWORD PTR [r14+248]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	xor r8, r8
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	mov QWORD PTR [r15+64], rax
	bswap rdx
	mov QWORD PTR [r15+72], rdx
	mov rax, QWORD PTR [r15+64]
	bswap rax
	mov rdx, QWORD PTR [r15+72]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	xor r8, r8
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	mov QWORD PTR [r15+80], rax
	bswap rdx
	mov QWORD PTR [r15+88], rdx
	xor rax, rax
	mov QWORD PTR [r15+32], rax
	mov QWORD PTR [r15+40], rax
	mov rsi, QWORD PTR [r15+232]
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	xor rax, rax
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rax
	mov rbx, QWORD PTR [r15+288]
	mov r12, QWORD PTR [r15+296]
	mov rsi, r15
	add rsi, 128
	sub rsi, r12
	mov rcx, 0
20:
	movzx eax, BYTE PTR [rbx+rcx*1]
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 20b
	mov rax, 1
	mov BYTE PTR [rsi-1], al
	mov rax, QWORD PTR [r15+224]
	and rax, 15
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx ecx, BYTE PTR [r15+112]
	or rcx, rax
	mov BYTE PTR [r15+112], cl
	movzx eax, BYTE PTR [r15+127]
	mov rcx, rax
	and rcx, 63
	mov QWORD PTR [r15+256], rcx
	and rax, 192
	mov BYTE PTR [r15+127], al
	mov rsi, r10
	sub rsi, rdi
	shr rsi, 4
	movdqu xmm0, XMMWORD PTR [r15+112]
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	cmp rsi, 10
	je 21f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 23f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 24f
23:
24:
	jmp 22f
21:
22:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	movdqu XMMWORD PTR [r15+112], xmm0
	mov rax, QWORD PTR [r15+80]
	bswap rax
	mov rdx, QWORD PTR [r15+88]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	xor r8, r8
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	mov QWORD PTR [r15+96], rax
	bswap rdx
	mov QWORD PTR [r15+104], rdx
	mov rax, QWORD PTR [r15+96]
	bswap rax
	mov rdx, QWORD PTR [r15+104]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	xor r8, r8
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	mov QWORD PTR [r15+144], rax
	bswap rdx
	mov QWORD PTR [r15+152], rdx
	mov rax, QWORD PTR [r15+144]
	bswap rax
	mov rdx, QWORD PTR [r15+152]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	xor r8, r8
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	mov QWORD PTR [r15+320], rax
	bswap rdx
	mov QWORD PTR [r15+328], rdx
	mov rax, QWORD PTR [r15+80]
	mov rdx, QWORD PTR [r15+88]
	movq xmm12, rax
	movq xmm11, rdx
	punpcklqdq xmm12, xmm11
	mov rax, QWORD PTR [r15+96]
	mov rdx, QWORD PTR [r15+104]
	movq xmm13, rax
	movq xmm11, rdx
	punpcklqdq xmm13, xmm11
	mov rax, QWORD PTR [r15+144]
	mov rdx, QWORD PTR [r15+152]
	movq xmm14, rax
	movq xmm11, rdx
	punpcklqdq xmm14, xmm11
	movdqu XMMWORD PTR [r15+384], xmm12
	movdqu XMMWORD PTR [r15+416], xmm13
	movdqu XMMWORD PTR [r15+480], xmm14
	movdqa xmm11, xmm12
	pxor xmm11, xmm13
	movdqu XMMWORD PTR [r15+400], xmm11
	pxor xmm11, xmm14
	movdqu XMMWORD PTR [r15+448], xmm11
	movdqa xmm11, xmm13
	pxor xmm11, xmm14
	movdqu XMMWORD PTR [r15+432], xmm11
	movdqa xmm11, xmm12
	pxor xmm11, xmm14
	movdqu XMMWORD PTR [r15+464], xmm11
	mov rsi, QWORD PTR [r15+232]
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	mov r11, QWORD PTR [r15+240]
	mov r12, QWORD PTR [r15+248]
	shr r12, 4
	pxor xmm12, xmm12
	pxor xmm10, xmm10
	mov r13, 0
	cmp r12, 8
	jb 25f
27:
	mov rax, QWORD PTR [r15+320]
	mov rdx, QWORD PTR [r15+328]
	mov QWORD PTR [r15+336], rax
	mov QWORD PTR [r15+344], rdx
	mov r9, r13
	add r9, 1
	test r9, 1
	jne 28f
210:
	mov rax, QWORD PTR [r15+336]
	bswap rax
	mov rdx, QWORD PTR [r15+344]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	xor r8, r8
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	mov QWORD PTR [r15+336], rax
	bswap rdx
	mov QWORD PTR [r15+344], rdx
	shr r9, 1
	test r9, 1
	je 210b
	jmp 29f
28:
29:
	mov rax, QWORD PTR [r15+336]
	mov rdx, QWORD PTR [r15+344]
	xor rax, QWORD PTR [r15+144]
	xor rdx, QWORD PTR [r15+152]
	movq xmm11, rax
	movq xmm13, rdx
	punpcklqdq xmm11, xmm13
	movdqu XMMWORD PTR [r15+496], xmm11
	movdqu xmm0, XMMWORD PTR [r11]
	movdqu xmm11, XMMWORD PTR [r15+384]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+512], xmm11
	pxor xmm0, xmm11
	movdqu xmm1, XMMWORD PTR [r11+16]
	movdqu xmm11, XMMWORD PTR [r15+400]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+528], xmm11
	pxor xmm1, xmm11
	movdqu xmm2, XMMWORD PTR [r11+32]
	movdqu xmm11, XMMWORD PTR [r15+416]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+544], xmm11
	pxor xmm2, xmm11
	movdqu xmm3, XMMWORD PTR [r11+48]
	movdqu xmm11, XMMWORD PTR [r15+432]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+560], xmm11
	pxor xmm3, xmm11
	movdqu xmm4, XMMWORD PTR [r11+64]
	movdqu xmm11, XMMWORD PTR [r15+448]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+576], xmm11
	pxor xmm4, xmm11
	movdqu xmm5, XMMWORD PTR [r11+80]
	movdqu xmm11, XMMWORD PTR [r15+464]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+592], xmm11
	pxor xmm5, xmm11
	movdqu xmm6, XMMWORD PTR [r11+96]
	movdqu xmm11, XMMWORD PTR [r15+480]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+608], xmm11
	pxor xmm6, xmm11
	movdqu xmm7, XMMWORD PTR [r11+112]
	movdqu xmm11, XMMWORD PTR [r15+496]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+624], xmm11
	pxor xmm7, xmm11
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	pxor xmm2, xmm8
	pxor xmm3, xmm8
	pxor xmm4, xmm8
	pxor xmm5, xmm8
	pxor xmm6, xmm8
	pxor xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	cmp rsi, 10
	je 211f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	cmp rsi, 12
	je 213f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	jmp 214f
213:
214:
	jmp 212f
211:
212:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	aesenclast xmm2, xmm8
	aesenclast xmm3, xmm8
	aesenclast xmm4, xmm8
	aesenclast xmm5, xmm8
	aesenclast xmm6, xmm8
	aesenclast xmm7, xmm8
	pxor xmm10, xmm0
	pxor xmm10, xmm1
	pxor xmm10, xmm2
	pxor xmm10, xmm3
	pxor xmm10, xmm4
	pxor xmm10, xmm5
	pxor xmm10, xmm6
	pxor xmm10, xmm7
	movdqu xmm12, XMMWORD PTR [r15+624]
	add r11, 128
	add r13, 1
	sub r12, 8
	cmp r12, 8
	jae 27b
	jmp 26f
25:
26:
	test r12, r12
	je 215f
	cmp r12, 1
	je 217f
	cmp r12, 2
	je 219f
	cmp r12, 3
	je 221f
	cmp r12, 4
	je 223f
	cmp r12, 5
	je 225f
	cmp r12, 6
	je 227f
	movdqu xmm0, XMMWORD PTR [r11]
	movdqu xmm11, XMMWORD PTR [r15+384]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+512], xmm11
	pxor xmm0, xmm11
	movdqu xmm1, XMMWORD PTR [r11+16]
	movdqu xmm11, XMMWORD PTR [r15+400]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+528], xmm11
	pxor xmm1, xmm11
	movdqu xmm2, XMMWORD PTR [r11+32]
	movdqu xmm11, XMMWORD PTR [r15+416]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+544], xmm11
	pxor xmm2, xmm11
	movdqu xmm3, XMMWORD PTR [r11+48]
	movdqu xmm11, XMMWORD PTR [r15+432]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+560], xmm11
	pxor xmm3, xmm11
	movdqu xmm4, XMMWORD PTR [r11+64]
	movdqu xmm11, XMMWORD PTR [r15+448]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+576], xmm11
	pxor xmm4, xmm11
	movdqu xmm5, XMMWORD PTR [r11+80]
	movdqu xmm11, XMMWORD PTR [r15+464]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+592], xmm11
	pxor xmm5, xmm11
	movdqu xmm6, XMMWORD PTR [r11+96]
	movdqu xmm11, XMMWORD PTR [r15+480]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+608], xmm11
	pxor xmm6, xmm11
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	pxor xmm2, xmm8
	pxor xmm3, xmm8
	pxor xmm4, xmm8
	pxor xmm5, xmm8
	pxor xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	cmp rsi, 10
	je 229f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	cmp rsi, 12
	je 231f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	jmp 232f
231:
232:
	jmp 230f
229:
230:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	aesenclast xmm2, xmm8
	aesenclast xmm3, xmm8
	aesenclast xmm4, xmm8
	aesenclast xmm5, xmm8
	aesenclast xmm6, xmm8
	pxor xmm10, xmm0
	pxor xmm10, xmm1
	pxor xmm10, xmm2
	pxor xmm10, xmm3
	pxor xmm10, xmm4
	pxor xmm10, xmm5
	pxor xmm10, xmm6
	movdqu xmm12, XMMWORD PTR [r15+608]
	add r11, 112
	jmp 228f
227:
	movdqu xmm0, XMMWORD PTR [r11]
	movdqu xmm11, XMMWORD PTR [r15+384]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+512], xmm11
	pxor xmm0, xmm11
	movdqu xmm1, XMMWORD PTR [r11+16]
	movdqu xmm11, XMMWORD PTR [r15+400]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+528], xmm11
	pxor xmm1, xmm11
	movdqu xmm2, XMMWORD PTR [r11+32]
	movdqu xmm11, XMMWORD PTR [r15+416]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+544], xmm11
	pxor xmm2, xmm11
	movdqu xmm3, XMMWORD PTR [r11+48]
	movdqu xmm11, XMMWORD PTR [r15+432]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+560], xmm11
	pxor xmm3, xmm11
	movdqu xmm4, XMMWORD PTR [r11+64]
	movdqu xmm11, XMMWORD PTR [r15+448]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+576], xmm11
	pxor xmm4, xmm11
	movdqu xmm5, XMMWORD PTR [r11+80]
	movdqu xmm11, XMMWORD PTR [r15+464]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+592], xmm11
	pxor xmm5, xmm11
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	pxor xmm2, xmm8
	pxor xmm3, xmm8
	pxor xmm4, xmm8
	pxor xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	cmp rsi, 10
	je 233f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	cmp rsi, 12
	je 235f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	jmp 236f
235:
236:
	jmp 234f
233:
234:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	aesenclast xmm2, xmm8
	aesenclast xmm3, xmm8
	aesenclast xmm4, xmm8
	aesenclast xmm5, xmm8
	pxor xmm10, xmm0
	pxor xmm10, xmm1
	pxor xmm10, xmm2
	pxor xmm10, xmm3
	pxor xmm10, xmm4
	pxor xmm10, xmm5
	movdqu xmm12, XMMWORD PTR [r15+592]
	add r11, 96
228:
	jmp 226f
225:
	movdqu xmm0, XMMWORD PTR [r11]
	movdqu xmm11, XMMWORD PTR [r15+384]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+512], xmm11
	pxor xmm0, xmm11
	movdqu xmm1, XMMWORD PTR [r11+16]
	movdqu xmm11, XMMWORD PTR [r15+400]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+528], xmm11
	pxor xmm1, xmm11
	movdqu xmm2, XMMWORD PTR [r11+32]
	movdqu xmm11, XMMWORD PTR [r15+416]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+544], xmm11
	pxor xmm2, xmm11
	movdqu xmm3, XMMWORD PTR [r11+48]
	movdqu xmm11, XMMWORD PTR [r15+432]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+560], xmm11
	pxor xmm3, xmm11
	movdqu xmm4, XMMWORD PTR [r11+64]
	movdqu xmm11, XMMWORD PTR [r15+448]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+576], xmm11
	pxor xmm4, xmm11
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	pxor xmm2, xmm8
	pxor xmm3, xmm8
	pxor xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	cmp rsi, 10
	je 237f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	cmp rsi, 12
	je 239f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	jmp 240f
239:
240:
	jmp 238f
237:
238:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	aesenclast xmm2, xmm8
	aesenclast xmm3, xmm8
	aesenclast xmm4, xmm8
	pxor xmm10, xmm0
	pxor xmm10, xmm1
	pxor xmm10, xmm2
	pxor xmm10, xmm3
	pxor xmm10, xmm4
	movdqu xmm12, XMMWORD PTR [r15+576]
	add r11, 80
226:
	jmp 224f
223:
	movdqu xmm0, XMMWORD PTR [r11]
	movdqu xmm11, XMMWORD PTR [r15+384]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+512], xmm11
	pxor xmm0, xmm11
	movdqu xmm1, XMMWORD PTR [r11+16]
	movdqu xmm11, XMMWORD PTR [r15+400]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+528], xmm11
	pxor xmm1, xmm11
	movdqu xmm2, XMMWORD PTR [r11+32]
	movdqu xmm11, XMMWORD PTR [r15+416]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+544], xmm11
	pxor xmm2, xmm11
	movdqu xmm3, XMMWORD PTR [r11+48]
	movdqu xmm11, XMMWORD PTR [r15+432]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+560], xmm11
	pxor xmm3, xmm11
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	pxor xmm2, xmm8
	pxor xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	cmp rsi, 10
	je 241f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	cmp rsi, 12
	je 243f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	jmp 244f
243:
244:
	jmp 242f
241:
242:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	aesenclast xmm2, xmm8
	aesenclast xmm3, xmm8
	pxor xmm10, xmm0
	pxor xmm10, xmm1
	pxor xmm10, xmm2
	pxor xmm10, xmm3
	movdqu xmm12, XMMWORD PTR [r15+560]
	add r11, 64
224:
	jmp 222f
221:
	movdqu xmm0, XMMWORD PTR [r11]
	movdqu xmm11, XMMWORD PTR [r15+384]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+512], xmm11
	pxor xmm0, xmm11
	movdqu xmm1, XMMWORD PTR [r11+16]
	movdqu xmm11, XMMWORD PTR [r15+400]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+528], xmm11
	pxor xmm1, xmm11
	movdqu xmm2, XMMWORD PTR [r11+32]
	movdqu xmm11, XMMWORD PTR [r15+416]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+544], xmm11
	pxor xmm2, xmm11
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	pxor xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	cmp rsi, 10
	je 245f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	cmp rsi, 12
	je 247f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	jmp 248f
247:
248:
	jmp 246f
245:
246:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	aesenclast xmm2, xmm8
	pxor xmm10, xmm0
	pxor xmm10, xmm1
	pxor xmm10, xmm2
	movdqu xmm12, XMMWORD PTR [r15+544]
	add r11, 48
222:
	jmp 220f
219:
	movdqu xmm0, XMMWORD PTR [r11]
	movdqu xmm11, XMMWORD PTR [r15+384]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+512], xmm11
	pxor xmm0, xmm11
	movdqu xmm1, XMMWORD PTR [r11+16]
	movdqu xmm11, XMMWORD PTR [r15+400]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+528], xmm11
	pxor xmm1, xmm11
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	cmp rsi, 10
	je 249f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	cmp rsi, 12
	je 251f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	jmp 252f
251:
252:
	jmp 250f
249:
250:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	pxor xmm10, xmm0
	pxor xmm10, xmm1
	movdqu xmm12, XMMWORD PTR [r15+528]
	add r11, 32
220:
	jmp 218f
217:
	movdqu xmm0, XMMWORD PTR [r11]
	movdqu xmm11, XMMWORD PTR [r15+384]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+512], xmm11
	pxor xmm0, xmm11
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	cmp rsi, 10
	je 253f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 255f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 256f
255:
256:
	jmp 254f
253:
254:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	pxor xmm10, xmm0
	movdqu xmm12, XMMWORD PTR [r15+512]
	add r11, 16
218:
	jmp 216f
215:
216:
	mov rbx, r11
	mov r12, QWORD PTR [r15+248]
	and r12, 15
	je 257f
	xor rax, rax
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rsi, r15
	add rsi, 128
	mov rcx, 0
259:
	movzx eax, BYTE PTR [rbx+rcx*1]
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 259b
	mov rax, 128
	mov BYTE PTR [rsi+rcx*1], al
	movdqu xmm11, XMMWORD PTR [rdi+240]
	pxor xmm12, xmm11
	movdqu xmm0, XMMWORD PTR [r15+128]
	pxor xmm0, xmm12
	mov rsi, r10
	sub rsi, rdi
	shr rsi, 4
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	cmp rsi, 10
	je 260f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 262f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 263f
262:
263:
	jmp 261f
260:
261:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	pxor xmm10, xmm0
	jmp 258f
257:
258:
	movdqu XMMWORD PTR [r15+48], xmm10
	mov rax, QWORD PTR [r15+112]
	bswap rax
	mov rdx, QWORD PTR [r15+120]
	bswap rdx
	mov rcx, rax
	ror rcx, 56
	movabs r8, -256
	and rcx, r8
	mov r8, rdx
	shr r8, 56
	or rcx, r8
	xor rcx, rax
	mov rbx, QWORD PTR [r15+256]
	mov r9, rbx
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -2
	mov r8, rax
	ror r8, 63
	and r8, r11
	mov r9, rdx
	shr r9, 63
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 63
	and r8, r11
	mov r9, rcx
	shr r9, 63
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 63
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 1
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -4
	mov r8, rax
	ror r8, 62
	and r8, r11
	mov r9, rdx
	shr r9, 62
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 62
	and r8, r11
	mov r9, rcx
	shr r9, 62
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 62
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 2
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -16
	mov r8, rax
	ror r8, 60
	and r8, r11
	mov r9, rdx
	shr r9, 60
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 60
	and r8, r11
	mov r9, rcx
	shr r9, 60
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 60
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 3
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -256
	mov r8, rax
	ror r8, 56
	and r8, r11
	mov r9, rdx
	shr r9, 56
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 56
	and r8, r11
	mov r9, rcx
	shr r9, 56
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 56
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 4
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -65536
	mov r8, rax
	ror r8, 48
	and r8, r11
	mov r9, rdx
	shr r9, 48
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 48
	and r8, r11
	mov r9, rcx
	shr r9, 48
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 48
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 5
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -4294967296
	mov r8, rax
	ror r8, 32
	and r8, r11
	mov r9, rdx
	shr r9, 32
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 32
	and r8, r11
	mov r9, rcx
	shr r9, 32
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 32
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+16], rax
	mov QWORD PTR [r15+24], rdx
	mov QWORD PTR [r15+272], rax
	mov QWORD PTR [r15+280], rdx
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	movq xmm12, rax
	movq xmm11, rdx
	punpcklqdq xmm12, xmm11
	pxor xmm10, xmm10
	mov r11, QWORD PTR [r15+208]
	mov r12, QWORD PTR [r15+216]
	mov rbp, r12
	shr r12, 4
	mov r13, 0
	cmp r12, 8
	jb 264f
266:
	mov rax, QWORD PTR [r15+320]
	mov rdx, QWORD PTR [r15+328]
	mov QWORD PTR [r15+336], rax
	mov QWORD PTR [r15+344], rdx
	mov r9, r13
	add r9, 1
	test r9, 1
	jne 267f
269:
	mov rax, QWORD PTR [r15+336]
	bswap rax
	mov rdx, QWORD PTR [r15+344]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	xor r8, r8
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	mov QWORD PTR [r15+336], rax
	bswap rdx
	mov QWORD PTR [r15+344], rdx
	shr r9, 1
	test r9, 1
	je 269b
	jmp 268f
267:
268:
	mov rax, QWORD PTR [r15+336]
	mov rdx, QWORD PTR [r15+344]
	xor rax, QWORD PTR [r15+144]
	xor rdx, QWORD PTR [r15+152]
	movq xmm11, rax
	movq xmm13, rdx
	punpcklqdq xmm11, xmm13
	movdqu XMMWORD PTR [r15+496], xmm11
	movdqu xmm0, XMMWORD PTR [r11]
	pxor xmm10, xmm0
	movdqu xmm11, XMMWORD PTR [r15+384]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+512], xmm11
	pxor xmm0, xmm11
	movdqu xmm1, XMMWORD PTR [r11+16]
	pxor xmm10, xmm1
	movdqu xmm11, XMMWORD PTR [r15+400]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+528], xmm11
	pxor xmm1, xmm11
	movdqu xmm2, XMMWORD PTR [r11+32]
	pxor xmm10, xmm2
	movdqu xmm11, XMMWORD PTR [r15+416]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+544], xmm11
	pxor xmm2, xmm11
	movdqu xmm3, XMMWORD PTR [r11+48]
	pxor xmm10, xmm3
	movdqu xmm11, XMMWORD PTR [r15+432]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+560], xmm11
	pxor xmm3, xmm11
	movdqu xmm4, XMMWORD PTR [r11+64]
	pxor xmm10, xmm4
	movdqu xmm11, XMMWORD PTR [r15+448]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+576], xmm11
	pxor xmm4, xmm11
	movdqu xmm5, XMMWORD PTR [r11+80]
	pxor xmm10, xmm5
	movdqu xmm11, XMMWORD PTR [r15+464]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+592], xmm11
	pxor xmm5, xmm11
	movdqu xmm6, XMMWORD PTR [r11+96]
	pxor xmm10, xmm6
	movdqu xmm11, XMMWORD PTR [r15+480]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+608], xmm11
	pxor xmm6, xmm11
	movdqu xmm7, XMMWORD PTR [r11+112]
	pxor xmm10, xmm7
	movdqu xmm11, XMMWORD PTR [r15+496]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+624], xmm11
	pxor xmm7, xmm11
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	pxor xmm2, xmm8
	pxor xmm3, xmm8
	pxor xmm4, xmm8
	pxor xmm5, xmm8
	pxor xmm6, xmm8
	pxor xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	cmp rsi, 10
	je 270f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	cmp rsi, 12
	je 272f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	jmp 273f
272:
273:
	jmp 271f
270:
271:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	aesenclast xmm2, xmm8
	aesenclast xmm3, xmm8
	aesenclast xmm4, xmm8
	aesenclast xmm5, xmm8
	aesenclast xmm6, xmm8
	aesenclast xmm7, xmm8
	movdqu xmm11, XMMWORD PTR [r15+512]
	pxor xmm0, xmm11
	movdqu XMMWORD PTR [r11], xmm0
	movdqu xmm11, XMMWORD PTR [r15+528]
	pxor xmm1, xmm11
	movdqu XMMWORD PTR [r11+16], xmm1
	movdqu xmm11, XMMWORD PTR [r15+544]
	pxor xmm2, xmm11
	movdqu XMMWORD PTR [r11+32], xmm2
	movdqu xmm11, XMMWORD PTR [r15+560]
	pxor xmm3, xmm11
	movdqu XMMWORD PTR [r11+48], xmm3
	movdqu xmm11, XMMWORD PTR [r15+576]
	pxor xmm4, xmm11
	movdqu XMMWORD PTR [r11+64], xmm4
	movdqu xmm11, XMMWORD PTR [r15+592]
	pxor xmm5, xmm11
	movdqu XMMWORD PTR [r11+80], xmm5
	movdqu xmm11, XMMWORD PTR [r15+608]
	pxor xmm6, xmm11
	movdqu XMMWORD PTR [r11+96], xmm6
	movdqu xmm11, XMMWORD PTR [r15+624]
	pxor xmm7, xmm11
	movdqu XMMWORD PTR [r11+112], xmm7
	movdqu xmm12, XMMWORD PTR [r15+624]
	add r11, 128
	add r13, 1
	sub r12, 8
	cmp r12, 8
	jae 266b
	jmp 265f
264:
265:
	test r12, r12
	je 274f
	cmp r12, 1
	je 276f
	cmp r12, 2
	je 278f
	cmp r12, 3
	je 280f
	cmp r12, 4
	je 282f
	cmp r12, 5
	je 284f
	cmp r12, 6
	je 286f
	movdqu xmm0, XMMWORD PTR [r11]
	pxor xmm10, xmm0
	movdqu xmm11, XMMWORD PTR [r15+384]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+512], xmm11
	pxor xmm0, xmm11
	movdqu xmm1, XMMWORD PTR [r11+16]
	pxor xmm10, xmm1
	movdqu xmm11, XMMWORD PTR [r15+400]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+528], xmm11
	pxor xmm1, xmm11
	movdqu xmm2, XMMWORD PTR [r11+32]
	pxor xmm10, xmm2
	movdqu xmm11, XMMWORD PTR [r15+416]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+544], xmm11
	pxor xmm2, xmm11
	movdqu xmm3, XMMWORD PTR [r11+48]
	pxor xmm10, xmm3
	movdqu xmm11, XMMWORD PTR [r15+432]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+560], xmm11
	pxor xmm3, xmm11
	movdqu xmm4, XMMWORD PTR [r11+64]
	pxor xmm10, xmm4
	movdqu xmm11, XMMWORD PTR [r15+448]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+576], xmm11
	pxor xmm4, xmm11
	movdqu xmm5, XMMWORD PTR [r11+80]
	pxor xmm10, xmm5
	movdqu xmm11, XMMWORD PTR [r15+464]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+592], xmm11
	pxor xmm5, xmm11
	movdqu xmm6, XMMWORD PTR [r11+96]
	pxor xmm10, xmm6
	movdqu xmm11, XMMWORD PTR [r15+480]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+608], xmm11
	pxor xmm6, xmm11
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	pxor xmm2, xmm8
	pxor xmm3, xmm8
	pxor xmm4, xmm8
	pxor xmm5, xmm8
	pxor xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	cmp rsi, 10
	je 288f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	cmp rsi, 12
	je 290f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	jmp 291f
290:
291:
	jmp 289f
288:
289:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	aesenclast xmm2, xmm8
	aesenclast xmm3, xmm8
	aesenclast xmm4, xmm8
	aesenclast xmm5, xmm8
	aesenclast xmm6, xmm8
	movdqu xmm11, XMMWORD PTR [r15+512]
	pxor xmm0, xmm11
	movdqu XMMWORD PTR [r11], xmm0
	movdqu xmm11, XMMWORD PTR [r15+528]
	pxor xmm1, xmm11
	movdqu XMMWORD PTR [r11+16], xmm1
	movdqu xmm11, XMMWORD PTR [r15+544]
	pxor xmm2, xmm11
	movdqu XMMWORD PTR [r11+32], xmm2
	movdqu xmm11, XMMWORD PTR [r15+560]
	pxor xmm3, xmm11
	movdqu XMMWORD PTR [r11+48], xmm3
	movdqu xmm11, XMMWORD PTR [r15+576]
	pxor xmm4, xmm11
	movdqu XMMWORD PTR [r11+64], xmm4
	movdqu xmm11, XMMWORD PTR [r15+592]
	pxor xmm5, xmm11
	movdqu XMMWORD PTR [r11+80], xmm5
	movdqu xmm11, XMMWORD PTR [r15+608]
	pxor xmm6, xmm11
	movdqu XMMWORD PTR [r11+96], xmm6
	movdqu xmm12, XMMWORD PTR [r15+608]
	add r11, 112
	jmp 287f
286:
	movdqu xmm0, XMMWORD PTR [r11]
	pxor xmm10, xmm0
	movdqu xmm11, XMMWORD PTR [r15+384]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+512], xmm11
	pxor xmm0, xmm11
	movdqu xmm1, XMMWORD PTR [r11+16]
	pxor xmm10, xmm1
	movdqu xmm11, XMMWORD PTR [r15+400]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+528], xmm11
	pxor xmm1, xmm11
	movdqu xmm2, XMMWORD PTR [r11+32]
	pxor xmm10, xmm2
	movdqu xmm11, XMMWORD PTR [r15+416]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+544], xmm11
	pxor xmm2, xmm11
	movdqu xmm3, XMMWORD PTR [r11+48]
	pxor xmm10, xmm3
	movdqu xmm11, XMMWORD PTR [r15+432]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+560], xmm11
	pxor xmm3, xmm11
	movdqu xmm4, XMMWORD PTR [r11+64]
	pxor xmm10, xmm4
	movdqu xmm11, XMMWORD PTR [r15+448]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+576], xmm11
	pxor xmm4, xmm11
	movdqu xmm5, XMMWORD PTR [r11+80]
	pxor xmm10, xmm5
	movdqu xmm11, XMMWORD PTR [r15+464]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+592], xmm11
	pxor xmm5, xmm11
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	pxor xmm2, xmm8
	pxor xmm3, xmm8
	pxor xmm4, xmm8
	pxor xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	cmp rsi, 10
	je 292f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	cmp rsi, 12
	je 294f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	jmp 295f
294:
295:
	jmp 293f
292:
293:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	aesenclast xmm2, xmm8
	aesenclast xmm3, xmm8
	aesenclast xmm4, xmm8
	aesenclast xmm5, xmm8
	movdqu xmm11, XMMWORD PTR [r15+512]
	pxor xmm0, xmm11
	movdqu XMMWORD PTR [r11], xmm0
	movdqu xmm11, XMMWORD PTR [r15+528]
	pxor xmm1, xmm11
	movdqu XMMWORD PTR [r11+16], xmm1
	movdqu xmm11, XMMWORD PTR [r15+544]
	pxor xmm2, xmm11
	movdqu XMMWORD PTR [r11+32], xmm2
	movdqu xmm11, XMMWORD PTR [r15+560]
	pxor xmm3, xmm11
	movdqu XMMWORD PTR [r11+48], xmm3
	movdqu xmm11, XMMWORD PTR [r15+576]
	pxor xmm4, xmm11
	movdqu XMMWORD PTR [r11+64], xmm4
	movdqu xmm11, XMMWORD PTR [r15+592]
	pxor xmm5, xmm11
	movdqu XMMWORD PTR [r11+80], xmm5
	movdqu xmm12, XMMWORD PTR [r15+592]
	add r11, 96
287:
	jmp 285f
284:
	movdqu xmm0, XMMWORD PTR [r11]
	pxor xmm10, xmm0
	movdqu xmm11, XMMWORD PTR [r15+384]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+512], xmm11
	pxor xmm0, xmm11
	movdqu xmm1, XMMWORD PTR [r11+16]
	pxor xmm10, xmm1
	movdqu xmm11, XMMWORD PTR [r15+400]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+528], xmm11
	pxor xmm1, xmm11
	movdqu xmm2, XMMWORD PTR [r11+32]
	pxor xmm10, xmm2
	movdqu xmm11, XMMWORD PTR [r15+416]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+544], xmm11
	pxor xmm2, xmm11
	movdqu xmm3, XMMWORD PTR [r11+48]
	pxor xmm10, xmm3
	movdqu xmm11, XMMWORD PTR [r15+432]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+560], xmm11
	pxor xmm3, xmm11
	movdqu xmm4, XMMWORD PTR [r11+64]
	pxor xmm10, xmm4
	movdqu xmm11, XMMWORD PTR [r15+448]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+576], xmm11
	pxor xmm4, xmm11
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	pxor xmm2, xmm8
	pxor xmm3, xmm8
	pxor xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	cmp rsi, 10
	je 296f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	cmp rsi, 12
	je 298f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	jmp 299f
298:
299:
	jmp 297f
296:
297:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	aesenclast xmm2, xmm8
	aesenclast xmm3, xmm8
	aesenclast xmm4, xmm8
	movdqu xmm11, XMMWORD PTR [r15+512]
	pxor xmm0, xmm11
	movdqu XMMWORD PTR [r11], xmm0
	movdqu xmm11, XMMWORD PTR [r15+528]
	pxor xmm1, xmm11
	movdqu XMMWORD PTR [r11+16], xmm1
	movdqu xmm11, XMMWORD PTR [r15+544]
	pxor xmm2, xmm11
	movdqu XMMWORD PTR [r11+32], xmm2
	movdqu xmm11, XMMWORD PTR [r15+560]
	pxor xmm3, xmm11
	movdqu XMMWORD PTR [r11+48], xmm3
	movdqu xmm11, XMMWORD PTR [r15+576]
	pxor xmm4, xmm11
	movdqu XMMWORD PTR [r11+64], xmm4
	movdqu xmm12, XMMWORD PTR [r15+576]
	add r11, 80
285:
	jmp 283f
282:
	movdqu xmm0, XMMWORD PTR [r11]
	pxor xmm10, xmm0
	movdqu xmm11, XMMWORD PTR [r15+384]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+512], xmm11
	pxor xmm0, xmm11
	movdqu xmm1, XMMWORD PTR [r11+16]
	pxor xmm10, xmm1
	movdqu xmm11, XMMWORD PTR [r15+400]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+528], xmm11
	pxor xmm1, xmm11
	movdqu xmm2, XMMWORD PTR [r11+32]
	pxor xmm10, xmm2
	movdqu xmm11, XMMWORD PTR [r15+416]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+544], xmm11
	pxor xmm2, xmm11
	movdqu xmm3, XMMWORD PTR [r11+48]
	pxor xmm10, xmm3
	movdqu xmm11, XMMWORD PTR [r15+432]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+560], xmm11
	pxor xmm3, xmm11
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	pxor xmm2, xmm8
	pxor xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	cmp rsi, 10
	je 2100f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	cmp rsi, 12
	je 2102f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	jmp 2103f
2102:
2103:
	jmp 2101f
2100:
2101:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	aesenclast xmm2, xmm8
	aesenclast xmm3, xmm8
	movdqu xmm11, XMMWORD PTR [r15+512]
	pxor xmm0, xmm11
	movdqu XMMWORD PTR [r11], xmm0
	movdqu xmm11, XMMWORD PTR [r15+528]
	pxor xmm1, xmm11
	movdqu XMMWORD PTR [r11+16], xmm1
	movdqu xmm11, XMMWORD PTR [r15+544]
	pxor xmm2, xmm11
	movdqu XMMWORD PTR [r11+32], xmm2
	movdqu xmm11, XMMWORD PTR [r15+560]
	pxor xmm3, xmm11
	movdqu XMMWORD PTR [r11+48], xmm3
	movdqu xmm12, XMMWORD PTR [r15+560]
	add r11, 64
283:
	jmp 281f
280:
	movdqu xmm0, XMMWORD PTR [r11]
	pxor xmm10, xmm0
	movdqu xmm11, XMMWORD PTR [r15+384]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+512], xmm11
	pxor xmm0, xmm11
	movdqu xmm1, XMMWORD PTR [r11+16]
	pxor xmm10, xmm1
	movdqu xmm11, XMMWORD PTR [r15+400]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+528], xmm11
	pxor xmm1, xmm11
	movdqu xmm2, XMMWORD PTR [r11+32]
	pxor xmm10, xmm2
	movdqu xmm11, XMMWORD PTR [r15+416]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+544], xmm11
	pxor xmm2, xmm11
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	pxor xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	cmp rsi, 10
	je 2104f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	cmp rsi, 12
	je 2106f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	jmp 2107f
2106:
2107:
	jmp 2105f
2104:
2105:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	aesenclast xmm2, xmm8
	movdqu xmm11, XMMWORD PTR [r15+512]
	pxor xmm0, xmm11
	movdqu XMMWORD PTR [r11], xmm0
	movdqu xmm11, XMMWORD PTR [r15+528]
	pxor xmm1, xmm11
	movdqu XMMWORD PTR [r11+16], xmm1
	movdqu xmm11, XMMWORD PTR [r15+544]
	pxor xmm2, xmm11
	movdqu XMMWORD PTR [r11+32], xmm2
	movdqu xmm12, XMMWORD PTR [r15+544]
	add r11, 48
281:
	jmp 279f
278:
	movdqu xmm0, XMMWORD PTR [r11]
	pxor xmm10, xmm0
	movdqu xmm11, XMMWORD PTR [r15+384]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+512], xmm11
	pxor xmm0, xmm11
	movdqu xmm1, XMMWORD PTR [r11+16]
	pxor xmm10, xmm1
	movdqu xmm11, XMMWORD PTR [r15+400]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+528], xmm11
	pxor xmm1, xmm11
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	cmp rsi, 10
	je 2108f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	cmp rsi, 12
	je 2110f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	jmp 2111f
2110:
2111:
	jmp 2109f
2108:
2109:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	movdqu xmm11, XMMWORD PTR [r15+512]
	pxor xmm0, xmm11
	movdqu XMMWORD PTR [r11], xmm0
	movdqu xmm11, XMMWORD PTR [r15+528]
	pxor xmm1, xmm11
	movdqu XMMWORD PTR [r11+16], xmm1
	movdqu xmm12, XMMWORD PTR [r15+528]
	add r11, 32
279:
	jmp 277f
276:
	movdqu xmm0, XMMWORD PTR [r11]
	pxor xmm10, xmm0
	movdqu xmm11, XMMWORD PTR [r15+384]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+512], xmm11
	pxor xmm0, xmm11
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	cmp rsi, 10
	je 2112f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 2114f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 2115f
2114:
2115:
	jmp 2113f
2112:
2113:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	movdqu xmm11, XMMWORD PTR [r15+512]
	pxor xmm0, xmm11
	movdqu XMMWORD PTR [r11], xmm0
	movdqu xmm12, XMMWORD PTR [r15+512]
	add r11, 16
277:
	jmp 275f
274:
275:
	mov rbx, r11
	mov r12, rbp
	and r12, 15
	je 2116f
	movdqu xmm11, XMMWORD PTR [rdi+240]
	pxor xmm12, xmm11
	movdqa xmm0, xmm12
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	cmp rsi, 10
	je 2118f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 2120f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 2121f
2120:
2121:
	jmp 2119f
2118:
2119:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	movdqu XMMWORD PTR [r15+112], xmm0
	xor rax, rax
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rsi, r15
	add rsi, 128
	mov rcx, 0
2122:
	movzx eax, BYTE PTR [rbx+rcx*1]
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 2122b
	mov rax, 128
	mov BYTE PTR [rsi+rcx*1], al
	movdqu xmm11, XMMWORD PTR [r15+128]
	pxor xmm10, xmm11
	mov rcx, 0
2123:
	movzx eax, BYTE PTR [rbx+rcx*1]
	movzx edx, BYTE PTR [r15+rcx*1+112]
	xor rax, rdx
	mov BYTE PTR [rbx+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 2123b
	jmp 2117f
2116:
2117:
	movdqa xmm0, xmm10
	pxor xmm0, xmm12
	movdqu xmm11, XMMWORD PTR [r15+64]
	pxor xmm0, xmm11
	mov rsi, r10
	sub rsi, rdi
	shr rsi, 4
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	cmp rsi, 10
	je 2124f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 2126f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 2127f
2126:
2127:
	jmp 2125f
2124:
2125:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	movdqu xmm11, XMMWORD PTR [r15+48]
	pxor xmm0, xmm11
	movdqu XMMWORD PTR [r15], xmm0
	mov rbx, r15
	mov rsi, QWORD PTR [r15+304]
	mov r12, QWORD PTR [r15+224]
	mov rcx, 0
2128:
	movzx eax, BYTE PTR [rbx+rcx*1]
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 2128b
	mov rbx, QWORD PTR [r15+160]
	mov rbp, QWORD PTR [r15+168]
	mov r12, QWORD PTR [r15+176]
	mov r13, QWORD PTR [r15+184]
	mov r14, QWORD PTR [r15+192]
	mov r15, QWORD PTR [r15+200]
	lea rsp, [rsp+688]
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
	lea rsp, [rsp-688]
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
	lea rsp, [rsp+688]
	lea rsp, [rsp+8]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6

vg_aes_ocb_open_aesni:
	lea rsp, [rsp-896]
	mov rax, QWORD PTR [rsp+904]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+912]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+920]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+928]
	mov QWORD PTR [rsp+32], rax
	mov rax, rsp
	add rax, 48
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+40]
	mov QWORD PTR [rax+160], rbx
	mov QWORD PTR [rax+168], rbp
	mov QWORD PTR [rax+176], r12
	mov QWORD PTR [rax+184], r13
	mov QWORD PTR [rax+192], r14
	mov QWORD PTR [rax+200], r15
	mov r15, rax
	mov r14, rdi
	mov QWORD PTR [r15+232], rsi
	mov QWORD PTR [r15+288], rdx
	mov QWORD PTR [r15+296], rcx
	mov QWORD PTR [r15+240], r8
	mov QWORD PTR [r15+248], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+208], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r15+216], rax
	mov rax, QWORD PTR [rsp+32]
	mov QWORD PTR [r15+224], rax
	mov rax, QWORD PTR [rsp+24]
	mov QWORD PTR [r15+304], rax
	mov rax, QWORD PTR [r14+240]
	bswap rax
	mov rdx, QWORD PTR [r14+248]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	xor r8, r8
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	mov QWORD PTR [r15+64], rax
	bswap rdx
	mov QWORD PTR [r15+72], rdx
	mov rax, QWORD PTR [r15+64]
	bswap rax
	mov rdx, QWORD PTR [r15+72]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	xor r8, r8
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	mov QWORD PTR [r15+80], rax
	bswap rdx
	mov QWORD PTR [r15+88], rdx
	xor rax, rax
	mov QWORD PTR [r15+32], rax
	mov QWORD PTR [r15+40], rax
	mov rsi, QWORD PTR [r15+232]
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	xor rax, rax
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rax
	mov rbx, QWORD PTR [r15+288]
	mov r12, QWORD PTR [r15+296]
	mov rsi, r15
	add rsi, 128
	sub rsi, r12
	mov rcx, 0
20:
	movzx eax, BYTE PTR [rbx+rcx*1]
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 20b
	mov rax, 1
	mov BYTE PTR [rsi-1], al
	mov rax, QWORD PTR [r15+224]
	and rax, 15
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx ecx, BYTE PTR [r15+112]
	or rcx, rax
	mov BYTE PTR [r15+112], cl
	movzx eax, BYTE PTR [r15+127]
	mov rcx, rax
	and rcx, 63
	mov QWORD PTR [r15+256], rcx
	and rax, 192
	mov BYTE PTR [r15+127], al
	mov rsi, r10
	sub rsi, rdi
	shr rsi, 4
	movdqu xmm0, XMMWORD PTR [r15+112]
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	cmp rsi, 10
	je 21f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 23f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 24f
23:
24:
	jmp 22f
21:
22:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	movdqu XMMWORD PTR [r15+112], xmm0
	mov rax, QWORD PTR [r15+80]
	bswap rax
	mov rdx, QWORD PTR [r15+88]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	xor r8, r8
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	mov QWORD PTR [r15+96], rax
	bswap rdx
	mov QWORD PTR [r15+104], rdx
	mov rax, QWORD PTR [r15+96]
	bswap rax
	mov rdx, QWORD PTR [r15+104]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	xor r8, r8
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	mov QWORD PTR [r15+144], rax
	bswap rdx
	mov QWORD PTR [r15+152], rdx
	mov rax, QWORD PTR [r15+144]
	bswap rax
	mov rdx, QWORD PTR [r15+152]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	xor r8, r8
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	mov QWORD PTR [r15+320], rax
	bswap rdx
	mov QWORD PTR [r15+328], rdx
	mov rax, QWORD PTR [r15+80]
	mov rdx, QWORD PTR [r15+88]
	movq xmm12, rax
	movq xmm11, rdx
	punpcklqdq xmm12, xmm11
	mov rax, QWORD PTR [r15+96]
	mov rdx, QWORD PTR [r15+104]
	movq xmm13, rax
	movq xmm11, rdx
	punpcklqdq xmm13, xmm11
	mov rax, QWORD PTR [r15+144]
	mov rdx, QWORD PTR [r15+152]
	movq xmm14, rax
	movq xmm11, rdx
	punpcklqdq xmm14, xmm11
	movdqu XMMWORD PTR [r15+384], xmm12
	movdqu XMMWORD PTR [r15+416], xmm13
	movdqu XMMWORD PTR [r15+480], xmm14
	movdqa xmm11, xmm12
	pxor xmm11, xmm13
	movdqu XMMWORD PTR [r15+400], xmm11
	pxor xmm11, xmm14
	movdqu XMMWORD PTR [r15+448], xmm11
	movdqa xmm11, xmm13
	pxor xmm11, xmm14
	movdqu XMMWORD PTR [r15+432], xmm11
	movdqa xmm11, xmm12
	pxor xmm11, xmm14
	movdqu XMMWORD PTR [r15+464], xmm11
	mov rsi, QWORD PTR [r15+232]
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	mov r11, QWORD PTR [r15+240]
	mov r12, QWORD PTR [r15+248]
	shr r12, 4
	pxor xmm12, xmm12
	pxor xmm10, xmm10
	mov r13, 0
	cmp r12, 8
	jb 25f
27:
	mov rax, QWORD PTR [r15+320]
	mov rdx, QWORD PTR [r15+328]
	mov QWORD PTR [r15+336], rax
	mov QWORD PTR [r15+344], rdx
	mov r9, r13
	add r9, 1
	test r9, 1
	jne 28f
210:
	mov rax, QWORD PTR [r15+336]
	bswap rax
	mov rdx, QWORD PTR [r15+344]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	xor r8, r8
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	mov QWORD PTR [r15+336], rax
	bswap rdx
	mov QWORD PTR [r15+344], rdx
	shr r9, 1
	test r9, 1
	je 210b
	jmp 29f
28:
29:
	mov rax, QWORD PTR [r15+336]
	mov rdx, QWORD PTR [r15+344]
	xor rax, QWORD PTR [r15+144]
	xor rdx, QWORD PTR [r15+152]
	movq xmm11, rax
	movq xmm13, rdx
	punpcklqdq xmm11, xmm13
	movdqu XMMWORD PTR [r15+496], xmm11
	movdqu xmm0, XMMWORD PTR [r11]
	movdqu xmm11, XMMWORD PTR [r15+384]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+512], xmm11
	pxor xmm0, xmm11
	movdqu xmm1, XMMWORD PTR [r11+16]
	movdqu xmm11, XMMWORD PTR [r15+400]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+528], xmm11
	pxor xmm1, xmm11
	movdqu xmm2, XMMWORD PTR [r11+32]
	movdqu xmm11, XMMWORD PTR [r15+416]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+544], xmm11
	pxor xmm2, xmm11
	movdqu xmm3, XMMWORD PTR [r11+48]
	movdqu xmm11, XMMWORD PTR [r15+432]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+560], xmm11
	pxor xmm3, xmm11
	movdqu xmm4, XMMWORD PTR [r11+64]
	movdqu xmm11, XMMWORD PTR [r15+448]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+576], xmm11
	pxor xmm4, xmm11
	movdqu xmm5, XMMWORD PTR [r11+80]
	movdqu xmm11, XMMWORD PTR [r15+464]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+592], xmm11
	pxor xmm5, xmm11
	movdqu xmm6, XMMWORD PTR [r11+96]
	movdqu xmm11, XMMWORD PTR [r15+480]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+608], xmm11
	pxor xmm6, xmm11
	movdqu xmm7, XMMWORD PTR [r11+112]
	movdqu xmm11, XMMWORD PTR [r15+496]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+624], xmm11
	pxor xmm7, xmm11
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	pxor xmm2, xmm8
	pxor xmm3, xmm8
	pxor xmm4, xmm8
	pxor xmm5, xmm8
	pxor xmm6, xmm8
	pxor xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	cmp rsi, 10
	je 211f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	cmp rsi, 12
	je 213f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	jmp 214f
213:
214:
	jmp 212f
211:
212:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	aesenclast xmm2, xmm8
	aesenclast xmm3, xmm8
	aesenclast xmm4, xmm8
	aesenclast xmm5, xmm8
	aesenclast xmm6, xmm8
	aesenclast xmm7, xmm8
	pxor xmm10, xmm0
	pxor xmm10, xmm1
	pxor xmm10, xmm2
	pxor xmm10, xmm3
	pxor xmm10, xmm4
	pxor xmm10, xmm5
	pxor xmm10, xmm6
	pxor xmm10, xmm7
	movdqu xmm12, XMMWORD PTR [r15+624]
	add r11, 128
	add r13, 1
	sub r12, 8
	cmp r12, 8
	jae 27b
	jmp 26f
25:
26:
	test r12, r12
	je 215f
	cmp r12, 1
	je 217f
	cmp r12, 2
	je 219f
	cmp r12, 3
	je 221f
	cmp r12, 4
	je 223f
	cmp r12, 5
	je 225f
	cmp r12, 6
	je 227f
	movdqu xmm0, XMMWORD PTR [r11]
	movdqu xmm11, XMMWORD PTR [r15+384]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+512], xmm11
	pxor xmm0, xmm11
	movdqu xmm1, XMMWORD PTR [r11+16]
	movdqu xmm11, XMMWORD PTR [r15+400]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+528], xmm11
	pxor xmm1, xmm11
	movdqu xmm2, XMMWORD PTR [r11+32]
	movdqu xmm11, XMMWORD PTR [r15+416]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+544], xmm11
	pxor xmm2, xmm11
	movdqu xmm3, XMMWORD PTR [r11+48]
	movdqu xmm11, XMMWORD PTR [r15+432]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+560], xmm11
	pxor xmm3, xmm11
	movdqu xmm4, XMMWORD PTR [r11+64]
	movdqu xmm11, XMMWORD PTR [r15+448]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+576], xmm11
	pxor xmm4, xmm11
	movdqu xmm5, XMMWORD PTR [r11+80]
	movdqu xmm11, XMMWORD PTR [r15+464]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+592], xmm11
	pxor xmm5, xmm11
	movdqu xmm6, XMMWORD PTR [r11+96]
	movdqu xmm11, XMMWORD PTR [r15+480]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+608], xmm11
	pxor xmm6, xmm11
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	pxor xmm2, xmm8
	pxor xmm3, xmm8
	pxor xmm4, xmm8
	pxor xmm5, xmm8
	pxor xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	cmp rsi, 10
	je 229f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	cmp rsi, 12
	je 231f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	jmp 232f
231:
232:
	jmp 230f
229:
230:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	aesenclast xmm2, xmm8
	aesenclast xmm3, xmm8
	aesenclast xmm4, xmm8
	aesenclast xmm5, xmm8
	aesenclast xmm6, xmm8
	pxor xmm10, xmm0
	pxor xmm10, xmm1
	pxor xmm10, xmm2
	pxor xmm10, xmm3
	pxor xmm10, xmm4
	pxor xmm10, xmm5
	pxor xmm10, xmm6
	movdqu xmm12, XMMWORD PTR [r15+608]
	add r11, 112
	jmp 228f
227:
	movdqu xmm0, XMMWORD PTR [r11]
	movdqu xmm11, XMMWORD PTR [r15+384]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+512], xmm11
	pxor xmm0, xmm11
	movdqu xmm1, XMMWORD PTR [r11+16]
	movdqu xmm11, XMMWORD PTR [r15+400]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+528], xmm11
	pxor xmm1, xmm11
	movdqu xmm2, XMMWORD PTR [r11+32]
	movdqu xmm11, XMMWORD PTR [r15+416]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+544], xmm11
	pxor xmm2, xmm11
	movdqu xmm3, XMMWORD PTR [r11+48]
	movdqu xmm11, XMMWORD PTR [r15+432]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+560], xmm11
	pxor xmm3, xmm11
	movdqu xmm4, XMMWORD PTR [r11+64]
	movdqu xmm11, XMMWORD PTR [r15+448]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+576], xmm11
	pxor xmm4, xmm11
	movdqu xmm5, XMMWORD PTR [r11+80]
	movdqu xmm11, XMMWORD PTR [r15+464]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+592], xmm11
	pxor xmm5, xmm11
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	pxor xmm2, xmm8
	pxor xmm3, xmm8
	pxor xmm4, xmm8
	pxor xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	cmp rsi, 10
	je 233f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	cmp rsi, 12
	je 235f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	jmp 236f
235:
236:
	jmp 234f
233:
234:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	aesenclast xmm2, xmm8
	aesenclast xmm3, xmm8
	aesenclast xmm4, xmm8
	aesenclast xmm5, xmm8
	pxor xmm10, xmm0
	pxor xmm10, xmm1
	pxor xmm10, xmm2
	pxor xmm10, xmm3
	pxor xmm10, xmm4
	pxor xmm10, xmm5
	movdqu xmm12, XMMWORD PTR [r15+592]
	add r11, 96
228:
	jmp 226f
225:
	movdqu xmm0, XMMWORD PTR [r11]
	movdqu xmm11, XMMWORD PTR [r15+384]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+512], xmm11
	pxor xmm0, xmm11
	movdqu xmm1, XMMWORD PTR [r11+16]
	movdqu xmm11, XMMWORD PTR [r15+400]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+528], xmm11
	pxor xmm1, xmm11
	movdqu xmm2, XMMWORD PTR [r11+32]
	movdqu xmm11, XMMWORD PTR [r15+416]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+544], xmm11
	pxor xmm2, xmm11
	movdqu xmm3, XMMWORD PTR [r11+48]
	movdqu xmm11, XMMWORD PTR [r15+432]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+560], xmm11
	pxor xmm3, xmm11
	movdqu xmm4, XMMWORD PTR [r11+64]
	movdqu xmm11, XMMWORD PTR [r15+448]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+576], xmm11
	pxor xmm4, xmm11
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	pxor xmm2, xmm8
	pxor xmm3, xmm8
	pxor xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	cmp rsi, 10
	je 237f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	cmp rsi, 12
	je 239f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	jmp 240f
239:
240:
	jmp 238f
237:
238:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	aesenclast xmm2, xmm8
	aesenclast xmm3, xmm8
	aesenclast xmm4, xmm8
	pxor xmm10, xmm0
	pxor xmm10, xmm1
	pxor xmm10, xmm2
	pxor xmm10, xmm3
	pxor xmm10, xmm4
	movdqu xmm12, XMMWORD PTR [r15+576]
	add r11, 80
226:
	jmp 224f
223:
	movdqu xmm0, XMMWORD PTR [r11]
	movdqu xmm11, XMMWORD PTR [r15+384]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+512], xmm11
	pxor xmm0, xmm11
	movdqu xmm1, XMMWORD PTR [r11+16]
	movdqu xmm11, XMMWORD PTR [r15+400]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+528], xmm11
	pxor xmm1, xmm11
	movdqu xmm2, XMMWORD PTR [r11+32]
	movdqu xmm11, XMMWORD PTR [r15+416]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+544], xmm11
	pxor xmm2, xmm11
	movdqu xmm3, XMMWORD PTR [r11+48]
	movdqu xmm11, XMMWORD PTR [r15+432]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+560], xmm11
	pxor xmm3, xmm11
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	pxor xmm2, xmm8
	pxor xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	cmp rsi, 10
	je 241f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	cmp rsi, 12
	je 243f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	jmp 244f
243:
244:
	jmp 242f
241:
242:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	aesenclast xmm2, xmm8
	aesenclast xmm3, xmm8
	pxor xmm10, xmm0
	pxor xmm10, xmm1
	pxor xmm10, xmm2
	pxor xmm10, xmm3
	movdqu xmm12, XMMWORD PTR [r15+560]
	add r11, 64
224:
	jmp 222f
221:
	movdqu xmm0, XMMWORD PTR [r11]
	movdqu xmm11, XMMWORD PTR [r15+384]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+512], xmm11
	pxor xmm0, xmm11
	movdqu xmm1, XMMWORD PTR [r11+16]
	movdqu xmm11, XMMWORD PTR [r15+400]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+528], xmm11
	pxor xmm1, xmm11
	movdqu xmm2, XMMWORD PTR [r11+32]
	movdqu xmm11, XMMWORD PTR [r15+416]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+544], xmm11
	pxor xmm2, xmm11
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	pxor xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	cmp rsi, 10
	je 245f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	cmp rsi, 12
	je 247f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	jmp 248f
247:
248:
	jmp 246f
245:
246:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	aesenclast xmm2, xmm8
	pxor xmm10, xmm0
	pxor xmm10, xmm1
	pxor xmm10, xmm2
	movdqu xmm12, XMMWORD PTR [r15+544]
	add r11, 48
222:
	jmp 220f
219:
	movdqu xmm0, XMMWORD PTR [r11]
	movdqu xmm11, XMMWORD PTR [r15+384]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+512], xmm11
	pxor xmm0, xmm11
	movdqu xmm1, XMMWORD PTR [r11+16]
	movdqu xmm11, XMMWORD PTR [r15+400]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+528], xmm11
	pxor xmm1, xmm11
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	cmp rsi, 10
	je 249f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	cmp rsi, 12
	je 251f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	jmp 252f
251:
252:
	jmp 250f
249:
250:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	pxor xmm10, xmm0
	pxor xmm10, xmm1
	movdqu xmm12, XMMWORD PTR [r15+528]
	add r11, 32
220:
	jmp 218f
217:
	movdqu xmm0, XMMWORD PTR [r11]
	movdqu xmm11, XMMWORD PTR [r15+384]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+512], xmm11
	pxor xmm0, xmm11
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	cmp rsi, 10
	je 253f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 255f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 256f
255:
256:
	jmp 254f
253:
254:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	pxor xmm10, xmm0
	movdqu xmm12, XMMWORD PTR [r15+512]
	add r11, 16
218:
	jmp 216f
215:
216:
	mov rbx, r11
	mov r12, QWORD PTR [r15+248]
	and r12, 15
	je 257f
	xor rax, rax
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rsi, r15
	add rsi, 128
	mov rcx, 0
259:
	movzx eax, BYTE PTR [rbx+rcx*1]
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 259b
	mov rax, 128
	mov BYTE PTR [rsi+rcx*1], al
	movdqu xmm11, XMMWORD PTR [rdi+240]
	pxor xmm12, xmm11
	movdqu xmm0, XMMWORD PTR [r15+128]
	pxor xmm0, xmm12
	mov rsi, r10
	sub rsi, rdi
	shr rsi, 4
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	cmp rsi, 10
	je 260f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 262f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 263f
262:
263:
	jmp 261f
260:
261:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	pxor xmm10, xmm0
	jmp 258f
257:
258:
	movdqu XMMWORD PTR [r15+48], xmm10
	mov rax, QWORD PTR [r15+112]
	bswap rax
	mov rdx, QWORD PTR [r15+120]
	bswap rdx
	mov rcx, rax
	ror rcx, 56
	movabs r8, -256
	and rcx, r8
	mov r8, rdx
	shr r8, 56
	or rcx, r8
	xor rcx, rax
	mov rbx, QWORD PTR [r15+256]
	mov r9, rbx
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -2
	mov r8, rax
	ror r8, 63
	and r8, r11
	mov r9, rdx
	shr r9, 63
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 63
	and r8, r11
	mov r9, rcx
	shr r9, 63
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 63
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 1
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -4
	mov r8, rax
	ror r8, 62
	and r8, r11
	mov r9, rdx
	shr r9, 62
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 62
	and r8, r11
	mov r9, rcx
	shr r9, 62
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 62
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 2
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -16
	mov r8, rax
	ror r8, 60
	and r8, r11
	mov r9, rdx
	shr r9, 60
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 60
	and r8, r11
	mov r9, rcx
	shr r9, 60
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 60
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 3
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -256
	mov r8, rax
	ror r8, 56
	and r8, r11
	mov r9, rdx
	shr r9, 56
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 56
	and r8, r11
	mov r9, rcx
	shr r9, 56
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 56
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 4
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -65536
	mov r8, rax
	ror r8, 48
	and r8, r11
	mov r9, rdx
	shr r9, 48
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 48
	and r8, r11
	mov r9, rcx
	shr r9, 48
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 48
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 5
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -4294967296
	mov r8, rax
	ror r8, 32
	and r8, r11
	mov r9, rdx
	shr r9, 32
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 32
	and r8, r11
	mov r9, rcx
	shr r9, 32
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 32
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+16], rax
	mov QWORD PTR [r15+24], rdx
	mov QWORD PTR [r15+272], rax
	mov QWORD PTR [r15+280], rdx
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	movq xmm12, rax
	movq xmm11, rdx
	punpcklqdq xmm12, xmm11
	pxor xmm10, xmm10
	mov r8, r15
	add r8, 624
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+16], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+32], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+48], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+64], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+80], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+96], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+112], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+128], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+144], xmm8
	cmp rsi, 10
	je 264f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+160], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+176], xmm8
	cmp rsi, 12
	je 266f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+192], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+208], xmm8
	jmp 267f
266:
267:
	jmp 265f
264:
265:
	mov r11, QWORD PTR [r15+208]
	mov r12, QWORD PTR [r15+216]
	mov rbp, r12
	shr r12, 4
	mov r13, 0
	cmp r12, 8
	jb 268f
270:
	mov rax, QWORD PTR [r15+320]
	mov rdx, QWORD PTR [r15+328]
	mov QWORD PTR [r15+336], rax
	mov QWORD PTR [r15+344], rdx
	mov r9, r13
	add r9, 1
	test r9, 1
	jne 271f
273:
	mov rax, QWORD PTR [r15+336]
	bswap rax
	mov rdx, QWORD PTR [r15+344]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	xor r8, r8
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	mov QWORD PTR [r15+336], rax
	bswap rdx
	mov QWORD PTR [r15+344], rdx
	shr r9, 1
	test r9, 1
	je 273b
	jmp 272f
271:
272:
	mov rax, QWORD PTR [r15+336]
	mov rdx, QWORD PTR [r15+344]
	xor rax, QWORD PTR [r15+144]
	xor rdx, QWORD PTR [r15+152]
	movq xmm11, rax
	movq xmm13, rdx
	punpcklqdq xmm11, xmm13
	movdqu XMMWORD PTR [r15+496], xmm11
	movdqu xmm0, XMMWORD PTR [r11]
	movdqu xmm11, XMMWORD PTR [r15+384]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+512], xmm11
	pxor xmm0, xmm11
	movdqu xmm1, XMMWORD PTR [r11+16]
	movdqu xmm11, XMMWORD PTR [r15+400]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+528], xmm11
	pxor xmm1, xmm11
	movdqu xmm2, XMMWORD PTR [r11+32]
	movdqu xmm11, XMMWORD PTR [r15+416]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+544], xmm11
	pxor xmm2, xmm11
	movdqu xmm3, XMMWORD PTR [r11+48]
	movdqu xmm11, XMMWORD PTR [r15+432]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+560], xmm11
	pxor xmm3, xmm11
	movdqu xmm4, XMMWORD PTR [r11+64]
	movdqu xmm11, XMMWORD PTR [r15+448]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+576], xmm11
	pxor xmm4, xmm11
	movdqu xmm5, XMMWORD PTR [r11+80]
	movdqu xmm11, XMMWORD PTR [r15+464]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+592], xmm11
	pxor xmm5, xmm11
	movdqu xmm6, XMMWORD PTR [r11+96]
	movdqu xmm11, XMMWORD PTR [r15+480]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+608], xmm11
	pxor xmm6, xmm11
	movdqu xmm7, XMMWORD PTR [r11+112]
	movdqu xmm11, XMMWORD PTR [r15+496]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+624], xmm11
	pxor xmm7, xmm11
	mov r8, r15
	add r8, 624
	movdqu xmm8, XMMWORD PTR [r10]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	pxor xmm2, xmm8
	pxor xmm3, xmm8
	pxor xmm4, xmm8
	pxor xmm5, xmm8
	pxor xmm6, xmm8
	pxor xmm7, xmm8
	cmp rsi, 10
	je 274f
	cmp rsi, 12
	je 276f
	movdqu xmm8, XMMWORD PTR [r8+208]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [r8+192]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	jmp 277f
276:
277:
	movdqu xmm8, XMMWORD PTR [r8+176]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [r8+160]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	jmp 275f
274:
275:
	movdqu xmm8, XMMWORD PTR [r8+144]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [r8+128]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [r8+112]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [r8+96]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [r8+80]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [r8+64]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [r8+48]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [r8+32]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [r8+16]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi]
	aesdeclast xmm0, xmm8
	aesdeclast xmm1, xmm8
	aesdeclast xmm2, xmm8
	aesdeclast xmm3, xmm8
	aesdeclast xmm4, xmm8
	aesdeclast xmm5, xmm8
	aesdeclast xmm6, xmm8
	aesdeclast xmm7, xmm8
	movdqu xmm11, XMMWORD PTR [r15+512]
	pxor xmm0, xmm11
	movdqu XMMWORD PTR [r11], xmm0
	pxor xmm10, xmm0
	movdqu xmm11, XMMWORD PTR [r15+528]
	pxor xmm1, xmm11
	movdqu XMMWORD PTR [r11+16], xmm1
	pxor xmm10, xmm1
	movdqu xmm11, XMMWORD PTR [r15+544]
	pxor xmm2, xmm11
	movdqu XMMWORD PTR [r11+32], xmm2
	pxor xmm10, xmm2
	movdqu xmm11, XMMWORD PTR [r15+560]
	pxor xmm3, xmm11
	movdqu XMMWORD PTR [r11+48], xmm3
	pxor xmm10, xmm3
	movdqu xmm11, XMMWORD PTR [r15+576]
	pxor xmm4, xmm11
	movdqu XMMWORD PTR [r11+64], xmm4
	pxor xmm10, xmm4
	movdqu xmm11, XMMWORD PTR [r15+592]
	pxor xmm5, xmm11
	movdqu XMMWORD PTR [r11+80], xmm5
	pxor xmm10, xmm5
	movdqu xmm11, XMMWORD PTR [r15+608]
	pxor xmm6, xmm11
	movdqu XMMWORD PTR [r11+96], xmm6
	pxor xmm10, xmm6
	movdqu xmm11, XMMWORD PTR [r15+624]
	pxor xmm7, xmm11
	movdqu XMMWORD PTR [r11+112], xmm7
	pxor xmm10, xmm7
	movdqu xmm12, XMMWORD PTR [r15+624]
	add r11, 128
	add r13, 1
	sub r12, 8
	cmp r12, 8
	jae 270b
	jmp 269f
268:
269:
	test r12, r12
	je 278f
	cmp r12, 1
	je 280f
	cmp r12, 2
	je 282f
	cmp r12, 3
	je 284f
	cmp r12, 4
	je 286f
	cmp r12, 5
	je 288f
	cmp r12, 6
	je 290f
	movdqu xmm0, XMMWORD PTR [r11]
	movdqu xmm11, XMMWORD PTR [r15+384]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+512], xmm11
	pxor xmm0, xmm11
	movdqu xmm1, XMMWORD PTR [r11+16]
	movdqu xmm11, XMMWORD PTR [r15+400]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+528], xmm11
	pxor xmm1, xmm11
	movdqu xmm2, XMMWORD PTR [r11+32]
	movdqu xmm11, XMMWORD PTR [r15+416]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+544], xmm11
	pxor xmm2, xmm11
	movdqu xmm3, XMMWORD PTR [r11+48]
	movdqu xmm11, XMMWORD PTR [r15+432]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+560], xmm11
	pxor xmm3, xmm11
	movdqu xmm4, XMMWORD PTR [r11+64]
	movdqu xmm11, XMMWORD PTR [r15+448]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+576], xmm11
	pxor xmm4, xmm11
	movdqu xmm5, XMMWORD PTR [r11+80]
	movdqu xmm11, XMMWORD PTR [r15+464]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+592], xmm11
	pxor xmm5, xmm11
	movdqu xmm6, XMMWORD PTR [r11+96]
	movdqu xmm11, XMMWORD PTR [r15+480]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+608], xmm11
	pxor xmm6, xmm11
	mov r8, r15
	add r8, 624
	movdqu xmm8, XMMWORD PTR [r10]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	pxor xmm2, xmm8
	pxor xmm3, xmm8
	pxor xmm4, xmm8
	pxor xmm5, xmm8
	pxor xmm6, xmm8
	cmp rsi, 10
	je 292f
	cmp rsi, 12
	je 294f
	movdqu xmm8, XMMWORD PTR [r8+208]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [r8+192]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	jmp 295f
294:
295:
	movdqu xmm8, XMMWORD PTR [r8+176]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [r8+160]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	jmp 293f
292:
293:
	movdqu xmm8, XMMWORD PTR [r8+144]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [r8+128]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [r8+112]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [r8+96]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [r8+80]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [r8+64]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [r8+48]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [r8+32]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [r8+16]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	movdqu xmm8, XMMWORD PTR [rdi]
	aesdeclast xmm0, xmm8
	aesdeclast xmm1, xmm8
	aesdeclast xmm2, xmm8
	aesdeclast xmm3, xmm8
	aesdeclast xmm4, xmm8
	aesdeclast xmm5, xmm8
	aesdeclast xmm6, xmm8
	movdqu xmm11, XMMWORD PTR [r15+512]
	pxor xmm0, xmm11
	movdqu XMMWORD PTR [r11], xmm0
	pxor xmm10, xmm0
	movdqu xmm11, XMMWORD PTR [r15+528]
	pxor xmm1, xmm11
	movdqu XMMWORD PTR [r11+16], xmm1
	pxor xmm10, xmm1
	movdqu xmm11, XMMWORD PTR [r15+544]
	pxor xmm2, xmm11
	movdqu XMMWORD PTR [r11+32], xmm2
	pxor xmm10, xmm2
	movdqu xmm11, XMMWORD PTR [r15+560]
	pxor xmm3, xmm11
	movdqu XMMWORD PTR [r11+48], xmm3
	pxor xmm10, xmm3
	movdqu xmm11, XMMWORD PTR [r15+576]
	pxor xmm4, xmm11
	movdqu XMMWORD PTR [r11+64], xmm4
	pxor xmm10, xmm4
	movdqu xmm11, XMMWORD PTR [r15+592]
	pxor xmm5, xmm11
	movdqu XMMWORD PTR [r11+80], xmm5
	pxor xmm10, xmm5
	movdqu xmm11, XMMWORD PTR [r15+608]
	pxor xmm6, xmm11
	movdqu XMMWORD PTR [r11+96], xmm6
	pxor xmm10, xmm6
	movdqu xmm12, XMMWORD PTR [r15+608]
	add r11, 112
	jmp 291f
290:
	movdqu xmm0, XMMWORD PTR [r11]
	movdqu xmm11, XMMWORD PTR [r15+384]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+512], xmm11
	pxor xmm0, xmm11
	movdqu xmm1, XMMWORD PTR [r11+16]
	movdqu xmm11, XMMWORD PTR [r15+400]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+528], xmm11
	pxor xmm1, xmm11
	movdqu xmm2, XMMWORD PTR [r11+32]
	movdqu xmm11, XMMWORD PTR [r15+416]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+544], xmm11
	pxor xmm2, xmm11
	movdqu xmm3, XMMWORD PTR [r11+48]
	movdqu xmm11, XMMWORD PTR [r15+432]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+560], xmm11
	pxor xmm3, xmm11
	movdqu xmm4, XMMWORD PTR [r11+64]
	movdqu xmm11, XMMWORD PTR [r15+448]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+576], xmm11
	pxor xmm4, xmm11
	movdqu xmm5, XMMWORD PTR [r11+80]
	movdqu xmm11, XMMWORD PTR [r15+464]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+592], xmm11
	pxor xmm5, xmm11
	mov r8, r15
	add r8, 624
	movdqu xmm8, XMMWORD PTR [r10]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	pxor xmm2, xmm8
	pxor xmm3, xmm8
	pxor xmm4, xmm8
	pxor xmm5, xmm8
	cmp rsi, 10
	je 296f
	cmp rsi, 12
	je 298f
	movdqu xmm8, XMMWORD PTR [r8+208]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [r8+192]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	jmp 299f
298:
299:
	movdqu xmm8, XMMWORD PTR [r8+176]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [r8+160]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	jmp 297f
296:
297:
	movdqu xmm8, XMMWORD PTR [r8+144]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [r8+128]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [r8+112]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [r8+96]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [r8+80]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [r8+64]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [r8+48]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [r8+32]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [r8+16]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	movdqu xmm8, XMMWORD PTR [rdi]
	aesdeclast xmm0, xmm8
	aesdeclast xmm1, xmm8
	aesdeclast xmm2, xmm8
	aesdeclast xmm3, xmm8
	aesdeclast xmm4, xmm8
	aesdeclast xmm5, xmm8
	movdqu xmm11, XMMWORD PTR [r15+512]
	pxor xmm0, xmm11
	movdqu XMMWORD PTR [r11], xmm0
	pxor xmm10, xmm0
	movdqu xmm11, XMMWORD PTR [r15+528]
	pxor xmm1, xmm11
	movdqu XMMWORD PTR [r11+16], xmm1
	pxor xmm10, xmm1
	movdqu xmm11, XMMWORD PTR [r15+544]
	pxor xmm2, xmm11
	movdqu XMMWORD PTR [r11+32], xmm2
	pxor xmm10, xmm2
	movdqu xmm11, XMMWORD PTR [r15+560]
	pxor xmm3, xmm11
	movdqu XMMWORD PTR [r11+48], xmm3
	pxor xmm10, xmm3
	movdqu xmm11, XMMWORD PTR [r15+576]
	pxor xmm4, xmm11
	movdqu XMMWORD PTR [r11+64], xmm4
	pxor xmm10, xmm4
	movdqu xmm11, XMMWORD PTR [r15+592]
	pxor xmm5, xmm11
	movdqu XMMWORD PTR [r11+80], xmm5
	pxor xmm10, xmm5
	movdqu xmm12, XMMWORD PTR [r15+592]
	add r11, 96
291:
	jmp 289f
288:
	movdqu xmm0, XMMWORD PTR [r11]
	movdqu xmm11, XMMWORD PTR [r15+384]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+512], xmm11
	pxor xmm0, xmm11
	movdqu xmm1, XMMWORD PTR [r11+16]
	movdqu xmm11, XMMWORD PTR [r15+400]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+528], xmm11
	pxor xmm1, xmm11
	movdqu xmm2, XMMWORD PTR [r11+32]
	movdqu xmm11, XMMWORD PTR [r15+416]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+544], xmm11
	pxor xmm2, xmm11
	movdqu xmm3, XMMWORD PTR [r11+48]
	movdqu xmm11, XMMWORD PTR [r15+432]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+560], xmm11
	pxor xmm3, xmm11
	movdqu xmm4, XMMWORD PTR [r11+64]
	movdqu xmm11, XMMWORD PTR [r15+448]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+576], xmm11
	pxor xmm4, xmm11
	mov r8, r15
	add r8, 624
	movdqu xmm8, XMMWORD PTR [r10]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	pxor xmm2, xmm8
	pxor xmm3, xmm8
	pxor xmm4, xmm8
	cmp rsi, 10
	je 2100f
	cmp rsi, 12
	je 2102f
	movdqu xmm8, XMMWORD PTR [r8+208]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [r8+192]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	jmp 2103f
2102:
2103:
	movdqu xmm8, XMMWORD PTR [r8+176]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [r8+160]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	jmp 2101f
2100:
2101:
	movdqu xmm8, XMMWORD PTR [r8+144]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [r8+128]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [r8+112]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [r8+96]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [r8+80]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [r8+64]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [r8+48]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [r8+32]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [r8+16]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	movdqu xmm8, XMMWORD PTR [rdi]
	aesdeclast xmm0, xmm8
	aesdeclast xmm1, xmm8
	aesdeclast xmm2, xmm8
	aesdeclast xmm3, xmm8
	aesdeclast xmm4, xmm8
	movdqu xmm11, XMMWORD PTR [r15+512]
	pxor xmm0, xmm11
	movdqu XMMWORD PTR [r11], xmm0
	pxor xmm10, xmm0
	movdqu xmm11, XMMWORD PTR [r15+528]
	pxor xmm1, xmm11
	movdqu XMMWORD PTR [r11+16], xmm1
	pxor xmm10, xmm1
	movdqu xmm11, XMMWORD PTR [r15+544]
	pxor xmm2, xmm11
	movdqu XMMWORD PTR [r11+32], xmm2
	pxor xmm10, xmm2
	movdqu xmm11, XMMWORD PTR [r15+560]
	pxor xmm3, xmm11
	movdqu XMMWORD PTR [r11+48], xmm3
	pxor xmm10, xmm3
	movdqu xmm11, XMMWORD PTR [r15+576]
	pxor xmm4, xmm11
	movdqu XMMWORD PTR [r11+64], xmm4
	pxor xmm10, xmm4
	movdqu xmm12, XMMWORD PTR [r15+576]
	add r11, 80
289:
	jmp 287f
286:
	movdqu xmm0, XMMWORD PTR [r11]
	movdqu xmm11, XMMWORD PTR [r15+384]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+512], xmm11
	pxor xmm0, xmm11
	movdqu xmm1, XMMWORD PTR [r11+16]
	movdqu xmm11, XMMWORD PTR [r15+400]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+528], xmm11
	pxor xmm1, xmm11
	movdqu xmm2, XMMWORD PTR [r11+32]
	movdqu xmm11, XMMWORD PTR [r15+416]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+544], xmm11
	pxor xmm2, xmm11
	movdqu xmm3, XMMWORD PTR [r11+48]
	movdqu xmm11, XMMWORD PTR [r15+432]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+560], xmm11
	pxor xmm3, xmm11
	mov r8, r15
	add r8, 624
	movdqu xmm8, XMMWORD PTR [r10]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	pxor xmm2, xmm8
	pxor xmm3, xmm8
	cmp rsi, 10
	je 2104f
	cmp rsi, 12
	je 2106f
	movdqu xmm8, XMMWORD PTR [r8+208]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [r8+192]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	jmp 2107f
2106:
2107:
	movdqu xmm8, XMMWORD PTR [r8+176]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [r8+160]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	jmp 2105f
2104:
2105:
	movdqu xmm8, XMMWORD PTR [r8+144]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [r8+128]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [r8+112]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [r8+96]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [r8+80]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [r8+64]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [r8+48]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [r8+32]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [r8+16]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	movdqu xmm8, XMMWORD PTR [rdi]
	aesdeclast xmm0, xmm8
	aesdeclast xmm1, xmm8
	aesdeclast xmm2, xmm8
	aesdeclast xmm3, xmm8
	movdqu xmm11, XMMWORD PTR [r15+512]
	pxor xmm0, xmm11
	movdqu XMMWORD PTR [r11], xmm0
	pxor xmm10, xmm0
	movdqu xmm11, XMMWORD PTR [r15+528]
	pxor xmm1, xmm11
	movdqu XMMWORD PTR [r11+16], xmm1
	pxor xmm10, xmm1
	movdqu xmm11, XMMWORD PTR [r15+544]
	pxor xmm2, xmm11
	movdqu XMMWORD PTR [r11+32], xmm2
	pxor xmm10, xmm2
	movdqu xmm11, XMMWORD PTR [r15+560]
	pxor xmm3, xmm11
	movdqu XMMWORD PTR [r11+48], xmm3
	pxor xmm10, xmm3
	movdqu xmm12, XMMWORD PTR [r15+560]
	add r11, 64
287:
	jmp 285f
284:
	movdqu xmm0, XMMWORD PTR [r11]
	movdqu xmm11, XMMWORD PTR [r15+384]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+512], xmm11
	pxor xmm0, xmm11
	movdqu xmm1, XMMWORD PTR [r11+16]
	movdqu xmm11, XMMWORD PTR [r15+400]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+528], xmm11
	pxor xmm1, xmm11
	movdqu xmm2, XMMWORD PTR [r11+32]
	movdqu xmm11, XMMWORD PTR [r15+416]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+544], xmm11
	pxor xmm2, xmm11
	mov r8, r15
	add r8, 624
	movdqu xmm8, XMMWORD PTR [r10]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	pxor xmm2, xmm8
	cmp rsi, 10
	je 2108f
	cmp rsi, 12
	je 2110f
	movdqu xmm8, XMMWORD PTR [r8+208]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [r8+192]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	jmp 2111f
2110:
2111:
	movdqu xmm8, XMMWORD PTR [r8+176]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [r8+160]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	jmp 2109f
2108:
2109:
	movdqu xmm8, XMMWORD PTR [r8+144]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [r8+128]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [r8+112]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [r8+96]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [r8+80]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [r8+64]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [r8+48]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [r8+32]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [r8+16]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	movdqu xmm8, XMMWORD PTR [rdi]
	aesdeclast xmm0, xmm8
	aesdeclast xmm1, xmm8
	aesdeclast xmm2, xmm8
	movdqu xmm11, XMMWORD PTR [r15+512]
	pxor xmm0, xmm11
	movdqu XMMWORD PTR [r11], xmm0
	pxor xmm10, xmm0
	movdqu xmm11, XMMWORD PTR [r15+528]
	pxor xmm1, xmm11
	movdqu XMMWORD PTR [r11+16], xmm1
	pxor xmm10, xmm1
	movdqu xmm11, XMMWORD PTR [r15+544]
	pxor xmm2, xmm11
	movdqu XMMWORD PTR [r11+32], xmm2
	pxor xmm10, xmm2
	movdqu xmm12, XMMWORD PTR [r15+544]
	add r11, 48
285:
	jmp 283f
282:
	movdqu xmm0, XMMWORD PTR [r11]
	movdqu xmm11, XMMWORD PTR [r15+384]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+512], xmm11
	pxor xmm0, xmm11
	movdqu xmm1, XMMWORD PTR [r11+16]
	movdqu xmm11, XMMWORD PTR [r15+400]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+528], xmm11
	pxor xmm1, xmm11
	mov r8, r15
	add r8, 624
	movdqu xmm8, XMMWORD PTR [r10]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	cmp rsi, 10
	je 2112f
	cmp rsi, 12
	je 2114f
	movdqu xmm8, XMMWORD PTR [r8+208]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [r8+192]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	jmp 2115f
2114:
2115:
	movdqu xmm8, XMMWORD PTR [r8+176]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [r8+160]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	jmp 2113f
2112:
2113:
	movdqu xmm8, XMMWORD PTR [r8+144]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [r8+128]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [r8+112]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [r8+96]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [r8+80]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [r8+64]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [r8+48]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [r8+32]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [r8+16]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	movdqu xmm8, XMMWORD PTR [rdi]
	aesdeclast xmm0, xmm8
	aesdeclast xmm1, xmm8
	movdqu xmm11, XMMWORD PTR [r15+512]
	pxor xmm0, xmm11
	movdqu XMMWORD PTR [r11], xmm0
	pxor xmm10, xmm0
	movdqu xmm11, XMMWORD PTR [r15+528]
	pxor xmm1, xmm11
	movdqu XMMWORD PTR [r11+16], xmm1
	pxor xmm10, xmm1
	movdqu xmm12, XMMWORD PTR [r15+528]
	add r11, 32
283:
	jmp 281f
280:
	movdqu xmm0, XMMWORD PTR [r11]
	movdqu xmm11, XMMWORD PTR [r15+384]
	pxor xmm11, xmm12
	movdqu XMMWORD PTR [r15+512], xmm11
	pxor xmm0, xmm11
	mov r8, r15
	add r8, 624
	movdqu xmm8, XMMWORD PTR [r10]
	pxor xmm0, xmm8
	cmp rsi, 10
	je 2116f
	cmp rsi, 12
	je 2118f
	movdqu xmm8, XMMWORD PTR [r8+208]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+192]
	aesdec xmm0, xmm8
	jmp 2119f
2118:
2119:
	movdqu xmm8, XMMWORD PTR [r8+176]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+160]
	aesdec xmm0, xmm8
	jmp 2117f
2116:
2117:
	movdqu xmm8, XMMWORD PTR [r8+144]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+128]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+112]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+96]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+80]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+64]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+48]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+32]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+16]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi]
	aesdeclast xmm0, xmm8
	movdqu xmm11, XMMWORD PTR [r15+512]
	pxor xmm0, xmm11
	movdqu XMMWORD PTR [r11], xmm0
	pxor xmm10, xmm0
	movdqu xmm12, XMMWORD PTR [r15+512]
	add r11, 16
281:
	jmp 279f
278:
279:
	mov rbx, r11
	mov r12, rbp
	and r12, 15
	je 2120f
	movdqu xmm11, XMMWORD PTR [rdi+240]
	pxor xmm12, xmm11
	movdqa xmm0, xmm12
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	cmp rsi, 10
	je 2122f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 2124f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 2125f
2124:
2125:
	jmp 2123f
2122:
2123:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	movdqu XMMWORD PTR [r15+112], xmm0
	mov rcx, 0
2126:
	movzx eax, BYTE PTR [rbx+rcx*1]
	movzx edx, BYTE PTR [r15+rcx*1+112]
	xor rax, rdx
	mov BYTE PTR [rbx+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 2126b
	xor rax, rax
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rsi, r15
	add rsi, 128
	mov rcx, 0
2127:
	movzx eax, BYTE PTR [rbx+rcx*1]
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 2127b
	mov rax, 128
	mov BYTE PTR [rsi+rcx*1], al
	movdqu xmm11, XMMWORD PTR [r15+128]
	pxor xmm10, xmm11
	jmp 2121f
2120:
2121:
	movdqa xmm0, xmm10
	pxor xmm0, xmm12
	movdqu xmm11, XMMWORD PTR [r15+64]
	pxor xmm0, xmm11
	mov rsi, r10
	sub rsi, rdi
	shr rsi, 4
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	cmp rsi, 10
	je 2128f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 2130f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 2131f
2130:
2131:
	jmp 2129f
2128:
2129:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	movdqu xmm11, XMMWORD PTR [r15+48]
	pxor xmm0, xmm11
	movdqu XMMWORD PTR [r15+128], xmm0
	mov rbx, QWORD PTR [r15+304]
	mov rsi, r15
	mov r12, QWORD PTR [r15+224]
	mov rcx, 0
2132:
	movzx eax, BYTE PTR [rbx+rcx*1]
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 2132b
	xor rdx, rdx
	mov rcx, 0
	mov r12, QWORD PTR [r15+224]
2133:
	movzx eax, BYTE PTR [r15+rcx*1]
	movzx r8d, BYTE PTR [r15+rcx*1+128]
	xor rax, r8
	or rdx, rax
	add rcx, 1
	cmp rcx, r12
	jne 2133b
	sub rdx, 1
	shr rdx, 63
	mov QWORD PTR [r15], rdx
	mov rbx, QWORD PTR [r15+208]
	mov r12, QWORD PTR [r15+216]
	xor rdx, rdx
	sub rdx, QWORD PTR [r15]
	movq xmm6, rdx
	punpcklqdq xmm6, xmm6
	mov rcx, 0
	mov r8, r12
	shr r8, 4
	test r8, r8
	je 2134f
2136:
	movdqu xmm7, XMMWORD PTR [rbx+rcx*1]
	pand xmm7, xmm6
	movdqu XMMWORD PTR [rbx+rcx*1], xmm7
	add rcx, 16
	sub r8, 1
	jne 2136b
	jmp 2135f
2134:
2135:
	cmp rcx, r12
	je 2137f
2139:
	movzx eax, BYTE PTR [rbx+rcx*1]
	and rax, rdx
	mov BYTE PTR [rbx+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 2139b
	jmp 2138f
2137:
2138:
	mov rax, QWORD PTR [r15]
	mov rbx, QWORD PTR [r15+160]
	mov rbp, QWORD PTR [r15+168]
	mov r12, QWORD PTR [r15+176]
	mov r13, QWORD PTR [r15+184]
	mov r14, QWORD PTR [r15+192]
	mov r15, QWORD PTR [r15+200]
	lea rsp, [rsp+896]
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
	lea rsp, [rsp-896]
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
	lea rsp, [rsp+896]
	lea rsp, [rsp+8]
	mov eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	ret
	.p2align 6

vg_aes_ocb_seal:
	lea rsp, [rsp-3632]
	mov rax, QWORD PTR [rsp+3640]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3648]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+3656]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+3664]
	mov QWORD PTR [rsp+32], rax
	mov rax, rsp
	add rax, 48
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+40]
	mov QWORD PTR [rax+160], rbx
	mov QWORD PTR [rax+168], rbp
	mov QWORD PTR [rax+176], r12
	mov QWORD PTR [rax+184], r13
	mov QWORD PTR [rax+192], r14
	mov QWORD PTR [rax+200], r15
	mov r15, rax
	mov r14, rdi
	mov QWORD PTR [r15+232], rsi
	mov QWORD PTR [r15+288], rdx
	mov QWORD PTR [r15+296], rcx
	mov QWORD PTR [r15+240], r8
	mov QWORD PTR [r15+248], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+208], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r15+216], rax
	mov rax, QWORD PTR [rsp+32]
	mov QWORD PTR [r15+224], rax
	mov rax, QWORD PTR [rsp+24]
	mov QWORD PTR [r15+304], rax
	mov rax, QWORD PTR [r14+240]
	bswap rax
	mov rdx, QWORD PTR [r14+248]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	xor r8, r8
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	mov QWORD PTR [r15+64], rax
	bswap rdx
	mov QWORD PTR [r15+72], rdx
	mov rax, QWORD PTR [r15+64]
	bswap rax
	mov rdx, QWORD PTR [r15+72]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	xor r8, r8
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	mov QWORD PTR [r15+80], rax
	bswap rdx
	mov QWORD PTR [r15+88], rdx
	xor rax, rax
	mov QWORD PTR [r15+32], rax
	mov QWORD PTR [r15+40], rax
	mov rax, QWORD PTR [r15+80]
	mov rdx, QWORD PTR [r15+88]
	mov QWORD PTR [r15+2560], rax
	mov QWORD PTR [r15+2568], rdx
	mov r9, QWORD PTR [r15+216]
	mov rax, QWORD PTR [r15+248]
	or r9, rax
	shr r9, 5
	mov r10, r15
	add r10, 2560
	mov r11, 1
	movabs rsi, 157587932685088877
	test r9, r9
	je 20f
22:
	add r11, r11
	mov rax, r11
	mul rsi
	shr rax, 58
	ror rax, 60
	add rax, r15
	mov rdi, rax
	mov rax, QWORD PTR [r10]
	bswap rax
	mov rdx, QWORD PTR [r10+8]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	xor r8, r8
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	mov QWORD PTR [rdi+2560], rax
	bswap rdx
	mov QWORD PTR [rdi+2568], rdx
	mov r10, rdi
	add r10, 2560
	shr r9, 1
	test r9, r9
	jne 22b
	jmp 21f
20:
21:
	xor rax, rax
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rax
	mov rbx, QWORD PTR [r15+288]
	mov r12, QWORD PTR [r15+296]
	mov rsi, r15
	add rsi, 128
	sub rsi, r12
	mov rcx, 0
23:
	movzx eax, BYTE PTR [rbx+rcx*1]
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 23b
	mov rax, 1
	mov BYTE PTR [rsi-1], al
	mov rax, QWORD PTR [r15+224]
	and rax, 15
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx ecx, BYTE PTR [r15+112]
	or rcx, rax
	mov BYTE PTR [r15+112], cl
	movzx eax, BYTE PTR [r15+127]
	mov rcx, rax
	and rcx, 63
	mov QWORD PTR [r15+256], rcx
	and rax, 192
	mov BYTE PTR [r15+127], al
	mov rdx, r15
	add rdx, 112
	mov rcx, 1
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks}
	mov rax, QWORD PTR [r15+112]
	bswap rax
	mov rdx, QWORD PTR [r15+120]
	bswap rdx
	mov rcx, rax
	ror rcx, 56
	movabs r8, -256
	and rcx, r8
	mov r8, rdx
	shr r8, 56
	or rcx, r8
	xor rcx, rax
	mov rbx, QWORD PTR [r15+256]
	mov r9, rbx
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -2
	mov r8, rax
	ror r8, 63
	and r8, r11
	mov r9, rdx
	shr r9, 63
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 63
	and r8, r11
	mov r9, rcx
	shr r9, 63
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 63
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 1
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -4
	mov r8, rax
	ror r8, 62
	and r8, r11
	mov r9, rdx
	shr r9, 62
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 62
	and r8, r11
	mov r9, rcx
	shr r9, 62
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 62
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 2
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -16
	mov r8, rax
	ror r8, 60
	and r8, r11
	mov r9, rdx
	shr r9, 60
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 60
	and r8, r11
	mov r9, rcx
	shr r9, 60
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 60
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 3
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -256
	mov r8, rax
	ror r8, 56
	and r8, r11
	mov r9, rdx
	shr r9, 56
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 56
	and r8, r11
	mov r9, rcx
	shr r9, 56
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 56
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 4
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -65536
	mov r8, rax
	ror r8, 48
	and r8, r11
	mov r9, rdx
	shr r9, 48
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 48
	and r8, r11
	mov r9, rcx
	shr r9, 48
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 48
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 5
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -4294967296
	mov r8, rax
	ror r8, 32
	and r8, r11
	mov r9, rdx
	shr r9, 32
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 32
	and r8, r11
	mov r9, rcx
	shr r9, 32
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 32
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+16], rax
	mov QWORD PTR [r15+24], rdx
	mov QWORD PTR [r15+272], rax
	mov QWORD PTR [r15+280], rdx
	xor rax, rax
	mov QWORD PTR [r15+48], rax
	mov QWORD PTR [r15+56], rax
	xor rax, rax
	mov QWORD PTR [r15+144], rax
	mov QWORD PTR [r15+152], rax
	mov rbx, QWORD PTR [r15+240]
	mov rax, QWORD PTR [r15+248]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+112], rcx
	shr rax, 4
	mov QWORD PTR [r15+248], rax
	mov rbp, 1
	test rax, rax
	je 24f
26:
	mov r12, QWORD PTR [r15+248]
	cmp r12, 8
	jb 27f
	mov r12, 8
	jmp 28f
27:
28:
	mov r13, 0
	mov rsi, r15
	add rsi, 384
29:
	mov rax, rbp
	mov rcx, 0
	sub rcx, rbp
	and rax, rcx
	movabs rcx, 157587932685088877
	mul rcx
	shr rax, 58
	ror rax, 60
	mov rcx, r15
	add rcx, rax
	mov rax, QWORD PTR [r15+144]
	mov rdx, QWORD PTR [r15+152]
	xor rax, QWORD PTR [rcx+2560]
	xor rdx, QWORD PTR [rcx+2568]
	mov QWORD PTR [r15+144], rax
	mov QWORD PTR [r15+152], rdx
	mov rax, QWORD PTR [rbx]
	mov rdx, QWORD PTR [rbx+8]
	xor rax, QWORD PTR [r15+144]
	xor rdx, QWORD PTR [r15+152]
	mov QWORD PTR [rsi], rax
	mov QWORD PTR [rsi+8], rdx
	add rsi, 16
	add rbx, 16
	add rbp, 1
	add r13, 1
	cmp r13, r12
	jne 29b
	mov rdx, r15
	add rdx, 384
	mov rcx, r12
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks}
	mov r13, 0
	mov rsi, r15
	add rsi, 384
210:
	mov rax, QWORD PTR [r15+48]
	mov rdx, QWORD PTR [r15+56]
	xor rax, QWORD PTR [rsi]
	xor rdx, QWORD PTR [rsi+8]
	mov QWORD PTR [r15+48], rax
	mov QWORD PTR [r15+56], rdx
	add rsi, 16
	add r13, 1
	cmp r13, r12
	jne 210b
	mov rax, QWORD PTR [r15+248]
	sub rax, r12
	mov QWORD PTR [r15+248], rax
	jne 26b
	jmp 25f
24:
25:
	mov r12, QWORD PTR [r15+112]
	test r12, r12
	je 211f
	mov rax, QWORD PTR [r15+144]
	mov rdx, QWORD PTR [r15+152]
	xor rax, QWORD PTR [r14+240]
	xor rdx, QWORD PTR [r14+248]
	mov QWORD PTR [r15+144], rax
	mov QWORD PTR [r15+152], rdx
	xor rax, rax
	mov QWORD PTR [r15+384], rax
	mov QWORD PTR [r15+392], rax
	mov rsi, r15
	add rsi, 384
	mov rcx, 0
213:
	movzx eax, BYTE PTR [rbx+rcx*1]
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 213b
	mov rax, 128
	mov BYTE PTR [rsi+rcx*1], al
	mov rax, QWORD PTR [r15+384]
	mov rdx, QWORD PTR [r15+392]
	xor rax, QWORD PTR [r15+144]
	xor rdx, QWORD PTR [r15+152]
	mov QWORD PTR [r15+384], rax
	mov QWORD PTR [r15+392], rdx
	mov rdx, r15
	add rdx, 384
	mov rcx, 1
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks}
	mov rax, QWORD PTR [r15+48]
	mov rdx, QWORD PTR [r15+56]
	xor rax, QWORD PTR [r15+384]
	xor rdx, QWORD PTR [r15+392]
	mov QWORD PTR [r15+48], rax
	mov QWORD PTR [r15+56], rdx
	jmp 212f
211:
212:
	mov r13, QWORD PTR [r15+216]
	shr r13, 4
	test r13, r13
	je 214f
	mov rbx, QWORD PTR [r15+208]
	mov r12, r13
	mov rbp, 1
	movdqu xmm0, XMMWORD PTR [r15+16]
	movdqu xmm1, XMMWORD PTR [r15+32]
	movdqu xmm4, XMMWORD PTR [r15+2560]
	movdqu xmm5, XMMWORD PTR [r15+2576]
	cmp r12, 4
	jb 216f
218:
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm1, xmm3
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	pxor xmm0, xmm5
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm1, xmm3
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm1, xmm3
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	mov rax, rbp
	mov rcx, 0
	sub rcx, rbp
	and rax, rcx
	movabs rcx, 157587932685088877
	mul rcx
	shr rax, 58
	ror rax, 60
	mov rcx, r15
	add rcx, rax
	movdqu xmm2, XMMWORD PTR [rcx+2560]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm1, xmm3
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	sub r12, 4
	cmp r12, 4
	jae 218b
	jmp 217f
216:
217:
	test r12, r12
	je 219f
221:
	mov rax, rbp
	mov rcx, 0
	sub rcx, rbp
	and rax, rcx
	movabs rcx, 157587932685088877
	mul rcx
	shr rax, 58
	ror rax, 60
	mov rcx, r15
	add rcx, rax
	movdqu xmm2, XMMWORD PTR [rcx+2560]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm1, xmm3
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	sub r12, 1
	jne 221b
	jmp 220f
219:
220:
	movdqu XMMWORD PTR [r15+16], xmm0
	movdqu XMMWORD PTR [r15+32], xmm1
	mov rdx, QWORD PTR [r15+208]
	mov rcx, r13
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks}
	mov rax, QWORD PTR [r15+272]
	mov rdx, QWORD PTR [r15+280]
	mov QWORD PTR [r15+16], rax
	mov QWORD PTR [r15+24], rdx
	mov rbx, QWORD PTR [r15+208]
	mov r12, r13
	mov rbp, 1
	movdqu xmm0, XMMWORD PTR [r15+16]
	movdqu xmm1, XMMWORD PTR [r15+32]
	movdqu xmm4, XMMWORD PTR [r15+2560]
	movdqu xmm5, XMMWORD PTR [r15+2576]
	cmp r12, 4
	jb 222f
224:
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	pxor xmm0, xmm5
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	mov rax, rbp
	mov rcx, 0
	sub rcx, rbp
	and rax, rcx
	movabs rcx, 157587932685088877
	mul rcx
	shr rax, 58
	ror rax, 60
	mov rcx, r15
	add rcx, rax
	movdqu xmm2, XMMWORD PTR [rcx+2560]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	sub r12, 4
	cmp r12, 4
	jae 224b
	jmp 223f
222:
223:
	test r12, r12
	je 225f
227:
	mov rax, rbp
	mov rcx, 0
	sub rcx, rbp
	and rax, rcx
	movabs rcx, 157587932685088877
	mul rcx
	shr rax, 58
	ror rax, 60
	mov rcx, r15
	add rcx, rax
	movdqu xmm2, XMMWORD PTR [rcx+2560]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	sub r12, 1
	jne 227b
	jmp 226f
225:
226:
	movdqu XMMWORD PTR [r15+16], xmm0
	movdqu XMMWORD PTR [r15+32], xmm1
	jmp 215f
214:
215:
	mov rbx, QWORD PTR [r15+208]
	mov rax, QWORD PTR [r15+216]
	mov r12, rax
	and r12, 15
	sub rax, r12
	add rbx, rax
	test r12, r12
	je 228f
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	xor rax, QWORD PTR [r14+240]
	xor rdx, QWORD PTR [r14+248]
	mov QWORD PTR [r15+16], rax
	mov QWORD PTR [r15+24], rdx
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rdx
	mov rdx, r15
	add rdx, 112
	mov rcx, 1
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks}
	xor rax, rax
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rsi, r15
	add rsi, 128
	mov rcx, 0
230:
	movzx eax, BYTE PTR [rbx+rcx*1]
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 230b
	mov rax, 128
	mov BYTE PTR [rsi+rcx*1], al
	mov rax, QWORD PTR [r15+32]
	mov rdx, QWORD PTR [r15+40]
	xor rax, QWORD PTR [r15+128]
	xor rdx, QWORD PTR [r15+136]
	mov QWORD PTR [r15+32], rax
	mov QWORD PTR [r15+40], rdx
	mov rcx, 0
231:
	movzx eax, BYTE PTR [rbx+rcx*1]
	movzx edx, BYTE PTR [r15+rcx*1+112]
	xor rax, rdx
	mov BYTE PTR [rbx+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 231b
	jmp 229f
228:
229:
	mov rax, QWORD PTR [r15+32]
	mov rdx, QWORD PTR [r15+40]
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rdx
	mov rax, QWORD PTR [r15+112]
	mov rdx, QWORD PTR [r15+120]
	xor rax, QWORD PTR [r15+16]
	xor rdx, QWORD PTR [r15+24]
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rdx
	mov rax, QWORD PTR [r15+112]
	mov rdx, QWORD PTR [r15+120]
	xor rax, QWORD PTR [r15+64]
	xor rdx, QWORD PTR [r15+72]
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rdx
	mov rdx, r15
	add rdx, 112
	mov rcx, 1
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks}
	mov rax, QWORD PTR [r15+112]
	mov rdx, QWORD PTR [r15+120]
	mov QWORD PTR [r15], rax
	mov QWORD PTR [r15+8], rdx
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	xor rax, QWORD PTR [r15+48]
	xor rdx, QWORD PTR [r15+56]
	mov QWORD PTR [r15], rax
	mov QWORD PTR [r15+8], rdx
	mov rbx, r15
	mov rsi, QWORD PTR [r15+304]
	mov r12, QWORD PTR [r15+224]
	mov rcx, 0
232:
	movzx eax, BYTE PTR [rbx+rcx*1]
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 232b
	mov rbx, QWORD PTR [r15+160]
	mov rbp, QWORD PTR [r15+168]
	mov r12, QWORD PTR [r15+176]
	mov r13, QWORD PTR [r15+184]
	mov r14, QWORD PTR [r15+192]
	mov r15, QWORD PTR [r15+200]
	lea rsp, [rsp+3632]
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
	lea rsp, [rsp-3632]
	movdqu XMMWORD PTR [rsp+3616], xmm0
	movdqu XMMWORD PTR [rsp+3600], xmm0
	movdqu XMMWORD PTR [rsp+3584], xmm0
	movdqu XMMWORD PTR [rsp+3568], xmm0
	movdqu XMMWORD PTR [rsp+3552], xmm0
	movdqu XMMWORD PTR [rsp+3536], xmm0
	movdqu XMMWORD PTR [rsp+3520], xmm0
	movdqu XMMWORD PTR [rsp+3504], xmm0
	movdqu XMMWORD PTR [rsp+3488], xmm0
	movdqu XMMWORD PTR [rsp+3472], xmm0
	movdqu XMMWORD PTR [rsp+3456], xmm0
	movdqu XMMWORD PTR [rsp+3440], xmm0
	movdqu XMMWORD PTR [rsp+3424], xmm0
	movdqu XMMWORD PTR [rsp+3408], xmm0
	movdqu XMMWORD PTR [rsp+3392], xmm0
	movdqu XMMWORD PTR [rsp+3376], xmm0
	movdqu XMMWORD PTR [rsp+3360], xmm0
	movdqu XMMWORD PTR [rsp+3344], xmm0
	movdqu XMMWORD PTR [rsp+3328], xmm0
	movdqu XMMWORD PTR [rsp+3312], xmm0
	movdqu XMMWORD PTR [rsp+3296], xmm0
	movdqu XMMWORD PTR [rsp+3280], xmm0
	movdqu XMMWORD PTR [rsp+3264], xmm0
	movdqu XMMWORD PTR [rsp+3248], xmm0
	movdqu XMMWORD PTR [rsp+3232], xmm0
	movdqu XMMWORD PTR [rsp+3216], xmm0
	movdqu XMMWORD PTR [rsp+3200], xmm0
	movdqu XMMWORD PTR [rsp+3184], xmm0
	movdqu XMMWORD PTR [rsp+3168], xmm0
	movdqu XMMWORD PTR [rsp+3152], xmm0
	movdqu XMMWORD PTR [rsp+3136], xmm0
	movdqu XMMWORD PTR [rsp+3120], xmm0
	movdqu XMMWORD PTR [rsp+3104], xmm0
	movdqu XMMWORD PTR [rsp+3088], xmm0
	movdqu XMMWORD PTR [rsp+3072], xmm0
	movdqu XMMWORD PTR [rsp+3056], xmm0
	movdqu XMMWORD PTR [rsp+3040], xmm0
	movdqu XMMWORD PTR [rsp+3024], xmm0
	movdqu XMMWORD PTR [rsp+3008], xmm0
	movdqu XMMWORD PTR [rsp+2992], xmm0
	movdqu XMMWORD PTR [rsp+2976], xmm0
	movdqu XMMWORD PTR [rsp+2960], xmm0
	movdqu XMMWORD PTR [rsp+2944], xmm0
	movdqu XMMWORD PTR [rsp+2928], xmm0
	movdqu XMMWORD PTR [rsp+2912], xmm0
	movdqu XMMWORD PTR [rsp+2896], xmm0
	movdqu XMMWORD PTR [rsp+2880], xmm0
	movdqu XMMWORD PTR [rsp+2864], xmm0
	movdqu XMMWORD PTR [rsp+2848], xmm0
	movdqu XMMWORD PTR [rsp+2832], xmm0
	movdqu XMMWORD PTR [rsp+2816], xmm0
	movdqu XMMWORD PTR [rsp+2800], xmm0
	movdqu XMMWORD PTR [rsp+2784], xmm0
	movdqu XMMWORD PTR [rsp+2768], xmm0
	movdqu XMMWORD PTR [rsp+2752], xmm0
	movdqu XMMWORD PTR [rsp+2736], xmm0
	movdqu XMMWORD PTR [rsp+2720], xmm0
	movdqu XMMWORD PTR [rsp+2704], xmm0
	movdqu XMMWORD PTR [rsp+2688], xmm0
	movdqu XMMWORD PTR [rsp+2672], xmm0
	movdqu XMMWORD PTR [rsp+2656], xmm0
	movdqu XMMWORD PTR [rsp+2640], xmm0
	movdqu XMMWORD PTR [rsp+2624], xmm0
	movdqu XMMWORD PTR [rsp+2608], xmm0
	movdqu XMMWORD PTR [rsp+2592], xmm0
	movdqu XMMWORD PTR [rsp+2576], xmm0
	movdqu XMMWORD PTR [rsp+2560], xmm0
	movdqu XMMWORD PTR [rsp+2544], xmm0
	movdqu XMMWORD PTR [rsp+2528], xmm0
	movdqu XMMWORD PTR [rsp+2512], xmm0
	movdqu XMMWORD PTR [rsp+2496], xmm0
	movdqu XMMWORD PTR [rsp+2480], xmm0
	movdqu XMMWORD PTR [rsp+2464], xmm0
	movdqu XMMWORD PTR [rsp+2448], xmm0
	movdqu XMMWORD PTR [rsp+2432], xmm0
	movdqu XMMWORD PTR [rsp+2416], xmm0
	movdqu XMMWORD PTR [rsp+2400], xmm0
	movdqu XMMWORD PTR [rsp+2384], xmm0
	movdqu XMMWORD PTR [rsp+2368], xmm0
	movdqu XMMWORD PTR [rsp+2352], xmm0
	movdqu XMMWORD PTR [rsp+2336], xmm0
	movdqu XMMWORD PTR [rsp+2320], xmm0
	movdqu XMMWORD PTR [rsp+2304], xmm0
	movdqu XMMWORD PTR [rsp+2288], xmm0
	movdqu XMMWORD PTR [rsp+2272], xmm0
	movdqu XMMWORD PTR [rsp+2256], xmm0
	movdqu XMMWORD PTR [rsp+2240], xmm0
	movdqu XMMWORD PTR [rsp+2224], xmm0
	movdqu XMMWORD PTR [rsp+2208], xmm0
	movdqu XMMWORD PTR [rsp+2192], xmm0
	movdqu XMMWORD PTR [rsp+2176], xmm0
	movdqu XMMWORD PTR [rsp+2160], xmm0
	movdqu XMMWORD PTR [rsp+2144], xmm0
	movdqu XMMWORD PTR [rsp+2128], xmm0
	movdqu XMMWORD PTR [rsp+2112], xmm0
	movdqu XMMWORD PTR [rsp+2096], xmm0
	movdqu XMMWORD PTR [rsp+2080], xmm0
	movdqu XMMWORD PTR [rsp+2064], xmm0
	movdqu XMMWORD PTR [rsp+2048], xmm0
	movdqu XMMWORD PTR [rsp+2032], xmm0
	movdqu XMMWORD PTR [rsp+2016], xmm0
	movdqu XMMWORD PTR [rsp+2000], xmm0
	movdqu XMMWORD PTR [rsp+1984], xmm0
	movdqu XMMWORD PTR [rsp+1968], xmm0
	movdqu XMMWORD PTR [rsp+1952], xmm0
	movdqu XMMWORD PTR [rsp+1936], xmm0
	movdqu XMMWORD PTR [rsp+1920], xmm0
	movdqu XMMWORD PTR [rsp+1904], xmm0
	movdqu XMMWORD PTR [rsp+1888], xmm0
	movdqu XMMWORD PTR [rsp+1872], xmm0
	movdqu XMMWORD PTR [rsp+1856], xmm0
	movdqu XMMWORD PTR [rsp+1840], xmm0
	movdqu XMMWORD PTR [rsp+1824], xmm0
	movdqu XMMWORD PTR [rsp+1808], xmm0
	movdqu XMMWORD PTR [rsp+1792], xmm0
	movdqu XMMWORD PTR [rsp+1776], xmm0
	movdqu XMMWORD PTR [rsp+1760], xmm0
	movdqu XMMWORD PTR [rsp+1744], xmm0
	movdqu XMMWORD PTR [rsp+1728], xmm0
	movdqu XMMWORD PTR [rsp+1712], xmm0
	movdqu XMMWORD PTR [rsp+1696], xmm0
	movdqu XMMWORD PTR [rsp+1680], xmm0
	movdqu XMMWORD PTR [rsp+1664], xmm0
	movdqu XMMWORD PTR [rsp+1648], xmm0
	movdqu XMMWORD PTR [rsp+1632], xmm0
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
	lea rsp, [rsp+3632]
	lea rsp, [rsp+8]
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

vg_aes_ocb_open:
	lea rsp, [rsp-3632]
	mov rax, QWORD PTR [rsp+3640]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+3648]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+3656]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+3664]
	mov QWORD PTR [rsp+32], rax
	mov rax, rsp
	add rax, 48
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+40]
	mov QWORD PTR [rax+160], rbx
	mov QWORD PTR [rax+168], rbp
	mov QWORD PTR [rax+176], r12
	mov QWORD PTR [rax+184], r13
	mov QWORD PTR [rax+192], r14
	mov QWORD PTR [rax+200], r15
	mov r15, rax
	mov r14, rdi
	mov QWORD PTR [r15+232], rsi
	mov QWORD PTR [r15+288], rdx
	mov QWORD PTR [r15+296], rcx
	mov QWORD PTR [r15+240], r8
	mov QWORD PTR [r15+248], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+208], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r15+216], rax
	mov rax, QWORD PTR [rsp+32]
	mov QWORD PTR [r15+224], rax
	mov rax, QWORD PTR [rsp+24]
	mov QWORD PTR [r15+304], rax
	mov rax, QWORD PTR [r14+240]
	bswap rax
	mov rdx, QWORD PTR [r14+248]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	xor r8, r8
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	mov QWORD PTR [r15+64], rax
	bswap rdx
	mov QWORD PTR [r15+72], rdx
	mov rax, QWORD PTR [r15+64]
	bswap rax
	mov rdx, QWORD PTR [r15+72]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	xor r8, r8
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	mov QWORD PTR [r15+80], rax
	bswap rdx
	mov QWORD PTR [r15+88], rdx
	xor rax, rax
	mov QWORD PTR [r15+32], rax
	mov QWORD PTR [r15+40], rax
	mov rax, QWORD PTR [r15+80]
	mov rdx, QWORD PTR [r15+88]
	mov QWORD PTR [r15+2560], rax
	mov QWORD PTR [r15+2568], rdx
	mov r9, QWORD PTR [r15+216]
	mov rax, QWORD PTR [r15+248]
	or r9, rax
	shr r9, 5
	mov r10, r15
	add r10, 2560
	mov r11, 1
	movabs rsi, 157587932685088877
	test r9, r9
	je 20f
22:
	add r11, r11
	mov rax, r11
	mul rsi
	shr rax, 58
	ror rax, 60
	add rax, r15
	mov rdi, rax
	mov rax, QWORD PTR [r10]
	bswap rax
	mov rdx, QWORD PTR [r10+8]
	bswap rdx
	mov rcx, rax
	shr rcx, 63
	xor r8, r8
	sub r8, rcx
	and r8, 135
	mov rcx, rdx
	shr rcx, 63
	add rax, rax
	or rax, rcx
	add rdx, rdx
	xor rdx, r8
	bswap rax
	mov QWORD PTR [rdi+2560], rax
	bswap rdx
	mov QWORD PTR [rdi+2568], rdx
	mov r10, rdi
	add r10, 2560
	shr r9, 1
	test r9, r9
	jne 22b
	jmp 21f
20:
21:
	xor rax, rax
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rax
	mov rbx, QWORD PTR [r15+288]
	mov r12, QWORD PTR [r15+296]
	mov rsi, r15
	add rsi, 128
	sub rsi, r12
	mov rcx, 0
23:
	movzx eax, BYTE PTR [rbx+rcx*1]
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 23b
	mov rax, 1
	mov BYTE PTR [rsi-1], al
	mov rax, QWORD PTR [r15+224]
	and rax, 15
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx ecx, BYTE PTR [r15+112]
	or rcx, rax
	mov BYTE PTR [r15+112], cl
	movzx eax, BYTE PTR [r15+127]
	mov rcx, rax
	and rcx, 63
	mov QWORD PTR [r15+256], rcx
	and rax, 192
	mov BYTE PTR [r15+127], al
	mov rdx, r15
	add rdx, 112
	mov rcx, 1
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks}
	mov rax, QWORD PTR [r15+112]
	bswap rax
	mov rdx, QWORD PTR [r15+120]
	bswap rdx
	mov rcx, rax
	ror rcx, 56
	movabs r8, -256
	and rcx, r8
	mov r8, rdx
	shr r8, 56
	or rcx, r8
	xor rcx, rax
	mov rbx, QWORD PTR [r15+256]
	mov r9, rbx
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -2
	mov r8, rax
	ror r8, 63
	and r8, r11
	mov r9, rdx
	shr r9, 63
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 63
	and r8, r11
	mov r9, rcx
	shr r9, 63
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 63
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 1
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -4
	mov r8, rax
	ror r8, 62
	and r8, r11
	mov r9, rdx
	shr r9, 62
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 62
	and r8, r11
	mov r9, rcx
	shr r9, 62
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 62
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 2
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -16
	mov r8, rax
	ror r8, 60
	and r8, r11
	mov r9, rdx
	shr r9, 60
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 60
	and r8, r11
	mov r9, rcx
	shr r9, 60
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 60
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 3
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -256
	mov r8, rax
	ror r8, 56
	and r8, r11
	mov r9, rdx
	shr r9, 56
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 56
	and r8, r11
	mov r9, rcx
	shr r9, 56
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 56
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 4
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -65536
	mov r8, rax
	ror r8, 48
	and r8, r11
	mov r9, rdx
	shr r9, 48
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 48
	and r8, r11
	mov r9, rcx
	shr r9, 48
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 48
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	mov r9, rbx
	shr r9, 5
	and r9, 1
	xor r10, r10
	sub r10, r9
	movabs r11, -4294967296
	mov r8, rax
	ror r8, 32
	and r8, r11
	mov r9, rdx
	shr r9, 32
	or r8, r9
	xor r8, rax
	and r8, r10
	xor rax, r8
	mov r8, rdx
	ror r8, 32
	and r8, r11
	mov r9, rcx
	shr r9, 32
	or r8, r9
	xor r8, rdx
	and r8, r10
	xor rdx, r8
	mov r8, rcx
	ror r8, 32
	and r8, r11
	xor r8, rcx
	and r8, r10
	xor rcx, r8
	bswap rax
	bswap rdx
	mov QWORD PTR [r15+16], rax
	mov QWORD PTR [r15+24], rdx
	mov QWORD PTR [r15+272], rax
	mov QWORD PTR [r15+280], rdx
	xor rax, rax
	mov QWORD PTR [r15+48], rax
	mov QWORD PTR [r15+56], rax
	xor rax, rax
	mov QWORD PTR [r15+144], rax
	mov QWORD PTR [r15+152], rax
	mov rbx, QWORD PTR [r15+240]
	mov rax, QWORD PTR [r15+248]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+112], rcx
	shr rax, 4
	mov QWORD PTR [r15+248], rax
	mov rbp, 1
	test rax, rax
	je 24f
26:
	mov r12, QWORD PTR [r15+248]
	cmp r12, 8
	jb 27f
	mov r12, 8
	jmp 28f
27:
28:
	mov r13, 0
	mov rsi, r15
	add rsi, 384
29:
	mov rax, rbp
	mov rcx, 0
	sub rcx, rbp
	and rax, rcx
	movabs rcx, 157587932685088877
	mul rcx
	shr rax, 58
	ror rax, 60
	mov rcx, r15
	add rcx, rax
	mov rax, QWORD PTR [r15+144]
	mov rdx, QWORD PTR [r15+152]
	xor rax, QWORD PTR [rcx+2560]
	xor rdx, QWORD PTR [rcx+2568]
	mov QWORD PTR [r15+144], rax
	mov QWORD PTR [r15+152], rdx
	mov rax, QWORD PTR [rbx]
	mov rdx, QWORD PTR [rbx+8]
	xor rax, QWORD PTR [r15+144]
	xor rdx, QWORD PTR [r15+152]
	mov QWORD PTR [rsi], rax
	mov QWORD PTR [rsi+8], rdx
	add rsi, 16
	add rbx, 16
	add rbp, 1
	add r13, 1
	cmp r13, r12
	jne 29b
	mov rdx, r15
	add rdx, 384
	mov rcx, r12
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks}
	mov r13, 0
	mov rsi, r15
	add rsi, 384
210:
	mov rax, QWORD PTR [r15+48]
	mov rdx, QWORD PTR [r15+56]
	xor rax, QWORD PTR [rsi]
	xor rdx, QWORD PTR [rsi+8]
	mov QWORD PTR [r15+48], rax
	mov QWORD PTR [r15+56], rdx
	add rsi, 16
	add r13, 1
	cmp r13, r12
	jne 210b
	mov rax, QWORD PTR [r15+248]
	sub rax, r12
	mov QWORD PTR [r15+248], rax
	jne 26b
	jmp 25f
24:
25:
	mov r12, QWORD PTR [r15+112]
	test r12, r12
	je 211f
	mov rax, QWORD PTR [r15+144]
	mov rdx, QWORD PTR [r15+152]
	xor rax, QWORD PTR [r14+240]
	xor rdx, QWORD PTR [r14+248]
	mov QWORD PTR [r15+144], rax
	mov QWORD PTR [r15+152], rdx
	xor rax, rax
	mov QWORD PTR [r15+384], rax
	mov QWORD PTR [r15+392], rax
	mov rsi, r15
	add rsi, 384
	mov rcx, 0
213:
	movzx eax, BYTE PTR [rbx+rcx*1]
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 213b
	mov rax, 128
	mov BYTE PTR [rsi+rcx*1], al
	mov rax, QWORD PTR [r15+384]
	mov rdx, QWORD PTR [r15+392]
	xor rax, QWORD PTR [r15+144]
	xor rdx, QWORD PTR [r15+152]
	mov QWORD PTR [r15+384], rax
	mov QWORD PTR [r15+392], rdx
	mov rdx, r15
	add rdx, 384
	mov rcx, 1
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks}
	mov rax, QWORD PTR [r15+48]
	mov rdx, QWORD PTR [r15+56]
	xor rax, QWORD PTR [r15+384]
	xor rdx, QWORD PTR [r15+392]
	mov QWORD PTR [r15+48], rax
	mov QWORD PTR [r15+56], rdx
	jmp 212f
211:
212:
	mov r13, QWORD PTR [r15+216]
	shr r13, 4
	test r13, r13
	je 214f
	mov rbx, QWORD PTR [r15+208]
	mov r12, r13
	mov rbp, 1
	movdqu xmm0, XMMWORD PTR [r15+16]
	movdqu xmm1, XMMWORD PTR [r15+32]
	movdqu xmm4, XMMWORD PTR [r15+2560]
	movdqu xmm5, XMMWORD PTR [r15+2576]
	cmp r12, 4
	jb 216f
218:
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	pxor xmm0, xmm5
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	mov rax, rbp
	mov rcx, 0
	sub rcx, rbp
	and rax, rcx
	movabs rcx, 157587932685088877
	mul rcx
	shr rax, 58
	ror rax, 60
	mov rcx, r15
	add rcx, rax
	movdqu xmm2, XMMWORD PTR [rcx+2560]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	sub r12, 4
	cmp r12, 4
	jae 218b
	jmp 217f
216:
217:
	test r12, r12
	je 219f
221:
	mov rax, rbp
	mov rcx, 0
	sub rcx, rbp
	and rax, rcx
	movabs rcx, 157587932685088877
	mul rcx
	shr rax, 58
	ror rax, 60
	mov rcx, r15
	add rcx, rax
	movdqu xmm2, XMMWORD PTR [rcx+2560]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	sub r12, 1
	jne 221b
	jmp 220f
219:
220:
	movdqu XMMWORD PTR [r15+16], xmm0
	movdqu XMMWORD PTR [r15+32], xmm1
	mov rdx, QWORD PTR [r15+208]
	mov rcx, r13
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_decrypt_blocks}
	mov rax, QWORD PTR [r15+272]
	mov rdx, QWORD PTR [r15+280]
	mov QWORD PTR [r15+16], rax
	mov QWORD PTR [r15+24], rdx
	mov rbx, QWORD PTR [r15+208]
	mov r12, r13
	mov rbp, 1
	movdqu xmm0, XMMWORD PTR [r15+16]
	movdqu xmm1, XMMWORD PTR [r15+32]
	movdqu xmm4, XMMWORD PTR [r15+2560]
	movdqu xmm5, XMMWORD PTR [r15+2576]
	cmp r12, 4
	jb 222f
224:
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	pxor xmm0, xmm5
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	mov rax, rbp
	mov rcx, 0
	sub rcx, rbp
	and rax, rcx
	movabs rcx, 157587932685088877
	mul rcx
	shr rax, 58
	ror rax, 60
	mov rcx, r15
	add rcx, rax
	movdqu xmm2, XMMWORD PTR [rcx+2560]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	sub r12, 4
	cmp r12, 4
	jae 224b
	jmp 223f
222:
223:
	test r12, r12
	je 225f
227:
	mov rax, rbp
	mov rcx, 0
	sub rcx, rbp
	and rax, rcx
	movabs rcx, 157587932685088877
	mul rcx
	shr rax, 58
	ror rax, 60
	mov rcx, r15
	add rcx, rax
	movdqu xmm2, XMMWORD PTR [rcx+2560]
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [rbx]
	pxor xmm3, xmm0
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rbx], xmm3
	add rbx, 16
	add rbp, 1
	sub r12, 1
	jne 227b
	jmp 226f
225:
226:
	movdqu XMMWORD PTR [r15+16], xmm0
	movdqu XMMWORD PTR [r15+32], xmm1
	jmp 215f
214:
215:
	mov rbx, QWORD PTR [r15+208]
	mov rax, QWORD PTR [r15+216]
	mov r12, rax
	and r12, 15
	sub rax, r12
	add rbx, rax
	test r12, r12
	je 228f
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	xor rax, QWORD PTR [r14+240]
	xor rdx, QWORD PTR [r14+248]
	mov QWORD PTR [r15+16], rax
	mov QWORD PTR [r15+24], rdx
	mov rax, QWORD PTR [r15+16]
	mov rdx, QWORD PTR [r15+24]
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rdx
	mov rdx, r15
	add rdx, 112
	mov rcx, 1
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks}
	mov rcx, 0
230:
	movzx eax, BYTE PTR [rbx+rcx*1]
	movzx edx, BYTE PTR [r15+rcx*1+112]
	xor rax, rdx
	mov BYTE PTR [rbx+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 230b
	xor rax, rax
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rax
	mov rsi, r15
	add rsi, 128
	mov rcx, 0
231:
	movzx eax, BYTE PTR [rbx+rcx*1]
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 231b
	mov rax, 128
	mov BYTE PTR [rsi+rcx*1], al
	mov rax, QWORD PTR [r15+32]
	mov rdx, QWORD PTR [r15+40]
	xor rax, QWORD PTR [r15+128]
	xor rdx, QWORD PTR [r15+136]
	mov QWORD PTR [r15+32], rax
	mov QWORD PTR [r15+40], rdx
	jmp 229f
228:
229:
	mov rax, QWORD PTR [r15+32]
	mov rdx, QWORD PTR [r15+40]
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rdx
	mov rax, QWORD PTR [r15+112]
	mov rdx, QWORD PTR [r15+120]
	xor rax, QWORD PTR [r15+16]
	xor rdx, QWORD PTR [r15+24]
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rdx
	mov rax, QWORD PTR [r15+112]
	mov rdx, QWORD PTR [r15+120]
	xor rax, QWORD PTR [r15+64]
	xor rdx, QWORD PTR [r15+72]
	mov QWORD PTR [r15+112], rax
	mov QWORD PTR [r15+120], rdx
	mov rdx, r15
	add rdx, 112
	mov rcx, 1
	mov rdi, r14
	mov rsi, QWORD PTR [r15+232]
	mov r8, r15
	add r8, 512
	call {vg_aes_encrypt_blocks}
	mov rax, QWORD PTR [r15+112]
	mov rdx, QWORD PTR [r15+120]
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rdx
	mov rax, QWORD PTR [r15+128]
	mov rdx, QWORD PTR [r15+136]
	xor rax, QWORD PTR [r15+48]
	xor rdx, QWORD PTR [r15+56]
	mov QWORD PTR [r15+128], rax
	mov QWORD PTR [r15+136], rdx
	mov rbx, QWORD PTR [r15+304]
	mov rsi, r15
	mov r12, QWORD PTR [r15+224]
	mov rcx, 0
232:
	movzx eax, BYTE PTR [rbx+rcx*1]
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 232b
	xor rdx, rdx
	mov rcx, 0
	mov r12, QWORD PTR [r15+224]
233:
	movzx eax, BYTE PTR [r15+rcx*1]
	movzx r8d, BYTE PTR [r15+rcx*1+128]
	xor rax, r8
	or rdx, rax
	add rcx, 1
	cmp rcx, r12
	jne 233b
	sub rdx, 1
	shr rdx, 63
	mov QWORD PTR [r15], rdx
	mov rbx, QWORD PTR [r15+208]
	mov r12, QWORD PTR [r15+216]
	xor rdx, rdx
	sub rdx, QWORD PTR [r15]
	movq xmm6, rdx
	punpcklqdq xmm6, xmm6
	mov rcx, 0
	mov r8, r12
	shr r8, 4
	test r8, r8
	je 234f
236:
	movdqu xmm7, XMMWORD PTR [rbx+rcx*1]
	pand xmm7, xmm6
	movdqu XMMWORD PTR [rbx+rcx*1], xmm7
	add rcx, 16
	sub r8, 1
	jne 236b
	jmp 235f
234:
235:
	cmp rcx, r12
	je 237f
239:
	movzx eax, BYTE PTR [rbx+rcx*1]
	and rax, rdx
	mov BYTE PTR [rbx+rcx*1], al
	add rcx, 1
	cmp rcx, r12
	jne 239b
	jmp 238f
237:
238:
	mov rax, QWORD PTR [r15]
	mov rbx, QWORD PTR [r15+160]
	mov rbp, QWORD PTR [r15+168]
	mov r12, QWORD PTR [r15+176]
	mov r13, QWORD PTR [r15+184]
	mov r14, QWORD PTR [r15+192]
	mov r15, QWORD PTR [r15+200]
	lea rsp, [rsp+3632]
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
	lea rsp, [rsp-3632]
	movdqu XMMWORD PTR [rsp+3616], xmm0
	movdqu XMMWORD PTR [rsp+3600], xmm0
	movdqu XMMWORD PTR [rsp+3584], xmm0
	movdqu XMMWORD PTR [rsp+3568], xmm0
	movdqu XMMWORD PTR [rsp+3552], xmm0
	movdqu XMMWORD PTR [rsp+3536], xmm0
	movdqu XMMWORD PTR [rsp+3520], xmm0
	movdqu XMMWORD PTR [rsp+3504], xmm0
	movdqu XMMWORD PTR [rsp+3488], xmm0
	movdqu XMMWORD PTR [rsp+3472], xmm0
	movdqu XMMWORD PTR [rsp+3456], xmm0
	movdqu XMMWORD PTR [rsp+3440], xmm0
	movdqu XMMWORD PTR [rsp+3424], xmm0
	movdqu XMMWORD PTR [rsp+3408], xmm0
	movdqu XMMWORD PTR [rsp+3392], xmm0
	movdqu XMMWORD PTR [rsp+3376], xmm0
	movdqu XMMWORD PTR [rsp+3360], xmm0
	movdqu XMMWORD PTR [rsp+3344], xmm0
	movdqu XMMWORD PTR [rsp+3328], xmm0
	movdqu XMMWORD PTR [rsp+3312], xmm0
	movdqu XMMWORD PTR [rsp+3296], xmm0
	movdqu XMMWORD PTR [rsp+3280], xmm0
	movdqu XMMWORD PTR [rsp+3264], xmm0
	movdqu XMMWORD PTR [rsp+3248], xmm0
	movdqu XMMWORD PTR [rsp+3232], xmm0
	movdqu XMMWORD PTR [rsp+3216], xmm0
	movdqu XMMWORD PTR [rsp+3200], xmm0
	movdqu XMMWORD PTR [rsp+3184], xmm0
	movdqu XMMWORD PTR [rsp+3168], xmm0
	movdqu XMMWORD PTR [rsp+3152], xmm0
	movdqu XMMWORD PTR [rsp+3136], xmm0
	movdqu XMMWORD PTR [rsp+3120], xmm0
	movdqu XMMWORD PTR [rsp+3104], xmm0
	movdqu XMMWORD PTR [rsp+3088], xmm0
	movdqu XMMWORD PTR [rsp+3072], xmm0
	movdqu XMMWORD PTR [rsp+3056], xmm0
	movdqu XMMWORD PTR [rsp+3040], xmm0
	movdqu XMMWORD PTR [rsp+3024], xmm0
	movdqu XMMWORD PTR [rsp+3008], xmm0
	movdqu XMMWORD PTR [rsp+2992], xmm0
	movdqu XMMWORD PTR [rsp+2976], xmm0
	movdqu XMMWORD PTR [rsp+2960], xmm0
	movdqu XMMWORD PTR [rsp+2944], xmm0
	movdqu XMMWORD PTR [rsp+2928], xmm0
	movdqu XMMWORD PTR [rsp+2912], xmm0
	movdqu XMMWORD PTR [rsp+2896], xmm0
	movdqu XMMWORD PTR [rsp+2880], xmm0
	movdqu XMMWORD PTR [rsp+2864], xmm0
	movdqu XMMWORD PTR [rsp+2848], xmm0
	movdqu XMMWORD PTR [rsp+2832], xmm0
	movdqu XMMWORD PTR [rsp+2816], xmm0
	movdqu XMMWORD PTR [rsp+2800], xmm0
	movdqu XMMWORD PTR [rsp+2784], xmm0
	movdqu XMMWORD PTR [rsp+2768], xmm0
	movdqu XMMWORD PTR [rsp+2752], xmm0
	movdqu XMMWORD PTR [rsp+2736], xmm0
	movdqu XMMWORD PTR [rsp+2720], xmm0
	movdqu XMMWORD PTR [rsp+2704], xmm0
	movdqu XMMWORD PTR [rsp+2688], xmm0
	movdqu XMMWORD PTR [rsp+2672], xmm0
	movdqu XMMWORD PTR [rsp+2656], xmm0
	movdqu XMMWORD PTR [rsp+2640], xmm0
	movdqu XMMWORD PTR [rsp+2624], xmm0
	movdqu XMMWORD PTR [rsp+2608], xmm0
	movdqu XMMWORD PTR [rsp+2592], xmm0
	movdqu XMMWORD PTR [rsp+2576], xmm0
	movdqu XMMWORD PTR [rsp+2560], xmm0
	movdqu XMMWORD PTR [rsp+2544], xmm0
	movdqu XMMWORD PTR [rsp+2528], xmm0
	movdqu XMMWORD PTR [rsp+2512], xmm0
	movdqu XMMWORD PTR [rsp+2496], xmm0
	movdqu XMMWORD PTR [rsp+2480], xmm0
	movdqu XMMWORD PTR [rsp+2464], xmm0
	movdqu XMMWORD PTR [rsp+2448], xmm0
	movdqu XMMWORD PTR [rsp+2432], xmm0
	movdqu XMMWORD PTR [rsp+2416], xmm0
	movdqu XMMWORD PTR [rsp+2400], xmm0
	movdqu XMMWORD PTR [rsp+2384], xmm0
	movdqu XMMWORD PTR [rsp+2368], xmm0
	movdqu XMMWORD PTR [rsp+2352], xmm0
	movdqu XMMWORD PTR [rsp+2336], xmm0
	movdqu XMMWORD PTR [rsp+2320], xmm0
	movdqu XMMWORD PTR [rsp+2304], xmm0
	movdqu XMMWORD PTR [rsp+2288], xmm0
	movdqu XMMWORD PTR [rsp+2272], xmm0
	movdqu XMMWORD PTR [rsp+2256], xmm0
	movdqu XMMWORD PTR [rsp+2240], xmm0
	movdqu XMMWORD PTR [rsp+2224], xmm0
	movdqu XMMWORD PTR [rsp+2208], xmm0
	movdqu XMMWORD PTR [rsp+2192], xmm0
	movdqu XMMWORD PTR [rsp+2176], xmm0
	movdqu XMMWORD PTR [rsp+2160], xmm0
	movdqu XMMWORD PTR [rsp+2144], xmm0
	movdqu XMMWORD PTR [rsp+2128], xmm0
	movdqu XMMWORD PTR [rsp+2112], xmm0
	movdqu XMMWORD PTR [rsp+2096], xmm0
	movdqu XMMWORD PTR [rsp+2080], xmm0
	movdqu XMMWORD PTR [rsp+2064], xmm0
	movdqu XMMWORD PTR [rsp+2048], xmm0
	movdqu XMMWORD PTR [rsp+2032], xmm0
	movdqu XMMWORD PTR [rsp+2016], xmm0
	movdqu XMMWORD PTR [rsp+2000], xmm0
	movdqu XMMWORD PTR [rsp+1984], xmm0
	movdqu XMMWORD PTR [rsp+1968], xmm0
	movdqu XMMWORD PTR [rsp+1952], xmm0
	movdqu XMMWORD PTR [rsp+1936], xmm0
	movdqu XMMWORD PTR [rsp+1920], xmm0
	movdqu XMMWORD PTR [rsp+1904], xmm0
	movdqu XMMWORD PTR [rsp+1888], xmm0
	movdqu XMMWORD PTR [rsp+1872], xmm0
	movdqu XMMWORD PTR [rsp+1856], xmm0
	movdqu XMMWORD PTR [rsp+1840], xmm0
	movdqu XMMWORD PTR [rsp+1824], xmm0
	movdqu XMMWORD PTR [rsp+1808], xmm0
	movdqu XMMWORD PTR [rsp+1792], xmm0
	movdqu XMMWORD PTR [rsp+1776], xmm0
	movdqu XMMWORD PTR [rsp+1760], xmm0
	movdqu XMMWORD PTR [rsp+1744], xmm0
	movdqu XMMWORD PTR [rsp+1728], xmm0
	movdqu XMMWORD PTR [rsp+1712], xmm0
	movdqu XMMWORD PTR [rsp+1696], xmm0
	movdqu XMMWORD PTR [rsp+1680], xmm0
	movdqu XMMWORD PTR [rsp+1664], xmm0
	movdqu XMMWORD PTR [rsp+1648], xmm0
	movdqu XMMWORD PTR [rsp+1632], xmm0
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
	lea rsp, [rsp+3632]
	lea rsp, [rsp+8]
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
