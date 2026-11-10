// The functions of `src/rsa_pss.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pss_sign_crt_ifma512:
	lea rsp, [rsp-392]
	mov QWORD PTR [rsp+328], rbx
	mov QWORD PTR [rsp+336], rbp
	mov QWORD PTR [rsp+344], r12
	mov QWORD PTR [rsp+128], rdi
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+136], rcx
	mov QWORD PTR [rsp+152], r8
	mov QWORD PTR [rsp+160], r9
	mov rax, QWORD PTR [rsp+480]
	mov QWORD PTR [rsp+296], rax
	mov rax, QWORD PTR [rsp+496]
	mov QWORD PTR [rsp+312], rax
	mov rax, QWORD PTR [rsp+504]
	mov QWORD PTR [rsp+320], rax
	mov rax, QWORD PTR [rsp+512]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+520]
	mov QWORD PTR [rsp+176], rax
	mov rsi, QWORD PTR [rsp+144]
	movzx eax, BYTE PTR [rsi]
	test rax, rax
	mov r11, QWORD PTR [rsp+528]
	mov r11, QWORD PTR [r11+40]
	mov QWORD PTR [rsp+376], r11
	je 20f
	mov rdx, QWORD PTR [rsp+136]
	shl rdx, 3
	sub rdx, 1
	cmp rax, 2
	sbb rdx, 0
	cmp rax, 4
	sbb rdx, 0
	cmp rax, 8
	sbb rdx, 0
	cmp rax, 16
	sbb rdx, 0
	cmp rax, 32
	sbb rdx, 0
	cmp rax, 64
	sbb rdx, 0
	cmp rax, 128
	sbb rdx, 0
	mov QWORD PTR [rsp+216], rdx
	mov rax, rdx
	add rax, 7
	shr rax, 3
	mov QWORD PTR [rsp+224], rax
	mov r8, QWORD PTR [rsp+136]
	sub r8, rax
	mov QWORD PTR [rsp+208], r8
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2560
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, QWORD PTR [rsp+208]
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+296]
	mov rcx, QWORD PTR [rsp+312]
	mov r8, QWORD PTR [rsp+320]
	mov r9, QWORD PTR [rsp+216]
	mov rax, QWORD PTR [rsp+168]
	add rax, 4096
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+176]
	sub rax, 512
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+528]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+536]
	mov QWORD PTR [rsp+24], rax
	mov r11, QWORD PTR [rsp+376]
	cmp r11, 0
	je 22f
	cmp r11, 1
	je 24f
	cmp r11, 2
	je 26f
	cmp r11, 3
	je 28f
	cmp r11, 4
	je 210f
	cmp r11, 5
	je 212f
	cmp r11, 6
	je 214f
	call {vg_rsa_pss_sha512_256_encode}
	jmp 215f
214:
	call {vg_rsa_pss_sha512_224_encode}
215:
	jmp 213f
212:
	call {vg_rsa_pss_sha512_encode}
213:
	jmp 211f
210:
	call {vg_rsa_pss_sha384_encode}
211:
	jmp 29f
28:
	call {vg_rsa_pss_sha256_encode}
29:
	jmp 27f
26:
	call {vg_rsa_pss_sha224_encode}
27:
	jmp 25f
24:
	call {vg_rsa_pss_sha1_encode}
25:
	jmp 23f
22:
	call {vg_rsa_pss_md5_encode}
23:
	test eax, eax
	je 216f
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+416]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+440]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+456]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+464]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+472]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 2560
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 8192
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+176]
	sub rax, 1024
	mov QWORD PTR [rsp+104], rax
	mov rdi, QWORD PTR [rsp+128]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+144]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+152]
	mov r9, QWORD PTR [rsp+160]
	call {vg_rsa_private_checked_ifma512}
	jmp 217f
216:
	mov rdi, QWORD PTR [rsp+128]
	mov r10, QWORD PTR [rsp+136]
	mov eax, 0
	mov r8d, 0
218:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 218b
217:
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+128]
	mov r10, QWORD PTR [rsp+136]
	mov eax, 0
	mov r8d, 0
219:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 219b
21:
	mov rbx, QWORD PTR [rsp+328]
	mov rbp, QWORD PTR [rsp+336]
	mov r12, QWORD PTR [rsp+344]
	lea rsp, [rsp+392]
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
	lea rsp, [rsp-3656]
	movdqu XMMWORD PTR [rsp+3640], xmm0
	movdqu XMMWORD PTR [rsp+3624], xmm0
	movdqu XMMWORD PTR [rsp+3608], xmm0
	movdqu XMMWORD PTR [rsp+3592], xmm0
	movdqu XMMWORD PTR [rsp+3576], xmm0
	movdqu XMMWORD PTR [rsp+3560], xmm0
	movdqu XMMWORD PTR [rsp+3544], xmm0
	movdqu XMMWORD PTR [rsp+3528], xmm0
	movdqu XMMWORD PTR [rsp+3512], xmm0
	movdqu XMMWORD PTR [rsp+3496], xmm0
	movdqu XMMWORD PTR [rsp+3480], xmm0
	movdqu XMMWORD PTR [rsp+3464], xmm0
	movdqu XMMWORD PTR [rsp+3448], xmm0
	movdqu XMMWORD PTR [rsp+3432], xmm0
	movdqu XMMWORD PTR [rsp+3416], xmm0
	movdqu XMMWORD PTR [rsp+3400], xmm0
	movdqu XMMWORD PTR [rsp+3384], xmm0
	movdqu XMMWORD PTR [rsp+3368], xmm0
	movdqu XMMWORD PTR [rsp+3352], xmm0
	movdqu XMMWORD PTR [rsp+3336], xmm0
	movdqu XMMWORD PTR [rsp+3320], xmm0
	movdqu XMMWORD PTR [rsp+3304], xmm0
	movdqu XMMWORD PTR [rsp+3288], xmm0
	movdqu XMMWORD PTR [rsp+3272], xmm0
	movdqu XMMWORD PTR [rsp+3256], xmm0
	movdqu XMMWORD PTR [rsp+3240], xmm0
	movdqu XMMWORD PTR [rsp+3224], xmm0
	movdqu XMMWORD PTR [rsp+3208], xmm0
	movdqu XMMWORD PTR [rsp+3192], xmm0
	movdqu XMMWORD PTR [rsp+3176], xmm0
	movdqu XMMWORD PTR [rsp+3160], xmm0
	movdqu XMMWORD PTR [rsp+3144], xmm0
	movdqu XMMWORD PTR [rsp+3128], xmm0
	movdqu XMMWORD PTR [rsp+3112], xmm0
	movdqu XMMWORD PTR [rsp+3096], xmm0
	movdqu XMMWORD PTR [rsp+3080], xmm0
	movdqu XMMWORD PTR [rsp+3064], xmm0
	movdqu XMMWORD PTR [rsp+3048], xmm0
	movdqu XMMWORD PTR [rsp+3032], xmm0
	movdqu XMMWORD PTR [rsp+3016], xmm0
	movdqu XMMWORD PTR [rsp+3000], xmm0
	movdqu XMMWORD PTR [rsp+2984], xmm0
	movdqu XMMWORD PTR [rsp+2968], xmm0
	movdqu XMMWORD PTR [rsp+2952], xmm0
	movdqu XMMWORD PTR [rsp+2936], xmm0
	movdqu XMMWORD PTR [rsp+2920], xmm0
	movdqu XMMWORD PTR [rsp+2904], xmm0
	movdqu XMMWORD PTR [rsp+2888], xmm0
	movdqu XMMWORD PTR [rsp+2872], xmm0
	movdqu XMMWORD PTR [rsp+2856], xmm0
	movdqu XMMWORD PTR [rsp+2840], xmm0
	movdqu XMMWORD PTR [rsp+2824], xmm0
	movdqu XMMWORD PTR [rsp+2808], xmm0
	movdqu XMMWORD PTR [rsp+2792], xmm0
	movdqu XMMWORD PTR [rsp+2776], xmm0
	movdqu XMMWORD PTR [rsp+2760], xmm0
	movdqu XMMWORD PTR [rsp+2744], xmm0
	movdqu XMMWORD PTR [rsp+2728], xmm0
	movdqu XMMWORD PTR [rsp+2712], xmm0
	movdqu XMMWORD PTR [rsp+2696], xmm0
	movdqu XMMWORD PTR [rsp+2680], xmm0
	movdqu XMMWORD PTR [rsp+2664], xmm0
	movdqu XMMWORD PTR [rsp+2648], xmm0
	movdqu XMMWORD PTR [rsp+2632], xmm0
	movdqu XMMWORD PTR [rsp+2616], xmm0
	movdqu XMMWORD PTR [rsp+2600], xmm0
	movdqu XMMWORD PTR [rsp+2584], xmm0
	movdqu XMMWORD PTR [rsp+2568], xmm0
	movdqu XMMWORD PTR [rsp+2552], xmm0
	movdqu XMMWORD PTR [rsp+2536], xmm0
	movdqu XMMWORD PTR [rsp+2520], xmm0
	movdqu XMMWORD PTR [rsp+2504], xmm0
	movdqu XMMWORD PTR [rsp+2488], xmm0
	movdqu XMMWORD PTR [rsp+2472], xmm0
	movdqu XMMWORD PTR [rsp+2456], xmm0
	movdqu XMMWORD PTR [rsp+2440], xmm0
	movdqu XMMWORD PTR [rsp+2424], xmm0
	movdqu XMMWORD PTR [rsp+2408], xmm0
	movdqu XMMWORD PTR [rsp+2392], xmm0
	movdqu XMMWORD PTR [rsp+2376], xmm0
	movdqu XMMWORD PTR [rsp+2360], xmm0
	movdqu XMMWORD PTR [rsp+2344], xmm0
	movdqu XMMWORD PTR [rsp+2328], xmm0
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
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+3656]
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

vg_rsa_pss_sign_crt_ifma:
	lea rsp, [rsp-392]
	mov QWORD PTR [rsp+328], rbx
	mov QWORD PTR [rsp+336], rbp
	mov QWORD PTR [rsp+344], r12
	mov QWORD PTR [rsp+128], rdi
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+136], rcx
	mov QWORD PTR [rsp+152], r8
	mov QWORD PTR [rsp+160], r9
	mov rax, QWORD PTR [rsp+480]
	mov QWORD PTR [rsp+296], rax
	mov rax, QWORD PTR [rsp+496]
	mov QWORD PTR [rsp+312], rax
	mov rax, QWORD PTR [rsp+504]
	mov QWORD PTR [rsp+320], rax
	mov rax, QWORD PTR [rsp+512]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+520]
	mov QWORD PTR [rsp+176], rax
	mov rsi, QWORD PTR [rsp+144]
	movzx eax, BYTE PTR [rsi]
	test rax, rax
	mov r11, QWORD PTR [rsp+528]
	mov r11, QWORD PTR [r11+40]
	mov QWORD PTR [rsp+376], r11
	je 20f
	mov rdx, QWORD PTR [rsp+136]
	shl rdx, 3
	sub rdx, 1
	cmp rax, 2
	sbb rdx, 0
	cmp rax, 4
	sbb rdx, 0
	cmp rax, 8
	sbb rdx, 0
	cmp rax, 16
	sbb rdx, 0
	cmp rax, 32
	sbb rdx, 0
	cmp rax, 64
	sbb rdx, 0
	cmp rax, 128
	sbb rdx, 0
	mov QWORD PTR [rsp+216], rdx
	mov rax, rdx
	add rax, 7
	shr rax, 3
	mov QWORD PTR [rsp+224], rax
	mov r8, QWORD PTR [rsp+136]
	sub r8, rax
	mov QWORD PTR [rsp+208], r8
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2560
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, QWORD PTR [rsp+208]
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+296]
	mov rcx, QWORD PTR [rsp+312]
	mov r8, QWORD PTR [rsp+320]
	mov r9, QWORD PTR [rsp+216]
	mov rax, QWORD PTR [rsp+168]
	add rax, 4096
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+176]
	sub rax, 512
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+528]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+536]
	mov QWORD PTR [rsp+24], rax
	mov r11, QWORD PTR [rsp+376]
	cmp r11, 0
	je 22f
	cmp r11, 1
	je 24f
	cmp r11, 2
	je 26f
	cmp r11, 3
	je 28f
	cmp r11, 4
	je 210f
	cmp r11, 5
	je 212f
	cmp r11, 6
	je 214f
	call {vg_rsa_pss_sha512_256_encode}
	jmp 215f
214:
	call {vg_rsa_pss_sha512_224_encode}
215:
	jmp 213f
212:
	call {vg_rsa_pss_sha512_encode}
213:
	jmp 211f
210:
	call {vg_rsa_pss_sha384_encode}
211:
	jmp 29f
28:
	call {vg_rsa_pss_sha256_encode}
29:
	jmp 27f
26:
	call {vg_rsa_pss_sha224_encode}
27:
	jmp 25f
24:
	call {vg_rsa_pss_sha1_encode}
25:
	jmp 23f
22:
	call {vg_rsa_pss_md5_encode}
23:
	test eax, eax
	je 216f
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+416]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+440]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+456]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+464]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+472]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 2560
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 8192
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+176]
	sub rax, 1024
	mov QWORD PTR [rsp+104], rax
	mov rdi, QWORD PTR [rsp+128]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+144]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+152]
	mov r9, QWORD PTR [rsp+160]
	call {vg_rsa_private_checked_ifma}
	jmp 217f
216:
	mov rdi, QWORD PTR [rsp+128]
	mov r10, QWORD PTR [rsp+136]
	mov eax, 0
	mov r8d, 0
218:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 218b
217:
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+128]
	mov r10, QWORD PTR [rsp+136]
	mov eax, 0
	mov r8d, 0
219:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 219b
21:
	mov rbx, QWORD PTR [rsp+328]
	mov rbp, QWORD PTR [rsp+336]
	mov r12, QWORD PTR [rsp+344]
	lea rsp, [rsp+392]
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
	lea rsp, [rsp-3656]
	movdqu XMMWORD PTR [rsp+3640], xmm0
	movdqu XMMWORD PTR [rsp+3624], xmm0
	movdqu XMMWORD PTR [rsp+3608], xmm0
	movdqu XMMWORD PTR [rsp+3592], xmm0
	movdqu XMMWORD PTR [rsp+3576], xmm0
	movdqu XMMWORD PTR [rsp+3560], xmm0
	movdqu XMMWORD PTR [rsp+3544], xmm0
	movdqu XMMWORD PTR [rsp+3528], xmm0
	movdqu XMMWORD PTR [rsp+3512], xmm0
	movdqu XMMWORD PTR [rsp+3496], xmm0
	movdqu XMMWORD PTR [rsp+3480], xmm0
	movdqu XMMWORD PTR [rsp+3464], xmm0
	movdqu XMMWORD PTR [rsp+3448], xmm0
	movdqu XMMWORD PTR [rsp+3432], xmm0
	movdqu XMMWORD PTR [rsp+3416], xmm0
	movdqu XMMWORD PTR [rsp+3400], xmm0
	movdqu XMMWORD PTR [rsp+3384], xmm0
	movdqu XMMWORD PTR [rsp+3368], xmm0
	movdqu XMMWORD PTR [rsp+3352], xmm0
	movdqu XMMWORD PTR [rsp+3336], xmm0
	movdqu XMMWORD PTR [rsp+3320], xmm0
	movdqu XMMWORD PTR [rsp+3304], xmm0
	movdqu XMMWORD PTR [rsp+3288], xmm0
	movdqu XMMWORD PTR [rsp+3272], xmm0
	movdqu XMMWORD PTR [rsp+3256], xmm0
	movdqu XMMWORD PTR [rsp+3240], xmm0
	movdqu XMMWORD PTR [rsp+3224], xmm0
	movdqu XMMWORD PTR [rsp+3208], xmm0
	movdqu XMMWORD PTR [rsp+3192], xmm0
	movdqu XMMWORD PTR [rsp+3176], xmm0
	movdqu XMMWORD PTR [rsp+3160], xmm0
	movdqu XMMWORD PTR [rsp+3144], xmm0
	movdqu XMMWORD PTR [rsp+3128], xmm0
	movdqu XMMWORD PTR [rsp+3112], xmm0
	movdqu XMMWORD PTR [rsp+3096], xmm0
	movdqu XMMWORD PTR [rsp+3080], xmm0
	movdqu XMMWORD PTR [rsp+3064], xmm0
	movdqu XMMWORD PTR [rsp+3048], xmm0
	movdqu XMMWORD PTR [rsp+3032], xmm0
	movdqu XMMWORD PTR [rsp+3016], xmm0
	movdqu XMMWORD PTR [rsp+3000], xmm0
	movdqu XMMWORD PTR [rsp+2984], xmm0
	movdqu XMMWORD PTR [rsp+2968], xmm0
	movdqu XMMWORD PTR [rsp+2952], xmm0
	movdqu XMMWORD PTR [rsp+2936], xmm0
	movdqu XMMWORD PTR [rsp+2920], xmm0
	movdqu XMMWORD PTR [rsp+2904], xmm0
	movdqu XMMWORD PTR [rsp+2888], xmm0
	movdqu XMMWORD PTR [rsp+2872], xmm0
	movdqu XMMWORD PTR [rsp+2856], xmm0
	movdqu XMMWORD PTR [rsp+2840], xmm0
	movdqu XMMWORD PTR [rsp+2824], xmm0
	movdqu XMMWORD PTR [rsp+2808], xmm0
	movdqu XMMWORD PTR [rsp+2792], xmm0
	movdqu XMMWORD PTR [rsp+2776], xmm0
	movdqu XMMWORD PTR [rsp+2760], xmm0
	movdqu XMMWORD PTR [rsp+2744], xmm0
	movdqu XMMWORD PTR [rsp+2728], xmm0
	movdqu XMMWORD PTR [rsp+2712], xmm0
	movdqu XMMWORD PTR [rsp+2696], xmm0
	movdqu XMMWORD PTR [rsp+2680], xmm0
	movdqu XMMWORD PTR [rsp+2664], xmm0
	movdqu XMMWORD PTR [rsp+2648], xmm0
	movdqu XMMWORD PTR [rsp+2632], xmm0
	movdqu XMMWORD PTR [rsp+2616], xmm0
	movdqu XMMWORD PTR [rsp+2600], xmm0
	movdqu XMMWORD PTR [rsp+2584], xmm0
	movdqu XMMWORD PTR [rsp+2568], xmm0
	movdqu XMMWORD PTR [rsp+2552], xmm0
	movdqu XMMWORD PTR [rsp+2536], xmm0
	movdqu XMMWORD PTR [rsp+2520], xmm0
	movdqu XMMWORD PTR [rsp+2504], xmm0
	movdqu XMMWORD PTR [rsp+2488], xmm0
	movdqu XMMWORD PTR [rsp+2472], xmm0
	movdqu XMMWORD PTR [rsp+2456], xmm0
	movdqu XMMWORD PTR [rsp+2440], xmm0
	movdqu XMMWORD PTR [rsp+2424], xmm0
	movdqu XMMWORD PTR [rsp+2408], xmm0
	movdqu XMMWORD PTR [rsp+2392], xmm0
	movdqu XMMWORD PTR [rsp+2376], xmm0
	movdqu XMMWORD PTR [rsp+2360], xmm0
	movdqu XMMWORD PTR [rsp+2344], xmm0
	movdqu XMMWORD PTR [rsp+2328], xmm0
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
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+3656]
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

vg_rsa_pss_sign_crt_adx:
	lea rsp, [rsp-392]
	mov QWORD PTR [rsp+328], rbx
	mov QWORD PTR [rsp+336], rbp
	mov QWORD PTR [rsp+344], r12
	mov QWORD PTR [rsp+128], rdi
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+136], rcx
	mov QWORD PTR [rsp+152], r8
	mov QWORD PTR [rsp+160], r9
	mov rax, QWORD PTR [rsp+480]
	mov QWORD PTR [rsp+296], rax
	mov rax, QWORD PTR [rsp+496]
	mov QWORD PTR [rsp+312], rax
	mov rax, QWORD PTR [rsp+504]
	mov QWORD PTR [rsp+320], rax
	mov rax, QWORD PTR [rsp+512]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+520]
	mov QWORD PTR [rsp+176], rax
	mov rsi, QWORD PTR [rsp+144]
	movzx eax, BYTE PTR [rsi]
	test rax, rax
	mov r11, QWORD PTR [rsp+528]
	mov r11, QWORD PTR [r11+40]
	mov QWORD PTR [rsp+376], r11
	je 20f
	mov rdx, QWORD PTR [rsp+136]
	shl rdx, 3
	sub rdx, 1
	cmp rax, 2
	sbb rdx, 0
	cmp rax, 4
	sbb rdx, 0
	cmp rax, 8
	sbb rdx, 0
	cmp rax, 16
	sbb rdx, 0
	cmp rax, 32
	sbb rdx, 0
	cmp rax, 64
	sbb rdx, 0
	cmp rax, 128
	sbb rdx, 0
	mov QWORD PTR [rsp+216], rdx
	mov rax, rdx
	add rax, 7
	shr rax, 3
	mov QWORD PTR [rsp+224], rax
	mov r8, QWORD PTR [rsp+136]
	sub r8, rax
	mov QWORD PTR [rsp+208], r8
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2560
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, QWORD PTR [rsp+208]
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+296]
	mov rcx, QWORD PTR [rsp+312]
	mov r8, QWORD PTR [rsp+320]
	mov r9, QWORD PTR [rsp+216]
	mov rax, QWORD PTR [rsp+168]
	add rax, 4096
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+176]
	sub rax, 512
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+528]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+536]
	mov QWORD PTR [rsp+24], rax
	mov r11, QWORD PTR [rsp+376]
	cmp r11, 0
	je 22f
	cmp r11, 1
	je 24f
	cmp r11, 2
	je 26f
	cmp r11, 3
	je 28f
	cmp r11, 4
	je 210f
	cmp r11, 5
	je 212f
	cmp r11, 6
	je 214f
	call {vg_rsa_pss_sha512_256_encode}
	jmp 215f
214:
	call {vg_rsa_pss_sha512_224_encode}
215:
	jmp 213f
212:
	call {vg_rsa_pss_sha512_encode}
213:
	jmp 211f
210:
	call {vg_rsa_pss_sha384_encode}
211:
	jmp 29f
28:
	call {vg_rsa_pss_sha256_encode}
29:
	jmp 27f
26:
	call {vg_rsa_pss_sha224_encode}
27:
	jmp 25f
24:
	call {vg_rsa_pss_sha1_encode}
25:
	jmp 23f
22:
	call {vg_rsa_pss_md5_encode}
23:
	test eax, eax
	je 216f
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+416]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+440]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+456]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+464]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+472]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 2560
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 8192
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+176]
	sub rax, 1024
	mov QWORD PTR [rsp+104], rax
	mov rdi, QWORD PTR [rsp+128]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+144]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+152]
	mov r9, QWORD PTR [rsp+160]
	call {vg_rsa_private_checked_adx}
	jmp 217f
216:
	mov rdi, QWORD PTR [rsp+128]
	mov r10, QWORD PTR [rsp+136]
	mov eax, 0
	mov r8d, 0
218:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 218b
217:
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+128]
	mov r10, QWORD PTR [rsp+136]
	mov eax, 0
	mov r8d, 0
219:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 219b
21:
	mov rbx, QWORD PTR [rsp+328]
	mov rbp, QWORD PTR [rsp+336]
	mov r12, QWORD PTR [rsp+344]
	lea rsp, [rsp+392]
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
	lea rsp, [rsp-3656]
	movdqu XMMWORD PTR [rsp+3640], xmm0
	movdqu XMMWORD PTR [rsp+3624], xmm0
	movdqu XMMWORD PTR [rsp+3608], xmm0
	movdqu XMMWORD PTR [rsp+3592], xmm0
	movdqu XMMWORD PTR [rsp+3576], xmm0
	movdqu XMMWORD PTR [rsp+3560], xmm0
	movdqu XMMWORD PTR [rsp+3544], xmm0
	movdqu XMMWORD PTR [rsp+3528], xmm0
	movdqu XMMWORD PTR [rsp+3512], xmm0
	movdqu XMMWORD PTR [rsp+3496], xmm0
	movdqu XMMWORD PTR [rsp+3480], xmm0
	movdqu XMMWORD PTR [rsp+3464], xmm0
	movdqu XMMWORD PTR [rsp+3448], xmm0
	movdqu XMMWORD PTR [rsp+3432], xmm0
	movdqu XMMWORD PTR [rsp+3416], xmm0
	movdqu XMMWORD PTR [rsp+3400], xmm0
	movdqu XMMWORD PTR [rsp+3384], xmm0
	movdqu XMMWORD PTR [rsp+3368], xmm0
	movdqu XMMWORD PTR [rsp+3352], xmm0
	movdqu XMMWORD PTR [rsp+3336], xmm0
	movdqu XMMWORD PTR [rsp+3320], xmm0
	movdqu XMMWORD PTR [rsp+3304], xmm0
	movdqu XMMWORD PTR [rsp+3288], xmm0
	movdqu XMMWORD PTR [rsp+3272], xmm0
	movdqu XMMWORD PTR [rsp+3256], xmm0
	movdqu XMMWORD PTR [rsp+3240], xmm0
	movdqu XMMWORD PTR [rsp+3224], xmm0
	movdqu XMMWORD PTR [rsp+3208], xmm0
	movdqu XMMWORD PTR [rsp+3192], xmm0
	movdqu XMMWORD PTR [rsp+3176], xmm0
	movdqu XMMWORD PTR [rsp+3160], xmm0
	movdqu XMMWORD PTR [rsp+3144], xmm0
	movdqu XMMWORD PTR [rsp+3128], xmm0
	movdqu XMMWORD PTR [rsp+3112], xmm0
	movdqu XMMWORD PTR [rsp+3096], xmm0
	movdqu XMMWORD PTR [rsp+3080], xmm0
	movdqu XMMWORD PTR [rsp+3064], xmm0
	movdqu XMMWORD PTR [rsp+3048], xmm0
	movdqu XMMWORD PTR [rsp+3032], xmm0
	movdqu XMMWORD PTR [rsp+3016], xmm0
	movdqu XMMWORD PTR [rsp+3000], xmm0
	movdqu XMMWORD PTR [rsp+2984], xmm0
	movdqu XMMWORD PTR [rsp+2968], xmm0
	movdqu XMMWORD PTR [rsp+2952], xmm0
	movdqu XMMWORD PTR [rsp+2936], xmm0
	movdqu XMMWORD PTR [rsp+2920], xmm0
	movdqu XMMWORD PTR [rsp+2904], xmm0
	movdqu XMMWORD PTR [rsp+2888], xmm0
	movdqu XMMWORD PTR [rsp+2872], xmm0
	movdqu XMMWORD PTR [rsp+2856], xmm0
	movdqu XMMWORD PTR [rsp+2840], xmm0
	movdqu XMMWORD PTR [rsp+2824], xmm0
	movdqu XMMWORD PTR [rsp+2808], xmm0
	movdqu XMMWORD PTR [rsp+2792], xmm0
	movdqu XMMWORD PTR [rsp+2776], xmm0
	movdqu XMMWORD PTR [rsp+2760], xmm0
	movdqu XMMWORD PTR [rsp+2744], xmm0
	movdqu XMMWORD PTR [rsp+2728], xmm0
	movdqu XMMWORD PTR [rsp+2712], xmm0
	movdqu XMMWORD PTR [rsp+2696], xmm0
	movdqu XMMWORD PTR [rsp+2680], xmm0
	movdqu XMMWORD PTR [rsp+2664], xmm0
	movdqu XMMWORD PTR [rsp+2648], xmm0
	movdqu XMMWORD PTR [rsp+2632], xmm0
	movdqu XMMWORD PTR [rsp+2616], xmm0
	movdqu XMMWORD PTR [rsp+2600], xmm0
	movdqu XMMWORD PTR [rsp+2584], xmm0
	movdqu XMMWORD PTR [rsp+2568], xmm0
	movdqu XMMWORD PTR [rsp+2552], xmm0
	movdqu XMMWORD PTR [rsp+2536], xmm0
	movdqu XMMWORD PTR [rsp+2520], xmm0
	movdqu XMMWORD PTR [rsp+2504], xmm0
	movdqu XMMWORD PTR [rsp+2488], xmm0
	movdqu XMMWORD PTR [rsp+2472], xmm0
	movdqu XMMWORD PTR [rsp+2456], xmm0
	movdqu XMMWORD PTR [rsp+2440], xmm0
	movdqu XMMWORD PTR [rsp+2424], xmm0
	movdqu XMMWORD PTR [rsp+2408], xmm0
	movdqu XMMWORD PTR [rsp+2392], xmm0
	movdqu XMMWORD PTR [rsp+2376], xmm0
	movdqu XMMWORD PTR [rsp+2360], xmm0
	movdqu XMMWORD PTR [rsp+2344], xmm0
	movdqu XMMWORD PTR [rsp+2328], xmm0
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
	mov QWORD PTR [rsp], r11
	lea rsp, [rsp+3656]
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

vg_rsa_pss_sign:
	lea rsp, [rsp-392]
	mov QWORD PTR [rsp+328], rbx
	mov QWORD PTR [rsp+336], rbp
	mov QWORD PTR [rsp+344], r12
	mov QWORD PTR [rsp+128], rdi
	mov QWORD PTR [rsp+144], rdx
	mov QWORD PTR [rsp+136], rcx
	mov QWORD PTR [rsp+152], r8
	mov QWORD PTR [rsp+160], r9
	mov rax, QWORD PTR [rsp+480]
	mov QWORD PTR [rsp+296], rax
	mov rax, QWORD PTR [rsp+496]
	mov QWORD PTR [rsp+312], rax
	mov rax, QWORD PTR [rsp+504]
	mov QWORD PTR [rsp+320], rax
	mov rax, QWORD PTR [rsp+512]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+520]
	mov QWORD PTR [rsp+176], rax
	mov rsi, QWORD PTR [rsp+144]
	movzx eax, BYTE PTR [rsi]
	test rax, rax
	mov r11, QWORD PTR [rsp+528]
	mov r11, QWORD PTR [r11+40]
	mov QWORD PTR [rsp+376], r11
	je 20f
	mov rdx, QWORD PTR [rsp+136]
	shl rdx, 3
	sub rdx, 1
	cmp rax, 2
	sbb rdx, 0
	cmp rax, 4
	sbb rdx, 0
	cmp rax, 8
	sbb rdx, 0
	cmp rax, 16
	sbb rdx, 0
	cmp rax, 32
	sbb rdx, 0
	cmp rax, 64
	sbb rdx, 0
	cmp rax, 128
	sbb rdx, 0
	mov QWORD PTR [rsp+216], rdx
	mov rax, rdx
	add rax, 7
	shr rax, 3
	mov QWORD PTR [rsp+224], rax
	mov r8, QWORD PTR [rsp+136]
	sub r8, rax
	mov QWORD PTR [rsp+208], r8
	mov rdi, QWORD PTR [rsp+168]
	add rdi, 2560
	mov eax, 0
	mov BYTE PTR [rdi], al
	add rdi, QWORD PTR [rsp+208]
	mov rsi, QWORD PTR [rsp+224]
	mov rdx, QWORD PTR [rsp+296]
	mov rcx, QWORD PTR [rsp+312]
	mov r8, QWORD PTR [rsp+320]
	mov r9, QWORD PTR [rsp+216]
	mov rax, QWORD PTR [rsp+168]
	add rax, 4096
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+176]
	sub rax, 512
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+528]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+536]
	mov QWORD PTR [rsp+24], rax
	mov r11, QWORD PTR [rsp+376]
	cmp r11, 0
	je 22f
	cmp r11, 1
	je 24f
	cmp r11, 2
	je 26f
	cmp r11, 3
	je 28f
	cmp r11, 4
	je 210f
	cmp r11, 5
	je 212f
	cmp r11, 6
	je 214f
	call {vg_rsa_pss_sha512_256_encode}
	jmp 215f
214:
	call {vg_rsa_pss_sha512_224_encode}
215:
	jmp 213f
212:
	call {vg_rsa_pss_sha512_encode}
213:
	jmp 211f
210:
	call {vg_rsa_pss_sha384_encode}
211:
	jmp 29f
28:
	call {vg_rsa_pss_sha256_encode}
29:
	jmp 27f
26:
	call {vg_rsa_pss_sha224_encode}
27:
	jmp 25f
24:
	call {vg_rsa_pss_sha1_encode}
25:
	jmp 23f
22:
	call {vg_rsa_pss_md5_encode}
23:
	test eax, eax
	je 216f
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+408]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+416]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+424]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+440]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+448]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+456]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+464]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+472]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 2560
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 8192
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+176]
	sub rax, 1024
	mov QWORD PTR [rsp+104], rax
	mov rdi, QWORD PTR [rsp+128]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+144]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+152]
	mov r9, QWORD PTR [rsp+160]
	call {vg_rsa_private_checked}
	jmp 217f
216:
	mov rdi, QWORD PTR [rsp+128]
	mov r10, QWORD PTR [rsp+136]
	mov eax, 0
	mov r8d, 0
218:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 218b
217:
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+128]
	mov r10, QWORD PTR [rsp+136]
	mov eax, 0
	mov r8d, 0
219:
	mov BYTE PTR [rdi+r8*1], al
	add r8, 1
	cmp r8, r10
	jne 219b
21:
	mov rbx, QWORD PTR [rsp+328]
	mov rbp, QWORD PTR [rsp+336]
	mov r12, QWORD PTR [rsp+344]
	lea rsp, [rsp+392]
	ret
	.p2align 6

vg_rsa_pss_verify_precomputed_rsa_ifma:
	lea rsp, [rsp-392]
	mov QWORD PTR [rsp+328], rbx
	mov QWORD PTR [rsp+336], rbp
	mov QWORD PTR [rsp+344], r12
	mov QWORD PTR [rsp+144], rdi
	mov QWORD PTR [rsp+136], rsi
	mov QWORD PTR [rsp+152], rdx
	mov QWORD PTR [rsp+160], rcx
	mov QWORD PTR [rsp+296], r8
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+304], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+440]
	mov QWORD PTR [rsp+176], rax
	mov rsi, QWORD PTR [rsp+144]
	movzx eax, BYTE PTR [rsi]
	test rax, rax
	mov r11, QWORD PTR [rsp+464]
	mov r11, QWORD PTR [r11+40]
	mov QWORD PTR [rsp+376], r11
	je 20f
	mov rdx, QWORD PTR [rsp+136]
	shl rdx, 3
	sub rdx, 1
	cmp rax, 2
	sbb rdx, 0
	cmp rax, 4
	sbb rdx, 0
	cmp rax, 8
	sbb rdx, 0
	cmp rax, 16
	sbb rdx, 0
	cmp rax, 32
	sbb rdx, 0
	cmp rax, 64
	sbb rdx, 0
	cmp rax, 128
	sbb rdx, 0
	mov QWORD PTR [rsp+216], rdx
	mov rax, rdx
	add rax, 7
	shr rax, 3
	mov QWORD PTR [rsp+224], rax
	mov r8, QWORD PTR [rsp+136]
	sub r8, rax
	mov QWORD PTR [rsp+208], r8
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 8192
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+176]
	sub rax, 1024
	mov QWORD PTR [rsp+24], rax
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+448]
	mov rcx, QWORD PTR [rsp+456]
	mov r8, QWORD PTR [rsp+152]
	mov r9, QWORD PTR [rsp+160]
	call {vg_rsa_public_precomputed_checked_ifma}
	mov rcx, QWORD PTR [rsp+168]
	movzx r9d, BYTE PTR [rcx]
	mov r10, QWORD PTR [rsp+208]
	mov r11d, 0
	sub r11, r10
	and r9, r11
	cmp r9, 1
	sbb r9, r9
	mov QWORD PTR [rsp+264], r9
	mov rdi, QWORD PTR [rsp+296]
	mov rsi, rcx
	add rsi, r10
	mov rdx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+416]
	mov r9, QWORD PTR [rsp+424]
	mov rax, QWORD PTR [rsp+136]
	add rax, 7
	shr rax, 3
	mov r10, QWORD PTR [rsp+176]
	sub r10, rax
	mov QWORD PTR [rsp+8], r10
	shl rax, 3
	add rax, rcx
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+464]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+472]
	mov QWORD PTR [rsp+24], rax
	mov rcx, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [rsp+376]
	cmp r11, 0
	je 22f
	cmp r11, 1
	je 24f
	cmp r11, 2
	je 26f
	cmp r11, 3
	je 28f
	cmp r11, 4
	je 210f
	cmp r11, 5
	je 212f
	cmp r11, 6
	je 214f
	call {vg_rsa_pss_sha512_256_check_encoding}
	jmp 215f
214:
	call {vg_rsa_pss_sha512_224_check_encoding}
215:
	jmp 213f
212:
	call {vg_rsa_pss_sha512_check_encoding}
213:
	jmp 211f
210:
	call {vg_rsa_pss_sha384_check_encoding}
211:
	jmp 29f
28:
	call {vg_rsa_pss_sha256_check_encoding}
29:
	jmp 27f
26:
	call {vg_rsa_pss_sha224_check_encoding}
27:
	jmp 25f
24:
	call {vg_rsa_pss_sha1_check_encoding}
25:
	jmp 23f
22:
	call {vg_rsa_pss_md5_check_encoding}
23:
	and rax, QWORD PTR [rsp+264]
	jmp 21f
20:
	mov eax, 0
21:
	mov rbx, QWORD PTR [rsp+328]
	mov rbp, QWORD PTR [rsp+336]
	mov r12, QWORD PTR [rsp+344]
	lea rsp, [rsp+392]
	ret
	.p2align 6

vg_rsa_pss_verify_precomputed_rsa_adx:
	lea rsp, [rsp-392]
	mov QWORD PTR [rsp+328], rbx
	mov QWORD PTR [rsp+336], rbp
	mov QWORD PTR [rsp+344], r12
	mov QWORD PTR [rsp+144], rdi
	mov QWORD PTR [rsp+136], rsi
	mov QWORD PTR [rsp+152], rdx
	mov QWORD PTR [rsp+160], rcx
	mov QWORD PTR [rsp+296], r8
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+304], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+440]
	mov QWORD PTR [rsp+176], rax
	mov rsi, QWORD PTR [rsp+144]
	movzx eax, BYTE PTR [rsi]
	test rax, rax
	mov r11, QWORD PTR [rsp+464]
	mov r11, QWORD PTR [r11+40]
	mov QWORD PTR [rsp+376], r11
	je 20f
	mov rdx, QWORD PTR [rsp+136]
	shl rdx, 3
	sub rdx, 1
	cmp rax, 2
	sbb rdx, 0
	cmp rax, 4
	sbb rdx, 0
	cmp rax, 8
	sbb rdx, 0
	cmp rax, 16
	sbb rdx, 0
	cmp rax, 32
	sbb rdx, 0
	cmp rax, 64
	sbb rdx, 0
	cmp rax, 128
	sbb rdx, 0
	mov QWORD PTR [rsp+216], rdx
	mov rax, rdx
	add rax, 7
	shr rax, 3
	mov QWORD PTR [rsp+224], rax
	mov r8, QWORD PTR [rsp+136]
	sub r8, rax
	mov QWORD PTR [rsp+208], r8
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 8192
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+176]
	sub rax, 1024
	mov QWORD PTR [rsp+24], rax
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+448]
	mov rcx, QWORD PTR [rsp+456]
	mov r8, QWORD PTR [rsp+152]
	mov r9, QWORD PTR [rsp+160]
	call {vg_rsa_public_precomputed_checked_adx}
	mov rcx, QWORD PTR [rsp+168]
	movzx r9d, BYTE PTR [rcx]
	mov r10, QWORD PTR [rsp+208]
	mov r11d, 0
	sub r11, r10
	and r9, r11
	cmp r9, 1
	sbb r9, r9
	mov QWORD PTR [rsp+264], r9
	mov rdi, QWORD PTR [rsp+296]
	mov rsi, rcx
	add rsi, r10
	mov rdx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+416]
	mov r9, QWORD PTR [rsp+424]
	mov rax, QWORD PTR [rsp+136]
	add rax, 7
	shr rax, 3
	mov r10, QWORD PTR [rsp+176]
	sub r10, rax
	mov QWORD PTR [rsp+8], r10
	shl rax, 3
	add rax, rcx
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+464]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+472]
	mov QWORD PTR [rsp+24], rax
	mov rcx, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [rsp+376]
	cmp r11, 0
	je 22f
	cmp r11, 1
	je 24f
	cmp r11, 2
	je 26f
	cmp r11, 3
	je 28f
	cmp r11, 4
	je 210f
	cmp r11, 5
	je 212f
	cmp r11, 6
	je 214f
	call {vg_rsa_pss_sha512_256_check_encoding}
	jmp 215f
214:
	call {vg_rsa_pss_sha512_224_check_encoding}
215:
	jmp 213f
212:
	call {vg_rsa_pss_sha512_check_encoding}
213:
	jmp 211f
210:
	call {vg_rsa_pss_sha384_check_encoding}
211:
	jmp 29f
28:
	call {vg_rsa_pss_sha256_check_encoding}
29:
	jmp 27f
26:
	call {vg_rsa_pss_sha224_check_encoding}
27:
	jmp 25f
24:
	call {vg_rsa_pss_sha1_check_encoding}
25:
	jmp 23f
22:
	call {vg_rsa_pss_md5_check_encoding}
23:
	and rax, QWORD PTR [rsp+264]
	jmp 21f
20:
	mov eax, 0
21:
	mov rbx, QWORD PTR [rsp+328]
	mov rbp, QWORD PTR [rsp+336]
	mov r12, QWORD PTR [rsp+344]
	lea rsp, [rsp+392]
	ret
	.p2align 6

vg_rsa_pss_verify_precomputed:
	lea rsp, [rsp-392]
	mov QWORD PTR [rsp+328], rbx
	mov QWORD PTR [rsp+336], rbp
	mov QWORD PTR [rsp+344], r12
	mov QWORD PTR [rsp+144], rdi
	mov QWORD PTR [rsp+136], rsi
	mov QWORD PTR [rsp+152], rdx
	mov QWORD PTR [rsp+160], rcx
	mov QWORD PTR [rsp+296], r8
	mov rax, QWORD PTR [rsp+400]
	mov QWORD PTR [rsp+304], rax
	mov rax, QWORD PTR [rsp+432]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+440]
	mov QWORD PTR [rsp+176], rax
	mov rsi, QWORD PTR [rsp+144]
	movzx eax, BYTE PTR [rsi]
	test rax, rax
	mov r11, QWORD PTR [rsp+464]
	mov r11, QWORD PTR [r11+40]
	mov QWORD PTR [rsp+376], r11
	je 20f
	mov rdx, QWORD PTR [rsp+136]
	shl rdx, 3
	sub rdx, 1
	cmp rax, 2
	sbb rdx, 0
	cmp rax, 4
	sbb rdx, 0
	cmp rax, 8
	sbb rdx, 0
	cmp rax, 16
	sbb rdx, 0
	cmp rax, 32
	sbb rdx, 0
	cmp rax, 64
	sbb rdx, 0
	cmp rax, 128
	sbb rdx, 0
	mov QWORD PTR [rsp+216], rdx
	mov rax, rdx
	add rax, 7
	shr rax, 3
	mov QWORD PTR [rsp+224], rax
	mov r8, QWORD PTR [rsp+136]
	sub r8, rax
	mov QWORD PTR [rsp+208], r8
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+168]
	add rax, 8192
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+176]
	sub rax, 1024
	mov QWORD PTR [rsp+24], rax
	mov rdi, QWORD PTR [rsp+168]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+448]
	mov rcx, QWORD PTR [rsp+456]
	mov r8, QWORD PTR [rsp+152]
	mov r9, QWORD PTR [rsp+160]
	call {vg_rsa_public_precomputed_checked}
	mov rcx, QWORD PTR [rsp+168]
	movzx r9d, BYTE PTR [rcx]
	mov r10, QWORD PTR [rsp+208]
	mov r11d, 0
	sub r11, r10
	and r9, r11
	cmp r9, 1
	sbb r9, r9
	mov QWORD PTR [rsp+264], r9
	mov rdi, QWORD PTR [rsp+296]
	mov rsi, rcx
	add rsi, r10
	mov rdx, QWORD PTR [rsp+224]
	mov r8, QWORD PTR [rsp+416]
	mov r9, QWORD PTR [rsp+424]
	mov rax, QWORD PTR [rsp+136]
	add rax, 7
	shr rax, 3
	mov r10, QWORD PTR [rsp+176]
	sub r10, rax
	mov QWORD PTR [rsp+8], r10
	shl rax, 3
	add rax, rcx
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+464]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+472]
	mov QWORD PTR [rsp+24], rax
	mov rcx, QWORD PTR [rsp+216]
	mov r11, QWORD PTR [rsp+376]
	cmp r11, 0
	je 22f
	cmp r11, 1
	je 24f
	cmp r11, 2
	je 26f
	cmp r11, 3
	je 28f
	cmp r11, 4
	je 210f
	cmp r11, 5
	je 212f
	cmp r11, 6
	je 214f
	call {vg_rsa_pss_sha512_256_check_encoding}
	jmp 215f
214:
	call {vg_rsa_pss_sha512_224_check_encoding}
215:
	jmp 213f
212:
	call {vg_rsa_pss_sha512_check_encoding}
213:
	jmp 211f
210:
	call {vg_rsa_pss_sha384_check_encoding}
211:
	jmp 29f
28:
	call {vg_rsa_pss_sha256_check_encoding}
29:
	jmp 27f
26:
	call {vg_rsa_pss_sha224_check_encoding}
27:
	jmp 25f
24:
	call {vg_rsa_pss_sha1_check_encoding}
25:
	jmp 23f
22:
	call {vg_rsa_pss_md5_check_encoding}
23:
	and rax, QWORD PTR [rsp+264]
	jmp 21f
20:
	mov eax, 0
21:
	mov rbx, QWORD PTR [rsp+328]
	mov rbp, QWORD PTR [rsp+336]
	mov r12, QWORD PTR [rsp+344]
	lea rsp, [rsp+392]
	ret
	.p2align 6
