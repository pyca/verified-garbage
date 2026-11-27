// The functions of `src/hkdf.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hkdf_key:
	lea rsp, [rsp-3104]
	mov r11, rcx
	mov rcx, rsi
	mov rsi, rdx
	add rsi, 192
	mov rax, rdx
	mov rdx, rdi
	mov rdi, rax
	mov r8, rsp
	mov r11, QWORD PTR [r11]
	call r11
	lea rsp, [rsp+3104]
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
	lea rsp, [rsp-3128]
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
	lea rsp, [rsp+3128]
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

vg_hkdf_extract:
	lea rsp, [rsp-3520]
	mov QWORD PTR [rsp], rbx
	mov QWORD PTR [rsp+8], rbp
	mov QWORD PTR [rsp+16], r12
	mov QWORD PTR [rsp+24], r13
	mov rbx, rdx
	mov rbp, rcx
	mov r12, r8
	mov r13, QWORD PTR [rsp+3528]
	mov rdx, rdi
	mov rcx, rsi
	mov rdi, rsp
	add rdi, 32
	mov rsi, rsp
	add rsi, 224
	mov r8, rsp
	add r8, 416
	mov r11, QWORD PTR [r13]
	call r11
	mov rdi, rsp
	add rdi, 32
	mov rsi, QWORD PTR [r13+40]
	mov rdx, rbx
	mov rcx, rbp
	mov r8, rsp
	add r8, 416
	mov r11, QWORD PTR [r13+8]
	call r11
	mov rdi, rsp
	add rdi, 32
	mov rsi, rsp
	add rsi, 224
	mov rdx, QWORD PTR [r13+40]
	add rdx, rbp
	mov rcx, r12
	mov r8, rsp
	add r8, 416
	mov r11, QWORD PTR [r13+16]
	call r11
	mov rbx, QWORD PTR [rsp]
	mov rbp, QWORD PTR [rsp+8]
	mov r12, QWORD PTR [rsp+16]
	mov r13, QWORD PTR [rsp+24]
	lea rsp, [rsp+3520]
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
	lea rsp, [rsp-3544]
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
	lea rsp, [rsp+3544]
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

vg_hkdf_expand:
	lea rsp, [rsp-2200]
	mov QWORD PTR [rsp], rbx
	mov QWORD PTR [rsp+8], rbp
	mov QWORD PTR [rsp+16], r12
	mov QWORD PTR [rsp+24], r13
	mov QWORD PTR [rsp+32], r14
	mov QWORD PTR [rsp+40], r15
	mov QWORD PTR [rsp+48], rsi
	mov QWORD PTR [rsp+56], rdx
	mov rbx, rdi
	mov rbp, rcx
	mov r12, r8
	mov r13, r9
	mov r14d, 1
	mov r15d, 0
	test r12, r12
	jne 20f
	jmp 21f
20:
22:
	mov rax, QWORD PTR [rbx]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rbx+8]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rbx+16]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rbx+24]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rbx+32]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rbx+40]
	mov QWORD PTR [rsp+104], rax
	mov rax, QWORD PTR [rbx+48]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rbx+56]
	mov QWORD PTR [rsp+120], rax
	mov rdi, rsp
	add rdi, 64
	mov rsi, QWORD PTR [r13+40]
	mov rdx, rsp
	add rdx, 256
	mov rcx, r15
	mov r8, rsp
	add r8, 328
	mov r11, QWORD PTR [r13+8]
	call r11
	mov rdi, rsp
	add rdi, 64
	mov rsi, QWORD PTR [r13+40]
	add rsi, r15
	mov rdx, QWORD PTR [rsp+48]
	mov rcx, QWORD PTR [rsp+56]
	mov r8, rsp
	add r8, 328
	mov r11, QWORD PTR [r13+8]
	call r11
	mov BYTE PTR [rsp+320], r14b
	mov rdi, rsp
	add rdi, 64
	mov rsi, QWORD PTR [r13+40]
	add rsi, r15
	add rsi, QWORD PTR [rsp+56]
	mov rdx, rsp
	add rdx, 320
	mov ecx, 1
	mov r8, rsp
	add r8, 328
	mov r11, QWORD PTR [r13+8]
	call r11
	mov rdi, rsp
	add rdi, 64
	mov rsi, rbx
	add rsi, 192
	mov rdx, QWORD PTR [r13+40]
	add rdx, r15
	add rdx, QWORD PTR [rsp+56]
	add rdx, 1
	mov rcx, rsp
	add rcx, 256
	mov r8, rsp
	add r8, 328
	mov r11, QWORD PTR [r13+16]
	call r11
	mov rax, QWORD PTR [r13+32]
	cmp r12, rax
	jb 23f
	jmp 24f
23:
	mov rax, r12
24:
	mov r8d, 0
25:
	movzx edx, BYTE PTR [rsp+r8*1+256]
	mov BYTE PTR [rbp+r8*1], dl
	add r8, 1
	cmp r8, rax
	jne 25b
	add rbp, rax
	sub r12, rax
	mov r15, QWORD PTR [r13+32]
	add r14, 1
	test r12, r12
	jne 22b
21:
	mov rbx, QWORD PTR [rsp]
	mov rbp, QWORD PTR [rsp+8]
	mov r12, QWORD PTR [rsp+16]
	mov r13, QWORD PTR [rsp+24]
	mov r14, QWORD PTR [rsp+32]
	mov r15, QWORD PTR [rsp+40]
	lea rsp, [rsp+2200]
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
	lea rsp, [rsp-2224]
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
	lea rsp, [rsp+2224]
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
