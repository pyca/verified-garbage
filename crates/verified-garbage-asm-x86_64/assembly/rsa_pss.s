// The functions of `src/rsa_pss.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pss_sign_precomputed_crt_ifma512:
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
	mov rax, QWORD PTR [rsp+544]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+552]
	mov QWORD PTR [rsp+120], rax
	call {vg_rsa_private_checked_precomputed_ifma512}
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
	mov r11d, 16
	test r11d, esp
	je 220f
	xor r11d, r11d
	lea rsp, [rsp-3656]
	mov QWORD PTR [rsp+3648], r11
	movdqu XMMWORD PTR [rsp+3632], xmm0
	vmovdqu YMMWORD PTR [rsp+3600], ymm0
	vmovdqu YMMWORD PTR [rsp+3568], ymm0
	vmovdqu YMMWORD PTR [rsp+3536], ymm0
	vmovdqu YMMWORD PTR [rsp+3504], ymm0
	vmovdqu YMMWORD PTR [rsp+3472], ymm0
	vmovdqu YMMWORD PTR [rsp+3440], ymm0
	vmovdqu YMMWORD PTR [rsp+3408], ymm0
	vmovdqu YMMWORD PTR [rsp+3376], ymm0
	vmovdqu YMMWORD PTR [rsp+3344], ymm0
	vmovdqu YMMWORD PTR [rsp+3312], ymm0
	vmovdqu YMMWORD PTR [rsp+3280], ymm0
	vmovdqu YMMWORD PTR [rsp+3248], ymm0
	vmovdqu YMMWORD PTR [rsp+3216], ymm0
	vmovdqu YMMWORD PTR [rsp+3184], ymm0
	vmovdqu YMMWORD PTR [rsp+3152], ymm0
	vmovdqu YMMWORD PTR [rsp+3120], ymm0
	vmovdqu YMMWORD PTR [rsp+3088], ymm0
	vmovdqu YMMWORD PTR [rsp+3056], ymm0
	vmovdqu YMMWORD PTR [rsp+3024], ymm0
	vmovdqu YMMWORD PTR [rsp+2992], ymm0
	vmovdqu YMMWORD PTR [rsp+2960], ymm0
	vmovdqu YMMWORD PTR [rsp+2928], ymm0
	vmovdqu YMMWORD PTR [rsp+2896], ymm0
	vmovdqu YMMWORD PTR [rsp+2864], ymm0
	vmovdqu YMMWORD PTR [rsp+2832], ymm0
	vmovdqu YMMWORD PTR [rsp+2800], ymm0
	vmovdqu YMMWORD PTR [rsp+2768], ymm0
	vmovdqu YMMWORD PTR [rsp+2736], ymm0
	vmovdqu YMMWORD PTR [rsp+2704], ymm0
	vmovdqu YMMWORD PTR [rsp+2672], ymm0
	vmovdqu YMMWORD PTR [rsp+2640], ymm0
	vmovdqu YMMWORD PTR [rsp+2608], ymm0
	vmovdqu YMMWORD PTR [rsp+2576], ymm0
	vmovdqu YMMWORD PTR [rsp+2544], ymm0
	vmovdqu YMMWORD PTR [rsp+2512], ymm0
	vmovdqu YMMWORD PTR [rsp+2480], ymm0
	vmovdqu YMMWORD PTR [rsp+2448], ymm0
	vmovdqu YMMWORD PTR [rsp+2416], ymm0
	vmovdqu YMMWORD PTR [rsp+2384], ymm0
	vmovdqu YMMWORD PTR [rsp+2352], ymm0
	vmovdqu YMMWORD PTR [rsp+2320], ymm0
	vmovdqu YMMWORD PTR [rsp+2288], ymm0
	vmovdqu YMMWORD PTR [rsp+2256], ymm0
	vmovdqu YMMWORD PTR [rsp+2224], ymm0
	vmovdqu YMMWORD PTR [rsp+2192], ymm0
	vmovdqu YMMWORD PTR [rsp+2160], ymm0
	vmovdqu YMMWORD PTR [rsp+2128], ymm0
	vmovdqu YMMWORD PTR [rsp+2096], ymm0
	vmovdqu YMMWORD PTR [rsp+2064], ymm0
	vmovdqu YMMWORD PTR [rsp+2032], ymm0
	vmovdqu YMMWORD PTR [rsp+2000], ymm0
	vmovdqu YMMWORD PTR [rsp+1968], ymm0
	vmovdqu YMMWORD PTR [rsp+1936], ymm0
	vmovdqu YMMWORD PTR [rsp+1904], ymm0
	vmovdqu YMMWORD PTR [rsp+1872], ymm0
	vmovdqu YMMWORD PTR [rsp+1840], ymm0
	vmovdqu YMMWORD PTR [rsp+1808], ymm0
	vmovdqu YMMWORD PTR [rsp+1776], ymm0
	vmovdqu YMMWORD PTR [rsp+1744], ymm0
	vmovdqu YMMWORD PTR [rsp+1712], ymm0
	vmovdqu YMMWORD PTR [rsp+1680], ymm0
	vmovdqu YMMWORD PTR [rsp+1648], ymm0
	vmovdqu YMMWORD PTR [rsp+1616], ymm0
	vmovdqu YMMWORD PTR [rsp+1584], ymm0
	vmovdqu YMMWORD PTR [rsp+1552], ymm0
	vmovdqu YMMWORD PTR [rsp+1520], ymm0
	vmovdqu YMMWORD PTR [rsp+1488], ymm0
	vmovdqu YMMWORD PTR [rsp+1456], ymm0
	vmovdqu YMMWORD PTR [rsp+1424], ymm0
	vmovdqu YMMWORD PTR [rsp+1392], ymm0
	vmovdqu YMMWORD PTR [rsp+1360], ymm0
	vmovdqu YMMWORD PTR [rsp+1328], ymm0
	vmovdqu YMMWORD PTR [rsp+1296], ymm0
	vmovdqu YMMWORD PTR [rsp+1264], ymm0
	vmovdqu YMMWORD PTR [rsp+1232], ymm0
	vmovdqu YMMWORD PTR [rsp+1200], ymm0
	vmovdqu YMMWORD PTR [rsp+1168], ymm0
	vmovdqu YMMWORD PTR [rsp+1136], ymm0
	vmovdqu YMMWORD PTR [rsp+1104], ymm0
	vmovdqu YMMWORD PTR [rsp+1072], ymm0
	vmovdqu YMMWORD PTR [rsp+1040], ymm0
	vmovdqu YMMWORD PTR [rsp+1008], ymm0
	vmovdqu YMMWORD PTR [rsp+976], ymm0
	vmovdqu YMMWORD PTR [rsp+944], ymm0
	vmovdqu YMMWORD PTR [rsp+912], ymm0
	vmovdqu YMMWORD PTR [rsp+880], ymm0
	vmovdqu YMMWORD PTR [rsp+848], ymm0
	vmovdqu YMMWORD PTR [rsp+816], ymm0
	vmovdqu YMMWORD PTR [rsp+784], ymm0
	vmovdqu YMMWORD PTR [rsp+752], ymm0
	vmovdqu YMMWORD PTR [rsp+720], ymm0
	vmovdqu YMMWORD PTR [rsp+688], ymm0
	vmovdqu YMMWORD PTR [rsp+656], ymm0
	vmovdqu YMMWORD PTR [rsp+624], ymm0
	vmovdqu YMMWORD PTR [rsp+592], ymm0
	vmovdqu YMMWORD PTR [rsp+560], ymm0
	vmovdqu YMMWORD PTR [rsp+528], ymm0
	vmovdqu YMMWORD PTR [rsp+496], ymm0
	vmovdqu YMMWORD PTR [rsp+464], ymm0
	vmovdqu YMMWORD PTR [rsp+432], ymm0
	vmovdqu YMMWORD PTR [rsp+400], ymm0
	vmovdqu YMMWORD PTR [rsp+368], ymm0
	vmovdqu YMMWORD PTR [rsp+336], ymm0
	vmovdqu YMMWORD PTR [rsp+304], ymm0
	vmovdqu YMMWORD PTR [rsp+272], ymm0
	vmovdqu YMMWORD PTR [rsp+240], ymm0
	vmovdqu YMMWORD PTR [rsp+208], ymm0
	vmovdqu YMMWORD PTR [rsp+176], ymm0
	vmovdqu YMMWORD PTR [rsp+144], ymm0
	vmovdqu YMMWORD PTR [rsp+112], ymm0
	vmovdqu YMMWORD PTR [rsp+80], ymm0
	vmovdqu YMMWORD PTR [rsp+48], ymm0
	vmovdqu YMMWORD PTR [rsp+16], ymm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+3656]
	jmp 221f
220:
	xor r11d, r11d
	lea rsp, [rsp-3656]
	mov QWORD PTR [rsp+3648], r11
	vmovdqu YMMWORD PTR [rsp+3616], ymm0
	vmovdqu YMMWORD PTR [rsp+3584], ymm0
	vmovdqu YMMWORD PTR [rsp+3552], ymm0
	vmovdqu YMMWORD PTR [rsp+3520], ymm0
	vmovdqu YMMWORD PTR [rsp+3488], ymm0
	vmovdqu YMMWORD PTR [rsp+3456], ymm0
	vmovdqu YMMWORD PTR [rsp+3424], ymm0
	vmovdqu YMMWORD PTR [rsp+3392], ymm0
	vmovdqu YMMWORD PTR [rsp+3360], ymm0
	vmovdqu YMMWORD PTR [rsp+3328], ymm0
	vmovdqu YMMWORD PTR [rsp+3296], ymm0
	vmovdqu YMMWORD PTR [rsp+3264], ymm0
	vmovdqu YMMWORD PTR [rsp+3232], ymm0
	vmovdqu YMMWORD PTR [rsp+3200], ymm0
	vmovdqu YMMWORD PTR [rsp+3168], ymm0
	vmovdqu YMMWORD PTR [rsp+3136], ymm0
	vmovdqu YMMWORD PTR [rsp+3104], ymm0
	vmovdqu YMMWORD PTR [rsp+3072], ymm0
	vmovdqu YMMWORD PTR [rsp+3040], ymm0
	vmovdqu YMMWORD PTR [rsp+3008], ymm0
	vmovdqu YMMWORD PTR [rsp+2976], ymm0
	vmovdqu YMMWORD PTR [rsp+2944], ymm0
	vmovdqu YMMWORD PTR [rsp+2912], ymm0
	vmovdqu YMMWORD PTR [rsp+2880], ymm0
	vmovdqu YMMWORD PTR [rsp+2848], ymm0
	vmovdqu YMMWORD PTR [rsp+2816], ymm0
	vmovdqu YMMWORD PTR [rsp+2784], ymm0
	vmovdqu YMMWORD PTR [rsp+2752], ymm0
	vmovdqu YMMWORD PTR [rsp+2720], ymm0
	vmovdqu YMMWORD PTR [rsp+2688], ymm0
	vmovdqu YMMWORD PTR [rsp+2656], ymm0
	vmovdqu YMMWORD PTR [rsp+2624], ymm0
	vmovdqu YMMWORD PTR [rsp+2592], ymm0
	vmovdqu YMMWORD PTR [rsp+2560], ymm0
	vmovdqu YMMWORD PTR [rsp+2528], ymm0
	vmovdqu YMMWORD PTR [rsp+2496], ymm0
	vmovdqu YMMWORD PTR [rsp+2464], ymm0
	vmovdqu YMMWORD PTR [rsp+2432], ymm0
	vmovdqu YMMWORD PTR [rsp+2400], ymm0
	vmovdqu YMMWORD PTR [rsp+2368], ymm0
	vmovdqu YMMWORD PTR [rsp+2336], ymm0
	vmovdqu YMMWORD PTR [rsp+2304], ymm0
	vmovdqu YMMWORD PTR [rsp+2272], ymm0
	vmovdqu YMMWORD PTR [rsp+2240], ymm0
	vmovdqu YMMWORD PTR [rsp+2208], ymm0
	vmovdqu YMMWORD PTR [rsp+2176], ymm0
	vmovdqu YMMWORD PTR [rsp+2144], ymm0
	vmovdqu YMMWORD PTR [rsp+2112], ymm0
	vmovdqu YMMWORD PTR [rsp+2080], ymm0
	vmovdqu YMMWORD PTR [rsp+2048], ymm0
	vmovdqu YMMWORD PTR [rsp+2016], ymm0
	vmovdqu YMMWORD PTR [rsp+1984], ymm0
	vmovdqu YMMWORD PTR [rsp+1952], ymm0
	vmovdqu YMMWORD PTR [rsp+1920], ymm0
	vmovdqu YMMWORD PTR [rsp+1888], ymm0
	vmovdqu YMMWORD PTR [rsp+1856], ymm0
	vmovdqu YMMWORD PTR [rsp+1824], ymm0
	vmovdqu YMMWORD PTR [rsp+1792], ymm0
	vmovdqu YMMWORD PTR [rsp+1760], ymm0
	vmovdqu YMMWORD PTR [rsp+1728], ymm0
	vmovdqu YMMWORD PTR [rsp+1696], ymm0
	vmovdqu YMMWORD PTR [rsp+1664], ymm0
	vmovdqu YMMWORD PTR [rsp+1632], ymm0
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
	lea rsp, [rsp+3656]
221:
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

vg_rsa_pss_sign_precomputed_crt_ifma:
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
	mov rax, QWORD PTR [rsp+544]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+552]
	mov QWORD PTR [rsp+120], rax
	call {vg_rsa_private_checked_precomputed_ifma}
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
	mov r11d, 16
	test r11d, esp
	je 220f
	xor r11d, r11d
	lea rsp, [rsp-3656]
	mov QWORD PTR [rsp+3648], r11
	movdqu XMMWORD PTR [rsp+3632], xmm0
	vmovdqu YMMWORD PTR [rsp+3600], ymm0
	vmovdqu YMMWORD PTR [rsp+3568], ymm0
	vmovdqu YMMWORD PTR [rsp+3536], ymm0
	vmovdqu YMMWORD PTR [rsp+3504], ymm0
	vmovdqu YMMWORD PTR [rsp+3472], ymm0
	vmovdqu YMMWORD PTR [rsp+3440], ymm0
	vmovdqu YMMWORD PTR [rsp+3408], ymm0
	vmovdqu YMMWORD PTR [rsp+3376], ymm0
	vmovdqu YMMWORD PTR [rsp+3344], ymm0
	vmovdqu YMMWORD PTR [rsp+3312], ymm0
	vmovdqu YMMWORD PTR [rsp+3280], ymm0
	vmovdqu YMMWORD PTR [rsp+3248], ymm0
	vmovdqu YMMWORD PTR [rsp+3216], ymm0
	vmovdqu YMMWORD PTR [rsp+3184], ymm0
	vmovdqu YMMWORD PTR [rsp+3152], ymm0
	vmovdqu YMMWORD PTR [rsp+3120], ymm0
	vmovdqu YMMWORD PTR [rsp+3088], ymm0
	vmovdqu YMMWORD PTR [rsp+3056], ymm0
	vmovdqu YMMWORD PTR [rsp+3024], ymm0
	vmovdqu YMMWORD PTR [rsp+2992], ymm0
	vmovdqu YMMWORD PTR [rsp+2960], ymm0
	vmovdqu YMMWORD PTR [rsp+2928], ymm0
	vmovdqu YMMWORD PTR [rsp+2896], ymm0
	vmovdqu YMMWORD PTR [rsp+2864], ymm0
	vmovdqu YMMWORD PTR [rsp+2832], ymm0
	vmovdqu YMMWORD PTR [rsp+2800], ymm0
	vmovdqu YMMWORD PTR [rsp+2768], ymm0
	vmovdqu YMMWORD PTR [rsp+2736], ymm0
	vmovdqu YMMWORD PTR [rsp+2704], ymm0
	vmovdqu YMMWORD PTR [rsp+2672], ymm0
	vmovdqu YMMWORD PTR [rsp+2640], ymm0
	vmovdqu YMMWORD PTR [rsp+2608], ymm0
	vmovdqu YMMWORD PTR [rsp+2576], ymm0
	vmovdqu YMMWORD PTR [rsp+2544], ymm0
	vmovdqu YMMWORD PTR [rsp+2512], ymm0
	vmovdqu YMMWORD PTR [rsp+2480], ymm0
	vmovdqu YMMWORD PTR [rsp+2448], ymm0
	vmovdqu YMMWORD PTR [rsp+2416], ymm0
	vmovdqu YMMWORD PTR [rsp+2384], ymm0
	vmovdqu YMMWORD PTR [rsp+2352], ymm0
	vmovdqu YMMWORD PTR [rsp+2320], ymm0
	vmovdqu YMMWORD PTR [rsp+2288], ymm0
	vmovdqu YMMWORD PTR [rsp+2256], ymm0
	vmovdqu YMMWORD PTR [rsp+2224], ymm0
	vmovdqu YMMWORD PTR [rsp+2192], ymm0
	vmovdqu YMMWORD PTR [rsp+2160], ymm0
	vmovdqu YMMWORD PTR [rsp+2128], ymm0
	vmovdqu YMMWORD PTR [rsp+2096], ymm0
	vmovdqu YMMWORD PTR [rsp+2064], ymm0
	vmovdqu YMMWORD PTR [rsp+2032], ymm0
	vmovdqu YMMWORD PTR [rsp+2000], ymm0
	vmovdqu YMMWORD PTR [rsp+1968], ymm0
	vmovdqu YMMWORD PTR [rsp+1936], ymm0
	vmovdqu YMMWORD PTR [rsp+1904], ymm0
	vmovdqu YMMWORD PTR [rsp+1872], ymm0
	vmovdqu YMMWORD PTR [rsp+1840], ymm0
	vmovdqu YMMWORD PTR [rsp+1808], ymm0
	vmovdqu YMMWORD PTR [rsp+1776], ymm0
	vmovdqu YMMWORD PTR [rsp+1744], ymm0
	vmovdqu YMMWORD PTR [rsp+1712], ymm0
	vmovdqu YMMWORD PTR [rsp+1680], ymm0
	vmovdqu YMMWORD PTR [rsp+1648], ymm0
	vmovdqu YMMWORD PTR [rsp+1616], ymm0
	vmovdqu YMMWORD PTR [rsp+1584], ymm0
	vmovdqu YMMWORD PTR [rsp+1552], ymm0
	vmovdqu YMMWORD PTR [rsp+1520], ymm0
	vmovdqu YMMWORD PTR [rsp+1488], ymm0
	vmovdqu YMMWORD PTR [rsp+1456], ymm0
	vmovdqu YMMWORD PTR [rsp+1424], ymm0
	vmovdqu YMMWORD PTR [rsp+1392], ymm0
	vmovdqu YMMWORD PTR [rsp+1360], ymm0
	vmovdqu YMMWORD PTR [rsp+1328], ymm0
	vmovdqu YMMWORD PTR [rsp+1296], ymm0
	vmovdqu YMMWORD PTR [rsp+1264], ymm0
	vmovdqu YMMWORD PTR [rsp+1232], ymm0
	vmovdqu YMMWORD PTR [rsp+1200], ymm0
	vmovdqu YMMWORD PTR [rsp+1168], ymm0
	vmovdqu YMMWORD PTR [rsp+1136], ymm0
	vmovdqu YMMWORD PTR [rsp+1104], ymm0
	vmovdqu YMMWORD PTR [rsp+1072], ymm0
	vmovdqu YMMWORD PTR [rsp+1040], ymm0
	vmovdqu YMMWORD PTR [rsp+1008], ymm0
	vmovdqu YMMWORD PTR [rsp+976], ymm0
	vmovdqu YMMWORD PTR [rsp+944], ymm0
	vmovdqu YMMWORD PTR [rsp+912], ymm0
	vmovdqu YMMWORD PTR [rsp+880], ymm0
	vmovdqu YMMWORD PTR [rsp+848], ymm0
	vmovdqu YMMWORD PTR [rsp+816], ymm0
	vmovdqu YMMWORD PTR [rsp+784], ymm0
	vmovdqu YMMWORD PTR [rsp+752], ymm0
	vmovdqu YMMWORD PTR [rsp+720], ymm0
	vmovdqu YMMWORD PTR [rsp+688], ymm0
	vmovdqu YMMWORD PTR [rsp+656], ymm0
	vmovdqu YMMWORD PTR [rsp+624], ymm0
	vmovdqu YMMWORD PTR [rsp+592], ymm0
	vmovdqu YMMWORD PTR [rsp+560], ymm0
	vmovdqu YMMWORD PTR [rsp+528], ymm0
	vmovdqu YMMWORD PTR [rsp+496], ymm0
	vmovdqu YMMWORD PTR [rsp+464], ymm0
	vmovdqu YMMWORD PTR [rsp+432], ymm0
	vmovdqu YMMWORD PTR [rsp+400], ymm0
	vmovdqu YMMWORD PTR [rsp+368], ymm0
	vmovdqu YMMWORD PTR [rsp+336], ymm0
	vmovdqu YMMWORD PTR [rsp+304], ymm0
	vmovdqu YMMWORD PTR [rsp+272], ymm0
	vmovdqu YMMWORD PTR [rsp+240], ymm0
	vmovdqu YMMWORD PTR [rsp+208], ymm0
	vmovdqu YMMWORD PTR [rsp+176], ymm0
	vmovdqu YMMWORD PTR [rsp+144], ymm0
	vmovdqu YMMWORD PTR [rsp+112], ymm0
	vmovdqu YMMWORD PTR [rsp+80], ymm0
	vmovdqu YMMWORD PTR [rsp+48], ymm0
	vmovdqu YMMWORD PTR [rsp+16], ymm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+3656]
	jmp 221f
220:
	xor r11d, r11d
	lea rsp, [rsp-3656]
	mov QWORD PTR [rsp+3648], r11
	vmovdqu YMMWORD PTR [rsp+3616], ymm0
	vmovdqu YMMWORD PTR [rsp+3584], ymm0
	vmovdqu YMMWORD PTR [rsp+3552], ymm0
	vmovdqu YMMWORD PTR [rsp+3520], ymm0
	vmovdqu YMMWORD PTR [rsp+3488], ymm0
	vmovdqu YMMWORD PTR [rsp+3456], ymm0
	vmovdqu YMMWORD PTR [rsp+3424], ymm0
	vmovdqu YMMWORD PTR [rsp+3392], ymm0
	vmovdqu YMMWORD PTR [rsp+3360], ymm0
	vmovdqu YMMWORD PTR [rsp+3328], ymm0
	vmovdqu YMMWORD PTR [rsp+3296], ymm0
	vmovdqu YMMWORD PTR [rsp+3264], ymm0
	vmovdqu YMMWORD PTR [rsp+3232], ymm0
	vmovdqu YMMWORD PTR [rsp+3200], ymm0
	vmovdqu YMMWORD PTR [rsp+3168], ymm0
	vmovdqu YMMWORD PTR [rsp+3136], ymm0
	vmovdqu YMMWORD PTR [rsp+3104], ymm0
	vmovdqu YMMWORD PTR [rsp+3072], ymm0
	vmovdqu YMMWORD PTR [rsp+3040], ymm0
	vmovdqu YMMWORD PTR [rsp+3008], ymm0
	vmovdqu YMMWORD PTR [rsp+2976], ymm0
	vmovdqu YMMWORD PTR [rsp+2944], ymm0
	vmovdqu YMMWORD PTR [rsp+2912], ymm0
	vmovdqu YMMWORD PTR [rsp+2880], ymm0
	vmovdqu YMMWORD PTR [rsp+2848], ymm0
	vmovdqu YMMWORD PTR [rsp+2816], ymm0
	vmovdqu YMMWORD PTR [rsp+2784], ymm0
	vmovdqu YMMWORD PTR [rsp+2752], ymm0
	vmovdqu YMMWORD PTR [rsp+2720], ymm0
	vmovdqu YMMWORD PTR [rsp+2688], ymm0
	vmovdqu YMMWORD PTR [rsp+2656], ymm0
	vmovdqu YMMWORD PTR [rsp+2624], ymm0
	vmovdqu YMMWORD PTR [rsp+2592], ymm0
	vmovdqu YMMWORD PTR [rsp+2560], ymm0
	vmovdqu YMMWORD PTR [rsp+2528], ymm0
	vmovdqu YMMWORD PTR [rsp+2496], ymm0
	vmovdqu YMMWORD PTR [rsp+2464], ymm0
	vmovdqu YMMWORD PTR [rsp+2432], ymm0
	vmovdqu YMMWORD PTR [rsp+2400], ymm0
	vmovdqu YMMWORD PTR [rsp+2368], ymm0
	vmovdqu YMMWORD PTR [rsp+2336], ymm0
	vmovdqu YMMWORD PTR [rsp+2304], ymm0
	vmovdqu YMMWORD PTR [rsp+2272], ymm0
	vmovdqu YMMWORD PTR [rsp+2240], ymm0
	vmovdqu YMMWORD PTR [rsp+2208], ymm0
	vmovdqu YMMWORD PTR [rsp+2176], ymm0
	vmovdqu YMMWORD PTR [rsp+2144], ymm0
	vmovdqu YMMWORD PTR [rsp+2112], ymm0
	vmovdqu YMMWORD PTR [rsp+2080], ymm0
	vmovdqu YMMWORD PTR [rsp+2048], ymm0
	vmovdqu YMMWORD PTR [rsp+2016], ymm0
	vmovdqu YMMWORD PTR [rsp+1984], ymm0
	vmovdqu YMMWORD PTR [rsp+1952], ymm0
	vmovdqu YMMWORD PTR [rsp+1920], ymm0
	vmovdqu YMMWORD PTR [rsp+1888], ymm0
	vmovdqu YMMWORD PTR [rsp+1856], ymm0
	vmovdqu YMMWORD PTR [rsp+1824], ymm0
	vmovdqu YMMWORD PTR [rsp+1792], ymm0
	vmovdqu YMMWORD PTR [rsp+1760], ymm0
	vmovdqu YMMWORD PTR [rsp+1728], ymm0
	vmovdqu YMMWORD PTR [rsp+1696], ymm0
	vmovdqu YMMWORD PTR [rsp+1664], ymm0
	vmovdqu YMMWORD PTR [rsp+1632], ymm0
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
	lea rsp, [rsp+3656]
221:
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

vg_rsa_pss_sign_precomputed_crt_adx:
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
	mov rax, QWORD PTR [rsp+544]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+552]
	mov QWORD PTR [rsp+120], rax
	call {vg_rsa_private_checked_precomputed_adx}
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
	mov r11d, 16
	test r11d, esp
	je 220f
	xor r11d, r11d
	lea rsp, [rsp-3656]
	mov QWORD PTR [rsp+3648], r11
	movdqu XMMWORD PTR [rsp+3632], xmm0
	vmovdqu YMMWORD PTR [rsp+3600], ymm0
	vmovdqu YMMWORD PTR [rsp+3568], ymm0
	vmovdqu YMMWORD PTR [rsp+3536], ymm0
	vmovdqu YMMWORD PTR [rsp+3504], ymm0
	vmovdqu YMMWORD PTR [rsp+3472], ymm0
	vmovdqu YMMWORD PTR [rsp+3440], ymm0
	vmovdqu YMMWORD PTR [rsp+3408], ymm0
	vmovdqu YMMWORD PTR [rsp+3376], ymm0
	vmovdqu YMMWORD PTR [rsp+3344], ymm0
	vmovdqu YMMWORD PTR [rsp+3312], ymm0
	vmovdqu YMMWORD PTR [rsp+3280], ymm0
	vmovdqu YMMWORD PTR [rsp+3248], ymm0
	vmovdqu YMMWORD PTR [rsp+3216], ymm0
	vmovdqu YMMWORD PTR [rsp+3184], ymm0
	vmovdqu YMMWORD PTR [rsp+3152], ymm0
	vmovdqu YMMWORD PTR [rsp+3120], ymm0
	vmovdqu YMMWORD PTR [rsp+3088], ymm0
	vmovdqu YMMWORD PTR [rsp+3056], ymm0
	vmovdqu YMMWORD PTR [rsp+3024], ymm0
	vmovdqu YMMWORD PTR [rsp+2992], ymm0
	vmovdqu YMMWORD PTR [rsp+2960], ymm0
	vmovdqu YMMWORD PTR [rsp+2928], ymm0
	vmovdqu YMMWORD PTR [rsp+2896], ymm0
	vmovdqu YMMWORD PTR [rsp+2864], ymm0
	vmovdqu YMMWORD PTR [rsp+2832], ymm0
	vmovdqu YMMWORD PTR [rsp+2800], ymm0
	vmovdqu YMMWORD PTR [rsp+2768], ymm0
	vmovdqu YMMWORD PTR [rsp+2736], ymm0
	vmovdqu YMMWORD PTR [rsp+2704], ymm0
	vmovdqu YMMWORD PTR [rsp+2672], ymm0
	vmovdqu YMMWORD PTR [rsp+2640], ymm0
	vmovdqu YMMWORD PTR [rsp+2608], ymm0
	vmovdqu YMMWORD PTR [rsp+2576], ymm0
	vmovdqu YMMWORD PTR [rsp+2544], ymm0
	vmovdqu YMMWORD PTR [rsp+2512], ymm0
	vmovdqu YMMWORD PTR [rsp+2480], ymm0
	vmovdqu YMMWORD PTR [rsp+2448], ymm0
	vmovdqu YMMWORD PTR [rsp+2416], ymm0
	vmovdqu YMMWORD PTR [rsp+2384], ymm0
	vmovdqu YMMWORD PTR [rsp+2352], ymm0
	vmovdqu YMMWORD PTR [rsp+2320], ymm0
	vmovdqu YMMWORD PTR [rsp+2288], ymm0
	vmovdqu YMMWORD PTR [rsp+2256], ymm0
	vmovdqu YMMWORD PTR [rsp+2224], ymm0
	vmovdqu YMMWORD PTR [rsp+2192], ymm0
	vmovdqu YMMWORD PTR [rsp+2160], ymm0
	vmovdqu YMMWORD PTR [rsp+2128], ymm0
	vmovdqu YMMWORD PTR [rsp+2096], ymm0
	vmovdqu YMMWORD PTR [rsp+2064], ymm0
	vmovdqu YMMWORD PTR [rsp+2032], ymm0
	vmovdqu YMMWORD PTR [rsp+2000], ymm0
	vmovdqu YMMWORD PTR [rsp+1968], ymm0
	vmovdqu YMMWORD PTR [rsp+1936], ymm0
	vmovdqu YMMWORD PTR [rsp+1904], ymm0
	vmovdqu YMMWORD PTR [rsp+1872], ymm0
	vmovdqu YMMWORD PTR [rsp+1840], ymm0
	vmovdqu YMMWORD PTR [rsp+1808], ymm0
	vmovdqu YMMWORD PTR [rsp+1776], ymm0
	vmovdqu YMMWORD PTR [rsp+1744], ymm0
	vmovdqu YMMWORD PTR [rsp+1712], ymm0
	vmovdqu YMMWORD PTR [rsp+1680], ymm0
	vmovdqu YMMWORD PTR [rsp+1648], ymm0
	vmovdqu YMMWORD PTR [rsp+1616], ymm0
	vmovdqu YMMWORD PTR [rsp+1584], ymm0
	vmovdqu YMMWORD PTR [rsp+1552], ymm0
	vmovdqu YMMWORD PTR [rsp+1520], ymm0
	vmovdqu YMMWORD PTR [rsp+1488], ymm0
	vmovdqu YMMWORD PTR [rsp+1456], ymm0
	vmovdqu YMMWORD PTR [rsp+1424], ymm0
	vmovdqu YMMWORD PTR [rsp+1392], ymm0
	vmovdqu YMMWORD PTR [rsp+1360], ymm0
	vmovdqu YMMWORD PTR [rsp+1328], ymm0
	vmovdqu YMMWORD PTR [rsp+1296], ymm0
	vmovdqu YMMWORD PTR [rsp+1264], ymm0
	vmovdqu YMMWORD PTR [rsp+1232], ymm0
	vmovdqu YMMWORD PTR [rsp+1200], ymm0
	vmovdqu YMMWORD PTR [rsp+1168], ymm0
	vmovdqu YMMWORD PTR [rsp+1136], ymm0
	vmovdqu YMMWORD PTR [rsp+1104], ymm0
	vmovdqu YMMWORD PTR [rsp+1072], ymm0
	vmovdqu YMMWORD PTR [rsp+1040], ymm0
	vmovdqu YMMWORD PTR [rsp+1008], ymm0
	vmovdqu YMMWORD PTR [rsp+976], ymm0
	vmovdqu YMMWORD PTR [rsp+944], ymm0
	vmovdqu YMMWORD PTR [rsp+912], ymm0
	vmovdqu YMMWORD PTR [rsp+880], ymm0
	vmovdqu YMMWORD PTR [rsp+848], ymm0
	vmovdqu YMMWORD PTR [rsp+816], ymm0
	vmovdqu YMMWORD PTR [rsp+784], ymm0
	vmovdqu YMMWORD PTR [rsp+752], ymm0
	vmovdqu YMMWORD PTR [rsp+720], ymm0
	vmovdqu YMMWORD PTR [rsp+688], ymm0
	vmovdqu YMMWORD PTR [rsp+656], ymm0
	vmovdqu YMMWORD PTR [rsp+624], ymm0
	vmovdqu YMMWORD PTR [rsp+592], ymm0
	vmovdqu YMMWORD PTR [rsp+560], ymm0
	vmovdqu YMMWORD PTR [rsp+528], ymm0
	vmovdqu YMMWORD PTR [rsp+496], ymm0
	vmovdqu YMMWORD PTR [rsp+464], ymm0
	vmovdqu YMMWORD PTR [rsp+432], ymm0
	vmovdqu YMMWORD PTR [rsp+400], ymm0
	vmovdqu YMMWORD PTR [rsp+368], ymm0
	vmovdqu YMMWORD PTR [rsp+336], ymm0
	vmovdqu YMMWORD PTR [rsp+304], ymm0
	vmovdqu YMMWORD PTR [rsp+272], ymm0
	vmovdqu YMMWORD PTR [rsp+240], ymm0
	vmovdqu YMMWORD PTR [rsp+208], ymm0
	vmovdqu YMMWORD PTR [rsp+176], ymm0
	vmovdqu YMMWORD PTR [rsp+144], ymm0
	vmovdqu YMMWORD PTR [rsp+112], ymm0
	vmovdqu YMMWORD PTR [rsp+80], ymm0
	vmovdqu YMMWORD PTR [rsp+48], ymm0
	vmovdqu YMMWORD PTR [rsp+16], ymm0
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+3656]
	jmp 221f
220:
	xor r11d, r11d
	lea rsp, [rsp-3656]
	mov QWORD PTR [rsp+3648], r11
	vmovdqu YMMWORD PTR [rsp+3616], ymm0
	vmovdqu YMMWORD PTR [rsp+3584], ymm0
	vmovdqu YMMWORD PTR [rsp+3552], ymm0
	vmovdqu YMMWORD PTR [rsp+3520], ymm0
	vmovdqu YMMWORD PTR [rsp+3488], ymm0
	vmovdqu YMMWORD PTR [rsp+3456], ymm0
	vmovdqu YMMWORD PTR [rsp+3424], ymm0
	vmovdqu YMMWORD PTR [rsp+3392], ymm0
	vmovdqu YMMWORD PTR [rsp+3360], ymm0
	vmovdqu YMMWORD PTR [rsp+3328], ymm0
	vmovdqu YMMWORD PTR [rsp+3296], ymm0
	vmovdqu YMMWORD PTR [rsp+3264], ymm0
	vmovdqu YMMWORD PTR [rsp+3232], ymm0
	vmovdqu YMMWORD PTR [rsp+3200], ymm0
	vmovdqu YMMWORD PTR [rsp+3168], ymm0
	vmovdqu YMMWORD PTR [rsp+3136], ymm0
	vmovdqu YMMWORD PTR [rsp+3104], ymm0
	vmovdqu YMMWORD PTR [rsp+3072], ymm0
	vmovdqu YMMWORD PTR [rsp+3040], ymm0
	vmovdqu YMMWORD PTR [rsp+3008], ymm0
	vmovdqu YMMWORD PTR [rsp+2976], ymm0
	vmovdqu YMMWORD PTR [rsp+2944], ymm0
	vmovdqu YMMWORD PTR [rsp+2912], ymm0
	vmovdqu YMMWORD PTR [rsp+2880], ymm0
	vmovdqu YMMWORD PTR [rsp+2848], ymm0
	vmovdqu YMMWORD PTR [rsp+2816], ymm0
	vmovdqu YMMWORD PTR [rsp+2784], ymm0
	vmovdqu YMMWORD PTR [rsp+2752], ymm0
	vmovdqu YMMWORD PTR [rsp+2720], ymm0
	vmovdqu YMMWORD PTR [rsp+2688], ymm0
	vmovdqu YMMWORD PTR [rsp+2656], ymm0
	vmovdqu YMMWORD PTR [rsp+2624], ymm0
	vmovdqu YMMWORD PTR [rsp+2592], ymm0
	vmovdqu YMMWORD PTR [rsp+2560], ymm0
	vmovdqu YMMWORD PTR [rsp+2528], ymm0
	vmovdqu YMMWORD PTR [rsp+2496], ymm0
	vmovdqu YMMWORD PTR [rsp+2464], ymm0
	vmovdqu YMMWORD PTR [rsp+2432], ymm0
	vmovdqu YMMWORD PTR [rsp+2400], ymm0
	vmovdqu YMMWORD PTR [rsp+2368], ymm0
	vmovdqu YMMWORD PTR [rsp+2336], ymm0
	vmovdqu YMMWORD PTR [rsp+2304], ymm0
	vmovdqu YMMWORD PTR [rsp+2272], ymm0
	vmovdqu YMMWORD PTR [rsp+2240], ymm0
	vmovdqu YMMWORD PTR [rsp+2208], ymm0
	vmovdqu YMMWORD PTR [rsp+2176], ymm0
	vmovdqu YMMWORD PTR [rsp+2144], ymm0
	vmovdqu YMMWORD PTR [rsp+2112], ymm0
	vmovdqu YMMWORD PTR [rsp+2080], ymm0
	vmovdqu YMMWORD PTR [rsp+2048], ymm0
	vmovdqu YMMWORD PTR [rsp+2016], ymm0
	vmovdqu YMMWORD PTR [rsp+1984], ymm0
	vmovdqu YMMWORD PTR [rsp+1952], ymm0
	vmovdqu YMMWORD PTR [rsp+1920], ymm0
	vmovdqu YMMWORD PTR [rsp+1888], ymm0
	vmovdqu YMMWORD PTR [rsp+1856], ymm0
	vmovdqu YMMWORD PTR [rsp+1824], ymm0
	vmovdqu YMMWORD PTR [rsp+1792], ymm0
	vmovdqu YMMWORD PTR [rsp+1760], ymm0
	vmovdqu YMMWORD PTR [rsp+1728], ymm0
	vmovdqu YMMWORD PTR [rsp+1696], ymm0
	vmovdqu YMMWORD PTR [rsp+1664], ymm0
	vmovdqu YMMWORD PTR [rsp+1632], ymm0
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
	lea rsp, [rsp+3656]
221:
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

vg_rsa_pss_sign_precomputed:
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
	mov rax, QWORD PTR [rsp+544]
	mov QWORD PTR [rsp+112], rax
	mov rax, QWORD PTR [rsp+552]
	mov QWORD PTR [rsp+120], rax
	call {vg_rsa_private_checked_precomputed}
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
	lea rsp, [rsp-3656]
	mov QWORD PTR [rsp+3648], r11
	movdqu XMMWORD PTR [rsp+3632], xmm0
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
