// The functions of `src/rsa_pkcs1_enc.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pkcs1_decrypt_sha256_shani_crt_ifma512:
	lea rsp, [rsp-216]
	mov QWORD PTR [rsp+112], rdi
	mov QWORD PTR [rsp+120], rdx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], r8
	mov QWORD PTR [rsp+144], r9
	mov rax, QWORD PTR [rsp+224]
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+232]
	mov QWORD PTR [rsp+160], rax
	mov rax, QWORD PTR [rsp+240]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+176], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+184], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+296]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+104], rax
	mov rsi, r8
	mov rdx, rcx
	mov rcx, r8
	mov r8, r9
	mov r9, QWORD PTR [rsp+152]
	call {vg_rsa_private_checked_ifma512}
	mov QWORD PTR [rsp+192], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+136]
	mov r10d, 0
	mov eax, 0
20:
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 20b
	mov rsi, QWORD PTR [rsp+160]
	mov rcx, QWORD PTR [rsp+168]
	mov rdi, QWORD PTR [rsp+184]
	add rdi, QWORD PTR [rsp+136]
	sub rdi, rcx
	mov r10d, 0
21:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 21b
	mov rdi, QWORD PTR [rsp+184]
	call {vg_sha256_init_core}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2416
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 192
	call {vg_sha256_finalize_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+136]
	add rdx, 64
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1104
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_shani}
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+136]
	add rax, 31
	shr rax, 5
	mov QWORD PTR [rsp+208], rax
22:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 108
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 110
	mov BYTE PTR [rdi+1028], dl
	mov edx, 103
	mov BYTE PTR [rdi+1029], dl
	mov edx, 116
	mov BYTE PTR [rdi+1030], dl
	mov edx, 104
	mov BYTE PTR [rdi+1031], dl
	mov edx, 8
	mov BYTE PTR [rdi+1032], dl
	mov edx, 0
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 10
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 74
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1136
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_shani}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, 8
	jne 22b
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
23:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 109
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 115
	mov BYTE PTR [rdi+1028], dl
	mov edx, 115
	mov BYTE PTR [rdi+1029], dl
	mov edx, 97
	mov BYTE PTR [rdi+1030], dl
	mov edx, 103
	mov BYTE PTR [rdi+1031], dl
	mov edx, 101
	mov BYTE PTR [rdi+1032], dl
	mov rdx, r9
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	mov BYTE PTR [rdi+1034], dl
	shr rdx, 8
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 11
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 75
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_shani}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, QWORD PTR [rsp+208]
	jne 23b
	mov r9, QWORD PTR [rsp+136]
	sub r9, 11
	mov r8d, 0
24:
	add r8, r8
	add r8, 1
	cmp r8, r9
	jb 24b
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 1136
	mov ecx, 0
	mov r11d, 0
25:
	movzx eax, BYTE PTR [rsi+rcx*1]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx edx, BYTE PTR [rsi+rcx*1+1]
	add rax, rdx
	and rax, r8
	mov rdx, r9
	cmp rdx, rax
	sbb rdx, rdx
	xor r11, rax
	and r11, rdx
	xor r11, rax
	add rcx, 2
	cmp rcx, 256
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	mov r9, QWORD PTR [rsp+136]
	mov ecx, 2
	mov edx, 0
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rdi+rcx*1]
	cmp rax, 1
	sbb rax, rax
	mov rsi, rdx
	xor rsi, -1
	and rsi, rax
	and rsi, rcx
	or r10, rsi
	or rdx, rax
	add rcx, 1
	cmp rcx, r9
	jne 26b
	movzx eax, BYTE PTR [rdi]
	cmp rax, 1
	sbb rax, rax
	movzx esi, BYTE PTR [rdi+1]
	xor rsi, 2
	cmp rsi, 1
	sbb rsi, rsi
	and rax, rsi
	and rax, rdx
	mov rsi, r10
	cmp rsi, 10
	sbb rsi, rsi
	xor rsi, -1
	and rax, rsi
	mov rsi, r9
	sub rsi, r10
	sub rsi, 1
	mov rdx, r11
	xor rdx, rsi
	and rdx, rax
	xor rdx, r11
	mov r10, rax
	mov r11, QWORD PTR [rsp+192]
	mov r11d, r11d
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rsi, r9
	sub rsi, rdx
	and rdx, r11
	mov r8, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov QWORD PTR [r8], rdx
	mov rdx, rsi
	mov rsi, rcx
	mov ecx, 0
27:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	and rax, r10
	xor rax, r8
	mov r8, rcx
	cmp r8, rdx
	sbb r8, r8
	xor r8, -1
	and r8, r11
	and rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, r9
	jne 27b
	mov rax, QWORD PTR [rsp+192]
	lea rsp, [rsp+216]
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
	lea rsp, [rsp-3480]
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
	lea rsp, [rsp+3480]
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

vg_rsa_pkcs1_decrypt_precomputed_sha256_shani_crt_ifma512:
	lea rsp, [rsp-216]
	mov QWORD PTR [rsp+112], rdi
	mov QWORD PTR [rsp+120], rdx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], r8
	mov QWORD PTR [rsp+144], r9
	mov rax, QWORD PTR [rsp+224]
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+232]
	mov QWORD PTR [rsp+160], rax
	mov rax, QWORD PTR [rsp+240]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+176], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+184], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+296]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+104], rax
	mov rsi, r8
	mov rdx, rcx
	mov rcx, r8
	mov r8, r9
	mov r9, QWORD PTR [rsp+152]
	call {vg_rsa_private_checked_ifma512}
	mov QWORD PTR [rsp+192], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+136]
	mov r10d, 0
	mov eax, 0
20:
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 20b
	mov rsi, QWORD PTR [rsp+160]
	mov rcx, QWORD PTR [rsp+168]
	mov rdi, QWORD PTR [rsp+184]
	add rdi, QWORD PTR [rsp+136]
	sub rdi, rcx
	mov r10d, 0
21:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 21b
	mov rdi, QWORD PTR [rsp+184]
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2416
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 192
	call {vg_sha256_finalize_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+136]
	add rdx, 64
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1104
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_shani}
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+136]
	add rax, 31
	shr rax, 5
	mov QWORD PTR [rsp+208], rax
22:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 108
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 110
	mov BYTE PTR [rdi+1028], dl
	mov edx, 103
	mov BYTE PTR [rdi+1029], dl
	mov edx, 116
	mov BYTE PTR [rdi+1030], dl
	mov edx, 104
	mov BYTE PTR [rdi+1031], dl
	mov edx, 8
	mov BYTE PTR [rdi+1032], dl
	mov edx, 0
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 10
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 74
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1136
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_shani}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, 8
	jne 22b
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
23:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 109
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 115
	mov BYTE PTR [rdi+1028], dl
	mov edx, 115
	mov BYTE PTR [rdi+1029], dl
	mov edx, 97
	mov BYTE PTR [rdi+1030], dl
	mov edx, 103
	mov BYTE PTR [rdi+1031], dl
	mov edx, 101
	mov BYTE PTR [rdi+1032], dl
	mov rdx, r9
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	mov BYTE PTR [rdi+1034], dl
	shr rdx, 8
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 11
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 75
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_shani}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, QWORD PTR [rsp+208]
	jne 23b
	mov r9, QWORD PTR [rsp+136]
	sub r9, 11
	mov r8d, 0
24:
	add r8, r8
	add r8, 1
	cmp r8, r9
	jb 24b
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 1136
	mov ecx, 0
	mov r11d, 0
25:
	movzx eax, BYTE PTR [rsi+rcx*1]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx edx, BYTE PTR [rsi+rcx*1+1]
	add rax, rdx
	and rax, r8
	mov rdx, r9
	cmp rdx, rax
	sbb rdx, rdx
	xor r11, rax
	and r11, rdx
	xor r11, rax
	add rcx, 2
	cmp rcx, 256
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	mov r9, QWORD PTR [rsp+136]
	mov ecx, 2
	mov edx, 0
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rdi+rcx*1]
	cmp rax, 1
	sbb rax, rax
	mov rsi, rdx
	xor rsi, -1
	and rsi, rax
	and rsi, rcx
	or r10, rsi
	or rdx, rax
	add rcx, 1
	cmp rcx, r9
	jne 26b
	movzx eax, BYTE PTR [rdi]
	cmp rax, 1
	sbb rax, rax
	movzx esi, BYTE PTR [rdi+1]
	xor rsi, 2
	cmp rsi, 1
	sbb rsi, rsi
	and rax, rsi
	and rax, rdx
	mov rsi, r10
	cmp rsi, 10
	sbb rsi, rsi
	xor rsi, -1
	and rax, rsi
	mov rsi, r9
	sub rsi, r10
	sub rsi, 1
	mov rdx, r11
	xor rdx, rsi
	and rdx, rax
	xor rdx, r11
	mov r10, rax
	mov r11, QWORD PTR [rsp+192]
	mov r11d, r11d
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rsi, r9
	sub rsi, rdx
	and rdx, r11
	mov r8, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov QWORD PTR [r8], rdx
	mov rdx, rsi
	mov rsi, rcx
	mov ecx, 0
27:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	and rax, r10
	xor rax, r8
	mov r8, rcx
	cmp r8, rdx
	sbb r8, r8
	xor r8, -1
	and r8, r11
	and rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, r9
	jne 27b
	mov rax, QWORD PTR [rsp+192]
	lea rsp, [rsp+216]
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
	lea rsp, [rsp-3480]
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
	lea rsp, [rsp+3480]
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

vg_rsa_pkcs1_decrypt_sha256_shani_crt_ifma:
	lea rsp, [rsp-216]
	mov QWORD PTR [rsp+112], rdi
	mov QWORD PTR [rsp+120], rdx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], r8
	mov QWORD PTR [rsp+144], r9
	mov rax, QWORD PTR [rsp+224]
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+232]
	mov QWORD PTR [rsp+160], rax
	mov rax, QWORD PTR [rsp+240]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+176], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+184], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+296]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+104], rax
	mov rsi, r8
	mov rdx, rcx
	mov rcx, r8
	mov r8, r9
	mov r9, QWORD PTR [rsp+152]
	call {vg_rsa_private_checked_ifma}
	mov QWORD PTR [rsp+192], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+136]
	mov r10d, 0
	mov eax, 0
20:
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 20b
	mov rsi, QWORD PTR [rsp+160]
	mov rcx, QWORD PTR [rsp+168]
	mov rdi, QWORD PTR [rsp+184]
	add rdi, QWORD PTR [rsp+136]
	sub rdi, rcx
	mov r10d, 0
21:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 21b
	mov rdi, QWORD PTR [rsp+184]
	call {vg_sha256_init_core}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2416
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 192
	call {vg_sha256_finalize_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+136]
	add rdx, 64
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1104
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_shani}
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+136]
	add rax, 31
	shr rax, 5
	mov QWORD PTR [rsp+208], rax
22:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 108
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 110
	mov BYTE PTR [rdi+1028], dl
	mov edx, 103
	mov BYTE PTR [rdi+1029], dl
	mov edx, 116
	mov BYTE PTR [rdi+1030], dl
	mov edx, 104
	mov BYTE PTR [rdi+1031], dl
	mov edx, 8
	mov BYTE PTR [rdi+1032], dl
	mov edx, 0
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 10
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 74
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1136
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_shani}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, 8
	jne 22b
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
23:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 109
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 115
	mov BYTE PTR [rdi+1028], dl
	mov edx, 115
	mov BYTE PTR [rdi+1029], dl
	mov edx, 97
	mov BYTE PTR [rdi+1030], dl
	mov edx, 103
	mov BYTE PTR [rdi+1031], dl
	mov edx, 101
	mov BYTE PTR [rdi+1032], dl
	mov rdx, r9
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	mov BYTE PTR [rdi+1034], dl
	shr rdx, 8
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 11
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 75
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_shani}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, QWORD PTR [rsp+208]
	jne 23b
	mov r9, QWORD PTR [rsp+136]
	sub r9, 11
	mov r8d, 0
24:
	add r8, r8
	add r8, 1
	cmp r8, r9
	jb 24b
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 1136
	mov ecx, 0
	mov r11d, 0
25:
	movzx eax, BYTE PTR [rsi+rcx*1]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx edx, BYTE PTR [rsi+rcx*1+1]
	add rax, rdx
	and rax, r8
	mov rdx, r9
	cmp rdx, rax
	sbb rdx, rdx
	xor r11, rax
	and r11, rdx
	xor r11, rax
	add rcx, 2
	cmp rcx, 256
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	mov r9, QWORD PTR [rsp+136]
	mov ecx, 2
	mov edx, 0
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rdi+rcx*1]
	cmp rax, 1
	sbb rax, rax
	mov rsi, rdx
	xor rsi, -1
	and rsi, rax
	and rsi, rcx
	or r10, rsi
	or rdx, rax
	add rcx, 1
	cmp rcx, r9
	jne 26b
	movzx eax, BYTE PTR [rdi]
	cmp rax, 1
	sbb rax, rax
	movzx esi, BYTE PTR [rdi+1]
	xor rsi, 2
	cmp rsi, 1
	sbb rsi, rsi
	and rax, rsi
	and rax, rdx
	mov rsi, r10
	cmp rsi, 10
	sbb rsi, rsi
	xor rsi, -1
	and rax, rsi
	mov rsi, r9
	sub rsi, r10
	sub rsi, 1
	mov rdx, r11
	xor rdx, rsi
	and rdx, rax
	xor rdx, r11
	mov r10, rax
	mov r11, QWORD PTR [rsp+192]
	mov r11d, r11d
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rsi, r9
	sub rsi, rdx
	and rdx, r11
	mov r8, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov QWORD PTR [r8], rdx
	mov rdx, rsi
	mov rsi, rcx
	mov ecx, 0
27:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	and rax, r10
	xor rax, r8
	mov r8, rcx
	cmp r8, rdx
	sbb r8, r8
	xor r8, -1
	and r8, r11
	and rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, r9
	jne 27b
	mov rax, QWORD PTR [rsp+192]
	lea rsp, [rsp+216]
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
	lea rsp, [rsp-3480]
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
	lea rsp, [rsp+3480]
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

vg_rsa_pkcs1_decrypt_precomputed_sha256_shani_crt_ifma:
	lea rsp, [rsp-216]
	mov QWORD PTR [rsp+112], rdi
	mov QWORD PTR [rsp+120], rdx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], r8
	mov QWORD PTR [rsp+144], r9
	mov rax, QWORD PTR [rsp+224]
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+232]
	mov QWORD PTR [rsp+160], rax
	mov rax, QWORD PTR [rsp+240]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+176], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+184], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+296]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+104], rax
	mov rsi, r8
	mov rdx, rcx
	mov rcx, r8
	mov r8, r9
	mov r9, QWORD PTR [rsp+152]
	call {vg_rsa_private_checked_ifma}
	mov QWORD PTR [rsp+192], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+136]
	mov r10d, 0
	mov eax, 0
20:
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 20b
	mov rsi, QWORD PTR [rsp+160]
	mov rcx, QWORD PTR [rsp+168]
	mov rdi, QWORD PTR [rsp+184]
	add rdi, QWORD PTR [rsp+136]
	sub rdi, rcx
	mov r10d, 0
21:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 21b
	mov rdi, QWORD PTR [rsp+184]
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2416
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 192
	call {vg_sha256_finalize_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+136]
	add rdx, 64
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1104
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_shani}
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+136]
	add rax, 31
	shr rax, 5
	mov QWORD PTR [rsp+208], rax
22:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 108
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 110
	mov BYTE PTR [rdi+1028], dl
	mov edx, 103
	mov BYTE PTR [rdi+1029], dl
	mov edx, 116
	mov BYTE PTR [rdi+1030], dl
	mov edx, 104
	mov BYTE PTR [rdi+1031], dl
	mov edx, 8
	mov BYTE PTR [rdi+1032], dl
	mov edx, 0
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 10
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 74
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1136
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_shani}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, 8
	jne 22b
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
23:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 109
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 115
	mov BYTE PTR [rdi+1028], dl
	mov edx, 115
	mov BYTE PTR [rdi+1029], dl
	mov edx, 97
	mov BYTE PTR [rdi+1030], dl
	mov edx, 103
	mov BYTE PTR [rdi+1031], dl
	mov edx, 101
	mov BYTE PTR [rdi+1032], dl
	mov rdx, r9
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	mov BYTE PTR [rdi+1034], dl
	shr rdx, 8
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 11
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 75
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_shani}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, QWORD PTR [rsp+208]
	jne 23b
	mov r9, QWORD PTR [rsp+136]
	sub r9, 11
	mov r8d, 0
24:
	add r8, r8
	add r8, 1
	cmp r8, r9
	jb 24b
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 1136
	mov ecx, 0
	mov r11d, 0
25:
	movzx eax, BYTE PTR [rsi+rcx*1]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx edx, BYTE PTR [rsi+rcx*1+1]
	add rax, rdx
	and rax, r8
	mov rdx, r9
	cmp rdx, rax
	sbb rdx, rdx
	xor r11, rax
	and r11, rdx
	xor r11, rax
	add rcx, 2
	cmp rcx, 256
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	mov r9, QWORD PTR [rsp+136]
	mov ecx, 2
	mov edx, 0
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rdi+rcx*1]
	cmp rax, 1
	sbb rax, rax
	mov rsi, rdx
	xor rsi, -1
	and rsi, rax
	and rsi, rcx
	or r10, rsi
	or rdx, rax
	add rcx, 1
	cmp rcx, r9
	jne 26b
	movzx eax, BYTE PTR [rdi]
	cmp rax, 1
	sbb rax, rax
	movzx esi, BYTE PTR [rdi+1]
	xor rsi, 2
	cmp rsi, 1
	sbb rsi, rsi
	and rax, rsi
	and rax, rdx
	mov rsi, r10
	cmp rsi, 10
	sbb rsi, rsi
	xor rsi, -1
	and rax, rsi
	mov rsi, r9
	sub rsi, r10
	sub rsi, 1
	mov rdx, r11
	xor rdx, rsi
	and rdx, rax
	xor rdx, r11
	mov r10, rax
	mov r11, QWORD PTR [rsp+192]
	mov r11d, r11d
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rsi, r9
	sub rsi, rdx
	and rdx, r11
	mov r8, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov QWORD PTR [r8], rdx
	mov rdx, rsi
	mov rsi, rcx
	mov ecx, 0
27:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	and rax, r10
	xor rax, r8
	mov r8, rcx
	cmp r8, rdx
	sbb r8, r8
	xor r8, -1
	and r8, r11
	and rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, r9
	jne 27b
	mov rax, QWORD PTR [rsp+192]
	lea rsp, [rsp+216]
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
	lea rsp, [rsp-3480]
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
	lea rsp, [rsp+3480]
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

vg_rsa_pkcs1_decrypt_sha256_shani_crt_adx:
	lea rsp, [rsp-216]
	mov QWORD PTR [rsp+112], rdi
	mov QWORD PTR [rsp+120], rdx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], r8
	mov QWORD PTR [rsp+144], r9
	mov rax, QWORD PTR [rsp+224]
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+232]
	mov QWORD PTR [rsp+160], rax
	mov rax, QWORD PTR [rsp+240]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+176], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+184], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+296]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+104], rax
	mov rsi, r8
	mov rdx, rcx
	mov rcx, r8
	mov r8, r9
	mov r9, QWORD PTR [rsp+152]
	call {vg_rsa_private_checked_adx}
	mov QWORD PTR [rsp+192], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+136]
	mov r10d, 0
	mov eax, 0
20:
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 20b
	mov rsi, QWORD PTR [rsp+160]
	mov rcx, QWORD PTR [rsp+168]
	mov rdi, QWORD PTR [rsp+184]
	add rdi, QWORD PTR [rsp+136]
	sub rdi, rcx
	mov r10d, 0
21:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 21b
	mov rdi, QWORD PTR [rsp+184]
	call {vg_sha256_init_core}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2416
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 192
	call {vg_sha256_finalize_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+136]
	add rdx, 64
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1104
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_shani}
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+136]
	add rax, 31
	shr rax, 5
	mov QWORD PTR [rsp+208], rax
22:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 108
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 110
	mov BYTE PTR [rdi+1028], dl
	mov edx, 103
	mov BYTE PTR [rdi+1029], dl
	mov edx, 116
	mov BYTE PTR [rdi+1030], dl
	mov edx, 104
	mov BYTE PTR [rdi+1031], dl
	mov edx, 8
	mov BYTE PTR [rdi+1032], dl
	mov edx, 0
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 10
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 74
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1136
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_shani}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, 8
	jne 22b
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
23:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 109
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 115
	mov BYTE PTR [rdi+1028], dl
	mov edx, 115
	mov BYTE PTR [rdi+1029], dl
	mov edx, 97
	mov BYTE PTR [rdi+1030], dl
	mov edx, 103
	mov BYTE PTR [rdi+1031], dl
	mov edx, 101
	mov BYTE PTR [rdi+1032], dl
	mov rdx, r9
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	mov BYTE PTR [rdi+1034], dl
	shr rdx, 8
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 11
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 75
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_shani}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, QWORD PTR [rsp+208]
	jne 23b
	mov r9, QWORD PTR [rsp+136]
	sub r9, 11
	mov r8d, 0
24:
	add r8, r8
	add r8, 1
	cmp r8, r9
	jb 24b
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 1136
	mov ecx, 0
	mov r11d, 0
25:
	movzx eax, BYTE PTR [rsi+rcx*1]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx edx, BYTE PTR [rsi+rcx*1+1]
	add rax, rdx
	and rax, r8
	mov rdx, r9
	cmp rdx, rax
	sbb rdx, rdx
	xor r11, rax
	and r11, rdx
	xor r11, rax
	add rcx, 2
	cmp rcx, 256
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	mov r9, QWORD PTR [rsp+136]
	mov ecx, 2
	mov edx, 0
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rdi+rcx*1]
	cmp rax, 1
	sbb rax, rax
	mov rsi, rdx
	xor rsi, -1
	and rsi, rax
	and rsi, rcx
	or r10, rsi
	or rdx, rax
	add rcx, 1
	cmp rcx, r9
	jne 26b
	movzx eax, BYTE PTR [rdi]
	cmp rax, 1
	sbb rax, rax
	movzx esi, BYTE PTR [rdi+1]
	xor rsi, 2
	cmp rsi, 1
	sbb rsi, rsi
	and rax, rsi
	and rax, rdx
	mov rsi, r10
	cmp rsi, 10
	sbb rsi, rsi
	xor rsi, -1
	and rax, rsi
	mov rsi, r9
	sub rsi, r10
	sub rsi, 1
	mov rdx, r11
	xor rdx, rsi
	and rdx, rax
	xor rdx, r11
	mov r10, rax
	mov r11, QWORD PTR [rsp+192]
	mov r11d, r11d
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rsi, r9
	sub rsi, rdx
	and rdx, r11
	mov r8, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov QWORD PTR [r8], rdx
	mov rdx, rsi
	mov rsi, rcx
	mov ecx, 0
27:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	and rax, r10
	xor rax, r8
	mov r8, rcx
	cmp r8, rdx
	sbb r8, r8
	xor r8, -1
	and r8, r11
	and rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, r9
	jne 27b
	mov rax, QWORD PTR [rsp+192]
	lea rsp, [rsp+216]
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
	lea rsp, [rsp-3480]
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
	lea rsp, [rsp+3480]
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

vg_rsa_pkcs1_decrypt_precomputed_sha256_shani_crt_adx:
	lea rsp, [rsp-216]
	mov QWORD PTR [rsp+112], rdi
	mov QWORD PTR [rsp+120], rdx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], r8
	mov QWORD PTR [rsp+144], r9
	mov rax, QWORD PTR [rsp+224]
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+232]
	mov QWORD PTR [rsp+160], rax
	mov rax, QWORD PTR [rsp+240]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+176], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+184], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+296]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+104], rax
	mov rsi, r8
	mov rdx, rcx
	mov rcx, r8
	mov r8, r9
	mov r9, QWORD PTR [rsp+152]
	call {vg_rsa_private_checked_adx}
	mov QWORD PTR [rsp+192], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+136]
	mov r10d, 0
	mov eax, 0
20:
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 20b
	mov rsi, QWORD PTR [rsp+160]
	mov rcx, QWORD PTR [rsp+168]
	mov rdi, QWORD PTR [rsp+184]
	add rdi, QWORD PTR [rsp+136]
	sub rdi, rcx
	mov r10d, 0
21:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 21b
	mov rdi, QWORD PTR [rsp+184]
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2416
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 192
	call {vg_sha256_finalize_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+136]
	add rdx, 64
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1104
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_shani}
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+136]
	add rax, 31
	shr rax, 5
	mov QWORD PTR [rsp+208], rax
22:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 108
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 110
	mov BYTE PTR [rdi+1028], dl
	mov edx, 103
	mov BYTE PTR [rdi+1029], dl
	mov edx, 116
	mov BYTE PTR [rdi+1030], dl
	mov edx, 104
	mov BYTE PTR [rdi+1031], dl
	mov edx, 8
	mov BYTE PTR [rdi+1032], dl
	mov edx, 0
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 10
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 74
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1136
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_shani}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, 8
	jne 22b
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
23:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 109
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 115
	mov BYTE PTR [rdi+1028], dl
	mov edx, 115
	mov BYTE PTR [rdi+1029], dl
	mov edx, 97
	mov BYTE PTR [rdi+1030], dl
	mov edx, 103
	mov BYTE PTR [rdi+1031], dl
	mov edx, 101
	mov BYTE PTR [rdi+1032], dl
	mov rdx, r9
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	mov BYTE PTR [rdi+1034], dl
	shr rdx, 8
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 11
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 75
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_shani}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, QWORD PTR [rsp+208]
	jne 23b
	mov r9, QWORD PTR [rsp+136]
	sub r9, 11
	mov r8d, 0
24:
	add r8, r8
	add r8, 1
	cmp r8, r9
	jb 24b
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 1136
	mov ecx, 0
	mov r11d, 0
25:
	movzx eax, BYTE PTR [rsi+rcx*1]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx edx, BYTE PTR [rsi+rcx*1+1]
	add rax, rdx
	and rax, r8
	mov rdx, r9
	cmp rdx, rax
	sbb rdx, rdx
	xor r11, rax
	and r11, rdx
	xor r11, rax
	add rcx, 2
	cmp rcx, 256
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	mov r9, QWORD PTR [rsp+136]
	mov ecx, 2
	mov edx, 0
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rdi+rcx*1]
	cmp rax, 1
	sbb rax, rax
	mov rsi, rdx
	xor rsi, -1
	and rsi, rax
	and rsi, rcx
	or r10, rsi
	or rdx, rax
	add rcx, 1
	cmp rcx, r9
	jne 26b
	movzx eax, BYTE PTR [rdi]
	cmp rax, 1
	sbb rax, rax
	movzx esi, BYTE PTR [rdi+1]
	xor rsi, 2
	cmp rsi, 1
	sbb rsi, rsi
	and rax, rsi
	and rax, rdx
	mov rsi, r10
	cmp rsi, 10
	sbb rsi, rsi
	xor rsi, -1
	and rax, rsi
	mov rsi, r9
	sub rsi, r10
	sub rsi, 1
	mov rdx, r11
	xor rdx, rsi
	and rdx, rax
	xor rdx, r11
	mov r10, rax
	mov r11, QWORD PTR [rsp+192]
	mov r11d, r11d
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rsi, r9
	sub rsi, rdx
	and rdx, r11
	mov r8, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov QWORD PTR [r8], rdx
	mov rdx, rsi
	mov rsi, rcx
	mov ecx, 0
27:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	and rax, r10
	xor rax, r8
	mov r8, rcx
	cmp r8, rdx
	sbb r8, r8
	xor r8, -1
	and r8, r11
	and rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, r9
	jne 27b
	mov rax, QWORD PTR [rsp+192]
	lea rsp, [rsp+216]
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
	lea rsp, [rsp-3480]
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
	lea rsp, [rsp+3480]
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

vg_rsa_pkcs1_decrypt_sha256_shani:
	lea rsp, [rsp-216]
	mov QWORD PTR [rsp+112], rdi
	mov QWORD PTR [rsp+120], rdx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], r8
	mov QWORD PTR [rsp+144], r9
	mov rax, QWORD PTR [rsp+224]
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+232]
	mov QWORD PTR [rsp+160], rax
	mov rax, QWORD PTR [rsp+240]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+176], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+184], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+296]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+104], rax
	mov rsi, r8
	mov rdx, rcx
	mov rcx, r8
	mov r8, r9
	mov r9, QWORD PTR [rsp+152]
	call {vg_rsa_private_checked}
	mov QWORD PTR [rsp+192], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+136]
	mov r10d, 0
	mov eax, 0
20:
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 20b
	mov rsi, QWORD PTR [rsp+160]
	mov rcx, QWORD PTR [rsp+168]
	mov rdi, QWORD PTR [rsp+184]
	add rdi, QWORD PTR [rsp+136]
	sub rdi, rcx
	mov r10d, 0
21:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 21b
	mov rdi, QWORD PTR [rsp+184]
	call {vg_sha256_init_core}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2416
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 192
	call {vg_sha256_finalize_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+136]
	add rdx, 64
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1104
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_shani}
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+136]
	add rax, 31
	shr rax, 5
	mov QWORD PTR [rsp+208], rax
22:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 108
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 110
	mov BYTE PTR [rdi+1028], dl
	mov edx, 103
	mov BYTE PTR [rdi+1029], dl
	mov edx, 116
	mov BYTE PTR [rdi+1030], dl
	mov edx, 104
	mov BYTE PTR [rdi+1031], dl
	mov edx, 8
	mov BYTE PTR [rdi+1032], dl
	mov edx, 0
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 10
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 74
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1136
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_shani}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, 8
	jne 22b
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
23:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 109
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 115
	mov BYTE PTR [rdi+1028], dl
	mov edx, 115
	mov BYTE PTR [rdi+1029], dl
	mov edx, 97
	mov BYTE PTR [rdi+1030], dl
	mov edx, 103
	mov BYTE PTR [rdi+1031], dl
	mov edx, 101
	mov BYTE PTR [rdi+1032], dl
	mov rdx, r9
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	mov BYTE PTR [rdi+1034], dl
	shr rdx, 8
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 11
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 75
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_shani}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, QWORD PTR [rsp+208]
	jne 23b
	mov r9, QWORD PTR [rsp+136]
	sub r9, 11
	mov r8d, 0
24:
	add r8, r8
	add r8, 1
	cmp r8, r9
	jb 24b
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 1136
	mov ecx, 0
	mov r11d, 0
25:
	movzx eax, BYTE PTR [rsi+rcx*1]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx edx, BYTE PTR [rsi+rcx*1+1]
	add rax, rdx
	and rax, r8
	mov rdx, r9
	cmp rdx, rax
	sbb rdx, rdx
	xor r11, rax
	and r11, rdx
	xor r11, rax
	add rcx, 2
	cmp rcx, 256
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	mov r9, QWORD PTR [rsp+136]
	mov ecx, 2
	mov edx, 0
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rdi+rcx*1]
	cmp rax, 1
	sbb rax, rax
	mov rsi, rdx
	xor rsi, -1
	and rsi, rax
	and rsi, rcx
	or r10, rsi
	or rdx, rax
	add rcx, 1
	cmp rcx, r9
	jne 26b
	movzx eax, BYTE PTR [rdi]
	cmp rax, 1
	sbb rax, rax
	movzx esi, BYTE PTR [rdi+1]
	xor rsi, 2
	cmp rsi, 1
	sbb rsi, rsi
	and rax, rsi
	and rax, rdx
	mov rsi, r10
	cmp rsi, 10
	sbb rsi, rsi
	xor rsi, -1
	and rax, rsi
	mov rsi, r9
	sub rsi, r10
	sub rsi, 1
	mov rdx, r11
	xor rdx, rsi
	and rdx, rax
	xor rdx, r11
	mov r10, rax
	mov r11, QWORD PTR [rsp+192]
	mov r11d, r11d
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rsi, r9
	sub rsi, rdx
	and rdx, r11
	mov r8, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov QWORD PTR [r8], rdx
	mov rdx, rsi
	mov rsi, rcx
	mov ecx, 0
27:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	and rax, r10
	xor rax, r8
	mov r8, rcx
	cmp r8, rdx
	sbb r8, r8
	xor r8, -1
	and r8, r11
	and rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, r9
	jne 27b
	mov rax, QWORD PTR [rsp+192]
	lea rsp, [rsp+216]
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
	lea rsp, [rsp-3480]
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
	lea rsp, [rsp+3480]
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

vg_rsa_pkcs1_decrypt_precomputed_sha256_shani:
	lea rsp, [rsp-216]
	mov QWORD PTR [rsp+112], rdi
	mov QWORD PTR [rsp+120], rdx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], r8
	mov QWORD PTR [rsp+144], r9
	mov rax, QWORD PTR [rsp+224]
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+232]
	mov QWORD PTR [rsp+160], rax
	mov rax, QWORD PTR [rsp+240]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+176], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+184], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+296]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+104], rax
	mov rsi, r8
	mov rdx, rcx
	mov rcx, r8
	mov r8, r9
	mov r9, QWORD PTR [rsp+152]
	call {vg_rsa_private_checked}
	mov QWORD PTR [rsp+192], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+136]
	mov r10d, 0
	mov eax, 0
20:
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 20b
	mov rsi, QWORD PTR [rsp+160]
	mov rcx, QWORD PTR [rsp+168]
	mov rdi, QWORD PTR [rsp+184]
	add rdi, QWORD PTR [rsp+136]
	sub rdi, rcx
	mov r10d, 0
21:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 21b
	mov rdi, QWORD PTR [rsp+184]
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2416
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 192
	call {vg_sha256_finalize_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+136]
	add rdx, 64
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1104
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_shani}
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+136]
	add rax, 31
	shr rax, 5
	mov QWORD PTR [rsp+208], rax
22:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 108
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 110
	mov BYTE PTR [rdi+1028], dl
	mov edx, 103
	mov BYTE PTR [rdi+1029], dl
	mov edx, 116
	mov BYTE PTR [rdi+1030], dl
	mov edx, 104
	mov BYTE PTR [rdi+1031], dl
	mov edx, 8
	mov BYTE PTR [rdi+1032], dl
	mov edx, 0
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 10
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 74
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1136
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_shani}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, 8
	jne 22b
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
23:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 109
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 115
	mov BYTE PTR [rdi+1028], dl
	mov edx, 115
	mov BYTE PTR [rdi+1029], dl
	mov edx, 97
	mov BYTE PTR [rdi+1030], dl
	mov edx, 103
	mov BYTE PTR [rdi+1031], dl
	mov edx, 101
	mov BYTE PTR [rdi+1032], dl
	mov rdx, r9
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	mov BYTE PTR [rdi+1034], dl
	shr rdx, 8
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 11
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_shani}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 75
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_shani}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, QWORD PTR [rsp+208]
	jne 23b
	mov r9, QWORD PTR [rsp+136]
	sub r9, 11
	mov r8d, 0
24:
	add r8, r8
	add r8, 1
	cmp r8, r9
	jb 24b
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 1136
	mov ecx, 0
	mov r11d, 0
25:
	movzx eax, BYTE PTR [rsi+rcx*1]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx edx, BYTE PTR [rsi+rcx*1+1]
	add rax, rdx
	and rax, r8
	mov rdx, r9
	cmp rdx, rax
	sbb rdx, rdx
	xor r11, rax
	and r11, rdx
	xor r11, rax
	add rcx, 2
	cmp rcx, 256
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	mov r9, QWORD PTR [rsp+136]
	mov ecx, 2
	mov edx, 0
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rdi+rcx*1]
	cmp rax, 1
	sbb rax, rax
	mov rsi, rdx
	xor rsi, -1
	and rsi, rax
	and rsi, rcx
	or r10, rsi
	or rdx, rax
	add rcx, 1
	cmp rcx, r9
	jne 26b
	movzx eax, BYTE PTR [rdi]
	cmp rax, 1
	sbb rax, rax
	movzx esi, BYTE PTR [rdi+1]
	xor rsi, 2
	cmp rsi, 1
	sbb rsi, rsi
	and rax, rsi
	and rax, rdx
	mov rsi, r10
	cmp rsi, 10
	sbb rsi, rsi
	xor rsi, -1
	and rax, rsi
	mov rsi, r9
	sub rsi, r10
	sub rsi, 1
	mov rdx, r11
	xor rdx, rsi
	and rdx, rax
	xor rdx, r11
	mov r10, rax
	mov r11, QWORD PTR [rsp+192]
	mov r11d, r11d
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rsi, r9
	sub rsi, rdx
	and rdx, r11
	mov r8, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov QWORD PTR [r8], rdx
	mov rdx, rsi
	mov rsi, rcx
	mov ecx, 0
27:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	and rax, r10
	xor rax, r8
	mov r8, rcx
	cmp r8, rdx
	sbb r8, r8
	xor r8, -1
	and r8, r11
	and rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, r9
	jne 27b
	mov rax, QWORD PTR [rsp+192]
	lea rsp, [rsp+216]
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
	lea rsp, [rsp-3480]
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
	lea rsp, [rsp+3480]
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

vg_rsa_pkcs1_decrypt_sha256_avx2_crt_ifma512:
	lea rsp, [rsp-216]
	mov QWORD PTR [rsp+112], rdi
	mov QWORD PTR [rsp+120], rdx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], r8
	mov QWORD PTR [rsp+144], r9
	mov rax, QWORD PTR [rsp+224]
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+232]
	mov QWORD PTR [rsp+160], rax
	mov rax, QWORD PTR [rsp+240]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+176], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+184], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+296]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+104], rax
	mov rsi, r8
	mov rdx, rcx
	mov rcx, r8
	mov r8, r9
	mov r9, QWORD PTR [rsp+152]
	call {vg_rsa_private_checked_ifma512}
	mov QWORD PTR [rsp+192], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+136]
	mov r10d, 0
	mov eax, 0
20:
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 20b
	mov rsi, QWORD PTR [rsp+160]
	mov rcx, QWORD PTR [rsp+168]
	mov rdi, QWORD PTR [rsp+184]
	add rdi, QWORD PTR [rsp+136]
	sub rdi, rcx
	mov r10d, 0
21:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 21b
	mov rdi, QWORD PTR [rsp+184]
	call {vg_sha256_init_core}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2416
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 192
	call {vg_sha256_finalize_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+136]
	add rdx, 64
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1104
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_avx2}
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+136]
	add rax, 31
	shr rax, 5
	mov QWORD PTR [rsp+208], rax
22:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 108
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 110
	mov BYTE PTR [rdi+1028], dl
	mov edx, 103
	mov BYTE PTR [rdi+1029], dl
	mov edx, 116
	mov BYTE PTR [rdi+1030], dl
	mov edx, 104
	mov BYTE PTR [rdi+1031], dl
	mov edx, 8
	mov BYTE PTR [rdi+1032], dl
	mov edx, 0
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 10
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 74
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1136
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_avx2}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, 8
	jne 22b
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
23:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 109
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 115
	mov BYTE PTR [rdi+1028], dl
	mov edx, 115
	mov BYTE PTR [rdi+1029], dl
	mov edx, 97
	mov BYTE PTR [rdi+1030], dl
	mov edx, 103
	mov BYTE PTR [rdi+1031], dl
	mov edx, 101
	mov BYTE PTR [rdi+1032], dl
	mov rdx, r9
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	mov BYTE PTR [rdi+1034], dl
	shr rdx, 8
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 11
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 75
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_avx2}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, QWORD PTR [rsp+208]
	jne 23b
	mov r9, QWORD PTR [rsp+136]
	sub r9, 11
	mov r8d, 0
24:
	add r8, r8
	add r8, 1
	cmp r8, r9
	jb 24b
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 1136
	mov ecx, 0
	mov r11d, 0
25:
	movzx eax, BYTE PTR [rsi+rcx*1]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx edx, BYTE PTR [rsi+rcx*1+1]
	add rax, rdx
	and rax, r8
	mov rdx, r9
	cmp rdx, rax
	sbb rdx, rdx
	xor r11, rax
	and r11, rdx
	xor r11, rax
	add rcx, 2
	cmp rcx, 256
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	mov r9, QWORD PTR [rsp+136]
	mov ecx, 2
	mov edx, 0
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rdi+rcx*1]
	cmp rax, 1
	sbb rax, rax
	mov rsi, rdx
	xor rsi, -1
	and rsi, rax
	and rsi, rcx
	or r10, rsi
	or rdx, rax
	add rcx, 1
	cmp rcx, r9
	jne 26b
	movzx eax, BYTE PTR [rdi]
	cmp rax, 1
	sbb rax, rax
	movzx esi, BYTE PTR [rdi+1]
	xor rsi, 2
	cmp rsi, 1
	sbb rsi, rsi
	and rax, rsi
	and rax, rdx
	mov rsi, r10
	cmp rsi, 10
	sbb rsi, rsi
	xor rsi, -1
	and rax, rsi
	mov rsi, r9
	sub rsi, r10
	sub rsi, 1
	mov rdx, r11
	xor rdx, rsi
	and rdx, rax
	xor rdx, r11
	mov r10, rax
	mov r11, QWORD PTR [rsp+192]
	mov r11d, r11d
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rsi, r9
	sub rsi, rdx
	and rdx, r11
	mov r8, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov QWORD PTR [r8], rdx
	mov rdx, rsi
	mov rsi, rcx
	mov ecx, 0
27:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	and rax, r10
	xor rax, r8
	mov r8, rcx
	cmp r8, rdx
	sbb r8, r8
	xor r8, -1
	and r8, r11
	and rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, r9
	jne 27b
	mov rax, QWORD PTR [rsp+192]
	lea rsp, [rsp+216]
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
	lea rsp, [rsp-3480]
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
	lea rsp, [rsp+3480]
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

vg_rsa_pkcs1_decrypt_precomputed_sha256_avx2_crt_ifma512:
	lea rsp, [rsp-216]
	mov QWORD PTR [rsp+112], rdi
	mov QWORD PTR [rsp+120], rdx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], r8
	mov QWORD PTR [rsp+144], r9
	mov rax, QWORD PTR [rsp+224]
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+232]
	mov QWORD PTR [rsp+160], rax
	mov rax, QWORD PTR [rsp+240]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+176], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+184], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+296]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+104], rax
	mov rsi, r8
	mov rdx, rcx
	mov rcx, r8
	mov r8, r9
	mov r9, QWORD PTR [rsp+152]
	call {vg_rsa_private_checked_ifma512}
	mov QWORD PTR [rsp+192], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+136]
	mov r10d, 0
	mov eax, 0
20:
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 20b
	mov rsi, QWORD PTR [rsp+160]
	mov rcx, QWORD PTR [rsp+168]
	mov rdi, QWORD PTR [rsp+184]
	add rdi, QWORD PTR [rsp+136]
	sub rdi, rcx
	mov r10d, 0
21:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 21b
	mov rdi, QWORD PTR [rsp+184]
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2416
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 192
	call {vg_sha256_finalize_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+136]
	add rdx, 64
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1104
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_avx2}
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+136]
	add rax, 31
	shr rax, 5
	mov QWORD PTR [rsp+208], rax
22:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 108
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 110
	mov BYTE PTR [rdi+1028], dl
	mov edx, 103
	mov BYTE PTR [rdi+1029], dl
	mov edx, 116
	mov BYTE PTR [rdi+1030], dl
	mov edx, 104
	mov BYTE PTR [rdi+1031], dl
	mov edx, 8
	mov BYTE PTR [rdi+1032], dl
	mov edx, 0
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 10
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 74
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1136
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_avx2}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, 8
	jne 22b
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
23:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 109
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 115
	mov BYTE PTR [rdi+1028], dl
	mov edx, 115
	mov BYTE PTR [rdi+1029], dl
	mov edx, 97
	mov BYTE PTR [rdi+1030], dl
	mov edx, 103
	mov BYTE PTR [rdi+1031], dl
	mov edx, 101
	mov BYTE PTR [rdi+1032], dl
	mov rdx, r9
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	mov BYTE PTR [rdi+1034], dl
	shr rdx, 8
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 11
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 75
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_avx2}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, QWORD PTR [rsp+208]
	jne 23b
	mov r9, QWORD PTR [rsp+136]
	sub r9, 11
	mov r8d, 0
24:
	add r8, r8
	add r8, 1
	cmp r8, r9
	jb 24b
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 1136
	mov ecx, 0
	mov r11d, 0
25:
	movzx eax, BYTE PTR [rsi+rcx*1]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx edx, BYTE PTR [rsi+rcx*1+1]
	add rax, rdx
	and rax, r8
	mov rdx, r9
	cmp rdx, rax
	sbb rdx, rdx
	xor r11, rax
	and r11, rdx
	xor r11, rax
	add rcx, 2
	cmp rcx, 256
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	mov r9, QWORD PTR [rsp+136]
	mov ecx, 2
	mov edx, 0
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rdi+rcx*1]
	cmp rax, 1
	sbb rax, rax
	mov rsi, rdx
	xor rsi, -1
	and rsi, rax
	and rsi, rcx
	or r10, rsi
	or rdx, rax
	add rcx, 1
	cmp rcx, r9
	jne 26b
	movzx eax, BYTE PTR [rdi]
	cmp rax, 1
	sbb rax, rax
	movzx esi, BYTE PTR [rdi+1]
	xor rsi, 2
	cmp rsi, 1
	sbb rsi, rsi
	and rax, rsi
	and rax, rdx
	mov rsi, r10
	cmp rsi, 10
	sbb rsi, rsi
	xor rsi, -1
	and rax, rsi
	mov rsi, r9
	sub rsi, r10
	sub rsi, 1
	mov rdx, r11
	xor rdx, rsi
	and rdx, rax
	xor rdx, r11
	mov r10, rax
	mov r11, QWORD PTR [rsp+192]
	mov r11d, r11d
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rsi, r9
	sub rsi, rdx
	and rdx, r11
	mov r8, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov QWORD PTR [r8], rdx
	mov rdx, rsi
	mov rsi, rcx
	mov ecx, 0
27:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	and rax, r10
	xor rax, r8
	mov r8, rcx
	cmp r8, rdx
	sbb r8, r8
	xor r8, -1
	and r8, r11
	and rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, r9
	jne 27b
	mov rax, QWORD PTR [rsp+192]
	lea rsp, [rsp+216]
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
	lea rsp, [rsp-3480]
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
	lea rsp, [rsp+3480]
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

vg_rsa_pkcs1_decrypt_sha256_avx2_crt_ifma:
	lea rsp, [rsp-216]
	mov QWORD PTR [rsp+112], rdi
	mov QWORD PTR [rsp+120], rdx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], r8
	mov QWORD PTR [rsp+144], r9
	mov rax, QWORD PTR [rsp+224]
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+232]
	mov QWORD PTR [rsp+160], rax
	mov rax, QWORD PTR [rsp+240]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+176], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+184], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+296]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+104], rax
	mov rsi, r8
	mov rdx, rcx
	mov rcx, r8
	mov r8, r9
	mov r9, QWORD PTR [rsp+152]
	call {vg_rsa_private_checked_ifma}
	mov QWORD PTR [rsp+192], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+136]
	mov r10d, 0
	mov eax, 0
20:
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 20b
	mov rsi, QWORD PTR [rsp+160]
	mov rcx, QWORD PTR [rsp+168]
	mov rdi, QWORD PTR [rsp+184]
	add rdi, QWORD PTR [rsp+136]
	sub rdi, rcx
	mov r10d, 0
21:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 21b
	mov rdi, QWORD PTR [rsp+184]
	call {vg_sha256_init_core}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2416
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 192
	call {vg_sha256_finalize_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+136]
	add rdx, 64
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1104
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_avx2}
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+136]
	add rax, 31
	shr rax, 5
	mov QWORD PTR [rsp+208], rax
22:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 108
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 110
	mov BYTE PTR [rdi+1028], dl
	mov edx, 103
	mov BYTE PTR [rdi+1029], dl
	mov edx, 116
	mov BYTE PTR [rdi+1030], dl
	mov edx, 104
	mov BYTE PTR [rdi+1031], dl
	mov edx, 8
	mov BYTE PTR [rdi+1032], dl
	mov edx, 0
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 10
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 74
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1136
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_avx2}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, 8
	jne 22b
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
23:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 109
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 115
	mov BYTE PTR [rdi+1028], dl
	mov edx, 115
	mov BYTE PTR [rdi+1029], dl
	mov edx, 97
	mov BYTE PTR [rdi+1030], dl
	mov edx, 103
	mov BYTE PTR [rdi+1031], dl
	mov edx, 101
	mov BYTE PTR [rdi+1032], dl
	mov rdx, r9
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	mov BYTE PTR [rdi+1034], dl
	shr rdx, 8
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 11
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 75
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_avx2}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, QWORD PTR [rsp+208]
	jne 23b
	mov r9, QWORD PTR [rsp+136]
	sub r9, 11
	mov r8d, 0
24:
	add r8, r8
	add r8, 1
	cmp r8, r9
	jb 24b
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 1136
	mov ecx, 0
	mov r11d, 0
25:
	movzx eax, BYTE PTR [rsi+rcx*1]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx edx, BYTE PTR [rsi+rcx*1+1]
	add rax, rdx
	and rax, r8
	mov rdx, r9
	cmp rdx, rax
	sbb rdx, rdx
	xor r11, rax
	and r11, rdx
	xor r11, rax
	add rcx, 2
	cmp rcx, 256
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	mov r9, QWORD PTR [rsp+136]
	mov ecx, 2
	mov edx, 0
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rdi+rcx*1]
	cmp rax, 1
	sbb rax, rax
	mov rsi, rdx
	xor rsi, -1
	and rsi, rax
	and rsi, rcx
	or r10, rsi
	or rdx, rax
	add rcx, 1
	cmp rcx, r9
	jne 26b
	movzx eax, BYTE PTR [rdi]
	cmp rax, 1
	sbb rax, rax
	movzx esi, BYTE PTR [rdi+1]
	xor rsi, 2
	cmp rsi, 1
	sbb rsi, rsi
	and rax, rsi
	and rax, rdx
	mov rsi, r10
	cmp rsi, 10
	sbb rsi, rsi
	xor rsi, -1
	and rax, rsi
	mov rsi, r9
	sub rsi, r10
	sub rsi, 1
	mov rdx, r11
	xor rdx, rsi
	and rdx, rax
	xor rdx, r11
	mov r10, rax
	mov r11, QWORD PTR [rsp+192]
	mov r11d, r11d
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rsi, r9
	sub rsi, rdx
	and rdx, r11
	mov r8, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov QWORD PTR [r8], rdx
	mov rdx, rsi
	mov rsi, rcx
	mov ecx, 0
27:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	and rax, r10
	xor rax, r8
	mov r8, rcx
	cmp r8, rdx
	sbb r8, r8
	xor r8, -1
	and r8, r11
	and rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, r9
	jne 27b
	mov rax, QWORD PTR [rsp+192]
	lea rsp, [rsp+216]
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
	lea rsp, [rsp-3480]
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
	lea rsp, [rsp+3480]
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

vg_rsa_pkcs1_decrypt_precomputed_sha256_avx2_crt_ifma:
	lea rsp, [rsp-216]
	mov QWORD PTR [rsp+112], rdi
	mov QWORD PTR [rsp+120], rdx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], r8
	mov QWORD PTR [rsp+144], r9
	mov rax, QWORD PTR [rsp+224]
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+232]
	mov QWORD PTR [rsp+160], rax
	mov rax, QWORD PTR [rsp+240]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+176], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+184], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+296]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+104], rax
	mov rsi, r8
	mov rdx, rcx
	mov rcx, r8
	mov r8, r9
	mov r9, QWORD PTR [rsp+152]
	call {vg_rsa_private_checked_ifma}
	mov QWORD PTR [rsp+192], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+136]
	mov r10d, 0
	mov eax, 0
20:
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 20b
	mov rsi, QWORD PTR [rsp+160]
	mov rcx, QWORD PTR [rsp+168]
	mov rdi, QWORD PTR [rsp+184]
	add rdi, QWORD PTR [rsp+136]
	sub rdi, rcx
	mov r10d, 0
21:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 21b
	mov rdi, QWORD PTR [rsp+184]
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2416
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 192
	call {vg_sha256_finalize_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+136]
	add rdx, 64
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1104
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_avx2}
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+136]
	add rax, 31
	shr rax, 5
	mov QWORD PTR [rsp+208], rax
22:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 108
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 110
	mov BYTE PTR [rdi+1028], dl
	mov edx, 103
	mov BYTE PTR [rdi+1029], dl
	mov edx, 116
	mov BYTE PTR [rdi+1030], dl
	mov edx, 104
	mov BYTE PTR [rdi+1031], dl
	mov edx, 8
	mov BYTE PTR [rdi+1032], dl
	mov edx, 0
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 10
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 74
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1136
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_avx2}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, 8
	jne 22b
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
23:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 109
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 115
	mov BYTE PTR [rdi+1028], dl
	mov edx, 115
	mov BYTE PTR [rdi+1029], dl
	mov edx, 97
	mov BYTE PTR [rdi+1030], dl
	mov edx, 103
	mov BYTE PTR [rdi+1031], dl
	mov edx, 101
	mov BYTE PTR [rdi+1032], dl
	mov rdx, r9
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	mov BYTE PTR [rdi+1034], dl
	shr rdx, 8
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 11
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 75
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_avx2}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, QWORD PTR [rsp+208]
	jne 23b
	mov r9, QWORD PTR [rsp+136]
	sub r9, 11
	mov r8d, 0
24:
	add r8, r8
	add r8, 1
	cmp r8, r9
	jb 24b
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 1136
	mov ecx, 0
	mov r11d, 0
25:
	movzx eax, BYTE PTR [rsi+rcx*1]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx edx, BYTE PTR [rsi+rcx*1+1]
	add rax, rdx
	and rax, r8
	mov rdx, r9
	cmp rdx, rax
	sbb rdx, rdx
	xor r11, rax
	and r11, rdx
	xor r11, rax
	add rcx, 2
	cmp rcx, 256
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	mov r9, QWORD PTR [rsp+136]
	mov ecx, 2
	mov edx, 0
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rdi+rcx*1]
	cmp rax, 1
	sbb rax, rax
	mov rsi, rdx
	xor rsi, -1
	and rsi, rax
	and rsi, rcx
	or r10, rsi
	or rdx, rax
	add rcx, 1
	cmp rcx, r9
	jne 26b
	movzx eax, BYTE PTR [rdi]
	cmp rax, 1
	sbb rax, rax
	movzx esi, BYTE PTR [rdi+1]
	xor rsi, 2
	cmp rsi, 1
	sbb rsi, rsi
	and rax, rsi
	and rax, rdx
	mov rsi, r10
	cmp rsi, 10
	sbb rsi, rsi
	xor rsi, -1
	and rax, rsi
	mov rsi, r9
	sub rsi, r10
	sub rsi, 1
	mov rdx, r11
	xor rdx, rsi
	and rdx, rax
	xor rdx, r11
	mov r10, rax
	mov r11, QWORD PTR [rsp+192]
	mov r11d, r11d
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rsi, r9
	sub rsi, rdx
	and rdx, r11
	mov r8, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov QWORD PTR [r8], rdx
	mov rdx, rsi
	mov rsi, rcx
	mov ecx, 0
27:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	and rax, r10
	xor rax, r8
	mov r8, rcx
	cmp r8, rdx
	sbb r8, r8
	xor r8, -1
	and r8, r11
	and rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, r9
	jne 27b
	mov rax, QWORD PTR [rsp+192]
	lea rsp, [rsp+216]
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
	lea rsp, [rsp-3480]
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
	lea rsp, [rsp+3480]
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

vg_rsa_pkcs1_decrypt_sha256_avx2_crt_adx:
	lea rsp, [rsp-216]
	mov QWORD PTR [rsp+112], rdi
	mov QWORD PTR [rsp+120], rdx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], r8
	mov QWORD PTR [rsp+144], r9
	mov rax, QWORD PTR [rsp+224]
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+232]
	mov QWORD PTR [rsp+160], rax
	mov rax, QWORD PTR [rsp+240]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+176], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+184], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+296]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+104], rax
	mov rsi, r8
	mov rdx, rcx
	mov rcx, r8
	mov r8, r9
	mov r9, QWORD PTR [rsp+152]
	call {vg_rsa_private_checked_adx}
	mov QWORD PTR [rsp+192], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+136]
	mov r10d, 0
	mov eax, 0
20:
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 20b
	mov rsi, QWORD PTR [rsp+160]
	mov rcx, QWORD PTR [rsp+168]
	mov rdi, QWORD PTR [rsp+184]
	add rdi, QWORD PTR [rsp+136]
	sub rdi, rcx
	mov r10d, 0
21:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 21b
	mov rdi, QWORD PTR [rsp+184]
	call {vg_sha256_init_core}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2416
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 192
	call {vg_sha256_finalize_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+136]
	add rdx, 64
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1104
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_avx2}
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+136]
	add rax, 31
	shr rax, 5
	mov QWORD PTR [rsp+208], rax
22:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 108
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 110
	mov BYTE PTR [rdi+1028], dl
	mov edx, 103
	mov BYTE PTR [rdi+1029], dl
	mov edx, 116
	mov BYTE PTR [rdi+1030], dl
	mov edx, 104
	mov BYTE PTR [rdi+1031], dl
	mov edx, 8
	mov BYTE PTR [rdi+1032], dl
	mov edx, 0
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 10
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 74
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1136
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_avx2}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, 8
	jne 22b
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
23:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 109
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 115
	mov BYTE PTR [rdi+1028], dl
	mov edx, 115
	mov BYTE PTR [rdi+1029], dl
	mov edx, 97
	mov BYTE PTR [rdi+1030], dl
	mov edx, 103
	mov BYTE PTR [rdi+1031], dl
	mov edx, 101
	mov BYTE PTR [rdi+1032], dl
	mov rdx, r9
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	mov BYTE PTR [rdi+1034], dl
	shr rdx, 8
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 11
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 75
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_avx2}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, QWORD PTR [rsp+208]
	jne 23b
	mov r9, QWORD PTR [rsp+136]
	sub r9, 11
	mov r8d, 0
24:
	add r8, r8
	add r8, 1
	cmp r8, r9
	jb 24b
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 1136
	mov ecx, 0
	mov r11d, 0
25:
	movzx eax, BYTE PTR [rsi+rcx*1]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx edx, BYTE PTR [rsi+rcx*1+1]
	add rax, rdx
	and rax, r8
	mov rdx, r9
	cmp rdx, rax
	sbb rdx, rdx
	xor r11, rax
	and r11, rdx
	xor r11, rax
	add rcx, 2
	cmp rcx, 256
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	mov r9, QWORD PTR [rsp+136]
	mov ecx, 2
	mov edx, 0
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rdi+rcx*1]
	cmp rax, 1
	sbb rax, rax
	mov rsi, rdx
	xor rsi, -1
	and rsi, rax
	and rsi, rcx
	or r10, rsi
	or rdx, rax
	add rcx, 1
	cmp rcx, r9
	jne 26b
	movzx eax, BYTE PTR [rdi]
	cmp rax, 1
	sbb rax, rax
	movzx esi, BYTE PTR [rdi+1]
	xor rsi, 2
	cmp rsi, 1
	sbb rsi, rsi
	and rax, rsi
	and rax, rdx
	mov rsi, r10
	cmp rsi, 10
	sbb rsi, rsi
	xor rsi, -1
	and rax, rsi
	mov rsi, r9
	sub rsi, r10
	sub rsi, 1
	mov rdx, r11
	xor rdx, rsi
	and rdx, rax
	xor rdx, r11
	mov r10, rax
	mov r11, QWORD PTR [rsp+192]
	mov r11d, r11d
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rsi, r9
	sub rsi, rdx
	and rdx, r11
	mov r8, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov QWORD PTR [r8], rdx
	mov rdx, rsi
	mov rsi, rcx
	mov ecx, 0
27:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	and rax, r10
	xor rax, r8
	mov r8, rcx
	cmp r8, rdx
	sbb r8, r8
	xor r8, -1
	and r8, r11
	and rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, r9
	jne 27b
	mov rax, QWORD PTR [rsp+192]
	lea rsp, [rsp+216]
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
	lea rsp, [rsp-3480]
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
	lea rsp, [rsp+3480]
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

vg_rsa_pkcs1_decrypt_precomputed_sha256_avx2_crt_adx:
	lea rsp, [rsp-216]
	mov QWORD PTR [rsp+112], rdi
	mov QWORD PTR [rsp+120], rdx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], r8
	mov QWORD PTR [rsp+144], r9
	mov rax, QWORD PTR [rsp+224]
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+232]
	mov QWORD PTR [rsp+160], rax
	mov rax, QWORD PTR [rsp+240]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+176], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+184], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+296]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+104], rax
	mov rsi, r8
	mov rdx, rcx
	mov rcx, r8
	mov r8, r9
	mov r9, QWORD PTR [rsp+152]
	call {vg_rsa_private_checked_adx}
	mov QWORD PTR [rsp+192], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+136]
	mov r10d, 0
	mov eax, 0
20:
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 20b
	mov rsi, QWORD PTR [rsp+160]
	mov rcx, QWORD PTR [rsp+168]
	mov rdi, QWORD PTR [rsp+184]
	add rdi, QWORD PTR [rsp+136]
	sub rdi, rcx
	mov r10d, 0
21:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 21b
	mov rdi, QWORD PTR [rsp+184]
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2416
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 192
	call {vg_sha256_finalize_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+136]
	add rdx, 64
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1104
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_avx2}
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+136]
	add rax, 31
	shr rax, 5
	mov QWORD PTR [rsp+208], rax
22:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 108
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 110
	mov BYTE PTR [rdi+1028], dl
	mov edx, 103
	mov BYTE PTR [rdi+1029], dl
	mov edx, 116
	mov BYTE PTR [rdi+1030], dl
	mov edx, 104
	mov BYTE PTR [rdi+1031], dl
	mov edx, 8
	mov BYTE PTR [rdi+1032], dl
	mov edx, 0
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 10
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 74
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1136
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_avx2}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, 8
	jne 22b
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
23:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 109
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 115
	mov BYTE PTR [rdi+1028], dl
	mov edx, 115
	mov BYTE PTR [rdi+1029], dl
	mov edx, 97
	mov BYTE PTR [rdi+1030], dl
	mov edx, 103
	mov BYTE PTR [rdi+1031], dl
	mov edx, 101
	mov BYTE PTR [rdi+1032], dl
	mov rdx, r9
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	mov BYTE PTR [rdi+1034], dl
	shr rdx, 8
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 11
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 75
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_avx2}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, QWORD PTR [rsp+208]
	jne 23b
	mov r9, QWORD PTR [rsp+136]
	sub r9, 11
	mov r8d, 0
24:
	add r8, r8
	add r8, 1
	cmp r8, r9
	jb 24b
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 1136
	mov ecx, 0
	mov r11d, 0
25:
	movzx eax, BYTE PTR [rsi+rcx*1]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx edx, BYTE PTR [rsi+rcx*1+1]
	add rax, rdx
	and rax, r8
	mov rdx, r9
	cmp rdx, rax
	sbb rdx, rdx
	xor r11, rax
	and r11, rdx
	xor r11, rax
	add rcx, 2
	cmp rcx, 256
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	mov r9, QWORD PTR [rsp+136]
	mov ecx, 2
	mov edx, 0
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rdi+rcx*1]
	cmp rax, 1
	sbb rax, rax
	mov rsi, rdx
	xor rsi, -1
	and rsi, rax
	and rsi, rcx
	or r10, rsi
	or rdx, rax
	add rcx, 1
	cmp rcx, r9
	jne 26b
	movzx eax, BYTE PTR [rdi]
	cmp rax, 1
	sbb rax, rax
	movzx esi, BYTE PTR [rdi+1]
	xor rsi, 2
	cmp rsi, 1
	sbb rsi, rsi
	and rax, rsi
	and rax, rdx
	mov rsi, r10
	cmp rsi, 10
	sbb rsi, rsi
	xor rsi, -1
	and rax, rsi
	mov rsi, r9
	sub rsi, r10
	sub rsi, 1
	mov rdx, r11
	xor rdx, rsi
	and rdx, rax
	xor rdx, r11
	mov r10, rax
	mov r11, QWORD PTR [rsp+192]
	mov r11d, r11d
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rsi, r9
	sub rsi, rdx
	and rdx, r11
	mov r8, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov QWORD PTR [r8], rdx
	mov rdx, rsi
	mov rsi, rcx
	mov ecx, 0
27:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	and rax, r10
	xor rax, r8
	mov r8, rcx
	cmp r8, rdx
	sbb r8, r8
	xor r8, -1
	and r8, r11
	and rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, r9
	jne 27b
	mov rax, QWORD PTR [rsp+192]
	lea rsp, [rsp+216]
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
	lea rsp, [rsp-3480]
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
	lea rsp, [rsp+3480]
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

vg_rsa_pkcs1_decrypt_sha256_avx2:
	lea rsp, [rsp-216]
	mov QWORD PTR [rsp+112], rdi
	mov QWORD PTR [rsp+120], rdx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], r8
	mov QWORD PTR [rsp+144], r9
	mov rax, QWORD PTR [rsp+224]
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+232]
	mov QWORD PTR [rsp+160], rax
	mov rax, QWORD PTR [rsp+240]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+176], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+184], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+296]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+104], rax
	mov rsi, r8
	mov rdx, rcx
	mov rcx, r8
	mov r8, r9
	mov r9, QWORD PTR [rsp+152]
	call {vg_rsa_private_checked}
	mov QWORD PTR [rsp+192], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+136]
	mov r10d, 0
	mov eax, 0
20:
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 20b
	mov rsi, QWORD PTR [rsp+160]
	mov rcx, QWORD PTR [rsp+168]
	mov rdi, QWORD PTR [rsp+184]
	add rdi, QWORD PTR [rsp+136]
	sub rdi, rcx
	mov r10d, 0
21:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 21b
	mov rdi, QWORD PTR [rsp+184]
	call {vg_sha256_init_core}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2416
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 192
	call {vg_sha256_finalize_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+136]
	add rdx, 64
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1104
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_avx2}
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+136]
	add rax, 31
	shr rax, 5
	mov QWORD PTR [rsp+208], rax
22:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 108
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 110
	mov BYTE PTR [rdi+1028], dl
	mov edx, 103
	mov BYTE PTR [rdi+1029], dl
	mov edx, 116
	mov BYTE PTR [rdi+1030], dl
	mov edx, 104
	mov BYTE PTR [rdi+1031], dl
	mov edx, 8
	mov BYTE PTR [rdi+1032], dl
	mov edx, 0
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 10
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 74
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1136
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_avx2}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, 8
	jne 22b
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
23:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 109
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 115
	mov BYTE PTR [rdi+1028], dl
	mov edx, 115
	mov BYTE PTR [rdi+1029], dl
	mov edx, 97
	mov BYTE PTR [rdi+1030], dl
	mov edx, 103
	mov BYTE PTR [rdi+1031], dl
	mov edx, 101
	mov BYTE PTR [rdi+1032], dl
	mov rdx, r9
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	mov BYTE PTR [rdi+1034], dl
	shr rdx, 8
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 11
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 75
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_avx2}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, QWORD PTR [rsp+208]
	jne 23b
	mov r9, QWORD PTR [rsp+136]
	sub r9, 11
	mov r8d, 0
24:
	add r8, r8
	add r8, 1
	cmp r8, r9
	jb 24b
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 1136
	mov ecx, 0
	mov r11d, 0
25:
	movzx eax, BYTE PTR [rsi+rcx*1]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx edx, BYTE PTR [rsi+rcx*1+1]
	add rax, rdx
	and rax, r8
	mov rdx, r9
	cmp rdx, rax
	sbb rdx, rdx
	xor r11, rax
	and r11, rdx
	xor r11, rax
	add rcx, 2
	cmp rcx, 256
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	mov r9, QWORD PTR [rsp+136]
	mov ecx, 2
	mov edx, 0
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rdi+rcx*1]
	cmp rax, 1
	sbb rax, rax
	mov rsi, rdx
	xor rsi, -1
	and rsi, rax
	and rsi, rcx
	or r10, rsi
	or rdx, rax
	add rcx, 1
	cmp rcx, r9
	jne 26b
	movzx eax, BYTE PTR [rdi]
	cmp rax, 1
	sbb rax, rax
	movzx esi, BYTE PTR [rdi+1]
	xor rsi, 2
	cmp rsi, 1
	sbb rsi, rsi
	and rax, rsi
	and rax, rdx
	mov rsi, r10
	cmp rsi, 10
	sbb rsi, rsi
	xor rsi, -1
	and rax, rsi
	mov rsi, r9
	sub rsi, r10
	sub rsi, 1
	mov rdx, r11
	xor rdx, rsi
	and rdx, rax
	xor rdx, r11
	mov r10, rax
	mov r11, QWORD PTR [rsp+192]
	mov r11d, r11d
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rsi, r9
	sub rsi, rdx
	and rdx, r11
	mov r8, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov QWORD PTR [r8], rdx
	mov rdx, rsi
	mov rsi, rcx
	mov ecx, 0
27:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	and rax, r10
	xor rax, r8
	mov r8, rcx
	cmp r8, rdx
	sbb r8, r8
	xor r8, -1
	and r8, r11
	and rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, r9
	jne 27b
	mov rax, QWORD PTR [rsp+192]
	lea rsp, [rsp+216]
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
	lea rsp, [rsp-3480]
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
	lea rsp, [rsp+3480]
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

vg_rsa_pkcs1_decrypt_precomputed_sha256_avx2:
	lea rsp, [rsp-216]
	mov QWORD PTR [rsp+112], rdi
	mov QWORD PTR [rsp+120], rdx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], r8
	mov QWORD PTR [rsp+144], r9
	mov rax, QWORD PTR [rsp+224]
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+232]
	mov QWORD PTR [rsp+160], rax
	mov rax, QWORD PTR [rsp+240]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+176], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+184], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+296]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+104], rax
	mov rsi, r8
	mov rdx, rcx
	mov rcx, r8
	mov r8, r9
	mov r9, QWORD PTR [rsp+152]
	call {vg_rsa_private_checked}
	mov QWORD PTR [rsp+192], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+136]
	mov r10d, 0
	mov eax, 0
20:
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 20b
	mov rsi, QWORD PTR [rsp+160]
	mov rcx, QWORD PTR [rsp+168]
	mov rdi, QWORD PTR [rsp+184]
	add rdi, QWORD PTR [rsp+136]
	sub rdi, rcx
	mov r10d, 0
21:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 21b
	mov rdi, QWORD PTR [rsp+184]
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2416
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 192
	call {vg_sha256_finalize_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+136]
	add rdx, 64
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1104
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_avx2}
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+136]
	add rax, 31
	shr rax, 5
	mov QWORD PTR [rsp+208], rax
22:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 108
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 110
	mov BYTE PTR [rdi+1028], dl
	mov edx, 103
	mov BYTE PTR [rdi+1029], dl
	mov edx, 116
	mov BYTE PTR [rdi+1030], dl
	mov edx, 104
	mov BYTE PTR [rdi+1031], dl
	mov edx, 8
	mov BYTE PTR [rdi+1032], dl
	mov edx, 0
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 10
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 74
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1136
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_avx2}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, 8
	jne 22b
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
23:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 109
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 115
	mov BYTE PTR [rdi+1028], dl
	mov edx, 115
	mov BYTE PTR [rdi+1029], dl
	mov edx, 97
	mov BYTE PTR [rdi+1030], dl
	mov edx, 103
	mov BYTE PTR [rdi+1031], dl
	mov edx, 101
	mov BYTE PTR [rdi+1032], dl
	mov rdx, r9
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	mov BYTE PTR [rdi+1034], dl
	shr rdx, 8
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 11
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch_avx2}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 75
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch_avx2}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, QWORD PTR [rsp+208]
	jne 23b
	mov r9, QWORD PTR [rsp+136]
	sub r9, 11
	mov r8d, 0
24:
	add r8, r8
	add r8, 1
	cmp r8, r9
	jb 24b
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 1136
	mov ecx, 0
	mov r11d, 0
25:
	movzx eax, BYTE PTR [rsi+rcx*1]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx edx, BYTE PTR [rsi+rcx*1+1]
	add rax, rdx
	and rax, r8
	mov rdx, r9
	cmp rdx, rax
	sbb rdx, rdx
	xor r11, rax
	and r11, rdx
	xor r11, rax
	add rcx, 2
	cmp rcx, 256
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	mov r9, QWORD PTR [rsp+136]
	mov ecx, 2
	mov edx, 0
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rdi+rcx*1]
	cmp rax, 1
	sbb rax, rax
	mov rsi, rdx
	xor rsi, -1
	and rsi, rax
	and rsi, rcx
	or r10, rsi
	or rdx, rax
	add rcx, 1
	cmp rcx, r9
	jne 26b
	movzx eax, BYTE PTR [rdi]
	cmp rax, 1
	sbb rax, rax
	movzx esi, BYTE PTR [rdi+1]
	xor rsi, 2
	cmp rsi, 1
	sbb rsi, rsi
	and rax, rsi
	and rax, rdx
	mov rsi, r10
	cmp rsi, 10
	sbb rsi, rsi
	xor rsi, -1
	and rax, rsi
	mov rsi, r9
	sub rsi, r10
	sub rsi, 1
	mov rdx, r11
	xor rdx, rsi
	and rdx, rax
	xor rdx, r11
	mov r10, rax
	mov r11, QWORD PTR [rsp+192]
	mov r11d, r11d
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rsi, r9
	sub rsi, rdx
	and rdx, r11
	mov r8, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov QWORD PTR [r8], rdx
	mov rdx, rsi
	mov rsi, rcx
	mov ecx, 0
27:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	and rax, r10
	xor rax, r8
	mov r8, rcx
	cmp r8, rdx
	sbb r8, r8
	xor r8, -1
	and r8, r11
	and rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, r9
	jne 27b
	mov rax, QWORD PTR [rsp+192]
	lea rsp, [rsp+216]
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
	lea rsp, [rsp-3480]
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
	lea rsp, [rsp+3480]
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

vg_rsa_pkcs1_decrypt_crt_ifma512:
	lea rsp, [rsp-216]
	mov QWORD PTR [rsp+112], rdi
	mov QWORD PTR [rsp+120], rdx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], r8
	mov QWORD PTR [rsp+144], r9
	mov rax, QWORD PTR [rsp+224]
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+232]
	mov QWORD PTR [rsp+160], rax
	mov rax, QWORD PTR [rsp+240]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+176], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+184], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+296]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+104], rax
	mov rsi, r8
	mov rdx, rcx
	mov rcx, r8
	mov r8, r9
	mov r9, QWORD PTR [rsp+152]
	call {vg_rsa_private_checked_ifma512}
	mov QWORD PTR [rsp+192], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+136]
	mov r10d, 0
	mov eax, 0
20:
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 20b
	mov rsi, QWORD PTR [rsp+160]
	mov rcx, QWORD PTR [rsp+168]
	mov rdi, QWORD PTR [rsp+184]
	add rdi, QWORD PTR [rsp+136]
	sub rdi, rcx
	mov r10d, 0
21:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 21b
	mov rdi, QWORD PTR [rsp+184]
	call {vg_sha256_init_core}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2416
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 192
	call {vg_sha256_finalize_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+136]
	add rdx, 64
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1104
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch}
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+136]
	add rax, 31
	shr rax, 5
	mov QWORD PTR [rsp+208], rax
22:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 108
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 110
	mov BYTE PTR [rdi+1028], dl
	mov edx, 103
	mov BYTE PTR [rdi+1029], dl
	mov edx, 116
	mov BYTE PTR [rdi+1030], dl
	mov edx, 104
	mov BYTE PTR [rdi+1031], dl
	mov edx, 8
	mov BYTE PTR [rdi+1032], dl
	mov edx, 0
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 10
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 74
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1136
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, 8
	jne 22b
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
23:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 109
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 115
	mov BYTE PTR [rdi+1028], dl
	mov edx, 115
	mov BYTE PTR [rdi+1029], dl
	mov edx, 97
	mov BYTE PTR [rdi+1030], dl
	mov edx, 103
	mov BYTE PTR [rdi+1031], dl
	mov edx, 101
	mov BYTE PTR [rdi+1032], dl
	mov rdx, r9
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	mov BYTE PTR [rdi+1034], dl
	shr rdx, 8
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 11
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 75
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, QWORD PTR [rsp+208]
	jne 23b
	mov r9, QWORD PTR [rsp+136]
	sub r9, 11
	mov r8d, 0
24:
	add r8, r8
	add r8, 1
	cmp r8, r9
	jb 24b
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 1136
	mov ecx, 0
	mov r11d, 0
25:
	movzx eax, BYTE PTR [rsi+rcx*1]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx edx, BYTE PTR [rsi+rcx*1+1]
	add rax, rdx
	and rax, r8
	mov rdx, r9
	cmp rdx, rax
	sbb rdx, rdx
	xor r11, rax
	and r11, rdx
	xor r11, rax
	add rcx, 2
	cmp rcx, 256
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	mov r9, QWORD PTR [rsp+136]
	mov ecx, 2
	mov edx, 0
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rdi+rcx*1]
	cmp rax, 1
	sbb rax, rax
	mov rsi, rdx
	xor rsi, -1
	and rsi, rax
	and rsi, rcx
	or r10, rsi
	or rdx, rax
	add rcx, 1
	cmp rcx, r9
	jne 26b
	movzx eax, BYTE PTR [rdi]
	cmp rax, 1
	sbb rax, rax
	movzx esi, BYTE PTR [rdi+1]
	xor rsi, 2
	cmp rsi, 1
	sbb rsi, rsi
	and rax, rsi
	and rax, rdx
	mov rsi, r10
	cmp rsi, 10
	sbb rsi, rsi
	xor rsi, -1
	and rax, rsi
	mov rsi, r9
	sub rsi, r10
	sub rsi, 1
	mov rdx, r11
	xor rdx, rsi
	and rdx, rax
	xor rdx, r11
	mov r10, rax
	mov r11, QWORD PTR [rsp+192]
	mov r11d, r11d
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rsi, r9
	sub rsi, rdx
	and rdx, r11
	mov r8, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov QWORD PTR [r8], rdx
	mov rdx, rsi
	mov rsi, rcx
	mov ecx, 0
27:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	and rax, r10
	xor rax, r8
	mov r8, rcx
	cmp r8, rdx
	sbb r8, r8
	xor r8, -1
	and r8, r11
	and rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, r9
	jne 27b
	mov rax, QWORD PTR [rsp+192]
	lea rsp, [rsp+216]
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
	lea rsp, [rsp-3480]
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
	lea rsp, [rsp+3480]
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

vg_rsa_pkcs1_decrypt_precomputed_crt_ifma512:
	lea rsp, [rsp-216]
	mov QWORD PTR [rsp+112], rdi
	mov QWORD PTR [rsp+120], rdx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], r8
	mov QWORD PTR [rsp+144], r9
	mov rax, QWORD PTR [rsp+224]
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+232]
	mov QWORD PTR [rsp+160], rax
	mov rax, QWORD PTR [rsp+240]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+176], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+184], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+296]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+104], rax
	mov rsi, r8
	mov rdx, rcx
	mov rcx, r8
	mov r8, r9
	mov r9, QWORD PTR [rsp+152]
	call {vg_rsa_private_checked_ifma512}
	mov QWORD PTR [rsp+192], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+136]
	mov r10d, 0
	mov eax, 0
20:
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 20b
	mov rsi, QWORD PTR [rsp+160]
	mov rcx, QWORD PTR [rsp+168]
	mov rdi, QWORD PTR [rsp+184]
	add rdi, QWORD PTR [rsp+136]
	sub rdi, rcx
	mov r10d, 0
21:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 21b
	mov rdi, QWORD PTR [rsp+184]
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2416
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 192
	call {vg_sha256_finalize_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+136]
	add rdx, 64
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1104
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch}
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+136]
	add rax, 31
	shr rax, 5
	mov QWORD PTR [rsp+208], rax
22:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 108
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 110
	mov BYTE PTR [rdi+1028], dl
	mov edx, 103
	mov BYTE PTR [rdi+1029], dl
	mov edx, 116
	mov BYTE PTR [rdi+1030], dl
	mov edx, 104
	mov BYTE PTR [rdi+1031], dl
	mov edx, 8
	mov BYTE PTR [rdi+1032], dl
	mov edx, 0
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 10
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 74
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1136
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, 8
	jne 22b
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
23:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 109
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 115
	mov BYTE PTR [rdi+1028], dl
	mov edx, 115
	mov BYTE PTR [rdi+1029], dl
	mov edx, 97
	mov BYTE PTR [rdi+1030], dl
	mov edx, 103
	mov BYTE PTR [rdi+1031], dl
	mov edx, 101
	mov BYTE PTR [rdi+1032], dl
	mov rdx, r9
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	mov BYTE PTR [rdi+1034], dl
	shr rdx, 8
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 11
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 75
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, QWORD PTR [rsp+208]
	jne 23b
	mov r9, QWORD PTR [rsp+136]
	sub r9, 11
	mov r8d, 0
24:
	add r8, r8
	add r8, 1
	cmp r8, r9
	jb 24b
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 1136
	mov ecx, 0
	mov r11d, 0
25:
	movzx eax, BYTE PTR [rsi+rcx*1]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx edx, BYTE PTR [rsi+rcx*1+1]
	add rax, rdx
	and rax, r8
	mov rdx, r9
	cmp rdx, rax
	sbb rdx, rdx
	xor r11, rax
	and r11, rdx
	xor r11, rax
	add rcx, 2
	cmp rcx, 256
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	mov r9, QWORD PTR [rsp+136]
	mov ecx, 2
	mov edx, 0
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rdi+rcx*1]
	cmp rax, 1
	sbb rax, rax
	mov rsi, rdx
	xor rsi, -1
	and rsi, rax
	and rsi, rcx
	or r10, rsi
	or rdx, rax
	add rcx, 1
	cmp rcx, r9
	jne 26b
	movzx eax, BYTE PTR [rdi]
	cmp rax, 1
	sbb rax, rax
	movzx esi, BYTE PTR [rdi+1]
	xor rsi, 2
	cmp rsi, 1
	sbb rsi, rsi
	and rax, rsi
	and rax, rdx
	mov rsi, r10
	cmp rsi, 10
	sbb rsi, rsi
	xor rsi, -1
	and rax, rsi
	mov rsi, r9
	sub rsi, r10
	sub rsi, 1
	mov rdx, r11
	xor rdx, rsi
	and rdx, rax
	xor rdx, r11
	mov r10, rax
	mov r11, QWORD PTR [rsp+192]
	mov r11d, r11d
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rsi, r9
	sub rsi, rdx
	and rdx, r11
	mov r8, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov QWORD PTR [r8], rdx
	mov rdx, rsi
	mov rsi, rcx
	mov ecx, 0
27:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	and rax, r10
	xor rax, r8
	mov r8, rcx
	cmp r8, rdx
	sbb r8, r8
	xor r8, -1
	and r8, r11
	and rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, r9
	jne 27b
	mov rax, QWORD PTR [rsp+192]
	lea rsp, [rsp+216]
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
	lea rsp, [rsp-3480]
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
	lea rsp, [rsp+3480]
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

vg_rsa_pkcs1_decrypt_crt_ifma:
	lea rsp, [rsp-216]
	mov QWORD PTR [rsp+112], rdi
	mov QWORD PTR [rsp+120], rdx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], r8
	mov QWORD PTR [rsp+144], r9
	mov rax, QWORD PTR [rsp+224]
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+232]
	mov QWORD PTR [rsp+160], rax
	mov rax, QWORD PTR [rsp+240]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+176], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+184], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+296]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+104], rax
	mov rsi, r8
	mov rdx, rcx
	mov rcx, r8
	mov r8, r9
	mov r9, QWORD PTR [rsp+152]
	call {vg_rsa_private_checked_ifma}
	mov QWORD PTR [rsp+192], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+136]
	mov r10d, 0
	mov eax, 0
20:
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 20b
	mov rsi, QWORD PTR [rsp+160]
	mov rcx, QWORD PTR [rsp+168]
	mov rdi, QWORD PTR [rsp+184]
	add rdi, QWORD PTR [rsp+136]
	sub rdi, rcx
	mov r10d, 0
21:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 21b
	mov rdi, QWORD PTR [rsp+184]
	call {vg_sha256_init_core}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2416
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 192
	call {vg_sha256_finalize_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+136]
	add rdx, 64
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1104
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch}
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+136]
	add rax, 31
	shr rax, 5
	mov QWORD PTR [rsp+208], rax
22:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 108
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 110
	mov BYTE PTR [rdi+1028], dl
	mov edx, 103
	mov BYTE PTR [rdi+1029], dl
	mov edx, 116
	mov BYTE PTR [rdi+1030], dl
	mov edx, 104
	mov BYTE PTR [rdi+1031], dl
	mov edx, 8
	mov BYTE PTR [rdi+1032], dl
	mov edx, 0
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 10
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 74
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1136
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, 8
	jne 22b
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
23:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 109
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 115
	mov BYTE PTR [rdi+1028], dl
	mov edx, 115
	mov BYTE PTR [rdi+1029], dl
	mov edx, 97
	mov BYTE PTR [rdi+1030], dl
	mov edx, 103
	mov BYTE PTR [rdi+1031], dl
	mov edx, 101
	mov BYTE PTR [rdi+1032], dl
	mov rdx, r9
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	mov BYTE PTR [rdi+1034], dl
	shr rdx, 8
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 11
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 75
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, QWORD PTR [rsp+208]
	jne 23b
	mov r9, QWORD PTR [rsp+136]
	sub r9, 11
	mov r8d, 0
24:
	add r8, r8
	add r8, 1
	cmp r8, r9
	jb 24b
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 1136
	mov ecx, 0
	mov r11d, 0
25:
	movzx eax, BYTE PTR [rsi+rcx*1]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx edx, BYTE PTR [rsi+rcx*1+1]
	add rax, rdx
	and rax, r8
	mov rdx, r9
	cmp rdx, rax
	sbb rdx, rdx
	xor r11, rax
	and r11, rdx
	xor r11, rax
	add rcx, 2
	cmp rcx, 256
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	mov r9, QWORD PTR [rsp+136]
	mov ecx, 2
	mov edx, 0
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rdi+rcx*1]
	cmp rax, 1
	sbb rax, rax
	mov rsi, rdx
	xor rsi, -1
	and rsi, rax
	and rsi, rcx
	or r10, rsi
	or rdx, rax
	add rcx, 1
	cmp rcx, r9
	jne 26b
	movzx eax, BYTE PTR [rdi]
	cmp rax, 1
	sbb rax, rax
	movzx esi, BYTE PTR [rdi+1]
	xor rsi, 2
	cmp rsi, 1
	sbb rsi, rsi
	and rax, rsi
	and rax, rdx
	mov rsi, r10
	cmp rsi, 10
	sbb rsi, rsi
	xor rsi, -1
	and rax, rsi
	mov rsi, r9
	sub rsi, r10
	sub rsi, 1
	mov rdx, r11
	xor rdx, rsi
	and rdx, rax
	xor rdx, r11
	mov r10, rax
	mov r11, QWORD PTR [rsp+192]
	mov r11d, r11d
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rsi, r9
	sub rsi, rdx
	and rdx, r11
	mov r8, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov QWORD PTR [r8], rdx
	mov rdx, rsi
	mov rsi, rcx
	mov ecx, 0
27:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	and rax, r10
	xor rax, r8
	mov r8, rcx
	cmp r8, rdx
	sbb r8, r8
	xor r8, -1
	and r8, r11
	and rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, r9
	jne 27b
	mov rax, QWORD PTR [rsp+192]
	lea rsp, [rsp+216]
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
	lea rsp, [rsp-3480]
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
	lea rsp, [rsp+3480]
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

vg_rsa_pkcs1_decrypt_precomputed_crt_ifma:
	lea rsp, [rsp-216]
	mov QWORD PTR [rsp+112], rdi
	mov QWORD PTR [rsp+120], rdx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], r8
	mov QWORD PTR [rsp+144], r9
	mov rax, QWORD PTR [rsp+224]
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+232]
	mov QWORD PTR [rsp+160], rax
	mov rax, QWORD PTR [rsp+240]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+176], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+184], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+296]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+104], rax
	mov rsi, r8
	mov rdx, rcx
	mov rcx, r8
	mov r8, r9
	mov r9, QWORD PTR [rsp+152]
	call {vg_rsa_private_checked_ifma}
	mov QWORD PTR [rsp+192], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+136]
	mov r10d, 0
	mov eax, 0
20:
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 20b
	mov rsi, QWORD PTR [rsp+160]
	mov rcx, QWORD PTR [rsp+168]
	mov rdi, QWORD PTR [rsp+184]
	add rdi, QWORD PTR [rsp+136]
	sub rdi, rcx
	mov r10d, 0
21:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 21b
	mov rdi, QWORD PTR [rsp+184]
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2416
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 192
	call {vg_sha256_finalize_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+136]
	add rdx, 64
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1104
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch}
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+136]
	add rax, 31
	shr rax, 5
	mov QWORD PTR [rsp+208], rax
22:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 108
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 110
	mov BYTE PTR [rdi+1028], dl
	mov edx, 103
	mov BYTE PTR [rdi+1029], dl
	mov edx, 116
	mov BYTE PTR [rdi+1030], dl
	mov edx, 104
	mov BYTE PTR [rdi+1031], dl
	mov edx, 8
	mov BYTE PTR [rdi+1032], dl
	mov edx, 0
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 10
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 74
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1136
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, 8
	jne 22b
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
23:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 109
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 115
	mov BYTE PTR [rdi+1028], dl
	mov edx, 115
	mov BYTE PTR [rdi+1029], dl
	mov edx, 97
	mov BYTE PTR [rdi+1030], dl
	mov edx, 103
	mov BYTE PTR [rdi+1031], dl
	mov edx, 101
	mov BYTE PTR [rdi+1032], dl
	mov rdx, r9
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	mov BYTE PTR [rdi+1034], dl
	shr rdx, 8
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 11
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 75
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, QWORD PTR [rsp+208]
	jne 23b
	mov r9, QWORD PTR [rsp+136]
	sub r9, 11
	mov r8d, 0
24:
	add r8, r8
	add r8, 1
	cmp r8, r9
	jb 24b
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 1136
	mov ecx, 0
	mov r11d, 0
25:
	movzx eax, BYTE PTR [rsi+rcx*1]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx edx, BYTE PTR [rsi+rcx*1+1]
	add rax, rdx
	and rax, r8
	mov rdx, r9
	cmp rdx, rax
	sbb rdx, rdx
	xor r11, rax
	and r11, rdx
	xor r11, rax
	add rcx, 2
	cmp rcx, 256
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	mov r9, QWORD PTR [rsp+136]
	mov ecx, 2
	mov edx, 0
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rdi+rcx*1]
	cmp rax, 1
	sbb rax, rax
	mov rsi, rdx
	xor rsi, -1
	and rsi, rax
	and rsi, rcx
	or r10, rsi
	or rdx, rax
	add rcx, 1
	cmp rcx, r9
	jne 26b
	movzx eax, BYTE PTR [rdi]
	cmp rax, 1
	sbb rax, rax
	movzx esi, BYTE PTR [rdi+1]
	xor rsi, 2
	cmp rsi, 1
	sbb rsi, rsi
	and rax, rsi
	and rax, rdx
	mov rsi, r10
	cmp rsi, 10
	sbb rsi, rsi
	xor rsi, -1
	and rax, rsi
	mov rsi, r9
	sub rsi, r10
	sub rsi, 1
	mov rdx, r11
	xor rdx, rsi
	and rdx, rax
	xor rdx, r11
	mov r10, rax
	mov r11, QWORD PTR [rsp+192]
	mov r11d, r11d
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rsi, r9
	sub rsi, rdx
	and rdx, r11
	mov r8, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov QWORD PTR [r8], rdx
	mov rdx, rsi
	mov rsi, rcx
	mov ecx, 0
27:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	and rax, r10
	xor rax, r8
	mov r8, rcx
	cmp r8, rdx
	sbb r8, r8
	xor r8, -1
	and r8, r11
	and rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, r9
	jne 27b
	mov rax, QWORD PTR [rsp+192]
	lea rsp, [rsp+216]
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
	lea rsp, [rsp-3480]
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
	lea rsp, [rsp+3480]
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

vg_rsa_pkcs1_decrypt_crt_adx:
	lea rsp, [rsp-216]
	mov QWORD PTR [rsp+112], rdi
	mov QWORD PTR [rsp+120], rdx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], r8
	mov QWORD PTR [rsp+144], r9
	mov rax, QWORD PTR [rsp+224]
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+232]
	mov QWORD PTR [rsp+160], rax
	mov rax, QWORD PTR [rsp+240]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+176], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+184], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+296]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+104], rax
	mov rsi, r8
	mov rdx, rcx
	mov rcx, r8
	mov r8, r9
	mov r9, QWORD PTR [rsp+152]
	call {vg_rsa_private_checked_adx}
	mov QWORD PTR [rsp+192], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+136]
	mov r10d, 0
	mov eax, 0
20:
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 20b
	mov rsi, QWORD PTR [rsp+160]
	mov rcx, QWORD PTR [rsp+168]
	mov rdi, QWORD PTR [rsp+184]
	add rdi, QWORD PTR [rsp+136]
	sub rdi, rcx
	mov r10d, 0
21:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 21b
	mov rdi, QWORD PTR [rsp+184]
	call {vg_sha256_init_core}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2416
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 192
	call {vg_sha256_finalize_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+136]
	add rdx, 64
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1104
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch}
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+136]
	add rax, 31
	shr rax, 5
	mov QWORD PTR [rsp+208], rax
22:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 108
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 110
	mov BYTE PTR [rdi+1028], dl
	mov edx, 103
	mov BYTE PTR [rdi+1029], dl
	mov edx, 116
	mov BYTE PTR [rdi+1030], dl
	mov edx, 104
	mov BYTE PTR [rdi+1031], dl
	mov edx, 8
	mov BYTE PTR [rdi+1032], dl
	mov edx, 0
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 10
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 74
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1136
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, 8
	jne 22b
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
23:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 109
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 115
	mov BYTE PTR [rdi+1028], dl
	mov edx, 115
	mov BYTE PTR [rdi+1029], dl
	mov edx, 97
	mov BYTE PTR [rdi+1030], dl
	mov edx, 103
	mov BYTE PTR [rdi+1031], dl
	mov edx, 101
	mov BYTE PTR [rdi+1032], dl
	mov rdx, r9
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	mov BYTE PTR [rdi+1034], dl
	shr rdx, 8
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 11
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 75
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, QWORD PTR [rsp+208]
	jne 23b
	mov r9, QWORD PTR [rsp+136]
	sub r9, 11
	mov r8d, 0
24:
	add r8, r8
	add r8, 1
	cmp r8, r9
	jb 24b
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 1136
	mov ecx, 0
	mov r11d, 0
25:
	movzx eax, BYTE PTR [rsi+rcx*1]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx edx, BYTE PTR [rsi+rcx*1+1]
	add rax, rdx
	and rax, r8
	mov rdx, r9
	cmp rdx, rax
	sbb rdx, rdx
	xor r11, rax
	and r11, rdx
	xor r11, rax
	add rcx, 2
	cmp rcx, 256
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	mov r9, QWORD PTR [rsp+136]
	mov ecx, 2
	mov edx, 0
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rdi+rcx*1]
	cmp rax, 1
	sbb rax, rax
	mov rsi, rdx
	xor rsi, -1
	and rsi, rax
	and rsi, rcx
	or r10, rsi
	or rdx, rax
	add rcx, 1
	cmp rcx, r9
	jne 26b
	movzx eax, BYTE PTR [rdi]
	cmp rax, 1
	sbb rax, rax
	movzx esi, BYTE PTR [rdi+1]
	xor rsi, 2
	cmp rsi, 1
	sbb rsi, rsi
	and rax, rsi
	and rax, rdx
	mov rsi, r10
	cmp rsi, 10
	sbb rsi, rsi
	xor rsi, -1
	and rax, rsi
	mov rsi, r9
	sub rsi, r10
	sub rsi, 1
	mov rdx, r11
	xor rdx, rsi
	and rdx, rax
	xor rdx, r11
	mov r10, rax
	mov r11, QWORD PTR [rsp+192]
	mov r11d, r11d
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rsi, r9
	sub rsi, rdx
	and rdx, r11
	mov r8, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov QWORD PTR [r8], rdx
	mov rdx, rsi
	mov rsi, rcx
	mov ecx, 0
27:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	and rax, r10
	xor rax, r8
	mov r8, rcx
	cmp r8, rdx
	sbb r8, r8
	xor r8, -1
	and r8, r11
	and rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, r9
	jne 27b
	mov rax, QWORD PTR [rsp+192]
	lea rsp, [rsp+216]
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
	lea rsp, [rsp-3480]
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
	lea rsp, [rsp+3480]
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

vg_rsa_pkcs1_decrypt_precomputed_crt_adx:
	lea rsp, [rsp-216]
	mov QWORD PTR [rsp+112], rdi
	mov QWORD PTR [rsp+120], rdx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], r8
	mov QWORD PTR [rsp+144], r9
	mov rax, QWORD PTR [rsp+224]
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+232]
	mov QWORD PTR [rsp+160], rax
	mov rax, QWORD PTR [rsp+240]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+176], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+184], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+296]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+104], rax
	mov rsi, r8
	mov rdx, rcx
	mov rcx, r8
	mov r8, r9
	mov r9, QWORD PTR [rsp+152]
	call {vg_rsa_private_checked_adx}
	mov QWORD PTR [rsp+192], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+136]
	mov r10d, 0
	mov eax, 0
20:
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 20b
	mov rsi, QWORD PTR [rsp+160]
	mov rcx, QWORD PTR [rsp+168]
	mov rdi, QWORD PTR [rsp+184]
	add rdi, QWORD PTR [rsp+136]
	sub rdi, rcx
	mov r10d, 0
21:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 21b
	mov rdi, QWORD PTR [rsp+184]
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2416
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 192
	call {vg_sha256_finalize_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+136]
	add rdx, 64
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1104
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch}
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+136]
	add rax, 31
	shr rax, 5
	mov QWORD PTR [rsp+208], rax
22:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 108
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 110
	mov BYTE PTR [rdi+1028], dl
	mov edx, 103
	mov BYTE PTR [rdi+1029], dl
	mov edx, 116
	mov BYTE PTR [rdi+1030], dl
	mov edx, 104
	mov BYTE PTR [rdi+1031], dl
	mov edx, 8
	mov BYTE PTR [rdi+1032], dl
	mov edx, 0
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 10
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 74
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1136
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, 8
	jne 22b
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
23:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 109
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 115
	mov BYTE PTR [rdi+1028], dl
	mov edx, 115
	mov BYTE PTR [rdi+1029], dl
	mov edx, 97
	mov BYTE PTR [rdi+1030], dl
	mov edx, 103
	mov BYTE PTR [rdi+1031], dl
	mov edx, 101
	mov BYTE PTR [rdi+1032], dl
	mov rdx, r9
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	mov BYTE PTR [rdi+1034], dl
	shr rdx, 8
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 11
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 75
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, QWORD PTR [rsp+208]
	jne 23b
	mov r9, QWORD PTR [rsp+136]
	sub r9, 11
	mov r8d, 0
24:
	add r8, r8
	add r8, 1
	cmp r8, r9
	jb 24b
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 1136
	mov ecx, 0
	mov r11d, 0
25:
	movzx eax, BYTE PTR [rsi+rcx*1]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx edx, BYTE PTR [rsi+rcx*1+1]
	add rax, rdx
	and rax, r8
	mov rdx, r9
	cmp rdx, rax
	sbb rdx, rdx
	xor r11, rax
	and r11, rdx
	xor r11, rax
	add rcx, 2
	cmp rcx, 256
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	mov r9, QWORD PTR [rsp+136]
	mov ecx, 2
	mov edx, 0
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rdi+rcx*1]
	cmp rax, 1
	sbb rax, rax
	mov rsi, rdx
	xor rsi, -1
	and rsi, rax
	and rsi, rcx
	or r10, rsi
	or rdx, rax
	add rcx, 1
	cmp rcx, r9
	jne 26b
	movzx eax, BYTE PTR [rdi]
	cmp rax, 1
	sbb rax, rax
	movzx esi, BYTE PTR [rdi+1]
	xor rsi, 2
	cmp rsi, 1
	sbb rsi, rsi
	and rax, rsi
	and rax, rdx
	mov rsi, r10
	cmp rsi, 10
	sbb rsi, rsi
	xor rsi, -1
	and rax, rsi
	mov rsi, r9
	sub rsi, r10
	sub rsi, 1
	mov rdx, r11
	xor rdx, rsi
	and rdx, rax
	xor rdx, r11
	mov r10, rax
	mov r11, QWORD PTR [rsp+192]
	mov r11d, r11d
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rsi, r9
	sub rsi, rdx
	and rdx, r11
	mov r8, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov QWORD PTR [r8], rdx
	mov rdx, rsi
	mov rsi, rcx
	mov ecx, 0
27:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	and rax, r10
	xor rax, r8
	mov r8, rcx
	cmp r8, rdx
	sbb r8, r8
	xor r8, -1
	and r8, r11
	and rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, r9
	jne 27b
	mov rax, QWORD PTR [rsp+192]
	lea rsp, [rsp+216]
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
	lea rsp, [rsp-3480]
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
	lea rsp, [rsp+3480]
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

vg_rsa_pkcs1_decrypt:
	lea rsp, [rsp-216]
	mov QWORD PTR [rsp+112], rdi
	mov QWORD PTR [rsp+120], rdx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], r8
	mov QWORD PTR [rsp+144], r9
	mov rax, QWORD PTR [rsp+224]
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+232]
	mov QWORD PTR [rsp+160], rax
	mov rax, QWORD PTR [rsp+240]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+176], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+184], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+296]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+104], rax
	mov rsi, r8
	mov rdx, rcx
	mov rcx, r8
	mov r8, r9
	mov r9, QWORD PTR [rsp+152]
	call {vg_rsa_private_checked}
	mov QWORD PTR [rsp+192], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+136]
	mov r10d, 0
	mov eax, 0
20:
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 20b
	mov rsi, QWORD PTR [rsp+160]
	mov rcx, QWORD PTR [rsp+168]
	mov rdi, QWORD PTR [rsp+184]
	add rdi, QWORD PTR [rsp+136]
	sub rdi, rcx
	mov r10d, 0
21:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 21b
	mov rdi, QWORD PTR [rsp+184]
	call {vg_sha256_init_core}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2416
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 192
	call {vg_sha256_finalize_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+136]
	add rdx, 64
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1104
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch}
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+136]
	add rax, 31
	shr rax, 5
	mov QWORD PTR [rsp+208], rax
22:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 108
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 110
	mov BYTE PTR [rdi+1028], dl
	mov edx, 103
	mov BYTE PTR [rdi+1029], dl
	mov edx, 116
	mov BYTE PTR [rdi+1030], dl
	mov edx, 104
	mov BYTE PTR [rdi+1031], dl
	mov edx, 8
	mov BYTE PTR [rdi+1032], dl
	mov edx, 0
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 10
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 74
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1136
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, 8
	jne 22b
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
23:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 109
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 115
	mov BYTE PTR [rdi+1028], dl
	mov edx, 115
	mov BYTE PTR [rdi+1029], dl
	mov edx, 97
	mov BYTE PTR [rdi+1030], dl
	mov edx, 103
	mov BYTE PTR [rdi+1031], dl
	mov edx, 101
	mov BYTE PTR [rdi+1032], dl
	mov rdx, r9
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	mov BYTE PTR [rdi+1034], dl
	shr rdx, 8
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 11
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 75
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, QWORD PTR [rsp+208]
	jne 23b
	mov r9, QWORD PTR [rsp+136]
	sub r9, 11
	mov r8d, 0
24:
	add r8, r8
	add r8, 1
	cmp r8, r9
	jb 24b
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 1136
	mov ecx, 0
	mov r11d, 0
25:
	movzx eax, BYTE PTR [rsi+rcx*1]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx edx, BYTE PTR [rsi+rcx*1+1]
	add rax, rdx
	and rax, r8
	mov rdx, r9
	cmp rdx, rax
	sbb rdx, rdx
	xor r11, rax
	and r11, rdx
	xor r11, rax
	add rcx, 2
	cmp rcx, 256
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	mov r9, QWORD PTR [rsp+136]
	mov ecx, 2
	mov edx, 0
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rdi+rcx*1]
	cmp rax, 1
	sbb rax, rax
	mov rsi, rdx
	xor rsi, -1
	and rsi, rax
	and rsi, rcx
	or r10, rsi
	or rdx, rax
	add rcx, 1
	cmp rcx, r9
	jne 26b
	movzx eax, BYTE PTR [rdi]
	cmp rax, 1
	sbb rax, rax
	movzx esi, BYTE PTR [rdi+1]
	xor rsi, 2
	cmp rsi, 1
	sbb rsi, rsi
	and rax, rsi
	and rax, rdx
	mov rsi, r10
	cmp rsi, 10
	sbb rsi, rsi
	xor rsi, -1
	and rax, rsi
	mov rsi, r9
	sub rsi, r10
	sub rsi, 1
	mov rdx, r11
	xor rdx, rsi
	and rdx, rax
	xor rdx, r11
	mov r10, rax
	mov r11, QWORD PTR [rsp+192]
	mov r11d, r11d
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rsi, r9
	sub rsi, rdx
	and rdx, r11
	mov r8, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov QWORD PTR [r8], rdx
	mov rdx, rsi
	mov rsi, rcx
	mov ecx, 0
27:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	and rax, r10
	xor rax, r8
	mov r8, rcx
	cmp r8, rdx
	sbb r8, r8
	xor r8, -1
	and r8, r11
	and rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, r9
	jne 27b
	mov rax, QWORD PTR [rsp+192]
	lea rsp, [rsp+216]
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
	lea rsp, [rsp-3480]
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
	lea rsp, [rsp+3480]
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

vg_rsa_pkcs1_decrypt_precomputed:
	lea rsp, [rsp-216]
	mov QWORD PTR [rsp+112], rdi
	mov QWORD PTR [rsp+120], rdx
	mov QWORD PTR [rsp+128], rcx
	mov QWORD PTR [rsp+136], r8
	mov QWORD PTR [rsp+144], r9
	mov rax, QWORD PTR [rsp+224]
	mov QWORD PTR [rsp+152], rax
	mov rax, QWORD PTR [rsp+232]
	mov QWORD PTR [rsp+160], rax
	mov rax, QWORD PTR [rsp+240]
	mov QWORD PTR [rsp+168], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+176], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+184], rax
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+288]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+296]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+304]
	mov QWORD PTR [rsp+56], rax
	mov rax, QWORD PTR [rsp+312]
	mov QWORD PTR [rsp+64], rax
	mov rax, QWORD PTR [rsp+320]
	mov QWORD PTR [rsp+72], rax
	mov rax, QWORD PTR [rsp+328]
	mov QWORD PTR [rsp+80], rax
	mov rax, QWORD PTR [rsp+336]
	mov QWORD PTR [rsp+88], rax
	mov rax, QWORD PTR [rsp+344]
	mov QWORD PTR [rsp+96], rax
	mov rax, QWORD PTR [rsp+352]
	mov QWORD PTR [rsp+104], rax
	mov rsi, r8
	mov rdx, rcx
	mov rcx, r8
	mov r8, r9
	mov r9, QWORD PTR [rsp+152]
	call {vg_rsa_private_checked}
	mov QWORD PTR [rsp+192], rax
	mov rdi, QWORD PTR [rsp+184]
	mov rcx, QWORD PTR [rsp+136]
	mov r10d, 0
	mov eax, 0
20:
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 20b
	mov rsi, QWORD PTR [rsp+160]
	mov rcx, QWORD PTR [rsp+168]
	mov rdi, QWORD PTR [rsp+184]
	add rdi, QWORD PTR [rsp+136]
	sub rdi, rcx
	mov r10d, 0
21:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1+2416], al
	add r10, 1
	cmp r10, rcx
	jne 21b
	mov rdi, QWORD PTR [rsp+184]
	call {vg_sha256_init}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 0
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 2416
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+136]
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 192
	call {vg_sha256_finalize_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1040
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+176]
	mov rcx, QWORD PTR [rsp+136]
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+136]
	add rdx, 64
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1104
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch}
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
	mov rax, QWORD PTR [rsp+136]
	add rax, 31
	shr rax, 5
	mov QWORD PTR [rsp+208], rax
22:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 108
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 110
	mov BYTE PTR [rdi+1028], dl
	mov edx, 103
	mov BYTE PTR [rdi+1029], dl
	mov edx, 116
	mov BYTE PTR [rdi+1030], dl
	mov edx, 104
	mov BYTE PTR [rdi+1031], dl
	mov edx, 8
	mov BYTE PTR [rdi+1032], dl
	mov edx, 0
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 10
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 74
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1136
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, 8
	jne 22b
	mov eax, 0
	mov QWORD PTR [rsp+200], rax
23:
	mov rdi, QWORD PTR [rsp+184]
	mov rax, QWORD PTR [rsp+200]
	mov r9, QWORD PTR [rsp+136]
	mov edx, 0
	mov BYTE PTR [rdi+1024], dl
	mov BYTE PTR [rdi+1025], al
	mov edx, 109
	mov BYTE PTR [rdi+1026], dl
	mov edx, 101
	mov BYTE PTR [rdi+1027], dl
	mov edx, 115
	mov BYTE PTR [rdi+1028], dl
	mov edx, 115
	mov BYTE PTR [rdi+1029], dl
	mov edx, 97
	mov BYTE PTR [rdi+1030], dl
	mov edx, 103
	mov BYTE PTR [rdi+1031], dl
	mov edx, 101
	mov BYTE PTR [rdi+1032], dl
	mov rdx, r9
	add rdx, rdx
	add rdx, rdx
	add rdx, rdx
	mov BYTE PTR [rdi+1034], dl
	shr rdx, 8
	mov BYTE PTR [rdi+1033], dl
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1104
	mov ecx, 32
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_init_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov esi, 64
	mov rdx, QWORD PTR [rsp+184]
	add rdx, 1024
	mov ecx, 11
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_sha256_update_scratch}
	mov rdi, QWORD PTR [rsp+184]
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 96
	mov edx, 75
	mov rcx, QWORD PTR [rsp+200]
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, rcx
	add rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov r8, QWORD PTR [rsp+184]
	add r8, 192
	call {vg_hmac_sha256_finalize_scratch}
	mov rax, QWORD PTR [rsp+200]
	add rax, 1
	mov QWORD PTR [rsp+200], rax
	cmp rax, QWORD PTR [rsp+208]
	jne 23b
	mov r9, QWORD PTR [rsp+136]
	sub r9, 11
	mov r8d, 0
24:
	add r8, r8
	add r8, 1
	cmp r8, r9
	jb 24b
	mov rsi, QWORD PTR [rsp+184]
	add rsi, 1136
	mov ecx, 0
	mov r11d, 0
25:
	movzx eax, BYTE PTR [rsi+rcx*1]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	movzx edx, BYTE PTR [rsi+rcx*1+1]
	add rax, rdx
	and rax, r8
	mov rdx, r9
	cmp rdx, rax
	sbb rdx, rdx
	xor r11, rax
	and r11, rdx
	xor r11, rax
	add rcx, 2
	cmp rcx, 256
	jne 25b
	mov rdi, QWORD PTR [rsp+112]
	mov r9, QWORD PTR [rsp+136]
	mov ecx, 2
	mov edx, 0
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rdi+rcx*1]
	cmp rax, 1
	sbb rax, rax
	mov rsi, rdx
	xor rsi, -1
	and rsi, rax
	and rsi, rcx
	or r10, rsi
	or rdx, rax
	add rcx, 1
	cmp rcx, r9
	jne 26b
	movzx eax, BYTE PTR [rdi]
	cmp rax, 1
	sbb rax, rax
	movzx esi, BYTE PTR [rdi+1]
	xor rsi, 2
	cmp rsi, 1
	sbb rsi, rsi
	and rax, rsi
	and rax, rdx
	mov rsi, r10
	cmp rsi, 10
	sbb rsi, rsi
	xor rsi, -1
	and rax, rsi
	mov rsi, r9
	sub rsi, r10
	sub rsi, 1
	mov rdx, r11
	xor rdx, rsi
	and rdx, rax
	xor rdx, r11
	mov r10, rax
	mov r11, QWORD PTR [rsp+192]
	mov r11d, r11d
	xor r11, 1
	cmp r11, 1
	sbb r11, r11
	mov rsi, r9
	sub rsi, rdx
	and rdx, r11
	mov r8, QWORD PTR [rsp+120]
	mov rcx, QWORD PTR [rsp+184]
	add rcx, 1392
	mov QWORD PTR [r8], rdx
	mov rdx, rsi
	mov rsi, rcx
	mov ecx, 0
27:
	movzx eax, BYTE PTR [rdi+rcx*1]
	movzx r8d, BYTE PTR [rsi+rcx*1]
	xor rax, r8
	and rax, r10
	xor rax, r8
	mov r8, rcx
	cmp r8, rdx
	sbb r8, r8
	xor r8, -1
	and r8, r11
	and rax, r8
	mov BYTE PTR [rdi+rcx*1], al
	add rcx, 1
	cmp rcx, r9
	jne 27b
	mov rax, QWORD PTR [rsp+192]
	lea rsp, [rsp+216]
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
	lea rsp, [rsp-3480]
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
	lea rsp, [rsp+3480]
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

vg_rsa_pkcs1_encrypt_random_ifma:
	lea rsp, [rsp-1160]
	mov rax, r8
	sub rax, QWORD PTR [rsp+1184]
	sub rax, 3
	mov rsi, QWORD PTR [rsp+1192]
	mov r11, QWORD PTR [rsp+1200]
	mov QWORD PTR [rsp+64], rdi
	mov QWORD PTR [rsp+72], rdx
	mov QWORD PTR [rsp+80], rcx
	mov QWORD PTR [rsp+88], r8
	mov QWORD PTR [rsp+96], r9
	mov QWORD PTR [rsp+104], rax
	mov rdi, rsp
	add rdi, 128
	mov ecx, 0
	mov edx, 0
	test r11, r11
	jne 20f
	jmp 21f
20:
22:
	movzx eax, BYTE PTR [rsi+rcx*1]
	add rcx, 1
	test rax, rax
	jne 23f
	jmp 24f
23:
	mov BYTE PTR [rdi+rdx*1], al
	add rdx, 1
24:
	cmp rdx, QWORD PTR [rsp+104]
	je 25f
	mov rax, r11
	sub rax, rcx
	jmp 26f
25:
	mov eax, 0
	test rax, rax
26:
	jne 22b
21:
	cmp rdx, QWORD PTR [rsp+104]
	je 27f
	mov rdi, QWORD PTR [rsp+64]
	mov r10, QWORD PTR [rsp+88]
	mov eax, 0
29:
	mov BYTE PTR [rdi], al
	add rdi, 1
	sub r10, 1
	jne 29b
	mov rdi, rsp
	add rdi, 128
	mov r10d, 0
	mov rcx, rdx
	test rdx, rdx
	jne 210f
	jmp 211f
210:
212:
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 212b
211:
	mov r10, QWORD PTR [rsp+104]
	add r10, 128
	mov r8, QWORD PTR [rsp+72]
	cmp r11, r10
	jae 213f
	mov eax, 0
	mov QWORD PTR [r8], rax
	mov r9, QWORD PTR [rsp+104]
	add r9, r11
	sub r9, rdx
	cmp r10, r9
	cmovb r9, r10
	mov QWORD PTR [r8+8], r9
	jmp 214f
213:
	mov QWORD PTR [r8], r11
	mov eax, 0
	mov QWORD PTR [r8+8], rax
	mov eax, 3
214:
	jmp 28f
27:
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rax], rcx
	mov r10d, 0
	mov QWORD PTR [rax+8], r10
	mov rax, QWORD PTR [rsp+1176]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+1184]
	mov QWORD PTR [rsp+8], rax
	mov QWORD PTR [rsp+16], rdi
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+1208]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+1216]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+1224]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+1232]
	mov QWORD PTR [rsp+56], rax
	mov rdi, QWORD PTR [rsp+64]
	mov rsi, QWORD PTR [rsp+88]
	mov rdx, QWORD PTR [rsp+80]
	mov rcx, QWORD PTR [rsp+88]
	mov r8, QWORD PTR [rsp+96]
	mov r9, QWORD PTR [rsp+1168]
	call {vg_rsa_pkcs1_encrypt_precomputed_ifma}
	mov r11d, 2
	sub r11d, eax
	mov rdi, rsp
	add rdi, 128
	mov rcx, QWORD PTR [rsp+104]
	mov r10d, 0
	mov eax, 0
215:
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 215b
	mov eax, r11d
28:
	lea rsp, [rsp+1160]
	ret
	.p2align 6

vg_rsa_pkcs1_encrypt_random_adx:
	lea rsp, [rsp-1160]
	mov rax, r8
	sub rax, QWORD PTR [rsp+1184]
	sub rax, 3
	mov rsi, QWORD PTR [rsp+1192]
	mov r11, QWORD PTR [rsp+1200]
	mov QWORD PTR [rsp+64], rdi
	mov QWORD PTR [rsp+72], rdx
	mov QWORD PTR [rsp+80], rcx
	mov QWORD PTR [rsp+88], r8
	mov QWORD PTR [rsp+96], r9
	mov QWORD PTR [rsp+104], rax
	mov rdi, rsp
	add rdi, 128
	mov ecx, 0
	mov edx, 0
	test r11, r11
	jne 20f
	jmp 21f
20:
22:
	movzx eax, BYTE PTR [rsi+rcx*1]
	add rcx, 1
	test rax, rax
	jne 23f
	jmp 24f
23:
	mov BYTE PTR [rdi+rdx*1], al
	add rdx, 1
24:
	cmp rdx, QWORD PTR [rsp+104]
	je 25f
	mov rax, r11
	sub rax, rcx
	jmp 26f
25:
	mov eax, 0
	test rax, rax
26:
	jne 22b
21:
	cmp rdx, QWORD PTR [rsp+104]
	je 27f
	mov rdi, QWORD PTR [rsp+64]
	mov r10, QWORD PTR [rsp+88]
	mov eax, 0
29:
	mov BYTE PTR [rdi], al
	add rdi, 1
	sub r10, 1
	jne 29b
	mov rdi, rsp
	add rdi, 128
	mov r10d, 0
	mov rcx, rdx
	test rdx, rdx
	jne 210f
	jmp 211f
210:
212:
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 212b
211:
	mov r10, QWORD PTR [rsp+104]
	add r10, 128
	mov r8, QWORD PTR [rsp+72]
	cmp r11, r10
	jae 213f
	mov eax, 0
	mov QWORD PTR [r8], rax
	mov r9, QWORD PTR [rsp+104]
	add r9, r11
	sub r9, rdx
	cmp r10, r9
	cmovb r9, r10
	mov QWORD PTR [r8+8], r9
	jmp 214f
213:
	mov QWORD PTR [r8], r11
	mov eax, 0
	mov QWORD PTR [r8+8], rax
	mov eax, 3
214:
	jmp 28f
27:
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rax], rcx
	mov r10d, 0
	mov QWORD PTR [rax+8], r10
	mov rax, QWORD PTR [rsp+1176]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+1184]
	mov QWORD PTR [rsp+8], rax
	mov QWORD PTR [rsp+16], rdi
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+1208]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+1216]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+1224]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+1232]
	mov QWORD PTR [rsp+56], rax
	mov rdi, QWORD PTR [rsp+64]
	mov rsi, QWORD PTR [rsp+88]
	mov rdx, QWORD PTR [rsp+80]
	mov rcx, QWORD PTR [rsp+88]
	mov r8, QWORD PTR [rsp+96]
	mov r9, QWORD PTR [rsp+1168]
	call {vg_rsa_pkcs1_encrypt_precomputed_adx}
	mov r11d, 2
	sub r11d, eax
	mov rdi, rsp
	add rdi, 128
	mov rcx, QWORD PTR [rsp+104]
	mov r10d, 0
	mov eax, 0
215:
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 215b
	mov eax, r11d
28:
	lea rsp, [rsp+1160]
	ret
	.p2align 6

vg_rsa_pkcs1_encrypt_random:
	lea rsp, [rsp-1160]
	mov rax, r8
	sub rax, QWORD PTR [rsp+1184]
	sub rax, 3
	mov rsi, QWORD PTR [rsp+1192]
	mov r11, QWORD PTR [rsp+1200]
	mov QWORD PTR [rsp+64], rdi
	mov QWORD PTR [rsp+72], rdx
	mov QWORD PTR [rsp+80], rcx
	mov QWORD PTR [rsp+88], r8
	mov QWORD PTR [rsp+96], r9
	mov QWORD PTR [rsp+104], rax
	mov rdi, rsp
	add rdi, 128
	mov ecx, 0
	mov edx, 0
	test r11, r11
	jne 20f
	jmp 21f
20:
22:
	movzx eax, BYTE PTR [rsi+rcx*1]
	add rcx, 1
	test rax, rax
	jne 23f
	jmp 24f
23:
	mov BYTE PTR [rdi+rdx*1], al
	add rdx, 1
24:
	cmp rdx, QWORD PTR [rsp+104]
	je 25f
	mov rax, r11
	sub rax, rcx
	jmp 26f
25:
	mov eax, 0
	test rax, rax
26:
	jne 22b
21:
	cmp rdx, QWORD PTR [rsp+104]
	je 27f
	mov rdi, QWORD PTR [rsp+64]
	mov r10, QWORD PTR [rsp+88]
	mov eax, 0
29:
	mov BYTE PTR [rdi], al
	add rdi, 1
	sub r10, 1
	jne 29b
	mov rdi, rsp
	add rdi, 128
	mov r10d, 0
	mov rcx, rdx
	test rdx, rdx
	jne 210f
	jmp 211f
210:
212:
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 212b
211:
	mov r10, QWORD PTR [rsp+104]
	add r10, 128
	mov r8, QWORD PTR [rsp+72]
	cmp r11, r10
	jae 213f
	mov eax, 0
	mov QWORD PTR [r8], rax
	mov r9, QWORD PTR [rsp+104]
	add r9, r11
	sub r9, rdx
	cmp r10, r9
	cmovb r9, r10
	mov QWORD PTR [r8+8], r9
	jmp 214f
213:
	mov QWORD PTR [r8], r11
	mov eax, 0
	mov QWORD PTR [r8+8], rax
	mov eax, 3
214:
	jmp 28f
27:
	mov rax, QWORD PTR [rsp+72]
	mov QWORD PTR [rax], rcx
	mov r10d, 0
	mov QWORD PTR [rax+8], r10
	mov rax, QWORD PTR [rsp+1176]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+1184]
	mov QWORD PTR [rsp+8], rax
	mov QWORD PTR [rsp+16], rdi
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+1208]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+1216]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+1224]
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+1232]
	mov QWORD PTR [rsp+56], rax
	mov rdi, QWORD PTR [rsp+64]
	mov rsi, QWORD PTR [rsp+88]
	mov rdx, QWORD PTR [rsp+80]
	mov rcx, QWORD PTR [rsp+88]
	mov r8, QWORD PTR [rsp+96]
	mov r9, QWORD PTR [rsp+1168]
	call {vg_rsa_pkcs1_encrypt_precomputed}
	mov r11d, 2
	sub r11d, eax
	mov rdi, rsp
	add rdi, 128
	mov rcx, QWORD PTR [rsp+104]
	mov r10d, 0
	mov eax, 0
215:
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 215b
	mov eax, r11d
28:
	lea rsp, [rsp+1160]
	ret
	.p2align 6
