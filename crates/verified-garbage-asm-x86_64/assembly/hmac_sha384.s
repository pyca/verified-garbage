// The functions of `src/hmac_sha384.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_sha384_init_shani:
	cmp rcx, 129
	jae 20f
	lea rsp, [rsp-1880]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+1376], rbx
	mov QWORD PTR [r8+1384], rbp
	mov QWORD PTR [r8+1392], r12
	mov QWORD PTR [r8+1400], r13
	mov QWORD PTR [r8+1408], r14
	mov QWORD PTR [r8+1416], r15
	mov rbx, rdi
	mov r12, rsi
	mov r15, r8
	mov rbp, rdx
	mov r13, rcx
	mov rdi, rbx
	call {vg_sha384_init}
	mov rdi, r12
	call {vg_sha384_init}
	mov eax, 909522486
	mov DWORD PTR [rbx+64], eax
	mov DWORD PTR [rbx+68], eax
	mov DWORD PTR [rbx+72], eax
	mov DWORD PTR [rbx+76], eax
	mov DWORD PTR [rbx+80], eax
	mov DWORD PTR [rbx+84], eax
	mov DWORD PTR [rbx+88], eax
	mov DWORD PTR [rbx+92], eax
	mov DWORD PTR [rbx+96], eax
	mov DWORD PTR [rbx+100], eax
	mov DWORD PTR [rbx+104], eax
	mov DWORD PTR [rbx+108], eax
	mov DWORD PTR [rbx+112], eax
	mov DWORD PTR [rbx+116], eax
	mov DWORD PTR [rbx+120], eax
	mov DWORD PTR [rbx+124], eax
	mov DWORD PTR [rbx+128], eax
	mov DWORD PTR [rbx+132], eax
	mov DWORD PTR [rbx+136], eax
	mov DWORD PTR [rbx+140], eax
	mov DWORD PTR [rbx+144], eax
	mov DWORD PTR [rbx+148], eax
	mov DWORD PTR [rbx+152], eax
	mov DWORD PTR [rbx+156], eax
	mov DWORD PTR [rbx+160], eax
	mov DWORD PTR [rbx+164], eax
	mov DWORD PTR [rbx+168], eax
	mov DWORD PTR [rbx+172], eax
	mov DWORD PTR [rbx+176], eax
	mov DWORD PTR [rbx+180], eax
	mov DWORD PTR [rbx+184], eax
	mov DWORD PTR [rbx+188], eax
	mov r14d, 0
	test r13, r13
	je 22f
24:
	movzx eax, BYTE PTR [rbp+r14*1]
	xor eax, 54
	mov BYTE PTR [rbx+r14*1+64], al
	add r14, 1
	cmp r14, r13
	jne 24b
	jmp 23f
22:
23:
	mov eax, DWORD PTR [rbx+64]
	xor eax, 1785358954
	mov DWORD PTR [r12+64], eax
	mov eax, DWORD PTR [rbx+68]
	xor eax, 1785358954
	mov DWORD PTR [r12+68], eax
	mov eax, DWORD PTR [rbx+72]
	xor eax, 1785358954
	mov DWORD PTR [r12+72], eax
	mov eax, DWORD PTR [rbx+76]
	xor eax, 1785358954
	mov DWORD PTR [r12+76], eax
	mov eax, DWORD PTR [rbx+80]
	xor eax, 1785358954
	mov DWORD PTR [r12+80], eax
	mov eax, DWORD PTR [rbx+84]
	xor eax, 1785358954
	mov DWORD PTR [r12+84], eax
	mov eax, DWORD PTR [rbx+88]
	xor eax, 1785358954
	mov DWORD PTR [r12+88], eax
	mov eax, DWORD PTR [rbx+92]
	xor eax, 1785358954
	mov DWORD PTR [r12+92], eax
	mov eax, DWORD PTR [rbx+96]
	xor eax, 1785358954
	mov DWORD PTR [r12+96], eax
	mov eax, DWORD PTR [rbx+100]
	xor eax, 1785358954
	mov DWORD PTR [r12+100], eax
	mov eax, DWORD PTR [rbx+104]
	xor eax, 1785358954
	mov DWORD PTR [r12+104], eax
	mov eax, DWORD PTR [rbx+108]
	xor eax, 1785358954
	mov DWORD PTR [r12+108], eax
	mov eax, DWORD PTR [rbx+112]
	xor eax, 1785358954
	mov DWORD PTR [r12+112], eax
	mov eax, DWORD PTR [rbx+116]
	xor eax, 1785358954
	mov DWORD PTR [r12+116], eax
	mov eax, DWORD PTR [rbx+120]
	xor eax, 1785358954
	mov DWORD PTR [r12+120], eax
	mov eax, DWORD PTR [rbx+124]
	xor eax, 1785358954
	mov DWORD PTR [r12+124], eax
	mov eax, DWORD PTR [rbx+128]
	xor eax, 1785358954
	mov DWORD PTR [r12+128], eax
	mov eax, DWORD PTR [rbx+132]
	xor eax, 1785358954
	mov DWORD PTR [r12+132], eax
	mov eax, DWORD PTR [rbx+136]
	xor eax, 1785358954
	mov DWORD PTR [r12+136], eax
	mov eax, DWORD PTR [rbx+140]
	xor eax, 1785358954
	mov DWORD PTR [r12+140], eax
	mov eax, DWORD PTR [rbx+144]
	xor eax, 1785358954
	mov DWORD PTR [r12+144], eax
	mov eax, DWORD PTR [rbx+148]
	xor eax, 1785358954
	mov DWORD PTR [r12+148], eax
	mov eax, DWORD PTR [rbx+152]
	xor eax, 1785358954
	mov DWORD PTR [r12+152], eax
	mov eax, DWORD PTR [rbx+156]
	xor eax, 1785358954
	mov DWORD PTR [r12+156], eax
	mov eax, DWORD PTR [rbx+160]
	xor eax, 1785358954
	mov DWORD PTR [r12+160], eax
	mov eax, DWORD PTR [rbx+164]
	xor eax, 1785358954
	mov DWORD PTR [r12+164], eax
	mov eax, DWORD PTR [rbx+168]
	xor eax, 1785358954
	mov DWORD PTR [r12+168], eax
	mov eax, DWORD PTR [rbx+172]
	xor eax, 1785358954
	mov DWORD PTR [r12+172], eax
	mov eax, DWORD PTR [rbx+176]
	xor eax, 1785358954
	mov DWORD PTR [r12+176], eax
	mov eax, DWORD PTR [rbx+180]
	xor eax, 1785358954
	mov DWORD PTR [r12+180], eax
	mov eax, DWORD PTR [rbx+184]
	xor eax, 1785358954
	mov DWORD PTR [r12+184], eax
	mov eax, DWORD PTR [rbx+188]
	xor eax, 1785358954
	mov DWORD PTR [r12+188], eax
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov rbx, r12
	mov rsi, r12
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov rbx, QWORD PTR [r15+1376]
	mov rbp, QWORD PTR [r15+1384]
	mov r12, QWORD PTR [r15+1392]
	mov r13, QWORD PTR [r15+1400]
	mov r14, QWORD PTR [r15+1408]
	mov r15, QWORD PTR [r15+1416]
	lea rsp, [rsp+1880]
21:
	ret
20:
	lea rsp, [rsp-3416]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+1872], rbx
	mov QWORD PTR [r8+1880], rbp
	mov QWORD PTR [r8+1888], r12
	mov QWORD PTR [r8+1896], r13
	mov QWORD PTR [r8+1904], r14
	mov QWORD PTR [r8+1912], r15
	mov r15, r8
	mov rbx, rdx
	mov rbp, rcx
	mov r12, rdi
	mov r13, rsi
	cmp rbp, 129
	jae 25f
	mov rdx, rbx
	mov rcx, rbp
	jmp 26f
25:
	mov rdi, r15
	add rdi, 2512
	call {vg_sha384_init}
	mov rdi, r15
	add rdi, 2512
	mov esi, 0
	mov rdx, rbx
	mov rcx, rbp
	mov r8, r15
	call {vg_sha512_update_scratch_shani}
	mov rdi, r15
	add rdi, 2512
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2800
	mov rcx, r15
	call {vg_sha512_finalize_scratch_shani}
	mov rdx, r15
	add rdx, 2800
	mov ecx, 48
26:
	mov rdi, r12
	mov rsi, r13
	mov r8, r15
	call {vg_hmac_sha384_init_scratch_shani}
	mov rbx, QWORD PTR [r15+1872]
	mov rbp, QWORD PTR [r15+1880]
	mov r12, QWORD PTR [r15+1888]
	mov r13, QWORD PTR [r15+1896]
	mov r14, QWORD PTR [r15+1904]
	mov r15, QWORD PTR [r15+1912]
	mov r11d, 0
	mov QWORD PTR [rsp+8], r11
	mov QWORD PTR [rsp+16], r11
	mov QWORD PTR [rsp+24], r11
	mov QWORD PTR [rsp+32], r11
	mov QWORD PTR [rsp+40], r11
	mov QWORD PTR [rsp+48], r11
	mov QWORD PTR [rsp+56], r11
	mov QWORD PTR [rsp+64], r11
	mov QWORD PTR [rsp+72], r11
	mov QWORD PTR [rsp+80], r11
	mov QWORD PTR [rsp+88], r11
	mov QWORD PTR [rsp+96], r11
	mov QWORD PTR [rsp+104], r11
	mov QWORD PTR [rsp+112], r11
	mov QWORD PTR [rsp+120], r11
	mov QWORD PTR [rsp+128], r11
	mov QWORD PTR [rsp+136], r11
	mov QWORD PTR [rsp+144], r11
	mov QWORD PTR [rsp+152], r11
	mov QWORD PTR [rsp+160], r11
	mov QWORD PTR [rsp+168], r11
	mov QWORD PTR [rsp+176], r11
	mov QWORD PTR [rsp+184], r11
	mov QWORD PTR [rsp+192], r11
	mov QWORD PTR [rsp+200], r11
	mov QWORD PTR [rsp+208], r11
	mov QWORD PTR [rsp+216], r11
	mov QWORD PTR [rsp+224], r11
	mov QWORD PTR [rsp+232], r11
	mov QWORD PTR [rsp+240], r11
	mov QWORD PTR [rsp+248], r11
	mov QWORD PTR [rsp+256], r11
	mov QWORD PTR [rsp+264], r11
	mov QWORD PTR [rsp+272], r11
	mov QWORD PTR [rsp+280], r11
	mov QWORD PTR [rsp+288], r11
	mov QWORD PTR [rsp+296], r11
	mov QWORD PTR [rsp+304], r11
	mov QWORD PTR [rsp+312], r11
	mov QWORD PTR [rsp+320], r11
	mov QWORD PTR [rsp+328], r11
	mov QWORD PTR [rsp+336], r11
	mov QWORD PTR [rsp+344], r11
	mov QWORD PTR [rsp+352], r11
	mov QWORD PTR [rsp+360], r11
	mov QWORD PTR [rsp+368], r11
	mov QWORD PTR [rsp+376], r11
	mov QWORD PTR [rsp+384], r11
	mov QWORD PTR [rsp+392], r11
	mov QWORD PTR [rsp+400], r11
	mov QWORD PTR [rsp+408], r11
	mov QWORD PTR [rsp+416], r11
	mov QWORD PTR [rsp+424], r11
	mov QWORD PTR [rsp+432], r11
	mov QWORD PTR [rsp+440], r11
	mov QWORD PTR [rsp+448], r11
	mov QWORD PTR [rsp+456], r11
	mov QWORD PTR [rsp+464], r11
	mov QWORD PTR [rsp+472], r11
	mov QWORD PTR [rsp+480], r11
	mov QWORD PTR [rsp+488], r11
	mov QWORD PTR [rsp+496], r11
	mov QWORD PTR [rsp+504], r11
	mov QWORD PTR [rsp+512], r11
	mov QWORD PTR [rsp+520], r11
	mov QWORD PTR [rsp+528], r11
	mov QWORD PTR [rsp+536], r11
	mov QWORD PTR [rsp+544], r11
	mov QWORD PTR [rsp+552], r11
	mov QWORD PTR [rsp+560], r11
	mov QWORD PTR [rsp+568], r11
	mov QWORD PTR [rsp+576], r11
	mov QWORD PTR [rsp+584], r11
	mov QWORD PTR [rsp+592], r11
	mov QWORD PTR [rsp+600], r11
	mov QWORD PTR [rsp+608], r11
	mov QWORD PTR [rsp+616], r11
	mov QWORD PTR [rsp+624], r11
	mov QWORD PTR [rsp+632], r11
	mov QWORD PTR [rsp+640], r11
	mov QWORD PTR [rsp+648], r11
	mov QWORD PTR [rsp+656], r11
	mov QWORD PTR [rsp+664], r11
	mov QWORD PTR [rsp+672], r11
	mov QWORD PTR [rsp+680], r11
	mov QWORD PTR [rsp+688], r11
	mov QWORD PTR [rsp+696], r11
	mov QWORD PTR [rsp+704], r11
	mov QWORD PTR [rsp+712], r11
	mov QWORD PTR [rsp+720], r11
	mov QWORD PTR [rsp+728], r11
	mov QWORD PTR [rsp+736], r11
	mov QWORD PTR [rsp+744], r11
	mov QWORD PTR [rsp+752], r11
	mov QWORD PTR [rsp+760], r11
	mov QWORD PTR [rsp+768], r11
	mov QWORD PTR [rsp+776], r11
	mov QWORD PTR [rsp+784], r11
	mov QWORD PTR [rsp+792], r11
	mov QWORD PTR [rsp+800], r11
	mov QWORD PTR [rsp+808], r11
	mov QWORD PTR [rsp+816], r11
	mov QWORD PTR [rsp+824], r11
	mov QWORD PTR [rsp+832], r11
	mov QWORD PTR [rsp+840], r11
	mov QWORD PTR [rsp+848], r11
	mov QWORD PTR [rsp+856], r11
	mov QWORD PTR [rsp+864], r11
	mov QWORD PTR [rsp+872], r11
	mov QWORD PTR [rsp+880], r11
	mov QWORD PTR [rsp+888], r11
	mov QWORD PTR [rsp+896], r11
	mov QWORD PTR [rsp+904], r11
	mov QWORD PTR [rsp+912], r11
	mov QWORD PTR [rsp+920], r11
	mov QWORD PTR [rsp+928], r11
	mov QWORD PTR [rsp+936], r11
	mov QWORD PTR [rsp+944], r11
	mov QWORD PTR [rsp+952], r11
	mov QWORD PTR [rsp+960], r11
	mov QWORD PTR [rsp+968], r11
	mov QWORD PTR [rsp+976], r11
	mov QWORD PTR [rsp+984], r11
	mov QWORD PTR [rsp+992], r11
	mov QWORD PTR [rsp+1000], r11
	mov QWORD PTR [rsp+1008], r11
	mov QWORD PTR [rsp+1016], r11
	mov QWORD PTR [rsp+1024], r11
	mov QWORD PTR [rsp+1032], r11
	mov QWORD PTR [rsp+1040], r11
	mov QWORD PTR [rsp+1048], r11
	mov QWORD PTR [rsp+1056], r11
	mov QWORD PTR [rsp+1064], r11
	mov QWORD PTR [rsp+1072], r11
	mov QWORD PTR [rsp+1080], r11
	mov QWORD PTR [rsp+1088], r11
	mov QWORD PTR [rsp+1096], r11
	mov QWORD PTR [rsp+1104], r11
	mov QWORD PTR [rsp+1112], r11
	mov QWORD PTR [rsp+1120], r11
	mov QWORD PTR [rsp+1128], r11
	mov QWORD PTR [rsp+1136], r11
	mov QWORD PTR [rsp+1144], r11
	mov QWORD PTR [rsp+1152], r11
	mov QWORD PTR [rsp+1160], r11
	mov QWORD PTR [rsp+1168], r11
	mov QWORD PTR [rsp+1176], r11
	mov QWORD PTR [rsp+1184], r11
	mov QWORD PTR [rsp+1192], r11
	mov QWORD PTR [rsp+1200], r11
	mov QWORD PTR [rsp+1208], r11
	mov QWORD PTR [rsp+1216], r11
	mov QWORD PTR [rsp+1224], r11
	mov QWORD PTR [rsp+1232], r11
	mov QWORD PTR [rsp+1240], r11
	mov QWORD PTR [rsp+1248], r11
	mov QWORD PTR [rsp+1256], r11
	mov QWORD PTR [rsp+1264], r11
	mov QWORD PTR [rsp+1272], r11
	mov QWORD PTR [rsp+1280], r11
	mov QWORD PTR [rsp+1288], r11
	mov QWORD PTR [rsp+1296], r11
	mov QWORD PTR [rsp+1304], r11
	mov QWORD PTR [rsp+1312], r11
	mov QWORD PTR [rsp+1320], r11
	mov QWORD PTR [rsp+1328], r11
	mov QWORD PTR [rsp+1336], r11
	mov QWORD PTR [rsp+1344], r11
	mov QWORD PTR [rsp+1352], r11
	mov QWORD PTR [rsp+1360], r11
	mov QWORD PTR [rsp+1368], r11
	mov QWORD PTR [rsp+1376], r11
	mov QWORD PTR [rsp+1384], r11
	mov QWORD PTR [rsp+1392], r11
	mov QWORD PTR [rsp+1400], r11
	mov QWORD PTR [rsp+1408], r11
	mov QWORD PTR [rsp+1416], r11
	mov QWORD PTR [rsp+1424], r11
	mov QWORD PTR [rsp+1432], r11
	mov QWORD PTR [rsp+1440], r11
	mov QWORD PTR [rsp+1448], r11
	mov QWORD PTR [rsp+1456], r11
	mov QWORD PTR [rsp+1464], r11
	mov QWORD PTR [rsp+1472], r11
	mov QWORD PTR [rsp+1480], r11
	mov QWORD PTR [rsp+1488], r11
	mov QWORD PTR [rsp+1496], r11
	mov QWORD PTR [rsp+1504], r11
	mov QWORD PTR [rsp+1512], r11
	mov QWORD PTR [rsp+1520], r11
	mov QWORD PTR [rsp+1528], r11
	mov QWORD PTR [rsp+1536], r11
	mov QWORD PTR [rsp+1544], r11
	mov QWORD PTR [rsp+1552], r11
	mov QWORD PTR [rsp+1560], r11
	mov QWORD PTR [rsp+1568], r11
	mov QWORD PTR [rsp+1576], r11
	mov QWORD PTR [rsp+1584], r11
	mov QWORD PTR [rsp+1592], r11
	mov QWORD PTR [rsp+1600], r11
	mov QWORD PTR [rsp+1608], r11
	mov QWORD PTR [rsp+1616], r11
	mov QWORD PTR [rsp+1624], r11
	mov QWORD PTR [rsp+1632], r11
	mov QWORD PTR [rsp+1640], r11
	mov QWORD PTR [rsp+1648], r11
	mov QWORD PTR [rsp+1656], r11
	mov QWORD PTR [rsp+1664], r11
	mov QWORD PTR [rsp+1672], r11
	mov QWORD PTR [rsp+1680], r11
	mov QWORD PTR [rsp+1688], r11
	mov QWORD PTR [rsp+1696], r11
	mov QWORD PTR [rsp+1704], r11
	mov QWORD PTR [rsp+1712], r11
	mov QWORD PTR [rsp+1720], r11
	mov QWORD PTR [rsp+1728], r11
	mov QWORD PTR [rsp+1736], r11
	mov QWORD PTR [rsp+1744], r11
	mov QWORD PTR [rsp+1752], r11
	mov QWORD PTR [rsp+1760], r11
	mov QWORD PTR [rsp+1768], r11
	mov QWORD PTR [rsp+1776], r11
	mov QWORD PTR [rsp+1784], r11
	mov QWORD PTR [rsp+1792], r11
	mov QWORD PTR [rsp+1800], r11
	mov QWORD PTR [rsp+1808], r11
	mov QWORD PTR [rsp+1816], r11
	mov QWORD PTR [rsp+1824], r11
	mov QWORD PTR [rsp+1832], r11
	mov QWORD PTR [rsp+1840], r11
	mov QWORD PTR [rsp+1848], r11
	mov QWORD PTR [rsp+1856], r11
	mov QWORD PTR [rsp+1864], r11
	mov QWORD PTR [rsp+1872], r11
	mov QWORD PTR [rsp+1880], r11
	mov QWORD PTR [rsp+1888], r11
	mov QWORD PTR [rsp+1896], r11
	mov QWORD PTR [rsp+1904], r11
	mov QWORD PTR [rsp+1912], r11
	mov QWORD PTR [rsp+1920], r11
	mov QWORD PTR [rsp+1928], r11
	mov QWORD PTR [rsp+1936], r11
	mov QWORD PTR [rsp+1944], r11
	mov QWORD PTR [rsp+1952], r11
	mov QWORD PTR [rsp+1960], r11
	mov QWORD PTR [rsp+1968], r11
	mov QWORD PTR [rsp+1976], r11
	mov QWORD PTR [rsp+1984], r11
	mov QWORD PTR [rsp+1992], r11
	mov QWORD PTR [rsp+2000], r11
	mov QWORD PTR [rsp+2008], r11
	mov QWORD PTR [rsp+2016], r11
	mov QWORD PTR [rsp+2024], r11
	mov QWORD PTR [rsp+2032], r11
	mov QWORD PTR [rsp+2040], r11
	mov QWORD PTR [rsp+2048], r11
	mov QWORD PTR [rsp+2056], r11
	mov QWORD PTR [rsp+2064], r11
	mov QWORD PTR [rsp+2072], r11
	mov QWORD PTR [rsp+2080], r11
	mov QWORD PTR [rsp+2088], r11
	mov QWORD PTR [rsp+2096], r11
	mov QWORD PTR [rsp+2104], r11
	mov QWORD PTR [rsp+2112], r11
	mov QWORD PTR [rsp+2120], r11
	mov QWORD PTR [rsp+2128], r11
	mov QWORD PTR [rsp+2136], r11
	mov QWORD PTR [rsp+2144], r11
	mov QWORD PTR [rsp+2152], r11
	mov QWORD PTR [rsp+2160], r11
	mov QWORD PTR [rsp+2168], r11
	mov QWORD PTR [rsp+2176], r11
	mov QWORD PTR [rsp+2184], r11
	mov QWORD PTR [rsp+2192], r11
	mov QWORD PTR [rsp+2200], r11
	mov QWORD PTR [rsp+2208], r11
	mov QWORD PTR [rsp+2216], r11
	mov QWORD PTR [rsp+2224], r11
	mov QWORD PTR [rsp+2232], r11
	mov QWORD PTR [rsp+2240], r11
	mov QWORD PTR [rsp+2248], r11
	mov QWORD PTR [rsp+2256], r11
	mov QWORD PTR [rsp+2264], r11
	mov QWORD PTR [rsp+2272], r11
	mov QWORD PTR [rsp+2280], r11
	mov QWORD PTR [rsp+2288], r11
	mov QWORD PTR [rsp+2296], r11
	mov QWORD PTR [rsp+2304], r11
	mov QWORD PTR [rsp+2312], r11
	mov QWORD PTR [rsp+2320], r11
	mov QWORD PTR [rsp+2328], r11
	mov QWORD PTR [rsp+2336], r11
	mov QWORD PTR [rsp+2344], r11
	mov QWORD PTR [rsp+2352], r11
	mov QWORD PTR [rsp+2360], r11
	mov QWORD PTR [rsp+2368], r11
	mov QWORD PTR [rsp+2376], r11
	mov QWORD PTR [rsp+2384], r11
	mov QWORD PTR [rsp+2392], r11
	mov QWORD PTR [rsp+2400], r11
	mov QWORD PTR [rsp+2408], r11
	mov QWORD PTR [rsp+2416], r11
	mov QWORD PTR [rsp+2424], r11
	mov QWORD PTR [rsp+2432], r11
	mov QWORD PTR [rsp+2440], r11
	mov QWORD PTR [rsp+2448], r11
	mov QWORD PTR [rsp+2456], r11
	mov QWORD PTR [rsp+2464], r11
	mov QWORD PTR [rsp+2472], r11
	mov QWORD PTR [rsp+2480], r11
	mov QWORD PTR [rsp+2488], r11
	mov QWORD PTR [rsp+2496], r11
	mov QWORD PTR [rsp+2504], r11
	mov QWORD PTR [rsp+2512], r11
	mov QWORD PTR [rsp+2520], r11
	mov QWORD PTR [rsp+2528], r11
	mov QWORD PTR [rsp+2536], r11
	mov QWORD PTR [rsp+2544], r11
	mov QWORD PTR [rsp+2552], r11
	mov QWORD PTR [rsp+2560], r11
	mov QWORD PTR [rsp+2568], r11
	mov QWORD PTR [rsp+2576], r11
	mov QWORD PTR [rsp+2584], r11
	mov QWORD PTR [rsp+2592], r11
	mov QWORD PTR [rsp+2600], r11
	mov QWORD PTR [rsp+2608], r11
	mov QWORD PTR [rsp+2616], r11
	mov QWORD PTR [rsp+2624], r11
	mov QWORD PTR [rsp+2632], r11
	mov QWORD PTR [rsp+2640], r11
	mov QWORD PTR [rsp+2648], r11
	mov QWORD PTR [rsp+2656], r11
	mov QWORD PTR [rsp+2664], r11
	mov QWORD PTR [rsp+2672], r11
	mov QWORD PTR [rsp+2680], r11
	mov QWORD PTR [rsp+2688], r11
	mov QWORD PTR [rsp+2696], r11
	mov QWORD PTR [rsp+2704], r11
	mov QWORD PTR [rsp+2712], r11
	mov QWORD PTR [rsp+2720], r11
	mov QWORD PTR [rsp+2728], r11
	mov QWORD PTR [rsp+2736], r11
	mov QWORD PTR [rsp+2744], r11
	mov QWORD PTR [rsp+2752], r11
	mov QWORD PTR [rsp+2760], r11
	mov QWORD PTR [rsp+2768], r11
	mov QWORD PTR [rsp+2776], r11
	mov QWORD PTR [rsp+2784], r11
	mov QWORD PTR [rsp+2792], r11
	mov QWORD PTR [rsp+2800], r11
	mov QWORD PTR [rsp+2808], r11
	mov QWORD PTR [rsp+2816], r11
	mov QWORD PTR [rsp+2824], r11
	mov QWORD PTR [rsp+2832], r11
	mov QWORD PTR [rsp+2840], r11
	mov QWORD PTR [rsp+2848], r11
	mov QWORD PTR [rsp+2856], r11
	mov QWORD PTR [rsp+2864], r11
	mov QWORD PTR [rsp+2872], r11
	mov QWORD PTR [rsp+2880], r11
	mov QWORD PTR [rsp+2888], r11
	mov QWORD PTR [rsp+2896], r11
	mov QWORD PTR [rsp+2904], r11
	mov QWORD PTR [rsp+2912], r11
	mov QWORD PTR [rsp+2920], r11
	mov QWORD PTR [rsp+2928], r11
	mov QWORD PTR [rsp+2936], r11
	mov QWORD PTR [rsp+2944], r11
	mov QWORD PTR [rsp+2952], r11
	mov QWORD PTR [rsp+2960], r11
	mov QWORD PTR [rsp+2968], r11
	mov QWORD PTR [rsp+2976], r11
	mov QWORD PTR [rsp+2984], r11
	mov QWORD PTR [rsp+2992], r11
	mov QWORD PTR [rsp+3000], r11
	mov QWORD PTR [rsp+3008], r11
	mov QWORD PTR [rsp+3016], r11
	mov QWORD PTR [rsp+3024], r11
	mov QWORD PTR [rsp+3032], r11
	mov QWORD PTR [rsp+3040], r11
	mov QWORD PTR [rsp+3048], r11
	mov QWORD PTR [rsp+3056], r11
	mov QWORD PTR [rsp+3064], r11
	mov QWORD PTR [rsp+3072], r11
	mov QWORD PTR [rsp+3080], r11
	mov QWORD PTR [rsp+3088], r11
	mov QWORD PTR [rsp+3096], r11
	mov QWORD PTR [rsp+3104], r11
	mov QWORD PTR [rsp+3112], r11
	mov QWORD PTR [rsp+3120], r11
	mov QWORD PTR [rsp+3128], r11
	mov QWORD PTR [rsp+3136], r11
	mov QWORD PTR [rsp+3144], r11
	mov QWORD PTR [rsp+3152], r11
	mov QWORD PTR [rsp+3160], r11
	mov QWORD PTR [rsp+3168], r11
	mov QWORD PTR [rsp+3176], r11
	mov QWORD PTR [rsp+3184], r11
	mov QWORD PTR [rsp+3192], r11
	mov QWORD PTR [rsp+3200], r11
	mov QWORD PTR [rsp+3208], r11
	mov QWORD PTR [rsp+3216], r11
	mov QWORD PTR [rsp+3224], r11
	mov QWORD PTR [rsp+3232], r11
	mov QWORD PTR [rsp+3240], r11
	mov QWORD PTR [rsp+3248], r11
	mov QWORD PTR [rsp+3256], r11
	mov QWORD PTR [rsp+3264], r11
	mov QWORD PTR [rsp+3272], r11
	mov QWORD PTR [rsp+3280], r11
	mov QWORD PTR [rsp+3288], r11
	mov QWORD PTR [rsp+3296], r11
	mov QWORD PTR [rsp+3304], r11
	mov QWORD PTR [rsp+3312], r11
	mov QWORD PTR [rsp+3320], r11
	mov QWORD PTR [rsp+3328], r11
	mov QWORD PTR [rsp+3336], r11
	mov QWORD PTR [rsp+3344], r11
	mov QWORD PTR [rsp+3352], r11
	mov QWORD PTR [rsp+3360], r11
	mov QWORD PTR [rsp+3368], r11
	mov QWORD PTR [rsp+3376], r11
	mov QWORD PTR [rsp+3384], r11
	mov QWORD PTR [rsp+3392], r11
	mov QWORD PTR [rsp+3400], r11
	mov QWORD PTR [rsp+3408], r11
	lea rsp, [rsp+3416]
	jmp 21b
	.p2align 6

vg_hmac_sha384_finalize_shani:
	lea rsp, [rsp-1880]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+1376], rbx
	mov QWORD PTR [r8+1384], rbp
	mov QWORD PTR [r8+1392], r12
	mov QWORD PTR [r8+1400], r13
	mov QWORD PTR [r8+1408], r14
	mov QWORD PTR [r8+1416], r15
	mov rbx, rdi
	mov r12, rsi
	mov r13, rcx
	mov r15, r8
	mov rsi, rdx
	mov rdx, r15
	add rdx, 1424
	mov rcx, r15
	call {vg_sha512_finalize_scratch_shani}
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu XMMWORD PTR [rbx], xmm0
	movdqu xmm0, XMMWORD PTR [r12+16]
	movdqu XMMWORD PTR [rbx+16], xmm0
	movdqu xmm0, XMMWORD PTR [r12+32]
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu xmm0, XMMWORD PTR [r12+48]
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu xmm0, XMMWORD PTR [r15+1424]
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu xmm0, XMMWORD PTR [r15+1440]
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu xmm0, XMMWORD PTR [r15+1456]
	movdqu XMMWORD PTR [rbx+96], xmm0
	mov rbp, rbx
	add rbp, 64
	mov eax, 128
	movq xmm1, rax
	movdqu XMMWORD PTR [rbp+48], xmm1
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbp+64], xmm0
	movdqu XMMWORD PTR [rbp+80], xmm0
	movdqu XMMWORD PTR [rbp+96], xmm0
	mov r12d, 176
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	movdqu XMMWORD PTR [rbp+112], xmm7
	mov rsi, rbp
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_shani}
	mov rbx, rdi
	mov r15, rcx
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	mov rax, QWORD PTR [rbx+32]
	bswap rax
	mov QWORD PTR [rbp+32], rax
	mov rax, QWORD PTR [rbx+40]
	bswap rax
	mov QWORD PTR [rbp+40], rax
	mov rax, QWORD PTR [rbx+48]
	bswap rax
	mov QWORD PTR [rbp+48], rax
	mov rax, QWORD PTR [rbx+56]
	bswap rax
	mov QWORD PTR [rbp+56], rax
	movdqu xmm0, XMMWORD PTR [rbp]
	movdqu XMMWORD PTR [r13], xmm0
	movdqu xmm0, XMMWORD PTR [rbp+16]
	movdqu XMMWORD PTR [r13+16], xmm0
	movdqu xmm0, XMMWORD PTR [rbp+32]
	movdqu XMMWORD PTR [r13+32], xmm0
	mov rbx, QWORD PTR [r15+1376]
	mov rbp, QWORD PTR [r15+1384]
	mov r12, QWORD PTR [r15+1392]
	mov r13, QWORD PTR [r15+1400]
	mov r14, QWORD PTR [r15+1408]
	mov r15, QWORD PTR [r15+1416]
	lea rsp, [rsp+1880]
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
	lea rsp, [rsp-1896]
	movdqu XMMWORD PTR [rsp+1512], xmm0
	movdqu XMMWORD PTR [rsp+1496], xmm0
	movdqu XMMWORD PTR [rsp+1480], xmm0
	movdqu XMMWORD PTR [rsp+1464], xmm0
	movdqu XMMWORD PTR [rsp+1448], xmm0
	lea rsp, [rsp+1896]
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

vg_hmac_sha384_init_avx512:
	cmp rcx, 129
	jae 20f
	lea rsp, [rsp-1880]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+1376], rbx
	mov QWORD PTR [r8+1384], rbp
	mov QWORD PTR [r8+1392], r12
	mov QWORD PTR [r8+1400], r13
	mov QWORD PTR [r8+1408], r14
	mov QWORD PTR [r8+1416], r15
	mov rbx, rdi
	mov r12, rsi
	mov r15, r8
	mov rbp, rdx
	mov r13, rcx
	mov rdi, rbx
	call {vg_sha384_init}
	mov rdi, r12
	call {vg_sha384_init}
	mov eax, 909522486
	mov DWORD PTR [rbx+64], eax
	mov DWORD PTR [rbx+68], eax
	mov DWORD PTR [rbx+72], eax
	mov DWORD PTR [rbx+76], eax
	mov DWORD PTR [rbx+80], eax
	mov DWORD PTR [rbx+84], eax
	mov DWORD PTR [rbx+88], eax
	mov DWORD PTR [rbx+92], eax
	mov DWORD PTR [rbx+96], eax
	mov DWORD PTR [rbx+100], eax
	mov DWORD PTR [rbx+104], eax
	mov DWORD PTR [rbx+108], eax
	mov DWORD PTR [rbx+112], eax
	mov DWORD PTR [rbx+116], eax
	mov DWORD PTR [rbx+120], eax
	mov DWORD PTR [rbx+124], eax
	mov DWORD PTR [rbx+128], eax
	mov DWORD PTR [rbx+132], eax
	mov DWORD PTR [rbx+136], eax
	mov DWORD PTR [rbx+140], eax
	mov DWORD PTR [rbx+144], eax
	mov DWORD PTR [rbx+148], eax
	mov DWORD PTR [rbx+152], eax
	mov DWORD PTR [rbx+156], eax
	mov DWORD PTR [rbx+160], eax
	mov DWORD PTR [rbx+164], eax
	mov DWORD PTR [rbx+168], eax
	mov DWORD PTR [rbx+172], eax
	mov DWORD PTR [rbx+176], eax
	mov DWORD PTR [rbx+180], eax
	mov DWORD PTR [rbx+184], eax
	mov DWORD PTR [rbx+188], eax
	mov r14d, 0
	test r13, r13
	je 22f
24:
	movzx eax, BYTE PTR [rbp+r14*1]
	xor eax, 54
	mov BYTE PTR [rbx+r14*1+64], al
	add r14, 1
	cmp r14, r13
	jne 24b
	jmp 23f
22:
23:
	mov eax, DWORD PTR [rbx+64]
	xor eax, 1785358954
	mov DWORD PTR [r12+64], eax
	mov eax, DWORD PTR [rbx+68]
	xor eax, 1785358954
	mov DWORD PTR [r12+68], eax
	mov eax, DWORD PTR [rbx+72]
	xor eax, 1785358954
	mov DWORD PTR [r12+72], eax
	mov eax, DWORD PTR [rbx+76]
	xor eax, 1785358954
	mov DWORD PTR [r12+76], eax
	mov eax, DWORD PTR [rbx+80]
	xor eax, 1785358954
	mov DWORD PTR [r12+80], eax
	mov eax, DWORD PTR [rbx+84]
	xor eax, 1785358954
	mov DWORD PTR [r12+84], eax
	mov eax, DWORD PTR [rbx+88]
	xor eax, 1785358954
	mov DWORD PTR [r12+88], eax
	mov eax, DWORD PTR [rbx+92]
	xor eax, 1785358954
	mov DWORD PTR [r12+92], eax
	mov eax, DWORD PTR [rbx+96]
	xor eax, 1785358954
	mov DWORD PTR [r12+96], eax
	mov eax, DWORD PTR [rbx+100]
	xor eax, 1785358954
	mov DWORD PTR [r12+100], eax
	mov eax, DWORD PTR [rbx+104]
	xor eax, 1785358954
	mov DWORD PTR [r12+104], eax
	mov eax, DWORD PTR [rbx+108]
	xor eax, 1785358954
	mov DWORD PTR [r12+108], eax
	mov eax, DWORD PTR [rbx+112]
	xor eax, 1785358954
	mov DWORD PTR [r12+112], eax
	mov eax, DWORD PTR [rbx+116]
	xor eax, 1785358954
	mov DWORD PTR [r12+116], eax
	mov eax, DWORD PTR [rbx+120]
	xor eax, 1785358954
	mov DWORD PTR [r12+120], eax
	mov eax, DWORD PTR [rbx+124]
	xor eax, 1785358954
	mov DWORD PTR [r12+124], eax
	mov eax, DWORD PTR [rbx+128]
	xor eax, 1785358954
	mov DWORD PTR [r12+128], eax
	mov eax, DWORD PTR [rbx+132]
	xor eax, 1785358954
	mov DWORD PTR [r12+132], eax
	mov eax, DWORD PTR [rbx+136]
	xor eax, 1785358954
	mov DWORD PTR [r12+136], eax
	mov eax, DWORD PTR [rbx+140]
	xor eax, 1785358954
	mov DWORD PTR [r12+140], eax
	mov eax, DWORD PTR [rbx+144]
	xor eax, 1785358954
	mov DWORD PTR [r12+144], eax
	mov eax, DWORD PTR [rbx+148]
	xor eax, 1785358954
	mov DWORD PTR [r12+148], eax
	mov eax, DWORD PTR [rbx+152]
	xor eax, 1785358954
	mov DWORD PTR [r12+152], eax
	mov eax, DWORD PTR [rbx+156]
	xor eax, 1785358954
	mov DWORD PTR [r12+156], eax
	mov eax, DWORD PTR [rbx+160]
	xor eax, 1785358954
	mov DWORD PTR [r12+160], eax
	mov eax, DWORD PTR [rbx+164]
	xor eax, 1785358954
	mov DWORD PTR [r12+164], eax
	mov eax, DWORD PTR [rbx+168]
	xor eax, 1785358954
	mov DWORD PTR [r12+168], eax
	mov eax, DWORD PTR [rbx+172]
	xor eax, 1785358954
	mov DWORD PTR [r12+172], eax
	mov eax, DWORD PTR [rbx+176]
	xor eax, 1785358954
	mov DWORD PTR [r12+176], eax
	mov eax, DWORD PTR [rbx+180]
	xor eax, 1785358954
	mov DWORD PTR [r12+180], eax
	mov eax, DWORD PTR [rbx+184]
	xor eax, 1785358954
	mov DWORD PTR [r12+184], eax
	mov eax, DWORD PTR [rbx+188]
	xor eax, 1785358954
	mov DWORD PTR [r12+188], eax
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov rdx, r12
	mov rcx, r12
	add rcx, 64
	mov r8, r15
	call {vg_sha512_compress2_avx512}
	mov rbx, QWORD PTR [r15+1376]
	mov rbp, QWORD PTR [r15+1384]
	mov r12, QWORD PTR [r15+1392]
	mov r13, QWORD PTR [r15+1400]
	mov r14, QWORD PTR [r15+1408]
	mov r15, QWORD PTR [r15+1416]
	lea rsp, [rsp+1880]
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
	lea rsp, [rsp-1896]
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
	lea rsp, [rsp+1896]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
21:
	ret
20:
	lea rsp, [rsp-3416]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+1872], rbx
	mov QWORD PTR [r8+1880], rbp
	mov QWORD PTR [r8+1888], r12
	mov QWORD PTR [r8+1896], r13
	mov QWORD PTR [r8+1904], r14
	mov QWORD PTR [r8+1912], r15
	mov r15, r8
	mov rbx, rdx
	mov rbp, rcx
	mov r12, rdi
	mov r13, rsi
	cmp rbp, 129
	jae 25f
	mov rdx, rbx
	mov rcx, rbp
	jmp 26f
25:
	mov rdi, r15
	add rdi, 2512
	call {vg_sha384_init}
	mov rdi, r15
	add rdi, 2512
	mov esi, 0
	mov rdx, rbx
	mov rcx, rbp
	mov r8, r15
	call {vg_sha512_update_scratch_avx2}
	mov rdi, r15
	add rdi, 2512
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2800
	mov rcx, r15
	call {vg_sha512_finalize_scratch_avx2}
	mov rdx, r15
	add rdx, 2800
	mov ecx, 48
26:
	mov rdi, r12
	mov rsi, r13
	mov r8, r15
	call {vg_hmac_sha384_init_scratch_avx512}
	mov rbx, QWORD PTR [r15+1872]
	mov rbp, QWORD PTR [r15+1880]
	mov r12, QWORD PTR [r15+1888]
	mov r13, QWORD PTR [r15+1896]
	mov r14, QWORD PTR [r15+1904]
	mov r15, QWORD PTR [r15+1912]
	mov r11d, 0
	mov QWORD PTR [rsp+8], r11
	mov QWORD PTR [rsp+16], r11
	mov QWORD PTR [rsp+24], r11
	mov QWORD PTR [rsp+32], r11
	mov QWORD PTR [rsp+40], r11
	mov QWORD PTR [rsp+48], r11
	mov QWORD PTR [rsp+56], r11
	mov QWORD PTR [rsp+64], r11
	mov QWORD PTR [rsp+72], r11
	mov QWORD PTR [rsp+80], r11
	mov QWORD PTR [rsp+88], r11
	mov QWORD PTR [rsp+96], r11
	mov QWORD PTR [rsp+104], r11
	mov QWORD PTR [rsp+112], r11
	mov QWORD PTR [rsp+120], r11
	mov QWORD PTR [rsp+128], r11
	mov QWORD PTR [rsp+136], r11
	mov QWORD PTR [rsp+144], r11
	mov QWORD PTR [rsp+152], r11
	mov QWORD PTR [rsp+160], r11
	mov QWORD PTR [rsp+168], r11
	mov QWORD PTR [rsp+176], r11
	mov QWORD PTR [rsp+184], r11
	mov QWORD PTR [rsp+192], r11
	mov QWORD PTR [rsp+200], r11
	mov QWORD PTR [rsp+208], r11
	mov QWORD PTR [rsp+216], r11
	mov QWORD PTR [rsp+224], r11
	mov QWORD PTR [rsp+232], r11
	mov QWORD PTR [rsp+240], r11
	mov QWORD PTR [rsp+248], r11
	mov QWORD PTR [rsp+256], r11
	mov QWORD PTR [rsp+264], r11
	mov QWORD PTR [rsp+272], r11
	mov QWORD PTR [rsp+280], r11
	mov QWORD PTR [rsp+288], r11
	mov QWORD PTR [rsp+296], r11
	mov QWORD PTR [rsp+304], r11
	mov QWORD PTR [rsp+312], r11
	mov QWORD PTR [rsp+320], r11
	mov QWORD PTR [rsp+328], r11
	mov QWORD PTR [rsp+336], r11
	mov QWORD PTR [rsp+344], r11
	mov QWORD PTR [rsp+352], r11
	mov QWORD PTR [rsp+360], r11
	mov QWORD PTR [rsp+368], r11
	mov QWORD PTR [rsp+376], r11
	mov QWORD PTR [rsp+384], r11
	mov QWORD PTR [rsp+392], r11
	mov QWORD PTR [rsp+400], r11
	mov QWORD PTR [rsp+408], r11
	mov QWORD PTR [rsp+416], r11
	mov QWORD PTR [rsp+424], r11
	mov QWORD PTR [rsp+432], r11
	mov QWORD PTR [rsp+440], r11
	mov QWORD PTR [rsp+448], r11
	mov QWORD PTR [rsp+456], r11
	mov QWORD PTR [rsp+464], r11
	mov QWORD PTR [rsp+472], r11
	mov QWORD PTR [rsp+480], r11
	mov QWORD PTR [rsp+488], r11
	mov QWORD PTR [rsp+496], r11
	mov QWORD PTR [rsp+504], r11
	mov QWORD PTR [rsp+512], r11
	mov QWORD PTR [rsp+520], r11
	mov QWORD PTR [rsp+528], r11
	mov QWORD PTR [rsp+536], r11
	mov QWORD PTR [rsp+544], r11
	mov QWORD PTR [rsp+552], r11
	mov QWORD PTR [rsp+560], r11
	mov QWORD PTR [rsp+568], r11
	mov QWORD PTR [rsp+576], r11
	mov QWORD PTR [rsp+584], r11
	mov QWORD PTR [rsp+592], r11
	mov QWORD PTR [rsp+600], r11
	mov QWORD PTR [rsp+608], r11
	mov QWORD PTR [rsp+616], r11
	mov QWORD PTR [rsp+624], r11
	mov QWORD PTR [rsp+632], r11
	mov QWORD PTR [rsp+640], r11
	mov QWORD PTR [rsp+648], r11
	mov QWORD PTR [rsp+656], r11
	mov QWORD PTR [rsp+664], r11
	mov QWORD PTR [rsp+672], r11
	mov QWORD PTR [rsp+680], r11
	mov QWORD PTR [rsp+688], r11
	mov QWORD PTR [rsp+696], r11
	mov QWORD PTR [rsp+704], r11
	mov QWORD PTR [rsp+712], r11
	mov QWORD PTR [rsp+720], r11
	mov QWORD PTR [rsp+728], r11
	mov QWORD PTR [rsp+736], r11
	mov QWORD PTR [rsp+744], r11
	mov QWORD PTR [rsp+752], r11
	mov QWORD PTR [rsp+760], r11
	mov QWORD PTR [rsp+768], r11
	mov QWORD PTR [rsp+776], r11
	mov QWORD PTR [rsp+784], r11
	mov QWORD PTR [rsp+792], r11
	mov QWORD PTR [rsp+800], r11
	mov QWORD PTR [rsp+808], r11
	mov QWORD PTR [rsp+816], r11
	mov QWORD PTR [rsp+824], r11
	mov QWORD PTR [rsp+832], r11
	mov QWORD PTR [rsp+840], r11
	mov QWORD PTR [rsp+848], r11
	mov QWORD PTR [rsp+856], r11
	mov QWORD PTR [rsp+864], r11
	mov QWORD PTR [rsp+872], r11
	mov QWORD PTR [rsp+880], r11
	mov QWORD PTR [rsp+888], r11
	mov QWORD PTR [rsp+896], r11
	mov QWORD PTR [rsp+904], r11
	mov QWORD PTR [rsp+912], r11
	mov QWORD PTR [rsp+920], r11
	mov QWORD PTR [rsp+928], r11
	mov QWORD PTR [rsp+936], r11
	mov QWORD PTR [rsp+944], r11
	mov QWORD PTR [rsp+952], r11
	mov QWORD PTR [rsp+960], r11
	mov QWORD PTR [rsp+968], r11
	mov QWORD PTR [rsp+976], r11
	mov QWORD PTR [rsp+984], r11
	mov QWORD PTR [rsp+992], r11
	mov QWORD PTR [rsp+1000], r11
	mov QWORD PTR [rsp+1008], r11
	mov QWORD PTR [rsp+1016], r11
	mov QWORD PTR [rsp+1024], r11
	mov QWORD PTR [rsp+1032], r11
	mov QWORD PTR [rsp+1040], r11
	mov QWORD PTR [rsp+1048], r11
	mov QWORD PTR [rsp+1056], r11
	mov QWORD PTR [rsp+1064], r11
	mov QWORD PTR [rsp+1072], r11
	mov QWORD PTR [rsp+1080], r11
	mov QWORD PTR [rsp+1088], r11
	mov QWORD PTR [rsp+1096], r11
	mov QWORD PTR [rsp+1104], r11
	mov QWORD PTR [rsp+1112], r11
	mov QWORD PTR [rsp+1120], r11
	mov QWORD PTR [rsp+1128], r11
	mov QWORD PTR [rsp+1136], r11
	mov QWORD PTR [rsp+1144], r11
	mov QWORD PTR [rsp+1152], r11
	mov QWORD PTR [rsp+1160], r11
	mov QWORD PTR [rsp+1168], r11
	mov QWORD PTR [rsp+1176], r11
	mov QWORD PTR [rsp+1184], r11
	mov QWORD PTR [rsp+1192], r11
	mov QWORD PTR [rsp+1200], r11
	mov QWORD PTR [rsp+1208], r11
	mov QWORD PTR [rsp+1216], r11
	mov QWORD PTR [rsp+1224], r11
	mov QWORD PTR [rsp+1232], r11
	mov QWORD PTR [rsp+1240], r11
	mov QWORD PTR [rsp+1248], r11
	mov QWORD PTR [rsp+1256], r11
	mov QWORD PTR [rsp+1264], r11
	mov QWORD PTR [rsp+1272], r11
	mov QWORD PTR [rsp+1280], r11
	mov QWORD PTR [rsp+1288], r11
	mov QWORD PTR [rsp+1296], r11
	mov QWORD PTR [rsp+1304], r11
	mov QWORD PTR [rsp+1312], r11
	mov QWORD PTR [rsp+1320], r11
	mov QWORD PTR [rsp+1328], r11
	mov QWORD PTR [rsp+1336], r11
	mov QWORD PTR [rsp+1344], r11
	mov QWORD PTR [rsp+1352], r11
	mov QWORD PTR [rsp+1360], r11
	mov QWORD PTR [rsp+1368], r11
	mov QWORD PTR [rsp+1376], r11
	mov QWORD PTR [rsp+1384], r11
	mov QWORD PTR [rsp+1392], r11
	mov QWORD PTR [rsp+1400], r11
	mov QWORD PTR [rsp+1408], r11
	mov QWORD PTR [rsp+1416], r11
	mov QWORD PTR [rsp+1424], r11
	mov QWORD PTR [rsp+1432], r11
	mov QWORD PTR [rsp+1440], r11
	mov QWORD PTR [rsp+1448], r11
	mov QWORD PTR [rsp+1456], r11
	mov QWORD PTR [rsp+1464], r11
	mov QWORD PTR [rsp+1472], r11
	mov QWORD PTR [rsp+1480], r11
	mov QWORD PTR [rsp+1488], r11
	mov QWORD PTR [rsp+1496], r11
	mov QWORD PTR [rsp+1504], r11
	mov QWORD PTR [rsp+1512], r11
	mov QWORD PTR [rsp+1520], r11
	mov QWORD PTR [rsp+1528], r11
	mov QWORD PTR [rsp+1536], r11
	mov QWORD PTR [rsp+1544], r11
	mov QWORD PTR [rsp+1552], r11
	mov QWORD PTR [rsp+1560], r11
	mov QWORD PTR [rsp+1568], r11
	mov QWORD PTR [rsp+1576], r11
	mov QWORD PTR [rsp+1584], r11
	mov QWORD PTR [rsp+1592], r11
	mov QWORD PTR [rsp+1600], r11
	mov QWORD PTR [rsp+1608], r11
	mov QWORD PTR [rsp+1616], r11
	mov QWORD PTR [rsp+1624], r11
	mov QWORD PTR [rsp+1632], r11
	mov QWORD PTR [rsp+1640], r11
	mov QWORD PTR [rsp+1648], r11
	mov QWORD PTR [rsp+1656], r11
	mov QWORD PTR [rsp+1664], r11
	mov QWORD PTR [rsp+1672], r11
	mov QWORD PTR [rsp+1680], r11
	mov QWORD PTR [rsp+1688], r11
	mov QWORD PTR [rsp+1696], r11
	mov QWORD PTR [rsp+1704], r11
	mov QWORD PTR [rsp+1712], r11
	mov QWORD PTR [rsp+1720], r11
	mov QWORD PTR [rsp+1728], r11
	mov QWORD PTR [rsp+1736], r11
	mov QWORD PTR [rsp+1744], r11
	mov QWORD PTR [rsp+1752], r11
	mov QWORD PTR [rsp+1760], r11
	mov QWORD PTR [rsp+1768], r11
	mov QWORD PTR [rsp+1776], r11
	mov QWORD PTR [rsp+1784], r11
	mov QWORD PTR [rsp+1792], r11
	mov QWORD PTR [rsp+1800], r11
	mov QWORD PTR [rsp+1808], r11
	mov QWORD PTR [rsp+1816], r11
	mov QWORD PTR [rsp+1824], r11
	mov QWORD PTR [rsp+1832], r11
	mov QWORD PTR [rsp+1840], r11
	mov QWORD PTR [rsp+1848], r11
	mov QWORD PTR [rsp+1856], r11
	mov QWORD PTR [rsp+1864], r11
	mov QWORD PTR [rsp+1872], r11
	mov QWORD PTR [rsp+1880], r11
	mov QWORD PTR [rsp+1888], r11
	mov QWORD PTR [rsp+1896], r11
	mov QWORD PTR [rsp+1904], r11
	mov QWORD PTR [rsp+1912], r11
	mov QWORD PTR [rsp+1920], r11
	mov QWORD PTR [rsp+1928], r11
	mov QWORD PTR [rsp+1936], r11
	mov QWORD PTR [rsp+1944], r11
	mov QWORD PTR [rsp+1952], r11
	mov QWORD PTR [rsp+1960], r11
	mov QWORD PTR [rsp+1968], r11
	mov QWORD PTR [rsp+1976], r11
	mov QWORD PTR [rsp+1984], r11
	mov QWORD PTR [rsp+1992], r11
	mov QWORD PTR [rsp+2000], r11
	mov QWORD PTR [rsp+2008], r11
	mov QWORD PTR [rsp+2016], r11
	mov QWORD PTR [rsp+2024], r11
	mov QWORD PTR [rsp+2032], r11
	mov QWORD PTR [rsp+2040], r11
	mov QWORD PTR [rsp+2048], r11
	mov QWORD PTR [rsp+2056], r11
	mov QWORD PTR [rsp+2064], r11
	mov QWORD PTR [rsp+2072], r11
	mov QWORD PTR [rsp+2080], r11
	mov QWORD PTR [rsp+2088], r11
	mov QWORD PTR [rsp+2096], r11
	mov QWORD PTR [rsp+2104], r11
	mov QWORD PTR [rsp+2112], r11
	mov QWORD PTR [rsp+2120], r11
	mov QWORD PTR [rsp+2128], r11
	mov QWORD PTR [rsp+2136], r11
	mov QWORD PTR [rsp+2144], r11
	mov QWORD PTR [rsp+2152], r11
	mov QWORD PTR [rsp+2160], r11
	mov QWORD PTR [rsp+2168], r11
	mov QWORD PTR [rsp+2176], r11
	mov QWORD PTR [rsp+2184], r11
	mov QWORD PTR [rsp+2192], r11
	mov QWORD PTR [rsp+2200], r11
	mov QWORD PTR [rsp+2208], r11
	mov QWORD PTR [rsp+2216], r11
	mov QWORD PTR [rsp+2224], r11
	mov QWORD PTR [rsp+2232], r11
	mov QWORD PTR [rsp+2240], r11
	mov QWORD PTR [rsp+2248], r11
	mov QWORD PTR [rsp+2256], r11
	mov QWORD PTR [rsp+2264], r11
	mov QWORD PTR [rsp+2272], r11
	mov QWORD PTR [rsp+2280], r11
	mov QWORD PTR [rsp+2288], r11
	mov QWORD PTR [rsp+2296], r11
	mov QWORD PTR [rsp+2304], r11
	mov QWORD PTR [rsp+2312], r11
	mov QWORD PTR [rsp+2320], r11
	mov QWORD PTR [rsp+2328], r11
	mov QWORD PTR [rsp+2336], r11
	mov QWORD PTR [rsp+2344], r11
	mov QWORD PTR [rsp+2352], r11
	mov QWORD PTR [rsp+2360], r11
	mov QWORD PTR [rsp+2368], r11
	mov QWORD PTR [rsp+2376], r11
	mov QWORD PTR [rsp+2384], r11
	mov QWORD PTR [rsp+2392], r11
	mov QWORD PTR [rsp+2400], r11
	mov QWORD PTR [rsp+2408], r11
	mov QWORD PTR [rsp+2416], r11
	mov QWORD PTR [rsp+2424], r11
	mov QWORD PTR [rsp+2432], r11
	mov QWORD PTR [rsp+2440], r11
	mov QWORD PTR [rsp+2448], r11
	mov QWORD PTR [rsp+2456], r11
	mov QWORD PTR [rsp+2464], r11
	mov QWORD PTR [rsp+2472], r11
	mov QWORD PTR [rsp+2480], r11
	mov QWORD PTR [rsp+2488], r11
	mov QWORD PTR [rsp+2496], r11
	mov QWORD PTR [rsp+2504], r11
	mov QWORD PTR [rsp+2512], r11
	mov QWORD PTR [rsp+2520], r11
	mov QWORD PTR [rsp+2528], r11
	mov QWORD PTR [rsp+2536], r11
	mov QWORD PTR [rsp+2544], r11
	mov QWORD PTR [rsp+2552], r11
	mov QWORD PTR [rsp+2560], r11
	mov QWORD PTR [rsp+2568], r11
	mov QWORD PTR [rsp+2576], r11
	mov QWORD PTR [rsp+2584], r11
	mov QWORD PTR [rsp+2592], r11
	mov QWORD PTR [rsp+2600], r11
	mov QWORD PTR [rsp+2608], r11
	mov QWORD PTR [rsp+2616], r11
	mov QWORD PTR [rsp+2624], r11
	mov QWORD PTR [rsp+2632], r11
	mov QWORD PTR [rsp+2640], r11
	mov QWORD PTR [rsp+2648], r11
	mov QWORD PTR [rsp+2656], r11
	mov QWORD PTR [rsp+2664], r11
	mov QWORD PTR [rsp+2672], r11
	mov QWORD PTR [rsp+2680], r11
	mov QWORD PTR [rsp+2688], r11
	mov QWORD PTR [rsp+2696], r11
	mov QWORD PTR [rsp+2704], r11
	mov QWORD PTR [rsp+2712], r11
	mov QWORD PTR [rsp+2720], r11
	mov QWORD PTR [rsp+2728], r11
	mov QWORD PTR [rsp+2736], r11
	mov QWORD PTR [rsp+2744], r11
	mov QWORD PTR [rsp+2752], r11
	mov QWORD PTR [rsp+2760], r11
	mov QWORD PTR [rsp+2768], r11
	mov QWORD PTR [rsp+2776], r11
	mov QWORD PTR [rsp+2784], r11
	mov QWORD PTR [rsp+2792], r11
	mov QWORD PTR [rsp+2800], r11
	mov QWORD PTR [rsp+2808], r11
	mov QWORD PTR [rsp+2816], r11
	mov QWORD PTR [rsp+2824], r11
	mov QWORD PTR [rsp+2832], r11
	mov QWORD PTR [rsp+2840], r11
	mov QWORD PTR [rsp+2848], r11
	mov QWORD PTR [rsp+2856], r11
	mov QWORD PTR [rsp+2864], r11
	mov QWORD PTR [rsp+2872], r11
	mov QWORD PTR [rsp+2880], r11
	mov QWORD PTR [rsp+2888], r11
	mov QWORD PTR [rsp+2896], r11
	mov QWORD PTR [rsp+2904], r11
	mov QWORD PTR [rsp+2912], r11
	mov QWORD PTR [rsp+2920], r11
	mov QWORD PTR [rsp+2928], r11
	mov QWORD PTR [rsp+2936], r11
	mov QWORD PTR [rsp+2944], r11
	mov QWORD PTR [rsp+2952], r11
	mov QWORD PTR [rsp+2960], r11
	mov QWORD PTR [rsp+2968], r11
	mov QWORD PTR [rsp+2976], r11
	mov QWORD PTR [rsp+2984], r11
	mov QWORD PTR [rsp+2992], r11
	mov QWORD PTR [rsp+3000], r11
	mov QWORD PTR [rsp+3008], r11
	mov QWORD PTR [rsp+3016], r11
	mov QWORD PTR [rsp+3024], r11
	mov QWORD PTR [rsp+3032], r11
	mov QWORD PTR [rsp+3040], r11
	mov QWORD PTR [rsp+3048], r11
	mov QWORD PTR [rsp+3056], r11
	mov QWORD PTR [rsp+3064], r11
	mov QWORD PTR [rsp+3072], r11
	mov QWORD PTR [rsp+3080], r11
	mov QWORD PTR [rsp+3088], r11
	mov QWORD PTR [rsp+3096], r11
	mov QWORD PTR [rsp+3104], r11
	mov QWORD PTR [rsp+3112], r11
	mov QWORD PTR [rsp+3120], r11
	mov QWORD PTR [rsp+3128], r11
	mov QWORD PTR [rsp+3136], r11
	mov QWORD PTR [rsp+3144], r11
	mov QWORD PTR [rsp+3152], r11
	mov QWORD PTR [rsp+3160], r11
	mov QWORD PTR [rsp+3168], r11
	mov QWORD PTR [rsp+3176], r11
	mov QWORD PTR [rsp+3184], r11
	mov QWORD PTR [rsp+3192], r11
	mov QWORD PTR [rsp+3200], r11
	mov QWORD PTR [rsp+3208], r11
	mov QWORD PTR [rsp+3216], r11
	mov QWORD PTR [rsp+3224], r11
	mov QWORD PTR [rsp+3232], r11
	mov QWORD PTR [rsp+3240], r11
	mov QWORD PTR [rsp+3248], r11
	mov QWORD PTR [rsp+3256], r11
	mov QWORD PTR [rsp+3264], r11
	mov QWORD PTR [rsp+3272], r11
	mov QWORD PTR [rsp+3280], r11
	mov QWORD PTR [rsp+3288], r11
	mov QWORD PTR [rsp+3296], r11
	mov QWORD PTR [rsp+3304], r11
	mov QWORD PTR [rsp+3312], r11
	mov QWORD PTR [rsp+3320], r11
	mov QWORD PTR [rsp+3328], r11
	mov QWORD PTR [rsp+3336], r11
	mov QWORD PTR [rsp+3344], r11
	mov QWORD PTR [rsp+3352], r11
	mov QWORD PTR [rsp+3360], r11
	mov QWORD PTR [rsp+3368], r11
	mov QWORD PTR [rsp+3376], r11
	mov QWORD PTR [rsp+3384], r11
	mov QWORD PTR [rsp+3392], r11
	mov QWORD PTR [rsp+3400], r11
	mov QWORD PTR [rsp+3408], r11
	lea rsp, [rsp+3416]
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
	lea rsp, [rsp-3440]
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
	lea rsp, [rsp+3440]
	xor eax, eax
	xor ecx, ecx
	xor edx, edx
	xor esi, esi
	xor edi, edi
	xor r8d, r8d
	xor r9d, r9d
	xor r10d, r10d
	xor r11d, r11d
	jmp 21b
	.p2align 6

vg_hmac_sha384_init_avx2:
	cmp rcx, 129
	jae 20f
	lea rsp, [rsp-1880]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+1376], rbx
	mov QWORD PTR [r8+1384], rbp
	mov QWORD PTR [r8+1392], r12
	mov QWORD PTR [r8+1400], r13
	mov QWORD PTR [r8+1408], r14
	mov QWORD PTR [r8+1416], r15
	mov rbx, rdi
	mov r12, rsi
	mov r15, r8
	mov rbp, rdx
	mov r13, rcx
	mov rdi, rbx
	call {vg_sha384_init}
	mov rdi, r12
	call {vg_sha384_init}
	mov eax, 909522486
	mov DWORD PTR [rbx+64], eax
	mov DWORD PTR [rbx+68], eax
	mov DWORD PTR [rbx+72], eax
	mov DWORD PTR [rbx+76], eax
	mov DWORD PTR [rbx+80], eax
	mov DWORD PTR [rbx+84], eax
	mov DWORD PTR [rbx+88], eax
	mov DWORD PTR [rbx+92], eax
	mov DWORD PTR [rbx+96], eax
	mov DWORD PTR [rbx+100], eax
	mov DWORD PTR [rbx+104], eax
	mov DWORD PTR [rbx+108], eax
	mov DWORD PTR [rbx+112], eax
	mov DWORD PTR [rbx+116], eax
	mov DWORD PTR [rbx+120], eax
	mov DWORD PTR [rbx+124], eax
	mov DWORD PTR [rbx+128], eax
	mov DWORD PTR [rbx+132], eax
	mov DWORD PTR [rbx+136], eax
	mov DWORD PTR [rbx+140], eax
	mov DWORD PTR [rbx+144], eax
	mov DWORD PTR [rbx+148], eax
	mov DWORD PTR [rbx+152], eax
	mov DWORD PTR [rbx+156], eax
	mov DWORD PTR [rbx+160], eax
	mov DWORD PTR [rbx+164], eax
	mov DWORD PTR [rbx+168], eax
	mov DWORD PTR [rbx+172], eax
	mov DWORD PTR [rbx+176], eax
	mov DWORD PTR [rbx+180], eax
	mov DWORD PTR [rbx+184], eax
	mov DWORD PTR [rbx+188], eax
	mov r14d, 0
	test r13, r13
	je 22f
24:
	movzx eax, BYTE PTR [rbp+r14*1]
	xor eax, 54
	mov BYTE PTR [rbx+r14*1+64], al
	add r14, 1
	cmp r14, r13
	jne 24b
	jmp 23f
22:
23:
	mov eax, DWORD PTR [rbx+64]
	xor eax, 1785358954
	mov DWORD PTR [r12+64], eax
	mov eax, DWORD PTR [rbx+68]
	xor eax, 1785358954
	mov DWORD PTR [r12+68], eax
	mov eax, DWORD PTR [rbx+72]
	xor eax, 1785358954
	mov DWORD PTR [r12+72], eax
	mov eax, DWORD PTR [rbx+76]
	xor eax, 1785358954
	mov DWORD PTR [r12+76], eax
	mov eax, DWORD PTR [rbx+80]
	xor eax, 1785358954
	mov DWORD PTR [r12+80], eax
	mov eax, DWORD PTR [rbx+84]
	xor eax, 1785358954
	mov DWORD PTR [r12+84], eax
	mov eax, DWORD PTR [rbx+88]
	xor eax, 1785358954
	mov DWORD PTR [r12+88], eax
	mov eax, DWORD PTR [rbx+92]
	xor eax, 1785358954
	mov DWORD PTR [r12+92], eax
	mov eax, DWORD PTR [rbx+96]
	xor eax, 1785358954
	mov DWORD PTR [r12+96], eax
	mov eax, DWORD PTR [rbx+100]
	xor eax, 1785358954
	mov DWORD PTR [r12+100], eax
	mov eax, DWORD PTR [rbx+104]
	xor eax, 1785358954
	mov DWORD PTR [r12+104], eax
	mov eax, DWORD PTR [rbx+108]
	xor eax, 1785358954
	mov DWORD PTR [r12+108], eax
	mov eax, DWORD PTR [rbx+112]
	xor eax, 1785358954
	mov DWORD PTR [r12+112], eax
	mov eax, DWORD PTR [rbx+116]
	xor eax, 1785358954
	mov DWORD PTR [r12+116], eax
	mov eax, DWORD PTR [rbx+120]
	xor eax, 1785358954
	mov DWORD PTR [r12+120], eax
	mov eax, DWORD PTR [rbx+124]
	xor eax, 1785358954
	mov DWORD PTR [r12+124], eax
	mov eax, DWORD PTR [rbx+128]
	xor eax, 1785358954
	mov DWORD PTR [r12+128], eax
	mov eax, DWORD PTR [rbx+132]
	xor eax, 1785358954
	mov DWORD PTR [r12+132], eax
	mov eax, DWORD PTR [rbx+136]
	xor eax, 1785358954
	mov DWORD PTR [r12+136], eax
	mov eax, DWORD PTR [rbx+140]
	xor eax, 1785358954
	mov DWORD PTR [r12+140], eax
	mov eax, DWORD PTR [rbx+144]
	xor eax, 1785358954
	mov DWORD PTR [r12+144], eax
	mov eax, DWORD PTR [rbx+148]
	xor eax, 1785358954
	mov DWORD PTR [r12+148], eax
	mov eax, DWORD PTR [rbx+152]
	xor eax, 1785358954
	mov DWORD PTR [r12+152], eax
	mov eax, DWORD PTR [rbx+156]
	xor eax, 1785358954
	mov DWORD PTR [r12+156], eax
	mov eax, DWORD PTR [rbx+160]
	xor eax, 1785358954
	mov DWORD PTR [r12+160], eax
	mov eax, DWORD PTR [rbx+164]
	xor eax, 1785358954
	mov DWORD PTR [r12+164], eax
	mov eax, DWORD PTR [rbx+168]
	xor eax, 1785358954
	mov DWORD PTR [r12+168], eax
	mov eax, DWORD PTR [rbx+172]
	xor eax, 1785358954
	mov DWORD PTR [r12+172], eax
	mov eax, DWORD PTR [rbx+176]
	xor eax, 1785358954
	mov DWORD PTR [r12+176], eax
	mov eax, DWORD PTR [rbx+180]
	xor eax, 1785358954
	mov DWORD PTR [r12+180], eax
	mov eax, DWORD PTR [rbx+184]
	xor eax, 1785358954
	mov DWORD PTR [r12+184], eax
	mov eax, DWORD PTR [rbx+188]
	xor eax, 1785358954
	mov DWORD PTR [r12+188], eax
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov rbx, r12
	mov rsi, r12
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov rbx, QWORD PTR [r15+1376]
	mov rbp, QWORD PTR [r15+1384]
	mov r12, QWORD PTR [r15+1392]
	mov r13, QWORD PTR [r15+1400]
	mov r14, QWORD PTR [r15+1408]
	mov r15, QWORD PTR [r15+1416]
	lea rsp, [rsp+1880]
21:
	ret
20:
	lea rsp, [rsp-3416]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+1872], rbx
	mov QWORD PTR [r8+1880], rbp
	mov QWORD PTR [r8+1888], r12
	mov QWORD PTR [r8+1896], r13
	mov QWORD PTR [r8+1904], r14
	mov QWORD PTR [r8+1912], r15
	mov r15, r8
	mov rbx, rdx
	mov rbp, rcx
	mov r12, rdi
	mov r13, rsi
	cmp rbp, 129
	jae 25f
	mov rdx, rbx
	mov rcx, rbp
	jmp 26f
25:
	mov rdi, r15
	add rdi, 2512
	call {vg_sha384_init}
	mov rdi, r15
	add rdi, 2512
	mov esi, 0
	mov rdx, rbx
	mov rcx, rbp
	mov r8, r15
	call {vg_sha512_update_scratch_avx2}
	mov rdi, r15
	add rdi, 2512
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2800
	mov rcx, r15
	call {vg_sha512_finalize_scratch_avx2}
	mov rdx, r15
	add rdx, 2800
	mov ecx, 48
26:
	mov rdi, r12
	mov rsi, r13
	mov r8, r15
	call {vg_hmac_sha384_init_scratch_avx2}
	mov rbx, QWORD PTR [r15+1872]
	mov rbp, QWORD PTR [r15+1880]
	mov r12, QWORD PTR [r15+1888]
	mov r13, QWORD PTR [r15+1896]
	mov r14, QWORD PTR [r15+1904]
	mov r15, QWORD PTR [r15+1912]
	mov r11d, 0
	mov QWORD PTR [rsp+8], r11
	mov QWORD PTR [rsp+16], r11
	mov QWORD PTR [rsp+24], r11
	mov QWORD PTR [rsp+32], r11
	mov QWORD PTR [rsp+40], r11
	mov QWORD PTR [rsp+48], r11
	mov QWORD PTR [rsp+56], r11
	mov QWORD PTR [rsp+64], r11
	mov QWORD PTR [rsp+72], r11
	mov QWORD PTR [rsp+80], r11
	mov QWORD PTR [rsp+88], r11
	mov QWORD PTR [rsp+96], r11
	mov QWORD PTR [rsp+104], r11
	mov QWORD PTR [rsp+112], r11
	mov QWORD PTR [rsp+120], r11
	mov QWORD PTR [rsp+128], r11
	mov QWORD PTR [rsp+136], r11
	mov QWORD PTR [rsp+144], r11
	mov QWORD PTR [rsp+152], r11
	mov QWORD PTR [rsp+160], r11
	mov QWORD PTR [rsp+168], r11
	mov QWORD PTR [rsp+176], r11
	mov QWORD PTR [rsp+184], r11
	mov QWORD PTR [rsp+192], r11
	mov QWORD PTR [rsp+200], r11
	mov QWORD PTR [rsp+208], r11
	mov QWORD PTR [rsp+216], r11
	mov QWORD PTR [rsp+224], r11
	mov QWORD PTR [rsp+232], r11
	mov QWORD PTR [rsp+240], r11
	mov QWORD PTR [rsp+248], r11
	mov QWORD PTR [rsp+256], r11
	mov QWORD PTR [rsp+264], r11
	mov QWORD PTR [rsp+272], r11
	mov QWORD PTR [rsp+280], r11
	mov QWORD PTR [rsp+288], r11
	mov QWORD PTR [rsp+296], r11
	mov QWORD PTR [rsp+304], r11
	mov QWORD PTR [rsp+312], r11
	mov QWORD PTR [rsp+320], r11
	mov QWORD PTR [rsp+328], r11
	mov QWORD PTR [rsp+336], r11
	mov QWORD PTR [rsp+344], r11
	mov QWORD PTR [rsp+352], r11
	mov QWORD PTR [rsp+360], r11
	mov QWORD PTR [rsp+368], r11
	mov QWORD PTR [rsp+376], r11
	mov QWORD PTR [rsp+384], r11
	mov QWORD PTR [rsp+392], r11
	mov QWORD PTR [rsp+400], r11
	mov QWORD PTR [rsp+408], r11
	mov QWORD PTR [rsp+416], r11
	mov QWORD PTR [rsp+424], r11
	mov QWORD PTR [rsp+432], r11
	mov QWORD PTR [rsp+440], r11
	mov QWORD PTR [rsp+448], r11
	mov QWORD PTR [rsp+456], r11
	mov QWORD PTR [rsp+464], r11
	mov QWORD PTR [rsp+472], r11
	mov QWORD PTR [rsp+480], r11
	mov QWORD PTR [rsp+488], r11
	mov QWORD PTR [rsp+496], r11
	mov QWORD PTR [rsp+504], r11
	mov QWORD PTR [rsp+512], r11
	mov QWORD PTR [rsp+520], r11
	mov QWORD PTR [rsp+528], r11
	mov QWORD PTR [rsp+536], r11
	mov QWORD PTR [rsp+544], r11
	mov QWORD PTR [rsp+552], r11
	mov QWORD PTR [rsp+560], r11
	mov QWORD PTR [rsp+568], r11
	mov QWORD PTR [rsp+576], r11
	mov QWORD PTR [rsp+584], r11
	mov QWORD PTR [rsp+592], r11
	mov QWORD PTR [rsp+600], r11
	mov QWORD PTR [rsp+608], r11
	mov QWORD PTR [rsp+616], r11
	mov QWORD PTR [rsp+624], r11
	mov QWORD PTR [rsp+632], r11
	mov QWORD PTR [rsp+640], r11
	mov QWORD PTR [rsp+648], r11
	mov QWORD PTR [rsp+656], r11
	mov QWORD PTR [rsp+664], r11
	mov QWORD PTR [rsp+672], r11
	mov QWORD PTR [rsp+680], r11
	mov QWORD PTR [rsp+688], r11
	mov QWORD PTR [rsp+696], r11
	mov QWORD PTR [rsp+704], r11
	mov QWORD PTR [rsp+712], r11
	mov QWORD PTR [rsp+720], r11
	mov QWORD PTR [rsp+728], r11
	mov QWORD PTR [rsp+736], r11
	mov QWORD PTR [rsp+744], r11
	mov QWORD PTR [rsp+752], r11
	mov QWORD PTR [rsp+760], r11
	mov QWORD PTR [rsp+768], r11
	mov QWORD PTR [rsp+776], r11
	mov QWORD PTR [rsp+784], r11
	mov QWORD PTR [rsp+792], r11
	mov QWORD PTR [rsp+800], r11
	mov QWORD PTR [rsp+808], r11
	mov QWORD PTR [rsp+816], r11
	mov QWORD PTR [rsp+824], r11
	mov QWORD PTR [rsp+832], r11
	mov QWORD PTR [rsp+840], r11
	mov QWORD PTR [rsp+848], r11
	mov QWORD PTR [rsp+856], r11
	mov QWORD PTR [rsp+864], r11
	mov QWORD PTR [rsp+872], r11
	mov QWORD PTR [rsp+880], r11
	mov QWORD PTR [rsp+888], r11
	mov QWORD PTR [rsp+896], r11
	mov QWORD PTR [rsp+904], r11
	mov QWORD PTR [rsp+912], r11
	mov QWORD PTR [rsp+920], r11
	mov QWORD PTR [rsp+928], r11
	mov QWORD PTR [rsp+936], r11
	mov QWORD PTR [rsp+944], r11
	mov QWORD PTR [rsp+952], r11
	mov QWORD PTR [rsp+960], r11
	mov QWORD PTR [rsp+968], r11
	mov QWORD PTR [rsp+976], r11
	mov QWORD PTR [rsp+984], r11
	mov QWORD PTR [rsp+992], r11
	mov QWORD PTR [rsp+1000], r11
	mov QWORD PTR [rsp+1008], r11
	mov QWORD PTR [rsp+1016], r11
	mov QWORD PTR [rsp+1024], r11
	mov QWORD PTR [rsp+1032], r11
	mov QWORD PTR [rsp+1040], r11
	mov QWORD PTR [rsp+1048], r11
	mov QWORD PTR [rsp+1056], r11
	mov QWORD PTR [rsp+1064], r11
	mov QWORD PTR [rsp+1072], r11
	mov QWORD PTR [rsp+1080], r11
	mov QWORD PTR [rsp+1088], r11
	mov QWORD PTR [rsp+1096], r11
	mov QWORD PTR [rsp+1104], r11
	mov QWORD PTR [rsp+1112], r11
	mov QWORD PTR [rsp+1120], r11
	mov QWORD PTR [rsp+1128], r11
	mov QWORD PTR [rsp+1136], r11
	mov QWORD PTR [rsp+1144], r11
	mov QWORD PTR [rsp+1152], r11
	mov QWORD PTR [rsp+1160], r11
	mov QWORD PTR [rsp+1168], r11
	mov QWORD PTR [rsp+1176], r11
	mov QWORD PTR [rsp+1184], r11
	mov QWORD PTR [rsp+1192], r11
	mov QWORD PTR [rsp+1200], r11
	mov QWORD PTR [rsp+1208], r11
	mov QWORD PTR [rsp+1216], r11
	mov QWORD PTR [rsp+1224], r11
	mov QWORD PTR [rsp+1232], r11
	mov QWORD PTR [rsp+1240], r11
	mov QWORD PTR [rsp+1248], r11
	mov QWORD PTR [rsp+1256], r11
	mov QWORD PTR [rsp+1264], r11
	mov QWORD PTR [rsp+1272], r11
	mov QWORD PTR [rsp+1280], r11
	mov QWORD PTR [rsp+1288], r11
	mov QWORD PTR [rsp+1296], r11
	mov QWORD PTR [rsp+1304], r11
	mov QWORD PTR [rsp+1312], r11
	mov QWORD PTR [rsp+1320], r11
	mov QWORD PTR [rsp+1328], r11
	mov QWORD PTR [rsp+1336], r11
	mov QWORD PTR [rsp+1344], r11
	mov QWORD PTR [rsp+1352], r11
	mov QWORD PTR [rsp+1360], r11
	mov QWORD PTR [rsp+1368], r11
	mov QWORD PTR [rsp+1376], r11
	mov QWORD PTR [rsp+1384], r11
	mov QWORD PTR [rsp+1392], r11
	mov QWORD PTR [rsp+1400], r11
	mov QWORD PTR [rsp+1408], r11
	mov QWORD PTR [rsp+1416], r11
	mov QWORD PTR [rsp+1424], r11
	mov QWORD PTR [rsp+1432], r11
	mov QWORD PTR [rsp+1440], r11
	mov QWORD PTR [rsp+1448], r11
	mov QWORD PTR [rsp+1456], r11
	mov QWORD PTR [rsp+1464], r11
	mov QWORD PTR [rsp+1472], r11
	mov QWORD PTR [rsp+1480], r11
	mov QWORD PTR [rsp+1488], r11
	mov QWORD PTR [rsp+1496], r11
	mov QWORD PTR [rsp+1504], r11
	mov QWORD PTR [rsp+1512], r11
	mov QWORD PTR [rsp+1520], r11
	mov QWORD PTR [rsp+1528], r11
	mov QWORD PTR [rsp+1536], r11
	mov QWORD PTR [rsp+1544], r11
	mov QWORD PTR [rsp+1552], r11
	mov QWORD PTR [rsp+1560], r11
	mov QWORD PTR [rsp+1568], r11
	mov QWORD PTR [rsp+1576], r11
	mov QWORD PTR [rsp+1584], r11
	mov QWORD PTR [rsp+1592], r11
	mov QWORD PTR [rsp+1600], r11
	mov QWORD PTR [rsp+1608], r11
	mov QWORD PTR [rsp+1616], r11
	mov QWORD PTR [rsp+1624], r11
	mov QWORD PTR [rsp+1632], r11
	mov QWORD PTR [rsp+1640], r11
	mov QWORD PTR [rsp+1648], r11
	mov QWORD PTR [rsp+1656], r11
	mov QWORD PTR [rsp+1664], r11
	mov QWORD PTR [rsp+1672], r11
	mov QWORD PTR [rsp+1680], r11
	mov QWORD PTR [rsp+1688], r11
	mov QWORD PTR [rsp+1696], r11
	mov QWORD PTR [rsp+1704], r11
	mov QWORD PTR [rsp+1712], r11
	mov QWORD PTR [rsp+1720], r11
	mov QWORD PTR [rsp+1728], r11
	mov QWORD PTR [rsp+1736], r11
	mov QWORD PTR [rsp+1744], r11
	mov QWORD PTR [rsp+1752], r11
	mov QWORD PTR [rsp+1760], r11
	mov QWORD PTR [rsp+1768], r11
	mov QWORD PTR [rsp+1776], r11
	mov QWORD PTR [rsp+1784], r11
	mov QWORD PTR [rsp+1792], r11
	mov QWORD PTR [rsp+1800], r11
	mov QWORD PTR [rsp+1808], r11
	mov QWORD PTR [rsp+1816], r11
	mov QWORD PTR [rsp+1824], r11
	mov QWORD PTR [rsp+1832], r11
	mov QWORD PTR [rsp+1840], r11
	mov QWORD PTR [rsp+1848], r11
	mov QWORD PTR [rsp+1856], r11
	mov QWORD PTR [rsp+1864], r11
	mov QWORD PTR [rsp+1872], r11
	mov QWORD PTR [rsp+1880], r11
	mov QWORD PTR [rsp+1888], r11
	mov QWORD PTR [rsp+1896], r11
	mov QWORD PTR [rsp+1904], r11
	mov QWORD PTR [rsp+1912], r11
	mov QWORD PTR [rsp+1920], r11
	mov QWORD PTR [rsp+1928], r11
	mov QWORD PTR [rsp+1936], r11
	mov QWORD PTR [rsp+1944], r11
	mov QWORD PTR [rsp+1952], r11
	mov QWORD PTR [rsp+1960], r11
	mov QWORD PTR [rsp+1968], r11
	mov QWORD PTR [rsp+1976], r11
	mov QWORD PTR [rsp+1984], r11
	mov QWORD PTR [rsp+1992], r11
	mov QWORD PTR [rsp+2000], r11
	mov QWORD PTR [rsp+2008], r11
	mov QWORD PTR [rsp+2016], r11
	mov QWORD PTR [rsp+2024], r11
	mov QWORD PTR [rsp+2032], r11
	mov QWORD PTR [rsp+2040], r11
	mov QWORD PTR [rsp+2048], r11
	mov QWORD PTR [rsp+2056], r11
	mov QWORD PTR [rsp+2064], r11
	mov QWORD PTR [rsp+2072], r11
	mov QWORD PTR [rsp+2080], r11
	mov QWORD PTR [rsp+2088], r11
	mov QWORD PTR [rsp+2096], r11
	mov QWORD PTR [rsp+2104], r11
	mov QWORD PTR [rsp+2112], r11
	mov QWORD PTR [rsp+2120], r11
	mov QWORD PTR [rsp+2128], r11
	mov QWORD PTR [rsp+2136], r11
	mov QWORD PTR [rsp+2144], r11
	mov QWORD PTR [rsp+2152], r11
	mov QWORD PTR [rsp+2160], r11
	mov QWORD PTR [rsp+2168], r11
	mov QWORD PTR [rsp+2176], r11
	mov QWORD PTR [rsp+2184], r11
	mov QWORD PTR [rsp+2192], r11
	mov QWORD PTR [rsp+2200], r11
	mov QWORD PTR [rsp+2208], r11
	mov QWORD PTR [rsp+2216], r11
	mov QWORD PTR [rsp+2224], r11
	mov QWORD PTR [rsp+2232], r11
	mov QWORD PTR [rsp+2240], r11
	mov QWORD PTR [rsp+2248], r11
	mov QWORD PTR [rsp+2256], r11
	mov QWORD PTR [rsp+2264], r11
	mov QWORD PTR [rsp+2272], r11
	mov QWORD PTR [rsp+2280], r11
	mov QWORD PTR [rsp+2288], r11
	mov QWORD PTR [rsp+2296], r11
	mov QWORD PTR [rsp+2304], r11
	mov QWORD PTR [rsp+2312], r11
	mov QWORD PTR [rsp+2320], r11
	mov QWORD PTR [rsp+2328], r11
	mov QWORD PTR [rsp+2336], r11
	mov QWORD PTR [rsp+2344], r11
	mov QWORD PTR [rsp+2352], r11
	mov QWORD PTR [rsp+2360], r11
	mov QWORD PTR [rsp+2368], r11
	mov QWORD PTR [rsp+2376], r11
	mov QWORD PTR [rsp+2384], r11
	mov QWORD PTR [rsp+2392], r11
	mov QWORD PTR [rsp+2400], r11
	mov QWORD PTR [rsp+2408], r11
	mov QWORD PTR [rsp+2416], r11
	mov QWORD PTR [rsp+2424], r11
	mov QWORD PTR [rsp+2432], r11
	mov QWORD PTR [rsp+2440], r11
	mov QWORD PTR [rsp+2448], r11
	mov QWORD PTR [rsp+2456], r11
	mov QWORD PTR [rsp+2464], r11
	mov QWORD PTR [rsp+2472], r11
	mov QWORD PTR [rsp+2480], r11
	mov QWORD PTR [rsp+2488], r11
	mov QWORD PTR [rsp+2496], r11
	mov QWORD PTR [rsp+2504], r11
	mov QWORD PTR [rsp+2512], r11
	mov QWORD PTR [rsp+2520], r11
	mov QWORD PTR [rsp+2528], r11
	mov QWORD PTR [rsp+2536], r11
	mov QWORD PTR [rsp+2544], r11
	mov QWORD PTR [rsp+2552], r11
	mov QWORD PTR [rsp+2560], r11
	mov QWORD PTR [rsp+2568], r11
	mov QWORD PTR [rsp+2576], r11
	mov QWORD PTR [rsp+2584], r11
	mov QWORD PTR [rsp+2592], r11
	mov QWORD PTR [rsp+2600], r11
	mov QWORD PTR [rsp+2608], r11
	mov QWORD PTR [rsp+2616], r11
	mov QWORD PTR [rsp+2624], r11
	mov QWORD PTR [rsp+2632], r11
	mov QWORD PTR [rsp+2640], r11
	mov QWORD PTR [rsp+2648], r11
	mov QWORD PTR [rsp+2656], r11
	mov QWORD PTR [rsp+2664], r11
	mov QWORD PTR [rsp+2672], r11
	mov QWORD PTR [rsp+2680], r11
	mov QWORD PTR [rsp+2688], r11
	mov QWORD PTR [rsp+2696], r11
	mov QWORD PTR [rsp+2704], r11
	mov QWORD PTR [rsp+2712], r11
	mov QWORD PTR [rsp+2720], r11
	mov QWORD PTR [rsp+2728], r11
	mov QWORD PTR [rsp+2736], r11
	mov QWORD PTR [rsp+2744], r11
	mov QWORD PTR [rsp+2752], r11
	mov QWORD PTR [rsp+2760], r11
	mov QWORD PTR [rsp+2768], r11
	mov QWORD PTR [rsp+2776], r11
	mov QWORD PTR [rsp+2784], r11
	mov QWORD PTR [rsp+2792], r11
	mov QWORD PTR [rsp+2800], r11
	mov QWORD PTR [rsp+2808], r11
	mov QWORD PTR [rsp+2816], r11
	mov QWORD PTR [rsp+2824], r11
	mov QWORD PTR [rsp+2832], r11
	mov QWORD PTR [rsp+2840], r11
	mov QWORD PTR [rsp+2848], r11
	mov QWORD PTR [rsp+2856], r11
	mov QWORD PTR [rsp+2864], r11
	mov QWORD PTR [rsp+2872], r11
	mov QWORD PTR [rsp+2880], r11
	mov QWORD PTR [rsp+2888], r11
	mov QWORD PTR [rsp+2896], r11
	mov QWORD PTR [rsp+2904], r11
	mov QWORD PTR [rsp+2912], r11
	mov QWORD PTR [rsp+2920], r11
	mov QWORD PTR [rsp+2928], r11
	mov QWORD PTR [rsp+2936], r11
	mov QWORD PTR [rsp+2944], r11
	mov QWORD PTR [rsp+2952], r11
	mov QWORD PTR [rsp+2960], r11
	mov QWORD PTR [rsp+2968], r11
	mov QWORD PTR [rsp+2976], r11
	mov QWORD PTR [rsp+2984], r11
	mov QWORD PTR [rsp+2992], r11
	mov QWORD PTR [rsp+3000], r11
	mov QWORD PTR [rsp+3008], r11
	mov QWORD PTR [rsp+3016], r11
	mov QWORD PTR [rsp+3024], r11
	mov QWORD PTR [rsp+3032], r11
	mov QWORD PTR [rsp+3040], r11
	mov QWORD PTR [rsp+3048], r11
	mov QWORD PTR [rsp+3056], r11
	mov QWORD PTR [rsp+3064], r11
	mov QWORD PTR [rsp+3072], r11
	mov QWORD PTR [rsp+3080], r11
	mov QWORD PTR [rsp+3088], r11
	mov QWORD PTR [rsp+3096], r11
	mov QWORD PTR [rsp+3104], r11
	mov QWORD PTR [rsp+3112], r11
	mov QWORD PTR [rsp+3120], r11
	mov QWORD PTR [rsp+3128], r11
	mov QWORD PTR [rsp+3136], r11
	mov QWORD PTR [rsp+3144], r11
	mov QWORD PTR [rsp+3152], r11
	mov QWORD PTR [rsp+3160], r11
	mov QWORD PTR [rsp+3168], r11
	mov QWORD PTR [rsp+3176], r11
	mov QWORD PTR [rsp+3184], r11
	mov QWORD PTR [rsp+3192], r11
	mov QWORD PTR [rsp+3200], r11
	mov QWORD PTR [rsp+3208], r11
	mov QWORD PTR [rsp+3216], r11
	mov QWORD PTR [rsp+3224], r11
	mov QWORD PTR [rsp+3232], r11
	mov QWORD PTR [rsp+3240], r11
	mov QWORD PTR [rsp+3248], r11
	mov QWORD PTR [rsp+3256], r11
	mov QWORD PTR [rsp+3264], r11
	mov QWORD PTR [rsp+3272], r11
	mov QWORD PTR [rsp+3280], r11
	mov QWORD PTR [rsp+3288], r11
	mov QWORD PTR [rsp+3296], r11
	mov QWORD PTR [rsp+3304], r11
	mov QWORD PTR [rsp+3312], r11
	mov QWORD PTR [rsp+3320], r11
	mov QWORD PTR [rsp+3328], r11
	mov QWORD PTR [rsp+3336], r11
	mov QWORD PTR [rsp+3344], r11
	mov QWORD PTR [rsp+3352], r11
	mov QWORD PTR [rsp+3360], r11
	mov QWORD PTR [rsp+3368], r11
	mov QWORD PTR [rsp+3376], r11
	mov QWORD PTR [rsp+3384], r11
	mov QWORD PTR [rsp+3392], r11
	mov QWORD PTR [rsp+3400], r11
	mov QWORD PTR [rsp+3408], r11
	lea rsp, [rsp+3416]
	jmp 21b
	.p2align 6

vg_hmac_sha384_finalize_avx2:
	lea rsp, [rsp-1880]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+1376], rbx
	mov QWORD PTR [r8+1384], rbp
	mov QWORD PTR [r8+1392], r12
	mov QWORD PTR [r8+1400], r13
	mov QWORD PTR [r8+1408], r14
	mov QWORD PTR [r8+1416], r15
	mov rbx, rdi
	mov r12, rsi
	mov r13, rcx
	mov r15, r8
	mov rsi, rdx
	mov rdx, r15
	add rdx, 1424
	mov rcx, r15
	call {vg_sha512_finalize_scratch_avx2}
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu XMMWORD PTR [rbx], xmm0
	movdqu xmm0, XMMWORD PTR [r12+16]
	movdqu XMMWORD PTR [rbx+16], xmm0
	movdqu xmm0, XMMWORD PTR [r12+32]
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu xmm0, XMMWORD PTR [r12+48]
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu xmm0, XMMWORD PTR [r15+1424]
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu xmm0, XMMWORD PTR [r15+1440]
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu xmm0, XMMWORD PTR [r15+1456]
	movdqu XMMWORD PTR [rbx+96], xmm0
	mov rbp, rbx
	add rbp, 64
	mov eax, 128
	movq xmm1, rax
	movdqu XMMWORD PTR [rbp+48], xmm1
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbp+64], xmm0
	movdqu XMMWORD PTR [rbp+80], xmm0
	movdqu XMMWORD PTR [rbp+96], xmm0
	mov r12d, 176
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	movdqu XMMWORD PTR [rbp+112], xmm7
	mov rsi, rbp
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress_avx2}
	mov rbx, rdi
	mov r15, rcx
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	mov rax, QWORD PTR [rbx+32]
	bswap rax
	mov QWORD PTR [rbp+32], rax
	mov rax, QWORD PTR [rbx+40]
	bswap rax
	mov QWORD PTR [rbp+40], rax
	mov rax, QWORD PTR [rbx+48]
	bswap rax
	mov QWORD PTR [rbp+48], rax
	mov rax, QWORD PTR [rbx+56]
	bswap rax
	mov QWORD PTR [rbp+56], rax
	movdqu xmm0, XMMWORD PTR [rbp]
	movdqu XMMWORD PTR [r13], xmm0
	movdqu xmm0, XMMWORD PTR [rbp+16]
	movdqu XMMWORD PTR [r13+16], xmm0
	movdqu xmm0, XMMWORD PTR [rbp+32]
	movdqu XMMWORD PTR [r13+32], xmm0
	mov rbx, QWORD PTR [r15+1376]
	mov rbp, QWORD PTR [r15+1384]
	mov r12, QWORD PTR [r15+1392]
	mov r13, QWORD PTR [r15+1400]
	mov r14, QWORD PTR [r15+1408]
	mov r15, QWORD PTR [r15+1416]
	lea rsp, [rsp+1880]
	ret
	.p2align 6

vg_hmac_sha384_init:
	cmp rcx, 129
	jae 20f
	lea rsp, [rsp-1880]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+1376], rbx
	mov QWORD PTR [r8+1384], rbp
	mov QWORD PTR [r8+1392], r12
	mov QWORD PTR [r8+1400], r13
	mov QWORD PTR [r8+1408], r14
	mov QWORD PTR [r8+1416], r15
	mov rbx, rdi
	mov r12, rsi
	mov r15, r8
	mov rbp, rdx
	mov r13, rcx
	mov rdi, rbx
	call {vg_sha384_init}
	mov rdi, r12
	call {vg_sha384_init}
	mov eax, 909522486
	mov DWORD PTR [rbx+64], eax
	mov DWORD PTR [rbx+68], eax
	mov DWORD PTR [rbx+72], eax
	mov DWORD PTR [rbx+76], eax
	mov DWORD PTR [rbx+80], eax
	mov DWORD PTR [rbx+84], eax
	mov DWORD PTR [rbx+88], eax
	mov DWORD PTR [rbx+92], eax
	mov DWORD PTR [rbx+96], eax
	mov DWORD PTR [rbx+100], eax
	mov DWORD PTR [rbx+104], eax
	mov DWORD PTR [rbx+108], eax
	mov DWORD PTR [rbx+112], eax
	mov DWORD PTR [rbx+116], eax
	mov DWORD PTR [rbx+120], eax
	mov DWORD PTR [rbx+124], eax
	mov DWORD PTR [rbx+128], eax
	mov DWORD PTR [rbx+132], eax
	mov DWORD PTR [rbx+136], eax
	mov DWORD PTR [rbx+140], eax
	mov DWORD PTR [rbx+144], eax
	mov DWORD PTR [rbx+148], eax
	mov DWORD PTR [rbx+152], eax
	mov DWORD PTR [rbx+156], eax
	mov DWORD PTR [rbx+160], eax
	mov DWORD PTR [rbx+164], eax
	mov DWORD PTR [rbx+168], eax
	mov DWORD PTR [rbx+172], eax
	mov DWORD PTR [rbx+176], eax
	mov DWORD PTR [rbx+180], eax
	mov DWORD PTR [rbx+184], eax
	mov DWORD PTR [rbx+188], eax
	mov r14d, 0
	test r13, r13
	je 22f
24:
	movzx eax, BYTE PTR [rbp+r14*1]
	xor eax, 54
	mov BYTE PTR [rbx+r14*1+64], al
	add r14, 1
	cmp r14, r13
	jne 24b
	jmp 23f
22:
23:
	mov eax, DWORD PTR [rbx+64]
	xor eax, 1785358954
	mov DWORD PTR [r12+64], eax
	mov eax, DWORD PTR [rbx+68]
	xor eax, 1785358954
	mov DWORD PTR [r12+68], eax
	mov eax, DWORD PTR [rbx+72]
	xor eax, 1785358954
	mov DWORD PTR [r12+72], eax
	mov eax, DWORD PTR [rbx+76]
	xor eax, 1785358954
	mov DWORD PTR [r12+76], eax
	mov eax, DWORD PTR [rbx+80]
	xor eax, 1785358954
	mov DWORD PTR [r12+80], eax
	mov eax, DWORD PTR [rbx+84]
	xor eax, 1785358954
	mov DWORD PTR [r12+84], eax
	mov eax, DWORD PTR [rbx+88]
	xor eax, 1785358954
	mov DWORD PTR [r12+88], eax
	mov eax, DWORD PTR [rbx+92]
	xor eax, 1785358954
	mov DWORD PTR [r12+92], eax
	mov eax, DWORD PTR [rbx+96]
	xor eax, 1785358954
	mov DWORD PTR [r12+96], eax
	mov eax, DWORD PTR [rbx+100]
	xor eax, 1785358954
	mov DWORD PTR [r12+100], eax
	mov eax, DWORD PTR [rbx+104]
	xor eax, 1785358954
	mov DWORD PTR [r12+104], eax
	mov eax, DWORD PTR [rbx+108]
	xor eax, 1785358954
	mov DWORD PTR [r12+108], eax
	mov eax, DWORD PTR [rbx+112]
	xor eax, 1785358954
	mov DWORD PTR [r12+112], eax
	mov eax, DWORD PTR [rbx+116]
	xor eax, 1785358954
	mov DWORD PTR [r12+116], eax
	mov eax, DWORD PTR [rbx+120]
	xor eax, 1785358954
	mov DWORD PTR [r12+120], eax
	mov eax, DWORD PTR [rbx+124]
	xor eax, 1785358954
	mov DWORD PTR [r12+124], eax
	mov eax, DWORD PTR [rbx+128]
	xor eax, 1785358954
	mov DWORD PTR [r12+128], eax
	mov eax, DWORD PTR [rbx+132]
	xor eax, 1785358954
	mov DWORD PTR [r12+132], eax
	mov eax, DWORD PTR [rbx+136]
	xor eax, 1785358954
	mov DWORD PTR [r12+136], eax
	mov eax, DWORD PTR [rbx+140]
	xor eax, 1785358954
	mov DWORD PTR [r12+140], eax
	mov eax, DWORD PTR [rbx+144]
	xor eax, 1785358954
	mov DWORD PTR [r12+144], eax
	mov eax, DWORD PTR [rbx+148]
	xor eax, 1785358954
	mov DWORD PTR [r12+148], eax
	mov eax, DWORD PTR [rbx+152]
	xor eax, 1785358954
	mov DWORD PTR [r12+152], eax
	mov eax, DWORD PTR [rbx+156]
	xor eax, 1785358954
	mov DWORD PTR [r12+156], eax
	mov eax, DWORD PTR [rbx+160]
	xor eax, 1785358954
	mov DWORD PTR [r12+160], eax
	mov eax, DWORD PTR [rbx+164]
	xor eax, 1785358954
	mov DWORD PTR [r12+164], eax
	mov eax, DWORD PTR [rbx+168]
	xor eax, 1785358954
	mov DWORD PTR [r12+168], eax
	mov eax, DWORD PTR [rbx+172]
	xor eax, 1785358954
	mov DWORD PTR [r12+172], eax
	mov eax, DWORD PTR [rbx+176]
	xor eax, 1785358954
	mov DWORD PTR [r12+176], eax
	mov eax, DWORD PTR [rbx+180]
	xor eax, 1785358954
	mov DWORD PTR [r12+180], eax
	mov eax, DWORD PTR [rbx+184]
	xor eax, 1785358954
	mov DWORD PTR [r12+184], eax
	mov eax, DWORD PTR [rbx+188]
	xor eax, 1785358954
	mov DWORD PTR [r12+188], eax
	mov rsi, rbx
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
	mov rbx, r12
	mov rsi, r12
	add rsi, 64
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
	mov rbx, QWORD PTR [r15+1376]
	mov rbp, QWORD PTR [r15+1384]
	mov r12, QWORD PTR [r15+1392]
	mov r13, QWORD PTR [r15+1400]
	mov r14, QWORD PTR [r15+1408]
	mov r15, QWORD PTR [r15+1416]
	lea rsp, [rsp+1880]
21:
	ret
20:
	lea rsp, [rsp-3416]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+1872], rbx
	mov QWORD PTR [r8+1880], rbp
	mov QWORD PTR [r8+1888], r12
	mov QWORD PTR [r8+1896], r13
	mov QWORD PTR [r8+1904], r14
	mov QWORD PTR [r8+1912], r15
	mov r15, r8
	mov rbx, rdx
	mov rbp, rcx
	mov r12, rdi
	mov r13, rsi
	cmp rbp, 129
	jae 25f
	mov rdx, rbx
	mov rcx, rbp
	jmp 26f
25:
	mov rdi, r15
	add rdi, 2512
	call {vg_sha384_init}
	mov rdi, r15
	add rdi, 2512
	mov esi, 0
	mov rdx, rbx
	mov rcx, rbp
	mov r8, r15
	call {vg_sha512_update_scratch}
	mov rdi, r15
	add rdi, 2512
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2800
	mov rcx, r15
	call {vg_sha512_finalize_scratch}
	mov rdx, r15
	add rdx, 2800
	mov ecx, 48
26:
	mov rdi, r12
	mov rsi, r13
	mov r8, r15
	call {vg_hmac_sha384_init_scratch}
	mov rbx, QWORD PTR [r15+1872]
	mov rbp, QWORD PTR [r15+1880]
	mov r12, QWORD PTR [r15+1888]
	mov r13, QWORD PTR [r15+1896]
	mov r14, QWORD PTR [r15+1904]
	mov r15, QWORD PTR [r15+1912]
	mov r11d, 0
	mov QWORD PTR [rsp+8], r11
	mov QWORD PTR [rsp+16], r11
	mov QWORD PTR [rsp+24], r11
	mov QWORD PTR [rsp+32], r11
	mov QWORD PTR [rsp+40], r11
	mov QWORD PTR [rsp+48], r11
	mov QWORD PTR [rsp+56], r11
	mov QWORD PTR [rsp+64], r11
	mov QWORD PTR [rsp+72], r11
	mov QWORD PTR [rsp+80], r11
	mov QWORD PTR [rsp+88], r11
	mov QWORD PTR [rsp+96], r11
	mov QWORD PTR [rsp+104], r11
	mov QWORD PTR [rsp+112], r11
	mov QWORD PTR [rsp+120], r11
	mov QWORD PTR [rsp+128], r11
	mov QWORD PTR [rsp+136], r11
	mov QWORD PTR [rsp+144], r11
	mov QWORD PTR [rsp+152], r11
	mov QWORD PTR [rsp+160], r11
	mov QWORD PTR [rsp+168], r11
	mov QWORD PTR [rsp+176], r11
	mov QWORD PTR [rsp+184], r11
	mov QWORD PTR [rsp+192], r11
	mov QWORD PTR [rsp+200], r11
	mov QWORD PTR [rsp+208], r11
	mov QWORD PTR [rsp+216], r11
	mov QWORD PTR [rsp+224], r11
	mov QWORD PTR [rsp+232], r11
	mov QWORD PTR [rsp+240], r11
	mov QWORD PTR [rsp+248], r11
	mov QWORD PTR [rsp+256], r11
	mov QWORD PTR [rsp+264], r11
	mov QWORD PTR [rsp+272], r11
	mov QWORD PTR [rsp+280], r11
	mov QWORD PTR [rsp+288], r11
	mov QWORD PTR [rsp+296], r11
	mov QWORD PTR [rsp+304], r11
	mov QWORD PTR [rsp+312], r11
	mov QWORD PTR [rsp+320], r11
	mov QWORD PTR [rsp+328], r11
	mov QWORD PTR [rsp+336], r11
	mov QWORD PTR [rsp+344], r11
	mov QWORD PTR [rsp+352], r11
	mov QWORD PTR [rsp+360], r11
	mov QWORD PTR [rsp+368], r11
	mov QWORD PTR [rsp+376], r11
	mov QWORD PTR [rsp+384], r11
	mov QWORD PTR [rsp+392], r11
	mov QWORD PTR [rsp+400], r11
	mov QWORD PTR [rsp+408], r11
	mov QWORD PTR [rsp+416], r11
	mov QWORD PTR [rsp+424], r11
	mov QWORD PTR [rsp+432], r11
	mov QWORD PTR [rsp+440], r11
	mov QWORD PTR [rsp+448], r11
	mov QWORD PTR [rsp+456], r11
	mov QWORD PTR [rsp+464], r11
	mov QWORD PTR [rsp+472], r11
	mov QWORD PTR [rsp+480], r11
	mov QWORD PTR [rsp+488], r11
	mov QWORD PTR [rsp+496], r11
	mov QWORD PTR [rsp+504], r11
	mov QWORD PTR [rsp+512], r11
	mov QWORD PTR [rsp+520], r11
	mov QWORD PTR [rsp+528], r11
	mov QWORD PTR [rsp+536], r11
	mov QWORD PTR [rsp+544], r11
	mov QWORD PTR [rsp+552], r11
	mov QWORD PTR [rsp+560], r11
	mov QWORD PTR [rsp+568], r11
	mov QWORD PTR [rsp+576], r11
	mov QWORD PTR [rsp+584], r11
	mov QWORD PTR [rsp+592], r11
	mov QWORD PTR [rsp+600], r11
	mov QWORD PTR [rsp+608], r11
	mov QWORD PTR [rsp+616], r11
	mov QWORD PTR [rsp+624], r11
	mov QWORD PTR [rsp+632], r11
	mov QWORD PTR [rsp+640], r11
	mov QWORD PTR [rsp+648], r11
	mov QWORD PTR [rsp+656], r11
	mov QWORD PTR [rsp+664], r11
	mov QWORD PTR [rsp+672], r11
	mov QWORD PTR [rsp+680], r11
	mov QWORD PTR [rsp+688], r11
	mov QWORD PTR [rsp+696], r11
	mov QWORD PTR [rsp+704], r11
	mov QWORD PTR [rsp+712], r11
	mov QWORD PTR [rsp+720], r11
	mov QWORD PTR [rsp+728], r11
	mov QWORD PTR [rsp+736], r11
	mov QWORD PTR [rsp+744], r11
	mov QWORD PTR [rsp+752], r11
	mov QWORD PTR [rsp+760], r11
	mov QWORD PTR [rsp+768], r11
	mov QWORD PTR [rsp+776], r11
	mov QWORD PTR [rsp+784], r11
	mov QWORD PTR [rsp+792], r11
	mov QWORD PTR [rsp+800], r11
	mov QWORD PTR [rsp+808], r11
	mov QWORD PTR [rsp+816], r11
	mov QWORD PTR [rsp+824], r11
	mov QWORD PTR [rsp+832], r11
	mov QWORD PTR [rsp+840], r11
	mov QWORD PTR [rsp+848], r11
	mov QWORD PTR [rsp+856], r11
	mov QWORD PTR [rsp+864], r11
	mov QWORD PTR [rsp+872], r11
	mov QWORD PTR [rsp+880], r11
	mov QWORD PTR [rsp+888], r11
	mov QWORD PTR [rsp+896], r11
	mov QWORD PTR [rsp+904], r11
	mov QWORD PTR [rsp+912], r11
	mov QWORD PTR [rsp+920], r11
	mov QWORD PTR [rsp+928], r11
	mov QWORD PTR [rsp+936], r11
	mov QWORD PTR [rsp+944], r11
	mov QWORD PTR [rsp+952], r11
	mov QWORD PTR [rsp+960], r11
	mov QWORD PTR [rsp+968], r11
	mov QWORD PTR [rsp+976], r11
	mov QWORD PTR [rsp+984], r11
	mov QWORD PTR [rsp+992], r11
	mov QWORD PTR [rsp+1000], r11
	mov QWORD PTR [rsp+1008], r11
	mov QWORD PTR [rsp+1016], r11
	mov QWORD PTR [rsp+1024], r11
	mov QWORD PTR [rsp+1032], r11
	mov QWORD PTR [rsp+1040], r11
	mov QWORD PTR [rsp+1048], r11
	mov QWORD PTR [rsp+1056], r11
	mov QWORD PTR [rsp+1064], r11
	mov QWORD PTR [rsp+1072], r11
	mov QWORD PTR [rsp+1080], r11
	mov QWORD PTR [rsp+1088], r11
	mov QWORD PTR [rsp+1096], r11
	mov QWORD PTR [rsp+1104], r11
	mov QWORD PTR [rsp+1112], r11
	mov QWORD PTR [rsp+1120], r11
	mov QWORD PTR [rsp+1128], r11
	mov QWORD PTR [rsp+1136], r11
	mov QWORD PTR [rsp+1144], r11
	mov QWORD PTR [rsp+1152], r11
	mov QWORD PTR [rsp+1160], r11
	mov QWORD PTR [rsp+1168], r11
	mov QWORD PTR [rsp+1176], r11
	mov QWORD PTR [rsp+1184], r11
	mov QWORD PTR [rsp+1192], r11
	mov QWORD PTR [rsp+1200], r11
	mov QWORD PTR [rsp+1208], r11
	mov QWORD PTR [rsp+1216], r11
	mov QWORD PTR [rsp+1224], r11
	mov QWORD PTR [rsp+1232], r11
	mov QWORD PTR [rsp+1240], r11
	mov QWORD PTR [rsp+1248], r11
	mov QWORD PTR [rsp+1256], r11
	mov QWORD PTR [rsp+1264], r11
	mov QWORD PTR [rsp+1272], r11
	mov QWORD PTR [rsp+1280], r11
	mov QWORD PTR [rsp+1288], r11
	mov QWORD PTR [rsp+1296], r11
	mov QWORD PTR [rsp+1304], r11
	mov QWORD PTR [rsp+1312], r11
	mov QWORD PTR [rsp+1320], r11
	mov QWORD PTR [rsp+1328], r11
	mov QWORD PTR [rsp+1336], r11
	mov QWORD PTR [rsp+1344], r11
	mov QWORD PTR [rsp+1352], r11
	mov QWORD PTR [rsp+1360], r11
	mov QWORD PTR [rsp+1368], r11
	mov QWORD PTR [rsp+1376], r11
	mov QWORD PTR [rsp+1384], r11
	mov QWORD PTR [rsp+1392], r11
	mov QWORD PTR [rsp+1400], r11
	mov QWORD PTR [rsp+1408], r11
	mov QWORD PTR [rsp+1416], r11
	mov QWORD PTR [rsp+1424], r11
	mov QWORD PTR [rsp+1432], r11
	mov QWORD PTR [rsp+1440], r11
	mov QWORD PTR [rsp+1448], r11
	mov QWORD PTR [rsp+1456], r11
	mov QWORD PTR [rsp+1464], r11
	mov QWORD PTR [rsp+1472], r11
	mov QWORD PTR [rsp+1480], r11
	mov QWORD PTR [rsp+1488], r11
	mov QWORD PTR [rsp+1496], r11
	mov QWORD PTR [rsp+1504], r11
	mov QWORD PTR [rsp+1512], r11
	mov QWORD PTR [rsp+1520], r11
	mov QWORD PTR [rsp+1528], r11
	mov QWORD PTR [rsp+1536], r11
	mov QWORD PTR [rsp+1544], r11
	mov QWORD PTR [rsp+1552], r11
	mov QWORD PTR [rsp+1560], r11
	mov QWORD PTR [rsp+1568], r11
	mov QWORD PTR [rsp+1576], r11
	mov QWORD PTR [rsp+1584], r11
	mov QWORD PTR [rsp+1592], r11
	mov QWORD PTR [rsp+1600], r11
	mov QWORD PTR [rsp+1608], r11
	mov QWORD PTR [rsp+1616], r11
	mov QWORD PTR [rsp+1624], r11
	mov QWORD PTR [rsp+1632], r11
	mov QWORD PTR [rsp+1640], r11
	mov QWORD PTR [rsp+1648], r11
	mov QWORD PTR [rsp+1656], r11
	mov QWORD PTR [rsp+1664], r11
	mov QWORD PTR [rsp+1672], r11
	mov QWORD PTR [rsp+1680], r11
	mov QWORD PTR [rsp+1688], r11
	mov QWORD PTR [rsp+1696], r11
	mov QWORD PTR [rsp+1704], r11
	mov QWORD PTR [rsp+1712], r11
	mov QWORD PTR [rsp+1720], r11
	mov QWORD PTR [rsp+1728], r11
	mov QWORD PTR [rsp+1736], r11
	mov QWORD PTR [rsp+1744], r11
	mov QWORD PTR [rsp+1752], r11
	mov QWORD PTR [rsp+1760], r11
	mov QWORD PTR [rsp+1768], r11
	mov QWORD PTR [rsp+1776], r11
	mov QWORD PTR [rsp+1784], r11
	mov QWORD PTR [rsp+1792], r11
	mov QWORD PTR [rsp+1800], r11
	mov QWORD PTR [rsp+1808], r11
	mov QWORD PTR [rsp+1816], r11
	mov QWORD PTR [rsp+1824], r11
	mov QWORD PTR [rsp+1832], r11
	mov QWORD PTR [rsp+1840], r11
	mov QWORD PTR [rsp+1848], r11
	mov QWORD PTR [rsp+1856], r11
	mov QWORD PTR [rsp+1864], r11
	mov QWORD PTR [rsp+1872], r11
	mov QWORD PTR [rsp+1880], r11
	mov QWORD PTR [rsp+1888], r11
	mov QWORD PTR [rsp+1896], r11
	mov QWORD PTR [rsp+1904], r11
	mov QWORD PTR [rsp+1912], r11
	mov QWORD PTR [rsp+1920], r11
	mov QWORD PTR [rsp+1928], r11
	mov QWORD PTR [rsp+1936], r11
	mov QWORD PTR [rsp+1944], r11
	mov QWORD PTR [rsp+1952], r11
	mov QWORD PTR [rsp+1960], r11
	mov QWORD PTR [rsp+1968], r11
	mov QWORD PTR [rsp+1976], r11
	mov QWORD PTR [rsp+1984], r11
	mov QWORD PTR [rsp+1992], r11
	mov QWORD PTR [rsp+2000], r11
	mov QWORD PTR [rsp+2008], r11
	mov QWORD PTR [rsp+2016], r11
	mov QWORD PTR [rsp+2024], r11
	mov QWORD PTR [rsp+2032], r11
	mov QWORD PTR [rsp+2040], r11
	mov QWORD PTR [rsp+2048], r11
	mov QWORD PTR [rsp+2056], r11
	mov QWORD PTR [rsp+2064], r11
	mov QWORD PTR [rsp+2072], r11
	mov QWORD PTR [rsp+2080], r11
	mov QWORD PTR [rsp+2088], r11
	mov QWORD PTR [rsp+2096], r11
	mov QWORD PTR [rsp+2104], r11
	mov QWORD PTR [rsp+2112], r11
	mov QWORD PTR [rsp+2120], r11
	mov QWORD PTR [rsp+2128], r11
	mov QWORD PTR [rsp+2136], r11
	mov QWORD PTR [rsp+2144], r11
	mov QWORD PTR [rsp+2152], r11
	mov QWORD PTR [rsp+2160], r11
	mov QWORD PTR [rsp+2168], r11
	mov QWORD PTR [rsp+2176], r11
	mov QWORD PTR [rsp+2184], r11
	mov QWORD PTR [rsp+2192], r11
	mov QWORD PTR [rsp+2200], r11
	mov QWORD PTR [rsp+2208], r11
	mov QWORD PTR [rsp+2216], r11
	mov QWORD PTR [rsp+2224], r11
	mov QWORD PTR [rsp+2232], r11
	mov QWORD PTR [rsp+2240], r11
	mov QWORD PTR [rsp+2248], r11
	mov QWORD PTR [rsp+2256], r11
	mov QWORD PTR [rsp+2264], r11
	mov QWORD PTR [rsp+2272], r11
	mov QWORD PTR [rsp+2280], r11
	mov QWORD PTR [rsp+2288], r11
	mov QWORD PTR [rsp+2296], r11
	mov QWORD PTR [rsp+2304], r11
	mov QWORD PTR [rsp+2312], r11
	mov QWORD PTR [rsp+2320], r11
	mov QWORD PTR [rsp+2328], r11
	mov QWORD PTR [rsp+2336], r11
	mov QWORD PTR [rsp+2344], r11
	mov QWORD PTR [rsp+2352], r11
	mov QWORD PTR [rsp+2360], r11
	mov QWORD PTR [rsp+2368], r11
	mov QWORD PTR [rsp+2376], r11
	mov QWORD PTR [rsp+2384], r11
	mov QWORD PTR [rsp+2392], r11
	mov QWORD PTR [rsp+2400], r11
	mov QWORD PTR [rsp+2408], r11
	mov QWORD PTR [rsp+2416], r11
	mov QWORD PTR [rsp+2424], r11
	mov QWORD PTR [rsp+2432], r11
	mov QWORD PTR [rsp+2440], r11
	mov QWORD PTR [rsp+2448], r11
	mov QWORD PTR [rsp+2456], r11
	mov QWORD PTR [rsp+2464], r11
	mov QWORD PTR [rsp+2472], r11
	mov QWORD PTR [rsp+2480], r11
	mov QWORD PTR [rsp+2488], r11
	mov QWORD PTR [rsp+2496], r11
	mov QWORD PTR [rsp+2504], r11
	mov QWORD PTR [rsp+2512], r11
	mov QWORD PTR [rsp+2520], r11
	mov QWORD PTR [rsp+2528], r11
	mov QWORD PTR [rsp+2536], r11
	mov QWORD PTR [rsp+2544], r11
	mov QWORD PTR [rsp+2552], r11
	mov QWORD PTR [rsp+2560], r11
	mov QWORD PTR [rsp+2568], r11
	mov QWORD PTR [rsp+2576], r11
	mov QWORD PTR [rsp+2584], r11
	mov QWORD PTR [rsp+2592], r11
	mov QWORD PTR [rsp+2600], r11
	mov QWORD PTR [rsp+2608], r11
	mov QWORD PTR [rsp+2616], r11
	mov QWORD PTR [rsp+2624], r11
	mov QWORD PTR [rsp+2632], r11
	mov QWORD PTR [rsp+2640], r11
	mov QWORD PTR [rsp+2648], r11
	mov QWORD PTR [rsp+2656], r11
	mov QWORD PTR [rsp+2664], r11
	mov QWORD PTR [rsp+2672], r11
	mov QWORD PTR [rsp+2680], r11
	mov QWORD PTR [rsp+2688], r11
	mov QWORD PTR [rsp+2696], r11
	mov QWORD PTR [rsp+2704], r11
	mov QWORD PTR [rsp+2712], r11
	mov QWORD PTR [rsp+2720], r11
	mov QWORD PTR [rsp+2728], r11
	mov QWORD PTR [rsp+2736], r11
	mov QWORD PTR [rsp+2744], r11
	mov QWORD PTR [rsp+2752], r11
	mov QWORD PTR [rsp+2760], r11
	mov QWORD PTR [rsp+2768], r11
	mov QWORD PTR [rsp+2776], r11
	mov QWORD PTR [rsp+2784], r11
	mov QWORD PTR [rsp+2792], r11
	mov QWORD PTR [rsp+2800], r11
	mov QWORD PTR [rsp+2808], r11
	mov QWORD PTR [rsp+2816], r11
	mov QWORD PTR [rsp+2824], r11
	mov QWORD PTR [rsp+2832], r11
	mov QWORD PTR [rsp+2840], r11
	mov QWORD PTR [rsp+2848], r11
	mov QWORD PTR [rsp+2856], r11
	mov QWORD PTR [rsp+2864], r11
	mov QWORD PTR [rsp+2872], r11
	mov QWORD PTR [rsp+2880], r11
	mov QWORD PTR [rsp+2888], r11
	mov QWORD PTR [rsp+2896], r11
	mov QWORD PTR [rsp+2904], r11
	mov QWORD PTR [rsp+2912], r11
	mov QWORD PTR [rsp+2920], r11
	mov QWORD PTR [rsp+2928], r11
	mov QWORD PTR [rsp+2936], r11
	mov QWORD PTR [rsp+2944], r11
	mov QWORD PTR [rsp+2952], r11
	mov QWORD PTR [rsp+2960], r11
	mov QWORD PTR [rsp+2968], r11
	mov QWORD PTR [rsp+2976], r11
	mov QWORD PTR [rsp+2984], r11
	mov QWORD PTR [rsp+2992], r11
	mov QWORD PTR [rsp+3000], r11
	mov QWORD PTR [rsp+3008], r11
	mov QWORD PTR [rsp+3016], r11
	mov QWORD PTR [rsp+3024], r11
	mov QWORD PTR [rsp+3032], r11
	mov QWORD PTR [rsp+3040], r11
	mov QWORD PTR [rsp+3048], r11
	mov QWORD PTR [rsp+3056], r11
	mov QWORD PTR [rsp+3064], r11
	mov QWORD PTR [rsp+3072], r11
	mov QWORD PTR [rsp+3080], r11
	mov QWORD PTR [rsp+3088], r11
	mov QWORD PTR [rsp+3096], r11
	mov QWORD PTR [rsp+3104], r11
	mov QWORD PTR [rsp+3112], r11
	mov QWORD PTR [rsp+3120], r11
	mov QWORD PTR [rsp+3128], r11
	mov QWORD PTR [rsp+3136], r11
	mov QWORD PTR [rsp+3144], r11
	mov QWORD PTR [rsp+3152], r11
	mov QWORD PTR [rsp+3160], r11
	mov QWORD PTR [rsp+3168], r11
	mov QWORD PTR [rsp+3176], r11
	mov QWORD PTR [rsp+3184], r11
	mov QWORD PTR [rsp+3192], r11
	mov QWORD PTR [rsp+3200], r11
	mov QWORD PTR [rsp+3208], r11
	mov QWORD PTR [rsp+3216], r11
	mov QWORD PTR [rsp+3224], r11
	mov QWORD PTR [rsp+3232], r11
	mov QWORD PTR [rsp+3240], r11
	mov QWORD PTR [rsp+3248], r11
	mov QWORD PTR [rsp+3256], r11
	mov QWORD PTR [rsp+3264], r11
	mov QWORD PTR [rsp+3272], r11
	mov QWORD PTR [rsp+3280], r11
	mov QWORD PTR [rsp+3288], r11
	mov QWORD PTR [rsp+3296], r11
	mov QWORD PTR [rsp+3304], r11
	mov QWORD PTR [rsp+3312], r11
	mov QWORD PTR [rsp+3320], r11
	mov QWORD PTR [rsp+3328], r11
	mov QWORD PTR [rsp+3336], r11
	mov QWORD PTR [rsp+3344], r11
	mov QWORD PTR [rsp+3352], r11
	mov QWORD PTR [rsp+3360], r11
	mov QWORD PTR [rsp+3368], r11
	mov QWORD PTR [rsp+3376], r11
	mov QWORD PTR [rsp+3384], r11
	mov QWORD PTR [rsp+3392], r11
	mov QWORD PTR [rsp+3400], r11
	mov QWORD PTR [rsp+3408], r11
	lea rsp, [rsp+3416]
	jmp 21b
	.p2align 6

vg_hmac_sha384_finalize:
	lea rsp, [rsp-1880]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+1376], rbx
	mov QWORD PTR [r8+1384], rbp
	mov QWORD PTR [r8+1392], r12
	mov QWORD PTR [r8+1400], r13
	mov QWORD PTR [r8+1408], r14
	mov QWORD PTR [r8+1416], r15
	mov rbx, rdi
	mov r12, rsi
	mov r13, rcx
	mov r15, r8
	mov rsi, rdx
	mov rdx, r15
	add rdx, 1424
	mov rcx, r15
	call {vg_sha512_finalize_scratch}
	movdqu xmm0, XMMWORD PTR [r12]
	movdqu XMMWORD PTR [rbx], xmm0
	movdqu xmm0, XMMWORD PTR [r12+16]
	movdqu XMMWORD PTR [rbx+16], xmm0
	movdqu xmm0, XMMWORD PTR [r12+32]
	movdqu XMMWORD PTR [rbx+32], xmm0
	movdqu xmm0, XMMWORD PTR [r12+48]
	movdqu XMMWORD PTR [rbx+48], xmm0
	movdqu xmm0, XMMWORD PTR [r15+1424]
	movdqu XMMWORD PTR [rbx+64], xmm0
	movdqu xmm0, XMMWORD PTR [r15+1440]
	movdqu XMMWORD PTR [rbx+80], xmm0
	movdqu xmm0, XMMWORD PTR [r15+1456]
	movdqu XMMWORD PTR [rbx+96], xmm0
	mov rbp, rbx
	add rbp, 64
	mov eax, 128
	movq xmm1, rax
	movdqu XMMWORD PTR [rbp+48], xmm1
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rbp+64], xmm0
	movdqu XMMWORD PTR [rbp+80], xmm0
	movdqu XMMWORD PTR [rbp+96], xmm0
	mov r12d, 176
	mov rax, r12
	shr rax, 61
	bswap rax
	movq xmm7, rax
	mov rax, r12
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	movq xmm8, rax
	punpcklqdq xmm7, xmm8
	movdqu XMMWORD PTR [rbp+112], xmm7
	mov rsi, rbp
	mov rdi, rbx
	mov edx, 1
	mov rcx, r15
	call {vg_sha512_compress}
	mov rbx, rdi
	mov r15, rcx
	mov rax, QWORD PTR [rbx]
	bswap rax
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	bswap rax
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	bswap rax
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	bswap rax
	mov QWORD PTR [rbp+24], rax
	mov rax, QWORD PTR [rbx+32]
	bswap rax
	mov QWORD PTR [rbp+32], rax
	mov rax, QWORD PTR [rbx+40]
	bswap rax
	mov QWORD PTR [rbp+40], rax
	mov rax, QWORD PTR [rbx+48]
	bswap rax
	mov QWORD PTR [rbp+48], rax
	mov rax, QWORD PTR [rbx+56]
	bswap rax
	mov QWORD PTR [rbp+56], rax
	movdqu xmm0, XMMWORD PTR [rbp]
	movdqu XMMWORD PTR [r13], xmm0
	movdqu xmm0, XMMWORD PTR [rbp+16]
	movdqu XMMWORD PTR [r13+16], xmm0
	movdqu xmm0, XMMWORD PTR [rbp+32]
	movdqu XMMWORD PTR [r13+32], xmm0
	mov rbx, QWORD PTR [r15+1376]
	mov rbp, QWORD PTR [r15+1384]
	mov r12, QWORD PTR [r15+1392]
	mov r13, QWORD PTR [r15+1400]
	mov r14, QWORD PTR [r15+1408]
	mov r15, QWORD PTR [r15+1416]
	lea rsp, [rsp+1880]
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
	lea rsp, [rsp-1896]
	movdqu XMMWORD PTR [rsp+1512], xmm0
	movdqu XMMWORD PTR [rsp+1496], xmm0
	movdqu XMMWORD PTR [rsp+1480], xmm0
	movdqu XMMWORD PTR [rsp+1464], xmm0
	movdqu XMMWORD PTR [rsp+1448], xmm0
	movdqu XMMWORD PTR [rsp+136], xmm0
	movdqu XMMWORD PTR [rsp+120], xmm0
	movdqu XMMWORD PTR [rsp+104], xmm0
	movdqu XMMWORD PTR [rsp+88], xmm0
	movdqu XMMWORD PTR [rsp+72], xmm0
	movdqu XMMWORD PTR [rsp+56], xmm0
	movdqu XMMWORD PTR [rsp+40], xmm0
	movdqu XMMWORD PTR [rsp+24], xmm0
	movdqu XMMWORD PTR [rsp+8], xmm0
	lea rsp, [rsp+1896]
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
