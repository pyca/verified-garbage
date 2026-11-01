// The functions of `src/ecdsa_p384.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p384_verify:
	mov r8, rcx
	mov r9, rdi
	mov rcx, rdx
	mov r10, rdx
	add r10, 48
	mov rdx, rdi
	add rdx, 1
	mov QWORD PTR [r8], rbx
	mov QWORD PTR [r8+8], rbp
	mov QWORD PTR [r8+16], r12
	mov QWORD PTR [r8+24], r13
	mov QWORD PTR [r8+32], r14
	mov QWORD PTR [r8+40], r15
	mov r14, rdi
	mov rdi, r8
	mov rax, QWORD PTR [rcx+40]
	bswap rax
	mov QWORD PTR [rdi+1552], rax
	mov rax, QWORD PTR [rcx+32]
	bswap rax
	mov QWORD PTR [rdi+1560], rax
	mov rax, QWORD PTR [rcx+24]
	bswap rax
	mov QWORD PTR [rdi+1568], rax
	mov rax, QWORD PTR [rcx+16]
	bswap rax
	mov QWORD PTR [rdi+1576], rax
	mov rax, QWORD PTR [rcx+8]
	bswap rax
	mov QWORD PTR [rdi+1584], rax
	mov rax, QWORD PTR [rcx]
	bswap rax
	mov QWORD PTR [rdi+1592], rax
	mov rax, QWORD PTR [rsi+40]
	bswap rax
	mov QWORD PTR [rdi+1600], rax
	mov rax, QWORD PTR [rsi+32]
	bswap rax
	mov QWORD PTR [rdi+1608], rax
	mov rax, QWORD PTR [rsi+24]
	bswap rax
	mov QWORD PTR [rdi+1616], rax
	mov rax, QWORD PTR [rsi+16]
	bswap rax
	mov QWORD PTR [rdi+1624], rax
	mov rax, QWORD PTR [rsi+8]
	bswap rax
	mov QWORD PTR [rdi+1632], rax
	mov rax, QWORD PTR [rsi]
	bswap rax
	mov QWORD PTR [rdi+1640], rax
	mov rax, QWORD PTR [rdx+40]
	bswap rax
	mov QWORD PTR [rdi+1648], rax
	mov rax, QWORD PTR [rdx+32]
	bswap rax
	mov QWORD PTR [rdi+1656], rax
	mov rax, QWORD PTR [rdx+24]
	bswap rax
	mov QWORD PTR [rdi+1664], rax
	mov rax, QWORD PTR [rdx+16]
	bswap rax
	mov QWORD PTR [rdi+1672], rax
	mov rax, QWORD PTR [rdx+8]
	bswap rax
	mov QWORD PTR [rdi+1680], rax
	mov rax, QWORD PTR [rdx]
	bswap rax
	mov QWORD PTR [rdi+1688], rax
	movabs rax, 4294967295
	mov QWORD PTR [rdi+64], rax
	movabs rax, -4294967296
	mov QWORD PTR [rdi+72], rax
	movabs rax, -2
	mov QWORD PTR [rdi+80], rax
	movabs rax, -1
	mov QWORD PTR [rdi+88], rax
	movabs rax, -1
	mov QWORD PTR [rdi+96], rax
	movabs rax, -1
	mov QWORD PTR [rdi+104], rax
	movabs rax, -1374695839762142861
	mov QWORD PTR [rdi+112], rax
	movabs rax, 6348401684107011962
	mov QWORD PTR [rdi+120], rax
	movabs rax, -4079331616924160545
	mov QWORD PTR [rdi+128], rax
	movabs rax, -1
	mov QWORD PTR [rdi+136], rax
	movabs rax, -1
	mov QWORD PTR [rdi+144], rax
	movabs rax, -1
	mov QWORD PTR [rdi+152], rax
	movabs rax, 0
	mov QWORD PTR [rdi+208], rax
	movabs rax, 0
	mov QWORD PTR [rdi+216], rax
	movabs rax, 0
	mov QWORD PTR [rdi+224], rax
	movabs rax, 0
	mov QWORD PTR [rdi+232], rax
	movabs rax, 0
	mov QWORD PTR [rdi+240], rax
	movabs rax, 0
	mov QWORD PTR [rdi+248], rax
	movabs rax, 1
	mov QWORD PTR [rdi+256], rax
	movabs rax, 0
	mov QWORD PTR [rdi+264], rax
	movabs rax, 0
	mov QWORD PTR [rdi+272], rax
	movabs rax, 0
	mov QWORD PTR [rdi+280], rax
	movabs rax, 0
	mov QWORD PTR [rdi+288], rax
	movabs rax, 0
	mov QWORD PTR [rdi+296], rax
	movabs rax, -4294967295
	mov QWORD PTR [rdi+304], rax
	movabs rax, 4294967295
	mov QWORD PTR [rdi+312], rax
	movabs rax, 1
	mov QWORD PTR [rdi+320], rax
	movabs rax, 0
	mov QWORD PTR [rdi+328], rax
	movabs rax, 0
	mov QWORD PTR [rdi+336], rax
	movabs rax, 0
	mov QWORD PTR [rdi+344], rax
	movabs rax, 17179869180
	mov QWORD PTR [rdi+352], rax
	movabs rax, -17179869184
	mov QWORD PTR [rdi+360], rax
	movabs rax, -5
	mov QWORD PTR [rdi+368], rax
	movabs rax, -1
	mov QWORD PTR [rdi+376], rax
	movabs rax, -1
	mov QWORD PTR [rdi+384], rax
	movabs rax, -1
	mov QWORD PTR [rdi+392], rax
	movabs rax, 1744187536785508710
	mov QWORD PTR [rdi+400], rax
	movabs rax, -1910360172469643068
	mov QWORD PTR [rdi+408], rax
	movabs rax, 7482275382463301262
	mov QWORD PTR [rdi+416], rax
	movabs rax, -6222316845941481305
	mov QWORD PTR [rdi+424], rax
	movabs rax, 2486380466413134270
	mov QWORD PTR [rdi+432], rax
	movabs rax, 7428744631655809005
	mov QWORD PTR [rdi+440], rax
	movabs rax, 4454189113653900584
	mov QWORD PTR [rdi+448], rax
	movabs rax, 2369870743683386936
	mov QWORD PTR [rdi+456], rax
	movabs rax, -8674993926805172882
	mov QWORD PTR [rdi+464], rax
	movabs rax, 7229551204834152191
	mov QWORD PTR [rdi+472], rax
	movabs rax, -9137813387582972373
	mov QWORD PTR [rdi+480], rax
	movabs rax, 5564951339003155731
	mov QWORD PTR [rdi+488], rax
	movabs rax, 2523209505731486974
	mov QWORD PTR [rdi+496], rax
	movabs rax, -6791524172683761236
	mov QWORD PTR [rdi+504], rax
	movabs rax, -8381788974133039024
	mov QWORD PTR [rdi+512], rax
	movabs rax, -4124362564652695591
	mov QWORD PTR [rdi+520], rax
	movabs rax, -2485984631113275328
	mov QWORD PTR [rdi+528], rax
	movabs rax, 3132442392059561449
	mov QWORD PTR [rdi+536], rax
	movabs rax, 3256554584917936553
	mov QWORD PTR [rdi+544], rax
	movabs rax, -54744796168018919
	mov QWORD PTR [rdi+552], rax
	movabs rax, -4882385527837808313
	mov QWORD PTR [rdi+560], rax
	movabs rax, -3166794598585787195
	mov QWORD PTR [rdi+568], rax
	movabs rax, 4589268600508278933
	mov QWORD PTR [rdi+576], rax
	movabs rax, 902107514168524577
	mov QWORD PTR [rdi+584], rax
	movabs rax, 1374695839762142861
	mov QWORD PTR [rdi+592], rax
	movabs rax, -6348401684107011963
	mov QWORD PTR [rdi+600], rax
	movabs rax, 4079331616924160544
	mov QWORD PTR [rdi+608], rax
	movabs rax, 0
	mov QWORD PTR [rdi+616], rax
	movabs rax, 0
	mov QWORD PTR [rdi+624], rax
	movabs rax, 0
	mov QWORD PTR [rdi+632], rax
	movabs rax, 4294967293
	mov QWORD PTR [rdi+640], rax
	movabs rax, -4294967296
	mov QWORD PTR [rdi+648], rax
	movabs rax, -2
	mov QWORD PTR [rdi+656], rax
	movabs rax, -1
	mov QWORD PTR [rdi+664], rax
	movabs rax, -1
	mov QWORD PTR [rdi+672], rax
	movabs rax, -1
	mov QWORD PTR [rdi+680], rax
	movabs rax, -1374695839762142863
	mov QWORD PTR [rdi+688], rax
	movabs rax, 6348401684107011962
	mov QWORD PTR [rdi+696], rax
	movabs rax, -4079331616924160545
	mov QWORD PTR [rdi+704], rax
	movabs rax, -1
	mov QWORD PTR [rdi+712], rax
	movabs rax, -1
	mov QWORD PTR [rdi+720], rax
	movabs rax, -1
	mov QWORD PTR [rdi+728], rax
	movabs rax, 0
	mov QWORD PTR [rdi+736], rax
	movabs rax, 0
	mov QWORD PTR [rdi+744], rax
	movabs rax, 0
	mov QWORD PTR [rdi+752], rax
	movabs rax, 0
	mov QWORD PTR [rdi+760], rax
	movabs rax, 0
	mov QWORD PTR [rdi+768], rax
	movabs rax, 0
	mov QWORD PTR [rdi+776], rax
	movabs rax, -4294967295
	mov QWORD PTR [rdi+784], rax
	movabs rax, 4294967295
	mov QWORD PTR [rdi+792], rax
	movabs rax, 1
	mov QWORD PTR [rdi+800], rax
	movabs rax, 0
	mov QWORD PTR [rdi+808], rax
	movabs rax, 0
	mov QWORD PTR [rdi+816], rax
	movabs rax, 0
	mov QWORD PTR [rdi+824], rax
	movabs rax, 0
	mov QWORD PTR [rdi+832], rax
	movabs rax, 0
	mov QWORD PTR [rdi+840], rax
	movabs rax, 0
	mov QWORD PTR [rdi+848], rax
	movabs rax, 0
	mov QWORD PTR [rdi+856], rax
	movabs rax, 0
	mov QWORD PTR [rdi+864], rax
	movabs rax, 0
	mov QWORD PTR [rdi+872], rax
	movabs rax, -1
	mov QWORD PTR [rdi+2176], rax
	mov rsi, r14
	mov ebx, 0
20:
	movzx eax, BYTE PTR [rdi+rbx*1+1552]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2224], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2225], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2226], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2227], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2228], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2229], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2230], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2231], dl
	add rbx, 1
	cmp rbx, 48
	jne 20b
	mov ebx, 0
21:
	movzx eax, BYTE PTR [rdi+rbx*1+640]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2616], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2617], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2618], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2619], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2620], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2621], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2622], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2623], dl
	add rbx, 1
	cmp rbx, 48
	jne 21b
	mov ebx, 0
22:
	movzx eax, BYTE PTR [rdi+rbx*1+688]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3008], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3009], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3010], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3011], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3012], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3013], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3014], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3015], dl
	add rbx, 1
	cmp rbx, 48
	jne 22b
	mov rax, QWORD PTR [r10+40]
	bswap rax
	mov QWORD PTR [rdi+1504], rax
	mov rax, QWORD PTR [r10+32]
	bswap rax
	mov QWORD PTR [rdi+1512], rax
	mov rax, QWORD PTR [r10+24]
	bswap rax
	mov QWORD PTR [rdi+1520], rax
	mov rax, QWORD PTR [r10+16]
	bswap rax
	mov QWORD PTR [rdi+1528], rax
	mov rax, QWORD PTR [r10+8]
	bswap rax
	mov QWORD PTR [rdi+1536], rax
	mov rax, QWORD PTR [r10]
	bswap rax
	mov QWORD PTR [rdi+1544], rax
	movabs rax, -8589934591
	mov QWORD PTR [rdi+1936], rax
	movabs rax, 8589934592
	mov QWORD PTR [rdi+1944], rax
	movabs rax, -8589934592
	mov QWORD PTR [rdi+1952], rax
	movabs rax, 8589934592
	mov QWORD PTR [rdi+1960], rax
	movabs rax, 1
	mov QWORD PTR [rdi+1968], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1976], rax
	movabs rax, 581395848458481100
	mov QWORD PTR [rdi+1984], rax
	movabs rax, -636786727019859220
	mov QWORD PTR [rdi+1992], rax
	movabs rax, 8643006485390950958
	mov QWORD PTR [rdi+2000], rax
	movabs rax, -2074105615313827102
	mov QWORD PTR [rdi+2008], rax
	movabs rax, -5320121202432139116
	mov QWORD PTR [rdi+2016], rax
	movabs rax, -3672666480684580871
	mov QWORD PTR [rdi+2024], rax
	mov rdx, r9
	add rdx, 49
	mov rax, QWORD PTR [rdx+40]
	bswap rax
	mov QWORD PTR [rdi+1792], rax
	mov rax, QWORD PTR [rdx+32]
	bswap rax
	mov QWORD PTR [rdi+1800], rax
	mov rax, QWORD PTR [rdx+24]
	bswap rax
	mov QWORD PTR [rdi+1808], rax
	mov rax, QWORD PTR [rdx+16]
	bswap rax
	mov QWORD PTR [rdi+1816], rax
	mov rax, QWORD PTR [rdx+8]
	bswap rax
	mov QWORD PTR [rdi+1824], rax
	mov rax, QWORD PTR [rdx]
	bswap rax
	mov QWORD PTR [rdi+1832], rax
	movzx edx, BYTE PTR [r9]
	xor rdx, 4
	cmp rdx, 1
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+2176]
	and rax, rdx
	mov QWORD PTR [rdi+2176], rax
	call {vg_p384_check_point}
	mov rdx, QWORD PTR [rdi+1552]
	sub rdx, QWORD PTR [rdi+112]
	mov rdx, QWORD PTR [rdi+1560]
	sbb rdx, QWORD PTR [rdi+120]
	mov rdx, QWORD PTR [rdi+1568]
	sbb rdx, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rdi+1576]
	sbb rdx, QWORD PTR [rdi+136]
	mov rdx, QWORD PTR [rdi+1584]
	sbb rdx, QWORD PTR [rdi+144]
	mov rdx, QWORD PTR [rdi+1592]
	sbb rdx, QWORD PTR [rdi+152]
	sbb rax, rax
	mov rbp, rax
	mov rdx, QWORD PTR [rdi+1552]
	or rdx, QWORD PTR [rdi+1560]
	or rdx, QWORD PTR [rdi+1568]
	or rdx, QWORD PTR [rdi+1576]
	or rdx, QWORD PTR [rdi+1584]
	or rdx, QWORD PTR [rdi+1592]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	and rdx, rbp
	mov rax, QWORD PTR [rdi+2176]
	and rax, rdx
	mov QWORD PTR [rdi+2176], rax
	mov rdx, QWORD PTR [rdi+1504]
	sub rdx, QWORD PTR [rdi+112]
	mov rdx, QWORD PTR [rdi+1512]
	sbb rdx, QWORD PTR [rdi+120]
	mov rdx, QWORD PTR [rdi+1520]
	sbb rdx, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rdi+1528]
	sbb rdx, QWORD PTR [rdi+136]
	mov rdx, QWORD PTR [rdi+1536]
	sbb rdx, QWORD PTR [rdi+144]
	mov rdx, QWORD PTR [rdi+1544]
	sbb rdx, QWORD PTR [rdi+152]
	sbb rax, rax
	mov rbp, rax
	mov rdx, QWORD PTR [rdi+1504]
	or rdx, QWORD PTR [rdi+1512]
	or rdx, QWORD PTR [rdi+1520]
	or rdx, QWORD PTR [rdi+1528]
	or rdx, QWORD PTR [rdi+1536]
	or rdx, QWORD PTR [rdi+1544]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	and rdx, rbp
	mov rax, QWORD PTR [rdi+2176]
	and rax, rdx
	mov QWORD PTR [rdi+2176], rax
	mov r12, rsi
	mov esi, 1840
	mov edx, 1504
	mov ecx, 544
	call {vg_p384_mul_mod_n}
	mov rsi, r12
	call {vg_p384_inv_mod_n}
	mov r12, rsi
	mov esi, 1984
	mov edx, 1600
	mov ecx, 544
	call {vg_p384_mul_mod_n}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1936
	mov edx, 1552
	mov ecx, 544
	call {vg_p384_mul_mod_n}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2032
	mov edx, 1984
	mov ecx, 1456
	call {vg_p384_mul_mod_n}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2080
	mov edx, 1936
	mov ecx, 1456
	call {vg_p384_mul_mod_n}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1696
	mov edx, 2032
	mov ecx, 256
	call {vg_p384_mul_mod_n}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1744
	mov edx, 2080
	mov ecx, 256
	call {vg_p384_mul_mod_n}
	mov rsi, r12
	mov r8, QWORD PTR [rdi+1696]
	mov r9, QWORD PTR [rdi+1704]
	mov r10, QWORD PTR [rdi+1712]
	mov r11, QWORD PTR [rdi+1720]
	mov r12, QWORD PTR [rdi+1728]
	mov r13, QWORD PTR [rdi+1736]
	mov r14d, 0
	mov ebx, 0
	movabs rax, 0
	mov QWORD PTR [rdi+6400], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6408], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6416], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6424], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6432], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6440], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6448], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6456], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6464], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6472], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6480], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6488], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6496], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6504], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6512], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6520], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6528], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6536], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6544], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6552], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6560], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6568], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6576], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6584], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6592], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6600], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6608], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6616], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6624], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6632], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6640], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6648], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6656], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6664], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6672], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6680], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6688], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6696], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6704], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6712], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6720], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6728], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6736], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6744], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6752], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6760], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6768], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6776], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6784], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6792], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6800], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6808], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6816], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6824], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6832], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6840], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6848], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6856], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6864], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6872], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6880], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6888], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6896], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6904], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6912], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6920], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6928], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6936], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6944], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6952], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6960], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6968], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6976], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6984], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6992], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7000], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7008], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7016], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7024], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7032], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7040], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7048], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7056], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7064], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7072], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7080], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7088], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7096], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7104], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7112], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7120], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7128], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7136], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7144], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7152], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7160], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7168], rax
23:
	mov rcx, r8
	and rcx, 1
	test rcx, rcx
	je 24f
	mov rcx, r8
	and rcx, 511
	cmp rcx, 256
	jb 26f
	sub rcx, 512
	jmp 27f
26:
27:
	mov rax, rcx
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	sub r8, rcx
	sbb r9, rdx
	sbb r10, rdx
	sbb r11, rdx
	sbb r12, rdx
	sbb r13, rdx
	sbb r14, rdx
	mov WORD PTR [rdi+rbx*2+6400], cx
	shr r8, 9
	mov rax, r9
	shl rax, 55
	or r8, rax
	shr r9, 9
	mov rax, r10
	shl rax, 55
	or r9, rax
	shr r10, 9
	mov rax, r11
	shl rax, 55
	or r10, rax
	shr r11, 9
	mov rax, r12
	shl rax, 55
	or r11, rax
	shr r12, 9
	mov rax, r13
	shl rax, 55
	or r12, rax
	shr r13, 9
	mov rax, r14
	shl rax, 55
	or r13, rax
	shr r14, 9
	add rbx, 9
	jmp 25f
24:
	shr r8, 1
	mov rax, r9
	shl rax, 63
	or r8, rax
	shr r9, 1
	mov rax, r10
	shl rax, 63
	or r9, rax
	shr r10, 1
	mov rax, r11
	shl rax, 63
	or r10, rax
	shr r11, 1
	mov rax, r12
	shl rax, 63
	or r11, rax
	shr r12, 1
	mov rax, r13
	shl rax, 63
	or r12, rax
	shr r13, 1
	mov rax, r14
	shl rax, 63
	or r13, rax
	shr r14, 1
	add rbx, 1
25:
	cmp rbx, 385
	jb 23b
	mov r8, QWORD PTR [rdi+1744]
	mov r9, QWORD PTR [rdi+1752]
	mov r10, QWORD PTR [rdi+1760]
	mov r11, QWORD PTR [rdi+1768]
	mov r12, QWORD PTR [rdi+1776]
	mov r13, QWORD PTR [rdi+1784]
	mov r14d, 0
	mov ebx, 0
	movabs rax, 0
	mov QWORD PTR [rdi+3568], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3576], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3584], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3592], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3600], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3608], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3616], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3624], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3632], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3640], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3648], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3656], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3664], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3672], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3680], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3688], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3696], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3704], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3712], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3720], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3728], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3736], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3744], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3752], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3760], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3768], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3776], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3784], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3792], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3800], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3808], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3816], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3824], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3832], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3840], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3848], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3856], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3864], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3872], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3880], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3888], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3896], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3904], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3912], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3920], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3928], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3936], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3944], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3952], rax
28:
	mov rcx, r8
	and rcx, 1
	test rcx, rcx
	je 29f
	mov rcx, r8
	and rcx, 31
	cmp rcx, 16
	jb 211f
	sub rcx, 32
	jmp 212f
211:
212:
	mov rax, rcx
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	sub r8, rcx
	sbb r9, rdx
	sbb r10, rdx
	sbb r11, rdx
	sbb r12, rdx
	sbb r13, rdx
	sbb r14, rdx
	mov BYTE PTR [rdi+rbx*1+3568], cl
	shr r8, 5
	mov rax, r9
	shl rax, 59
	or r8, rax
	shr r9, 5
	mov rax, r10
	shl rax, 59
	or r9, rax
	shr r10, 5
	mov rax, r11
	shl rax, 59
	or r10, rax
	shr r11, 5
	mov rax, r12
	shl rax, 59
	or r11, rax
	shr r12, 5
	mov rax, r13
	shl rax, 59
	or r12, rax
	shr r13, 5
	mov rax, r14
	shl rax, 59
	or r13, rax
	shr r14, 5
	add rbx, 5
	jmp 210f
29:
	shr r8, 1
	mov rax, r9
	shl rax, 63
	or r8, rax
	shr r9, 1
	mov rax, r10
	shl rax, 63
	or r9, rax
	shr r10, 1
	mov rax, r11
	shl rax, 63
	or r10, rax
	shr r11, 1
	mov rax, r12
	shl rax, 63
	or r11, rax
	shr r12, 1
	mov rax, r13
	shl rax, 63
	or r12, rax
	shr r13, 1
	mov rax, r14
	shl rax, 63
	or r13, rax
	shr r14, 1
	add rbx, 1
210:
	cmp rbx, 385
	jb 28b
	mov rax, QWORD PTR [rdi+1888]
	mov QWORD PTR [rdi+4096], rax
	mov rax, QWORD PTR [rdi+1896]
	mov QWORD PTR [rdi+4104], rax
	mov rax, QWORD PTR [rdi+1904]
	mov QWORD PTR [rdi+4112], rax
	mov rax, QWORD PTR [rdi+1912]
	mov QWORD PTR [rdi+4120], rax
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rdi+4128], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rdi+4136], rax
	mov rax, QWORD PTR [rdi+2128]
	mov QWORD PTR [rdi+4144], rax
	mov rax, QWORD PTR [rdi+2136]
	mov QWORD PTR [rdi+4152], rax
	mov rax, QWORD PTR [rdi+2144]
	mov QWORD PTR [rdi+4160], rax
	mov rax, QWORD PTR [rdi+2152]
	mov QWORD PTR [rdi+4168], rax
	mov rax, QWORD PTR [rdi+2160]
	mov QWORD PTR [rdi+4176], rax
	mov rax, QWORD PTR [rdi+2168]
	mov QWORD PTR [rdi+4184], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+4192], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+4200], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+4208], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+4216], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+4224], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+4232], rax
	mov ebx, 1
	mov rcx, QWORD PTR [rdi+1888]
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1896]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1920]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1928]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov r13, rbp
	mov QWORD PTR [rdi+4056], r8
	mov QWORD PTR [rdi+4064], r9
	mov rcx, QWORD PTR [rdi+1896]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1904]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1920]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1928]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov r14, rbp
	mov rcx, QWORD PTR [rdi+1904]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1912]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1920]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1928]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov r15, rbp
	mov rcx, QWORD PTR [rdi+1912]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1920]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1928]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov r8, rbp
	mov rcx, QWORD PTR [rdi+1920]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1928]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov r9, rbp
	mov rax, QWORD PTR [rdi+4056]
	add rax, rax
	mov QWORD PTR [rdi+4056], rax
	mov rax, QWORD PTR [rdi+4064]
	adc rax, rax
	mov QWORD PTR [rdi+4064], rax
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	adc r8, r8
	adc r9, r9
	mov ecx, 0
	adc rcx, rcx
	mov rax, QWORD PTR [rdi+1888]
	mul rax
	mov QWORD PTR [rdi+4048], rax
	add rdx, QWORD PTR [rdi+4056]
	mov QWORD PTR [rdi+4056], rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1896]
	mul rax
	add rax, rbp
	adc rdx, 0
	add rax, QWORD PTR [rdi+4064]
	mov QWORD PTR [rdi+4064], rax
	adc r10, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1904]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc r12, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1912]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc r14, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1920]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc r8, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1928]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rcx, rdx
	mov ebp, 0
	adc rbp, 0
	mov QWORD PTR [rdi+1168], r13
	mov QWORD PTR [rdi+1176], r14
	mov QWORD PTR [rdi+1184], r15
	mov QWORD PTR [rdi+1192], r8
	mov QWORD PTR [rdi+1200], r9
	mov QWORD PTR [rdi+1208], rcx
	mov r13, QWORD PTR [rdi+4048]
	mov r14, QWORD PTR [rdi+4056]
	mov r15, QWORD PTR [rdi+4064]
	mov rcx, r13
	shl rcx, 32
	add rcx, r13
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r13d, 0
	adc r13, 0
	sub r14, rbp
	sbb r15, rdx
	sbb r10, r13
	sbb r11, 0
	sbb r12, 0
	mov r13, rcx
	sbb r13, 0
	mov rcx, r14
	shl rcx, 32
	add rcx, r14
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r14d, 0
	adc r14, 0
	sub r15, rbp
	sbb r10, rdx
	sbb r11, r14
	sbb r12, 0
	sbb r13, 0
	mov r14, rcx
	sbb r14, 0
	mov rcx, r15
	shl rcx, 32
	add rcx, r15
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r15d, 0
	adc r15, 0
	sub r10, rbp
	sbb r11, rdx
	sbb r12, r15
	sbb r13, 0
	sbb r14, 0
	mov r15, rcx
	sbb r15, 0
	mov rcx, r10
	shl rcx, 32
	add rcx, r10
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r10d, 0
	adc r10, 0
	sub r11, rbp
	sbb r12, rdx
	sbb r13, r10
	sbb r14, 0
	sbb r15, 0
	mov r10, rcx
	sbb r10, 0
	mov rcx, r11
	shl rcx, 32
	add rcx, r11
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r11d, 0
	adc r11, 0
	sub r12, rbp
	sbb r13, rdx
	sbb r14, r11
	sbb r15, 0
	sbb r10, 0
	mov r11, rcx
	sbb r11, 0
	mov rcx, r12
	shl rcx, 32
	add rcx, r12
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r12d, 0
	adc r12, 0
	sub r13, rbp
	sbb r14, rdx
	sbb r15, r12
	sbb r10, 0
	sbb r11, 0
	mov r12, rcx
	sbb r12, 0
	mov r8d, 0
	add r13, QWORD PTR [rdi+1168]
	adc r14, QWORD PTR [rdi+1176]
	adc r15, QWORD PTR [rdi+1184]
	adc r10, QWORD PTR [rdi+1192]
	adc r11, QWORD PTR [rdi+1200]
	adc r12, QWORD PTR [rdi+1208]
	adc r8, 0
	sub r13, QWORD PTR [rdi+64]
	sbb r14, QWORD PTR [rdi+72]
	sbb r15, QWORD PTR [rdi+80]
	sbb r10, QWORD PTR [rdi+88]
	sbb r11, QWORD PTR [rdi+96]
	sbb r12, QWORD PTR [rdi+104]
	sbb r8, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r13, rcx
	adc r14, rdx
	adc r15, rbp
	adc r10, rax
	adc r11, rax
	adc r12, rax
	mov QWORD PTR [rdi+1168], r13
	mov QWORD PTR [rdi+1176], r14
	mov QWORD PTR [rdi+1184], r15
	mov QWORD PTR [rdi+1192], r10
	mov QWORD PTR [rdi+1200], r11
	mov QWORD PTR [rdi+1208], r12
	mov rcx, QWORD PTR [rdi+2128]
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov ebp, 0
	mov rax, QWORD PTR [rdi+2136]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2144]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2152]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2160]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2168]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov r13, rbp
	mov QWORD PTR [rdi+4056], r8
	mov QWORD PTR [rdi+4064], r9
	mov rcx, QWORD PTR [rdi+2136]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+2144]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2152]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2160]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2168]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov r14, rbp
	mov rcx, QWORD PTR [rdi+2144]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+2152]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2160]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2168]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov r15, rbp
	mov rcx, QWORD PTR [rdi+2152]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+2160]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2168]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov r8, rbp
	mov rcx, QWORD PTR [rdi+2160]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+2168]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov r9, rbp
	mov rax, QWORD PTR [rdi+4056]
	add rax, rax
	mov QWORD PTR [rdi+4056], rax
	mov rax, QWORD PTR [rdi+4064]
	adc rax, rax
	mov QWORD PTR [rdi+4064], rax
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	adc r8, r8
	adc r9, r9
	mov ecx, 0
	adc rcx, rcx
	mov rax, QWORD PTR [rdi+2128]
	mul rax
	mov QWORD PTR [rdi+4048], rax
	add rdx, QWORD PTR [rdi+4056]
	mov QWORD PTR [rdi+4056], rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+2136]
	mul rax
	add rax, rbp
	adc rdx, 0
	add rax, QWORD PTR [rdi+4064]
	mov QWORD PTR [rdi+4064], rax
	adc r10, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+2144]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc r12, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+2152]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc r14, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+2160]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc r8, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+2168]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rcx, rdx
	mov ebp, 0
	adc rbp, 0
	mov QWORD PTR [rdi+1216], r13
	mov QWORD PTR [rdi+1224], r14
	mov QWORD PTR [rdi+1232], r15
	mov QWORD PTR [rdi+1240], r8
	mov QWORD PTR [rdi+1248], r9
	mov QWORD PTR [rdi+1256], rcx
	mov r13, QWORD PTR [rdi+4048]
	mov r14, QWORD PTR [rdi+4056]
	mov r15, QWORD PTR [rdi+4064]
	mov rcx, r13
	shl rcx, 32
	add rcx, r13
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r13d, 0
	adc r13, 0
	sub r14, rbp
	sbb r15, rdx
	sbb r10, r13
	sbb r11, 0
	sbb r12, 0
	mov r13, rcx
	sbb r13, 0
	mov rcx, r14
	shl rcx, 32
	add rcx, r14
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r14d, 0
	adc r14, 0
	sub r15, rbp
	sbb r10, rdx
	sbb r11, r14
	sbb r12, 0
	sbb r13, 0
	mov r14, rcx
	sbb r14, 0
	mov rcx, r15
	shl rcx, 32
	add rcx, r15
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r15d, 0
	adc r15, 0
	sub r10, rbp
	sbb r11, rdx
	sbb r12, r15
	sbb r13, 0
	sbb r14, 0
	mov r15, rcx
	sbb r15, 0
	mov rcx, r10
	shl rcx, 32
	add rcx, r10
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r10d, 0
	adc r10, 0
	sub r11, rbp
	sbb r12, rdx
	sbb r13, r10
	sbb r14, 0
	sbb r15, 0
	mov r10, rcx
	sbb r10, 0
	mov rcx, r11
	shl rcx, 32
	add rcx, r11
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r11d, 0
	adc r11, 0
	sub r12, rbp
	sbb r13, rdx
	sbb r14, r11
	sbb r15, 0
	sbb r10, 0
	mov r11, rcx
	sbb r11, 0
	mov rcx, r12
	shl rcx, 32
	add rcx, r12
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r12d, 0
	adc r12, 0
	sub r13, rbp
	sbb r14, rdx
	sbb r15, r12
	sbb r10, 0
	sbb r11, 0
	mov r12, rcx
	sbb r12, 0
	mov r8d, 0
	add r13, QWORD PTR [rdi+1216]
	adc r14, QWORD PTR [rdi+1224]
	adc r15, QWORD PTR [rdi+1232]
	adc r10, QWORD PTR [rdi+1240]
	adc r11, QWORD PTR [rdi+1248]
	adc r12, QWORD PTR [rdi+1256]
	adc r8, 0
	sub r13, QWORD PTR [rdi+64]
	sbb r14, QWORD PTR [rdi+72]
	sbb r15, QWORD PTR [rdi+80]
	sbb r10, QWORD PTR [rdi+88]
	sbb r11, QWORD PTR [rdi+96]
	sbb r12, QWORD PTR [rdi+104]
	sbb r8, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r13, rcx
	adc r14, rdx
	adc r15, rbp
	adc r10, rax
	adc r11, rax
	adc r12, rax
	mov QWORD PTR [rdi+1216], r13
	mov QWORD PTR [rdi+1224], r14
	mov QWORD PTR [rdi+1232], r15
	mov QWORD PTR [rdi+1240], r10
	mov QWORD PTR [rdi+1248], r11
	mov QWORD PTR [rdi+1256], r12
	mov rcx, QWORD PTR [rdi+1216]
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov r13, rbp
	mov QWORD PTR [rdi+4056], r8
	mov QWORD PTR [rdi+4064], r9
	mov rcx, QWORD PTR [rdi+1224]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov r14, rbp
	mov rcx, QWORD PTR [rdi+1232]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov r15, rbp
	mov rcx, QWORD PTR [rdi+1240]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov r8, rbp
	mov rcx, QWORD PTR [rdi+1248]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov r9, rbp
	mov rax, QWORD PTR [rdi+4056]
	add rax, rax
	mov QWORD PTR [rdi+4056], rax
	mov rax, QWORD PTR [rdi+4064]
	adc rax, rax
	mov QWORD PTR [rdi+4064], rax
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	adc r8, r8
	adc r9, r9
	mov ecx, 0
	adc rcx, rcx
	mov rax, QWORD PTR [rdi+1216]
	mul rax
	mov QWORD PTR [rdi+4048], rax
	add rdx, QWORD PTR [rdi+4056]
	mov QWORD PTR [rdi+4056], rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1224]
	mul rax
	add rax, rbp
	adc rdx, 0
	add rax, QWORD PTR [rdi+4064]
	mov QWORD PTR [rdi+4064], rax
	adc r10, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1232]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc r12, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1240]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc r14, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1248]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc r8, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1256]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rcx, rdx
	mov ebp, 0
	adc rbp, 0
	mov QWORD PTR [rdi+784], r13
	mov QWORD PTR [rdi+792], r14
	mov QWORD PTR [rdi+800], r15
	mov QWORD PTR [rdi+808], r8
	mov QWORD PTR [rdi+816], r9
	mov QWORD PTR [rdi+824], rcx
	mov r13, QWORD PTR [rdi+4048]
	mov r14, QWORD PTR [rdi+4056]
	mov r15, QWORD PTR [rdi+4064]
	mov rcx, r13
	shl rcx, 32
	add rcx, r13
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r13d, 0
	adc r13, 0
	sub r14, rbp
	sbb r15, rdx
	sbb r10, r13
	sbb r11, 0
	sbb r12, 0
	mov r13, rcx
	sbb r13, 0
	mov rcx, r14
	shl rcx, 32
	add rcx, r14
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r14d, 0
	adc r14, 0
	sub r15, rbp
	sbb r10, rdx
	sbb r11, r14
	sbb r12, 0
	sbb r13, 0
	mov r14, rcx
	sbb r14, 0
	mov rcx, r15
	shl rcx, 32
	add rcx, r15
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r15d, 0
	adc r15, 0
	sub r10, rbp
	sbb r11, rdx
	sbb r12, r15
	sbb r13, 0
	sbb r14, 0
	mov r15, rcx
	sbb r15, 0
	mov rcx, r10
	shl rcx, 32
	add rcx, r10
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r10d, 0
	adc r10, 0
	sub r11, rbp
	sbb r12, rdx
	sbb r13, r10
	sbb r14, 0
	sbb r15, 0
	mov r10, rcx
	sbb r10, 0
	mov rcx, r11
	shl rcx, 32
	add rcx, r11
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r11d, 0
	adc r11, 0
	sub r12, rbp
	sbb r13, rdx
	sbb r14, r11
	sbb r15, 0
	sbb r10, 0
	mov r11, rcx
	sbb r11, 0
	mov rcx, r12
	shl rcx, 32
	add rcx, r12
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r12d, 0
	adc r12, 0
	sub r13, rbp
	sbb r14, rdx
	sbb r15, r12
	sbb r10, 0
	sbb r11, 0
	mov r12, rcx
	sbb r12, 0
	mov r8d, 0
	add r13, QWORD PTR [rdi+784]
	adc r14, QWORD PTR [rdi+792]
	adc r15, QWORD PTR [rdi+800]
	adc r10, QWORD PTR [rdi+808]
	adc r11, QWORD PTR [rdi+816]
	adc r12, QWORD PTR [rdi+824]
	adc r8, 0
	sub r13, QWORD PTR [rdi+64]
	sbb r14, QWORD PTR [rdi+72]
	sbb r15, QWORD PTR [rdi+80]
	sbb r10, QWORD PTR [rdi+88]
	sbb r11, QWORD PTR [rdi+96]
	sbb r12, QWORD PTR [rdi+104]
	sbb r8, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r13, rcx
	adc r14, rdx
	adc r15, rbp
	adc r10, rax
	adc r11, rax
	adc r12, rax
	mov QWORD PTR [rdi+784], r13
	mov QWORD PTR [rdi+792], r14
	mov QWORD PTR [rdi+800], r15
	mov QWORD PTR [rdi+808], r10
	mov QWORD PTR [rdi+816], r11
	mov QWORD PTR [rdi+824], r12
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1888]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, r8
	shl rcx, 32
	add rcx, r8
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r8d, 0
	adc r8, 0
	sub r9, rbp
	sbb r10, rdx
	sbb r11, r8
	sbb r12, 0
	sbb r13, 0
	sbb rcx, 0
	add r14, rcx
	adc r15, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+1896]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, r9
	shl rcx, 32
	add rcx, r9
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r9d, 0
	adc r9, 0
	sub r10, rbp
	sbb r11, rdx
	sbb r12, r9
	sbb r13, 0
	sbb r14, 0
	sbb rcx, 0
	add r15, rcx
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1904]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, r10
	shl rcx, 32
	add rcx, r10
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r10d, 0
	adc r10, 0
	sub r11, rbp
	sbb r12, rdx
	sbb r13, r10
	sbb r14, 0
	sbb r15, 0
	sbb rcx, 0
	add r8, rcx
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1912]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, r11
	shl rcx, 32
	add rcx, r11
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r11d, 0
	adc r11, 0
	sub r12, rbp
	sbb r13, rdx
	sbb r14, r11
	sbb r15, 0
	sbb r8, 0
	sbb rcx, 0
	add r9, rcx
	adc r10, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1920]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, r12
	shl rcx, 32
	add rcx, r12
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r12d, 0
	adc r12, 0
	sub r13, rbp
	sbb r14, rdx
	sbb r15, r12
	sbb r8, 0
	sbb r9, 0
	sbb rcx, 0
	add r10, rcx
	adc r11, 0
	mov r12d, 0
	mov rcx, QWORD PTR [rdi+1928]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rcx, r13
	shl rcx, 32
	add rcx, r13
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r13d, 0
	adc r13, 0
	sub r14, rbp
	sbb r15, rdx
	sbb r8, r13
	sbb r9, 0
	sbb r10, 0
	sbb rcx, 0
	add r11, rcx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+736], r14
	mov QWORD PTR [rdi+744], r15
	mov QWORD PTR [rdi+752], r8
	mov QWORD PTR [rdi+760], r9
	mov QWORD PTR [rdi+768], r10
	mov QWORD PTR [rdi+776], r11
	mov r8, QWORD PTR [rdi+736]
	mov r9, QWORD PTR [rdi+744]
	mov r10, QWORD PTR [rdi+752]
	mov r11, QWORD PTR [rdi+760]
	mov r12, QWORD PTR [rdi+768]
	mov r13, QWORD PTR [rdi+776]
	mov r14d, 0
	add r8, QWORD PTR [rdi+736]
	adc r9, QWORD PTR [rdi+744]
	adc r10, QWORD PTR [rdi+752]
	adc r11, QWORD PTR [rdi+760]
	adc r12, QWORD PTR [rdi+768]
	adc r13, QWORD PTR [rdi+776]
	adc r14, 0
	sub r8, QWORD PTR [rdi+64]
	sbb r9, QWORD PTR [rdi+72]
	sbb r10, QWORD PTR [rdi+80]
	sbb r11, QWORD PTR [rdi+88]
	sbb r12, QWORD PTR [rdi+96]
	sbb r13, QWORD PTR [rdi+104]
	sbb r14, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+736], r8
	mov QWORD PTR [rdi+744], r9
	mov QWORD PTR [rdi+752], r10
	mov QWORD PTR [rdi+760], r11
	mov QWORD PTR [rdi+768], r12
	mov QWORD PTR [rdi+776], r13
	mov r8, QWORD PTR [rdi+736]
	mov r9, QWORD PTR [rdi+744]
	mov r10, QWORD PTR [rdi+752]
	mov r11, QWORD PTR [rdi+760]
	mov r12, QWORD PTR [rdi+768]
	mov r13, QWORD PTR [rdi+776]
	mov r14d, 0
	add r8, QWORD PTR [rdi+736]
	adc r9, QWORD PTR [rdi+744]
	adc r10, QWORD PTR [rdi+752]
	adc r11, QWORD PTR [rdi+760]
	adc r12, QWORD PTR [rdi+768]
	adc r13, QWORD PTR [rdi+776]
	adc r14, 0
	sub r8, QWORD PTR [rdi+64]
	sbb r9, QWORD PTR [rdi+72]
	sbb r10, QWORD PTR [rdi+80]
	sbb r11, QWORD PTR [rdi+88]
	sbb r12, QWORD PTR [rdi+96]
	sbb r13, QWORD PTR [rdi+104]
	sbb r14, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+736], r8
	mov QWORD PTR [rdi+744], r9
	mov QWORD PTR [rdi+752], r10
	mov QWORD PTR [rdi+760], r11
	mov QWORD PTR [rdi+768], r12
	mov QWORD PTR [rdi+776], r13
	mov r8, QWORD PTR [rdi+1168]
	mov r9, QWORD PTR [rdi+1176]
	mov r10, QWORD PTR [rdi+1184]
	mov r11, QWORD PTR [rdi+1192]
	mov r12, QWORD PTR [rdi+1200]
	mov r13, QWORD PTR [rdi+1208]
	sub r8, QWORD PTR [rdi+304]
	sbb r9, QWORD PTR [rdi+312]
	sbb r10, QWORD PTR [rdi+320]
	sbb r11, QWORD PTR [rdi+328]
	sbb r12, QWORD PTR [rdi+336]
	sbb r13, QWORD PTR [rdi+344]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1264], r8
	mov QWORD PTR [rdi+1272], r9
	mov QWORD PTR [rdi+1280], r10
	mov QWORD PTR [rdi+1288], r11
	mov QWORD PTR [rdi+1296], r12
	mov QWORD PTR [rdi+1304], r13
	mov r8, QWORD PTR [rdi+1264]
	mov r9, QWORD PTR [rdi+1272]
	mov r10, QWORD PTR [rdi+1280]
	mov r11, QWORD PTR [rdi+1288]
	mov r12, QWORD PTR [rdi+1296]
	mov r13, QWORD PTR [rdi+1304]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1264]
	adc r9, QWORD PTR [rdi+1272]
	adc r10, QWORD PTR [rdi+1280]
	adc r11, QWORD PTR [rdi+1288]
	adc r12, QWORD PTR [rdi+1296]
	adc r13, QWORD PTR [rdi+1304]
	adc r14, 0
	sub r8, QWORD PTR [rdi+64]
	sbb r9, QWORD PTR [rdi+72]
	sbb r10, QWORD PTR [rdi+80]
	sbb r11, QWORD PTR [rdi+88]
	sbb r12, QWORD PTR [rdi+96]
	sbb r13, QWORD PTR [rdi+104]
	sbb r14, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1312], r8
	mov QWORD PTR [rdi+1320], r9
	mov QWORD PTR [rdi+1328], r10
	mov QWORD PTR [rdi+1336], r11
	mov QWORD PTR [rdi+1344], r12
	mov QWORD PTR [rdi+1352], r13
	mov r8, QWORD PTR [rdi+1312]
	mov r9, QWORD PTR [rdi+1320]
	mov r10, QWORD PTR [rdi+1328]
	mov r11, QWORD PTR [rdi+1336]
	mov r12, QWORD PTR [rdi+1344]
	mov r13, QWORD PTR [rdi+1352]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1264]
	adc r9, QWORD PTR [rdi+1272]
	adc r10, QWORD PTR [rdi+1280]
	adc r11, QWORD PTR [rdi+1288]
	adc r12, QWORD PTR [rdi+1296]
	adc r13, QWORD PTR [rdi+1304]
	adc r14, 0
	sub r8, QWORD PTR [rdi+64]
	sbb r9, QWORD PTR [rdi+72]
	sbb r10, QWORD PTR [rdi+80]
	sbb r11, QWORD PTR [rdi+88]
	sbb r12, QWORD PTR [rdi+96]
	sbb r13, QWORD PTR [rdi+104]
	sbb r14, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1264], r8
	mov QWORD PTR [rdi+1272], r9
	mov QWORD PTR [rdi+1280], r10
	mov QWORD PTR [rdi+1288], r11
	mov QWORD PTR [rdi+1296], r12
	mov QWORD PTR [rdi+1304], r13
	mov rcx, QWORD PTR [rdi+1264]
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov r13, rbp
	mov QWORD PTR [rdi+4056], r8
	mov QWORD PTR [rdi+4064], r9
	mov rcx, QWORD PTR [rdi+1272]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov r14, rbp
	mov rcx, QWORD PTR [rdi+1280]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov r15, rbp
	mov rcx, QWORD PTR [rdi+1288]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov r8, rbp
	mov rcx, QWORD PTR [rdi+1296]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov r9, rbp
	mov rax, QWORD PTR [rdi+4056]
	add rax, rax
	mov QWORD PTR [rdi+4056], rax
	mov rax, QWORD PTR [rdi+4064]
	adc rax, rax
	mov QWORD PTR [rdi+4064], rax
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	adc r8, r8
	adc r9, r9
	mov ecx, 0
	adc rcx, rcx
	mov rax, QWORD PTR [rdi+1264]
	mul rax
	mov QWORD PTR [rdi+4048], rax
	add rdx, QWORD PTR [rdi+4056]
	mov QWORD PTR [rdi+4056], rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1272]
	mul rax
	add rax, rbp
	adc rdx, 0
	add rax, QWORD PTR [rdi+4064]
	mov QWORD PTR [rdi+4064], rax
	adc r10, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1280]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc r12, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1288]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc r14, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1296]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc r8, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1304]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rcx, rdx
	mov ebp, 0
	adc rbp, 0
	mov QWORD PTR [rdi+1024], r13
	mov QWORD PTR [rdi+1032], r14
	mov QWORD PTR [rdi+1040], r15
	mov QWORD PTR [rdi+1048], r8
	mov QWORD PTR [rdi+1056], r9
	mov QWORD PTR [rdi+1064], rcx
	mov r13, QWORD PTR [rdi+4048]
	mov r14, QWORD PTR [rdi+4056]
	mov r15, QWORD PTR [rdi+4064]
	mov rcx, r13
	shl rcx, 32
	add rcx, r13
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r13d, 0
	adc r13, 0
	sub r14, rbp
	sbb r15, rdx
	sbb r10, r13
	sbb r11, 0
	sbb r12, 0
	mov r13, rcx
	sbb r13, 0
	mov rcx, r14
	shl rcx, 32
	add rcx, r14
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r14d, 0
	adc r14, 0
	sub r15, rbp
	sbb r10, rdx
	sbb r11, r14
	sbb r12, 0
	sbb r13, 0
	mov r14, rcx
	sbb r14, 0
	mov rcx, r15
	shl rcx, 32
	add rcx, r15
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r15d, 0
	adc r15, 0
	sub r10, rbp
	sbb r11, rdx
	sbb r12, r15
	sbb r13, 0
	sbb r14, 0
	mov r15, rcx
	sbb r15, 0
	mov rcx, r10
	shl rcx, 32
	add rcx, r10
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r10d, 0
	adc r10, 0
	sub r11, rbp
	sbb r12, rdx
	sbb r13, r10
	sbb r14, 0
	sbb r15, 0
	mov r10, rcx
	sbb r10, 0
	mov rcx, r11
	shl rcx, 32
	add rcx, r11
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r11d, 0
	adc r11, 0
	sub r12, rbp
	sbb r13, rdx
	sbb r14, r11
	sbb r15, 0
	sbb r10, 0
	mov r11, rcx
	sbb r11, 0
	mov rcx, r12
	shl rcx, 32
	add rcx, r12
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r12d, 0
	adc r12, 0
	sub r13, rbp
	sbb r14, rdx
	sbb r15, r12
	sbb r10, 0
	sbb r11, 0
	mov r12, rcx
	sbb r12, 0
	mov r8d, 0
	add r13, QWORD PTR [rdi+1024]
	adc r14, QWORD PTR [rdi+1032]
	adc r15, QWORD PTR [rdi+1040]
	adc r10, QWORD PTR [rdi+1048]
	adc r11, QWORD PTR [rdi+1056]
	adc r12, QWORD PTR [rdi+1064]
	adc r8, 0
	sub r13, QWORD PTR [rdi+64]
	sbb r14, QWORD PTR [rdi+72]
	sbb r15, QWORD PTR [rdi+80]
	sbb r10, QWORD PTR [rdi+88]
	sbb r11, QWORD PTR [rdi+96]
	sbb r12, QWORD PTR [rdi+104]
	sbb r8, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r13, rcx
	adc r14, rdx
	adc r15, rbp
	adc r10, rax
	adc r11, rax
	adc r12, rax
	mov QWORD PTR [rdi+1024], r13
	mov QWORD PTR [rdi+1032], r14
	mov QWORD PTR [rdi+1040], r15
	mov QWORD PTR [rdi+1048], r10
	mov QWORD PTR [rdi+1056], r11
	mov QWORD PTR [rdi+1064], r12
	mov r8, QWORD PTR [rdi+1024]
	mov r9, QWORD PTR [rdi+1032]
	mov r10, QWORD PTR [rdi+1040]
	mov r11, QWORD PTR [rdi+1048]
	mov r12, QWORD PTR [rdi+1056]
	mov r13, QWORD PTR [rdi+1064]
	sub r8, QWORD PTR [rdi+736]
	sbb r9, QWORD PTR [rdi+744]
	sbb r10, QWORD PTR [rdi+752]
	sbb r11, QWORD PTR [rdi+760]
	sbb r12, QWORD PTR [rdi+768]
	sbb r13, QWORD PTR [rdi+776]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1024], r8
	mov QWORD PTR [rdi+1032], r9
	mov QWORD PTR [rdi+1040], r10
	mov QWORD PTR [rdi+1048], r11
	mov QWORD PTR [rdi+1056], r12
	mov QWORD PTR [rdi+1064], r13
	mov r8, QWORD PTR [rdi+1024]
	mov r9, QWORD PTR [rdi+1032]
	mov r10, QWORD PTR [rdi+1040]
	mov r11, QWORD PTR [rdi+1048]
	mov r12, QWORD PTR [rdi+1056]
	mov r13, QWORD PTR [rdi+1064]
	sub r8, QWORD PTR [rdi+736]
	sbb r9, QWORD PTR [rdi+744]
	sbb r10, QWORD PTR [rdi+752]
	sbb r11, QWORD PTR [rdi+760]
	sbb r12, QWORD PTR [rdi+768]
	sbb r13, QWORD PTR [rdi+776]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1024], r8
	mov QWORD PTR [rdi+1032], r9
	mov QWORD PTR [rdi+1040], r10
	mov QWORD PTR [rdi+1048], r11
	mov QWORD PTR [rdi+1056], r12
	mov QWORD PTR [rdi+1064], r13
	mov r8, QWORD PTR [rdi+736]
	mov r9, QWORD PTR [rdi+744]
	mov r10, QWORD PTR [rdi+752]
	mov r11, QWORD PTR [rdi+760]
	mov r12, QWORD PTR [rdi+768]
	mov r13, QWORD PTR [rdi+776]
	sub r8, QWORD PTR [rdi+1024]
	sbb r9, QWORD PTR [rdi+1032]
	sbb r10, QWORD PTR [rdi+1040]
	sbb r11, QWORD PTR [rdi+1048]
	sbb r12, QWORD PTR [rdi+1056]
	sbb r13, QWORD PTR [rdi+1064]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1312], r8
	mov QWORD PTR [rdi+1320], r9
	mov QWORD PTR [rdi+1328], r10
	mov QWORD PTR [rdi+1336], r11
	mov QWORD PTR [rdi+1344], r12
	mov QWORD PTR [rdi+1352], r13
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1264]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1312]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1320]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1328]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1336]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1344]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1352]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, r8
	shl rcx, 32
	add rcx, r8
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r8d, 0
	adc r8, 0
	sub r9, rbp
	sbb r10, rdx
	sbb r11, r8
	sbb r12, 0
	sbb r13, 0
	sbb rcx, 0
	add r14, rcx
	adc r15, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+1272]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1312]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1320]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1328]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1336]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1344]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1352]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, r9
	shl rcx, 32
	add rcx, r9
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r9d, 0
	adc r9, 0
	sub r10, rbp
	sbb r11, rdx
	sbb r12, r9
	sbb r13, 0
	sbb r14, 0
	sbb rcx, 0
	add r15, rcx
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1280]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1312]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1320]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1328]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1336]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1344]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1352]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, r10
	shl rcx, 32
	add rcx, r10
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r10d, 0
	adc r10, 0
	sub r11, rbp
	sbb r12, rdx
	sbb r13, r10
	sbb r14, 0
	sbb r15, 0
	sbb rcx, 0
	add r8, rcx
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1288]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1312]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1320]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1328]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1336]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1344]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1352]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, r11
	shl rcx, 32
	add rcx, r11
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r11d, 0
	adc r11, 0
	sub r12, rbp
	sbb r13, rdx
	sbb r14, r11
	sbb r15, 0
	sbb r8, 0
	sbb rcx, 0
	add r9, rcx
	adc r10, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1296]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1312]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1320]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1328]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1336]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1344]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1352]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, r12
	shl rcx, 32
	add rcx, r12
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r12d, 0
	adc r12, 0
	sub r13, rbp
	sbb r14, rdx
	sbb r15, r12
	sbb r8, 0
	sbb r9, 0
	sbb rcx, 0
	add r10, rcx
	adc r11, 0
	mov r12d, 0
	mov rcx, QWORD PTR [rdi+1304]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1312]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1320]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1328]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1336]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1344]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1352]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rcx, r13
	shl rcx, 32
	add rcx, r13
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r13d, 0
	adc r13, 0
	sub r14, rbp
	sbb r15, rdx
	sbb r8, r13
	sbb r9, 0
	sbb r10, 0
	sbb rcx, 0
	add r11, rcx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+1072], r14
	mov QWORD PTR [rdi+1080], r15
	mov QWORD PTR [rdi+1088], r8
	mov QWORD PTR [rdi+1096], r9
	mov QWORD PTR [rdi+1104], r10
	mov QWORD PTR [rdi+1112], r11
	mov r8, QWORD PTR [rdi+784]
	mov r9, QWORD PTR [rdi+792]
	mov r10, QWORD PTR [rdi+800]
	mov r11, QWORD PTR [rdi+808]
	mov r12, QWORD PTR [rdi+816]
	mov r13, QWORD PTR [rdi+824]
	mov r14d, 0
	add r8, QWORD PTR [rdi+784]
	adc r9, QWORD PTR [rdi+792]
	adc r10, QWORD PTR [rdi+800]
	adc r11, QWORD PTR [rdi+808]
	adc r12, QWORD PTR [rdi+816]
	adc r13, QWORD PTR [rdi+824]
	adc r14, 0
	sub r8, QWORD PTR [rdi+64]
	sbb r9, QWORD PTR [rdi+72]
	sbb r10, QWORD PTR [rdi+80]
	sbb r11, QWORD PTR [rdi+88]
	sbb r12, QWORD PTR [rdi+96]
	sbb r13, QWORD PTR [rdi+104]
	sbb r14, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+784], r8
	mov QWORD PTR [rdi+792], r9
	mov QWORD PTR [rdi+800], r10
	mov QWORD PTR [rdi+808], r11
	mov QWORD PTR [rdi+816], r12
	mov QWORD PTR [rdi+824], r13
	mov r8, QWORD PTR [rdi+784]
	mov r9, QWORD PTR [rdi+792]
	mov r10, QWORD PTR [rdi+800]
	mov r11, QWORD PTR [rdi+808]
	mov r12, QWORD PTR [rdi+816]
	mov r13, QWORD PTR [rdi+824]
	mov r14d, 0
	add r8, QWORD PTR [rdi+784]
	adc r9, QWORD PTR [rdi+792]
	adc r10, QWORD PTR [rdi+800]
	adc r11, QWORD PTR [rdi+808]
	adc r12, QWORD PTR [rdi+816]
	adc r13, QWORD PTR [rdi+824]
	adc r14, 0
	sub r8, QWORD PTR [rdi+64]
	sbb r9, QWORD PTR [rdi+72]
	sbb r10, QWORD PTR [rdi+80]
	sbb r11, QWORD PTR [rdi+88]
	sbb r12, QWORD PTR [rdi+96]
	sbb r13, QWORD PTR [rdi+104]
	sbb r14, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+784], r8
	mov QWORD PTR [rdi+792], r9
	mov QWORD PTR [rdi+800], r10
	mov QWORD PTR [rdi+808], r11
	mov QWORD PTR [rdi+816], r12
	mov QWORD PTR [rdi+824], r13
	mov r8, QWORD PTR [rdi+784]
	mov r9, QWORD PTR [rdi+792]
	mov r10, QWORD PTR [rdi+800]
	mov r11, QWORD PTR [rdi+808]
	mov r12, QWORD PTR [rdi+816]
	mov r13, QWORD PTR [rdi+824]
	mov r14d, 0
	add r8, QWORD PTR [rdi+784]
	adc r9, QWORD PTR [rdi+792]
	adc r10, QWORD PTR [rdi+800]
	adc r11, QWORD PTR [rdi+808]
	adc r12, QWORD PTR [rdi+816]
	adc r13, QWORD PTR [rdi+824]
	adc r14, 0
	sub r8, QWORD PTR [rdi+64]
	sbb r9, QWORD PTR [rdi+72]
	sbb r10, QWORD PTR [rdi+80]
	sbb r11, QWORD PTR [rdi+88]
	sbb r12, QWORD PTR [rdi+96]
	sbb r13, QWORD PTR [rdi+104]
	sbb r14, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+784], r8
	mov QWORD PTR [rdi+792], r9
	mov QWORD PTR [rdi+800], r10
	mov QWORD PTR [rdi+808], r11
	mov QWORD PTR [rdi+816], r12
	mov QWORD PTR [rdi+824], r13
	mov r8, QWORD PTR [rdi+1072]
	mov r9, QWORD PTR [rdi+1080]
	mov r10, QWORD PTR [rdi+1088]
	mov r11, QWORD PTR [rdi+1096]
	mov r12, QWORD PTR [rdi+1104]
	mov r13, QWORD PTR [rdi+1112]
	sub r8, QWORD PTR [rdi+784]
	sbb r9, QWORD PTR [rdi+792]
	sbb r10, QWORD PTR [rdi+800]
	sbb r11, QWORD PTR [rdi+808]
	sbb r12, QWORD PTR [rdi+816]
	sbb r13, QWORD PTR [rdi+824]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1072], r8
	mov QWORD PTR [rdi+1080], r9
	mov QWORD PTR [rdi+1088], r10
	mov QWORD PTR [rdi+1096], r11
	mov QWORD PTR [rdi+1104], r12
	mov QWORD PTR [rdi+1112], r13
	mov r8, QWORD PTR [rdi+2128]
	mov r9, QWORD PTR [rdi+2136]
	mov r10, QWORD PTR [rdi+2144]
	mov r11, QWORD PTR [rdi+2152]
	mov r12, QWORD PTR [rdi+2160]
	mov r13, QWORD PTR [rdi+2168]
	mov r14d, 0
	add r8, QWORD PTR [rdi+2128]
	adc r9, QWORD PTR [rdi+2136]
	adc r10, QWORD PTR [rdi+2144]
	adc r11, QWORD PTR [rdi+2152]
	adc r12, QWORD PTR [rdi+2160]
	adc r13, QWORD PTR [rdi+2168]
	adc r14, 0
	sub r8, QWORD PTR [rdi+64]
	sbb r9, QWORD PTR [rdi+72]
	sbb r10, QWORD PTR [rdi+80]
	sbb r11, QWORD PTR [rdi+88]
	sbb r12, QWORD PTR [rdi+96]
	sbb r13, QWORD PTR [rdi+104]
	sbb r14, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+832], r8
	mov QWORD PTR [rdi+840], r9
	mov QWORD PTR [rdi+848], r10
	mov QWORD PTR [rdi+856], r11
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
213:
	mov r8, QWORD PTR [rdi+1024]
	mov r9, QWORD PTR [rdi+1032]
	mov r10, QWORD PTR [rdi+1040]
	mov r11, QWORD PTR [rdi+1048]
	mov r12, QWORD PTR [rdi+1056]
	mov r13, QWORD PTR [rdi+1064]
	sub r8, QWORD PTR [rdi+736]
	sbb r9, QWORD PTR [rdi+744]
	sbb r10, QWORD PTR [rdi+752]
	sbb r11, QWORD PTR [rdi+760]
	sbb r12, QWORD PTR [rdi+768]
	sbb r13, QWORD PTR [rdi+776]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1168], r8
	mov QWORD PTR [rdi+1176], r9
	mov QWORD PTR [rdi+1184], r10
	mov QWORD PTR [rdi+1192], r11
	mov QWORD PTR [rdi+1200], r12
	mov QWORD PTR [rdi+1208], r13
	mov rcx, QWORD PTR [rdi+1168]
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov r13, rbp
	mov QWORD PTR [rdi+4056], r8
	mov QWORD PTR [rdi+4064], r9
	mov rcx, QWORD PTR [rdi+1176]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov r14, rbp
	mov rcx, QWORD PTR [rdi+1184]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov r15, rbp
	mov rcx, QWORD PTR [rdi+1192]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov r8, rbp
	mov rcx, QWORD PTR [rdi+1200]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov r9, rbp
	mov rax, QWORD PTR [rdi+4056]
	add rax, rax
	mov QWORD PTR [rdi+4056], rax
	mov rax, QWORD PTR [rdi+4064]
	adc rax, rax
	mov QWORD PTR [rdi+4064], rax
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	adc r8, r8
	adc r9, r9
	mov ecx, 0
	adc rcx, rcx
	mov rax, QWORD PTR [rdi+1168]
	mul rax
	mov QWORD PTR [rdi+4048], rax
	add rdx, QWORD PTR [rdi+4056]
	mov QWORD PTR [rdi+4056], rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1176]
	mul rax
	add rax, rbp
	adc rdx, 0
	add rax, QWORD PTR [rdi+4064]
	mov QWORD PTR [rdi+4064], rax
	adc r10, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1184]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc r12, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1192]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc r14, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1200]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc r8, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1208]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rcx, rdx
	mov ebp, 0
	adc rbp, 0
	mov QWORD PTR [rdi+1216], r13
	mov QWORD PTR [rdi+1224], r14
	mov QWORD PTR [rdi+1232], r15
	mov QWORD PTR [rdi+1240], r8
	mov QWORD PTR [rdi+1248], r9
	mov QWORD PTR [rdi+1256], rcx
	mov r13, QWORD PTR [rdi+4048]
	mov r14, QWORD PTR [rdi+4056]
	mov r15, QWORD PTR [rdi+4064]
	mov rcx, r13
	shl rcx, 32
	add rcx, r13
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r13d, 0
	adc r13, 0
	sub r14, rbp
	sbb r15, rdx
	sbb r10, r13
	sbb r11, 0
	sbb r12, 0
	mov r13, rcx
	sbb r13, 0
	mov rcx, r14
	shl rcx, 32
	add rcx, r14
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r14d, 0
	adc r14, 0
	sub r15, rbp
	sbb r10, rdx
	sbb r11, r14
	sbb r12, 0
	sbb r13, 0
	mov r14, rcx
	sbb r14, 0
	mov rcx, r15
	shl rcx, 32
	add rcx, r15
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r15d, 0
	adc r15, 0
	sub r10, rbp
	sbb r11, rdx
	sbb r12, r15
	sbb r13, 0
	sbb r14, 0
	mov r15, rcx
	sbb r15, 0
	mov rcx, r10
	shl rcx, 32
	add rcx, r10
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r10d, 0
	adc r10, 0
	sub r11, rbp
	sbb r12, rdx
	sbb r13, r10
	sbb r14, 0
	sbb r15, 0
	mov r10, rcx
	sbb r10, 0
	mov rcx, r11
	shl rcx, 32
	add rcx, r11
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r11d, 0
	adc r11, 0
	sub r12, rbp
	sbb r13, rdx
	sbb r14, r11
	sbb r15, 0
	sbb r10, 0
	mov r11, rcx
	sbb r11, 0
	mov rcx, r12
	shl rcx, 32
	add rcx, r12
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r12d, 0
	adc r12, 0
	sub r13, rbp
	sbb r14, rdx
	sbb r15, r12
	sbb r10, 0
	sbb r11, 0
	mov r12, rcx
	sbb r12, 0
	mov r8d, 0
	add r13, QWORD PTR [rdi+1216]
	adc r14, QWORD PTR [rdi+1224]
	adc r15, QWORD PTR [rdi+1232]
	adc r10, QWORD PTR [rdi+1240]
	adc r11, QWORD PTR [rdi+1248]
	adc r12, QWORD PTR [rdi+1256]
	adc r8, 0
	sub r13, QWORD PTR [rdi+64]
	sbb r14, QWORD PTR [rdi+72]
	sbb r15, QWORD PTR [rdi+80]
	sbb r10, QWORD PTR [rdi+88]
	sbb r11, QWORD PTR [rdi+96]
	sbb r12, QWORD PTR [rdi+104]
	sbb r8, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r13, rcx
	adc r14, rdx
	adc r15, rbp
	adc r10, rax
	adc r11, rax
	adc r12, rax
	mov QWORD PTR [rdi+1216], r13
	mov QWORD PTR [rdi+1224], r14
	mov QWORD PTR [rdi+1232], r15
	mov QWORD PTR [rdi+1240], r10
	mov QWORD PTR [rdi+1248], r11
	mov QWORD PTR [rdi+1256], r12
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+832]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, r8
	shl rcx, 32
	add rcx, r8
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r8d, 0
	adc r8, 0
	sub r9, rbp
	sbb r10, rdx
	sbb r11, r8
	sbb r12, 0
	sbb r13, 0
	sbb rcx, 0
	add r14, rcx
	adc r15, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+840]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, r9
	shl rcx, 32
	add rcx, r9
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r9d, 0
	adc r9, 0
	sub r10, rbp
	sbb r11, rdx
	sbb r12, r9
	sbb r13, 0
	sbb r14, 0
	sbb rcx, 0
	add r15, rcx
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+848]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, r10
	shl rcx, 32
	add rcx, r10
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r10d, 0
	adc r10, 0
	sub r11, rbp
	sbb r12, rdx
	sbb r13, r10
	sbb r14, 0
	sbb r15, 0
	sbb rcx, 0
	add r8, rcx
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+856]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, r11
	shl rcx, 32
	add rcx, r11
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r11d, 0
	adc r11, 0
	sub r12, rbp
	sbb r13, rdx
	sbb r14, r11
	sbb r15, 0
	sbb r8, 0
	sbb rcx, 0
	add r9, rcx
	adc r10, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+864]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, r12
	shl rcx, 32
	add rcx, r12
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r12d, 0
	adc r12, 0
	sub r13, rbp
	sbb r14, rdx
	sbb r15, r12
	sbb r8, 0
	sbb r9, 0
	sbb rcx, 0
	add r10, rcx
	adc r11, 0
	mov r12d, 0
	mov rcx, QWORD PTR [rdi+872]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rcx, r13
	shl rcx, 32
	add rcx, r13
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r13d, 0
	adc r13, 0
	sub r14, rbp
	sbb r15, rdx
	sbb r8, r13
	sbb r9, 0
	sbb r10, 0
	sbb rcx, 0
	add r11, rcx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+832], r14
	mov QWORD PTR [rdi+840], r15
	mov QWORD PTR [rdi+848], r8
	mov QWORD PTR [rdi+856], r9
	mov QWORD PTR [rdi+864], r10
	mov QWORD PTR [rdi+872], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1024]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, r8
	shl rcx, 32
	add rcx, r8
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r8d, 0
	adc r8, 0
	sub r9, rbp
	sbb r10, rdx
	sbb r11, r8
	sbb r12, 0
	sbb r13, 0
	sbb rcx, 0
	add r14, rcx
	adc r15, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+1032]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, r9
	shl rcx, 32
	add rcx, r9
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r9d, 0
	adc r9, 0
	sub r10, rbp
	sbb r11, rdx
	sbb r12, r9
	sbb r13, 0
	sbb r14, 0
	sbb rcx, 0
	add r15, rcx
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1040]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, r10
	shl rcx, 32
	add rcx, r10
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r10d, 0
	adc r10, 0
	sub r11, rbp
	sbb r12, rdx
	sbb r13, r10
	sbb r14, 0
	sbb r15, 0
	sbb rcx, 0
	add r8, rcx
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1048]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, r11
	shl rcx, 32
	add rcx, r11
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r11d, 0
	adc r11, 0
	sub r12, rbp
	sbb r13, rdx
	sbb r14, r11
	sbb r15, 0
	sbb r8, 0
	sbb rcx, 0
	add r9, rcx
	adc r10, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1056]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, r12
	shl rcx, 32
	add rcx, r12
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r12d, 0
	adc r12, 0
	sub r13, rbp
	sbb r14, rdx
	sbb r15, r12
	sbb r8, 0
	sbb r9, 0
	sbb rcx, 0
	add r10, rcx
	adc r11, 0
	mov r12d, 0
	mov rcx, QWORD PTR [rdi+1064]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rcx, r13
	shl rcx, 32
	add rcx, r13
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r13d, 0
	adc r13, 0
	sub r14, rbp
	sbb r15, rdx
	sbb r8, r13
	sbb r9, 0
	sbb r10, 0
	sbb rcx, 0
	add r11, rcx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+1024], r14
	mov QWORD PTR [rdi+1032], r15
	mov QWORD PTR [rdi+1040], r8
	mov QWORD PTR [rdi+1048], r9
	mov QWORD PTR [rdi+1056], r10
	mov QWORD PTR [rdi+1064], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+736]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, r8
	shl rcx, 32
	add rcx, r8
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r8d, 0
	adc r8, 0
	sub r9, rbp
	sbb r10, rdx
	sbb r11, r8
	sbb r12, 0
	sbb r13, 0
	sbb rcx, 0
	add r14, rcx
	adc r15, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+744]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, r9
	shl rcx, 32
	add rcx, r9
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r9d, 0
	adc r9, 0
	sub r10, rbp
	sbb r11, rdx
	sbb r12, r9
	sbb r13, 0
	sbb r14, 0
	sbb rcx, 0
	add r15, rcx
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+752]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, r10
	shl rcx, 32
	add rcx, r10
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r10d, 0
	adc r10, 0
	sub r11, rbp
	sbb r12, rdx
	sbb r13, r10
	sbb r14, 0
	sbb r15, 0
	sbb rcx, 0
	add r8, rcx
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+760]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, r11
	shl rcx, 32
	add rcx, r11
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r11d, 0
	adc r11, 0
	sub r12, rbp
	sbb r13, rdx
	sbb r14, r11
	sbb r15, 0
	sbb r8, 0
	sbb rcx, 0
	add r9, rcx
	adc r10, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+768]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, r12
	shl rcx, 32
	add rcx, r12
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r12d, 0
	adc r12, 0
	sub r13, rbp
	sbb r14, rdx
	sbb r15, r12
	sbb r8, 0
	sbb r9, 0
	sbb rcx, 0
	add r10, rcx
	adc r11, 0
	mov r12d, 0
	mov rcx, QWORD PTR [rdi+776]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rcx, r13
	shl rcx, 32
	add rcx, r13
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r13d, 0
	adc r13, 0
	sub r14, rbp
	sbb r15, rdx
	sbb r8, r13
	sbb r9, 0
	sbb r10, 0
	sbb rcx, 0
	add r11, rcx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+1312], r14
	mov QWORD PTR [rdi+1320], r15
	mov QWORD PTR [rdi+1328], r8
	mov QWORD PTR [rdi+1336], r9
	mov QWORD PTR [rdi+1344], r10
	mov QWORD PTR [rdi+1352], r11
	mov r8, QWORD PTR [rdi+1072]
	mov r9, QWORD PTR [rdi+1080]
	mov r10, QWORD PTR [rdi+1088]
	mov r11, QWORD PTR [rdi+1096]
	mov r12, QWORD PTR [rdi+1104]
	mov r13, QWORD PTR [rdi+1112]
	sub r8, QWORD PTR [rdi+784]
	sbb r9, QWORD PTR [rdi+792]
	sbb r10, QWORD PTR [rdi+800]
	sbb r11, QWORD PTR [rdi+808]
	sbb r12, QWORD PTR [rdi+816]
	sbb r13, QWORD PTR [rdi+824]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1360], r8
	mov QWORD PTR [rdi+1368], r9
	mov QWORD PTR [rdi+1376], r10
	mov QWORD PTR [rdi+1384], r11
	mov QWORD PTR [rdi+1392], r12
	mov QWORD PTR [rdi+1400], r13
	mov rcx, QWORD PTR [rdi+1360]
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1368]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov r13, rbp
	mov QWORD PTR [rdi+4056], r8
	mov QWORD PTR [rdi+4064], r9
	mov rcx, QWORD PTR [rdi+1368]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1376]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov r14, rbp
	mov rcx, QWORD PTR [rdi+1376]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1384]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov r15, rbp
	mov rcx, QWORD PTR [rdi+1384]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1392]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov r8, rbp
	mov rcx, QWORD PTR [rdi+1392]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1400]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov r9, rbp
	mov rax, QWORD PTR [rdi+4056]
	add rax, rax
	mov QWORD PTR [rdi+4056], rax
	mov rax, QWORD PTR [rdi+4064]
	adc rax, rax
	mov QWORD PTR [rdi+4064], rax
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	adc r8, r8
	adc r9, r9
	mov ecx, 0
	adc rcx, rcx
	mov rax, QWORD PTR [rdi+1360]
	mul rax
	mov QWORD PTR [rdi+4048], rax
	add rdx, QWORD PTR [rdi+4056]
	mov QWORD PTR [rdi+4056], rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1368]
	mul rax
	add rax, rbp
	adc rdx, 0
	add rax, QWORD PTR [rdi+4064]
	mov QWORD PTR [rdi+4064], rax
	adc r10, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1376]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc r12, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1384]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc r14, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1392]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc r8, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1400]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rcx, rdx
	mov ebp, 0
	adc rbp, 0
	mov QWORD PTR [rdi+1408], r13
	mov QWORD PTR [rdi+1416], r14
	mov QWORD PTR [rdi+1424], r15
	mov QWORD PTR [rdi+1432], r8
	mov QWORD PTR [rdi+1440], r9
	mov QWORD PTR [rdi+1448], rcx
	mov r13, QWORD PTR [rdi+4048]
	mov r14, QWORD PTR [rdi+4056]
	mov r15, QWORD PTR [rdi+4064]
	mov rcx, r13
	shl rcx, 32
	add rcx, r13
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r13d, 0
	adc r13, 0
	sub r14, rbp
	sbb r15, rdx
	sbb r10, r13
	sbb r11, 0
	sbb r12, 0
	mov r13, rcx
	sbb r13, 0
	mov rcx, r14
	shl rcx, 32
	add rcx, r14
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r14d, 0
	adc r14, 0
	sub r15, rbp
	sbb r10, rdx
	sbb r11, r14
	sbb r12, 0
	sbb r13, 0
	mov r14, rcx
	sbb r14, 0
	mov rcx, r15
	shl rcx, 32
	add rcx, r15
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r15d, 0
	adc r15, 0
	sub r10, rbp
	sbb r11, rdx
	sbb r12, r15
	sbb r13, 0
	sbb r14, 0
	mov r15, rcx
	sbb r15, 0
	mov rcx, r10
	shl rcx, 32
	add rcx, r10
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r10d, 0
	adc r10, 0
	sub r11, rbp
	sbb r12, rdx
	sbb r13, r10
	sbb r14, 0
	sbb r15, 0
	mov r10, rcx
	sbb r10, 0
	mov rcx, r11
	shl rcx, 32
	add rcx, r11
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r11d, 0
	adc r11, 0
	sub r12, rbp
	sbb r13, rdx
	sbb r14, r11
	sbb r15, 0
	sbb r10, 0
	mov r11, rcx
	sbb r11, 0
	mov rcx, r12
	shl rcx, 32
	add rcx, r12
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r12d, 0
	adc r12, 0
	sub r13, rbp
	sbb r14, rdx
	sbb r15, r12
	sbb r10, 0
	sbb r11, 0
	mov r12, rcx
	sbb r12, 0
	mov r8d, 0
	add r13, QWORD PTR [rdi+1408]
	adc r14, QWORD PTR [rdi+1416]
	adc r15, QWORD PTR [rdi+1424]
	adc r10, QWORD PTR [rdi+1432]
	adc r11, QWORD PTR [rdi+1440]
	adc r12, QWORD PTR [rdi+1448]
	adc r8, 0
	sub r13, QWORD PTR [rdi+64]
	sbb r14, QWORD PTR [rdi+72]
	sbb r15, QWORD PTR [rdi+80]
	sbb r10, QWORD PTR [rdi+88]
	sbb r11, QWORD PTR [rdi+96]
	sbb r12, QWORD PTR [rdi+104]
	sbb r8, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r13, rcx
	adc r14, rdx
	adc r15, rbp
	adc r10, rax
	adc r11, rax
	adc r12, rax
	mov QWORD PTR [rdi+1408], r13
	mov QWORD PTR [rdi+1416], r14
	mov QWORD PTR [rdi+1424], r15
	mov QWORD PTR [rdi+1432], r10
	mov QWORD PTR [rdi+1440], r11
	mov QWORD PTR [rdi+1448], r12
	mov r8, QWORD PTR [rdi+1024]
	mov r9, QWORD PTR [rdi+1032]
	mov r10, QWORD PTR [rdi+1040]
	mov r11, QWORD PTR [rdi+1048]
	mov r12, QWORD PTR [rdi+1056]
	mov r13, QWORD PTR [rdi+1064]
	sub r8, QWORD PTR [rdi+1312]
	sbb r9, QWORD PTR [rdi+1320]
	sbb r10, QWORD PTR [rdi+1328]
	sbb r11, QWORD PTR [rdi+1336]
	sbb r12, QWORD PTR [rdi+1344]
	sbb r13, QWORD PTR [rdi+1352]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1264], r8
	mov QWORD PTR [rdi+1272], r9
	mov QWORD PTR [rdi+1280], r10
	mov QWORD PTR [rdi+1288], r11
	mov QWORD PTR [rdi+1296], r12
	mov QWORD PTR [rdi+1304], r13
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1072]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, r8
	shl rcx, 32
	add rcx, r8
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r8d, 0
	adc r8, 0
	sub r9, rbp
	sbb r10, rdx
	sbb r11, r8
	sbb r12, 0
	sbb r13, 0
	sbb rcx, 0
	add r14, rcx
	adc r15, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+1080]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, r9
	shl rcx, 32
	add rcx, r9
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r9d, 0
	adc r9, 0
	sub r10, rbp
	sbb r11, rdx
	sbb r12, r9
	sbb r13, 0
	sbb r14, 0
	sbb rcx, 0
	add r15, rcx
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1088]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, r10
	shl rcx, 32
	add rcx, r10
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r10d, 0
	adc r10, 0
	sub r11, rbp
	sbb r12, rdx
	sbb r13, r10
	sbb r14, 0
	sbb r15, 0
	sbb rcx, 0
	add r8, rcx
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1096]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, r11
	shl rcx, 32
	add rcx, r11
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r11d, 0
	adc r11, 0
	sub r12, rbp
	sbb r13, rdx
	sbb r14, r11
	sbb r15, 0
	sbb r8, 0
	sbb rcx, 0
	add r9, rcx
	adc r10, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1104]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, r12
	shl rcx, 32
	add rcx, r12
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r12d, 0
	adc r12, 0
	sub r13, rbp
	sbb r14, rdx
	sbb r15, r12
	sbb r8, 0
	sbb r9, 0
	sbb rcx, 0
	add r10, rcx
	adc r11, 0
	mov r12d, 0
	mov rcx, QWORD PTR [rdi+1112]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rcx, r13
	shl rcx, 32
	add rcx, r13
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r13d, 0
	adc r13, 0
	sub r14, rbp
	sbb r15, rdx
	sbb r8, r13
	sbb r9, 0
	sbb r10, 0
	sbb rcx, 0
	add r11, rcx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+1072], r14
	mov QWORD PTR [rdi+1080], r15
	mov QWORD PTR [rdi+1088], r8
	mov QWORD PTR [rdi+1096], r9
	mov QWORD PTR [rdi+1104], r10
	mov QWORD PTR [rdi+1112], r11
	mov r8, QWORD PTR [rdi+1408]
	mov r9, QWORD PTR [rdi+1416]
	mov r10, QWORD PTR [rdi+1424]
	mov r11, QWORD PTR [rdi+1432]
	mov r12, QWORD PTR [rdi+1440]
	mov r13, QWORD PTR [rdi+1448]
	sub r8, QWORD PTR [rdi+1024]
	sbb r9, QWORD PTR [rdi+1032]
	sbb r10, QWORD PTR [rdi+1040]
	sbb r11, QWORD PTR [rdi+1048]
	sbb r12, QWORD PTR [rdi+1056]
	sbb r13, QWORD PTR [rdi+1064]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+736], r8
	mov QWORD PTR [rdi+744], r9
	mov QWORD PTR [rdi+752], r10
	mov QWORD PTR [rdi+760], r11
	mov QWORD PTR [rdi+768], r12
	mov QWORD PTR [rdi+776], r13
	mov r8, QWORD PTR [rdi+736]
	mov r9, QWORD PTR [rdi+744]
	mov r10, QWORD PTR [rdi+752]
	mov r11, QWORD PTR [rdi+760]
	mov r12, QWORD PTR [rdi+768]
	mov r13, QWORD PTR [rdi+776]
	sub r8, QWORD PTR [rdi+1312]
	sbb r9, QWORD PTR [rdi+1320]
	sbb r10, QWORD PTR [rdi+1328]
	sbb r11, QWORD PTR [rdi+1336]
	sbb r12, QWORD PTR [rdi+1344]
	sbb r13, QWORD PTR [rdi+1352]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+736], r8
	mov QWORD PTR [rdi+744], r9
	mov QWORD PTR [rdi+752], r10
	mov QWORD PTR [rdi+760], r11
	mov QWORD PTR [rdi+768], r12
	mov QWORD PTR [rdi+776], r13
	mov r8, QWORD PTR [rdi+1024]
	mov r9, QWORD PTR [rdi+1032]
	mov r10, QWORD PTR [rdi+1040]
	mov r11, QWORD PTR [rdi+1048]
	mov r12, QWORD PTR [rdi+1056]
	mov r13, QWORD PTR [rdi+1064]
	sub r8, QWORD PTR [rdi+736]
	sbb r9, QWORD PTR [rdi+744]
	sbb r10, QWORD PTR [rdi+752]
	sbb r11, QWORD PTR [rdi+760]
	sbb r12, QWORD PTR [rdi+768]
	sbb r13, QWORD PTR [rdi+776]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+784], r8
	mov QWORD PTR [rdi+792], r9
	mov QWORD PTR [rdi+800], r10
	mov QWORD PTR [rdi+808], r11
	mov QWORD PTR [rdi+816], r12
	mov QWORD PTR [rdi+824], r13
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1360]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+784]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+792]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+800]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+808]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, r8
	shl rcx, 32
	add rcx, r8
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r8d, 0
	adc r8, 0
	sub r9, rbp
	sbb r10, rdx
	sbb r11, r8
	sbb r12, 0
	sbb r13, 0
	sbb rcx, 0
	add r14, rcx
	adc r15, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+1368]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+784]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+792]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+800]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+808]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, r9
	shl rcx, 32
	add rcx, r9
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r9d, 0
	adc r9, 0
	sub r10, rbp
	sbb r11, rdx
	sbb r12, r9
	sbb r13, 0
	sbb r14, 0
	sbb rcx, 0
	add r15, rcx
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1376]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+784]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+792]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+800]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+808]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, r10
	shl rcx, 32
	add rcx, r10
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r10d, 0
	adc r10, 0
	sub r11, rbp
	sbb r12, rdx
	sbb r13, r10
	sbb r14, 0
	sbb r15, 0
	sbb rcx, 0
	add r8, rcx
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1384]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+784]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+792]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+800]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+808]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, r11
	shl rcx, 32
	add rcx, r11
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r11d, 0
	adc r11, 0
	sub r12, rbp
	sbb r13, rdx
	sbb r14, r11
	sbb r15, 0
	sbb r8, 0
	sbb rcx, 0
	add r9, rcx
	adc r10, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1392]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+784]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+792]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+800]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+808]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, r12
	shl rcx, 32
	add rcx, r12
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r12d, 0
	adc r12, 0
	sub r13, rbp
	sbb r14, rdx
	sbb r15, r12
	sbb r8, 0
	sbb r9, 0
	sbb rcx, 0
	add r10, rcx
	adc r11, 0
	mov r12d, 0
	mov rcx, QWORD PTR [rdi+1400]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+784]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+792]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+800]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+808]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rcx, r13
	shl rcx, 32
	add rcx, r13
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r13d, 0
	adc r13, 0
	sub r14, rbp
	sbb r15, rdx
	sbb r8, r13
	sbb r9, 0
	sbb r10, 0
	sbb rcx, 0
	add r11, rcx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+784], r14
	mov QWORD PTR [rdi+792], r15
	mov QWORD PTR [rdi+800], r8
	mov QWORD PTR [rdi+808], r9
	mov QWORD PTR [rdi+816], r10
	mov QWORD PTR [rdi+824], r11
	mov r8, QWORD PTR [rdi+784]
	mov r9, QWORD PTR [rdi+792]
	mov r10, QWORD PTR [rdi+800]
	mov r11, QWORD PTR [rdi+808]
	mov r12, QWORD PTR [rdi+816]
	mov r13, QWORD PTR [rdi+824]
	sub r8, QWORD PTR [rdi+1072]
	sbb r9, QWORD PTR [rdi+1080]
	sbb r10, QWORD PTR [rdi+1088]
	sbb r11, QWORD PTR [rdi+1096]
	sbb r12, QWORD PTR [rdi+1104]
	sbb r13, QWORD PTR [rdi+1112]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+784], r8
	mov QWORD PTR [rdi+792], r9
	mov QWORD PTR [rdi+800], r10
	mov QWORD PTR [rdi+808], r11
	mov QWORD PTR [rdi+816], r12
	mov QWORD PTR [rdi+824], r13
	mov rax, rbx
	mov ecx, 144
	mul rcx
	mov rdx, rdi
	add rdx, 4096
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdi+736]
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu xmm1, XMMWORD PTR [rdi+752]
	movdqu XMMWORD PTR [rdx+16], xmm1
	movdqu xmm2, XMMWORD PTR [rdi+768]
	movdqu XMMWORD PTR [rdx+32], xmm2
	movdqu xmm3, XMMWORD PTR [rdi+784]
	movdqu XMMWORD PTR [rdx+48], xmm3
	movdqu xmm4, XMMWORD PTR [rdi+800]
	movdqu XMMWORD PTR [rdx+64], xmm4
	movdqu xmm5, XMMWORD PTR [rdi+816]
	movdqu XMMWORD PTR [rdx+80], xmm5
	movdqu xmm6, XMMWORD PTR [rdi+832]
	movdqu XMMWORD PTR [rdx+96], xmm6
	movdqu xmm7, XMMWORD PTR [rdi+848]
	movdqu XMMWORD PTR [rdx+112], xmm7
	movdqu xmm8, XMMWORD PTR [rdi+864]
	movdqu XMMWORD PTR [rdx+128], xmm8
	add rbx, 1
	cmp rbx, 8
	jb 213b
	mov rax, QWORD PTR [rdi+1024]
	mov QWORD PTR [rdi+5248], rax
	mov rax, QWORD PTR [rdi+1032]
	mov QWORD PTR [rdi+5256], rax
	mov rax, QWORD PTR [rdi+1040]
	mov QWORD PTR [rdi+5264], rax
	mov rax, QWORD PTR [rdi+1048]
	mov QWORD PTR [rdi+5272], rax
	mov rax, QWORD PTR [rdi+1056]
	mov QWORD PTR [rdi+5280], rax
	mov rax, QWORD PTR [rdi+1064]
	mov QWORD PTR [rdi+5288], rax
	mov rax, QWORD PTR [rdi+1072]
	mov QWORD PTR [rdi+5296], rax
	mov rax, QWORD PTR [rdi+1080]
	mov QWORD PTR [rdi+5304], rax
	mov rax, QWORD PTR [rdi+1088]
	mov QWORD PTR [rdi+5312], rax
	mov rax, QWORD PTR [rdi+1096]
	mov QWORD PTR [rdi+5320], rax
	mov rax, QWORD PTR [rdi+1104]
	mov QWORD PTR [rdi+5328], rax
	mov rax, QWORD PTR [rdi+1112]
	mov QWORD PTR [rdi+5336], rax
	mov rax, QWORD PTR [rdi+832]
	mov QWORD PTR [rdi+5344], rax
	mov rax, QWORD PTR [rdi+840]
	mov QWORD PTR [rdi+5352], rax
	mov rax, QWORD PTR [rdi+848]
	mov QWORD PTR [rdi+5360], rax
	mov rax, QWORD PTR [rdi+856]
	mov QWORD PTR [rdi+5368], rax
	mov rax, QWORD PTR [rdi+864]
	mov QWORD PTR [rdi+5376], rax
	mov rax, QWORD PTR [rdi+872]
	mov QWORD PTR [rdi+5384], rax
	mov ebx, 0
214:
	mov rax, rbx
	mov ecx, 144
	mul rcx
	mov rdx, rdi
	add rdx, 4096
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdx+96]
	movdqu XMMWORD PTR [rdi+1120], xmm0
	movdqu xmm1, XMMWORD PTR [rdx+112]
	movdqu XMMWORD PTR [rdi+1136], xmm1
	movdqu xmm2, XMMWORD PTR [rdx+128]
	movdqu XMMWORD PTR [rdi+1152], xmm2
	mov rcx, QWORD PTR [rdi+1120]
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov r13, rbp
	mov QWORD PTR [rdi+4056], r8
	mov QWORD PTR [rdi+4064], r9
	mov rcx, QWORD PTR [rdi+1128]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov r14, rbp
	mov rcx, QWORD PTR [rdi+1136]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov r15, rbp
	mov rcx, QWORD PTR [rdi+1144]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov r8, rbp
	mov rcx, QWORD PTR [rdi+1152]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov r9, rbp
	mov rax, QWORD PTR [rdi+4056]
	add rax, rax
	mov QWORD PTR [rdi+4056], rax
	mov rax, QWORD PTR [rdi+4064]
	adc rax, rax
	mov QWORD PTR [rdi+4064], rax
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	adc r8, r8
	adc r9, r9
	mov ecx, 0
	adc rcx, rcx
	mov rax, QWORD PTR [rdi+1120]
	mul rax
	mov QWORD PTR [rdi+4048], rax
	add rdx, QWORD PTR [rdi+4056]
	mov QWORD PTR [rdi+4056], rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1128]
	mul rax
	add rax, rbp
	adc rdx, 0
	add rax, QWORD PTR [rdi+4064]
	mov QWORD PTR [rdi+4064], rax
	adc r10, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1136]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc r12, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1144]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc r14, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1152]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc r8, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1160]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rcx, rdx
	mov ebp, 0
	adc rbp, 0
	mov QWORD PTR [rdi+1024], r13
	mov QWORD PTR [rdi+1032], r14
	mov QWORD PTR [rdi+1040], r15
	mov QWORD PTR [rdi+1048], r8
	mov QWORD PTR [rdi+1056], r9
	mov QWORD PTR [rdi+1064], rcx
	mov r13, QWORD PTR [rdi+4048]
	mov r14, QWORD PTR [rdi+4056]
	mov r15, QWORD PTR [rdi+4064]
	mov rcx, r13
	shl rcx, 32
	add rcx, r13
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r13d, 0
	adc r13, 0
	sub r14, rbp
	sbb r15, rdx
	sbb r10, r13
	sbb r11, 0
	sbb r12, 0
	mov r13, rcx
	sbb r13, 0
	mov rcx, r14
	shl rcx, 32
	add rcx, r14
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r14d, 0
	adc r14, 0
	sub r15, rbp
	sbb r10, rdx
	sbb r11, r14
	sbb r12, 0
	sbb r13, 0
	mov r14, rcx
	sbb r14, 0
	mov rcx, r15
	shl rcx, 32
	add rcx, r15
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r15d, 0
	adc r15, 0
	sub r10, rbp
	sbb r11, rdx
	sbb r12, r15
	sbb r13, 0
	sbb r14, 0
	mov r15, rcx
	sbb r15, 0
	mov rcx, r10
	shl rcx, 32
	add rcx, r10
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r10d, 0
	adc r10, 0
	sub r11, rbp
	sbb r12, rdx
	sbb r13, r10
	sbb r14, 0
	sbb r15, 0
	mov r10, rcx
	sbb r10, 0
	mov rcx, r11
	shl rcx, 32
	add rcx, r11
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r11d, 0
	adc r11, 0
	sub r12, rbp
	sbb r13, rdx
	sbb r14, r11
	sbb r15, 0
	sbb r10, 0
	mov r11, rcx
	sbb r11, 0
	mov rcx, r12
	shl rcx, 32
	add rcx, r12
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r12d, 0
	adc r12, 0
	sub r13, rbp
	sbb r14, rdx
	sbb r15, r12
	sbb r10, 0
	sbb r11, 0
	mov r12, rcx
	sbb r12, 0
	mov r8d, 0
	add r13, QWORD PTR [rdi+1024]
	adc r14, QWORD PTR [rdi+1032]
	adc r15, QWORD PTR [rdi+1040]
	adc r10, QWORD PTR [rdi+1048]
	adc r11, QWORD PTR [rdi+1056]
	adc r12, QWORD PTR [rdi+1064]
	adc r8, 0
	sub r13, QWORD PTR [rdi+64]
	sbb r14, QWORD PTR [rdi+72]
	sbb r15, QWORD PTR [rdi+80]
	sbb r10, QWORD PTR [rdi+88]
	sbb r11, QWORD PTR [rdi+96]
	sbb r12, QWORD PTR [rdi+104]
	sbb r8, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r13, rcx
	adc r14, rdx
	adc r15, rbp
	adc r10, rax
	adc r11, rax
	adc r12, rax
	mov QWORD PTR [rdi+1024], r13
	mov QWORD PTR [rdi+1032], r14
	mov QWORD PTR [rdi+1040], r15
	mov QWORD PTR [rdi+1048], r10
	mov QWORD PTR [rdi+1056], r11
	mov QWORD PTR [rdi+1064], r12
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1024]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, r8
	shl rcx, 32
	add rcx, r8
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r8d, 0
	adc r8, 0
	sub r9, rbp
	sbb r10, rdx
	sbb r11, r8
	sbb r12, 0
	sbb r13, 0
	sbb rcx, 0
	add r14, rcx
	adc r15, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+1032]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, r9
	shl rcx, 32
	add rcx, r9
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r9d, 0
	adc r9, 0
	sub r10, rbp
	sbb r11, rdx
	sbb r12, r9
	sbb r13, 0
	sbb r14, 0
	sbb rcx, 0
	add r15, rcx
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1040]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, r10
	shl rcx, 32
	add rcx, r10
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r10d, 0
	adc r10, 0
	sub r11, rbp
	sbb r12, rdx
	sbb r13, r10
	sbb r14, 0
	sbb r15, 0
	sbb rcx, 0
	add r8, rcx
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1048]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, r11
	shl rcx, 32
	add rcx, r11
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r11d, 0
	adc r11, 0
	sub r12, rbp
	sbb r13, rdx
	sbb r14, r11
	sbb r15, 0
	sbb r8, 0
	sbb rcx, 0
	add r9, rcx
	adc r10, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1056]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, r12
	shl rcx, 32
	add rcx, r12
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r12d, 0
	adc r12, 0
	sub r13, rbp
	sbb r14, rdx
	sbb r15, r12
	sbb r8, 0
	sbb r9, 0
	sbb rcx, 0
	add r10, rcx
	adc r11, 0
	mov r12d, 0
	mov rcx, QWORD PTR [rdi+1064]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rcx, r13
	shl rcx, 32
	add rcx, r13
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r13d, 0
	adc r13, 0
	sub r14, rbp
	sbb r15, rdx
	sbb r8, r13
	sbb r9, 0
	sbb r10, 0
	sbb rcx, 0
	add r11, rcx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+1072], r14
	mov QWORD PTR [rdi+1080], r15
	mov QWORD PTR [rdi+1088], r8
	mov QWORD PTR [rdi+1096], r9
	mov QWORD PTR [rdi+1104], r10
	mov QWORD PTR [rdi+1112], r11
	mov rax, rbx
	mov ecx, 96
	mul rcx
	mov rdx, rdi
	add rdx, 5392
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdi+1024]
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu xmm1, XMMWORD PTR [rdi+1040]
	movdqu XMMWORD PTR [rdx+16], xmm1
	movdqu xmm2, XMMWORD PTR [rdi+1056]
	movdqu XMMWORD PTR [rdx+32], xmm2
	movdqu xmm3, XMMWORD PTR [rdi+1072]
	movdqu XMMWORD PTR [rdx+48], xmm3
	movdqu xmm4, XMMWORD PTR [rdi+1088]
	movdqu XMMWORD PTR [rdx+64], xmm4
	movdqu xmm5, XMMWORD PTR [rdi+1104]
	movdqu XMMWORD PTR [rdx+80], xmm5
	add rbx, 1
	cmp rbx, 8
	jb 214b
	movabs rax, 0
	mov QWORD PTR [rdi+736], rax
	movabs rax, 0
	mov QWORD PTR [rdi+744], rax
	movabs rax, 0
	mov QWORD PTR [rdi+752], rax
	movabs rax, 0
	mov QWORD PTR [rdi+760], rax
	movabs rax, 0
	mov QWORD PTR [rdi+768], rax
	movabs rax, 0
	mov QWORD PTR [rdi+776], rax
	movabs rax, -4294967295
	mov QWORD PTR [rdi+784], rax
	movabs rax, 4294967295
	mov QWORD PTR [rdi+792], rax
	movabs rax, 1
	mov QWORD PTR [rdi+800], rax
	movabs rax, 0
	mov QWORD PTR [rdi+808], rax
	movabs rax, 0
	mov QWORD PTR [rdi+816], rax
	movabs rax, 0
	mov QWORD PTR [rdi+824], rax
	movabs rax, 0
	mov QWORD PTR [rdi+832], rax
	movabs rax, 0
	mov QWORD PTR [rdi+840], rax
	movabs rax, 0
	mov QWORD PTR [rdi+848], rax
	movabs rax, 0
	mov QWORD PTR [rdi+856], rax
	movabs rax, 0
	mov QWORD PTR [rdi+864], rax
	movabs rax, 0
	mov QWORD PTR [rdi+872], rax
	mov ebx, 385
215:
	sub rbx, 1
	cmp rbx, 384
	je 216f
	mov rcx, QWORD PTR [rdi+832]
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov ebp, 0
	mov rax, QWORD PTR [rdi+840]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+848]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+856]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+864]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+872]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov r13, rbp
	mov QWORD PTR [rdi+4056], r8
	mov QWORD PTR [rdi+4064], r9
	mov rcx, QWORD PTR [rdi+840]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+848]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+856]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+864]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+872]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov r14, rbp
	mov rcx, QWORD PTR [rdi+848]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+856]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+864]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+872]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov r15, rbp
	mov rcx, QWORD PTR [rdi+856]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+864]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+872]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov r8, rbp
	mov rcx, QWORD PTR [rdi+864]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+872]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov r9, rbp
	mov rax, QWORD PTR [rdi+4056]
	add rax, rax
	mov QWORD PTR [rdi+4056], rax
	mov rax, QWORD PTR [rdi+4064]
	adc rax, rax
	mov QWORD PTR [rdi+4064], rax
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	adc r8, r8
	adc r9, r9
	mov ecx, 0
	adc rcx, rcx
	mov rax, QWORD PTR [rdi+832]
	mul rax
	mov QWORD PTR [rdi+4048], rax
	add rdx, QWORD PTR [rdi+4056]
	mov QWORD PTR [rdi+4056], rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+840]
	mul rax
	add rax, rbp
	adc rdx, 0
	add rax, QWORD PTR [rdi+4064]
	mov QWORD PTR [rdi+4064], rax
	adc r10, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+848]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc r12, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+856]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc r14, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+864]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc r8, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+872]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rcx, rdx
	mov ebp, 0
	adc rbp, 0
	mov QWORD PTR [rdi+1168], r13
	mov QWORD PTR [rdi+1176], r14
	mov QWORD PTR [rdi+1184], r15
	mov QWORD PTR [rdi+1192], r8
	mov QWORD PTR [rdi+1200], r9
	mov QWORD PTR [rdi+1208], rcx
	mov r13, QWORD PTR [rdi+4048]
	mov r14, QWORD PTR [rdi+4056]
	mov r15, QWORD PTR [rdi+4064]
	mov rcx, r13
	shl rcx, 32
	add rcx, r13
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r13d, 0
	adc r13, 0
	sub r14, rbp
	sbb r15, rdx
	sbb r10, r13
	sbb r11, 0
	sbb r12, 0
	mov r13, rcx
	sbb r13, 0
	mov rcx, r14
	shl rcx, 32
	add rcx, r14
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r14d, 0
	adc r14, 0
	sub r15, rbp
	sbb r10, rdx
	sbb r11, r14
	sbb r12, 0
	sbb r13, 0
	mov r14, rcx
	sbb r14, 0
	mov rcx, r15
	shl rcx, 32
	add rcx, r15
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r15d, 0
	adc r15, 0
	sub r10, rbp
	sbb r11, rdx
	sbb r12, r15
	sbb r13, 0
	sbb r14, 0
	mov r15, rcx
	sbb r15, 0
	mov rcx, r10
	shl rcx, 32
	add rcx, r10
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r10d, 0
	adc r10, 0
	sub r11, rbp
	sbb r12, rdx
	sbb r13, r10
	sbb r14, 0
	sbb r15, 0
	mov r10, rcx
	sbb r10, 0
	mov rcx, r11
	shl rcx, 32
	add rcx, r11
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r11d, 0
	adc r11, 0
	sub r12, rbp
	sbb r13, rdx
	sbb r14, r11
	sbb r15, 0
	sbb r10, 0
	mov r11, rcx
	sbb r11, 0
	mov rcx, r12
	shl rcx, 32
	add rcx, r12
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r12d, 0
	adc r12, 0
	sub r13, rbp
	sbb r14, rdx
	sbb r15, r12
	sbb r10, 0
	sbb r11, 0
	mov r12, rcx
	sbb r12, 0
	mov r8d, 0
	add r13, QWORD PTR [rdi+1168]
	adc r14, QWORD PTR [rdi+1176]
	adc r15, QWORD PTR [rdi+1184]
	adc r10, QWORD PTR [rdi+1192]
	adc r11, QWORD PTR [rdi+1200]
	adc r12, QWORD PTR [rdi+1208]
	adc r8, 0
	sub r13, QWORD PTR [rdi+64]
	sbb r14, QWORD PTR [rdi+72]
	sbb r15, QWORD PTR [rdi+80]
	sbb r10, QWORD PTR [rdi+88]
	sbb r11, QWORD PTR [rdi+96]
	sbb r12, QWORD PTR [rdi+104]
	sbb r8, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r13, rcx
	adc r14, rdx
	adc r15, rbp
	adc r10, rax
	adc r11, rax
	adc r12, rax
	mov QWORD PTR [rdi+1168], r13
	mov QWORD PTR [rdi+1176], r14
	mov QWORD PTR [rdi+1184], r15
	mov QWORD PTR [rdi+1192], r10
	mov QWORD PTR [rdi+1200], r11
	mov QWORD PTR [rdi+1208], r12
	mov rcx, QWORD PTR [rdi+784]
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov ebp, 0
	mov rax, QWORD PTR [rdi+792]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+800]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+808]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov r13, rbp
	mov QWORD PTR [rdi+4056], r8
	mov QWORD PTR [rdi+4064], r9
	mov rcx, QWORD PTR [rdi+792]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+800]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+808]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov r14, rbp
	mov rcx, QWORD PTR [rdi+800]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+808]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov r15, rbp
	mov rcx, QWORD PTR [rdi+808]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov r8, rbp
	mov rcx, QWORD PTR [rdi+816]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov r9, rbp
	mov rax, QWORD PTR [rdi+4056]
	add rax, rax
	mov QWORD PTR [rdi+4056], rax
	mov rax, QWORD PTR [rdi+4064]
	adc rax, rax
	mov QWORD PTR [rdi+4064], rax
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	adc r8, r8
	adc r9, r9
	mov ecx, 0
	adc rcx, rcx
	mov rax, QWORD PTR [rdi+784]
	mul rax
	mov QWORD PTR [rdi+4048], rax
	add rdx, QWORD PTR [rdi+4056]
	mov QWORD PTR [rdi+4056], rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+792]
	mul rax
	add rax, rbp
	adc rdx, 0
	add rax, QWORD PTR [rdi+4064]
	mov QWORD PTR [rdi+4064], rax
	adc r10, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+800]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc r12, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+808]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc r14, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+816]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc r8, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+824]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rcx, rdx
	mov ebp, 0
	adc rbp, 0
	mov QWORD PTR [rdi+1216], r13
	mov QWORD PTR [rdi+1224], r14
	mov QWORD PTR [rdi+1232], r15
	mov QWORD PTR [rdi+1240], r8
	mov QWORD PTR [rdi+1248], r9
	mov QWORD PTR [rdi+1256], rcx
	mov r13, QWORD PTR [rdi+4048]
	mov r14, QWORD PTR [rdi+4056]
	mov r15, QWORD PTR [rdi+4064]
	mov rcx, r13
	shl rcx, 32
	add rcx, r13
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r13d, 0
	adc r13, 0
	sub r14, rbp
	sbb r15, rdx
	sbb r10, r13
	sbb r11, 0
	sbb r12, 0
	mov r13, rcx
	sbb r13, 0
	mov rcx, r14
	shl rcx, 32
	add rcx, r14
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r14d, 0
	adc r14, 0
	sub r15, rbp
	sbb r10, rdx
	sbb r11, r14
	sbb r12, 0
	sbb r13, 0
	mov r14, rcx
	sbb r14, 0
	mov rcx, r15
	shl rcx, 32
	add rcx, r15
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r15d, 0
	adc r15, 0
	sub r10, rbp
	sbb r11, rdx
	sbb r12, r15
	sbb r13, 0
	sbb r14, 0
	mov r15, rcx
	sbb r15, 0
	mov rcx, r10
	shl rcx, 32
	add rcx, r10
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r10d, 0
	adc r10, 0
	sub r11, rbp
	sbb r12, rdx
	sbb r13, r10
	sbb r14, 0
	sbb r15, 0
	mov r10, rcx
	sbb r10, 0
	mov rcx, r11
	shl rcx, 32
	add rcx, r11
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r11d, 0
	adc r11, 0
	sub r12, rbp
	sbb r13, rdx
	sbb r14, r11
	sbb r15, 0
	sbb r10, 0
	mov r11, rcx
	sbb r11, 0
	mov rcx, r12
	shl rcx, 32
	add rcx, r12
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r12d, 0
	adc r12, 0
	sub r13, rbp
	sbb r14, rdx
	sbb r15, r12
	sbb r10, 0
	sbb r11, 0
	mov r12, rcx
	sbb r12, 0
	mov r8d, 0
	add r13, QWORD PTR [rdi+1216]
	adc r14, QWORD PTR [rdi+1224]
	adc r15, QWORD PTR [rdi+1232]
	adc r10, QWORD PTR [rdi+1240]
	adc r11, QWORD PTR [rdi+1248]
	adc r12, QWORD PTR [rdi+1256]
	adc r8, 0
	sub r13, QWORD PTR [rdi+64]
	sbb r14, QWORD PTR [rdi+72]
	sbb r15, QWORD PTR [rdi+80]
	sbb r10, QWORD PTR [rdi+88]
	sbb r11, QWORD PTR [rdi+96]
	sbb r12, QWORD PTR [rdi+104]
	sbb r8, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r13, rcx
	adc r14, rdx
	adc r15, rbp
	adc r10, rax
	adc r11, rax
	adc r12, rax
	mov QWORD PTR [rdi+1216], r13
	mov QWORD PTR [rdi+1224], r14
	mov QWORD PTR [rdi+1232], r15
	mov QWORD PTR [rdi+1240], r10
	mov QWORD PTR [rdi+1248], r11
	mov QWORD PTR [rdi+1256], r12
	mov r8, QWORD PTR [rdi+1216]
	mov r9, QWORD PTR [rdi+1224]
	mov r10, QWORD PTR [rdi+1232]
	mov r11, QWORD PTR [rdi+1240]
	mov r12, QWORD PTR [rdi+1248]
	mov r13, QWORD PTR [rdi+1256]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1216]
	adc r9, QWORD PTR [rdi+1224]
	adc r10, QWORD PTR [rdi+1232]
	adc r11, QWORD PTR [rdi+1240]
	adc r12, QWORD PTR [rdi+1248]
	adc r13, QWORD PTR [rdi+1256]
	adc r14, 0
	sub r8, QWORD PTR [rdi+64]
	sbb r9, QWORD PTR [rdi+72]
	sbb r10, QWORD PTR [rdi+80]
	sbb r11, QWORD PTR [rdi+88]
	sbb r12, QWORD PTR [rdi+96]
	sbb r13, QWORD PTR [rdi+104]
	sbb r14, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1216], r8
	mov QWORD PTR [rdi+1224], r9
	mov QWORD PTR [rdi+1232], r10
	mov QWORD PTR [rdi+1240], r11
	mov QWORD PTR [rdi+1248], r12
	mov QWORD PTR [rdi+1256], r13
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+736]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, r8
	shl rcx, 32
	add rcx, r8
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r8d, 0
	adc r8, 0
	sub r9, rbp
	sbb r10, rdx
	sbb r11, r8
	sbb r12, 0
	sbb r13, 0
	sbb rcx, 0
	add r14, rcx
	adc r15, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+744]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, r9
	shl rcx, 32
	add rcx, r9
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r9d, 0
	adc r9, 0
	sub r10, rbp
	sbb r11, rdx
	sbb r12, r9
	sbb r13, 0
	sbb r14, 0
	sbb rcx, 0
	add r15, rcx
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+752]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, r10
	shl rcx, 32
	add rcx, r10
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r10d, 0
	adc r10, 0
	sub r11, rbp
	sbb r12, rdx
	sbb r13, r10
	sbb r14, 0
	sbb r15, 0
	sbb rcx, 0
	add r8, rcx
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+760]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, r11
	shl rcx, 32
	add rcx, r11
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r11d, 0
	adc r11, 0
	sub r12, rbp
	sbb r13, rdx
	sbb r14, r11
	sbb r15, 0
	sbb r8, 0
	sbb rcx, 0
	add r9, rcx
	adc r10, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+768]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, r12
	shl rcx, 32
	add rcx, r12
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r12d, 0
	adc r12, 0
	sub r13, rbp
	sbb r14, rdx
	sbb r15, r12
	sbb r8, 0
	sbb r9, 0
	sbb rcx, 0
	add r10, rcx
	adc r11, 0
	mov r12d, 0
	mov rcx, QWORD PTR [rdi+776]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rcx, r13
	shl rcx, 32
	add rcx, r13
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r13d, 0
	adc r13, 0
	sub r14, rbp
	sbb r15, rdx
	sbb r8, r13
	sbb r9, 0
	sbb r10, 0
	sbb rcx, 0
	add r11, rcx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+1264], r14
	mov QWORD PTR [rdi+1272], r15
	mov QWORD PTR [rdi+1280], r8
	mov QWORD PTR [rdi+1288], r9
	mov QWORD PTR [rdi+1296], r10
	mov QWORD PTR [rdi+1304], r11
	mov r8, QWORD PTR [rdi+736]
	mov r9, QWORD PTR [rdi+744]
	mov r10, QWORD PTR [rdi+752]
	mov r11, QWORD PTR [rdi+760]
	mov r12, QWORD PTR [rdi+768]
	mov r13, QWORD PTR [rdi+776]
	sub r8, QWORD PTR [rdi+1168]
	sbb r9, QWORD PTR [rdi+1176]
	sbb r10, QWORD PTR [rdi+1184]
	sbb r11, QWORD PTR [rdi+1192]
	sbb r12, QWORD PTR [rdi+1200]
	sbb r13, QWORD PTR [rdi+1208]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1312], r8
	mov QWORD PTR [rdi+1320], r9
	mov QWORD PTR [rdi+1328], r10
	mov QWORD PTR [rdi+1336], r11
	mov QWORD PTR [rdi+1344], r12
	mov QWORD PTR [rdi+1352], r13
	mov r8, QWORD PTR [rdi+736]
	mov r9, QWORD PTR [rdi+744]
	mov r10, QWORD PTR [rdi+752]
	mov r11, QWORD PTR [rdi+760]
	mov r12, QWORD PTR [rdi+768]
	mov r13, QWORD PTR [rdi+776]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1168]
	adc r9, QWORD PTR [rdi+1176]
	adc r10, QWORD PTR [rdi+1184]
	adc r11, QWORD PTR [rdi+1192]
	adc r12, QWORD PTR [rdi+1200]
	adc r13, QWORD PTR [rdi+1208]
	adc r14, 0
	sub r8, QWORD PTR [rdi+64]
	sbb r9, QWORD PTR [rdi+72]
	sbb r10, QWORD PTR [rdi+80]
	sbb r11, QWORD PTR [rdi+88]
	sbb r12, QWORD PTR [rdi+96]
	sbb r13, QWORD PTR [rdi+104]
	sbb r14, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+736], r8
	mov QWORD PTR [rdi+744], r9
	mov QWORD PTR [rdi+752], r10
	mov QWORD PTR [rdi+760], r11
	mov QWORD PTR [rdi+768], r12
	mov QWORD PTR [rdi+776], r13
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1312]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+736]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+744]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+752]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+760]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+768]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+776]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, r8
	shl rcx, 32
	add rcx, r8
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r8d, 0
	adc r8, 0
	sub r9, rbp
	sbb r10, rdx
	sbb r11, r8
	sbb r12, 0
	sbb r13, 0
	sbb rcx, 0
	add r14, rcx
	adc r15, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+1320]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+736]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+744]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+752]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+760]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+768]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+776]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, r9
	shl rcx, 32
	add rcx, r9
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r9d, 0
	adc r9, 0
	sub r10, rbp
	sbb r11, rdx
	sbb r12, r9
	sbb r13, 0
	sbb r14, 0
	sbb rcx, 0
	add r15, rcx
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1328]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+736]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+744]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+752]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+760]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+768]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+776]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, r10
	shl rcx, 32
	add rcx, r10
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r10d, 0
	adc r10, 0
	sub r11, rbp
	sbb r12, rdx
	sbb r13, r10
	sbb r14, 0
	sbb r15, 0
	sbb rcx, 0
	add r8, rcx
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1336]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+736]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+744]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+752]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+760]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+768]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+776]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, r11
	shl rcx, 32
	add rcx, r11
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r11d, 0
	adc r11, 0
	sub r12, rbp
	sbb r13, rdx
	sbb r14, r11
	sbb r15, 0
	sbb r8, 0
	sbb rcx, 0
	add r9, rcx
	adc r10, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1344]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+736]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+744]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+752]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+760]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+768]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+776]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, r12
	shl rcx, 32
	add rcx, r12
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r12d, 0
	adc r12, 0
	sub r13, rbp
	sbb r14, rdx
	sbb r15, r12
	sbb r8, 0
	sbb r9, 0
	sbb rcx, 0
	add r10, rcx
	adc r11, 0
	mov r12d, 0
	mov rcx, QWORD PTR [rdi+1352]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+736]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+744]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+752]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+760]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+768]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+776]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rcx, r13
	shl rcx, 32
	add rcx, r13
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r13d, 0
	adc r13, 0
	sub r14, rbp
	sbb r15, rdx
	sbb r8, r13
	sbb r9, 0
	sbb r10, 0
	sbb rcx, 0
	add r11, rcx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+1312], r14
	mov QWORD PTR [rdi+1320], r15
	mov QWORD PTR [rdi+1328], r8
	mov QWORD PTR [rdi+1336], r9
	mov QWORD PTR [rdi+1344], r10
	mov QWORD PTR [rdi+1352], r11
	mov r8, QWORD PTR [rdi+1312]
	mov r9, QWORD PTR [rdi+1320]
	mov r10, QWORD PTR [rdi+1328]
	mov r11, QWORD PTR [rdi+1336]
	mov r12, QWORD PTR [rdi+1344]
	mov r13, QWORD PTR [rdi+1352]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1312]
	adc r9, QWORD PTR [rdi+1320]
	adc r10, QWORD PTR [rdi+1328]
	adc r11, QWORD PTR [rdi+1336]
	adc r12, QWORD PTR [rdi+1344]
	adc r13, QWORD PTR [rdi+1352]
	adc r14, 0
	sub r8, QWORD PTR [rdi+64]
	sbb r9, QWORD PTR [rdi+72]
	sbb r10, QWORD PTR [rdi+80]
	sbb r11, QWORD PTR [rdi+88]
	sbb r12, QWORD PTR [rdi+96]
	sbb r13, QWORD PTR [rdi+104]
	sbb r14, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+736], r8
	mov QWORD PTR [rdi+744], r9
	mov QWORD PTR [rdi+752], r10
	mov QWORD PTR [rdi+760], r11
	mov QWORD PTR [rdi+768], r12
	mov QWORD PTR [rdi+776], r13
	mov r8, QWORD PTR [rdi+736]
	mov r9, QWORD PTR [rdi+744]
	mov r10, QWORD PTR [rdi+752]
	mov r11, QWORD PTR [rdi+760]
	mov r12, QWORD PTR [rdi+768]
	mov r13, QWORD PTR [rdi+776]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1312]
	adc r9, QWORD PTR [rdi+1320]
	adc r10, QWORD PTR [rdi+1328]
	adc r11, QWORD PTR [rdi+1336]
	adc r12, QWORD PTR [rdi+1344]
	adc r13, QWORD PTR [rdi+1352]
	adc r14, 0
	sub r8, QWORD PTR [rdi+64]
	sbb r9, QWORD PTR [rdi+72]
	sbb r10, QWORD PTR [rdi+80]
	sbb r11, QWORD PTR [rdi+88]
	sbb r12, QWORD PTR [rdi+96]
	sbb r13, QWORD PTR [rdi+104]
	sbb r14, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1312], r8
	mov QWORD PTR [rdi+1320], r9
	mov QWORD PTR [rdi+1328], r10
	mov QWORD PTR [rdi+1336], r11
	mov QWORD PTR [rdi+1344], r12
	mov QWORD PTR [rdi+1352], r13
	mov r8, QWORD PTR [rdi+1264]
	mov r9, QWORD PTR [rdi+1272]
	mov r10, QWORD PTR [rdi+1280]
	mov r11, QWORD PTR [rdi+1288]
	mov r12, QWORD PTR [rdi+1296]
	mov r13, QWORD PTR [rdi+1304]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1264]
	adc r9, QWORD PTR [rdi+1272]
	adc r10, QWORD PTR [rdi+1280]
	adc r11, QWORD PTR [rdi+1288]
	adc r12, QWORD PTR [rdi+1296]
	adc r13, QWORD PTR [rdi+1304]
	adc r14, 0
	sub r8, QWORD PTR [rdi+64]
	sbb r9, QWORD PTR [rdi+72]
	sbb r10, QWORD PTR [rdi+80]
	sbb r11, QWORD PTR [rdi+88]
	sbb r12, QWORD PTR [rdi+96]
	sbb r13, QWORD PTR [rdi+104]
	sbb r14, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1264], r8
	mov QWORD PTR [rdi+1272], r9
	mov QWORD PTR [rdi+1280], r10
	mov QWORD PTR [rdi+1288], r11
	mov QWORD PTR [rdi+1296], r12
	mov QWORD PTR [rdi+1304], r13
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+784]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+832]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+840]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+848]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+856]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+864]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+872]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, r8
	shl rcx, 32
	add rcx, r8
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r8d, 0
	adc r8, 0
	sub r9, rbp
	sbb r10, rdx
	sbb r11, r8
	sbb r12, 0
	sbb r13, 0
	sbb rcx, 0
	add r14, rcx
	adc r15, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+792]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+832]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+840]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+848]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+856]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+864]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+872]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, r9
	shl rcx, 32
	add rcx, r9
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r9d, 0
	adc r9, 0
	sub r10, rbp
	sbb r11, rdx
	sbb r12, r9
	sbb r13, 0
	sbb r14, 0
	sbb rcx, 0
	add r15, rcx
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+800]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+832]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+840]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+848]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+856]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+864]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+872]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, r10
	shl rcx, 32
	add rcx, r10
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r10d, 0
	adc r10, 0
	sub r11, rbp
	sbb r12, rdx
	sbb r13, r10
	sbb r14, 0
	sbb r15, 0
	sbb rcx, 0
	add r8, rcx
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+808]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+832]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+840]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+848]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+856]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+864]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+872]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, r11
	shl rcx, 32
	add rcx, r11
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r11d, 0
	adc r11, 0
	sub r12, rbp
	sbb r13, rdx
	sbb r14, r11
	sbb r15, 0
	sbb r8, 0
	sbb rcx, 0
	add r9, rcx
	adc r10, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+816]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+832]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+840]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+848]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+856]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+864]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+872]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, r12
	shl rcx, 32
	add rcx, r12
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r12d, 0
	adc r12, 0
	sub r13, rbp
	sbb r14, rdx
	sbb r15, r12
	sbb r8, 0
	sbb r9, 0
	sbb rcx, 0
	add r10, rcx
	adc r11, 0
	mov r12d, 0
	mov rcx, QWORD PTR [rdi+824]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+832]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+840]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+848]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+856]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+864]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+872]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rcx, r13
	shl rcx, 32
	add rcx, r13
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r13d, 0
	adc r13, 0
	sub r14, rbp
	sbb r15, rdx
	sbb r8, r13
	sbb r9, 0
	sbb r10, 0
	sbb rcx, 0
	add r11, rcx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+832], r14
	mov QWORD PTR [rdi+840], r15
	mov QWORD PTR [rdi+848], r8
	mov QWORD PTR [rdi+856], r9
	mov QWORD PTR [rdi+864], r10
	mov QWORD PTR [rdi+872], r11
	mov r8, QWORD PTR [rdi+832]
	mov r9, QWORD PTR [rdi+840]
	mov r10, QWORD PTR [rdi+848]
	mov r11, QWORD PTR [rdi+856]
	mov r12, QWORD PTR [rdi+864]
	mov r13, QWORD PTR [rdi+872]
	mov r14d, 0
	add r8, QWORD PTR [rdi+832]
	adc r9, QWORD PTR [rdi+840]
	adc r10, QWORD PTR [rdi+848]
	adc r11, QWORD PTR [rdi+856]
	adc r12, QWORD PTR [rdi+864]
	adc r13, QWORD PTR [rdi+872]
	adc r14, 0
	sub r8, QWORD PTR [rdi+64]
	sbb r9, QWORD PTR [rdi+72]
	sbb r10, QWORD PTR [rdi+80]
	sbb r11, QWORD PTR [rdi+88]
	sbb r12, QWORD PTR [rdi+96]
	sbb r13, QWORD PTR [rdi+104]
	sbb r14, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+832], r8
	mov QWORD PTR [rdi+840], r9
	mov QWORD PTR [rdi+848], r10
	mov QWORD PTR [rdi+856], r11
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
	mov rcx, QWORD PTR [rdi+1312]
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1320]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1328]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1336]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1344]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1352]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov r13, rbp
	mov QWORD PTR [rdi+4056], r8
	mov QWORD PTR [rdi+4064], r9
	mov rcx, QWORD PTR [rdi+1320]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1328]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1336]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1344]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1352]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov r14, rbp
	mov rcx, QWORD PTR [rdi+1328]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1336]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1344]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1352]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov r15, rbp
	mov rcx, QWORD PTR [rdi+1336]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1344]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1352]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov r8, rbp
	mov rcx, QWORD PTR [rdi+1344]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1352]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov r9, rbp
	mov rax, QWORD PTR [rdi+4056]
	add rax, rax
	mov QWORD PTR [rdi+4056], rax
	mov rax, QWORD PTR [rdi+4064]
	adc rax, rax
	mov QWORD PTR [rdi+4064], rax
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	adc r8, r8
	adc r9, r9
	mov ecx, 0
	adc rcx, rcx
	mov rax, QWORD PTR [rdi+1312]
	mul rax
	mov QWORD PTR [rdi+4048], rax
	add rdx, QWORD PTR [rdi+4056]
	mov QWORD PTR [rdi+4056], rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1320]
	mul rax
	add rax, rbp
	adc rdx, 0
	add rax, QWORD PTR [rdi+4064]
	mov QWORD PTR [rdi+4064], rax
	adc r10, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1328]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc r12, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1336]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc r14, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1344]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc r8, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1352]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rcx, rdx
	mov ebp, 0
	adc rbp, 0
	mov QWORD PTR [rdi+736], r13
	mov QWORD PTR [rdi+744], r14
	mov QWORD PTR [rdi+752], r15
	mov QWORD PTR [rdi+760], r8
	mov QWORD PTR [rdi+768], r9
	mov QWORD PTR [rdi+776], rcx
	mov r13, QWORD PTR [rdi+4048]
	mov r14, QWORD PTR [rdi+4056]
	mov r15, QWORD PTR [rdi+4064]
	mov rcx, r13
	shl rcx, 32
	add rcx, r13
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r13d, 0
	adc r13, 0
	sub r14, rbp
	sbb r15, rdx
	sbb r10, r13
	sbb r11, 0
	sbb r12, 0
	mov r13, rcx
	sbb r13, 0
	mov rcx, r14
	shl rcx, 32
	add rcx, r14
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r14d, 0
	adc r14, 0
	sub r15, rbp
	sbb r10, rdx
	sbb r11, r14
	sbb r12, 0
	sbb r13, 0
	mov r14, rcx
	sbb r14, 0
	mov rcx, r15
	shl rcx, 32
	add rcx, r15
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r15d, 0
	adc r15, 0
	sub r10, rbp
	sbb r11, rdx
	sbb r12, r15
	sbb r13, 0
	sbb r14, 0
	mov r15, rcx
	sbb r15, 0
	mov rcx, r10
	shl rcx, 32
	add rcx, r10
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r10d, 0
	adc r10, 0
	sub r11, rbp
	sbb r12, rdx
	sbb r13, r10
	sbb r14, 0
	sbb r15, 0
	mov r10, rcx
	sbb r10, 0
	mov rcx, r11
	shl rcx, 32
	add rcx, r11
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r11d, 0
	adc r11, 0
	sub r12, rbp
	sbb r13, rdx
	sbb r14, r11
	sbb r15, 0
	sbb r10, 0
	mov r11, rcx
	sbb r11, 0
	mov rcx, r12
	shl rcx, 32
	add rcx, r12
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r12d, 0
	adc r12, 0
	sub r13, rbp
	sbb r14, rdx
	sbb r15, r12
	sbb r10, 0
	sbb r11, 0
	mov r12, rcx
	sbb r12, 0
	mov r8d, 0
	add r13, QWORD PTR [rdi+736]
	adc r14, QWORD PTR [rdi+744]
	adc r15, QWORD PTR [rdi+752]
	adc r10, QWORD PTR [rdi+760]
	adc r11, QWORD PTR [rdi+768]
	adc r12, QWORD PTR [rdi+776]
	adc r8, 0
	sub r13, QWORD PTR [rdi+64]
	sbb r14, QWORD PTR [rdi+72]
	sbb r15, QWORD PTR [rdi+80]
	sbb r10, QWORD PTR [rdi+88]
	sbb r11, QWORD PTR [rdi+96]
	sbb r12, QWORD PTR [rdi+104]
	sbb r8, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r13, rcx
	adc r14, rdx
	adc r15, rbp
	adc r10, rax
	adc r11, rax
	adc r12, rax
	mov QWORD PTR [rdi+736], r13
	mov QWORD PTR [rdi+744], r14
	mov QWORD PTR [rdi+752], r15
	mov QWORD PTR [rdi+760], r10
	mov QWORD PTR [rdi+768], r11
	mov QWORD PTR [rdi+776], r12
	mov r8, QWORD PTR [rdi+736]
	mov r9, QWORD PTR [rdi+744]
	mov r10, QWORD PTR [rdi+752]
	mov r11, QWORD PTR [rdi+760]
	mov r12, QWORD PTR [rdi+768]
	mov r13, QWORD PTR [rdi+776]
	sub r8, QWORD PTR [rdi+1264]
	sbb r9, QWORD PTR [rdi+1272]
	sbb r10, QWORD PTR [rdi+1280]
	sbb r11, QWORD PTR [rdi+1288]
	sbb r12, QWORD PTR [rdi+1296]
	sbb r13, QWORD PTR [rdi+1304]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+736], r8
	mov QWORD PTR [rdi+744], r9
	mov QWORD PTR [rdi+752], r10
	mov QWORD PTR [rdi+760], r11
	mov QWORD PTR [rdi+768], r12
	mov QWORD PTR [rdi+776], r13
	mov r8, QWORD PTR [rdi+736]
	mov r9, QWORD PTR [rdi+744]
	mov r10, QWORD PTR [rdi+752]
	mov r11, QWORD PTR [rdi+760]
	mov r12, QWORD PTR [rdi+768]
	mov r13, QWORD PTR [rdi+776]
	sub r8, QWORD PTR [rdi+1264]
	sbb r9, QWORD PTR [rdi+1272]
	sbb r10, QWORD PTR [rdi+1280]
	sbb r11, QWORD PTR [rdi+1288]
	sbb r12, QWORD PTR [rdi+1296]
	sbb r13, QWORD PTR [rdi+1304]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+736], r8
	mov QWORD PTR [rdi+744], r9
	mov QWORD PTR [rdi+752], r10
	mov QWORD PTR [rdi+760], r11
	mov QWORD PTR [rdi+768], r12
	mov QWORD PTR [rdi+776], r13
	mov r8, QWORD PTR [rdi+1264]
	mov r9, QWORD PTR [rdi+1272]
	mov r10, QWORD PTR [rdi+1280]
	mov r11, QWORD PTR [rdi+1288]
	mov r12, QWORD PTR [rdi+1296]
	mov r13, QWORD PTR [rdi+1304]
	sub r8, QWORD PTR [rdi+736]
	sbb r9, QWORD PTR [rdi+744]
	sbb r10, QWORD PTR [rdi+752]
	sbb r11, QWORD PTR [rdi+760]
	sbb r12, QWORD PTR [rdi+768]
	sbb r13, QWORD PTR [rdi+776]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+784], r8
	mov QWORD PTR [rdi+792], r9
	mov QWORD PTR [rdi+800], r10
	mov QWORD PTR [rdi+808], r11
	mov QWORD PTR [rdi+816], r12
	mov QWORD PTR [rdi+824], r13
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1312]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+784]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+792]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+800]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+808]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, r8
	shl rcx, 32
	add rcx, r8
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r8d, 0
	adc r8, 0
	sub r9, rbp
	sbb r10, rdx
	sbb r11, r8
	sbb r12, 0
	sbb r13, 0
	sbb rcx, 0
	add r14, rcx
	adc r15, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+1320]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+784]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+792]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+800]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+808]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, r9
	shl rcx, 32
	add rcx, r9
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r9d, 0
	adc r9, 0
	sub r10, rbp
	sbb r11, rdx
	sbb r12, r9
	sbb r13, 0
	sbb r14, 0
	sbb rcx, 0
	add r15, rcx
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1328]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+784]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+792]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+800]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+808]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, r10
	shl rcx, 32
	add rcx, r10
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r10d, 0
	adc r10, 0
	sub r11, rbp
	sbb r12, rdx
	sbb r13, r10
	sbb r14, 0
	sbb r15, 0
	sbb rcx, 0
	add r8, rcx
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1336]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+784]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+792]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+800]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+808]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, r11
	shl rcx, 32
	add rcx, r11
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r11d, 0
	adc r11, 0
	sub r12, rbp
	sbb r13, rdx
	sbb r14, r11
	sbb r15, 0
	sbb r8, 0
	sbb rcx, 0
	add r9, rcx
	adc r10, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1344]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+784]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+792]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+800]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+808]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, r12
	shl rcx, 32
	add rcx, r12
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r12d, 0
	adc r12, 0
	sub r13, rbp
	sbb r14, rdx
	sbb r15, r12
	sbb r8, 0
	sbb r9, 0
	sbb rcx, 0
	add r10, rcx
	adc r11, 0
	mov r12d, 0
	mov rcx, QWORD PTR [rdi+1352]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+784]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+792]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+800]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+808]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rcx, r13
	shl rcx, 32
	add rcx, r13
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r13d, 0
	adc r13, 0
	sub r14, rbp
	sbb r15, rdx
	sbb r8, r13
	sbb r9, 0
	sbb r10, 0
	sbb rcx, 0
	add r11, rcx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+784], r14
	mov QWORD PTR [rdi+792], r15
	mov QWORD PTR [rdi+800], r8
	mov QWORD PTR [rdi+808], r9
	mov QWORD PTR [rdi+816], r10
	mov QWORD PTR [rdi+824], r11
	mov rcx, QWORD PTR [rdi+1216]
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov r13, rbp
	mov QWORD PTR [rdi+4056], r8
	mov QWORD PTR [rdi+4064], r9
	mov rcx, QWORD PTR [rdi+1224]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov r14, rbp
	mov rcx, QWORD PTR [rdi+1232]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov r15, rbp
	mov rcx, QWORD PTR [rdi+1240]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov r8, rbp
	mov rcx, QWORD PTR [rdi+1248]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov r9, rbp
	mov rax, QWORD PTR [rdi+4056]
	add rax, rax
	mov QWORD PTR [rdi+4056], rax
	mov rax, QWORD PTR [rdi+4064]
	adc rax, rax
	mov QWORD PTR [rdi+4064], rax
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	adc r8, r8
	adc r9, r9
	mov ecx, 0
	adc rcx, rcx
	mov rax, QWORD PTR [rdi+1216]
	mul rax
	mov QWORD PTR [rdi+4048], rax
	add rdx, QWORD PTR [rdi+4056]
	mov QWORD PTR [rdi+4056], rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1224]
	mul rax
	add rax, rbp
	adc rdx, 0
	add rax, QWORD PTR [rdi+4064]
	mov QWORD PTR [rdi+4064], rax
	adc r10, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1232]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc r12, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1240]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc r14, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1248]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc r8, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1256]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rcx, rdx
	mov ebp, 0
	adc rbp, 0
	mov QWORD PTR [rdi+1216], r13
	mov QWORD PTR [rdi+1224], r14
	mov QWORD PTR [rdi+1232], r15
	mov QWORD PTR [rdi+1240], r8
	mov QWORD PTR [rdi+1248], r9
	mov QWORD PTR [rdi+1256], rcx
	mov r13, QWORD PTR [rdi+4048]
	mov r14, QWORD PTR [rdi+4056]
	mov r15, QWORD PTR [rdi+4064]
	mov rcx, r13
	shl rcx, 32
	add rcx, r13
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r13d, 0
	adc r13, 0
	sub r14, rbp
	sbb r15, rdx
	sbb r10, r13
	sbb r11, 0
	sbb r12, 0
	mov r13, rcx
	sbb r13, 0
	mov rcx, r14
	shl rcx, 32
	add rcx, r14
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r14d, 0
	adc r14, 0
	sub r15, rbp
	sbb r10, rdx
	sbb r11, r14
	sbb r12, 0
	sbb r13, 0
	mov r14, rcx
	sbb r14, 0
	mov rcx, r15
	shl rcx, 32
	add rcx, r15
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r15d, 0
	adc r15, 0
	sub r10, rbp
	sbb r11, rdx
	sbb r12, r15
	sbb r13, 0
	sbb r14, 0
	mov r15, rcx
	sbb r15, 0
	mov rcx, r10
	shl rcx, 32
	add rcx, r10
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r10d, 0
	adc r10, 0
	sub r11, rbp
	sbb r12, rdx
	sbb r13, r10
	sbb r14, 0
	sbb r15, 0
	mov r10, rcx
	sbb r10, 0
	mov rcx, r11
	shl rcx, 32
	add rcx, r11
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r11d, 0
	adc r11, 0
	sub r12, rbp
	sbb r13, rdx
	sbb r14, r11
	sbb r15, 0
	sbb r10, 0
	mov r11, rcx
	sbb r11, 0
	mov rcx, r12
	shl rcx, 32
	add rcx, r12
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r12d, 0
	adc r12, 0
	sub r13, rbp
	sbb r14, rdx
	sbb r15, r12
	sbb r10, 0
	sbb r11, 0
	mov r12, rcx
	sbb r12, 0
	mov r8d, 0
	add r13, QWORD PTR [rdi+1216]
	adc r14, QWORD PTR [rdi+1224]
	adc r15, QWORD PTR [rdi+1232]
	adc r10, QWORD PTR [rdi+1240]
	adc r11, QWORD PTR [rdi+1248]
	adc r12, QWORD PTR [rdi+1256]
	adc r8, 0
	sub r13, QWORD PTR [rdi+64]
	sbb r14, QWORD PTR [rdi+72]
	sbb r15, QWORD PTR [rdi+80]
	sbb r10, QWORD PTR [rdi+88]
	sbb r11, QWORD PTR [rdi+96]
	sbb r12, QWORD PTR [rdi+104]
	sbb r8, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r13, rcx
	adc r14, rdx
	adc r15, rbp
	adc r10, rax
	adc r11, rax
	adc r12, rax
	mov QWORD PTR [rdi+1216], r13
	mov QWORD PTR [rdi+1224], r14
	mov QWORD PTR [rdi+1232], r15
	mov QWORD PTR [rdi+1240], r10
	mov QWORD PTR [rdi+1248], r11
	mov QWORD PTR [rdi+1256], r12
	mov r8, QWORD PTR [rdi+1216]
	mov r9, QWORD PTR [rdi+1224]
	mov r10, QWORD PTR [rdi+1232]
	mov r11, QWORD PTR [rdi+1240]
	mov r12, QWORD PTR [rdi+1248]
	mov r13, QWORD PTR [rdi+1256]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1216]
	adc r9, QWORD PTR [rdi+1224]
	adc r10, QWORD PTR [rdi+1232]
	adc r11, QWORD PTR [rdi+1240]
	adc r12, QWORD PTR [rdi+1248]
	adc r13, QWORD PTR [rdi+1256]
	adc r14, 0
	sub r8, QWORD PTR [rdi+64]
	sbb r9, QWORD PTR [rdi+72]
	sbb r10, QWORD PTR [rdi+80]
	sbb r11, QWORD PTR [rdi+88]
	sbb r12, QWORD PTR [rdi+96]
	sbb r13, QWORD PTR [rdi+104]
	sbb r14, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1216], r8
	mov QWORD PTR [rdi+1224], r9
	mov QWORD PTR [rdi+1232], r10
	mov QWORD PTR [rdi+1240], r11
	mov QWORD PTR [rdi+1248], r12
	mov QWORD PTR [rdi+1256], r13
	mov r8, QWORD PTR [rdi+784]
	mov r9, QWORD PTR [rdi+792]
	mov r10, QWORD PTR [rdi+800]
	mov r11, QWORD PTR [rdi+808]
	mov r12, QWORD PTR [rdi+816]
	mov r13, QWORD PTR [rdi+824]
	sub r8, QWORD PTR [rdi+1216]
	sbb r9, QWORD PTR [rdi+1224]
	sbb r10, QWORD PTR [rdi+1232]
	sbb r11, QWORD PTR [rdi+1240]
	sbb r12, QWORD PTR [rdi+1248]
	sbb r13, QWORD PTR [rdi+1256]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+784], r8
	mov QWORD PTR [rdi+792], r9
	mov QWORD PTR [rdi+800], r10
	mov QWORD PTR [rdi+808], r11
	mov QWORD PTR [rdi+816], r12
	mov QWORD PTR [rdi+824], r13
	jmp 217f
216:
217:
	movzx r8d, BYTE PTR [rdi+rbx*1+3568]
	test r8, r8
	je 218f
	cmp r8, 128
	jb 220f
	mov eax, 256
	sub rax, r8
	mov r8, rax
	mov rax, r8
	sub rax, 1
	shr rax, 1
	mov ecx, 144
	mul rcx
	mov rdx, rdi
	add rdx, 4096
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu XMMWORD PTR [rdi+1024], xmm0
	movdqu xmm1, XMMWORD PTR [rdx+16]
	movdqu XMMWORD PTR [rdi+1040], xmm1
	movdqu xmm2, XMMWORD PTR [rdx+32]
	movdqu XMMWORD PTR [rdi+1056], xmm2
	movdqu xmm3, XMMWORD PTR [rdx+48]
	movdqu XMMWORD PTR [rdi+1072], xmm3
	movdqu xmm4, XMMWORD PTR [rdx+64]
	movdqu XMMWORD PTR [rdi+1088], xmm4
	movdqu xmm5, XMMWORD PTR [rdx+80]
	movdqu XMMWORD PTR [rdi+1104], xmm5
	movdqu xmm6, XMMWORD PTR [rdx+96]
	movdqu XMMWORD PTR [rdi+1120], xmm6
	movdqu xmm7, XMMWORD PTR [rdx+112]
	movdqu XMMWORD PTR [rdi+1136], xmm7
	movdqu xmm8, XMMWORD PTR [rdx+128]
	movdqu XMMWORD PTR [rdi+1152], xmm8
	mov rax, r8
	sub rax, 1
	mov ecx, 48
	mul rcx
	mov rdx, rdi
	add rdx, 5392
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu XMMWORD PTR [rdi+6160], xmm0
	movdqu xmm1, XMMWORD PTR [rdx+16]
	movdqu XMMWORD PTR [rdi+6176], xmm1
	movdqu xmm2, XMMWORD PTR [rdx+32]
	movdqu XMMWORD PTR [rdi+6192], xmm2
	movdqu xmm3, XMMWORD PTR [rdx+48]
	movdqu XMMWORD PTR [rdi+6208], xmm3
	movdqu xmm4, XMMWORD PTR [rdx+64]
	movdqu XMMWORD PTR [rdi+6224], xmm4
	movdqu xmm5, XMMWORD PTR [rdx+80]
	movdqu XMMWORD PTR [rdi+6240], xmm5
	mov r8, QWORD PTR [rdi+208]
	mov r9, QWORD PTR [rdi+216]
	mov r10, QWORD PTR [rdi+224]
	mov r11, QWORD PTR [rdi+232]
	mov r12, QWORD PTR [rdi+240]
	mov r13, QWORD PTR [rdi+248]
	sub r8, QWORD PTR [rdi+1072]
	sbb r9, QWORD PTR [rdi+1080]
	sbb r10, QWORD PTR [rdi+1088]
	sbb r11, QWORD PTR [rdi+1096]
	sbb r12, QWORD PTR [rdi+1104]
	sbb r13, QWORD PTR [rdi+1112]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1072], r8
	mov QWORD PTR [rdi+1080], r9
	mov QWORD PTR [rdi+1088], r10
	mov QWORD PTR [rdi+1096], r11
	mov QWORD PTR [rdi+1104], r12
	mov QWORD PTR [rdi+1112], r13
	jmp 221f
220:
	mov rax, r8
	sub rax, 1
	shr rax, 1
	mov ecx, 144
	mul rcx
	mov rdx, rdi
	add rdx, 4096
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu XMMWORD PTR [rdi+1024], xmm0
	movdqu xmm1, XMMWORD PTR [rdx+16]
	movdqu XMMWORD PTR [rdi+1040], xmm1
	movdqu xmm2, XMMWORD PTR [rdx+32]
	movdqu XMMWORD PTR [rdi+1056], xmm2
	movdqu xmm3, XMMWORD PTR [rdx+48]
	movdqu XMMWORD PTR [rdi+1072], xmm3
	movdqu xmm4, XMMWORD PTR [rdx+64]
	movdqu XMMWORD PTR [rdi+1088], xmm4
	movdqu xmm5, XMMWORD PTR [rdx+80]
	movdqu XMMWORD PTR [rdi+1104], xmm5
	movdqu xmm6, XMMWORD PTR [rdx+96]
	movdqu XMMWORD PTR [rdi+1120], xmm6
	movdqu xmm7, XMMWORD PTR [rdx+112]
	movdqu XMMWORD PTR [rdi+1136], xmm7
	movdqu xmm8, XMMWORD PTR [rdx+128]
	movdqu XMMWORD PTR [rdi+1152], xmm8
	mov rax, r8
	sub rax, 1
	mov ecx, 48
	mul rcx
	mov rdx, rdi
	add rdx, 5392
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu XMMWORD PTR [rdi+6160], xmm0
	movdqu xmm1, XMMWORD PTR [rdx+16]
	movdqu XMMWORD PTR [rdi+6176], xmm1
	movdqu xmm2, XMMWORD PTR [rdx+32]
	movdqu XMMWORD PTR [rdi+6192], xmm2
	movdqu xmm3, XMMWORD PTR [rdx+48]
	movdqu XMMWORD PTR [rdi+6208], xmm3
	movdqu xmm4, XMMWORD PTR [rdx+64]
	movdqu XMMWORD PTR [rdi+6224], xmm4
	movdqu xmm5, XMMWORD PTR [rdx+80]
	movdqu XMMWORD PTR [rdi+6240], xmm5
221:
	call {vg_p384_jac_add_cached}
	jmp 219f
218:
219:
	movzx r8d, WORD PTR [rdi+rbx*2+6400]
	test r8, r8
	je 222f
	cmp r8, 256
	jb 224f
	mov eax, 65536
	sub rax, r8
	mov r8, rax
	mov rax, r8
	sub rax, 1
	mov ecx, 96
	mul rcx
	lea rdx, {VG_P384_GTAB}
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu XMMWORD PTR [rdi+1024], xmm0
	movdqu xmm1, XMMWORD PTR [rdx+16]
	movdqu XMMWORD PTR [rdi+1040], xmm1
	movdqu xmm2, XMMWORD PTR [rdx+32]
	movdqu XMMWORD PTR [rdi+1056], xmm2
	movdqu xmm3, XMMWORD PTR [rdx+48]
	movdqu XMMWORD PTR [rdi+1072], xmm3
	movdqu xmm4, XMMWORD PTR [rdx+64]
	movdqu XMMWORD PTR [rdi+1088], xmm4
	movdqu xmm5, XMMWORD PTR [rdx+80]
	movdqu XMMWORD PTR [rdi+1104], xmm5
	movabs rax, -4294967295
	mov QWORD PTR [rdi+1120], rax
	movabs rax, 4294967295
	mov QWORD PTR [rdi+1128], rax
	movabs rax, 1
	mov QWORD PTR [rdi+1136], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1144], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1152], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1160], rax
	mov r8, QWORD PTR [rdi+208]
	mov r9, QWORD PTR [rdi+216]
	mov r10, QWORD PTR [rdi+224]
	mov r11, QWORD PTR [rdi+232]
	mov r12, QWORD PTR [rdi+240]
	mov r13, QWORD PTR [rdi+248]
	sub r8, QWORD PTR [rdi+1072]
	sbb r9, QWORD PTR [rdi+1080]
	sbb r10, QWORD PTR [rdi+1088]
	sbb r11, QWORD PTR [rdi+1096]
	sbb r12, QWORD PTR [rdi+1104]
	sbb r13, QWORD PTR [rdi+1112]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1072], r8
	mov QWORD PTR [rdi+1080], r9
	mov QWORD PTR [rdi+1088], r10
	mov QWORD PTR [rdi+1096], r11
	mov QWORD PTR [rdi+1104], r12
	mov QWORD PTR [rdi+1112], r13
	jmp 225f
224:
	mov rax, r8
	sub rax, 1
	mov ecx, 96
	mul rcx
	lea rdx, {VG_P384_GTAB}
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu XMMWORD PTR [rdi+1024], xmm0
	movdqu xmm1, XMMWORD PTR [rdx+16]
	movdqu XMMWORD PTR [rdi+1040], xmm1
	movdqu xmm2, XMMWORD PTR [rdx+32]
	movdqu XMMWORD PTR [rdi+1056], xmm2
	movdqu xmm3, XMMWORD PTR [rdx+48]
	movdqu XMMWORD PTR [rdi+1072], xmm3
	movdqu xmm4, XMMWORD PTR [rdx+64]
	movdqu XMMWORD PTR [rdi+1088], xmm4
	movdqu xmm5, XMMWORD PTR [rdx+80]
	movdqu XMMWORD PTR [rdi+1104], xmm5
	movabs rax, -4294967295
	mov QWORD PTR [rdi+1120], rax
	movabs rax, 4294967295
	mov QWORD PTR [rdi+1128], rax
	movabs rax, 1
	mov QWORD PTR [rdi+1136], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1144], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1152], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1160], rax
225:
	call {vg_p384_jac_add_affine}
	jmp 223f
222:
223:
	test rbx, rbx
	jne 215b
	mov r12, rsi
	mov esi, 832
	mov edx, 832
	mov ecx, 832
	call {vg_p384_mul_mod_p}
	mov rsi, r12
	movabs rax, -8589934591
	mov QWORD PTR [rdi+1696], rax
	movabs rax, 8589934592
	mov QWORD PTR [rdi+1704], rax
	movabs rax, -8589934592
	mov QWORD PTR [rdi+1712], rax
	movabs rax, 8589934592
	mov QWORD PTR [rdi+1720], rax
	movabs rax, 1
	mov QWORD PTR [rdi+1728], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1736], rax
	movabs rax, 2316802901605165427
	mov QWORD PTR [rdi+1456], rax
	movabs rax, -2580967570294927855
	mov QWORD PTR [rdi+1464], rax
	movabs rax, 633002615215383305
	mov QWORD PTR [rdi+1472], rax
	movabs rax, 5499242126189750188
	mov QWORD PTR [rdi+1480], rax
	movabs rax, -4079331617873953950
	mov QWORD PTR [rdi+1488], rax
	movabs rax, -1
	mov QWORD PTR [rdi+1496], rax
	movabs rax, 1374695844057110156
	mov QWORD PTR [rdi+112], rax
	movabs rax, -6348401688401979259
	mov QWORD PTR [rdi+120], rax
	movabs rax, 4079331616924160543
	mov QWORD PTR [rdi+128], rax
	movabs rax, 0
	mov QWORD PTR [rdi+136], rax
	movabs rax, 0
	mov QWORD PTR [rdi+144], rax
	movabs rax, 0
	mov QWORD PTR [rdi+152], rax
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1552]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1696]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1704]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1712]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1720]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r14, rbp
	adc r15, 0
	mov rcx, r8
	shl rcx, 32
	add rcx, r8
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r8d, 0
	adc r8, 0
	sub r9, rbp
	sbb r10, rdx
	sbb r11, r8
	sbb r12, 0
	sbb r13, 0
	sbb rcx, 0
	add r14, rcx
	adc r15, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+1560]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1696]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1704]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1712]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1720]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	add r15, rbp
	adc r8, 0
	mov rcx, r9
	shl rcx, 32
	add rcx, r9
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r9d, 0
	adc r9, 0
	sub r10, rbp
	sbb r11, rdx
	sbb r12, r9
	sbb r13, 0
	sbb r14, 0
	sbb rcx, 0
	add r15, rcx
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1568]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1696]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1704]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1712]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1720]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rcx, r10
	shl rcx, 32
	add rcx, r10
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r10d, 0
	adc r10, 0
	sub r11, rbp
	sbb r12, rdx
	sbb r13, r10
	sbb r14, 0
	sbb r15, 0
	sbb rcx, 0
	add r8, rcx
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1576]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1696]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1704]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1712]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1720]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rcx, r11
	shl rcx, 32
	add rcx, r11
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r11d, 0
	adc r11, 0
	sub r12, rbp
	sbb r13, rdx
	sbb r14, r11
	sbb r15, 0
	sbb r8, 0
	sbb rcx, 0
	add r9, rcx
	adc r10, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1584]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1696]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1704]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1712]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1720]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	add r10, rbp
	adc r11, 0
	mov rcx, r12
	shl rcx, 32
	add rcx, r12
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r12d, 0
	adc r12, 0
	sub r13, rbp
	sbb r14, rdx
	sbb r15, r12
	sbb r8, 0
	sbb r9, 0
	sbb rcx, 0
	add r10, rcx
	adc r11, 0
	mov r12d, 0
	mov rcx, QWORD PTR [rdi+1592]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1696]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1704]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1712]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1720]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1728]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1736]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	add r11, rbp
	adc r12, 0
	mov rcx, r13
	shl rcx, 32
	add rcx, r13
	movabs rax, -4294967295
	mul rcx
	mov rbp, rdx
	mov eax, -1
	mul rcx
	add rbp, rax
	adc rdx, rcx
	mov r13d, 0
	adc r13, 0
	sub r14, rbp
	sbb r15, rdx
	sbb r8, r13
	sbb r9, 0
	sbb r10, 0
	sbb rcx, 0
	add r11, rcx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+1696], r14
	mov QWORD PTR [rdi+1704], r15
	mov QWORD PTR [rdi+1712], r8
	mov QWORD PTR [rdi+1720], r9
	mov QWORD PTR [rdi+1728], r10
	mov QWORD PTR [rdi+1736], r11
	mov r12, rsi
	mov esi, 1744
	mov edx, 1696
	mov ecx, 832
	call {vg_p384_mul_mod_p}
	mov rsi, r12
	mov r8, QWORD PTR [rdi+736]
	mov r9, QWORD PTR [rdi+744]
	mov r10, QWORD PTR [rdi+752]
	mov r11, QWORD PTR [rdi+760]
	mov r12, QWORD PTR [rdi+768]
	mov r13, QWORD PTR [rdi+776]
	sub r8, QWORD PTR [rdi+1744]
	sbb r9, QWORD PTR [rdi+1752]
	sbb r10, QWORD PTR [rdi+1760]
	sbb r11, QWORD PTR [rdi+1768]
	sbb r12, QWORD PTR [rdi+1776]
	sbb r13, QWORD PTR [rdi+1784]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1984], r8
	mov QWORD PTR [rdi+1992], r9
	mov QWORD PTR [rdi+2000], r10
	mov QWORD PTR [rdi+2008], r11
	mov QWORD PTR [rdi+2016], r12
	mov QWORD PTR [rdi+2024], r13
	mov r8, QWORD PTR [rdi+1696]
	mov r9, QWORD PTR [rdi+1704]
	mov r10, QWORD PTR [rdi+1712]
	mov r11, QWORD PTR [rdi+1720]
	mov r12, QWORD PTR [rdi+1728]
	mov r13, QWORD PTR [rdi+1736]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1456]
	adc r9, QWORD PTR [rdi+1464]
	adc r10, QWORD PTR [rdi+1472]
	adc r11, QWORD PTR [rdi+1480]
	adc r12, QWORD PTR [rdi+1488]
	adc r13, QWORD PTR [rdi+1496]
	adc r14, 0
	sub r8, QWORD PTR [rdi+64]
	sbb r9, QWORD PTR [rdi+72]
	sbb r10, QWORD PTR [rdi+80]
	sbb r11, QWORD PTR [rdi+88]
	sbb r12, QWORD PTR [rdi+96]
	sbb r13, QWORD PTR [rdi+104]
	sbb r14, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1696], r8
	mov QWORD PTR [rdi+1704], r9
	mov QWORD PTR [rdi+1712], r10
	mov QWORD PTR [rdi+1720], r11
	mov QWORD PTR [rdi+1728], r12
	mov QWORD PTR [rdi+1736], r13
	mov r12, rsi
	mov esi, 1744
	mov edx, 1696
	mov ecx, 832
	call {vg_p384_mul_mod_p}
	mov rsi, r12
	mov r8, QWORD PTR [rdi+736]
	mov r9, QWORD PTR [rdi+744]
	mov r10, QWORD PTR [rdi+752]
	mov r11, QWORD PTR [rdi+760]
	mov r12, QWORD PTR [rdi+768]
	mov r13, QWORD PTR [rdi+776]
	sub r8, QWORD PTR [rdi+1744]
	sbb r9, QWORD PTR [rdi+1752]
	sbb r10, QWORD PTR [rdi+1760]
	sbb r11, QWORD PTR [rdi+1768]
	sbb r12, QWORD PTR [rdi+1776]
	sbb r13, QWORD PTR [rdi+1784]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1888], r8
	mov QWORD PTR [rdi+1896], r9
	mov QWORD PTR [rdi+1904], r10
	mov QWORD PTR [rdi+1912], r11
	mov QWORD PTR [rdi+1920], r12
	mov QWORD PTR [rdi+1928], r13
	mov rdx, QWORD PTR [rdi+1984]
	or rdx, QWORD PTR [rdi+1992]
	or rdx, QWORD PTR [rdi+2000]
	or rdx, QWORD PTR [rdi+2008]
	or rdx, QWORD PTR [rdi+2016]
	or rdx, QWORD PTR [rdi+2024]
	cmp rdx, 1
	sbb rdx, rdx
	mov rbp, rdx
	mov rdx, QWORD PTR [rdi+1552]
	sub rdx, QWORD PTR [rdi+112]
	mov rdx, QWORD PTR [rdi+1560]
	sbb rdx, QWORD PTR [rdi+120]
	mov rdx, QWORD PTR [rdi+1568]
	sbb rdx, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rdi+1576]
	sbb rdx, QWORD PTR [rdi+136]
	mov rdx, QWORD PTR [rdi+1584]
	sbb rdx, QWORD PTR [rdi+144]
	mov rdx, QWORD PTR [rdi+1592]
	sbb rdx, QWORD PTR [rdi+152]
	sbb rax, rax
	mov r12, rax
	mov rdx, QWORD PTR [rdi+1888]
	or rdx, QWORD PTR [rdi+1896]
	or rdx, QWORD PTR [rdi+1904]
	or rdx, QWORD PTR [rdi+1912]
	or rdx, QWORD PTR [rdi+1920]
	or rdx, QWORD PTR [rdi+1928]
	cmp rdx, 1
	sbb rdx, rdx
	and rdx, r12
	or rdx, rbp
	mov rax, QWORD PTR [rdi+2176]
	and rax, rdx
	mov QWORD PTR [rdi+2176], rax
	mov rdx, QWORD PTR [rdi+832]
	or rdx, QWORD PTR [rdi+840]
	or rdx, QWORD PTR [rdi+848]
	or rdx, QWORD PTR [rdi+856]
	or rdx, QWORD PTR [rdi+864]
	or rdx, QWORD PTR [rdi+872]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+2176]
	and rax, rdx
	mov QWORD PTR [rdi+2176], rax
	mov rax, QWORD PTR [rdi+2176]
	and rax, 1
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	ret
	.p2align 6

vg_ecdsa_p384_verify_adx:
	mov r8, rcx
	mov r9, rdi
	mov rcx, rdx
	mov r10, rdx
	add r10, 48
	mov rdx, rdi
	add rdx, 1
	mov QWORD PTR [r8], rbx
	mov QWORD PTR [r8+8], rbp
	mov QWORD PTR [r8+16], r12
	mov QWORD PTR [r8+24], r13
	mov QWORD PTR [r8+32], r14
	mov QWORD PTR [r8+40], r15
	mov r14, rdi
	mov rdi, r8
	mov rax, QWORD PTR [rcx+40]
	bswap rax
	mov QWORD PTR [rdi+1552], rax
	mov rax, QWORD PTR [rcx+32]
	bswap rax
	mov QWORD PTR [rdi+1560], rax
	mov rax, QWORD PTR [rcx+24]
	bswap rax
	mov QWORD PTR [rdi+1568], rax
	mov rax, QWORD PTR [rcx+16]
	bswap rax
	mov QWORD PTR [rdi+1576], rax
	mov rax, QWORD PTR [rcx+8]
	bswap rax
	mov QWORD PTR [rdi+1584], rax
	mov rax, QWORD PTR [rcx]
	bswap rax
	mov QWORD PTR [rdi+1592], rax
	mov rax, QWORD PTR [rsi+40]
	bswap rax
	mov QWORD PTR [rdi+1600], rax
	mov rax, QWORD PTR [rsi+32]
	bswap rax
	mov QWORD PTR [rdi+1608], rax
	mov rax, QWORD PTR [rsi+24]
	bswap rax
	mov QWORD PTR [rdi+1616], rax
	mov rax, QWORD PTR [rsi+16]
	bswap rax
	mov QWORD PTR [rdi+1624], rax
	mov rax, QWORD PTR [rsi+8]
	bswap rax
	mov QWORD PTR [rdi+1632], rax
	mov rax, QWORD PTR [rsi]
	bswap rax
	mov QWORD PTR [rdi+1640], rax
	mov rax, QWORD PTR [rdx+40]
	bswap rax
	mov QWORD PTR [rdi+1648], rax
	mov rax, QWORD PTR [rdx+32]
	bswap rax
	mov QWORD PTR [rdi+1656], rax
	mov rax, QWORD PTR [rdx+24]
	bswap rax
	mov QWORD PTR [rdi+1664], rax
	mov rax, QWORD PTR [rdx+16]
	bswap rax
	mov QWORD PTR [rdi+1672], rax
	mov rax, QWORD PTR [rdx+8]
	bswap rax
	mov QWORD PTR [rdi+1680], rax
	mov rax, QWORD PTR [rdx]
	bswap rax
	mov QWORD PTR [rdi+1688], rax
	movabs rax, 4294967295
	mov QWORD PTR [rdi+64], rax
	movabs rax, -4294967296
	mov QWORD PTR [rdi+72], rax
	movabs rax, -2
	mov QWORD PTR [rdi+80], rax
	movabs rax, -1
	mov QWORD PTR [rdi+88], rax
	movabs rax, -1
	mov QWORD PTR [rdi+96], rax
	movabs rax, -1
	mov QWORD PTR [rdi+104], rax
	movabs rax, -1374695839762142861
	mov QWORD PTR [rdi+112], rax
	movabs rax, 6348401684107011962
	mov QWORD PTR [rdi+120], rax
	movabs rax, -4079331616924160545
	mov QWORD PTR [rdi+128], rax
	movabs rax, -1
	mov QWORD PTR [rdi+136], rax
	movabs rax, -1
	mov QWORD PTR [rdi+144], rax
	movabs rax, -1
	mov QWORD PTR [rdi+152], rax
	movabs rax, 0
	mov QWORD PTR [rdi+208], rax
	movabs rax, 0
	mov QWORD PTR [rdi+216], rax
	movabs rax, 0
	mov QWORD PTR [rdi+224], rax
	movabs rax, 0
	mov QWORD PTR [rdi+232], rax
	movabs rax, 0
	mov QWORD PTR [rdi+240], rax
	movabs rax, 0
	mov QWORD PTR [rdi+248], rax
	movabs rax, 1
	mov QWORD PTR [rdi+256], rax
	movabs rax, 0
	mov QWORD PTR [rdi+264], rax
	movabs rax, 0
	mov QWORD PTR [rdi+272], rax
	movabs rax, 0
	mov QWORD PTR [rdi+280], rax
	movabs rax, 0
	mov QWORD PTR [rdi+288], rax
	movabs rax, 0
	mov QWORD PTR [rdi+296], rax
	movabs rax, -4294967295
	mov QWORD PTR [rdi+304], rax
	movabs rax, 4294967295
	mov QWORD PTR [rdi+312], rax
	movabs rax, 1
	mov QWORD PTR [rdi+320], rax
	movabs rax, 0
	mov QWORD PTR [rdi+328], rax
	movabs rax, 0
	mov QWORD PTR [rdi+336], rax
	movabs rax, 0
	mov QWORD PTR [rdi+344], rax
	movabs rax, 17179869180
	mov QWORD PTR [rdi+352], rax
	movabs rax, -17179869184
	mov QWORD PTR [rdi+360], rax
	movabs rax, -5
	mov QWORD PTR [rdi+368], rax
	movabs rax, -1
	mov QWORD PTR [rdi+376], rax
	movabs rax, -1
	mov QWORD PTR [rdi+384], rax
	movabs rax, -1
	mov QWORD PTR [rdi+392], rax
	movabs rax, 1744187536785508710
	mov QWORD PTR [rdi+400], rax
	movabs rax, -1910360172469643068
	mov QWORD PTR [rdi+408], rax
	movabs rax, 7482275382463301262
	mov QWORD PTR [rdi+416], rax
	movabs rax, -6222316845941481305
	mov QWORD PTR [rdi+424], rax
	movabs rax, 2486380466413134270
	mov QWORD PTR [rdi+432], rax
	movabs rax, 7428744631655809005
	mov QWORD PTR [rdi+440], rax
	movabs rax, 4454189113653900584
	mov QWORD PTR [rdi+448], rax
	movabs rax, 2369870743683386936
	mov QWORD PTR [rdi+456], rax
	movabs rax, -8674993926805172882
	mov QWORD PTR [rdi+464], rax
	movabs rax, 7229551204834152191
	mov QWORD PTR [rdi+472], rax
	movabs rax, -9137813387582972373
	mov QWORD PTR [rdi+480], rax
	movabs rax, 5564951339003155731
	mov QWORD PTR [rdi+488], rax
	movabs rax, 2523209505731486974
	mov QWORD PTR [rdi+496], rax
	movabs rax, -6791524172683761236
	mov QWORD PTR [rdi+504], rax
	movabs rax, -8381788974133039024
	mov QWORD PTR [rdi+512], rax
	movabs rax, -4124362564652695591
	mov QWORD PTR [rdi+520], rax
	movabs rax, -2485984631113275328
	mov QWORD PTR [rdi+528], rax
	movabs rax, 3132442392059561449
	mov QWORD PTR [rdi+536], rax
	movabs rax, 3256554584917936553
	mov QWORD PTR [rdi+544], rax
	movabs rax, -54744796168018919
	mov QWORD PTR [rdi+552], rax
	movabs rax, -4882385527837808313
	mov QWORD PTR [rdi+560], rax
	movabs rax, -3166794598585787195
	mov QWORD PTR [rdi+568], rax
	movabs rax, 4589268600508278933
	mov QWORD PTR [rdi+576], rax
	movabs rax, 902107514168524577
	mov QWORD PTR [rdi+584], rax
	movabs rax, 1374695839762142861
	mov QWORD PTR [rdi+592], rax
	movabs rax, -6348401684107011963
	mov QWORD PTR [rdi+600], rax
	movabs rax, 4079331616924160544
	mov QWORD PTR [rdi+608], rax
	movabs rax, 0
	mov QWORD PTR [rdi+616], rax
	movabs rax, 0
	mov QWORD PTR [rdi+624], rax
	movabs rax, 0
	mov QWORD PTR [rdi+632], rax
	movabs rax, 4294967293
	mov QWORD PTR [rdi+640], rax
	movabs rax, -4294967296
	mov QWORD PTR [rdi+648], rax
	movabs rax, -2
	mov QWORD PTR [rdi+656], rax
	movabs rax, -1
	mov QWORD PTR [rdi+664], rax
	movabs rax, -1
	mov QWORD PTR [rdi+672], rax
	movabs rax, -1
	mov QWORD PTR [rdi+680], rax
	movabs rax, -1374695839762142863
	mov QWORD PTR [rdi+688], rax
	movabs rax, 6348401684107011962
	mov QWORD PTR [rdi+696], rax
	movabs rax, -4079331616924160545
	mov QWORD PTR [rdi+704], rax
	movabs rax, -1
	mov QWORD PTR [rdi+712], rax
	movabs rax, -1
	mov QWORD PTR [rdi+720], rax
	movabs rax, -1
	mov QWORD PTR [rdi+728], rax
	movabs rax, 0
	mov QWORD PTR [rdi+736], rax
	movabs rax, 0
	mov QWORD PTR [rdi+744], rax
	movabs rax, 0
	mov QWORD PTR [rdi+752], rax
	movabs rax, 0
	mov QWORD PTR [rdi+760], rax
	movabs rax, 0
	mov QWORD PTR [rdi+768], rax
	movabs rax, 0
	mov QWORD PTR [rdi+776], rax
	movabs rax, -4294967295
	mov QWORD PTR [rdi+784], rax
	movabs rax, 4294967295
	mov QWORD PTR [rdi+792], rax
	movabs rax, 1
	mov QWORD PTR [rdi+800], rax
	movabs rax, 0
	mov QWORD PTR [rdi+808], rax
	movabs rax, 0
	mov QWORD PTR [rdi+816], rax
	movabs rax, 0
	mov QWORD PTR [rdi+824], rax
	movabs rax, 0
	mov QWORD PTR [rdi+832], rax
	movabs rax, 0
	mov QWORD PTR [rdi+840], rax
	movabs rax, 0
	mov QWORD PTR [rdi+848], rax
	movabs rax, 0
	mov QWORD PTR [rdi+856], rax
	movabs rax, 0
	mov QWORD PTR [rdi+864], rax
	movabs rax, 0
	mov QWORD PTR [rdi+872], rax
	movabs rax, -1
	mov QWORD PTR [rdi+2176], rax
	mov rsi, r14
	mov ebx, 0
20:
	movzx eax, BYTE PTR [rdi+rbx*1+1552]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2224], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2225], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2226], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2227], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2228], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2229], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2230], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2231], dl
	add rbx, 1
	cmp rbx, 48
	jne 20b
	mov ebx, 0
21:
	movzx eax, BYTE PTR [rdi+rbx*1+640]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2616], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2617], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2618], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2619], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2620], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2621], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2622], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2623], dl
	add rbx, 1
	cmp rbx, 48
	jne 21b
	mov ebx, 0
22:
	movzx eax, BYTE PTR [rdi+rbx*1+688]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3008], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3009], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3010], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3011], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3012], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3013], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3014], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3015], dl
	add rbx, 1
	cmp rbx, 48
	jne 22b
	mov rax, QWORD PTR [r10+40]
	bswap rax
	mov QWORD PTR [rdi+1504], rax
	mov rax, QWORD PTR [r10+32]
	bswap rax
	mov QWORD PTR [rdi+1512], rax
	mov rax, QWORD PTR [r10+24]
	bswap rax
	mov QWORD PTR [rdi+1520], rax
	mov rax, QWORD PTR [r10+16]
	bswap rax
	mov QWORD PTR [rdi+1528], rax
	mov rax, QWORD PTR [r10+8]
	bswap rax
	mov QWORD PTR [rdi+1536], rax
	mov rax, QWORD PTR [r10]
	bswap rax
	mov QWORD PTR [rdi+1544], rax
	movabs rax, -8589934591
	mov QWORD PTR [rdi+1936], rax
	movabs rax, 8589934592
	mov QWORD PTR [rdi+1944], rax
	movabs rax, -8589934592
	mov QWORD PTR [rdi+1952], rax
	movabs rax, 8589934592
	mov QWORD PTR [rdi+1960], rax
	movabs rax, 1
	mov QWORD PTR [rdi+1968], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1976], rax
	movabs rax, 581395848458481100
	mov QWORD PTR [rdi+1984], rax
	movabs rax, -636786727019859220
	mov QWORD PTR [rdi+1992], rax
	movabs rax, 8643006485390950958
	mov QWORD PTR [rdi+2000], rax
	movabs rax, -2074105615313827102
	mov QWORD PTR [rdi+2008], rax
	movabs rax, -5320121202432139116
	mov QWORD PTR [rdi+2016], rax
	movabs rax, -3672666480684580871
	mov QWORD PTR [rdi+2024], rax
	mov rdx, r9
	add rdx, 49
	mov rax, QWORD PTR [rdx+40]
	bswap rax
	mov QWORD PTR [rdi+1792], rax
	mov rax, QWORD PTR [rdx+32]
	bswap rax
	mov QWORD PTR [rdi+1800], rax
	mov rax, QWORD PTR [rdx+24]
	bswap rax
	mov QWORD PTR [rdi+1808], rax
	mov rax, QWORD PTR [rdx+16]
	bswap rax
	mov QWORD PTR [rdi+1816], rax
	mov rax, QWORD PTR [rdx+8]
	bswap rax
	mov QWORD PTR [rdi+1824], rax
	mov rax, QWORD PTR [rdx]
	bswap rax
	mov QWORD PTR [rdi+1832], rax
	movzx edx, BYTE PTR [r9]
	xor rdx, 4
	cmp rdx, 1
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+2176]
	and rax, rdx
	mov QWORD PTR [rdi+2176], rax
	call {vg_p384_check_point_adx}
	mov rdx, QWORD PTR [rdi+1552]
	sub rdx, QWORD PTR [rdi+112]
	mov rdx, QWORD PTR [rdi+1560]
	sbb rdx, QWORD PTR [rdi+120]
	mov rdx, QWORD PTR [rdi+1568]
	sbb rdx, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rdi+1576]
	sbb rdx, QWORD PTR [rdi+136]
	mov rdx, QWORD PTR [rdi+1584]
	sbb rdx, QWORD PTR [rdi+144]
	mov rdx, QWORD PTR [rdi+1592]
	sbb rdx, QWORD PTR [rdi+152]
	sbb rax, rax
	mov rbp, rax
	mov rdx, QWORD PTR [rdi+1552]
	or rdx, QWORD PTR [rdi+1560]
	or rdx, QWORD PTR [rdi+1568]
	or rdx, QWORD PTR [rdi+1576]
	or rdx, QWORD PTR [rdi+1584]
	or rdx, QWORD PTR [rdi+1592]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	and rdx, rbp
	mov rax, QWORD PTR [rdi+2176]
	and rax, rdx
	mov QWORD PTR [rdi+2176], rax
	mov rdx, QWORD PTR [rdi+1504]
	sub rdx, QWORD PTR [rdi+112]
	mov rdx, QWORD PTR [rdi+1512]
	sbb rdx, QWORD PTR [rdi+120]
	mov rdx, QWORD PTR [rdi+1520]
	sbb rdx, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rdi+1528]
	sbb rdx, QWORD PTR [rdi+136]
	mov rdx, QWORD PTR [rdi+1536]
	sbb rdx, QWORD PTR [rdi+144]
	mov rdx, QWORD PTR [rdi+1544]
	sbb rdx, QWORD PTR [rdi+152]
	sbb rax, rax
	mov rbp, rax
	mov rdx, QWORD PTR [rdi+1504]
	or rdx, QWORD PTR [rdi+1512]
	or rdx, QWORD PTR [rdi+1520]
	or rdx, QWORD PTR [rdi+1528]
	or rdx, QWORD PTR [rdi+1536]
	or rdx, QWORD PTR [rdi+1544]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	and rdx, rbp
	mov rax, QWORD PTR [rdi+2176]
	and rax, rdx
	mov QWORD PTR [rdi+2176], rax
	mov r12, rsi
	mov esi, 1840
	mov edx, 1504
	mov ecx, 544
	call {vg_p384_mul_mod_n_adx}
	mov rsi, r12
	call {vg_p384_inv_mod_n_adx}
	mov r12, rsi
	mov esi, 1984
	mov edx, 1600
	mov ecx, 544
	call {vg_p384_mul_mod_n_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1936
	mov edx, 1552
	mov ecx, 544
	call {vg_p384_mul_mod_n_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2032
	mov edx, 1984
	mov ecx, 1456
	call {vg_p384_mul_mod_n_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2080
	mov edx, 1936
	mov ecx, 1456
	call {vg_p384_mul_mod_n_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1696
	mov edx, 2032
	mov ecx, 256
	call {vg_p384_mul_mod_n_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1744
	mov edx, 2080
	mov ecx, 256
	call {vg_p384_mul_mod_n_adx}
	mov rsi, r12
	mov r8, QWORD PTR [rdi+1696]
	mov r9, QWORD PTR [rdi+1704]
	mov r10, QWORD PTR [rdi+1712]
	mov r11, QWORD PTR [rdi+1720]
	mov r12, QWORD PTR [rdi+1728]
	mov r13, QWORD PTR [rdi+1736]
	mov r14d, 0
	mov ebx, 0
	movabs rax, 0
	mov QWORD PTR [rdi+6400], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6408], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6416], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6424], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6432], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6440], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6448], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6456], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6464], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6472], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6480], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6488], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6496], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6504], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6512], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6520], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6528], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6536], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6544], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6552], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6560], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6568], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6576], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6584], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6592], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6600], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6608], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6616], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6624], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6632], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6640], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6648], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6656], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6664], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6672], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6680], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6688], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6696], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6704], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6712], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6720], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6728], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6736], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6744], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6752], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6760], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6768], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6776], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6784], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6792], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6800], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6808], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6816], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6824], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6832], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6840], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6848], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6856], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6864], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6872], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6880], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6888], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6896], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6904], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6912], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6920], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6928], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6936], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6944], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6952], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6960], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6968], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6976], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6984], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6992], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7000], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7008], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7016], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7024], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7032], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7040], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7048], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7056], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7064], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7072], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7080], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7088], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7096], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7104], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7112], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7120], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7128], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7136], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7144], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7152], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7160], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7168], rax
23:
	mov rcx, r8
	and rcx, 1
	test rcx, rcx
	je 24f
	mov rcx, r8
	and rcx, 511
	cmp rcx, 256
	jb 26f
	sub rcx, 512
	jmp 27f
26:
27:
	mov rax, rcx
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	sub r8, rcx
	sbb r9, rdx
	sbb r10, rdx
	sbb r11, rdx
	sbb r12, rdx
	sbb r13, rdx
	sbb r14, rdx
	mov WORD PTR [rdi+rbx*2+6400], cx
	shr r8, 9
	mov rax, r9
	shl rax, 55
	or r8, rax
	shr r9, 9
	mov rax, r10
	shl rax, 55
	or r9, rax
	shr r10, 9
	mov rax, r11
	shl rax, 55
	or r10, rax
	shr r11, 9
	mov rax, r12
	shl rax, 55
	or r11, rax
	shr r12, 9
	mov rax, r13
	shl rax, 55
	or r12, rax
	shr r13, 9
	mov rax, r14
	shl rax, 55
	or r13, rax
	shr r14, 9
	add rbx, 9
	jmp 25f
24:
	shr r8, 1
	mov rax, r9
	shl rax, 63
	or r8, rax
	shr r9, 1
	mov rax, r10
	shl rax, 63
	or r9, rax
	shr r10, 1
	mov rax, r11
	shl rax, 63
	or r10, rax
	shr r11, 1
	mov rax, r12
	shl rax, 63
	or r11, rax
	shr r12, 1
	mov rax, r13
	shl rax, 63
	or r12, rax
	shr r13, 1
	mov rax, r14
	shl rax, 63
	or r13, rax
	shr r14, 1
	add rbx, 1
25:
	cmp rbx, 385
	jb 23b
	mov r8, QWORD PTR [rdi+1744]
	mov r9, QWORD PTR [rdi+1752]
	mov r10, QWORD PTR [rdi+1760]
	mov r11, QWORD PTR [rdi+1768]
	mov r12, QWORD PTR [rdi+1776]
	mov r13, QWORD PTR [rdi+1784]
	mov r14d, 0
	mov ebx, 0
	movabs rax, 0
	mov QWORD PTR [rdi+3568], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3576], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3584], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3592], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3600], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3608], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3616], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3624], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3632], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3640], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3648], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3656], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3664], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3672], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3680], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3688], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3696], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3704], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3712], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3720], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3728], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3736], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3744], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3752], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3760], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3768], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3776], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3784], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3792], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3800], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3808], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3816], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3824], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3832], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3840], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3848], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3856], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3864], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3872], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3880], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3888], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3896], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3904], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3912], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3920], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3928], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3936], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3944], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3952], rax
28:
	mov rcx, r8
	and rcx, 1
	test rcx, rcx
	je 29f
	mov rcx, r8
	and rcx, 31
	cmp rcx, 16
	jb 211f
	sub rcx, 32
	jmp 212f
211:
212:
	mov rax, rcx
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	sub r8, rcx
	sbb r9, rdx
	sbb r10, rdx
	sbb r11, rdx
	sbb r12, rdx
	sbb r13, rdx
	sbb r14, rdx
	mov BYTE PTR [rdi+rbx*1+3568], cl
	shr r8, 5
	mov rax, r9
	shl rax, 59
	or r8, rax
	shr r9, 5
	mov rax, r10
	shl rax, 59
	or r9, rax
	shr r10, 5
	mov rax, r11
	shl rax, 59
	or r10, rax
	shr r11, 5
	mov rax, r12
	shl rax, 59
	or r11, rax
	shr r12, 5
	mov rax, r13
	shl rax, 59
	or r12, rax
	shr r13, 5
	mov rax, r14
	shl rax, 59
	or r13, rax
	shr r14, 5
	add rbx, 5
	jmp 210f
29:
	shr r8, 1
	mov rax, r9
	shl rax, 63
	or r8, rax
	shr r9, 1
	mov rax, r10
	shl rax, 63
	or r9, rax
	shr r10, 1
	mov rax, r11
	shl rax, 63
	or r10, rax
	shr r11, 1
	mov rax, r12
	shl rax, 63
	or r11, rax
	shr r12, 1
	mov rax, r13
	shl rax, 63
	or r12, rax
	shr r13, 1
	mov rax, r14
	shl rax, 63
	or r13, rax
	shr r14, 1
	add rbx, 1
210:
	cmp rbx, 385
	jb 28b
	mov rax, QWORD PTR [rdi+1888]
	mov QWORD PTR [rdi+4096], rax
	mov rax, QWORD PTR [rdi+1896]
	mov QWORD PTR [rdi+4104], rax
	mov rax, QWORD PTR [rdi+1904]
	mov QWORD PTR [rdi+4112], rax
	mov rax, QWORD PTR [rdi+1912]
	mov QWORD PTR [rdi+4120], rax
	mov rax, QWORD PTR [rdi+1920]
	mov QWORD PTR [rdi+4128], rax
	mov rax, QWORD PTR [rdi+1928]
	mov QWORD PTR [rdi+4136], rax
	mov rax, QWORD PTR [rdi+2128]
	mov QWORD PTR [rdi+4144], rax
	mov rax, QWORD PTR [rdi+2136]
	mov QWORD PTR [rdi+4152], rax
	mov rax, QWORD PTR [rdi+2144]
	mov QWORD PTR [rdi+4160], rax
	mov rax, QWORD PTR [rdi+2152]
	mov QWORD PTR [rdi+4168], rax
	mov rax, QWORD PTR [rdi+2160]
	mov QWORD PTR [rdi+4176], rax
	mov rax, QWORD PTR [rdi+2168]
	mov QWORD PTR [rdi+4184], rax
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+4192], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+4200], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+4208], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+4216], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+4224], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+4232], rax
	mov ebx, 1
	mov rdx, QWORD PTR [rdi+1888]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1896]
	mulx r10, rax, QWORD PTR [rdi+1904]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1912]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1920]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1928]
	adcx r12, rax
	adcx r13, rbp
	mov QWORD PTR [rdi+4056], r8
	mov QWORD PTR [rdi+4064], r9
	mov rdx, QWORD PTR [rdi+1896]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1904]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1912]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1920]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+1928]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+1904]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1912]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1920]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+1928]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, QWORD PTR [rdi+1912]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1920]
	adox r14, rax
	adcx r15, rcx
	mulx r8, rax, QWORD PTR [rdi+1928]
	adox r15, rax
	adcx r8, rbp
	adox r8, rbp
	mov rdx, QWORD PTR [rdi+1920]
	xor ebp, ebp
	mulx r9, rax, QWORD PTR [rdi+1928]
	adox r8, rax
	adcx r9, rbp
	adox r9, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+1888]
	mulx rcx, rax, rdx
	adcx rbp, rbp
	adox rbp, rax
	mov QWORD PTR [rdi+4048], rbp
	mov rdx, QWORD PTR [rdi+4056]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+1896]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+4064]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	adcx r10, r10
	adox r10, rcx
	mov rdx, QWORD PTR [rdi+1904]
	mulx rcx, rax, rdx
	adcx r11, r11
	adox r11, rax
	adcx r12, r12
	adox r12, rcx
	mov rdx, QWORD PTR [rdi+1912]
	mulx rcx, rax, rdx
	adcx r13, r13
	adox r13, rax
	adcx r14, r14
	adox r14, rcx
	mov rdx, QWORD PTR [rdi+1920]
	mulx rcx, rax, rdx
	adcx r15, r15
	adox r15, rax
	adcx r8, r8
	adox r8, rcx
	mov rdx, QWORD PTR [rdi+1928]
	mulx rcx, rax, rdx
	adcx r9, r9
	adox r9, rax
	mov edx, 0
	adcx rcx, rdx
	adox rcx, rdx
	mov QWORD PTR [rdi+1168], r13
	mov QWORD PTR [rdi+1176], r14
	mov QWORD PTR [rdi+1184], r15
	mov QWORD PTR [rdi+1192], r8
	mov QWORD PTR [rdi+1200], r9
	mov QWORD PTR [rdi+1208], rcx
	mov r13, QWORD PTR [rdi+4048]
	mov r14, QWORD PTR [rdi+4056]
	mov r15, QWORD PTR [rdi+4064]
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r10, rbp
	sbb r11, 0
	sbb r12, 0
	mov r13, rdx
	sbb r13, 0
	movabs rdx, 4294967297
	imul rdx, r14
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r14, rcx
	add rax, r14
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r15, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	mov r14, rdx
	sbb r14, 0
	movabs rdx, 4294967297
	imul rdx, r15
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r15, rcx
	add rax, r15
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	mov r15, rdx
	sbb r15, 0
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	mov r10, rdx
	sbb r10, 0
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r10, 0
	mov r11, rdx
	sbb r11, 0
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r10, 0
	sbb r11, 0
	mov r12, rdx
	sbb r12, 0
	mov r8d, 0
	add r13, QWORD PTR [rdi+1168]
	adc r14, QWORD PTR [rdi+1176]
	adc r15, QWORD PTR [rdi+1184]
	adc r10, QWORD PTR [rdi+1192]
	adc r11, QWORD PTR [rdi+1200]
	adc r12, QWORD PTR [rdi+1208]
	adc r8, 0
	sub r13, QWORD PTR [rdi+64]
	sbb r14, QWORD PTR [rdi+72]
	sbb r15, QWORD PTR [rdi+80]
	sbb r10, QWORD PTR [rdi+88]
	sbb r11, QWORD PTR [rdi+96]
	sbb r12, QWORD PTR [rdi+104]
	sbb r8, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r13, rcx
	adc r14, rdx
	adc r15, rbp
	adc r10, rax
	adc r11, rax
	adc r12, rax
	mov QWORD PTR [rdi+1168], r13
	mov QWORD PTR [rdi+1176], r14
	mov QWORD PTR [rdi+1184], r15
	mov QWORD PTR [rdi+1192], r10
	mov QWORD PTR [rdi+1200], r11
	mov QWORD PTR [rdi+1208], r12
	mov rdx, QWORD PTR [rdi+2128]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+2136]
	mulx r10, rax, QWORD PTR [rdi+2144]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+2152]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+2160]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+2168]
	adcx r12, rax
	adcx r13, rbp
	mov QWORD PTR [rdi+4056], r8
	mov QWORD PTR [rdi+4064], r9
	mov rdx, QWORD PTR [rdi+2136]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+2144]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+2152]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+2160]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+2168]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+2144]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+2152]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+2160]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+2168]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, QWORD PTR [rdi+2152]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+2160]
	adox r14, rax
	adcx r15, rcx
	mulx r8, rax, QWORD PTR [rdi+2168]
	adox r15, rax
	adcx r8, rbp
	adox r8, rbp
	mov rdx, QWORD PTR [rdi+2160]
	xor ebp, ebp
	mulx r9, rax, QWORD PTR [rdi+2168]
	adox r8, rax
	adcx r9, rbp
	adox r9, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+2128]
	mulx rcx, rax, rdx
	adcx rbp, rbp
	adox rbp, rax
	mov QWORD PTR [rdi+4048], rbp
	mov rdx, QWORD PTR [rdi+4056]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+2136]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+4064]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	adcx r10, r10
	adox r10, rcx
	mov rdx, QWORD PTR [rdi+2144]
	mulx rcx, rax, rdx
	adcx r11, r11
	adox r11, rax
	adcx r12, r12
	adox r12, rcx
	mov rdx, QWORD PTR [rdi+2152]
	mulx rcx, rax, rdx
	adcx r13, r13
	adox r13, rax
	adcx r14, r14
	adox r14, rcx
	mov rdx, QWORD PTR [rdi+2160]
	mulx rcx, rax, rdx
	adcx r15, r15
	adox r15, rax
	adcx r8, r8
	adox r8, rcx
	mov rdx, QWORD PTR [rdi+2168]
	mulx rcx, rax, rdx
	adcx r9, r9
	adox r9, rax
	mov edx, 0
	adcx rcx, rdx
	adox rcx, rdx
	mov QWORD PTR [rdi+1216], r13
	mov QWORD PTR [rdi+1224], r14
	mov QWORD PTR [rdi+1232], r15
	mov QWORD PTR [rdi+1240], r8
	mov QWORD PTR [rdi+1248], r9
	mov QWORD PTR [rdi+1256], rcx
	mov r13, QWORD PTR [rdi+4048]
	mov r14, QWORD PTR [rdi+4056]
	mov r15, QWORD PTR [rdi+4064]
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r10, rbp
	sbb r11, 0
	sbb r12, 0
	mov r13, rdx
	sbb r13, 0
	movabs rdx, 4294967297
	imul rdx, r14
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r14, rcx
	add rax, r14
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r15, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	mov r14, rdx
	sbb r14, 0
	movabs rdx, 4294967297
	imul rdx, r15
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r15, rcx
	add rax, r15
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	mov r15, rdx
	sbb r15, 0
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	mov r10, rdx
	sbb r10, 0
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r10, 0
	mov r11, rdx
	sbb r11, 0
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r10, 0
	sbb r11, 0
	mov r12, rdx
	sbb r12, 0
	mov r8d, 0
	add r13, QWORD PTR [rdi+1216]
	adc r14, QWORD PTR [rdi+1224]
	adc r15, QWORD PTR [rdi+1232]
	adc r10, QWORD PTR [rdi+1240]
	adc r11, QWORD PTR [rdi+1248]
	adc r12, QWORD PTR [rdi+1256]
	adc r8, 0
	sub r13, QWORD PTR [rdi+64]
	sbb r14, QWORD PTR [rdi+72]
	sbb r15, QWORD PTR [rdi+80]
	sbb r10, QWORD PTR [rdi+88]
	sbb r11, QWORD PTR [rdi+96]
	sbb r12, QWORD PTR [rdi+104]
	sbb r8, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r13, rcx
	adc r14, rdx
	adc r15, rbp
	adc r10, rax
	adc r11, rax
	adc r12, rax
	mov QWORD PTR [rdi+1216], r13
	mov QWORD PTR [rdi+1224], r14
	mov QWORD PTR [rdi+1232], r15
	mov QWORD PTR [rdi+1240], r10
	mov QWORD PTR [rdi+1248], r11
	mov QWORD PTR [rdi+1256], r12
	mov rdx, QWORD PTR [rdi+1216]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1224]
	mulx r10, rax, QWORD PTR [rdi+1232]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1240]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1248]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1256]
	adcx r12, rax
	adcx r13, rbp
	mov QWORD PTR [rdi+4056], r8
	mov QWORD PTR [rdi+4064], r9
	mov rdx, QWORD PTR [rdi+1224]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1232]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+1256]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+1232]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+1256]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, QWORD PTR [rdi+1240]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r14, rax
	adcx r15, rcx
	mulx r8, rax, QWORD PTR [rdi+1256]
	adox r15, rax
	adcx r8, rbp
	adox r8, rbp
	mov rdx, QWORD PTR [rdi+1248]
	xor ebp, ebp
	mulx r9, rax, QWORD PTR [rdi+1256]
	adox r8, rax
	adcx r9, rbp
	adox r9, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+1216]
	mulx rcx, rax, rdx
	adcx rbp, rbp
	adox rbp, rax
	mov QWORD PTR [rdi+4048], rbp
	mov rdx, QWORD PTR [rdi+4056]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+1224]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+4064]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	adcx r10, r10
	adox r10, rcx
	mov rdx, QWORD PTR [rdi+1232]
	mulx rcx, rax, rdx
	adcx r11, r11
	adox r11, rax
	adcx r12, r12
	adox r12, rcx
	mov rdx, QWORD PTR [rdi+1240]
	mulx rcx, rax, rdx
	adcx r13, r13
	adox r13, rax
	adcx r14, r14
	adox r14, rcx
	mov rdx, QWORD PTR [rdi+1248]
	mulx rcx, rax, rdx
	adcx r15, r15
	adox r15, rax
	adcx r8, r8
	adox r8, rcx
	mov rdx, QWORD PTR [rdi+1256]
	mulx rcx, rax, rdx
	adcx r9, r9
	adox r9, rax
	mov edx, 0
	adcx rcx, rdx
	adox rcx, rdx
	mov QWORD PTR [rdi+784], r13
	mov QWORD PTR [rdi+792], r14
	mov QWORD PTR [rdi+800], r15
	mov QWORD PTR [rdi+808], r8
	mov QWORD PTR [rdi+816], r9
	mov QWORD PTR [rdi+824], rcx
	mov r13, QWORD PTR [rdi+4048]
	mov r14, QWORD PTR [rdi+4056]
	mov r15, QWORD PTR [rdi+4064]
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r10, rbp
	sbb r11, 0
	sbb r12, 0
	mov r13, rdx
	sbb r13, 0
	movabs rdx, 4294967297
	imul rdx, r14
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r14, rcx
	add rax, r14
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r15, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	mov r14, rdx
	sbb r14, 0
	movabs rdx, 4294967297
	imul rdx, r15
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r15, rcx
	add rax, r15
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	mov r15, rdx
	sbb r15, 0
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	mov r10, rdx
	sbb r10, 0
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r10, 0
	mov r11, rdx
	sbb r11, 0
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r10, 0
	sbb r11, 0
	mov r12, rdx
	sbb r12, 0
	mov r8d, 0
	add r13, QWORD PTR [rdi+784]
	adc r14, QWORD PTR [rdi+792]
	adc r15, QWORD PTR [rdi+800]
	adc r10, QWORD PTR [rdi+808]
	adc r11, QWORD PTR [rdi+816]
	adc r12, QWORD PTR [rdi+824]
	adc r8, 0
	sub r13, QWORD PTR [rdi+64]
	sbb r14, QWORD PTR [rdi+72]
	sbb r15, QWORD PTR [rdi+80]
	sbb r10, QWORD PTR [rdi+88]
	sbb r11, QWORD PTR [rdi+96]
	sbb r12, QWORD PTR [rdi+104]
	sbb r8, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r13, rcx
	adc r14, rdx
	adc r15, rbp
	adc r10, rax
	adc r11, rax
	adc r12, rax
	mov QWORD PTR [rdi+784], r13
	mov QWORD PTR [rdi+792], r14
	mov QWORD PTR [rdi+800], r15
	mov QWORD PTR [rdi+808], r10
	mov QWORD PTR [rdi+816], r11
	mov QWORD PTR [rdi+824], r12
	mov rdx, QWORD PTR [rdi+1888]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1216]
	mulx r10, rax, QWORD PTR [rdi+1224]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1232]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1240]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1248]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+1256]
	adcx r13, rax
	adcx r14, rbp
	mov r15d, 0
	movabs rdx, 4294967297
	imul rdx, r8
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r8, rcx
	add rax, r8
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r9, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	sbb rdx, 0
	add r14, rdx
	adc r15, 0
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+1896]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1216]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1224]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1232]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1256]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	adcx r8, rbp
	adox r8, rbp
	movabs rdx, 4294967297
	imul rdx, r9
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r9, rcx
	add rax, r9
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	sbb rdx, 0
	add r15, rdx
	adc r8, 0
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+1904]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1216]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1224]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1232]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1256]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	sbb rdx, 0
	add r8, rdx
	adc r9, 0
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+1912]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1216]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1224]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1232]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1256]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r8, 0
	sbb rdx, 0
	add r9, rdx
	adc r10, 0
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+1920]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1216]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1224]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1232]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1256]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	adcx r11, rbp
	adox r11, rbp
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r8, 0
	sbb r9, 0
	sbb rdx, 0
	add r10, rdx
	adc r11, 0
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+1928]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1216]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1224]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1232]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1256]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	adcx r12, rbp
	adox r12, rbp
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r8, rbp
	sbb r9, 0
	sbb r10, 0
	sbb rdx, 0
	add r11, rdx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+736], r14
	mov QWORD PTR [rdi+744], r15
	mov QWORD PTR [rdi+752], r8
	mov QWORD PTR [rdi+760], r9
	mov QWORD PTR [rdi+768], r10
	mov QWORD PTR [rdi+776], r11
	mov r8, QWORD PTR [rdi+736]
	mov r9, QWORD PTR [rdi+744]
	mov r10, QWORD PTR [rdi+752]
	mov r11, QWORD PTR [rdi+760]
	mov r12, QWORD PTR [rdi+768]
	mov r13, QWORD PTR [rdi+776]
	mov r14d, 0
	add r8, QWORD PTR [rdi+736]
	adc r9, QWORD PTR [rdi+744]
	adc r10, QWORD PTR [rdi+752]
	adc r11, QWORD PTR [rdi+760]
	adc r12, QWORD PTR [rdi+768]
	adc r13, QWORD PTR [rdi+776]
	adc r14, 0
	sub r8, QWORD PTR [rdi+64]
	sbb r9, QWORD PTR [rdi+72]
	sbb r10, QWORD PTR [rdi+80]
	sbb r11, QWORD PTR [rdi+88]
	sbb r12, QWORD PTR [rdi+96]
	sbb r13, QWORD PTR [rdi+104]
	sbb r14, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+736], r8
	mov QWORD PTR [rdi+744], r9
	mov QWORD PTR [rdi+752], r10
	mov QWORD PTR [rdi+760], r11
	mov QWORD PTR [rdi+768], r12
	mov QWORD PTR [rdi+776], r13
	mov r8, QWORD PTR [rdi+736]
	mov r9, QWORD PTR [rdi+744]
	mov r10, QWORD PTR [rdi+752]
	mov r11, QWORD PTR [rdi+760]
	mov r12, QWORD PTR [rdi+768]
	mov r13, QWORD PTR [rdi+776]
	mov r14d, 0
	add r8, QWORD PTR [rdi+736]
	adc r9, QWORD PTR [rdi+744]
	adc r10, QWORD PTR [rdi+752]
	adc r11, QWORD PTR [rdi+760]
	adc r12, QWORD PTR [rdi+768]
	adc r13, QWORD PTR [rdi+776]
	adc r14, 0
	sub r8, QWORD PTR [rdi+64]
	sbb r9, QWORD PTR [rdi+72]
	sbb r10, QWORD PTR [rdi+80]
	sbb r11, QWORD PTR [rdi+88]
	sbb r12, QWORD PTR [rdi+96]
	sbb r13, QWORD PTR [rdi+104]
	sbb r14, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+736], r8
	mov QWORD PTR [rdi+744], r9
	mov QWORD PTR [rdi+752], r10
	mov QWORD PTR [rdi+760], r11
	mov QWORD PTR [rdi+768], r12
	mov QWORD PTR [rdi+776], r13
	mov r8, QWORD PTR [rdi+1168]
	mov r9, QWORD PTR [rdi+1176]
	mov r10, QWORD PTR [rdi+1184]
	mov r11, QWORD PTR [rdi+1192]
	mov r12, QWORD PTR [rdi+1200]
	mov r13, QWORD PTR [rdi+1208]
	sub r8, QWORD PTR [rdi+304]
	sbb r9, QWORD PTR [rdi+312]
	sbb r10, QWORD PTR [rdi+320]
	sbb r11, QWORD PTR [rdi+328]
	sbb r12, QWORD PTR [rdi+336]
	sbb r13, QWORD PTR [rdi+344]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1264], r8
	mov QWORD PTR [rdi+1272], r9
	mov QWORD PTR [rdi+1280], r10
	mov QWORD PTR [rdi+1288], r11
	mov QWORD PTR [rdi+1296], r12
	mov QWORD PTR [rdi+1304], r13
	mov r8, QWORD PTR [rdi+1264]
	mov r9, QWORD PTR [rdi+1272]
	mov r10, QWORD PTR [rdi+1280]
	mov r11, QWORD PTR [rdi+1288]
	mov r12, QWORD PTR [rdi+1296]
	mov r13, QWORD PTR [rdi+1304]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1264]
	adc r9, QWORD PTR [rdi+1272]
	adc r10, QWORD PTR [rdi+1280]
	adc r11, QWORD PTR [rdi+1288]
	adc r12, QWORD PTR [rdi+1296]
	adc r13, QWORD PTR [rdi+1304]
	adc r14, 0
	sub r8, QWORD PTR [rdi+64]
	sbb r9, QWORD PTR [rdi+72]
	sbb r10, QWORD PTR [rdi+80]
	sbb r11, QWORD PTR [rdi+88]
	sbb r12, QWORD PTR [rdi+96]
	sbb r13, QWORD PTR [rdi+104]
	sbb r14, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1312], r8
	mov QWORD PTR [rdi+1320], r9
	mov QWORD PTR [rdi+1328], r10
	mov QWORD PTR [rdi+1336], r11
	mov QWORD PTR [rdi+1344], r12
	mov QWORD PTR [rdi+1352], r13
	mov r8, QWORD PTR [rdi+1312]
	mov r9, QWORD PTR [rdi+1320]
	mov r10, QWORD PTR [rdi+1328]
	mov r11, QWORD PTR [rdi+1336]
	mov r12, QWORD PTR [rdi+1344]
	mov r13, QWORD PTR [rdi+1352]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1264]
	adc r9, QWORD PTR [rdi+1272]
	adc r10, QWORD PTR [rdi+1280]
	adc r11, QWORD PTR [rdi+1288]
	adc r12, QWORD PTR [rdi+1296]
	adc r13, QWORD PTR [rdi+1304]
	adc r14, 0
	sub r8, QWORD PTR [rdi+64]
	sbb r9, QWORD PTR [rdi+72]
	sbb r10, QWORD PTR [rdi+80]
	sbb r11, QWORD PTR [rdi+88]
	sbb r12, QWORD PTR [rdi+96]
	sbb r13, QWORD PTR [rdi+104]
	sbb r14, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1264], r8
	mov QWORD PTR [rdi+1272], r9
	mov QWORD PTR [rdi+1280], r10
	mov QWORD PTR [rdi+1288], r11
	mov QWORD PTR [rdi+1296], r12
	mov QWORD PTR [rdi+1304], r13
	mov rdx, QWORD PTR [rdi+1264]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1272]
	mulx r10, rax, QWORD PTR [rdi+1280]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1288]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1296]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1304]
	adcx r12, rax
	adcx r13, rbp
	mov QWORD PTR [rdi+4056], r8
	mov QWORD PTR [rdi+4064], r9
	mov rdx, QWORD PTR [rdi+1272]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1280]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1288]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+1304]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+1280]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1288]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+1304]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, QWORD PTR [rdi+1288]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r14, rax
	adcx r15, rcx
	mulx r8, rax, QWORD PTR [rdi+1304]
	adox r15, rax
	adcx r8, rbp
	adox r8, rbp
	mov rdx, QWORD PTR [rdi+1296]
	xor ebp, ebp
	mulx r9, rax, QWORD PTR [rdi+1304]
	adox r8, rax
	adcx r9, rbp
	adox r9, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+1264]
	mulx rcx, rax, rdx
	adcx rbp, rbp
	adox rbp, rax
	mov QWORD PTR [rdi+4048], rbp
	mov rdx, QWORD PTR [rdi+4056]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+1272]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+4064]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	adcx r10, r10
	adox r10, rcx
	mov rdx, QWORD PTR [rdi+1280]
	mulx rcx, rax, rdx
	adcx r11, r11
	adox r11, rax
	adcx r12, r12
	adox r12, rcx
	mov rdx, QWORD PTR [rdi+1288]
	mulx rcx, rax, rdx
	adcx r13, r13
	adox r13, rax
	adcx r14, r14
	adox r14, rcx
	mov rdx, QWORD PTR [rdi+1296]
	mulx rcx, rax, rdx
	adcx r15, r15
	adox r15, rax
	adcx r8, r8
	adox r8, rcx
	mov rdx, QWORD PTR [rdi+1304]
	mulx rcx, rax, rdx
	adcx r9, r9
	adox r9, rax
	mov edx, 0
	adcx rcx, rdx
	adox rcx, rdx
	mov QWORD PTR [rdi+1024], r13
	mov QWORD PTR [rdi+1032], r14
	mov QWORD PTR [rdi+1040], r15
	mov QWORD PTR [rdi+1048], r8
	mov QWORD PTR [rdi+1056], r9
	mov QWORD PTR [rdi+1064], rcx
	mov r13, QWORD PTR [rdi+4048]
	mov r14, QWORD PTR [rdi+4056]
	mov r15, QWORD PTR [rdi+4064]
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r10, rbp
	sbb r11, 0
	sbb r12, 0
	mov r13, rdx
	sbb r13, 0
	movabs rdx, 4294967297
	imul rdx, r14
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r14, rcx
	add rax, r14
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r15, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	mov r14, rdx
	sbb r14, 0
	movabs rdx, 4294967297
	imul rdx, r15
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r15, rcx
	add rax, r15
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	mov r15, rdx
	sbb r15, 0
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	mov r10, rdx
	sbb r10, 0
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r10, 0
	mov r11, rdx
	sbb r11, 0
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r10, 0
	sbb r11, 0
	mov r12, rdx
	sbb r12, 0
	mov r8d, 0
	add r13, QWORD PTR [rdi+1024]
	adc r14, QWORD PTR [rdi+1032]
	adc r15, QWORD PTR [rdi+1040]
	adc r10, QWORD PTR [rdi+1048]
	adc r11, QWORD PTR [rdi+1056]
	adc r12, QWORD PTR [rdi+1064]
	adc r8, 0
	sub r13, QWORD PTR [rdi+64]
	sbb r14, QWORD PTR [rdi+72]
	sbb r15, QWORD PTR [rdi+80]
	sbb r10, QWORD PTR [rdi+88]
	sbb r11, QWORD PTR [rdi+96]
	sbb r12, QWORD PTR [rdi+104]
	sbb r8, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r13, rcx
	adc r14, rdx
	adc r15, rbp
	adc r10, rax
	adc r11, rax
	adc r12, rax
	mov QWORD PTR [rdi+1024], r13
	mov QWORD PTR [rdi+1032], r14
	mov QWORD PTR [rdi+1040], r15
	mov QWORD PTR [rdi+1048], r10
	mov QWORD PTR [rdi+1056], r11
	mov QWORD PTR [rdi+1064], r12
	mov r8, QWORD PTR [rdi+1024]
	mov r9, QWORD PTR [rdi+1032]
	mov r10, QWORD PTR [rdi+1040]
	mov r11, QWORD PTR [rdi+1048]
	mov r12, QWORD PTR [rdi+1056]
	mov r13, QWORD PTR [rdi+1064]
	sub r8, QWORD PTR [rdi+736]
	sbb r9, QWORD PTR [rdi+744]
	sbb r10, QWORD PTR [rdi+752]
	sbb r11, QWORD PTR [rdi+760]
	sbb r12, QWORD PTR [rdi+768]
	sbb r13, QWORD PTR [rdi+776]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1024], r8
	mov QWORD PTR [rdi+1032], r9
	mov QWORD PTR [rdi+1040], r10
	mov QWORD PTR [rdi+1048], r11
	mov QWORD PTR [rdi+1056], r12
	mov QWORD PTR [rdi+1064], r13
	mov r8, QWORD PTR [rdi+1024]
	mov r9, QWORD PTR [rdi+1032]
	mov r10, QWORD PTR [rdi+1040]
	mov r11, QWORD PTR [rdi+1048]
	mov r12, QWORD PTR [rdi+1056]
	mov r13, QWORD PTR [rdi+1064]
	sub r8, QWORD PTR [rdi+736]
	sbb r9, QWORD PTR [rdi+744]
	sbb r10, QWORD PTR [rdi+752]
	sbb r11, QWORD PTR [rdi+760]
	sbb r12, QWORD PTR [rdi+768]
	sbb r13, QWORD PTR [rdi+776]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1024], r8
	mov QWORD PTR [rdi+1032], r9
	mov QWORD PTR [rdi+1040], r10
	mov QWORD PTR [rdi+1048], r11
	mov QWORD PTR [rdi+1056], r12
	mov QWORD PTR [rdi+1064], r13
	mov r8, QWORD PTR [rdi+736]
	mov r9, QWORD PTR [rdi+744]
	mov r10, QWORD PTR [rdi+752]
	mov r11, QWORD PTR [rdi+760]
	mov r12, QWORD PTR [rdi+768]
	mov r13, QWORD PTR [rdi+776]
	sub r8, QWORD PTR [rdi+1024]
	sbb r9, QWORD PTR [rdi+1032]
	sbb r10, QWORD PTR [rdi+1040]
	sbb r11, QWORD PTR [rdi+1048]
	sbb r12, QWORD PTR [rdi+1056]
	sbb r13, QWORD PTR [rdi+1064]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1312], r8
	mov QWORD PTR [rdi+1320], r9
	mov QWORD PTR [rdi+1328], r10
	mov QWORD PTR [rdi+1336], r11
	mov QWORD PTR [rdi+1344], r12
	mov QWORD PTR [rdi+1352], r13
	mov rdx, QWORD PTR [rdi+1264]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1312]
	mulx r10, rax, QWORD PTR [rdi+1320]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1328]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1336]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1344]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+1352]
	adcx r13, rax
	adcx r14, rbp
	mov r15d, 0
	movabs rdx, 4294967297
	imul rdx, r8
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r8, rcx
	add rax, r8
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r9, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	sbb rdx, 0
	add r14, rdx
	adc r15, 0
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+1272]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	adcx r8, rbp
	adox r8, rbp
	movabs rdx, 4294967297
	imul rdx, r9
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r9, rcx
	add rax, r9
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	sbb rdx, 0
	add r15, rdx
	adc r8, 0
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+1280]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	sbb rdx, 0
	add r8, rdx
	adc r9, 0
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+1288]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r8, 0
	sbb rdx, 0
	add r9, rdx
	adc r10, 0
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+1296]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	adcx r11, rbp
	adox r11, rbp
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r8, 0
	sbb r9, 0
	sbb rdx, 0
	add r10, rdx
	adc r11, 0
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+1304]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	adcx r12, rbp
	adox r12, rbp
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r8, rbp
	sbb r9, 0
	sbb r10, 0
	sbb rdx, 0
	add r11, rdx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+1072], r14
	mov QWORD PTR [rdi+1080], r15
	mov QWORD PTR [rdi+1088], r8
	mov QWORD PTR [rdi+1096], r9
	mov QWORD PTR [rdi+1104], r10
	mov QWORD PTR [rdi+1112], r11
	mov r8, QWORD PTR [rdi+784]
	mov r9, QWORD PTR [rdi+792]
	mov r10, QWORD PTR [rdi+800]
	mov r11, QWORD PTR [rdi+808]
	mov r12, QWORD PTR [rdi+816]
	mov r13, QWORD PTR [rdi+824]
	mov r14d, 0
	add r8, QWORD PTR [rdi+784]
	adc r9, QWORD PTR [rdi+792]
	adc r10, QWORD PTR [rdi+800]
	adc r11, QWORD PTR [rdi+808]
	adc r12, QWORD PTR [rdi+816]
	adc r13, QWORD PTR [rdi+824]
	adc r14, 0
	sub r8, QWORD PTR [rdi+64]
	sbb r9, QWORD PTR [rdi+72]
	sbb r10, QWORD PTR [rdi+80]
	sbb r11, QWORD PTR [rdi+88]
	sbb r12, QWORD PTR [rdi+96]
	sbb r13, QWORD PTR [rdi+104]
	sbb r14, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+784], r8
	mov QWORD PTR [rdi+792], r9
	mov QWORD PTR [rdi+800], r10
	mov QWORD PTR [rdi+808], r11
	mov QWORD PTR [rdi+816], r12
	mov QWORD PTR [rdi+824], r13
	mov r8, QWORD PTR [rdi+784]
	mov r9, QWORD PTR [rdi+792]
	mov r10, QWORD PTR [rdi+800]
	mov r11, QWORD PTR [rdi+808]
	mov r12, QWORD PTR [rdi+816]
	mov r13, QWORD PTR [rdi+824]
	mov r14d, 0
	add r8, QWORD PTR [rdi+784]
	adc r9, QWORD PTR [rdi+792]
	adc r10, QWORD PTR [rdi+800]
	adc r11, QWORD PTR [rdi+808]
	adc r12, QWORD PTR [rdi+816]
	adc r13, QWORD PTR [rdi+824]
	adc r14, 0
	sub r8, QWORD PTR [rdi+64]
	sbb r9, QWORD PTR [rdi+72]
	sbb r10, QWORD PTR [rdi+80]
	sbb r11, QWORD PTR [rdi+88]
	sbb r12, QWORD PTR [rdi+96]
	sbb r13, QWORD PTR [rdi+104]
	sbb r14, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+784], r8
	mov QWORD PTR [rdi+792], r9
	mov QWORD PTR [rdi+800], r10
	mov QWORD PTR [rdi+808], r11
	mov QWORD PTR [rdi+816], r12
	mov QWORD PTR [rdi+824], r13
	mov r8, QWORD PTR [rdi+784]
	mov r9, QWORD PTR [rdi+792]
	mov r10, QWORD PTR [rdi+800]
	mov r11, QWORD PTR [rdi+808]
	mov r12, QWORD PTR [rdi+816]
	mov r13, QWORD PTR [rdi+824]
	mov r14d, 0
	add r8, QWORD PTR [rdi+784]
	adc r9, QWORD PTR [rdi+792]
	adc r10, QWORD PTR [rdi+800]
	adc r11, QWORD PTR [rdi+808]
	adc r12, QWORD PTR [rdi+816]
	adc r13, QWORD PTR [rdi+824]
	adc r14, 0
	sub r8, QWORD PTR [rdi+64]
	sbb r9, QWORD PTR [rdi+72]
	sbb r10, QWORD PTR [rdi+80]
	sbb r11, QWORD PTR [rdi+88]
	sbb r12, QWORD PTR [rdi+96]
	sbb r13, QWORD PTR [rdi+104]
	sbb r14, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+784], r8
	mov QWORD PTR [rdi+792], r9
	mov QWORD PTR [rdi+800], r10
	mov QWORD PTR [rdi+808], r11
	mov QWORD PTR [rdi+816], r12
	mov QWORD PTR [rdi+824], r13
	mov r8, QWORD PTR [rdi+1072]
	mov r9, QWORD PTR [rdi+1080]
	mov r10, QWORD PTR [rdi+1088]
	mov r11, QWORD PTR [rdi+1096]
	mov r12, QWORD PTR [rdi+1104]
	mov r13, QWORD PTR [rdi+1112]
	sub r8, QWORD PTR [rdi+784]
	sbb r9, QWORD PTR [rdi+792]
	sbb r10, QWORD PTR [rdi+800]
	sbb r11, QWORD PTR [rdi+808]
	sbb r12, QWORD PTR [rdi+816]
	sbb r13, QWORD PTR [rdi+824]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1072], r8
	mov QWORD PTR [rdi+1080], r9
	mov QWORD PTR [rdi+1088], r10
	mov QWORD PTR [rdi+1096], r11
	mov QWORD PTR [rdi+1104], r12
	mov QWORD PTR [rdi+1112], r13
	mov r8, QWORD PTR [rdi+2128]
	mov r9, QWORD PTR [rdi+2136]
	mov r10, QWORD PTR [rdi+2144]
	mov r11, QWORD PTR [rdi+2152]
	mov r12, QWORD PTR [rdi+2160]
	mov r13, QWORD PTR [rdi+2168]
	mov r14d, 0
	add r8, QWORD PTR [rdi+2128]
	adc r9, QWORD PTR [rdi+2136]
	adc r10, QWORD PTR [rdi+2144]
	adc r11, QWORD PTR [rdi+2152]
	adc r12, QWORD PTR [rdi+2160]
	adc r13, QWORD PTR [rdi+2168]
	adc r14, 0
	sub r8, QWORD PTR [rdi+64]
	sbb r9, QWORD PTR [rdi+72]
	sbb r10, QWORD PTR [rdi+80]
	sbb r11, QWORD PTR [rdi+88]
	sbb r12, QWORD PTR [rdi+96]
	sbb r13, QWORD PTR [rdi+104]
	sbb r14, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+832], r8
	mov QWORD PTR [rdi+840], r9
	mov QWORD PTR [rdi+848], r10
	mov QWORD PTR [rdi+856], r11
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
213:
	mov r8, QWORD PTR [rdi+1024]
	mov r9, QWORD PTR [rdi+1032]
	mov r10, QWORD PTR [rdi+1040]
	mov r11, QWORD PTR [rdi+1048]
	mov r12, QWORD PTR [rdi+1056]
	mov r13, QWORD PTR [rdi+1064]
	sub r8, QWORD PTR [rdi+736]
	sbb r9, QWORD PTR [rdi+744]
	sbb r10, QWORD PTR [rdi+752]
	sbb r11, QWORD PTR [rdi+760]
	sbb r12, QWORD PTR [rdi+768]
	sbb r13, QWORD PTR [rdi+776]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1168], r8
	mov QWORD PTR [rdi+1176], r9
	mov QWORD PTR [rdi+1184], r10
	mov QWORD PTR [rdi+1192], r11
	mov QWORD PTR [rdi+1200], r12
	mov QWORD PTR [rdi+1208], r13
	mov rdx, QWORD PTR [rdi+1168]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1176]
	mulx r10, rax, QWORD PTR [rdi+1184]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1192]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1200]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1208]
	adcx r12, rax
	adcx r13, rbp
	mov QWORD PTR [rdi+4056], r8
	mov QWORD PTR [rdi+4064], r9
	mov rdx, QWORD PTR [rdi+1176]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1184]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1192]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1200]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+1208]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+1184]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1192]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1200]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+1208]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, QWORD PTR [rdi+1192]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1200]
	adox r14, rax
	adcx r15, rcx
	mulx r8, rax, QWORD PTR [rdi+1208]
	adox r15, rax
	adcx r8, rbp
	adox r8, rbp
	mov rdx, QWORD PTR [rdi+1200]
	xor ebp, ebp
	mulx r9, rax, QWORD PTR [rdi+1208]
	adox r8, rax
	adcx r9, rbp
	adox r9, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+1168]
	mulx rcx, rax, rdx
	adcx rbp, rbp
	adox rbp, rax
	mov QWORD PTR [rdi+4048], rbp
	mov rdx, QWORD PTR [rdi+4056]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+1176]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+4064]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	adcx r10, r10
	adox r10, rcx
	mov rdx, QWORD PTR [rdi+1184]
	mulx rcx, rax, rdx
	adcx r11, r11
	adox r11, rax
	adcx r12, r12
	adox r12, rcx
	mov rdx, QWORD PTR [rdi+1192]
	mulx rcx, rax, rdx
	adcx r13, r13
	adox r13, rax
	adcx r14, r14
	adox r14, rcx
	mov rdx, QWORD PTR [rdi+1200]
	mulx rcx, rax, rdx
	adcx r15, r15
	adox r15, rax
	adcx r8, r8
	adox r8, rcx
	mov rdx, QWORD PTR [rdi+1208]
	mulx rcx, rax, rdx
	adcx r9, r9
	adox r9, rax
	mov edx, 0
	adcx rcx, rdx
	adox rcx, rdx
	mov QWORD PTR [rdi+1216], r13
	mov QWORD PTR [rdi+1224], r14
	mov QWORD PTR [rdi+1232], r15
	mov QWORD PTR [rdi+1240], r8
	mov QWORD PTR [rdi+1248], r9
	mov QWORD PTR [rdi+1256], rcx
	mov r13, QWORD PTR [rdi+4048]
	mov r14, QWORD PTR [rdi+4056]
	mov r15, QWORD PTR [rdi+4064]
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r10, rbp
	sbb r11, 0
	sbb r12, 0
	mov r13, rdx
	sbb r13, 0
	movabs rdx, 4294967297
	imul rdx, r14
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r14, rcx
	add rax, r14
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r15, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	mov r14, rdx
	sbb r14, 0
	movabs rdx, 4294967297
	imul rdx, r15
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r15, rcx
	add rax, r15
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	mov r15, rdx
	sbb r15, 0
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	mov r10, rdx
	sbb r10, 0
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r10, 0
	mov r11, rdx
	sbb r11, 0
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r10, 0
	sbb r11, 0
	mov r12, rdx
	sbb r12, 0
	mov r8d, 0
	add r13, QWORD PTR [rdi+1216]
	adc r14, QWORD PTR [rdi+1224]
	adc r15, QWORD PTR [rdi+1232]
	adc r10, QWORD PTR [rdi+1240]
	adc r11, QWORD PTR [rdi+1248]
	adc r12, QWORD PTR [rdi+1256]
	adc r8, 0
	sub r13, QWORD PTR [rdi+64]
	sbb r14, QWORD PTR [rdi+72]
	sbb r15, QWORD PTR [rdi+80]
	sbb r10, QWORD PTR [rdi+88]
	sbb r11, QWORD PTR [rdi+96]
	sbb r12, QWORD PTR [rdi+104]
	sbb r8, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r13, rcx
	adc r14, rdx
	adc r15, rbp
	adc r10, rax
	adc r11, rax
	adc r12, rax
	mov QWORD PTR [rdi+1216], r13
	mov QWORD PTR [rdi+1224], r14
	mov QWORD PTR [rdi+1232], r15
	mov QWORD PTR [rdi+1240], r10
	mov QWORD PTR [rdi+1248], r11
	mov QWORD PTR [rdi+1256], r12
	mov rdx, QWORD PTR [rdi+832]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1168]
	mulx r10, rax, QWORD PTR [rdi+1176]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1184]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1192]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1200]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+1208]
	adcx r13, rax
	adcx r14, rbp
	mov r15d, 0
	movabs rdx, 4294967297
	imul rdx, r8
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r8, rcx
	add rax, r8
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r9, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	sbb rdx, 0
	add r14, rdx
	adc r15, 0
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+840]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1176]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1184]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1192]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1200]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1208]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	adcx r8, rbp
	adox r8, rbp
	movabs rdx, 4294967297
	imul rdx, r9
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r9, rcx
	add rax, r9
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	sbb rdx, 0
	add r15, rdx
	adc r8, 0
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+848]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1176]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1184]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1192]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1200]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1208]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	sbb rdx, 0
	add r8, rdx
	adc r9, 0
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+856]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1176]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1184]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1192]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1200]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1208]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r8, 0
	sbb rdx, 0
	add r9, rdx
	adc r10, 0
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+864]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1176]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1184]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1192]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1200]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1208]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	adcx r11, rbp
	adox r11, rbp
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r8, 0
	sbb r9, 0
	sbb rdx, 0
	add r10, rdx
	adc r11, 0
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+872]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1176]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1184]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1192]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1200]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1208]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	adcx r12, rbp
	adox r12, rbp
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r8, rbp
	sbb r9, 0
	sbb r10, 0
	sbb rdx, 0
	add r11, rdx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+832], r14
	mov QWORD PTR [rdi+840], r15
	mov QWORD PTR [rdi+848], r8
	mov QWORD PTR [rdi+856], r9
	mov QWORD PTR [rdi+864], r10
	mov QWORD PTR [rdi+872], r11
	mov rdx, QWORD PTR [rdi+1024]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1216]
	mulx r10, rax, QWORD PTR [rdi+1224]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1232]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1240]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1248]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+1256]
	adcx r13, rax
	adcx r14, rbp
	mov r15d, 0
	movabs rdx, 4294967297
	imul rdx, r8
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r8, rcx
	add rax, r8
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r9, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	sbb rdx, 0
	add r14, rdx
	adc r15, 0
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+1032]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1216]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1224]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1232]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1256]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	adcx r8, rbp
	adox r8, rbp
	movabs rdx, 4294967297
	imul rdx, r9
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r9, rcx
	add rax, r9
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	sbb rdx, 0
	add r15, rdx
	adc r8, 0
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+1040]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1216]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1224]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1232]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1256]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	sbb rdx, 0
	add r8, rdx
	adc r9, 0
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+1048]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1216]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1224]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1232]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1256]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r8, 0
	sbb rdx, 0
	add r9, rdx
	adc r10, 0
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+1056]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1216]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1224]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1232]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1256]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	adcx r11, rbp
	adox r11, rbp
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r8, 0
	sbb r9, 0
	sbb rdx, 0
	add r10, rdx
	adc r11, 0
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+1064]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1216]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1224]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1232]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1256]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	adcx r12, rbp
	adox r12, rbp
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r8, rbp
	sbb r9, 0
	sbb r10, 0
	sbb rdx, 0
	add r11, rdx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+1024], r14
	mov QWORD PTR [rdi+1032], r15
	mov QWORD PTR [rdi+1040], r8
	mov QWORD PTR [rdi+1048], r9
	mov QWORD PTR [rdi+1056], r10
	mov QWORD PTR [rdi+1064], r11
	mov rdx, QWORD PTR [rdi+736]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1216]
	mulx r10, rax, QWORD PTR [rdi+1224]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1232]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1240]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1248]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+1256]
	adcx r13, rax
	adcx r14, rbp
	mov r15d, 0
	movabs rdx, 4294967297
	imul rdx, r8
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r8, rcx
	add rax, r8
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r9, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	sbb rdx, 0
	add r14, rdx
	adc r15, 0
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+744]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1216]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1224]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1232]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1256]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	adcx r8, rbp
	adox r8, rbp
	movabs rdx, 4294967297
	imul rdx, r9
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r9, rcx
	add rax, r9
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	sbb rdx, 0
	add r15, rdx
	adc r8, 0
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+752]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1216]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1224]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1232]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1256]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	sbb rdx, 0
	add r8, rdx
	adc r9, 0
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+760]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1216]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1224]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1232]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1256]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r8, 0
	sbb rdx, 0
	add r9, rdx
	adc r10, 0
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+768]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1216]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1224]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1232]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1256]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	adcx r11, rbp
	adox r11, rbp
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r8, 0
	sbb r9, 0
	sbb rdx, 0
	add r10, rdx
	adc r11, 0
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+776]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1216]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1224]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1232]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1256]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	adcx r12, rbp
	adox r12, rbp
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r8, rbp
	sbb r9, 0
	sbb r10, 0
	sbb rdx, 0
	add r11, rdx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+1312], r14
	mov QWORD PTR [rdi+1320], r15
	mov QWORD PTR [rdi+1328], r8
	mov QWORD PTR [rdi+1336], r9
	mov QWORD PTR [rdi+1344], r10
	mov QWORD PTR [rdi+1352], r11
	mov r8, QWORD PTR [rdi+1072]
	mov r9, QWORD PTR [rdi+1080]
	mov r10, QWORD PTR [rdi+1088]
	mov r11, QWORD PTR [rdi+1096]
	mov r12, QWORD PTR [rdi+1104]
	mov r13, QWORD PTR [rdi+1112]
	sub r8, QWORD PTR [rdi+784]
	sbb r9, QWORD PTR [rdi+792]
	sbb r10, QWORD PTR [rdi+800]
	sbb r11, QWORD PTR [rdi+808]
	sbb r12, QWORD PTR [rdi+816]
	sbb r13, QWORD PTR [rdi+824]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1360], r8
	mov QWORD PTR [rdi+1368], r9
	mov QWORD PTR [rdi+1376], r10
	mov QWORD PTR [rdi+1384], r11
	mov QWORD PTR [rdi+1392], r12
	mov QWORD PTR [rdi+1400], r13
	mov rdx, QWORD PTR [rdi+1360]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1368]
	mulx r10, rax, QWORD PTR [rdi+1376]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1384]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1392]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1400]
	adcx r12, rax
	adcx r13, rbp
	mov QWORD PTR [rdi+4056], r8
	mov QWORD PTR [rdi+4064], r9
	mov rdx, QWORD PTR [rdi+1368]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+1400]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+1376]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+1400]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, QWORD PTR [rdi+1384]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r14, rax
	adcx r15, rcx
	mulx r8, rax, QWORD PTR [rdi+1400]
	adox r15, rax
	adcx r8, rbp
	adox r8, rbp
	mov rdx, QWORD PTR [rdi+1392]
	xor ebp, ebp
	mulx r9, rax, QWORD PTR [rdi+1400]
	adox r8, rax
	adcx r9, rbp
	adox r9, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+1360]
	mulx rcx, rax, rdx
	adcx rbp, rbp
	adox rbp, rax
	mov QWORD PTR [rdi+4048], rbp
	mov rdx, QWORD PTR [rdi+4056]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+1368]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+4064]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	adcx r10, r10
	adox r10, rcx
	mov rdx, QWORD PTR [rdi+1376]
	mulx rcx, rax, rdx
	adcx r11, r11
	adox r11, rax
	adcx r12, r12
	adox r12, rcx
	mov rdx, QWORD PTR [rdi+1384]
	mulx rcx, rax, rdx
	adcx r13, r13
	adox r13, rax
	adcx r14, r14
	adox r14, rcx
	mov rdx, QWORD PTR [rdi+1392]
	mulx rcx, rax, rdx
	adcx r15, r15
	adox r15, rax
	adcx r8, r8
	adox r8, rcx
	mov rdx, QWORD PTR [rdi+1400]
	mulx rcx, rax, rdx
	adcx r9, r9
	adox r9, rax
	mov edx, 0
	adcx rcx, rdx
	adox rcx, rdx
	mov QWORD PTR [rdi+1408], r13
	mov QWORD PTR [rdi+1416], r14
	mov QWORD PTR [rdi+1424], r15
	mov QWORD PTR [rdi+1432], r8
	mov QWORD PTR [rdi+1440], r9
	mov QWORD PTR [rdi+1448], rcx
	mov r13, QWORD PTR [rdi+4048]
	mov r14, QWORD PTR [rdi+4056]
	mov r15, QWORD PTR [rdi+4064]
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r10, rbp
	sbb r11, 0
	sbb r12, 0
	mov r13, rdx
	sbb r13, 0
	movabs rdx, 4294967297
	imul rdx, r14
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r14, rcx
	add rax, r14
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r15, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	mov r14, rdx
	sbb r14, 0
	movabs rdx, 4294967297
	imul rdx, r15
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r15, rcx
	add rax, r15
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	mov r15, rdx
	sbb r15, 0
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	mov r10, rdx
	sbb r10, 0
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r10, 0
	mov r11, rdx
	sbb r11, 0
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r10, 0
	sbb r11, 0
	mov r12, rdx
	sbb r12, 0
	mov r8d, 0
	add r13, QWORD PTR [rdi+1408]
	adc r14, QWORD PTR [rdi+1416]
	adc r15, QWORD PTR [rdi+1424]
	adc r10, QWORD PTR [rdi+1432]
	adc r11, QWORD PTR [rdi+1440]
	adc r12, QWORD PTR [rdi+1448]
	adc r8, 0
	sub r13, QWORD PTR [rdi+64]
	sbb r14, QWORD PTR [rdi+72]
	sbb r15, QWORD PTR [rdi+80]
	sbb r10, QWORD PTR [rdi+88]
	sbb r11, QWORD PTR [rdi+96]
	sbb r12, QWORD PTR [rdi+104]
	sbb r8, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r13, rcx
	adc r14, rdx
	adc r15, rbp
	adc r10, rax
	adc r11, rax
	adc r12, rax
	mov QWORD PTR [rdi+1408], r13
	mov QWORD PTR [rdi+1416], r14
	mov QWORD PTR [rdi+1424], r15
	mov QWORD PTR [rdi+1432], r10
	mov QWORD PTR [rdi+1440], r11
	mov QWORD PTR [rdi+1448], r12
	mov r8, QWORD PTR [rdi+1024]
	mov r9, QWORD PTR [rdi+1032]
	mov r10, QWORD PTR [rdi+1040]
	mov r11, QWORD PTR [rdi+1048]
	mov r12, QWORD PTR [rdi+1056]
	mov r13, QWORD PTR [rdi+1064]
	sub r8, QWORD PTR [rdi+1312]
	sbb r9, QWORD PTR [rdi+1320]
	sbb r10, QWORD PTR [rdi+1328]
	sbb r11, QWORD PTR [rdi+1336]
	sbb r12, QWORD PTR [rdi+1344]
	sbb r13, QWORD PTR [rdi+1352]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1264], r8
	mov QWORD PTR [rdi+1272], r9
	mov QWORD PTR [rdi+1280], r10
	mov QWORD PTR [rdi+1288], r11
	mov QWORD PTR [rdi+1296], r12
	mov QWORD PTR [rdi+1304], r13
	mov rdx, QWORD PTR [rdi+1072]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1264]
	mulx r10, rax, QWORD PTR [rdi+1272]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1280]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1288]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1296]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+1304]
	adcx r13, rax
	adcx r14, rbp
	mov r15d, 0
	movabs rdx, 4294967297
	imul rdx, r8
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r8, rcx
	add rax, r8
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r9, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	sbb rdx, 0
	add r14, rdx
	adc r15, 0
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+1080]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1264]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1272]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1280]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1288]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1304]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	adcx r8, rbp
	adox r8, rbp
	movabs rdx, 4294967297
	imul rdx, r9
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r9, rcx
	add rax, r9
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	sbb rdx, 0
	add r15, rdx
	adc r8, 0
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+1088]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1264]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1272]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1280]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1288]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1304]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	sbb rdx, 0
	add r8, rdx
	adc r9, 0
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+1096]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1264]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1272]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1280]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1288]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1304]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r8, 0
	sbb rdx, 0
	add r9, rdx
	adc r10, 0
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+1104]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1264]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1272]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1280]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1288]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1304]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	adcx r11, rbp
	adox r11, rbp
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r8, 0
	sbb r9, 0
	sbb rdx, 0
	add r10, rdx
	adc r11, 0
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+1112]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1264]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1272]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1280]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1288]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1304]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	adcx r12, rbp
	adox r12, rbp
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r8, rbp
	sbb r9, 0
	sbb r10, 0
	sbb rdx, 0
	add r11, rdx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+1072], r14
	mov QWORD PTR [rdi+1080], r15
	mov QWORD PTR [rdi+1088], r8
	mov QWORD PTR [rdi+1096], r9
	mov QWORD PTR [rdi+1104], r10
	mov QWORD PTR [rdi+1112], r11
	mov r8, QWORD PTR [rdi+1408]
	mov r9, QWORD PTR [rdi+1416]
	mov r10, QWORD PTR [rdi+1424]
	mov r11, QWORD PTR [rdi+1432]
	mov r12, QWORD PTR [rdi+1440]
	mov r13, QWORD PTR [rdi+1448]
	sub r8, QWORD PTR [rdi+1024]
	sbb r9, QWORD PTR [rdi+1032]
	sbb r10, QWORD PTR [rdi+1040]
	sbb r11, QWORD PTR [rdi+1048]
	sbb r12, QWORD PTR [rdi+1056]
	sbb r13, QWORD PTR [rdi+1064]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+736], r8
	mov QWORD PTR [rdi+744], r9
	mov QWORD PTR [rdi+752], r10
	mov QWORD PTR [rdi+760], r11
	mov QWORD PTR [rdi+768], r12
	mov QWORD PTR [rdi+776], r13
	mov r8, QWORD PTR [rdi+736]
	mov r9, QWORD PTR [rdi+744]
	mov r10, QWORD PTR [rdi+752]
	mov r11, QWORD PTR [rdi+760]
	mov r12, QWORD PTR [rdi+768]
	mov r13, QWORD PTR [rdi+776]
	sub r8, QWORD PTR [rdi+1312]
	sbb r9, QWORD PTR [rdi+1320]
	sbb r10, QWORD PTR [rdi+1328]
	sbb r11, QWORD PTR [rdi+1336]
	sbb r12, QWORD PTR [rdi+1344]
	sbb r13, QWORD PTR [rdi+1352]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+736], r8
	mov QWORD PTR [rdi+744], r9
	mov QWORD PTR [rdi+752], r10
	mov QWORD PTR [rdi+760], r11
	mov QWORD PTR [rdi+768], r12
	mov QWORD PTR [rdi+776], r13
	mov r8, QWORD PTR [rdi+1024]
	mov r9, QWORD PTR [rdi+1032]
	mov r10, QWORD PTR [rdi+1040]
	mov r11, QWORD PTR [rdi+1048]
	mov r12, QWORD PTR [rdi+1056]
	mov r13, QWORD PTR [rdi+1064]
	sub r8, QWORD PTR [rdi+736]
	sbb r9, QWORD PTR [rdi+744]
	sbb r10, QWORD PTR [rdi+752]
	sbb r11, QWORD PTR [rdi+760]
	sbb r12, QWORD PTR [rdi+768]
	sbb r13, QWORD PTR [rdi+776]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+784], r8
	mov QWORD PTR [rdi+792], r9
	mov QWORD PTR [rdi+800], r10
	mov QWORD PTR [rdi+808], r11
	mov QWORD PTR [rdi+816], r12
	mov QWORD PTR [rdi+824], r13
	mov rdx, QWORD PTR [rdi+1360]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+784]
	mulx r10, rax, QWORD PTR [rdi+792]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+800]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+808]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+816]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+824]
	adcx r13, rax
	adcx r14, rbp
	mov r15d, 0
	movabs rdx, 4294967297
	imul rdx, r8
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r8, rcx
	add rax, r8
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r9, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	sbb rdx, 0
	add r14, rdx
	adc r15, 0
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+1368]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+784]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+792]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+808]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+816]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+824]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	adcx r8, rbp
	adox r8, rbp
	movabs rdx, 4294967297
	imul rdx, r9
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r9, rcx
	add rax, r9
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	sbb rdx, 0
	add r15, rdx
	adc r8, 0
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+1376]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+784]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+792]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+808]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+816]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+824]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	sbb rdx, 0
	add r8, rdx
	adc r9, 0
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+1384]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+784]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+792]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+808]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+816]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+824]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r8, 0
	sbb rdx, 0
	add r9, rdx
	adc r10, 0
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+1392]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+784]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+792]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+808]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+816]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+824]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	adcx r11, rbp
	adox r11, rbp
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r8, 0
	sbb r9, 0
	sbb rdx, 0
	add r10, rdx
	adc r11, 0
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+1400]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+784]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+792]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+808]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+816]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+824]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	adcx r12, rbp
	adox r12, rbp
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r8, rbp
	sbb r9, 0
	sbb r10, 0
	sbb rdx, 0
	add r11, rdx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+784], r14
	mov QWORD PTR [rdi+792], r15
	mov QWORD PTR [rdi+800], r8
	mov QWORD PTR [rdi+808], r9
	mov QWORD PTR [rdi+816], r10
	mov QWORD PTR [rdi+824], r11
	mov r8, QWORD PTR [rdi+784]
	mov r9, QWORD PTR [rdi+792]
	mov r10, QWORD PTR [rdi+800]
	mov r11, QWORD PTR [rdi+808]
	mov r12, QWORD PTR [rdi+816]
	mov r13, QWORD PTR [rdi+824]
	sub r8, QWORD PTR [rdi+1072]
	sbb r9, QWORD PTR [rdi+1080]
	sbb r10, QWORD PTR [rdi+1088]
	sbb r11, QWORD PTR [rdi+1096]
	sbb r12, QWORD PTR [rdi+1104]
	sbb r13, QWORD PTR [rdi+1112]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+784], r8
	mov QWORD PTR [rdi+792], r9
	mov QWORD PTR [rdi+800], r10
	mov QWORD PTR [rdi+808], r11
	mov QWORD PTR [rdi+816], r12
	mov QWORD PTR [rdi+824], r13
	mov rax, rbx
	mov ecx, 144
	mul rcx
	mov rdx, rdi
	add rdx, 4096
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdi+736]
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu xmm1, XMMWORD PTR [rdi+752]
	movdqu XMMWORD PTR [rdx+16], xmm1
	movdqu xmm2, XMMWORD PTR [rdi+768]
	movdqu XMMWORD PTR [rdx+32], xmm2
	movdqu xmm3, XMMWORD PTR [rdi+784]
	movdqu XMMWORD PTR [rdx+48], xmm3
	movdqu xmm4, XMMWORD PTR [rdi+800]
	movdqu XMMWORD PTR [rdx+64], xmm4
	movdqu xmm5, XMMWORD PTR [rdi+816]
	movdqu XMMWORD PTR [rdx+80], xmm5
	movdqu xmm6, XMMWORD PTR [rdi+832]
	movdqu XMMWORD PTR [rdx+96], xmm6
	movdqu xmm7, XMMWORD PTR [rdi+848]
	movdqu XMMWORD PTR [rdx+112], xmm7
	movdqu xmm8, XMMWORD PTR [rdi+864]
	movdqu XMMWORD PTR [rdx+128], xmm8
	add rbx, 1
	cmp rbx, 8
	jb 213b
	mov rax, QWORD PTR [rdi+1024]
	mov QWORD PTR [rdi+5248], rax
	mov rax, QWORD PTR [rdi+1032]
	mov QWORD PTR [rdi+5256], rax
	mov rax, QWORD PTR [rdi+1040]
	mov QWORD PTR [rdi+5264], rax
	mov rax, QWORD PTR [rdi+1048]
	mov QWORD PTR [rdi+5272], rax
	mov rax, QWORD PTR [rdi+1056]
	mov QWORD PTR [rdi+5280], rax
	mov rax, QWORD PTR [rdi+1064]
	mov QWORD PTR [rdi+5288], rax
	mov rax, QWORD PTR [rdi+1072]
	mov QWORD PTR [rdi+5296], rax
	mov rax, QWORD PTR [rdi+1080]
	mov QWORD PTR [rdi+5304], rax
	mov rax, QWORD PTR [rdi+1088]
	mov QWORD PTR [rdi+5312], rax
	mov rax, QWORD PTR [rdi+1096]
	mov QWORD PTR [rdi+5320], rax
	mov rax, QWORD PTR [rdi+1104]
	mov QWORD PTR [rdi+5328], rax
	mov rax, QWORD PTR [rdi+1112]
	mov QWORD PTR [rdi+5336], rax
	mov rax, QWORD PTR [rdi+832]
	mov QWORD PTR [rdi+5344], rax
	mov rax, QWORD PTR [rdi+840]
	mov QWORD PTR [rdi+5352], rax
	mov rax, QWORD PTR [rdi+848]
	mov QWORD PTR [rdi+5360], rax
	mov rax, QWORD PTR [rdi+856]
	mov QWORD PTR [rdi+5368], rax
	mov rax, QWORD PTR [rdi+864]
	mov QWORD PTR [rdi+5376], rax
	mov rax, QWORD PTR [rdi+872]
	mov QWORD PTR [rdi+5384], rax
	mov ebx, 0
214:
	mov rax, rbx
	mov ecx, 144
	mul rcx
	mov rdx, rdi
	add rdx, 4096
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdx+96]
	movdqu XMMWORD PTR [rdi+1120], xmm0
	movdqu xmm1, XMMWORD PTR [rdx+112]
	movdqu XMMWORD PTR [rdi+1136], xmm1
	movdqu xmm2, XMMWORD PTR [rdx+128]
	movdqu XMMWORD PTR [rdi+1152], xmm2
	mov rdx, QWORD PTR [rdi+1120]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1128]
	mulx r10, rax, QWORD PTR [rdi+1136]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1144]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1152]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1160]
	adcx r12, rax
	adcx r13, rbp
	mov QWORD PTR [rdi+4056], r8
	mov QWORD PTR [rdi+4064], r9
	mov rdx, QWORD PTR [rdi+1128]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1136]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1144]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1152]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+1160]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+1136]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1144]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1152]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+1160]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, QWORD PTR [rdi+1144]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1152]
	adox r14, rax
	adcx r15, rcx
	mulx r8, rax, QWORD PTR [rdi+1160]
	adox r15, rax
	adcx r8, rbp
	adox r8, rbp
	mov rdx, QWORD PTR [rdi+1152]
	xor ebp, ebp
	mulx r9, rax, QWORD PTR [rdi+1160]
	adox r8, rax
	adcx r9, rbp
	adox r9, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+1120]
	mulx rcx, rax, rdx
	adcx rbp, rbp
	adox rbp, rax
	mov QWORD PTR [rdi+4048], rbp
	mov rdx, QWORD PTR [rdi+4056]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+1128]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+4064]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	adcx r10, r10
	adox r10, rcx
	mov rdx, QWORD PTR [rdi+1136]
	mulx rcx, rax, rdx
	adcx r11, r11
	adox r11, rax
	adcx r12, r12
	adox r12, rcx
	mov rdx, QWORD PTR [rdi+1144]
	mulx rcx, rax, rdx
	adcx r13, r13
	adox r13, rax
	adcx r14, r14
	adox r14, rcx
	mov rdx, QWORD PTR [rdi+1152]
	mulx rcx, rax, rdx
	adcx r15, r15
	adox r15, rax
	adcx r8, r8
	adox r8, rcx
	mov rdx, QWORD PTR [rdi+1160]
	mulx rcx, rax, rdx
	adcx r9, r9
	adox r9, rax
	mov edx, 0
	adcx rcx, rdx
	adox rcx, rdx
	mov QWORD PTR [rdi+1024], r13
	mov QWORD PTR [rdi+1032], r14
	mov QWORD PTR [rdi+1040], r15
	mov QWORD PTR [rdi+1048], r8
	mov QWORD PTR [rdi+1056], r9
	mov QWORD PTR [rdi+1064], rcx
	mov r13, QWORD PTR [rdi+4048]
	mov r14, QWORD PTR [rdi+4056]
	mov r15, QWORD PTR [rdi+4064]
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r10, rbp
	sbb r11, 0
	sbb r12, 0
	mov r13, rdx
	sbb r13, 0
	movabs rdx, 4294967297
	imul rdx, r14
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r14, rcx
	add rax, r14
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r15, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	mov r14, rdx
	sbb r14, 0
	movabs rdx, 4294967297
	imul rdx, r15
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r15, rcx
	add rax, r15
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	mov r15, rdx
	sbb r15, 0
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	mov r10, rdx
	sbb r10, 0
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r10, 0
	mov r11, rdx
	sbb r11, 0
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r10, 0
	sbb r11, 0
	mov r12, rdx
	sbb r12, 0
	mov r8d, 0
	add r13, QWORD PTR [rdi+1024]
	adc r14, QWORD PTR [rdi+1032]
	adc r15, QWORD PTR [rdi+1040]
	adc r10, QWORD PTR [rdi+1048]
	adc r11, QWORD PTR [rdi+1056]
	adc r12, QWORD PTR [rdi+1064]
	adc r8, 0
	sub r13, QWORD PTR [rdi+64]
	sbb r14, QWORD PTR [rdi+72]
	sbb r15, QWORD PTR [rdi+80]
	sbb r10, QWORD PTR [rdi+88]
	sbb r11, QWORD PTR [rdi+96]
	sbb r12, QWORD PTR [rdi+104]
	sbb r8, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r13, rcx
	adc r14, rdx
	adc r15, rbp
	adc r10, rax
	adc r11, rax
	adc r12, rax
	mov QWORD PTR [rdi+1024], r13
	mov QWORD PTR [rdi+1032], r14
	mov QWORD PTR [rdi+1040], r15
	mov QWORD PTR [rdi+1048], r10
	mov QWORD PTR [rdi+1056], r11
	mov QWORD PTR [rdi+1064], r12
	mov rdx, QWORD PTR [rdi+1024]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1120]
	mulx r10, rax, QWORD PTR [rdi+1128]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1136]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1144]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1152]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+1160]
	adcx r13, rax
	adcx r14, rbp
	mov r15d, 0
	movabs rdx, 4294967297
	imul rdx, r8
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r8, rcx
	add rax, r8
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r9, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	sbb rdx, 0
	add r14, rdx
	adc r15, 0
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+1032]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1120]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1128]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1136]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1144]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1152]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1160]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	adcx r8, rbp
	adox r8, rbp
	movabs rdx, 4294967297
	imul rdx, r9
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r9, rcx
	add rax, r9
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	sbb rdx, 0
	add r15, rdx
	adc r8, 0
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+1040]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1120]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1128]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1136]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1144]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1152]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1160]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	sbb rdx, 0
	add r8, rdx
	adc r9, 0
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+1048]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1120]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1128]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1136]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1144]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1152]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1160]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r8, 0
	sbb rdx, 0
	add r9, rdx
	adc r10, 0
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+1056]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1120]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1128]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1136]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1144]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1152]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1160]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	adcx r11, rbp
	adox r11, rbp
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r8, 0
	sbb r9, 0
	sbb rdx, 0
	add r10, rdx
	adc r11, 0
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+1064]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1120]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1128]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1136]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1144]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1152]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1160]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	adcx r12, rbp
	adox r12, rbp
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r8, rbp
	sbb r9, 0
	sbb r10, 0
	sbb rdx, 0
	add r11, rdx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+1072], r14
	mov QWORD PTR [rdi+1080], r15
	mov QWORD PTR [rdi+1088], r8
	mov QWORD PTR [rdi+1096], r9
	mov QWORD PTR [rdi+1104], r10
	mov QWORD PTR [rdi+1112], r11
	mov rax, rbx
	mov ecx, 96
	mul rcx
	mov rdx, rdi
	add rdx, 5392
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdi+1024]
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu xmm1, XMMWORD PTR [rdi+1040]
	movdqu XMMWORD PTR [rdx+16], xmm1
	movdqu xmm2, XMMWORD PTR [rdi+1056]
	movdqu XMMWORD PTR [rdx+32], xmm2
	movdqu xmm3, XMMWORD PTR [rdi+1072]
	movdqu XMMWORD PTR [rdx+48], xmm3
	movdqu xmm4, XMMWORD PTR [rdi+1088]
	movdqu XMMWORD PTR [rdx+64], xmm4
	movdqu xmm5, XMMWORD PTR [rdi+1104]
	movdqu XMMWORD PTR [rdx+80], xmm5
	add rbx, 1
	cmp rbx, 8
	jb 214b
	movabs rax, 0
	mov QWORD PTR [rdi+736], rax
	movabs rax, 0
	mov QWORD PTR [rdi+744], rax
	movabs rax, 0
	mov QWORD PTR [rdi+752], rax
	movabs rax, 0
	mov QWORD PTR [rdi+760], rax
	movabs rax, 0
	mov QWORD PTR [rdi+768], rax
	movabs rax, 0
	mov QWORD PTR [rdi+776], rax
	movabs rax, -4294967295
	mov QWORD PTR [rdi+784], rax
	movabs rax, 4294967295
	mov QWORD PTR [rdi+792], rax
	movabs rax, 1
	mov QWORD PTR [rdi+800], rax
	movabs rax, 0
	mov QWORD PTR [rdi+808], rax
	movabs rax, 0
	mov QWORD PTR [rdi+816], rax
	movabs rax, 0
	mov QWORD PTR [rdi+824], rax
	movabs rax, 0
	mov QWORD PTR [rdi+832], rax
	movabs rax, 0
	mov QWORD PTR [rdi+840], rax
	movabs rax, 0
	mov QWORD PTR [rdi+848], rax
	movabs rax, 0
	mov QWORD PTR [rdi+856], rax
	movabs rax, 0
	mov QWORD PTR [rdi+864], rax
	movabs rax, 0
	mov QWORD PTR [rdi+872], rax
	mov ebx, 385
215:
	sub rbx, 1
	cmp rbx, 384
	je 216f
	mov rdx, QWORD PTR [rdi+832]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+840]
	mulx r10, rax, QWORD PTR [rdi+848]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+856]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+864]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+872]
	adcx r12, rax
	adcx r13, rbp
	mov QWORD PTR [rdi+4056], r8
	mov QWORD PTR [rdi+4064], r9
	mov rdx, QWORD PTR [rdi+840]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+856]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+872]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+848]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+856]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+872]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, QWORD PTR [rdi+856]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r14, rax
	adcx r15, rcx
	mulx r8, rax, QWORD PTR [rdi+872]
	adox r15, rax
	adcx r8, rbp
	adox r8, rbp
	mov rdx, QWORD PTR [rdi+864]
	xor ebp, ebp
	mulx r9, rax, QWORD PTR [rdi+872]
	adox r8, rax
	adcx r9, rbp
	adox r9, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+832]
	mulx rcx, rax, rdx
	adcx rbp, rbp
	adox rbp, rax
	mov QWORD PTR [rdi+4048], rbp
	mov rdx, QWORD PTR [rdi+4056]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+840]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+4064]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	adcx r10, r10
	adox r10, rcx
	mov rdx, QWORD PTR [rdi+848]
	mulx rcx, rax, rdx
	adcx r11, r11
	adox r11, rax
	adcx r12, r12
	adox r12, rcx
	mov rdx, QWORD PTR [rdi+856]
	mulx rcx, rax, rdx
	adcx r13, r13
	adox r13, rax
	adcx r14, r14
	adox r14, rcx
	mov rdx, QWORD PTR [rdi+864]
	mulx rcx, rax, rdx
	adcx r15, r15
	adox r15, rax
	adcx r8, r8
	adox r8, rcx
	mov rdx, QWORD PTR [rdi+872]
	mulx rcx, rax, rdx
	adcx r9, r9
	adox r9, rax
	mov edx, 0
	adcx rcx, rdx
	adox rcx, rdx
	mov QWORD PTR [rdi+1168], r13
	mov QWORD PTR [rdi+1176], r14
	mov QWORD PTR [rdi+1184], r15
	mov QWORD PTR [rdi+1192], r8
	mov QWORD PTR [rdi+1200], r9
	mov QWORD PTR [rdi+1208], rcx
	mov r13, QWORD PTR [rdi+4048]
	mov r14, QWORD PTR [rdi+4056]
	mov r15, QWORD PTR [rdi+4064]
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r10, rbp
	sbb r11, 0
	sbb r12, 0
	mov r13, rdx
	sbb r13, 0
	movabs rdx, 4294967297
	imul rdx, r14
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r14, rcx
	add rax, r14
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r15, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	mov r14, rdx
	sbb r14, 0
	movabs rdx, 4294967297
	imul rdx, r15
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r15, rcx
	add rax, r15
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	mov r15, rdx
	sbb r15, 0
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	mov r10, rdx
	sbb r10, 0
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r10, 0
	mov r11, rdx
	sbb r11, 0
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r10, 0
	sbb r11, 0
	mov r12, rdx
	sbb r12, 0
	mov r8d, 0
	add r13, QWORD PTR [rdi+1168]
	adc r14, QWORD PTR [rdi+1176]
	adc r15, QWORD PTR [rdi+1184]
	adc r10, QWORD PTR [rdi+1192]
	adc r11, QWORD PTR [rdi+1200]
	adc r12, QWORD PTR [rdi+1208]
	adc r8, 0
	sub r13, QWORD PTR [rdi+64]
	sbb r14, QWORD PTR [rdi+72]
	sbb r15, QWORD PTR [rdi+80]
	sbb r10, QWORD PTR [rdi+88]
	sbb r11, QWORD PTR [rdi+96]
	sbb r12, QWORD PTR [rdi+104]
	sbb r8, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r13, rcx
	adc r14, rdx
	adc r15, rbp
	adc r10, rax
	adc r11, rax
	adc r12, rax
	mov QWORD PTR [rdi+1168], r13
	mov QWORD PTR [rdi+1176], r14
	mov QWORD PTR [rdi+1184], r15
	mov QWORD PTR [rdi+1192], r10
	mov QWORD PTR [rdi+1200], r11
	mov QWORD PTR [rdi+1208], r12
	mov rdx, QWORD PTR [rdi+784]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+792]
	mulx r10, rax, QWORD PTR [rdi+800]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+808]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+816]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+824]
	adcx r12, rax
	adcx r13, rbp
	mov QWORD PTR [rdi+4056], r8
	mov QWORD PTR [rdi+4064], r9
	mov rdx, QWORD PTR [rdi+792]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+808]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+816]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+824]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+800]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+808]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+816]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+824]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, QWORD PTR [rdi+808]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+816]
	adox r14, rax
	adcx r15, rcx
	mulx r8, rax, QWORD PTR [rdi+824]
	adox r15, rax
	adcx r8, rbp
	adox r8, rbp
	mov rdx, QWORD PTR [rdi+816]
	xor ebp, ebp
	mulx r9, rax, QWORD PTR [rdi+824]
	adox r8, rax
	adcx r9, rbp
	adox r9, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+784]
	mulx rcx, rax, rdx
	adcx rbp, rbp
	adox rbp, rax
	mov QWORD PTR [rdi+4048], rbp
	mov rdx, QWORD PTR [rdi+4056]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+792]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+4064]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	adcx r10, r10
	adox r10, rcx
	mov rdx, QWORD PTR [rdi+800]
	mulx rcx, rax, rdx
	adcx r11, r11
	adox r11, rax
	adcx r12, r12
	adox r12, rcx
	mov rdx, QWORD PTR [rdi+808]
	mulx rcx, rax, rdx
	adcx r13, r13
	adox r13, rax
	adcx r14, r14
	adox r14, rcx
	mov rdx, QWORD PTR [rdi+816]
	mulx rcx, rax, rdx
	adcx r15, r15
	adox r15, rax
	adcx r8, r8
	adox r8, rcx
	mov rdx, QWORD PTR [rdi+824]
	mulx rcx, rax, rdx
	adcx r9, r9
	adox r9, rax
	mov edx, 0
	adcx rcx, rdx
	adox rcx, rdx
	mov QWORD PTR [rdi+1216], r13
	mov QWORD PTR [rdi+1224], r14
	mov QWORD PTR [rdi+1232], r15
	mov QWORD PTR [rdi+1240], r8
	mov QWORD PTR [rdi+1248], r9
	mov QWORD PTR [rdi+1256], rcx
	mov r13, QWORD PTR [rdi+4048]
	mov r14, QWORD PTR [rdi+4056]
	mov r15, QWORD PTR [rdi+4064]
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r10, rbp
	sbb r11, 0
	sbb r12, 0
	mov r13, rdx
	sbb r13, 0
	movabs rdx, 4294967297
	imul rdx, r14
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r14, rcx
	add rax, r14
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r15, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	mov r14, rdx
	sbb r14, 0
	movabs rdx, 4294967297
	imul rdx, r15
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r15, rcx
	add rax, r15
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	mov r15, rdx
	sbb r15, 0
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	mov r10, rdx
	sbb r10, 0
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r10, 0
	mov r11, rdx
	sbb r11, 0
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r10, 0
	sbb r11, 0
	mov r12, rdx
	sbb r12, 0
	mov r8d, 0
	add r13, QWORD PTR [rdi+1216]
	adc r14, QWORD PTR [rdi+1224]
	adc r15, QWORD PTR [rdi+1232]
	adc r10, QWORD PTR [rdi+1240]
	adc r11, QWORD PTR [rdi+1248]
	adc r12, QWORD PTR [rdi+1256]
	adc r8, 0
	sub r13, QWORD PTR [rdi+64]
	sbb r14, QWORD PTR [rdi+72]
	sbb r15, QWORD PTR [rdi+80]
	sbb r10, QWORD PTR [rdi+88]
	sbb r11, QWORD PTR [rdi+96]
	sbb r12, QWORD PTR [rdi+104]
	sbb r8, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r13, rcx
	adc r14, rdx
	adc r15, rbp
	adc r10, rax
	adc r11, rax
	adc r12, rax
	mov QWORD PTR [rdi+1216], r13
	mov QWORD PTR [rdi+1224], r14
	mov QWORD PTR [rdi+1232], r15
	mov QWORD PTR [rdi+1240], r10
	mov QWORD PTR [rdi+1248], r11
	mov QWORD PTR [rdi+1256], r12
	mov r8, QWORD PTR [rdi+736]
	mov r9, QWORD PTR [rdi+744]
	mov r10, QWORD PTR [rdi+752]
	mov r11, QWORD PTR [rdi+760]
	mov r12, QWORD PTR [rdi+768]
	mov r13, QWORD PTR [rdi+776]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1168]
	adc r9, QWORD PTR [rdi+1176]
	adc r10, QWORD PTR [rdi+1184]
	adc r11, QWORD PTR [rdi+1192]
	adc r12, QWORD PTR [rdi+1200]
	adc r13, QWORD PTR [rdi+1208]
	adc r14, 0
	sub r8, QWORD PTR [rdi+64]
	sbb r9, QWORD PTR [rdi+72]
	sbb r10, QWORD PTR [rdi+80]
	sbb r11, QWORD PTR [rdi+88]
	sbb r12, QWORD PTR [rdi+96]
	sbb r13, QWORD PTR [rdi+104]
	sbb r14, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1264], r8
	mov QWORD PTR [rdi+1272], r9
	mov QWORD PTR [rdi+1280], r10
	mov QWORD PTR [rdi+1288], r11
	mov QWORD PTR [rdi+1296], r12
	mov QWORD PTR [rdi+1304], r13
	mov r8, QWORD PTR [rdi+736]
	mov r9, QWORD PTR [rdi+744]
	mov r10, QWORD PTR [rdi+752]
	mov r11, QWORD PTR [rdi+760]
	mov r12, QWORD PTR [rdi+768]
	mov r13, QWORD PTR [rdi+776]
	sub r8, QWORD PTR [rdi+1168]
	sbb r9, QWORD PTR [rdi+1176]
	sbb r10, QWORD PTR [rdi+1184]
	sbb r11, QWORD PTR [rdi+1192]
	sbb r12, QWORD PTR [rdi+1200]
	sbb r13, QWORD PTR [rdi+1208]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1312], r8
	mov QWORD PTR [rdi+1320], r9
	mov QWORD PTR [rdi+1328], r10
	mov QWORD PTR [rdi+1336], r11
	mov QWORD PTR [rdi+1344], r12
	mov QWORD PTR [rdi+1352], r13
	mov rdx, QWORD PTR [rdi+1264]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1312]
	mulx r10, rax, QWORD PTR [rdi+1320]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1328]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1336]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1344]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+1352]
	adcx r13, rax
	adcx r14, rbp
	mov r15d, 0
	movabs rdx, 4294967297
	imul rdx, r8
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r8, rcx
	add rax, r8
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r9, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	sbb rdx, 0
	add r14, rdx
	adc r15, 0
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+1272]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	adcx r8, rbp
	adox r8, rbp
	movabs rdx, 4294967297
	imul rdx, r9
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r9, rcx
	add rax, r9
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	sbb rdx, 0
	add r15, rdx
	adc r8, 0
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+1280]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	sbb rdx, 0
	add r8, rdx
	adc r9, 0
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+1288]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r8, 0
	sbb rdx, 0
	add r9, rdx
	adc r10, 0
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+1296]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	adcx r11, rbp
	adox r11, rbp
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r8, 0
	sbb r9, 0
	sbb rdx, 0
	add r10, rdx
	adc r11, 0
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+1304]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1312]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1320]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1328]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1336]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1344]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1352]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	adcx r12, rbp
	adox r12, rbp
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r8, rbp
	sbb r9, 0
	sbb r10, 0
	sbb rdx, 0
	add r11, rdx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+1360], r14
	mov QWORD PTR [rdi+1368], r15
	mov QWORD PTR [rdi+1376], r8
	mov QWORD PTR [rdi+1384], r9
	mov QWORD PTR [rdi+1392], r10
	mov QWORD PTR [rdi+1400], r11
	mov r8, QWORD PTR [rdi+784]
	mov r9, QWORD PTR [rdi+792]
	mov r10, QWORD PTR [rdi+800]
	mov r11, QWORD PTR [rdi+808]
	mov r12, QWORD PTR [rdi+816]
	mov r13, QWORD PTR [rdi+824]
	mov r14d, 0
	add r8, QWORD PTR [rdi+832]
	adc r9, QWORD PTR [rdi+840]
	adc r10, QWORD PTR [rdi+848]
	adc r11, QWORD PTR [rdi+856]
	adc r12, QWORD PTR [rdi+864]
	adc r13, QWORD PTR [rdi+872]
	adc r14, 0
	sub r8, QWORD PTR [rdi+64]
	sbb r9, QWORD PTR [rdi+72]
	sbb r10, QWORD PTR [rdi+80]
	sbb r11, QWORD PTR [rdi+88]
	sbb r12, QWORD PTR [rdi+96]
	sbb r13, QWORD PTR [rdi+104]
	sbb r14, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1264], r8
	mov QWORD PTR [rdi+1272], r9
	mov QWORD PTR [rdi+1280], r10
	mov QWORD PTR [rdi+1288], r11
	mov QWORD PTR [rdi+1296], r12
	mov QWORD PTR [rdi+1304], r13
	mov rdx, QWORD PTR [rdi+1360]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1368]
	mulx r10, rax, QWORD PTR [rdi+1376]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1384]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1392]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1400]
	adcx r12, rax
	adcx r13, rbp
	mov QWORD PTR [rdi+4056], r8
	mov QWORD PTR [rdi+4064], r9
	mov rdx, QWORD PTR [rdi+1368]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+1400]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+1376]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+1400]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, QWORD PTR [rdi+1384]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r14, rax
	adcx r15, rcx
	mulx r8, rax, QWORD PTR [rdi+1400]
	adox r15, rax
	adcx r8, rbp
	adox r8, rbp
	mov rdx, QWORD PTR [rdi+1392]
	xor ebp, ebp
	mulx r9, rax, QWORD PTR [rdi+1400]
	adox r8, rax
	adcx r9, rbp
	adox r9, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+1360]
	mulx rcx, rax, rdx
	adcx rbp, rbp
	adox rbp, rax
	mov QWORD PTR [rdi+4048], rbp
	mov rdx, QWORD PTR [rdi+4056]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+1368]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+4064]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	adcx r10, r10
	adox r10, rcx
	mov rdx, QWORD PTR [rdi+1376]
	mulx rcx, rax, rdx
	adcx r11, r11
	adox r11, rax
	adcx r12, r12
	adox r12, rcx
	mov rdx, QWORD PTR [rdi+1384]
	mulx rcx, rax, rdx
	adcx r13, r13
	adox r13, rax
	adcx r14, r14
	adox r14, rcx
	mov rdx, QWORD PTR [rdi+1392]
	mulx rcx, rax, rdx
	adcx r15, r15
	adox r15, rax
	adcx r8, r8
	adox r8, rcx
	mov rdx, QWORD PTR [rdi+1400]
	mulx rcx, rax, rdx
	adcx r9, r9
	adox r9, rax
	mov edx, 0
	adcx rcx, rdx
	adox rcx, rdx
	mov QWORD PTR [rdi+1312], r13
	mov QWORD PTR [rdi+1320], r14
	mov QWORD PTR [rdi+1328], r15
	mov QWORD PTR [rdi+1336], r8
	mov QWORD PTR [rdi+1344], r9
	mov QWORD PTR [rdi+1352], rcx
	mov r13, QWORD PTR [rdi+4048]
	mov r14, QWORD PTR [rdi+4056]
	mov r15, QWORD PTR [rdi+4064]
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r10, rbp
	sbb r11, 0
	sbb r12, 0
	mov r13, rdx
	sbb r13, 0
	movabs rdx, 4294967297
	imul rdx, r14
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r14, rcx
	add rax, r14
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r15, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	mov r14, rdx
	sbb r14, 0
	movabs rdx, 4294967297
	imul rdx, r15
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r15, rcx
	add rax, r15
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	mov r15, rdx
	sbb r15, 0
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	mov r10, rdx
	sbb r10, 0
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r10, 0
	mov r11, rdx
	sbb r11, 0
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r10, 0
	sbb r11, 0
	mov r12, rdx
	sbb r12, 0
	mov r8d, 0
	add r13, QWORD PTR [rdi+1312]
	adc r14, QWORD PTR [rdi+1320]
	adc r15, QWORD PTR [rdi+1328]
	adc r10, QWORD PTR [rdi+1336]
	adc r11, QWORD PTR [rdi+1344]
	adc r12, QWORD PTR [rdi+1352]
	adc r8, 0
	sub r13, QWORD PTR [rdi+64]
	sbb r14, QWORD PTR [rdi+72]
	sbb r15, QWORD PTR [rdi+80]
	sbb r10, QWORD PTR [rdi+88]
	sbb r11, QWORD PTR [rdi+96]
	sbb r12, QWORD PTR [rdi+104]
	sbb r8, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r13, rcx
	adc r14, rdx
	adc r15, rbp
	adc r10, rax
	adc r11, rax
	adc r12, rax
	mov QWORD PTR [rdi+1312], r13
	mov QWORD PTR [rdi+1320], r14
	mov QWORD PTR [rdi+1328], r15
	mov QWORD PTR [rdi+1336], r10
	mov QWORD PTR [rdi+1344], r11
	mov QWORD PTR [rdi+1352], r12
	mov rdx, QWORD PTR [rdi+736]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1216]
	mulx r10, rax, QWORD PTR [rdi+1224]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1232]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1240]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1248]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+1256]
	adcx r13, rax
	adcx r14, rbp
	mov r15d, 0
	movabs rdx, 4294967297
	imul rdx, r8
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r8, rcx
	add rax, r8
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r9, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	sbb rdx, 0
	add r14, rdx
	adc r15, 0
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+744]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1216]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1224]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1232]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1256]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	adcx r8, rbp
	adox r8, rbp
	movabs rdx, 4294967297
	imul rdx, r9
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r9, rcx
	add rax, r9
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	sbb rdx, 0
	add r15, rdx
	adc r8, 0
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+752]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1216]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1224]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1232]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1256]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	sbb rdx, 0
	add r8, rdx
	adc r9, 0
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+760]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1216]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1224]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1232]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1256]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r8, 0
	sbb rdx, 0
	add r9, rdx
	adc r10, 0
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+768]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1216]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1224]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1232]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1256]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	adcx r11, rbp
	adox r11, rbp
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r8, 0
	sbb r9, 0
	sbb rdx, 0
	add r10, rdx
	adc r11, 0
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+776]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1216]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1224]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1232]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1256]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	adcx r12, rbp
	adox r12, rbp
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r8, rbp
	sbb r9, 0
	sbb r10, 0
	sbb rdx, 0
	add r11, rdx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+1408], r14
	mov QWORD PTR [rdi+1416], r15
	mov QWORD PTR [rdi+1424], r8
	mov QWORD PTR [rdi+1432], r9
	mov QWORD PTR [rdi+1440], r10
	mov QWORD PTR [rdi+1448], r11
	mov rdx, QWORD PTR [rdi+1264]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1272]
	mulx r10, rax, QWORD PTR [rdi+1280]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1288]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1296]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1304]
	adcx r12, rax
	adcx r13, rbp
	mov QWORD PTR [rdi+4056], r8
	mov QWORD PTR [rdi+4064], r9
	mov rdx, QWORD PTR [rdi+1272]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1280]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1288]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+1304]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+1280]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1288]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+1304]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, QWORD PTR [rdi+1288]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r14, rax
	adcx r15, rcx
	mulx r8, rax, QWORD PTR [rdi+1304]
	adox r15, rax
	adcx r8, rbp
	adox r8, rbp
	mov rdx, QWORD PTR [rdi+1296]
	xor ebp, ebp
	mulx r9, rax, QWORD PTR [rdi+1304]
	adox r8, rax
	adcx r9, rbp
	adox r9, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+1264]
	mulx rcx, rax, rdx
	adcx rbp, rbp
	adox rbp, rax
	mov QWORD PTR [rdi+4048], rbp
	mov rdx, QWORD PTR [rdi+4056]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+1272]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+4064]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	adcx r10, r10
	adox r10, rcx
	mov rdx, QWORD PTR [rdi+1280]
	mulx rcx, rax, rdx
	adcx r11, r11
	adox r11, rax
	adcx r12, r12
	adox r12, rcx
	mov rdx, QWORD PTR [rdi+1288]
	mulx rcx, rax, rdx
	adcx r13, r13
	adox r13, rax
	adcx r14, r14
	adox r14, rcx
	mov rdx, QWORD PTR [rdi+1296]
	mulx rcx, rax, rdx
	adcx r15, r15
	adox r15, rax
	adcx r8, r8
	adox r8, rcx
	mov rdx, QWORD PTR [rdi+1304]
	mulx rcx, rax, rdx
	adcx r9, r9
	adox r9, rax
	mov edx, 0
	adcx rcx, rdx
	adox rcx, rdx
	mov QWORD PTR [rdi+1264], r13
	mov QWORD PTR [rdi+1272], r14
	mov QWORD PTR [rdi+1280], r15
	mov QWORD PTR [rdi+1288], r8
	mov QWORD PTR [rdi+1296], r9
	mov QWORD PTR [rdi+1304], rcx
	mov r13, QWORD PTR [rdi+4048]
	mov r14, QWORD PTR [rdi+4056]
	mov r15, QWORD PTR [rdi+4064]
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r10, rbp
	sbb r11, 0
	sbb r12, 0
	mov r13, rdx
	sbb r13, 0
	movabs rdx, 4294967297
	imul rdx, r14
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r14, rcx
	add rax, r14
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r15, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	mov r14, rdx
	sbb r14, 0
	movabs rdx, 4294967297
	imul rdx, r15
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r15, rcx
	add rax, r15
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	mov r15, rdx
	sbb r15, 0
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	mov r10, rdx
	sbb r10, 0
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r10, 0
	mov r11, rdx
	sbb r11, 0
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r10, 0
	sbb r11, 0
	mov r12, rdx
	sbb r12, 0
	mov r8d, 0
	add r13, QWORD PTR [rdi+1264]
	adc r14, QWORD PTR [rdi+1272]
	adc r15, QWORD PTR [rdi+1280]
	adc r10, QWORD PTR [rdi+1288]
	adc r11, QWORD PTR [rdi+1296]
	adc r12, QWORD PTR [rdi+1304]
	adc r8, 0
	sub r13, QWORD PTR [rdi+64]
	sbb r14, QWORD PTR [rdi+72]
	sbb r15, QWORD PTR [rdi+80]
	sbb r10, QWORD PTR [rdi+88]
	sbb r11, QWORD PTR [rdi+96]
	sbb r12, QWORD PTR [rdi+104]
	sbb r8, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r13, rcx
	adc r14, rdx
	adc r15, rbp
	adc r10, rax
	adc r11, rax
	adc r12, rax
	mov QWORD PTR [rdi+1264], r13
	mov QWORD PTR [rdi+1272], r14
	mov QWORD PTR [rdi+1280], r15
	mov QWORD PTR [rdi+1288], r10
	mov QWORD PTR [rdi+1296], r11
	mov QWORD PTR [rdi+1304], r12
	mov r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+88]
	mov r12, QWORD PTR [rdi+96]
	mov r13, QWORD PTR [rdi+104]
	sub r8, QWORD PTR [rdi+1312]
	sbb r9, QWORD PTR [rdi+1320]
	sbb r10, QWORD PTR [rdi+1328]
	sbb r11, QWORD PTR [rdi+1336]
	sbb r12, QWORD PTR [rdi+1344]
	sbb r13, QWORD PTR [rdi+1352]
	mov QWORD PTR [rdi+4048], r8
	mov QWORD PTR [rdi+4056], r9
	mov QWORD PTR [rdi+4064], r10
	mov QWORD PTR [rdi+4072], r11
	mov QWORD PTR [rdi+4080], r12
	mov QWORD PTR [rdi+4088], r13
	mov edx, 9
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+4048]
	mulx r10, rax, QWORD PTR [rdi+4056]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+4064]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+4072]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+4080]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+4088]
	adcx r13, rax
	adcx r14, rbp
	mov r15d, 0
	mov edx, 12
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1408]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1416]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1424]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1432]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1440]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1448]
	adox r13, rax
	adcx r14, rcx
	adox r14, rbp
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r14
	xor ebp, ebp
	movabs rax, -4294967295
	mulx rcx, rax, rax
	adox r8, rax
	adcx r9, rcx
	mov eax, -1
	mulx rcx, rax, rax
	adox r9, rax
	adcx r10, rcx
	adox r10, rdx
	mov r14d, 0
	adcx r11, rbp
	adox r11, rbp
	adcx r12, rbp
	adox r12, rbp
	adcx r13, rbp
	adox r13, rbp
	adcx r14, rbp
	adox r14, rbp
	sub r8, QWORD PTR [rdi+64]
	sbb r9, QWORD PTR [rdi+72]
	sbb r10, QWORD PTR [rdi+80]
	sbb r11, QWORD PTR [rdi+88]
	sbb r12, QWORD PTR [rdi+96]
	sbb r13, QWORD PTR [rdi+104]
	sbb r14, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1312], r8
	mov QWORD PTR [rdi+1320], r9
	mov QWORD PTR [rdi+1328], r10
	mov QWORD PTR [rdi+1336], r11
	mov QWORD PTR [rdi+1344], r12
	mov QWORD PTR [rdi+1352], r13
	mov r8, QWORD PTR [rdi+1264]
	mov r9, QWORD PTR [rdi+1272]
	mov r10, QWORD PTR [rdi+1280]
	mov r11, QWORD PTR [rdi+1288]
	mov r12, QWORD PTR [rdi+1296]
	mov r13, QWORD PTR [rdi+1304]
	sub r8, QWORD PTR [rdi+1168]
	sbb r9, QWORD PTR [rdi+1176]
	sbb r10, QWORD PTR [rdi+1184]
	sbb r11, QWORD PTR [rdi+1192]
	sbb r12, QWORD PTR [rdi+1200]
	sbb r13, QWORD PTR [rdi+1208]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1264], r8
	mov QWORD PTR [rdi+1272], r9
	mov QWORD PTR [rdi+1280], r10
	mov QWORD PTR [rdi+1288], r11
	mov QWORD PTR [rdi+1296], r12
	mov QWORD PTR [rdi+1304], r13
	mov r8, QWORD PTR [rdi+1264]
	mov r9, QWORD PTR [rdi+1272]
	mov r10, QWORD PTR [rdi+1280]
	mov r11, QWORD PTR [rdi+1288]
	mov r12, QWORD PTR [rdi+1296]
	mov r13, QWORD PTR [rdi+1304]
	sub r8, QWORD PTR [rdi+1216]
	sbb r9, QWORD PTR [rdi+1224]
	sbb r10, QWORD PTR [rdi+1232]
	sbb r11, QWORD PTR [rdi+1240]
	sbb r12, QWORD PTR [rdi+1248]
	sbb r13, QWORD PTR [rdi+1256]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+832], r8
	mov QWORD PTR [rdi+840], r9
	mov QWORD PTR [rdi+848], r10
	mov QWORD PTR [rdi+856], r11
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
	mov rdx, QWORD PTR [rdi+1216]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1224]
	mulx r10, rax, QWORD PTR [rdi+1232]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1240]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1248]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1256]
	adcx r12, rax
	adcx r13, rbp
	mov QWORD PTR [rdi+4056], r8
	mov QWORD PTR [rdi+4064], r9
	mov rdx, QWORD PTR [rdi+1224]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1232]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+1256]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+1232]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1240]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+1256]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, QWORD PTR [rdi+1240]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1248]
	adox r14, rax
	adcx r15, rcx
	mulx r8, rax, QWORD PTR [rdi+1256]
	adox r15, rax
	adcx r8, rbp
	adox r8, rbp
	mov rdx, QWORD PTR [rdi+1248]
	xor ebp, ebp
	mulx r9, rax, QWORD PTR [rdi+1256]
	adox r8, rax
	adcx r9, rbp
	adox r9, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+1216]
	mulx rcx, rax, rdx
	adcx rbp, rbp
	adox rbp, rax
	mov QWORD PTR [rdi+4048], rbp
	mov rdx, QWORD PTR [rdi+4056]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+1224]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+4064]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	adcx r10, r10
	adox r10, rcx
	mov rdx, QWORD PTR [rdi+1232]
	mulx rcx, rax, rdx
	adcx r11, r11
	adox r11, rax
	adcx r12, r12
	adox r12, rcx
	mov rdx, QWORD PTR [rdi+1240]
	mulx rcx, rax, rdx
	adcx r13, r13
	adox r13, rax
	adcx r14, r14
	adox r14, rcx
	mov rdx, QWORD PTR [rdi+1248]
	mulx rcx, rax, rdx
	adcx r15, r15
	adox r15, rax
	adcx r8, r8
	adox r8, rcx
	mov rdx, QWORD PTR [rdi+1256]
	mulx rcx, rax, rdx
	adcx r9, r9
	adox r9, rax
	mov edx, 0
	adcx rcx, rdx
	adox rcx, rdx
	mov QWORD PTR [rdi+1168], r13
	mov QWORD PTR [rdi+1176], r14
	mov QWORD PTR [rdi+1184], r15
	mov QWORD PTR [rdi+1192], r8
	mov QWORD PTR [rdi+1200], r9
	mov QWORD PTR [rdi+1208], rcx
	mov r13, QWORD PTR [rdi+4048]
	mov r14, QWORD PTR [rdi+4056]
	mov r15, QWORD PTR [rdi+4064]
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r10, rbp
	sbb r11, 0
	sbb r12, 0
	mov r13, rdx
	sbb r13, 0
	movabs rdx, 4294967297
	imul rdx, r14
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r14, rcx
	add rax, r14
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r15, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	mov r14, rdx
	sbb r14, 0
	movabs rdx, 4294967297
	imul rdx, r15
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r15, rcx
	add rax, r15
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	mov r15, rdx
	sbb r15, 0
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	mov r10, rdx
	sbb r10, 0
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r10, 0
	mov r11, rdx
	sbb r11, 0
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r10, 0
	sbb r11, 0
	mov r12, rdx
	sbb r12, 0
	mov r8d, 0
	add r13, QWORD PTR [rdi+1168]
	adc r14, QWORD PTR [rdi+1176]
	adc r15, QWORD PTR [rdi+1184]
	adc r10, QWORD PTR [rdi+1192]
	adc r11, QWORD PTR [rdi+1200]
	adc r12, QWORD PTR [rdi+1208]
	adc r8, 0
	sub r13, QWORD PTR [rdi+64]
	sbb r14, QWORD PTR [rdi+72]
	sbb r15, QWORD PTR [rdi+80]
	sbb r10, QWORD PTR [rdi+88]
	sbb r11, QWORD PTR [rdi+96]
	sbb r12, QWORD PTR [rdi+104]
	sbb r8, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r13, rcx
	adc r14, rdx
	adc r15, rbp
	adc r10, rax
	adc r11, rax
	adc r12, rax
	mov QWORD PTR [rdi+1168], r13
	mov QWORD PTR [rdi+1176], r14
	mov QWORD PTR [rdi+1184], r15
	mov QWORD PTR [rdi+1192], r10
	mov QWORD PTR [rdi+1200], r11
	mov QWORD PTR [rdi+1208], r12
	mov rdx, QWORD PTR [rdi+1312]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1360]
	mulx r10, rax, QWORD PTR [rdi+1368]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1376]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1384]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1392]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+1400]
	adcx r13, rax
	adcx r14, rbp
	mov r15d, 0
	movabs rdx, 4294967297
	imul rdx, r8
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r8, rcx
	add rax, r8
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r9, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	sbb rdx, 0
	add r14, rdx
	adc r15, 0
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+1320]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1360]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1400]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	adcx r8, rbp
	adox r8, rbp
	movabs rdx, 4294967297
	imul rdx, r9
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r9, rcx
	add rax, r9
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	sbb rdx, 0
	add r15, rdx
	adc r8, 0
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+1328]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1360]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1400]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	sbb rdx, 0
	add r8, rdx
	adc r9, 0
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+1336]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1360]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1400]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r8, 0
	sbb rdx, 0
	add r9, rdx
	adc r10, 0
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+1344]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1360]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1400]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	adcx r11, rbp
	adox r11, rbp
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r8, 0
	sbb r9, 0
	sbb rdx, 0
	add r10, rdx
	adc r11, 0
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+1352]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1360]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1400]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	adcx r12, rbp
	adox r12, rbp
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r8, rbp
	sbb r9, 0
	sbb r10, 0
	sbb rdx, 0
	add r11, rdx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+1360], r14
	mov QWORD PTR [rdi+1368], r15
	mov QWORD PTR [rdi+1376], r8
	mov QWORD PTR [rdi+1384], r9
	mov QWORD PTR [rdi+1392], r10
	mov QWORD PTR [rdi+1400], r11
	mov r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+88]
	mov r12, QWORD PTR [rdi+96]
	mov r13, QWORD PTR [rdi+104]
	sub r8, QWORD PTR [rdi+1312]
	sbb r9, QWORD PTR [rdi+1320]
	sbb r10, QWORD PTR [rdi+1328]
	sbb r11, QWORD PTR [rdi+1336]
	sbb r12, QWORD PTR [rdi+1344]
	sbb r13, QWORD PTR [rdi+1352]
	mov QWORD PTR [rdi+4048], r8
	mov QWORD PTR [rdi+4056], r9
	mov QWORD PTR [rdi+4064], r10
	mov QWORD PTR [rdi+4072], r11
	mov QWORD PTR [rdi+4080], r12
	mov QWORD PTR [rdi+4088], r13
	mov edx, 1
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+4048]
	mulx r10, rax, QWORD PTR [rdi+4056]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+4064]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+4072]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+4080]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+4088]
	adcx r13, rax
	adcx r14, rbp
	mov r15d, 0
	mov edx, 4
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1408]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1416]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1424]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1432]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1440]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1448]
	adox r13, rax
	adcx r14, rcx
	adox r14, rbp
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r14
	xor ebp, ebp
	movabs rax, -4294967295
	mulx rcx, rax, rax
	adox r8, rax
	adcx r9, rcx
	mov eax, -1
	mulx rcx, rax, rax
	adox r9, rax
	adcx r10, rcx
	adox r10, rdx
	mov r14d, 0
	adcx r11, rbp
	adox r11, rbp
	adcx r12, rbp
	adox r12, rbp
	adcx r13, rbp
	adox r13, rbp
	adcx r14, rbp
	adox r14, rbp
	sub r8, QWORD PTR [rdi+64]
	sbb r9, QWORD PTR [rdi+72]
	sbb r10, QWORD PTR [rdi+80]
	sbb r11, QWORD PTR [rdi+88]
	sbb r12, QWORD PTR [rdi+96]
	sbb r13, QWORD PTR [rdi+104]
	sbb r14, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+736], r8
	mov QWORD PTR [rdi+744], r9
	mov QWORD PTR [rdi+752], r10
	mov QWORD PTR [rdi+760], r11
	mov QWORD PTR [rdi+768], r12
	mov QWORD PTR [rdi+776], r13
	mov r8, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+72]
	mov r10, QWORD PTR [rdi+80]
	mov r11, QWORD PTR [rdi+88]
	mov r12, QWORD PTR [rdi+96]
	mov r13, QWORD PTR [rdi+104]
	sub r8, QWORD PTR [rdi+1168]
	sbb r9, QWORD PTR [rdi+1176]
	sbb r10, QWORD PTR [rdi+1184]
	sbb r11, QWORD PTR [rdi+1192]
	sbb r12, QWORD PTR [rdi+1200]
	sbb r13, QWORD PTR [rdi+1208]
	mov QWORD PTR [rdi+4048], r8
	mov QWORD PTR [rdi+4056], r9
	mov QWORD PTR [rdi+4064], r10
	mov QWORD PTR [rdi+4072], r11
	mov QWORD PTR [rdi+4080], r12
	mov QWORD PTR [rdi+4088], r13
	mov edx, 8
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+4048]
	mulx r10, rax, QWORD PTR [rdi+4056]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+4064]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+4072]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+4080]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+4088]
	adcx r13, rax
	adcx r14, rbp
	mov r15d, 0
	mov edx, 3
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1360]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1368]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1376]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1384]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1392]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1400]
	adox r13, rax
	adcx r14, rcx
	adox r14, rbp
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r14
	xor ebp, ebp
	movabs rax, -4294967295
	mulx rcx, rax, rax
	adox r8, rax
	adcx r9, rcx
	mov eax, -1
	mulx rcx, rax, rax
	adox r9, rax
	adcx r10, rcx
	adox r10, rdx
	mov r14d, 0
	adcx r11, rbp
	adox r11, rbp
	adcx r12, rbp
	adox r12, rbp
	adcx r13, rbp
	adox r13, rbp
	adcx r14, rbp
	adox r14, rbp
	sub r8, QWORD PTR [rdi+64]
	sbb r9, QWORD PTR [rdi+72]
	sbb r10, QWORD PTR [rdi+80]
	sbb r11, QWORD PTR [rdi+88]
	sbb r12, QWORD PTR [rdi+96]
	sbb r13, QWORD PTR [rdi+104]
	sbb r14, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+784], r8
	mov QWORD PTR [rdi+792], r9
	mov QWORD PTR [rdi+800], r10
	mov QWORD PTR [rdi+808], r11
	mov QWORD PTR [rdi+816], r12
	mov QWORD PTR [rdi+824], r13
	jmp 217f
216:
217:
	movzx r8d, BYTE PTR [rdi+rbx*1+3568]
	test r8, r8
	je 218f
	cmp r8, 128
	jb 220f
	mov eax, 256
	sub rax, r8
	mov r8, rax
	mov rax, r8
	sub rax, 1
	shr rax, 1
	mov ecx, 144
	mul rcx
	mov rdx, rdi
	add rdx, 4096
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu XMMWORD PTR [rdi+1024], xmm0
	movdqu xmm1, XMMWORD PTR [rdx+16]
	movdqu XMMWORD PTR [rdi+1040], xmm1
	movdqu xmm2, XMMWORD PTR [rdx+32]
	movdqu XMMWORD PTR [rdi+1056], xmm2
	movdqu xmm3, XMMWORD PTR [rdx+48]
	movdqu XMMWORD PTR [rdi+1072], xmm3
	movdqu xmm4, XMMWORD PTR [rdx+64]
	movdqu XMMWORD PTR [rdi+1088], xmm4
	movdqu xmm5, XMMWORD PTR [rdx+80]
	movdqu XMMWORD PTR [rdi+1104], xmm5
	movdqu xmm6, XMMWORD PTR [rdx+96]
	movdqu XMMWORD PTR [rdi+1120], xmm6
	movdqu xmm7, XMMWORD PTR [rdx+112]
	movdqu XMMWORD PTR [rdi+1136], xmm7
	movdqu xmm8, XMMWORD PTR [rdx+128]
	movdqu XMMWORD PTR [rdi+1152], xmm8
	mov rax, r8
	sub rax, 1
	mov ecx, 48
	mul rcx
	mov rdx, rdi
	add rdx, 5392
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu XMMWORD PTR [rdi+6160], xmm0
	movdqu xmm1, XMMWORD PTR [rdx+16]
	movdqu XMMWORD PTR [rdi+6176], xmm1
	movdqu xmm2, XMMWORD PTR [rdx+32]
	movdqu XMMWORD PTR [rdi+6192], xmm2
	movdqu xmm3, XMMWORD PTR [rdx+48]
	movdqu XMMWORD PTR [rdi+6208], xmm3
	movdqu xmm4, XMMWORD PTR [rdx+64]
	movdqu XMMWORD PTR [rdi+6224], xmm4
	movdqu xmm5, XMMWORD PTR [rdx+80]
	movdqu XMMWORD PTR [rdi+6240], xmm5
	mov r8, QWORD PTR [rdi+208]
	mov r9, QWORD PTR [rdi+216]
	mov r10, QWORD PTR [rdi+224]
	mov r11, QWORD PTR [rdi+232]
	mov r12, QWORD PTR [rdi+240]
	mov r13, QWORD PTR [rdi+248]
	sub r8, QWORD PTR [rdi+1072]
	sbb r9, QWORD PTR [rdi+1080]
	sbb r10, QWORD PTR [rdi+1088]
	sbb r11, QWORD PTR [rdi+1096]
	sbb r12, QWORD PTR [rdi+1104]
	sbb r13, QWORD PTR [rdi+1112]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1072], r8
	mov QWORD PTR [rdi+1080], r9
	mov QWORD PTR [rdi+1088], r10
	mov QWORD PTR [rdi+1096], r11
	mov QWORD PTR [rdi+1104], r12
	mov QWORD PTR [rdi+1112], r13
	jmp 221f
220:
	mov rax, r8
	sub rax, 1
	shr rax, 1
	mov ecx, 144
	mul rcx
	mov rdx, rdi
	add rdx, 4096
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu XMMWORD PTR [rdi+1024], xmm0
	movdqu xmm1, XMMWORD PTR [rdx+16]
	movdqu XMMWORD PTR [rdi+1040], xmm1
	movdqu xmm2, XMMWORD PTR [rdx+32]
	movdqu XMMWORD PTR [rdi+1056], xmm2
	movdqu xmm3, XMMWORD PTR [rdx+48]
	movdqu XMMWORD PTR [rdi+1072], xmm3
	movdqu xmm4, XMMWORD PTR [rdx+64]
	movdqu XMMWORD PTR [rdi+1088], xmm4
	movdqu xmm5, XMMWORD PTR [rdx+80]
	movdqu XMMWORD PTR [rdi+1104], xmm5
	movdqu xmm6, XMMWORD PTR [rdx+96]
	movdqu XMMWORD PTR [rdi+1120], xmm6
	movdqu xmm7, XMMWORD PTR [rdx+112]
	movdqu XMMWORD PTR [rdi+1136], xmm7
	movdqu xmm8, XMMWORD PTR [rdx+128]
	movdqu XMMWORD PTR [rdi+1152], xmm8
	mov rax, r8
	sub rax, 1
	mov ecx, 48
	mul rcx
	mov rdx, rdi
	add rdx, 5392
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu XMMWORD PTR [rdi+6160], xmm0
	movdqu xmm1, XMMWORD PTR [rdx+16]
	movdqu XMMWORD PTR [rdi+6176], xmm1
	movdqu xmm2, XMMWORD PTR [rdx+32]
	movdqu XMMWORD PTR [rdi+6192], xmm2
	movdqu xmm3, XMMWORD PTR [rdx+48]
	movdqu XMMWORD PTR [rdi+6208], xmm3
	movdqu xmm4, XMMWORD PTR [rdx+64]
	movdqu XMMWORD PTR [rdi+6224], xmm4
	movdqu xmm5, XMMWORD PTR [rdx+80]
	movdqu XMMWORD PTR [rdi+6240], xmm5
221:
	call {vg_p384_jac_add_cached_adx}
	jmp 219f
218:
219:
	movzx r8d, WORD PTR [rdi+rbx*2+6400]
	test r8, r8
	je 222f
	cmp r8, 256
	jb 224f
	mov eax, 65536
	sub rax, r8
	mov r8, rax
	mov rax, r8
	sub rax, 1
	mov ecx, 96
	mul rcx
	lea rdx, {VG_P384_GTAB}
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu XMMWORD PTR [rdi+1024], xmm0
	movdqu xmm1, XMMWORD PTR [rdx+16]
	movdqu XMMWORD PTR [rdi+1040], xmm1
	movdqu xmm2, XMMWORD PTR [rdx+32]
	movdqu XMMWORD PTR [rdi+1056], xmm2
	movdqu xmm3, XMMWORD PTR [rdx+48]
	movdqu XMMWORD PTR [rdi+1072], xmm3
	movdqu xmm4, XMMWORD PTR [rdx+64]
	movdqu XMMWORD PTR [rdi+1088], xmm4
	movdqu xmm5, XMMWORD PTR [rdx+80]
	movdqu XMMWORD PTR [rdi+1104], xmm5
	movabs rax, -4294967295
	mov QWORD PTR [rdi+1120], rax
	movabs rax, 4294967295
	mov QWORD PTR [rdi+1128], rax
	movabs rax, 1
	mov QWORD PTR [rdi+1136], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1144], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1152], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1160], rax
	mov r8, QWORD PTR [rdi+208]
	mov r9, QWORD PTR [rdi+216]
	mov r10, QWORD PTR [rdi+224]
	mov r11, QWORD PTR [rdi+232]
	mov r12, QWORD PTR [rdi+240]
	mov r13, QWORD PTR [rdi+248]
	sub r8, QWORD PTR [rdi+1072]
	sbb r9, QWORD PTR [rdi+1080]
	sbb r10, QWORD PTR [rdi+1088]
	sbb r11, QWORD PTR [rdi+1096]
	sbb r12, QWORD PTR [rdi+1104]
	sbb r13, QWORD PTR [rdi+1112]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1072], r8
	mov QWORD PTR [rdi+1080], r9
	mov QWORD PTR [rdi+1088], r10
	mov QWORD PTR [rdi+1096], r11
	mov QWORD PTR [rdi+1104], r12
	mov QWORD PTR [rdi+1112], r13
	jmp 225f
224:
	mov rax, r8
	sub rax, 1
	mov ecx, 96
	mul rcx
	lea rdx, {VG_P384_GTAB}
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu XMMWORD PTR [rdi+1024], xmm0
	movdqu xmm1, XMMWORD PTR [rdx+16]
	movdqu XMMWORD PTR [rdi+1040], xmm1
	movdqu xmm2, XMMWORD PTR [rdx+32]
	movdqu XMMWORD PTR [rdi+1056], xmm2
	movdqu xmm3, XMMWORD PTR [rdx+48]
	movdqu XMMWORD PTR [rdi+1072], xmm3
	movdqu xmm4, XMMWORD PTR [rdx+64]
	movdqu XMMWORD PTR [rdi+1088], xmm4
	movdqu xmm5, XMMWORD PTR [rdx+80]
	movdqu XMMWORD PTR [rdi+1104], xmm5
	movabs rax, -4294967295
	mov QWORD PTR [rdi+1120], rax
	movabs rax, 4294967295
	mov QWORD PTR [rdi+1128], rax
	movabs rax, 1
	mov QWORD PTR [rdi+1136], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1144], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1152], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1160], rax
225:
	call {vg_p384_jac_add_affine_adx}
	jmp 223f
222:
223:
	test rbx, rbx
	jne 215b
	mov r12, rsi
	mov esi, 832
	mov edx, 832
	mov ecx, 832
	call {vg_p384_mul_mod_p_adx}
	mov rsi, r12
	movabs rax, -8589934591
	mov QWORD PTR [rdi+1696], rax
	movabs rax, 8589934592
	mov QWORD PTR [rdi+1704], rax
	movabs rax, -8589934592
	mov QWORD PTR [rdi+1712], rax
	movabs rax, 8589934592
	mov QWORD PTR [rdi+1720], rax
	movabs rax, 1
	mov QWORD PTR [rdi+1728], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1736], rax
	movabs rax, 2316802901605165427
	mov QWORD PTR [rdi+1456], rax
	movabs rax, -2580967570294927855
	mov QWORD PTR [rdi+1464], rax
	movabs rax, 633002615215383305
	mov QWORD PTR [rdi+1472], rax
	movabs rax, 5499242126189750188
	mov QWORD PTR [rdi+1480], rax
	movabs rax, -4079331617873953950
	mov QWORD PTR [rdi+1488], rax
	movabs rax, -1
	mov QWORD PTR [rdi+1496], rax
	movabs rax, 1374695844057110156
	mov QWORD PTR [rdi+112], rax
	movabs rax, -6348401688401979259
	mov QWORD PTR [rdi+120], rax
	movabs rax, 4079331616924160543
	mov QWORD PTR [rdi+128], rax
	movabs rax, 0
	mov QWORD PTR [rdi+136], rax
	movabs rax, 0
	mov QWORD PTR [rdi+144], rax
	movabs rax, 0
	mov QWORD PTR [rdi+152], rax
	mov rdx, QWORD PTR [rdi+1552]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1696]
	mulx r10, rax, QWORD PTR [rdi+1704]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1712]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1720]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1728]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+1736]
	adcx r13, rax
	adcx r14, rbp
	mov r15d, 0
	movabs rdx, 4294967297
	imul rdx, r8
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r8, rcx
	add rax, r8
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r9, rax
	sbb r10, rcx
	sbb r11, rbp
	sbb r12, 0
	sbb r13, 0
	sbb rdx, 0
	add r14, rdx
	adc r15, 0
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+1560]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1696]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1704]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1712]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1720]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1728]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1736]
	adox r14, rax
	adcx r15, rcx
	adox r15, rbp
	adcx r8, rbp
	adox r8, rbp
	movabs rdx, 4294967297
	imul rdx, r9
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r9, rcx
	add rax, r9
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r10, rax
	sbb r11, rcx
	sbb r12, rbp
	sbb r13, 0
	sbb r14, 0
	sbb rdx, 0
	add r15, rdx
	adc r8, 0
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+1568]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1696]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1704]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1712]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1720]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1728]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1736]
	adox r15, rax
	adcx r8, rcx
	adox r8, rbp
	adcx r9, rbp
	adox r9, rbp
	movabs rdx, 4294967297
	imul rdx, r10
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r10, rcx
	add rax, r10
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r11, rax
	sbb r12, rcx
	sbb r13, rbp
	sbb r14, 0
	sbb r15, 0
	sbb rdx, 0
	add r8, rdx
	adc r9, 0
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+1576]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1696]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1704]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1712]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1720]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1728]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1736]
	adox r8, rax
	adcx r9, rcx
	adox r9, rbp
	adcx r10, rbp
	adox r10, rbp
	movabs rdx, 4294967297
	imul rdx, r11
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r11, rcx
	add rax, r11
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r12, rax
	sbb r13, rcx
	sbb r14, rbp
	sbb r15, 0
	sbb r8, 0
	sbb rdx, 0
	add r9, rdx
	adc r10, 0
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+1584]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1696]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1704]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1712]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1720]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1728]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1736]
	adox r9, rax
	adcx r10, rcx
	adox r10, rbp
	adcx r11, rbp
	adox r11, rbp
	movabs rdx, 4294967297
	imul rdx, r12
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r12, rcx
	add rax, r12
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r13, rax
	sbb r14, rcx
	sbb r15, rbp
	sbb r8, 0
	sbb r9, 0
	sbb rdx, 0
	add r10, rdx
	adc r11, 0
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+1592]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1696]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+1704]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+1712]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+1720]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+1728]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1736]
	adox r10, rax
	adcx r11, rcx
	adox r11, rbp
	adcx r12, rbp
	adox r12, rbp
	movabs rdx, 4294967297
	imul rdx, r13
	movabs rax, -4294967295
	mulx rax, rcx, rax
	mov ecx, -1
	mulx rcx, r13, rcx
	add rax, r13
	adc rcx, rdx
	mov ebp, 0
	adc rbp, rbp
	sub r14, rax
	sbb r15, rcx
	sbb r8, rbp
	sbb r9, 0
	sbb r10, 0
	sbb rdx, 0
	add r11, rdx
	adc r12, 0
	mov r13d, 0
	sub r14, QWORD PTR [rdi+64]
	sbb r15, QWORD PTR [rdi+72]
	sbb r8, QWORD PTR [rdi+80]
	sbb r9, QWORD PTR [rdi+88]
	sbb r10, QWORD PTR [rdi+96]
	sbb r11, QWORD PTR [rdi+104]
	sbb r12, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r14, rcx
	adc r15, rdx
	adc r8, rbp
	adc r9, rax
	adc r10, rax
	adc r11, rax
	mov QWORD PTR [rdi+1696], r14
	mov QWORD PTR [rdi+1704], r15
	mov QWORD PTR [rdi+1712], r8
	mov QWORD PTR [rdi+1720], r9
	mov QWORD PTR [rdi+1728], r10
	mov QWORD PTR [rdi+1736], r11
	mov r12, rsi
	mov esi, 1744
	mov edx, 1696
	mov ecx, 832
	call {vg_p384_mul_mod_p_adx}
	mov rsi, r12
	mov r8, QWORD PTR [rdi+736]
	mov r9, QWORD PTR [rdi+744]
	mov r10, QWORD PTR [rdi+752]
	mov r11, QWORD PTR [rdi+760]
	mov r12, QWORD PTR [rdi+768]
	mov r13, QWORD PTR [rdi+776]
	sub r8, QWORD PTR [rdi+1744]
	sbb r9, QWORD PTR [rdi+1752]
	sbb r10, QWORD PTR [rdi+1760]
	sbb r11, QWORD PTR [rdi+1768]
	sbb r12, QWORD PTR [rdi+1776]
	sbb r13, QWORD PTR [rdi+1784]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1984], r8
	mov QWORD PTR [rdi+1992], r9
	mov QWORD PTR [rdi+2000], r10
	mov QWORD PTR [rdi+2008], r11
	mov QWORD PTR [rdi+2016], r12
	mov QWORD PTR [rdi+2024], r13
	mov r8, QWORD PTR [rdi+1696]
	mov r9, QWORD PTR [rdi+1704]
	mov r10, QWORD PTR [rdi+1712]
	mov r11, QWORD PTR [rdi+1720]
	mov r12, QWORD PTR [rdi+1728]
	mov r13, QWORD PTR [rdi+1736]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1456]
	adc r9, QWORD PTR [rdi+1464]
	adc r10, QWORD PTR [rdi+1472]
	adc r11, QWORD PTR [rdi+1480]
	adc r12, QWORD PTR [rdi+1488]
	adc r13, QWORD PTR [rdi+1496]
	adc r14, 0
	sub r8, QWORD PTR [rdi+64]
	sbb r9, QWORD PTR [rdi+72]
	sbb r10, QWORD PTR [rdi+80]
	sbb r11, QWORD PTR [rdi+88]
	sbb r12, QWORD PTR [rdi+96]
	sbb r13, QWORD PTR [rdi+104]
	sbb r14, 0
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1696], r8
	mov QWORD PTR [rdi+1704], r9
	mov QWORD PTR [rdi+1712], r10
	mov QWORD PTR [rdi+1720], r11
	mov QWORD PTR [rdi+1728], r12
	mov QWORD PTR [rdi+1736], r13
	mov r12, rsi
	mov esi, 1744
	mov edx, 1696
	mov ecx, 832
	call {vg_p384_mul_mod_p_adx}
	mov rsi, r12
	mov r8, QWORD PTR [rdi+736]
	mov r9, QWORD PTR [rdi+744]
	mov r10, QWORD PTR [rdi+752]
	mov r11, QWORD PTR [rdi+760]
	mov r12, QWORD PTR [rdi+768]
	mov r13, QWORD PTR [rdi+776]
	sub r8, QWORD PTR [rdi+1744]
	sbb r9, QWORD PTR [rdi+1752]
	sbb r10, QWORD PTR [rdi+1760]
	sbb r11, QWORD PTR [rdi+1768]
	sbb r12, QWORD PTR [rdi+1776]
	sbb r13, QWORD PTR [rdi+1784]
	sbb rax, rax
	mov ecx, eax
	mov rdx, rax
	shl rdx, 32
	mov rbp, rax
	shl rbp, 1
	add r8, rcx
	adc r9, rdx
	adc r10, rbp
	adc r11, rax
	adc r12, rax
	adc r13, rax
	mov QWORD PTR [rdi+1888], r8
	mov QWORD PTR [rdi+1896], r9
	mov QWORD PTR [rdi+1904], r10
	mov QWORD PTR [rdi+1912], r11
	mov QWORD PTR [rdi+1920], r12
	mov QWORD PTR [rdi+1928], r13
	mov rdx, QWORD PTR [rdi+1984]
	or rdx, QWORD PTR [rdi+1992]
	or rdx, QWORD PTR [rdi+2000]
	or rdx, QWORD PTR [rdi+2008]
	or rdx, QWORD PTR [rdi+2016]
	or rdx, QWORD PTR [rdi+2024]
	cmp rdx, 1
	sbb rdx, rdx
	mov rbp, rdx
	mov rdx, QWORD PTR [rdi+1552]
	sub rdx, QWORD PTR [rdi+112]
	mov rdx, QWORD PTR [rdi+1560]
	sbb rdx, QWORD PTR [rdi+120]
	mov rdx, QWORD PTR [rdi+1568]
	sbb rdx, QWORD PTR [rdi+128]
	mov rdx, QWORD PTR [rdi+1576]
	sbb rdx, QWORD PTR [rdi+136]
	mov rdx, QWORD PTR [rdi+1584]
	sbb rdx, QWORD PTR [rdi+144]
	mov rdx, QWORD PTR [rdi+1592]
	sbb rdx, QWORD PTR [rdi+152]
	sbb rax, rax
	mov r12, rax
	mov rdx, QWORD PTR [rdi+1888]
	or rdx, QWORD PTR [rdi+1896]
	or rdx, QWORD PTR [rdi+1904]
	or rdx, QWORD PTR [rdi+1912]
	or rdx, QWORD PTR [rdi+1920]
	or rdx, QWORD PTR [rdi+1928]
	cmp rdx, 1
	sbb rdx, rdx
	and rdx, r12
	or rdx, rbp
	mov rax, QWORD PTR [rdi+2176]
	and rax, rdx
	mov QWORD PTR [rdi+2176], rax
	mov rdx, QWORD PTR [rdi+832]
	or rdx, QWORD PTR [rdi+840]
	or rdx, QWORD PTR [rdi+848]
	or rdx, QWORD PTR [rdi+856]
	or rdx, QWORD PTR [rdi+864]
	or rdx, QWORD PTR [rdi+872]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+2176]
	and rax, rdx
	mov QWORD PTR [rdi+2176], rax
	mov rax, QWORD PTR [rdi+2176]
	and rax, 1
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	ret
	.p2align 6
