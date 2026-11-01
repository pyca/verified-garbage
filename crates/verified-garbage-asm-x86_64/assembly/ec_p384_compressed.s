// The functions of `src/ec_p384_compressed.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_p384_compress_public_key:
	mov r8, rdx
	mov r9, rsi
	mov rcx, rsi
	add rcx, 1
	mov rsi, rcx
	mov rdx, rcx
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
	mov rcx, QWORD PTR [rdi+2176]
	mov rdx, QWORD PTR [rdi+1792]
	and rdx, 1
	add rdx, 2
	and rdx, rcx
	mov BYTE PTR [rsi], dl
	mov rax, QWORD PTR [rdi+1648]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+41], rax
	mov rax, QWORD PTR [rdi+1656]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+33], rax
	mov rax, QWORD PTR [rdi+1664]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+25], rax
	mov rax, QWORD PTR [rdi+1672]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+17], rax
	mov rax, QWORD PTR [rdi+1680]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+9], rax
	mov rax, QWORD PTR [rdi+1688]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+1], rax
	mov rax, rcx
	and rax, 1
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	ret
	.p2align 6

vg_ec_p384_decompress_public_key:
	mov r8, rdx
	mov r9, rsi
	mov rcx, rsi
	add rcx, 1
	mov rsi, rcx
	mov rdx, rcx
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
	movzx edx, BYTE PTR [r9]
	mov QWORD PTR [rdi+1600], rdx
	and rdx, -2
	xor rdx, 2
	cmp rdx, 1
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+2176]
	and rax, rdx
	mov QWORD PTR [rdi+2176], rax
	mov rdx, QWORD PTR [rdi+1648]
	sub rdx, QWORD PTR [rdi+64]
	mov rdx, QWORD PTR [rdi+1656]
	sbb rdx, QWORD PTR [rdi+72]
	mov rdx, QWORD PTR [rdi+1664]
	sbb rdx, QWORD PTR [rdi+80]
	mov rdx, QWORD PTR [rdi+1672]
	sbb rdx, QWORD PTR [rdi+88]
	mov rdx, QWORD PTR [rdi+1680]
	sbb rdx, QWORD PTR [rdi+96]
	mov rdx, QWORD PTR [rdi+1688]
	sbb rdx, QWORD PTR [rdi+104]
	sbb rax, rax
	mov rdx, rax
	mov rax, QWORD PTR [rdi+2176]
	and rax, rdx
	mov QWORD PTR [rdi+2176], rax
	mov r12, rsi
	mov esi, 1696
	mov edx, 1648
	mov ecx, 1936
	call {vg_p384_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2032
	mov edx, 1696
	mov ecx, 1696
	call {vg_p384_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2080
	mov edx, 2032
	mov ecx, 1696
	call {vg_p384_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2032
	mov edx, 352
	mov ecx, 1696
	call {vg_p384_mul_mod_p}
	mov rsi, r12
	mov r8, QWORD PTR [rdi+2080]
	mov r9, QWORD PTR [rdi+2088]
	mov r10, QWORD PTR [rdi+2096]
	mov r11, QWORD PTR [rdi+2104]
	mov r12, QWORD PTR [rdi+2112]
	mov r13, QWORD PTR [rdi+2120]
	mov r14d, 0
	add r8, QWORD PTR [rdi+2032]
	adc r9, QWORD PTR [rdi+2040]
	adc r10, QWORD PTR [rdi+2048]
	adc r11, QWORD PTR [rdi+2056]
	adc r12, QWORD PTR [rdi+2064]
	adc r13, QWORD PTR [rdi+2072]
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
	mov QWORD PTR [rdi+1888], r8
	mov QWORD PTR [rdi+1896], r9
	mov QWORD PTR [rdi+1904], r10
	mov QWORD PTR [rdi+1912], r11
	mov QWORD PTR [rdi+1920], r12
	mov QWORD PTR [rdi+1928], r13
	mov r8, QWORD PTR [rdi+1888]
	mov r9, QWORD PTR [rdi+1896]
	mov r10, QWORD PTR [rdi+1904]
	mov r11, QWORD PTR [rdi+1912]
	mov r12, QWORD PTR [rdi+1920]
	mov r13, QWORD PTR [rdi+1928]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1984]
	adc r9, QWORD PTR [rdi+1992]
	adc r10, QWORD PTR [rdi+2000]
	adc r11, QWORD PTR [rdi+2008]
	adc r12, QWORD PTR [rdi+2016]
	adc r13, QWORD PTR [rdi+2024]
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
	mov QWORD PTR [rdi+2080], r8
	mov QWORD PTR [rdi+2088], r9
	mov QWORD PTR [rdi+2096], r10
	mov QWORD PTR [rdi+2104], r11
	mov QWORD PTR [rdi+2112], r12
	mov QWORD PTR [rdi+2120], r13
	movabs rax, 1073741824
	mov QWORD PTR [rdi+640], rax
	movabs rax, -4611686019501129728
	mov QWORD PTR [rdi+648], rax
	movabs rax, -1
	mov QWORD PTR [rdi+656], rax
	movabs rax, -1
	mov QWORD PTR [rdi+664], rax
	movabs rax, -1
	mov QWORD PTR [rdi+672], rax
	movabs rax, 4611686018427387903
	mov QWORD PTR [rdi+680], rax
	mov ebx, 0
20:
	movzx eax, BYTE PTR [rdi+rbx*1+640]
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
	jne 20b
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+1456], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+1464], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+1472], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+1480], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+1488], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+1496], rax
	mov ebx, 384
21:
	sub rbx, 1
	mov rcx, QWORD PTR [rdi+1456]
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1464]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1472]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1480]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1488]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1496]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov r13, rbp
	mov QWORD PTR [rdi+4056], r8
	mov QWORD PTR [rdi+4064], r9
	mov rcx, QWORD PTR [rdi+1464]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1472]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1480]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1488]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1496]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov r14, rbp
	mov rcx, QWORD PTR [rdi+1472]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1480]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1488]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1496]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov r15, rbp
	mov rcx, QWORD PTR [rdi+1480]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1488]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1496]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov r8, rbp
	mov rcx, QWORD PTR [rdi+1488]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1496]
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
	mov rax, QWORD PTR [rdi+1456]
	mul rax
	mov QWORD PTR [rdi+4048], rax
	add rdx, QWORD PTR [rdi+4056]
	mov QWORD PTR [rdi+4056], rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1464]
	mul rax
	add rax, rbp
	adc rdx, 0
	add rax, QWORD PTR [rdi+4064]
	mov QWORD PTR [rdi+4064], rax
	adc r10, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1472]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc r12, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1480]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc r14, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1488]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc r8, rdx
	mov ebp, 0
	adc rbp, 0
	mov rax, QWORD PTR [rdi+1496]
	mul rax
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rcx, rdx
	mov ebp, 0
	adc rbp, 0
	mov QWORD PTR [rdi+1456], r13
	mov QWORD PTR [rdi+1464], r14
	mov QWORD PTR [rdi+1472], r15
	mov QWORD PTR [rdi+1480], r8
	mov QWORD PTR [rdi+1488], r9
	mov QWORD PTR [rdi+1496], rcx
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
	add r13, QWORD PTR [rdi+1456]
	adc r14, QWORD PTR [rdi+1464]
	adc r15, QWORD PTR [rdi+1472]
	adc r10, QWORD PTR [rdi+1480]
	adc r11, QWORD PTR [rdi+1488]
	adc r12, QWORD PTR [rdi+1496]
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
	mov QWORD PTR [rdi+1456], r13
	mov QWORD PTR [rdi+1464], r14
	mov QWORD PTR [rdi+1472], r15
	mov QWORD PTR [rdi+1480], r10
	mov QWORD PTR [rdi+1488], r11
	mov QWORD PTR [rdi+1496], r12
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov r14d, 0
	mov r15d, 0
	mov rcx, QWORD PTR [rdi+1456]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+2080]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2088]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2096]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2104]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2112]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2120]
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
	mov rcx, QWORD PTR [rdi+1464]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+2080]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2088]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2096]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2104]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2112]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2120]
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
	mov rcx, QWORD PTR [rdi+1472]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+2080]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2088]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2096]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2104]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2112]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2120]
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
	mov rcx, QWORD PTR [rdi+1480]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+2080]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2088]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2096]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2104]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2112]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2120]
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
	mov rcx, QWORD PTR [rdi+1488]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+2080]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2088]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2096]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2104]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2112]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2120]
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
	mov rcx, QWORD PTR [rdi+1496]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+2080]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2088]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r14, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2096]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r15, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2104]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2112]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+2120]
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
	mov QWORD PTR [rdi+1504], r14
	mov QWORD PTR [rdi+1512], r15
	mov QWORD PTR [rdi+1520], r8
	mov QWORD PTR [rdi+1528], r9
	mov QWORD PTR [rdi+1536], r10
	mov QWORD PTR [rdi+1544], r11
	movzx eax, BYTE PTR [rdi+rbx*1+3008]
	mov ecx, 0
	sub rcx, rax
	mov rax, QWORD PTR [rdi+1456]
	mov rdx, QWORD PTR [rdi+1504]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1456], rax
	mov rax, QWORD PTR [rdi+1464]
	mov rdx, QWORD PTR [rdi+1512]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1464], rax
	mov rax, QWORD PTR [rdi+1472]
	mov rdx, QWORD PTR [rdi+1520]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1472], rax
	mov rax, QWORD PTR [rdi+1480]
	mov rdx, QWORD PTR [rdi+1528]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1480], rax
	mov rax, QWORD PTR [rdi+1488]
	mov rdx, QWORD PTR [rdi+1536]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1488], rax
	mov rax, QWORD PTR [rdi+1496]
	mov rdx, QWORD PTR [rdi+1544]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1496], rax
	test rbx, rbx
	jne 21b
	mov r12, rsi
	mov esi, 1792
	mov edx, 1456
	mov ecx, 256
	call {vg_p384_mul_mod_p}
	mov rsi, r12
	mov r8, QWORD PTR [rdi+208]
	mov r9, QWORD PTR [rdi+216]
	mov r10, QWORD PTR [rdi+224]
	mov r11, QWORD PTR [rdi+232]
	mov r12, QWORD PTR [rdi+240]
	mov r13, QWORD PTR [rdi+248]
	sub r8, QWORD PTR [rdi+1792]
	sbb r9, QWORD PTR [rdi+1800]
	sbb r10, QWORD PTR [rdi+1808]
	sbb r11, QWORD PTR [rdi+1816]
	sbb r12, QWORD PTR [rdi+1824]
	sbb r13, QWORD PTR [rdi+1832]
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
	mov QWORD PTR [rdi+1840], r8
	mov QWORD PTR [rdi+1848], r9
	mov QWORD PTR [rdi+1856], r10
	mov QWORD PTR [rdi+1864], r11
	mov QWORD PTR [rdi+1872], r12
	mov QWORD PTR [rdi+1880], r13
	mov rdx, QWORD PTR [rdi+1792]
	xor rdx, QWORD PTR [rdi+1600]
	and rdx, 1
	mov ecx, 0
	sub rcx, rdx
	mov rax, QWORD PTR [rdi+1792]
	mov rdx, QWORD PTR [rdi+1840]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1792], rax
	mov rax, QWORD PTR [rdi+1800]
	mov rdx, QWORD PTR [rdi+1848]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1800], rax
	mov rax, QWORD PTR [rdi+1808]
	mov rdx, QWORD PTR [rdi+1856]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1808], rax
	mov rax, QWORD PTR [rdi+1816]
	mov rdx, QWORD PTR [rdi+1864]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1816], rax
	mov rax, QWORD PTR [rdi+1824]
	mov rdx, QWORD PTR [rdi+1872]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1824], rax
	mov rax, QWORD PTR [rdi+1832]
	mov rdx, QWORD PTR [rdi+1880]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1832], rax
	mov r12, rsi
	mov esi, 1744
	mov edx, 1792
	mov ecx, 1936
	call {vg_p384_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2032
	mov edx, 1744
	mov ecx, 1744
	call {vg_p384_mul_mod_p}
	mov rsi, r12
	mov r8, QWORD PTR [rdi+2032]
	mov r9, QWORD PTR [rdi+2040]
	mov r10, QWORD PTR [rdi+2048]
	mov r11, QWORD PTR [rdi+2056]
	mov r12, QWORD PTR [rdi+2064]
	mov r13, QWORD PTR [rdi+2072]
	sub r8, QWORD PTR [rdi+2080]
	sbb r9, QWORD PTR [rdi+2088]
	sbb r10, QWORD PTR [rdi+2096]
	sbb r11, QWORD PTR [rdi+2104]
	sbb r12, QWORD PTR [rdi+2112]
	sbb r13, QWORD PTR [rdi+2120]
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
	mov rdx, QWORD PTR [rdi+1888]
	or rdx, QWORD PTR [rdi+1896]
	or rdx, QWORD PTR [rdi+1904]
	or rdx, QWORD PTR [rdi+1912]
	or rdx, QWORD PTR [rdi+1920]
	or rdx, QWORD PTR [rdi+1928]
	cmp rdx, 1
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+2176]
	and rax, rdx
	mov QWORD PTR [rdi+2176], rax
	mov rdx, QWORD PTR [rdi+1792]
	xor rdx, QWORD PTR [rdi+1600]
	and rdx, 1
	mov ecx, 0
	sub rcx, rdx
	mov rdx, rcx
	xor rdx, -1
	mov rax, QWORD PTR [rdi+2176]
	and rax, rdx
	mov QWORD PTR [rdi+2176], rax
	mov rcx, QWORD PTR [rdi+2176]
	mov eax, 4
	and rax, rcx
	mov BYTE PTR [rsi], al
	mov rax, QWORD PTR [rdi+1648]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+41], rax
	mov rax, QWORD PTR [rdi+1656]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+33], rax
	mov rax, QWORD PTR [rdi+1664]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+25], rax
	mov rax, QWORD PTR [rdi+1672]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+17], rax
	mov rax, QWORD PTR [rdi+1680]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+9], rax
	mov rax, QWORD PTR [rdi+1688]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+1], rax
	mov rax, QWORD PTR [rdi+1792]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+89], rax
	mov rax, QWORD PTR [rdi+1800]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+81], rax
	mov rax, QWORD PTR [rdi+1808]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+73], rax
	mov rax, QWORD PTR [rdi+1816]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+65], rax
	mov rax, QWORD PTR [rdi+1824]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+57], rax
	mov rax, QWORD PTR [rdi+1832]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+49], rax
	mov rax, rcx
	and rax, 1
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	ret
	.p2align 6

vg_ec_p384_compress_public_key_adx:
	mov r8, rdx
	mov r9, rsi
	mov rcx, rsi
	add rcx, 1
	mov rsi, rcx
	mov rdx, rcx
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
	mov rcx, QWORD PTR [rdi+2176]
	mov rdx, QWORD PTR [rdi+1792]
	and rdx, 1
	add rdx, 2
	and rdx, rcx
	mov BYTE PTR [rsi], dl
	mov rax, QWORD PTR [rdi+1648]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+41], rax
	mov rax, QWORD PTR [rdi+1656]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+33], rax
	mov rax, QWORD PTR [rdi+1664]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+25], rax
	mov rax, QWORD PTR [rdi+1672]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+17], rax
	mov rax, QWORD PTR [rdi+1680]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+9], rax
	mov rax, QWORD PTR [rdi+1688]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+1], rax
	mov rax, rcx
	and rax, 1
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	ret
	.p2align 6

vg_ec_p384_decompress_public_key_adx:
	mov r8, rdx
	mov r9, rsi
	mov rcx, rsi
	add rcx, 1
	mov rsi, rcx
	mov rdx, rcx
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
	movzx edx, BYTE PTR [r9]
	mov QWORD PTR [rdi+1600], rdx
	and rdx, -2
	xor rdx, 2
	cmp rdx, 1
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+2176]
	and rax, rdx
	mov QWORD PTR [rdi+2176], rax
	mov rdx, QWORD PTR [rdi+1648]
	sub rdx, QWORD PTR [rdi+64]
	mov rdx, QWORD PTR [rdi+1656]
	sbb rdx, QWORD PTR [rdi+72]
	mov rdx, QWORD PTR [rdi+1664]
	sbb rdx, QWORD PTR [rdi+80]
	mov rdx, QWORD PTR [rdi+1672]
	sbb rdx, QWORD PTR [rdi+88]
	mov rdx, QWORD PTR [rdi+1680]
	sbb rdx, QWORD PTR [rdi+96]
	mov rdx, QWORD PTR [rdi+1688]
	sbb rdx, QWORD PTR [rdi+104]
	sbb rax, rax
	mov rdx, rax
	mov rax, QWORD PTR [rdi+2176]
	and rax, rdx
	mov QWORD PTR [rdi+2176], rax
	mov r12, rsi
	mov esi, 1696
	mov edx, 1648
	mov ecx, 1936
	call {vg_p384_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2032
	mov edx, 1696
	mov ecx, 1696
	call {vg_p384_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2080
	mov edx, 2032
	mov ecx, 1696
	call {vg_p384_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2032
	mov edx, 352
	mov ecx, 1696
	call {vg_p384_mul_mod_p_adx}
	mov rsi, r12
	mov r8, QWORD PTR [rdi+2080]
	mov r9, QWORD PTR [rdi+2088]
	mov r10, QWORD PTR [rdi+2096]
	mov r11, QWORD PTR [rdi+2104]
	mov r12, QWORD PTR [rdi+2112]
	mov r13, QWORD PTR [rdi+2120]
	mov r14d, 0
	add r8, QWORD PTR [rdi+2032]
	adc r9, QWORD PTR [rdi+2040]
	adc r10, QWORD PTR [rdi+2048]
	adc r11, QWORD PTR [rdi+2056]
	adc r12, QWORD PTR [rdi+2064]
	adc r13, QWORD PTR [rdi+2072]
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
	mov QWORD PTR [rdi+1888], r8
	mov QWORD PTR [rdi+1896], r9
	mov QWORD PTR [rdi+1904], r10
	mov QWORD PTR [rdi+1912], r11
	mov QWORD PTR [rdi+1920], r12
	mov QWORD PTR [rdi+1928], r13
	mov r8, QWORD PTR [rdi+1888]
	mov r9, QWORD PTR [rdi+1896]
	mov r10, QWORD PTR [rdi+1904]
	mov r11, QWORD PTR [rdi+1912]
	mov r12, QWORD PTR [rdi+1920]
	mov r13, QWORD PTR [rdi+1928]
	mov r14d, 0
	add r8, QWORD PTR [rdi+1984]
	adc r9, QWORD PTR [rdi+1992]
	adc r10, QWORD PTR [rdi+2000]
	adc r11, QWORD PTR [rdi+2008]
	adc r12, QWORD PTR [rdi+2016]
	adc r13, QWORD PTR [rdi+2024]
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
	mov QWORD PTR [rdi+2080], r8
	mov QWORD PTR [rdi+2088], r9
	mov QWORD PTR [rdi+2096], r10
	mov QWORD PTR [rdi+2104], r11
	mov QWORD PTR [rdi+2112], r12
	mov QWORD PTR [rdi+2120], r13
	movabs rax, 1073741824
	mov QWORD PTR [rdi+640], rax
	movabs rax, -4611686019501129728
	mov QWORD PTR [rdi+648], rax
	movabs rax, -1
	mov QWORD PTR [rdi+656], rax
	movabs rax, -1
	mov QWORD PTR [rdi+664], rax
	movabs rax, -1
	mov QWORD PTR [rdi+672], rax
	movabs rax, 4611686018427387903
	mov QWORD PTR [rdi+680], rax
	mov ebx, 0
20:
	movzx eax, BYTE PTR [rdi+rbx*1+640]
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
	jne 20b
	mov rax, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+1456], rax
	mov rax, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+1464], rax
	mov rax, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+1472], rax
	mov rax, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+1480], rax
	mov rax, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+1488], rax
	mov rax, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+1496], rax
	mov ebx, 384
21:
	sub rbx, 1
	mov rdx, QWORD PTR [rdi+1456]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1464]
	mulx r10, rax, QWORD PTR [rdi+1472]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1480]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1488]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+1496]
	adcx r12, rax
	adcx r13, rbp
	mov QWORD PTR [rdi+4056], r8
	mov QWORD PTR [rdi+4064], r9
	mov rdx, QWORD PTR [rdi+1464]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1472]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1480]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1488]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+1496]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+1472]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1480]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1488]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+1496]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, QWORD PTR [rdi+1480]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1488]
	adox r14, rax
	adcx r15, rcx
	mulx r8, rax, QWORD PTR [rdi+1496]
	adox r15, rax
	adcx r8, rbp
	adox r8, rbp
	mov rdx, QWORD PTR [rdi+1488]
	xor ebp, ebp
	mulx r9, rax, QWORD PTR [rdi+1496]
	adox r8, rax
	adcx r9, rbp
	adox r9, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+1456]
	mulx rcx, rax, rdx
	adcx rbp, rbp
	adox rbp, rax
	mov QWORD PTR [rdi+4048], rbp
	mov rdx, QWORD PTR [rdi+4056]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+4056], rdx
	mov rdx, QWORD PTR [rdi+1464]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+4064]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+4064], rdx
	adcx r10, r10
	adox r10, rcx
	mov rdx, QWORD PTR [rdi+1472]
	mulx rcx, rax, rdx
	adcx r11, r11
	adox r11, rax
	adcx r12, r12
	adox r12, rcx
	mov rdx, QWORD PTR [rdi+1480]
	mulx rcx, rax, rdx
	adcx r13, r13
	adox r13, rax
	adcx r14, r14
	adox r14, rcx
	mov rdx, QWORD PTR [rdi+1488]
	mulx rcx, rax, rdx
	adcx r15, r15
	adox r15, rax
	adcx r8, r8
	adox r8, rcx
	mov rdx, QWORD PTR [rdi+1496]
	mulx rcx, rax, rdx
	adcx r9, r9
	adox r9, rax
	mov edx, 0
	adcx rcx, rdx
	adox rcx, rdx
	mov QWORD PTR [rdi+1456], r13
	mov QWORD PTR [rdi+1464], r14
	mov QWORD PTR [rdi+1472], r15
	mov QWORD PTR [rdi+1480], r8
	mov QWORD PTR [rdi+1488], r9
	mov QWORD PTR [rdi+1496], rcx
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
	add r13, QWORD PTR [rdi+1456]
	adc r14, QWORD PTR [rdi+1464]
	adc r15, QWORD PTR [rdi+1472]
	adc r10, QWORD PTR [rdi+1480]
	adc r11, QWORD PTR [rdi+1488]
	adc r12, QWORD PTR [rdi+1496]
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
	mov QWORD PTR [rdi+1456], r13
	mov QWORD PTR [rdi+1464], r14
	mov QWORD PTR [rdi+1472], r15
	mov QWORD PTR [rdi+1480], r10
	mov QWORD PTR [rdi+1488], r11
	mov QWORD PTR [rdi+1496], r12
	mov rdx, QWORD PTR [rdi+1456]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+2080]
	mulx r10, rax, QWORD PTR [rdi+2088]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+2096]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+2104]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+2112]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+2120]
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
	mov rdx, QWORD PTR [rdi+1464]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+2080]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+2088]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+2096]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+2104]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+2112]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+2120]
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
	mov rdx, QWORD PTR [rdi+1472]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+2080]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+2088]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+2096]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+2104]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+2112]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+2120]
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
	mov rdx, QWORD PTR [rdi+1480]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+2080]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+2088]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+2096]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+2104]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+2112]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+2120]
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
	mov rdx, QWORD PTR [rdi+1488]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+2080]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+2088]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+2096]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+2104]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+2112]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+2120]
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
	mov rdx, QWORD PTR [rdi+1496]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+2080]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+2088]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+2096]
	adox r15, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+2104]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+2112]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+2120]
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
	mov QWORD PTR [rdi+1504], r14
	mov QWORD PTR [rdi+1512], r15
	mov QWORD PTR [rdi+1520], r8
	mov QWORD PTR [rdi+1528], r9
	mov QWORD PTR [rdi+1536], r10
	mov QWORD PTR [rdi+1544], r11
	movzx eax, BYTE PTR [rdi+rbx*1+3008]
	mov ecx, 0
	sub rcx, rax
	mov rax, QWORD PTR [rdi+1456]
	mov rdx, QWORD PTR [rdi+1504]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1456], rax
	mov rax, QWORD PTR [rdi+1464]
	mov rdx, QWORD PTR [rdi+1512]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1464], rax
	mov rax, QWORD PTR [rdi+1472]
	mov rdx, QWORD PTR [rdi+1520]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1472], rax
	mov rax, QWORD PTR [rdi+1480]
	mov rdx, QWORD PTR [rdi+1528]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1480], rax
	mov rax, QWORD PTR [rdi+1488]
	mov rdx, QWORD PTR [rdi+1536]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1488], rax
	mov rax, QWORD PTR [rdi+1496]
	mov rdx, QWORD PTR [rdi+1544]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1496], rax
	test rbx, rbx
	jne 21b
	mov r12, rsi
	mov esi, 1792
	mov edx, 1456
	mov ecx, 256
	call {vg_p384_mul_mod_p_adx}
	mov rsi, r12
	mov r8, QWORD PTR [rdi+208]
	mov r9, QWORD PTR [rdi+216]
	mov r10, QWORD PTR [rdi+224]
	mov r11, QWORD PTR [rdi+232]
	mov r12, QWORD PTR [rdi+240]
	mov r13, QWORD PTR [rdi+248]
	sub r8, QWORD PTR [rdi+1792]
	sbb r9, QWORD PTR [rdi+1800]
	sbb r10, QWORD PTR [rdi+1808]
	sbb r11, QWORD PTR [rdi+1816]
	sbb r12, QWORD PTR [rdi+1824]
	sbb r13, QWORD PTR [rdi+1832]
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
	mov QWORD PTR [rdi+1840], r8
	mov QWORD PTR [rdi+1848], r9
	mov QWORD PTR [rdi+1856], r10
	mov QWORD PTR [rdi+1864], r11
	mov QWORD PTR [rdi+1872], r12
	mov QWORD PTR [rdi+1880], r13
	mov rdx, QWORD PTR [rdi+1792]
	xor rdx, QWORD PTR [rdi+1600]
	and rdx, 1
	mov ecx, 0
	sub rcx, rdx
	mov rax, QWORD PTR [rdi+1792]
	mov rdx, QWORD PTR [rdi+1840]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1792], rax
	mov rax, QWORD PTR [rdi+1800]
	mov rdx, QWORD PTR [rdi+1848]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1800], rax
	mov rax, QWORD PTR [rdi+1808]
	mov rdx, QWORD PTR [rdi+1856]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1808], rax
	mov rax, QWORD PTR [rdi+1816]
	mov rdx, QWORD PTR [rdi+1864]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1816], rax
	mov rax, QWORD PTR [rdi+1824]
	mov rdx, QWORD PTR [rdi+1872]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1824], rax
	mov rax, QWORD PTR [rdi+1832]
	mov rdx, QWORD PTR [rdi+1880]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1832], rax
	mov r12, rsi
	mov esi, 1744
	mov edx, 1792
	mov ecx, 1936
	call {vg_p384_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2032
	mov edx, 1744
	mov ecx, 1744
	call {vg_p384_mul_mod_p_adx}
	mov rsi, r12
	mov r8, QWORD PTR [rdi+2032]
	mov r9, QWORD PTR [rdi+2040]
	mov r10, QWORD PTR [rdi+2048]
	mov r11, QWORD PTR [rdi+2056]
	mov r12, QWORD PTR [rdi+2064]
	mov r13, QWORD PTR [rdi+2072]
	sub r8, QWORD PTR [rdi+2080]
	sbb r9, QWORD PTR [rdi+2088]
	sbb r10, QWORD PTR [rdi+2096]
	sbb r11, QWORD PTR [rdi+2104]
	sbb r12, QWORD PTR [rdi+2112]
	sbb r13, QWORD PTR [rdi+2120]
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
	mov rdx, QWORD PTR [rdi+1888]
	or rdx, QWORD PTR [rdi+1896]
	or rdx, QWORD PTR [rdi+1904]
	or rdx, QWORD PTR [rdi+1912]
	or rdx, QWORD PTR [rdi+1920]
	or rdx, QWORD PTR [rdi+1928]
	cmp rdx, 1
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+2176]
	and rax, rdx
	mov QWORD PTR [rdi+2176], rax
	mov rdx, QWORD PTR [rdi+1792]
	xor rdx, QWORD PTR [rdi+1600]
	and rdx, 1
	mov ecx, 0
	sub rcx, rdx
	mov rdx, rcx
	xor rdx, -1
	mov rax, QWORD PTR [rdi+2176]
	and rax, rdx
	mov QWORD PTR [rdi+2176], rax
	mov rcx, QWORD PTR [rdi+2176]
	mov eax, 4
	and rax, rcx
	mov BYTE PTR [rsi], al
	mov rax, QWORD PTR [rdi+1648]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+41], rax
	mov rax, QWORD PTR [rdi+1656]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+33], rax
	mov rax, QWORD PTR [rdi+1664]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+25], rax
	mov rax, QWORD PTR [rdi+1672]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+17], rax
	mov rax, QWORD PTR [rdi+1680]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+9], rax
	mov rax, QWORD PTR [rdi+1688]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+1], rax
	mov rax, QWORD PTR [rdi+1792]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+89], rax
	mov rax, QWORD PTR [rdi+1800]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+81], rax
	mov rax, QWORD PTR [rdi+1808]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+73], rax
	mov rax, QWORD PTR [rdi+1816]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+65], rax
	mov rax, QWORD PTR [rdi+1824]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+57], rax
	mov rax, QWORD PTR [rdi+1832]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+49], rax
	mov rax, rcx
	and rax, 1
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	ret
	.p2align 6
