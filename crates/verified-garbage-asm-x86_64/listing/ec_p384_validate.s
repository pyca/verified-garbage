// The functions of `src/ec_p384_validate.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_p384_validate_public_key:
	mov r8, rsi
	mov r9, rdi
	mov rcx, rdi
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

vg_ec_p384_validate_public_key_adx:
	mov r8, rsi
	mov r9, rdi
	mov rcx, rdi
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
