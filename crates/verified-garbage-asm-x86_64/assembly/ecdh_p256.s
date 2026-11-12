// The functions of `src/ecdh_p256.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdh_p256_ifma:
	mov r8, rcx
	mov r9, rdx
	mov rcx, rsi
	add rdx, 1
	mov QWORD PTR [r8], rbx
	mov QWORD PTR [r8+8], rbp
	mov QWORD PTR [r8+16], r12
	mov QWORD PTR [r8+24], r13
	mov QWORD PTR [r8+32], r14
	mov QWORD PTR [r8+40], r15
	mov r14, rdi
	mov rdi, r8
	mov rax, QWORD PTR [rcx+24]
	bswap rax
	mov QWORD PTR [rdi+1056], rax
	mov rax, QWORD PTR [rcx+16]
	bswap rax
	mov QWORD PTR [rdi+1064], rax
	mov rax, QWORD PTR [rcx+8]
	bswap rax
	mov QWORD PTR [rdi+1072], rax
	mov rax, QWORD PTR [rcx]
	bswap rax
	mov QWORD PTR [rdi+1080], rax
	mov rax, QWORD PTR [rsi+24]
	bswap rax
	mov QWORD PTR [rdi+1088], rax
	mov rax, QWORD PTR [rsi+16]
	bswap rax
	mov QWORD PTR [rdi+1096], rax
	mov rax, QWORD PTR [rsi+8]
	bswap rax
	mov QWORD PTR [rdi+1104], rax
	mov rax, QWORD PTR [rsi]
	bswap rax
	mov QWORD PTR [rdi+1112], rax
	mov rax, QWORD PTR [rdx+24]
	bswap rax
	mov QWORD PTR [rdi+1120], rax
	mov rax, QWORD PTR [rdx+16]
	bswap rax
	mov QWORD PTR [rdi+1128], rax
	mov rax, QWORD PTR [rdx+8]
	bswap rax
	mov QWORD PTR [rdi+1136], rax
	mov rax, QWORD PTR [rdx]
	bswap rax
	mov QWORD PTR [rdi+1144], rax
	movabs rax, -1
	mov QWORD PTR [rdi+64], rax
	movabs rax, 4294967295
	mov QWORD PTR [rdi+72], rax
	movabs rax, 0
	mov QWORD PTR [rdi+80], rax
	movabs rax, -4294967295
	mov QWORD PTR [rdi+88], rax
	movabs rax, -884452912994769583
	mov QWORD PTR [rdi+96], rax
	movabs rax, -4834901526196019580
	mov QWORD PTR [rdi+104], rax
	movabs rax, -1
	mov QWORD PTR [rdi+112], rax
	movabs rax, -4294967296
	mov QWORD PTR [rdi+120], rax
	movabs rax, 0
	mov QWORD PTR [rdi+160], rax
	movabs rax, 0
	mov QWORD PTR [rdi+168], rax
	movabs rax, 0
	mov QWORD PTR [rdi+176], rax
	movabs rax, 0
	mov QWORD PTR [rdi+184], rax
	movabs rax, 1
	mov QWORD PTR [rdi+192], rax
	movabs rax, 0
	mov QWORD PTR [rdi+200], rax
	movabs rax, 0
	mov QWORD PTR [rdi+208], rax
	movabs rax, 0
	mov QWORD PTR [rdi+216], rax
	movabs rax, 1
	mov QWORD PTR [rdi+224], rax
	movabs rax, -4294967296
	mov QWORD PTR [rdi+232], rax
	movabs rax, -1
	mov QWORD PTR [rdi+240], rax
	movabs rax, 4294967294
	mov QWORD PTR [rdi+248], rax
	movabs rax, -4
	mov QWORD PTR [rdi+256], rax
	movabs rax, 17179869183
	mov QWORD PTR [rdi+264], rax
	movabs rax, 0
	mov QWORD PTR [rdi+272], rax
	movabs rax, -17179869180
	mov QWORD PTR [rdi+280], rax
	movabs rax, -8514444157349119585
	mov QWORD PTR [rdi+288], rax
	movabs rax, 490911490938540466
	mov QWORD PTR [rdi+296], rax
	movabs rax, -5699760509517853564
	mov QWORD PTR [rdi+304], rax
	movabs rax, -7741667585760569188
	mov QWORD PTR [rdi+312], rax
	movabs rax, 8784043285714375740
	mov QWORD PTR [rdi+320], rax
	movabs rax, 8483257759279461889
	mov QWORD PTR [rdi+328], rax
	movabs rax, 8789745728267363600
	mov QWORD PTR [rdi+336], rax
	movabs rax, 1770019616739251654
	mov QWORD PTR [rdi+344], rax
	movabs rax, -2453807210370345462
	mov QWORD PTR [rdi+352], rax
	movabs rax, -8409706061646666660
	mov QWORD PTR [rdi+360], rax
	movabs rax, -3249199208764148955
	mov QWORD PTR [rdi+368], rax
	movabs rax, -8830996915122840187
	mov QWORD PTR [rdi+376], rax
	movabs rax, -8996981949549908318
	mov QWORD PTR [rdi+384], rax
	movabs rax, 5087230966250696614
	mov QWORD PTR [rdi+392], rax
	movabs rax, 2901921493521525849
	mov QWORD PTR [rdi+400], rax
	movabs rax, 7413256579398063648
	mov QWORD PTR [rdi+408], rax
	movabs rax, 884452912994769583
	mov QWORD PTR [rdi+416], rax
	movabs rax, 4834901526196019579
	mov QWORD PTR [rdi+424], rax
	movabs rax, 0
	mov QWORD PTR [rdi+432], rax
	movabs rax, 4294967295
	mov QWORD PTR [rdi+440], rax
	movabs rax, -3
	mov QWORD PTR [rdi+448], rax
	movabs rax, 4294967295
	mov QWORD PTR [rdi+456], rax
	movabs rax, 0
	mov QWORD PTR [rdi+464], rax
	movabs rax, -4294967295
	mov QWORD PTR [rdi+472], rax
	movabs rax, -884452912994769585
	mov QWORD PTR [rdi+480], rax
	movabs rax, -4834901526196019580
	mov QWORD PTR [rdi+488], rax
	movabs rax, -1
	mov QWORD PTR [rdi+496], rax
	movabs rax, -4294967296
	mov QWORD PTR [rdi+504], rax
	movabs rax, 0
	mov QWORD PTR [rdi+512], rax
	movabs rax, 0
	mov QWORD PTR [rdi+520], rax
	movabs rax, 0
	mov QWORD PTR [rdi+528], rax
	movabs rax, 0
	mov QWORD PTR [rdi+536], rax
	movabs rax, 1
	mov QWORD PTR [rdi+544], rax
	movabs rax, -4294967296
	mov QWORD PTR [rdi+552], rax
	movabs rax, -1
	mov QWORD PTR [rdi+560], rax
	movabs rax, 4294967294
	mov QWORD PTR [rdi+568], rax
	movabs rax, 0
	mov QWORD PTR [rdi+576], rax
	movabs rax, 0
	mov QWORD PTR [rdi+584], rax
	movabs rax, 0
	mov QWORD PTR [rdi+592], rax
	movabs rax, 0
	mov QWORD PTR [rdi+600], rax
	movabs rax, -1
	mov QWORD PTR [rdi+1472], rax
	mov rsi, r14
	mov ebx, 0
20:
	movzx eax, BYTE PTR [rdi+rbx*1+1056]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1504], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1505], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1506], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1507], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1508], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1509], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1510], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1511], dl
	add rbx, 1
	cmp rbx, 32
	jne 20b
	mov ebx, 0
21:
	movzx eax, BYTE PTR [rdi+rbx*1+448]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1768], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1769], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1770], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1771], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1772], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1773], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1774], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1775], dl
	add rbx, 1
	cmp rbx, 32
	jne 21b
	mov ebx, 0
22:
	movzx eax, BYTE PTR [rdi+rbx*1+480]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2032], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2033], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2034], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2035], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2036], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2037], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2038], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2039], dl
	add rbx, 1
	cmp rbx, 32
	jne 22b
	movabs rax, 3
	mov QWORD PTR [rdi+1312], rax
	movabs rax, -17179869185
	mov QWORD PTR [rdi+1320], rax
	movabs rax, -2
	mov QWORD PTR [rdi+1328], rax
	movabs rax, 21474836477
	mov QWORD PTR [rdi+1336], rax
	movabs rax, -2838148052449706529
	mov QWORD PTR [rdi+1344], rax
	movabs rax, -5985277524727025520
	mov QWORD PTR [rdi+1352], rax
	movabs rax, -1899920169839284522
	mov QWORD PTR [rdi+1360], rax
	movabs rax, -2580555864783501260
	mov QWORD PTR [rdi+1368], rax
	mov rdx, r9
	add rdx, 33
	mov rax, QWORD PTR [rdx+24]
	bswap rax
	mov QWORD PTR [rdi+1216], rax
	mov rax, QWORD PTR [rdx+16]
	bswap rax
	mov QWORD PTR [rdi+1224], rax
	mov rax, QWORD PTR [rdx+8]
	bswap rax
	mov QWORD PTR [rdi+1232], rax
	mov rax, QWORD PTR [rdx]
	bswap rax
	mov QWORD PTR [rdi+1240], rax
	movzx edx, BYTE PTR [r9]
	xor rdx, 4
	cmp rdx, 1
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+1472]
	and rax, rdx
	mov QWORD PTR [rdi+1472], rax
	call {vg_p256_check_point_adx}
	movabs rax, -884452912994769583
	mov QWORD PTR [rdi+2336], rax
	movabs rax, -4834901526196019580
	mov QWORD PTR [rdi+2344], rax
	movabs rax, -1
	mov QWORD PTR [rdi+2352], rax
	movabs rax, -4294967296
	mov QWORD PTR [rdi+2360], rax
	mov r8, QWORD PTR [rdi+2336]
	sub r8, QWORD PTR [rdi+1056]
	mov QWORD PTR [rdi+2336], r8
	mov r8, QWORD PTR [rdi+2344]
	sbb r8, QWORD PTR [rdi+1064]
	mov QWORD PTR [rdi+2344], r8
	mov r8, QWORD PTR [rdi+2352]
	sbb r8, QWORD PTR [rdi+1072]
	mov QWORD PTR [rdi+2352], r8
	mov r8, QWORD PTR [rdi+2360]
	sbb r8, QWORD PTR [rdi+1080]
	mov QWORD PTR [rdi+2360], r8
	mov rcx, QWORD PTR [rdi+1056]
	and rcx, 1
	sub rcx, 1
	mov rax, QWORD PTR [rdi+1056]
	mov rdx, QWORD PTR [rdi+2336]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1056], rax
	mov rax, QWORD PTR [rdi+1064]
	mov rdx, QWORD PTR [rdi+2344]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1064], rax
	mov rax, QWORD PTR [rdi+1072]
	mov rdx, QWORD PTR [rdi+2352]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1072], rax
	mov rax, QWORD PTR [rdi+1080]
	mov rdx, QWORD PTR [rdi+2360]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1080], rax
	movabs rax, -1
	mov QWORD PTR [rdi+2336], rax
	movabs rax, -1
	mov QWORD PTR [rdi+2344], rax
	movabs rax, -1
	mov QWORD PTR [rdi+2352], rax
	movabs rax, -1
	mov QWORD PTR [rdi+2360], rax
	movabs rax, 15
	mov QWORD PTR [rdi+2368], rax
	mov r8, QWORD PTR [rdi+2336]
	add r8, QWORD PTR [rdi+1056]
	mov QWORD PTR [rdi+2336], r8
	mov r8, QWORD PTR [rdi+2344]
	adc r8, QWORD PTR [rdi+1064]
	mov QWORD PTR [rdi+2344], r8
	mov r8, QWORD PTR [rdi+2352]
	adc r8, QWORD PTR [rdi+1072]
	mov QWORD PTR [rdi+2352], r8
	mov r8, QWORD PTR [rdi+2360]
	adc r8, QWORD PTR [rdi+1080]
	mov QWORD PTR [rdi+2360], r8
	mov r8, QWORD PTR [rdi+2368]
	adc r8, 0
	mov QWORD PTR [rdi+2368], r8
	mov ebx, 0
23:
	movzx eax, BYTE PTR [rdi+rbx*1+2336]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2400], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2401], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2402], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2403], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2404], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2405], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2406], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2407], dl
	add rbx, 1
	cmp rbx, 40
	jne 23b
	mov rax, QWORD PTR [rdi+1280]
	mov QWORD PTR [rdi+5312], rax
	mov rax, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+5320], rax
	mov rax, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+5328], rax
	mov rax, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+5336], rax
	mov rax, QWORD PTR [rdi+1440]
	mov QWORD PTR [rdi+5344], rax
	mov rax, QWORD PTR [rdi+1448]
	mov QWORD PTR [rdi+5352], rax
	mov rax, QWORD PTR [rdi+1456]
	mov QWORD PTR [rdi+5360], rax
	mov rax, QWORD PTR [rdi+1464]
	mov QWORD PTR [rdi+5368], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+5376], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+5384], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+5392], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+5400], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+5408], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+5416], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+5424], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+5432], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+5440], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+5448], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+5456], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+5464], rax
	mov ebx, 1
	mov rax, rbx
	sub rax, 1
	mov ecx, 160
	mul rcx
	mov rdx, rdi
	add rdx, 2752
	add rdx, rax
	mov rax, QWORD PTR [rdi+5312]
	mov QWORD PTR [rdx], rax
	mov rax, QWORD PTR [rdi+5320]
	mov QWORD PTR [rdx+8], rax
	mov rax, QWORD PTR [rdi+5328]
	mov QWORD PTR [rdx+16], rax
	mov rax, QWORD PTR [rdi+5336]
	mov QWORD PTR [rdx+24], rax
	mov rax, QWORD PTR [rdi+5344]
	mov QWORD PTR [rdx+32], rax
	mov rax, QWORD PTR [rdi+5352]
	mov QWORD PTR [rdx+40], rax
	mov rax, QWORD PTR [rdi+5360]
	mov QWORD PTR [rdx+48], rax
	mov rax, QWORD PTR [rdi+5368]
	mov QWORD PTR [rdx+56], rax
	mov rax, QWORD PTR [rdi+5376]
	mov QWORD PTR [rdx+64], rax
	mov rax, QWORD PTR [rdi+5384]
	mov QWORD PTR [rdx+72], rax
	mov rax, QWORD PTR [rdi+5392]
	mov QWORD PTR [rdx+80], rax
	mov rax, QWORD PTR [rdi+5400]
	mov QWORD PTR [rdx+88], rax
	mov rax, QWORD PTR [rdi+5408]
	mov QWORD PTR [rdx+96], rax
	mov rax, QWORD PTR [rdi+5416]
	mov QWORD PTR [rdx+104], rax
	mov rax, QWORD PTR [rdi+5424]
	mov QWORD PTR [rdx+112], rax
	mov rax, QWORD PTR [rdi+5432]
	mov QWORD PTR [rdx+120], rax
	mov rax, QWORD PTR [rdi+5440]
	mov QWORD PTR [rdx+128], rax
	mov rax, QWORD PTR [rdi+5448]
	mov QWORD PTR [rdx+136], rax
	mov rax, QWORD PTR [rdi+5456]
	mov QWORD PTR [rdx+144], rax
	mov rax, QWORD PTR [rdi+5464]
	mov QWORD PTR [rdx+152], rax
	mov rdx, QWORD PTR [rdi+1280]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+1288]
	mulx r11, rax, QWORD PTR [rdi+1296]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1304]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+1288]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+1304]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+1296]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+1304]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+1280]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+1288]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+1296]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+1304]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+800], r12
	mov QWORD PTR [rdi+808], r13
	mov QWORD PTR [rdi+816], r14
	mov QWORD PTR [rdi+824], r15
	mov rdx, QWORD PTR [rdi+1440]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+1448]
	mulx r11, rax, QWORD PTR [rdi+1456]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1464]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+1448]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1456]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+1464]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+1456]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+1464]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+1440]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+1448]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+1456]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+1464]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+832], r12
	mov QWORD PTR [rdi+840], r13
	mov QWORD PTR [rdi+848], r14
	mov QWORD PTR [rdi+856], r15
	mov rdx, r12
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+840]
	mulx r11, rax, QWORD PTR [rdi+848]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+856]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, r13
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+856]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, r14
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+856]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+832]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+840]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+848]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, r15
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
	mov QWORD PTR [rdi+880], r14
	mov QWORD PTR [rdi+888], r15
	mov rdx, QWORD PTR [rdi+1280]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+832]
	mulx r10, rax, QWORD PTR [rdi+840]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+848]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+856]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+1288]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+856]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+1296]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+856]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+1304]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+856]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+896], r12
	mov QWORD PTR [rdi+904], r13
	mov QWORD PTR [rdi+912], r14
	mov QWORD PTR [rdi+920], r15
	mov r8, r12
	mov r9, r13
	mov r10, r14
	mov r11, r15
	mov r12d, 0
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+896], r8
	mov QWORD PTR [rdi+904], r9
	mov QWORD PTR [rdi+912], r10
	mov QWORD PTR [rdi+920], r11
	mov r8, r8
	mov r9, r9
	mov r10, r10
	mov r11, r11
	mov r12d, 0
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+896], r8
	mov QWORD PTR [rdi+904], r9
	mov QWORD PTR [rdi+912], r10
	mov QWORD PTR [rdi+920], r11
	mov r8, QWORD PTR [rdi+800]
	mov r9, QWORD PTR [rdi+808]
	mov r10, QWORD PTR [rdi+816]
	mov r11, QWORD PTR [rdi+824]
	sub r8, QWORD PTR [rdi+224]
	sbb r9, QWORD PTR [rdi+232]
	sbb r10, QWORD PTR [rdi+240]
	sbb r11, QWORD PTR [rdi+248]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+928], r8
	mov QWORD PTR [rdi+936], r9
	mov QWORD PTR [rdi+944], r10
	mov QWORD PTR [rdi+952], r11
	mov r8, r8
	mov r9, r9
	mov r10, r10
	mov r11, r11
	mov r12d, 0
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+960], r8
	mov QWORD PTR [rdi+968], r9
	mov QWORD PTR [rdi+976], r10
	mov QWORD PTR [rdi+984], r11
	mov r8, r8
	mov r9, r9
	mov r10, r10
	mov r11, r11
	mov r12d, 0
	add r8, QWORD PTR [rdi+928]
	adc r9, QWORD PTR [rdi+936]
	adc r10, QWORD PTR [rdi+944]
	adc r11, QWORD PTR [rdi+952]
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+928], r8
	mov QWORD PTR [rdi+936], r9
	mov QWORD PTR [rdi+944], r10
	mov QWORD PTR [rdi+952], r11
	mov rdx, r8
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+936]
	mulx r11, rax, QWORD PTR [rdi+944]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+952]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+936]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+944]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+952]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+944]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+952]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, r8
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+936]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+944]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+952]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+5312], r12
	mov QWORD PTR [rdi+5320], r13
	mov QWORD PTR [rdi+5328], r14
	mov QWORD PTR [rdi+5336], r15
	mov r8, r12
	mov r9, r13
	mov r10, r14
	mov r11, r15
	sub r8, QWORD PTR [rdi+896]
	sbb r9, QWORD PTR [rdi+904]
	sbb r10, QWORD PTR [rdi+912]
	sbb r11, QWORD PTR [rdi+920]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+5312], r8
	mov QWORD PTR [rdi+5320], r9
	mov QWORD PTR [rdi+5328], r10
	mov QWORD PTR [rdi+5336], r11
	mov r8, r8
	mov r9, r9
	mov r10, r10
	mov r11, r11
	sub r8, QWORD PTR [rdi+896]
	sbb r9, QWORD PTR [rdi+904]
	sbb r10, QWORD PTR [rdi+912]
	sbb r11, QWORD PTR [rdi+920]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+5312], r8
	mov QWORD PTR [rdi+5320], r9
	mov QWORD PTR [rdi+5328], r10
	mov QWORD PTR [rdi+5336], r11
	mov r8, QWORD PTR [rdi+896]
	mov r9, QWORD PTR [rdi+904]
	mov r10, QWORD PTR [rdi+912]
	mov r11, QWORD PTR [rdi+920]
	sub r8, QWORD PTR [rdi+5312]
	sbb r9, QWORD PTR [rdi+5320]
	sbb r10, QWORD PTR [rdi+5328]
	sbb r11, QWORD PTR [rdi+5336]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+960], r8
	mov QWORD PTR [rdi+968], r9
	mov QWORD PTR [rdi+976], r10
	mov QWORD PTR [rdi+984], r11
	mov rdx, QWORD PTR [rdi+928]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+960]
	mulx r10, rax, QWORD PTR [rdi+968]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+976]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+984]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+936]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+960]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+968]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+976]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+984]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+944]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+960]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+968]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+976]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+984]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+952]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+960]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+968]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+976]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+984]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+5344], r12
	mov QWORD PTR [rdi+5352], r13
	mov QWORD PTR [rdi+5360], r14
	mov QWORD PTR [rdi+5368], r15
	mov r8, QWORD PTR [rdi+864]
	mov r9, QWORD PTR [rdi+872]
	mov r10, QWORD PTR [rdi+880]
	mov r11, QWORD PTR [rdi+888]
	mov r12d, 0
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+864], r8
	mov QWORD PTR [rdi+872], r9
	mov QWORD PTR [rdi+880], r10
	mov QWORD PTR [rdi+888], r11
	mov r8, r8
	mov r9, r9
	mov r10, r10
	mov r11, r11
	mov r12d, 0
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+864], r8
	mov QWORD PTR [rdi+872], r9
	mov QWORD PTR [rdi+880], r10
	mov QWORD PTR [rdi+888], r11
	mov r8, r8
	mov r9, r9
	mov r10, r10
	mov r11, r11
	mov r12d, 0
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+864], r8
	mov QWORD PTR [rdi+872], r9
	mov QWORD PTR [rdi+880], r10
	mov QWORD PTR [rdi+888], r11
	mov r8, QWORD PTR [rdi+5344]
	mov r9, QWORD PTR [rdi+5352]
	mov r10, QWORD PTR [rdi+5360]
	mov r11, QWORD PTR [rdi+5368]
	sub r8, QWORD PTR [rdi+864]
	sbb r9, QWORD PTR [rdi+872]
	sbb r10, QWORD PTR [rdi+880]
	sbb r11, QWORD PTR [rdi+888]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+5344], r8
	mov QWORD PTR [rdi+5352], r9
	mov QWORD PTR [rdi+5360], r10
	mov QWORD PTR [rdi+5368], r11
	mov r8, QWORD PTR [rdi+1440]
	mov r9, QWORD PTR [rdi+1448]
	mov r10, QWORD PTR [rdi+1456]
	mov r11, QWORD PTR [rdi+1464]
	mov r12d, 0
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+5376], r8
	mov QWORD PTR [rdi+5384], r9
	mov QWORD PTR [rdi+5392], r10
	mov QWORD PTR [rdi+5400], r11
	mov rdx, r8
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+5384]
	mulx r11, rax, QWORD PTR [rdi+5392]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+5400]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+5384]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5392]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+5400]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+5392]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+5400]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, r8
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+5384]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+5392]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+5400]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+5408], r12
	mov QWORD PTR [rdi+5416], r13
	mov QWORD PTR [rdi+5424], r14
	mov QWORD PTR [rdi+5432], r15
	mov rdx, r12
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+5376]
	mulx r10, rax, QWORD PTR [rdi+5384]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+5392]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+5400]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, r13
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5376]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+5384]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+5392]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+5400]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, r14
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5376]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+5384]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+5392]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+5400]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, r15
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5376]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+5384]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+5392]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+5400]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+5440], r12
	mov QWORD PTR [rdi+5448], r13
	mov QWORD PTR [rdi+5456], r14
	mov QWORD PTR [rdi+5464], r15
	mov rax, QWORD PTR [rdi+5312]
	mov QWORD PTR [rdi+608], rax
	mov rax, QWORD PTR [rdi+5320]
	mov QWORD PTR [rdi+616], rax
	mov rax, QWORD PTR [rdi+5328]
	mov QWORD PTR [rdi+624], rax
	mov rax, QWORD PTR [rdi+5336]
	mov QWORD PTR [rdi+632], rax
	mov rax, QWORD PTR [rdi+5344]
	mov QWORD PTR [rdi+640], rax
	mov rax, QWORD PTR [rdi+5352]
	mov QWORD PTR [rdi+648], rax
	mov rax, QWORD PTR [rdi+5360]
	mov QWORD PTR [rdi+656], rax
	mov rax, QWORD PTR [rdi+5368]
	mov QWORD PTR [rdi+664], rax
	mov rax, QWORD PTR [rdi+896]
	mov QWORD PTR [rdi+5312], rax
	mov rax, QWORD PTR [rdi+904]
	mov QWORD PTR [rdi+5320], rax
	mov rax, QWORD PTR [rdi+912]
	mov QWORD PTR [rdi+5328], rax
	mov rax, QWORD PTR [rdi+920]
	mov QWORD PTR [rdi+5336], rax
	mov rax, QWORD PTR [rdi+864]
	mov QWORD PTR [rdi+5344], rax
	mov rax, QWORD PTR [rdi+872]
	mov QWORD PTR [rdi+5352], rax
	mov rax, QWORD PTR [rdi+880]
	mov QWORD PTR [rdi+5360], rax
	mov rax, QWORD PTR [rdi+888]
	mov QWORD PTR [rdi+5368], rax
24:
	add rbx, 1
	mov r8, QWORD PTR [rdi+608]
	mov r9, QWORD PTR [rdi+616]
	mov r10, QWORD PTR [rdi+624]
	mov r11, QWORD PTR [rdi+632]
	sub r8, QWORD PTR [rdi+5312]
	sbb r9, QWORD PTR [rdi+5320]
	sbb r10, QWORD PTR [rdi+5328]
	sbb r11, QWORD PTR [rdi+5336]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+800], r8
	mov QWORD PTR [rdi+808], r9
	mov QWORD PTR [rdi+816], r10
	mov QWORD PTR [rdi+824], r11
	mov rdx, r8
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+808]
	mulx r11, rax, QWORD PTR [rdi+816]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+824]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+808]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+816]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+824]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+816]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+824]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, r8
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+808]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+816]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+824]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+832], r12
	mov QWORD PTR [rdi+840], r13
	mov QWORD PTR [rdi+848], r14
	mov QWORD PTR [rdi+856], r15
	mov rdx, QWORD PTR [rdi+5376]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+800]
	mulx r10, rax, QWORD PTR [rdi+808]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+816]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+824]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+5384]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+808]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+816]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+824]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+5392]
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
	mov rdx, QWORD PTR [rdi+5400]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r11, rax
	adcx r12, rcx
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
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+5376], r12
	mov QWORD PTR [rdi+5384], r13
	mov QWORD PTR [rdi+5392], r14
	mov QWORD PTR [rdi+5400], r15
	mov rdx, QWORD PTR [rdi+608]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+832]
	mulx r10, rax, QWORD PTR [rdi+840]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+848]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+856]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+616]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+856]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+624]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+856]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+632]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+856]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+608], r12
	mov QWORD PTR [rdi+616], r13
	mov QWORD PTR [rdi+624], r14
	mov QWORD PTR [rdi+632], r15
	mov rdx, QWORD PTR [rdi+5312]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+832]
	mulx r10, rax, QWORD PTR [rdi+840]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+848]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+856]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+5320]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+856]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+5328]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+856]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+5336]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+856]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+896], r12
	mov QWORD PTR [rdi+904], r13
	mov QWORD PTR [rdi+912], r14
	mov QWORD PTR [rdi+920], r15
	mov r8, QWORD PTR [rdi+640]
	mov r9, QWORD PTR [rdi+648]
	mov r10, QWORD PTR [rdi+656]
	mov r11, QWORD PTR [rdi+664]
	sub r8, QWORD PTR [rdi+5344]
	sbb r9, QWORD PTR [rdi+5352]
	sbb r10, QWORD PTR [rdi+5360]
	sbb r11, QWORD PTR [rdi+5368]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+928], r8
	mov QWORD PTR [rdi+936], r9
	mov QWORD PTR [rdi+944], r10
	mov QWORD PTR [rdi+952], r11
	mov rdx, r8
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+936]
	mulx r11, rax, QWORD PTR [rdi+944]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+952]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+936]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+944]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+952]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+944]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+952]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, r8
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+936]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+944]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+952]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+960], r12
	mov QWORD PTR [rdi+968], r13
	mov QWORD PTR [rdi+976], r14
	mov QWORD PTR [rdi+984], r15
	mov r8, QWORD PTR [rdi+608]
	mov r9, QWORD PTR [rdi+616]
	mov r10, QWORD PTR [rdi+624]
	mov r11, QWORD PTR [rdi+632]
	sub r8, QWORD PTR [rdi+896]
	sbb r9, QWORD PTR [rdi+904]
	sbb r10, QWORD PTR [rdi+912]
	sbb r11, QWORD PTR [rdi+920]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+864], r8
	mov QWORD PTR [rdi+872], r9
	mov QWORD PTR [rdi+880], r10
	mov QWORD PTR [rdi+888], r11
	mov rdx, QWORD PTR [rdi+640]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+864]
	mulx r10, rax, QWORD PTR [rdi+872]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+880]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+888]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+648]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+872]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+880]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+888]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+656]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+872]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+880]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+888]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+664]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+872]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+880]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+888]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+640], r12
	mov QWORD PTR [rdi+648], r13
	mov QWORD PTR [rdi+656], r14
	mov QWORD PTR [rdi+664], r15
	mov r8, QWORD PTR [rdi+960]
	mov r9, QWORD PTR [rdi+968]
	mov r10, QWORD PTR [rdi+976]
	mov r11, QWORD PTR [rdi+984]
	sub r8, QWORD PTR [rdi+608]
	sbb r9, QWORD PTR [rdi+616]
	sbb r10, QWORD PTR [rdi+624]
	sbb r11, QWORD PTR [rdi+632]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+5312], r8
	mov QWORD PTR [rdi+5320], r9
	mov QWORD PTR [rdi+5328], r10
	mov QWORD PTR [rdi+5336], r11
	mov r8, r8
	mov r9, r9
	mov r10, r10
	mov r11, r11
	sub r8, QWORD PTR [rdi+896]
	sbb r9, QWORD PTR [rdi+904]
	sbb r10, QWORD PTR [rdi+912]
	sbb r11, QWORD PTR [rdi+920]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+5312], r8
	mov QWORD PTR [rdi+5320], r9
	mov QWORD PTR [rdi+5328], r10
	mov QWORD PTR [rdi+5336], r11
	mov r8, QWORD PTR [rdi+608]
	mov r9, QWORD PTR [rdi+616]
	mov r10, QWORD PTR [rdi+624]
	mov r11, QWORD PTR [rdi+632]
	sub r8, QWORD PTR [rdi+5312]
	sbb r9, QWORD PTR [rdi+5320]
	sbb r10, QWORD PTR [rdi+5328]
	sbb r11, QWORD PTR [rdi+5336]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+5344], r8
	mov QWORD PTR [rdi+5352], r9
	mov QWORD PTR [rdi+5360], r10
	mov QWORD PTR [rdi+5368], r11
	mov rdx, QWORD PTR [rdi+928]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+5344]
	mulx r10, rax, QWORD PTR [rdi+5352]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+5360]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+5368]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+936]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5344]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+5352]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+5360]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+5368]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+944]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5344]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+5352]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+5360]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+5368]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+952]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5344]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+5352]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+5360]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+5368]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+5344], r12
	mov QWORD PTR [rdi+5352], r13
	mov QWORD PTR [rdi+5360], r14
	mov QWORD PTR [rdi+5368], r15
	mov r8, r12
	mov r9, r13
	mov r10, r14
	mov r11, r15
	sub r8, QWORD PTR [rdi+640]
	sbb r9, QWORD PTR [rdi+648]
	sbb r10, QWORD PTR [rdi+656]
	sbb r11, QWORD PTR [rdi+664]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+5344], r8
	mov QWORD PTR [rdi+5352], r9
	mov QWORD PTR [rdi+5360], r10
	mov QWORD PTR [rdi+5368], r11
	mov rdx, QWORD PTR [rdi+5408]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+832]
	mulx r10, rax, QWORD PTR [rdi+840]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+848]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+856]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+5416]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+856]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+5424]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+856]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+5432]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+856]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+5408], r12
	mov QWORD PTR [rdi+5416], r13
	mov QWORD PTR [rdi+5424], r14
	mov QWORD PTR [rdi+5432], r15
	mov rdx, r12
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+5376]
	mulx r10, rax, QWORD PTR [rdi+5384]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+5392]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+5400]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, r13
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5376]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+5384]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+5392]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+5400]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, r14
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5376]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+5384]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+5392]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+5400]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, r15
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5376]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+5384]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+5392]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+5400]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+5440], r12
	mov QWORD PTR [rdi+5448], r13
	mov QWORD PTR [rdi+5456], r14
	mov QWORD PTR [rdi+5464], r15
	mov rax, rbx
	sub rax, 1
	mov ecx, 160
	mul rcx
	mov rdx, rdi
	add rdx, 2752
	add rdx, rax
	mov rax, QWORD PTR [rdi+5312]
	mov QWORD PTR [rdx], rax
	mov rax, QWORD PTR [rdi+5320]
	mov QWORD PTR [rdx+8], rax
	mov rax, QWORD PTR [rdi+5328]
	mov QWORD PTR [rdx+16], rax
	mov rax, QWORD PTR [rdi+5336]
	mov QWORD PTR [rdx+24], rax
	mov rax, QWORD PTR [rdi+5344]
	mov QWORD PTR [rdx+32], rax
	mov rax, QWORD PTR [rdi+5352]
	mov QWORD PTR [rdx+40], rax
	mov rax, QWORD PTR [rdi+5360]
	mov QWORD PTR [rdx+48], rax
	mov rax, QWORD PTR [rdi+5368]
	mov QWORD PTR [rdx+56], rax
	mov rax, QWORD PTR [rdi+5376]
	mov QWORD PTR [rdx+64], rax
	mov rax, QWORD PTR [rdi+5384]
	mov QWORD PTR [rdx+72], rax
	mov rax, QWORD PTR [rdi+5392]
	mov QWORD PTR [rdx+80], rax
	mov rax, QWORD PTR [rdi+5400]
	mov QWORD PTR [rdx+88], rax
	mov rax, QWORD PTR [rdi+5408]
	mov QWORD PTR [rdx+96], rax
	mov rax, QWORD PTR [rdi+5416]
	mov QWORD PTR [rdx+104], rax
	mov rax, QWORD PTR [rdi+5424]
	mov QWORD PTR [rdx+112], rax
	mov rax, QWORD PTR [rdi+5432]
	mov QWORD PTR [rdx+120], rax
	mov rax, QWORD PTR [rdi+5440]
	mov QWORD PTR [rdx+128], rax
	mov rax, QWORD PTR [rdi+5448]
	mov QWORD PTR [rdx+136], rax
	mov rax, QWORD PTR [rdi+5456]
	mov QWORD PTR [rdx+144], rax
	mov rax, QWORD PTR [rdi+5464]
	mov QWORD PTR [rdx+152], rax
	cmp rbx, 16
	jne 24b
	stmxcsr DWORD PTR [rdi+5472]
	mov r12d, DWORD PTR [rdi+5472]
	and r12d, 65535
	mov eax, 8127
	mov DWORD PTR [rdi+5476], eax
	ldmxcsr DWORD PTR [rdi+5476]
	lfence
	movabs rax, 0
	mov QWORD PTR [rdi+6400], rax
	movabs rax, -1
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
	movabs rax, -1
	mov QWORD PTR [rdi+6456], rax
	movabs rax, 4503599627370416
	mov QWORD PTR [rdi+6464], rax
	movabs rax, 4503599627370416
	mov QWORD PTR [rdi+6472], rax
	movabs rax, 4503599627370416
	mov QWORD PTR [rdi+6480], rax
	movabs rax, 4503599627370400
	mov QWORD PTR [rdi+6488], rax
	movabs rax, 1407374883553279
	mov QWORD PTR [rdi+6496], rax
	movabs rax, 1407374883553279
	mov QWORD PTR [rdi+6504], rax
	movabs rax, 1407374883553279
	mov QWORD PTR [rdi+6512], rax
	movabs rax, 1688849860263935
	mov QWORD PTR [rdi+6520], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6528], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6536], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6544], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6552], rax
	movabs rax, 5497558138880
	mov QWORD PTR [rdi+6560], rax
	movabs rax, 5497558138880
	mov QWORD PTR [rdi+6568], rax
	movabs rax, 5497558138880
	mov QWORD PTR [rdi+6576], rax
	movabs rax, 6597069766656
	mov QWORD PTR [rdi+6584], rax
	movabs rax, 22517998131609600
	mov QWORD PTR [rdi+6592], rax
	movabs rax, 22517998131609600
	mov QWORD PTR [rdi+6600], rax
	movabs rax, 22517998131609600
	mov QWORD PTR [rdi+6608], rax
	movabs rax, 27021597757931520
	mov QWORD PTR [rdi+6616], rax
	movabs rax, 281474976710655
	mov QWORD PTR [rdi+6624], rax
	movabs rax, 281474976710655
	mov QWORD PTR [rdi+6632], rax
	movabs rax, 281474976710655
	mov QWORD PTR [rdi+6640], rax
	movabs rax, 281474976710655
	mov QWORD PTR [rdi+6648], rax
	movabs rax, 4503599627370495
	mov QWORD PTR [rdi+6656], rax
	movabs rax, 4503599627370495
	mov QWORD PTR [rdi+6664], rax
	movabs rax, 4503599627370495
	mov QWORD PTR [rdi+6672], rax
	movabs rax, 4503599627370495
	mov QWORD PTR [rdi+6680], rax
	movabs rax, 68719476736
	mov QWORD PTR [rdi+6688], rax
	movabs rax, 68719476736
	mov QWORD PTR [rdi+6696], rax
	movabs rax, 68719476736
	mov QWORD PTR [rdi+6704], rax
	movabs rax, 68719476736
	mov QWORD PTR [rdi+6712], rax
	movabs rax, 281474976645120
	mov QWORD PTR [rdi+6720], rax
	movabs rax, 281474976645120
	mov QWORD PTR [rdi+6728], rax
	movabs rax, 281474976645120
	mov QWORD PTR [rdi+6736], rax
	movabs rax, 281474976645120
	mov QWORD PTR [rdi+6744], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6752], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6760], rax
	movabs rax, -1
	mov QWORD PTR [rdi+6768], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6776], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6784], rax
	movabs rax, 4503599627370486
	mov QWORD PTR [rdi+6792], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6800], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6808], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6816], rax
	movabs rax, 175921860444159
	mov QWORD PTR [rdi+6824], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6832], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6840], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6848], rax
	movabs rax, 687194767360
	mov QWORD PTR [rdi+6856], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6864], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6872], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6880], rax
	movabs rax, 2814749766451200
	mov QWORD PTR [rdi+6888], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6896], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6904], rax
	movabs rax, -1
	mov QWORD PTR [rdi+6912], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6920], rax
	movabs rax, -1
	mov QWORD PTR [rdi+6928], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6936], rax
	movabs rax, 4503599627370296
	mov QWORD PTR [rdi+6944], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6952], rax
	movabs rax, 4503599627370296
	mov QWORD PTR [rdi+6960], rax
	movabs rax, 4503599627370491
	mov QWORD PTR [rdi+6968], rax
	movabs rax, 3518437208883199
	mov QWORD PTR [rdi+6976], rax
	movabs rax, 0
	mov QWORD PTR [rdi+6984], rax
	movabs rax, 3518437208883199
	mov QWORD PTR [rdi+6992], rax
	movabs rax, 87960930222079
	mov QWORD PTR [rdi+7000], rax
	movabs rax, 13743895347200
	mov QWORD PTR [rdi+7008], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7016], rax
	movabs rax, 13743895347200
	mov QWORD PTR [rdi+7024], rax
	movabs rax, 343597383680
	mov QWORD PTR [rdi+7032], rax
	movabs rax, 56294995329024000
	mov QWORD PTR [rdi+7040], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7048], rax
	movabs rax, 56294995329024000
	mov QWORD PTR [rdi+7056], rax
	movabs rax, 1407374883225600
	mov QWORD PTR [rdi+7064], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7072], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7080], rax
	movabs rax, -1
	mov QWORD PTR [rdi+7088], rax
	movabs rax, -1
	mov QWORD PTR [rdi+7096], rax
	movabs rax, -1
	mov QWORD PTR [rdi+7104], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7112], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7120], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7128], rax
	movabs rax, 4503599627370476
	mov QWORD PTR [rdi+7136], rax
	movabs rax, 4503599627370493
	mov QWORD PTR [rdi+7144], rax
	movabs rax, 4503599627370493
	mov QWORD PTR [rdi+7152], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7160], rax
	movabs rax, 351843720888319
	mov QWORD PTR [rdi+7168], rax
	movabs rax, 52776558133247
	mov QWORD PTR [rdi+7176], rax
	movabs rax, 52776558133247
	mov QWORD PTR [rdi+7184], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7192], rax
	movabs rax, 1374389534720
	mov QWORD PTR [rdi+7200], rax
	movabs rax, 206158430208
	mov QWORD PTR [rdi+7208], rax
	movabs rax, 206158430208
	mov QWORD PTR [rdi+7216], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7224], rax
	movabs rax, 5629499532902400
	mov QWORD PTR [rdi+7232], rax
	movabs rax, 844424929935360
	mov QWORD PTR [rdi+7240], rax
	movabs rax, 844424929935360
	mov QWORD PTR [rdi+7248], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7256], rax
	movabs rax, 4503599627370494
	mov QWORD PTR [rdi+7264], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7272], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7280], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7288], rax
	movabs rax, 35184372088831
	mov QWORD PTR [rdi+7296], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7304], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7312], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7320], rax
	movabs rax, 137438953472
	mov QWORD PTR [rdi+7328], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7336], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7344], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7352], rax
	movabs rax, 562949953290240
	mov QWORD PTR [rdi+7360], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7368], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7376], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7384], rax
	movabs rax, 4503599627370494
	mov QWORD PTR [rdi+7392], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7400], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7408], rax
	movabs rax, 4503599627370483
	mov QWORD PTR [rdi+7416], rax
	movabs rax, 35184372088831
	mov QWORD PTR [rdi+7424], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7432], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7440], rax
	movabs rax, 228698418577407
	mov QWORD PTR [rdi+7448], rax
	movabs rax, 137438953472
	mov QWORD PTR [rdi+7456], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7464], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7472], rax
	movabs rax, 893353197568
	mov QWORD PTR [rdi+7480], rax
	movabs rax, 562949953290240
	mov QWORD PTR [rdi+7488], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7496], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7504], rax
	movabs rax, 3659174696386560
	mov QWORD PTR [rdi+7512], rax
	movabs rax, 4503599627370476
	mov QWORD PTR [rdi+7520], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7528], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7536], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7544], rax
	movabs rax, 351843720888319
	mov QWORD PTR [rdi+7552], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7560], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7568], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7576], rax
	movabs rax, 1374389534720
	mov QWORD PTR [rdi+7584], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7592], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7600], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7608], rax
	movabs rax, 5629499532902400
	mov QWORD PTR [rdi+7616], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7624], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7632], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7640], rax
	movabs rax, 4
	mov QWORD PTR [rdi+7648], rax
	movabs rax, 2
	mov QWORD PTR [rdi+7656], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7664], rax
	movabs rax, 4
	mov QWORD PTR [rdi+7672], rax
	movabs rax, 4433230883192832
	mov QWORD PTR [rdi+7680], rax
	movabs rax, 4468415255281664
	mov QWORD PTR [rdi+7688], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7696], rax
	movabs rax, 4433230883192832
	mov QWORD PTR [rdi+7704], rax
	movabs rax, 4503599627370495
	mov QWORD PTR [rdi+7712], rax
	movabs rax, 4503599627370495
	mov QWORD PTR [rdi+7720], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7728], rax
	movabs rax, 4503599627370495
	mov QWORD PTR [rdi+7736], rax
	movabs rax, 4503324749463551
	mov QWORD PTR [rdi+7744], rax
	movabs rax, 4503462188417023
	mov QWORD PTR [rdi+7752], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7760], rax
	movabs rax, 4503324749463551
	mov QWORD PTR [rdi+7768], rax
	movabs rax, 262143
	mov QWORD PTR [rdi+7776], rax
	movabs rax, 131071
	mov QWORD PTR [rdi+7784], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7792], rax
	movabs rax, 262143
	mov QWORD PTR [rdi+7800], rax
	movabs rax, 4
	mov QWORD PTR [rdi+7808], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7816], rax
	movabs rax, 8
	mov QWORD PTR [rdi+7824], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7832], rax
	movabs rax, 4433230883192832
	mov QWORD PTR [rdi+7840], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7848], rax
	movabs rax, 4362862139015168
	mov QWORD PTR [rdi+7856], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7864], rax
	movabs rax, 4503599627370495
	mov QWORD PTR [rdi+7872], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7880], rax
	movabs rax, 4503599627370495
	mov QWORD PTR [rdi+7888], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7896], rax
	movabs rax, 4503324749463551
	mov QWORD PTR [rdi+7904], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7912], rax
	movabs rax, 4503049871556607
	mov QWORD PTR [rdi+7920], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7928], rax
	movabs rax, 262143
	mov QWORD PTR [rdi+7936], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7944], rax
	movabs rax, 524287
	mov QWORD PTR [rdi+7952], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7960], rax
	movabs rax, 2
	mov QWORD PTR [rdi+7968], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7976], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7984], rax
	movabs rax, 0
	mov QWORD PTR [rdi+7992], rax
	movabs rax, 4468415255281664
	mov QWORD PTR [rdi+8000], rax
	movabs rax, 0
	mov QWORD PTR [rdi+8008], rax
	movabs rax, 0
	mov QWORD PTR [rdi+8016], rax
	movabs rax, 0
	mov QWORD PTR [rdi+8024], rax
	movabs rax, 4503599627370495
	mov QWORD PTR [rdi+8032], rax
	movabs rax, 0
	mov QWORD PTR [rdi+8040], rax
	movabs rax, 0
	mov QWORD PTR [rdi+8048], rax
	movabs rax, 0
	mov QWORD PTR [rdi+8056], rax
	movabs rax, 4503462188417023
	mov QWORD PTR [rdi+8064], rax
	movabs rax, 0
	mov QWORD PTR [rdi+8072], rax
	movabs rax, 0
	mov QWORD PTR [rdi+8080], rax
	movabs rax, 0
	mov QWORD PTR [rdi+8088], rax
	movabs rax, 131071
	mov QWORD PTR [rdi+8096], rax
	movabs rax, 0
	mov QWORD PTR [rdi+8104], rax
	movabs rax, 0
	mov QWORD PTR [rdi+8112], rax
	movabs rax, 0
	mov QWORD PTR [rdi+8120], rax
	movabs rax, -1
	mov QWORD PTR [rdi+8128], rax
	movabs rax, -1
	mov QWORD PTR [rdi+8136], rax
	movabs rax, 0
	mov QWORD PTR [rdi+8144], rax
	movabs rax, 0
	mov QWORD PTR [rdi+8152], rax
	mov r10, rdi
	add r10, 6400
	mov r9, r10
	add r9, 128
	mov rcx, rdi
	add rcx, 2752
	mov rdx, rdi
	add rdx, 2848
	mov ebx, 51
	add rdi, 992
	vpxorq ymm0, ymm0, ymm0
	vpxorq ymm1, ymm1, ymm1
	vpxorq ymm2, ymm2, ymm2
	vpxorq ymm3, ymm3, ymm3
	vpxorq ymm4, ymm4, ymm4
	vpxorq ymm5, ymm5, ymm5
	vpxorq ymm6, ymm6, ymm6
	vpxorq ymm7, ymm7, ymm7
	vpxorq ymm8, ymm8, ymm8
	vpxorq ymm9, ymm9, ymm9
	vpxorq ymm10, ymm10, ymm10
	vpxorq ymm11, ymm11, ymm11
	vpxorq ymm12, ymm12, ymm12
	vpxorq ymm13, ymm13, ymm13
	vpxorq ymm14, ymm14, ymm14
	vpxorq ymm15, ymm15, ymm15
	vpxorq ymm16, ymm16, ymm16
	vpxorq ymm17, ymm17, ymm17
	vpxorq ymm18, ymm18, ymm18
	vpxorq ymm19, ymm19, ymm19
	vmovdqu64 ymm31, YMMWORD PTR [rcx]
	vmovdqu64 ymm30, YMMWORD PTR [rcx+32]
	vmovdqu64 ymm29, YMMWORD PTR [rcx+64]
	vmovdqu64 ymm28, YMMWORD PTR [rdx]
	vmovdqu64 ymm27, YMMWORD PTR [rdx+32]
	vpermq ymm26, ymm28, 0
	vpermq ymm25, ymm31, 0
	vmovdqu64 ymm24, YMMWORD PTR [r10]
	vpternlogq ymm26, ymm25, ymm24, 216
	vpermq ymm25, ymm29, 0
	vmovdqu64 ymm24, YMMWORD PTR [r10+352]
	vpternlogq ymm26, ymm25, ymm24, 216
	vpermq ymm25, ymm30, 0
	vmovdqu64 ymm24, YMMWORD PTR [r10+32]
	vpternlogq ymm26, ymm25, ymm24, 216
	vpermq ymm25, ymm28, 85
	vpermq ymm24, ymm31, 85
	vmovdqu64 ymm23, YMMWORD PTR [r10]
	vpternlogq ymm25, ymm24, ymm23, 216
	vpermq ymm24, ymm29, 85
	vmovdqu64 ymm23, YMMWORD PTR [r10+352]
	vpternlogq ymm25, ymm24, ymm23, 216
	vpermq ymm24, ymm30, 85
	vmovdqu64 ymm23, YMMWORD PTR [r10+32]
	vpternlogq ymm25, ymm24, ymm23, 216
	vpermq ymm24, ymm28, 170
	vpermq ymm23, ymm31, 170
	vmovdqu64 ymm22, YMMWORD PTR [r10]
	vpternlogq ymm24, ymm23, ymm22, 216
	vpermq ymm23, ymm29, 170
	vmovdqu64 ymm22, YMMWORD PTR [r10+352]
	vpternlogq ymm24, ymm23, ymm22, 216
	vpermq ymm23, ymm30, 170
	vmovdqu64 ymm22, YMMWORD PTR [r10+32]
	vpternlogq ymm24, ymm23, ymm22, 216
	vpermq ymm28, ymm28, 255
	vpermq ymm31, ymm31, 255
	vmovdqu64 ymm23, YMMWORD PTR [r10]
	vpternlogq ymm28, ymm31, ymm23, 216
	vpermq ymm31, ymm29, 255
	vmovdqu64 ymm29, YMMWORD PTR [r10+352]
	vpternlogq ymm28, ymm31, ymm29, 216
	vpermq ymm31, ymm30, 255
	vmovdqu64 ymm30, YMMWORD PTR [r10+32]
	vpternlogq ymm28, ymm31, ymm30, 216
	vpsllq ymm31, ymm26, 2
	vmovdqu64 ymm30, YMMWORD PTR [r10+256]
	vpandq ymm30, ymm31, ymm30
	vpsrlq ymm31, ymm26, 50
	vpsllq ymm29, ymm25, 14
	vpaddq ymm31, ymm31, ymm29
	vmovdqu64 ymm29, YMMWORD PTR [r10+256]
	vpandq ymm29, ymm31, ymm29
	vpsrlq ymm31, ymm25, 38
	vpsllq ymm26, ymm24, 26
	vpaddq ymm31, ymm31, ymm26
	vmovdqu64 ymm26, YMMWORD PTR [r10+256]
	vpandq ymm26, ymm31, ymm26
	vpsrlq ymm31, ymm24, 26
	vpsllq ymm25, ymm28, 38
	vpaddq ymm31, ymm31, ymm25
	vmovdqu64 ymm25, YMMWORD PTR [r10+256]
	vpandq ymm25, ymm31, ymm25
	vpsrlq ymm31, ymm28, 14
	vmovdqu64 ymm28, YMMWORD PTR [r10+352]
	vpandq ymm28, ymm30, ymm28
	vpaddq ymm30, ymm30, ymm28
	vmovdqu64 ymm28, YMMWORD PTR [r10+352]
	vpandq ymm28, ymm29, ymm28
	vpaddq ymm29, ymm29, ymm28
	vmovdqu64 ymm28, YMMWORD PTR [r10+352]
	vpandq ymm28, ymm26, ymm28
	vpaddq ymm28, ymm26, ymm28
	vmovdqu64 ymm26, YMMWORD PTR [r10+352]
	vpandq ymm26, ymm25, ymm26
	vpaddq ymm26, ymm25, ymm26
	vmovdqu64 ymm25, YMMWORD PTR [r10+352]
	vpandq ymm25, ymm31, ymm25
	vpaddq ymm31, ymm31, ymm25
	vpsraq ymm25, ymm31, 48
	vmovdqu64 ymm24, YMMWORD PTR [r10+224]
	vpandq ymm24, ymm31, ymm24
	vpaddq ymm31, ymm30, ymm25
	vpsllq ymm30, ymm25, 44
	vpsubq ymm30, ymm29, ymm30
	vpsllq ymm29, ymm25, 36
	vpsubq ymm29, ymm26, ymm29
	vpsllq ymm26, ymm25, 16
	vpaddq ymm26, ymm24, ymm26
	vpsraq ymm25, ymm31, 52
	vmovdqu64 ymm24, YMMWORD PTR [r10+256]
	vpandq ymm24, ymm31, ymm24
	vpaddq ymm31, ymm30, ymm25
	vpsraq ymm30, ymm31, 52
	vmovdqu64 ymm25, YMMWORD PTR [r10+256]
	vpandq ymm25, ymm31, ymm25
	vpaddq ymm31, ymm28, ymm30
	vpsraq ymm30, ymm31, 52
	vmovdqu64 ymm28, YMMWORD PTR [r10+256]
	vpandq ymm28, ymm31, ymm28
	vpaddq ymm31, ymm29, ymm30
	vpsraq ymm30, ymm31, 52
	vmovdqu64 ymm29, YMMWORD PTR [r10+256]
	vpandq ymm29, ymm31, ymm29
	vpaddq ymm31, ymm26, ymm30
	vpermq ymm30, ymm27, 85
	vpermq ymm26, ymm27, 170
	vpermq ymm23, ymm27, 255
	vpsllq ymm22, ymm27, 1
	vmovdqu64 ymm21, YMMWORD PTR [r10+256]
	vpandq ymm21, ymm22, ymm21
	vpsrlq ymm27, ymm27, 51
	vpsllq ymm22, ymm30, 13
	vpaddq ymm27, ymm27, ymm22
	vmovdqu64 ymm22, YMMWORD PTR [r10+256]
	vpandq ymm22, ymm27, ymm22
	vpsrlq ymm30, ymm30, 39
	vpsllq ymm27, ymm26, 25
	vpaddq ymm30, ymm30, ymm27
	vmovdqu64 ymm27, YMMWORD PTR [r10+256]
	vpandq ymm27, ymm30, ymm27
	vpsrlq ymm30, ymm26, 27
	vpsllq ymm26, ymm23, 37
	vpaddq ymm30, ymm30, ymm26
	vmovdqu64 ymm26, YMMWORD PTR [r10+256]
	vpandq ymm26, ymm30, ymm26
	vpsrlq ymm30, ymm23, 15
	vmovdqa64 ymm20, ymm24
	vmovdqa64 ymm23, ymm29
	vmovdqa64 ymm24, ymm31
	vmovdqa64 ymm29, ymm30
	vmovdqa64 ymm31, ymm25
	vmovdqa64 ymm25, ymm21
	vmovdqa64 ymm21, ymm31
	vmovdqa64 ymm31, ymm28
	vmovdqa64 ymm28, ymm26
	vmovdqa64 ymm26, ymm22
	vmovdqa64 ymm22, ymm31
	vmovdqu64 ymm31, YMMWORD PTR [r9]
	vpsraq ymm30, ymm24, 48
	vmovdqu64 ymm29, YMMWORD PTR [r10+224]
	vpandq ymm29, ymm24, ymm29
	vpaddq ymm28, ymm20, ymm30
	vpsllq ymm27, ymm30, 44
	vpsubq ymm27, ymm21, ymm27
	vpsllq ymm26, ymm30, 36
	vpsubq ymm26, ymm23, ymm26
	vpsllq ymm30, ymm30, 16
	vpaddq ymm30, ymm29, ymm30
	vpsraq ymm29, ymm28, 52
	vmovdqu64 ymm25, YMMWORD PTR [r10+256]
	vpandq ymm25, ymm28, ymm25
	vpaddq ymm29, ymm27, ymm29
	vpsraq ymm28, ymm29, 52
	vmovdqu64 ymm27, YMMWORD PTR [r10+256]
	vpandq ymm27, ymm29, ymm27
	vpaddq ymm29, ymm22, ymm28
	vpsraq ymm28, ymm29, 52
	vmovdqu64 ymm24, YMMWORD PTR [r10+256]
	vpandq ymm24, ymm29, ymm24
	vpaddq ymm29, ymm26, ymm28
	vpsraq ymm28, ymm29, 52
	vmovdqu64 ymm26, YMMWORD PTR [r10+256]
	vpandq ymm26, ymm29, ymm26
	vpaddq ymm30, ymm30, ymm28
	vpermq ymm29, ymm25, 80
	vpermq ymm28, ymm27, 80
	vpermq ymm23, ymm24, 80
	vpermq ymm22, ymm26, 80
	vpermq ymm21, ymm30, 80
	vpermq ymm20, ymm25, 170
	vpermq ymm19, ymm27, 170
	vpermq ymm18, ymm24, 170
	vpermq ymm17, ymm26, 170
	vpermq ymm16, ymm30, 170
	vpermq ymm25, ymm25, 255
	vpermq ymm27, ymm27, 255
	vpermq ymm24, ymm24, 255
	vpermq ymm26, ymm26, 255
	vpermq ymm30, ymm30, 255
	vpxorq ymm15, ymm15, ymm15
	vpsubq ymm14, ymm15, ymm25
	vpsubq ymm13, ymm15, ymm27
	vpsubq ymm12, ymm15, ymm24
	vpsubq ymm11, ymm15, ymm26
	vpsubq ymm15, ymm15, ymm30
	vpternlogq ymm25, ymm14, ymm31, 216
	vpternlogq ymm27, ymm13, ymm31, 216
	vpternlogq ymm24, ymm12, ymm31, 216
	vpternlogq ymm26, ymm11, ymm31, 216
	vpternlogq ymm30, ymm15, ymm31, 216
	vpxorq ymm31, ymm31, ymm31
	vpmadd52luq ymm31, ymm29, ymm29
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm29, ymm28
	vpaddq ymm15, ymm15, ymm15
	vpmadd52huq ymm15, ymm29, ymm29
	vpxorq ymm14, ymm14, ymm14
	vpmadd52huq ymm14, ymm29, ymm28
	vpmadd52luq ymm14, ymm29, ymm23
	vpaddq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm28, ymm28
	vpxorq ymm13, ymm13, ymm13
	vpmadd52huq ymm13, ymm29, ymm23
	vpmadd52luq ymm13, ymm28, ymm23
	vpmadd52luq ymm13, ymm29, ymm22
	vpaddq ymm13, ymm13, ymm13
	vpmadd52huq ymm13, ymm28, ymm28
	vpxorq ymm12, ymm12, ymm12
	vpmadd52huq ymm12, ymm28, ymm23
	vpmadd52luq ymm12, ymm28, ymm22
	vpxorq ymm11, ymm11, ymm11
	vpmadd52huq ymm11, ymm29, ymm22
	vpmadd52luq ymm11, ymm29, ymm21
	vpaddq ymm12, ymm12, ymm11
	vpaddq ymm12, ymm12, ymm12
	vpmadd52luq ymm12, ymm23, ymm23
	vpxorq ymm11, ymm11, ymm11
	vpmadd52huq ymm11, ymm28, ymm22
	vpmadd52huq ymm11, ymm29, ymm21
	vpxorq ymm10, ymm10, ymm10
	vpmadd52luq ymm10, ymm23, ymm22
	vpmadd52luq ymm10, ymm28, ymm21
	vpaddq ymm11, ymm11, ymm10
	vpaddq ymm11, ymm11, ymm11
	vpmadd52huq ymm11, ymm23, ymm23
	vpxorq ymm10, ymm10, ymm10
	vpmadd52huq ymm10, ymm23, ymm22
	vpmadd52huq ymm10, ymm28, ymm21
	vpmadd52luq ymm10, ymm23, ymm21
	vpaddq ymm10, ymm10, ymm10
	vpmadd52luq ymm10, ymm22, ymm22
	vpxorq ymm9, ymm9, ymm9
	vpmadd52huq ymm9, ymm23, ymm21
	vpmadd52luq ymm9, ymm22, ymm21
	vpaddq ymm9, ymm9, ymm9
	vpmadd52huq ymm9, ymm22, ymm22
	vpxorq ymm8, ymm8, ymm8
	vpmadd52huq ymm8, ymm22, ymm21
	vpaddq ymm8, ymm8, ymm8
	vpmadd52luq ymm8, ymm21, ymm21
	vpxorq ymm7, ymm7, ymm7
	vpmadd52huq ymm7, ymm21, ymm21
	vmovdqu64 ymm6, YMMWORD PTR [r10+256]
	vpandq ymm6, ymm31, ymm6
	vpsrlq ymm5, ymm31, 52
	vpsllq ymm4, ymm31, 56
	vpsrlq ymm4, ymm4, 12
	vpaddq ymm15, ymm15, ymm5
	vpaddq ymm15, ymm15, ymm4
	vpsrlq ymm6, ymm6, 8
	vpaddq ymm14, ymm14, ymm6
	vpmadd52luq ymm13, ymm31, YMMWORD PTR [r10+288]
	vpmadd52huq ymm12, ymm31, YMMWORD PTR [r10+288]
	vpmadd52luq ymm12, ymm31, YMMWORD PTR [r10+320]
	vpmadd52huq ymm11, ymm31, YMMWORD PTR [r10+320]
	vmovdqu64 ymm31, YMMWORD PTR [r10+256]
	vpandq ymm31, ymm15, ymm31
	vpsrlq ymm6, ymm15, 52
	vpsllq ymm5, ymm15, 56
	vpsrlq ymm5, ymm5, 12
	vpaddq ymm14, ymm14, ymm6
	vpaddq ymm14, ymm14, ymm5
	vpsrlq ymm31, ymm31, 8
	vpaddq ymm31, ymm13, ymm31
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r10+288]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r10+288]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r10+320]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r10+320]
	vmovdqu64 ymm15, YMMWORD PTR [r10+256]
	vpandq ymm15, ymm14, ymm15
	vpsrlq ymm13, ymm14, 52
	vpsllq ymm6, ymm14, 56
	vpsrlq ymm6, ymm6, 12
	vpaddq ymm31, ymm31, ymm13
	vpaddq ymm31, ymm31, ymm6
	vpsrlq ymm15, ymm15, 8
	vpaddq ymm15, ymm12, ymm15
	vpmadd52luq ymm11, ymm14, YMMWORD PTR [r10+288]
	vpmadd52huq ymm10, ymm14, YMMWORD PTR [r10+288]
	vpmadd52luq ymm10, ymm14, YMMWORD PTR [r10+320]
	vpmadd52huq ymm9, ymm14, YMMWORD PTR [r10+320]
	vmovdqu64 ymm14, YMMWORD PTR [r10+256]
	vpandq ymm14, ymm31, ymm14
	vpsrlq ymm13, ymm31, 52
	vpsllq ymm12, ymm31, 56
	vpsrlq ymm12, ymm12, 12
	vpaddq ymm15, ymm15, ymm13
	vpaddq ymm15, ymm15, ymm12
	vpsrlq ymm14, ymm14, 8
	vpaddq ymm14, ymm11, ymm14
	vpmadd52luq ymm10, ymm31, YMMWORD PTR [r10+288]
	vpmadd52huq ymm9, ymm31, YMMWORD PTR [r10+288]
	vpmadd52luq ymm9, ymm31, YMMWORD PTR [r10+320]
	vpmadd52huq ymm8, ymm31, YMMWORD PTR [r10+320]
	vmovdqu64 ymm31, YMMWORD PTR [r10+256]
	vpandq ymm31, ymm15, ymm31
	vpsrlq ymm13, ymm15, 52
	vpsllq ymm12, ymm15, 56
	vpsrlq ymm12, ymm12, 12
	vpaddq ymm14, ymm14, ymm13
	vpaddq ymm14, ymm14, ymm12
	vpsrlq ymm31, ymm31, 8
	vpaddq ymm31, ymm10, ymm31
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r10+288]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r10+288]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r10+320]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r10+320]
	vmovdqa64 ymm0, ymm25
	vmovdqa64 ymm1, ymm27
	vmovdqa64 ymm2, ymm24
	vmovdqa64 ymm3, ymm26
	vmovdqa64 ymm4, ymm30
	vmovdqa64 ymm5, ymm20
	vmovdqa64 ymm6, ymm19
	vmovdqa64 ymm10, ymm29
	vmovdqa64 ymm11, ymm28
	vmovdqa64 ymm12, ymm23
	vmovdqa64 ymm13, ymm22
	vmovdqa64 ymm15, ymm14
	vmovdqa64 ymm14, ymm21
	vmovdqa64 ymm19, ymm7
	vmovdqa64 ymm7, ymm18
	vmovdqa64 ymm18, ymm8
	vmovdqa64 ymm8, ymm17
	vmovdqa64 ymm17, ymm9
	vmovdqa64 ymm9, ymm16
	vmovdqa64 ymm16, ymm31
25:
	sub rbx, 1
	mov r11d, 5
26:
	vpermq ymm31, ymm15, 102
	vpermq ymm30, ymm16, 102
	vpermq ymm29, ymm17, 102
	vpermq ymm28, ymm18, 102
	vpermq ymm27, ymm19, 102
	vpsubq ymm31, ymm15, ymm31
	vpsubq ymm30, ymm16, ymm30
	vpsubq ymm29, ymm17, ymm29
	vpsubq ymm28, ymm18, ymm28
	vpsubq ymm27, ymm19, ymm27
	vpsllq ymm26, ymm31, 5
	vpsllq ymm25, ymm30, 5
	vpsllq ymm24, ymm29, 5
	vpsllq ymm23, ymm28, 5
	vpsllq ymm22, ymm27, 5
	vpsllq ymm31, ymm31, 4
	vpsllq ymm30, ymm30, 4
	vpsllq ymm29, ymm29, 4
	vpsllq ymm28, ymm28, 4
	vpsllq ymm27, ymm27, 4
	vpaddq ymm31, ymm26, ymm31
	vpaddq ymm30, ymm25, ymm30
	vpaddq ymm29, ymm24, ymm29
	vpaddq ymm28, ymm23, ymm28
	vpaddq ymm27, ymm22, ymm27
	vpsllq ymm26, ymm0, 2
	vpsllq ymm25, ymm1, 2
	vpsllq ymm24, ymm2, 2
	vpsllq ymm23, ymm3, 2
	vpsllq ymm22, ymm4, 2
	vpermq ymm26, ymm26, 0
	vpermq ymm25, ymm25, 0
	vpermq ymm24, ymm24, 0
	vpermq ymm23, ymm23, 0
	vpermq ymm22, ymm22, 0
	vpaddq ymm21, ymm5, ymm5
	vpaddq ymm20, ymm6, ymm6
	vpaddq ymm7, ymm7, ymm7
	vpaddq ymm8, ymm8, ymm8
	vpaddq ymm9, ymm9, ymm9
	vmovdqu64 ymm6, YMMWORD PTR [r10]
	vpandq ymm6, ymm21, ymm6
	vpaddq ymm26, ymm26, ymm6
	vmovdqu64 ymm21, YMMWORD PTR [r10]
	vpandq ymm21, ymm20, ymm21
	vpaddq ymm25, ymm25, ymm21
	vmovdqu64 ymm21, YMMWORD PTR [r10]
	vpandq ymm21, ymm7, ymm21
	vpaddq ymm24, ymm24, ymm21
	vmovdqu64 ymm21, YMMWORD PTR [r10]
	vpandq ymm21, ymm8, ymm21
	vpaddq ymm23, ymm23, ymm21
	vmovdqu64 ymm21, YMMWORD PTR [r10]
	vpandq ymm21, ymm9, ymm21
	vpaddq ymm22, ymm22, ymm21
	vmovdqu64 ymm21, YMMWORD PTR [r10+32]
	vpternlogq ymm26, ymm31, ymm21, 216
	vmovdqu64 ymm31, YMMWORD PTR [r10+32]
	vpternlogq ymm25, ymm30, ymm31, 216
	vmovdqu64 ymm31, YMMWORD PTR [r10+32]
	vpternlogq ymm24, ymm29, ymm31, 216
	vmovdqu64 ymm31, YMMWORD PTR [r10+32]
	vpternlogq ymm23, ymm28, ymm31, 216
	vmovdqu64 ymm31, YMMWORD PTR [r10+32]
	vpternlogq ymm22, ymm27, ymm31, 216
	vmovdqu64 ymm31, YMMWORD PTR [r10+64]
	vpaddq ymm31, ymm26, ymm31
	vmovdqu64 ymm30, YMMWORD PTR [r10+96]
	vpaddq ymm30, ymm25, ymm30
	vmovdqu64 ymm29, YMMWORD PTR [r10+128]
	vpaddq ymm29, ymm24, ymm29
	vmovdqu64 ymm28, YMMWORD PTR [r10+160]
	vpaddq ymm28, ymm23, ymm28
	vmovdqu64 ymm27, YMMWORD PTR [r10+192]
	vpaddq ymm27, ymm22, ymm27
	vpsraq ymm26, ymm27, 48
	vmovdqu64 ymm25, YMMWORD PTR [r10+224]
	vpandq ymm25, ymm27, ymm25
	vpaddq ymm31, ymm31, ymm26
	vpsllq ymm27, ymm26, 44
	vpsubq ymm30, ymm30, ymm27
	vpsllq ymm27, ymm26, 36
	vpsubq ymm28, ymm28, ymm27
	vpsllq ymm27, ymm26, 16
	vpaddq ymm27, ymm25, ymm27
	vpsraq ymm26, ymm31, 52
	vmovdqu64 ymm25, YMMWORD PTR [r10+256]
	vpandq ymm25, ymm31, ymm25
	vpaddq ymm31, ymm30, ymm26
	vpsraq ymm30, ymm31, 52
	vmovdqu64 ymm26, YMMWORD PTR [r10+256]
	vpandq ymm26, ymm31, ymm26
	vpaddq ymm31, ymm29, ymm30
	vpsraq ymm30, ymm31, 52
	vmovdqu64 ymm29, YMMWORD PTR [r10+256]
	vpandq ymm29, ymm31, ymm29
	vpaddq ymm31, ymm28, ymm30
	vpsraq ymm30, ymm31, 52
	vmovdqu64 ymm28, YMMWORD PTR [r10+256]
	vpandq ymm28, ymm31, ymm28
	vpaddq ymm31, ymm27, ymm30
	vpxorq ymm30, ymm30, ymm30
	vpmadd52luq ymm30, ymm25, ymm25
	vpxorq ymm27, ymm27, ymm27
	vpmadd52luq ymm27, ymm25, ymm26
	vpaddq ymm27, ymm27, ymm27
	vpmadd52huq ymm27, ymm25, ymm25
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm25, ymm26
	vpmadd52luq ymm24, ymm25, ymm29
	vpaddq ymm24, ymm24, ymm24
	vpmadd52luq ymm24, ymm26, ymm26
	vpxorq ymm23, ymm23, ymm23
	vpmadd52huq ymm23, ymm25, ymm29
	vpmadd52luq ymm23, ymm26, ymm29
	vpmadd52luq ymm23, ymm25, ymm28
	vpaddq ymm23, ymm23, ymm23
	vpmadd52huq ymm23, ymm26, ymm26
	vpxorq ymm22, ymm22, ymm22
	vpmadd52huq ymm22, ymm26, ymm29
	vpmadd52luq ymm22, ymm26, ymm28
	vpxorq ymm21, ymm21, ymm21
	vpmadd52huq ymm21, ymm25, ymm28
	vpmadd52luq ymm21, ymm25, ymm31
	vpaddq ymm22, ymm22, ymm21
	vpaddq ymm22, ymm22, ymm22
	vpmadd52luq ymm22, ymm29, ymm29
	vpxorq ymm21, ymm21, ymm21
	vpmadd52huq ymm21, ymm26, ymm28
	vpmadd52huq ymm21, ymm25, ymm31
	vpxorq ymm20, ymm20, ymm20
	vpmadd52luq ymm20, ymm29, ymm28
	vpmadd52luq ymm20, ymm26, ymm31
	vpaddq ymm21, ymm21, ymm20
	vpaddq ymm21, ymm21, ymm21
	vpmadd52huq ymm21, ymm29, ymm29
	vpxorq ymm20, ymm20, ymm20
	vpmadd52huq ymm20, ymm29, ymm28
	vpmadd52huq ymm20, ymm26, ymm31
	vpmadd52luq ymm20, ymm29, ymm31
	vpaddq ymm20, ymm20, ymm20
	vpmadd52luq ymm20, ymm28, ymm28
	vpxorq ymm9, ymm9, ymm9
	vpmadd52huq ymm9, ymm29, ymm31
	vpmadd52luq ymm9, ymm28, ymm31
	vpaddq ymm9, ymm9, ymm9
	vpmadd52huq ymm9, ymm28, ymm28
	vpxorq ymm8, ymm8, ymm8
	vpmadd52huq ymm8, ymm28, ymm31
	vpaddq ymm8, ymm8, ymm8
	vpmadd52luq ymm8, ymm31, ymm31
	vpxorq ymm7, ymm7, ymm7
	vpmadd52huq ymm7, ymm31, ymm31
	vmovdqu64 ymm6, YMMWORD PTR [r10+256]
	vpandq ymm6, ymm30, ymm6
	vpsrlq ymm5, ymm30, 52
	vpsllq ymm4, ymm30, 56
	vpsrlq ymm4, ymm4, 12
	vpaddq ymm27, ymm27, ymm5
	vpaddq ymm27, ymm27, ymm4
	vpsrlq ymm6, ymm6, 8
	vpaddq ymm24, ymm24, ymm6
	vpmadd52luq ymm23, ymm30, YMMWORD PTR [r10+288]
	vpmadd52huq ymm22, ymm30, YMMWORD PTR [r10+288]
	vpmadd52luq ymm22, ymm30, YMMWORD PTR [r10+320]
	vpmadd52huq ymm21, ymm30, YMMWORD PTR [r10+320]
	vmovdqu64 ymm30, YMMWORD PTR [r10+256]
	vpandq ymm30, ymm27, ymm30
	vpsrlq ymm6, ymm27, 52
	vpsllq ymm5, ymm27, 56
	vpsrlq ymm5, ymm5, 12
	vpaddq ymm24, ymm24, ymm6
	vpaddq ymm24, ymm24, ymm5
	vpsrlq ymm30, ymm30, 8
	vpaddq ymm30, ymm23, ymm30
	vpmadd52luq ymm22, ymm27, YMMWORD PTR [r10+288]
	vpmadd52huq ymm21, ymm27, YMMWORD PTR [r10+288]
	vpmadd52luq ymm21, ymm27, YMMWORD PTR [r10+320]
	vpmadd52huq ymm20, ymm27, YMMWORD PTR [r10+320]
	vmovdqu64 ymm27, YMMWORD PTR [r10+256]
	vpandq ymm27, ymm24, ymm27
	vpsrlq ymm23, ymm24, 52
	vpsllq ymm6, ymm24, 56
	vpsrlq ymm6, ymm6, 12
	vpaddq ymm30, ymm30, ymm23
	vpaddq ymm30, ymm30, ymm6
	vpsrlq ymm27, ymm27, 8
	vpaddq ymm27, ymm22, ymm27
	vpmadd52luq ymm21, ymm24, YMMWORD PTR [r10+288]
	vpmadd52huq ymm20, ymm24, YMMWORD PTR [r10+288]
	vpmadd52luq ymm20, ymm24, YMMWORD PTR [r10+320]
	vpmadd52huq ymm9, ymm24, YMMWORD PTR [r10+320]
	vmovdqu64 ymm24, YMMWORD PTR [r10+256]
	vpandq ymm24, ymm30, ymm24
	vpsrlq ymm23, ymm30, 52
	vpsllq ymm22, ymm30, 56
	vpsrlq ymm22, ymm22, 12
	vpaddq ymm27, ymm27, ymm23
	vpaddq ymm27, ymm27, ymm22
	vpsrlq ymm24, ymm24, 8
	vpaddq ymm24, ymm21, ymm24
	vpmadd52luq ymm20, ymm30, YMMWORD PTR [r10+288]
	vpmadd52huq ymm9, ymm30, YMMWORD PTR [r10+288]
	vpmadd52luq ymm9, ymm30, YMMWORD PTR [r10+320]
	vpmadd52huq ymm8, ymm30, YMMWORD PTR [r10+320]
	vmovdqu64 ymm30, YMMWORD PTR [r10+256]
	vpandq ymm30, ymm27, ymm30
	vpsrlq ymm23, ymm27, 52
	vpsllq ymm22, ymm27, 56
	vpsrlq ymm22, ymm22, 12
	vpaddq ymm24, ymm24, ymm23
	vpaddq ymm24, ymm24, ymm22
	vpsrlq ymm30, ymm30, 8
	vpaddq ymm30, ymm20, ymm30
	vpmadd52luq ymm9, ymm27, YMMWORD PTR [r10+288]
	vpmadd52huq ymm8, ymm27, YMMWORD PTR [r10+288]
	vpmadd52luq ymm8, ymm27, YMMWORD PTR [r10+320]
	vpmadd52huq ymm7, ymm27, YMMWORD PTR [r10+320]
	vpermq ymm27, ymm24, 192
	vpermq ymm23, ymm30, 192
	vpermq ymm22, ymm9, 192
	vpermq ymm21, ymm8, 192
	vpermq ymm20, ymm7, 192
	vpsllq ymm10, ymm10, 2
	vpsllq ymm11, ymm11, 2
	vpsllq ymm12, ymm12, 2
	vpsllq ymm13, ymm13, 2
	vpsllq ymm14, ymm14, 2
	vpermq ymm6, ymm10, 244
	vpermq ymm5, ymm11, 244
	vpermq ymm4, ymm12, 244
	vpermq ymm3, ymm13, 244
	vpermq ymm2, ymm14, 244
	vmovdqu64 ymm1, YMMWORD PTR [r10+352]
	vmovdqa64 ymm0, ymm24
	vpternlogq ymm0, ymm27, ymm1, 216
	vmovdqu64 ymm1, YMMWORD PTR [r10+352]
	vmovdqu64 YMMWORD PTR [rdi+4512], ymm31
	vmovdqa64 ymm31, ymm30
	vpternlogq ymm31, ymm23, ymm1, 216
	vmovdqu64 ymm1, YMMWORD PTR [r10+352]
	vmovdqu64 YMMWORD PTR [rdi+4544], ymm28
	vmovdqa64 ymm28, ymm9
	vpternlogq ymm28, ymm22, ymm1, 216
	vmovdqu64 ymm1, YMMWORD PTR [r10+352]
	vmovdqu64 YMMWORD PTR [rdi+4576], ymm29
	vmovdqa64 ymm29, ymm8
	vpternlogq ymm29, ymm21, ymm1, 216
	vmovdqu64 ymm1, YMMWORD PTR [r10+352]
	vmovdqu64 YMMWORD PTR [rdi+4608], ymm26
	vmovdqa64 ymm26, ymm7
	vpternlogq ymm26, ymm20, ymm1, 216
	vmovdqu64 ymm1, YMMWORD PTR [r10]
	vpandq ymm1, ymm27, ymm1
	vpsubq ymm27, ymm0, ymm1
	vmovdqu64 ymm1, YMMWORD PTR [r10]
	vpandq ymm1, ymm23, ymm1
	vpsubq ymm31, ymm31, ymm1
	vmovdqu64 ymm23, YMMWORD PTR [r10]
	vpandq ymm23, ymm22, ymm23
	vpsubq ymm28, ymm28, ymm23
	vmovdqu64 ymm23, YMMWORD PTR [r10]
	vpandq ymm23, ymm21, ymm23
	vpsubq ymm29, ymm29, ymm23
	vmovdqu64 ymm23, YMMWORD PTR [r10]
	vpandq ymm23, ymm20, ymm23
	vpsubq ymm26, ymm26, ymm23
	vmovdqu64 ymm23, YMMWORD PTR [r10]
	vpandq ymm23, ymm10, ymm23
	vpsubq ymm27, ymm27, ymm23
	vmovdqu64 ymm23, YMMWORD PTR [r10]
	vpandq ymm23, ymm11, ymm23
	vpsubq ymm31, ymm31, ymm23
	vmovdqu64 ymm23, YMMWORD PTR [r10]
	vpandq ymm23, ymm12, ymm23
	vpsubq ymm28, ymm28, ymm23
	vmovdqu64 ymm23, YMMWORD PTR [r10]
	vpandq ymm23, ymm13, ymm23
	vpsubq ymm29, ymm29, ymm23
	vmovdqu64 ymm23, YMMWORD PTR [r10]
	vpandq ymm23, ymm14, ymm23
	vpsubq ymm26, ymm26, ymm23
	vmovdqu64 ymm23, YMMWORD PTR [r10+352]
	vpandq ymm23, ymm6, ymm23
	vpaddq ymm27, ymm27, ymm23
	vmovdqu64 ymm23, YMMWORD PTR [r10+352]
	vpandq ymm23, ymm5, ymm23
	vpaddq ymm31, ymm31, ymm23
	vmovdqu64 ymm23, YMMWORD PTR [r10+352]
	vpandq ymm23, ymm4, ymm23
	vpaddq ymm28, ymm28, ymm23
	vmovdqu64 ymm23, YMMWORD PTR [r10+352]
	vpandq ymm23, ymm3, ymm23
	vpaddq ymm29, ymm29, ymm23
	vmovdqu64 ymm23, YMMWORD PTR [r10+352]
	vpandq ymm23, ymm2, ymm23
	vpaddq ymm26, ymm26, ymm23
	vmovdqu64 ymm23, YMMWORD PTR [r10+384]
	vpaddq ymm23, ymm27, ymm23
	vmovdqu64 ymm27, YMMWORD PTR [r10+416]
	vpaddq ymm27, ymm31, ymm27
	vmovdqu64 ymm31, YMMWORD PTR [r10+128]
	vpaddq ymm31, ymm28, ymm31
	vmovdqu64 ymm28, YMMWORD PTR [r10+448]
	vpaddq ymm28, ymm29, ymm28
	vmovdqu64 ymm29, YMMWORD PTR [r10+480]
	vpaddq ymm29, ymm26, ymm29
	vpsraq ymm26, ymm29, 48
	vmovdqu64 ymm22, YMMWORD PTR [r10+224]
	vpandq ymm22, ymm29, ymm22
	vpaddq ymm29, ymm23, ymm26
	vpsllq ymm23, ymm26, 44
	vpsubq ymm27, ymm27, ymm23
	vpsllq ymm23, ymm26, 36
	vpsubq ymm28, ymm28, ymm23
	vpsllq ymm26, ymm26, 16
	vpaddq ymm26, ymm22, ymm26
	vpsraq ymm23, ymm29, 52
	vmovdqu64 ymm22, YMMWORD PTR [r10+256]
	vpandq ymm22, ymm29, ymm22
	vpaddq ymm29, ymm27, ymm23
	vpsraq ymm27, ymm29, 52
	vmovdqu64 ymm23, YMMWORD PTR [r10+256]
	vpandq ymm23, ymm29, ymm23
	vpaddq ymm31, ymm31, ymm27
	vpsraq ymm29, ymm31, 52
	vmovdqu64 ymm27, YMMWORD PTR [r10+256]
	vpandq ymm27, ymm31, ymm27
	vpaddq ymm31, ymm28, ymm29
	vpsraq ymm29, ymm31, 52
	vmovdqu64 ymm28, YMMWORD PTR [r10+256]
	vpandq ymm28, ymm31, ymm28
	vpaddq ymm31, ymm26, ymm29
	vpxorq ymm29, ymm29, ymm29
	vpmadd52luq ymm29, ymm22, ymm22
	vpxorq ymm26, ymm26, ymm26
	vpmadd52luq ymm26, ymm22, ymm23
	vpaddq ymm26, ymm26, ymm26
	vpmadd52huq ymm26, ymm22, ymm22
	vpxorq ymm21, ymm21, ymm21
	vpmadd52huq ymm21, ymm22, ymm23
	vpmadd52luq ymm21, ymm22, ymm27
	vpaddq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm23, ymm23
	vpxorq ymm20, ymm20, ymm20
	vpmadd52huq ymm20, ymm22, ymm27
	vpmadd52luq ymm20, ymm23, ymm27
	vpmadd52luq ymm20, ymm22, ymm28
	vpaddq ymm20, ymm20, ymm20
	vpmadd52huq ymm20, ymm23, ymm23
	vpxorq ymm14, ymm14, ymm14
	vpmadd52huq ymm14, ymm23, ymm27
	vpmadd52luq ymm14, ymm23, ymm28
	vpxorq ymm13, ymm13, ymm13
	vpmadd52huq ymm13, ymm22, ymm28
	vpmadd52luq ymm13, ymm22, ymm31
	vpaddq ymm14, ymm14, ymm13
	vpaddq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm27, ymm27
	vpxorq ymm13, ymm13, ymm13
	vpmadd52huq ymm13, ymm23, ymm28
	vpmadd52huq ymm13, ymm22, ymm31
	vpxorq ymm12, ymm12, ymm12
	vpmadd52luq ymm12, ymm27, ymm28
	vpmadd52luq ymm12, ymm23, ymm31
	vpaddq ymm13, ymm13, ymm12
	vpaddq ymm13, ymm13, ymm13
	vpmadd52huq ymm13, ymm27, ymm27
	vpxorq ymm12, ymm12, ymm12
	vpmadd52huq ymm12, ymm27, ymm28
	vpmadd52huq ymm12, ymm23, ymm31
	vpmadd52luq ymm12, ymm27, ymm31
	vpaddq ymm12, ymm12, ymm12
	vpmadd52luq ymm12, ymm28, ymm28
	vpxorq ymm11, ymm11, ymm11
	vpmadd52huq ymm11, ymm27, ymm31
	vpmadd52luq ymm11, ymm28, ymm31
	vpaddq ymm11, ymm11, ymm11
	vpmadd52huq ymm11, ymm28, ymm28
	vpxorq ymm10, ymm10, ymm10
	vpmadd52huq ymm10, ymm28, ymm31
	vpaddq ymm10, ymm10, ymm10
	vpmadd52luq ymm10, ymm31, ymm31
	vpxorq ymm6, ymm6, ymm6
	vpmadd52huq ymm6, ymm31, ymm31
	vmovdqu64 ymm5, YMMWORD PTR [r10+256]
	vpandq ymm5, ymm29, ymm5
	vpsrlq ymm4, ymm29, 52
	vpsllq ymm3, ymm29, 56
	vpsrlq ymm3, ymm3, 12
	vpaddq ymm26, ymm26, ymm4
	vpaddq ymm26, ymm26, ymm3
	vpsrlq ymm5, ymm5, 8
	vpaddq ymm21, ymm21, ymm5
	vpmadd52luq ymm20, ymm29, YMMWORD PTR [r10+288]
	vpmadd52huq ymm14, ymm29, YMMWORD PTR [r10+288]
	vpmadd52luq ymm14, ymm29, YMMWORD PTR [r10+320]
	vpmadd52huq ymm13, ymm29, YMMWORD PTR [r10+320]
	vmovdqu64 ymm29, YMMWORD PTR [r10+256]
	vpandq ymm29, ymm26, ymm29
	vpsrlq ymm5, ymm26, 52
	vpsllq ymm4, ymm26, 56
	vpsrlq ymm4, ymm4, 12
	vpaddq ymm21, ymm21, ymm5
	vpaddq ymm21, ymm21, ymm4
	vpsrlq ymm29, ymm29, 8
	vpaddq ymm29, ymm20, ymm29
	vpmadd52luq ymm14, ymm26, YMMWORD PTR [r10+288]
	vpmadd52huq ymm13, ymm26, YMMWORD PTR [r10+288]
	vpmadd52luq ymm13, ymm26, YMMWORD PTR [r10+320]
	vpmadd52huq ymm12, ymm26, YMMWORD PTR [r10+320]
	vmovdqu64 ymm26, YMMWORD PTR [r10+256]
	vpandq ymm26, ymm21, ymm26
	vpsrlq ymm20, ymm21, 52
	vpsllq ymm5, ymm21, 56
	vpsrlq ymm5, ymm5, 12
	vpaddq ymm29, ymm29, ymm20
	vpaddq ymm29, ymm29, ymm5
	vpsrlq ymm26, ymm26, 8
	vpaddq ymm26, ymm14, ymm26
	vpmadd52luq ymm13, ymm21, YMMWORD PTR [r10+288]
	vpmadd52huq ymm12, ymm21, YMMWORD PTR [r10+288]
	vpmadd52luq ymm12, ymm21, YMMWORD PTR [r10+320]
	vpmadd52huq ymm11, ymm21, YMMWORD PTR [r10+320]
	vmovdqu64 ymm21, YMMWORD PTR [r10+256]
	vpandq ymm21, ymm29, ymm21
	vpsrlq ymm20, ymm29, 52
	vpsllq ymm14, ymm29, 56
	vpsrlq ymm14, ymm14, 12
	vpaddq ymm26, ymm26, ymm20
	vpaddq ymm26, ymm26, ymm14
	vpsrlq ymm21, ymm21, 8
	vpaddq ymm21, ymm13, ymm21
	vpmadd52luq ymm12, ymm29, YMMWORD PTR [r10+288]
	vpmadd52huq ymm11, ymm29, YMMWORD PTR [r10+288]
	vpmadd52luq ymm11, ymm29, YMMWORD PTR [r10+320]
	vpmadd52huq ymm10, ymm29, YMMWORD PTR [r10+320]
	vmovdqu64 ymm29, YMMWORD PTR [r10+256]
	vpandq ymm29, ymm26, ymm29
	vpsrlq ymm20, ymm26, 52
	vpsllq ymm14, ymm26, 56
	vpsrlq ymm14, ymm14, 12
	vpaddq ymm21, ymm21, ymm20
	vpaddq ymm21, ymm21, ymm14
	vpsrlq ymm29, ymm29, 8
	vpaddq ymm29, ymm12, ymm29
	vpmadd52luq ymm11, ymm26, YMMWORD PTR [r10+288]
	vpmadd52huq ymm10, ymm26, YMMWORD PTR [r10+288]
	vpmadd52luq ymm10, ymm26, YMMWORD PTR [r10+320]
	vpmadd52huq ymm6, ymm26, YMMWORD PTR [r10+320]
	vpermq ymm26, ymm21, 166
	vpermq ymm20, ymm29, 166
	vpermq ymm14, ymm11, 166
	vpermq ymm13, ymm10, 166
	vpermq ymm12, ymm6, 166
	vpermq ymm5, ymm21, 0
	vpermq ymm4, ymm29, 0
	vpermq ymm3, ymm11, 0
	vpermq ymm2, ymm10, 0
	vpermq ymm1, ymm6, 0
	vpermq ymm24, ymm24, 255
	vpermq ymm30, ymm30, 255
	vpermq ymm9, ymm9, 255
	vpermq ymm8, ymm8, 255
	vpermq ymm7, ymm7, 255
	vpermq ymm15, ymm15, 255
	vpermq ymm16, ymm16, 255
	vpermq ymm17, ymm17, 255
	vpermq ymm18, ymm18, 255
	vpermq ymm19, ymm19, 255
	vpsllq ymm15, ymm15, 4
	vpsllq ymm16, ymm16, 4
	vpsllq ymm17, ymm17, 4
	vpsllq ymm18, ymm18, 4
	vpsllq ymm19, ymm19, 4
	vpsubq ymm26, ymm26, ymm5
	vpsubq ymm20, ymm20, ymm4
	vpsubq ymm14, ymm14, ymm3
	vpsubq ymm13, ymm13, ymm2
	vpsubq ymm12, ymm12, ymm1
	vpsubq ymm26, ymm26, ymm15
	vpsubq ymm20, ymm20, ymm16
	vpsubq ymm17, ymm14, ymm17
	vpsubq ymm18, ymm13, ymm18
	vpsubq ymm19, ymm12, ymm19
	vpaddq ymm26, ymm26, ymm26
	vpaddq ymm20, ymm20, ymm20
	vpaddq ymm17, ymm17, ymm17
	vpaddq ymm18, ymm18, ymm18
	vpaddq ymm19, ymm19, ymm19
	vpaddq ymm16, ymm26, ymm26
	vpaddq ymm15, ymm20, ymm20
	vpaddq ymm14, ymm17, ymm17
	vpaddq ymm13, ymm18, ymm18
	vpaddq ymm12, ymm19, ymm19
	vpsubq ymm16, ymm24, ymm16
	vpsubq ymm15, ymm30, ymm15
	vpsubq ymm14, ymm9, ymm14
	vpsubq ymm13, ymm8, ymm13
	vpsubq ymm12, ymm7, ymm12
	vpsubq ymm26, ymm26, ymm16
	vmovdqu64 ymm0, YMMWORD PTR [r10+512]
	vpternlogq ymm16, ymm26, ymm0, 216
	vpsubq ymm26, ymm20, ymm15
	vmovdqu64 ymm20, YMMWORD PTR [r10+512]
	vpternlogq ymm15, ymm26, ymm20, 216
	vpsubq ymm26, ymm17, ymm14
	vmovdqu64 ymm20, YMMWORD PTR [r10+512]
	vpternlogq ymm14, ymm26, ymm20, 216
	vpsubq ymm26, ymm18, ymm13
	vmovdqu64 ymm20, YMMWORD PTR [r10+512]
	vpternlogq ymm13, ymm26, ymm20, 216
	vpsubq ymm26, ymm19, ymm12
	vmovdqu64 ymm20, YMMWORD PTR [r10+512]
	vpternlogq ymm12, ymm26, ymm20, 216
	vpermq ymm26, ymm25, 255
	vmovdqu64 ymm25, YMMWORD PTR [rdi+4608]
	vpermq ymm25, ymm25, 255
	vmovdqu64 ymm20, YMMWORD PTR [rdi+4576]
	vpermq ymm20, ymm20, 255
	vmovdqu64 ymm19, YMMWORD PTR [rdi+4544]
	vpermq ymm19, ymm19, 255
	vmovdqu64 ymm18, YMMWORD PTR [rdi+4512]
	vpermq ymm18, ymm18, 255
	vmovdqu64 ymm17, YMMWORD PTR [r10+352]
	vpandq ymm17, ymm26, ymm17
	vpaddq ymm26, ymm16, ymm17
	vmovdqu64 ymm17, YMMWORD PTR [r10+352]
	vpandq ymm17, ymm25, ymm17
	vpaddq ymm25, ymm15, ymm17
	vmovdqu64 ymm17, YMMWORD PTR [r10+352]
	vpandq ymm17, ymm20, ymm17
	vpaddq ymm20, ymm14, ymm17
	vmovdqu64 ymm17, YMMWORD PTR [r10+352]
	vpandq ymm17, ymm19, ymm17
	vpaddq ymm19, ymm13, ymm17
	vmovdqu64 ymm17, YMMWORD PTR [r10+352]
	vpandq ymm17, ymm18, ymm17
	vpaddq ymm18, ymm12, ymm17
	vmovdqu64 ymm17, YMMWORD PTR [r10]
	vpternlogq ymm26, ymm21, ymm17, 216
	vmovdqu64 ymm21, YMMWORD PTR [r10]
	vpternlogq ymm25, ymm29, ymm21, 216
	vmovdqu64 ymm29, YMMWORD PTR [r10]
	vpternlogq ymm20, ymm11, ymm29, 216
	vmovdqu64 ymm29, YMMWORD PTR [r10]
	vpternlogq ymm19, ymm10, ymm29, 216
	vmovdqu64 ymm29, YMMWORD PTR [r10]
	vpternlogq ymm18, ymm6, ymm29, 216
	vmovdqu64 ymm29, YMMWORD PTR [r10+544]
	vpaddq ymm29, ymm26, ymm29
	vmovdqu64 ymm26, YMMWORD PTR [r10+576]
	vpaddq ymm26, ymm25, ymm26
	vmovdqu64 ymm25, YMMWORD PTR [r10+128]
	vpaddq ymm25, ymm20, ymm25
	vmovdqu64 ymm21, YMMWORD PTR [r10+608]
	vpaddq ymm21, ymm19, ymm21
	vmovdqu64 ymm20, YMMWORD PTR [r10+640]
	vpaddq ymm20, ymm18, ymm20
	vpsraq ymm19, ymm20, 48
	vmovdqu64 ymm18, YMMWORD PTR [r10+224]
	vpandq ymm18, ymm20, ymm18
	vpaddq ymm29, ymm29, ymm19
	vpsllq ymm20, ymm19, 44
	vpsubq ymm26, ymm26, ymm20
	vpsllq ymm20, ymm19, 36
	vpsubq ymm21, ymm21, ymm20
	vpsllq ymm20, ymm19, 16
	vpaddq ymm20, ymm18, ymm20
	vpsraq ymm19, ymm29, 52
	vmovdqu64 ymm18, YMMWORD PTR [r10+256]
	vpandq ymm18, ymm29, ymm18
	vpaddq ymm29, ymm26, ymm19
	vpsraq ymm26, ymm29, 52
	vmovdqu64 ymm19, YMMWORD PTR [r10+256]
	vpandq ymm19, ymm29, ymm19
	vpaddq ymm29, ymm25, ymm26
	vpsraq ymm26, ymm29, 52
	vmovdqu64 ymm25, YMMWORD PTR [r10+256]
	vpandq ymm25, ymm29, ymm25
	vpaddq ymm29, ymm21, ymm26
	vpsraq ymm26, ymm29, 52
	vmovdqu64 ymm21, YMMWORD PTR [r10+256]
	vpandq ymm21, ymm29, ymm21
	vpaddq ymm29, ymm20, ymm26
	vpxorq ymm26, ymm26, ymm26
	vpmadd52luq ymm26, ymm18, ymm18
	vpxorq ymm20, ymm20, ymm20
	vpmadd52luq ymm20, ymm18, ymm19
	vpaddq ymm20, ymm20, ymm20
	vpmadd52huq ymm20, ymm18, ymm18
	vpxorq ymm17, ymm17, ymm17
	vpmadd52huq ymm17, ymm18, ymm19
	vpmadd52luq ymm17, ymm18, ymm25
	vpaddq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm19, ymm19
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm18, ymm25
	vpmadd52luq ymm16, ymm19, ymm25
	vpmadd52luq ymm16, ymm18, ymm21
	vpaddq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm19, ymm19
	vpxorq ymm15, ymm15, ymm15
	vpmadd52huq ymm15, ymm19, ymm25
	vpmadd52luq ymm15, ymm19, ymm21
	vpxorq ymm14, ymm14, ymm14
	vpmadd52huq ymm14, ymm18, ymm21
	vpmadd52luq ymm14, ymm18, ymm29
	vpaddq ymm15, ymm15, ymm14
	vpaddq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm25, ymm25
	vpxorq ymm14, ymm14, ymm14
	vpmadd52huq ymm14, ymm19, ymm21
	vpmadd52huq ymm14, ymm18, ymm29
	vpxorq ymm13, ymm13, ymm13
	vpmadd52luq ymm13, ymm25, ymm21
	vpmadd52luq ymm13, ymm19, ymm29
	vpaddq ymm14, ymm14, ymm13
	vpaddq ymm14, ymm14, ymm14
	vpmadd52huq ymm14, ymm25, ymm25
	vpxorq ymm13, ymm13, ymm13
	vpmadd52huq ymm13, ymm25, ymm21
	vpmadd52huq ymm13, ymm19, ymm29
	vpmadd52luq ymm13, ymm25, ymm29
	vpaddq ymm13, ymm13, ymm13
	vpmadd52luq ymm13, ymm21, ymm21
	vpxorq ymm12, ymm12, ymm12
	vpmadd52huq ymm12, ymm25, ymm29
	vpmadd52luq ymm12, ymm21, ymm29
	vpaddq ymm12, ymm12, ymm12
	vpmadd52huq ymm12, ymm21, ymm21
	vpxorq ymm11, ymm11, ymm11
	vpmadd52huq ymm11, ymm21, ymm29
	vpaddq ymm11, ymm11, ymm11
	vpmadd52luq ymm11, ymm29, ymm29
	vpxorq ymm10, ymm10, ymm10
	vpmadd52huq ymm10, ymm29, ymm29
	vmovdqu64 ymm6, YMMWORD PTR [r10+256]
	vpandq ymm6, ymm26, ymm6
	vpsrlq ymm0, ymm26, 52
	vmovdqu64 YMMWORD PTR [rdi+4640], ymm29
	vpsllq ymm29, ymm26, 56
	vpsrlq ymm29, ymm29, 12
	vpaddq ymm20, ymm20, ymm0
	vpaddq ymm29, ymm20, ymm29
	vpsrlq ymm20, ymm6, 8
	vpaddq ymm20, ymm17, ymm20
	vpmadd52luq ymm16, ymm26, YMMWORD PTR [r10+288]
	vpmadd52huq ymm15, ymm26, YMMWORD PTR [r10+288]
	vpmadd52luq ymm15, ymm26, YMMWORD PTR [r10+320]
	vpmadd52huq ymm14, ymm26, YMMWORD PTR [r10+320]
	vmovdqu64 ymm26, YMMWORD PTR [r10+256]
	vpandq ymm26, ymm29, ymm26
	vpsrlq ymm17, ymm29, 52
	vpsllq ymm6, ymm29, 56
	vpsrlq ymm6, ymm6, 12
	vpaddq ymm20, ymm20, ymm17
	vpaddq ymm20, ymm20, ymm6
	vpsrlq ymm26, ymm26, 8
	vpaddq ymm26, ymm16, ymm26
	vpmadd52luq ymm15, ymm29, YMMWORD PTR [r10+288]
	vpmadd52huq ymm14, ymm29, YMMWORD PTR [r10+288]
	vpmadd52luq ymm14, ymm29, YMMWORD PTR [r10+320]
	vpmadd52huq ymm13, ymm29, YMMWORD PTR [r10+320]
	vmovdqu64 ymm29, YMMWORD PTR [r10+256]
	vpandq ymm29, ymm20, ymm29
	vpsrlq ymm17, ymm20, 52
	vpsllq ymm16, ymm20, 56
	vpsrlq ymm16, ymm16, 12
	vpaddq ymm26, ymm26, ymm17
	vpaddq ymm26, ymm26, ymm16
	vpsrlq ymm29, ymm29, 8
	vpaddq ymm29, ymm15, ymm29
	vpmadd52luq ymm14, ymm20, YMMWORD PTR [r10+288]
	vpmadd52huq ymm13, ymm20, YMMWORD PTR [r10+288]
	vpmadd52luq ymm13, ymm20, YMMWORD PTR [r10+320]
	vpmadd52huq ymm12, ymm20, YMMWORD PTR [r10+320]
	vmovdqu64 ymm20, YMMWORD PTR [r10+256]
	vpandq ymm20, ymm26, ymm20
	vpsrlq ymm17, ymm26, 52
	vpsllq ymm16, ymm26, 56
	vpsrlq ymm16, ymm16, 12
	vpaddq ymm29, ymm29, ymm17
	vpaddq ymm29, ymm29, ymm16
	vpsrlq ymm20, ymm20, 8
	vpaddq ymm20, ymm14, ymm20
	vpmadd52luq ymm13, ymm26, YMMWORD PTR [r10+288]
	vpmadd52huq ymm12, ymm26, YMMWORD PTR [r10+288]
	vpmadd52luq ymm12, ymm26, YMMWORD PTR [r10+320]
	vpmadd52huq ymm11, ymm26, YMMWORD PTR [r10+320]
	vmovdqu64 ymm26, YMMWORD PTR [r10+256]
	vpandq ymm26, ymm29, ymm26
	vpsrlq ymm17, ymm29, 52
	vpsllq ymm16, ymm29, 56
	vpsrlq ymm16, ymm16, 12
	vpaddq ymm20, ymm20, ymm17
	vpaddq ymm20, ymm20, ymm16
	vpsrlq ymm26, ymm26, 8
	vpaddq ymm26, ymm13, ymm26
	vpmadd52luq ymm12, ymm29, YMMWORD PTR [r10+288]
	vpmadd52huq ymm11, ymm29, YMMWORD PTR [r10+288]
	vpmadd52luq ymm11, ymm29, YMMWORD PTR [r10+320]
	vpmadd52huq ymm10, ymm29, YMMWORD PTR [r10+320]
	vpermq ymm29, ymm20, 102
	vpermq ymm17, ymm26, 102
	vpermq ymm16, ymm12, 102
	vpermq ymm15, ymm11, 102
	vpermq ymm14, ymm10, 102
	vpsubq ymm29, ymm29, ymm20
	vpsubq ymm17, ymm17, ymm26
	vpsubq ymm16, ymm16, ymm12
	vpsubq ymm15, ymm15, ymm11
	vpsubq ymm14, ymm14, ymm10
	vpsubq ymm29, ymm29, ymm24
	vpsubq ymm30, ymm17, ymm30
	vpsubq ymm24, ymm16, ymm9
	vpsubq ymm17, ymm15, ymm8
	vpsubq ymm16, ymm14, ymm7
	vpsllq ymm15, ymm5, 4
	vpsllq ymm14, ymm4, 4
	vpsllq ymm13, ymm3, 4
	vpsllq ymm9, ymm2, 4
	vpsllq ymm8, ymm1, 4
	vpsubq ymm29, ymm29, ymm15
	vpsubq ymm30, ymm30, ymm14
	vpsubq ymm24, ymm24, ymm13
	vpsubq ymm17, ymm17, ymm9
	vpsubq ymm16, ymm16, ymm8
	vmovdqu64 ymm15, YMMWORD PTR [rdi+4640]
	vmovdqa64 ymm0, ymm29
	vmovdqa64 ymm1, ymm30
	vmovdqa64 ymm2, ymm24
	vmovdqa64 ymm3, ymm17
	vmovdqa64 ymm4, ymm16
	vmovdqa64 ymm5, ymm22
	vmovdqa64 ymm6, ymm23
	vmovdqa64 ymm7, ymm27
	vmovdqa64 ymm8, ymm28
	vmovdqa64 ymm9, ymm31
	vmovdqa64 ymm13, ymm21
	vmovdqa64 ymm14, ymm15
	vmovdqa64 ymm15, ymm20
	vmovdqa64 ymm16, ymm26
	vmovdqa64 ymm17, ymm12
	vmovdqa64 ymm12, ymm25
	vmovdqa64 ymm31, ymm18
	vmovdqa64 ymm18, ymm11
	vmovdqa64 ymm11, ymm19
	vmovdqa64 ymm19, ymm10
	vmovdqa64 ymm10, ymm31
	sub r11, 1
	jne 26b
	vmovdqu64 YMMWORD PTR [rdi+4512], ymm0
	vmovdqu64 YMMWORD PTR [rdi+4544], ymm1
	vmovdqu64 YMMWORD PTR [rdi+4576], ymm2
	vmovdqu64 YMMWORD PTR [rdi+4608], ymm3
	vmovdqu64 YMMWORD PTR [rdi+4640], ymm4
	vmovdqu64 YMMWORD PTR [rdi+4672], ymm5
	vmovdqu64 YMMWORD PTR [rdi+4704], ymm6
	vmovdqu64 YMMWORD PTR [rdi+4736], ymm7
	vmovdqu64 YMMWORD PTR [rdi+4768], ymm8
	vmovdqu64 YMMWORD PTR [rdi+4800], ymm9
	vmovdqu64 YMMWORD PTR [rdi+4832], ymm10
	vmovdqu64 YMMWORD PTR [rdi+4864], ymm11
	vmovdqu64 YMMWORD PTR [rdi+4896], ymm12
	vmovdqu64 YMMWORD PTR [rdi+4928], ymm13
	vmovdqu64 YMMWORD PTR [rdi+4960], ymm14
	vmovdqu64 YMMWORD PTR [rdi+4992], ymm15
	vmovdqu64 YMMWORD PTR [rdi+5024], ymm16
	vmovdqu64 YMMWORD PTR [rdi+5056], ymm17
	vmovdqu64 YMMWORD PTR [rdi+5088], ymm18
	vmovdqu64 YMMWORD PTR [rdi+5120], ymm19
	sub rdi, 992
	mov rax, rbx
	mov ecx, 5
	mul rcx
	mov rcx, rax
	mov eax, 0
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2405]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2404]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2403]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2402]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2401]
	add rax, rdx
	mov rdx, rax
	shr rdx, 4
	sub rdx, 1
	xor rax, rdx
	and rax, 15
	add rax, 1
	mov r8, rax
	mov rdx, rdi
	add rdx, 2752
	vmovq xmm13, r8
	vpbroadcastd ymm13, xmm13
	mov ecx, 1
	vmovq xmm12, rcx
	vpbroadcastd ymm12, xmm12
	vmovdqa ymm14, ymm12
	vpxor ymm0, ymm0, ymm0
	vpxor ymm1, ymm1, ymm1
	vpxor ymm2, ymm2, ymm2
	vpxor ymm3, ymm3, ymm3
	vpxor ymm4, ymm4, ymm4
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+32]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+64]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+96]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+128]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+160]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+192]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+224]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+256]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+288]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+320]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+352]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+384]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+416]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+448]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+480]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+512]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+544]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+576]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+608]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+640]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+672]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+704]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+736]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+768]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+800]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+832]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+864]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+896]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+928]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+960]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+992]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1024]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1056]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1088]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1120]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1152]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1184]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1216]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1248]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1280]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1312]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1344]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1376]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1408]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1440]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1472]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1504]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1536]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1568]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1600]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1632]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1664]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1696]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1728]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1760]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1792]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1824]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1856]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1888]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1920]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1952]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1984]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2016]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2048]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2080]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2112]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2144]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2176]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2208]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2240]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2272]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2304]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2336]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2368]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2400]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2432]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2464]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2496]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2528]
	vpor ymm4, ymm4, ymm11
	vmovdqu YMMWORD PTR [rdi+5312], ymm0
	vmovdqu YMMWORD PTR [rdi+5344], ymm1
	vmovdqu YMMWORD PTR [rdi+5376], ymm2
	vmovdqu YMMWORD PTR [rdi+5408], ymm3
	vmovdqu YMMWORD PTR [rdi+5440], ymm4
	vzeroupper
	mov r8, QWORD PTR [rdi+160]
	mov r9, QWORD PTR [rdi+168]
	mov r10, QWORD PTR [rdi+176]
	mov r11, QWORD PTR [rdi+184]
	sub r8, QWORD PTR [rdi+5344]
	sbb r9, QWORD PTR [rdi+5352]
	sbb r10, QWORD PTR [rdi+5360]
	sbb r11, QWORD PTR [rdi+5368]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+1024], r8
	mov QWORD PTR [rdi+1032], r9
	mov QWORD PTR [rdi+1040], r10
	mov QWORD PTR [rdi+1048], r11
	mov rax, rbx
	mov ecx, 5
	mul rcx
	mov rcx, rax
	movzx eax, BYTE PTR [rdi+rcx*1+2405]
	sub rax, 1
	mov rcx, rax
	mov rax, QWORD PTR [rdi+5344]
	mov rdx, QWORD PTR [rdi+1024]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+5344], rax
	mov rax, QWORD PTR [rdi+5352]
	mov rdx, QWORD PTR [rdi+1032]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+5352], rax
	mov rax, QWORD PTR [rdi+5360]
	mov rdx, QWORD PTR [rdi+1040]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+5360], rax
	mov rax, QWORD PTR [rdi+5368]
	mov rdx, QWORD PTR [rdi+1048]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+5368], rax
	mov r10, rdi
	add r10, 6400
	mov r9, r10
	add r9, 128
	mov rcx, rdi
	add rcx, 5312
	mov rdx, rdi
	add rdx, 5408
	add rdi, 992
	vmovdqu64 ymm0, YMMWORD PTR [rdi+4512]
	vmovdqu64 ymm1, YMMWORD PTR [rdi+4544]
	vmovdqu64 ymm2, YMMWORD PTR [rdi+4576]
	vmovdqu64 ymm3, YMMWORD PTR [rdi+4608]
	vmovdqu64 ymm4, YMMWORD PTR [rdi+4640]
	vmovdqu64 ymm5, YMMWORD PTR [rdi+4672]
	vmovdqu64 ymm6, YMMWORD PTR [rdi+4704]
	vmovdqu64 ymm7, YMMWORD PTR [rdi+4736]
	vmovdqu64 ymm8, YMMWORD PTR [rdi+4768]
	vmovdqu64 ymm9, YMMWORD PTR [rdi+4800]
	vmovdqu64 ymm10, YMMWORD PTR [rdi+4832]
	vmovdqu64 ymm11, YMMWORD PTR [rdi+4864]
	vmovdqu64 ymm12, YMMWORD PTR [rdi+4896]
	vmovdqu64 ymm13, YMMWORD PTR [rdi+4928]
	vmovdqu64 ymm14, YMMWORD PTR [rdi+4960]
	vmovdqu64 ymm15, YMMWORD PTR [rdi+4992]
	vmovdqu64 ymm16, YMMWORD PTR [rdi+5024]
	vmovdqu64 ymm17, YMMWORD PTR [rdi+5056]
	vmovdqu64 ymm18, YMMWORD PTR [rdi+5088]
	vmovdqu64 ymm19, YMMWORD PTR [rdi+5120]
	vmovdqu64 ymm31, YMMWORD PTR [rcx]
	vmovdqu64 ymm30, YMMWORD PTR [rcx+32]
	vmovdqu64 ymm29, YMMWORD PTR [rcx+64]
	vmovdqu64 ymm28, YMMWORD PTR [rdx]
	vmovdqu64 ymm27, YMMWORD PTR [rdx+32]
	vpermq ymm26, ymm28, 0
	vpermq ymm25, ymm31, 0
	vmovdqu64 ymm24, YMMWORD PTR [r10]
	vpternlogq ymm26, ymm25, ymm24, 216
	vpermq ymm25, ymm29, 0
	vmovdqu64 ymm24, YMMWORD PTR [r10+352]
	vpternlogq ymm26, ymm25, ymm24, 216
	vpermq ymm25, ymm30, 0
	vmovdqu64 ymm24, YMMWORD PTR [r10+32]
	vpternlogq ymm26, ymm25, ymm24, 216
	vpermq ymm25, ymm28, 85
	vpermq ymm24, ymm31, 85
	vmovdqu64 ymm23, YMMWORD PTR [r10]
	vpternlogq ymm25, ymm24, ymm23, 216
	vpermq ymm24, ymm29, 85
	vmovdqu64 ymm23, YMMWORD PTR [r10+352]
	vpternlogq ymm25, ymm24, ymm23, 216
	vpermq ymm24, ymm30, 85
	vmovdqu64 ymm23, YMMWORD PTR [r10+32]
	vpternlogq ymm25, ymm24, ymm23, 216
	vpermq ymm24, ymm28, 170
	vpermq ymm23, ymm31, 170
	vmovdqu64 ymm22, YMMWORD PTR [r10]
	vpternlogq ymm24, ymm23, ymm22, 216
	vpermq ymm23, ymm29, 170
	vmovdqu64 ymm22, YMMWORD PTR [r10+352]
	vpternlogq ymm24, ymm23, ymm22, 216
	vpermq ymm23, ymm30, 170
	vmovdqu64 ymm22, YMMWORD PTR [r10+32]
	vpternlogq ymm24, ymm23, ymm22, 216
	vpermq ymm28, ymm28, 255
	vpermq ymm31, ymm31, 255
	vmovdqu64 ymm23, YMMWORD PTR [r10]
	vpternlogq ymm28, ymm31, ymm23, 216
	vpermq ymm31, ymm29, 255
	vmovdqu64 ymm29, YMMWORD PTR [r10+352]
	vpternlogq ymm28, ymm31, ymm29, 216
	vpermq ymm31, ymm30, 255
	vmovdqu64 ymm30, YMMWORD PTR [r10+32]
	vpternlogq ymm28, ymm31, ymm30, 216
	vpsllq ymm31, ymm26, 2
	vmovdqu64 ymm30, YMMWORD PTR [r10+256]
	vpandq ymm30, ymm31, ymm30
	vpsrlq ymm31, ymm26, 50
	vpsllq ymm29, ymm25, 14
	vpaddq ymm31, ymm31, ymm29
	vmovdqu64 ymm29, YMMWORD PTR [r10+256]
	vpandq ymm29, ymm31, ymm29
	vpsrlq ymm31, ymm25, 38
	vpsllq ymm26, ymm24, 26
	vpaddq ymm31, ymm31, ymm26
	vmovdqu64 ymm26, YMMWORD PTR [r10+256]
	vpandq ymm26, ymm31, ymm26
	vpsrlq ymm31, ymm24, 26
	vpsllq ymm25, ymm28, 38
	vpaddq ymm31, ymm31, ymm25
	vmovdqu64 ymm25, YMMWORD PTR [r10+256]
	vpandq ymm25, ymm31, ymm25
	vpsrlq ymm31, ymm28, 14
	vmovdqu64 ymm28, YMMWORD PTR [r10+352]
	vpandq ymm28, ymm30, ymm28
	vpaddq ymm30, ymm30, ymm28
	vmovdqu64 ymm28, YMMWORD PTR [r10+352]
	vpandq ymm28, ymm29, ymm28
	vpaddq ymm29, ymm29, ymm28
	vmovdqu64 ymm28, YMMWORD PTR [r10+352]
	vpandq ymm28, ymm26, ymm28
	vpaddq ymm28, ymm26, ymm28
	vmovdqu64 ymm26, YMMWORD PTR [r10+352]
	vpandq ymm26, ymm25, ymm26
	vpaddq ymm26, ymm25, ymm26
	vmovdqu64 ymm25, YMMWORD PTR [r10+352]
	vpandq ymm25, ymm31, ymm25
	vpaddq ymm31, ymm31, ymm25
	vpsraq ymm25, ymm31, 48
	vmovdqu64 ymm24, YMMWORD PTR [r10+224]
	vpandq ymm24, ymm31, ymm24
	vpaddq ymm31, ymm30, ymm25
	vpsllq ymm30, ymm25, 44
	vpsubq ymm30, ymm29, ymm30
	vpsllq ymm29, ymm25, 36
	vpsubq ymm29, ymm26, ymm29
	vpsllq ymm26, ymm25, 16
	vpaddq ymm26, ymm24, ymm26
	vpsraq ymm25, ymm31, 52
	vmovdqu64 ymm24, YMMWORD PTR [r10+256]
	vpandq ymm24, ymm31, ymm24
	vpaddq ymm31, ymm30, ymm25
	vpsraq ymm30, ymm31, 52
	vmovdqu64 ymm25, YMMWORD PTR [r10+256]
	vpandq ymm25, ymm31, ymm25
	vpaddq ymm31, ymm28, ymm30
	vpsraq ymm30, ymm31, 52
	vmovdqu64 ymm28, YMMWORD PTR [r10+256]
	vpandq ymm28, ymm31, ymm28
	vpaddq ymm31, ymm29, ymm30
	vpsraq ymm30, ymm31, 52
	vmovdqu64 ymm29, YMMWORD PTR [r10+256]
	vpandq ymm29, ymm31, ymm29
	vpaddq ymm31, ymm26, ymm30
	vpermq ymm30, ymm27, 85
	vpermq ymm26, ymm27, 170
	vpermq ymm23, ymm27, 255
	vpsllq ymm22, ymm27, 1
	vmovdqu64 ymm21, YMMWORD PTR [r10+256]
	vpandq ymm21, ymm22, ymm21
	vpsrlq ymm27, ymm27, 51
	vpsllq ymm22, ymm30, 13
	vpaddq ymm27, ymm27, ymm22
	vmovdqu64 ymm22, YMMWORD PTR [r10+256]
	vpandq ymm22, ymm27, ymm22
	vpsrlq ymm30, ymm30, 39
	vpsllq ymm27, ymm26, 25
	vpaddq ymm30, ymm30, ymm27
	vmovdqu64 ymm27, YMMWORD PTR [r10+256]
	vpandq ymm27, ymm30, ymm27
	vpsrlq ymm30, ymm26, 27
	vpsllq ymm26, ymm23, 37
	vpaddq ymm30, ymm30, ymm26
	vmovdqu64 ymm26, YMMWORD PTR [r10+256]
	vpandq ymm26, ymm30, ymm26
	vpsrlq ymm30, ymm23, 15
	vmovdqa64 ymm20, ymm24
	vmovdqa64 ymm23, ymm29
	vmovdqa64 ymm24, ymm31
	vmovdqa64 ymm29, ymm30
	vmovdqa64 ymm31, ymm25
	vmovdqa64 ymm25, ymm21
	vmovdqa64 ymm21, ymm31
	vmovdqa64 ymm31, ymm28
	vmovdqa64 ymm28, ymm26
	vmovdqa64 ymm26, ymm22
	vmovdqa64 ymm22, ymm31
	vmovdqu64 ymm31, YMMWORD PTR [r9]
	vpermq ymm30, ymm10, 87
	vpermq ymm19, ymm11, 87
	vpermq ymm18, ymm12, 87
	vpermq ymm17, ymm13, 87
	vpermq ymm16, ymm14, 87
	vpermq ymm15, ymm5, 85
	vpermq ymm6, ymm6, 85
	vpermq ymm7, ymm7, 85
	vpermq ymm8, ymm8, 85
	vpermq ymm9, ymm9, 85
	vmovdqu64 ymm5, YMMWORD PTR [r10+672]
	vpternlogq ymm30, ymm15, ymm5, 216
	vmovdqu64 ymm15, YMMWORD PTR [r10+672]
	vpternlogq ymm19, ymm6, ymm15, 216
	vmovdqu64 ymm15, YMMWORD PTR [r10+672]
	vpternlogq ymm18, ymm7, ymm15, 216
	vmovdqu64 ymm15, YMMWORD PTR [r10+672]
	vpternlogq ymm17, ymm8, ymm15, 216
	vmovdqu64 ymm15, YMMWORD PTR [r10+672]
	vpternlogq ymm16, ymm9, ymm15, 216
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm30, ymm20
	vpxorq ymm9, ymm9, ymm9
	vpmadd52huq ymm9, ymm30, ymm20
	vpmadd52luq ymm9, ymm19, ymm20
	vpmadd52luq ymm9, ymm30, ymm21
	vpxorq ymm8, ymm8, ymm8
	vpmadd52huq ymm8, ymm19, ymm20
	vpmadd52luq ymm8, ymm19, ymm21
	vpmadd52luq ymm8, ymm30, ymm22
	vpxorq ymm7, ymm7, ymm7
	vpmadd52huq ymm7, ymm30, ymm21
	vpmadd52luq ymm7, ymm18, ymm20
	vpaddq ymm8, ymm8, ymm7
	vpxorq ymm7, ymm7, ymm7
	vpmadd52huq ymm7, ymm19, ymm21
	vpmadd52luq ymm7, ymm18, ymm21
	vpmadd52luq ymm7, ymm30, ymm23
	vpxorq ymm6, ymm6, ymm6
	vpmadd52huq ymm6, ymm18, ymm20
	vpmadd52luq ymm6, ymm19, ymm22
	vpxorq ymm5, ymm5, ymm5
	vpmadd52huq ymm5, ymm30, ymm22
	vpmadd52luq ymm5, ymm17, ymm20
	vpaddq ymm7, ymm7, ymm6
	vpaddq ymm7, ymm7, ymm5
	vpxorq ymm6, ymm6, ymm6
	vpmadd52huq ymm6, ymm18, ymm21
	vpmadd52huq ymm6, ymm17, ymm20
	vpmadd52luq ymm6, ymm19, ymm23
	vpxorq ymm5, ymm5, ymm5
	vpmadd52huq ymm5, ymm19, ymm22
	vpmadd52huq ymm5, ymm30, ymm23
	vpmadd52luq ymm5, ymm16, ymm20
	vmovdqu64 YMMWORD PTR [rdi+4512], ymm29
	vpxorq ymm29, ymm29, ymm29
	vpmadd52luq ymm29, ymm18, ymm22
	vpmadd52luq ymm29, ymm17, ymm21
	vpmadd52luq ymm29, ymm30, ymm24
	vpaddq ymm6, ymm6, ymm5
	vpaddq ymm29, ymm6, ymm29
	vpxorq ymm6, ymm6, ymm6
	vpmadd52huq ymm6, ymm18, ymm22
	vpmadd52luq ymm6, ymm17, ymm22
	vpmadd52huq ymm6, ymm30, ymm24
	vpxorq ymm30, ymm30, ymm30
	vpmadd52huq ymm30, ymm17, ymm21
	vpmadd52luq ymm30, ymm18, ymm23
	vpmadd52luq ymm30, ymm16, ymm21
	vpxorq ymm5, ymm5, ymm5
	vpmadd52huq ymm5, ymm19, ymm23
	vpmadd52huq ymm5, ymm16, ymm20
	vpmadd52luq ymm5, ymm19, ymm24
	vpaddq ymm30, ymm6, ymm30
	vpaddq ymm30, ymm30, ymm5
	vpxorq ymm20, ymm20, ymm20
	vpmadd52huq ymm20, ymm17, ymm22
	vpmadd52huq ymm20, ymm16, ymm21
	vpmadd52luq ymm20, ymm18, ymm24
	vpxorq ymm21, ymm21, ymm21
	vpmadd52huq ymm21, ymm18, ymm23
	vpmadd52huq ymm21, ymm19, ymm24
	vpxorq ymm19, ymm19, ymm19
	vpmadd52luq ymm19, ymm17, ymm23
	vpmadd52luq ymm19, ymm16, ymm22
	vpaddq ymm21, ymm20, ymm21
	vpaddq ymm21, ymm21, ymm19
	vpxorq ymm20, ymm20, ymm20
	vpmadd52huq ymm20, ymm17, ymm23
	vpmadd52huq ymm20, ymm18, ymm24
	vpmadd52luq ymm20, ymm17, ymm24
	vpxorq ymm19, ymm19, ymm19
	vpmadd52huq ymm19, ymm16, ymm22
	vpmadd52luq ymm19, ymm16, ymm23
	vpaddq ymm22, ymm20, ymm19
	vpxorq ymm20, ymm20, ymm20
	vpmadd52huq ymm20, ymm16, ymm23
	vpmadd52huq ymm20, ymm17, ymm24
	vpmadd52luq ymm20, ymm16, ymm24
	vpxorq ymm23, ymm23, ymm23
	vpmadd52huq ymm23, ymm16, ymm24
	vmovdqu64 ymm24, YMMWORD PTR [r10+256]
	vpandq ymm24, ymm15, ymm24
	vpsrlq ymm19, ymm15, 52
	vpsllq ymm18, ymm15, 56
	vpsrlq ymm18, ymm18, 12
	vpaddq ymm19, ymm9, ymm19
	vpaddq ymm19, ymm19, ymm18
	vpsrlq ymm24, ymm24, 8
	vpaddq ymm24, ymm8, ymm24
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r10+288]
	vpmadd52huq ymm29, ymm15, YMMWORD PTR [r10+288]
	vpmadd52luq ymm29, ymm15, YMMWORD PTR [r10+320]
	vpmadd52huq ymm30, ymm15, YMMWORD PTR [r10+320]
	vmovdqu64 ymm18, YMMWORD PTR [r10+256]
	vpandq ymm18, ymm19, ymm18
	vpsrlq ymm17, ymm19, 52
	vpsllq ymm16, ymm19, 56
	vpsrlq ymm16, ymm16, 12
	vpaddq ymm24, ymm24, ymm17
	vpaddq ymm24, ymm24, ymm16
	vpsrlq ymm18, ymm18, 8
	vpaddq ymm18, ymm7, ymm18
	vpmadd52luq ymm29, ymm19, YMMWORD PTR [r10+288]
	vpmadd52huq ymm30, ymm19, YMMWORD PTR [r10+288]
	vpmadd52luq ymm30, ymm19, YMMWORD PTR [r10+320]
	vpmadd52huq ymm21, ymm19, YMMWORD PTR [r10+320]
	vmovdqu64 ymm19, YMMWORD PTR [r10+256]
	vpandq ymm19, ymm24, ymm19
	vpsrlq ymm17, ymm24, 52
	vpsllq ymm16, ymm24, 56
	vpsrlq ymm16, ymm16, 12
	vpaddq ymm18, ymm18, ymm17
	vpaddq ymm18, ymm18, ymm16
	vpsrlq ymm19, ymm19, 8
	vpaddq ymm29, ymm29, ymm19
	vpmadd52luq ymm30, ymm24, YMMWORD PTR [r10+288]
	vpmadd52huq ymm21, ymm24, YMMWORD PTR [r10+288]
	vpmadd52luq ymm21, ymm24, YMMWORD PTR [r10+320]
	vpmadd52huq ymm22, ymm24, YMMWORD PTR [r10+320]
	vmovdqu64 ymm24, YMMWORD PTR [r10+256]
	vpandq ymm24, ymm18, ymm24
	vpsrlq ymm19, ymm18, 52
	vpsllq ymm17, ymm18, 56
	vpsrlq ymm17, ymm17, 12
	vpaddq ymm29, ymm29, ymm19
	vpaddq ymm29, ymm29, ymm17
	vpsrlq ymm24, ymm24, 8
	vpaddq ymm30, ymm30, ymm24
	vpmadd52luq ymm21, ymm18, YMMWORD PTR [r10+288]
	vpmadd52huq ymm22, ymm18, YMMWORD PTR [r10+288]
	vpmadd52luq ymm22, ymm18, YMMWORD PTR [r10+320]
	vpmadd52huq ymm20, ymm18, YMMWORD PTR [r10+320]
	vmovdqu64 ymm24, YMMWORD PTR [r10+256]
	vpandq ymm24, ymm29, ymm24
	vpsrlq ymm19, ymm29, 52
	vpsllq ymm18, ymm29, 56
	vpsrlq ymm18, ymm18, 12
	vpaddq ymm30, ymm30, ymm19
	vpaddq ymm30, ymm30, ymm18
	vpsrlq ymm24, ymm24, 8
	vpaddq ymm24, ymm21, ymm24
	vpmadd52luq ymm22, ymm29, YMMWORD PTR [r10+288]
	vpmadd52huq ymm20, ymm29, YMMWORD PTR [r10+288]
	vpmadd52luq ymm20, ymm29, YMMWORD PTR [r10+320]
	vpmadd52huq ymm23, ymm29, YMMWORD PTR [r10+320]
	vpermq ymm29, ymm30, 0
	vpermq ymm21, ymm24, 0
	vpermq ymm19, ymm22, 0
	vpermq ymm18, ymm20, 0
	vpermq ymm17, ymm23, 0
	vpermq ymm30, ymm30, 156
	vpermq ymm24, ymm24, 156
	vpermq ymm22, ymm22, 156
	vpermq ymm20, ymm20, 156
	vpermq ymm23, ymm23, 156
	vmovdqu64 ymm16, YMMWORD PTR [r10+352]
	vpandq ymm16, ymm29, ymm16
	vpsubq ymm30, ymm30, ymm16
	vmovdqu64 ymm16, YMMWORD PTR [r10+352]
	vpandq ymm16, ymm21, ymm16
	vpsubq ymm24, ymm24, ymm16
	vmovdqu64 ymm16, YMMWORD PTR [r10+352]
	vpandq ymm16, ymm19, ymm16
	vpsubq ymm22, ymm22, ymm16
	vmovdqu64 ymm16, YMMWORD PTR [r10+352]
	vpandq ymm16, ymm18, ymm16
	vpsubq ymm20, ymm20, ymm16
	vmovdqu64 ymm16, YMMWORD PTR [r10+352]
	vpandq ymm16, ymm17, ymm16
	vpsubq ymm23, ymm23, ymm16
	vpxorq ymm16, ymm16, ymm16
	vpsubq ymm15, ymm16, ymm30
	vpsubq ymm9, ymm16, ymm24
	vpsubq ymm8, ymm16, ymm22
	vpsubq ymm7, ymm16, ymm20
	vpsubq ymm16, ymm16, ymm23
	vpternlogq ymm30, ymm15, ymm31, 216
	vpternlogq ymm24, ymm9, ymm31, 216
	vpternlogq ymm22, ymm8, ymm31, 216
	vpternlogq ymm20, ymm7, ymm31, 216
	vpternlogq ymm23, ymm16, ymm31, 216
	vmovdqu64 ymm31, YMMWORD PTR [r10+704]
	vpternlogq ymm30, ymm0, ymm31, 216
	vmovdqu64 ymm31, YMMWORD PTR [r10+704]
	vpternlogq ymm24, ymm1, ymm31, 216
	vmovdqu64 ymm31, YMMWORD PTR [r10+704]
	vpternlogq ymm22, ymm2, ymm31, 216
	vmovdqu64 ymm31, YMMWORD PTR [r10+704]
	vpternlogq ymm20, ymm3, ymm31, 216
	vmovdqu64 ymm31, YMMWORD PTR [r10+704]
	vpternlogq ymm23, ymm4, ymm31, 216
	vmovdqu64 ymm31, YMMWORD PTR [r10+736]
	vpaddq ymm31, ymm30, ymm31
	vmovdqu64 ymm30, YMMWORD PTR [r10+768]
	vpaddq ymm30, ymm24, ymm30
	vmovdqu64 ymm24, YMMWORD PTR [r10+128]
	vpaddq ymm24, ymm22, ymm24
	vmovdqu64 ymm22, YMMWORD PTR [r10+800]
	vpaddq ymm22, ymm20, ymm22
	vmovdqu64 ymm20, YMMWORD PTR [r10+832]
	vpaddq ymm20, ymm23, ymm20
	vpsraq ymm23, ymm20, 48
	vmovdqu64 ymm16, YMMWORD PTR [r10+224]
	vpandq ymm16, ymm20, ymm16
	vpaddq ymm31, ymm31, ymm23
	vpsllq ymm20, ymm23, 44
	vpsubq ymm30, ymm30, ymm20
	vpsllq ymm20, ymm23, 36
	vpsubq ymm22, ymm22, ymm20
	vpsllq ymm23, ymm23, 16
	vpaddq ymm23, ymm16, ymm23
	vpsraq ymm20, ymm31, 52
	vmovdqu64 ymm16, YMMWORD PTR [r10+256]
	vpandq ymm16, ymm31, ymm16
	vpaddq ymm31, ymm30, ymm20
	vpsraq ymm30, ymm31, 52
	vmovdqu64 ymm20, YMMWORD PTR [r10+256]
	vpandq ymm20, ymm31, ymm20
	vpaddq ymm31, ymm24, ymm30
	vpsraq ymm30, ymm31, 52
	vmovdqu64 ymm24, YMMWORD PTR [r10+256]
	vpandq ymm24, ymm31, ymm24
	vpaddq ymm31, ymm22, ymm30
	vpsraq ymm30, ymm31, 52
	vmovdqu64 ymm22, YMMWORD PTR [r10+256]
	vpandq ymm22, ymm31, ymm22
	vpaddq ymm31, ymm23, ymm30
	vpermq ymm30, ymm16, 170
	vpermq ymm23, ymm20, 170
	vpermq ymm15, ymm24, 170
	vpermq ymm9, ymm22, 170
	vpermq ymm8, ymm31, 170
	vmovdqu64 ymm7, YMMWORD PTR [r10]
	vpternlogq ymm25, ymm10, ymm7, 216
	vmovdqu64 ymm10, YMMWORD PTR [r10]
	vpternlogq ymm26, ymm11, ymm10, 216
	vmovdqu64 ymm11, YMMWORD PTR [r10]
	vpternlogq ymm27, ymm12, ymm11, 216
	vmovdqu64 ymm12, YMMWORD PTR [r10]
	vpternlogq ymm28, ymm13, ymm12, 216
	vmovdqu64 ymm13, YMMWORD PTR [rdi+4512]
	vmovdqu64 ymm12, YMMWORD PTR [r10]
	vpternlogq ymm13, ymm14, ymm12, 216
	vmovdqu64 ymm14, YMMWORD PTR [r10+672]
	vpternlogq ymm25, ymm30, ymm14, 216
	vmovdqu64 ymm14, YMMWORD PTR [r10+672]
	vpternlogq ymm26, ymm23, ymm14, 216
	vmovdqu64 ymm14, YMMWORD PTR [r10+672]
	vpternlogq ymm27, ymm15, ymm14, 216
	vmovdqu64 ymm14, YMMWORD PTR [r10+672]
	vpternlogq ymm28, ymm9, ymm14, 216
	vmovdqu64 ymm14, YMMWORD PTR [r10+672]
	vpternlogq ymm13, ymm8, ymm14, 216
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm16, ymm25
	vpxorq ymm12, ymm12, ymm12
	vpmadd52huq ymm12, ymm16, ymm25
	vpmadd52luq ymm12, ymm20, ymm25
	vpmadd52luq ymm12, ymm16, ymm26
	vpxorq ymm11, ymm11, ymm11
	vpmadd52huq ymm11, ymm20, ymm25
	vpmadd52luq ymm11, ymm20, ymm26
	vpmadd52luq ymm11, ymm16, ymm27
	vpxorq ymm10, ymm10, ymm10
	vpmadd52huq ymm10, ymm16, ymm26
	vpmadd52luq ymm10, ymm24, ymm25
	vpaddq ymm11, ymm11, ymm10
	vpxorq ymm10, ymm10, ymm10
	vpmadd52huq ymm10, ymm20, ymm26
	vpmadd52luq ymm10, ymm24, ymm26
	vpmadd52luq ymm10, ymm16, ymm28
	vpxorq ymm7, ymm7, ymm7
	vpmadd52huq ymm7, ymm24, ymm25
	vpmadd52luq ymm7, ymm20, ymm27
	vpxorq ymm6, ymm6, ymm6
	vpmadd52huq ymm6, ymm16, ymm27
	vpmadd52luq ymm6, ymm22, ymm25
	vpaddq ymm10, ymm10, ymm7
	vpaddq ymm10, ymm10, ymm6
	vpxorq ymm7, ymm7, ymm7
	vpmadd52huq ymm7, ymm24, ymm26
	vpmadd52huq ymm7, ymm22, ymm25
	vpmadd52luq ymm7, ymm20, ymm28
	vpxorq ymm6, ymm6, ymm6
	vpmadd52huq ymm6, ymm20, ymm27
	vpmadd52huq ymm6, ymm16, ymm28
	vpmadd52luq ymm6, ymm31, ymm25
	vpxorq ymm5, ymm5, ymm5
	vpmadd52luq ymm5, ymm24, ymm27
	vpmadd52luq ymm5, ymm22, ymm26
	vpmadd52luq ymm5, ymm16, ymm13
	vpaddq ymm7, ymm7, ymm6
	vpaddq ymm7, ymm7, ymm5
	vpxorq ymm6, ymm6, ymm6
	vpmadd52huq ymm6, ymm24, ymm27
	vpmadd52luq ymm6, ymm22, ymm27
	vpmadd52huq ymm6, ymm16, ymm13
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm22, ymm26
	vpmadd52luq ymm16, ymm24, ymm28
	vpmadd52luq ymm16, ymm31, ymm26
	vpxorq ymm5, ymm5, ymm5
	vpmadd52huq ymm5, ymm20, ymm28
	vpmadd52huq ymm5, ymm31, ymm25
	vpmadd52luq ymm5, ymm20, ymm13
	vpaddq ymm25, ymm6, ymm16
	vpaddq ymm25, ymm25, ymm5
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm22, ymm27
	vpmadd52huq ymm16, ymm31, ymm26
	vpmadd52luq ymm16, ymm24, ymm13
	vpxorq ymm26, ymm26, ymm26
	vpmadd52huq ymm26, ymm24, ymm28
	vpmadd52huq ymm26, ymm20, ymm13
	vpxorq ymm20, ymm20, ymm20
	vpmadd52luq ymm20, ymm22, ymm28
	vpmadd52luq ymm20, ymm31, ymm27
	vpaddq ymm26, ymm16, ymm26
	vpaddq ymm26, ymm26, ymm20
	vpxorq ymm20, ymm20, ymm20
	vpmadd52huq ymm20, ymm22, ymm28
	vpmadd52huq ymm20, ymm24, ymm13
	vpmadd52luq ymm20, ymm22, ymm13
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm31, ymm27
	vpmadd52luq ymm24, ymm31, ymm28
	vpaddq ymm27, ymm20, ymm24
	vpxorq ymm24, ymm24, ymm24
	vpmadd52huq ymm24, ymm31, ymm28
	vpmadd52huq ymm24, ymm22, ymm13
	vpmadd52luq ymm24, ymm31, ymm13
	vpxorq ymm28, ymm28, ymm28
	vpmadd52huq ymm28, ymm31, ymm13
	vmovdqu64 ymm31, YMMWORD PTR [r10+256]
	vpandq ymm31, ymm14, ymm31
	vpsrlq ymm22, ymm14, 52
	vpsllq ymm20, ymm14, 56
	vpsrlq ymm20, ymm20, 12
	vpaddq ymm22, ymm12, ymm22
	vpaddq ymm22, ymm22, ymm20
	vpsrlq ymm31, ymm31, 8
	vpaddq ymm31, ymm11, ymm31
	vpmadd52luq ymm10, ymm14, YMMWORD PTR [r10+288]
	vpmadd52huq ymm7, ymm14, YMMWORD PTR [r10+288]
	vpmadd52luq ymm7, ymm14, YMMWORD PTR [r10+320]
	vpmadd52huq ymm25, ymm14, YMMWORD PTR [r10+320]
	vmovdqu64 ymm20, YMMWORD PTR [r10+256]
	vpandq ymm20, ymm22, ymm20
	vpsrlq ymm16, ymm22, 52
	vpsllq ymm14, ymm22, 56
	vpsrlq ymm14, ymm14, 12
	vpaddq ymm31, ymm31, ymm16
	vpaddq ymm31, ymm31, ymm14
	vpsrlq ymm20, ymm20, 8
	vpaddq ymm20, ymm10, ymm20
	vpmadd52luq ymm7, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm25, ymm22, YMMWORD PTR [r10+288]
	vpmadd52luq ymm25, ymm22, YMMWORD PTR [r10+320]
	vpmadd52huq ymm26, ymm22, YMMWORD PTR [r10+320]
	vmovdqu64 ymm22, YMMWORD PTR [r10+256]
	vpandq ymm22, ymm31, ymm22
	vpsrlq ymm16, ymm31, 52
	vpsllq ymm14, ymm31, 56
	vpsrlq ymm14, ymm14, 12
	vpaddq ymm20, ymm20, ymm16
	vpaddq ymm20, ymm20, ymm14
	vpsrlq ymm22, ymm22, 8
	vpaddq ymm22, ymm7, ymm22
	vpmadd52luq ymm25, ymm31, YMMWORD PTR [r10+288]
	vpmadd52huq ymm26, ymm31, YMMWORD PTR [r10+288]
	vpmadd52luq ymm26, ymm31, YMMWORD PTR [r10+320]
	vpmadd52huq ymm27, ymm31, YMMWORD PTR [r10+320]
	vmovdqu64 ymm31, YMMWORD PTR [r10+256]
	vpandq ymm31, ymm20, ymm31
	vpsrlq ymm16, ymm20, 52
	vpsllq ymm14, ymm20, 56
	vpsrlq ymm14, ymm14, 12
	vpaddq ymm22, ymm22, ymm16
	vpaddq ymm22, ymm22, ymm14
	vpsrlq ymm31, ymm31, 8
	vpaddq ymm31, ymm25, ymm31
	vpmadd52luq ymm26, ymm20, YMMWORD PTR [r10+288]
	vpmadd52huq ymm27, ymm20, YMMWORD PTR [r10+288]
	vpmadd52luq ymm27, ymm20, YMMWORD PTR [r10+320]
	vpmadd52huq ymm24, ymm20, YMMWORD PTR [r10+320]
	vmovdqu64 ymm25, YMMWORD PTR [r10+256]
	vpandq ymm25, ymm22, ymm25
	vpsrlq ymm20, ymm22, 52
	vpsllq ymm16, ymm22, 56
	vpsrlq ymm16, ymm16, 12
	vpaddq ymm31, ymm31, ymm20
	vpaddq ymm31, ymm31, ymm16
	vpsrlq ymm25, ymm25, 8
	vpaddq ymm26, ymm26, ymm25
	vpmadd52luq ymm27, ymm22, YMMWORD PTR [r10+288]
	vpmadd52huq ymm24, ymm22, YMMWORD PTR [r10+288]
	vpmadd52luq ymm24, ymm22, YMMWORD PTR [r10+320]
	vpmadd52huq ymm28, ymm22, YMMWORD PTR [r10+320]
	vpermq ymm25, ymm31, 141
	vpermq ymm22, ymm26, 141
	vpermq ymm20, ymm27, 141
	vpermq ymm16, ymm24, 141
	vpermq ymm14, ymm28, 141
	vmovdqu64 ymm13, YMMWORD PTR [r10]
	vpandq ymm13, ymm25, ymm13
	vpaddq ymm25, ymm25, ymm13
	vmovdqu64 ymm13, YMMWORD PTR [r10]
	vpandq ymm13, ymm22, ymm13
	vpaddq ymm22, ymm22, ymm13
	vmovdqu64 ymm13, YMMWORD PTR [r10]
	vpandq ymm13, ymm20, ymm13
	vpaddq ymm20, ymm20, ymm13
	vmovdqu64 ymm13, YMMWORD PTR [r10]
	vpandq ymm13, ymm16, ymm13
	vpaddq ymm16, ymm16, ymm13
	vmovdqu64 ymm13, YMMWORD PTR [r10]
	vpandq ymm13, ymm14, ymm13
	vpaddq ymm14, ymm14, ymm13
	vmovdqu64 ymm13, YMMWORD PTR [r10+704]
	vpandq ymm13, ymm31, ymm13
	vpsubq ymm25, ymm25, ymm13
	vmovdqu64 ymm13, YMMWORD PTR [r10+704]
	vpandq ymm13, ymm26, ymm13
	vpsubq ymm22, ymm22, ymm13
	vmovdqu64 ymm13, YMMWORD PTR [r10+704]
	vpandq ymm13, ymm27, ymm13
	vpsubq ymm20, ymm20, ymm13
	vmovdqu64 ymm13, YMMWORD PTR [r10+704]
	vpandq ymm13, ymm24, ymm13
	vpsubq ymm16, ymm16, ymm13
	vmovdqu64 ymm13, YMMWORD PTR [r10+704]
	vpandq ymm13, ymm28, ymm13
	vpsubq ymm14, ymm14, ymm13
	vmovdqu64 ymm13, YMMWORD PTR [r10+352]
	vpternlogq ymm25, ymm29, ymm13, 216
	vmovdqu64 ymm29, YMMWORD PTR [r10+352]
	vpternlogq ymm22, ymm21, ymm29, 216
	vmovdqu64 ymm29, YMMWORD PTR [r10+352]
	vpternlogq ymm20, ymm19, ymm29, 216
	vmovdqu64 ymm29, YMMWORD PTR [r10+352]
	vpternlogq ymm16, ymm18, ymm29, 216
	vmovdqu64 ymm29, YMMWORD PTR [r10+352]
	vpternlogq ymm14, ymm17, ymm29, 216
	vmovdqu64 ymm29, YMMWORD PTR [r10+864]
	vpaddq ymm29, ymm25, ymm29
	vmovdqu64 ymm25, YMMWORD PTR [r10+896]
	vpaddq ymm25, ymm22, ymm25
	vmovdqu64 ymm22, YMMWORD PTR [r10+128]
	vpaddq ymm22, ymm20, ymm22
	vmovdqu64 ymm21, YMMWORD PTR [r10+928]
	vpaddq ymm21, ymm16, ymm21
	vmovdqu64 ymm20, YMMWORD PTR [r10+960]
	vpaddq ymm20, ymm14, ymm20
	vpsraq ymm19, ymm20, 48
	vmovdqu64 ymm18, YMMWORD PTR [r10+224]
	vpandq ymm18, ymm20, ymm18
	vpaddq ymm29, ymm29, ymm19
	vpsllq ymm20, ymm19, 44
	vpsubq ymm25, ymm25, ymm20
	vpsllq ymm20, ymm19, 36
	vpsubq ymm21, ymm21, ymm20
	vpsllq ymm20, ymm19, 16
	vpaddq ymm20, ymm18, ymm20
	vpsraq ymm19, ymm29, 52
	vmovdqu64 ymm18, YMMWORD PTR [r10+256]
	vpandq ymm18, ymm29, ymm18
	vpaddq ymm29, ymm25, ymm19
	vpsraq ymm25, ymm29, 52
	vmovdqu64 ymm19, YMMWORD PTR [r10+256]
	vpandq ymm19, ymm29, ymm19
	vpaddq ymm29, ymm22, ymm25
	vpsraq ymm25, ymm29, 52
	vmovdqu64 ymm22, YMMWORD PTR [r10+256]
	vpandq ymm22, ymm29, ymm22
	vpaddq ymm29, ymm21, ymm25
	vpsraq ymm25, ymm29, 52
	vmovdqu64 ymm21, YMMWORD PTR [r10+256]
	vpandq ymm21, ymm29, ymm21
	vpaddq ymm29, ymm20, ymm25
	vpsraq ymm25, ymm28, 48
	vmovdqu64 ymm20, YMMWORD PTR [r10+224]
	vpandq ymm20, ymm28, ymm20
	vpaddq ymm31, ymm31, ymm25
	vpsllq ymm28, ymm25, 44
	vpsubq ymm28, ymm26, ymm28
	vpsllq ymm26, ymm25, 36
	vpsubq ymm26, ymm24, ymm26
	vpsllq ymm25, ymm25, 16
	vpaddq ymm25, ymm20, ymm25
	vpsraq ymm24, ymm31, 52
	vmovdqu64 ymm20, YMMWORD PTR [r10+256]
	vpandq ymm20, ymm31, ymm20
	vpaddq ymm31, ymm28, ymm24
	vpsraq ymm28, ymm31, 52
	vmovdqu64 ymm24, YMMWORD PTR [r10+256]
	vpandq ymm24, ymm31, ymm24
	vpaddq ymm31, ymm27, ymm28
	vpsraq ymm28, ymm31, 52
	vmovdqu64 ymm27, YMMWORD PTR [r10+256]
	vpandq ymm27, ymm31, ymm27
	vpaddq ymm31, ymm26, ymm28
	vpsraq ymm28, ymm31, 52
	vmovdqu64 ymm26, YMMWORD PTR [r10+256]
	vpandq ymm26, ymm31, ymm26
	vpaddq ymm31, ymm25, ymm28
	vmovdqu64 ymm28, YMMWORD PTR [r10+32]
	vmovdqa64 ymm25, ymm18
	vpternlogq ymm25, ymm30, ymm28, 216
	vmovdqu64 ymm30, YMMWORD PTR [r10+32]
	vmovdqa64 ymm28, ymm19
	vpternlogq ymm28, ymm23, ymm30, 216
	vmovdqu64 ymm30, YMMWORD PTR [r10+32]
	vmovdqa64 ymm23, ymm22
	vpternlogq ymm23, ymm15, ymm30, 216
	vmovdqu64 ymm30, YMMWORD PTR [r10+32]
	vmovdqa64 ymm17, ymm21
	vpternlogq ymm17, ymm9, ymm30, 216
	vmovdqu64 ymm30, YMMWORD PTR [r10+32]
	vmovdqa64 ymm16, ymm29
	vpternlogq ymm16, ymm8, ymm30, 216
	vpermq ymm30, ymm18, 255
	vpermq ymm15, ymm19, 255
	vpermq ymm14, ymm22, 255
	vpermq ymm13, ymm21, 255
	vpermq ymm12, ymm29, 255
	vmovdqu64 ymm11, YMMWORD PTR [r10+352]
	vmovdqa64 ymm10, ymm18
	vpternlogq ymm10, ymm30, ymm11, 216
	vmovdqu64 ymm30, YMMWORD PTR [r10+352]
	vmovdqa64 ymm11, ymm19
	vpternlogq ymm11, ymm15, ymm30, 216
	vmovdqu64 ymm30, YMMWORD PTR [r10+352]
	vmovdqa64 ymm15, ymm22
	vpternlogq ymm15, ymm14, ymm30, 216
	vmovdqu64 ymm30, YMMWORD PTR [r10+352]
	vmovdqa64 ymm14, ymm21
	vpternlogq ymm14, ymm13, ymm30, 216
	vmovdqu64 ymm30, YMMWORD PTR [r10+352]
	vmovdqa64 ymm13, ymm29
	vpternlogq ymm13, ymm12, ymm30, 216
	vpxorq ymm30, ymm30, ymm30
	vpmadd52luq ymm30, ymm25, ymm10
	vpxorq ymm12, ymm12, ymm12
	vpmadd52huq ymm12, ymm25, ymm10
	vpmadd52luq ymm12, ymm28, ymm10
	vpmadd52luq ymm12, ymm25, ymm11
	vpxorq ymm9, ymm9, ymm9
	vpmadd52huq ymm9, ymm28, ymm10
	vpmadd52luq ymm9, ymm28, ymm11
	vpmadd52luq ymm9, ymm25, ymm15
	vpxorq ymm8, ymm8, ymm8
	vpmadd52huq ymm8, ymm25, ymm11
	vpmadd52luq ymm8, ymm23, ymm10
	vpaddq ymm9, ymm9, ymm8
	vpxorq ymm8, ymm8, ymm8
	vpmadd52huq ymm8, ymm28, ymm11
	vpmadd52luq ymm8, ymm23, ymm11
	vpmadd52luq ymm8, ymm25, ymm14
	vpxorq ymm7, ymm7, ymm7
	vpmadd52huq ymm7, ymm23, ymm10
	vpmadd52luq ymm7, ymm28, ymm15
	vpxorq ymm6, ymm6, ymm6
	vpmadd52huq ymm6, ymm25, ymm15
	vpmadd52luq ymm6, ymm17, ymm10
	vpaddq ymm8, ymm8, ymm7
	vpaddq ymm8, ymm8, ymm6
	vpxorq ymm7, ymm7, ymm7
	vpmadd52huq ymm7, ymm23, ymm11
	vpmadd52huq ymm7, ymm17, ymm10
	vpmadd52luq ymm7, ymm28, ymm14
	vpxorq ymm6, ymm6, ymm6
	vpmadd52huq ymm6, ymm28, ymm15
	vpmadd52huq ymm6, ymm25, ymm14
	vpmadd52luq ymm6, ymm16, ymm10
	vpxorq ymm5, ymm5, ymm5
	vpmadd52luq ymm5, ymm23, ymm15
	vpmadd52luq ymm5, ymm17, ymm11
	vpmadd52luq ymm5, ymm25, ymm13
	vpaddq ymm7, ymm7, ymm6
	vpaddq ymm7, ymm7, ymm5
	vpxorq ymm6, ymm6, ymm6
	vpmadd52huq ymm6, ymm23, ymm15
	vpmadd52luq ymm6, ymm17, ymm15
	vpmadd52huq ymm6, ymm25, ymm13
	vpxorq ymm25, ymm25, ymm25
	vpmadd52huq ymm25, ymm17, ymm11
	vpmadd52luq ymm25, ymm23, ymm14
	vpmadd52luq ymm25, ymm16, ymm11
	vpxorq ymm5, ymm5, ymm5
	vpmadd52huq ymm5, ymm28, ymm14
	vpmadd52huq ymm5, ymm16, ymm10
	vpmadd52luq ymm5, ymm28, ymm13
	vpaddq ymm25, ymm6, ymm25
	vpaddq ymm25, ymm25, ymm5
	vpxorq ymm10, ymm10, ymm10
	vpmadd52huq ymm10, ymm17, ymm15
	vpmadd52huq ymm10, ymm16, ymm11
	vpmadd52luq ymm10, ymm23, ymm13
	vpxorq ymm11, ymm11, ymm11
	vpmadd52huq ymm11, ymm23, ymm14
	vpmadd52huq ymm11, ymm28, ymm13
	vpxorq ymm28, ymm28, ymm28
	vpmadd52luq ymm28, ymm17, ymm14
	vpmadd52luq ymm28, ymm16, ymm15
	vpaddq ymm11, ymm10, ymm11
	vpaddq ymm28, ymm11, ymm28
	vpxorq ymm11, ymm11, ymm11
	vpmadd52huq ymm11, ymm17, ymm14
	vpmadd52huq ymm11, ymm23, ymm13
	vpmadd52luq ymm11, ymm17, ymm13
	vpxorq ymm23, ymm23, ymm23
	vpmadd52huq ymm23, ymm16, ymm15
	vpmadd52luq ymm23, ymm16, ymm14
	vpaddq ymm23, ymm11, ymm23
	vpxorq ymm15, ymm15, ymm15
	vpmadd52huq ymm15, ymm16, ymm14
	vpmadd52huq ymm15, ymm17, ymm13
	vpmadd52luq ymm15, ymm16, ymm13
	vpxorq ymm17, ymm17, ymm17
	vpmadd52huq ymm17, ymm16, ymm13
	vmovdqu64 ymm16, YMMWORD PTR [r10+256]
	vpandq ymm16, ymm30, ymm16
	vpsrlq ymm14, ymm30, 52
	vpsllq ymm13, ymm30, 56
	vpsrlq ymm13, ymm13, 12
	vpaddq ymm14, ymm12, ymm14
	vpaddq ymm14, ymm14, ymm13
	vpsrlq ymm16, ymm16, 8
	vpaddq ymm16, ymm9, ymm16
	vpmadd52luq ymm8, ymm30, YMMWORD PTR [r10+288]
	vpmadd52huq ymm7, ymm30, YMMWORD PTR [r10+288]
	vpmadd52luq ymm7, ymm30, YMMWORD PTR [r10+320]
	vpmadd52huq ymm25, ymm30, YMMWORD PTR [r10+320]
	vmovdqu64 ymm30, YMMWORD PTR [r10+256]
	vpandq ymm30, ymm14, ymm30
	vpsrlq ymm13, ymm14, 52
	vpsllq ymm12, ymm14, 56
	vpsrlq ymm12, ymm12, 12
	vpaddq ymm16, ymm16, ymm13
	vpaddq ymm16, ymm16, ymm12
	vpsrlq ymm30, ymm30, 8
	vpaddq ymm30, ymm8, ymm30
	vpmadd52luq ymm7, ymm14, YMMWORD PTR [r10+288]
	vpmadd52huq ymm25, ymm14, YMMWORD PTR [r10+288]
	vpmadd52luq ymm25, ymm14, YMMWORD PTR [r10+320]
	vpmadd52huq ymm28, ymm14, YMMWORD PTR [r10+320]
	vmovdqu64 ymm14, YMMWORD PTR [r10+256]
	vpandq ymm14, ymm16, ymm14
	vpsrlq ymm13, ymm16, 52
	vpsllq ymm12, ymm16, 56
	vpsrlq ymm12, ymm12, 12
	vpaddq ymm30, ymm30, ymm13
	vpaddq ymm30, ymm30, ymm12
	vpsrlq ymm14, ymm14, 8
	vpaddq ymm14, ymm7, ymm14
	vpmadd52luq ymm25, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm28, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm28, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm23, ymm16, YMMWORD PTR [r10+320]
	vmovdqu64 ymm16, YMMWORD PTR [r10+256]
	vpandq ymm16, ymm30, ymm16
	vpsrlq ymm13, ymm30, 52
	vpsllq ymm12, ymm30, 56
	vpsrlq ymm12, ymm12, 12
	vpaddq ymm14, ymm14, ymm13
	vpaddq ymm14, ymm14, ymm12
	vpsrlq ymm16, ymm16, 8
	vpaddq ymm25, ymm25, ymm16
	vpmadd52luq ymm28, ymm30, YMMWORD PTR [r10+288]
	vpmadd52huq ymm23, ymm30, YMMWORD PTR [r10+288]
	vpmadd52luq ymm23, ymm30, YMMWORD PTR [r10+320]
	vpmadd52huq ymm15, ymm30, YMMWORD PTR [r10+320]
	vmovdqu64 ymm30, YMMWORD PTR [r10+256]
	vpandq ymm30, ymm14, ymm30
	vpsrlq ymm16, ymm14, 52
	vpsllq ymm13, ymm14, 56
	vpsrlq ymm13, ymm13, 12
	vpaddq ymm25, ymm25, ymm16
	vpaddq ymm25, ymm25, ymm13
	vpsrlq ymm30, ymm30, 8
	vpaddq ymm30, ymm28, ymm30
	vpmadd52luq ymm23, ymm14, YMMWORD PTR [r10+288]
	vpmadd52huq ymm15, ymm14, YMMWORD PTR [r10+288]
	vpmadd52luq ymm15, ymm14, YMMWORD PTR [r10+320]
	vpmadd52huq ymm17, ymm14, YMMWORD PTR [r10+320]
	vpermq ymm28, ymm25, 170
	vpermq ymm16, ymm30, 170
	vpermq ymm14, ymm23, 170
	vpermq ymm13, ymm15, 170
	vpermq ymm12, ymm17, 170
	vpermq ymm11, ymm25, 255
	vpermq ymm10, ymm30, 255
	vpermq ymm9, ymm23, 255
	vpermq ymm8, ymm15, 255
	vpermq ymm7, ymm17, 255
	vpermq ymm6, ymm25, 0
	vpermq ymm5, ymm30, 0
	vpermq ymm4, ymm23, 0
	vpermq ymm3, ymm15, 0
	vpermq ymm2, ymm17, 0
	vpsllq ymm1, ymm28, 3
	vpsllq ymm0, ymm16, 3
	vmovdqu64 YMMWORD PTR [rdi+4544], ymm31
	vpsllq ymm31, ymm14, 3
	vmovdqu64 YMMWORD PTR [rdi+4576], ymm26
	vpsllq ymm26, ymm13, 3
	vmovdqu64 YMMWORD PTR [rdi+4608], ymm27
	vpsllq ymm27, ymm12, 3
	vmovdqu64 YMMWORD PTR [rdi+4640], ymm24
	vpsllq ymm24, ymm11, 2
	vmovdqu64 YMMWORD PTR [rdi+4672], ymm20
	vpsllq ymm20, ymm10, 2
	vmovdqu64 YMMWORD PTR [rdi+4704], ymm29
	vpsllq ymm29, ymm9, 2
	vmovdqu64 YMMWORD PTR [rdi+4736], ymm21
	vpsllq ymm21, ymm8, 2
	vmovdqu64 YMMWORD PTR [rdi+4768], ymm22
	vpsllq ymm22, ymm7, 2
	vpaddq ymm24, ymm1, ymm24
	vpaddq ymm20, ymm0, ymm20
	vpaddq ymm31, ymm31, ymm29
	vpaddq ymm29, ymm26, ymm21
	vpaddq ymm27, ymm27, ymm22
	vpsubq ymm26, ymm6, ymm24
	vpsubq ymm22, ymm5, ymm20
	vpsubq ymm21, ymm4, ymm31
	vpsubq ymm1, ymm3, ymm29
	vpsubq ymm0, ymm2, ymm27
	vpsllq ymm28, ymm28, 2
	vpsllq ymm16, ymm16, 2
	vpsllq ymm14, ymm14, 2
	vpsllq ymm13, ymm13, 2
	vpsllq ymm12, ymm12, 2
	vpaddq ymm28, ymm24, ymm28
	vpaddq ymm24, ymm20, ymm16
	vpaddq ymm31, ymm31, ymm14
	vpaddq ymm29, ymm29, ymm13
	vpaddq ymm27, ymm27, ymm12
	vpsubq ymm28, ymm28, ymm6
	vpsubq ymm24, ymm24, ymm5
	vpsubq ymm31, ymm31, ymm4
	vpsubq ymm29, ymm29, ymm3
	vpsubq ymm27, ymm27, ymm2
	vmovdqu64 ymm20, YMMWORD PTR [r10+704]
	vpternlogq ymm26, ymm28, ymm20, 216
	vmovdqu64 ymm28, YMMWORD PTR [r10+704]
	vpternlogq ymm22, ymm24, ymm28, 216
	vmovdqu64 ymm28, YMMWORD PTR [r10+704]
	vpternlogq ymm21, ymm31, ymm28, 216
	vmovdqu64 ymm31, YMMWORD PTR [r10+704]
	vpternlogq ymm1, ymm29, ymm31, 216
	vmovdqu64 ymm31, YMMWORD PTR [r10+704]
	vpternlogq ymm0, ymm27, ymm31, 216
	vmovdqu64 ymm31, YMMWORD PTR [r10]
	vpternlogq ymm26, ymm25, ymm31, 216
	vmovdqu64 ymm31, YMMWORD PTR [r10]
	vpternlogq ymm22, ymm30, ymm31, 216
	vmovdqu64 ymm31, YMMWORD PTR [r10]
	vpternlogq ymm21, ymm23, ymm31, 216
	vmovdqu64 ymm31, YMMWORD PTR [r10]
	vpternlogq ymm1, ymm15, ymm31, 216
	vmovdqu64 ymm31, YMMWORD PTR [r10]
	vpternlogq ymm0, ymm17, ymm31, 216
	vmovdqu64 ymm31, YMMWORD PTR [r10+352]
	vpternlogq ymm26, ymm11, ymm31, 216
	vmovdqu64 ymm31, YMMWORD PTR [r10+352]
	vpternlogq ymm22, ymm10, ymm31, 216
	vmovdqu64 ymm31, YMMWORD PTR [r10+352]
	vpternlogq ymm21, ymm9, ymm31, 216
	vmovdqu64 ymm31, YMMWORD PTR [r10+352]
	vpternlogq ymm1, ymm8, ymm31, 216
	vmovdqu64 ymm31, YMMWORD PTR [r10+352]
	vpternlogq ymm0, ymm7, ymm31, 216
	vmovdqu64 ymm31, YMMWORD PTR [r10+992]
	vpaddq ymm31, ymm26, ymm31
	vmovdqu64 ymm30, YMMWORD PTR [r10+1024]
	vpaddq ymm30, ymm22, ymm30
	vmovdqu64 ymm29, YMMWORD PTR [r10+128]
	vpaddq ymm29, ymm21, ymm29
	vmovdqu64 ymm28, YMMWORD PTR [r10+1056]
	vpaddq ymm28, ymm1, ymm28
	vmovdqu64 ymm27, YMMWORD PTR [r10+1088]
	vpaddq ymm27, ymm0, ymm27
	vpsraq ymm26, ymm27, 48
	vmovdqu64 ymm25, YMMWORD PTR [r10+224]
	vpandq ymm25, ymm27, ymm25
	vpaddq ymm31, ymm31, ymm26
	vpsllq ymm27, ymm26, 44
	vpsubq ymm30, ymm30, ymm27
	vpsllq ymm27, ymm26, 36
	vpsubq ymm28, ymm28, ymm27
	vpsllq ymm27, ymm26, 16
	vpaddq ymm27, ymm25, ymm27
	vpsraq ymm26, ymm31, 52
	vmovdqu64 ymm25, YMMWORD PTR [r10+256]
	vpandq ymm25, ymm31, ymm25
	vpaddq ymm31, ymm30, ymm26
	vpsraq ymm30, ymm31, 52
	vmovdqu64 ymm26, YMMWORD PTR [r10+256]
	vpandq ymm26, ymm31, ymm26
	vpaddq ymm31, ymm29, ymm30
	vpsraq ymm30, ymm31, 52
	vmovdqu64 ymm29, YMMWORD PTR [r10+256]
	vpandq ymm29, ymm31, ymm29
	vpaddq ymm31, ymm28, ymm30
	vpsraq ymm30, ymm31, 52
	vmovdqu64 ymm28, YMMWORD PTR [r10+256]
	vpandq ymm28, ymm31, ymm28
	vpaddq ymm31, ymm27, ymm30
	vmovdqu64 ymm30, YMMWORD PTR [r10+704]
	vmovdqa64 ymm27, ymm25
	vpternlogq ymm27, ymm18, ymm30, 216
	vmovdqu64 ymm30, YMMWORD PTR [r10+704]
	vmovdqa64 ymm24, ymm26
	vpternlogq ymm24, ymm19, ymm30, 216
	vmovdqu64 ymm30, YMMWORD PTR [rdi+4768]
	vmovdqu64 ymm23, YMMWORD PTR [r10+704]
	vmovdqa64 ymm22, ymm29
	vpternlogq ymm22, ymm30, ymm23, 216
	vmovdqu64 ymm23, YMMWORD PTR [rdi+4736]
	vmovdqu64 ymm21, YMMWORD PTR [r10+704]
	vmovdqa64 ymm20, ymm28
	vpternlogq ymm20, ymm23, ymm21, 216
	vmovdqu64 ymm21, YMMWORD PTR [rdi+4704]
	vmovdqu64 ymm17, YMMWORD PTR [r10+704]
	vmovdqa64 ymm16, ymm31
	vpternlogq ymm16, ymm21, ymm17, 216
	vmovdqu64 ymm17, YMMWORD PTR [rdi+4672]
	vpermq ymm17, ymm17, 0
	vmovdqu64 ymm15, YMMWORD PTR [rdi+4640]
	vpermq ymm15, ymm15, 0
	vmovdqu64 ymm14, YMMWORD PTR [rdi+4608]
	vpermq ymm14, ymm14, 0
	vmovdqu64 ymm13, YMMWORD PTR [rdi+4576]
	vpermq ymm13, ymm13, 0
	vmovdqu64 ymm12, YMMWORD PTR [rdi+4544]
	vpermq ymm12, ymm12, 0
	vmovdqu64 ymm11, YMMWORD PTR [r10+352]
	vpternlogq ymm27, ymm17, ymm11, 216
	vmovdqu64 ymm17, YMMWORD PTR [r10+352]
	vpternlogq ymm24, ymm15, ymm17, 216
	vmovdqu64 ymm17, YMMWORD PTR [r10+352]
	vpternlogq ymm22, ymm14, ymm17, 216
	vmovdqu64 ymm17, YMMWORD PTR [r10+352]
	vpternlogq ymm20, ymm13, ymm17, 216
	vmovdqu64 ymm17, YMMWORD PTR [r10+352]
	vpternlogq ymm16, ymm12, ymm17, 216
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm27, ymm25
	vpxorq ymm15, ymm15, ymm15
	vpmadd52huq ymm15, ymm27, ymm25
	vpmadd52luq ymm15, ymm24, ymm25
	vpmadd52luq ymm15, ymm27, ymm26
	vpxorq ymm14, ymm14, ymm14
	vpmadd52huq ymm14, ymm24, ymm25
	vpmadd52luq ymm14, ymm24, ymm26
	vpmadd52luq ymm14, ymm27, ymm29
	vpxorq ymm13, ymm13, ymm13
	vpmadd52huq ymm13, ymm27, ymm26
	vpmadd52luq ymm13, ymm22, ymm25
	vpaddq ymm14, ymm14, ymm13
	vpxorq ymm13, ymm13, ymm13
	vpmadd52huq ymm13, ymm24, ymm26
	vpmadd52luq ymm13, ymm22, ymm26
	vpmadd52luq ymm13, ymm27, ymm28
	vpxorq ymm12, ymm12, ymm12
	vpmadd52huq ymm12, ymm22, ymm25
	vpmadd52luq ymm12, ymm24, ymm29
	vpxorq ymm11, ymm11, ymm11
	vpmadd52huq ymm11, ymm27, ymm29
	vpmadd52luq ymm11, ymm20, ymm25
	vpaddq ymm13, ymm13, ymm12
	vpaddq ymm13, ymm13, ymm11
	vpxorq ymm12, ymm12, ymm12
	vpmadd52huq ymm12, ymm22, ymm26
	vpmadd52huq ymm12, ymm20, ymm25
	vpmadd52luq ymm12, ymm24, ymm28
	vpxorq ymm11, ymm11, ymm11
	vpmadd52huq ymm11, ymm24, ymm29
	vpmadd52huq ymm11, ymm27, ymm28
	vpmadd52luq ymm11, ymm16, ymm25
	vpxorq ymm10, ymm10, ymm10
	vpmadd52luq ymm10, ymm22, ymm29
	vpmadd52luq ymm10, ymm20, ymm26
	vpmadd52luq ymm10, ymm27, ymm31
	vpaddq ymm12, ymm12, ymm11
	vpaddq ymm12, ymm12, ymm10
	vpxorq ymm11, ymm11, ymm11
	vpmadd52huq ymm11, ymm22, ymm29
	vpmadd52luq ymm11, ymm20, ymm29
	vpmadd52huq ymm11, ymm27, ymm31
	vpxorq ymm27, ymm27, ymm27
	vpmadd52huq ymm27, ymm20, ymm26
	vpmadd52luq ymm27, ymm22, ymm28
	vpmadd52luq ymm27, ymm16, ymm26
	vpxorq ymm10, ymm10, ymm10
	vpmadd52huq ymm10, ymm24, ymm28
	vpmadd52huq ymm10, ymm16, ymm25
	vpmadd52luq ymm10, ymm24, ymm31
	vpaddq ymm27, ymm11, ymm27
	vpaddq ymm27, ymm27, ymm10
	vpxorq ymm11, ymm11, ymm11
	vpmadd52huq ymm11, ymm20, ymm29
	vpmadd52huq ymm11, ymm16, ymm26
	vpmadd52luq ymm11, ymm22, ymm31
	vpxorq ymm10, ymm10, ymm10
	vpmadd52huq ymm10, ymm22, ymm28
	vpmadd52huq ymm10, ymm24, ymm31
	vpxorq ymm24, ymm24, ymm24
	vpmadd52luq ymm24, ymm20, ymm28
	vpmadd52luq ymm24, ymm16, ymm29
	vpaddq ymm11, ymm11, ymm10
	vpaddq ymm24, ymm11, ymm24
	vpxorq ymm11, ymm11, ymm11
	vpmadd52huq ymm11, ymm20, ymm28
	vpmadd52huq ymm11, ymm22, ymm31
	vpmadd52luq ymm11, ymm20, ymm31
	vpxorq ymm22, ymm22, ymm22
	vpmadd52huq ymm22, ymm16, ymm29
	vpmadd52luq ymm22, ymm16, ymm28
	vpaddq ymm22, ymm11, ymm22
	vpxorq ymm11, ymm11, ymm11
	vpmadd52huq ymm11, ymm16, ymm28
	vpmadd52huq ymm11, ymm20, ymm31
	vpmadd52luq ymm11, ymm16, ymm31
	vpxorq ymm20, ymm20, ymm20
	vpmadd52huq ymm20, ymm16, ymm31
	vmovdqu64 ymm16, YMMWORD PTR [r10+256]
	vpandq ymm16, ymm17, ymm16
	vpsrlq ymm10, ymm17, 52
	vpsllq ymm9, ymm17, 56
	vpsrlq ymm9, ymm9, 12
	vpaddq ymm15, ymm15, ymm10
	vpaddq ymm15, ymm15, ymm9
	vpsrlq ymm16, ymm16, 8
	vpaddq ymm16, ymm14, ymm16
	vpmadd52luq ymm13, ymm17, YMMWORD PTR [r10+288]
	vpmadd52huq ymm12, ymm17, YMMWORD PTR [r10+288]
	vpmadd52luq ymm12, ymm17, YMMWORD PTR [r10+320]
	vpmadd52huq ymm27, ymm17, YMMWORD PTR [r10+320]
	vmovdqu64 ymm17, YMMWORD PTR [r10+256]
	vpandq ymm17, ymm15, ymm17
	vpsrlq ymm14, ymm15, 52
	vpsllq ymm10, ymm15, 56
	vpsrlq ymm10, ymm10, 12
	vpaddq ymm16, ymm16, ymm14
	vpaddq ymm16, ymm16, ymm10
	vpsrlq ymm17, ymm17, 8
	vpaddq ymm17, ymm13, ymm17
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r10+288]
	vpmadd52huq ymm27, ymm15, YMMWORD PTR [r10+288]
	vpmadd52luq ymm27, ymm15, YMMWORD PTR [r10+320]
	vpmadd52huq ymm24, ymm15, YMMWORD PTR [r10+320]
	vmovdqu64 ymm15, YMMWORD PTR [r10+256]
	vpandq ymm15, ymm16, ymm15
	vpsrlq ymm14, ymm16, 52
	vpsllq ymm13, ymm16, 56
	vpsrlq ymm13, ymm13, 12
	vpaddq ymm17, ymm17, ymm14
	vpaddq ymm17, ymm17, ymm13
	vpsrlq ymm15, ymm15, 8
	vpaddq ymm15, ymm12, ymm15
	vpmadd52luq ymm27, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm24, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm24, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm22, ymm16, YMMWORD PTR [r10+320]
	vmovdqu64 ymm16, YMMWORD PTR [r10+256]
	vpandq ymm16, ymm17, ymm16
	vpsrlq ymm14, ymm17, 52
	vpsllq ymm13, ymm17, 56
	vpsrlq ymm13, ymm13, 12
	vpaddq ymm15, ymm15, ymm14
	vpaddq ymm15, ymm15, ymm13
	vpsrlq ymm16, ymm16, 8
	vpaddq ymm27, ymm27, ymm16
	vpmadd52luq ymm24, ymm17, YMMWORD PTR [r10+288]
	vpmadd52huq ymm22, ymm17, YMMWORD PTR [r10+288]
	vpmadd52luq ymm22, ymm17, YMMWORD PTR [r10+320]
	vpmadd52huq ymm11, ymm17, YMMWORD PTR [r10+320]
	vmovdqu64 ymm17, YMMWORD PTR [r10+256]
	vpandq ymm17, ymm15, ymm17
	vpsrlq ymm16, ymm15, 52
	vpsllq ymm14, ymm15, 56
	vpsrlq ymm14, ymm14, 12
	vpaddq ymm27, ymm27, ymm16
	vpaddq ymm27, ymm27, ymm14
	vpsrlq ymm17, ymm17, 8
	vpaddq ymm24, ymm24, ymm17
	vpmadd52luq ymm22, ymm15, YMMWORD PTR [r10+288]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r10+288]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r10+320]
	vpmadd52huq ymm20, ymm15, YMMWORD PTR [r10+320]
	vpermq ymm17, ymm27, 170
	vpermq ymm16, ymm24, 170
	vpermq ymm15, ymm22, 170
	vpermq ymm14, ymm11, 170
	vpermq ymm13, ymm20, 170
	vpsllq ymm17, ymm17, 2
	vpsllq ymm16, ymm16, 2
	vpsllq ymm15, ymm15, 2
	vpsllq ymm14, ymm14, 2
	vpsllq ymm13, ymm13, 2
	vpsubq ymm17, ymm27, ymm17
	vpsubq ymm16, ymm24, ymm16
	vpsubq ymm15, ymm22, ymm15
	vpsubq ymm14, ymm11, ymm14
	vpsubq ymm13, ymm20, ymm13
	vpaddq ymm17, ymm17, ymm17
	vpaddq ymm16, ymm16, ymm16
	vpaddq ymm15, ymm15, ymm15
	vpaddq ymm14, ymm14, ymm14
	vpaddq ymm13, ymm13, ymm13
	vmovdqa64 ymm0, ymm17
	vmovdqa64 ymm1, ymm16
	vmovdqa64 ymm2, ymm15
	vmovdqa64 ymm3, ymm14
	vmovdqa64 ymm4, ymm13
	vmovdqa64 ymm5, ymm18
	vmovdqa64 ymm6, ymm19
	vmovdqa64 ymm7, ymm30
	vmovdqa64 ymm8, ymm23
	vmovdqa64 ymm9, ymm21
	vmovdqa64 ymm10, ymm25
	vmovdqa64 ymm12, ymm29
	vmovdqa64 ymm13, ymm28
	vmovdqa64 ymm14, ymm31
	vmovdqa64 ymm15, ymm27
	vmovdqa64 ymm16, ymm24
	vmovdqa64 ymm17, ymm22
	vmovdqa64 ymm18, ymm11
	vmovdqa64 ymm11, ymm26
	vmovdqa64 ymm19, ymm20
	test rbx, rbx
	jne 25b
	vmovdqu64 ymm31, YMMWORD PTR [r10]
	vpternlogq ymm0, ymm5, ymm31, 216
	vmovdqu64 ymm31, YMMWORD PTR [r10]
	vpternlogq ymm1, ymm6, ymm31, 216
	vmovdqu64 ymm31, YMMWORD PTR [r10]
	vpternlogq ymm2, ymm7, ymm31, 216
	vmovdqu64 ymm31, YMMWORD PTR [r10]
	vpternlogq ymm3, ymm8, ymm31, 216
	vmovdqu64 ymm31, YMMWORD PTR [r10]
	vpternlogq ymm4, ymm9, ymm31, 216
	vmovdqu64 ymm31, YMMWORD PTR [r10+32]
	vpternlogq ymm0, ymm10, ymm31, 216
	vmovdqu64 ymm31, YMMWORD PTR [r10+32]
	vpternlogq ymm1, ymm11, ymm31, 216
	vmovdqu64 ymm31, YMMWORD PTR [r10+32]
	vpternlogq ymm2, ymm12, ymm31, 216
	vmovdqu64 ymm31, YMMWORD PTR [r10+32]
	vpternlogq ymm3, ymm13, ymm31, 216
	vmovdqu64 ymm31, YMMWORD PTR [r10+32]
	vpternlogq ymm4, ymm14, ymm31, 216
	vmovdqu64 ymm31, YMMWORD PTR [r10+1120]
	vpaddq ymm31, ymm0, ymm31
	vmovdqu64 ymm30, YMMWORD PTR [r10+1152]
	vpaddq ymm30, ymm1, ymm30
	vmovdqu64 ymm29, YMMWORD PTR [r10+128]
	vpaddq ymm29, ymm2, ymm29
	vmovdqu64 ymm28, YMMWORD PTR [r10+1184]
	vpaddq ymm28, ymm3, ymm28
	vmovdqu64 ymm27, YMMWORD PTR [r10+1216]
	vpaddq ymm27, ymm4, ymm27
	vpsraq ymm26, ymm27, 48
	vmovdqu64 ymm25, YMMWORD PTR [r10+224]
	vpandq ymm25, ymm27, ymm25
	vpaddq ymm31, ymm31, ymm26
	vpsllq ymm27, ymm26, 44
	vpsubq ymm30, ymm30, ymm27
	vpsllq ymm27, ymm26, 36
	vpsubq ymm28, ymm28, ymm27
	vpsllq ymm27, ymm26, 16
	vpaddq ymm27, ymm25, ymm27
	vpsraq ymm26, ymm31, 52
	vmovdqu64 ymm25, YMMWORD PTR [r10+256]
	vpandq ymm25, ymm31, ymm25
	vpaddq ymm31, ymm30, ymm26
	vpsraq ymm30, ymm31, 52
	vmovdqu64 ymm26, YMMWORD PTR [r10+256]
	vpandq ymm26, ymm31, ymm26
	vpaddq ymm31, ymm29, ymm30
	vpsraq ymm30, ymm31, 52
	vmovdqu64 ymm29, YMMWORD PTR [r10+256]
	vpandq ymm29, ymm31, ymm29
	vpaddq ymm31, ymm28, ymm30
	vpsraq ymm30, ymm31, 52
	vmovdqu64 ymm28, YMMWORD PTR [r10+256]
	vpandq ymm28, ymm31, ymm28
	vpaddq ymm31, ymm27, ymm30
	vmovdqu64 ymm30, YMMWORD PTR [r10+1248]
	vmovdqu64 ymm27, YMMWORD PTR [r10+1280]
	vmovdqu64 ymm24, YMMWORD PTR [r10+1312]
	vmovdqu64 ymm23, YMMWORD PTR [r10+1344]
	vmovdqu64 ymm22, YMMWORD PTR [r10+1376]
	vpxorq ymm21, ymm21, ymm21
	vpmadd52luq ymm21, ymm25, ymm30
	vpxorq ymm20, ymm20, ymm20
	vpmadd52huq ymm20, ymm25, ymm30
	vpmadd52luq ymm20, ymm26, ymm30
	vpmadd52luq ymm20, ymm25, ymm27
	vpxorq ymm19, ymm19, ymm19
	vpmadd52huq ymm19, ymm26, ymm30
	vpmadd52luq ymm19, ymm26, ymm27
	vpmadd52luq ymm19, ymm25, ymm24
	vpxorq ymm18, ymm18, ymm18
	vpmadd52huq ymm18, ymm25, ymm27
	vpmadd52luq ymm18, ymm29, ymm30
	vpaddq ymm19, ymm19, ymm18
	vpxorq ymm18, ymm18, ymm18
	vpmadd52huq ymm18, ymm26, ymm27
	vpmadd52luq ymm18, ymm29, ymm27
	vpmadd52luq ymm18, ymm25, ymm23
	vpxorq ymm17, ymm17, ymm17
	vpmadd52huq ymm17, ymm29, ymm30
	vpmadd52luq ymm17, ymm26, ymm24
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm25, ymm24
	vpmadd52luq ymm16, ymm28, ymm30
	vpaddq ymm18, ymm18, ymm17
	vpaddq ymm18, ymm18, ymm16
	vpxorq ymm17, ymm17, ymm17
	vpmadd52huq ymm17, ymm29, ymm27
	vpmadd52huq ymm17, ymm28, ymm30
	vpmadd52luq ymm17, ymm26, ymm23
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm26, ymm24
	vpmadd52huq ymm16, ymm25, ymm23
	vpmadd52luq ymm16, ymm31, ymm30
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm29, ymm24
	vpmadd52luq ymm15, ymm28, ymm27
	vpmadd52luq ymm15, ymm25, ymm22
	vpaddq ymm17, ymm17, ymm16
	vpaddq ymm17, ymm17, ymm15
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm29, ymm24
	vpmadd52luq ymm16, ymm28, ymm24
	vpmadd52huq ymm16, ymm25, ymm22
	vpxorq ymm25, ymm25, ymm25
	vpmadd52huq ymm25, ymm28, ymm27
	vpmadd52luq ymm25, ymm29, ymm23
	vpmadd52luq ymm25, ymm31, ymm27
	vpxorq ymm15, ymm15, ymm15
	vpmadd52huq ymm15, ymm26, ymm23
	vpmadd52huq ymm15, ymm31, ymm30
	vpmadd52luq ymm15, ymm26, ymm22
	vpaddq ymm30, ymm16, ymm25
	vpaddq ymm30, ymm30, ymm15
	vpxorq ymm25, ymm25, ymm25
	vpmadd52huq ymm25, ymm28, ymm24
	vpmadd52huq ymm25, ymm31, ymm27
	vpmadd52luq ymm25, ymm29, ymm22
	vpxorq ymm27, ymm27, ymm27
	vpmadd52huq ymm27, ymm29, ymm23
	vpmadd52huq ymm27, ymm26, ymm22
	vpxorq ymm26, ymm26, ymm26
	vpmadd52luq ymm26, ymm28, ymm23
	vpmadd52luq ymm26, ymm31, ymm24
	vpaddq ymm27, ymm25, ymm27
	vpaddq ymm27, ymm27, ymm26
	vpxorq ymm26, ymm26, ymm26
	vpmadd52huq ymm26, ymm28, ymm23
	vpmadd52huq ymm26, ymm29, ymm22
	vpmadd52luq ymm26, ymm28, ymm22
	vpxorq ymm29, ymm29, ymm29
	vpmadd52huq ymm29, ymm31, ymm24
	vpmadd52luq ymm29, ymm31, ymm23
	vpaddq ymm29, ymm26, ymm29
	vpxorq ymm26, ymm26, ymm26
	vpmadd52huq ymm26, ymm31, ymm23
	vpmadd52huq ymm26, ymm28, ymm22
	vpmadd52luq ymm26, ymm31, ymm22
	vpxorq ymm28, ymm28, ymm28
	vpmadd52huq ymm28, ymm31, ymm22
	vmovdqu64 ymm31, YMMWORD PTR [r10+256]
	vpandq ymm31, ymm21, ymm31
	vpsrlq ymm25, ymm21, 52
	vpsllq ymm24, ymm21, 56
	vpsrlq ymm24, ymm24, 12
	vpaddq ymm25, ymm20, ymm25
	vpaddq ymm25, ymm25, ymm24
	vpsrlq ymm31, ymm31, 8
	vpaddq ymm31, ymm19, ymm31
	vpmadd52luq ymm18, ymm21, YMMWORD PTR [r10+288]
	vpmadd52huq ymm17, ymm21, YMMWORD PTR [r10+288]
	vpmadd52luq ymm17, ymm21, YMMWORD PTR [r10+320]
	vpmadd52huq ymm30, ymm21, YMMWORD PTR [r10+320]
	vmovdqu64 ymm24, YMMWORD PTR [r10+256]
	vpandq ymm24, ymm25, ymm24
	vpsrlq ymm23, ymm25, 52
	vpsllq ymm22, ymm25, 56
	vpsrlq ymm22, ymm22, 12
	vpaddq ymm31, ymm31, ymm23
	vpaddq ymm31, ymm31, ymm22
	vpsrlq ymm24, ymm24, 8
	vpaddq ymm24, ymm18, ymm24
	vpmadd52luq ymm17, ymm25, YMMWORD PTR [r10+288]
	vpmadd52huq ymm30, ymm25, YMMWORD PTR [r10+288]
	vpmadd52luq ymm30, ymm25, YMMWORD PTR [r10+320]
	vpmadd52huq ymm27, ymm25, YMMWORD PTR [r10+320]
	vmovdqu64 ymm25, YMMWORD PTR [r10+256]
	vpandq ymm25, ymm31, ymm25
	vpsrlq ymm23, ymm31, 52
	vpsllq ymm22, ymm31, 56
	vpsrlq ymm22, ymm22, 12
	vpaddq ymm24, ymm24, ymm23
	vpaddq ymm24, ymm24, ymm22
	vpsrlq ymm25, ymm25, 8
	vpaddq ymm25, ymm17, ymm25
	vpmadd52luq ymm30, ymm31, YMMWORD PTR [r10+288]
	vpmadd52huq ymm27, ymm31, YMMWORD PTR [r10+288]
	vpmadd52luq ymm27, ymm31, YMMWORD PTR [r10+320]
	vpmadd52huq ymm29, ymm31, YMMWORD PTR [r10+320]
	vmovdqu64 ymm31, YMMWORD PTR [r10+256]
	vpandq ymm31, ymm24, ymm31
	vpsrlq ymm23, ymm24, 52
	vpsllq ymm22, ymm24, 56
	vpsrlq ymm22, ymm22, 12
	vpaddq ymm25, ymm25, ymm23
	vpaddq ymm25, ymm25, ymm22
	vpsrlq ymm31, ymm31, 8
	vpaddq ymm31, ymm30, ymm31
	vpmadd52luq ymm27, ymm24, YMMWORD PTR [r10+288]
	vpmadd52huq ymm29, ymm24, YMMWORD PTR [r10+288]
	vpmadd52luq ymm29, ymm24, YMMWORD PTR [r10+320]
	vpmadd52huq ymm26, ymm24, YMMWORD PTR [r10+320]
	vmovdqu64 ymm30, YMMWORD PTR [r10+256]
	vpandq ymm30, ymm25, ymm30
	vpsrlq ymm24, ymm25, 52
	vpsllq ymm23, ymm25, 56
	vpsrlq ymm23, ymm23, 12
	vpaddq ymm31, ymm31, ymm24
	vpaddq ymm31, ymm31, ymm23
	vpsrlq ymm30, ymm30, 8
	vpaddq ymm30, ymm27, ymm30
	vpmadd52luq ymm29, ymm25, YMMWORD PTR [r10+288]
	vpmadd52huq ymm26, ymm25, YMMWORD PTR [r10+288]
	vpmadd52luq ymm26, ymm25, YMMWORD PTR [r10+320]
	vpmadd52huq ymm28, ymm25, YMMWORD PTR [r10+320]
	vpsraq ymm27, ymm28, 48
	vmovdqu64 ymm25, YMMWORD PTR [r10+224]
	vpandq ymm25, ymm28, ymm25
	vpaddq ymm31, ymm31, ymm27
	vpsllq ymm28, ymm27, 44
	vpsubq ymm30, ymm30, ymm28
	vpsllq ymm28, ymm27, 36
	vpsubq ymm28, ymm26, ymm28
	vpsllq ymm27, ymm27, 16
	vpaddq ymm27, ymm25, ymm27
	vpsraq ymm26, ymm31, 52
	vmovdqu64 ymm25, YMMWORD PTR [r10+256]
	vpandq ymm25, ymm31, ymm25
	vpaddq ymm31, ymm30, ymm26
	vpsraq ymm30, ymm31, 52
	vmovdqu64 ymm26, YMMWORD PTR [r10+256]
	vpandq ymm26, ymm31, ymm26
	vpaddq ymm31, ymm29, ymm30
	vpsraq ymm30, ymm31, 52
	vmovdqu64 ymm29, YMMWORD PTR [r10+256]
	vpandq ymm29, ymm31, ymm29
	vpaddq ymm31, ymm28, ymm30
	vpsraq ymm30, ymm31, 52
	vmovdqu64 ymm28, YMMWORD PTR [r10+256]
	vpandq ymm28, ymm31, ymm28
	vpaddq ymm31, ymm27, ymm30
	vmovdqa64 ymm0, ymm25
	vmovdqa64 ymm1, ymm26
	vmovdqa64 ymm2, ymm29
	vmovdqa64 ymm3, ymm28
	vmovdqa64 ymm4, ymm31
	vmovdqu64 YMMWORD PTR [rdi+4512], ymm0
	vmovdqu64 YMMWORD PTR [rdi+4544], ymm1
	vmovdqu64 YMMWORD PTR [rdi+4576], ymm2
	vmovdqu64 YMMWORD PTR [rdi+4608], ymm3
	vmovdqu64 YMMWORD PTR [rdi+4640], ymm4
	sub rdi, 992
	vzeroupper
	lfence
	mov DWORD PTR [rdi+5472], r12d
	ldmxcsr DWORD PTR [rdi+5472]
	mov r8, QWORD PTR [rdi+5528]
	mov rax, QWORD PTR [rdi+5560]
	mov r9, rax
	shl rax, 52
	or r8, rax
	shr r9, 12
	mov rax, QWORD PTR [rdi+5592]
	mov r10, rax
	shl rax, 40
	or r9, rax
	shr r10, 24
	mov rax, QWORD PTR [rdi+5624]
	mov r11, rax
	shl rax, 28
	or r10, rax
	shr r11, 36
	mov rax, QWORD PTR [rdi+5656]
	mov r12, rax
	shl rax, 16
	or r11, rax
	shr r12, 48
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+512], r8
	mov QWORD PTR [rdi+520], r9
	mov QWORD PTR [rdi+528], r10
	mov QWORD PTR [rdi+536], r11
	mov r8, QWORD PTR [rdi+5504]
	mov rax, QWORD PTR [rdi+5536]
	mov r9, rax
	shl rax, 52
	or r8, rax
	shr r9, 12
	mov rax, QWORD PTR [rdi+5568]
	mov r10, rax
	shl rax, 40
	or r9, rax
	shr r10, 24
	mov rax, QWORD PTR [rdi+5600]
	mov r11, rax
	shl rax, 28
	or r10, rax
	shr r11, 36
	mov rax, QWORD PTR [rdi+5632]
	mov r12, rax
	shl rax, 16
	or r11, rax
	shr r12, 48
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+544], r8
	mov QWORD PTR [rdi+552], r9
	mov QWORD PTR [rdi+560], r10
	mov QWORD PTR [rdi+568], r11
	mov r8, QWORD PTR [rdi+5512]
	mov rax, QWORD PTR [rdi+5544]
	mov r9, rax
	shl rax, 52
	or r8, rax
	shr r9, 12
	mov rax, QWORD PTR [rdi+5576]
	mov r10, rax
	shl rax, 40
	or r9, rax
	shr r10, 24
	mov rax, QWORD PTR [rdi+5608]
	mov r11, rax
	shl rax, 28
	or r10, rax
	shr r11, 36
	mov rax, QWORD PTR [rdi+5640]
	mov r12, rax
	shl rax, 16
	or r11, rax
	shr r12, 48
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+576], r8
	mov QWORD PTR [rdi+584], r9
	mov QWORD PTR [rdi+592], r10
	mov QWORD PTR [rdi+600], r11
	mov rax, QWORD PTR [rdi+576]
	or rax, QWORD PTR [rdi+584]
	or rax, QWORD PTR [rdi+592]
	or rax, QWORD PTR [rdi+600]
	mov ecx, 0
	sub rcx, rax
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+160]
	mov rdx, QWORD PTR [rdi+544]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rdi+168]
	mov rdx, QWORD PTR [rdi+552]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rdi+176]
	mov rdx, QWORD PTR [rdi+560]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rdi+184]
	mov rdx, QWORD PTR [rdi+568]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+568], rax
	xor rcx, -1
	movabs rax, 1
	and rax, rcx
	or rax, QWORD PTR [rdi+544]
	mov QWORD PTR [rdi+544], rax
	movabs rax, -4294967296
	and rax, rcx
	or rax, QWORD PTR [rdi+552]
	mov QWORD PTR [rdi+552], rax
	movabs rax, -1
	and rax, rcx
	or rax, QWORD PTR [rdi+560]
	mov QWORD PTR [rdi+560], rax
	movabs rax, 4294967294
	and rax, rcx
	or rax, QWORD PTR [rdi+568]
	mov QWORD PTR [rdi+568], rax
	mov rdx, QWORD PTR [rdi+512]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+576]
	mulx r10, rax, QWORD PTR [rdi+584]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+592]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+600]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+520]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+528]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+600]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+536]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+600]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+512], r12
	mov QWORD PTR [rdi+520], r13
	mov QWORD PTR [rdi+528], r14
	mov QWORD PTR [rdi+536], r15
	mov rdx, QWORD PTR [rdi+576]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+584]
	mulx r11, rax, QWORD PTR [rdi+592]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+600]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+584]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+592]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+600]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+576]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+584]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+592]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+600]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+800], r12
	mov QWORD PTR [rdi+808], r13
	mov QWORD PTR [rdi+816], r14
	mov QWORD PTR [rdi+824], r15
	mov rdx, r12
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+576]
	mulx r10, rax, QWORD PTR [rdi+584]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+592]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+600]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, r13
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, r14
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+600]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, r15
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+600]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+576], r12
	mov QWORD PTR [rdi+584], r13
	mov QWORD PTR [rdi+592], r14
	mov QWORD PTR [rdi+600], r15
	mov r8, QWORD PTR [rdi+160]
	mov r9, QWORD PTR [rdi+168]
	mov r10, QWORD PTR [rdi+176]
	mov r11, QWORD PTR [rdi+184]
	sub r8, QWORD PTR [rdi+544]
	sbb r9, QWORD PTR [rdi+552]
	sbb r10, QWORD PTR [rdi+560]
	sbb r11, QWORD PTR [rdi+568]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+1024], r8
	mov QWORD PTR [rdi+1032], r9
	mov QWORD PTR [rdi+1040], r10
	mov QWORD PTR [rdi+1048], r11
	movzx ecx, BYTE PTR [rdi+1504]
	sub rcx, 1
	mov rax, QWORD PTR [rdi+544]
	mov rdx, QWORD PTR [rdi+1024]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rdi+552]
	mov rdx, QWORD PTR [rdi+1032]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rdi+560]
	mov rdx, QWORD PTR [rdi+1040]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rdi+568]
	mov rdx, QWORD PTR [rdi+1048]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+568], rax
	call {vg_p256_inv_mod_p_adx}
	mov rdx, QWORD PTR [rdi+512]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+992]
	mulx r10, rax, QWORD PTR [rdi+1000]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1008]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1016]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+520]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+992]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1000]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1008]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+1016]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+528]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+992]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1000]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1008]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+1016]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+536]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+992]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1000]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1008]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+1016]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+1152], r12
	mov QWORD PTR [rdi+1160], r13
	mov QWORD PTR [rdi+1168], r14
	mov QWORD PTR [rdi+1176], r15
	mov rdx, QWORD PTR [rdi+1152]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+192]
	mulx r10, rax, QWORD PTR [rdi+200]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+208]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+216]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+1160]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+192]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+200]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+208]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+216]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+1168]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+192]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+200]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+208]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+216]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+1176]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+192]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+200]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+208]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+216]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+1184], r12
	mov QWORD PTR [rdi+1192], r13
	mov QWORD PTR [rdi+1200], r14
	mov QWORD PTR [rdi+1208], r15
	mov rdx, QWORD PTR [rdi+1088]
	sub rdx, QWORD PTR [rdi+96]
	mov rdx, QWORD PTR [rdi+1096]
	sbb rdx, QWORD PTR [rdi+104]
	mov rdx, QWORD PTR [rdi+1104]
	sbb rdx, QWORD PTR [rdi+112]
	mov rdx, QWORD PTR [rdi+1112]
	sbb rdx, QWORD PTR [rdi+120]
	sbb rax, rax
	mov rbp, rax
	mov rdx, QWORD PTR [rdi+1088]
	or rdx, QWORD PTR [rdi+1096]
	or rdx, QWORD PTR [rdi+1104]
	or rdx, QWORD PTR [rdi+1112]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	and rdx, rbp
	mov rax, QWORD PTR [rdi+1472]
	and rax, rdx
	mov QWORD PTR [rdi+1472], rax
	mov rdx, QWORD PTR [rdi+576]
	or rdx, QWORD PTR [rdi+584]
	or rdx, QWORD PTR [rdi+592]
	or rdx, QWORD PTR [rdi+600]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+1472]
	and rax, rdx
	mov QWORD PTR [rdi+1472], rax
	mov rcx, QWORD PTR [rdi+1472]
	mov rax, QWORD PTR [rdi+1184]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+24], rax
	mov rax, QWORD PTR [rdi+1192]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+16], rax
	mov rax, QWORD PTR [rdi+1200]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+8], rax
	mov rax, QWORD PTR [rdi+1208]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi], rax
	mov rax, rcx
	and rax, 1
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
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
	lea rsp, [rsp-16]
	movdqu XMMWORD PTR [rsp], xmm0
	lea rsp, [rsp+16]
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

vg_ecdh_p256:
	mov r8, rcx
	mov r9, rdx
	mov rcx, rsi
	add rdx, 1
	mov QWORD PTR [r8], rbx
	mov QWORD PTR [r8+8], rbp
	mov QWORD PTR [r8+16], r12
	mov QWORD PTR [r8+24], r13
	mov QWORD PTR [r8+32], r14
	mov QWORD PTR [r8+40], r15
	mov r14, rdi
	mov rdi, r8
	mov rax, QWORD PTR [rcx+24]
	bswap rax
	mov QWORD PTR [rdi+1056], rax
	mov rax, QWORD PTR [rcx+16]
	bswap rax
	mov QWORD PTR [rdi+1064], rax
	mov rax, QWORD PTR [rcx+8]
	bswap rax
	mov QWORD PTR [rdi+1072], rax
	mov rax, QWORD PTR [rcx]
	bswap rax
	mov QWORD PTR [rdi+1080], rax
	mov rax, QWORD PTR [rsi+24]
	bswap rax
	mov QWORD PTR [rdi+1088], rax
	mov rax, QWORD PTR [rsi+16]
	bswap rax
	mov QWORD PTR [rdi+1096], rax
	mov rax, QWORD PTR [rsi+8]
	bswap rax
	mov QWORD PTR [rdi+1104], rax
	mov rax, QWORD PTR [rsi]
	bswap rax
	mov QWORD PTR [rdi+1112], rax
	mov rax, QWORD PTR [rdx+24]
	bswap rax
	mov QWORD PTR [rdi+1120], rax
	mov rax, QWORD PTR [rdx+16]
	bswap rax
	mov QWORD PTR [rdi+1128], rax
	mov rax, QWORD PTR [rdx+8]
	bswap rax
	mov QWORD PTR [rdi+1136], rax
	mov rax, QWORD PTR [rdx]
	bswap rax
	mov QWORD PTR [rdi+1144], rax
	movabs rax, -1
	mov QWORD PTR [rdi+64], rax
	movabs rax, 4294967295
	mov QWORD PTR [rdi+72], rax
	movabs rax, 0
	mov QWORD PTR [rdi+80], rax
	movabs rax, -4294967295
	mov QWORD PTR [rdi+88], rax
	movabs rax, -884452912994769583
	mov QWORD PTR [rdi+96], rax
	movabs rax, -4834901526196019580
	mov QWORD PTR [rdi+104], rax
	movabs rax, -1
	mov QWORD PTR [rdi+112], rax
	movabs rax, -4294967296
	mov QWORD PTR [rdi+120], rax
	movabs rax, 0
	mov QWORD PTR [rdi+160], rax
	movabs rax, 0
	mov QWORD PTR [rdi+168], rax
	movabs rax, 0
	mov QWORD PTR [rdi+176], rax
	movabs rax, 0
	mov QWORD PTR [rdi+184], rax
	movabs rax, 1
	mov QWORD PTR [rdi+192], rax
	movabs rax, 0
	mov QWORD PTR [rdi+200], rax
	movabs rax, 0
	mov QWORD PTR [rdi+208], rax
	movabs rax, 0
	mov QWORD PTR [rdi+216], rax
	movabs rax, 1
	mov QWORD PTR [rdi+224], rax
	movabs rax, -4294967296
	mov QWORD PTR [rdi+232], rax
	movabs rax, -1
	mov QWORD PTR [rdi+240], rax
	movabs rax, 4294967294
	mov QWORD PTR [rdi+248], rax
	movabs rax, -4
	mov QWORD PTR [rdi+256], rax
	movabs rax, 17179869183
	mov QWORD PTR [rdi+264], rax
	movabs rax, 0
	mov QWORD PTR [rdi+272], rax
	movabs rax, -17179869180
	mov QWORD PTR [rdi+280], rax
	movabs rax, -8514444157349119585
	mov QWORD PTR [rdi+288], rax
	movabs rax, 490911490938540466
	mov QWORD PTR [rdi+296], rax
	movabs rax, -5699760509517853564
	mov QWORD PTR [rdi+304], rax
	movabs rax, -7741667585760569188
	mov QWORD PTR [rdi+312], rax
	movabs rax, 8784043285714375740
	mov QWORD PTR [rdi+320], rax
	movabs rax, 8483257759279461889
	mov QWORD PTR [rdi+328], rax
	movabs rax, 8789745728267363600
	mov QWORD PTR [rdi+336], rax
	movabs rax, 1770019616739251654
	mov QWORD PTR [rdi+344], rax
	movabs rax, -2453807210370345462
	mov QWORD PTR [rdi+352], rax
	movabs rax, -8409706061646666660
	mov QWORD PTR [rdi+360], rax
	movabs rax, -3249199208764148955
	mov QWORD PTR [rdi+368], rax
	movabs rax, -8830996915122840187
	mov QWORD PTR [rdi+376], rax
	movabs rax, -8996981949549908318
	mov QWORD PTR [rdi+384], rax
	movabs rax, 5087230966250696614
	mov QWORD PTR [rdi+392], rax
	movabs rax, 2901921493521525849
	mov QWORD PTR [rdi+400], rax
	movabs rax, 7413256579398063648
	mov QWORD PTR [rdi+408], rax
	movabs rax, 884452912994769583
	mov QWORD PTR [rdi+416], rax
	movabs rax, 4834901526196019579
	mov QWORD PTR [rdi+424], rax
	movabs rax, 0
	mov QWORD PTR [rdi+432], rax
	movabs rax, 4294967295
	mov QWORD PTR [rdi+440], rax
	movabs rax, -3
	mov QWORD PTR [rdi+448], rax
	movabs rax, 4294967295
	mov QWORD PTR [rdi+456], rax
	movabs rax, 0
	mov QWORD PTR [rdi+464], rax
	movabs rax, -4294967295
	mov QWORD PTR [rdi+472], rax
	movabs rax, -884452912994769585
	mov QWORD PTR [rdi+480], rax
	movabs rax, -4834901526196019580
	mov QWORD PTR [rdi+488], rax
	movabs rax, -1
	mov QWORD PTR [rdi+496], rax
	movabs rax, -4294967296
	mov QWORD PTR [rdi+504], rax
	movabs rax, 0
	mov QWORD PTR [rdi+512], rax
	movabs rax, 0
	mov QWORD PTR [rdi+520], rax
	movabs rax, 0
	mov QWORD PTR [rdi+528], rax
	movabs rax, 0
	mov QWORD PTR [rdi+536], rax
	movabs rax, 1
	mov QWORD PTR [rdi+544], rax
	movabs rax, -4294967296
	mov QWORD PTR [rdi+552], rax
	movabs rax, -1
	mov QWORD PTR [rdi+560], rax
	movabs rax, 4294967294
	mov QWORD PTR [rdi+568], rax
	movabs rax, 0
	mov QWORD PTR [rdi+576], rax
	movabs rax, 0
	mov QWORD PTR [rdi+584], rax
	movabs rax, 0
	mov QWORD PTR [rdi+592], rax
	movabs rax, 0
	mov QWORD PTR [rdi+600], rax
	movabs rax, -1
	mov QWORD PTR [rdi+1472], rax
	mov rsi, r14
	mov ebx, 0
20:
	movzx eax, BYTE PTR [rdi+rbx*1+1056]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1504], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1505], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1506], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1507], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1508], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1509], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1510], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1511], dl
	add rbx, 1
	cmp rbx, 32
	jne 20b
	mov ebx, 0
21:
	movzx eax, BYTE PTR [rdi+rbx*1+448]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1768], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1769], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1770], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1771], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1772], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1773], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1774], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1775], dl
	add rbx, 1
	cmp rbx, 32
	jne 21b
	mov ebx, 0
22:
	movzx eax, BYTE PTR [rdi+rbx*1+480]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2032], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2033], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2034], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2035], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2036], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2037], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2038], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2039], dl
	add rbx, 1
	cmp rbx, 32
	jne 22b
	movabs rax, 3
	mov QWORD PTR [rdi+1312], rax
	movabs rax, -17179869185
	mov QWORD PTR [rdi+1320], rax
	movabs rax, -2
	mov QWORD PTR [rdi+1328], rax
	movabs rax, 21474836477
	mov QWORD PTR [rdi+1336], rax
	movabs rax, -2838148052449706529
	mov QWORD PTR [rdi+1344], rax
	movabs rax, -5985277524727025520
	mov QWORD PTR [rdi+1352], rax
	movabs rax, -1899920169839284522
	mov QWORD PTR [rdi+1360], rax
	movabs rax, -2580555864783501260
	mov QWORD PTR [rdi+1368], rax
	mov rdx, r9
	add rdx, 33
	mov rax, QWORD PTR [rdx+24]
	bswap rax
	mov QWORD PTR [rdi+1216], rax
	mov rax, QWORD PTR [rdx+16]
	bswap rax
	mov QWORD PTR [rdi+1224], rax
	mov rax, QWORD PTR [rdx+8]
	bswap rax
	mov QWORD PTR [rdi+1232], rax
	mov rax, QWORD PTR [rdx]
	bswap rax
	mov QWORD PTR [rdi+1240], rax
	movzx edx, BYTE PTR [r9]
	xor rdx, 4
	cmp rdx, 1
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+1472]
	and rax, rdx
	mov QWORD PTR [rdi+1472], rax
	call {vg_p256_check_point}
	movabs rax, -884452912994769583
	mov QWORD PTR [rdi+2336], rax
	movabs rax, -4834901526196019580
	mov QWORD PTR [rdi+2344], rax
	movabs rax, -1
	mov QWORD PTR [rdi+2352], rax
	movabs rax, -4294967296
	mov QWORD PTR [rdi+2360], rax
	mov r8, QWORD PTR [rdi+2336]
	sub r8, QWORD PTR [rdi+1056]
	mov QWORD PTR [rdi+2336], r8
	mov r8, QWORD PTR [rdi+2344]
	sbb r8, QWORD PTR [rdi+1064]
	mov QWORD PTR [rdi+2344], r8
	mov r8, QWORD PTR [rdi+2352]
	sbb r8, QWORD PTR [rdi+1072]
	mov QWORD PTR [rdi+2352], r8
	mov r8, QWORD PTR [rdi+2360]
	sbb r8, QWORD PTR [rdi+1080]
	mov QWORD PTR [rdi+2360], r8
	mov rcx, QWORD PTR [rdi+1056]
	and rcx, 1
	sub rcx, 1
	mov rax, QWORD PTR [rdi+1056]
	mov rdx, QWORD PTR [rdi+2336]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1056], rax
	mov rax, QWORD PTR [rdi+1064]
	mov rdx, QWORD PTR [rdi+2344]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1064], rax
	mov rax, QWORD PTR [rdi+1072]
	mov rdx, QWORD PTR [rdi+2352]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1072], rax
	mov rax, QWORD PTR [rdi+1080]
	mov rdx, QWORD PTR [rdi+2360]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1080], rax
	movabs rax, -1
	mov QWORD PTR [rdi+2336], rax
	movabs rax, -1
	mov QWORD PTR [rdi+2344], rax
	movabs rax, -1
	mov QWORD PTR [rdi+2352], rax
	movabs rax, -1
	mov QWORD PTR [rdi+2360], rax
	movabs rax, 15
	mov QWORD PTR [rdi+2368], rax
	mov r8, QWORD PTR [rdi+2336]
	add r8, QWORD PTR [rdi+1056]
	mov QWORD PTR [rdi+2336], r8
	mov r8, QWORD PTR [rdi+2344]
	adc r8, QWORD PTR [rdi+1064]
	mov QWORD PTR [rdi+2344], r8
	mov r8, QWORD PTR [rdi+2352]
	adc r8, QWORD PTR [rdi+1072]
	mov QWORD PTR [rdi+2352], r8
	mov r8, QWORD PTR [rdi+2360]
	adc r8, QWORD PTR [rdi+1080]
	mov QWORD PTR [rdi+2360], r8
	mov r8, QWORD PTR [rdi+2368]
	adc r8, 0
	mov QWORD PTR [rdi+2368], r8
	mov ebx, 0
23:
	movzx eax, BYTE PTR [rdi+rbx*1+2336]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2400], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2401], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2402], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2403], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2404], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2405], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2406], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2407], dl
	add rbx, 1
	cmp rbx, 40
	jne 23b
	mov rax, QWORD PTR [rdi+1280]
	mov QWORD PTR [rdi+5312], rax
	mov rax, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+5320], rax
	mov rax, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+5328], rax
	mov rax, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+5336], rax
	mov rax, QWORD PTR [rdi+1440]
	mov QWORD PTR [rdi+5344], rax
	mov rax, QWORD PTR [rdi+1448]
	mov QWORD PTR [rdi+5352], rax
	mov rax, QWORD PTR [rdi+1456]
	mov QWORD PTR [rdi+5360], rax
	mov rax, QWORD PTR [rdi+1464]
	mov QWORD PTR [rdi+5368], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+5376], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+5384], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+5392], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+5400], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+5408], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+5416], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+5424], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+5432], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+5440], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+5448], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+5456], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+5464], rax
	mov ebx, 1
	mov rax, rbx
	sub rax, 1
	mov ecx, 160
	mul rcx
	mov rdx, rdi
	add rdx, 2752
	add rdx, rax
	mov rax, QWORD PTR [rdi+5312]
	mov QWORD PTR [rdx], rax
	mov rax, QWORD PTR [rdi+5320]
	mov QWORD PTR [rdx+8], rax
	mov rax, QWORD PTR [rdi+5328]
	mov QWORD PTR [rdx+16], rax
	mov rax, QWORD PTR [rdi+5336]
	mov QWORD PTR [rdx+24], rax
	mov rax, QWORD PTR [rdi+5344]
	mov QWORD PTR [rdx+32], rax
	mov rax, QWORD PTR [rdi+5352]
	mov QWORD PTR [rdx+40], rax
	mov rax, QWORD PTR [rdi+5360]
	mov QWORD PTR [rdx+48], rax
	mov rax, QWORD PTR [rdi+5368]
	mov QWORD PTR [rdx+56], rax
	mov rax, QWORD PTR [rdi+5376]
	mov QWORD PTR [rdx+64], rax
	mov rax, QWORD PTR [rdi+5384]
	mov QWORD PTR [rdx+72], rax
	mov rax, QWORD PTR [rdi+5392]
	mov QWORD PTR [rdx+80], rax
	mov rax, QWORD PTR [rdi+5400]
	mov QWORD PTR [rdx+88], rax
	mov rax, QWORD PTR [rdi+5408]
	mov QWORD PTR [rdx+96], rax
	mov rax, QWORD PTR [rdi+5416]
	mov QWORD PTR [rdx+104], rax
	mov rax, QWORD PTR [rdi+5424]
	mov QWORD PTR [rdx+112], rax
	mov rax, QWORD PTR [rdi+5432]
	mov QWORD PTR [rdx+120], rax
	mov rax, QWORD PTR [rdi+5440]
	mov QWORD PTR [rdx+128], rax
	mov rax, QWORD PTR [rdi+5448]
	mov QWORD PTR [rdx+136], rax
	mov rax, QWORD PTR [rdi+5456]
	mov QWORD PTR [rdx+144], rax
	mov rax, QWORD PTR [rdi+5464]
	mov QWORD PTR [rdx+152], rax
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+1280]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1288]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1296]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1304]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+1288]
	mov ebp, 0
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
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1296]
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
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1304]
	mov ebp, 0
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
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+800], r12
	mov QWORD PTR [rdi+808], r13
	mov QWORD PTR [rdi+816], r8
	mov QWORD PTR [rdi+824], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+1440]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1440]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1448]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1456]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1464]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+1448]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1440]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1448]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1456]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1464]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1456]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1440]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1448]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1456]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1464]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1464]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1440]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1448]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1456]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1464]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+832], r12
	mov QWORD PTR [rdi+840], r13
	mov QWORD PTR [rdi+848], r8
	mov QWORD PTR [rdi+856], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+832]
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
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+840]
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
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+848]
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
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+856]
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
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
	mov QWORD PTR [rdi+880], r8
	mov QWORD PTR [rdi+888], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+1280]
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
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+1288]
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
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1296]
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
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1304]
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
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+896], r12
	mov QWORD PTR [rdi+904], r13
	mov QWORD PTR [rdi+912], r8
	mov QWORD PTR [rdi+920], r9
	mov r8, QWORD PTR [rdi+896]
	mov r9, QWORD PTR [rdi+904]
	mov r10, QWORD PTR [rdi+912]
	mov r11, QWORD PTR [rdi+920]
	mov r12d, 0
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+896], r8
	mov QWORD PTR [rdi+904], r9
	mov QWORD PTR [rdi+912], r10
	mov QWORD PTR [rdi+920], r11
	mov r8, QWORD PTR [rdi+896]
	mov r9, QWORD PTR [rdi+904]
	mov r10, QWORD PTR [rdi+912]
	mov r11, QWORD PTR [rdi+920]
	mov r12d, 0
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+896], r8
	mov QWORD PTR [rdi+904], r9
	mov QWORD PTR [rdi+912], r10
	mov QWORD PTR [rdi+920], r11
	mov r8, QWORD PTR [rdi+800]
	mov r9, QWORD PTR [rdi+808]
	mov r10, QWORD PTR [rdi+816]
	mov r11, QWORD PTR [rdi+824]
	sub r8, QWORD PTR [rdi+224]
	sbb r9, QWORD PTR [rdi+232]
	sbb r10, QWORD PTR [rdi+240]
	sbb r11, QWORD PTR [rdi+248]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+928], r8
	mov QWORD PTR [rdi+936], r9
	mov QWORD PTR [rdi+944], r10
	mov QWORD PTR [rdi+952], r11
	mov r8, QWORD PTR [rdi+928]
	mov r9, QWORD PTR [rdi+936]
	mov r10, QWORD PTR [rdi+944]
	mov r11, QWORD PTR [rdi+952]
	mov r12d, 0
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+960], r8
	mov QWORD PTR [rdi+968], r9
	mov QWORD PTR [rdi+976], r10
	mov QWORD PTR [rdi+984], r11
	mov r8, QWORD PTR [rdi+960]
	mov r9, QWORD PTR [rdi+968]
	mov r10, QWORD PTR [rdi+976]
	mov r11, QWORD PTR [rdi+984]
	mov r12d, 0
	add r8, QWORD PTR [rdi+928]
	adc r9, QWORD PTR [rdi+936]
	adc r10, QWORD PTR [rdi+944]
	adc r11, QWORD PTR [rdi+952]
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+928], r8
	mov QWORD PTR [rdi+936], r9
	mov QWORD PTR [rdi+944], r10
	mov QWORD PTR [rdi+952], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+928]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+928]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+936]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+944]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+952]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+936]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+928]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+936]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+944]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+952]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+944]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+928]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+936]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+944]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+952]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+952]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+928]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+936]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+944]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+952]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+5312], r12
	mov QWORD PTR [rdi+5320], r13
	mov QWORD PTR [rdi+5328], r8
	mov QWORD PTR [rdi+5336], r9
	mov r8, QWORD PTR [rdi+5312]
	mov r9, QWORD PTR [rdi+5320]
	mov r10, QWORD PTR [rdi+5328]
	mov r11, QWORD PTR [rdi+5336]
	sub r8, QWORD PTR [rdi+896]
	sbb r9, QWORD PTR [rdi+904]
	sbb r10, QWORD PTR [rdi+912]
	sbb r11, QWORD PTR [rdi+920]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+5312], r8
	mov QWORD PTR [rdi+5320], r9
	mov QWORD PTR [rdi+5328], r10
	mov QWORD PTR [rdi+5336], r11
	mov r8, QWORD PTR [rdi+5312]
	mov r9, QWORD PTR [rdi+5320]
	mov r10, QWORD PTR [rdi+5328]
	mov r11, QWORD PTR [rdi+5336]
	sub r8, QWORD PTR [rdi+896]
	sbb r9, QWORD PTR [rdi+904]
	sbb r10, QWORD PTR [rdi+912]
	sbb r11, QWORD PTR [rdi+920]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+5312], r8
	mov QWORD PTR [rdi+5320], r9
	mov QWORD PTR [rdi+5328], r10
	mov QWORD PTR [rdi+5336], r11
	mov r8, QWORD PTR [rdi+896]
	mov r9, QWORD PTR [rdi+904]
	mov r10, QWORD PTR [rdi+912]
	mov r11, QWORD PTR [rdi+920]
	sub r8, QWORD PTR [rdi+5312]
	sbb r9, QWORD PTR [rdi+5320]
	sbb r10, QWORD PTR [rdi+5328]
	sbb r11, QWORD PTR [rdi+5336]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+960], r8
	mov QWORD PTR [rdi+968], r9
	mov QWORD PTR [rdi+976], r10
	mov QWORD PTR [rdi+984], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+928]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+960]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+968]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+936]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+960]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+968]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+944]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+960]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+968]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+952]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+960]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+968]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+5344], r12
	mov QWORD PTR [rdi+5352], r13
	mov QWORD PTR [rdi+5360], r8
	mov QWORD PTR [rdi+5368], r9
	mov r8, QWORD PTR [rdi+864]
	mov r9, QWORD PTR [rdi+872]
	mov r10, QWORD PTR [rdi+880]
	mov r11, QWORD PTR [rdi+888]
	mov r12d, 0
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+864], r8
	mov QWORD PTR [rdi+872], r9
	mov QWORD PTR [rdi+880], r10
	mov QWORD PTR [rdi+888], r11
	mov r8, QWORD PTR [rdi+864]
	mov r9, QWORD PTR [rdi+872]
	mov r10, QWORD PTR [rdi+880]
	mov r11, QWORD PTR [rdi+888]
	mov r12d, 0
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+864], r8
	mov QWORD PTR [rdi+872], r9
	mov QWORD PTR [rdi+880], r10
	mov QWORD PTR [rdi+888], r11
	mov r8, QWORD PTR [rdi+864]
	mov r9, QWORD PTR [rdi+872]
	mov r10, QWORD PTR [rdi+880]
	mov r11, QWORD PTR [rdi+888]
	mov r12d, 0
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+864], r8
	mov QWORD PTR [rdi+872], r9
	mov QWORD PTR [rdi+880], r10
	mov QWORD PTR [rdi+888], r11
	mov r8, QWORD PTR [rdi+5344]
	mov r9, QWORD PTR [rdi+5352]
	mov r10, QWORD PTR [rdi+5360]
	mov r11, QWORD PTR [rdi+5368]
	sub r8, QWORD PTR [rdi+864]
	sbb r9, QWORD PTR [rdi+872]
	sbb r10, QWORD PTR [rdi+880]
	sbb r11, QWORD PTR [rdi+888]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+5344], r8
	mov QWORD PTR [rdi+5352], r9
	mov QWORD PTR [rdi+5360], r10
	mov QWORD PTR [rdi+5368], r11
	mov r8, QWORD PTR [rdi+1440]
	mov r9, QWORD PTR [rdi+1448]
	mov r10, QWORD PTR [rdi+1456]
	mov r11, QWORD PTR [rdi+1464]
	mov r12d, 0
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+5376], r8
	mov QWORD PTR [rdi+5384], r9
	mov QWORD PTR [rdi+5392], r10
	mov QWORD PTR [rdi+5400], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+5376]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+5376]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5384]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5392]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5400]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+5384]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+5376]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5384]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5392]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5400]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+5392]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+5376]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5384]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5392]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5400]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+5400]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+5376]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5384]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5392]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5400]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+5408], r12
	mov QWORD PTR [rdi+5416], r13
	mov QWORD PTR [rdi+5424], r8
	mov QWORD PTR [rdi+5432], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+5408]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+5376]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5384]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5392]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5400]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+5416]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+5376]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5384]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5392]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5400]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+5424]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+5376]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5384]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5392]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5400]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+5432]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+5376]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5384]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5392]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5400]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+5440], r12
	mov QWORD PTR [rdi+5448], r13
	mov QWORD PTR [rdi+5456], r8
	mov QWORD PTR [rdi+5464], r9
	mov rax, QWORD PTR [rdi+5312]
	mov QWORD PTR [rdi+608], rax
	mov rax, QWORD PTR [rdi+5320]
	mov QWORD PTR [rdi+616], rax
	mov rax, QWORD PTR [rdi+5328]
	mov QWORD PTR [rdi+624], rax
	mov rax, QWORD PTR [rdi+5336]
	mov QWORD PTR [rdi+632], rax
	mov rax, QWORD PTR [rdi+5344]
	mov QWORD PTR [rdi+640], rax
	mov rax, QWORD PTR [rdi+5352]
	mov QWORD PTR [rdi+648], rax
	mov rax, QWORD PTR [rdi+5360]
	mov QWORD PTR [rdi+656], rax
	mov rax, QWORD PTR [rdi+5368]
	mov QWORD PTR [rdi+664], rax
	mov rax, QWORD PTR [rdi+896]
	mov QWORD PTR [rdi+5312], rax
	mov rax, QWORD PTR [rdi+904]
	mov QWORD PTR [rdi+5320], rax
	mov rax, QWORD PTR [rdi+912]
	mov QWORD PTR [rdi+5328], rax
	mov rax, QWORD PTR [rdi+920]
	mov QWORD PTR [rdi+5336], rax
	mov rax, QWORD PTR [rdi+864]
	mov QWORD PTR [rdi+5344], rax
	mov rax, QWORD PTR [rdi+872]
	mov QWORD PTR [rdi+5352], rax
	mov rax, QWORD PTR [rdi+880]
	mov QWORD PTR [rdi+5360], rax
	mov rax, QWORD PTR [rdi+888]
	mov QWORD PTR [rdi+5368], rax
24:
	add rbx, 1
	mov r8, QWORD PTR [rdi+608]
	mov r9, QWORD PTR [rdi+616]
	mov r10, QWORD PTR [rdi+624]
	mov r11, QWORD PTR [rdi+632]
	sub r8, QWORD PTR [rdi+5312]
	sbb r9, QWORD PTR [rdi+5320]
	sbb r10, QWORD PTR [rdi+5328]
	sbb r11, QWORD PTR [rdi+5336]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+800], r8
	mov QWORD PTR [rdi+808], r9
	mov QWORD PTR [rdi+816], r10
	mov QWORD PTR [rdi+824], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+800]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+800]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+808]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+808]
	mov ebp, 0
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
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+816]
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
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+824]
	mov ebp, 0
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
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+832], r12
	mov QWORD PTR [rdi+840], r13
	mov QWORD PTR [rdi+848], r8
	mov QWORD PTR [rdi+856], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+5376]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+800]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+808]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+5384]
	mov ebp, 0
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
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+5392]
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
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+5400]
	mov ebp, 0
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
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+5376], r12
	mov QWORD PTR [rdi+5384], r13
	mov QWORD PTR [rdi+5392], r8
	mov QWORD PTR [rdi+5400], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+608]
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
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+616]
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
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+624]
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
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+632]
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
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+608], r12
	mov QWORD PTR [rdi+616], r13
	mov QWORD PTR [rdi+624], r8
	mov QWORD PTR [rdi+632], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+5312]
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
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+5320]
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
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+5328]
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
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+5336]
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
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+896], r12
	mov QWORD PTR [rdi+904], r13
	mov QWORD PTR [rdi+912], r8
	mov QWORD PTR [rdi+920], r9
	mov r8, QWORD PTR [rdi+640]
	mov r9, QWORD PTR [rdi+648]
	mov r10, QWORD PTR [rdi+656]
	mov r11, QWORD PTR [rdi+664]
	sub r8, QWORD PTR [rdi+5344]
	sbb r9, QWORD PTR [rdi+5352]
	sbb r10, QWORD PTR [rdi+5360]
	sbb r11, QWORD PTR [rdi+5368]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+928], r8
	mov QWORD PTR [rdi+936], r9
	mov QWORD PTR [rdi+944], r10
	mov QWORD PTR [rdi+952], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+928]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+928]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+936]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+944]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+952]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+936]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+928]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+936]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+944]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+952]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+944]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+928]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+936]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+944]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+952]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+952]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+928]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+936]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+944]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+952]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+960], r12
	mov QWORD PTR [rdi+968], r13
	mov QWORD PTR [rdi+976], r8
	mov QWORD PTR [rdi+984], r9
	mov r8, QWORD PTR [rdi+608]
	mov r9, QWORD PTR [rdi+616]
	mov r10, QWORD PTR [rdi+624]
	mov r11, QWORD PTR [rdi+632]
	sub r8, QWORD PTR [rdi+896]
	sbb r9, QWORD PTR [rdi+904]
	sbb r10, QWORD PTR [rdi+912]
	sbb r11, QWORD PTR [rdi+920]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+864], r8
	mov QWORD PTR [rdi+872], r9
	mov QWORD PTR [rdi+880], r10
	mov QWORD PTR [rdi+888], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+640]
	mov ebp, 0
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
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+648]
	mov ebp, 0
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
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+656]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+864]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+872]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+664]
	mov ebp, 0
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
	mov rax, QWORD PTR [rdi+880]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+888]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+640], r12
	mov QWORD PTR [rdi+648], r13
	mov QWORD PTR [rdi+656], r8
	mov QWORD PTR [rdi+664], r9
	mov r8, QWORD PTR [rdi+960]
	mov r9, QWORD PTR [rdi+968]
	mov r10, QWORD PTR [rdi+976]
	mov r11, QWORD PTR [rdi+984]
	sub r8, QWORD PTR [rdi+608]
	sbb r9, QWORD PTR [rdi+616]
	sbb r10, QWORD PTR [rdi+624]
	sbb r11, QWORD PTR [rdi+632]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+5312], r8
	mov QWORD PTR [rdi+5320], r9
	mov QWORD PTR [rdi+5328], r10
	mov QWORD PTR [rdi+5336], r11
	mov r8, QWORD PTR [rdi+5312]
	mov r9, QWORD PTR [rdi+5320]
	mov r10, QWORD PTR [rdi+5328]
	mov r11, QWORD PTR [rdi+5336]
	sub r8, QWORD PTR [rdi+896]
	sbb r9, QWORD PTR [rdi+904]
	sbb r10, QWORD PTR [rdi+912]
	sbb r11, QWORD PTR [rdi+920]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+5312], r8
	mov QWORD PTR [rdi+5320], r9
	mov QWORD PTR [rdi+5328], r10
	mov QWORD PTR [rdi+5336], r11
	mov r8, QWORD PTR [rdi+608]
	mov r9, QWORD PTR [rdi+616]
	mov r10, QWORD PTR [rdi+624]
	mov r11, QWORD PTR [rdi+632]
	sub r8, QWORD PTR [rdi+5312]
	sbb r9, QWORD PTR [rdi+5320]
	sbb r10, QWORD PTR [rdi+5328]
	sbb r11, QWORD PTR [rdi+5336]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+5344], r8
	mov QWORD PTR [rdi+5352], r9
	mov QWORD PTR [rdi+5360], r10
	mov QWORD PTR [rdi+5368], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+928]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+5344]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5352]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5360]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5368]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+936]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+5344]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5352]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5360]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5368]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+944]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+5344]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5352]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5360]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5368]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+952]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+5344]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5352]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5360]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5368]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+5344], r12
	mov QWORD PTR [rdi+5352], r13
	mov QWORD PTR [rdi+5360], r8
	mov QWORD PTR [rdi+5368], r9
	mov r8, QWORD PTR [rdi+5344]
	mov r9, QWORD PTR [rdi+5352]
	mov r10, QWORD PTR [rdi+5360]
	mov r11, QWORD PTR [rdi+5368]
	sub r8, QWORD PTR [rdi+640]
	sbb r9, QWORD PTR [rdi+648]
	sbb r10, QWORD PTR [rdi+656]
	sbb r11, QWORD PTR [rdi+664]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+5344], r8
	mov QWORD PTR [rdi+5352], r9
	mov QWORD PTR [rdi+5360], r10
	mov QWORD PTR [rdi+5368], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+5408]
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
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+5416]
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
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+5424]
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
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+5432]
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
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+5408], r12
	mov QWORD PTR [rdi+5416], r13
	mov QWORD PTR [rdi+5424], r8
	mov QWORD PTR [rdi+5432], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+5408]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+5376]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5384]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5392]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5400]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+5416]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+5376]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5384]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5392]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5400]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+5424]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+5376]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5384]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5392]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5400]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+5432]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+5376]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5384]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5392]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5400]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+5440], r12
	mov QWORD PTR [rdi+5448], r13
	mov QWORD PTR [rdi+5456], r8
	mov QWORD PTR [rdi+5464], r9
	mov rax, rbx
	sub rax, 1
	mov ecx, 160
	mul rcx
	mov rdx, rdi
	add rdx, 2752
	add rdx, rax
	mov rax, QWORD PTR [rdi+5312]
	mov QWORD PTR [rdx], rax
	mov rax, QWORD PTR [rdi+5320]
	mov QWORD PTR [rdx+8], rax
	mov rax, QWORD PTR [rdi+5328]
	mov QWORD PTR [rdx+16], rax
	mov rax, QWORD PTR [rdi+5336]
	mov QWORD PTR [rdx+24], rax
	mov rax, QWORD PTR [rdi+5344]
	mov QWORD PTR [rdx+32], rax
	mov rax, QWORD PTR [rdi+5352]
	mov QWORD PTR [rdx+40], rax
	mov rax, QWORD PTR [rdi+5360]
	mov QWORD PTR [rdx+48], rax
	mov rax, QWORD PTR [rdi+5368]
	mov QWORD PTR [rdx+56], rax
	mov rax, QWORD PTR [rdi+5376]
	mov QWORD PTR [rdx+64], rax
	mov rax, QWORD PTR [rdi+5384]
	mov QWORD PTR [rdx+72], rax
	mov rax, QWORD PTR [rdi+5392]
	mov QWORD PTR [rdx+80], rax
	mov rax, QWORD PTR [rdi+5400]
	mov QWORD PTR [rdx+88], rax
	mov rax, QWORD PTR [rdi+5408]
	mov QWORD PTR [rdx+96], rax
	mov rax, QWORD PTR [rdi+5416]
	mov QWORD PTR [rdx+104], rax
	mov rax, QWORD PTR [rdi+5424]
	mov QWORD PTR [rdx+112], rax
	mov rax, QWORD PTR [rdi+5432]
	mov QWORD PTR [rdx+120], rax
	mov rax, QWORD PTR [rdi+5440]
	mov QWORD PTR [rdx+128], rax
	mov rax, QWORD PTR [rdi+5448]
	mov QWORD PTR [rdx+136], rax
	mov rax, QWORD PTR [rdi+5456]
	mov QWORD PTR [rdx+144], rax
	mov rax, QWORD PTR [rdi+5464]
	mov QWORD PTR [rdx+152], rax
	cmp rbx, 16
	jne 24b
	mov ebx, 51
	mov rax, QWORD PTR [rdi+1280]
	mov QWORD PTR [rdi+512], rax
	mov rax, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+520], rax
	mov rax, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+528], rax
	mov rax, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+536], rax
	mov rax, QWORD PTR [rdi+1440]
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rdi+1448]
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rdi+1456]
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rdi+1464]
	mov QWORD PTR [rdi+568], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+576], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+584], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+592], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+600], rax
	sub rbx, 1
	mov rax, rbx
	mov ecx, 5
	mul rcx
	mov rcx, rax
	mov eax, 0
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2405]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2404]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2403]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2402]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2401]
	add rax, rdx
	mov rdx, rax
	shr rdx, 4
	sub rdx, 1
	xor rax, rdx
	and rax, 15
	add rax, 1
	mov r8, rax
	mov rdx, rdi
	add rdx, 2752
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
	mov ecx, 1
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+16]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+32]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+48]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+64]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+80]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+96]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+112]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+128]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+144]
	pand xmm14, xmm15
	por xmm9, xmm14
	mov ecx, 2
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+160]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+176]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+192]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+208]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+224]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+240]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+256]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+272]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+288]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+304]
	pand xmm14, xmm15
	por xmm9, xmm14
	mov ecx, 3
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+320]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+336]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+352]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+368]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+384]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+400]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+416]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+432]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+448]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+464]
	pand xmm14, xmm15
	por xmm9, xmm14
	mov ecx, 4
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+480]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+496]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+512]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+528]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+544]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+560]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+576]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+592]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+608]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+624]
	pand xmm14, xmm15
	por xmm9, xmm14
	mov ecx, 5
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+640]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+656]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+672]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+688]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+704]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+720]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+736]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+752]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+768]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+784]
	pand xmm14, xmm15
	por xmm9, xmm14
	mov ecx, 6
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+800]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+816]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+832]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+848]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+864]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+880]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+896]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+912]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+928]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+944]
	pand xmm14, xmm15
	por xmm9, xmm14
	mov ecx, 7
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+960]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+976]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+992]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1008]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1024]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1040]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1056]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1072]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1088]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1104]
	pand xmm14, xmm15
	por xmm9, xmm14
	mov ecx, 8
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+1120]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1136]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1152]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1168]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1184]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1200]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1216]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1232]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1248]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1264]
	pand xmm14, xmm15
	por xmm9, xmm14
	mov ecx, 9
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+1280]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1296]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1312]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1328]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1344]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1360]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1376]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1392]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1408]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1424]
	pand xmm14, xmm15
	por xmm9, xmm14
	mov ecx, 10
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+1440]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1456]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1472]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1488]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1504]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1520]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1536]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1552]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1568]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1584]
	pand xmm14, xmm15
	por xmm9, xmm14
	mov ecx, 11
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+1600]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1616]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1632]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1648]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1664]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1680]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1696]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1712]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1728]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1744]
	pand xmm14, xmm15
	por xmm9, xmm14
	mov ecx, 12
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+1760]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1776]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1792]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1808]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1824]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1840]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1856]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1872]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1888]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1904]
	pand xmm14, xmm15
	por xmm9, xmm14
	mov ecx, 13
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+1920]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1936]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1952]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1968]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1984]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2000]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2016]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2032]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2048]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2064]
	pand xmm14, xmm15
	por xmm9, xmm14
	mov ecx, 14
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+2080]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2096]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2112]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2128]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2144]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2160]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2176]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2192]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2208]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2224]
	pand xmm14, xmm15
	por xmm9, xmm14
	mov ecx, 15
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+2240]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2256]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2272]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2288]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2304]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2320]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2336]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2352]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2368]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2384]
	pand xmm14, xmm15
	por xmm9, xmm14
	mov ecx, 16
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+2400]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2416]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2432]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2448]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2464]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2480]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2496]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2512]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2528]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2544]
	pand xmm14, xmm15
	por xmm9, xmm14
	movdqu XMMWORD PTR [rdi+5312], xmm0
	movdqu XMMWORD PTR [rdi+5328], xmm1
	movdqu XMMWORD PTR [rdi+5344], xmm2
	movdqu XMMWORD PTR [rdi+5360], xmm3
	movdqu XMMWORD PTR [rdi+5376], xmm4
	movdqu XMMWORD PTR [rdi+5392], xmm5
	movdqu XMMWORD PTR [rdi+5408], xmm6
	movdqu XMMWORD PTR [rdi+5424], xmm7
	movdqu XMMWORD PTR [rdi+5440], xmm8
	movdqu XMMWORD PTR [rdi+5456], xmm9
	mov r8, QWORD PTR [rdi+160]
	mov r9, QWORD PTR [rdi+168]
	mov r10, QWORD PTR [rdi+176]
	mov r11, QWORD PTR [rdi+184]
	sub r8, QWORD PTR [rdi+5344]
	sbb r9, QWORD PTR [rdi+5352]
	sbb r10, QWORD PTR [rdi+5360]
	sbb r11, QWORD PTR [rdi+5368]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+1024], r8
	mov QWORD PTR [rdi+1032], r9
	mov QWORD PTR [rdi+1040], r10
	mov QWORD PTR [rdi+1048], r11
	mov rax, rbx
	mov ecx, 5
	mul rcx
	mov rcx, rax
	movzx eax, BYTE PTR [rdi+rcx*1+2405]
	sub rax, 1
	mov rcx, rax
	mov rax, QWORD PTR [rdi+5344]
	mov rdx, QWORD PTR [rdi+1024]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+5344], rax
	mov rax, QWORD PTR [rdi+5352]
	mov rdx, QWORD PTR [rdi+1032]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+5352], rax
	mov rax, QWORD PTR [rdi+5360]
	mov rdx, QWORD PTR [rdi+1040]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+5360], rax
	mov rax, QWORD PTR [rdi+5368]
	mov rdx, QWORD PTR [rdi+1048]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+5368], rax
	add rbx, 1
25:
	sub rbx, 1
	add rbx, 20480
26:
	mov r8, QWORD PTR [rdi+544]
	mov r9, QWORD PTR [rdi+552]
	mov r10, QWORD PTR [rdi+560]
	mov r11, QWORD PTR [rdi+568]
	mov r12d, 0
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+832], r8
	mov QWORD PTR [rdi+840], r9
	mov QWORD PTR [rdi+848], r10
	mov QWORD PTR [rdi+856], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+576]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+584]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+592]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+600]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+800], r12
	mov QWORD PTR [rdi+808], r13
	mov QWORD PTR [rdi+816], r8
	mov QWORD PTR [rdi+824], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+832]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+840]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+848]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+856]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+576], r12
	mov QWORD PTR [rdi+584], r13
	mov QWORD PTR [rdi+592], r8
	mov QWORD PTR [rdi+600], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+832]
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
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+840]
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
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+848]
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
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+856]
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
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+832], r12
	mov QWORD PTR [rdi+840], r13
	mov QWORD PTR [rdi+848], r8
	mov QWORD PTR [rdi+856], r9
	mov r8, QWORD PTR [rdi+512]
	mov r9, QWORD PTR [rdi+520]
	mov r10, QWORD PTR [rdi+528]
	mov r11, QWORD PTR [rdi+536]
	sub r8, QWORD PTR [rdi+800]
	sbb r9, QWORD PTR [rdi+808]
	sbb r10, QWORD PTR [rdi+816]
	sbb r11, QWORD PTR [rdi+824]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+896], r8
	mov QWORD PTR [rdi+904], r9
	mov QWORD PTR [rdi+912], r10
	mov QWORD PTR [rdi+920], r11
	mov r8, QWORD PTR [rdi+512]
	mov r9, QWORD PTR [rdi+520]
	mov r10, QWORD PTR [rdi+528]
	mov r11, QWORD PTR [rdi+536]
	mov r12d, 0
	add r8, QWORD PTR [rdi+800]
	adc r9, QWORD PTR [rdi+808]
	adc r10, QWORD PTR [rdi+816]
	adc r11, QWORD PTR [rdi+824]
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+928], r8
	mov QWORD PTR [rdi+936], r9
	mov QWORD PTR [rdi+944], r10
	mov QWORD PTR [rdi+952], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+896]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+928]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+936]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+944]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+952]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+904]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+928]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+936]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+944]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+952]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+912]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+928]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+936]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+944]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+952]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+920]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+928]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+936]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+944]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+952]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+896], r12
	mov QWORD PTR [rdi+904], r13
	mov QWORD PTR [rdi+912], r8
	mov QWORD PTR [rdi+920], r9
	mov r8, QWORD PTR [rdi+896]
	mov r9, QWORD PTR [rdi+904]
	mov r10, QWORD PTR [rdi+912]
	mov r11, QWORD PTR [rdi+920]
	mov r12d, 0
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+928], r8
	mov QWORD PTR [rdi+936], r9
	mov QWORD PTR [rdi+944], r10
	mov QWORD PTR [rdi+952], r11
	mov r8, QWORD PTR [rdi+928]
	mov r9, QWORD PTR [rdi+936]
	mov r10, QWORD PTR [rdi+944]
	mov r11, QWORD PTR [rdi+952]
	mov r12d, 0
	add r8, QWORD PTR [rdi+896]
	adc r9, QWORD PTR [rdi+904]
	adc r10, QWORD PTR [rdi+912]
	adc r11, QWORD PTR [rdi+920]
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+896], r8
	mov QWORD PTR [rdi+904], r9
	mov QWORD PTR [rdi+912], r10
	mov QWORD PTR [rdi+920], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+512]
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
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+520]
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
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+528]
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
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+536]
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
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
	mov QWORD PTR [rdi+880], r8
	mov QWORD PTR [rdi+888], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+832]
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
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+840]
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
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+848]
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
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+856]
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
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+832], r12
	mov QWORD PTR [rdi+840], r13
	mov QWORD PTR [rdi+848], r8
	mov QWORD PTR [rdi+856], r9
	mov r8, QWORD PTR [rdi+832]
	mov r9, QWORD PTR [rdi+840]
	mov r10, QWORD PTR [rdi+848]
	mov r11, QWORD PTR [rdi+856]
	mov rax, r8
	and rax, 1
	mov ecx, 0
	sub rcx, rax
	mov rdx, rcx
	shr rdx, 32
	movabs rbp, -4294967295
	and rbp, rcx
	mov r12d, 0
	add r8, rcx
	adc r9, rdx
	adc r10, 0
	adc r11, rbp
	adc r12, 0
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
	mov QWORD PTR [rdi+832], r8
	mov QWORD PTR [rdi+840], r9
	mov QWORD PTR [rdi+848], r10
	mov QWORD PTR [rdi+856], r11
	mov r8, QWORD PTR [rdi+864]
	mov r9, QWORD PTR [rdi+872]
	mov r10, QWORD PTR [rdi+880]
	mov r11, QWORD PTR [rdi+888]
	mov r12d, 0
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+928], r8
	mov QWORD PTR [rdi+936], r9
	mov QWORD PTR [rdi+944], r10
	mov QWORD PTR [rdi+952], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+896]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+904]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+912]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+920]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+512], r12
	mov QWORD PTR [rdi+520], r13
	mov QWORD PTR [rdi+528], r8
	mov QWORD PTR [rdi+536], r9
	mov r8, QWORD PTR [rdi+512]
	mov r9, QWORD PTR [rdi+520]
	mov r10, QWORD PTR [rdi+528]
	mov r11, QWORD PTR [rdi+536]
	sub r8, QWORD PTR [rdi+928]
	sbb r9, QWORD PTR [rdi+936]
	sbb r10, QWORD PTR [rdi+944]
	sbb r11, QWORD PTR [rdi+952]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+512], r8
	mov QWORD PTR [rdi+520], r9
	mov QWORD PTR [rdi+528], r10
	mov QWORD PTR [rdi+536], r11
	mov r8, QWORD PTR [rdi+864]
	mov r9, QWORD PTR [rdi+872]
	mov r10, QWORD PTR [rdi+880]
	mov r11, QWORD PTR [rdi+888]
	sub r8, QWORD PTR [rdi+512]
	sbb r9, QWORD PTR [rdi+520]
	sbb r10, QWORD PTR [rdi+528]
	sbb r11, QWORD PTR [rdi+536]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+544], r8
	mov QWORD PTR [rdi+552], r9
	mov QWORD PTR [rdi+560], r10
	mov QWORD PTR [rdi+568], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+896]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+904]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+912]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+920]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+544], r12
	mov QWORD PTR [rdi+552], r13
	mov QWORD PTR [rdi+560], r8
	mov QWORD PTR [rdi+568], r9
	mov r8, QWORD PTR [rdi+544]
	mov r9, QWORD PTR [rdi+552]
	mov r10, QWORD PTR [rdi+560]
	mov r11, QWORD PTR [rdi+568]
	sub r8, QWORD PTR [rdi+832]
	sbb r9, QWORD PTR [rdi+840]
	sbb r10, QWORD PTR [rdi+848]
	sbb r11, QWORD PTR [rdi+856]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+544], r8
	mov QWORD PTR [rdi+552], r9
	mov QWORD PTR [rdi+560], r10
	mov QWORD PTR [rdi+568], r11
	sub rbx, 4096
	cmp rbx, 4096
	jae 26b
	sub rbx, 1
	mov rax, rbx
	mov ecx, 5
	mul rcx
	mov rcx, rax
	mov eax, 0
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2405]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2404]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2403]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2402]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2401]
	add rax, rdx
	mov rdx, rax
	shr rdx, 4
	sub rdx, 1
	xor rax, rdx
	and rax, 15
	add rax, 1
	mov r8, rax
	add rbx, 1
	movq xmm13, r8
	pshufd xmm13, xmm13, 0
	mov ecx, 1
	movq xmm12, rcx
	pshufd xmm12, xmm12, 0
	movdqa xmm11, xmm12
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
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+576]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+584]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+592]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+600]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+800], r12
	mov QWORD PTR [rdi+808], r13
	mov QWORD PTR [rdi+816], r8
	mov QWORD PTR [rdi+824], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+512]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+5408]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5416]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5424]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5432]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+520]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+5408]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5416]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5424]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5432]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+528]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+5408]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5416]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5424]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5432]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+536]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+5408]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5416]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5424]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5432]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
	mov QWORD PTR [rdi+880], r8
	mov QWORD PTR [rdi+888], r9
	mov rdx, rdi
	add rdx, 2752
	movdqa xmm15, xmm11
	pcmpeqd xmm15, xmm13
	paddd xmm11, xmm12
	movdqu xmm14, XMMWORD PTR [rdx]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+16]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+32]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+48]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+64]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+80]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+96]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+112]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+128]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+144]
	pand xmm14, xmm15
	por xmm9, xmm14
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+5312]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+800]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+808]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+5320]
	mov ebp, 0
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
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+5328]
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
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+5336]
	mov ebp, 0
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
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+896], r12
	mov QWORD PTR [rdi+904], r13
	mov QWORD PTR [rdi+912], r8
	mov QWORD PTR [rdi+920], r9
	mov rdx, rdi
	add rdx, 2752
	movdqa xmm15, xmm11
	pcmpeqd xmm15, xmm13
	paddd xmm11, xmm12
	movdqu xmm14, XMMWORD PTR [rdx+160]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+176]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+192]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+208]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+224]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+240]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+256]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+272]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+288]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+304]
	pand xmm14, xmm15
	por xmm9, xmm14
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+544]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+5440]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5448]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5456]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5464]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+552]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+5440]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5448]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5456]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5464]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+560]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+5440]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5448]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5456]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5464]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+568]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+5440]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5448]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5456]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5464]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+928], r12
	mov QWORD PTR [rdi+936], r13
	mov QWORD PTR [rdi+944], r8
	mov QWORD PTR [rdi+952], r9
	mov rdx, rdi
	add rdx, 2752
	movdqa xmm15, xmm11
	pcmpeqd xmm15, xmm13
	paddd xmm11, xmm12
	movdqu xmm14, XMMWORD PTR [rdx+320]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+336]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+352]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+368]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+384]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+400]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+416]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+432]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+448]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+464]
	pand xmm14, xmm15
	por xmm9, xmm14
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+5344]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+5352]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+5360]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+5368]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+960], r12
	mov QWORD PTR [rdi+968], r13
	mov QWORD PTR [rdi+976], r8
	mov QWORD PTR [rdi+984], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+960]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+800]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+808]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+968]
	mov ebp, 0
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
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+976]
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
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+984]
	mov ebp, 0
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
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+960], r12
	mov QWORD PTR [rdi+968], r13
	mov QWORD PTR [rdi+976], r8
	mov QWORD PTR [rdi+984], r9
	mov rdx, rdi
	add rdx, 2752
	movdqa xmm15, xmm11
	pcmpeqd xmm15, xmm13
	paddd xmm11, xmm12
	movdqu xmm14, XMMWORD PTR [rdx+480]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+496]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+512]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+528]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+544]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+560]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+576]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+592]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+608]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+624]
	pand xmm14, xmm15
	por xmm9, xmm14
	mov r8, QWORD PTR [rdi+896]
	mov r9, QWORD PTR [rdi+904]
	mov r10, QWORD PTR [rdi+912]
	mov r11, QWORD PTR [rdi+920]
	sub r8, QWORD PTR [rdi+864]
	sbb r9, QWORD PTR [rdi+872]
	sbb r10, QWORD PTR [rdi+880]
	sbb r11, QWORD PTR [rdi+888]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+896], r8
	mov QWORD PTR [rdi+904], r9
	mov QWORD PTR [rdi+912], r10
	mov QWORD PTR [rdi+920], r11
	mov rdx, rdi
	add rdx, 2752
	movdqa xmm15, xmm11
	pcmpeqd xmm15, xmm13
	paddd xmm11, xmm12
	movdqu xmm14, XMMWORD PTR [rdx+640]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+656]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+672]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+688]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+704]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+720]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+736]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+752]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+768]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+784]
	pand xmm14, xmm15
	por xmm9, xmm14
	mov r8, QWORD PTR [rdi+960]
	mov r9, QWORD PTR [rdi+968]
	mov r10, QWORD PTR [rdi+976]
	mov r11, QWORD PTR [rdi+984]
	sub r8, QWORD PTR [rdi+928]
	sbb r9, QWORD PTR [rdi+936]
	sbb r10, QWORD PTR [rdi+944]
	sbb r11, QWORD PTR [rdi+952]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+960], r8
	mov QWORD PTR [rdi+968], r9
	mov QWORD PTR [rdi+976], r10
	mov QWORD PTR [rdi+984], r11
	mov rdx, rdi
	add rdx, 2752
	movdqa xmm15, xmm11
	pcmpeqd xmm15, xmm13
	paddd xmm11, xmm12
	movdqu xmm14, XMMWORD PTR [rdx+800]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+816]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+832]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+848]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+864]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+880]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+896]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+912]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+928]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+944]
	pand xmm14, xmm15
	por xmm9, xmm14
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+896]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+904]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+912]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+920]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+800], r12
	mov QWORD PTR [rdi+808], r13
	mov QWORD PTR [rdi+816], r8
	mov QWORD PTR [rdi+824], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+800]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+808]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+816]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+824]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+832], r12
	mov QWORD PTR [rdi+840], r13
	mov QWORD PTR [rdi+848], r8
	mov QWORD PTR [rdi+856], r9
	mov rdx, rdi
	add rdx, 2752
	movdqa xmm15, xmm11
	pcmpeqd xmm15, xmm13
	paddd xmm11, xmm12
	movdqu xmm14, XMMWORD PTR [rdx+960]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+976]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+992]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1008]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1024]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1040]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1056]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1072]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1088]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1104]
	pand xmm14, xmm15
	por xmm9, xmm14
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+864]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+800]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+808]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+872]
	mov ebp, 0
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
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+880]
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
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+888]
	mov ebp, 0
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
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
	mov QWORD PTR [rdi+880], r8
	mov QWORD PTR [rdi+888], r9
	mov rdx, rdi
	add rdx, 2752
	movdqa xmm15, xmm11
	pcmpeqd xmm15, xmm13
	paddd xmm11, xmm12
	movdqu xmm14, XMMWORD PTR [rdx+1120]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1136]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1152]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1168]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1184]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1200]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1216]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1232]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1248]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1264]
	pand xmm14, xmm15
	por xmm9, xmm14
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+960]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+960]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+968]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+968]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+960]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+968]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+976]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+960]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+968]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+984]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+960]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+968]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+512], r12
	mov QWORD PTR [rdi+520], r13
	mov QWORD PTR [rdi+528], r8
	mov QWORD PTR [rdi+536], r9
	mov rdx, rdi
	add rdx, 2752
	movdqa xmm15, xmm11
	pcmpeqd xmm15, xmm13
	paddd xmm11, xmm12
	movdqu xmm14, XMMWORD PTR [rdx+1280]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1296]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1312]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1328]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1344]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1360]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1376]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1392]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1408]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1424]
	pand xmm14, xmm15
	por xmm9, xmm14
	mov r8, QWORD PTR [rdi+512]
	mov r9, QWORD PTR [rdi+520]
	mov r10, QWORD PTR [rdi+528]
	mov r11, QWORD PTR [rdi+536]
	sub r8, QWORD PTR [rdi+832]
	sbb r9, QWORD PTR [rdi+840]
	sbb r10, QWORD PTR [rdi+848]
	sbb r11, QWORD PTR [rdi+856]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+512], r8
	mov QWORD PTR [rdi+520], r9
	mov QWORD PTR [rdi+528], r10
	mov QWORD PTR [rdi+536], r11
	mov r8, QWORD PTR [rdi+512]
	mov r9, QWORD PTR [rdi+520]
	mov r10, QWORD PTR [rdi+528]
	mov r11, QWORD PTR [rdi+536]
	sub r8, QWORD PTR [rdi+864]
	sbb r9, QWORD PTR [rdi+872]
	sbb r10, QWORD PTR [rdi+880]
	sbb r11, QWORD PTR [rdi+888]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+512], r8
	mov QWORD PTR [rdi+520], r9
	mov QWORD PTR [rdi+528], r10
	mov QWORD PTR [rdi+536], r11
	mov rdx, rdi
	add rdx, 2752
	movdqa xmm15, xmm11
	pcmpeqd xmm15, xmm13
	paddd xmm11, xmm12
	movdqu xmm14, XMMWORD PTR [rdx+1440]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1456]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1472]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1488]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1504]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1520]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1536]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1552]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1568]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1584]
	pand xmm14, xmm15
	por xmm9, xmm14
	mov r8, QWORD PTR [rdi+512]
	mov r9, QWORD PTR [rdi+520]
	mov r10, QWORD PTR [rdi+528]
	mov r11, QWORD PTR [rdi+536]
	sub r8, QWORD PTR [rdi+864]
	sbb r9, QWORD PTR [rdi+872]
	sbb r10, QWORD PTR [rdi+880]
	sbb r11, QWORD PTR [rdi+888]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+512], r8
	mov QWORD PTR [rdi+520], r9
	mov QWORD PTR [rdi+528], r10
	mov QWORD PTR [rdi+536], r11
	mov rdx, rdi
	add rdx, 2752
	movdqa xmm15, xmm11
	pcmpeqd xmm15, xmm13
	paddd xmm11, xmm12
	movdqu xmm14, XMMWORD PTR [rdx+1600]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1616]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1632]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1648]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1664]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1680]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1696]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1712]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1728]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1744]
	pand xmm14, xmm15
	por xmm9, xmm14
	mov r8, QWORD PTR [rdi+864]
	mov r9, QWORD PTR [rdi+872]
	mov r10, QWORD PTR [rdi+880]
	mov r11, QWORD PTR [rdi+888]
	sub r8, QWORD PTR [rdi+512]
	sbb r9, QWORD PTR [rdi+520]
	sbb r10, QWORD PTR [rdi+528]
	sbb r11, QWORD PTR [rdi+536]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+544], r8
	mov QWORD PTR [rdi+552], r9
	mov QWORD PTR [rdi+560], r10
	mov QWORD PTR [rdi+568], r11
	mov rdx, rdi
	add rdx, 2752
	movdqa xmm15, xmm11
	pcmpeqd xmm15, xmm13
	paddd xmm11, xmm12
	movdqu xmm14, XMMWORD PTR [rdx+1760]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1776]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1792]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1808]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1824]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1840]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1856]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1872]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1888]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1904]
	pand xmm14, xmm15
	por xmm9, xmm14
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+960]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+968]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+976]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+984]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+544], r12
	mov QWORD PTR [rdi+552], r13
	mov QWORD PTR [rdi+560], r8
	mov QWORD PTR [rdi+568], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+928]
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
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+936]
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
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+944]
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
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+952]
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
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+928], r12
	mov QWORD PTR [rdi+936], r13
	mov QWORD PTR [rdi+944], r8
	mov QWORD PTR [rdi+952], r9
	mov rdx, rdi
	add rdx, 2752
	movdqa xmm15, xmm11
	pcmpeqd xmm15, xmm13
	paddd xmm11, xmm12
	movdqu xmm14, XMMWORD PTR [rdx+1920]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1936]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1952]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1968]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1984]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2000]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2016]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2032]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2048]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2064]
	pand xmm14, xmm15
	por xmm9, xmm14
	mov r8, QWORD PTR [rdi+544]
	mov r9, QWORD PTR [rdi+552]
	mov r10, QWORD PTR [rdi+560]
	mov r11, QWORD PTR [rdi+568]
	sub r8, QWORD PTR [rdi+928]
	sbb r9, QWORD PTR [rdi+936]
	sbb r10, QWORD PTR [rdi+944]
	sbb r11, QWORD PTR [rdi+952]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+544], r8
	mov QWORD PTR [rdi+552], r9
	mov QWORD PTR [rdi+560], r10
	mov QWORD PTR [rdi+568], r11
	mov rdx, rdi
	add rdx, 2752
	movdqa xmm15, xmm11
	pcmpeqd xmm15, xmm13
	paddd xmm11, xmm12
	movdqu xmm14, XMMWORD PTR [rdx+2080]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2096]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2112]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2128]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2144]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2160]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2176]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2192]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2208]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2224]
	pand xmm14, xmm15
	por xmm9, xmm14
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+576]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+5376]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5384]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5392]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5400]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+584]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+5376]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5384]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5392]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5400]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+592]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+5376]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5384]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5392]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5400]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+600]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+5376]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5384]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5392]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5400]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+576], r12
	mov QWORD PTR [rdi+584], r13
	mov QWORD PTR [rdi+592], r8
	mov QWORD PTR [rdi+600], r9
	mov rdx, rdi
	add rdx, 2752
	movdqa xmm15, xmm11
	pcmpeqd xmm15, xmm13
	paddd xmm11, xmm12
	movdqu xmm14, XMMWORD PTR [rdx+2240]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2256]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2272]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2288]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2304]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2320]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2336]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2352]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2368]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2384]
	pand xmm14, xmm15
	por xmm9, xmm14
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+576]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+584]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+592]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+600]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+576], r12
	mov QWORD PTR [rdi+584], r13
	mov QWORD PTR [rdi+592], r8
	mov QWORD PTR [rdi+600], r9
	mov rdx, rdi
	add rdx, 2752
	movdqa xmm15, xmm11
	pcmpeqd xmm15, xmm13
	paddd xmm11, xmm12
	movdqu xmm14, XMMWORD PTR [rdx+2400]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2416]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2432]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2448]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2464]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2480]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2496]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2512]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2528]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2544]
	pand xmm14, xmm15
	por xmm9, xmm14
	movdqu XMMWORD PTR [rdi+5312], xmm0
	movdqu XMMWORD PTR [rdi+5328], xmm1
	movdqu XMMWORD PTR [rdi+5344], xmm2
	movdqu XMMWORD PTR [rdi+5360], xmm3
	movdqu XMMWORD PTR [rdi+5376], xmm4
	movdqu XMMWORD PTR [rdi+5392], xmm5
	movdqu XMMWORD PTR [rdi+5408], xmm6
	movdqu XMMWORD PTR [rdi+5424], xmm7
	movdqu XMMWORD PTR [rdi+5440], xmm8
	movdqu XMMWORD PTR [rdi+5456], xmm9
	sub rbx, 1
	mov r8, QWORD PTR [rdi+160]
	mov r9, QWORD PTR [rdi+168]
	mov r10, QWORD PTR [rdi+176]
	mov r11, QWORD PTR [rdi+184]
	sub r8, QWORD PTR [rdi+5344]
	sbb r9, QWORD PTR [rdi+5352]
	sbb r10, QWORD PTR [rdi+5360]
	sbb r11, QWORD PTR [rdi+5368]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+1024], r8
	mov QWORD PTR [rdi+1032], r9
	mov QWORD PTR [rdi+1040], r10
	mov QWORD PTR [rdi+1048], r11
	mov rax, rbx
	mov ecx, 5
	mul rcx
	mov rcx, rax
	movzx eax, BYTE PTR [rdi+rcx*1+2405]
	sub rax, 1
	mov rcx, rax
	mov rax, QWORD PTR [rdi+5344]
	mov rdx, QWORD PTR [rdi+1024]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+5344], rax
	mov rax, QWORD PTR [rdi+5352]
	mov rdx, QWORD PTR [rdi+1032]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+5352], rax
	mov rax, QWORD PTR [rdi+5360]
	mov rdx, QWORD PTR [rdi+1040]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+5360], rax
	mov rax, QWORD PTR [rdi+5368]
	mov rdx, QWORD PTR [rdi+1048]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+5368], rax
	add rbx, 1
	cmp rbx, 1
	jne 25b
	sub rbx, 1
	add rbx, 20480
27:
	mov r8, QWORD PTR [rdi+544]
	mov r9, QWORD PTR [rdi+552]
	mov r10, QWORD PTR [rdi+560]
	mov r11, QWORD PTR [rdi+568]
	mov r12d, 0
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+832], r8
	mov QWORD PTR [rdi+840], r9
	mov QWORD PTR [rdi+848], r10
	mov QWORD PTR [rdi+856], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+576]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+584]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+592]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+600]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+800], r12
	mov QWORD PTR [rdi+808], r13
	mov QWORD PTR [rdi+816], r8
	mov QWORD PTR [rdi+824], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+832]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+840]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+848]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+856]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+576], r12
	mov QWORD PTR [rdi+584], r13
	mov QWORD PTR [rdi+592], r8
	mov QWORD PTR [rdi+600], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+832]
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
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+840]
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
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+848]
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
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+856]
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
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+832], r12
	mov QWORD PTR [rdi+840], r13
	mov QWORD PTR [rdi+848], r8
	mov QWORD PTR [rdi+856], r9
	mov r8, QWORD PTR [rdi+512]
	mov r9, QWORD PTR [rdi+520]
	mov r10, QWORD PTR [rdi+528]
	mov r11, QWORD PTR [rdi+536]
	sub r8, QWORD PTR [rdi+800]
	sbb r9, QWORD PTR [rdi+808]
	sbb r10, QWORD PTR [rdi+816]
	sbb r11, QWORD PTR [rdi+824]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+896], r8
	mov QWORD PTR [rdi+904], r9
	mov QWORD PTR [rdi+912], r10
	mov QWORD PTR [rdi+920], r11
	mov r8, QWORD PTR [rdi+512]
	mov r9, QWORD PTR [rdi+520]
	mov r10, QWORD PTR [rdi+528]
	mov r11, QWORD PTR [rdi+536]
	mov r12d, 0
	add r8, QWORD PTR [rdi+800]
	adc r9, QWORD PTR [rdi+808]
	adc r10, QWORD PTR [rdi+816]
	adc r11, QWORD PTR [rdi+824]
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+928], r8
	mov QWORD PTR [rdi+936], r9
	mov QWORD PTR [rdi+944], r10
	mov QWORD PTR [rdi+952], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+896]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+928]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+936]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+944]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+952]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+904]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+928]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+936]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+944]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+952]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+912]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+928]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+936]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+944]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+952]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+920]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+928]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+936]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+944]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+952]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+896], r12
	mov QWORD PTR [rdi+904], r13
	mov QWORD PTR [rdi+912], r8
	mov QWORD PTR [rdi+920], r9
	mov r8, QWORD PTR [rdi+896]
	mov r9, QWORD PTR [rdi+904]
	mov r10, QWORD PTR [rdi+912]
	mov r11, QWORD PTR [rdi+920]
	mov r12d, 0
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+928], r8
	mov QWORD PTR [rdi+936], r9
	mov QWORD PTR [rdi+944], r10
	mov QWORD PTR [rdi+952], r11
	mov r8, QWORD PTR [rdi+928]
	mov r9, QWORD PTR [rdi+936]
	mov r10, QWORD PTR [rdi+944]
	mov r11, QWORD PTR [rdi+952]
	mov r12d, 0
	add r8, QWORD PTR [rdi+896]
	adc r9, QWORD PTR [rdi+904]
	adc r10, QWORD PTR [rdi+912]
	adc r11, QWORD PTR [rdi+920]
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+896], r8
	mov QWORD PTR [rdi+904], r9
	mov QWORD PTR [rdi+912], r10
	mov QWORD PTR [rdi+920], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+512]
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
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+520]
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
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+528]
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
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+536]
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
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
	mov QWORD PTR [rdi+880], r8
	mov QWORD PTR [rdi+888], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+832]
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
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+840]
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
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+848]
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
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+856]
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
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+832], r12
	mov QWORD PTR [rdi+840], r13
	mov QWORD PTR [rdi+848], r8
	mov QWORD PTR [rdi+856], r9
	mov r8, QWORD PTR [rdi+832]
	mov r9, QWORD PTR [rdi+840]
	mov r10, QWORD PTR [rdi+848]
	mov r11, QWORD PTR [rdi+856]
	mov rax, r8
	and rax, 1
	mov ecx, 0
	sub rcx, rax
	mov rdx, rcx
	shr rdx, 32
	movabs rbp, -4294967295
	and rbp, rcx
	mov r12d, 0
	add r8, rcx
	adc r9, rdx
	adc r10, 0
	adc r11, rbp
	adc r12, 0
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
	mov QWORD PTR [rdi+832], r8
	mov QWORD PTR [rdi+840], r9
	mov QWORD PTR [rdi+848], r10
	mov QWORD PTR [rdi+856], r11
	mov r8, QWORD PTR [rdi+864]
	mov r9, QWORD PTR [rdi+872]
	mov r10, QWORD PTR [rdi+880]
	mov r11, QWORD PTR [rdi+888]
	mov r12d, 0
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+928], r8
	mov QWORD PTR [rdi+936], r9
	mov QWORD PTR [rdi+944], r10
	mov QWORD PTR [rdi+952], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+896]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+904]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+912]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+920]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+512], r12
	mov QWORD PTR [rdi+520], r13
	mov QWORD PTR [rdi+528], r8
	mov QWORD PTR [rdi+536], r9
	mov r8, QWORD PTR [rdi+512]
	mov r9, QWORD PTR [rdi+520]
	mov r10, QWORD PTR [rdi+528]
	mov r11, QWORD PTR [rdi+536]
	sub r8, QWORD PTR [rdi+928]
	sbb r9, QWORD PTR [rdi+936]
	sbb r10, QWORD PTR [rdi+944]
	sbb r11, QWORD PTR [rdi+952]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+512], r8
	mov QWORD PTR [rdi+520], r9
	mov QWORD PTR [rdi+528], r10
	mov QWORD PTR [rdi+536], r11
	mov r8, QWORD PTR [rdi+864]
	mov r9, QWORD PTR [rdi+872]
	mov r10, QWORD PTR [rdi+880]
	mov r11, QWORD PTR [rdi+888]
	sub r8, QWORD PTR [rdi+512]
	sbb r9, QWORD PTR [rdi+520]
	sbb r10, QWORD PTR [rdi+528]
	sbb r11, QWORD PTR [rdi+536]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+544], r8
	mov QWORD PTR [rdi+552], r9
	mov QWORD PTR [rdi+560], r10
	mov QWORD PTR [rdi+568], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+896]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+904]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+912]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+920]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+544], r12
	mov QWORD PTR [rdi+552], r13
	mov QWORD PTR [rdi+560], r8
	mov QWORD PTR [rdi+568], r9
	mov r8, QWORD PTR [rdi+544]
	mov r9, QWORD PTR [rdi+552]
	mov r10, QWORD PTR [rdi+560]
	mov r11, QWORD PTR [rdi+568]
	sub r8, QWORD PTR [rdi+832]
	sbb r9, QWORD PTR [rdi+840]
	sbb r10, QWORD PTR [rdi+848]
	sbb r11, QWORD PTR [rdi+856]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+544], r8
	mov QWORD PTR [rdi+552], r9
	mov QWORD PTR [rdi+560], r10
	mov QWORD PTR [rdi+568], r11
	sub rbx, 4096
	cmp rbx, 4096
	jae 27b
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+576]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+584]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+592]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+600]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+800], r12
	mov QWORD PTR [rdi+808], r13
	mov QWORD PTR [rdi+816], r8
	mov QWORD PTR [rdi+824], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+512]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+5408]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5416]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5424]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5432]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+520]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+5408]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5416]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5424]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5432]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+528]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+5408]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5416]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5424]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5432]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+536]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+5408]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5416]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5424]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5432]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
	mov QWORD PTR [rdi+880], r8
	mov QWORD PTR [rdi+888], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+5312]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+800]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+808]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+5320]
	mov ebp, 0
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
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+5328]
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
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+5336]
	mov ebp, 0
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
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+896], r12
	mov QWORD PTR [rdi+904], r13
	mov QWORD PTR [rdi+912], r8
	mov QWORD PTR [rdi+920], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+544]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+5440]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5448]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5456]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5464]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+552]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+5440]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5448]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5456]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5464]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+560]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+5440]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5448]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5456]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5464]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+568]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+5440]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5448]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5456]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5464]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+928], r12
	mov QWORD PTR [rdi+936], r13
	mov QWORD PTR [rdi+944], r8
	mov QWORD PTR [rdi+952], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+5344]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+5352]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+5360]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+5368]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+960], r12
	mov QWORD PTR [rdi+968], r13
	mov QWORD PTR [rdi+976], r8
	mov QWORD PTR [rdi+984], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+960]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+800]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+808]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+968]
	mov ebp, 0
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
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+976]
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
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+984]
	mov ebp, 0
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
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+960], r12
	mov QWORD PTR [rdi+968], r13
	mov QWORD PTR [rdi+976], r8
	mov QWORD PTR [rdi+984], r9
	mov r8, QWORD PTR [rdi+896]
	mov r9, QWORD PTR [rdi+904]
	mov r10, QWORD PTR [rdi+912]
	mov r11, QWORD PTR [rdi+920]
	sub r8, QWORD PTR [rdi+864]
	sbb r9, QWORD PTR [rdi+872]
	sbb r10, QWORD PTR [rdi+880]
	sbb r11, QWORD PTR [rdi+888]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+896], r8
	mov QWORD PTR [rdi+904], r9
	mov QWORD PTR [rdi+912], r10
	mov QWORD PTR [rdi+920], r11
	mov r8, QWORD PTR [rdi+960]
	mov r9, QWORD PTR [rdi+968]
	mov r10, QWORD PTR [rdi+976]
	mov r11, QWORD PTR [rdi+984]
	sub r8, QWORD PTR [rdi+928]
	sbb r9, QWORD PTR [rdi+936]
	sbb r10, QWORD PTR [rdi+944]
	sbb r11, QWORD PTR [rdi+952]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+960], r8
	mov QWORD PTR [rdi+968], r9
	mov QWORD PTR [rdi+976], r10
	mov QWORD PTR [rdi+984], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+896]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+904]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+912]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+920]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+800], r12
	mov QWORD PTR [rdi+808], r13
	mov QWORD PTR [rdi+816], r8
	mov QWORD PTR [rdi+824], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+800]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+808]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+816]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+824]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+832], r12
	mov QWORD PTR [rdi+840], r13
	mov QWORD PTR [rdi+848], r8
	mov QWORD PTR [rdi+856], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+864]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+800]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+808]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+816]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+824]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+872]
	mov ebp, 0
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
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+880]
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
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+888]
	mov ebp, 0
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
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
	mov QWORD PTR [rdi+880], r8
	mov QWORD PTR [rdi+888], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+960]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+960]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+968]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+968]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+960]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+968]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+976]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+960]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+968]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+984]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+960]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+968]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+976]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+984]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+512], r12
	mov QWORD PTR [rdi+520], r13
	mov QWORD PTR [rdi+528], r8
	mov QWORD PTR [rdi+536], r9
	mov r8, QWORD PTR [rdi+512]
	mov r9, QWORD PTR [rdi+520]
	mov r10, QWORD PTR [rdi+528]
	mov r11, QWORD PTR [rdi+536]
	sub r8, QWORD PTR [rdi+832]
	sbb r9, QWORD PTR [rdi+840]
	sbb r10, QWORD PTR [rdi+848]
	sbb r11, QWORD PTR [rdi+856]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+512], r8
	mov QWORD PTR [rdi+520], r9
	mov QWORD PTR [rdi+528], r10
	mov QWORD PTR [rdi+536], r11
	mov r8, QWORD PTR [rdi+512]
	mov r9, QWORD PTR [rdi+520]
	mov r10, QWORD PTR [rdi+528]
	mov r11, QWORD PTR [rdi+536]
	sub r8, QWORD PTR [rdi+864]
	sbb r9, QWORD PTR [rdi+872]
	sbb r10, QWORD PTR [rdi+880]
	sbb r11, QWORD PTR [rdi+888]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+512], r8
	mov QWORD PTR [rdi+520], r9
	mov QWORD PTR [rdi+528], r10
	mov QWORD PTR [rdi+536], r11
	mov r8, QWORD PTR [rdi+512]
	mov r9, QWORD PTR [rdi+520]
	mov r10, QWORD PTR [rdi+528]
	mov r11, QWORD PTR [rdi+536]
	sub r8, QWORD PTR [rdi+864]
	sbb r9, QWORD PTR [rdi+872]
	sbb r10, QWORD PTR [rdi+880]
	sbb r11, QWORD PTR [rdi+888]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+512], r8
	mov QWORD PTR [rdi+520], r9
	mov QWORD PTR [rdi+528], r10
	mov QWORD PTR [rdi+536], r11
	mov r8, QWORD PTR [rdi+864]
	mov r9, QWORD PTR [rdi+872]
	mov r10, QWORD PTR [rdi+880]
	mov r11, QWORD PTR [rdi+888]
	sub r8, QWORD PTR [rdi+512]
	sbb r9, QWORD PTR [rdi+520]
	sbb r10, QWORD PTR [rdi+528]
	sbb r11, QWORD PTR [rdi+536]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+544], r8
	mov QWORD PTR [rdi+552], r9
	mov QWORD PTR [rdi+560], r10
	mov QWORD PTR [rdi+568], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+960]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+968]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+976]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+984]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+544]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+552]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+560]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+568]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+544], r12
	mov QWORD PTR [rdi+552], r13
	mov QWORD PTR [rdi+560], r8
	mov QWORD PTR [rdi+568], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+928]
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
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+936]
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
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+944]
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
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+952]
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
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+928], r12
	mov QWORD PTR [rdi+936], r13
	mov QWORD PTR [rdi+944], r8
	mov QWORD PTR [rdi+952], r9
	mov r8, QWORD PTR [rdi+544]
	mov r9, QWORD PTR [rdi+552]
	mov r10, QWORD PTR [rdi+560]
	mov r11, QWORD PTR [rdi+568]
	sub r8, QWORD PTR [rdi+928]
	sbb r9, QWORD PTR [rdi+936]
	sbb r10, QWORD PTR [rdi+944]
	sbb r11, QWORD PTR [rdi+952]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+544], r8
	mov QWORD PTR [rdi+552], r9
	mov QWORD PTR [rdi+560], r10
	mov QWORD PTR [rdi+568], r11
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+576]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+5376]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5384]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5392]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5400]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+584]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+5376]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5384]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5392]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5400]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+592]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+5376]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5384]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5392]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5400]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+600]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+5376]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5384]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5392]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+5400]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+576], r12
	mov QWORD PTR [rdi+584], r13
	mov QWORD PTR [rdi+592], r8
	mov QWORD PTR [rdi+600], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+576]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+584]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+592]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+600]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+896]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+904]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+912]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+920]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+576], r12
	mov QWORD PTR [rdi+584], r13
	mov QWORD PTR [rdi+592], r8
	mov QWORD PTR [rdi+600], r9
	mov rax, QWORD PTR [rdi+576]
	or rax, QWORD PTR [rdi+584]
	or rax, QWORD PTR [rdi+592]
	or rax, QWORD PTR [rdi+600]
	mov ecx, 0
	sub rcx, rax
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+160]
	mov rdx, QWORD PTR [rdi+544]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rdi+168]
	mov rdx, QWORD PTR [rdi+552]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rdi+176]
	mov rdx, QWORD PTR [rdi+560]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rdi+184]
	mov rdx, QWORD PTR [rdi+568]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+568], rax
	xor rcx, -1
	movabs rax, 1
	and rax, rcx
	or rax, QWORD PTR [rdi+544]
	mov QWORD PTR [rdi+544], rax
	movabs rax, -4294967296
	and rax, rcx
	or rax, QWORD PTR [rdi+552]
	mov QWORD PTR [rdi+552], rax
	movabs rax, -1
	and rax, rcx
	or rax, QWORD PTR [rdi+560]
	mov QWORD PTR [rdi+560], rax
	movabs rax, 4294967294
	and rax, rcx
	or rax, QWORD PTR [rdi+568]
	mov QWORD PTR [rdi+568], rax
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+512]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+520]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+528]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+536]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+512], r12
	mov QWORD PTR [rdi+520], r13
	mov QWORD PTR [rdi+528], r8
	mov QWORD PTR [rdi+536], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+576]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+584]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+592]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+600]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+800], r12
	mov QWORD PTR [rdi+808], r13
	mov QWORD PTR [rdi+816], r8
	mov QWORD PTR [rdi+824], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+800]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+808]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+816]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+824]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+576]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+584]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+592]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+600]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+576], r12
	mov QWORD PTR [rdi+584], r13
	mov QWORD PTR [rdi+592], r8
	mov QWORD PTR [rdi+600], r9
	mov r8, QWORD PTR [rdi+160]
	mov r9, QWORD PTR [rdi+168]
	mov r10, QWORD PTR [rdi+176]
	mov r11, QWORD PTR [rdi+184]
	sub r8, QWORD PTR [rdi+544]
	sbb r9, QWORD PTR [rdi+552]
	sbb r10, QWORD PTR [rdi+560]
	sbb r11, QWORD PTR [rdi+568]
	sbb rax, rax
	mov rdx, QWORD PTR [rdi+64]
	and rdx, rax
	mov QWORD PTR [rdi+128], rdx
	mov rdx, QWORD PTR [rdi+72]
	and rdx, rax
	mov QWORD PTR [rdi+136], rdx
	mov rdx, QWORD PTR [rdi+80]
	and rdx, rax
	mov QWORD PTR [rdi+144], rdx
	mov rdx, QWORD PTR [rdi+88]
	and rdx, rax
	mov QWORD PTR [rdi+152], rdx
	add r8, QWORD PTR [rdi+128]
	adc r9, QWORD PTR [rdi+136]
	adc r10, QWORD PTR [rdi+144]
	adc r11, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+1024], r8
	mov QWORD PTR [rdi+1032], r9
	mov QWORD PTR [rdi+1040], r10
	mov QWORD PTR [rdi+1048], r11
	movzx ecx, BYTE PTR [rdi+1504]
	sub rcx, 1
	mov rax, QWORD PTR [rdi+544]
	mov rdx, QWORD PTR [rdi+1024]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rdi+552]
	mov rdx, QWORD PTR [rdi+1032]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rdi+560]
	mov rdx, QWORD PTR [rdi+1040]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rdi+568]
	mov rdx, QWORD PTR [rdi+1048]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+568], rax
	call {vg_p256_inv_mod_p}
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+512]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+520]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+528]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+536]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+992]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1000]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1008]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1016]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+1152], r12
	mov QWORD PTR [rdi+1160], r13
	mov QWORD PTR [rdi+1168], r8
	mov QWORD PTR [rdi+1176], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+1152]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	add r12, rbp
	adc r13, 0
	mov rax, r8
	shl rax, 32
	mov rdx, r8
	shr rdx, 32
	mov rcx, r8
	sub rcx, rax
	mov rbp, r8
	sbb rbp, rdx
	add r9, rax
	adc r10, rdx
	adc r11, rcx
	adc r12, rbp
	adc r13, 0
	mov r8d, 0
	mov rcx, QWORD PTR [rdi+1160]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	add r13, rbp
	adc r8, 0
	mov rax, r9
	shl rax, 32
	mov rdx, r9
	shr rdx, 32
	mov rcx, r9
	sub rcx, rax
	mov rbp, r9
	sbb rbp, rdx
	add r10, rax
	adc r11, rdx
	adc r12, rcx
	adc r13, rbp
	adc r8, 0
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1168]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	add r8, rbp
	adc r9, 0
	mov rax, r10
	shl rax, 32
	mov rdx, r10
	shr rdx, 32
	mov rcx, r10
	sub rcx, rax
	mov rbp, r10
	sbb rbp, rdx
	add r11, rax
	adc r12, rdx
	adc r13, rcx
	adc r8, rbp
	adc r9, 0
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1176]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+192]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+200]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+208]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+216]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	add r9, rbp
	adc r10, 0
	mov rax, r11
	shl rax, 32
	mov rdx, r11
	shr rdx, 32
	mov rcx, r11
	sub rcx, rax
	mov rbp, r11
	sbb rbp, rdx
	add r12, rax
	adc r13, rdx
	adc r8, rcx
	adc r9, rbp
	adc r10, 0
	mov r11d, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r8
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r9
	sbb rbp, QWORD PTR [rdi+88]
	sbb r10, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r8, rdx
	cmovae r9, rbp
	mov QWORD PTR [rdi+1184], r12
	mov QWORD PTR [rdi+1192], r13
	mov QWORD PTR [rdi+1200], r8
	mov QWORD PTR [rdi+1208], r9
	mov rdx, QWORD PTR [rdi+1088]
	sub rdx, QWORD PTR [rdi+96]
	mov rdx, QWORD PTR [rdi+1096]
	sbb rdx, QWORD PTR [rdi+104]
	mov rdx, QWORD PTR [rdi+1104]
	sbb rdx, QWORD PTR [rdi+112]
	mov rdx, QWORD PTR [rdi+1112]
	sbb rdx, QWORD PTR [rdi+120]
	sbb rax, rax
	mov rbp, rax
	mov rdx, QWORD PTR [rdi+1088]
	or rdx, QWORD PTR [rdi+1096]
	or rdx, QWORD PTR [rdi+1104]
	or rdx, QWORD PTR [rdi+1112]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	and rdx, rbp
	mov rax, QWORD PTR [rdi+1472]
	and rax, rdx
	mov QWORD PTR [rdi+1472], rax
	mov rdx, QWORD PTR [rdi+576]
	or rdx, QWORD PTR [rdi+584]
	or rdx, QWORD PTR [rdi+592]
	or rdx, QWORD PTR [rdi+600]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+1472]
	and rax, rdx
	mov QWORD PTR [rdi+1472], rax
	mov rcx, QWORD PTR [rdi+1472]
	mov rax, QWORD PTR [rdi+1184]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+24], rax
	mov rax, QWORD PTR [rdi+1192]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+16], rax
	mov rax, QWORD PTR [rdi+1200]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+8], rax
	mov rax, QWORD PTR [rdi+1208]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi], rax
	mov rax, rcx
	and rax, 1
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
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
	lea rsp, [rsp-8]
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

vg_ecdh_p256_adx:
	mov r8, rcx
	mov r9, rdx
	mov rcx, rsi
	add rdx, 1
	mov QWORD PTR [r8], rbx
	mov QWORD PTR [r8+8], rbp
	mov QWORD PTR [r8+16], r12
	mov QWORD PTR [r8+24], r13
	mov QWORD PTR [r8+32], r14
	mov QWORD PTR [r8+40], r15
	mov r14, rdi
	mov rdi, r8
	mov rax, QWORD PTR [rcx+24]
	bswap rax
	mov QWORD PTR [rdi+1056], rax
	mov rax, QWORD PTR [rcx+16]
	bswap rax
	mov QWORD PTR [rdi+1064], rax
	mov rax, QWORD PTR [rcx+8]
	bswap rax
	mov QWORD PTR [rdi+1072], rax
	mov rax, QWORD PTR [rcx]
	bswap rax
	mov QWORD PTR [rdi+1080], rax
	mov rax, QWORD PTR [rsi+24]
	bswap rax
	mov QWORD PTR [rdi+1088], rax
	mov rax, QWORD PTR [rsi+16]
	bswap rax
	mov QWORD PTR [rdi+1096], rax
	mov rax, QWORD PTR [rsi+8]
	bswap rax
	mov QWORD PTR [rdi+1104], rax
	mov rax, QWORD PTR [rsi]
	bswap rax
	mov QWORD PTR [rdi+1112], rax
	mov rax, QWORD PTR [rdx+24]
	bswap rax
	mov QWORD PTR [rdi+1120], rax
	mov rax, QWORD PTR [rdx+16]
	bswap rax
	mov QWORD PTR [rdi+1128], rax
	mov rax, QWORD PTR [rdx+8]
	bswap rax
	mov QWORD PTR [rdi+1136], rax
	mov rax, QWORD PTR [rdx]
	bswap rax
	mov QWORD PTR [rdi+1144], rax
	movabs rax, -1
	mov QWORD PTR [rdi+64], rax
	movabs rax, 4294967295
	mov QWORD PTR [rdi+72], rax
	movabs rax, 0
	mov QWORD PTR [rdi+80], rax
	movabs rax, -4294967295
	mov QWORD PTR [rdi+88], rax
	movabs rax, -884452912994769583
	mov QWORD PTR [rdi+96], rax
	movabs rax, -4834901526196019580
	mov QWORD PTR [rdi+104], rax
	movabs rax, -1
	mov QWORD PTR [rdi+112], rax
	movabs rax, -4294967296
	mov QWORD PTR [rdi+120], rax
	movabs rax, 0
	mov QWORD PTR [rdi+160], rax
	movabs rax, 0
	mov QWORD PTR [rdi+168], rax
	movabs rax, 0
	mov QWORD PTR [rdi+176], rax
	movabs rax, 0
	mov QWORD PTR [rdi+184], rax
	movabs rax, 1
	mov QWORD PTR [rdi+192], rax
	movabs rax, 0
	mov QWORD PTR [rdi+200], rax
	movabs rax, 0
	mov QWORD PTR [rdi+208], rax
	movabs rax, 0
	mov QWORD PTR [rdi+216], rax
	movabs rax, 1
	mov QWORD PTR [rdi+224], rax
	movabs rax, -4294967296
	mov QWORD PTR [rdi+232], rax
	movabs rax, -1
	mov QWORD PTR [rdi+240], rax
	movabs rax, 4294967294
	mov QWORD PTR [rdi+248], rax
	movabs rax, -4
	mov QWORD PTR [rdi+256], rax
	movabs rax, 17179869183
	mov QWORD PTR [rdi+264], rax
	movabs rax, 0
	mov QWORD PTR [rdi+272], rax
	movabs rax, -17179869180
	mov QWORD PTR [rdi+280], rax
	movabs rax, -8514444157349119585
	mov QWORD PTR [rdi+288], rax
	movabs rax, 490911490938540466
	mov QWORD PTR [rdi+296], rax
	movabs rax, -5699760509517853564
	mov QWORD PTR [rdi+304], rax
	movabs rax, -7741667585760569188
	mov QWORD PTR [rdi+312], rax
	movabs rax, 8784043285714375740
	mov QWORD PTR [rdi+320], rax
	movabs rax, 8483257759279461889
	mov QWORD PTR [rdi+328], rax
	movabs rax, 8789745728267363600
	mov QWORD PTR [rdi+336], rax
	movabs rax, 1770019616739251654
	mov QWORD PTR [rdi+344], rax
	movabs rax, -2453807210370345462
	mov QWORD PTR [rdi+352], rax
	movabs rax, -8409706061646666660
	mov QWORD PTR [rdi+360], rax
	movabs rax, -3249199208764148955
	mov QWORD PTR [rdi+368], rax
	movabs rax, -8830996915122840187
	mov QWORD PTR [rdi+376], rax
	movabs rax, -8996981949549908318
	mov QWORD PTR [rdi+384], rax
	movabs rax, 5087230966250696614
	mov QWORD PTR [rdi+392], rax
	movabs rax, 2901921493521525849
	mov QWORD PTR [rdi+400], rax
	movabs rax, 7413256579398063648
	mov QWORD PTR [rdi+408], rax
	movabs rax, 884452912994769583
	mov QWORD PTR [rdi+416], rax
	movabs rax, 4834901526196019579
	mov QWORD PTR [rdi+424], rax
	movabs rax, 0
	mov QWORD PTR [rdi+432], rax
	movabs rax, 4294967295
	mov QWORD PTR [rdi+440], rax
	movabs rax, -3
	mov QWORD PTR [rdi+448], rax
	movabs rax, 4294967295
	mov QWORD PTR [rdi+456], rax
	movabs rax, 0
	mov QWORD PTR [rdi+464], rax
	movabs rax, -4294967295
	mov QWORD PTR [rdi+472], rax
	movabs rax, -884452912994769585
	mov QWORD PTR [rdi+480], rax
	movabs rax, -4834901526196019580
	mov QWORD PTR [rdi+488], rax
	movabs rax, -1
	mov QWORD PTR [rdi+496], rax
	movabs rax, -4294967296
	mov QWORD PTR [rdi+504], rax
	movabs rax, 0
	mov QWORD PTR [rdi+512], rax
	movabs rax, 0
	mov QWORD PTR [rdi+520], rax
	movabs rax, 0
	mov QWORD PTR [rdi+528], rax
	movabs rax, 0
	mov QWORD PTR [rdi+536], rax
	movabs rax, 1
	mov QWORD PTR [rdi+544], rax
	movabs rax, -4294967296
	mov QWORD PTR [rdi+552], rax
	movabs rax, -1
	mov QWORD PTR [rdi+560], rax
	movabs rax, 4294967294
	mov QWORD PTR [rdi+568], rax
	movabs rax, 0
	mov QWORD PTR [rdi+576], rax
	movabs rax, 0
	mov QWORD PTR [rdi+584], rax
	movabs rax, 0
	mov QWORD PTR [rdi+592], rax
	movabs rax, 0
	mov QWORD PTR [rdi+600], rax
	movabs rax, -1
	mov QWORD PTR [rdi+1472], rax
	mov rsi, r14
	mov ebx, 0
20:
	movzx eax, BYTE PTR [rdi+rbx*1+1056]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1504], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1505], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1506], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1507], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1508], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1509], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1510], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1511], dl
	add rbx, 1
	cmp rbx, 32
	jne 20b
	mov ebx, 0
21:
	movzx eax, BYTE PTR [rdi+rbx*1+448]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1768], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1769], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1770], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1771], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1772], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1773], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1774], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+1775], dl
	add rbx, 1
	cmp rbx, 32
	jne 21b
	mov ebx, 0
22:
	movzx eax, BYTE PTR [rdi+rbx*1+480]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2032], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2033], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2034], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2035], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2036], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2037], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2038], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2039], dl
	add rbx, 1
	cmp rbx, 32
	jne 22b
	movabs rax, 3
	mov QWORD PTR [rdi+1312], rax
	movabs rax, -17179869185
	mov QWORD PTR [rdi+1320], rax
	movabs rax, -2
	mov QWORD PTR [rdi+1328], rax
	movabs rax, 21474836477
	mov QWORD PTR [rdi+1336], rax
	movabs rax, -2838148052449706529
	mov QWORD PTR [rdi+1344], rax
	movabs rax, -5985277524727025520
	mov QWORD PTR [rdi+1352], rax
	movabs rax, -1899920169839284522
	mov QWORD PTR [rdi+1360], rax
	movabs rax, -2580555864783501260
	mov QWORD PTR [rdi+1368], rax
	mov rdx, r9
	add rdx, 33
	mov rax, QWORD PTR [rdx+24]
	bswap rax
	mov QWORD PTR [rdi+1216], rax
	mov rax, QWORD PTR [rdx+16]
	bswap rax
	mov QWORD PTR [rdi+1224], rax
	mov rax, QWORD PTR [rdx+8]
	bswap rax
	mov QWORD PTR [rdi+1232], rax
	mov rax, QWORD PTR [rdx]
	bswap rax
	mov QWORD PTR [rdi+1240], rax
	movzx edx, BYTE PTR [r9]
	xor rdx, 4
	cmp rdx, 1
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+1472]
	and rax, rdx
	mov QWORD PTR [rdi+1472], rax
	call {vg_p256_check_point_adx}
	movabs rax, -884452912994769583
	mov QWORD PTR [rdi+2336], rax
	movabs rax, -4834901526196019580
	mov QWORD PTR [rdi+2344], rax
	movabs rax, -1
	mov QWORD PTR [rdi+2352], rax
	movabs rax, -4294967296
	mov QWORD PTR [rdi+2360], rax
	mov r8, QWORD PTR [rdi+2336]
	sub r8, QWORD PTR [rdi+1056]
	mov QWORD PTR [rdi+2336], r8
	mov r8, QWORD PTR [rdi+2344]
	sbb r8, QWORD PTR [rdi+1064]
	mov QWORD PTR [rdi+2344], r8
	mov r8, QWORD PTR [rdi+2352]
	sbb r8, QWORD PTR [rdi+1072]
	mov QWORD PTR [rdi+2352], r8
	mov r8, QWORD PTR [rdi+2360]
	sbb r8, QWORD PTR [rdi+1080]
	mov QWORD PTR [rdi+2360], r8
	mov rcx, QWORD PTR [rdi+1056]
	and rcx, 1
	sub rcx, 1
	mov rax, QWORD PTR [rdi+1056]
	mov rdx, QWORD PTR [rdi+2336]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1056], rax
	mov rax, QWORD PTR [rdi+1064]
	mov rdx, QWORD PTR [rdi+2344]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1064], rax
	mov rax, QWORD PTR [rdi+1072]
	mov rdx, QWORD PTR [rdi+2352]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1072], rax
	mov rax, QWORD PTR [rdi+1080]
	mov rdx, QWORD PTR [rdi+2360]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1080], rax
	movabs rax, -1
	mov QWORD PTR [rdi+2336], rax
	movabs rax, -1
	mov QWORD PTR [rdi+2344], rax
	movabs rax, -1
	mov QWORD PTR [rdi+2352], rax
	movabs rax, -1
	mov QWORD PTR [rdi+2360], rax
	movabs rax, 15
	mov QWORD PTR [rdi+2368], rax
	mov r8, QWORD PTR [rdi+2336]
	add r8, QWORD PTR [rdi+1056]
	mov QWORD PTR [rdi+2336], r8
	mov r8, QWORD PTR [rdi+2344]
	adc r8, QWORD PTR [rdi+1064]
	mov QWORD PTR [rdi+2344], r8
	mov r8, QWORD PTR [rdi+2352]
	adc r8, QWORD PTR [rdi+1072]
	mov QWORD PTR [rdi+2352], r8
	mov r8, QWORD PTR [rdi+2360]
	adc r8, QWORD PTR [rdi+1080]
	mov QWORD PTR [rdi+2360], r8
	mov r8, QWORD PTR [rdi+2368]
	adc r8, 0
	mov QWORD PTR [rdi+2368], r8
	mov ebx, 0
23:
	movzx eax, BYTE PTR [rdi+rbx*1+2336]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2400], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2401], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2402], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2403], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2404], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2405], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2406], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+2407], dl
	add rbx, 1
	cmp rbx, 40
	jne 23b
	mov rax, QWORD PTR [rdi+1280]
	mov QWORD PTR [rdi+5312], rax
	mov rax, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+5320], rax
	mov rax, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+5328], rax
	mov rax, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+5336], rax
	mov rax, QWORD PTR [rdi+1440]
	mov QWORD PTR [rdi+5344], rax
	mov rax, QWORD PTR [rdi+1448]
	mov QWORD PTR [rdi+5352], rax
	mov rax, QWORD PTR [rdi+1456]
	mov QWORD PTR [rdi+5360], rax
	mov rax, QWORD PTR [rdi+1464]
	mov QWORD PTR [rdi+5368], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+5376], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+5384], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+5392], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+5400], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+5408], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+5416], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+5424], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+5432], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+5440], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+5448], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+5456], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+5464], rax
	mov ebx, 1
	mov rax, rbx
	sub rax, 1
	mov ecx, 160
	mul rcx
	mov rdx, rdi
	add rdx, 2752
	add rdx, rax
	mov rax, QWORD PTR [rdi+5312]
	mov QWORD PTR [rdx], rax
	mov rax, QWORD PTR [rdi+5320]
	mov QWORD PTR [rdx+8], rax
	mov rax, QWORD PTR [rdi+5328]
	mov QWORD PTR [rdx+16], rax
	mov rax, QWORD PTR [rdi+5336]
	mov QWORD PTR [rdx+24], rax
	mov rax, QWORD PTR [rdi+5344]
	mov QWORD PTR [rdx+32], rax
	mov rax, QWORD PTR [rdi+5352]
	mov QWORD PTR [rdx+40], rax
	mov rax, QWORD PTR [rdi+5360]
	mov QWORD PTR [rdx+48], rax
	mov rax, QWORD PTR [rdi+5368]
	mov QWORD PTR [rdx+56], rax
	mov rax, QWORD PTR [rdi+5376]
	mov QWORD PTR [rdx+64], rax
	mov rax, QWORD PTR [rdi+5384]
	mov QWORD PTR [rdx+72], rax
	mov rax, QWORD PTR [rdi+5392]
	mov QWORD PTR [rdx+80], rax
	mov rax, QWORD PTR [rdi+5400]
	mov QWORD PTR [rdx+88], rax
	mov rax, QWORD PTR [rdi+5408]
	mov QWORD PTR [rdx+96], rax
	mov rax, QWORD PTR [rdi+5416]
	mov QWORD PTR [rdx+104], rax
	mov rax, QWORD PTR [rdi+5424]
	mov QWORD PTR [rdx+112], rax
	mov rax, QWORD PTR [rdi+5432]
	mov QWORD PTR [rdx+120], rax
	mov rax, QWORD PTR [rdi+5440]
	mov QWORD PTR [rdx+128], rax
	mov rax, QWORD PTR [rdi+5448]
	mov QWORD PTR [rdx+136], rax
	mov rax, QWORD PTR [rdi+5456]
	mov QWORD PTR [rdx+144], rax
	mov rax, QWORD PTR [rdi+5464]
	mov QWORD PTR [rdx+152], rax
	mov rdx, QWORD PTR [rdi+1280]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+1288]
	mulx r11, rax, QWORD PTR [rdi+1296]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1304]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+1288]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1296]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+1304]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+1296]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+1304]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+1280]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+1288]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+1296]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+1304]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+800], r12
	mov QWORD PTR [rdi+808], r13
	mov QWORD PTR [rdi+816], r14
	mov QWORD PTR [rdi+824], r15
	mov rdx, QWORD PTR [rdi+1440]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+1448]
	mulx r11, rax, QWORD PTR [rdi+1456]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1464]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+1448]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1456]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+1464]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+1456]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+1464]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+1440]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+1448]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+1456]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+1464]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+832], r12
	mov QWORD PTR [rdi+840], r13
	mov QWORD PTR [rdi+848], r14
	mov QWORD PTR [rdi+856], r15
	mov rdx, r12
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+840]
	mulx r11, rax, QWORD PTR [rdi+848]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+856]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, r13
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+856]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, r14
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+856]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+832]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+840]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+848]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, r15
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
	mov QWORD PTR [rdi+880], r14
	mov QWORD PTR [rdi+888], r15
	mov rdx, QWORD PTR [rdi+1280]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+832]
	mulx r10, rax, QWORD PTR [rdi+840]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+848]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+856]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+1288]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+856]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+1296]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+856]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+1304]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+856]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+896], r12
	mov QWORD PTR [rdi+904], r13
	mov QWORD PTR [rdi+912], r14
	mov QWORD PTR [rdi+920], r15
	mov r8, r12
	mov r9, r13
	mov r10, r14
	mov r11, r15
	mov r12d, 0
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+896], r8
	mov QWORD PTR [rdi+904], r9
	mov QWORD PTR [rdi+912], r10
	mov QWORD PTR [rdi+920], r11
	mov r8, r8
	mov r9, r9
	mov r10, r10
	mov r11, r11
	mov r12d, 0
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+896], r8
	mov QWORD PTR [rdi+904], r9
	mov QWORD PTR [rdi+912], r10
	mov QWORD PTR [rdi+920], r11
	mov r8, QWORD PTR [rdi+800]
	mov r9, QWORD PTR [rdi+808]
	mov r10, QWORD PTR [rdi+816]
	mov r11, QWORD PTR [rdi+824]
	sub r8, QWORD PTR [rdi+224]
	sbb r9, QWORD PTR [rdi+232]
	sbb r10, QWORD PTR [rdi+240]
	sbb r11, QWORD PTR [rdi+248]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+928], r8
	mov QWORD PTR [rdi+936], r9
	mov QWORD PTR [rdi+944], r10
	mov QWORD PTR [rdi+952], r11
	mov r8, r8
	mov r9, r9
	mov r10, r10
	mov r11, r11
	mov r12d, 0
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+960], r8
	mov QWORD PTR [rdi+968], r9
	mov QWORD PTR [rdi+976], r10
	mov QWORD PTR [rdi+984], r11
	mov r8, r8
	mov r9, r9
	mov r10, r10
	mov r11, r11
	mov r12d, 0
	add r8, QWORD PTR [rdi+928]
	adc r9, QWORD PTR [rdi+936]
	adc r10, QWORD PTR [rdi+944]
	adc r11, QWORD PTR [rdi+952]
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+928], r8
	mov QWORD PTR [rdi+936], r9
	mov QWORD PTR [rdi+944], r10
	mov QWORD PTR [rdi+952], r11
	mov rdx, r8
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+936]
	mulx r11, rax, QWORD PTR [rdi+944]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+952]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+936]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+944]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+952]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+944]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+952]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, r8
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+936]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+944]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+952]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+5312], r12
	mov QWORD PTR [rdi+5320], r13
	mov QWORD PTR [rdi+5328], r14
	mov QWORD PTR [rdi+5336], r15
	mov r8, r12
	mov r9, r13
	mov r10, r14
	mov r11, r15
	sub r8, QWORD PTR [rdi+896]
	sbb r9, QWORD PTR [rdi+904]
	sbb r10, QWORD PTR [rdi+912]
	sbb r11, QWORD PTR [rdi+920]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+5312], r8
	mov QWORD PTR [rdi+5320], r9
	mov QWORD PTR [rdi+5328], r10
	mov QWORD PTR [rdi+5336], r11
	mov r8, r8
	mov r9, r9
	mov r10, r10
	mov r11, r11
	sub r8, QWORD PTR [rdi+896]
	sbb r9, QWORD PTR [rdi+904]
	sbb r10, QWORD PTR [rdi+912]
	sbb r11, QWORD PTR [rdi+920]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+5312], r8
	mov QWORD PTR [rdi+5320], r9
	mov QWORD PTR [rdi+5328], r10
	mov QWORD PTR [rdi+5336], r11
	mov r8, QWORD PTR [rdi+896]
	mov r9, QWORD PTR [rdi+904]
	mov r10, QWORD PTR [rdi+912]
	mov r11, QWORD PTR [rdi+920]
	sub r8, QWORD PTR [rdi+5312]
	sbb r9, QWORD PTR [rdi+5320]
	sbb r10, QWORD PTR [rdi+5328]
	sbb r11, QWORD PTR [rdi+5336]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+960], r8
	mov QWORD PTR [rdi+968], r9
	mov QWORD PTR [rdi+976], r10
	mov QWORD PTR [rdi+984], r11
	mov rdx, QWORD PTR [rdi+928]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+960]
	mulx r10, rax, QWORD PTR [rdi+968]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+976]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+984]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+936]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+960]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+968]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+976]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+984]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+944]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+960]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+968]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+976]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+984]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+952]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+960]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+968]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+976]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+984]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+5344], r12
	mov QWORD PTR [rdi+5352], r13
	mov QWORD PTR [rdi+5360], r14
	mov QWORD PTR [rdi+5368], r15
	mov r8, QWORD PTR [rdi+864]
	mov r9, QWORD PTR [rdi+872]
	mov r10, QWORD PTR [rdi+880]
	mov r11, QWORD PTR [rdi+888]
	mov r12d, 0
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+864], r8
	mov QWORD PTR [rdi+872], r9
	mov QWORD PTR [rdi+880], r10
	mov QWORD PTR [rdi+888], r11
	mov r8, r8
	mov r9, r9
	mov r10, r10
	mov r11, r11
	mov r12d, 0
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+864], r8
	mov QWORD PTR [rdi+872], r9
	mov QWORD PTR [rdi+880], r10
	mov QWORD PTR [rdi+888], r11
	mov r8, r8
	mov r9, r9
	mov r10, r10
	mov r11, r11
	mov r12d, 0
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+864], r8
	mov QWORD PTR [rdi+872], r9
	mov QWORD PTR [rdi+880], r10
	mov QWORD PTR [rdi+888], r11
	mov r8, QWORD PTR [rdi+5344]
	mov r9, QWORD PTR [rdi+5352]
	mov r10, QWORD PTR [rdi+5360]
	mov r11, QWORD PTR [rdi+5368]
	sub r8, QWORD PTR [rdi+864]
	sbb r9, QWORD PTR [rdi+872]
	sbb r10, QWORD PTR [rdi+880]
	sbb r11, QWORD PTR [rdi+888]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+5344], r8
	mov QWORD PTR [rdi+5352], r9
	mov QWORD PTR [rdi+5360], r10
	mov QWORD PTR [rdi+5368], r11
	mov r8, QWORD PTR [rdi+1440]
	mov r9, QWORD PTR [rdi+1448]
	mov r10, QWORD PTR [rdi+1456]
	mov r11, QWORD PTR [rdi+1464]
	mov r12d, 0
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+5376], r8
	mov QWORD PTR [rdi+5384], r9
	mov QWORD PTR [rdi+5392], r10
	mov QWORD PTR [rdi+5400], r11
	mov rdx, r8
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+5384]
	mulx r11, rax, QWORD PTR [rdi+5392]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+5400]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+5384]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5392]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+5400]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+5392]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+5400]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, r8
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+5384]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+5392]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+5400]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+5408], r12
	mov QWORD PTR [rdi+5416], r13
	mov QWORD PTR [rdi+5424], r14
	mov QWORD PTR [rdi+5432], r15
	mov rdx, r12
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+5376]
	mulx r10, rax, QWORD PTR [rdi+5384]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+5392]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+5400]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, r13
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5376]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+5384]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+5392]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+5400]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, r14
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5376]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+5384]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+5392]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+5400]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, r15
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5376]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+5384]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+5392]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+5400]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+5440], r12
	mov QWORD PTR [rdi+5448], r13
	mov QWORD PTR [rdi+5456], r14
	mov QWORD PTR [rdi+5464], r15
	mov rax, QWORD PTR [rdi+5312]
	mov QWORD PTR [rdi+608], rax
	mov rax, QWORD PTR [rdi+5320]
	mov QWORD PTR [rdi+616], rax
	mov rax, QWORD PTR [rdi+5328]
	mov QWORD PTR [rdi+624], rax
	mov rax, QWORD PTR [rdi+5336]
	mov QWORD PTR [rdi+632], rax
	mov rax, QWORD PTR [rdi+5344]
	mov QWORD PTR [rdi+640], rax
	mov rax, QWORD PTR [rdi+5352]
	mov QWORD PTR [rdi+648], rax
	mov rax, QWORD PTR [rdi+5360]
	mov QWORD PTR [rdi+656], rax
	mov rax, QWORD PTR [rdi+5368]
	mov QWORD PTR [rdi+664], rax
	mov rax, QWORD PTR [rdi+896]
	mov QWORD PTR [rdi+5312], rax
	mov rax, QWORD PTR [rdi+904]
	mov QWORD PTR [rdi+5320], rax
	mov rax, QWORD PTR [rdi+912]
	mov QWORD PTR [rdi+5328], rax
	mov rax, QWORD PTR [rdi+920]
	mov QWORD PTR [rdi+5336], rax
	mov rax, QWORD PTR [rdi+864]
	mov QWORD PTR [rdi+5344], rax
	mov rax, QWORD PTR [rdi+872]
	mov QWORD PTR [rdi+5352], rax
	mov rax, QWORD PTR [rdi+880]
	mov QWORD PTR [rdi+5360], rax
	mov rax, QWORD PTR [rdi+888]
	mov QWORD PTR [rdi+5368], rax
24:
	add rbx, 1
	mov r8, QWORD PTR [rdi+608]
	mov r9, QWORD PTR [rdi+616]
	mov r10, QWORD PTR [rdi+624]
	mov r11, QWORD PTR [rdi+632]
	sub r8, QWORD PTR [rdi+5312]
	sbb r9, QWORD PTR [rdi+5320]
	sbb r10, QWORD PTR [rdi+5328]
	sbb r11, QWORD PTR [rdi+5336]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+800], r8
	mov QWORD PTR [rdi+808], r9
	mov QWORD PTR [rdi+816], r10
	mov QWORD PTR [rdi+824], r11
	mov rdx, r8
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+808]
	mulx r11, rax, QWORD PTR [rdi+816]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+824]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+808]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+816]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+824]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+816]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+824]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, r8
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+808]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+816]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+824]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+832], r12
	mov QWORD PTR [rdi+840], r13
	mov QWORD PTR [rdi+848], r14
	mov QWORD PTR [rdi+856], r15
	mov rdx, QWORD PTR [rdi+5376]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+800]
	mulx r10, rax, QWORD PTR [rdi+808]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+816]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+824]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+5384]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+808]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+816]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+824]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+5392]
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
	mov rdx, QWORD PTR [rdi+5400]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r11, rax
	adcx r12, rcx
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
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+5376], r12
	mov QWORD PTR [rdi+5384], r13
	mov QWORD PTR [rdi+5392], r14
	mov QWORD PTR [rdi+5400], r15
	mov rdx, QWORD PTR [rdi+608]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+832]
	mulx r10, rax, QWORD PTR [rdi+840]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+848]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+856]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+616]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+856]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+624]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+856]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+632]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+856]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+608], r12
	mov QWORD PTR [rdi+616], r13
	mov QWORD PTR [rdi+624], r14
	mov QWORD PTR [rdi+632], r15
	mov rdx, QWORD PTR [rdi+5312]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+832]
	mulx r10, rax, QWORD PTR [rdi+840]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+848]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+856]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+5320]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+856]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+5328]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+856]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+5336]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+856]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+896], r12
	mov QWORD PTR [rdi+904], r13
	mov QWORD PTR [rdi+912], r14
	mov QWORD PTR [rdi+920], r15
	mov r8, QWORD PTR [rdi+640]
	mov r9, QWORD PTR [rdi+648]
	mov r10, QWORD PTR [rdi+656]
	mov r11, QWORD PTR [rdi+664]
	sub r8, QWORD PTR [rdi+5344]
	sbb r9, QWORD PTR [rdi+5352]
	sbb r10, QWORD PTR [rdi+5360]
	sbb r11, QWORD PTR [rdi+5368]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+928], r8
	mov QWORD PTR [rdi+936], r9
	mov QWORD PTR [rdi+944], r10
	mov QWORD PTR [rdi+952], r11
	mov rdx, r8
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+936]
	mulx r11, rax, QWORD PTR [rdi+944]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+952]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+936]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+944]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+952]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+944]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+952]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, r8
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+936]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+944]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+952]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+960], r12
	mov QWORD PTR [rdi+968], r13
	mov QWORD PTR [rdi+976], r14
	mov QWORD PTR [rdi+984], r15
	mov r8, QWORD PTR [rdi+608]
	mov r9, QWORD PTR [rdi+616]
	mov r10, QWORD PTR [rdi+624]
	mov r11, QWORD PTR [rdi+632]
	sub r8, QWORD PTR [rdi+896]
	sbb r9, QWORD PTR [rdi+904]
	sbb r10, QWORD PTR [rdi+912]
	sbb r11, QWORD PTR [rdi+920]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+864], r8
	mov QWORD PTR [rdi+872], r9
	mov QWORD PTR [rdi+880], r10
	mov QWORD PTR [rdi+888], r11
	mov rdx, QWORD PTR [rdi+640]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+864]
	mulx r10, rax, QWORD PTR [rdi+872]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+880]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+888]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+648]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+872]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+880]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+888]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+656]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+872]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+880]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+888]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+664]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+864]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+872]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+880]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+888]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+640], r12
	mov QWORD PTR [rdi+648], r13
	mov QWORD PTR [rdi+656], r14
	mov QWORD PTR [rdi+664], r15
	mov r8, QWORD PTR [rdi+960]
	mov r9, QWORD PTR [rdi+968]
	mov r10, QWORD PTR [rdi+976]
	mov r11, QWORD PTR [rdi+984]
	sub r8, QWORD PTR [rdi+608]
	sbb r9, QWORD PTR [rdi+616]
	sbb r10, QWORD PTR [rdi+624]
	sbb r11, QWORD PTR [rdi+632]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+5312], r8
	mov QWORD PTR [rdi+5320], r9
	mov QWORD PTR [rdi+5328], r10
	mov QWORD PTR [rdi+5336], r11
	mov r8, r8
	mov r9, r9
	mov r10, r10
	mov r11, r11
	sub r8, QWORD PTR [rdi+896]
	sbb r9, QWORD PTR [rdi+904]
	sbb r10, QWORD PTR [rdi+912]
	sbb r11, QWORD PTR [rdi+920]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+5312], r8
	mov QWORD PTR [rdi+5320], r9
	mov QWORD PTR [rdi+5328], r10
	mov QWORD PTR [rdi+5336], r11
	mov r8, QWORD PTR [rdi+608]
	mov r9, QWORD PTR [rdi+616]
	mov r10, QWORD PTR [rdi+624]
	mov r11, QWORD PTR [rdi+632]
	sub r8, QWORD PTR [rdi+5312]
	sbb r9, QWORD PTR [rdi+5320]
	sbb r10, QWORD PTR [rdi+5328]
	sbb r11, QWORD PTR [rdi+5336]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+5344], r8
	mov QWORD PTR [rdi+5352], r9
	mov QWORD PTR [rdi+5360], r10
	mov QWORD PTR [rdi+5368], r11
	mov rdx, QWORD PTR [rdi+928]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+5344]
	mulx r10, rax, QWORD PTR [rdi+5352]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+5360]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+5368]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+936]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5344]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+5352]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+5360]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+5368]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+944]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5344]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+5352]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+5360]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+5368]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+952]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5344]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+5352]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+5360]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+5368]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+5344], r12
	mov QWORD PTR [rdi+5352], r13
	mov QWORD PTR [rdi+5360], r14
	mov QWORD PTR [rdi+5368], r15
	mov r8, r12
	mov r9, r13
	mov r10, r14
	mov r11, r15
	sub r8, QWORD PTR [rdi+640]
	sbb r9, QWORD PTR [rdi+648]
	sbb r10, QWORD PTR [rdi+656]
	sbb r11, QWORD PTR [rdi+664]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+5344], r8
	mov QWORD PTR [rdi+5352], r9
	mov QWORD PTR [rdi+5360], r10
	mov QWORD PTR [rdi+5368], r11
	mov rdx, QWORD PTR [rdi+5408]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+832]
	mulx r10, rax, QWORD PTR [rdi+840]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+848]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+856]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+5416]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+856]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+5424]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+856]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+5432]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+856]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+5408], r12
	mov QWORD PTR [rdi+5416], r13
	mov QWORD PTR [rdi+5424], r14
	mov QWORD PTR [rdi+5432], r15
	mov rdx, r12
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+5376]
	mulx r10, rax, QWORD PTR [rdi+5384]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+5392]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+5400]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, r13
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5376]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+5384]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+5392]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+5400]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, r14
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5376]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+5384]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+5392]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+5400]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, r15
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5376]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+5384]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+5392]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+5400]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+5440], r12
	mov QWORD PTR [rdi+5448], r13
	mov QWORD PTR [rdi+5456], r14
	mov QWORD PTR [rdi+5464], r15
	mov rax, rbx
	sub rax, 1
	mov ecx, 160
	mul rcx
	mov rdx, rdi
	add rdx, 2752
	add rdx, rax
	mov rax, QWORD PTR [rdi+5312]
	mov QWORD PTR [rdx], rax
	mov rax, QWORD PTR [rdi+5320]
	mov QWORD PTR [rdx+8], rax
	mov rax, QWORD PTR [rdi+5328]
	mov QWORD PTR [rdx+16], rax
	mov rax, QWORD PTR [rdi+5336]
	mov QWORD PTR [rdx+24], rax
	mov rax, QWORD PTR [rdi+5344]
	mov QWORD PTR [rdx+32], rax
	mov rax, QWORD PTR [rdi+5352]
	mov QWORD PTR [rdx+40], rax
	mov rax, QWORD PTR [rdi+5360]
	mov QWORD PTR [rdx+48], rax
	mov rax, QWORD PTR [rdi+5368]
	mov QWORD PTR [rdx+56], rax
	mov rax, QWORD PTR [rdi+5376]
	mov QWORD PTR [rdx+64], rax
	mov rax, QWORD PTR [rdi+5384]
	mov QWORD PTR [rdx+72], rax
	mov rax, QWORD PTR [rdi+5392]
	mov QWORD PTR [rdx+80], rax
	mov rax, QWORD PTR [rdi+5400]
	mov QWORD PTR [rdx+88], rax
	mov rax, QWORD PTR [rdi+5408]
	mov QWORD PTR [rdx+96], rax
	mov rax, QWORD PTR [rdi+5416]
	mov QWORD PTR [rdx+104], rax
	mov rax, QWORD PTR [rdi+5424]
	mov QWORD PTR [rdx+112], rax
	mov rax, QWORD PTR [rdi+5432]
	mov QWORD PTR [rdx+120], rax
	mov rax, QWORD PTR [rdi+5440]
	mov QWORD PTR [rdx+128], rax
	mov rax, QWORD PTR [rdi+5448]
	mov QWORD PTR [rdx+136], rax
	mov rax, QWORD PTR [rdi+5456]
	mov QWORD PTR [rdx+144], rax
	mov rax, QWORD PTR [rdi+5464]
	mov QWORD PTR [rdx+152], rax
	cmp rbx, 16
	jne 24b
	mov ebx, 51
	mov rax, QWORD PTR [rdi+1280]
	mov QWORD PTR [rdi+512], rax
	mov rax, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+520], rax
	mov rax, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+528], rax
	mov rax, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+536], rax
	mov rax, QWORD PTR [rdi+1440]
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rdi+1448]
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rdi+1456]
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rdi+1464]
	mov QWORD PTR [rdi+568], rax
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+576], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+584], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+592], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+600], rax
	sub rbx, 1
	mov rax, rbx
	mov ecx, 5
	mul rcx
	mov rcx, rax
	mov eax, 0
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2405]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2404]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2403]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2402]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2401]
	add rax, rdx
	mov rdx, rax
	shr rdx, 4
	sub rdx, 1
	xor rax, rdx
	and rax, 15
	add rax, 1
	mov r8, rax
	mov rdx, rdi
	add rdx, 2752
	vmovq xmm13, r8
	vpbroadcastd ymm13, xmm13
	mov ecx, 1
	vmovq xmm12, rcx
	vpbroadcastd ymm12, xmm12
	vmovdqa ymm14, ymm12
	vpxor ymm0, ymm0, ymm0
	vpxor ymm1, ymm1, ymm1
	vpxor ymm2, ymm2, ymm2
	vpxor ymm3, ymm3, ymm3
	vpxor ymm4, ymm4, ymm4
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+32]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+64]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+96]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+128]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+160]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+192]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+224]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+256]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+288]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+320]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+352]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+384]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+416]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+448]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+480]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+512]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+544]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+576]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+608]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+640]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+672]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+704]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+736]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+768]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+800]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+832]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+864]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+896]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+928]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+960]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+992]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1024]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1056]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1088]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1120]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1152]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1184]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1216]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1248]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1280]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1312]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1344]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1376]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1408]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1440]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1472]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1504]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1536]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1568]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1600]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1632]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1664]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1696]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1728]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1760]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1792]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1824]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1856]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1888]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1920]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1952]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1984]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2016]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2048]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2080]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2112]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2144]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2176]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2208]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2240]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2272]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2304]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2336]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2368]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2400]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2432]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2464]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2496]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2528]
	vpor ymm4, ymm4, ymm11
	vmovdqu YMMWORD PTR [rdi+5312], ymm0
	vmovdqu YMMWORD PTR [rdi+5344], ymm1
	vmovdqu YMMWORD PTR [rdi+5376], ymm2
	vmovdqu YMMWORD PTR [rdi+5408], ymm3
	vmovdqu YMMWORD PTR [rdi+5440], ymm4
	vzeroupper
	mov r8, QWORD PTR [rdi+160]
	mov r9, QWORD PTR [rdi+168]
	mov r10, QWORD PTR [rdi+176]
	mov r11, QWORD PTR [rdi+184]
	sub r8, QWORD PTR [rdi+5344]
	sbb r9, QWORD PTR [rdi+5352]
	sbb r10, QWORD PTR [rdi+5360]
	sbb r11, QWORD PTR [rdi+5368]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+1024], r8
	mov QWORD PTR [rdi+1032], r9
	mov QWORD PTR [rdi+1040], r10
	mov QWORD PTR [rdi+1048], r11
	mov rax, rbx
	mov ecx, 5
	mul rcx
	mov rcx, rax
	movzx eax, BYTE PTR [rdi+rcx*1+2405]
	sub rax, 1
	mov rcx, rax
	mov rax, QWORD PTR [rdi+5344]
	mov rdx, QWORD PTR [rdi+1024]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+5344], rax
	mov rax, QWORD PTR [rdi+5352]
	mov rdx, QWORD PTR [rdi+1032]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+5352], rax
	mov rax, QWORD PTR [rdi+5360]
	mov rdx, QWORD PTR [rdi+1040]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+5360], rax
	mov rax, QWORD PTR [rdi+5368]
	mov rdx, QWORD PTR [rdi+1048]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+5368], rax
	add rbx, 1
25:
	sub rbx, 1
	add rbx, 20480
26:
	mov r8, QWORD PTR [rdi+544]
	mov r9, QWORD PTR [rdi+552]
	mov r10, QWORD PTR [rdi+560]
	mov r11, QWORD PTR [rdi+568]
	mov r12d, 0
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+832], r8
	mov QWORD PTR [rdi+840], r9
	mov QWORD PTR [rdi+848], r10
	mov QWORD PTR [rdi+856], r11
	mov rdx, QWORD PTR [rdi+576]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+584]
	mulx r11, rax, QWORD PTR [rdi+592]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+600]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+584]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+592]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+600]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+576]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+584]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+592]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+600]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+800], r12
	mov QWORD PTR [rdi+808], r13
	mov QWORD PTR [rdi+816], r14
	mov QWORD PTR [rdi+824], r15
	mov rdx, QWORD PTR [rdi+832]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+576]
	mulx r10, rax, QWORD PTR [rdi+584]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+592]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+600]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+840]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+848]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+600]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+856]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+600]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+576], r12
	mov QWORD PTR [rdi+584], r13
	mov QWORD PTR [rdi+592], r14
	mov QWORD PTR [rdi+600], r15
	mov rdx, QWORD PTR [rdi+832]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+840]
	mulx r11, rax, QWORD PTR [rdi+848]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+856]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+840]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+856]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+848]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+856]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+832]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+840]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+848]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+856]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+832], r12
	mov QWORD PTR [rdi+840], r13
	mov QWORD PTR [rdi+848], r14
	mov QWORD PTR [rdi+856], r15
	mov r8, QWORD PTR [rdi+512]
	mov r9, QWORD PTR [rdi+520]
	mov r10, QWORD PTR [rdi+528]
	mov r11, QWORD PTR [rdi+536]
	sub r8, QWORD PTR [rdi+800]
	sbb r9, QWORD PTR [rdi+808]
	sbb r10, QWORD PTR [rdi+816]
	sbb r11, QWORD PTR [rdi+824]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+896], r8
	mov QWORD PTR [rdi+904], r9
	mov QWORD PTR [rdi+912], r10
	mov QWORD PTR [rdi+920], r11
	mov r8, QWORD PTR [rdi+512]
	mov r9, QWORD PTR [rdi+520]
	mov r10, QWORD PTR [rdi+528]
	mov r11, QWORD PTR [rdi+536]
	mov r12d, 0
	add r8, QWORD PTR [rdi+800]
	adc r9, QWORD PTR [rdi+808]
	adc r10, QWORD PTR [rdi+816]
	adc r11, QWORD PTR [rdi+824]
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+928], r8
	mov QWORD PTR [rdi+936], r9
	mov QWORD PTR [rdi+944], r10
	mov QWORD PTR [rdi+952], r11
	mov rdx, QWORD PTR [rdi+896]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+928]
	mulx r10, rax, QWORD PTR [rdi+936]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+944]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+952]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+904]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+928]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+936]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+944]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+952]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+912]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+928]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+936]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+944]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+952]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+920]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+928]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+936]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+944]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+952]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+896], r12
	mov QWORD PTR [rdi+904], r13
	mov QWORD PTR [rdi+912], r14
	mov QWORD PTR [rdi+920], r15
	mov r8, r12
	mov r9, r13
	mov r10, r14
	mov r11, r15
	mov r12d, 0
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+928], r8
	mov QWORD PTR [rdi+936], r9
	mov QWORD PTR [rdi+944], r10
	mov QWORD PTR [rdi+952], r11
	mov r8, r8
	mov r9, r9
	mov r10, r10
	mov r11, r11
	mov r12d, 0
	add r8, QWORD PTR [rdi+896]
	adc r9, QWORD PTR [rdi+904]
	adc r10, QWORD PTR [rdi+912]
	adc r11, QWORD PTR [rdi+920]
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+896], r8
	mov QWORD PTR [rdi+904], r9
	mov QWORD PTR [rdi+912], r10
	mov QWORD PTR [rdi+920], r11
	mov rdx, QWORD PTR [rdi+512]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+832]
	mulx r10, rax, QWORD PTR [rdi+840]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+848]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+856]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+520]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+856]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+528]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+856]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+536]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+856]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
	mov QWORD PTR [rdi+880], r14
	mov QWORD PTR [rdi+888], r15
	mov rdx, QWORD PTR [rdi+832]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+840]
	mulx r11, rax, QWORD PTR [rdi+848]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+856]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+840]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+856]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+848]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+856]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+832]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+840]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+848]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+856]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+832], r12
	mov QWORD PTR [rdi+840], r13
	mov QWORD PTR [rdi+848], r14
	mov QWORD PTR [rdi+856], r15
	mov r8, r12
	mov r9, r13
	mov r10, r14
	mov r11, r15
	mov rax, r8
	and rax, 1
	mov ecx, 0
	sub rcx, rax
	mov rdx, rcx
	shr rdx, 32
	movabs rbp, -4294967295
	and rbp, rcx
	mov r12d, 0
	add r8, rcx
	adc r9, rdx
	adc r10, 0
	adc r11, rbp
	adc r12, 0
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
	mov QWORD PTR [rdi+832], r8
	mov QWORD PTR [rdi+840], r9
	mov QWORD PTR [rdi+848], r10
	mov QWORD PTR [rdi+856], r11
	mov r8, QWORD PTR [rdi+864]
	mov r9, QWORD PTR [rdi+872]
	mov r10, QWORD PTR [rdi+880]
	mov r11, QWORD PTR [rdi+888]
	mov r12d, 0
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+928], r8
	mov QWORD PTR [rdi+936], r9
	mov QWORD PTR [rdi+944], r10
	mov QWORD PTR [rdi+952], r11
	mov rdx, QWORD PTR [rdi+896]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+904]
	mulx r11, rax, QWORD PTR [rdi+912]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+920]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+904]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+912]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+920]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+912]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+920]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+896]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+904]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+912]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+920]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+512], r12
	mov QWORD PTR [rdi+520], r13
	mov QWORD PTR [rdi+528], r14
	mov QWORD PTR [rdi+536], r15
	mov r8, r12
	mov r9, r13
	mov r10, r14
	mov r11, r15
	sub r8, QWORD PTR [rdi+928]
	sbb r9, QWORD PTR [rdi+936]
	sbb r10, QWORD PTR [rdi+944]
	sbb r11, QWORD PTR [rdi+952]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+512], r8
	mov QWORD PTR [rdi+520], r9
	mov QWORD PTR [rdi+528], r10
	mov QWORD PTR [rdi+536], r11
	mov r8, QWORD PTR [rdi+864]
	mov r9, QWORD PTR [rdi+872]
	mov r10, QWORD PTR [rdi+880]
	mov r11, QWORD PTR [rdi+888]
	sub r8, QWORD PTR [rdi+512]
	sbb r9, QWORD PTR [rdi+520]
	sbb r10, QWORD PTR [rdi+528]
	sbb r11, QWORD PTR [rdi+536]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+544], r8
	mov QWORD PTR [rdi+552], r9
	mov QWORD PTR [rdi+560], r10
	mov QWORD PTR [rdi+568], r11
	mov rdx, QWORD PTR [rdi+896]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+544]
	mulx r10, rax, QWORD PTR [rdi+552]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+560]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+568]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+904]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+544]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+552]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+560]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+568]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+912]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+544]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+552]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+560]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+568]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+920]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+544]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+552]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+560]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+568]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+544], r12
	mov QWORD PTR [rdi+552], r13
	mov QWORD PTR [rdi+560], r14
	mov QWORD PTR [rdi+568], r15
	mov r8, r12
	mov r9, r13
	mov r10, r14
	mov r11, r15
	sub r8, QWORD PTR [rdi+832]
	sbb r9, QWORD PTR [rdi+840]
	sbb r10, QWORD PTR [rdi+848]
	sbb r11, QWORD PTR [rdi+856]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+544], r8
	mov QWORD PTR [rdi+552], r9
	mov QWORD PTR [rdi+560], r10
	mov QWORD PTR [rdi+568], r11
	sub rbx, 4096
	cmp rbx, 4096
	jae 26b
	sub rbx, 1
	mov rax, rbx
	mov ecx, 5
	mul rcx
	mov rcx, rax
	mov eax, 0
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2405]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2404]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2403]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2402]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+2401]
	add rax, rdx
	mov rdx, rax
	shr rdx, 4
	sub rdx, 1
	xor rax, rdx
	and rax, 15
	add rax, 1
	mov r8, rax
	add rbx, 1
	vmovq xmm13, r8
	vpbroadcastd ymm13, xmm13
	mov ecx, 1
	vmovq xmm12, rcx
	vpbroadcastd ymm12, xmm12
	vmovdqa ymm14, ymm12
	vpxor ymm0, ymm0, ymm0
	vpxor ymm1, ymm1, ymm1
	vpxor ymm2, ymm2, ymm2
	vpxor ymm3, ymm3, ymm3
	vpxor ymm4, ymm4, ymm4
	mov rdx, QWORD PTR [rdi+576]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+584]
	mulx r11, rax, QWORD PTR [rdi+592]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+600]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+584]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+592]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+600]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+576]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+584]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+592]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+600]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+800], r12
	mov QWORD PTR [rdi+808], r13
	mov QWORD PTR [rdi+816], r14
	mov QWORD PTR [rdi+824], r15
	mov rdx, QWORD PTR [rdi+512]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+5408]
	mulx r10, rax, QWORD PTR [rdi+5416]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+5424]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+5432]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+520]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5408]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+5416]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+5424]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+5432]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+528]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5408]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+5416]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+5424]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+5432]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+536]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5408]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+5416]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+5424]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+5432]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
	mov QWORD PTR [rdi+880], r14
	mov QWORD PTR [rdi+888], r15
	mov rdx, rdi
	add rdx, 2752
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+32]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+64]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+96]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+128]
	vpor ymm4, ymm4, ymm11
	mov rdx, QWORD PTR [rdi+5312]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+800]
	mulx r10, rax, QWORD PTR [rdi+808]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+816]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+824]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+5320]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+808]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+816]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+824]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+5328]
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
	mov rdx, QWORD PTR [rdi+5336]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r11, rax
	adcx r12, rcx
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
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+896], r12
	mov QWORD PTR [rdi+904], r13
	mov QWORD PTR [rdi+912], r14
	mov QWORD PTR [rdi+920], r15
	mov rdx, rdi
	add rdx, 2752
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+160]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+192]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+224]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+256]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+288]
	vpor ymm4, ymm4, ymm11
	mov rdx, QWORD PTR [rdi+544]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+5440]
	mulx r10, rax, QWORD PTR [rdi+5448]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+5456]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+5464]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+552]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5440]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+5448]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+5456]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+5464]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+560]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5440]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+5448]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+5456]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+5464]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+568]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5440]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+5448]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+5456]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+5464]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+928], r12
	mov QWORD PTR [rdi+936], r13
	mov QWORD PTR [rdi+944], r14
	mov QWORD PTR [rdi+952], r15
	mov rdx, rdi
	add rdx, 2752
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+320]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+352]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+384]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+416]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+448]
	vpor ymm4, ymm4, ymm11
	mov rdx, QWORD PTR [rdi+5344]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+576]
	mulx r10, rax, QWORD PTR [rdi+584]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+592]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+600]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+5352]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+5360]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+600]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+5368]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+600]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+960], r12
	mov QWORD PTR [rdi+968], r13
	mov QWORD PTR [rdi+976], r14
	mov QWORD PTR [rdi+984], r15
	mov rdx, r12
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+800]
	mulx r10, rax, QWORD PTR [rdi+808]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+816]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+824]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, r13
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+808]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+816]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+824]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, r14
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
	mov rdx, r15
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r11, rax
	adcx r12, rcx
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
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+960], r12
	mov QWORD PTR [rdi+968], r13
	mov QWORD PTR [rdi+976], r14
	mov QWORD PTR [rdi+984], r15
	mov rdx, rdi
	add rdx, 2752
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+480]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+512]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+544]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+576]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+608]
	vpor ymm4, ymm4, ymm11
	mov r8, QWORD PTR [rdi+896]
	mov r9, QWORD PTR [rdi+904]
	mov r10, QWORD PTR [rdi+912]
	mov r11, QWORD PTR [rdi+920]
	sub r8, QWORD PTR [rdi+864]
	sbb r9, QWORD PTR [rdi+872]
	sbb r10, QWORD PTR [rdi+880]
	sbb r11, QWORD PTR [rdi+888]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+896], r8
	mov QWORD PTR [rdi+904], r9
	mov QWORD PTR [rdi+912], r10
	mov QWORD PTR [rdi+920], r11
	mov rdx, rdi
	add rdx, 2752
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+640]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+672]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+704]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+736]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+768]
	vpor ymm4, ymm4, ymm11
	mov r8, QWORD PTR [rdi+960]
	mov r9, QWORD PTR [rdi+968]
	mov r10, QWORD PTR [rdi+976]
	mov r11, QWORD PTR [rdi+984]
	sub r8, QWORD PTR [rdi+928]
	sbb r9, QWORD PTR [rdi+936]
	sbb r10, QWORD PTR [rdi+944]
	sbb r11, QWORD PTR [rdi+952]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+960], r8
	mov QWORD PTR [rdi+968], r9
	mov QWORD PTR [rdi+976], r10
	mov QWORD PTR [rdi+984], r11
	mov rdx, rdi
	add rdx, 2752
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+800]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+832]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+864]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+896]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+928]
	vpor ymm4, ymm4, ymm11
	mov rdx, QWORD PTR [rdi+896]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+904]
	mulx r11, rax, QWORD PTR [rdi+912]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+920]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+904]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+912]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+920]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+912]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+920]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+896]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+904]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+912]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+920]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+800], r12
	mov QWORD PTR [rdi+808], r13
	mov QWORD PTR [rdi+816], r14
	mov QWORD PTR [rdi+824], r15
	mov rdx, r12
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+896]
	mulx r10, rax, QWORD PTR [rdi+904]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+912]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+920]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, r13
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+896]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+904]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+912]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+920]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, r14
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+896]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+904]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+912]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+920]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, r15
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+896]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+904]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+912]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+920]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+832], r12
	mov QWORD PTR [rdi+840], r13
	mov QWORD PTR [rdi+848], r14
	mov QWORD PTR [rdi+856], r15
	mov rdx, rdi
	add rdx, 2752
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+960]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+992]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1024]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1056]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1088]
	vpor ymm4, ymm4, ymm11
	mov rdx, QWORD PTR [rdi+864]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+800]
	mulx r10, rax, QWORD PTR [rdi+808]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+816]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+824]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+872]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+808]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+816]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+824]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+880]
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
	mov rdx, QWORD PTR [rdi+888]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r11, rax
	adcx r12, rcx
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
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
	mov QWORD PTR [rdi+880], r14
	mov QWORD PTR [rdi+888], r15
	mov rdx, rdi
	add rdx, 2752
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1120]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1152]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1184]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1216]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1248]
	vpor ymm4, ymm4, ymm11
	mov rdx, QWORD PTR [rdi+960]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+968]
	mulx r11, rax, QWORD PTR [rdi+976]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+984]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+968]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+976]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+984]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+976]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+984]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+960]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+968]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+976]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+984]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+512], r12
	mov QWORD PTR [rdi+520], r13
	mov QWORD PTR [rdi+528], r14
	mov QWORD PTR [rdi+536], r15
	mov rdx, rdi
	add rdx, 2752
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1280]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1312]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1344]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1376]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1408]
	vpor ymm4, ymm4, ymm11
	mov r8, r12
	mov r9, r13
	mov r10, r14
	mov r11, r15
	sub r8, QWORD PTR [rdi+832]
	sbb r9, QWORD PTR [rdi+840]
	sbb r10, QWORD PTR [rdi+848]
	sbb r11, QWORD PTR [rdi+856]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+512], r8
	mov QWORD PTR [rdi+520], r9
	mov QWORD PTR [rdi+528], r10
	mov QWORD PTR [rdi+536], r11
	mov r8, r8
	mov r9, r9
	mov r10, r10
	mov r11, r11
	sub r8, QWORD PTR [rdi+864]
	sbb r9, QWORD PTR [rdi+872]
	sbb r10, QWORD PTR [rdi+880]
	sbb r11, QWORD PTR [rdi+888]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+512], r8
	mov QWORD PTR [rdi+520], r9
	mov QWORD PTR [rdi+528], r10
	mov QWORD PTR [rdi+536], r11
	mov rdx, rdi
	add rdx, 2752
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1440]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1472]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1504]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1536]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1568]
	vpor ymm4, ymm4, ymm11
	mov r8, r8
	mov r9, r9
	mov r10, r10
	mov r11, r11
	sub r8, QWORD PTR [rdi+864]
	sbb r9, QWORD PTR [rdi+872]
	sbb r10, QWORD PTR [rdi+880]
	sbb r11, QWORD PTR [rdi+888]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+512], r8
	mov QWORD PTR [rdi+520], r9
	mov QWORD PTR [rdi+528], r10
	mov QWORD PTR [rdi+536], r11
	mov rdx, rdi
	add rdx, 2752
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1600]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1632]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1664]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1696]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1728]
	vpor ymm4, ymm4, ymm11
	mov r8, QWORD PTR [rdi+864]
	mov r9, QWORD PTR [rdi+872]
	mov r10, QWORD PTR [rdi+880]
	mov r11, QWORD PTR [rdi+888]
	sub r8, QWORD PTR [rdi+512]
	sbb r9, QWORD PTR [rdi+520]
	sbb r10, QWORD PTR [rdi+528]
	sbb r11, QWORD PTR [rdi+536]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+544], r8
	mov QWORD PTR [rdi+552], r9
	mov QWORD PTR [rdi+560], r10
	mov QWORD PTR [rdi+568], r11
	mov rdx, rdi
	add rdx, 2752
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1760]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1792]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1824]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1856]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1888]
	vpor ymm4, ymm4, ymm11
	mov rdx, QWORD PTR [rdi+960]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+544]
	mulx r10, rax, QWORD PTR [rdi+552]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+560]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+568]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+968]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+544]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+552]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+560]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+568]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+976]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+544]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+552]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+560]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+568]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+984]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+544]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+552]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+560]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+568]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+544], r12
	mov QWORD PTR [rdi+552], r13
	mov QWORD PTR [rdi+560], r14
	mov QWORD PTR [rdi+568], r15
	mov rdx, QWORD PTR [rdi+928]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+832]
	mulx r10, rax, QWORD PTR [rdi+840]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+848]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+856]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+936]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+856]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+944]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+856]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+952]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+856]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+928], r12
	mov QWORD PTR [rdi+936], r13
	mov QWORD PTR [rdi+944], r14
	mov QWORD PTR [rdi+952], r15
	mov rdx, rdi
	add rdx, 2752
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1920]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1952]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1984]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2016]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2048]
	vpor ymm4, ymm4, ymm11
	mov r8, QWORD PTR [rdi+544]
	mov r9, QWORD PTR [rdi+552]
	mov r10, QWORD PTR [rdi+560]
	mov r11, QWORD PTR [rdi+568]
	sub r8, QWORD PTR [rdi+928]
	sbb r9, QWORD PTR [rdi+936]
	sbb r10, QWORD PTR [rdi+944]
	sbb r11, QWORD PTR [rdi+952]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+544], r8
	mov QWORD PTR [rdi+552], r9
	mov QWORD PTR [rdi+560], r10
	mov QWORD PTR [rdi+568], r11
	mov rdx, rdi
	add rdx, 2752
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2080]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2112]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2144]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2176]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2208]
	vpor ymm4, ymm4, ymm11
	mov rdx, QWORD PTR [rdi+576]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+5376]
	mulx r10, rax, QWORD PTR [rdi+5384]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+5392]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+5400]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+584]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5376]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+5384]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+5392]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+5400]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+592]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5376]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+5384]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+5392]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+5400]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+600]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5376]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+5384]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+5392]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+5400]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+576], r12
	mov QWORD PTR [rdi+584], r13
	mov QWORD PTR [rdi+592], r14
	mov QWORD PTR [rdi+600], r15
	mov rdx, rdi
	add rdx, 2752
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2240]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2272]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2304]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2336]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2368]
	vpor ymm4, ymm4, ymm11
	mov rdx, r12
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+896]
	mulx r10, rax, QWORD PTR [rdi+904]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+912]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+920]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, r13
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+896]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+904]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+912]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+920]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, r14
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+896]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+904]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+912]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+920]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, r15
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+896]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+904]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+912]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+920]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+576], r12
	mov QWORD PTR [rdi+584], r13
	mov QWORD PTR [rdi+592], r14
	mov QWORD PTR [rdi+600], r15
	mov rdx, rdi
	add rdx, 2752
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2400]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2432]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2464]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2496]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2528]
	vpor ymm4, ymm4, ymm11
	vmovdqu YMMWORD PTR [rdi+5312], ymm0
	vmovdqu YMMWORD PTR [rdi+5344], ymm1
	vmovdqu YMMWORD PTR [rdi+5376], ymm2
	vmovdqu YMMWORD PTR [rdi+5408], ymm3
	vmovdqu YMMWORD PTR [rdi+5440], ymm4
	vzeroupper
	sub rbx, 1
	mov r8, QWORD PTR [rdi+160]
	mov r9, QWORD PTR [rdi+168]
	mov r10, QWORD PTR [rdi+176]
	mov r11, QWORD PTR [rdi+184]
	sub r8, QWORD PTR [rdi+5344]
	sbb r9, QWORD PTR [rdi+5352]
	sbb r10, QWORD PTR [rdi+5360]
	sbb r11, QWORD PTR [rdi+5368]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+1024], r8
	mov QWORD PTR [rdi+1032], r9
	mov QWORD PTR [rdi+1040], r10
	mov QWORD PTR [rdi+1048], r11
	mov rax, rbx
	mov ecx, 5
	mul rcx
	mov rcx, rax
	movzx eax, BYTE PTR [rdi+rcx*1+2405]
	sub rax, 1
	mov rcx, rax
	mov rax, QWORD PTR [rdi+5344]
	mov rdx, QWORD PTR [rdi+1024]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+5344], rax
	mov rax, QWORD PTR [rdi+5352]
	mov rdx, QWORD PTR [rdi+1032]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+5352], rax
	mov rax, QWORD PTR [rdi+5360]
	mov rdx, QWORD PTR [rdi+1040]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+5360], rax
	mov rax, QWORD PTR [rdi+5368]
	mov rdx, QWORD PTR [rdi+1048]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+5368], rax
	add rbx, 1
	cmp rbx, 1
	jne 25b
	sub rbx, 1
	add rbx, 20480
27:
	mov r8, QWORD PTR [rdi+544]
	mov r9, QWORD PTR [rdi+552]
	mov r10, QWORD PTR [rdi+560]
	mov r11, QWORD PTR [rdi+568]
	mov r12d, 0
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+832], r8
	mov QWORD PTR [rdi+840], r9
	mov QWORD PTR [rdi+848], r10
	mov QWORD PTR [rdi+856], r11
	mov rdx, QWORD PTR [rdi+576]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+584]
	mulx r11, rax, QWORD PTR [rdi+592]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+600]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+584]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+592]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+600]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+576]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+584]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+592]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+600]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+800], r12
	mov QWORD PTR [rdi+808], r13
	mov QWORD PTR [rdi+816], r14
	mov QWORD PTR [rdi+824], r15
	mov rdx, QWORD PTR [rdi+832]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+576]
	mulx r10, rax, QWORD PTR [rdi+584]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+592]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+600]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+840]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+848]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+600]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+856]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+600]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+576], r12
	mov QWORD PTR [rdi+584], r13
	mov QWORD PTR [rdi+592], r14
	mov QWORD PTR [rdi+600], r15
	mov rdx, QWORD PTR [rdi+832]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+840]
	mulx r11, rax, QWORD PTR [rdi+848]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+856]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+840]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+856]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+848]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+856]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+832]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+840]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+848]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+856]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+832], r12
	mov QWORD PTR [rdi+840], r13
	mov QWORD PTR [rdi+848], r14
	mov QWORD PTR [rdi+856], r15
	mov r8, QWORD PTR [rdi+512]
	mov r9, QWORD PTR [rdi+520]
	mov r10, QWORD PTR [rdi+528]
	mov r11, QWORD PTR [rdi+536]
	sub r8, QWORD PTR [rdi+800]
	sbb r9, QWORD PTR [rdi+808]
	sbb r10, QWORD PTR [rdi+816]
	sbb r11, QWORD PTR [rdi+824]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+896], r8
	mov QWORD PTR [rdi+904], r9
	mov QWORD PTR [rdi+912], r10
	mov QWORD PTR [rdi+920], r11
	mov r8, QWORD PTR [rdi+512]
	mov r9, QWORD PTR [rdi+520]
	mov r10, QWORD PTR [rdi+528]
	mov r11, QWORD PTR [rdi+536]
	mov r12d, 0
	add r8, QWORD PTR [rdi+800]
	adc r9, QWORD PTR [rdi+808]
	adc r10, QWORD PTR [rdi+816]
	adc r11, QWORD PTR [rdi+824]
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+928], r8
	mov QWORD PTR [rdi+936], r9
	mov QWORD PTR [rdi+944], r10
	mov QWORD PTR [rdi+952], r11
	mov rdx, QWORD PTR [rdi+896]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+928]
	mulx r10, rax, QWORD PTR [rdi+936]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+944]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+952]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+904]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+928]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+936]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+944]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+952]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+912]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+928]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+936]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+944]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+952]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+920]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+928]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+936]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+944]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+952]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+896], r12
	mov QWORD PTR [rdi+904], r13
	mov QWORD PTR [rdi+912], r14
	mov QWORD PTR [rdi+920], r15
	mov r8, r12
	mov r9, r13
	mov r10, r14
	mov r11, r15
	mov r12d, 0
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+928], r8
	mov QWORD PTR [rdi+936], r9
	mov QWORD PTR [rdi+944], r10
	mov QWORD PTR [rdi+952], r11
	mov r8, r8
	mov r9, r9
	mov r10, r10
	mov r11, r11
	mov r12d, 0
	add r8, QWORD PTR [rdi+896]
	adc r9, QWORD PTR [rdi+904]
	adc r10, QWORD PTR [rdi+912]
	adc r11, QWORD PTR [rdi+920]
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+896], r8
	mov QWORD PTR [rdi+904], r9
	mov QWORD PTR [rdi+912], r10
	mov QWORD PTR [rdi+920], r11
	mov rdx, QWORD PTR [rdi+512]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+832]
	mulx r10, rax, QWORD PTR [rdi+840]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+848]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+856]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+520]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+856]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+528]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+856]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+536]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+856]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
	mov QWORD PTR [rdi+880], r14
	mov QWORD PTR [rdi+888], r15
	mov rdx, QWORD PTR [rdi+832]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+840]
	mulx r11, rax, QWORD PTR [rdi+848]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+856]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+840]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+856]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+848]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+856]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+832]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+840]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+848]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+856]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+832], r12
	mov QWORD PTR [rdi+840], r13
	mov QWORD PTR [rdi+848], r14
	mov QWORD PTR [rdi+856], r15
	mov r8, r12
	mov r9, r13
	mov r10, r14
	mov r11, r15
	mov rax, r8
	and rax, 1
	mov ecx, 0
	sub rcx, rax
	mov rdx, rcx
	shr rdx, 32
	movabs rbp, -4294967295
	and rbp, rcx
	mov r12d, 0
	add r8, rcx
	adc r9, rdx
	adc r10, 0
	adc r11, rbp
	adc r12, 0
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
	mov QWORD PTR [rdi+832], r8
	mov QWORD PTR [rdi+840], r9
	mov QWORD PTR [rdi+848], r10
	mov QWORD PTR [rdi+856], r11
	mov r8, QWORD PTR [rdi+864]
	mov r9, QWORD PTR [rdi+872]
	mov r10, QWORD PTR [rdi+880]
	mov r11, QWORD PTR [rdi+888]
	mov r12d, 0
	add r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, 0
	mov rax, r8
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r9
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r10
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r11
	sbb rbp, QWORD PTR [rdi+88]
	sbb r12, 0
	cmovae r8, rax
	cmovae r9, rcx
	cmovae r10, rdx
	cmovae r11, rbp
	mov QWORD PTR [rdi+928], r8
	mov QWORD PTR [rdi+936], r9
	mov QWORD PTR [rdi+944], r10
	mov QWORD PTR [rdi+952], r11
	mov rdx, QWORD PTR [rdi+896]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+904]
	mulx r11, rax, QWORD PTR [rdi+912]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+920]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+904]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+912]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+920]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+912]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+920]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+896]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+904]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+912]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+920]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+512], r12
	mov QWORD PTR [rdi+520], r13
	mov QWORD PTR [rdi+528], r14
	mov QWORD PTR [rdi+536], r15
	mov r8, r12
	mov r9, r13
	mov r10, r14
	mov r11, r15
	sub r8, QWORD PTR [rdi+928]
	sbb r9, QWORD PTR [rdi+936]
	sbb r10, QWORD PTR [rdi+944]
	sbb r11, QWORD PTR [rdi+952]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+512], r8
	mov QWORD PTR [rdi+520], r9
	mov QWORD PTR [rdi+528], r10
	mov QWORD PTR [rdi+536], r11
	mov r8, QWORD PTR [rdi+864]
	mov r9, QWORD PTR [rdi+872]
	mov r10, QWORD PTR [rdi+880]
	mov r11, QWORD PTR [rdi+888]
	sub r8, QWORD PTR [rdi+512]
	sbb r9, QWORD PTR [rdi+520]
	sbb r10, QWORD PTR [rdi+528]
	sbb r11, QWORD PTR [rdi+536]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+544], r8
	mov QWORD PTR [rdi+552], r9
	mov QWORD PTR [rdi+560], r10
	mov QWORD PTR [rdi+568], r11
	mov rdx, QWORD PTR [rdi+896]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+544]
	mulx r10, rax, QWORD PTR [rdi+552]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+560]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+568]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+904]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+544]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+552]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+560]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+568]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+912]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+544]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+552]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+560]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+568]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+920]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+544]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+552]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+560]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+568]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+544], r12
	mov QWORD PTR [rdi+552], r13
	mov QWORD PTR [rdi+560], r14
	mov QWORD PTR [rdi+568], r15
	mov r8, r12
	mov r9, r13
	mov r10, r14
	mov r11, r15
	sub r8, QWORD PTR [rdi+832]
	sbb r9, QWORD PTR [rdi+840]
	sbb r10, QWORD PTR [rdi+848]
	sbb r11, QWORD PTR [rdi+856]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+544], r8
	mov QWORD PTR [rdi+552], r9
	mov QWORD PTR [rdi+560], r10
	mov QWORD PTR [rdi+568], r11
	sub rbx, 4096
	cmp rbx, 4096
	jae 27b
	mov rdx, QWORD PTR [rdi+576]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+584]
	mulx r11, rax, QWORD PTR [rdi+592]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+600]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+584]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+592]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+600]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+576]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+584]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+592]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+600]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+800], r12
	mov QWORD PTR [rdi+808], r13
	mov QWORD PTR [rdi+816], r14
	mov QWORD PTR [rdi+824], r15
	mov rdx, QWORD PTR [rdi+512]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+5408]
	mulx r10, rax, QWORD PTR [rdi+5416]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+5424]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+5432]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+520]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5408]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+5416]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+5424]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+5432]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+528]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5408]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+5416]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+5424]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+5432]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+536]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5408]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+5416]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+5424]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+5432]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
	mov QWORD PTR [rdi+880], r14
	mov QWORD PTR [rdi+888], r15
	mov rdx, QWORD PTR [rdi+5312]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+800]
	mulx r10, rax, QWORD PTR [rdi+808]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+816]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+824]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+5320]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+808]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+816]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+824]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+5328]
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
	mov rdx, QWORD PTR [rdi+5336]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r11, rax
	adcx r12, rcx
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
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+896], r12
	mov QWORD PTR [rdi+904], r13
	mov QWORD PTR [rdi+912], r14
	mov QWORD PTR [rdi+920], r15
	mov rdx, QWORD PTR [rdi+544]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+5440]
	mulx r10, rax, QWORD PTR [rdi+5448]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+5456]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+5464]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+552]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5440]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+5448]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+5456]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+5464]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+560]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5440]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+5448]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+5456]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+5464]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+568]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5440]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+5448]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+5456]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+5464]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+928], r12
	mov QWORD PTR [rdi+936], r13
	mov QWORD PTR [rdi+944], r14
	mov QWORD PTR [rdi+952], r15
	mov rdx, QWORD PTR [rdi+5344]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+576]
	mulx r10, rax, QWORD PTR [rdi+584]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+592]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+600]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+5352]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+5360]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+600]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+5368]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+600]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+960], r12
	mov QWORD PTR [rdi+968], r13
	mov QWORD PTR [rdi+976], r14
	mov QWORD PTR [rdi+984], r15
	mov rdx, r12
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+800]
	mulx r10, rax, QWORD PTR [rdi+808]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+816]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+824]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, r13
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+808]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+816]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+824]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, r14
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
	mov rdx, r15
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r11, rax
	adcx r12, rcx
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
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+960], r12
	mov QWORD PTR [rdi+968], r13
	mov QWORD PTR [rdi+976], r14
	mov QWORD PTR [rdi+984], r15
	mov r8, QWORD PTR [rdi+896]
	mov r9, QWORD PTR [rdi+904]
	mov r10, QWORD PTR [rdi+912]
	mov r11, QWORD PTR [rdi+920]
	sub r8, QWORD PTR [rdi+864]
	sbb r9, QWORD PTR [rdi+872]
	sbb r10, QWORD PTR [rdi+880]
	sbb r11, QWORD PTR [rdi+888]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+896], r8
	mov QWORD PTR [rdi+904], r9
	mov QWORD PTR [rdi+912], r10
	mov QWORD PTR [rdi+920], r11
	mov r8, QWORD PTR [rdi+960]
	mov r9, QWORD PTR [rdi+968]
	mov r10, QWORD PTR [rdi+976]
	mov r11, QWORD PTR [rdi+984]
	sub r8, QWORD PTR [rdi+928]
	sbb r9, QWORD PTR [rdi+936]
	sbb r10, QWORD PTR [rdi+944]
	sbb r11, QWORD PTR [rdi+952]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+960], r8
	mov QWORD PTR [rdi+968], r9
	mov QWORD PTR [rdi+976], r10
	mov QWORD PTR [rdi+984], r11
	mov rdx, QWORD PTR [rdi+896]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+904]
	mulx r11, rax, QWORD PTR [rdi+912]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+920]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+904]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+912]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+920]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+912]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+920]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+896]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+904]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+912]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+920]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+800], r12
	mov QWORD PTR [rdi+808], r13
	mov QWORD PTR [rdi+816], r14
	mov QWORD PTR [rdi+824], r15
	mov rdx, r12
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+896]
	mulx r10, rax, QWORD PTR [rdi+904]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+912]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+920]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, r13
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+896]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+904]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+912]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+920]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, r14
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+896]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+904]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+912]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+920]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, r15
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+896]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+904]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+912]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+920]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+832], r12
	mov QWORD PTR [rdi+840], r13
	mov QWORD PTR [rdi+848], r14
	mov QWORD PTR [rdi+856], r15
	mov rdx, QWORD PTR [rdi+864]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+800]
	mulx r10, rax, QWORD PTR [rdi+808]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+816]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+824]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+872]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+808]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+816]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+824]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+880]
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
	mov rdx, QWORD PTR [rdi+888]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+800]
	adox r11, rax
	adcx r12, rcx
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
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+864], r12
	mov QWORD PTR [rdi+872], r13
	mov QWORD PTR [rdi+880], r14
	mov QWORD PTR [rdi+888], r15
	mov rdx, QWORD PTR [rdi+960]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+968]
	mulx r11, rax, QWORD PTR [rdi+976]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+984]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+968]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+976]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+984]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+976]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+984]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+960]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+968]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+976]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+984]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+512], r12
	mov QWORD PTR [rdi+520], r13
	mov QWORD PTR [rdi+528], r14
	mov QWORD PTR [rdi+536], r15
	mov r8, r12
	mov r9, r13
	mov r10, r14
	mov r11, r15
	sub r8, QWORD PTR [rdi+832]
	sbb r9, QWORD PTR [rdi+840]
	sbb r10, QWORD PTR [rdi+848]
	sbb r11, QWORD PTR [rdi+856]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+512], r8
	mov QWORD PTR [rdi+520], r9
	mov QWORD PTR [rdi+528], r10
	mov QWORD PTR [rdi+536], r11
	mov r8, r8
	mov r9, r9
	mov r10, r10
	mov r11, r11
	sub r8, QWORD PTR [rdi+864]
	sbb r9, QWORD PTR [rdi+872]
	sbb r10, QWORD PTR [rdi+880]
	sbb r11, QWORD PTR [rdi+888]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+512], r8
	mov QWORD PTR [rdi+520], r9
	mov QWORD PTR [rdi+528], r10
	mov QWORD PTR [rdi+536], r11
	mov r8, r8
	mov r9, r9
	mov r10, r10
	mov r11, r11
	sub r8, QWORD PTR [rdi+864]
	sbb r9, QWORD PTR [rdi+872]
	sbb r10, QWORD PTR [rdi+880]
	sbb r11, QWORD PTR [rdi+888]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+512], r8
	mov QWORD PTR [rdi+520], r9
	mov QWORD PTR [rdi+528], r10
	mov QWORD PTR [rdi+536], r11
	mov r8, QWORD PTR [rdi+864]
	mov r9, QWORD PTR [rdi+872]
	mov r10, QWORD PTR [rdi+880]
	mov r11, QWORD PTR [rdi+888]
	sub r8, QWORD PTR [rdi+512]
	sbb r9, QWORD PTR [rdi+520]
	sbb r10, QWORD PTR [rdi+528]
	sbb r11, QWORD PTR [rdi+536]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+544], r8
	mov QWORD PTR [rdi+552], r9
	mov QWORD PTR [rdi+560], r10
	mov QWORD PTR [rdi+568], r11
	mov rdx, QWORD PTR [rdi+960]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+544]
	mulx r10, rax, QWORD PTR [rdi+552]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+560]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+568]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+968]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+544]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+552]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+560]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+568]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+976]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+544]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+552]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+560]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+568]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+984]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+544]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+552]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+560]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+568]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+544], r12
	mov QWORD PTR [rdi+552], r13
	mov QWORD PTR [rdi+560], r14
	mov QWORD PTR [rdi+568], r15
	mov rdx, QWORD PTR [rdi+928]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+832]
	mulx r10, rax, QWORD PTR [rdi+840]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+848]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+856]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+936]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+856]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+944]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+856]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+952]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+832]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+840]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+848]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+856]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+928], r12
	mov QWORD PTR [rdi+936], r13
	mov QWORD PTR [rdi+944], r14
	mov QWORD PTR [rdi+952], r15
	mov r8, QWORD PTR [rdi+544]
	mov r9, QWORD PTR [rdi+552]
	mov r10, QWORD PTR [rdi+560]
	mov r11, QWORD PTR [rdi+568]
	sub r8, QWORD PTR [rdi+928]
	sbb r9, QWORD PTR [rdi+936]
	sbb r10, QWORD PTR [rdi+944]
	sbb r11, QWORD PTR [rdi+952]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+544], r8
	mov QWORD PTR [rdi+552], r9
	mov QWORD PTR [rdi+560], r10
	mov QWORD PTR [rdi+568], r11
	mov rdx, QWORD PTR [rdi+576]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+5376]
	mulx r10, rax, QWORD PTR [rdi+5384]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+5392]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+5400]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+584]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5376]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+5384]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+5392]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+5400]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+592]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5376]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+5384]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+5392]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+5400]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+600]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+5376]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+5384]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+5392]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+5400]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+576], r12
	mov QWORD PTR [rdi+584], r13
	mov QWORD PTR [rdi+592], r14
	mov QWORD PTR [rdi+600], r15
	mov rdx, r12
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+896]
	mulx r10, rax, QWORD PTR [rdi+904]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+912]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+920]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, r13
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+896]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+904]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+912]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+920]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, r14
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+896]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+904]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+912]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+920]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, r15
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+896]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+904]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+912]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+920]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+576], r12
	mov QWORD PTR [rdi+584], r13
	mov QWORD PTR [rdi+592], r14
	mov QWORD PTR [rdi+600], r15
	mov rax, QWORD PTR [rdi+576]
	or rax, QWORD PTR [rdi+584]
	or rax, QWORD PTR [rdi+592]
	or rax, QWORD PTR [rdi+600]
	mov ecx, 0
	sub rcx, rax
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+160]
	mov rdx, QWORD PTR [rdi+544]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rdi+168]
	mov rdx, QWORD PTR [rdi+552]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rdi+176]
	mov rdx, QWORD PTR [rdi+560]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rdi+184]
	mov rdx, QWORD PTR [rdi+568]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+568], rax
	xor rcx, -1
	movabs rax, 1
	and rax, rcx
	or rax, QWORD PTR [rdi+544]
	mov QWORD PTR [rdi+544], rax
	movabs rax, -4294967296
	and rax, rcx
	or rax, QWORD PTR [rdi+552]
	mov QWORD PTR [rdi+552], rax
	movabs rax, -1
	and rax, rcx
	or rax, QWORD PTR [rdi+560]
	mov QWORD PTR [rdi+560], rax
	movabs rax, 4294967294
	and rax, rcx
	or rax, QWORD PTR [rdi+568]
	mov QWORD PTR [rdi+568], rax
	mov rdx, QWORD PTR [rdi+512]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+576]
	mulx r10, rax, QWORD PTR [rdi+584]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+592]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+600]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+520]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+528]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+600]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+536]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+600]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+512], r12
	mov QWORD PTR [rdi+520], r13
	mov QWORD PTR [rdi+528], r14
	mov QWORD PTR [rdi+536], r15
	mov rdx, QWORD PTR [rdi+576]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+584]
	mulx r11, rax, QWORD PTR [rdi+592]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+600]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+584]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+592]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+600]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+576]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+584]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+592]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+600]
	mulx r15, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+800], r12
	mov QWORD PTR [rdi+808], r13
	mov QWORD PTR [rdi+816], r14
	mov QWORD PTR [rdi+824], r15
	mov rdx, r12
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+576]
	mulx r10, rax, QWORD PTR [rdi+584]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+592]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+600]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, r13
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+600]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, r14
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+600]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, r15
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+576]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+584]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+592]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+600]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+576], r12
	mov QWORD PTR [rdi+584], r13
	mov QWORD PTR [rdi+592], r14
	mov QWORD PTR [rdi+600], r15
	mov r8, QWORD PTR [rdi+160]
	mov r9, QWORD PTR [rdi+168]
	mov r10, QWORD PTR [rdi+176]
	mov r11, QWORD PTR [rdi+184]
	sub r8, QWORD PTR [rdi+544]
	sbb r9, QWORD PTR [rdi+552]
	sbb r10, QWORD PTR [rdi+560]
	sbb r11, QWORD PTR [rdi+568]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+1024], r8
	mov QWORD PTR [rdi+1032], r9
	mov QWORD PTR [rdi+1040], r10
	mov QWORD PTR [rdi+1048], r11
	movzx ecx, BYTE PTR [rdi+1504]
	sub rcx, 1
	mov rax, QWORD PTR [rdi+544]
	mov rdx, QWORD PTR [rdi+1024]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+544], rax
	mov rax, QWORD PTR [rdi+552]
	mov rdx, QWORD PTR [rdi+1032]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+552], rax
	mov rax, QWORD PTR [rdi+560]
	mov rdx, QWORD PTR [rdi+1040]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+560], rax
	mov rax, QWORD PTR [rdi+568]
	mov rdx, QWORD PTR [rdi+1048]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+568], rax
	call {vg_p256_inv_mod_p_adx}
	mov rdx, QWORD PTR [rdi+512]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+992]
	mulx r10, rax, QWORD PTR [rdi+1000]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1008]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1016]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+520]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+992]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1000]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1008]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+1016]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+528]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+992]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1000]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1008]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+1016]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+536]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+992]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1000]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1008]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+1016]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+1152], r12
	mov QWORD PTR [rdi+1160], r13
	mov QWORD PTR [rdi+1168], r14
	mov QWORD PTR [rdi+1176], r15
	mov rdx, QWORD PTR [rdi+1152]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+192]
	mulx r10, rax, QWORD PTR [rdi+200]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+208]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+216]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+1160]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+192]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+200]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+208]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+216]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+1168]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+192]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+200]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+208]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+216]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+1176]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+192]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+200]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+208]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+216]
	adox r14, rax
	adcx r15, rbp
	adox r15, rbp
	mov rdx, r8
	mov rax, r8
	shl rax, 32
	mov rbp, r8
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r8, rcx, rcx
	add r9, rax
	adc r10, rbp
	adc r11, rcx
	adc r8, 0
	mov rdx, r9
	mov rax, r9
	shl rax, 32
	mov rbp, r9
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r9, rcx, rcx
	add r10, rax
	adc r11, rbp
	adc r8, rcx
	adc r9, 0
	mov rdx, r10
	mov rax, r10
	shl rax, 32
	mov rbp, r10
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r10, rcx, rcx
	add r11, rax
	adc r8, rbp
	adc r9, rcx
	adc r10, 0
	mov rdx, r11
	mov rax, r11
	shl rax, 32
	mov rbp, r11
	shr rbp, 32
	movabs rcx, -4294967295
	mulx r11, rcx, rcx
	add r8, rax
	adc r9, rbp
	adc r10, rcx
	adc r11, 0
	add r12, r8
	adc r13, r9
	adc r14, r10
	adc r15, r11
	mov r8d, 0
	adc r8, 0
	mov rax, r12
	sub rax, QWORD PTR [rdi+64]
	mov rcx, r13
	sbb rcx, QWORD PTR [rdi+72]
	mov rdx, r14
	sbb rdx, QWORD PTR [rdi+80]
	mov rbp, r15
	sbb rbp, QWORD PTR [rdi+88]
	sbb r8, 0
	cmovae r12, rax
	cmovae r13, rcx
	cmovae r14, rdx
	cmovae r15, rbp
	mov QWORD PTR [rdi+1184], r12
	mov QWORD PTR [rdi+1192], r13
	mov QWORD PTR [rdi+1200], r14
	mov QWORD PTR [rdi+1208], r15
	mov rdx, QWORD PTR [rdi+1088]
	sub rdx, QWORD PTR [rdi+96]
	mov rdx, QWORD PTR [rdi+1096]
	sbb rdx, QWORD PTR [rdi+104]
	mov rdx, QWORD PTR [rdi+1104]
	sbb rdx, QWORD PTR [rdi+112]
	mov rdx, QWORD PTR [rdi+1112]
	sbb rdx, QWORD PTR [rdi+120]
	sbb rax, rax
	mov rbp, rax
	mov rdx, QWORD PTR [rdi+1088]
	or rdx, QWORD PTR [rdi+1096]
	or rdx, QWORD PTR [rdi+1104]
	or rdx, QWORD PTR [rdi+1112]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	and rdx, rbp
	mov rax, QWORD PTR [rdi+1472]
	and rax, rdx
	mov QWORD PTR [rdi+1472], rax
	mov rdx, QWORD PTR [rdi+576]
	or rdx, QWORD PTR [rdi+584]
	or rdx, QWORD PTR [rdi+592]
	or rdx, QWORD PTR [rdi+600]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+1472]
	and rax, rdx
	mov QWORD PTR [rdi+1472], rax
	mov rcx, QWORD PTR [rdi+1472]
	mov rax, QWORD PTR [rdi+1184]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+24], rax
	mov rax, QWORD PTR [rdi+1192]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+16], rax
	mov rax, QWORD PTR [rdi+1200]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+8], rax
	mov rax, QWORD PTR [rdi+1208]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi], rax
	mov rax, rcx
	and rax, 1
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
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
	lea rsp, [rsp-8]
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
