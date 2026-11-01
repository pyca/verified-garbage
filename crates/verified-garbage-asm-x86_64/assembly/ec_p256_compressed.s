// The functions of `src/ec_p256_compressed.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_p256_compress_public_key:
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
	mov rcx, QWORD PTR [rdi+1472]
	mov rdx, QWORD PTR [rdi+1216]
	and rdx, 1
	add rdx, 2
	and rdx, rcx
	mov BYTE PTR [rsi], dl
	mov rax, QWORD PTR [rdi+1120]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+25], rax
	mov rax, QWORD PTR [rdi+1128]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+17], rax
	mov rax, QWORD PTR [rdi+1136]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+9], rax
	mov rax, QWORD PTR [rdi+1144]
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

vg_ec_p256_decompress_public_key:
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
	movzx edx, BYTE PTR [r9]
	mov QWORD PTR [rdi+1088], rdx
	and rdx, -2
	xor rdx, 2
	cmp rdx, 1
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+1472]
	and rax, rdx
	mov QWORD PTR [rdi+1472], rax
	mov rdx, QWORD PTR [rdi+1120]
	sub rdx, QWORD PTR [rdi+64]
	mov rdx, QWORD PTR [rdi+1128]
	sbb rdx, QWORD PTR [rdi+72]
	mov rdx, QWORD PTR [rdi+1136]
	sbb rdx, QWORD PTR [rdi+80]
	mov rdx, QWORD PTR [rdi+1144]
	sbb rdx, QWORD PTR [rdi+88]
	sbb rax, rax
	mov rdx, rax
	mov rax, QWORD PTR [rdi+1472]
	and rax, rdx
	mov QWORD PTR [rdi+1472], rax
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+1120]
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
	mov rcx, QWORD PTR [rdi+1128]
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
	mov rcx, QWORD PTR [rdi+1136]
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
	mov rcx, QWORD PTR [rdi+1144]
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
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
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
	mov QWORD PTR [rdi+1376], r12
	mov QWORD PTR [rdi+1384], r13
	mov QWORD PTR [rdi+1392], r8
	mov QWORD PTR [rdi+1400], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+1376]
	mov ebp, 0
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
	mov rcx, QWORD PTR [rdi+1384]
	mov ebp, 0
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
	mov rcx, QWORD PTR [rdi+1392]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
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
	mov rcx, QWORD PTR [rdi+1400]
	mov ebp, 0
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
	mov QWORD PTR [rdi+1408], r12
	mov QWORD PTR [rdi+1416], r13
	mov QWORD PTR [rdi+1424], r8
	mov QWORD PTR [rdi+1432], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+256]
	mov ebp, 0
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
	mov rcx, QWORD PTR [rdi+264]
	mov ebp, 0
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
	mov rcx, QWORD PTR [rdi+272]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
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
	mov rcx, QWORD PTR [rdi+280]
	mov ebp, 0
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
	mov QWORD PTR [rdi+1376], r12
	mov QWORD PTR [rdi+1384], r13
	mov QWORD PTR [rdi+1392], r8
	mov QWORD PTR [rdi+1400], r9
	mov r8, QWORD PTR [rdi+1408]
	mov r9, QWORD PTR [rdi+1416]
	mov r10, QWORD PTR [rdi+1424]
	mov r11, QWORD PTR [rdi+1432]
	mov r12d, 0
	add r8, QWORD PTR [rdi+1376]
	adc r9, QWORD PTR [rdi+1384]
	adc r10, QWORD PTR [rdi+1392]
	adc r11, QWORD PTR [rdi+1400]
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
	mov QWORD PTR [rdi+1280], r8
	mov QWORD PTR [rdi+1288], r9
	mov QWORD PTR [rdi+1296], r10
	mov QWORD PTR [rdi+1304], r11
	mov r8, QWORD PTR [rdi+1280]
	mov r9, QWORD PTR [rdi+1288]
	mov r10, QWORD PTR [rdi+1296]
	mov r11, QWORD PTR [rdi+1304]
	mov r12d, 0
	add r8, QWORD PTR [rdi+1344]
	adc r9, QWORD PTR [rdi+1352]
	adc r10, QWORD PTR [rdi+1360]
	adc r11, QWORD PTR [rdi+1368]
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
	mov QWORD PTR [rdi+1408], r8
	mov QWORD PTR [rdi+1416], r9
	mov QWORD PTR [rdi+1424], r10
	mov QWORD PTR [rdi+1432], r11
	movabs rax, 0
	mov QWORD PTR [rdi+448], rax
	movabs rax, 1073741824
	mov QWORD PTR [rdi+456], rax
	movabs rax, 4611686018427387904
	mov QWORD PTR [rdi+464], rax
	movabs rax, 4611686017353646080
	mov QWORD PTR [rdi+472], rax
	mov ebx, 0
20:
	movzx eax, BYTE PTR [rdi+rbx*1+448]
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
	jne 20b
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+992], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+1000], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+1008], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+1016], rax
	mov ebx, 256
21:
	sub rbx, 1
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+992]
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
	mov rcx, QWORD PTR [rdi+1000]
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
	mov rcx, QWORD PTR [rdi+1008]
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
	mov rcx, QWORD PTR [rdi+1016]
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
	mov QWORD PTR [rdi+992], r12
	mov QWORD PTR [rdi+1000], r13
	mov QWORD PTR [rdi+1008], r8
	mov QWORD PTR [rdi+1016], r9
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+992]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1408]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1416]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1424]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1432]
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
	mov rcx, QWORD PTR [rdi+1000]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1408]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1416]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1424]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1432]
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
	mov rcx, QWORD PTR [rdi+1008]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1408]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1416]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1424]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1432]
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
	mov rcx, QWORD PTR [rdi+1016]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1408]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r11, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1416]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r12, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1424]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r13, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1432]
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
	mov QWORD PTR [rdi+1024], r12
	mov QWORD PTR [rdi+1032], r13
	mov QWORD PTR [rdi+1040], r8
	mov QWORD PTR [rdi+1048], r9
	movzx eax, BYTE PTR [rdi+rbx*1+2032]
	mov ecx, 0
	sub rcx, rax
	mov rax, QWORD PTR [rdi+992]
	mov rdx, QWORD PTR [rdi+1024]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+992], rax
	mov rax, QWORD PTR [rdi+1000]
	mov rdx, QWORD PTR [rdi+1032]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1000], rax
	mov rax, QWORD PTR [rdi+1008]
	mov rdx, QWORD PTR [rdi+1040]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1008], rax
	mov rax, QWORD PTR [rdi+1016]
	mov rdx, QWORD PTR [rdi+1048]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1016], rax
	test rbx, rbx
	jne 21b
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+992]
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
	mov rcx, QWORD PTR [rdi+1000]
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
	mov rcx, QWORD PTR [rdi+1008]
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
	mov rcx, QWORD PTR [rdi+1016]
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
	mov QWORD PTR [rdi+1216], r12
	mov QWORD PTR [rdi+1224], r13
	mov QWORD PTR [rdi+1232], r8
	mov QWORD PTR [rdi+1240], r9
	mov r8, QWORD PTR [rdi+160]
	mov r9, QWORD PTR [rdi+168]
	mov r10, QWORD PTR [rdi+176]
	mov r11, QWORD PTR [rdi+184]
	sub r8, QWORD PTR [rdi+1216]
	sbb r9, QWORD PTR [rdi+1224]
	sbb r10, QWORD PTR [rdi+1232]
	sbb r11, QWORD PTR [rdi+1240]
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
	mov QWORD PTR [rdi+1248], r8
	mov QWORD PTR [rdi+1256], r9
	mov QWORD PTR [rdi+1264], r10
	mov QWORD PTR [rdi+1272], r11
	mov rdx, QWORD PTR [rdi+1216]
	xor rdx, QWORD PTR [rdi+1088]
	and rdx, 1
	mov ecx, 0
	sub rcx, rdx
	mov rax, QWORD PTR [rdi+1216]
	mov rdx, QWORD PTR [rdi+1248]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1216], rax
	mov rax, QWORD PTR [rdi+1224]
	mov rdx, QWORD PTR [rdi+1256]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1224], rax
	mov rax, QWORD PTR [rdi+1232]
	mov rdx, QWORD PTR [rdi+1264]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1232], rax
	mov rax, QWORD PTR [rdi+1240]
	mov rdx, QWORD PTR [rdi+1272]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1240], rax
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+1216]
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
	mov rcx, QWORD PTR [rdi+1224]
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
	mov rcx, QWORD PTR [rdi+1232]
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
	mov rcx, QWORD PTR [rdi+1240]
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
	mov r8d, 0
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov r12d, 0
	mov r13d, 0
	mov rcx, QWORD PTR [rdi+1184]
	mov ebp, 0
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r8, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r9, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add rax, rbp
	adc rdx, 0
	add r10, rax
	adc rdx, 0
	mov rbp, rdx
	mov rax, QWORD PTR [rdi+1208]
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
	mov rcx, QWORD PTR [rdi+1192]
	mov ebp, 0
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
	mov rcx, QWORD PTR [rdi+1200]
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
	mov rcx, QWORD PTR [rdi+1208]
	mov ebp, 0
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
	mov QWORD PTR [rdi+1376], r12
	mov QWORD PTR [rdi+1384], r13
	mov QWORD PTR [rdi+1392], r8
	mov QWORD PTR [rdi+1400], r9
	mov r8, QWORD PTR [rdi+1376]
	mov r9, QWORD PTR [rdi+1384]
	mov r10, QWORD PTR [rdi+1392]
	mov r11, QWORD PTR [rdi+1400]
	sub r8, QWORD PTR [rdi+1408]
	sbb r9, QWORD PTR [rdi+1416]
	sbb r10, QWORD PTR [rdi+1424]
	sbb r11, QWORD PTR [rdi+1432]
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
	mov QWORD PTR [rdi+1280], r8
	mov QWORD PTR [rdi+1288], r9
	mov QWORD PTR [rdi+1296], r10
	mov QWORD PTR [rdi+1304], r11
	mov rdx, QWORD PTR [rdi+1280]
	or rdx, QWORD PTR [rdi+1288]
	or rdx, QWORD PTR [rdi+1296]
	or rdx, QWORD PTR [rdi+1304]
	cmp rdx, 1
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+1472]
	and rax, rdx
	mov QWORD PTR [rdi+1472], rax
	mov rdx, QWORD PTR [rdi+1216]
	xor rdx, QWORD PTR [rdi+1088]
	and rdx, 1
	mov ecx, 0
	sub rcx, rdx
	mov rdx, rcx
	xor rdx, -1
	mov rax, QWORD PTR [rdi+1472]
	and rax, rdx
	mov QWORD PTR [rdi+1472], rax
	mov rcx, QWORD PTR [rdi+1472]
	mov eax, 4
	and rax, rcx
	mov BYTE PTR [rsi], al
	mov rax, QWORD PTR [rdi+1120]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+25], rax
	mov rax, QWORD PTR [rdi+1128]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+17], rax
	mov rax, QWORD PTR [rdi+1136]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+9], rax
	mov rax, QWORD PTR [rdi+1144]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+1], rax
	mov rax, QWORD PTR [rdi+1216]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+57], rax
	mov rax, QWORD PTR [rdi+1224]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+49], rax
	mov rax, QWORD PTR [rdi+1232]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+41], rax
	mov rax, QWORD PTR [rdi+1240]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+33], rax
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

vg_ec_p256_compress_public_key_adx:
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
	mov rcx, QWORD PTR [rdi+1472]
	mov rdx, QWORD PTR [rdi+1216]
	and rdx, 1
	add rdx, 2
	and rdx, rcx
	mov BYTE PTR [rsi], dl
	mov rax, QWORD PTR [rdi+1120]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+25], rax
	mov rax, QWORD PTR [rdi+1128]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+17], rax
	mov rax, QWORD PTR [rdi+1136]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+9], rax
	mov rax, QWORD PTR [rdi+1144]
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

vg_ec_p256_decompress_public_key_adx:
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
	movzx edx, BYTE PTR [r9]
	mov QWORD PTR [rdi+1088], rdx
	and rdx, -2
	xor rdx, 2
	cmp rdx, 1
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+1472]
	and rax, rdx
	mov QWORD PTR [rdi+1472], rax
	mov rdx, QWORD PTR [rdi+1120]
	sub rdx, QWORD PTR [rdi+64]
	mov rdx, QWORD PTR [rdi+1128]
	sbb rdx, QWORD PTR [rdi+72]
	mov rdx, QWORD PTR [rdi+1136]
	sbb rdx, QWORD PTR [rdi+80]
	mov rdx, QWORD PTR [rdi+1144]
	sbb rdx, QWORD PTR [rdi+88]
	sbb rax, rax
	mov rdx, rax
	mov rax, QWORD PTR [rdi+1472]
	and rax, rdx
	mov QWORD PTR [rdi+1472], rax
	mov rdx, QWORD PTR [rdi+1120]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1312]
	mulx r10, rax, QWORD PTR [rdi+1320]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1328]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1336]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+1128]
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
	mulx r13, rax, QWORD PTR [rdi+1336]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+1136]
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
	mulx r14, rax, QWORD PTR [rdi+1336]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+1144]
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
	mulx r15, rax, QWORD PTR [rdi+1336]
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
	mulx r10, r9, QWORD PTR [rdi+1160]
	mulx r11, rax, QWORD PTR [rdi+1168]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1176]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+1160]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+1176]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+1168]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+1176]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+1152]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+1160]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+1168]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+1176]
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
	mov QWORD PTR [rdi+1376], r12
	mov QWORD PTR [rdi+1384], r13
	mov QWORD PTR [rdi+1392], r14
	mov QWORD PTR [rdi+1400], r15
	mov rdx, QWORD PTR [rdi+1376]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1152]
	mulx r10, rax, QWORD PTR [rdi+1160]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1168]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1176]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+1384]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1152]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1160]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+1176]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+1392]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1152]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1160]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+1176]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+1400]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1152]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1160]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+1176]
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
	mov QWORD PTR [rdi+1408], r12
	mov QWORD PTR [rdi+1416], r13
	mov QWORD PTR [rdi+1424], r14
	mov QWORD PTR [rdi+1432], r15
	mov rdx, QWORD PTR [rdi+256]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1152]
	mulx r10, rax, QWORD PTR [rdi+1160]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1168]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1176]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+264]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1152]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1160]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+1176]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+272]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1152]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1160]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+1176]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+280]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1152]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1160]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1168]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+1176]
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
	mov QWORD PTR [rdi+1376], r12
	mov QWORD PTR [rdi+1384], r13
	mov QWORD PTR [rdi+1392], r14
	mov QWORD PTR [rdi+1400], r15
	mov r8, QWORD PTR [rdi+1408]
	mov r9, QWORD PTR [rdi+1416]
	mov r10, QWORD PTR [rdi+1424]
	mov r11, QWORD PTR [rdi+1432]
	mov r12d, 0
	add r8, QWORD PTR [rdi+1376]
	adc r9, QWORD PTR [rdi+1384]
	adc r10, QWORD PTR [rdi+1392]
	adc r11, QWORD PTR [rdi+1400]
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
	mov QWORD PTR [rdi+1280], r8
	mov QWORD PTR [rdi+1288], r9
	mov QWORD PTR [rdi+1296], r10
	mov QWORD PTR [rdi+1304], r11
	mov r8, QWORD PTR [rdi+1280]
	mov r9, QWORD PTR [rdi+1288]
	mov r10, QWORD PTR [rdi+1296]
	mov r11, QWORD PTR [rdi+1304]
	mov r12d, 0
	add r8, QWORD PTR [rdi+1344]
	adc r9, QWORD PTR [rdi+1352]
	adc r10, QWORD PTR [rdi+1360]
	adc r11, QWORD PTR [rdi+1368]
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
	mov QWORD PTR [rdi+1408], r8
	mov QWORD PTR [rdi+1416], r9
	mov QWORD PTR [rdi+1424], r10
	mov QWORD PTR [rdi+1432], r11
	movabs rax, 0
	mov QWORD PTR [rdi+448], rax
	movabs rax, 1073741824
	mov QWORD PTR [rdi+456], rax
	movabs rax, 4611686018427387904
	mov QWORD PTR [rdi+464], rax
	movabs rax, 4611686017353646080
	mov QWORD PTR [rdi+472], rax
	mov ebx, 0
20:
	movzx eax, BYTE PTR [rdi+rbx*1+448]
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
	jne 20b
	mov rax, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+992], rax
	mov rax, QWORD PTR [rdi+232]
	mov QWORD PTR [rdi+1000], rax
	mov rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+1008], rax
	mov rax, QWORD PTR [rdi+248]
	mov QWORD PTR [rdi+1016], rax
	mov ebx, 256
21:
	sub rbx, 1
	mov rdx, QWORD PTR [rdi+992]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+1000]
	mulx r11, rax, QWORD PTR [rdi+1008]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1016]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+1000]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1008]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+1016]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+1008]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+1016]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+992]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+1000]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+1008]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+1016]
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
	mov QWORD PTR [rdi+992], r12
	mov QWORD PTR [rdi+1000], r13
	mov QWORD PTR [rdi+1008], r14
	mov QWORD PTR [rdi+1016], r15
	mov rdx, QWORD PTR [rdi+992]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1408]
	mulx r10, rax, QWORD PTR [rdi+1416]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1424]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1432]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+1000]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1408]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+1416]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1424]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+1432]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+1008]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1408]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+1416]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1424]
	adox r12, rax
	adcx r13, rcx
	mulx r14, rax, QWORD PTR [rdi+1432]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+1016]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1408]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+1416]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+1424]
	adox r13, rax
	adcx r14, rcx
	mulx r15, rax, QWORD PTR [rdi+1432]
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
	mov QWORD PTR [rdi+1024], r12
	mov QWORD PTR [rdi+1032], r13
	mov QWORD PTR [rdi+1040], r14
	mov QWORD PTR [rdi+1048], r15
	movzx eax, BYTE PTR [rdi+rbx*1+2032]
	mov ecx, 0
	sub rcx, rax
	mov rax, QWORD PTR [rdi+992]
	mov rdx, QWORD PTR [rdi+1024]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+992], rax
	mov rax, QWORD PTR [rdi+1000]
	mov rdx, QWORD PTR [rdi+1032]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1000], rax
	mov rax, QWORD PTR [rdi+1008]
	mov rdx, QWORD PTR [rdi+1040]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1008], rax
	mov rax, QWORD PTR [rdi+1016]
	mov rdx, QWORD PTR [rdi+1048]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1016], rax
	test rbx, rbx
	jne 21b
	mov rdx, QWORD PTR [rdi+992]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+192]
	mulx r10, rax, QWORD PTR [rdi+200]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+208]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+216]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+1000]
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
	mov rdx, QWORD PTR [rdi+1008]
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
	mov rdx, QWORD PTR [rdi+1016]
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
	mov QWORD PTR [rdi+1216], r12
	mov QWORD PTR [rdi+1224], r13
	mov QWORD PTR [rdi+1232], r14
	mov QWORD PTR [rdi+1240], r15
	mov r8, QWORD PTR [rdi+160]
	mov r9, QWORD PTR [rdi+168]
	mov r10, QWORD PTR [rdi+176]
	mov r11, QWORD PTR [rdi+184]
	sub r8, QWORD PTR [rdi+1216]
	sbb r9, QWORD PTR [rdi+1224]
	sbb r10, QWORD PTR [rdi+1232]
	sbb r11, QWORD PTR [rdi+1240]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+1248], r8
	mov QWORD PTR [rdi+1256], r9
	mov QWORD PTR [rdi+1264], r10
	mov QWORD PTR [rdi+1272], r11
	mov rdx, QWORD PTR [rdi+1216]
	xor rdx, QWORD PTR [rdi+1088]
	and rdx, 1
	mov ecx, 0
	sub rcx, rdx
	mov rax, QWORD PTR [rdi+1216]
	mov rdx, QWORD PTR [rdi+1248]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1216], rax
	mov rax, QWORD PTR [rdi+1224]
	mov rdx, QWORD PTR [rdi+1256]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1224], rax
	mov rax, QWORD PTR [rdi+1232]
	mov rdx, QWORD PTR [rdi+1264]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1232], rax
	mov rax, QWORD PTR [rdi+1240]
	mov rdx, QWORD PTR [rdi+1272]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1240], rax
	mov rdx, QWORD PTR [rdi+1216]
	xor ebp, ebp
	mulx r9, r8, QWORD PTR [rdi+1312]
	mulx r10, rax, QWORD PTR [rdi+1320]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+1328]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1336]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+1224]
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
	mulx r13, rax, QWORD PTR [rdi+1336]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+1232]
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
	mulx r14, rax, QWORD PTR [rdi+1336]
	adox r13, rax
	adcx r14, rbp
	adox r14, rbp
	mov rdx, QWORD PTR [rdi+1240]
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
	mulx r15, rax, QWORD PTR [rdi+1336]
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
	mov rdx, QWORD PTR [rdi+1184]
	xor ebp, ebp
	mulx r10, r9, QWORD PTR [rdi+1192]
	mulx r11, rax, QWORD PTR [rdi+1200]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+1208]
	adcx r11, rax
	adcx r12, rbp
	mov rdx, QWORD PTR [rdi+1192]
	xor ebp, ebp
	mulx rcx, rax, QWORD PTR [rdi+1200]
	adox r11, rax
	adcx r12, rcx
	mulx r13, rax, QWORD PTR [rdi+1208]
	adox r12, rax
	adcx r13, rbp
	adox r13, rbp
	mov rdx, QWORD PTR [rdi+1200]
	xor ebp, ebp
	mulx r14, rax, QWORD PTR [rdi+1208]
	adcx r13, rax
	adcx r14, rbp
	xor ebp, ebp
	mov rdx, QWORD PTR [rdi+1184]
	mulx rax, r8, rdx
	adcx r9, r9
	adox r9, rax
	mov rdx, QWORD PTR [rdi+1192]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+1200]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+1208]
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
	mov QWORD PTR [rdi+1376], r12
	mov QWORD PTR [rdi+1384], r13
	mov QWORD PTR [rdi+1392], r14
	mov QWORD PTR [rdi+1400], r15
	mov r8, QWORD PTR [rdi+1376]
	mov r9, QWORD PTR [rdi+1384]
	mov r10, QWORD PTR [rdi+1392]
	mov r11, QWORD PTR [rdi+1400]
	sub r8, QWORD PTR [rdi+1408]
	sbb r9, QWORD PTR [rdi+1416]
	sbb r10, QWORD PTR [rdi+1424]
	sbb r11, QWORD PTR [rdi+1432]
	sbb rax, rax
	mov ecx, eax
	movabs rdx, -4294967295
	and rdx, rax
	add r8, rax
	adc r9, rcx
	adc r10, 0
	adc r11, rdx
	mov QWORD PTR [rdi+1280], r8
	mov QWORD PTR [rdi+1288], r9
	mov QWORD PTR [rdi+1296], r10
	mov QWORD PTR [rdi+1304], r11
	mov rdx, QWORD PTR [rdi+1280]
	or rdx, QWORD PTR [rdi+1288]
	or rdx, QWORD PTR [rdi+1296]
	or rdx, QWORD PTR [rdi+1304]
	cmp rdx, 1
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+1472]
	and rax, rdx
	mov QWORD PTR [rdi+1472], rax
	mov rdx, QWORD PTR [rdi+1216]
	xor rdx, QWORD PTR [rdi+1088]
	and rdx, 1
	mov ecx, 0
	sub rcx, rdx
	mov rdx, rcx
	xor rdx, -1
	mov rax, QWORD PTR [rdi+1472]
	and rax, rdx
	mov QWORD PTR [rdi+1472], rax
	mov rcx, QWORD PTR [rdi+1472]
	mov eax, 4
	and rax, rcx
	mov BYTE PTR [rsi], al
	mov rax, QWORD PTR [rdi+1120]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+25], rax
	mov rax, QWORD PTR [rdi+1128]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+17], rax
	mov rax, QWORD PTR [rdi+1136]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+9], rax
	mov rax, QWORD PTR [rdi+1144]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+1], rax
	mov rax, QWORD PTR [rdi+1216]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+57], rax
	mov rax, QWORD PTR [rdi+1224]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+49], rax
	mov rax, QWORD PTR [rdi+1232]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+41], rax
	mov rax, QWORD PTR [rdi+1240]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+33], rax
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
